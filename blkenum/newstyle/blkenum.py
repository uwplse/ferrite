#!/usr/bin/env python3

# The NBD protocol is described here:
# https://github.com/yoe/nbd/blob/master/doc/proto.md
#
# The server implements the newstyle negotiation.
# The backend is an in-memory buffer.

from enum import Enum, unique
import pickle
import socket, socketserver, http.server
import struct
import sys
import os.path, tempfile
import threading
import argparse

INIT_PASSWD       = 0x4e42444d41474943 # "NBDMAGIC"
OPTS_MAGIC        = 0x49484156454F5054 # "IHAVEOPT"
REPLY_MAGIC       = 0x3e889045565a9
NBD_REQUEST_MAGIC = 0x25609513
NBD_REPLY_MAGIC   = 0x67446698

NBD_OPT_EXPORT_NAME = 1
NBD_OPT_ABORT       = 2
NBD_OPT_LIST        = 3

NBD_REP_ACK          = 1
NBD_REP_SERVER       = 2
NBD_REP_FLAG_ERROR   = 1 << 31
NBD_REP_ERR_UNSUP    = 1 | NBD_REP_FLAG_ERROR
NBD_REP_ERR_POLICY   = 2 | NBD_REP_FLAG_ERROR
NBD_REP_ERR_INVALID  = 3 | NBD_REP_FLAG_ERROR
NBD_REP_ERR_PLATFORM = 4 | NBD_REP_FLAG_ERROR

# global flags
NBD_FLAG_FIXED_NEWSTYLE   = 1 << 0
NBD_FLAG_NO_ZEROES        = 1 << 1
# client-to-server flags
NBD_FLAG_C_FIXED_NEWSTYLE = NBD_FLAG_FIXED_NEWSTYLE
NBD_FLAG_C_NO_ZEROES      = NBD_FLAG_NO_ZEROES

NBD_FLAG_HAS_FLAGS  = 1 << 0
NBD_FLAG_READ_ONLY  = 1 << 1
NBD_FLAG_SEND_FLUSH = 1 << 2
NBD_FLAG_SEND_FUA   = 1 << 3
NBD_FLAG_ROTATIONAL = 1 << 4
NBD_FLAG_SEND_TRIM  = 1 << 5

NBD_CMD_MASK     = 0xffff
NBD_CMD_FLAG_FUA = 1 << 16

EPERM  =  1
EIO    =  5
ENOMEM = 12
EINVAL = 22
ENOSPC = 28

@unique
class Cmd(Enum):
    read  = 0
    write = 1
    disc  = 2
    flush = 3
    trim  = 4

class TCPServer(socketserver.TCPServer):
    allow_reuse_address = True
    # to be initialized in main
    backend = None

class Log:
    _trace = None
    _snapshot = None
    @classmethod
    def begin(cls):
        assert cls._snapshot == None
        assert cls._trace == None
        cls._snapshot = TCPServer.backend.copy()
        cls._trace = []
    @classmethod
    def echo(cls, s):
        cls.add("echo", s)
    @classmethod
    def end(cls):
        assert cls._snapshot != None
        assert cls._trace != None
        r = pickle.dumps((cls._snapshot, cls._trace))
        cls._trace = None
        cls._snapshot = None
        return r
    @classmethod
    def dump(cls):
        return TCPServer.backend
    # be careful about online reload due to caching
    #@classmethod
    #def load(cls, s):
    #  TCPServer.backend[:] = bytearray(s)
    @classmethod
    def add(cls, cmd, *args):
        if cls._trace != None:
            cls._trace.append((cmd, tuple(args)))

class NBDHandler(socketserver.StreamRequestHandler):
    def handle(self):
        buf = TCPServer.backend
        lock = TCPServer.lock

        # fixed newstyle negotiation
        size = len(buf)
        smallflags = NBD_FLAG_FIXED_NEWSTYLE
        self.wfile.write(struct.pack("!QQH", INIT_PASSWD, OPTS_MAGIC, smallflags))
        cflags = struct.unpack("!I", self.rfile.read(4))[0]
        print("negotiation:", hex(cflags))
        assert cflags & smallflags

        # option haggling
        trans_flags = NBD_FLAG_HAS_FLAGS | NBD_FLAG_SEND_FLUSH | NBD_FLAG_SEND_FUA | NBD_FLAG_SEND_TRIM
        while True:
            s = self.rfile.read(16)
            (magic, option, length) = struct.unpack("!QII", s)
            print("option:", hex(magic), hex(option), length)
            assert magic == OPTS_MAGIC
            data = None
            if length:
                data = self.rfile.read(length)
            if option == NBD_OPT_ABORT:
                self.wfile.write(struct.pack("!QIII", REPLY_MAGIC, option, NBD_REP_ACK, 0))
                return
            elif option == NBD_OPT_EXPORT_NAME:
                # ignore export name
                print("export:", data)
                self.wfile.write(struct.pack("!QH", size, trans_flags) + b'\0' * 124)
                break
            else:
                self.wfile.write(struct.pack("!QIII", REPLY_MAGIC, option, NBD_REP_ERR_UNSUP, 0))

        # transmission phase
        while True:
            s = self.rfile.read(28)
            (magic, typ, hdl, off, n) = struct.unpack("!II8sQI", s)
            assert magic == NBD_REQUEST_MAGIC
            cmd = Cmd(typ & NBD_CMD_MASK)
            fua = typ & NBD_CMD_FLAG_FUA
            print(cmd.name, end='')
            if n > 0:
                print(", from=%s, len=%s" % (off, n), end='')
            if fua:
                print(", fua=1", end='')
            print()
            if cmd == Cmd.read:
                if off + n > size:
                    self.reply(EINVAL, hdl)
                    continue
                self.reply(0, hdl)
                self.wfile.write(buf[off:off+n])
            elif cmd == Cmd.write:
                # data follows the request
                # no need to deal with FUA here
                data = self.rfile.read(n)
                if off + n > size:
                    self.reply(ENOSPC, hdl)
                    continue
                lock.acquire()
                buf[off:off+n] = data
                lock.release()
                self.reply(0, hdl)
                Log.add(cmd.name, data, off, fua)
            elif cmd == Cmd.disc:
                self.request.close()
                return
            elif cmd == Cmd.flush:
                # flush is no-op as this is in-memory
                self.reply(0, hdl)
                Log.add(cmd.name)
            elif cmd == Cmd.trim:
                if off + n > size:
                    self.reply(EINVAL, hdl)
                    continue
                lock.acquire()
                buf[off:off+n] = b'\x00' * n
                lock.release()
                self.reply(0, hdl)
            else:
                self.reply(EINVAL, hdl)
    def reply(self, error, hdl):
        self.wfile.write(struct.pack("!II", NBD_REPLY_MAGIC, error) + hdl)

class HTTPHandler(http.server.SimpleHTTPRequestHandler):
    def handle(self):
        lock = TCPServer.lock
        lock.acquire()
        super().handle()
        lock.release()
    def do_GET(self):
        # call Log.* based on request URI
        assert self.path.startswith('/')
        k = self.path[1:]
        r = getattr(Log, k)()
        self.send_response(200)
        if r == None:
            self.end_headers()
            return
        data = r
        self.send_header("Content-Type", "application/octet-stream")
        self.send_header("Content-Length", len(data))
        self.end_headers()
        self.wfile.write(data)
    def do_POST(self):
        # call Log.* based on request URI
        assert self.path.startswith('/')
        k = self.path[1:]
        content_length = int(self.headers.get("content-length", 0))
        content = self.rfile.read(content_length)
        getattr(Log, k)(content)
        self.send_response(200)
        self.end_headers()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="A Network Block Device (NBD) server")
    parser.add_argument(
        "--size", type=int, metavar="megs", default=16,
        help="disk size in megabytes (default: 16)")
    parser.add_argument(
        "--load", type=str, metavar="file",
        help="load file as disk image")
    args = parser.parse_args()

    if args.load != None:
        TCPServer.backend = bytearray(open(args.load, "rb").read())
    else:
        TCPServer.backend = bytearray(args.size * 1024 * 1024)
    TCPServer.lock = threading.Lock()

    host, port = "", 10809
    server = TCPServer((host, port), NBDHandler)
    # monitor
    monitor = TCPServer(("", 10880), HTTPHandler)
    threading.Thread(target=monitor.serve_forever).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.shutdown()
        monitor.shutdown()
