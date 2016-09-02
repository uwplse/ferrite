#!/usr/bin/env python3

import pickle
import sys
import itertools

def partition(lst, cond):
    sublst = []
    for e in lst:
        if cond(e):
            if len(sublst):
                yield sublst
            sublst = []
        else:
            sublst.append(e)
    if len(sublst):
        yield sublst

def apply_cmd(buf, lst):
    for (cmd, args) in lst:
        assert cmd == 'write'
        (data, off, fua) = args
        assert fua == 0
        assert off < len(buf)
        assert off + len(data) <= len(buf)
        buf[off:off+len(data)] = data

def gen(f):
    (snapshot, trace) = pickle.load(f)
    for (cmd, args) in trace:
        aux = None
        print(cmd, end='')
        if cmd == 'write':
            data, off, fua = args
            print(': len=%s, off=%s, fua=%s' % (len(data), off, fua), end='')
        print()
    for sublist in list(partition(trace, lambda x: x[0] == 'flush')):
        # try every possible prefix in the sublist; ignore the last one
        for perm in itertools.permutations(sublist):
            buf = snapshot.copy()
            perm = perm[:-1]
            if len(perm) == 0:
                continue
            apply_cmd(buf, perm)
            yield buf
        # apply the sublist
        apply_cmd(snapshot, sublist)
        yield snapshot

if __name__ == '__main__':
    assert len(sys.argv) == 2
    with open(sys.argv[1], 'rb') as inp:
        for i, img in enumerate(gen(inp)):
            with open(inp.name + '.' + '{:03d}'.format(i), 'wb') as out:
                out.write(img)
