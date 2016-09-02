// test Dafny for ext4/ordered:
// - append has the prefix property
// - goal: safeAppend() satisfies atomicity/durability
//

// (ondisk, incache)
datatype Object = File(f_ondisk: string, f_incore: string) |
                  Directory(d_ondisk: map<string, int>, d_incore: map<string, int>)
// use fd->inode (should be fd->ino->inode) for now
type Filesystem = map<int, Object>

datatype option<T> = None | Some(get: T)
type T

class World {
  var fs: Filesystem;

  function method file_ondisk(fd: int) : string
    requires fd in fs;
    requires fs[fd].File?;
    reads this;
  {
    fs[fd].f_ondisk // first part is ondisk
  }

  function method file_content(fd: int) : string
    requires fd in fs;
    requires fs[fd].File?;
    reads this;
  {
    fs[fd].f_incore // second part is incache
  }

  predicate file_wf(fd: int)
    reads this;
  {
    fd in fs && fs[fd].File? && file_ondisk(fd) <= file_content(fd)
  }

  method append(fd: int, s: string) returns ()
    requires file_wf(fd);
    modifies this;
    ensures file_wf(fd);
    ensures file_ondisk(fd) == old(file_ondisk(fd));
    ensures file_content(fd) == old(file_content(fd)) + s;
    ensures forall fd' :: fd' != fd && fd' in old(fs) ==> fd' in fs && fs[fd'] == old(fs[fd']);
  {
    // append data to cache
    var f := fs[fd];
    fs := fs[fd := File(f.f_ondisk, f.f_incore + s)];
  }

  method fsync(fd: int) returns ()
    requires file_wf(fd);
    modifies this;
    ensures file_wf(fd);
    ensures file_ondisk(fd) == old(file_content(fd));
    ensures file_content(fd) == old(file_content(fd));
    ensures forall fd' :: fd' != fd && fd' in old(fs) ==> fd' in fs && fs[fd'] == old(fs[fd']);
  {
    // copy cache to disk
    var f := fs[fd];
    fs := fs[fd := File(f.f_incore, f.f_incore)];
  }

  method partial_flush(fd: int) returns ()
    requires file_wf(fd);
    modifies this;
    ensures file_wf(fd);
    ensures file_content(fd) == old(file_content(fd));
    ensures old(file_ondisk(fd)) <= file_ondisk(fd) <= file_content(fd);
  {
    // copy a random number of bytes from cache to disk
    var f := fs[fd];
    var n: int, m: int := *, *;
    assume(0 <= n < m <= |f.f_ondisk|);
    fs := fs[fd := File(f.f_ondisk[0..n] + f.f_incore[n..m] + f.f_ondisk[m..], f.f_incore)];
  }

  method grow_flush(fd: int) returns ()
    requires file_wf(fd);
    modifies this;
    ensures file_wf(fd);
    ensures file_content(fd) == old(file_content(fd));
    ensures old(file_ondisk(fd)) <= file_ondisk(fd);
  {
    // copy a random number of bytes from cache to disk
    var f := fs[fd];
    var s: string := *;
    assume(s <= f.f_incore[|f.f_ondisk|..]);
    fs := fs[fd := File(f.f_ondisk + s, f.f_incore)];
  }

  method crash() returns ()
    modifies this;
    ensures forall fd :: old(file_wf(fd)) ==> file_wf(fd) &&
       file_ondisk(fd) == file_content(fd) == old(file_ondisk(fd));
    ensures forall fd :: old(dir_wf(fd)) ==> dir_wf(fd) &&
       dir_ondisk(fd) == dir_content(fd) == old(dir_ondisk(fd));
  {
    // lose the cache part (copy disk to cache)
    fs := map fd | fd in fs :: if fs[fd].File?
      then File(fs[fd].f_ondisk, fs[fd].f_ondisk)
      else Directory(fs[fd].d_ondisk, fs[fd].d_ondisk);
  }

  method safeAppend(fd: int, s: string) returns (r: int)
    requires file_wf(fd);
    // must be already synced before or empty
    requires file_ondisk(fd) == file_content(fd);
    modifies this;
    ensures file_wf(fd);
    // prefix
    // to get atomicity one needs a separate parser with the prefix property
    ensures old(file_content(fd)) <= file_content(fd) <= old(file_content(fd)) + s;
    ensures file_content(fd)[|old(file_content(fd))|..] <= s;
    // durability
    ensures r == 0 ==> file_content(fd) == old(file_content(fd)) + s;
  {
    r := -1;
    if (*) { grow_flush(fd); }
    if (*) { partial_flush(fd); }
    if (*) { crash(); return; }
    append(fd, s);
    if (*) { grow_flush(fd); }
    if (*) { partial_flush(fd); }
    if (*) { crash(); return; }
    fsync(fd);
    r := 0;
    if (*) { grow_flush(fd); }
    if (*) { partial_flush(fd); }
    if (*) { crash(); return; }
  }

  // serializer with prefix property
  function method encode(t: T) : string
  function method decode(s: string) : option<T>
  lemma decoder_encoder_ok(t: T)
    ensures forall s: string :: s <= encode(t) ==>
            decode(s) == Some(t) || decode(s) == None;

  method safeAppendAtomic(fd: int, t: T) returns (r: int)
    requires file_wf(fd);
    // must be already synced before or empty
    requires file_ondisk(fd) == file_content(fd);
    modifies this;
    ensures file_wf(fd);
    // atomicity
    ensures old(file_content(fd)) <= file_content(fd);
    ensures decode(file_content(fd)[|old(file_content(fd))|..]) == Some(t) ||
            decode(file_content(fd)[|old(file_content(fd))|..]) == None;
    {
      var s := encode(t);
      r := safeAppend(fd, s);
      decoder_encoder_ok(t);
    }


  predicate dir_wf(fd: int)
    reads this;
  {
    fd in fs && fs[fd].Directory?
  }

  function method dir_ondisk(fd: int) : map<string, int>
    requires dir_wf(fd);
    reads this;
  {
    fs[fd].d_ondisk
  }

  function method dir_content(fd: int) : map<string, int>
    requires dir_wf(fd);
    reads this;
  {
    fs[fd].d_incore
  }

  function method dir_lookup_content(fd: int, name: string) : string
    requires dir_wf(fd);
    requires name in dir_content(fd);
    requires file_wf(dir_content(fd)[name]);
    reads this;
  {
    file_content(dir_content(fd)[name])
  }

  function method dir_lookup_ondisk(fd: int, name: string) : string
    requires dir_wf(fd);
    requires name in dir_ondisk(fd);
    requires file_wf(dir_ondisk(fd)[name]);
    reads this;
  {
    file_ondisk(dir_ondisk(fd)[name])
  }

  method create(dirfd: int, name: string) returns (r: int)
    requires dir_wf(dirfd);
    requires name !in dir_content(dirfd);
    modifies this;
    ensures dir_wf(dirfd);
    ensures dir_ondisk(dirfd) == old(dir_ondisk(dirfd));
    ensures file_wf(r);
    ensures file_content(r) == "";
    ensures r !in old(fs);
    ensures name in dir_content(dirfd);
    ensures forall n :: n != name && n !in old(dir_content(dirfd)) ==>
            n !in dir_content(dirfd);
    ensures dir_content(dirfd)[name] == r;
    ensures forall n :: n != name && n in old(dir_content(dirfd)) ==>
            n in dir_content(dirfd) && dir_content(dirfd)[n] == old(dir_content(dirfd)[n]);
    ensures forall n :: n != name && n in old(dir_ondisk(dirfd)) ==>
            n in dir_ondisk(dirfd) && dir_ondisk(dirfd)[n] == old(dir_ondisk(dirfd)[n]);
    ensures forall fd :: old(file_wf(fd)) ==>
            file_wf(fd) && fs[fd] == old(fs[fd]);
  {
    var d := fs[dirfd];
    var ino: int := *;
    assume(ino !in fs);
    var f := File("", "");
    fs := fs[dirfd := Directory(d.d_ondisk, d.d_incore[name := ino])];
    fs := fs[ino := f];
    r := ino;
  }

  method unlink(dirfd: int, name: string)
    requires dir_wf(dirfd);
    requires name in dir_content(dirfd);
    modifies this;
    ensures dir_wf(dirfd);
    ensures dir_ondisk(dirfd) == old(dir_ondisk(dirfd));
    ensures name !in dir_content(dirfd);
    ensures forall n :: n != name && n in old(dir_content(dirfd)) ==> n in dir_content(dirfd) && dir_content(dirfd)[n] == old(dir_content(dirfd)[n]);
    ensures forall fd :: old(file_wf(fd)) ==>
            file_wf(fd) && file_content(fd) == old(file_content(fd)) && file_ondisk(fd) == old(file_ondisk(fd));
  {
    var d := fs[dirfd];
    var m := map n | n in d.d_incore && n != name :: d.d_incore[n];
    fs := fs[dirfd := Directory(d.d_ondisk, m)];
  }

  method rename(dirfd: int, from: string, to: string)
    requires dir_wf(dirfd);
    requires from in dir_content(dirfd);
    requires from != to;
    modifies this;
    ensures dir_wf(dirfd);
    ensures dir_ondisk(dirfd) == old(dir_ondisk(dirfd));
    ensures to in dir_content(dirfd);
    ensures from !in dir_content(dirfd);
    ensures dir_content(dirfd)[to] == old(dir_content(dirfd)[from]);
    ensures forall fd :: old(file_wf(fd)) ==>
            file_wf(fd) && file_content(fd) == old(file_content(fd)) && file_ondisk(fd) == old(file_ondisk(fd));
  {
    var d := fs[dirfd];
    var ino := d.d_incore[from];
    fs := fs[dirfd := Directory(d.d_ondisk, d.d_incore[to := ino])];
    unlink(dirfd, from);
  }

  method dsync(dirfd: int) returns ()
    requires dir_wf(dirfd);
    modifies this;
    ensures dir_wf(dirfd);
    ensures dir_ondisk(dirfd) == dir_content(dirfd) == old(dir_content(dirfd));
    ensures forall fd :: old(file_wf(fd)) ==>
            file_wf(fd) && file_content(fd) == old(file_content(fd)) && file_ondisk(fd) == old(file_ondisk(fd));
  {
    // flush incore to disk
    var d := fs[dirfd];
    fs := fs[dirfd := Directory(d.d_incore, d.d_incore)];
  }

  method safeReplaceWithContent(dirfd: int, s: string, name: string, tmpname: string) returns (r: int)
    requires dir_wf(dirfd);
    // dir must be already synced before or empty
    requires dir_ondisk(dirfd) == dir_content(dirfd);
    requires name in dir_content(dirfd);
    requires file_wf(dir_content(dirfd)[name]);
    // file must be already synced before or empty
    requires file_ondisk(dir_content(dirfd)[name]) == file_content(dir_content(dirfd)[name]);
    requires tmpname !in dir_content(dirfd);
    requires name != tmpname;
    modifies this;
    ensures dir_wf(dirfd);
    ensures name in dir_content(dirfd);
    ensures file_wf(dir_content(dirfd)[name]);
    // atomicity
    ensures dir_lookup_content(dirfd, name) == old(dir_lookup_content(dirfd, name)) ||
            dir_lookup_content(dirfd, name) == s;
    // durability
    ensures r == 0 ==> dir_lookup_content(dirfd, name) == s;
  {
    r := -1;

    if (*) { crash(); return; }

    var fd := create(dirfd, tmpname);

    if (*) { crash(); return;}

    append(fd, s);

    if (*) { crash(); return; }

    fsync(fd);

    if (*) { crash(); return; }

    rename(dirfd, tmpname, name);

    if (*) { crash(); return; }

    dsync(dirfd);

    if (*) { crash(); return; }

    r := 0;

    if (*) { crash(); return; }
  }

  method safeCreateWithContent(dirfd: int, s: string, name: string, tmpname: string) returns (r: int)
    requires dir_wf(dirfd);
    // dir must be already synced before or empty
    requires dir_ondisk(dirfd) == dir_content(dirfd);
    requires name !in dir_content(dirfd);
    requires tmpname !in dir_content(dirfd);
    requires name != tmpname;
    modifies this;
    ensures dir_wf(dirfd);
    // atomicity
    ensures name !in dir_content(dirfd) ||
            (file_wf(dir_content(dirfd)[name]) && dir_lookup_content(dirfd, name) == s);
    // durability
    ensures r == 0 ==>
            name in dir_content(dirfd) &&
            file_wf(dir_content(dirfd)[name]) &&
            dir_lookup_content(dirfd, name) == s;
  {
    r := -1;

    if (*) { crash(); return; }

    var fd := create(dirfd, tmpname);

    if (*) { crash(); return;}

    append(fd, s);

    if (*) { crash(); return; }

    fsync(fd);

    if (*) { crash(); return; }

    rename(dirfd, tmpname, name);

    if (*) { crash(); return; }

    dsync(dirfd);

    if (*) { crash(); return; }

    r := 0;

    if (*) { crash(); return; }
  }
}
