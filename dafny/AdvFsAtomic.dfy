// test Dafny for AdvFS/Atomic:
// - append and fsync are copy-on-write
// - goal: safeAppend() satisfies atomicity/durability
//

// (ondisk, incache)
type File = (string, string)
// use fd->inode (should be fd->ino->inode) for now
type Filesystem = map<int, File>

class World {
  var fs: Filesystem;

  function ondisk(fd: int) : string
    requires fd in fs;
    reads this;
  {
    fs[fd].0 // first part is ondisk
  }

  function content(fd: int) : string
    requires fd in fs;
    reads this;
  {
    fs[fd].1 // second part is incache
  }

  method append(fd: int, s: string) returns ()
    requires fd in fs;
    modifies this;
    ensures fd in fs;
    ensures ondisk(fd) == old(ondisk(fd));
    ensures content(fd) == old(content(fd)) + s;
  {
    // append data to cache
    var f := fs[fd];
    fs := fs[fd := (f.0, f.1 + s)];
  }

  method fsync(fd: int) returns ()
    requires fd in fs;
    modifies this;
    ensures fd in fs;
    ensures ondisk(fd) == old(content(fd));
    ensures content(fd) == old(content(fd));
  {
    // copy cache to disk
    var f := fs[fd];
    fs := fs[fd := (f.1, f.1)];
  }

  method crash() returns ()
    modifies this;
    ensures forall fd :: fd in old(fs) ==> fd in fs;
    ensures forall fd :: fd in old(fs) ==> ondisk(fd) == content(fd);
    ensures forall fd :: fd in old(fs) ==> ondisk(fd) == old(ondisk(fd));
  {
    // lose the cache part (copy disk to cache)
    fs := map fd | fd in fs :: (fs[fd].0, fs[fd].0);
  }

  method safeAppend(fd: int, s: string) returns (r: int)
    requires fd in fs;
    // must be already synced before or empty
    requires ondisk(fd) == content(fd);
    modifies this;
    ensures fd in fs;
    // atomicity
    ensures content(fd) == old(content(fd)) || content(fd) == old(content(fd)) + s;
    // durability
    ensures r == 0 ==> content(fd) == old(content(fd)) + s;
  {
    r := -1;
    if (*) { crash(); return; }
    append(fd, s);
    if (*) { crash(); return; }
    fsync(fd);
    r := 0;
    if (*) { crash(); return; }
  }
}
