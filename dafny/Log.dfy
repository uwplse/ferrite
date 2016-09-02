// Arrakis log

newtype u8 = x: int | 0 <= x < 256
type bytes = seq<u8>

datatype option<T> = None | Some(get: T)

class World {
  var log: bytes;
  var end: nat;

  function method paddingLen(n: nat): nat
    ensures 0 <= paddingLen(n) < 512;
    ensures (n + paddingLen(n)) % 512 == 0;
  {
    if ((n % 512) == 0) then 0 else (512 - (n % 512))
  }

  function method entryLenFromPayloadLen(n: nat): nat
    ensures entryLenFromPayloadLen(n) % 512 == 0;
    ensures entryLenFromPayloadLen(n) >= 512;
  {
    n + 17 + paddingLen(n + 17)
  }


  function method encode64(n: nat): bytes
    ensures |encode64(n)| == 8;
  function method decode64(s: bytes): nat
    requires |s| == 8;
  lemma decode64_encode64_ok(n: nat)
    ensures forall n: nat :: decode64(encode64(n)) == n;

  function method readEntry(offset: nat): option<bytes>
    reads this;
  {
    if offset + 16 <= |log| &&
       offset + 16 + decode64(log[offset..offset + 8]) <= |log| &&
       offset + entryLenFromPayloadLen(decode64(log[offset..offset + 8])) <= |log| &&
       log[offset + entryLenFromPayloadLen(decode64(log[offset..offset + 8])) - 1] == 0xff
    then
      Some(log[offset + 16..offset + 16 + decode64(log[offset..offset + 8])])
    else
      None
  }

  // size (8) + next (8) + payload + padding + 0xff
  method append(s: bytes) returns (r: int)
    requires end + entryLenFromPayloadLen(|s|) <= |log|;
    requires forall i :: end <= i < |log| ==> log[i] == 0;
    modifies this;
    ensures |log| == old(|log|);
    ensures end <= |log|;
    ensures r == 0 ==> forall i :: end <= i < |log| ==> log[i] == 0;
    ensures old(log[0..end]) <= log[0..end];
    // atomicity
    ensures readEntry(old(end)) == None ||
            readEntry(old(end)) == Some(s);
    // durability
    ensures r == 0 ==> readEntry(old(end)) == Some(s);
  {
    r := -1;

    var plen := paddingLen(|s| + 17);

    var size: bytes := encode64(|s|);

    var next: bytes := *;
    assume(|next| == 8);

    var padding: bytes := *;
    assume(|padding| == plen && forall i :: 0 <= i < plen ==> padding[i] == 0);

    var marker: bytes := [0xff];

    var entry := size + next + s + padding + marker;
    assert(|entry| == entryLenFromPayloadLen(|s|));
    decode64_encode64_ok(|s|);
    assert(decode64(size) == |s|);
    assert(entry[0..8] == size);
    assert(decode64(entry[0..8]) == |s|);
    assert(entry[16..16+decode64(entry[0..8])] == s);

    // prefix failure
    if (*)
    {
      var partial: bytes := *;
      // atomic; though not necessary, but simplify the reasoning
      assume(entry[0..8] <= partial < entry);
      var newLog := log[0..end] + partial + log[end + |partial|..];
      log := newLog;
      assert(log[end..end + 8] == size);
      return;
    }

    var newEnd := end + |entry|;
    var newLog := log[0..end] + entry + log[newEnd..];
    assert(newLog[end..newEnd] == entry);
    log := newLog;

    assert(log[end..end + 8] == size);
    assert(log[end + 16..end + 16 + decode64(log[end..end + 8])] == s);
    end := newEnd;
    r := 0;
  }
}
