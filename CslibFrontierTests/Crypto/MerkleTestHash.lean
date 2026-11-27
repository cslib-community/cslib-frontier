/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Init

/-!
# A fixed-length hash for Merkle-tree tests

`Cslib.Crypto.merkleVerify` accepts only authentication paths whose labels have the length of the
root, as the digests of a hash do, so tests of honest openings need a hash whose digests all have
one length. `polyHash` reads a word as a number in bijective base two, with digits `1` for `false`
and `2` for `true`, reducing modulo the prime `65521` after each digit, and returns the low sixteen
bits of the result. Words of at most fourteen bits are never reduced, so distinct such words have
distinct digests. Longer words, such as the hash inputs of internal nodes, can collide; tests that
need a collision-free trace check it with `decide`. `keyedPolyHash` pads or truncates it to the
length of a key, for statements about hashes whose digests have the key's length.
-/

@[expose] public section

namespace CslibFrontierTests.Crypto.MerkleTestHash

/-- A sixteen-bit polynomial hash: the word read in bijective base two modulo `65521`, as sixteen
bits from the least significant. -/
def polyHash (x : List Bool) : List Bool :=
  (List.range 16).map (x.foldl (fun a b => (2 * a + bif b then 2 else 1) % 65521) 0).testBit

/-- Every digest of `polyHash` has sixteen bits. -/
@[simp]
theorem length_polyHash (x : List Bool) : (polyHash x).length = 16 := by
  simp [polyHash]

/-- A keyed hash with digests of the key's length: `polyHash`, padded with `false` or truncated to
`k.length` bits. Short keys leave few digests, so it has collisions. -/
def keyedPolyHash (k x : List Bool) : List Bool :=
  (polyHash x ++ List.replicate k.length false).take k.length

/-- Every digest of `keyedPolyHash k` has `k.length` bits. -/
@[simp]
theorem length_keyedPolyHash (k x : List Bool) : (keyedPolyHash k x).length = k.length := by
  simp [keyedPolyHash]

end CslibFrontierTests.Crypto.MerkleTestHash
