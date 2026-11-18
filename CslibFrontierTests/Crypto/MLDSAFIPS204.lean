/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204

/-!
# ML-DSA byte verification

Exercise Algorithm 29's signed shuffle and rejection stream, Algorithm 27's digest boundary,
and Algorithm 21's rejection of noncanonical hint encodings.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204

-- NIST ACVP-Server, ML-DSA-keyGen-FIPS204/internalProjection.json, tgId 1, tcId 1
-- (commit 975de31eb83d87039ec88934fdc47d8c312b892d). Compare a SHAKE256 fingerprint of
-- the complete expected public-key bytes to keep the 1312-byte fixture out of the source.
private def keyGenSeed : List Byte := [
    0x71, 0x94, 0xb1, 0x3c, 0x95, 0x23, 0x10, 0x10, 0xaf, 0xd2, 0xc9, 0x09,
    0x99, 0x2b, 0xd2, 0x00, 0x3b, 0xa6, 0xf4, 0x37, 0xc3, 0x88, 0x6b, 0xdb,
    0xe3, 0xf6, 0xb8, 0x67, 0xa1, 0x4b, 0xa1, 0x61]

private def publicKeyFingerprint : List Byte := [
    0x0d, 0xb3, 0x22, 0x35, 0x94, 0xa1, 0xfc, 0xe8, 0xdb, 0x48, 0xc8, 0xf1,
    0x79, 0x36, 0x11, 0xa1, 0x7f, 0xcc, 0x00, 0x06, 0xff, 0xea, 0x26, 0xcf,
    0x70, 0x94, 0xd8, 0x32, 0x50, 0x37, 0x28, 0x8f]

#guard (keyGenPublic .mlDSA44 (fun i => keyGenSeed[i.val]!)).map (Keccak.shake256 · 32) ==
  some publicKeyFingerprint

-- Independent SHAKE256(0^256) expansion followed by the FIPS 204 Algorithm 29 shuffle.
private def zeroDigestSupport (value : ZMod 8380417) : Option (List ℕ) := do
  let c ← sampleInBall .mlDSA44 (List.replicate 32 0)
  return ((List.finRange 256).filter fun i => c i == value).map Fin.val

#guard zeroDigestSupport 1 ==
  some [5, 17, 23, 29, 30, 34, 51, 54, 59, 67, 88, 113, 127, 141, 147, 231, 233, 236, 248]
#guard zeroDigestSupport (-1) == some
  [18, 25, 38, 48, 70, 79, 86, 87, 98, 100, 114, 116, 129, 173, 195, 213, 219, 242, 244, 253]

private def signature (digest : List Byte) (hint : List Byte) : List Byte :=
  digest ++ List.replicate 2304 0 ++ hint

private def digest44 : List Byte := (List.finRange 32).map (fun i => Fin.ofNat 256 i.val)

#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 84 0))).map (·.digest) ==
  some digest44
#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 83 0))).isNone
-- Index 7 is used twice in the first row. A nonzero unused byte is also invalid.
#guard (sigDecode .mlDSA44 (signature digest44
  ([7, 7] ++ List.replicate 78 0 ++ [2, 2, 2, 2]))).isNone
#guard (sigDecode .mlDSA44 (signature digest44 (1 :: List.replicate 83 0))).isNone

#guard verify .mlDSA44 [] [] [] [] == some false
#guard verify .mlDSA44 [] [] (List.replicate 256 0) [] == none
