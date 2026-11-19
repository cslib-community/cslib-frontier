/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.SparseDigestChallenges
meta import CslibFrontier.Crypto.Computational.MLDSA.ChallengeRowProgramming

/-!
# Bounded Algorithm 29 row programming

A row with discarded candidate bytes, mixed sign bits and an unused suffix is programmed to a
different signed support. Two digest addresses exercise success and exhaustion in the actual
SHAKE256 interface, including the first byte beyond the programmed prefix.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Crypto Cslib.Crypto.MLDSA Cslib.Crypto.MLDSA.FIPS204

private def checkRows (s : Level) : Bool :=
  let row : FixedBytes 221 := fun j =>
    if j.val < 8 then 165 else if j.val < 10 then 255 else if j.val < 80 then 7 else 222
  let exhausted : FixedBytes 221 := fun _ => 255
  let target : Poly := fun j => if j.val < s.params.τ then -1 else 0
  if h : InBall s.params.τ target then
    let d : ChallengeRow.Target s := ⟨target, h⟩
    let (out, old) := ChallengeRow.exchangeSampleInBall s (row, d)
    sampleInBallBytes s row.toList == some old.val && old.val != target &&
      sampleInBallBytes s out.toList == some target &&
      out 8 == 255 && out 9 == 255 && out 220 == 222 &&
      (ChallengeRow.exchangeSampleInBall s (out, old)).1 == row &&
      (sampleInBallBytes s exhausted.toList).isNone &&
      (ChallengeRow.exchangeSampleInBall s (exhausted, d)).1 == exhausted
  else false

#guard checkRows .mlDSA44
#guard checkRows .mlDSA65
#guard checkRows .mlDSA87

-- Once expansion is complete, every longer raw read at every address has the background suffix.
example (H : Xofs) (s : Level) (rows challenges) (x : List Bool) (j : ℕ) (hj : 221 ≤ j) :
    (H.withSparseDigestChallenges s rows challenges).h256.byteAt x j = H.h256.byteAt x j := by
  simp only [Xofs.withSparseDigestChallenges, Xofs.withPrefixRegister,
    ExtendableOutput.byteAt_withPrefixes]
  have beyond (r : FixedBytes 221) : r.toList[j]? = none :=
    List.getElem?_eq_none (by simpa only [FixedBytes.length_toList] using hj)
  split <;> simp only [Option.bind_some, beyond, Option.bind_none, Option.getD_none]

-- On a single shared device a successful digest and an exhausted one retain different outcomes.
example (H : Xofs) (s : Level) (rows challenges) (d e : FixedBytes (digestBytes s)) (p : Poly)
    (hd : sampleInBallBytes s (rows (Keccak.fixedBytesEquivBitsLE _ d)).toList = some p)
    (he : sampleInBallBytes s (rows (Keccak.fixedBytesEquivBitsLE _ e)).toList = none) :
    let G := H.withSparseDigestChallenges s rows challenges
    G.sampleInBall s d.toList = some (challenges (Keccak.fixedBytesEquivBitsLE _ d)).val ∧
      G.sampleInBall s e.toList = none := by
  simp only [Xofs.sampleInBall_withSparseDigestChallenges, hd, he, Option.map_some,
    Option.map_none, and_self]
