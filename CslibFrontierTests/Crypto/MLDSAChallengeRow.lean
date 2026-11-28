/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.SparseDigestChallenges
meta import CslibFrontier.Crypto.Computational.MLDSA.SparseDigestChallenges

/-!
# Bounded Algorithm 29 row programming

A row with discarded candidate bytes, mixed sign bits and an unused suffix is programmed to a
different signed support. Two digest addresses exercise success and exhaustion in the actual
SHAKE256 interface, including the first byte beyond the programmed prefix.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA Cslib.Crypto.MLDSA.FIPS204

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

private def testStream (salt : ℕ) : ExtendableOutput where
  read x n := List.ofFn fun i : Fin n =>
    ⟨(x.length + i.val + salt) % 256, Nat.mod_lt _ (by decide)⟩
  length_read _ _ := List.length_ofFn
  take_read _ {_ _} h := by
    apply List.ext_getElem (by simp [h])
    intro _ _ _
    simp

private def digestAddr (s : Level) (tag : Bool) (d : FixedBytes (digestBytes s)) :
    BitString (8 * digestBytes s + 2) :=
  Xofs.queryAddress (8 * digestBytes s) tag (Keccak.bytesToBitsLE d.toList)
    (by rw [Keccak.length_bytesToBitsLE, FixedBytes.length_toList])

private def checkInstalledOracle (s : Level) : Bool :=
  let H : Xofs := ⟨testStream 11, testStream 37⟩
  let row : FixedBytes 221 := fun j =>
    if j.val < 8 then 165 else if j.val < 10 then 255 else if j.val < 80 then 7 else 222
  let exhausted : FixedBytes 221 := fun _ => 255
  let target₁ : Poly := fun j => if j.val < s.params.τ then -1 else 0
  let target₂ : Poly := fun j => if j.val < s.params.τ then 1 else 0
  if h₁ : InBall s.params.τ target₁ then
    if h₂ : InBall s.params.τ target₂ then
      let c₁ : ChallengeRow.Target s := ⟨target₁, h₁⟩
      let c₂ : ChallengeRow.Target s := ⟨target₂, h₂⟩
      let bit0 : Fin (8 * digestBytes s) := ⟨0, by cases s <;> decide⟩
      let rows (x : BitString (8 * digestBytes s)) : FixedBytes 221 :=
        if x bit0 then row else exhausted
      let challenges (x : BitString (8 * digestBytes s)) : ChallengeRow.Target s :=
        if x bit0 then c₁ else c₂
      let G := H.withSparseDigestChallenges s rows challenges
      let dSucc : FixedBytes (digestBytes s) := fun _ => 1
      let dExh : FixedBytes (digestBytes s) := fun _ => 2
      let wSucc := Keccak.bytesToBitsLE dSucc.toList
      let wExh := Keccak.bytesToBitsLE dExh.toList
      let a := 8 * digestBytes s
      let addrSucc := digestAddr s true dSucc
      let addrExh := digestAddr s true dExh
      let addr128 := digestAddr s false dSucc
      let succBytes := G.h256.readBytes dSucc.toList 222
      let exhBytes := G.h256.readBytes dExh.toList 222
      let probes : List (Fin (8 * 222)) :=
        [⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8 * 8, by decide⟩, ⟨8 * 220 + 1, by decide⟩,
          ⟨8 * 221, by decide⟩, ⟨8 * 221 + 7, by decide⟩]
      let sameAt (addr : BitString (a + 2)) (v : BitString 512) :=
        probes.all fun idx =>
          H.sparseDigestResponse s rows a 222 addr v idx == G.queryTable a 222 addr idx
      G.sampleInBall s dSucc.toList == some target₁ &&
        G.sampleInBall s dExh.toList == none &&
        succBytes[8]? == some 255 && succBytes[9]? == some 255 && succBytes[220]? == some 222 &&
        succBytes[221]? == some (H.h256.byteAt wSucc 221) &&
        exhBytes == exhausted.toList ++ [H.h256.byteAt wExh 221] &&
        sameAt addrSucc c₁.responseBits &&
        sameAt addrExh c₂.responseBits &&
        sameAt addr128 c₁.responseBits
    else false
  else false

#guard checkInstalledOracle .mlDSA44
#guard checkInstalledOracle .mlDSA65
#guard checkInstalledOracle .mlDSA87

-- Once expansion is complete, every longer raw read at every address has the background suffix.
example (H : Xofs) (s : Level) (rows challenges) (x : List Bool) (j : ℕ) (hj : 221 ≤ j) :
    (H.withSparseDigestChallenges s rows challenges).h256.byteAt x j = H.h256.byteAt x j := by
  simp only [Xofs.withSparseDigestChallenges, Xofs.withPrefixLists,
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
