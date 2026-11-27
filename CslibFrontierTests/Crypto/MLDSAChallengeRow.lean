/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.ChallengeRowProgramming
meta import CslibFrontier.Crypto.Computational.MLDSA.ChallengeRowProgramming

/-!
# Bounded Algorithm 29 row programming

A row with discarded candidate bytes, mixed sign bits and an unused suffix is programmed to a
different signed support. The all-255 candidate row exhausts the byte budget.
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
