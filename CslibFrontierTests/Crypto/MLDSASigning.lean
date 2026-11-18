/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.MLDSA.SigningROM
import CslibFrontier.Crypto.Game.CloseTo.RejectedProgramming
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Tests for bounded ML-DSA signing

The one-coefficient fixture separates Algorithm 7's second-stage rejection checks from the
earlier response and low-bits checks. It also exercises counter-stepped first-success semantics.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Crypto Cslib.Crypto.MLDSA

namespace MLDSASigningTests

/-- Small executable parameters for the rejection predicates. The attempt tests do not claim
that this is a secure or standardized parameter set. -/
private abbrev toy : Params where
  n := 1
  q := 17
  k := 1
  ℓ := 1
  η := 1
  γ₁ := 8
  γ₂ := 2
  τ := 1
  β := 0

/-- A valid one-coefficient parameter set for the compressed-signing correctness client. -/
private abbrev correctnessToy : Params where
  n := 1
  q := 17
  k := 1
  ℓ := 1
  η := 1
  γ₁ := 8
  γ₂ := 2
  τ := 1
  β := 1

private def hash : Hash toy := fun _ => ![1]

private def correctnessHash : Hash correctnessToy := fun _ => ![1]

/-- With `s₂ = 3`, `d = 2` gives `t₀ = -1`. The accepting mask makes the hint set. -/
private def hintSk : SecretKey toy :=
  ⟨Matrix.of fun _ _ => ![1], fun _ => ![0], fun _ => ![3]⟩

/-- With `s₂ = 2`, `d = 2` gives `t₀ = 2`, exactly the rejected `γ₂` boundary. -/
private def normSk : SecretKey toy :=
  ⟨Matrix.of fun _ _ => ![1], fun _ => ![0], fun _ => ![2]⟩

private def correctnessSk : SecretKey correctnessToy :=
  ⟨Matrix.of fun _ _ => ![1], fun _ => ![0], fun _ => ![1]⟩

private def acceptingMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![6]

private def normBoundaryMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![7]

private def correctnessMask :
    Fin correctnessToy.ℓ → Fin correctnessToy.n → ZMod correctnessToy.q :=
  fun _ => ![5]

private def correctnessSchedule (_ : ℕ) :
    Fin correctnessToy.ℓ → Fin correctnessToy.n → ZMod correctnessToy.q :=
  correctnessMask

/-- This mask is rejected by the first-stage response check for `hintSk`. -/
private def firstStageRejectMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![8]

private theorem correctnessToy_valid : correctnessToy.Valid :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

private theorem correctnessHash_inBall : ∀ x, InBall correctnessToy.τ (correctnessHash x) := by
  intro _
  simp only [correctnessHash]
  decide +kernel

private theorem correctnessSk_short :
    ∀ i j, |(correctnessSk.s₂ i j).valMinAbs| ≤ correctnessToy.η := by
  intro i j
  fin_cases i; fin_cases j
  decide +kernel

example : hintWeight toy (fun _ => ![true]) = 1 := by decide +kernel

-- All checks pass when the single set hint is permitted.
example : (compressedSignAttempt toy 2 1 hash hintSk [] acceptingMask).isSome = true := by
  decide +kernel

-- The same candidate is rejected only because its hint weight exceeds `ω = 0`.
example : (compressedSignAttempt toy 2 0 hash hintSk [] acceptingMask).isNone = true := by
  decide +kernel

-- The line-28 product norm uses a strict bound and rejects `|c t₀| = γ₂`.
example : (compressedSignAttempt toy 2 1 hash normSk [] normBoundaryMask).isNone = true := by
  decide +kernel

-- The correctness hypotheses are jointly satisfiable, and the valid fixture has an output.
example :
    (compressedSignAttempt correctnessToy 2 1 correctnessHash correctnessSk []
      correctnessMask).isSome = true := by
  decide +kernel

-- A compressed output is the same response/challenge accepted by the uncompressed attempt.
example {σ : CompressedSignature correctnessToy}
    (hout : compressedSignAttempt correctnessToy 2 1 correctnessHash correctnessSk []
      correctnessMask = some σ) :
    signAttempt correctnessToy correctnessHash correctnessSk [] correctnessMask =
      some (⟨σ.z, σ.c⟩ : Signature correctnessToy) :=
  signAttempt_eq_some_of_compressedSignAttempt_eq_some
    correctnessToy 2 1 correctnessHash correctnessSk [] correctnessMask hout

-- Every output of the valid compressed attempt passes the compressed verifier.
example {σ : CompressedSignature correctnessToy}
    (hout : compressedSignAttempt correctnessToy 2 1 correctnessHash correctnessSk []
      correctnessMask = some σ) :
    compressedVerify correctnessToy 2 correctnessHash correctnessSk.publicKey [] σ = true :=
  compressedVerify_compressedSignAttempt correctnessToy correctnessToy_valid (by decide)
    correctnessHash_inBall correctnessSk_short hout

-- A nonzero secret shifts the mask by one. With A = 0 and s₂ = 0 the remaining checks
-- always pass. Of the sixteen masks -7 through 8, precisely -7 through 5 give |z| < 7.
private def shiftedSk : SecretKey correctnessToy :=
  ⟨0, fun _ => ![1], 0⟩

example : ((List.range 16).filter fun i =>
    (compressedSignAttempt correctnessToy 2 1 correctnessHash shiftedSk []
      (fun _ => ![(8 : ZMod 17) - i])).isSome).length = 13 := by decide +kernel

example :
    freshSigningAttempt correctnessToy 2 1 (by decide) shiftedSk ![1] =
      simulateFreshSigningAttempt correctnessToy 2 1 (by decide) shiftedSk.publicKey ![1] := by
  apply freshSigningAttempt_eq_simulate correctnessToy correctnessToy_valid (by decide)
  · intro i j
    fin_cases i; fin_cases j
    decide +kernel
  · intro i j
    fin_cases i; fin_cases j
    decide +kernel
  · decide +kernel

private def acceptImmediately (_ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  acceptingMask

private def acceptSecond (κ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  if κ = 0 then firstStageRejectMask else acceptingMask

private def alwaysReject (_ : ℕ) : Fin toy.ℓ → Fin toy.n → ZMod toy.q :=
  firstStageRejectMask

-- No attempt means the single uniform failure result.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptImmediately 0).isNone = true := by
  decide +kernel

-- The first scheduled attempt succeeds.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptImmediately 1).isSome = true := by
  decide +kernel

-- Counter zero rejects, then line 31 advances by `ℓ = 1` and counter one succeeds.
example : (compressedSignBounded toy 2 1 hash hintSk [] acceptSecond 2).isSome = true := by
  decide +kernel

-- Exhausting two rejecting attempts returns the same failure value.
example : (compressedSignBounded toy 2 1 hash hintSk [] alwaysReject 2).isNone = true := by
  decide +kernel

example : signingAttemptCounter toy 5 (2 : Fin 3) = 7 := by decide

-- Bounded signing inherits the one-attempt compressed-verification guarantee.
example {σ : CompressedSignature correctnessToy}
    (hout : compressedSignBounded correctnessToy 2 1 correctnessHash correctnessSk []
      correctnessSchedule 1 = some σ) :
    compressedVerify correctnessToy 2 correctnessHash correctnessSk.publicKey [] σ = true :=
  compressedVerify_compressedSignBounded correctnessToy correctnessToy_valid (by decide)
    correctnessHash_inBall correctnessSk_short hout

open Cslib Cslib.OracleComp

-- The first internal trial rejects. The second accepts. Direct hash queries on either side
-- see the same state, while the outer program receives only the final signing reply.
private def interleaved : OracleComp (SigningROMSpec toy Bool) Bool := do
  let before ← query (spec := SigningROMSpec toy Bool) (.inr (0, []))
  let sig ← query (spec := SigningROMSpec toy Bool) (.inl [])
  let after ← query (spec := SigningROMSpec toy Bool) (.inr (0, []))
  return !before && sig.isSome && after

private def countTrials : (q : List Bool ⊕ SigningHashPoint toy) →
    StateM ℕ (SigningROMSpec toy Bool q) :=
  sumHandler (fun _ n =>
    (if n == 0 then none else
      some (true, ⟨0, fun _ _ => false, 0⟩), n + 1))
    (fun _ n => (n != 0, n))

-- Four permitted attempts stop after the second, and the following direct query sees both.
example : (interpret countTrials (expandSigningRetries toy 4 interleaved)).run 0 = (true, 2) := by
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  simp only [expandSigningRetries, interleaved, hr, List.findSomeM?_cons, List.findSomeM?_nil,
    sumHandler, interpret_bind, interpret_query, countTrials, StateT.run, bind_pure_comp]
  rfl

-- The rejected point is the first coin, and its digest equals that coin. Among the four
-- equiprobable two-coin tapes, reading `false` returns true once if the rejected write is kept,
-- twice if it is erased. Comparing only the response of the signing attempt misses this effect.
private def readAfterRejection (keep : Bool) (coins : Bool × Bool) : Bool :=
  let step := RandomOracle.programmedTrialStep keep (fun (_ : Unit) x => x) id
    (fun _ _ => (none : Option Unit))
  let rejected := step (.inl ()) coins.1 []
  (step (.inr false) coins.2 rejected.2).1

example :
    let tapes := [(false, false), (false, true), (true, false), (true, true)]
    (tapes.countP (readAfterRejection true), tapes.countP (readAfterRejection false)) = (1, 2) := by
  decide +kernel

end MLDSASigningTests
