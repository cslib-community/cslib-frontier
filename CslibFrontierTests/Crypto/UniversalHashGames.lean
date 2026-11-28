/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: local-only (test suite)

import Cslib.Foundations.Data.BitString
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Crypto.Primitives.UHF.Difference
import CslibFrontier.Crypto.Primitives.UHF.PairwiseUnpredictability
import CslibFrontier.Crypto.Primitives.UHF.PolynomialPrediction
import CslibFrontier.Crypto.Primitives.UHF.XorHash.PRF
import CslibFrontier.Crypto.Primitives.UHF.XorHash.Reduction
import CslibFrontier.Crypto.Primitives.UHF.XorHash.Word
import CslibFrontier.Crypto.Protocols.MAC.OneTime
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.HashFamily.Polynomial
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.BooleanRing

set_option linter.privateModule false

/-!
# Single-pair universal hash games

The collision and difference experiments reject repeated messages, and the exhaustive search
examines all distinct pairs. A nonzero difference checks the order of the two hashes.
The prediction game reveals one digest and rejects a prediction for the queried message.
-/

namespace Cslib.Crypto.UHF.Tests

open Cslib.Probability
open scoped ENNReal NNReal

private def hash (_ : Unit) (m : Fin 3) : Bool := decide (m = 0)

example :
    (bestCollisionGuess hash [0, 1, 2]).map (fun guess => (guess.first, guess.second)) =
      some (1, 2) := by
  decide

example : (bestCollisionGuess hash [0, 0]).isNone := by
  decide

example : ProbComp.eval (collisionExperiment hash (pure ⟨0, 0⟩)) true = 0 := by
  simp [collisionExperiment, ProbComp.eval_uniform]

example :
    ProbComp.eval (differenceExperiment (fun (_ : Unit) (m : ZMod 3) => m)
      (pure ⟨⟨0, 1⟩, 1⟩)) true = 1 := by
  simp [differenceExperiment, ProbComp.eval_uniform]

example :
    ProbComp.eval (differenceExperiment (fun (_ : Unit) (m : ZMod 3) => m)
      (pure ⟨⟨0, 0⟩, 0⟩)) true = 0 := by
  simp [differenceExperiment, ProbComp.eval_uniform]

/-- A repeated message does not hide the collision of the two distinct messages. -/
example :
    1 ≤ ((3 : ℝ≥0∞) ^ 2 / 2) *
      ProbComp.eval (collisionExperiment (fun (_ : Unit) (_ : Bool) => false)
        (collisionPairReduction false (pure [false, true, false]))) true := by
  have h := eval_multiQueryExperiment_le_collisionPairReduction
    (fun (_ : Unit) (_ : Bool) => false) false (pure [false, true, false]) (Q := 3)
    (by simp)
  simpa [multiQueryExperiment, ProbComp.eval_uniform] using h

open Turing.MultiTapeTM in
/-- The actual wrapper on the repeated-message list is strict PPT. -/
example : IsPPTOn encUnit (encCollisionGuess encBool)
    (fun _ => collisionPairReduction false (pure [false, true, false])) :=
  isPPTOn_collisionPairReduction (encM := encBool) (A := fun _ : Unit => pure [false, true, false])
    (ComputableInPolyTime.const [false, true, false]).isPPTOn false

private def unitSetup (_ : ℕ) : ProbComp Unit := pure ()

private def boolHash (_ : ℕ) (_ : Unit) (_ : Unit) (m : Bool) : Bool := m

private def constHash (_ : ℕ) (_ : Unit) (_ : Unit) (_ : Bool) : Bool := false

open Turing.MultiTapeTM in
/-- An injective hash on both Boolean messages is secure in the asymptotic game. -/
example : IsMultiQueryUHF encUnit encBool unitSetup (fun _ _ _ => true) boolHash := by
  have h : IsComputationalUHF encUnit encBool unitSetup (fun _ _ _ => true) boolHash := by
    apply Game.Indistinguishable.of_negligible_succProbability
    intro A _
    have hfalse (n : ℕ) : collisionGame unitSetup (fun _ _ _ => true) boolHash A n =
        PMF.pure false := by
      simp [collisionGame, unitSetup, boolHash, ProbComp.eval_uniform, PMF.uniformOfFintype_unit]
    simp [hfalse, Game.succProbability]
  exact h.isMultiQueryUHF (ComputableInPolyTime.const ()).isPPTOn

open Turing.MultiTapeTM in
/-- A strict PPT adversary always wins the single-pair game against a constant hash. -/
theorem not_isComputationalUHF_const :
    ¬ IsComputationalUHF encUnit encBool unitSetup (fun _ _ _ => true) constHash := by
  intro h
  let guess : CollisionGuess Bool := ⟨false, true⟩
  have hwin (n : ℕ) :
      collisionGame unitSetup (fun _ _ _ => true) constHash (fun _ => pure guess) n =
        PMF.pure true := by
    simp [collisionGame, unitSetup, constHash, guess, ProbComp.eval_uniform,
      PMF.uniformOfFintype_unit]
  have hnegl := h.negligible_succProbability (fun _ => pure guess)
    (ComputableInPolyTime.const guess).isPPTOn
  exact not_negligible_const one_ne_zero (by simpa [hwin, Game.succProbability] using hnegl)

open Turing.MultiTapeTM in
/-- A strict PPT adversary always wins the multi-query game against a constant hash. -/
theorem not_isMultiQueryUHF_const :
    ¬ IsMultiQueryUHF encUnit encBool unitSetup (fun _ _ _ => true) constHash := by
  intro h
  let ms := [false, true, false]
  have hwin (n : ℕ) :
      multiQueryGame unitSetup (fun _ _ _ => true) constHash (fun _ => pure ms) n =
        PMF.pure true := by
    simp [multiQueryGame, unitSetup, constHash, ms, ProbComp.eval_uniform,
      PMF.uniformOfFintype_unit]
  have hnegl := h.negligible_succProbability (fun _ => pure ms)
    (ComputableInPolyTime.const ms).isPPTOn
  exact not_negligible_const one_ne_zero (by simpa [hwin, Game.succProbability] using hnegl)

/-- Invalid messages do not contribute collisions to the multi-query game. -/
example (n : ℕ) :
    multiQueryGame unitSetup (fun _ _ m => m) constHash (fun _ => pure [false, true, false]) n =
      PMF.pure false := by
  simp [multiQueryGame, unitSetup, constHash, ProbComp.eval_uniform, PMF.uniformOfFintype_unit]

private def residueHash (_ : ℕ) (_ : Unit) (_ : Unit) (m : Bool) : ZMod 3 :=
  if m then 1 else 0

open Turing.MultiTapeTM in
/-- The public prediction of one always succeeds on the ordered Boolean pair. -/
theorem not_isComputationalDUF_residueHash :
    ¬ IsComputationalDUF encUnit encBool unitSetup (fun _ _ _ => true) residueHash
      (fun _ => encZMod 3) := by
  intro h
  let guess : DifferenceGuess Bool (List Bool) := ⟨⟨false, true⟩, encZMod 3 1⟩
  have hwin (n : ℕ) : differenceGame unitSetup (fun _ _ _ => true) residueHash
      (fun _ => encZMod 3) (fun _ => pure guess) n = PMF.pure true := by
    simp [differenceGame, unitSetup, residueHash, guess, ProbComp.eval_uniform,
      PMF.uniformOfFintype_unit]
  have hnegl := h.negligible_succProbability (fun _ => pure guess)
    (ComputableInPolyTime.const guess).isPPTOn
  exact not_negligible_const one_ne_zero (by simpa [hwin, Game.succProbability] using hnegl)

/-- Repeating a block uses two distinct table entries, even against an empty comparison input. -/
example :
    (PMF.uniformOfFintype (Bool × Fin 2 → BitString 2)).map
        (fun f => xorHash f ⟨[true, true], by decide⟩ - xorHash f ⟨[], by decide⟩) =
      PMF.uniformOfFintype (BitString 2) :=
  uniform_xorHash_sub (by decide)

/-- The finite collision game uses the ideal table's pairwise bound. -/
example (A : ProbComp (CollisionGuess {m : List Bool // m.length ≤ 2})) :
    ProbComp.eval (collisionExperiment (xorHash (Y := BitString 2)) A) true ≤
      (Fintype.card (BitString 2) : ℝ≥0∞)⁻¹ :=
  (isUniversalHash_iff_eval_collisionExperiment_le _ _).mp
    isDeltaUniversalHash_xorHash.isUniversalHash A

/-- The finite reduction bounds success on short messages and uses at most four table calls. -/
example (F : Bool → Bool × Fin 2 → BitString 2)
    (A : ProbComp (CollisionGuess {m : List Bool // m.length ≤ 2})) :
    ProbComp.eval (collisionExperiment (fun k => xorHash (F k)) A) true ≤
      (PRF.advantage F (xorHashCollisionReduction A) : ℝ≥0∞) +
        (Fintype.card (BitString 2) : ℝ≥0∞)⁻¹ ∧
    (xorHashCollisionReduction (Y := BitString 2) A).IsQueryBounded 4 :=
  ⟨eval_collisionExperiment_xorHash_le_prfAdvantage F A,
    isQueryBounded_xorHashCollisionReduction A⟩

/-- Three messages of at most two blocks give three candidate pairs and at most six queries. -/
example (F : Bool → Bool × Fin 2 → BitString 2)
    (A : ProbComp (List {m : List Bool // m.length ≤ 2}))
    (hA : ∀ ms ∈ (ProbComp.eval A).support, ms.length ≤ 3) :
    ProbComp.eval (multiQueryExperiment (fun k => xorHash (F k)) A) true ≤
      (PRF.advantage F (xorHashMultiQueryReduction 3 A) : ℝ≥0∞) +
        (3 : ℝ≥0∞) * (Fintype.card (BitString 2) : ℝ≥0∞)⁻¹ ∧
    (xorHashMultiQueryReduction (Y := BitString 2) 3 A).IsQueryBounded 6 := by
  refine ⟨?_, isQueryBounded_xorHashMultiQueryReduction 3 A⟩
  simpa only [show (3 : ℕ).choose 2 = 3 by decide, Nat.cast_ofNat] using
    eval_multiQueryExperiment_xorHash_le_prfAdvantage F A hA

/-- The wrapper rejects a repeated message and detects the collision once it sees a distinct one. -/
example :
    let m₀ : {m : List Bool // m.length ≤ 1} := ⟨[false], by decide⟩
    let m₁ : {m : List Bool // m.length ≤ 1} := ⟨[true], by decide⟩
    let A : ProbComp (List {m : List Bool // m.length ≤ 1}) := pure [m₀, m₀, m₁]
    let oracle (_ : Bool × Fin 1) : ProbComp (BitString 2) := pure 0
    (xorHashMultiQueryReduction 2 A).run oracle = pure false ∧
      (xorHashMultiQueryReduction 3 A).run oracle = pure true :=
  ⟨rfl, rfl⟩

/-- Equal blocks at different positions use different queries, and the extra block is ignored. -/
example :
    (xorHashWordQueries 2 2 [[false], [false], [true]]).run
        (fun q => pure (if q.2.headD false then [true, true] else [false, true])) =
      pure [true, false] := rfl

/-- No reply is needed to produce the initial zero digest for an empty message. -/
example :
    (xorHashWordQueries 2 2 []).run (fun _ => pure []) = pure [false, false] := rfl

/-- A constant table produces a collision for distinct valid one-bit messages. -/
example :
    (xorHashWordCollisionReduction (fun _ => 2) (fun _ => 1) (fun _ => 1)
        (fun _ => pure ⟨[[true]], [[false]]⟩) 0 []).run (fun _ => pure [true]) =
      pure true := rfl

/-- A malformed block loses even when the constant table would give equal digests. -/
example :
    (xorHashWordCollisionReduction (fun _ => 2) (fun _ => 1) (fun _ => 1)
        (fun _ => pure ⟨[[true, false]], [[false]]⟩) 0 []).run (fun _ => pure [true]) =
      pure false := rfl

open Turing.MultiTapeTM in
/-- A two-block cap and `n`-bit blocks and digests instantiate the security result. -/
example {family : List Bool → List Bool → List Bool}
    (hPRF : PseudorandomFunctionOver (fun n => 2 + n) id family) :
    IsComputationalUHF encUnary (encList encBits) (fun n => pure n)
      (fun _ n => xorHashWordValid 2 n)
      (fun _ => xorHashWordFamily (fun _ => 2) id id family) :=
  isComputationalUHF_xorHashWordFamily hPRF (.const 2) .id' negligible_inv_two_pow

/-- Only a distinct valid message within the cap produces a collision under a constant table. -/
example :
    let A : ℕ × ℕ → ProbComp (List (List (List Bool))) :=
      fun _ => pure [[[false]], [[false]], [[true, true]], [[true]]]
    let B := xorHashWordMultiQueryReduction (fun _ => 2) (fun _ => 1) (fun _ => 1)
    (B (fun _ => 3) A 0 []).run (fun _ => pure [true]) = pure false ∧
      (B (fun _ => 4) A 0 []).run (fun _ => pure [true]) = pure true ∧
      (B (fun _ => 4) A 0 []).IsQueryBounded 8 :=
  ⟨rfl, rfl, isQueryBounded_xorHashWordMultiQueryReduction _ _ _ _ _ _ _⟩

/-- The direct bound applies to two valid one-block messages and three-bit digests. -/
example :
    let ℓ : ℕ → ℕ := fun _ => 2
    let blockWidth : ℕ → ℕ := fun _ => 1
    let width : ℕ → ℕ := fun _ => 3
    let Q : ℕ → ℕ := fun _ => 2
    let A : ℕ × ℕ → ProbComp (List (List (List Bool))) :=
      fun _ => pure [[[false]], [[true]]]
    let F : List Bool → List Bool → List Bool := fun _ _ => [false, false, false]
    let B := xorHashWordMultiQueryReduction ℓ blockWidth width Q A
    Game.succProbability
        (multiQueryGame (fun n => pure n) (fun _ n => xorHashWordValid (ℓ n) (blockWidth n))
          (fun _ => xorHashWordFamily ℓ blockWidth width F) A 0) ≤
      Game.advantage (ProbComp.eval (prfRealGame (fun n => ℓ n + blockWidth n) F B 0))
        (ProbComp.eval (prfIdealGame (fun n => ℓ n + blockWidth n) width B 0)) + 1 / 4 := by
  intro ℓ blockWidth width Q A F B
  have hquarter : ((Q 0 : ℝ≥0) ^ 2 / 2) * ((2 : ℝ≥0) ^ width 0)⁻¹ = 1 / 4 := by
    norm_num [Q, width]
  have hcap : ∀ ms ∈ (ProbComp.eval (A (0, 0))).support, ms.length ≤ Q 0 := by
    intro ms hms
    simp only [A, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hms
    subst ms
    decide
  simpa only [hquarter] using
    succProbability_multiQueryGame_xorHashWordFamily_le (ℓ := ℓ) (blockWidth := blockWidth)
      (width := width) F (fun _ _ _ => rfl) A 0 hcap

private def echoGuess (target : Bool) : PredictionAdversary Bool Bool Unit where
  choose _ := pure (false, ())
  guess _ digest := pure ⟨target, digest⟩

example : ProbComp.eval (predictionExperiment (fun k : Bool => fun _ => k) (echoGuess true))
    true = 1 := by
  simp [predictionExperiment, echoGuess, ProbComp.eval_uniform, ENNReal.mul_inv_cancel]

example : ProbComp.eval (predictionExperiment (fun k : Bool => fun _ => k) (echoGuess false))
    true = 0 := by
  simp [predictionExperiment, echoGuess, ProbComp.eval_uniform]

/-- Masked `Hxpoly` gives a one-time MAC for bounded-length messages. -/
example {F σ : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (A : TwoStage Unit {m : List F // m.length ≤ ℓ} F
      ({m : List F // m.length ≤ ℓ} × F) σ) :
    let H (key : F × F) (m : {m : List F // m.length ≤ ℓ}) := xpolyHash key.1 m.val + key.2
    ProbComp.eval (oneTimeForgeExperiment (ProbComp.uniform (F × F)) (fun k m => pure (H k m))
      (fun k m t => decide (H k m = t)) (A.choose ()) A.guess) true ≤ (ℓ + 1) / Fintype.card F :=
  oneTimeForgeExperiment_hash_le
    (isPairwiseUnpredictable_add_uniform (isDeltaUniversalHash_xpolyHash (F := F) ℓ)) A

private def repeatWithWrongTag : TwoStage Unit Bool Bool (Bool × Bool) Unit where
  choose _ := pure (false, ())
  guess _ tag := pure (false, !tag)

/-- A fresh pair with the queried message and a different tag fails equality verification. -/
example : ProbComp.eval
    (oneTimeForgeExperiment (pure ()) (fun _ _ => pure true)
      (fun _ _ t => decide (true = t))
      (repeatWithWrongTag.choose ()) repeatWithWrongTag.guess) true = 0 := by
  simp [oneTimeForgeExperiment, repeatWithWrongTag]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A one-block cap suffices for the deterministic attack, with both prime-field stages PPT. -/
example : ProbComp.eval
    (predictionExperiment
      (fun k (m : {m : List (ZMod 5) // m.length ≤ 1}) => xpolyHash k m.val)
      (xpolyPrediction le_rfl)) true = 1 ∧
    TwoStage.IsPPT Turing.MultiTapeTM.encUnit (encXpolyMessage 5 1)
      (Turing.MultiTapeTM.encZMod 5) (encPredictionGuess (encXpolyMessage 5 1)
        (Turing.MultiTapeTM.encZMod 5)) Turing.MultiTapeTM.encUnit
      (fun _ => xpolyPrediction le_rfl) :=
  ⟨eval_predictionExperiment_xpolyHash le_rfl, isPPT_xpolyPrediction le_rfl⟩

end Cslib.Crypto.UHF.Tests
