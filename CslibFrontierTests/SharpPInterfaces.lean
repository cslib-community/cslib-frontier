/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of counting interfaces)

import CslibFrontier.Computability.Complexity.Classes.SharpP.Threshold
import CslibFrontier.Computability.Complexity.Classes.SharpP.AdditiveApproximation
import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Checked clients for Goldreich's counting interfaces

The threshold boundary attains the exponential upper bound; short-word solutions have different
lengths; the empty certificate can be a solution; and the easy-search theorem is instantiated
with Valiant's existing complete count, not an assumed completeness theorem for a new problem.
-/

set_option linter.privateModule false

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

-- Inclusive threshold and the extra count bit when `f = 2 ^ p`.
example : PolyTimeOracleProgram (encPair encBits encNat) encBool
    (AnswersBits encBits (fun _ : List Bool => 1))
    (· = fun q : List Bool × ℕ => decide (q.2 ≤ 1)) :=
  threshold_polyTimeOracleProgram (p := 0) (by simp)

example : ComputableInPolyTimeWithOracle
    ((encPair encBits encNat) '' {q : List Bool × ℕ | q.2 ≤ 1})
    (fun _ : List Bool => 1) encBits encNat :=
  computableInPolyTimeWithOracle_threshold (enc := encBits)
    (f := fun _ => 1) (p := 0) (by simp)

example : ComputableInPolyTimeWithOracle
    ((encPair encBits encNat) '' {q : List Bool × ℕ | q.2 = 0})
    (fun _ : List Bool => 0) encBits encNat := by
  simpa using computableInPolyTimeWithOracle_threshold (enc := encBits)
    (f := fun _ => 0) (p := 0) (by simp)

-- Three solutions, including the empty word: exact-length padding must preserve all three.
example : (fun (_ : List Bool) (w : List Bool) => w.length ≤ 1) ∈ FNP encBits := by
  refine ⟨⟨1, fun _ _ h => by simpa using h⟩, fun q => decide (q.2.length ≤ 1), ?_, ?_⟩
  · exact ComputableInPolyTime.unary_le'
      (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const 1)
  · simp

example (a : List Bool) : searchCount (fun (_ : List Bool) w => w.length ≤ 1) a = 3 := by
  let e : {w : List Bool // w.length ≤ 1} ≃ Option Bool :=
    { toFun := fun w => w.val.head?
      invFun := fun o => ⟨o.toList, by cases o <;> simp⟩
      left_inv := fun ⟨w, hw⟩ => by
        apply Subtype.ext
        cases w with
        | nil => rfl
        | cons b rest =>
          have : rest = [] := by simpa using hw
          subst rest
          rfl
      right_inv := fun o => by cases o <;> rfl }
  simpa only [searchCount, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_bool]
    using Nat.card_congr e

example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) :
    searchCount R.IsWitness ∈ SharpP enc :=
  searchCount_mem_SharpP R.isWitness_mem_FNP

example {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop} (hR : R ∈ FNP enc)
    (h : ∀ {β : Type} (encB : β ↪ List Bool) (S : β → List Bool → Prop),
      S ∈ FNP encB → ∃ r : β → α, ComputableInPolyTime r encB enc ∧
        ∀ b, Nonempty ({w // S b w} ≃ {w // R (r b) w})) :
    SharpPComplete enc (searchCount R) := by
  apply sharpPComplete_searchCount hR
  intro β encB S hS
  obtain ⟨r, hr, hequiv⟩ := h encB S hS
  exact ⟨r, hr, fun b => Nat.card_congr (hequiv b).some⟩

example : ∃ R : List (List Bool) → List Bool → Prop, R ∈ FPSearch encBoolTable ∧
    IsTotalSearch R ∧ SharpPMetricComplete encBoolTable (searchCount R) :=
  exists_mem_FPSearch_sharpPMetricComplete

example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) :
    IsPPTOn (NPRelation.encAdditiveApproximationInput enc) (encPair encNat encNat)
      (fun q : α × ℕ × ℕ => R.additiveEstimate q.1 q.2.1 q.2.2) :=
  R.isPPTOn_additiveEstimate

-- Fix polynomial inverse accuracy: runtime is polynomial in instance length and unary `t`.
example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) (p : Polynomial ℕ) :
    IsPPTOn (encPair enc encUnary) (encPair encNat encNat)
      (fun q : α × ℕ => R.additiveEstimate q.1 (p.eval (enc q.1).length) q.2) := by
  apply R.isPPTOn_additiveEstimate.preprocess
    (prepare := fun q : α × ℕ => (q.1, p.eval (enc q.1).length, q.2))
  exact (ComputableInPolyTime.fst _ _).prod
    (((ComputableInPolyTime.unary_eval p).comp
      ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst _ _))).prod
      (ComputableInPolyTime.snd _ _))

example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) (a : α) {k : ℕ}
    (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ((ProbComp.eval (R.additiveEstimate a k (Nat.clog 2 ⌈δ⁻¹⌉₊))).toOuterMeasure {out |
      (2 : ℝ) ^ R.certLength.eval (enc a).length / k <
        |(out.1 : ℝ) / out.2 - searchCount R.IsWitness a|}).toReal < δ :=
  R.additiveEstimate_error_confidence a hk hδ hδ₁

-- Zero-length certificates: accepting/rejecting the empty word gives one/zero solutions.
example (a : List Bool) :
    searchCount (⟨0, fun _ => false, .const false⟩ : NPRelation encBits).IsWitness a = 0 := by
  rw [NPRelation.searchCount_eq]
  exact acceptCount_false _ _

example (a : List Bool) :
    searchCount (⟨0, fun _ => true, .const true⟩ : NPRelation encBits).IsWitness a = 1 := by
  rw [NPRelation.searchCount_eq, acceptCount_true]
  simp

-- Unit accuracy and confidence zero are admitted, for every relation.
example {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) (a : α) :
    ((ProbComp.eval (R.additiveEstimate a 1 0)).toOuterMeasure {out |
      (2 : ℝ) ^ R.certLength.eval (enc a).length <
        |(out.1 : ℝ) / out.2 - searchCount R.IsWitness a|}).toReal < 1 := by
  simpa only [Nat.cast_one, div_one, pow_zero] using
    R.additiveEstimate_error a (k := 1) (by decide) 0

-- Exercise 6.23 is the existing identity, not Proposition 6.23 above.
example (A : List (List Bool)) : BipartitePerfectMatchingCount A = ZeroOnePermanent A :=
  bipartitePerfectMatchingCount_eq_zeroOnePermanent A
