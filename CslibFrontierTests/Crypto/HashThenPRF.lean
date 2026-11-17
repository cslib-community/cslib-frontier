/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Primitives.PRF.HashThenPRF
import CslibFrontier.Probability.HashFamily.Polynomial

set_option linter.privateModule false

/-!
# Tests for `PRF(UHF)` composition

Checks the API and hypotheses of `CslibFrontier.Crypto.PRF.HashThenPRF` and
`CslibFrontier.Crypto.UHF.Finite` as a `module` client:
- instantiating `PRF.advantage_hashThenPRF_le` with `coeffPolyHash`;
- equation `(6.17)` (§6.5, p. 231) on `hashThenPRF`;
- `UHF.multiQueryExperiment` on constant hashes, repeated lists, two-query lists, and
  `collisionDistinguisher`;
- tightness/necessity on constant hashes, counterexample when `m₀ = m₁` (`Z = Bool`), comparison
  with `(Q ^ 2 / 2 : ℕ) * ε`, and the query-bound hypothesis probe.
-/

namespace Cslib.Crypto.PRF.Tests

open Cslib.Probability
open scoped ENNReal NNReal

/-! ### Instantiation with `coeffPolyHash` and equation (6.17) (§6.5, p. 231) -/

example {K₂ F Z : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K₂] [Nonempty K₂]
    [Fintype Z] [Nonempty Z] [DecidableEq Z] (n : ℕ) (f : K₂ → F → Z)
    {A : Adversary (Fin n → F) Z} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (advantage (hashThenPRF (fun k (x : Fin n → F) => coeffPolyHash k x) f) A : ℝ≥0∞) ≤
      advantage f (hashReduction (fun k (x : Fin n → F) => coeffPolyHash k x) A) +
        (Q.choose 2 : ℕ) * ((n : ℝ≥0∞) / Fintype.card F) :=
  advantage_hashThenPRF_le (isUniversalHash_coeffPolyHash n) f hQ

example {K₁ K₂ M Y Z : Type} (H : K₁ → M → Y) (F : K₂ → Y → Z) (k : K₁ × K₂) (m : M) :
    hashThenPRF H F k m = F k.2 (H k.1 m) := rfl

/-! ### Multi-query UHF game checks -/

/-- A constant hash wins Attack Game 7.2 on any two distinct messages. -/
private theorem eval_multiQueryExperiment_const_pair {K₁ M Y : Type} [Fintype K₁] [Nonempty K₁]
    [DecidableEq M] [DecidableEq Y] (y₀ : Y) {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    ProbComp.eval (UHF.multiQueryExperiment (fun (_ : K₁) (_ : M) => y₀) (pure [m₀, m₁])) true =
      1 := by
  have hcol : decide (∃ m ∈ [m₀, m₁], ∃ m' ∈ [m₀, m₁], m ≠ m' ∧ True) = true :=
    decide_eq_true ⟨m₀, by simp, m₁, by simp, hm, trivial⟩
  simp only [UHF.multiQueryExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, hcol, PMF.bind_const, PMF.pure_apply, ↓reduceIte]

example {K₁ M Y : Type} [Fintype K₁] [Nonempty K₁] [DecidableEq M] [DecidableEq Y]
    (H : K₁ → M → Y) (m : M) :
    ProbComp.eval (UHF.multiQueryExperiment H (pure [m, m])) true = 0 := by
  have hno : ∀ k : K₁,
      decide (∃ x ∈ [m, m], ∃ x' ∈ [m, m], x ≠ x' ∧ H k x = H k x') = false := fun k => by
    apply decide_eq_false
    rintro ⟨x, hx, x', hx', hne, -⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> exact hne rfl
  simp only [UHF.multiQueryExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, hno, PMF.bind_const, PMF.pure_apply, Bool.true_eq_false,
    ↓reduceIte]

example {K₁ M Y : Type} [Fintype K₁] [Nonempty K₁] [DecidableEq M] [DecidableEq Y]
    {H : K₁ → M → Y} {ε : ℝ≥0∞} (hH : IsUniversalHash (PMF.uniformOfFintype K₁) H ε)
    (m₀ m₁ : M) :
    ProbComp.eval (UHF.multiQueryExperiment H (pure [m₀, m₁])) true ≤ ε := by
  have hle := UHF.eval_multiQueryExperiment_le (B := pure [m₀, m₁]) (Q := 2) hH fun ms hms => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hms
    subst hms
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, le_refl]
  simpa only [Nat.choose_self, Nat.cast_one, one_mul] using hle

example {M Z : Type} [DecidableEq Z] (m₀ m₁ : M) :
    (collisionDistinguisher (Z := Z) m₀ m₁).IsQueryBounded 2 :=
  isQueryBounded_collisionDistinguisher m₀ m₁

/-! ### Necessity, failure probe when `m₀ = m₁`, book comparison, and query-bound probe -/

example {K₁ K₂ M Y Z : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂] [Fintype M]
    [DecidableEq M] [Fintype Z] [Nonempty Z] [DecidableEq Z] (y₀ : Y) (F : K₂ → Y → Z)
    {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    (1 : ℝ≥0∞) ≤
      advantage (hashThenPRF (fun (_ : K₁) (_ : M) => y₀) F) (collisionDistinguisher m₀ m₁) +
        (Fintype.card Z : ℝ≥0∞)⁻¹ := by
  have h := toOuterMeasure_collision_le_advantage_collisionDistinguisher
    (fun (_ : K₁) (_ : M) => y₀) F hm
  have huniv : (PMF.uniformOfFintype K₁).toOuterMeasure {k | y₀ = y₀} = 1 := by
    simp only [PMF.toOuterMeasure_apply, Set.mem_ofPred_eq, Set.indicator_of_mem,
      PMF.uniformOfFintype_apply, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  exact huniv ▸ h

private theorem advantage_collisionDistinguisher_self {K₁ K₂ M Y Z : Type} [Fintype K₁]
    [Nonempty K₁] [Fintype K₂] [Nonempty K₂] [Fintype M] [DecidableEq M] [Fintype Z]
    [Nonempty Z] [DecidableEq Z] (H : K₁ → M → Y) (F : K₂ → Y → Z) (m₀ : M) :
    advantage (hashThenPRF H F) (collisionDistinguisher m₀ m₀) = 0 := by
  have hreal :
      ProbComp.eval (realExperiment (hashThenPRF H F) (collisionDistinguisher m₀ m₀)) =
        PMF.pure true := by
    rw [eval_realExperiment_collisionDistinguisher]
    simp only [decide_true, PMF.bind_const]
  have hideal :
      ProbComp.eval (idealExperiment (collisionDistinguisher (Z := Z) m₀ m₀)) = PMF.pure true := by
    rw [eval_idealExperiment_collisionDistinguisher]
    simp only [decide_true, PMF.bind_const]
  rw [advantage, hreal, hideal, Game.advantage_self]

example :
    ¬ ((1 : ℝ≥0∞) ≤
      (advantage (hashThenPRF (fun (_ : Unit) (_ : Unit) => ()) (fun (_ : Unit) (_ : Unit) => true))
        (collisionDistinguisher () ()) : ℝ≥0∞) + (Fintype.card Bool : ℝ≥0∞)⁻¹) := by
  rw [advantage_collisionDistinguisher_self]
  norm_num

example {K₁ K₂ M Y Z : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂] [Fintype M]
    [DecidableEq M] [Fintype Y] [DecidableEq Y] [Fintype Z] [Nonempty Z]
    {H : K₁ → M → Y} {ε : ℝ≥0∞} (hH : IsUniversalHash (PMF.uniformOfFintype K₁) H ε)
    (F : K₂ → Y → Z) {A : Adversary M Z} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (advantage (hashThenPRF H F) A : ℝ≥0∞) ≤
      advantage F (hashReduction H A) + ((Q ^ 2 / 2 : ℕ) : ℝ≥0∞) * ε := by
  refine (advantage_hashThenPRF_le hH F hQ).trans ?_
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) bot_le)
  rw [Nat.choose_two_right, sq]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left Q (Nat.sub_le Q 1))

example : Nat.choose 2 2 < 2 ^ 2 / 2 := by decide

example {K₁ M Y : Type} [Fintype K₁] [Nonempty K₁] [DecidableEq M] [DecidableEq Y]
    (y₀ : Y) {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    ¬ ([m₀, m₁].length ≤ 1) ∧
      ProbComp.eval (UHF.multiQueryExperiment (fun (_ : K₁) (_ : M) => y₀) (pure [m₀, m₁])) true =
        1 :=
  ⟨by simp, eval_multiQueryExperiment_const_pair y₀ hm⟩

end Cslib.Crypto.PRF.Tests
