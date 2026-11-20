/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID.CollisionCount
public import CslibFrontier.Probability.PMF.Event
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Probability.PMF.UniformSubset
import Mathlib.Data.Nat.Choose.Cast

/-!
# Distinct independent samples

A noninjective sample tuple has at least one colliding pair. The first moment of the
existing collision count therefore bounds the probability of repetitions by
`choose k 2 * collisionProbability μ`. A bound on each point mass gives the usual birthday
union bound without a uniformity assumption. This is the sampling estimate used in
[ChukhinKulikovMihajlinSmal2026], proof of Lemma 5.2, printed p. 10 (PDF p. 11).

## Main results

* `collisionCount_eq_zero_iff`: a tuple has no colliding pairs exactly when it is injective.
* `iid_not_injective_le`: the collision first-moment bound.
* `iid_not_injective_le_of_mass_le`: the point-mass version used for distinct input tuples.
* `iid_injective_pair_ge`: the sum of the two light-atom tuple-validity probabilities.
-/

public section
namespace Cslib.Probability.PMF
open Finset
open scoped BigOperators
variable {α : Type*}

/-- A sample tuple has no colliding pair precisely when all entries are distinct. -/
theorem collisionCount_eq_zero_iff [DecidableEq α] {k : ℕ} (x : Fin k → α) :
    collisionCount x = 0 ↔ Function.Injective x := by
  rw [collisionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies, not_and]
  constructor
  · intro h i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact @h (i, j) hij heq
    · exact @h (j, i) hji heq.symm
  · intro h ij hlt heq
    exact (ne_of_lt hlt) (h heq)

variable [Finite α]

/-- The probability of any repetition is at most the expected number of colliding pairs. -/
theorem iid_not_injective_le (μ : PMF α) (k : ℕ) :
    ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤
      k.choose 2 * collisionProbability μ := by
  classical
  have := Fintype.ofFinite α
  rw [toOuterMeasure_apply_toReal, ← sum_iid_mul_collisionCount]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : Function.Injective x
  · simp only [Set.mem_ofPred_eq, hx, not_true_eq_false, ite_false]
    positivity
  · simp only [Set.mem_ofPred_eq, hx, not_false_eq_true, ite_true]
    have hcount : 1 ≤ collisionCount x := Nat.one_le_iff_ne_zero.mpr
      (fun h => hx ((collisionCount_eq_zero_iff x).mp h))
    have hc : (1 : ℝ) ≤ collisionCount x := by exact_mod_cast hcount
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
      (ENNReal.toReal_nonneg (a := iid μ k x))

/-- If every atom has mass at most `bound`, repetitions among `k` independent draws
have probability at most `choose k 2 * bound`, even for a nonuniform source. -/
theorem iid_not_injective_le_of_mass_le (μ : PMF α) (k : ℕ) {bound : ℝ}
    (h : ∀ a, (μ a).toReal ≤ bound) :
    ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤ k.choose 2 * bound :=
  (iid_not_injective_le μ k).trans
    (mul_le_mul_of_nonneg_left (collisionProbability_le_of_mass_le μ h) (by positivity))

/-- A lower bound for receiving an injective tuple, in real probability units. -/
theorem iid_injective_ge_of_mass_le (μ : PMF α) (k : ℕ) {bound : ℝ}
    (h : ∀ a, (μ a).toReal ≤ bound) :
    1 - k.choose 2 * bound ≤ ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal := by
  have hc := toOuterMeasure_toReal_add_compl (iid μ k) {x | Function.Injective x}
  have hb := iid_not_injective_le_of_mass_le μ k h
  change _ + ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal = 1 at hc
  linarith

/-- The two distinct-tuple probabilities in the light-atom case of submission 865.
Their sum exceeds one by at least `1/k`; the source subsequently telescopes `k` hybrid steps. -/
theorem iid_injective_pair_ge {β : Type*} [Finite β] (μ : PMF α) (ν : PMF β)
    (k : ℕ) (hk : 0 < k)
    (hμ : ∀ a, (μ a).toReal ≤ ((k : ℝ) ^ 2)⁻¹)
    (hν : ∀ b, (ν b).toReal ≤ ((k : ℝ) ^ 2)⁻¹) :
    1 + (k : ℝ)⁻¹ ≤ ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal +
      ((iid ν k).toOuterMeasure {y | Function.Injective y}).toReal := by
  have hl := iid_injective_ge_of_mass_le μ k hμ
  have hr := iid_injective_ge_of_mass_le ν k hν
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have heq : 2 - 2 * (k.choose 2 : ℝ) * ((k : ℝ) ^ 2)⁻¹ = 1 + (k : ℝ)⁻¹ := by
    rw [Nat.cast_choose_two]
    field_simp [hk']; ring
  linarith

/-- Averaging a bounded score over ordered distinct draws can increase its expectation
by at most the birthday bound for independent uniform draws. -/
theorem expect_embedding_le_expect_add [Fintype α] [Nonempty α] (k : ℕ)
    [Nonempty (Fin k ↪ α)] (f : (Fin k → α) → ℝ) (h₀ : ∀ a, 0 ≤ f a) (h₁ : ∀ a, f a ≤ 1) :
    letI : Fintype (Fin k ↪ α) := Fintype.ofFinite _
    (𝔼 x : Fin k ↪ α, f x) ≤ (𝔼 a, f a) + (k.choose 2 : ℝ) / Fintype.card α := by
  classical
  let _ : Fintype (Fin k ↪ α) := Fintype.ofFinite _
  let s := (univ : Finset (Fin k → α)).filter Function.Injective
  have hs : s.Nonempty := by
    let x := Classical.choice (inferInstance : Nonempty (Fin k ↪ α))
    exact ⟨x, mem_filter.mpr ⟨mem_univ _, x.injective⟩⟩
  have hrepr : (𝔼 x : Fin k ↪ α, f x) = 𝔼 a ∈ s, f a := by
    refine Finset.expect_nbij (fun x : Fin k ↪ α => (x : Fin k → α))
      (fun x _ => mem_filter.mpr ⟨mem_univ _, x.injective⟩) (fun _ _ => rfl)
      (fun x _ y _ h => Function.Embedding.ext fun i => congrFun h i) ?_
    intro a ha
    exact ⟨⟨a, (mem_filter.mp ha).2⟩, mem_univ _, rfl⟩
  change (𝔼 x : Fin k ↪ α, f x) ≤ _
  rw [hrepr]
  refine (expect_finset_le_expect_add_compl s hs f h₀ h₁).trans (add_le_add_right ?_ _)
  have happly (a : α) : (uniformOfFintype α a).toReal ≤ (Fintype.card α : ℝ)⁻¹ := by
    rw [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hcollision := iid_not_injective_le_of_mass_le (uniformOfFintype α) k happly
  rw [iid_uniformOfFintype, ← div_eq_mul_inv] at hcollision
  simpa only [s, mem_filter, mem_univ, true_and] using hcollision

/-- Conditioning on distinct draws can decrease a bounded expectation by at most the
birthday bound for independent uniform draws. -/
theorem expect_le_expect_embedding_add [Fintype α] [Nonempty α] (k : ℕ)
    [Nonempty (Fin k ↪ α)] (f : (Fin k → α) → ℝ) (h₀ : ∀ a, 0 ≤ f a) (h₁ : ∀ a, f a ≤ 1) :
    letI : Fintype (Fin k ↪ α) := Fintype.ofFinite _
    (𝔼 a, f a) ≤ (𝔼 x : Fin k ↪ α, f x) + (k.choose 2 : ℝ) / Fintype.card α := by
  let _ : Fintype (Fin k ↪ α) := Fintype.ofFinite _
  have h := expect_embedding_le_expect_add k (fun a => 1 - f a)
    (fun a => sub_nonneg.mpr (h₁ a)) (fun a => sub_le_self _ (h₀ a))
  simp only [Finset.expect_sub_distrib, Fintype.expect_const] at h
  linarith

end Cslib.Probability.PMF
