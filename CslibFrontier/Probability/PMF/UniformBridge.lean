/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.Product
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Bridging finite-set counting and averages to uniform `PMF`s

Connects `Finset` filter cardinalities (`(s.filter P).card`) and uniform averages (`𝔼 x ∈ s, f x`,
`𝔼 x, f x`) to event probabilities, level-set sums, and expectations under `PMF.uniformOfFinset`
and `PMF.uniformOfFintype`. Combinatorial counting bounds and finite quantile existence on arbitrary
types then follow directly from the `PMF` theorems in `Probability.Concentration`,
`Probability.BoundedDifferences`, and `Probability.Quantile`.

## Main results

* `Cslib.Probability.PMF.card_filter_eq_card_mul_toOuterMeasure_uniformOfFinset`,
  `Cslib.Probability.PMF.card_filter_le_of_toOuterMeasure_uniformOfFinset_le`: subset filter counts
  from `uniformOfFinset` event probabilities.
* `Cslib.Probability.PMF.card_filter_univ_eq_card_mul_toOuterMeasure_uniformOfFintype`,
  `Cslib.Probability.PMF.card_filter_univ_le_of_toOuterMeasure_uniformOfFintype_le`,
  `Cslib.Probability.PMF.card_filter_pi_le_of_toOuterMeasure_le`: whole-type and product-space
  filter counts from `uniformOfFintype` / `PMF.pi` event probabilities.
* `Cslib.Probability.PMF.tsum_uniformOfFinset_toReal_mul`,
  `Cslib.Probability.PMF.sum_uniformOfFinset_toReal_mul`,
  `Cslib.Probability.PMF.sum_uniformOfFintype_toReal_mul`,
  `Cslib.Probability.PMF.sum_pi_uniformOfFintype_toReal_mul`: uniform `PMF` expectations equal `𝔼`.
* `Cslib.Probability.PMF.sum_subtype_uniformOfFintype_ite_toReal`: indicator sums on `↥s` equal
  filter density `(s.filter P).card / s.card`, without requiring `[Fintype α]`.
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators ENNReal

variable {α : Type*}

/-! ### Filter counts and event probabilities -/

/-- The number of elements of a nonempty `s : Finset α` satisfying `P` is `#s` times the
probability of `{x | P x}` under `uniformOfFinset s hs`. -/
theorem card_filter_eq_card_mul_toOuterMeasure_uniformOfFinset (s : Finset α) (hs : s.Nonempty)
    (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) =
      s.card * ((uniformOfFinset s hs).toOuterMeasure {x | P x}).toReal := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
  rw [toOuterMeasure_uniformOfFinset_toReal s hs {x | P x}]
  simp only [Set.mem_ofPred_eq]
  exact (mul_div_cancel₀ _ hcard).symm

/-- An upper bound `B` on the `uniformOfFinset` probability of `{x | P x}` bounds
`(s.filter P).card` by `#s * B`. -/
theorem card_filter_le_of_toOuterMeasure_uniformOfFinset_le (s : Finset α) (hs : s.Nonempty)
    (P : α → Prop) [DecidablePred P] {B : ℝ}
    (h : ((uniformOfFinset s hs).toOuterMeasure {x | P x}).toReal ≤ B) :
    ((s.filter P).card : ℝ) ≤ s.card * B := by
  rw [card_filter_eq_card_mul_toOuterMeasure_uniformOfFinset s hs P]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg s.card)

/-- On a nonempty finite type, `#{x | P x}` is `Fintype.card α` times the `uniformOfFintype`
probability of `{x | P x}`. -/
theorem card_filter_univ_eq_card_mul_toOuterMeasure_uniformOfFintype [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    (#{x : α | P x} : ℝ) =
      Fintype.card α * ((uniformOfFintype α).toOuterMeasure {x | P x}).toReal := by
  simpa [uniformOfFintype] using
    card_filter_eq_card_mul_toOuterMeasure_uniformOfFinset Finset.univ Finset.univ_nonempty P

/-- An upper bound `B` on the `uniformOfFintype` probability of `{x | P x}` bounds `#{x | P x}` by
`Fintype.card α * B`. -/
theorem card_filter_univ_le_of_toOuterMeasure_uniformOfFintype_le [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] {B : ℝ}
    (h : ((uniformOfFintype α).toOuterMeasure {x | P x}).toReal ≤ B) :
    (#{x : α | P x} : ℝ) ≤ Fintype.card α * B := by
  rw [card_filter_univ_eq_card_mul_toOuterMeasure_uniformOfFintype P]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/-- Counting bound on `ι → β` from a tail bound under `pi (fun _ : ι => uniformOfFintype β)`. -/
theorem card_filter_pi_le_of_toOuterMeasure_le {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] (P : (ι → β) → Prop) [DecidablePred P] {B : ℝ}
    (h : ((pi fun _ : ι => uniformOfFintype β).toOuterMeasure {x | P x}).toReal ≤ B) :
    (#{x : ι → β | P x} : ℝ) ≤ (Fintype.card β : ℝ) ^ Fintype.card ι * B := by
  rw [pi_uniformOfFintype] at h
  simpa [Fintype.card_fun] using card_filter_univ_le_of_toOuterMeasure_uniformOfFintype_le P h

/-! ### Uniform expectations and subtype indicator sums -/

/-- The expectation of `f` under `uniformOfFinset s hs` equals the `Finset` average `𝔼 x ∈ s, f x`,
without assuming `[Fintype α]`. -/
theorem tsum_uniformOfFinset_toReal_mul (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    (∑' x, ((uniformOfFinset s hs) x).toReal * f x) = 𝔼 x ∈ s, f x := by
  classical
  rw [tsum_eq_sum fun x (hx : x ∉ s) => by simp [uniformOfFinset_apply, hx],
    expect_eq_sum_div_card, sum_div]
  refine sum_congr rfl fun x hx => ?_
  simp [uniformOfFinset_apply, hx, div_eq_inv_mul]

/-- Finite-type sum form of `tsum_uniformOfFinset_toReal_mul`. -/
theorem sum_uniformOfFinset_toReal_mul [Fintype α] (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    (∑ x, ((uniformOfFinset s hs) x).toReal * f x) = 𝔼 x ∈ s, f x := by
  have h := tsum_uniformOfFinset_toReal_mul s hs f
  rwa [tsum_fintype] at h

/-- The expectation of `f` under `uniformOfFintype α` equals `𝔼 x, f x`. -/
theorem sum_uniformOfFintype_toReal_mul [Fintype α] [Nonempty α] (f : α → ℝ) :
    (∑ x, ((uniformOfFintype α) x).toReal * f x) = 𝔼 x, f x := by
  simpa [uniformOfFintype] using sum_uniformOfFinset_toReal_mul Finset.univ Finset.univ_nonempty f

/-- The expectation of `f` under independent uniform coordinates `pi (fun _ => uniformOfFintype β)`
equals `𝔼 x, f x`. -/
theorem sum_pi_uniformOfFintype_toReal_mul {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] (f : (ι → β) → ℝ) :
    (∑ x, ((pi fun _ : ι => uniformOfFintype β) x).toReal * f x) = 𝔼 x, f x := by
  rw [pi_uniformOfFintype]
  exact sum_uniformOfFintype_toReal_mul f

/-- Over the finite subtype `↥s` of a nonempty `s : Finset α`, summing the uniform mass where `P`
holds gives `(s.filter P).card / s.card`, without requiring `[Fintype α]`. -/
theorem sum_subtype_uniformOfFintype_ite_toReal (s : Finset α) [Nonempty s] (P : α → Prop)
    [DecidablePred P] :
    (∑ x : s, if P x.1 then ((uniformOfFintype s) x).toReal else 0) =
      (s.filter P).card / s.card := by
  simp only [uniformOfFintype_apply, Fintype.card_coe, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 2
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp [and_comm]

end Cslib.Probability.PMF
