/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Additivity and the union bound for discrete outer measures

The outer measure of a discrete distribution is additive on disjoint events: every set is
Carathéodory-measurable for it (`PMF.toOuterMeasure_caratheodory`). For arbitrary events it is
subadditive; since every probability is finite, the union bound also holds for the real-valued
probabilities `(p.toOuterMeasure s).toReal`. The counting bound `sum_toReal_indicator_le`
generalizes the disjoint case to events that overlap at most `Q` times.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_union_of_disjoint`: additivity on two disjoint events.
* `Cslib.Probability.PMF.toOuterMeasure_biUnion_finset`: additivity on finitely many pairwise
  disjoint events.
* `Cslib.Probability.PMF.sum_toOuterMeasure_le_one`: the probabilities of finitely many pairwise
  disjoint events add up to at most `1`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le`: the union bound for
  real-valued probabilities of finitely many events.
* `Cslib.Probability.PMF.sum_toReal_indicator_le`: if every outcome satisfies at most `Q` of
  finitely many predicates, their probabilities add up to at most `Q`.
* `Cslib.Probability.PMF.toOuterMeasure_lookup_isSome_le`: the union bound for finding a random
  key in an association list.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- The probability of a union of two disjoint events is the sum of their probabilities. -/
theorem toOuterMeasure_union_of_disjoint (p : PMF α) {s t : Set α} (h : Disjoint s t) :
    p.toOuterMeasure (s ∪ t) = p.toOuterMeasure s + p.toOuterMeasure t := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  exact tsum_congr fun y => congrFun (Set.indicator_union_of_disjoint h (⇑p)) y

/-- The probability of a union of finitely many pairwise disjoint events is the sum of their
probabilities. -/
theorem toOuterMeasure_biUnion_finset {ι : Type*} (p : PMF α) (J : Finset ι) {B : ι → Set α}
    (hB : (J : Set ι).PairwiseDisjoint B) :
    p.toOuterMeasure (⋃ j ∈ J, B j) = ∑ j ∈ J, p.toOuterMeasure (B j) := by
  simp only [PMF.toOuterMeasure_apply, Finset.indicator_biUnion J B hB]
  exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- The probabilities of finitely many pairwise disjoint events add up to at most `1`. -/
theorem sum_toOuterMeasure_le_one {ι : Type*} (p : PMF α) (J : Finset ι) {B : ι → Set α}
    (hB : (J : Set ι).PairwiseDisjoint B) : ∑ j ∈ J, p.toOuterMeasure (B j) ≤ 1 := by
  simpa only [← toOuterMeasure_biUnion_finset p J hB] using toOuterMeasure_le_one p _

/-- **Union bound** for real-valued probabilities: the probability of a union of finitely many
events is at most the sum of their probabilities. -/
theorem toOuterMeasure_toReal_biUnion_finset_le {ι : Type*} (p : PMF α) (J : Finset ι)
    (B : ι → Set α) :
    (p.toOuterMeasure (⋃ j ∈ J, B j)).toReal ≤ ∑ j ∈ J, (p.toOuterMeasure (B j)).toReal := by
  rw [← ENNReal.toReal_sum fun j _ => toOuterMeasure_ne_top p (B j)]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => toOuterMeasure_ne_top p (B j))
    (MeasureTheory.measure_biUnion_finset_le J B)

/-- If each outcome in the support of `p : PMF α` satisfies `pred x m = true` for at most `Q`
indices `m : M`, then the sum over `m : M` of `Pr_{x ← p}[pred x m = true]` is at most `Q`. -/
theorem sum_toReal_indicator_le {M : Type*} [Fintype M] (p : PMF α)
    (pred : α → M → Bool) (Q : ℕ)
    (hcard : ∀ x ∈ p.support, (Finset.univ.filter fun m => pred x m = true).card ≤ Q) :
    (∑ m : M, ((p.map fun x => pred x m) true).toReal) ≤ (Q : ℝ) := by
  have hterm (m : M) :
      ((p.map fun x => pred x m) true).toReal =
        ∑' x : α, (p x).toReal * if pred x m = true then 1 else 0 := by
    simp only [_root_.PMF.map, Function.comp_def, bind_apply_toReal_tsum]
    exact tsum_congr fun x => by cases pred x m <;> simp
  simp_rw [hterm]
  have hsumm (m : M) :
      Summable (fun x : α => (p x).toReal * if pred x m = true then (1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun x => by split_ifs <;> positivity)
      (fun x => by split_ifs <;> simp [ENNReal.toReal_nonneg]) (summable_toReal p)
  rw [← Summable.tsum_finsetSum (fun m _ => hsumm m)]
  calc ∑' x : α, ∑ m : M, ((p x).toReal * if pred x m = true then (1 : ℝ) else 0)
      ≤ ∑' x : α, (p x).toReal * (Q : ℝ) := by
        refine Summable.tsum_le_tsum (fun x => ?_)
          (summable_sum fun m _ => hsumm m) ((summable_toReal p).mul_right (Q : ℝ))
        rw [← Finset.mul_sum]
        by_cases hx : x ∈ p.support
        · simpa only [Finset.sum_boole] using
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcard x hx)) ENNReal.toReal_nonneg
        · rw [(_root_.PMF.apply_eq_zero_iff _ _).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = (Q : ℝ) := by
        rw [tsum_mul_right, tsum_toReal, one_mul]

/-- A sample hits a list of keys with probability at most its length times the largest
allowed point mass. Repeated keys are allowed. -/
theorem toOuterMeasure_mem_list_le {κ : Type*} (p : PMF α) (f : α → κ) {δ : ℝ≥0∞}
    (hpoint : ∀ k, p.toOuterMeasure {a | f a = k} ≤ δ) (keys : List κ) :
    p.toOuterMeasure {a | f a ∈ keys} ≤ keys.length * δ := by
  induction keys with
  | nil => simp
  | cons k ks ih =>
    simpa only [List.mem_cons, Set.ofPred_or, List.length_cons, Nat.cast_add_one, add_mul,
      one_mul, add_comm] using
      (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) {a | f a = k} {a | f a ∈ ks}).trans
        (add_le_add (hpoint k) ih)

/-- **Union bound for association-list lookups**: if a key `f a` of an outcome `a ← p` equals
any fixed key with probability at most `δ`, then it is found in an association list `cache`
with probability at most `cache.length * δ`. -/
theorem toOuterMeasure_lookup_isSome_le {κ V : Type*} [BEq κ] [LawfulBEq κ] (p : PMF α)
    (f : α → κ) {δ : ℝ≥0∞} (hpoint : ∀ k, p.toOuterMeasure {a | f a = k} ≤ δ)
    (cache : List (κ × V)) :
    p.toOuterMeasure {a | (cache.lookup (f a)).isSome} ≤ cache.length * δ := by
  refine (p.toOuterMeasure.mono fun a ha => ?_).trans
    ((toOuterMeasure_mem_list_le p f hpoint (cache.map Prod.fst)).trans_eq
      (by rw [List.length_map]))
  obtain ⟨e, he, hit⟩ := List.lookup_isSome_iff.mp ha
  exact List.mem_map.mpr ⟨e, he, (eq_of_beq hit).symm⟩

end Cslib.Probability.PMF
