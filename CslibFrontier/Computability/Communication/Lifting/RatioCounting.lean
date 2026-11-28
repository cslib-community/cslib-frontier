/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.UnsafeWitness
public import CslibFrontier.Computability.Communication.Lifting.WitnessCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting canonical parity-test families

Canonical parity tests with a fixed support inject into partial conditioning assignments.
Consequently a support-dependent size bound gives a geometric bound on the entire family,
without counting different outer output sets that can produce the same witness.
-/

public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ} [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}

omit [NeZero m] in
private theorem parityTest_ext (a b : ParityTest F Y) (hp : a.parity = b.parity)
    (hc : a.conditioned = b.conditioned) (ha : a.assignment = b.assignment) : a = b := by
  cases a
  cases b
  cases hp
  cases hc
  cases ha
  rfl

open scoped Classical in
/-- Canonical tests with a fixed parity support have no multiplicity beyond their partial
conditioning assignment. -/
theorem card_parityTest_fiber_le (P : ParityTest F Y → Prop)
    (hcanonical : ∀ w, P w → w.IsCanonical)
    (k : Finset (Fin n) → ℕ) (hsize : ∀ w, P w → w.conditioned.card ≤ k w.parity)
    (S : Finset (Fin n)) :
    Fintype.card {w : ParityTest F Y // P w ∧ w.parity = S} ≤
      Fintype.card (ConditioningAssignment (univ \ S) m (k S)) := by
  classical
  let encode (w : {w : ParityTest F Y // P w ∧ w.parity = S}) :
      ConditioningAssignment (univ \ S) m (k S) :=
    { coordinates := w.val.conditioned
      subset := fun i hi => mem_sdiff.mpr ⟨mem_univ _,
        fun hs => disjoint_left.mp w.val.disjoint hi (w.property.2.symm ▸ hs)⟩
      card_le := by simpa only [w.property.2] using hsize w.val w.property.1
      values := fun i => w.val.assignment i }
  refine Fintype.card_le_of_injective encode fun a b h => Subtype.ext ?_
  have hc : a.val.conditioned = b.val.conditioned := congrArg ConditioningAssignment.coordinates h
  refine parityTest_ext _ _ (a.property.2.trans b.property.2.symm) hc (funext fun i => ?_)
  by_cases hi : i ∈ a.val.conditioned
  · have hi' : i ∈ b.val.conditioned := hc ▸ hi
    simpa only [encode, hi, hi', dite_true] using congrArg
      (fun c : ConditioningAssignment (univ \ S) m (k S) =>
        if h : i ∈ c.coordinates then c.values ⟨i, h⟩ else 0) h
  · rw [hcanonical a.val a.property.1 i hi, hcanonical b.val b.property.1 i (hc ▸ hi)]

open scoped Classical in
/-- Grouping canonical tests by their parity support bounds the family by partial assignments. -/
theorem sum_parityTest_pow_le_sum_conditioningAssignment (P : ParityTest F Y → Prop)
    (hcanonical : ∀ w, P w → w.IsCanonical)
    (hnonempty : ∀ w, P w → w.parity.Nonempty)
    (k : Finset (Fin n) → ℕ) (hsize : ∀ w, P w → w.conditioned.card ≤ k w.parity)
    {q : ℝ} (hq : 0 ≤ q) :
    (∑ w : {w : ParityTest F Y // P w}, q ^ w.val.parity.card) ≤
      ∑ S ∈ (univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        (Fintype.card (ConditioningAssignment (univ \ S) m (k S)) : ℝ) * q ^ S.card := by
  classical
  rw [← sum_fiberwise_of_maps_to' (fun w _ =>
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hnonempty w.val w.property⟩)
    (fun S => q ^ S.card)]
  refine sum_le_sum fun S _ => ?_
  simp only [sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq _)
  rw [← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter P fun w => w.parity = S)]
  exact_mod_cast card_parityTest_fiber_le P hcanonical k hsize S

open scoped Classical in
/-- A support-dependent bound on conditioning sizes eliminates the explicit finite witness
budget from a geometric union bound. -/
theorem sum_parityTest_pow_le_one (P : ParityTest F Y → Prop)
    (hcanonical : ∀ w, P w → w.IsCanonical)
    (hnonempty : ∀ w, P w → w.parity.Nonempty)
    (k : Finset (Fin n) → ℕ) (hsize : ∀ w, P w → w.conditioned.card ≤ k w.parity)
    (hNm : 1 ≤ n * m) {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hk : ∀ S : Finset (Fin n), S.Nonempty →
      ((n * m : ℕ) : ℝ) ^ k S ≤ u ^ S.card)
    (hw : (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1)
    (hnw : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2) :
    (∑ w : {w : ParityTest F Y // P w}, q ^ w.val.parity.card) ≤ 1 :=
  (sum_parityTest_pow_le_sum_conditioningAssignment P hcanonical hnonempty k hsize hq).trans
    (sum_conditioningAssignment_mul_pow_le_one n m k hNm hu hq hk hw hnw)

/-- A density-ratio gap bounds the number of conditioned coordinates by the parity order
divided by the gap's exponent. -/
theorem conditioningSize_le_div_of_ratio {n r j s : ℕ} (hn : 2 ≤ n) (hr : 0 < r)
    {d : ℝ} (hd : (n : ℝ) ^ (2 * r) ≤ d)
    (hjs : d ^ j ≤ (n : ℝ) ^ (2 * s)) : j ≤ s / r := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hp : (n : ℝ) ^ ((2 * r) * j) ≤ (n : ℝ) ^ (2 * s) := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (by positivity) hd _).trans hjs
  have he := (pow_le_pow_iff_right₀ hn1).mp hp
  rw [Nat.mul_assoc, Nat.mul_comm r j] at he
  exact (Nat.le_div_iff_mul_le hr).mpr (by omega)

/-- A coarse alphabet bound raised to the truncated conditioning size is paid for by a
geometric weight on the parity size. -/
theorem pow_div_le_pow_of_le_pow {A r s : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hA : (A : ℝ) ≤ u ^ r) : (A : ℝ) ^ (s / r) ≤ u ^ s := by
  calc
    _ ≤ (u ^ r) ^ (s / r) := pow_le_pow_left₀ (Nat.cast_nonneg _) hA _
    _ = u ^ (r * (s / r)) := (pow_mul _ _ _).symm
    _ ≤ u ^ s := pow_le_pow_right₀ hu (Nat.mul_div_le s r)

end Cslib.Communication.Lifting
