/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin

/-!
# Interpolation on consecutive Hamming layers

The elementary symmetric polynomials form an integral interpolation basis on every
consecutive band of the Boolean cube. The coefficients are integral because a discrete
primitive shifts the binomial basis by one via Pascal’s recurrence.

## Main results

* `Cslib.exists_multilinear_of_consecutive_weights` prescribes an integer at each weight in a
  band of width `t` with a multilinear polynomial of total degree at most `t - 1`.

## References

* [Alman and Williams, *Probabilistic Rank and Matrix Rigidity*, Lemma 3.2][AlmanWilliams2017]
-/

public section

namespace Cslib

open Finset MvPolynomial

/-- Pascal's recurrence makes a discrete primitive of the binomial basis integral. -/
theorem exists_choose_interpolant (k t : ℕ) (value : ℕ → ℤ) :
    ∃ a : Fin t → ℤ, ∀ w, k ≤ w → w < k + t →
      ∑ j : Fin t, a j * (w.choose j : ℤ) = value w := by
  induction t generalizing value with
  | zero => exact ⟨Fin.elim0, fun w h₁ h₂ => by omega⟩
  | succ t ih =>
    obtain ⟨a, ha⟩ := ih (fun w => value (w + 1) - value w)
    let prim (w : ℕ) : ℤ := ∑ j : Fin t, a j * (w.choose (j + 1) : ℤ)
    have step (w : ℕ) : prim (w + 1) = prim w + ∑ j : Fin t, a j * (w.choose j : ℤ) := by
      simp only [prim, Nat.choose_succ_succ, Nat.cast_add, mul_add, sum_add_distrib]
      exact add_comm _ _
    refine ⟨Fin.cons (value k - prim k) a, ?_⟩
    intro w hw upper
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      Fin.cons_succ, Fin.val_succ]
    change value k - prim k + prim w = value w
    induction w, hw using Nat.le_induction with
    | base => omega
    | succ w hw prev =>
      rw [step, ha w hw (by omega)]
      have := prev (by omega)
      omega

/-- A squarefree monomial survives at a Boolean point precisely when its variables
belong to the support of the point. Thus the j-th elementary symmetric value counts j-subsets. -/
private theorem eval_esymm_on_support {n : ℕ} (x : Finset (Fin n)) (j : ℕ) :
    eval (fun i => if i ∈ x then (1 : ℤ) else 0) (esymm (Fin n) ℤ j) = x.card.choose j := by
  classical
  rw [esymm, map_sum]
  simp only [map_prod, eval_X]
  have indicator (s : Finset (Fin n)) :
      (∏ i ∈ s, (if i ∈ x then (1 : ℤ) else 0)) = if s ⊆ x then 1 else 0 := by
    by_cases h : s ⊆ x
    · rw [ite_eq_left h]
      exact prod_eq_one fun i hi => by simp [h hi]
    · obtain ⟨i, hi, hx⟩ := Finset.not_subset.mp h
      rw [ite_eq_right h]
      exact prod_eq_zero hi (by simp [hx])
  simp_rw [indicator]
  rw [← Finset.sum_filter]
  have filter_eq : ((univ : Finset (Fin n)).powersetCard j).filter (· ⊆ x) =
      x.powersetCard j := by ext s; simp [and_comm]
  simp [filter_eq]

/-- Integer multilinear interpolation on consecutive layers of a Boolean cube.
The value function prescribes one integer per weight in the half-open band.
See [Alman and Williams, Lemma 3.2][AlmanWilliams2017]. -/
theorem exists_multilinear_of_consecutive_weights (n k t : ℕ) (value : ℕ → ℤ) :
    ∃ p : MvPolynomial (Fin n) ℤ, p.totalDegree ≤ t - 1 ∧ (∀ i, p.degreeOf i ≤ 1) ∧
      ∀ x : Finset (Fin n), k ≤ x.card → x.card < k + t →
        eval (fun i => if i ∈ x then (1 : ℤ) else 0) p = value x.card := by
  classical
  obtain ⟨a, ha⟩ := exists_choose_interpolant k t value
  refine ⟨∑ j : Fin t, C (a j) * esymm (Fin n) ℤ j, ?_, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro j _
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add, esymm]
    apply totalDegree_finsetSum_le
    intro s hs
    apply (totalDegree_finsetProd _ _).trans
    have hcard := (mem_powersetCard.mp hs).2
    simpa using (show s.card ≤ t - 1 by have := j.isLt; omega)
  · intro i
    apply (degreeOf_sum_le ..).trans
    apply Finset.sup_le
    intro j _
    apply (degreeOf_C_mul_le ..).trans
    unfold esymm
    apply (degreeOf_sum_le ..).trans
    apply Finset.sup_le
    intro s _
    apply (degreeOf_prod_le ..).trans
    by_cases hi : i ∈ s <;> simp [degreeOf_X, hi]
  · intro x hx hxt
    simpa only [map_sum, map_mul, eval_C, eval_esymm_on_support] using ha x.card hx hxt

end Cslib
