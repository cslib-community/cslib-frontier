/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Residue
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# Pure-power relations annihilated by the residue

The residue respects each reduction `X i ^ ell = r i`. Shifting a geometric-series index
pairs the two terms; the omitted lower face vanishes by its coordinate exponent and the
upper face by total degree. `linear_mul_mem_ideal` proves vanishing on arbitrary multiples
of the generated relation ideal, over any commutative coefficient ring.

Ported from `LeanCanny.CountingHierarchy.PurePowerResidueRelations` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`; this is an algebraic step toward the counting bounds.
-/

public section

namespace MvPolynomial.PurePower

open MvPolynomial
open scoped BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

private noncomputable def raiseIndex (j : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update j i (j i + 1)

private noncomputable def lowerIndex (j : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update j i (j i - 1)

private theorem powerProduct_raise (r : Fin n → MvPolynomial (Fin n) S)
    (j : Fin n → ℕ) (i : Fin n) :
    (∏ k, r k ^ raiseIndex j i k) = (∏ k, r k ^ j k) * r i := by
  have heq (k : Fin n) : r k ^ raiseIndex j i k =
      r k ^ j k * (if k = i then r i else 1) := by
    by_cases hk : k = i
    · subst k
      simp [raiseIndex, pow_succ]
    · simp [raiseIndex, hk]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp

private theorem target_raise (ell : ℕ) (j : Fin n → ℕ) (i : Fin n) :
    target ell (raiseIndex j i) = target ell j + Finsupp.single i ell := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [target, raiseIndex, Nat.mul_add, Nat.add_assoc]
  · simp [target, raiseIndex, hk]

private theorem term_raise (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) (j : Fin n → ℕ) (i : Fin n) :
    term ell r (v * X i ^ ell) (raiseIndex j i) = term ell r (v * r i) j := by
  rw [term, powerProduct_raise, target_raise]
  have hmul : (v * X i ^ ell) * ((∏ k, r k ^ j k) * r i) =
      ((v * r i) * ∏ k, r k ^ j k) * X i ^ ell := by ring
  rw [hmul, X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial, mul_one]
  rfl

private theorem term_axis_zero {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (v : MvPolynomial (Fin n) S)
    (j : Fin n → ℕ) (i : Fin n) (hj : j i = 0) :
    term ell r (v * X i ^ ell) j = 0 := by
  have hnot : ¬Finsupp.single i ell ≤ target ell j := by
    rw [Finsupp.single_le_iff]
    simp only [target, Finsupp.coe_equivFunOnFinite_symm, hj, Nat.mul_zero, Nat.add_zero]
    omega
  rw [term]
  have hmul : (v * X i ^ ell) * (∏ k, r k ^ j k) =
      (v * ∏ k, r k ^ j k) * X i ^ ell := by ring
  rw [hmul, X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', ite_eq_right hnot]

/-- The two filtered rectangular sums are exactly reindexed by incrementing
the selected coordinate. This equality itself needs no degree assumptions. -/
private theorem shifted_sum (ell B : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    (∑ j ∈ (indices n B).filter (fun j => j i < B), term ell r (v * r i) j) =
      ∑ j ∈ (indices n B).filter (fun j => 0 < j i), term ell r (v * X i ^ ell) j := by
  refine Finset.sum_nbij' (raiseIndex · i) (lowerIndex · i) (fun j hj => ?_) (fun k hk => ?_)
    (fun j _ => ?_) (fun k hk => ?_) fun j _ => (term_raise ell r v j i).symm
  · obtain ⟨hj, hji⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨mem_indices.2 fun a => ?_, by simp [raiseIndex]⟩
    have := mem_indices.1 hj a
    by_cases ha : a = i <;> simp [raiseIndex, ha] <;> omega
  · obtain ⟨hk, hki⟩ := Finset.mem_filter.1 hk
    have hiB := mem_indices.1 hk i
    refine Finset.mem_filter.2 ⟨mem_indices.2 fun a => ?_, ?_⟩
    · have := mem_indices.1 hk a
      by_cases ha : a = i <;> simp [lowerIndex, ha] <;> omega
    · simp only [lowerIndex, Function.update_self]
      omega
  · funext a
    by_cases ha : a = i <;> simp [raiseIndex, lowerIndex, ha]
  · have := (Finset.mem_filter.1 hk).2
    funext a
    by_cases ha : a = i <;> simp [raiseIndex, lowerIndex, ha]
    omega

/-- The canonical functional respects each defining reduction relation. -/
theorem residue_mul_X_pow {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    residue ell r (v * X i ^ ell) = residue ell r (v * r i) := by
  let B := v.totalDegree + ell
  have hx : (X i ^ ell : MvPolynomial (Fin n) S).totalDegree ≤ ell := by
    rw [X_pow_eq_monomial]
    simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i ell) (1 : S)
  have hleft : (v * X i ^ ell).totalDegree ≤ B :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left hx _)
  have hright : (v * r i).totalDegree < B :=
    (MvPolynomial.totalDegree_mul _ _).trans_lt (Nat.add_lt_add_left (hr i) _)
  rw [residue_eq_truncated hell r hr _ hleft,
    residue_eq_truncated hell r hr _ hright.le]
  change (∑ j ∈ indices n B, term ell r (v * X i ^ ell) j) =
    ∑ j ∈ indices n B, term ell r (v * r i) j
  have hL :
      (∑ j ∈ (indices n B).filter (fun j => 0 < j i), term ell r (v * X i ^ ell) j) =
        ∑ j ∈ indices n B, term ell r (v * X i ^ ell) j := by
    refine Finset.sum_filter_of_ne fun j _ hne => Nat.pos_of_ne_zero fun hji => hne ?_
    exact term_axis_zero hell r v j i hji
  have hR :
      (∑ j ∈ (indices n B).filter (fun j => j i < B), term ell r (v * r i) j) =
        ∑ j ∈ indices n B, term ell r (v * r i) j := by
    refine Finset.sum_filter_of_ne fun j _ hne => not_le.1 fun hji => hne ?_
    have hd : j i ≤ (∑ i, j i) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact term_eq_zero_of_degree_lt hell r hr (v * r i) j (by omega)
  rw [← hL, ← hR, shifted_sum]

/-- The actual ideal of the pure-power relations. -/
@[expose] noncomputable def relationIdeal (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    Ideal (MvPolynomial (Fin n) S) := Ideal.span (Set.range (fun i => X i ^ ell - r i))

private theorem linear_mul_generator {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    linear hell r hr (v * (X i ^ ell - r i)) = 0 := by
  rw [mul_sub, map_sub]
  simp only [linear_apply]
  rw [residue_mul_X_pow hell r hr, sub_self]

/-- Vanishing on the generated ideal is proved for all polynomial multiples,
which is the induction invariant required by ideal closure. -/
theorem linear_mul_mem_ideal {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (q : MvPolynomial (Fin n) S) (hq : q ∈ relationIdeal ell r) :
    ∀ v, linear hell r hr (v * q) = 0 := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    exact (linear_mul_generator hell r hr · i)
  | zero => intro v; rw [mul_zero, map_zero]
  | add q t hq ht ihq iht => intro v; rw [mul_add, map_add, ihq v, iht v, add_zero]
  | smul c q hq ih =>
    intro v
    change linear hell r hr (v * (c * q)) = 0
    simpa only [mul_assoc] using ih (v * c)

theorem linear_mem_ideal {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (q : MvPolynomial (Fin n) S) (hq : q ∈ relationIdeal ell r) :
    linear hell r hr q = 0 := by
  simpa only [one_mul] using linear_mul_mem_ideal hell r hr q hq 1

end MvPolynomial.PurePower
