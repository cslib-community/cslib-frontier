/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomial
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProductBounds

/-!
# Uniform size bounds for integer sign labels

The degree and coefficient norm of the label depend only on the width and
the degree and coefficient norm budgets of the individual tests. Each
denominator and each cleared error term inherits the bounds on the two
compositions of the sign product.

Adapted from `ClearedSignTestBounds` and `RootLabelPolynomialBounds` in
lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- A degree bound for the integer label of `m` tests of degree at most `D`. -/
@[expose] def signLabelDegreeBound (m B D : ℕ) : ℕ :=
  2 * ((m + 1) * ((2 * (m + 1) * (2 * B + 1)) * D))

/-- A base-two coefficient norm exponent for the integer label of `m` tests
whose individual norms are at most `2 ^ b`. -/
@[expose] def signLabelNormExponent (m B b : ℕ) : ℕ :=
  m.size + 2 * ((m + 1) * ((2 * (m + 1) * (2 * B + 1)) * (2 * B + 1 + b) + 2)) + 3

/-- The degree and coefficient budgets hold uniformly for every target sign assignment. -/
theorem signLabelPolynomial_bounds {m : ℕ} (B : ℕ) (g : Fin m → ℤ[X])
    (target : Fin m → SignType) {D b : ℕ}
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, (g i).coeffNorm1 ≤ 2 ^ b) :
    (signLabelPolynomial B g target).natDegree ≤ signLabelDegreeBound m B D ∧
      (signLabelPolynomial B g target).coeffNorm1 ≤ 2 ^ signLabelNormExponent m B b := by
  let n := 2 * (m + 1) * (2 * B + 1)
  let K := n * D
  let H := n * (2 * B + 1 + b)
  let L := (m + 1) * (H + 2)
  let p := dyadicSignProduct B (m + 1)
  let a (i : Fin m) := p.comp (g i)
  let a' (i : Fin m) := p.comp (-g i)
  let d (i : Fin m) := a i + a' i
  let dev (i : Fin m) := a i - a' i - C (target i : ℤ) * d i
  let e (i : Fin m) := dev i * ∏ j ∈ univ.erase i, d j
  let P := ∏ i, d i
  let S := ∑ i, (e i) ^ 2
  have hPos (i : Fin m) : (a i).natDegree ≤ K ∧ (a i).coeffNorm1 ≤ 2 ^ H :=
    dyadicSignProduct_comp_bounds B (m + 1) (g i) (hD i) (hb i)
  have hNeg (i : Fin m) : (a' i).natDegree ≤ K ∧ (a' i).coeffNorm1 ≤ 2 ^ H :=
    dyadicSignProduct_comp_bounds B (m + 1) (-g i)
      (by simpa only [natDegree_neg] using hD i) (by simpa only [coeffNorm1_neg] using hb i)
  have hdouble (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_two]
  have hDen (i : Fin m) : (d i).natDegree ≤ K ∧ (d i).coeffNorm1 ≤ 2 ^ (H + 1) :=
    ⟨(natDegree_add_le _ _).trans (max_le (hPos i).1 (hNeg i).1),
      (coeffNorm1_add_le _ _).trans ((Nat.add_le_add (hPos i).2 (hNeg i).2).trans_eq (hdouble H))⟩
  have hDev (i : Fin m) : (dev i).natDegree ≤ K ∧ (dev i).coeffNorm1 ≤ 2 ^ (H + 2) := by
    have ht : (target i : ℤ).natAbs ≤ 1 := by cases target i <;> decide
    refine ⟨(natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le (hPos i).1 (hNeg i).1))
      ((natDegree_C_mul_le _ _).trans (hDen i).1)), ?_⟩
    have hct := (coeffNorm1_C_mul_le (target i : ℤ) (d i)).trans
      ((Nat.mul_le_mul ht (hDen i).2).trans_eq (Nat.one_mul _))
    have hsub := (coeffNorm1_sub_le (a i) (a' i)).trans
      ((Nat.add_le_add (hPos i).2 (hNeg i).2).trans_eq (hdouble H))
    exact (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hsub hct).trans_eq (hdouble (H + 1)))
  have hProd (I : Finset (Fin m)) :
      (∏ i ∈ I, d i).natDegree ≤ m * K ∧ (∏ i ∈ I, d i).coeffNorm1 ≤ 2 ^ (m * (H + 1)) := by
    have hI : I.card ≤ m := by simpa only [Fintype.card_fin] using I.card_le_univ
    constructor
    · refine (natDegree_prod_le _ _).trans (le_trans ?_ (Nat.mul_le_mul_right K hI))
      simpa only [sum_const, nsmul_eq_mul, Nat.cast_id] using
        sum_le_sum (fun i (_ : i ∈ I) => (hDen i).1)
    · refine (coeffNorm1_prod_le _ _).trans ((prod_le_prod fun i _ => (hDen i).2).trans ?_)
      rw [prod_const, ← pow_mul, Nat.mul_comm (H + 1) I.card]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hI)
  have hE (i : Fin m) : (e i).natDegree ≤ (m + 1) * K ∧ (e i).coeffNorm1 ≤ 2 ^ L := by
    have hp := hProd (univ.erase i)
    refine ⟨natDegree_mul_le.trans ((Nat.add_le_add (hDev i).1 hp.1).trans_eq (by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])), ?_⟩
    refine (coeffNorm1_mul_le _ _).trans ((Nat.mul_le_mul (hDev i).2 hp.2).trans ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by
      calc
        H + 2 + m * (H + 1) ≤ H + 2 + m * (H + 2) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left m (by omega)) _
        _ = L := by
          dsimp only [L]
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])
  have hPdeg : P.natDegree ≤ (m + 1) * K :=
    (hProd univ).1.trans (Nat.mul_le_mul_right K (Nat.le_succ m))
  have hPnorm : P.coeffNorm1 ≤ 2 ^ L :=
    (hProd univ).2.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul (Nat.le_succ m) (by omega)))
  have hSq (q : ℤ[X]) (hq : q.coeffNorm1 ≤ 2 ^ L) :
      (q ^ 2).coeffNorm1 ≤ 2 ^ (2 * L) :=
    (coeffNorm1_pow_le _ _).trans ((Nat.pow_le_pow_left hq 2).trans_eq (by
      rw [← pow_mul, Nat.mul_comm L 2]))
  have hSdeg : S.natDegree ≤ 2 * ((m + 1) * K) :=
    natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hE i).1)
  have hSnorm : S.coeffNorm1 ≤ 2 ^ (m.size + 2 * L) := by
    refine (coeffNorm1_sum_le _ _).trans ((sum_le_sum fun i _ => hSq (e i) (hE i).2).trans ?_)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact (Nat.mul_le_mul_right _ m.lt_size_self.le).trans_eq (pow_add _ _ _).symm
  change (P ^ 2 - C 4 * S).natDegree ≤ 2 * ((m + 1) * K) ∧
    (P ^ 2 - C 4 * S).coeffNorm1 ≤ 2 ^ (m.size + 2 * L + 3)
  refine ⟨(natDegree_sub_le _ _).trans (max_le
    (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hPdeg))
    ((natDegree_C_mul_le _ _).trans hSdeg)), ?_⟩
  have hscaled : (C 4 * S).coeffNorm1 ≤ 2 ^ (m.size + 2 * L + 2) := by
    refine (coeffNorm1_C_mul_le _ _).trans ((Nat.mul_le_mul_left 4 hSnorm).trans_eq ?_)
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, Nat.add_comm 2]
  have hfirst := (hSq P hPnorm).trans
    (show 2 ^ (2 * L) ≤ 2 ^ (m.size + 2 * L + 2) from Nat.pow_le_pow_right (by decide) (by omega))
  exact (coeffNorm1_sub_le _ _).trans ((Nat.add_le_add hfirst hscaled).trans_eq
    (by simpa only [Nat.add_assoc] using hdouble (m.size + 2 * L + 2)))

end Polynomial
