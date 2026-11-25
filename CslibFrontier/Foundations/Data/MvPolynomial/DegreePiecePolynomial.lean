/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, specialization of multivariate polynomials)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.Data.MvPolynomial.FirstVariable
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A polynomial for a fixed-degree piece

When the first variable is retained and all others are specialized, the degree is
specified by a nonzero coefficient and the vanishing of all higher coefficients. The
polynomial below encodes these as zeros by adding one coordinate for the inverse of
the selected coefficient.

Adapted from `DegreePiecePolynomial` and `DegreePiecePolynomialBounds` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

variable {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- The squared inverse equation for coefficient `k`, plus the squares of coefficients
`k + 1` through `N`. The inverse is coordinate zero, with the parameters following it. -/
noncomputable def degreePiecePolynomial (P : MvPolynomial (Fin (m + 1)) R)
    (N k : ℕ) : MvPolynomial (Fin (m + 1)) R :=
  let a (j : ℕ) := rename Fin.succ ((finSuccEquiv R m P).coeff j)
  (a k * X 0 - 1) ^ 2 + ∑ j ∈ Finset.Ioc k N, a j ^ 2

/-- The higher-coefficient squares can be evaluated by a bounded sum with a degree guard. -/
theorem degreePiecePolynomial_eq_sum_range (P : MvPolynomial (Fin (m + 1)) R) (N k : ℕ) :
    let a (j : ℕ) := rename Fin.succ ((finSuccEquiv R m P).coeff j)
    degreePiecePolynomial P N k =
      (a k * X 0 - 1) ^ 2 + ∑ j ∈ Finset.range (N + 1), (if k < j then a j else 0) ^ 2 := by
  have hindex : (Finset.range (N + 1)).filter (fun j => k < j) = Finset.Ioc k N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff, and_comm]
  rw [degreePiecePolynomial]
  dsimp
  rw [← hindex, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- Evaluating the lift substitutes the parameters into each coefficient and the first
coordinate into the inverse equation. -/
theorem eval₂_degreePiecePolynomial (P : MvPolynomial (Fin (m + 1)) R) (N k : ℕ)
    (f : R →+* S) (t : S) (x : Fin m → S) :
    eval₂ f (Fin.cons t x) (degreePiecePolynomial P N k) =
      (eval₂ f x ((finSuccEquiv R m P).coeff k) * t - 1) ^ 2 +
        ∑ j ∈ Finset.Ioc k N, (eval₂ f x ((finSuccEquiv R m P).coeff j)) ^ 2 := by
  simp only [degreePiecePolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_one,
    eval₂_X, Fin.cons_zero, eval₂_sum, eval₂_rename, Function.comp_def, Fin.cons_succ]

/-- A real zero of the lift solves the inverse equation for coefficient `k` and
makes each higher coefficient through `N` vanish. -/
theorem eval₂_degreePiecePolynomial_eq_zero_iff (P : MvPolynomial (Fin (m + 1)) R) (N k : ℕ)
    (f : R →+* ℝ) (t : ℝ) (x : Fin m → ℝ) :
    eval₂ f (Fin.cons t x) (degreePiecePolynomial P N k) = 0 ↔
      eval₂ f x ((finSuccEquiv R m P).coeff k) * t = 1 ∧
        ∀ j ∈ Finset.Ioc k N, eval₂ f x ((finSuccEquiv R m P).coeff j) = 0 := by
  rw [eval₂_degreePiecePolynomial,
    add_eq_zero_iff_of_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    sq_eq_zero_iff, sub_eq_zero, Finset.sum_sq_eq_zero_iff]

/-- The inverse coordinate increases degree by at most one before squaring. -/
theorem totalDegree_degreePiecePolynomial_le (P : MvPolynomial (Fin (m + 1)) R) (N k : ℕ) :
    (degreePiecePolynomial P N k).totalDegree ≤ 2 * (P.totalDegree + 1) := by
  let a (j : ℕ) := rename Fin.succ ((finSuccEquiv R m P).coeff j)
  have ha (j : ℕ) : (a j).totalDegree ≤ P.totalDegree :=
    (totalDegree_rename_le _ _).trans (totalDegree_coeff_finSuccEquiv_le P j)
  have hinverse : (a k * X 0 - 1).totalDegree ≤ P.totalDegree + 1 := by
    have hmul := (totalDegree_mul (a k) (X 0)).trans
      (Nat.add_le_add (ha k) (totalDegree_X_le 0))
    apply (totalDegree_sub _ _).trans
    rw [totalDegree_one]
    exact max_le hmul (Nat.zero_le _)
  rw [degreePiecePolynomial]
  apply (totalDegree_add _ _).trans
  refine max_le ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hinverse)) ?_
  exact totalDegree_finsetSum_le fun j _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ((ha j).trans (Nat.le_succ _)))

end MvPolynomial
