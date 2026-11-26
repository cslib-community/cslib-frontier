/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, products of polynomials in disjoint variables)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Products of polynomials in disjoint variables

A monomial of a product `p * q` is the sum of a monomial of `p` and one of `q`. When `p` and `q`
have no variable in common, each variable occurs in at most one of the two, so the degree of the
product in each variable is the larger of the two degrees. In particular a product of multilinear
polynomials in disjoint sets of variables is multilinear.

## Main results

* `MvPolynomial.mul_mem_restrictDegree_of_disjoint_vars`: if `p` and `q` have degree at most `n`
  in each variable and no variable in common, so does `p * q`.
* `MvPolynomial.X_mem_restrictDegree`, `MvPolynomial.C_mem_restrictDegree`,
  `MvPolynomial.vars_X_subset`: variables and constants. Unlike Mathlib's `MvPolynomial.vars_X`,
  these hold without `[Nontrivial R]`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- A product of polynomials of degree at most `n` in each variable, with no variable in common,
has degree at most `n` in each variable. -/
theorem mul_mem_restrictDegree_of_disjoint_vars {p q : MvPolynomial σ R} {n : ℕ}
    (hp : p ∈ restrictDegree σ R n) (hq : q ∈ restrictDegree σ R n)
    (hpq : Disjoint p.vars q.vars) : p * q ∈ restrictDegree σ R n := by
  classical
  rw [mem_restrictDegree] at hp hq ⊢
  intro s hs i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q hs)
  rw [Finsupp.add_apply]
  by_cases hai : a i = 0
  · rw [hai, zero_add]
    exact hq b hb i
  · have hip : i ∈ p.vars :=
      (mem_vars_iff_mem_support i).mpr ⟨a, ha, Finsupp.mem_support_iff.mpr hai⟩
    have hbi : b i = 0 := by
      by_contra hbi
      exact Finset.disjoint_left.mp hpq hip
        ((mem_vars_iff_mem_support i).mpr ⟨b, hb, Finsupp.mem_support_iff.mpr hbi⟩)
    rw [hbi, add_zero]
    exact hp a ha i

/-- A variable has degree at most one in each variable. -/
theorem X_mem_restrictDegree {n : ℕ} (hn : 1 ≤ n) (i : σ) : (X i : MvPolynomial σ R) ∈
    restrictDegree σ R n := by
  classical
  rw [mem_restrictDegree]
  intro s hs j
  rw [Finset.mem_singleton.mp (support_monomial_subset hs), Finsupp.single_apply]
  split <;> omega

/-- A constant has degree zero in each variable. -/
theorem C_mem_restrictDegree (n : ℕ) (r : R) : (C r : MvPolynomial σ R) ∈ restrictDegree σ R n := by
  rw [mem_restrictDegree]
  intro s hs j
  rw [C_apply] at hs
  rw [Finset.mem_singleton.mp (support_monomial_subset hs)]
  exact Nat.zero_le _

/-- A variable involves at most itself. -/
theorem vars_X_subset (i : σ) : (X i : MvPolynomial σ R).vars ⊆ {i} := by
  classical
  intro j hj
  obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
  rw [Finset.mem_singleton.mp (support_monomial_subset hd)] at hjd
  exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (Finsupp.support_single_subset hjd))

end MvPolynomial
