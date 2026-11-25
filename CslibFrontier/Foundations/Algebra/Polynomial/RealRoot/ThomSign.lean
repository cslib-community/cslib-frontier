/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real polynomial roots)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Defs
import CslibFrontier.Foundations.Data.Finset.CoordinateSelection
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Basic.Sign.Basic
import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.Interval.Set.Infinite

/-!
# Thom signs for real polynomial roots

Agreement of the signs of a polynomial and its derivatives at ordered endpoints forces
agreement throughout the interval. For a nonzero polynomial this distinguishes all
real roots using only the positive derivative orders through a degree bound.

Adapted from `LeanCanny.Algebra.ThomEncoding` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Set

/-- The sign of the `k`-th derivative at `x`, with order zero giving the sign of `p(x)`. -/
@[expose] noncomputable def derivativeSign (p : Polynomial ℝ) (x : ℝ) (k : ℕ) : SignType :=
  SignType.sign ((derivative^[k] p).eval x)

private theorem sign_eval_eq_on_Icc (p : Polynomial ℝ) {a b : ℝ}
    (hs : SignType.sign (p.eval a) = SignType.sign (p.eval b))
    (hd : ∀ z ∈ Icc a b, SignType.sign (p.derivative.eval z) =
      SignType.sign (p.derivative.eval a)) {z : ℝ} (hz : z ∈ Icc a b) :
    SignType.sign (p.eval z) = SignType.sign (p.eval a) := by
  by_cases hp : 0 ≤ p.derivative.eval a
  · have hm : MonotoneOn (fun x => p.eval x) (Icc a b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a b) p.differentiable.continuous.continuousOn
        p.differentiableOn (fun w hw => by
          rw [(p.hasDerivAt w).deriv, ← sign_nonneg_iff, hd w (interior_subset hw)]
          exact sign_nonneg_iff.mpr hp)
    have hz' := (SignType.sign.monotone.comp_monotoneOn hm).mapsTo_Icc hz
    simpa only [Function.comp_apply, ← hs, Icc_self, mem_singleton_iff] using hz'
  · have hm : AntitoneOn (fun x => p.eval x) (Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) p.differentiable.continuous.continuousOn
        p.differentiableOn (fun w hw => by
          rw [(p.hasDerivAt w).deriv, ← sign_nonpos_iff, hd w (interior_subset hw)]
          exact sign_nonpos_iff.mpr (le_of_not_ge hp))
    have hz' := (SignType.sign.monotone.comp_antitoneOn hm).mapsTo_Icc hz
    simpa only [Function.comp_apply, ← hs, Icc_self, mem_singleton_iff] using hz'

private theorem derivativeSign_eq_on_Icc : (D : ℕ) → (p : Polynomial ℝ) → (a b : ℝ) →
    p.natDegree ≤ D → (∀ k ≤ D, p.derivativeSign a k = p.derivativeSign b k) →
    ∀ z ∈ Icc a b, ∀ k ≤ D, p.derivativeSign z k = p.derivativeSign a k
  | 0, p, a, _, hD, _, z, _, k, hk => by
    rw [Nat.eq_zero_of_le_zero hk, eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hD)]
    simp only [derivativeSign, Function.iterate_zero_apply, eval_C]
  | D + 1, p, a, b, hD, hs, z, hz, k, hk => by
    have hds (j : ℕ) (hj : j ≤ D) :
        p.derivative.derivativeSign a j = p.derivative.derivativeSign b j := by
      simpa only [derivativeSign, Function.iterate_succ_apply] using hs (j + 1) (by omega)
    have hi := derivativeSign_eq_on_Icc D p.derivative a b
      ((natDegree_derivative_le p).trans (by omega)) hds
    cases k with
    | zero =>
      exact sign_eval_eq_on_Icc p (hs 0 (Nat.zero_le _))
        (fun w hw => hi w hw 0 (Nat.zero_le _)) hz
    | succ k =>
      simpa only [derivativeSign, Function.iterate_succ_apply] using hi z hz k (by omega)

private theorem eq_of_derivativeSign_eq_of_le {p : Polynomial ℝ} (hp : p ≠ 0)
    {D : ℕ} (hD : p.natDegree ≤ D) {a b : ℝ} (hab : a ≤ b) (ha : p.IsRoot a)
    (hs : ∀ k ≤ D, p.derivativeSign a k = p.derivativeSign b k) : a = b := by
  by_contra hne
  apply hp
  apply eq_zero_of_infinite_isRoot
  refine (Ioo_infinite (lt_of_le_of_ne hab hne)).mono fun z hz => ?_
  apply sign_eq_zero_iff.mp
  simpa only [derivativeSign, Function.iterate_zero_apply, ha.eq_zero, sign_zero] using
    derivativeSign_eq_on_Icc D p a b hD hs z (mem_Icc_of_Ioo hz) 0 (Nat.zero_le _)

/-- On the real roots of a nonzero polynomial, the derivative signs of orders `1` through
any upper bound on the degree determine the root uniquely. -/
theorem injOn_derivativeSign_roots (p : Polynomial ℝ) (hp : p ≠ 0) {D : ℕ}
    (hD : p.natDegree ≤ D) :
    InjOn (fun x (k : Fin D) => p.derivativeSign x (k.val + 1)) {x | p.IsRoot x} := by
  intro a ha b hb h
  have hs (k : ℕ) (hk : k ≤ D) : p.derivativeSign a k = p.derivativeSign b k :=
    match k with
    | 0 => by simp only [derivativeSign, Function.iterate_zero_apply,
        (show p.IsRoot a from ha).eq_zero, (show p.IsRoot b from hb).eq_zero]
    | k + 1 => congrFun h ⟨k, Nat.lt_of_succ_le hk⟩
  rcases le_total a b with hab | hba
  · exact eq_of_derivativeSign_eq_of_le hp hD hab ha hs
  · exact (eq_of_derivativeSign_eq_of_le hp hD hba hb (fun k hk => (hs k hk).symm)).symm

/-- In any nonempty finite subset of the real roots, at most `N` derivative sign tests
select one root when the degree is bounded by `D ≤ 2 ^ N`. Index `i : Fin D` tests
derivative order `i + 1`. -/
theorem exists_short_derivativeSign_selector (p : Polynomial ℝ) (hp : p ≠ 0) {D N : ℕ}
    (hD : p.natDegree ≤ D) (hDN : D ≤ 2 ^ N) {S : Finset ℝ} (hS : S.Nonempty)
    (hroots : ∀ x ∈ S, p.IsRoot x) :
    ∃ L : List (Fin D × SignType), L.length ≤ N ∧
      ∃ x ∈ S, ∀ y ∈ S, (∀ c ∈ L, p.derivativeSign y (c.1.val + 1) = c.2) ↔ y = x := by
  classical
  exact Finset.exists_short_coordinate_selector hS
    ((p.injOn_derivativeSign_roots hp hD).mono fun x hx => hroots x hx)
    ((card_le_degree_of_subset_roots fun x hx => (mem_roots hp).mpr (hroots x hx)).trans
      (hD.trans hDN))

end Polynomial
