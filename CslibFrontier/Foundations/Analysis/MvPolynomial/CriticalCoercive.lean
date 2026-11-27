/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Linarith

/-!
# Coercive minima of the separated critical deformation

The separated even-power potential is nonnegative and has compact sublevels for nonnegative
centers. Perturbing it by a nonnegative multiple of a nonnegative input preserves compact
sublevels, so the actual deformed polynomial attains its minimum. These minima are uniformly
bounded over nonnegative parameters exactly when the input has a real zero.

Adapted from `SeparatedPowerPotential`, `CoerciveMinimum`, and `CriticalMinimum` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. For the boundedness criterion, minimizing the
input on one compact sublevel gives a positive uniform lower bound if there is no zero.
-/

public section

namespace MvPolynomial.CriticalSystem

open Set
open scoped BigOperators

variable {n : ℕ}

private noncomputable def potentialTerm (ell : ℕ) (a t : ℝ) : ℝ :=
  t ^ (ell + 1) - (ell + 1 : ℕ) * a ^ ell * t + (ell + 1 : ℕ) * a ^ (ell + 1)

private theorem potentialTerm_nonneg (ell : ℕ) (he : Even (ell + 1)) {a : ℝ} (ha : 0 ≤ a)
    (t : ℝ) : 0 ≤ potentialTerm ell a t := by
  by_cases ht : 0 ≤ t
  · have h := pow_add_mul_le_add_pow ha
      (show 0 ≤ 2 * a + (t - a) by linarith) (ell + 1)
    rw [show a + (t - a) = t by ring, Nat.add_sub_cancel] at h
    unfold potentialTerm
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at h ⊢
    nlinarith [pow_nonneg ha ell]
  · exact add_nonneg (sub_nonneg.mpr
      ((mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge ht)).trans
        (he.pow_nonneg t))) (by positivity)

private theorem abs_le_potentialTerm (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    |t| ≤ potentialTerm ell a t + (ell + 1 : ℕ) * a ^ ell + 1 := by
  let c : ℝ := (ell + 1 : ℕ) * a ^ ell
  have hc : 0 ≤ c := by positivity
  change |t| ≤ potentialTerm ell a t + c + 1
  by_cases ht : |t| ≤ c + 1
  · linarith [potentialTerm_nonneg ell he ha t]
  · have hlarge : c + 1 ≤ |t| := (lt_of_not_ge ht).le
    have hp : |t| ^ 2 ≤ t ^ (ell + 1) := calc
      _ ≤ |t| ^ (ell + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = _ := by rw [← abs_pow, abs_of_nonneg (he.pow_nonneg t)]
    have hquad := mul_le_mul_of_nonneg_right hlarge (abs_nonneg t)
    have hlin := mul_le_mul_of_nonneg_left (le_abs_self t) hc
    have hconst : 0 ≤ (ell + 1 : ℕ) * a ^ (ell + 1) := by positivity
    change |t| ≤ (t ^ (ell + 1) - c * t + (ell + 1 : ℕ) * a ^ (ell + 1)) + c + 1
    nlinarith

private theorem eval_potential_eq_sum (ell : ℕ) (a x : Fin n → ℝ) :
    eval x (potentialPolynomial ell a) = ∑ i, potentialTerm ell (a i) (x i) := by
  classical
  simp only [potentialPolynomial, map_sum, map_add, map_sub, map_mul, map_pow, eval_X, eval_C,
    potentialTerm]

/-- With nonnegative centers and an even leading exponent, the real potential is nonnegative. -/
theorem eval_potentialPolynomial_nonneg (ell : ℕ) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (x : Fin n → ℝ) :
    0 ≤ eval x (potentialPolynomial ell a) := by
  rw [eval_potential_eq_sum]
  exact Finset.sum_nonneg fun i _ => potentialTerm_nonneg ell he (ha i) (x i)

/-- Each sublevel of the separated potential is compact. -/
theorem isCompact_sublevel_eval_potentialPolynomial (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (B : ℝ) :
    IsCompact {x | eval x (potentialPolynomial ell a) ≤ B} := by
  have hclosed : IsClosed {x | eval x (potentialPolynomial ell a) ≤ B} :=
    isClosed_le (continuous_eval _) continuous_const
  let bound (i : Fin n) := B + (ell + 1 : ℕ) * a i ^ ell + 1
  apply (isCompact_Icc : IsCompact (Icc (fun i => -bound i) bound)).of_isClosed_subset hclosed
  intro x hx
  change eval x (potentialPolynomial ell a) ≤ B at hx
  rw [eval_potential_eq_sum] at hx
  have hbound (i : Fin n) : |x i| ≤ bound i := by
    have hterm : potentialTerm ell (a i) (x i) ≤ ∑ j, potentialTerm ell (a j) (x j) :=
      Finset.single_le_sum (fun j _ => potentialTerm_nonneg ell he (ha j) (x j)) (Finset.mem_univ i)
    exact (abs_le_potentialTerm ell hell he (ha i) (x i)).trans
      (add_le_add (add_le_add (hterm.trans hx) le_rfl) le_rfl)
  exact ⟨fun i => (abs_le.mp (hbound i)).1, fun i => (abs_le.mp (hbound i)).2⟩

private theorem eval_potential_le_eval_deformed (ell : ℕ) (a x : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (hF : 0 ≤ eval x F) {u : ℝ} (hu : 0 ≤ u) :
    eval x (potentialPolynomial ell a) ≤ eval x (deformedPolynomial ell a u F) := by
  rw [eval_deformedPolynomial]
  exact le_add_of_nonneg_right (by positivity)

/-- Perturbing by a nonnegative multiple of a nonnegative polynomial preserves compact
sublevels of the separated potential. -/
theorem isCompact_sublevel_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) (B : ℝ) :
    IsCompact {x | eval x (deformedPolynomial ell a u F) ≤ B} :=
  (isCompact_sublevel_eval_potentialPolynomial ell hell he a ha B).of_isClosed_subset
    (isClosed_le (continuous_eval _) continuous_const)
    (fun x hx => (eval_potential_le_eval_deformed ell a x F (hF x) hu).trans hx)

/-- The real deformed polynomial attains a global minimum. -/
theorem exists_isMinOn_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) :
    ∃ x, IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) univ x := by
  let f (x : Fin n → ℝ) := eval x (deformedPolynomial ell a u F)
  have hk : IsCompact {x | f x ≤ f 0} :=
    isCompact_sublevel_eval_deformedPolynomial ell hell he a ha F hF u hu (f 0)
  have hf : Continuous f := continuous_eval _
  obtain ⟨x, hmin⟩ := hf.exists_forall_le' 0 (by
    filter_upwards [hk.compl_mem_cocompact] with y hy
    change ¬ f y ≤ f 0 at hy
    exact le_of_not_ge hy)
  exact ⟨x, fun y _ => hmin y⟩

/-- A nonnegative real input has a zero exactly when there is a common bound such that,
for each nonnegative parameter, some point has deformed value at most that bound. -/
theorem exists_zero_iff_bounded_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F) :
    (∃ x, eval x F = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → ∃ x, eval x (deformedPolynomial ell a u F) ≤ B := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨eval x (potentialPolynomial ell a), fun u _ => ⟨x, ?_⟩⟩
    rw [eval_deformedPolynomial, hx, mul_zero, mul_zero, add_zero]
  · rintro ⟨B, hB⟩
    obtain ⟨x₀, hx₀⟩ := hB 0 le_rfl
    have hx₀' := (eval_potential_le_eval_deformed ell a x₀ F (hF x₀) le_rfl).trans hx₀
    have hnonneg := (eval_potentialPolynomial_nonneg ell he a ha x₀).trans hx₀'
    obtain ⟨x, _, hmin⟩ :=
      (isCompact_sublevel_eval_potentialPolynomial ell hell he a ha B).exists_isMinOn
        ⟨x₀, hx₀'⟩ (continuous_eval F).continuousOn
    refine ⟨x, le_antisymm ?_ (hF x)⟩
    by_contra! hpos
    let c : ℝ := (ell + 1 : ℕ) * eval x F
    have hc : 0 < c := by positivity
    let u := (B + 1) / c
    have hu : 0 ≤ u := by positivity
    obtain ⟨y, hy⟩ := hB u hu
    have hyK := (eval_potential_le_eval_deformed ell a y F (hF y) hu).trans hy
    have hle : u * c ≤ u * ((ell + 1 : ℕ) * eval y F) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmin hyK) (by positivity)) hu
    have hu_eq : u * c = B + 1 := div_mul_cancel₀ _ hc.ne'
    rw [eval_deformedPolynomial] at hy
    linarith [eval_potentialPolynomial_nonneg ell he a ha y]

end MvPolynomial.CriticalSystem
