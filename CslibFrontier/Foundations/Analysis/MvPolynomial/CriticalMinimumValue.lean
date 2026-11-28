/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalCoercive
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.Analysis.CoerciveMinimum
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Minimum values of the critical deformation

A global minimizer of the real deformation satisfies the normalized critical equations.
Cayley–Hamilton in the pure-power quotient then gives a characteristic root at its value.
For nonnegative parameters, the attained minimum is continuous and nondecreasing, and has
a uniform upper bound exactly when the input polynomial has a real zero. For a continuous family
of nonnegative inputs, the minimum is jointly continuous in the family parameter and penalty.
It diverges as the penalty tends to infinity exactly on fibers with no real zero.

Adapted from `CriticalMinimum`, `CoerciveMinimumValue`, and `CriticalMinimumValue` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. Joint continuity and divergence adapt
`FiberCoerciveMinimum` at the same revision.
-/

public section

namespace MvPolynomial.CriticalSystem

open Set Filter PurePower

variable {n : ℕ}

/-- The infimum of the values of the real deformation. Under the coercivity and sign
hypotheses, it is attained by a global minimizer. -/
noncomputable def criticalMinimumValue (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) : ℝ :=
  sInf (range (fun x => eval x (deformedPolynomial ell a u F)))

/-- Any global minimizer realizes the infimum defining `criticalMinimumValue`. -/
theorem criticalMinimumValue_eq_of_isMinOn (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) {x : Fin n → ℝ}
    (hx : IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) univ x) :
    criticalMinimumValue ell a F u = eval x (deformedPolynomial ell a u F) := by
  apply IsLeast.csInf_eq
  refine ⟨mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hx (mem_univ y)

/-- The attained minimum for the nonnegative parameter is a root of the actual
critical-value characteristic polynomial. -/
theorem isRoot_valuePolynomial_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : F.totalDegree ≤ ell)
    (hFn : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) :
    (valuePolynomial hell a u F hF).IsRoot (criticalMinimumValue ell a F u) := by
  obtain ⟨x, hx⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hFn u hu
  let p := deformedPolynomial ell a u F
  have hrel := aeval_criticalLower_eq_pow_of_isLocalMin_eval_deformedPolynomial ell a u F
    (hx.isLocalMin Filter.univ_mem)
  rw [criticalMinimumValue_eq_of_isMinOn ell a F u hx]
  simpa only [valuePolynomial, aeval_eq_eval] using
    isRoot_charpoly_multiplicationMatrix_of_aeval_eq hell (criticalLower ell a u F)
      (criticalLower_degree ell hell a u F hF) p x hrel

private theorem monotone_eval_deformedPolynomial (ell : ℕ) (a x : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (hF : 0 ≤ eval x F) :
    Monotone (fun u => eval x (deformedPolynomial ell a u F)) := by
  intro u v huv
  simp only [eval_deformedPolynomial]
  have hscale : 0 ≤ (ell + 1 : ℕ) * eval x F := by positivity
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right huv hscale)

/-- The minimum increases weakly with the nonnegative deformation parameter. -/
theorem monotoneOn_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) : MonotoneOn (criticalMinimumValue ell a F) (Ici 0) := by
  intro u hu v hv huv
  obtain ⟨x, hx⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hF u hu
  obtain ⟨y, hy⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hF v hv
  rw [criticalMinimumValue_eq_of_isMinOn ell a F u hx,
    criticalMinimumValue_eq_of_isMinOn ell a F v hy]
  exact (hx (mem_univ y)).trans (monotone_eval_deformedPolynomial ell a y F (hF y) huv)

/-- The critical minimum is jointly continuous in the parameter of the input family and the
nonnegative penalty. Continuity of the input family is required for joint evaluation. -/
theorem continuous_criticalMinimumValue {A : Type*} [TopologicalSpace A] {ell : ℕ}
    (hell : 1 ≤ ell) (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : A → MvPolynomial (Fin n) ℝ)
    (hF : Continuous (fun q : A × (Fin n → ℝ) => eval q.2 (F q.1)))
    (hFn : ∀ p x, 0 ≤ eval x (F p)) :
    Continuous (fun q : A × Ici (0 : ℝ) => criticalMinimumValue ell a (F q.1) q.2.val) := by
  unfold criticalMinimumValue
  apply continuous_sInf_range_of_compact_sublevels
    (G := fun x => eval x (potentialPolynomial ell a))
  · simp only [eval_deformedPolynomial]
    let Domain := (A × Ici (0 : ℝ)) × (Fin n → ℝ)
    have hu : Continuous (fun q : Domain => (q.fst.snd : ℝ)) :=
      continuous_subtypeVal.comp (continuous_snd.comp continuous_fst)
    have hv : Continuous (fun q : Domain => eval q.snd (F q.fst.fst)) :=
      hF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact ((continuous_eval (potentialPolynomial ell a)).comp continuous_snd).add
      (hu.mul (continuous_const.mul hv))
  · intro q x
    rw [eval_deformedPolynomial]
    exact le_add_of_nonneg_right (mul_nonneg q.2.property (mul_nonneg (by positivity) (hFn _ _)))
  · exact isCompact_sublevel_eval_potentialPolynomial ell hell he a ha

/-- The minimum of a fixed input is continuous on the nonnegative penalty half-line. -/
theorem continuousOn_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) : ContinuousOn (criticalMinimumValue ell a F) (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun u : Ici (0 : ℝ) => criticalMinimumValue ell a F u)
  have h : Continuous (fun q : ℝ × Ici (0 : ℝ) => criticalMinimumValue ell a F q.2.val) :=
    continuous_criticalMinimumValue hell he a ha (fun _ : ℝ => F)
      ((continuous_eval F).comp continuous_snd) (fun _ => hF)
  have hcomp := h.comp' (Continuous.prodMk_right (Y := Ici (0 : ℝ)) (0 : ℝ))
  change Continuous (fun u : Ici (0 : ℝ) => criticalMinimumValue ell a F u) at hcomp
  exact hcomp

/-- The nonnegative input has a real zero exactly when the deformation minima
have a uniform upper bound for all nonnegative parameters. -/
theorem exists_zero_iff_bounded_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F) :
    (∃ x, eval x F = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → criticalMinimumValue ell a F u ≤ B := by
  rw [exists_zero_iff_bounded_eval_deformedPolynomial ell hell he a ha F hF]
  refine exists_congr fun B => forall_congr' fun u => imp_congr_right fun hu => ?_
  obtain ⟨x, hx⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hF u hu
  rw [criticalMinimumValue_eq_of_isMinOn ell a F u hx]
  exact ⟨fun ⟨y, hy⟩ => (hx (mem_univ y)).trans hy, fun h => ⟨x, h⟩⟩

/-- A nonnegative input has no real zero exactly when its critical minima tend to infinity
as the penalty tends to infinity. -/
theorem not_exists_zero_iff_tendsto_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F) :
    (¬∃ x, eval x F = 0) ↔ Tendsto (criticalMinimumValue ell a F) atTop atTop := by
  rw [exists_zero_iff_bounded_criticalMinimumValue hell he a ha F hF]
  constructor
  · intro h
    apply tendsto_atTop.mpr
    intro B
    obtain ⟨u, hu, hBu⟩ : ∃ u : ℝ, 0 ≤ u ∧ B < criticalMinimumValue ell a F u := by
      by_contra hlarge
      exact h ⟨B, fun u hu => le_of_not_gt fun hBu => hlarge ⟨u, hu, hBu⟩⟩
    exact (eventually_ge_atTop u).mono fun v hv =>
      hBu.le.trans (monotoneOn_criticalMinimumValue hell he a ha F hF hu (hu.trans hv) hv)
  · rintro h ⟨B, hB⟩
    obtain ⟨u, hu, hBu⟩ := ((eventually_ge_atTop (0 : ℝ)).and (h.eventually_gt_atTop B)).exists
    exact (not_lt_of_ge (hB u hu)) hBu

end MvPolynomial.CriticalSystem
