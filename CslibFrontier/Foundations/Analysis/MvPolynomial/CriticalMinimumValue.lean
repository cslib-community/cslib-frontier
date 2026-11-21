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
import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Minimum values of the critical deformation

A global minimizer of the real deformation satisfies the normalized critical equations.
Cayley–Hamilton in the pure-power quotient then gives a characteristic root at its value.
For nonnegative parameters, the attained minimum is continuous and nondecreasing, and has
a uniform upper bound exactly when the input polynomial has a real zero.

Adapted from `CriticalMinimum`, `CoerciveMinimumValue`, and `CriticalMinimumValue` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
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
  have hzero (i : Fin n) : eval x (pderiv i p) = 0 := by
    have hmin : IsMinOn (fun t => eval (Function.update x i t) p) univ (x i) := by
      intro t _
      change eval (Function.update x i (x i)) p ≤ eval (Function.update x i t) p
      rw [Function.update_eq_self]
      exact hx (mem_univ _)
    exact (hmin.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero (hasDerivAt_eval_update p x i)
  have hrel (i : Fin n) : aeval x (criticalLower ell a u F i) = x i ^ ell := by
    have hi := hzero i
    dsimp only [p] at hi
    rw [pderiv_deformedPolynomial, map_mul, eval_C, map_sub, map_pow, eval_X] at hi
    have hc : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simpa only [aeval_eq_eval] using (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hc)).symm
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

/-- On the nonnegative half-line the minimum is continuous. Locally all minimizers lie
in one compact sublevel of the potential. -/
theorem continuousOn_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) : ContinuousOn (criticalMinimumValue ell a F) (Ici 0) := by
  let G (x : Fin n → ℝ) := eval x (potentialPolynomial ell a)
  let f (u : ℝ) (x : Fin n → ℝ) := eval x (deformedPolynomial ell a u F)
  have hf : Continuous (fun z : ℝ × (Fin n → ℝ) => f z.1 z.2) := by
    simp only [f, eval_deformedPolynomial]
    exact ((continuous_eval _).comp continuous_snd).add
      (continuous_fst.mul (continuous_const.mul ((continuous_eval F).comp continuous_snd)))
  have hparam (x : Fin n → ℝ) : Monotone (fun u => f u x) :=
    monotone_eval_deformedPolynomial ell a x F (hF x)
  have hlocal (U : ℝ) : ContinuousOn (criticalMinimumValue ell a F) (Icc 0 U) := by
    let K := {x | G x ≤ f U 0}
    have hK : IsCompact K :=
      isCompact_sublevel_eval_potentialPolynomial ell hell he a ha (f U 0)
    apply (hK.continuous_sInf (f := f) hf).continuousOn.congr
    intro u hu
    obtain ⟨x, hx⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hF u hu.1
    have hxK : x ∈ K := by
      have hle : G x ≤ f u x := by
        simpa only [G, f, eval_deformedPolynomial ell a x 0 F, zero_mul, add_zero] using
          hparam x hu.1
      exact hle.trans ((hx (mem_univ 0)).trans (hparam 0 hu.2))
    rw [criticalMinimumValue_eq_of_isMinOn ell a F u hx]
    symm
    apply IsLeast.csInf_eq
    refine ⟨mem_image_of_mem _ hxK, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact hx (mem_univ y)
  intro u hu
  have hlt : u < u + 1 := lt_add_of_pos_right u zero_lt_one
  exact (hlocal (u + 1) u ⟨hu, hlt.le⟩).mono_of_mem_nhdsWithin
    (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt)))

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

end MvPolynomial.CriticalSystem
