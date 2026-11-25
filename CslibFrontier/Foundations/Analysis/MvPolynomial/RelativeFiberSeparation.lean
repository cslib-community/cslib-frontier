/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, real multivariate polynomial fibers)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.RelativeValueSection
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchGrowth
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.DegreePieceSeparation
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalMinimumValue
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Separation of empty real fibers on fixed-degree pieces

On a parameter space where the specialized relative critical-value section has fixed degree,
emptiness of the zero fiber of a nonnegative polynomial is clopen.

Adapted from `RelativeFiberSeparation` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open Filter Set

variable {A : Type*} [TopologicalSpace A] {n m ell : ℕ}

/-- In a continuous parameter family of nonnegative real fibers, the locus of empty zero
fibers is clopen where the specialized relative critical-value section has fixed degree.
The degree bound and nonzero coefficient together specify that degree. -/
theorem isClopen_relative_emptyFibers_of_fixed_degree (hell : 1 ≤ ell) (he : Even (ell + 1))
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ ell)
    (r : A → Fin m → ℝ) (hr : Continuous r)
    (hnonneg : ∀ x z, 0 ≤ eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P)
    (k : ℕ) (hdegree : ∀ x, (specializedRelativeValueSection hell P hP (r x)).natDegree ≤ k)
    (hlead : ∀ x, (specializedRelativeValueSection hell P hP (r x)).coeff k ≠ 0) :
    IsClopen {x | ¬∃ z : Fin n → ℝ, eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P = 0} := by
  let F := rename finSumFinEquiv.symm P
  have hF : F.totalDegree ≤ ell := (totalDegree_rename_le _ _).trans hP
  let fiber (x : A) :=
    (sumRingEquiv ℤ (Fin n) (Fin m) F).map (eval₂Hom (Int.castRingHom ℝ) (r x))
  have hfiber (x : A) : (fiber x).totalDegree ≤ ell :=
    (totalDegree_map_le _ _).trans ((totalDegree_sumRingEquiv_le F).trans hF)
  have heval (x : A) (z : Fin n → ℝ) :
      eval z (fiber x) = eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P := by
    dsimp only [fiber, F]
    rw [eval_map, eval₂_sumRingEquiv, eval₂_rename]
    congr 2
    funext i
    refine Fin.addCases (motive := fun j =>
      Sum.elim z (r x) (finSumFinEquiv.symm j) = Fin.addCases z (r x) j)
      (fun j => ?_) (fun j => ?_) i
    · simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.addCases_left]
    · simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.addCases_right]
  have hfamily : Continuous (fun q : A × (Fin n → ℝ) => eval q.2 (fiber q.1)) := by
    have hcoords : Continuous (fun q : A × (Fin n → ℝ) =>
        (Fin.addCases q.2 (r q.1) : Fin (n + m) → ℝ)) := by
      apply continuous_pi
      intro i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      rcases j with j | j
      · simp only [finSumFinEquiv_apply_left, Fin.addCases_left]
        exact (continuous_apply j).comp continuous_snd
      · simp only [finSumFinEquiv_apply_right, Fin.addCases_right]
        exact ((continuous_apply j).comp hr).comp continuous_fst
    simpa only [heval, Function.comp_def, eval_map] using
      (continuous_eval (P.map (Int.castRingHom ℝ))).comp hcoords
  have hpos (x : A) (z : Fin n → ℝ) : 0 ≤ eval z (fiber x) := by
    rw [heval]
    exact hnonneg x z
  let μ (x : A) := criticalMinimumValue ell (fun _ => 0) (fiber x)
  let Q (x : A) := relativeValueBivariate hell F hF (r x)
  let D := ell ^ n
  have hroot (x : A) (u : ℝ) (hu : 0 ≤ u) :
      (Q x).eval₂ (Polynomial.evalRingHom u) (μ x u) = 0 := by
    dsimp only [Q]
    rw [← Polynomial.eval_map, relativeValueBivariate_map]
    exact isRoot_valuePolynomial_criticalMinimumValue hell he _ (fun _ => le_rfl)
      (fiber x) (hfiber x) (hpos x) u hu
  have hsection (x : A) (v : ℝ) :
      (specializedRelativeValueSection hell P hP (r x)).eval v =
        (Q x).eval₂ (Polynomial.evalRingHom (v ^ (D + 1))) v := by
    dsimp only [Q]
    rw [eval_specializedRelativeValueSection, eval₂_finiteRelativeValueSection,
      ← Polynomial.eval_map, relativeValueBivariate_map]
  have hcoeff (i : ℕ) :
      Continuous (fun x => (specializedRelativeValueSection hell P hP (r x)).coeff i) := by
    simp only [coeff_specializedRelativeValueSection_eq_eval₂]
    simpa only [eval_map, Function.comp_def] using
      (continuous_eval (((finSuccEquiv ℤ m (finiteRelativeValueSection hell P hP)).coeff i).map
        (Int.castRingHom ℝ))).comp hr
  -- Clamp negative test arguments so that continuity only uses nonnegative penalties.
  let test (x : A) (v : ℝ) := μ x ((max v 0) ^ (D + 1)) - v
  have htest : Continuous (fun q : A × ℝ => test q.1 q.2) := by
    have hpenalty : Continuous (fun q : A × ℝ => (max q.2 0) ^ (D + 1)) :=
      (continuous_snd.max continuous_const).pow _
    have hμ := continuous_criticalMinimumValue hell he _ (fun _ => le_rfl) fiber hfamily hpos
    exact (hμ.comp (continuous_fst.prodMk
      (hpenalty.subtype_mk fun q => pow_nonneg (le_max_right q.2 0) _))).sub continuous_snd
  let emptyFiber (x : A) := ¬∃ z : Fin n → ℝ, eval z (fiber x) = 0
  suffices hclopen : IsClopen {x | emptyFiber x} by
    simpa only [emptyFiber, heval] using hclopen
  refine Polynomial.eventualSign_isClopen_of_fixed_degree
    (fun x => specializedRelativeValueSection hell P hP (r x)) k hcoeff hdegree hlead
    test htest emptyFiber ?_ ?_ ?_
  · intro x v h
    have hμ_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ μ x u := by
      obtain ⟨z, hz⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he _ (fun _ => le_rfl)
        (fiber x) (hpos x) u hu
      dsimp only [μ]
      rw [criticalMinimumValue_eq_of_isMinOn _ _ _ _ hz, eval_deformedPolynomial]
      exact add_nonneg (eval_potentialPolynomial_nonneg ell he _ (fun _ => le_rfl) _)
        (mul_nonneg hu (mul_nonneg (by positivity) (hpos x z)))
    have hEq : μ x ((max v 0) ^ (D + 1)) = v := sub_eq_zero.mp h
    have hv : 0 ≤ v := hEq ▸ hμ_nonneg _ (pow_nonneg (le_max_right v 0) _)
    rw [max_eq_left hv] at hEq
    exact (hsection x v).trans
      ((congrArg ((Q x).eval₂ (Polynomial.evalRingHom (v ^ (D + 1)))) hEq).symm.trans
        (hroot x _ (pow_nonneg hv _)))
  · intro x hx
    have hdiv := (not_exists_zero_iff_tendsto_criticalMinimumValue hell he _
      (fun _ => le_rfl) (fiber x) (hpos x)).mp hx
    have ht : Tendsto (fun v : ℝ => μ x (v ^ (D + 1))) atTop atTop :=
      hdiv.comp (tendsto_pow_atTop (Nat.succ_ne_zero D))
    let S := Polynomial.Bivariate.swap (Q x)
    have hS : S ≠ 0 := by
      intro hz
      have hz' := congrArg Polynomial.Bivariate.swap hz
      simp only [S, Polynomial.Bivariate.swap_swap_apply, map_zero] at hz'
      exact (relativeValueBivariate_monic hell F hF (r x)).ne_zero hz'
    have hSdegree (j : ℕ) : (S.coeff j).natDegree ≤ D := by
      apply (Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap S j).trans_eq
      dsimp only [S, Q]
      rw [Polynomial.Bivariate.swap_swap_apply, relativeValueBivariate_natDegree]
    have hSroot : ∀ᶠ v : ℝ in atTop,
        S.eval₂ (Polynomial.evalRingHom (μ x (v ^ (D + 1)))) (v ^ (D + 1)) = 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
      exact (Polynomial.Bivariate.eval₂_eval₂RingHom_swap (RingHom.id ℝ) _ _ (Q x)).trans
        (hroot x _ (pow_nonneg hv _))
    have hgrowth := Polynomial.eventually_lt_of_eval₂_pow_eq_zero S hS hSdegree
      tendsto_id ht hSroot
    filter_upwards [hgrowth, eventually_ge_atTop (0 : ℝ)] with v hvg hv
    simpa only [test, max_eq_left hv, sub_pos, id_eq] using hvg
  · intro x hx
    obtain ⟨B, hB⟩ := (exists_zero_iff_bounded_criticalMinimumValue hell he _
      (fun _ => le_rfl) (fiber x) (hpos x)).mp (not_not.mp hx)
    filter_upwards [eventually_gt_atTop B, eventually_ge_atTop (0 : ℝ)] with v hvB hv
    simpa only [test, max_eq_left hv, sub_neg] using
      (hB _ (pow_nonneg hv (D + 1))).trans_lt hvB

end MvPolynomial.CriticalSystem
