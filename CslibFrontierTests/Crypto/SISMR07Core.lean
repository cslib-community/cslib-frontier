/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.SIS.MR07Core
import CslibFrontier.Foundations.Probability.Gaussian.MassBounds
import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for `CslibFrontier/Crypto/Computational/SIS/MR07Core.lean`

Ordinary `module` client verifying the public interfaces and non-vacuity of the finite
Micciancio–Regev `IncGDD` to `ℓ₂`-SIS core reduction on the concrete 2-D lattice pair
`B = I₂` and `S = diag(2, 3)` (`det S = 6`, index `6`):

1. Exact cardinalities (`card_gridRep`, `card_sublatticeQuot`), `finrank_intLattice`,
   `norm_intColCast`, and dual-mass monotonicity (`gaussianMass_dual_gridLattice_le`).
2. Discrete-grid joint factorization (`idealGridSample_eq_bind_discreteGaussian`) and marginal
   closeness (`idealGridSample_fst_closeTo_uniform`, discrete-grid step toward
   [MicciancioRegev2007], Lemma 5.7) with the dual-mass premise discharged from scratch via
   `ZLattice.gaussianMass_dual_sub_one_le_of_gap`.
3. HNF-free uniform quotient sampling (`map_quotientHom_uniform_eq_uniform_sublatticeQuot`,
   `quotientHom_toVec`), uniform SIS matrix distribution (`idealCombine_matrix_eq_uniform`),
   unconditional lattice membership on a non-kernel vector (`combineOutput_mem_intLattice`), and
   the combining norm bound on a nonzero kernel vector
   (`combineOutput_mem_intLattice_and_norm_sub_le`), plus the explicit map/parallelepiped
   characterizations (`idealGridSample_eq_map`, `combineColumn_fst_toVec`, `combineColumn_snd_val`).
4. Non-vacuous instantiation of `idealIncGDDStep_succProb_of_sisEll2`,
   `idealIncGDDStep_support_mem_intLattice`, and `incGDD_succProb_of_closeTo_idealIncGDDStep` on
   `(n = 2, m = 2, q = 4, β = 1, g = 1, r = 6, ε = 1 / 10000)` for an arbitrary target
   `t : EuclideanSpace ℝ (Fin 2)`, yielding an explicit strictly positive lower bound
   `1 / 4000 > 0`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SISMR07Core

open Cslib Cslib.Crypto Cslib.Crypto.SIS Cslib.Crypto.SIS.MR07 Cslib.Probability
open ZLattice Module MeasureTheory ProbabilityTheory
open scoped _root_.Matrix BigOperators ENNReal NNReal RealInnerProductSpace

/-- Standard 2-D integer identity basis `B = I₂`. -/
def toyB : Matrix (Fin 2) (Fin 2) ℤ := 1

/-- Non-isotropic 2-D sublattice basis `S = diag(2, 3)` of index `6` in `ℤ²`. -/
def toyS : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 3]

private theorem toyB_det : toyB.det = 1 := by
  decide

/-- `toyB` has nonzero determinant. -/
theorem toyB_det_ne : toyB.det ≠ 0 := by
  rw [toyB_det]; decide

private theorem toyS_det : toyS.det = 6 := by
  decide

/-- `toyS` has nonzero determinant. -/
theorem toyS_det_ne : toyS.det ≠ 0 := by
  rw [toyS_det]; decide

/-- `intLattice toyS` is a sublattice of `intLattice toyB`. -/
theorem toyS_le_toyB : intLattice toyS ≤ intLattice toyB := by
  rw [intLattice, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change intCol toyS j ∈ intLattice toyB
  rw [mem_intLattice_iff]
  refine ⟨fun i => toyS i j, ?_⟩
  ext i
  simp [intCol, toyB]

/-- Part 1 cardinality and rank checks on `B = I₂`, `S = diag(2, 3)`, `q = 2`. -/
theorem test_part1_cards :
    Fintype.card (GridRep toyB 2) = 4 ∧
    Fintype.card (GridRep toyS 2) = 24 ∧
    Fintype.card (SublatticeQuot toyB toyS) = 6 ∧
    Module.finrank ℤ (intLattice toyB) = 2 ∧
    ‖intColCast toyB toyS toyB_det_ne‖ = ‖intCol toyS‖ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_gridRep toyB_det_ne (by decide : 0 < 2), toyB_det]; decide
  · rw [card_gridRep toyS_det_ne (by decide : 0 < 2), toyS_det]; decide
  · rw [card_sublatticeQuot toyB_det_ne toyS_det_ne toyS_le_toyB, toyB_det, toyS_det]; decide
  · exact finrank_intLattice toyB_det_ne
  · exact norm_intColCast toyB toyS toyB_det_ne

/-- Part 1 dual-mass monotonicity check on `toyB = I₂` and fine grid `G_4`. -/
theorem test_part1_dual_mono :
    gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin 2))) (gridLattice 2 4)) (1 / 6) 0 - 1 ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB)) (1 / 6) 0 - 1 :=
  gaussianMass_dual_gridLattice_le toyB_det_ne (by decide : 0 < 4) (by norm_num : (0 : ℝ) < 6)

/-- Dual of `intLattice toyB = ℤ²` has minimum nonzero vector norm at least `1`. -/
private theorem dual_toyB_gap
    (w : LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB))
    (hw : w ≠ 0) :
    (1 : ℝ) ≤ ‖(w : EuclideanSpace ℝ (Fin 2))‖ := by
  have hint : ∀ j : Fin 2, ∃ k : ℤ, (w : EuclideanSpace ℝ (Fin 2)) j = (k : ℝ) := by
    intro j
    have hmem : intCol toyB j ∈ intLattice toyB := Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := w.property (intCol toyB j) hmem
    refine ⟨k, ?_⟩
    simp only [LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one, innerₗ_apply_apply] at hk
    have hinner : ⟪(w : EuclideanSpace ℝ (Fin 2)), intCol toyB j⟫ =
        (w : EuclideanSpace ℝ (Fin 2)) j := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      fin_cases j <;> simp [intCol, toyB, dotProduct, Matrix.one_apply]
    exact hinner.symm.trans hk.symm
  have hne : ∃ j : Fin 2, (w : EuclideanSpace ℝ (Fin 2)) j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw
    apply Subtype.ext
    ext j
    exact hall j
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨k₀, hk₀⟩ := hint j₀
  have hk0 : k₀ ≠ 0 := by
    intro h0
    apply hj₀
    rw [hk₀, h0, Int.cast_zero]
  have h1le : (1 : ℝ) ≤ |(k₀ : ℝ)| := by
    have : (1 : ℤ) ≤ |k₀| := Int.one_le_abs hk0
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(k₀ : ℝ)| := h1le
    _ = ‖(w : EuclideanSpace ℝ (Fin 2)) j₀‖ := by rw [hk₀, Real.norm_eq_abs]
    _ ≤ ‖(w : EuclideanSpace ℝ (Fin 2))‖ := PiLp.norm_apply_le (w : EuclideanSpace ℝ (Fin 2)) j₀

/-- Concrete dual-mass bound for `toyB = I₂` at width `s = 12 / √2` (`2 / s = 1 / (6 / √2)`). -/
private theorem toyB_dual_mass_le :
    gaussianMass (LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB))
      (2 / (2 * (6 : ℝ) / ((1 : ℝ) * Real.sqrt (2 : ℕ)))) 0 - 1 ≤ (1 / 10000 : ℝ) := by
  have := isZLattice_intLattice toyB_det_ne
  let s' : ℝ := 6 / Real.sqrt 2
  have hs' : 0 < s' := by positivity
  have hwidth_eq : 2 / (2 * (6 : ℝ) / ((1 : ℝ) * Real.sqrt (2 : ℕ))) = 1 / s' := by
    dsimp only [s']
    simp only [Nat.cast_ofNat]
    field_simp
  rw [hwidth_eq]
  refine ZLattice.gaussianMass_dual_sub_one_le_of_gap (intLattice toyB) s' hs' 1 zero_lt_one
    dual_toyB_gap (1 / 10000) (by norm_num) ?_
  rw [finrank_euclideanSpace_fin]
  have hsq : s' ^ 2 = 18 := by
    dsimp only [s']
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hexp_arg : -3 * Real.pi * s' ^ 2 * 1 ^ 2 / 4 ≤ (-40 : ℝ) := by
    rw [hsq]
    nlinarith
  have h2le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ (40 : ℕ) ≤ Real.exp 40 := by
    calc (2 : ℝ) ^ (40 : ℕ) ≤ (Real.exp 1) ^ (40 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) h2le 40
      _ = Real.exp ((40 : ℕ) * (1 : ℝ)) := (Real.exp_natCast_mul 40 1).symm
      _ = Real.exp 40 := by norm_num
  have hexp_le : Real.exp (-40 : ℝ) ≤ ((2 : ℝ) ^ (40 : ℕ))⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) hpow
  calc (2 : ℝ) ^ 2 * Real.exp (-3 * Real.pi * s' ^ 2 * 1 ^ 2 / 4)
      ≤ 4 * Real.exp (-40 : ℝ) := by
        have h := Real.exp_le_exp.mpr hexp_arg
        nlinarith
    _ ≤ 4 * ((2 : ℝ) ^ (40 : ℕ))⁻¹ := by linarith
    _ ≤ (1 / 10000 : ℝ) / (1 + 1 / 10000) := by norm_num

/-- Part 2 check: exact conditional discrete-Gaussian factorization
(`idealGridSample_eq_bind_discreteGaussian`) and discrete-grid marginal closeness
(`idealGridSample_fst_closeTo_uniform`) on `toyB = I₂`, `q = 4`, `ε = 1 / 10000`. -/
theorem test_part2_grid_sample (t : EuclideanSpace ℝ (Fin 2)) :
    let s : ℝ := 2 * (6 : ℝ) / ((1 : ℝ) * Real.sqrt (2 : ℕ))
    have hs : 0 < s := by positivity
    (idealGridSample toyB toyB_det_ne 4 (by decide) s hs t =
      ((idealGridSample toyB toyB_det_ne 4 (by decide) s hs t).map Prod.fst).bind fun c =>
        (ZLattice.discreteGaussian (intLattice toyB) s hs (t + c.toVec)).map fun y => (c, y)) ∧
    CloseTo ((idealGridSample toyB toyB_det_ne 4 (by decide) s hs t).map Prod.fst)
      (PMF.uniformOfFintype (GridRep toyB 4))
      (ENNReal.ofReal ((1 / 10000 : ℝ) / (2 * (1 - 1 / 10000)))) := by
  intro s hs
  have := isZLattice_intLattice toyB_det_ne
  have : DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB)) :=
    discreteTopology_dualSubmodule (intLattice toyB)
  have hdual_s : gaussianMass (LinearMap.BilinForm.dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB)) (1 / s) 0 - 1 ≤ (1 / 10000 : ℝ) := by
    have hle := ZLattice.gaussianMass_le_of_le
      (LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin 2))) (intLattice toyB))
      (one_div_pos.mpr hs) (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hs.le) 0
    have hdual2 := toyB_dual_mass_le
    dsimp only [s] at hle ⊢
    linarith
  exact ⟨idealGridSample_eq_bind_discreteGaussian toyB toyB_det_ne 4 (by decide) s hs t,
    idealGridSample_fst_closeTo_uniform toyB toyB_det_ne 4 (by decide) hs
      (by norm_num) (by norm_num) hdual_s t⟩

/-- Part 3 checks: HNF-free quotient surjection, uniform SIS matrix distribution,
unconditional lattice membership on a non-kernel `z = ![1, 1]`, and the combining norm bound
on the nonzero kernel vector `z = ![4, 0]`. -/
theorem test_part3_combine
    (V : Fin 2 → SublatticeQuot toyB toyS) (C : Fin 2 → GridRep toyB 4) :
    letI : NeZero (toyS.det / toyB.det).natAbs :=
      ⟨by
        rw [← card_sublatticeQuot toyB_det_ne toyS_det_ne toyS_le_toyB]
        exact Fintype.card_ne_zero⟩
    (PMF.uniformOfFintype (Fin 2 → ZMod (toyS.det / toyB.det).natAbs)).map
        (quotientHom toyB toyS toyS_det_ne toyS_le_toyB) =
      PMF.uniformOfFintype (SublatticeQuot toyB toyS) ∧
    (PMF.uniformOfFintype (Fin 2 → GridRep toyB 4)).bind
      (fun C' => (PMF.uniformOfFintype (Fin 2 → SublatticeQuot toyB toyS)).map
        (fun V' => combineMatrix toyB toyS 4 V' C')) =
      PMF.uniformOfFintype (Matrix (Fin 2) (Fin 2) (ZMod 4)) ∧
    combineOutput toyB toyS 4 V C ![1, 1] ∈ intLattice toyB ∧
    ‖combineOutput toyB toyS 4 V C ![4, 0] -
        ∑ i : Fin 2, (![4, 0] : Fin 2 → ℤ) i • (C i).toVec‖ ≤
      Real.sqrt (2 : ℕ) * (2 : ℕ) * ‖intCol toyS‖ *
        ‖WithLp.toLp 2 (fun i : Fin 2 => ((![4, 0] : Fin 2 → ℤ) i : ℝ))‖ / (4 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact map_quotientHom_uniform_eq_uniform_sublatticeQuot toyB toyS
      toyB_det_ne toyS_det_ne toyS_le_toyB
  · exact idealCombine_matrix_eq_uniform toyB toyS toyB_det_ne toyS_det_ne toyS_le_toyB
  · exact combineOutput_mem_intLattice toyB toyS toyS_det_ne toyS_le_toyB 4 (by decide) V C ![1, 1]
  · have hker : InKernelLattice (combineMatrix toyB toyS 4 V C) ![4, 0] := by
      unfold InKernelLattice
      have h4 : (4 : ZMod 4) = 0 := rfl
      ext i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h4]
    exact (combineOutput_mem_intLattice_and_norm_sub_le (by decide : 0 < 4) toyB toyS
      toyS_det_ne toyS_le_toyB V C ![4, 0] hker).2

/-- Explicit map and parallelepiped characterizations (`idealGridSample_eq_map`,
`quotientHom_toVec`, `combineColumn_fst_toVec`, and `combineColumn_snd_val`) exercised on
`toyB = I₂` and `toyS = diag(2, 3)`. -/
theorem test_part2_part3_interfaces
    (x : Fin 2 → ZMod (toyS.det / toyB.det).natAbs)
    (v : SublatticeQuot toyB toyS) (c : GridRep toyB 4) (k : Fin 2)
    (t : EuclideanSpace ℝ (Fin 2))
    (f : gridLattice 2 4 → GridRep toyB 4 × intLattice toyB)
    (hf_fst : ∀ r, (f r).1.toVec = modParallelepiped toyB (-r.val))
    (hf_snd : ∀ r, ((f r).2 : EuclideanSpace ℝ (Fin 2)) = r.val + (f r).1.toVec) :
    idealGridSample toyB toyB_det_ne 4 (by decide) 6 (by norm_num) t =
      (ZLattice.discreteGaussian (gridLattice 2 4) 6 (by norm_num) t).map f ∧
    (quotientHom toyB toyS toyS_det_ne toyS_le_toyB x).toVec =
      modParallelepiped toyS
        (WithLp.toLp 2 (fun i => ((toyB *ᵥ fun j => ((x j).val : ℤ)) i : ℝ))) ∧
    (combineColumn toyB toyS 4 v c).1.toVec = modParallelepiped toyS (v.toVec + c.toVec) ∧
    (((combineColumn toyB toyS 4 v c).2 k).val : ℤ) =
      Int.floor ((4 : ℝ) * (((toyS.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ
        WithLp.ofLp (combineColumn toyB toyS 4 v c).1.toVec) k)) :=
  ⟨idealGridSample_eq_map toyB toyB_det_ne 4 (by decide) 6 (by norm_num) t f hf_fst hf_snd,
   quotientHom_toVec toyB toyS toyS_det_ne toyS_le_toyB x,
   combineColumn_fst_toVec toyS_det_ne (by decide : 0 < 4) v c,
   by simpa using combineColumn_snd_val toyS_det_ne (by decide : 0 < 4) v c k⟩

/-- Deterministic toy `ℓ₂`-SIS solver outputting the first standard basis vector `![1, 0]`. -/
def toySolver : Matrix (Fin 2) (Fin 2) (ZMod 4) → ProbComp (Fin 2 → ℤ) :=
  fun _ => pure ![1, 0]

private theorem toySolver_adv_ge :
    (1 / 256 : ℝ) ≤ (sisEll2Advantage 4 1 toySolver : ℝ) := by
  classical
  have hsol0 : IsEll2Solution (0 : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 ![1, 0] := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_two]
    · ext i
      simp [Matrix.mulVec, dotProduct]
  have hcard : Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod 4)) = 256 := by
    change Fintype.card (Fin 2 → Fin 2 → ZMod 4) = 256
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    norm_num
  have hle_enn : (256 : ℝ≥0∞)⁻¹ ≤
      (ProbComp.eval (sisEll2Experiment 4 1 toySolver)) true := by
    unfold sisEll2Experiment toySolver
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_apply,
      PMF.pure_apply]
    refine le_trans ?_ (le_tsum (a := (0 : Matrix (Fin 2) (Fin 2) (ZMod 4))) _)
    rw [PMF.uniformOfFintype_apply, hcard]
    simp only [Nat.cast_ofNat]
    rw [tsum_eq_single (![1, 0] : Fin 2 → ℤ) (fun z hz => by simp [hz])]
    simp [hsol0]
  have htoR := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hle_enn
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at htoR
  have h1 : (1 / 256 : ℝ) = (256 : ℝ)⁻¹ := one_div 256
  rw [h1]
  exact htoR

/-- Part 4 non-vacuous check: all hypotheses of `idealIncGDDStep_succProb_of_sisEll2` and
`incGDD_succProb_of_closeTo_idealIncGDDStep` are simultaneously satisfied on
`(n = 2, m = 2, q = 4, B = I₂, S = diag(2, 3), β = 1, g = 1, r = 6, ε = 1 / 10000)` for any
target `t : EuclideanSpace ℝ (Fin 2)` (including non-origin targets where `0 ∈ L(B)` is not a
trivial `IncGDD` solution), with a strictly positive concrete lower bound `1 / 4000 > 0`. -/
theorem test_part4_incGDD_nonvacuous (t : EuclideanSpace ℝ (Fin 2)) :
    (1 / 4000 : ℝ) ≤
      ((idealIncGDDStep toyB toyS toyB_det_ne
          1 6 le_rfl (by norm_num) t toySolver).toOuterMeasure
        {v | IncGDD.IsSolution 1 (intLattice toyB)
          (intColCast toyB toyS toyB_det_ne) t 6 v}).toReal ∧
    (∀ v ∈ (idealIncGDDStep toyB toyS toyB_det_ne
          1 6 le_rfl (by norm_num) t toySolver).support, v ∈ intLattice toyB) ∧
    (∀ μ : PMF (EuclideanSpace ℝ (Fin 2)),
      CloseTo μ
        (idealIncGDDStep toyB toyS toyB_det_ne
          1 6 le_rfl (by norm_num) t toySolver)
        (ENNReal.ofReal (1 / 100000 : ℝ)) →
      (1 / 5000 : ℝ) ≤
        (μ.toOuterMeasure
          {v | IncGDD.IsSolution 1 (intLattice toyB)
            (intColCast toyB toyS toyB_det_ne) t 6 v}).toReal) := by
  have hsqrt2_lt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hε : (1 / 10000 : ℝ) ≤ 1 / (400 * max 1 (Real.sqrt (2 : ℕ))) := by
    have hmax : max (1 : ℝ) (Real.sqrt (2 : ℕ)) ≤ 2 := by
      simpa only [Nat.cast_ofNat] using max_le (by norm_num) hsqrt2_lt.le
    have hpos : (0 : ℝ) < 400 * max 1 (Real.sqrt (2 : ℕ)) := by positivity
    rw [div_le_div_iff₀ (by norm_num) hpos]
    nlinarith
  have hq : (1 : ℝ) * (2 : ℕ) * Real.sqrt (2 : ℕ) * 1 ≤ (4 : ℕ) := by
    simp only [Nat.cast_ofNat]
    nlinarith
  have hbase := idealIncGDDStep_succProb_of_sisEll2 (q := 4)
    (by decide : 1 ≤ 2) (by decide : 1 ≤ 2)
    toyB toyS toyB_det_ne toyS_det_ne toyS_le_toyB
    (β := 1) (g := 1) (r := 6) (ε := 1 / 10000)
    le_rfl zero_lt_one (by norm_num) (by norm_num) hε hq toyB_dual_mass_le t toySolver
  have hfloor : (Nat.floor (1 : ℝ) : ℝ) = 1 := by norm_num
  have hadv := toySolver_adv_ge
  have hnum : (1 / 4000 : ℝ) ≤
      (1 / 3 : ℝ) * ((sisEll2Advantage 4 1 toySolver : ℝ) /
          (2 * (Nat.floor (1 : ℝ) : ℝ) * (2 : ℕ)) -
        (2 : ℕ) * (1 / 10000 : ℝ) / (2 * (1 - 1 / 10000))) := by
    rw [hfloor]
    push_cast
    linarith
  refine ⟨hnum.trans hbase, ?_, ?_⟩
  · exact fun _ hv => idealIncGDDStep_support_mem_intLattice toyB toyS toyB_det_ne toyS_det_ne
      toyS_le_toyB 1 6 le_rfl (by norm_num) t toySolver hv
  · intro μ hclose
    have htr := incGDD_succProb_of_closeTo_idealIncGDDStep (q := 4)
      (by decide : 1 ≤ 2) (by decide : 1 ≤ 2)
      toyB toyS toyB_det_ne toyS_det_ne toyS_le_toyB
      (β := 1) (g := 1) (r := 6) (ε := 1 / 10000) (η := 1 / 100000)
      le_rfl zero_lt_one (by norm_num) (by norm_num) hε (by norm_num)
      hq toyB_dual_mass_le t toySolver μ hclose
    linarith

end CslibFrontierTests.Crypto.SISMR07Core
