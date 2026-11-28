/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Probabilistic.DiscreteGaussian1D
import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Non-vacuous `module` client tests for the strict-PPT 1-D discrete Gaussian sampler `sampleZ`
and the 1-D integer lattice distribution `ZLattice.discreteGaussianInt`.
-/

set_option linter.privateModule false

open Module ProbabilityTheory Cslib Cslib.Probability ZLattice
open scoped ENNReal RealInnerProductSpace

namespace CslibFrontierTests.DiscreteGaussian1D

private theorem exp_neg_three_pi_lt_one_sixteenth : Real.exp (-3 * Real.pi) < 1 / 16 := by
  have hpi : 4 * Real.log 2 < 3 * Real.pi := by linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have hlt : Real.exp (-3 * Real.pi) < Real.exp (-4 * Real.log 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hval : Real.exp (-4 * Real.log 2) = 1 / 16 := by
    rw [show (-4 : ℝ) * Real.log 2 = -((4 : ℕ) * Real.log 2) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rwa [hval] at hlt

private noncomputable abbrev D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal

private instance : DiscreteTopology D1 := ZLattice.discreteTopology_dualSubmodule intLatticeReal
private instance : IsZLattice ℝ D1 := ZLattice.isZLattice_dualSubmodule intLatticeReal

private theorem dual_small_two : ZLattice.gaussianMass D1 (1 / 2) 0 - 1 ≤ 1 / 2 :=
  ZLattice.gaussianMass_dual_sub_one_le_of_gap intLatticeReal 2 (by norm_num)
    1 (by norm_num) (fun _ hw => ZLattice.one_le_norm_of_mem_dualSubmodule_intLatticeReal hw)
    (1 / 2) (by norm_num) (by
      have hdim : finrank ℝ ℝ = 1 := finrank_self ℝ
      have hexp : -3 * Real.pi * (2 : ℝ) ^ 2 * 1 ^ 2 / 4 = -3 * Real.pi := by ring
      rw [hdim, pow_one, hexp]
      linarith [exp_neg_three_pi_lt_one_sixteenth])

private theorem concrete_sampleZ_err_le_quarter :
    (1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340 +
      (8 * (2 : ℕ) + 24 : ℝ) / (2 : ℝ) ^ 10 +
      (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (2 * Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2)) ≤
    1 / 4 := by
  have hterm1 : (1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340 ≤ 1 / 8 := by
    have h1 : (1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ≤ Real.exp (-1 / 160) := by
      have hexp := Real.add_one_le_exp (-1 / 160 : ℝ)
      push_cast; linarith
    have hnn : 0 ≤ 1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ)) := by norm_num
    have hpow : (1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340 ≤
        (Real.exp (-1 / 160)) ^ 340 := pow_le_pow_left₀ hnn h1 340
    have hexp_mul : (Real.exp (-1 / 160)) ^ 340 = Real.exp (-340 / 160) := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    have hlog : 3 * Real.log 2 < 340 / 160 := by linarith [Real.log_two_lt_d9]
    have hlt : Real.exp (-340 / 160) < Real.exp (-3 * Real.log 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    have hval : Real.exp (-3 * Real.log 2) = 1 / 8 := by
      rw [show (-3 : ℝ) * Real.log 2 = -((3 : ℕ) * Real.log 2) by norm_num, Real.exp_neg,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hexp_mul] at hpow
    rw [hval] at hlt
    exact hpow.trans hlt.le
  have hterm2 : (8 * (2 : ℕ) + 24 : ℝ) / (2 : ℝ) ^ 10 ≤ 1 / 16 := by norm_num
  have hterm3 : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) *
      (2 * Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2)) ≤ 1 / 16 := by
    have hlog : 7 * Real.log 2 < 4 * Real.pi := by linarith [Real.log_two_lt_d9, Real.pi_gt_three]
    have hlt : Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2) < Real.exp (-7 * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      push_cast; linarith
    have hval : Real.exp (-7 * Real.log 2) = 1 / 128 := by
      rw [show (-7 : ℝ) * Real.log 2 = -((7 : ℕ) * Real.log 2) by norm_num, Real.exp_neg,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hcoef : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 := by norm_num
    rw [hcoef]
    rw [hval] at hlt
    linarith
  exact (add_le_add (add_le_add hterm1 hterm2) hterm3).trans (by norm_num)

private def concreteSampleZInput : SampleZInput :=
  { sSq := 4, center := 1 / 3, tail := 2, prec := 10, maxTrials := 340 }

private theorem concreteSampleZInput_sqrt :
    Real.sqrt ((concreteSampleZInput.sSq : ℚ) : ℝ) = 2 := by
  simp only [concreteSampleZInput, Rat.cast_ofNat]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem concreteSampleZInput_dg_eq :
    discreteGaussianInt (Real.sqrt ((concreteSampleZInput.sSq : ℚ) : ℝ))
      (by rw [concreteSampleZInput_sqrt]; norm_num) (concreteSampleZInput.center : ℝ) =
      discreteGaussianInt 2 (by norm_num) (1 / 3 : ℝ) := by
  have hcenter : (concreteSampleZInput.center : ℝ) = 1 / 3 := by simp [concreteSampleZInput]
  have hsqrt4 := concreteSampleZInput_sqrt
  congr 1

example :
    CloseTo (ProbComp.eval (sampleZ concreteSampleZInput))
      (discreteGaussianInt 2 (by norm_num) (1 / 3 : ℝ))
      (ENNReal.ofReal (1 / 4)) := by
  have h := closeTo_eval_sampleZ_discreteGaussian concreteSampleZInput
    (by decide : (0 : ℚ) < 4) (by rw [concreteSampleZInput_sqrt]; norm_num) (by decide : 1 ≤ 2)
    (ε := 1 / 2) (by norm_num) (by norm_num)
    (by rw [concreteSampleZInput_sqrt]; exact dual_small_two)
    (by decide : 8 * (2 * 2 + 6) ≤ 2 ^ 10)
  rw [concreteSampleZInput_dg_eq] at h
  exact h.mono (ENNReal.ofReal_le_ofReal concrete_sampleZ_err_le_quarter)

example :
    CloseTo (ProbComp.eval (sampleZ concreteSampleZInput))
      (discreteGaussianInt 2 (by norm_num) (1 / 3 : ℝ))
      (ENNReal.ofReal (1 / 4)) := by
  have hη : ZLattice.smoothingParameter intLatticeReal (1 / 2) ≤ 2 :=
    ZLattice.smoothingParameter_le_of_dual_mass_le intLatticeReal (by norm_num) dual_small_two
  have h := closeTo_eval_sampleZ_discreteGaussian_of_smoothingParameter_le concreteSampleZInput
    (by decide : (0 : ℚ) < 4) (by rw [concreteSampleZInput_sqrt]; norm_num) (by decide : 1 ≤ 2)
    (ε := 1 / 2) (by norm_num) (by norm_num) (by rw [concreteSampleZInput_sqrt]; exact hη)
    (by decide : 8 * (2 * 2 + 6) ≤ 2 ^ 10)
  rw [concreteSampleZInput_dg_eq] at h
  exact h.mono (ENNReal.ofReal_le_ofReal concrete_sampleZ_err_le_quarter)

example : Cslib.Probability.IsPPTOn SampleZInput.enc Turing.MultiTapeTM.encIntBin sampleZ :=
  isPPTOn_sampleZ

example {z : ℤ} (hz : z ∈ (ProbComp.eval (sampleZ concreteSampleZInput)).support) :
    |(z : ℝ) - (1 / 3 : ℝ)| ≤ 7 := by
  have h := mem_support_sampleZ_abs_sub_le concreteSampleZInput (by decide : (0 : ℚ) < 4) hz
  rw [concreteSampleZInput_sqrt] at h
  dsimp only [concreteSampleZInput] at h
  norm_num at h
  exact h

end CslibFrontierTests.DiscreteGaussian1D
