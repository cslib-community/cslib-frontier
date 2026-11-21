/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Computability.Probabilistic.DiscreteGaussian1D

import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Non-vacuous `module` client tests for the strict-PPT 1-D discrete Gaussian sampler `sampleZ`,
grid Gaussian sampler `sampleGridGaussian`, and HNF-free quotient sampler `sampleQuotientModS`.
-/

open Module ProbabilityTheory Cslib Cslib.Probability Cslib.LinearAlgebra
open scoped ENNReal RealInnerProductSpace

public section

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

private theorem dual_gap1 (w : D1) (hw : w ≠ 0) : (1 : ℝ) ≤ ‖(w : ℝ)‖ := by
  have h1 : (1 : ℝ) ∈ intLatticeReal := by
    rw [intLatticeReal]
    exact Submodule.subset_span (Set.mem_range.mpr ⟨(), by simp⟩)
  have hm := w.property 1 h1
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hk' : (k : ℝ) = (w : ℝ) := by
    simpa [real_inner_comm] using hk
  have hkn : k ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    change (w : ℝ) = 0
    rw [h, Int.cast_zero] at hk'
    exact hk'.symm
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hkn)
  rwa [hk', ← Real.norm_eq_abs] at ha

private theorem dual_small_two : ZLattice.gaussianMass D1 (1 / 2) 0 - 1 ≤ 1 / 2 := by
  have h := ZLattice.gaussianMass_dual_sub_one_le_of_gap intLatticeReal 2 (by norm_num)
    1 (by norm_num) dual_gap1 (1 / 2) (by norm_num) (by
      have hdim : finrank ℝ ℝ = 1 := finrank_self ℝ
      have hexp : -3 * Real.pi * (2 : ℝ) ^ 2 * 1 ^ 2 / 4 = -3 * Real.pi := by ring
      rw [hdim, pow_one, hexp]
      linarith [exp_neg_three_pi_lt_one_sixteenth])
  exact h

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

/-- Concrete `SampleZInput` (`sSq = 4`, `center = 1 / 3`, `tail = 2`, `prec = 10`,
`maxTrials = 340`) satisfying every hypothesis of `closeTo_eval_sampleZ_discreteGaussian` with
explicit statistical distance `< 1 / 4`. -/
def concreteSampleZInput : SampleZInput :=
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

/-- Concrete 2-D identity basis `B = I₂`. -/
def basisI2 : IntTable := ⟨2, 2, [[1, 0], [0, 1]]⟩

/-- Concrete 2-D diagonal sublattice basis `S = diag(2, 3)` of quotient index `D = 6`. -/
def sublatticeDiag23 : IntTable := ⟨2, 2, [[2, 0], [0, 3]]⟩

example : quotientIndex basisI2 sublatticeDiag23 = 6 := by decide

example : gridReduceInt 2 5 basisI2 [7, -3] = ([3, 3], [2, 0]) := by decide

example : quotientReduceInt 2 basisI2 sublatticeDiag23 [5, 4] = [1, 1] := by decide

example :
    let inp : QuotientSampleInput :=
      { dim := 2, basis := basisI2, sublattice := sublatticeDiag23, extraBits := 10 }
    CloseTo (ProbComp.eval (sampleQuotientModS inp))
      ((PMF.piFin fun _ : Fin 2 => PMF.uniformOfFintype (ZMod 6)).map
        fun z => quotientReduceInt 2 basisI2 sublatticeDiag23
          (List.ofFn fun i => (z i).val))
      ((2 : ℝ≥0∞) / 2 ^ 10) := by
  intro inp
  have hD : quotientIndex inp.basis inp.sublattice = 6 := by decide
  have h := closeTo_eval_sampleQuotientModS_pi inp (by rw [hD]; omega)
  dsimp only [inp] at h hD ⊢
  revert h
  generalize quotientIndex basisI2 sublatticeDiag23 = D at hD ⊢
  subst hD
  intro h
  exact h

/-- Concrete 2-D `GridSampleInput` (`dim = 2`, `q = 2`, `B = I₂`, `s² = 1`, `target = [0, 1/3]`)
satisfying every hypothesis of `closeTo_eval_sampleGridGaussian_pi` with distance `< 1 / 2`. -/
def concreteGridInput : GridSampleInput :=
  { dim := 2, modulus := 2, basis := basisI2, sSq := 1, target := [0, 1 / 3],
    tail := 2, prec := 10, maxTrials := 340 }

example :
    CloseTo (ProbComp.eval (sampleGridGaussian concreteGridInput))
      ((PMF.piFin fun i : Fin 2 =>
          discreteGaussianInt 2 (by norm_num)
            ((2 : ℝ) * (concreteGridInput.target.getD i.val 0 : ℝ))).map
        fun r => gridReduceInt 2 2 basisI2 (List.ofFn r))
      (ENNReal.ofReal (1 / 2)) := by
  have hqs : (concreteGridInput.modulus : ℝ) * Real.sqrt (concreteGridInput.sSq : ℝ) = 2 := by
    simp [concreteGridInput]
  have h := closeTo_eval_sampleGridGaussian_pi concreteGridInput
    (by decide : (0 : ℚ) < 1) (by decide : 0 < 2)
    (by rw [hqs]; norm_num) (by decide : 1 ≤ 2)
    (ε := 1 / 2) (by norm_num) (by norm_num)
    (by rw [hqs]; exact dual_small_two)
    (by decide : 8 * (2 * 2 + 6) ≤ 2 ^ 10)
  have hpmf :
      (PMF.piFin fun i : Fin concreteGridInput.dim =>
          discreteGaussianInt
            ((concreteGridInput.modulus : ℝ) * Real.sqrt (concreteGridInput.sSq : ℝ))
            (by positivity)
            ((concreteGridInput.modulus : ℝ) * (concreteGridInput.target.getD i.val 0 : ℝ))) =
        (PMF.piFin fun i : Fin 2 =>
          discreteGaussianInt 2 (by norm_num)
            ((2 : ℝ) * (concreteGridInput.target.getD i.val 0 : ℝ))) := by
    congr 1
    funext i
    congr 1
  rw [hpmf] at h
  refine h.mono (ENNReal.ofReal_le_ofReal ?_)
  dsimp only [concreteGridInput]
  have h2 := mul_le_mul_of_nonneg_left concrete_sampleZ_err_le_quarter
    (by norm_num : (0 : ℝ) ≤ ((2 : ℕ) : ℝ))
  exact h2.trans (by norm_num)

example : Cslib.Probability.IsPPTOn SampleZInput.enc Turing.MultiTapeTM.encIntBin sampleZ :=
  isPPTOn_sampleZ

example :
    Cslib.Probability.IsPPTOn GridSampleInput.enc
      (Turing.MultiTapeTM.encPair (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin)
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin))
      sampleGridGaussian :=
  isPPTOn_sampleGridGaussian

example :
    Cslib.Probability.IsPPTOn QuotientSampleInput.enc
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin)
      sampleQuotientModS :=
  isPPTOn_sampleQuotientModS

example {z : ℤ} (hz : z ∈ (ProbComp.eval (sampleZ concreteSampleZInput)).support) :
    |z| ≤ 6 := by
  have h := mem_support_sampleZ_abs_sub_le concreteSampleZInput hz
  have hfloor : concreteSampleZInput.center.floor = 0 := by
    dsimp only [concreteSampleZInput]
    rw [show (1 / 3 : ℚ).floor = Int.floor (1 / 3 : ℚ) from rfl, Int.floor_eq_iff]
    norm_num
  have hrad :
      (Nat.sqrt ((concreteSampleZInput.tail ^ 2 * concreteSampleZInput.sSq.num.natAbs) /
        concreteSampleZInput.sSq.den) + 2 : ℤ) = 6 := by
    dsimp only [concreteSampleZInput]
    have hnum : (4 : ℚ).num = 4 := rfl
    have hden : (4 : ℚ).den = 1 := rfl
    rw [hnum, hden, show 2 ^ 2 * Int.natAbs 4 / 1 = 4 * 4 by norm_num, Nat.sqrt_eq]
    norm_num
  rw [hfloor, sub_zero, hrad] at h
  exact h

example {p : List ℤ × List ℤ}
    (hp : p ∈ (ProbComp.eval (sampleGridGaussian concreteGridInput)).support) :
    ∃ r' : List ℤ, r'.length = 2 ∧ p = gridReduceInt 2 2 basisI2 r' :=
  mem_support_sampleGridGaussian concreteGridInput hp

example {v : List ℤ}
    (hv : v ∈ (ProbComp.eval (sampleQuotientModS
      { dim := 2, basis := basisI2, sublattice := sublatticeDiag23, extraBits := 10 })).support) :
    ∃ x : List ℕ, x.length = 2 ∧ v = quotientReduceInt 2 basisI2 sublatticeDiag23 x := by
  rcases mem_support_sampleQuotientModS _ hv with rfl | hx
  · exact ⟨[0, 0], rfl, by decide⟩
  · exact hx

end CslibFrontierTests.DiscreteGaussian1D
