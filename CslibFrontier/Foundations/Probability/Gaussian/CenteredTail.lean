/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.MassBounds
public import CslibFrontier.Foundations.Probability.Gaussian.DiscreteTail

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Real

/-!
# Uniform tails of centered lattice Gaussians

## Main results

* `ZLattice.discreteGaussian_zero_norm_ge_le`: a bound uniform over full-rank lattices
  at every radius.
* `ZLattice.discreteGaussian_zero_norm_gt_sqrt_lt`: the strict probability bound outside
  radius `s * sqrt dim`, including dimension zero.
* `ZLattice.gaussianMass_dual_sub_one_le_of_gap`: a quantitative sufficient width criterion
  bounding the nonzero dual Gaussian mass from an explicit dual norm gap.

## References

The strict-radius endpoint is the normalized probability form of [Regev2009], Lemma 2.5,
printed page 16 of the May 2, 2009 author version, credited there to Banaszczyk. Its mass
comparison is proved using Lemma 2.4, rather than assumed. The proof uses the exponential
moment at width `2 * s`. The dual-gap width criterion supports the dual-tail condition in
[Regev2009], Claim 3.8, and the smoothing-parameter upper bound in [MicciancioRegev2007],
Lemma 3.2. These estimates are centered at zero; uniform off-center estimates, eventual
smoothing criteria, efficient sampling and the quantum reduction remain separate work.
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A uniform centered tail estimate obtained by doubling the width in the exponential moment. -/
theorem discreteGaussian_zero_norm_ge_le (s : ℝ) (hs : 0 < s) (R : ℝ) (hR : 0 ≤ R) :
    (discreteGaussian L s hs 0).toOuterMeasure {z : L | R ≤ ‖(z : E)‖} ≤
      ENNReal.ofReal (2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * R ^ 2 / (4 * s ^ 2))) := by
  have ht : s < 2 * s := by linarith
  have h := discreteGaussian_norm_ge_le L s hs (2 * s) ht 0 R hR
  simp only [sub_zero] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-Real.pi * (1 / s ^ 2 - 1 / (2 * s) ^ 2) * R ^ 2) *
        ((2 * s) / s) ^ finrank ℝ E :=
      mul_le_mul_of_nonneg_left (gaussianMass_zero_div_le L s hs (2 * s) ht.le)
        (Real.exp_pos _).le
    _ = 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * R ^ 2 / (4 * s ^ 2)) := by
      have hw : (2 * s) / s = 2 := by field_simp
      rw [hw, mul_comm]
      congr 2
      field_simp
      ring

private theorem two_pow_mul_exp_lt_quarter_pow (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ n * Real.exp (-3 * Real.pi * n / 4) < (1 / 4 : ℝ) ^ n := by
  have hpi : 4 * Real.log 2 < Real.pi := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have he : (2 : ℝ) * Real.exp (-3 * Real.pi / 4) < 1 / 4 := by
    have h : Real.log 2 - 3 * Real.pi / 4 < -2 * Real.log 2 := by linarith
    have hh := Real.exp_lt_exp.mpr h
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
    have hr : Real.exp (-2 * Real.log 2) = (1 / 4 : ℝ) := by
      rw [show -2 * Real.log 2 = -((2 : ℕ) * Real.log 2) by ring, Real.exp_neg,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hr] at hh
    simpa only [neg_mul, neg_div, Real.exp_neg, div_eq_mul_inv] using hh
  have hp := pow_lt_pow_left₀ he (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-3 * Real.pi / 4)) hn.ne'
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 2
  ring

/-- A centered discrete Gaussian lies strictly outside radius `s * sqrt dim` with probability
strictly less than `4 ^ (-dim)`. In dimension zero the strict event is empty. -/
theorem discreteGaussian_zero_norm_gt_sqrt_lt (s : ℝ) (hs : 0 < s) :
    (discreteGaussian L s hs 0).toOuterMeasure
      {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E)‖} <
        ENNReal.ofReal ((1 / 4 : ℝ) ^ finrank ℝ E) := by
  by_cases hn : finrank ℝ E = 0
  · have : Subsingleton E := (finrank_zero_iff).mp hn
    have hempty : {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E)‖} = ∅ := by
      ext z
      change (s * Real.sqrt (finrank ℝ E) < ‖(z : E)‖) ↔ False
      rw [Subsingleton.elim (z : E) 0, hn]
      simp
    rw [hempty, measure_empty, hn]
    norm_num
  · have hnpos : 0 < finrank ℝ E := Nat.pos_of_ne_zero hn
    have h := discreteGaussian_zero_norm_ge_le L s hs
      (s * Real.sqrt (finrank ℝ E)) (by positivity)
    have heq : -3 * Real.pi * (s * Real.sqrt (finrank ℝ E)) ^ 2 / (4 * s ^ 2) =
        -3 * Real.pi * finrank ℝ E / 4 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
    rw [heq] at h
    have hsubset : {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E)‖} ⊆
        {z : L | s * Real.sqrt (finrank ℝ E) ≤ ‖(z : E)‖} := by
      intro z hz
      change s * Real.sqrt (finrank ℝ E) < ‖(z : E)‖ at hz
      change s * Real.sqrt (finrank ℝ E) ≤ ‖(z : E)‖
      exact le_of_lt hz
    apply lt_of_le_of_lt ((discreteGaussian L s hs 0).toOuterMeasure.mono hsubset)
    apply lt_of_le_of_lt h
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (two_pow_mul_exp_lt_quarter_pow (finrank ℝ E) hnpos)

private theorem discreteGaussian_nonzero_toReal
    (M : Submodule ℤ E) [DiscreteTopology M] (s : ℝ) (hs : 0 < s) :
    ((discreteGaussian M s hs 0).toOuterMeasure {z : M | z ≠ 0}).toReal =
      1 - 1 / gaussianMass M s 0 := by
  let p := discreteGaussian M s hs 0
  have hevent : {z : M | z ≠ 0} = ({0} : Set M)ᶜ := rfl
  rw [hevent, ← PMF.toMeasure_apply_eq_toOuterMeasure_apply p
    (measurableSet_singleton 0).compl]
  change p.toMeasure.real ({0} : Set M)ᶜ = _
  rw [probReal_compl_eq_one_sub (measurableSet_singleton 0), Measure.real,
    PMF.toMeasure_apply_singleton p 0 (measurableSet_singleton 0)]
  simp [p, discreteGaussian_apply_toReal, gaussianWeight]

/-- An explicit dual gap and exponential width criterion bound the actual nonzero dual mass.
The error `ε` is arbitrary and positive; it is not assumed to bound the desired mass. -/
theorem gaussianMass_dual_sub_one_le_of_gap (s : ℝ) (hs : 0 < s) (a : ℝ) (ha : 0 < a)
    (hgap : ∀ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
      w ≠ 0 → a ≤ ‖(w : E)‖)
    (ε : ℝ) (hε : 0 < ε)
    (hwidth : 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * s ^ 2 * a ^ 2 / 4) ≤
      ε / (1 + ε)) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have : IsZLattice ℝ D := isZLattice_dualSubmodule L
  have hs' : 0 < 1 / s := one_div_pos.mpr hs
  have htail := discreteGaussian_zero_norm_ge_le D (1 / s) hs' a ha.le
  have hexp : -3 * Real.pi * a ^ 2 / (4 * (1 / s) ^ 2) =
      -3 * Real.pi * s ^ 2 * a ^ 2 / 4 := by
    field_simp
  rw [hexp] at htail
  have hsubset : {w : D | w ≠ 0} ⊆ {w : D | a ≤ ‖(w : E)‖} := fun w hw ↦ hgap w hw
  have hprob := ((discreteGaussian D (1 / s) hs' 0).toOuterMeasure.mono hsubset).trans
    (htail.trans (ENNReal.ofReal_le_ofReal hwidth))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
  rw [OuterMeasure.measureOf_eq_coe, discreteGaussian_nonzero_toReal D (1 / s) hs',
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hm : 0 < gaussianMass D (1 / s) 0 := gaussianMass_pos D (1 / s) hs' 0
  have he : 0 < 1 + ε := by positivity
  have hr : 1 - 1 / gaussianMass D (1 / s) 0 =
      (gaussianMass D (1 / s) 0 - 1) / gaussianMass D (1 / s) 0 := by
    field_simp
  rw [hr] at hreal
  have hmul := (div_le_div_iff₀ hm he).mp hreal
  change gaussianMass D (1 / s) 0 - 1 ≤ ε
  nlinarith

end ZLattice
