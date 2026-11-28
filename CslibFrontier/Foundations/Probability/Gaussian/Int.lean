/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate (Mathlib, 1-D integer discrete Gaussian distribution)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import Mathlib.Algebra.Module.ZLattice.Covolume

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One-dimensional discrete Gaussian distribution on `ℤ`

Specializes `ZLattice.discreteGaussian` to the standard one-dimensional integer lattice
`ZLattice.intLatticeReal = ℤ ⊂ ℝ`, giving `ZLattice.discreteGaussianInt` as a `PMF ℤ` together
with its pointwise mass formula, unit covolume, and unit dual-lattice gap without any
computability or Turing-machine dependencies.

## Main definitions

* `ZLattice.intLatticeReal`: the standard integer lattice `ℤ ⊂ ℝ`.
* `ZLattice.intLatticeRealEquiv`: additive equivalence `ℤ ≃+ intLatticeReal`.
* `ZLattice.discreteGaussianInt`: canonical discrete Gaussian distribution on `ℤ`.

## Main results

* `ZLattice.mem_intLatticeReal_iff`: membership in `intLatticeReal` characterizes integer reals.
* `ZLattice.covolume_intLatticeReal`: `intLatticeReal` has unit Lebesgue covolume.
* `ZLattice.one_le_norm_of_mem_dualSubmodule_intLatticeReal`: every nonzero dual vector of
  `intLatticeReal` has norm at least `1`.
* `ZLattice.discreteGaussianInt_apply`: pointwise mass formula for `discreteGaussianInt`.
-/

public section

namespace ZLattice

open ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- The standard 1-D integer lattice `ℤ ⊂ ℝ`. -/
noncomputable abbrev intLatticeReal : Submodule ℤ ℝ :=
  Submodule.span ℤ (Set.range (Module.Basis.singleton Unit ℝ))

/-- Membership in `intLatticeReal` characterizes integer real numbers. -/
theorem mem_intLatticeReal_iff (x : ℝ) : x ∈ intLatticeReal ↔ ∃ n : ℤ, (n : ℝ) = x := by
  rw [intLatticeReal, Set.range_unique, Submodule.mem_span_singleton]
  simp

/-- Additive equivalence identifying `ℤ` with `intLatticeReal ⊂ ℝ`. -/
noncomputable def intLatticeRealEquiv : ℤ ≃+ intLatticeReal where
  toFun n := ⟨(n : ℝ), (mem_intLatticeReal_iff _).mpr ⟨n, rfl⟩⟩
  invFun z := Int.floor (z : ℝ)
  left_inv n := Int.floor_intCast n
  right_inv z := by
    obtain ⟨n, hn⟩ := (mem_intLatticeReal_iff (z : ℝ)).mp z.property
    ext
    dsimp only
    rw [← hn, Int.floor_intCast]
  map_add' m n := by ext; push_cast; rfl

/-- Real coercion of `intLatticeRealEquiv n` is `(n : ℝ)`. -/
@[simp]
theorem coe_intLatticeRealEquiv (n : ℤ) : ((intLatticeRealEquiv n : intLatticeReal) : ℝ) = n := by
  rfl

/-- Real coercion of `intLatticeRealEquiv.symm z` equals `(z : ℝ)`. -/
@[simp]
theorem coe_intLatticeRealEquiv_symm (z : intLatticeReal) :
    ((intLatticeRealEquiv.symm z : ℤ) : ℝ) = (z : ℝ) := by
  rw [← coe_intLatticeRealEquiv, intLatticeRealEquiv.apply_symm_apply]

/-- The standard integer lattice `ℤ ⊂ ℝ` has Lebesgue covolume `1`. -/
theorem covolume_intLatticeReal :
    ZLattice.covolume intLatticeReal (MeasureTheory.volume : MeasureTheory.Measure ℝ) = 1 := by
  have hF := ZSpan.isAddFundamentalDomain (Module.Basis.singleton Unit ℝ)
    (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain intLatticeReal MeasureTheory.volume hF]
  have hdom : ZSpan.fundamentalDomain (Module.Basis.singleton Unit ℝ) = Set.Ico (0 : ℝ) 1 := by
    ext x
    simp [ZSpan.fundamentalDomain]
  rw [hdom, MeasureTheory.measureReal_def, Real.volume_Ico]
  simp

/-- Every nonzero vector in the dual lattice of `intLatticeReal = ℤ ⊂ ℝ` has norm at least `1`. -/
theorem one_le_norm_of_mem_dualSubmodule_intLatticeReal
    {y : LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal} (hy : y ≠ 0) :
    (1 : ℝ) ≤ ‖(y : ℝ)‖ := by
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp
    (y.property 1 ((mem_intLatticeReal_iff 1).mpr ⟨1, by simp⟩))
  have hk' : (k : ℝ) = (y : ℝ) := by simpa [real_inner_comm] using hk
  have hkn : k ≠ 0 := fun h => hy (Subtype.ext (by simpa [h] using hk'.symm))
  rw [Real.norm_eq_abs, ← hk']
  exact_mod_cast Int.one_le_abs hkn

/-- Canonical discrete Gaussian on `ℤ` induced by `ZLattice.discreteGaussian` on `ℤ ⊂ ℝ`. -/
noncomputable def discreteGaussianInt (s : ℝ) (hs : 0 < s) (c : ℝ) : PMF ℤ :=
  (ZLattice.discreteGaussian intLatticeReal s hs c).map intLatticeRealEquiv.symm

/-- Pushforward characterization of `discreteGaussianInt`. -/
theorem discreteGaussianInt_eq_map (s : ℝ) (hs : 0 < s) (c : ℝ) :
    discreteGaussianInt s hs c =
      (ZLattice.discreteGaussian intLatticeReal s hs c).map intLatticeRealEquiv.symm := by
  rfl

/-- Pointwise evaluation formula for `discreteGaussianInt`. -/
theorem discreteGaussianInt_apply (s : ℝ) (hs : 0 < s) (c : ℝ) (x : ℤ) :
    discreteGaussianInt s hs c x =
      ENNReal.ofReal (gaussianWeight s ((x : ℝ) - c)) /
        ENNReal.ofReal (ZLattice.gaussianMass intLatticeReal s c) := by
  classical
  unfold discreteGaussianInt
  rw [PMF.map_apply, tsum_eq_single (intLatticeRealEquiv x)]
  · simp only [AddEquiv.symm_apply_apply, ↓reduceIte, ZLattice.discreteGaussian_apply]
    rfl
  · intro z hz
    exact ite_eq_right fun heq => hz (by simpa using (congrArg intLatticeRealEquiv heq).symm)

end ZLattice
