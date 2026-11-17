/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import CslibFrontier.Foundations.Quantum.POVM
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Measurements in a star-ordered algebra

A *measurement* with outcomes `α` in an ordered algebra `A` (`Cslib.Quantum.Measurement`) is a
family of nonnegative effects `E_a ∈ A` summing to `1`: a positive-operator-valued measurement
whose effects are observables of `A` rather than matrices. In a state `φ` it gives outcome `a`
with probability `Re φ(E_a)` (`Cslib.Quantum.Measurement.prob`), and the outcome distribution is
the probability mass function `Cslib.Quantum.Measurement.distribution`. On the matrix algebra with
a vector state this is the Born rule of `Cslib.Quantum.POVM`
(`Cslib.Quantum.POVM.prob_toMeasurement`).

A measurement can be *post-processed* by a map of outcomes, `b ↦ ∑_{f a = b} E_a`
(`Cslib.Quantum.Measurement.map`), which pushes the outcome distribution forward
(`Cslib.Quantum.Measurement.distribution_map`). It is *projective* when its effects are
idempotent (`Cslib.Quantum.Measurement.IsProjective`). A two-outcome measurement has the
observable `E_false - E_true` (`Cslib.Quantum.Measurement.observable`), a self-adjoint contraction
in any algebra with a continuous functional calculus
(`Cslib.Quantum.Measurement.star_observable_mul_self_le_one`), and an involution when the
measurement is projective (`Cslib.Quantum.Measurement.observable_mul_self`).

## Main definitions

* `Cslib.Quantum.Measurement`: a measurement with outcomes `α` in `A`.
* `Cslib.Quantum.Measurement.prob`, `Cslib.Quantum.Measurement.distribution`: the outcome
  probabilities and distribution in a state.
* `Cslib.Quantum.Measurement.map`: post-processing of outcomes.
* `Cslib.Quantum.Measurement.const`: the measurement with a fixed outcome.
* `Cslib.Quantum.Measurement.IsProjective`: projective measurements.
* `Cslib.Quantum.Measurement.observable`: the `±1` observable of a two-outcome measurement.
* `Cslib.Quantum.POVM.toMeasurement`: a POVM as a measurement in the matrix algebra.

## Main results

* `Cslib.Quantum.Measurement.sum_prob`: the outcome probabilities sum to `1`.
* `Cslib.Quantum.Measurement.distribution_map`: post-processing pushes the distribution forward.
* `Cslib.Quantum.Measurement.star_observable_mul_self_le_one`: the observable is a contraction.
* `Cslib.Quantum.Measurement.observable_map`: the observable of a post-processed measurement.
-/

@[expose] public section

namespace Cslib.Quantum

open Finset
open scoped ComplexOrder

/-- A **measurement** with outcomes `α` in the ordered algebra `A`: nonnegative effects summing to
the identity. -/
structure Measurement (α A : Type*) [Fintype α] [Ring A] [PartialOrder A] where
  /-- The effect `E_a` of the outcome `a`. -/
  effect : α → A
  /-- Every effect is nonnegative. -/
  nonneg : ∀ a, 0 ≤ effect a
  /-- The effects sum to the identity. -/
  sum_effect : ∑ a, effect a = 1

namespace Measurement

variable {α β A : Type*} [Fintype α] [Fintype β]

section Ring

variable [Ring A] [PartialOrder A]

@[ext]
theorem ext {M N : Measurement α A} (h : ∀ a, M.effect a = N.effect a) : M = N := by
  cases M; cases N; congr; funext a; exact h a

variable [IsOrderedAddMonoid A]

/-- Every effect is at most the identity. -/
theorem effect_le_one (M : Measurement α A) (a : α) : M.effect a ≤ 1 := by
  rw [← M.sum_effect]
  exact single_le_sum (fun b _ => M.nonneg b) (mem_univ a)

/-- Post-processing of the outcomes by `f`: the effect of `b` is `∑_{f a = b} E_a`. -/
def map [DecidableEq β] (f : α → β) (M : Measurement α A) : Measurement β A where
  effect b := ∑ a with f a = b, M.effect a
  nonneg b := sum_nonneg fun a _ => M.nonneg a
  sum_effect := by rw [sum_fiberwise, M.sum_effect]

theorem map_effect [DecidableEq β] (f : α → β) (M : Measurement α A) (b : β) :
    (M.map f).effect b = ∑ a with f a = b, M.effect a :=
  rfl

/-- A measurement is **projective** when its effects are idempotent. -/
def IsProjective (M : Measurement α A) : Prop :=
  ∀ a, M.effect a * M.effect a = M.effect a

end Ring

section AlgState

variable [Ring A] [PartialOrder A] [Algebra ℂ A]

/-- The probability `Re φ(E_a)` of the outcome `a` in the state `φ`. -/
noncomputable def prob (φ : AlgState A) (M : Measurement α A) (a : α) : ℝ :=
  (φ (M.effect a)).re

theorem prob_nonneg (φ : AlgState A) (M : Measurement α A) (a : α) : 0 ≤ M.prob φ a :=
  φ.re_apply_nonneg (M.nonneg a)

theorem ofReal_prob (φ : AlgState A) (M : Measurement α A) (a : α) :
    (M.prob φ a : ℂ) = φ (M.effect a) :=
  φ.ofReal_re_apply (M.nonneg a)

/-- The outcome probabilities sum to `1`. -/
@[simp]
theorem sum_prob (φ : AlgState A) (M : Measurement α A) : ∑ a, M.prob φ a = 1 := by
  simp only [prob, ← Complex.re_sum, ← map_sum, M.sum_effect, AlgState.map_one, Complex.one_re]

/-- The outcome distribution of `M` in the state `φ`. -/
noncomputable def distribution (φ : AlgState A) (M : Measurement α A) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (M.prob φ a)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => M.prob_nonneg φ a, sum_prob,
      ENNReal.ofReal_one]

@[simp]
theorem distribution_apply (φ : AlgState A) (M : Measurement α A) (a : α) :
    M.distribution φ a = ENNReal.ofReal (M.prob φ a) := by
  rw [distribution, PMF.ofFintype_apply]

variable [IsOrderedAddMonoid A]

theorem prob_map [DecidableEq β] (φ : AlgState A) (f : α → β) (M : Measurement α A) (b : β) :
    (M.map f).prob φ b = ∑ a with f a = b, M.prob φ a := by
  simp only [prob, map_effect, map_sum, Complex.re_sum]

/-- Post-processing pushes the outcome distribution forward. -/
theorem distribution_map [DecidableEq β] (φ : AlgState A) (f : α → β) (M : Measurement α A) :
    (M.map f).distribution φ = (M.distribution φ).map f := by
  ext b
  rw [distribution_apply, PMF.map_apply, tsum_fintype, prob_map,
    ENNReal.ofReal_sum_of_nonneg fun a _ => M.prob_nonneg φ a, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  rw [distribution_apply]
  by_cases h : f a = b
  · simp [h]
  · simp [h, Ne.symm h]

end AlgState

section Const

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

/-- The trivial measurement with the fixed outcome `a`. -/
def const [DecidableEq α] (a : α) : Measurement α A where
  effect a' := if a' = a then 1 else 0
  nonneg a' := by
    split_ifs
    · simp
    · exact le_rfl
  sum_effect := by simp

theorem isProjective_const [DecidableEq α] (a : α) : (const a : Measurement α A).IsProjective :=
  fun a' => by simp only [const]; split_ifs <;> simp

theorem prob_const [Algebra ℂ A] [DecidableEq α] (φ : AlgState A) (a a' : α) :
    (const a : Measurement α A).prob φ a' = if a' = a then 1 else 0 := by
  simp only [prob, const]; split_ifs <;> simp

end Const

section Observable

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

/-- The `±1` observable `E_false - E_true` of a two-outcome measurement. -/
def observable (M : Measurement Bool A) : A :=
  M.effect false - M.effect true

omit [StarRing A] [StarOrderedRing A] in
theorem observable_eq (M : Measurement Bool A) : M.observable = 2 * M.effect false - 1 := by
  rw [observable, ← M.sum_effect, Fintype.sum_bool]
  noncomm_ring

theorem isSelfAdjoint_observable (M : Measurement Bool A) : IsSelfAdjoint M.observable :=
  ((M.nonneg false).isSelfAdjoint).sub (M.nonneg true).isSelfAdjoint

omit [StarRing A] [StarOrderedRing A] in
/-- The observable of a projective two-outcome measurement is an involution. -/
theorem observable_mul_self {M : Measurement Bool A} (hM : M.IsProjective) :
    M.observable * M.observable = 1 := by
  rw [observable_eq]
  have h := hM false
  calc (2 * M.effect false - 1) * (2 * M.effect false - 1)
      = 4 * (M.effect false * M.effect false) - 4 * M.effect false + 1 := by noncomm_ring
    _ = 1 := by rw [h]; abel

variable [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- The observable of a two-outcome measurement is a contraction, `O⋆O ≤ 1`. -/
theorem star_observable_mul_self_le_one (M : Measurement Bool A) :
    star M.observable * M.observable ≤ 1 := by
  rw [M.isSelfAdjoint_observable.star_eq, observable_eq]
  set E := M.effect false
  have h0 : 0 ≤ E := M.nonneg false
  have h1 : 0 ≤ 1 - E := sub_nonneg.mpr (M.effect_le_one false)
  have hc : 0 ≤ E * (1 - E) := Commute.mul_nonneg h0 h1 ((Commute.one_right E).sub_right
    (Commute.refl E))
  have : (2 * E - 1) * (2 * E - 1) = 1 - 4 * (E * (1 - E)) := by noncomm_ring
  rw [this, sub_le_self_iff, show (4 : A) * (E * (1 - E)) =
    E * (1 - E) + E * (1 - E) + E * (1 - E) + E * (1 - E) by noncomm_ring]
  exact add_nonneg (add_nonneg (add_nonneg hc hc) hc) hc

end Observable

/-- The observable of a post-processed measurement: `∑_r (-1)^{g(r)} M_r`. -/
theorem observable_map {α A : Type*} [Fintype α] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℂ A] (M : Measurement α A) (g : α → Bool) :
    (M.map g).observable = ∑ r, (Cslib.BitString.signVal (g r) : ℂ) • M.effect r := by
  classical
  simp only [observable, map_effect, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  cases g r <;> simp [Cslib.BitString.signVal]

end Measurement

namespace POVM

open Matrix
open scoped MatrixOrder

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- A POVM as a measurement in the matrix algebra. -/
def toMeasurement (M : POVM α ι) : Measurement α (Matrix ι ι ℂ) where
  effect := M.effect
  nonneg a := Matrix.nonneg_iff_posSemidef.mpr (M.posSemidef a)
  sum_effect := M.sum_effect

@[simp]
theorem toMeasurement_effect (M : POVM α ι) (a : α) : M.toMeasurement.effect a = M.effect a :=
  rfl

/-- In a vector state, a POVM measures with the Born rule. -/
theorem prob_toMeasurement (M : POVM α ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (a : α) :
    M.toMeasurement.prob (AlgState.vector ψ hψ) a = M.prob ψ a :=
  rfl

theorem distribution_toMeasurement (M : POVM α ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    M.toMeasurement.distribution (AlgState.vector ψ hψ) = M.measure ψ hψ := by
  ext a
  rw [Measurement.distribution_apply, measure_apply, prob_toMeasurement]

end POVM

end Cslib.Quantum
