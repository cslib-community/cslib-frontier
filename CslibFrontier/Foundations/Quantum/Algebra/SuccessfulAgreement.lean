/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
public import Mathlib.Data.Fintype.Option
import Mathlib.Analysis.Real.Sqrt

/-!
# Agreement on successful measurement outcomes

One side may return a field value or a failure outcome. The comparison charges disagreements
on successful outcomes. Replacing a measurement on the other side changes the disagreement
by at most the square root of the summed squared state distances.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped Real

variable {A α : Type*} [Fintype α] [Ring A] [PartialOrder A] [Algebra ℂ A]

/-- The state pairing of successful effects with the opposing disagreement effects.
For commuting measurements this is the probability of differing answers with a
successful first outcome. -/
@[expose] noncomputable def successfulMismatch (φ : AlgState A) (P : Measurement (Option α) A)
    (Q : Measurement α A) : ℝ :=
  ∑ a, (φ (P.effect (some a) * (1 - Q.effect a))).re

/-- For postprocessed measurements, the mismatch is the sum of the original joint weights
whose decoded outcomes disagree and whose first outcome decodes successfully. -/
theorem successfulMismatch_map_map {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq α] [IsOrderedAddMonoid A] (φ : AlgState A) (P : Measurement β A)
    (Q : Measurement γ A) (f : β → Option α) (g : γ → α) :
    successfulMismatch φ (P.map f) (Q.map g) =
      ∑ b, ∑ c, if ∃ a, f b = some a ∧ a ≠ g c then (φ (P.effect b * Q.effect c)).re else 0 := by
  classical
  have hComplement (a : α) : 1 - (Q.map g).effect a = ∑ c with g c ≠ a, Q.effect c := by
    rw [Measurement.map_effect, sub_eq_iff_eq_add]
    rw [sum_filter_not_add_sum_filter, Q.sum_effect]
  calc
    _ = ∑ a, ∑ b, ∑ c, if f b = some a then
        if g c ≠ a then (φ (P.effect b * Q.effect c)).re else 0 else 0 := by
      simp only [successfulMismatch, hComplement]
      simp only [Measurement.map_effect, sum_mul, mul_sum, map_sum, Complex.re_sum, sum_filter]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
      split_ifs <;> simp_all
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      cases h : f b with
      | none => simp
      | some a =>
        simp [ne_comm, sum_ite_eq]

/-- The successful mismatch averages over a classical choice of the first measurement. -/
theorem successfulMismatch_mixture_left {ι : Type*} [Fintype ι] [IsOrderedAddMonoid A]
    [PosSMulMono ℝ A] (φ : AlgState A) (p : PMF ι) (M : ι → Measurement (Option α) A)
    (Q : Measurement α A) :
    successfulMismatch φ (mixture p M) Q = ∑ i, (p i).toReal * successfulMismatch φ (M i) Q := by
  have h (r : ℝ) (a b : A) : (φ ((r • a) * b)).re = r * (φ (a * b)).re := by
    rw [← IsScalarTower.algebraMap_smul ℂ r a, smul_mul_assoc, map_smul, Complex.coe_algebraMap,
      smul_eq_mul, Complex.re_ofReal_mul]
  simp only [successfulMismatch, mixture_effect, sum_mul, map_sum, Complex.re_sum, h,
    Finset.mul_sum]
  exact sum_comm

omit [Algebra ℂ A] in
/-- Completing an optional measurement with a fallback adds the failure effect to
the fallback outcome's successful effect. -/
theorem map_getD_effect [DecidableEq α] [IsOrderedAddMonoid A]
    (P : Measurement (Option α) A) (fallback a : α) :
    (P.map (fun x => x.getD fallback)).effect a =
      (if fallback = a then P.effect none else 0) + P.effect (some a) := by
  simp only [map_effect, sum_filter, Fintype.sum_option, Option.getD_none, Option.getD_some,
    sum_ite_eq', mem_univ, ite_true]

/-- Replacing failure with a fixed outcome adds at most the original failure mass to
the disagreement probability. -/
theorem one_sub_agreement_map_getD_le [DecidableEq α] [IsOrderedAddMonoid A]
    [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
    (φ : AlgState A) (P : Measurement (Option α) A) (Q : Measurement α A) (fallback : α)
    (hc : Commute (P.effect none) (Q.effect fallback)) :
    1 - agreement φ (P.map (fun a => a.getD fallback)) Q ≤
      successfulMismatch φ P Q + (φ (P.effect none)).re := by
  classical
  have hsum : (φ (P.effect none)).re + ∑ a, (φ (P.effect (some a))).re = 1 := by
    simpa only [Fintype.sum_option, Measurement.prob] using P.sum_prob φ
  have hpos := φ.re_apply_nonneg (Commute.mul_nonneg (P.nonneg none) (Q.nonneg fallback) hc)
  unfold agreement successfulMismatch
  simp only [map_getD_effect, add_mul, mul_sub, mul_one, map_add, map_sub, Complex.add_re,
    Complex.sub_re, sum_add_distrib, sum_sub_distrib, ite_mul, zero_mul, apply_ite, map_zero,
    Complex.zero_re, sum_ite_eq, mem_univ, ite_true]
  linarith

variable [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- Replacing the second measurement increases disagreement on successful outcomes by at most
its state distance from the original measurement. -/
theorem successfulMismatch_le (φ : AlgState A) (P : Measurement (Option α) A)
    (Q R : Measurement α A) :
    successfulMismatch φ P R ≤ successfulMismatch φ P Q +
      √(∑ a, φ.norm (Q.effect a - R.effect a) ^ 2) := by
  have hP : ∑ a, φ.norm (P.effect (some a)) ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ a, (φ (P.effect (some a))).re := sum_le_sum fun a _ => by
        rw [AlgState.norm_sq, (P.nonneg (some a)).isSelfAdjoint.star_eq]
        exact φ.re_apply_mono (P.effect_mul_self_le (some a))
      _ ≤ ∑ a : Option α, (φ (P.effect a)).re := by
        rw [Fintype.sum_option]
        exact le_add_of_nonneg_left (φ.re_apply_nonneg (P.nonneg none))
      _ = 1 := P.sum_prob φ
  apply sub_le_iff_le_add'.mp
  unfold successfulMismatch
  rw [← sum_sub_distrib]
  calc
    _ = ∑ a, (φ (star (P.effect (some a)) * (Q.effect a - R.effect a))).re := by
      refine sum_congr rfl fun a _ => ?_
      rw [(P.nonneg (some a)).isSelfAdjoint.star_eq, ← Complex.sub_re, ← map_sub]
      congr 1
      noncomm_ring
    _ ≤ ∑ a, φ.norm (P.effect (some a)) * φ.norm (Q.effect a - R.effect a) :=
      sum_le_sum fun a _ => φ.re_apply_star_mul_le _ _
    _ ≤ √(∑ a, φ.norm (P.effect (some a)) ^ 2) *
        √(∑ a, φ.norm (Q.effect a - R.effect a) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := by
      simpa only [Real.sqrt_one, one_mul] using mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hP) (Real.sqrt_nonneg _)

end Cslib.Quantum.Measurement
