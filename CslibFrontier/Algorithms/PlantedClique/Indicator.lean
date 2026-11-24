/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.TopSelection
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Indicator vectors and the rank-one clique signal

The indicator of a nonempty finite set has norm equal to the square root of its cardinality.
Its outer-product matrix is therefore its cardinality times the orthogonal projection onto the
normalized indicator. This file connects that matrix description to coordinate rounding.

The final lemma removes the sign ambiguity in a spectral approximation and proves the overlap
condition required by the deterministic degree cleanup step.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero-one indicator vector of a vertex set, with the Euclidean norm. -/
@[expose] def indicator (S : Finset ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => if i ∈ S then 1 else 0

/-- The indicator divided by the square root of the set cardinality. -/
noncomputable def unitIndicator (S : Finset ι) : EuclideanSpace ℝ ι :=
  (1 / Real.sqrt S.card) • indicator S

/-- The clique signal before subtracting the diagonal: the indicator outer product. -/
@[expose] def cliqueSignal (S : Finset ι) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (indicator S) (indicator S)

/-- The norm of a zero-one indicator is the square root of its support size. -/
theorem norm_indicator (S : Finset ι) : ‖indicator S‖ = Real.sqrt S.card := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [indicator, ite_pow]

omit [Fintype ι] in
/-- Coordinates of the normalized indicator. -/
theorem unitIndicator_apply (S : Finset ι) (i : ι) :
    unitIndicator S i = if i ∈ S then 1 / Real.sqrt S.card else 0 := by
  simp [unitIndicator, indicator, mul_ite]

omit [Fintype ι] in
/-- Every coordinate of the normalized indicator is nonnegative. -/
theorem unitIndicator_nonneg (S : Finset ι) (i : ι) : 0 ≤ unitIndicator S i := by
  rw [unitIndicator_apply]
  split_ifs <;> positivity

omit [Fintype ι] [DecidableEq ι] in
/-- The normalization height has squared reciprocal equal to the cardinality. -/
theorem card_mul_unitIndicator_height_sq {S : Finset ι} (hS : S.Nonempty) :
    (S.card : ℝ) * (1 / Real.sqrt S.card) ^ 2 = 1 := by
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
  rw [one_div, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_inv_cancel₀ hc]

/-- A nonempty set has a unit normalized indicator. -/
theorem norm_unitIndicator {S : Finset ι} (hS : S.Nonempty) : ‖unitIndicator S‖ = 1 := by
  have hsqrt : 0 < Real.sqrt (S.card : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hS.card_pos)
  rw [unitIndicator, norm_smul_of_nonneg (by positivity), norm_indicator, one_div,
    inv_mul_cancel₀ hsqrt.ne']

omit [Fintype ι] in
/-- Recover the original indicator from its normalized direction. -/
theorem indicator_eq_sqrt_smul_unitIndicator {S : Finset ι} (hS : S.Nonempty) :
    indicator S = Real.sqrt S.card • unitIndicator S := by
  have hsqrt : Real.sqrt (S.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hS.card_pos)).ne'
  simp [unitIndicator, smul_smul, hsqrt]

private theorem cliqueSignal_apply_indicator (S : Finset ι) (y : EuclideanSpace ℝ ι) :
    (cliqueSignal S).toEuclideanLin y = inner ℝ (indicator S) y • indicator S := by
  ext i
  change (∑ j, indicator S i * indicator S j * y j) =
    (∑ j, y j * indicator S j) * indicator S i
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The clique signal acts as cardinality times projection onto its unit indicator. -/
theorem cliqueSignal_apply {S : Finset ι} (hS : S.Nonempty) (y : EuclideanSpace ℝ ι) :
    (cliqueSignal S).toEuclideanLin y =
      ((S.card : ℝ) * inner ℝ (unitIndicator S) y) • unitIndicator S := by
  rw [cliqueSignal_apply_indicator]
  simp only [indicator_eq_sqrt_smul_unitIndicator hS, real_inner_smul_left, smul_smul]
  congr 1
  calc
    Real.sqrt S.card * inner ℝ (unitIndicator S) y * Real.sqrt S.card =
        (Real.sqrt S.card) ^ 2 * inner ℝ (unitIndicator S) y := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The normalized indicator is an eigenvector of the clique signal with eigenvalue `#S`. -/
theorem cliqueSignal_unitIndicator {S : Finset ι} (hS : S.Nonempty) :
    (cliqueSignal S).toEuclideanLin (unitIndicator S) = (S.card : ℝ) • unitIndicator S := by
  rw [cliqueSignal_apply hS, real_inner_self_eq_norm_sq, norm_unitIndicator hS]
  simp

/-- Rounding the largest absolute coordinates removes the sign ambiguity of a spectral
approximation and loses at most a sixteenth of the target set when squared error is `1 / 32`. -/
theorem sixteen_mul_card_sdiff_le_of_signed_norm_sub_sq_le {S T : Finset ι}
    (hS : S.Nonempty) (hcard : S.card = T.card) {x : EuclideanSpace ℝ ι} {s : ℝ}
    (hs : s = 1 ∨ s = -1) (horder : ∀ i ∉ T, ∀ j ∈ T, |x i| ≤ |x j|)
    (herror : ‖x - s • unitIndicator S‖ ^ 2 ≤ 1 / 32) :
    16 * (S \ T).card ≤ S.card := by
  have hsabs (i : ι) : |s * unitIndicator S i| = unitIndicator S i := by
    rcases hs with rfl | rfl <;> simp [abs_of_nonneg (unitIndicator_nonneg S i)]
  have henergy : (∑ i, (|x i| - if i ∈ S then 1 / Real.sqrt S.card else 0) ^ 2) ≤
      ∑ i, (x i - s * unitIndicator S i) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hcontract := sq_le_sq.mpr
      (abs_abs_sub_abs_le_abs_sub (x i) (s * unitIndicator S i))
    rw [hsabs i] at hcontract
    simpa only [unitIndicator_apply] using hcontract
  rw [EuclideanSpace.real_norm_sq_eq] at herror
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at herror
  exact Finset.sixteen_mul_card_sdiff_le_of_sum_sq_le S T (fun i => |x i|)
    (by positivity) (card_mul_unitIndicator_height_sq hS) hcard horder (henergy.trans herror)

end Cslib.Algorithms.PlantedClique
