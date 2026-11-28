/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyEstimatedMean
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.MeanBias

/-!
# First deterministic mean error after the completed raw walk

Stationarity of the full-terminal raw walk and first-prefix telescoping preserve the
absolute input mean error, divided by `rate k + G x y`. This gives the first clipped
mean envelope without converting a clipped relative bound back to an absolute bound.
The target is explicitly nonnegative. Second-signal preparation still requires the
full-rank maximum in `preparationError`; no recursive relative budget is proved here.
The first-prefix pattern is adapted from Samuel Schlesinger's compression API.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual first discrepancy of a completed raw walk: stationarity removes the walk,
while rate normalization is retained exactly. Empty conditioning slices are allowed. -/
theorem actualClippedMean_first_eq {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (x y : ZMod P) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    actualClippedMean HP s t Ls La Lt D ss st k G ζ
      (firstSignalIncrement F k second) (fun _ _ _ _ => 0) 0 i x y =
      min 1 (|rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
        (input (i + 1)) x y - G x y| / (rate k + G x y)) := by
  dsimp only
  unfold actualClippedMean twoMaskMean
  simp only [Fin.isValue, ↓reduceIte, actualPrefix_firstSignalIncrement _ _ _ (fun _ _ _ _ => 0)
    (by intros; rfl)]
  unfold rowSliceMean
  rw [← expect_div]
  change min 1 (|rowSliceMean _ _ (conditionalWalk _ _ _ _ _) x y / rate k -
    G x y / rate k| / (1 + G x y / rate k)) = _
  rw [rowSliceMean_conditionalWalk, ← sub_div, abs_div, abs_of_pos (rate_pos k), div_div]
  congr 2
  field_simp

/-- A matrix-unit absolute input mean bound gives the genuine first clipped mean
bound after any completed raw walk. This direction needs no upper bound on G. -/
theorem actualClippedMean_first_le {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (x y : ZMod P) (hG : 0 ≤ G x y) {error : ℝ}
    (he : |rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
      (input (i + 1)) x y - G x y| ≤ error) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    actualClippedMean HP s t Ls La Lt D ss st k G ζ
      (firstSignalIncrement F k second) (fun _ _ _ _ => 0) 0 i x y ≤
      min 1 (error / (rate k + G x y)) := by
  dsimp only
  rw [actualClippedMean_first_eq]
  exact min_le_min_left _ (div_le_div_of_nonneg_right he (by positivity))

/-- First deterministic envelope of the actual finite estimated residual, after its
completed full-terminal raw walk. Structural requests stay fixed across walk precisions.
Preparation is applied later; no full-rank maximum has been replaced by a usage maximum. -/
theorem actualEstimatedResidual_first_mean_le
    {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (steps : ℕ → ℕ) (ζ : ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ) (j : ℕ) (x y : ZMod P) :
    actualClippedMean HP s.roles.source s.roles.terminal (side P s.sourceExponent)
      (side P s.terminalExponent) (side P s.terminalExponent) s.direction s.sourceSuffix
      s.terminalSuffix s.terminalExponent s.residual ζ
      (firstSignalIncrement (s.walkSteps children steps) s.terminalExponent second)
      (fun _ _ _ _ => 0) 0 j x y ≤
      min 1 (s.cost children j x y / (rate s.terminalExponent + s.residual x y)) :=
  actualClippedMean_first_le HP s.roles.source s.roles.terminal (side P s.sourceExponent)
    (side P s.terminalExponent) (side P s.terminalExponent) s.direction s.sourceSuffix
    s.terminalSuffix (fun _ => s.walkGraphAt s.terminalExponent)
    (fun k _ _ => steps k) (s.input children) s.terminalExponent ζ s.residual second
    j x y (s.residual_nonneg x y) (s.mean_sub_le children j x y)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
