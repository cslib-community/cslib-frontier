/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.RandomMatrix.Independent
import Mathlib.Data.NNRat.BigOperators

/-!
# The spectral norm of planted-clique noise

The centered symmetric noise is an instance of the independent centered bounded-entry matrix
model. The shared spectral-norm tail theorem gives `36 √n` except on a set of uniform seeds
of density at most `2 exp (-n)`.

## Main results

* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le`: the spectral-norm tail bound.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

/-- The centered symmetric planted-clique noise has norm at most `36 √n`, with failure
density at most `2 exp (-n)` under independent uniform edge coins. -/
theorem dens_noise_opNorm_gt_le {n : ℕ} (S : Finset (Fin n)) :
    (dens ({ω : Coins n | 36 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (-(n : ℝ)) := by
  classical
  let score (ij : Fin n × Fin n) (b : Bool) : ℝ :=
    if ij.1 ∈ S ∧ ij.2 ∈ S then 0 else -BitString.signVal b
  have hmean (ij : Fin n × Fin n) :
      ∑ b, (PMF.uniformOfFintype Bool b).toReal * score ij b = 0 := by
    simp only [Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool, score]
    split_ifs <;> norm_num
  have hosc (ij : Fin n × Fin n) (a b : Bool) : |score ij a - score ij b| ≤ 2 := by
    dsimp only [score]
    split_ifs <;> cases a <;> cases b <;> norm_num
  have hmatrix (ω : Coins n) (i j : Fin n) : noise S ω i j =
      (if i < j then score (i, j) (ω (i, j)) else 0) +
      (if j < i then score (j, i) (ω (j, i)) else 0) := by
    simp only [noise, upperNoise, Matrix.add_apply, Matrix.transpose_apply, score]
    split_ifs <;> simp_all
  have h := PMF.pi_opNorm_symmetric_gt_le (fun _ => PMF.uniformOfFintype Bool)
    score hmean hosc (noise S) hmatrix
  rw [PMF.pi_uniformOfFintype, PMF.toOuterMeasure_uniformOfFintype_toReal] at h
  simpa only [dens, NNRat.cast_div, NNRat.cast_natCast, Set.mem_ofPred_eq] using h

end Cslib.Probability.PlantedClique
