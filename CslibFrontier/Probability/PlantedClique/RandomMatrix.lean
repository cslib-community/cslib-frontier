/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.RandomMatrix.Independent
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The spectral norm of planted-clique noise

The centered symmetric noise is an instance of the independent centered bounded-entry matrix
model, with score oscillation two. The shared quadratic-net theorem gives `5 √n` except on a
set of uniform seeds of density at most `2 exp (-n)`. A parameterized version retains the
tradeoff between the norm constant and its exponential failure probability.

These bounds use an elementary net argument, rather than the sharper asymptotic random-matrix
estimate used in the planted-clique paper.

## Main results

* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le_mul`: the parameterized spectral tail.
* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le`: the bound at `5 √n`.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

/-- The elementary quadratic-net tail at any nonnegative multiple of `√n`.
For example, the signed-noise constant `9 / 2` gives failure at most `2 exp (-385 n / 1024)`.
The adjacency matrix's centered noise is half of this signed matrix. -/
theorem dens_noise_opNorm_gt_le_mul {n : ℕ} (S : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c) :
    (dens ({ω : Coins n | c * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (((7 : ℝ) / 2 - 49 * c ^ 2 / 256) * n) := by
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
    score hmean (by norm_num : (0 : ℝ) < 2) hosc (noise S) hmatrix hc
  rw [PMF.pi_uniformOfFintype, PMF.toOuterMeasure_uniformOfFintype_toReal] at h
  norm_num only [show (64 : ℝ) * 2 ^ 2 = 256 by norm_num] at h
  simpa only [dens, NNRat.cast_div, NNRat.cast_natCast, Set.mem_ofPred_eq] using h

/-- The centered symmetric planted-clique noise has norm at most `5 √n`, with failure
density at most `2 exp (-n)` under independent uniform edge coins. -/
theorem dens_noise_opNorm_gt_le {n : ℕ} (S : Finset (Fin n)) :
    (dens ({ω : Coins n | 5 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (-(n : ℝ)) := by
  apply (dens_noise_opNorm_gt_le_mul S (c := 5) (by norm_num)).trans
  gcongr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Cslib.Probability.PlantedClique
