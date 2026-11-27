/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PlantedClique.Degree
public import CslibFrontier.Probability.PlantedClique.RandomMatrix
public import Mathlib.Data.Finset.Density
import Mathlib.Data.NNRat.BigOperators

/-!
# Recovery from the planted-clique noise and degree bounds

A recovery map that returns the fixed planted set whenever the noise norm is at most `36 √n`
and all outside degrees into that set are at most five eighths of its size has failure density
at most `2 exp (-n) + n exp (-|S| / 32)`. The common probability argument combines the two
exceptional events; each algorithm supplies its deterministic correctness under their complements.

## Main results

* `dens_recover_ne_le_of_noise_degree`: the conditional bound for any seed-indexed recovery map.
-/

public section

namespace Cslib.Probability.PlantedClique

open Finset Real

/-- Conditional recovery bound from the spectral-norm and outside-degree events. The map
`recover` is indexed by edge seeds; callers supply its correctness on the two good events. -/
theorem dens_recover_ne_le_of_noise_degree {n : ℕ} (S : Finset (Fin n)) (hS : 0 < S.card)
    (recover : Coins n → Finset (Fin n))
    (hrecover : ∀ ω,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤ 36 * sqrt n →
      (∀ v ∉ S, 8 * (S.filter ((sample S ω).Adj v)).card ≤ 5 * S.card) →
      recover ω = S) :
    (dens ({ω : Coins n | recover ω ≠ S} : Finset _) : ℝ) ≤
      2 * exp (-(n : ℝ)) + n * exp (-(S.card : ℝ) / 32) := by
  classical
  let N : Finset (Coins n) := {ω | 36 * sqrt n <
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖}
  let D : Finset (Coins n) := {ω | ∃ v, v ∉ S ∧
    5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card}
  have hsub : ({ω : Coins n | recover ω ≠ S} : Finset _) ⊆ N ∪ D := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    simp only [N, D, mem_filter, mem_univ, true_and, not_lt, not_exists, not_and] at hω hnot
    exact hω (hrecover ω hnot.1 fun v hv => hnot.2 v hv)
  calc
    _ ≤ (dens (N ∪ D) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ (dens N : ℝ) + (dens D : ℝ) := by exact_mod_cast dens_union_le N D
    _ ≤ _ := add_le_add (dens_noise_opNorm_gt_le S) (dens_exists_outside_degree_gt_le S hS)

end Cslib.Probability.PlantedClique
