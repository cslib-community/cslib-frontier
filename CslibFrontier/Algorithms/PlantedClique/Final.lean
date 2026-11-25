/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Correctness
public import CslibFrontier.Algorithms.PlantedClique.RandomGraph
public import CslibFrontier.Probability.PlantedClique.Problem
public import CslibFrontier.Probability.PlantedClique.Recovery
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Density
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recovery of a planted clique with high probability

For every fixed planted set `S` of size at least `1024 √n`, the integer matrix-power algorithm
recovers `S` except on a fraction at most `2 exp (-n) + n exp (-|S| / 32)` of the independent
fair edge seeds. The two exceptional events are a large noise operator norm and an excessive
degree into `S` from a vertex outside `S`.

Both the density statement and its uniform `PMF` interpretation concern the executable recovery
algorithm, including its integer growth search, largest-coordinate rounding, and degree cleanup.
The planted set is a parameter of the random experiment and the specification; the algorithm
receives only the sampled graph and the cardinality of the planted set.

The final statements use the generic `DistributionalSearchProblem.experiment` applied to
`searchProblem`. They allow any prior on hidden sets of the target size, including the usual
uniform prior `uniformPlantedSet`. The bound is obtained by averaging the fixed-set bound.
The experiment's solver takes only the graph as input; hidden-state access is confined to
sampling and semantic scoring. This probability argument is independent of the computational
model; `PolyTime` connects it to the uniform native machine certificate for the same recovery
function on explicit dense graph encodings.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Real
open Cslib.Probability.PlantedClique

variable {n : ℕ}

/-- The integer matrix-power algorithm recovers every fixed planted set of size at least
`1024 √n`, except on the stated fraction of uniform independent edge seeds. -/
theorem dens_recover_ne_le (S : Finset (Fin n)) (hn : 1 ≤ n) (hk : 6 ≤ S.card)
    (hsize : 1024 * Real.sqrt n ≤ (S.card : ℝ)) :
    (dens ({ω : Coins n | recover (sample S ω) S.card ≠ S} : Finset _) : ℝ) ≤
      2 * exp (-(n : ℝ)) + n * exp (-(S.card : ℝ) / 32) := by
  classical
  refine dens_recover_ne_le_of_noise_degree S (by omega)
    (fun ω => recover (sample S ω) S.card) ?_
  intro ω hnoise hdegree
  have hclique : (sample S ω).IsClique (S : Set (Fin n)) := by
    intro i hi j hj hij
    exact sample_adj_of_mem S ω hi hj hij
  exact recover_eq_of_opNorm_le (sample S ω) S hk hclique
    (opNorm_residual_le_card_div_sixteen S ω hn hsize hnoise) hdegree

/-- Probability-mass-function form of the fixed-planted-set recovery bound. The coins are
uniform on the finite product of independent Boolean edge choices. -/
theorem prob_recover_ne_le (S : Finset (Fin n)) (hn : 1 ≤ n) (hk : 6 ≤ S.card)
    (hsize : 1024 * Real.sqrt n ≤ (S.card : ℝ)) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | recover (sample S ω) S.card ≠ S}).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(S.card : ℝ) / 32) := by
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    dens_recover_ne_le S hn hk hsize

open scoped Classical in
/-- The graph-only recovery algorithm solves the distributional search problem with the stated
failure bound, for any prior on hidden `k`-sets independent of the subsequent edge coins.
Classical decidability in this semantic statement supplies the graph's adjacency test; the
sampled graph has the executable adjacency decision procedure used by `prob_recover_ne_le`. -/
theorem searchProblem_recover_failure_le {k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsize : 1024 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment (fun G => PMF.pure (recover G k)) false).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(k : ℝ) / 32) := by
  refine searchProblem_failure_le_of_fixedSet prior (fun G => recover G k) (by positivity) ?_
  intro S hS
  simpa only [hS, recover_eq_classical] using
    prob_recover_ne_le S hn (by simpa only [hS] using hk)
      (by simpa only [hS] using hsize)

open scoped Classical in
/-- Recovery succeeds with the same error bound in the uniform-hidden-set planted-clique
search problem. The returned answer is computed from the sampled graph and `k` alone. -/
theorem uniformSearchProblem_recover_failure_le {k : ℕ} (hkn : k ≤ n)
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsize : 1024 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem (uniformPlantedSet n k hkn)).experiment
      (fun G => PMF.pure (recover G k)) false).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(k : ℝ) / 32) :=
  searchProblem_recover_failure_le _ hn hk hsize

end Cslib.Algorithms.PlantedClique
