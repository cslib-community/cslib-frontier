/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Distributional.Distinguishing
public import CslibFrontier.Probability.Distributional.Search
public import CslibFrontier.Probability.PlantedClique.Model
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.EventBind

/-!
# Planted clique as a distributional problem

The joint law `instanceDistribution` samples a hidden set of size `k` from a supplied prior,
then plants it using independent fair edge coins. `searchProblem` reveals only the resulting
graph and accepts exactly the hidden set. The target size is a parameter of the problem and
may be known to an algorithm; the sampled hidden set is not part of its input.

This is exact recovery of the latent planted set. It differs from the relation-search problem
of finding any `k`-clique in the observed graph. The distinction is explicit in the success
relation, which is allowed to inspect the state even though the algorithm cannot.

`detectionProblem` compares the graph marginal of the same planted law with the null law
`G(n, 1/2)`. Both problems are semantic specifications: a computational model and its resource
or uniformity conditions are supplied separately to the generic game and solver predicates.
`uniformPlantedSet` gives the usual uniform prior, while arbitrary priors allow fixed hidden
sets and nonuniform planting laws without changing either specification.

`searchProblem_failure_le_of_fixedSet` transfers a uniform fixed-planted-set failure bound for
any graph-only deterministic solver to the search experiment under an arbitrary hidden-set prior.
-/

public section

namespace Cslib.Probability.PlantedClique

/-- A complete planted-clique state, including the hidden set used to generate the graph. -/
structure PlantedInstance (n : ℕ) where
  /-- The hidden vertex set planted as a clique. -/
  planted : Finset (Fin n)
  /-- The graph observed by a recovery algorithm or a test. -/
  graph : SimpleGraph (Fin n)

variable {n k : ℕ}

/-- Sample a hidden `k`-set according to `prior`, then independent edge coins for its graph. -/
@[expose] noncomputable def instanceDistribution
    (prior : PMF {S : Finset (Fin n) // S.card = k}) : PMF (PlantedInstance n) :=
  prior.bind fun S => (PMF.uniformOfFintype (Coins n)).map fun ω =>
    ⟨S.val, sample S.val ω⟩

/-- Exact planted-set recovery: the solver observes the graph and must return the hidden set. -/
@[expose] noncomputable def searchProblem
    (prior : PMF {S : Finset (Fin n) // S.card = k}) :
    DistributionalSearchProblem (PlantedInstance n) (SimpleGraph (Fin n)) (Finset (Fin n)) where
  distribution := instanceDistribution prior
  observe := PlantedInstance.graph
  accepts state answer := answer = state.planted

/-- A graph-only solver's uniform failure bound for every fixed planted set also bounds its
failure under any independent prior on planted sets of the specified size. -/
theorem searchProblem_failure_le_of_fixedSet
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (solve : SimpleGraph (Fin n) → Finset (Fin n)) {error : ℝ} (herror : 0 ≤ error)
    (hsolve : ∀ S : Finset (Fin n), S.card = k →
      ((PMF.uniformOfFintype (Coins n)).toOuterMeasure
        {ω : Coins n | solve (sample S ω) ≠ S}).toReal ≤ error) :
    ((searchProblem prior).experiment (fun G => PMF.pure (solve G)) false).toReal ≤ error := by
  rw [DistributionalSearchProblem.experiment_pure_false]
  have h := PMF.toOuterMeasure_bind_failure_toReal_le prior
    (fun S => (PMF.uniformOfFintype (Coins n)).map fun ω =>
      (⟨S.val, sample S.val ω⟩ : PlantedInstance n)) Set.univ
    {state : PlantedInstance n | solve state.graph ≠ state.planted} herror
    (fun S _ _ => by
      rw [PMF.toOuterMeasure_map_apply]
      exact hsolve S.val S.property)
  simpa only [Set.compl_univ, MeasureTheory.measure_empty, ENNReal.toReal_zero, zero_add,
    searchProblem, instanceDistribution] using h

/-- Distinguish an unplanted fair random graph from the graph law planted according to `prior`.
The hidden set is marginalized out before the distinguisher receives its observation. -/
@[expose] noncomputable def detectionProblem
    (prior : PMF {S : Finset (Fin n) // S.card = k}) :
    DistinguishingProblem (SimpleGraph (Fin n)) where
  nullDist := (PMF.uniformOfFintype (Coins n)).map (sample ∅)
  alternativeDist := (instanceDistribution prior).map PlantedInstance.graph

/-- The uniform prior on all `k`-subsets of the `n` vertices. -/
@[expose] noncomputable def uniformPlantedSet (n k : ℕ) (hkn : k ≤ n) :
    PMF {S : Finset (Fin n) // S.card = k} :=
  letI : Nonempty {S : Finset (Fin n) // S.card = k} := by
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (by simpa using hkn)
    exact ⟨⟨S, hS⟩⟩
  PMF.uniformOfFintype {S : Finset (Fin n) // S.card = k}

end Cslib.Probability.PlantedClique
