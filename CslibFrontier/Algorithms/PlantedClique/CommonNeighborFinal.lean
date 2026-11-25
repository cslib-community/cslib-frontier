/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.CommonNeighborProgram
public import CslibFrontier.Algorithms.PlantedClique.CommonNeighborRecovery
public import CslibFrontier.Probability.PlantedClique.Uniqueness
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic.Positivity

/-!
# The common-neighbor algorithm's finite probability bound

The executable wrapper enumerates every seed of a fixed size and returns the first verified
clique of the requested size. For a fixed planted seed, the exposure and concentration argument
controls reduced recovery. If the planted clique is unique, a successful planted seed forces
the wrapper to return it, even when other seeds are tried first. A union bound combines these
two proved random-graph estimates.

The last theorem averages the fixed-set bound over an arbitrary independent prior on hidden
sets. The solver receives only the graph and the public target size.

## References

* [N. Alon, M. Krivelevich, B. Sudakov, *Finding a large hidden clique in a random
  graph*][AlonKrivelevichSudakov1998], Section 2.3, Algorithm B. The reduced solver here is the
  certified integer matrix-power variant; the seed enumeration and common-neighbor restriction
  implement the paper's constant-reduction argument.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability Cslib.Probability.PlantedClique Cslib.Probability.PMF

/-- The executable common-neighbor wrapper recovers every fixed planted set with the stated
finite failure bound. Its premises are numerical size conditions; all exposure, independence,
concentration, reduced recovery, and uniqueness estimates are discharged in the proof. -/
theorem prob_commonNeighborRecover_ne_le {n : ℕ} (S : Finset (Fin n)) (s : ℕ)
    (hn : 1 ≤ n) (hk : 6 ≤ S.card - s)
    (hsize : 1024 * Real.sqrt ((S.card : ℝ) + 2 * n * (2 ^ s : ℝ)⁻¹) ≤
      (S.card - s : ℕ)) :
    ((uniformOfFintype (Coins n)).toOuterMeasure {ω |
      vertexSet n (commonNeighborRecover recoverInput s
        (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S}).toReal ≤
      (Real.exp (-2 * n * ((2 ^ s : ℝ)⁻¹) ^ 2) +
        (2 * Real.exp (-((S.card - s : ℕ) : ℝ)) +
          n * Real.exp (-((S.card - s : ℕ) : ℝ) / 32))) +
      (n * Real.exp (-(S.card : ℝ) / 32) +
        n.choose (S.card / 4) * ((2 : ℝ) ^ (S.card / 4).choose 2)⁻¹) := by
  classical
  obtain ⟨T, hT, hTs⟩ := Finset.exists_subset_card_eq (s := S) (by omega : s ≤ S.card)
  let failure : Set (Coins n) := {ω |
    vertexSet n (commonNeighborRecover recoverInput s
      (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S}
  let reducedFailure : Set (Coins n) := {ω |
    let U := (sample S ω).commonNeighborhood T
    let e := U.orderEmbOfFin rfl
    recover ((sample S ω).comap e) (S.card - T.card) ≠
      Finset.univ.filter fun i => e i ∈ S}
  let nonunique : Set (Coins n) := {ω |
    ∃ Q : Finset (Fin n), (sample S ω).IsClique (Q : Set (Fin n)) ∧
      Q.card = S.card ∧ Q ≠ S}
  have hsub : failure ⊆ reducedFailure ∪ nonunique := fun ω hω => by
    by_contra h
    obtain ⟨hr, hu⟩ : ω ∉ reducedFailure ∧ ω ∉ nonunique := by simpa using h
    have hclique : (sample S ω).IsClique (S : Set (Fin n)) :=
      fun _ hi _ hj hij => sample_adj_of_mem S ω hi hj hij
    have hunique (Q : Finset (Fin n)) (hQ : (sample S ω).IsClique (Q : Set (Fin n)))
        (hcard : Q.card = S.card) : Q = S :=
      Classical.byContradiction fun hne => hu ⟨Q, hQ, hcard, hne⟩
    have hrec : let U := (sample S ω).commonNeighborhood T
        let e := U.orderEmbOfFin rfl
        recover ((sample S ω).comap e) (S.card - T.card) =
          Finset.univ.filter fun i => e i ∈ S := by
      simpa only [reducedFailure, Set.mem_ofPred_eq, not_not] using hr
    refine hω ?_
    simpa only [hTs] using
      commonNeighborRecover_ofGraph_eq_of_recover (sample S ω) S T hT hclique hunique hrec
  have hprob : ((uniformOfFintype (Coins n)).toOuterMeasure failure).toReal ≤
      ((uniformOfFintype (Coins n)).toOuterMeasure reducedFailure).toReal +
        ((uniformOfFintype (Coins n)).toOuterMeasure nonunique).toReal := by
    apply ENNReal.toReal_le_add _ (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _)
    exact ((uniformOfFintype (Coins n)).toOuterMeasure.mono hsub).trans
      (MeasureTheory.measure_union_le (μ := (uniformOfFintype (Coins n)).toOuterMeasure) _ _)
  refine hprob.trans (add_le_add ?_ ?_)
  · simpa only [reducedFailure, hTs] using prob_recover_commonNeighborhood_ne_le S T hT hn
      (by simpa only [hTs] using hk) (by simpa only [hTs] using hsize)
  · exact prob_exists_clique_ne_le S (S.card / 4) (by omega) (by omega)

/-- The same executable common-neighbor algorithm attains the finite recovery bound under
any prior on hidden sets of the specified size, independent of the subsequent edge coins. -/
theorem searchProblem_commonNeighborRecover_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k}) (s : ℕ)
    (hn : 1 ≤ n) (hk : 6 ≤ k - s)
    (hsize : 1024 * Real.sqrt ((k : ℝ) + 2 * n * (2 ^ s : ℝ)⁻¹) ≤ (k - s : ℕ)) :
    ((searchProblem prior).experiment (fun G => PMF.pure
      (vertexSet n (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G k))))
        false).toReal ≤
      (Real.exp (-2 * n * ((2 ^ s : ℝ)⁻¹) ^ 2) +
        (2 * Real.exp (-((k - s : ℕ) : ℝ)) +
          n * Real.exp (-((k - s : ℕ) : ℝ) / 32))) +
      (n * Real.exp (-(k : ℝ) / 32) +
        n.choose (k / 4) * ((2 : ℝ) ^ (k / 4).choose 2)⁻¹) := by
  refine searchProblem_failure_le_of_fixedSet prior
    (fun G => vertexSet n (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G k)))
    (by positivity) ?_
  intro S hS
  simpa only [hS] using prob_commonNeighborRecover_ne_le S s hn
    (by simpa only [hS] using hk) (by simpa only [hS] using hsize)

end Cslib.Algorithms.PlantedClique
