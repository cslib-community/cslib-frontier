/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveComparisons
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PartitionComparisons
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.Precompute
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveComparisons

/-!
# Every recursive local job uses the original decision-tree bank

The fallback in `cachedMSFOn` makes it total for arbitrary topologies. Along the actual
MSF recursion, every compacted local job fits both dimensions of the originally prepared
bank. Its program is obtained from the two indexed lookups and the endpoint catalogue.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

variable {V E W : Type} [LinearOrder V] [LinearOrder E] [LinearOrder W] {w : E → W}

private theorem roundInputs_support (g : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    ∀ j ∈ roundInputs g alg hw ends S, (support j.1 j.2).card ≤ (support ends S).card := by
  rw [roundInputs]
  split
  next h =>
    let r := round g alg ends S
    intro j hj
    rcases List.mem_cons.mp hj with rfl | later
    · exact le_rfl
    · have decrease := round_support_le g alg ends S
      have sub : (support r.ends r.remaining).card ≤ (support ends S).card := by
        change 4 * (support r.ends r.remaining).card ≤ _ at decrease
        omega
      exact (roundInputs_support g alg hw r.ends r.remaining j later).trans sub
  next => simp
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt g alg hw ends S (by assumption)

omit [LinearOrder V] in
private theorem localJobs_mem (ps : List (PartitionPart V E W)) (ends : E → Sym2 V)
    (S : Finset E) (job : (E → Sym2 V) × Finset E)
    (mem : job ∈ PrimPartition.localJobs w ends S ps) :
    ∃ p ∈ ps, ∃ active : Finset E,
      job.2 = compactParallel job.1 w (internalEdges job.1 active p.vertices) := by
  induction ps generalizing ends S with
  | nil => simp [PrimPartition.localJobs] at mem
  | cons p ps ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨p, List.mem_cons_self .., S, rfl⟩
    · obtain ⟨q, hit, active, eq⟩ := ih _ _ tail
      exact ⟨q, List.mem_cons_of_mem _ hit, active, eq⟩

/-- Both original bank indices are in range for every small comparison program actually
invoked in every graph of the recursive trace. -/
theorem forestRounds_lookup_bounds (w : E → W) (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) {level job : (E → Sym2 V) × Finset E}
    (roundMem : level ∈ forestRounds ends w hw S)
    (jobMem : job ∈ PrimPartition.localJobs w level.1 (nonloops level.1 level.2)
      (roundParts (PrimPartition.HeapPrim.grower 2 w) level.1 level.2)) :
    let r := (support ends S).card.log2.log2.log2 + 1
    (OptimalTree.vertices job.1 job.2).card < r + 1 ∧ job.2.card < r ^ 2 + 1 := by
  let r := (support ends S).card.log2.log2.log2 + 1
  let g : PrimPartition.Grower V E W w := PrimPartition.HeapPrim.grower 2 w
  let alg : Solvers V E W w := bankSolvers w hw (MSFPrecompute.fillBank r (r ^ 2)) rfl
  have levelSize := roundInputs_support g alg hw ends S level roundMem
  obtain ⟨p, hp, active, eq⟩ := localJobs_mem _ _ _ _ jobMem
  have hn : (support level.1 (nonloops level.1 level.2)).card ≤ (support ends S).card := by
    simpa only [support_nonloops] using levelSize
  obtain ⟨vertices, edges⟩ := partition_lookup_fits g hw (localEnds := job.1)
    (active := active) hn hp
  rw [eq]
  exact ⟨Nat.lt_succ_of_le vertices, Nat.lt_succ_of_le edges⟩

/-- At each actual invocation the selected program reads the stored tree. The two witnesses
are the bounds used by the guards of `cachedMSFOn`, for the original bank at all levels. -/
theorem forestRounds_cached_lookup (w : E → W) (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) {level job : (E → Sym2 V) × Finset E}
    (roundMem : level ∈ forestRounds ends w hw S)
    (jobMem : job ∈ PrimPartition.localJobs w level.1 (nonloops level.1 level.2)
      (roundParts (PrimPartition.HeapPrim.grower 2 w) level.1 level.2)) :
    let r := (support ends S).card.log2.log2.log2 + 1
    let bank := MSFPrecompute.fillBank r (r ^ 2)
    ∃ (hv : (OptimalTree.vertices job.1 job.2).card < r + 1) (he : job.2.card < r ^ 2 + 1),
      let labels := job.2.orderEmbOfFin rfl
      let table := (bank.get ⟨_, hv⟩).get ⟨_, he⟩
      let topology := OptimalTree.localEnds job.1 job.2
      let tree := MSFPrecompute.lookup table (fun i => (OptimalTree.endpointPair (topology i)).1)
        (fun i => (OptimalTree.endpointPair (topology i)).2)
      MSFPrecompute.cachedMSFOn bank job.1 job.2 =
        Finset.map labels.toEmbedding <$> Cslib.Query.LEQuery.relabel labels tree := by
  obtain ⟨hv, he⟩ := forestRounds_lookup_bounds w hw ends S roundMem jobMem
  exact ⟨hv, he, by simp only [MSFPrecompute.cachedMSFOn, dite_eq_left hv, dite_eq_left he]⟩

end Cslib.Multigraph.PettieRamachandran
