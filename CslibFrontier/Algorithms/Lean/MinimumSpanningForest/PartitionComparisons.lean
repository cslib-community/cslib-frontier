/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.CachedReduction
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Packing

/-!
# Charging all small-graph comparisons in a partition

Each Prim prefix has a tree reaching every vertex in the prefix. Its local minimum spanning
forest therefore has at least one fewer edges than the number of vertices in the compact local
topology. The local forests use disjoint edge labels and their union is acyclic in the original
graph. Gluing the compact topologies at a common vertex bounds the sum of their optimal budgets
by the single worst-case budget at the size of the original input. This directly bounds the
local comparison programs used in the recursive reduction, as required by the inequality in
[PettieRamachandran2002], Corollary 5.6.
-/

public section

namespace Cslib.Multigraph

open Finset
open scoped Sym2

variable {E V : Type} {W : Type*} [LinearOrder W]
variable {ends : E → Sym2 V} {w key : E → W} {S : Finset E} {C : Set V}

/-- The edges adding fresh vertices along a Prim prefix form a tree on the reached vertices. -/
theorem PrimPrefix.exists_tree (pre : PrimPrefix ends S key C) :
    ∃ (A : Finset V) (F : Finset E), (A : Set V) = C ∧ F ⊆ internalEdges ends S C ∧
      IsAcyclic ends F ∧ A.card = F.card + 1 := by
  classical
  induction pre with
  | start v =>
    exact ⟨{v}, ∅, by simp, empty_subset _,
      by simpa only [coe_empty] using (isAcyclic_empty (ends := ends)), by simp⟩
  | @step C e u v prior hu hv he inc _ ih =>
    obtain ⟨A, F, hA, hF, ac, card⟩ := ih
    have contained (f : E) (hf : f ∈ F) : ∀ z ∈ ends f, z ∈ C :=
      (mem_internalEdges.1 (hF hf)).2
    have newEdge : e ∉ F := fun h => hv (contained e h v (by simp [inc]))
    have newVert : v ∉ A := fun h => hv (hA ▸ h)
    have separates {x y : V} (hx : x ∈ C) (hy : y ∉ C) : ¬Joins ends F x y := by
      intro path
      obtain ⟨f, hf, cut⟩ := path.exists_mem_edgeCut hx hy
      obtain ⟨s, t, pair, _, outside⟩ := Graph.mem_edgeCut_iff.1 cut
      exact outside (contained f hf t (by change ends f = s(s,t) at pair; simp [pair]))
    refine ⟨insert v A, insert e F, by simp [hA], ?_, ?_, ?_⟩
    · intro f hf
      rcases mem_insert.1 hf with rfl | hf
      · apply mem_internalEdges.2 ⟨he, ?_⟩
        intro z hz
        rcases (Sym2.mem_iff.mp (inc ▸ hz)) with rfl | rfl
        · exact Set.mem_insert_of_mem _ hu
        · exact Set.mem_insert _ _
      · exact mem_internalEdges.2 ⟨(mem_internalEdges.1 (hF hf)).1,
          fun z hz => Set.mem_insert_of_mem _ (contained f hf z hz)⟩
    · rw [coe_insert]
      apply PrimPartition.acyclic_insert ac
      intro x y hxy
      rcases Sym2.eq_iff.mp (inc.symm.trans hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact separates hu hv
      · exact fun path => separates hu hv path.symm
    · rw [card_insert_of_notMem newEdge, card_insert_of_notMem newVert, card]

namespace PrimPartition

variable [LinearOrder E] [LinearOrder V]

/-- The compact edge subset and current quotient endpoint map at each small-program invocation. -/
noncomputable def localJobs (w : E → W) (ends : E → Sym2 V) (S : Finset E) :
    List (PartitionPart V E W) → List ((E → Sym2 V) × Finset E)
  | [] => []
  | p :: ps => (ends, compactParallel ends w (internalEdges ends S p.vertices)) ::
      localJobs w (p.nextEnds ends S) (p.remaining ends w S) ps

private def jobSize (job : (E → Sym2 V) × Finset E) : ℕ × ℕ :=
  (job.2.card, (OptimalTree.vertices job.1 job.2).card)

private theorem jobSizes_le {ps : List (PartitionPart V E W)} (run : Valid w ends S ps)
    (hw : Function.Injective w) :
    ((localJobs w ends S ps).map fun j => (jobSize j).1).sum ≤ S.card ∧
    ((localJobs w ends S ps).map fun j => (jobSize j).2 - 1).sum ≤
      (collect w ends S ps).forests.card := by
  induction run with
  | nil => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | @cons ends S p ps prim raised tail ih =>
    let I := internalEdges ends S p.vertices
    let T := compactParallel ends w I
    let remain := p.remaining ends w S
    let next := p.nextEnds ends S
    let F := msf ends w I
    have left : I ⊆ S := fun _ h => (mem_internalEdges.1 h).1
    have rest : remain ⊆ S \ I := p.remaining_subset_sdiff ends w S
    have hE := card_le_card rest
    have hI := card_sdiff_add_card_eq_card left
    have hT : T.card ≤ I.card := card_le_card compactParallel_subset
    obtain ⟨A, F', hA, sub, ac, card⟩ := prim.exists_tree
    have hV : (OptimalTree.vertices ends T).card ≤ A.card :=
      card_le_card (vertices_compactParallel_subset (fun e he z hz => by
        change z ∈ (A : Set V)
        rw [hA]
        exact (mem_internalEdges.1 he).2 z hz))
    have hF : F'.card ≤ F.card := ac.card_le_spanningForest sub (isSpanningForest_msf w hw)
    have sep : Disjoint F (collect w next remain ps).forests := disjoint_left.2 fun e hf hg =>
      (mem_sdiff.1 (rest (forests_subset hg))).2 (msf_subset w hf)
    let tail := localJobs w next remain ps
    let edges := (tail.map fun j => (jobSize j).1).sum
    let vertices := (tail.map fun j => (jobSize j).2 - 1).sum
    change T.card + edges ≤ S.card ∧ (OptimalTree.vertices ends T).card - 1 + vertices ≤
      (F ∪ (collect w next remain ps).forests).card
    rw [card_union_of_disjoint sep]
    change edges ≤ remain.card ∧ vertices ≤ (collect w next remain ps).forests.card at ih
    exact ⟨by omega, by omega⟩

/-- The sum of compact local edge counts in a partition fits its input edge count. -/
theorem sum_localJobs_edges_le {ps : List (PartitionPart V E W)} (run : Valid w ends S ps)
    (hw : Function.Injective w) :
    ((localJobs w ends S ps).map (fun j => j.2.card)).sum ≤ S.card :=
  (jobSizes_le run hw).1

/-- Sum of actual cached local-program comparisons in one valid partition is at most the
global worst-case optimum at the input edge count and any nonempty support bound. -/
theorem sum_cached_countQueries_le {ps : List (PartitionPart V E W)} (run : Valid w ends S ps)
    (hw : Function.Injective w) (X : Finset V) (hx : X.Nonempty)
    (support : ∀ e ∈ S, ∀ x ∈ ends e, x ∈ X) (maxV maxE : ℕ) :
    ((localJobs w ends S ps).map fun j =>
      (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank maxV maxE) j.1 j.2).countQueries
        (Cslib.Query.LEQuery.keyOracle w)).sum ≤ OptimalTree.worstCase S.card X.card := by
  let jobs := localJobs w ends S ps
  have each (j : (E → Sym2 V) × Finset E) :
      (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank maxV maxE) j.1 j.2).countQueries
        (Cslib.Query.LEQuery.keyOracle w) ≤ OptimalTree.worstCase (jobSize j).1 (jobSize j).2 := by
    rw [MSFPrecompute.cachedMSFOn_fill]
    exact (optimalMSFOn_spec _ _ w hw.injOn).2.trans
      (OptimalTree.optimalMSFComparisons_le_worstCase _)
  have sum (js : List ((E → Sym2 V) × Finset E)) :
      (js.map fun j =>
        (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank maxV maxE) j.1 j.2).countQueries
          (Cslib.Query.LEQuery.keyOracle w)).sum ≤
      (js.map fun j => OptimalTree.worstCase (jobSize j).1 (jobSize j).2).sum := by
    induction js with
    | nil => exact le_rfl
    | cons j js ih => exact Nat.add_le_add (each j) ih
  have pack := OptimalTree.sum_worstCase_le (jobs.map jobSize)
  simp only [List.map_map, Function.comp_def] at pack
  have ⟨edges, vertices⟩ := jobSizes_le run hw
  have cap := (isAcyclic_forests (ends := ends) (S := S) (ps := ps) hw).card_le
    (fun e he => support e (forests_subset he))
  exact (sum jobs).trans (pack.trans (OptimalTree.worstCase_mono edges (by
    change ((localJobs w ends S ps).map _).sum + 1 ≤ X.card
    have pos := Finset.card_pos.mpr hx
    omega)))

end PrimPartition

namespace PettieRamachandran

variable [LinearOrder E] [LinearOrder V]

/-- Total weight comparisons performed by the cached small programs in one recursive round.
Each summand is read from the CSLib query interpreter on the program supplied at that call. -/
noncomputable def roundLocalComparisons (grower : PrimPartition.Grower V E W w)
    (maxV maxE : ℕ) (ends : E → Sym2 V) (S : Finset E) : ℕ :=
  let jobs := PrimPartition.localJobs w ends (nonloops ends S) (roundParts grower ends S)
  (jobs.map fun j =>
    (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank maxV maxE) j.1 j.2).countQueries
      (Cslib.Query.LEQuery.keyOracle w)).sum

/-- The small-program comparisons of the actual round fit the global optimal budget,
including rounds whose input consists entirely of loops. -/
theorem roundLocalComparisons_le (grower : PrimPartition.Grower V E W w) (hw : Function.Injective w)
    (maxV maxE : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    roundLocalComparisons grower maxV maxE ends S ≤
      OptimalTree.worstCase S.card (support ends S).card := by
  let A := nonloops ends S
  let X := support ends A
  by_cases hX : X.Nonempty
  · have valid : PrimPartition.Valid w ends A (roundParts grower ends S) :=
      PrimPartition.valid_partition ..
    have contain (e : E) (he : e ∈ A) (z : V) (hz : z ∈ ends e) : z ∈ X :=
      mem_support.2 ⟨e, he, (mem_nonloops.1 he).2, hz⟩
    have cost := PrimPartition.sum_cached_countQueries_le valid hw X hX contain maxV maxE
    exact cost.trans (OptimalTree.worstCase_mono
      (card_le_card (fun _ he => (mem_nonloops.1 he).1)) (by simp [X, A]))
  · have none : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have nil : roundParts grower ends S = [] := by
      change PrimPartition.partition grower X.card.log2.log2.log2 ends A id ∅ X.toList = []
      simp [none, PrimPartition.partition]
    simp [roundLocalComparisons, nil, PrimPartition.localJobs]

end PettieRamachandran
end Cslib.Multigraph
