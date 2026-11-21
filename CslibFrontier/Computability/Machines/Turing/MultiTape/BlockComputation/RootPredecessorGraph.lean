/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorQuery

/-!
# Class ranks in the copied and subdivided block graph

For a numbered half-edge, the old vertex of the subdivided network is its row and its copied
edge is its column. These two sides embed into the one vertex universe used by the seed.
Summing the executable raw-schedule comparisons over numbered half-edges gives the original
seeded packing rank in this graph.
-/

public section

namespace Turing.MultiTapeTM.RootPredecessorGraph

open MultiTapePTM Cslib

/-- Number of half-edges after Boolean copying and subdivision. -/
abbrev edgeCount (k q copies : ℕ) := 2 * (q * (3 * k + 1) * copies)

/-- Cardinality of the disjoint union of old vertices and subdivision vertices. -/
abbrev vertexCount (k q copies : ℕ) := q * (3 * k + 2) + q * (3 * k + 1) * copies

variable {k q copies : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)

/-- The old endpoint of a numbered half-edge, in the original block vertex type. -/
@[expose] noncomputable def rowOf (e : Fin (edgeCount k q copies)) : Fin q ⊕ BlockEdge k q :=
  let graph := (machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code
  Sum.elim graph.src graph.tgt ((explicitEdgeEquiv k q copies).symm e)

/-- The copied edge at the other end of either of its two half-edges. -/
@[expose] def colOf (k q copies : ℕ) (e : Fin (edgeCount k q copies)) :
    BlockEdge k q × Fin copies :=
  Sum.elim id id ((explicitEdgeEquiv k q copies).symm e)

/-- The runtime input for a represented schedule and shared seed, including padded indices. -/
@[expose] def inputOfIndices (k q copies σ a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (e candidate : ℕ) : RootPredecessorQuery.Input :=
  ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies,
    ⟨vertexCount k q copies, a, seed 0, seed 1, seed 2, seed 3, e, candidate⟩⟩

/-- The represented instance for two genuine edges in the finite graph. -/
@[expose] def graphInput (k q copies σ a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (e candidate : Fin (edgeCount k q copies)) : RootPredecessorQuery.Input :=
  inputOfIndices k q copies σ a seed e.val candidate.val

/-- The raw query on a numbered half-edge returns its original tagged row and column keys. -/
theorem query_endpoint (e : Fin (edgeCount k q copies)) :
    RootEndpointQuery.query k
      ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies, e.val⟩ =
        some ((explicitVertexEquiv k q copies (.inl (rowOf machine input b σ code e))).val,
          (explicitVertexEquiv k q copies (.inr (colOf k q copies e))).val) := by
  have h := RootEndpointQuery.query_explicitEdgeEquiv machine input b σ code
    ((explicitEdgeEquiv k q copies).symm e)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  unfold rowOf colOf
  cases (explicitEdgeEquiv k q copies).symm e <;> rfl

variable (a : ℕ) (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (e candidate : Fin (edgeCount k q copies))

/-- The native predecessor leaf on the represented root graph compares exactly the labels
of the two actual half-edges in the seed's packing, in their original numbering. -/
theorem query_eq_predecessor :
    RootPredecessorQuery.query k (graphInput k q copies σ a seed e candidate) =
      PacketPacking.Seeded.predecessor (vertexCount k q copies) a
        (explicitVertexEquiv k q copies).toEmbedding
        (rowOf machine input b σ code) (colOf k q copies) seed e candidate := by
  simp only [RootPredecessorQuery.query, RootPredecessorQuery.finishInput,
    RootPredecessorQuery.request, graphInput, inputOfIndices]
  rw [query_endpoint machine input b σ code e, query_endpoint machine input b σ code candidate,
    SeededPredecessorFinish.run_some]
  exact SeededPredecessor.test_ofEdges _ a (explicitVertexEquiv k q copies).toEmbedding
    (rowOf machine input b σ code) (colOf k q copies) seed e candidate

/-- The sum of runtime predecessor bits is the class rank used by the seeded packing of the
actual copied and subdivided block graph. -/
theorem rank_eq_sum_query :
    PacketPacking.Seeded.rank (vertexCount k q copies) a
        (explicitVertexEquiv k q copies).toEmbedding
        (rowOf machine input b σ code) (colOf k q copies) seed e =
      ∑ candidate : Fin (edgeCount k q copies),
        (RootPredecessorQuery.query k (graphInput k q copies σ a seed e candidate)).toNat := by
  rw [PacketPacking.Seeded.rank_eq_sum_predecessors]
  exact Finset.sum_congr rfl fun candidate _ =>
    congrArg Bool.toNat (query_eq_predecessor machine input b σ code a seed e candidate).symm

end Turing.MultiTapeTM.RootPredecessorGraph
