/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorGraph
public import CslibFrontier.Foundations.Combinatorics.SeededPacking

/-!
# A balanced seed for the numbered root half-edges

Each row or column fiber embeds into the corresponding incidence set of the subdivided Boolean
network. Its degree bound supplies the hypotheses of the four-wise balance estimate for exactly
the numeric endpoints used by the physical verifier.
-/

public section

namespace Turing.MultiTapeTM.RootPredecessorGraph

open Cslib Circuits.Frontier MultiTapePTM

/-- The variance inequality suffices for a balanced seed on the actual numbered root graph. -/
theorem exists_balanced_seed {k q copies : ℕ} {State : Type} (M : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool) (a : ℕ)
    (hc : 0 < copies)
    (hsize : 2 * (2 * (3 * k + 1) * copies) * (64 ^ (2 * a)) ^ 2 ≤ edgeCount k q copies) :
    ∃ seed, PacketPacking.Seeded.Balanced (vertexCount k q copies) a
      (explicitVertexEquiv k q copies).toEmbedding (rowOf M input b σ code) (colOf k q copies)
      seed := by
  classical
  let N := (M.blockNetwork input b (scheduleOfNat k q σ)).binarize code
  let ee := explicitEdgeEquiv k q copies
  let Δ := 2 * (3 * k + 1) * copies
  have hd : N.subdivide.MaxDegreeLE Δ := TensorNetwork.maxDegreeLE_subdivide _
    (TensorNetwork.loopless_binarize _ _ (M.loopless_blockNetwork input b _))
    (TensorNetwork.maxDegreeLE_binarize _ _ (M.maxDegreeLE_blockNetwork input b _))
    (by dsimp [Δ]; nlinarith)
  have fiber {α : Type} [DecidableEq α] (key : Fin (edgeCount k q copies) → α)
      (v : α) (w : (Fin q ⊕ BlockEdge k q) ⊕ (BlockEdge k q × Fin copies))
      (hin : ∀ e, key e = v → ee.symm e ∈ N.subdivide.incidenceSet w) :
      (Finset.univ.filter fun e => key e = v).card ≤ Δ := by
    have h := hd w
    rw [Set.ncard_eq_toFinset_card'] at h
    exact le_trans (Finset.card_le_card_of_injOn ee.symm
      (fun e he => Set.mem_toFinset.mpr (hin e (Finset.mem_filter.mp he).2))
      ee.symm.injective.injOn) h
  apply PacketPacking.Seeded.exists_balanced_labels _ _ _ _ _ (Δ := Δ)
  · intro r
    apply fiber _ r (.inl r)
    intro e he
    rw [Multigraph.mem_incidenceSet]
    change Sum.elim N.src N.tgt (ee.symm e) = r at he
    cases eq : ee.symm e with
    | inl p => exact Or.inl (congrArg Sum.inl (by simpa only [eq, Sum.elim_inl] using he))
    | inr p => exact Or.inl (congrArg Sum.inl (by simpa only [eq, Sum.elim_inr] using he))
  · intro c
    apply fiber _ c (.inr c)
    intro e he
    rw [Multigraph.mem_incidenceSet]
    change Sum.elim id id (ee.symm e) = c at he
    cases eq : ee.symm e with
    | inl p => exact Or.inr (congrArg Sum.inr (by simpa only [eq, Sum.elim_inl, id_eq] using he))
    | inr p => exact Or.inr (congrArg Sum.inr (by simpa only [eq, Sum.elim_inr, id_eq] using he))
  · simpa only [Fintype.card_fin] using hsize

end Turing.MultiTapeTM.RootPredecessorGraph
