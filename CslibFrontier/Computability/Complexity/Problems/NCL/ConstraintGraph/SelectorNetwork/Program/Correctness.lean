/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Program
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Emission
import Mathlib.Data.List.GetD

/-!
# Correctness of graph and direction block emission

The concrete block-list program emits exactly the same finite graph and canonical directions
as the complete selector-network simulation, in their shared owner-cell order.

## Main definitions

* `SelectorNetwork.AndOr.Program.blocks`: graph blocks of the actual implementation.
* `SelectorNetwork.AndOr.Program.stateBlocks`: its canonical-direction blocks.

## Main results

* `SelectorNetwork.AndOr.Program.graph_blocks`: exact graph serialization.
* `SelectorNetwork.AndOr.Program.bits_stateBlocks`: exact direction serialization.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Program

open Diagram

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m : ℕ} (order : Vert U C R ≃ Fin m) {budget : ℕ}
variable (hshape : ∀ v, (cell N A v).top.length ≤ budget)

/-- Actual graph blocks in source-cell order, carrying their source row. -/
@[expose] def blocks (stride : ℕ) (row : Vert U C R → ℕ) : List (Block budget) :=
  (List.ofFn order.symm).map fun v =>
    ⟨⟨cell N A v, hshape v⟩, Sparse.context N A order stride v,
      (Numbering.ownedShared v).map (fun e => Sparse.code N A order stride (.inl e)), row v⟩

/-- Graph blocks serialize the original numbered implementation. -/
theorem graph_blocks (stride : ℕ) (row : Vert U C R → ℕ)
    (hstride : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ stride) :
    graph (blocks N A order hshape stride row) =
      AndOrGraph.ofFinite (Numbering.graph N A order) := by
  have hraw : vertices (blocks N A order hshape stride row) =
      Sparse.rawVertices N A order stride := by
    simp only [vertices, blocks, List.flatMap_map, blockVertices,
      Sparse.rawVertices]
  have hnames : names (blocks N A order hshape stride row) = Sparse.names N A order stride := by
    simp only [names, blocks, List.flatMap_map, blockNames, Sparse.context,
      Sparse.names]
  rw [← Sparse.data_eq_ofFinite N A order stride hstride]
  exact AndOrGraph.ext (by rw [graph, hraw, hnames]; rfl) (by rw [graph, hnames]; rfl)

/-- Actual canonical-direction blocks use the same owner order and local boundary order. -/
@[expose] def stateBlocks (s : Edge C R → Bool) : List (StateBlock budget) :=
  (List.ofFn order.symm).map fun v =>
    ⟨⟨cell N A v, hshape v⟩,
      List.ofFn (fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
        ((polarity N A v + s) ∘ port N A v) (finSumFinEquiv.symm i)),
      (Numbering.ownedShared v).map s⟩

private theorem privateBits_ofFn (v : Vert U C R) (s : Edge C R → Bool) :
    (cell N A v).privateBits
      (List.ofFn fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
        ((polarity N A v + s) ∘ port N A v) (finSumFinEquiv.symm i)) =
      (Replacement.innerList (cell N A v).openSim).map
        (fun e => (cell N A v).openSim.enc ((polarity N A v + s) ∘ port N A v) e.val) := by
  unfold Cell.privateBits
  have hread (x : Fin (cell N A v).top.length ⊕ Fin (cell N A v).bottom.length) :
      (List.ofFn fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
        ((polarity N A v + s) ∘ port N A v) (finSumFinEquiv.symm i)).getD
          (finSumFinEquiv x).val false = ((polarity N A v + s) ∘ port N A v) x := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (finSumFinEquiv x).isLt)]
    simp only [List.getElem_ofFn, finSumFinEquiv.symm_apply_apply]
  simp only [hread]

/-- Direction blocks serialize the same canonical global simulation as graph emission. -/
theorem bits_stateBlocks [Fintype U] [Fintype C] [Fintype R] (s : Edge C R → Bool) :
    bits (stateBlocks N A order hshape s) =
      List.ofFn ((Numbering.simulation N A order).enc ((AndOr.simulation N A).enc s)) := by
  rw [Numbering.bits_enc]
  simp only [bits, stateBlocks, List.flatMap_map, blockBits, Numbering.edgeList,
    List.map_flatMap, Numbering.localEdges, List.map_append, List.map_map,
    privateBits_ofFn]
  simp only [Function.comp_def, AndOr.simulation_enc_shared, AndOr.simulation_enc_private]

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Program
