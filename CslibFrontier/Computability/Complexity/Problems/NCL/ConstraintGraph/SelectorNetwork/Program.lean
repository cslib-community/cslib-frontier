/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Template.Bounded
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time block-list emission

A block supplies its bounded cell shape, ambient context, owned shared names, and row. The
program emits the actual local templates and compacts their sparse wire names by first-index
lookup. Canonical direction blocks use the same shapes and their boundary directions.

## Main definitions

* `SelectorNetwork.AndOr.Program.Block`: one graph-emission block.
* `SelectorNetwork.AndOr.Program.graph`: the complete explicit graph program.
* `SelectorNetwork.AndOr.Program.StateBlock`: one canonical-direction block.

## Main results

* `SelectorNetwork.AndOr.Program.computableInPolyTime_graph`: standard graph-data emission.
* `SelectorNetwork.AndOr.Program.computableInPolyTime_bits`: canonical-direction emission.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Program

open _root_.Turing.MultiTapeTM

/-- Portable input data for one bounded standard implementation. -/
structure Block (budget : ℕ) where
  /-- The actual bounded implementation shape. -/
  shape : Cell.Bounded budget
  /-- The boundary names, private offset and row polarity. -/
  context : TemplateContext
  /-- Shared names owned by the source cell. -/
  ownedNames : List ℕ
  /-- The source row of every vertex and owned wire in this block. -/
  row : ℕ

/-- The standard shape/context encodings and unary intermediate names and row indices. -/
enc_structure encBlock (budget : ℕ) : Block budget where
  shape : (Cell.encBounded budget), context : encTemplateContext,
  ownedNames : (encList encUnary), row : encUnary

/-- Vertex emission for one bounded block. -/
@[expose] def blockVertices {budget : ℕ} (b : Block budget) : List (Vertex ℕ) :=
  b.shape.val.template.instantiate b.context

/-- Shared names and private creation names owned by one block. -/
@[expose] def blockNames {budget : ℕ} (b : Block budget) : List ℕ :=
  b.ownedNames ++ b.shape.val.template.privateWires.map (fun j => b.context.privateBase + j)

/-- All emitted vertices before sparse address compaction. -/
@[expose] def vertices {budget : ℕ} (blocks : List (Block budget)) : List (Vertex ℕ) :=
  blocks.flatMap blockVertices

/-- Every owned shared or private wire in block order. -/
@[expose] def names {budget : ℕ} (blocks : List (Block budget)) : List ℕ :=
  blocks.flatMap blockNames

/-- Emit the graph and compact all names by first-index lookup. -/
@[expose] def graph {budget : ℕ} (blocks : List (Block budget)) : AndOrGraph where
  vertices := (vertices blocks).map (Vertex.map (fun e => (names blocks).idxOf e))
  edgeCount := (names blocks).length

open scoped Block
attribute [local fun_prop] Template.computableInPolyTime_instantiate

/-- Reading the actual bounded local template from a block is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_blockTemplate (budget : ℕ) :
    ComputableInPolyTime (fun b : Block budget => b.shape.val.template)
      (encBlock budget) encTemplate :=
  (Cell.computableInPolyTime_template budget).comp (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_blockVertices (budget : ℕ) :
    ComputableInPolyTime (blockVertices (budget := budget)) (encBlock budget)
      (encList (encVertex encUnary)) := by fun_prop [blockVertices]

@[local fun_prop]
private theorem computableInPolyTime_blockNames (budget : ℕ) :
    ComputableInPolyTime (blockNames (budget := budget)) (encBlock budget) (encList encUnary) := by
  have hp := encTemplate_privateWires_polyTime (computableInPolyTime_blockTemplate budget)
  fun_prop [blockNames]

@[local fun_prop]
private theorem computableInPolyTime_vertices (budget : ℕ) :
    ComputableInPolyTime (vertices (budget := budget)) (encList (encBlock budget))
      (encList (encVertex encUnary)) := by fun_prop [vertices]

@[local fun_prop]
private theorem computableInPolyTime_names (budget : ℕ) :
    ComputableInPolyTime (names (budget := budget)) (encList (encBlock budget))
      (encList encUnary) := by fun_prop [names]

@[local fun_prop]
private theorem computableInPolyTime_compactVertex :
    ComputableInPolyTime (fun p : List ℕ × Vertex ℕ => p.2.map (fun e => p.1.idxOf e))
      (encPair (encList encUnary) (encVertex encUnary)) (encVertex encNat) := by
  apply Vertex.computableInPolyTime_mapWithInput (by fun_prop)
  simpa only [Function.comp_def] using ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.idxOfWithInput (by fun_prop) (by fun_prop))

/-- Block-list graph emission is polynomial-time in the standard explicit graph encoding. -/
theorem computableInPolyTime_graph (budget : ℕ) :
    ComputableInPolyTime (graph (budget := budget)) (encList (encBlock budget)) encAndOrGraph := by
  open scoped AndOrGraph in
  have hports : ComputableInPolyTime (fun blocks : List (Block budget) =>
      (vertices blocks).map (fun v => v.map (fun e => (names blocks).idxOf e)))
      (encList (encBlock budget)) (encList (encVertex encNat)) :=
    ComputableInPolyTime.mapWithInput (computableInPolyTime_vertices budget)
      (computableInPolyTime_compactVertex.comp
        (g := fun p : List (Block budget) × Vertex ℕ => (names p.1, p.2)) (by fun_prop))
  have hc : ComputableInPolyTime (fun blocks : List (Block budget) => (names blocks).length)
      (encList (encBlock budget)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  fun_prop [graph]

/-- Input data for one canonical orientation block. -/
structure StateBlock (budget : ℕ) where
  /-- The bounded implementation shape. -/
  shape : Cell.Bounded budget
  /-- The top and bottom directions in local reference order. -/
  boundary : List Bool
  /-- Directions of the shared wires owned by this source cell. -/
  owned : List Bool

/-- Frame the shape and the two actual direction lists. -/
enc_structure encStateBlock (budget : ℕ) : StateBlock budget where
  shape : (Cell.encBounded budget), boundary : (encList encBool), owned : (encList encBool)

/-- Canonical shared and private directions for one block. -/
@[expose] def blockBits {budget : ℕ} (b : StateBlock budget) : List Bool :=
  b.owned ++ b.shape.val.privateBits b.boundary

/-- The canonical orientation in the same owner and creation order as graph emission. -/
@[expose] def bits {budget : ℕ} (blocks : List (StateBlock budget)) : List Bool :=
  blocks.flatMap blockBits

/-- Canonical direction emission is polynomial-time in the block-list encoding. -/
theorem computableInPolyTime_bits (budget : ℕ) :
    ComputableInPolyTime (bits (budget := budget)) (encList (encStateBlock budget))
      (encList encBool) := by
  open scoped StateBlock in
  have hb : ComputableInPolyTime (blockBits (budget := budget))
      (encStateBlock budget) (encList encBool) :=
    ComputableInPolyTime.listAppend' (by fun_prop)
      ((Cell.computableInPolyTime_privateBits budget).comp
        (g := fun b : StateBlock budget => (b.shape, b.boundary)) (by fun_prop))
  exact ComputableInPolyTime.flatMapWithInput (list := id) (by fun_prop)
    (hb.comp (ComputableInPolyTime.snd _ _))

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Program
