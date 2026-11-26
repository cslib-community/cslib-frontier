/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Cells
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Enumeration
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Portable local implementation templates

Local wire references distinguish a boundary position from a private creation number. A
context supplies boundary names, a private offset, and the possible reversed row output.
Instantiating a template is a polynomial-time list map using unary intermediate addresses.

## Main definitions

* `SelectorNetwork.AndOr.Template`: portable local vertex data and private wire numbers.
* `SelectorNetwork.AndOr.Template.instantiate`: emit the vertices on ambient natural names.
* `SelectorNetwork.AndOr.Cell.template`: the actual portable data of each certified cell.

## Main results

* `SelectorNetwork.AndOr.Template.computableInPolyTime_instantiate`: polynomial-time emission.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

open Diagram _root_.Turing.MultiTapeTM

/-- A boundary index or a private creation number inside one implementation. -/
structure WireRef where
  /-- True for a boundary position; false for a private creation number. -/
  boundary : Bool
  /-- The position or creation number. -/
  index : ℕ
  deriving @[expose] DecidableEq

/-- Unary local positions and their boundary/private tag. -/
enc_structure encWireRef : WireRef where
  boundary : encBool, index : encUnary

/-- The ambient information used to instantiate one portable implementation. -/
structure TemplateContext where
  /-- Names of the top ports followed by the bottom ports. -/
  boundaryNames : List ℕ
  /-- Offset of the cell's private creation numbers. -/
  privateBase : ℕ
  /-- Whether this cell reverses one row port. -/
  reverse : Bool
  /-- The reversed row port's ambient name. -/
  anchor : ℕ

/-- Framed boundary names and unary intermediate offsets. -/
enc_structure encTemplateContext : TemplateContext where
  boundaryNames : (encList encUnary), privateBase : encUnary, reverse : encBool, anchor : encUnary

/-- A portable standard implementation with local wire references. -/
structure Template where
  /-- The implementation vertices. -/
  vertices : List (Vertex WireRef)
  /-- All private wires, in creation order. -/
  privateWires : List ℕ

/-- Structural local data, with unary private creation numbers. -/
enc_structure encTemplate : Template where
  vertices : (encList (encVertex encWireRef)), privateWires : (encList encUnary)

namespace WireRef

/-- Resolve a local reference in its ambient context. -/
@[expose] def resolve (C : TemplateContext) (r : WireRef) : ℕ :=
  if r.boundary then C.boundaryNames.getD r.index 0 else C.privateBase + r.index

private theorem computableInPolyTime_resolve :
    ComputableInPolyTime (fun p : TemplateContext × WireRef => resolve p.1 p.2)
      (encPair encTemplateContext encWireRef) encUnary := by
  unfold resolve
  fun_prop

end WireRef

namespace Template

/-- Emit one vertex and change the row anchor's reference direction when requested. -/
@[expose] def instantiateVertex (C : TemplateContext) (v : Vertex WireRef) : Vertex ℕ :=
  (v.map (WireRef.resolve C)).reorient (fun e => C.reverse && decide (e = C.anchor))

/-- Emit a complete local implementation on its ambient wire names. -/
@[expose] def instantiate (T : Template) (C : TemplateContext) : List (Vertex ℕ) :=
  T.vertices.map (instantiateVertex C)

private theorem computableInPolyTime_instantiateVertex :
    ComputableInPolyTime (fun p : TemplateContext × Vertex WireRef => instantiateVertex p.1 p.2)
      (encPair encTemplateContext (encVertex encWireRef)) (encVertex encUnary) := by
  unfold instantiateVertex Vertex.reorient Vertex.map
  simp only [List.map_map, Function.comp_def, WeightedPort.map, WeightedPort.reorient,
    Port.map, Port.reorient]
  apply encVertex_mk_polyTime
  · change ComputableInPolyTime (fun p : TemplateContext × Vertex WireRef =>
        p.2.ports.map fun q =>
          (⟨Port.mk (WireRef.resolve p.1 q.port.edge)
            ((p.1.reverse && decide (WireRef.resolve p.1 q.port.edge = p.1.anchor)) ^^ q.port.dir),
              q.weight⟩ : WeightedPort ℕ)) _ _
    apply ComputableInPolyTime.mapWithInput
      (encA := encWeightedPort encWireRef) (by fun_prop)
    have hp : ComputableInPolyTime
        (fun p : (TemplateContext × Vertex WireRef) × (WeightedPort WireRef) =>
          (p.1.1, p.2.port.edge))
        (encPair (encPair encTemplateContext (encVertex encWireRef))
          (encWeightedPort encWireRef)) (encPair encTemplateContext encWireRef) := by
      fun_prop
    have hr := WireRef.computableInPolyTime_resolve.comp hp
    fun_prop
  · fun_prop

private theorem computableInPolyTime_mapVertices :
    ComputableInPolyTime
      (fun p : TemplateContext × List (Vertex WireRef) => p.2.map (instantiateVertex p.1))
      (encPair encTemplateContext (encList (encVertex encWireRef)))
      (encList (encVertex encUnary)) := by
  apply ComputableInPolyTime.mapWithInput
    (f := fun (p : TemplateContext × List (Vertex WireRef)) v => instantiateVertex p.1 v)
    (ComputableInPolyTime.snd encTemplateContext (encList (encVertex encWireRef)))
  have hf := ComputableInPolyTime.fst
    (encPair encTemplateContext (encList (encVertex encWireRef))) (encVertex encWireRef)
  have hh := hf.fst'.prod
    (ComputableInPolyTime.snd
      (encPair encTemplateContext (encList (encVertex encWireRef))) (encVertex encWireRef))
  simpa only [Function.comp_def] using computableInPolyTime_instantiateVertex.comp hh

/-- Portable-template emission is polynomial-time in its structural data and unary addresses. -/
theorem computableInPolyTime_instantiate :
    ComputableInPolyTime (fun p : Template × TemplateContext => instantiate p.1 p.2)
      (encPair encTemplate encTemplateContext) (encList (encVertex encUnary)) := by
  have hv := encTemplate_vertices_polyTime
    (ComputableInPolyTime.fst encTemplate encTemplateContext)
  simpa only [instantiate, Function.comp_def] using computableInPolyTime_mapVertices.comp
    ((ComputableInPolyTime.snd encTemplate encTemplateContext).prod hv)

end Template

namespace Cell

/-- The local boundary index or private creation number of each implementation wire. -/
@[expose] def wireRef (c : Cell) (e : c.diagram.Edge) : WireRef :=
  match Diagram.Replacement.label c.openSim
      (fun x => (finSumFinEquiv x).val) e with
  | .inl i => ⟨true, i⟩
  | .inr e => ⟨false, c.diagram.num e.val⟩

/-- The actual certified implementation, erased to portable local vertex and wire data. -/
@[expose] def template (c : Cell) : Template where
  vertices := (c.diagram.vertexList Prim.interp).map (Vertex.map (wireRef c))
  privateWires := (Diagram.Replacement.innerList c.openSim).map fun e => c.diagram.num e.val

end Cell
end Cslib.Complexity.NCL.SelectorNetwork.AndOr
