/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Activation

/-!
# The generators of circuits

Circuits are drawn over a small alphabet (`Cslib.Complexity.NCL.Gate`). Most generators are one
threshold vertex on all their wires (`Cslib.Complexity.NCL.Gate.vert`), whose weights are the
colors of the wires: drawn on one blue and two red wires with minimum in-flow two it is an AND
vertex, on three blue wires an OR vertex. The others stand for small gadgets, which are replaced
later by AND/OR diagrams: the red-blue conversions, drawn with their free red wire, and the free
ends of wires.

Reasoning about circuits happens over this alphabet, where a conversion is one vertex and a free
end has no constraint.

## Main definitions

* `Cslib.Complexity.NCL.Gate`, `Cslib.Complexity.NCL.Gate.interp`.
* `Cslib.Complexity.NCL.Gate.node`: an AND or OR vertex in a given drawing.
-/

public section

namespace Cslib.Complexity.NCL

local notation "R" => Color.red
local notation "B" => Color.blue

/-- The generators of circuits. -/
inductive Gate : List Color → List Color → Type
  /-- One vertex on all the wires, weighted by their colors, with the given minimum in-flow. -/
  | vert {a b : List Color} (need : ℕ) : Gate a b
  /-- A red-blue conversion from the red wire above to the blue wire below, beside a free red wire
  below. -/
  | conv : Gate [R] [B, R]
  /-- A red-blue conversion from the blue wire above to the red wire below, beside a free red wire
  below. -/
  | vnoc : Gate [B] [R, R]
  /-- A blue wire ending below with no constraint. -/
  | free : Gate [B] []
  /-- A blue wire starting above with no constraint. -/
  | start : Gate [] [B]
  /-- Two red wires ending below with no constraint. -/
  | cap : Gate [R, R] []

namespace Gate

/-- The vertices of the generators. A conversion is a vertex on its two converted wires with
minimum in-flow one; a free end is a vertex with minimum in-flow zero. -/
@[expose] def interp : Diagram.Interp Gate := ⟨fun
  | vert need => [Diagram.genVertex _ _ need]
  | conv => Prim.conv
  | vnoc => [⟨[⟨⟨.inl 0, true⟩, 2⟩, ⟨⟨.inr 0, false⟩, 1⟩], 1⟩, .loose ⟨.inr 1, false⟩ 1]
  | free => Prim.free
  | start => [.loose ⟨.inr 0, false⟩ 2]
  | cap => [.loose ⟨.inl 0, true⟩ 1, .loose ⟨.inl 1, true⟩ 1]⟩

/-- Circuit gates read their incoming wires positively and outgoing wires negatively. -/
theorem interp_forward : interp.Forward := by
  intro a b g v hv p hp
  cases g <;> aesop (add simp [interp, Diagram.genVertex, Prim.conv, Prim.wireRedBlue, Prim.free,
    Vertex.map, Port.map, Vertex.loose])

/-- A vertex with minimum in-flow two on the wires `a` above and `b` below: an AND vertex on one
blue and two red wires, an OR vertex on three blue wires. -/
abbrev node (a b : List Color) : Diagram Gate a b := .gen (.vert 2)

end Gate

end Cslib.Complexity.NCL
