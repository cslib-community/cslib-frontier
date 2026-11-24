/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Implements

/-!
# Primitive generators

A primitive generator (`Cslib.Complexity.NCL.Prim`) is its list of vertices on its own wires:
`.inl i` is the `i`-th wire above, `.inr j` the `j`-th wire below. A wire above points into a
vertex when it points down, a wire below when it points up. The diagrams of this library are over
primitives, interpreted by themselves (`Cslib.Complexity.NCL.Prim.interp`).

This file supplies the internal vertex drawings and abstract generators implemented by gadgets.
`Protected.Cell` is the frozen finite alphabet used by the external marked-word interface.

## Main definitions

* `Cslib.Complexity.NCL.Prim`, `Cslib.Complexity.NCL.Prim.interp`.
* AND and OR vertices in several drawings, such as `Cslib.Complexity.NCL.Prim.andSplit`.
* `Cslib.Complexity.NCL.Prim.free`: a blue wire end with no constraint.
* `Cslib.Complexity.NCL.Prim.conv`: a red-blue conversion with its free red wire drawn.
-/

public section

namespace Cslib.Complexity.NCL

/-- A primitive generator: its vertices on its own wires. -/
abbrev Prim (a b : List Color) : Type := List (Vertex (Fin a.length ⊕ Fin b.length))

namespace Prim

/-- Primitives mean themselves. -/
@[expose] def interp : Diagram.Interp Prim := ⟨fun g => g⟩

local notation "R" => Color.red
local notation "B" => Color.blue

/-- An OR vertex with one wire above and two below. -/
@[expose] def orSplit : Prim [B] [B, B] := [.or ⟨.inl 0, true⟩ ⟨.inr 0, false⟩ ⟨.inr 1, false⟩]

/-- An AND vertex with its blue wire above and its red wires below. -/
@[expose] def andSplit : Prim [B] [R, R] := [.and ⟨.inr 0, false⟩ ⟨.inr 1, false⟩ ⟨.inl 0, true⟩]

/-- An OR vertex with all three wires below. -/
@[expose] def orSource : Prim [] [B, B, B] :=
  [.or ⟨.inr 0, false⟩ ⟨.inr 1, false⟩ ⟨.inr 2, false⟩]

/-- An AND vertex with all wires below: blue, red, red. -/
@[expose] def andSource : Prim [] [B, R, R] :=
  [.and ⟨.inr 1, false⟩ ⟨.inr 2, false⟩ ⟨.inr 0, false⟩]

/-- An AND vertex with two red wires above and its blue wire below. -/
@[expose] def andJoin : Prim [R, R] [B] := [.and ⟨.inl 0, true⟩ ⟨.inl 1, true⟩ ⟨.inr 0, false⟩]

/-- An AND vertex with all its wires above: red, red, blue. -/
@[expose] def andSink : Prim [R, R, B] [] := [.and ⟨.inl 0, true⟩ ⟨.inl 1, true⟩ ⟨.inl 2, true⟩]

/-- An AND vertex with a red wire above, and below its blue wire then a red wire. -/
@[expose]
def andRedToBlueRed : Prim [R] [B, R] := [.and ⟨.inl 0, true⟩ ⟨.inr 1, false⟩ ⟨.inr 0, false⟩]

/-- An AND vertex with a red wire above, and below a red wire then its blue wire. -/
@[expose]
def andRedToRedBlue : Prim [R] [R, B] := [.and ⟨.inl 0, true⟩ ⟨.inr 0, false⟩ ⟨.inr 1, false⟩]

/-- A red-blue wire: the red wire above or the blue wire below points in
[DemaineHearn2008, Section 3.1]. -/
@[expose] def wireRedBlue : Prim [R] [B] := [⟨[⟨⟨.inl 0, true⟩, 1⟩, ⟨⟨.inr 0, false⟩, 2⟩], 1⟩]

/-- A red-blue conversion with its free red wire `F` drawn: a red-blue wire from the red wire
above to the blue wire below, and the wire `F` below with no constraint. -/
@[expose] def conv : Prim [R] [B, R] :=
  wireRedBlue.map (Vertex.map (Sum.map id Fin.castSucc)) ++ [.loose ⟨.inr 1, false⟩ 1]

/-- A blue wire end with no constraint. -/
@[expose] def free : Prim [B] [] := [.loose ⟨.inl 0, true⟩ 2]

end Prim

end Cslib.Complexity.NCL
