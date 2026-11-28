/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Clause

/-!
# A blue-port conjunction cell

Two blue-to-red converters feed an AND vertex. Their two auxiliary red ports are capped inside
the cell, leaving two blue inputs and one blue output.

## Main definitions

* `Gadgets.AndTree.binaryGenerator`: the conjunction implication at its three blue ports.
* `Gadgets.AndTree.binaryDiagram`: its standard AND/OR implementation.

## Main results

* `Gadgets.AndTree.binaryOpenSim`: exact open simulation of the conjunction cell.
-/

public section

namespace Cslib.Complexity.NCL.Gadgets.AndTree

open Diagram
local notation "B" => Color.blue
local notation "R" => Color.red

/-- The output may point outward only when both blue inputs point inward. -/
@[expose] def binaryGenerator : Prim [B, B] [B] :=
  [Vertex.clause [⟨.inl 0, true⟩, ⟨.inr 0, false⟩],
    Vertex.clause [⟨.inl 1, true⟩, ⟨.inr 0, false⟩]]

/-- Two converters, a red-wire permutation, and an AND with a paired auxiliary cap. -/
@[expose] def binaryCore : Diagram Gate [B, B] [B] :=
  (((gen Gate.vnoc).tensor (gen Gate.vnoc)).comp (pad [R] (swap R R) [R])).comp
    ((gen (Gate.vert (a := [R, R]) (b := [B]) 2)).tensor (gen Gate.cap))

/-- Expand both converters and the auxiliary cap into ordinary AND/OR vertices. -/
@[expose] def binaryDiagram : Diagram Prim [B, B] [B] := binaryCore.subst Gate.expand

private def mainWire (i : Fin 2) : binaryCore.Edge :=
  binaryCore.numEquiv.symm ⟨2 + 2 * i.val, by change 2 + 2 * i.val < 7; omega⟩

private def binaryCert : Cert binaryGenerator binaryCore where
  canon β y := if y = .inl 0 then β (.inl 0)
    else if y = .inl 1 then β (.inl 1)
    else if y = binaryCore.bottom 0 then β (.inr 0)
    else if y = mainWire 0 then β (.inl 0)
    else if y = mainWire 1 then β (.inl 1)
    else false
  rounds := 2
  refute _ := .conflict
  pre β x := if x = .inl 0 ∧ β (.inl 0) then [mainWire 0]
    else if x = .inl 1 ∧ β (.inl 1) then [mainWire 1] else []
  post β x := if x = .inl 0 ∧ !β (.inl 0) then [mainWire 0]
    else if x = .inl 1 ∧ !β (.inl 1) then [mainWire 1] else []

private def binaryCoreOpenSim :
    OpenSim Prim.interp Gate.interp (gen binaryGenerator) binaryCore :=
  OpenSim.ofCert binaryCert (by decide +kernel)

/-- The conjunction implication is implemented with ordinary AND and OR vertices. -/
def binaryOpenSim : OpenSim Prim.interp Prim.interp (gen binaryGenerator) binaryDiagram :=
  binaryCoreOpenSim.trans (openSimSubst Gate.expandOpenSim binaryCore)

/-- The three-port source is the Boolean conjunction implication. -/
theorem legal_binary_iff (s : Fin 2 ⊕ Fin 1 → Bool) :
    ((gen binaryGenerator).graph Prim.interp).Legal s ↔
      s (.inr 0) = false ∨ s (.inl 0) = true ∧ s (.inl 1) = true := by
  rw [← genLegal_iff]
  by_cases ho : s (.inr 0) = false <;>
    simp [GenLegal, Prim.interp, binaryGenerator, Vertex.sat_clause_iff, Port.In, ho]

/-- Every expanded generator is one standard AND or OR vertex. -/
theorem binary_checkStandard : binaryDiagram.checkGens
    Prim.checkStandard = true := by decide +kernel

/-- The blue conjunction cell has fifteen standard vertices. -/
theorem binary_vertexCount : (binaryDiagram.vertexList Prim.interp).length = 15 := by decide +kernel

/-- The blue conjunction cell creates twenty-two internal or outgoing wires. -/
theorem binary_innerCount : binaryDiagram.innerCount = 22 := by decide +kernel

end Cslib.Complexity.NCL.Gadgets.AndTree
