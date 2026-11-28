/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.AndTree
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Wire
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Realizes
public import CslibFrontier.Computability.Complexity.Problems.NCL.Assembly.GraphReorient

/-!
# AND/OR cells for selector networks

Rows use a disjunction with one reversed boundary reference direction. Characters use a
conjunction, and binary exclusions use a blue bend. Inactive exclusions have two free ends.

## Main definitions

* `SelectorNetwork.AndOr.Cell`: the four local implementation shapes.

## Main results

* `SelectorNetwork.AndOr.Cell.openSim`: exact open implementation of every local shape.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

open Diagram
local notation "B" => Color.blue

/-- The local shapes used in a selector network. -/
inductive Cell
  /-- A row disjunction, with its final character below. -/
  | row (arity : ℕ)
  /-- All relation branches are forced when the character is selected. -/
  | character (degree : ℕ)
  /-- Two branch endpoints, with an optional binary exclusion. -/
  | relation (required : Bool)

namespace Cell

/-- Two independent unrestricted blue endpoints. -/
@[expose] def freePair : Diagram Prim [] [B, B] := Gadgets.freeStart.tensor Gadgets.freeStart

private def freePairCert : Cert (show Prim [] [B, B] from [genVertex [] [B, B] 0]) freePair where
  canon β y := if y = freePair.bottom 0 then β (.inr 0)
    else if y = freePair.bottom 1 then β (.inr 1) else [2, 7].contains (freePair.num y)
  rounds := 0
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

private def freePairOpenSim :
    OpenSim Prim.interp Prim.interp (gen [genVertex [] [B, B] 0]) freePair :=
  OpenSim.ofCert freePairCert (by decide +kernel)

/-- Input colors of a selector cell. -/
abbrev top : Cell → List Color
  | .row n | .character n => Gadgets.OrTree.bundle n
  | .relation _ => []

/-- Output colors of a selector cell. -/
abbrev bottom : Cell → List Color
  | .row _ | .character _ => [B]
  | .relation _ => [B, B]

/-- Logical source of the local implementation. -/
@[expose] def generator : (c : Cell) → Prim c.top c.bottom
  | .row n => Gadgets.OrTree.generator n
  | .character n => Gadgets.AndTree.generator n
  | .relation true => Gadgets.Wire.generator [] [B, B] B
  | .relation false => [genVertex [] [B, B] 0]

/-- The actual standard AND/OR implementation. -/
@[expose] def diagram : (c : Cell) → Diagram Prim c.top c.bottom
  | .row n => Gadgets.OrTree.diagram n
  | .character n => Gadgets.AndTree.diagram n
  | .relation true => Gadgets.Wire.cup B
  | .relation false => freePair

/-- Every selector cell has a complete open implementation, including all boundary reversals. -/
def openSim : (c : Cell) →
    OpenSim Prim.interp Prim.interp (gen c.generator) c.diagram
  | .row n => Gadgets.OrTree.openSim n
  | .character n => Gadgets.AndTree.openSim n
  | .relation true => Gadgets.Wire.cupOpenSim B
  | .relation false => freePairOpenSim

/-- Every implementation consists of standard AND/OR generators. -/
theorem checkStandard (c : Cell) :
    c.diagram.checkGens Prim.checkStandard = true := by
  cases c with
  | row n =>
    exact ((Bool.and_eq_true _ _).mp
      ((checkGens_and _ _ _).symm.trans (Gadgets.OrTree.checkStandard n))).2
  | character n => exact Gadgets.AndTree.checkStandard n
  | relation r => cases r <;> decide +kernel

/-- Local implementations have consistent colored boundary incidences. -/
theorem checkPorts (c : Cell) : c.diagram.checkGens Prim.interp.checkPorts = true :=
  ((checkGens_checkStandard_iff _).mp c.checkStandard).2.2

/-- Each selector cell uses linearly many standard vertices and created wires. -/
theorem size_le (c : Cell) :
    (c.diagram.vertexList Prim.interp).length ≤ 64 + 22 * c.top.length ∧
      c.diagram.innerCount ≤ 64 + 22 * c.top.length := by
  cases c with
  | row n =>
    simp only [diagram, top, Gadgets.OrTree.length_vertexList, Gadgets.OrTree.innerCount,
      Gadgets.OrTree.length_bundle]
    omega
  | character n =>
    simp only [diagram, top, Gadgets.AndTree.length_vertexList, Gadgets.AndTree.innerCount,
      Gadgets.OrTree.length_bundle]
    omega
  | relation r => cases r <;> decide +kernel

end Cell
end Cslib.Complexity.NCL.SelectorNetwork.AndOr
