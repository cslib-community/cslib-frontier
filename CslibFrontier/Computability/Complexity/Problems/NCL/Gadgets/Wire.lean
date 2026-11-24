/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.ConvDrawings
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Standard
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Generator

/-!
# Wires and bends

Two conversions implement a wire of either color. A blue bend uses an AND and a conversion;
red bends use two further conversions, whose auxiliary red wires are joined together.
Each wire imposes the disjunction of its two inward boundary directions. The certificates
check at most four boundary states and use only the central wires as moves.

## Main definitions

* `Cslib.Complexity.NCL.Gadgets.Wire.straight`: two equal-color ports, one above and one below.
* `Cslib.Complexity.NCL.Gadgets.Wire.cup`, `Cslib.Complexity.NCL.Gadgets.Wire.cap`: two ports
  below or above.

## Main results

* `Cslib.Complexity.NCL.Gadgets.Wire.straightOpenSim`,
  `Cslib.Complexity.NCL.Gadgets.Wire.cupOpenSim`,
  `Cslib.Complexity.NCL.Gadgets.Wire.capOpenSim`: certified AND/OR implementations.

## References

* [E. D. Demaine and R. A. Hearn, *Constraint Logic: A Uniform Framework for Modeling
  Computation as Games*][DemaineHearn2008]
-/

public section

namespace Cslib.Complexity.NCL.Gadgets.Wire

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- A two-port wire with the prescribed drawing. -/
@[expose] def generator (a b : List Color) (c : Color) : Prim a b :=
  [genVertex a b c.weight]

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def blueStraightCore : Diagram Prim [B] [B] :=
  (gen Conv.blueToRedRedGenerator).comp (gen Conv.redRedToBlueGenerator)

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def redStraightCore : Diagram Prim [R] [R] :=
  (gen Prim.conv).comp (gen Conv.blueRedToRedGenerator)

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def blueCupCore : Diagram Prim [] [B, B] :=
  (gen Prim.andSource).comp ((Diagram.id [B]).tensor (gen Conv.redRedToBlueGenerator))

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def blueCapCore : Diagram Prim [B, B] [] :=
  ((gen Conv.blueToRedRedGenerator).tensor (Diagram.id [B])).comp (gen Prim.andSink)

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def redCupCore : Diagram Prim [] [R, R] :=
  ((gen (generator [] [B, B] B)).comp
    ((gen Conv.blueToRedRedGenerator).tensor (Diagram.id [B]))).comp
    ((Diagram.id [R]).tensor (gen Conv.redBlueToRedGenerator))

/-- The small conversion-level core used by its wire certificate. -/
@[expose] def redCapCore : Diagram Prim [R, R] [] :=
  (((Diagram.id [R]).tensor (gen Conv.redToRedBlueGenerator)).comp
    ((gen Conv.redRedToBlueGenerator).tensor (Diagram.id [B]))).comp
    (gen (generator [B, B] [] B))

/-- A straight wire, implemented by two conversions with their auxiliary red wires joined. -/
@[expose] def straight : (c : Color) → Diagram Prim [c] [c]
  | .blue => Gadgets.vnoc.comp Conv.redRedToBlue
  | .red => Gadgets.conv.comp Conv.blueRedToRed

/-- A blue cup, shared by the blue and red bends. -/
@[expose] def blueCup : Diagram Prim [] [B, B] :=
  (gen Prim.andSource).comp ((Diagram.id [B]).tensor Conv.redRedToBlue)

/-- A blue cap, shared by the blue and red bends. -/
@[expose] def blueCap : Diagram Prim [B, B] [] :=
  (Gadgets.vnoc.tensor (Diagram.id [B])).comp (gen Prim.andSink)

/-- A cup, with both external ports below. -/
@[expose] def cup : (c : Color) → Diagram Prim [] [c, c]
  | .blue => blueCup
  | .red => ((blueCup.comp (Gadgets.vnoc.tensor (Diagram.id [B]))).comp
      ((Diagram.id [R]).tensor Conv.redBlueToRed))

/-- A cap, with both external ports above. -/
@[expose] def cap : (c : Color) → Diagram Prim [c, c] []
  | .blue => blueCap
  | .red => (((Diagram.id [R]).tensor Conv.redToRedBlue).comp
      (Conv.redRedToBlue.tensor (Diagram.id [B]))).comp blueCap

end Cslib.Complexity.NCL.Gadgets.Wire

end

public section

namespace Cslib.Complexity.NCL.Gadgets.Wire

open Diagram
local notation "R" => Color.red
local notation "B" => Color.blue

private def blueStraightCert : Cert (generator [B] [B] B) blueStraightCore where
  canon β y := if y = .inl 0 then β (.inl 0)
    else if y = blueStraightCore.bottom 0 then β (.inr 0)
    else if blueStraightCore.num y = 1 then β (.inr 0) else false
  rounds := 2
  refute _ := .conflict
  pre β x := if x = .inr 0 ∧ β x = false then
    [blueStraightCore.numEquiv.symm ⟨1, by decide⟩] else []
  post β x := if x = .inr 0 ∧ β x = true then
    [blueStraightCore.numEquiv.symm ⟨1, by decide⟩] else []

private def redStraightCert : Cert (generator [R] [R] R) redStraightCore where
  canon β y := if y = .inl 0 then β (.inl 0)
    else if y = redStraightCore.bottom 0 then β (.inr 0)
    else if redStraightCore.num y = 1 then β (.inr 0) else false
  rounds := 2
  refute _ := .conflict
  pre β x := if x = .inr 0 ∧ β x = false then [redStraightCore.numEquiv.symm ⟨1, by decide⟩] else []
  post β x := if x = .inr 0 ∧ β x = true then [redStraightCore.numEquiv.symm ⟨1, by decide⟩] else []

private def blueCupCert : Cert (generator [] [B, B] B) blueCupCore where
  canon β y := if y = blueCupCore.bottom 0 then β (.inr 0)
    else if y = blueCupCore.bottom 1 then β (.inr 1)
    else if blueCupCore.num y = 1 then β (.inr 1) else false
  rounds := 2
  refute _ := .conflict
  pre β x := if x = .inr 1 ∧ β x = false then [blueCupCore.numEquiv.symm ⟨1, by decide⟩] else []
  post β x := if x = .inr 1 ∧ β x = true then [blueCupCore.numEquiv.symm ⟨1, by decide⟩] else []

private def blueCapCert : Cert (generator [B, B] [] B) blueCapCore where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else if blueCapCore.num y = 2 then β (.inl 0) else true
  rounds := 2
  refute _ := .conflict
  pre β x := if x = .inl 0 ∧ β x = true then [blueCapCore.numEquiv.symm ⟨2, by decide⟩] else []
  post β x := if x = .inl 0 ∧ β x = false then [blueCapCore.numEquiv.symm ⟨2, by decide⟩] else []

private def redCupCert : Cert (generator [] [R, R] R) redCupCore where
  canon β y := if y = redCupCore.bottom 0 then β (.inr 0)
    else if y = redCupCore.bottom 1 then β (.inr 1)
    else if redCupCore.num y = 0 then β (.inr 0)
    else if redCupCore.num y = 1 then β (.inr 1) else false
  rounds := 3
  refute _ := .conflict
  pre β x := if β x = false then
      [redCupCore.numEquiv.symm ⟨if x = .inr 0 then 0 else 1, by split <;> decide⟩] else []
  post β x := if β x = true then
      [redCupCore.numEquiv.symm ⟨if x = .inr 0 then 0 else 1, by split <;> decide⟩] else []

private def redCapCert : Cert (generator [R, R] [] R) redCapCore where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else if redCapCore.num y = 3 then β (.inl 1)
    else if redCapCore.num y = 4 then β (.inl 0) else false
  rounds := 3
  refute _ := .conflict
  pre β x := if β x = true then
      [redCapCore.numEquiv.symm ⟨if x = .inl 0 then 4 else 3, by split <;> decide⟩] else []
  post β x := if β x = false then
      [redCapCore.numEquiv.symm ⟨if x = .inl 0 then 4 else 3, by split <;> decide⟩] else []

private def blueStraightCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [B] [B] B)) blueStraightCore :=
  OpenSim.ofCert blueStraightCert (by decide +kernel)

private def redStraightCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [R] [R] R)) redStraightCore :=
  OpenSim.ofCert redStraightCert (by decide +kernel)

private def blueCupCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [] [B, B] B)) blueCupCore :=
  OpenSim.ofCert blueCupCert (by decide +kernel)

private def blueCapCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [B, B] [] B)) blueCapCore :=
  OpenSim.ofCert blueCapCert (by decide +kernel)

private def redCupCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [] [R, R] R)) redCupCore :=
  OpenSim.ofCert redCupCert (by decide +kernel)

private def redCapCoreOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [R, R] [] R)) redCapCore :=
  OpenSim.ofCert redCapCert (by decide +kernel)

/-- A straight wire realizes its two-port threshold. -/
def straightOpenSim (c : Color) :
    OpenSim Prim.interp Prim.interp (gen (generator [c] [c] c)) (straight c) := by
  cases c with
  | blue =>
    exact (blueStraightCoreOpenSim).trans
      (Conv.blueToRedRedOpenSim.comp Conv.redRedToBlueOpenSim)
  | red =>
    exact (redStraightCoreOpenSim).trans
      (Conv.openSim.comp Conv.blueRedToRedOpenSim)

private def blueCupOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [] [B, B] B)) blueCup :=
  (blueCupCoreOpenSim).trans
    ((OpenSim.refl _).comp ((OpenSim.idWires [B]).tensor Conv.redRedToBlueOpenSim))

/-- A cup realizes the disjunction of its two inward directions. -/
def cupOpenSim : (c : Color) →
    OpenSim Prim.interp Prim.interp (gen (generator [] [c, c] c)) (cup c)
  | .blue => blueCupOpenSim
  | .red => (redCupCoreOpenSim).trans
      ((blueCupOpenSim.comp (Conv.blueToRedRedOpenSim.tensor (OpenSim.idWires [B]))).comp
        ((OpenSim.idWires [R]).tensor Conv.redBlueToRedOpenSim))

private def blueCapOpenSim :
    OpenSim Prim.interp Prim.interp (gen (generator [B, B] [] B)) blueCap :=
  (blueCapCoreOpenSim).trans
    ((Conv.blueToRedRedOpenSim.tensor (OpenSim.idWires [B])).comp (OpenSim.refl _))

/-- A cap realizes the disjunction of its two inward directions. -/
def capOpenSim : (c : Color) →
    OpenSim Prim.interp Prim.interp (gen (generator [c, c] [] c)) (cap c)
  | .blue => blueCapOpenSim
  | .red => (redCapCoreOpenSim).trans
      ((((OpenSim.idWires [R]).tensor Conv.redToRedBlueOpenSim).comp
        (Conv.redRedToBlueOpenSim.tensor (OpenSim.idWires [B]))).comp blueCapOpenSim)

/-- Straight wire implementations contain standard single-vertex AND/OR cells. -/
theorem straight_checkStandard (c : Color) :
    (straight c).checkGens (fun g => (g.length == 1) && Prim.checkStandard g) = true := by
  cases c <;> decide +kernel

/-- Cup implementations contain standard single-vertex AND/OR cells. -/
theorem cup_checkStandard (c : Color) :
    (cup c).checkGens (fun g => (g.length == 1) && Prim.checkStandard g) = true := by
  cases c <;> decide +kernel

/-- Cap implementations contain standard single-vertex AND/OR cells. -/
theorem cap_checkStandard (c : Color) :
    (cap c).checkGens (fun g => (g.length == 1) && Prim.checkStandard g) = true := by
  cases c <;> decide +kernel

/-- Straight wire implementations have no crossings. -/
theorem straight_planar (c : Color) : (straight c).Planar := by
  cases c <;> decide +kernel

/-- Cup implementations have no crossings. -/
theorem cup_planar (c : Color) : (cup c).Planar := by
  cases c <;> decide +kernel

/-- Cap implementations have no crossings. -/
theorem cap_planar (c : Color) : (cap c).Planar := by
  cases c <;> decide +kernel

/-- A blue cap uses six vertices; a red cap uses sixteen. -/
theorem cap_length_vertexList (c : Color) : ((cap c).vertexList Prim.interp).length =
    (match c with | .red => 16 | .blue => 6) := by
  cases c <;> decide +kernel

/-- Blue and red caps create eight and twenty-three wires respectively. -/
theorem cap_innerCount (c : Color) : (cap c).innerCount =
    (match c with | .red => 23 | .blue => 8) := by
  cases c <;> decide +kernel

/-- A cap has at most sixteen vertices. -/
theorem cap_length_vertexList_le (c : Color) : ((cap c).vertexList Prim.interp).length ≤ 16 := by
  rw [cap_length_vertexList]
  cases c <;> decide +kernel

/-- A cap creates at most twenty-three wires beyond its two incoming wires. -/
theorem cap_innerCount_le (c : Color) : (cap c).innerCount ≤ 23 := by
  rw [cap_innerCount]
  cases c <;> decide +kernel

end Cslib.Complexity.NCL.Gadgets.Wire
