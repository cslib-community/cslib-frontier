/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Carrier.Borders
import Mathlib.Data.Nat.Count

/-!
# Logical addresses on canonical Robinson carriers

The smallest enclosing frame determines the row and column wires. Counting the free
coordinates assigns integer addresses centered at the frame center. The nearest-border
signals agree with those arithmetic wires, and neighboring carriers obey the address
step equations needed to transport a pointed payload.

## Main definitions

* `point`: the integer address of a crossing, centered at its owner frame.
* `addressedSquareOfHierarchy`: an addressed square from the carrier and corner equations.

## Main results

* `addressedSquareOfHierarchy`: packages the crossing and wire step equations.
* `intervalEdge_pair_iff_horizontalCarrier`: canonical clear edges agree with carrier geometry.

## References

Ported from lean-wang revision `64268a3`,
`ShadedCarrierHierarchy` (lines 196–392),
`ShadedCarrierBorderIntervals` (lines 32–628) and `ShadedCarrierHierarchyAddressing`
(lines 28–511). `AddressedSquare` replaces the source's `SquareAddressing`; the carrier
arithmetic and wire-equation arguments closely follow the source.
-/

public section

namespace Cslib.WangTile.Robinson.Carrier

open Canonical

/-- A row's owner frame carries horizontally through every nonboundary column
inside that frame, including across complete nested frames. -/
@[expose] def isHorizontalCarrier (level x y : Nat) : Bool :=
  match depthAt (level - 1) y with
  | none => false
  | some depth => inFrame depth x && !onFrameBoundary depth x

/-- A column's owner frame carries vertically through every nonboundary row
inside that frame, including across complete nested frames. -/
@[expose] def isVerticalCarrier (level x y : Nat) : Bool :=
  match depthAt (level - 1) x with
  | none => false
  | some depth => inFrame depth y && !onFrameBoundary depth y

/-- Carrier role predicted by the nested frame hierarchy.  The corner marker
is deliberately erased to `.active`; marker placement is a separate centered
coordinate property. -/
@[expose] def carrierRole (level x y : Nat) : RouteRole :=
  match isHorizontalCarrier level x y, isVerticalCarrier level x y with
  | false, false => .inactive
  | true, false => .horizontal
  | false, true => .vertical
  | true, true => .active

@[simp] private theorem carrierRole_isHorizontalCarrier (level x y : Nat) :
    (carrierRole level x y).horizontalCarrier =
      isHorizontalCarrier level x y := by
  cases horizontal : isHorizontalCarrier level x y <;>
    cases vertical : isVerticalCarrier level x y <;>
    simp [carrierRole, horizontal, vertical, RouteRole.horizontalCarrier]

@[simp] private theorem carrierRole_isVerticalCarrier (level x y : Nat) :
    (carrierRole level x y).verticalCarrier =
      isVerticalCarrier level x y := by
  cases horizontal : isHorizontalCarrier level x y <;>
    cases vertical : isVerticalCarrier level x y <;>
    simp [carrierRole, horizontal, vertical, RouteRole.verticalCarrier]

/-- Coordinates that become logical vertices of their depth's carrier grid. -/
private def isFreeCoordinate (depth coordinate : Nat) : Bool :=
  depthAt depth coordinate == some depth &&
    !onFrameBoundary depth coordinate

private theorem isFreeCoordinate_eq_true_of_owner
    {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth)
    (interior : onFrameBoundary depth coordinate = false) :
    isFreeCoordinate depth coordinate = true := by
  simp [isFreeCoordinate, depthAt_self_of_depthAt_eq_some owner, interior]

private theorem depthAt_self_eq_some_of_isFreeCoordinate
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true) :
    depthAt depth coordinate = some depth :=
  (by simpa [isFreeCoordinate] using free : _ ∧ _).1

/-- At a mutual horizontal/vertical crossing, the row and column have the
same smallest owner depth. -/
private theorem ownerDepth_eq_of_mutual_containment
    {bound x y xDepth yDepth : Nat}
    (xOwner : depthAt bound x = some xDepth)
    (yOwner : depthAt bound y = some yDepth)
    (xInYFrame : inFrame yDepth x = true)
    (yInXFrame : inFrame xDepth y = true) : xDepth = yDepth := by
  exact Nat.le_antisymm (depthAt_le_of_inFrame xOwner (depthAt_pos yOwner) xInYFrame)
    (depthAt_le_of_inFrame yOwner (depthAt_pos xOwner) yInXFrame)

/-- Geometric center of the depth-`depth` frame containing a coordinate. -/
private def frameCenter (depth coordinate : Nat) : Nat :=
  coordinate - coordinate % period depth + (2 * scale depth + 1)

/-- Moving one physical cell inside a frame cannot cross its period boundary,
so both cells use the same centered logical origin. -/
private theorem frameCenter_succ_of_inFrame_not_boundary
    {depth coordinate : Nat} (inside : inFrame depth coordinate = true)
    (interior : onFrameBoundary depth coordinate = false) :
    frameCenter depth (coordinate + 1) = frameCenter depth coordinate := by
  have inside' := (inFrame_eq_true_iff _ _).mp inside
  have interior' := (onFrameBoundary_eq_false_iff _ _).mp interior
  have residueSuccLt : coordinate % period depth + 1 < period depth := by
    have endLt := frameEndResidue_lt_period depth
    omega
  have oneLt := one_lt_period depth
  have successorMod :
      (coordinate + 1) % period depth = coordinate % period depth + 1 := by
    calc
      (coordinate + 1) % period depth =
          (coordinate % period depth + 1 % period depth) % period depth := by
            rw [Nat.add_mod]
      _ = (coordinate % period depth + 1) % period depth := by
            rw [Nat.mod_eq_of_lt oneLt]
      _ = coordinate % period depth + 1 :=
            Nat.mod_eq_of_lt residueSuccLt
  have residueLe : coordinate % period depth ≤ coordinate := Nat.mod_le _ _
  simp only [frameCenter, successorMod]
  omega

private theorem frameCenter_eq_self_of_centerResidue
    {depth coordinate : Nat}
    (center : coordinate % period depth = 2 * scale depth + 1) :
    frameCenter depth coordinate = coordinate := by
  have := Nat.mod_le coordinate (period depth)
  simp only [frameCenter, center]; omega

/-- Logical vertex coordinate centered at the geometric frame center. -/
private def axisCoordinate (depth coordinate : Nat) : Int :=
  (Nat.count (isFreeCoordinate depth ·) coordinate : Int) -
    Nat.count (isFreeCoordinate depth ·) (frameCenter depth coordinate)

private theorem axisCoordinate_eq_zero_of_centerResidue
    {depth coordinate : Nat}
    (center : coordinate % period depth = 2 * scale depth + 1) :
    axisCoordinate depth coordinate = 0 := by
  rw [axisCoordinate, frameCenter_eq_self_of_centerResidue center]; omega

/-- Logical source immediately before the next step across a channel gap. -/
private def axisSource (depth coordinate : Nat) : Int :=
  (Nat.count (isFreeCoordinate depth ·) coordinate : Int) - 1 -
    Nat.count (isFreeCoordinate depth ·) (frameCenter depth coordinate)

private theorem axisCoordinate_succ_of_free
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisCoordinate depth (coordinate + 1) =
      axisCoordinate depth coordinate + 1 := by
  simp [axisCoordinate, Nat.count_succ, free, sameCenter]; omega

private theorem axisSource_succ_of_free
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisSource depth (coordinate + 1) =
      axisCoordinate depth coordinate := by
  simp [axisSource, axisCoordinate, Nat.count_succ, free, sameCenter]

private theorem axisSource_succ_of_not_free
    {depth coordinate : Nat} (notFree : isFreeCoordinate depth coordinate = false)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisSource depth (coordinate + 1) = axisSource depth coordinate := by
  simp [axisSource, Nat.count_succ, notFree, sameCenter]

private theorem axisCoordinate_succ_of_not_free
    {depth coordinate : Nat} (notFree : isFreeCoordinate depth coordinate = false)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisCoordinate depth (coordinate + 1) = axisSource depth coordinate + 1 := by
  simp [axisCoordinate, axisSource, Nat.count_succ, notFree, sameCenter]; omega

/-- Forget whether a crossing carries the distinguished corner marker. -/
@[expose] def eraseCorner : RouteRole → RouteRole
  | .corner => .active
  | role => role

/-- Logical crossing address predicted by the row and column owner frames. -/
def point (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) y, depthAt (level - 1) x with
  | some rowDepth, some columnDepth =>
      (axisCoordinate rowDepth x, axisCoordinate columnDepth y)
  | _, _ => (0, 0)

/-- Address held constant along a horizontal channel gap.  Boundary rows have
no crossings, so they may carry the arbitrary zero address. -/
private def horizontalSource (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) y with
  | none => (0, 0)
  | some depth =>
      if onFrameBoundary depth y then (0, 0)
      else (axisSource depth x, axisCoordinate depth y)

/-- Address held constant along a vertical channel gap. -/
private def verticalSource (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) x with
  | none => (0, 0)
  | some depth =>
      if onFrameBoundary depth x then (0, 0)
      else (axisCoordinate depth x, axisSource depth y)

private inductive AddressAxis where
  | horizontal
  | vertical

private def orientedNat : AddressAxis → Nat → Nat → Nat × Nat
  | .horizontal, along, transverse => (along, transverse)
  | .vertical, along, transverse => (transverse, along)

private def orientedInt : AddressAxis → Int → Int → Int × Int
  | .horizontal, along, transverse => (along, transverse)
  | .vertical, along, transverse => (transverse, along)

private def primaryCarrier (axis : AddressAxis) (level along transverse : Nat) : Bool :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => isHorizontalCarrier level p.1 p.2
  | .vertical => isVerticalCarrier level p.1 p.2

private def crossingCarrier (axis : AddressAxis) (level along transverse : Nat) : Bool :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => isVerticalCarrier level p.1 p.2
  | .vertical => isHorizontalCarrier level p.1 p.2

private def pointAt (axis : AddressAxis) (level along transverse : Nat) : Int × Int :=
  let p := orientedNat axis along transverse
  point level p.1 p.2

private def sourceAt (axis : AddressAxis) (level along transverse : Nat) : Int × Int :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => horizontalSource level p.1 p.2
  | .vertical => verticalSource level p.1 p.2

private def roleAt (axis : AddressAxis) (level along transverse : Nat) : RouteRole :=
  let p := orientedNat axis along transverse
  carrierRole level p.1 p.2

private def primaryRole : AddressAxis → RouteRole
  | .horizontal => .horizontal
  | .vertical => .vertical

private def roleIsPrimaryCarrier : AddressAxis → RouteRole → Bool
  | .horizontal => RouteRole.horizontalCarrier
  | .vertical => RouteRole.verticalCarrier

@[simp] private theorem roleAt_isPrimaryCarrier (axis : AddressAxis)
    (level along transverse : Nat) :
    roleIsPrimaryCarrier axis (roleAt axis level along transverse) =
      primaryCarrier axis level along transverse := by
  cases axis <;>
    simp [roleIsPrimaryCarrier, roleAt, primaryCarrier, orientedNat]

@[simp] private theorem eraseCorner_isPrimaryCarrier
    (axis : AddressAxis) (role : RouteRole) :
    roleIsPrimaryCarrier axis (eraseCorner role) =
      roleIsPrimaryCarrier axis role := by
  cases axis <;> cases role <;> rfl

private theorem primaryCarrier_iff_of_owner
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    primaryCarrier axis level along transverse = true ↔
      inFrame depth along = true ∧ onFrameBoundary depth along = false := by
  cases axis <;>
    simp [primaryCarrier, orientedNat, isHorizontalCarrier,
      isVerticalCarrier, owner]

private theorem crossingCarrier_iff_of_owner
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) along = some depth) :
    crossingCarrier axis level along transverse = true ↔
      inFrame depth transverse = true ∧
        onFrameBoundary depth transverse = false := by
  cases axis <;>
    simp [crossingCarrier, orientedNat, isHorizontalCarrier,
      isVerticalCarrier, owner]

private theorem alongOwner_eq_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    depthAt (level - 1) along = some depth := by
  have alongInFrame := (primaryCarrier_iff_of_owner axis owner).1 primary
  cases alongOwner : depthAt (level - 1) along with
  | none =>
      cases axis <;>
        simp [crossingCarrier, orientedNat, isHorizontalCarrier,
          isVerticalCarrier, alongOwner] at crossing
  | some alongDepth =>
      have transverseInFrame :=
        (crossingCarrier_iff_of_owner axis alongOwner).1 crossing
      have sameDepth := ownerDepth_eq_of_mutual_containment
        alongOwner owner alongInFrame.1 transverseInFrame.1
      simp [sameDepth]

private theorem free_eq_true_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    isFreeCoordinate depth along = true := by
  have alongData := (primaryCarrier_iff_of_owner axis owner).1 primary
  exact isFreeCoordinate_eq_true_of_owner
    (alongOwner_eq_of_mutual_carriers axis owner primary crossing)
    alongData.2

private theorem free_eq_false_of_not_crossing
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseInterior : onFrameBoundary depth transverse = false)
    (crossing : crossingCarrier axis level along transverse = false) :
    isFreeCoordinate depth along = false := by
  cases free : isFreeCoordinate depth along with
  | false => rfl
  | true =>
      have alongOwner := depthAt_eq_some_mono
        (depthAt_self_eq_some_of_isFreeCoordinate free)
        (depthAt_le owner)
      have transverseInside := inFrame_eq_true_of_depthAt_eq_some owner
      have : crossingCarrier axis level along transverse = true :=
        (crossingCarrier_iff_of_owner axis alongOwner).2
          ⟨transverseInside, transverseInterior⟩
      simp [this] at crossing

private theorem pointAt_eq_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    pointAt axis level along transverse =
      orientedInt axis (axisCoordinate depth along)
        (axisCoordinate depth transverse) := by
  have alongOwner := alongOwner_eq_of_mutual_carriers
    axis owner primary crossing
  cases axis <;>
    simp [pointAt, orientedNat, orientedInt, point, owner, alongOwner]

private theorem transverseInterior_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    onFrameBoundary depth transverse = false := by
  have alongOwner := alongOwner_eq_of_mutual_carriers
    axis owner primary crossing
  exact ((crossingCarrier_iff_of_owner axis alongOwner).1 crossing).2

private theorem sourceAt_eq_of_transverseInterior
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseInterior : onFrameBoundary depth transverse = false) :
    sourceAt axis level along transverse =
      orientedInt axis (axisSource depth along)
        (axisCoordinate depth transverse) := by
  cases axis <;>
    simp [sourceAt, orientedNat, orientedInt, horizontalSource,
      verticalSource, owner, transverseInterior]

private theorem sourceAt_eq_zero_of_transverseBoundary
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseBoundary : onFrameBoundary depth transverse = true) :
    sourceAt axis level along transverse = (0, 0) := by
  cases axis <;>
    simp [sourceAt, orientedNat, horizontalSource, verticalSource,
      owner, transverseBoundary]

private theorem roleAt_eq_of_primary
    (axis : AddressAxis) {level along transverse : Nat}
    (primary : primaryCarrier axis level along transverse = true) :
    roleAt axis level along transverse =
      if crossingCarrier axis level along transverse = true then .active
      else primaryRole axis := by
  cases crossing : crossingCarrier axis level along transverse <;> cases axis
  all_goals
    simp only [primaryCarrier, roleAt, crossingCarrier, primaryRole, orientedNat]
      at primary crossing ⊢
    simp [carrierRole, primary, crossing]

/-- A crossing at the centers of both owner frames has logical address zero. -/
theorem point_eq_zero_of_centerResidues
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (columnOwner : depthAt (level - 1) x = some depth)
    (xCenter : x % period depth = 2 * scale depth + 1)
    (yCenter : y % period depth = 2 * scale depth + 1) :
    point level x y = (0, 0) := by
  simp [point, rowOwner, columnOwner,
    axisCoordinate_eq_zero_of_centerResidue xCenter,
    axisCoordinate_eq_zero_of_centerResidue yCenter]

private def axisSuccessor : AddressAxis → Int × Int → Int × Int
  | .horizontal => fun p => (p.1 + 1, p.2)
  | .vertical => fun p => (p.1, p.2 + 1)

private def axisOutgoing : AddressAxis → RouteRole →
    Int × Int → Int × Int → Int × Int
  | .horizontal => RouteRole.horizontalOutgoing
  | .vertical => RouteRole.verticalOutgoing

private def AxisStepAt (axis : AddressAxis) (level along transverse : Nat)
    (firstRole secondRole : RouteRole) : Prop :=
  let outgoing := axisOutgoing axis firstRole
    (pointAt axis level along transverse)
    (sourceAt axis level along transverse)
  match secondRole with
  | .active | .corner =>
      pointAt axis level (along + 1) transverse = axisSuccessor axis outgoing
  | .horizontal =>
      match axis with
      | .horizontal => sourceAt axis level (along + 1) transverse = outgoing
      | .vertical => False
  | .vertical =>
      match axis with
      | .horizontal => False
      | .vertical => sourceAt axis level (along + 1) transverse = outgoing
  | .inactive => False

@[simp] private theorem axisOutgoing_active (axis : AddressAxis)
    (point source : Int × Int) :
    axisOutgoing axis .active point source = point := by
  cases axis <;> rfl

@[simp] private theorem axisOutgoing_primary (axis : AddressAxis)
    (point source : Int × Int) :
    axisOutgoing axis (primaryRole axis) point source = source := by
  cases axis <;> rfl

@[simp] private theorem axisStepAt_active (axis : AddressAxis)
    (level along transverse : Nat) (firstRole : RouteRole) :
    AxisStepAt axis level along transverse firstRole .active ↔
      pointAt axis level (along + 1) transverse =
        axisSuccessor axis
          (axisOutgoing axis firstRole
            (pointAt axis level along transverse)
            (sourceAt axis level along transverse)) := by
  cases axis <;> rfl

@[simp] private theorem axisStepAt_primary (axis : AddressAxis)
    (level along transverse : Nat) (firstRole : RouteRole) :
    AxisStepAt axis level along transverse firstRole (primaryRole axis) ↔
      sourceAt axis level (along + 1) transverse =
        axisOutgoing axis firstRole
          (pointAt axis level along transverse)
          (sourceAt axis level along transverse) := by
  cases axis <;> rfl

@[simp] private theorem axisSuccessor_oriented (axis : AddressAxis)
    (along transverse : Int) :
    axisSuccessor axis (orientedInt axis along transverse) =
      orientedInt axis (along + 1) transverse := by
  cases axis <;> rfl

private theorem axis_step (axis : AddressAxis) (level along transverse : Nat)
    (firstPrimary : primaryCarrier axis level along transverse = true)
    (secondPrimary :
      primaryCarrier axis level (along + 1) transverse = true) :
    AxisStepAt axis level along transverse
      (roleAt axis level along transverse)
      (roleAt axis level (along + 1) transverse) := by
  cases owner : depthAt (level - 1) transverse with
  | none =>
      cases axis <;>
        simp [primaryCarrier, orientedNat, isHorizontalCarrier,
          isVerticalCarrier, owner] at firstPrimary
  | some depth =>
      have firstData := (primaryCarrier_iff_of_owner axis owner).1 firstPrimary
      have sameCenter := frameCenter_succ_of_inFrame_not_boundary firstData.1 firstData.2
      rw [roleAt_eq_of_primary axis firstPrimary, roleAt_eq_of_primary axis secondPrimary]
      cases transverseBoundary : onFrameBoundary depth transverse with
      | true =>
          have firstCrossing : crossingCarrier axis level along transverse = false :=
            Bool.eq_false_iff.2 fun crossing => by
              simpa [transverseBoundary] using
                transverseInterior_of_mutual_carriers axis owner firstPrimary crossing
          have secondCrossing : crossingCarrier axis level (along + 1) transverse = false :=
            Bool.eq_false_iff.2 fun crossing => by
              simpa [transverseBoundary] using
                transverseInterior_of_mutual_carriers axis owner secondPrimary crossing
          simp only [firstCrossing, secondCrossing, Bool.false_eq_true, ↓reduceIte]
          rw [axisStepAt_primary, axisOutgoing_primary,
            sourceAt_eq_zero_of_transverseBoundary axis owner transverseBoundary,
            sourceAt_eq_zero_of_transverseBoundary axis owner transverseBoundary]
      | false =>
          cases firstCrossing : crossingCarrier axis level along transverse with
          | false =>
              have firstFree := free_eq_false_of_not_crossing
                axis owner transverseBoundary firstCrossing
              have firstSource := sourceAt_eq_of_transverseInterior
                (along := along) axis owner transverseBoundary
              cases secondCrossing :
                  crossingCarrier axis level (along + 1) transverse with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [axisStepAt_primary, axisOutgoing_primary, firstSource,
                    sourceAt_eq_of_transverseInterior (along := along + 1) axis owner
                      transverseBoundary,
                    axisSource_succ_of_not_free firstFree sameCenter]
              | true =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [axisStepAt_active, axisOutgoing_primary, firstSource,
                    pointAt_eq_of_mutual_carriers axis owner secondPrimary secondCrossing,
                    axisSuccessor_oriented, axisCoordinate_succ_of_not_free firstFree sameCenter]
          | true =>
              have firstFree := free_eq_true_of_mutual_carriers
                axis owner firstPrimary firstCrossing
              have firstPoint := pointAt_eq_of_mutual_carriers
                axis owner firstPrimary firstCrossing
              cases secondCrossing :
                  crossingCarrier axis level (along + 1) transverse with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [axisStepAt_primary, axisOutgoing_active, firstPoint,
                    sourceAt_eq_of_transverseInterior (along := along + 1) axis owner
                      transverseBoundary,
                    axisSource_succ_of_free firstFree sameCenter]
              | true =>
                  simp only [↓reduceIte]
                  rw [axisStepAt_active, axisOutgoing_active, firstPoint,
                    pointAt_eq_of_mutual_carriers axis owner secondPrimary secondCrossing,
                    axisSuccessor_oriented, axisCoordinate_succ_of_free firstFree sameCenter]

/-- Replacing an active hierarchy role by the corner marker preserves the
axis-neutral addressing step. -/
private theorem axis_step_of_erased_roles
    (axis : AddressAxis) (level along transverse : Nat)
    (firstRole secondRole : RouteRole)
    (firstRoleEq : eraseCorner firstRole = roleAt axis level along transverse)
    (secondRoleEq : eraseCorner secondRole =
      roleAt axis level (along + 1) transverse)
    (firstCarrier : roleIsPrimaryCarrier axis firstRole = true)
    (secondCarrier : roleIsPrimaryCarrier axis secondRole = true) :
    AxisStepAt axis level along transverse firstRole secondRole := by
  have firstPrimary : primaryCarrier axis level along transverse = true := by
    rwa [← roleAt_isPrimaryCarrier, ← firstRoleEq, eraseCorner_isPrimaryCarrier]
  have secondPrimary : primaryCarrier axis level (along + 1) transverse = true := by
    rwa [← roleAt_isPrimaryCarrier, ← secondRoleEq, eraseCorner_isPrimaryCarrier]
  have step := axis_step axis level along transverse firstPrimary secondPrimary
  rw [← firstRoleEq, ← secondRoleEq] at step
  cases axis <;> cases firstRole <;> cases secondRole <;>
    simp only [roleIsPrimaryCarrier, RouteRole.horizontalCarrier,
      RouteRole.verticalCarrier] at firstCarrier secondCarrier <;>
    simp only [eraseCorner, AxisStepAt, axisOutgoing, pointAt, sourceAt,
      orientedNat, axisSuccessor] at step ⊢ <;>
    exact step

/-- Turn a concrete square whose roles follow the hierarchy into an addressed
carrier square.  The concrete substitution proof only has to supply role
recognition and centered corner markers. -/
def addressedSquareOfHierarchy
    {S : RoutedScaffold} {n level : Nat}
    (base : Rectangle S.tiles (n + 1) (n + 1))
    (roleEq : ∀ i j,
      eraseCorner (S.role (base.tile i j)) = carrierRole level i.val j.val)
    (cornerZero : ∀ i j, S.role (base.tile i j) = .corner →
      point level i.val j.val = (0, 0)) :
    AddressedSquare S n where
  base := base
  point := fun i j => point level i.val j.val
  horizontalSource := fun i j => horizontalSource level i.val j.val
  verticalSource := fun i j => verticalSource level i.val j.val
  corner_zero := cornerZero
  hstep := by
    intro i j hi leftCarrier rightCarrier
    have step := axis_step_of_erased_roles .horizontal level i.val j.val
      (S.role (base.tile i j))
      (S.role (base.tile ⟨i.val + 1, hi⟩ j))
      (roleEq i j) (roleEq ⟨i.val + 1, hi⟩ j)
      leftCarrier rightCarrier
    cases rightRole : S.role (base.tile ⟨i.val + 1, hi⟩ j) <;>
      simp only [rightRole, RouteRole.horizontalCarrier, Bool.false_eq_true] at rightCarrier <;>
      simpa only [AxisStepAt, axisOutgoing, pointAt,
        sourceAt, orientedNat, axisSuccessor, rightRole, Fin.val_mk] using step
  vstep := by
    intro i j hj lowerCarrier upperCarrier
    have step := axis_step_of_erased_roles .vertical level j.val i.val
      (S.role (base.tile i j))
      (S.role (base.tile i ⟨j.val + 1, hj⟩))
      (roleEq i j) (roleEq i ⟨j.val + 1, hj⟩)
      lowerCarrier upperCarrier
    cases upperRole : S.role (base.tile i ⟨j.val + 1, hj⟩) <;>
      simp only [upperRole, RouteRole.verticalCarrier, Bool.false_eq_true] at upperCarrier <;>
      simpa only [AxisStepAt, axisOutgoing, pointAt,
        sourceAt, orientedNat, axisSuccessor, upperRole, Fin.val_mk] using step

/-- Addressing a square preserves its underlying matching patch. -/
@[simp] theorem addressedSquareOfHierarchy_base
    {S : RoutedScaffold} {n level : Nat}
    (base : Rectangle S.tiles (n + 1) (n + 1))
    (roleEq : ∀ i j,
      eraseCorner (S.role (base.tile i j)) = carrierRole level i.val j.val)
    (cornerZero : ∀ i j, S.role (base.tile i j) = .corner →
      point level i.val j.val = (0, 0)) :
    (addressedSquareOfHierarchy base roleEq cornerZero).base = base := by rfl

/-- A selected closing border is exactly a closing boundary of one of the
contributing frame depths.  The outer border contributes only an opening. -/
private theorem selectedBorder_eq_some_false_iff
    (level coordinate transverse : Nat) :
    selectedBorder level coordinate transverse = some false ↔
      ∃ depth, 1 ≤ depth ∧ depth ≤ level ∧
        inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  rw [selectedBorder_eq_some_iff]
  simp [outerBorder, frameBorder_eq_some_false_iff]

/-- Once the smallest frame containing the transverse coordinate is known,
every selected frame boundary comes from that depth or a larger one. -/
private theorem selectedBorder_eq_some_iff_of_owner
    {level ownerDepth coordinate transverse : Nat} {orientation : Bool}
    (owner : depthAt (level - 1) transverse = some ownerDepth) :
    selectedBorder level coordinate transverse = some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, ownerDepth ≤ depth ∧ depth ≤ level ∧
          frameBorder depth coordinate transverse = some orientation := by
  rw [selectedBorder_eq_some_iff]
  refine or_congr_right ⟨fun ⟨depth, pos, hle, hb⟩ => ⟨depth, ?_, hle, hb⟩,
    fun ⟨depth, hle, hb, hbor⟩ => ⟨depth, (depthAt_pos owner).trans_le hle, hb, hbor⟩⟩
  refine depthAt_le_of_inFrame owner pos ?_
  cases orientation
  · exact ((frameBorder_eq_some_false_iff _ _ _).1 hb).1
  · exact ((frameBorder_eq_some_true_iff _ _ _).1 hb).1

/-- Closing-border normal form relative to the smallest containing frame. -/
private theorem selectedBorder_eq_some_false_iff_of_owner
    {level ownerDepth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some ownerDepth) :
    selectedBorder level coordinate transverse = some false ↔
      ∃ depth, ownerDepth ≤ depth ∧ depth ≤ level ∧
        inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  rw [selectedBorder_eq_some_iff_of_owner owner]
  simp [outerBorder, frameBorder_eq_some_false_iff]

/-- No selected boundary of any enclosing frame enters the strict interior of
the smallest frame owning the transverse coordinate. -/
private theorem selectedBorder_eq_none_of_owner_interior
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (inside : inFrame depth coordinate = true)
    (interior : onFrameBoundary depth coordinate = false) :
    selectedBorder level coordinate transverse = none := by
  cases borderEq : selectedBorder level coordinate transverse with
  | none => rfl
  | some orientation =>
      have insideData := (inFrame_eq_true_iff _ _).mp inside
      have startLarge : 1 < frameStartResidue depth := by
        simp [frameStartResidue, scale_pos]
      rcases (selectedBorder_eq_some_iff_of_owner owner).1 borderEq with
        outer | ⟨frameDepth, depthLeFrame, _, frame⟩
      · have coordinateMod : coordinate % period depth = 1 := by
          rw [((outerBorder_eq_some_iff _ _ _).mp outer).1, Nat.mod_eq_of_lt (one_lt_period depth)]
        omega
      · rcases depthLeFrame.eq_or_lt with rfl | less
        · cases orientation
          · simp [onFrameBoundary, ((frameBorder_eq_some_false_iff _ _ _).1 frame).2] at interior
          · simp [onFrameBoundary, ((frameBorder_eq_some_true_iff _ _ _).1 frame).2] at interior
        · have largeResidue : coordinate % period depth = 0 ∨ coordinate % period depth = 1 := by
            cases orientation
            · exact Or.inl (largeClosing_mod_small less
                ((frameBorder_eq_some_false_iff _ _ _).1 frame).2)
            · exact Or.inr (largeOpening_mod_small less
                ((frameBorder_eq_some_true_iff _ _ _).1 frame).2)
          rcases largeResidue with zero | one <;> omega

/-- Start of the frame-period block containing `coordinate`. -/
private def frameBase (depth coordinate : Nat) : Nat :=
  period depth * (coordinate / period depth)

private def frameOpening (depth coordinate : Nat) : Nat :=
  frameBase depth coordinate + frameStartResidue depth

private def frameClosing (depth coordinate : Nat) : Nat :=
  frameBase depth coordinate + frameEndResidue depth

private theorem coordinate_lt_frameBase_add_period (depth coordinate : Nat) :
    coordinate < frameBase depth coordinate + period depth := by
  have decomposition : frameBase depth coordinate + coordinate % period depth = coordinate :=
    Nat.div_add_mod coordinate (period depth)
  have periodPositive := lt_trans Nat.zero_lt_one (one_lt_period depth)
  have residueLt := Nat.mod_lt coordinate periodPositive
  omega

private theorem mod_eq_sub_frameBase_of_mem_block
    {depth reference coordinate : Nat}
    (lower : frameBase depth reference ≤ coordinate)
    (upper : coordinate < frameBase depth reference + period depth) :
    coordinate % period depth = coordinate - frameBase depth reference := by
  let base := frameBase depth reference
  have offsetLt : coordinate - base < period depth := by
    omega
  have baseMod : base % period depth = 0 := by
    simp [base, frameBase]
  calc
    coordinate % period depth =
        (base + (coordinate - base)) % period depth := by
      rw [Nat.add_sub_of_le lower]
    _ = (base % period depth +
        (coordinate - base) % period depth) % period depth := by
      rw [Nat.add_mod]
    _ = coordinate - base := by
      rw [baseMod, Nat.mod_eq_of_lt offsetLt]
      simp [Nat.mod_eq_of_lt offsetLt]

private theorem frameOpening_mod (depth coordinate : Nat) :
    frameOpening depth coordinate % period depth = frameStartResidue depth := by
  have startLt : frameStartResidue depth < period depth :=
    (frameStartResidue_lt_frameEndResidue depth).trans
      (frameEndResidue_lt_period depth)
  simp [frameOpening, frameBase, Nat.add_mod, Nat.mod_eq_of_lt startLt]

private theorem frameClosing_mod (depth coordinate : Nat) :
    frameClosing depth coordinate % period depth = frameEndResidue depth := by
  simp [frameClosing, frameBase, Nat.add_mod,
    Nat.mod_eq_of_lt (frameEndResidue_lt_period depth)]

private theorem frameOpening_lt_frameClosing (depth coordinate : Nat) :
    frameOpening depth coordinate < frameClosing depth coordinate := by
  simp only [frameOpening, frameClosing]
  exact Nat.add_lt_add_left
    (frameStartResidue_lt_frameEndResidue depth) _

private theorem between_frameBounds
    {depth coordinate position : Nat}
    (afterOpening : frameOpening depth coordinate < position)
    (beforeClosing : position < frameClosing depth coordinate) :
    inFrame depth position = true ∧ onFrameBoundary depth position = false := by
  let base := frameBase depth coordinate
  simp only [frameOpening, frameClosing] at afterOpening beforeClosing
  have endLt := frameEndResidue_lt_period depth
  have positionMod : position % period depth = position - base :=
    mod_eq_sub_frameBase_of_mem_block (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · simp [inFrame, positionMod]; omega
  · simp [onFrameBoundary, positionMod]; omega

private theorem selectedBorder_frameOpening
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    selectedBorder level (frameOpening depth coordinate) transverse = some true :=
  (selectedBorder_eq_some_iff _ _ _ _).2 <| Or.inr ⟨depth, depthAt_pos owner,
    by have := depthAt_le owner; omega,
    (frameBorder_eq_some_true_iff _ _ _).2
      ⟨inFrame_eq_true_of_depthAt_eq_some owner, frameOpening_mod depth coordinate⟩⟩

private theorem selectedBorder_frameClosing
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    selectedBorder level (frameClosing depth coordinate) transverse = some false :=
  (selectedBorder_eq_some_iff _ _ _ _).2 <| Or.inr ⟨depth, depthAt_pos owner,
    by have := depthAt_le owner; omega,
    (frameBorder_eq_some_false_iff _ _ _).2
      ⟨inFrame_eq_true_of_depthAt_eq_some owner, frameClosing_mod depth coordinate⟩⟩

private theorem selectedBorder_none_between_frameBounds
    {level depth coordinate transverse position : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (afterOpening : frameOpening depth coordinate < position)
    (beforeClosing : position < frameClosing depth coordinate) :
    selectedBorder level position transverse = none := by
  have geometry := between_frameBounds afterOpening beforeClosing
  exact selectedBorder_eq_none_of_owner_interior owner geometry.1 geometry.2

/-- A clear canonical edge lies strictly between a witnessed opening and
closing border when no closing intervenes before the opening and no border
intervenes after the closing. -/
private theorem between_borders_of_intervalEdge_eq_none
    {interior : Nat → Option Bool} {opening closing position length : Nat}
    (clear : Canonical.intervalEdge interior length position = .none)
    (positionClear : interior position = none)
    (openingBorder : interior opening = some true)
    (closingBorder : interior closing = some false)
    (openingBeforeClosing : opening < closing)
    (closingBeforeEnd : closing < length)
    (noClosingBeforeOpening : ∀ candidate, position ≤ candidate →
      candidate < opening → interior candidate ≠ some false)
    (noBorderAfterClosing : ∀ candidate, closing < candidate →
      candidate < position → interior candidate = none) :
    opening < position ∧ position < closing := by
  have edgeData := (Canonical.intervalEdge_eq_none_iff
    interior length position).1 clear
  constructor
  · rcases Nat.lt_trichotomy position opening with before | rfl | after
    · rw [Canonical.nextInterior_eq_of_no_opposite_before openingBorder
        noClosingBeforeOpening before.le (openingBeforeClosing.trans closingBeforeEnd)] at edgeData
      simp at edgeData
    · exact absurd (positionClear.symm.trans openingBorder) nofun
    · exact after
  · rcases Nat.lt_trichotomy position closing with before | rfl | after
    · exact before
    · exact absurd (positionClear.symm.trans closingBorder) nofun
    · exact (edgeData.2 (Canonical.previousInterior_eq_of_none_between
        closingBorder noBorderAfterClosing after)).elim

private theorem selectedBorder_ne_some_false_before_frameOpening
    {level depth coordinate transverse candidate : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (coordinateClear : selectedBorder level coordinate transverse = none)
    (lower : coordinate ≤ candidate)
    (beforeOpening : candidate < frameOpening depth coordinate) :
    selectedBorder level candidate transverse ≠ some false := by
  intro selected
  rcases (selectedBorder_eq_some_false_iff_of_owner owner).1 selected with
    ⟨frameDepth, depthLeFrame, _, _, closing⟩
  have baseLe : frameBase depth coordinate ≤ candidate :=
      (Nat.mul_div_le coordinate (period depth)).trans lower
  have openingBeforeBlockEnd : frameOpening depth coordinate <
        frameBase depth coordinate + period depth := by
      simp only [frameOpening]
      exact Nat.add_lt_add_left
        ((frameStartResidue_lt_frameEndResidue depth).trans
          (frameEndResidue_lt_period depth)) _
  have candidateMod : candidate % period depth =
        candidate - frameBase depth coordinate :=
      mod_eq_sub_frameBase_of_mem_block baseLe
        (beforeOpening.trans openingBeforeBlockEnd)
  rcases depthLeFrame.eq_or_lt with equal | larger
  · subst frameDepth
    have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth
    simp only [frameOpening] at beforeOpening
    omega
  · have largeResidue : candidate % period depth = 0 :=
      largeClosing_mod_small larger closing
    have coordinateBaseLe : frameBase depth coordinate ≤ coordinate :=
      Nat.mul_div_le coordinate (period depth)
    rw [show candidate = coordinate by omega, coordinateClear] at selected
    cases selected

private theorem selectedBorder_eq_none_after_frameClosing
    {level depth coordinate transverse candidate : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (afterClosing : frameClosing depth coordinate < candidate)
    (beforeCoordinate : candidate < coordinate) :
    selectedBorder level candidate transverse = none := by
  cases selected : selectedBorder level candidate transverse with
  | none => rfl
  | some orientation =>
      rcases (selectedBorder_eq_some_iff_of_owner owner).1 selected with
        outer | frame
      · have candidateOne := ((outerBorder_eq_some_iff _ _ _).mp outer).1
        have closingLarge : 1 < frameClosing depth coordinate := by
          simp only [frameClosing, frameEndResidue]
          have := scale_pos depth
          omega
        omega
      · rcases frame with ⟨frameDepth, depthLeFrame, _, border⟩
        have baseLe : frameBase depth coordinate ≤ candidate := by
          simp only [frameClosing] at afterClosing; omega
        have candidateMod : candidate % period depth = candidate - frameBase depth coordinate :=
          mod_eq_sub_frameBase_of_mem_block baseLe
            (beforeCoordinate.trans (coordinate_lt_frameBase_add_period depth coordinate))
        have afterEnd : frameEndResidue depth < candidate % period depth := by
          simp only [frameClosing] at afterClosing; omega
        have endLarge : 1 < frameEndResidue depth := by
          have := scale_pos depth
          simp only [frameEndResidue]; omega
        have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth
        rcases depthLeFrame.eq_or_lt with rfl | larger
        · cases orientation
          · have := ((frameBorder_eq_some_false_iff _ _ _).1 border).2
            omega
          · have := ((frameBorder_eq_some_true_iff _ _ _).1 border).2
            omega
        · cases orientation
          · have := largeClosing_mod_small larger ((frameBorder_eq_some_false_iff _ _ _).1 border).2
            omega
          · have := largeOpening_mod_small larger ((frameBorder_eq_some_true_iff _ _ _).1 border).2
            omega

private theorem selectedBorder_ne_some_false_of_no_owner
    {level coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = none)
    (coordinate_lt : coordinate < 2 * scale level) :
    selectedBorder level coordinate transverse ≠ some false := by
  intro selected
  rcases (selectedBorder_eq_some_false_iff level coordinate transverse).1
      selected with ⟨depth, positive, bounded, inside, closing⟩
  by_cases withinSearch : depth ≤ level - 1
  · have outside := inFrame_eq_false_of_depthAt_eq_none owner
      positive withinSearch
    simp [inside] at outside
  · have depthEq : depth = level := by omega
    subst depth
    have residueLe := Nat.mod_le coordinate (period level)
    rw [closing] at residueLe
    simp only [frameEndResidue] at residueLe
    have := scale_pos level
    omega

private theorem period_dvd_two_mul_scale {depth level : Nat} (hdepth : depth < level) :
    period depth ∣ 2 * scale level :=
  dvd_mul_of_dvd_right (period_dvd_scale_of_lt hdepth) 2

private theorem frameClosing_lt_two_mul_scale
    {depth level coordinate : Nat} (hdepth : depth < level)
    (coordinate_lt : coordinate < 2 * scale level) :
    frameClosing depth coordinate < 2 * scale level := by
  have periodPositive := lt_trans Nat.zero_lt_one (one_lt_period depth)
  have lengthDvd := period_dvd_two_mul_scale hdepth
  have quotientLt : coordinate / period depth <
      (2 * scale level) / period depth := by
    apply (Nat.div_lt_iff_lt_mul periodPositive).2
    rw [Nat.mul_comm, Nat.mul_div_cancel' lengthDvd]
    exact coordinate_lt
  have nextBlockLe : period depth * (coordinate / period depth + 1) ≤
      2 * scale level := by
    have multiplied := Nat.mul_le_mul_left (period depth)
      (Nat.succ_le_iff.2 quotientLt)
    rw [Nat.mul_div_cancel' lengthDvd] at multiplied
    exact multiplied
  have closingBeforeNext : frameClosing depth coordinate <
      period depth * (coordinate / period depth + 1) := by
    have endLt := frameEndResidue_lt_period depth
    simpa [frameClosing, frameBase, Nat.mul_add] using
      Nat.add_lt_add_left endLt (period depth * (coordinate / period depth))
  exact closingBeforeNext.trans_le nextBlockLe

/-- Every arithmetic horizontal carrier cell has clear canonical signal on
both horizontal edges for the actual selected-border sequence. -/
private theorem intervalEdge_pair_of_horizontalCarrier
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < 2 * scale level)
    (carrier : isHorizontalCarrier level coordinate transverse = true) :
    Canonical.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) coordinate = .none ∧
      Canonical.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) (coordinate + 1) = .none := by
  cases owner : depthAt (level - 1) transverse with
  | none => simp [isHorizontalCarrier, owner] at carrier
  | some depth =>
      have carrierData : inFrame depth coordinate = true ∧
          onFrameBoundary depth coordinate = false := by
        simpa [isHorizontalCarrier, owner] using carrier
      have insideData := (inFrame_eq_true_iff _ _).mp carrierData.1
      have interiorData := (onFrameBoundary_eq_false_iff _ _).mp carrierData.2
      have decomposition := Nat.div_add_mod coordinate (period depth)
      have openingBefore : frameOpening depth coordinate < coordinate := by
        unfold frameOpening frameBase
        omega
      have beforeClosing : coordinate < frameClosing depth coordinate := by
        unfold frameClosing frameBase
        omega
      have depth_lt_level : depth < level := by
        have := depthAt_le owner
        have := depthAt_pos owner
        omega
      have closingBeforeEnd := frameClosing_lt_two_mul_scale depth_lt_level coordinate_lt
      have noBorder := fun candidate (after : frameOpening depth coordinate < candidate)
          (before : candidate < frameClosing depth coordinate) =>
        selectedBorder_none_between_frameBounds owner after before
      exact ⟨Canonical.intervalEdge_eq_none_of_between_borders
          (selectedBorder_frameOpening owner) (selectedBorder_frameClosing owner)
          noBorder openingBefore (by omega) closingBeforeEnd,
        Canonical.intervalEdge_eq_none_of_between_borders
          (selectedBorder_frameOpening owner) (selectedBorder_frameClosing owner)
          noBorder (by omega) (by omega) closingBeforeEnd⟩

/-- Conversely, the canonical signal can be clear on both sides of a cell only
inside the smallest frame owning its row. -/
private theorem horizontalCarrier_of_intervalEdge_pair
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < 2 * scale level)
    (clear :
      Canonical.intervalEdge
            (fun x => selectedBorder level x transverse)
            (2 * scale level) coordinate = .none ∧
        Canonical.intervalEdge
            (fun x => selectedBorder level x transverse)
            (2 * scale level) (coordinate + 1) = .none) :
    isHorizontalCarrier level coordinate transverse = true := by
  let interior := fun x => selectedBorder level x transverse
  have coordinateClear : interior coordinate = none :=
    Canonical.interior_eq_none_of_adjacent_clear
      interior coordinate_lt clear.1 clear.2
  have coordinateClear' : selectedBorder level coordinate transverse = none := by
    simpa [interior] using coordinateClear
  have edgeData := (Canonical.intervalEdge_eq_none_iff
    interior (2 * scale level) coordinate).1 clear.1
  cases owner : depthAt (level - 1) transverse with
  | none =>
      obtain ⟨candidate, lower, upper, selected⟩ :=
        Canonical.exists_interior_of_nextInterior_eq_some edgeData.1
      have candidate_lt : candidate < 2 * scale level := by
        have coordinateLe : coordinate ≤ 2 * scale level := coordinate_lt.le
        simpa [Nat.add_sub_of_le coordinateLe] using upper
      exact (selectedBorder_ne_some_false_of_no_owner owner candidate_lt
        selected).elim
  | some depth =>
      have depth_lt_level : depth < level := by
        have := depthAt_le owner
        have := depthAt_pos owner
        omega
      have closingBeforeEnd := frameClosing_lt_two_mul_scale
        depth_lt_level coordinate_lt
      have openingBorder := selectedBorder_frameOpening
        (level := level) (coordinate := coordinate) owner
      have closingBorder := selectedBorder_frameClosing
        (level := level) (coordinate := coordinate) owner
      have bounds := between_borders_of_intervalEdge_eq_none
        clear.1 coordinateClear
        (by simpa [interior] using openingBorder)
        (by simpa [interior] using closingBorder)
        (frameOpening_lt_frameClosing depth coordinate) closingBeforeEnd
        (fun candidate lower before =>
          selectedBorder_ne_some_false_before_frameOpening owner
            coordinateClear' lower before)
        (fun candidate after before =>
          selectedBorder_eq_none_after_frameClosing owner after before)
      have geometry := between_frameBounds bounds.1 bounds.2
      simpa [isHorizontalCarrier, owner] using geometry

/-- Both canonical signal edges are clear exactly on an arithmetic horizontal carrier. -/
theorem intervalEdge_pair_iff_horizontalCarrier
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < side level) :
    (Canonical.intervalEdge
          (fun x => selectedBorder level x transverse)
          (side level) coordinate = .none ∧
      Canonical.intervalEdge
          (fun x => selectedBorder level x transverse)
          (side level) (coordinate + 1) = .none) ↔
      isHorizontalCarrier level coordinate transverse = true := by
  constructor
  · exact horizontalCarrier_of_intervalEdge_pair coordinate_lt
  · exact intervalEdge_pair_of_horizontalCarrier coordinate_lt

end Cslib.WangTile.Robinson.Carrier
