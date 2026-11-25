/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Carrier.Addresses

/-!
# Centered corner markers of the Robinson scaffold

The canonical seed patches have exactly the arithmetic hierarchy's carrier roles. Every
all-clear index-zero northeast quarter is the center of a recursive frame: inherited markers
lift a center, new markers introduce a center, and boundary copies cannot carry both axes.
Consequently every corner marker has logical payload address `(0, 0)`.

## Main definitions

* `canonicalAddressing`: a canonical seed patch with compatible wire and crossing addresses.

## References

Ported from [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3), revision
`64268a3`, `ShadedCarrierConcreteRoles`, `ShadedCarrierSquareGeometry` (lines 57–77),
and `ShadedCarrierCornerAddressing` (the centered-marker induction and corner-zero theorem,
lines 247–420, and the addressed-square construction, lines 424–431). The proofs closely
follow the source, with `AddressedSquare` replacing `SquareAddressing`. This is the backward
seed-removal construction after [Robinson1971], in the corrected scaffold of [Ollinger2008]
as presented in [JeandelVanier2020], §3.3, pp. 26–29. Robinson describes the geometric
construction in §7, pp. 201–205; the Ollinger internal locator is not verified.
-/

public section

namespace Cslib.WangTile.Robinson.Carrier

open Canonical

private theorem previousInterior_congr_of_lt
    {left right : Nat → Option Bool} {position : Nat}
    (equal : ∀ coordinate, coordinate < position →
      left coordinate = right coordinate) :
    previousInterior left position =
      previousInterior right position := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      have current := equal position (by omega)
      cases rightCurrent : right position with
      | none =>
          have prior := inductionHypothesis fun coordinate lower =>
            equal coordinate (lower.trans (by omega))
          simp [previousInterior, current,
            rightCurrent, prior]
      | some orientation =>
          simp [previousInterior, current, rightCurrent]

private theorem nextInterior_congr_of_lt
    {left right : Nat → Option Bool} {length position fuel : Nat}
    (bounded : position + fuel ≤ length)
    (equal : ∀ coordinate, coordinate < length →
      left coordinate = right coordinate) :
    nextInterior left position fuel =
      nextInterior right position fuel := by
  induction fuel generalizing position with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      have position_lt : position < length := by omega
      have current := equal position position_lt
      cases rightCurrent : right position with
      | none =>
          have tail := inductionHypothesis (position := position + 1)
            (by omega)
          simp [nextInterior, current,
            rightCurrent, tail]
      | some orientation =>
          simp [nextInterior, current, rightCurrent]

private theorem intervalEdge_congr_of_lt
    {left right : Nat → Option Bool} {length position : Nat}
    (bounded : position ≤ length)
    (equal : ∀ coordinate, coordinate < length →
      left coordinate = right coordinate) :
    intervalEdge left length position =
      intervalEdge right length position := by
  have nextEqual := nextInterior_congr_of_lt
    (left := left) (right := right) (length := length)
    (position := position) (fuel := length - position)
    (by omega) equal
  have previousEqual := previousInterior_congr_of_lt
    (left := left) (right := right) (position := position)
    fun coordinate lower => equal coordinate (lower.trans_le bounded)
  unfold intervalEdge
  rw [nextEqual, previousEqual]

private theorem horizontalCarrier_canonicalPatch_iff
    (level : ℕ) (i j : Fin (side level)) :
    (scaffold.role ((canonicalPatch level seedNode).tile i j)).horizontalCarrier = true ↔
      isHorizontalCarrier level i j = true := by
  rw [scaffold_role]
  change (ShadedSite.routeRole (ShadedSite.tile (site level seedNode i j))).horizontalCarrier =
    true ↔ _
  rw [ShadedSite.horizontalCarrier_iff]
  change (intervalEdge (fun x => rowInterior level seedNode x j) (side level) i = .none ∧
    intervalEdge (fun x => rowInterior level seedNode x j) (side level) (i.val + 1) = .none) ↔ _
  have equal : ∀ x, x < side level →
      rowInterior level seedNode x j = selectedBorder level x j :=
    fun x hx => rowInterior_seed_eq_selectedBorder level x j hx j.isLt
  rw [intervalEdge_congr_of_lt i.isLt.le equal,
    intervalEdge_congr_of_lt (by omega : i.val + 1 ≤ side level) equal]
  exact intervalEdge_pair_iff_horizontalCarrier i.isLt

private theorem verticalCarrier_canonicalPatch_iff
    (level : ℕ) (i j : Fin (side level)) :
    (scaffold.role ((canonicalPatch level seedNode).tile i j)).verticalCarrier = true ↔
      isVerticalCarrier level i j = true := by
  rw [scaffold_role]
  change (ShadedSite.routeRole (ShadedSite.tile (site level seedNode i j))).verticalCarrier =
    true ↔ _
  rw [ShadedSite.verticalCarrier_iff]
  change (intervalEdge (fun y => columnInterior level seedNode i y) (side level) j = .none ∧
    intervalEdge (fun y => columnInterior level seedNode i y) (side level) (j.val + 1) = .none) ↔ _
  have equal : ∀ y, y < side level →
      columnInterior level seedNode i y = selectedBorder level y i :=
    fun y hy => columnInterior_seed_eq_selectedBorder level i y i.isLt hy
  rw [intervalEdge_congr_of_lt j.isLt.le equal,
    intervalEdge_congr_of_lt (by omega : j.val + 1 ≤ side level) equal]
  exact intervalEdge_pair_iff_horizontalCarrier j.isLt

private theorem eraseCorner_eq_carrierRole_of_carriers
    (level x y : ℕ) (role : RouteRole)
    (horizontal : role.horizontalCarrier = isHorizontalCarrier level x y)
    (vertical : role.verticalCarrier = isVerticalCarrier level x y) :
    eraseCorner role = carrierRole level x y := by
  cases role <;>
    cases horizontalCarrier : isHorizontalCarrier level x y <;>
    cases verticalCarrier : isVerticalCarrier level x y <;>
    simp_all [eraseCorner, carrierRole, RouteRole.horizontalCarrier, RouteRole.verticalCarrier]

private theorem canonicalPatch_carrierRole (level : ℕ) (i j : Fin (side level)) :
    eraseCorner (scaffold.role ((canonicalPatch level seedNode).tile i j)) =
      carrierRole level i j :=
  eraseCorner_eq_carrierRole_of_carriers level i j _
    (Bool.eq_iff_iff.mpr (horizontalCarrier_canonicalPatch_iff level i j))
    (Bool.eq_iff_iff.mpr (verticalCarrier_canonicalPatch_iff level i j))

private theorem quadrantAt_eq_northeast_iff (x y : ℕ) :
    quadrantAt x y = .northeast ↔ x % 2 = 1 ∧ y % 2 = 1 := by
  have xCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have yCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases xCases with hx | hx <;> rcases yCases with hy | hy <;>
      simp [quadrantAt, Quadrant.ofBits, hx, hy]

/-- Fine quarter coordinate of an inherited northeast quarter. -/
private def liftCoordinate (coordinate : ℕ) : ℕ := 4 * coordinate - 3

private theorem ceilDivFour_liftCoordinate
    {coordinate : ℕ} (positive : 0 < coordinate) :
    ceilDivFour (liftCoordinate coordinate) =
      coordinate := by
  exact ceilDivFour_four_mul_sub_three coordinate positive

private theorem liftCoordinate_mod_four
    {coordinate : ℕ} (positive : 0 < coordinate) :
    liftCoordinate coordinate % 4 = 1 := by
  unfold liftCoordinate
  omega

private theorem inFrame_succ_liftCoordinate
    (depth : ℕ) {coordinate : ℕ} (positive : 0 < coordinate) :
    inFrame (depth + 1) (liftCoordinate coordinate) =
      inFrame depth coordinate := by
  rw [inFrame_succ_iff_ceilDivFour,
    ceilDivFour_liftCoordinate positive]

private theorem liftCoordinate_centerResidue
    {depth coordinate : ℕ} (positive : 0 < coordinate)
    (center : coordinate % period depth = 2 * scale depth + 1) :
    liftCoordinate coordinate % period (depth + 1) =
      2 * scale (depth + 1) + 1 := by
  have decomposition := Nat.mod_add_div coordinate (period depth)
  have scaleEq : scale (depth + 1) = 4 * scale depth := by
    simp [scale, pow_succ, Nat.mul_comm]
  have expression : liftCoordinate coordinate =
      2 * scale (depth + 1) + 1 + period (depth + 1) * (coordinate / period depth) := by
    rw [period_succ, scaleEq, Nat.mul_assoc, liftCoordinate]
    omega
  have centerLt : 2 * scale (depth + 1) + 1 < period (depth + 1) := by
    rw [period_eq_four_mul_scale]
    have := scale_pos (depth + 1)
    omega
  rw [expression, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt centerLt]

/-- For coordinates at residue one modulo four, inherited positive-depth
frames shift up by one depth and no new depth-one owner is introduced. -/
private theorem depthAt_liftCoordinate
    (bound coordinate : ℕ) (positive : 0 < coordinate)
    (modOne : coordinate % 4 = 1) :
    depthAt (bound + 1) (liftCoordinate coordinate) =
      (depthAt bound coordinate).map (fun depth => depth + 1) := by
  induction bound with
  | zero =>
      simp only [depthAt, Option.map_none]
      rw [inFrame_succ_liftCoordinate 0 positive]
      simp [inFrame, period, scale, frameStartResidue,
        frameEndResidue, modOne]
  | succ bound inductionHypothesis =>
      change
        (match depthAt (bound + 1) (liftCoordinate coordinate) with
        | some depth => some depth
        | none =>
            if inFrame (bound + 2) (liftCoordinate coordinate) = true then
              some (bound + 2)
            else none) =
          Option.map (fun depth => depth + 1)
            (match depthAt bound coordinate with
            | some depth => some depth
            | none =>
                if inFrame (bound + 1) coordinate = true then
                  some (bound + 1)
                else none)
      rw [inductionHypothesis]
      cases previous : depthAt bound coordinate with
      | some depth => simp
      | none =>
          simp only [Option.map_none]
          rw [inFrame_succ_liftCoordinate (bound + 1) positive]
          by_cases inside : inFrame (bound + 1) coordinate <;>
            simp [inside]

private theorem onFrameBoundary_eq_false_of_liftCoordinate
    {depth coordinate : ℕ} (depthPositive : 0 < depth)
    (coordinatePositive : 0 < coordinate)
    (modOne : coordinate % 4 = 1)
    (fineInterior :
      onFrameBoundary (depth + 1) (liftCoordinate coordinate) = false) :
    onFrameBoundary depth coordinate = false := by
  have fineData := (onFrameBoundary_eq_false_iff _ _).mp fineInterior
  apply Bool.eq_false_iff.2
  intro boundary
  have coarseData : coordinate % period depth = frameStartResidue depth ∨
      coordinate % period depth = frameEndResidue depth := by
    simpa only [onFrameBoundary, Bool.or_eq_true,
      decide_eq_true_eq] using boundary
  rcases coarseData with opening | closing
  · apply fineData.1
    apply (openingBoundary_succ_iff depth (liftCoordinate coordinate)).2
    exact ⟨by simpa [ceilDivFour_liftCoordinate coordinatePositive] using opening,
      liftCoordinate_mod_four coordinatePositive⟩
  · have zeroResidue : coordinate % period 0 = 0 :=
      largeClosing_mod_small depthPositive closing
    have periodZero : period 0 = 4 := by simp [period]
    rw [periodZero, modOne] at zeroResidue
    contradiction

private theorem horizontalCarrier_of_liftCoordinate
    {level x y : ℕ} (levelPositive : 0 < level)
    (xPositive : 0 < x) (yPositive : 0 < y)
    (xMod : x % 4 = 1) (yMod : y % 4 = 1)
    (fineCarrier : isHorizontalCarrier (level + 1)
      (liftCoordinate x) (liftCoordinate y) = true) :
    isHorizontalCarrier level x y = true := by
  have rowShift : depthAt level (liftCoordinate y) =
      (depthAt (level - 1) y).map (fun depth => depth + 1) := by
    simpa [Nat.sub_add_cancel levelPositive] using
      depthAt_liftCoordinate (level - 1) y yPositive yMod
  cases owner : depthAt (level - 1) y with
  | none => simp [isHorizontalCarrier, rowShift, owner] at fineCarrier
  | some depth =>
      have fineData : inFrame (depth + 1) (liftCoordinate x) = true ∧
          onFrameBoundary (depth + 1) (liftCoordinate x) = false := by
        simpa [isHorizontalCarrier, rowShift, owner] using fineCarrier
      have coarseData : inFrame depth x = true ∧
          onFrameBoundary depth x = false := by
        refine ⟨?_, onFrameBoundary_eq_false_of_liftCoordinate
          (depthAt_pos owner) xPositive xMod fineData.2⟩
        simpa [inFrame_succ_liftCoordinate depth xPositive] using fineData.1
      simpa [isHorizontalCarrier, owner] using coarseData

private theorem verticalCarrier_of_liftCoordinate
    {level x y : ℕ} (levelPositive : 0 < level)
    (xPositive : 0 < x) (yPositive : 0 < y)
    (xMod : x % 4 = 1) (yMod : y % 4 = 1)
    (fineCarrier : isVerticalCarrier (level + 1)
      (liftCoordinate x) (liftCoordinate y) = true) :
    isVerticalCarrier level x y = true := by
  simpa only [isVerticalCarrier, isHorizontalCarrier] using
    horizontalCarrier_of_liftCoordinate levelPositive yPositive xPositive
      yMod xMod fineCarrier

private theorem depthAt_eq_one_of_center_one
    {bound coordinate : ℕ} (boundPositive : 0 < bound)
    (center : coordinate % period 1 = 2 * scale 1 + 1) :
    depthAt bound coordinate = some 1 := by
  have inside : inFrame 1 coordinate = true := by
    simp [inFrame, center, frameStartResidue, frameEndResidue, scale]
  have atOne : depthAt 1 coordinate = some 1 := by
    simp [depthAt, inside]
  exact depthAt_eq_some_mono atOne boundPositive

/-- A crossing lies at the common center of one horizontal and vertical
carrier frame. -/
private structure Centered (level x y depth : ℕ) : Prop where
  rowOwner : depthAt (level - 1) y = some depth
  columnOwner : depthAt (level - 1) x = some depth
  xCenter : x % period depth = 2 * scale depth + 1
  yCenter : y % period depth = 2 * scale depth + 1

private theorem Centered.lift
    {level x y depth : ℕ} (centered : Centered level x y depth)
    (levelPositive : 0 < level) (xPositive : 0 < x) (yPositive : 0 < y)
    (xMod : x % 4 = 1) (yMod : y % 4 = 1) :
    Centered (level + 1) (liftCoordinate x) (liftCoordinate y) (depth + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have shifted := depthAt_liftCoordinate (level - 1) y yPositive yMod
    rw [Nat.sub_add_cancel levelPositive, centered.rowOwner] at shifted
    simpa using shifted
  · have shifted := depthAt_liftCoordinate (level - 1) x xPositive xMod
    rw [Nat.sub_add_cancel levelPositive, centered.columnOwner] at shifted
    simpa using shifted
  · exact liftCoordinate_centerResidue xPositive centered.xCenter
  · exact liftCoordinate_centerResidue yPositive centered.yCenter

private theorem centeredAtOne
    {level x y : ℕ} (levelPositive : 0 < level)
    (xCenter : x % period 1 = 2 * scale 1 + 1)
    (yCenter : y % period 1 = 2 * scale 1 + 1) :
    Centered (level + 1) x y 1 := by
  exact ⟨depthAt_eq_one_of_center_one levelPositive yCenter,
    depthAt_eq_one_of_center_one levelPositive xCenter,
    xCenter, yCenter⟩

/-- Every all-clear index-zero crossing in a canonical seed supertile is the
center of one of its recursive carrier frames. -/
private theorem indexZero_crossing_centered :
    ∀ level x y : ℕ,
      x < 4 ^ level →
      y < 4 ^ level →
      supertileIndexGrid level seedNode x y = 0 →
      isHorizontalCarrier level (2 * x + 1) (2 * y + 1) = true →
      isVerticalCarrier level (2 * x + 1) (2 * y + 1) = true →
      ∃ depth, Centered level (2 * x + 1) (2 * y + 1) depth := by
  intro level
  induction level with
  | zero =>
      intro x y xBound yBound indexZero horizontal vertical
      simp [isHorizontalCarrier] at horizontal
  | succ level inductionHypothesis =>
      intro x y xBound yBound indexZero horizontal vertical
      have parentXBound : x / 4 < 4 ^ level := Nat.div_lt_of_lt_mul (by rwa [pow_succ'] at xBound)
      have parentYBound : y / 4 < 4 ^ level := Nat.div_lt_of_lt_mul (by rwa [pow_succ'] at yBound)
      have levelPositive : 0 < level := Nat.pos_of_ne_zero fun levelZero => by
        subst level
        simp [isHorizontalCarrier] at horizontal
      rcases supertileIndexGrid_zero_cases level x y xBound yBound indexZero with
          ⟨xMod, yMod, parentZero, parentXEven, parentYEven⟩ |
          ⟨xMod, yMod, parentFour, parentXOdd, parentYOdd⟩ |
          ⟨xMod, yMod, parentXEven, parentYEven⟩
      · let coarseX := 2 * (x / 4) + 1
        let coarseY := 2 * (y / 4) + 1
        have coarseXPositive : 0 < coarseX := by simp [coarseX]
        have coarseYPositive : 0 < coarseY := by simp [coarseY]
        have coarseXMod : coarseX % 4 = 1 := by
          simp only [coarseX]
          omega
        have coarseYMod : coarseY % 4 = 1 := by
          simp only [coarseY]
          omega
        have fineXEq : 2 * x + 1 = liftCoordinate coarseX := by
          simp only [coarseX, liftCoordinate]
          omega
        have fineYEq : 2 * y + 1 = liftCoordinate coarseY := by
          simp only [coarseY, liftCoordinate]
          omega
        have coarseHorizontal :
            isHorizontalCarrier level coarseX coarseY = true := by
          apply horizontalCarrier_of_liftCoordinate levelPositive
            coarseXPositive coarseYPositive coarseXMod coarseYMod
          simpa only [fineXEq, fineYEq] using horizontal
        have coarseVertical :
            isVerticalCarrier level coarseX coarseY = true := by
          apply verticalCarrier_of_liftCoordinate levelPositive
            coarseXPositive coarseYPositive coarseXMod coarseYMod
          simpa only [fineXEq, fineYEq] using vertical
        rcases inductionHypothesis (x / 4) (y / 4)
            parentXBound parentYBound parentZero
            coarseHorizontal coarseVertical with ⟨depth, coarseCentered⟩
        exact ⟨depth + 1, by
          simpa only [fineXEq, fineYEq] using
            coarseCentered.lift levelPositive coarseXPositive coarseYPositive
              coarseXMod coarseYMod⟩
      · let coarseX := 2 * (x / 4) + 1
        let coarseY := 2 * (y / 4) + 1
        have fineXEq : 2 * x + 1 = liftCoordinate coarseX := by
          simp only [coarseX, liftCoordinate]
          omega
        have fineYEq : 2 * y + 1 = liftCoordinate coarseY := by
          simp only [coarseY, liftCoordinate]
          omega
        have xCenter :
            liftCoordinate coarseX % period 1 = 2 * scale 1 + 1 := by
          simp only [coarseX, liftCoordinate, period, scale]
          omega
        have yCenter :
            liftCoordinate coarseY % period 1 = 2 * scale 1 + 1 := by
          simp only [coarseY, liftCoordinate, period, scale]
          omega
        exact ⟨1, by
          simpa only [fineXEq, fineYEq] using
            centeredAtOne levelPositive xCenter yCenter⟩
      · have xOpening :
            (2 * x + 1) % period 1 = frameStartResidue 1 := by
          simp only [period, frameStartResidue, scale]
          omega
        have yInside : inFrame 1 (2 * y + 1) = true := by
          simp [inFrame, period, frameStartResidue, frameEndResidue, scale]
          omega
        have rowOwnerOne : depthAt 1 (2 * y + 1) = some 1 := by
          simp [depthAt, yInside]
        have rowOwner : depthAt level (2 * y + 1) = some 1 :=
          depthAt_eq_some_mono rowOwnerOne levelPositive
        have xBoundary : onFrameBoundary 1 (2 * x + 1) = true := by
          simp [onFrameBoundary, xOpening]
        simp [isHorizontalCarrier, rowOwner, xBoundary] at horizontal

private theorem corner_point_zero
    (level : ℕ) (i j : Fin (side level))
    (corner : scaffold.role ((canonicalPatch level seedNode).tile i j) = .corner) :
    point level i.val j.val = (0, 0) := by
  have horizontal : isHorizontalCarrier level i.val j.val = true :=
    (horizontalCarrier_canonicalPatch_iff level i j).mp (by
      rw [corner]; rfl)
  have vertical : isVerticalCarrier level i.val j.val = true :=
    (verticalCarrier_canonicalPatch_iff level i j).mp (by
      rw [corner]; rfl)
  rw [scaffold_role] at corner
  have marker := (ShadedSite.corner_iff (site level seedNode i j)).mp corner
  have indexZero : supertileIndexGrid level seedNode (i.val / 2) (j.val / 2) = 0 :=
    by simpa only [site] using congrArg QuarterIndex.index marker.2
  have northeast : quadrantAt i.val j.val = .northeast :=
    by simpa only [site] using congrArg QuarterIndex.quadrant marker.2
  have parity := (quadrantAt_eq_northeast_iff i.val j.val).mp northeast
  have iEq : i.val = 2 * (i.val / 2) + 1 := by omega
  have jEq : j.val = 2 * (j.val / 2) + 1 := by omega
  have tileXBound : i.val / 2 < 4 ^ level := by
    have := i.isLt
    simp only [side] at this
    omega
  have tileYBound : j.val / 2 < 4 ^ level := by
    have := j.isLt
    simp only [side] at this
    omega
  obtain ⟨depth, rowOwner, columnOwner, xCenter, yCenter⟩ := indexZero_crossing_centered level
    (i.val / 2) (j.val / 2) tileXBound tileYBound indexZero
    (by simpa only [← iEq, ← jEq] using horizontal)
    (by simpa only [← iEq, ← jEq] using vertical)
  apply point_eq_zero_of_centerResidues (depth := depth)
  · simpa only [← jEq] using rowOwner
  · simpa only [← iEq] using columnOwner
  · simpa only [← iEq] using xCenter
  · simpa only [← jEq] using yCenter

private theorem cast_square_tile {τ : List WangTile} {m n : ℕ}
    (R : Rectangle τ m m) (h : m = n) (i j : Fin n) :
    (h ▸ R).tile i j = R.tile (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst n
  rfl

/-- A canonical decorated seed square with compatible integer payload addresses.
Every seeded crossing receives the pointed payload's origin. -/
def canonicalAddressing (level : ℕ) :
    AddressedSquare scaffold (side level - 1) :=
  let sideEq : side level = side level - 1 + 1 := by
    have sidePositive : 0 < side level := by simp [side]
    omega
  addressedSquareOfHierarchy (level := level)
    (sideEq ▸ canonicalPatch level seedNode)
    (by
      intro i j
      rw [cast_square_tile]
      exact canonicalPatch_carrierRole level _ _)
    (by
      intro i j hc
      rw [cast_square_tile] at hc
      exact corner_point_zero level _ _ hc)

/-- The addressed canonical square retains the canonical decorated tile at each coordinate. -/
@[simp] theorem canonicalAddressing_base_tile (level : ℕ)
    (i j : Fin (side level - 1 + 1)) :
    (canonicalAddressing level).base.tile i j =
      ShadedSite.tile (site level seedNode i.val j.val) := by
  unfold canonicalAddressing
  rw [addressedSquareOfHierarchy_base, cast_square_tile]
  rfl

end Cslib.WangTile.Robinson.Carrier
