/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Basic
import Mathlib.Data.Nat.Find

/-!
# Outward-facing light boundaries of Robinson boards

A matching shade assignment gives a discrete signed face height inside every uniformly
light oriented red cycle. The local shade rules conserve flow and forbid right turns;
the outer cycle has height one. The resulting minimum principle forces the nearest
selected boundary on each side of a free row or column to face outwards.
The free-line predicates are provided for the subsequent free-grid construction;
this module does not establish the existence of free rows or columns.

## Main definitions

* `IsFreeRow` and `IsFreeColumn`: board lines crossed by no selected
  light boundary.
* `Geometry`: the four outward-facing nearest-boundary conditions.

## Main results

* `CycleShade.geometry`: every uniformly light oriented red board
  in a locally allowed matching shade grid satisfies the full nearest-boundary conditions.

## References

The outward-facing boundary construction is after [JeandelVanier2020], §3.3,
Figure 18 (manuscript pp. 27–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, modules `Closed104.OrientedLightHeightWeights`, `OrientedLightHeight`,
`OrientedLightFreeHeight`, `OrientedLightBoundarySearch`, `OrientedLightHorizontalGeometry`,
`OrientedLightVerticalGeometry`, `ShadedObstructionGeometry` and
`ShadedLightBoardFreeLines`. The hypotheses, quarter-coordinate conventions and
nearest-boundary conclusion agree with `OrientedLightGeometry.CycleShade.geometry` there.
-/

public section
namespace Cslib.WangTile.Robinson

/-- No selected light vertical border crosses this strict board row. -/
@[expose] def IsFreeRow (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → ShadeState)
    (west east row : Nat) : Prop :=
  ∀ quarterX, quarterWest west < quarterX → quarterX < quarterEast east →
    selectedVerticalFor
      (componentAt indexGrid quarterX row) (quadrantAt quarterX row)
      (shadeGrid quarterX row) = none

/-- No selected light horizontal border crosses this strict board column. -/
@[expose] def IsFreeColumn (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → ShadeState)
    (south north column : Nat) : Prop :=
  ∀ quarterY, quarterSouth south < quarterY → quarterY < quarterNorth north →
    selectedHorizontalFor
      (componentAt indexGrid column quarterY) (quadrantAt column quarterY)
      (shadeGrid column quarterY) = none

/-- Nearest selected borders around each interior free-line crossing point face
outwards, with every intervening position clear of selected borders. -/
structure Geometry
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → ShadeState)
    (west east south north : Nat) : Prop where
  /-- A free row meets a selected horizontal boundary locally or at its nearest
  outward-facing boundary above or below. -/
  verticalBoundary : ∀ {column row : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    IsFreeRow indexGrid shadeGrid west east row →
    ¬IsFreeColumn indexGrid shadeGrid south north column →
      selectedHorizontalFor
          (componentAt indexGrid column row) (quadrantAt column row)
          (shadeGrid column row) ≠ none ∨
      (∃ boundary, row < boundary ∧ boundary < quarterNorth north ∧
        selectedHorizontalFor
          (componentAt indexGrid column boundary) (quadrantAt column boundary)
          (shadeGrid column boundary) = some .north ∧
        ∀ y, row < y → y < boundary →
          selectedHorizontalFor
            (componentAt indexGrid column y) (quadrantAt column y)
            (shadeGrid column y) = none) ∨
      (∃ boundary, quarterSouth south < boundary ∧ boundary < row ∧
        selectedHorizontalFor
          (componentAt indexGrid column boundary) (quadrantAt column boundary)
          (shadeGrid column boundary) = some .south ∧
        ∀ y, boundary < y → y < row →
          selectedHorizontalFor
            (componentAt indexGrid column y) (quadrantAt column y)
            (shadeGrid column y) = none)
  /-- A free column meets a selected vertical boundary locally or at its nearest
  outward-facing boundary to the right or left. -/
  horizontalBoundary : ∀ {column row : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    IsFreeColumn indexGrid shadeGrid south north column →
    ¬IsFreeRow indexGrid shadeGrid west east row →
      selectedVerticalFor
          (componentAt indexGrid column row) (quadrantAt column row)
          (shadeGrid column row) ≠ none ∨
      (∃ boundary, column < boundary ∧ boundary < quarterEast east ∧
        selectedVerticalFor
          (componentAt indexGrid boundary row) (quadrantAt boundary row)
          (shadeGrid boundary row) = some .east ∧
        ∀ x, column < x → x < boundary →
          selectedVerticalFor
            (componentAt indexGrid x row) (quadrantAt x row)
            (shadeGrid x row) = none) ∨
      (∃ boundary, quarterWest west < boundary ∧ boundary < column ∧
        selectedVerticalFor
          (componentAt indexGrid boundary row) (quadrantAt boundary row)
          (shadeGrid boundary row) = some .west ∧
        ∀ x, boundary < x → x < column →
          selectedVerticalFor
            (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none)

/-- Weight of a directed light edge.  `positive` specifies which of the two
directions gives weight `1`. -/
private def edgeWeight (value : Option Shade) (positive : Bool) : Int :=
  if value = some .light then
    if positive then 1 else -1
  else
    0

/-- Horizontal edge immediately to the right of a quarter tile. -/
private def rightWeight (quadrant : Quadrant) (state : ShadeState) : Int :=
  edgeWeight state.east quadrant.yBit

/-- Horizontal edge immediately to the left of a quarter tile. -/
private def leftWeight (quadrant : Quadrant) (state : ShadeState) : Int :=
  edgeWeight state.west quadrant.yBit

/-- Vertical edge immediately above a quarter tile, measured as the height
change from its left face to its right face. -/
private def upWeight (quadrant : Quadrant) (state : ShadeState) : Int :=
  edgeWeight state.north quadrant.xBit

/-- Vertical edge immediately below a quarter tile, measured as the height
change from its left face to its right face. -/
private def downWeight (quadrant : Quadrant) (state : ShadeState) : Int :=
  edgeWeight state.south quadrant.xBit

private theorem neg_one_le_edgeWeight (value : Option Shade)
    (positive : Bool) : (-1 : Int) ≤ edgeWeight value positive := by
  unfold edgeWeight
  split_ifs <;> omega

private theorem neg_one_le_rightWeight (quadrant : Quadrant)
    (state : ShadeState) : (-1 : Int) ≤ rightWeight quadrant state :=
  neg_one_le_edgeWeight _ _

private theorem neg_one_le_upWeight (quadrant : Quadrant)
    (state : ShadeState) : (-1 : Int) ≤ upWeight quadrant state :=
  neg_one_le_edgeWeight _ _

private def allThick : List Thick :=
  [.a, .b, .c, .d, .e, .f, .g, .h, .i, .j, .k, .l, .m, .n, .o, .p, .q, .r, .s, .t]

private theorem mem_allThick (component : Thick) : component ∈ allThick := by
  cases component <;> simp [allThick]

private def edgeOptions (present : Bool) : List (Option Shade) :=
  if present then [some .light, some .dark] else [none]

private theorem mem_edgeOptions {value : Option Shade} {present : Bool}
    (h : value.isSome = present) : value ∈ edgeOptions present := by
  cases value with
  | none => simp [← h, edgeOptions]
  | some shade => cases shade <;> simp [← h, edgeOptions]

/-- Combined Boolean check of all ten local flow, turn, and selected-boundary properties
at one quarter tile. -/
private def localGeometryOk (component : Thick) (quadrant : Quadrant)
    (state : ShadeState) : Bool :=
  !allowedFor component quadrant state ||
    let r := rightWeight quadrant state
    let l := leftWeight quadrant state
    let u := upWeight quadrant state
    let d := downWeight quadrant state
    (r - l == u - d) &&
    !(r == -1 && u == -1) &&
    (match selectedHorizontalFor component quadrant state with
      | none => r == 0 && l == 0
      | some .south => r == -1 || l == -1
      | some .north => r == 1 || l == 1) &&
    (match selectedVerticalFor component quadrant state with
      | none => u == 0 && d == 0
      | some .west => u == -1 || d == -1
      | some .east => u == 1 || d == 1) &&
    (match state.west, state.east with
      | some .light, some .light => u == 0
      | _, _ => true) &&
    (match state.south, state.north with
      | some .light, some .light => r == 0
      | _, _ => true)

private theorem localGeometryOk_all :
    (allThick.all fun component =>
      Quadrant.all.all fun quadrant =>
        (edgeOptions (hasWest component quadrant)).all fun w =>
          (edgeOptions (hasEast component quadrant)).all fun e =>
            (edgeOptions (hasSouth component quadrant)).all fun s =>
              (edgeOptions (hasNorth component quadrant)).all fun n =>
                localGeometryOk component quadrant ⟨w, e, s, n⟩) = true := by
  decide +kernel

private theorem localGeometryOk_of_allowed (component : Thick) (quadrant : Quadrant)
    (state : ShadeState) (allowed : allowedFor component quadrant state = true) :
    localGeometryOk component quadrant state = true := by
  have hrules := allowedFor_iff.mp allowed
  rcases state with ⟨w, e, s, n⟩
  have h1 := List.all_eq_true.mp localGeometryOk_all component (mem_allThick component)
  have h2 := List.all_eq_true.mp h1 quadrant (Quadrant.mem_all quadrant)
  have h3 := List.all_eq_true.mp h2 w (mem_edgeOptions hrules.west_present)
  have h4 := List.all_eq_true.mp h3 e (mem_edgeOptions hrules.east_present)
  have h5 := List.all_eq_true.mp h4 s (mem_edgeOptions hrules.south_present)
  exact List.all_eq_true.mp h5 n (mem_edgeOptions hrules.north_present)

private theorem localGeometry_unpack {component : Thick} {quadrant : Quadrant}
    {state : ShadeState} (allowed : allowedFor component quadrant state = true) :
    (rightWeight quadrant state - leftWeight quadrant state =
        upWeight quadrant state - downWeight quadrant state) ∧
      ¬ (rightWeight quadrant state = -1 ∧ upWeight quadrant state = -1) ∧
      (match selectedHorizontalFor component quadrant state with
        | none => rightWeight quadrant state = 0 ∧ leftWeight quadrant state = 0
        | some .south => rightWeight quadrant state = -1 ∨ leftWeight quadrant state = -1
        | some .north => rightWeight quadrant state = 1 ∨ leftWeight quadrant state = 1) ∧
      (match selectedVerticalFor component quadrant state with
        | none => upWeight quadrant state = 0 ∧ downWeight quadrant state = 0
        | some .west => upWeight quadrant state = -1 ∨ downWeight quadrant state = -1
        | some .east => upWeight quadrant state = 1 ∨ downWeight quadrant state = 1) ∧
      (state.west = some .light → state.east = some .light → upWeight quadrant state = 0) ∧
      (state.south = some .light → state.north = some .light → rightWeight quadrant state = 0) := by
  have h := localGeometryOk_of_allowed component quadrant state allowed
  simp only [localGeometryOk, allowed, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq, beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨hbal, hturn⟩, hhor⟩, hver⟩, hup⟩, hright⟩ := h
  refine ⟨hbal, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hr, hu⟩
    rcases hturn with hne | hne <;> exact hne (by assumption)
  · rcases hsh : selectedHorizontalFor component quadrant state with _ | _ | _ <;>
      rw [hsh] at hhor <;> simpa only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hhor
  · rcases hsv : selectedVerticalFor component quadrant state with _ | _ | _ <;>
      rw [hsv] at hver <;> simpa only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hver
  · intro hw he
    simpa only [hw, he, beq_iff_eq] using hup
  · intro hs hn
    simpa only [hs, hn, beq_iff_eq] using hright

/-- The signed light flow has zero divergence at every allowed quarter tile. -/
private theorem balance_of_allowed (component : Thick) (quadrant : Quadrant)
    (state : ShadeState)
    (allowed : allowedFor component quadrant state = true) :
    rightWeight quadrant state - leftWeight quadrant state =
      upWeight quadrant state - downWeight quadrant state :=
  (localGeometry_unpack allowed).1

/-- A west-pointing bottom edge and a north-pointing left edge would be a
right turn, so they cannot meet at an allowed quarter tile. -/
private theorem not_right_negative_and_up_negative_of_allowed
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true) :
    ¬ (rightWeight quadrant state = -1 ∧ upWeight quadrant state = -1) :=
  (localGeometry_unpack allowed).2.1

private theorem horizontal_none_weights_zero
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedHorizontalFor component quadrant state = none) :
    rightWeight quadrant state = 0 ∧ leftWeight quadrant state = 0 := by
  have h := (localGeometry_unpack allowed).2.2.1
  rwa [hselected] at h

private theorem vertical_none_weights_zero
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedVerticalFor component quadrant state = none) :
    upWeight quadrant state = 0 ∧ downWeight quadrant state = 0 := by
  have h := (localGeometry_unpack allowed).2.2.2.1
  rwa [hselected] at h

private theorem horizontal_south_has_negative_weight
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedHorizontalFor component quadrant state = some .south) :
    rightWeight quadrant state = -1 ∨ leftWeight quadrant state = -1 := by
  have h := (localGeometry_unpack allowed).2.2.1
  rwa [hselected] at h

private theorem horizontal_north_has_positive_weight
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedHorizontalFor component quadrant state = some .north) :
    rightWeight quadrant state = 1 ∨ leftWeight quadrant state = 1 := by
  have h := (localGeometry_unpack allowed).2.2.1
  rwa [hselected] at h

private theorem vertical_west_has_negative_weight
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedVerticalFor component quadrant state = some .west) :
    upWeight quadrant state = -1 ∨ downWeight quadrant state = -1 := by
  have h := (localGeometry_unpack allowed).2.2.2.1
  rwa [hselected] at h

private theorem vertical_east_has_positive_weight
    (component : Thick) (quadrant : Quadrant) (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (hselected : selectedVerticalFor component quadrant state = some .east) :
    upWeight quadrant state = 1 ∨ downWeight quadrant state = 1 := by
  have h := (localGeometry_unpack allowed).2.2.2.1
  rwa [hselected] at h

/-- A horizontal light wire leaves no vertical light edge in the same quarter. -/
private theorem up_zero_of_horizontal_light (component : Thick) (quadrant : Quadrant)
    (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (west : state.west = some .light) (east : state.east = some .light) :
    upWeight quadrant state = 0 :=
  (localGeometry_unpack allowed).2.2.2.2.1 west east

/-- A vertical light wire leaves no horizontal light edge in the same quarter. -/
private theorem right_zero_of_vertical_light (component : Thick) (quadrant : Quadrant)
    (state : ShadeState)
    (allowed : allowedFor component quadrant state = true)
    (south : state.south = some .light) (north : state.north = some .light) :
    rightWeight quadrant state = 0 :=
  (localGeometry_unpack allowed).2.2.2.2.2 south north

private def rightWeightAt (stateGrid : Nat → Nat → ShadeState)
    (x y : Nat) : Int :=
  rightWeight (quadrantAt x y) (stateGrid x y)

private def leftWeightAt (stateGrid : Nat → Nat → ShadeState)
    (x y : Nat) : Int :=
  leftWeight (quadrantAt x y) (stateGrid x y)

private def upWeightAt (stateGrid : Nat → Nat → ShadeState)
    (x y : Nat) : Int :=
  upWeight (quadrantAt x y) (stateGrid x y)

private def downWeightAt (stateGrid : Nat → Nat → ShadeState)
    (x y : Nat) : Int :=
  downWeight (quadrantAt x y) (stateGrid x y)

/-- Height of the face above the horizontal edge at `bottom + offset`, on the
vertical scan immediately to the right of `column`. -/
private def faceHeight (stateGrid : Nat → Nat → ShadeState)
    (column bottom : Nat) : Nat → Int
  | 0 => rightWeightAt stateGrid column bottom
  | offset + 1 =>
      faceHeight stateGrid column bottom offset +
        rightWeightAt stateGrid column (bottom + offset + 1)

private theorem ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    rightWeightAt stateGrid x y = leftWeightAt stateGrid (x + 1) y := by
  unfold rightWeightAt leftWeightAt rightWeight leftWeight
  rw [valid.hmatch x y]
  congr 1
  simp only [quadrantAt_yBit]

private theorem ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    upWeightAt stateGrid x y = downWeightAt stateGrid x (y + 1) := by
  unfold upWeightAt downWeightAt upWeight downWeight
  rw [valid.vmatch x y]
  congr 1
  simp only [quadrantAt_xBit]

private theorem ValidShadeGrid.balanceAt
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    rightWeightAt stateGrid x y - leftWeightAt stateGrid x y =
      upWeightAt stateGrid x y - downWeightAt stateGrid x y :=
  balance_of_allowed _ _ _ (valid.allowed x y)

variable {indexGrid : Nat → Nat → Index}
  {stateGrid : Nat → Nat → ShadeState}
  {west east south north : Nat}

private theorem CycleShade.south_rightWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x : Nat} (hwest : quarterWest west ≤ x)
    (heast : x < quarterEast east) :
    rightWeightAt stateGrid x (quarterSouth south) = 1 := by
  have light : (stateGrid x (quarterSouth south)).east = some .light := by
    rcases hwest.eq_or_lt with rfl | hwest
    · exact shaded.southwest
    · exact (shaded.south_at cycle valid hwest heast).2
  rw [rightWeightAt, rightWeight, light, quadrantAt_quarterSouth_yBit]
  rfl

private theorem CycleShade.south_upWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x : Nat} (hwest : quarterWest west < x)
    (heast : x < quarterEast east) :
    upWeightAt stateGrid x (quarterSouth south) = 0 :=
  up_zero_of_horizontal_light _ _ _ (valid.allowed x (quarterSouth south))
    (shaded.south_at cycle valid hwest heast).1
    (shaded.south_at cycle valid hwest heast).2

private theorem CycleShade.west_rightWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {y : Nat} (hsouth : quarterSouth south < y)
    (hnorth : y < quarterNorth north) :
    rightWeightAt stateGrid (quarterWest west) y = 0 :=
  right_zero_of_vertical_light _ _ _ (valid.allowed (quarterWest west) y)
    (shaded.west_at cycle valid hsouth hnorth).1
    (shaded.west_at cycle valid hsouth hnorth).2

private theorem CycleShade.faceHeight_south
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column : Nat} (hwest : quarterWest west ≤ column)
    (heast : column < quarterEast east) :
    faceHeight stateGrid column (quarterSouth south) 0 = 1 := by
  simpa [faceHeight] using CycleShade.south_rightWeightAt shaded cycle valid hwest heast

private theorem CycleShade.faceHeight_west
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {offset : Nat}
    (hnorth : quarterSouth south + offset < quarterNorth north) :
    faceHeight stateGrid (quarterWest west) (quarterSouth south) offset = 1 := by
  induction offset with
  | zero =>
      refine CycleShade.faceHeight_south shaded cycle valid le_rfl ?_
      have := cycle.west_lt_east
      simp [quarterWest, quarterEast] at this ⊢
      omega
  | succ offset ih =>
      rw [faceHeight, ih (by omega), CycleShade.west_rightWeightAt shaded cycle valid
        (y := quarterSouth south + offset + 1) (by omega) hnorth]
      omega

/-- Horizontal variation of face height is the signed vertical edge at the
shared vertex. -/
private theorem CycleShade.faceHeight_sub_left
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column offset : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east) :
    faceHeight stateGrid column (quarterSouth south) offset -
        faceHeight stateGrid (column - 1) (quarterSouth south) offset =
      upWeightAt stateGrid column (quarterSouth south + offset) := by
  induction offset with
  | zero =>
      simp only [faceHeight, Nat.add_zero,
        CycleShade.south_rightWeightAt shaded cycle valid (le_of_lt hwest) heast,
        CycleShade.south_rightWeightAt shaded cycle valid (x := column - 1) (by omega) (by omega),
        CycleShade.south_upWeightAt shaded cycle valid hwest heast, sub_self]
  | succ offset ih =>
      have hhor := ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ valid
        (column - 1) (quarterSouth south + offset + 1)
      rw [Nat.sub_add_cancel (by omega)] at hhor
      have hloc := ValidShadeGrid.balanceAt valid column (quarterSouth south + offset + 1)
      have hver := ValidShadeGrid.upWeightAt_eq_downWeightAt_succ valid
        column (quarterSouth south + offset)
      simp only [faceHeight, ← Nat.add_assoc]
      omega

/-- The counterclockwise outer board and the absence of right turns give a
discrete minimum principle: every strict interior face has positive height. -/
private theorem CycleShade.one_le_faceHeight
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {xOffset yOffset : Nat}
    (heast : quarterWest west + xOffset < quarterEast east)
    (hnorth : quarterSouth south + yOffset < quarterNorth north) :
    (1 : Int) ≤ faceHeight stateGrid
      (quarterWest west + xOffset) (quarterSouth south) yOffset := by
  induction xOffset generalizing yOffset with
  | zero => exact (CycleShade.faceHeight_west shaded cycle valid hnorth).ge
  | succ xOffset ihx =>
      induction yOffset with
      | zero =>
          exact (CycleShade.faceHeight_south shaded cycle valid
            (column := quarterWest west + (xOffset + 1)) (by omega) heast).ge
      | succ yOffset ihy =>
          have hleft := ihx (by omega) hnorth
          have hbelow := ihy (by omega)
          by_contra hlow
          have hdiff := CycleShade.faceHeight_sub_left shaded cycle valid
            (column := quarterWest west + (xOffset + 1))
            (offset := yOffset + 1) (by omega) heast
          have hcol : quarterWest west + (xOffset + 1) - 1 = quarterWest west + xOffset := by omega
          have hy : quarterSouth south + yOffset + 1 = quarterSouth south + (yOffset + 1) := by
            omega
          rw [hcol] at hdiff
          have hcur : faceHeight stateGrid (quarterWest west + (xOffset + 1))
              (quarterSouth south) (yOffset + 1) =
              faceHeight stateGrid (quarterWest west + (xOffset + 1)) (quarterSouth south) yOffset +
                rightWeightAt stateGrid (quarterWest west + (xOffset + 1))
                  (quarterSouth south + (yOffset + 1)) := by
            rw [faceHeight, hy]
          have hup_ge := neg_one_le_upWeight (quadrantAt (quarterWest west + (xOffset + 1))
            (quarterSouth south + (yOffset + 1)))
            (stateGrid (quarterWest west + (xOffset + 1)) (quarterSouth south + (yOffset + 1)))
          have hright_ge := neg_one_le_rightWeight (quadrantAt (quarterWest west + (xOffset + 1))
            (quarterSouth south + (yOffset + 1)))
            (stateGrid (quarterWest west + (xOffset + 1)) (quarterSouth south + (yOffset + 1)))
          refine not_right_negative_and_up_negative_of_allowed _ _ _
            (valid.allowed (quarterWest west + (xOffset + 1))
              (quarterSouth south + (yOffset + 1))) ?_
          dsimp only [rightWeightAt, upWeightAt] at hdiff hcur ⊢
          omega

private theorem ValidShadeGrid.horizontal_none_weightsAt_zero
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) = none) :
    rightWeightAt stateGrid x y = 0 ∧ leftWeightAt stateGrid x y = 0 := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_none_weights_zero _ _ _ (valid.allowed x y) hselected

private theorem ValidShadeGrid.vertical_none_weightsAt_zero
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) = none) :
    upWeightAt stateGrid x y = 0 ∧ downWeightAt stateGrid x y = 0 := by
  simpa [upWeightAt, downWeightAt] using
    vertical_none_weights_zero _ _ _ (valid.allowed x y) hselected

/-- Absolute-coordinate form of the positive-height theorem. -/
private theorem CycleShade.one_le_faceHeight_at
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west ≤ column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south ≤ row)
    (hnorth : row < quarterNorth north) :
    (1 : Int) ≤ faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) := by
  simpa only [show quarterWest west + (column - quarterWest west) = column by omega] using
    CycleShade.one_le_faceHeight shaded cycle valid (xOffset := column - quarterWest west)
      (yOffset := row - quarterSouth south) (by omega) (by omega)

/-- Every face on a free row has the outer board's height one. -/
private theorem CycleShade.faceHeight_eq_one_of_freeRow
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west ≤ column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south ≤ row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeRow indexGrid stateGrid west east row) :
    faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  let rowOffset := row - quarterSouth south
  have hrow : quarterSouth south + rowOffset = row := by
    dsimp [rowOffset]
    omega
  have all : ∀ xOffset,
      quarterWest west + xOffset < quarterEast east →
      faceHeight stateGrid (quarterWest west + xOffset)
        (quarterSouth south) rowOffset = 1 := by
    intro xOffset
    induction xOffset with
    | zero =>
        intro _
        simpa using CycleShade.faceHeight_west shaded cycle valid (offset := rowOffset) (by omega)
    | succ xOffset ih =>
        intro heastOffset
        have hprevious := ih (by omega)
        let column := quarterWest west + (xOffset + 1)
        have hnone := free column (by simp [column])
          (by simpa [column] using heastOffset)
        have hzero :=
          ValidShadeGrid.vertical_none_weightsAt_zero valid hnone
        have hdiff := CycleShade.faceHeight_sub_left
          shaded cycle valid (column := column) (offset := rowOffset)
          (by simp [column]) (by simpa [column] using heastOffset)
        have hleft : column - 1 = quarterWest west + xOffset := by
          simp [column]
        rw [hleft, hrow] at hdiff
        dsimp [column] at hdiff hzero
        omega
  simpa only [show quarterWest west + (column - quarterWest west) = column by omega] using
    all (column - quarterWest west) (by omega)

/-- Height immediately to the right of a free column is one. -/
private theorem CycleShade.faceHeight_eq_one_right_of_freeColumn
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west ≤ column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south ≤ row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column) :
    faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  suffices all : ∀ offset, quarterSouth south + offset < quarterNorth north →
      faceHeight stateGrid column (quarterSouth south) offset = 1 from
    all (row - quarterSouth south) (by omega)
  intro offset hnorthOffset
  induction offset with
  | zero => exact CycleShade.faceHeight_south shaded cycle valid hwest heast
  | succ offset ih =>
      have hzero := ValidShadeGrid.horizontal_none_weightsAt_zero valid
        (free (quarterSouth south + offset + 1) (by omega) (by omega))
      rw [faceHeight, ih (by omega), hzero.1, add_zero]

/-- Height immediately to the left of a strict free column is one. -/
private theorem CycleShade.faceHeight_eq_one_left_of_freeColumn
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south ≤ row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column) :
    faceHeight stateGrid (column - 1) (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  suffices all : ∀ offset, quarterSouth south + offset < quarterNorth north →
      faceHeight stateGrid (column - 1) (quarterSouth south) offset = 1 from
    all (row - quarterSouth south) (by omega)
  intro offset hnorthOffset
  induction offset with
  | zero => exact CycleShade.faceHeight_south shaded cycle valid (by omega) (by omega)
  | succ offset ih =>
      have hzero := ValidShadeGrid.horizontal_none_weightsAt_zero valid
        (free (quarterSouth south + offset + 1) (by omega) (by omega))
      have hmatch := ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ valid
        (column - 1) (quarterSouth south + offset + 1)
      rw [Nat.sub_add_cancel (by omega), hzero.2] at hmatch
      rw [faceHeight, ih (by omega), hmatch, add_zero]

/-- A finite run of zero-weight steps leaves an integer potential unchanged. -/
private theorem potential_eq_of_zero_steps
    {potential weight : Nat → Int} {start finish : Nat}
    (startLeFinish : start ≤ finish)
    (step : ∀ position, start < position → position ≤ finish →
      potential position = potential (position - 1) + weight position)
    (zero : ∀ position, start < position → position ≤ finish →
      weight position = 0) :
    potential finish = potential start := by
  induction finish, startLeFinish using Nat.le_induction with
  | base => rfl
  | succ finish _ inductionHypothesis =>
      rw [step (finish + 1) (by omega) le_rfl,
        zero (finish + 1) (by omega) le_rfl]
      have previous : finish + 1 - 1 = finish := by omega
      rw [previous, inductionHypothesis
        (fun position lower upper => step position lower (by omega))
        (fun position lower upper => zero position lower (by omega))]
      omega

/-- A nearest `-1` step above a unit-height point contradicts positivity. -/
private theorem negative_step_after_false
    {potential weight : Nat → Int} {start boundary : Nat}
    (startBoundary : start < boundary)
    (startHeight : potential start = 1)
    (step : ∀ position, start < position → position ≤ boundary →
      potential position = potential (position - 1) + weight position)
    (zero : ∀ position, start < position → position < boundary →
      weight position = 0)
    (negative : weight boundary = -1)
    (positive : 1 ≤ potential boundary) : False := by
  have stable := potential_eq_of_zero_steps
    (potential := potential) (weight := weight)
    (start := start) (finish := boundary - 1) (by omega)
    (fun position lower upper => step position lower (by omega))
    (fun position lower upper => zero position lower (by omega))
  have boundaryStep := step boundary startBoundary le_rfl
  rw [stable, startHeight, negative] at boundaryStep
  omega

/-- A nearest `+1` step below a unit-height point contradicts positivity at
the preceding point. -/
private theorem positive_step_before_false
    {potential weight : Nat → Int} {boundary finish : Nat}
    (boundaryFinish : boundary ≤ finish)
    (finishHeight : potential finish = 1)
    (boundaryStep :
      potential boundary = potential (boundary - 1) + weight boundary)
    (stepAfter : ∀ position, boundary < position → position ≤ finish →
      potential position = potential (position - 1) + weight position)
    (zero : ∀ position, boundary < position → position ≤ finish →
      weight position = 0)
    (positiveWeight : weight boundary = 1)
    (positiveBefore : 1 ≤ potential (boundary - 1)) : False := by
  have stable := potential_eq_of_zero_steps
    (potential := potential) (weight := weight)
    (start := boundary) (finish := finish) boundaryFinish stepAfter zero
  rw [finishHeight] at stable
  rw [stable.symm, positiveWeight] at boundaryStep
  omega

/-- A weight seen on either side of a coordinate occurs on the primary side
of that coordinate or its predecessor. -/
private theorem exists_adjacent_weight
    {primary secondary : Nat → Nat → Int}
    {coordinate position : Nat} {weight : Int}
    (coordinatePositive : 0 < coordinate)
    (shared : ∀ scan other,
      primary scan other = secondary (scan + 1) other)
    (atCoordinate : primary coordinate position = weight ∨
      secondary coordinate position = weight) :
    ∃ scan, (scan = coordinate ∨ scan + 1 = coordinate) ∧
      primary scan position = weight ∧
      ∀ other, primary coordinate other = 0 → secondary coordinate other = 0 →
        primary scan other = 0 := by
  rcases atCoordinate with primaryWeight | secondaryWeight
  · exact ⟨coordinate, Or.inl rfl, primaryWeight, fun _ primaryZero _ => primaryZero⟩
  · refine ⟨coordinate - 1, Or.inr (by omega), ?_, ?_⟩
    · rw [shared, show coordinate - 1 + 1 = coordinate by omega, secondaryWeight]
    · intro other _ secondaryZero
      rw [shared, show coordinate - 1 + 1 = coordinate by omega, secondaryZero]

/-- An oriented selected boundary after a unit-height point cannot be the
direction whose local weight is `-1`. The potential, weights, and choice of
the two directions are abstract, so the same scan applies on both axes. -/
private theorem selected_after_eq_of_negative_rejected
    {Direction : Type}
    {selected : Nat → Option Direction}
    {primary secondary potential : Nat → Nat → Int}
    {coordinate start boundary : Nat} {expected rejected : Direction}
    (directions : ∀ direction, direction = expected ∨ direction = rejected)
    (coordinatePositive : 0 < coordinate)
    (startBoundary : start < boundary)
    (boundarySelected : selected boundary ≠ none)
    (rejectedWeight : selected boundary = some rejected →
      primary coordinate boundary = -1 ∨ secondary coordinate boundary = -1)
    (shared : ∀ scan position,
      primary scan position = secondary (scan + 1) position)
    (startHeight : ∀ scan,
      scan = coordinate ∨ scan + 1 = coordinate → potential scan start = 1)
    (step : ∀ scan position,
      scan = coordinate ∨ scan + 1 = coordinate →
      start < position → position ≤ boundary →
      potential scan position =
        potential scan (position - 1) + primary scan position)
    (zero : ∀ position, start < position → position < boundary →
      primary coordinate position = 0 ∧ secondary coordinate position = 0)
    (positive : ∀ scan,
      scan = coordinate ∨ scan + 1 = coordinate →
      1 ≤ potential scan boundary) :
    selected boundary = some expected := by
  cases value : selected boundary with
  | none => exact (boundarySelected value).elim
  | some direction =>
      rcases directions direction with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨scan, scanEq, boundaryWeight, zeroOfPair⟩ :=
          exists_adjacent_weight coordinatePositive shared (rejectedWeight value)
        apply negative_step_after_false
          (potential := potential scan)
          (weight := primary scan) startBoundary
          (startHeight scan scanEq)
          (fun position lower upper =>
            step scan position scanEq lower upper)
          (fun position lower upper =>
            let pair := zero position lower upper
            zeroOfPair position pair.1 pair.2)
          boundaryWeight
          (positive scan scanEq)

/-- An oriented selected boundary before a unit-height point cannot be the
direction whose local weight is `+1`. This is the reverse scan dual of
`selected_after_eq_of_negative_rejected`. -/
private theorem selected_before_eq_of_positive_rejected
    {Direction : Type}
    {selected : Nat → Option Direction}
    {primary secondary potential : Nat → Nat → Int}
    {coordinate boundary finish : Nat} {expected rejected : Direction}
    (directions : ∀ direction, direction = expected ∨ direction = rejected)
    (coordinatePositive : 0 < coordinate)
    (boundaryFinish : boundary ≤ finish)
    (boundarySelected : selected boundary ≠ none)
    (rejectedWeight : selected boundary = some rejected →
      primary coordinate boundary = 1 ∨ secondary coordinate boundary = 1)
    (shared : ∀ scan position,
      primary scan position = secondary (scan + 1) position)
    (finishHeight : ∀ scan,
      scan = coordinate ∨ scan + 1 = coordinate → potential scan finish = 1)
    (step : ∀ scan position,
      scan = coordinate ∨ scan + 1 = coordinate →
      boundary ≤ position → position ≤ finish →
      potential scan position =
        potential scan (position - 1) + primary scan position)
    (zero : ∀ position, boundary < position → position ≤ finish →
      primary coordinate position = 0 ∧ secondary coordinate position = 0)
    (positiveBefore : ∀ scan,
      scan = coordinate ∨ scan + 1 = coordinate →
      1 ≤ potential scan (boundary - 1)) :
    selected boundary = some expected := by
  cases value : selected boundary with
  | none => exact (boundarySelected value).elim
  | some direction =>
      rcases directions direction with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨scan, scanEq, boundaryWeight, zeroOfPair⟩ :=
          exists_adjacent_weight coordinatePositive shared (rejectedWeight value)
        apply positive_step_before_false
          (potential := potential scan)
          (weight := primary scan) boundaryFinish
          (finishHeight scan scanEq)
          (step scan boundary scanEq le_rfl boundaryFinish)
          (fun position lower upper =>
            step scan position scanEq (by omega) upper)
          (fun position lower upper =>
            let pair := zero position lower upper
            zeroOfPair position pair.1 pair.2)
          boundaryWeight
          (positiveBefore scan scanEq)

private theorem exists_first_after
    {P : Nat → Prop} {start finish : Nat}
    (hstart : start < finish) (hfinish : P finish) :
    ∃ first, start < first ∧ first ≤ finish ∧ P first ∧
      ∀ value, start < value → value < first → ¬ P value := by
  classical
  have witness : ∃ value, start < value ∧ P value := ⟨finish, hstart, hfinish⟩
  refine ⟨Nat.find witness, (Nat.find_spec witness).1,
    Nat.find_min' witness ⟨hstart, hfinish⟩, (Nat.find_spec witness).2, ?_⟩
  intro value lower upper present
  exact Nat.find_min witness upper ⟨lower, present⟩

private theorem exists_last_before
    {P : Nat → Prop} {first finish : Nat}
    (hfirst : first < finish) (hfirstP : P first) :
    ∃ last, first ≤ last ∧ last < finish ∧ P last ∧
      ∀ value, last < value → value < finish → ¬ P value := by
  classical
  have bound : first ≤ finish - 1 := by omega
  have greatestBound := Nat.findGreatest_le (P := P) (finish - 1)
  refine ⟨Nat.findGreatest P (finish - 1), Nat.le_findGreatest bound hfirstP,
    by omega, Nat.findGreatest_spec bound hfirstP, ?_⟩
  intro value lower upper
  exact Nat.findGreatest_is_greatest lower (by omega)

/-- Given any selected point in an open interval, expose the current point or
the nearest selected point on one side.  The two callbacks provide the
domain-specific orientation of those nearest points. -/
private theorem boundary_of_exists_selected
    {Direction : Type} {selected : Nat → Option Direction}
    {lower coordinate upper : Nat} {after before : Direction}
    (witness : ∃ boundary, lower < boundary ∧ boundary < upper ∧
      selected boundary ≠ none)
    (orientAfter : ∀ boundary, coordinate < boundary → boundary < upper →
      selected boundary ≠ none →
      (∀ value, coordinate < value → value < boundary →
        selected value = none) →
      selected boundary = some after)
    (orientBefore : ∀ boundary, lower < boundary → boundary < coordinate →
      selected boundary ≠ none →
      (∀ value, boundary < value → value < coordinate →
        selected value = none) →
      selected coordinate = none →
      selected boundary = some before) :
    selected coordinate ≠ none ∨
      (∃ boundary, coordinate < boundary ∧ boundary < upper ∧
        selected boundary = some after ∧
        ∀ value, coordinate < value → value < boundary →
          selected value = none) ∨
      (∃ boundary, lower < boundary ∧ boundary < coordinate ∧
        selected boundary = some before ∧
        ∀ value, boundary < value → value < coordinate →
          selected value = none) := by
  by_cases atCoordinate : selected coordinate ≠ none
  · exact Or.inl atCoordinate
  have coordinateClear : selected coordinate = none := not_ne_iff.mp atCoordinate
  rcases witness with ⟨boundary, boundaryLower, boundaryUpper, boundarySelected⟩
  rcases lt_trichotomy coordinate boundary with afterCoordinate | equal | beforeCoordinate
  · rcases exists_first_after (P := fun value => selected value ≠ none)
        afterCoordinate boundarySelected with
      ⟨first, coordinateFirst, firstBoundary, firstSelected, between⟩
    have clear : ∀ value, coordinate < value → value < first → selected value = none :=
      fun value hlo hhi => not_ne_iff.mp (between value hlo hhi)
    have firstUpper : first < upper := by omega
    exact Or.inr (Or.inl ⟨first, coordinateFirst, firstUpper,
      orientAfter first coordinateFirst firstUpper firstSelected clear, clear⟩)
  · subst boundary
    exact (boundarySelected coordinateClear).elim
  · rcases exists_last_before (P := fun value => selected value ≠ none)
        beforeCoordinate boundarySelected with
      ⟨last, boundaryLast, lastCoordinate, lastSelected, between⟩
    have clear : ∀ value, last < value → value < coordinate → selected value = none :=
      fun value hlo hhi => not_ne_iff.mp (between value hlo hhi)
    have lastLower : lower < last := by omega
    exact Or.inr (Or.inr ⟨last, lastLower, lastCoordinate,
      orientBefore last lastLower lastCoordinate lastSelected clear coordinateClear, clear⟩)

/-- Combine nearest-boundary search with the common unit-height argument.
The caller supplies one axis's selected directions, local weights, potential,
and the facts that the potential is one on the free line and positive inside
the surrounding board. -/
private theorem boundary_of_unit_height
    {Direction : Type} {selected : Nat → Option Direction}
    {primary secondary potential : Nat → Nat → Int}
    {lower point upper scanCoordinate beforeFinish : Nat}
    {after before rejectedAfter rejectedBefore : Direction}
    (witness : ∃ boundary, lower < boundary ∧ boundary < upper ∧
      selected boundary ≠ none)
    (directionsAfter : ∀ direction,
      direction = after ∨ direction = rejectedAfter)
    (directionsBefore : ∀ direction,
      direction = before ∨ direction = rejectedBefore)
    (scanPositive : 0 < scanCoordinate)
    (pointInside : lower < point ∧ point < upper)
    (beforeFinishLe : beforeFinish ≤ point)
    (beforeFinishUpper : beforeFinish < upper)
    (boundaryLeBeforeFinish : ∀ boundary,
      lower < boundary → boundary < point → boundary ≤ beforeFinish)
    (rejectedAfterWeight : ∀ boundary,
      selected boundary = some rejectedAfter →
        primary scanCoordinate boundary = -1 ∨
          secondary scanCoordinate boundary = -1)
    (rejectedBeforeWeight : ∀ boundary,
      selected boundary = some rejectedBefore →
        primary scanCoordinate boundary = 1 ∨
          secondary scanCoordinate boundary = 1)
    (shared : ∀ scan position,
      primary scan position = secondary (scan + 1) position)
    (pointHeight : ∀ scan,
      scan = scanCoordinate ∨ scan + 1 = scanCoordinate →
        potential scan point = 1)
    (beforeHeight : ∀ scan,
      scan = scanCoordinate ∨ scan + 1 = scanCoordinate →
        potential scan beforeFinish = 1)
    (step : ∀ scan position,
      scan = scanCoordinate ∨ scan + 1 = scanCoordinate →
      lower < position → position < upper →
        potential scan position =
          potential scan (position - 1) + primary scan position)
    (zeroWeights : ∀ position, selected position = none →
      primary scanCoordinate position = 0 ∧
        secondary scanCoordinate position = 0)
    (positive : ∀ scan position,
      scan = scanCoordinate ∨ scan + 1 = scanCoordinate →
      lower ≤ position → position < upper → 1 ≤ potential scan position) :
    selected point ≠ none ∨
      (∃ boundary, point < boundary ∧ boundary < upper ∧
        selected boundary = some after ∧
        ∀ value, point < value → value < boundary →
          selected value = none) ∨
      (∃ boundary, lower < boundary ∧ boundary < point ∧
        selected boundary = some before ∧
        ∀ value, boundary < value → value < point →
          selected value = none) := by
  apply boundary_of_exists_selected witness
  · intro boundary pointBoundary boundaryUpper boundarySelected between
    apply selected_after_eq_of_negative_rejected directionsAfter scanPositive
      pointBoundary boundarySelected (rejectedAfterWeight boundary) shared
      pointHeight
    · intro scan position scanEq lowerPosition upperPosition
      exact step scan position scanEq (by omega) (by omega)
    · intro position pointPosition positionBoundary
      exact zeroWeights position (between position pointPosition positionBoundary)
    · intro scan scanEq
      exact positive scan boundary scanEq (by omega) boundaryUpper
  · intro boundary boundaryLower boundaryPoint boundarySelected between pointClear
    apply selected_before_eq_of_positive_rejected directionsBefore scanPositive
      (boundaryLeBeforeFinish boundary boundaryLower boundaryPoint)
      boundarySelected (rejectedBeforeWeight boundary) shared beforeHeight
    · intro scan position scanEq boundaryPosition positionFinish
      exact step scan position scanEq (by omega) (by omega)
    · intro position boundaryPosition positionFinish
      apply zeroWeights
      by_cases positionPoint : position = point
      · simpa [positionPoint] using pointClear
      · exact between position boundaryPosition (by omega)
    · intro scan scanEq
      exact positive scan (boundary - 1) scanEq (by omega) (by omega)

private theorem ValidShadeGrid.vertical_west_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .west) :
    upWeightAt stateGrid x y = -1 ∨ downWeightAt stateGrid x y = -1 := by
  simpa [upWeightAt, downWeightAt] using
    vertical_west_has_negative_weight _ _ _
      (valid.allowed x y) hselected

private theorem ValidShadeGrid.vertical_east_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .east) :
    upWeightAt stateGrid x y = 1 ∨ downWeightAt stateGrid x y = 1 := by
  simpa [upWeightAt, downWeightAt] using
    vertical_east_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem faceHeight_step_right
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {row position : Nat} (rowSouth : quarterSouth south ≤ row)
    (westPosition : quarterWest west < position)
    (eastPosition : position < quarterEast east) :
    faceHeight stateGrid position (quarterSouth south)
        (row - quarterSouth south) =
      faceHeight stateGrid (position - 1) (quarterSouth south)
          (row - quarterSouth south) + upWeightAt stateGrid position row := by
  have difference := CycleShade.faceHeight_sub_left
    shaded cycle valid (column := position)
      (offset := row - quarterSouth south) westPosition eastPosition
  rw [show quarterSouth south + (row - quarterSouth south) = row by omega]
    at difference
  omega

private theorem ValidShadeGrid.horizontal_south_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .south) :
    rightWeightAt stateGrid x y = -1 ∨ leftWeightAt stateGrid x y = -1 := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_south_has_negative_weight _ _ _
      (valid.allowed x y) hselected

private theorem ValidShadeGrid.horizontal_north_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .north) :
    rightWeightAt stateGrid x y = 1 ∨ leftWeightAt stateGrid x y = 1 := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_north_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem faceHeight_step_up {scan position : Nat}
    (southPosition : quarterSouth south < position) :
    faceHeight stateGrid scan (quarterSouth south)
        (position - quarterSouth south) =
      faceHeight stateGrid scan (quarterSouth south)
          (position - 1 - quarterSouth south) +
        rightWeightAt stateGrid scan position := by
  have offset : position - quarterSouth south =
      (position - 1 - quarterSouth south) + 1 := by omega
  rw [offset, faceHeight]
  congr 2
  omega

/-- A valid light Robinson board has the outward-facing nearest boundaries
required by the obstruction-signal argument. -/
theorem CycleShade.geometry
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    Geometry
      indexGrid stateGrid west east south north where
  verticalBoundary := by
    intro column row hwest heast hsouth hnorth free notFree
    let selected := fun y =>
      selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (stateGrid column y)
    have witness : ∃ boundary,
        quarterSouth south < boundary ∧ boundary < quarterNorth north ∧
          selected boundary ≠ none := by
      simp only [IsFreeColumn] at notFree
      push Not at notFree
      exact notFree
    have height (scan) (scanEq : scan = column ∨ scan + 1 = column) :
        faceHeight stateGrid scan (quarterSouth south) (row - quarterSouth south) = 1 :=
      CycleShade.faceHeight_eq_one_of_freeRow shaded cycle valid
        (by rcases scanEq with h | h <;> omega) (by rcases scanEq with h | h <;> omega)
        (le_of_lt hsouth) hnorth free
    apply boundary_of_unit_height
      (selected := selected)
      (primary := fun scan y => rightWeightAt stateGrid scan y)
      (secondary := fun scan y => leftWeightAt stateGrid scan y)
      (potential := fun scan y => faceHeight stateGrid scan (quarterSouth south)
        (y - quarterSouth south))
      (lower := quarterSouth south) (point := row)
      (upper := quarterNorth north) (scanCoordinate := column)
      (beforeFinish := row)
      (after := .north) (before := .south)
      (rejectedAfter := .south) (rejectedBefore := .north) witness
    · rintro (_ | _) <;> simp
    · rintro (_ | _) <;> simp
    · omega
    · exact ⟨hsouth, hnorth⟩
    · omega
    · exact hnorth
    · omega
    · exact fun _ => ValidShadeGrid.horizontal_south_has_negative_weightAt valid
    · exact fun _ => ValidShadeGrid.horizontal_north_has_positive_weightAt valid
    · exact ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ valid
    · exact height
    · exact height
    · exact fun _ _ _ positionSouth _ => faceHeight_step_up positionSouth
    · exact fun _ => ValidShadeGrid.horizontal_none_weightsAt_zero valid
    · intro scan position scanEq positionSouth positionNorth
      exact CycleShade.one_le_faceHeight_at
        shaded cycle valid
        (by rcases scanEq with h | h <;> omega)
        (by rcases scanEq with h | h <;> omega)
        (row := position) positionSouth positionNorth
  horizontalBoundary := by
    intro column row hwest heast hsouth hnorth free notFree
    let selected := fun x => selectedVerticalFor
      (componentAt indexGrid x row) (quadrantAt x row) (stateGrid x row)
    have witness : ∃ boundary,
        quarterWest west < boundary ∧ boundary < quarterEast east ∧
          selected boundary ≠ none := by
      simp only [IsFreeRow] at notFree
      push Not at notFree
      exact notFree
    apply boundary_of_unit_height
      (selected := selected)
      (primary := fun scan x => upWeightAt stateGrid x scan)
      (secondary := fun scan x => downWeightAt stateGrid x scan)
      (potential := fun scan x => faceHeight stateGrid x (quarterSouth south)
        (scan - quarterSouth south))
      (lower := quarterWest west) (point := column)
      (upper := quarterEast east) (scanCoordinate := row)
      (beforeFinish := column - 1)
      (after := .east) (before := .west)
      (rejectedAfter := .west) (rejectedBefore := .east) witness
    · rintro (_ | _) <;> simp
    · rintro (_ | _) <;> simp
    · omega
    · exact ⟨hwest, heast⟩
    · omega
    · omega
    · omega
    · exact fun _ => ValidShadeGrid.vertical_west_has_negative_weightAt valid
    · exact fun _ => ValidShadeGrid.vertical_east_has_positive_weightAt valid
    · exact fun scan x => ValidShadeGrid.upWeightAt_eq_downWeightAt_succ valid x scan
    · intro scan scanEq
      exact CycleShade.faceHeight_eq_one_right_of_freeColumn
        shaded cycle valid (column := column) (row := scan)
        (le_of_lt hwest) heast
        (by rcases scanEq with h | h <;> omega)
        (by rcases scanEq with h | h <;> omega) free
    · intro scan scanEq
      exact CycleShade.faceHeight_eq_one_left_of_freeColumn
        shaded cycle valid (column := column) (row := scan)
        hwest heast
        (by rcases scanEq with h | h <;> omega)
        (by rcases scanEq with h | h <;> omega) free
    · intro scan position scanEq positionWest positionEast
      exact faceHeight_step_right shaded cycle valid
        (by rcases scanEq with h | h <;> omega) positionWest positionEast
    · exact fun _ => ValidShadeGrid.vertical_none_weightsAt_zero valid
    · intro scan position scanEq positionWest positionEast
      exact CycleShade.one_le_faceHeight_at
        shaded cycle valid (column := position) (row := scan)
        positionWest positionEast
        (by rcases scanEq with h | h <;> omega)
        (by rcases scanEq with h | h <;> omega)

end Cslib.WangTile.Robinson
