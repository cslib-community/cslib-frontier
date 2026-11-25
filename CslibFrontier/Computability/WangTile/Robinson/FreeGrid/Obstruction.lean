/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.FreeGrid.Basic

/-!
# Obstruction signals at Robinson free-line crossings

Inside a uniformly light red board, matching obstruction signals vanish along every free
row and column. Conversely, a non-free line crossing a free line receives a nonempty signal
from its nearest outward-facing selected boundary. These two facts distinguish payload
crossings from the intervening horizontal and vertical wires.

## Main definitions

* `MarkedFreeGrid.routedGrid`: every consecutive marked free grid
  inside a light board gives the routed grid consumed by generic seed removal.

The canonical patch construction supplies a plane instance satisfying these hypotheses.

## References

After the obstruction argument in [JeandelVanier2020], §3.3, pp. 27–28, Figure 18.
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, `Closed104.ShadedLightBoardSignals`, `ShadedLightBoardFreeLines`,
`SignalCorridors`, `ShadedObstructionGeometry`, and `ShadedPayloadCorridors`.
In particular, the nearest-boundary argument retains the source theorem
`ShadedObstructionGeometry.Geometry.crossingObstruction`; the routed-grid construction replaces
`ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive` by separating scaffold
geometry from the generic payload propagation in `Routing`. The local signal rule, strict
board intervals and arbitrary-plane scope are unchanged.
-/

public section
namespace Cslib.WangTile.Robinson

private theorem flow_transmits {before after : SignalFlow}
    (allowed : flowAllowed none before after = true) : before = after := by
  simpa only [flowAllowed, decide_eq_true_eq] using allowed

private theorem flow_clear_between
    (before after : ℕ → SignalFlow) {lower upper position : ℕ}
    (hleft : lower < position) (hright : position < upper)
    (matching : ∀ x, after x = before (x + 1))
    (transmit : ∀ x, lower < x → x < upper → before x = after x)
    (left_rule : after lower ≠ .forward) (right_rule : before upper ≠ .backward) :
    before position = .none ∧ after position = .none := by
  have first : after lower = .none := by
    cases h : after lower
    · rfl
    · exact (left_rule h).elim
    · exact (right_rule ((value_between id after before (hleft.trans hright)
        (fun x _ _ => matching x) transmit).symm.trans h)).elim
  have at_position := (value_between id after before hleft (fun x _ _ => matching x)
    fun x hl hx => transmit x hl (hx.trans hright)).symm.trans first
  exact ⟨at_position, (transmit position hleft hright).symm.trans at_position⟩

private theorem flow_blocked_of_boundary
    {δ : Type*} (selected : ℕ → Option δ) (coding : Option δ → Option Bool)
    (positive negative : δ) (coding_none : coding none = none)
    (coding_live : ∀ direction, coding (some direction) ≠ none)
    (coding_positive : coding (some positive) = some true)
    (coding_negative : coding (some negative) = some false)
    (before after : ℕ → SignalFlow)
    (matching : ∀ x, after x = before (x + 1))
    (allowed : ∀ x, flowAllowed (coding (selected x)) (before x) (after x) = true)
    {lower upper position : ℕ}
    (boundary : selected position ≠ none ∨
      (∃ bound, position < bound ∧ bound < upper ∧ selected bound = some positive ∧
        ∀ x, position < x → x < bound → selected x = none) ∨
      (∃ bound, lower < bound ∧ bound < position ∧ selected bound = some negative ∧
        ∀ x, bound < x → x < position → selected x = none)) :
    ¬ (before position = .none ∧ after position = .none) := by
  intro clear
  have step_eq {lo hi : ℕ} (hle : lo < hi)
      (between : ∀ x, lo < x → x < hi → selected x = none) : after lo = before hi :=
    value_between (fun x => x) after before hle (fun x _ _ => matching x)
      fun x hl hr => flow_transmits (by simpa only [between x hl hr, coding_none] using allowed x)
  rcases boundary with here | ⟨bound, hbound, _, selected_bound, between⟩ |
      ⟨bound, _, hbound, selected_bound, between⟩
  · have local_rule := allowed position
    rcases h : coding (selected position) with _ | (_ | _)
    · rcases hs : selected position with _ | d
      · exact here hs
      · exact coding_live d (hs ▸ h)
    all_goals simp [h, flowAllowed, clear.1, clear.2] at local_rule
  · have local_rule := allowed bound
    simp only [selected_bound, coding_positive, flowAllowed, decide_eq_true_eq] at local_rule
    exact local_rule.1 ((step_eq hbound between).symm.trans clear.2)
  · have local_rule := allowed bound
    simp only [selected_bound, coding_negative, flowAllowed, decide_eq_true_eq] at local_rule
    exact local_rule.1 ((step_eq hbound between).trans clear.1)

private theorem selected_horizontal_of_lane
    (component : Thick) (quadrant : Quadrant) (shade : ShadeState) (positive : Bool)
    (lane : containsLine component (if positive then .r1 else .r3) = true)
    (phase : quadrant.yBit = positive) (value : shade.west = some .light) :
    selectedHorizontalFor component quadrant shade =
      some (if positive then .north else .south) := by
  simp only [selectedHorizontalFor, horizontalShade?, value, ↓reduceIte]
  cases positive <;> cases component <;> cases quadrant <;>
    simp_all [containsLine, horizontalInterior?, Quadrant.yBit, redHorizontalAt]

private theorem selected_vertical_of_lane
    (component : Thick) (quadrant : Quadrant) (shade : ShadeState) (positive : Bool)
    (lane : containsLine component (if positive then .r0 else .r2) = true)
    (phase : quadrant.xBit = positive) (value : shade.south = some .light) :
    selectedVerticalFor component quadrant shade =
      some (if positive then .east else .west) := by
  simp only [selectedVerticalFor, verticalShade?, value, ↓reduceIte]
  cases positive <;> cases component <;> cases quadrant <;>
    simp_all [containsLine, verticalInterior?, Quadrant.xBit, redVerticalAt]

namespace ValidSignalGrid

variable {indexGrid : ℕ → ℕ → Index} {shadeGrid : ℕ → ℕ → ShadeState}
  {signalGrid : ℕ → ℕ → SignalState}

private theorem horizontal_allowed (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    (x y : ℕ) :
    SignalState.horizontalAllowed
      (selectedVerticalFor (componentAt indexGrid x y) (quadrantAt x y)
        (shadeGrid x y)) (signalGrid x y) = true :=
  ((Bool.and_eq_true _ _).mp (valid.signalAllowed x y)).1

private theorem vertical_allowed (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    (x y : ℕ) :
    SignalState.verticalAllowed
      (selectedHorizontalFor (componentAt indexGrid x y) (quadrantAt x y)
        (shadeGrid x y)) (signalGrid x y) = true :=
  ((Bool.and_eq_true _ _).mp (valid.signalAllowed x y)).2

end ValidSignalGrid

section

variable {indexGrid : ℕ → ℕ → Index} {shadeGrid : ℕ → ℕ → ShadeState}
  {signalGrid : ℕ → ℕ → SignalState} {west east south north : ℕ}

private theorem CycleShade.horizontal_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    (positive : Bool) {x : ℕ} (hw : quarterWest west < x) (he : x < quarterEast east) :
    selectedHorizontalFor
      (componentAt indexGrid x (if positive then quarterSouth south else quarterNorth north))
      (quadrantAt x (if positive then quarterSouth south else quarterNorth north))
      (shadeGrid x (if positive then quarterSouth south else quarterNorth north)) =
      some (if positive then .north else .south) := by
  have hw' : west < x / 2 := by simp only [quarterWest] at hw; omega
  have he' : x / 2 < east := by simp only [quarterEast] at he; omega
  cases positive
  · exact selected_horizontal_of_lane _ _ _ false
      (by simpa [componentAt, quarterNorth, show 2 * north / 2 = north by omega] using
        cycle.northLane (x / 2) hw' he')
      (quadrantAt_quarterNorth_yBit x north) (shaded.north_at cycle valid.shadeValid hw he).1
  · exact selected_horizontal_of_lane _ _ _ true
      (by simpa [componentAt, quarterSouth, show (2 * south + 1) / 2 = south by omega] using
        cycle.southLane (x / 2) hw' he')
      (quadrantAt_quarterSouth_yBit x south) (shaded.south_at cycle valid.shadeValid hw he).1

private theorem CycleShade.vertical_selected
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    (positive : Bool) {y : ℕ} (hs : quarterSouth south < y) (hn : y < quarterNorth north) :
    selectedVerticalFor
      (componentAt indexGrid (if positive then quarterWest west else quarterEast east) y)
      (quadrantAt (if positive then quarterWest west else quarterEast east) y)
      (shadeGrid (if positive then quarterWest west else quarterEast east) y) =
      some (if positive then .east else .west) := by
  have hs' : south < y / 2 := by simp only [quarterSouth] at hs; omega
  have hn' : y / 2 < north := by simp only [quarterNorth] at hn; omega
  cases positive
  · exact selected_vertical_of_lane _ _ _ false
      (by simpa [componentAt, quarterEast, show 2 * east / 2 = east by omega] using
        cycle.eastLane (y / 2) hs' hn')
      (quadrantAt_quarterEast_xBit east y) (shaded.east_at cycle valid.shadeValid hs hn).1
  · exact selected_vertical_of_lane _ _ _ true
      (by simpa [componentAt, quarterWest, show (2 * west + 1) / 2 = west by omega] using
        cycle.westLane (y / 2) hs' hn')
      (quadrantAt_quarterWest_xBit west y) (shaded.west_at cycle valid.shadeValid hs hn).1

/-- Both horizontal signal edges vanish at each strict interior point of a free board row. -/
private theorem CycleShade.clear_at_free_row
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    {x y : ℕ} (hs : quarterSouth south < y) (hn : y < quarterNorth north)
    (free : IsFreeRow indexGrid shadeGrid west east y)
    (hw : quarterWest west < x) (he : x < quarterEast east) :
    (signalGrid x y).west = .none ∧ (signalGrid x y).east = .none := by
  have hend (b : Bool) := by
    have h := valid.horizontal_allowed (if b then quarterWest west else quarterEast east) y
    rw [shaded.vertical_selected cycle valid b hs hn] at h
    exact h
  refine flow_clear_between (fun x => (signalGrid x y).west)
    (fun x => (signalGrid x y).east) hw he (fun x => valid.horizontal x y)
    (fun x hxw hxe => flow_transmits (by
      simpa only [free x hxw hxe, SignalState.horizontalAllowed, horizontalInteriorCode]
        using valid.horizontal_allowed x y)) ?_ ?_
  · have h := hend true
    simp only [↓reduceIte, SignalState.horizontalAllowed, horizontalInteriorCode, flowAllowed,
      decide_eq_true_eq] at h
    exact h.2
  · have h := hend false
    simp only [Bool.false_eq_true, ↓reduceIte, SignalState.horizontalAllowed,
      horizontalInteriorCode, flowAllowed, decide_eq_true_eq] at h
    exact h.2

/-- Both vertical signal edges vanish at each strict interior point of a free board column. -/
private theorem CycleShade.clear_at_free_column
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    {x y : ℕ} (hw : quarterWest west < x) (he : x < quarterEast east)
    (free : IsFreeColumn indexGrid shadeGrid south north x)
    (hs : quarterSouth south < y) (hn : y < quarterNorth north) :
    (signalGrid x y).south = .none ∧ (signalGrid x y).north = .none := by
  have hend (b : Bool) := by
    have h := valid.vertical_allowed x (if b then quarterSouth south else quarterNorth north)
    rw [shaded.horizontal_selected cycle valid b hw he] at h
    exact h
  refine flow_clear_between (fun y => (signalGrid x y).south)
    (fun y => (signalGrid x y).north) hs hn (fun y => valid.vertical x y)
    (fun y hys hyn => flow_transmits (by
      simpa only [free y hys hyn, SignalState.verticalAllowed, verticalInteriorCode]
        using valid.vertical_allowed x y)) ?_ ?_
  · have h := hend true
    simp only [↓reduceIte, SignalState.verticalAllowed, verticalInteriorCode, flowAllowed,
      decide_eq_true_eq] at h
    exact h.2
  · have h := hend false
    simp only [Bool.false_eq_true, ↓reduceIte, SignalState.verticalAllowed,
      verticalInteriorCode, flowAllowed, decide_eq_true_eq] at h
    exact h.2

/-- Every crossing of free rows and columns has all four obstruction signals absent. -/
private theorem CycleShade.clear_at_free_crossing
    (shaded : CycleShade shadeGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid)
    {x y : ℕ} (hw : quarterWest west < x) (he : x < quarterEast east)
    (hs : quarterSouth south < y) (hn : y < quarterNorth north)
    (row : IsFreeRow indexGrid shadeGrid west east y)
    (column : IsFreeColumn indexGrid shadeGrid south north x) :
    signalGrid x y = SignalState.clear := by
  obtain ⟨hw', he'⟩ := shaded.clear_at_free_row cycle valid hs hn row hw he
  obtain ⟨hs', hn'⟩ := shaded.clear_at_free_column cycle valid hw he column hs hn
  cases h : signalGrid x y
  simp_all [SignalState.clear]

end

section

/-- Each non-free direction is obstructed wherever it crosses a free line inside the board. -/
private structure CrossingObstruction (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → ShadeState) (signalGrid : ℕ → ℕ → SignalState)
    (west east south north : ℕ) : Prop where
  /-- A non-free column at a free row has at least one nonempty vertical signal. -/
  verticalBlocked : ∀ {column row : ℕ},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    IsFreeRow indexGrid shadeGrid west east row →
    ¬ IsFreeColumn indexGrid shadeGrid south north column →
      ¬ ((signalGrid column row).south = .none ∧ (signalGrid column row).north = .none)
  /-- A non-free row at a free column has at least one nonempty horizontal signal. -/
  horizontalBlocked : ∀ {column row : ℕ},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    IsFreeColumn indexGrid shadeGrid south north column →
    ¬ IsFreeRow indexGrid shadeGrid west east row →
      ¬ ((signalGrid column row).west = .none ∧ (signalGrid column row).east = .none)

/-- Outward-facing nearest selected boundaries force every non-free crossing to be blocked. -/
private theorem Geometry.crossingObstruction
    {indexGrid : ℕ → ℕ → Index} {shadeGrid : ℕ → ℕ → ShadeState}
    {signalGrid : ℕ → ℕ → SignalState} {west east south north : ℕ}
    (geometry : Geometry indexGrid shadeGrid west east south north)
    (valid : ValidSignalGrid indexGrid shadeGrid signalGrid) :
    CrossingObstruction indexGrid shadeGrid signalGrid west east south north :=
  ⟨fun hw he hs hn free not_free => flow_blocked_of_boundary
      (fun y => selectedHorizontalFor
        (componentAt indexGrid _ y) (quadrantAt _ y) (shadeGrid _ y))
      verticalInteriorCode .north .south rfl (by rintro (_ | _) <;> decide) rfl rfl
      (fun y => (signalGrid _ y).south) (fun y => (signalGrid _ y).north)
      (fun y => valid.vertical _ y) (fun y => valid.vertical_allowed _ y)
      (geometry.verticalBoundary hw he hs hn free not_free),
    fun hw he hs hn free not_free => flow_blocked_of_boundary
      (fun x => selectedVerticalFor
        (componentAt indexGrid x _) (quadrantAt x _) (shadeGrid x _))
      horizontalInteriorCode .east .west rfl (by rintro (_ | _) <;> decide) rfl rfl
      (fun x => (signalGrid x _).west) (fun x => (signalGrid x _).east)
      (fun x => valid.horizontal x _) (fun x => valid.horizontal_allowed x _)
      (geometry.horizontalBoundary hw he hs hn free not_free)⟩

end

/-- Consecutive free lines in a light Robinson board form a routed grid in the original plane.
The marker becomes the seeded southwest crossing and every intervening cell is a wire. -/
def MarkedFreeGrid.routedGrid
    {P : Cslib.WangTile.Plane scaffold.tiles} (D : DecodedPlane P)
    (R : QuarterPlane.Regrouped D.quarterPlane) (a b : ℤ)
    {west east south north n : ℕ}
    (grid : MarkedFreeGrid
      (fun i j => R.parent.index (a + i) (b + j))
      (fun x y => (D.siteGrid R a b x y).shade) west east south north n)
    (cycle : CycleOn (fun i j => R.parent.index (a + i) (b + j)) west east south north)
    (shaded : CycleShade (fun x y => (D.siteGrid R a b x y).shade)
      west east south north .light) : RoutedGrid scaffold P n :=
  let ox := R.origin.1 + 2 * a
  let oy := R.origin.2 + 2 * b
  have valid := D.validGrid R a b
  have geometry := CycleShade.geometry shaded cycle valid.shadeValid
  have obstruction := geometry.crossingObstruction valid
  have role (x y : ℕ) :
      scaffold.role (P.tile (ox + x) (oy + y)) =
        ShadedSite.routeRole (ShadedSite.tile (D.siteGrid R a b x y)) := by
    simpa only [scaffold_role, DecodedPlane.siteGrid, ox, oy] using
      (congrArg ShadedSite.routeRole (D.tile_eq (ox + x) (oy + y))).symm
  have crossing_clear (i j : Fin (n + 1)) :
      (D.siteGrid R a b (grid.column i) (grid.row j)).signal = SignalState.clear :=
    CycleShade.clear_at_free_crossing shaded cycle valid
      (grid.column_west i) (grid.column_east i) (grid.row_south j) (grid.row_north j)
      (grid.freeRow j) (grid.freeColumn i)
  { column := fun i => ox + grid.column i
    row := fun j => oy + grid.row j
    column_strictMono := fun _ _ hij => by
      dsimp only; exact Int.add_lt_add_left (Int.ofNat_lt.mpr (grid.column_strictMono hij)) ox
    row_strictMono := fun _ _ hij => by
      dsimp only; exact Int.add_lt_add_left (Int.ofNat_lt.mpr (grid.row_strictMono hij)) oy
    crossing := fun i j => by
      simp only [role]; exact (ShadedSite.crossing_iff _).2 (crossing_clear i j)
    corner := by
      rw [role]
      exact (ShadedSite.corner_iff _).2
        ⟨crossing_clear 0 0, (R.quarter_at a b (grid.column 0) (grid.row 0)).trans grid.marker⟩
    horizontal := by
      intro i j x hl hr
      let k := (x - ox).toNat
      have hx : ox + k = x := by dsimp only [k]; omega
      have left : grid.column i.castSucc < k := by dsimp only [k]; omega
      have right : k < grid.column i.succ := by dsimp only [k]; omega
      have hw := (grid.column_west i.castSucc).trans left
      have he := right.trans (grid.column_east i.succ)
      change scaffold.role (P.tile x (oy + grid.row j)) = .horizontal
      rw [← hx, role]
      exact (ShadedSite.horizontal_iff_role _).2
        ⟨CycleShade.clear_at_free_row shaded cycle valid
           (grid.row_south j) (grid.row_north j) (grid.freeRow j) hw he,
         obstruction.verticalBlocked hw he (grid.row_south j) (grid.row_north j)
           (grid.freeRow j) (grid.noFreeColumnBetween i k left right)⟩
    vertical := by
      intro i j y hl hr
      let k := (y - oy).toNat
      have hy : oy + k = y := by dsimp only [k]; omega
      have lower : grid.row j.castSucc < k := by dsimp only [k]; omega
      have upper : k < grid.row j.succ := by dsimp only [k]; omega
      have hs := (grid.row_south j.castSucc).trans lower
      have hn := upper.trans (grid.row_north j.succ)
      change scaffold.role (P.tile (ox + grid.column i) y) = .vertical
      rw [← hy, role]
      exact (ShadedSite.vertical_iff_role _).2
        ⟨obstruction.horizontalBlocked (grid.column_west i) (grid.column_east i)
           hs hn (grid.freeColumn i) (grid.noFreeRowBetween j k lower upper),
         CycleShade.clear_at_free_column shaded cycle valid
           (grid.column_west i) (grid.column_east i) (grid.freeColumn i) hs hn⟩ }

end Cslib.WangTile.Robinson
