/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Certificates

/-!
# Red-wire shades and their propagation

Each red edge of a Robinson quarter carries a light or dark shade. Straight wires and
corners preserve shades; crossings require opposite shades. A locally allowed matching
assignment therefore respects the parity of each red-graph path, and every rectangular
oriented red cycle carries one shade around its boundary.

The coarsening results assume `ValidShadeGrid (iterateRefine 2 grid) fine`.
Existence of such a decoration is established only by the later `Canonical/*`
construction; this module proves preservation conditional on that hypothesis.

## Main definitions

* `ShadeState` and `allowedFor`: quarter shades and the local decoration rule.
* `ValidShadeGrid`: a locally allowed matching shade assignment.
* `CycleShade`: uniform shades on the inward corners of a rectangular board.
* `ValidPortLabeling`: a parity-consistent labeling with the prescribed incidence.

## Main results

* `CycleOn.exists_cycleShade`: every oriented red cycle has a uniform shade.
* `CycleShade.south_at` and the other side lemmas propagate that shade along
  the complete boundary.
* `Path.sound`: path parity determines shade equality or opposition.
* `ValidPortLabeling.validShadeGrid`: consistent port labels give valid shades.
* `ValidShadeGrid.coarsen` and `CycleShade.coarsen`: coarsening through two substitutions
  preserves matching shade rules and the shade of every oriented cycle.

## References

The shading rules are after [JeandelVanier2020], §3.3, Figures 17–18 (manuscript pp. 24, 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, modules `Closed104.RedShades`, `RedShadePaths`, `RedShadeCycles` and
`RedShadeGraph`, `RedShadeGraphCoarsening`, `SignalCorridors`, `Signals` and `ShadedSignals`.
These are local decoration and propagation steps of the corrected Robinson scaffold, not the
seed-removal theorem.
-/

public section
namespace Cslib.WangTile.Robinson

-- Finite downstream checks need the generated equality helpers through ordinary imports.
@[expose] public section
/-- The two shades of a red wire. -/
inductive Shade where
  | light
  | dark
deriving DecidableEq
end

namespace Shade

/-- Both shades, in light/dark order for finite enumeration. -/
@[expose] def all : List Shade := [.light, .dark]

/-- Every shade occurs in the finite enumeration. -/
@[simp] theorem mem_all (shade : Shade) : shade ∈ all := by
  cases shade <;> decide

/-- The two wire shades form a finite type. -/
instance : Fintype Shade := Fintype.ofList all mem_all

/-- Exchange the two red-wire shades. -/
@[expose] def opposite : Shade → Shade
  | .light => .dark
  | .dark => .light

/-- Exchanging the shade twice is the identity. -/
@[simp] theorem opposite_opposite (shade : Shade) :
    shade.opposite.opposite = shade := by
  cases shade <;> rfl

/-- Distinct shades are opposites. -/
theorem eq_opposite_of_ne {first second : Shade} (hne : first ≠ second) :
    second = first.opposite := by
  cases first <;> cases second <;> simp_all [opposite]

end Shade

@[expose] public section
/-- Optional shade carried by each edge of one quarter tile. -/
structure ShadeState where
  /-- Shade on the west edge, absent when there is no red wire. -/
  west : Option Shade
  /-- Shade on the east edge. -/
  east : Option Shade
  /-- Shade on the south edge. -/
  south : Option Shade
  /-- Shade on the north edge. -/
  north : Option Shade
deriving DecidableEq
end

namespace ShadeState

/-- Every four-edge shade state, in west/east/south/north order. -/
@[expose] def all : List ShadeState :=
  let edgeValues := none :: Shade.all.map some
  edgeValues.flatMap fun west =>
    edgeValues.flatMap fun east =>
      edgeValues.flatMap fun south =>
        edgeValues.map fun north => ⟨west, east, south, north⟩

private theorem mem_edgeValues (value : Option Shade) :
    value ∈ (none :: Shade.all.map some) := by
  rcases value with _ | shade
  · simp
  · simp

/-- Every four-edge shade state occurs in the enumeration. -/
@[simp] theorem mem_all (state : ShadeState) : state ∈ all := by
  rcases state with ⟨west, east, south, north⟩
  simp only [all, List.mem_flatMap, List.mem_map]
  exact ⟨west, mem_edgeValues _, east, mem_edgeValues _, south, mem_edgeValues _,
    north, mem_edgeValues _, rfl⟩

end ShadeState

/-- Local rule with the thick component made explicit for proof reuse. -/
@[expose] def allowedFor (component : Thick) (quadrant : Quadrant) (state : ShadeState) : Bool :=
  decide (Option.isSome state.west = hasWest component quadrant) &&
    decide (Option.isSome state.east = hasEast component quadrant) &&
    decide (Option.isSome state.south = hasSouth component quadrant) &&
    decide (Option.isSome state.north = hasNorth component quadrant) &&
    (if hasHorizontal component quadrant then decide (state.west = state.east)
      else true) &&
    (if hasVertical component quadrant then decide (state.south = state.north)
      else true) &&
    (if cornerEast component quadrant && cornerSouth component quadrant then
      decide (state.east = state.south) else true) &&
    (if cornerEast component quadrant && cornerNorth component quadrant then
      decide (state.east = state.north) else true) &&
    (if cornerWest component quadrant && cornerSouth component quadrant then
      decide (state.west = state.south) else true) &&
    (if cornerWest component quadrant && cornerNorth component quadrant then
      decide (state.west = state.north) else true) &&
    (if hasHorizontal component quadrant && hasVertical component quadrant then
      decide (state.west ≠ state.south) else true)

/-- The incidence, transmission and crossing conditions of one allowed quarter. -/
structure Allowed (component : Thick) (quadrant : Quadrant) (state : ShadeState) : Prop where
  /-- West labels are present exactly where the red wire meets the west edge. -/
  west_present : state.west.isSome = hasWest component quadrant
  /-- East labels have exactly the prescribed incidence. -/
  east_present : state.east.isSome = hasEast component quadrant
  /-- South labels have exactly the prescribed incidence. -/
  south_present : state.south.isSome = hasSouth component quadrant
  /-- North labels have exactly the prescribed incidence. -/
  north_present : state.north.isSome = hasNorth component quadrant
  /-- A horizontal wire preserves its shade. -/
  horizontal_eq : hasHorizontal component quadrant = true → state.west = state.east
  /-- A vertical wire preserves its shade. -/
  vertical_eq : hasVertical component quadrant = true → state.south = state.north
  /-- A southeast corner preserves its shade. -/
  east_south_corner_eq : cornerEast component quadrant = true →
    cornerSouth component quadrant = true → state.east = state.south
  /-- A northeast corner preserves its shade. -/
  east_north_corner_eq : cornerEast component quadrant = true →
    cornerNorth component quadrant = true → state.east = state.north
  /-- A southwest corner preserves its shade. -/
  west_south_corner_eq : cornerWest component quadrant = true →
    cornerSouth component quadrant = true → state.west = state.south
  /-- A northwest corner preserves its shade. -/
  west_north_corner_eq : cornerWest component quadrant = true →
    cornerNorth component quadrant = true → state.west = state.north
  /-- The two wires at a crossing have opposite shades. -/
  crossing_opposite : hasHorizontal component quadrant = true →
    hasVertical component quadrant = true → state.west ≠ state.south

/-- The Boolean local checker expresses exactly the named shading conditions. -/
theorem allowedFor_iff {component : Thick} {quadrant : Quadrant} {state : ShadeState} :
    allowedFor component quadrant state = true ↔ Allowed component quadrant state := by
  simp only [allowedFor, Bool.and_eq_true, decide_eq_true_eq,
    Bool.ite_eq_true_distrib, ite_true_right, and_imp]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, he⟩, hs⟩, hn⟩, hh⟩, hv⟩, hes⟩, hen⟩, hws⟩, hwn⟩, hc⟩
    exact ⟨hw, he, hs, hn, hh, hv, hes, hen, hws, hwn, hc⟩
  · rintro ⟨hw, he, hs, hn, hh, hv, hes, hen, hws, hwn, hc⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, he⟩, hs⟩, hn⟩, hh⟩, hv⟩, hes⟩, hen⟩, hws⟩, hwn⟩, hc⟩

/-- Local red-path incidence, propagation, corner, and crossing rules. -/
@[expose] def locallyAllowed (site : QuarterIndex) (state : ShadeState) : Bool :=
  allowedFor (components site.index).thick site.quadrant state

/-- A locally allowed, edge-matching shade assignment over a quarter grid. -/
structure ValidShadeGrid (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → ShadeState) : Prop where
  /-- Every quarter satisfies the local incidence and shade rules. -/
  allowed : ∀ x y,
    locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true
  /-- Adjacent quarters agree on horizontal shared edges. -/
  hmatch : ∀ x y, (stateGrid x y).east = (stateGrid (x + 1) y).west
  /-- Adjacent quarters agree on vertical shared edges. -/
  vmatch : ∀ x y, (stateGrid x y).north = (stateGrid x (y + 1)).south

/-- Read the named local shading conditions at any quarter of a valid grid. -/
theorem ValidShadeGrid.rules
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    Allowed (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) :=
  allowedFor_iff.mp (valid.allowed x y)

/-- Matching and transmission on an interval identify its two boundary values. -/
theorem value_between {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β)
    {start finish : Nat} (hlt : start < finish)
    (hmatch : ∀ position, start ≤ position → position < finish →
      outgoing (state position) = incoming (state (position + 1)))
    (htransmit : ∀ position, start < position → position < finish →
      incoming (state position) = outgoing (state position)) :
    outgoing (state start) = incoming (state finish) := by
  induction finish with
  | zero => omega
  | succ finish ih =>
      by_cases h : start = finish
      · subst finish
        exact hmatch start (by omega) (by omega)
      · exact (ih (by omega) (fun x hx hy => hmatch x hx (by omega))
          (fun x hx hy => htransmit x hx (by omega))).trans
          ((htransmit finish (by omega) (by omega)).trans (hmatch finish (by omega) (by omega)))

/- Parent coordinates refer to tile centers and lanes.  The `quarter*`
coordinates select the inward side of each boundary tile, where the shade
layer actually carries the cycle. -/

/-- Inward quarter coordinate of the west boundary. -/
@[expose] def quarterWest (west : Nat) : Nat := 2 * west + 1
/-- Inward quarter coordinate of the east boundary. -/
@[expose] def quarterEast (east : Nat) : Nat := 2 * east
/-- Inward quarter coordinate of the south boundary. -/
@[expose] def quarterSouth (south : Nat) : Nat := 2 * south + 1
/-- Inward quarter coordinate of the north boundary. -/
@[expose] def quarterNorth (north : Nat) : Nat := 2 * north

/-- Every quarter of a parent has that parent’s thick component. -/
theorem componentAt_double_add (grid : Nat → Nat → Index)
    (x y dx dy : Nat) (hdx : dx < 2) (hdy : dy < 2) :
    componentAt grid (2 * x + dx) (2 * y + dy) =
      indexThick (grid x y) := by
  unfold componentAt
  have hx : (2 * x + dx) / 2 = x := by omega
  have hy : (2 * y + dy) / 2 = y := by omega
  rw [hx, hy]

/-- The inward south quarter has its north-facing bit set. -/
theorem quadrantAt_quarterSouth_yBit (x south : Nat) :
    (quadrantAt x (quarterSouth south)).yBit = true := by
  simp [quadrantAt_yBit, quarterSouth]

/-- The inward north quarter has its south-facing bit set. -/
theorem quadrantAt_quarterNorth_yBit (x north : Nat) :
    (quadrantAt x (quarterNorth north)).yBit = false := by
  simp [quadrantAt_yBit, quarterNorth]

/-- The inward west quarter has its east-facing bit set. -/
theorem quadrantAt_quarterWest_xBit (west y : Nat) :
    (quadrantAt (quarterWest west) y).xBit = true := by
  simp [quadrantAt_xBit, quarterWest]

/-- The inward east quarter has its west-facing bit set. -/
theorem quadrantAt_quarterEast_xBit (east y : Nat) :
    (quadrantAt (quarterEast east) y).xBit = false := by
  simp [quadrantAt_xBit, quarterEast]

/-- The inward southwest quarter joins the east and north red edges. -/
theorem CycleOn.southwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    cornerEast
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true ∧
      cornerNorth
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
  rw [quarterWest, quarterSouth,
    componentAt_double_add grid west south 1 1 (by omega) (by omega),
    cycle.southwest]
  simp [quadrantAt, Quadrant.ofBits,
    cornerEast, cornerNorth]

/-- The inward southeast quarter joins the west and north red edges. -/
theorem CycleOn.southeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    cornerWest
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true ∧
      cornerNorth
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true := by
  rw [quarterEast, quarterSouth,
    show 2 * east = 2 * east + 0 by omega,
    componentAt_double_add grid east south 0 1 (by omega) (by omega),
    cycle.southeast]
  simp [quadrantAt, Quadrant.ofBits,
    cornerWest, cornerNorth]

/-- The inward northeast quarter joins the west and south red edges. -/
theorem CycleOn.northeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    cornerWest
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true ∧
      cornerSouth
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true := by
  rw [quarterEast, quarterNorth,
    show 2 * east = 2 * east + 0 by omega,
    show 2 * north = 2 * north + 0 by omega,
    componentAt_double_add grid east north 0 0 (by omega) (by omega),
    cycle.northeast]
  simp [quadrantAt, Quadrant.ofBits,
    cornerWest, cornerSouth]

/-- The inward northwest quarter joins the east and south red edges. -/
theorem CycleOn.northwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    cornerEast
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true ∧
      cornerSouth
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true := by
  rw [quarterWest, quarterNorth,
    show 2 * north = 2 * north + 0 by omega,
    componentAt_double_add grid west north 1 0 (by omega) (by omega),
    cycle.northwest]
  simp [quadrantAt, Quadrant.ofBits,
    cornerEast, cornerSouth]

/-- Every strict interior quarter on the south side carries a horizontal wire. -/
theorem CycleOn.south_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    hasHorizontal
      (componentAt grid qx (quarterSouth south))
      (quadrantAt qx (quarterSouth south)) = true := by
  have hline := cycle.southLane (qx / 2)
    (by dsimp only [quarterWest, quarterEast] at hwest heast; omega)
    (by dsimp only [quarterWest, quarterEast] at hwest heast; omega)
  simp only [hasHorizontal, quadrantAt_quarterSouth_yBit]
  simpa [redHorizontalAt, componentAt, quarterSouth, Nat.add_div] using hline

/-- Every strict interior quarter on the north side carries a horizontal wire. -/
theorem CycleOn.north_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    hasHorizontal
      (componentAt grid qx (quarterNorth north))
      (quadrantAt qx (quarterNorth north)) = true := by
  have hline := cycle.northLane (qx / 2)
    (by dsimp only [quarterWest, quarterEast] at hwest heast; omega)
    (by dsimp only [quarterWest, quarterEast] at hwest heast; omega)
  simp only [hasHorizontal, quadrantAt_quarterNorth_yBit]
  simpa [redHorizontalAt, componentAt, quarterNorth, Nat.add_div] using hline

/-- Every strict interior quarter on the west side carries a vertical wire. -/
theorem CycleOn.west_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    hasVertical
      (componentAt grid (quarterWest west) qy)
      (quadrantAt (quarterWest west) qy) = true := by
  have hline := cycle.westLane (qy / 2)
    (by dsimp only [quarterSouth, quarterNorth] at hsouth hnorth; omega)
    (by dsimp only [quarterSouth, quarterNorth] at hsouth hnorth; omega)
  simp only [hasVertical, quadrantAt_quarterWest_xBit]
  simpa [redVerticalAt, componentAt, quarterWest, Nat.add_div] using hline

/-- Every strict interior quarter on the east side carries a vertical wire. -/
theorem CycleOn.east_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    hasVertical
      (componentAt grid (quarterEast east) qy)
      (quadrantAt (quarterEast east) qy) = true := by
  have hline := cycle.eastLane (qy / 2)
    (by dsimp only [quarterSouth, quarterNorth] at hsouth hnorth; omega)
    (by dsimp only [quarterSouth, quarterNorth] at hsouth hnorth; omega)
  simp only [hasVertical, quadrantAt_quarterEast_xBit]
  simpa [redVerticalAt, componentAt, quarterEast, Nat.add_div] using hline

/- The four path lemmas turn geometric cycle lanes into transmissive
quarter-level red lines.  Starting from one present corner shade, edge matching
and corner equalities carry it counterclockwise to all four corners. -/

/-- Uniform shade at the four inward quarter corners of an arbitrary board. -/
structure CycleShade (stateGrid : Nat → Nat → ShadeState)
    (west east south north : Nat) (shade : Shade) : Prop where
  /-- East shade at the southwest inward corner. -/
  southwest : (stateGrid (quarterWest west) (quarterSouth south)).east =
    some shade
  /-- West shade at the southeast inward corner. -/
  southeast : (stateGrid (quarterEast east) (quarterSouth south)).west =
    some shade
  /-- West shade at the northeast inward corner. -/
  northeast : (stateGrid (quarterEast east) (quarterNorth north)).west =
    some shade
  /-- East shade at the northwest inward corner. -/
  northwest : (stateGrid (quarterWest west) (quarterNorth north)).east =
    some shade

/-- A shade on one edge of any oriented board propagates to every corner. -/
theorem CycleOn.cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) (shade : Shade)
    (hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east = some shade) :
    CycleShade stateGrid west east south north shade := by
  have hquarterWestEast : quarterWest west < quarterEast east := by
    unfold quarterWest quarterEast
    have := cycle.west_lt_east
    omega
  have hquarterSouthNorth : quarterSouth south < quarterNorth north := by
    unfold quarterSouth quarterNorth
    have := cycle.south_lt_north
    omega
  have hsouth :
      (stateGrid (quarterWest west) (quarterSouth south)).east =
        (stateGrid (quarterEast east) (quarterSouth south)).west := by
    exact value_between (fun x => stateGrid x (quarterSouth south))
      ShadeState.east ShadeState.west hquarterWestEast
      (fun x _ _ => valid.hmatch x (quarterSouth south))
      (fun x hw he => (valid.rules x (quarterSouth south)).horizontal_eq (cycle.south_path hw he))
  have hseNorth :
      (stateGrid (quarterEast east) (quarterSouth south)).north = some shade := by
    rw [← (valid.rules (quarterEast east) (quarterSouth south)).west_north_corner_eq
      (cycle.southeast_corner).1 (cycle.southeast_corner).2]
    exact hsouth.symm.trans hshade
  have heast :
      (stateGrid (quarterEast east) (quarterSouth south)).north =
        (stateGrid (quarterEast east) (quarterNorth north)).south := by
    exact value_between (fun y => stateGrid (quarterEast east) y)
      ShadeState.north ShadeState.south hquarterSouthNorth
      (fun y _ _ => valid.vmatch (quarterEast east) y)
      (fun y hs hn => (valid.rules (quarterEast east) y).vertical_eq (cycle.east_path hs hn))
  have hneWest :
      (stateGrid (quarterEast east) (quarterNorth north)).west = some shade := by
    rw [(valid.rules (quarterEast east) (quarterNorth north)).west_south_corner_eq
      (cycle.northeast_corner).1 (cycle.northeast_corner).2]
    exact heast.symm.trans hseNorth
  have hnorth :
      (stateGrid (quarterWest west) (quarterNorth north)).east =
        (stateGrid (quarterEast east) (quarterNorth north)).west := by
    exact value_between (fun x => stateGrid x (quarterNorth north))
      ShadeState.east ShadeState.west hquarterWestEast
      (fun x _ _ => valid.hmatch x (quarterNorth north))
      (fun x hw he => (valid.rules x (quarterNorth north)).horizontal_eq (cycle.north_path hw he))
  exact {
    southwest := hshade
    southeast := hsouth.symm.trans hshade
    northeast := hneWest
    northwest := hnorth.trans hneWest
  }

/-- Every oriented red board has one uniform light/dark corner shade. -/
theorem CycleOn.exists_cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) :
    ∃ shade, CycleShade stateGrid west east south north shade := by
  have heast : hasEast
      (componentAt grid (quarterWest west) (quarterSouth south))
      (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
    simp [hasEast, (cycle.southwest_corner).1]
  have hpresent := ((valid.rules (quarterWest west) (quarterSouth south)).east_present).trans heast
  rcases hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east with _ | shade
  · simp [hshade] at hpresent
  · exact ⟨shade, CycleOn.cycleShade cycle valid shade hshade⟩

private theorem value_inside {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β) {start finish position : Nat}
    (hstart : start < position) (hfinish : position < finish)
    (hmatch : ∀ x, start ≤ x → x < finish →
      outgoing (state x) = incoming (state (x + 1)))
    (htransmit : ∀ x, start < x → x < finish →
      incoming (state x) = outgoing (state x)) {value : β}
    (hvalue : outgoing (state start) = value) :
    incoming (state position) = value ∧ outgoing (state position) = value := by
  have flow := value_between state outgoing incoming hstart
    (fun x hx hy => hmatch x hx (lt_trans hy hfinish))
    (fun x hx hy => htransmit x hx (lt_trans hy hfinish))
  have hin := flow.symm.trans hvalue
  exact ⟨hin, (htransmit position hstart hfinish).symm.trans hin⟩

/-- The south side of a uniformly shaded cycle carries its corner shade. -/
theorem CycleShade.south_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat} {shade : Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterSouth south)).west = some shade ∧
      (stateGrid qx (quarterSouth south)).east = some shade := by
  exact value_inside (fun x => stateGrid x (quarterSouth south))
    ShadeState.east ShadeState.west hwest heast
    (fun x _ _ => valid.hmatch x (quarterSouth south))
    (fun x hw he => (valid.rules x (quarterSouth south)).horizontal_eq
      (cycle.south_path hw he)) shaded.southwest

/-- The north side of a uniformly shaded cycle carries its corner shade. -/
theorem CycleShade.north_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat} {shade : Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterNorth north)).west = some shade ∧
      (stateGrid qx (quarterNorth north)).east = some shade := by
  exact value_inside (fun x => stateGrid x (quarterNorth north))
    ShadeState.east ShadeState.west hwest heast
    (fun x _ _ => valid.hmatch x (quarterNorth north))
    (fun x hw he => (valid.rules x (quarterNorth north)).horizontal_eq
      (cycle.north_path hw he)) shaded.northwest

/-- The west side of a uniformly shaded cycle carries its corner shade. -/
theorem CycleShade.west_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat} {shade : Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterWest west) qy).south = some shade ∧
      (stateGrid (quarterWest west) qy).north = some shade := by
  apply value_inside (fun y => stateGrid (quarterWest west) y)
    ShadeState.north ShadeState.south hsouth hnorth
    (fun y _ _ => valid.vmatch (quarterWest west) y)
    (fun y hs hn => (valid.rules (quarterWest west) y).vertical_eq
      (cycle.west_path hs hn))
  exact ((valid.rules (quarterWest west) (quarterSouth south)).east_north_corner_eq
    (cycle.southwest_corner).1 (cycle.southwest_corner).2).symm.trans shaded.southwest

/-- The east side of a uniformly shaded cycle carries its corner shade. -/
theorem CycleShade.east_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → ShadeState}
    {west east south north : Nat} {shade : Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterEast east) qy).south = some shade ∧
      (stateGrid (quarterEast east) qy).north = some shade := by
  apply value_inside (fun y => stateGrid (quarterEast east) y)
    ShadeState.north ShadeState.south hsouth hnorth
    (fun y _ _ => valid.vmatch (quarterEast east) y)
    (fun y hs hn => (valid.rules (quarterEast east) y).vertical_eq
      (cycle.east_path hs hn))
  exact ((valid.rules (quarterEast east) (quarterSouth south)).west_north_corner_eq
    (cycle.southeast_corner).1 (cycle.southeast_corner).2).symm.trans shaded.southeast

/-- Shade at the indicated edge port. -/
@[expose] def value (stateGrid : Nat → Nat → ShadeState) (port : Port) :
    Option Shade :=
  match port.side with
  | .west => (stateGrid port.x port.y).west
  | .east => (stateGrid port.x port.y).east
  | .south => (stateGrid port.x port.y).south
  | .north => (stateGrid port.x port.y).north

/-- A locally allowed shade state has exactly the red-graph incidence at each port. -/
theorem value_isSome_eq_portPresent_of_allowed
    {grid : Nat → Nat → Index} {shadeGrid : Nat → Nat → ShadeState}
    (port : Port)
    (allowed : locallyAllowed
      ⟨grid (port.x / 2) (port.y / 2), quadrantAt port.x port.y⟩
      (shadeGrid port.x port.y) = true) :
    (value shadeGrid port).isSome = portPresent grid port := by
  rcases port with ⟨x, y, side⟩
  have rules := allowedFor_iff.mp allowed
  cases side
  · exact rules.west_present
  · exact rules.east_present
  · exact rules.south_present
  · exact rules.north_present

/-- Allowed shade states have exactly the red-graph incidence. -/
theorem value_isSome_eq_portPresent
    {grid : Nat → Nat → Index} {shadeGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid grid shadeGrid) (port : Port) :
    (value shadeGrid port).isSome = portPresent grid port :=
  value_isSome_eq_portPresent_of_allowed port (valid.allowed port.x port.y)

/-- Even parity means equal shades; odd parity means opposite present shades. -/
@[expose] def Related (parity : Bool) (first second : Option Shade) : Prop :=
  match parity with
  | false => first = second
  | true => ∃ shade, first = some shade ∧ second = some shade.opposite

/-- Equality or opposition of present shades is symmetric. -/
theorem Related.symm {parity : Bool} {first second : Option Shade}
    (relation : Related parity first second) : Related parity second first := by
  cases parity
  · exact Eq.symm relation
  · rcases relation with ⟨shade, rfl, rfl⟩
    exact ⟨shade.opposite, rfl, by simp⟩

/-- Shade relations compose by taking the exclusive-or of their parities. -/
theorem Related.trans {first second third : Option Shade}
    {firstParity secondParity : Bool}
    (firstRelation : Related firstParity first second)
    (secondRelation : Related secondParity second third) :
    Related (Bool.xor firstParity secondParity) first third := by
  cases firstParity <;> cases secondParity
  · exact Eq.trans firstRelation secondRelation
  · subst second
    exact secondRelation
  · subst second
    exact firstRelation
  · rcases firstRelation with ⟨firstShade, rfl, rfl⟩
    rcases secondRelation with ⟨secondShade, heq, hthird⟩
    simp only [Option.some.injEq] at heq
    subst secondShade
    simpa [Related] using Eq.symm hthird

private theorem related_true_of_ne_of_present
    {first second : Option Shade}
    (hfirst : first.isSome = true) (hsecond : second.isSome = true)
    (hne : first ≠ second) : Related true first second := by
  rcases first with _ | first
  · simp at hfirst
  rcases second with _ | second
  · simp at hsecond
  refine ⟨first, rfl, congrArg some ?_⟩
  exact Shade.eq_opposite_of_ne (by
    intro heq
    apply hne
    exact congrArg some heq)

private theorem Link.sound_on {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState} {region : Nat → Nat → Prop}
    (allowed : ∀ x y, region x y → locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true)
    (hmatch : ∀ x y, region x y → region (x + 1) y →
      (stateGrid x y).east = (stateGrid (x + 1) y).west)
    (vmatch : ∀ x y, region x y → region x (y + 1) →
      (stateGrid x y).north = (stateGrid x (y + 1)).south)
    {first second : Port} {parity : Bool} (link : Link indexGrid first second parity) :
    region first.x first.y → region second.x second.y →
      Related parity (value stateGrid first) (value stateGrid second) := by
  induction link with
  | horizontalMatch x y => exact hmatch x y
  | verticalMatch x y => exact vmatch x y
  | horizontal x y hpath =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).horizontal_eq hpath
  | vertical x y hpath =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).vertical_eq hpath
  | westNorth x y hwest hnorth =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).west_north_corner_eq hwest hnorth
  | westSouth x y hwest hsouth =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).west_south_corner_eq hwest hsouth
  | eastNorth x y heast hnorth =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).east_north_corner_eq heast hnorth
  | eastSouth x y heast hsouth =>
      exact fun h _ => (allowedFor_iff.mp (allowed x y h)).east_south_corner_eq heast hsouth
  | crossing x y hhorizontal hvertical =>
      intro h _
      have rules : Allowed (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) :=
        allowedFor_iff.mp (allowed x y h)
      apply related_true_of_ne_of_present
      · exact rules.west_present.trans (by
          simp only [hasWest, hhorizontal, Bool.true_or])
      · exact rules.south_present.trans (by
          simp only [hasSouth, hvertical, Bool.true_or])
      · exact rules.crossing_opposite hhorizontal hvertical
  | symm link ih => exact fun hfirst hsecond => Related.symm (ih hsecond hfirst)

/-- Each graph link enforces the corresponding shade parity in a valid grid. -/
theorem Link.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (link : Link indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) :=
  link.sound_on (region := fun _ _ => True)
    (fun x y _ => valid.allowed x y)
    (fun x y _ _ => valid.hmatch x y) (fun x y _ _ => valid.vmatch x y) trivial trivial

/-- A parity-consistent assignment to all red-graph ports.  Incidence is part
of the data because match links exist independently of whether the shared
edge carries a red wire. -/
structure ValidPortLabeling (indexGrid : Nat → Nat → Index) where
  /-- Optional shade at each quarter-edge port. -/
  label : Port → Option Shade
  /-- Labels are present exactly on the geometrically prescribed red edges. -/
  present : ∀ port, (label port).isSome = portPresent indexGrid port
  /-- Every local connection respects its crossing parity. -/
  related : ∀ {first second parity}, Link indexGrid first second parity →
    Related parity (label first) (label second)

namespace ValidPortLabeling

/-- Regroup four labeled ports into the corresponding quarter shade state. -/
@[expose] def stateGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
    Nat → Nat → ShadeState := fun x y =>
  { west := labeling.label ⟨x, y, .west⟩
    east := labeling.label ⟨x, y, .east⟩
    south := labeling.label ⟨x, y, .south⟩
    north := labeling.label ⟨x, y, .north⟩ }

private theorem ne_of_related_true
    {first second : Option Shade}
    (related : Related true first second) : first ≠ second := by
  rcases related with ⟨shade, rfl, rfl⟩
  intro equal
  simp only [Option.some.injEq] at equal
  cases shade <;> contradiction

/-- Port incidence and parity-link consistency are exactly the local shade
tile and edge-matching rules. -/
theorem validShadeGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
    ValidShadeGrid indexGrid labeling.stateGrid := by
  constructor
  · intro x y
    simp only [locallyAllowed]
    apply allowedFor_iff.mpr
    constructor
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .west⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .east⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .south⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .north⟩
    · intro hpath
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .east⟩
      exact labeling.related (Link.horizontal x y hpath)
    · intro hpath
      change labeling.label ⟨x, y, .south⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.vertical x y hpath)
    · intro heast hsouth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.eastSouth x y heast hsouth)
    · intro heast hnorth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.eastNorth x y heast hnorth)
    · intro hwest hsouth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.westSouth x y hwest hsouth)
    · intro hwest hnorth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.westNorth x y hwest hnorth)
    · intro hhorizontal hvertical
      change labeling.label ⟨x, y, .west⟩ ≠
        labeling.label ⟨x, y, .south⟩
      exact ne_of_related_true
        (labeling.related (Link.crossing x y hhorizontal hvertical))
  · intro x y
    change labeling.label ⟨x, y, .east⟩ =
      labeling.label ⟨x + 1, y, .west⟩
    exact labeling.related (Link.horizontalMatch x y)
  · intro x y
    change labeling.label ⟨x, y, .north⟩ =
      labeling.label ⟨x, y + 1, .south⟩
    exact labeling.related (Link.verticalMatch x y)

end ValidPortLabeling

/-- The parity of a red-graph path determines the relation between its endpoint shades. -/
theorem Path.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (path : Path indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port => rfl
  | ofLink link => exact link.sound valid
  | trans firstPath secondPath firstIH secondIH =>
      exact Related.trans firstIH secondIH

/-- A bounded red-wire path relates its endpoint shades using only local validity and
matching within the bounding rectangle. -/
theorem BoundedPath.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → ShadeState} {width height : Nat}
    (allowed : ∀ x y, x < width → y < height → locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true)
    (hmatch : ∀ x y, x + 1 < width → y < height →
      (stateGrid x y).east = (stateGrid (x + 1) y).west)
    (vmatch : ∀ x y, x < width → y + 1 < height →
      (stateGrid x y).north = (stateGrid x (y + 1)).south)
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port bounds => rfl
  | ofLink link first second =>
      exact link.sound_on (region := fun x y => x < width ∧ y < height)
        (fun x y h => allowed x y h.1 h.2)
        (fun x y _ h => hmatch x y h.1 h.2)
        (fun x y _ h => vmatch x y h.1 h.2) first second
  | trans firstPath secondPath firstIH secondIH => exact Related.trans firstIH secondIH

@[expose] public section
/-- Which side of a vertical red border is the board interior. -/
inductive HorizontalDirection where
  | west
  | east
deriving DecidableEq
end

@[expose] public section
/-- Which side of a horizontal red border is the board interior. -/
inductive VerticalDirection where
  | south
  | north
deriving DecidableEq
end

/-- Vertical red boundary through a quarter, if any. -/
@[expose] def verticalInterior? (component : Thick) (quadrant : Quadrant) :
    Option HorizontalDirection :=
  match component, quadrant with
  | .a, .southeast | .b, .northeast => some .east
  | .c, .northwest | .d, .southwest => some .west
  | component, quadrant =>
      if redVerticalAt component quadrant.xBit then
        if quadrant.xBit then some .east else some .west
      else none

/-- Horizontal red boundary through a quarter, if any. -/
@[expose] def horizontalInterior? (component : Thick) (quadrant : Quadrant) :
    Option VerticalDirection :=
  match component, quadrant with
  | .a, .southeast | .d, .southwest => some .south
  | .b, .northeast | .c, .northwest => some .north
  | component, quadrant =>
      if redHorizontalAt component quadrant.yBit then
        if quadrant.yBit then some .north else some .south
      else none

/-- Shade of the vertical red path through a quarter, if present. -/
@[expose] def verticalShade? (state : ShadeState) : Option Shade :=
  match state.south with
  | some shade => some shade
  | none => state.north

/-- Shade of the horizontal red path through a quarter, if present. -/
@[expose] def horizontalShade? (state : ShadeState) : Option Shade :=
  match state.west with
  | some shade => some shade
  | none => state.east

/-- Selected vertical-border rule with the component made explicit. -/
@[expose] def selectedVerticalFor (component : Thick) (quadrant : Quadrant)
    (state : ShadeState) : Option HorizontalDirection :=
  if verticalShade? state = some .light then
    verticalInterior? component quadrant
  else none

/-- Selected horizontal-border rule with the component made explicit. -/
@[expose] def selectedHorizontalFor (component : Thick) (quadrant : Quadrant)
    (state : ShadeState) : Option VerticalDirection :=
  if horizontalShade? state = some .light then
    horizontalInterior? component quadrant
  else none

/-- Pull the four shades of a coarse quarter from its refined boundary ports. -/
def coarsen (fine : Nat → Nat → ShadeState) (x y : Nat) : ShadeState :=
  { west := value fine (refinedPort ⟨x, y, .west⟩)
    east := value fine (refinedPort ⟨x, y, .east⟩)
    south := value fine (refinedPort ⟨x, y, .south⟩)
    north := value fine (refinedPort ⟨x, y, .north⟩) }

/-- A coarsened port reads its corresponding refined port. -/
@[simp] theorem value_coarsen (fine : Nat → Nat → ShadeState) (port : Port) :
    value (coarsen fine) port = value fine (refinedPort port) := by
  cases port with
  | mk x y side => cases side <;> rfl

/-- Coarsening a valid twice-substituted assignment preserves all shade rules and matches. -/
theorem ValidShadeGrid.coarsen {grid : Nat → Nat → Index} {fine : Nat → Nat → ShadeState}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine) :
    ValidShadeGrid grid (coarsen fine) := by
  let labeling : ValidPortLabeling grid :=
    { label := fun port => value fine (refinedPort port)
      present := fun port =>
        (value_isSome_eq_portPresent hfine _).trans (refinedPort_present grid port)
      related := fun link => (Link.refine link).sound hfine }
  exact labeling.validShadeGrid

private theorem coarse_value {grid : Nat → Nat → Index}
    {fine : Nat → Nat → ShadeState}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine)
    (port : Port) (live : portPresent grid port = true)
    {shade : Shade} (start : value fine (sparsePort port) = some shade) :
    value (coarsen fine) port = some shade := by
  have relation : value fine (sparsePort port) = value fine (refinedPort port) :=
    (livePortPath grid port live).sound hfine
  rw [value_coarsen]
  exact relation.symm.trans start

/-- A uniformly shaded refined cycle induces the same shade on its coarse ancestor. -/
theorem CycleShade.coarsen {grid : Nat → Nat → Index} {fine : Nat → Nat → ShadeState}
    {west east south north : Nat} {shade : Shade}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine)
    (cycle : CycleOn grid west east south north)
    (shaded : CycleShade fine (4 * west) (4 * east) (4 * south) (4 * north) shade) :
    CycleShade (coarsen fine) west east south north shade := by
  have apply_port := coarse_value hfine
  constructor
  · apply apply_port ⟨quarterWest west, quarterSouth south, .east⟩
    · have corner := cycle.southwest_corner
      simp [portPresent, hasEast, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterWest, quarterSouth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.southwest
  · apply apply_port ⟨quarterEast east, quarterSouth south, .west⟩
    · have corner := cycle.southeast_corner
      simp [portPresent, hasWest, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterEast, quarterSouth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.southeast
  · apply apply_port ⟨quarterEast east, quarterNorth north, .west⟩
    · have corner := cycle.northeast_corner
      simp [portPresent, hasWest, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterEast, quarterNorth,
        ← Nat.mul_assoc] using shaded.northeast
  · apply apply_port ⟨quarterWest west, quarterNorth north, .east⟩
    · have corner := cycle.northwest_corner
      simp [portPresent, hasEast, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterWest, quarterNorth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.northwest

end Cslib.WangTile.Robinson
