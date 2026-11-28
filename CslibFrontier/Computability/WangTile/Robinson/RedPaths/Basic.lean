/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles
import Mathlib.Tactic.FinCases

/-!
# Quarter ports and oriented red paths

The corrected Robinson tiles have four quarter sites. Red wires occupy specific lanes and
corners; walks through their ports record the parity of horizontal-to-vertical crossings.
A bounded walk keeps every intermediate port inside its stated rectangle.

## Main definitions

* `QuarterIndex`: a tile index and its named quadrant.
* `CycleOn`: rectangular cycles with their exact inward-facing red lanes.
* `Path`, `BoundedPath`: parity-labelled red walks.

## Main results

* `subdivideTileAt_horizontal_iff`, `subdivideTileAt_vertical_iff`: exact quarter matching.
* `CycleOn.refine`: substitution preserves oriented cycles and doubles them.
* `fixed_cycle`: every twice-substituted tile contains an oriented cycle.

## References

The red-wire construction is after [JeandelVanier2020], §§3.2–3.3, Figures 16–18
(manuscript pp. 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, modules `Closed104.TileSubdivision`, `QuarterGeometry`,
`Quarters`, `RedCycleExpansion`, `RedCycleScaling`, `RedBoards`,
`OrientedRedCycles`, `RedShadeGraph` and `RedShadeGraphBoundedPath`.
The port and crossing parity semantics are unchanged; wire incidence is independent of shades.
Internal seam colours use this library's `WangTile` code, in top/bottom/left/right order,
an injective recolouring of the source's north/south/east/west code.
-/

public section
namespace Cslib.WangTile.Robinson

-- Expose the generated equality helpers so finite certificates reduce through ordinary imports.
@[expose] public section
/-- The four quadrants of a subdivided Wang tile. -/
inductive Quadrant where
  | southwest
  | southeast
  | northwest
  | northeast
deriving DecidableEq
end

namespace Quadrant

/-- Horizontal coordinate of a quadrant: `false` for west, `true` for east. -/
@[expose] def xBit : Quadrant → Bool
  | southwest => false
  | southeast => true
  | northwest => false
  | northeast => true

/-- Vertical coordinate of a quadrant: `false` for south, `true` for north. -/
@[expose] def yBit : Quadrant → Bool
  | southwest => false
  | southeast => false
  | northwest => true
  | northeast => true

/-- The quadrant with the specified horizontal and vertical bits. -/
@[expose] def ofBits : Bool × Bool → Quadrant
  | (false, false) => southwest
  | (true, false) => southeast
  | (false, true) => northwest
  | (true, true) => northeast

/-- All four quarter positions, in southwest/southeast/northwest/northeast order. -/
@[expose] def all : List Quadrant :=
  [southwest, southeast, northwest, northeast]

/-- Every quadrant occurs in the enumeration. -/
theorem mem_all (q : Quadrant) : q ∈ all := by
  cases q <;> decide

instance : Fintype Quadrant := Fintype.ofList all mem_all

end Quadrant

/-- Horizontal macro-edge colors are split by west/east half. -/
@[expose] def horizontalEdgeColor (x : Bool) (color : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (Encodable.encode x) color)

/-- Vertical macro-edge colors are split by south/north half. -/
@[expose] def verticalEdgeColor (y : Bool) (color : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (Encodable.encode y) color)

/-- Internal vertical seam color between west and east quadrants. -/
@[expose] def internalVerticalColor (t : WangTile) (y : Bool) : Nat :=
  Nat.pair 2 (Nat.pair (Encodable.encode y) (Encodable.encode t))

/-- Internal horizontal seam color between south and north quadrants. -/
@[expose] def internalHorizontalColor (t : WangTile) (x : Bool) : Nat :=
  Nat.pair 3 (Nat.pair (Encodable.encode x) (Encodable.encode t))

/-- The quadrant tile of `t` in the 2x2 subdivision. -/
@[expose] def subdivideTileAt (t : WangTile) : Quadrant → WangTile
  | .southwest =>
      { top := internalHorizontalColor t false
        bottom := horizontalEdgeColor false t.bottom
        right := internalVerticalColor t false
        left := verticalEdgeColor false t.left }
  | .southeast =>
      { top := internalHorizontalColor t true
        bottom := horizontalEdgeColor true t.bottom
        right := verticalEdgeColor false t.right
        left := internalVerticalColor t false }
  | .northwest =>
      { top := horizontalEdgeColor false t.top
        bottom := internalHorizontalColor t false
        right := internalVerticalColor t true
        left := verticalEdgeColor true t.left }
  | .northeast =>
      { top := horizontalEdgeColor true t.top
        bottom := internalHorizontalColor t true
        right := verticalEdgeColor true t.right
        left := internalVerticalColor t true }

/-- Matching quarter edges identify internal parents or matching external macro-edges. -/
theorem subdivideTileAt_horizontal_iff (left right : WangTile) (q r : Quadrant) :
    (subdivideTileAt left q).right = (subdivideTileAt right r).left ↔
      match q, r with
      | .southwest, .southeast | .northwest, .northeast => left = right
      | .southeast, .southwest | .northeast, .northwest => left.right = right.left
      | _, _ => False := by
  cases q <;> cases r <;>
    simp [subdivideTileAt, verticalEdgeColor, internalVerticalColor,
      Nat.pair_eq_pair]

/-- The vertical counterpart of quarter-edge matching. -/
theorem subdivideTileAt_vertical_iff (lower upper : WangTile) (q r : Quadrant) :
    (subdivideTileAt lower q).top = (subdivideTileAt upper r).bottom ↔
      match q, r with
      | .southwest, .northwest | .southeast, .northeast => lower = upper
      | .northwest, .southwest | .northeast, .southeast => lower.top = upper.bottom
      | _, _ => False := by
  cases q <;> cases r <;>
    simp [subdivideTileAt, horizontalEdgeColor, internalHorizontalColor,
      Nat.pair_eq_pair]

@[expose] public section
/-- A quarter of one indexed tile of the corrected Robinson alphabet. -/
structure QuarterIndex where
  /-- The parent tile. -/
  index : Index
  /-- The quarter occupied in that parent. -/
  quadrant : Quadrant
  deriving DecidableEq
end

/-- The ordinary Wang tile encoding a quarter and its internal seams. -/
@[expose] def quarterTile (site : QuarterIndex) : WangTile :=
  subdivideTileAt (tile (components site.index)) site.quadrant

@[expose] public section
/-- The four red lane atoms: east vertical, north horizontal, west vertical, south horizontal. -/
inductive ThickLine where
  | r0 | r1 | r2 | r3
  deriving DecidableEq
end

/-- Membership of a red lane in a thick component; green lanes are omitted. -/
@[expose] def containsLine (component : Thick) (line : ThickLine) : Bool :=
  match line with
  | .r0 => (component matches .e | .h | .j | .t)
  | .r1 => (component matches .e | .f | .k | .s)
  | .r2 => (component matches .f | .g | .l | .r)
  | .r3 => (component matches .g | .h | .i | .q)

/-- Red vertical path in the west (`false`) or east (`true`) half of a tile. -/
@[expose] def redVerticalAt (component : Thick) (east : Bool) : Bool :=
  if east then containsLine component .r0 else containsLine component .r2

/-- Red horizontal path in the south (`false`) or north (`true`) half of a tile. -/
@[expose] def redHorizontalAt (component : Thick) (north : Bool) : Bool :=
  if north then containsLine component .r1 else containsLine component .r3

/-- Red corner path entering the west edge of this quarter. -/
@[expose] def cornerWest (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.c, .northwest) | (.d, .southwest)

/-- Red corner path entering the east edge of this quarter. -/
@[expose] def cornerEast (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.a, .southeast) | (.b, .northeast)

/-- Red corner path entering the south edge of this quarter. -/
@[expose] def cornerSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.a, .southeast) | (.d, .southwest)

/-- Red corner path entering the north edge of this quarter. -/
@[expose] def cornerNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.b, .northeast) | (.c, .northwest)

/-- A horizontal red wire crosses this quarter. -/
@[expose] def hasHorizontal (component : Thick) (quadrant : Quadrant) : Bool :=
  redHorizontalAt component quadrant.yBit

/-- A vertical red wire crosses this quarter. -/
@[expose] def hasVertical (component : Thick) (quadrant : Quadrant) : Bool :=
  redVerticalAt component quadrant.xBit

/-- A red wire meets the west edge of this quarter. -/
@[expose] def hasWest (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerWest component quadrant

/-- A red wire meets the east edge of this quarter. -/
@[expose] def hasEast (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerEast component quadrant

/-- A red wire meets the south edge of this quarter. -/
@[expose] def hasSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerSouth component quadrant

/-- A red wire meets the north edge of this quarter. -/
@[expose] def hasNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerNorth component quadrant

/-- The quarter selected by the parity of its coordinates. -/
@[expose] def quadrantAt (x y : Nat) : Quadrant :=
  Quadrant.ofBits (x % 2 == 1, y % 2 == 1)

/-- The horizontal bit of a quarter is the parity of its horizontal coordinate. -/
@[simp] theorem quadrantAt_xBit (x y : Nat) :
    (quadrantAt x y).xBit = (x % 2 == 1) := by
  unfold quadrantAt
  cases x % 2 == 1 <;> cases y % 2 == 1 <;> rfl

/-- The vertical bit of a quarter is the parity of its vertical coordinate. -/
@[simp] theorem quadrantAt_yBit (x y : Nat) :
    (quadrantAt x y).yBit = (y % 2 == 1) := by
  unfold quadrantAt
  cases x % 2 == 1 <;> cases y % 2 == 1 <;> rfl

/-- Thick component at quarter coordinates, grouped by pairs in each direction. -/
@[expose] def componentAt (grid : Nat → Nat → Index) (x y : Nat) : Thick :=
  (components (grid (x / 2) (y / 2))).thick

/-- Thick component of an indexed tile. -/
abbrev indexThick (index : Index) : Thick := (components index).thick

/-- The southwest child preserves the complete old thick component. -/
theorem childBlock_thick_southwest (parent : Index) :
    indexThick (childBlock parent 0 0) = indexThick parent := by
  fin_cases parent <;> rfl

@[simp] private theorem refineIndexGrid_even_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y) = childBlock (grid x y) 0 0 := by
  simpa using refineIndexGrid_child grid x y 0 0

@[simp] private theorem refineIndexGrid_odd_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x + 1) (2 * y) = childBlock (grid x y) 1 0 := by
  simpa using refineIndexGrid_child grid x y 1 0

@[simp] private theorem refineIndexGrid_even_odd (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y + 1) = childBlock (grid x y) 0 1 := by
  simpa using refineIndexGrid_child grid x y 0 1

/-- A rectangular red cycle with the four inward-facing lane orientations. -/
structure CycleOn (grid : Nat → Nat → Index) (west east south north : Nat) : Prop where
  /-- Positive horizontal extent. -/
  west_lt_east : west < east
  /-- Positive vertical extent. -/
  south_lt_north : south < north
  /-- Southwest inward corner. -/
  southwest : indexThick (grid west south) = .b
  /-- Southeast inward corner. -/
  southeast : indexThick (grid east south) = .c
  /-- Northwest inward corner. -/
  northwest : indexThick (grid west north) = .a
  /-- Northeast inward corner. -/
  northeast : indexThick (grid east north) = .d
  /-- North-facing horizontal lane on the south side. -/
  southLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x south)) .r1 = true
  /-- South-facing horizontal lane on the north side. -/
  northLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x north)) .r3 = true
  /-- East-facing vertical lane on the west side. -/
  westLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid west y)) .r0 = true
  /-- West-facing vertical lane on the east side. -/
  eastLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid east y)) .r2 = true

/-- The parity split used by both horizontal and vertical lane refinement. -/
private theorem refinedLane {coarse fine : Nat → Index} {lower upper : Nat}
    (property : Index → Prop) (oddChild : Index → Index)
    (even : ∀ x, fine (2 * x) = childBlock (coarse x) 0 0)
    (odd : ∀ x, fine (2 * x + 1) = oddChild (coarse x))
    (parent : ∀ x, lower < x → x < upper → property (coarse x))
    (children : ∀ p, property p → property (childBlock p 0 0) ∧ property (oddChild p))
    (boundary : property (oddChild (coarse lower))) :
    ∀ x, 2 * lower < x → x < 2 * upper → property (fine x) := by
  intro x hl hu
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · exact even k ▸ (children _ (parent k (by omega) (by omega))).1
  · rw [odd]
    exact if h : k = lower then h ▸ boundary else (children _ (parent k (by omega) (by omega))).2

private theorem refinedHorizontalLane {grid : Nat → Nat → Index} {west east row : Nat}
    {line : ThickLine} {corner : Thick}
    (hcert : (∀ p : Index, containsLine (indexThick p) line = true →
        containsLine (indexThick (childBlock p 0 0)) line = true ∧
          containsLine (indexThick (childBlock p 1 0)) line = true) ∧
      ∀ p : Index, indexThick p = corner →
        containsLine (indexThick (childBlock p 1 0)) line = true)
    (parentLane : ∀ x, west < x → x < east → containsLine (indexThick (grid x row)) line = true)
    (hwest : indexThick (grid west row) = corner) :
    ∀ x, 2 * west < x → x < 2 * east →
      containsLine (indexThick (refineIndexGrid grid x (2 * row))) line = true :=
  refinedLane _ _ (fun x => refineIndexGrid_even_even grid x row)
    (fun x => refineIndexGrid_odd_even grid x row) parentLane hcert.1 (hcert.2 _ hwest)

private theorem refinedVerticalLane {grid : Nat → Nat → Index} {south north column : Nat}
    {line : ThickLine} {corner : Thick}
    (hcert : (∀ p : Index, containsLine (indexThick p) line = true →
        containsLine (indexThick (childBlock p 0 0)) line = true ∧
          containsLine (indexThick (childBlock p 0 1)) line = true) ∧
      ∀ p : Index, indexThick p = corner →
        containsLine (indexThick (childBlock p 0 1)) line = true)
    (parentLane : ∀ y, south < y → y < north →
      containsLine (indexThick (grid column y)) line = true)
    (hsouth : indexThick (grid column south) = corner) :
    ∀ y, 2 * south < y → y < 2 * north →
      containsLine (indexThick (refineIndexGrid grid (2 * column) y)) line = true :=
  refinedLane _ _ (fun y => refineIndexGrid_even_even grid column y)
    (fun y => refineIndexGrid_even_odd grid column y) parentLane hcert.1 (hcert.2 _ hsouth)

/-- An oriented red cycle transfers across grids agreeing from the origin through its
northeast corner. -/
theorem CycleOn.congr {g h : ℕ → ℕ → Index} {w e b t : ℕ}
    (c : CycleOn g w e b t) (eq : ∀ x y, x ≤ e → y ≤ t → g x y = h x y) :
    CycleOn h w e b t where
  west_lt_east := c.west_lt_east
  south_lt_north := c.south_lt_north
  southwest := by rw [← eq w b c.west_lt_east.le c.south_lt_north.le]; exact c.southwest
  southeast := by rw [← eq e b le_rfl c.south_lt_north.le]; exact c.southeast
  northwest := by rw [← eq w t c.west_lt_east.le le_rfl]; exact c.northwest
  northeast := by rw [← eq e t le_rfl le_rfl]; exact c.northeast
  southLane x hl hu := by rw [← eq x b hu.le c.south_lt_north.le]; exact c.southLane x hl hu
  northLane x hl hu := by rw [← eq x t hu.le le_rfl]; exact c.northLane x hl hu
  westLane y hl hu := by rw [← eq w y c.west_lt_east.le hu.le]; exact c.westLane y hl hu
  eastLane y hl hu := by rw [← eq e y le_rfl hu.le]; exact c.eastLane y hl hu

/-- Substitution doubles an oriented red cycle and preserves all four lanes. -/
theorem CycleOn.refine {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    CycleOn (refineIndexGrid grid)
      (2 * west) (2 * east) (2 * south) (2 * north) where
  west_lt_east := by have := cycle.west_lt_east; omega
  south_lt_north := by have := cycle.south_lt_north; omega
  southwest := by simpa using (childBlock_thick_southwest (grid west south)).trans cycle.southwest
  southeast := by simpa using (childBlock_thick_southwest (grid east south)).trans cycle.southeast
  northwest := by simpa using (childBlock_thick_southwest (grid west north)).trans cycle.northwest
  northeast := by simpa using (childBlock_thick_southwest (grid east north)).trans cycle.northeast
  southLane := refinedHorizontalLane (by decide +kernel) cycle.southLane cycle.southwest
  northLane := refinedHorizontalLane (by decide +kernel) cycle.northLane cycle.northwest
  westLane := refinedVerticalLane (by decide +kernel) cycle.westLane cycle.southwest
  eastLane := refinedVerticalLane (by decide +kernel) cycle.eastLane cycle.southeast

/-- Every twice-substituted tile contains the same oriented red board. -/
theorem fixed_cycle (parent : Index) :
    CycleOn (iterateRefine 2 (fun _ _ => parent)) 1 3 1 3 := by
  have checked : ∀ p : Index,
      let g := iterateRefine 2 (fun _ _ => p)
      indexThick (g 1 1) = .b ∧ indexThick (g 3 1) = .c ∧
      indexThick (g 1 3) = .a ∧ indexThick (g 3 3) = .d ∧
      containsLine (indexThick (g 2 1)) .r1 = true ∧
      containsLine (indexThick (g 2 3)) .r3 = true ∧
      containsLine (indexThick (g 1 2)) .r0 = true ∧
      containsLine (indexThick (g 3 2)) .r2 = true := by decide
  obtain ⟨sw, se, nw, ne, s, n, w, e⟩ := checked parent
  refine ⟨by decide, by decide, sw, se, nw, ne, ?_, ?_, ?_, ?_⟩
  all_goals
    intro z hz₁ hz₂
    have : z = 2 := by omega
    subst z
    assumption

/-- Every further substitution preserves the board and scales its coordinates by two. -/
theorem CycleOn.iterateRefine {grid : Nat → Nat → Index} {w e s n : Nat}
    (cycle : CycleOn grid w e s n) (level : Nat) :
    CycleOn (Robinson.iterateRefine level grid)
      (2 ^ level * w) (2 ^ level * e) (2 ^ level * s) (2 ^ level * n) := by
  induction level with
  | zero => simpa only [Robinson.iterateRefine, pow_zero, Nat.one_mul] using cycle
  | succ level ih =>
    simpa only [Robinson.iterateRefine, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using ih.refine

@[expose] public section
/-- A quarter-tile edge at an absolute coordinate. -/
inductive Side where
  | west
  | east
  | south
  | north
deriving DecidableEq
end

/-- The four possible port sides form a finite alphabet. -/
instance : Fintype Side :=
  Fintype.ofList [.west, .east, .south, .north] (by intro side; cases side <;> simp)

@[expose] public section
/-- A side of a quarter at a nonnegative coordinate. -/
structure Port where
  /-- Horizontal quarter coordinate. -/
  x : Nat
  /-- Vertical quarter coordinate. -/
  y : Nat
  /-- The edge of the quarter. -/
  side : Side
deriving DecidableEq
end

/-- Whether the unshaded quarter geometry carries a red wire at a port. -/
@[expose] def portPresent (grid : Nat → Nat → Index) (port : Port) : Bool :=
  let component := componentAt grid port.x port.y
  let quadrant := quadrantAt port.x port.y
  match port.side with
  | .west => hasWest component quadrant
  | .east => hasEast component quadrant
  | .south => hasSouth component quadrant
  | .north => hasNorth component quadrant

/-- One local shade-preserving or shade-reversing connection. -/
inductive Link (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | horizontalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x + 1, y, .west⟩ false
  | verticalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .north⟩ ⟨x, y + 1, .south⟩ false
  | horizontal (x y : Nat)
      (hpath : hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .east⟩ false
  | vertical (x y : Nat)
      (hpath : hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .south⟩ ⟨x, y, .north⟩ false
  | westNorth (x y : Nat)
      (hwest : cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .north⟩ false
  | westSouth (x y : Nat)
      (hwest : cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ false
  | eastNorth (x y : Nat)
      (heast : cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .north⟩ false
  | eastSouth (x y : Nat)
      (heast : cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .south⟩ false
  | crossing (x y : Nat)
      (hhorizontal : hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hvertical : hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ true
  | symm {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Link indexGrid second first parity

/-- A finite red-wire walk, labelled by the parity of its crossings. -/
inductive Path (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | refl (port : Port) : Path indexGrid port port false
  | ofLink {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Path indexGrid first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool} :
      Path indexGrid first second firstParity →
      Path indexGrid second third secondParity →
      Path indexGrid first third (Bool.xor firstParity secondParity)

/-- Reversing a walk preserves its crossing parity. -/
theorem Path.symm {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (path : Path grid first second parity) : Path grid second first parity := by
  induction path with
  | refl port => exact .refl port
  | ofLink link => exact .ofLink (.symm link)
  | trans _ _ ih₁ ih₂ => simpa only [Bool.xor_comm] using Path.trans ih₂ ih₁

/-- A port lies in the quarter rectangle with the specified width and height. -/
@[expose] def PortInBounds (port : Port) (width height : Nat) : Prop :=
  port.x < width ∧ port.y < height

/-- A parity-labelled red walk whose every endpoint stays in a fixed rectangle. -/
inductive BoundedPath (indexGrid : Nat → Nat → Index)
    (width height : Nat) : Port → Port → Bool → Prop where
  | refl (port : Port) (hport : PortInBounds port width height) :
      BoundedPath indexGrid width height port port false
  | ofLink {first second : Port} {parity : Bool}
      (link : Link indexGrid first second parity)
      (hfirst : PortInBounds first width height)
      (hsecond : PortInBounds second width height) :
      BoundedPath indexGrid width height first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool}
      (firstPath : BoundedPath indexGrid width height
        first second firstParity)
      (secondPath : BoundedPath indexGrid width height
        second third secondParity) :
      BoundedPath indexGrid width height first third
        (Bool.xor firstParity secondParity)

/-- Forgetting the rectangle bounds gives an ordinary red walk. -/
theorem BoundedPath.path
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Path indexGrid first second parity := by
  induction path with
  | refl port => exact .refl port
  | ofLink link => exact .ofLink link
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The first endpoint of a bounded red walk lies in its bounding rectangle. -/
theorem BoundedPath.first_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds first width height := by
  induction path <;> assumption

end Cslib.WangTile.Robinson
