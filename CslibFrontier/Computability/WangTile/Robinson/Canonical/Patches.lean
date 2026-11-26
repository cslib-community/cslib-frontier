/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Canonical.Certificates
import CslibFrontier.Computability.WangTile.Compactness

/-!
# Canonical decorated Robinson patches

The selected closed substitution produces matching corrected tiles and shade blocks.
Nearest selected borders determine obstruction signals along each row and column.
Pairing these three layers gives finite scaffold patches of unbounded size.

## Main definitions

* `canonicalPatch`: the decorated square of side `2 * 4^level` below a selected root.

## Main results

* `scaffold_tilesPlane`: the concrete decorated scaffold tiles the plane.

## References

Restructured from [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`: its `ShadedSubstitutionSupertiles`, `ShadedSignalRectangle` and
`ShadedSubstitutionPlane` modules in the corrected Robinson development.
-/

public section

namespace Cslib.WangTile.Robinson.Canonical

/-- The finite local shade rules needed when decorating a bounded square. -/
structure ShadeValidOn (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → ShadeState) (width height : ℕ) : Prop where
  /-- Every quarter in the rectangle satisfies the local shade rule. -/
  allowed : ∀ x y, x < width → y < height →
    locallyAllowed ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩
      (shadeGrid x y) = true
  /-- Adjacent horizontal quarters inside the rectangle carry matching shades. -/
  hmatch : ∀ x y, x + 1 < width → y < height →
    (shadeGrid x y).east = (shadeGrid (x + 1) y).west
  /-- Adjacent vertical quarters inside the rectangle carry matching shades. -/
  vmatch : ∀ x y, x < width → y + 1 < height →
    (shadeGrid x y).north = (shadeGrid x (y + 1)).south

/-- Position in a `4 x 4` child block, encoded in south-to-north row order. -/
@[expose] def childPosition (x y : Nat) : Fin 16 :=
  blockPosition ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩

/-- Simultaneously replace every node in a grid by its certified child block. -/
private def refineNodeGrid (grid : Nat → Nat → Node) : Nat → Nat → Node :=
  fun x y => (grid (x / 4) (y / 4)).child (childPosition x y)

/-- Tile-and-shade compatibility inside a bounded node rectangle. -/
private structure CompatibleOn (grid : Nat → Nat → Node) (width height : Nat) : Prop where
  hmatch : ∀ x y, x + 1 < width → y < height →
    HCompatible (grid x y) (grid (x + 1) y)
  vmatch : ∀ x y, x < width → y + 1 < height →
    VCompatible (grid x y) (grid x (y + 1))

private theorem CompatibleOn.refine {grid : Nat → Nat → Node} {width height : Nat}
    (compatible : CompatibleOn grid width height) :
    CompatibleOn (refineNodeGrid grid) (4 * width) (4 * height) := by
  constructor
  · intro x y hx hy
    by_cases hboundary : x % 4 = 3
    · simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        show (x + 1) / 4 = x / 4 + 1 by omega, show (x + 1) % 4 = 0 by omega] using
        children_hCompatible_boundary (compatible.hmatch (x / 4) (y / 4) (by omega) (by omega))
          ⟨y % 4, by omega⟩
    · simpa [refineNodeGrid, childPosition, blockPosition, show (x + 1) / 4 = x / 4 by omega,
        show (x + 1) % 4 = x % 4 + 1 by omega] using
        children_hCompatible_within (grid (x / 4) (y / 4)) ⟨x % 4, by omega⟩ ⟨y % 4, by omega⟩
  · intro x y hx hy
    by_cases hboundary : y % 4 = 3
    · simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        show (y + 1) / 4 = y / 4 + 1 by omega, show (y + 1) % 4 = 0 by omega] using
        children_vCompatible_boundary (compatible.vmatch (x / 4) (y / 4) (by omega) (by omega))
          ⟨x % 4, by omega⟩
    · simpa [refineNodeGrid, childPosition, blockPosition, show (y + 1) / 4 = y / 4 by omega,
        show (y + 1) % 4 = y % 4 + 1 by omega] using
        children_vCompatible_within (grid (x / 4) (y / 4)) ⟨x % 4, by omega⟩ ⟨y % 4, by omega⟩

/-- The decorated supertile obtained by repeatedly substituting the selected 4×4 children. -/
@[expose] def supertileNodeGrid : ℕ → Node → ℕ → ℕ → Node
  | 0, root, _, _ => root
  | level + 1, root, x, y =>
      (supertileNodeGrid level root (x / 4) (y / 4)).child (childPosition x y)

/-- Underlying corrected tile at a coordinate in the decorated supertile. -/
@[expose] def supertileIndexGrid (level : Nat) (root : Node) : Nat → Nat → Index :=
  fun x y => (supertileNodeGrid level root x y).parent

/-- Flatten each corrected-tile shade block into its four quarter states. -/
@[expose] def supertileShadeGrid (level : Nat) (root : Node) :
    Nat → Nat → ShadeState := fun x y =>
  ((supertileNodeGrid level root (x / 2) (y / 2)).block).at (x % 2) (y % 2)

/-- The canonical index grid is the two-substitutions-per-level refinement of its root. -/
theorem supertileIndexGrid_eq_iterateRefine (level : ℕ) (root : Node) :
    supertileIndexGrid level root = iterateRefine (2 * level) (coarseGrid root.parent) := by
  funext x y
  induction level generalizing x y with
  | zero => rfl
  | succ level ih =>
      have hxy : (childPosition x y).val % 4 = x % 4 ∧ (childPosition x y).val / 4 = y % 4 := by
        simp only [childPosition, blockPosition]; omega
      rw [Nat.mul_succ, Nat.add_comm _ 2, ← iterateRefine_add, iterateRefine_two_local]
      change ((supertileNodeGrid level root (x / 4) (y / 4)).child
        (childPosition x y)).parent = _
      rw [Node.child_parent, hxy.1, hxy.2]
      exact congrArg (fun parent => fineGrid parent (x % 4) (y % 4)) (ih (x / 4) (y / 4))

/-- Inside the root block, canonical indices agree with any grid with the same root tile. -/
theorem supertileIndexGrid_eq_of_root_eq (level : ℕ) (root : Node) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = root.parent) {x y : ℕ} (hx : x < 4 ^ level)
    (hy : y < 4 ^ level) :
    supertileIndexGrid level root x y = iterateRefine (2 * level) coarse x y := by
  rw [supertileIndexGrid_eq_iterateRefine]
  apply iterateRefine_eq_of_root_eq rootEq.symm
  · rwa [pow_mul]
  · rwa [pow_mul]

/-- A four-by-four tile block in a supertile is the child block of its coarser node. -/
theorem supertileNodeGrid_block (level : ℕ) (root : Node)
    (bx by₀ x y : ℕ) (hx : x < 4) (hy : y < 4) :
    supertileNodeGrid (level + 1) root (4 * bx + x) (4 * by₀ + y) =
      (supertileNodeGrid level root bx by₀).child (childPosition x y) := by
  simp only [supertileNodeGrid, childPosition, Nat.mul_add_div (by decide : 0 < 4),
    Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.add_zero, Nat.mul_add_mod]

/-- The inherited sparse quarters keep the shade of their parent quarters. -/
theorem supertileShadeGrid_sparse (level : ℕ) (root : Node) (x y : ℕ) :
    supertileShadeGrid (level + 1) root (sparseCoordinate x) (sparseCoordinate y) =
      supertileShadeGrid level root x y := by
  have coords (z : ℕ) : sparseCoordinate z / 2 = 4 * (z / 2) ∧
      sparseCoordinate z % 2 = z % 2 := by dsimp only [sparseCoordinate]; omega
  have position : childPosition (4 * (x / 2)) (4 * (y / 2)) = 0 :=
    Fin.ext (by simp [childPosition, blockPosition])
  simp only [supertileShadeGrid, (coords x).1, (coords y).1, (coords x).2, (coords y).2,
    supertileNodeGrid, position, Node.child_zero_block, Nat.mul_div_right _ (by decide : 0 < 4)]

/-- Each eight-by-eight quarter block is the first supertile of its coarser node. -/
theorem supertileShadeGrid_block (level : ℕ) (root : Node)
    (bx by₀ x y : ℕ) (hx : x < 8) (hy : y < 8) :
    supertileShadeGrid (level + 1) root (8 * bx + x) (8 * by₀ + y) =
      supertileShadeGrid 1 (supertileNodeGrid level root bx by₀) x y := by
  dsimp only [supertileShadeGrid]
  rw [show (8 * bx + x) / 2 = 4 * bx + x / 2 by omega,
    show (8 * by₀ + y) / 2 = 4 * by₀ + y / 2 by omega,
    supertileNodeGrid_block level root bx by₀ (x / 2) (y / 2) (by omega) (by omega)]
  dsimp only [supertileNodeGrid]
  congr 1 <;> omega

private theorem supertileNodeGrid_compatible (level : Nat) (root : Node) :
    CompatibleOn (supertileNodeGrid level root) (4 ^ level) (4 ^ level) := by
  induction level with
  | zero => constructor <;> intro _ _ h <;> omega
  | succ level ih =>
      change CompatibleOn (refineNodeGrid (supertileNodeGrid level root))
        (4 ^ (level + 1)) (4 ^ (level + 1))
      simpa only [pow_succ, Nat.mul_comm] using ih.refine

/-- Adjacent entries in two-entry blocks match either inside one block or across its seam. -/
private theorem adjacent_pairs {α : Type*} (rel : α → α → Prop)
    (block : ℕ → ℕ → α) {n x : ℕ}
    (within : ∀ i, i < n → rel (block i 0) (block i 1))
    (between : ∀ i, i + 1 < n → rel (block i 1) (block (i + 1) 0))
    (hx : x + 1 < 2 * n) :
    rel (block (x / 2) (x % 2)) (block ((x + 1) / 2) ((x + 1) % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h, show (x + 1) / 2 = x / 2 by omega, show (x + 1) % 2 = 1 by omega]
    exact within _ (by omega)
  · rw [h, show (x + 1) / 2 = x / 2 + 1 by omega, show (x + 1) % 2 = 0 by omega]
    exact between _ (by omega)

/-- Every canonical supertile obeys the shade rules throughout its finite square. -/
theorem supertile_validShadeRectangle (level : Nat) (root : Node) :
    ShadeValidOn
      (supertileIndexGrid level root) (supertileShadeGrid level root)
      (2 * 4 ^ level) (2 * 4 ^ level) := by
  constructor
  · intro x y hx hy
    simpa [supertileIndexGrid, supertileShadeGrid, quadrantAt, Nat.mod_mod] using
      (supertileNodeGrid level root (x / 2) (y / 2)).block_allowed
        ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩
  · intro x y hx hy
    refine adjacent_pairs (fun a b : ShadeState => a.east = b.west)
      (fun i r => (supertileNodeGrid level root i (y / 2)).block.at r (y % 2))
      (n := 4 ^ level) ?_ ?_ hx
    · intro i _
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        simp [ShadeBlock.at, hy, (supertileNodeGrid level root i (y / 2)).block_internal]
    · intro i hi
      have blockMatch := ((supertileNodeGrid_compatible level root).hmatch
        i (y / 2) hi (by omega)).2
      simp only [ShadeBlock.hMatches, ShadeBlock.at, Bool.and_eq_true, decide_eq_true_eq,
        one_ne_zero, ↓reduceIte] at blockMatch
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [ShadeBlock.at, hy, blockMatch]
  · intro x y hx hy
    refine adjacent_pairs (fun a b : ShadeState => a.north = b.south)
      (fun i r => (supertileNodeGrid level root (x / 2) i).block.at (x % 2) r)
      (n := 4 ^ level) ?_ ?_ hy
    · intro i _
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
        simp [ShadeBlock.at, hx, (supertileNodeGrid level root (x / 2) i).block_internal]
    · intro i hi
      have blockMatch := ((supertileNodeGrid_compatible level root).vmatch
        (x / 2) i (by omega) hi).2
      simp only [ShadeBlock.vMatches, ShadeBlock.at, Bool.and_eq_true, decide_eq_true_eq,
        one_ne_zero, ↓reduceIte] at blockMatch
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> simp [ShadeBlock.at, hx, blockMatch]

/-- Orientation of the last selected border strictly before an edge. -/
@[expose] def previousInterior (interior : ℕ → Option Bool) : ℕ → Option Bool
  | 0 => none
  | position + 1 => (interior position).orElse fun _ => previousInterior interior position

/-- Orientation of the first selected border in a bounded suffix. -/
@[expose] def nextInterior (interior : ℕ → Option Bool) : ℕ → ℕ → Option Bool
  | _, 0 => none
  | position, fuel + 1 => (interior position).orElse fun _ =>
      nextInterior interior (position + 1) fuel

/-- A selected border remains the previous one until another border occurs. -/
theorem previousInterior_eq_of_none_between
    {interior : ℕ → Option Bool} {border position : ℕ} {orientation : Bool}
    (selected : interior border = some orientation)
    (between : ∀ candidate, border < candidate → candidate < position →
      interior candidate = none) (afterBorder : border < position) :
    previousInterior interior position = some orientation := by
  induction position, Nat.succ_le_of_lt afterBorder using Nat.le_induction with
  | base => simp [previousInterior, selected]
  | succ position _ ih =>
      simp [previousInterior, between position (by omega) (by omega),
        ih (fun candidate lower _ => between candidate lower (by omega)) (by omega)]

/-- A bounded suffix has the given first orientation if a border with that orientation occurs
and no opposite border precedes it. -/
theorem nextInterior_eq_of_no_opposite_before
    {interior : ℕ → Option Bool} {position border length : ℕ} {orientation : Bool}
    (selected : interior border = some orientation)
    (noOpposite : ∀ candidate, position ≤ candidate → candidate < border →
      interior candidate ≠ some (!orientation))
    (atMostBorder : position ≤ border) (borderBeforeEnd : border < length) :
    nextInterior interior position (length - position) = some orientation := by
  induction distance : border - position generalizing position with
  | zero =>
      obtain rfl : position = border := by omega
      obtain ⟨fuel, fuelEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt borderBeforeEnd)
      simp [fuelEq, nextInterior, selected]
  | succ distance ih =>
      have fuelEq : length - position = length - (position + 1) + 1 := by omega
      rw [fuelEq]
      cases current : interior position with
      | none =>
          simp only [nextInterior, current, Option.orElse_none]
          apply ih (position := position + 1) <;>
            first | omega | exact fun candidate lower => noOpposite candidate (by omega)
      | some currentOrientation =>
          have := noOpposite position le_rfl (by omega)
          cases orientation <;> cases currentOrientation <;> simp [nextInterior, current] at this ⊢

/-- A successful suffix scan witnesses an actual selected border in the scanned interval. -/
theorem exists_interior_of_nextInterior_eq_some
    {interior : ℕ → Option Bool} {position fuel : ℕ} {orientation : Bool}
    (next : nextInterior interior position fuel = some orientation) :
    ∃ candidate, position ≤ candidate ∧ candidate < position + fuel ∧
      interior candidate = some orientation := by
  induction fuel generalizing position with
  | zero => simp [nextInterior] at next
  | succ fuel ih =>
      cases current : interior position with
      | none =>
          simp only [nextInterior, current, Option.orElse_none] at next
          obtain ⟨candidate, lower, upper, selected⟩ := ih next
          exact ⟨candidate, by omega, by omega, selected⟩
      | some currentOrientation =>
          simp only [nextInterior, current, Option.orElse_some, Option.some.injEq] at next
          exact ⟨position, le_rfl, by omega, next ▸ current⟩

/-- Canonical edge flow determined by the nearest selected borders. The clear case is the
interval before a closing border whose previous border is opening or absent. -/
@[expose] def intervalEdge (interior : ℕ → Option Bool) (length position : ℕ) : SignalFlow :=
  match nextInterior interior position (length - position) with
  | none => .backward
  | some false =>
      if previousInterior interior position = some false then .forward else .none
  | some true =>
      if previousInterior interior position = some true then .backward else .forward

/-- The exact nearest-border condition for a clear edge. -/
theorem intervalEdge_eq_none_iff (interior : ℕ → Option Bool) (length position : ℕ) :
    intervalEdge interior length position = .none ↔
      nextInterior interior position (length - position) = some false ∧
        previousInterior interior position ≠ some false := by
  unfold intervalEdge
  rcases nextInterior interior position (length - position) with _ | _ | _ <;>
    rcases previousInterior interior position with _ | _ | _ <;> simp

/-- Every edge between consecutive opening and closing borders is clear. -/
theorem intervalEdge_eq_none_of_between_borders
    {interior : ℕ → Option Bool} {length opening closing position : ℕ}
    (openingBorder : interior opening = some true)
    (closingBorder : interior closing = some false)
    (noBorder : ∀ candidate, opening < candidate → candidate < closing →
      interior candidate = none)
    (afterOpening : opening < position) (atMostClosing : position ≤ closing)
    (closingBeforeEnd : closing < length) :
    intervalEdge interior length position = .none := by
  refine (intervalEdge_eq_none_iff ..).mpr ⟨nextInterior_eq_of_no_opposite_before closingBorder
    (fun candidate positionLe beforeClosing => by
      simp [noBorder candidate (afterOpening.trans_le positionLe) beforeClosing])
    atMostClosing closingBeforeEnd, ?_⟩
  simp [previousInterior_eq_of_none_between openingBorder
    (fun candidate lower upper => noBorder candidate lower (upper.trans_le atMostClosing))
    afterOpening]

/-- Nearest-border flows satisfy the one-dimensional local obstruction rule. -/
theorem intervalEdge_allowed (interior : ℕ → Option Bool) (length position : ℕ)
    (hposition : position < length) :
    flowAllowed (interior position) (intervalEdge interior length position)
      (intervalEdge interior length (position + 1)) = true := by
  have hlength : length - position = length - (position + 1) + 1 := by omega
  cases hcurrent : interior position with
  | none =>
      simp [flowAllowed, intervalEdge, hcurrent, hlength, previousInterior, nextInterior]
  | some current =>
      cases current <;> rcases hprevious : previousInterior interior position with _ | _ | _ <;>
        rcases hnext : nextInterior interior (position + 1) (length - (position + 1))
          with _ | _ | _ <;>
        simp [flowAllowed, intervalEdge, hcurrent, hprevious, hnext, hlength, previousInterior,
          nextInterior]

/-- A selected border cannot have clear canonical signal edges on both sides. -/
theorem interior_eq_none_of_adjacent_clear
    (interior : ℕ → Option Bool) {length position : ℕ} (hposition : position < length)
    (hleft : intervalEdge interior length position = .none)
    (hright : intervalEdge interior length (position + 1) = .none) :
    interior position = none := by
  have allowed := hleft ▸ hright ▸ intervalEdge_allowed interior length position hposition
  cases hcurrent : interior position with
  | none => rfl
  | some current => cases current <;> simp [flowAllowed, hcurrent] at allowed

/-- Side length in quarter tiles of a decorated supertile. -/
@[expose] def side (level : ℕ) : ℕ := 2 * 4 ^ level

/-- Selected vertical-border orientation along a quarter-tile row. -/
@[expose] def rowInterior (level : ℕ) (root : Node) (x y : ℕ) : Option Bool :=
  (supertileNodeGrid level root (x / 2) (y / 2)).rowInterior (x % 2) (y % 2)

/-- Selected horizontal-border orientation along a quarter-tile column. -/
@[expose] def columnInterior (level : ℕ) (root : Node) (x y : ℕ) : Option Bool :=
  (supertileNodeGrid level root (x / 2) (y / 2)).columnInterior (x % 2) (y % 2)

/-- The three-layer canonical site. Its four signal edges use the nearest selected borders. -/
@[expose] def site (level : ℕ) (root : Node) (x y : ℕ) : ShadedSite where
  quarter := ⟨supertileIndexGrid level root (x / 2) (y / 2), quadrantAt x y⟩
  shade := supertileShadeGrid level root x y
  signal := {
    west := intervalEdge (fun x => rowInterior level root x y) (side level) x
    east := intervalEdge (fun x => rowInterior level root x y) (side level) (x + 1)
    south := intervalEdge (fun y => columnInterior level root x y) (side level) y
    north := intervalEdge (fun y => columnInterior level root x y) (side level) (y + 1) }

private theorem site_allowed (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x < side level) (hy : y < side level) :
    signalsAllowed (site level root x y).quarter (site level root x y).shade
      (site level root x y).signal = true := by
  have hh := intervalEdge_allowed (fun x => rowInterior level root x y) (side level) x hx
  have hv := intervalEdge_allowed (fun y => columnInterior level root x y) (side level) y hy
  simpa [signalsAllowed, SignalState.horizontalAllowed, SignalState.verticalAllowed,
    site, rowInterior, columnInterior, Node.rowInterior, Node.columnInterior,
    supertileIndexGrid, supertileShadeGrid, quadrantAt, Nat.mod_mod] using
    Bool.and_eq_true_iff.mpr ⟨hh, hv⟩

private theorem quarter_hmatch (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x + 1 < side level) (hy : y < side level) :
    (quarterTile (site level root x y).quarter).right =
      (quarterTile (site level root (x + 1) y).quarter).left := by
  let block (i r : ℕ) : QuarterIndex :=
    ⟨(supertileNodeGrid level root i (y / 2)).parent, quadrantAt r y⟩
  have within (i : ℕ) (_ : i < 4 ^ level) :
      (quarterTile (block i 0)).right = (quarterTile (block i 1)).left := by
    rcases Nat.mod_two_eq_zero_or_one y with hybit | hybit <;>
      simp [block, quarterTile, quadrantAt, Quadrant.ofBits,
        subdivideTileAt_horizontal_iff, hybit]
  have between (i : ℕ) (hi : i + 1 < 4 ^ level) :
      (quarterTile (block i 1)).right = (quarterTile (block (i + 1) 0)).left := by
    have matched := ((supertileNodeGrid_compatible level root).hmatch
      i (y / 2) hi (by dsimp only [side] at hy; omega)).1
    rcases Nat.mod_two_eq_zero_or_one y with hybit | hybit <;>
      simpa [block, quarterTile, quadrantAt, Quadrant.ofBits,
        subdivideTileAt_horizontal_iff, hybit] using matched
  simpa only [block, site, supertileIndexGrid, quadrantAt, Nat.mod_mod] using
    adjacent_pairs (fun a b : QuarterIndex => (quarterTile a).right = (quarterTile b).left)
      block within between (x := x) (by dsimp only [side] at hx; exact hx)

private theorem quarter_vmatch (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x < side level) (hy : y + 1 < side level) :
    (quarterTile (site level root x y).quarter).top =
      (quarterTile (site level root x (y + 1)).quarter).bottom := by
  let block (i r : ℕ) : QuarterIndex :=
    ⟨(supertileNodeGrid level root (x / 2) i).parent, quadrantAt x r⟩
  have within (i : ℕ) (_ : i < 4 ^ level) :
      (quarterTile (block i 0)).top = (quarterTile (block i 1)).bottom := by
    rcases Nat.mod_two_eq_zero_or_one x with hxbit | hxbit <;>
      simp [block, quarterTile, quadrantAt, Quadrant.ofBits,
        subdivideTileAt_vertical_iff, hxbit]
  have between (i : ℕ) (hi : i + 1 < 4 ^ level) :
      (quarterTile (block i 1)).top = (quarterTile (block (i + 1) 0)).bottom := by
    have matched := ((supertileNodeGrid_compatible level root).vmatch
      (x / 2) i (by dsimp only [side] at hx; omega) hi).1
    rcases Nat.mod_two_eq_zero_or_one x with hxbit | hxbit <;>
      simpa [block, quarterTile, quadrantAt, Quadrant.ofBits,
        subdivideTileAt_vertical_iff, hxbit] using matched
  simpa only [block, site, supertileIndexGrid, quadrantAt, Nat.mod_mod] using
    adjacent_pairs (fun a b : QuarterIndex => (quarterTile a).top = (quarterTile b).bottom)
      block within between (x := y) (by dsimp only [side] at hy; exact hy)

/-- A canonical three-layer patch of the concrete scaffold, with matching edges and local
shade/signal allowance proved from the closed decorated substitution. -/
@[expose] def canonicalPatch (level : ℕ) (root : Node) :
    Rectangle scaffold.tiles (side level) (side level) where
  tile i j := ShadedSite.tile (site level root i.val j.val)
  mem i j := by
    exact ShadedSite.tile_mem _
      ((supertile_validShadeRectangle level root).allowed i.val j.val i.isLt j.isLt)
      (site_allowed level root i.val j.val i.isLt j.isLt)
  horizontal i j hi := by
    exact (ShadedSite.horizontal_iff _ _).mpr
      ⟨quarter_hmatch level root i.val j.val hi j.isLt,
        (supertile_validShadeRectangle level root).hmatch i.val j.val hi j.isLt, rfl⟩
  vertical i j hj := by
    exact (ShadedSite.vertical_iff _ _).mpr
      ⟨quarter_vmatch level root i.val j.val i.isLt hj,
        (supertile_validShadeRectangle level root).vmatch i.val j.val i.isLt hj, rfl⟩

/-- Canonical patch sides grow beyond their substitution level. -/
theorem lt_side (level : ℕ) : level < side level := by
  have := Nat.lt_two_pow_self (n := level)
  have := Nat.pow_le_pow_left (n := 2) (m := 4) (by decide) level
  dsimp only [side]; omega

/-- The concrete decorated Robinson scaffold has a plane tiling, by compactness of its
canonical finite squares. This proves scaffold nonemptiness, not payload realization. -/
theorem scaffold_tilesPlane : TilesPlane scaffold.tiles :=
  (tilesPlane_iff_squares _).mpr fun n =>
    ⟨(canonicalPatch (n + 1) seedNode).crop (lt_side (n + 1)).le (lt_side (n + 1)).le⟩

end Cslib.WangTile.Robinson.Canonical
