/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
meta import Lean.Data.RArray

/-!
# Corrected Robinson tiles and their substitution

This module uses lean-wang's corrected transcription of the 104-tile Ollinger–Robinson
alphabet and its substitution. Its thin, thick and black layers contribute edge-colour digits
in bases 4, 4 and 2. The substitution replaces each tile by a matching square of four tiles,
preserves matching across adjacent squares, and reflects
matching of their boundaries. Thin-layer matching determines the parity phases of a tiling.

## Main definitions

* `Components` and `components`: the three layers of each of the 104 tiles.
* `tile` and `tileSet`: the edge-colour interpretation and finite palette.
* `childBlock`: the corrected Figure 16 substitution, with west/east coordinate first.
* `refineIndexGrid`, `iterateRefine`: simultaneous substitution of natural-coordinate grids.

## Main results

* `tile_components_injective`: distinct indices represent distinct Wang tiles.
* `child_horizontal`, `child_vertical`: each substitution square matches internally.
* `horizontal_iff_children`, `vertical_iff_children`: boundary matching is preserved and reflected.
* `thin_east`, `thin_north`: the forced neighboring thin-layer phases.

## References

The tile set originates in [Ollinger2008], as presented in [JeandelVanier2020], §3.2
(authors' manuscript pp. 22–26), Figures 13 and 16; the matching and recognition arguments
follow the corresponding steps of Proposition 8 on p. 24.

Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3), revision
`64268a3`, the `Robinson.Closed104.Data`, `Figure16`, `Tiles` and `RedBoards` modules.
Here “corrected” identifies the transcription specified in its
[plan, lines 94–98](https://github.com/edemaine/lean-wang/blob/64268a3/plan.md#L94-L98):
the 104 triples of `figures/fig13-human.tsv` and the second thick-layer summand at `L2b`
with southeast entry `R1` rather than `R3` in the transcription of Figure 16(c).
Its numeric edge coding retains both boundary lanes and two colours in each thin/thick
layer, and one black-layer bit. Agreement with the printed figures is not checked in Lean;
the results concern the explicit palette and substitution below.
-/

public section
namespace Cslib.WangTile.Robinson

/-- The four thin-layer phases in the corrected Figure 13 alphabet. -/
inductive Thin where
  | a | b | c | d
  deriving DecidableEq

/-- The twenty thick-layer components in the corrected Figure 13 alphabet. -/
inductive Thick where
  | a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s | t
  deriving DecidableEq

/-- The five black-layer components in the corrected Figure 13 alphabet. -/
inductive Black where
  | a | b | c | d | e
  deriving DecidableEq

/-- A corrected Robinson tile's three superimposed component layers. -/
structure Components where
  /-- The thin-layer phase. -/
  thin : Thin
  /-- The thick-layer component. -/
  thick : Thick
  /-- The black-layer component. -/
  black : Black
  deriving DecidableEq

/-- Index in the corrected 104-tile alphabet, in Figure 13 order. -/
abbrev Index := Fin 104

private meta def quoteLookupTable : Lean.RArray Lean.Term → Lean.MacroM Lean.Term
  | .leaf entry => `(Lean.RArray.leaf $entry)
  | .branch index left right => do
    let pivot := Lean.Syntax.mkNumLit (toString index)
    `(Lean.RArray.branch $pivot $(← quoteLookupTable left) $(← quoteLookupTable right))

/-- Build a balanced table literal for kernel reduction in finite Robinson certificates.
Indices in the range of the literal select the corresponding source entry. -/
scoped macro "lookupTable![" xs:term,+ "]" : term => do
  let entries := xs.getElems
  if h : 0 < entries.size then
    quoteLookupTable (Lean.RArray.ofArray entries h)
  else
    Lean.Macro.throwError "expected a nonempty lookup table"

/-- The component triple of a tile in the corrected Figure 13 alphabet. -/
@[expose] def components (index : Index) : Components :=
  let table : Lean.RArray Components := lookupTable![
    ⟨.a, .b, .a⟩, ⟨.a, .c, .a⟩, ⟨.a, .a, .a⟩,
    ⟨.a, .d, .a⟩, ⟨.b, .b, .a⟩, ⟨.b, .c, .a⟩,
    ⟨.b, .a, .a⟩, ⟨.b, .d, .a⟩, ⟨.c, .m, .b⟩,
    ⟨.c, .m, .c⟩, ⟨.c, .i, .b⟩, ⟨.c, .i, .c⟩,
    ⟨.c, .t, .c⟩, ⟨.c, .e, .c⟩, ⟨.c, .j, .c⟩,
    ⟨.c, .h, .c⟩, ⟨.c, .l, .b⟩, ⟨.c, .f, .b⟩,
    ⟨.c, .r, .b⟩, ⟨.c, .g, .b⟩, ⟨.c, .o, .b⟩,
    ⟨.c, .o, .c⟩, ⟨.c, .k, .b⟩, ⟨.c, .k, .c⟩,
    ⟨.c, .n, .b⟩, ⟨.c, .n, .c⟩, ⟨.c, .q, .b⟩,
    ⟨.c, .q, .c⟩, ⟨.c, .p, .b⟩, ⟨.c, .p, .c⟩,
    ⟨.c, .s, .b⟩, ⟨.c, .s, .c⟩, ⟨.a, .m, .b⟩,
    ⟨.a, .m, .c⟩, ⟨.a, .i, .b⟩, ⟨.a, .i, .c⟩,
    ⟨.a, .t, .c⟩, ⟨.a, .e, .c⟩, ⟨.a, .j, .c⟩,
    ⟨.a, .h, .c⟩, ⟨.a, .l, .b⟩, ⟨.a, .f, .b⟩,
    ⟨.a, .r, .b⟩, ⟨.a, .g, .b⟩, ⟨.a, .o, .b⟩,
    ⟨.a, .o, .c⟩, ⟨.a, .k, .b⟩, ⟨.a, .k, .c⟩,
    ⟨.a, .n, .b⟩, ⟨.a, .n, .c⟩, ⟨.a, .q, .b⟩,
    ⟨.a, .q, .c⟩, ⟨.a, .p, .b⟩, ⟨.a, .p, .c⟩,
    ⟨.a, .s, .b⟩, ⟨.a, .s, .c⟩, ⟨.d, .t, .d⟩,
    ⟨.d, .t, .e⟩, ⟨.d, .e, .d⟩, ⟨.d, .j, .d⟩,
    ⟨.d, .j, .e⟩, ⟨.d, .h, .e⟩, ⟨.d, .l, .d⟩,
    ⟨.d, .l, .e⟩, ⟨.d, .f, .d⟩, ⟨.d, .r, .d⟩,
    ⟨.d, .r, .e⟩, ⟨.d, .g, .e⟩, ⟨.d, .o, .d⟩,
    ⟨.d, .o, .e⟩, ⟨.d, .k, .d⟩, ⟨.d, .n, .d⟩,
    ⟨.d, .n, .e⟩, ⟨.d, .q, .e⟩, ⟨.d, .p, .d⟩,
    ⟨.d, .p, .e⟩, ⟨.d, .s, .d⟩, ⟨.d, .m, .d⟩,
    ⟨.d, .m, .e⟩, ⟨.d, .i, .e⟩, ⟨.a, .t, .d⟩,
    ⟨.a, .t, .e⟩, ⟨.a, .e, .d⟩, ⟨.a, .j, .d⟩,
    ⟨.a, .j, .e⟩, ⟨.a, .h, .e⟩, ⟨.a, .l, .d⟩,
    ⟨.a, .l, .e⟩, ⟨.a, .f, .d⟩, ⟨.a, .r, .d⟩,
    ⟨.a, .r, .e⟩, ⟨.a, .g, .e⟩, ⟨.a, .o, .d⟩,
    ⟨.a, .o, .e⟩, ⟨.a, .k, .d⟩, ⟨.a, .n, .d⟩,
    ⟨.a, .n, .e⟩, ⟨.a, .q, .e⟩, ⟨.a, .p, .d⟩,
    ⟨.a, .p, .e⟩, ⟨.a, .s, .d⟩, ⟨.a, .m, .d⟩,
    ⟨.a, .m, .e⟩, ⟨.a, .i, .e⟩
  ]
  table.get index.val

/-- Superimpose thin, thick and black edge digits with weights 1, 4 and 16. -/
@[expose] def tile (layers : Components) : WangTile :=
  let thin : WangTile := match layers.thin with
    | .a => ⟨1, 2, 2, 1⟩
    | .b => ⟨3, 0, 0, 3⟩
    | .c => ⟨0, 3, 1, 2⟩
    | .d => ⟨2, 1, 3, 0⟩
  let thick : WangTile := match layers.thick with
    | .a => ⟨2, 1, 3, 0⟩
    | .b => ⟨1, 2, 2, 1⟩
    | .c => ⟨0, 3, 1, 2⟩
    | .d => ⟨3, 0, 0, 3⟩
    | .e => ⟨1, 1, 1, 1⟩
    | .f => ⟨0, 0, 1, 1⟩
    | .g => ⟨0, 0, 0, 0⟩
    | .h => ⟨1, 1, 0, 0⟩
    | .i => ⟨3, 3, 0, 0⟩
    | .j => ⟨1, 1, 3, 3⟩
    | .k => ⟨2, 2, 1, 1⟩
    | .l => ⟨0, 0, 2, 2⟩
    | .m => ⟨3, 3, 3, 3⟩
    | .n => ⟨2, 2, 3, 3⟩
    | .o => ⟨2, 2, 2, 2⟩
    | .p => ⟨3, 3, 2, 2⟩
    | .q => ⟨2, 2, 0, 0⟩
    | .r => ⟨0, 0, 3, 3⟩
    | .s => ⟨3, 3, 1, 1⟩
    | .t => ⟨1, 1, 2, 2⟩
  let black : WangTile := match layers.black with
    | .a => ⟨0, 1, 1, 0⟩
    | .b => ⟨1, 0, 0, 0⟩
    | .c => ⟨1, 0, 1, 1⟩
    | .d => ⟨1, 1, 0, 1⟩
    | .e => ⟨0, 0, 0, 1⟩
  ⟨thin.top + 4 * thick.top + 16 * black.top,
    thin.bottom + 4 * thick.bottom + 16 * black.bottom,
    thin.left + 4 * thick.left + 16 * black.left,
    thin.right + 4 * thick.right + 16 * black.right⟩

/-- Distinct alphabet indices represent distinct Wang tiles. -/
theorem tile_components_injective : Function.Injective (fun i : Index => tile (components i)) := by
  have h : ∀ i j : Index,
      (tile (components i)).top = (tile (components j)).top →
      (tile (components i)).bottom = (tile (components j)).bottom →
      (tile (components i)).left = (tile (components j)).left →
      (tile (components i)).right = (tile (components j)).right → i = j := by decide +kernel
  intro i j hij
  exact h i j (congrArg WangTile.top hij) (congrArg WangTile.bottom hij)
    (congrArg WangTile.left hij) (congrArg WangTile.right hij)

/-- The 104 corrected tiles, with the component alphabet's order retained. -/
def tileSet : List WangTile :=
  (List.finRange 104).map fun index => tile (components index)

/-- Palette membership is witnessed by an index in the corrected alphabet. -/
theorem mem_tileSet {t : WangTile} :
    t ∈ tileSet ↔ ∃ index : Index, tile (components index) = t := by
  simp [tileSet]

/-- Every indexed corrected tile belongs to the concrete palette. -/
theorem tile_components_mem (index : Index) : tile (components index) ∈ tileSet :=
  mem_tileSet.mpr ⟨index, rfl⟩

/-- The corrected Figure 16 substitution; `x = 0` is west and `y = 0` is south.
The 416 entries flatten lean-wang's layer rules `phiL1Star`, `phiL2Component1`,
`phiL2Component2` and `phiL3` at the revision cited in the module documentation. -/
@[expose] def childBlock (parent : Index) (x y : Fin 2) : Index :=
  let square (sw se nw ne : Index) : Index :=
    if y = 0 then (if x = 0 then sw else se) else (if x = 0 then nw else ne)
  let table : Lean.RArray Index := lookupTable![
    square 0 22 57 4, square 1 20 63 4, square 2 26 69 4,
    square 3 24 75 4, square 0 17 61 7, square 1 16 67 7,
    square 2 19 73 7, square 3 18 79 7, square 32 8 76 5,
    square 33 9 76 5, square 34 10 76 5, square 35 11 76 5,
    square 36 29 58 5, square 37 31 58 5, square 38 9 58 5,
    square 39 11 58 5, square 40 28 64 5, square 41 30 64 5,
    square 42 8 64 5, square 43 10 64 5, square 44 28 70 5,
    square 45 29 70 5, square 46 30 70 5, square 47 31 70 5,
    square 48 8 70 5, square 49 9 70 5, square 50 10 70 5,
    square 51 11 70 5, square 52 28 76 5, square 53 29 76 5,
    square 54 30 76 5, square 55 31 76 5, square 32 24 74 4,
    square 33 25 74 4, square 34 26 74 4, square 35 27 74 4,
    square 36 21 56 4, square 37 23 56 4, square 38 25 56 4,
    square 39 27 56 4, square 40 20 62 4, square 41 22 62 4,
    square 42 24 62 4, square 43 26 62 4, square 44 20 68 4,
    square 45 21 68 4, square 46 22 68 4, square 47 23 68 4,
    square 48 24 68 4, square 49 25 68 4, square 50 26 68 4,
    square 51 27 68 4, square 52 20 74 4, square 53 21 74 4,
    square 54 22 74 4, square 55 23 74 4, square 80 12 59 6,
    square 81 12 60 6, square 82 13 59 6, square 83 14 59 6,
    square 84 14 60 6, square 85 15 60 6, square 86 12 65 6,
    square 87 12 66 6, square 88 13 65 6, square 89 14 65 6,
    square 90 14 66 6, square 91 15 66 6, square 92 12 71 6,
    square 93 12 72 6, square 94 13 71 6, square 95 14 71 6,
    square 96 14 72 6, square 97 15 72 6, square 98 12 77 6,
    square 99 12 78 6, square 100 13 77 6, square 101 14 77 6,
    square 102 14 78 6, square 103 15 78 6, square 80 21 56 4,
    square 81 21 57 4, square 82 23 56 4, square 83 25 56 4,
    square 84 25 57 4, square 85 27 57 4, square 86 21 62 4,
    square 87 21 63 4, square 88 23 62 4, square 89 25 62 4,
    square 90 25 63 4, square 91 27 63 4, square 92 21 68 4,
    square 93 21 69 4, square 94 23 68 4, square 95 25 68 4,
    square 96 25 69 4, square 97 27 69 4, square 98 21 74 4,
    square 99 21 75 4, square 100 23 74 4, square 101 25 74 4,
    square 102 25 75 4, square 103 27 75 4
  ]
  table.get parent.val

/-- Simultaneous substitution of an index grid at the quotient and parity coordinates. -/
@[expose] def refineIndexGrid (grid : Nat → Nat → Index) (x y : Nat) : Index :=
  childBlock (grid (x / 2) (y / 2))
    ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩

/-- Substitution at an arbitrary child position. -/
@[simp] theorem refineIndexGrid_child (grid : Nat → Nat → Index) (x y : Nat)
    (dx dy : Fin 2) :
    refineIndexGrid grid (2 * x + dx) (2 * y + dy) = childBlock (grid x y) dx dy := by
  have hx : (2 * x + dx) / 2 = x := by omega
  have hy : (2 * y + dy) / 2 = y := by omega
  have hdx : (2 * x + dx) % 2 = dx := by omega
  have hdy : (2 * y + dy) % 2 = dy := by omega
  simp only [refineIndexGrid, hx, hy, hdx, hdy]

/-- Iterate simultaneous substitution. -/
@[expose] def iterateRefine : Nat → (Nat → Nat → Index) → Nat → Nat → Index
  | 0, grid => grid
  | level + 1, grid => refineIndexGrid (iterateRefine level grid)

/-- Refining in two successive stages adds their depths. -/
theorem iterateRefine_add (m n : ℕ) (g : ℕ → ℕ → Index) :
    iterateRefine m (iterateRefine n g) = iterateRefine (m + n) g := by
  induction m with
  | zero => simp only [iterateRefine, Nat.zero_add]
  | succ m ih => simp only [iterateRefine, Nat.succ_add, ih]

/-- The substituted block below the origin depends only on the root tile. -/
theorem iterateRefine_eq_of_root_eq {g h : ℕ → ℕ → Index} (eq : g 0 0 = h 0 0) (depth : ℕ) :
    ∀ x y, x < 2 ^ depth → y < 2 ^ depth →
      iterateRefine depth g x y = iterateRefine depth h x y := by
  induction depth with
  | zero =>
    intro x y hx hy
    have : x = 0 ∧ y = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using And.intro hx hy
    simpa only [iterateRefine, this.1, this.2] using eq
  | succ depth ih =>
    intro x y hx hy
    simp only [pow_succ] at hx hy
    simp only [iterateRefine, refineIndexGrid]
    rw [ih (x / 2) (y / 2) (by omega) (by omega)]

/-- The thin-layer phase immediately east of a given phase. -/
@[expose] def phaseEast : Thin → Thin
  | .a => .c | .b => .d | .c => .a | .d => .b

/-- The thin-layer phase immediately north of a given phase. -/
@[expose] def phaseNorth : Thin → Thin
  | .a => .d | .b => .c | .c => .b | .d => .a

private def verifiedAt (parent : Index) : Prop :=
  (∀ x : Fin 2,
    (tile (components (childBlock parent x 0))).top =
      (tile (components (childBlock parent x 1))).bottom) ∧
  (∀ y : Fin 2,
    (tile (components (childBlock parent 0 y))).right =
      (tile (components (childBlock parent 1 y))).left) ∧
  ∀ other : Index,
    ((tile (components parent)).right = (tile (components other)).left ↔
      ∀ y : Fin 2, (tile (components (childBlock parent 1 y))).right =
        (tile (components (childBlock other 0 y))).left) ∧
    ((tile (components parent)).top = (tile (components other)).bottom ↔
      ∀ x : Fin 2, (tile (components (childBlock parent x 1))).top =
        (tile (components (childBlock other x 0))).bottom) ∧
    ((tile (components parent)).right = (tile (components other)).left →
      (components other).thin = phaseEast (components parent).thin) ∧
    ((tile (components parent)).top = (tile (components other)).bottom →
      (components other).thin = phaseNorth (components parent).thin)

private instance (parent : Index) : Decidable (verifiedAt parent) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem verified : ∀ parent : Index, verifiedAt parent := by decide +kernel

/-- Children in each row of a substituted tile match horizontally. -/
theorem child_horizontal (parent : Index) (y : Fin 2) :
    (tile (components (childBlock parent 0 y))).right =
      (tile (components (childBlock parent 1 y))).left :=
  (verified parent).2.1 y

/-- Children in each column of a substituted tile match vertically. -/
theorem child_vertical (parent : Index) (x : Fin 2) :
    (tile (components (childBlock parent x 0))).top =
      (tile (components (childBlock parent x 1))).bottom :=
  (verified parent).1 x

/-- Parent tiles match horizontally exactly when both substitution boundary edges match. -/
theorem horizontal_iff_children (left right : Index) :
    (tile (components left)).right = (tile (components right)).left ↔
      ∀ y : Fin 2, (tile (components (childBlock left 1 y))).right =
        (tile (components (childBlock right 0 y))).left :=
  ((verified left).2.2 right).1

/-- Parent tiles match vertically exactly when both substitution boundary edges match. -/
theorem vertical_iff_children (lower upper : Index) :
    (tile (components lower)).top = (tile (components upper)).bottom ↔
      ∀ x : Fin 2, (tile (components (childBlock lower x 1))).top =
        (tile (components (childBlock upper x 0))).bottom :=
  ((verified lower).2.2 upper).2.1

/-- Horizontal matching determines the eastern tile's thin-layer phase. -/
theorem thin_east {left right : Index}
    (matching : (tile (components left)).right = (tile (components right)).left) :
    (components right).thin = phaseEast (components left).thin :=
  ((verified left).2.2 right).2.2.1 matching

/-- Vertical matching determines the northern tile's thin-layer phase. -/
theorem thin_north {lower upper : Index}
    (matching : (tile (components lower)).top = (tile (components upper)).bottom) :
    (components upper).thin = phaseNorth (components lower).thin :=
  ((verified lower).2.2 upper).2.2.2 matching

/-- Two eastward phase steps return to the original phase. -/
@[simp] theorem phaseEast_involutive (phase : Thin) : phaseEast (phaseEast phase) = phase := by
  cases phase <;> rfl

/-- Two northward phase steps return to the original phase. -/
@[simp] theorem phaseNorth_involutive (phase : Thin) : phaseNorth (phaseNorth phase) = phase := by
  cases phase <;> rfl

end Cslib.WangTile.Robinson
