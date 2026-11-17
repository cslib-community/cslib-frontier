/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Reduction
import CslibFrontier.Computability.RelationAlgebra.Undecidable

/-! # The relation algebra of a tile list: checked instances

The frame and the table of `RA(τ)` on small lists of tiles: the rules that make tile edges match,
the agreement of the arithmetic on atom numbers with the frame, lists of tiles that are
instances of the reduction, and the undecidability theorem applied to a Boolean decision
procedure. -/

@[expose] public section

namespace Cslib.Tests.RelationAlgebraTiling

open Cslib Cslib.RelationAlgebra Cslib.WangTile Tiling Tiling.Atom

/-- Two tiles: the first matches itself in both directions, the second in neither, and the first
can stand to the left of the second but not to its right. -/
def tiles : List WangTile := [⟨0, 0, 0, 0⟩, ⟨1, 2, 0, 3⟩]

/-- The first position of `tiles`. -/
def t₀ : Fin tiles.length := ⟨0, by decide⟩

/-- The second position of `tiles`. -/
def t₁ : Fin tiles.length := ⟨1, by decide⟩

/-! ### The frame -/

/-- ∀ may ask for a green apex over any tile edge. -/
example : (green .one .reverse, green .two .forward, tile t₁ .forward) ∈
    (tilingFrame tiles).cycles := by decide

/-- Rule 1: an edge with a green apex is not white. -/
example : (green .one .reverse, green .two .forward, white .one .two) ∉
    (tilingFrame tiles).cycles := by decide

/-- Rule 2: with a step from the column of `t₀` to the column of `t₁` the tiles match, since the
right colour of the first is the left colour of the second. -/
example : (tile t₁ .forward, tile t₀ .reverse, step .one .reverse) ∈
    (tilingFrame tiles).cycles := by decide

/-- Rule 2: the other way round they do not match. -/
example : (tile t₀ .forward, tile t₁ .reverse, step .one .reverse) ∉
    (tilingFrame tiles).cycles := by decide

/-- The dual of rule 2: the second tile cannot stand above itself. -/
example : (tile t₁ .reverse, tile t₁ .forward, step .two .reverse) ∉
    (tilingFrame tiles).cycles := by decide

/-- Rule 3 forbids `u` over a tile edge, except for the tile at position `0`. -/
example : (u .one .reverse, green .two .forward, tile t₁ .forward) ∉
      (tilingFrame tiles).cycles ∧
    (u .one .reverse, green .two .forward, tile t₀ .forward) ∈ (tilingFrame tiles).cycles := by
  decide

/-- Rule 4 in one of its Peircean transforms: `(g₀₁, -1₁, v₀₁)`. -/
example : (green .one .forward, step .one .reverse, v .one .forward) ∉
    (tilingFrame tiles).cycles := by decide

/-- A network with two nodes, a `1`-node and a `2`-node joined by a tile edge, built from its
labels. -/
def tileEdge : AtomicNetwork (tilingFrame tiles) Bool :=
  Tiling.network
    (fun d e => match d, e with
      | false, false => unit .one
      | false, true => tile t₁ .forward
      | true, false => tile t₁ .reverse
      | true, true => unit .two)
    (fun d => if d then .two else .one) (by decide) (by decide) (by decide) (by decide)

example : tileEdge false true = tile t₁ .forward := rfl

/-! ### The table -/

example : (tilingTable tiles).size = 32 := rfl

example : (tilingTable tiles).conv =
    [0, 1, 2, 3, 6, 9, 4, 7, 10, 5, 8, 11, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24,
      27, 26, 29, 28, 31, 30] := by decide

/-- Atoms on which every rule and each kind of node occurs. -/
def sample : List (Atom (Fin tiles.length)) :=
  [unit .one, white .one .two, white .two .one, green .one .forward, green .one .reverse,
    green .two .forward, u .one .reverse, u .two .reverse, v .one .reverse, v .two .forward,
    step .one .forward, step .one .reverse, step .two .reverse, tile t₀ .forward,
    tile t₀ .reverse, tile t₁ .forward, tile t₁ .reverse]

/-- On the sample, the arithmetic on atom numbers that defines the table agrees with the
frame. -/
example : ∀ r ∈ sample, ∀ s ∈ sample, ∀ t ∈ sample,
    (CycleCode tiles r.code s.code t.code ↔ (r, s, t) ∈ (tilingFrame tiles).cycles) := by
  decide

/-! ### The tiling problem and the reduction -/

example : freshTile tiles = ⟨4, 4, 4, 4⟩ := rfl

/-- The empty list is a yes-instance of the tiling problem. -/
example : EveryTileOccurs [] := by simp [EveryTileOccurs]

/-- Through the reduction, the table of the algebra of the special tile alone satisfies the
predicate of the representation problem. -/
example : (tilingTable [freshTile []]).IsRepresentable :=
  (everyTileOccurs_iff_isRepresentable []).mp (by simp [EveryTileOccurs])

/-- A tile that tiles the plane by itself. -/
example : EveryTileOccurs [⟨0, 0, 0, 0⟩] := fun t ht =>
  ⟨fun _ _ => t, rfl, fun _ _ => ⟨ht, by simp_all⟩⟩

/-- A list whose only tile does not match itself vertically is a no-instance of the tiling
problem, and the table of its algebra is a no-instance of the representation problem, by
Theorems 1 and 3. -/
example : ¬EveryTileOccurs [⟨0, 1, 0, 0⟩] ∧ ¬(tilingTable [⟨0, 1, 0, 0⟩]).IsRepresentable := by
  have h : ¬EveryIndexOccurs [⟨0, 1, 0, 0⟩] := fun h => by
    obtain ⟨F, -, hF⟩ := h ⟨0, by decide⟩
    have := (hF 0 0).2
    simp [Fin.fin_one_eq_zero] at this
  exact ⟨fun h' => h (everyTileOccurs_iff_everyIndexOccurs.mp h'),
    fun h' => h (everyIndexOccurs_of_hasWinningStrategy (isRepresentable_tilingTable_iff.mp h'))⟩

/-- No computable Boolean function decides the representation problem, with the predicate named
by `AtomTable.IsRepresentable` rather than written out as in the theorem. -/
example (f : AtomTable → Bool) (hf : Computable f) : ¬∀ t, f t = true ↔ t.IsRepresentable := by
  intro decides
  apply AtomTable.not_computablePred_representable_complexAlgebra
  have hp : ComputablePred fun t => f t = true := ⟨inferInstance, hf.of_eq fun _ => by simp⟩
  exact hp.of_eq decides

end Cslib.Tests.RelationAlgebraTiling
