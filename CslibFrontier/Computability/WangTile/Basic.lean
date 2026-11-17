/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.Primrec.List

/-!
# Wang tiles and finite patches

A Wang tile is an oriented unit square with natural-number edge colours. A finite palette is
a list; repetitions do not affect tiling. We distinguish tilings of the integer plane, tilings
of the natural-number quadrant with a prescribed southwest tile, and plane tilings with a
prescribed tile at the origin. These definitions alone do not establish undecidability;
the unseeded plane theorem is proved in the separate `WangTile.Undecidable` module.

## Main definitions

* `Cslib.WangTile`: the four edge colours, coded in order `(top, bottom, left, right)`.
* `Cslib.WangTile.TilesPlane`: a matching tiling of the integer plane.
* `Cslib.WangTile.SeededInstance`: a palette and a distinguished tile, coded in that order.
* `Cslib.WangTile.TilesQuadrant`, `Cslib.WangTile.TilesAtOrigin`: the two seeded problems.
* `Cslib.WangTile.Rectangle`, `Cslib.WangTile.SeededSquare`: matching finite patches.

## References

The prior formalization is [lean-wang, revision 64268a3, Basic](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Basic.lean).
-/

public section

namespace Cslib

-- Exposed so that `decide` can evaluate the derived `DecidableEq` instance in client modules.
@[expose] public section WangTileDef

/-- A Wang tile: a unit square in fixed orientation with a colour on each edge. -/
structure WangTile where
  /-- The colour on the top edge. -/
  top : ℕ
  /-- The colour on the bottom edge. -/
  bottom : ℕ
  /-- The colour on the left edge. -/
  left : ℕ
  /-- The colour on the right edge. -/
  right : ℕ
  deriving DecidableEq

end WangTileDef

namespace WangTile

/-- A tile is coded as the tuple `(top, bottom, left, right)`. -/
@[expose] def equivProd : WangTile ≃ ℕ × ℕ × ℕ × ℕ where
  toFun t := (t.top, t.bottom, t.left, t.right)
  invFun := fun (top, bottom, left, right) => ⟨top, bottom, left, right⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable WangTile := Primcodable.ofEquiv _ equivProd

/-- The tiles of `τ` tile the plane: some map `ℤ × ℤ → τ` matches colours on every pair of
horizontally and vertically adjacent cells. -/
@[expose] def TilesPlane (τ : List WangTile) : Prop :=
  ∃ f : ℤ → ℤ → WangTile, ∀ x y,
    f x y ∈ τ ∧ (f x y).right = (f (x + 1) y).left ∧ (f x y).top = (f x (y + 1)).bottom

/-- A finite palette with a prescribed tile. The seed need not belong to the palette. -/
structure SeededInstance where
  /-- The tiles allowed in the tiling. -/
  tiles : List WangTile
  /-- The tile prescribed at the origin. -/
  seed : WangTile

/-- A seeded instance is coded as `(tiles, seed)`. -/
@[expose] def SeededInstance.equivProd : SeededInstance ≃ List WangTile × WangTile where
  toFun I := (I.tiles, I.seed)
  invFun := fun (tiles, seed) => ⟨tiles, seed⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable SeededInstance := Primcodable.ofEquiv _ SeededInstance.equivProd

/-- A matching tiling of the quadrant `ℕ × ℕ` whose southwest tile is the seed. -/
@[expose] def TilesQuadrant (I : SeededInstance) : Prop :=
  ∃ f : ℕ → ℕ → WangTile, f 0 0 = I.seed ∧ ∀ x y,
    f x y ∈ I.tiles ∧ (f x y).right = (f (x + 1) y).left ∧
      (f x y).top = (f x (y + 1)).bottom

/-- A matching tiling of the integer plane with the seed at the origin. -/
@[expose] def TilesAtOrigin (I : SeededInstance) : Prop :=
  ∃ f : ℤ → ℤ → WangTile, f 0 0 = I.seed ∧ ∀ x y,
    f x y ∈ I.tiles ∧ (f x y).right = (f (x + 1) y).left ∧
      (f x y).top = (f x (y + 1)).bottom

/-- A matching rectangular patch of width `w` and height `h`, with no boundary conditions. -/
structure Rectangle (τ : List WangTile) (w h : ℕ) where
  /-- The tile at each position, indexed from the southwest corner. -/
  tile : Fin w → Fin h → WangTile
  /-- Every tile belongs to the palette. -/
  mem : ∀ i j, tile i j ∈ τ
  /-- Horizontally adjacent edges match. -/
  horizontal : ∀ (i : Fin w) (j : Fin h) (hi : i.val + 1 < w),
    (tile i j).right = (tile ⟨i.val + 1, hi⟩ j).left
  /-- Vertically adjacent edges match. -/
  vertical : ∀ (i : Fin w) (j : Fin h) (hj : j.val + 1 < h),
    (tile i j).top = (tile i ⟨j.val + 1, hj⟩).bottom

/-- A square of side `n + 1` with prescribed southwest tile. The side is always positive. -/
structure SeededSquare (I : SeededInstance) (n : ℕ)
    extends Rectangle I.tiles (n + 1) (n + 1) where
  /-- The southwest tile is the seed. -/
  corner : tile 0 0 = I.seed

/-- A tile assembled from four primitive-recursive colour functions is primitive recursive. -/
theorem primrec_mk {α : Type*} [Primcodable α] {top bottom left right : α → ℕ}
    (ht : Primrec top) (hb : Primrec bottom) (hl : Primrec left) (hr : Primrec right) :
    Primrec (fun a => WangTile.mk (top a) (bottom a) (left a) (right a)) :=
  (Primrec.of_equiv_symm (e := equivProd)).comp (ht.pair (hb.pair (hl.pair hr)))

/-- Reading a tile's top colour is primitive recursive. -/
theorem primrec_top : Primrec WangTile.top :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivProd))

/-- Reading a tile's bottom colour is primitive recursive. -/
theorem primrec_bottom : Primrec WangTile.bottom :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))

/-- Reading a tile's left colour is primitive recursive. -/
theorem primrec_left : Primrec WangTile.left :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

/-- Reading a tile's right colour is primitive recursive. -/
theorem primrec_right : Primrec WangTile.right :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

/-- Reading the palette of a seeded instance is primitive recursive. -/
theorem SeededInstance.primrec_tiles : Primrec SeededInstance.tiles :=
  Primrec.fst.comp Primrec.of_equiv

/-- Reading the seed of a seeded instance is primitive recursive. -/
theorem SeededInstance.primrec_seed : Primrec SeededInstance.seed :=
  Primrec.snd.comp Primrec.of_equiv

/-- Building a seeded instance from a palette and a seed is primitive recursive. -/
theorem SeededInstance.primrec₂_mk : Primrec₂ SeededInstance.mk :=
  (Primrec.of_equiv_symm.comp Primrec.id : Primrec SeededInstance.equivProd.symm).comp₂
    Primrec₂.pair

end WangTile

end Cslib
