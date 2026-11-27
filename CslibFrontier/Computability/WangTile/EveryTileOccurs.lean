/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic

/-!
# The tiling problem in which every tile must occur

The tiling problem that Hirsch and Hodkinson reduce to representability of finite relation
algebras asks of a finite set of Wang tiles whether each of its tiles lies at the origin of some
tiling of the plane by the set [HirschHodkinson2001], Section 3. This is not the domino problem:
a set that tiles the plane may contain a tile that no tiling uses.

## Main definitions

* `Cslib.WangTile.EveryTileOccurs`: every tile of a list is at the origin of a tiling by the list.
* `Cslib.WangTile.EveryIndexOccurs`: the same for tilings by positions of the list, the form in
  which the source states the problem.
* `Cslib.WangTile.freshTile`: a tile with one colour on its four edges, used by no tile of the
  list; the source's special tile `T₀`.

## Main results

* `Cslib.WangTile.lt_freshTile`: the colour of the fresh tile exceeds every colour of the list.
* `Cslib.WangTile.everyTileOccurs_iff_everyIndexOccurs`: the two forms of the problem agree.
* `Cslib.WangTile.everyTileOccurs_cons_freshTile_iff`: adjoining the fresh tile to a list does
  not change the answer.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.WangTile

/-- Every tile of `τ` is at the origin of some tiling of the plane by `τ`. -/
@[expose] def EveryTileOccurs (τ : List WangTile) : Prop :=
  ∀ t ∈ τ, TilesAtOrigin ⟨τ, t⟩

/-- Every position of the list `L` is at the origin of some tiling of the plane by positions of
`L`: there are maps `F : ℤ → ℤ → Fin L.length`, one with `F 0 0 = i` for each position `i`, in
which the tiles at horizontally and vertically adjacent cells match. This is the tiling problem
of [HirschHodkinson2001], Section 3, where the tiles are `T₀, …, Tₖ₋₁` and a tiling is a map to
`{0, …, k - 1}`. -/
@[expose] def EveryIndexOccurs (L : List WangTile) : Prop :=
  ∀ i : Fin L.length, ∃ F : ℤ → ℤ → Fin L.length, F 0 0 = i ∧ ∀ x y,
    L[F x y].right = L[F (x + 1) y].left ∧ L[F x y].top = L[F x (y + 1)].bottom

/-- A tile whose four edges carry one colour, which is larger than every colour of a tile of
`τ`. -/
@[expose] def freshTile (τ : List WangTile) : WangTile :=
  let c := τ.foldr (fun t c => max (max (max t.top t.bottom) (max t.left t.right) + 1) c) 0
  ⟨c, c, c, c⟩

/-- The two problems agree: a tiling by positions gives a tiling by their tiles, and a tiling by
tiles of the list is one by positions holding them, where the position at the origin can be any
that holds the tile there. -/
theorem everyTileOccurs_iff_everyIndexOccurs {L : List WangTile} :
    EveryTileOccurs L ↔ EveryIndexOccurs L := by
  constructor
  · intro h i
    obtain ⟨f, hf, hmem⟩ := h L[i] (L.getElem_mem i.isLt)
    choose idx hidx using fun x y => List.mem_iff_get.mp (hmem x y).1
    let F (x y : ℤ) : Fin L.length := if x = 0 ∧ y = 0 then i else idx x y
    have hF (x y : ℤ) : L[F x y] = f x y := by
      by_cases hxy : x = 0 ∧ y = 0
      · simp [F, hxy, hf]
      · simpa [F, hxy] using hidx x y
    exact ⟨F, by simp [F], fun x y => by simpa only [hF] using (hmem x y).2⟩
  · intro h t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨F, hF, hmatch⟩ := h ⟨i, hi⟩
    exact ⟨fun x y => L[F x y], by simp [hF], fun x y => ⟨L.getElem_mem _, hmatch x y⟩⟩

/-- Every colour of a tile of `τ` is smaller than the colour on the four edges of `freshTile τ`,
which is therefore on no edge of a tile of `τ`. -/
theorem lt_freshTile {τ : List WangTile} {t : WangTile} (ht : t ∈ τ) :
    max (max t.top t.bottom) (max t.left t.right) < (freshTile τ).top := by
  induction τ with
  | nil => simp at ht
  | cons s τ ih =>
    obtain rfl | ht := List.mem_cons.mp ht
    · exact lt_max_of_lt_left (Nat.lt_succ_self _)
    · exact lt_max_of_lt_right (ih ht)

/-- Adjoining the fresh tile does not change the problem: it tiles the plane by itself, and in
no tiling does it lie beside another tile, so a tiling with a tile of `τ` at the origin does not
use it. This is the reduction to tile sets with a special tile in [HirschHodkinson2001],
Section 3. -/
theorem everyTileOccurs_cons_freshTile_iff {τ : List WangTile} :
    EveryTileOccurs (freshTile τ :: τ) ↔ EveryTileOccurs τ := by
  constructor
  · intro h t ht
    obtain ⟨f, hf : f 0 0 = t, hmem : ∀ x y, f x y ∈ freshTile τ :: τ ∧ _⟩ :=
      h t (List.mem_cons_of_mem _ ht)
    -- neighbours of the fresh tile are fresh, since their touching colours are equal
    have key {a b : WangTile} (ha : a ∈ freshTile τ :: τ) (hb : b ∈ freshTile τ :: τ)
        (hab : a.right = b.left ∨ a.top = b.bottom) : a = freshTile τ ↔ b = freshTile τ := by
      obtain rfl | ha := List.mem_cons.mp ha <;> obtain rfl | hb := List.mem_cons.mp hb
      · exact .rfl
      · have := lt_freshTile hb
        obtain h | h := hab <;> exact (by simp only [freshTile] at h this ⊢; omega : False).elim
      · have := lt_freshTile ha
        obtain h | h := hab <;> exact (by simp only [freshTile] at h this ⊢; omega : False).elim
      · have := lt_freshTile ha
        have := lt_freshTile hb
        constructor <;> rintro rfl <;> simp only [freshTile] at * <;> omega
    have hrow (x y : ℤ) : f x y = freshTile τ ↔ f (x + 1) y = freshTile τ :=
      key (hmem x y).1 (hmem (x + 1) y).1 (.inl (hmem x y).2.1)
    have hcol (x y : ℤ) : f x y = freshTile τ ↔ f x (y + 1) = freshTile τ :=
      key (hmem x y).1 (hmem x (y + 1)).1 (.inr (hmem x y).2.2)
    have row (x y : ℤ) : f x y = freshTile τ ↔ f 0 y = freshTile τ := by
      induction x with
      | zero => rfl
      | succ n ih => exact (hrow n y).symm.trans ih
      | pred n ih => rw [← ih, hrow, sub_add_cancel]
    have col (y : ℤ) : f 0 y = freshTile τ ↔ f 0 0 = freshTile τ := by
      induction y with
      | zero => rfl
      | succ n ih => exact (hcol 0 n).symm.trans ih
      | pred n ih => rw [← ih, hcol, sub_add_cancel]
    have h0 : f 0 0 ≠ freshTile τ := by
      rintro h0
      have := lt_freshTile ht
      rw [← hf, h0] at this
      simp only [freshTile] at this
      omega
    refine ⟨f, hf, fun x y => ⟨?_, (hmem x y).2⟩⟩
    exact (List.mem_cons.mp (hmem x y).1).resolve_left fun h => h0 ((col y).mp ((row x y).mp h))
  · intro h t ht
    obtain rfl | ht := List.mem_cons.mp ht
    · exact ⟨fun _ _ => freshTile τ, rfl, fun _ _ => ⟨List.mem_cons_self, rfl, rfl⟩⟩
    · obtain ⟨f, hf, hmem⟩ := h t ht
      exact ⟨f, hf, fun x y => ⟨List.mem_cons_of_mem _ (hmem x y).1, (hmem x y).2⟩⟩

end Cslib.WangTile
