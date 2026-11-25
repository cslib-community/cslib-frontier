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
  refine ⟨fun h i => ?_, fun h t ht => ?_⟩
  · obtain ⟨f, hf, hmem⟩ := h L[i] (L.getElem_mem i.isLt)
    choose idx hidx using fun x y => List.mem_iff_get.mp (hmem x y).1
    let F (x y : ℤ) : Fin L.length := if x = 0 ∧ y = 0 then i else idx x y
    have hF (x y : ℤ) : L[F x y] = f x y := by
      by_cases hxy : x = 0 ∧ y = 0
      · simp [F, hxy, hf]
      · simpa [F, hxy] using hidx x y
    exact ⟨F, by simp [F], fun x y => by simpa only [hF] using (hmem x y).2⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨F, hF, hmatch⟩ := h ⟨i, hi⟩
    exact ⟨fun x y => L[F x y], by simp [hF], fun x y => ⟨L.getElem_mem _, hmatch x y⟩⟩

/-- Every colour of a tile of `τ` is smaller than the colour on the four edges of `freshTile τ`,
which is therefore on no edge of a tile of `τ`. -/
theorem lt_freshTile {τ : List WangTile} {t : WangTile} (ht : t ∈ τ) :
    max (max t.top t.bottom) (max t.left t.right) < (freshTile τ).top := by
  induction τ with
  | nil => simp at ht
  | cons _ _ ih =>
    exact (List.mem_cons.mp ht).elim
      (fun h => h ▸ lt_max_of_lt_left (Nat.lt_succ_self _)) (fun h => lt_max_of_lt_right (ih h))

/-- Adjoining the fresh tile does not change the problem: it tiles the plane by itself, and in
no tiling does it lie beside another tile, so a tiling with a tile of `τ` at the origin does not
use it. This is the reduction to tile sets with a special tile in [HirschHodkinson2001],
Section 3. -/
theorem everyTileOccurs_cons_freshTile_iff {τ : List WangTile} :
    EveryTileOccurs (freshTile τ :: τ) ↔ EveryTileOccurs τ := by
  refine ⟨fun h t ht => ?_, fun h t ht => (List.mem_cons.mp ht).elim
    (fun e => by
      subst e
      exact ⟨fun _ _ => freshTile τ, rfl, fun _ _ => ⟨List.mem_cons_self, rfl, rfl⟩⟩)
    fun ht' => by
      obtain ⟨f, hf, hmem⟩ := h t ht'
      exact ⟨f, hf, fun x y => ⟨List.mem_cons_of_mem _ (hmem x y).1, (hmem x y).2⟩⟩⟩
  obtain ⟨f, hf : f 0 0 = t, hmem : ∀ x y, f x y ∈ freshTile τ :: τ ∧ _⟩ :=
    h t (List.mem_cons_of_mem _ ht)
  have hno {s : WangTile} (hs : s ∈ τ)
      (h : (freshTile τ).right = s.left ∨ (freshTile τ).top = s.bottom ∨
        s.right = (freshTile τ).left ∨ s.top = (freshTile τ).bottom) : False := by
    have := lt_freshTile hs
    simp only [freshTile] at h this; omega
  -- neighbours of the fresh tile are fresh, since their touching colours are equal
  have key {a b : WangTile} (ha : a ∈ freshTile τ :: τ) (hb : b ∈ freshTile τ :: τ)
      (hab : a.right = b.left ∨ a.top = b.bottom) : a = freshTile τ ↔ b = freshTile τ :=
    ⟨fun e => (List.mem_cons.mp hb).resolve_right fun hb' =>
      hno hb' ((e ▸ hab).imp id .inl),
     fun e => (List.mem_cons.mp ha).resolve_right fun ha' =>
      hno ha' (.inr (.inr (e ▸ hab)))⟩
  have shift {P : ℤ → Prop} (hP : ∀ z, P z ↔ P (z + 1)) (z : ℤ) : P z ↔ P 0 := by
    induction z with
    | zero => rfl
    | succ n ih => exact (hP n).symm.trans ih
    | pred n ih => exact (hP _).trans (by simpa only [sub_add_cancel] using ih)
  have h0 : f 0 0 ≠ freshTile τ := fun e => by
    have := e ▸ hf ▸ lt_freshTile ht
    simp only [freshTile] at this; omega
  refine ⟨f, hf, fun x y => ⟨(List.mem_cons.mp (hmem x y).1).resolve_left fun hx => h0 ?_,
    (hmem x y).2⟩⟩
  exact (shift (fun y => key (hmem 0 y).1 (hmem 0 (y + 1)).1 (.inr (hmem 0 y).2.2)) y).mp
    ((shift (fun x => key (hmem x y).1 (hmem (x + 1) y).1 (.inl (hmem x y).2.1)) x).mp hx)

end Cslib.WangTile
