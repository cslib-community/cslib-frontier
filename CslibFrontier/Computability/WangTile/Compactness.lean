/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
import Mathlib.Combinatorics.Compactness
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.NatAbs

/-!
# Compactness for Wang tilings

Finite matching squares of every size suffice to tile the plane. With a prescribed southwest
tile they suffice to tile the quadrant. Both results use Mathlib's Rado selection lemma: on any
finite set of cells the selected global labelling agrees with one sufficiently large patch.

## Main results

* `Cslib.WangTile.tilesPlane_iff_squares`: plane tilings are equivalent to finite squares of
  every positive side length.
* `Cslib.WangTile.tilesQuadrant_iff_seededSquares`: the seeded analogue for quadrants.
-/

public section

namespace Cslib.WangTile

private theorem exists_matching {α : Type} (τ : List WangTile) (east north : α → α)
    (P : α → WangTile → Prop)
    (patch : ∀ s : Finset α, ∃ f : s → {t // t ∈ τ},
      (∀ p : s, P p (f p)) ∧
      (∀ p q : s, (q : α) = east p → (f p).val.right = (f q).val.left) ∧
      (∀ p q : s, (q : α) = north p → (f p).val.top = (f q).val.bottom)) :
    ∃ f : α → WangTile, ∀ p,
      f p ∈ τ ∧ P p (f p) ∧
      (f p).right = (f (east p)).left ∧ (f p).top = (f (north p)).bottom := by
  classical
  let : Fintype {t // t ∈ τ} := Fintype.ofFinset (p := {t | t ∈ τ}) τ.toFinset (by simp)
  choose g hg using patch
  obtain ⟨f, hf⟩ := Finset.rado_selection_subtype (β := fun _ : α => {t // t ∈ τ}) g
  refine ⟨fun p => (f p).val, fun p => ⟨(f p).property, ?_⟩⟩
  obtain ⟨s, hs, heq⟩ := hf {p, east p, north p}
  have hp : p ∈ s := hs (by simp)
  have he : east p ∈ s := hs (by simp)
  have hn : north p ∈ s := hs (by simp)
  simp only [heq ⟨p, by simp⟩,
    heq ⟨east p, by simp⟩,
    heq ⟨north p, by simp⟩]
  exact ⟨(hg s).1 ⟨p, hp⟩, (hg s).2.1 ⟨p, hp⟩ ⟨east p, he⟩ rfl,
    (hg s).2.2 ⟨p, hp⟩ ⟨north p, hn⟩ rfl⟩

private theorem Rectangle.horizontal_eq {τ : List WangTile} {w h : ℕ} (q : Rectangle τ w h)
    {i i' : Fin w} {j j' : Fin h} (hi : i.val + 1 = i'.val) (hj : j = j') :
    (q.tile i j).right = (q.tile i' j').left := by
  simpa only [hj, Fin.ext_iff, hi] using q.horizontal i j (hi ▸ i'.isLt)

private theorem Rectangle.vertical_eq {τ : List WangTile} {w h : ℕ} (q : Rectangle τ w h)
    {i i' : Fin w} {j j' : Fin h} (hi : i = i') (hj : j.val + 1 = j'.val) :
    (q.tile i j).top = (q.tile i' j').bottom := by
  simpa only [hi, Fin.ext_iff, hj] using q.vertical i j (hj ▸ j'.isLt)

/-- A finite palette tiles the plane iff it tiles squares of every positive side length. -/
theorem tilesPlane_iff_squares (τ : List WangTile) :
    TilesPlane τ ↔ ∀ n, Nonempty (Rectangle τ (n + 1) (n + 1)) := by
  classical
  constructor
  · rintro ⟨f, hf⟩ n
    exact ⟨{
      tile := fun i j => f i.val j.val
      mem := fun i j => (hf i.val j.val).1
      horizontal := fun i j hi => by simpa using (hf i.val j.val).2.1
      vertical := fun i j hj => by simpa using (hf i.val j.val).2.2 }⟩
  · intro h
    obtain ⟨f, hf⟩ := exists_matching τ (fun p : ℤ × ℤ => (p.1 + 1, p.2))
      (fun p => (p.1, p.2 + 1)) (fun _ _ => True) (by
        intro s
        let N := s.sup fun p => max p.1.natAbs p.2.natAbs
        let q := (h (2 * N)).some
        have bounds (p : s) : -(N : ℤ) ≤ p.val.1 ∧ p.val.1 ≤ N ∧
            -(N : ℤ) ≤ p.val.2 ∧ p.val.2 ≤ N := by
          have := Finset.le_sup (f := fun q : ℤ × ℤ => max q.1.natAbs q.2.natAbs) p.property
          omega
        let ix (p : s) : Fin (2 * N + 1) :=
          ⟨(p.val.1 + N).toNat, by have := bounds p; omega⟩
        let iy (p : s) : Fin (2 * N + 1) :=
          ⟨(p.val.2 + N).toNat, by have := bounds p; omega⟩
        refine ⟨fun p => ⟨q.tile (ix p) (iy p), q.mem _ _⟩, fun _ => trivial, ?_, ?_⟩
        · intro p r hr
          have := bounds p; have := bounds r
          obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hr
          exact q.horizontal_eq (by dsimp only [ix]; omega) (Fin.ext (by dsimp only [iy]; omega))
        · intro p r hr
          have := bounds p; have := bounds r
          obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hr
          exact q.vertical_eq (Fin.ext (by dsimp only [ix]; omega)) (by dsimp only [iy]; omega))
    exact ⟨fun x y => f (x, y), fun x y => ⟨(hf _).1, (hf _).2.2⟩⟩

/-- A seeded palette tiles the quadrant iff it has seeded squares of every positive side. -/
theorem tilesQuadrant_iff_seededSquares (I : SeededInstance) :
    TilesQuadrant I ↔ ∀ n, Nonempty (SeededSquare I n) := by
  classical
  constructor
  · rintro ⟨f, hseed, hf⟩ n
    exact ⟨{
      tile := fun i j => f i.val j.val
      mem := fun i j => (hf i.val j.val).1
      horizontal := fun i j hi => (hf i.val j.val).2.1
      vertical := fun i j hj => (hf i.val j.val).2.2
      corner := hseed }⟩
  · intro h
    obtain ⟨f, hf⟩ := exists_matching I.tiles (fun p : ℕ × ℕ => (p.1 + 1, p.2))
      (fun p => (p.1, p.2 + 1)) (fun p t => p = (0, 0) → t = I.seed) (by
        intro s
        let N := s.sup fun p => max p.1 p.2
        let q := (h N).some
        let ix (p : s) : Fin (N + 1) :=
          ⟨p.val.1, Nat.lt_succ_of_le (Finset.le_sup_of_le p.property (Nat.le_max_left _ _))⟩
        let iy (p : s) : Fin (N + 1) :=
          ⟨p.val.2, Nat.lt_succ_of_le (Finset.le_sup_of_le p.property (Nat.le_max_right _ _))⟩
        refine ⟨fun p => ⟨q.tile (ix p) (iy p), q.mem _ _⟩, ?_,
          fun p r hr =>
            q.horizontal_eq (congrArg Prod.fst hr).symm (Fin.ext (congrArg Prod.snd hr).symm),
          fun p r hr =>
            q.vertical_eq (Fin.ext (congrArg Prod.fst hr).symm) (congrArg Prod.snd hr).symm⟩
        intro p hp
        simpa only [show ix p = 0 from Fin.ext (congrArg Prod.fst hp),
          show iy p = 0 from Fin.ext (congrArg Prod.snd hp)] using q.corner)
    exact ⟨fun x y => f (x, y), (hf _).2.1 rfl,
      fun x y => ⟨(hf _).1, (hf _).2.2⟩⟩

end Cslib.WangTile
