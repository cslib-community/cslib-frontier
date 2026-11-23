/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
import CslibFrontier.Tactic.FinIndex
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
  have ep : f p = g s ⟨p, hp⟩ := heq ⟨p, by simp⟩
  have ee : f (east p) = g s ⟨east p, he⟩ := heq ⟨east p, by simp⟩
  have en : f (north p) = g s ⟨north p, hn⟩ := heq ⟨north p, by simp⟩
  dsimp only
  rw [ep, ee, en]
  exact ⟨(hg s).1 ⟨p, hp⟩, (hg s).2.1 ⟨p, hp⟩ ⟨east p, he⟩ rfl,
    (hg s).2.2 ⟨p, hp⟩ ⟨north p, hn⟩ rfl⟩

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
    have localPatch (s : Finset (ℤ × ℤ)) := h (2 * s.sup fun p => max p.1.natAbs p.2.natAbs)
    obtain ⟨f, hf⟩ := exists_matching τ (fun p : ℤ × ℤ => (p.1 + 1, p.2))
      (fun p => (p.1, p.2 + 1)) (fun _ _ => True) (by
        intro s
        let N := s.sup fun p => max p.1.natAbs p.2.natAbs
        let q := (localPatch s).some
        have bounds (p : s) : -(N : ℤ) ≤ p.val.1 ∧ p.val.1 ≤ N ∧
            -(N : ℤ) ≤ p.val.2 ∧ p.val.2 ≤ N := by
          have hx : p.val.1.natAbs ≤ N :=
            Finset.le_sup_of_le p.property (Nat.le_max_left _ _)
          have hy : p.val.2.natAbs ≤ N :=
            Finset.le_sup_of_le p.property (Nat.le_max_right _ _)
          omega
        let ix (p : s) : Fin (2 * N + 1) :=
          ⟨(p.val.1 + N).toNat, by have := bounds p; omega⟩
        let iy (p : s) : Fin (2 * N + 1) :=
          ⟨(p.val.2 + N).toNat, by have := bounds p; omega⟩
        refine ⟨fun p => ⟨q.tile (ix p) (iy p), q.mem _ _⟩, fun _ => trivial, ?_, ?_⟩
        · intro p r hr
          have hx : (ix p).val + 1 = (ix r).val := by
            have := bounds p
            have := bounds r
            have hfirst := congrArg Prod.fst hr
            have hsecond := congrArg Prod.snd hr
            dsimp only [ix]
            omega
          have hy : iy p = iy r := by
            have hsecond := congrArg Prod.snd hr
            fin_index [iy]
          simpa only [hy, Fin.ext_iff, hx] using
            q.horizontal (ix p) (iy p) (by omega : (ix p).val + 1 < 2 * N + 1)
        · intro p r hr
          have hx : ix p = ix r := by
            have hfirst := congrArg Prod.fst hr
            fin_index [ix]
          have hy : (iy p).val + 1 = (iy r).val := by
            have := bounds p
            have := bounds r
            have hfirst := congrArg Prod.fst hr
            have hsecond := congrArg Prod.snd hr
            dsimp only [iy]
            omega
          simpa only [hx, Fin.ext_iff, hy] using
            q.vertical (ix p) (iy p) (by omega : (iy p).val + 1 < 2 * N + 1))
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
        refine ⟨fun p => ⟨q.tile (ix p) (iy p), q.mem _ _⟩, ?_, ?_, ?_⟩
        · intro p hp
          have hx : ix p = 0 := Fin.ext (congrArg Prod.fst hp)
          have hy : iy p = 0 := Fin.ext (congrArg Prod.snd hp)
          simpa only [hx, hy] using q.corner
        · intro p r hr
          have hx : (ix p).val + 1 = (ix r).val := (congrArg Prod.fst hr).symm
          have hy : iy p = iy r := Fin.ext (congrArg Prod.snd hr).symm
          simpa only [hy, Fin.ext_iff, hx] using
            q.horizontal (ix p) (iy p) (by omega : (ix p).val + 1 < N + 1)
        · intro p r hr
          have hx : ix p = ix r := Fin.ext (congrArg Prod.fst hr).symm
          have hy : (iy p).val + 1 = (iy r).val := (congrArg Prod.snd hr).symm
          simpa only [hx, Fin.ext_iff, hy] using
            q.vertical (ix p) (iy p) (by omega : (iy p).val + 1 < N + 1))
    exact ⟨fun x y => f (x, y), (hf _).2.1 rfl,
      fun x y => ⟨(hf _).1, (hf _).2.2⟩⟩

end Cslib.WangTile
