/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Frame
public import CslibFrontier.Computability.WangTile.EveryTileOccurs
public import CslibFrontier.Foundations.RelationAlgebra.Game

/-!
# A winning strategy gives tilings

Theorem 3 of [HirschHodkinson2001]: if ∃ has a winning strategy in the game of `RA(τ)`, then every
tile of `τ` is at the origin of a tiling of the plane by `τ`.

A winning strategy gives a saturated network with an edge labelled by any chosen tile atom, from
a `1`-node `a₀` to a `2`-node `b₀`. Saturation provides a `0`-node `c` joined to both by green
edges, and then `1`-nodes `aₓ` and `2`-nodes `b_y` for all integers `x`, `y`, each joined to `c`
by a green edge and to the next by a step. By rule 1 the edge from `aₓ` to `b_y` is labelled by a
tile atom, and by rule 2 and its dual these tiles match. The nodes `aₓ` need not be distinct.

The source's hypothesis that `T₀` is a special tile is not used.

## Main results

* `Cslib.RelationAlgebra.everyIndexOccurs_of_hasWinningStrategy`: Theorem 3.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra

open WangTile Tiling Tiling.Atom

variable {L : List WangTile}

/-- A relation in which every element has a successor and a predecessor contains a chain indexed
by the integers through any given element. -/
private theorem exists_int_chain {S : Type*} {R : S → S → Prop} (hsucc : ∀ s, ∃ s', R s s')
    (hpred : ∀ s, ∃ s', R s' s) (s₀ : S) : ∃ f : ℤ → S, f 0 = s₀ ∧ ∀ x, R (f x) (f (x + 1)) := by
  choose succ hsucc using hsucc
  choose pred hpred using hpred
  refine ⟨fun x => x.inductionOn' 0 s₀ (fun _ _ => succ) fun _ _ => pred, Int.inductionOn'_self,
    fun x => ?_⟩
  beta_reduce
  obtain hx | hx := le_or_gt 0 x
  · rw [Int.inductionOn'_add_one hx]
    exact hsucc _
  · have := Int.inductionOn'_sub_one (zero := s₀) (succ := fun _ _ => succ)
      (pred := fun _ _ => pred) (show x + 1 ≤ 0 by omega)
    rw [add_sub_cancel_right] at this
    rw [this]
    exact hpred _

/-- ∀ may ask for green edges to a new `0`-node on any tile edge. -/
private theorem cycle_green_green_tile (i : Fin L.length) :
    Cycle L (green .one .reverse) (green .two .forward) (tile i .forward) :=
  ⟨rfl, rfl, rfl, nofun, nofun, nofun, by simp [Forbidden, Rule, conv, Direction.flip]⟩

/-- ∀ may ask for a step in either direction from a node with a green edge. -/
private theorem cycle_step_green_green (d : Axis) (o : Direction) :
    Cycle L (step d o) (green d .reverse) (green d .reverse) :=
  ⟨rfl, rfl, rfl, nofun, nofun, nofun, by
    cases d <;> cases o <;> simp [Forbidden, Rule, conv, Direction.flip]⟩

/-- **Theorem 3 of [HirschHodkinson2001]**: if ∃ has a winning strategy in the game on the frame
of `RA(τ)`, then every position of the list of tiles is at the origin of a tiling of the plane by
positions of the list. -/
theorem everyIndexOccurs_of_hasWinningStrategy (h : (tilingFrame L).HasWinningStrategy) :
    EveryIndexOccurs L := by
  intro i
  obtain ⟨D, N, hN, a₀, b₀, hab⟩ := h.exists_saturated (tile i .forward)
  obtain ⟨c, ha₀, hb₀⟩ := hN (m := a₀) (n := b₀) (hab ▸ cycle_green_green_tile i)
  -- the nodes of kind `d` with a green edge to `c`, joined by steps in a chain through any of them
  have chain (d : Axis) (s₀ : D) (hs₀ : N s₀ c = green d .reverse) : ∃ f : ℤ → D, f 0 = s₀ ∧
      ∀ x, N (f x) c = green d .reverse ∧ N (f x) (f (x + 1)) = step d .forward := by
    have next (o : Direction) (s : {s // N s c = green d .reverse}) :
        ∃ s' : {s // N s c = green d .reverse}, N s s' = step d o := by
      obtain ⟨p, hp, hpc⟩ := hN (m := s.1) (n := c) (a := step d o) (b := green d .reverse)
        (by rw [s.2]; exact cycle_step_green_green d o)
      exact ⟨⟨p, hpc⟩, hp⟩
    obtain ⟨f, hf, hstep⟩ := exists_int_chain (R := fun s s' => N s.1 s'.1 = step d .forward)
      (next .forward) (fun s => (next .reverse s).imp fun s' hs' => by
        rw [← N.conv_label, hs']; rfl) ⟨s₀, hs₀⟩
    exact ⟨fun x => (f x).1, congrArg Subtype.val hf, fun x => ⟨(f x).2, hstep x⟩⟩
  obtain ⟨a, rfl, ha⟩ := chain .one a₀ ha₀
  obtain ⟨b, rfl, hb⟩ := chain .two b₀ (by rw [← N.conv_label, hb₀]; rfl)
  have hcb (y : ℤ) : N c (b y) = green .two .forward := by rw [← N.conv_label, (hb y).1]; rfl
  -- the tiles on the edges from the `a x` to the `b y`
  choose F hF using fun x y => Cycle.exists_eq_tile
    (show Cycle L _ _ (N (a x) (b y)) from (ha x).1 ▸ hcb y ▸ N.label_mem_cycles (a x) c (b y))
  have hF' (x y : ℤ) : N (b y) (a x) = tile (F x y) .reverse := by rw [← N.conv_label, hF]; rfl
  refine ⟨F, by simpa [hF] using hab, fun x y => ⟨?_, ?_⟩⟩
  · have hc : Cycle L _ _ _ := N.label_mem_cycles (a (x + 1)) (b y) (a x)
    rw [hF, hF', ← N.conv_label (a x), (ha x).2] at hc
    exact (not_not.mp fun hne => hc.not_forbidden (.inl hne)).symm
  · have hc : Cycle L _ _ _ := N.label_mem_cycles (b (y + 1)) (a x) (b y)
    rw [hF, hF', ← N.conv_label (b y), (hb y).2] at hc
    exact (not_not.mp fun hne => hc.not_forbidden (.inl hne)).symm

end Cslib.RelationAlgebra
