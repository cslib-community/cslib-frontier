/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.EveryTileOccurs
public import Mathlib.Computability.RE
import CslibFrontier.Foundations.Computability.ComputablePred
import CslibFrontier.Foundations.Data.List.Primrec
import Mathlib.Data.List.Sublists

/-!
# Deciding the domino problem from the problem in which every tile must occur

Hirsch and Hodkinson say that the undecidability of their tiling problem, in which every tile
must lie at the origin of some tiling, follows from that of the domino problem, and give no
argument [HirschHodkinson2001], Section 3. The argument here is not taken from a source: a list
of tiles tiles the plane if and only if some non-empty sublist has each of its tiles at the
origin of a tiling by the sublist, namely the tiles that a tiling uses, and a list has finitely
many sublists. So a decision procedure for the source's problem gives one for the domino problem.
The procedure asks about every sublist; it is not a many-one reduction.

This file does not show that either problem is undecidable.

## Main results

* `Cslib.WangTile.tilesPlane_iff_exists_sublist_everyTileOccurs`: the characterization of the
  lists that tile the plane by their sublists.
* `Cslib.WangTile.computablePred_tilesPlane_of_computablePred_everyTileOccurs`: if the problem
  in which every tile must occur is decidable, so is the domino problem.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.WangTile

/-- A list of tiles tiles the plane if and only if some non-empty sublist of it has each of its
tiles at the origin of a tiling by the sublist. Given a tiling, the sublist consists of the tiles
that the tiling uses, and translating the tiling brings any of them to the origin. The sublist
must be non-empty: the empty list has every tile at the origin of a tiling and does not tile the
plane. -/
theorem tilesPlane_iff_exists_sublist_everyTileOccurs {τ : List WangTile} :
    TilesPlane τ ↔ ∃ σ, σ.Sublist τ ∧ σ ≠ [] ∧ EveryTileOccurs σ := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    have hmem (x y : ℤ) : f x y ∈ τ.filter fun t => ∃ x y, f x y = t :=
      List.mem_filter.mpr ⟨(hf x y).1, by simp⟩
    refine ⟨_, List.filter_sublist, List.ne_nil_of_mem (hmem 0 0), fun t ht => ?_⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, f a b = t := by simpa using (List.mem_filter.mp ht).2
    exact ⟨fun x y => f (a + x) (b + y), by simp, fun x y => ⟨hmem _ _,
      by simpa only [add_assoc] using (hf (a + x) (b + y)).2.1,
      by simpa only [add_assoc] using (hf (a + x) (b + y)).2.2⟩⟩
  · rintro ⟨σ, hσ, hne, h⟩
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil σ hne
    obtain ⟨f, -, hf⟩ := h t ht
    exact ⟨f, fun x y => ⟨hσ.subset (hf x y).1, (hf x y).2⟩⟩

/-- A decision procedure for the problem in which every tile must occur gives one for the domino
problem: a list tiles the plane if and only if one of its non-empty sublists is a yes-instance of
the former. This is the step from the domino problem to the tiling problem of
[HirschHodkinson2001], Section 3, which the source asserts without an argument; it does not say
that either problem is undecidable. -/
theorem computablePred_tilesPlane_of_computablePred_everyTileOccurs
    (h : ComputablePred EveryTileOccurs) : ComputablePred TilesPlane := by
  have hne : ComputablePred fun σ : List WangTile => σ ≠ [] :=
    (Primrec.eq.comp .id (.const [])).not.computablePred
  exact (ComputablePred.exists_mem_list (p := fun _ σ => σ ≠ [] ∧ EveryTileOccurs σ)
    ((hne.and h).comp Computable.snd) Primrec.list_sublists.to_comp).of_eq fun τ => by
      simp only [List.mem_sublists, tilesPlane_iff_exists_sublist_everyTileOccurs]

end Cslib.WangTile
