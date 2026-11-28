/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.TilesPlaneOfEveryTileOccurs

/-! # Tiling the plane and sublists in which every tile occurs: checked instances

Both sides of `tilesPlane_iff_exists_sublist_everyTileOccurs` on small lists, each side checked
without the theorem: lists on which both fail, a list that is its own witness, and a list whose
only witness is a proper sublist. -/

@[expose] public section

namespace Cslib.Tests.WangTileSublists

open Cslib Cslib.WangTile

/-- A tile that tiles the plane by itself. -/
def plain : WangTile := ⟨0, 0, 0, 0⟩

/-- A tile that matches neither itself nor `plain` on any side. -/
def useless : WangTile := ⟨1, 2, 3, 4⟩

/-- The empty list does not tile the plane, although each of its tiles is at the origin of a
tiling: this is why the sublist in the theorem must be non-empty. -/
example : ¬TilesPlane [] ∧ EveryTileOccurs [] :=
  ⟨fun ⟨f, hf⟩ => by simpa using (hf 0 0).1, by simp [EveryTileOccurs]⟩

/-- The empty list has no non-empty sublist. -/
example : ¬∃ σ : List WangTile, σ.Sublist [] ∧ σ ≠ [] ∧ EveryTileOccurs σ := by simp

/-- A list whose only tile does not match itself: it does not tile the plane, and its only
non-empty sublist, the list itself, is a no-instance of the other problem. -/
example : ¬TilesPlane [useless] ∧
    ¬∃ σ : List WangTile, σ.Sublist [useless] ∧ σ ≠ [] ∧ EveryTileOccurs σ := by
  have h : ¬TilesPlane [useless] := fun ⟨f, hf⟩ => by
    have h₀ := (hf 0 0).1
    have h₁ := (hf 1 0).1
    have := (hf 0 0).2.1
    simp_all [useless]
  refine ⟨h, ?_⟩
  rintro ⟨σ, hσ, hne, hocc⟩
  obtain rfl | rfl := List.sublist_singleton.mp hσ
  · exact hne rfl
  · obtain ⟨f, -, hf⟩ := hocc useless (by simp)
    exact h ⟨f, hf⟩

/-- A single tile that matches itself: the list tiles the plane and is its own witness. -/
example : TilesPlane [plain] ∧ [plain].Sublist [plain] ∧ [plain] ≠ [] ∧
    EveryTileOccurs [plain] :=
  ⟨⟨fun _ _ => plain, fun _ _ => ⟨by simp, rfl, rfl⟩⟩, .refl _, by simp,
    fun t ht => ⟨fun _ _ => t, rfl, fun _ _ => ⟨ht, by simp_all [plain]⟩⟩⟩

/-- A list that tiles the plane and has a tile that no tiling uses: the list is a no-instance of
the problem in which every tile must occur, and the witness is the proper sublist `[plain]`. -/
example : TilesPlane [plain, useless] ∧ ¬EveryTileOccurs [plain, useless] ∧
    [plain].Sublist [plain, useless] ∧ [plain] ≠ [] ∧ EveryTileOccurs [plain] := by
  refine ⟨⟨fun _ _ => plain, fun _ _ => ⟨by simp, rfl, rfl⟩⟩, fun h => ?_, by simp, by simp,
    fun t ht => ⟨fun _ _ => t, rfl, fun _ _ => ⟨ht, by simp_all [plain]⟩⟩⟩
  obtain ⟨f, h₀, hf⟩ := h useless (by simp)
  have h₁ := (hf 1 0).1
  have := (hf 0 0).2.1
  obtain h₁ | h₁ : f 1 0 = plain ∨ f 1 0 = useless := by simpa using h₁
  all_goals simp_all [plain, useless]

end Cslib.Tests.WangTileSublists
