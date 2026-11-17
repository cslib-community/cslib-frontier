/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Hierarchy
public import CslibFrontier.Computability.WangTile.Robinson.Recognizability
import Mathlib.Data.Fin.VecNotation

/-! Ordinary-import clients of the corrected Robinson hierarchy. The concrete four-row patch
checks that the recognition hypotheses are satisfiable. A matching two-by-two patch with no
parent guards the essential one-cell context of that theorem. -/

namespace Cslib.Tests.WangTile.Robinson

open Cslib.WangTile
open Cslib.WangTile.Robinson

private def neighborhood : Neighborhood where
  cell i j := (![![6, 67, 7, 66], ![20, 40, 28, 40],
    ![4, 64, 5, 62], ![15, 3, 18, 89]] : Fin 4 → Fin 4 → Index) j i
  horizontal := by decide
  vertical := by decide
  phase := by decide

example : ∃! p : Index,
    childBlock p 0 0 = 40 ∧ childBlock p 1 0 = 28 ∧
      childBlock p 0 1 = 64 ∧ childBlock p 1 1 = 5 :=
  existsUnique_centerParent neighborhood

example : childBlock 16 0 0 = 40 ∧ childBlock 16 1 0 = 28 ∧
    childBlock 16 0 1 = 64 ∧ childBlock 16 1 1 = 5 := by decide

-- These four tiles match, but their isolated block has no substitution parent.
example : (components 33).thin = .a ∧
    (tile (components 33)).right = (tile (components 14)).left ∧
    (tile (components 77)).right = (tile (components 6)).left ∧
    (tile (components 33)).top = (tile (components 77)).bottom ∧
    (tile (components 14)).top = (tile (components 6)).bottom := by decide

example : ¬ ∃ p : Index,
    childBlock p 0 0 = 33 ∧ childBlock p 1 0 = 14 ∧
      childBlock p 0 1 = 77 ∧ childBlock p 1 1 = 6 := by decide

/-- Recurrence applies to a given tiling, preserving its actual tiles pointwise. -/
public theorem tile103_occurs_in_given_tiling {f : ℤ → ℤ → Cslib.WangTile}
    (hf : ∀ x y, f x y ∈ tileSet ∧ (f x y).right = (f (x + 1) y).left ∧
      (f x y).top = (f x (y + 1)).bottom) :
    ∃ x y, f x y = tile (components 103) := by
  obtain ⟨p, hp⟩ := exists_plane_eq hf
  obtain ⟨x, y, hxy⟩ := (tower p).every_tile 0 103
  rw [(tower p).zero] at hxy
  exact ⟨x, y, by rw [← hp, hxy]⟩

-- The tower and recurrence apply to a concrete nonempty family of planes.
example : ∃ p : IndexPlane, ∃ x y : ℤ, p.index x y = 103 := by
  obtain ⟨f, hf⟩ := tilesPlane_tileSet
  obtain ⟨p, _⟩ := exists_plane_eq hf
  have h := (tower p).every_tile 0 103
  exact ⟨p, by simpa only [(tower p).zero] using h⟩

end Cslib.Tests.WangTile.Robinson
