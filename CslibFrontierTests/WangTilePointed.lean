/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Pointed
public import CslibFrontierTests.WangTile

/-!
# Pointed-plane Wang tilings: checked instances

The pointed extension preserves both the halting and nonhalting machine cases through ordinary
module imports. An empty source palette cannot acquire a pointed tiling, and a mismatched tile
cannot acquire a two-by-two seeded patch. The finite test uses no infinite tiling hypothesis.
-/

-- This test module contains anonymous examples rather than an exported API.
set_option linter.privateModule false

namespace Cslib.Tests.WangTile

open Cslib.WangTile

example (input : List Bool) :
    TilesAtOrigin (pointedExtension (OfTM0.seededInstance moveM input)) :=
  (tilesAtOrigin_pointedExtension_iff _).mpr (tilesQuadrant_moveM input)

example (input : List Bool) :
    ¬ TilesAtOrigin (pointedExtension (OfTM0.seededInstance haltM input)) := by
  intro h
  exact not_tilesQuadrant_haltM input ((tilesAtOrigin_pointedExtension_iff _).mp h)

example : ¬ TilesAtOrigin (pointedExtension ⟨[], monochrome⟩) := by
  intro h
  obtain ⟨f, _, hf⟩ := (tilesAtOrigin_pointedExtension_iff _).mp h
  simpa using (hf 0 0).1

private def incompatible : SeededInstance := ⟨[⟨0, 0, 0, 1⟩], ⟨0, 0, 0, 1⟩⟩

example : ¬ Nonempty (SeededSquare (pointedExtension incompatible) 1) := by
  intro h
  obtain ⟨s⟩ := seededSquare_of_pointedExtension h
  have h₀ : s.tile 0 0 = ⟨0, 0, 0, 1⟩ := by simpa [incompatible] using s.mem 0 0
  have h₁ : s.tile 1 0 = ⟨0, 0, 0, 1⟩ := by simpa [incompatible] using s.mem 1 0
  have he := s.horizontal 0 0 (by decide)
  simp [h₀, h₁] at he

end Cslib.Tests.WangTile
