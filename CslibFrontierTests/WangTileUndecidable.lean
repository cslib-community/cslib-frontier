/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Undecidable
import CslibFrontier.Computability.WangTile.Robinson.Reduction

/-!
# Clients of domino undecidability and concrete seed removal

No computable Boolean function decides plane tileability. Concrete seed removal also sends a
monochrome seeded quadrant to a tileable plane palette and an empty seeded palette to a
nontileable plane palette. These are ordinary-module clients of the unconditional equivalence.
-/

-- Regression examples add no public test API.
set_option linter.privateModule false

open Cslib.WangTile Cslib.WangTile.Robinson

example (f : List Cslib.WangTile → Bool) (hf : Computable f) :
    ¬ ∀ τ, f τ = true ↔ TilesPlane τ := by
  intro decides
  apply not_computablePred_tilesPlane
  have hp : ComputablePred (fun τ => f τ = true) :=
    ⟨inferInstance, hf.of_eq fun _ => by simp⟩
  exact hp.of_eq decides

example : TilesPlane (removeSeed ⟨[⟨3, 3, 3, 3⟩], ⟨3, 3, 3, 3⟩⟩) := by
  apply (tilesPlane_removeSeed_iff _).mpr
  refine ⟨fun _ _ => ⟨3, 3, 3, 3⟩, rfl, ?_⟩
  intro x y
  exact ⟨by simp, rfl, rfl⟩

example : ¬ TilesPlane (removeSeed ⟨[], ⟨3, 3, 3, 3⟩⟩) := by
  intro h
  obtain ⟨f, _, hf⟩ := (tilesPlane_removeSeed_iff _).mp h
  simpa using (hf 0 0).1
