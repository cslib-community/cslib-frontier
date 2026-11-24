/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Compactness
public import CslibFrontier.Computability.WangTile.SeededUndecidable
import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Restrict

/-!
# Wang tilings: checked instances

Empty palettes, a monochrome tile, incompatible horizontal edges, and an absent seed exercise
the matching predicates through ordinary module imports. A machine that halts immediately and
one that moves right forever exercise both sides of the TM0 equivalence.
-/

namespace Cslib.Tests.WangTile

open Cslib.WangTile

-- Ordinary imports expose the documented tuple coding of both records.
example (t : WangTile) :
    Encodable.encode t = Encodable.encode (t.top, t.bottom, t.left, t.right) := rfl

example (I : SeededInstance) : Encodable.encode I = Encodable.encode (I.tiles, I.seed) := rfl

example : (⟨0, 0, 0, 0⟩ : WangTile) ∈ [⟨1, 2, 3, 4⟩, ⟨0, 0, 0, 0⟩] ∧
    (⟨0, 0, 0, 0⟩ : WangTile) ≠ ⟨1, 2, 3, 4⟩ := by decide

example : ¬ TilesPlane [] := by
  rintro ⟨f, hf⟩
  simpa using (hf 0 0).1

/-- The tile with colour zero on every edge. -/
@[expose] public def monochrome : WangTile := ⟨0, 0, 0, 0⟩

/-- A single monochrome tile covers the plane. -/
public theorem monochrome_tiles : TilesPlane [monochrome] :=
  ⟨fun _ _ => monochrome, by simp [monochrome]⟩

example : ∀ n, Nonempty (Rectangle [monochrome] (n + 1) (n + 1)) :=
  (tilesPlane_iff_squares [monochrome]).mp monochrome_tiles

private def mismatch : WangTile := ⟨0, 0, 0, 1⟩

example : ¬ TilesPlane [mismatch] := by
  rintro ⟨f, hf⟩
  have h₀ : f 0 0 = mismatch := by simpa using (hf 0 0).1
  have h₁ : f 1 0 = mismatch := by simpa using (hf 1 0).1
  have he := (hf 0 0).2.1
  simp [h₀, h₁, mismatch] at he

example : ¬ TilesQuadrant ⟨[monochrome], mismatch⟩ := by
  rintro ⟨f, hseed, hf⟩
  have hm := (hf 0 0).1
  rw [hseed] at hm
  simp [monochrome, mismatch] at hm

example : TilesQuadrant ⟨[monochrome], monochrome⟩ := by
  apply (tilesQuadrant_iff_seededSquares _).mpr
  intro n
  exact ⟨{
    tile := fun _ _ => monochrome
    mem := by simp
    horizontal := by simp [monochrome]
    vertical := by simp [monochrome]
    corner := rfl }⟩

/-! The source machines use a binary alphabet and a single state. -/

/-- A machine with no enabled transition. -/
@[expose] public def haltM : Turing.TM0.Machine Bool Unit := fun _ _ => none

/-- A machine that moves right forever, including beyond the end of its finite input. -/
@[expose] public def moveM : Turing.TM0.Machine Bool Unit := fun _ _ => some ((), .move .right)

/-- Immediate halting prevents the associated seeded quadrant from being tiled. -/
public theorem not_tilesQuadrant_haltM (input : List Bool) :
    ¬ TilesQuadrant (OfTM0.seededInstance haltM input) := by
  intro h
  apply (OfTM0.tilesQuadrant_seededInstance_iff haltM input).mp h
  apply (Turing.TM0.eval_dom_iff haltM input).mpr
  exact ⟨_, Relation.ReflTransGen.refl, rfl⟩

/-- An infinite right-moving run gives a tiling of the associated seeded quadrant. -/
public theorem tilesQuadrant_moveM (input : List Bool) :
    TilesQuadrant (OfTM0.seededInstance moveM input) := by
  apply (OfTM0.tilesQuadrant_seededInstance_iff moveM input).mpr
  intro h
  obtain ⟨cfg, _, hc⟩ := (Turing.TM0.eval_dom_iff moveM input).mp h
  obtain ⟨q, x, L, R, rfl⟩ := Turing.TM0.exists_cfgOf cfg
  rw [Turing.TM0.step_of_eq_right (M := moveM) (q := q) (a := x) (q' := ()) rfl L R] at hc
  cases hc

/-- Starting on `true`, this machine halts after moving left onto the blank half of the tape.
Clamping the move at the origin would instead leave it rewriting `true` forever. -/
private def crossM : Turing.TM0.Machine Bool (Fin 2) := fun q a =>
  if q = 0 then some (1, .move .left) else if a then some (1, .write true) else none

example : ¬ TilesQuadrant (OfTM0.seededInstance crossM [true]) := by
  intro h
  apply (OfTM0.tilesQuadrant_seededInstance_iff crossM [true]).mp h
  apply (Turing.TM0.eval_dom_iff crossM [true]).mpr
  refine ⟨Turing.TM0.cfgOf 1 false [] [true], Relation.ReflTransGen.single ?_, rfl⟩
  change Turing.TM0.step crossM (Turing.TM0.cfgOf 0 true [] []) =
    some (Turing.TM0.cfgOf 1 false [] [true])
  exact Turing.TM0.step_of_eq_left (M := crossM) (q := 0) (a := true) (q' := 1) rfl [] []

end Cslib.Tests.WangTile
