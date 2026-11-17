/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Realization

/-! Ordinary-module clients of canonical carrier geometry and pointed-payload realization.
The level-two patch contains an actual unblocked corner at quarter coordinate `(9, 9)`.
A two-colour payload whose seed occurs only at the origin exercises pointed-plane realization. -/

-- These regression examples intentionally add no public test API.
set_option linter.privateModule false

open Cslib Cslib.WangTile Cslib.WangTile.Robinson
open Cslib.WangTile.Robinson.Canonical Cslib.WangTile.Robinson.Carrier

example : (BorderState.seed.refine 2 3).Admissible :=
  BorderState.refine_admissible BorderState.seed_admissible 2 3

example (x y : Fin 2) :
    (BorderState.seed.refine 2 3).halo.row x.castSucc y.castSucc =
      (BorderState.seed.refine 2 3).node.rowInterior x y :=
  (BorderState.observations
    (BorderState.refine_admissible BorderState.seed_admissible 2 3) x y).1

example : rowInterior 2 seedNode 5 6 = some true := by
  rw [rowInterior_seed_eq_selectedBorder 2 5 6 (by decide) (by decide)]
  decide +kernel

example : rowInterior 2 seedNode 12 6 = some false := by
  rw [rowInterior_seed_eq_selectedBorder 2 12 6 (by decide) (by decide)]
  decide +kernel

example : rowInterior 2 seedNode 6 6 = none := by
  rw [rowInterior_seed_eq_selectedBorder 2 6 6 (by decide) (by decide)]
  decide +kernel

example : columnInterior 2 seedNode 6 5 = some true := by
  rw [columnInterior_seed_eq_selectedBorder 2 6 5 (by decide) (by decide)]
  decide +kernel

private theorem canonical_corner :
    scaffold.role ((canonicalAddressing 2).base.tile ⟨9, by decide⟩ ⟨9, by decide⟩) = .corner := by
  rw [canonicalAddressing_base_tile, scaffold_role, ShadedSite.routeRole_tile]
  decide +kernel

example : (canonicalAddressing 2).point ⟨9, by decide⟩ ⟨9, by decide⟩ = (0, 0) :=
  (canonicalAddressing 2).corner_zero _ _ canonical_corner

private def edge (x : ℤ) : ℕ := if x ≤ 0 then 2 else 3

private def cross (x y : ℤ) : WangTile :=
  ⟨edge (y + 1), edge y, edge x, edge (x + 1)⟩

private def palette : List WangTile :=
  [2, 3].flatMap fun t => [2, 3].flatMap fun b => [2, 3].flatMap fun l => [2, 3].map fun r =>
    ⟨t, b, l, r⟩

private theorem cross_mem (x y : ℤ) : cross x y ∈ palette := by
  have h (z : ℤ) : edge z = 2 ∨ edge z = 3 := by unfold edge; split <;> simp
  rcases h x with a | a <;> rcases h (x + 1) with b | b <;> rcases h y with c | c <;>
    rcases h (y + 1) with d | d <;> simp [cross, palette, a, b, c, d]

example (x y : ℤ) : cross x y = ⟨3, 2, 2, 3⟩ ↔ x = 0 ∧ y = 0 := by
  simp [cross, edge, WangTile.mk.injEq]
  omega

example : TilesPlane (combine scaffold ⟨palette, ⟨3, 2, 2, 3⟩⟩) := by
  apply scaffold_realizes
  exact ⟨cross, by simp [cross, edge], fun x y => ⟨cross_mem x y, rfl, rfl⟩⟩
