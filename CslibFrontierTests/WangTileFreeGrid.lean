/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Forcing
public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Certificates
import CslibFrontier.Computability.WangTile.Robinson.Canonical.Patches
import CslibFrontier.Computability.WangTile.Robinson.FreeGrid.Obstruction

/-!
# Marked free grids and nontrivial Robinson routing

Clients check a nontrivial odd-base path and an absent port, then construct a two-by-two
routed grid from an actual canonical scaffold plane. A constant payload on that plane supplies
a satisfying input to `scaffold_forces`; incompatible edge colours and a seed outside the
palette exercise its use in refuting combined tilings.
-/

-- These are local regression examples, with no test-only public API.
set_option linter.privateModule false

namespace Cslib.Tests.WangTile.FreeGrid
open Cslib.WangTile Cslib.WangTile.Robinson

private abbrev oddGrid := iterateRefine 4 (fun _ _ => (0 : Index))

-- A covered live crossing connects to a different corner port, so its path is nontrivial.
example : ∃ (source : Port) (parity : Bool), source ≠ ⟨6, 6, .west⟩ ∧
    BoundedPath oddGrid 16 16 source ⟨6, 6, .west⟩ parity := by
  obtain ⟨source, parity, sourceMem, path⟩ := odd_base_exists_boundedPath
    (target := ⟨6, 6, .west⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)
  refine ⟨source, parity, ?_, path⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
  rcases sourceMem with rfl | rfl | rfl | rfl <;> decide

-- The coverage premise is substantive: a nearby port is absent.
example : portPresent oddGrid ⟨4, 4, .west⟩ = false := by decide +kernel

-- An actual canonical scaffold plane has a routed grid with two rows and columns.
example : ∃ P : Cslib.WangTile.Plane scaffold.tiles,
    Nonempty (Cslib.WangTile.RoutedGrid scaffold P 1) := by
  obtain ⟨P⟩ := (Cslib.WangTile.nonempty_plane_iff _).2 Canonical.scaffold_tilesPlane
  let D := DecodedPlane.ofPlane P
  let R := QuarterPlane.regroup D.quarterPlane
  obtain ⟨a, b, scale, cycle, shaded, ⟨grid⟩⟩ := exists_markedFreeGrid D R 1
  exact ⟨P, ⟨grid.routedGrid D R a b cycle shaded⟩⟩

private def payload : SeededInstance := ⟨[⟨0, 0, 0, 0⟩], ⟨0, 0, 0, 0⟩⟩

private theorem populated_combination : TilesPlane (combine scaffold payload) := by
  obtain ⟨f, matching⟩ := Canonical.scaffold_tilesPlane
  have allowed (base : WangTile) : payload.seed ∈ routedPayloads scaffold payload base := by
    apply mem_routedPayloads.mpr
    have complete : payload.seed ∈ completePayloads payload.tiles :=
      mem_completePayloads_of_mem List.mem_cons_self
    cases scaffold.role base
    · exact complete
    · exact ⟨complete, rfl⟩
    · exact ⟨complete, rfl⟩
    · exact List.mem_cons_self
    · exact ⟨List.mem_cons_self, rfl⟩
  refine ⟨fun x y => layer (f x y) payload.seed, ?_⟩
  intro x y
  refine ⟨mem_combine.mpr ⟨f x y, (matching x y).1, payload.seed, allowed _, rfl⟩, ?_, ?_⟩
  · change Nat.pair (f x y).right 0 = Nat.pair (f (x + 1) y).left 0
    rw [(matching x y).2.1]
  · change Nat.pair (f x y).top 0 = Nat.pair (f x (y + 1)).bottom 0
    rw [(matching x y).2.2]

-- The premise of the forcing theorem is satisfiable.
example : TilesPlane (combine scaffold payload) := populated_combination

-- Incompatible horizontal colours forbid a row of width two.
private def bad : SeededInstance := ⟨[⟨0, 0, 0, 1⟩], ⟨0, 0, 0, 1⟩⟩

example : ¬ TilesPlane (combine scaffold bad) := by
  intro h
  obtain ⟨sq⟩ := scaffold_forces bad h 1
  have hi : (0 : Fin 2).val + 1 < 1 + 1 := by decide
  have h0 := sq.mem 0 0
  have h1 := sq.mem ⟨(0 : Fin 2).val + 1, hi⟩ 0
  have hm := sq.horizontal 0 0 hi
  simp only [bad, List.mem_singleton] at h0 h1
  rw [h0, h1] at hm
  exact absurd hm (by decide)

-- A seed outside the palette is impossible even in a one-cell square.
private def outside : SeededInstance := ⟨[⟨0, 0, 0, 0⟩], ⟨1, 1, 1, 1⟩⟩

example : ¬ TilesPlane (combine scaffold outside) := by
  intro h
  obtain ⟨sq⟩ := scaffold_forces outside h 0
  have h0 := sq.mem 0 0
  rw [sq.corner] at h0
  simp [outside] at h0

end Cslib.Tests.WangTile.FreeGrid
