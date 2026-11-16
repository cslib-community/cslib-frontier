/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Forcing
public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.OddCoverage
import CslibFrontier.Computability.WangTile.Robinson.Canonical.Patches

/-!
# Marked free grids and nontrivial Robinson routing

Clients check a nontrivial odd-base path and an absent port, then construct a two-by-two
routed grid from an actual canonical scaffold plane. Every cell between its first two
crossings is a horizontal wire, so the extraction does not skip another crossing. A constant
payload on the canonical scaffold plane supplies a satisfying input to `scaffold_forces`.
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

-- The plane and grid hypotheses have a genuine instance with two distinct rows and columns.
example : ∃ (P : Cslib.WangTile.Plane scaffold.tiles)
    (G : Cslib.WangTile.RoutedGrid scaffold P 1),
    G.column 0 < G.column 1 ∧ G.row 0 < G.row 1 ∧
      scaffold.role (P.tile (G.column 0) (G.row 0)) = .corner ∧
      ∀ x, G.column 0 < x → x < G.column 1 →
        scaffold.role (P.tile x (G.row 0)) = .horizontal := by
  obtain ⟨P⟩ := (Cslib.WangTile.nonempty_plane_iff _).2 Canonical.scaffold_tilesPlane
  let D := DecodedPlane.ofPlane P
  let R := QuarterPlane.regroup D.quarterPlane
  obtain ⟨a, b, scale, cycle, shaded, ⟨grid⟩⟩ := FreeGrid.exists_markedGrid D R 1
  let G := grid.routedGrid D R a b cycle shaded
  exact ⟨P, G, G.column_strictMono (by decide), G.row_strictMono (by decide), G.corner,
    fun x hl hr => G.horizontal 0 0 x hl hr⟩

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

-- The actual combined plane yields a seeded square with two rows and two columns.
example : Nonempty (SeededSquare payload 1) :=
  scaffold_forces payload populated_combination 1

end Cslib.Tests.WangTile.FreeGrid
