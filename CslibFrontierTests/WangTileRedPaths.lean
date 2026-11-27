/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Geometry

/-! Ordinary-module clients of quarter subdivision, parity paths and red shading. -/

-- This client contains private fixtures and anonymous examples, not an exported API.
set_option linter.privateModule false

open Cslib.WangTile.Robinson

/-- A tile with two straight red lanes crossing in its northeast quarter. -/
private def crossingGrid (_ _ : Nat) : Index := 13

/-- Light horizontal lanes and dark vertical lanes form a matching shade assignment. -/
private def crossingShades (x y : Nat) : ShadeState :=
  { west := if y % 2 == 1 then some .light else none
    east := if y % 2 == 1 then some .light else none
    south := if x % 2 == 1 then some .dark else none
    north := if x % 2 == 1 then some .dark else none }

private theorem crossing_valid : ValidShadeGrid crossingGrid crossingShades := by
  constructor
  · intro x y
    cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
      simp [crossingGrid, crossingShades, locallyAllowed, allowedFor, components,
        quadrantAt, Quadrant.ofBits, hasWest, hasEast, hasSouth, hasNorth,
        hasHorizontal, hasVertical, cornerWest, cornerEast, cornerSouth, cornerNorth,
        redHorizontalAt, redVerticalAt, containsLine, Quadrant.xBit, Quadrant.yBit, hx, hy]
  · intro x y; rfl
  · intro x y; rfl

/-- A crossing reverses shade even in an infinite matching grid. -/
example : Related true (some Shade.light) (some Shade.dark) := by
  have path : Path crossingGrid ⟨1, 1, .west⟩ ⟨1, 1, .south⟩ true :=
    .ofLink (.crossing 1 1 (by decide) (by decide))
  exact path.sound crossing_valid

/-- The same crossing remains an odd path after two substitutions. -/
example : Path (iterateRefine 2 crossingGrid)
    (refinedPort ⟨1, 1, .west⟩)
    (refinedPort ⟨1, 1, .south⟩) true := by
  apply Path.refine
  exact .ofLink (.crossing 1 1 (by decide) (by decide))

/-- Two crossings cancel their parity; every intermediate port remains in the box. -/
example : BoundedPath crossingGrid 2 2
    ⟨1, 1, .west⟩ ⟨1, 1, .west⟩ false := by
  have link : Link crossingGrid ⟨1, 1, .west⟩ ⟨1, 1, .south⟩ true :=
    .crossing 1 1 (by decide) (by decide)
  exact .trans (.ofLink link ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
    (.ofLink link.symm ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)

/-- Equal shades at an occupied crossing violate the local rule. -/
example : allowedFor .e .northeast ⟨some .light, some .light, some .light, some .light⟩ =
    false := by decide

/-- Combined signal certificates can decide actual shade states through ordinary imports. -/
example : (⟨some .light, none, none, none⟩ : ShadeState) ≠ ⟨some .dark, none, none, none⟩ := by
  decide

/-- Finite equality and ordinary quarter encoding are visible through ordinary imports. -/
example : (⟨1, 1, .west⟩ : Port) ≠ ⟨1, 1, .east⟩ := by decide

example : (subdivideTileAt ⟨1, 2, 3, 4⟩ .southwest).right =
    (subdivideTileAt ⟨1, 2, 3, 4⟩ .southeast).left := by rfl

/-- Exact macro-edge colours still distinguish incompatible neighboring quarters. -/
example : (subdivideTileAt ⟨1, 2, 3, 4⟩ .southeast).right ≠
    (subdivideTileAt ⟨1, 2, 5, 4⟩ .southwest).left := by decide

/-- The same oriented board survives arbitrarily many further substitutions. -/
example (n : Nat) : CycleOn
    (iterateRefine n (iterateRefine 2 (fun _ _ => 103)))
    (2 ^ n) (3 * 2 ^ n) (2 ^ n) (3 * 2 ^ n) := by
  simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using (fixed_cycle 103).iterateRefine n

/-- Complete local coverage reaches a concrete live macrocell exit. -/
example : ∃ source ∈ sources 13, ∃ parity,
    BoundedPath (fineGrid 13)
      8 8 source ⟨7, 1, .east⟩ parity :=
  exists_boundedPath 13 (by decide) (by decide)

/-- A live old east port connects evenly to its side-sensitive refined image. -/
example : Path (iterateRefine 2 crossingGrid)
    (sparsePort ⟨1, 1, .east⟩)
    (refinedPort ⟨1, 1, .east⟩) false :=
  livePortPath crossingGrid ⟨1, 1, .east⟩ (by decide)

/-! A light board with a nonempty interior, free row 2, and non-free column 3.
The fixture is adapted from reviewer-claude-shading's checked example; it asserts local
shade validity, without asserting that these indices tile as ordinary Robinson Wang tiles. -/

namespace Cslib.WangTile.Robinson.Tests

private def boardGrid (x y : Nat) : Index :=
  match x % 4, y % 4 with
  | 0, 0 => 0 | 3, 0 => 1 | 0, 3 => 2 | 3, 3 => 3
  | 1, 0 | 2, 0 => 22
  | 1, 3 | 2, 3 => 10
  | 0, 1 | 0, 2 => 14
  | 3, 1 | 3, 2 => 16
  | 1, 1 => 0 | 2, 1 => 1 | 1, 2 => 2 | 2, 2 => 3
  | _, _ => 0

private def lightShade : Option Shade := some .light

private def boardShades (x y : Nat) : ShadeState :=
  match x % 8, y % 8 with
  | 1, 1 => ⟨none, lightShade, none, lightShade⟩
  | 2, 1 | 3, 1 | 4, 1 | 5, 1 => ⟨lightShade, lightShade, none, none⟩
  | 6, 1 => ⟨lightShade, none, none, lightShade⟩
  | 1, 2 | 1, 3 | 1, 4 | 1, 5 => ⟨none, none, lightShade, lightShade⟩
  | 6, 2 | 6, 3 | 6, 4 | 6, 5 => ⟨none, none, lightShade, lightShade⟩
  | 1, 6 => ⟨none, lightShade, lightShade, none⟩
  | 2, 6 | 3, 6 | 4, 6 | 5, 6 => ⟨lightShade, lightShade, none, none⟩
  | 6, 6 => ⟨lightShade, none, lightShade, none⟩
  | 3, 3 => ⟨none, lightShade, none, lightShade⟩
  | 4, 3 => ⟨lightShade, none, none, lightShade⟩
  | 3, 4 => ⟨none, lightShade, lightShade, none⟩
  | 4, 4 => ⟨lightShade, none, lightShade, none⟩
  | _, _ => ⟨none, none, none, none⟩

private theorem boardGrid_mod (x y : Nat) : boardGrid x y = boardGrid (x % 4) (y % 4) := by
  simp [boardGrid]

private theorem boardShades_congr {a b a' b' : Nat} (ha : a % 8 = a' % 8) (hb : b % 8 = b' % 8) :
    boardShades a b = boardShades a' b' := by
  unfold boardShades; rw [ha, hb]

private theorem quadrantAt_mod (x y : Nat) : quadrantAt x y = quadrantAt (x % 8) (y % 8) := by
  have hx : x % 8 % 2 = x % 2 := by omega
  have hy : y % 8 % 2 = y % 2 := by omega
  simp [quadrantAt, hx, hy]

private theorem boardValid : ValidShadeGrid boardGrid boardShades where
  allowed x y := by
    have finite : ∀ x y : Fin 8,
        locallyAllowed
          ⟨boardGrid (x.val / 2) (y.val / 2), quadrantAt x.val y.val⟩
          (boardShades x.val y.val) = true := by
      decide
    have h := finite ⟨x % 8, Nat.mod_lt _ (by decide)⟩ ⟨y % 8, Nat.mod_lt _ (by decide)⟩
    have hx : (x % 8 / 2) % 4 = (x / 2) % 4 := by omega
    have hy : (y % 8 / 2) % 4 = (y / 2) % 4 := by omega
    rw [boardGrid_mod (x / 2), boardShades_congr (a' := x % 8) (b' := y % 8) (by omega) (by omega),
      quadrantAt_mod x, ← hx, ← hy, ← boardGrid_mod]
    exact h
  hmatch x y := by
    have finite : ∀ x y : Fin 8,
        (boardShades x.val y.val).east = (boardShades (x.val + 1) y.val).west := by decide
    have h := finite ⟨x % 8, Nat.mod_lt _ (by decide)⟩ ⟨y % 8, Nat.mod_lt _ (by decide)⟩
    rw [boardShades_congr (a := x) (a' := x % 8) (b := y) (b' := y % 8) (by omega) (by omega),
      boardShades_congr (a := x + 1) (a' := x % 8 + 1) (b := y) (b' := y % 8) (by omega) (by omega)]
    exact h
  vmatch x y := by
    have finite : ∀ x y : Fin 8,
        (boardShades x.val y.val).north = (boardShades x.val (y.val + 1)).south := by decide
    have h := finite ⟨x % 8, Nat.mod_lt _ (by decide)⟩ ⟨y % 8, Nat.mod_lt _ (by decide)⟩
    rw [boardShades_congr (a := x) (a' := x % 8) (b := y) (b' := y % 8) (by omega) (by omega),
      boardShades_congr (a := x) (a' := x % 8) (b := y + 1) (b' := y % 8 + 1) (by omega) (by omega)]
    exact h

private theorem boardCycle : CycleOn boardGrid 0 3 0 3 where
  west_lt_east := by decide
  south_lt_north := by decide
  southwest := by decide
  southeast := by decide
  northwest := by decide
  northeast := by decide
  southLane x h₁ h₂ := by
    have : x = 1 ∨ x = 2 := by omega
    rcases this with rfl | rfl <;> decide
  northLane x h₁ h₂ := by
    have : x = 1 ∨ x = 2 := by omega
    rcases this with rfl | rfl <;> decide
  westLane y h₁ h₂ := by
    have : y = 1 ∨ y = 2 := by omega
    rcases this with rfl | rfl <;> decide
  eastLane y h₁ h₂ := by
    have : y = 1 ∨ y = 2 := by omega
    rcases this with rfl | rfl <;> decide

private theorem boardLight : CycleShade boardShades 0 3 0 3 .light := by
  constructor <;> decide

private theorem freeRow : IsFreeRow boardGrid boardShades 0 3 2 := by
  intro x h₁ h₂
  have : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    simp only [quarterWest, quarterEast] at h₁ h₂; omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

private theorem notFreeColumn : ¬ IsFreeColumn boardGrid boardShades 0 3 3 := by
  intro h
  have := h 3 (by decide) (by decide)
  revert this
  decide

/-- The geometry theorem applied at an interior point: the alternatives it offers. -/
example :
    selectedHorizontalFor (componentAt boardGrid 3 2) (quadrantAt 3 2) (boardShades 3 2) ≠ none ∨
    (∃ boundary, 2 < boundary ∧ boundary < quarterNorth 3 ∧
      selectedHorizontalFor (componentAt boardGrid 3 boundary) (quadrantAt 3 boundary)
        (boardShades 3 boundary) = some .north ∧
      ∀ y, 2 < y → y < boundary →
        selectedHorizontalFor (componentAt boardGrid 3 y) (quadrantAt 3 y)
          (boardShades 3 y) = none) ∨
    (∃ boundary, quarterSouth 0 < boundary ∧ boundary < 2 ∧
      selectedHorizontalFor (componentAt boardGrid 3 boundary) (quadrantAt 3 boundary)
        (boardShades 3 boundary) = some .south ∧
      ∀ y, boundary < y → y < 2 →
        selectedHorizontalFor (componentAt boardGrid 3 y) (quadrantAt 3 y)
          (boardShades 3 y) = none) :=
  (boardLight.geometry boardCycle boardValid).verticalBoundary
    (by decide) (by decide) (by decide) (by decide) freeRow notFreeColumn

/-- The local alternative fails here; the inner board's south side at `y = 3`
is selected with its interior to the north. -/
example :
    selectedHorizontalFor (componentAt boardGrid 3 2) (quadrantAt 3 2) (boardShades 3 2) = none ∧
    selectedHorizontalFor (componentAt boardGrid 3 3) (quadrantAt 3 3) (boardShades 3 3) =
      some .north := by
  constructor <;> decide

/-- A wrongly oriented inner boundary is rejected by the local rules together with the outer
light cycle: flipping nothing but the claim, `some .south` at `y = 3` is false. -/
example : selectedHorizontalFor (componentAt boardGrid 3 3) (quadrantAt 3 3) (boardShades 3 3) ≠
    some .south := by decide

end Cslib.WangTile.Robinson.Tests
