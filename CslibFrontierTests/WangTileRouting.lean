/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Routing
import Mathlib.Tactic.FinCases

/-! Ordinary-module clients of routing: actual addressed squares, extraction from a constant
corner grid, and an absent-seed example separating realization from forcing. -/

-- These are local regression examples, with no test-only public API.
set_option linter.privateModule false

open Cslib Cslib.WangTile

private def zeroTile : WangTile := ⟨0, 0, 0, 0⟩

private def uniformScaffold (role : RouteRole) : RoutedScaffold where
  tiles := [zeroTile]
  role := fun _ => role

private def uniformPlane (role : RouteRole) : Plane (uniformScaffold role).tiles where
  tile := fun _ _ => zeroTile
  mem := fun _ _ => List.mem_cons_self
  horizontal := fun _ _ => rfl
  vertical := fun _ _ => rfl

private def activeAddressing (n : ℕ) : AddressedSquare (uniformScaffold .active) n where
  base := {
    tile := fun _ _ => zeroTile
    mem := fun _ _ => List.mem_cons_self
    horizontal := fun _ _ _ => rfl
    vertical := fun _ _ _ => rfl }
  point := fun i j => (i.val, j.val)
  horizontalSource := fun _ _ => (0, 0)
  verticalSource := fun _ _ => (0, 0)
  corner_zero := fun _ _ h => RouteRole.noConfusion h
  hstep := fun _ _ _ _ _ => by simp [uniformScaffold, RouteRole.horizontalOutgoing]
  vstep := fun _ _ _ _ _ => by simp [uniformScaffold, RouteRole.verticalOutgoing]

/-- Full crossing grids realize any pointed plane, without forcing its seed to occur. -/
example : Realizes (uniformScaffold .active) :=
  realizes_of_addressedSquares fun n => ⟨n, le_rfl, ⟨activeAddressing n⟩⟩

private def cornerGrid (n : ℕ) :
    RoutedGrid (uniformScaffold .corner) (uniformPlane .corner) n where
  column i := i.val
  row j := j.val
  column_strictMono := fun i j h => by
    change (i.val : ℤ) < j.val
    have : i.val < j.val := h
    omega
  row_strictMono := fun i j h => by
    change (i.val : ℤ) < j.val
    have : i.val < j.val := h
    omega
  crossing := fun _ _ => Or.inr rfl
  corner := rfl
  horizontal := fun _ _ _ h₁ h₂ => by simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂; omega
  vertical := fun _ _ _ h₁ h₂ => by simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂; omega

/-- At a seeded monochrome crossing every finite grid extracts a square with that seed. -/
example (n : ℕ) : Nonempty (SeededSquare ⟨[zeroTile], zeroTile⟩ n) := by
  let P : RoutedPlane (uniformScaffold .corner) ⟨[zeroTile], zeroTile⟩ := {
    base := uniformPlane .corner
    payload := fun _ _ => zeroTile
    allowed := fun _ _ => mem_routedPayloads.mpr ⟨List.mem_cons_self, rfl⟩
    horizontal := fun _ _ => rfl
    vertical := fun _ _ => rfl }
  exact ⟨(cornerGrid n).seededSquare P⟩

/-- Realization alone does not remove a seed: an active scaffold accepts a palette whose seed
is absent, so its forward forcing obligation fails. -/
example : ¬ Forces (uniformScaffold .active) := by
  intro forces
  let I : SeededInstance := ⟨[zeroTile], ⟨1, 1, 1, 1⟩⟩
  have combined : TilesPlane (combine (uniformScaffold .active) I) := by
    refine ⟨fun _ _ => layer zeroTile zeroTile, fun _ _ => ⟨?_, rfl, rfl⟩⟩
    exact mem_combine.mpr ⟨zeroTile, List.mem_cons_self, zeroTile,
      mem_routedPayloads.mpr List.mem_cons_self, rfl⟩
  obtain ⟨square⟩ := forces I combined 0
  have hm := square.mem 0 0
  rw [square.corner] at hm
  have he : I.seed = zeroTile := List.mem_singleton.mp hm
  have ht := congrArg WangTile.top he
  simp [I, zeroTile] at ht

private def wireTile (x y : ℤ) : WangTile :=
  ⟨((y + 1) % 2).toNat, (y % 2).toNat, (x % 2).toNat, ((x + 1) % 2).toNat⟩

private def wireScaffold : RoutedScaffold where
  tiles := [⟨1, 0, 0, 1⟩, ⟨1, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩, ⟨0, 1, 1, 0⟩]
  role t := if t.bottom = 0 then
    if t.left = 0 then .corner else .horizontal
    else if t.left = 0 then .vertical else .inactive

private def wirePlane : Plane wireScaffold.tiles where
  tile := wireTile
  mem x y := by
    simp only [wireScaffold, wireTile, List.mem_cons, WangTile.mk.injEq]
    omega
  horizontal := fun _ _ => rfl
  vertical := fun _ _ => rfl

private def spacedGrid (n : ℕ) : RoutedGrid wireScaffold wirePlane n where
  column i := 2 * (i.val : ℤ)
  row j := 2 * (j.val : ℤ)
  column_strictMono := fun i j h => by
    change 2 * (i.val : ℤ) < 2 * (j.val : ℤ)
    have : i.val < j.val := h
    omega
  row_strictMono := fun i j h => by
    change 2 * (i.val : ℤ) < 2 * (j.val : ℤ)
    have : i.val < j.val := h
    omega
  crossing := fun i j => Or.inr (by simp [wireScaffold, wirePlane, wireTile])
  corner := rfl
  horizontal i j x h₁ h₂ := by
    have hx : x = 2 * (i.val : ℤ) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega
    simp [wireScaffold, wirePlane, wireTile, hx, Int.add_emod]
  vertical i j y h₁ h₂ := by
    have hy : y = 2 * (j.val : ℤ) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega
    simp [wireScaffold, wirePlane, wireTile, hy, Int.add_emod]

private def wirePayload : RoutedPlane wireScaffold ⟨[⟨0, 0, 0, 0⟩], ⟨0, 0, 0, 0⟩⟩ where
  base := wirePlane
  payload := fun _ _ => ⟨0, 0, 0, 0⟩
  allowed x y := by
    apply mem_routedPayloads.mpr
    simp only [wireScaffold, wirePlane, wireTile]
    have complete : (⟨0, 0, 0, 0⟩ : WangTile) ∈ completePayloads [⟨0, 0, 0, 0⟩] :=
      mem_completePayloads_of_mem List.mem_cons_self
    split_ifs <;> simp_all
  horizontal := fun _ _ => rfl
  vertical := fun _ _ => rfl

/-- Every adjacent pair of crossings has an actual intervening wire in each axis. -/
example :
    (spacedGrid 1).column 0 < 1 ∧ 1 < (spacedGrid 1).column 1 ∧
    wireScaffold.role (wirePlane.tile 1 0) = .horizontal ∧
    (spacedGrid 1).row 0 < 1 ∧ 1 < (spacedGrid 1).row 1 ∧
    wireScaffold.role (wirePlane.tile 0 1) = .vertical := by decide +kernel

/-- Extraction crosses nonempty intervals of wires and retains the prescribed seed. -/
example (n : ℕ) : Nonempty (SeededSquare ⟨[⟨0, 0, 0, 0⟩], ⟨0, 0, 0, 0⟩⟩ n) :=
  ⟨(spacedGrid n).seededSquare wirePayload⟩

/-- The smallest wire patch contains one genuine corner and both outgoing carrier wires. -/
private def spacedAddressing : AddressedSquare wireScaffold 1 where
  base := {
    tile := fun i j => wireTile i.val j.val
    mem := by decide +kernel
    horizontal := by decide +kernel
    vertical := by decide +kernel }
  point := fun _ _ => (0, 0)
  horizontalSource := fun _ _ => (0, 0)
  verticalSource := fun _ _ => (0, 0)
  corner_zero := by decide +kernel
  hstep := by
    intro i j hi
    have hi0 : i = 0 := Fin.ext
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi)))
    subst i
    fin_cases j <;> simp [wireScaffold, wireTile,
      RouteRole.horizontalCarrier, RouteRole.horizontalOutgoing]
  vstep := by
    intro i j hj
    have hj0 : j = 0 := Fin.ext
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hj)))
    subst j
    fin_cases i <;> simp [wireScaffold, wireTile,
      RouteRole.verticalCarrier, RouteRole.verticalOutgoing]

/-- Corner placement and both address equations have actual carrier premises in this patch. -/
example :
    wireScaffold.role (spacedAddressing.base.tile 0 0) = .corner ∧
    wireScaffold.role (spacedAddressing.base.tile 1 0) = .horizontal ∧
    wireScaffold.role (spacedAddressing.base.tile 0 1) = .vertical ∧
    spacedAddressing.point 0 0 = (0, 0) := by
  exact ⟨rfl, rfl, rfl, spacedAddressing.corner_zero 0 0 rfl⟩

/-- Cropping constructs a smaller matching rectangle through ordinary dot notation. -/
example : Nonempty (Rectangle wireScaffold.tiles 1 1) :=
  ⟨spacedAddressing.base.crop (by decide) (by decide)⟩
