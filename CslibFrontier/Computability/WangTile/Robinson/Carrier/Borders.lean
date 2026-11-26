/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Canonical.Patches
public import CslibFrontier.Computability.WangTile.Robinson.Carrier.BorderCertificates
import CslibFrontier.Tactic.FinIndex
import Mathlib.Data.Nat.Periodic

/-!
# Recursive owners and selected borders of canonical Robinson patches

Each coordinate belongs to its smallest enclosing positive-depth frame. The selected border
at a quarter is the persistent outer opening or a boundary of one of the frames present at
that substitution level. The checked finite halo invariant identifies this arithmetic union
with the selected shade boundaries of the actual decorated substitution.

## Main definitions

* `depthAt`: the smallest positive frame depth containing a coordinate.
* `selectedBorder`: the bounded union of the outer opening and frame boundaries.

## Main results

* `selectedBorder_eq_some_iff`: exact characterization by frame boundaries.
* `rowInterior_seed_eq_selectedBorder`, `columnInterior_seed_eq_selectedBorder`: the canonical
  selected shade borders agree with the arithmetic hierarchy.
* `supertileIndexGrid_zero_cases`: the three ways a canonical child carries index zero.

## References

After [JeandelVanier2020], §3.3, pp. 26–29. The recursive owner and halo
argument is ported from lean-wang revision
`64268a3aaaef3eac65559352ef94f62ab9c00482`, `ShadedCarrierHierarchy` (lines 24–193),
`ShadedCarrierBorderGeometry`, and `ShadedCarrierBorderHierarchy`. The arithmetic closely
follows the source; the halo bridge is restructured around the named `BorderState` invariant.
-/

public section

namespace Cslib.WangTile.Robinson.Canonical

/-- The persistent outer opening occurs precisely at coordinate one with positive transverse
coordinate, and points toward increasing coordinates. -/
theorem outerBorder_eq_some_iff (coordinate transverse : ℕ) (orientation : Bool) :
    outerBorder coordinate transverse = some orientation ↔
      coordinate = 1 ∧ 1 ≤ transverse ∧ orientation = true := by
  unfold outerBorder
  split_ifs <;> simp_all [eq_comm]

end Cslib.WangTile.Robinson.Canonical

namespace Cslib.WangTile.Robinson.Carrier

open Canonical

/-- Linear scale of a depth-`depth` frame, growing by four at each level. -/
@[expose] def scale (depth : ℕ) : ℕ := 4 ^ depth

/-- Period of the depth-`depth` frames along either coordinate axis. -/
@[expose] def period (depth : ℕ) : ℕ := 4 ^ (depth + 1)

/-- Opening boundary residue of a frame, one unit beyond its scale. -/
@[expose] def frameStartResidue (depth : ℕ) : ℕ := scale depth + 1

/-- Closing boundary residue of a frame, three times its scale. -/
@[expose] def frameEndResidue (depth : ℕ) : ℕ := 3 * scale depth

/-- Whether a coordinate belongs to the closed interval of a depth-`depth` frame. -/
@[expose] def inFrame (depth coordinate : ℕ) : Bool :=
  frameStartResidue depth ≤ coordinate % period depth &&
    coordinate % period depth ≤ frameEndResidue depth

/-- Whether a coordinate is an opening or closing boundary at the given depth. -/
@[expose] def onFrameBoundary (depth coordinate : ℕ) : Bool :=
  coordinate % period depth = frameStartResidue depth ||
    coordinate % period depth = frameEndResidue depth

/-- Membership in a frame is the pair of bounds on the coordinate's period residue. -/
theorem inFrame_eq_true_iff (depth coordinate : ℕ) :
    inFrame depth coordinate = true ↔
      frameStartResidue depth ≤ coordinate % period depth ∧
        coordinate % period depth ≤ frameEndResidue depth := by
  simp [inFrame]

/-- An interior coordinate has neither boundary residue. -/
theorem onFrameBoundary_eq_false_iff (depth coordinate : ℕ) :
    onFrameBoundary depth coordinate = false ↔
      coordinate % period depth ≠ frameStartResidue depth ∧
        coordinate % period depth ≠ frameEndResidue depth := by
  simp [onFrameBoundary]

/-- Smallest frame depth at most `bound` containing a coordinate. -/
@[expose] def depthAt : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | bound + 1, coordinate =>
      match depthAt bound coordinate with
      | some depth => some depth
      | none => if inFrame (bound + 1) coordinate then some (bound + 1)
          else none

/-- A search with no positive depths has no owner. -/
@[simp] theorem depthAt_zero (coordinate : ℕ) :
    depthAt 0 coordinate = none := by
  rfl

/-- `depthAt` is a bounded `List.find?`. -/
private theorem depthAt_eq_find? (bound coordinate : ℕ) :
    depthAt bound coordinate = (List.range' 1 bound).find? (inFrame · coordinate) := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
    rw [depthAt, ih, List.range'_1_concat, List.find?_append]
    cases (List.range' 1 bound).find? (inFrame · coordinate) <;> simp [Nat.add_comm]

private theorem depthAt_eq_some_iff {bound coordinate depth : ℕ} :
    depthAt bound coordinate = some depth ↔
      (0 < depth ∧ depth ≤ bound) ∧ inFrame depth coordinate = true ∧
        ∀ smaller, 0 < smaller → smaller < depth → inFrame smaller coordinate = false := by
  rw [depthAt_eq_find?, List.find?_range'_eq_some, List.mem_range'_1]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  exact ⟨fun ⟨inside, range, least⟩ => ⟨by omega, inside, least⟩,
    fun ⟨range, inside, least⟩ => ⟨inside, by omega, least⟩⟩

private theorem depthAt_eq_none_iff {bound coordinate : ℕ} :
    depthAt bound coordinate = none ↔
      ∀ depth, 0 < depth → depth ≤ bound → inFrame depth coordinate = false := by
  simp only [depthAt_eq_find?, List.find?_range'_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true]
  grind

/-- Once a coordinate acquires an owner, increasing the search bound preserves it. -/
theorem depthAt_eq_some_mono {small bound coordinate depth : ℕ}
    (owner : depthAt small coordinate = some depth) (hsmall : small ≤ bound) :
    depthAt bound coordinate = some depth := by
  rw [depthAt_eq_some_iff] at owner ⊢
  exact ⟨⟨owner.1.1, owner.1.2.trans hsmall⟩, owner.2⟩

/-- Every owner depth lies inside the bound searched by `depthAt`. -/
theorem depthAt_le {bound coordinate depth : ℕ}
    (owner : depthAt bound coordinate = some depth) : depth ≤ bound :=
  (depthAt_eq_some_iff.mp owner).1.2

/-- `depthAt` never returns the unsearched depth zero. -/
theorem depthAt_pos {bound coordinate depth : ℕ}
    (owner : depthAt bound coordinate = some depth) : 0 < depth :=
  (depthAt_eq_some_iff.mp owner).1.1

/-- An owner is a frame that actually contains the coordinate. -/
theorem inFrame_eq_true_of_depthAt_eq_some {bound coordinate depth : ℕ}
    (owner : depthAt bound coordinate = some depth) : inFrame depth coordinate = true :=
  (depthAt_eq_some_iff.mp owner).2.1

/-- If no owner was found, none of the searched positive-depth frames contains the coordinate. -/
theorem inFrame_eq_false_of_depthAt_eq_none {bound coordinate depth : ℕ}
    (owner : depthAt bound coordinate = none) (hpositive : 0 < depth) (hbound : depth ≤ bound) :
    inFrame depth coordinate = false :=
  depthAt_eq_none_iff.mp owner depth hpositive hbound

/-- The returned owner is the smallest positive frame containing the coordinate. -/
theorem depthAt_le_of_inFrame {bound coordinate ownerDepth depth : ℕ}
    (owner : depthAt bound coordinate = some ownerDepth) (hpositive : 0 < depth)
    (contained : inFrame depth coordinate = true) : ownerDepth ≤ depth := by
  by_contra larger
  have outside := (depthAt_eq_some_iff.mp owner).2.2 depth hpositive (by omega)
  simp [contained] at outside

/-- Restricting the search to the returned depth still finds the same owner. -/
theorem depthAt_self_of_depthAt_eq_some {bound coordinate depth : ℕ}
    (owner : depthAt bound coordinate = some depth) : depthAt depth coordinate = some depth := by
  rw [depthAt_eq_some_iff] at owner ⊢
  exact ⟨⟨owner.1.1, le_rfl⟩, owner.2⟩

/-- Every frame has positive scale. -/
theorem scale_pos (depth : ℕ) : 0 < scale depth := by
  simp [scale]

/-- A frame period consists of four scale units. -/
theorem period_eq_four_mul_scale (depth : ℕ) :
    period depth = 4 * scale depth := by
  simp [period, scale, pow_succ, Nat.mul_comm]

/-- Every frame period exceeds one. -/
theorem one_lt_period (depth : ℕ) : 1 < period depth := by
  rw [period_eq_four_mul_scale]
  have := scale_pos depth
  omega

/-- The closing boundary lies strictly inside one period. -/
theorem frameEndResidue_lt_period (depth : ℕ) :
    frameEndResidue depth < period depth := by
  rw [frameEndResidue, period_eq_four_mul_scale]
  have positive := scale_pos depth
  omega

/-- The border contributed by one frame depth: `true` is the opening toward increasing
coordinates, `false` the closing toward decreasing coordinates. -/
@[expose] def frameBorder (depth coordinate transverse : ℕ) : Option Bool :=
  if inFrame depth transverse then
    if coordinate % period depth = frameStartResidue depth then some true
    else if coordinate % period depth = frameEndResidue depth then some false
    else none
  else none

/-- All selected borders in a canonical level supertile, as a direct bounded
search through its frame depths. -/
@[expose] def selectedBorder (level coordinate transverse : ℕ) : Option Bool :=
  Fin.findSome? fun (index : Fin (level + 1)) =>
    if index.val = 0 then outerBorder coordinate transverse
    else frameBorder index.val coordinate transverse

private theorem ceilDivFour_add_four_mul (coordinate multiple : ℕ) :
    ceilDivFour (coordinate + 4 * multiple) =
      ceilDivFour coordinate + multiple := by
  unfold ceilDivFour
  have h : coordinate + 4 * multiple + 3 = (coordinate + 3) + 4 * multiple := by omega
  rw [h, Nat.add_mul_div_left (coordinate + 3) multiple (y := 4) (by decide)]

/-- Rounding an opening boundary up recovers its positive coarse coordinate. -/
theorem ceilDivFour_four_mul_sub_three (n : ℕ) (positive : 0 < n) :
    ceilDivFour (4 * n - 3) = n := by
  unfold ceilDivFour
  omega

/-- Two substitutions multiply every frame period by four. -/
theorem period_succ (depth : ℕ) :
    period (depth + 1) = 4 * period depth := by
  simp [period, pow_succ, Nat.mul_comm]

private theorem frameStartResidue_succ (depth : ℕ) :
    frameStartResidue (depth + 1) = 4 * frameStartResidue depth - 3 := by
  simp only [frameStartResidue, scale, pow_succ]
  have positive : 0 < 4 ^ depth := scale_pos depth
  omega

private theorem frameEndResidue_succ (depth : ℕ) :
    frameEndResidue (depth + 1) = 4 * frameEndResidue depth := by
  simp [frameEndResidue, scale, pow_succ, Nat.mul_comm, Nat.mul_left_comm]

private inductive FrameSide where
  | opening
  | closing

private def FrameSide.boundaryResidue : FrameSide → ℕ → ℕ
  | .opening => frameStartResidue
  | .closing => frameEndResidue

private def FrameSide.fineResidue : FrameSide → ℕ
  | .opening => 1
  | .closing => 0

private theorem FrameSide.boundaryResidue_pos
    (side : FrameSide) (depth : ℕ) :
    0 < side.boundaryResidue depth := by
  cases side <;> simp [boundaryResidue, frameStartResidue,
    frameEndResidue, scale, pow_pos]

private theorem FrameSide.boundaryResidue_lt_period
    (side : FrameSide) (depth : ℕ) :
    side.boundaryResidue depth < period depth := by
  have positive : 0 < scale depth := scale_pos depth
  rw [period_eq_four_mul_scale]
  cases side <;> simp only [boundaryResidue, frameStartResidue,
    frameEndResidue] <;> omega

private theorem FrameSide.ceilDivFour_boundaryResidue_succ
    (side : FrameSide) (depth : ℕ) :
    ceilDivFour (side.boundaryResidue (depth + 1)) =
      side.boundaryResidue depth := by
  cases side <;>
    simp only [boundaryResidue, frameStartResidue, frameEndResidue,
      scale, pow_succ] <;>
    unfold ceilDivFour <;> omega

private theorem inFrame_ceilDivFour_periodic (depth : ℕ) :
    Function.Periodic (fun coordinate =>
      inFrame depth (ceilDivFour coordinate)) (period (depth + 1)) := by
  intro coordinate
  simp [inFrame, period_succ, ceilDivFour_add_four_mul]

private theorem inFrame_periodic (depth : ℕ) :
    Function.Periodic (inFrame depth) (period depth) := by
  intro coordinate
  simp [inFrame]

/-- A coordinate belongs to a refined frame exactly when its rounded coarse coordinate does. -/
theorem inFrame_succ_iff_ceilDivFour (depth coordinate : ℕ) :
    inFrame (depth + 1) coordinate =
      inFrame depth (ceilDivFour coordinate) := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (lt_trans Nat.zero_lt_one (one_lt_period (depth + 1)))
  rw [← (inFrame_periodic (depth + 1)).map_mod_nat coordinate,
    ← (inFrame_ceilDivFour_periodic depth).map_mod_nat coordinate]
  change inFrame (depth + 1) residue = inFrame depth (ceilDivFour residue)
  have periodEq := period_succ depth
  have startEq := frameStartResidue_succ depth
  have endEq := frameEndResidue_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour; rw [periodEq] at residueLt; omega
  apply Bool.eq_iff_iff.mpr
  rw [inFrame_eq_true_iff, inFrame_eq_true_iff, Nat.mod_eq_of_lt residueLt]
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [Nat.mod_eq_of_lt coarseLt]
    unfold ceilDivFour
    omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    have := scale_pos depth
    have := period_eq_four_mul_scale depth
    rw [coarseEq, Nat.mod_self]
    simp only [frameStartResidue, frameEndResidue] at endEq ⊢
    unfold ceilDivFour at coarseEq
    omega

private theorem boundaryLiftCondition_periodic
    (side : FrameSide) (depth : ℕ) :
    Function.Periodic (fun coordinate =>
      ceilDivFour coordinate % period depth = side.boundaryResidue depth ∧
        coordinate % 4 = side.fineResidue) (period (depth + 1)) := by
  intro coordinate
  exact propext (by simp [period_succ, ceilDivFour_add_four_mul])

private theorem boundary_periodic (side : FrameSide) (depth : ℕ) :
    Function.Periodic (fun coordinate =>
      coordinate % period (depth + 1) = side.boundaryResidue (depth + 1))
      (period (depth + 1)) := by
  intro coordinate
  simp

private theorem boundary_succ_iff
    (side : FrameSide) (depth coordinate : ℕ) :
    coordinate % period (depth + 1) = side.boundaryResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = side.boundaryResidue depth ∧
        coordinate % 4 = side.fineResidue := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (lt_trans Nat.zero_lt_one (one_lt_period (depth + 1)))
  rw [← (boundary_periodic side depth).map_mod_nat coordinate,
    ← (boundaryLiftCondition_periodic side depth).map_mod_nat coordinate]
  change residue % period (depth + 1) = side.boundaryResidue (depth + 1) ↔
    ceilDivFour residue % period depth = side.boundaryResidue depth ∧
      residue % 4 = side.fineResidue
  rw [Nat.mod_eq_of_lt residueLt]
  have periodEq := period_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour; rw [periodEq] at residueLt; omega
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [Nat.mod_eq_of_lt coarseLt]
    cases side with
    | opening =>
      have : 0 < frameStartResidue depth := by simp [frameStartResidue]
      simp only [FrameSide.boundaryResidue, FrameSide.fineResidue, frameStartResidue_succ]
      unfold ceilDivFour; omega
    | closing =>
      simp only [FrameSide.boundaryResidue, FrameSide.fineResidue, frameEndResidue_succ]
      unfold ceilDivFour; omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    have := side.boundaryResidue_pos depth
    have := side.boundaryResidue_lt_period depth
    have := side.ceilDivFour_boundaryResidue_succ depth
    rw [coarseEq, Nat.mod_self]
    constructor
    · intro h; rw [h] at coarseEq; omega
    · rintro ⟨h, _⟩; omega

/-- An opening boundary survives refinement exactly at fine residue one. -/
theorem openingBoundary_succ_iff (depth coordinate : ℕ) :
    coordinate % period (depth + 1) = frameStartResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameStartResidue depth ∧
        coordinate % 4 = 1 := by
  simpa [FrameSide.boundaryResidue, FrameSide.fineResidue] using
    boundary_succ_iff .opening depth coordinate

/-- A closing boundary survives refinement exactly at fine residue zero. -/
theorem closingBoundary_succ_iff (depth coordinate : ℕ) :
    coordinate % period (depth + 1) = frameEndResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameEndResidue depth ∧
        coordinate % 4 = 0 := by
  simpa [FrameSide.boundaryResidue, FrameSide.fineResidue] using
    boundary_succ_iff .closing depth coordinate

private theorem frameBorder_succ (depth coordinate transverse : ℕ) :
    liftBorder coordinate
        (frameBorder depth (ceilDivFour coordinate)
          (ceilDivFour transverse)) =
      frameBorder (depth + 1) coordinate transverse := by
  rw [frameBorder, frameBorder,
    ← inFrame_succ_iff_ceilDivFour depth transverse]
  simp only [openingBoundary_succ_iff, closingBoundary_succ_iff]
  have boundaryDistinct : frameStartResidue depth ≠ frameEndResidue depth := by
    have := scale_pos depth
    simp only [frameStartResidue, frameEndResidue]
    omega
  by_cases inside : inFrame (depth + 1) transverse <;>
    simp only [inside, ite_true]
  · by_cases opening :
        ceilDivFour coordinate % period depth = frameStartResidue depth
    · by_cases fineOpening : coordinate % 4 = 1 <;>
        simp [liftBorder, opening, fineOpening, boundaryDistinct]
    · by_cases closing :
          ceilDivFour coordinate % period depth = frameEndResidue depth
      · by_cases fineClosing : coordinate % 4 = 0 <;>
          simp [liftBorder, closing, fineClosing, boundaryDistinct.symm]
      · simp [liftBorder, opening, closing]
  · rfl

/- A deeper frame boundary projects to residue zero or one at every shallower
scale.  Shallower frame boundaries lie strictly beyond those residues, so no
point can belong to frame boundaries of two different depths.  The persistent
outer opening at coordinate one is disjoint for the same reason. -/

/-- Every shallower frame period divides a deeper frame scale. -/
theorem period_dvd_scale_of_lt {small large : ℕ} (h : small < large) :
    period small ∣ scale large := by
  rw [period, scale]
  exact Nat.pow_dvd_pow 4 (by omega)

private theorem largeBoundary_mod_small (side : FrameSide)
    {small large coordinate : ℕ} (h : small < large)
    (boundary : coordinate % period large = side.boundaryResidue large) :
    coordinate % period small = side.fineResidue := by
  have periodDvd : period small ∣ period large := by
    rw [period, period]
    exact Nat.pow_dvd_pow 4 (by omega)
  have scaleDvd : period small ∣ scale large := period_dvd_scale_of_lt h
  calc
    coordinate % period small =
        (coordinate % period large) % period small :=
      (Nat.mod_mod_of_dvd coordinate periodDvd).symm
    _ = side.boundaryResidue large % period small := by rw [boundary]
    _ = side.fineResidue := by
      cases side with
      | opening =>
          rw [FrameSide.boundaryResidue, FrameSide.fineResidue,
            frameStartResidue, Nat.add_mod,
            Nat.mod_eq_zero_of_dvd scaleDvd]
          have oneLt := one_lt_period small
          simp [Nat.mod_eq_of_lt oneLt]
      | closing =>
          rw [FrameSide.boundaryResidue, FrameSide.fineResidue,
            frameEndResidue, Nat.mul_mod,
            Nat.mod_eq_zero_of_dvd scaleDvd]
          simp

/-- A deeper opening has residue one in every shallower frame period. -/
theorem largeOpening_mod_small {small large coordinate : ℕ}
    (h : small < large)
    (opening : coordinate % period large = frameStartResidue large) :
    coordinate % period small = 1 := by
  exact largeBoundary_mod_small .opening h opening

/-- A deeper closing has residue zero in every shallower frame period. -/
theorem largeClosing_mod_small {small large coordinate : ℕ}
    (h : small < large)
    (closing : coordinate % period large = frameEndResidue large) :
    coordinate % period small = 0 := by
  exact largeBoundary_mod_small .closing h closing

private theorem outerBorder_lift (coordinate transverse : ℕ) :
    liftBorder coordinate
        (outerBorder (ceilDivFour coordinate) (ceilDivFour transverse)) =
      outerBorder coordinate transverse := by
  unfold outerBorder ceilDivFour
  split_ifs with h1 h2
  · simp [liftBorder, h2.1]
  · have hm : coordinate % 4 ≠ 1 := by omega
    simp [liftBorder, hm]
  · omega
  · simp [liftBorder]

/-- The opening precedes the closing in every frame period. -/
theorem frameStartResidue_lt_frameEndResidue (depth : ℕ) :
    frameStartResidue depth < frameEndResidue depth := by
  simp only [frameStartResidue, frameEndResidue]
  have := scale_pos depth
  omega

/-- An increasing-facing border is exactly an opening with transverse coordinate
inside its frame. -/
theorem frameBorder_eq_some_true_iff (depth coordinate transverse : ℕ) :
    frameBorder depth coordinate transverse = some true ↔
      inFrame depth transverse = true ∧
        coordinate % period depth = frameStartResidue depth := by
  unfold frameBorder
  by_cases inside : inFrame depth transverse <;>
    by_cases opening : coordinate % period depth = frameStartResidue depth <;>
    simp [inside, opening]

/-- A decreasing-facing border is exactly a closing with transverse coordinate inside its frame. -/
theorem frameBorder_eq_some_false_iff (depth coordinate transverse : ℕ) :
    frameBorder depth coordinate transverse = some false ↔
      inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  have distinct := (frameStartResidue_lt_frameEndResidue depth).ne
  unfold frameBorder
  split_ifs <;> simp_all

private theorem frameBorder_residue_gt_one
    {depth coordinate transverse : ℕ} {orientation : Bool}
    (border : frameBorder depth coordinate transverse = some orientation) :
    1 < coordinate % period depth := by
  have positive := scale_pos depth
  cases orientation with
  | false =>
    have boundary := ((frameBorder_eq_some_false_iff _ _ _).1 border).2
    simp only [frameEndResidue] at boundary
    omega
  | true =>
    have boundary := ((frameBorder_eq_some_true_iff _ _ _).1 border).2
    simp only [frameStartResidue] at boundary
    omega

private theorem frameBorders_disjoint_of_lt
    {small large coordinate transverse : ℕ} (h : small < large)
    {smallOrientation largeOrientation : Bool}
    (smallBorder : frameBorder small coordinate transverse = some smallOrientation)
    (largeBorder : frameBorder large coordinate transverse = some largeOrientation) :
    False := by
  have largeResidue : coordinate % period small = 0 ∨
      coordinate % period small = 1 := by
    cases largeOrientation with
    | false =>
      exact .inl (largeClosing_mod_small h ((frameBorder_eq_some_false_iff _ _ _).1 largeBorder).2)
    | true =>
      exact .inr (largeOpening_mod_small h ((frameBorder_eq_some_true_iff _ _ _).1 largeBorder).2)
  have smallResidue := frameBorder_residue_gt_one smallBorder
  omega

private theorem outerBorder_frameBorder_disjoint
    {depth coordinate transverse : ℕ} {outerOrientation frameOrientation : Bool}
    (outer : outerBorder coordinate transverse = some outerOrientation)
    (frame : frameBorder depth coordinate transverse = some frameOrientation) :
    False := by
  have coordinateMod : coordinate % period depth = 1 := by
    rw [((outerBorder_eq_some_iff _ _ _).mp outer).1, Nat.mod_eq_of_lt (one_lt_period depth)]
  have boundary := frameBorder_residue_gt_one frame
  omega

private theorem liftBorder_eq_some_imp
    {coordinate : ℕ} {border : Option Bool} {orientation : Bool}
    (lifted : liftBorder coordinate border = some orientation) :
    border = some orientation := by
  cases border with
  | none => simp [liftBorder] at lifted
  | some value =>
      cases value <;> cases orientation <;> simp_all [liftBorder]

/- Because all candidate borders are pairwise disjoint, the executable
`Fin.findSome?` selector has the simple extensional description below.  Its
lifted form then separates the inherited depths `2 .. level + 1` from the new
depth-one frame used by the substitution recurrence. -/

/-- The finite selector contains exactly the outer opening and the frame
boundaries at depths `1` through `level`. -/
theorem selectedBorder_eq_some_iff
    (level coordinate transverse : ℕ) (orientation : Bool) :
    selectedBorder level coordinate transverse = some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, 1 ≤ depth ∧ depth ≤ level ∧
          frameBorder depth coordinate transverse = some orientation := by
  rw [selectedBorder, Fin.findSome?_eq_some_iff]
  constructor
  · rintro ⟨index, candidate, _⟩
    by_cases zero : index.val = 0
    · exact .inl (by simpa [zero] using candidate)
    · exact .inr ⟨index.val, Nat.one_le_iff_ne_zero.2 zero, Nat.le_of_lt_succ index.isLt,
        by simpa [zero] using candidate⟩
  · rintro (outer | ⟨depth, positive, bounded, border⟩)
    · exact ⟨⟨0, Nat.zero_lt_succ level⟩, by simpa using outer,
        fun prior priorLt => (Nat.not_lt_zero prior.val priorLt).elim⟩
    · refine ⟨⟨depth, by omega⟩, ?_, fun prior priorLt => ?_⟩
      · simpa [Nat.ne_of_gt positive] using border
      · by_cases zero : prior.val = 0
        · cases outerEq : outerBorder coordinate transverse with
          | none => simp [zero]
          | some outerOrientation =>
              exact (outerBorder_frameBorder_disjoint outerEq border).elim
        · cases priorEq : frameBorder prior.val coordinate transverse with
          | none => simp [zero]
          | some priorOrientation =>
              exact (frameBorders_disjoint_of_lt priorLt priorEq border).elim

private theorem lift_selectedBorder_eq_some_iff
    (level coordinate transverse : ℕ) (orientation : Bool) :
    liftBorder coordinate
        (selectedBorder level (ceilDivFour coordinate) (ceilDivFour transverse)) =
          some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, 2 ≤ depth ∧ depth ≤ level + 1 ∧
          frameBorder depth coordinate transverse = some orientation := by
  constructor
  · intro lifted
    have coarse := liftBorder_eq_some_imp lifted
    rcases (selectedBorder_eq_some_iff _ _ _ _).1 coarse with outer | ⟨depth, hpos, hle, border⟩
    · exact .inl (by rw [← outerBorder_lift]; simpa only [outer, coarse] using lifted)
    · exact .inr ⟨depth + 1, by omega, by omega,
        by rw [← frameBorder_succ]; simpa only [border, coarse] using lifted⟩
  · rintro (outer | ⟨depth, hlo, hhi, border⟩)
    · have h := outerBorder_lift coordinate transverse
      rw [outer] at h
      have hc := liftBorder_eq_some_imp h
      simpa only [(selectedBorder_eq_some_iff level _ _ _).2 (.inl hc), hc] using h
    · obtain ⟨prior, rfl⟩ : ∃ prior, depth = prior + 1 := ⟨depth - 1, by omega⟩
      rw [← frameBorder_succ] at border
      have hc := liftBorder_eq_some_imp border
      simpa only [(selectedBorder_eq_some_iff level _ _ _).2
        (.inr ⟨prior, by omega, by omega, hc⟩), hc] using border

private theorem ceilDivFour_eight_mul_add (block offset : ℕ) :
    ceilDivFour (8 * block + offset) =
      2 * block + ceilDivFour offset := by
  unfold ceilDivFour
  have h : 8 * block + offset + 3 = (offset + 3) + 4 * (2 * block) := by omega
  rw [h, Nat.add_mul_div_left _ _ (by decide), Nat.add_comm]

private theorem frameBorder_zero_parity (coordinate transverse offsetX offsetY : ℕ) :
    frameBorder 0 (2 * coordinate + offsetX) (2 * transverse + offsetY) =
      frameBorder 0 (2 * (coordinate % 2) + offsetX)
        (2 * (transverse % 2) + offsetY) := by
  have hmod (a b : ℕ) : (2 * a + b) % 4 = (2 * (a % 2) + b) % 4 := by omega
  simp [frameBorder, inFrame, period, frameStartResidue, frameEndResidue, scale, hmod]

private theorem liftBorder_eight_mul_add (block offset : ℕ)
    (border : Option Bool) :
    liftBorder (8 * block + offset) border = liftBorder offset border := by
  cases border with
  | none => rfl
  | some orientation =>
      cases orientation <;>
        simp [liftBorder, Nat.add_mod, Nat.mul_mod]

/-- Splitting the direct finite formula at depth one recovers the local
substitution recurrence used by the finite-state factor. -/
private theorem selectedBorder_succ (level coordinate transverse : ℕ) :
    selectedBorder (level + 1) coordinate transverse =
      Option.or
        (liftBorder coordinate <|
          selectedBorder level (ceilDivFour coordinate) (ceilDivFour transverse))
        (liftBorder coordinate <|
          frameBorder 0 (ceilDivFour coordinate) (ceilDivFour transverse)) := by
  apply Option.ext
  intro orientation
  rw [selectedBorder_eq_some_iff, Option.or_eq_some_iff,
    lift_selectedBorder_eq_some_iff, frameBorder_succ]
  constructor
  · rintro (outer | ⟨depth, positive, bounded, border⟩)
    · exact Or.inl (Or.inl outer)
    · rcases eq_or_ne depth 1 with rfl | depthNe
      · refine .inr ⟨?_, border⟩
        cases oldEq : liftBorder coordinate
            (selectedBorder level (ceilDivFour coordinate)
              (ceilDivFour transverse)) with
        | none => rfl
        | some _ =>
          rcases (lift_selectedBorder_eq_some_iff _ _ _ _).1 oldEq with
            oldOuter | ⟨_, oldLower, _, oldBorder⟩
          · exact (outerBorder_frameBorder_disjoint oldOuter border).elim
          · exact (frameBorders_disjoint_of_lt oldLower border oldBorder).elim
      · exact .inl (.inr ⟨depth, by omega, bounded, border⟩)
  · rintro ((outer | ⟨depth, lower, bounded, border⟩) | ⟨_, new⟩)
    · exact Or.inl outer
    · exact Or.inr ⟨depth, by omega, bounded, border⟩
    · exact Or.inr ⟨1, by omega, by omega, new⟩

private theorem selectedBorder_succ_block
    (level blockX blockY offsetX offsetY : ℕ) :
    selectedBorder (level + 1)
        (8 * blockX + offsetX) (8 * blockY + offsetY) =
      Option.or
        (liftBorder offsetX <|
          selectedBorder level
            (2 * blockX + ceilDivFour offsetX)
            (2 * blockY + ceilDivFour offsetY))
        (liftBorder offsetX <|
          frameBorder 0
            (2 * (blockX % 2) + ceilDivFour offsetX)
            (2 * (blockY % 2) + ceilDivFour offsetY)) := by
  rw [selectedBorder_succ, ceilDivFour_eight_mul_add, ceilDivFour_eight_mul_add,
    liftBorder_eight_mul_add, liftBorder_eight_mul_add, frameBorder_zero_parity]

private theorem selectedBorder_succ_child
    (level blockX blockY childX childY x y : ℕ) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY) + y) =
      Option.or
        (liftBorder (2 * childX + x) <|
          selectedBorder level
            (2 * blockX + ceilDivFour (2 * childX + x))
            (2 * blockY + ceilDivFour (2 * childY + y)))
        (liftBorder (2 * childX + x) <|
          frameBorder 0
            (2 * (blockX % 2) + ceilDivFour (2 * childX + x))
            (2 * (blockY % 2) + ceilDivFour (2 * childY + y))) := by
  have h (a b c : ℕ) : 2 * (4 * a + b) + c = 8 * a + (2 * b + c) := by omega
  rw [h, h, selectedBorder_succ_block]

/-- The arithmetic halo at a canonical node, including its one-quarter boundary margin. -/
private def arithmeticState (level x y : ℕ) : BorderState where
  node := supertileNodeGrid level seedNode x y
  xParity := ⟨x % 2, Nat.mod_lt _ (by decide)⟩
  yParity := ⟨y % 2, Nat.mod_lt _ (by decide)⟩
  halo.row i j := selectedBorder level (2 * x + i.val) (2 * y + j.val)
  halo.column i j := selectedBorder level (2 * y + j.val) (2 * x + i.val)

private theorem frameBorder_zero (x y : ℕ) : frameBorder 0 x y = baseFrame x y := by
  simp [frameBorder, inFrame, period, frameStartResidue, frameEndResidue, scale, baseFrame]

private theorem arithmeticState_succ (level x y : ℕ) (i j : Fin 4) :
    arithmeticState (level + 1) (4 * x + i.val) (4 * y + j.val) =
      (arithmeticState level x y).refine i j := by
  have node : supertileNodeGrid (level + 1) seedNode (4 * x + i.val) (4 * y + j.val) =
      (supertileNodeGrid level seedNode x y).child (blockPosition i j) := by
    have node := supertileNodeGrid_block level seedNode x y i.val j.val i.isLt j.isLt
    simpa only [childPosition, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using node
  unfold arithmeticState BorderState.refine
  simp only [node]
  congr 1
  · fin_index
  · fin_index
  · apply congrArg₂ BorderHalo.mk
    · funext a b
      simpa only [frameBorder_zero] using
        selectedBorder_succ_child level x y i.val j.val a.val b.val
    · funext a b
      simpa only [frameBorder_zero] using
        selectedBorder_succ_child level y x j.val i.val b.val a.val

private theorem arithmeticState_zero : arithmeticState 0 0 0 = BorderState.seed := by
  unfold arithmeticState BorderState.seed
  congr 1
  apply congrArg₂ BorderHalo.mk <;> funext x y <;>
    simp [selectedBorder, Fin.findSome?, Fin.foldl_succ]

private theorem arithmeticState_admissible (level x y : ℕ)
    (hx : x < 4 ^ level) (hy : y < 4 ^ level) :
    (arithmeticState level x y).Admissible := by
  induction level generalizing x y with
  | zero =>
    obtain rfl : x = 0 := by simpa using hx
    obtain rfl : y = 0 := by simpa using hy
    exact arithmeticState_zero.symm ▸ BorderState.seed_admissible
  | succ level ih =>
    have hx' : x / 4 < 4 ^ level := by rw [pow_succ] at hx; omega
    have hy' : y / 4 < 4 ^ level := by rw [pow_succ] at hy; omega
    simpa only [← arithmeticState_succ, Nat.div_add_mod] using
      BorderState.refine_admissible (ih _ _ hx' hy')
        ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩

/-- The three certified ways index zero occurs in a canonical child block. -/
theorem supertileIndexGrid_zero_cases
    (level x y : ℕ) (hx : x < 4 ^ (level + 1))
    (hy : y < 4 ^ (level + 1))
    (indexZero : supertileIndexGrid (level + 1) seedNode x y = 0) :
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      supertileIndexGrid level seedNode (x / 4) (y / 4) = 0 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) ∨
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      supertileIndexGrid level seedNode (x / 4) (y / 4) = 4 ∧
      (x / 4) % 2 = 1 ∧ (y / 4) % 2 = 1) ∨
    (x % 4 = 2 ∧ y % 4 = 2 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) := by
  have hx' : x / 4 < 4 ^ level := by rw [pow_succ] at hx; omega
  have hy' : y / 4 < 4 ^ level := by rw [pow_succ] at hy; omega
  let i : Fin 4 := ⟨x % 4, Nat.mod_lt _ (by decide)⟩
  let j : Fin 4 := ⟨y % 4, Nat.mod_lt _ (by decide)⟩
  have eqn : (arithmeticState level (x / 4) (y / 4)).refine i j =
      arithmeticState (level + 1) x y := by
    simp only [← arithmeticState_succ, i, j, Nat.div_add_mod]
  simpa only [arithmeticState, supertileIndexGrid, Fin.ext_iff, i, j, Fin.val_zero, Fin.val_one,
    Fin.val_two] using
    BorderState.corner_transition (arithmeticState_admissible level _ _ hx' hy') i j
      (eqn ▸ indexZero)

private theorem interiors_seed_eq_selectedBorder
    (level x y : ℕ) (hx : x < side level) (hy : y < side level) :
    rowInterior level seedNode x y = selectedBorder level x y ∧
      columnInterior level seedNode x y = selectedBorder level y x := by
  have hx' : x / 2 < 4 ^ level := by dsimp only [side] at hx; omega
  have hy' : y / 2 < 4 ^ level := by dsimp only [side] at hy; omega
  have observation := BorderState.observations
    (arithmeticState_admissible level _ _ hx' hy')
    ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩
  simpa only [arithmeticState, Fin.val_castSucc, Nat.div_add_mod, rowInterior, columnInterior] using
    And.intro observation.1.symm observation.2.symm

/-- Actual selected vertical borders of the seed patch are precisely the arithmetic borders. -/
theorem rowInterior_seed_eq_selectedBorder
    (level x y : ℕ) (hx : x < side level) (hy : y < side level) :
    rowInterior level seedNode x y = selectedBorder level x y :=
  (interiors_seed_eq_selectedBorder level x y hx hy).1

/-- Actual selected horizontal borders of the seed patch are the transposed arithmetic borders. -/
theorem columnInterior_seed_eq_selectedBorder
    (level x y : ℕ) (hx : x < side level) (hy : y < side level) :
    columnInterior level seedNode x y = selectedBorder level y x :=
  (interiors_seed_eq_selectedBorder level x y hx hy).2

end Cslib.WangTile.Robinson.Carrier
