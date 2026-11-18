/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary coordinate-order clients)

public import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
public import CslibFrontier.Foundations.Geometry.Polygonal.Join
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Ordinary clients derive continuum simplicity from coordinate order, test a shared knot
and source reversal, and retain the essential closed-parameter restriction. Node heights
may make large excursions. Routes have at least one segment; the no-patch case is a line.
-/

public section

namespace Cslib.Tests.PolygonalCoordinateOrder

open Cslib.Polygonal Cslib.Polygonal.Route

private def bent : Route := (line (⟨0, 3⟩ : ℂ) ⟨1, -100⟩).append ⟨4, 7⟩

private theorem bent_increasing : StrictMono fun k => (bent.point k).re := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · change (0 : ℝ) < 1
    norm_num
  · change (1 : ℝ) < 4
    norm_num

-- Large height excursions do not create self-contact in a strictly ordered x-chain.
/-- Strict coordinate order proves simplicity even with large imaginary excursions. -/
theorem increasing_excursive_simple :
    ((line (⟨0, 3⟩ : ℂ) ⟨1, -100⟩).append ⟨4, 7⟩).IsSimple :=
  isSimple_of_strictMono_re bent_increasing

-- Adjacent descriptions of one knot coincide; neither comparison is strict.
example : bent.eval 0 1 = bent.eval 1 0 ∧
    bent.position 0 1 = bent.position 1 0 ∧
    ¬(bent.eval 0 1).re < (bent.eval 1 0).re ∧
    ((bent.eval 0 1).re < (bent.eval 1 0).re ↔ bent.position 0 1 < bent.position 1 0) := by
  refine ⟨?_, ?_, ?_, eval_re_lt_iff_position_lt_of_strictMono bent bent_increasing
    0 1 1 0 (by norm_num) (by norm_num)⟩ <;>
    norm_num [bent, eval, position, line, append, AffineMap.lineMap_apply_module] <;>
    rfl

example : StrictAnti fun k => (bent.reverse.point k).re := by
  intro i j hij
  change (bent.point j.rev).re < (bent.point i.rev).re
  exact bent_increasing (Fin.rev_lt_rev.mpr hij)

-- Complementary positions reverse the order; no second affine interpolation proof.
example (i j : Fin bent.reverse.segments) (s t : ℝ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    (bent.reverse.eval i s).re < (bent.reverse.eval j t).re ↔
      bent.reverse.position j t < bent.reverse.position i s := by
  rw [eval_reverse, eval_reverse, position_reverse, position_reverse]
  rw [eval_re_lt_iff_position_lt_of_strictMono bent bent_increasing i.rev j.rev
    (1 - s) (1 - t) (Set.Icc.one_sub_mem hs) (Set.Icc.one_sub_mem ht)]
  constructor <;> intro h <;> linarith

example : bent.reverse.IsSimple := (isSimple_of_strictMono_re bent_increasing).reverse

-- A single nonvertical segment is the no-patch case, not a zero-segment route.
example : (line (0 : ℂ) ⟨2, 5⟩).IsSimple := by
  apply isSimple_of_strictMono_re
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  change (0 : ℝ) < 2
  norm_num

-- A degenerate first segment cannot satisfy strict node order.
example : ¬StrictMono fun k => (((line (0 : ℂ) 0).append 1).point k).re := by
  intro h
  have hh := (Fin.strictMono_iff_lt_succ.mp h) (0 : Fin 2)
  change (0 : ℝ) < 0 at hh
  exact (lt_irrefl 0) hh

private def unequalSteps : Route := (line (0 : ℂ) 1).append 100

private theorem unequalSteps_increasing : StrictMono fun k => (unequalSteps.point k).re := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · change (0 : ℝ) < 1
    norm_num
  · change (1 : ℝ) < 100
    norm_num

-- Outside [0,1] evaluation order can disagree with position order despite strict nodes.
example : StrictMono (fun k => (unequalSteps.point k).re) ∧
    (unequalSteps.eval 0 2).re < (unequalSteps.eval 1 (1 / 2)).re ∧
    ¬unequalSteps.position 0 2 < unequalSteps.position 1 (1 / 2) := by
  refine ⟨unequalSteps_increasing, ?_, ?_⟩
  · change (AffineMap.lineMap (0 : ℂ) 1 2).re <
      (AffineMap.lineMap (1 : ℂ) 100 (1 / 2)).re
    norm_num [AffineMap.lineMap_apply_module]
  · norm_num [position, unequalSteps, segments, append, line]

end Cslib.Tests.PolygonalCoordinateOrder
