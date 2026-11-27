/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary trisection API client)

public import CslibFrontier.Foundations.Geometry.Polygonal.Trisection
import Mathlib.Tactic.NormNum

/-! # Two cuts within one segment -/

public section

namespace CslibFrontierTests.PolygonalTrisection

open Cslib.Polygonal

private def p : Route := Route.line 0 3

/-- Two cuts in the same original segment give distinct new ends. -/
theorem one_segment_cut_points :
    ((Route.line 0 3).trisect (1 / 3) (1 / 3) 1).start = 1 ∧
      ((Route.line 0 3).trisect (1 / 3) (1 / 3) 1).finish = 2 := by
  change (p.trisect (1 / 3) (1 / 3) 1).endpoint false = 1 ∧
    (p.trisect (1 / 3) (1 / 3) 1).endpoint true = 2
  rw [Route.endpoint_trisect, Route.endpoint_trisect]
  change (Route.line 0 3).eval 0 (1 / 3) = 1 ∧
    (Route.line 0 3).eval 0 (1 - 1 / 3) = 2
  rw [Route.eval_line, Route.eval_line]
  norm_num [AffineMap.lineMap_apply_module', Complex.real_smul]

example : (∀ k : Fin 3, (p.trisect (1 / 3) (1 / 3) k).IsSimple) ∧
    (⋃ k : Fin 3, (p.trisect (1 / 3) (1 / 3) k).support) = p.support := by
  have hp : p.IsSimple := Route.isSimple_line (by norm_num)
  exact ⟨hp.trisect (by norm_num) (by norm_num) (by norm_num),
    p.support_trisect (by norm_num) (by norm_num) (by norm_num)⟩

-- The final chord's first point represents the second cut in the old parameter.
example : ∃ (j : Fin p.segments) (r : ℝ), r ∈ Set.Icc 0 1 ∧
    p.eval j r = (p.trisect (1 / 3) (1 / 3) 2).eval 0 0 ∧
    p.position j r = 2 / 3 := by
  obtain ⟨j, r, hr, he, _, hlo, _⟩ := p.exists_trisect_eval
    (s := 1 / 3) (t := 1 / 3) (by norm_num) (by norm_num) (by norm_num) 2 0 0 (by simp)
  refine ⟨j, r, hr, he, ?_⟩
  have h := hlo.mpr (by simp [Route.AtEnd, Route.position])
  have hi : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  rw [hi] at h
  change p.position j r = (p.segments : ℝ) - 1 / 3 at h
  have hc : p.segments = 1 := rfl
  rw [hc, Nat.cast_one] at h
  linarith

end CslibFrontierTests.PolygonalTrisection
