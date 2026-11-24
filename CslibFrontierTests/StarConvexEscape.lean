/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary client of star-convex escape)

import CslibFrontier.Foundations.Geometry.StarConvexEscape
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.NormNum

/-!
Escape from `-1` to the boundary of the radius-two disk while avoiding two perpendicular
spokes from `0`. Both the starting point and the entire obstacle are inside the disk.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.StarConvexEscape

open Cslib

example :
    ∃ y ∈ frontier (Metric.closedBall (0 : ℂ) 2),
      segment ℝ (-1 : ℂ) y ⊆
        Metric.closedBall (0 : ℂ) 2 \ (segment ℝ (0 : ℂ) 1 ∪ segment ℝ 0 Complex.I) := by
  have h1 := left_mem_segment ℝ (0 : ℂ) 1
  have hi := left_mem_segment ℝ (0 : ℂ) Complex.I
  have hs := ((convex_segment (𝕜 := ℝ) (0 : ℂ) 1).starConvex h1).union
    ((convex_segment (𝕜 := ℝ) (0 : ℂ) Complex.I).starConvex hi)
  refine exists_segment_to_frontier_avoiding_starConvex (isCompact_closedBall _ _)
    (convex_closedBall _ _) hs (Or.inl h1) ?_ ?_
  · rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_one]
    norm_num
  · rintro (h | h)
    · rw [segment_eq_image_lineMap] at h
      obtain ⟨t, ht, heq⟩ := h
      have hre := congrArg Complex.re heq
      norm_num [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, smul_eq_mul]
        at hre
      linarith only [ht.1, hre]
    · rw [segment_eq_image_lineMap] at h
      obtain ⟨t, _, heq⟩ := h
      have hre := congrArg Complex.re heq
      norm_num [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re, smul_eq_mul]
        at hre

end CslibFrontierTests.StarConvexEscape
