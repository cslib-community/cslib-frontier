/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary client of paths around separated rectangles)

import CslibFrontier.Foundations.Geometry.SeparatedStarObstacles
import Mathlib.Tactic.NormNum

/-!
Two nondegenerate disjoint horizontal spokes lie in separated rectangles with common
vertical bounds. Their complement is path connected.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparatedStarObstacles

open Cslib

private def center (i : Bool) : ℂ := if i then 3 else 0
private def tip (i : Bool) : ℂ := if i then 4 else 1
private noncomputable def leftBound (i : Bool) : ℝ := if i then 5 / 2 else -1
private def rightBound (i : Bool) : ℝ := if i then 5 else 2

example : IsPathConnected (⋃ i : Bool, segment ℝ (center i) (tip i))ᶜ := by
  refine isPathConnected_compl_iUnion_starConvex_of_separated_rectangles
    (fun i => segment ℝ (center i) (tip i)) center leftBound rightBound (-1) 1
    (fun i => (convex_segment (𝕜 := ℝ) _ _).starConvex (left_mem_segment ℝ _ _))
    (fun i => left_mem_segment ℝ _ _) ?_ ?_ (x := -2) ?_
  · intro i z hz
    let box : Set ℂ := {w | w.re ∈ Set.Ioo (leftBound i) (rightBound i) ∧
      w.im ∈ Set.Ioo (-1) 1}
    have hbox : Convex ℝ box :=
      ((convex_Ioo _ _).linear_preimage Complex.reCLM.toLinearMap).inter
        ((convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap)
    have hc : center i ∈ box := by
      cases i <;> norm_num [box, center, leftBound, rightBound, Set.mem_Ioo]
    have ht : tip i ∈ box := by
      cases i <;> norm_num [box, tip, leftBound, rightBound, Set.mem_Ioo]
    exact hbox.segment_subset hc ht hz
  · intro i j hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    cases i <;> cases j <;> simp_all [leftBound, rightBound, Set.mem_Icc] <;> linarith
  · intro i
    cases i <;> norm_num [leftBound, rightBound, Set.mem_Ioo]

end CslibFrontierTests.SeparatedStarObstacles
