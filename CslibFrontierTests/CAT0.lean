/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Foundations.Geometry.CAT0.Toolkit
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.MidpointTerm

/-! Tests of the complete CAT(0) API and of formal midpoint terms. -/

namespace CslibFrontierTests.CAT0

open Cslib Cslib.CAT0

/-- The real line is a complete CAT(0) space, through the inner product space instance. -/
example : CompleteCAT0Space ℝ := inferInstance

/-- The chosen midpoint of `0` and `2` in `ℝ` is `1`: it is the unique point at distance `1`
from both. -/
example : mid (0 : ℝ) 2 = 1 := by
  have h1 := dist_mid_left (0 : ℝ) 2
  have h2 := dist_mid_right (0 : ℝ) 2
  obtain ⟨γ, -, hγ⟩ := existsUnique_dist_eq (0 : ℝ) 2 (t := 1 / 2) (by norm_num) (by norm_num)
  have e1 : mid (0 : ℝ) 2 = γ := hγ _ ⟨by rw [h1]; ring, by rw [h2]; ring⟩
  have e2 : (1 : ℝ) = γ := hγ _ ⟨by norm_num [Real.dist_eq], by norm_num [Real.dist_eq]⟩
  rw [e1, ← e2]

/-- The point at fraction `1/4` between `0` and `4` in `ℝ` satisfies the inequality of the point
at fraction `t`, from its distances. -/
example : IsPointAt (0 : ℝ) 4 (1 / 4) 1 :=
  isPointAt_of_dist (by norm_num) (by norm_num) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq])

/-- The projection onto the closed convex set `[1, 2]` of `5` is a nearest point. -/
example : ∃ P ∈ Set.Icc (1 : ℝ) 2, ∀ q ∈ Set.Icc (1 : ℝ) 2, dist 5 P ≤ dist 5 q := by
  obtain ⟨P, hP, h, -⟩ := exists_proj (Set.Icc (1 : ℝ) 2) isClosed_Icc ⟨1, by norm_num⟩
    (fun x hx v hv m h1 h2 => by
      rw [Real.dist_eq, Real.dist_eq] at h1 h2
      constructor <;> cases abs_cases (x - m) <;> cases abs_cases (m - v) <;>
        cases abs_cases (x - v) <;> linarith [hx.1, hx.2, hv.1, hv.2])
    5
  exact ⟨P, hP, h⟩

/-! ### Formal midpoints: the boundary used by the curvature proof -/

open Cslib.Circuits.Arithmetic.Separation MidpointTerm

/-- Two midpoints of letters: depth `2`. -/
abbrev term2 : FreeMagma ℕ := (FreeMagma.of 0 * FreeMagma.of 1) * FreeMagma.of 2

example : depth term2 = 2 := rfl

/-- A term of depth exactly `n` stays at level `n`. -/
example : place 2 term2 = .inl term2 := place_of_depth_le le_rfl

/-- A term of depth `n + 1` splits into its two arguments, of depth at most `n`. -/
example : place 1 term2 = .inr (FreeMagma.of 0 * FreeMagma.of 1, FreeMagma.of 2) := rfl

/-- The lemma form, for an arbitrary term of depth `n + 1`. -/
example (s : FreeMagma ℕ) (h : depth s = 3) : ∃ a b, s = a * b ∧ depth a ≤ 2 ∧ depth b ≤ 2 := by
  obtain ⟨a, b, hs, -, ha, hb⟩ := place_of_depth_eq_succ (n := 2) h
  exact ⟨a, b, hs, ha, hb⟩

example : base term2 = 0 := rfl

end CslibFrontierTests.CAT0
