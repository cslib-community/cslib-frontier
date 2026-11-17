/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
import CslibFrontier.Foundations.Combinatorics.Expander.Chernoff
import CslibFrontier.Foundations.Combinatorics.Expander.LowerBound

set_option linter.privateModule false
open Cslib Finset Real
open scoped BigOperators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V] [Nonempty D]
  (G : RotationMap V D)

-- Arora–Barak Theorem 7.41 with the corrected sign, for `k = t + 1` walk vertices and
-- `λ = λ(G)`.
example (B : Finset V) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ < |(G.visitCount B p : ℝ) / (t + 1) - dens B|} : ℝ) <
      2 * exp (-(1 - G.spectralExpansion) * δ ^ 2 * (t + 1) / 60) :=
  G.dens_filter_abs_visitCount_div_sub_gt_lt B le_rfl hδ t

-- Non-vacuity: on the complete graph with loops (`λ = 0`), deviations of `1 / 2` over `288`
-- vertices have probability at most `2 e⁻²`, which is less than one.
example (B : Finset (Fin 5)) :
    (dens {p : Fin 5 × (Fin 287 → Fin 5) |
      1 / 2 < |((RotationMap.complete (Fin 5)).visitCount B p : ℝ) / (287 + 1) - dens B|} : ℝ) <
      1 := by
  have h := (RotationMap.complete (Fin 5)).dens_filter_abs_visitCount_div_sub_dens_gt_le B
    (δ := 1 / 2) (by norm_num) 287
  rw [RotationMap.spectralExpansion_complete] at h
  refine h.trans_lt ?_
  have he : 3 ≤ exp 2 := by linarith [add_one_le_exp 2]
  have : exp (-(1 - 0) * (1 / 2) ^ 2 * ((287 : ℕ) + 1 : ℝ) / 36) = (exp 2)⁻¹ := by
    rw [← exp_neg]; norm_num
  rw [this]
  have : 0 < exp 2 := exp_pos 2
  rw [← div_eq_mul_inv, div_lt_one this]
  linarith

-- The general form: a bounded function with mean zero.
example {g : V → ℝ} (hg : 𝔼 v, g v = 0) (hg₁ : ∀ v, |g v| ≤ 1) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ * (t + 1) ≤ |∑ i ∈ range (t + 1), g (G.walkAt p i)|} : ℝ) ≤
      2 * exp (-(1 - G.spectralExpansion) * δ ^ 2 * (t + 1) / 36) :=
  G.dens_filter_le_abs_sum_walkAt_le hg hg₁ hδ t
