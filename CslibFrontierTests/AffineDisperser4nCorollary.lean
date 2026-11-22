/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Corollary

/-!
# Tests for `(5, 3, 9)` / bigraded Farkas optimality and explicit `4N - o(N)` bounds in `P`
-/

namespace CslibFrontierTests.AffineDisperser4nCorollary

open Filter Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean.SemiCircuit Cslib.Complexity
open Cslib.Circuits.Boolean.AffineDisperser4n

/-- Weight-constraint optimality check: `(α, β, c) = (5, 3, 9)` attains `c - α = 4` tightly across
all three inequalities, any solution has `c - α ≤ 4`, and equality forces `9 ≤ c`. -/
example :
    (5 : ℚ) ≤ 3 + 2 ∧ (9 : ℚ) ≤ 2 * 3 + 3 ∧ (9 : ℚ) ≤ 2 * 5 - 3 + 2 ∧ (9 : ℚ) - 5 = 4 := by
  norm_num

example {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * β + 3) (h₃ : c ≤ 2 * α - β + 2)
    (h₄ : c - α = 4) : c - α ≤ 4 ∧ 9 ≤ c := by
  obtain ⟨_, _, hc, _⟩ := weight_lower_bounds_of_sub_eq_four h₁ h₂ h₃ h₄
  exact ⟨weight_sub_le_four h₁ h₃, hc⟩

/-- Bigraded Farkas optimality check: even with separate equation weight `ce` and bigraded
`(dg, de)` weights, attaining `c - w_init = 4` forces `ce = 1`, `9 ≤ c`, and `4 ≤ w 1 0`. -/
example {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {ce c w_init : ℚ}
    (h_init : w 2 0 ≤ w_init) (h_reroute : w 2 0 ≤ w 1 0 + 1) (h_move : ce ≤ 1)
    (h_pis : w 2 0 ≤ bp 1 0 1 0 + 1 + ce) (h_pc : c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2)
    (h_aop : c ≤ 2 * bp 1 0 1 0 + 3) (h_opt : c - w_init = 4) :
    c - w_init ≤ 4 ∧ ce = 1 ∧ 9 ≤ c ∧ 4 ≤ w 1 0 := by
  obtain ⟨hce, _, _, _, hc, _⟩ :=
    stratified_weight_lower_bounds_of_sub_eq_four h_init h_move h_pis h_pc h_aop h_opt
  exact ⟨stratified_weight_sub_le_four h_init h_move h_pis h_pc, hce, hc,
    stratified_fanout_one_lower_bound h_init h_reroute h_move h_pis h_pc h_aop h_opt⟩

/-- An explicit language in `P` (`explicitDisperserLanguage`) whose `N`-bit slices eventually
require at least `3.6 * N` genuinely binary `B₂` gates. -/
example : ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (L.slice N)) →
      36 * N ≤ 10 * C.program.cost binaryB2Cost := by
  refine ⟨Cslib.AffineDisperser.explicitDisperserLanguage,
    Cslib.AffineDisperser.explicitDisperserLanguage_mem_P, ?_⟩
  have hev : ∀ᶠ N in atTop, 2 ^ 200 ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [eventually_four_mul_le_cost_add_explicitDisperser, hev] with N hlb hN C hC
  rw [Cslib.AffineDisperser.slice_explicitDisperserLanguage] at hC
  have hC' := hlb C hC
  have hN0 : N ≠ 0 := by have : 0 < 2 ^ 200 := Nat.two_pow_pos 200; omega
  have hlog : 200 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by omega) hN0).2 hN
  have hdiv : 54 * N / (Nat.log 2 N + 1) ≤ 54 * N / 201 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h100 : 100 ≤ N := le_trans (by decide) hN
  omega

/-- Unconditional language in `P` (`Li.primeDisperserLanguage`) requiring
`4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates. -/
example : ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (L.slice N)) →
      4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.program.cost binaryB2Cost : ℝ) :=
  exists_mem_P_eventually_four_mul_sub_le_cost_primeDisperser

end CslibFrontierTests.AffineDisperser4nCorollary
