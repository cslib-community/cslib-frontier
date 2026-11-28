/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Corollary

/-!
# Tests for `(5, 3, 9)` / bigraded Farkas optimality and explicit `4N - o(N)` bounds in `P`
-/

set_option linter.privateModule false

public section

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

/-- Non-vacuous `State`-grounded bigraded Farkas optimality check: `stratifiedStepSound_uniform`
satisfies `StratifiedStepSound` with `c - w_init = 9 - 5 = 4`, and any `StratifiedStepSound`
potential attaining `c - w_init = 4` satisfies `ce = 1`, `bp 0 1 1 0 = bp 1 0 1 0`, `5 ≤ w 2 0`,
and `9 ≤ c`. -/
example : StratifiedStepSound 1 (fun dg de => (weight (dg + de) : ℚ)) (fun _ _ _ _ => 3) 9 5 :=
  stratifiedStepSound_uniform

example {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {c w_init : ℚ}
    (h : StratifiedStepSound ce w bp c w_init) (h_opt : c - w_init = 4) :
    c - w_init ≤ 4 ∧ ce = 1 ∧ bp 0 1 1 0 = bp 1 0 1 0 ∧ 5 ≤ w 2 0 ∧ 9 ≤ c := by
  obtain ⟨hce, _, hbp, hw2, _, hc, _⟩ := stratified_weight_lower_bounds_of_sub_eq_four h h_opt
  exact ⟨stratified_weight_sub_le_four h, hce, hbp, hw2, hc⟩

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
  exists_mem_P_eventually_le_cost_primeDisperser

end CslibFrontierTests.AffineDisperser4nCorollary
