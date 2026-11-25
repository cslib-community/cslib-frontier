/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
public import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Internal Helpers for Johnson-Bound Curve and Affine Proximity Gaps

Siegel error-bound substitution, `johnsonCurveBound` scaling, and rational-to-integer weight
clearing helpers shared privately by at least two submodules (`JohnsonCurve`, `JohnsonAffine`,
and `Dichotomy`).

## Main results

* `Cslib.Code.johnsonCurveBound_mul_cast_le`: linear weight scaling of `johnsonCurveBound`.
* `Cslib.Code.rat_weights_to_nat`, `Cslib.Code.rat_weights_johnson_nat`: rational weight clearing.
* `Cslib.Code.siegel_eta_bound_le`: explicit-constant `η`-parameterized error conversion.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- Internal helper: linear weight scaling of `johnsonCurveBound` over `ℝ`. -/
theorem johnsonCurveBound_mul_cast_le
    {n m d D r M : ℕ} (hn : 1 ≤ n) (hM : 0 < M) {U : ℝ}
    (hU : (ProximityGap.johnsonCurveBound n m d D r n : ℝ) ≤ U) :
    (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) ≤ (M : ℝ) * U := by
  have hmul : (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) * n ≤
      (ProximityGap.johnsonCurveBound n m d D r n : ℝ) * (M * n) := by
    exact_mod_cast ProximityGap.johnsonCurveBound_mul_le (m := m) (d := d) (D := D) (r := r)
      (Nat.le_mul_of_pos_left n hM)
  exact (le_of_mul_le_mul_right (by linarith) (Nat.cast_pos.2 hn)).trans
    (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg M))

/-- Internal helper: integer weights bounded by `M` sum to at most `M * |ι|` over any subset. -/
theorem sum_le_mul_card_of_le {ι : Type*} [Fintype ι] {W : ι → ℕ} {M : ℕ}
    (hW : ∀ i, W i ≤ M) (S : Finset ι) : ∑ i ∈ S, W i ≤ M * Fintype.card ι :=
  (Finset.sum_le_sum fun i _ => hW i).trans <| by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]; exact Nat.mul_le_mul_left M S.card_le_univ

/-- Internal helper: clears common denominator `M > 0` from rational weights `μ : ι → ℚ` with
`μ i = a_i / M ≤ 1`, producing integer weights `W : ι → ℕ` and threshold `B_W = ⌈θ * M⌉₊` with
exact subset equivalence `θ ≤ ∑_{i ∈ S} μ i ↔ B_W ≤ ∑_{i ∈ S} W i` and `θ ≤ (B_W + M - 1) / M`. -/
theorem rat_weights_to_nat
    {ι : Type*} [Fintype ι] {M : ℕ} (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    (θ : ℚ) :
    ∃ W : ι → ℕ,
      (∀ i, 0 ≤ μ i) ∧
      (∀ i, W i ≤ M) ∧
      (∑ i : ι, W i ≤ M * Fintype.card ι) ∧
      (∀ S : Finset ι, θ ≤ ∑ i ∈ S, μ i ↔ ⌈θ * (M : ℚ)⌉₊ ≤ ∑ i ∈ S, W i) ∧
      θ ≤ (((⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℚ) := by
  let W : ι → ℕ := fun i => (hμ_den i).choose
  have hW_eq (i) : μ i = (W i : ℚ) / M := (hμ_den i).choose_spec
  have hM_posQ : (0 : ℚ) < M := Nat.cast_pos.2 hM
  have hW_le (i) : W i ≤ M := Nat.cast_le.1 ((div_le_one hM_posQ).1 (hW_eq i ▸ hμ_le i))
  refine ⟨W, fun i => hW_eq i ▸ div_nonneg (Nat.cast_nonneg _) hM_posQ.le, hW_le,
    sum_le_mul_card_of_le hW_le univ, fun S => ?_, ?_⟩
  · rw [show ∑ i ∈ S, μ i = ((∑ i ∈ S, W i : ℕ) : ℚ) / M by
      rw [Nat.cast_sum, sum_div]; exact sum_congr rfl fun i _ => hW_eq i,
      le_div_iff₀ hM_posQ, Nat.ceil_le]
  · set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
    set t : ℕ := (B_W + M - 1) / M
    have hBW : (B_W : ℚ) ≤ (M : ℚ) * t := by
      exact_mod_cast (show B_W ≤ M * t by
        have hmod : M * t + (B_W + M - 1) % M = B_W + M - 1 := Nat.div_add_mod _ _
        have := Nat.mod_lt (B_W + M - 1) hM; omega)
    exact le_of_mul_le_mul_right (by linarith [Nat.le_ceil (θ * M)]) hM_posQ

/-- Internal helper: substitutes `(m + 1) ^ 6 ≤ 64 / η ^ 6` into the explicit Siegel error bound
`1800 * c * (m + 1) ^ 6 * n ^ 2 / (ρ * q)` (`1800 * 64 = 115200`). -/
theorem siegel_eta_bound_le {n k m q : ℕ} {c η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : 0 < q) (hc : 0 ≤ c) (hη : 0 < η)
    (hpow : ((m + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6)) :
    1800 * c * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (q : ℝ)) ≤
      115200 * c * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (q : ℝ)) := by
  have hn : 1 ≤ n := hk.trans hkn
  have hρ_pos : 0 < (k : ℝ) / (n : ℝ) := by positivity
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 hq
  refine (by gcongr : _ ≤ 1800 * c * (64 / η ^ 6) * (n : ℝ) ^ 2 / (((k : ℝ) / n) * q)).trans_eq ?_
  field_simp; ring

theorem rat_weights_johnson_nat {ι : Type*} [Fintype ι] {k m D M : ℕ} (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1) (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / M)
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ) (hroot : (D : ℚ) < m * θ) :
    ∃ W : ι → ℕ, (∀ i, W i ≤ M) ∧ ∑ i : ι, W i ≤ M * Fintype.card ι ∧
      k ≤ (⌈θ * M⌉₊ + M - 1) / M ∧ D < m * ((⌈θ * M⌉₊ + M - 1) / M) ∧
      ∀ S : Finset ι, θ ≤ ∑ i ∈ S, μ i ↔ ⌈θ * M⌉₊ ≤ ∑ i ∈ S, W i := by
  obtain ⟨W, _, hW_le, hW_sum, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact ⟨W, hW_le, hW_sum, Nat.cast_le.1 (hk_le.trans hθ_le_t), by
    exact_mod_cast hroot.trans_le (mul_le_mul_of_nonneg_left hθ_le_t (Nat.cast_nonneg m)),
    hsum_iff⟩

/-- Internal helper: a threshold `θ ≤ n` converted to integer weights with denominator `M`
(`B_W = ⌈θ * M⌉₊`, `t = ⌈B_W / M⌉`) gives a relative radius `(n - t) / n` no larger than any
bound `R` on `1 - θ / n`. -/
theorem ceilDiv_radius_le {n M : ℕ} {θ : ℚ} {R : ℝ} (hM : 0 < M) (hn : 1 ≤ n)
    (hθ_le_t : θ ≤ (((⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℚ))
    (hθ_le_n : (θ : ℝ) ≤ (n : ℝ)) (hθ : 1 - (θ : ℝ) / (n : ℝ) ≤ R) :
    ((n - (⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℝ) / (n : ℝ) ≤ R := by
  set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
  set t : ℕ := (B_W + M - 1) / M
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hBW : B_W ≤ M * n := Nat.ceil_le.2 <|
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hθ_le_n) (Nat.cast_nonneg M)).trans_eq
      (by push_cast; ring)
  have ht_le : t ≤ n := by rw [Nat.div_le_iff_le_mul_add_pred hM]; omega
  rw [Nat.cast_sub ht_le, sub_div, div_self hnR.ne']
  linarith [div_le_div_of_nonneg_right (show (θ : ℝ) ≤ t by exact_mod_cast hθ_le_t) hnR.le]

/-- Internal helper: weights bounded by `1` sum to at most `|ι|` over any finite subset. -/
theorem sum_le_card_of_le_one {ι : Type*} [Fintype ι] {μ : ι → ℚ}
    (hμ_le : ∀ i, μ i ≤ 1) (S : Finset ι) : ∑ i ∈ S, μ i ≤ (Fintype.card ι : ℚ) :=
  (Finset.sum_le_sum fun i _ => hμ_le i).trans <| by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast S.card_le_univ

end Cslib.Code
