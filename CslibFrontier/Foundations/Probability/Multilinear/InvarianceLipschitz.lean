/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Invariance
public import Mathlib.Topology.EMetricSpace.Lipschitz
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.Probability.SmoothTests

/-!
# The Basic Invariance Principle for Lipschitz test functions

**Corollary 11.68** of [O'Donnell][ODonnell2014]: in the setting of Corollary 11.67
(`abs_integral_comp_multilinearEval_sub_le_of_influence_le`: `F` of degree at most `k` with
`Var[F] ≤ 1` and all influences at most `ε`, and independent variables whose laws satisfy
Hypothesis 11.65), if `ψ : ℝ → ℝ` is merely `K`-Lipschitz, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ 9 K · 2ᵏ · ε^(1/4)`.

The proof applies the general transfer `abs_integral_comp_sub_le_of_lipschitzWith` of
`CslibFrontier.Foundations.Probability.SmoothTests` at `m = 4`: it turns any `C⁴` comparison
`|E[φ(X)] - E[φ(Y)]| ≤ C τ⁴` (for `|φ⁗| ≤ C`) into `|E[ψ(X)] - E[ψ(Y)]| ≤ 16 K τ`, by smoothing
`ψ` with the four-fold moving average. With the bound `C / 12 · k · 9ᵏ · ε` of Corollary 11.67
one may take `τ = 9/16 · 2ᵏ · ε^(1/4)`, since `k 9ᵏ ε / 12 ≤ τ⁴` by `k 9ᵏ ≤ 16ᵏ`.

Lipschitz tests are also stable under `L²` perturbations, `|E[ψ(X)] - E[ψ(Y)]| ≤ K ‖X - Y‖₂`
(`LipschitzWith.abs_integral_comp_sub_le_sqrt`), so
by the orthonormality of monomials two polynomials `F` and `G` in variables satisfying
Hypothesis 11.65 give `|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K ‖F̂ - Ĝ‖₂`. This is the tail estimate in the
proof of Corollary 11.69.

## Main results

* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith`:
  Corollary 11.68.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_sqrt`:
  `|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K √(∑ S, (F̂(S) - Ĝ(S))²)` under Hypothesis 11.65.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset Real
open scoped NNReal

namespace ProbabilityTheory

/-! ### Corollary 11.68 -/

/-- `k 9ᵏ ≤ 16ᵏ`, so that `(k 9ᵏ)^(1/4) ≤ 2ᵏ`. -/
private theorem mul_nine_pow_le (k : ℕ) : k * 9 ^ k ≤ 16 ^ k := by
  rcases k with _ | _ | k
  · simp
  · norm_num
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ 9, pow_succ 16]
    have h9 : 0 ≤ 9 ^ (k + 2) := Nat.zero_le _
    nlinarith

/-- The arithmetic of Corollary 11.68: `k 9ᵏ ε / 12 ≤ (9/16 · 2ᵏ · ε^(1/4))⁴`. -/
private theorem mul_nine_pow_mul_div_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    k * 9 ^ k * ε / 12 ≤ (9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ)) ^ 4 := by
  have hk : (k : ℝ) * 9 ^ k ≤ 16 ^ k := by exact_mod_cast mul_nine_pow_le k
  have he : (ε ^ (1 / 4 : ℝ)) ^ 4 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε]
    norm_num
  rw [mul_pow, mul_pow, he, ← pow_mul, mul_comm k 4, pow_mul]
  have h16 : (0 : ℝ) ≤ 16 ^ k * ε := by positivity
  norm_num
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ ν : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-- **Corollary 11.68** [O'Donnell, Corollary 11.68][ODonnell2014]: in the setting of the Basic
Invariance Principle `abs_integral_comp_multilinearEval_sub_le`, if moreover
`Var[F] = ∑_{S ≠ ∅} F̂(S) ^ 2 ≤ 1` and `Inf_t[F] ≤ ε` for all `t`, then for every `K`-Lipschitz
`ψ : ℝ → ℝ`, `|E[ψ(F(x))] - E[ψ(F(y))]| ≤ 9 K · 2ᵏ · ε^(1/4)`. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) {ψ : ℝ → ℝ} {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
  refine (abs_integral_comp_sub_le_of_lipschitzWith (X := multilinearEval c)
    (Y := multilinearEval c) (m := 4) four_ne_zero (τ := 9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ))
    (by positivity) (fun φ C hφ hC => ⟨integrable_comp_multilinearEval μ
      (fun i => (hμ i).memLp_four) c (n := 3) le_rfl hφ hC, integrable_comp_multilinearEval ν
      (fun i => (hν i).memLp_four) c (n := 3) le_rfl hφ hC, ?_⟩) hψ).trans_eq (by norm_num; ring)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (abs_integral_comp_multilinearEval_sub_le_of_influence_le μ ν hμ hν hc hvar hε0 hε hφ
    hC).trans ?_
  calc C / 12 * k * 9 ^ k * ε = C * (k * 9 ^ k * ε / 12) := by ring
    _ ≤ C * (9 / 16 * 2 ^ k * ε ^ (1 / 4 : ℝ)) ^ 4 := by
        gcongr
        exact mul_nine_pow_mul_div_le k hε0

/-! ### Lipschitz tests of nearby polynomials -/

omit [DecidableEq ι] in
/-- For variables whose laws satisfy Hypothesis 11.65 and `K`-Lipschitz `ψ`,
`|E[ψ(F(z))] - E[ψ(G(z))]| ≤ K ‖F - G‖₂ = K √(∑ S, (F̂(S) - Ĝ(S))²)`, by Cauchy–Schwarz and the
orthonormality of monomials [O'Donnell, Remark 11.64][ODonnell2014]. This is the tail estimate
in the proof of [O'Donnell, Corollary 11.69][ODonnell2014]. -/
theorem abs_integral_comp_multilinearEval_sub_le_sqrt (hμ : ∀ i, HasInvarianceMoments (μ i))
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ) (c d : Finset ι → ℝ) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval d z) ∂Measure.pi μ| ≤
      K * √(∑ S, (c S - d S) ^ 2) := by
  have hL (e : Finset ι → ℝ) : MemLp (multilinearEval e) 2 (Measure.pi μ) := by
    have h := memLp_multilinearEval μ (p := 2) two_ne_zero
      (fun i => (hμ i).memLp_four.mono_exponent (by norm_num)) e
    exact_mod_cast h
  have hD (z : ι → ℝ) : multilinearEval c z - multilinearEval d z =
      multilinearEval (c - d) z := by
    simp only [multilinearEval_def, Pi.sub_apply, sub_mul, sum_sub_distrib]
  refine (hψ.abs_integral_comp_sub_le_sqrt (hL c) (hL d)).trans_eq ?_
  simp_rw [hD]
  rw [integral_multilinearEval_sq_of_hasInvarianceMoments μ hμ]
  simp

end ProbabilityTheory
