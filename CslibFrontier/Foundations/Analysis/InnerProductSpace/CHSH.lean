/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The CHSH inequality for vectors

For vectors `u₀, u₁, v₀, v₁` of norm at most `1` in a (semi-)inner product space,
`Re⟨u₀, v₀⟩ + Re⟨u₀, v₁⟩ + Re⟨u₁, v₀⟩ - Re⟨u₁, v₁⟩ ≤ 2√2` (`chsh_re_inner_le`). The first two terms
are at most `‖v₀ + v₁‖` and the last two at most `‖v₀ - v₁‖` by Cauchy–Schwarz, and the
parallelogram law bounds `‖v₀ + v₁‖ + ‖v₀ - v₁‖` by `2√2`. Applied to the vectors `(A_x ⊗ 1) ψ`
and `(1 ⊗ B_y) ψ` of a quantum strategy, or to the observables themselves in the GNS
pre-inner product space of a state, this is Tsirelson's inequality [Cirel'son][Cirelson1980].

Mathlib's `tsirelson_inequality` (`Mathlib.Algebra.Star.CHSH`) is the operator form of the same
bound, for a CHSH tuple of self-adjoint involutions in an ordered `*`-algebra.

The bound has an exact sum-of-squares form (`chsh_sos`): with `c = 1/√2`,

`‖u₀ - c(v₀ + v₁)‖² + ‖u₁ - c(v₀ - v₁)‖² = ‖u₀‖² + ‖u₁‖² + ‖v₀‖² + ‖v₁‖² - √2 · CHSH`,

where `CHSH` is the left-hand side above. So vectors that nearly attain `2√2` nearly satisfy
`u₀ = c(v₀ + v₁)` and `u₁ = c(v₀ - v₁)` (`chsh_rigidity`): the robust form of the rigidity of the
optimal CHSH strategy.

## Main results

* `chsh_re_inner_le`: the CHSH inequality for vectors of norm at most `1`.
* `chsh_sos`: the sum-of-squares identity.
* `chsh_rigidity`: near-optimal vectors are close to the optimal configuration.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
-/

public section

/-- The **CHSH inequality for vectors**: for vectors `u₀, u₁, v₀, v₁` of norm at most `1` in an
inner product space, `Re⟨u₀,v₀⟩ + Re⟨u₀,v₁⟩ + Re⟨u₁,v₀⟩ - Re⟨u₁,v₁⟩ ≤ 2√2`. -/
theorem chsh_re_inner_le {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    {u₀ u₁ v₀ v₁ : E} (hu₀ : ‖u₀‖ ≤ 1) (hu₁ : ‖u₁‖ ≤ 1) (hv₀ : ‖v₀‖ ≤ 1) (hv₁ : ‖v₁‖ ≤ 1) :
    RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) + RCLike.re (inner 𝕜 u₁ v₀) -
      RCLike.re (inner 𝕜 u₁ v₁) ≤ 2 * √2 := by
  have h₀ : RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) ≤ ‖v₀ + v₁‖ := by
    rw [← map_add, ← inner_add_right]
    exact (re_inner_le_norm u₀ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₀)
  have h₁ : RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁) ≤ ‖v₀ - v₁‖ := by
    rw [← map_sub, ← inner_sub_right]
    exact (re_inner_le_norm u₁ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₁)
  have hab : ‖v₀ + v₁‖ + ‖v₀ - v₁‖ ≤ 2 * √2 := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    nlinarith [parallelogram_law_with_norm 𝕜 v₀ v₁, pow_le_one₀ (n := 2) (norm_nonneg _) hv₀,
      pow_le_one₀ (n := 2) (norm_nonneg _) hv₁, sq_nonneg (‖v₀ + v₁‖ - ‖v₀ - v₁‖)]
  linarith

/-- The **sum-of-squares identity** behind the CHSH inequality: with `c = 1/√2`,
`‖u₀ - c(v₀ + v₁)‖² + ‖u₁ - c(v₀ - v₁)‖²` is
`‖u₀‖² + ‖u₁‖² + ‖v₀‖² + ‖v₁‖² - √2 (Re⟨u₀,v₀⟩ + Re⟨u₀,v₁⟩ + Re⟨u₁,v₀⟩ - Re⟨u₁,v₁⟩)`. -/
theorem chsh_sos {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u₀ u₁ v₀ v₁ : E) :
    ‖u₀ - ((√2)⁻¹ : 𝕜) • (v₀ + v₁)‖ ^ 2 + ‖u₁ - ((√2)⁻¹ : 𝕜) • (v₀ - v₁)‖ ^ 2 =
      ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖v₀‖ ^ 2 + ‖v₁‖ ^ 2 - √2 * (RCLike.re (inner 𝕜 u₀ v₀) +
        RCLike.re (inner 𝕜 u₀ v₁) + RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁)) := by
  have hc : ((√2)⁻¹ : 𝕜) = (((√2)⁻¹ : ℝ) : 𝕜) := by push_cast; rfl
  have h2 : (√2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by rw [inv_pow, Real.sq_sqrt zero_le_two, one_div]
  have hs : 2 * (√2)⁻¹ = √2 := by
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  rw [norm_sub_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), hc, inner_smul_right, inner_smul_right,
    RCLike.re_ofReal_mul, RCLike.re_ofReal_mul, norm_smul, norm_smul, mul_pow, mul_pow,
    RCLike.norm_ofReal, abs_of_pos (by positivity), h2, inner_add_right, inner_sub_right,
    map_add, map_sub]
  have : ‖v₀ + v₁‖ ^ 2 + ‖v₀ - v₁‖ ^ 2 = 2 * (‖v₀‖ ^ 2 + ‖v₁‖ ^ 2) := by
    nlinarith [parallelogram_law_with_norm 𝕜 v₀ v₁]
  linear_combination (1 / 2 : ℝ) * this - (RCLike.re (inner 𝕜 u₀ v₀) +
    RCLike.re (inner 𝕜 u₀ v₁) + RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁)) * hs

/-- **Robust rigidity of CHSH for vectors**: vectors of norm at most `1` whose CHSH expression is
at least `2√2 - η` satisfy `‖u₀ - c(v₀ + v₁)‖² + ‖u₁ - c(v₀ - v₁)‖² + (4 - ∑ norms²) ≤ √2 η`,
with `c = 1/√2`. -/
theorem chsh_rigidity {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {u₀ u₁ v₀ v₁ : E} {η : ℝ}
    (h : 2 * √2 - η ≤ RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) +
      RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁)) :
    ‖u₀ - ((√2)⁻¹ : 𝕜) • (v₀ + v₁)‖ ^ 2 + ‖u₁ - ((√2)⁻¹ : 𝕜) • (v₀ - v₁)‖ ^ 2 +
      (4 - (‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖v₀‖ ^ 2 + ‖v₁‖ ^ 2)) ≤ √2 * η := by
  rw [chsh_sos]
  have h2 : √2 * (2 * √2) = 4 := by
    rw [← mul_assoc, mul_comm √2 2, mul_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
  nlinarith [Real.sqrt_nonneg 2]
