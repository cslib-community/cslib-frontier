/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import CslibFrontier.Foundations.Analysis.Asymptotics.PolyErr
import CslibFrontier.Foundations.Analysis.InnerProductSpace.CHSH

/-!
# Robust rigidity of CHSH

Tsirelson's inequality bounds the CHSH expression `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` of self-adjoint
contractions by `2√2` in every state (`Cslib.Quantum.AlgState.re_chsh_le`). Observables that nearly
attain the bound are rigid. For exact attainment this is
[Summers and Werner, Theorem 2.1][SummersWerner1987]; the robust form is
[McKague, Yang and Scarani, Theorem 2][McKagueYangScarani2012] (arXiv:1203.2976v1, equations (11)
and (13)–(14), PDF p. 3, derived in the Supplementary Information, PDF pp. 5–6). With
`c = 1/√2`, Alice's observables are determined by Bob's, `A₀ ≈ c(B₀ + B₁)` and
`A₁ ≈ c(B₀ - B₁)`, all four observables are nearly involutions, and Alice's observables nearly
anticommute,

`‖A₀A₁ + A₁A₀‖_φ ≤ (4 + 2√2) √(√2 η)`

when the CHSH expression is at least `2√2 - η` (`Cslib.Quantum.AlgState.chsh_anticomm`).
McKague, Yang and Scarani assume Hermitian unitary (`±1`-eigenvalue) observables on a bipartite
state and obtain `‖{A₀, A₁} ψ‖ ≤ 4 √(√2 ε)`. The statement here holds for arbitrary self-adjoint
contractions in any star-ordered algebra with a continuous functional calculus, so it covers
non-projective measurements; the constant `(4 + 2√2) √(√2 η)` comes from the sum-of-squares
derivation below rather than from the paper. Anticommuting `±1` observables are the Pauli `X`
and `Z` of a qubit; this is the algebraic core of the self-test of the EPR pair.

The proof is the sum-of-squares identity of the CHSH inequality (`chsh_sos`), read in the GNS
pre-inner product space of the state (`Cslib.Quantum.AlgState.chsh_rigidity`), and then the
approximation calculus of `Cslib.Quantum.AlgState.Approx`:
`A₀A₁ ≈ A₀X₁ = X₁A₀ ≈ X₁X₀` with `X₀ = c(B₀ + B₁)` and `X₁ = c(B₀ - B₁)`, because Alice's
observables commute with Bob's, and `X₁X₀ + X₀X₁ = B₀² - B₁² ≈ 0`. Only the near-anticommutation
step uses commutation; the observables may come from arbitrary, non-projective measurements.

## Main results

* `Cslib.Quantum.AlgState.chsh_rigidity`: the sum-of-squares bound for near-optimal observables.
* `Cslib.Quantum.AlgState.chsh_approx`: Alice's observables are close to Bob's combinations, and
  Bob's observables are near involutions.
* `Cslib.Quantum.AlgState.chsh_anticomm`: Alice's observables nearly anticommute.

## References

* [S. J. Summers and R. Werner, *Maximal violation of Bell's inequalities is generic in quantum
  field theory*][SummersWerner1987]
* [M. McKague, T. H. Yang and V. Scarani, *Robust self-testing of the
  singlet*][McKagueYangScarani2012]
-/

@[expose] public section

namespace Cslib.Quantum.AlgState

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- The CHSH expression `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁`. -/
def chshExpr (A₀ A₁ B₀ B₁ : A) : A :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- **Robust rigidity of CHSH**: if self-adjoint contractions reach `2√2 - η` in the state `φ`,
then with `c = 1/√2`,
`‖A₀ - c(B₀ + B₁)‖²_φ + ‖A₁ - c(B₀ - B₁)‖²_φ + (4 - ∑ ‖·‖²_φ) ≤ √2 η`. -/
theorem chsh_rigidity (φ : AlgState A) {A₀ A₁ B₀ B₁ : A} (hA₀ : IsSelfAdjoint A₀)
    (hA₁ : IsSelfAdjoint A₁) {η : ℝ} (h : 2 * √2 - η ≤ (φ (chshExpr A₀ A₁ B₀ B₁)).re) :
    φ.norm (A₀ - ((√2)⁻¹ : ℂ) • (B₀ + B₁)) ^ 2 + φ.norm (A₁ - ((√2)⁻¹ : ℂ) • (B₀ - B₁)) ^ 2 +
      (4 - (φ.norm A₀ ^ 2 + φ.norm A₁ ^ 2 + φ.norm B₀ ^ 2 + φ.norm B₁ ^ 2)) ≤ √2 * η := by
  have hv := _root_.chsh_rigidity (𝕜 := ℂ) (u₀ := φ.toPreGNS A₀) (u₁ := φ.toPreGNS A₁)
    (v₀ := φ.toPreGNS B₀) (v₁ := φ.toPreGNS B₁) (η := η) (by
      simp only [inner_toPreGNS, hA₀.star_eq, hA₁.star_eq, RCLike.re_to_complex]
      simpa only [chshExpr, map_add, map_sub, Complex.add_re, Complex.sub_re] using h)
  simp only [norm, map_sub, map_smul, map_add]
  exact hv

variable [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- A self-adjoint contraction `B` is as close to an involution as its state norm is to `1`:
`‖1 - B²‖²_φ ≤ 1 - ‖B‖²_φ`. -/
theorem norm_one_sub_mul_self_sq_le (φ : AlgState A) {B : A} (hB : IsSelfAdjoint B)
    (hB' : star B * B ≤ 1) : φ.norm (1 - B * B) ^ 2 ≤ 1 - φ.norm B ^ 2 := by
  rw [hB.star_eq] at hB'
  have h0 : 0 ≤ 1 - B * B := sub_nonneg.mpr hB'
  have h1 : 1 - B * B ≤ 1 := by
    have := star_mul_self_nonneg B
    rw [hB.star_eq] at this
    exact sub_le_self _ this
  have hsq := mul_self_le_self_of_nonneg_of_le_one h0 h1
  rw [norm_sq, norm_sq, h0.isSelfAdjoint.star_eq, hB.star_eq]
  have := φ.re_apply_mono hsq
  simpa [map_sub] using this

/-- **Robust rigidity of CHSH**, as approximations: if self-adjoint contractions reach
`2√2 - η`, then with `δ = √(√2 η)`, `A₀ ≈ c(B₀ + B₁)`, `A₁ ≈ c(B₀ - B₁)` and `B_y² ≈ 1`, all
`δ`-close in the state. -/
theorem chsh_approx (φ : AlgState A) {A₀ A₁ B₀ B₁ : A} (hA₀ : IsSelfAdjoint A₀)
    (hA₁ : IsSelfAdjoint A₁) (hB₀ : IsSelfAdjoint B₀) (hB₁ : IsSelfAdjoint B₁)
    (hA₀' : star A₀ * A₀ ≤ 1) (hA₁' : star A₁ * A₁ ≤ 1) (hB₀' : star B₀ * B₀ ≤ 1)
    (hB₁' : star B₁ * B₁ ≤ 1) {η : ℝ} (h : 2 * √2 - η ≤ (φ (chshExpr A₀ A₁ B₀ B₁)).re) :
    (A₀ ≈[φ; √(√2 * η)] ((√2)⁻¹ : ℂ) • (B₀ + B₁)) ∧
      (A₁ ≈[φ; √(√2 * η)] ((√2)⁻¹ : ℂ) • (B₀ - B₁)) ∧
      (1 - B₀ * B₀ ≈[φ; √(√2 * η)] 0) ∧ (1 - B₁ * B₁ ≈[φ; √(√2 * η)] 0) := by
  have hr := φ.chsh_rigidity hA₀ hA₁ h
  have n₀ := φ.norm_le_one hA₀'
  have n₁ := φ.norm_le_one hA₁'
  have m₀ := φ.norm_le_one hB₀'
  have m₁ := φ.norm_le_one hB₁'
  have p₀ := φ.norm_nonneg A₀
  have p₁ := φ.norm_nonneg A₁
  have q₀ := φ.norm_nonneg B₀
  have q₁ := φ.norm_nonneg B₁
  have s₀ := sq_nonneg (φ.norm (A₀ - ((√2)⁻¹ : ℂ) • (B₀ + B₁)))
  have s₁ := sq_nonneg (φ.norm (A₁ - ((√2)⁻¹ : ℂ) • (B₀ - B₁)))
  have b₀ := φ.norm_one_sub_mul_self_sq_le hB₀ hB₀'
  have b₁ := φ.norm_one_sub_mul_self_sq_le hB₁ hB₁'
  have key : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ √2 * η → x ≤ √(√2 * η) := fun x hx hle =>
    Real.le_sqrt_of_sq_le hle
  refine ⟨key _ (φ.norm_nonneg _) (by nlinarith), key _ (φ.norm_nonneg _) (by nlinarith),
    ?_, ?_⟩
  · rw [Approx, sub_zero]
    exact key _ (φ.norm_nonneg _) (by nlinarith)
  · rw [Approx, sub_zero]
    exact key _ (φ.norm_nonneg _) (by nlinarith)

omit [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] in
/-- Left multiplication by `c(B₀ ± B₁)` with `c = 1/√2` and contractions `B_y` stretches the state
norm by at most `√2`. -/
theorem norm_smul_add_mul_le (φ : AlgState A) {B₀ B₁ : A} (hB₀' : star B₀ * B₀ ≤ 1)
    (hB₁' : star B₁ * B₁ ≤ 1) (s : ℂ) (hs : ‖s‖ = 1) (y : A) :
    φ.norm ((((√2)⁻¹ : ℂ) • (B₀ + s • B₁)) * y) ≤ √2 * φ.norm y := by
  rw [smul_mul_assoc, norm_smul, add_mul, smul_mul_assoc]
  have h₀ := φ.norm_mul_le_of_star_mul_self_le_one hB₀' y
  have h₁ := φ.norm_mul_le_of_star_mul_self_le_one hB₁' y
  have hadd := φ.norm_add_le (B₀ * y) (s • (B₁ * y))
  rw [norm_smul, hs, one_mul] at hadd
  have hc : ‖((√2)⁻¹ : ℂ)‖ = (√2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hc]
  have h2 : (√2)⁻¹ * 2 = √2 := by
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  calc (√2)⁻¹ * φ.norm (B₀ * y + s • (B₁ * y)) ≤ (√2)⁻¹ * (φ.norm y + φ.norm y) :=
        mul_le_mul_of_nonneg_left (hadd.trans (add_le_add h₀ h₁)) (by positivity)
    _ = √2 * φ.norm y := by rw [← two_mul, ← mul_assoc, h2]

/-- **Near-optimal CHSH observables anticommute**: if self-adjoint contractions with Alice's
observables commuting with Bob's reach `2√2 - η` in the state `φ`, then
`‖A₀A₁ + A₁A₀‖_φ ≤ (4 + 2√2) √(√2 η)`. -/
theorem chsh_anticomm (φ : AlgState A) {A₀ A₁ B₀ B₁ : A} (hA₀ : IsSelfAdjoint A₀)
    (hA₁ : IsSelfAdjoint A₁) (hB₀ : IsSelfAdjoint B₀) (hB₁ : IsSelfAdjoint B₁)
    (hA₀' : star A₀ * A₀ ≤ 1) (hA₁' : star A₁ * A₁ ≤ 1) (hB₀' : star B₀ * B₀ ≤ 1)
    (hB₁' : star B₁ * B₁ ≤ 1) (h₀₀ : Commute A₀ B₀) (h₀₁ : Commute A₀ B₁)
    (h₁₀ : Commute A₁ B₀) (h₁₁ : Commute A₁ B₁) {η : ℝ}
    (h : 2 * √2 - η ≤ (φ (chshExpr A₀ A₁ B₀ B₁)).re) :
    A₀ * A₁ + A₁ * A₀ ≈[φ; (4 + 2 * √2) * √(√2 * η)] 0 := by
  obtain ⟨e₀, e₁, b₀, b₁⟩ := φ.chsh_approx hA₀ hA₁ hB₀ hB₁ hA₀' hA₁' hB₀' hB₁' h
  have hcc : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
    norm_num
  set δ := √(√2 * η)
  set c : ℂ := (√2)⁻¹
  set X₀ := c • (B₀ + B₁)
  set X₁ := c • (B₀ - B₁)
  have hX₀ : ∀ y, φ.norm (X₀ * y) ≤ √2 * φ.norm y := fun y => by
    have := φ.norm_smul_add_mul_le hB₀' hB₁' 1 (by simp) y
    rwa [one_smul] at this
  have hX₁ : ∀ y, φ.norm (X₁ * y) ≤ √2 * φ.norm y := fun y => by
    have := φ.norm_smul_add_mul_le hB₀' hB₁' (-1) (by simp) y
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have c₀ : Commute A₀ X₁ := ((h₀₀.sub_right h₀₁).smul_right c)
  have c₁ : Commute A₁ X₀ := ((h₁₀.add_right h₁₁).smul_right c)
  have hs : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have t₀ : A₀ * A₁ ≈[φ; δ + √2 * δ] X₁ * X₀ :=
    calc A₀ * A₁ ≈[φ; δ] A₀ * X₁ := e₁.mul_left hA₀'
      _ = X₁ * A₀ := c₀.eq
      _ ≈[φ; √2 * δ] X₁ * X₀ := e₀.mul_left_of_norm_mul_le hs hX₁
  have t₁ : A₁ * A₀ ≈[φ; δ + √2 * δ] X₀ * X₁ :=
    calc A₁ * A₀ ≈[φ; δ] A₁ * X₀ := e₀.mul_left hA₁'
      _ = X₀ * A₁ := c₁.eq
      _ ≈[φ; √2 * δ] X₀ * X₁ := e₁.mul_left_of_norm_mul_le hs hX₀
  have hXX : X₁ * X₀ + X₀ * X₁ = (1 - B₁ * B₁) - (1 - B₀ * B₀) := by
    simp only [X₀, X₁, smul_mul_smul_comm, hcc, ← smul_add]
    rw [show (B₀ - B₁) * (B₀ + B₁) + (B₀ + B₁) * (B₀ - B₁) =
      (2 : ℂ) • ((1 - B₁ * B₁) - (1 - B₀ * B₀)) by rw [two_smul]; noncomm_ring, smul_smul]
    norm_num
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have := (t₀.add t₁).trans (approx_of_eq hXX le_rfl |>.trans (b₁.sub b₀))
  refine (by simpa using this : A₀ * A₁ + A₁ * A₀ ≈[φ; _] 0).mono (le_of_eq ?_)
  ring

end Cslib.Quantum.AlgState
