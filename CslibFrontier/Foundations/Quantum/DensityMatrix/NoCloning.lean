/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace

/-!
# Mixed-state no-cloning under Kraus channels

A completely positive trace-preserving (CPTP) map from `ℂ^ι` to `ℂ^{ι'}` given in Kraus form by a
finite family `{Kⱼ}_{j ∈ s}` with `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1` acts on density matrices by
`ρ ↦ ∑_{j ∈ s} Kⱼ ρ Kⱼᴴ`. Using the finite-dimensional Uhlmann purification characterization of
`Cslib.Quantum.rootFidelity`
(`CslibFrontier/Foundations/Quantum/DensityMatrix/PurificationOverlap.lean`), this file
establishes:

* **Extremal characterizations of root fidelity**
  (`Cslib.Quantum.rootFidelity_eq_zero_iff_mul_eq_zero`,
  `Cslib.Quantum.rootFidelity_eq_one_iff_eq`): for positive semidefinite `ρ, σ`,
  `rootFidelity ρ σ = 0` iff `ρ * σ = 0` (orthogonal supports), and for density matrices `ρ, σ`,
  `0 ≤ rootFidelity ρ σ ≤ 1` with `rootFidelity ρ σ = 1` iff `ρ = σ`.
* **Multiplicativity under Kronecker products** (`Cslib.Quantum.rootFidelity_kronecker`): for
  positive semidefinite matrices, `rootFidelity (ρ₁ ⊗ₖ ρ₂) (σ₁ ⊗ₖ σ₂) =
  rootFidelity ρ₁ σ₁ * rootFidelity ρ₂ σ₂`.
* **Monotonicity under CPTP Kraus channels** (`Cslib.Quantum.rootFidelity_le_of_kraus`): for
  positive semidefinite `ρ, σ` and `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1`, Stinespring dilation into `ι' × (s × ι)`
  preserves purification inner products and yields
  `rootFidelity ρ σ ≤ rootFidelity (∑_{j ∈ s} Kⱼ ρ Kⱼᴴ) (∑_{j ∈ s} Kⱼ σ Kⱼᴴ)`.
* **Mixed-state CPTP no-cloning** (`Cslib.Quantum.mul_eq_zero_or_eq_of_kraus_clone`,
  `Cslib.Quantum.not_exists_kraus_clone`): if a CPTP Kraus channel maps two density matrices `ρ, σ`
  to their two-copy product states `ρ ⊗ₖ ρ` and `σ ⊗ₖ σ`, then
  `rootFidelity ρ σ ≤ (rootFidelity ρ σ)²`, forcing `rootFidelity ρ σ ∈ {0, 1}` and hence
  `ρ * σ = 0 ∨ ρ = σ`. Consequently, for `|ι| ≥ 2`, no CPTP Kraus channel clones every density
  matrix on `ℂ^ι`.

Scope: this file treats **mixed-state cloning** `ρ ↦ ρ ⊗ₖ ρ` (two independent copies). The weaker
notion of **broadcasting** (`Tr_1 ℰ(ρ) = Tr_2 ℰ(ρ) = ρ`, allowing correlations between the output
registers, which is possible iff `ρ * σ = σ * ρ`) is not formalized here. All results are original
formulations over the library's matrix and fidelity API.

## Main results

* `Cslib.Quantum.rootFidelity_nonneg`, `Cslib.Quantum.rootFidelity_le_one`: `rootFidelity` of
  density matrices lies in `[0, 1]`.
* `Cslib.Quantum.rootFidelity_eq_zero_iff_mul_eq_zero`: `rootFidelity ρ σ = 0 ↔ ρ * σ = 0` for
  positive semidefinite `ρ, σ`.
* `Cslib.Quantum.rootFidelity_eq_one_iff_eq`: `rootFidelity ρ σ = 1 ↔ ρ = σ` for density matrices.
* `Cslib.Quantum.rootFidelity_kronecker`: multiplicativity of `rootFidelity` under `⊗ₖ`.
* `Cslib.Quantum.rootFidelity_le_of_kraus`: monotonicity of `rootFidelity` under Kraus channels.
* `Cslib.Quantum.mul_eq_zero_or_eq_of_kraus_clone`: a CPTP Kraus channel cloning two density
  matrices `ρ, σ` forces `ρ * σ = 0 ∨ ρ = σ`.
* `Cslib.Quantum.not_exists_kraus_clone`: if `|ι| ≥ 2`, no CPTP Kraus channel clones every density
  matrix on `ℂ^ι`.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

/-! ### Canonical square-root purifications and extremal root fidelity -/

section Extremal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def purifySqrt (ρ : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun ⟨i, k⟩ => CFC.sqrt ρ i k

private theorem coefficients_purifySqrt (ρ : Matrix ι ι ℂ) :
    coefficients (purifySqrt ρ) = CFC.sqrt ρ := by
  ext i k
  rfl

private theorem partialTraceRight_pureState_purifySqrt {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    partialTraceRight (pureState (purifySqrt ρ)) = ρ := by
  rw [partialTraceRight_pureState_eq_coefficients, coefficients_purifySqrt,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self _ hρ.nonneg

private theorem norm_purifySqrt {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    ‖purifySqrt ρ‖ = 1 := by
  have ht : (pureState (purifySqrt ρ)).trace = 1 := by
    rw [← trace_partialTraceRight, partialTraceRight_pureState_purifySqrt hρ.posSemidef,
      hρ.trace_eq_one]
  rw [trace_pureState] at ht
  have hsq : ‖purifySqrt ρ‖ ^ 2 = 1 ^ 2 := by
    rw [one_pow]
    exact_mod_cast ht
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

private theorem traceNorm_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : A.traceNorm = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; unfold Matrix.traceNorm; simp [CFC.sqrt_zero]⟩
  let B := CFC.sqrt (Aᴴ * A)
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have htr : B.trace = 0 :=
    Complex.ext h (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm
  have hB0 : B = 0 := by
    simpa only [Matrix.mul_one] using
      (hB.trace_mul_eq_zero_iff PosSemidef.one).mp (by simpa only [Matrix.mul_one] using htr)
  have hAA : Aᴴ * A = 0 := by
    rw [← CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg]
    change B * B = 0
    rw [hB0, Matrix.mul_zero]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hAA, trace_zero])

/-- Root fidelity is nonnegative for arbitrary square matrices. -/
theorem rootFidelity_nonneg (ρ σ : Matrix ι ι ℂ) : 0 ≤ rootFidelity ρ σ := by
  unfold rootFidelity Matrix.traceNorm
  exact (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).trace_nonneg).1

/-- Root fidelity of two density matrices is at most `1`. -/
theorem rootFidelity_le_one {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    rootFidelity ρ σ ≤ 1 := by
  obtain ⟨U, _, hsq⟩ := exists_localUnitary_norm_sub_sq_eq
    (purifySqrt ρ) (purifySqrt σ) (norm_purifySqrt hρ) (norm_purifySqrt hσ)
  rw [partialTraceRight_pureState_purifySqrt hρ.posSemidef,
    partialTraceRight_pureState_purifySqrt hσ.posSemidef] at hsq
  have hnn : 0 ≤ ‖WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ (purifySqrt ρ).ofLp) -
      purifySqrt σ‖ ^ 2 := sq_nonneg _
  linarith

/-- Two positive semidefinite matrices have zero root fidelity if and only if their matrix product
is zero (equivalently, their supports are orthogonal). -/
theorem rootFidelity_eq_zero_iff_mul_eq_zero {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    rootFidelity ρ σ = 0 ↔ ρ * σ = 0 := by
  let P := CFC.sqrt ρ
  let Q := CFC.sqrt σ
  have hP : Pᴴ = P := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq
  have hQ : Qᴴ = Q := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).isHermitian.eq
  have hP2 : P * P = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hQ2 : Q * Q = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  unfold rootFidelity
  rw [traceNorm_eq_zero_iff]
  refine ⟨fun hPQ => ?_, fun hρσ => ?_⟩
  · calc
      ρ * σ = P * (P * Q) * Q := by simp only [← hP2, ← hQ2, Matrix.mul_assoc]
      _ = 0 := by rw [hPQ, Matrix.mul_zero, Matrix.zero_mul]
  · apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    have htr : ((P * Q)ᴴ * (P * Q)).trace = (ρ * σ).trace := by
      rw [conjTranspose_mul, hP, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc P P Q, hP2,
        trace_mul_comm Q, Matrix.mul_assoc, hQ2]
    rw [htr, hρσ, trace_zero]

/-- Two density matrices have root fidelity `1` if and only if they are equal. -/
theorem rootFidelity_eq_one_iff_eq {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    rootFidelity ρ σ = 1 ↔ ρ = σ := by
  refine ⟨fun hf => ?_, fun h => ?_⟩
  · obtain ⟨U, hU, hsq⟩ := exists_localUnitary_norm_sub_sq_eq
      (purifySqrt ρ) (purifySqrt σ) (norm_purifySqrt hρ) (norm_purifySqrt hσ)
    rw [partialTraceRight_pureState_purifySqrt hρ.posSemidef,
      partialTraceRight_pureState_purifySqrt hσ.posSemidef, hf, sub_self, mul_zero] at hsq
    have heq : WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ (purifySqrt ρ).ofLp) =
        purifySqrt σ :=
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    have hUU : Uᵀ * Uᵀᴴ = 1 :=
      (mem_unitaryGroup_iff).mp (transpose_mem_unitaryGroup_iff.mpr hU)
    have hpt := congrArg (fun x => partialTraceRight (pureState x)) heq
    rw [partialTraceRight_pureState_eq_coefficients, coefficients_one_kronecker,
      conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul,
      ← partialTraceRight_pureState_eq_coefficients,
      partialTraceRight_pureState_purifySqrt hρ.posSemidef,
      partialTraceRight_pureState_purifySqrt hσ.posSemidef] at hpt
    exact hpt
  · subst h
    unfold rootFidelity Matrix.traceNorm
    have hsqrt : CFC.sqrt ((CFC.sqrt ρ * CFC.sqrt ρ)ᴴ * (CFC.sqrt ρ * CFC.sqrt ρ)) = ρ := by
      rw [CFC.sqrt_mul_sqrt_self _ hρ.posSemidef.nonneg]
      apply CFC.sqrt_unique _ hρ.posSemidef.nonneg
      rw [hρ.posSemidef.isHermitian.eq]
    rw [hsqrt, hρ.trace_eq_one, Complex.one_re]

end Extremal

/-! ### Multiplicativity under Kronecker products and monotonicity under Kraus channels -/

section KroneckerAndKraus

private theorem posSemidef_kronecker {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂]
    {A : Matrix ι₁ ι₁ ℂ} {B : Matrix ι₂ ι₂ ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι₁
  let _ := Fintype.ofFinite ι₂
  let R₁ := CFC.sqrt A
  let R₂ := CFC.sqrt B
  have hR₁ : R₁ᴴ = R₁ := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hR₂ : R₂ᴴ = R₂ := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hfac : (R₁ ⊗ₖ R₂)ᴴ * (R₁ ⊗ₖ R₂) = A ⊗ₖ B := by
    rw [conjTranspose_kronecker, hR₁, hR₂, ← mul_kronecker_mul,
      CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]
  exact hfac ▸ posSemidef_conjTranspose_mul_self (R₁ ⊗ₖ R₂)

open Classical in
private theorem sqrt_kronecker {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {A : Matrix ι₁ ι₁ ℂ} {B : Matrix ι₂ ι₂ ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply CFC.sqrt_unique _ (posSemidef_kronecker
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
  rw [← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self _ hA.nonneg,
    CFC.sqrt_mul_sqrt_self _ hB.nonneg]

private theorem traceNorm_kronecker_square {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) :
    (A ⊗ₖ B).traceNorm = A.traceNorm * B.traceNorm := by
  unfold Matrix.traceNorm
  have hAB : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = (Aᴴ * A) ⊗ₖ (Bᴴ * B) := by
    rw [conjTranspose_kronecker, mul_kronecker_mul]
  rw [hAB, sqrt_kronecker (posSemidef_conjTranspose_mul_self A)
    (posSemidef_conjTranspose_mul_self B), trace_kronecker]
  have h₁ := (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg).2
  have h₂ := (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Bᴴ * B))).trace_nonneg).2
  rw [Complex.mul_re, ← h₁, ← h₂, mul_zero, sub_zero]

/-- **Multiplicativity of root fidelity** under Kronecker products of positive semidefinite
matrices. -/
theorem rootFidelity_kronecker {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] {ρ₁ σ₁ : Matrix ι₁ ι₁ ℂ} {ρ₂ σ₂ : Matrix ι₂ ι₂ ℂ}
    (hρ₁ : ρ₁.PosSemidef) (hσ₁ : σ₁.PosSemidef)
    (hρ₂ : ρ₂.PosSemidef) (hσ₂ : σ₂.PosSemidef) :
    rootFidelity (ρ₁ ⊗ₖ ρ₂) (σ₁ ⊗ₖ σ₂) = rootFidelity ρ₁ σ₁ * rootFidelity ρ₂ σ₂ := by
  unfold rootFidelity
  rw [sqrt_kronecker hρ₁ hρ₂, sqrt_kronecker hσ₁ hσ₂, ← mul_kronecker_mul,
    traceNorm_kronecker_square]

/-- **Monotonicity of root fidelity under CPTP Kraus channels**: for positive semidefinite
matrices `ρ, σ` and a Kraus family `{Kⱼ}_{j ∈ s}` with `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1`, applying the
channel `τ ↦ ∑_{j ∈ s} Kⱼ τ Kⱼᴴ` cannot decrease root fidelity. -/
theorem rootFidelity_le_of_kraus {ι ι' α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (s : Finset α) (K : α → Matrix ι' ι ℂ)
    (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1) {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    rootFidelity ρ σ ≤
      rootFidelity (∑ j ∈ s, K j * ρ * (K j)ᴴ) (∑ j ∈ s, K j * σ * (K j)ᴴ) := by
  classical
  obtain ⟨U, hU, hoverlap⟩ :=
    exists_localUnitary_inner_re_eq_rootFidelity (purifySqrt ρ) (purifySqrt σ)
  rw [partialTraceRight_pureState_purifySqrt hρ,
    partialTraceRight_pureState_purifySqrt hσ] at hoverlap
  let ψ' : EuclideanSpace ℂ (ι × ι) :=
    WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ (purifySqrt ρ).ofLp)
  let φ : EuclideanSpace ℂ (ι × ι) := purifySqrt σ
  have hψ'_pt : partialTraceRight (pureState ψ') = ρ := by
    have hUU : Uᵀ * Uᵀᴴ = 1 :=
      (mem_unitaryGroup_iff).mp (transpose_mem_unitaryGroup_iff.mpr hU)
    rw [partialTraceRight_pureState_eq_coefficients, coefficients_one_kronecker,
      conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul,
      ← partialTraceRight_pureState_eq_coefficients, partialTraceRight_pureState_purifySqrt hρ]
  let W : Matrix (ι' × (↥s × ι)) (ι × ι) ℂ :=
    fun ⟨p, ⟨j, k⟩⟩ ⟨i, k'⟩ => if k = k' then K j.val p i else 0
  have hW_mulVec (ξ : EuclideanSpace ℂ (ι × ι)) (p : ι') (j : ↥s) (k : ι) :
      (W *ᵥ ξ.ofLp) (p, (j, k)) = ∑ i : ι, K j.val p i * ξ.ofLp (i, k) := by
    simp only [W, mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, zero_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [Ne.symm hk']) (by simp)]
    simp
  have hW : Wᴴ * W = 1 := by
    ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
    have hlhs : (Wᴴ * W) (i₁, k₁) (i₂, k₂) =
        ∑ p : ι', ∑ j : ↥s, ∑ k : ι,
          star (if k = k₁ then K j.val p i₁ else 0) * (if k = k₂ then K j.val p i₂ else 0) := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => rfl
    rw [hlhs, Matrix.one_apply]
    by_cases hk : k₁ = k₂
    · subst hk
      have hsum : (∑ p : ι', ∑ j : ↥s, ∑ k : ι,
          star (if k = k₁ then K j.val p i₁ else 0) * (if k = k₁ then K j.val p i₂ else 0)) =
          ∑ j ∈ s, ((K j)ᴴ * K j) i₁ i₂ := by
        simp only [apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
        rw [Finset.sum_comm, ← Finset.sum_coe_sort s]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mul_apply, conjTranspose_apply]
      rw [hsum, ← Matrix.sum_apply, hK, Matrix.one_apply]
      simp
    · rw [ite_eq_right_iff.mpr fun h' => absurd (Prod.mk.inj h').2 hk]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun j _ =>
        Finset.sum_eq_zero fun k _ => ?_
      by_cases hk₁ : k = k₁
      · subst hk₁; simp [hk]
      · simp [hk₁]
  have hW_pt (ξ : EuclideanSpace ℂ (ι × ι)) :
      partialTraceRight (pureState (W.toEuclideanLin ξ)) =
        ∑ j ∈ s, K j * partialTraceRight (pureState ξ) * (K j)ᴴ := by
    ext p₁ p₂
    simp only [partialTraceRight_apply, pureState_apply, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hW_mulVec, star_sum, star_mul', Matrix.mul_apply, conjTranspose_apply,
      partialTraceRight_apply, pureState_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    exact Finset.sum_congr rfl fun k _ => by ring
  have hW_inner : inner ℂ (W.toEuclideanLin ψ') (W.toEuclideanLin φ) = inner ℂ ψ' φ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm _ (star _), dotProduct_comm _ (star _)]
    change star (W *ᵥ ψ'.ofLp) ⬝ᵥ (W *ᵥ φ.ofLp) = star ψ'.ofLp ⬝ᵥ φ.ofLp
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hW, one_mulVec]
  have hub := inner_localUnitary_re_le_rootFidelity
    (W.toEuclideanLin ψ') (W.toEuclideanLin φ) 1 (one_mem _)
  have hid : WithLp.toLp 2
      (((1 : Matrix ι' ι' ℂ) ⊗ₖ (1 : Matrix (↥s × ι) (↥s × ι) ℂ)) *ᵥ
        (W.toEuclideanLin ψ').ofLp) = W.toEuclideanLin ψ' := by
    rw [one_kronecker_one, one_mulVec]
  rw [hid, hW_inner, hW_pt ψ', hW_pt φ, hψ'_pt,
    partialTraceRight_pureState_purifySqrt hσ] at hub
  exact hoverlap ▸ hub

end KroneckerAndKraus

/-! ### Mixed-state CPTP no-cloning -/

section MixedNoCloning

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mixed-state no-cloning, dichotomy form**: if a CPTP Kraus channel `{Kⱼ}_{j ∈ s}`
(`∑_{j ∈ s} Kⱼᴴ Kⱼ = 1`) from `ℂ^ι` to `ℂ^{ι × ι}` clones two density matrices `ρ` and `σ`
(`∑_{j ∈ s} Kⱼ ρ Kⱼᴴ = ρ ⊗ₖ ρ` and `∑_{j ∈ s} Kⱼ σ Kⱼᴴ = σ ⊗ₖ σ`), then `ρ * σ = 0` (orthogonal
supports) or `ρ = σ`. -/
theorem mul_eq_zero_or_eq_of_kraus_clone (s : Finset α) (K : α → Matrix (ι × ι) ι ℂ)
    (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1) {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hρ_clone : ∑ j ∈ s, K j * ρ * (K j)ᴴ = ρ ⊗ₖ ρ)
    (hσ_clone : ∑ j ∈ s, K j * σ * (K j)ᴴ = σ ⊗ₖ σ) :
    ρ * σ = 0 ∨ ρ = σ := by
  have hmono := rootFidelity_le_of_kraus s K hK hρ.posSemidef hσ.posSemidef
  rw [hρ_clone, hσ_clone,
    rootFidelity_kronecker hρ.posSemidef hσ.posSemidef hρ.posSemidef hσ.posSemidef] at hmono
  have hnn := rootFidelity_nonneg ρ σ
  have hle1 := rootFidelity_le_one hρ hσ
  have hprod : rootFidelity ρ σ * (1 - rootFidelity ρ σ) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h0 | h1
  · exact Or.inl ((rootFidelity_eq_zero_iff_mul_eq_zero hρ.posSemidef hσ.posSemidef).mp h0)
  · exact Or.inr ((rootFidelity_eq_one_iff_eq hρ hσ).mp (by linarith))

/-- **Mixed-state no-cloning**: if `|ι| ≥ 2`, no CPTP Kraus channel `{Kⱼ}_{j ∈ s}`
(`∑_{j ∈ s} Kⱼᴴ Kⱼ = 1`) maps every density matrix `ρ` on `ℂ^ι` to `ρ ⊗ₖ ρ`. -/
theorem not_exists_kraus_clone [Nontrivial ι] (s : Finset α) :
    ¬ ∃ K : α → Matrix (ι × ι) ι ℂ, (∑ j ∈ s, (K j)ᴴ * K j = 1) ∧
      ∀ ρ : Matrix ι ι ℂ, IsDensityMatrix ρ → ∑ j ∈ s, K j * ρ * (K j)ᴴ = ρ ⊗ₖ ρ := by
  rintro ⟨K, hK, hclone⟩
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have : Nonempty ι := ⟨i⟩
  let ρ : Matrix ι ι ℂ := pureState (ket i)
  let σ : Matrix ι ι ℂ := (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ)
  have hρ : IsDensityMatrix ρ := isDensityMatrix_pureState (norm_ket i)
  have hσ : IsDensityMatrix σ := by
    rw [show σ = partialTraceLeft (pureState (maxEntangled ι)) from
      (partialTraceLeft_pureState_maxEntangled (ι := ι)).symm]
    exact (isDensityMatrix_pureState (norm_maxEntangled (ι := ι))).partialTraceLeft
  have hc0 : (Fintype.card ι : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rcases mul_eq_zero_or_eq_of_kraus_clone s K hK hρ hσ (hclone ρ hρ) (hclone σ hσ) with h0 | heq
  · have hii := congrFun (congrFun h0 i) i
    simp only [ρ, σ, Matrix.mul_smul, Matrix.smul_apply, pureState_apply,
      ket_apply, ↓reduceIte, star_one, mul_one, smul_eq_mul, Matrix.zero_apply] at hii
    exact hc0 hii
  · have hjj := congrFun (congrFun heq j) j
    simp only [ρ, σ, pureState_apply, ket_apply, hij.symm, ↓reduceIte, zero_mul,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one] at hjj
    exact hc0 hjj.symm

end MixedNoCloning

end Cslib.Quantum
