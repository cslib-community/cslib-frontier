/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral decomposition of finite-dimensional complex unitaries

Any linear isometry equivalence `R : E ≃ₗᵢ[ℂ] E` on a finite-dimensional complex inner product
space admits an orthonormal basis of eigenvectors with unit-modulus eigenvalues `μ k + I * ν k`
(`LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`), constructed by simultaneously
diagonalizing its commuting Hermitian part `(R + R⁻¹) / 2` and skew-Hermitian part
`-I (R - R⁻¹) / 2`.

## Main results

* `LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`: unitary diagonalization on
  finite-dimensional complex inner product spaces.
-/

public section

namespace LinearIsometryEquiv

/-- Any unitary on a finite-dimensional complex inner product space has an orthonormal basis of
eigenvectors with unit-modulus eigenvalues `μ k + I * ν k`. -/
theorem exists_orthonormalBasis_eigenvectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (μ ν : Fin (Module.finrank ℂ E) → ℝ),
      (∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1) ∧
      (∀ k, R (b k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • b k) := by
  let H : E →ₗ[ℂ] E := (1 / 2 : ℂ) • (R.toLinearMap + R.symm.toLinearMap)
  let K : E →ₗ[ℂ] E := (-Complex.I / 2 : ℂ) • (R.toLinearMap - R.symm.toLinearMap)
  have hR_apply : ∀ x, R.toLinearMap x = R x := fun _ => rfl
  have hRm_apply : ∀ x, R.symm.toLinearMap x = R.symm x := fun _ => rfl
  have hR_star : star R.toLinearMap = R.symm.toLinearMap := R.adjoint_toLinearMap_eq_symm
  have hRm_star : star R.symm.toLinearMap = R.toLinearMap := by rw [← hR_star, star_star]
  have hHsym : H.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint H).mpr <| by
    simp only [IsSelfAdjoint, H, star_smul, star_add, hR_star, hRm_star, add_comm]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by
      simp only [Complex.star_def, map_div₀, map_one, map_ofNat]]
  have hKsym : K.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint K).mpr <| by
    simp only [IsSelfAdjoint, K, star_smul, star_sub, hR_star, hRm_star]
    rw [show star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) by
      simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_I, map_ofNat]; ring,
      neg_smul, ← smul_neg, neg_sub]
  have hHK : ∀ x, H (K x) = K (H x) := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_smul, map_add, map_sub, hR_apply, hRm_apply, R.apply_symm_apply, R.symm_apply_apply]
    module
  have hR_decomp : ∀ x, R x = H x + Complex.I • K x := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      hR_apply, hRm_apply, smul_smul]
    rw [show Complex.I * (-Complex.I / 2) = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module
  let S (lam : Module.End.Eigenvalues H) : Submodule ℂ E := Module.End.eigenspace H (lam : ℂ)
  have hKS (lam : Module.End.Eigenvalues H) : ∀ x ∈ S lam, K x ∈ S lam := fun x hx => by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hHK, hx, K.map_smul]
  let K_S (lam : Module.End.Eigenvalues H) : S lam →ₗ[ℂ] S lam := K.restrict (hKS lam)
  have hK_S (lam : Module.End.Eigenvalues H) : (K_S lam).IsSymmetric :=
    hKsym.restrict_invariant (hKS lam)
  let v_family (lam : Module.End.Eigenvalues H) :
      OrthonormalBasis (Fin (Module.finrank ℂ (S lam))) ℂ (S lam) :=
    (hK_S lam).eigenvectorBasis rfl
  let bSig := hHsym.direct_sum_isInternal.collectedOrthonormalBasis
    hHsym.orthogonalFamily_eigenspaces' v_family
  let e : (Σ lam : Module.End.Eigenvalues H, Fin (Module.finrank ℂ (S lam))) ≃
      Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis bSig.toBasis).symm
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E := bSig.reindex e
  let μ : Fin (Module.finrank ℂ E) → ℝ := fun k => Complex.re ((e.symm k).1 : ℂ)
  let ν : Fin (Module.finrank ℂ E) → ℝ :=
    fun k => (hK_S (e.symm k).1).eigenvalues rfl (e.symm k).2
  have hb_eq : ∀ k, b k = ((v_family (e.symm k).1 (e.symm k).2 : S (e.symm k).1) : E) := fun k => by
    simp only [b, bSig, OrthonormalBasis.reindex_apply,
      DirectSum.IsInternal.collectedOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis,
      DirectSum.IsInternal.collectedBasis_coe, OrthonormalBasis.coe_toBasis]
  have hvH : ∀ k, H (b k) = (μ k : ℂ) • b k := fun k => by
    have hre : (μ k : ℂ) = ((e.symm k).1 : ℂ) :=
      Complex.conj_eq_iff_re.mp (hHsym.conj_eigenvalue_eq_self (e.symm k).1.property)
    rw [hre, hb_eq k]
    exact Module.End.mem_eigenspace_iff.mp (v_family (e.symm k).1 (e.symm k).2).property
  have hvK : ∀ k, K (b k) = (ν k : ℂ) • b k := fun k => by
    rw [hb_eq k]
    exact congrArg Subtype.val ((hK_S (e.symm k).1).apply_eigenvectorBasis rfl (e.symm k).2)
  have heig : ∀ k, R (b k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • b k := fun k => by
    rw [hR_decomp, hvH k, hvK k, smul_smul, ← add_smul]
  have hunit : ∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1 := fun k => by
    have hnorm : ‖((μ k : ℂ) + Complex.I * (ν k : ℂ))‖ = 1 := by
      simpa only [heig k, norm_smul, b.orthonormal.1 k, mul_one] using R.norm_map (b k)
    rw [← Complex.normSq_add_mul_I (μ k) (ν k), mul_comm (ν k : ℂ) Complex.I, ← Complex.sq_norm,
      hnorm, one_pow]
  exact ⟨b, μ, ν, hunit, heig⟩

end LinearIsometryEquiv
