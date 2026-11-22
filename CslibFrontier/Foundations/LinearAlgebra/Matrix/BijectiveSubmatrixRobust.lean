/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Invertible submatrix-robust matrices over `𝔽₂`

Given a submatrix-robust `n × n` matrix `M` over `𝔽₂` with deficiency `t = 2 ⌊√n⌋ + 1`
(`Matrix.exists_submatrixRobust`), its full rank is at least `n - t`, so `dim (ker M) ≤ t`. Adding a
linear isomorphism from `ker M` onto a complement of `range M` (annihilating a complement of
`ker M`) repairs `M` into a bijective linear map `N_mat.mulVec` by a perturbation of rank at most
`t`, preserving submatrix-robustness with deficiency `2 t = 2 (2 ⌊√n⌋ + 1)`
(`Matrix.exists_bijective_submatrixRobust`).

## Main results

* `Matrix.exists_bijective_submatrixRobust`: invertible `n × n` matrices over `𝔽₂` with square-block
  deficiency at most `2 (2 ⌊√n⌋ + 1)` exist.
-/

public section

namespace Matrix

open Set
open scoped Finset

/-- **Invertible submatrix-robust matrices over `𝔽₂`.** Modifying a counting-chosen submatrix-robust
matrix by a matrix of rank at most `n - rank ≤ 2 ⌊√n⌋ + 1` produces a bijective linear map
`N_mat.mulVec` whose every square block has deficiency at most `2 (2 ⌊√n⌋ + 1)`. -/
theorem exists_bijective_submatrixRobust (n : ℕ) :
    ∃ N_mat : Matrix (Fin n) (Fin n) (ZMod 2),
      Function.Bijective N_mat.mulVec ∧
      N_mat.SubmatrixRobust (2 * (2 * Nat.sqrt n + 1)) := by
  classical
  obtain ⟨M, hM⟩ := Matrix.exists_submatrixRobust n
  set t := 2 * Nat.sqrt n + 1
  let fM := M.mulVecLin
  let K_sub := LinearMap.ker fM
  let R_sub := LinearMap.range fM
  obtain ⟨C_dom, hC_dom⟩ := Submodule.exists_isCompl K_sub
  obtain ⟨C_cod, hC_cod⟩ := Submodule.exists_isCompl R_sub
  have hfin_eq : Module.finrank (ZMod 2) K_sub = Module.finrank (ZMod 2) C_cod := by
    have h1 := fM.finrank_range_add_finrank_ker
    have h2 := Submodule.finrank_add_eq_of_isCompl hC_cod
    dsimp only [K_sub, R_sub] at *
    omega
  let φ : K_sub ≃ₗ[ZMod 2] C_cod := LinearEquiv.ofFinrankEq K_sub C_cod hfin_eq
  let π_K : (Fin n → ZMod 2) →ₗ[ZMod 2] K_sub := K_sub.projectionOnto C_dom hC_dom
  let gLin : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    C_cod.subtype.comp (φ.toLinearMap.comp π_K)
  let L_new := fM + gLin
  have hinj : Function.Injective L_new := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv0 : fM v + gLin v = 0 := hv
    have hfg : fM v = -gLin v := eq_neg_of_add_eq_zero_left hv0
    have hmem_inf : fM v ∈ R_sub ⊓ C_cod :=
      ⟨LinearMap.mem_range_self fM v, hfg ▸ C_cod.neg_mem (φ (π_K v)).2⟩
    rw [hC_cod.disjoint.eq_bot] at hmem_inf
    have hvK : v ∈ K_sub := hmem_inf
    have hg0 : gLin v = 0 := by
      have hf0 : fM v = 0 := hvK
      rw [hf0, zero_add] at hv0
      exact hv0
    have hπ : π_K v = ⟨v, hvK⟩ := Submodule.projectionOnto_apply_left hC_dom ⟨v, hvK⟩
    have hφ0 : φ ⟨v, hvK⟩ = 0 := by
      apply Subtype.ext
      simpa only [gLin, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe, hπ,
        Submodule.coe_zero] using hg0
    exact congrArg Subtype.val (φ.injective (hφ0.trans (map_zero φ).symm))
  have hbij_L : Function.Bijective L_new :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  let N_mat := LinearMap.toMatrix' L_new
  let E_mat := LinearMap.toMatrix' gLin
  have hN_mul : N_mat.mulVec = L_new := by ext v i; simp [N_mat]
  refine ⟨N_mat, hN_mul ▸ hbij_L, fun S_set T_set hST => ?_⟩
  have hK_le_t : Module.finrank (ZMod 2) K_sub ≤ t := by
    have hfull := hM univ univ rfl
    rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, M.blockRank_eq_rank] at hfull
    have hsub_le :
        (M.submatrix ((↑) : ↥(univ : Set (Fin n)) → Fin n)
          ((↑) : ↥(univ : Set (Fin n)) → Fin n)).rank ≤ Module.finrank (ZMod 2) R_sub := by
      let resU : (Fin n → ZMod 2) →ₗ[ZMod 2] (↥(univ : Set (Fin n)) → ZMod 2) :=
        LinearMap.funLeft (ZMod 2) (ZMod 2) (Subtype.val : ↥(univ : Set (Fin n)) → Fin n)
      let extU : (↥(univ : Set (Fin n)) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
        LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.Set.univ (Fin n)).symm
      have hfacU : (M.submatrix ((↑) : ↥(univ : Set (Fin n)) → Fin n)
          ((↑) : ↥(univ : Set (Fin n)) → Fin n)).mulVecLin = resU.comp (fM.comp extU) :=
        LinearMap.ext fun x => funext fun i => by
          change (M.submatrix _ _ *ᵥ x) i = (M *ᵥ fun j => x ⟨j, trivial⟩) i.1
          simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
          exact Fintype.sum_equiv (Equiv.Set.univ (Fin n)) _ _ fun _ => rfl
      change Module.finrank (ZMod 2) (LinearMap.range _) ≤ _
      rw [hfacU, LinearMap.range_comp]
      exact (Submodule.finrank_map_le _ _).trans
        (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
    have hrn := fM.finrank_range_add_finrank_ker
    have hfin_dom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
      rw [Module.finrank_pi, Fintype.card_fin]
    dsimp only [K_sub, R_sub] at *
    omega
  have hE_mul : E_mat.mulVec = gLin := by ext v i; simp [E_mat]
  have hM_eq_sub : M = N_mat - E_mat := by
    ext i j
    simp [N_mat, E_mat, L_new, fM, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hE_sub_rank :
      (E_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n)).rank ≤
        Module.finrank (ZMod 2) K_sub := by
    let resS : (Fin n → ZMod 2) →ₗ[ZMod 2] (S_set → ZMod 2) :=
      { toFun := fun y i => y i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let extT : (T_set → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      { toFun := fun x j => if hj : j ∈ T_set then x ⟨j, hj⟩ else 0
        map_add' := fun x₁ x₂ => by ext j; by_cases hj : j ∈ T_set <;> simp [hj]
        map_smul' := fun c x => by ext j; by_cases hj : j ∈ T_set <;> simp [hj] }
    have hfac : (E_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n)).mulVecLin =
        (resS.comp (C_cod.subtype.comp φ.toLinearMap)).comp (π_K.comp extT) :=
      LinearMap.ext fun x => funext fun i => by
        change (E_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n) *ᵥ x) i =
          gLin (extT x) i.1
        rw [← congrFun (congrFun hE_mul (extT x)) i.1]
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, extT, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ T_set)]
        have h0 : (∑ j : {j : Fin n // j ∉ T_set},
            E_mat i.1 j.1 * (if hj : j.1 ∈ T_set then x ⟨j.1, hj⟩ else 0)) = 0 :=
          Finset.sum_eq_zero fun j _ => by simp [j.2]
        rw [h0, add_zero]
        exact Finset.sum_congr rfl fun j _ => by simp [j.2]
    change Module.finrank (ZMod 2)
      (LinearMap.range (E_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n)).mulVecLin) ≤ _
    rw [hfac]
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (LinearMap.finrank_range_le _)
  have hbr_M : M.blockRank S_set T_set ≤
      N_mat.blockRank S_set T_set + Module.finrank (ZMod 2) K_sub := by
    rw [M.blockRank_eq_rank, N_mat.blockRank_eq_rank, hM_eq_sub, Matrix.submatrix_sub]
    set A_b := N_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n)
    set B_b := E_mat.submatrix ((↑) : S_set → Fin n) ((↑) : T_set → Fin n)
    have hsup : LinearMap.range (A_b - B_b).mulVecLin ≤
        LinearMap.range A_b.mulVecLin ⊔ LinearMap.range B_b.mulVecLin := by
      rintro _ ⟨x, rfl⟩
      have hsub_v : (A_b - B_b).mulVecLin x = A_b.mulVecLin x - B_b.mulVecLin x := by
        ext i; simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Pi.sub_apply]
      rw [hsub_v]
      exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)
    have hrank_le : (A_b - B_b).rank ≤ A_b.rank + B_b.rank := by
      have hmono := Submodule.finrank_mono hsup
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A_b.mulVecLin) (LinearMap.range B_b.mulVecLin)
      change Module.finrank (ZMod 2) (LinearMap.range (A_b - B_b).mulVecLin) ≤
        Module.finrank (ZMod 2) (LinearMap.range A_b.mulVecLin) +
          Module.finrank (ZMod 2) (LinearMap.range B_b.mulVecLin)
      omega
    exact hrank_le.trans (Nat.add_le_add_left hE_sub_rank _)
  have hM_st := hM S_set T_set hST
  omega

end Matrix
