/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
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
  let fM := M.mulVecLin
  obtain ⟨C_dom, hC_dom⟩ := (LinearMap.ker fM).exists_isCompl
  obtain ⟨C_cod, hC_cod⟩ := (LinearMap.range fM).exists_isCompl
  have hrank := fM.finrank_range_add_finrank_ker
  have hcompl := Submodule.finrank_add_eq_of_isCompl hC_cod
  -- `gLin` maps `ker M` isomorphically onto a complement of `range M` and kills `C_dom`.
  have hfin : Module.finrank (ZMod 2) (LinearMap.ker fM) = Module.finrank (ZMod 2) C_cod := by
    omega
  let φ := LinearEquiv.ofFinrankEq _ _ hfin
  let gLin := C_cod.subtype ∘ₗ φ.toLinearMap ∘ₗ (LinearMap.ker fM).projectionOnto C_dom hC_dom
  have hinj : Function.Injective (fM + gLin) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv0 : fM v + gLin v = 0 := hv
    have hvK : fM v = 0 := Submodule.disjoint_def.mp hC_cod.disjoint _
      (LinearMap.mem_range_self _ v) (eq_neg_of_add_eq_zero_left hv0 ▸ C_cod.neg_mem (φ _).2)
    rw [hvK, zero_add] at hv0
    have : (⟨v, hvK⟩ : LinearMap.ker fM) = 0 := by
      simpa [gLin, Submodule.projectionOnto_apply_left hC_dom ⟨v, hvK⟩] using hv0
    exact congrArg Subtype.val this
  let N := LinearMap.toMatrix' (fM + gLin)
  let E := LinearMap.toMatrix' gLin
  refine ⟨N, ?_, fun S T hST => ?_⟩
  · have hbij : Function.Bijective (fM + gLin) := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
    simpa only [N, funext (LinearMap.toMatrix'_mulVec (fM + gLin))] using hbij
  -- `M` has rank at least `n - t`, so `dim (ker M) ≤ t`.
  have hK := hM univ univ rfl
  have hMr : M.blockRank univ univ = M.rank := by
    rw [blockRank_eq_rank]; exact rank_submatrix M (Equiv.Set.univ _) (Equiv.Set.univ _)
  rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hMr] at hK
  rw [Module.finrank_fin_fun] at hrank
  change M.rank + _ = _ at hrank
  -- `M = N - E`, where `E` factors through `ker M`.
  have hE : E.rank ≤ Module.finrank (ZMod 2) (LinearMap.ker fM) := by
    rw [rank, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range
      ((LinearMap.ker fM).projectionOnto C_dom hC_dom) (C_cod.subtype ∘ₗ φ.toLinearMap))).trans
      (LinearMap.finrank_range_le _)
  have hMeq : M = N - E := by
    rw [← map_sub, add_sub_cancel_right]; exact (LinearMap.toMatrix'_toLin' M).symm
  have hsub := rank_sub_le (N.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n))
    (E.submatrix Subtype.val Subtype.val)
  change ((N - E).submatrix _ _).rank ≤ _ at hsub
  rw [← hMeq, ← M.blockRank_eq_rank, ← N.blockRank_eq_rank] at hsub
  have := (rank_submatrix_le E (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).trans hE
  have := hM S T hST
  omega

end Matrix
