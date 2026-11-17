/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Eigenvector
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative bounds for the second adjacency eigenvector

The raw adjacency matrix is a rank-two signal plus an error. An operator-norm bound on that
error isolates the second eigenvalue, while a sharper bound in the planted-indicator direction
controls its eigenline. Keeping the projection coefficient, rather than normalizing the
projection, gives the approximation needed for largest-coordinate rounding.

These are deterministic intermediate bounds for the raw-adjacency algorithm. The constants
below are obtained by the residual argument in this file; the probabilistic hypotheses are
discharged separately for the planted graph distribution.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix
open scoped RealInnerProductSpace

private theorem residual_parameter_bounds {q k t : ℝ}
    (hq : 4294967296 ≤ q) (hk : 51 / 7 * q ≤ k)
    (ht : t ≤ 1 / 64) (htsmall : k ≤ 16 * q → t ≤ 1 / 16384) :
    let ε := 15 / 7 * q + 1
    let r := 1025 / 2048 * q + 1
    let gap := k / 2 - ε
    let residual := r + t * ε + k / 2 * t
    0 < gap ∧ k / 6 ≤ gap ∧ residual ≤ k / 14 ∧
      ∃ d : ℝ, 0 ≤ d ∧ residual ≤ gap * d ∧ t + d ≤ 107 / 320 := by
  dsimp
  have hq0 : 0 ≤ q := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hε : 0 ≤ 15 / 7 * q + 1 := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  by_cases hsmall : k ≤ 16 * q
  · have hts := htsmall hsmall
    have hεt := mul_le_mul_of_nonneg_right hts hε
    have hkt := mul_le_mul_of_nonneg_left hts (by positivity : 0 ≤ k / 2)
    refine ⟨by linarith, 107 / 320 - 1 / 16384, by norm_num, ?_, by linarith⟩
    linarith
  · have hεt := mul_le_mul_of_nonneg_right ht hε
    have hkt := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ k / 2)
    have hlarge := lt_of_not_ge hsmall
    refine ⟨by linarith, 1 / 8, by norm_num, ?_, by linarith⟩
    linarith

variable {n : ℕ}

/-- Deterministic spectral bounds for the raw adjacency matrix, assuming a global perturbation
bound and a sharper perturbation bound in the planted-indicator direction. For
`(51 / 7) √n ≤ #S` in the stated sparse regime, the second eigenvalue lies within `#S / 8`
of `#S / 2`, all other eigenvalues stay at least `#S / 6` away, and a scalar multiple of the
unit second eigenvector approximates the normalized indicator within `107 / 320`.
The scalar has absolute value at most one, so approximating the unit eigenvector does not
amplify the numerical error when this scalar is applied. -/
theorem secondEigenvector_bounds_of_residual_le
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * S.card ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        15 / 7 * Real.sqrt n + 1)
    (hdirection : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))
        (unitIndicator S)‖ ≤ 1025 / 2048 * Real.sqrt n + 1) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)
    let j : Fin n := ⟨1, lt_of_lt_of_le (by norm_num : 1 < 2 ^ 64) hnlarge⟩
    |hT.eigenvalues hn j - (S.card : ℝ) / 2| ≤ (S.card : ℝ) / 8 ∧
      (∀ i, i ≠ j → (S.card : ℝ) / 6 ≤
        |hT.eigenvalues hn i - (S.card : ℝ) / 2|) ∧
      ∃ c : ℝ, |c| ≤ 1 ∧ ‖c • secondEigenvector G - unitIndicator S‖ ≤ 107 / 320 := by
  classical
  let q := Real.sqrt (n : ℝ)
  let k : ℝ := S.card
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq_sq : q ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hnreal : (18446744073709551616 : ℝ) ≤ n := by
    norm_num at hnlarge
    exact_mod_cast hnlarge
  have hq : 4294967296 ≤ q := by nlinarith only [hq0, hq_sq, hnreal]
  have hqpos : 0 < q := by linarith only [hq]
  have hk : 51 / 7 * q ≤ k := hsize
  have hkpos : 0 < k := by linarith only [hk, hq]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hkpos)
  have huniv : (univ : Finset (Fin n)).Nonempty := hS.mono (subset_univ S)
  have hnthree : 3 ≤ n := (by norm_num : 3 ≤ 2 ^ 64).trans hnlarge
  have hsparse' : 4096 * k ≤ (n : ℝ) := by
    change (4096 : ℝ) * S.card ≤ (n : ℝ)
    exact_mod_cast hsparse
  let T := (G.adjMatrix ℝ).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (G.isHermitian_adjMatrix ℝ)
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)
  let j : Fin n := ⟨1, by omega⟩
  let w := unitIndicator (univ : Finset (Fin n))
  let u := unitIndicator S
  let t := |inner ℝ w u|
  let x := u - inner ℝ w u • w
  let v := hT.eigenvectorBasis hn j
  let c := (hT.eigenvectorBasis hn).repr x j
  let ε := 15 / 7 * q + 1
  let r := 1025 / 2048 * q + 1
  let gap := k / 2 - ε
  let residual := r + t * ε + k / 2 * t
  have hw : ‖w‖ = 1 := norm_unitIndicator huniv
  have hu : ‖u‖ = 1 := norm_unitIndicator hS
  have hv : ‖v‖ = 1 := (hT.eigenvectorBasis hn).norm_eq_one j
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huw : inner ℝ u w = inner ℝ w u := real_inner_comm _ _
  have hinner : inner ℝ w u = Real.sqrt k / q := by
    simpa only [w, u, k, q, Fintype.card_fin] using inner_unitIndicator_univ S
  have ht_eq : t = Real.sqrt k / q := by
    change |inner ℝ w u| = Real.sqrt k / q
    rw [hinner, abs_of_nonneg (by positivity)]
  have hrootk : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hkpos.le
  have ht : t ≤ 1 / 64 := by
    rw [ht_eq]
    apply (div_le_iff₀ hqpos).mpr
    have hroot : 64 * Real.sqrt k ≤ q :=
      (sq_le_sq₀ (by positivity) hq0).mp (by nlinarith only [hrootk, hq_sq, hsparse'])
    linarith only [hroot]
  have htsmall : k ≤ 16 * q → t ≤ 1 / 16384 := by
    intro hsmall
    rw [ht_eq]
    apply (div_le_iff₀ hqpos).mpr
    have hscaled := mul_le_mul_of_nonneg_left hsmall
      (by norm_num : (0 : ℝ) ≤ 268435456)
    have hqmul : 4294967296 * q ≤ q ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hq0]
    have hroot : 16384 * Real.sqrt k ≤ q :=
      (sq_le_sq₀ (by positivity) hq0).mp (by nlinarith only [hrootk, hscaled, hqmul])
    linarith only [hroot]
  obtain ⟨hgap0, hgapk, hresk, d, hd0, hresd, htd⟩ :=
    residual_parameter_bounds hq hk ht htsmall
  have herr (y : EuclideanSpace ℝ (Fin n)) :
      ‖T y - (((n : ℝ) / 2 * inner ℝ w y) • w + (k / 2 * inner ℝ u y) • u)‖ ≤
        ε * ‖y‖ := by
    rw [adjMatrix_rank_two_residual_eq G S hS y]
    exact (ContinuousLinearMap.le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right hnoise (norm_nonneg y))
  have hRw : ‖T w - (((n : ℝ) / 2) • w + (k / 2 * inner ℝ w u) • u)‖ ≤ ε := by
    simpa only [hww, huw, mul_one, hw] using herr w
  have hRu : ‖T u - (((n : ℝ) / 2 * inner ℝ w u) • w + (k / 2) • u)‖ ≤ r := by
    have hdir :
        ‖T u - (((n : ℝ) / 2 * inner ℝ w u) • w + (k / 2 * inner ℝ u u) • u)‖ ≤ r := by
      rw [adjMatrix_rank_two_residual_eq G S hS u]
      exact hdirection
    simpa only [huu, mul_one] using hdir
  have hres : ‖T x - (k / 2) • x‖ ≤ residual :=
    LinearMap.norm_sub_inner_smul_residual_le_of_rank_two hw hu
      (by positivity : 0 ≤ k / 2) hRw hRu
  have hsep : ∀ i, i ≠ j → gap ≤ |hT.eigenvalues hn i - k / 2| := by
    apply hT.second_eigenvalue_separation_of_rank_two hn hnthree hw
      (by positivity : 0 ≤ k / 2)
    · change k / 2 - ε ≤ (n : ℝ) / 2 - ε - k / 2
      linarith only [hsparse', hkpos]
    · exact le_rfl
    · exact herr
  have hprojection := hT.gap_mul_sq_norm_sub_projection_le hn j x (k / 2) gap
    hgap0.le hsep
  have hxclose : ‖x - c • v‖ ≤ d := by
    apply (sq_le_sq₀ (norm_nonneg _) hd0).mp
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hgap0)
    calc
      gap ^ 2 * ‖x - c • v‖ ^ 2 ≤ ‖T x - (k / 2) • x‖ ^ 2 := hprojection
      _ ≤ (gap * d) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hgap0.le hd0)).mpr
        (hres.trans hresd)
      _ = gap ^ 2 * d ^ 2 := by ring
  have hnear : ‖u - c • v‖ ≤ 107 / 320 := by
    have hux : ‖u - x‖ = t := by
      simp [x, t, norm_smul, hw, Real.norm_eq_abs]
    calc
      ‖u - c • v‖ ≤ ‖u - x‖ + ‖x - c • v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ t + d := by rw [hux]; exact add_le_add le_rfl hxclose
      _ ≤ 107 / 320 := htd
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa only [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℝ hw, hu] using
      (Submodule.norm_starProjection_apply_le (Submodule.span ℝ {w})ᗮ u)
  have hc : |c| ≤ 1 := by
    change |(hT.eigenvectorBasis hn).repr x j| ≤ 1
    rw [OrthonormalBasis.repr_apply_apply]
    have hi := abs_real_inner_le_norm v x
    rw [hv, one_mul] at hi
    exact hi.trans hxnorm
  have hclower : 3 / 5 ≤ |c| := by
    have htriangle := norm_sub_norm_le u (c • v)
    rw [hu, norm_smul, hv, Real.norm_eq_abs, mul_one] at htriangle
    linarith only [htriangle, hnear]
  have hcenter : |hT.eigenvalues hn j - k / 2| ≤ k / 8 := by
    have hcoord := (hT.abs_eigenvalue_sub_mul_abs_repr_le_norm_residual hn j x (k / 2)).trans
      (hres.trans hresk)
    change |hT.eigenvalues hn j - k / 2| * |c| ≤ k / 14 at hcoord
    have hscaled := mul_le_mul_of_nonneg_left hclower
      (abs_nonneg (hT.eigenvalues hn j - k / 2))
    linarith only [hcoord, hscaled, hkpos]
  refine ⟨hcenter, fun i hi => hgapk.trans (hsep i hi), c, hc, ?_⟩
  have hv_eq : v = secondEigenvector G := by
    exact (secondEigenvector_eq G (by omega)).symm
  rw [← hv_eq, norm_sub_rev]
  exact hnear

end Cslib.Algorithms.PlantedClique
