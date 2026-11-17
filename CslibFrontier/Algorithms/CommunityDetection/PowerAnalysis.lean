/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.CommunityDetection.IntegerCentering
public import CslibFrontier.Algorithms.IntegerPower.Approximation
public import CslibFrontier.Probability.StochasticBlockModel.Model
public import CslibFrontier.Foundations.Data.BitString.SignWord
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic correctness with integer centering

The integer matrix `B = D² A - c (J-I)` differs from `D²` times the ideal shifted centered
matrix by `(D² m-c) J + (c-D² p) I`, where `m=(p+q)/2`. If `c` approximates `D² m` within one
and lies in `[0,D²]`, this additional perturbation has operator norm at most `n+D²`.
The same quantity bounds the change in every true-label row margin.

The shared integer power search therefore gives approximate labels whenever the squared total
residual is at most `gap / 64` times the squared growth threshold `D n`. Its sign rounding then
makes at most `gap * n / 8` errors, which weighted-vote cleanup corrects. This is a deterministic
step: the stochastic block model supplies the noise and row-margin bounds separately, without
any independence requirement between the two stages.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Finset Matrix BitString Probability.StochasticBlockModel
open scoped RealInnerProductSpace unitInterval

variable {n : ℕ}

private theorem ones_apply_bound (hn : 0 < n) (y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (fun _ _ => (1 : ℝ))) y‖ ≤
      (n : ℝ) * ‖y‖ := by
  let u := NormedSpace.normalize (signWord (fun _ : Fin n => false))
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize
    (norm_pos_iff.mp (show 0 < ‖signWord (fun _ : Fin n => false)‖ by
      rw [norm_signWord, Fintype.card_fin]
      exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))
  have hact : Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (fun _ _ => (1 : ℝ))) y =
      ((n : ℝ) * inner ℝ u y) • u := by
    have h := signWord_rankOne_apply (fun _ : Fin n => false) 1 y
    change (Matrix.of (fun _ _ => (1 : ℝ))).toEuclideanLin y = _
    simpa only [signVal_false, one_smul, Fintype.card_fin, one_mul, Matrix.vecMulVec, u] using h
  rw [hact, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), hu,
    mul_one]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [hu, one_mul] using abs_real_inner_le_norm u y) (Nat.cast_nonneg n)

private theorem integerMatrix_residual_le (params : PowerParameters) (p q : I)
    (g : Fin n → Bool) (ω : Coins n) (hn : 0 < n)
    (hc : params.center ≤ params.resolution ^ 2)
    (hcenter : |(params.resolution : ℝ) ^ 2 * midpoint p q - params.center| ≤ 1)
    {r : ℝ} (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ r)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((integerMatrix params (sample ω)).map (Int.castRingHom ℝ)) y -
      (((params.resolution : ℝ) ^ 2 * gap p q * n) *
        inner ℝ (NormedSpace.normalize (signWord g)) y) •
          NormedSpace.normalize (signWord g)‖ ≤
      ((params.resolution : ℝ) ^ 2 * r + n + (params.resolution : ℝ) ^ 2) * ‖y‖ := by
  let S : ℝ := (params.resolution : ℝ) ^ 2
  let a : ℝ := S * midpoint p q - params.center
  let b : ℝ := (params.center : ℝ) - S * p
  let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => 1)
  have hB : (integerMatrix params (sample ω)).map (Int.castRingHom ℝ) =
      (S * gap p q) • Matrix.vecMulVec (fun i => signVal (g i))
        (fun i => signVal (g i)) + S • noise p q g ω + a • J + b • 1 := by
    rw [integerMatrix_cast_eq params p q, shiftedCenteredAdjacency_sample, smul_add, smul_smul]
  have hsignal : Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((S * gap p q) • Matrix.vecMulVec (fun i => signVal (g i))
        (fun i => signVal (g i))) y =
      ((S * gap p q * n) * inner ℝ (NormedSpace.normalize (signWord g)) y) •
        NormedSpace.normalize (signWord g) := by
    change ((S * gap p q) • Matrix.vecMulVec (fun i => signVal (g i))
      (fun i => signVal (g i))).toEuclideanLin y = _
    simpa only [Fintype.card_fin] using signWord_rankOne_apply g (S * gap p q) y
  have heq : Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((integerMatrix params (sample ω)).map (Int.castRingHom ℝ)) y -
      ((S * gap p q * n) * inner ℝ (NormedSpace.normalize (signWord g)) y) •
        NormedSpace.normalize (signWord g) =
      S • (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω) y) +
        a • (Matrix.toEuclideanCLM (𝕜 := ℝ) J y) + b • y := by
    rw [hB, map_add, map_add, map_add, add_apply, add_apply, add_apply, hsignal]
    simp only [map_smul, smul_apply, map_one, one_apply_eq_self]
    abel
  have hS : 0 ≤ S := sq_nonneg _
  have hN : ‖S • (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω) y)‖ ≤
      S * (r * ‖y‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hS]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right hnoise (norm_nonneg y))) hS
  have hJ : ‖a • (Matrix.toEuclideanCLM (𝕜 := ℝ) J y)‖ ≤ (n : ℝ) * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)).trans
      (by simpa only [one_mul] using ones_apply_bound hn y)
  have hI : ‖b • y‖ ≤ S * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_diagonal_error_le params p hc) (norm_nonneg y)
  rw [heq]
  calc
    ‖S • (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω) y) +
        a • (Matrix.toEuclideanCLM (𝕜 := ℝ) J y) + b • y‖
        ≤ ‖S • (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω) y)‖ +
          ‖a • (Matrix.toEuclideanCLM (𝕜 := ℝ) J y)‖ + ‖b • y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ S * (r * ‖y‖) + (n : ℝ) * ‖y‖ + S * ‖y‖ := add_le_add (add_le_add hN hJ) hI
    _ = _ := by dsimp only [S]; ring

/-- Deterministic recovery by the exact integer algorithm. The centering error, spectral
residual and true-label margins are explicit; the distributional analysis proves these premises
with probability tending to one for fixed `p > q`. -/
theorem recoverPower_sample_eq_or_not_of_bounds (params : PowerParameters) (p q : I)
    (g : Fin n → Bool) (ω : Coins n) (hn : 0 < n) (hpq : (q : ℝ) < p)
    (hD : 0 < params.resolution) (hc : params.center ≤ params.resolution ^ 2)
    (hcenter : |(params.resolution : ℝ) ^ 2 * midpoint p q - params.center| ≤ 1)
    (r : ℝ) (hr : 0 ≤ r)
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ r)
    (hDgap : 2 ≤ (params.resolution : ℝ) * gap p q)
    (hsize : 64 * ((params.resolution : ℝ) ^ 2 * r + n +
      (params.resolution : ℝ) ^ 2) ^ 2 ≤
        gap p q * ((params.resolution : ℝ) * n) ^ 2)
    (hmargin : ∀ i, gap p q * n / 2 <
      signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j)) :
    recoverPower params (sample ω) = g ∨ recoverPower params (sample ω) = fun i => !g i := by
  let D : ℝ := params.resolution
  let S : ℝ := D ^ 2
  let k : ℕ := params.resolution * n
  let R : ℝ := S * r + n + S
  let a : ℝ := S * gap p q * n
  let v := NormedSpace.normalize (signWord g)
  let M := integerMatrix params (sample ω)
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))
  have hd : 0 < gap p q := by dsimp [gap]; linarith
  have hd1 : gap p q ≤ 1 := by dsimp [gap]; linarith [p.2.2, q.2.1]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hD0 : 0 < D := Nat.cast_pos.mpr hD
  have hS : 0 < S := sq_pos_of_pos hD0
  have hk : 0 < k := Nat.mul_pos hD hn
  have hkR : (k : ℝ) = D * n := Nat.cast_mul _ _
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hbound : 64 * R ^ 2 ≤ gap p q * (k : ℝ) ^ 2 := by
    simpa only [hkR] using hsize
  have hratio : (R / (k : ℝ)) ^ 2 ≤ gap p q / 64 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
    nlinarith only [hbound]
  have hReighth : R ≤ (k : ℝ) / 8 := by
    apply (sq_le_sq₀ hR (by positivity : (0 : ℝ) ≤ (k : ℝ) / 8)).mp
    nlinarith only [hbound, mul_le_mul_of_nonneg_right hd1 (sq_nonneg (k : ℝ))]
  have hRk : R ≤ (k : ℝ) := by
    linarith only [hReighth, hk0]
  have hsignalSize : 2 * (k : ℝ) ≤ a := by
    calc
      2 * (k : ℝ) = 2 * (D * n) := by rw [hkR]
      _ ≤ (D * gap p q) * (D * n) :=
        mul_le_mul_of_nonneg_right hDgap (by positivity)
      _ = a := by dsimp only [a, S]; ring
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize
    (norm_pos_iff.mp (show 0 < ‖signWord g‖ by
      rw [norm_signWord, Fintype.card_fin]
      exact Real.sqrt_pos.mpr hnR))
  have hresidual (y : EuclideanSpace ℝ (Fin n)) :
      ‖T y - (a * inner ℝ v y) • v‖ ≤ R * ‖y‖ :=
    integerMatrix_residual_le params p q g ω hn hc hcenter hnoise y
  have hsignal : ‖T v - a • v‖ ≤ R := by
    simpa only [real_inner_self_eq_norm_sq, hv, one_pow, mul_one] using hresidual v
  have htriangle : a ≤ ‖T v - a • v‖ + ‖T v‖ := by
    calc
      a = ‖a • v‖ := by rw [norm_smul_of_nonneg ha, hv, mul_one]
      _ ≤ ‖a • v - T v‖ + ‖T v‖ := norm_le_norm_sub_add _ _
      _ = _ := by rw [norm_sub_rev]
  have hnormgain : (k : ℝ) ≤ ‖T v‖ := by
    linarith only [hsignalSize, hRk, hsignal, htriangle]
  have hgain : 2 * ((k : ℝ) ^ 2 / 4) ≤ ‖T v‖ ^ 2 := by
    have hsq := (sq_le_sq₀ hk0.le (norm_nonneg (T v))).mpr hnormgain
    nlinarith only [hsq, sq_nonneg (k : ℝ)]
  have hM : (M.map (Int.castRingHom ℝ)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [M, integerMatrix, Matrix.map_apply, eq_comm, (sample ω).adj_comm]
  obtain ⟨s, hs, hclose⟩ := IntegerPower.recoveredVector_alignment M hk hM hv hR hgain hresidual
  let z := WithLp.toLp 2 (fun i => (IntegerPower.recoveredVector M k i : ℝ))
  have hclose' : ‖NormedSpace.normalize z - s • v‖ ^ 2 ≤ gap p q / 8 := by
    nlinarith only [hclose, hratio]
  have hround (g' : Fin n → Bool)
      (hdist : ‖NormedSpace.normalize z - NormedSpace.normalize (signWord g')‖ ^ 2 ≤
        gap p q / 8) :
      (hammingDist (powerLabels params (sample ω)) g' : ℝ) ≤ gap p q * n / 8 := by
    have h := hammingDist_signRound_le_card_mul_norm_sub_sq g' (NormedSpace.normalize z)
    rw [signRound_normalize] at h
    simp only [Fintype.card_fin] at h
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left hdist hnR.le])
  obtain ⟨g', hg', herr⟩ : ∃ g' : Fin n → Bool, (g' = g ∨ g' = fun i => !g i) ∧
      (hammingDist (powerLabels params (sample ω)) g' : ℝ) ≤ gap p q * n / 8 := by
    rcases hs with rfl | rfl
    · exact ⟨g, Or.inl rfl, hround g (by simpa only [one_smul, v] using hclose')⟩
    · exact ⟨fun i => !g i, Or.inr rfl, hround _ (by
        simpa only [neg_one_smul, signWord_not, NormedSpace.normalize_neg, v] using hclose')⟩
  have hcentering : (n : ℝ) + S ≤ S * gap p q * n / 16 := by
    change (n : ℝ) + S ≤ a / 16
    calc
      (n : ℝ) + S ≤ R := by dsimp only [R]; nlinarith [mul_nonneg hS.le hr]
      _ ≤ a / 16 := by linarith only [hReighth, hsignalSize]
  have hcost : 2 * S * (hammingDist (powerLabels params (sample ω)) g' : ℝ) ≤
      S * gap p q * n / 4 := by
    calc
      2 * S * (hammingDist (powerLabels params (sample ω)) g' : ℝ)
          ≤ 2 * S * (gap p q * n / 8) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ = _ := by ring
  have hm (i : Fin n) : 2 * S * (hammingDist (powerLabels params (sample ω)) g' : ℝ) <
      signVal (g i) * ∑ j, M.map (Int.castRingHom ℝ) i j * signVal (g j) := by
    have he := abs_integerMatrix_margin_sub_le params p q (sample ω) g hc hcenter i
    have ht := mul_lt_mul_of_pos_left (hmargin i) hS
    have he' := (abs_le.mp he).1
    change -((n : ℝ) + S) ≤
      signVal (g i) * ∑ j, M.map (Int.castRingHom ℝ) i j * signVal (g j) -
        S * (signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j *
          signVal (g j)) at he'
    nlinarith only [he', ht, hcentering, hcost, ha]
  have hm' (i : Fin n) : 2 * S * (hammingDist (powerLabels params (sample ω)) g' : ℝ) <
      signVal (g' i) * ∑ j, M.map (Int.castRingHom ℝ) i j * signVal (g' j) := by
    rcases hg' with rfl | rfl
    · exact hm i
    · simpa only [signVal_not, mul_neg, sum_neg_distrib, neg_mul, neg_neg] using hm i
  have hcorrect : recoverPower params (sample ω) = g' :=
    cleanup_eq_of_margin (fun i j => abs_integerMatrix_le params (sample ω) hc i j) hm'
  rcases hg' with rfl | rfl
  · exact Or.inl hcorrect
  · exact Or.inr hcorrect

end Cslib.Algorithms.CommunityDetection
