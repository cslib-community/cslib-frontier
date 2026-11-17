/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Eigenvector
public import CslibFrontier.Algorithms.PlantedClique.EigenvectorProgram
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.PowerIteration
import CslibFrontier.Algorithms.IntegerPower.Search
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.AdjMatrix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An integer-power approximation to the second adjacency eigenvector

The integer polynomial filter `16 (n + k + 1)² I - (2 A - k I)²` preserves the raw adjacency
eigenvectors and makes its second eigenline dominant in the proved planted-clique spectral
regime. Applying a fixed polynomial number of iterations to every standard basis vector and
selecting a column of maximum squared norm gives a direction within `1 / 128` of a unit second
eigenvector, up to sign. The integer output is the actual list computed by `eigenvectorPowerColumn`.

The chosen iteration count is conservative. Its purpose is to obtain an explicit uniform
native polynomial-time realization with binary arithmetic; no approximation, overlap or
eigenvalue supplied by the caller is an input to the computation.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix Turing.MultiTapeTM IntegerPower
open scoped RealInnerProductSpace

/-- A fixed polynomial iteration count giving directional error at most `1 / 128` in the
raw-adjacency spectral regime. -/
@[expose] def eigenvectorIterations (n : ℕ) : ℕ := 1048576 * n ^ 3

/-- The iteration count is computed in polynomial time with unary input and output. -/
@[fun_prop] theorem computableInPolyTime_eigenvectorIterations :
    ComputableInPolyTime eigenvectorIterations encUnary encUnary := by
  unfold eigenvectorIterations
  exact ComputableInPolyTime.unary_mul' (by fun_prop) (.unary_pow 3)

private theorem filter_spectrum_bounds {ι : Type*} (μ : ι → ℝ) (j : ι)
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hrad : ∀ i, |μ i| ≤ (n : ℝ))
    (hcenter : |μ j - (k : ℝ) / 2| ≤ (k : ℝ) / 8)
    (hsep : ∀ i, i ≠ j → (k : ℝ) / 6 ≤ |μ i - (k : ℝ) / 2|) :
    let K : ℝ := 16 * ((n : ℝ) + k + 1) ^ 2
    let f : ι → ℝ := fun i => K - (2 * μ i - k) ^ 2
    0 < f j ∧ 0 ≤ K - (k : ℝ) ^ 2 / 9 ∧
      (∀ i, i ≠ j → |f i| ≤ K - (k : ℝ) ^ 2 / 9) ∧
      (K - (k : ℝ) ^ 2 / 9) / f j ≤ 1 - 1 / (3072 * (n : ℝ) ^ 2) := by
  let K : ℝ := 16 * ((n : ℝ) + k + 1) ^ 2
  let f : ι → ℝ := fun i => K - (2 * μ i - k) ^ 2
  change 0 < f j ∧ 0 ≤ K - (k : ℝ) ^ 2 / 9 ∧ _ ∧ _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hnpos : (0 : ℝ) < n := by linarith
  have hKlow : (k : ℝ) ^ 2 ≤ K := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ k)
      (by positivity : (0 : ℝ) ≤ (n : ℝ) + k + 1)).mpr
        (show (k : ℝ) ≤ (n : ℝ) + k + 1 by linarith)
    dsimp only [K]
    nlinarith only [hsq, sq_nonneg ((n : ℝ) + k + 1)]
  have hKup : K ≤ 144 * (n : ℝ) ^ 2 := by
    have hsum : (n : ℝ) + k + 1 ≤ 3 * n := by linarith
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + k + 1)
      (by positivity : (0 : ℝ) ≤ 3 * n)).mpr hsum
    dsimp only [K]
    nlinarith only [hsq]
  have hselected : (2 * μ j - k) ^ 2 ≤ (k : ℝ) ^ 2 / 16 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (μ j - (k : ℝ) / 2))
      (by positivity : (0 : ℝ) ≤ (k : ℝ) / 8)).mpr hcenter
    rw [sq_abs] at hsq
    nlinarith only [hsq]
  have hpositive : 0 < f j := by
    dsimp only [f]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hbeta : 0 ≤ K - (k : ℝ) ^ 2 / 9 := by
    nlinarith [sq_nonneg (k : ℝ)]
  have hnonneg (i : ι) : 0 ≤ f i := by
    have hd : |2 * μ i - k| ≤ 2 * (n : ℝ) + k := by
      calc
        |2 * μ i - k| ≤ |2 * μ i| + |(k : ℝ)| := abs_sub _ _
        _ = 2 * |μ i| + k := by
          simp only [abs_mul, Nat.abs_ofNat, Nat.abs_cast]
        _ ≤ _ := by linarith [hrad i]
    have hsq := (sq_le_sq₀ (abs_nonneg (2 * μ i - k))
      (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + k)).mpr hd
    rw [sq_abs] at hsq
    have hlarge := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + k)
      (by positivity : (0 : ℝ) ≤ 4 * ((n : ℝ) + k + 1))).mpr
        (show 2 * (n : ℝ) + k ≤ 4 * ((n : ℝ) + k + 1) by linarith)
    dsimp only [f, K]
    nlinarith only [hsq, hlarge]
  have hother (i : ι) (hij : i ≠ j) : |f i| ≤ K - (k : ℝ) ^ 2 / 9 := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) / 6)
      (abs_nonneg (μ i - (k : ℝ) / 2))).mpr (hsep i hij)
    rw [sq_abs] at hsq
    rw [abs_of_nonneg (hnonneg i)]
    dsimp only [f]
    nlinarith only [hsq]
  refine ⟨hpositive, hbeta, hother, ?_⟩
  apply (div_le_iff₀ hpositive).mpr
  have halphaup : f j ≤ 144 * (n : ℝ) ^ 2 :=
    (sub_le_self K (sq_nonneg _)).trans hKup
  have hfrac : f j / (3072 * (n : ℝ) ^ 2) ≤ 3 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 3072 * (n : ℝ) ^ 2)).mpr
    nlinarith only [halphaup]
  have hgap : K - (k : ℝ) ^ 2 / 9 ≤ f j - 3 / 64 := by
    dsimp only [f]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  calc
    K - (k : ℝ) ^ 2 / 9 ≤ f j - 3 / 64 := hgap
    _ ≤ f j - f j / (3072 * (n : ℝ) ^ 2) := sub_le_sub_left hfrac _
    _ = _ := by ring

private theorem power_error_le {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q)
    (hcontract : q ≤ 1 - 1 / (3072 * (n : ℝ) ^ 2)) :
    2 * (n : ℝ) * q ^ (2 * eigenvectorIterations n) ≤ (1 / 128 : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hdecay := (pow_le_pow_left₀ hq hcontract (eigenvectorIterations n)).trans
    (Real.one_sub_pow_le_one_div_one_add_mul (by positivity) (by linarith)
      (eigenvectorIterations n))
  have hscale : 256 * (n : ℝ) ≤
      1 + (eigenvectorIterations n : ℝ) * (1 / (3072 * (n : ℝ) ^ 2)) := by
    simp only [eigenvectorIterations, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have heq : (1048576 : ℝ) * (n : ℝ) ^ 3 * (1 / (3072 * (n : ℝ) ^ 2)) =
        (1024 / 3 : ℝ) * n := by field_simp; ring
    rw [heq]
    linarith
  have hpow : q ^ eigenvectorIterations n ≤ 1 / (256 * (n : ℝ)) :=
    hdecay.trans (one_div_le_one_div_of_le (by positivity) hscale)
  have hsq := (sq_le_sq₀ (pow_nonneg hq (eigenvectorIterations n))
    (by positivity : (0 : ℝ) ≤ 1 / (256 * (n : ℝ)))).mpr hpow
  rw [Nat.mul_comm 2, pow_mul]
  calc
    2 * (n : ℝ) * (q ^ eigenvectorIterations n) ^ 2 ≤
        2 * (n : ℝ) * (1 / (256 * (n : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / (32768 * (n : ℝ)) := by field_simp; ring
    _ ≤ 1 / 32768 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ ≤ _ := by norm_num

private theorem secondEigenvectorFilter_cast {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) :
    (secondEigenvectorFilter G k).map (Int.castRingHom ℝ) =
      (16 * ((n : ℝ) + k + 1) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        ((2 : ℝ) • G.adjMatrix ℝ - (k : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) ^ 2 := by
  have hA : (Int.castRingHom ℝ).mapMatrix (G.adjMatrix ℤ) = G.adjMatrix ℝ := by
    ext i j
    by_cases h : G.Adj i j <;> simp [h]
  change (Int.castRingHom ℝ).mapMatrix (secondEigenvectorFilter G k) = _
  simp only [secondEigenvectorFilter, map_sub, map_pow, map_zsmul, map_one, hA]
  simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_mul, Int.cast_pow,
    Int.cast_add, Int.cast_one]

private theorem secondEigenvectorFilter_apply {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) {v : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (hv : (G.adjMatrix ℝ).toEuclideanLin v = μ • v) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((secondEigenvectorFilter G k).map (Int.castRingHom ℝ)) v =
      (16 * ((n : ℝ) + k + 1) ^ 2 - (2 * μ - k) ^ 2) • v := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (G.adjMatrix ℝ)
  let B := (2 : ℝ) • A - (k : ℝ) •
    (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  have hAv : A v = μ • v := hv
  have hBv : B v = (2 * μ - k) • v := by
    simp only [B, sub_apply, smul_apply, one_apply_eq_self, hAv, smul_smul, sub_smul]
  have hBsq : (B ^ 2) v = (2 * μ - k) ^ 2 • v := by
    calc
      (B ^ 2) v = B (B v) := by rw [pow_two, mul_apply_eq_comp]
      _ = B ((2 * μ - k) • v) := congrArg B hBv
      _ = (2 * μ - k) • B v := B.map_smul _ _
      _ = (2 * μ - k) ^ 2 • v := by rw [hBv, smul_smul, pow_two]
  rw [secondEigenvectorFilter_cast]
  simp only [map_sub, map_smul, map_pow, map_one]
  change (16 * ((n : ℝ) + k + 1) ^ 2) • v - (B ^ 2) v = _
  rw [hBsq, sub_smul]

/-- The actual integer column computed by the native program is nonzero, and its normalized
direction approximates the raw adjacency matrix's second eigenvector up to sign. The spectral
promise centers that eigenvalue within `k / 8` of `k / 2` and separates every other eigenvalue
from the filter's center by at least `k / 6`. No planted set is needed for this numerical result. -/
theorem eigenvectorPowerColumn_approximation (x : RecoveryInput)
    (htwo : 1 < x.vertexCount) (hk : 1 ≤ x.cliqueSize) (hkn : x.cliqueSize ≤ x.vertexCount)
    (hspectrum :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (x.graph.isHermitian_adjMatrix ℝ)
      let d := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := x.vertexCount)
      |hT.eigenvalues d ⟨1, htwo⟩ - (x.cliqueSize : ℝ) / 2| ≤ x.cliqueSize / 8 ∧
        ∀ i, i ≠ ⟨1, htwo⟩ → (x.cliqueSize : ℝ) / 6 ≤
          |hT.eigenvalues d i - (x.cliqueSize : ℝ) / 2|) :
    ∃ z : Fin x.vertexCount → ℤ,
      eigenvectorPowerColumn x (eigenvectorIterations x.vertexCount) = List.ofFn z ∧
      (WithLp.toLp 2 (fun i => (z i : ℝ)) : EuclideanSpace ℝ (Fin x.vertexCount)) ≠ 0 ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ‖‖WithLp.toLp 2 (fun i => (z i : ℝ))‖⁻¹ • WithLp.toLp 2 (fun i => (z i : ℝ)) -
          s • secondEigenvector x.graph‖ ≤ 1 / 128 := by
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (x.graph.isHermitian_adjMatrix ℝ)
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := x.vertexCount)
  let b := hT.eigenvectorBasis hn
  let μ := hT.eigenvalues hn
  let j : Fin x.vertexCount := ⟨1, htwo⟩
  let K : ℝ := 16 * ((x.vertexCount : ℝ) + x.cliqueSize + 1) ^ 2
  let f : Fin x.vertexCount → ℝ := fun i => K - (2 * μ i - x.cliqueSize) ^ 2
  let β : ℝ := K - (x.cliqueSize : ℝ) ^ 2 / 9
  let M := secondEigenvectorFilter x.graph x.cliqueSize
  let T := (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))).toLinearMap
  obtain ⟨hcenter, hsep⟩ := hspectrum
  obtain ⟨hα, hβ, hother, hratio⟩ := filter_spectrum_bounds μ j (by omega) hk hkn
    x.graph.abs_adjMatrix_eigenvalues_le hcenter hsep
  change 0 < f j at hα
  change 0 ≤ β at hβ
  change ∀ i, i ≠ j → |f i| ≤ β at hother
  change β / f j ≤ 1 - 1 / (3072 * (x.vertexCount : ℝ) ^ 2) at hratio
  have heigen (i : Fin x.vertexCount) : T (b i) = f i • b i :=
    secondEigenvectorFilter_apply x.graph x.cliqueSize (hT.apply_eigenvectorBasis hn i)
  obtain ⟨seed, hout, hmax⟩ := eigenvectorPowerColumn_spec x
    (eigenvectorIterations x.vertexCount) (by omega)
  have hmax' (l : Fin x.vertexCount) :
      ‖(T ^ eigenvectorIterations x.vertexCount)
        (EuclideanSpace.basisFun (Fin x.vertexCount) ℝ l)‖ ^ 2 ≤
      ‖(T ^ eigenvectorIterations x.vertexCount)
        (EuclideanSpace.basisFun (Fin x.vertexCount) ℝ seed)‖ ^ 2 := by
    dsimp only [T]
    rw [norm_sq_powerVector, norm_sq_powerVector]
    exact_mod_cast (show dotProduct (powerVector M (eigenvectorIterations x.vertexCount) l)
        (powerVector M (eigenvectorIterations x.vertexCount) l) ≤
      dotProduct (powerVector M (eigenvectorIterations x.vertexCount) seed)
        (powerVector M (eigenvectorIterations x.vertexCount) seed) by
      simpa only [dotProduct, powerVector_apply, ← pow_two] using hmax l)
  obtain ⟨hz, s, hs, herror⟩ := b.exists_sign_normalize_pow_column_sub_sq_le T f heigen
    (EuclideanSpace.basisFun (Fin x.vertexCount) ℝ) j hα hβ hother
    (eigenvectorIterations x.vertexCount) seed hmax'
  have hsecond : b j = secondEigenvector x.graph := by
    exact (secondEigenvector_eq x.graph htwo).symm
  rw [Fintype.card_fin] at herror
  have hsmall := herror.trans (power_error_le (by omega) (div_nonneg hβ hα.le) hratio)
  rw [← toLp_powerVector, hsecond] at hsmall
  rw [← toLp_powerVector] at hz
  refine ⟨powerVector M (eigenvectorIterations x.vertexCount) seed, ?_, hz, s, hs, ?_⟩
  · rw [hout]
    apply congrArg List.ofFn
    funext i
    exact (powerVector_apply M (eigenvectorIterations x.vertexCount) seed i).symm
  · exact (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 128)).mp hsmall

end Cslib.Algorithms.PlantedClique
