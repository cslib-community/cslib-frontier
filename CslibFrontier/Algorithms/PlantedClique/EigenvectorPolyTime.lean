/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.EigenvectorApproximation
public import CslibFrontier.Algorithms.PlantedClique.Representation
public import CslibFrontier.Algorithms.IntegerVector.Normalize
public import CslibFrontier.Computability.Probabilistic.DistributionalSearch
public import CslibFrontier.Probability.PlantedClique.Problem
public import CslibFrontier.Probability.PlantedClique.Recovery
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A native finite-precision second-eigenvector solver

`approximateSecondEigenvectorInput` computes a rational approximation to the second eigenvector
of the ordinary adjacency matrix in Algorithm A of [AlonKrivelevichSudakov1998], Section 2.1.
It selects a maximum-norm column of an integer spectral-filter power and normalizes that column
with a binary integer square root. Both computations have unconditional native polynomial-time
certificates. On the planted-clique good event, the returned rational vector is within `1 / 64`
of one orientation of Mathlib's ordered unit second eigenvector.

The recovery program selects the largest absolute coordinates of the integer column and applies
the existing degree cleanup. Rational normalization multiplies every coordinate by the same
positive factor, so the selected indices, including ties, are exactly those of the actual
rational approximation. The separated-spectrum guarantee scales this vector to compare it
with the hidden unit indicator, bounds the missed fraction by twice the squared distance,
and applies the exact degree cleanup inequalities. The original rank-two signal guarantee
also remains available through `recoverFromApproximateSecondEigenvector_eq`.

The fixed-set and arbitrary-prior probability theorems discharge the noise, spectral, and
approximation conditions. In the explicit regime `1 ≤ n`, `6 ≤ k`, `4096 k ≤ n`, and
`8192 √n ≤ k`, failure is at most `2 exp (-n) + n exp (-k / 32)`. The all-parameter budget is one
outside this regime, so one fixed native program supplies a strict PPT solver for the complete
family. Its input contains only the graph and the public target size; the hidden set and prior
are used only in the specification and probability argument.

`EigenvectorSharp` combines the separated-spectrum and scaled-alignment interface with
stronger concentration estimates to prove the threshold `(51 / 7) √n` for this same program,
when `n ≥ 2 ^ 64` and `4096 k ≤ n`. `EigenvectorHybrid` removes that upper-size restriction
by branching to the existing certified integer solver for large cliques.

Runtime uses the existing dense-input encoding: unary `n` and `k`, raw adjacency bits, and
binary integer arithmetic for filter entries and vector coordinates. The polynomial iteration
count is computed from `n`; no convergence witness or accuracy hypothesis is an algorithm input.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Turing.MultiTapeTM Cslib.Algorithms.IntegerVector
open Cslib.Probability Cslib.Probability.PlantedClique
open scoped ENNReal

/-- Compute a rational approximation to the second adjacency eigenvector with fixed precision
scale `128`. The function is total on every dense input, including dimension zero. -/
@[expose] def approximateSecondEigenvectorInput (x : RecoveryInput) : RationalVector :=
  normalize 128 (eigenvectorPowerColumn x (eigenvectorIterations x.vertexCount))

/-- One native polynomial-time certificate computes and writes the actual rational vector
for every encoded input; it requires no spectral or planted-clique promise. -/
@[fun_prop] theorem computableInPolyTime_approximateSecondEigenvectorInput :
    ComputableInPolyTime approximateSecondEigenvectorInput encRecoveryInput encRationalVector := by
  unfold approximateSecondEigenvectorInput
  fun_prop

/-- On the separated spectral promise, the computed rational output approximates one
orientation of the ordered unit second eigenvector to the tolerance needed by degree cleanup. -/
theorem approximateSecondEigenvectorInput_close (x : RecoveryInput)
    (htwo : 1 < x.vertexCount) (hk : 1 ≤ x.cliqueSize) (hkn : x.cliqueSize ≤ x.vertexCount)
    (hspectrum :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (x.graph.isHermitian_adjMatrix ℝ)
      let d := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := x.vertexCount)
      |hT.eigenvalues d ⟨1, htwo⟩ - (x.cliqueSize : ℝ) / 2| ≤ x.cliqueSize / 8 ∧
        ∀ i, i ≠ ⟨1, htwo⟩ → (x.cliqueSize : ℝ) / 6 ≤
          |hT.eigenvalues d i - (x.cliqueSize : ℝ) / 2|) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖(approximateSecondEigenvectorInput x).toEuclidean x.vertexCount -
        s • secondEigenvector x.graph‖ ≤ 1 / 64 := by
  obtain ⟨z, hstored, hz, s, hs, hclose⟩ :=
    eigenvectorPowerColumn_approximation x htwo hk hkn hspectrum
  have hnormalize := normalize_close 128 (by norm_num) z hz
  refine ⟨s, hs, ?_⟩
  rw [approximateSecondEigenvectorInput, hstored]
  calc
    _ ≤ ‖(normalize 128 (List.ofFn z)).toEuclidean x.vertexCount -
          ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖⁻¹ •
            WithLp.toLp 2 (fun i => (z i : ℝ))‖ +
        ‖‖WithLp.toLp 2 (fun i => (z i : ℝ))‖⁻¹ •
            WithLp.toLp 2 (fun i => (z i : ℝ)) - s • secondEigenvector x.graph‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 1 / 128 + 1 / 128 := add_le_add hnormalize hclose
    _ = 1 / 64 := by norm_num

/-- Recover from the computed filter column by stable absolute-coordinate selection followed
by degree cleanup. Normalization preserves the comparisons and need not be recomputed. -/
@[expose] def recoverApproximateEigenvectorInput (x : RecoveryInput) : List ℕ :=
  recoverEigenvectorPowerInput x (eigenvectorIterations x.vertexCount)

/-- The full second-eigenvector recovery program is uniformly native polynomial-time on all
dense inputs, with no accuracy, dimension, or clique-size premises. -/
@[fun_prop] theorem computableInPolyTime_recoverApproximateEigenvectorInput :
    ComputableInPolyTime recoverApproximateEigenvectorInput encRecoveryInput
      (encList encUnary) := by
  unfold recoverApproximateEigenvectorInput
  fun_prop

private theorem toFinset_largestIndices_normalize {n : ℕ} (p : ℕ) (hp : 0 < p)
    (k : ℕ) (z : Fin n → ℤ) :
    (largestIndices k (List.ofFn z)).toFinset =
      (List.selectLargest (fun i => |(normalize p (List.ofFn z)).toEuclidean n i|)
        k (List.finRange n)).image Fin.val := by
  classical
  rw [toFinset_largestIndices_ofFn]
  have hc : (0 : ℝ) < (p : ℝ) / (normalize p (List.ofFn z)).denominator :=
    div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (normalize_denominator_pos _ _))
  have hcompare :
      (fun i j : Fin n => decide ((z j).natAbs ≤ (z i).natAbs)) =
        (fun i j => decide (|(normalize p (List.ofFn z)).toEuclidean n j| ≤
          |(normalize p (List.ofFn z)).toEuclidean n i|)) := by
    funext i j
    apply decide_eq_decide.mpr
    simp only [normalize_toEuclidean_ofFn, PiLp.smul_apply, smul_eq_mul,
      abs_mul, abs_of_pos hc, mul_le_mul_iff_right₀ hc]
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le (α := ℝ) (m := (z j).natAbs) (n := (z i).natAbs)).symm
  simp only [List.selectLargest, hcompare]

private theorem vertexSet_recoverApproximateEigenvectorInput (x : RecoveryInput)
    (hn : 0 < x.vertexCount) :
    vertexSet x.vertexCount (recoverApproximateEigenvectorInput x) =
      x.graph.recoverCliqueByDegree x.cliqueSize
        (List.selectLargest
          (fun j => |(approximateSecondEigenvectorInput x).toEuclidean x.vertexCount j|)
          x.cliqueSize (List.finRange x.vertexCount)) := by
  classical
  obtain ⟨i, hstored, -⟩ :=
    eigenvectorPowerColumn_spec x (eigenvectorIterations x.vertexCount) hn
  let z := fun j =>
    (secondEigenvectorFilter x.graph x.cliqueSize ^ eigenvectorIterations x.vertexCount) j i
  have hselection :
      (largestIndices x.cliqueSize
        (eigenvectorPowerColumn x (eigenvectorIterations x.vertexCount))).toFinset =
      (List.selectLargest
        (fun j => |(approximateSecondEigenvectorInput x).toEuclidean x.vertexCount j|)
        x.cliqueSize (List.finRange x.vertexCount)).image Fin.val := by
    rw [approximateSecondEigenvectorInput, hstored]
    exact toFinset_largestIndices_normalize 128 (by norm_num) x.cliqueSize z
  apply vertexSet_eq_of_toFinset_eq_image
  unfold recoverApproximateEigenvectorInput recoverEigenvectorPowerInput
  exact RecoveryInput.toFinset_cleanup x _ _ hselection (nodup_largestIndices _ _)

private theorem recoverCliqueByDegree_eq_of_scaled_approximation {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hk : 200 ≤ S.card) (hclique : G.IsClique (S : Set (Fin n)))
    (halignment : ∃ c : ℝ, |c| ≤ 1 ∧
      ‖c • secondEigenvector G - unitIndicator S‖ ≤ 107 / 320)
    (hdegree : ∀ v ∉ S, ((S.filter (G.Adj v)).card : ℝ) ≤ 129 / 256 * S.card)
    (v : EuclideanSpace ℝ (Fin n))
    (happrox : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖v - s • secondEigenvector G‖ ≤ 1 / 64) :
    G.recoverCliqueByDegree S.card
      (List.selectLargest (fun i => |v i|) S.card (List.finRange n)) = S := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hkR : (200 : ℝ) ≤ S.card := by exact_mod_cast hk
  obtain ⟨c, hc, halignment⟩ := halignment
  obtain ⟨s, hs, happrox⟩ := happrox
  let w := (c * s) • v
  let T := List.selectLargest (fun i => |v i|) S.card (List.finRange n)
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hscaled : w - c • secondEigenvector G = (c * s) • (v - s • secondEigenvector G) := by
    dsimp only [w]
    rw [smul_sub, smul_smul, mul_assoc, hs2, mul_one]
  have herror : ‖w - c • secondEigenvector G‖ ≤ 1 / 64 := by
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_mul, hsabs, mul_one]
    exact (mul_le_mul_of_nonneg_left happrox (abs_nonneg c)).trans (by linarith)
  have hnear : ‖w - unitIndicator S‖ ≤ 7 / 20 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub w (c • secondEigenvector G) (unitIndicator S)
    linarith
  have hsq : ‖w - unitIndicator S‖ ^ 2 ≤ 49 / 400 := by
    nlinarith [norm_nonneg (w - unitIndicator S)]
  have hT : T.card = S.card := by
    dsimp only [T]
    rw [List.card_selectLargest _ _ (List.nodup_finRange n), List.length_finRange,
      min_eq_left (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)]
  have horder : ∀ i ∉ T, ∀ j ∈ T, |w i| ≤ |w j| := by
    intro i hi j hj
    change |(c * s) * v i| ≤ |(c * s) * v j|
    rw [abs_mul (c * s) (v i), abs_mul (c * s) (v j)]
    exact mul_le_mul_of_nonneg_left
      (List.weight_le_of_notMem_selectLargest (fun i => |v i|) S.card
        (List.finRange n) (List.mem_finRange i) hi hj) (abs_nonneg _)
  have hround := card_sdiff_le_signed_norm_sub_sq hS hT.symm
    (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) horder
  simp only [one_smul] at hround
  have hmiss : ((S \ T).card : ℝ) ≤ 49 / 200 * S.card := by
    calc
      _ ≤ 2 * S.card * ‖w - unitIndicator S‖ ^ 2 := hround
      _ ≤ 2 * S.card * (49 / 400) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  apply G.recoverCliqueByDegree_eq_of_overlap rfl hT hclique
  · have h : (4 : ℝ) * (((S \ T).card : ℝ) + 1) ≤ S.card := by linarith
    exact_mod_cast h
  · intro u hu
    have hdegree' := hdegree u hu
    have h : (4 : ℝ) * ((S.filter (G.Adj u)).card + (S \ T).card) < 3 * S.card := by
      linarith
    exact_mod_cast h

/-- Deterministic correctness for the actual integer-arithmetic recovery program. The proof
uses its computed rational approximation, exact ordering agreement, and the existing tolerance
theorem for Algorithm A. -/
theorem recoverApproximateEigenvectorInput_eq (x : RecoveryInput)
    (S : Finset (Fin x.vertexCount)) (hcard : S.card = x.cliqueSize)
    (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ x.vertexCount)
    (hclique : x.graph.IsClique (S : Set (Fin x.vertexCount)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin x.vertexCount) (𝕜 := ℝ)
      (x.graph.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (x.graph.Adj v)).card ≤ 5 * S.card) :
    vertexSet x.vertexCount (recoverApproximateEigenvectorInput x) = S := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have htwo : 1 < x.vertexCount := by omega
  have hclose := approximateSecondEigenvectorInput_close x htwo (by omega) (by omega)
    (by
      obtain ⟨hcenter, hsep⟩ := adjMatrix_eigenvalues_bounds x.graph S hS hsparse hnoise
      rw [hcard] at hcenter hsep
      refine ⟨hcenter, fun i hi => ?_⟩
      exact le_trans (by linarith [show (0 : ℝ) ≤ x.cliqueSize by positivity] :
        (x.cliqueSize : ℝ) / 6 ≤ x.cliqueSize / 4) (hsep i hi))
  rw [vertexSet_recoverApproximateEigenvectorInput x (by omega), ← hcard]
  exact recoverFromApproximateSecondEigenvector_eq x.graph S hk hsparse hclique hnoise hdegree
    ((approximateSecondEigenvectorInput x).toEuclidean x.vertexCount) hclose

/-- The actual native recovery program succeeds from a separated second eigenvalue and a
scaled second eigenvector close to the hidden indicator. The proof keeps the program's exact
selected indices, including ties, while scaling only the vector used to certify their overlap. -/
theorem recoverApproximateEigenvectorInput_eq_of_spectral_bounds (x : RecoveryInput)
    (S : Finset (Fin x.vertexCount)) (hcard : S.card = x.cliqueSize)
    (htwo : 1 < x.vertexCount) (hk : 200 ≤ S.card)
    (hspectrum :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (x.graph.isHermitian_adjMatrix ℝ)
      let d := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := x.vertexCount)
      |hT.eigenvalues d ⟨1, htwo⟩ - (x.cliqueSize : ℝ) / 2| ≤ x.cliqueSize / 8 ∧
        ∀ i, i ≠ ⟨1, htwo⟩ → (x.cliqueSize : ℝ) / 6 ≤
          |hT.eigenvalues d i - (x.cliqueSize : ℝ) / 2|)
    (hclique : x.graph.IsClique (S : Set (Fin x.vertexCount)))
    (halignment : ∃ c : ℝ, |c| ≤ 1 ∧
      ‖c • secondEigenvector x.graph - unitIndicator S‖ ≤ 107 / 320)
    (hdegree : ∀ v ∉ S, ((S.filter (x.graph.Adj v)).card : ℝ) ≤ 129 / 256 * S.card) :
    vertexSet x.vertexCount (recoverApproximateEigenvectorInput x) = S := by
  have hkn : x.cliqueSize ≤ x.vertexCount := by
    rw [← hcard]
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hclose := approximateSecondEigenvectorInput_close x htwo (by omega) hkn hspectrum
  rw [vertexSet_recoverApproximateEigenvectorInput x (by omega), ← hcard]
  exact recoverCliqueByDegree_eq_of_scaled_approximation x.graph S hk hclique halignment hdegree
    ((approximateSecondEigenvectorInput x).toEuclidean x.vertexCount) hclose

private theorem adjMatrix_graph_ofGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (RecoveryInput.graph ⟨n, k, (RecoveryInput.ofGraph G k).adjacencyBits⟩).adjMatrix ℝ =
      G.adjMatrix ℝ := by
  have hgraph : RecoveryInput.graph ⟨n, k, (RecoveryInput.ofGraph G k).adjacencyBits⟩ = G :=
    RecoveryInput.graph_ofGraph G k
  ext i j
  by_cases hAdj : G.Adj i j <;> simp [SimpleGraph.adjMatrix, hgraph, hAdj]

/-- Presenting a graph by its canonical dense encoding preserves the deterministic guarantee
for the actual recovery program. This bridge also hides the representation's adjacency decider. -/
theorem recoverApproximateEigenvectorInput_ofGraph_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card) :
    vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G S.card)) = S := by
  classical
  let x : RecoveryInput := ⟨n, S.card, (RecoveryInput.ofGraph G S.card).adjacencyBits⟩
  have hgraph : x.graph = G := RecoveryInput.graph_ofGraph G S.card
  have hA : x.graph.adjMatrix ℝ = G.adjMatrix ℝ := adjMatrix_graph_ofGraph G S.card
  have h := recoverApproximateEigenvectorInput_eq x S rfl hk hsparse
  simp only [hA, hgraph] at h
  change vertexSet n (recoverApproximateEigenvectorInput x) = S
  exact h hclique hnoise hdegree

/-- Canonical dense graph encoding preserves the separated-spectrum recovery guarantee.
The computed program receives only the graph and its target clique size. -/
theorem recoverApproximateEigenvectorInput_ofGraph_eq_of_spectral_bounds {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (htwo : 1 < n) (hk : 200 ≤ S.card)
    (hspectrum :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
      let d := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)
      |hT.eigenvalues d ⟨1, htwo⟩ - (S.card : ℝ) / 2| ≤ S.card / 8 ∧
        ∀ i, i ≠ ⟨1, htwo⟩ → (S.card : ℝ) / 6 ≤
          |hT.eigenvalues d i - (S.card : ℝ) / 2|)
    (hclique : G.IsClique (S : Set (Fin n)))
    (halignment : ∃ c : ℝ, |c| ≤ 1 ∧
      ‖c • secondEigenvector G - unitIndicator S‖ ≤ 107 / 320)
    (hdegree : ∀ v ∉ S, ((S.filter (G.Adj v)).card : ℝ) ≤ 129 / 256 * S.card) :
    vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G S.card)) = S := by
  classical
  let x : RecoveryInput := ⟨n, S.card, (RecoveryInput.ofGraph G S.card).adjacencyBits⟩
  have hgraph : x.graph = G := RecoveryInput.graph_ofGraph G S.card
  have hA : x.graph.adjMatrix ℝ = G.adjMatrix ℝ := adjMatrix_graph_ofGraph G S.card
  have h := recoverApproximateEigenvectorInput_eq_of_spectral_bounds x S rfl htwo hk
  simp only [hA, hgraph] at h
  change vertexSet n (recoverApproximateEigenvectorInput x) = S
  exact h hspectrum hclique halignment hdegree

/-- On the good noise and degree events, the fixed executable program returns the planted
set from its canonical graph representation. No approximation premise remains. -/
theorem recoverApproximateEigenvectorInput_sample_eq {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    (hn : 1 ≤ n) (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (noise S ω)‖ ≤ 36 * Real.sqrt n)
    (hdegree : ∀ v ∉ S, 8 * (S.filter ((sample S ω).Adj v)).card ≤ 5 * S.card) :
    vertexSet n (recoverApproximateEigenvectorInput
      (RecoveryInput.ofGraph (sample S ω) S.card)) = S := by
  apply recoverApproximateEigenvectorInput_ofGraph_eq (sample S ω) S hk hsparse
  · exact fun _ hi _ hj hij => sample_adj_of_mem S ω hi hj hij
  · exact opNorm_raw_residual_le_card_div_256 S ω hn hsize hnoise
  · exact hdegree

/-- Fixed-planted-set failure probability of the actual native second-eigenvector program.
Only the independent fair edge coins are random. -/
theorem prob_recoverApproximateEigenvectorInput_ne_le {n : ℕ} (S : Finset (Fin n))
    (hn : 1 ≤ n) (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ)) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | vertexSet n (recoverApproximateEigenvectorInput
        (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S}).toReal ≤
      2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(S.card : ℝ) / 32) := by
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  have h := dens_recover_ne_le_of_noise_degree S (by omega)
    (fun ω => vertexSet n (recoverApproximateEigenvectorInput
      (RecoveryInput.ofGraph (sample S ω) S.card)))
    (fun ω => recoverApproximateEigenvectorInput_sample_eq S ω hn hk hsparse hsize)
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using h

/-- Every independent prior on hidden sets of the public target size has the same exponential
failure guarantee for the actual graph-only native program. -/
theorem searchProblem_recoverApproximateEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsparse : 4096 * k ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(k : ℝ) / 32) := by
  refine searchProblem_failure_le_of_fixedSet prior
    (fun G => vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))
    (by positivity) ?_
  intro S hS
  simpa only [hS] using prob_recoverApproximateEigenvectorInput_ne_le S hn
    (by simpa only [hS] using hk) (by simpa only [hS] using hsparse)
    (by simpa only [hS] using hsize)

open scoped Classical in
/-- The exponential recovery budget in the proved numerical regime, and the universal
probability bound one for every other parameter, including dimension zero. -/
@[expose] noncomputable def eigenvectorRecoveryFailureBound (n k : ℕ) : ℝ≥0∞ :=
  if 1 ≤ n ∧ 6 ≤ k ∧ 4096 * k ≤ n ∧ 8192 * Real.sqrt n ≤ (k : ℝ) then
    ENNReal.ofReal (2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(k : ℝ) / 32))
  else 1

/-- The same fixed recovery function satisfies its total failure budget for every parameter
and every prior on hidden sets of the supplied target size. -/
theorem recoverApproximateEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k}) :
    (searchProblem prior).experiment (fun G => PMF.pure
      (vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))) false ≤
        eigenvectorRecoveryFailureBound n k := by
  classical
  unfold eigenvectorRecoveryFailureBound
  split_ifs with h
  · exact (ENNReal.le_ofReal_iff_toReal_le
      (((searchProblem prior).experiment _).apply_ne_top false) (by positivity)).mpr
        (searchProblem_recoverApproximateEigenvectorInput_failure_le prior h.1 h.2.1
          h.2.2.1 h.2.2.2)
  · exact PMF.coe_le_one _ _

/-- One strict PPT program implements the finite-precision second-eigenvector algorithm for
the whole planted-clique family. The schedule `k n` is supplied as public input and need not
itself be computable; the prior never changes the program or its native certificate. -/
theorem searchProblem_eigenvector_hasPPTSolver (k : ℕ → ℕ)
    (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}) :
    DistributionalSearchProblem.HasSolver (fun n => searchProblem (prior n))
      (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
        (ProbComp.eval (program (RecoveryInput.ofGraph G (k n)))).map (vertexSet n))
      (IsPPTOn encRecoveryInput (encList encUnary))
      (fun n => eigenvectorRecoveryFailureBound n (k n)) :=
  DistributionalSearchProblem.HasSolver.of_computableInPolyTime
    (fun n => searchProblem (prior n))
    (fun n G => RecoveryInput.ofGraph G (k n)) vertexSet
    computableInPolyTime_recoverApproximateEigenvectorInput
    (fun n => recoverApproximateEigenvectorInput_failure_le (prior n))

end Cslib.Algorithms.PlantedClique
