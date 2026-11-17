/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
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
rational approximation. Correctness therefore uses `recoverFromApproximateSecondEigenvector_eq`
without another rounding argument.

The fixed-set and arbitrary-prior probability theorems discharge the noise, spectral, and
approximation conditions. In the explicit regime `1 ≤ n`, `6 ≤ k`, `4096 k ≤ n`, and
`8192 √n ≤ k`, failure is at most `2 exp (-n) + n exp (-k / 32)`. The all-parameter budget is one
outside this regime, so one fixed native program supplies a strict PPT solver for the complete
family. Its input contains only the graph and the public target size; the hidden set and prior
are used only in the specification and probability argument.

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

/-- On the rank-two signal promise, the computed rational output approximates one orientation
of the ordered unit second eigenvector to the tolerance needed by degree cleanup. -/
theorem approximateSecondEigenvectorInput_close (x : RecoveryInput)
    (S : Finset (Fin x.vertexCount)) (hcard : S.card = x.cliqueSize) (hS : S.Nonempty)
    (hsparse : 4096 * S.card ≤ x.vertexCount)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin x.vertexCount) (𝕜 := ℝ)
      (x.graph.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖(approximateSecondEigenvectorInput x).toEuclidean x.vertexCount -
        s • secondEigenvector x.graph‖ ≤ 1 / 64 := by
  obtain ⟨z, hstored, hz, s, hs, hclose⟩ :=
    eigenvectorPowerColumn_approximation x S hcard hS hsparse hnoise
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
  have hn : 0 < x.vertexCount := by
    have hcard_le := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hcard_le
    omega
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
  rw [RecoveryInput.toFinset_cleanup x _ _ hselection (nodup_largestIndices _ _), ← hcard]
  rw [recoverFromApproximateSecondEigenvector_eq x.graph S hk hsparse hclique hnoise hdegree
    ((approximateSecondEigenvectorInput x).toEuclidean x.vertexCount)
    (approximateSecondEigenvectorInput_close x S hcard hS hsparse hnoise)]

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
  have hA : x.graph.adjMatrix ℝ = G.adjMatrix ℝ := by
    ext i j
    by_cases hAdj : G.Adj i j <;> simp [SimpleGraph.adjMatrix, hgraph, hAdj]
  have h := recoverApproximateEigenvectorInput_eq x S rfl hk hsparse
  simp only [hA, hgraph] at h
  change vertexSet n (recoverApproximateEigenvectorInput x) = S
  exact h hclique hnoise hdegree

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
