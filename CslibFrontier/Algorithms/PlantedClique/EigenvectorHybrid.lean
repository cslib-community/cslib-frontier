/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.PlantedClique.EigenvectorSharp
public import CslibFrontier.Algorithms.PlantedClique.PolyTime
import Mathlib.Tactic.Linarith

/-!
# A native hybrid eigenvector solver for all large clique sizes

The recovery program branches on the public integer test `1048576 * n ≤ k ^ 2`. For these
large cliques it uses the existing certified integer matrix-power solver. Otherwise it uses
the finite-precision second eigenvector of the raw adjacency matrix. The test and both branches
have unconditional native polynomial-time certificates on the dense input encoding.

This original hybrid covers every target size `k ≥ (51 / 7) √n` once `n ≥ 2 ^ 64`. The complementary
branch of the integer test implies `4096 k ≤ n`, the sparsity condition of the sharper
second-eigenvector analysis. The output is computed from the graph and public target size alone;
the hidden set and its prior occur only in the probability specification.

The hybrid's large-clique branch is the library's integer matrix-power algorithm. It is a
distinct algorithm from the literal Algorithm A in [AlonKrivelevichSudakov1998], Section 2.1.

## Main results

* `computableInPolyTime_recoverHybridEigenvectorInput`: a uniform native certificate.
* `prob_recoverHybridEigenvectorInput_ne_le`: the fixed-planted-set failure bound.
* `searchProblem_recoverHybridEigenvectorInput_failure_le`: recovery under any hidden-set prior.
* `searchProblem_hybridEigenvector_hasPPTSolver`: one fixed strict PPT program for the family.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM
open scoped ENNReal

/-- Use the certified integer matrix-power solver when `1024 √n ≤ k`, testing the equivalent
integer inequality, and use the finite-precision raw second eigenvector otherwise. -/
@[expose] def recoverHybridEigenvectorInput (x : RecoveryInput) : List ℕ :=
  if 1048576 * x.vertexCount ≤ x.cliqueSize ^ 2 then recoverInput x
  else recoverApproximateEigenvectorInput x

/-- One native polynomial-time machine computes the branch decision and the complete hybrid
recovery output on every dense input, with no probabilistic or spectral promise. -/
@[fun_prop] theorem computableInPolyTime_recoverHybridEigenvectorInput :
    ComputableInPolyTime recoverHybridEigenvectorInput encRecoveryInput
      (encList encUnary) := by
  unfold recoverHybridEigenvectorInput
  simp only [pow_two]
  fun_prop

private theorem sqrt_size_of_large_branch {n k : ℕ} (h : 1048576 * n ≤ k ^ 2) :
    1024 * Real.sqrt n ≤ (k : ℝ) := by
  have h' : (1048576 : ℝ) * n ≤ (k : ℝ) ^ 2 := by exact_mod_cast h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ),
    Nat.cast_nonneg (α := ℝ) k]

private theorem sparse_of_small_branch {n k : ℕ} (hn : 2 ^ 64 ≤ n)
    (h : ¬1048576 * n ≤ k ^ 2) : 4096 * k ≤ n := by
  have hk : k ^ 2 < 1048576 * n := Nat.lt_of_not_ge h
  have hn' : 17592186044416 ≤ n := by omega
  have hnn : 17592186044416 * n ≤ n * n := Nat.mul_le_mul_right n hn'
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).1
  nlinarith

private theorem min_clique_size {n k : ℕ} (hn : 2 ^ 64 ≤ n)
    (hsize : (51 / 7 : ℝ) * Real.sqrt n ≤ k) : 6 ≤ k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hk : (6 : ℝ) ≤ k := by linarith
  exact_mod_cast hk

private theorem base_error_le_sharp (n k : ℕ) :
    2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(k : ℝ) / 32) ≤
      eigenvectorSharpError n k := by
  have hnoise : 2 * Real.exp (-(n : ℝ)) ≤ 2 * Real.exp (-(n : ℝ) / 64) := by
    gcongr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdegree : (n : ℝ) * Real.exp (-(k : ℝ) / 32) ≤
      n * Real.exp (-(k : ℝ) / 32768) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg n)
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  unfold eigenvectorSharpError
  linarith [Real.exp_pos (-(n : ℝ) / 16777216)]

/-- Every fixed planted set of size at least `(51 / 7) √n` is recovered by the native hybrid
with the stated exponential error, once `n ≥ 2 ^ 64`. There is no upper bound on the clique size. -/
theorem prob_recoverHybridEigenvectorInput_ne_le {n : ℕ} (S : Finset (Fin n))
    (hnlarge : 2 ^ 64 ≤ n) (hsize : 51 / 7 * Real.sqrt n ≤ (S.card : ℝ)) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | vertexSet n (recoverHybridEigenvectorInput
        (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S}).toReal ≤
      eigenvectorSharpError n S.card := by
  classical
  by_cases hbranch : 1048576 * n ≤ S.card ^ 2
  · have hbase := prob_recover_ne_le S (by omega) (min_clique_size hnlarge hsize)
      (sqrt_size_of_large_branch hbranch)
    simp_rw [recover_eq_classical] at hbase
    have hbridge (ω : Coins n) :
        vertexSet n (recoverHybridEigenvectorInput
          (RecoveryInput.ofGraph (sample S ω) S.card)) =
          @recover n (sample S ω) (Classical.decRel _) S.card := by
      change vertexSet n (if 1048576 * n ≤ S.card ^ 2 then
        recoverInput (RecoveryInput.ofGraph (sample S ω) S.card) else
        recoverApproximateEigenvectorInput (RecoveryInput.ofGraph (sample S ω) S.card)) = _
      rw [ite_eq_left hbranch, vertexSet_recoverInput_ofGraph]
    simpa only [hbridge] using hbase.trans (base_error_le_sharp n S.card)
  · have hsharp := prob_recoverApproximateEigenvectorInput_ne_le_sharp S hnlarge
      (sparse_of_small_branch hnlarge hbranch) hsize
    simpa only [recoverHybridEigenvectorInput, RecoveryInput.ofGraph, hbranch, ite_false]
      using hsharp

/-- The same graph-only hybrid program recovers a clique of size at least `(51 / 7) √n` under
any independent prior on hidden sets, for every `n ≥ 2 ^ 64` and without an upper-size promise. -/
theorem searchProblem_recoverHybridEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hnlarge : 2 ^ 64 ≤ n) (hsize : 51 / 7 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      eigenvectorSharpError n k := by
  refine searchProblem_failure_le_of_fixedSet prior
    (fun G => vertexSet n (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G k)))
    (by unfold eigenvectorSharpError; positivity) ?_
  intro S hS
  simpa only [hS] using prob_recoverHybridEigenvectorInput_ne_le S hnlarge
    (by simpa only [hS] using hsize)

open scoped Classical in
/-- The exponential hybrid recovery budget for `n ≥ 2 ^ 64` and `k ≥ (51 / 7) √n`, and the
universal probability bound one for every other parameter, including dimension zero. -/
@[expose] noncomputable def hybridEigenvectorRecoveryFailureBound (n k : ℕ) : ℝ≥0∞ :=
  if 2 ^ 64 ≤ n ∧ 51 / 7 * Real.sqrt n ≤ (k : ℝ) then
    ENNReal.ofReal (eigenvectorSharpError n k)
  else 1

/-- The fixed native hybrid function meets its total failure budget under every hidden-set
prior, including parameters outside the numerical success regime. -/
theorem recoverHybridEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k}) :
    (searchProblem prior).experiment (fun G => PMF.pure
      (vertexSet n (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G k)))) false ≤
        hybridEigenvectorRecoveryFailureBound n k := by
  classical
  unfold hybridEigenvectorRecoveryFailureBound
  split_ifs with h
  · exact (ENNReal.le_ofReal_iff_toReal_le
      (((searchProblem prior).experiment _).apply_ne_top false)
      (by unfold eigenvectorSharpError; positivity)).mpr
        (searchProblem_recoverHybridEigenvectorInput_failure_le prior h.1 h.2)
  · exact PMF.coe_le_one _ _

/-- One fixed strict PPT program solves the whole planted-clique family with the hybrid
failure budget. The public target schedule and hidden-set prior never alter its native machine. -/
theorem searchProblem_hybridEigenvector_hasPPTSolver (k : ℕ → ℕ)
    (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}) :
    DistributionalSearchProblem.HasSolver (fun n => searchProblem (prior n))
      (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
        (ProbComp.eval (program (RecoveryInput.ofGraph G (k n)))).map (vertexSet n))
      (IsPPTOn encRecoveryInput (encList encUnary))
      (fun n => hybridEigenvectorRecoveryFailureBound n (k n)) :=
  DistributionalSearchProblem.HasSolver.of_computableInPolyTime
    (fun n => searchProblem (prior n))
    (fun n G => RecoveryInput.ofGraph G (k n)) vertexSet
    computableInPolyTime_recoverHybridEigenvectorInput
    (fun n => recoverHybridEigenvectorInput_failure_le (prior n))

end Cslib.Algorithms.PlantedClique
