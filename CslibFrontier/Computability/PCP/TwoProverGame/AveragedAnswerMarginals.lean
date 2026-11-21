/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AveragedAnswerStates
public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
import CslibFrontier.Foundations.Quantum.DensityMatrix.PartialTracePairing
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDomination

/-!
# Marginals of checked-answer states

For independent local question draws, forgetting Bob's checked outcomes in Alice's
marginal leaves the marginal after only Alice's averaged measurement. Thus a supported
checked-answer branch has relative entropy at most the negative logarithm of its Born
weight from the resulting question-independent reference on Alice's system. These are
the marginal and postselection comparisons used in
[Bavarian, Vidick and Yuen, Claim 5.13][BavarianVidickYuen2022].

## Main results

* `sum_partialTraceRight_averagedCheckedVector`: forgetting Bob's checked outcomes.
* `relativeEntropy_normalizedCheckedVector_partialTraceRight_le`: the branch entropy bound.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Quantum Matrix Finset
open scoped Kronecker MatrixOrder ComplexOrder

variable {τ X Y A B ι κ : Type*} [Fintype τ] [DecidableEq τ] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype X] [Fintype Y]

variable (S : QuantumStrategy X Y (τ → A) (τ → B) ι κ) (C : Finset τ)

omit [Fintype Y] in
/-- Alice's marginal when both players' checked answers are forgotten. Its construction
uses only Alice's averaged measurement and the input state. -/
noncomputable def averagedCheckedMarginalAlice (p : PMF X) : Matrix ι ι ℂ :=
  ∑ a, partialTraceRight
    (densityConj ((POVM.mixture p (S.checkedAlice C)).sqrtEffect a ⊗ₖ (1 : Matrix κ κ ℂ))
      (pureState S.state))

/-- Summing Bob's checked outcomes leaves Alice's selected marginal, independently
of the law over Bob's full questions. -/
theorem sum_partialTraceRight_averagedCheckedVector (p : PMF X) (q : PMF Y) (a : C → A) :
    (∑ b, partialTraceRight (pureState (S.averagedCheckedVector C p q a b))) =
      partialTraceRight
        (densityConj ((POVM.mixture p (S.checkedAlice C)).sqrtEffect a ⊗ₖ (1 : Matrix κ κ ℂ))
          (pureState S.state)) := by
  let L := (POVM.mixture p (S.checkedAlice C)).sqrtEffect a
  let N := POVM.mixture q (S.checkedBob C)
  let ρ := densityConj (L ⊗ₖ (1 : Matrix κ κ ℂ)) (pureState S.state)
  have hbranch (b : C → B) : pureState (S.averagedCheckedVector C p q a b) =
      densityConj ((1 : Matrix ι ι ℂ) ⊗ₖ N.sqrtEffect b) ρ := by
    rw [averagedCheckedVector_eq, ← densityConj_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, densityConj_pureState]
    rfl
  have hN : ∑ b, (N.sqrtEffect b)ᴴ * N.sqrtEffect b = 1 := by
    simp only [N.conjTranspose_sqrtEffect, N.sqrtEffect_mul_self, N.sum_effect]
  simp_rw [hbranch, densityConj_apply]
  rw [← partialTraceRight_sum]
  simpa only [ρ, L, densityConj_apply] using partialTraceRight_kraus univ N.sqrtEffect hN ρ

/-- The total marginal over all checked outcomes is independent of Bob's full
question distribution. -/
theorem sum_sum_partialTraceRight_averagedCheckedVector (p : PMF X) (q : PMF Y) :
    (∑ a, ∑ b, partialTraceRight (pureState (S.averagedCheckedVector C p q a b))) =
      S.averagedCheckedMarginalAlice C p := by
  simp_rw [sum_partialTraceRight_averagedCheckedVector, averagedCheckedMarginalAlice]

/-- Each unnormalized checked branch is dominated by the same marginal reference
on Alice's system, for every distribution of Bob's full questions. -/
theorem partialTraceRight_averagedCheckedVector_le (p : PMF X) (q : PMF Y)
    (a : C → A) (b : C → B) :
    partialTraceRight (pureState (S.averagedCheckedVector C p q a b)) ≤
      S.averagedCheckedMarginalAlice C p := by
  rw [← S.sum_sum_partialTraceRight_averagedCheckedVector C p q]
  have hnonneg (a' : C → A) (b' : C → B) :
      0 ≤ partialTraceRight (pureState (S.averagedCheckedVector C p q a' b')) :=
    (posSemidef_partialTraceRight (posSemidef_pureState _)).nonneg
  exact (single_le_sum (fun b' _ => hnonneg a b') (mem_univ b)).trans
    (single_le_sum (fun a' _ => sum_nonneg fun b' _ => hnonneg a' b') (mem_univ a))

omit [Fintype Y] in
/-- The marginal from the nonselective measurement is a density matrix. -/
theorem isDensityMatrix_averagedCheckedMarginalAlice (p : PMF X) :
    IsDensityMatrix (S.averagedCheckedMarginalAlice C p) := by
  let M := POVM.mixture p (S.checkedAlice C)
  let U (a : C → A) := M.sqrtEffect a ⊗ₖ (1 : Matrix κ κ ℂ)
  let ρ := pureState S.state
  have hρ := isDensityMatrix_pureState S.norm_state
  change IsDensityMatrix (∑ a, partialTraceRight (densityConj (U a) ρ))
  refine ⟨posSemidef_sum _ fun a _ => posSemidef_partialTraceRight
    (by rw [densityConj_apply]; exact hρ.posSemidef.mul_mul_conjTranspose_same _), ?_⟩
  have ht (a : C → A) :
      (densityConj (U a) ρ).trace = ((M.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ).trace := by
    rw [densityConj_apply, trace_mul_cycle]
    simp only [U, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      M.conjTranspose_sqrtEffect, M.sqrtEffect_mul_self, Matrix.one_mul]
  have hsum : (∑ a, M.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) = 1 := calc
    _ = (∑ a, M.effect a) ⊗ₖ (1 : Matrix κ κ ℂ) := by
      ext i j
      simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]
    _ = 1 := by rw [M.sum_effect, one_kronecker_one]
  simp only [trace_sum, trace_partialTraceRight, ht]
  rw [← trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, hρ.trace_eq_one]

/-- The entropy of a normalized supported branch relative to the common Alice
marginal is at most the logarithmic cost of selecting its checked answers. -/
theorem relativeEntropy_normalizedCheckedVector_partialTraceRight_le
    (p : PMF X) (q : PMF Y) (a : C → A) (b : C → B)
    (h : (a, b) ∈ (p.bind fun x => q.bind fun y => S.checkedAnswers C x y).support) :
    relativeEntropy (partialTraceRight (pureState (S.normalizedCheckedVector C p q a b)))
      (S.averagedCheckedMarginalAlice C p) ≤
        ((-Real.log ((p.bind fun x => q.bind fun y => S.checkedAnswers C x y) (a, b)).toReal : ℝ) :
          WithTop ℝ) := by
  let v := S.averagedCheckedVector C p q a b
  let ψ := S.normalizedCheckedVector C p q a b
  have hn := S.norm_normalizedCheckedVector C p q a b h
  have hweight : 0 < ((p.bind fun x => q.bind fun y => S.checkedAnswers C x y) (a, b)).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp h) (PMF.apply_ne_top _ _)
  have hv : v = ‖v‖ • ψ := S.averagedCheckedVector_eq_norm_smul_normalized C p q a b
  have hpure : pureState v = ‖v‖ ^ 2 • pureState ψ := by
    conv_lhs => rw [hv]
    exact pureState_real_smul _ _
  have hle : ‖v‖ ^ 2 • partialTraceRight (pureState ψ) ≤
      S.averagedCheckedMarginalAlice C p := by
    have hm := S.partialTraceRight_averagedCheckedVector_le C p q a b
    change partialTraceRight (pureState v) ≤ _ at hm
    rw [hpure, ← algebraMap_smul ℂ (‖v‖ ^ 2) (pureState ψ), partialTraceRight_smul,
      algebraMap_smul] at hm
    exact hm
  rw [← S.norm_averagedCheckedVector_sq C p q a b] at hweight ⊢
  exact relativeEntropy_le_neg_log_of_smul_le (isDensityMatrix_pureState hn).partialTraceRight
    (S.isDensityMatrix_averagedCheckedMarginalAlice C p).posSemidef hweight hle

end Cslib.PCP.QuantumStrategy
