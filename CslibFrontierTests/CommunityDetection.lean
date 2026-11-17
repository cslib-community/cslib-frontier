/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Algorithms.CommunityDetection.Asymptotics
import CslibFrontier.Algorithms.CommunityDetection.PolyTime
import Mathlib.Tactic.NormNum

/-!
# Clients of the stochastic block model recovery theorem

The finite example has nondegenerate probabilities `p = 3/4`, `q = 1/4`, and a vertex count
satisfying the conservative size threshold. It applies the complete search experiment theorem,
including its actual graph distribution, under an arbitrary prior. This is a theorem client,
not an execution of an eigensolver on a graph with 12,864 vertices. The native finite example
uses fixed integer parameters and the improved cubic size condition.

The other examples check the exact-signal cleanup, absence of label information when `p = q`,
and the asymptotic guarantee through ordinary imports. The computational client instantiates
the actual native recovery theorem at the same nondegenerate probabilities and independent
uniform hidden labels, obtaining one fixed program for the whole graph family.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CommunityDetection

open Cslib Cslib.Algorithms.CommunityDetection Cslib.Probability.StochasticBlockModel
open Cslib.BitString Finset Filter Real
open Cslib.Probability Turing.MultiTapeTM
open scoped unitInterval Topology

private noncomputable def within : I := ⟨3 / 4, by constructor <;> norm_num⟩

private noncomputable def between : I := ⟨1 / 4, by constructor <;> norm_num⟩

private noncomputable def uniformLabels (n : ℕ) : PMF (Fin n → Bool) :=
  PMF.pi fun _ => PMF.coin ⟨1 / 2, by constructor <;> norm_num⟩

open scoped Classical in
/-- A nondegenerate numerical instance satisfies every premise of the finite theorem. -/
example (prior : PMF (Fin 12864 → Bool)) :
    ((searchProblem within between prior).experiment
      (fun G => PMF.pure (recoverSpectral within between G)) false).toReal ≤
        2 * exp (-12864) + 25728 * exp (-402) := by
  have h := searchProblem_recoverSpectral_failure_le within between prior
    (by norm_num [within, between]) (by norm_num [gap, within, between])
  norm_num [gap, within, between] at h ⊢
  exact h

open scoped Classical in
/-- Fixed centering parameters satisfy the improved native size condition at a concrete
nondegenerate probability pair, uniformly over the hidden-label prior. -/
example (prior : PMF (Fin 52461568 → Bool)) :
    ((searchProblem within between prior).experiment
      (fun G => PMF.pure (fun i : Fin 52461568 =>
        (recoverInput ⟨128, 8192⟩ (DenseGraphInput.ofGraph G)).getD i.val false)) false).toReal ≤
      2 * exp (-52461568) + 104923136 * exp (-1639424) := by
  have h := recoverInput_failure_le ⟨128, 8192⟩ within between prior
    (by norm_num [within, between]) (by norm_num [gap, within, between])
    (by norm_num)
    (by norm_num [Cslib.Probability.StochasticBlockModel.midpoint, within, between])
    (by norm_num)
  norm_num [gap, within, between] at h ⊢
  exact h

/-- Equal within-community and between-community probabilities reveal no labels in the law. -/
example {n : ℕ} (p : I) (g h : Fin n → Bool) : graphLaw p p g = graphLaw p p h := by
  simp [graphLaw, coinLaw, edgeProbability]

/-- A perfect rank-one sign matrix is a fixed point of the cleanup step. -/
example (g : Fin 3 → Bool) :
    cleanup (Matrix.vecMulVec (fun i => signVal (g i)) (fun i => signVal (g i))) g = g := by
  apply cleanup_eq_of_margin (C := 1)
  · intro i j
    simp [Matrix.vecMulVec, abs_mul]
  · intro i
    simp only [hammingDist_self, Nat.cast_zero, mul_zero, Matrix.vecMulVec]
    rw [Finset.mul_sum]
    have hterm (j : Fin 3) :
        signVal (g i) * (signVal (g i) * signVal (g j) * signVal (g j)) = 1 := by
      calc
        _ = (signVal (g i) * signVal (g i)) *
          (signVal (g j) * signVal (g j)) := by ring
        _ = 1 := by rw [signVal_mul_self, signVal_mul_self, one_mul]
    simp [hterm]

open scoped Classical in
/-- The asymptotic theorem concerns the actual failure mass in the generic search experiment. -/
example (p q : I) (prior : ∀ n, PMF (Fin n → Bool)) (hpq : (q : ℝ) < p) :
    Tendsto (fun n => (searchProblem p q (prior n)).experiment
      (fun G => PMF.pure (recoverSpectral p q G)) false) atTop (𝓝 0) :=
  tendsto_searchProblem_recoverSpectral_failure p q prior hpq

open scoped Classical in
/-- A single fixed native program recovers uniformly random hidden labels for the entire
nondegenerate dense SBM family. Both encodings and the actual represented output are explicit. -/
example : ∃ params : PowerParameters,
    IsPPTOn encDenseGraphInput (encList encBool) (fun x => pure (recoverInput params x)) ∧
    Tendsto (fun n => (searchProblem within between (uniformLabels n)).experiment
      (fun G => PMF.pure (fun i : Fin n =>
        (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false)) false)
      atTop (𝓝 0) := by
  obtain ⟨params, hprogram, hsuccess⟩ := exists_recoverInput_ppt_tendsto_failure within between
    (by norm_num [within, between])
  exact ⟨params, hprogram, hsuccess uniformLabels⟩

end CslibFrontierTests.CommunityDetection
