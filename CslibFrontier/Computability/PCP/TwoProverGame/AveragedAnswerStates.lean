/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PlayerSwap
public import CslibFrontier.Foundations.Quantum.POVM.OutcomeVector
public import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker
import CslibFrontier.Foundations.Quantum.DensityMatrix.PartialTracePairing
import CslibFrontier.Foundations.Quantum.POVM.Postprocessing
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Averaged checked-answer states

Restrict each player's measurement to the answers on a checked set. Given independent laws
of the full questions, average the two restricted measurements on their respective spaces.
The square-root branch for a pair of checked answers has squared norm equal to the
probability of those answers in the original strategy with questions drawn from those laws.

This is the measurement construction in
[Bavarian, Vidick and Yuen, §4.4][BavarianVidickYuen2022], equations (12)–(21). The two local
question laws are parameters, so the same identity applies to fixed questions and to a noisy
mixture of anchor and ordinary questions.

## Main results

* `measure_averagedChecked`: the averaged effects produce the original checked-answer
  distribution under independent questions.
* `norm_averagedCheckedVector_sq`: the corresponding identity for the state norm.
* `partialTraceRight_averagedCheckedVector_swap`: exchanging the players exchanges the
  two marginals of the checked branch.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Quantum Matrix
open scoped Kronecker unitInterval

variable {τ X Y A B ι κ : Type*} [Fintype τ] [DecidableEq τ] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (S : QuantumStrategy X Y (τ → A) (τ → B) ι κ) (C : Finset τ)

open Classical in
/-- Alice's measurement with only her checked answers retained. -/
noncomputable def checkedAlice (x : X) : POVM (C → A) ι :=
  (S.alice x).map fun a i => a i

open Classical in
/-- Bob's measurement with only his checked answers retained. -/
noncomputable def checkedBob (y : Y) : POVM (C → B) κ :=
  (S.bob y).map fun b i => b i

/-- The law obtained by keeping each player's answers on the checked coordinates. -/
@[expose] noncomputable def checkedAnswers (x : X) (y : Y) : PMF ((C → A) × (C → B)) :=
  (S.answers x y).map (Prod.map (fun a i => a i) (fun b i => b i))

/-- The local checked measurements give the pushforward of the full answer law. -/
theorem measure_checked (x : X) (y : Y) :
    ((S.checkedAlice C x).kronecker (S.checkedBob C y)).measure S.state S.norm_state =
      S.checkedAnswers C x y := by
  classical
  rw [checkedAlice, checkedBob, POVM.kronecker_map, POVM.measure_map]
  rfl

variable [Fintype X] [Fintype Y]

/-- Average the two players' checked measurements over independent full questions. -/
noncomputable def averagedChecked (p : PMF X) (q : PMF Y) : POVM ((C → A) × (C → B)) (ι × κ) :=
  (POVM.mixture p (S.checkedAlice C)).kronecker (POVM.mixture q (S.checkedBob C))

/-- Drawing independent local questions and retaining the checked answers has the same
distribution as measuring the state with the averaged checked effects. -/
theorem measure_averagedChecked (p : PMF X) (q : PMF Y) :
    (S.averagedChecked C p q).measure S.state S.norm_state =
      p.bind fun x => q.bind fun y => S.checkedAnswers C x y := by
  rw [averagedChecked, POVM.kronecker_mixture, POVM.measure_mixture, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, measure_checked]

/-- The unnormalized branch after the joint averaged checked measurement. -/
noncomputable def averagedCheckedVector (p : PMF X) (q : PMF Y)
    (a : C → A) (b : C → B) : EuclideanSpace ℂ (ι × κ) :=
  (S.averagedChecked C p q).outcomeVector S.state (a, b)

/-- The branch can be formed by applying square roots of the two local averaged effects. -/
theorem averagedCheckedVector_eq (p : PMF X) (q : PMF Y) (a : C → A) (b : C → B) :
    S.averagedCheckedVector C p q a b = WithLp.toLp 2
      (((POVM.mixture p (S.checkedAlice C)).sqrtEffect a ⊗ₖ
        (POVM.mixture q (S.checkedBob C)).sqrtEffect b) *ᵥ S.state.ofLp) := by
  rw [averagedCheckedVector, POVM.outcomeVector, averagedChecked, POVM.sqrtEffect_kronecker]

/-- The Alice marginal of the exchanged checked-answer branch is the original Bob marginal. -/
theorem partialTraceRight_averagedCheckedVector_swap (p : PMF X) (q : PMF Y)
    (a : C → A) (b : C → B) :
    partialTraceRight (pureState (S.swap.averagedCheckedVector C q p b a)) =
      partialTraceLeft (pureState (S.averagedCheckedVector C p q a b)) := by
  let e := Equiv.prodComm κ ι
  have hv : (S.swap.averagedCheckedVector C q p b a).ofLp =
      (S.averagedCheckedVector C p q a b).ofLp ∘ e := by
    rw [averagedCheckedVector_eq, averagedCheckedVector_eq]
    let M := (POVM.mixture p (S.checkedAlice C)).sqrtEffect a
    let N := (POVM.mixture q (S.checkedBob C)).sqrtEffect b
    change ((N ⊗ₖ M) *ᵥ (S.state.ofLp ∘ e)) = ((M ⊗ₖ N) *ᵥ S.state.ofLp) ∘ e
    rw [← submatrix_kronecker_prodComm, submatrix_mulVec_equiv, Function.comp_assoc,
      e.self_comp_symm, Function.comp_id]
  rw [← partialTraceRight_reindex_prodComm]
  congr 1
  ext i j
  simp only [pureState_apply, hv, reindex_apply, submatrix_apply, Equiv.prodComm_symm,
    Function.comp_apply, e]

/-- The squared norm of the branch is the probability of the checked answer pair
in the independently sampled experiment. -/
theorem norm_averagedCheckedVector_sq (p : PMF X) (q : PMF Y) (a : C → A) (b : C → B) :
    ‖S.averagedCheckedVector C p q a b‖ ^ 2 =
      ((p.bind fun x => q.bind fun y => S.checkedAnswers C x y) (a, b)).toReal := by
  rw [← measure_averagedChecked, POVM.measure_apply, ENNReal.toReal_ofReal
    (POVM.prob_nonneg _ _ _), averagedCheckedVector, POVM.norm_outcomeVector_sq]

/-- If a coin selects between two laws for Alice's questions, the squared norm of
the resulting branch is the convex combination of the two squared norms. This gives
the noisy-anchor normalization identity of BVY equation (21). -/
theorem norm_averagedCheckedVector_sq_coin (η : I) (p₀ p₁ : PMF X) (q : PMF Y)
    (a : C → A) (b : C → B) :
    ‖S.averagedCheckedVector C
      ((Probability.PMF.coin η).bind fun anchor => if anchor then p₀ else p₁) q a b‖ ^ 2 =
        (η : ℝ) * ‖S.averagedCheckedVector C p₀ q a b‖ ^ 2 +
          (1 - (η : ℝ)) * ‖S.averagedCheckedVector C p₁ q a b‖ ^ 2 := by
  simp only [norm_averagedCheckedVector_sq, PMF.bind_bind]
  rw [Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
  simp only [Probability.PMF.coin_apply_toReal, Bool.false_eq_true, ite_true, ite_false]

/-- Normalize the branch using the inverse of its norm. A branch of zero weight stays zero. -/
noncomputable def normalizedCheckedVector (p : PMF X) (q : PMF Y)
    (a : C → A) (b : C → B) : EuclideanSpace ℂ (ι × κ) :=
  let v := S.averagedCheckedVector C p q a b
  ‖v‖⁻¹ • v

/-- Recover an unnormalized branch from its normalized vector and original norm.
The identity also holds for a zero-weight branch. -/
theorem averagedCheckedVector_eq_norm_smul_normalized
    (p : PMF X) (q : PMF Y) (a : C → A) (b : C → B) :
    S.averagedCheckedVector C p q a b =
      ‖S.averagedCheckedVector C p q a b‖ • S.normalizedCheckedVector C p q a b := by
  simpa only [normalizedCheckedVector, NormedSpace.normalize] using
    (NormedSpace.norm_smul_normalize (S.averagedCheckedVector C p q a b)).symm

/-- A possible pair of checked answers gives a normalized conditional state. -/
theorem norm_normalizedCheckedVector (p : PMF X) (q : PMF Y) (a : C → A) (b : C → B)
    (h : (a, b) ∈ (p.bind fun x => q.bind fun y => S.checkedAnswers C x y).support) :
    ‖S.normalizedCheckedVector C p q a b‖ = 1 := by
  have hmass : 0 < ((p.bind fun x => q.bind fun y => S.checkedAnswers C x y) (a, b)).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp h) (PMF.apply_ne_top _ _)
  have hnorm : ‖S.averagedCheckedVector C p q a b‖ ≠ 0 := by
    have hsq := S.norm_averagedCheckedVector_sq C p q a b
    exact fun hzero => by rw [hzero, zero_pow (by decide)] at hsq; linarith
  simpa only [normalizedCheckedVector, NormedSpace.normalize] using
    NormedSpace.norm_normalize (norm_ne_zero_iff.mp hnorm)

end Cslib.PCP.QuantumStrategy
