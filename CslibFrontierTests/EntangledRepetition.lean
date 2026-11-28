/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.CheckedAnswerRegister
import CslibFrontier.Computability.PCP.TwoProverGame.EntangledRepetition
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Entangled repetition of CHSH -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped Real

example {n : ℕ} (hn : 0 < n) : (chsh.pow n).quantumValue ≤ Real.cos (π / 8) ^ 2 := by
  rw [← quantumValue_chsh]
  exact chsh.quantumValue_pow_le_of_pos hn

open Cslib.PCP (QuantumStrategy)
open Cslib.Probability.PMF (coin)
open scoped unitInterval

private noncomputable def echoStrategy :
    QuantumStrategy Bool Bool (Fin 2 → Bool) (Fin 2 → Bool) (Fin 1) (Fin 1) :=
  QuantumStrategy.ofDeterministic (fun x _ => x) (fun y _ => y)

/-- The branch with both checked answers true has weight `1 - η` when the coin
replaces Alice's true input by false and Bob's input is always true. -/
private theorem echo_weight (η : I) :
    ‖echoStrategy.averagedCheckedVector {0}
      ((coin η).bind fun erase => PMF.pure (!erase)) (PMF.pure true)
      (fun _ => true) (fun _ => true)‖ ^ 2 = 1 - (η : ℝ) := by
  classical
  have h (x : Bool) :
      ‖echoStrategy.averagedCheckedVector {0} (PMF.pure x) (PMF.pure true)
        (fun _ => true) (fun _ => true)‖ ^ 2 = if x then 1 else 0 := by
    rw [QuantumStrategy.norm_averagedCheckedVector_sq]
    simp only [PMF.pure_bind, echoStrategy, QuantumStrategy.checkedAnswers,
      QuantumStrategy.answers_ofDeterministic, PMF.pure_map, Prod.map_apply, PMF.pure_apply]
    cases x
    · have hn : (fun _ : ({0} : Finset (Fin 2)) => true) ≠ fun _ => false :=
        fun e => Bool.noConfusion (congrFun e ⟨0, by simp⟩)
      simp [Prod.mk.injEq, hn]
    · simp
  have hmix : (fun erase : Bool => PMF.pure (!erase)) =
      (fun erase => if erase then PMF.pure false else PMF.pure true) := by
    funext erase
    cases erase <;> rfl
  rw [hmix, QuantumStrategy.norm_averagedCheckedVector_sq_coin, h, h]
  simp

open Cslib.Quantum (normalizeDensity partialTraceRight pureState relativeEntropy)

/-- A noisy question with erase probability `η < 1` gives an entropy bound in
terms of the surviving branch weight `1 - η`. -/
example (η : I) (hη : (η : ℝ) < 1) :
    relativeEntropy
      (partialTraceRight (pureState (echoStrategy.normalizedCheckedVector {0}
        ((coin η).bind fun erase => PMF.pure (!erase)) (PMF.pure true)
        (fun _ => true) (fun _ => true))))
      (echoStrategy.averagedCheckedMarginalAlice {0}
        ((coin η).bind fun erase => PMF.pure (!erase))) ≤
      ((-Real.log (1 - (η : ℝ)) : ℝ) : WithTop ℝ) := by
  classical
  let p := (coin η).bind fun erase => PMF.pure (!erase)
  let q := PMF.pure true
  let a : ({0} : Finset (Fin 2)) → Bool := fun _ => true
  let b : ({0} : Finset (Fin 2)) → Bool := fun _ => true
  have hw : ((p.bind fun x => q.bind fun y => echoStrategy.checkedAnswers {0} x y) (a, b)).toReal =
      1 - (η : ℝ) := (echoStrategy.norm_averagedCheckedVector_sq {0} p q a b).symm.trans
        (echo_weight η)
  have h : (a, b) ∈ (p.bind fun x => q.bind fun y => echoStrategy.checkedAnswers {0} x y).support :=
    (PMF.mem_support_iff _ _).mpr (fun hz => by
      rw [hz, ENNReal.toReal_zero] at hw
      exact (sub_pos.mpr hη).ne' hw.symm)
  simpa only [hw] using
    echoStrategy.relativeEntropy_normalizedCheckedVector_partialTraceRight_le {0} p q a b h

/-- Keeping Bob's true label and the corresponding checked answers has event mass
`η` and costs at most `log 4 - log η` nats against the uniform answer reference. -/
example (η : I) (hη : 0 < (η : ℝ)) :
    let C : Finset (Fin 2) := {0}
    let w (y : Bool) : Set ((C → Bool) × (C → Bool)) :=
      if y then {(fun _ => true, fun _ => true)} else ∅
    relativeEntropy
      (normalizeDensity (echoStrategy.checkedAnswerRegister C (fun _ => PMF.pure true)
        (coin η) PMF.pure w))
      (echoStrategy.checkedAnswerProductReference C (fun _ => PMF.pure true) (coin η)) ≤
      ((Real.log 4 - Real.log (η : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  dsimp only
  let C : Finset (Fin 2) := {0}
  let ans : (C → Bool) × (C → Bool) := (fun _ => true, fun _ => true)
  let w (y : Bool) : Set ((C → Bool) × (C → Bool)) := if y then {ans} else ∅
  let p (_ : Bool) := PMF.pure true
  have he : {z : Bool × ((C → Bool) × (C → Bool)) | z.2 ∈ w z.1} = {(true, ans)} := by
    ext ⟨y, z⟩
    cases y <;> simp [w]
  have hw : ((echoStrategy.checkedAnswersWithLabel C p (coin η) PMF.pure).toOuterMeasure
      {z | z.2 ∈ w z.1}).toReal = (η : ℝ) := by
    rw [he, PMF.toOuterMeasure_apply_singleton, echoStrategy.checkedAnswersWithLabel_apply]
    simp [ans, p, echoStrategy, QuantumStrategy.checkedAnswers,
      QuantumStrategy.answers_ofDeterministic, PMF.pure_map, Prod.map_apply, PMF.pure_apply,
      Cslib.Probability.PMF.coin_apply_toReal]
  have hc : Fintype.card ((C → Bool) × (C → Bool)) = 4 := by
    simp [Fintype.card_prod, C]
  have h := echoStrategy.relativeEntropy_normalize_checkedAnswerRegister_le C
    p (coin η) PMF.pure w (hw.symm ▸ hη)
  simpa only [hw, hc, Nat.cast_ofNat] using h

/-- Independent play gives the lower end of the interval for repeated CHSH. -/
example (n : ℕ) : (Real.cos (π / 8) ^ 2) ^ n ≤ (chsh.pow n).quantumValue := by
  rw [← quantumValue_chsh]
  exact chsh.pow_quantumValue_le_quantumValue_pow n
