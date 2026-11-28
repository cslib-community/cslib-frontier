/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Game.Distributional
import CslibFrontier.Crypto.Computational.Basic
import CslibFrontier.Crypto.Primitives.PRG.Circuit
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
Checks that the neutral problem data instantiate both uniform PPT programs and actual circuit
families. Reading the first bit perfectly distinguishes the two point-mass laws in each model.
The circuit test has zero gates because output wires are free. Equal laws, conversely, satisfy
the PPT indistinguishability predicate. All semantic tests use a realizer for the whole family.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DistributionalDistinguishing

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open Circuits Circuits.Boolean
open scoped NNReal

private noncomputable def separatedWords (_ : ℕ) : DistinguishingProblem (List Bool) :=
  ⟨PMF.pure [false], PMF.pure [true]⟩

private def firstBit : Distinguisher := fun _ input => pure (input.headD false)

private theorem firstBit_ppt : IsPPT encBool firstBit :=
  ((ComputableInPolyTime.headD false).comp
    (ComputableInPolyTime.snd encUnary encBits)).isPPTOn

private noncomputable def wordEval (program : Distinguisher) (n : ℕ) (input : List Bool) :
    PMF Bool := ProbComp.eval (program n input)

example : IsPPTTest (wordEval firstBit) := isPPTTest_eval.mpr firstBit_ppt

private theorem firstBit_advantage (n : ℕ) :
    Game.advantage (Distributional.game separatedWords wordEval false firstBit n)
      (Distributional.game separatedWords wordEval true firstBit n) = 1 := by
  simp [Distributional.game, DistinguishingProblem.experiment, separatedWords, wordEval,
    firstBit, ProbComp.eval_pure, Game.advantage, Game.succProbability]

example : ¬ Game.Indistinguishable
    (Distributional.game separatedWords wordEval false)
    (Distributional.game separatedWords wordEval true) (IsPPT encBool) := by
  intro h
  apply not_negligible_const (c := 1) one_ne_zero
  simpa only [firstBit_advantage] using h firstBit firstBit_ppt

example : ¬ ComputationallyIndistinguishable (fun n => (separatedWords n).nullDist)
    (fun n => (separatedWords n).alternativeDist) := by
  rw [computationallyIndistinguishable_iff_tests]
  intro h
  apply not_negligible_const (c := 1) one_ne_zero
  have hneg := h (wordEval firstBit) (isPPTTest_eval.mpr firstBit_ppt)
  change Negligible (fun n =>
    Game.advantage (Distributional.game separatedWords wordEval false firstBit n)
      (Distributional.game separatedWords wordEval true firstBit n)) at hneg
  simpa only [firstBit_advantage] using hneg

example (X : ℕ → PMF (List Bool)) :
    Game.Indistinguishable
      (Distributional.game (fun n => ⟨X n, X n⟩) wordEval false)
      (Distributional.game (fun n => ⟨X n, X n⟩) wordEval true) (IsPPT encBool) :=
  Game.Indistinguishable.refl _ _

private def firstWire (n : ℕ) : Circuit signature (n + 1) 1 :=
  Circuit.wiring signature (fun _ => 0)

private noncomputable def circuitEval (C : ∀ n, Circuit signature (n + 1) 1)
    (n : ℕ) (input : BitString (n + 1)) : PMF Bool :=
  PMF.pure ((C n).eval interpretation input 0)

private def WithinCircuitSize (n size : ℕ) (C : ∀ n, Circuit signature (n + 1) 1) : Prop :=
  (C n).size ≤ size

private noncomputable def separatedBits (n : ℕ) : DistinguishingProblem (BitString (n + 1)) :=
  ⟨PMF.pure (fun _ => false), PMF.pure (fun _ => true)⟩

example (n : ℕ) : WithinCircuitSize n 0 firstWire := by
  simp [WithinCircuitSize, firstWire]

example (n : ℕ) : PRG.IsCircuitTest 0 (circuitEval firstWire n) := by
  apply (PRG.isCircuitTest_iff_exists_circuit _).mpr
  exact ⟨firstWire n, by simp [firstWire], rfl⟩

private theorem firstWire_advantage (n : ℕ) :
    Game.advantage (Distributional.game separatedBits circuitEval false firstWire n)
      (Distributional.game separatedBits circuitEval true firstWire n) = 1 := by
  simp [Distributional.game, DistinguishingProblem.experiment, separatedBits, circuitEval,
    firstWire, Game.advantage, Game.succProbability]

example : ¬ Game.IndistinguishableWithin
    (Distributional.game separatedBits circuitEval false)
    (Distributional.game separatedBits circuitEval true) WithinCircuitSize (fun _ _ => 0) := by
  intro h
  have htests := (Distributional.indistinguishableWithin_iff_realized_tests
    separatedBits circuitEval WithinCircuitSize (fun _ _ => 0)).mp h
  have hbound := htests 0 0 (circuitEval firstWire)
    ⟨firstWire, by simp [WithinCircuitSize, firstWire], rfl⟩
  change Game.advantage (Distributional.game separatedBits circuitEval false firstWire 0)
    (Distributional.game separatedBits circuitEval true firstWire 0) ≤ 0 at hbound
  rw [firstWire_advantage] at hbound
  exact not_le_of_gt zero_lt_one hbound

end CslibFrontierTests.DistributionalDistinguishing
