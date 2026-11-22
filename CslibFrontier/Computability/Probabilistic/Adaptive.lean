/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strict PPT adaptive iteration

A bounded probabilistic loop is strict PPT when its step is strict PPT and one invariant bounds
the encoded size of every reachable state. The same rule proves the final invariant. The step
may capture the original input. Constant-growth and length-nonincreasing variants supply the
size invariant automatically.

The efficiency proofs specialize the strict oracle iteration rules to empty external channels.
Embedding a closed program preserves sampling and commutes with iteration; the shared oracle
calculus supplies the clean realization and its polynomial clock. Support transport carries the
client invariant to that realization. Clients supply ordinary programs and invariants, without
machines, replay code or decoders.

## Main results

* `Cslib.Probability.IsPPTOn.iterate_spec`: certify efficiency and the final supported invariant.
* `Cslib.Probability.IsPPTOn.iterateWith_spec`: allow the step to capture the original input.
* `Cslib.Probability.IsPPTOn.iterateWith_of_bounded_growth`, `.iterate_of_bounded_growth`,
  `.iterate_of_length_le`: infer a size invariant from polynomial growth or nonincrease.

All numerical callback premises are plain certificates; invariants cover every supported prefix.

## References

Adapted from Computability/Probabilistic/Adaptive.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the strict oracle loop compiler with plain
callbacks.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {α State : Type} {input : α ↪ List Bool} {stateEncoding : State ↪ List Bool}

/-- The loop body may capture the original input; plain count and initial-state certificates
retain independent resource bounds before their strict oracle realization. -/
theorem IsPPTOn.iterateWith_spec {initial : α → State} {count : α → ℕ}
    {step : α → State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn (encPair input stateEncoding) stateEncoding (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → State → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step a state)).support, invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a state,
        state ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support →
        invariant a (count a) state := by
  have hloop := IsOraclePPTOn.iterateWith_spec hcount hinitial
    (hstep.isOraclePPTOn (Operation := Empty)) invariant hbase
    (fun a i state hi hstate next hnext => hpreserve a i state hi hstate next
      ((ProbOracleComp.support_sample _).subset hnext)) hsize hbound
  refine ⟨?_, fun a => ProbComp.iterate_invariant (count a) (step a) (initial a)
    (invariant a) (hbase a)
    (fun i hi state hinvariant => hpreserve a i state hi hinvariant)⟩
  apply IsOraclePPTOn.isPPTOn
  simpa only [ProbOracleComp.sample, OracleComp.substitute_eq_interpret,
    OracleComp.interpret_iterate] using hloop.1

/-- One invariant proves both a polynomial resource bound and the final supported postcondition.
The resource invariant must hold on every possible execution, not just with high probability.
The bound may depend on the original input and need not be computable: the proof chooses one
computable polynomial majorant for the compiled loop clock. -/
theorem IsPPTOn.iterate_spec {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → State → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step state)).support, invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a state, state ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support →
        invariant a (count a) state :=
  IsPPTOn.iterateWith_spec (step := fun _ => step) hcount hinitial
    (hstep.preprocess (ComputableInPolyTime.snd input stateEncoding))
    invariant hbase hpreserve hsize hbound

/-- Captured-input steps may grow by a polynomially bounded amount depending on that input.
The joint step certificate charges the captured input, and the growth bound covers every
supported next state from every current state. -/
theorem IsPPTOn.iterateWith_of_bounded_growth {initial : α → State} {count : α → ℕ}
    {step : α → State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn (encPair input stateEncoding) stateEncoding (fun pair => step pair.1 pair.2))
    {growth : α → ℕ} (hpoly : PolyBounded (fun a => (input a).length) growth)
    (hgrowth : ∀ a state next, next ∈ (ProbComp.eval (step a state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length + growth a) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) (step a) (initial a)) := by
  have hloop : IsOraclePPTOn (Operation := Empty) input stateEncoding
      (fun a => OracleComp.iterate (count a)
        (fun state => ProbOracleComp.sample (step a state)) (initial a)) :=
    IsOraclePPTOn.iterateWith_of_bounded_growth hcount hinitial
      (hstep.isOraclePPTOn (Operation := Empty)) hpoly
      (fun (a : α) (state next : State) hnext => hgrowth a state next
        ((ProbOracleComp.support_sample _).subset hnext))
  apply IsOraclePPTOn.isPPTOn
  simpa only [ProbOracleComp.sample, OracleComp.substitute_eq_interpret,
    OracleComp.interpret_iterate] using hloop

/-- A strict PPT step with constant growth can be repeated a polynomial number of times. -/
theorem IsPPTOn.iterate_of_bounded_growth {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    {growth : ℕ} (hgrowth : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length + growth) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  IsPPTOn.iterateWith_of_bounded_growth (step := fun _ => step) hcount hinitial
    (hstep.preprocess (ComputableInPolyTime.snd input stateEncoding))
    (.const growth) (fun _ => hgrowth)

/-- Iteration of a step that never increases its encoded state needs no extra size invariant. -/
theorem IsPPTOn.iterate_of_length_le {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  IsPPTOn.iterate_of_bounded_growth hcount hinitial hstep (growth := 0) (by simpa using hshrink)


end Cslib.Probability
