/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Time
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords

/-!
# Explicit halting time and query contracts for oracle programs

These numerical contracts describe one finite machine, its supported halting configurations,
and the complete joint output/external-state law. They contain no clean-phase compiler witness.
The `Oracle.Time` facade exports their machine-construction and quantitative closure theorems.

## Main definitions

* `ComputesOracleInTimeOn`, `ComputesOracleInTime`: explicit halting clocks.
* `ComputesOracleInTimeAndQueriesOn`, `ComputesOracleInTimeAndQueries`: separate query bounds.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

/-- One finite-control oracle machine realizes the joint output and external-state distribution of
`program` within `t a` steps across all shared stateful handlers, and has halted on every supported
execution at step `t a`. -/
@[expose] def ComputesOracleInTimeOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool) (t : α → ℕ)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> program a) s =
        ProbOracleComp.runWith oracle (machine.runOracle (t a) (input a)) s ∧
      ∀ final ∈ (ProbOracleComp.runWith oracle
          (machine.runOracleConfigFrom (t a) (machine.initialConfig (input a))) s).support,
        final.1.tapes.state = none

/-- Uniform halting oracle realization on a unary security parameter and auxiliary word, indexed by
`(n, aux.length)`. -/
@[expose] def ComputesOracleInTime {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (t : ℕ → ℕ → ℕ)
    (program : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTimeOn (encPair encUnary encBits) output
    (fun input => t input.1 input.2.length) (fun input => program input.1 input.2)

/-- Joint explicit `(t, q)` realization: `program` is realized by a halting oracle machine within
`t a` steps and makes at most `q a` external queries on every execution path. -/
@[expose] def ComputesOracleInTimeAndQueriesOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool) (t q : α → ℕ)
    (program : α → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTimeOn input output t program ∧
    ∀ a, (program a).IsQueryBounded (q a)

/-- Parameterized joint `(t, q)` time-and-query realization on a unary security parameter and
auxiliary word. -/
@[expose] def ComputesOracleInTimeAndQueries {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (t q : ℕ → ℕ → ℕ)
    (program : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTime output t program ∧
    ∀ n aux, (program n aux).IsQueryBounded (q n aux.length)

end Cslib.Probability
