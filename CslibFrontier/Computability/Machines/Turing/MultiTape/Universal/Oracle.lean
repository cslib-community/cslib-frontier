/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Basic

/-!
# Finite multi-tape oracle descriptions

Extend the universal machine's finite transition table with a unary query tape. An ordinary
instruction can append a tally symbol to that tape in addition to updating the work tapes.
A query instruction asks whether the tally length belongs to the oracle and selects a successor
state from the answer. It clears the query tape and leaves the other tapes in place.

Since the query tape is write-only and unary, the configuration stores only its length. The input
and output use the same words as the ordinary universal simulator. A missing transition halts.
The construction is an explicit oracle-machine variant of the existing simulator.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- A local instruction of a deterministic machine with a unary membership oracle. -/
inductive OracleInstruction where
  /-- Apply the ordinary tape action and optionally append a tally to the query tape. -/
  | step (action : Act) (tally : Bool)
  /-- Submit the query tape and resume in the state chosen by the membership bit. -/
  | query (yes no : ℕ)

/-- An oracle Turing machine description, with the ordinary scanned-symbol keys. -/
structure OracleDesc where
  /-- The number of work tapes, excluding the input, output and query tape. -/
  tapes : ℕ
  /-- The initial control state. -/
  initial : ℕ
  /-- The first matching table entry supplies the instruction. -/
  table : List (Key × OracleInstruction)

namespace OracleDesc

/-- A finite snapshot of the oracle machine. Ordinary work tapes use the universal
simulator's zippers. -/
structure Config where
  /-- The finite control, input head and work tapes. -/
  ordinary : SCfg
  /-- The number of tallies written to the pending query tape. -/
  queryLength : ℕ
  /-- The word emitted so far. -/
  output : List ℕ

/-- Start with the initial state and empty work, query and output tapes. -/
@[expose] def init (M : OracleDesc) : Config :=
  ⟨Universal.init ⟨M.tapes, M.initial, []⟩, 0, []⟩

/-- Apply a selected local instruction to the tapes and control. Only a query uses the answer. -/
@[expose] def Config.applyInstruction (c : Config) (x : List ℕ) (answer : Bool) :
    OracleInstruction → Config
  | .step action tally =>
    ⟨action.apply x c.ordinary, c.queryLength + tally.toNat,
      c.output ++ action.output.toList⟩
  | .query yes no =>
    ⟨{ c.ordinary with state := some (bif answer then yes else no) }, 0, c.output⟩

/-- Given an answer to the current query tape, take a single instruction.
An ordinary instruction ignores the supplied bit. The halted configuration is absorbing. -/
@[expose] def stepWith (M : OracleDesc) (x : List ℕ) (c : Config) (answer : Bool) : Config :=
  match c.ordinary.state with
  | none => c
  | some q =>
    match M.table.find? (·.1 = c.ordinary.key x q) with
    | none => { c with ordinary := { c.ordinary with state := none } }
    | some entry => c.applyInstruction x answer entry.2

/-- One instruction relative to the given membership oracle. -/
@[expose] def step (M : OracleDesc) (oracle : ℕ → Bool) (x : List ℕ) (c : Config) : Config :=
  M.stepWith x c (oracle c.queryLength)

/-- Inspect the machine after the specified number of steps. -/
@[expose] def runFor (M : OracleDesc) (oracle : ℕ → Bool) (x : List ℕ)
    (fuel : ℕ) : Config :=
  (M.step oracle x)^[fuel] M.init

/-- Halting absorbs every further step. -/
theorem step_halted (M : OracleDesc) (oracle : ℕ → Bool) (x : List ℕ) {c : Config}
    (h : c.ordinary.state = none) : M.step oracle x c = c := by
  simp [step, stepWith, h]

end OracleDesc

end Turing.MultiTapeTM.Universal
