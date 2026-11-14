/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter
public import CslibFrontierTests.OracleDescription

/-!
# Tests for the fixed-channel oracle interpreter word program

This module reuses the adaptive description client from `OracleDescription`. Its second request
contains the first reply, so the interpreter exercises reply decoding, a non-head table lookup and
finite-channel dispatch before returning the second reply. The encoded reply budget is large enough
for either one-symbol unary answer.

These tests check source semantics and the structural coin/call/request coordinates. They do not
claim a native interpreter clock, workspace or static program size; those belong to the named
machine witness that realizes this word program.

The boundary checks cover a channel-count mismatch, a zero source clock and a malformed framed-list
request. Each returns locally without changing the shared handler state.
-/

@[expose] public section

namespace CslibFrontierTests.OracleInterpreter

open Cslib Cslib.Probability Turing.MultiTapePTM.Universal

namespace OD := CslibFrontierTests.OracleDescription

/-- Runtime request for the adaptive four-instruction fixture. -/
def runInput : RunInput := ⟨OD.description, 4, [], 19⟩

/-- Nineteen bits contain either encoded reply `[7]` or `[9]`. -/
theorem handler_prefix_fits : ReplyBoundsFit runInput OD.handler := by
  intro query log reply nextState hreply
  by_cases hlog : log.isEmpty
  · simp only [OD.handler, hlog, ↓reduceIte, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hreply
    rcases hreply with ⟨rfl, rfl⟩
    decide
  · simp only [OD.handler, hlog, ↓reduceIte, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hreply
    rcases hreply with ⟨rfl, rfl⟩
    decide

/-- The Boolean interpreter preserves the complete adaptive output/log law. -/
theorem run_interpreter :
    ProbOracleComp.runWith OD.handler
        ((wordCodec 1).adapt (run 1 runInput)) [] =
      PMF.pure ([9], [[], [7]]) := by
  exact (runWith_input_eq_runOracle runInput OD.handler [] handler_prefix_fits).trans
    OD.run_description

/-- The adaptive client submits only canonical requests satisfying both request coordinates. -/
theorem run_request_bounds : (run 1 runInput).QueriesSatisfy (RequestFits runInput) :=
  queriesSatisfy_run_requestBounds 1 runInput

/-- The adaptive client consumes at most its named private-coin coordinate. -/
theorem run_private_coins :
    OracleComp.IsCostBounded
        (Sum.elim (fun _ => 1) (fun _ : Fin 1 × List Bool => 0))
        (run 1 runInput) (privateCoinBound runInput) :=
  isCostBounded_run_privateCoins 1 runInput

/-- The adaptive client makes at most its named call coordinate. -/
theorem run_queries : (run 1 runInput).IsQueryBounded (queryBound runInput) :=
  isQueryBounded_run 1 runInput

/-- A fixed-channel mismatch is rejected before the shared handler is called. -/
theorem run_channel_mismatch (log : List (List ℕ)) :
    ProbOracleComp.runWith OD.handler
        ((wordCodec 0).adapt (run 0 ⟨OD.description, 4, [], 19⟩)) log =
      PMF.pure ([], log) := by
  rw [run_of_operations_ne]
  · simp only [OracleCodec.adapt_pure, ProbOracleComp.runWith_pure]
  · simp [OD.description]

/-- A zero clock returns before sampling or calling the handler. -/
theorem run_zero (log : List (List ℕ)) :
    ProbOracleComp.runWith OD.handler
        ((wordCodec 1).adapt (run 1 ⟨OD.description, 0, [], 19⟩)) log =
      PMF.pure ([], log) := by
  simp only [Turing.MultiTapePTM.Universal.run_zero, OracleCodec.adapt_pure,
    ProbOracleComp.runWith_pure]

/-- A single unmatched terminator is not a canonical framed unary-list request. -/
def malformedRequest : Fin 1 × List Bool := (0, [true])

theorem decode_malformedRequest : (wordCodec 1).decodeQuery malformedRequest = none := rfl

/-- The malformed request is answered by `[]` without changing the typed handler state. -/
theorem malformed_request_no_call (log : List (List ℕ)) :
    (wordCodec 1).wordOracle OD.handler malformedRequest log = PMF.pure ([], log) := by
  rw [wordCodec_wordOracle_of_malformed OD.handler malformedRequest decode_malformedRequest]
  rfl

/-- The adaptive fixture has four table rows, so successful execution does not reduce to a
constant head-entry lookup. -/
theorem description_table_length : OD.description.table.length = 4 := rfl

end CslibFrontierTests.OracleInterpreter
