/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter.Native
public import CslibFrontierTests.OracleDescription

/-!
# Tests for the fixed-channel oracle interpreter word program

This module reuses the adaptive description client from `OracleDescription`. Its second request
contains the first reply, so the interpreter exercises reply decoding, a non-head table lookup and
finite-channel dispatch before returning the second reply. The encoded reply budget is large enough
for either one-symbol unary answer.

These tests check source semantics, structural coin/call/request coordinates, and the retained
native witness's open semantics, framed runtime-input partition and static structural bound.

The boundary checks cover a channel-count mismatch, a zero source clock and a malformed framed-list
request. Each returns locally without changing the shared handler state.
-/

@[expose] public section

namespace CslibFrontierTests.OracleInterpreter

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapePTM.Universal
open Turing.MultiTapePTM.Universal.NativeInterpreter

/-- Runtime request for the adaptive four-instruction fixture. -/
def runInput : RunInput := ⟨CslibFrontierTests.OracleDescription.description, 4, [], 19⟩

/-- Nineteen bits contain either encoded reply `[7]` or `[9]`. -/
theorem handler_prefix_fits :
    ReplyPrefixFits CslibFrontierTests.OracleDescription.handler
      runInput.fuel runInput.replyBits := by
  intro query log reply nextState hreply
  by_cases hlog : log.isEmpty
  · simp only [CslibFrontierTests.OracleDescription.handler, hlog,
      PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hreply
    rcases hreply with ⟨rfl, rfl⟩
    decide
  · simp only [CslibFrontierTests.OracleDescription.handler, hlog,
      PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hreply
    rcases hreply with ⟨rfl, rfl⟩
    decide

/-- The second supported reply needs nineteen bits. An eighteen-bit budget fails the
typed correspondence's prefix premise on a reachable, nonempty log. -/
example : ¬ ReplyPrefixFits CslibFrontierTests.OracleDescription.handler 4 18 := by
  intro hfit
  have h := hfit (0, [7]) [[]] [9] [[], [7]] (by
    simp [CslibFrontierTests.OracleDescription.handler])
  exact (by decide : ¬ (encList encUnary ([9] : List ℕ)).length ≤ 18) h

/-- The Boolean interpreter preserves the complete adaptive output/log law. -/
theorem run_interpreter :
    ProbOracleComp.runWith CslibFrontierTests.OracleDescription.handler
        ((wordCodec 1).adapt (run 1 runInput)) [] =
      PMF.pure ([9], [[], [7]]) := by
  exact (runWith_eq_runOracle runInput
    CslibFrontierTests.OracleDescription.handler [] handler_prefix_fits).trans
      CslibFrontierTests.OracleDescription.run_description

/-- The adaptive client submits only canonical requests satisfying both request coordinates. -/
theorem run_request_bounds : (run 1 runInput).QueriesSatisfy (RequestFits runInput) :=
  queriesSatisfy_run_requestBounds 1 runInput

/-- The adaptive client consumes at most its named private-coin coordinate. -/
theorem run_private_coins :
    OracleComp.IsCostBounded
        (Sum.elim (fun _ => 1) (fun _ : Fin 1 × List Bool => 0))
        (run 1 runInput) runInput.fuel :=
  isCostBounded_run_privateCoins 1 runInput

/-- The adaptive client makes at most its named call coordinate. -/
theorem run_queries : (run 1 runInput).IsQueryBounded runInput.fuel :=
  isQueryBounded_run 1 runInput

/-- A fixed-channel mismatch is rejected before the shared handler is called. -/
theorem run_channel_mismatch (log : List (List ℕ)) :
    ProbOracleComp.runWith (fun query : Fin 0 × List ℕ => Fin.elim0 query.1)
        ((wordCodec 0).adapt
          (run 0 ⟨CslibFrontierTests.OracleDescription.description, 4, [], 19⟩)) log =
      PMF.pure ([], log) := by
  rw [run_of_operations_ne]
  · simp only [OracleCodec.adapt_pure, ProbOracleComp.runWith_pure]
  · simp [CslibFrontierTests.OracleDescription.description]

/-- A zero clock returns before sampling or calling the handler. -/
theorem run_zero (log : List (List ℕ)) :
    ProbOracleComp.runWith CslibFrontierTests.OracleDescription.handler
        ((wordCodec 1).adapt
          (run 1 ⟨CslibFrontierTests.OracleDescription.description, 0, [], 19⟩)) log =
      PMF.pure ([], log) := by
  simp only [Turing.MultiTapePTM.Universal.run_zero, OracleCodec.adapt_pure,
    ProbOracleComp.runWith_pure]

/-- A single unmatched terminator is not a canonical framed unary-list request. -/
def malformedRequest : Fin 1 × List Bool := (0, [true])

theorem decode_malformedRequest : (wordCodec 1).decodeQuery malformedRequest = none := by
  simp [wordCodec, malformedRequest, PartialDecoder.ofDecoder, PartialDecoder.checked,
    unaryListDecoder, Decoder.list, Decoder.unary,
    frames_of_ne_nil, unframe, dropFrame, encList_cons, encList_nil, encUnary_apply, frame]

/-- The malformed request is answered by `[]` without changing the typed handler state. -/
theorem malformed_request_no_call (log : List (List ℕ)) :
    (wordCodec 1).wordOracle CslibFrontierTests.OracleDescription.handler malformedRequest log =
      PMF.pure ([], log) := by
  rw [OracleCodec.wordOracle_of_decodeQuery_eq_none (wordCodec 1)
    CslibFrontierTests.OracleDescription.handler
    decode_malformedRequest]
  rfl

/-- The adaptive fixture has four table rows, so successful execution does not reduce to a
constant head-entry lookup. -/
theorem description_table_length :
    CslibFrontierTests.OracleDescription.description.table.length = 4 := rfl

/-! ### Retained native interpreter -/

/-- The actual retained finite-control machine, after its word interface and output are decoded,
has the adaptive fixture's expected result and final shared log. -/
theorem native_interpreter_typed :
    ProbOracleComp.runWith CslibFrontierTests.OracleDescription.handler
        ((wordCodec runInput.desc.operations).adapt
          (unaryListDecoder.decode <$>
            (artifact runInput.desc.operations).machine.runOracle
              ((artifact runInput.desc.operations).time runInput) (eRunInput runInput))) [] =
      PMF.pure ([9], [[], [7]]) := by
  calc
    _ = ProbOracleComp.runWith CslibFrontierTests.OracleDescription.handler
        (runInput.desc.runOracle runInput.fuel runInput.input) [] :=
      runWith_artifact_eq_runOracle runInput
        CslibFrontierTests.OracleDescription.handler [] handler_prefix_fits
    _ = PMF.pure ([9], [[], [7]]) := by
      simpa only [runInput] using CslibFrontierTests.OracleDescription.run_description

/-- The actual runtime word charges the supplied description once, including the `encPair`
framing overhead, and then the clock/input/reply-budget tail. -/
theorem run_input_size_partition :
    runInputSize runInput =
      2 * suppliedDescSize runInput + 1 + runParameterSize runInput :=
  runInputSize_eq_framed runInput

/-- A machine with no installed channel rejects the one-channel description before calling
a handler. Its only result is the encoding of the empty source output. -/
example (log : List (List ℕ)) :
    ProbOracleComp.runWith (fun q : Fin 0 × List Bool => Fin.elim0 q.1)
        ((artifact 0).machine.runOracle ((artifact 0).time runInput) (eRunInput runInput)) log =
      PMF.pure (encList encUnary [], log) := by
  rw [Turing.MultiTapePTM.Internal.NativeOracleProgram.time,
    ((artifact 0).computes runInput).runOracle, run_of_operations_ne 0 runInput (by decide)]
  simp

end CslibFrontierTests.OracleInterpreter
