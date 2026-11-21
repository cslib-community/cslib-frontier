/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram.Forget
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram.Static

import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-! # Checked named native oracle artifacts -/

public section

open Cslib Cslib.Probability
open Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapePTM.Internal

namespace CslibFrontierTests.Internal.NativeOracleWitness

abbrev Operation := Fin 2

private def encLiftedBits : ULift.{1} (List Bool) ↪ List Bool :=
  ⟨ULift.down, fun _ _ h => ULift.ext h⟩

private def liftedAccounting : OnlineAccounting (ULift.{1} (List Bool)) where
  time := fun _ _ => 0
  workspace := fun _ _ => 0

example (input : ULift.{1} (List Bool)) : liftedAccounting.totalTime input = 0 := by
  simp [liftedAccounting, OnlineAccounting.totalTime]

private noncomputable def liftedClassifiedCompiler :=
  ClassifiedCompiler.inPhase .localStep
    (Turing.MultiTapeTM.Internal.NativeCompiler.const encLiftedBits encLiftedBits
      (ULift.up [] : ULift.{1} (List Bool)))

example (input : ULift.{1} (List Bool)) :
    liftedClassifiedCompiler.online.totalTime input =
      liftedClassifiedCompiler.compiler.time input :=
  liftedClassifiedCompiler.time_eq input

private noncomputable def liftedInputArtifact := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep
    (Turing.MultiTapeTM.Internal.NativeCompiler.const encLiftedBits encUnit ()))

example (input : ULift.{1} (List Bool)) : liftedInputArtifact.machine.ComputesTidily
    (encLiftedBits input) (liftedInputArtifact.time input) (encUnit <$> pure ()) :=
  liftedInputArtifact.computes input

private noncomputable def liftedPrepare := ClassifiedCompiler.inPhase .inputCopy
  (Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit encLiftedBits
    (ULift.up [] : ULift.{1} (List Bool)))

private noncomputable def liftedSource := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep
    (Turing.MultiTapeTM.Internal.NativeCompiler.const encLiftedBits encUnit ()))

private noncomputable def liftedPreprocessed :=
  NativeOracleProgram.preprocess liftedPrepare liftedSource

example : liftedPreprocessed.time () =
    5 * liftedPrepare.compiler.time () +
      liftedSource.time (ULift.up [] : ULift.{1} (List Bool)) + 9 :=
  NativeOracleProgram.time_preprocess liftedPrepare liftedSource ()

/-- The first and second calls use genuinely different fixed native operation artifacts. -/
noncomputable def firstArtifact :=
  NativeOracleProgram.queryTake (r := 2) (0 : Operation)

noncomputable def secondArtifact :=
  NativeOracleProgram.queryTake (r := 2) (1 : Operation)

example : firstArtifact.description.table.length = firstArtifact.observationRowCount :=
  firstArtifact.description_table_length

example : firstArtifact.staticBits ≤ firstArtifact.staticBitsBound :=
  firstArtifact.staticBits_le_staticBitsBound

example : Description.observationRowCount 1 0 2 = 27 := by decide

/-- The generic preservation theorem applies to an explicit coordinate schedule without a
dependent family of witness records. -/
example : Cslib.PolynomiallyBounded (fun _ : ℕ => 1) := by
  apply Description.staticBits_polynomiallyBounded_of_le
    (stateCard := fun _ => 1) (tapeCount := fun _ => 0) (stateTagCount := fun _ => 1)
    (operationCount := fun _ => 0) (initialTag := fun _ => 0) (maxRowBits := fun _ => 1)
  · exact Cslib.PolynomiallyBounded.const 0
  · exact Cslib.PolynomiallyBounded.const 1
  · exact Cslib.PolynomiallyBounded.const 0
  · exact Cslib.PolynomiallyBounded.const 0
  · simpa [Description.observationRowCount] using Cslib.PolynomiallyBounded.const 3
  · exact Cslib.PolynomiallyBounded.const 1
  · intro n
    simp [Description.scheduledBitsBound, Description.structuralBitsBound,
      Description.observationRowCount]

-- Each primitive certificate already quantifies over every shared stateful handler.
example : firstArtifact.machine.ComputesTidily
    (encPair encBits encUnary ([false], 1))
    (firstArtifact.time ([false], 1))
    (encBits <$> NativeOracleProgram.queryTakeProgram
      (0 : Operation) ([false], 1)) :=
  firstArtifact.computes ([false], 1)

example : secondArtifact.machine.ComputesTidily
    (encPair encBits encUnary ([true], 2))
    (secondArtifact.time ([true], 2))
    (encBits <$> NativeOracleProgram.queryTakeProgram
      (1 : Operation) ([true], 2)) :=
  secondArtifact.computes ([true], 2)

/-- An actual constant compiler prepares the first request. -/
noncomputable def firstRequestCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit
    (encPair encBits encUnary) ([false], 1)

/-- A deterministic local branch is a retained oracle artifact with no dummy coin or query. -/
noncomputable def localArtifact := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep firstRequestCompiler)

example : localArtifact.machine.ComputesTidily (encUnit ())
    (localArtifact.time ()) (encPair encBits encUnary <$> pure ([false], 1)) :=
  localArtifact.computes ()

/-- Emitted pair size exposes both the framing of the dynamic first component and the encoded
second component; it is separate from the final artifact's static charge. -/
example (request : List Bool × ℕ) :
    localArtifact.outputBits request =
      2 * (encBits request.1).length + 1 + (encUnary request.2).length := by
  change (encPair encBits encUnary request).length =
    2 * (encBits request.1).length + 1 + (encUnary request.2).length
  exact length_encPair request

/-! #### Typed retained composition -/

/-- A genuinely typed postprocessor discards a `Bool`; its constant machine has an
input-independent one-step clock. -/
noncomputable def discardBitCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const encBool encUnit ()

noncomputable def discardBit :=
  ClassifiedCompiler.inPhase .localStep discardBitCompiler

def discardBitOnline : OnlineAccounting Unit where
  time := fun phase _ => if phase = .localStep then 1 else 0
  workspace := fun _ _ => 0

theorem discardBit_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Bool) (state' : OracleState)
    (_hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    discardBit.online.time phase middle ≤ discardBitOnline.time phase input ∧
      discardBit.online.workspace phase middle ≤ discardBitOnline.workspace phase input := by
  constructor <;>
    simp [discardBit, discardBitCompiler, discardBitOnline, ClassifiedCompiler.inPhase,
      ClassifiedCompiler.ofAccounting, ClassifiedCompiler.finishCompilerAccounting,
      OnlineAccounting.withWorkspaceFloor,
      Turing.MultiTapeTM.Internal.NativeCompiler.const]

noncomputable def typedPostArtifact := NativeOracleProgram.postprocess
  (NativeOracleProgram.fairBit (r := 2) encUnit) discardBit discardBitOnline
    discardBit_resource_bound

example : typedPostArtifact.machine.ComputesTidily (encUnit ())
    (typedPostArtifact.time ())
    (encUnit <$> ((fun _ : Bool => ()) <$> ProbOracleComp.sample (ProbComp.uniform Bool))) :=
  typedPostArtifact.computes ()

/-- The captured continuation consumes an actually typed `(Unit × Bool)` and emits `Unit`; no
decoder or raw-word cast appears in the artifact or its proof. -/
noncomputable def typedContinuationCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const (encPair encUnit encBool) encUnit ()

noncomputable def typedContinuation := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep typedContinuationCompiler)

def typedContinuationOnline : OnlineAccounting Unit where
  time := fun phase _ => if phase = .localStep then 1 else 0
  workspace := fun _ _ => 0

theorem typedContinuation_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Bool) (state' : OracleState)
    (_hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    typedContinuation.online.time phase (input, middle) ≤
        typedContinuationOnline.time phase input ∧
      typedContinuation.online.workspace phase (input, middle) ≤
        typedContinuationOnline.workspace phase input := by
  constructor <;>
    simp [typedContinuation, typedContinuationCompiler, typedContinuationOnline,
      NativeOracleProgram.ofCompiler, ClassifiedCompiler.inPhase, ClassifiedCompiler.ofAccounting,
      ClassifiedCompiler.finishCompilerAccounting, OnlineAccounting.withWorkspaceFloor,
      Turing.MultiTapeTM.Internal.NativeCompiler.const]

noncomputable def typedCapturedArtifact := NativeOracleProgram.sequenceCaptured
  (NativeOracleProgram.fairBit (r := 2) encUnit) typedContinuation typedContinuationOnline
    typedContinuation_resource_bound

example : typedCapturedArtifact.machine.ComputesTidily (encUnit ())
    (typedCapturedArtifact.time ())
    (encUnit <$> NativeOracleProgram.capturedProgram
      (fun _ : Unit => ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun _ : Unit × Bool => pure ()) ()) :=
  typedCapturedArtifact.computes ()

/-- Binary dispatch likewise preserves a typed `Bool` output rather than forcing a raw word. -/
noncomputable def trueCondition := ClassifiedCompiler.inPhase .dispatch
  (Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit encBits [true])

noncomputable def typedDispatchArtifact := NativeOracleProgram.dispatch trueCondition
  (NativeOracleProgram.fairBit (r := 2) encUnit)
  (NativeOracleProgram.fairBit (r := 2) encUnit)

example : typedDispatchArtifact.machine.ComputesTidily (encUnit ())
    (typedDispatchArtifact.time ())
    (encBool <$> ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  typedDispatchArtifact.computes ()

noncomputable def firstPrepared := NativeOracleProgram.preprocess
  (ClassifiedCompiler.inPhase .marshalling firstRequestCompiler) firstArtifact

/-- The continuation request compiler extracts the first reply with the retained frame parser and
pairs it with the fixed reply limit `2`. -/
noncomputable def secondRequestProjection := ClassifiedCompiler.inPhase .parsing
  (Turing.MultiTapeTM.Internal.NativeCompiler.second encUnit encBits)

noncomputable def secondRequestLimit := ClassifiedCompiler.inPhase .marshalling
  (Turing.MultiTapeTM.Internal.NativeCompiler.const
    (encPair encUnit encBits) encUnary 2)

noncomputable def secondRequest :=
  ClassifiedCompiler.pair secondRequestProjection secondRequestLimit

noncomputable def secondPrepared := NativeOracleProgram.preprocess
  secondRequest secondArtifact

theorem secondRequestCompiler_time (input : Unit × List Bool) :
    secondRequest.compiler.time input = 12 * input.2.length + 32 := by
  rcases input with ⟨inputUnit, word⟩
  cases inputUnit
  simp only [secondRequest, ClassifiedCompiler.pair,
    secondRequestProjection, secondRequestLimit, ClassifiedCompiler.inPhase,
    ClassifiedCompiler.ofAccounting,
    Turing.MultiTapeTM.Internal.NativeCompiler.pair,
    Turing.MultiTapeTM.Internal.NativeCompiler.comp,
    Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame,
    Turing.MultiTapeTM.Internal.NativeCompiler.second,
    Turing.MultiTapeTM.Internal.NativeCompiler.ofTransducer, length_encPair, encUnit_apply,
    encBits_apply]
  rw [show (Turing.MultiTapeTM.Internal.NativeCompiler.const
    (encPair encUnit encBits) encUnary 2).time ((), word) = 3 by rfl]
  simp only [List.length_nil]
  omega

/-- A uniform phase schedule for the second artifact on the first query's one-bit reply prefix. -/
def secondClock (_ : OnlinePhase) (_ : Unit) : ℕ := 1000

/-- The finite one-bit continuation range retains the second artifact's phase-local workspace
instead of replacing it by zero. -/
noncomputable def secondOnline : OnlineAccounting Unit where
  time := secondClock
  workspace := fun phase input =>
    max (secondPrepared.online.workspace phase (input, []))
      (max (secondPrepared.online.workspace phase (input, [false]))
        (secondPrepared.online.workspace phase (input, [true])))

theorem secondPrepared_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : List Bool) (state' : OracleState)
    (hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (NativeOracleProgram.queryTakeProgram (0 : Operation) ([false], 1)) state).support)
    (phase : OnlinePhase) :
    secondPrepared.online.time phase (input, middle) ≤ secondOnline.time phase input ∧
      secondPrepared.online.workspace phase (input, middle) ≤
        secondOnline.workspace phase input := by
  have hlength : middle.length ≤ 1 := by
    rw [NativeOracleProgram.queryTakeProgram, ProbOracleComp.runWith_map] at hmiddle
    obtain ⟨⟨reply, replyState⟩, _, heq⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hmiddle
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact List.length_take_le 1 reply
  constructor
  · refine (OnlineAccounting.time_le_totalTime secondPrepared.online phase
      (input, middle)).trans ?_
    change secondPrepared.time (input, middle) ≤ secondOnline.time phase input
    rw [show secondPrepared.time (input, middle) =
        5 * secondRequest.compiler.time (input, middle) +
          secondArtifact.time (middle, 2) + 9 by
      simpa only [secondPrepared, Function.const_apply] using
        (NativeOracleProgram.time_preprocess secondRequest secondArtifact (input, middle)),
      secondRequestCompiler_time,
      show secondArtifact.time (middle, 2) = 4 * middle.length + 2 * 2 + 6 by
        simpa only [secondArtifact, NativeOracleProgram.queryTake,
          NativeOracleProgram.time] using
          (NativeOracleProgram.totalTime_queryTakeOnline (middle, 2))]
    simp only [secondOnline, secondClock]
    omega
  · rcases middle with _ | ⟨bit, rest⟩
    · exact le_max_left _ _
    · have hrest : rest = [] := by
        exact List.eq_nil_of_length_eq_zero (by
          simp only [List.length_cons] at hlength
          omega)
      subst rest
      cases bit
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The concrete two-call client is the retained captured-input machine, not merely semantic bind.
Its second request is the first reply prefix. -/
noncomputable def adaptiveArtifact :=
  NativeOracleProgram.sequenceCaptured firstPrepared secondPrepared secondOnline
    secondPrepared_resource_bound

def adaptive : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool) :=
  NativeOracleProgram.capturedProgram
    (fun _ : Unit => NativeOracleProgram.queryTakeProgram (0 : Operation) ([false], 1))
    (fun input : Unit × List Bool =>
      NativeOracleProgram.queryTakeProgram (1 : Operation) (input.2, 2)) ()

example : adaptiveArtifact.machine.ComputesTidily (encUnit ())
    (adaptiveArtifact.time ()) (encBits <$> adaptive) :=
  adaptiveArtifact.computes ()

/-- A deterministic stateful handler. Its second answer is nonempty only at state `1` and only
when it observes the request produced from the first answer. -/
noncomputable def handler : Operation × List Bool → StateT ℕ PMF (List Bool)
  | _, 0 => PMF.pure ([true, false], 1)
  | request, state + 1 =>
      if state = 0 ∧ request = ((1 : Operation), [true]) then
        PMF.pure ([false, true], state + 2)
      else
        PMF.pure ([], state + 2)

/-- The complete result/final-state law observes both adaptive calls. -/
example : ProbOracleComp.runWith handler adaptive 0 =
    PMF.pure ([false, true], 2) := by
  simp [adaptive, NativeOracleProgram.capturedProgram,
    NativeOracleProgram.queryTakeProgram, handler]

/-- The generated first-order description has the same complete stateful law, with explicit
natural-symbol encoding at its output. -/
example : ProbOracleComp.runWith handler (adaptiveArtifact.descriptionRun ()) 0 =
    (ProbOracleComp.runWith handler (encBits <$> adaptive) 0).map
      (Prod.map (List.map Turing.MultiTapeTM.Universal.eBit) id) :=
  adaptiveArtifact.runWith_descriptionRun handler () 0

/-- The handler is not memoryless or constant. -/
example : handler ((0 : Operation), [false]) 0 ≠
    handler ((0 : Operation), [false]) 1 := by
  change PMF.pure ([true, false], 1) ≠ PMF.pure ([], 2)
  intro h
  have hmem : ([true, false], 1) ∈ (PMF.pure ([true, false], 1)).support :=
    (PMF.mem_support_pure_iff _ _).mpr rfl
  rw [h, PMF.mem_support_pure_iff] at hmem
  simp at hmem

/-- Regression witness: iteration preserves a nonzero query-phase workspace peak instead of
zeroing it and recovering only a generic controller bound. -/
def loopRoundOnline : OnlineAccounting Unit where
  time := fun _ _ => 3
  workspace
    | .lookup, _ => 7
    | _, _ => 0

example : (NativeOracleProgram.boundedIterationAccountingOn
    (fun _ : Unit => 2) (fun _ => 5) loopRoundOnline 4).workspace .lookup () = 7 :=
  rfl

example : 7 ≤ (NativeOracleProgram.boundedIterationAccountingOn
    (fun _ : Unit => 2) (fun _ => 5) loopRoundOnline 4).totalWorkspace () :=
  NativeOracleProgram.workspace_le_boundedIterationAccountingOn
    (fun _ : Unit => 2) (fun _ => 5) loopRoundOnline 4 .lookup ()

end CslibFrontierTests.Internal.NativeOracleWitness
