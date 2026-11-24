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

/-- The first and second calls use the artifacts of two different fixed operations. -/
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

/-- A constant compiler prepares the first request. -/
noncomputable def firstRequestCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit
    (encPair encBits encUnary) ([false], 1)

/-- A deterministic local branch is a retained oracle artifact with no dummy coin or query. -/
noncomputable def localArtifact := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep firstRequestCompiler)

example : localArtifact.machine.ComputesTidily (encUnit ())
    (localArtifact.time ()) (encPair encBits encUnary <$> pure ([false], 1)) :=
  localArtifact.computes ()

/-! #### Typed retained composition -/

/-- A typed postprocessor discards a `Bool`; its constant machine has an
input-independent one-step clock. -/
noncomputable def discardBitCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const encBool encUnit ()

noncomputable def discardBit :=
  ClassifiedCompiler.inPhase .localStep discardBitCompiler

def discardBitOnline : OnlineAccounting Unit where
  time := fun phase _ => if phase = .localStep then 1 else 0

theorem discardBit_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Bool) (state' : OracleState)
    (_hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    discardBit.online.time phase middle ≤ discardBitOnline.time phase input := by
  simp [discardBit, discardBitCompiler, discardBitOnline, ClassifiedCompiler.inPhase,
    Turing.MultiTapeTM.Internal.NativeCompiler.const]

noncomputable def typedPostArtifact := NativeOracleProgram.postprocess
  (NativeOracleProgram.fairBit (r := 2) encUnit) discardBit discardBitOnline
    discardBit_resource_bound

example : typedPostArtifact.machine.ComputesTidily (encUnit ())
    (typedPostArtifact.time ())
    (encUnit <$> ((fun _ : Bool => ()) <$> ProbOracleComp.sample (ProbComp.uniform Bool))) :=
  typedPostArtifact.computes ()

/-- The captured continuation consumes a typed `(Unit × Bool)` and emits `Unit`; no
decoder or raw-word cast appears in the artifact or its proof. -/
noncomputable def typedContinuationCompiler :=
  Turing.MultiTapeTM.Internal.NativeCompiler.const (encPair encUnit encBool) encUnit ()

noncomputable def typedContinuation := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep typedContinuationCompiler)

def typedContinuationOnline : OnlineAccounting Unit where
  time := fun phase _ => if phase = .localStep then 1 else 0

theorem typedContinuation_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Bool) (state' : OracleState)
    (_hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    typedContinuation.online.time phase (input, middle) ≤
      typedContinuationOnline.time phase input := by
  simp [typedContinuation, typedContinuationCompiler, typedContinuationOnline,
    NativeOracleProgram.ofCompiler, ClassifiedCompiler.inPhase,
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

/-- Binary dispatch keeps the typed `Bool` output of its branches. -/
noncomputable def trueCondition := ClassifiedCompiler.inPhase .dispatch
  (Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit encBits [true])

noncomputable def typedDispatchArtifact := NativeOracleProgram.dispatch trueCondition
  (NativeOracleProgram.fairBit (r := 2) encUnit)
  (NativeOracleProgram.fairBit (r := 2) encUnit)

example : typedDispatchArtifact.machine.ComputesTidily (encUnit ())
    (typedDispatchArtifact.time ())
    (encBool <$> ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  typedDispatchArtifact.computes ()

/-! #### Finite dispatch -/

/-- A test that never selects its case. -/
noncomputable def emptyCondition := ClassifiedCompiler.inPhase .dispatch
  (Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit encBits [])

/-- A deterministic branch that emits a fixed bit. -/
noncomputable def constBitArtifact (bit : Bool) := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep
    (Turing.MultiTapeTM.Internal.NativeCompiler.const encUnit encBool bit))

/-- Two retained cases. The first test emits the empty word, so its case is skipped; the second
selects the fair-bit sampler. -/
noncomputable def dispatchCases :
    List (NativeOracleProgram.DispatchCase 2 Unit Bool encUnit encBool) :=
  [{ test := fun _ => []
     condition := emptyCondition
     program := fun _ => pure true
     branch := constBitArtifact true },
   { test := fun _ => [true]
     condition := trueCondition
     program := fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)
     branch := NativeOracleProgram.fairBit (r := 2) encUnit }]

noncomputable def finiteDispatchArtifact :=
  NativeOracleProgram.finiteDispatch dispatchCases (constBitArtifact false)

/-- First-match selection skips the first case and does not reach the fallback. -/
example : NativeOracleProgram.dispatchProgram dispatchCases (fun _ : Unit => pure false) () =
    ProbOracleComp.sample (ProbComp.uniform Bool) := by
  simp [NativeOracleProgram.dispatchProgram, dispatchCases]

example : finiteDispatchArtifact.machine.ComputesTidily (encUnit ())
    (finiteDispatchArtifact.time ())
    (encBool <$>
      NativeOracleProgram.dispatchProgram dispatchCases (fun _ : Unit => pure false) ()) :=
  finiteDispatchArtifact.computes ()

/-! #### Bounded iteration -/

/-- One loop round as a program: drop the first bit of the word. -/
def dropBitStep (word : List Bool) :
    ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool) :=
  pure word.tail

/-- The loop body is the retained one-pass transducer for `List.tail`. -/
noncomputable def dropBit := NativeOracleProgram.ofCompiler (r := 2)
  (ClassifiedCompiler.inPhase .localStep Turing.MultiTapeTM.Internal.NativeCompiler.tailDecoder)

/-- A round on any suffix of the initial word is charged the body's clock on the whole word. -/
def dropBitOnline : OnlineAccounting (List Bool) where
  time := fun phase word => if phase = .localStep then 4 * word.length + 8 else 0

theorem dropBit_clock (initial : List Bool) (n : ℕ) (_hn : n ≤ initial.length - 1)
    (current : List Bool) (hcurrent : current = initial.drop n) (phase : OnlinePhase) :
    dropBit.online.time phase current ≤ dropBitOnline.time phase initial := by
  subst hcurrent
  have hdrop : (initial.drop n).length ≤ initial.length := by
    rw [List.length_drop]
    exact Nat.sub_le _ _
  by_cases hphase : phase = .localStep
  · simp only [dropBit, dropBitOnline, NativeOracleProgram.ofCompiler, ClassifiedCompiler.inPhase,
      Turing.MultiTapeTM.Internal.NativeCompiler.tailDecoder,
      Turing.MultiTapeTM.Internal.NativeCompiler.ofTransducer, encBits_apply, hphase, ↓reduceIte]
    omega
  · simp [dropBit, dropBitOnline, NativeOracleProgram.ofCompiler, ClassifiedCompiler.inPhase,
      hphase]

/-- Before the last ordinary round the next word is the next suffix, and it is nonempty. -/
theorem dropBit_preserve (initial : List Bool) (n : ℕ) (hn : n < initial.length - 1)
    (current : List Bool) (hcurrent : current = initial.drop n) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState) (next : List Bool)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (dropBitStep current) state).support) :
    next = initial.drop (n + 1) ∧ encBits next ≠ [] := by
  simp only [dropBitStep, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hnext
  rcases Prod.mk.inj hnext with ⟨rfl, rfl⟩
  subst hcurrent
  have htail : (initial.drop n).tail = initial.drop (n + 1) := by rw [List.tail_drop]
  refine ⟨htail, ?_⟩
  rw [htail, encBits_apply]
  intro hempty
  have hlength := congrArg List.length hempty
  rw [List.length_drop, List.length_nil] at hlength
  omega

/-- The stopping round drops the last bit and emits the empty word. -/
theorem dropBit_last (initial current : List Bool)
    (hcurrent : current = initial.drop (initial.length - 1)) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (state : OracleState) :
    ProbOracleComp.runWith oracle (encBits <$> dropBitStep current) state =
      ProbOracleComp.runWith oracle (pure []) state := by
  have htail : current.tail = [] := by
    subst hcurrent
    rw [List.tail_drop]
    exact List.drop_eq_nil_of_le (by omega)
  simp only [dropBitStep, htail, map_pure, encBits_apply]

theorem dropBit_length (initial : List Bool) (n : ℕ) (_hn : n ≤ initial.length - 1)
    (current : List Bool) (hcurrent : current = initial.drop n) :
    (encBits current).length ≤ initial.length := by
  subst hcurrent
  rw [encBits_apply, List.length_drop]
  exact Nat.sub_le _ _

/-- A loop whose number of rounds depends on the input: it drops one bit per round until the word
is empty. On `word` it runs `word.length - 1` ordinary rounds, each leaving a nonempty word, and
the stopping round drops the last bit, which `iterateWhile` reads as its terminator. -/
noncomputable def dropBitsArtifact :=
  NativeOracleProgram.boundedIterationEncodedOn Turing.MultiTapeTM.Decoder.bits dropBit
    (fun word => word.length - 1) (fun word => word.length) dropBitOnline
    (fun initial n current => current = initial.drop n)
    (fun _ => rfl) dropBit_clock dropBit_preserve dropBit_last dropBit_length

example (word : List Bool) : dropBitsArtifact.machine.ComputesTidily (encBits word)
    (dropBitsArtifact.time word)
    (encBits <$> OracleComp.iterate (word.length - 1) dropBitStep word) :=
  dropBitsArtifact.computes word

/-- The recorded clock of the loop: `word.length` body rounds and the loop scaffolding. -/
example (word : List Bool) : dropBitsArtifact.time word =
    (word.length - 1 + 1) * (dropBitOnline.totalTime word + 10 * word.length + 23) +
      8 * word.length + 17 :=
  NativeOracleProgram.time_boundedIterationEncodedOn _ _ _ _ _ _ _ _ _ _ _ word

/-- On a two-bit word the loop runs one ordinary round and returns the last bit. -/
example : OracleComp.iterate ([true, false].length - 1) dropBitStep [true, false] =
    pure [false] := by
  simp [OracleComp.iterate_succ, dropBitStep]

/-! #### Forgetting to the existential predicate -/

/-- The one-step sampler has the constant clock `1`, so the forgetful theorem applies to it. -/
example : IsOraclePPTOn encUnit encBool
    (fun _ : Unit => (ProbOracleComp.sample (ProbComp.uniform Bool) :
      ProbOracleComp (fun _ : Operation × List Bool => List Bool) Bool)) :=
  (NativeOracleProgram.fairBit (r := 2) encUnit).isOraclePPTOn
    ⟨fun _ => 1, Cslib.PolynomiallyBounded.const 1,
      fun input => (NativeOracleProgram.totalTime_fairBitOnline input).le⟩

/-! #### An adaptive two-query client -/

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
def secondOnline : OnlineAccounting Unit where
  time := fun _ _ => 1000

theorem secondPrepared_resource_bound (input : Unit) (OracleState : Type)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : List Bool) (state' : OracleState)
    (hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle
        (NativeOracleProgram.queryTakeProgram (0 : Operation) ([false], 1)) state).support)
    (phase : OnlinePhase) :
    secondPrepared.online.time phase (input, middle) ≤ secondOnline.time phase input := by
  have hlength : middle.length ≤ 1 := by
    rw [NativeOracleProgram.queryTakeProgram, ProbOracleComp.runWith_map] at hmiddle
    obtain ⟨⟨reply, replyState⟩, _, heq⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hmiddle
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact List.length_take_le 1 reply
  refine (OnlineAccounting.time_le_totalTime secondPrepared.online phase
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
  simp only [secondOnline]
  omega

/-- The concrete two-call client is the retained captured-input machine. Its second request is the
first reply prefix. -/
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

end CslibFrontierTests.Internal.NativeOracleWitness
