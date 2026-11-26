/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput

/-!
# Explicit transition tables for streaming folds

This module assembles the streaming-fold kernel entirely from retained effect-free transition
tables. Its correctness theorems use the established tape-transformation specifications; no
transition function is recovered from a relation or from the legacy noncomputable assembly.

## Main definitions

* `Turing.MultiTapeMachine.onWords`: run an explicit tidy table between virtual input and output
  work tapes.
* `Turing.MultiTapeMachine.streamRound`: one explicit read/emit/update stream round.
* `Turing.MultiTapeMachine.stream`: the complete explicit streaming-fold table.

## Main results

* `Turing.MultiTapeMachine.transformsTapes_onWords_extendTapes`: selected-tape semantics and
  exact resources for a lifted callback.
* `Turing.MultiTapeMachine.transformsTapesAt_streamRound`: exact semantics and resources of one
  stream round.
* `Turing.MultiTapeMachine.computesTidily_stream_after`: the assembled stream table computes the
  accumulated stream and final output with the stated clock and workspace bounds.
-/

public section

namespace Turing.MultiTapeMachine

variable {K : ℕ} {Q InitState EmitState NextState FinishState : Type}

/-- Run a tidy explicit table between a virtual input work tape and a fresh output work tape. -/
def onWords {k : ℕ} {State : Type}
    (machine : MultiTapeMachine k Bool State Empty Id) (mark : Bool) :
    MultiTapeMachine (k + 1 + 2) Bool
      (MultiTapeTM.MarkWorkState ⊕ (State ⊕ MultiTapeTM.RewindWorkState) ⊕
        MultiTapeTM.MarkWorkState) Empty Id :=
  machine.outputToWord.inputFromWord mark

private lemma onWords_post {k : ℕ} (input output : List Bool) :
    Fin.append
        (Function.update (fun _ : Fin (k + 1) => ([] : List Bool)) (Fin.last k) output)
        ![input, []] =
      Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
        ((Fin.last k).castAdd 2) output := by
  rw [Fin.append_update_left, MultiTapeTM.append_nil_eq_update]

theorem transformsTapes_onWords {k : ℕ} {State : Type}
    {machine : MultiTapeMachine k Bool State Empty Id}
    {input output : List Bool} {time space : ℕ} (mark : Bool)
    (h : machine.toTM.ComputesTidilyInTimeAndSpace input output time space) :
    MultiTapeTM.TransformsTapes (onWords machine mark).toTM
      (fun _ tapes =>
        tapes = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
      (fun _ tapes tapes' emitted =>
        tapes' = Function.update tapes ((Fin.last k).castAdd 2) output ∧ emitted = [])
      (time + output.length + 6)
      (space + 2 * input.length + 2 * output.length + 3 * k + 18) := by
  obtain ⟨tapes', emitted, ⟨rfl, rfl⟩, path⟩ :=
    MultiTapeTM.transformsTapes_iff_nil_output.mp
      (computesTidilyInTimeAndSpace_outputToWord h) input (fun _ => []) ⟨rfl, rfl⟩
  have key := transformsTapes_inputFromWord mark (machine := machine.outputToWord)
    (word := input) (tapes₀ := fun _ => [])
    (tapes₁ := Function.update (fun _ => []) (Fin.last k) output) (emitted := []) path
  rw [onWords]
  exact key.imp (fun _ _ htapes => htapes.trans (MultiTapeTM.append_nil_eq_update input).symm)
    (fun _ _ _ _ htapes ⟨htapes', hemitted⟩ =>
      ⟨htapes'.trans (htapes ▸ onWords_post input output), hemitted⟩)
    (by omega)
    (by omega)

/-- Run a tidy explicit table between two selected tapes, preserving the input and emitting
nothing. -/
theorem transformsTapes_onWords_extendTapes {k : ℕ} {State : Type}
    {machine : MultiTapeMachine k Bool State Empty Id}
    {input output : List Bool} {time space K : ℕ} (mark : Bool)
    (h : machine.toTM.ComputesTidilyInTimeAndSpace input output time space)
    {embedding : Fin (k + 1 + 2) ↪ Fin K} {value target : Fin K}
    (hvalue : embedding (Fin.natAdd (k + 1) 0) = value)
    (htarget : embedding ((Fin.last k).castAdd 2) = target) :
    MultiTapeTM.TransformsTapes ((onWords machine mark).extendTapes embedding).toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value input)
      (fun _ tapes tapes' emitted =>
        tapes' = Function.update tapes target output ∧ emitted = [])
      (time + output.length + 6)
      (space + 2 * input.length + 2 * output.length + 3 * k + 18 +
        (K - (k + 1 + 2))) := by
  have hselected := ((transformsTapes_onWords mark h).imp
    (P' := fun _ tapes => True ∧
      tapes = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
    (fun _ _ htapes => htapes.2) (fun _ _ _ _ _ hpost => hpost)
    le_rfl le_rfl).extendTapes_update embedding
  rw [hvalue, htarget] at hselected
  simpa only [toTM_extendTapes] using hselected.imp (fun _ _ htapes => ⟨trivial, htapes⟩)
    (fun _ _ _ _ _ hpost => hpost) le_rfl le_rfl

/-- Copy the word on selected source tape `embedding 1` to blank target `embedding 0`. -/
private def copyWord (embedding : Fin (0 + 1 + 2) ↪ Fin K) (mark : Bool) :
    MultiTapeMachine K Bool
      (MultiTapeTM.MarkWorkState ⊕
        ((Unit ⊕ MultiTapeTM.RewindState) ⊕ MultiTapeTM.RewindWorkState) ⊕
          MultiTapeTM.MarkWorkState) Empty Id :=
  ((onWords (tidyCopy Bool) mark).extendTapes embedding)

private theorem transformsTapes_copyWord
    (embedding : Fin (0 + 1 + 2) ↪ Fin K) (mark : Bool) (word : List Bool) :
    MultiTapeTM.TransformsTapes (copyWord embedding mark).toTM
      (fun _ tapes =>
        tapes (embedding 1) = word ∧ tapes (embedding 0) = [] ∧ tapes (embedding 2) = [])
      (fun _ tapes tapes' emitted =>
        tapes' = Function.update tapes (embedding 0) word ∧ emitted = [])
      (3 * word.length + 10) (4 * word.length + K + 15) := by
  have hK : 3 ≤ K := by simpa using Fintype.card_le_of_embedding embedding
  rw [copyWord, toTM_extendTapes]
  refine ((transformsTapes_onWords
    (machine := tidyCopy Bool) (input := word) (output := word) mark
    (computesTidily_tidyCopy word)).extendTapes embedding).imp
    (fun _ tapes ⟨h₁, h₀, h₂⟩ => ?_)
    (fun _ tapes tapes' _ ⟨h₁, h₀, h₂⟩ ⟨⟨hword, hemitted⟩, hextra⟩ => ⟨?_, hemitted⟩)
    (by omega)
    (by omega)
  · funext selected
    fin_cases selected <;> simp [h₀, h₁, h₂]
  · funext tape
    by_cases htape : tape ∈ Set.range embedding
    · obtain ⟨selected, rfl⟩ := htape
      have := congrFun hword selected
      fin_cases selected <;> simp_all [embedding.injective.eq_iff]
    · rw [hextra tape htape, Function.update_of_ne fun h => htape ⟨0, h.symm⟩]

/-- Clearing one selected tape while preserving all other tapes. -/
private theorem transformsTapes_clearWork_tapeEmb
    (tape : Fin K) (word : List Bool) (tapes₀ tapes₁ : Fin K → List Bool)
    (hword : tapes₀ tape = word) (hpost : Function.update tapes₀ tape [] = tapes₁) :
    MultiTapeTM.TransformsTapes
      ((clearWork Bool).extendTapes (MultiTapeTM.tapeEmb tape)).toTM
      (fun _ tapes => tapes = tapes₀)
      (fun _ _ tapes' output => tapes' = tapes₁ ∧ output = [])
      (3 * (word.length + 1)) (word.length + 1 + K) := by
  rw [toTM_extendTapes]
  exact ((transformsTapes_clearWork word).tapeEmb tape).imp
    (fun _ _ h => h ▸ hword)
    (fun _ _ _ _ htapes ⟨_, ⟨hvalue, he⟩, hextra⟩ =>
      ⟨by rw [hextra, hvalue, htapes, hpost], he⟩)
    le_rfl (by have := tape.pos; omega)

/-- Emit from `value`, compute a next state into `next`, move it back to `value`, and clean up. -/
private def frozenRound (emitter : MultiTapeMachine K Bool EmitState Empty Id)
    (nextMachine : MultiTapeMachine K Bool NextState Empty Id)
    (value next flag : Fin K) (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag) :=
  emitter.seq (nextMachine.seq
    (((clearWork Bool).extendTapes (MultiTapeTM.tapeEmb value)).seq
      ((copyWord (MultiTapeTM.threeTapes value next flag
          hValueNext hValueFlag hNextFlag) true).seq
        ((clearWork Bool).extendTapes (MultiTapeTM.tapeEmb next)))))

/-- Exact tape, output, time, and workspace behavior of the explicit frozen-round table. -/
private theorem transformsTapes_frozenRound
    {emitter : MultiTapeMachine K Bool EmitState Empty Id}
    {nextMachine : MultiTapeMachine K Bool NextState Empty Id}
    {value next flag : Fin K} (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag)
    {word emitted nextWord : List Bool} {emitterTime emitterSpace nextTime nextSpace : ℕ}
    (hEmitter : MultiTapeTM.TransformsTapes emitter.toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value word)
      (fun _ tapes tapes' output => tapes' = tapes ∧ output = emitted)
      emitterTime emitterSpace)
    (hNext : MultiTapeTM.TransformsTapes nextMachine.toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value word)
      (fun _ tapes tapes' output =>
        tapes' = Function.update tapes next nextWord ∧ output = []) nextTime nextSpace) :
    MultiTapeTM.TransformsTapes
      (frozenRound emitter nextMachine value next flag
        hValueNext hValueFlag hNextFlag).toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value word)
      (fun _ _ tapes' output =>
        tapes' = Function.update (fun _ => []) value nextWord ∧ output = emitted)
      (emitterTime + (nextTime + (3 * (word.length + 1) +
        ((3 * nextWord.length + 10) + 3 * (nextWord.length + 1)))))
      (emitterSpace + (nextSpace + ((word.length + 1 + K) +
        ((4 * nextWord.length + K + 15) + (nextWord.length + 1 + K))))) := by
  set tapes₀ := Function.update (fun _ => ([] : List Bool)) value word
  set tapes₁ := Function.update tapes₀ next nextWord
  set tapes₂ := Function.update tapes₁ value []
  set tapes₃ := Function.update tapes₂ value nextWord
  have htapes₄ : Function.update tapes₃ next [] =
      Function.update (fun _ => []) value nextWord := by
    funext tape
    simp only [tapes₃, tapes₂, tapes₁, tapes₀, Function.update_apply]
    split_ifs <;> simp_all
  have h₀ := hEmitter.imp
    (Q' := fun _ _ tapes' output => tapes' = tapes₀ ∧ output = emitted)
    (fun _ _ h => h) (fun _ _ _ _ htapes ⟨h, he⟩ => ⟨h.trans htapes, he⟩) le_rfl le_rfl
  have h₁ := hNext.imp
    (Q' := fun _ _ tapes' output => tapes' = tapes₁ ∧ output = [])
    (fun _ _ h => h) (fun _ _ _ _ htapes ⟨h, he⟩ => ⟨by rw [h, htapes], he⟩) le_rfl le_rfl
  have h₂ := transformsTapes_clearWork_tapeEmb value word tapes₁ tapes₂
    (by simp [tapes₁, tapes₀, hValueNext]) rfl
  have h₃ := (transformsTapes_copyWord
    (MultiTapeTM.threeTapes value next flag hValueNext hValueFlag hNextFlag)
    true nextWord).imp
    (P' := fun _ tapes => tapes = tapes₂)
    (Q' := fun _ _ tapes' output => tapes' = tapes₃ ∧ output = [])
    (fun _ _ h => by
      simp [h, MultiTapeTM.threeTapes, tapes₂, tapes₁, tapes₀,
        hValueNext.symm, hValueFlag.symm, hNextFlag.symm])
    (fun _ _ _ _ htapes ⟨h, he⟩ =>
      ⟨by rw [h, htapes]; simp [MultiTapeTM.threeTapes, tapes₃], he⟩) le_rfl le_rfl
  have h₄ := transformsTapes_clearWork_tapeEmb next nextWord tapes₃
    (Function.update (fun _ => []) value nextWord)
    (by simp [tapes₃, tapes₂, tapes₁, hValueNext.symm]) htapes₄
  rw [frozenRound, toTM_seq, toTM_seq, toTM_seq, toTM_seq]
  exact (h₀.seq_eq (h₁.seq_eq (h₂.seq_eq (h₃.seq_eq h₄)))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h, by simp [he]⟩) le_rfl le_rfl

/-- Read one token into `value`, then perform one input-frozen stream round. -/
def streamRound (reader : MultiTapeTM.InputReader Bool Q)
    (emitter : MultiTapeMachine K Bool EmitState Empty Id)
    (nextMachine : MultiTapeMachine K Bool NextState Empty Id)
    (value next flag : Fin K) (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag) :=
  (reader.appendReadTable value).seq
    (frozenRound emitter nextMachine value next flag hValueNext hValueFlag hNextFlag).freezeInput

/-- One explicit round has the established exact cursor, tape, output, time, and workspace law. -/
theorem transformsTapesAt_streamRound
    {reader : MultiTapeTM.InputReader Bool Q}
    {emitter : MultiTapeMachine K Bool EmitState Empty Id}
    {nextMachine : MultiTapeMachine K Bool NextState Empty Id}
    {value next flag : Fin K} (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag)
    (input : List Bool) (position : Fin (input.length + 2))
    (hposition : position.val ≠ 0) (word : List Bool)
    {emitted nextWord : List Bool} {emitterTime emitterSpace nextTime nextSpace : ℕ}
    (hEmitter : MultiTapeTM.TransformsTapes emitter.toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value
        (word ++ (reader.read reader.q₀ (input.drop (position.val - 1))).1))
      (fun _ tapes tapes' output => tapes' = tapes ∧ output = emitted)
      emitterTime emitterSpace)
    (hNext : MultiTapeTM.TransformsTapes nextMachine.toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value
        (word ++ (reader.read reader.q₀ (input.drop (position.val - 1))).1))
      (fun _ tapes tapes' output =>
        tapes' = Function.update tapes next nextWord ∧ output = []) nextTime nextSpace) :
    let read := reader.read reader.q₀ (input.drop (position.val - 1))
    MultiTapeTM.TransformsTapesAt
      (streamRound reader emitter nextMachine value next flag
        hValueNext hValueFlag hNextFlag).toTM
      (fun actualInput actualPosition tapes => actualInput = input ∧
        actualPosition.val = position.val ∧
        tapes = Function.update (fun _ => []) value word)
      (fun _ _ _ finalPosition finalTapes output =>
        finalPosition.val = position.val + read.2 ∧
        finalTapes = Function.update (fun _ => []) value nextWord ∧ output = emitted)
      (word.length + 1 + ((read.2 + 1) + ((word ++ read.1).length + 2)) +
        (emitterTime + (nextTime + (3 * ((word ++ read.1).length + 1) +
          ((3 * nextWord.length + 10) + 3 * (nextWord.length + 1))))))
      ((word ++ read.1).length + 2 + (K - 1) +
        (emitterSpace + (nextSpace + (((word ++ read.1).length + 1 + K) +
          ((4 * nextWord.length + K + 15) + (nextWord.length + 1 + K)))))) := by
  intro read
  have hread := (MultiTapeTM.transformsTapesAt_appendReadTable
    reader value input position hposition word).imp
    (P' := fun actualInput actualPosition tapes => actualInput = input ∧
      actualPosition.val = position.val ∧
      tapes = Function.update (fun _ => []) value word)
    (fun _ _ tapes ⟨hinput, hpos, htapes⟩ =>
      ⟨hinput, hpos, by simp [htapes]⟩)
    (fun _ _ _ _ _ _ _ h => h) le_rfl le_rfl
  have hfrozen := (transformsTapes_frozenRound hValueNext hValueFlag hNextFlag
    hEmitter hNext).freezeInput
  rw [streamRound, toTM_seq, toTM_freezeInput]
  refine (MultiTapeTM.transformsTapesAt_seq hread hfrozen
    fun _ _ _ _ _ _ ⟨_, _, htapes⟩ ⟨_, htapes', _⟩ => by
      rw [htapes', htapes, Function.update_idem]).imp (fun _ _ _ h => h) ?_ le_rfl le_rfl
  rintro _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨hpos, -, rfl⟩, ⟨rfl, htapes, rfl⟩, rfl⟩
  exact ⟨hpos, htapes, rfl⟩

/-- The complete explicit streaming fold: initialize, iterate, finalize, clean, and rewind input. -/
def stream (reader : MultiTapeTM.InputReader Bool Q)
    (initializer : MultiTapeMachine K Bool InitState Empty Id)
    (emitter : MultiTapeMachine K Bool EmitState Empty Id)
    (nextMachine : MultiTapeMachine K Bool NextState Empty Id)
    (finalizer : MultiTapeMachine K Bool FinishState Empty Id)
    (value next flag : Fin K) (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag) :=
  initializer.seq
    ((streamRound reader emitter nextMachine value next flag
      hValueNext hValueFlag hNextFlag).whileInput.seq
      (((finalizer.seq ((clearWork Bool).extendTapes
        (MultiTapeTM.tapeEmb value))).freezeInput).seq (rewindInputOn K Bool)))

/-- The complete explicit stream table computes tidily with the established exact phase bounds. -/
theorem computesTidily_stream_after
    {reader : MultiTapeTM.InputReader Bool Q}
    {initializer : MultiTapeMachine K Bool InitState Empty Id}
    {emitter : MultiTapeMachine K Bool EmitState Empty Id}
    {nextMachine : MultiTapeMachine K Bool NextState Empty Id}
    {finalizer : MultiTapeMachine K Bool FinishState Empty Id}
    {value next flag : Fin K} (hValueNext : value ≠ next)
    (hValueFlag : value ≠ flag) (hNextFlag : next ≠ flag)
    (input inputPrefix initialWord finalWord loopOutput finalOutput : List Bool)
    {initializerTime initializerSpace loopTime loopSpace finalTime finalSpace : ℕ}
    (hInitializer : MultiTapeTM.TransformsTapesAt initializer.toTM
      (fun actualInput position tapes =>
        actualInput = input ∧ position.val = 1 ∧ tapes = fun _ => [])
      (fun _ _ _ position' tapes' output => position'.val = 1 + inputPrefix.length ∧
        tapes' = Function.update (fun _ => []) value initialWord ∧ output = [])
      initializerTime initializerSpace)
    (hloop : MultiTapeTM.TransformsTapesAt
      (streamRound reader emitter nextMachine value next flag
        hValueNext hValueFlag hNextFlag).whileInput.toTM
      (fun actualInput position tapes => actualInput = input ∧
        position.val = 1 + inputPrefix.length ∧
        tapes = Function.update (fun _ => []) value initialWord)
      (fun actualInput _ _ position' tapes' output => actualInput = input ∧
        position'.val = 1 + input.length ∧
        tapes' = Function.update (fun _ => []) value finalWord ∧ output = loopOutput)
      loopTime loopSpace)
    (hFinal : MultiTapeTM.TransformsTapes finalizer.toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value finalWord)
      (fun _ tapes tapes' output => tapes' = tapes ∧ output = finalOutput)
      finalTime finalSpace) :
    (stream reader initializer emitter nextMachine finalizer value next flag
      hValueNext hValueFlag hNextFlag).toTM.ComputesTidilyInTimeAndSpace
      input (loopOutput ++ finalOutput)
      (initializerTime + loopTime +
        ((finalTime + 3 * (finalWord.length + 1)) + (input.length + 2)))
      (initializerSpace +
        (loopSpace + ((finalSpace + (finalWord.length + 1 + K)) + K))) := by
  have hInitializer' := hInitializer.imp
    (Q' := fun actualInput _ _ position' tapes' output => actualInput = input ∧
      position'.val = 1 + inputPrefix.length ∧
      tapes' = Function.update (fun _ => []) value initialWord ∧ output = [])
    (fun _ _ _ h => h) (fun _ _ _ _ _ _ ⟨hinput, _, _⟩ h => ⟨hinput, h⟩)
    le_rfl le_rfl
  rw [toTM_whileInput] at hloop
  have hFinal' := hFinal.imp
    (Q' := fun _ _ tapes' output =>
      tapes' = Function.update (fun _ => []) value finalWord ∧ output = finalOutput)
    (fun _ _ h => h)
    (fun _ _ _ _ htapes ⟨h, he⟩ => ⟨h.trans htapes, he⟩) le_rfl le_rfl
  have hclear := transformsTapes_clearWork_tapeEmb value finalWord
    (Function.update (fun _ => []) value finalWord) (fun _ => [])
    (Function.update_self _ _ _) (by rw [Function.update_idem]; simp)
  have hfin := (hFinal'.seq_eq hclear).freezeInput_eq input (1 + input.length)
  have hrewind := (MultiTapeMachine.transformsTapesAt_rewindInputOn (k := K) input).imp
    (P' := fun actualInput position tapes => actualInput = input ∧
      position.val = 1 + input.length ∧ tapes = (fun _ => []))
    (Q' := fun actualInput _ _ position' tapes' output => actualInput = input ∧
      position'.val = 1 ∧ tapes' = (fun _ => []) ∧ output = [])
    (fun _ _ _ h => h.1)
    (by rintro _ _ _ _ _ _ ⟨hinput, _, rfl⟩ ⟨rfl, htapes, he⟩
        exact ⟨hinput, rfl, htapes, he⟩) le_rfl le_rfl
  have hall := hInitializer'.seq_eq (hloop.seq_eq (hfin.seq_eq hrewind))
  simpa only [stream, toTM_seq, toTM_whileInput, toTM_freezeInput] using
    (hall.transformsTapes (fun _ _ _ _ _ _ h => Fin.ext h.2.1)).imp
    (fun _ _ ⟨hinput, htapes⟩ => ⟨hinput, rfl, htapes⟩)
    (fun _ _ _ _ _ ⟨_, _, htapes, he⟩ => ⟨htapes, by simpa using he⟩)
    (by omega) (by omega)

end Turing.MultiTapeMachine

end
