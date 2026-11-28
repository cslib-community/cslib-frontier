/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelStreamTable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec
public import CslibFrontier.Foundations.Data.Fin.Embedding

/-!
# Named native streaming folds

This module retains an explicit stream table assembled from named callback compilers. The framed
initial state is copied directly from the input prefix, list elements are decoded one frame at a
time, and the input list is never copied to work tapes. The construction records the exact
callback-lifting, loop, finalization, cleanup and rewind bounds from the stream kernel.

No machine is selected from an existential computability certificate. The only supplied bounds
are `sMax`, for the peak lifted callback workspace, and `lMax`, for the encoded state and element
lengths along this particular fold. The per-round clock is the explicit construction formula.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.frameValueReader`: read the contents of one framed
  list element without retaining its framing.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairTable`: the explicit stream assembly
  from named callback tables.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairRoundCost`, `.streamFoldPairTime`,
  `.streamFoldPairWorkspace`: the construction-derived resource formulas.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPair`: retain the concrete single-pass
  stream table and its exact semantic and resource certificate for an initial state paired with
  an encoded list.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Encodings

/-- Read one standard framed value, emitting its contents and stopping after its closing marker. -/
@[expose] def frameValueReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, true => (some true, none)
    | false, false => (none, none)
    | true, bit => (some false, some bit)

/-- `frameValueReader` removes exactly one layer of standard framing. -/
theorem read_frameValueReader (word rest : List Bool) :
    frameValueReader.read false (frame word ++ rest) = (word, (frame word).length) := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [frame_cons, List.cons_append, List.cons_append,
      frameValueReader.read_cons_of_some (q' := true) _ rfl,
      frameValueReader.read_cons_of_some (q' := false) _ rfl, ih]
    simp [frameValueReader, Nat.add_assoc]

/-- The next-state callback followed by the retained framing transducer required by the explicit
stream table. -/
@[expose] def streamFramedNext {Alpha Sigma : Type*}
    {next : Sigma × Alpha → Sigma} {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    (compiler : NativeCompiler next (encPair encS encA) encS) :
    NativeCompiler (fun input => frame (encS (next input)))
      (encPair encS encA) encBits :=
  (encodeFrame encS).comp compiler

/-- The final callback preceded by the retained typed unframing transducer required by the
explicit stream table. -/
@[expose] def streamUnframedFinish {Sigma Phi : Type*}
    {finish : Sigma → Phi} {encS : Sigma ↪ List Bool} {encF : Phi ↪ List Bool}
    (compiler : NativeCompiler finish encS encF) :
    NativeCompiler finish (encFramed encS) encF :=
  compiler.comp (unframeValue encS)

/-- Exact clock of a tidy callback lifted to emit from a selected work tape. -/
@[expose] def inputFromWordTime {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.time input + 4

/-- Construction-derived workspace bound for a tidy callback lifted to emit from a selected work
tape in a `K`-tape stream machine. -/
@[expose] def inputFromWordWorkspace {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (K : ℕ) (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.workspace input + 2 * ((encIn input).length + 2) + 2 * compiler.tapeCount + 8 +
    (K - (compiler.tapeCount + 2))

/-- Exact clock of a tidy callback lifted to write its output between selected work tapes. -/
@[expose] def onWordsTime {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.time input + (encOut (f input)).length + 6

/-- Construction-derived workspace bound for a tidy callback lifted to write its output between
selected work tapes in a `K`-tape stream machine. -/
@[expose] def onWordsWorkspace {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (K : ℕ) (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.workspace input + 2 * (encIn input).length + 2 * (encOut (f input)).length +
    3 * compiler.tapeCount + 18 + (K - (compiler.tapeCount + 1 + 2))

/-- The exact number of tapes in the retained pair-stream assembly. -/
@[expose] def streamFoldPairTapeCount {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) : ℕ :=
  emitCompiler.tapeCount + (streamFramedNext nextCompiler).tapeCount +
    (streamUnframedFinish finishCompiler).tapeCount + 11

/-! ### Explicit stream-machine assembly -/

/-- The retained pair-stream program as one explicit, choice-free transition table. -/
@[expose] def streamFoldPairTable {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) :=
  let framedNext := streamFramedNext nextCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  let M := emitCompiler.tapeCount + framedNext.tapeCount + unframedFinish.tapeCount + 8
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let V : Fin K := ⟨M, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let N : Fin K := ⟨M + 1, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let F : Fin K := ⟨M + 2, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  let emitSource := Fin.natAdd emitCompiler.tapeCount (0 : Fin 2)
  let nextSource := Fin.natAdd (framedNext.tapeCount + 1) (0 : Fin 2)
  let nextTarget := (Fin.last framedNext.tapeCount).castAdd 2
  have hNextSourceTarget : nextSource ≠ nextTarget := by
    simp [nextSource, nextTarget, Fin.ext_iff]
  let finishSource := Fin.natAdd unframedFinish.tapeCount (0 : Fin 2)
  have hEmit : emitCompiler.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount]; omega
  have hNext : framedNext.tapeCount + 1 + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, framedNext]; omega
  have hFinish : unframedFinish.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, unframedFinish]; omega
  let emitEmbedding := Fin.embeddingAt hEmit emitSource V
  let nextEmbedding := Fin.embeddingAt₂ hNext hNextSourceTarget hVN
  let finishEmbedding := Fin.embeddingAt hFinish finishSource V
  MultiTapeMachine.stream frameValueReader (rawFrameReader.appendReadTable V)
    ((emitCompiler.table.inputFromWord true).extendTapes emitEmbedding)
    ((MultiTapeMachine.onWords framedNext.table true).extendTapes nextEmbedding)
    ((unframedFinish.table.inputFromWord true).extendTapes finishEmbedding)
    V N F hVN hVF hNF

/-- Exact time charged to round `j`. Outside the list range it is zero; the stream machine uses
this function only over `Finset.range input.2.length`. -/
@[expose] def streamFoldPairRoundCost {Alpha Sigma Epsilon : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (input : Sigma × List Alpha) (j : ℕ) : ℕ :=
  if hj : j < input.2.length then
    let pair := (streamState input.1 next input.2 j, input.2[j])
    inputFromWordTime emitCompiler pair + onWordsTime (streamFramedNext nextCompiler) pair +
      12 * ((encS (streamState input.1 next input.2 j)).length +
        (encS (streamState input.1 next input.2 (j + 1))).length +
        (encA input.2[j]).length) + 32
  else
    0

/-- Construction-derived clock of the retained pair-stream machine. -/
@[expose] def streamFoldPairTime {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) (input : Sigma × List Alpha) : ℕ :=
  let finalState := streamState input.1 next input.2 input.2.length
  let initialFrame := frame (encS input.1)
  let finalFrame := frame (encS finalState)
  let unframedFinish := streamUnframedFinish finishCompiler
  2 * initialFrame.length + 4 +
    ((encList encA input.2).length +
      (∑ j ∈ Finset.range input.2.length,
        streamFoldPairRoundCost nextCompiler emitCompiler input j) + 1) +
    ((inputFromWordTime unframedFinish finalState + 3 * (finalFrame.length + 1)) +
      ((encPair encS (encList encA) input).length + 2))

/-- Construction-derived workspace bound of the retained pair-stream machine. -/
@[expose] def streamFoldPairWorkspace {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (sMax lMax : Sigma × List Alpha → ℕ) (input : Sigma × List Alpha) : ℕ :=
  let finalState := streamState input.1 next input.2 input.2.length
  let initialFrame := frame (encS input.1)
  let finalFrame := frame (encS finalState)
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  initialFrame.length + 2 + (K - 1) +
    (2 * K * (sMax input + 16 * lMax input + 4 * K + 26) + K +
      (inputFromWordWorkspace K unframedFinish finalState +
        (finalFrame.length + 1 + K) + K))

/-- Retain the concrete pair-prefix streaming fold. `sMax` bounds the sum of the two lifted
callback workspaces in each round; `lMax` bounds every encoded stream state and element. -/
@[expose] def streamFoldPair
    {Alpha Sigma Epsilon Phi Omega : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi} {result : Sigma × List Alpha → Omega}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    {encOut : Omega ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (hresult : ∀ input, encOut (result input) =
      streamEmit next (fun pair => encE (emit pair)) input.1 input.2 ++
        encF (finish (streamState input.1 next input.2 input.2.length)))
    (sMax lMax : Sigma × List Alpha → ℕ)
    (hspace : ∀ input j (hj : j < input.2.length),
      let pair := (streamState input.1 next input.2 j, input.2[j])
      inputFromWordWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          emitCompiler pair +
        onWordsWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          (streamFramedNext nextCompiler) pair ≤ sMax input)
    (hstate : ∀ input j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lMax input)
    (helem : ∀ input j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lMax input) :
    NativeCompiler result (encPair encS (encList encA)) encOut := by
  let framedNext := streamFramedNext nextCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  let M := emitCompiler.tapeCount + framedNext.tapeCount + unframedFinish.tapeCount + 8
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let V : Fin K := ⟨M, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let N : Fin K := ⟨M + 1, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let F : Fin K := ⟨M + 2, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  let emitSource := Fin.natAdd emitCompiler.tapeCount (0 : Fin 2)
  let nextSource := Fin.natAdd (framedNext.tapeCount + 1) (0 : Fin 2)
  let nextTarget := (Fin.last framedNext.tapeCount).castAdd 2
  have hNextSourceTarget : nextSource ≠ nextTarget := by
    simp [nextSource, nextTarget, Fin.ext_iff]
  let finishSource := Fin.natAdd unframedFinish.tapeCount (0 : Fin 2)
  have hEmit : emitCompiler.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount]; omega
  have hNext : framedNext.tapeCount + 1 + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, framedNext]; omega
  have hFinish : unframedFinish.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, unframedFinish]; omega
  let emitEmbedding := Fin.embeddingAt hEmit emitSource V
  let nextEmbedding := Fin.embeddingAt₂ hNext hNextSourceTarget hVN
  let finishEmbedding := Fin.embeddingAt hFinish finishSource V
  have emitInput : emitEmbedding (Fin.natAdd emitCompiler.tapeCount (0 : Fin 2)) = V := by
    simpa only [emitEmbedding, emitSource, K] using
      Fin.embeddingAt_source hEmit emitSource V
  have nextInput :
      nextEmbedding (Fin.natAdd (framedNext.tapeCount + 1) (0 : Fin 2)) = V := by
    simpa only [nextEmbedding, nextSource, framedNext, K] using
      Fin.embeddingAt₂_first hNext hNextSourceTarget hVN
  have nextOutput : nextEmbedding ((Fin.last framedNext.tapeCount).castAdd 2) = N := by
    simpa only [nextEmbedding, nextTarget, framedNext, K] using
      Fin.embeddingAt₂_second hNext hNextSourceTarget hVN
  have finishInput :
      finishEmbedding (Fin.natAdd unframedFinish.tapeCount (0 : Fin 2)) = V := by
    simpa only [finishEmbedding, finishSource, unframedFinish, K] using
      Fin.embeddingAt_source hFinish finishSource V
  let initializer := rawFrameReader.appendReadTable V
  let emitter :=
    (emitCompiler.table.inputFromWord true).extendTapes emitEmbedding
  let nextMachine :=
    (MultiTapeMachine.onWords framedNext.table true).extendTapes nextEmbedding
  let finalizer :=
    (unframedFinish.table.inputFromWord true).extendTapes finishEmbedding
  let table := streamFoldPairTable nextCompiler emitCompiler finishCompiler
  letI := emitCompiler.stateFintype
  letI := framedNext.stateFintype
  letI := unframedFinish.stateFintype
  let appendReadEncoding := sumStateEncoding unitStateEncoding
    (sumStateEncoding Universal.eBit rewindWorkStateEncoding)
  let clearEncoding := sumStateEncoding unitStateEncoding rewindWorkStateEncoding
  let copyEncoding := sumStateEncoding markWorkStateEncoding
    (sumStateEncoding
      (sumStateEncoding (sumStateEncoding unitStateEncoding rewindStateEncoding)
        rewindWorkStateEncoding)
      markWorkStateEncoding)
  let emitterEncoding := sumStateEncoding markWorkStateEncoding
    (sumStateEncoding emitCompiler.stateEncoding markWorkStateEncoding)
  let nextEncoding := sumStateEncoding markWorkStateEncoding
    (sumStateEncoding
      (sumStateEncoding framedNext.stateEncoding rewindWorkStateEncoding)
      markWorkStateEncoding)
  let finalizerEncoding := sumStateEncoding markWorkStateEncoding
    (sumStateEncoding unframedFinish.stateEncoding markWorkStateEncoding)
  let frozenRoundEncoding := sumStateEncoding emitterEncoding
    (sumStateEncoding nextEncoding
      (sumStateEncoding clearEncoding (sumStateEncoding copyEncoding clearEncoding)))
  let roundEncoding := sumStateEncoding appendReadEncoding frozenRoundEncoding
  let stateEncoding := sumStateEncoding appendReadEncoding
    (sumStateEncoding (sumStateEncoding roundEncoding unitStateEncoding)
      (sumStateEncoding (sumStateEncoding finalizerEncoding clearEncoding)
        rewindStateEncoding))
  refine
    { tapeCount := K
      State := _
      table := table
      stateEncoding := stateEncoding
      time := streamFoldPairTime nextCompiler emitCompiler finishCompiler
      workspace := streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler sMax lMax
      computes := ?_ }
  intro input
  let finalState := streamState input.1 next input.2 input.2.length
  have hreadInit : rawFrameReader.read rawFrameReader.q₀
      ((encPair encS (encList encA) input).drop 0) =
      (frame (encS input.1), (frame (encS input.1)).length) := by
    rw [List.drop_zero, encPair_apply]
    exact read_rawFrameReader (encS input.1) (encList encA input.2)
  have hinit := transformsTapesAt_appendReadTable rawFrameReader V
    (encPair encS (encList encA) input) 1 (by simp) []
  simp only [Fin.val_one, Nat.sub_self, hreadInit, List.length_nil, List.nil_append] at hinit
  have hinit' := hinit.imp
    (P' := fun input' p ws => input' = encPair encS (encList encA) input ∧
      p.val = 1 ∧ ws = fun _ => [])
    (Q' := fun _ _ _ p' ws' e => p'.val = 1 + (frame (encS input.1)).length ∧
      ws' = Function.update (fun _ => []) V (frame (encS input.1)) ∧ e = [])
    (fun _ _ ws ⟨hin, hp, hws⟩ => ⟨hin, hp, by simp [hws]⟩)
    (by
      rintro _ _ ws _ _ _ ⟨_, _, rfl⟩ ⟨hp, hws, hem⟩
      exact ⟨hp, hws, hem⟩)
    le_rfl le_rfl
  have hE := fun pair => MultiTapeMachine.transformsTapes_inputFromWord_extendTapes true
    (emitCompiler.computes pair) emitInput
  have hN := fun pair => MultiTapeMachine.transformsTapes_onWords_extendTapes true
    (framedNext.computes pair) nextInput nextOutput
  have hloop := transformsTapesAt_streamLoop_encoded_after_of_round
    (round := (MultiTapeMachine.streamRound frameValueReader emitter nextMachine
      V N F hVN hVF hNF).toTM)
    (roundSpec := MultiTapeMachine.transformsTapesAt_streamRound
      (reader := frameValueReader) (emitter := emitter) (nextMachine := nextMachine)
      hVN hVF hNF)
    frameValueReader
    (fun value => frame (encA value)) (fun value => frame_ne_nil (encA value))
    (fun value rest => read_frameValueReader (encA value) rest)
    (frame (encS input.1)) input.1 input.2 next (fun pair => encE (emit pair)) hE hN
    (roundCost := streamFoldPairRoundCost nextCompiler emitCompiler input)
    (sMax := sMax input) (lMax := lMax input) (by
      intro j hj
      simp only [streamFoldPairRoundCost, hj, dite_true, inputFromWordTime, onWordsTime,
        framedNext, streamFramedNext, encBits_apply]
      rw [streamState_succ input.1 next input.2 hj])
    (by
      intro j hj
      simpa only [inputFromWordWorkspace, onWordsWorkspace, framedNext] using
        hspace input j hj)
    (hstate input) (helem input)
  have hF := MultiTapeMachine.transformsTapes_inputFromWord_extendTapes true
    (unframedFinish.computes finalState) finishInput
  rw [← MultiTapeMachine.toTM_whileInput
    (MultiTapeMachine.streamRound frameValueReader emitter nextMachine
      V N F hVN hVF hNF)] at hloop
  have h := MultiTapeMachine.computesTidily_stream_after
    (reader := frameValueReader) (initializer := initializer) (emitter := emitter)
    (nextMachine := nextMachine) (finalizer := finalizer)
    hVN hVF hNF
    (encPair encS (encList encA) input) (frame (encS input.1))
    (frame (encS input.1)) (frame (encS finalState))
    (streamEmit next (fun pair => encE (emit pair)) input.1 input.2)
    (encF (finish finalState)) hinit' hloop hF
  rw [hresult input]
  have hencList :
      encList encA input.2 =
        List.flatMap (fun value => frame (encA value)) input.2 := rfl
  refine h.mono ?_ ?_
  · simp only [streamFoldPairTime, inputFromWordTime, finalState, hencList, unframedFinish]
    omega
  · simp only [streamFoldPairWorkspace, inputFromWordWorkspace, finalState, unframedFinish]
    exact le_rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
