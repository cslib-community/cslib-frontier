/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexParameters
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.SpaceNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Combined parameter and ID input

The input is a framed `encParameters` prefix followed by unchanged canonical choice bits.
Only the prefix is extracted for preparation. The streaming pass skips that prefix and feeds
bits to the existing reader, ignoring bits after the declared ID width. The pass traverses the
whole supplied word; it does not generate nondeterministic choices or implement full scan lowering.

## Main results

* `run_eq`: agreement with parameter validation and the existing reader.
* `prefix_length_le`: header dispatch and reader registers occupy at most
  `12 * ((encParameters input.parameters).length + 1)` bits at every streamed prefix.
* `native_run`: one native machine with workspace bounded by a uniform constant times that
  parameter length, independently of the supplied choice suffix length.

The combined encoding is `frame (encParameters parameters) ++ choices`. Parameter extraction
uses the existing finite `readFrameT` transducer with zero workspace. The streaming backend
runs native preparation once, resets to the original input, skips the header with a binary
counter and feeds only the declared ID prefix to the existing reader. It scans the rest of
the supplied word without advancing the reader, then finalizes. Thus it is a deterministic
supplied-word interface, not an exact first-halting nondeterministic choice-consumption theorem.
The parameter-length bound in `VertexParameters.length_encParameters_le` gives logarithmic
workspace in `dimension + claimedWidth`, including invalid parameter values.

The ordinary-import client is `CslibFrontierTests.DoubleCountingCombined`.
Nondeterministic choice production, original graph-tape composition and full native scan lowering
remain in [#6747](https://github.com/cslib-community/cslib-frontier/issues/6747).
-/

public section
namespace Turing.DoubleCounting.Combined
open MultiTapeTM ComputableInSpace VertexReader VertexParameters

/-- One parameter header and its read-only choice suffix. -/
structure Input where
  /-- Runtime dimension and claimed width. -/
  parameters : Parameters
  /-- Supplied ID source, possibly truncated or followed by further words. -/
  choices : List Bool

/-- Framed existing parameter encoding, followed by raw canonical ID bits. -/
enc_structure encInput : Input where parameters : encParameters, choices : encBits

/-- Header cells still to skip and the retained reader registers. -/
structure Context where
  /-- Remaining cells of the framed parameter prefix. -/
  skip : ℕ
  /-- Existing ID reader state, including dimension and width. -/
  reader : State

/-- Framed binary skip counter followed by the existing reader-state encoding. -/
enc_structure encContext : Context where skip : encNat, reader : encState

/-- Closed failed preparation state, exposed so ordinary-import `start` computes. -/
@[expose] def rejected : State := ⟨0, 0, 0, 0, true⟩

/-- Runtime preparation and the exact prefix offset; no choice suffix is copied. -/
@[expose] def start (x : Input) : Context :=
  ⟨2 * (encParameters x.parameters).length + 1, (prepare x.parameters).getD rejected⟩

/-- Existing reader step with an explicitly supplied present bit. Its body is exposed so
ordinary-import clients can evaluate `step`; Lean disallows private dependencies in that body. -/
@[expose] def feed (s : State) (b : Bool) : State :=
  if (machine 0).halted s then s else (machine 0).next (s, some b)

/-- One original-input cell: skip header cells, then use the existing reader transition. -/
@[expose] def step : Context × Bool → Context
  | (⟨0, s⟩, b) => ⟨0, feed s b⟩
  | (⟨k + 1, s⟩, _) => ⟨k, s⟩

/-- Reject unfinished header/ID input; otherwise retain the reader's range/truncation check. -/
@[expose] def finish (s : Context) : Option ℕ :=
  if s.skip = 0 ∧ s.reader.cursor = s.reader.width then result s.reader else none

/-- One streaming interface on the combined encoded input. -/
@[expose] def run (x : Input) : Option ℕ :=
  finish ((encInput x).foldl (fun s b => step (s, b)) (start x))

private theorem fold_skip (s : State) (bits : List Bool) (k : ℕ) (h : bits.length ≤ k) :
    bits.foldl (fun s b => step (s, b)) ⟨k, s⟩ = ⟨k - bits.length, s⟩ := by
  induction bits generalizing k with
  | nil => simp
  | cons b bits ih =>
    cases k with
    | zero => simp at h
    | succ k => simpa [step] using ih k (by simpa using h)

private theorem fold_zero (s : State) (bits : List Bool) :
    bits.foldl (fun s b => step (s, b)) ⟨0, s⟩ = ⟨0, bits.foldl feed s⟩ := by
  induction bits generalizing s with
  | nil => rfl
  | cons b bits ih => simpa [step] using ih (feed s b)

private theorem feed_run (N : ℕ) (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    (w.take j).foldl feed (machine N).init = (machine N).run w j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, ih (by omega),
      List.foldl_cons, List.foldl_nil, QueryMachine.run_succ]
    have hget := List.getElem?_eq_getElem (show j < w.length by omega)
    unfold feed QueryMachine.step QueryMachine.read
    change (if (machine N).halted ((machine N).run w j) then (machine N).run w j
      else (machine N).next ((machine N).run w j, some w[j])) =
      (if (machine N).halted ((machine N).run w j) then (machine N).run w j
      else (machine N).next ((machine N).run w j, w[(machine N).query ((machine N).run w j)]?))
    by_cases ht : j < N.size
    · rw [query_run N w j ht, hget]
    · rw [(halted_iff N w j).mpr (by omega)]
      rfl

private theorem fold_rejected (bits : List Bool) : bits.foldl feed rejected = rejected := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [feed, rejected, machine, VertexReader.isHalted] using ih

private theorem prefix_eq (x : Input) (j : ℕ) :
    (encInput x |>.take j).foldl (fun s b => step (s, b)) (start x) =
      if j ≤ (frame (encParameters x.parameters)).length then
        ⟨(frame (encParameters x.parameters)).length - j, (start x).reader⟩
      else ⟨0, (x.choices.take (j - (frame (encParameters x.parameters)).length)).foldl
        feed (start x).reader⟩ := by
  have hh : (start x).skip = (frame (encParameters x.parameters)).length := by
    simp [start]
  rw [encInput_apply]
  simp only [encInputFields, encPair_apply, encBits_apply, List.take_append, List.foldl_append]
  rw [show start x = ⟨(frame (encParameters x.parameters)).length, (start x).reader⟩ from
    hh ▸ rfl]
  rw [fold_skip (start x).reader ((frame (encParameters x.parameters)).take j)
    (frame (encParameters x.parameters)).length (by simp only [List.length_take]; omega)]
  dsimp only
  by_cases hj : j ≤ (frame (encParameters x.parameters)).length
  · simp only [hj, ite_true, Nat.sub_eq_zero_of_le hj, List.length_take,
      Nat.min_eq_left hj, List.take_zero, List.foldl_nil]
  · simp only [hj, ite_false, List.length_take, Nat.min_eq_right (by omega :
        (frame (encParameters x.parameters)).length ≤ j), Nat.sub_self]
    exact fold_zero _ _

/-- Exact semantic agreement with validation and the existing ID reader, including rejection. -/
theorem run_eq (x : Input) :
    run x = (prepare x.parameters).bind (fun s =>
      result ((machine 0).runFrom x.choices s x.parameters.width)) := by
  have hfull := prefix_eq x (encInput x).length
  rw [List.take_length] at hfull
  have hlen : (encInput x).length =
      (frame (encParameters x.parameters)).length + x.choices.length := by
    simp [encInput_apply, encInputFields]
  have hstate : (encInput x).foldl (fun s b => step (s, b)) (start x) =
      ⟨0, x.choices.foldl feed (start x).reader⟩ := by
    rw [hlen] at hfull
    by_cases he : x.choices = []
    · simpa [he] using hfull
    · have hp : 0 < x.choices.length := List.length_pos_iff.mpr he
      simpa [he, show ¬(frame (encParameters x.parameters)).length + x.choices.length ≤
        (frame (encParameters x.parameters)).length by omega] using hfull
  rw [run, hstate]
  cases hp : prepare x.parameters with
  | none =>
    simp only [start, hp, Option.getD_none, fold_rejected]
    simp [finish, rejected, result]
  | some s =>
    obtain ⟨hw, rfl⟩ := (prepare_eq_some_iff _ _).mp hp
    have hf := List.take_length (l := x.choices) ▸
      feed_run x.parameters.dimension x.choices x.choices.length le_rfl
    simp only [start, hp, Option.getD_some, hf, finish, true_and, Option.bind_some]
    rw [runFrom_prepare _ _ hp, hw]
    by_cases hl : x.parameters.dimension.size ≤ x.choices.length
    · rw [(machine x.parameters.dimension).run_eq_of_le x.choices
        ((halted_iff _ _ _).mpr le_rfl) hl]
      simp [run_eq_prefix]
    · have hc : min x.choices.length x.parameters.dimension.size ≠
          x.parameters.dimension.size := by omega
      rw [run_eq_prefix, run_eq_prefix]
      simp [hc, result, show x.choices.length < x.parameters.dimension.size by omega]

private theorem reader_length_le (p : Parameters) (bits : List Bool) :
    (encState (bits.foldl feed ((prepare p).getD rejected))).length ≤
      8 * (encParameters p).length + 9 := by
  cases hp : prepare p with
  | none =>
    rw [Option.getD_none, fold_rejected]
    simp [rejected, encState_apply, encStateFields]
  | some s =>
    obtain ⟨_, rfl⟩ := (prepare_eq_some_iff p s).mp hp
    simp only [Option.getD_some,
      List.take_length (l := bits) ▸ feed_run p.dimension bits bits.length le_rfl]
    have := length_run_le p.dimension bits bits.length
    have : p.dimension.size ≤ (encParameters p).length := by
      simp only [encParameters_apply, encParametersFields, length_encPair,
        encNat_apply, ← Nat.size_eq_bits_len]
      omega
    have := Nat.log2_le_self p.dimension.size
    omega

/-- All retained dispatch/reader context is bounded independently of the choice suffix length. -/
theorem prefix_length_le (x : Input) (j : ℕ) :
    (encContext ((encInput x |>.take j).foldl (fun s b => step (s, b)) (start x))).length ≤
      12 * ((encParameters x.parameters).length + 1) := by
  rw [prefix_eq]
  split
  · have hr := reader_length_le x.parameters []
    change (encState (start x).reader).length ≤ _ at hr
    have hk := (length_encNat_le_self
      ((frame (encParameters x.parameters)).length - j)).trans (Nat.sub_le _ _)
    simp only [length_frame] at hk
    simp only [encContext_apply, encContextFields, length_encPair, length_frame]
    omega
  · have hr := reader_length_le x.parameters
      (x.choices.take (j - (frame (encParameters x.parameters)).length))
    change (encState ((x.choices.take (j - (frame (encParameters x.parameters)).length)).foldl
      feed (start x).reader)).length ≤ _ at hr
    simp only [encContext_apply, encContextFields, length_encPair]
    have hz : (encNat 0).length = 0 := rfl
    rw [hz]
    omega

private theorem parameters_inSpace : ComputableInSpace Input.parameters encInput encParameters
    (fun x => (encParameters x.parameters).length) :=
  ComputableInSpace.framedPrefix Input.parameters encInput encParameters Input.choices
    (fun x => by simp [encInput_apply, encInputFields])

/-- Native initialization reads only the small prefix into work space; its certificate does
not charge or retain the choice suffix. -/
theorem start_inSpace : ComputableInSpace start encInput encContext
    (fun x => (encParameters x.parameters).length) := by
  have hp := parameters_inSpace
  have hn := budget_comp_linear natSize (encParameters_dimension_budget hp)
  have hw := budget_comp_linear natSize (encParameters_width_budget hp)
  have hone : ComputableInSpace (fun _ : Input => 1) encInput encNat
      (fun x => (encParameters x.parameters).length) :=
    budget_const 1
  have hlen := budget_natAdd (budget_natAdd (budget_natAdd hn hn) hone) hw
  have hoff := budget_natAdd (budget_natAdd hlen hlen) hone
  have hprep := budget_comp_linear prepare_inSpace hp
  have hload := budget_optionGetD (encB := encState) rejected hprep
  exact (encContext_mk_budget hoff hload).of_enc_eq fun x => by
    apply congrArg encContext
    simp only [start]
    congr 1
    simp only [encParameters_apply, encParametersFields, length_encPair,
      encNat_apply, ← Nat.size_eq_bits_len]
    omega

private theorem feed_inSpace : ComputableInSpace (fun p : State × Bool => feed p.1 p.2)
    (encPair encState encBool) encState (fun p => (encPair encState encBool p).length) := by
  have hs := fst encState encBool
  have hb := snd encState encBool
  exact budget_ite (budget_comp_linear (halted_inSpace 0) hs) hs
    (budget_comp_linear (next_inSpace 0) (budget_prod hs (budget_optionSome hb)))

/-- Native header skipping and bit delivery reuse the certified reader step. -/
theorem step_inSpace : ComputableInSpace step (encPair encContext encBool) encContext
    (fun p => (encPair encContext encBool p).length) := by
  have hc := fst encContext encBool
  have hk := encContext_skip_budget hc
  have hr := encContext_reader_budget hc
  exact (encContext_mk_budget (budget_natPred hk)
    (budget_ite (budget_natIsZero hk)
      (budget_comp_linear feed_inSpace (budget_prod hr (snd encContext encBool))) hr)).of_enc_eq
    fun (⟨k, _⟩, _) => by cases k <;> simp [step]

/-- Native completion checks account for truncated IDs and retained reader context. -/
theorem finish_inSpace : ComputableInSpace finish encContext (encOption encNat)
    (fun s => (encContext s).length) := by
  have hid := of_inO
    (ComputableInO.of_eq (encIn := encContext) (encMid := encContext) fun _ => rfl)
  have hr := encContext_reader_budget hid
  exact (budget_ite (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
      (budget_prod (budget_natIsZero (encContext_skip_budget hid))
        (budget_natEq (encState_cursor_budget hr) (encState_width_budget hr))))
    (budget_comp_linear result_inSpace hr) (budget_const none)).of_enc_eq fun s => by
      simp [finish, Bool.and_eq_true]

/-- One actual native machine performs prefix dispatch, parameter preparation and streaming
ID decoding. Its workspace is uniform in runtime parameters and independent of suffix length.
This deterministic supplied-word interface makes no nondeterministic occurrence claim. -/
theorem native_run : ∃ time c, ComputableInTimeAndSpace run encInput (encOption encNat) time
    (fun x => c * ((encParameters x.parameters).length + 1)) := by
  obtain ⟨TI, cI, hI, _⟩ := Internal.NormalForm.space start_inSpace
  obtain ⟨TN, cN, hN, _⟩ := Internal.NormalForm.space step_inSpace
  obtain ⟨TF, cF, hF, _⟩ := Internal.NormalForm.space finish_inSpace
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair encContext encBool) (encOut := encBits) ([] : List Bool)
  let B : Input → ℕ := fun x => 12 * ((encParameters x.parameters).length + 1)
  let R : Input → ℕ → ℕ := fun x j =>
    cN * (TN (streamState (start x) step (encInput x) j, (encInput x)[j]!) + 1) +
      2 * cE + 2 * B x + 4
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold_sum
    (encIn := encInput) (encOut := encOption encNat)
    reader (fun b : Bool => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    (fun x => encInput x) (fun x => by simp)
    (init := start) (next := step) (emit := fun _ => ([] : List Bool)) (finish := finish)
    (g := run) hI hN hE.computableTidilyInTimeAndSpace hF
    (fun x => by
      simp only [encBits_apply, streamEmit_const_nil, List.nil_append,
        streamState, List.take_length, run])
    (roundCost := R) (sMax := fun x => cN * (2 * B x + 3) + cE) (lMax := B)
    (fun x j hj => by
      have h0 := prefix_length_le x j
      have h1 := prefix_length_le x (j + 1)
      simp only [R, streamState, encBool_apply, List.length_singleton]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      dsimp only [B] at *
      omega)
    (fun x j hj => by
      have h0 := prefix_length_le x j
      have hm := Nat.mul_le_mul_left cN (show
          (encPair encContext encBool
            (streamState (start x) step (encInput x) j, (encInput x)[j])).length + 1 ≤
            2 * B x + 3 by
        simp only [length_encPair, encBool_apply, List.length_singleton, streamState]
        dsimp only [B]
        omega)
      omega)
    (fun x j _ => prefix_length_le x j)
    (fun x _ _ => by simp only [encBool_apply, List.length_singleton]; dsimp [B]; omega)
  refine ⟨_, c * (cI + 13 * cF + 27 * cN + cE + 13),
    (ComputableTidilyInTimeAndSpace.computableInTimeAndSpace h).mono
      (fun _ => le_rfl) (fun x => ?_)⟩
  have hlast := prefix_length_le x (encInput x).length
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left c
  have hmF := Nat.mul_le_mul_left cF (show
      (encContext (streamState (start x) step (encInput x) (encInput x).length)).length + 1 ≤
        13 * ((encParameters x.parameters).length + 1) by
    simp only [streamState]
    omega)
  dsimp only [B]
  nlinarith

end Turing.DoubleCounting.Combined
