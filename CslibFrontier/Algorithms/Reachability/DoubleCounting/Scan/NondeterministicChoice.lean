/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexReader
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Nondeterministic stop or destination choice

One choice at a destination boundary consumes the leading bit of
`Cslib.DoubleCounting.Scan.Binary.destinations`. False stops. True reads one fixed-width
vertex ID from the next nondeterministic bits, using the existing vertex reader's registers.
The query answer from the original input is ignored during this phase.

## Main results

* `firstHalting_accept_iff` identifies the exact successful traces.
* `firstHalting_stop_iff` and `firstHalting_vertex_iff` specify their returned flags and ranks.
* `length_run_le` bounds every encoded state, including out-of-range choices.
* `exists_routines` compiles this phase given a certified start on the original input.
* `native_firstHalting_accept_iff` characterizes successful native occurrence traces.

This is the choice phase for #6747. The surrounding scan supplies the dimension, owns the
remaining path budget, and runs the same-input adjacency callback after a valid choice.
-/

public section

namespace Turing.DoubleCounting.NondeterministicChoice

open Cslib.DoubleCounting.Scan.Binary MultiTapeTM ComputableInSpace

/-- Registers for one destination boundary. The two flags distinguish waiting for the marker,
stopping, and reading a vertex. -/
structure State where
  /-- True once the continue marker has been chosen. -/
  reading : Bool
  /-- True once the stop marker has been chosen. -/
  stopped : Bool
  /-- Vertex reader registers, initially positioned at the start of the ID. -/
  reader : VertexReader.State

/-- Two framed flags followed by the binary vertex reader registers. -/
enc_structure encState : State where
  reading : encBool, stopped : encBool, reader : VertexReader.encState

/-- The runtime selects stop or starts a fixed-width vertex reader. A completed out-of-range
ID rejects. A successful halted state returns stop via `stopped`, or the rank via
`VertexReader.result`. -/
@[expose] def machine (N : ℕ) : NondeterministicQueryMachine State where
  init := ⟨false, false, (VertexReader.machine N).init⟩
  query _ := 0
  next := fun (s, _, bit) =>
    if s.reading then { s with reader := VertexReader.advance s.reader (some bit) }
    else ⟨bit, !bit, s.reader⟩
  halted s := s.stopped || (s.reading && (VertexReader.machine N).halted s.reader)
  accept s := s.stopped || (s.reading && (VertexReader.result s.reader).isSome)

private theorem accept_eq (N : ℕ) (s : State) :
    (machine N).accept s = (s.stopped || (s.reading && (VertexReader.result s.reader).isSome)) :=
  rfl

private theorem replay_reading (N : ℕ) (input consumed bits : List Bool) :
    (machine N).replay input bits
      ⟨true, false, (VertexReader.machine N).run (consumed ++ bits) consumed.length⟩ =
      ⟨true, false,
        (VertexReader.machine N).run (consumed ++ bits) (consumed.length + bits.length)⟩ := by
  induction bits generalizing consumed with
  | nil => simp
  | cons bit bits ih =>
    have he : consumed ++ bit :: bits = (consumed ++ [bit]) ++ bits := by simp
    have hlen : (consumed ++ [bit]).length = consumed.length + 1 := by simp
    let R := VertexReader.machine N
    have hstep :
        (machine N).step input ⟨true, false, R.run (consumed ++ bit :: bits) consumed.length⟩ bit =
          ⟨true, false, R.run (consumed ++ bit :: bits) (consumed.length + 1)⟩ := by
      rw [QueryMachine.run_succ]
      by_cases h : consumed.length < N.size
      · have hlive : R.halted (R.run (consumed ++ bit :: bits) consumed.length) = false :=
          Bool.eq_false_iff.mpr fun ht => by
            have := (VertexReader.halted_iff _ _ _).mp ht
            omega
        have hread : R.read (consumed ++ bit :: bits)
            (R.run (consumed ++ bit :: bits) consumed.length) = some bit := by
          unfold QueryMachine.read
          rw [VertexReader.query_run N _ _ h, List.getElem?_append_right le_rfl, Nat.sub_self]
          rfl
        change (if R.halted _ then _ else _) = State.mk true false (R.step _ _)
        rw [hlive]
        simp only [Bool.false_eq_true, ite_false, QueryMachine.step, hlive, hread]
        rfl
      · have hhalt : R.halted (R.run (consumed ++ bit :: bits) consumed.length) = true :=
          (VertexReader.halted_iff _ _ _).mpr (by omega)
        simp [NondeterministicQueryMachine.step, QueryMachine.step, machine, hhalt, R]
    rw [NondeterministicQueryMachine.replay_cons, hstep, he, ← hlen, ih]
    congr 2
    simp only [List.length_cons]
    omega

/-- A continue marker starts the fixed-width reader on the remaining selector bits. -/
theorem run_continue (N : ℕ) (input bits : List Bool) :
    (machine N).run input (true :: bits) =
      ⟨true, false, (VertexReader.machine N).run bits bits.length⟩ := by
  simpa [NondeterministicQueryMachine.run, NondeterministicQueryMachine.replay_cons,
    NondeterministicQueryMachine.step, machine] using replay_reading N input [] bits

private theorem run_stop (N : ℕ) (input bits : List Bool) :
    (machine N).run input (false :: bits) = ⟨false, true, (VertexReader.machine N).init⟩ := by
  rw [NondeterministicQueryMachine.run, NondeterministicQueryMachine.replay_cons]
  exact (machine N).replay_of_halted input rfl bits

/-- A continuation first halts after exactly the fixed width of the vertex reader. -/
theorem firstHalting_continue_iff (N : ℕ) (input bits : List Bool) :
    (machine N).FirstHalting input (true :: bits) (machine N).init ↔ bits.length = N.size := by
  have hh (bs : List Bool) :
      (machine N).halted ((machine N).run input (true :: bs)) = true ↔ N.size ≤ bs.length := by
    rw [run_continue]
    exact VertexReader.halted_iff N bs bs.length
  constructor
  · intro h
    have hlo := (hh bits).mp h.1
    by_contra! hne
    have hlt : N.size < bits.length := by omega
    have hp := h.2 (N.size + 1) (by simpa using hlt)
    rw [List.take_succ_cons] at hp
    have ht := (hh (bits.take N.size)).mpr (by simp [List.length_take, Nat.min_eq_left hlt.le])
    exact Bool.noConfusion (hp.symm.trans ht)
  · intro h
    refine ⟨(hh bits).mpr h.ge, ?_⟩
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      rw [List.take_succ_cons]
      apply Bool.eq_false_iff.mpr
      intro ht
      have hle := (hh (bits.take n)).mp ht
      have hp := List.length_take_le n bits
      simp only [List.length_cons] at hn
      omega

/-- Stopping successfully at the first halt has exactly the single stop marker as trace. -/
theorem firstHalting_stop_iff (N : ℕ) (input choices : List Bool) :
    (machine N).FirstHalting input choices (machine N).init ∧
      ((machine N).run input choices).stopped = true ↔ choices = [false] := by
  cases choices with
  | nil => simp [NondeterministicQueryMachine.FirstHalting, machine]
  | cons bit bits =>
    cases bit
    · rw [run_stop]
      constructor
      · rintro ⟨h, _⟩
        cases bits with
        | nil => rfl
        | cons b bs => exact Bool.noConfusion (h.2 1 (by simp))
      · rintro h
        cases h
        refine ⟨⟨rfl, ?_⟩, rfl⟩
        intro n hn
        have hnzero : n = 0 := by simpa using hn
        subst n
        rfl
    · simp [run_continue]

/-- At the fixed width, the continuation returns the canonical range-checked decoder. -/
theorem result_run_continue (N : ℕ) (input bits : List Bool)
    (hlen : bits.length = N.size) :
    VertexReader.result ((machine N).run input (true :: bits)).reader =
      (decodeVertex (N := N) bits).map Fin.val := by
  rw [run_continue]
  change VertexReader.result ((VertexReader.machine N).run bits bits.length) = _
  rw [hlen, VertexReader.result_eq_decodeVertex, List.take_of_length_le hlen.le]

/-- A first halt yields a valid rank while reading precisely for the canonical continue marker
and vertex ID. This gives both directions of the trace correspondence for each vertex. -/
theorem firstHalting_vertex_iff (N : ℕ) (input choices : List Bool) (v : Fin N) :
    (machine N).FirstHalting input choices (machine N).init ∧
      ((machine N).run input choices).reading = true ∧
      VertexReader.result ((machine N).run input choices).reader = some v.val ↔
      choices = true :: vertex v := by
  cases choices with
  | nil => simp [machine]
  | cons bit bits =>
    cases bit
    · simp [run_stop]
    · have hreading : ((machine N).run input (true :: bits)).reading = true := by
        rw [run_continue]
      simp only [firstHalting_continue_iff, hreading, true_and, List.cons.injEq]
      constructor
      · rintro ⟨hlen, hresult⟩
        rw [result_run_continue N input bits hlen] at hresult
        obtain ⟨u, hu, huv⟩ := Option.map_eq_some_iff.mp hresult
        have he : u = v := Fin.ext huv
        exact (decodeVertex_eq_some_iff bits v).mp (he ▸ hu)
      · rintro rfl
        refine ⟨length_vertex v, ?_⟩
        rw [result_run_continue N input _ (length_vertex v),
          (decodeVertex_eq_some_iff _ v).mpr rfl]
        rfl

/-- The accepted first-halting traces are precisely the canonical destination-boundary choices. -/
theorem firstHalting_accept_iff (N : ℕ) (input choices : List Bool) :
    (machine N).FirstHalting input choices (machine N).init ∧
      (machine N).accept ((machine N).run input choices) = true ↔
      choices = [false] ∨ ∃ v : Fin N, choices = true :: vertex v := by
  constructor
  · rintro ⟨hfirst, haccept⟩
    by_cases hstop : ((machine N).run input choices).stopped = true
    · exact Or.inl ((firstHalting_stop_iff N input choices).mp ⟨hfirst, hstop⟩)
    · have hread :
          ((machine N).run input choices).reading = true ∧
            (VertexReader.result ((machine N).run input choices).reader).isSome = true := by
        simpa [accept_eq, Bool.eq_false_iff.mpr hstop] using haccept
      cases choices with
      | nil => simp [machine] at hread
      | cons bit bits =>
        cases bit
        · simp [run_stop] at hread
        · have hlen := (firstHalting_continue_iff N input bits).mp hfirst
          have hisSome := hread.2
          rw [result_run_continue N input bits hlen] at hisSome
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (by simpa using hisSome :
            (decodeVertex (N := N) bits).isSome = true)
          exact Or.inr ⟨v, congrArg (true :: ·) ((decodeVertex_eq_some_iff bits v).mp hv)⟩
  · rintro (hstop | ⟨v, hv⟩)
    · obtain ⟨hfirst, hflag⟩ := (firstHalting_stop_iff N input choices).mpr hstop
      exact ⟨hfirst, by simp [accept_eq, hflag]⟩
    · obtain ⟨hfirst, hflag, hresult⟩ := (firstHalting_vertex_iff N input choices v).mpr hv
      exact ⟨hfirst, by simp [accept_eq, hflag, hresult]⟩

/-- Every branch has halted after at most one marker and the fixed ID width. -/
theorem haltsWithin (N : ℕ) (input : List Bool) :
    (machine N).HaltsWithin input (N.size + 1) := by
  intro choices hlen
  cases choices with
  | nil => simp at hlen
  | cons bit bits =>
    cases bit
    · rw [run_stop]
      rfl
    · rw [run_continue]
      exact (VertexReader.halted_iff _ _ _).mpr (by simpa using hlen.ge)

/-- Live and halted branches retain only the bounded vertex reader and two flags. -/
theorem length_run_le (N : ℕ) (input choices : List Bool) :
    (encState ((machine N).run input choices)).length ≤
      4 * (Nat.log2 N.size + 1) + 4 * N.size + 11 := by
  have bound (a b : Bool) (bits : List Bool) (t : ℕ) :
      (encState ⟨a, b, (VertexReader.machine N).run bits t⟩).length ≤
        4 * (Nat.log2 N.size + 1) + 4 * N.size + 11 := by
    have h := VertexReader.length_run_le N bits t
    simp only [encState_apply, encStateFields, length_encPair, encBool_apply, List.length_singleton]
    omega
  cases choices with
  | nil => exact bound false false [] 0
  | cons bit bits =>
    cases bit
    · rw [run_stop]
      exact bound false true [] 0
    · rw [run_continue]
      exact bound true false bits bits.length

/-- State with a read answer and a selector; the state and read answer are framed. -/
abbrev encStep : (State × Option Bool × Bool) ↪ List Bool :=
  encPair encState (encPair (encOption encBool) encBool)

/-- Enter the choice phase with a dimension computed within the input budget. -/
theorem init_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    {dimension : α → ℕ} (hdim : ComputableInSpace dimension encIn encNat budget) :
    ComputableInSpace (fun a => (machine (dimension a)).init) encIn encState budget :=
  encState_mk_budget ((constZero false).mono_le fun _ => Nat.zero_le _)
    ((constZero false).mono_le fun _ => Nat.zero_le _) (VertexReader.init_budget hdim)

/-- The choice phase has no dependency on the original input. -/
theorem query_inSpace (N : ℕ) :
    ComputableInSpace (machine N).query encState encNat (fun s => (encState s).length) :=
  budget_const 0 (.refl _)

/-- Native transition computation reuses the vertex reader's certified bit update. -/
theorem next_inSpace (N : ℕ) :
    ComputableInSpace (machine N).next encStep encState (fun p => (encStep p).length) := by
  have hs := fst encState (encPair (encOption encBool) encBool)
  have hb := snd' (snd encState (encPair (encOption encBool) encBool))
  have hr := encState_reader_budget hs
  have hread := encState_reading_budget hs
  have hstep := budget_comp_linear (VertexReader.next_inSpace N)
    (budget_prod hr (budget_optionSome hb))
  exact budget_ite hread (encState_mk_budget hread (encState_stopped_budget hs) hstep)
    (encState_mk_budget hb (budget_finite Bool.not hb) hr)

/-- Native halting uses the stop flag and the existing width comparison. -/
theorem halted_inSpace (N : ℕ) :
    ComputableInSpace (machine N).halted encState encBool (fun s => (encState s).length) := by
  have hs := of_inO (ComputableInO.of_eq (encIn := encState) (encMid := encState) fun _ => rfl)
  exact budget_finite (fun (p : Bool × Bool × Bool) => p.1 || (p.2.1 && p.2.2))
    (budget_prod (encState_stopped_budget hs) (budget_prod (encState_reading_budget hs)
      (budget_comp_linear (VertexReader.halted_inSpace N) (encState_reader_budget hs))))

/-- Native acceptance checks the stop flag or the reader's range-checked result. -/
theorem accept_inSpace (N : ℕ) :
    ComputableInSpace (machine N).accept encState encBool (fun s => (encState s).length) := by
  have hs := of_inO (ComputableInO.of_eq (encIn := encState) (encMid := encState) fun _ => rfl)
  exact budget_finite (fun (p : Bool × Bool × Bool) => p.1 || (p.2.1 && p.2.2))
    (budget_prod (encState_stopped_budget hs) (budget_prod (encState_reading_budget hs)
      (budget_optionIsSome
        (budget_comp_linear VertexReader.result_inSpace (encState_reader_budget hs)))))

open NondeterministicQueryMachine in
/-- Compile one destination-boundary phase on the unchanged input. The start routine supplies the
dimension and initializes the reader. The workspace envelope covers both the dimension and
the compiler's original-input position counter. -/
theorem exists_routines {α : Type} (enc : α ↪ List Bool) (dimension budget : α → ℕ)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ budget a)
    (hdim : ∀ a, (dimension a).size + 1 ≤ budget a)
    (hstart : ComputableInSpace (fun a => (machine (dimension a)).init) enc encState budget) :
    Nonempty (Routines (machine 0) (fun a => (machine (dimension a)).init) enc budget) := by
  refine (machine 0).exists_routines (query_inSpace 0) (next_inSpace 0) (halted_inSpace 0)
    (accept_inSpace 0) _ budget hlog hstart ⟨15, fun a choices => ?_⟩
  have h := length_run_le (dimension a) (enc a) choices
  have hwidth := Nat.log2_le_self (dimension a).size
  exact h.trans (by have := hdim a; omega)

open NondeterministicQueryMachine in
/-- Successful native occurrence lists are unique for each canonical choice, with the verdict
read at the first native halt. Any accepting halted occurrence list records such a choice. -/
theorem native_firstHalting_accept_iff {α : Type} {enc : α ↪ List Bool}
    {dimension budget : α → ℕ}
    (R : Routines (machine 0) (fun a => (machine (dimension a)).init) enc budget)
    (a : α) (choices : List Bool) :
    (∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
        some (choices, final) ∧ final.Halted ∧ final.output = [true]) ↔
    choices = [false] ∨ ∃ v : Fin (dimension a), choices = true :: vertex v := by
  rw [← firstHalting_accept_iff (dimension a) (enc a) choices]
  constructor
  · rintro ⟨_, ⟨final, hreplay, hhalt, hout⟩, _⟩
    obtain ⟨hfirst, houtput⟩ := R.replay_correct a hreplay hhalt
    exact ⟨hfirst, List.cons.inj (houtput.symm.trans hout) |>.1⟩
  · rintro ⟨hfirst, haccept⟩
    obtain ⟨indices, ⟨final, hreplay, hhalt⟩, hunique⟩ :=
      (R.existsUnique_replay_iff a choices).mpr hfirst
    have hout := (R.replay_correct a hreplay hhalt).2
    exact ⟨indices, ⟨final, hreplay, hhalt, hout.trans (congrArg (fun b => [b]) haccept)⟩,
      fun other ⟨finish, hr, hh, _⟩ => hunique other ⟨finish, hr, hh⟩⟩

end Turing.DoubleCounting.NondeterministicChoice
