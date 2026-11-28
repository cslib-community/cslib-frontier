/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of same-input predecessor queries)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor.Runtime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-! # Same-input scalar predecessor loop, with a one-read callback callee -/

set_option linter.privateModule false

namespace Turing.DoubleCounting.Predecessor.Tests
open MultiTapeTM ComputableInSpace Cslib.DoubleCounting

private structure ReadState where
  index : ℕ
  reply : Option Bool
  finished : Bool

private enc_structure encRead : ReadState where
  index : encNat, reply : (encOption encBool), finished : encBool

private def reader : QueryMachine ReadState where
  init := ⟨0, none, false⟩
  query q := q.index
  next p := ⟨p.1.index, p.2, true⟩
  emit _ := []
  halted q := q.finished
  finish _ := []

-- The two request phases read different locations on the same original input.
private def start (q : State) : ReadState :=
  ⟨2 * q.cursor + if q.memberPhase then 1 else 0, none, false⟩
private def answer (q : ReadState) : Option Bool := q.reply
private def ctx : Context := ⟨3, 0, 2, 5, ⟨2, 4⟩⟩
private def loop := machine ctx reader start answer

-- Five calls (15 query-machine clocks) yield one qualifying predecessor.
example : loop.runFrom [true, true, false, false, true, false] (.inl (initial ctx)) 15 =
    .inl ⟨ctx, 3, 1, false, false⟩ := by rfl
-- Three qualifying predecessors are retained as count 3; the outer controller can detect a tie.
example : loop.runFrom [true, true, true, true, true, true] (.inl (initial ctx)) 18 =
    .inl ⟨ctx, 3, 3, false, false⟩ := by rfl
-- A truncated membership answer rejects at cursor 1, preserving the partial count and phase.
example : loop.runFrom [true, true, true] (.inl (initial ctx)) 12 =
    .inl ⟨ctx, 1, 1, true, true⟩ := by rfl
-- Call entry really retains the complete caller, including radius and expected tally.
example : loop.runFrom [true] (.inl (initial ctx)) 1 =
    .inr (initial ctx, start (initial ctx)) := by rfl

private theorem start_space : ComputableInSpace start encState encRead
    (fun q => (encState q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encState)).inO_one
  have two :=
    budget_const (Bs := fun a => (encState a).length) (encIn := encState) (encB := encNat) 2
  have one :=
    budget_const (Bs := fun a => (encState a).length) (encIn := encState) (encB := encNat) 1
  have zero :=
    budget_const (Bs := fun a => (encState a).length) (encIn := encState) (encB := encNat) 0
  exact (encRead_mk_budget
    (budget_natAdd (budget_natMul two (encState_cursor_budget hid))
      (budget_ite (encState_memberPhase_budget hid) one zero))
    (budget_const none) (budget_const false)).of_enc_eq fun _ => rfl

private theorem reader_next_space : ComputableInSpace reader.next
    (QueryMachine.encStateRead encRead) encRead
    (fun p => (QueryMachine.encStateRead encRead p).length) := by
  exact (encRead_mk_budget (encRead_index_budget (fst encRead (encOption encBool)))
    (snd encRead (encOption encBool)) (budget_const true)).of_enc_eq fun _ => rfl

-- A native scalar certificate is instantiated for a real bit-reading callee and its routing,
-- not by assuming the whole predecessor loop efficient.
example : ComputableInSpace loop.next (QueryMachine.encStateRead (encMachineState encRead))
    (encMachineState encRead)
    (fun p => (QueryMachine.encStateRead (encMachineState encRead) p).length) := by
  apply machine_next_inSpace encRead ctx reader start answer reader_next_space
  · exact encRead_finished_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one)
  · exact start_space
  · exact encRead_reply_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one)

example : ComputableInSpace loop.query (encMachineState encRead) encNat
    (fun p => (encMachineState encRead p).length) := by
  exact machine_query_inSpace encRead ctx reader start answer
    (encRead_index_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one)) start_space

-- Every clock of this actual read, including the suspended and returned states, is charged.
example (i : ℕ) (hi : i ≤ 3) :
    (encMachineState encRead (loop.runFrom [true] (.inl (initial ctx)) i)).length ≤
      4 * (encContext ctx).length + 8 * (Nat.log2 3 + 1) + 7 + 16 := by
  apply runFrom_call_encoding_le encRead ctx reader start answer [true] (initial ctx)
    (Returns.bounded (Returns.initial (ctx := ctx) (N := reader)
      (start := start) (answer := answer) (w := [true]))) (by rfl) 1 7
  · intro j hj
    have : j = 0 := by omega
    subst j
    rfl
  · rfl
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> decide +kernel
  · exact hi

private theorem reader_time (w : List Bool) (p : State) (T : ℕ)
    (hpre : ∀ i < T, reader.halted (reader.runFrom w (start p) i) = false)
    (hhalt : reader.halted (reader.runFrom w (start p) T) = true) : T = 1 := by
  cases T with
  | zero => change false = true at hhalt; contradiction
  | succ t =>
    cases t with
    | zero => rfl
    | succ t =>
      have bad := hpre 1 (by omega)
      change true = false at bad
      contradiction

private theorem reader_reply (w : List Bool) (p : State) (T : ℕ)
    (hpre : ∀ i < T, reader.halted (reader.runFrom w (start p) i) = false)
    (hhalt : reader.halted (reader.runFrom w (start p) T) = true) :
    answer (reader.runFrom w (start p) T) =
      if p.memberPhase then w[2 * p.cursor + 1]? else w[2 * p.cursor]? := by
  have hT := reader_time w p T hpre hhalt
  subst T
  cases hp : p.memberPhase <;>
    simp [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero, QueryMachine.step,
      QueryMachine.read, reader, start, answer, hp]

-- A finite trace of actual callee returns agrees with the original Option-valued fold,
-- including rejected input reads. This does not assert trace existence for arbitrary callees.
private theorem trace_result (w : List Bool) (q : State) (h : Returns ctx reader start answer w q)
    (hstop : halted q = true) :
    (if q.rejected then none else some q.count) =
      countPredecessors (fun u _ : Fin 3 => w[2 * u.val]?)
        (fun u => w[2 * u.val + 1]?) 2 := by
  apply result_of_returns (n := 3) _ _ (2 : Fin 3) rfl h hstop
  intro p _ _ T hpre hhalt
  exact reader_reply w p T hpre hhalt

-- The callee's one-step first halt supplies the generic termination premise. The native
-- query loop therefore halts with the original fold's result on every input, even truncated.
example (w : List Bool) : ∃ T q,
    loop.runFrom w (.inl (initial ctx)) T = .inl q ∧ halted q = true ∧
      (if q.rejected then none else some q.count) =
        countPredecessors (fun u _ : Fin 3 => w[2 * u.val]?)
          (fun u => w[2 * u.val + 1]?) 2 := by
  obtain ⟨q, hq, hstop⟩ := exists_stopped_returns ctx reader start answer w (by
    intro p _ _ _
    refine ⟨1, ?_, rfl⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl)
  obtain ⟨T, hT⟩ := hq.exists_run
  exact ⟨T, q, hT, hstop, trace_result w q hq hstop⟩

-- Result output is added once at halt; rejection, zero and tied counts remain distinct.
example : (computingMachine ctx reader start answer).output
    [false, false, false, false, false, false] 9 = encCountResult (some 0) := by rfl
example : (computingMachine ctx reader start answer).output
    [true, true, false, false, true, false] 15 = encCountResult (some 1) := by rfl
example : (computingMachine ctx reader start answer).output
    [true, true, true, true, true, true] 18 = encCountResult (some 3) := by rfl
example : (computingMachine ctx reader start answer).output
    [true, true, true] 12 = encCountResult none := by rfl

private theorem reader_state_bound (w : List Bool) (p : State) (hp : p.context.size = 3)
    (hlive : halted p = false) (T : ℕ)
    (hpre : ∀ i < T, reader.halted (reader.runFrom w (start p) i) = false)
    (hhalt : reader.halted (reader.runFrom w (start p) T) = true)
    (i : ℕ) (hi : i ≤ T) : (encRead (reader.runFrom w (start p) i)).length ≤ 13 := by
  have hT := reader_time w p T hpre hhalt
  subst T
  have hcur : p.cursor < 3 := by
    have h := (Bool.or_eq_false_iff.mp hlive).2
    simpa [hp] using h
  have hindex : 2 * p.cursor + (if p.memberPhase then 1 else 0) ≤ 5 := by
    cases p.memberPhase <;> simp <;> omega
  have hbits := length_encNat_le_log2 hindex
  have hb : (encNat (2 * p.cursor + (if p.memberPhase then 1 else 0))).length ≤ 3 := by
    simpa using hbits
  have casesI : i = 0 ∨ i = 1 := by omega
  rcases casesI with rfl | rfl
  · simp only [QueryMachine.runFrom_zero, start, encRead_apply, encReadFields, length_encPair,
      encOption_none, encBool_apply, List.length_singleton, List.length_nil]
    omega
  · change (encRead ⟨(start p).index, w[(start p).index]?, true⟩).length ≤ 13
    cases hw : w[(start p).index]? with
    | none =>
      simp only [start, encRead_apply, encReadFields, length_encPair, encOption_none,
        encBool_apply, List.length_singleton, List.length_nil]
      omega
    | some b =>
      simp only [start, encRead_apply, encReadFields, length_encPair, encOption_some,
        encBool_apply, List.length_cons, List.length_nil]
      omega

-- This is an actual native TM certificate from QueryMachine compilation, not just a semantic
-- query-loop completion statement. Its time function is independent of the displayed space.
public theorem reader_native_certificate : ∃ time c, ComputableInTimeAndSpace
    (fun w : List Bool => countPredecessors (fun u _ : Fin 3 => w[2 * u.val]?)
      (fun u => w[2 * u.val + 1]?) 2) encBits encCountResult time
    (fun w => c * (Nat.log2 w.length + 1 +
      4 * (encContext ⟨3, 0, 2, 5, ⟨2, 4⟩⟩).length +
      8 * (Nat.log2 3 + 1) + 13 + 16)) := by
  refine compute_of_callees encBits encRead ctx reader start answer _ _ (2 : Fin 3) rfl
    (encRead_index_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    reader_next_space
    (encRead_finished_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    start_space
    (encRead_reply_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    (fun _ => 13) _ ?_ ?_ ?_ ?_ ?_
  · intro w p _ _ _
    refine ⟨1, ?_, rfl⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  · intro w p hp _ hlive T hpre hhalt i hi
    exact reader_state_bound w p (by rw [hp]; rfl) hlive T hpre hhalt i hi
  · intro w p _ _ T hpre hhalt
    exact reader_reply w p T hpre hhalt
  · intro w
    change Nat.log2 w.length + 1 ≤ _
    omega
  · intro w
    change 4 * (encContext ctx).length + 8 * (Nat.log2 3 + 1) + 13 + 16 ≤
      Nat.log2 w.length + 1 + 4 * (encContext ctx).length + 8 * (Nat.log2 3 + 1) + 13 + 16
    omega

-- The native initializer accepts the context at runtime and copies no payload into its result.
example : ComputableInSpace Runtime.load Runtime.encInput (QueryMachine.encLocated State encState)
    (fun x => (encContext x.context).length + 1) := Runtime.load_inSpace

-- The same executor handles different runtime contexts; no machine is selected by the header.
example : ((Runtime.executor reader start answer).runFrom
    (Runtime.encInput ⟨ctx, [true, true, false, false, true, false]⟩)
    (Runtime.entry ReadState ⟨ctx, [true, true, false, false, true, false]⟩) 15).inner =
      .inl ⟨ctx, 3, 1, false, false⟩ := by
  rw [Runtime.executor_runFrom]
  rfl

example : ((Runtime.executor reader start answer).runFrom
    (Runtime.encInput ⟨ctx, [true, true, true, true, true, true]⟩)
    (Runtime.entry ReadState ⟨ctx, [true, true, true, true, true, true]⟩) 18).inner =
      .inl ⟨ctx, 3, 3, false, false⟩ := by
  rw [Runtime.executor_runFrom]
  rfl

example : ((Runtime.executor reader start answer).runFrom
    (Runtime.encInput ⟨ctx, [true, true, true]⟩)
    (Runtime.entry ReadState ⟨ctx, [true, true, true]⟩) 12).inner =
      .inl ⟨ctx, 1, 1, true, true⟩ := by
  rw [Runtime.executor_runFrom]
  rfl

example : ((Runtime.executor reader start answer).runFrom
    (Runtime.encInput ⟨⟨1, 0, 0, 0, ⟨0, 0⟩⟩, [false]⟩)
    (Runtime.entry ReadState ⟨⟨1, 0, 0, 0, ⟨0, 0⟩⟩, [false]⟩) 3).inner =
      .inl ⟨⟨1, 0, 0, 0, ⟨0, 0⟩⟩, 1, 0, false, false⟩ := by
  rw [Runtime.executor_runFrom]
  rfl

-- Native dispatch preserves the original callee transition and charges its retained offset.
example : ComputableInSpace reader.withOffset.next
    (QueryMachine.encStateRead (QueryMachine.encLocated ReadState encRead))
    (QueryMachine.encLocated ReadState encRead)
    (fun p => (QueryMachine.encStateRead (QueryMachine.encLocated ReadState encRead) p).length) :=
  QueryMachine.withOffset_next_inSpace reader encRead reader_next_space

-- Complete native-callee resource contracts compose with offset transport at every clock,
-- including suspended calls. This remains a query trace certificate, not a native executor.
example (w : List Bool) (q : State) (hq : Returns ctx reader start answer w q) :
    ∃ T, ((Runtime.executor reader start answer).runFrom (Runtime.encInput ⟨ctx, w⟩)
      (Runtime.entry ReadState ⟨ctx, w⟩) T).inner = .inl q ∧
      ∀ i ≤ T, (QueryMachine.encLocated _ (encMachineState encRead)
      ((Runtime.executor reader start answer).runFrom (Runtime.encInput ⟨ctx, w⟩)
        (Runtime.entry ReadState ⟨ctx, w⟩) i)).length ≤
      2 * (Nat.log2 (2 * (encContext ctx).length + 1) + 1) + 1 +
        (4 * (encContext ctx).length + 8 * (Nat.log2 ctx.size + 1) + 13 + 16) := by
  obtain ⟨T, hr, hb⟩ := hq.exists_run_encoding_le encRead 13
    (fun p hp _ hlive T hpre hhalt i hi =>
      reader_state_bound w p (by rw [hp]; rfl) hlive T hpre hhalt i hi)
  have hd := QueryMachine.withOffset_runFrom_encoding_le
    (computingMachine ⟨0, 0, 0, 0, ⟨0, 0⟩⟩ reader start answer) (encMachineState encRead)
    (Runtime.encInput ⟨ctx, w⟩) (Runtime.load ⟨ctx, w⟩).offset (.inl (initial ctx)) _ T
    (by
      intro i hi
      rw [Runtime.drop_payload]
      exact hb i hi)
  refine ⟨T, ?_, fun i hi => ?_⟩
  · rw [Runtime.executor_runFrom]
    exact hr
  · have hn := length_encNat_le_log2
      (Nat.le_refl (2 * (encContext ctx).length + 1))
    exact (hd i hi).trans (by simpa only [Runtime.load] using
      (show 2 * (encNat (2 * (encContext ctx).length + 1)).length + 1 +
          (4 * (encContext ctx).length + 8 * (Nat.log2 ctx.size + 1) + 13 + 16) ≤ _ from
        by omega))

private abbrev FramedReaderInput := {x : Runtime.Input // x.context.size = 3}

private def framedReaderCount (x : FramedReaderInput) : Option ℕ :=
  countPredecessors (fun u _ : Fin 3 => x.val.payload[2 * u.val]?)
    (fun u => x.val.payload[2 * u.val + 1]?) 2

private def encFramedReaderInput : FramedReaderInput ↪ List Bool :=
  (Function.Embedding.subtype _).trans Runtime.encInput

-- The same native witness consumes runtime contexts and keeps a truncated payload rejecting.
example : ∃ time c, ComputableInTimeAndSpace framedReaderCount encFramedReaderInput
    encCountResult time (fun x => c * (Nat.log2 (encFramedReaderInput x).length + 1 +
      (2 * (encNat (Runtime.load x.val).offset).length + 1 +
        (4 * (encContext x.val.context).length + 8 * (Nat.log2 x.val.context.size + 1) + 13 +
          16)))) := by
  refine Runtime.compute_of_callees encFramedReaderInput Subtype.val (fun _ => rfl)
    encRead reader start answer _ _ (fun _ => (2 : Fin 3)) Subtype.property
    (encRead_index_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    reader_next_space
    (encRead_finished_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    start_space (encRead_reply_budget (of_inO (ComputableInDegree.id' (enc := encRead)).inO_one))
    (fun _ => 13) _ ?_ ?_ ?_ (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_left _ _)
  · intro x p _ _ _
    refine ⟨1, ?_, rfl⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  · intro x p hp _ hlive T hpre hhalt i hi
    exact reader_state_bound x.val.payload p (hp ▸ x.property) hlive T hpre hhalt i hi
  · intro x p _ _ T hpre hhalt
    exact reader_reply x.val.payload p T hpre hhalt

example :
    let x : Runtime.Input := ⟨⟨3, 1, 2, 3, ⟨1, 2⟩⟩, [true, true, true]⟩
    (Runtime.executor reader start answer).finish ((Runtime.executor reader start answer).runFrom
      (Runtime.encInput x) (Runtime.entry ReadState x) 12) = encCountResult none := by
  dsimp only
  rw [Runtime.executor_runFrom]
  rfl

end Turing.DoubleCounting.Predecessor.Tests
