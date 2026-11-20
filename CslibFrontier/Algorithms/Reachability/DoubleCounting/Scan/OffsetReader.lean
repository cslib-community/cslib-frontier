/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# A supplied-word ID callee with a runtime offset

`callee` retains a binary offset and the existing ID reader registers. It queries the original
word at offset plus cursor, without copying a prefix, suffix or transcript. `load` validates
runtime parameters using `VertexParameters.prepare`. Each live transition delegates to the
existing reader. The offset remains fixed even when a query is past the end of the word.

## Main results

* `runFrom_eq`: exact agreement with the existing reader on `word.drop offset`.
* `query_loaded`, `halted_loaded_iff`: query positions and exactly `Nat.size N` attempted reads.
* `result_loaded`, `suffix_loaded`: the existing canonical codec's prefix and suffix contract.
* `length_loaded_le`: all-clock encoded state, charging the offset and reader parameters.
* `load_inSpace` and the five component certificates: actual native scalar operations, uniform
  in the offset, dimension and claimed width.
* `call_loaded`: the existing same-input call interface returns this callee's final state.

This is original deterministic supplied-word infrastructure for
[#6747](https://github.com/cslib-community/cslib-frontier/issues/6747), checked through ordinary
imports in `CslibFrontierTests.DoubleCountingOffsetReader`. Native component certificates do not
by themselves certify uniform whole-input dispatch into a caller. The existing call compiler
must also charge its suspended caller and original-input position; `call_length_le` charges the
former explicitly. Genuine nondeterministic choice production and full first-halting scan
lowering remain open. The canonical ID encoding is unchanged.
-/

public section
namespace Turing.DoubleCounting.OffsetReader
open MultiTapeTM ComputableInSpace VertexReader VertexParameters

/-- Runtime call arguments, with an absolute binary position in the original supplied word. -/
structure Request where
  /-- Absolute position of the first ID bit. -/
  offset : ℕ
  /-- Dimension and claimed width, checked by the existing preparation routine. -/
  parameters : Parameters

/-- Framed binary offset followed by the existing parameter encoding. -/
enc_structure encRequest : Request where offset : encNat, parameters : encParameters

/-- Retained call context; it contains no part of the supplied word. -/
structure Context where
  /-- Unchanging absolute position of the first ID bit. -/
  offset : ℕ
  /-- Existing scalar ID registers. -/
  reader : State

/-- Framed binary offset followed by the existing reader-state encoding. -/
enc_structure encContext : Context where offset : encNat, reader : encState

/-- Runtime arguments occupy logarithmic binary space, even for an invalid claimed width. -/
theorem length_encRequest_le (r : Request) :
    (encRequest r).length ≤ 2 * (Nat.log2 r.offset + 1) +
      3 * (Nat.log2 (r.parameters.dimension + r.parameters.width) + 1) + 2 := by
  have ho := length_encNat_le_log2 (le_refl r.offset)
  have hp := length_encParameters_le r.parameters
  simp only [encRequest_apply, encRequestFields, length_encPair]
  omega

/-- Validate parameters and attach the offset; invalid widths reject before calling. -/
@[expose] def load (r : Request) : Option Context :=
  (prepare r.parameters).map (fun s => ⟨r.offset, s⟩)

/-- An offset callee, entered using `runFrom` or a same-input state-returning call.
The default initial state is only a zero-dimensional reader at offset zero. -/
@[expose] def callee : QueryMachine Context where
  init := ⟨0, (machine 0).init⟩
  query s := s.offset + (machine 0).query s.reader
  next p := ⟨p.1.offset, (machine 0).next (p.1.reader, p.2)⟩
  emit _ := []
  halted s := (machine 0).halted s.reader
  finish s := (machine 0).finish s.reader

/-- Loading succeeds exactly when existing parameter preparation succeeds. -/
theorem load_eq_some_iff (r : Request) (s : Context) :
    load r = some s ↔ s.offset = r.offset ∧ prepare r.parameters = some s.reader := by
  cases s
  simp [load, Option.map_eq_some_iff, Context.mk.injEq, eq_comm, and_comm]

/-- Shifting query indices is exactly reading a dropped view of the same original word. -/
theorem runFrom_eq (w : List Bool) (offset : ℕ) (s : State) (t : ℕ) :
    callee.runFrom w ⟨offset, s⟩ t =
      ⟨offset, (machine 0).runFrom (w.drop offset) s t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, ih, QueryMachine.runFrom_succ]
    simp only [QueryMachine.step, QueryMachine.read, callee, List.getElem?_drop]
    split <;> simp_all

/-- A valid runtime load reuses the fixed-dimension reader verbatim. -/
theorem runFrom_loaded (r : Request) (s : Context) (h : load r = some s)
    (w : List Bool) (t : ℕ) :
    callee.runFrom w s t =
      ⟨r.offset, (machine r.parameters.dimension).run (w.drop r.offset) t⟩ := by
  obtain ⟨ho, hp⟩ := (load_eq_some_iff r s).mp h
  cases s with
  | mk offset reader =>
    dsimp only at ho hp
    subst offset
    rw [runFrom_eq, runFrom_prepare r.parameters reader hp]

/-- Every live query uses the absolute offset plus the current cursor. -/
theorem query_loaded (r : Request) (s : Context) (h : load r = some s)
    (w : List Bool) (t : ℕ) (ht : t < r.parameters.dimension.size) :
    callee.query (callee.runFrom w s t) = r.offset + t := by
  rw [runFrom_loaded r s h]
  exact congrArg (r.offset + ·) (query_run r.parameters.dimension (w.drop r.offset) t ht)

/-- The callee attempts exactly the measured width, including on truncated input. -/
theorem halted_loaded_iff (r : Request) (s : Context) (h : load r = some s)
    (w : List Bool) (t : ℕ) :
    callee.halted (callee.runFrom w s t) = true ↔ r.parameters.dimension.size ≤ t := by
  rw [runFrom_loaded r s h]
  exact halted_iff r.parameters.dimension (w.drop r.offset) t

/-- Final optional rank agrees with the existing canonical prefix decoder; invalid ranks and
missing bits remain rejection, without wrapping a rank into `Fin`. -/
theorem result_loaded (r : Request) (s : Context) (h : load r = some s) (w : List Bool) :
    result (callee.runFrom w s r.parameters.dimension.size).reader =
      (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := r.parameters.dimension)
        ((w.drop r.offset).take r.parameters.dimension.size)).map Fin.val := by
  rw [runFrom_loaded r s h]
  exact result_eq_decodeVertex r.parameters.dimension (w.drop r.offset)

/-- The untouched suffix begins at offset plus measured width. This is exactly the existing
prefix decoder's suffix, including when decoding fails. No suffix is stored in the callee. -/
theorem suffix_loaded (r : Request) (s : Context) (h : load r = some s) (w : List Bool) :
    (result (callee.runFrom w s r.parameters.dimension.size).reader).map
      (fun n => (n, w.drop (r.offset + r.parameters.dimension.size))) =
    (Cslib.DoubleCounting.Scan.Binary.readVertex (N := r.parameters.dimension)
      (w.drop r.offset)).map (fun p => (p.1.val, p.2)) := by
  rw [result_loaded r s h]
  simp only [Cslib.DoubleCounting.Scan.Binary.readVertex, Option.map_map, List.drop_drop]
  rfl

/-- All clocks charge the binary offset and retained parameters, even after halting. -/
theorem length_loaded_le (r : Request) (s : Context) (h : load r = some s)
    (w : List Bool) (t : ℕ) :
    (encContext (callee.runFrom w s t)).length ≤
      2 * (Nat.log2 r.offset + 1) + 8 * (Nat.log2 r.parameters.dimension + 1) + 10 := by
  obtain ⟨_, hp⟩ := (load_eq_some_iff r s).mp h
  have hr := runFrom_length_le r.parameters s.reader hp (w.drop r.offset) t
  rw [runFrom_prepare r.parameters s.reader hp] at hr
  have ho := length_encNat_le_log2 (le_refl r.offset)
  rw [runFrom_loaded r s h]
  simp only [encContext_apply, encContextFields, length_encPair]
  omega

/-- Uniform native load: parameter preparation is shared, and only a binary offset is attached. -/
theorem load_inSpace : ComputableInSpace load encRequest (encOption encContext)
    (fun r => (encRequest r).length) := by
  have hid := of_inO (ComputableInO.of_eq (encIn := encRequest) (encMid := encRequest) fun _ => rfl)
  have hp := budget_comp_linear prepare_inSpace (encRequest_parameters_budget hid)
  have ho := encRequest_offset_budget (fst encRequest encState)
  have hs := snd encRequest encState
  have hsome := budget_optionSome (encContext_mk_budget ho hs)
  have hnone := budget_const (encIn := encRequest) (encB := encOption encContext) none (.refl _)
  exact (budget_comp_linear (optionElimSnd hnone hsome) (budget_prod hid hp)).of_enc_eq
    fun r => by cases hp : prepare r.parameters <;> simp [load, hp]

/-- Actual native offset addition for querying the original input. -/
theorem query_inSpace : ComputableInSpace callee.query encContext encNat
    (fun s => (encContext s).length) := by
  have hid := of_inO (ComputableInO.of_eq (encIn := encContext) (encMid := encContext) fun _ => rfl)
  exact budget_natAdd (encContext_offset_budget hid)
    (budget_comp_linear (VertexReader.query_inSpace 0) (encContext_reader_budget hid))

/-- Actual native reader transition, retaining the binary offset. -/
theorem next_inSpace : ComputableInSpace callee.next (QueryMachine.encStateRead encContext)
    encContext (fun p => (QueryMachine.encStateRead encContext p).length) := by
  have hc := fst encContext (encOption encBool)
  have hb := snd encContext (encOption encBool)
  have hr := budget_comp_linear (VertexReader.next_inSpace 0)
    (budget_prod (encContext_reader_budget hc) hb)
  exact encContext_mk_budget (encContext_offset_budget hc) hr

/-- The native halt check reuses the reader's width comparison. -/
theorem halted_inSpace : ComputableInSpace callee.halted encContext encBool
    (fun s => (encContext s).length) := by
  change ComputableInSpace (fun s : Context => (machine 0).halted s.reader) _ _ _
  exact budget_comp_linear (VertexReader.halted_inSpace 0)
    (encContext_reader_budget (of_inO (ComputableInO.of_eq fun _ => rfl)))

/-- No callee output stream is retained. -/
theorem emit_inSpace : ComputableInSpace callee.emit (QueryMachine.encStateRead encContext)
    encBits (fun p => (QueryMachine.encStateRead encContext p).length) := budget_const [] (.refl _)

/-- Native finalization reuses the reader's range/truncation check. -/
theorem finish_inSpace : ComputableInSpace callee.finish encContext encBits
    (fun s => (encContext s).length) := by
  change ComputableInSpace (fun s : Context => (machine 0).finish s.reader) _ _ _
  exact budget_comp_linear (VertexReader.finish_inSpace 0)
    (encContext_reader_budget (of_inO (ComputableInO.of_eq fun _ => rfl)))

/-- A same-input caller resumes with the exact final offset-reader state, after one entry step,
the measured number of reads, and one return step. -/
theorem call_loaded {σ : Type} (M : QueryMachine σ) (request : σ → Option Context)
    (resume : σ → Context → σ) (r : Request) (s : Context) (h : load r = some s)
    (caller : σ) (w : List Bool) (hlive : M.halted caller = false)
    (hrequest : request caller = some s) :
    (M.withCalls callee request resume).runFrom w (.inl caller)
        (r.parameters.dimension.size + 2) =
      .inl (resume caller ⟨r.offset,
        (machine r.parameters.dimension).run (w.drop r.offset) r.parameters.dimension.size⟩) := by
  rw [← runFrom_loaded r s h]
  apply QueryMachine.withCalls_runFrom_call M callee request resume w caller s _ hlive hrequest
  · intro i hi
    cases hh : callee.halted (callee.runFrom w s i)
    · rfl
    · exact False.elim (by have := (halted_loaded_iff r s h w i).mp hh; omega)
  · exact (halted_loaded_iff r s h w _).mpr le_rfl

/-- Every physical clock of a same-input call charges both the suspended caller and the full
callee context. The reader contribution is logarithmic in offset and dimension. -/
theorem call_length_le {σ : Type} (M : QueryMachine σ) (request : σ → Option Context)
    (resume : σ → Context → σ) (r : Request) (s : Context) (h : load r = some s)
    (caller : σ) (w : List Bool) (encS : σ ↪ List Bool) (C : ℕ)
    (hlive : M.halted caller = false) (hrequest : request caller = some s)
    (hcaller : (encS caller).length ≤ C)
    (hresume : (encS (resume caller (callee.runFrom w s r.parameters.dimension.size))).length ≤ C)
    (t : ℕ) (ht : t ≤ r.parameters.dimension.size + 2) :
    (QueryMachine.encWithCalls encS encContext
      ((M.withCalls callee request resume).runFrom w (.inl caller) t)).length ≤
      2 * C + (2 * (Nat.log2 r.offset + 1) +
        8 * (Nat.log2 r.parameters.dimension + 1) + 10) + 2 := by
  apply QueryMachine.withCalls_runFrom_call_encoding_le M callee request resume w encS encContext
    hlive hrequest (fun i hi => ?_) ((halted_loaded_iff r s h w _).mpr le_rfl)
    hcaller hresume (fun i _ => length_loaded_le r s h w i) t ht
  cases hh : callee.halted (callee.runFrom w s i)
  · rfl
  · exact False.elim (by have := (halted_loaded_iff r s h w i).mp hh; omega)

end Turing.DoubleCounting.OffsetReader
