/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# A supplied-word ID callee with a runtime offset

`callee` retains a binary offset and the existing ID reader registers. It queries the original
word at offset plus cursor, without copying a prefix, suffix or transcript. `load` validates
runtime parameters using `VertexParameters.prepare`. Each live transition delegates to the
existing reader. The offset remains fixed even when a query is past the end of the word.

## Main results

* `runFrom_loaded`: validated runtime loads agree with the existing reader on `word.drop offset`.
* `query_loaded`, `halted_loaded_iff`: query positions and exactly `Nat.size N` attempted reads.
* `result_loaded`, `suffix_loaded`: the existing canonical codec's prefix and suffix contract.
* `length_loaded_le`: all-clock encoded state, charging the offset and reader parameters.
* `load_inSpace`: actual native parameter preparation and offset attachment. The callee
  specializes the shared `QueryMachine.withOffset` and its five native component certificates.
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

/-- The shared located state specialized to the existing ID registers. -/
abbrev Context := QueryMachine.Located State

/-- Framed binary offset followed by the existing reader-state encoding; words are unchanged. -/
abbrev encContext := QueryMachine.encLocated State encState

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
@[expose] def callee : QueryMachine Context := (machine 0).withOffset

/-- Loading succeeds exactly when existing parameter preparation succeeds. -/
theorem load_eq_some_iff (r : Request) (s : Context) :
    load r = some s ↔ s.offset = r.offset ∧ prepare r.parameters = some s.inner := by
  cases s
  simp [load, Option.map_eq_some_iff, QueryMachine.Located.mk.injEq, eq_comm, and_comm]

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
    rw [callee, QueryMachine.withOffset_runFrom, runFrom_prepare r.parameters reader hp]

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
    result (callee.runFrom w s r.parameters.dimension.size).inner =
      (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := r.parameters.dimension)
        ((w.drop r.offset).take r.parameters.dimension.size)).map Fin.val := by
  rw [runFrom_loaded r s h]
  exact result_eq_decodeVertex r.parameters.dimension (w.drop r.offset)

/-- The untouched suffix begins at offset plus measured width. This is exactly the existing
prefix decoder's suffix, including when decoding fails. No suffix is stored in the callee. -/
theorem suffix_loaded (r : Request) (s : Context) (h : load r = some s) (w : List Bool) :
    (result (callee.runFrom w s r.parameters.dimension.size).inner).map
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
  have hr := runFrom_length_le r.parameters s.inner hp (w.drop r.offset) t
  rw [runFrom_prepare r.parameters s.inner hp] at hr
  have ho := length_encNat_le_log2 (le_refl r.offset)
  rw [runFrom_loaded r s h]
  rw [QueryMachine.length_encLocated]
  dsimp only
  omega

/-- Uniform native load: parameter preparation is shared, and only a binary offset is attached. -/
theorem load_inSpace : ComputableInSpace load encRequest (encOption encContext)
    (fun r => (encRequest r).length) := by
  have hid := of_inO (ComputableInO.of_eq (encIn := encRequest) (encMid := encRequest) fun _ => rfl)
  have hp := budget_comp_linear prepare_inSpace (encRequest_parameters_budget hid)
  have ho := encRequest_offset_budget (fst encRequest encState)
  have hs := snd encRequest encState
  have hsome := budget_optionSome (QueryMachine.encLocated_mk_budget State encState ho hs)
  have hnone :=
    budget_const (Bs := fun a => (encRequest a).length) (encIn := encRequest)
      (encB := encOption encContext) none
  exact (budget_comp_linear (optionElimSnd hnone hsome) (budget_prod hid hp)).of_enc_eq
    fun r => by cases hp : prepare r.parameters <;> simp [load, hp]

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

/-- Every query-machine step of a same-input call charges both the suspended caller and the full
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
