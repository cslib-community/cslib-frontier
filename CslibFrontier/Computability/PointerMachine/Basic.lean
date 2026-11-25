/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Defs

/-!
# Pointer-machine invariants

Validity, pointer provenance, allocation freshness, determinism and the space bound.
The model itself is defined in `Defs`.

## Main results

* `Executes.valid`, `Executes.length_le`: validity and record-space bounds for halting runs.
* `Executes.unique`: uniqueness of the final state and instruction count.
* `Instr.effect_provenance`, `Instr.effect_heap_provenance`: register and heap-edge provenance.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- No records, null pointer registers and undefined data registers. -/
@[expose] def State.empty : State M L := ⟨0, fun _ => none, fun _ => M.undefined, []⟩

/-- The empty state is valid. -/
theorem State.empty_valid : (State.empty : State M L).Valid := by
  simp [State.Valid, State.empty]

/-- A register specifies a record exactly when it holds the position of that record. -/
theorem State.deref_eq_some {x : State M L} {r : Fin L.ptrRegs} {n : Record M L} :
    x.deref r = some n ↔ ∃ a, x.ptr r = some a ∧ x.heap[a]? = some n := by
  simp [State.deref, Option.bind_eq_some_iff]

/-- A record of a modified heap is an old record or the image of one. -/
theorem State.mem_heap_modify {x : State M L} {r : Fin L.ptrRegs} {g : Record M L → Record M L}
    {n : Record M L} (h : n ∈ (x.modify r g).heap) : n ∈ x.heap ∨ ∃ m ∈ x.heap, n = g m := by
  unfold State.modify at h
  split at h
  · exact .inl h
  · next a _ =>
    simp only [List.modify_eq_set_getElem?] at h
    cases hm : x.heap[a]? with
    | none => simp_all
    | some m =>
      rw [hm] at h
      rcases List.mem_or_eq_of_mem_set h with h | h
      · exact .inl h
      · exact .inr ⟨m, List.mem_of_getElem? hm, h⟩

/-- Modifying a record keeps the number of records. -/
@[simp] theorem State.length_heap_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).heap.length = x.heap.length := by
  unfold State.modify
  split <;> simp

/-- Modifying a record keeps the pointer registers. -/
@[simp] theorem State.ptr_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).ptr = x.ptr := by
  unfold State.modify
  split <;> rfl

/-- Modifying a record keeps the data registers. -/
@[simp] theorem State.data_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).data = x.data := by
  unfold State.modify
  split <;> rfl

private theorem ptr_setPtr_eq_some {x : State M L} {r' r : Fin L.ptrRegs} {p : Pointer} {a : ℕ}
    (h : (x.setPtr r' p).ptr r = some a) : p = some a ∨ x.ptr r = some a := by
  simp only [State.setPtr, Function.update_apply] at h
  split_ifs at h
  · exact .inl h
  · exact .inr h

private theorem State.Valid.setPtr {x : State M L} (hx : x.Valid) {r : Fin L.ptrRegs}
    {p : Pointer} (hp : ∀ a, p = some a → a < x.heap.length) : (x.setPtr r p).Valid :=
  ⟨fun r' a ha => (ptr_setPtr_eq_some ha).elim (hp a) (hx.1 r' a), hx.2⟩

private theorem State.Valid.modify {x : State M L} (hx : x.Valid) {r : Fin L.ptrRegs}
    {g : Record M L → Record M L}
    (hg : ∀ m ∈ x.heap, ∀ f a, (g m).ptr f = some a → a < x.heap.length) :
    (x.modify r g).Valid :=
  ⟨by simpa using hx.1, fun n hn f a ha => by
    rw [State.length_heap_modify]
    exact (State.mem_heap_modify hn).elim (hx.2 n · f a ha) fun ⟨m, hm, h⟩ =>
      hg m hm f a (h ▸ ha)⟩

/-- Instructions preserve validity. -/
theorem Instr.effect_valid {i : Instr M L} {x : State M L} (hx : x.Valid) :
    (i.effect x).Valid := by
  cases i with
  | null r => exact hx.setPtr fun _ h => nomatch h
  | movePtr r r' => exact hx.setPtr (hx.1 r')
  | loadPtr r f base =>
    simp only [Instr.effect]
    cases hn : x.deref base with
    | none => exact hx
    | some n =>
      obtain ⟨_, -, ha⟩ := State.deref_eq_some.mp hn
      exact hx.setPtr (hx.2 n (List.mem_of_getElem? ha) f)
  | loadData s f base => simp only [Instr.effect]; cases x.deref base <;> exact hx
  | storePtr f base r =>
    exact hx.modify fun m hm f' b hb => by
      simp only [Function.update_apply] at hb
      split_ifs at hb
      · exact hx.1 r b hb
      · exact hx.2 m hm f' b hb
  | storeData f base s => exact hx.modify fun m hm f' b hb => hx.2 m hm f' b hb
  | create r =>
    refine ⟨fun r' b hb => ?_, fun n hn f b hb => ?_⟩
    · simp only [Instr.effect, List.length_append, List.length_singleton] at hb ⊢
      exact (ptr_setPtr_eq_some hb).elim (fun h => Option.some.inj h ▸ Nat.lt_succ_self _)
        (fun h => Nat.lt_succ_of_lt (hx.1 r' b h))
    · simp only [Instr.effect, List.length_append, List.length_singleton] at hn ⊢
      rcases List.mem_append.mp hn with hn | hn
      · exact Nat.lt_succ_of_lt (hx.2 n hn f b hb)
      · rw [List.mem_singleton.mp hn] at hb; cases hb
  | moveData _ _ | op _ _ _ _ | goto _ | ifPtrEq _ _ _ | ifTest _ _ _ _ | halt => exact hx

/-- An instruction creates at most one record and removes none. -/
theorem Instr.effect_length {i : Instr M L} {x : State M L} :
    x.heap.length ≤ (i.effect x).heap.length ∧
      (i.effect x).heap.length ≤ x.heap.length + 1 := by
  cases i <;> simp only [Instr.effect, State.setPtr, State.setData]
  all_goals first
    | (cases x.deref ‹_› <;> simp)
    | simp

/-- A pointer in a register after an instruction was in a register before it, or in a field of
a record specified by a register, or specifies the record just created. -/
theorem Instr.effect_provenance {i : Instr M L} {x : State M L} {r : Fin L.ptrRegs} {a : ℕ}
    (ha : (i.effect x).ptr r = some a) :
    (∃ r', x.ptr r' = some a) ∨
    (∃ base n f, x.deref base = some n ∧ n.ptr f = some a) ∨
    (a = x.heap.length ∧ (i.effect x).heap.length = x.heap.length + 1) := by
  cases i with
  | null r' => exact (ptr_setPtr_eq_some ha).elim (fun h => nomatch h) (.inl ⟨r, ·⟩)
  | movePtr r' s => exact (ptr_setPtr_eq_some ha).elim (.inl ⟨s, ·⟩) (.inl ⟨r, ·⟩)
  | loadPtr r' f base =>
    simp only [Instr.effect] at ha
    cases hn : x.deref base with
    | none => exact .inl ⟨r, by simpa [hn] using ha⟩
    | some n =>
      exact (ptr_setPtr_eq_some (by simpa [hn] using ha)).elim
        (.inr ∘ .inl ∘ (⟨base, n, f, hn, ·⟩)) (.inl ⟨r, ·⟩)
  | loadData s f base =>
    simp only [Instr.effect] at ha
    cases hn : x.deref base <;> exact .inl ⟨r, by simpa [hn, State.setData] using ha⟩
  | storePtr _ _ _ | storeData _ _ _ => exact .inl ⟨r, by simpa [Instr.effect] using ha⟩
  | create r' =>
    exact (ptr_setPtr_eq_some ha).elim
      (fun h => .inr (.inr ⟨(Option.some.inj h).symm, by simp [Instr.effect]⟩)) (.inl ⟨r, ·⟩)
  | moveData _ _ | op _ _ _ _ | goto _ | ifPtrEq _ _ _ | ifTest _ _ _ _ | halt =>
    exact .inl ⟨r, ha⟩

/-- Every nonnull pointer stored in a record after an instruction was previously in a
register or a record. Allocation itself only puts null pointers in the new record. -/
theorem Instr.effect_heap_provenance {i : Instr M L} {x : State M L}
    {n : Record M L} (hn : n ∈ (i.effect x).heap) {f : Fin L.ptrFields} {a : ℕ}
    (ha : n.ptr f = some a) :
    (∃ r, x.ptr r = some a) ∨ ∃ m ∈ x.heap, ∃ g, m.ptr g = some a := by
  have old {m : Record M L} (hm : m ∈ x.heap) {g : Fin L.ptrFields}
      (hg : m.ptr g = some a) :
      (∃ r, x.ptr r = some a) ∨ ∃ m ∈ x.heap, ∃ g, m.ptr g = some a :=
    .inr ⟨m, hm, g, hg⟩
  cases i <;> simp only [Instr.effect] at hn
  case loadPtr r f base | loadData s f base =>
    cases he : x.deref base <;> simp only [he, Option.elim] at hn <;> exact old hn ha
  case storePtr g base r =>
    rcases State.mem_heap_modify hn with hm | ⟨m, hm, rfl⟩
    · exact old hm ha
    · simp only [Function.update_apply] at ha
      split_ifs at ha
      · exact .inl ⟨r, ha⟩
      · exact old hm ha
  case storeData g base s =>
    rcases State.mem_heap_modify hn with hm | ⟨m, hm, rfl⟩
    · exact old hm ha
    · exact old hm ha
  case create r =>
    rcases List.mem_append.mp hn with hm | hm
    · exact old hm ha
    · rw [List.mem_singleton.mp hm] at ha
      cases ha
  all_goals exact old hn ha

/-- In a valid state, `create` returns a pointer that no register or record held. -/
theorem Instr.create_fresh {x : State M L} (hx : x.Valid) {r : Fin L.ptrRegs} :
    ((Instr.create r).effect x).ptr r = some x.heap.length ∧
      (∀ r', x.ptr r' ≠ some x.heap.length) ∧
      ∀ n ∈ x.heap, ∀ f, n.ptr f ≠ some x.heap.length :=
  ⟨by simp [Instr.effect, State.setPtr], fun r' h => lt_irrefl _ (hx.1 r' _ h),
    fun n hn f h => lt_irrefl _ (hx.2 n hn f _ h)⟩

/-- A step executes the current instruction, which is not a `halt`. -/
theorem step_eq_some_iff {code : List (Instr M L)} {x y : State M L} :
    step code x = some y ↔
      ∃ i, code[x.pc]? = some i ∧ i ≠ .halt ∧ y = { i.effect x with pc := i.next x } := by
  unfold step
  split
  · simp_all
  · simp_all
  · next i hne hi => exact ⟨fun h => ⟨i, hi, by simpa using hne, (Option.some.inj h).symm⟩, by
      rintro ⟨j, hj, -, rfl⟩
      cases hi.symm.trans hj
      rfl⟩

/-- Program steps preserve validity. -/
theorem step_valid {code : List (Instr M L)} {x y : State M L}
    (hx : x.Valid) (h : step code x = some y) : y.Valid := by
  obtain ⟨i, -, -, rfl⟩ := step_eq_some_iff.mp h
  exact i.effect_valid hx

/-- A program step creates at most one record and removes none. -/
theorem step_length {code : List (Instr M L)} {x y : State M L} (h : step code x = some y) :
    x.heap.length ≤ y.heap.length ∧ y.heap.length ≤ x.heap.length + 1 := by
  obtain ⟨i, -, -, rfl⟩ := step_eq_some_iff.mp h
  exact i.effect_length

/-- Every state of a run from a valid state is valid. -/
theorem Runs.valid {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.Valid) : y.Valid := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih => exact step_valid ih hxy

/-- Space is at most the initial number of records plus the number of instructions executed. -/
theorem Runs.length_le {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) : y.heap.length ≤ x.heap.length + n :=
  h.apply_le_apply_add (fun x => x.heap.length) (fun _ _ hxy => (step_length hxy).2)

/-- Execution is deterministic. -/
theorem step_deterministic {code : List (Instr M L)} {x y z : State M L}
    (hy : step code x = some y) (hz : step code x = some z) : y = z :=
  Option.some.inj (hy.symm.trans hz)

/-- Successful execution preserves validity. -/
theorem Executes.valid {code : List (Instr M L)} {x y : State M L} {time : ℕ}
    (h : Executes code x y time) (hx : x.Valid) : y.Valid := by
  obtain ⟨n, hr, -, -⟩ := h
  exact hr.valid hx

/-- Space is bounded by the initial heap plus nonhalting instructions. -/
theorem Executes.length_le {code : List (Instr M L)} {x y : State M L} {time : ℕ}
    (h : Executes code x y time) : y.heap.length ≤ x.heap.length + (time - 1) := by
  obtain ⟨n, hr, -, rfl⟩ := h
  simpa using hr.length_le

/-- Runs with the same initial state and number of steps have the same final state. -/
theorem Runs.deterministic {code : List (Instr M L)} {x y z : State M L} {n : ℕ}
    (h : Runs code x y n) (h' : Runs code x z n) : y = z := by
  induction h generalizing z with
  | refl => exact h'.zero
  | tail _ _ _ _ hs ih =>
    obtain ⟨z', hr, hz⟩ := h'.succ
    cases ih hr
    exact step_deterministic hs hz

/-- Successful execution determines both the final state and the instruction count. -/
theorem Executes.unique {code : List (Instr M L)} {x y z : State M L} {t u : ℕ}
    (h : Executes code x y t) (h' : Executes code x z u) : y = z ∧ t = u := by
  obtain ⟨n, hr, hh, rfl⟩ := h
  obtain ⟨m, hr', hh', rfl⟩ := h'
  suffices y = z ∧ n = m from ⟨this.1, congrArg (· + 1) this.2⟩
  induction hr using Relation.RelatesInSteps.head_induction_on generalizing m with
  | hrefl =>
    cases m with
    | zero => exact ⟨hr'.zero, rfl⟩
    | succ m =>
      obtain ⟨w, hw, -⟩ := hr'.succ'
      simp [step, hh] at hw
  | hhead hs hr ih =>
    cases m with
    | zero =>
      cases hr'.zero
      simp [step, hh'] at hs
    | succ m =>
      obtain ⟨w, hw, hw'⟩ := hr'.succ'
      cases step_deterministic hs hw
      obtain ⟨rfl, rfl⟩ := ih m hw'
      exact ⟨rfl, rfl⟩

end Cslib.PointerMachine
