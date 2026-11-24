/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PointerMachine.SmallMSF
import Mathlib.Tactic.IntervalCases

/-!
# Binding a new input to a stored MSF comparison tree

The binder walks the reusable slot list and the input's edge list in the same topology order.
It copies each key and saves a pointer to the input edge in slot field 4. The comparison tree,
its output lists, and both list links are preserved. Addresses in the two lists need not be
contiguous. A caller can reuse the stored tree for every member of one topology group.

See [Pettie and Ramachandran, §6][PettieRamachandran2002].
-/

public section

namespace Cslib.PointerMachine.ComparisonTree.Binding

open Cslib.Query

variable {W E O : Type} [Inhabited W] [LinearOrder W]

/-- Addresses used when binding a single local topology coordinate. -/
structure Item (W : Type) where
  /-- Generic edge record referenced by the shared comparison tree. -/
  slot : ℕ
  /-- Edge record of the input instance. -/
  source : ℕ
  /-- Weight at the input address. -/
  key : W

/-- The slot and input lists use field 0 for their respective next pointers. -/
inductive Aligned (H : List (Record (model W) layout)) :
    Pointer → Pointer → List (Item W) → Prop where
  | nil : Aligned H none none []
  | cons {b : Item W} {r s rest} (slot : H[b.slot]? = some r) (src : H[b.source]? = some s)
      (weight : s.data 0 = b.key) (tail : Aligned H (r.ptr 0) (s.ptr 0) rest) :
      Aligned H (some b.slot) (some b.source) (b :: rest)

/-- Entry at instruction 12. Register 0 contains the root, 1 and 2 contain the aligned
heads, and 3 is null. On finishing the binder dispatches to the original interpreter at 0. -/
@[expose] def program (W : Type) [Inhabited W] [LinearOrder W] : List (Instr (model W) layout) :=
  (code W).take 11 ++ [.goto 20, .ifPtrEq 1 3 19, .loadData 0 0 2, .storeData 0 1 0,
    .storePtr 4 1 2, .loadPtr 1 0 1, .loadPtr 2 0 2, .goto 12, .goto 0,
    .null 3, .ifPtrEq 0 3 27, .loadPtr 1 0 0, .loadPtr 1 4 1, .storePtr 4 1 1, .loadPtr 0 1 0,
    .goto 21, .halt]

private def copyKey (b : Item W) (r : Record (model W) layout) : Record (model W) layout :=
  { r with data := Function.update r.data 0 b.key }

private def linkInput (b : Item W) (r : Record (model W) layout) : Record (model W) layout :=
  { r with ptr := Function.update r.ptr 4 (some b.source) }

private def write (H : List (Record (model W) layout)) (b : Item W) :
    List (Record (model W) layout) :=
  (H.modify b.slot (copyKey b)).modify b.slot (linkInput b)

private theorem write_other (H : List (Record (model W) layout)) (b : Item W) {j : ℕ}
    (ne : b.slot ≠ j) :
    (write H b)[j]? = H[j]? := by simp [write, List.getElem?_modify_ne, ne]

private theorem write_self {H : List (Record (model W) layout)} {b : Item W}
    {r : Record (model W) layout} (hr : H[b.slot]? = some r) :
    (write H b)[b.slot]? = some (linkInput b (copyKey b r)) := by simp [write, hr]

/-- A heap modification preserves the address and the four tree fields of every record. -/
def Preserves (H K : List (Record (model W) layout)) : Prop :=
  ∀ (i : ℕ) (r : Record (model W) layout), H[i]? = some r →
    ∃ s : Record (model W) layout, K[i]? = some s ∧ ∀ f : Fin 5, f ≠ 4 → s.ptr f = r.ptr f

private theorem Preserves.refl (H : List (Record (model W) layout)) : Preserves H H :=
  fun _ r read => ⟨r, read, fun _ _ => rfl⟩

private theorem Preserves.trans {H J K : List (Record (model W) layout)} (h : Preserves H J)
    (k : Preserves J K) : Preserves H K := by
  intro i r read
  obtain ⟨s, hs, same⟩ := h i r read
  obtain ⟨t, ht, same'⟩ := k i s hs
  exact ⟨t, ht, fun f hf => (same' f hf).trans (same f hf)⟩

private theorem write_preserves (H : List (Record (model W) layout)) (b : Item W) :
    Preserves H (write H b) := by
  intro i r read
  by_cases eq : b.slot = i
  · subst i
    exact ⟨_, write_self read, fun f hf => by simp [linkInput, copyKey, hf]⟩
  · exact ⟨r, (write_other H b eq).trans read, fun _ _ => rfl⟩

private theorem Aligned.transport {H K : List (Record (model W) layout)} {a b : Pointer}
    {xs : List (Item W)} (chain : Aligned H a b xs) (frame : Preserves H K)
    (sources : ∀ i ∈ xs, K[i.source]? = H[i.source]?) : Aligned K a b xs := by
  induction chain with
  | nil => exact .nil
  | @cons i r s xs hr hs hw tail ih =>
    obtain ⟨r', hr', eq⟩ := frame i.slot r hr
    refine Aligned.cons hr' ((sources i List.mem_cons_self).trans hs) hw ?_
    rw [eq 0 (by decide)]
    exact ih (fun j hj => sources j (List.mem_cons_of_mem _ hj))

private def advance (x : State (model W) layout) : ℕ → Option (State (model W) layout)
  | 0 => some x
  | n + 1 => (advance x n).bind (step (program W))

private theorem runs_advance {x y : State (model W) layout} {n : ℕ} (h : advance x n = some y) :
    Runs (program W) x y n := by
  induction n generalizing y with
  | zero => cases h; exact .refl _
  | succ n ih =>
    obtain ⟨z, hx, hy⟩ := Option.bind_eq_some_iff.1 h
    exact .tail _ _ _ _ (ih hx) hy

private theorem iteration (x : State (model W) layout) {b : Item W}
    {r s : Record (model W) layout} (pc : x.pc = 12)
    (dst : x.ptr 1 = some b.slot) (src : x.ptr 2 = some b.source) (null : x.ptr 3 = none)
    (dr : x.heap[b.slot]? = some r) (sr : x.heap[b.source]? = some s) (key : s.data 0 = b.key)
    (apart : b.slot ≠ b.source) :
    ∃ y, Runs (program W) x y 7 ∧ y.pc = 12 ∧ y.ptr 0 = x.ptr 0 ∧ y.ptr 1 = r.ptr 0 ∧
      y.ptr 2 = s.ptr 0 ∧ y.ptr 3 = none ∧ y.heap = write x.heap b := by
  let z := ((x.setData 0 b.key).setPtr 1 (r.ptr 0)).setPtr 2 (s.ptr 0)
  let y : State (model W) layout := { z with pc := 12, heap := write x.heap b }
  refine ⟨y, runs_advance ?_, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp [advance, step, program, code, Instr.effect, Instr.next, State.deref, State.modify,
      State.setPtr, State.setData, Function.update, pc, dst, src, null, dr, sr, key,
      List.getElem?_modify_ne, apart, y, z, write]
    rfl
  all_goals simp [y, z, State.setData, State.setPtr, null]

private theorem finish (x : State (model W) layout) (pc : x.pc = 12)
    (dst : x.ptr 1 = none) (zero : x.ptr 3 = none) :
    Runs (program W) x {x with pc := 0} 2 := by
  apply runs_advance
  simp [advance, step, program, code, Instr.effect, Instr.next, pc, dst, zero]

/-- After binding, the tree operand record has the input key and points back to the
corresponding physical input edge. -/
def Installed (H : List (Record (model W) layout)) (b : Item W) : Prop :=
  ∃ r, H[b.slot]? = some r ∧ r.data 0 = b.key ∧ r.ptr 4 = some b.source

/-- Binding uses seven instructions per coordinate and two for final dispatch. Tree and
output-list pointers survive. The physical addresses outside the slot list keep their records. -/
theorem Aligned.bind {sp ep : Pointer} {xs : List (Item W)} (x : State (model W) layout)
    (chain : Aligned x.heap sp ep xs) (nd : (xs.map Item.slot).Nodup)
    (disj : ∀ a ∈ xs, ∀ b ∈ xs, a.slot ≠ b.source) (pc : x.pc = 12)
    (headS : x.ptr 1 = sp) (headE : x.ptr 2 = ep) (zero : x.ptr 3 = none) :
    ∃ y, Runs (program W) x y (7 * xs.length + 2) ∧ y.pc = 0 ∧ y.ptr 0 = x.ptr 0 ∧
      y.ptr 3 = none ∧ Preserves x.heap y.heap ∧ (∀ b ∈ xs, Installed y.heap b) ∧
      ∀ i ∉ xs.map Item.slot, y.heap[i]? = x.heap[i]? := by
  induction xs generalizing x sp ep with
  | nil =>
    cases chain
    exact ⟨_, finish x pc headS zero, rfl, rfl, zero, Preserves.refl _, by simp, by simp⟩
  | cons b rest ih =>
    cases chain with
    | cons dr sr key tail =>
      rename_i r s
      obtain ⟨z, run, pc', root, dst, src, nil3, heap⟩ := iteration x pc headS headE zero dr sr key
        (disj b List.mem_cons_self b List.mem_cons_self)
      have frame : Preserves x.heap z.heap := heap ▸ write_preserves _ _
      have next : Aligned z.heap (r.ptr 0) (s.ptr 0) rest :=
        tail.transport frame fun j hj => heap ▸ write_other _ _
          (disj b List.mem_cons_self j (List.mem_cons_of_mem _ hj))
      obtain ⟨y, more, enter, tree, nil', stable, bound, outside⟩ :=
        ih z next (List.nodup_cons.1 nd).2
        (fun a ha c hc => disj a (List.mem_cons_of_mem _ ha) c (List.mem_cons_of_mem _ hc))
        pc' dst src nil3
      refine ⟨y, ?_, enter, tree.trans root, nil', frame.trans stable, ?_, ?_⟩
      · have steps := run.trans more
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using steps
      · intro item hi
        rcases List.mem_cons.1 hi with eq | hi
        · subst item
          have freed := (List.nodup_cons.1 nd).1
          have read := (outside _ freed).trans (heap ▸ write_self dr)
          exact ⟨_, read, by simp [copyKey, linkInput], by simp [linkInput]⟩
        · exact bound item hi
      · intro j hj
        have hb : b.slot ≠ j := fun h => hj (by simp [h])
        have later : j ∉ rest.map Item.slot := fun h => hj (List.mem_cons_of_mem _ h)
        exact (outside _ later).trans (heap ▸ write_other _ _ hb)

theorem Preserves.stored {H K : List (Record (model W) layout)} {addr : E → ℕ}
    {out : O → Pointer} {p : FreeM (LEQuery E) O} {i : ℕ} (tree : Stored H addr out p i)
    (frame : Preserves H K) : Stored K addr out p i := by
  induction tree with
  | leaf read tag result =>
    obtain ⟨s, hs, keep⟩ := frame _ _ read
    exact .leaf hs ((keep 0 (by decide)).trans tag) ((keep 1 (by decide)).trans result)
  | node read fst snd yes no _ _ ihL ihR =>
    obtain ⟨s, hs, keep⟩ := frame _ _ read
    exact .node hs ((keep 0 (by decide)).trans fst) ((keep 1 (by decide)).trans snd)
      ((keep 2 (by decide)).trans yes) ((keep 3 (by decide)).trans no) ihL ihR

theorem Preserves.edgeList {m : ℕ} {H K : List (Record (model W) layout)} {ptr : Pointer}
    {es : List (Fin m)} (h : EdgeList H ptr es) (frame : Preserves H K) : EdgeList K ptr es := by
  induction h with
  | nil => exact .nil
  | cons read key next _ ih =>
    obtain ⟨s, hs, keep⟩ := frame _ _ read
    exact .cons hs ((keep 0 (by decide)).trans key) ((keep 1 (by decide)).trans next) ih

private theorem traversal_step {x y : State (model W) layout} (hit : step (code W) x = some y) :
    step (program W) x = some y := by
  have used : x.pc < 11 := by
    by_contra h
    by_cases last : x.pc = 11
    · simp [step, code, last] at hit
    · have beyond : (code W).length ≤ x.pc := by change 12 ≤ _; omega
      simp [step, List.getElem?_eq_none beyond] at hit
  have read : (program W)[x.pc]? = (code W)[x.pc]? := by
    rw [program, List.getElem?_append_left, List.getElem?_take_of_lt used]
    simpa [code] using used
  simpa only [step, read] using hit

private theorem traversal_runs {x y : State (model W) layout} {n : ℕ} (h : Runs (code W) x y n) :
    Runs (program W) x y n := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ step ih => exact .tail _ _ _ _ ih (traversal_step step)

private theorem old_halt {pc : ℕ} (h : (code W)[pc]? = some .halt) : pc = 11 := by
  obtain ⟨lt, _⟩ := List.getElem?_eq_some_iff.1 h
  change pc < 12 at lt
  interval_cases pc <;> simp [code] at h ⊢

/-- A physical input edge has been selected when field 4 points back to its own address. -/
def Flagged (H : List (Record (model W) layout)) (i : ℕ) : Prop :=
  ∃ r : Record (model W) layout, H[i]? = some r ∧ r.ptr 4 = some i

private def mark (H : List (Record (model W) layout)) (i : ℕ) : List (Record (model W) layout) :=
  H.modify i fun r => { r with ptr := Function.update r.ptr 4 (some i) }

private theorem mark_frame (H : List (Record (model W) layout)) (i : ℕ) :
    Preserves H (mark H i) := by
  intro j r read
  by_cases eq : i = j
  · subst j
    exact ⟨{ r with ptr := Function.update r.ptr 4 (some i) }, by simp [mark, read],
      fun f hf => by simp [Function.update, hf]⟩
  · exact ⟨r, by simp [mark, List.getElem?_modify_ne, eq, read], fun _ _ => rfl⟩

private theorem mark_flags {H : List (Record (model W) layout)} {i j : ℕ}
    {r : Record (model W) layout} (read : H[i]? = some r) :
    Flagged (mark H i) j ↔ Flagged H j ∨ i = j := by
  by_cases eq : i = j
  · subst j
    simp [Flagged, mark, read]
  · simp [Flagged, mark, List.getElem?_modify_ne, eq]

private theorem decode_one (x : State (model W) layout) {i s d : ℕ}
    {node slot edge : Record (model W) layout}
    (pc : x.pc = 21) (head : x.ptr 0 = some i) (zero : x.ptr 3 = none)
    (read : x.heap[i]? = some node) (operand : node.ptr 0 = some s)
    (key : x.heap[s]? = some slot) (bound : slot.ptr 4 = some d) (_ed : x.heap[d]? = some edge) :
    ∃ y, Runs (program W) x y 6 ∧ y.pc = 21 ∧ y.ptr 0 = node.ptr 1 ∧ y.ptr 3 = none ∧
      y.heap = mark x.heap d := by
  let z := (x.setPtr 1 (some d)).setPtr 0 (node.ptr 1)
  let y : State (model W) layout := { z with pc := 21, heap := mark x.heap d }
  refine ⟨y, runs_advance ?_, rfl, ?_, ?_, rfl⟩
  · by_cases same : i = d
    · subst d
      simp [advance, step, program, code, pc, head, zero, Instr.effect, Instr.next, State.deref,
        State.modify, State.setPtr, Function.update, read, operand, key, bound, z, y, mark]
    · simp [advance, step, program, code, pc, head, zero, Instr.effect, Instr.next, State.deref,
        State.modify, State.setPtr, Function.update, read, operand, key, bound, z, y, mark,
        List.getElem?_modify_ne, Ne.symm same]
  all_goals simp [y, z, State.setPtr, zero]

private theorem decode_runs {m : ℕ} {ptr : Pointer} (actual : Fin m → ℕ)
    (srcRange : ∀ e, m ≤ actual e) (x : State (model W) layout) {es : List (Fin m)}
    (res : EdgeList x.heap ptr es) (pc : x.pc = 21) (head : x.ptr 0 = ptr) (zero : x.ptr 3 = none)
    (valid : ∀ e ∈ es, ∃ a b : Record (model W) layout,
      x.heap[e.val]? = some a ∧ a.ptr 4 = some (actual e) ∧ x.heap[actual e]? = some b) :
    ∃ y, Executes (program W) x y (6 * es.length + 2) ∧ Preserves x.heap y.heap ∧
      ∀ j, Flagged y.heap j ↔ Flagged x.heap j ∨ ∃ e ∈ es, actual e = j := by
  induction es generalizing x ptr with
  | nil =>
    cases res
    let y : State (model W) layout := { x with pc := 27 }
    refine ⟨y, ⟨1, runs_advance ?_, rfl, rfl⟩, Preserves.refl _, ?_⟩
    · simp [advance, step, program, code, Instr.effect, Instr.next, pc, head, zero, y]
    · simp [y]
  | cons e es ih =>
    cases res with
    | cons read slot tailptr tails =>
      obtain ⟨a, b, addr, ref, src⟩ := valid e List.mem_cons_self
      obtain ⟨z, run, pc', pos, null, heap⟩ := decode_one x pc head zero read slot addr ref src
      have frame : Preserves x.heap z.heap := heap ▸ mark_frame _ _
      obtain ⟨y, ⟨n, more, stop, time⟩, keep, flags⟩ :=
        ih z (Preserves.edgeList tails frame) pc' (pos.trans tailptr) null (by
          intro f hf
          obtain ⟨u, v, hu, hv, hw⟩ := valid f (List.mem_cons_of_mem _ hf)
          have ne : actual e ≠ f.val := by have := srcRange e; omega
          have addr' : z.heap[f.val]? = some u := by
            simp [heap, mark, List.getElem?_modify_ne, ne, hu]
          obtain ⟨v', h', _⟩ := frame _ _ hw
          exact ⟨u, v', addr', hv, h'⟩)
      refine ⟨y, ⟨6 + n, run.trans more, stop, by simp at time ⊢; omega⟩, frame.trans keep, ?_⟩
      intro j
      rw [flags, heap, mark_flags src]
      simp only [List.mem_cons, exists_eq_or_imp]
      tauto

private theorem dispatch_decode (x : State (model W) layout) (pc : x.pc = 11) :
    Runs (program W) x { x.setPtr 3 none with pc := 21 } 2 := by
  apply runs_advance
  simp [advance, step, program, code, Instr.effect, Instr.next, State.setPtr, pc]

private theorem Aligned.source_read {K : List (Record (model W) layout)}
    {sp ep : Pointer} {xs : List (Item W)} (h : Aligned K sp ep xs) {b : Item W} (hb : b ∈ xs) :
    ∃ r, K[b.source]? = some r := by
  induction h with
  | nil => cases hb
  | cons _ src _ _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, src⟩
    · exact ih hb

/-- Input records are listed in the numbering of the shared topology. -/
@[expose] def items {m : ℕ} (actual : Fin m → ℕ) (w : Fin m → W) : List (Item W) :=
  (List.finRange m).map fun e => ⟨e.val, actual e, w e⟩

omit [Inhabited W] [LinearOrder W] in
private theorem item_mem {m : ℕ} (actual : Fin m → ℕ) (w : Fin m → W) (e : Fin m) :
    (⟨e.val, actual e, w e⟩ : Item W) ∈ items actual w :=
  List.mem_map.2 ⟨e, List.mem_finRange _, rfl⟩

omit [Inhabited W] [LinearOrder W] in
private theorem slot_lt {m : ℕ} {actual : Fin m → ℕ} {w : Fin m → W}
    {b : Item W} (hb : b ∈ items actual w) : b.slot < m := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hb
  exact e.isLt

omit [Inhabited W] [LinearOrder W] in
private theorem slots_nodup {m : ℕ} (actual : Fin m → ℕ) (w : Fin m → W) :
    ((items actual w).map Item.slot).Nodup := by
  simpa [items, List.map_map, Function.comp_def] using
    (List.nodup_finRange m).map Fin.val_injective

/-- Instruction count for binding edge slots, traversing comparison nodes, and marking
the selected original edge records. The constant includes dispatch and halt. -/
@[expose] def instructionCount (edges queries outputs : ℕ) : ℕ :=
  7 * edges + 8 * queries + 6 * outputs + 9

/-- Execute binding, traversal, and output decoding on one physical program. The comparison
tree and output lists can be used again on the next aligned input. Source records live outside
the reusable slot range, and only source records selected at this leaf get newly flagged. -/
theorem executes {m : ℕ} (p : FreeM (LEQuery (Fin m)) (Finset (Fin m)))
    (w : Fin m → W) (actual : Fin m → ℕ) (apart : ∀ e, m ≤ actual e)
    (x : State (model W) layout) (root : ℕ) (out : Finset (Fin m) → Pointer)
    (pc : x.pc = 12) (node : x.ptr 0 = some root) (zero : x.ptr 3 = none)
    (chain : Aligned x.heap (x.ptr 1) (x.ptr 2) (items actual w))
    (tree : Stored x.heap Fin.val out p root)
    {es : List (Fin m)} (payload : EdgeList x.heap (out (p.eval (LEQuery.keyOracle w))) es) :
    ∃ y, Executes (program W) x y (instructionCount m (p.countQueries (LEQuery.keyOracle w))
      es.length) ∧ Preserves x.heap y.heap ∧
      ∀ j, m ≤ j → (Flagged y.heap j ↔ Flagged x.heap j ∨ ∃ e ∈ es, actual e = j) := by
  obtain ⟨z, bind, entry, first, null, structureZ, installed, outside⟩ :=
    chain.bind x (slots_nodup actual w) (by
      intro a ha b hb
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hb
      exact (slot_lt ha).trans_le (apart e) |>.ne) pc rfl rfl zero
  have weights : HoldsKeys z.heap Fin.val w := by
    intro e
    obtain ⟨r, read, value, _⟩ := installed _ (item_mem actual w e)
    exact ⟨r, read, value⟩
  obtain ⟨u, ⟨n, traverse, halt, cost⟩, result, heap⟩ :=
    (Preserves.stored tree structureZ).executes weights z rfl entry (first.trans node) null
  let v : State (model W) layout := { u.setPtr 3 none with pc := 21 }
  have toDecode : Runs (program W) u v 2 := dispatch_decode u (old_halt halt)
  have shape : Preserves x.heap v.heap := by
    change Preserves x.heap u.heap
    rwa [heap]
  have chosen : v.ptr 0 = out (p.eval (LEQuery.keyOracle w)) := by
    simpa [v, State.setPtr] using result
  obtain ⟨y, ⟨k, decode, stop, work⟩, final, flags⟩ :=
    decode_runs actual apart v (Preserves.edgeList payload shape) rfl chosen
      (by simp [v, State.setPtr])
      (by
        intro e _
        obtain ⟨a, read, _, link⟩ := installed _ (item_mem actual w e)
        obtain ⟨b, readB⟩ := chain.source_read (item_mem actual w e)
        obtain ⟨b', good, _⟩ := shape _ _ readB
        have atSlot : v.heap[e.val]? = some a := by change u.heap[_]? = _; rwa [heap]
        exact ⟨a, b', atSlot, link, good⟩)
  have count : (items actual w).length = m := by simp [items]
  rw [count] at bind
  refine ⟨y, ⟨_, ((bind.trans (traversal_runs traverse)).trans toDecode).trans decode, stop, ?_⟩,
    shape.trans final, ?_⟩
  · unfold instructionCount
    omega
  · intro j hj
    rw [flags]
    have same : v.heap[j]? = x.heap[j]? := by
      change u.heap[j]? = x.heap[j]?
      rw [heap]
      apply outside
      intro bad
      obtain ⟨b, hb, eq⟩ := List.mem_map.1 bad
      exact (slot_lt hb).not_ge (eq ▸ hj)
    simp only [Flagged, same]

end Cslib.PointerMachine.ComparisonTree.Binding
