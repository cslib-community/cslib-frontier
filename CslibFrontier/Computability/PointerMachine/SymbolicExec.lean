/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Notation
public import CslibFrontier.Computability.PointerMachine.SimpAttr
public import CslibFrontier.Computability.Program.WP
public meta import Lean.Elab.Tactic.Simp

/-!
# Symbolic execution of structured pointer-machine programs

Correctness proofs of structured programs follow the program text. `WP c x Q` is the
weakest-precondition form of `ExecWithin` (`Cslib.Program.WP` at the pointer machine), and the
tactic `pm_exec` runs its rules: it executes data instructions and conditionals on a symbolic
state and stops at loops and subprograms, which continue with `WP.loopUntil`, `WP.loop` and
`WP.call`.

Two kinds of facts never need stating in a specification, because they are read off the program
text and decided by `pm_frame`:

* `Code.ptrDests c`, `Code.dataDests c`: the registers that the instructions of `c` assign;
  executions keep every other register (`ExecWithin.ptr_keep`, `ExecWithin.data_keep`);
* `Code.KeepsHeap c`: no instruction of `c` stores or creates, so executions keep all records
  (`ExecWithin.heap_eq`);
* `Code.KeepsSize c`, `Code.fieldDests c`: no instruction creates a record, and the data fields
  that instructions store into; executions keep the number of records and every other data
  field (`ExecWithin.length_eq`, `ExecWithin.field_keep`).

For a small program with a fixed text, `pm_frame` evaluates these. For a large one, or one whose
text depends on a parameter, they follow by `simp` from the frames of its subprograms
(`Code.dataDests_seq` and the like).

## Main definitions

* `WP`: weakest preconditions for the pointer machine.
* `Code.ptrDests`, `Code.dataDests`, `Code.KeepsHeap`: frames read off the program text.

## Tactics

* `pm_exec`, `pm_exec [lemmas]` (scoped): on a goal `WP c x Q`, executes the data instructions
  and conditionals of `c`. The state reached is kept in assignment form by the simp set
  `pm_simps` and the given lemmas, which typically say which record a register specifies. A
  program given by name is a stop, where its specification applies (`WP.call`), unless its name
  is among the lemmas. A conditional takes the alternative that the simplified test decides,
  and otherwise splits.
* `pm_frame` (scoped): decides a frame condition, `c.ptrDests ⊆ ws`, `c.dataDests ⊆ ws` or
  `c.KeepsHeap`, from the program text.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- `WP c x Q`: the program `c` leads from `x` to a state `y`, in `n` instructions, with
`Q y n`. -/
abbrev WP (c : Code M L) (x : State M L) (Q : State M L → ℕ → Prop) : Prop :=
  Program.WP (instructionSet M L) c x Q

/-- A data instruction, with the state it reaches. -/
theorem WP.op {o : Op M L} {x : State M L} {Q : State M L → ℕ → Prop} (h : Q (o.effect x) 1) :
    WP (.op o) x Q :=
  Program.WP.op rfl h

/-- A specification is a weakest precondition whose postcondition bounds the count. -/
theorem WP.exists_execWithin {c : Code M L} {x : State M L} {T : ℕ} {P : State M L → Prop}
    (h : WP c x fun y n => n ≤ T ∧ P y) : ∃ y, ExecWithin c x y T ∧ P y :=
  Program.WP.exists_execWithin h

/-! ## Data instructions as assignments -/

section Effect

variable (x : State M L)

@[pm_simps] theorem Op.effect_null (r : Fin L.ptrRegs) :
    (Op.null r : Op M L).effect x = x.setPtr r none := rfl

@[pm_simps] theorem Op.effect_movePtr (r r' : Fin L.ptrRegs) :
    (Op.movePtr r r' : Op M L).effect x = x.setPtr r (x.ptr r') := rfl

@[pm_simps] theorem Op.effect_moveData (s s' : Fin L.dataRegs) :
    (Op.moveData s s' : Op M L).effect x = x.setData s (x.data s') := rfl

@[pm_simps] theorem Op.effect_op (o : M.Op) (s s₁ s₂ : Fin L.dataRegs) :
    (Op.op o s s₁ s₂ : Op M L).effect x = x.setData s (M.evalOp o (x.data s₁) (x.data s₂)) := rfl

@[pm_simps] theorem Op.effect_loadPtr (r : Fin L.ptrRegs) (f : Fin L.ptrFields)
    (base : Fin L.ptrRegs) :
    (Op.loadPtr r f base : Op M L).effect x =
      (x.deref base).elim x fun n => x.setPtr r (n.ptr f) := rfl

@[pm_simps] theorem Op.effect_loadData (s : Fin L.dataRegs) (f : Fin L.dataFields)
    (base : Fin L.ptrRegs) :
    (Op.loadData s f base : Op M L).effect x =
      (x.deref base).elim x fun n => x.setData s (n.data f) := rfl

@[pm_simps] theorem Op.effect_storePtr (f : Fin L.ptrFields) (base r : Fin L.ptrRegs) :
    (Op.storePtr f base r : Op M L).effect x =
      x.modify base fun n => { n with ptr := Function.update n.ptr f (x.ptr r) } := rfl

@[pm_simps] theorem Op.effect_storeData (f : Fin L.dataFields) (base : Fin L.ptrRegs)
    (s : Fin L.dataRegs) :
    (Op.storeData f base s : Op M L).effect x =
      x.modify base fun n => { n with data := Function.update n.data f (x.data s) } := rfl

@[pm_simps] theorem Op.effect_create (r : Fin L.ptrRegs) :
    (Op.create r : Op M L).effect x =
      { x.setPtr r (some x.heap.length) with heap := x.heap ++ [.blank] } := rfl

@[pm_simps] theorem Test.holds_ptrEq (r₁ r₂ : Fin L.ptrRegs) :
    (Test.ptrEq r₁ r₂ : Test M L).Holds x ↔ x.ptr r₁ = x.ptr r₂ := Iff.rfl

@[pm_simps] theorem Test.holds_data (p : M.Test) (s₁ s₂ : Fin L.dataRegs) :
    (Test.data p s₁ s₂ : Test M L).Holds x ↔ M.evalTest p (x.data s₁) (x.data s₂) = true :=
  Iff.rfl

/-- A record store through a register that specifies address `a` modifies the record there. -/
theorem State.heap_modify {r : Fin L.ptrRegs} {a : ℕ} (h : x.ptr r = some a)
    (g : Record M L → Record M L) : (x.modify r g).heap = x.heap.modify a g := by
  simp [State.modify, h]

end Effect

attribute [pm_simps] State.ptr_setPtr State.data_setPtr State.heap_setPtr State.pc_setPtr
  State.ptr_setData State.data_setData State.heap_setData State.pc_setData State.deref_setData
  State.deref_setPtr_of_ne State.deref_setPtr_some State.deref_setPtr_none
  State.ptr_modify State.data_modify Option.elim_some Option.elim_none
  Function.update_self Function.update_of_ne ne_eq not_false_eq_true not_true_eq_false

/-! ## Frames read off the program text -/

/-- The pointer register a data instruction assigns, if any. -/
@[expose] def Op.ptrDest : Op M L → Option (Fin L.ptrRegs)
  | .null r | .movePtr r _ | .loadPtr r _ _ | .create r => some r
  | _ => none

/-- The data register a data instruction assigns, if any. -/
@[expose] def Op.dataDest : Op M L → Option (Fin L.dataRegs)
  | .moveData s _ | .loadData s _ _ | .op _ s _ _ => some s
  | _ => none

/-- Whether a data instruction stores into a record or creates one. -/
@[expose] def Op.writesHeap : Op M L → Bool
  | .storePtr .. | .storeData .. | .create _ => true
  | _ => false

theorem Op.ptr_effect_of_ne {o : Op M L} {r : Fin L.ptrRegs} (h : o.ptrDest ≠ some r)
    (x : State M L) : (o.effect x).ptr r = x.ptr r := by
  cases o <;> simp only [Op.ptrDest, ne_eq, Option.some.injEq, reduceCtorEq,
    not_false_eq_true] at h <;>
    simp only [pm_simps, State.setPtr, State.setData]
  case loadPtr => cases x.deref ‹_› <;> simp [Function.update_of_ne (Ne.symm h)]
  case loadData => cases x.deref ‹_› <;> rfl
  all_goals simp [Function.update_of_ne (Ne.symm h)]

theorem Op.data_effect_of_ne {o : Op M L} {s : Fin L.dataRegs} (h : o.dataDest ≠ some s)
    (x : State M L) : (o.effect x).data s = x.data s := by
  cases o <;> simp only [Op.dataDest, ne_eq, Option.some.injEq, reduceCtorEq,
    not_false_eq_true] at h <;>
    simp only [pm_simps, State.setPtr, State.setData]
  case loadPtr => cases x.deref ‹_› <;> rfl
  case loadData => cases x.deref ‹_› <;> simp [Function.update_of_ne (Ne.symm h)]
  all_goals simp [Function.update_of_ne (Ne.symm h)]

theorem Op.heap_effect {o : Op M L} (h : o.writesHeap = false) (x : State M L) :
    (o.effect x).heap = x.heap := by
  cases o <;> simp only [Op.writesHeap, Bool.true_eq_false] at h <;>
    simp only [pm_simps, State.setPtr, State.setData]
  case loadPtr => cases x.deref ‹_› <;> rfl
  case loadData => cases x.deref ‹_› <;> rfl

/-- The data field a data instruction stores into, if any. -/
@[expose] def Op.fieldDest : Op M L → Option (Fin L.dataFields)
  | .storeData f _ _ => some f
  | _ => none

/-- Whether a data instruction creates a record. -/
@[expose] def Op.creates : Op M L → Bool
  | .create _ => true
  | _ => false

theorem Op.length_effect {o : Op M L} (h : o.creates = false) (x : State M L) :
    (o.effect x).heap.length = x.heap.length := by
  cases o <;> simp only [Op.creates, Bool.true_eq_false] at h <;>
    simp only [pm_simps, State.setPtr, State.setData, State.length_heap_modify]
  case loadPtr => cases x.deref ‹_› <;> rfl
  case loadData => cases x.deref ‹_› <;> rfl

/-- The data fields that the instructions of the program store into. -/
@[expose] def Code.fieldDests (c : Code M L) : List (Fin L.dataFields) :=
  (Program.Code.ops c).filterMap Op.fieldDest

/-- No instruction of the program creates a record. -/
@[expose] def Code.KeepsSize (c : Code M L) : Prop :=
  ∀ o ∈ Program.Code.ops c, o.creates = false

instance (c : Code M L) : Decidable c.KeepsSize :=
  inferInstanceAs (Decidable (∀ o ∈ Program.Code.ops c, o.creates = false))

/-- The pointer registers that the instructions of the program assign. -/
@[expose] def Code.ptrDests (c : Code M L) : List (Fin L.ptrRegs) :=
  (Program.Code.ops c).filterMap Op.ptrDest

/-- The data registers that the instructions of the program assign. -/
@[expose] def Code.dataDests (c : Code M L) : List (Fin L.dataRegs) :=
  (Program.Code.ops c).filterMap Op.dataDest

/-- No instruction of the program stores into a record or creates one. -/
@[expose] def Code.KeepsHeap (c : Code M L) : Prop :=
  ∀ o ∈ Program.Code.ops c, o.writesHeap = false

instance (c : Code M L) : Decidable c.KeepsHeap :=
  inferInstanceAs (Decidable (∀ o ∈ Program.Code.ops c, o.writesHeap = false))

/-! ### Frames of composite programs

The frames of a program are those of its parts, so a large program, or one whose text is not
fixed, such as a store per field of a record, gets its frames by `simp` from lemmas about its
subprograms instead of by evaluating its whole text. -/

@[simp] theorem Code.ptrDests_skip : Code.ptrDests (Program.Code.skip : Code M L) = [] := rfl

@[simp] theorem Code.ptrDests_op (o : Op M L) :
    Code.ptrDests (Program.Code.op o : Code M L) = o.ptrDest.toList := by
  cases h : o.ptrDest <;> simp [Code.ptrDests, h]

@[simp] theorem Code.ptrDests_seq (c d : Code M L) :
    Code.ptrDests (Program.Code.seq c d) = c.ptrDests ++ d.ptrDests := by
  simp [Code.ptrDests]

@[simp] theorem Code.ptrDests_branch (t : Test M L) (c d : Code M L) :
    Code.ptrDests (Program.Code.branch t c d) = c.ptrDests ++ d.ptrDests := by
  simp [Code.ptrDests]

@[simp] theorem Code.ptrDests_loop (t : Test M L) (c : Code M L) :
    Code.ptrDests (Program.Code.loop t c) = c.ptrDests := rfl

@[simp] theorem Code.ptrDests_loopUntil (t : Test M L) (c : Code M L) :
    Code.ptrDests (Program.Code.loopUntil t c) = c.ptrDests := rfl

@[simp] theorem Code.dataDests_skip : Code.dataDests (Program.Code.skip : Code M L) = [] := rfl

@[simp] theorem Code.dataDests_op (o : Op M L) :
    Code.dataDests (Program.Code.op o : Code M L) = o.dataDest.toList := by
  cases h : o.dataDest <;> simp [Code.dataDests, h]

@[simp] theorem Code.dataDests_seq (c d : Code M L) :
    Code.dataDests (Program.Code.seq c d) = c.dataDests ++ d.dataDests := by
  simp [Code.dataDests]

@[simp] theorem Code.dataDests_branch (t : Test M L) (c d : Code M L) :
    Code.dataDests (Program.Code.branch t c d) = c.dataDests ++ d.dataDests := by
  simp [Code.dataDests]

@[simp] theorem Code.dataDests_loop (t : Test M L) (c : Code M L) :
    Code.dataDests (Program.Code.loop t c) = c.dataDests := rfl

@[simp] theorem Code.dataDests_loopUntil (t : Test M L) (c : Code M L) :
    Code.dataDests (Program.Code.loopUntil t c) = c.dataDests := rfl

@[simp] theorem Code.fieldDests_skip : Code.fieldDests (Program.Code.skip : Code M L) = [] := rfl

@[simp] theorem Code.fieldDests_op (o : Op M L) :
    Code.fieldDests (Program.Code.op o : Code M L) = o.fieldDest.toList := by
  cases h : o.fieldDest <;> simp [Code.fieldDests, h]

@[simp] theorem Code.fieldDests_seq (c d : Code M L) :
    Code.fieldDests (Program.Code.seq c d) = c.fieldDests ++ d.fieldDests := by
  simp [Code.fieldDests]

@[simp] theorem Code.fieldDests_branch (t : Test M L) (c d : Code M L) :
    Code.fieldDests (Program.Code.branch t c d) = c.fieldDests ++ d.fieldDests := by
  simp [Code.fieldDests]

@[simp] theorem Code.fieldDests_loop (t : Test M L) (c : Code M L) :
    Code.fieldDests (Program.Code.loop t c) = c.fieldDests := rfl

@[simp] theorem Code.fieldDests_loopUntil (t : Test M L) (c : Code M L) :
    Code.fieldDests (Program.Code.loopUntil t c) = c.fieldDests := rfl

@[simp] theorem Code.keepsSize_skip : Code.KeepsSize (Program.Code.skip : Code M L) := by
  simp [Code.KeepsSize]

@[simp] theorem Code.keepsSize_op (o : Op M L) :
    Code.KeepsSize (Program.Code.op o : Code M L) ↔ o.creates = false := by
  simp [Code.KeepsSize]

@[simp] theorem Code.keepsSize_seq (c d : Code M L) :
    Code.KeepsSize (Program.Code.seq c d) ↔ c.KeepsSize ∧ d.KeepsSize := by
  simp [Code.KeepsSize, or_imp, forall_and]

@[simp] theorem Code.keepsSize_branch (t : Test M L) (c d : Code M L) :
    Code.KeepsSize (Program.Code.branch t c d) ↔ c.KeepsSize ∧ d.KeepsSize := by
  simp [Code.KeepsSize, or_imp, forall_and]

@[simp] theorem Code.keepsSize_loop (t : Test M L) (c : Code M L) :
    Code.KeepsSize (Program.Code.loop t c) ↔ c.KeepsSize := Iff.rfl

@[simp] theorem Code.keepsSize_loopUntil (t : Test M L) (c : Code M L) :
    Code.KeepsSize (Program.Code.loopUntil t c) ↔ c.KeepsSize := Iff.rfl

@[simp] theorem Code.keepsHeap_skip : Code.KeepsHeap (Program.Code.skip : Code M L) := by
  simp [Code.KeepsHeap]

@[simp] theorem Code.keepsHeap_op (o : Op M L) :
    Code.KeepsHeap (Program.Code.op o : Code M L) ↔ o.writesHeap = false := by
  simp [Code.KeepsHeap]

@[simp] theorem Code.keepsHeap_seq (c d : Code M L) :
    Code.KeepsHeap (Program.Code.seq c d) ↔ c.KeepsHeap ∧ d.KeepsHeap := by
  simp [Code.KeepsHeap, or_imp, forall_and]

@[simp] theorem Code.keepsHeap_branch (t : Test M L) (c d : Code M L) :
    Code.KeepsHeap (Program.Code.branch t c d) ↔ c.KeepsHeap ∧ d.KeepsHeap := by
  simp [Code.KeepsHeap, or_imp, forall_and]

@[simp] theorem Code.keepsHeap_loop (t : Test M L) (c : Code M L) :
    Code.KeepsHeap (Program.Code.loop t c) ↔ c.KeepsHeap := Iff.rfl

@[simp] theorem Code.keepsHeap_loopUntil (t : Test M L) (c : Code M L) :
    Code.KeepsHeap (Program.Code.loopUntil t c) ↔ c.KeepsHeap := Iff.rfl

namespace ExecWithin

variable {c : Code M L} {x y : State M L} {T : ℕ}

/-- Executions keep the pointer registers outside any list containing those the program
assigns. -/
theorem ptr_keep (run : ExecWithin c x y T) (ws : List (Fin L.ptrRegs)) (sub : c.ptrDests ⊆ ws)
    {r : Fin L.ptrRegs} (hr : r ∉ ws) : y.ptr r = x.ptr r :=
  let ⟨_, _, he⟩ := run
  Program.Exec.invariant_ops (I := instructionSet M L) (fun z => z.ptr r = x.ptr r) he
    (fun o ho z _ hz hP => Option.some.inj hz ▸ (o.ptr_effect_of_ne
      (fun h => hr (sub (List.mem_filterMap.mpr ⟨o, ho, h⟩))) z).trans hP) rfl

/-- Executions keep the data registers outside any list containing those the program
assigns. -/
theorem data_keep (run : ExecWithin c x y T) (ws : List (Fin L.dataRegs))
    (sub : c.dataDests ⊆ ws) {s : Fin L.dataRegs} (hs : s ∉ ws) : y.data s = x.data s :=
  let ⟨_, _, he⟩ := run
  Program.Exec.invariant_ops (I := instructionSet M L) (fun z => z.data s = x.data s) he
    (fun o ho z _ hz hP => Option.some.inj hz ▸ (o.data_effect_of_ne
      (fun h => hs (sub (List.mem_filterMap.mpr ⟨o, ho, h⟩))) z).trans hP) rfl

/-- Executions of a program that creates no record keep the number of records. -/
theorem length_eq (run : ExecWithin c x y T) (keep : c.KeepsSize) :
    y.heap.length = x.heap.length :=
  let ⟨_, _, he⟩ := run
  Program.Exec.invariant_ops (I := instructionSet M L)
    (fun z => z.heap.length = x.heap.length) he
    (fun o ho z _ hz hP => Option.some.inj hz ▸ (o.length_effect (keep o ho) z).trans hP) rfl

/-- Executions of a program that creates no record keep every data field it does not store
into, at every address. -/
theorem field_keep (run : ExecWithin c x y T) (keep : c.KeepsSize) {f : Fin L.dataFields}
    (hf : f ∉ c.fieldDests) (a : ℕ) :
    (y.heap[a]?).map (fun r => r.data f) = (x.heap[a]?).map (fun r => r.data f) := by
  refine run.data_frame f (fun o ho => ?_) a
  have created := keep o ho
  have stored : o.fieldDest ≠ some f := fun h => hf (List.mem_filterMap.mpr ⟨o, ho, h⟩)
  cases o <;> simp_all [Op.instr, Instr.WritesData, Op.fieldDest, Op.creates]

/-- Executions of a program that neither stores nor creates keep all records. -/
theorem heap_eq (run : ExecWithin c x y T) (keep : c.KeepsHeap) : y.heap = x.heap :=
  let ⟨_, _, he⟩ := run
  Program.Exec.invariant_ops (I := instructionSet M L) (fun z => z.heap = x.heap) he
    (fun o ho z _ hz hP => Option.some.inj hz ▸ (o.heap_effect (keep o ho) z).trans hP) rfl

end ExecWithin

/-! ## Tactics -/

/-- `pm_frame` decides a frame condition `c.ptrDests ⊆ ws`, `c.dataDests ⊆ ws` or `c.KeepsHeap`
from the program text, by evaluation. -/
scoped syntax (name := pmFrame) "pm_frame" : tactic

scoped macro_rules
  | `(tactic| pm_frame) => `(tactic| first | decide | exact of_decide_eq_true rfl)

/-- `pm_exec` executes the data instructions and conditionals of the program in a goal
`WP c x Q`, keeping the state reached in assignment form with the simp set `pm_simps` and the
given lemmas. It stops at loops and at programs given by name, unless the name is among the
given lemmas, in which case the program is unfolded and executed; at the end of the program it
leaves the postcondition. A conditional takes the alternative that the simplified test decides,
and otherwise splits into both, with the test or its negation as hypothesis `ht`. -/
scoped syntax (name := pmExec) "pm_exec" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

scoped macro_rules
  | `(tactic| pm_exec) => `(tactic| pm_exec [])
  | `(tactic| pm_exec [$args,*]) => `(tactic|
      (try simp only [$args,*]
       repeat' first
        | with_reducible refine Cslib.Program.WP.seq ?_
        | (with_reducible refine Cslib.PointerMachine.WP.op ?_
           try simp only [pm_simps, ↓reduceIte, Fin.isValue, Fin.reduceEq, $args,*])
        | (with_reducible refine Cslib.Program.WP.skip ?_
           try simp only [pm_simps, ↓reduceIte, Fin.isValue, Fin.reduceEq, $args,*])
        | (with_reducible apply Cslib.Program.WP.branch_pos
           · simp [pm_simps, $args,*])
        | (with_reducible apply Cslib.Program.WP.branch_neg
           · simp [pm_simps, $args,*])
        | (with_reducible refine Cslib.Program.WP.branch (fun ht => ?_) (fun ht => ?_)
           all_goals try simp only [pm_simps, $args,*] at ht)))

end Cslib.PointerMachine
