/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Quicksort
public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Algorithms.WordRAM.Quicksort.LocalModel

/-!
# Work stack for local-address quicksort

A pending range occupies two consecutive cells. The first holds its start reference and length,
and the second holds its exclusive endpoint reference. The stack cursor points at the first free
cell. Access to the stack uses immediate successor and predecessor.

## Main results

* `localPop_exec`: recover a frame and move the stack cursor back by two.
* `localRangeLength_exec`: compute a length without address subtraction.
* `localPushPair_exec`: conditionally push two measured ranges in twelve instructions or fewer.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM Reg

private abbrev stackModel := localModel

private abbrev StackState (n : ℕ) := Local.Data stackModel n 16 16

/-- Push the held endpoints and the subrange length in the supplied scalar register. -/
private def localPush (first last len : Fin 16) : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq (.op (.storeAddr sp first))
    (.seq (.op (.storeData sp len))
      (.seq (.op (.move .next sp sp))
        (.seq (.op (.storeAddr sp last)) (.op (.move .next sp sp)))))

/-- Pop the held endpoints and the subrange length into `lo`, `hi`, and `tmp`. -/
def localPop : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq (.op (.move .prev sp sp))
    (.seq (.op (.loadAddr hi sp))
      (.seq (.op (.move .prev sp sp))
        (.seq (.op (.loadAddr lo sp)) (.op (.loadData tmp sp)))))

/-- Stack reads are deterministic. -/
theorem localPop_noDraw : NoDraw localPop := by
  simp [NoDraw, localPop]

/-- Push takes five instructions and writes only the two stack slots and the stack cursor. -/
private theorem localPush_exec {n : ℕ} (first last len : Fin 16) (hLast : last ≠ sp)
    (x : Local.Data localModel n 16 16)
    (slot : Fin n) (hsp : x.addr sp = some slot) (hroom : slot.val + 2 < n) :
    let upper : Fin n := ⟨slot.val + 1, by omega⟩
    let next : Fin n := ⟨slot.val + 2, hroom⟩
    Program.Exec (Local.instructionSet localModel n 16 16) (localPush first last len) x
      { x with
        addr := Function.update x.addr sp (some next)
        refs := Function.update (Function.update x.refs slot (x.addr first)) upper (x.addr last)
        values := Function.update x.values slot (x.scalars len) } 5 := by
  intro upper next
  let x₁ := (Local.Op.storeAddr sp first).eval x
  let x₂ := (Local.Op.storeData sp len).eval x₁
  let x₃ := (Local.Op.move .next sp sp).eval x₂
  let x₄ := (Local.Op.storeAddr sp last).eval x₃
  let y := (Local.Op.move .next sp sp).eval x₄
  have hstep : Program.Exec (Local.instructionSet stackModel n 16 16)
      (localPush first last len) x y 5 :=
    .seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.op rfl))))
  have hu : slot.val + 1 < n := by omega
  have hn : slot.val + 1 + 1 < n := by omega
  simpa [y, x₄, x₃, x₂, x₁, Local.Op.eval, Local.Direction.move, hsp, hu, hn,
    upper, next, hLast, Function.update_idem, Nat.add_assoc] using hstep

/-- Pop takes five instructions and leaves the prepared stack cells unchanged. -/
theorem localPop_exec {n : ℕ} (x : Local.Data localModel n 16 16)
    (slot : Fin n) (hroom : slot.val + 2 < n)
    (hsp : x.addr sp = some ⟨slot.val + 2, hroom⟩) :
    let upper : Fin n := ⟨slot.val + 1, by omega⟩
    Program.Exec (Local.instructionSet localModel n 16 16) localPop x
      { x with
        addr := Function.update (Function.update (Function.update x.addr hi (x.refs upper))
          lo (x.refs slot)) sp (some slot)
        scalars := Function.update x.scalars tmp (x.values slot) } 5 := by
  intro upper
  let x₁ := (Local.Op.move .prev sp sp).eval x
  let x₂ := (Local.Op.loadAddr hi sp).eval x₁
  let x₃ := (Local.Op.move .prev sp sp).eval x₂
  let x₄ := (Local.Op.loadAddr lo sp).eval x₃
  let y := (Local.Op.loadData tmp sp).eval x₄
  have hstep : Program.Exec (Local.instructionSet stackModel n 16 16) localPop x y 5 :=
    .seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.op rfl))))
  have hfirst : slot.val + 2 - 1 = slot.val + 1 := by omega
  have hsecond : slot.val + 1 - 1 = slot.val := by omega
  have hne : sp ≠ hi := by decide
  have hne' : sp ≠ lo := by decide
  simpa [y, x₄, x₃, x₂, x₁, Local.Op.eval, Local.Direction.move, hsp, hfirst, hsecond,
    upper, Function.update_comm hne, Function.update_comm hne', Function.update_idem] using hstep

private abbrev StackCode := Program.Code (Local.Op stackModel 16 16)
  (Local.Test stackModel 16 16)

private def countFrom (last : Fin 16) : StackCode :=
  .loopUntil (.addrEq stackLo last)
    (.seq (.op (.move .next stackLo stackLo))
      (.op (.scalar (.bin .add) tmp tmp one)))

/-- Count the distance between two held endpoints by scanning from the first to the last. -/
def localRangeLength (first last : Fin 16) : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq (.op (.copyAddr stackLo first)) (.seq (.op (.copyData tmp zero)) (countFrom last))

/-- A range scan uses no random instruction. -/
theorem localRangeLength_noDraw (first last : Fin 16) : NoDraw (localRangeLength first last) := by
  simp [NoDraw, localRangeLength, countFrom]

private theorem countFrom_exec {n : ℕ} (last : Fin 16) (hlast : last ≠ stackLo)
    (x : StackState n) (start stop : Fin n) (k : ℕ)
    (hcursor : x.addr stackLo = some start) (hstop : x.addr last = some stop)
    (hspan : start.val + k = stop.val) (hone : x.scalars one = 1) :
    Program.Exec (Local.instructionSet stackModel n 16 16) (countFrom last) x
      { x with
        addr := Function.update x.addr stackLo (some stop)
        scalars := Function.update x.scalars tmp (x.scalars tmp + k) }
      (4 * k + 1) := by
  induction k generalizing x start with
  | zero =>
    have he : start = stop := Fin.ext (by omega)
    subst start
    have hstate :
        ({ x with
          addr := Function.update x.addr stackLo (some stop)
          scalars := Function.update x.scalars tmp (x.scalars tmp + 0) } : StackState n) = x := by
      simp only [Nat.add_zero, ← hcursor, Function.update_eq_self]
    rw [hstate]
    exact .loopUntil_exit (show x.addr stackLo = x.addr last by rw [hcursor, hstop])
  | succ k ih =>
    have hnext : start.val + 1 < n := by have := stop.isLt; omega
    let pos : Fin n := ⟨start.val + 1, hnext⟩
    let u := (Local.Op.move .next stackLo stackLo).eval x
    let v := (Local.Op.scalar (LocalScalar.bin .add) tmp tmp one).eval u
    have hu : v.addr stackLo = some pos := by
      simp [v, u, Local.Op.eval, Local.Direction.move, hcursor, hnext, pos]
    have hv : v.addr last = some stop := by
      simpa [v, u, Local.Op.eval, Local.Direction.move, hcursor, hnext, hlast] using hstop
    have ho : v.scalars one = 1 := by
      simpa [v, u, Local.Op.eval, hcursor] using hone
    have hb : Program.Exec (Local.instructionSet stackModel n 16 16)
        (.seq (.op (.move .next stackLo stackLo))
          (.op (.scalar (.bin .add) tmp tmp one))) x v 2 := .seq (.op rfl) (.op rfl)
    have ht : ¬(Local.instructionSet stackModel n 16 16).Holds (.addrEq stackLo last) x := by
      change x.addr stackLo ≠ x.addr last
      rw [hcursor, hstop]
      exact fun he => by have := congrArg Fin.val (Option.some.inj he); omega
    have hrun := Program.Exec.loopUntil_iter ht hb
      (ih v pos hu hv (by dsimp [pos]; omega) ho)
    convert hrun using 1
    · rfl
    · have hadd : x.scalars tmp + 1 + k = x.scalars tmp + (k + 1) := by ac_rfl
      simp [v, u, Local.Op.eval, Local.Direction.move, hcursor, hnext, hone,
        BinOp.eval, Function.update_idem, hadd]
    · omega

/-- Counting preserves memory and writes only the scan cursor and the length register. -/
theorem localRangeLength_exec {n : ℕ} (first last : Fin 16) (hlast : last ≠ stackLo)
    (x : Local.Data localModel n 16 16) (start stop : Fin n)
    (hstart : x.addr first = some start) (hstop : x.addr last = some stop)
    (horder : start.val ≤ stop.val) (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) :
    Program.Exec (Local.instructionSet localModel n 16 16)
      (localRangeLength first last) x
      { x with
        addr := Function.update x.addr stackLo (some stop)
        scalars := Function.update x.scalars tmp (stop.val - start.val) }
      (4 * (stop.val - start.val) + 3) := by
  let u := (Local.Op.copyAddr stackLo first).eval x
  let v := (Local.Op.copyData tmp zero).eval u
  have h₁ : Program.Exec (Local.instructionSet stackModel n 16 16)
      (.op (.copyAddr stackLo first)) x u 1 := .op rfl
  have h₂ : Program.Exec (Local.instructionSet stackModel n 16 16)
      (.op (.copyData tmp zero)) u v 1 := .op rfl
  have hcursor : v.addr stackLo = some start := by simp [v, u, Local.Op.eval, hstart]
  have hlast' : v.addr last = some stop := by simpa [v, u, Local.Op.eval, hlast] using hstop
  have hone' : v.scalars one = 1 := by simpa [v, u, Local.Op.eval] using hone
  have hrun := Program.Exec.seq h₁ (Program.Exec.seq h₂
    (countFrom_exec last hlast v start stop (stop.val - start.val) hcursor hlast'
      (by omega) hone'))
  convert hrun using 1
  · rfl
  · simp [v, u, Local.Op.eval, hzero, Function.update_idem]
  · omega

/-- Push a measured child if it has at least two elements. -/
def localPushIf (first last len : Fin 16) : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .branch (.scalar () one len) (localPush first last len) .skip

/-- Writing a stack frame is deterministic. -/
theorem localPushIf_noDraw (first last len : Fin 16) :
    NoDraw (localPushIf first last len) := by
  simp [NoDraw, localPushIf, localPush]

/-- State after conditionally storing a measured range in the next free frame. -/
@[expose] def enqueueState {n : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (hroom : slot.val + 2 < n) :
    Local.Data localModel n 16 16 :=
  let len := stop.val - start.val
  if 1 < len then
    { x with
      addr := Function.update x.addr sp (some ⟨slot.val + 2, hroom⟩)
      refs := Function.update (Function.update x.refs slot (some start))
        ⟨slot.val + 1, by omega⟩ (some stop)
      values := Function.update x.values slot len }
  else x

/-- Enqueuing an already measured child uses at most six instructions. -/
private theorem localPushIf_exec {n : ℕ} (first last len : Fin 16) (hlast : last ≠ sp)
    (x : Local.Data localModel n 16 16) (start stop slot : Fin n)
    (hstart : x.addr first = some start) (hstop : x.addr last = some stop)
    (hlen : x.scalars len = stop.val - start.val) (hone : x.scalars one = 1)
    (hslot : x.addr sp = some slot) (hroom : slot.val + 2 < n) :
    Program.ExecWithin (Local.instructionSet localModel n 16 16)
      (localPushIf first last len) x (enqueueState x start stop slot hroom) 6 := by
  have htest :
      (Local.instructionSet stackModel n 16 16).Holds (.scalar () one len) x ↔
        1 < stop.val - start.val := by simp [hone, hlen]
  by_cases h : 1 < stop.val - start.val
  · simp only [enqueueState, ite_eq_left h]
    refine Program.ExecWithin.branch_pos (htest.2 h) ⟨5, le_rfl, ?_⟩
    simpa only [hstart, hstop, hlen] using localPush_exec first last len hlast x slot hslot hroom
  · simp only [enqueueState, ite_eq_right h]
    have hskip : Program.ExecWithin (Local.instructionSet stackModel n 16 16) .skip x x 0 :=
      Program.ExecWithin.skip
    exact (Program.ExecWithin.branch_neg (fun ht => h (htest.1 ht)) hskip).mono (by decide)

/-- The next free frame advances only for a range of length at least two. -/
theorem enqueueState_top {n : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (hroom : slot.val + 2 < n) (hslot : x.addr sp = some slot) :
    (enqueueState x start stop slot hroom).addr sp =
      some (if 1 < stop.val - start.val then ⟨slot.val + 2, hroom⟩ else slot) := by
  by_cases h : 1 < stop.val - start.val <;> simp [enqueueState, h, hslot]

/-- Enqueuing changes only the stack cursor and frame cells. -/
theorem enqueueState_frame {n : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (hroom : slot.val + 2 < n) :
    (∀ r, r ≠ sp → (enqueueState x start stop slot hroom).addr r = x.addr r) ∧
    (enqueueState x start stop slot hroom).scalars = x.scalars := by
  constructor
  · intro r hr
    by_cases h : 1 < stop.val - start.val <;> simp [enqueueState, h, hr]
  · by_cases h : 1 < stop.val - start.val <;> simp [enqueueState, h]

/-- The stack cursor after a conditional enqueue. -/
@[expose] def afterEnqueue {n : ℕ} (start stop slot : Fin n) (hroom : slot.val + 2 < n) : Fin n :=
  if 1 < stop.val - start.val then ⟨slot.val + 2, hroom⟩ else slot

/-- The cursor of a conditional enqueue never retreats. -/
theorem le_afterEnqueue {n : ℕ} (start stop slot : Fin n) (hroom : slot.val + 2 < n) :
    slot.val ≤ (afterEnqueue start stop slot hroom).val := by
  unfold afterEnqueue
  split <;> simp

/-- The combined state effect of enqueuing two ranges in the given order. -/
@[expose] def enqueuePairState {n : ℕ} (x : Local.Data localModel n 16 16)
    (a b c d slot : Fin n) (hroom : slot.val + 4 < n) : Local.Data localModel n 16 16 :=
  let next := afterEnqueue a b slot (by omega)
  enqueueState (enqueueState x a b slot (by omega)) c d next
    (by unfold next afterEnqueue; split <;> omega)

/-- Two conditional enqueues, with heap space for both possible frames. -/
theorem localPushPair_exec {n : ℕ} (f₁ l₁ len₁ f₂ l₂ len₂ : Fin 16)
    (hl₁ : l₁ ≠ sp) (hf₂ : f₂ ≠ sp) (hl₂ : l₂ ≠ sp)
    (x : Local.Data localModel n 16 16) (a b c d slot : Fin n)
    (ha : x.addr f₁ = some a) (hb : x.addr l₁ = some b)
    (hc : x.addr f₂ = some c) (hd : x.addr l₂ = some d)
    (h₁ : x.scalars len₁ = b.val - a.val) (h₂ : x.scalars len₂ = d.val - c.val)
    (hone : x.scalars one = 1) (hslot : x.addr sp = some slot) (hroom : slot.val + 4 < n) :
    Program.ExecWithin (Local.instructionSet localModel n 16 16)
      (.seq (localPushIf f₁ l₁ len₁) (localPushIf f₂ l₂ len₂)) x
      (enqueuePairState x a b c d slot hroom) 12 := by
  have hroom₁ : slot.val + 2 < n := by omega
  let u := enqueueState x a b slot hroom₁
  let next := afterEnqueue a b slot hroom₁
  have hroom₂ : next.val + 2 < n := by
    unfold next afterEnqueue
    split <;> omega
  have he₁ := localPushIf_exec f₁ l₁ len₁ hl₁ x a b slot ha hb h₁ hone hslot hroom₁
  have frame := enqueueState_frame x a b slot hroom₁
  have he₂ := localPushIf_exec f₂ l₂ len₂ hl₂ u c d next
    ((frame.1 _ hf₂).trans hc) ((frame.1 _ hl₂).trans hd)
    (by simpa only [u, frame.2] using h₂) (by simpa only [u, frame.2] using hone)
    (enqueueState_top x a b slot hroom₁ hslot) hroom₂
  exact Program.ExecWithin.seq he₁ he₂

end Cslib.Algorithms.WordRAM.Quicksort
