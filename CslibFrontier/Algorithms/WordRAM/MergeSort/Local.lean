/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
import Mathlib.Data.Nat.Log

/-!
# Buffered merge sort with local addresses

The input is a packed key array. Each cell in the two merge buffers holds a numeric
index and a reference to its key. The merge compares keys through those references and
copies both fields of the selected entry. Cursors move one cell at a time.

After each pass the program swaps the source and destination registers. The caller
reads the numeric permutation from the buffer named by `resultReg` after the last pass.

## Main definitions

* `code`: the structured local-address sorter.
* `inputState`, `resultReg`, `permutation`: the prepared input and the numeric output.

## Main results

* `code_exec`, `pointer_exec`, and `pointer_exec_small`: instruction bounds for the
  structured sorter and its compiled pointer-machine program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MergeSort.LocalRef

open Cslib.WordRAM.Local

/-- Scalar operations used for the run lengths and counters. -/
inductive Scalar where
  | add
  | sub

/-- Natural-number keys and counters with addition, subtraction, and less-than. -/
@[expose, reducible] def model : Cslib.PointerMachine.Model where
  Value := ℕ
  undefined := 0
  Op := Scalar
  Test := Unit
  evalOp
    | .add, a, b => a + b
    | .sub, a, b => a - b
  evalTest _ a b := decide (a < b)

private abbrev key : Fin 8 := 0

/-- Holds the current source buffer, including the final numeric permutation on exit. -/
abbrev resultReg : Fin 8 := 1

private abbrev src := resultReg
private abbrev dst : Fin 8 := 2
private abbrev left : Fin 8 := 3
private abbrev right : Fin 8 := 4
private abbrev out : Fin 8 := 5
private abbrev lkey : Fin 8 := 6
private abbrev rkey : Fin 8 := 7

private abbrev zero : Fin 11 := 0
private abbrev one : Fin 11 := 1
private abbrev len : Fin 11 := 2
private abbrev width : Fin 11 := 3
private abbrev remain : Fin 11 := 4
private abbrev lcount : Fin 11 := 5
private abbrev rcount : Fin 11 := 6
private abbrev walk : Fin 11 := 7
private abbrev lvalue : Fin 11 := 8
private abbrev rvalue : Fin 11 := 9
private abbrev two : Fin 11 := 10

private abbrev SortCode := Program.Code (Op model 8 11) (Test model 8 11)
private abbrev instr := @Program.Code.op (Op model 8 11) (Test model 8 11)
local infixr:70 " ▷ " => Program.Code.seq

private def less (a b : Fin 11) : Test model 8 11 := .scalar () a b

private def next (r : Fin 8) : SortCode := instr (.move .next r r)

private def dec (r : Fin 11) : SortCode := instr (.scalar .sub r r one)

private def copyScalar (dst src : Fin 11) : SortCode := instr (.copyData dst src)

private def copyRef (dst src : Fin 8) : SortCode := instr (.copyAddr dst src)

private def writeEntry (head item : Fin 8) : SortCode :=
  instr (.storeData out lvalue) ▷ instr (.storeAddr out item) ▷ next out ▷ next head

private def emit (head item : Fin 8) (count : Fin 11) : SortCode :=
  instr (.loadData lvalue head) ▷ (writeEntry head item ▷ dec count)

private def initStep : SortCode :=
  instr (.scalar .sub lvalue len remain) ▷ (writeEntry key key ▷ dec remain)

private def initEntries : SortCode :=
  copyRef out src ▷ copyScalar remain len ▷ .loopUntil (less remain one) initStep

private def takeRun (count : Fin 11) : SortCode :=
  .branch (less remain width) (copyScalar count remain) (copyScalar count width) ▷
    instr (.scalar .sub remain remain count)

private def compareHeads : SortCode :=
  instr (.loadAddr rkey right) ▷ instr (.loadData lvalue lkey) ▷ instr (.loadData rvalue rkey)

private def mergeStep : SortCode :=
  instr (.loadAddr lkey left) ▷
    .branch (less zero rcount)
      (compareHeads ▷ .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount))
      (emit left lkey lcount)

private def drainRight : SortCode :=
  instr (.loadAddr rkey right) ▷ emit right rkey rcount

private def mergePair : SortCode :=
  takeRun lcount ▷ takeRun rcount ▷
  copyRef right left ▷ copyScalar walk lcount ▷
  .loopUntil (less walk one) (next right ▷ dec walk) ▷
  .loopUntil (less lcount one) mergeStep ▷
  .loopUntil (less rcount one) drainRight ▷ copyRef left right

private def swapBuffers : SortCode :=
  copyRef left src ▷ copyRef src dst ▷ copyRef dst left

private def doubleWidth : SortCode := instr (.scalar .add width width width)

private def mergePass : SortCode :=
  copyScalar remain len ▷ copyRef left src ▷ copyRef out dst ▷
  .loopUntil (less remain one) mergePair ▷ swapBuffers ▷ doubleWidth

private def sortTwo : SortCode :=
  instr (.loadData lvalue key) ▷ next key ▷ instr (.loadData rvalue key) ▷
  copyRef out src ▷
  .branch (less rvalue lvalue)
    (instr (.storeData out one) ▷ next out ▷ instr (.storeData out zero))
    (instr (.storeData out zero) ▷ next out ▷ instr (.storeData out one))

/-- Sort references by key and return the numeric permutation buffer in `resultReg`. -/
def code : Program.Code (Op model 8 11) (Test model 8 11) :=
  .branch (less two len)
    (initEntries ▷ copyScalar width one ▷ .loop (less width len) mergePass)
    (.branch (less one len) sortTwo
      (.branch (less zero len) (instr (.storeData src zero)) .skip))

private def permBase (n : ℕ) : ℕ := n

private def scratchBase (n : ℕ) : ℕ := 2 * n

/-- Packed keys followed by equally sized output and scratch slices. -/
def inputState (keys : List ℕ) : Data model (3 * keys.length) 8 11 :=
  let n := keys.length
  { addr := fun r =>
      if hn : 0 < n then
        if r = key then some ⟨0, by omega⟩
        else if r = src then some ⟨permBase n, by unfold permBase; omega⟩
        else if r = dst then some ⟨scratchBase n, by unfold scratchBase; omega⟩
        else none
      else none
    scalars := fun r => if r = len then n else if r = one then 1 else if r = two then 2 else 0
    values := fun a => keys[a.val]?.getD 0
    refs := fun _ => none }

/-- Read the numeric permutation from the returned buffer. -/
def permutation {n : ℕ} (x : Data model (3 * n) 8 11) : List ℕ :=
  (x.addr resultReg).elim [] fun base =>
    (List.range n).filterMap fun i =>
      if h : base.val + i < 3 * n then some (x.values ⟨base.val + i, h⟩) else none

/-! ## Instruction counts

The loops depend on run lengths and counters. Key comparisons influence which counter
decreases, so a bound on both branches suffices without tracking the buffer's contents.
-/

private abbrev MachineState (cells : ℕ) := Data model cells 8 11

private abbrev within {cells : ℕ} (c : SortCode) (x y : MachineState cells) (t : ℕ) :=
  Program.ExecWithin (instructionSet model cells 8 11) c x y t

private theorem primitive {cells : ℕ} (o : Op model 8 11) (x : MachineState cells) :
    within (instr o) x (o.eval x) 1 :=
  Program.ExecWithin.op rfl

private theorem addrOp_scalars {cells : ℕ} (x : MachineState cells) (d r : Fin 8) :
    ((Op.move .next d r).eval x).scalars = x.scalars := by
  cases h : x.addr r <;> simp [Op.eval, h]

private theorem loadAddr_scalars {cells : ℕ} (x : MachineState cells) (d r : Fin 8) :
    ((Op.loadAddr d r).eval x).scalars = x.scalars := by
  cases h : x.addr r <;> simp [Op.eval, h]

private theorem less_holds {cells : ℕ} (x : MachineState cells) (a b : Fin 11) :
    (instructionSet model cells 8 11).Holds (less a b) x ↔ x.scalars a < x.scalars b := by
  simp [less, model]

private theorem countdown_exec {cells T : ℕ} (counter : Fin 11) (body : SortCode)
    (P : MachineState cells → Prop) (x : MachineState cells)
    (hone : ∀ x, P x → x.scalars one = 1)
    (hbody : ∀ x, P x → 0 < x.scalars counter → ∃ y, within body x y T ∧
      P y ∧ y.scalars counter = x.scalars counter - 1)
    (hx : P x) :
    ∃ y, within (.loopUntil (less counter one) body) x y (x.scalars counter * (T + 2) + 1) ∧
      P y ∧ y.scalars counter = 0 := by
  have step : ∀ x, P x → ¬ (instructionSet model cells 8 11).Holds (less counter one) x →
      ∃ y, within body x y T ∧ P y ∧ y.scalars counter < x.scalars counter := by
    intro x hP ht
    rw [less_holds, hone x hP] at ht
    have hp : 1 ≤ (x.scalars counter : ℕ) := Nat.le_of_not_gt ht
    obtain ⟨y, hy, hPy, hdec⟩ := hbody x hP hp
    exact ⟨y, hy, hPy, hdec ▸ Nat.sub_lt hp (by decide)⟩
  obtain ⟨y, hy, hPy, exit⟩ :=
    Program.ExecWithin.loopUntil_invariant (I := instructionSet model cells 8 11)
      P (fun x => x.scalars counter) step hx
  rw [less_holds, hone y hPy] at exit
  exact ⟨y, hy, hPy, Nat.lt_one_iff.mp exit⟩

private theorem loadData_preserves {cells : ℕ} (x : MachineState cells) (d r i)
    (hi : i ≠ d) : ((Op.loadData d r).eval x).scalars i = x.scalars i := by
  cases h : x.addr r <;> simp [Op.eval, h, Function.update_of_ne hi]

private theorem writeEntry_exec {cells : ℕ} (head item : Fin 8) (x : MachineState cells) :
    ∃ y, within (writeEntry head item) x y 4 ∧ y.scalars = x.scalars := by
  let a := (Op.storeData out lvalue).eval x
  let b := (Op.storeAddr out item).eval a
  let c := (Op.move .next out out).eval b
  let d := (Op.move .next head head).eval c
  refine ⟨d, (primitive _ x).seq ((primitive _ a).seq ((primitive _ b).seq (primitive _ c))), ?_⟩
  have h₁ : a.scalars = x.scalars := by cases h : x.addr out <;> simp [a, Op.eval, h]
  have h₂ : b.scalars = a.scalars := by cases h : a.addr out <;> simp [b, Op.eval, h]
  have h₃ : c.scalars = b.scalars := by cases h : b.addr out <;> simp [c, Op.eval, h]
  have h₄ : d.scalars = c.scalars := by cases h : c.addr head <;> simp [d, Op.eval, h]
  exact h₄.trans (h₃.trans (h₂.trans h₁))

private theorem emit_exec {cells : ℕ} (head item : Fin 8) {count : Fin 11}
    (x : MachineState cells) (hc : count ≠ lvalue) (ho : one ≠ lvalue) :
    ∃ y, within (emit head item count) x y 6 ∧
      y.scalars count = x.scalars count - x.scalars one ∧
      ∀ i, i ≠ count → i ≠ lvalue → y.scalars i = x.scalars i := by
  let z := (Op.loadData lvalue head).eval x
  obtain ⟨m, hm, hsc⟩ := writeEntry_exec head item z
  let y := (Op.scalar (M := model) .sub count count one).eval m
  have hload : within (instr (.loadData lvalue head)) x z 1 := primitive _ _
  have hdec : within (dec count) m y 1 := primitive _ _
  refine ⟨y, hload.seq (hm.seq hdec), ?_, ?_⟩
  · simp only [y, Op.eval, Function.update_self, hsc]
    rw [loadData_preserves x _ _ _ hc, loadData_preserves x _ _ _ ho]
  · intro i hi hv
    simp only [y, Op.eval, Function.update_of_ne hi, hsc]
    exact loadData_preserves x _ _ _ hv

private theorem walk_exec {cells : ℕ} (x : MachineState cells) (h₁ : x.scalars one = 1) :
    ∃ y, within (.loopUntil (less walk one) (next right ▷ dec walk))
      x y (4 * x.scalars walk + 1) ∧
      (∀ i, i ≠ walk → y.scalars i = x.scalars i) := by
  have hf : ∀ (z : MachineState cells),
      (∀ i, i ≠ walk → z.scalars i = x.scalars i) → z.scalars one = 1 :=
    fun _ hz => (hz one (by decide)).trans h₁
  have hs : ∀ (z : MachineState cells), (∀ i, i ≠ walk → z.scalars i = x.scalars i) →
      0 < z.scalars walk → ∃ y, within (next right ▷ dec walk) z y 2 ∧
        (∀ i, i ≠ walk → y.scalars i = x.scalars i) ∧
        y.scalars walk = z.scalars walk - 1 := by
    intro z hz _
    let a := (Op.move .next right right).eval z
    let b := (Op.scalar (M := model) .sub walk walk one).eval a
    refine ⟨b, (primitive _ z).seq (primitive _ a), ?_, ?_⟩
    · intro i hi
      have ha : a.scalars = z.scalars := addrOp_scalars z _ _
      simp only [b, Op.eval, Function.update_of_ne hi, ha]
      exact hz i hi
    · have ha : a.scalars = z.scalars := addrOp_scalars z _ _
      simp [b, Op.eval, ha, hf z hz]
  obtain ⟨y, h, hsc, _⟩ :=
    countdown_exec walk (next right ▷ dec walk) (fun z => ∀ i, i ≠ walk → z.scalars i = x.scalars i)
      x hf hs (by simp)
  exact ⟨y, h.mono (by omega), hsc⟩

private def mergeFrame {cells : ℕ} (x y : MachineState cells) : Prop :=
  ∀ i, i ≠ lcount → i ≠ rcount → i ≠ lvalue → i ≠ rvalue → y.scalars i = x.scalars i

private theorem mergeStep_exec {cells : ℕ} (x : MachineState cells)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) (hl : 0 < x.scalars lcount) :
    ∃ y, within mergeStep x y 13 ∧ mergeFrame x y ∧
      y.scalars lcount + y.scalars rcount + 1 = x.scalars lcount + x.scalars rcount := by
  let a := (Op.loadAddr lkey left).eval x
  have ha : a.scalars = x.scalars := loadAddr_scalars x _ _
  by_cases hr : 0 < x.scalars rcount
  · let b := (Op.loadAddr rkey right).eval a
    let c := (Op.loadData lvalue lkey).eval b
    let d := (Op.loadData rvalue rkey).eval c
    have hd (i : Fin 11) (hi : i ≠ lvalue) (hj : i ≠ rvalue) : d.scalars i = x.scalars i := by
      exact (loadData_preserves c _ _ i hj).trans
        ((loadData_preserves b _ _ i hi).trans
          (congrFun (loadAddr_scalars a rkey right |>.trans ha) i))
    have hc : within compareHeads a d 3 :=
      (primitive _ a).seq ((primitive _ b).seq (primitive _ c))
    have ht : (instructionSet model cells 8 11).Holds (less zero rcount) a := by
      rwa [less_holds, ha, hzero]
    by_cases h : d.scalars rvalue < d.scalars lvalue
    · obtain ⟨y, hy, hyc, hyf⟩ := emit_exec (count := rcount) right rkey d
        (by decide) (by decide)
      have hp := Program.ExecWithin.branch_pos (neg := emit left lkey lcount)
        ((less_holds d _ _).2 h) hy
      have he : within mergeStep x y 13 := by
        unfold mergeStep
        exact (primitive (.loadAddr lkey left) x).seq
          (Program.ExecWithin.branch_pos ht (hc.seq (hp.mono (show 7 ≤ 8 by decide))))
      refine ⟨y, he, fun i hi hj hk hm => (hyf i hj hk).trans (hd i hk hm), ?_⟩
      rw [hyc, hyf lcount (by decide) (by decide), hd lcount (by decide) (by decide),
        hd rcount (by decide) (by decide), hd one (by decide) (by decide), hone]
      rw [Nat.add_assoc, Nat.sub_add_cancel hr]
    · obtain ⟨y, hy, hyc, hyf⟩ := emit_exec (count := lcount) left lkey d
        (by decide) (by decide)
      have hp := Program.ExecWithin.branch_neg (pos := emit right rkey rcount)
        (fun hh => h ((less_holds d _ _).1 hh)) hy
      have he : within mergeStep x y 13 := by
        unfold mergeStep
        exact (primitive (.loadAddr lkey left) x).seq
          (Program.ExecWithin.branch_pos ht (hc.seq hp))
      refine ⟨y, he, fun i hi hj hk hm => (hyf i hi hk).trans (hd i hk hm), ?_⟩
      rw [hyc, hyf rcount (by decide) (by decide), hd lcount (by decide) (by decide),
        hd rcount (by decide) (by decide), hd one (by decide) (by decide), hone]
      rw [Nat.add_right_comm, Nat.sub_add_cancel hl]
  · obtain ⟨y, hy, hyc, hyf⟩ := emit_exec (count := lcount) left lkey a
      (by decide) (by decide)
    have ht : ¬(instructionSet model cells 8 11).Holds (less zero rcount) a := by
      rwa [less_holds, ha, hzero]
    have hp := Program.ExecWithin.branch_neg (pos := compareHeads ▷
        .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount)) ht hy
    have he : within mergeStep x y 13 := ((primitive _ x).seq hp).mono (by decide)
    refine ⟨y, he, fun i hi _ hk _ => (hyf i hi hk).trans (congrFun ha i), ?_⟩
    rw [hyc, hyf rcount (by decide) (by decide), ha, hone]
    rw [Nat.add_right_comm, Nat.sub_add_cancel hl]

private def mergeSize {cells : ℕ} (x : MachineState cells) : ℕ :=
  x.scalars lcount + x.scalars rcount

private theorem mergeFrame_trans {cells : ℕ} {x y z : MachineState cells}
    (hxy : mergeFrame x y) (hyz : mergeFrame y z) : mergeFrame x z :=
  fun i hi hj hk hm => (hyz i hi hj hk hm).trans (hxy i hi hj hk hm)

private theorem mergeLeft_exec {cells : ℕ} (x : MachineState cells)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) :
    ∃ y t, within (.loopUntil (less lcount one) mergeStep) x y t ∧ mergeFrame x y ∧
      t + 15 * (y.scalars rcount : ℕ) ≤ 15 * mergeSize x + 1 := by
  induction hsize : mergeSize x using Nat.strong_induction_on generalizing x with
  | _ size ih =>
    by_cases hl : (x.scalars lcount : ℕ) = 0
    · have ht : (instructionSet model cells 8 11).Holds (less lcount one) x :=
        (less_holds x _ _).2 (by rw [hl, hone]; decide)
      refine ⟨x, 1, Program.ExecWithin.loopUntil_exit ht, fun _ _ _ _ _ => rfl, ?_⟩
      simp [← hsize, mergeSize, hl, Nat.add_comm]
    · have hpos := Nat.pos_of_ne_zero hl
      have het : ¬(instructionSet model cells 8 11).Holds (less lcount one) x := by
        rw [less_holds, hone]
        exact Nat.not_lt_of_ge hpos
      obtain ⟨y, hy, hf, hdec⟩ := mergeStep_exec x hzero hone hpos
      have hd : mergeSize y + 1 = size := hdec.trans hsize
      have hsmall : mergeSize y < size := by omega
      obtain ⟨z, t, hz, hfr, htime⟩ := ih (mergeSize y) hsmall y
        ((hf zero (by decide) (by decide) (by decide) (by decide)).trans hzero)
        ((hf one (by decide) (by decide) (by decide) (by decide)).trans hone) rfl
      refine ⟨z, 13 + t + 2, Program.ExecWithin.loopUntil_iter het hy hz,
        mergeFrame_trans hf hfr, ?_⟩
      omega

private theorem drainRight_exec {cells : ℕ} (x : MachineState cells)
    (hone : x.scalars one = 1) :
    ∃ y, within (.loopUntil (less rcount one) drainRight) x y
      (9 * (x.scalars rcount : ℕ) + 1) ∧ mergeFrame x y := by
  have step (a : MachineState cells) (hf : mergeFrame x a) (_ : 0 < a.scalars rcount) :
      ∃ b, within drainRight a b 7 ∧ mergeFrame x b ∧ b.scalars rcount = a.scalars rcount - 1 := by
    let z := (Op.loadAddr rkey right).eval a
    have hz : z.scalars = a.scalars := loadAddr_scalars a _ _
    obtain ⟨b, hb, hcount, hframe⟩ := emit_exec (count := rcount) right rkey z
      (by decide) (by decide)
    refine ⟨b, (primitive (.loadAddr rkey right) a).seq hb, ?_, ?_⟩
    · intro i hi hj hk hm
      exact (hframe i hj hk).trans ((congrFun hz i).trans (hf i hi hj hk hm))
    · rw [hcount, hz, hf one (by decide) (by decide) (by decide) (by decide), hone]
  obtain ⟨y, hy, hframe, _⟩ := countdown_exec rcount drainRight (mergeFrame x) x
    (fun _ h => (h one (by decide) (by decide) (by decide) (by decide)).trans hone)
    step (fun _ _ _ _ _ => rfl)
  exact ⟨y, hy.mono (by omega), hframe⟩

private theorem mergeSuffix_exec {cells : ℕ} (x : MachineState cells)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) :
    ∃ y, within (.loopUntil (less lcount one) mergeStep ▷
      .loopUntil (less rcount one) drainRight ▷ copyRef left right)
      x y (15 * mergeSize x + 3) ∧ mergeFrame x y := by
  obtain ⟨a, t, ha, hf, ht⟩ := mergeLeft_exec x hzero hone
  obtain ⟨b, hb, hg⟩ := drainRight_exec a
    ((hf one (by decide) (by decide) (by decide) (by decide)).trans hone)
  refine ⟨(Op.copyAddr left right).eval b, (ha.seq (hb.seq (primitive _ b))).mono (by omega), ?_⟩
  exact mergeFrame_trans hf hg

private def passFrame {cells : ℕ} (x y : MachineState cells) : Prop :=
  y.scalars zero = x.scalars zero ∧ y.scalars one = x.scalars one ∧
    y.scalars len = x.scalars len ∧ y.scalars width = x.scalars width

private theorem takeRun_exec {cells : ℕ} (x : MachineState cells) {count : Fin 11}
    (hr : count ≠ remain) :
    ∃ y, within (takeRun count) x y 4 ∧
      y.scalars count = min (x.scalars remain : ℕ) (x.scalars width) ∧
      y.scalars remain = (x.scalars remain : ℕ) - x.scalars width ∧
      ∀ i, i ≠ count → i ≠ remain → y.scalars i = x.scalars i := by
  let w : ℕ := min (x.scalars remain) (x.scalars width)
  have hcopy : ∃ a,
      within (.branch (less remain width) (copyScalar count remain) (copyScalar count width))
        x a 3 ∧ a.scalars = Function.update x.scalars count w := by
    by_cases h : (x.scalars remain : ℕ) < x.scalars width
    · have hp := Program.ExecWithin.branch_pos (I := instructionSet model cells 8 11)
        (neg := copyScalar count width) ((less_holds x _ _).2 h)
        (primitive (.copyData count remain) x)
      exact ⟨_, hp.mono (by decide), by simp [Op.eval, w, min_eq_left h.le]⟩
    · have hn := Program.ExecWithin.branch_neg (I := instructionSet model cells 8 11)
        (pos := copyScalar count remain) (fun ht => h ((less_holds x _ _).1 ht))
        (primitive (.copyData count width) x)
      exact ⟨_, hn, by simp [Op.eval, w, min_eq_right (Nat.le_of_not_gt h)]⟩
  obtain ⟨a, ha, hsc⟩ := hcopy
  let y := (Op.scalar (M := model) .sub remain remain count).eval a
  refine ⟨y, ha.seq (primitive _ a), ?_, ?_, ?_⟩
  · simp [y, Op.eval, hr, hsc, w]
  · simp only [y, Op.eval, Function.update_self, hsc, Function.update_of_ne (Ne.symm hr), model]
    by_cases h : (x.scalars remain : ℕ) ≤ x.scalars width
    · rw [show w = x.scalars remain from min_eq_left h, Nat.sub_self, Nat.sub_eq_zero_of_le h]
    · rw [show w = x.scalars width from min_eq_right (Nat.le_of_not_ge h)]
  · intro i hi hj
    simp [y, Op.eval, hsc, hi, hj]

private theorem mergePair_exec {cells : ℕ} (x : MachineState cells)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) :
    ∃ y, within mergePair x y
      (19 * min (x.scalars remain : ℕ) (2 * x.scalars width) + 14) ∧ passFrame x y ∧
      y.scalars remain = (x.scalars remain : ℕ) - 2 * x.scalars width := by
  obtain ⟨a, ha, hal, har, hfa⟩ := takeRun_exec (count := lcount) x (by decide)
  obtain ⟨b, hb, hbr, hbm, hfb⟩ := takeRun_exec (count := rcount) a (by decide)
  have hab (i : Fin 11) (hl : i ≠ lcount) (hr : i ≠ rcount) (hm : i ≠ remain) :
      b.scalars i = x.scalars i := (hfb i hr hm).trans (hfa i hl hm)
  let c := (Op.copyAddr right left).eval b
  let d := (Op.copyData walk lcount).eval c
  have hdc (i : Fin 11) (hi : i ≠ walk) : d.scalars i = b.scalars i := by
    simp [d, c, Op.eval, hi]
  have hdwalk : d.scalars walk = b.scalars lcount := by simp [d, c, Op.eval]
  obtain ⟨e, he, hef⟩ := walk_exec d
    ((hdc one (by decide)).trans ((hab one (by decide) (by decide) (by decide)).trans ho))
  have heq (i : Fin 11) (hi : i ≠ walk) : e.scalars i = b.scalars i :=
    (hef i hi).trans (hdc i hi)
  obtain ⟨y, hy, hyf⟩ := mergeSuffix_exec e
    ((heq zero (by decide)).trans ((hab zero (by decide) (by decide) (by decide)).trans hz))
    ((heq one (by decide)).trans ((hab one (by decide) (by decide) (by decide)).trans ho))
  have hfinal (i : Fin 11) (hl : i ≠ lcount) (hr : i ≠ rcount)
      (hv : i ≠ lvalue) (hk : i ≠ rvalue) (hw : i ≠ walk) :
      y.scalars i = b.scalars i := (hyf i hl hr hv hk).trans (heq i hw)
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hc : within (copyRef right left) b c 1 := primitive _ _
    have hd : within (copyScalar walk lcount) c d 1 := primitive _ _
    refine (ha.seq (hb.seq (hc.seq (hd.seq (he.seq hy))))).mono ?_
    rw [hdwalk, mergeSize, heq lcount (by decide), heq rcount (by decide),
      hfb lcount (by decide) (by decide), hal, hbr, har, hfa width (by decide) (by decide)]
    omega
  · exact (hfinal zero (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hab zero (by decide) (by decide) (by decide))
  · exact (hfinal one (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hab one (by decide) (by decide) (by decide))
  · exact (hfinal len (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hab len (by decide) (by decide) (by decide))
  · exact (hfinal width (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hab width (by decide) (by decide) (by decide))
  · rw [hfinal remain (by decide) (by decide) (by decide) (by decide) (by decide),
      hbm, har, hfa width (by decide) (by decide)]
    rw [Nat.sub_sub, two_mul]

-- Each pair takes up to two runs of width w, including a possibly partial last pair.
private def pairs (r w : ℕ) : ℕ :=
  if r = 0 then 0 else (r - 1) / (2 * w) + 1

private theorem pairs_step {r w : ℕ} (hr : 0 < r) (hw : 0 < w) :
    pairs r w = pairs (r - 2 * w) w + 1 := by
  by_cases h : r ≤ 2 * w
  · have hdiv : (r - 1) / (2 * w) = 0 := Nat.div_eq_of_lt (by omega)
    simp [pairs, hr.ne', Nat.sub_eq_zero_of_le h, hdiv]
  · have hrest : 0 < r - 2 * w := by omega
    have he : r - 1 = (r - 2 * w - 1) + 2 * w := by omega
    unfold pairs
    have hd : 0 < 2 * w := by omega
    rw [ite_eq_right hr.ne', ite_eq_right hrest.ne', he, Nat.add_div_right _ hd]

private theorem passFrame_trans {cells : ℕ} {x y z : MachineState cells}
    (hxy : passFrame x y) (hyz : passFrame y z) : passFrame x z := by
  rcases hxy with ⟨ha, hb, hc, hd⟩
  rcases hyz with ⟨he, hf, hg, hh⟩
  exact ⟨he.trans ha, hf.trans hb, hg.trans hc, hh.trans hd⟩

private theorem passLoop_exec {cells : ℕ} (x : MachineState cells)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1)
    (hw : 0 < x.scalars width) :
    ∃ y, within (.loopUntil (less remain one) mergePair) x y
      (19 * x.scalars remain + 16 * pairs (x.scalars remain) (x.scalars width) + 1) ∧
      passFrame x y := by
  let W : ℕ := x.scalars width
  let pot (s : MachineState cells) : ℕ := 19 * s.scalars remain + 16 * pairs (s.scalars remain) W
  have hs (a : MachineState cells) (ha : passFrame x a)
      (ht : ¬(instructionSet model cells 8 11).Holds (less remain one) a) :
      ∃ b t, within mergePair a b t ∧ passFrame x b ∧ t + 2 + pot b ≤ pot a := by
    have z := ha.1
    have o := ha.2.1
    have w := ha.2.2.2
    rw [less_holds, o, hone] at ht
    obtain ⟨b, hb, hframe, hbrem⟩ :=
      mergePair_exec a (z.trans hzero) (o.trans hone)
    have hpa : pairs (a.scalars remain) W = pairs (b.scalars remain) W + 1 := by
      rw [hbrem, w]
      exact pairs_step (Nat.le_of_not_gt ht) hw
    refine ⟨b, _, hb, passFrame_trans ha hframe, ?_⟩
    dsimp only [pot]
    rw [hpa, hbrem, w]
    let r : ℕ := a.scalars remain
    change 19 * min r (2 * W) + 14 + 2 +
      (19 * (r - 2 * W) + 16 * pairs (r - 2 * W) W) ≤
      19 * r + 16 * (pairs (r - 2 * W) W + 1)
    omega
  obtain ⟨y, hy, hframe, _⟩ :=
    Program.ExecWithin.loopUntil_potential (I := instructionSet model cells 8 11)
      (passFrame x) pot hs ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨y, hy, hframe⟩

private theorem pass_exec {cells : ℕ} (x : MachineState cells)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1)
    (hw : 0 < x.scalars width) :
    ∃ y, within mergePass x y
      (19 * x.scalars len + 16 * pairs (x.scalars len) (x.scalars width) + 8) ∧
      y.scalars zero = x.scalars zero ∧ y.scalars one = x.scalars one ∧
      y.scalars len = x.scalars len ∧ y.scalars width = x.scalars width + x.scalars width := by
  let a := (Op.copyData remain len).eval x
  let b := (Op.copyAddr left src).eval a
  let c := (Op.copyAddr out dst).eval b
  have hfc (i : Fin 11) (hi : i ≠ remain) : c.scalars i = x.scalars i := by
    simp [c, b, a, Op.eval, hi]
  have hcframe : passFrame x c :=
    ⟨hfc zero (by decide), hfc one (by decide), hfc len (by decide), hfc width (by decide)⟩
  have hcrem : c.scalars remain = x.scalars len := by simp [c, b, a, Op.eval]
  obtain ⟨d, hd, hdf⟩ := passLoop_exec c (hcframe.1.trans hzero) (hcframe.2.1.trans hone)
    (by rw [hcframe.2.2.2]; exact hw)
  let e := (Op.copyAddr left src).eval d
  let f := (Op.copyAddr src dst).eval e
  let g := (Op.copyAddr dst left).eval f
  let y := (Op.scalar (M := model) .add width width width).eval g
  have hswap : within swapBuffers d g 3 :=
    (primitive _ d).seq ((primitive _ e).seq (primitive _ f))
  have hwidth : within doubleWidth g y 1 := primitive _ _
  have hr : within mergePass x y
      (3 + (19 * c.scalars remain + 16 * pairs (c.scalars remain) (c.scalars width) +
        1 + (3 + 1))) :=
    (primitive _ x).seq ((primitive _ a).seq ((primitive _ b).seq (hd.seq (hswap.seq hwidth))))
      |>.mono (by omega)
  have hf (i : Fin 11) (hi : i ≠ width) : y.scalars i = d.scalars i := by
    simp [y, g, f, e, Op.eval, hi]
  obtain ⟨hz, ho, hn, hw'⟩ := passFrame_trans hcframe hdf
  refine ⟨y, ?_, (hf zero (by decide)).trans hz, (hf one (by decide)).trans ho,
    (hf len (by decide)).trans hn, ?_⟩
  · rw [hcrem, hcframe.2.2.2] at hr
    exact hr.mono (by omega)
  · simp [y, g, f, e, Op.eval, hw']

private theorem init_exec {cells : ℕ} (x : MachineState cells) (ho : x.scalars one = 1) :
    ∃ y, within initEntries x y (8 * x.scalars len + 3) ∧
      ∀ i, i ≠ remain → i ≠ lvalue → y.scalars i = x.scalars i := by
  let a := (Op.copyAddr out src).eval x
  let b := (Op.copyData remain len).eval a
  have hb (i : Fin 11) (hr : i ≠ remain) : b.scalars i = x.scalars i := by
    simp [b, a, Op.eval, hr]
  have hbr : b.scalars remain = x.scalars len := by simp [b, a, Op.eval]
  let P (z : MachineState cells) := ∀ i, i ≠ remain → i ≠ lvalue → z.scalars i = x.scalars i
  have hone (z : MachineState cells) (hz : P z) : z.scalars one = 1 :=
    (hz one (by decide) (by decide)).trans ho
  have hs (z : MachineState cells) (hz : P z) (_ : 0 < z.scalars remain) :
      ∃ y, within initStep z y 6 ∧ P y ∧ y.scalars remain = z.scalars remain - 1 := by
    let c := (Op.scalar (M := model) .sub lvalue len remain).eval z
    obtain ⟨d, hd, hdf⟩ := writeEntry_exec key key c
    let y := (Op.scalar (M := model) .sub remain remain one).eval d
    have he : within initStep z y 6 := (primitive _ z).seq (hd.seq (primitive _ d))
    refine ⟨y, he, ?_, ?_⟩
    · intro i hr hv
      simpa only [y, c, Op.eval, hdf, Function.update_of_ne hr, Function.update_of_ne hv]
        using hz i hr hv
    · have hrem : remain ≠ lvalue := by decide
      have hone' : one ≠ lvalue := by decide
      simp [y, c, Op.eval, hdf, hrem, hone', hone z hz]
  obtain ⟨y, hy, hf, _⟩ :=
    countdown_exec remain initStep P b hone hs (fun i hi _ => hb i hi)
  refine ⟨y, (primitive _ x |>.seq ((primitive _ a).seq hy)).mono ?_, hf⟩
  rw [hbr]
  omega

-- At width 2^k the quotient bounds the remaining geometric sum of pair counts.
-- The linear term pays the scan, one pair per pass, and the fixed pass overhead.
private def outerBudget (n k : ℕ) : ℕ :=
  (Nat.clog 2 n - k) * (19 * n + 26) + 16 * ((n - 1) / 2 ^ k) + 2

private theorem outerBudget_step {n k : ℕ} (hn : 0 < n) (hk : k < Nat.clog 2 n) :
    (19 * n + 16 * pairs n (2 ^ k) + 8) + 2 + outerBudget n (k + 1) ≤ outerBudget n k := by
  let q := (n - 1) / 2 ^ k
  have hdiv : (n - 1) / (2 * 2 ^ k) = q / 2 := by
    rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
  have hstep : Nat.clog 2 n - k = (Nat.clog 2 n - (k + 1)) + 1 := by omega
  have hhalf : 2 * (q / 2) ≤ q := by omega
  unfold outerBudget
  rw [hstep, Nat.add_mul, hpow, hdiv]
  simp only [pairs, ite_eq_right hn.ne', hdiv, Nat.one_mul]
  omega

private theorem outer_exec {cells n k : ℕ} (x : MachineState cells)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1)
    (hn : x.scalars len = n) (hw : x.scalars width = 2 ^ k) :
    ∃ y, within (.loop (less width len) mergePass) x y (outerBudget n k) := by
  induction h : Nat.clog 2 n - k using Nat.strong_induction_on generalizing k x with
  | _ remaining ih =>
    by_cases ht : (instructionSet model cells 8 11).Holds (less width len) x
    · have hlt : (2 : ℕ)^k < n := by
        rw [← hw, ← hn]
        exact (less_holds x width len).1 ht
      have hk : k < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by decide)).2 hlt
      obtain ⟨z, he, hzero, hone, hlen, hwidth⟩ := pass_exec x hz ho (by rw [hw]; positivity)
      have hd : Nat.clog 2 n - (k + 1) < remaining := by omega
      have hpow : z.scalars width = (2 : ℕ) ^ (k + 1) := by
        rw [hwidth, hw, pow_succ, Nat.mul_two]
      obtain ⟨y, hy⟩ := ih _ hd (k := k + 1) z (hzero.trans hz) (hone.trans ho)
        (hlen.trans hn) hpow rfl
      have he' := Program.ExecWithin.loop_iter ht he hy
      rw [hn, hw] at he'
      have hbound := outerBudget_step (Nat.zero_lt_of_lt hlt) hk
      exact ⟨y, he'.mono (by omega)⟩
    · exact ⟨x, (Program.ExecWithin.loop_exit ht).mono (by unfold outerBudget; omega)⟩

/-- From a prepared input of length at least three, the buffered sorter runs within
`19 * N * L + 24 * N + 26 * L - 9` structured instructions, where `L = Nat.clog 2 N`. -/
theorem code_exec (keys : List ℕ) (hn : 3 ≤ keys.length) :
    ∃ y, Program.ExecWithin (instructionSet model (3 * keys.length) 8 11) code (inputState keys) y
      (19 * keys.length * Nat.clog 2 keys.length + 24 * keys.length +
        26 * Nat.clog 2 keys.length - 9) := by
  let n := keys.length
  let x := inputState keys
  have ht : (instructionSet model (3 * n) 8 11).Holds (less two len) x :=
    (less_holds x two len).2 (show 2 < n from hn)
  obtain ⟨a, ha, hf⟩ := init_exec x rfl
  let b := (Op.copyData width one).eval a
  have hb : within (copyScalar width one) a b 1 := primitive _ _
  have hbframe (i : Fin 11) (hi : i ≠ width) (hr : i ≠ remain) (hv : i ≠ lvalue) :
      b.scalars i = x.scalars i := by
    exact (Function.update_of_ne hi _ _).trans (hf i hr hv)
  have hz : b.scalars zero = 0 := hbframe zero (by decide) (by decide) (by decide)
  have ho : b.scalars one = 1 := hbframe one (by decide) (by decide) (by decide)
  have hlen : b.scalars len = n := hbframe len (by decide) (by decide) (by decide)
  have hw : b.scalars width = 2 ^ (0 : ℕ) := by
    change Function.update a.scalars width (a.scalars one) width = 1
    rw [Function.update_self]
    exact hf one (by decide) (by decide)
  obtain ⟨y, hy⟩ := outer_exec b hz ho hlen hw
  refine ⟨y, ?_⟩
  unfold code
  apply (Program.ExecWithin.branch_pos ht (ha.seq (hb.seq hy))).mono
  change 8 * n + 3 + (1 + outerBudget n 0) + 1 ≤
    19 * n * Nat.clog 2 n + 24 * n + 26 * Nat.clog 2 n - 9
  unfold outerBudget
  simp only [Nat.sub_zero, pow_zero, Nat.div_one, Nat.mul_add]
  rw [Nat.mul_comm (Nat.clog 2 n) (19 * n), Nat.mul_comm (Nat.clog 2 n) 26]
  change 3 ≤ n at hn
  omega

/-- The compiled pointer machine meets the buffered sorter's bound with one additional
instruction for the final halt. -/
theorem pointer_exec (keys : List ℕ) (hn : 3 ≤ keys.length) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ 19 * keys.length * Nat.clog 2 keys.length + 24 * keys.length +
        26 * Nat.clog 2 keys.length - 8 := by
  obtain ⟨_, t, ht, he⟩ := code_exec keys hn
  exact ⟨_, t + 1, executes_compile he, by omega⟩

private theorem sortTwo_exec {cells : ℕ} (x : MachineState cells) :
    ∃ y, within sortTwo x y 9 := by
  let a := (Op.loadData lvalue key).eval x
  let b := (Op.move .next key key).eval a
  let c := (Op.loadData rvalue key).eval b
  let d := (Op.copyAddr out src).eval c
  have stores (first second : Fin 11) :
      ∃ y, within (instr (.storeData out first) ▷ next out ▷ instr (.storeData out second))
        d y 3 := by
    let e := (Op.storeData out first).eval d
    let f := (Op.move .next out out).eval e
    exact ⟨_, (primitive _ d).seq ((primitive _ e).seq (primitive _ f))⟩
  have branch : ∃ y, within (.branch (less rvalue lvalue)
      (instr (.storeData out one) ▷ next out ▷ instr (.storeData out zero))
      (instr (.storeData out zero) ▷ next out ▷ instr (.storeData out one))) d y 5 := by
    by_cases h : (instructionSet model cells 8 11).Holds (less rvalue lvalue) d
    · obtain ⟨y, hy⟩ := stores one zero
      exact ⟨y, (Program.ExecWithin.branch_pos h hy).mono (by decide)⟩
    · obtain ⟨y, hy⟩ := stores zero one
      exact ⟨y, Program.ExecWithin.branch_neg h hy⟩
  obtain ⟨y, hy⟩ := branch
  exact ⟨y, (primitive _ x).seq
    ((primitive _ a).seq ((primitive _ b).seq ((primitive _ c).seq hy)))⟩

/-- Inputs of length zero or one cost at most seven instructions. Two keys cost at most
thirteen. Both counts include the final pointer-machine halt. -/
theorem pointer_exec_small (keys : List ℕ) (hn : keys.length ≤ 2) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ if keys.length < 2 then 7 else 13 := by
  let x := inputState keys
  let I := instructionSet model (3 * keys.length) 8 11
  have htwo : ¬I.Holds (less two len) x :=
    fun h => (Nat.not_lt_of_ge hn) ((less_holds x two len).1 h)
  have hrun : ∃ y, within code x y (if keys.length < 2 then 6 else 12) := by
    unfold code
    by_cases hone : 1 < keys.length
    · obtain ⟨y, hy⟩ := sortTwo_exec x
      have h := Program.ExecWithin.branch_pos
        (neg := .branch (less zero len) (instr (.storeData src zero)) .skip)
        ((less_holds x one len).2 hone) hy
      refine ⟨y, (Program.ExecWithin.branch_neg htwo h).mono ?_⟩
      rw [ite_eq_right (by omega)]
    · have hnot : ¬I.Holds (less one len) x :=
        fun h => hone ((less_holds x one len).1 h)
      rw [ite_eq_left (by omega)]
      by_cases hzero : 0 < keys.length
      · have h := Program.ExecWithin.branch_pos (neg := .skip)
          ((less_holds x zero len).2 hzero) (primitive (.storeData src zero) x)
        exact ⟨_, Program.ExecWithin.branch_neg htwo (Program.ExecWithin.branch_neg hnot h)⟩
      · have hnotzero : ¬I.Holds (less zero len) x :=
          fun h => hzero ((less_holds x zero len).1 h)
        have h := Program.ExecWithin.branch_neg (pos := instr (.storeData src zero))
          hnotzero (Program.ExecWithin.skip (I := I) (T := 0))
        exact ⟨_, Program.ExecWithin.branch_neg htwo (Program.ExecWithin.branch_neg hnot h)⟩
  obtain ⟨_, t, ht, he⟩ := hrun
  refine ⟨_, t + 1, executes_compile he, ?_⟩
  by_cases h : keys.length < 2 <;> simp [h] at ht ⊢ <;> omega

end Cslib.Algorithms.WordRAM.MergeSort.LocalRef
