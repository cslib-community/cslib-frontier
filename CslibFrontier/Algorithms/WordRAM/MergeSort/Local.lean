/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Computability.WordRAM.Compile
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
* `wordRAMProgram`, `wordRAMInput`: the ordinary word-RAM program and its prepared input.

## Main results

* `code_exec`, `pointer_exec`, and `pointer_exec_small`: instruction bounds for the
  structured sorter and its compiled pointer-machine program.
* `wordRAM_executes`: the instruction bound for the interleaved standard word-RAM program.
* `wordRAM_address_arithmetic`, `wordRAM_offsets`: fixed-offset arithmetic in that program.
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
  ((.loopUntil (less lcount one) mergeStep ▷
    .loopUntil (less rcount one) drainRight) ▷ copyRef left right)

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
    ∃ y, within ((.loopUntil (less lcount one) mergeStep ▷
      .loopUntil (less rcount one) drainRight) ▷ copyRef left right)
      x y (15 * mergeSize x + 3) ∧ mergeFrame x y := by
  obtain ⟨a, t, ha, hf, ht⟩ := mergeLeft_exec x hzero hone
  obtain ⟨b, hb, hg⟩ := drainRight_exec a
    ((hf one (by decide) (by decide) (by decide) (by decide)).trans hone)
  refine ⟨(Op.copyAddr left right).eval b, ((ha.seq hb).seq (primitive _ b)).mono (by omega), ?_⟩
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
private def outerBudget (p n k : ℕ) : ℕ :=
  (Nat.clog 2 n - k) * (p * n + 26) + 16 * ((n - 1) / 2 ^ k) + 2

private theorem outerBudget_step {p n k : ℕ} (hn : 0 < n) (hk : k < Nat.clog 2 n) :
    (p * n + 16 * pairs n (2 ^ k) + 8) + 2 + outerBudget p n (k + 1) ≤ outerBudget p n k := by
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
    ∃ y, within (.loop (less width len) mergePass) x y (outerBudget 19 n k) := by
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
      have hbound := outerBudget_step (p := 19) (Nat.zero_lt_of_lt hlt) hk
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
  change 8 * n + 3 + (1 + outerBudget 19 n 0) + 1 ≤
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

section WordRAM

open Cslib.WordRAM

private abbrev FlatCode := Cslib.Program.Code (GenericOp .standard 20) (Cond 20)

private def ptrReg (i : Fin 8) : Fin 20 := i.castLE (by decide)

private def scalarReg (i : Fin 11) : Fin 20 := ⟨8 + i.val, by omega⟩

private def fieldAddr : Fin 20 := 19

private def wordOp (o : Cslib.WordRAM.Op .standard 20) : FlatCode := .op (.inl o)

-- Keys occupy one word each. Buffer entries occupy two adjacent words.
private def lowerWordOp : Cslib.WordRAM.Local.Op model 8 11 → FlatCode
  | .null dst => wordOp (.const (ptrReg dst) 0)
  | .copyAddr dst src => wordOp (.copy (ptrReg dst) (ptrReg src))
  | .move dir dst src =>
    let stride := if src = key then one else two
    let op := match dir with
      | .next => BinOp.add
      | .prev => BinOp.sub
    wordOp (.bin op (ptrReg dst) (ptrReg src) (scalarReg stride))
  | .copyData dst src => wordOp (.copy (scalarReg dst) (scalarReg src))
  | .scalar op dst a b =>
    let bin := match op with
      | .add => BinOp.add
      | .sub => BinOp.sub
    wordOp (.bin bin (scalarReg dst) (scalarReg a) (scalarReg b))
  | .loadData dst src => wordOp (.load (scalarReg dst) (ptrReg src))
  | .storeData dst src => wordOp (.store (ptrReg dst) (scalarReg src))
  | .loadAddr dst src =>
    wordOp (.bin .add fieldAddr (ptrReg src) (scalarReg one)) ▷
      wordOp (.load (ptrReg dst) fieldAddr)
  | .storeAddr dst src =>
    wordOp (.bin .add fieldAddr (ptrReg dst) (scalarReg one)) ▷
      wordOp (.store fieldAddr (ptrReg src))

private def lowerWordTest : Cslib.WordRAM.Local.Test model 8 11 → Cond 20
  | .addrEq a b => .eq (ptrReg a) (ptrReg b)
  | .scalar _ a b => .lt (scalarReg a) (scalarReg b)

private def lowerWordCode : SortCode → FlatCode
  | .skip => .skip
  | .op o => lowerWordOp o
  | .seq a b => .seq (lowerWordCode a) (lowerWordCode b)
  | .branch t a b => .branch (lowerWordTest t) (lowerWordCode a) (lowerWordCode b)
  | .loop t b => .loop (lowerWordTest t) (lowerWordCode b)
  | .loopUntil t b => .loopUntil (lowerWordTest t) (lowerWordCode b)

/-- Standard word-RAM code for the sorter on interleaved index/reference buffers.
The halt returns the base address of the active permutation buffer. -/
def wordRAMProgram : Cslib.WordRAM.Program .standard 20 :=
  (lowerWordCode code).assemble (flatMachine 0 .standard 20) 0 ++ [.halt (ptrReg resultReg)]

/-- Prepare the three slices for the ordinary word-RAM program. Each key occupies one
word, followed by two buffers of two-word entries. -/
def wordRAMInput (keys : List ℕ) : Cslib.WordRAM.State 20 :=
  let n := keys.length
  ⟨0, ⟨fun i =>
    if i = ptrReg src then n else if i = ptrReg dst then 3 * n else
    if i = scalarReg len then n else if i = scalarReg one then 1 else
    if i = scalarReg two then 2 else 0,
    fun a => keys[a]?.getD 0⟩⟩

private def localArithmetic (i : Instr .standard 20) : Bool :=
  match i with
  | .op (.alu (.bin op) dst args) =>
    let args : Fin 2 → Fin 20 := args
    if dst.val < 8 ∨ dst = fieldAddr then
      decide ((op = .add ∨ op = .sub) ∧ (args 0).val < 8 ∧
        (args 1 = scalarReg one ∨ args 1 = scalarReg two))
    else
      decide (8 ≤ (args 0).val ∧ (args 0).val < 19 ∧
        8 ≤ (args 1).val ∧ (args 1).val < 19)
  | .op (.alu .width _ _) => false
  | _ => true

/-- All arithmetic that produces an address uses a cursor and one of the two fixed
offset registers. The other arithmetic uses only scalar operands. -/
theorem wordRAM_address_arithmetic {op : BinOp} {d a b : Fin 20}
    (h : Instr.op (Cslib.WordRAM.Op.bin op d a b) ∈ wordRAMProgram)
    (hd : d.val < 8 ∨ d.val = 19) :
    (op = .add ∨ op = .sub) ∧ a.val < 8 ∧ (b.val = 9 ∨ b.val = 18) := by
  have check : wordRAMProgram.all localArithmetic = true := by decide
  have hl := List.all_eq_true.mp check _ h
  have hd' : d.val < 8 ∨ d = fieldAddr := hd.imp_right fun he => Fin.ext he
  simp only [localArithmetic, Cslib.WordRAM.Op.bin, ite_eq_left hd', decide_eq_true_eq] at hl
  obtain ⟨ho, ha, hb⟩ := hl
  exact ⟨ho, ha, hb.imp (congrArg Fin.val) (congrArg Fin.val)⟩

private def destination : Cslib.WordRAM.Op .standard 20 → Option (Fin 20)
  | .const d _ | .copy d _ | .load d _ | .alu _ d _ => some d
  | .store _ _ => none

private theorem eval_keeps_register {w : ℕ} {x y : Cslib.WordRAM.Data 20}
    {o : Cslib.WordRAM.Op .standard 20} {i : Fin 20}
    (h : o.eval w x = some y) (hi : destination o ≠ some i) : y.regs i = x.regs i := by
  cases o with
  | const =>
    obtain ⟨_, rfl⟩ := Cslib.WordRAM.Data.put_eq_some.mp h
    simp only [destination] at hi
    exact Function.update_of_ne (fun h => hi (congrArg some h.symm)) _ _
  | alu =>
    obtain ⟨_, _, _, rfl⟩ := Cslib.WordRAM.Op.eval_alu_eq_some.mp h
    simp only [destination] at hi
    exact Function.update_of_ne (fun h => hi (congrArg some h.symm)) _ _
  | copy | load =>
    cases h
    simp only [destination] at hi
    exact Function.update_of_ne (fun h => hi (congrArg some h.symm)) _ _
  | store =>
    cases h
    rfl

private theorem step_offsets {w : ℕ} {x y : Cslib.WordRAM.State 20}
    (h : Next w wordRAMProgram x y) (i : Fin 20)
    (hi : i = scalarReg one ∨ i = scalarReg two) : y.data.regs i = x.data.regs i := by
  let keeps (i : Fin 20) : Instr .standard 20 → Bool
    | .op op => decide (destination op ≠ some i)
    | _ => true
  have check : wordRAMProgram.all (keeps i) = true := by
    rcases hi with rfl | rfl <;> decide
  unfold Next Cslib.WordRAM.step at h
  split at h
  · cases h
  · next o ho =>
    have hold := List.all_eq_true.mp check _ (List.mem_of_getElem? ho)
    split at h
    · next z hz =>
      cases h
      exact eval_keeps_register hz (of_decide_eq_true hold)
    · cases h
  all_goals first | (cases h; rfl) | cases h

/-- A run from the prepared input preserves the two fixed address offsets. -/
theorem wordRAM_offsets {w t : ℕ} {keys : List ℕ} {y : Cslib.WordRAM.State 20}
    (h : Runs w wordRAMProgram (wordRAMInput keys) y t) :
    y.data.regs 9 = 1 ∧ y.data.regs 18 = 2 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ _ _ _ hs ih =>
    exact ⟨(step_offsets hs 9 (Or.inl rfl)).trans ih.1,
      (step_offsets hs 18 (Or.inr rfl)).trans ih.2⟩

private abbrev WordData := Cslib.WordRAM.Data 20

private abbrev wordWithin (w : ℕ) (c : FlatCode) (x y : WordData) (t : ℕ) :=
  Cslib.Program.ExecWithin (Cslib.WordRAM.instructionSet w .standard 20) c x y t

private theorem wordPrimitive {w : ℕ} {o : Cslib.WordRAM.Op .standard 20} {x y : WordData}
    (h : o.eval w x = some y) : wordWithin w (wordOp o) x y 1 :=
  Cslib.Program.ExecWithin.op h

private def wordStride (r : Fin 8) : ℕ := if r = key then 1 else 2

private def wordWriteEntry (x : WordData) (head item : Fin 8) : WordData :=
  let p := x.regs (ptrReg out)
  let v := x.regs (scalarReg lvalue)
  let ref := x.regs (ptrReg item)
  let y := ((x.write p v).set fieldAddr (p + 1)).write (p + 1) ref
  (y.set (ptrReg out) (p + 2)).set (ptrReg head) (x.regs (ptrReg head) + wordStride head)

private theorem wordWriteEntry_exec {w : ℕ} (x : WordData) (head item : Fin 8)
    (hhead : head ≠ out) (hitem : ptrReg item ≠ fieldAddr)
    (hone : x.regs (scalarReg one) = 1) (htwo : x.regs (scalarReg two) = 2)
    (hout : Fits w (x.regs (ptrReg out) + 2))
    (hnext : Fits w (x.regs (ptrReg head) + wordStride head)) :
    wordWithin w (lowerWordCode (writeEntry head item)) x (wordWriteEntry x head item) 5 := by
  let p := x.regs (ptrReg out)
  let a := x.write p (x.regs (scalarReg lvalue))
  let b := a.set fieldAddr (p + 1)
  let c := b.write (p + 1) (x.regs (ptrReg item))
  let d := c.set (ptrReg out) (p + 2)
  have hreg (i : Fin 20) (hi : i ≠ fieldAddr) : c.regs i = x.regs i := by
    simp [c, b, a, Function.update_of_ne hi]
  have hdreg (i : Fin 20) (hi : i ≠ fieldAddr) (hj : i ≠ ptrReg out) :
      d.regs i = x.regs i := by
    simpa [d, Function.update_of_ne hj] using hreg i hi
  have hptr (i : Fin 8) : ptrReg i ≠ fieldAddr :=
    fun h => by have := i.isLt; have he := congrArg Fin.val h; change i.val = 19 at he; omega
  have h₁ : wordWithin w (wordOp (.store (ptrReg out) (scalarReg lvalue))) x a 1 :=
    wordPrimitive rfl
  have h₂ : wordWithin w (wordOp (.bin .add fieldAddr (ptrReg out) (scalarReg one))) a b 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, Cslib.WordRAM.Data.write_regs, hone]
    exact Data.put_of_fits (hout.of_le (by change p + 1 ≤ p + 2; omega))
  have h₃ : wordWithin w (wordOp (.store fieldAddr (ptrReg item))) b c 1 := by
    apply wordPrimitive
    simp [c, b, a, Function.update_of_ne hitem]
  have h₄ : wordWithin w (wordOp (.bin .add (ptrReg out) (ptrReg out) (scalarReg two))) c d 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hreg _ (hptr out), hreg _ (by decide : scalarReg two ≠ fieldAddr), htwo]
    exact Data.put_of_fits hout
  let stride := if head = key then one else two
  have hstride : d.regs (scalarReg stride) = wordStride head := by
    by_cases hh : head = key
    · simpa only [stride, wordStride, ite_eq_left hh] using
        (hdreg _ (by decide : scalarReg one ≠ fieldAddr) (by decide)).trans hone
    · simpa only [stride, wordStride, ite_eq_right hh] using
        (hdreg _ (by decide : scalarReg two ≠ fieldAddr) (by decide)).trans htwo
  have hn : ptrReg head ≠ ptrReg out :=
    fun h => hhead (Fin.ext (congrArg (fun r : Fin 20 => r.val) h))
  have h₅ : wordWithin w (wordOp (.bin .add (ptrReg head) (ptrReg head) (scalarReg stride)))
      d (wordWriteEntry x head item) 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hdreg _ (hptr head) hn, hstride]
    exact Data.put_of_fits hnext
  exact h₁.seq ((h₂.seq h₃).seq (h₄.seq h₅))

-- The cursor equations are stated for the processed prefix, including the one-past position.
private structure WordInitInv (keys : List ℕ) (k : ℕ) (x : WordData) : Prop where
  le_length : k ≤ keys.length
  len_eq : x.regs (scalarReg len) = keys.length
  remain_eq : x.regs (scalarReg remain) = keys.length - k
  zero_eq : x.regs (scalarReg zero) = 0
  one_eq : x.regs (scalarReg one) = 1
  two_eq : x.regs (scalarReg two) = 2
  source_eq : x.regs (ptrReg src) = keys.length
  dest_eq : x.regs (ptrReg dst) = 3 * keys.length
  key_eq : x.regs (ptrReg key) = k
  out_eq : x.regs (ptrReg out) = keys.length + 2 * k
  keys_eq : ∀ i (hi : i < keys.length), x.mem i = keys[i]
  entries_eq : ∀ i, i < k →
    x.mem (keys.length + 2 * i) = i ∧ x.mem (keys.length + 2 * i + 1) = i

private theorem wordInitStep_exec {w k : ℕ} {keys : List ℕ} {x : WordData}
    (hfit : Fits w (5 * keys.length + 2)) (hx : WordInitInv keys k x) (hk : k < keys.length) :
    ∃ y, wordWithin w (lowerWordCode initStep) x y 7 ∧ WordInitInv keys (k + 1) y := by
  let n := keys.length
  let p := n + 2 * k
  let a := x.set (scalarReg lvalue) k
  let b := a.write p k
  let c := b.set fieldAddr (p + 1)
  let d := c.write (p + 1) k
  let e := d.set (ptrReg out) (p + 2)
  let f := e.set (ptrReg key) (k + 1)
  let y := f.set (scalarReg remain) (n - (k + 1))
  have h₁ : wordWithin w (wordOp (.bin .sub (scalarReg lvalue) (scalarReg len)
      (scalarReg remain))) x a 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hx.len_eq, hx.remain_eq]
    change x.put w (scalarReg lvalue) (n - (n - k)) = some a
    rw [show n - (n - k) = k by omega]
    exact Data.put_of_fits (hfit.of_le (by omega))
  have hframeA (i : Fin 20) (hi : i ≠ scalarReg lvalue) : a.regs i = x.regs i :=
    Function.update_of_ne hi _ _
  have hout : a.regs (ptrReg out) = p :=
    (hframeA _ (by decide)).trans hx.out_eq
  have hkey : a.regs (ptrReg key) = k :=
    (hframeA _ (by decide)).trans hx.key_eq
  have hone : a.regs (scalarReg one) = 1 :=
    (hframeA _ (by decide)).trans hx.one_eq
  have htwo : a.regs (scalarReg two) = 2 :=
    (hframeA _ (by decide)).trans hx.two_eq
  have haw : wordWithin w (lowerWordCode (writeEntry key key)) a f 5 := by
    have h : wordWriteEntry a key key = f := by
      unfold wordWriteEntry
      rw [hout, hkey, show a.regs (scalarReg lvalue) = k by simp [a]]
      rfl
    rw [← h]
    exact wordWriteEntry_exec a key key (by decide) (by decide) hone htwo
      (hfit.of_le (by rw [hout]; omega))
      (hfit.of_le (by rw [hkey]; simp only [wordStride, ite_true]; omega))
  have h₇ : wordWithin w (wordOp (.bin .sub (scalarReg remain) (scalarReg remain)
      (scalarReg one))) f y 1 := by
    apply wordPrimitive
    rw [Op.eval_bin]
    have hr : f.regs (scalarReg remain) = n - k := by
      simpa [f, e, d, c, b, a, ptrReg, scalarReg, key, out, remain, lvalue, fieldAddr]
        using hx.remain_eq
    have hone : f.regs (scalarReg one) = 1 := by
      simpa [f, e, d, c, b, a, ptrReg, scalarReg, key, out, one, lvalue, fieldAddr] using hx.one_eq
    rw [hr, hone]
    change f.put w (scalarReg remain) (n - k - 1) = some y
    rw [Nat.sub_sub]
    exact Data.put_of_fits (hfit.of_le (by omega))
  refine ⟨y, h₁.seq (haw.seq h₇), ?_⟩
  have hframe (i : Fin 20) (hl : i ≠ scalarReg lvalue) (hc : i ≠ fieldAddr)
      (ho : i ≠ ptrReg out) (hj : i ≠ ptrReg key) (hr : i ≠ scalarReg remain) :
      y.regs i = x.regs i := by
    simp [y, f, e, d, c, b, a, Function.update_of_ne, hl, hc, ho, hj, hr]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.len_eq
  · simp [y, n]
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.zero_eq
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.one_eq
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.two_eq
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.source_eq
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.dest_eq
  · simp [y, f, ptrReg, scalarReg, key, remain]
  · have h : p + 2 = n + 2 * (k + 1) := by dsimp [p]; omega
    simpa [y, f, e, ptrReg, scalarReg, key, out, remain, n] using h
  · intro i hi
    have hp : i ≠ p := by dsimp [p, n]; omega
    have hp' : i ≠ p + 1 := by dsimp [p, n]; omega
    simpa [y, f, e, d, c, b, a, Function.update_of_ne hp, Function.update_of_ne hp']
      using hx.keys_eq i hi
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · have h₁ : n + 2 * i ≠ p := by dsimp [p]; omega
      have h₂ : n + 2 * i ≠ p + 1 := by dsimp [p]; omega
      have h₃ : n + 2 * i + 1 ≠ p := by dsimp [p]; omega
      have h₄ : n + 2 * i + 1 ≠ p + 1 := by dsimp [p]; omega
      simpa [y, f, e, d, c, b, a, ← show n = keys.length from rfl,
        Function.update_of_ne h₁, Function.update_of_ne h₂,
        Function.update_of_ne h₃, Function.update_of_ne h₄] using hx.entries_eq i hlt
    · have h : p ≠ p + 1 := by omega
      change Function.update (Function.update x.mem p i) (p + 1) i p = i ∧
        Function.update (Function.update x.mem p i) (p + 1) i (p + 1) = i
      simp

private theorem wordInitEntries_exec {w : ℕ} (keys : List ℕ)
    (hfit : Fits w (5 * keys.length + 2)) :
    ∃ y, wordWithin w (lowerWordCode initEntries) (wordRAMInput keys).data y
      (9 * keys.length + 3) ∧ WordInitInv keys keys.length y := by
  let x := (wordRAMInput keys).data
  let a := x.set (ptrReg out) keys.length
  let b := a.set (scalarReg remain) keys.length
  have ha : wordWithin w (wordOp (.copy (ptrReg out) (ptrReg src))) x a 1 :=
    wordPrimitive rfl
  have hb : wordWithin w (wordOp (.copy (scalarReg remain) (scalarReg len))) a b 1 :=
    wordPrimitive rfl
  have hinit : WordInitInv keys 0 b := by
    refine ⟨Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [b, a, scalarReg, ptrReg, remain, out]
    · intro i hi
      simp [b, a, x, wordRAMInput, List.getElem?_eq_getElem hi]
    · intro i hi
      omega
  let P (s : WordData) := ∃ k, WordInitInv keys k s
  let cond := Cond.lt (scalarReg remain) (scalarReg one)
  have hs (s : WordData) (hp : P s) (ht : ¬cond.Holds s) :
      ∃ y, wordWithin w (lowerWordCode initStep) s y 7 ∧ P y ∧
        y.regs (scalarReg remain) < s.regs (scalarReg remain) := by
    obtain ⟨k, hk⟩ := hp
    change ¬s.regs (scalarReg remain) < s.regs (scalarReg one) at ht
    rw [hk.remain_eq, hk.one_eq] at ht
    have hlt : k < keys.length := by omega
    obtain ⟨y, he, hy⟩ := wordInitStep_exec hfit hk hlt
    exact ⟨y, he, ⟨k + 1, hy⟩, by rw [hy.remain_eq, hk.remain_eq]; omega⟩
  obtain ⟨y, hy, ⟨k, hk⟩, hstop⟩ :=
    Cslib.Program.ExecWithin.loopUntil_invariant
      (I := Cslib.WordRAM.instructionSet w .standard 20) (t := cond)
      P (fun s => s.regs (scalarReg remain)) hs (show P b from ⟨0, hinit⟩)
  change y.regs (scalarReg remain) < y.regs (scalarReg one) at hstop
  rw [hk.remain_eq, hk.one_eq] at hstop
  have hdone : k = keys.length := by have := hk.le_length; omega
  refine ⟨y, (ha.seq (hb.seq hy)).mono ?_, hdone ▸ hk⟩
  rw [hinit.remain_eq, Nat.sub_zero]
  omega

private def wordLoadRef (x : WordData) (d r : Fin 8) : WordData :=
  let a := x.regs (ptrReg r) + 1
  (x.set fieldAddr a).set (ptrReg d) (x.mem a)

private theorem wordLoadRef_exec {w : ℕ} (x : WordData) (d r : Fin 8)
    (hone : x.regs (scalarReg one) = 1) (hfit : Fits w (x.regs (ptrReg r) + 1)) :
    wordWithin w (lowerWordCode (instr (.loadAddr d r))) x (wordLoadRef x d r) 2 := by
  let a := x.set fieldAddr (x.regs (ptrReg r) + 1)
  have h₁ : wordWithin w (wordOp (.bin .add fieldAddr (ptrReg r) (scalarReg one))) x a 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hone]
    exact Data.put_of_fits hfit
  have h₂ : wordWithin w (wordOp (.load (ptrReg d) fieldAddr)) a (wordLoadRef x d r) 1 := by
    apply wordPrimitive
    simp [a, wordLoadRef]
  exact h₁.seq h₂

private def wordEmit (x : WordData) (head item : Fin 8) (count : Fin 11) : WordData :=
  let a := x.set (scalarReg lvalue) (x.mem (x.regs (ptrReg head)))
  (wordWriteEntry a head item).set (scalarReg count)
    (x.regs (scalarReg count) - 1)

private theorem wordEmit_exec {w : ℕ} (x : WordData) (head item : Fin 8) (count : Fin 11)
    (hhead : head ≠ out) (hitem : ptrReg item ≠ fieldAddr)
    (hc : scalarReg count ≠ scalarReg lvalue)
    (hone : x.regs (scalarReg one) = 1) (htwo : x.regs (scalarReg two) = 2)
    (hout : Fits w (x.regs (ptrReg out) + 2))
    (hnext : Fits w (x.regs (ptrReg head) + wordStride head))
    (hcount : Fits w (x.regs (scalarReg count))) :
    wordWithin w (lowerWordCode (emit head item count)) x (wordEmit x head item count) 7 := by
  let a := x.set (scalarReg lvalue) (x.mem (x.regs (ptrReg head)))
  let b := wordWriteEntry a head item
  have ha : wordWithin w (wordOp (.load (scalarReg lvalue) (ptrReg head))) x a 1 :=
    wordPrimitive rfl
  have hptr (r : Fin 8) (s : Fin 11) : ptrReg r ≠ scalarReg s := by
    intro h
    have hr := r.isLt
    have he := congrArg (fun r : Fin 20 => r.val) h
    change r.val = 8 + s.val at he
    omega
  have hscalar (s : Fin 11) : scalarReg s ≠ fieldAddr := by
    intro h
    have hs := s.isLt
    have he := congrArg (fun r : Fin 20 => r.val) h
    change 8 + s.val = 19 at he
    omega
  have hb : wordWithin w (lowerWordCode (writeEntry head item)) a b 5 :=
    wordWriteEntry_exec a head item hhead hitem
      (by simpa [a, Function.update_of_ne (by decide : scalarReg one ≠ scalarReg lvalue)])
      (by simpa [a, Function.update_of_ne (by decide : scalarReg two ≠ scalarReg lvalue)])
      (by simpa [a, Function.update_of_ne (hptr out lvalue)])
      (by simpa [a, Function.update_of_ne (hptr head lvalue)])
  have hframe (s : Fin 11) (hs : scalarReg s ≠ scalarReg lvalue) :
      b.regs (scalarReg s) = x.regs (scalarReg s) := by
    simp [b, wordWriteEntry, a, Function.update_of_ne hs, Function.update_of_ne (hscalar s),
      Function.update_of_ne (hptr out s).symm, Function.update_of_ne (hptr head s).symm]
  have hd : wordWithin w (lowerWordCode (dec count)) b (wordEmit x head item count) 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hframe count hc, hframe one (by decide), hone]
    exact Data.put_of_fits (hcount.of_le (Nat.sub_le _ _))
  exact ha.seq (hb.seq hd)

private def wordMergeSize (x : WordData) : ℕ :=
  x.regs (scalarReg lcount) + x.regs (scalarReg rcount)

-- The room inequalities ensure that the next entry can be accessed and advanced
-- whenever its run still has an entry. They include each run's one-past position.
private structure WordMergeRoom (limit : ℕ) (x : WordData) : Prop where
  left_room : x.regs (ptrReg left) + 2 * x.regs (scalarReg lcount) ≤ limit
  right_room : x.regs (ptrReg right) + 2 * x.regs (scalarReg rcount) ≤ limit
  out_room : x.regs (ptrReg out) + 2 * wordMergeSize x ≤ limit
  zero_eq : x.regs (scalarReg zero) = 0
  one_eq : x.regs (scalarReg one) = 1
  two_eq : x.regs (scalarReg two) = 2

-- A merge consumes entries without changing either run's end, or the end of its output.
private structure WordMergeFrame (x y : WordData) : Prop where
  right_end : y.regs (ptrReg right) + 2 * y.regs (scalarReg rcount) =
    x.regs (ptrReg right) + 2 * x.regs (scalarReg rcount)
  out_end : y.regs (ptrReg out) + 2 * wordMergeSize y =
    x.regs (ptrReg out) + 2 * wordMergeSize x
  left_zero : x.regs (scalarReg lcount) = 0 → y.regs (scalarReg lcount) = 0
  fixed : ∀ i ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
    scalarReg remain} : Finset (Fin 20)), y.regs i = x.regs i

private theorem WordMergeFrame.refl (x : WordData) : WordMergeFrame x x :=
  ⟨rfl, rfl, id, fun _ _ => rfl⟩

private theorem WordMergeFrame.trans {x y z : WordData}
    (hxy : WordMergeFrame x y) (hyz : WordMergeFrame y z) : WordMergeFrame x z :=
  ⟨hyz.right_end.trans hxy.right_end, hyz.out_end.trans hxy.out_end,
    fun hx => hyz.left_zero (hxy.left_zero hx),
    fun i hi => (hyz.fixed i hi).trans (hxy.fixed i hi)⟩

private abbrev sideHead (rightSide : Bool) := if rightSide then right else left
private abbrev sideItem (rightSide : Bool) := if rightSide then rkey else lkey
private abbrev sideCount (rightSide : Bool) := if rightSide then rcount else lcount

private theorem wordEmit_room {w limit : ℕ} {x : WordData} (rightSide : Bool)
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hpos : 0 < x.regs (scalarReg (sideCount rightSide))) :
    ∃ y, wordWithin w (lowerWordCode (emit (sideHead rightSide) (sideItem rightSide)
      (sideCount rightSide))) x y 7 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧
      WordMergeFrame x y := by
  have htotal : 0 < wordMergeSize x := by
    cases rightSide <;> simp [sideCount] at hpos <;> unfold wordMergeSize <;> omega
  have hout := hfit.of_le
    (show x.regs (ptrReg out) + 2 ≤ limit by have := hx.out_room; omega)
  let head := sideHead rightSide
  let item := sideItem rightSide
  let count := sideCount rightSide
  have hroom : x.regs (ptrReg head) + 2 * x.regs (scalarReg count) ≤ limit := by
    cases rightSide
    · exact hx.left_room
    · exact hx.right_room
  have hstride : wordStride head = 2 := by cases rightSide <;> decide
  have he := wordEmit_exec x head item count
    (by cases rightSide <;> decide) (by cases rightSide <;> decide)
    (by cases rightSide <;> decide) hx.one_eq hx.two_eq hout
    (hfit.of_le (by rw [hstride]; change 0 < x.regs (scalarReg count) at hpos; omega))
    (hfit.of_le (by omega))
  let y := wordEmit x head item count
  have hroom' := hx.out_room
  have hl := hx.left_room
  have hr := hx.right_room
  have hconst : y.regs (scalarReg zero) = x.regs (scalarReg zero) ∧
      y.regs (scalarReg one) = x.regs (scalarReg one) ∧
      y.regs (scalarReg two) = x.regs (scalarReg two) := by
    cases rightSide <;>
      simp (config := { decide := true }) [y, head, item, count, sideHead, sideItem, sideCount,
        wordEmit, wordWriteEntry, wordStride, ptrReg, scalarReg, fieldAddr]
  obtain ⟨hz, ho, ht⟩ := hconst
  have hfixed (i : Fin 20) (hi : i ∈ ({ptrReg src, ptrReg dst, scalarReg len,
      scalarReg width, scalarReg remain} : Finset (Fin 20))) : y.regs i = x.regs i := by
    have htest : ∀ j ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
        scalarReg remain} : Finset (Fin 20)), j ≠ fieldAddr ∧ j ≠ scalarReg lvalue ∧
        j ≠ ptrReg out ∧ j ≠ ptrReg left ∧ j ≠ ptrReg right ∧
        j ≠ scalarReg lcount ∧ j ≠ scalarReg rcount := by decide
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := htest i hi
    cases rightSide <;>
      simp [y, head, item, count, sideHead, sideCount, wordEmit, wordWriteEntry,
        Function.update_of_ne h₁, Function.update_of_ne h₂, Function.update_of_ne h₃,
        Function.update_of_ne h₄, Function.update_of_ne h₅, Function.update_of_ne h₆,
        Function.update_of_ne h₇]
  refine ⟨y, he, ⟨?_, ?_, ?_, hz.trans hx.zero_eq, ho.trans hx.one_eq,
    ht.trans hx.two_eq⟩, ?_, ⟨?_, ?_, ?_, hfixed⟩⟩ <;>
    cases rightSide <;>
      simp (config := { decide := true }) [y, head, item, count, sideHead, sideItem, sideCount,
        wordEmit, wordWriteEntry, wordStride, wordMergeSize, ptrReg, scalarReg, fieldAddr]
        at hpos hl hr hroom' ⊢ <;> omega

private def wordMergeReadFrame (x y : WordData) : Prop :=
  ∀ i, i ≠ fieldAddr → i ≠ ptrReg lkey → i ≠ ptrReg rkey →
    i ≠ scalarReg lvalue → i ≠ scalarReg rvalue → y.regs i = x.regs i

private theorem wordMergeReadFrame.room {limit : ℕ} {x y : WordData}
    (h : wordMergeReadFrame x y) (hx : WordMergeRoom limit x) : WordMergeRoom limit y := by
  have hleft : y.regs (ptrReg left) = x.regs (ptrReg left) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hright : y.regs (ptrReg right) = x.regs (ptrReg right) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : y.regs (ptrReg out) = x.regs (ptrReg out) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hl : y.regs (scalarReg lcount) = x.regs (scalarReg lcount) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr : y.regs (scalarReg rcount) = x.regs (scalarReg rcount) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_,
    (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.zero_eq,
    (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.one_eq,
    (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.two_eq⟩
  · simpa only [hleft, hl] using hx.left_room
  · simpa only [hright, hr] using hx.right_room
  · simpa only [wordMergeSize, hout, hl, hr] using hx.out_room

private theorem wordMergeReadFrame.left_count {x y : WordData} (h : wordMergeReadFrame x y) :
    y.regs (scalarReg lcount) = x.regs (scalarReg lcount) :=
  h _ (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem wordMergeReadFrame.right_count {x y : WordData} (h : wordMergeReadFrame x y) :
    y.regs (scalarReg rcount) = x.regs (scalarReg rcount) :=
  h _ (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem wordMergeReadFrame.size {x y : WordData} (h : wordMergeReadFrame x y) :
    wordMergeSize y = wordMergeSize x := by
  simp only [wordMergeSize, h.left_count, h.right_count]

private theorem wordMergeReadFrame.frame {x y : WordData} (h : wordMergeReadFrame x y) :
    WordMergeFrame x y := by
  have hr : y.regs (ptrReg right) = x.regs (ptrReg right) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have ho : y.regs (ptrReg out) = x.regs (ptrReg out) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨by rw [hr, h.right_count], by rw [ho, h.size], by rw [h.left_count]; exact id, ?_⟩
  intro i hi
  have good : ∀ j ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
      scalarReg remain} : Finset (Fin 20)), j ≠ fieldAddr ∧ j ≠ ptrReg lkey ∧
      j ≠ ptrReg rkey ∧ j ≠ scalarReg lvalue ∧ j ≠ scalarReg rvalue := by decide
  obtain ⟨a, b, c, d, e⟩ := good i hi
  exact h i a b c d e

private theorem wordMergeStep_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hl : 0 < x.regs (scalarReg lcount)) :
    ∃ y, wordWithin w (lowerWordCode mergeStep) x y 16 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y := by
  let a := wordLoadRef x lkey left
  have ha := wordLoadRef_exec x lkey left hx.one_eq
    (hfit.of_le (by have := hx.left_room; omega))
  have haf : wordMergeReadFrame x a := by
    intro i h₁ h₂ _ _ _
    simp [a, wordLoadRef, Function.update_of_ne h₁, Function.update_of_ne h₂]
  have haroom := haf.room hx
  let t := Cond.lt (scalarReg zero) (scalarReg rcount)
  by_cases hr : 0 < x.regs (scalarReg rcount)
  · have ht : t.Holds a := by
      change a.regs (scalarReg zero) < a.regs (scalarReg rcount)
      rwa [haroom.zero_eq, haf.right_count]
    let b := wordLoadRef a rkey right
    let c := b.set (scalarReg lvalue) (b.mem (b.regs (ptrReg lkey)))
    let d := c.set (scalarReg rvalue) (c.mem (c.regs (ptrReg rkey)))
    have hb := wordLoadRef_exec a rkey right haroom.one_eq
      (hfit.of_le (by have := haroom.right_room; rw [haf.right_count] at this; omega))
    have hc : wordWithin w (wordOp (.load (scalarReg lvalue) (ptrReg lkey))) b c 1 :=
      wordPrimitive rfl
    have hd : wordWithin w (wordOp (.load (scalarReg rvalue) (ptrReg rkey))) c d 1 :=
      wordPrimitive rfl
    have hdf : wordMergeReadFrame x d := by
      intro i h₁ h₂ h₃ h₄ h₅
      simp [d, c, b, wordLoadRef, Function.update_of_ne h₁, Function.update_of_ne h₃,
        Function.update_of_ne h₄, Function.update_of_ne h₅, haf i h₁ h₂ h₃ h₄ h₅]
    have hcompare : wordWithin w (lowerWordCode compareHeads) a d 4 :=
      hb.seq (hc.seq hd)
    let cmp := Cond.lt (scalarReg rvalue) (scalarReg lvalue)
    by_cases hcmp : cmp.Holds d
    · obtain ⟨y, hy, hyr, hs, hf⟩ := wordEmit_room true hfit (hdf.room hx)
        (by simpa only [sideCount, ite_true, hdf.right_count] using hr)
      have hbranch := Cslib.Program.ExecWithin.branch_pos (t := cmp)
        (neg := lowerWordCode (emit left lkey lcount)) hcmp hy
      refine ⟨y, ?_, hyr, hs.trans hdf.size, hdf.frame.trans hf⟩
      exact (ha.seq (Cslib.Program.ExecWithin.branch_pos (t := t)
        (neg := lowerWordCode (emit left lkey lcount)) ht (hcompare.seq hbranch))).mono
        (show 15 ≤ 16 by decide)
    · obtain ⟨y, hy, hyr, hs, hf⟩ := wordEmit_room false hfit (hdf.room hx)
        (by simpa only [sideCount, Bool.false_eq_true, ite_false, hdf.left_count] using hl)
      have hbranch := Cslib.Program.ExecWithin.branch_neg (t := cmp)
        (pos := lowerWordCode (emit right rkey rcount)) hcmp hy
      refine ⟨y, ?_, hyr, hs.trans hdf.size, hdf.frame.trans hf⟩
      have houter := Cslib.Program.ExecWithin.branch_pos (t := t)
        (neg := lowerWordCode (emit left lkey lcount)) ht (hcompare.seq hbranch)
      exact ha.seq houter
  · have ht : ¬t.Holds a := by
      change ¬a.regs (scalarReg zero) < a.regs (scalarReg rcount)
      rwa [haroom.zero_eq, haf.right_count]
    obtain ⟨y, hy, hyr, hs, hf⟩ := wordEmit_room false hfit haroom
      (by simpa only [sideCount, Bool.false_eq_true, ite_false, haf.left_count] using hl)
    have hbranch := Cslib.Program.ExecWithin.branch_neg (t := t)
      (pos := lowerWordCode (compareHeads ▷
        .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount))) ht hy
    exact ⟨y, (ha.seq hbranch).mono (show 11 ≤ 16 by decide), hyr, hs.trans haf.size,
      haf.frame.trans hf⟩

private theorem wordDrainRight_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hr : 0 < x.regs (scalarReg rcount)) :
    ∃ y, wordWithin w (lowerWordCode drainRight) x y 16 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y := by
  let a := wordLoadRef x rkey right
  have ha := wordLoadRef_exec x rkey right hx.one_eq
    (hfit.of_le (by have := hx.right_room; omega))
  have hf : wordMergeReadFrame x a := by
    intro i h₁ _ h₃ _ _
    simp [a, wordLoadRef, Function.update_of_ne h₁, Function.update_of_ne h₃]
  obtain ⟨y, he, hy, hs, hg⟩ := wordEmit_room true hfit (hf.room hx)
    (by simpa only [sideCount, ite_true, hf.right_count] using hr)
  exact ⟨y, (ha.seq he).mono (show 9 ≤ 16 by decide), hy, hs.trans hf.size, hf.frame.trans hg⟩

private theorem wordMergeLoop_exec {w limit : ℕ} (counter : Fin 11) (body : FlatCode)
    (step : ∀ x, WordMergeRoom limit x → 0 < x.regs (scalarReg counter) →
      ∃ y, wordWithin w body x y 16 ∧ WordMergeRoom limit y ∧
        wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y)
    (x : WordData) (hx : WordMergeRoom limit x) :
    ∃ y t, wordWithin w (.loopUntil (.lt (scalarReg counter) (scalarReg one)) body) x y t ∧
      WordMergeRoom limit y ∧ y.regs (scalarReg counter) = 0 ∧
      t + 18 * wordMergeSize y ≤ 18 * wordMergeSize x + 1 ∧ WordMergeFrame x y := by
  induction hn : wordMergeSize x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    let cond := Cond.lt (scalarReg counter) (scalarReg one)
    by_cases hzero : x.regs (scalarReg counter) = 0
    · have ht : cond.Holds x := by
        change x.regs (scalarReg counter) < x.regs (scalarReg one)
        rw [hzero, hx.one_eq]
        decide
      exact ⟨x, 1, Cslib.Program.ExecWithin.loopUntil_exit
        (I := Cslib.WordRAM.instructionSet w .standard 20) (body := body) (t := cond) ht,
        hx, hzero, by omega, WordMergeFrame.refl x⟩
    · have hpos := Nat.pos_of_ne_zero hzero
      have ht : ¬cond.Holds x := by
        change ¬x.regs (scalarReg counter) < x.regs (scalarReg one)
        rw [hx.one_eq]
        exact Nat.not_lt_of_ge hpos
      obtain ⟨y, he, hy, hsmall, hxy⟩ := step x hx hpos
      obtain ⟨z, t, hz, hroom, hstop, htime, hyz⟩ := ih (wordMergeSize y)
        (by omega) y hy rfl
      refine ⟨z, 16 + t + 2, Cslib.Program.ExecWithin.loopUntil_iter (t := cond) ht he hz,
        hroom, hstop, ?_, hxy.trans hyz⟩
      omega

private theorem wordMergeLoops_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x) :
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less lcount one) mergeStep ▷
      .loopUntil (less rcount one) drainRight)) x y (18 * wordMergeSize x + 2) ∧
      WordMergeRoom limit y ∧ wordMergeSize y = 0 ∧ WordMergeFrame x y := by
  obtain ⟨y, t₁, hy, hyroom, hyleft, ht₁, hxy⟩ :=
    wordMergeLoop_exec lcount (lowerWordCode mergeStep)
      (fun _ hs hpos => wordMergeStep_exec hfit hs hpos) x hx
  obtain ⟨z, t₂, hz, hzroom, hzright, ht₂, hyz⟩ :=
    wordMergeLoop_exec rcount (lowerWordCode drainRight)
      (fun _ hs hpos => wordDrainRight_exec hfit hs hpos) y hyroom
  exact ⟨z, (hy.seq hz).mono (by omega), hzroom,
    by simp [wordMergeSize, hyz.left_zero hyleft, hzright], hxy.trans hyz⟩

private def wordTakeRun (x : WordData) (count : Fin 11) : WordData :=
  let k := min (x.regs (scalarReg remain)) (x.regs (scalarReg width))
  (x.set (scalarReg count) k).set (scalarReg remain) (x.regs (scalarReg remain) - k)

private theorem wordTakeRun_exec {w : ℕ} (x : WordData) (count : Fin 11)
    (hc : scalarReg remain ≠ scalarReg count)
    (hfit : Fits w (x.regs (scalarReg remain))) :
    wordWithin w (lowerWordCode (takeRun count)) x (wordTakeRun x count) 4 := by
  let r := x.regs (scalarReg remain)
  let k := min r (x.regs (scalarReg width))
  let a := x.set (scalarReg count) k
  let t := Cond.lt (scalarReg remain) (scalarReg width)
  let cp := wordOp (.copy (scalarReg count) (scalarReg remain))
  let cn := wordOp (.copy (scalarReg count) (scalarReg width))
  have hs : wordWithin w (wordOp (.bin .sub (scalarReg remain) (scalarReg remain)
      (scalarReg count))) a (wordTakeRun x count) 1 := by
    apply wordPrimitive
    rw [Op.eval_bin]
    have hr : a.regs (scalarReg remain) = r := Function.update_of_ne hc _ _
    have hk : a.regs (scalarReg count) = k := by simp [a]
    rw [hr, hk]
    exact Data.put_of_fits (hfit.of_le (Nat.sub_le _ _))
  have hb : wordWithin w (.branch t cp cn) x a 3 := by
    by_cases ht : r < x.regs (scalarReg width)
    · have hmin : k = r := min_eq_left ht.le
      have hcopy : wordWithin w cp x a 1 := by
        apply wordPrimitive
        rw [Op.eval_copy]
        simp only [a, hmin]
        rfl
      have h := Cslib.Program.ExecWithin.branch_pos (t := t) (neg := cn) ht hcopy
      exact h.mono (by decide)
    · have hmin : k = x.regs (scalarReg width) := min_eq_right (Nat.le_of_not_gt ht)
      have hcopy : wordWithin w cn x a 1 := by
        apply wordPrimitive
        rw [Op.eval_copy]
        simp only [a, hmin]
      exact Cslib.Program.ExecWithin.branch_neg (t := t) (pos := cp) ht hcopy
  exact hb.seq hs

private theorem wordWalk_exec {w limit : ℕ} (x : WordData)
    (hfit : Fits w limit) (hone : x.regs (scalarReg one) = 1)
    (htwo : x.regs (scalarReg two) = 2)
    (hroom : x.regs (ptrReg right) + 2 * x.regs (scalarReg walk) ≤ limit) :
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less walk one) (next right ▷ dec walk)))
        x y (4 * x.regs (scalarReg walk) + 1) ∧
      y.regs (ptrReg right) = x.regs (ptrReg right) + 2 * x.regs (scalarReg walk) ∧
      ∀ i, i ≠ ptrReg right → i ≠ scalarReg walk → y.regs i = x.regs i := by
  let endpoint := x.regs (ptrReg right) + 2 * x.regs (scalarReg walk)
  let P (s : WordData) := s.regs (ptrReg right) + 2 * s.regs (scalarReg walk) = endpoint ∧
    ∀ i, i ≠ ptrReg right → i ≠ scalarReg walk → s.regs i = x.regs i
  let t := Cond.lt (scalarReg walk) (scalarReg one)
  let body := lowerWordCode (next right ▷ dec walk)
  have hs (s : WordData) (h : P s) (ht : ¬t.Holds s) :
      ∃ y, wordWithin w body s y 2 ∧ P y ∧
        y.regs (scalarReg walk) < s.regs (scalarReg walk) := by
    have h₁ := (h.2 _ (by decide : scalarReg one ≠ ptrReg right) (by decide)).trans hone
    have h₂ := (h.2 _ (by decide : scalarReg two ≠ ptrReg right) (by decide)).trans htwo
    change ¬s.regs (scalarReg walk) < s.regs (scalarReg one) at ht
    rw [h₁] at ht
    let r := s.regs (ptrReg right)
    let k := s.regs (scalarReg walk)
    let a := s.set (ptrReg right) (r + 2)
    let y := a.set (scalarReg walk) (k - 1)
    have hbound : r + 2 * k ≤ limit := h.1.le.trans hroom
    have ha : wordWithin w (wordOp (.bin .add (ptrReg right) (ptrReg right)
        (scalarReg two))) s a 1 := by
      apply wordPrimitive
      rw [Op.eval_bin, h₂]
      exact Data.put_of_fits (hfit.of_le (by change r + 2 ≤ limit; omega))
    have hb : wordWithin w (wordOp (.bin .sub (scalarReg walk) (scalarReg walk)
        (scalarReg one))) a y 1 := by
      apply wordPrimitive
      rw [Op.eval_bin]
      have hk : a.regs (scalarReg walk) = k :=
        Function.update_of_ne (by decide : scalarReg walk ≠ ptrReg right) (r + 2) s.regs
      have ho : a.regs (scalarReg one) = 1 :=
        (show a.regs (scalarReg one) = s.regs (scalarReg one) from
          Function.update_of_ne (by decide : scalarReg one ≠ ptrReg right) (r + 2) s.regs).trans h₁
      rw [hk, ho]
      exact Data.put_of_fits (hfit.of_le (by change k - 1 ≤ limit; omega))
    have hright : y.regs (ptrReg right) = r + 2 := by
      simp [y, a, Function.update_of_ne (by decide : ptrReg right ≠ scalarReg walk)]
    have hwalk : y.regs (scalarReg walk) = k - 1 := by simp [y]
    refine ⟨y, ha.seq hb, ⟨?_, ?_⟩, ?_⟩
    · rw [hright, hwalk, ← h.1]
      change r + 2 + 2 * (k - 1) = r + 2 * k
      omega
    · intro i hi hj
      simp [y, a, Function.update_of_ne hi, Function.update_of_ne hj, h.2 i hi hj]
    · rw [hwalk]
      change k - 1 < k
      omega
  obtain ⟨y, hy, hf, ht⟩ := Cslib.Program.ExecWithin.loopUntil_invariant
    (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t)
    P (fun s => s.regs (scalarReg walk)) hs (show P x from ⟨rfl, fun _ _ _ => rfl⟩)
  change y.regs (scalarReg walk) < y.regs (scalarReg one) at ht
  rw [(hf.2 _ (by decide : scalarReg one ≠ ptrReg right) (by decide)).trans hone] at ht
  have hzero : y.regs (scalarReg walk) = 0 := Nat.lt_one_iff.mp ht
  exact ⟨y, hy.mono (by omega), by simpa only [hzero, Nat.mul_zero, Nat.add_zero] using hf.1,
    hf.2⟩

private structure WordPassRoom (limit : ℕ) (x : WordData) : Prop where
  left_room : x.regs (ptrReg left) + 2 * x.regs (scalarReg remain) ≤ limit
  out_room : x.regs (ptrReg out) + 2 * x.regs (scalarReg remain) ≤ limit
  zero_eq : x.regs (scalarReg zero) = 0
  one_eq : x.regs (scalarReg one) = 1
  two_eq : x.regs (scalarReg two) = 2

private def wordPassFrame (x y : WordData) : Prop :=
  ∀ i ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width} : Finset (Fin 20)),
    y.regs i = x.regs i

private theorem wordMergePair_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordPassRoom limit x) :
    ∃ y, wordWithin w (lowerWordCode mergePair) x y
        (22 * min (x.regs (scalarReg remain)) (2 * x.regs (scalarReg width)) + 14) ∧
      WordPassRoom limit y ∧ wordPassFrame x y ∧
      y.regs (scalarReg remain) = x.regs (scalarReg remain) - 2 * x.regs (scalarReg width) := by
  let r := x.regs (scalarReg remain)
  let widthVal := x.regs (scalarReg width)
  let l := min r widthVal
  let b := min (r - l) widthVal
  let a₁ := wordTakeRun x lcount
  let a₂ := wordTakeRun a₁ rcount
  let a₃ := a₂.set (ptrReg right) (a₂.regs (ptrReg left))
  let a₄ := a₃.set (scalarReg walk) (a₃.regs (scalarReg lcount))
  have hleftroom := hx.left_room
  have houtroom := hx.out_room
  have haRem : a₁.regs (scalarReg remain) = r - l := by simp [a₁, wordTakeRun, r, l, widthVal]
  have haWidth : a₁.regs (scalarReg width) = widthVal := by
    simp [a₁, wordTakeRun, scalarReg, width, remain, lcount, widthVal]
  have hbReg : a₂.regs (scalarReg rcount) = b := by
    change ((a₁.set (scalarReg rcount) _).set (scalarReg remain) _).regs (scalarReg rcount) = b
    rw [Cslib.WordRAM.Data.set_regs, Function.update_of_ne (by decide :
      scalarReg rcount ≠ scalarReg remain), Cslib.WordRAM.Data.set_regs, Function.update_self]
    rw [haRem, haWidth]
  have hbRem : a₂.regs (scalarReg remain) = r - l - b := by
    simp [a₂, wordTakeRun, haRem, haWidth, b]
  have hbFrame (i : Fin 20) (hi : i ≠ scalarReg remain) (hl : i ≠ scalarReg lcount)
      (hr : i ≠ scalarReg rcount) : a₂.regs i = x.regs i := by
    simp [a₂, a₁, wordTakeRun, Function.update_of_ne hi, Function.update_of_ne hl,
      Function.update_of_ne hr]
  have ha₁ := wordTakeRun_exec x lcount (by decide) (hfit.of_le (by change r ≤ _; omega))
  have ha₂ := wordTakeRun_exec a₁ rcount (by decide) (hfit.of_le (by rw [haRem]; omega))
  have ha₃ : wordWithin w (lowerWordCode (copyRef right left)) a₂ a₃ 1 := wordPrimitive rfl
  have ha₄ : wordWithin w (lowerWordCode (copyScalar walk lcount)) a₃ a₄ 1 := wordPrimitive rfl
  have hdFrame (i : Fin 20) (hi : i ≠ ptrReg right) (hw : i ≠ scalarReg walk) :
      a₄.regs i = a₂.regs i := by
    simp [a₄, a₃, Function.update_of_ne hi, Function.update_of_ne hw]
  have hdL : a₄.regs (scalarReg lcount) = l := by
    rw [hdFrame _ (by decide) (by decide)]
    simp [a₂, a₁, wordTakeRun, r, l, widthVal, scalarReg, remain, lcount, rcount]
  have hdR : a₄.regs (ptrReg right) = x.regs (ptrReg left) := by
    have h : a₄.regs (ptrReg right) = a₂.regs (ptrReg left) := by
      simp [a₄, a₃, ptrReg, right, scalarReg, walk]
    exact h.trans (hbFrame _ (by decide) (by decide) (by decide))
  have hdWalk : a₄.regs (scalarReg walk) = l := by
    rw [← hdL]
    simp [a₄, scalarReg, walk, lcount]
  have same (i : Fin 20) (h₁ : i ≠ ptrReg right) (h₂ : i ≠ scalarReg walk)
      (h₃ : i ≠ scalarReg remain) (h₄ : i ≠ scalarReg lcount) (h₅ : i ≠ scalarReg rcount) :
      a₄.regs i = x.regs i :=
    (hdFrame i h₁ h₂).trans (hbFrame i h₃ h₄ h₅)
  have hlr : l + b = min r (2 * widthVal) := by
    dsimp [l, b]
    omega
  obtain ⟨e, he, heR, hef⟩ := wordWalk_exec a₄ hfit
    ((same _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.one_eq)
    ((same _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.two_eq)
    (by rw [hdR, hdWalk]; omega)
  rw [hdR, hdWalk] at heR
  have heq (i : Fin 20) (hi : i ≠ ptrReg right) (hw : i ≠ scalarReg walk) :
      e.regs i = a₂.regs i := (hef i hi hw).trans (hdFrame i hi hw)
  have held : e.regs (ptrReg left) = x.regs (ptrReg left) :=
    (heq _ (by decide) (by decide)).trans (hbFrame _ (by decide) (by decide) (by decide))
  have heout : e.regs (ptrReg out) = x.regs (ptrReg out) :=
    (heq _ (by decide) (by decide)).trans (hbFrame _ (by decide) (by decide) (by decide))
  have hel : e.regs (scalarReg lcount) = l := (hef _ (by decide) (by decide)).trans hdL
  have herb : e.regs (scalarReg rcount) = b := (heq _ (by decide) (by decide)).trans hbReg
  have hsize : wordMergeSize e = l + b := by rw [wordMergeSize, hel, herb]
  have heFrame (i : Fin 20) (h₁ : i ≠ ptrReg right) (h₂ : i ≠ scalarReg walk)
      (h₃ : i ≠ scalarReg remain) (h₄ : i ≠ scalarReg lcount) (h₅ : i ≠ scalarReg rcount) :
      e.regs i = x.regs i := (heq i h₁ h₂).trans (hbFrame i h₃ h₄ h₅)
  have heRoom : WordMergeRoom limit e := by
    refine ⟨by rw [held, hel]; omega, by rw [heR, herb]; omega,
      by rw [heout, hsize]; omega, ?_, ?_, ?_⟩
    · exact (heFrame _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.zero_eq
    · exact (heFrame _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.one_eq
    · exact (heFrame _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx.two_eq
  obtain ⟨f, hf, hfRoom, hfsize, hff⟩ := wordMergeLoops_exec hfit heRoom
  let y := f.set (ptrReg left) (f.regs (ptrReg right))
  have hy : wordWithin w (lowerWordCode (copyRef left right)) f y 1 := wordPrimitive rfl
  have hyR : y.regs (scalarReg remain) = r - l - b := by
    have eq : y.regs (scalarReg remain) = f.regs (scalarReg remain) :=
      Function.update_of_ne (by decide : scalarReg remain ≠ ptrReg left)
        (f.regs (ptrReg right)) f.regs
    exact eq.trans ((hff.fixed _ (by decide)).trans ((heq _ (by decide) (by decide)).trans hbRem))
  have hyL : y.regs (ptrReg left) = x.regs (ptrReg left) + 2 * (l + b) := by
    have hr0 : f.regs (scalarReg rcount) = 0 := by unfold wordMergeSize at hfsize; omega
    have hr := hff.right_end
    rw [hr0, heR, herb] at hr
    change y.regs (ptrReg left) = _
    rw [show y.regs (ptrReg left) = f.regs (ptrReg right) by simp [y]]
    omega
  have hyO : y.regs (ptrReg out) = x.regs (ptrReg out) + 2 * (l + b) := by
    have ho := hff.out_end
    rw [hfsize, heout, hsize] at ho
    have eq : y.regs (ptrReg out) = f.regs (ptrReg out) :=
      Function.update_of_ne (by decide : ptrReg out ≠ ptrReg left) (f.regs (ptrReg right)) f.regs
    rw [eq]
    omega
  have hframe (i : Fin 20) (hi : i ≠ ptrReg left) : y.regs i = f.regs i :=
    Function.update_of_ne hi _ _
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · apply (ha₁.seq (ha₂.seq (ha₃.seq (ha₄.seq (he.seq ((hf.seq hy))))))).mono
    rw [hdWalk, hsize, ← hlr]
    omega
  · rw [hyL, hyR]
    omega
  · rw [hyO, hyR]
    omega
  · exact (hframe _ (by decide)).trans hfRoom.zero_eq
  · exact (hframe _ (by decide)).trans hfRoom.one_eq
  · exact (hframe _ (by decide)).trans hfRoom.two_eq
  · intro i hi
    have good : ∀ j ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width} : Finset (Fin 20)),
        j ≠ ptrReg left ∧ j ≠ ptrReg right ∧ j ≠ scalarReg walk ∧
        j ≠ scalarReg remain ∧ j ≠ scalarReg lcount ∧ j ≠ scalarReg rcount := by decide
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := good i hi
    have hm : i ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
        scalarReg remain} : Finset (Fin 20)) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (show i = ptrReg src ∨ i = ptrReg dst ∨ i = scalarReg len ∨
          i = scalarReg width ∨ i = scalarReg remain from by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            tauto)
    exact (hframe i h₁).trans ((hff.fixed i hm).trans (heFrame i h₂ h₃ h₄ h₅ h₆))
  · rw [hyR, Nat.sub_sub, hlr]
    omega

private theorem wordPassLoop_exec {w limit : ℕ} (x : WordData)
    (hfit : Fits w limit) (hx : WordPassRoom limit x) (hw : 0 < x.regs (scalarReg width)) :
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less remain one) mergePair)) x y
        (22 * x.regs (scalarReg remain) +
          16 * pairs (x.regs (scalarReg remain)) (x.regs (scalarReg width)) + 1) ∧
      WordPassRoom limit y ∧ wordPassFrame x y := by
  let W := x.regs (scalarReg width)
  let P (s : WordData) := WordPassRoom limit s ∧ wordPassFrame x s
  let pot (s : WordData) :=
    22 * s.regs (scalarReg remain) + 16 * pairs (s.regs (scalarReg remain)) W
  let t := Cond.lt (scalarReg remain) (scalarReg one)
  have step (s : WordData) (h : P s) (ht : ¬t.Holds s) :
      ∃ y c, wordWithin w (lowerWordCode mergePair) s y c ∧ P y ∧ c + 2 + pot y ≤ pot s := by
    have hsW : s.regs (scalarReg width) = W := h.2 _ (by decide)
    change ¬s.regs (scalarReg remain) < s.regs (scalarReg one) at ht
    rw [h.1.one_eq] at ht
    obtain ⟨y, he, hroom, hframe, hrem⟩ := wordMergePair_exec hfit h.1
    refine ⟨y, _, he, ⟨hroom, fun i hi => (hframe i hi).trans (h.2 i hi)⟩, ?_⟩
    have hpair := pairs_step (w := W) (Nat.le_of_not_gt ht) hw
    dsimp only [pot]
    rw [hsW, hrem, hsW, hpair]
    omega
  obtain ⟨y, hy, hframe, _⟩ := Cslib.Program.ExecWithin.loopUntil_potential
    (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t)
    P pot step (show P x from ⟨hx, fun _ _ => rfl⟩)
  exact ⟨y, hy, hframe.1, hframe.2⟩

private structure WordPassState (n : ℕ) (x : WordData) : Prop where
  source_bound : x.regs (ptrReg src) ≤ 3 * n
  dest_bound : x.regs (ptrReg dst) ≤ 3 * n
  len_eq : x.regs (scalarReg len) = n
  zero_eq : x.regs (scalarReg zero) = 0
  one_eq : x.regs (scalarReg one) = 1
  two_eq : x.regs (scalarReg two) = 2

private theorem wordPass_exec {w n : ℕ} {x : WordData}
    (hfit : Fits w (5 * n + 2)) (hx : WordPassState n x)
    (hw : 0 < x.regs (scalarReg width)) (hwn : x.regs (scalarReg width) < n) :
    ∃ y, wordWithin w (lowerWordCode mergePass) x y
        (22 * n + 16 * pairs n (x.regs (scalarReg width)) + 8) ∧
      WordPassState n y ∧ y.regs (scalarReg width) = x.regs (scalarReg width) * 2 := by
  let a := x.set (scalarReg remain) n
  let b := a.set (ptrReg left) (x.regs (ptrReg src))
  let c := b.set (ptrReg out) (x.regs (ptrReg dst))
  have ha : wordWithin w (lowerWordCode (copyScalar remain len)) x a 1 := by
    apply wordPrimitive
    rw [Op.eval_copy, hx.len_eq]
  have hb : wordWithin w (lowerWordCode (copyRef left src)) a b 1 := wordPrimitive (by
    rw [Op.eval_copy]
    have hs : a.regs (ptrReg src) = x.regs (ptrReg src) :=
      Function.update_of_ne (by decide : ptrReg src ≠ scalarReg remain) n x.regs
    rw [hs])
  have hc : wordWithin w (lowerWordCode (copyRef out dst)) b c 1 := wordPrimitive (by
    simp [a, b, c, scalarReg, ptrReg, remain, left, dst])
  have hcrem : c.regs (scalarReg remain) = n := by
    simp [c, b, a, scalarReg, ptrReg, remain, out, left]
  have hframe (i : Fin 20) (h₁ : i ≠ ptrReg out) (h₂ : i ≠ ptrReg left)
      (h₃ : i ≠ scalarReg remain) : c.regs i = x.regs i := by
    simp [c, b, a, Function.update_of_ne h₁, Function.update_of_ne h₂, Function.update_of_ne h₃]
  have hcleft : c.regs (ptrReg left) = x.regs (ptrReg src) := by
    simp [c, b, ptrReg, out, left]
  have hcout : c.regs (ptrReg out) = x.regs (ptrReg dst) := by simp [c]
  have hcwidth := hframe (scalarReg width) (by decide) (by decide) (by decide)
  have hroom : WordPassRoom (5 * n + 2) c := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcleft, hcrem]
      have := hx.source_bound
      omega
    · rw [hcout, hcrem]
      have := hx.dest_bound
      omega
    · exact (hframe _ (by decide) (by decide) (by decide)).trans hx.zero_eq
    · exact (hframe _ (by decide) (by decide) (by decide)).trans hx.one_eq
    · exact (hframe _ (by decide) (by decide) (by decide)).trans hx.two_eq
  obtain ⟨d, hd, hdr, hdf⟩ := wordPassLoop_exec c hfit hroom (by rw [hcwidth]; exact hw)
  have dd (i : Fin 20) (hi : i ∈ ({ptrReg src, ptrReg dst, scalarReg len,
      scalarReg width} : Finset (Fin 20))) : d.regs i = x.regs i := by
    have check : ∀ j ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width} : Finset (Fin 20)),
        j ≠ ptrReg out ∧ j ≠ ptrReg left ∧ j ≠ scalarReg remain := by decide
    have ⟨h₁, h₂, h₃⟩ := check i hi
    exact (hdf i hi).trans (hframe i h₁ h₂ h₃)
  let e := d.set (ptrReg left) (d.regs (ptrReg src))
  let f := e.set (ptrReg src) (d.regs (ptrReg dst))
  let g := f.set (ptrReg dst) (d.regs (ptrReg src))
  let y := g.set (scalarReg width) (x.regs (scalarReg width) * 2)
  have he : wordWithin w (lowerWordCode (copyRef left src)) d e 1 := wordPrimitive rfl
  have hf : wordWithin w (lowerWordCode (copyRef src dst)) e f 1 := wordPrimitive (by
    simp [e, f, ptrReg, left, dst])
  have hg : wordWithin w (lowerWordCode (copyRef dst left)) f g 1 := wordPrimitive (by
    rw [Op.eval_copy]
    have he' : f.regs (ptrReg left) = d.regs (ptrReg src) := by
      simp [f, e, Function.update_of_ne (by decide : ptrReg left ≠ ptrReg src)]
    rw [he'])
  have hswap : wordWithin w (lowerWordCode swapBuffers) d g 3 := he.seq (hf.seq hg)
  have hgf (i : Fin 20) (h₁ : i ≠ ptrReg left) (h₂ : i ≠ ptrReg src) (h₃ : i ≠ ptrReg dst) :
      g.regs i = d.regs i := by
    simp [g, f, e, Function.update_of_ne h₁, Function.update_of_ne h₂, Function.update_of_ne h₃]
  have hwidth := (hgf (scalarReg width) (by decide) (by decide) (by decide)).trans
    (dd (scalarReg width) (by decide))
  have hwiden : wordWithin w (lowerWordCode doubleWidth) g y 1 := by
    apply wordPrimitive
    rw [Op.eval_bin, hwidth]
    change g.put w (scalarReg width)
      (x.regs (scalarReg width) + x.regs (scalarReg width)) = some y
    rw [← Nat.mul_two]
    exact Data.put_of_fits (hfit.of_le (by omega))
  have hsource : y.regs (ptrReg src) = x.regs (ptrReg dst) := by
    have eq : y.regs (ptrReg src) = d.regs (ptrReg dst) := by
      simp [y, g, f, Function.update_of_ne (by decide : ptrReg src ≠ scalarReg width),
        Function.update_of_ne (by decide : ptrReg src ≠ ptrReg dst)]
    exact eq.trans (dd _ (by decide))
  have hdest : y.regs (ptrReg dst) = x.regs (ptrReg src) := by
    have eq : y.regs (ptrReg dst) = d.regs (ptrReg src) := by
      simp [y, g, ptrReg, scalarReg, dst, width]
    exact eq.trans (dd _ (by decide))
  have hyframe (i : Fin 20) (h₁ : i ≠ ptrReg left) (h₂ : i ≠ ptrReg src) (h₃ : i ≠ ptrReg dst)
      (h₄ : i ≠ scalarReg width) : y.regs i = d.regs i :=
    (show y.regs i = g.regs i from Function.update_of_ne h₄ _ _).trans (hgf i h₁ h₂ h₃)
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have run := ha.seq (hb.seq (hc.seq (hd.seq (hswap.seq hwiden))))
    rw [hcrem, hcwidth] at run
    exact run.mono (by omega)
  · rw [hsource]
    exact hx.dest_bound
  · rw [hdest]
    exact hx.source_bound
  · exact (hyframe _ (by decide) (by decide) (by decide) (by decide)).trans
      ((dd _ (by decide)).trans hx.len_eq)
  · exact (hyframe _ (by decide) (by decide) (by decide) (by decide)).trans hdr.zero_eq
  · exact (hyframe _ (by decide) (by decide) (by decide) (by decide)).trans hdr.one_eq
  · exact (hyframe _ (by decide) (by decide) (by decide) (by decide)).trans hdr.two_eq
  · simp [y]

private theorem wordOuter_exec {w n k : ℕ} {x : WordData}
    (hfit : Fits w (5 * n + 2)) (hx : WordPassState n x)
    (hw : x.regs (scalarReg width) = 2 ^ k) :
    ∃ y, wordWithin w (lowerWordCode (.loop (less width len) mergePass)) x y
      (outerBudget 22 n k) := by
  induction hd : Nat.clog 2 n - k using Nat.strong_induction_on generalizing k x with
  | _ d ih =>
    let t := Cond.lt (scalarReg width) (scalarReg len)
    have hreg : 0 < x.regs (scalarReg width) := by rw [hw]; positivity
    by_cases ht : t.Holds x
    · have hlt : (2 : ℕ) ^ k < n := by
        change x.regs (scalarReg width) < x.regs (scalarReg len) at ht
        rwa [hw, hx.len_eq] at ht
      have hk := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).2 hlt
      obtain ⟨y, hy, hyState, hyWidth⟩ := wordPass_exec hfit hx hreg (by rw [hw]; exact hlt)
      have hwidth : y.regs (scalarReg width) = (2 : ℕ) ^ (k + 1) := by
        rw [hyWidth, hw, pow_succ]
      have hsmall : Nat.clog 2 n - (k + 1) < d := by omega
      obtain ⟨z, hz⟩ := ih _ hsmall hyState hwidth rfl
      have hz' : wordWithin w (.loop t (lowerWordCode mergePass)) y z
          (outerBudget 22 n (k + 1)) := hz
      have he := Cslib.Program.ExecWithin.loop_iter (t := t) ht hy hz'
      rw [hw] at he
      have hbudget := outerBudget_step (p := 22) (Nat.zero_lt_of_lt hlt) hk
      exact ⟨z, he.mono (by omega)⟩
    · have he : wordWithin w (.loop t (lowerWordCode mergePass)) x x 2 :=
        Cslib.Program.ExecWithin.loop_exit
          (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t) ht
      exact ⟨x, he.mono (by unfold outerBudget; omega)⟩

private theorem wordCode_exec {w : ℕ} (keys : List ℕ) (hn : 3 ≤ keys.length)
    (hfit : Fits w (5 * keys.length + 2)) :
    ∃ y, wordWithin w (lowerWordCode code) (wordRAMInput keys).data y
      (22 * keys.length * Nat.clog 2 keys.length + 25 * keys.length +
        26 * Nat.clog 2 keys.length - 9) := by
  let n := keys.length
  let x := (wordRAMInput keys).data
  have ht : (Cond.lt (scalarReg two) (scalarReg len)).Holds x := show 2 < n from hn
  obtain ⟨a, ha, hinit⟩ := wordInitEntries_exec keys hfit
  let b := a.set (scalarReg width) 1
  have hb : wordWithin w (lowerWordCode (copyScalar width one)) a b 1 := by
    apply wordPrimitive
    rw [Op.eval_copy, hinit.one_eq]
  have frame (i : Fin 20) (hi : i ≠ scalarReg width) : b.regs i = a.regs i :=
    Function.update_of_ne hi _ _
  have hstate : WordPassState n b := by
    refine ⟨?_, ?_, (frame _ (by decide)).trans hinit.len_eq,
      (frame _ (by decide)).trans hinit.zero_eq, (frame _ (by decide)).trans hinit.one_eq,
      (frame _ (by decide)).trans hinit.two_eq⟩
    · rw [frame _ (by decide), hinit.source_eq]
      omega
    · rw [frame _ (by decide), hinit.dest_eq]
  have hw : b.regs (scalarReg width) = 2 ^ (0 : ℕ) := by simp [b]
  obtain ⟨y, hy⟩ := wordOuter_exec hfit hstate hw
  refine ⟨y, ?_⟩
  have he : wordWithin w (lowerWordCode code) x y
      (9 * n + 3 + (1 + outerBudget 22 n 0) + 1) := by
    unfold code lowerWordCode
    exact Cslib.Program.ExecWithin.branch_pos
      (t := Cond.lt (scalarReg two) (scalarReg len)) ht (ha.seq (hb.seq hy))
  apply he.mono
  change 9 * n + 3 + (1 + outerBudget 22 n 0) + 1 ≤
    22 * n * Nat.clog 2 n + 25 * n + 26 * Nat.clog 2 n - 9
  unfold outerBudget
  simp only [Nat.sub_zero, pow_zero, Nat.div_one, Nat.mul_add]
  rw [Nat.mul_comm (Nat.clog 2 n) (22 * n), Nat.mul_comm (Nat.clog 2 n) 26]
  change 3 ≤ n at hn
  omega

private theorem wordAssemble_width (c : FlatCode) (w pc : ℕ) :
    c.assemble (flatMachine w .standard 20) pc = c.assemble (flatMachine 0 .standard 20) pc := by
  induction c generalizing pc with
  | op o => rcases o with _ | ⟨_, _⟩ <;> rfl
  | _ => simp [Cslib.Program.Code.assemble, flatMachine, *]

/-- The direct word-RAM implementation halts from the prepared input within the stated
instruction count, including halt. The word must hold the addresses of the interleaved
buffers and the input keys. -/
theorem wordRAM_executes {w : ℕ} (keys : List ℕ) (hn : 3 ≤ keys.length)
    (hfit : Fits w (5 * keys.length + 2)) (_hkeys : ∀ k ∈ keys, Fits w k) :
    ∃ base t, Cslib.WordRAM.Executes w wordRAMProgram (wordRAMInput keys) base t ∧
      t ≤ 22 * keys.length * Nat.clog 2 keys.length + 25 * keys.length +
        26 * Nat.clog 2 keys.length - 8 := by
  obtain ⟨y, t, ht, he⟩ := wordCode_exec keys hn hfit
  let finish := (lowerWordCode code).size
  let z : Cslib.WordRAM.State 20 := ⟨finish, y⟩
  have run := he.runs (flatMachine w .standard 20) [] [.halt (ptrReg resultReg)]
  have hrun : Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) z t := by
    simp only [List.nil_append, List.length_nil, Nat.zero_add, wordAssemble_width] at run
    exact run.map (r' := Next w wordRAMProgram)
      (fun a : ℕ × WordData => (⟨a.1, a.2⟩ : Cslib.WordRAM.State 20)) (fun _ _ h => h)
  have hend : Cslib.WordRAM.step w wordRAMProgram z = .halt (y.regs (ptrReg resultReg)) := by
    apply step_halt
    let ops := (lowerWordCode code).assemble (flatMachine 0 .standard 20) 0
    have hlen : ops.length = finish := Cslib.Program.Code.length_assemble _ _ _
    change (ops ++ [.halt (ptrReg resultReg)])[finish]? = _
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  exact ⟨_, t + 1, ⟨z, t, hrun, hend, rfl⟩, by omega⟩

end WordRAM

end Cslib.Algorithms.WordRAM.MergeSort.LocalRef
