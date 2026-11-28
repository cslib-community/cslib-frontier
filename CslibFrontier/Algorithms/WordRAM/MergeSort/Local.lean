/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Algorithms.WordRAM.MergeSort
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

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
* `pointer_sorts` and `pointer_sorts_small`: stable permutation output on the packed
  pointer machine.
* `packed_backends_agree`: the two backends return the same numeric permutation.
* `wordRAM_sorts` and `wordRAM_sorts_small`: stable permutation output and instruction counts
  for the interleaved standard word-RAM program.
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

private def preparePair : SortCode :=
  takeRun lcount ▷ takeRun rcount ▷ copyRef right left ▷ copyScalar walk lcount ▷
    .loopUntil (less walk one) (next right ▷ dec walk)

private def mergePair : SortCode :=
  preparePair ▷ ((.loopUntil (less lcount one) mergeStep ▷
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

/-- Read the numeric output buffer of the compiled packed pointer-machine sorter. -/
def pointerPermutation (n : ℕ) (x : PointerMachine.State model (layout 8 11)) :
    List ℕ :=
  (x.ptr resultReg).elim [] fun base =>
    (List.range n).filterMap fun i => (x.heap[base + i]?).map fun cell => cell.data 0

/-- Pointer-machine readback agrees with local-memory readback on the encoded state. -/
theorem pointerPermutation_encode {n : ℕ} (x : Data model (3 * n) 8 11) (pc : ℕ) :
    pointerPermutation n { encode x with pc := pc } = permutation x := by
  have hptr : ({ encode x with pc := pc }).ptr resultReg =
      (x.addr resultReg).map Fin.val := encode_ptr x resultReg
  have hheap : ({ encode x with pc := pc }).heap = (encode x).heap := rfl
  unfold pointerPermutation permutation
  rw [hptr, hheap]
  cases hp : x.addr resultReg with
  | none => rfl
  | some base =>
    simp only [Option.map_some, Option.elim_some]
    apply List.filterMap_congr
    intro i _
    by_cases hi : base.val + i < 3 * n
    · have hh : base.val + i < (encode x).heap.length := by simpa using hi
      rw [dite_eq_left hi, List.getElem?_eq_getElem hh, Option.map_some]
      exact congrArg some (encode_heap_getElem_data x ⟨base.val + i, hi⟩ hh)
    · have hh : ¬base.val + i < (encode x).heap.length := by simpa using hi
      rw [dite_eq_right hi, List.getElem?_eq_none (Nat.le_of_not_gt hh), Option.map_none]

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

private def writeEntryState {cells : ℕ} (head item : Fin 8)
    (x : MachineState cells) : MachineState cells :=
  let a := (Op.storeData out lvalue).eval x
  let b := (Op.storeAddr out item).eval a
  let c := (Op.move .next out out).eval b
  (Op.move .next head head).eval c

private theorem writeEntry_runs {cells : ℕ} (head item : Fin 8) (x : MachineState cells) :
    within (writeEntry head item) x (writeEntryState head item x) 4 :=
  (primitive _ _).seq ((primitive _ _).seq ((primitive _ _).seq (primitive _ _)))

private theorem writeEntry_exec {cells : ℕ} (head item : Fin 8) (x : MachineState cells) :
    ∃ y, within (writeEntry head item) x y 4 ∧ y.scalars = x.scalars := by
  refine ⟨writeEntryState head item x, writeEntry_runs head item x, ?_⟩
  unfold writeEntryState
  rw [addrOp_scalars, addrOp_scalars]
  cases h : x.addr out <;> simp [Op.eval, h]

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

-- A null cursor at the end of the array denotes its one-past position.
private def localPos {cells : ℕ} (a : Option (Fin cells)) : ℕ :=
  a.elim cells Fin.val


private theorem localPos_le {cells : ℕ} (a : Option (Fin cells)) : localPos a ≤ cells := by
  cases a with
  | none => exact le_rfl
  | some a => exact a.isLt.le

private theorem localPos_move {cells : ℕ} (x : MachineState cells) (r : Fin 8) :
    localPos (((Op.move .next r r).eval x).addr r) = min (localPos (x.addr r) + 1) cells := by
  cases h : x.addr r with
  | none => simp [Op.eval, h, localPos]
  | some a =>
    by_cases ha : a.val + 1 < cells
    · simp [Op.eval, h, localPos, Direction.move, ha]
    · have ha' := a.isLt
      simp [Op.eval, h, localPos, Direction.move, ha]
      omega

private theorem walk_exec {cells : ℕ} (x : MachineState cells) (h₁ : x.scalars one = 1) :
    ∃ y, within (.loopUntil (less walk one) (next right ▷ dec walk))
      x y (4 * (x.scalars walk : ℕ) + 1) ∧
      (∀ i, i ≠ walk → y.scalars i = x.scalars i) ∧
      (∀ i, i ≠ right → y.addr i = x.addr i) ∧ y.values = x.values ∧ y.refs = x.refs ∧
      localPos (y.addr right) = min (localPos (x.addr right) + x.scalars walk) cells := by
  let endPos := min (localPos (x.addr right) + x.scalars walk) cells
  let P (z : MachineState cells) :=
    (∀ i, i ≠ walk → z.scalars i = x.scalars i) ∧
    (∀ i, i ≠ right → z.addr i = x.addr i) ∧ z.values = x.values ∧ z.refs = x.refs ∧
    min (localPos (z.addr right) + z.scalars walk) cells = endPos
  have hone (z : MachineState cells) (hz : P z) : z.scalars one = 1 :=
    (hz.1 one (by decide)).trans h₁
  have hs (z : MachineState cells) (hz : P z) (hp : 0 < z.scalars walk) :
      ∃ y, within (next right ▷ dec walk) z y 2 ∧ P y ∧
        y.scalars walk = z.scalars walk - 1 := by
    let a := (Op.move .next right right).eval z
    let b := (Op.scalar (M := model) .sub walk walk one).eval a
    have ha : a.scalars = z.scalars := addrOp_scalars z _ _
    have hbw : b.scalars walk = z.scalars walk - 1 := by simp [b, Op.eval, ha, hone z hz]
    have hbpos : localPos (b.addr right) = min (localPos (z.addr right) + 1) cells :=
      localPos_move z right
    refine ⟨b, (primitive _ z).seq (primitive _ a), ⟨?_, ?_, ?_, ?_, ?_⟩, hbw⟩
    · intro i hi
      simp only [b, Op.eval, Function.update_of_ne hi, ha]
      exact hz.1 i hi
    · intro i hi
      have haddr : b.addr i = z.addr i := by
        cases hn : z.addr right <;> simp [b, a, Op.eval, hn, Function.update_of_ne hi]
      exact haddr.trans (hz.2.1 i hi)
    · have hval : b.values = z.values := by cases hn : z.addr right <;> simp [b, a, Op.eval, hn]
      exact hval.trans hz.2.2.1
    · have href : b.refs = z.refs := by cases hn : z.addr right <;> simp [b, a, Op.eval, hn]
      exact href.trans hz.2.2.2.1
    · have he := hz.2.2.2.2
      rw [hbpos, hbw, ← he]
      let p := localPos (z.addr right)
      let k : ℕ := z.scalars walk
      change min (min (p + 1) cells + (k - 1)) cells = min (p + k) cells
      change 0 < k at hp
      omega
  obtain ⟨y, hy, hf, hz⟩ :=
    countdown_exec walk (next right ▷ dec walk) P x hone hs
      ⟨(fun _ _ => rfl), (fun _ _ => rfl), rfl, rfl, rfl⟩
  have hpos := hf.2.2.2.2
  rw [hz, Nat.add_zero, min_eq_left (localPos_le _)] at hpos
  exact ⟨y, hy.mono (by omega), hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hpos⟩

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
      (∀ i, i ≠ count → i ≠ remain → y.scalars i = x.scalars i) ∧
      y.addr = x.addr ∧ y.values = x.values ∧ y.refs = x.refs := by
  let w : ℕ := min (x.scalars remain) (x.scalars width)
  have hcopy : ∃ a,
      within (.branch (less remain width) (copyScalar count remain) (copyScalar count width))
        x a 3 ∧ a.scalars = Function.update x.scalars count w ∧
        a.addr = x.addr ∧ a.values = x.values ∧ a.refs = x.refs := by
    by_cases h : (x.scalars remain : ℕ) < x.scalars width
    · have hp := Program.ExecWithin.branch_pos (I := instructionSet model cells 8 11)
        (neg := copyScalar count width) ((less_holds x _ _).2 h)
        (primitive (.copyData count remain) x)
      exact ⟨_, hp.mono (by decide), by simp [Op.eval, w, min_eq_left h.le], rfl, rfl, rfl⟩
    · have hn := Program.ExecWithin.branch_neg (I := instructionSet model cells 8 11)
        (pos := copyScalar count remain) (fun ht => h ((less_holds x _ _).1 ht))
        (primitive (.copyData count width) x)
      exact ⟨_, hn, by simp [Op.eval, w, min_eq_right (Nat.le_of_not_gt h)], rfl, rfl, rfl⟩
  obtain ⟨a, ha, hsc, haa, hav, har⟩ := hcopy
  let y := (Op.scalar (M := model) .sub remain remain count).eval a
  refine ⟨y, ha.seq (primitive _ a), ?_, ?_, ?_, haa, hav, har⟩
  · simp [y, Op.eval, hr, hsc, w]
  · simp only [y, Op.eval, Function.update_self, hsc, Function.update_of_ne (Ne.symm hr), model]
    by_cases h : (x.scalars remain : ℕ) ≤ x.scalars width
    · rw [show w = x.scalars remain from min_eq_left h, Nat.sub_self, Nat.sub_eq_zero_of_le h]
    · rw [show w = x.scalars width from min_eq_right (Nat.le_of_not_ge h)]
  · intro i hi hj
    simp [y, Op.eval, hsc, hi, hj]

private def LocalEntries {cells : ℕ} (x : MachineState cells) (base : ℕ)
    (indices : List ℕ) : Prop :=
  ∀ j (hj : j < indices.length), ∃ a k : Fin cells, a.val = base + j ∧
    k.val = indices[j] ∧ x.values a = k.val ∧ x.refs a = some k

private def LocalKeyMem (keys : List ℕ) (x : MachineState (3 * keys.length)) : Prop :=
  ∀ i : Fin keys.length, x.values ⟨i.val, by have := i.isLt; omega⟩ = keys[i]

private structure LocalMergeContents (keys : List ℕ) (base : ℕ) (L R emitted : List ℕ)
    (x : MachineState (3 * keys.length)) : Prop where
  keys_mem : LocalKeyMem keys x
  keys_separate : keys.length ≤ base
  left_entries : LocalEntries x (localPos (x.addr left)) L
  right_entries : LocalEntries x (localPos (x.addr right)) R
  output_entries : LocalEntries x base emitted
  output_cursor : localPos (x.addr out) = base + emitted.length
  left_count : x.scalars lcount = L.length
  right_count : x.scalars rcount = R.length
  left_separate : localPos (x.addr left) + L.length ≤ base ∨
    localPos (x.addr out) + (L.length + R.length) ≤ localPos (x.addr left)
  right_separate : localPos (x.addr right) + R.length ≤ base ∨
    localPos (x.addr out) + (L.length + R.length) ≤ localPos (x.addr right)
  output_room : localPos (x.addr out) + (L.length + R.length) ≤ 3 * keys.length

private def LocalMemoryFrame {cells : ℕ} (x y : MachineState cells) (lo hi : ℕ) : Prop :=
  ∀ i : Fin cells, i.val < lo ∨ hi ≤ i.val → y.values i = x.values i ∧ y.refs i = x.refs i

private theorem writeEntry_footprint {cells : ℕ} (head item : Fin 8) (x : MachineState cells)
    {a h : Fin cells} (ho : x.addr out = some a) (hh : x.addr head = some h)
    (hne : head ≠ out) :
    ∃ y, within (writeEntry head item) x y 4 ∧ y.scalars = x.scalars ∧
      y.values = Function.update x.values a (x.scalars lvalue) ∧
      y.refs = Function.update x.refs a (x.addr item) ∧
      y.addr = Function.update (Function.update x.addr out (Direction.move .next a))
        head (Direction.move .next h) := by
  refine ⟨writeEntryState head item x, writeEntry_runs head item x, ?_, ?_, ?_, ?_⟩ <;>
    simp only [writeEntryState, Op.eval, ho, Option.elim_some, Function.update_of_ne hne, hh]

private theorem localPos_some {cells : ℕ} {a : Option (Fin cells)} (h : localPos a < cells) :
    ∃ p : Fin cells, a = some p ∧ p.val = localPos a := by
  cases a with
  | none => exact (Nat.lt_irrefl _ h).elim
  | some p => exact ⟨p, rfl, rfl⟩

private theorem localPos_next {cells : ℕ} (a : Fin cells) :
    localPos (Direction.move .next a) = a.val + 1 := by
  rw [Direction.move]
  by_cases h : a.val + 1 < cells
  · simp only [dite_eq_left h, localPos, Option.elim_some]
  · simp only [dite_eq_right h, localPos, Option.elim_none]
    have := a.isLt
    omega

private theorem LocalEntries.head {cells : ℕ} {x : MachineState cells} {i : ℕ}
    {p : Option (Fin cells)} {xs : List ℕ} (h : LocalEntries x (localPos p) (i :: xs)) :
    ∃ a k : Fin cells, p = some a ∧ k.val = i ∧ x.values a = i ∧ x.refs a = some k := by
  obtain ⟨a, k, ha, hk, hv, hr⟩ := h 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at ha hk
  have hp : localPos p < cells := ha ▸ a.isLt
  obtain ⟨b, hbp, hb⟩ := localPos_some hp
  have hab : a = b := Fin.ext (ha.trans hb.symm)
  exact ⟨a, k, hab ▸ hbp, hk, hv.trans hk, hr⟩

private theorem LocalEntries.tail {cells : ℕ} {x : MachineState cells} {base i : ℕ}
    {xs : List ℕ} (h : LocalEntries x base (i :: xs)) : LocalEntries x (base + 1) xs := by
  intro j hj
  have hj' : j + 1 < (i :: xs).length := by
    simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hj
  obtain ⟨a, k, ha, hk, hv, hr⟩ := h (j + 1) hj'
  exact ⟨a, k, by omega, by simpa only [List.getElem_cons_succ] using hk, hv, hr⟩

private theorem LocalEntries.frame {cells : ℕ} {x y : MachineState cells} {base : ℕ}
    {xs : List ℕ} (h : LocalEntries x base xs)
    (hmem : ∀ a : Fin cells, base ≤ a.val → a.val < base + xs.length →
      y.values a = x.values a ∧ y.refs a = x.refs a) : LocalEntries y base xs := by
  intro j hj
  obtain ⟨a, k, ha, hk, hv, hr⟩ := h j hj
  obtain ⟨hval, href⟩ := hmem a (by omega) (by omega)
  exact ⟨a, k, ha, hk, hval.trans hv, href.trans hr⟩

private theorem LocalEntries.snoc {cells : ℕ} {x : MachineState cells} {base : ℕ}
    {xs : List ℕ} (h : LocalEntries x base xs) {a k : Fin cells}
    (ha : a.val = base + xs.length) (hv : x.values a = k.val) (hr : x.refs a = some k) :
    LocalEntries x base (xs ++ [k.val]) := by
  intro j hj
  by_cases hj' : j < xs.length
  · obtain ⟨b, l, hb, hl, hw, hq⟩ := h j hj'
    exact ⟨b, l, hb, by simpa only [List.getElem_append_left hj'] using hl, hw, hq⟩
  · have he : j = xs.length := by
      simp only [List.length_append, List.length_singleton] at hj
      omega
    subst j
    exact ⟨a, k, ha, by simp, hv, hr⟩

private abbrev localSideHead (side : Bool) := if side then right else left
private abbrev localSideItem (side : Bool) := if side then rkey else lkey
private abbrev localSideCount (side : Bool) := if side then rcount else lcount

-- One step leaves the ends of both input runs and the end of the output unchanged.
private structure LocalMergeFrame {cells : ℕ} (x y : MachineState cells) : Prop where
  scalars : mergeFrame x y
  src : y.addr LocalRef.src = x.addr LocalRef.src
  dst : y.addr LocalRef.dst = x.addr LocalRef.dst
  left_end : localPos (y.addr left) + y.scalars lcount = localPos (x.addr left) + x.scalars lcount
  right_end : localPos (y.addr right) + y.scalars rcount =
    localPos (x.addr right) + x.scalars rcount
  out_le : localPos (x.addr out) ≤ localPos (y.addr out)
  out_end : localPos (y.addr out) + mergeSize y = localPos (x.addr out) + mergeSize x
  mem : LocalMemoryFrame x y (localPos (x.addr out)) (localPos (y.addr out))

private theorem LocalMergeFrame.refl {cells : ℕ} (x : MachineState cells) :
    LocalMergeFrame x x :=
  ⟨fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, le_rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem LocalMergeFrame.trans {cells : ℕ} {x y z : MachineState cells}
    (hxy : LocalMergeFrame x y) (hyz : LocalMergeFrame y z) : LocalMergeFrame x z := by
  refine ⟨mergeFrame_trans hxy.scalars hyz.scalars, hyz.src.trans hxy.src,
    hyz.dst.trans hxy.dst, hyz.left_end.trans hxy.left_end, hyz.right_end.trans hxy.right_end,
    hxy.out_le.trans hyz.out_le, hyz.out_end.trans hxy.out_end, ?_⟩
  intro a ha
  rcases ha with hlo | hhi
  · have ⟨hv, hr⟩ := hxy.mem a (Or.inl hlo)
    have ⟨hv', hr'⟩ := hyz.mem a (Or.inl (hlo.trans_le hxy.out_le))
    exact ⟨hv'.trans hv, hr'.trans hr⟩
  · have ⟨hv, hr⟩ := hxy.mem a (Or.inr (hyz.out_le.trans hhi))
    have ⟨hv', hr'⟩ := hyz.mem a (Or.inr hhi)
    exact ⟨hv'.trans hv, hr'.trans hr⟩

private structure LocalEmission {cells : ℕ} (x y : MachineState cells) (side : Bool)
    (i : ℕ) : Prop where
  frame : LocalMergeFrame x y
  left_cursor : localPos (y.addr left) = localPos (x.addr left) + if side then 0 else 1
  right_cursor : localPos (y.addr right) = localPos (x.addr right) + if side then 1 else 0
  out_cursor : localPos (y.addr out) = localPos (x.addr out) + 1
  stored : ∃ a k : Fin cells, a.val = localPos (x.addr out) ∧ k.val = i ∧
    y.values a = i ∧ y.refs a = some k

private theorem localEmit_exec {cells : ℕ} {x : MachineState cells} (side : Bool)
    {a h k : Fin cells} (ha : x.addr out = some a)
    (hh : x.addr (localSideHead side) = some h)
    (hk : x.addr (localSideItem side) = some k)
    (hv : x.values h = k.val) (ho : x.scalars one = 1)
    (hp : 0 < x.scalars (localSideCount side)) :
    ∃ y, within (emit (localSideHead side) (localSideItem side) (localSideCount side)) x y 6 ∧
      LocalEmission x y side k.val := by
  let hd := localSideHead side
  let item := localSideItem side
  let count := localSideCount side
  let z := (Op.loadData lvalue hd).eval x
  have hzs : z.scalars = Function.update x.scalars lvalue k.val := by
    simp only [z, Op.eval, show x.addr hd = some h from hh, Option.elim_some, hv]
  have hza : z.addr = x.addr := by
    simp only [z, Op.eval, show x.addr hd = some h from hh, Option.elim_some]
  have hzv : z.values = x.values := by
    simp only [z, Op.eval, show x.addr hd = some h from hh, Option.elim_some]
  have hzr : z.refs = x.refs := by
    simp only [z, Op.eval, show x.addr hd = some h from hh, Option.elim_some]
  have hne : hd ≠ out := by cases side <;> decide
  obtain ⟨w, hw, hws, hwv, hwr, hwa⟩ := writeEntry_footprint hd item z
    (hza ▸ ha) (hza ▸ hh) hne
  let y := (Op.scalar (M := model) .sub count count one).eval w
  have hys : y.scalars =
      Function.update (Function.update x.scalars lvalue k.val) count (x.scalars count - 1) := by
    have hc : count ≠ lvalue := by cases side <;> decide
    have hn : one ≠ lvalue := by decide
    simp only [y, Op.eval, model, hws, hzs, Function.update_of_ne hc, Function.update_of_ne hn, ho]
  have hya : y.addr = Function.update (Function.update x.addr out (Direction.move .next a))
      hd (Direction.move .next h) := hwa.trans (by rw [hza])
  have hyv : y.values = Function.update x.values a k.val := by
    change w.values = _
    rw [hwv, hzv, hzs, Function.update_self]
  have hyr : y.refs = Function.update x.refs a (some k) := by
    change w.refs = _
    rw [hwr, hzr, hza, show x.addr item = some k from hk]
  have hpotential (r : Fin 11) (hr : r ≠ count) (hv' : r ≠ lvalue) :
      y.scalars r = x.scalars r := by
    rw [hys, Function.update_of_ne hr, Function.update_of_ne hv']
  have hscalar : y.scalars count = x.scalars count - 1 := by
    rw [hys, Function.update_self]
  have haddr (r : Fin 8) (hr : r ≠ hd) (ho' : r ≠ out) : y.addr r = x.addr r := by
    rw [hya, Function.update_of_ne hr, Function.update_of_ne ho']
  have hmove : localPos (y.addr hd) = localPos (x.addr hd) + 1 := by
    rw [hya, Function.update_self, localPos_next, show x.addr hd = some h from hh]
    rfl
  have hout : localPos (y.addr out) = localPos (x.addr out) + 1 := by
    rw [hya, Function.update_of_ne hne.symm, Function.update_self, localPos_next, ha]
    rfl
  have hleft : localPos (y.addr left) = localPos (x.addr left) + if side then 0 else 1 := by
    cases side
    · exact hmove
    · rw [haddr left (by decide) (by decide)]
      simp
  have hright : localPos (y.addr right) = localPos (x.addr right) + if side then 1 else 0 := by
    cases side
    · rw [haddr right (by decide) (by decide)]
      simp
    · exact hmove
  have hls : localPos (y.addr left) + y.scalars lcount =
      localPos (x.addr left) + x.scalars lcount := by
    cases side
    · rw [hleft, show y.scalars lcount = x.scalars lcount - 1 from hscalar]
      have h : (1 : ℕ) ≤ x.scalars lcount := hp
      change localPos (x.addr left) + 1 + ((x.scalars lcount : ℕ) - 1) = _
      rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel h]
    · rw [hleft, hpotential lcount (by decide) (by decide)]
      simp
  have hrs : localPos (y.addr right) + y.scalars rcount =
      localPos (x.addr right) + x.scalars rcount := by
    cases side
    · rw [hright, hpotential rcount (by decide) (by decide)]
      simp
    · rw [hright, show y.scalars rcount = x.scalars rcount - 1 from hscalar]
      have h : (1 : ℕ) ≤ x.scalars rcount := hp
      change localPos (x.addr right) + 1 + ((x.scalars rcount : ℕ) - 1) = _
      rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel h]
  have hsum : mergeSize y + 1 = mergeSize x := by
    unfold mergeSize
    cases side
    · rw [show y.scalars lcount = x.scalars lcount - 1 from hscalar,
        hpotential rcount (by decide) (by decide)]
      have h : (1 : ℕ) ≤ x.scalars lcount := hp
      rw [Nat.add_right_comm, Nat.sub_add_cancel h]
    · rw [show y.scalars rcount = x.scalars rcount - 1 from hscalar,
        hpotential lcount (by decide) (by decide)]
      have h : (1 : ℕ) ≤ x.scalars rcount := hp
      rw [Nat.add_assoc, Nat.sub_add_cancel h]
  have maxBound : localPos (y.addr out) + mergeSize y = localPos (x.addr out) + mergeSize x := by
    rw [hout, Nat.add_assoc, Nat.add_comm 1, hsum]
  have hm : LocalMemoryFrame x y (localPos (x.addr out)) (localPos (y.addr out)) := by
    intro q hq
    have hr : q ≠ a := by
      rw [hout, ha] at hq
      change q.val < a.val ∨ a.val + 1 ≤ q.val at hq
      intro hqa
      subst q
      omega
    rw [hyv, hyr, Function.update_of_ne hr, Function.update_of_ne hr]
    exact ⟨rfl, rfl⟩
  have hs : mergeFrame x y := by
    intro r hl hr hv' _
    exact hpotential r (by cases side <;> assumption) hv'
  have hsrc : y.addr src = x.addr src :=
    haddr _ (by cases side <;> decide) (by decide)
  have hdst : y.addr dst = x.addr dst :=
    haddr _ (by cases side <;> decide) (by decide)
  refine ⟨y, (primitive _ x).seq (hw.seq (primitive _ w)), ?_⟩
  refine ⟨⟨hs, hsrc, hdst, hls, hrs, by rw [hout]; omega, maxBound, hm⟩,
    hleft, hright, hout, ⟨a, k, ?_, rfl, ?_, ?_⟩⟩
  · rw [ha]
    rfl
  · rw [hyv, Function.update_self]
  · rw [hyr, Function.update_self]

private theorem LocalMergeContents.emit {keys : List ℕ} {base i : ℕ} {side : Bool}
    {L R U V emitted : List ℕ} {x y : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L R emitted x) (he : LocalEmission x y side i)
    (hleft : LocalEntries x (localPos (y.addr left)) U)
    (hright : LocalEntries x (localPos (y.addr right)) V)
    (hl : localPos (y.addr left) + U.length = localPos (x.addr left) + L.length)
    (hr : localPos (y.addr right) + V.length = localPos (x.addr right) + R.length) :
    LocalMergeContents keys base U V (emitted ++ [i]) y := by
  have hlo := h.output_cursor
  have hout := he.out_cursor
  have hnl := he.frame.left_end
  have hnr := he.frame.right_end
  have hlc : y.scalars lcount = U.length := by
    rw [h.left_count, ← hl] at hnl
    exact Nat.add_left_cancel hnl
  have hrc : y.scalars rcount = V.length := by
    rw [h.right_count, ← hr] at hnr
    exact Nat.add_left_cancel hnr
  have htotal := he.frame.out_end
  rw [mergeSize, mergeSize, hlc, hrc, h.left_count, h.right_count] at htotal
  have hstepL : localPos (x.addr left) ≤ localPos (y.addr left) := by
    rw [he.left_cursor]
    exact Nat.le_add_right ..
  have hstepR : localPos (x.addr right) ≤ localPos (y.addr right) := by
    rw [he.right_cursor]
    exact Nat.le_add_right ..
  have hb : base ≤ localPos (x.addr out) := by rw [hlo]; exact Nat.le_add_right ..
  have hend : localPos (y.addr out) ≤ localPos (x.addr out) + (L.length + R.length) := by
    rw [← htotal]
    exact Nat.le_add_right ..
  obtain ⟨a, k, ha, hk, hv, hq⟩ := he.stored
  refine ⟨?_, h.keys_separate, ?_, ?_, ?_, ?_, hlc, hrc, ?_, ?_, ?_⟩
  · intro j
    have hkj := j.isLt
    have hbase := h.keys_separate
    exact (he.frame.mem _ (Or.inl (by change j.val < localPos (x.addr out); omega))).1.trans
      (h.keys_mem j)
  · apply hleft.frame
    intro p hp₁ hp₂
    apply he.frame.mem
    rcases h.left_separate with h₁ | h₂
    · exact Or.inl (hp₂.trans_le (hl.trans_le (h₁.trans hb)))
    · exact Or.inr (hend.trans (h₂.trans (hstepL.trans hp₁)))
  · apply hright.frame
    intro p hp₁ hp₂
    apply he.frame.mem
    rcases h.right_separate with h₁ | h₂
    · exact Or.inl (hp₂.trans_le (hr.trans_le (h₁.trans hb)))
    · exact Or.inr (hend.trans (h₂.trans (hstepR.trans hp₁)))
  · rw [← hk]
    exact (h.output_entries.frame (fun a _ hlt =>
      he.frame.mem a (Or.inl (hlo.symm ▸ hlt)))).snoc (ha.trans hlo) (hv.trans hk.symm) hq
  · rw [hout, hlo, List.length_append, List.length_singleton, Nat.add_assoc]
  · rw [hl, htotal]
    exact h.left_separate.imp_right (fun hs => hs.trans hstepL)
  · rw [hr, htotal]
    exact h.right_separate.imp_right (fun hs => hs.trans hstepR)
  · rw [htotal]
    exact h.output_room

private theorem LocalMergeContents.emitLeft {keys : List ℕ} {base i : ℕ}
    {L R emitted : List ℕ} {x y : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base (i :: L) R emitted x) (he : LocalEmission x y false i) :
    LocalMergeContents keys base L R (emitted ++ [i]) y := by
  have hl := he.left_cursor
  have hr := he.right_cursor
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hl hr
  apply h.emit he
  · rw [hl]
    exact h.left_entries.tail
  · rw [hr]
    exact h.right_entries
  · rw [hl, List.length_cons]
    omega
  · rw [hr]

private theorem LocalMergeContents.emitRight {keys : List ℕ} {base i : ℕ}
    {L R emitted : List ℕ} {x y : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L (i :: R) emitted x) (he : LocalEmission x y true i) :
    LocalMergeContents keys base L R (emitted ++ [i]) y := by
  have hl := he.left_cursor
  have hr := he.right_cursor
  simp only [ite_true, Nat.add_zero] at hl hr
  apply h.emit he
  · rw [hl]
    exact h.left_entries
  · rw [hr]
    exact h.right_entries.tail
  · rw [hl]
  · rw [hr, List.length_cons]
    omega

private structure LocalMergeRead {cells : ℕ} (x y : MachineState cells) : Prop where
  scalar : ∀ j, j ≠ lvalue → j ≠ rvalue → y.scalars j = x.scalars j
  addr : ∀ j, j ≠ lkey → j ≠ rkey → y.addr j = x.addr j
  values : y.values = x.values
  refs : y.refs = x.refs

private theorem LocalMergeRead.trans {cells : ℕ} {x y z : MachineState cells}
    (hxy : LocalMergeRead x y) (hyz : LocalMergeRead y z) : LocalMergeRead x z :=
  ⟨fun j hj hk => (hyz.scalar j hj hk).trans (hxy.scalar j hj hk),
    fun j hj hk => (hyz.addr j hj hk).trans (hxy.addr j hj hk),
    hyz.values.trans hxy.values, hyz.refs.trans hxy.refs⟩

private theorem LocalMergeRead.frame {cells : ℕ} {x y : MachineState cells}
    (h : LocalMergeRead x y) : LocalMergeFrame x y := by
  have hl := h.addr left (by decide) (by decide)
  have hr := h.addr right (by decide) (by decide)
  have ho := h.addr out (by decide) (by decide)
  have hlc := h.scalar lcount (by decide) (by decide)
  have hrc := h.scalar rcount (by decide) (by decide)
  refine ⟨fun j _ _ hj hk => h.scalar j hj hk, h.addr _ (by decide) (by decide),
    h.addr _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, hlc]
  · rw [hr, hrc]
  · rw [ho]
  · rw [ho, mergeSize, hlc, hrc, mergeSize]
  · intro i _
    rw [h.values, h.refs]
    exact ⟨rfl, rfl⟩

private theorem LocalMergeContents.read {keys : List ℕ} {base : ℕ}
    {L R emitted : List ℕ} {x y : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L R emitted x) (hf : LocalMergeRead x y) :
    LocalMergeContents keys base L R emitted y := by
  have hl := hf.addr left (by decide) (by decide)
  have hr := hf.addr right (by decide) (by decide)
  have ho := hf.addr out (by decide) (by decide)
  have hlc := hf.scalar lcount (by decide) (by decide)
  have hrc := hf.scalar rcount (by decide) (by decide)
  have hm (a : Fin (3 * keys.length)) : y.values a = x.values a ∧ y.refs a = x.refs a := by
    rw [hf.values, hf.refs]
    exact ⟨rfl, rfl⟩
  refine ⟨fun j => (hm _).1.trans (h.keys_mem j), h.keys_separate, ?_, ?_,
    h.output_entries.frame (fun a _ _ => hm a), ?_, hlc.trans h.left_count,
    hrc.trans h.right_count, ?_, ?_, ?_⟩
  · rw [hl]
    exact h.left_entries.frame (fun a _ _ => hm a)
  · rw [hr]
    exact h.right_entries.frame (fun a _ _ => hm a)
  · rw [ho]
    exact h.output_cursor
  · rw [hl, ho]
    exact h.left_separate
  · rw [hr, ho]
    exact h.right_separate
  · rw [ho]
    exact h.output_room

private theorem localLoadRef_frame {cells : ℕ} (x : MachineState cells) (head item : Fin 8)
    (hi : item = lkey ∨ item = rkey) :
    LocalMergeRead x ((Op.loadAddr item head).eval x) := by
  cases h : x.addr head with
  | none =>
    simp only [Op.eval, h, Option.elim_none]
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩
  | some p =>
    simp only [Op.eval, h, Option.elim_some]
    refine ⟨fun _ _ _ => rfl, ?_, rfl, rfl⟩
    intro j h₁ h₂
    change Function.update x.addr item (x.refs p) j = _
    rw [Function.update_of_ne (hi.elim (fun h => h.symm ▸ h₁) (fun h => h.symm ▸ h₂))]

private theorem localLoadData_frame {cells : ℕ} (x : MachineState cells) (item : Fin 8)
    (r : Fin 11) (hr : r = lvalue ∨ r = rvalue) :
    LocalMergeRead x ((Op.loadData r item).eval x) := by
  cases h : x.addr item with
  | none =>
    simp only [Op.eval, h, Option.elim_none]
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩
  | some p =>
    simp only [Op.eval, h, Option.elim_some]
    refine ⟨?_, fun _ _ _ => rfl, rfl, rfl⟩
    intro j h₁ h₂
    change Function.update x.scalars r (x.values p) j = _
    rw [Function.update_of_ne (hr.elim (fun h => h.symm ▸ h₁) (fun h => h.symm ▸ h₂))]

private theorem LocalKeyMem.getD {keys : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalKeyMem keys x) {a : Fin (3 * keys.length)} (ha : a.val < keys.length) :
    x.values a = keys.getD a.val 0 := by
  rw [List.getD_eq_getElem keys 0 ha]
  obtain ⟨i, _⟩ := a
  exact h ⟨i, ha⟩

private theorem LocalMergeContents.outSome {keys : List ℕ} {base : ℕ}
    {L R emitted : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L R emitted x) (hp : 0 < L.length + R.length) :
    ∃ a : Fin (3 * keys.length), x.addr out = some a := by
  have hroom := h.output_room
  obtain ⟨a, ha, _⟩ := localPos_some (show localPos (x.addr out) < 3 * keys.length by omega)
  exact ⟨a, ha⟩

private theorem LocalMergeRead.size {cells : ℕ} {x y : MachineState cells}
    (h : LocalMergeRead x y) : mergeSize y = mergeSize x := by
  unfold mergeSize
  rw [h.scalar lcount (by decide) (by decide), h.scalar rcount (by decide) (by decide)]

private theorem LocalEmission.decreases {cells : ℕ} {x y : MachineState cells}
    {side : Bool} {i : ℕ} (h : LocalEmission x y side i) : mergeSize y + 1 = mergeSize x := by
  have hs := h.frame.out_end
  rw [h.out_cursor, Nat.add_assoc, Nat.add_comm 1] at hs
  exact Nat.add_left_cancel hs

private theorem localLoadRef_hit {cells : ℕ} {x : MachineState cells} {head item : Fin 8}
    {a k : Fin cells} (ha : x.addr head = some a) (hk : x.refs a = some k) :
    ((Op.loadAddr item head).eval x).addr item = some k := by
  simp only [Op.eval, ha, Option.elim_some, Function.update_self, hk]

private theorem localCompare_exec {cells : ℕ} {x : MachineState cells} {a ki kj : Fin cells}
    (hl : x.addr lkey = some ki) (hr : x.addr right = some a) (hj : x.refs a = some kj) :
    ∃ y, within compareHeads x y 3 ∧ LocalMergeRead x y ∧
      y.addr lkey = some ki ∧ y.addr rkey = some kj ∧
      y.scalars lvalue = x.values ki ∧ y.scalars rvalue = x.values kj := by
  let a₁ := (Op.loadAddr rkey right).eval x
  let a₂ := (Op.loadData lvalue lkey).eval a₁
  let y := (Op.loadData rvalue rkey).eval a₂
  have hne : lkey ≠ rkey := by decide
  have h₁ : a₁.addr lkey = some ki := by
    simp only [a₁, Op.eval, hr, Option.elim_some, Function.update_of_ne hne, hl]
  have h₂ : a₁.addr rkey = some kj := localLoadRef_hit hr hj
  have h₃ : a₂.addr rkey = some kj := by
    simp only [a₂, Op.eval, h₁, Option.elim_some, h₂]
  have hf₁ : LocalMergeRead x a₁ := localLoadRef_frame x right rkey (Or.inr rfl)
  have hf₂ : LocalMergeRead a₁ a₂ := localLoadData_frame a₁ lkey lvalue (Or.inl rfl)
  have hf₃ : LocalMergeRead a₂ y := localLoadData_frame a₂ rkey rvalue (Or.inr rfl)
  have hw : rvalue ≠ lvalue := by decide
  refine ⟨y, (primitive _ x).seq ((primitive _ a₁).seq (primitive _ a₂)),
    (hf₁.trans hf₂).trans hf₃, ?_, ?_, ?_, ?_⟩
  · simp only [y, Op.eval, h₃, Option.elim_some]
    simp only [a₂, Op.eval, h₁, Option.elim_some]
  · simp only [y, Op.eval, h₃, Option.elim_some]
  · have hw' : lvalue ≠ rvalue := hw.symm
    simp only [y, Op.eval, h₃, Option.elim_some, Function.update_of_ne hw']
    simp only [a₂, Op.eval, h₁, Option.elim_some, Function.update_self, hf₁.values]
  · simp only [y, Op.eval, h₃, Option.elim_some, Function.update_self, hf₂.values, hf₁.values]

private theorem localEmitLeft_exec {keys : List ℕ} {base i : ℕ}
    {L R emitted : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base (i :: L) R emitted x) {k : Fin (3 * keys.length)}
    (hk : x.addr lkey = some k) (hi : k.val = i) (ho : x.scalars one = 1) :
    ∃ y, within (emit left lkey lcount) x y 6 ∧ LocalEmission x y false i ∧
      LocalMergeContents keys base L R (emitted ++ [i]) y := by
  obtain ⟨a, ha⟩ := h.outSome (by simp)
  obtain ⟨p, _, hp, _, hv, _⟩ := h.left_entries.head
  have hc : 0 < (x.scalars lcount : ℕ) :=
    h.left_count.symm ▸ List.length_pos_of_mem List.mem_cons_self
  obtain ⟨y, hy, he⟩ := localEmit_exec false ha hp hk (hv.trans hi.symm) ho hc
  rw [hi] at he
  exact ⟨y, hy, he, h.emitLeft he⟩

private theorem localEmitRight_exec {keys : List ℕ} {base i : ℕ}
    {L R emitted : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L (i :: R) emitted x) {k : Fin (3 * keys.length)}
    (hk : x.addr rkey = some k) (hi : k.val = i) (ho : x.scalars one = 1) :
    ∃ y, within (emit right rkey rcount) x y 6 ∧ LocalEmission x y true i ∧
      LocalMergeContents keys base L R (emitted ++ [i]) y := by
  obtain ⟨a, ha⟩ := h.outSome (by simp)
  obtain ⟨p, _, hp, _, hv, _⟩ := h.right_entries.head
  have hc : 0 < (x.scalars rcount : ℕ) :=
    h.right_count.symm ▸ List.length_pos_of_mem List.mem_cons_self
  obtain ⟨y, hy, he⟩ := localEmit_exec true ha hp hk (hv.trans hi.symm) ho hc
  rw [hi] at he
  exact ⟨y, hy, he, h.emitRight he⟩

private abbrev localKeyLE (keys : List ℕ) (a b : ℕ) : Bool :=
  decide (keys.getD a 0 ≤ keys.getD b 0)

private structure LocalMergeModel (keys : List ℕ) (base : ℕ) (goal : List ℕ)
    (x : MachineState (3 * keys.length)) : Prop where
  runs : ∃ L R emitted, LocalMergeContents keys base L R emitted x ∧
    emitted ++ List.merge L R (localKeyLE keys) = goal

private theorem localMergeStep_correct {keys : List ℕ} {base : ℕ}
    {goal : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeModel keys base goal x) (hindex : ∀ i ∈ goal, i < keys.length)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) (hp : 0 < x.scalars lcount) :
    ∃ y, within mergeStep x y 13 ∧ LocalMergeFrame x y ∧
      mergeSize y + 1 = mergeSize x ∧ LocalMergeModel keys base goal y := by
  obtain ⟨L, R, emitted, hc, he⟩ := h.runs
  cases L with
  | nil =>
    have hl : x.scalars lcount = 0 := hc.left_count
    rw [hl] at hp
    exact (Nat.lt_irrefl _ hp).elim
  | cons i L =>
    let a := (Op.loadAddr lkey left).eval x
    have ha : within (instr (.loadAddr lkey left)) x a 1 := primitive _ _
    have haf : LocalMergeRead x a := localLoadRef_frame x left lkey (Or.inl rfl)
    have hca := hc.read haf
    have haz : a.scalars zero = 0 := (haf.scalar zero (by decide) (by decide)).trans hz
    have hao : a.scalars one = 1 := (haf.scalar one (by decide) (by decide)).trans ho
    obtain ⟨p, ki, hpi, hki, _, hri⟩ := hc.left_entries.head
    have hai : a.addr lkey = some ki := localLoadRef_hit hpi hri
    cases R with
    | nil =>
      have har : a.scalars rcount = 0 := hca.right_count
      have htest : ¬(instructionSet model (3 * keys.length) 8 11).Holds (less zero rcount) a := by
        rw [less_holds, haz, har]
        exact Nat.lt_irrefl _
      obtain ⟨y, hy, hyf, hout⟩ := localEmitLeft_exec hca hai hki hao
      have hb := Program.ExecWithin.branch_neg (pos := compareHeads ▷
        .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount)) htest hy
      have hex : within mergeStep x y 13 := (ha.seq hb).mono (by decide)
      refine ⟨y, hex, haf.frame.trans hyf.frame, hyf.decreases.trans haf.size, ⟨?_⟩⟩
      refine ⟨L, [], emitted ++ [i], hout, ?_⟩
      simpa only [List.merge_right, List.append_assoc, List.singleton_append] using he
    | cons j R =>
      have hmem (u : ℕ) (hu : u ∈ (i :: L) ++ (j :: R)) : u < keys.length := by
        apply hindex
        rw [← he]
        exact List.mem_append_right _ ((List.merge_perm_append _).symm.subset hu)
      have hi := hmem i (List.mem_append_left _ List.mem_cons_self)
      have hj := hmem j (List.mem_append_right _ List.mem_cons_self)
      have htest : (instructionSet model (3 * keys.length) 8 11).Holds (less zero rcount) a := by
        rw [less_holds, haz, hca.right_count]
        exact List.length_pos_of_mem List.mem_cons_self
      obtain ⟨q, kj, hqj, hkj, _, hrj⟩ := hca.right_entries.head
      obtain ⟨b, hb, hbf, hbi, hbj, hbl, hbr⟩ := localCompare_exec hai hqj hrj
      have hcb := hca.read hbf
      have hbo : b.scalars one = 1 := (hbf.scalar one (by decide) (by decide)).trans hao
      have hleft : b.scalars lvalue = keys.getD i 0 := by
        rw [hbl, hca.keys_mem.getD (hki.symm ▸ hi), hki]
      have hright : b.scalars rvalue = keys.getD j 0 := by
        rw [hbr, hca.keys_mem.getD (hkj.symm ▸ hj), hkj]
      by_cases hcmp : keys.getD j 0 < keys.getD i 0
      · obtain ⟨y, hy, hyf, hout⟩ := localEmitRight_exec hcb hbj hkj hbo
        have hbtest : (instructionSet model (3 * keys.length) 8 11).Holds
            (less rvalue lvalue) b := by
          rwa [less_holds, hleft, hright]
        have hbranch := Program.ExecWithin.branch_pos (neg := emit left lkey lcount) hbtest hy
        have hex : within mergeStep x y 13 := ha.seq (Program.ExecWithin.branch_pos htest
          (hb.seq (hbranch.mono (show 7 ≤ 8 by decide))))
        refine ⟨y, hex, (haf.trans hbf).frame.trans hyf.frame,
          hyf.decreases.trans (haf.trans hbf).size, ⟨?_⟩⟩
        refine ⟨i :: L, R, emitted ++ [j], hout, ?_⟩
        rw [List.cons_merge_cons] at he
        simpa only [localKeyLE, decide_eq_false (Nat.not_le_of_gt hcmp), Bool.false_eq_true,
          ite_false, List.append_assoc, List.singleton_append] using he
      · obtain ⟨y, hy, hyf, hout⟩ := localEmitLeft_exec hcb hbi hki hbo
        have hbtest : ¬(instructionSet model (3 * keys.length) 8 11).Holds
            (less rvalue lvalue) b := by
          rwa [less_holds, hleft, hright]
        have hbranch := Program.ExecWithin.branch_neg (pos := emit right rkey rcount) hbtest hy
        have hex : within mergeStep x y 13 :=
          ha.seq (Program.ExecWithin.branch_pos htest (hb.seq hbranch))
        refine ⟨y, hex, (haf.trans hbf).frame.trans hyf.frame,
          hyf.decreases.trans (haf.trans hbf).size, ⟨?_⟩⟩
        refine ⟨L, j :: R, emitted ++ [i], hout, ?_⟩
        rw [List.cons_merge_cons] at he
        simpa only [localKeyLE, decide_eq_true (Nat.le_of_not_gt hcmp), ite_true,
          List.append_assoc, List.singleton_append] using he

private theorem localDrainStep_correct {keys : List ℕ} {base : ℕ}
    {goal : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeModel keys base goal x) (ho : x.scalars one = 1)
    (hl : x.scalars lcount = 0) (hp : 0 < x.scalars rcount) :
    ∃ y, within drainRight x y 7 ∧ LocalMergeFrame x y ∧
      mergeSize y + 1 = mergeSize x ∧ y.scalars lcount = 0 ∧ LocalMergeModel keys base goal y := by
  obtain ⟨L, R, emitted, hc, he⟩ := h.runs
  have hn : L = [] := List.length_eq_zero_iff.mp (hc.left_count.symm.trans hl)
  subst L
  cases R with
  | nil =>
    have hrc : x.scalars rcount = 0 := hc.right_count
    rw [hrc] at hp
    exact (Nat.lt_irrefl _ hp).elim
  | cons j R =>
    let a := (Op.loadAddr rkey right).eval x
    have ha : within (instr (.loadAddr rkey right)) x a 1 := primitive _ _
    have haf : LocalMergeRead x a := localLoadRef_frame x right rkey (Or.inr rfl)
    have hca := hc.read haf
    have hao : a.scalars one = 1 := (haf.scalar one (by decide) (by decide)).trans ho
    obtain ⟨p, ki, hpi, hki, _, hri⟩ := hc.right_entries.head
    have hai : a.addr rkey = some ki := localLoadRef_hit hpi hri
    obtain ⟨y, hy, hyf, hout⟩ := localEmitRight_exec hca hai hki hao
    refine ⟨y, ha.seq hy, haf.frame.trans hyf.frame, hyf.decreases.trans haf.size,
      hout.left_count, ⟨[], R, emitted ++ [j], hout, ?_⟩⟩
    simpa only [List.nil_merge, List.append_assoc, List.singleton_append] using he

private theorem localMergeLoop_correct {cells : ℕ} (counter : Fin 11) (body : SortCode)
    (P : MachineState cells → Prop)
    (step : ∀ x, P x → x.scalars one = 1 → 0 < x.scalars counter →
      ∃ y, within body x y 13 ∧ LocalMergeFrame x y ∧
        mergeSize y + 1 = mergeSize x ∧ P y)
    (x : MachineState cells) (h₁ : x.scalars one = 1) (hx : P x) :
    ∃ y t, within (.loopUntil (less counter one) body) x y t ∧
      LocalMergeFrame x y ∧ y.scalars counter = 0 ∧
      t + 15 * mergeSize y ≤ 15 * mergeSize x + 1 ∧ P y := by
  induction hn : mergeSize x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hy : (x.scalars counter : ℕ) = 0
    · have ht : (instructionSet model cells 8 11).Holds (less counter one) x := by
        rw [less_holds, hy, h₁]
        decide
      exact ⟨x, 1, Program.ExecWithin.loopUntil_exit ht, LocalMergeFrame.refl x, hy, by omega, hx⟩
    · have hpos := Nat.pos_of_ne_zero hy
      have ht : ¬(instructionSet model cells 8 11).Holds (less counter one) x := by
        rw [less_holds, h₁]
        exact Nat.not_lt_of_ge hpos
      obtain ⟨y, hy, hxy, hdecr, hyp⟩ := step x hx h₁ hpos
      have ho := (hxy.scalars one (by decide) (by decide) (by decide) (by decide)).trans h₁
      obtain ⟨z, t, hz, hyz, hstop, htime, hzp⟩ := ih (mergeSize y) (by omega) y ho hyp rfl
      exact ⟨z, 13 + t + 2, Program.ExecWithin.loopUntil_iter ht hy hz, hxy.trans hyz,
        hstop, by omega, hzp⟩

private theorem localMergeSuffix_correct {keys : List ℕ} {base : ℕ}
    {L R emitted : List ℕ} {x : MachineState (3 * keys.length)}
    (h : LocalMergeContents keys base L R emitted x)
    (hindex : ∀ i ∈ emitted ++ (L ++ R), i < keys.length)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) :
    ∃ y, within ((.loopUntil (less lcount one) mergeStep ▷
        .loopUntil (less rcount one) drainRight) ▷ copyRef left right)
        x y (15 * (L.length + R.length) + 3) ∧
      LocalKeyMem keys y ∧ LocalEntries y base (emitted ++ List.merge L R (localKeyLE keys)) ∧
      localPos (y.addr left) = localPos (x.addr right) + R.length ∧
      localPos (y.addr out) = localPos (x.addr out) + (L.length + R.length) ∧
      LocalMemoryFrame x y (localPos (x.addr out)) (localPos (y.addr out)) ∧
      mergeFrame x y ∧ y.addr src = x.addr src ∧ y.addr dst = x.addr dst := by
  let goal := emitted ++ List.merge L R (localKeyLE keys)
  have hgoal : ∀ i ∈ goal, i < keys.length := by
    intro i hi
    exact hindex i ((List.Perm.append_left emitted (List.merge_perm_append _)).subset hi)
  let P (z : MachineState (3 * keys.length)) : Prop :=
    z.scalars zero = 0 ∧ LocalMergeModel keys base goal z
  have hP : P x := ⟨hz, ⟨L, R, emitted, h, rfl⟩⟩
  obtain ⟨a, t₁, ha, hxa, hla, ht₁, hpa⟩ :=
    localMergeLoop_correct lcount mergeStep P
      (fun _ hy hone hp => by
        obtain ⟨z, hz, hf, hd, hm⟩ := localMergeStep_correct hy.2 hgoal hy.1 hone hp
        exact ⟨z, hz, hf, hd,
          (hf.scalars zero (by decide) (by decide) (by decide) (by decide)).trans hy.1, hm⟩)
      x ho hP
  let Q (z : MachineState (3 * keys.length)) : Prop :=
    z.scalars lcount = 0 ∧ LocalMergeModel keys base goal z
  have hao := (hxa.scalars one (by decide) (by decide) (by decide) (by decide)).trans ho
  obtain ⟨b, t₂, hb, hab, hrb, ht₂, hpb⟩ :=
    localMergeLoop_correct rcount drainRight Q
      (fun _ hy hone hp => by
        obtain ⟨z, hz, hf, hd, hl, hm⟩ := localDrainStep_correct hy.2 hone hy.1 hp
        exact ⟨z, hz.mono (by decide), hf, hd, hl, hm⟩)
      a hao ⟨hla, hpa.2⟩
  obtain ⟨L', R', emitted', hc, he⟩ := hpb.2.runs
  have hl' : L' = [] := List.length_eq_zero_iff.mp (hc.left_count.symm.trans hpb.1)
  have hr' : R' = [] := List.length_eq_zero_iff.mp (hc.right_count.symm.trans hrb)
  have hout : emitted' = goal := by
    simpa only [hl', hr', List.nil_merge, List.append_nil] using he
  have hin : mergeSize x = L.length + R.length := by
    rw [mergeSize, h.left_count, h.right_count]
  have hfin : mergeSize b = 0 := by
    simp only [mergeSize, hpb.1, hrb, Nat.zero_add]
  let y := (Op.copyAddr left right).eval b
  have hex : within (copyRef left right) b y 1 := primitive _ _
  have hbframe := hxa.trans hab
  have hyl : y.addr left = b.addr right := by
    simp only [y, Op.eval, Function.update_self]
  have hyo : y.addr out = b.addr out := by
    have hne : out ≠ left := by decide
    simp only [y, Op.eval, Function.update_of_ne hne]
  have hys : y.addr src = b.addr src := by
    have hne : src ≠ left := by decide
    simp only [y, Op.eval, Function.update_of_ne hne]
  have hyd : y.addr dst = b.addr dst := by
    have hne : dst ≠ left := by decide
    simp only [y, Op.eval, Function.update_of_ne hne]
  have hright := hbframe.right_end
  have houtput := hbframe.out_end
  refine ⟨y, ((ha.seq hb).seq hex).mono (by omega), hc.keys_mem, ?_, ?_, ?_, ?_,
    hbframe.scalars, hys.trans hbframe.src, hyd.trans hbframe.dst⟩
  · rw [← show emitted' = emitted ++ List.merge L R (localKeyLE keys) from hout]
    exact hc.output_entries
  · rw [hyl]
    simpa only [hrb, h.right_count, Nat.add_zero] using hright
  · rw [hyo]
    simpa only [hfin, hin, Nat.add_zero] using houtput
  · rw [hyo]
    exact hbframe.mem


private structure LocalPairSetup {cells : ℕ} (x e : MachineState cells) : Prop where
  lcount_eq : e.scalars lcount = min (x.scalars remain : ℕ) (x.scalars width)
  rcount_eq : e.scalars rcount = min ((x.scalars remain : ℕ) - e.scalars lcount) (x.scalars width)
  remain_eq : e.scalars remain = (x.scalars remain : ℕ) - 2 * x.scalars width
  scalars : ∀ i, i ≠ lcount → i ≠ rcount → i ≠ remain → i ≠ walk → e.scalars i = x.scalars i
  addr : ∀ i, i ≠ right → e.addr i = x.addr i
  right_addr : localPos (e.addr right) = min (localPos (x.addr left) + e.scalars lcount) cells
  values : e.values = x.values
  refs : e.refs = x.refs

private theorem preparePair_exec {cells : ℕ} (x : MachineState cells) (ho : x.scalars one = 1) :
    ∃ e, within preparePair x e (4 * min (x.scalars remain : ℕ) (x.scalars width) + 11) ∧
      LocalPairSetup x e := by
  obtain ⟨a, ha, hal, har, hfa, haa, hav, harf⟩ := takeRun_exec (count := lcount) x (by decide)
  obtain ⟨b, hb, hbr, hbm, hfb, hba, hbv, hbrf⟩ := takeRun_exec (count := rcount) a (by decide)
  have hab (i : Fin 11) (hl : i ≠ lcount) (hr : i ≠ rcount) (hm : i ≠ remain) :
      b.scalars i = x.scalars i := (hfb i hr hm).trans (hfa i hl hm)
  let c := (Op.copyAddr right left).eval b
  let d := (Op.copyData walk lcount).eval c
  have hdc (i : Fin 11) (hi : i ≠ walk) : d.scalars i = b.scalars i := by
    simp [d, c, Op.eval, hi]
  have hdwalk : d.scalars walk = b.scalars lcount := by simp [d, c, Op.eval]
  have hbl := (hfb lcount (by decide) (by decide)).trans hal
  obtain ⟨e, he, hef, heAddr, heValues, heRefs, hePos⟩ := walk_exec d
    ((hdc one (by decide)).trans ((hab one (by decide) (by decide) (by decide)).trans ho))
  have heq (i : Fin 11) (hi : i ≠ walk) : e.scalars i = b.scalars i :=
    (hef i hi).trans (hdc i hi)
  have heL := (heq lcount (by decide)).trans hbl
  refine ⟨e, ?_, ⟨heL, ?_, ?_, ?_, ?_, ?_, heValues.trans (hbv.trans hav),
    heRefs.trans (hbrf.trans harf)⟩⟩
  · have hc : within (copyRef right left) b c 1 := primitive _ _
    have hd : within (copyScalar walk lcount) c d 1 := primitive _ _
    apply (ha.seq (hb.seq (hc.seq (hd.seq he)))).mono
    rw [hdwalk, hbl]
    omega
  · rw [heq rcount (by decide), hbr, hfa width (by decide) (by decide), heL]
    rw [har]
    let r : ℕ := x.scalars remain
    let w : ℕ := x.scalars width
    change min (r - w) w = min (r - min r w) w
    omega
  · rw [heq remain (by decide), hbm, har, hfa width (by decide) (by decide)]
    rw [Nat.sub_sub, two_mul]
  · intro i hl hr hm hw
    exact (heq i hw).trans (hab i hl hr hm)
  · intro i hi
    have h : d.addr i = b.addr i := by simp [d, c, Op.eval, Function.update_of_ne hi]
    exact (heAddr i hi).trans (h.trans (congrFun (hba.trans haa) i))
  · have hdAddr : d.addr right = x.addr left := by
      simp only [d, c, Op.eval, Function.update_self, hba, haa]
    rw [hePos, hdAddr, hdwalk, hbl, heL]

private theorem mergePair_exec {cells : ℕ} (x : MachineState cells)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) :
    ∃ y, within mergePair x y
      (19 * min (x.scalars remain : ℕ) (2 * x.scalars width) + 14) ∧ passFrame x y ∧
      y.scalars remain = (x.scalars remain : ℕ) - 2 * x.scalars width := by
  obtain ⟨e, he, hs⟩ := preparePair_exec x ho
  have hedge (i : Fin 11) (hl : i ≠ lcount) (hr : i ≠ rcount) (hm : i ≠ remain) (hw : i ≠ walk) :
      e.scalars i = x.scalars i := hs.scalars i hl hr hm hw
  obtain ⟨y, hy, hf⟩ := mergeSuffix_exec e
    ((hedge _ (by decide) (by decide) (by decide) (by decide)).trans hz)
    ((hedge _ (by decide) (by decide) (by decide) (by decide)).trans ho)
  have hsize : mergeSize e = min (x.scalars remain : ℕ) (2 * x.scalars width) := by
    unfold mergeSize
    rw [hs.rcount_eq, hs.lcount_eq]
    let r : ℕ := x.scalars remain
    let w : ℕ := x.scalars width
    change min r w + min (r - min r w) w = min r (2 * w)
    omega
  have hfinal (i : Fin 11) (hl : i ≠ lcount) (hr : i ≠ rcount) (hv : i ≠ lvalue)
      (hk : i ≠ rvalue) (hm : i ≠ remain) (hw : i ≠ walk) : y.scalars i = x.scalars i :=
    (hf i hl hr hv hk).trans (hedge i hl hr hm hw)
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- The flattened code and the original sequence have the same two stages.
    apply (he.seq hy).mono
    rw [hsize]
    change 4 * min (_ : ℕ) _ + 11 + (15 * min _ _ + 3) ≤ _
    omega
  · exact hfinal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfinal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfinal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfinal _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (hf remain (by decide) (by decide) (by decide) (by decide)).trans hs.remain_eq

private def mergeSuffix : SortCode :=
  (.loopUntil (less lcount one) mergeStep ▷ .loopUntil (less rcount one) drainRight) ▷
    copyRef left right

private structure LocalPairContents (keys : List ℕ) (base : ℕ) (L R emitted : List ℕ)
    (x : MachineState (3 * keys.length)) : Prop where
  keys_mem : LocalKeyMem keys x
  keys_separate : keys.length ≤ base
  left_entries : LocalEntries x (localPos (x.addr left)) L
  right_entries : LocalEntries x (localPos (x.addr left) + L.length) R
  output_entries : LocalEntries x base emitted
  output_cursor : localPos (x.addr out) = base + emitted.length
  left_length : L.length = min (x.scalars remain : ℕ) (x.scalars width)
  right_length : R.length = min ((x.scalars remain : ℕ) - L.length) (x.scalars width)
  source_room : localPos (x.addr left) + (L.length + R.length) ≤ 3 * keys.length
  output_room : localPos (x.addr out) + (L.length + R.length) ≤ 3 * keys.length
  separate : localPos (x.addr left) + (L.length + R.length) ≤ base ∨
    localPos (x.addr out) + (L.length + R.length) ≤ localPos (x.addr left)
  indices : ∀ i ∈ emitted ++ (L ++ R), i < keys.length

private structure LocalPairOutput (keys : List ℕ) (base : ℕ) (L R emitted : List ℕ)
    (x y : MachineState (3 * keys.length)) : Prop where
  keys_mem : LocalKeyMem keys y
  output : LocalEntries y base (emitted ++ List.merge L R
    (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0)))
  left_cursor : localPos (y.addr left) = localPos (x.addr left) + (L.length + R.length)
  out_cursor : localPos (y.addr out) = localPos (x.addr out) + (L.length + R.length)
  source : y.addr src = x.addr src
  destination : y.addr dst = x.addr dst
  memory : LocalMemoryFrame x y (localPos (x.addr out)) (localPos (y.addr out))

private theorem localPair_correct {keys : List ℕ}
    {base : ℕ} {L R emitted : List ℕ} {x y : MachineState (3 * keys.length)} {t : ℕ}
    (hx : LocalPairContents keys base L R emitted x) (hzero : x.scalars zero = 0)
    (hone : x.scalars one = 1)
    (hrun : Program.Exec (instructionSet model (3 * keys.length) 8 11) mergePair x y t) :
    LocalPairOutput keys base L R emitted x y := by
  obtain ⟨e, he, hs⟩ := preparePair_exec x hone
  have hleft : localPos (e.addr left) = localPos (x.addr left) := by rw [hs.addr left (by decide)]
  have hout : localPos (e.addr out) = localPos (x.addr out) := by rw [hs.addr out (by decide)]
  have hcntL := hs.lcount_eq.trans hx.left_length.symm
  have hcntR : e.scalars rcount = R.length := by rw [hs.rcount_eq, hcntL, ← hx.right_length]
  have hright : localPos (e.addr right) = localPos (x.addr left) + L.length := by
    rw [hs.right_addr, hcntL]
    exact min_eq_left (by have := hx.source_room; omega)
  have frame : ∀ i : Fin (3 * keys.length), e.values i = x.values i ∧ e.refs i = x.refs i :=
    fun i => ⟨congrFun hs.values i, congrFun hs.refs i⟩
  have entries (p : ℕ) (is : List ℕ) (h : LocalEntries x p is) : LocalEntries e p is := by
    intro j hj
    obtain ⟨a, k, ha, hk, hv, hr⟩ := h j hj
    exact ⟨a, k, ha, hk, (frame a).1.trans hv, (frame a).2.trans hr⟩
  have hm : LocalMergeContents keys base L R emitted e := by
    refine ⟨?_, hx.keys_separate, ?_, ?_, entries _ _ hx.output_entries,
      hout.trans hx.output_cursor, hcntL, hcntR, ?_, ?_, ?_⟩
    · intro i
      rw [hs.values]
      exact hx.keys_mem i
    · rw [hleft]
      exact entries _ _ hx.left_entries
    · rw [hright]
      exact entries _ _ hx.right_entries
    · rw [hleft, hout]
      have := hx.separate
      omega
    · rw [hright, hout]
      have := hx.separate
      omega
    · rw [hout]
      exact hx.output_room
  have hz := (hs.scalars zero (by decide) (by decide) (by decide) (by decide)).trans hzero
  have ho := (hs.scalars one (by decide) (by decide) (by decide) (by decide)).trans hone
  obtain ⟨z, hzrun, hk, hp, hl, hzo, hmem, _, hzs, hzd⟩ :=
    localMergeSuffix_correct hm hx.indices hz ho
  obtain ⟨_, _, hc⟩ := he.seq hzrun
  have hdet : z = y := (Program.Exec.unique hc hrun).1
  subst z
  rw [hright] at hl
  refine ⟨hk, hp, by omega, hzo.trans (by rw [hout]), hzs.trans (hs.addr src (by decide)),
    hzd.trans (hs.addr dst (by decide)), ?_⟩
  intro i hi
  have hh := hmem i (by rw [hout]; exact hi)
  exact ⟨hh.1.trans (frame i).1, hh.2.trans (frame i).2⟩

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

private theorem localEntries_slice {cells : ℕ} {x : MachineState cells} {base : ℕ} {xs : List ℕ}
    (h : LocalEntries x base xs) (lo len : ℕ) :
    LocalEntries x (base + lo) ((xs.drop lo).take len) := by
  intro j hj
  have hj' := hj
  rw [List.length_take, List.length_drop] at hj'
  have ht : lo + j < xs.length := by omega
  obtain ⟨a, k, ha, hk, hv, hr⟩ := h (lo + j) ht
  refine ⟨a, k, by omega, ?_, hv, hr⟩
  rw [List.getElem_take, List.getElem_drop]
  exact hk

private def localBuffers (n : ℕ) (x : MachineState (3 * n)) : Prop :=
  (localPos (x.addr src) = n ∧ localPos (x.addr dst) = 2 * n) ∨
    (localPos (x.addr src) = 2 * n ∧ localPos (x.addr dst) = n)

private structure LocalPassModel (keys source : List ℕ) (W : ℕ)
    (x : MachineState (3 * keys.length)) : Prop where
  keys_mem : LocalKeyMem keys x
  buffers : localBuffers keys.length x
  input : LocalEntries x (localPos (x.addr src)) source
  source_length : source.length = keys.length
  source_indices : ∀ i ∈ source, i < keys.length
  width_eq : x.scalars width = W
  progress : ∃ emitted q,
    LocalEntries x (localPos (x.addr dst)) emitted ∧
    emitted.length + x.scalars remain = keys.length ∧
    emitted.length = min keys.length (q * (2 * W)) ∧
    localPos (x.addr left) = localPos (x.addr src) + emitted.length ∧
    localPos (x.addr out) = localPos (x.addr dst) + emitted.length ∧
    StableMergePrefix keys source (2 * W) emitted.length emitted

private theorem localPassModel_step
    {keys source : List ℕ} {W t : ℕ} {x y : MachineState (3 * keys.length)}
    (h : LocalPassModel keys source W x)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1)
    (hstep : Program.Exec (instructionSet model (3 * keys.length) 8 11) mergePair x y t)
    (hr : 0 < x.scalars remain) (hstable : StableRuns keys W source) :
    LocalPassModel keys source W y ∧ passFrame x y := by
  obtain ⟨emitted, q, hem, hlen, hq, hleft, hout, hprefix⟩ := h.progress
  let n := keys.length
  let m := emitted.length
  let r : ℕ := x.scalars remain
  let l := min r W
  let b := min (r - l) W
  let L := (source.drop m).take l
  let R := (source.drop (m + l)).take b
  let tail := List.merge L R (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))
  have hcl : L.length = l := by
    simp only [L, List.length_take, List.length_drop, h.source_length]
    dsimp [l, m, r]
    omega
  have hcr : R.length = b := by
    simp only [R, List.length_take, List.length_drop, h.source_length]
    dsimp [b, l, m, r]
    omega
  have hpair : l + b = min r (2 * W) := by dsimp [l, b]; omega
  have hb := h.buffers
  have hpairContents : LocalPairContents keys (localPos (x.addr dst)) L R emitted x := by
    refine ⟨h.keys_mem, ?_, ?_, ?_, hem, hout, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold localBuffers at hb
      omega
    · rw [hleft]
      exact localEntries_slice h.input m l
    · rw [hleft, hcl, Nat.add_assoc]
      exact localEntries_slice h.input (m + l) b
    · rw [hcl, h.width_eq]
    · rw [hcr, hcl, h.width_eq]
    · rw [hcl, hcr, hleft]
      unfold localBuffers at hb
      omega
    · rw [hcl, hcr, hout]
      unfold localBuffers at hb
      omega
    · rw [hcl, hcr, hleft, hout]
      unfold localBuffers at hb
      omega
    · intro i hi
      apply h.source_indices
      rcases List.mem_append.mp hi with h₁ | h₂
      · exact List.mem_of_mem_take (hprefix.perm.subset h₁)
      · rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact List.mem_of_mem_drop (List.mem_of_mem_take h₂)
        · exact List.mem_of_mem_drop (List.mem_of_mem_take h₂)
  have hp := localPair_correct hpairContents hz ho hstep
  obtain ⟨z, hzrun, hf, hremain⟩ := mergePair_exec x hz ho
  obtain ⟨_, _, he⟩ := hzrun
  have hy : z = y := (Program.Exec.unique he hstep).1
  subst z
  have hslen : tail.length = l + b := by
    rw [show tail.length = (L ++ R).length from (List.merge_perm_append _).length_eq,
      List.length_append, hcl, hcr]
  have hr' : 0 < r := hr
  have hq' : m = min n (q * (2 * W)) := hq
  have hlen' : m + r = n := hlen
  have hm : m = q * (2 * W) := by omega
  have hnewlen : (emitted ++ tail).length = m + l + b := by
    rw [List.length_append, hslen]
    omega
  have hnewq : (emitted ++ tail).length = min n ((q + 1) * (2 * W)) := by
    rw [hnewlen, Nat.add_assoc m l b, hpair, Nat.add_mul]
    dsimp [n, m, r] at *
    rw [← hm]
    omega
  have hpre : StableMergePrefix keys source (2 * W) (m + l + b) (emitted ++ tail) := by
    apply stableMergePrefix_step h.source_length hstable hprefix hm (mid := m + l)
    · dsimp [l, m, r]; omega
    · dsimp [b, l, m, r]; omega
    · have h₁ : m + l - m = l := by omega
      have h₂ : m + l + b - (m + l) = b := by omega
      rw [h₁, h₂]
  have hlOut := hp.out_cursor
  rw [hcl, hcr, hout] at hlOut
  have hlLeft := hp.left_cursor
  rw [hcl, hcr, hleft] at hlLeft
  refine ⟨⟨hp.keys_mem, ?_, ?_, h.source_length, h.source_indices, hf.2.2.2.trans h.width_eq,
    ⟨emitted ++ tail, q + 1, ?_, ?_, hnewq, ?_, ?_, ?_⟩⟩, hf⟩
  · simpa only [localBuffers, hp.source, hp.destination] using hb
  · rw [hp.source]
    intro j hj
    obtain ⟨a, k, ha, hk, hv, href⟩ := h.input j hj
    have hjn : j < keys.length := hj.trans_le h.source_length.le
    have hmem := hp.memory a (by rw [hout, hlOut]; unfold localBuffers at hb; omega)
    exact ⟨a, k, ha, hk, hmem.1.trans hv, hmem.2.trans href⟩
  · rw [hp.destination]
    exact hp.output
  · rw [hremain, h.width_eq, hnewlen, Nat.add_assoc m l b, hpair]
    change m + min r (2 * W) + (r - 2 * W) = keys.length
    rw [Nat.add_assoc, Nat.add_comm (min r _), Nat.sub_add_min_cancel]
    exact hlen
  · rw [hp.source, hnewlen, hlLeft]
    omega
  · rw [hp.destination, hnewlen, hlOut]
    omega
  · rwa [hnewlen]

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

/-- The initialized prefix occupies the beginning of the primary buffer. -/
private structure LocalInitInv (keys : List ℕ) (hn : 0 < keys.length)
    (x : MachineState (3 * keys.length)) : Prop where
  remain_le : x.scalars remain ≤ keys.length
  scalars : ∀ r, r ≠ remain → r ≠ lvalue → x.scalars r = (inputState keys).scalars r
  src : x.addr LocalRef.src = (inputState keys).addr LocalRef.src
  dst : x.addr LocalRef.dst = (inputState keys).addr LocalRef.dst
  key : x.addr LocalRef.key = some ⟨keys.length - x.scalars remain, by omega⟩
  out : x.addr LocalRef.out =
    some ⟨permBase keys.length + (keys.length - x.scalars remain), by unfold permBase; omega⟩
  keys_eq : ∀ i : Fin keys.length, x.values ⟨i.val, by have := i.isLt; omega⟩ = keys[i]
  values : ∀ i : Fin keys.length, i.val < keys.length - x.scalars remain →
    x.values ⟨permBase keys.length + i.val, by unfold permBase; have := i.isLt; omega⟩ = i.val
  refs : ∀ i : Fin keys.length, i.val < keys.length - x.scalars remain →
    x.refs ⟨permBase keys.length + i.val, by unfold permBase; have := i.isLt; omega⟩ =
      some ⟨i.val, by have := i.isLt; omega⟩

private theorem initEntries_correct (keys : List ℕ) (hn : 0 < keys.length) :
    ∃ y, within initEntries (inputState keys) y (8 * keys.length + 3) ∧
      y.scalars remain = 0 ∧ LocalInitInv keys hn y := by
  let n := keys.length
  let x := inputState keys
  let a := (Op.copyAddr out src).eval x
  let b := (Op.copyData remain len).eval a
  have hbr : b.scalars remain = n := by
    simp only [b, a, Op.eval, Function.update_self]
    rfl
  have hone (z : MachineState (3 * n)) (hz : LocalInitInv keys hn z) :
      z.scalars one = 1 := (hz.scalars one (by decide) (by decide)).trans rfl
  have hs (z : MachineState (3 * n)) (hz : LocalInitInv keys hn z)
      (hp : 0 < z.scalars remain) :
      ∃ y, within initStep z y 6 ∧ LocalInitInv keys hn y ∧
        y.scalars remain = z.scalars remain - 1 := by
    let k : ℕ := n - z.scalars remain
    have hnpos : 0 < n := hn
    have hzrem : z.scalars remain ≤ n := hz.remain_le
    have hk : k < n := Nat.sub_lt hnpos hp
    let ka : Fin (3 * n) := ⟨k, Nat.lt_trans hk (by omega)⟩
    let oa : Fin (3 * n) := ⟨permBase n + k, by unfold permBase; omega⟩
    let c := (Op.scalar (M := model) .sub lvalue len remain).eval z
    have hcLen : z.scalars len = n := (hz.scalars len (by decide) (by decide)).trans rfl
    have hcVal : c.scalars lvalue = k := by
      simp only [c, Op.eval, Function.update_self, model, hcLen, k]
    obtain ⟨d, hd, hds, hdv, hdr, hda⟩ :=
      writeEntry_footprint key key c (a := oa) (h := ka) hz.out hz.key (by decide)
    let y := (Op.scalar (M := model) .sub remain remain one).eval d
    have he : within initStep z y 6 := (primitive _ z).seq (hd.seq (primitive _ d))
    have hr : y.scalars remain = z.scalars remain - 1 := by
      have h₁ : remain ≠ lvalue := by decide
      have h₂ : one ≠ lvalue := by decide
      simp only [y, Op.eval, hds, Function.update_self, Function.update_of_ne h₁,
        Function.update_of_ne h₂, model, c, hone z hz]
    have hka : Direction.move .next ka = some ⟨k + 1, by omega⟩ := by
      have h : k + 1 < 3 * n := by omega
      simp only [Direction.move, ka, dite_eq_left h]
    have hoa : Direction.move .next oa = some ⟨permBase n + (k + 1),
        by unfold permBase; omega⟩ := by
      have h : permBase n + k + 1 < 3 * n := by unfold permBase; omega
      rw [Direction.move]
      change (if t : permBase n + k + 1 < 3 * n then some (⟨permBase n + k + 1, t⟩ : Fin (3 * n))
        else none) = _
      rw [dite_eq_left h]
      exact congrArg some (Fin.ext (Nat.add_assoc ..))
    have hik : n - y.scalars remain = k + 1 := by
      rw [hr]
      apply (Nat.sub_eq_iff_eq_add ((Nat.sub_le ..).trans hzrem)).2
      rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel hp]
      exact (Nat.sub_add_cancel hzrem).symm
    refine ⟨y, he, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr⟩
    · rw [hr]
      exact (Nat.sub_le ..).trans hzrem
    · intro r h₁ h₂
      change Function.update d.scalars remain _ r = _
      rw [Function.update_of_ne h₁, hds]
      change Function.update z.scalars lvalue _ r = _
      rw [Function.update_of_ne h₂]
      exact hz.scalars r h₁ h₂
    · have h₁ : src ≠ key := by decide
      have h₂ : src ≠ out := by decide
      change d.addr src = _
      rw [hda, Function.update_of_ne h₁, Function.update_of_ne h₂]
      exact hz.src
    · have h₁ : dst ≠ key := by decide
      have h₂ : dst ≠ out := by decide
      change d.addr dst = _
      rw [hda, Function.update_of_ne h₁, Function.update_of_ne h₂]
      exact hz.dst
    · change d.addr key = _
      rw [hda, Function.update_self, hka]
      exact congrArg some (Fin.ext hik.symm)
    · have h₁ : out ≠ key := by decide
      change d.addr out = _
      rw [hda, Function.update_of_ne h₁, Function.update_self, hoa]
      exact congrArg some (Fin.ext (congrArg (permBase n + ·) hik.symm))
    · intro i
      change d.values _ = _
      rw [hdv, Function.update_of_ne]
      · exact hz.keys_eq i
      · intro eq
        have hi := i.isLt
        have h := congrArg Fin.val eq
        change i.val = n + k at h
        omega
    · intro i hi
      change d.values _ = _
      rw [hdv, hcVal]
      by_cases hi' : i.val = k
      · rw [show (⟨permBase n + i.val, _⟩ : Fin (3 * n)) = oa from Fin.ext (by simp [oa, hi'])]
        rw [Function.update_self, hi']
      · rw [Function.update_of_ne]
        · exact hz.values i (by change i.val < n - y.scalars remain at hi; omega)
        · intro eq
          have he := congrArg Fin.val eq
          change n + i.val = n + k at he
          exact hi' (Nat.add_left_cancel he)
    · intro i hi
      change d.refs _ = _
      rw [hdr]
      change Function.update z.refs oa (z.addr key) _ = _
      by_cases hi' : i.val = k
      · rw [show (⟨permBase n + i.val, _⟩ : Fin (3 * n)) = oa from Fin.ext (by simp [oa, hi'])]
        rw [Function.update_self, hz.key]
        exact congrArg some (Fin.ext hi'.symm)
      · rw [Function.update_of_ne]
        · exact hz.refs i (by change i.val < n - y.scalars remain at hi; omega)
        · intro eq
          have he := congrArg Fin.val eq
          change n + i.val = n + k at he
          exact hi' (Nat.add_left_cancel he)
  have hb : LocalInitInv keys hn b := by
    refine ⟨hbr.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h₁ _
      change Function.update x.scalars remain _ r = _
      rw [Function.update_of_ne h₁]
    · have h : src ≠ out := by decide
      change Function.update x.addr out (x.addr src) src = _
      rw [Function.update_of_ne h]
    · have h : dst ≠ out := by decide
      change Function.update x.addr out (x.addr src) dst = _
      rw [Function.update_of_ne h]
    · have h : key ≠ out := by decide
      change Function.update x.addr out (x.addr src) key = _
      rw [Function.update_of_ne h]
      simp [x, inputState, hn, hbr, n]
    · change Function.update x.addr out (x.addr src) out = _
      simp [x, inputState, hn, hbr, n]
    · intro i
      change keys[i.val]?.getD 0 = keys[i]
      simp [i.isLt]
    · intro i hi
      exact (Nat.not_lt_zero i.val (by simpa only [hbr, n, Nat.sub_self] using hi)).elim
    · intro i hi
      exact (Nat.not_lt_zero i.val (by simpa only [hbr, n, Nat.sub_self] using hi)).elim
  obtain ⟨y, hy, hinv, hrem⟩ := countdown_exec remain initStep (LocalInitInv keys hn) b hone hs hb
  refine ⟨y, (primitive _ x |>.seq ((primitive _ a).seq hy)).mono ?_, hrem, hinv⟩
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

private theorem localPassLoop_correct
    {keys source : List ℕ} {W t : ℕ} {x y : MachineState (3 * keys.length)}
    (h : Program.Exec (instructionSet model (3 * keys.length) 8 11)
      (.loopUntil (less remain one) mergePair) x y t)
    (hi : LocalPassModel keys source W x) (hstable : StableRuns keys W source)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) :
    LocalPassModel keys source W y ∧ y.scalars remain = 0 := by
  induction t using Nat.strong_induction_on generalizing x y with
  | _ t ih =>
    cases h with
    | loopUntil_exit ht =>
      rw [less_holds, ho] at ht
      exact ⟨hi, Nat.lt_one_iff.mp ht⟩
    | @loopUntil_iter _ _ a b _ m n ht hbody hrest =>
      rw [less_holds, ho] at ht
      obtain ⟨hm, hf⟩ := localPassModel_step hi hz ho hbody
        (Nat.le_of_not_gt ht) hstable
      exact ih n (by omega) hrest hm (hf.1.trans hz) (hf.2.1.trans ho)

private structure LocalSortContents (keys : List ℕ)
    (x : MachineState (3 * keys.length)) : Prop where
  keys_mem : LocalKeyMem keys x
  buffers : localBuffers keys.length x
  entries : ∃ indices,
    LocalEntries x (localPos (x.addr src)) indices ∧
    indices.Perm (List.range keys.length) ∧
    StableRuns keys (x.scalars width) indices

private theorem localPass_correct
    {keys : List ℕ} {x y : MachineState (3 * keys.length)} {t : ℕ}
    (h : Program.Exec (instructionSet model (3 * keys.length) 8 11) mergePass x y t)
    (hi : LocalSortContents keys x) (hl : x.scalars len = keys.length)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) (hw : 0 < x.scalars width) :
    LocalSortContents keys y ∧ y.scalars zero = x.scalars zero ∧
      y.scalars one = x.scalars one ∧ y.scalars len = x.scalars len ∧
      y.scalars width = 2 * (x.scalars width : ℕ) := by
  obtain ⟨source, hse, hperm, hstable⟩ := hi.entries
  let a := (Op.copyData remain len).eval x
  let b := (Op.copyAddr left src).eval a
  let c := (Op.copyAddr out dst).eval b
  have hc (r : Fin 11) (hr : r ≠ remain) : c.scalars r = x.scalars r :=
    Function.update_of_ne hr _ _
  have hcr : c.scalars remain = keys.length := by simp [a, b, c, Op.eval, hl]
  have hwc := hc width (by decide)
  have hs : c.addr src = x.addr src := by
    simp [c, b, a, Op.eval, Function.update_of_ne (by decide : src ≠ left),
      Function.update_of_ne (by decide : src ≠ out)]
  have hd' : c.addr dst = x.addr dst := by
    simp [c, b, a, Op.eval, Function.update_of_ne (by decide : dst ≠ left),
      Function.update_of_ne (by decide : dst ≠ out)]
  have hcl : c.addr left = x.addr src := by
    simp [c, b, a, Op.eval, Function.update_of_ne (by decide : left ≠ out)]
  have hco : c.addr out = x.addr dst := rfl
  have hsource_length : source.length = keys.length := by simpa using hperm.length_eq
  have hmodel : LocalPassModel keys source (x.scalars width) c := by
    refine ⟨hi.keys_mem, ?_, ?_, hsource_length,
      fun i hi => List.mem_range.mp (hperm.subset hi), hwc,
      ⟨[], 0, ?_, ?_, ?_, ?_, ?_, stableMergePrefix_empty keys source _⟩⟩
    · simpa only [localBuffers, hs, hd'] using hi.buffers
    · rw [hs]
      exact hse
    · intro j hj
      simp at hj
    · simp [hcr]
    · simp
    · simp [hcl, hs]
    · simp [hco, hd']
  obtain ⟨d, hd, hdframe⟩ := passLoop_exec c
    ((hc zero (by decide)).trans hz) ((hc one (by decide)).trans ho) (hwc.symm ▸ hw)
  have hdinv := hd
  obtain ⟨_, _, hdExact⟩ := hdinv
  obtain ⟨hoModel, hstop⟩ :=
    localPassLoop_correct hdExact hmodel hstable
      ((hc zero (by decide)).trans hz) ((hc one (by decide)).trans ho)
  obtain ⟨output, _, hout, houtLen, _, _, _, hp⟩ := hoModel.progress
  have hLen : output.length = keys.length := by rw [hstop, Nat.add_zero] at houtLen; exact houtLen
  have hper : output.Perm source := by
    have h := hp.perm
    rw [hLen, ← hsource_length, List.take_length] at h
    exact h
  let e := (Op.copyAddr left src).eval d
  let f := (Op.copyAddr src dst).eval e
  let g := (Op.copyAddr dst left).eval f
  let z := (Op.scalar (M := model) .add width width width).eval g
  have hswap : within swapBuffers d g 3 :=
    (primitive _ d).seq ((primitive _ e).seq (primitive _ f))
  have hwidth : within doubleWidth g z 1 := primitive _ _
  have ha : within (copyScalar remain len) x a 1 := primitive _ _
  have hb : within (copyRef left src) a b 1 := primitive _ _
  have hcExec : within (copyRef out dst) b c 1 := primitive _ _
  have he := ha.seq (hb.seq (hcExec.seq (hd.seq (hswap.seq hwidth))))
  obtain ⟨_, _, hex⟩ := he
  have heq : z = y := (Program.Exec.unique hex h).1
  rw [← heq]
  have hzbuf : z.addr src = d.addr dst ∧ z.addr dst = d.addr src := by
    simp (config := { decide := true }) [z, e, f, g, Op.eval]
  have hyw : z.scalars width = 2 * (x.scalars width : ℕ) := by
    have hwidth := hdframe.2.2.2.trans hwc
    simp [z, e, f, g, Op.eval, hwidth, two_mul]
  refine ⟨⟨?_, ?_, ⟨output, ?_, hper.trans hperm, ?_⟩⟩, ?_⟩
  · exact hoModel.keys_mem
  · unfold localBuffers
    rw [hzbuf.1, hzbuf.2]
    rcases hoModel.buffers with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  · have hmem₁ : z.values = d.values := rfl
    have hmem₂ : z.refs = d.refs := rfl
    rw [hzbuf.1]
    intro j hj
    obtain ⟨u, v, hu, hv, hva, hr⟩ := hout j hj
    exact ⟨u, v, hu, hv, by rw [hmem₁]; exact hva, by rw [hmem₂]; exact hr⟩
  · rw [hyw]
    exact hp.runs
  · have hh (i : Fin 11) (hi : i ≠ width) : z.scalars i = d.scalars i := by
      simp [z, e, f, g, Op.eval, Function.update_of_ne hi]
    exact ⟨(hh zero (by decide)).trans (hdframe.1.trans (hc zero (by decide))),
      (hh one (by decide)).trans (hdframe.2.1.trans (hc one (by decide))),
      (hh len (by decide)).trans (hdframe.2.2.1.trans (hc len (by decide))),
      hyw⟩

private theorem localOuter_correct
    {keys : List ℕ} {x y : MachineState (3 * keys.length)} {t : ℕ}
    (h : Program.Exec (instructionSet model (3 * keys.length) 8 11)
      (.loop (less width len) mergePass) x y t)
    (hi : LocalSortContents keys x) (hl : x.scalars len = keys.length)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) (hw : 0 < x.scalars width) :
    LocalSortContents keys y ∧ keys.length ≤ y.scalars width := by
  induction t using Nat.strong_induction_on generalizing x y with
  | _ t ih =>
    cases h with
    | loop_exit ht =>
      rw [less_holds, hl] at ht
      exact ⟨hi, Nat.le_of_not_gt ht⟩
    | @loop_iter _ _ _ b _ m n ht hbody hrest =>
      obtain ⟨hm, hz', ho', hl', hw'⟩ := localPass_correct hbody hi hl hz ho hw
      have hp : 0 < b.scalars width := by rw [hw']; exact Nat.mul_pos (by decide) hw
      exact ih n (by omega) hrest hm (hl'.trans hl) (hz'.trans hz) (ho'.trans ho) hp

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
  obtain ⟨a, ha, _, hinit⟩ := initEntries_correct keys (by omega)
  have hf := hinit.scalars
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

private theorem localEntries_permutation {n : ℕ} (hn : 0 < n)
    {x : MachineState (3 * n)} {indices : List ℕ}
    (h : LocalEntries x (localPos (x.addr src)) indices) (hlen : indices.length = n) :
    permutation x = indices := by
  cases hs : x.addr src with
  | none =>
    have hpos : 0 < indices.length := hlen ▸ hn
    obtain ⟨a, k, ha, hk, _, _⟩ := h 0 hpos
    have h₁ : a.val < 3 * n := a.isLt
    rw [hs] at ha
    change a.val = 3 * n + 0 at ha
    omega
  | some base =>
    unfold permutation
    rw [show x.addr resultReg = some base from hs]
    have hrange : List.range n = List.range indices.length := congrArg List.range hlen.symm
    simp only [Option.elim_some, hrange]
    calc
      _ = (List.range indices.length).filterMap (indices[·]?) := by
        apply List.filterMap_congr
        intro i hi
        have hi' := List.mem_range.mp hi
        obtain ⟨a, k, ha, hk, hv, _⟩ := h i hi'
        rw [hs] at ha
        change a.val = base.val + i at ha
        have hb : base.val + i < 3 * n := ha ▸ a.isLt
        rw [dite_eq_left hb, List.getElem?_eq_getElem hi']
        have he : (⟨base.val + i, hb⟩ : Fin (3 * n)) = a := Fin.ext ha.symm
        rw [he, hv, hk]
      _ = indices := List.filterMap_range_getElem?

private theorem localCode_correct (keys : List ℕ)
    (hn : 3 ≤ keys.length) :
    ∃ y, within code (inputState keys) y
      (19 * keys.length * Nat.clog 2 keys.length + 24 * keys.length +
        26 * Nat.clog 2 keys.length - 9) ∧
      (permutation y).Perm (List.range keys.length) ∧
      (permutation y).Pairwise (StableKeyOrder keys) := by
  let x := inputState keys
  have hnpos : 0 < keys.length := by omega
  obtain ⟨a, ha, harest, hi⟩ := initEntries_correct keys hnpos
  let b := (Op.copyData width one).eval a
  have hb : within (copyScalar width one) a b 1 := primitive _ _
  have hsc (i : Fin 11) (h₁ : i ≠ width) (h₂ : i ≠ remain) (h₃ : i ≠ lvalue) :
      b.scalars i = x.scalars i := by
    exact (show b.scalars i = a.scalars i from Function.update_of_ne h₁ _ _).trans
      (hi.scalars i h₂ h₃)
  have hz : b.scalars zero = 0 := hsc zero (by decide) (by decide) (by decide)
  have ho : b.scalars one = 1 := hsc one (by decide) (by decide) (by decide)
  have hl : b.scalars len = keys.length := hsc len (by decide) (by decide) (by decide)
  have hw : b.scalars width = 2 ^ (0 : ℕ) := by
    simp only [b, Op.eval, Function.update_self, pow_zero]
    exact hi.scalars one (by decide) (by decide)
  have hs : localPos (b.addr src) = keys.length := by
    change localPos (a.addr src) = _
    rw [hi.src]
    simp [inputState, hnpos, permBase, localPos]
  have hd : localPos (b.addr dst) = 2 * keys.length := by
    change localPos (a.addr dst) = _
    rw [hi.dst]
    have ht : dst ≠ src := by decide
    have hk : dst ≠ key := by decide
    simp [inputState, hnpos, scratchBase, localPos, ht, hk]
  have hbmodel : LocalSortContents keys b := by
    refine ⟨hi.keys_eq, Or.inl ⟨hs, hd⟩, ⟨List.range keys.length, ?_, .refl _, ?_⟩⟩
    · intro j hj
      simp only [List.length_range] at hj
      let i : Fin keys.length := ⟨j, hj⟩
      let ad : Fin (3 * keys.length) := ⟨keys.length + j, by omega⟩
      let adKey : Fin (3 * keys.length) := ⟨j, by omega⟩
      have hj' : i.val < keys.length - a.scalars remain := by simp [i, harest, hj]
      refine ⟨ad, adKey, by rw [hs], ?_, hi.values i hj', hi.refs i hj'⟩
      simp [adKey]
    · rw [hw, pow_zero]
      exact stableRuns_range keys
  obtain ⟨y, hy⟩ := outer_exec b hz ho hl hw
  have hyView := hy
  obtain ⟨_, _, hye⟩ := hyView
  obtain ⟨hf, hlarge⟩ := localOuter_correct hye hbmodel hl hz ho
    (by rw [hw]; decide)
  obtain ⟨indices, he, hperm, hord⟩ := hf.entries
  have hlen : indices.length = keys.length := by simpa using hperm.length_eq
  have hfinal := localEntries_permutation hnpos he hlen
  have ht : (instructionSet model (3 * keys.length) 8 11).Holds (less two len) x :=
    (less_holds x two len).2 (show 2 < keys.length from hn)
  have hex : within code x y
      (8 * keys.length + 3 + (1 + outerBudget 19 keys.length 0) + 1) := by
    unfold code
    exact Program.ExecWithin.branch_pos ht (ha.seq (hb.seq hy))
  obtain ⟨z, hzrun⟩ := code_exec keys hn
  have hzView := hzrun
  obtain ⟨_, _, ez⟩ := hzView
  obtain ⟨_, _, ey⟩ := hex
  have heq : z = y := (Program.Exec.unique ez ey).1
  subst z
  refine ⟨y, hzrun, ?_, ?_⟩
  · rw [hfinal]
    exact hperm
  · rw [hfinal]
    exact hord.finish (hlen.le.trans hlarge)

/-- The packed pointer-machine program returns the stable numeric permutation of the
original keys within the stated instruction bound, including its final halt. -/
theorem pointer_sorts (keys : List ℕ) (hn : 3 ≤ keys.length) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ 19 * keys.length * Nat.clog 2 keys.length + 24 * keys.length +
        26 * Nat.clog 2 keys.length - 8 ∧
      (pointerPermutation keys.length y).Perm (List.range keys.length) ∧
      (pointerPermutation keys.length y).Pairwise (StableKeyOrder keys) := by
  obtain ⟨y, ⟨t, ht, he⟩, hp, ho⟩ := localCode_correct keys hn
  refine ⟨_, t + 1, executes_compile he, by omega, ?_, ?_⟩
  · rwa [pointerPermutation_encode]
  · rwa [pointerPermutation_encode]

/-- The compiled pointer machine meets the buffered sorter's bound with one additional
instruction for the final halt. -/
theorem pointer_exec (keys : List ℕ) (hn : 3 ≤ keys.length) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ 19 * keys.length * Nat.clog 2 keys.length + 24 * keys.length +
        26 * Nat.clog 2 keys.length - 8 := by
  obtain ⟨_, t, ht, he⟩ := code_exec keys hn
  exact ⟨_, t + 1, executes_compile he, by omega⟩

private theorem shortCode_correct (keys : List ℕ) (hn : keys.length ≤ 1) :
    ∃ y, within code (inputState keys) y 6 ∧ permutation y = List.range keys.length := by
  let x := inputState keys
  let I := instructionSet model (3 * keys.length) 8 11
  have ht : ¬ I.Holds (less two len) x := by
    intro h
    have h' : 2 < keys.length := (less_holds x two len).mp h
    omega
  have ho : ¬ I.Holds (less one len) x := by
    intro h
    have h' : 1 < keys.length := (less_holds x one len).mp h
    omega
  by_cases hz : 0 < keys.length
  · let y := (Op.storeData src zero).eval x
    have hbody : within (instr (.storeData src zero)) x y 1 := primitive _ _
    have h := Program.ExecWithin.branch_pos (neg := .skip) ((less_holds x zero len).2 hz) hbody
    refine ⟨y, Program.ExecWithin.branch_neg ht (Program.ExecWithin.branch_neg ho h), ?_⟩
    have hs : keys.length = 1 := by omega
    cases keys with
    | nil => simp at hs
    | cons a as =>
      have has : as = [] := by simpa using hs
      subst as
      simp (config := { decide := true }) [y, x, Op.eval, inputState, permutation, permBase]
  · have hzero : keys.length = 0 := by omega
    have hnt : ¬ I.Holds (less zero len) x := fun h => hz ((less_holds x zero len).1 h)
    have h := Program.ExecWithin.branch_neg (pos := instr (.storeData src zero)) hnt
      (Program.ExecWithin.skip (I := I) (T := 0))
    refine ⟨x, Program.ExecWithin.branch_neg ht (Program.ExecWithin.branch_neg ho h), ?_⟩
    cases ha : x.addr resultReg <;> simp [permutation, hzero, ha]

/-- The packed pointer-machine sorter handles the empty list and singleton within
seven instructions, including halt. The output is the stable permutation of the input. -/
theorem pointer_sorts_short (keys : List ℕ) (hn : keys.length ≤ 1) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ 7 ∧ pointerPermutation keys.length y = List.range keys.length := by
  obtain ⟨y, ⟨t, ht, he⟩, hy⟩ := shortCode_correct keys hn
  exact ⟨_, t + 1, executes_compile he, by omega, (pointerPermutation_encode y _).trans hy⟩

private theorem twoCode_correct (a b : ℕ) :
    ∃ y, within code (inputState [a, b]) y 12 ∧
      (permutation y).Perm (List.range 2) ∧ (permutation y).Pairwise (StableKeyOrder [a, b]) := by
  let x := inputState [a, b]
  let v := (Op.loadData lvalue key).eval x
  let w := (Op.move .next key key).eval v
  let z := (Op.loadData rvalue key).eval w
  let s := (Op.copyAddr out src).eval z
  have ht : ¬ (instructionSet model 6 8 11).Holds (less two len) x := by
    rw [less_holds]
    change ¬ (2 : ℕ) < 2
    decide
  have ho : (instructionSet model 6 8 11).Holds (less one len) x := by
    rw [less_holds]
    change (1 : ℕ) < 2
    decide
  have hreads : s.scalars lvalue = a ∧ s.scalars rvalue = b := ⟨rfl, rfl⟩
  have prefixExec (q : SortCode) {y : MachineState 6} {T : ℕ}
      (h : within q s y T) :
      within (instr (.loadData lvalue key) ▷ next key ▷ instr (.loadData rvalue key) ▷
        copyRef out src ▷ q) x y (1 + (1 + (1 + (1 + T)))) :=
    (primitive _ x).seq ((primitive _ v).seq ((primitive _ w).seq ((primitive _ z).seq h)))
  let writes (i j : Fin 11) := instr (.storeData out i) ▷ next out ▷ instr (.storeData out j)
  have put (i j : Fin 11) :
      ∃ y, within (writes i j) s y 3 ∧ permutation y = [s.scalars i, s.scalars j] := by
    let t := (Op.storeData out i).eval s
    let u := (Op.move .next out out).eval t
    let y := (Op.storeData out j).eval u
    refine ⟨y, (primitive _ s).seq ((primitive _ t).seq (primitive _ u)), ?_⟩
    rfl
  have finish {y : MachineState 6} (h : within sortTwo x y 9) : within code x y 12 := by
    have hp := Program.ExecWithin.branch_pos
      (neg := .branch (less zero len) (instr (.storeData src zero)) .skip) ho h
    exact Program.ExecWithin.branch_neg ht hp
  by_cases hab : b < a
  · have hcmp : (instructionSet model 6 8 11).Holds (less rvalue lvalue) s :=
      (less_holds s _ _).2 (by simpa only [hreads.1, hreads.2] using hab)
    obtain ⟨y, hy, hp⟩ := put one zero
    have hsort : within sortTwo x y 8 := by
      unfold sortTwo
      have h := Program.ExecWithin.branch_pos (t := less rvalue lvalue)
        (neg := writes zero one) hcmp hy
      exact prefixExec _ h
    refine ⟨y, finish (hsort.mono (by decide)), ?_, ?_⟩
    · rw [hp, show s.scalars one = 1 from rfl, show s.scalars zero = 0 from rfl]
      exact List.Perm.swap 0 1 []
    · rw [hp, show s.scalars one = 1 from rfl, show s.scalars zero = 0 from rfl]
      simp [StableKeyOrder, hab]
  · have hcmp : ¬ (instructionSet model 6 8 11).Holds (less rvalue lvalue) s :=
      fun h => hab (by simpa only [hreads.1, hreads.2] using (less_holds s _ _).1 h)
    obtain ⟨y, hy, hp⟩ := put zero one
    have hsort : within sortTwo x y 9 := by
      unfold sortTwo
      have h := Program.ExecWithin.branch_neg (t := less rvalue lvalue)
        (pos := writes one zero) hcmp hy
      exact prefixExec _ h
    refine ⟨y, finish hsort, ?_, ?_⟩
    · rw [hp, show s.scalars one = 1 from rfl, show s.scalars zero = 0 from rfl]
      rfl
    · rw [hp, show s.scalars one = 1 from rfl, show s.scalars zero = 0 from rfl]
      have hle := Nat.le_of_not_gt hab
      simp [StableKeyOrder]
      omega

/-- The packed pointer-machine sorter returns the stable permutation of two keys. -/
theorem pointer_sorts_two (a b : ℕ) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState [a, b])) y t ∧
      t ≤ 13 ∧ (pointerPermutation 2 y).Perm (List.range 2) ∧
      (pointerPermutation 2 y).Pairwise (StableKeyOrder [a, b]) := by
  obtain ⟨y, ⟨t, ht, he⟩, hp, hs⟩ := twoCode_correct a b
  exact ⟨_, t + 1, executes_compile he, by omega,
    (pointerPermutation_encode y _) ▸ hp, (pointerPermutation_encode y _) ▸ hs⟩

/-- The packed pointer-machine sorter returns a stable permutation for lengths up to two.
The bound includes the final halt. -/
theorem pointer_sorts_small (keys : List ℕ) (hn : keys.length ≤ 2) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ (if keys.length < 2 then 7 else 13) ∧
      (pointerPermutation keys.length y).Perm (List.range keys.length) ∧
      (pointerPermutation keys.length y).Pairwise (StableKeyOrder keys) := by
  by_cases h : keys.length < 2
  · obtain ⟨y, t, hr, ht, he⟩ := pointer_sorts_short keys (by omega)
    have hord : (List.range keys.length).Pairwise (StableKeyOrder keys) := by
      have hs : keys.length = 0 ∨ keys.length = 1 := by omega
      rcases hs with hs | hs <;> rw [hs] <;> simp
    refine ⟨y, t, hr, by simpa [h] using ht, ?_, ?_⟩
    · rw [he]
    · rw [he]
      exact hord
  · have hn' : keys.length = 2 := by omega
    match keys with
    | a :: b :: rest =>
      have hr : rest = [] := by simpa using hn'
      subst rest
      obtain ⟨y, t, hr, ht, hp, ho⟩ := pointer_sorts_two a b
      exact ⟨y, t, hr, ht, hp, ho⟩

/-- Small packed pointer-machine inputs halt within seven instructions for lengths zero and
one, or thirteen instructions for length two. -/
theorem pointer_exec_small (keys : List ℕ) (hn : keys.length ≤ 2) :
    ∃ y t, PointerMachine.Executes (compile code).program (encode (inputState keys)) y t ∧
      t ≤ if keys.length < 2 then 7 else 13 := by
  obtain ⟨y, t, hr, ht, _, _⟩ := pointer_sorts_small keys hn
  exact ⟨y, t, hr, ht⟩


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

-- Buffer entries retain both the numerical index and the address of the original key.
-- Prepared keys start at address zero, so both words have the same numerical value.
private def WordEntries (mem : ℕ → ℕ) (p : ℕ) : List ℕ → Prop
  | [] => True
  | i :: is => mem p = i ∧ mem (p + 1) = i ∧ WordEntries mem (p + 2) is

private theorem wordEntries_append {mem : ℕ → ℕ} {p : ℕ} (a b : List ℕ) :
    WordEntries mem p (a ++ b) ↔
      WordEntries mem p a ∧ WordEntries mem (p + 2 * a.length) b := by
  induction a generalizing p with
  | nil => simp [WordEntries]
  | cons i is ih =>
    simp only [List.cons_append, List.length_cons, WordEntries, ih]
    have h : p + 2 + 2 * is.length = p + 2 * (is.length + 1) := by omega
    rw [h]
    tauto

private theorem wordEntries_congr {mem mem' : ℕ → ℕ} {p : ℕ} {is : List ℕ}
    (h : ∀ j, p ≤ j → j < p + 2 * is.length → mem' j = mem j)
    (hs : WordEntries mem p is) : WordEntries mem' p is := by
  induction is generalizing p with
  | nil => trivial
  | cons i is ih =>
    have hl : (i :: is).length = is.length + 1 := rfl
    have hp := h p (by omega) (by rw [hl]; omega)
    have hp' := h (p + 1) (by omega) (by rw [hl]; omega)
    refine ⟨hp.trans hs.1, hp'.trans hs.2.1, ih (p := p + 2) ?_ hs.2.2⟩
    intro j hj hlt
    exact h j (by omega) (by rw [hl]; omega)

private theorem wordEntries_iff_getElem {mem : ℕ → ℕ} {p : ℕ} {is : List ℕ} :
    WordEntries mem p is ↔ ∀ j (hj : j < is.length),
      mem (p + 2 * j) = is[j] ∧ mem (p + 2 * j + 1) = is[j] := by
  induction is generalizing p with
  | nil => simp [WordEntries]
  | cons i is ih =>
    constructor
    · intro h j hj
      cases j with
      | zero => simpa using And.intro h.1 h.2.1
      | succ j =>
        have hh := (ih (p := p + 2)).mp h.2.2 j (by simpa using hj)
        have he : p + 2 * (j + 1) = p + 2 + 2 * j := by omega
        simpa [he] using hh
    · intro h
      have hh := h 0 (by simp)
      refine ⟨by simpa using hh.1, by simpa using hh.2, (ih (p := p + 2)).mpr ?_⟩
      intro j hj
      have hh := h (j + 1) (Nat.succ_lt_succ hj)
      have he : p + 2 * (j + 1) = p + 2 + 2 * j := by omega
      simpa [he] using hh

private theorem WordInitInv.entries {keys : List ℕ} {k : ℕ} {x : WordData}
    (h : WordInitInv keys k x) : WordEntries x.mem keys.length (List.range k) := by
  apply wordEntries_iff_getElem.mpr
  intro j hj
  simp only [List.length_range] at hj
  simpa only [List.getElem_range] using h.entries_eq j hj

private theorem wordEmit_mem {x : WordData} {head item : Fin 8} {count : Fin 11}
    (h : x.regs (ptrReg item) = x.mem (x.regs (ptrReg head))) :
    (wordEmit x head item count).mem =
      Function.update (Function.update x.mem (x.regs (ptrReg out)) (x.regs (ptrReg item)))
        (x.regs (ptrReg out) + 1) (x.regs (ptrReg item)) := by
  have hp (r : Fin 8) : ptrReg r ≠ scalarReg lvalue := by
    intro h
    have hr := r.isLt
    have he := congrArg (fun r : Fin 20 => r.val) h
    change r.val = 8 + lvalue.val at he
    omega
  simp [wordEmit, wordWriteEntry, Function.update_of_ne (hp out),
    Function.update_of_ne (hp item), h]

-- Extend the previously written prefix after emitting its next entry.
private theorem wordEntries_emit {mem : ℕ → ℕ} {base : ℕ} {emitted : List ℕ}
    (h : WordEntries mem base emitted) (i : ℕ) :
    let p := base + 2 * emitted.length
    WordEntries (Function.update (Function.update mem p i) (p + 1) i) base (emitted ++ [i]) := by
  let p := base + 2 * emitted.length
  apply (wordEntries_append emitted [i]).mpr
  refine ⟨wordEntries_congr ?_ h, ?_⟩
  · intro j _ hj
    have h₁ : j ≠ p := by omega
    have h₂ : j ≠ p + 1 := by omega
    change Function.update (Function.update mem p i) (p + 1) i j = mem j
    rw [Function.update_of_ne h₂, Function.update_of_ne h₁]
  · change WordEntries (Function.update (Function.update mem p i) (p + 1) i) p [i]
    simp [WordEntries]

private def wordKeyMem (keys : List ℕ) (x : WordData) : Prop :=
  ∀ i (hi : i < keys.length), x.mem i = keys[i]

private theorem wordKeyMem_getD {keys : List ℕ} {x : WordData}
    (h : wordKeyMem keys x) {i : ℕ} (hi : i < keys.length) :
    x.mem i = keys.getD i 0 := by
  simpa only [List.getD_eq_getElem keys 0 hi] using h i hi

private abbrev sideHead (rightSide : Bool) := if rightSide then right else left
private abbrev sideItem (rightSide : Bool) := if rightSide then rkey else lkey
private abbrev sideCount (rightSide : Bool) := if rightSide then rcount else lcount

-- Cursor lengths and intervals determine which cells a merge can read or overwrite.
private structure WordMergeContents (keys : List ℕ) (base : ℕ) (side : Bool) (L R emitted : List ℕ)
    (x : WordData) : Prop where
  keys_mem : wordKeyMem keys x
  keys_separate : keys.length ≤ base
  left_entries : WordEntries x.mem (x.regs (ptrReg (sideHead side))) L
  right_entries : WordEntries x.mem (x.regs (ptrReg (sideHead (!side)))) R
  output_entries : WordEntries x.mem base emitted
  output_cursor : x.regs (ptrReg out) = base + 2 * emitted.length
  left_count : x.regs (scalarReg (sideCount side)) = L.length
  right_count : x.regs (scalarReg (sideCount (!side))) = R.length
  left_separate : x.regs (ptrReg (sideHead side)) + 2 * L.length ≤ base ∨
    x.regs (ptrReg out) + 2 * (L.length + R.length) ≤ x.regs (ptrReg (sideHead side))
  right_separate : x.regs (ptrReg (sideHead (!side))) + 2 * R.length ≤ base ∨
    x.regs (ptrReg out) + 2 * (L.length + R.length) ≤ x.regs (ptrReg (sideHead (!side)))

private theorem WordMergeContents.flip {keys : List ℕ} {base : ℕ} {side : Bool}
    {L R emitted : List ℕ} {x : WordData} (h : WordMergeContents keys base side L R emitted x) :
    WordMergeContents keys base (!side) R L emitted x := by
  refine ⟨h.keys_mem, h.keys_separate, h.right_entries, ?_, h.output_entries, h.output_cursor,
    h.right_count, ?_, ?_, ?_⟩
  · simpa only [Bool.not_not] using h.left_entries
  · simpa only [Bool.not_not] using h.left_count
  · simpa only [Nat.add_comm R.length L.length] using h.right_separate
  · simpa only [Bool.not_not, Nat.add_comm R.length L.length] using h.left_separate

private theorem wordEmit_correct {keys : List ℕ} {base i : ℕ} {L R emitted : List ℕ}
    {x : WordData} (side : Bool) (h : WordMergeContents keys base side (i :: L) R emitted x)
    (hi : x.regs (ptrReg (sideItem side)) = i) :
    WordMergeContents keys base side L R (emitted ++ [i])
      (wordEmit x (sideHead side) (sideItem side) (sideCount side)) := by
  let y := wordEmit x (sideHead side) (sideItem side) (sideCount side)
  let p := x.regs (ptrReg out)
  have hm : y.mem = Function.update (Function.update x.mem p i) (p + 1) i := by
    rw [wordEmit_mem (hi.trans h.left_entries.1.symm), hi]
  have hleft : y.regs (ptrReg (sideHead side)) = x.regs (ptrReg (sideHead side)) + 2 := by
    cases side <;>
      simp (config := { decide := true }) [y, wordEmit, wordWriteEntry, wordStride,
      ptrReg, scalarReg, fieldAddr, sideHead, sideItem, sideCount]
  have hright : y.regs (ptrReg (sideHead (!side))) = x.regs (ptrReg (sideHead (!side))) := by
    cases side <;>
      simp (config := { decide := true }) [y, wordEmit, wordWriteEntry, wordStride,
      ptrReg, scalarReg, fieldAddr, sideHead, sideItem, sideCount]
  have hout : y.regs (ptrReg out) = p + 2 := by
    cases side <;>
      simp (config := { decide := true }) [y, p, wordEmit, wordWriteEntry, wordStride,
      ptrReg, scalarReg, fieldAddr, sideHead, sideItem, sideCount]
  have hlc : y.regs (scalarReg (sideCount side)) = L.length := by
    have hval : y.regs (scalarReg (sideCount side)) =
        x.regs (scalarReg (sideCount side)) - 1 := by simp [y, wordEmit]
    rw [hval, h.left_count, List.length_cons, Nat.add_sub_cancel]
  have hrc : y.regs (scalarReg (sideCount (!side))) = R.length := by
    cases side <;>
      simpa (config := { decide := true }) [y, wordEmit, wordWriteEntry, wordStride, ptrReg,
        scalarReg, fieldAddr, sideHead, sideItem, sideCount] using h.right_count
  have hcursor : p = base + 2 * emitted.length := h.output_cursor
  have hls := h.left_separate
  have hrs := h.right_separate
  simp only [List.length_cons] at hls hrs
  have hframe (j : ℕ) (h₁ : j ≠ p) (h₂ : j ≠ p + 1) : y.mem j = x.mem j := by
    rw [hm, Function.update_of_ne h₂, Function.update_of_ne h₁]
  refine ⟨?_, h.keys_separate, ?_, ?_, ?_, ?_, hlc, hrc, ?_, ?_⟩
  · intro j hj
    have hn := h.keys_separate
    exact (hframe j (by omega) (by omega)).trans (h.keys_mem j hj)
  · rw [hleft]
    apply wordEntries_congr _ h.left_entries.2.2
    intro j h₁ h₂
    exact hframe j (by omega) (by omega)
  · rw [hright]
    apply wordEntries_congr _ h.right_entries
    intro j h₁ h₂
    exact hframe j (by omega) (by omega)
  · rw [hm, hcursor]
    exact wordEntries_emit h.output_entries i
  · rw [hout, hcursor, List.length_append]
    simp
    omega
  · rw [hleft, hout]
    dsimp only [p]
    omega
  · rw [hright, hout]
    dsimp only [p]
    omega

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
  out_mono : x.regs (ptrReg out) ≤ y.regs (ptrReg out)
  memory : ∀ i, i < x.regs (ptrReg out) ∨ y.regs (ptrReg out) ≤ i → y.mem i = x.mem i
  left_zero : x.regs (scalarReg lcount) = 0 → y.regs (scalarReg lcount) = 0
  fixed : ∀ i ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
    scalarReg remain} : Finset (Fin 20)), y.regs i = x.regs i

private theorem WordMergeFrame.refl (x : WordData) : WordMergeFrame x x :=
  ⟨rfl, rfl, le_rfl, fun _ _ => rfl, id, fun _ _ => rfl⟩

private theorem WordMergeFrame.trans {x y z : WordData}
    (hxy : WordMergeFrame x y) (hyz : WordMergeFrame y z) : WordMergeFrame x z := by
  refine ⟨hyz.right_end.trans hxy.right_end, hyz.out_end.trans hxy.out_end,
    hxy.out_mono.trans hyz.out_mono, ?_, fun hx => hyz.left_zero (hxy.left_zero hx),
    fun i hi => (hyz.fixed i hi).trans (hxy.fixed i hi)⟩
  intro i hi
  rcases hi with hi | hi
  · exact (hyz.memory i (Or.inl (hi.trans_le hxy.out_mono))).trans (hxy.memory i (Or.inl hi))
  · exact (hyz.memory i (Or.inr hi)).trans (hxy.memory i (Or.inr (hyz.out_mono.trans hi)))


private theorem wordEmit_room {w limit : ℕ} {x : WordData} (rightSide : Bool)
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hpos : 0 < x.regs (scalarReg (sideCount rightSide))) :
    ∃ y, wordWithin w (lowerWordCode (emit (sideHead rightSide) (sideItem rightSide)
      (sideCount rightSide))) x y 7 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧
      WordMergeFrame x y ∧ y = wordEmit x (sideHead rightSide)
        (sideItem rightSide) (sideCount rightSide) := by
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
  have houtEq : y.regs (ptrReg out) = x.regs (ptrReg out) + 2 := by
    cases rightSide <;>
      simp (config := { decide := true }) [y, head, item, count, sideHead, sideItem, sideCount,
        wordEmit, wordWriteEntry, wordStride, ptrReg, scalarReg, fieldAddr]
  have hmem (i : ℕ) (hi : i < x.regs (ptrReg out) ∨ y.regs (ptrReg out) ≤ i) :
      y.mem i = x.mem i := by
    rw [houtEq] at hi
    have hp : i ≠ x.regs (ptrReg out) := by omega
    have hq : i ≠ x.regs (ptrReg out) + 1 := by omega
    have h₁ : ptrReg out ≠ scalarReg lvalue := by decide
    cases rightSide <;>
      simp [y, head, item, count, sideHead, sideItem, sideCount, wordEmit, wordWriteEntry,
        Function.update_of_ne h₁, Function.update_of_ne hp, Function.update_of_ne hq]
  have houtMono : x.regs (ptrReg out) ≤ y.regs (ptrReg out) := by rw [houtEq]; omega
  refine ⟨y, he, ⟨?_, ?_, ?_, hz.trans hx.zero_eq, ho.trans hx.one_eq,
    ht.trans hx.two_eq⟩, ?_, ⟨?_, ?_, houtMono, hmem, ?_, hfixed⟩, rfl⟩ <;>
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

private theorem wordMergeReadFrame.frame {x y : WordData} (h : wordMergeReadFrame x y)
    (hm : y.mem = x.mem) : WordMergeFrame x y := by
  have hr : y.regs (ptrReg right) = x.regs (ptrReg right) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have ho : y.regs (ptrReg out) = x.regs (ptrReg out) :=
    h _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨by rw [hr, h.right_count], by rw [ho, h.size], by rw [ho],
    fun i _ => congrFun hm i, by rw [h.left_count]; exact id, ?_⟩
  intro i hi
  have good : ∀ j ∈ ({ptrReg src, ptrReg dst, scalarReg len, scalarReg width,
      scalarReg remain} : Finset (Fin 20)), j ≠ fieldAddr ∧ j ≠ ptrReg lkey ∧
      j ≠ ptrReg rkey ∧ j ≠ scalarReg lvalue ∧ j ≠ scalarReg rvalue := by decide
  obtain ⟨a, b, c, d, e⟩ := good i hi
  exact h i a b c d e


private def wordRightWins (x : WordData) : Prop :=
  0 < x.regs (scalarReg rcount) ∧
    x.mem (x.mem (x.regs (ptrReg right) + 1)) <
      x.mem (x.mem (x.regs (ptrReg left) + 1))

-- Describe the selected branch and the values read by the actual RAM instructions.
private structure WordEmission (x y : WordData) (side : Bool) : Prop where
  reads : ∃ z, wordMergeReadFrame x z ∧ z.mem = x.mem ∧
    z.regs (ptrReg (sideItem side)) = x.mem (x.regs (ptrReg (sideHead side)) + 1) ∧
    y = wordEmit z (sideHead side) (sideItem side) (sideCount side)

private theorem wordLoadRef_mem (x : WordData) (d r : Fin 8) :
    (wordLoadRef x d r).mem = x.mem := rfl

private theorem wordLoadRef_value (x : WordData) (d r : Fin 8) :
    (wordLoadRef x d r).regs (ptrReg d) = x.mem (x.regs (ptrReg r) + 1) := by
  simp only [wordLoadRef, Cslib.WordRAM.Data.set_regs, Function.update_self]

private theorem wordMergeStep_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hl : 0 < x.regs (scalarReg lcount)) :
    ∃ y, wordWithin w (lowerWordCode mergeStep) x y 16 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y ∧
      ∃ side, (side = true ↔ wordRightWins x) ∧ WordEmission x y side := by
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
    have haddr (r : Fin 8) (h₁ : ptrReg r ≠ fieldAddr) (h₂ : ptrReg r ≠ ptrReg lkey) :
        a.regs (ptrReg r) = x.regs (ptrReg r) := by
      simp [a, wordLoadRef, Function.update_of_ne h₁, Function.update_of_ne h₂]
    have hleft : d.regs (ptrReg lkey) = x.mem (x.regs (ptrReg left) + 1) := by
      have hb' : b.regs (ptrReg lkey) = a.regs (ptrReg lkey) := by
        simp [b, wordLoadRef, Function.update_of_ne (by decide : ptrReg lkey ≠ fieldAddr),
          Function.update_of_ne (by decide : ptrReg lkey ≠ ptrReg rkey)]
      have hd' : d.regs (ptrReg lkey) = b.regs (ptrReg lkey) := by
        simp [d, c, Function.update_of_ne (by decide : ptrReg lkey ≠ scalarReg lvalue),
          Function.update_of_ne (by decide : ptrReg lkey ≠ scalarReg rvalue)]
      exact hd'.trans (hb'.trans (wordLoadRef_value x lkey left))
    have hright : d.regs (ptrReg rkey) = x.mem (x.regs (ptrReg right) + 1) := by
      have hd' : d.regs (ptrReg rkey) = b.regs (ptrReg rkey) := by
        simp [d, c, Function.update_of_ne (by decide : ptrReg rkey ≠ scalarReg lvalue),
          Function.update_of_ne (by decide : ptrReg rkey ≠ scalarReg rvalue)]
      rw [hd', show b.regs (ptrReg rkey) = a.mem (a.regs (ptrReg right) + 1) from
        wordLoadRef_value a rkey right, haddr right (by decide) (by decide)]
      rfl
    have hlval : d.regs (scalarReg lvalue) = x.mem (x.mem (x.regs (ptrReg left) + 1)) := by
      have hd' : d.regs (scalarReg lvalue) = b.mem (b.regs (ptrReg lkey)) := by
        simp [d, c, Function.update_of_ne (by decide : scalarReg lvalue ≠ scalarReg rvalue)]
      have hdMem : b.mem = x.mem := rfl
      rw [hd', hdMem, ← hleft]
      exact congrArg x.mem (by
        simp [d, c, Function.update_of_ne (by decide : ptrReg lkey ≠ scalarReg lvalue),
          Function.update_of_ne (by decide : ptrReg lkey ≠ scalarReg rvalue)])
    have hrval : d.regs (scalarReg rvalue) = x.mem (x.mem (x.regs (ptrReg right) + 1)) := by
      have hd' : d.regs (scalarReg rvalue) = c.mem (c.regs (ptrReg rkey)) := by simp [d]
      have hcMem : c.mem = x.mem := rfl
      rw [hd', hcMem, ← hright]
      exact congrArg x.mem (by
        simp [d, Function.update_of_ne (by decide : ptrReg rkey ≠ scalarReg rvalue)])
    let cmp := Cond.lt (scalarReg rvalue) (scalarReg lvalue)
    have hchoice : cmp.Holds d ↔ wordRightWins x := by
      change d.regs (scalarReg rvalue) < d.regs (scalarReg lvalue) ↔ _
      rw [hrval, hlval]
      simp [wordRightWins, hr]
    by_cases hcmp : cmp.Holds d
    · obtain ⟨y, hy, hyr, hs, hf, heq⟩ := wordEmit_room true hfit (hdf.room hx)
        (by simpa only [sideCount, ite_true, hdf.right_count] using hr)
      have hbranch := Cslib.Program.ExecWithin.branch_pos (t := cmp)
        (neg := lowerWordCode (emit left lkey lcount)) hcmp hy
      refine ⟨y, ?_, hyr, hs.trans hdf.size, (hdf.frame rfl).trans hf, ?_⟩
      · exact (ha.seq (Cslib.Program.ExecWithin.branch_pos (t := t)
          (neg := lowerWordCode (emit left lkey lcount)) ht (hcompare.seq hbranch))).mono
          (show 15 ≤ 16 by decide)
      · exact ⟨true, by simp [hchoice.mp hcmp], ⟨⟨d, hdf, rfl, hright, heq⟩⟩⟩
    · obtain ⟨y, hy, hyr, hs, hf, heq⟩ := wordEmit_room false hfit (hdf.room hx)
        (by simpa only [sideCount, Bool.false_eq_true, ite_false, hdf.left_count] using hl)
      have hbranch := Cslib.Program.ExecWithin.branch_neg (t := cmp)
        (pos := lowerWordCode (emit right rkey rcount)) hcmp hy
      refine ⟨y, ?_, hyr, hs.trans hdf.size, (hdf.frame rfl).trans hf, ?_⟩
      · have houter := Cslib.Program.ExecWithin.branch_pos (t := t)
          (neg := lowerWordCode (emit left lkey lcount)) ht (hcompare.seq hbranch)
        exact ha.seq houter
      · refine ⟨false, ?_, ⟨⟨d, hdf, rfl, hleft, heq⟩⟩⟩
        simp only [Bool.false_eq_true, false_iff]
        exact fun h => hcmp (hchoice.mpr h)
  · have ht : ¬t.Holds a := by
      change ¬a.regs (scalarReg zero) < a.regs (scalarReg rcount)
      rwa [haroom.zero_eq, haf.right_count]
    obtain ⟨y, hy, hyr, hs, hf, heq⟩ := wordEmit_room false hfit haroom
      (by simpa only [sideCount, Bool.false_eq_true, ite_false, haf.left_count] using hl)
    have hbranch := Cslib.Program.ExecWithin.branch_neg (t := t)
      (pos := lowerWordCode (compareHeads ▷
        .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount))) ht hy
    exact ⟨y, (ha.seq hbranch).mono (show 11 ≤ 16 by decide), hyr, hs.trans haf.size,
      (haf.frame rfl).trans hf, false, by simp [wordRightWins, hr],
      ⟨⟨a, haf, rfl, wordLoadRef_value x lkey left, heq⟩⟩⟩

private theorem wordDrainRight_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x)
    (hr : 0 < x.regs (scalarReg rcount)) :
    ∃ y, wordWithin w (lowerWordCode drainRight) x y 16 ∧ WordMergeRoom limit y ∧
      wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y ∧ WordEmission x y true := by
  let a := wordLoadRef x rkey right
  have ha := wordLoadRef_exec x rkey right hx.one_eq
    (hfit.of_le (by have := hx.right_room; omega))
  have hf : wordMergeReadFrame x a := by
    intro i h₁ _ h₃ _ _
    simp [a, wordLoadRef, Function.update_of_ne h₁, Function.update_of_ne h₃]
  obtain ⟨y, he, hy, hs, hg, heq⟩ := wordEmit_room true hfit (hf.room hx)
    (by simpa only [sideCount, ite_true, hf.right_count] using hr)
  exact ⟨y, (ha.seq he).mono (show 9 ≤ 16 by decide), hy, hs.trans hf.size, (hf.frame rfl).trans hg,
    ⟨⟨a, hf, rfl, wordLoadRef_value x rkey right, heq⟩⟩⟩

private theorem WordMergeContents.read {keys : List ℕ} {base : ℕ} {side : Bool}
    {L R emitted : List ℕ} {x y : WordData}
    (h : WordMergeContents keys base side L R emitted x) (hf : wordMergeReadFrame x y)
    (hm : y.mem = x.mem) : WordMergeContents keys base side L R emitted y := by
  have h₁ : y.regs (ptrReg (sideHead side)) = x.regs (ptrReg (sideHead side)) := by
    cases side <;> exact hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h₂ : y.regs (ptrReg (sideHead (!side))) = x.regs (ptrReg (sideHead (!side))) := by
    cases side <;> exact hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h₃ : y.regs (scalarReg (sideCount side)) = x.regs (scalarReg (sideCount side)) := by
    cases side <;> exact hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h₄ : y.regs (scalarReg (sideCount (!side))) = x.regs (scalarReg (sideCount (!side))) := by
    cases side <;> exact hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h₅ : y.regs (ptrReg out) = x.regs (ptrReg out) :=
    hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, h.keys_separate, ?_, ?_, hm.symm ▸ h.output_entries,
    h₅.trans h.output_cursor, h₃.trans h.left_count, h₄.trans h.right_count, ?_, ?_⟩
  · intro i hi
    rw [hm]
    exact h.keys_mem i hi
  · rw [hm, h₁]
    exact h.left_entries
  · rw [hm, h₂]
    exact h.right_entries
  · rw [h₁, h₅]
    exact h.left_separate
  · rw [h₂, h₅]
    exact h.right_separate

private theorem WordEmission.correct {keys : List ℕ} {base i : ℕ} {side : Bool}
    {L R emitted : List ℕ} {x y : WordData}
    (h : WordEmission x y side) (hc : WordMergeContents keys base side (i :: L) R emitted x) :
    WordMergeContents keys base side L R (emitted ++ [i]) y := by
  obtain ⟨z, hf, hm, href, rfl⟩ := h.reads
  exact wordEmit_correct side (hc.read hf hm) (href.trans hc.left_entries.2.1)

private def keyLE (keys : List ℕ) (a b : ℕ) : Bool :=
  decide (keys.getD a 0 ≤ keys.getD b 0)

private structure WordMergeModel (keys : List ℕ) (base : ℕ) (goal : List ℕ)
    (x : WordData) : Prop where
  runs : ∃ L R emitted, WordMergeContents keys base false L R emitted x ∧
    emitted ++ List.merge L R (keyLE keys) = goal

private theorem wordMergeModel_merge_step {keys : List ℕ} {base : ℕ} {goal : List ℕ}
    {x y : WordData} (h : WordMergeModel keys base goal x)
    (hindex : ∀ i ∈ goal, i < keys.length) (hp : 0 < x.regs (scalarReg lcount))
    (hstep : ∃ side, (side = true ↔ wordRightWins x) ∧ WordEmission x y side) :
    WordMergeModel keys base goal y := by
  obtain ⟨L, R, emitted, hc, he⟩ := h.runs
  obtain ⟨side, hchoice, hy⟩ := hstep
  cases L with
  | nil =>
    have hl : x.regs (scalarReg lcount) = 0 := hc.left_count
    omega
  | cons i L =>
    cases R with
    | nil =>
      have hz : x.regs (scalarReg rcount) = 0 := hc.right_count
      have hs : side = false := by
        cases side
        · rfl
        · have := (hchoice.mp rfl).1
          omega
      subst side
      refine ⟨⟨L, [], emitted ++ [i], hy.correct hc, ?_⟩⟩
      simpa only [List.merge_right, List.append_assoc, List.singleton_append] using he
    | cons j R =>
      have hmem (a : ℕ) (ha : a ∈ (i :: L) ++ (j :: R)) : a < keys.length := by
        apply hindex
        rw [← he]
        exact List.mem_append_right _ ((List.merge_perm_append _).symm.subset ha)
      have hi := hmem i (List.mem_append_left _ List.mem_cons_self)
      have hj := hmem j (List.mem_append_right _ List.mem_cons_self)
      have hr : 0 < x.regs (scalarReg rcount) := by
        rw [show x.regs (scalarReg rcount) = (j :: R).length from hc.right_count]
        simp
      have hcmp : wordRightWins x ↔ keys.getD j 0 < keys.getD i 0 := by
        change 0 < x.regs (scalarReg rcount) ∧
          x.mem (x.mem (x.regs (ptrReg right) + 1)) <
            x.mem (x.mem (x.regs (ptrReg left) + 1)) ↔ _
        rw [show x.mem (x.regs (ptrReg right) + 1) = j from hc.right_entries.2.1,
          show x.mem (x.regs (ptrReg left) + 1) = i from hc.left_entries.2.1,
          wordKeyMem_getD hc.keys_mem hi, wordKeyMem_getD hc.keys_mem hj]
        simp [hr]
      cases side with
      | false =>
        have hle : keys.getD i 0 ≤ keys.getD j 0 :=
          Nat.le_of_not_gt (fun h => by have := hchoice.mpr (hcmp.mpr h); contradiction)
        refine ⟨⟨L, j :: R, emitted ++ [i], hy.correct hc, ?_⟩⟩
        rw [List.cons_merge_cons] at he
        simpa only [keyLE, decide_eq_true hle, ite_true, List.append_assoc,
          List.singleton_append] using he
      | true =>
        have hlt := hcmp.mp (hchoice.mp rfl)
        have hc' := (hy.correct hc.flip).flip
        refine ⟨⟨i :: L, R, emitted ++ [j], hc', ?_⟩⟩
        rw [List.cons_merge_cons] at he
        simpa only [keyLE, decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_eq_true,
          ite_false, List.append_assoc, List.singleton_append] using he

private theorem wordMergeModel_drain_step {keys : List ℕ} {base : ℕ} {goal : List ℕ}
    {x y : WordData} (h : WordMergeModel keys base goal x)
    (hl : x.regs (scalarReg lcount) = 0) (hr : 0 < x.regs (scalarReg rcount))
    (hy : WordEmission x y true) : WordMergeModel keys base goal y := by
  obtain ⟨L, R, emitted, hc, he⟩ := h.runs
  have hL : L = [] := List.length_eq_zero_iff.mp (hc.left_count.symm.trans hl)
  subst L
  cases R with
  | nil =>
    have hR : x.regs (scalarReg rcount) = 0 := hc.right_count
    omega
  | cons j R =>
    refine ⟨⟨[], R, emitted ++ [j], (hy.correct hc.flip).flip, ?_⟩⟩
    simpa only [List.nil_merge, List.append_assoc, List.singleton_append] using he

private theorem wordMergeLoop_exec {w limit : ℕ} (counter : Fin 11) (body : FlatCode)
    (P : WordData → Prop)
    (step : ∀ x, WordMergeRoom limit x → P x → 0 < x.regs (scalarReg counter) →
      ∃ y, wordWithin w body x y 16 ∧ WordMergeRoom limit y ∧
        wordMergeSize y + 1 = wordMergeSize x ∧ WordMergeFrame x y ∧ P y)
    (x : WordData) (hx : WordMergeRoom limit x) (hp : P x) :
    ∃ y t, wordWithin w (.loopUntil (.lt (scalarReg counter) (scalarReg one)) body) x y t ∧
      WordMergeRoom limit y ∧ y.regs (scalarReg counter) = 0 ∧
      t + 18 * wordMergeSize y ≤ 18 * wordMergeSize x + 1 ∧ WordMergeFrame x y ∧ P y := by
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
        hx, hzero, by omega, WordMergeFrame.refl x, hp⟩
    · have hpos := Nat.pos_of_ne_zero hzero
      have ht : ¬cond.Holds x := by
        change ¬x.regs (scalarReg counter) < x.regs (scalarReg one)
        rw [hx.one_eq]
        exact Nat.not_lt_of_ge hpos
      obtain ⟨y, he, hy, hsmall, hxy, hyp⟩ := step x hx hp hpos
      obtain ⟨z, t, hz, hroom, hstop, htime, hyz, hzp⟩ := ih (wordMergeSize y)
        (by omega) y hy hyp rfl
      refine ⟨z, 16 + t + 2, Cslib.Program.ExecWithin.loopUntil_iter (t := cond) ht he hz,
        hroom, hstop, ?_, hxy.trans hyz, hzp⟩
      omega

private theorem wordMergeLoops_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x) :
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less lcount one) mergeStep ▷
      .loopUntil (less rcount one) drainRight)) x y (18 * wordMergeSize x + 2) ∧
      WordMergeRoom limit y ∧ wordMergeSize y = 0 ∧ WordMergeFrame x y := by
  obtain ⟨y, t₁, hy, hyroom, hyleft, ht₁, hxy, _⟩ :=
    wordMergeLoop_exec lcount (lowerWordCode mergeStep) (fun _ => True)
      (fun _ hs _ hpos => by
        obtain ⟨z, hz, hr, ht, hf, _⟩ := wordMergeStep_exec hfit hs hpos
        exact ⟨z, hz, hr, ht, hf, trivial⟩) x hx trivial
  obtain ⟨z, t₂, hz, hzroom, hzright, ht₂, hyz, _⟩ :=
    wordMergeLoop_exec rcount (lowerWordCode drainRight) (fun _ => True)
      (fun _ hs _ hpos => by
        obtain ⟨z, hz, hr, ht, hf, _⟩ := wordDrainRight_exec hfit hs hpos
        exact ⟨z, hz, hr, ht, hf, trivial⟩) y hyroom trivial
  exact ⟨z, (hy.seq hz).mono (by omega), hzroom,
    by simp [wordMergeSize, hyz.left_zero hyleft, hzright], hxy.trans hyz⟩

-- Both loops together realize one stable list merge into the output buffer.
private theorem wordMergeLoops_correct {w limit base : ℕ} {keys goal : List ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordMergeRoom limit x) (hm : WordMergeModel keys base goal x)
    (hindex : ∀ i ∈ goal, i < keys.length) :
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less lcount one) mergeStep ▷
      .loopUntil (less rcount one) drainRight)) x y (18 * wordMergeSize x + 2) ∧
      WordMergeRoom limit y ∧ wordMergeSize y = 0 ∧ WordMergeFrame x y ∧
      wordKeyMem keys y ∧ WordEntries y.mem base goal := by
  obtain ⟨a, t₁, ha, haroom, hal, ht₁, hxa, ham⟩ :=
    wordMergeLoop_exec lcount (lowerWordCode mergeStep) (WordMergeModel keys base goal)
      (fun _ hr hp hpos => by
        obtain ⟨z, hz, hr', ht, hf, hs⟩ := wordMergeStep_exec hfit hr hpos
        exact ⟨z, hz, hr', ht, hf, wordMergeModel_merge_step hp hindex hpos hs⟩) x hx hm
  let P (s : WordData) := s.regs (scalarReg lcount) = 0 ∧ WordMergeModel keys base goal s
  obtain ⟨b, t₂, hb, hbroom, hbr, ht₂, hab, hbm⟩ :=
    wordMergeLoop_exec rcount (lowerWordCode drainRight) P
      (fun _ hr hp hpos => by
        obtain ⟨z, hz, hr', ht, hf, hs⟩ := wordDrainRight_exec hfit hr hpos
        exact ⟨z, hz, hr', ht, hf, hf.left_zero hp.1,
          wordMergeModel_drain_step hp.2 hp.1 hpos hs⟩) a haroom ⟨hal, ham⟩
  obtain ⟨L, R, out, h, ho⟩ := hbm.2.runs
  have hl : L = [] := List.length_eq_zero_iff.mp (h.left_count.symm.trans hbm.1)
  have hr : R = [] := List.length_eq_zero_iff.mp (h.right_count.symm.trans hbr)
  have hout : out = goal := by simpa [hl, hr] using ho
  refine ⟨b, (ha.seq hb).mono (by omega), hbroom, ?_, hxa.trans hab, h.keys_mem, ?_⟩
  · simp [wordMergeSize, hbm.1, hbr]
  · rw [← hout]
    exact h.output_entries

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
      y.mem = x.mem ∧
      ∀ i, i ≠ ptrReg right → i ≠ scalarReg walk → y.regs i = x.regs i := by
  let endpoint := x.regs (ptrReg right) + 2 * x.regs (scalarReg walk)
  let P (s : WordData) := s.regs (ptrReg right) + 2 * s.regs (scalarReg walk) = endpoint ∧
    s.mem = x.mem ∧ ∀ i, i ≠ ptrReg right → i ≠ scalarReg walk → s.regs i = x.regs i
  let t := Cond.lt (scalarReg walk) (scalarReg one)
  let body := lowerWordCode (next right ▷ dec walk)
  have hs (s : WordData) (h : P s) (ht : ¬t.Holds s) :
      ∃ y, wordWithin w body s y 2 ∧ P y ∧
        y.regs (scalarReg walk) < s.regs (scalarReg walk) := by
    have h₁ := (h.2.2 _ (by decide : scalarReg one ≠ ptrReg right) (by decide)).trans hone
    have h₂ := (h.2.2 _ (by decide : scalarReg two ≠ ptrReg right) (by decide)).trans htwo
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
    refine ⟨y, ha.seq hb, ⟨?_, h.2.1, ?_⟩, ?_⟩
    · rw [hright, hwalk, ← h.1]
      change r + 2 + 2 * (k - 1) = r + 2 * k
      omega
    · intro i hi hj
      simp [y, a, Function.update_of_ne hi, Function.update_of_ne hj, h.2.2 i hi hj]
    · rw [hwalk]
      change k - 1 < k
      omega
  obtain ⟨y, hy, hf, ht⟩ := Cslib.Program.ExecWithin.loopUntil_invariant
    (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t)
    P (fun s => s.regs (scalarReg walk)) hs (show P x from ⟨rfl, rfl, fun _ _ _ => rfl⟩)
  change y.regs (scalarReg walk) < y.regs (scalarReg one) at ht
  rw [(hf.2.2 _ (by decide : scalarReg one ≠ ptrReg right) (by decide)).trans hone] at ht
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

private structure WordPairContents (keys : List ℕ) (base : ℕ)
    (L R emitted : List ℕ) (x : WordData) : Prop where
  keys_mem : wordKeyMem keys x
  keys_separate : keys.length ≤ base
  left_entries : WordEntries x.mem (x.regs (ptrReg left)) L
  right_entries : WordEntries x.mem (x.regs (ptrReg left) + 2 * L.length) R
  output_entries : WordEntries x.mem base emitted
  output_cursor : x.regs (ptrReg out) = base + 2 * emitted.length
  left_length : L.length = min (x.regs (scalarReg remain)) (x.regs (scalarReg width))
  right_length : R.length = min (x.regs (scalarReg remain) - L.length) (x.regs (scalarReg width))
  separate : x.regs (ptrReg left) + 2 * (L.length + R.length) ≤ base ∨
    x.regs (ptrReg out) + 2 * (L.length + R.length) ≤ x.regs (ptrReg left)
  indices : ∀ i ∈ emitted ++ (L ++ R), i < keys.length

private structure WordPairResult (x y : WordData) : Prop where
  memory : ∀ i, i < x.regs (ptrReg out) ∨ y.regs (ptrReg out) ≤ i → y.mem i = x.mem i
  left_cursor : y.regs (ptrReg left) = x.regs (ptrReg left) +
    2 * min (x.regs (scalarReg remain)) (2 * x.regs (scalarReg width))
  out_cursor : y.regs (ptrReg out) = x.regs (ptrReg out) +
    2 * min (x.regs (scalarReg remain)) (2 * x.regs (scalarReg width))
  contents : ∀ keys base L R emitted, WordPairContents keys base L R emitted x →
    wordKeyMem keys y ∧ WordEntries y.mem base (emitted ++ List.merge L R (keyLE keys))

private theorem wordMergePair_exec {w limit : ℕ} {x : WordData}
    (hfit : Fits w limit) (hx : WordPassRoom limit x) :
    ∃ y, wordWithin w (lowerWordCode mergePair) x y
        (22 * min (x.regs (scalarReg remain)) (2 * x.regs (scalarReg width)) + 14) ∧
      WordPassRoom limit y ∧ wordPassFrame x y ∧
      (y.regs (scalarReg remain) = x.regs (scalarReg remain) - 2 * x.regs (scalarReg width)) ∧
      WordPairResult x y := by
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
  obtain ⟨e, he, heR, hmem, hef⟩ := wordWalk_exec a₄ hfit
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
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply ((ha₁.seq (ha₂.seq (ha₃.seq (ha₄.seq he)))).seq (hf.seq hy)).mono
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
  · have hemem : e.mem = x.mem := hmem
    refine ⟨?_, hyL.trans (by rw [hlr]), hyO.trans (by rw [hlr]), ?_⟩
    · intro i hi
      have hfOut : f.regs (ptrReg out) = y.regs (ptrReg out) :=
        (hframe _ (by decide)).symm
      have hi' : i < e.regs (ptrReg out) ∨ f.regs (ptrReg out) ≤ i := by
        rwa [heout, hfOut]
      exact (hff.memory i hi').trans (congrFun hemem i)
    · intro keys base L R emitted h
      have hl : L.length = l := h.left_length
      have hr : R.length = b := by rw [h.right_length, hl]
      have hLeft : e.regs (ptrReg left) = x.regs (ptrReg left) := held
      have hRight : e.regs (ptrReg right) = x.regs (ptrReg left) + 2 * L.length := by
        rwa [hl]
      have hmodel : WordMergeModel keys base (emitted ++ List.merge L R (keyLE keys)) e := by
        refine ⟨⟨L, R, emitted, ⟨?_, h.keys_separate, ?_, ?_, ?_, ?_, hel.trans hl.symm,
          herb.trans hr.symm, ?_, ?_⟩, rfl⟩⟩
        · intro i hi
          rw [hemem]
          exact h.keys_mem i hi
        · simp only [sideHead, Bool.false_eq_true, ite_false]
          rw [hemem, hLeft]
          exact h.left_entries
        · simp only [sideHead, Bool.not_false, ite_true]
          rw [hemem, hRight]
          exact h.right_entries
        · rw [hemem]
          exact h.output_entries
        · exact heout.trans h.output_cursor
        · simp only [sideHead, Bool.false_eq_true, ite_false]
          rw [hLeft, heout]
          have hs := h.separate
          omega
        · simp only [sideHead, Bool.not_false, ite_true]
          rw [hRight, heout]
          have hs := h.separate
          omega
      have hi : ∀ i ∈ emitted ++ List.merge L R (keyLE keys), i < keys.length := by
        intro i hi
        rcases List.mem_append.mp hi with h₁ | h₂
        · exact h.indices i (List.mem_append_left _ h₁)
        · exact h.indices i (List.mem_append_right _ ((List.merge_perm_append _).subset h₂))
      obtain ⟨z, hz, _, _, _, hkeys, hentries⟩ := wordMergeLoops_correct hfit heRoom hmodel hi
      obtain ⟨_, _, h₁⟩ := hz
      obtain ⟨_, _, h₂⟩ := hf
      have eq : z = f := (Cslib.Program.Exec.unique h₁ h₂).1
      subst z
      exact ⟨hkeys, hentries⟩

private theorem wordEntries_slice {mem : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : WordEntries mem base xs) (lo len : ℕ) :
    WordEntries mem (base + 2 * lo) ((xs.drop lo).take len) := by
  apply wordEntries_iff_getElem.mpr
  intro j hj
  have hj' := hj
  rw [List.length_take, List.length_drop] at hj'
  have ht : lo + j < xs.length := by omega
  have he := wordEntries_iff_getElem.mp h (lo + j) ht
  rw [List.getElem_take, List.getElem_drop]
  have haddr : base + 2 * (lo + j) = base + 2 * lo + 2 * j := by omega
  rwa [haddr] at he

private def wordBuffers (n : ℕ) (x : WordData) : Prop :=
  (x.regs (ptrReg src) = n ∧ x.regs (ptrReg dst) = 3 * n) ∨
    (x.regs (ptrReg src) = 3 * n ∧ x.regs (ptrReg dst) = n)

private structure WordPassModel (keys source : List ℕ) (W : ℕ) (x : WordData) : Prop where
  keys_mem : wordKeyMem keys x
  buffers : wordBuffers keys.length x
  input : WordEntries x.mem (x.regs (ptrReg src)) source
  source_length : source.length = keys.length
  source_indices : ∀ i ∈ source, i < keys.length
  width_eq : x.regs (scalarReg width) = W
  progress : ∃ emitted q,
    WordEntries x.mem (x.regs (ptrReg dst)) emitted ∧
    emitted.length + x.regs (scalarReg remain) = keys.length ∧
    emitted.length = min keys.length (q * (2 * W)) ∧
    x.regs (ptrReg left) = x.regs (ptrReg src) + 2 * emitted.length ∧
    x.regs (ptrReg out) = x.regs (ptrReg dst) + 2 * emitted.length ∧
    StableMergePrefix keys source (2 * W) emitted.length emitted

private theorem wordPassModel_step {keys source : List ℕ} {W : ℕ} {x y : WordData}
    (h : WordPassModel keys source W x) (hs : wordPassFrame x y) (hp : WordPairResult x y)
    (hr : 0 < x.regs (scalarReg remain))
    (hremain : y.regs (scalarReg remain) = x.regs (scalarReg remain) -
      2 * x.regs (scalarReg width)) (hstable : StableRuns keys W source) :
    WordPassModel keys source W y := by
  obtain ⟨emitted, q, hem, hlen, hq, hleft, hout, hprefix⟩ := h.progress
  let n := keys.length
  let m := emitted.length
  let r := x.regs (scalarReg remain)
  let l := min r W
  let b := min (r - l) W
  let L := (source.drop m).take l
  let R := (source.drop (m + l)).take b
  let tail := List.merge L R (keyLE keys)
  have hcl : L.length = l := by
    simp only [L, List.length_take, List.length_drop, h.source_length]
    dsimp [l, m, r]
    omega
  have hcr : R.length = b := by
    simp only [R, List.length_take, List.length_drop, h.source_length]
    dsimp [b, l, m, r]
    omega
  have hpair : l + b = min r (2 * W) := by dsimp [l, b]; omega
  have hsrc : y.regs (ptrReg src) = x.regs (ptrReg src) := hs _ (by decide)
  have hdst : y.regs (ptrReg dst) = x.regs (ptrReg dst) := hs _ (by decide)
  have hb := h.buffers
  have hlOut := hp.out_cursor
  rw [h.width_eq, hout, ← hpair] at hlOut
  have hlLeft := hp.left_cursor
  rw [h.width_eq, hleft, ← hpair] at hlLeft
  have hpairContents : WordPairContents keys (x.regs (ptrReg dst)) L R emitted x := by
    refine ⟨h.keys_mem, ?_, ?_, ?_, hem, hout, ?_, ?_, ?_, ?_⟩
    · unfold wordBuffers at hb
      omega
    · rw [hleft]
      exact wordEntries_slice h.input m l
    · rw [hleft, hcl]
      have he : x.regs (ptrReg src) + 2 * m + 2 * l =
          x.regs (ptrReg src) + 2 * (m + l) := by omega
      rw [he]
      exact wordEntries_slice h.input (m + l) b
    · rw [hcl, h.width_eq]
    · rw [hcr, hcl, h.width_eq]
    · rw [hcl, hcr, hleft, hout]
      unfold wordBuffers at hb
      omega
    · intro i hi
      apply h.source_indices
      rcases List.mem_append.mp hi with h₁ | h₂
      · exact List.mem_of_mem_take (hprefix.perm.subset h₁)
      · rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact List.mem_of_mem_drop (List.mem_of_mem_take h₂)
        · exact List.mem_of_mem_drop (List.mem_of_mem_take h₂)
  obtain ⟨hkeys, hentries⟩ := hp.contents keys _ L R emitted hpairContents
  have hslen : tail.length = l + b := by
    rw [show tail.length = (L ++ R).length from (List.merge_perm_append _).length_eq,
      List.length_append, hcl, hcr]
  have hm : m = q * (2 * W) := by omega
  have hnewlen : (emitted ++ tail).length = m + l + b := by
    rw [List.length_append, hslen]
    omega
  have hnewq : (emitted ++ tail).length = min n ((q + 1) * (2 * W)) := by
    rw [hnewlen, Nat.add_assoc m l b, hpair, Nat.add_mul]
    dsimp [n, m, r] at *
    rw [← hm]
    omega
  have hpre : StableMergePrefix keys source (2 * W) (m + l + b) (emitted ++ tail) := by
    apply stableMergePrefix_step h.source_length hstable hprefix hm
      (mid := m + l)
    · dsimp [l, m, r]; omega
    · dsimp [b, l, m, r]; omega
    · have h₁ : m + l - m = l := by omega
      have h₂ : m + l + b - (m + l) = b := by omega
      rw [h₁, h₂]
      rfl
  refine ⟨hkeys, ?_, ?_, h.source_length, h.source_indices, (hs _ (by decide)).trans h.width_eq,
    ⟨emitted ++ tail, q + 1, ?_, ?_, hnewq, ?_, ?_, ?_⟩⟩
  · simpa only [wordBuffers, hsrc, hdst] using hb
  · rw [hsrc]
    apply wordEntries_congr _ h.input
    intro i hi₁ hi₂
    rw [h.source_length] at hi₂
    apply hp.memory
    rw [hout, hlOut]
    unfold wordBuffers at hb
    omega
  · rwa [hdst]
  · rw [hremain, h.width_eq, hnewlen, Nat.add_assoc m l b, hpair]
    omega
  · rw [hsrc, hnewlen, hlLeft]
    omega
  · rw [hdst, hnewlen, hlOut]
    omega
  · rwa [hnewlen]

private theorem wordPassLoop_exec {w limit : ℕ} (x : WordData) (P : WordData → Prop)
    (hfit : Fits w limit) (hx : WordPassRoom limit x) (hw : 0 < x.regs (scalarReg width)) :
    ∀ (_ : P x)
      (_ : ∀ a b, P a → (0 < a.regs (scalarReg remain)) → wordPassFrame a b →
        WordPairResult a b →
        b.regs (scalarReg remain) = a.regs (scalarReg remain) - 2 * a.regs (scalarReg width) →
        P b),
    ∃ y, wordWithin w (lowerWordCode (.loopUntil (less remain one) mergePair)) x y
        (22 * x.regs (scalarReg remain) +
          16 * pairs (x.regs (scalarReg remain)) (x.regs (scalarReg width)) + 1) ∧
      WordPassRoom limit y ∧ wordPassFrame x y ∧ P y ∧ y.regs (scalarReg remain) = 0 := by
  intro hp hstep
  let W := x.regs (scalarReg width)
  let Inv (s : WordData) := WordPassRoom limit s ∧ wordPassFrame x s ∧ P s
  let pot (s : WordData) :=
    22 * s.regs (scalarReg remain) + 16 * pairs (s.regs (scalarReg remain)) W
  let t := Cond.lt (scalarReg remain) (scalarReg one)
  have step (s : WordData) (h : Inv s) (ht : ¬t.Holds s) :
      ∃ y c, wordWithin w (lowerWordCode mergePair) s y c ∧ Inv y ∧ c + 2 + pot y ≤ pot s := by
    have hsW : s.regs (scalarReg width) = W := h.2.1 _ (by decide)
    change ¬s.regs (scalarReg remain) < s.regs (scalarReg one) at ht
    rw [h.1.one_eq] at ht
    obtain ⟨y, he, hroom, hframe, hrem, hpairResult⟩ := wordMergePair_exec hfit h.1
    refine ⟨y, _, he, ⟨hroom, (fun i hi => (hframe i hi).trans (h.2.1 i hi)),
      hstep s y h.2.2 (Nat.le_of_not_gt ht) hframe hpairResult hrem⟩, ?_⟩
    have hpair := pairs_step (w := W) (Nat.le_of_not_gt ht) hw
    dsimp only [pot]
    rw [hsW, hrem, hsW, hpair]
    omega
  obtain ⟨y, hy, hframe, hstop⟩ := Cslib.Program.ExecWithin.loopUntil_potential
    (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t)
    Inv pot step (show Inv x from ⟨hx, (fun _ _ => rfl), hp⟩)
  change y.regs (scalarReg remain) < y.regs (scalarReg one) at hstop
  rw [hframe.1.one_eq] at hstop
  exact ⟨y, hy, hframe.1, hframe.2.1, hframe.2.2, Nat.lt_one_iff.mp hstop⟩

private structure WordSortContents (keys : List ℕ) (x : WordData) : Prop where
  keys_mem : wordKeyMem keys x
  buffers : wordBuffers keys.length x
  entries : ∃ indices,
    WordEntries x.mem (x.regs (ptrReg src)) indices ∧
    indices.Perm (List.range keys.length) ∧
    StableRuns keys (x.regs (scalarReg width)) indices

private theorem wordPassModel_init {keys source : List ℕ} {W : ℕ} {x y : WordData}
    (h : WordSortContents keys x)
    (hentries : WordEntries x.mem (x.regs (ptrReg src)) source)
    (hperm : source.Perm (List.range keys.length))
    (hm : y.mem = x.mem)
    (hsrc : y.regs (ptrReg src) = x.regs (ptrReg src))
    (hdst : y.regs (ptrReg dst) = x.regs (ptrReg dst))
    (hleft : y.regs (ptrReg left) = x.regs (ptrReg src))
    (hout : y.regs (ptrReg out) = x.regs (ptrReg dst))
    (hrem : y.regs (scalarReg remain) = keys.length)
    (hwidth : y.regs (scalarReg width) = W) :
    WordPassModel keys source W y := by
  refine ⟨?_, ?_, ?_, by simpa using hperm.length_eq,
    fun i hi => List.mem_range.mp (hperm.subset hi), hwidth,
    ⟨[], 0, trivial, ?_, ?_, ?_, ?_, stableMergePrefix_empty keys source (2 * W)⟩⟩
  · intro i hi
    rw [hm]
    exact h.keys_mem i hi
  · simpa only [wordBuffers, hsrc, hdst] using h.buffers
  · rw [hm, hsrc]
    exact hentries
  · simp [hrem]
  · simp
  · simp [hleft, hsrc]
  · simp [hout, hdst]

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
      WordPassState n y ∧ (y.regs (scalarReg width) = x.regs (scalarReg width) * 2) ∧
      ∀ keys, keys.length = n → WordSortContents keys x → WordSortContents keys y := by
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
  obtain ⟨d, hd, hdr, hdf, _, _⟩ :=
    wordPassLoop_exec c (fun _ => True) hfit hroom (by rw [hcwidth]; exact hw) trivial
      (fun _ _ _ _ _ _ _ => trivial)
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
  refine ⟨y, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
  · intro keys hlen hsort
    obtain ⟨source, hse, hperm, hstable⟩ := hsort.entries
    let W := x.regs (scalarReg width)
    have hmodel : WordPassModel keys source W c :=
      wordPassModel_init hsort hse hperm rfl
        (hframe _ (by decide) (by decide) (by decide))
        (hframe _ (by decide) (by decide) (by decide)) hcleft hcout
        (hcrem.trans hlen.symm) hcwidth
    obtain ⟨z, hz, _, _, hdone, hzero⟩ :=
      wordPassLoop_exec c (WordPassModel keys source W)
        hfit hroom (by rw [hcwidth]; exact hw) hmodel
        (fun _ _ hm hr hf hp hrem => wordPassModel_step hm hf hp hr hrem hstable)
    obtain ⟨_, _, h₁⟩ := hz
    obtain ⟨_, _, h₂⟩ := hd
    have heq : z = d := (Cslib.Program.Exec.unique h₁ h₂).1
    subst z
    obtain ⟨output, _, he, hlen', _, _, _, ho⟩ := hdone.progress
    rw [hzero, Nat.add_zero] at hlen'
    have hnewperm : output.Perm source := by
      have hp := ho.perm
      rw [hlen', ← hdone.source_length, List.take_length] at hp
      exact hp
    have hdb := hdone.buffers
    have hds : d.regs (ptrReg src) = x.regs (ptrReg src) := dd _ (by decide)
    have hdt : d.regs (ptrReg dst) = x.regs (ptrReg dst) := dd _ (by decide)
    refine ⟨hdone.keys_mem, ?_, ⟨output, ?_, hnewperm.trans hperm, ?_⟩⟩
    · unfold wordBuffers at hdb ⊢
      rw [hsource, hdest, ← hds, ← hdt]
      tauto
    · change WordEntries d.mem (y.regs (ptrReg src)) output
      rw [hsource, ← hdt]
      exact he
    · rw [show y.regs (scalarReg width) = W * 2 by simp [y, W], Nat.mul_comm W 2]
      exact ho.runs

private theorem wordOuter_exec {w n k : ℕ} {x : WordData}
    (hfit : Fits w (5 * n + 2)) (hx : WordPassState n x)
    (hw : x.regs (scalarReg width) = 2 ^ k) (keys : List ℕ) (hn : keys.length = n)
    (hsort : WordSortContents keys x) :
    ∃ y, wordWithin w (lowerWordCode (.loop (less width len) mergePass)) x y
      (outerBudget 22 n k) ∧ WordSortContents keys y ∧ n ≤ y.regs (scalarReg width) := by
  induction hd : Nat.clog 2 n - k using Nat.strong_induction_on generalizing k x with
  | _ d ih =>
    let t := Cond.lt (scalarReg width) (scalarReg len)
    have hreg : 0 < x.regs (scalarReg width) := by rw [hw]; positivity
    by_cases ht : t.Holds x
    · have hlt : (2 : ℕ) ^ k < n := by
        change x.regs (scalarReg width) < x.regs (scalarReg len) at ht
        rwa [hw, hx.len_eq] at ht
      have hk := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).2 hlt
      obtain ⟨y, hy, hyState, hyWidth, hySort⟩ := wordPass_exec hfit hx hreg (by rw [hw]; exact hlt)
      have hwidth : y.regs (scalarReg width) = (2 : ℕ) ^ (k + 1) := by
        rw [hyWidth, hw, pow_succ]
      have hsmall : Nat.clog 2 n - (k + 1) < d := by omega
      obtain ⟨z, hz, hzs, hzw⟩ := ih _ hsmall hyState hwidth (hySort keys hn hsort) rfl
      have hz' : wordWithin w (.loop t (lowerWordCode mergePass)) y z
          (outerBudget 22 n (k + 1)) := hz
      have he := Cslib.Program.ExecWithin.loop_iter (t := t) ht hy hz'
      rw [hw] at he
      have hbudget := outerBudget_step (p := 22) (Nat.zero_lt_of_lt hlt) hk
      exact ⟨z, he.mono (by omega), hzs, hzw⟩
    · have he : wordWithin w (.loop t (lowerWordCode mergePass)) x x 2 :=
        Cslib.Program.ExecWithin.loop_exit
          (I := Cslib.WordRAM.instructionSet w .standard 20) (t := t) ht
      have hstop : n ≤ x.regs (scalarReg width) := by
        apply Nat.le_of_not_gt
        change ¬x.regs (scalarReg width) < x.regs (scalarReg len) at ht
        rwa [hx.len_eq] at ht
      exact ⟨x, he.mono (by unfold outerBudget; omega), hsort, hstop⟩

private theorem wordCode_exec {w : ℕ} (keys : List ℕ) (hn : 3 ≤ keys.length)
    (hfit : Fits w (5 * keys.length + 2)) :
    ∃ y, wordWithin w (lowerWordCode code) (wordRAMInput keys).data y
      (22 * keys.length * Nat.clog 2 keys.length + 25 * keys.length +
        26 * Nat.clog 2 keys.length - 9) ∧ WordSortContents keys y ∧
      keys.length ≤ y.regs (scalarReg width) := by
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
  have hsrc := (frame (ptrReg src) (by decide)).trans hinit.source_eq
  have hdst := (frame (ptrReg dst) (by decide)).trans hinit.dest_eq
  have hsort : WordSortContents keys b := by
    refine ⟨hinit.keys_eq, Or.inl ⟨hsrc, hdst⟩, ⟨List.range keys.length, ?_, .refl _, ?_⟩⟩
    · rw [hsrc]
      exact hinit.entries
    · rw [hw, pow_zero]
      exact stableRuns_range keys
  obtain ⟨y, hy, hys, hyw⟩ := wordOuter_exec hfit hstate hw keys rfl hsort
  refine ⟨y, ?_, hys, hyw⟩
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

/-- The register naming the active interleaved output buffer after sorting. -/
abbrev wordRAMResultReg : Fin 20 := 1

private theorem wordRAM_finish {w t : ℕ} {keys : List ℕ} {y : WordData}
    (he : Cslib.Program.Exec (Cslib.WordRAM.instructionSet w .standard 20)
      (lowerWordCode code) (wordRAMInput keys).data y t) :
    ∃ z : Cslib.WordRAM.State 20, z.data = y ∧
      Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) z t ∧
      Cslib.WordRAM.step w wordRAMProgram z = .halt (z.data.regs wordRAMResultReg) := by
  let finish := (lowerWordCode code).size
  let z : Cslib.WordRAM.State 20 := ⟨finish, y⟩
  have run := he.runs (flatMachine w .standard 20) [] [.halt wordRAMResultReg]
  have hrun : Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) z t := by
    simp only [List.nil_append, List.length_nil, Nat.zero_add, wordAssemble_width] at run
    exact run.map (r' := Next w wordRAMProgram)
      (fun a : ℕ × WordData => (⟨a.1, a.2⟩ : Cslib.WordRAM.State 20)) (fun _ _ h => h)
  have hend : Cslib.WordRAM.step w wordRAMProgram z = .halt (y.regs wordRAMResultReg) := by
    apply step_halt
    let ops := (lowerWordCode code).assemble (flatMachine 0 .standard 20) 0
    have hlen : ops.length = finish := Cslib.Program.Code.length_assemble _ _ _
    change (ops ++ [.halt wordRAMResultReg])[finish]? = _
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  exact ⟨z, rfl, hrun, hend⟩

private theorem wordTinyExec {w : ℕ} (keys : List ℕ) (hn : keys.length ≤ 1) :
    ∃ y, wordWithin w (lowerWordCode code) (wordRAMInput keys).data y 6 ∧
      y.regs wordRAMResultReg = keys.length ∧
      ∀ i, i < keys.length → y.mem (keys.length + 2 * i) = i := by
  let I := Cslib.WordRAM.instructionSet w .standard 20
  let x := (wordRAMInput keys).data
  let t₀ := Cond.lt (scalarReg zero) (scalarReg len)
  let t₁ := Cond.lt (scalarReg one) (scalarReg len)
  let t₂ := Cond.lt (scalarReg two) (scalarReg len)
  have ht₁ : ¬t₁.Holds x := by change ¬(1 : ℕ) < keys.length; omega
  have ht₂ : ¬t₂.Holds x := by change ¬(2 : ℕ) < keys.length; omega
  let st := wordOp (.store (ptrReg src) (scalarReg zero))
  have finish {z : WordData} (h : wordWithin w (.branch t₀ st .skip) x z 2) :
      wordWithin w (lowerWordCode code) x z 6 := by
    unfold code lowerWordCode
    have h₁ := Cslib.Program.ExecWithin.branch_neg (I := I) (t := t₁)
      (pos := lowerWordCode sortTwo) ht₁ h
    exact Cslib.Program.ExecWithin.branch_neg (t := t₂) ht₂ h₁
  by_cases hz : 0 < keys.length
  · let y := x.write keys.length 0
    have he : wordWithin w st x y 1 := wordPrimitive rfl
    have hpos : t₀.Holds x := hz
    have hb := Cslib.Program.ExecWithin.branch_pos (I := I) (t := t₀) (neg := .skip) hpos he
    refine ⟨y, finish hb, rfl, ?_⟩
    intro i hi
    have hz : i = 0 := by omega
    subst i
    simp [y]
  · have ht₀ : ¬t₀.Holds x := hz
    have hb := Cslib.Program.ExecWithin.branch_neg (I := I) (t := t₀) (pos := st) ht₀
      (Cslib.Program.ExecWithin.skip (I := I) (T := 0))
    exact ⟨x, finish hb, rfl, fun _ h => (hz (Nat.zero_le _ |>.trans_lt h)).elim⟩

private theorem wordTwoExec {w : ℕ} (a b : ℕ) (hfit : Fits w 4) :
    ∃ (y : WordData) (output : List ℕ),
      wordWithin w (lowerWordCode code) (wordRAMInput [a, b]).data y 12 ∧
      output.Perm (List.range 2) ∧ output.Pairwise (StableKeyOrder [a, b]) ∧
      ∀ i (hi : i < output.length), y.mem (y.regs wordRAMResultReg + 2 * i) = output[i] := by
  let I := Cslib.WordRAM.instructionSet w .standard 20
  let x := (wordRAMInput [a, b]).data
  let a₁ := x.set (scalarReg lvalue) a
  let a₂ := a₁.set (ptrReg key) 1
  let a₃ := a₂.set (scalarReg rvalue) b
  let c := a₃.set (ptrReg out) 2
  have h₁ : wordWithin w (lowerWordCode (instr (.loadData lvalue key))) x a₁ 1 :=
    wordPrimitive rfl
  have h₂ : wordWithin w (lowerWordCode (next key)) a₁ a₂ 1 :=
    wordPrimitive (Data.put_of_fits (hfit.of_le (by decide : 1 ≤ 4)))
  have h₃ : wordWithin w (lowerWordCode (instr (.loadData rvalue key))) a₂ a₃ 1 :=
    wordPrimitive rfl
  have h₄ : wordWithin w (lowerWordCode (copyRef out src)) a₃ c 1 := wordPrimitive rfl
  let writes (i j : Fin 11) :=
    lowerWordCode (instr (.storeData out i) ▷ next out ▷ instr (.storeData out j))
  have put (i j : Fin 11) :
      ∃ y, wordWithin w (writes i j) c y 3 ∧ y.regs wordRAMResultReg = 2 ∧
        y.mem 2 = c.regs (scalarReg i) ∧ y.mem 4 = c.regs (scalarReg j) := by
    let d := c.write 2 (c.regs (scalarReg i))
    let e := d.set (ptrReg out) 4
    let y := e.write 4 (c.regs (scalarReg j))
    have hd : wordWithin w (wordOp (.store (ptrReg out) (scalarReg i))) c d 1 :=
      wordPrimitive rfl
    have he : wordWithin w (lowerWordCode (next out)) d e 1 :=
      wordPrimitive (Data.put_of_fits hfit)
    have hy : wordWithin w (wordOp (.store (ptrReg out) (scalarReg j))) e y 1 := by
      apply wordPrimitive
      have hj : scalarReg j ≠ ptrReg out := by
        intro h
        have h' := congrArg (fun r : Fin 20 => r.val) h
        change 8 + j.val = 5 at h'
        omega
      have hreg : e.regs (scalarReg j) = c.regs (scalarReg j) :=
        Function.update_of_ne hj 4 c.regs
      rw [Op.eval_store, hreg]
      rfl
    refine ⟨y, hd.seq (he.seq hy), rfl, ?_, ?_⟩ <;> simp [y, e, d]
  let test := Cond.lt (scalarReg rvalue) (scalarReg lvalue)
  have finish {y : WordData}
      (h : wordWithin w (.branch test (writes one zero) (writes zero one)) c y 5) :
      wordWithin w (lowerWordCode code) x y 12 := by
    have hs : wordWithin w (lowerWordCode sortTwo) x y 9 := h₁.seq (h₂.seq (h₃.seq (h₄.seq h)))
    let t₁ := Cond.lt (scalarReg one) (scalarReg len)
    let t₂ := Cond.lt (scalarReg two) (scalarReg len)
    have ht₁ : t₁.Holds x := show (1 : ℕ) < 2 by decide
    have ht₂ : ¬t₂.Holds x := show ¬(2 : ℕ) < 2 by decide
    have he : wordWithin w (lowerWordCode (.branch (less one len) sortTwo
        (.branch (less zero len) (instr (.storeData src zero)) .skip))) x y 10 :=
      Cslib.Program.ExecWithin.branch_pos (I := I) (t := t₁) ht₁ hs
    exact Cslib.Program.ExecWithin.branch_neg (I := I) (t := t₂) ht₂ he
  by_cases hcmp : b < a
  · obtain ⟨y, he, hb, hv₁, hv₀⟩ := put one zero
    have h : wordWithin w (.branch test (writes one zero) (writes zero one)) c y 5 := by
      exact (Cslib.Program.ExecWithin.branch_pos (I := I) (t := test)
        (neg := writes zero one) (show test.Holds c from hcmp) he).mono (by decide)
    refine ⟨y, [1, 0], finish h, List.Perm.swap 0 1 [], ?_, ?_⟩
    · simp [StableKeyOrder, hcmp]
    · intro i hi
      rw [hb]
      cases i with
      | zero => exact hv₁
      | succ i =>
        have hi' : i = 0 := by simp at hi; omega
        subst i
        exact hv₀
  · obtain ⟨y, he, hb, hv₀, hv₁⟩ := put zero one
    have h : wordWithin w (.branch test (writes one zero) (writes zero one)) c y 5 :=
      Cslib.Program.ExecWithin.branch_neg (I := I) (t := test)
        (pos := writes one zero) (show ¬test.Holds c from hcmp) he
    refine ⟨y, [0, 1], finish h, .refl _, ?_, ?_⟩
    · have hle := Nat.le_of_not_gt hcmp
      simp [StableKeyOrder]
      omega
    · intro i hi
      rw [hb]
      cases i with
      | zero => exact hv₀
      | succ i =>
        have hi' : i = 0 := by simp at hi; omega
        subst i
        exact hv₁

/-- The flat Word RAM sorter halts at the active output buffer and returns the stable sorted
permutation. The run count includes its final halt. The caller supplies a prepared array of
at least three keys and a word width that holds the keys and interleaved buffer addresses. -/
theorem wordRAM_sorts {w : ℕ} (keys : List ℕ) (hn : 3 ≤ keys.length)
    (hfit : Fits w (5 * keys.length + 2)) (_hkeys : ∀ k ∈ keys, Fits w k) :
    ∃ (y : Cslib.WordRAM.State 20) (t : ℕ) (output : List ℕ),
      Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) y t ∧
      Cslib.WordRAM.step w wordRAMProgram y = .halt (y.data.regs wordRAMResultReg) ∧
      t + 1 ≤ 22 * keys.length * Nat.clog 2 keys.length + 25 * keys.length +
        26 * Nat.clog 2 keys.length - 8 ∧
      output.Perm (List.range keys.length) ∧ output.Pairwise (StableKeyOrder keys) ∧
      ∀ i (hi : i < output.length),
        y.data.mem (y.data.regs wordRAMResultReg + 2 * i) = output[i] := by
  obtain ⟨y, hcode, hys, hyw⟩ := wordCode_exec keys hn hfit
  obtain ⟨t, ht, he⟩ := hcode
  obtain ⟨output, heo, hperm, hord⟩ := hys.entries
  obtain ⟨z, hzy, hrun, hend⟩ := wordRAM_finish he
  have hlen : output.length = keys.length := by simpa using hperm.length_eq
  refine ⟨z, t, output, hrun, hend, by omega, hperm, hord.finish (hlen ▸ hyw), ?_⟩
  intro i hi
  rw [hzy]
  exact (wordEntries_iff_getElem.mp heo i hi).1

/-- The direct word-RAM implementation halts from the prepared input within the stated
instruction count, including halt. -/
theorem wordRAM_executes {w : ℕ} (keys : List ℕ) (hn : 3 ≤ keys.length)
    (hfit : Fits w (5 * keys.length + 2)) (hkeys : ∀ k ∈ keys, Fits w k) :
    ∃ base t, Cslib.WordRAM.Executes w wordRAMProgram (wordRAMInput keys) base t ∧
      t ≤ 22 * keys.length * Nat.clog 2 keys.length + 25 * keys.length +
        26 * Nat.clog 2 keys.length - 8 := by
  obtain ⟨y, t, _, hrun, hend, ht, _⟩ := wordRAM_sorts keys hn hfit hkeys
  exact ⟨_, t + 1, ⟨y, t, hrun, hend, rfl⟩, ht⟩

/-- The standard Word RAM sorter returns a stable permutation for inputs of length at most two.
The bound includes the final halt. -/
theorem wordRAM_sorts_small {w : ℕ} (keys : List ℕ) (hn : keys.length ≤ 2)
    (hfit : Fits w (5 * keys.length + 2)) (_hkeys : ∀ k ∈ keys, Fits w k) :
    ∃ (y : Cslib.WordRAM.State 20) (t : ℕ) (output : List ℕ),
      Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) y t ∧
      Cslib.WordRAM.step w wordRAMProgram y = .halt (y.data.regs wordRAMResultReg) ∧
      t + 1 ≤ (if keys.length < 2 then 7 else 13) ∧
      output.Perm (List.range keys.length) ∧ output.Pairwise (StableKeyOrder keys) ∧
      ∀ i (hi : i < output.length),
        y.data.mem (y.data.regs wordRAMResultReg + 2 * i) = output[i] := by
  by_cases h : keys.length < 2
  · have hn' : keys.length ≤ 1 := by omega
    obtain ⟨y, ⟨t, ht, he⟩, hb, hm⟩ := wordTinyExec (w := w) keys hn'
    obtain ⟨z, hzy, hrun, hhalt⟩ := wordRAM_finish he
    have hord : (List.range keys.length).Pairwise (StableKeyOrder keys) := by
      have hs : keys.length = 0 ∨ keys.length = 1 := by omega
      rcases hs with hs | hs <;> rw [hs] <;> simp
    refine ⟨z, t, List.range keys.length, hrun, hhalt, by rw [ite_eq_left h]; omega,
      .refl _, hord, ?_⟩
    intro i hi
    rw [hzy, hb, List.getElem_range]
    exact hm i (by simpa only [List.length_range] using hi)
  · have hn' : keys.length = 2 := by omega
    match keys with
    | a :: b :: rest =>
      have hr : rest = [] := by simpa using hn'
      subst rest
      obtain ⟨v, output, ⟨t, ht, he⟩, hp, ho, hread⟩ :=
        wordTwoExec a b (hfit.of_le (show (4 : ℕ) ≤ 12 by decide))
      obtain ⟨z, hzy, hrun, hhalt⟩ := wordRAM_finish he
      refine ⟨z, t, output, hrun, hhalt, by rw [ite_eq_right h]; omega, hp, ho, ?_⟩
      intro i hi
      rw [hzy]
      exact hread i hi

/-- The packed implementations run to completion and their numeric outputs agree.
The two machine states use their own buffer layouts. -/
theorem packed_backends_agree {w : ℕ} (keys : List ℕ)
    (hfit : Fits w (5 * keys.length + 2)) (hkeys : ∀ k ∈ keys, Fits w k) :
    ∃ (u : Cslib.WordRAM.State 20) (v : PointerMachine.State model (layout 8 11))
      (tWord tPointer : ℕ),
      Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) u tWord ∧
      Cslib.WordRAM.step w wordRAMProgram u = .halt (u.data.regs wordRAMResultReg) ∧
      PointerMachine.Executes (compile code).program (encode (inputState keys)) v tPointer ∧
      ((List.range keys.length).map fun i => u.data.mem (u.data.regs wordRAMResultReg + 2 * i)) =
        pointerPermutation keys.length v := by
  have hword : ∃ (u : Cslib.WordRAM.State 20) (t : ℕ) (output : List ℕ),
      Cslib.WordRAM.Runs w wordRAMProgram (wordRAMInput keys) u t ∧
      Cslib.WordRAM.step w wordRAMProgram u = .halt (u.data.regs wordRAMResultReg) ∧
      output.Perm (List.range keys.length) ∧ output.Pairwise (StableKeyOrder keys) ∧
      ∀ i (hi : i < output.length),
        u.data.mem (u.data.regs wordRAMResultReg + 2 * i) = output[i] := by
    by_cases hn : 3 ≤ keys.length
    · obtain ⟨u, t, out, hr, hh, _, hs⟩ := wordRAM_sorts keys hn hfit hkeys
      exact ⟨u, t, out, hr, hh, hs⟩
    · obtain ⟨u, t, out, hr, hh, _, hs⟩ := wordRAM_sorts_small keys (by omega) hfit hkeys
      exact ⟨u, t, out, hr, hh, hs⟩
  have hptr : ∃ v t,
      PointerMachine.Executes (compile code).program (encode (inputState keys)) v t ∧
      (pointerPermutation keys.length v).Perm (List.range keys.length) ∧
      (pointerPermutation keys.length v).Pairwise (StableKeyOrder keys) := by
    by_cases hn : 3 ≤ keys.length
    · obtain ⟨v, t, hr, _, hs⟩ := pointer_sorts keys hn
      exact ⟨v, t, hr, hs⟩
    · obtain ⟨v, t, hr, _, hs⟩ := pointer_sorts_small keys (by omega)
      exact ⟨v, t, hr, hs⟩
  obtain ⟨u, wt, output, hrun, hhalt, hperm, hord, hread⟩ := hword
  obtain ⟨v, pt, hpExec, hpPerm, hpOrd⟩ := hptr
  have same : output = pointerPermutation keys.length v :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ h₁ h₂ => (h₁.asym h₂).elim) hord hpOrd (hperm.trans hpPerm.symm)
  refine ⟨u, v, wt, pt, hrun, hhalt, hpExec, ?_⟩
  rw [← same]
  apply List.ext_getElem
  · simpa using hperm.length_eq.symm
  · intro i _ hi
    simpa only [List.getElem_map, List.getElem_range] using hread i hi

end WordRAM

end Cslib.Algorithms.WordRAM.MergeSort.LocalRef
