/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.RecordRun
public import CslibFrontier.Algorithms.Lean.Sort.Bitonic.Layered
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Data.List.GetD

/-!
# The layout of the quasilinear formula

For a nondeterministic machine `ntm` with `k` work tapes, a slack `κ` and an input `x` of length
`n`, the formula of the quasilinear Cook–Levin reduction describes `N = 2 ^ τ` step records, with
`τ = n + κ + 1` (`StepRecord`, in `CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.
RecordRun`). Its variables are natural numbers of four kinds, told apart by their residue modulo
`8`: two constants, the bits of the records, the arrays of one sorting network per work tape, and
the flags of those networks. Above all of them come the fresh variables of the gadgets
(`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate`), one block per constraint.

A record holds the bits of its finite part (`Ctrl`): the state, the symbol under the input head,
the input move, the emitted symbol, the view of the output, and, for each work tape, the symbol
read, the symbol written, the move and the symbol left under the head. Then come the input-head
position, in `n + 2` bits, and the work-head positions, offset by `N`, in `τ + 2` bits each.

The constraints form the nine `Family`s (`famDefs`, `famCons`): the constants; the first record;
the last record; for each step, a table of the pairs of finite parts that a step can take
(`Allowed`); the input-head moves; the symbols under the input head; the work-head moves; the
switches of the sorting networks, whose flags are free; and, for each position of the sorted records
of a tape, the check that the keys increase and that each symbol read is what the previous visit of
the cell left there.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Ctrl`, `Ctrl.Allowed`: finite parts of records and the
  pairs a step can take.
* `Cslib.Complexity.CookLevin.Quasilinear.ctrlBit`, `decCtrl`: their bits and their decoding.
* `Cslib.Complexity.CookLevin.Quasilinear.Family`: the nine families of constraints.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout`: the parameters and variables of the formula.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.famDefs`, `Layout.famCons`: its constraints.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

variable {k : ℕ} {State : Type}

/-! ### The finite part of a record -/

/-- The finite part of a step record: the state, the symbol under the input head, the input move,
the emitted symbol and the view of the output, and for each work tape the symbol read, the symbol
written, the move and the symbol left under the head. -/
structure Ctrl (k : ℕ) (State : Type) where
  /-- the state, or `none` once halted -/
  state : Option State
  /-- the symbol under the input head -/
  inSym : Option Bool
  /-- the move of the input head -/
  inMove : SignType
  /-- the emitted symbol -/
  emit : Option Bool
  /-- the view of the output before the step -/
  out : OutView
  /-- the symbols read -/
  read : Fin k → Option Bool
  /-- the symbols written -/
  write : Fin k → Option (Option Bool)
  /-- the moves of the work heads -/
  move : Fin k → SignType
  /-- the symbols left under the work heads -/
  after : Fin k → Option Bool

namespace Ctrl

/-- Finite parts as tuples. -/
def equiv : Ctrl k State ≃ Option State × Option Bool × SignType × Option Bool × OutView ×
    (Fin k → Option Bool) × (Fin k → Option (Option Bool)) × (Fin k → SignType) ×
      (Fin k → Option Bool) where
  toFun c := (c.state, c.inSym, c.inMove, c.emit, c.out, c.read, c.write, c.move, c.after)
  invFun := fun (state, inSym, inMove, emit, out, read, write, move, after) =>
    ⟨state, inSym, inMove, emit, out, read, write, move, after⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _⟩ => rfl

/-- Finite parts of records over a finite state type form a finite type. -/
noncomputable instance [Fintype State] : Fintype (Ctrl k State) := by
  classical
  exact Fintype.ofEquiv _ equiv.symm

/-- The halted finite part with no symbols and no moves is the default. -/
instance : Inhabited (Ctrl k State) :=
  ⟨⟨none, none, 0, none, .empty, fun _ => none, fun _ => none, fun _ => 0, fun _ => none⟩⟩

/-- The action a running finite part takes, moving to the state `s`. -/
def action (c : Ctrl k State) (s : Option State) : Action k Bool State :=
  ⟨c.inMove, fun j => (c.write j, c.move j), c.emit, s⟩

/-- The pairs of finite parts of consecutive records: a halted record keeps its state and output and
does nothing; a running record takes a transition of `ntm` on the symbols it reads, emits its
symbol, and leaves under each work head what it writes, or what it read. -/
def Allowed (ntm : MultiTapeNTM k Bool State) (c c' : Ctrl k State) : Prop :=
  match c.state with
  | none => c'.state = none ∧ c.inMove = 0 ∧ c.emit = none ∧ c'.out = c.out ∧
      ∀ j, c.write j = none ∧ c.move j = 0 ∧ c.after j = c.read j
  | some q => ntm.Tr q c.inSym c.read (c.action c'.state) ∧ c'.out = c.out.push c.emit ∧
      ∀ j, c.after j = (c.write j).getD (c.read j)

end Ctrl

/-! ### Codes of the fields -/

/-- The two bits of a symbol: `00` blank, `10` false, `01` true. -/
def symBit : Option Bool → ℕ → Bool
  | none, _ => false
  | some false, i => decide (i = 0)
  | some true, i => decide (i = 1)

/-- The two bits of a write: `00` none, `10` blank, `01` false, `11` true. -/
def writeBit : Option (Option Bool) → ℕ → Bool
  | none, _ => false
  | some none, i => decide (i = 0)
  | some (some false), i => decide (i = 1)
  | some (some true), i => decide (i ≤ 1)

/-- The two bits of a move: `00` stay, `10` right, `01` left. -/
def moveBit : SignType → ℕ → Bool
  | .zero, _ => false
  | .pos, i => decide (i = 0)
  | .neg, i => decide (i = 1)

/-- The two bits of a view of the output: its index in binary. -/
def outBit (o : OutView) (i : ℕ) : Bool := o.index.testBit i

/-- Decoding two bits of a symbol. -/
def decSym (f : ℕ → Bool) : Option Bool :=
  if f 0 then some false else if f 1 then some true else none

/-- Decoding two bits of a write. -/
def decWrite (f : ℕ → Bool) : Option (Option Bool) :=
  if f 0 then (if f 1 then some (some true) else some none)
  else if f 1 then some (some false) else none

/-- Decoding two bits of a move. -/
def decMove (f : ℕ → Bool) : SignType :=
  if f 0 then .pos else if f 1 then .neg else .zero

/-- Decoding two bits of a view of the output. -/
def decOut (f : ℕ → Bool) : OutView := OutView.ofIndex (bitsVal f 2)

/-- Decoding the bits of a symbol gives the symbol. -/
@[simp] theorem decSym_symBit (s : Option Bool) : decSym (symBit s) = s := by
  rcases s with _ | _ | _ <;> rfl

/-- Decoding the bits of a write gives the write. -/
@[simp] theorem decWrite_writeBit (s : Option (Option Bool)) : decWrite (writeBit s) = s := by
  rcases s with _ | _ | _ | _ <;> rfl

/-- Decoding the bits of a move gives the move. -/
@[simp] theorem decMove_moveBit (m : SignType) : decMove (moveBit m) = m := by
  rcases m with _ | _ | _ <;> rfl

/-- Decoding the bits of a view of the output gives the view. -/
@[simp] theorem decOut_outBit (o : OutView) : decOut (outBit o) = o := by
  unfold decOut outBit
  rw [bitsVal_testBit _ _ (by have := o.index_lt; omega), OutView.ofIndex_index]

/-- Decoding a symbol reads only the first two bits. -/
theorem decSym_congr {f g : ℕ → Bool} (h : ∀ i < 2, f i = g i) : decSym f = decSym g := by
  unfold decSym
  rw [h 0 (by omega), h 1 (by omega)]

/-- Decoding a write reads only the first two bits. -/
private theorem decWrite_congr {f g : ℕ → Bool} (h : ∀ i < 2, f i = g i) :
    decWrite f = decWrite g := by
  unfold decWrite
  rw [h 0 (by omega), h 1 (by omega)]

/-- Decoding a move reads only the first two bits. -/
theorem decMove_congr {f g : ℕ → Bool} (h : ∀ i < 2, f i = g i) : decMove f = decMove g := by
  unfold decMove
  rw [h 0 (by omega), h 1 (by omega)]

/-- Decoding a view of the output reads only the first two bits. -/
theorem decOut_congr {f g : ℕ → Bool} (h : ∀ i < 2, f i = g i) : decOut f = decOut g := by
  unfold decOut
  rw [bitsVal_congr h]

section States

variable [Fintype State]

/-- The width of the code of a state. -/
def stWidth (State : Type) [Fintype State] : ℕ := Fintype.card (Option State)

/-- The index of a state. -/
noncomputable def stateIdx (q : Option State) : ℕ := (Fintype.equivFin (Option State) q).val

/-- The index of a state is below the width of the code of states. -/
private theorem stateIdx_lt (q : Option State) : stateIdx q < stWidth State :=
  (Fintype.equivFin (Option State) q).isLt

/-- The index of a state is below `2` to the width of the code of states. -/
private theorem stateIdx_lt_two_pow (q : Option State) : stateIdx q < 2 ^ stWidth State :=
  lt_of_lt_of_le (stateIdx_lt q) (Nat.lt_two_pow_self).le

/-- The bits of a state: its index in binary. -/
noncomputable def stateBit (q : Option State) (i : ℕ) : Bool := (stateIdx q).testBit i

/-- Decoding the bits of a state. -/
noncomputable def decState (f : ℕ → Bool) : Option State :=
  if h : bitsVal f (stWidth State) < stWidth State then
    (Fintype.equivFin (Option State)).symm ⟨_, h⟩
  else none

/-- Decoding the bits of a state gives the state. -/
@[simp] theorem decState_stateBit (q : Option State) : decState (stateBit q) = q := by
  unfold decState stateBit
  rw [dite_eq_left (by rw [bitsVal_testBit _ _ (stateIdx_lt_two_pow q)]; exact stateIdx_lt q)]
  simp only [bitsVal_testBit _ _ (stateIdx_lt_two_pow q)]
  exact (Fintype.equivFin (Option State)).symm_apply_apply q

/-- Decoding a state reads only the bits below the width of its code. -/
theorem decState_congr {f g : ℕ → Bool} (h : ∀ i < stWidth State, f i = g i) :
    (decState f : Option State) = decState g := by
  unfold decState
  simp only [bitsVal_congr h]

end States

/-! ### Bits of the finite part -/

section CtrlBits

variable [Fintype State]

/-- The width of the bits of a finite part. -/
def ctrlWidth (k : ℕ) (State : Type) [Fintype State] : ℕ := stWidth State + 8 + 8 * k

/-- The offset of the bits of work tape `j` in a finite part. -/
def tapeOff (State : Type) [Fintype State] (j : ℕ) : ℕ := stWidth State + 8 + 8 * j

/-- The bits of a finite part: the state, then two bits each for the symbol under the input head,
the input move, the emitted symbol and the view of the output, then eight bits per work tape for
the symbol read, the symbol written, the move and the symbol left. -/
noncomputable def ctrlBit (c : Ctrl k State) (i : ℕ) : Bool :=
  let S := stWidth State
  if i < S then stateBit c.state i
  else if i < S + 2 then symBit c.inSym (i - S)
  else if i < S + 4 then moveBit c.inMove (i - (S + 2))
  else if i < S + 6 then symBit c.emit (i - (S + 4))
  else if i < S + 8 then outBit c.out (i - (S + 6))
  else if h : S + 8 ≤ i ∧ i < S + 8 + 8 * k then
    let j : Fin k := ⟨(i - (S + 8)) / 8, by omega⟩
    let r := (i - (S + 8)) % 8
    if r < 2 then symBit (c.read j) r
    else if r < 4 then writeBit (c.write j) (r - 2)
    else if r < 6 then moveBit (c.move j) (r - 4)
    else symBit (c.after j) (r - 6)
  else false

/-- Decoding the bits of a finite part. -/
noncomputable def decCtrl (f : ℕ → Bool) : Ctrl k State where
  state := decState f
  inSym := decSym fun i => f (stWidth State + i)
  inMove := decMove fun i => f (stWidth State + 2 + i)
  emit := decSym fun i => f (stWidth State + 4 + i)
  out := decOut fun i => f (stWidth State + 6 + i)
  read j := decSym fun i => f (tapeOff State j + i)
  write j := decWrite fun i => f (tapeOff State j + 2 + i)
  move j := decMove fun i => f (tapeOff State j + 4 + i)
  after j := decSym fun i => f (tapeOff State j + 6 + i)

/-- Decoding a finite part reads only the bits below its width. -/
theorem decCtrl_congr {f g : ℕ → Bool} (h : ∀ i < ctrlWidth k State, f i = g i) :
    (decCtrl f : Ctrl k State) = decCtrl g := by
  unfold decCtrl ctrlWidth tapeOff at *
  congr 1
  · exact decState_congr fun i hi => h i (by omega)
  · exact decSym_congr fun i hi => h _ (by omega)
  · exact decMove_congr fun i hi => h _ (by omega)
  · exact decSym_congr fun i hi => h _ (by omega)
  · exact decOut_congr fun i hi => h _ (by omega)
  · funext j; exact decSym_congr fun i hi => h _ (by have := j.isLt; omega)
  · funext j; exact decWrite_congr fun i hi => h _ (by have := j.isLt; omega)
  · funext j; exact decMove_congr fun i hi => h _ (by have := j.isLt; omega)
  · funext j; exact decSym_congr fun i hi => h _ (by have := j.isLt; omega)

/-- The bits of work tape `j` in a finite part. -/
private theorem ctrlBit_tape (c : Ctrl k State) (j : Fin k) {r : ℕ} (hr : r < 8) :
    ctrlBit c (tapeOff State j + r) =
      if r < 2 then symBit (c.read j) r
      else if r < 4 then writeBit (c.write j) (r - 2)
      else if r < 6 then moveBit (c.move j) (r - 4)
      else symBit (c.after j) (r - 6) := by
  unfold ctrlBit tapeOff
  have hj := j.isLt
  simp only [show ¬ stWidth State + 8 + 8 * (j : ℕ) + r < stWidth State by omega,
    show ¬ stWidth State + 8 + 8 * (j : ℕ) + r < stWidth State + 2 by omega,
    show ¬ stWidth State + 8 + 8 * (j : ℕ) + r < stWidth State + 4 by omega,
    show ¬ stWidth State + 8 + 8 * (j : ℕ) + r < stWidth State + 6 by omega,
    show ¬ stWidth State + 8 + 8 * (j : ℕ) + r < stWidth State + 8 by omega, ite_false]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  have h1 : (stWidth State + 8 + 8 * (j : ℕ) + r - (stWidth State + 8)) / 8 = j := by omega
  have h2 : (stWidth State + 8 + 8 * (j : ℕ) + r - (stWidth State + 8)) % 8 = r := by omega
  simp only [h1, h2]

/-- The bits of the state of a finite part. -/
theorem ctrlBit_state (c : Ctrl k State) {i : ℕ} (hi : i < stWidth State) :
    ctrlBit c i = stateBit c.state i := by
  unfold ctrlBit
  rw [ite_eq_left hi]

/-- The bits of the symbol under the input head of a finite part. -/
theorem ctrlBit_inSym (c : Ctrl k State) {i : ℕ} (hi : i < 2) :
    ctrlBit c (stWidth State + i) = symBit c.inSym i := by
  unfold ctrlBit
  simp only [show ¬ stWidth State + i < stWidth State by omega,
    show stWidth State + i < stWidth State + 2 by omega, ite_false, ite_true,
    Nat.add_sub_cancel_left]

/-- The bits of the input move of a finite part. -/
theorem ctrlBit_inMove (c : Ctrl k State) {i : ℕ} (hi : i < 2) :
    ctrlBit c (stWidth State + 2 + i) = moveBit c.inMove i := by
  unfold ctrlBit
  simp only [show ¬ stWidth State + 2 + i < stWidth State by omega,
    show ¬ stWidth State + 2 + i < stWidth State + 2 by omega,
    show stWidth State + 2 + i < stWidth State + 4 by omega, ite_false, ite_true,
    Nat.add_sub_cancel_left]

/-- The bits of the emitted symbol of a finite part. -/
private theorem ctrlBit_emit (c : Ctrl k State) {i : ℕ} (hi : i < 2) :
    ctrlBit c (stWidth State + 4 + i) = symBit c.emit i := by
  unfold ctrlBit
  simp only [show ¬ stWidth State + 4 + i < stWidth State by omega,
    show ¬ stWidth State + 4 + i < stWidth State + 2 by omega,
    show ¬ stWidth State + 4 + i < stWidth State + 4 by omega,
    show stWidth State + 4 + i < stWidth State + 6 by omega, ite_false, ite_true,
    Nat.add_sub_cancel_left]

/-- The bits of the view of the output of a finite part. -/
theorem ctrlBit_out (c : Ctrl k State) {i : ℕ} (hi : i < 2) :
    ctrlBit c (stWidth State + 6 + i) = outBit c.out i := by
  unfold ctrlBit
  simp only [show ¬ stWidth State + 6 + i < stWidth State by omega,
    show ¬ stWidth State + 6 + i < stWidth State + 2 by omega,
    show ¬ stWidth State + 6 + i < stWidth State + 4 by omega,
    show ¬ stWidth State + 6 + i < stWidth State + 6 by omega,
    show stWidth State + 6 + i < stWidth State + 8 by omega, ite_false, ite_true,
    Nat.add_sub_cancel_left]

/-- The bits of the symbol read by work head `j`. -/
theorem ctrlBit_read (c : Ctrl k State) (j : Fin k) {i : ℕ} (hi : i < 2) :
    ctrlBit c (tapeOff State j + i) = symBit (c.read j) i := by
  rw [ctrlBit_tape c j (by omega), ite_eq_left hi]

/-- The bits of the write of work head `j`. -/
private theorem ctrlBit_write (c : Ctrl k State) (j : Fin k) {i : ℕ} (hi : i < 2) :
    ctrlBit c (tapeOff State j + 2 + i) = writeBit (c.write j) i := by
  rw [Nat.add_assoc, ctrlBit_tape c j (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel_left]

/-- The bits of the move of work head `j`. -/
theorem ctrlBit_move (c : Ctrl k State) (j : Fin k) {i : ℕ} (hi : i < 2) :
    ctrlBit c (tapeOff State j + 4 + i) = moveBit (c.move j) i := by
  rw [Nat.add_assoc, ctrlBit_tape c j (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel_left]

/-- The bits of the symbol left under work head `j`. -/
theorem ctrlBit_after (c : Ctrl k State) (j : Fin k) {i : ℕ} (hi : i < 2) :
    ctrlBit c (tapeOff State j + 6 + i) = symBit (c.after j) i := by
  rw [Nat.add_assoc, ctrlBit_tape c j (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- **Decoding inverts the bits of a finite part.** -/
@[simp] theorem decCtrl_ctrlBit (c : Ctrl k State) : decCtrl (ctrlBit c) = c := by
  cases c
  simp only [decCtrl]
  congr 1
  · rw [decState_congr fun i hi => ctrlBit_state _ hi, decState_stateBit]
  · rw [decSym_congr fun i hi => ctrlBit_inSym _ hi, decSym_symBit]
  · rw [decMove_congr fun i hi => ctrlBit_inMove _ hi, decMove_moveBit]
  · rw [decSym_congr fun i hi => ctrlBit_emit _ hi, decSym_symBit]
  · rw [decOut_congr fun i hi => ctrlBit_out _ hi, decOut_outBit]
  · funext j
    rw [decSym_congr fun i hi => ctrlBit_read _ j hi, decSym_symBit]
  · funext j
    rw [decWrite_congr fun i hi => ctrlBit_write _ j hi, decWrite_writeBit]
  · funext j
    rw [decMove_congr fun i hi => ctrlBit_move _ j hi, decMove_moveBit]
  · funext j
    rw [decSym_congr fun i hi => ctrlBit_after _ j hi, decSym_symBit]

end CtrlBits

/-! ### Parameters and variables -/

/-- The nine families of constraints of the formula. -/
inductive Family
  /-- the variables `true` and `false` are the constants -/
  | consts
  /-- the first record holds the initial configuration -/
  | init
  /-- the last record holds the accepting configuration -/
  | final
  /-- for each step, the finite parts of two consecutive records are an allowed pair -/
  | step
  /-- the input head moves as the record says -/
  | inMove
  /-- the symbol under the input head is the input symbol there -/
  | inSym
  /-- the work heads move as the record says -/
  | workMove
  /-- one switch of the sorting network of a tape, with a free flag -/
  | switch
  /-- for each sorted position of a tape, the keys increase and the symbol read is the symbol the
  previous visit of the cell left -/
  | sorted
  deriving DecidableEq

namespace Family

/-- The position of a family in the order in which the variables and clauses are numbered. -/
def index : Family → ℕ
  | consts => 0
  | init => 1
  | final => 2
  | step => 3
  | inMove => 4
  | inSym => 5
  | workMove => 6
  | switch => 7
  | sorted => 8

/-- The families, in the order of `index`. -/
def all : List Family :=
  [consts, init, final, step, inMove, inSym, workMove, switch, sorted]

/-- The family with the given number, if there is one. -/
def ofIndex? (n : ℕ) : Option Family := all[n]?

/-- Every family has a number below `9`. -/
theorem index_lt (f : Family) : f.index < 9 := by cases f <;> decide

/-- Looking up the number of a family gives the family. -/
theorem ofIndex?_index (f : Family) : ofIndex? f.index = some f := by cases f <;> rfl

/-- Every number below `9` is the number of a family. -/
theorem exists_index_eq {n : ℕ} (hn : n < 9) : ∃ f : Family, f.index = n := by
  interval_cases n
  exacts [⟨.consts, rfl⟩, ⟨.init, rfl⟩, ⟨.final, rfl⟩, ⟨.step, rfl⟩, ⟨.inMove, rfl⟩,
    ⟨.inSym, rfl⟩, ⟨.workMove, rfl⟩, ⟨.switch, rfl⟩, ⟨.sorted, rfl⟩]

/-- The number a family is found at is its own number. -/
theorem index_eq_of_ofIndex?_eq_some {n : ℕ} {f : Family} (h : ofIndex? n = some f) :
    f.index = n := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  have h9 : n < 9 := by simpa [all] using hn
  interval_cases n <;> rfl

end Family

/-- The parameters of the formula: the number of work tapes, the width of the code of a state, the
length of the input and the slack. -/
structure Layout where
  /-- the number of work tapes -/
  k : ℕ
  /-- the width of the code of a state -/
  S : ℕ
  /-- the length of the input -/
  n : ℕ
  /-- the slack, so that the machine runs for fewer than `2 ^ (n + κ + 1)` steps -/
  κ : ℕ

/-- The data a formula needs from the machine: the bits of the initial state and of the halted
state, and the bits of the allowed pairs of finite parts. -/
structure MachineData where
  /-- the bits of the initial state -/
  q0 : List Bool
  /-- the bits of the halted state -/
  halt : List Bool
  /-- the bits of the allowed pairs of finite parts, each of length `2 C` -/
  pairs : List (List Bool)

namespace Layout

variable (Λ : Layout)

/-- The number of bits of a time. -/
def τ : ℕ := Λ.n + Λ.κ + 1
/-- The number of records. -/
def N : ℕ := 2 ^ Λ.τ
/-- The width of a work-head position, offset by `N`. -/
def W : ℕ := Λ.τ + 2
/-- The width of the input-head position. -/
def I : ℕ := Λ.n + 2
/-- The width of the finite part. -/
def C : ℕ := Λ.S + 8 + 8 * Λ.k
/-- The width of a record. -/
def RB : ℕ := Λ.C + Λ.I + Λ.k * Λ.W
/-- The width of a payload of a sorting network: the time, the position, the symbol read and the
symbol left. -/
def P : ℕ := Λ.τ + Λ.W + 4
/-- The number of layers of a sorting network. -/
def L : ℕ := (schedule Λ.τ).length

/-- The offset of the bits of work tape `j` in the finite part. -/
def offTape (j : ℕ) : ℕ := Λ.S + 8 + 8 * j
/-- The offset of the input-head position in a record. -/
def offIn : ℕ := Λ.C
/-- The offset of the position of work head `j` in a record. -/
def offPos (j : ℕ) : ℕ := Λ.C + Λ.I + Λ.W * j

/-- The constant `true`. -/
def vTT : ℕ := 0
/-- The constant `false`. -/
def vFF : ℕ := 1
/-- Bit `f` of record `t`. -/
def vRec (t f : ℕ) : ℕ := 2 + 8 * (t * Λ.RB + f)
/-- Bit `b` of position `w` after layer `ℓ + 1` of the network of tape `j`. -/
def vArr (j ℓ w b : ℕ) : ℕ := 3 + 8 * (((j * Λ.L + ℓ) * Λ.N + w) * Λ.P + b)
/-- The flag of layer `ℓ` at the lower position `w` of the network of tape `j`. -/
def vFlag (j ℓ w : ℕ) : ℕ := 4 + 8 * ((j * Λ.L + ℓ) * Λ.N + w)

/-- A bound on the inner index of the variables of the first four kinds. -/
def inner : ℕ := Λ.N * Λ.RB + (Λ.k * Λ.L + 1) * Λ.N * (Λ.P + 1)
/-- The first fresh variable. -/
def AUX : ℕ := 8 * Λ.inner + 8

/-- A bound on the number of constraints of a family. -/
def MAXI : ℕ := 3 * Λ.N * Λ.I * (Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)

/-- A bound on the number of fresh variables of a constraint, for `R` allowed pairs. -/
def A (R : ℕ) : ℕ :=
  2 * (Λ.S + Λ.I + Λ.k * Λ.W + 2) + 4 * Λ.C * R + R + 4 * Λ.I + 4 + 9 * Λ.W +
    5 * (Λ.τ + Λ.W) + 2 * Λ.W + 4

/-- Fresh variable `i` of constraint `inst` of family `fam`. -/
def vAux (R : ℕ) (fam : Family) (inst i : ℕ) : ℕ :=
  Λ.AUX + (fam.index * Λ.MAXI + inst) * Λ.A R + i

/-- The variable holding bit `b` of the payload of record `t` in the network of tape `j`, before
the first layer: the bits of `t`, the position of head `j`, the symbol it reads and the symbol it
leaves. -/
def pay0 (j t b : ℕ) : ℕ :=
  if b < Λ.τ then (if t.testBit b then vTT else vFF)
  else if b < Λ.τ + Λ.W then Λ.vRec t (Λ.offPos j + (b - Λ.τ))
  else if b < Λ.τ + Λ.W + 2 then Λ.vRec t (Λ.offTape j + (b - (Λ.τ + Λ.W)))
  else Λ.vRec t (Λ.offTape j + 6 + (b - (Λ.τ + Λ.W + 2)))

/-- The variable holding bit `b` at position `w` after `ℓ` layers of the network of tape `j`. -/
def arrAt (j ℓ w b : ℕ) : ℕ := if ℓ = 0 then Λ.pay0 j w b else Λ.vArr j (ℓ - 1) w b

/-- The exponent of layer `ℓ`. -/
def expo (ℓ : ℕ) : ℕ := ((schedule Λ.τ).getD ℓ (0, 0)).2

/-- There are at least two records. -/
theorem two_le_N : 2 ≤ Λ.N := by
  unfold N τ
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (Λ.n + Λ.κ + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The work-head positions are offset by `N`, with room for `4 * N`. -/
theorem four_mul_N_eq_two_pow_W : 4 * Λ.N = 2 ^ Λ.W := by
  unfold N W
  rw [Nat.pow_add]
  ring

/-- The exponent of every layer is below `τ`. -/
theorem expo_lt {ℓ : ℕ} (hℓ : ℓ < Λ.L) : Λ.expo ℓ < Λ.τ := by
  unfold expo
  rw [List.getD_eq_getElem _ _ hℓ]
  have := mem_schedule (List.getElem_mem hℓ)
  omega

/-- The literals saying that the bits of record `t` from offset `off` are `bs`. -/
def fieldLits (t off : ℕ) (bs : List Bool) : List (ℕ × Bool) :=
  (List.range bs.length).map fun i => (Λ.vRec t (off + i), bs.getD i false)

/-- The move with code `m`: `0` stay, `1` right, `2` left. -/
def moveCode (m : ℕ) : SignType := if m = 1 then .pos else if m = 2 then .neg else .zero

/-- The list of the first two bits of a function. -/
def two (f : ℕ → Bool) : List Bool := [f 0, f 1]

/-! ### The constraints -/

variable (D : MachineData) (x : List Bool)

/-- The number of constraints of each family. -/
def count : Family → ℕ
  | .consts | .init | .final => 1
  | .step => Λ.N - 1
  | .inMove => (Λ.N - 1) * Λ.I * 3
  | .inSym => Λ.N * Λ.I
  | .workMove => (Λ.N - 1) * Λ.k
  | .switch => Λ.k * Λ.L * Λ.N * Λ.P
  | .sorted => Λ.k * Λ.N

/-- The literals of the first record: the initial state, the input head on the first cell, the
work heads at `0` and the empty output. -/
def initLits : List (ℕ × Bool) :=
  Λ.fieldLits 0 0 D.q0 ++ Λ.fieldLits 0 Λ.offIn (BitString.lowBits Λ.I 1) ++
    ((List.range Λ.k).flatMap fun j => Λ.fieldLits 0 (Λ.offPos j) (BitString.lowBits Λ.W Λ.N)) ++
    Λ.fieldLits 0 (Λ.S + 6) (two (outBit .empty))

/-- The literals of the last record: halted, with output `[true]`. -/
def finalLits : List (ℕ × Bool) :=
  Λ.fieldLits (Λ.N - 1) 0 D.halt ++ Λ.fieldLits (Λ.N - 1) (Λ.S + 6) (two (outBit (.one true)))

/-- The patterns of the finite parts of records `t` and `t + 1`, one for each allowed pair. -/
def stepPats (t : ℕ) : List (List (ℕ × Bool)) :=
  D.pairs.map fun bs => (List.range (2 * Λ.C)).map fun i =>
    (if i < Λ.C then Λ.vRec t i else Λ.vRec (t + 1) (i - Λ.C), bs.getD i false)

/-- The literals of the antecedent of an input-head move: the head at `z`, moving by `m`. -/
def inMoveLits (t z m : ℕ) : List (ℕ × Bool) :=
  Λ.fieldLits t Λ.offIn (BitString.lowBits Λ.I z) ++
    Λ.fieldLits t (Λ.S + 2) (two (moveBit (moveCode m)))

/-- The literals of the consequent of an input-head move. -/
def inNextLits (t z m : ℕ) : List (ℕ × Bool) :=
  Λ.fieldLits (t + 1) Λ.offIn (BitString.lowBits Λ.I (StepRecord.moveIn Λ.n z (moveCode m)))

/-- The literals of the input head at `z`. -/
def inAtLits (t z : ℕ) : List (ℕ × Bool) := Λ.fieldLits t Λ.offIn (BitString.lowBits Λ.I z)

/-- The literals of the symbol under the input head at `z`. -/
def inSymLits (t z : ℕ) : List (ℕ × Bool) :=
  Λ.fieldLits t Λ.S (two (symBit (StepRecord.inSym x z)))

/-- The pairs of the positions of head `j` in records `t` and `t + 1`. -/
def posPairs (t j : ℕ) : List (ℕ × ℕ) :=
  (List.range Λ.W).map fun i => (Λ.vRec t (Λ.offPos j + i), Λ.vRec (t + 1) (Λ.offPos j + i))

/-- The pairs of the keys of sorted positions `u - 1` and `u` of the network of tape `j`. -/
def keyPairs (j u : ℕ) : List (ℕ × ℕ) :=
  (List.range (Λ.τ + Λ.W)).map fun b => (Λ.arrAt j Λ.L (u - 1) b, Λ.arrAt j Λ.L u b)

/-- The pairs of the positions of sorted positions `u - 1` and `u` of the network of tape `j`. -/
def samePairs (j u : ℕ) : List (ℕ × ℕ) :=
  (List.range Λ.W).map fun i => (Λ.arrAt j Λ.L (u - 1) (Λ.τ + i), Λ.arrAt j Λ.L u (Λ.τ + i))

/-- The gates defining the fresh variables of constraint `inst` of family `fam`, from the base
`vAux R fam inst 0`. -/
def famDefs (fam : Family) (inst : ℕ) : List Gate :=
  let β := Λ.vAux D.pairs.length fam inst 0
  match fam with
  | .consts => [⟨.not, β, vFF, 0, 0⟩]
  | .init => matchGadget β vTT (Λ.initLits D)
  | .final => matchGadget β vTT (Λ.finalLits D)
  | .step => tableGadget β vTT vFF (2 * Λ.C) (Λ.stepPats D inst)
  | .inMove =>
    matchGadget β vTT (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)) ++
      matchGadget (β + 2 * (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length)
        vTT (Λ.inNextLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3))
  | .inSym =>
    matchGadget β vTT (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)) ++
      matchGadget (β + 2 * (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)).length) vTT
        (Λ.inSymLits x (inst / Λ.I) (inst % Λ.I))
  | .workMove =>
    addGadget β vTT (Λ.vRec (inst / Λ.k) (Λ.offTape (inst % Λ.k) + 4))
      (Λ.vRec (inst / Λ.k) (Λ.offTape (inst % Λ.k) + 5)) (Λ.posPairs (inst / Λ.k) (inst % Λ.k))
  | .switch => []
  | .sorted =>
    if inst % Λ.N = 0 then
      [⟨.not, β, Λ.arrAt (inst / Λ.N) Λ.L 0 (Λ.τ + Λ.W), 0, 0⟩,
        ⟨.not, β + 1, Λ.arrAt (inst / Λ.N) Λ.L 0 (Λ.τ + Λ.W + 1), 0, 0⟩]
    else
      ltGadget β vFF (Λ.keyPairs (inst / Λ.N) (inst % Λ.N)) ++
        eqGadget (β + 5 * (Λ.τ + Λ.W)) vTT (Λ.samePairs (inst / Λ.N) (inst % Λ.N)) ++
        [⟨.xnor, β + 5 * (Λ.τ + Λ.W) + 2 * Λ.W, Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W),
            Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N - 1) (Λ.τ + Λ.W + 2), 0⟩,
          ⟨.xnor, β + 5 * (Λ.τ + Λ.W) + 2 * Λ.W + 1,
            Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W + 1),
            Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N - 1) (Λ.τ + Λ.W + 3), 0⟩]

/-- The constraint gates of constraint `inst` of family `fam`: assertions on the outputs of the
gadgets, and the switches of the networks. -/
def famCons (fam : Family) (inst : ℕ) : List Gate :=
  let β := Λ.vAux D.pairs.length fam inst 0
  match fam with
  | .consts => [⟨.assert, 0, vTT, 0, 0⟩, ⟨.assert, 0, β, 0, 0⟩]
  | .init => [⟨.assert, 0, matchOut β vTT (Λ.initLits D).length, 0, 0⟩]
  | .final => [⟨.assert, 0, matchOut β vTT (Λ.finalLits D).length, 0, 0⟩]
  | .step => [⟨.assert, 0, tableOut β vFF (2 * Λ.C) (Λ.stepPats D inst).length, 0, 0⟩]
  | .inMove =>
    [⟨.imp, 0, matchOut β vTT
        (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length,
      matchOut (β + 2 * (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length)
        vTT (Λ.inNextLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length, 0⟩]
  | .inSym =>
    [⟨.imp, 0, matchOut β vTT (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)).length,
      matchOut (β + 2 * (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)).length) vTT
        (Λ.inSymLits x (inst / Λ.I) (inst % Λ.I)).length, 0⟩]
  | .workMove => [⟨.assert, 0, addOut β vTT Λ.W, 0, 0⟩]
  | .switch =>
    [⟨.mux, Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L + 1) (inst / Λ.P % Λ.N)
        (inst % Λ.P),
      Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L)
        (partner (Λ.expo (inst / Λ.P / Λ.N % Λ.L)) (inst / Λ.P % Λ.N)) (inst % Λ.P),
      Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L) (inst / Λ.P % Λ.N) (inst % Λ.P),
      Λ.vFlag (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L)
        (low (Λ.expo (inst / Λ.P / Λ.N % Λ.L)) (inst / Λ.P % Λ.N))⟩]
  | .sorted =>
    if inst % Λ.N = 0 then [⟨.assert, 0, β, 0, 0⟩, ⟨.assert, 0, β + 1, 0, 0⟩]
    else
      [⟨.assert, 0, ltOut β vFF (Λ.τ + Λ.W), 0, 0⟩,
        ⟨.imp, 0, eqOut (β + 5 * (Λ.τ + Λ.W)) vTT Λ.W, β + 5 * (Λ.τ + Λ.W) + 2 * Λ.W, 0⟩,
        ⟨.imp, 0, eqOut (β + 5 * (Λ.τ + Λ.W)) vTT Λ.W, β + 5 * (Λ.τ + Λ.W) + 2 * Λ.W + 1, 0⟩,
        ⟨.imp, 0, Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W),
          eqOut (β + 5 * (Λ.τ + Λ.W)) vTT Λ.W, 0⟩,
        ⟨.imp, 0, Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W + 1),
          eqOut (β + 5 * (Λ.τ + Λ.W)) vTT Λ.W, 0⟩]

/-- All gates of a constraint. -/
def famGates (fam : Family) (inst : ℕ) : List Gate :=
  Λ.famDefs D x fam inst ++ Λ.famCons D x fam inst

/-- An assignment satisfies every gate of every constraint. -/
def Sat (σ : ℕ → Bool) : Prop :=
  ∀ (fam : Family), ∀ inst < Λ.count fam, ∀ g ∈ Λ.famGates D x fam inst, g.Holds σ

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
