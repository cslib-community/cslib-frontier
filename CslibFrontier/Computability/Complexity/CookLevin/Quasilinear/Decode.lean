/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Meaning
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Sorted
public import CslibFrontier.Foundations.Data.Nat.MulAddDiv

/-!
# The machine data of the quasilinear formula and decoding records

The formula of `Cslib.Complexity.CookLevin.Quasilinear.Layout` reads three things from the machine
(`machineData`): the bits of the initial state, of the halted state, and of every allowed pair of
finite parts (`allowedPairs`). An assignment of its variables is read back as step records
(`Layout.recOf`): the finite part of each record is decoded from its bits, and the head positions
are read in binary.

This file also collects the arithmetic of the layout: literals of fields and binary digits.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.allowedPairs`, `machineData`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.ctrlOf`, `Layout.inPosOf`, `Layout.posVal`,
  `Layout.recOf`: records read from an assignment.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

variable {k : ℕ} {State : Type} [Fintype State]

/-! ### Fields of the finite part -/

/-- Symbols with the same two bits are equal. -/
theorem symBit_injective {s s' : Option Bool} (h : ∀ i < 2, symBit s i = symBit s' i) :
    s = s' := by
  rw [← decSym_symBit s, ← decSym_symBit s', decSym_congr h]

/-- States with the same bits are equal. -/
theorem stateBit_injective {q q' : Option State} (h : ∀ i < stWidth State, stateBit q i =
    stateBit q' i) : q = q' := by
  rw [← decState_stateBit q, ← decState_stateBit q', decState_congr h]

/-- Views of the output with the same two bits are equal. -/
theorem outBit_injective {o o' : OutView} (h : ∀ i < 2, outBit o i = outBit o' i) : o = o' := by
  rw [← decOut_outBit o, ← decOut_outBit o', decOut_congr h]

/-- Moves with the same two bits are equal. -/
theorem moveBit_injective {m m' : SignType} (h : ∀ i < 2, moveBit m i = moveBit m' i) :
    m = m' := by
  rw [← decMove_moveBit m, ← decMove_moveBit m', decMove_congr h]

/-! ### The machine data -/

open Classical in
/-- The allowed pairs of finite parts of `ntm`. -/
noncomputable def allowedPairs (ntm : MultiTapeNTM k Bool State) :
    List (Ctrl k State × Ctrl k State) :=
  (Finset.univ.filter fun p : Ctrl k State × Ctrl k State => Ctrl.Allowed ntm p.1 p.2).toList

/-- A pair is allowed exactly when `Ctrl.Allowed` holds. -/
theorem mem_allowedPairs {ntm : MultiTapeNTM k Bool State} {p : Ctrl k State × Ctrl k State} :
    p ∈ allowedPairs ntm ↔ Ctrl.Allowed ntm p.1 p.2 := by
  simp [allowedPairs]

/-- The bits of a pair of finite parts. -/
noncomputable def pairBits (c c' : Ctrl k State) : List Bool :=
  (List.range (2 * ctrlWidth k State)).map fun i =>
    if i < ctrlWidth k State then ctrlBit c i else ctrlBit c' (i - ctrlWidth k State)

/-- What the formula reads from the machine. -/
noncomputable def machineData (ntm : MultiTapeNTM k Bool State) : MachineData :=
  ⟨(List.range (stWidth State)).map (stateBit (some ntm.q₀)),
    (List.range (stWidth State)).map (stateBit (none : Option State)),
    (allowedPairs ntm).map fun p => pairBits p.1 p.2⟩

/-- The layout for a machine with `k` work tapes and states `State`, on inputs of length `n`. -/
def layoutOf (k : ℕ) (State : Type) [Fintype State] (κ n : ℕ) : Layout :=
  ⟨k, stWidth State, n, κ⟩

/-! ### Arithmetic of the layout -/

namespace Layout

variable (Λ : Layout)

/-- The literals of a field hold exactly when the bits of the record at the field are `bs`. -/
theorem litsHold_fieldLits {σ : ℕ → Bool} {t off : ℕ} {bs : List Bool} :
    LitsHold σ (Λ.fieldLits t off bs) ↔
      ∀ i < bs.length, σ (Λ.vRec t (off + i)) = bs.getD i false := by
  simp only [LitsHold, fieldLits, List.mem_map, List.mem_range]
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

/-- A digit of `lowBits` inside its width is the digit of the number. -/
theorem getD_lowBits {w v i : ℕ} (hi : i < w) :
    (BitString.lowBits w v).getD i false = v.testBit i := by
  simp [BitString.lowBits, List.getD_eq_getElem?_getD, hi]

/-- The list of two bits has length two. -/
@[simp] theorem length_two (f : ℕ → Bool) : (two f).length = 2 := rfl

/-- Reading one of the two bits. -/
theorem getD_two (f : ℕ → Bool) {i : ℕ} (hi : i < 2) : (two f).getD i false = f i := by
  interval_cases i <;> rfl

/-- Digits determine a number below `2 ^ w`. -/
theorem digits_iff {f : ℕ → Bool} {w v : ℕ} (hv : v < 2 ^ w) :
    (∀ i < w, f i = v.testBit i) ↔ bitsVal f w = v := by
  constructor
  · intro h
    rw [bitsVal_congr h, bitsVal_testBit _ _ hv]
  · intro h
    have := bitsVal_injective (f := f) (g := fun i => v.testBit i) (k := w)
      (by rw [h, bitsVal_testBit _ _ hv])
    exact this

/-! ### Records read from an assignment -/

/-- The finite part of record `t`. -/
noncomputable def ctrlOf (σ : ℕ → Bool) (t : ℕ) : Ctrl k State :=
  decCtrl fun i => σ (Λ.vRec t i)

/-- The input-head position of record `t`. -/
def inPosOf (σ : ℕ → Bool) (t : ℕ) : ℕ := bitsVal (fun i => σ (Λ.vRec t (Λ.offIn + i))) Λ.I

/-- The offset position of work head `j` in record `t`. -/
def posVal (σ : ℕ → Bool) (t j : ℕ) : ℕ := bitsVal (fun i => σ (Λ.vRec t (Λ.offPos j + i))) Λ.W

/-- Record `t`, read from an assignment. -/
noncomputable def recOf (σ : ℕ → Bool) (t : ℕ) : StepRecord k State :=
  ⟨(Λ.ctrlOf σ t : Ctrl k State).state, Λ.inPosOf σ t, fun j => (Λ.posVal σ t j : ℤ) - Λ.N,
    (Λ.ctrlOf σ t : Ctrl k State).read, (Λ.ctrlOf σ t : Ctrl k State).out,
    (Λ.ctrlOf σ t : Ctrl k State).action (Λ.ctrlOf σ (t + 1) : Ctrl k State).state⟩

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
