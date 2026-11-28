/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Compiler

/-!
# A natural-scalar basis with standard word-RAM implementations

`model` supplies the scalar operations and comparisons used by cached-height AVL algorithms.
`scalars` implements them by ordinary word-RAM instructions, with no heap effects. Zero costs
one instruction; maximum-plus-one and the height-gap comparison cost at most five; the other
comparisons cost at most three. Operand and destination registers may coincide, including
compiler temporaries. Operands are consumed before the selected temporary is overwritten.

Only the height-gap test needs extra admissibility: the truncated difference must fit a word.
In particular it does not compute `b + 1`, which could overflow at the largest word value.
-/

public section
namespace Cslib.PointerMachine.WordRAM.Natural
open Cslib.WordRAM (Code ExecWithin)

/-- Natural scalar operations used for cached subtree heights. -/
inductive Operation where
  /-- Return zero, ignoring both operands. -/
  | zero
  /-- One plus the larger operand. -/
  | maxSucc
  deriving DecidableEq

/-- Ordering and height-gap predicates on natural scalars. -/
inductive Test where
  /-- Strict scalar comparison. -/
  | lt
  /-- Nonstrict scalar comparison. -/
  | le
  /-- The first operand exceeds the second by at least two. -/
  | heavy
  deriving DecidableEq

/-- Natural scalar keys, payloads and heights; pointers remain in a separate machine bank. -/
abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Operation
  Test := Test
  evalOp
    | .zero, _, _ => 0
    | .maxSucc, a, b => max a b + 1
  evalTest
    | .lt, a, b => decide (a < b)
    | .le, a, b => decide (a ≤ b)
    | .heavy, a, b => decide (b + 1 < a)

private theorem select_spec {r : ℕ} (w : ℕ) (c : Cslib.WordRAM.Cond r) (d : Fin r)
    (x : Cslib.WordRAM.Data r) (yes no : ℕ)
    (hy : Cslib.WordRAM.Fits w yes) (hn : Cslib.WordRAM.Fits w no) :
    ExecWithin (B := .standard) w (.branch c (.op (.const d yes)) (.op (.const d no)))
      x (x.set d (if c.Holds x then yes else no)) 3 := by
  by_cases h : c.Holds x
  · simpa only [h, ↓reduceIte] using ((ExecWithin.const (d := d) (x := x) hy).branch_pos h).mono
      (show 1 + 1 ≤ 3 by decide)
  · simpa only [h, ↓reduceIte] using (ExecWithin.const (d := d) (x := x) hn).branch_neg h

private theorem scratch_result {L : Layout} (x : Cslib.WordRAM.Data (regCount L))
    (d spare : Fin (regCount L)) (middle value : ℕ)
    (temporary : L.ptrRegs + L.dataRegs + 2 ≤ spare.val) :
    ScalarResult d value x (((x.set d middle).set spare 1).set d value) where
  result := by simp [Cslib.WordRAM.Data.set]
  memory := rfl
  frame r hr hd := by
    have hs : r ≠ spare := by intro eq; subst spare; omega
    simp [Cslib.WordRAM.Data.set, hd, hs]

private theorem maxSucc_spec {L : Layout} (w : ℕ) (d a b spare : Fin (regCount L))
    (x : Cslib.WordRAM.Data (regCount L)) (u v : ℕ)
    (hu : x.regs a = u) (hv : x.regs b = v) (ne : spare ≠ d)
    (temporary : L.ptrRegs + L.dataRegs + 2 ≤ spare.val)
    (fit : Cslib.WordRAM.Fits w (max u v + 1)) :
    ∃ y, ExecWithin w
      (.seq (.branch (.lt a b) (.op (.copy d b)) (.op (.copy d a)))
        (.seq (.op (.const spare 1)) (.op (.bin .add d d spare)))) x y 5 ∧
      ScalarResult d (max u v + 1) x y := by
  have copy : ExecWithin (B := .standard) w
      (.branch (.lt a b) (.op (.copy d b)) (.op (.copy d a))) x (x.set d (max u v)) 3 := by
    by_cases h : u < v
    · have cond : (Cslib.WordRAM.Cond.lt a b).Holds x := by simpa [hu, hv] using h
      simpa [hv, max_eq_right (Nat.le_of_lt h)] using
        (ExecWithin.copy (B := .standard) (w := w) (x := x) (d := d) (s := b)).branch_pos cond
          |>.mono (show 1 + 1 ≤ 3 by decide)
    · have cond : ¬(Cslib.WordRAM.Cond.lt a b).Holds x := by simpa [hu, hv] using h
      simpa [hu, max_eq_left (Nat.le_of_not_gt h)] using
        (ExecWithin.copy (B := .standard) (w := w) (x := x) (d := d) (s := a)).branch_neg cond
  have one : Cslib.WordRAM.Fits w 1 := by
    change max u v + 1 < 2 ^ w at fit
    exact lt_of_le_of_lt (by omega) fit
  let y := (x.set d (max u v)).set spare 1
  have add : ExecWithin (B := .standard) w (.op (.bin .add d d spare)) y
      (y.set d (max u v + 1)) 1 := by
    simpa [y, Cslib.WordRAM.Data.set, Ne.symm ne] using
      (ExecWithin.bin (w := w) (x := y) (f := .add) (d := d) (i := d) (j := spare)
        (by simpa [y, Cslib.WordRAM.Data.set, Ne.symm ne] using fit))
  exact ⟨_, copy.seq ((ExecWithin.const one).seq add), scratch_result x d spare _ _ temporary⟩

private theorem heavy_spec {L : Layout} (w : ℕ) (d a b spare : Fin (regCount L))
    (x : Cslib.WordRAM.Data (regCount L)) (u v : ℕ)
    (hu : x.regs a = u) (hv : x.regs b = v) (ne : spare ≠ d)
    (temporary : L.ptrRegs + L.dataRegs + 2 ≤ spare.val)
    (fit : Cslib.WordRAM.Fits w (u - v)) (width : 1 < 2 ^ w) :
    ∃ y, ExecWithin w
      (.seq (.op (.bin .sub d a b)) (.seq (.op (.const spare 1))
        (.branch (.lt spare d) (.op (.const d 1)) (.op (.const d 0))))) x y 5 ∧
      ScalarResult d (if v + 1 < u then 1 else 0) x y := by
  have sub : ExecWithin (B := .standard) w (.op (.bin .sub d a b)) x (x.set d (u - v)) 1 := by
    simpa [hu, hv] using (ExecWithin.bin (w := w) (x := x) (f := .sub) (d := d) (i := a) (j := b)
      (by simpa [hu, hv] using fit))
  let y := (x.set d (u - v)).set spare 1
  have cond : (Cslib.WordRAM.Cond.lt spare d).Holds y ↔ v + 1 < u := by
    simp [y, Cslib.WordRAM.Data.set, Ne.symm ne, Nat.lt_sub_iff_add_lt, Nat.add_comm]
  have test := select_spec w (.lt spare d) d y 1 0 width (Cslib.WordRAM.fits_zero w)
  refine ⟨y.set d (if v + 1 < u then 1 else 0), ?_, scratch_result x d spare _ _ temporary⟩
  exact sub.seq ((ExecWithin.const width).seq (by simpa only [cond] using test))

/-- Concrete standard word-RAM scalar certificate for `model`, using the identity encoding.
Every operation is admissible when its result fits. The height-gap comparison requires only
its truncated difference to fit; strict and nonstrict comparisons require no extra headroom. -/
@[expose] def scalars (L : Layout) : Scalars model L :=
  let spare := fun d : Fin (regCount L) => if d = addrReg L then valueReg L else addrReg L
  have different : ∀ d, spare d ≠ d := by
    intro d
    dsimp only [spare]
    split
    · rename_i h
      subst d
      intro eq
      have bad := congrArg Fin.val eq
      simp [valueReg, addrReg] at bad
    · rename_i h
      exact Ne.symm h
  have temporary : ∀ d, L.ptrRegs + L.dataRegs + 2 ≤ (spare d).val := by
    intro d
    dsimp only [spare]
    split <;> simp [addrReg, valueReg]
  { encode := Function.Embedding.refl _
    op := fun o d a b => match o with
      | .zero => .op (.const d 0)
      | .maxSucc =>
          .seq (.branch (.lt a b) (.op (.copy d b)) (.op (.copy d a)))
            (.seq (.op (.const (spare d) 1)) (.op (.bin .add d d (spare d))))
    test := fun p d a b => match p with
      | .lt => .branch (.lt a b) (.op (.const d 1)) (.op (.const d 0))
      | .le => .branch (.lt b a) (.op (.const d 0)) (.op (.const d 1))
      | .heavy => .seq (.op (.bin .sub d a b)) (.seq (.op (.const (spare d) 1))
          (.branch (.lt (spare d) d) (.op (.const d 1)) (.op (.const d 0))))
    opTime := fun o => match o with | .zero => 1 | .maxSucc => 5
    testTime := fun p => match p with | .lt | .le => 3 | .heavy => 5
    OpSafe := fun _ _ _ _ => True
    TestSafe := fun w p a b => match p with
      | .lt | .le => True
      | .heavy => Cslib.WordRAM.Fits w (a - b)
    op_spec := by
      intro w o d a b x u v hu hv _ fit
      cases o with
      | zero => exact ⟨_, ExecWithin.const fit, ScalarResult.set ..⟩
      | maxSucc => exact maxSucc_spec w d a b (spare d) x u v hu hv (different d) (temporary d) fit
    test_spec := by
      intro w p d a b x u v hu hv safe width
      change x.regs a = u at hu
      change x.regs b = v at hv
      cases p with
      | lt =>
        refine ⟨_, ?_, ScalarResult.set ..⟩
        simpa [Cslib.WordRAM.Cond.holds_lt, hu, hv] using
          select_spec w (.lt a b) d x 1 0 width (Cslib.WordRAM.fits_zero w)
      | le =>
        refine ⟨_, ?_, ScalarResult.set ..⟩
        have run := select_spec w (.lt b a) d x 0 1 (Cslib.WordRAM.fits_zero w) width
        by_cases h : u ≤ v
        · simpa [Cslib.WordRAM.Cond.holds_lt, hu, hv, h, not_lt.mpr h] using run
        · simpa [Cslib.WordRAM.Cond.holds_lt, hu, hv, h, lt_of_not_ge h] using run
      | heavy =>
        simpa only [model, decide_eq_true_eq] using
          heavy_spec w d a b (spare d) x u v hu hv (different d) (temporary d) safe width }

end Cslib.PointerMachine.WordRAM.Natural
