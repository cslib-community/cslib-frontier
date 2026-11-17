/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Register facts across calls

Regressions for `regs_frame`: a value is carried across calls by frames stated as hypotheses, with
premises that exclude registers, bound their index or are hypotheses themselves, and by the frame
of an execution, the registers its code does not write; reads after `Data.set` and of a state
introduced by `let` reduce; values come from the fields of a bundle or the components of a
conjunction, and a bundle or a conjunction is proved field by field; a value left open is
inferred; the frame of two calls follows from their frames. A read that cannot be followed to the
stated value fails with the equation that is left and the premise that does not hold.
-/

namespace CslibFrontierTests.WordRAMRegsFrame

open Cslib.WordRAM

/-- Register names for the examples. -/
abbrev a : Fin 4 := 0
/-- Register names for the examples. -/
abbrev b : Fin 4 := 1
/-- Register names for the examples. -/
abbrev c : Fin 4 := 2
/-- Register names for the examples. -/
abbrev d : Fin 4 := 3

/-! ## Frames among the hypotheses -/

/-- A value carried across two calls. Neither the frames nor the value are named. -/
example (x y z : Data 4) (n : ℕ) (hx : x.regs a = n)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) (zf : ∀ i, i ≠ c → i ≠ d → z.regs i = y.regs i) :
    z.regs a = n := by
  regs_frame

/-- A frame whose premise bounds the index of the register. -/
example (x y : Data 4) (n : ℕ) (hx : x.regs d = n)
    (yf : ∀ i : Fin 4, 2 ≤ i.val → y.regs i = x.regs i) : y.regs d = n := by
  regs_frame

/-- A premise about a register that is a variable is a hypothesis. -/
example (x y : Data 4) (n : ℕ) (r : Fin 4) (hr : r ≠ b) (hx : x.regs r = n)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) : y.regs r = n := by
  regs_frame

/-- An equation between the registers of two states, and a fact about a single register that
relates two states. -/
example (x y z : Data 4) (yb : y.regs b = x.regs b)
    (zf : ∀ i, i ≠ c → z.regs i = y.regs i) : z.regs b = x.regs b := by
  regs_frame

/-- The frame of two calls follows from their frames. -/
example (x y z : Data 4) (yf : ∀ i, i ≠ b → y.regs i = x.regs i)
    (zf : ∀ i, i ≠ c → z.regs i = y.regs i) : ∀ i, i ≠ b → i ≠ c → z.regs i = x.regs i := by
  regs_frame

/-! ## Writes and executions -/

/-- Reads after `Data.set`, of a state introduced by `let`. -/
example (x : Data 4) (n : ℕ) (hx : x.regs a = n) :
    let y := (x.set b 1).set c 2
    y.regs a = n ∧ y.regs b = 1 := by
  regs_frame

/-- A program that writes `b` and `c`. -/
def bump : Code .standard 4 := ram[ b ← #5; c ← b + c ]

/-- An execution is a frame of the registers its code does not write. -/
example (w : ℕ) (x y z : Data 4) (n : ℕ) (hx : x.regs a = n) (he : ExecWithin w bump x y 2)
    (he' : Exec w bump y z 1) : z.regs a = n := by
  regs_frame

/-! ## Bundles -/

/-- The registers a callee reads. -/
structure Params (n m : ℕ) (x : Data 4) : Prop where
  /-- The first parameter. -/
  first : x.regs a = n
  /-- The last parameter. -/
  last : x.regs d = m

/-- The values are fields of a bundle, and the goal is a bundle. -/
example (w : ℕ) (x y : Data 4) (n m : ℕ) (hx : Params n m x) (he : ExecWithin w bump x y 2) :
    Params n m y := by
  regs_frame

/-- The values are the components of a conjunction. -/
example (x y : Data 4) (n m : ℕ) (hx : x.regs a = n ∧ x.regs d = m)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) : y.regs a = n ∧ y.regs d = m := by
  regs_frame

/-- A specification whose argument `n` is determined by the fact it is given. -/
theorem exists_succ (x : Data 4) {n : ℕ} (_ : x.regs a = n) : ∃ y : Data 4, y.regs a = n + 1 :=
  ⟨x.set a (n + 1), by simp⟩

/-- The value the callee is told is inferred. -/
example (x y : Data 4) (m : ℕ) (hx : x.regs a = m) (yf : ∀ i, i ≠ b → y.regs i = x.regs i) :
    ∃ z : Data 4, z.regs a = m + 1 := by
  obtain ⟨z, hz⟩ := exists_succ y (by regs_frame)
  exact ⟨z, hz⟩

/-! ## Failures -/

/-- error: regs_frame: could not prove
  z.regs b = n
Following the frames leaves
  y.regs b = n
`yf` does not give `y.regs b`: it needs
  b ≠ b -/
#guard_msgs (whitespace := lax) in
example (x y z : Data 4) (n : ℕ) (hx : x.regs b = n)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) (zf : ∀ i, i ≠ c → i ≠ d → z.regs i = y.regs i) :
    z.regs b = n := by
  regs_frame

/-- error: regs_frame: could not prove
  y.regs b = n
`he.regs_eq` does not give `y.regs b`: it needs
  Code.Preserves b bump -/
#guard_msgs (whitespace := lax) in
example (w : ℕ) (x y : Data 4) (n : ℕ) (hx : x.regs b = n) (he : ExecWithin w bump x y 2) :
    y.regs b = n := by
  regs_frame

/-- error: regs_frame: could not prove
  y.regs a = m
Following the frames leaves
  n = m -/
#guard_msgs (whitespace := lax) in
example (x y : Data 4) (n m : ℕ) (hx : x.regs a = n)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) : y.regs a = m := by
  regs_frame

/-- error: regs_frame: could not prove
  y.regs a = n
No hypothesis gives `y.regs a` or a frame of its state. -/
#guard_msgs (whitespace := lax) in
example (x y : Data 4) (n : ℕ) (hx : x.regs a = n) : y.regs a = n := by
  regs_frame

/-- error: regs_frame: could not prove
  y.regs d = m
Following the frames leaves
  x.regs d = m
No hypothesis gives `x.regs d` or a frame of its state. -/
#guard_msgs (whitespace := lax) in
example (x y : Data 4) (n m : ℕ) (hx : x.regs a = n)
    (yf : ∀ i, i ≠ b → y.regs i = x.regs i) : y.regs a = n ∧ y.regs d = m := by
  regs_frame

end CslibFrontierTests.WordRAMRegsFrame
