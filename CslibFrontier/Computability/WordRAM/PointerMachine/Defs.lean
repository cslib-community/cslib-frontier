/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-!
# Scalar basis for pointer simulation of the standard word RAM

The source machine's words, including numerical memory addresses, are scalar values. Its
arithmetic operations act on those scalars. The simulator's own heap addresses remain opaque
pointers: no scalar operation receives or produces a pointer. AVL navigation resolves numerical
memory addresses to heap nodes.

The word-width operation is interpreted at the source width. Scalar overflow is immaterial to
the forward simulation of successful source executions; no fault correspondence is claimed.
-/

public section
namespace Cslib.WordRAM.PointerMachine

/-- Standard word operations together with constants and the AVL height operation. -/
inductive Operation where
  /-- A program constant, independent of both arguments. -/
  | constant (value : ℕ)
  /-- A standard binary word-RAM operation on scalar words. -/
  | bin (operation : BinOp)
  /-- Read the source word width. -/
  | width
  /-- The AVL height operation. -/
  | maxSucc

/-- Scalar comparisons used by the source and by the AVL dictionary. -/
inductive Test where
  /-- Equality of scalar words. -/
  | eq
  /-- Strict scalar order. -/
  | lt
  /-- Nonstrict scalar order, used by balancing. -/
  | le
  /-- The first height exceeds the second by at least two. -/
  | heavy

/-- Natural words and heights, with precisely the source arithmetic and AVL scalar operations.
The width affects only the width-reading primitive, not pointer interpretation. -/
abbrev model (w : ℕ) : Cslib.PointerMachine.Model where
  Value := ℕ
  undefined := 0
  Op := Operation
  Test := Test
  evalOp
    | .constant n, _, _ => n
    | .bin f, a, b => f.eval a b
    | .width, _, _ => w
    | .maxSucc, a, b => max a b + 1
  evalTest
    | .eq, a, b => decide (a = b)
    | .lt, a, b => decide (a < b)
    | .le, a, b => decide (a ≤ b)
    | .heavy, a, b => decide (b + 1 < a)

/-- Seven navigation registers, four scalar scratch registers, then the source register bank.
Records contain left/right/parent links and key/height/value scalar fields. -/
abbrev layout (r : ℕ) : Cslib.PointerMachine.Layout :=
  Cslib.DataStructure.SearchTree.PointerMachine.layout 2 (r + 2)

/-- Place source registers after query, two AVL temporaries, and dictionary value scratch. -/
@[expose] def register {r : ℕ} (i : Fin r) : Fin (layout r).dataRegs :=
  ⟨i.val + 4, by simp [Nat.add_assoc]⟩

/-- Source registers never alias any dictionary scalar scratch register. -/
theorem register_ge_four {r : ℕ} (i : Fin r) : 4 ≤ (register i).val := by
  simp [register]

/-- Source register names do not alias the four scalar scratch registers. -/
theorem register_ne_scratch {r : ℕ} (i : Fin r) (j : ℕ) (hj : j < 4) :
    register i ≠ Fin.ofNat (layout r).dataRegs j := by
  intro h
  have ge := register_ge_four i
  have eq := congrArg Fin.val h
  change (register i).val = j % (r + 2 + 2) at eq
  rw [Nat.mod_eq_of_lt (by omega)] at eq
  omega

/-- The register placement preserves distinct source registers. -/
theorem register_injective {r : ℕ} : Function.Injective (@register r) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa only [register, Nat.add_right_cancel_iff] using this

end Cslib.WordRAM.PointerMachine
