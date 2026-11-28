/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Comparing encoded signed words

The low bits distinguish opposite signs. Within one sign, the encoded unsigned comparison
has the usual order for nonnegative integers and the reverse order for negative integers.
No signed comparison is added to the target machine.

## Main definitions

* `Signed.less`: an unsigned instruction block comparing the encoded input registers.

## Main results

* `Signed.exec_less`: comparison in at most eleven instructions, with the arithmetic frame.

## References

The instruction block is an original implementation using the sign-and-magnitude encoding.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

variable {r : ℕ}

/-- Compare two encoded signed integers, returning zero or one in `result`. -/
def less : Code .standard (r + 9) := ram[
  two ← #2; zero ← #0; signA ← left % two; signB ← right % two;
  if signA = signB then [
    if signA = zero then [
      if left < right then [ result ← #1 ] else [ result ← #0 ] ]
    else [ if right < left then [ result ← #1 ] else [ result ← #0 ] ] ]
  else [ result ← signA ] ]

private theorem lt_encoded (a b : ℤ) :
    (if (if a < 0 then 1 else 0 : ℕ) = (if b < 0 then 1 else 0) then
      if a < 0 then encode b < encode a else encode a < encode b
    else a < 0) ↔ a < b := by
  have ha := decode_encode a
  have hb := decode_encode b
  simp only [decode, encode_mod_two, encode_div_two] at ha hb
  by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;>
    simp only [encode, hna, hnb, ↓reduceIte, Nat.reduceEqDiff] at ha hb ⊢ <;>
    constructor <;> intro h <;> first | trivial | omega

/-- Signed comparison costs at most eleven unsigned instructions. The input encodings may
be used at any physical width admitting the constant two; the frame preserves the operands. -/
theorem exec_less {w : ℕ} (h2 : Fits w 2) (x : Data (r + 9)) {a b : ℤ}
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin w less x y 11 ∧
      y.regs result = (if a < b then 1 else 0) ∧ Frame x y := by
  have hcmp := lt_encoded a b
  have : Fits w (if a < 0 then 1 else 0) := by split_ifs <;> fits
  have : Fits w (if b < 0 then 1 else 0) := by split_ifs <;> fits
  have hrun : ∃ y, ExecWithin w less x y 11 ∧
      y.regs result = (if a < b then 1 else 0) ∧ y.mem = x.mem := by
    unfold less
    wram_exec [hxa, hxb, encode_mod_two] <;> wram_simp <;>
      split_ifs at * <;> first | rfl | omega
  obtain ⟨y, he, hyr, hym⟩ := hrun
  refine ⟨y, he, hyr, hym, fun i hi => he.regs_eq ?_⟩
  simp only [less, Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq,
    result, two, zero, signA, signB, Fin.ext_iff]
  omega

end Cslib.WordRAM.Signed
