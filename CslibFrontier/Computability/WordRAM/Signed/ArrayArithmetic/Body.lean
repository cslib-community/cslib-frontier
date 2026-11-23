/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.ArrayArithmetic.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native pointwise signed array operations

Both operands are read before the output store, so exact input/output aliases are valid.
The enclosing array loop is responsible for proving that earlier stores preserve unread
input cells. The numerical premises here concern only the two original values and addresses.
-/

public section

namespace Cslib.WordRAM.Signed.ArrayArithmetic

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem exec_arithmetic {w : ℕ} (subtract : Bool) (x : Data 16) (a b : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hla : x.regs left = encode a) (hlb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) (arithmetic subtract) x y 17 ∧
      y.regs result = encode (if subtract then a - b else a + b) ∧ Frame x y := by
  cases subtract with
  | false =>
    obtain ⟨y, he, hr, hf⟩ := Signed.exec_add ha hb x hla hlb
    exact ⟨y, he.mono (by decide), hr, hf⟩
  | true => exact Signed.exec_subtract ha hb x hla hlb

/-- The arithmetic workspace, index and address are the only body modifications. -/
@[expose] def BodyLocal (i : Fin 16) : Prop :=
  i.val < 9 ∨ i = Reg.index ∨ i = Reg.address

instance (i : Fin 16) : Decidable (BodyLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.index ∨ i = Reg.address))

private theorem body_preserves (subtract : Bool) (i : Fin 16) :
    ¬BodyLocal i → (body subtract).Preserves i := by
  cases subtract <;> decide +kernel +revert

/-- One complete pointwise operation costs at most twenty-four native instructions. -/
theorem exec_body {w : ℕ} (subtract : Bool) (x : Data 16) (a b : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hA : x.mem (x.regs Reg.inputA + x.regs Reg.index) = encode a)
    (hB : x.mem (x.regs Reg.inputB + x.regs Reg.index) = encode b)
    (haddrA : Fits (w + 2) (x.regs Reg.inputA + x.regs Reg.index))
    (haddrB : Fits (w + 2) (x.regs Reg.inputB + x.regs Reg.index))
    (haddrOut : Fits (w + 2) (x.regs Reg.output + x.regs Reg.index))
    (hnext : Fits (w + 2) (x.regs Reg.index + 1)) (hone : x.regs Reg.one = 1) :
    ∃ y, ExecWithin (w + 2) (body subtract) x y 24 ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧
      y.mem = Function.update x.mem (x.regs Reg.output + x.regs Reg.index)
        (encode (if subtract then a - b else a + b)) ∧
      ∀ i, ¬BodyLocal i → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin (w + 2) (body subtract) x y 24 ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧
      y.mem = Function.update x.mem (x.regs Reg.output + x.regs Reg.index)
        (encode (if subtract then a - b else a + b)) := by
    unfold body load finish
    generalize harith : arithmetic subtract = sub
    wram_exec [hA, hB]
    subst harith
    wram_call (exec_arithmetic subtract _ a b ha hb (by wram_simp) (by wram_simp))
      with t ⟨htres, htm, htf⟩
    have hti : t.regs Reg.index = x.regs Reg.index :=
      (htf _ (.inr (by decide))).trans (by wram_simp)
    have hto : t.regs Reg.output = x.regs Reg.output :=
      (htf _ (.inr (by decide))).trans (by wram_simp)
    have ht1 : t.regs Reg.one = 1 := (htf _ (.inr (by decide))).trans (by wram_simp [hone])
    wram_exec [hti, hto, ht1, htres]
    wram_simp [hti, hto, htm]
  obtain ⟨y, he, hyi, hym⟩ := hrun
  exact ⟨y, he, hyi, hym, fun i hi => he.regs_eq (body_preserves subtract i hi)⟩

end Cslib.WordRAM.Signed.ArrayArithmetic
