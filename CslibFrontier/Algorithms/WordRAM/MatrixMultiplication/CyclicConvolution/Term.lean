/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Program
public import CslibFrontier.Foundations.RingTheory.CyclicIntRing.Coefficients
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native cyclic-coefficient multiplication and accumulation

These are internal execution APIs for the coefficient loop. Each term computes its cyclic
index, loads the actual operands, calls the native signed multiply and add blocks, and advances
the summation counter. Source-width premises for the operands and partial sum will be derived
from coefficient magnitude bounds by the enclosing loop; no arithmetic result is supplied
as an input to the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.CyclicIntRing (subIndex)

/-- The actual wrap comparison and both unsigned subtractions take at most three instructions. -/
theorem exec_selectPartner {w : ℕ} (x : Data 32)
    (hfit : Fits w (x.regs Reg.coefficient + x.regs Reg.length)) :
    ExecWithin w selectPartner x
      (x.set Reg.partner (subIndex (x.regs Reg.length)
        (x.regs Reg.coefficient) (x.regs Reg.index))) 3 := by
  unfold selectPartner subIndex
  wram_exec
  all_goals
    simp only [show x.regs Reg.index ≤ x.regs Reg.coefficient ↔
      ¬x.regs Reg.coefficient < x.regs Reg.index by omega, hc, not_true_eq_false,
      not_false_eq_true, ↓reduceIte, Data.set, Function.update_idem]

/-- Exactly the arithmetic scratch, cyclic partner, partial sum, address and inner counter. -/
def TermLocal (i : Fin 32) : Prop :=
  i.val < 9 ∨ i = Reg.partner ∨ i = Reg.accumulator ∨ i = Reg.address ∨ i = Reg.index

instance (i : Fin 32) : Decidable (TermLocal i) :=
  inferInstanceAs (Decidable
    (i.val < 9 ∨ i = Reg.partner ∨ i = Reg.accumulator ∨ i = Reg.address ∨ i = Reg.index))

private theorem term_preserves (i : Fin 32) :
    ¬TermLocal i → term.Preserves i := by decide +kernel +revert

/-- All index work, two loads, signed multiply/add and counter work take forty native
instructions. The memory is unchanged and every parameter register is preserved. -/
theorem exec_term {w : ℕ} (x : Data 32) (a b s : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hp : GenericRAM.Signed.Fits w (a * b)) (hs : GenericRAM.Signed.Fits w s)
    (hwrap : Fits (w + 2) (x.regs Reg.coefficient + x.regs Reg.length))
    (haddrA : Fits (w + 2) (x.regs Reg.inputA + x.regs Reg.index))
    (haddrB : Fits (w + 2) (x.regs Reg.inputB +
      subIndex (x.regs Reg.length) (x.regs Reg.coefficient) (x.regs Reg.index)))
    (hnext : Fits (w + 2) (x.regs Reg.index + 1))
    (hreadA : x.mem (x.regs Reg.inputA + x.regs Reg.index) = encode a)
    (hreadB : x.mem (x.regs Reg.inputB +
      subIndex (x.regs Reg.length) (x.regs Reg.coefficient) (x.regs Reg.index)) = encode b)
    (hacc : x.regs Reg.accumulator = encode s) (hone : x.regs Reg.one = 1) :
    ∃ y, ExecWithin (w + 2) term x y 40 ∧
      y.regs Reg.accumulator = encode (s + a * b) ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧ y.mem = x.mem ∧
      ∀ i, ¬TermLocal i → y.regs i = x.regs i := by
  suffices ∃ y, ExecWithin (w + 2) term x y 40 ∧
      y.regs Reg.accumulator = encode (s + a * b) ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧ y.mem = x.mem by
    obtain ⟨y, hall, hacc', hidx', hmem'⟩ := this
    exact ⟨y, hall, hacc', hidx', hmem', fun i hi => hall.regs_eq (term_preserves i hi)⟩
  apply WP.exists_execWithin
  unfold term productTerm loadOperands addArguments finishTerm
  wram_call (exec_selectPartner x hwrap)
  wram_exec * [hreadA, hreadB]
  wram_call (Signed.exec_multiply (r := 23) ha hb hp _ (by wram_simp) (by wram_simp))
    with v ⟨hvresult, hvmem, _⟩
  have hvres : v.regs Signed.result = encode (a * b) := hvresult
  wram_exec *
  wram_call (Signed.exec_add (r := 23) hs hp _ (by wram_simp) (by wram_simp))
    with t ⟨htresult, htmem, _⟩
  have htres : t.regs Signed.result = encode (s + a * b) := htresult
  wram_exec *
  wram_simp * [htmem, hvmem]

end Cslib.Algorithms.WordRAM.CyclicConvolution
