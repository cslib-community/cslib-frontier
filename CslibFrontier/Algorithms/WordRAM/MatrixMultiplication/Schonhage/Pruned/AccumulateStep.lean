/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Add
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanStep
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual native selection and accumulation of one query

## Main results

* `PrunedQuery.exec_accumulateDispatch`: the real digit comparisons select a child's addition.
* `PrunedQuery.exec_accumulateStep`: include the source indexing, load, digit and counter work.

The child-value memory premise is needed only for selected queries. Unselected child-directory
cells may contain arbitrary prior values and are never loaded by the program.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Registers changed by selected signed accumulation or its unselected no-op. -/
def AccumulateDispatchLocal (i : Fin registers) : Prop := AddValueLocal i ∨ i = temporary

instance (i : Fin registers) : Decidable (AccumulateDispatchLocal i) :=
  inferInstanceAs (Decidable (AddValueLocal i ∨ i = temporary))

/-- Exactly the contributing parent queries load and add a child value. Selection is proved
from the actual comparisons with digit nine and the current term register. -/
theorem exec_accumulateDispatch {w : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers) (q : ℕ) (hq : x.regs query = q) (hd : x.regs digit = q % 10)
    (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hleft : selected true (x.regs term) q → x.mem (x.regs valueBase + q) = encode a)
    (hright : selected true (x.regs term) q →
      x.mem (x.regs childValues + q / 10) = encode b)
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10)) :
    ∃ y, ExecWithin (w + 2) accumulateDispatch x y 25 ∧
      y.mem = (if selected true (x.regs term) q then
        Function.update x.mem (x.regs valueBase + q) (encode (a + b)) else x.mem) ∧
      (∀ i, ¬AccumulateDispatchLocal i → y.regs i = x.regs i) := by
  by_cases hsel : selected true (x.regs term) q
  · obtain ⟨y, hy, hmem, hyr⟩ := exec_addValue ha hb x q hq h10 (hleft hsel) (hright hsel) hp hc
    exact ⟨y, (exec_selectDigit hd h9 hsel hy).mono (by decide),
      by simpa only [hsel, ↓reduceIte] using hmem, fun i hi => hyr i (fun h => hi (Or.inl h))⟩
  · exact ⟨x.set temporary (x.regs temporary),
      (exec_selectDigit_skip hd h9 hsel).mono (by decide), by simp [hsel],
      fun i _ => by simp only [Data.set_regs, Function.update_eq_self]⟩

/-- Registers changed by loading, dispatching and advancing one parent query. -/
def AccumulateStepLocal (i : Fin registers) : Prop :=
  AccumulateDispatchLocal i ∨ i = query ∨ i = digit ∨ i = index

instance (i : Fin registers) : Decidable (AccumulateStepLocal i) :=
  inferInstanceAs (Decidable
    (AccumulateDispatchLocal i ∨ i = query ∨ i = digit ∨ i = index))

/-- One complete native parent-query iteration, including every index/digit/control operation.
The conditional memory hypotheses reflect only which child words are actually requested. -/
theorem exec_accumulateStep {w : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h1 : x.regs one = 1) (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hleft : selected true (x.regs term) q → x.mem (x.regs valueBase + q) = encode a)
    (hright : selected true (x.regs term) q →
      x.mem (x.regs childValues + q / 10) = encode b)
    (h10fit : Fits (w + 2) 10)
    (hr : Fits (w + 2) (x.regs listBase + x.regs index))
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10))
    (hi : Fits (w + 2) (x.regs index + 1)) :
    ∃ y, ExecWithin (w + 2) accumulateStep x y 29 ∧ y.regs index = x.regs index + 1 ∧
      y.mem = (if selected true (x.regs term) q then
        Function.update x.mem (x.regs valueBase + q) (encode (a + b)) else x.mem) ∧
      (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i) := by
  have hmod : Fits (w + 2) (q % 10) :=
    h10fit.of_le (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  refine WP.exists_execWithin ?_
  wram_exec [accumulateStep, scanLoad, hq, h10, hr, hmod]
  wram_call (exec_accumulateDispatch ha hb _ q (by wram_simp) (by wram_simp)
    (by wram_simp [h9]) (by wram_simp [h10]) (by wram_simp; exact hleft)
    (by wram_simp; exact hright) (by wram_simp; exact hp) (by wram_simp; exact hc))
    with u ⟨hm, hf⟩
  wram_simp at hm
  wram_exec * [hi]
  refine ⟨by wram_simp, hm, fun i h => ?_⟩
  simp only [AccumulateStepLocal, not_or] at h
  rcases h with ⟨hd, hq', hdig, hind⟩
  wram_simp
  rw [hf i hd]
  simp only [AccumulateDispatchLocal, AddValueLocal, not_or] at hd
  rcases hd with ⟨⟨-, had, -⟩, -⟩
  wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
