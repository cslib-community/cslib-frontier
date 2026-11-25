/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Core
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Return
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Complete native callable queried-product execution

The caller supplies original zero/one matrices and coordinate occurrences in a local original
input block. The product computes its own tables, layouts, groups, encoded bands, epochs and
answers. Every source memory access is translated to actual base addition and load/store code;
dirty words are normalized without bulk clearing. The final answer pointer is absolute.

This is the callable product prerequisite for an ET-record adapter, not that adapter, an
Exact Triangle solver or the complete ordinary-3SUM bound under #1394.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete charge includes two linear span normalizations and the computed setup. -/
@[expose] def timeBound {m N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  coreTime (m := m) qs + 7 * QueriedProduct.inputEnd m N qs.length + 7 * qs.length + 14

private theorem spans_le_budget (L m N Q : ℕ) :
    QueriedProduct.inputEnd m N Q ≤ QueriedProduct.outputBase L m N Q ∧
      QueriedProduct.inputEnd m N Q + QueriedProduct.outputBase L m N Q + Q + 2 ≤
        QueriedProduct.wordBudget L m N Q := by
  have hsep : QueriedProduct.inputEnd m N Q ≤ QueriedProduct.outputBase L m N Q := by
    unfold QueriedProduct.outputBase QueriedProduct.groupedBase QueriedProduct.originalBase
      QueriedProduct.codeBase QueriedProduct.offsetBase QueriedProduct.snapshotBase
    omega
  have hend : QueriedProduct.outputBase L m N Q + Q ≤ QueriedProduct.memoryEnd L m N Q := by
    unfold QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
    have := Nat.zero_le (2 * (L + 1) * 10 ^ L)
    have := Nat.zero_le (10 ^ L)
    omega
  refine ⟨hsep, ?_⟩
  unfold QueriedProduct.wordBudget
  omega

/-- Caller-safe actual native product execution, for zero/one matrices with `D m ^ 18 ≤ N`, at
depth `19 * m`. The only local memory premise is the original input block; all remaining target
memory may be dirty. Every original occurrence is answered exactly, original input words are
restored exactly, and the caller memory outside the window is preserved. The numerical width
hypothesis is derived from original dimensions and base. -/
theorem exec {W b m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 163) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length →
      x.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W program x y (timeBound (m := m) qs) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (19 * m) m N qs.length ∧
      y.regs Reg.base = b ∧ y.regs Reg.modulus = windowSize N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length → y.mem (b + a) = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  obtain ⟨hsep, hspan⟩ := spans_le_budget (19 * m) m N qs.length
  have hbound : QueriedProduct.inputEnd m N qs.length +
      QueriedProduct.outputBase (19 * m) m N qs.length + qs.length + 2 <
        windowSize N qs.length := hspan.trans_lt (source_admission (Q := qs.length) hN).2.2
  have hM : 0 < windowSize N qs.length := Nat.two_pow_pos _
  obtain ⟨c, hc, cb, cM, cI, cQ, cO, cv, ci, cf⟩ := exec_core X Y qs x hb hinput hX hY hN hfit
  obtain ⟨s, hs, sm, sr⟩ := exec_restoreInput c cb cI cM hM (hfit.of_le (by omega))
  have sb : s.regs Reg.base = b := by regs_frame
  have sM : s.regs Reg.modulus = windowSize N qs.length := by regs_frame
  have sQ : s.regs Reg.queryCount = qs.length := by regs_frame
  have sO : s.regs Reg.output = QueriedProduct.outputBase (19 * m) m N qs.length := by regs_frame
  obtain ⟨y, hy, ym, yr, yf⟩ := exec_returnOutput s sb sO sQ sM hM (hfit.of_le (by omega))
  refine ⟨y, (hc.seq (hs.seq hy)).mono (by dsimp only [timeBound]; omega), yr, ?_, ?_,
    fun i => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · regs_frame
  · regs_frame
  · rw [ym, ← Nat.add_assoc,
      ArrayNormalize.normalizePrefix_read _ _ _ _ _ i.isLt, sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    simpa only [Nat.add_assoc] using cv i
  · rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_read _ _ _ _ _ ha]
    exact ci a ha
  · rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    exact cf a ha

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
