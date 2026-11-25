/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Setup

/-!
# Actual translated queried-product execution

The execution is derived from original zero/one matrices and request occurrences. The source
register bank and dirty source scratch are normalized by actual setup and translated loads.
No execution, routing, layout or cost certificate is a premise. These stage lemmas are internal
implementation APIs; exact physical answer/input words are normalized by the final spans.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Internal stage charge, before the two final span normalizations. -/
@[expose] def coreTime {m N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  517 * Nat.clog 2 (N + qs.length + 3) + 184 +
    3 * QueriedProduct.timeBound (show m ≤ 19 * m by omega) qs

/-- Source admission follows from the original thin geometry and zero/one entry bound. -/
theorem source_admission {m N Q : ℕ} (hN : D m ^ 18 ≤ N) :
    0 < sourceWidth N Q - 2 ∧
      QueriedProduct.magnitudeBound (19 * m) 1 < 2 ^ ((sourceWidth N Q - 2) - 1) ∧
      Fits (sourceWidth N Q) (QueriedProduct.wordBudget (19 * m) m N Q) :=
  QueriedProduct.admission_bounds (QueriedProduct.thin_admissionWidth_le m N Q 1 hN)

/-- Original words initialize an actual callable native product prefix, even with arbitrary
dirty target memory in the reserved window. Answers here are clipped physical words; the
subsequent real normalization makes them exact. Original duplicate requests retain their order. -/
theorem exec_core {W b m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 163) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length →
      x.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W core x y (coreTime (m := m) qs) ∧
      y.regs Reg.base = b ∧ y.regs Reg.modulus = windowSize N qs.length ∧
      y.regs Reg.inputSize = QueriedProduct.inputEnd m N qs.length ∧
      y.regs Reg.queryCount = qs.length ∧
      y.regs Reg.output = QueriedProduct.outputBase (19 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) %
            windowSize N qs.length = Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length →
        y.mem (b + a) % windowSize N qs.length = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  have hXabs (i k) : |X i k| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hX i k).1]; exact (hX i k).2
  have hYabs (k j) : |Y k j| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hY k j).1]; exact (hY k j).2
  have hbits : true = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j) :=
    fun _ => ⟨fun i k => (hX i k).1, fun k j => (hY k j).1⟩
  obtain ⟨hw, hmag, hbudget⟩ := source_admission (Q := qs.length) hN
  have htwo : sourceWidth N qs.length - 2 + 2 = sourceWidth N qs.length := by omega
  have hbudget' : Fits (sourceWidth N qs.length - 2 + 2)
      (QueriedProduct.wordBudget (19 * m) m N qs.length) := by simpa only [htwo] using hbudget
  have hi : InputFits (sourceWidth N qs.length) (QueriedProduct.input true (19 * m) X Y qs) := by
    simpa only [htwo] using
      QueriedProduct.input_fits hw (show m ≤ 19 * m by omega) true X Y qs hXabs hYabs hmag hbudget'
  have hrow : x.mem (b + 3) = N := by
    rw [hinput 3 (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hcount : x.mem (b + 4) = qs.length := by
    rw [hinput 4 (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  obtain ⟨s, hs, smem, smatch, sbound⟩ := exec_setup x hb hrow hcount hfit
  have vinput := MemoryWindow.view_mem_init_of_inputFits (r₀ := 160) hi s
    fun a ha => (congrFun smem (b + a)).trans (hinput a ha)
  obtain ⟨p, hp, pp, pv, pf⟩ := QueriedProduct.exec hw (show m ≤ 19 * m by omega)
    true X Y qs _ (fun a _ ha => vinput a ha) hXabs hYabs hbits hmag hbudget'
  have hp' : ExecWithin (sourceWidth N qs.length) (QueriedProduct.program true)
      (MemoryWindow.view (sourceWidth N qs.length) b s) p
      (QueriedProduct.timeBound (show m ≤ 19 * m by omega) qs) := by
    simpa only [htwo] using hp
  obtain ⟨-, hw_le, hwindow, -, -, -⟩ :=
    MemoryWindow.dynamicWidth_fits (b := b) (widthCoeff := 128) (S := N + qs.length + 3)
      (by decide) (by omega) (hfit.of_le (Nat.le_add_right _ 1024))
  obtain ⟨y, hy, ymatch, yframe⟩ := MemoryWindow.execWithin hp'
    (QueriedProduct.not_readsWidth true) sbound smatch hw_le hwindow
  refine ⟨y, hs.seq hy, ymatch.base_eq, ymatch.modulus_eq,
    (ymatch.regs _).trans pp.inputSize, (ymatch.regs _).trans pp.queryCount,
    (ymatch.regs _).trans pp.output, fun i => (ymatch.mem _).trans (pv i),
    fun a ha => (ymatch.mem a).trans ((pf a (by omega)).trans
      ((vinput a ha).trans (hinput a ha).symm)),
    fun a ha => (yframe a ha).trans (congrFun smem a)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
