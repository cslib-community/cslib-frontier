/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Forms
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# A native mixed-radix encoding cell

## Main results

* `Encoding.exec_cell`: charged index arithmetic, coefficient dispatch, signed linear form,
  output store and counter increment for one cell of a shared coordinate transform.

## References

The linear forms are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The registers modified by a cell, apart from the nine signed-arithmetic scratch registers. -/
def CellLocal (i : Fin 32) : Prop :=
  i = cell ∨ i = block ∨ i = term ∨ i = suffix ∨ i = address ∨
    i = accumulator ∨ i = group ∨ i = temporary

instance (i : Fin 32) : Decidable (CellLocal i) :=
  inferInstanceAs (Decidable (i = cell ∨ i = block ∨ i = term ∨ i = suffix ∨
    i = address ∨ i = accumulator ∨ i = group ∨ i = temporary))

/-- One output entry, with all index arithmetic and the counter increment charged. A single
ordinary explicit natural-number bound covers the addresses and index products; no fit
condition is imposed on an unspecified intermediate machine state. -/
theorem exec_cell {w : ℕ} (hw : 0 < w) (side : Bool) (x : Data 32)
    (P n s d i : ℕ) (hP : 0 < P) (hnpos : 0 < n) (hi : i < 10 * P * n)
    (hsrc : x.regs src = s) (hdst : x.regs dst = d) (hcell : x.regs cell = i)
    (hn : x.regs stride = n) (hseven : x.regs seven = 7)
    (hten : x.regs ten = 10) (hone : x.regs one = 1)
    (v : Fin 7 → ℤ) (B : ℤ) (hB : 0 ≤ B) (hv : ∀ a, |v a| ≤ B)
    (hmem : ∀ a, x.mem (s + (i / (10 * n) * 7 + a.val) * n + i % n) = encode (v a))
    (hval : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (s + d + 64 + 64 * P * n)) :
    ∃ y, ExecWithin (w + 2) (cellBody side) x y 205 ∧
      y.mem = Function.update x.mem (d + i)
        (encode (∑ a, coefficients side ⟨i / n % 10, Nat.mod_lt _ (by decide)⟩ a * v a)) ∧
      y.regs cell = i + 1 ∧
      (∀ a, 9 ≤ a.val → ¬CellLocal a → y.regs a = x.regs a) := by
  let p := i / (10 * n)
  let t : Fin 10 := ⟨i / n % 10, Nat.mod_lt _ (by decide)⟩
  let r := i % n
  -- Keep nonlinear arithmetic focused on index bounds, rather than the execution context.
  have hp : p < P :=
    (Nat.div_lt_iff_lt_mul (by positivity : 0 < 10 * n)).mpr (by nlinarith only [hi])
  have hr : r < n := Nat.mod_lt _ hnpos
  have hPn : n ≤ P * n := Nat.le_mul_of_pos_left n hP
  have hmul : p * n < P * n := Nat.mul_lt_mul_of_pos_right hp hnpos
  have h10n : Fits (w + 2) (10 * n) := haddr.of_le (by nlinarith only [hPn])
  have hpfit : Fits (w + 2) p := haddr.of_le (by nlinarith only [hp, hnpos])
  have hdiv : i / n ≤ i := Nat.div_le_self _ _
  have hdivfit : Fits (w + 2) (i / n) := haddr.of_le (by nlinarith only [hdiv, hi])
  have htfit : Fits (w + 2) t.val := haddr.of_le (by have := t.isLt; omega)
  have hrfit : Fits (w + 2) r := haddr.of_le (by nlinarith only [hr, hPn])
  have hp7 : Fits (w + 2) (p * 7) := haddr.of_le (by nlinarith only [hp, hnpos])
  have hp7n : Fits (w + 2) (p * 7 * n) := haddr.of_le (by nlinarith only [hmul])
  have hp7nr : Fits (w + 2) (p * 7 * n + r) := haddr.of_le (by nlinarith only [hmul, hr, hPn])
  have hgroup : Fits (w + 2) (s + (p * 7 * n + r)) :=
    haddr.of_le (by nlinarith only [hmul, hr, hPn])
  have hzmem (a : Fin 7) : x.mem (s + (p * 7 * n + r) + a.val * n) = encode (v a) := by
    simpa only [show s + (p * 7 * n + r) + a.val * n = s + (p * 7 + a.val) * n + r by ring] using
      hmem a
  have hspan : Fits (w + 2) (s + (p * 7 * n + r) + 7 * n) :=
    haddr.of_le (by nlinarith only [hmul, hr, hPn])
  have hdfit : Fits (w + 2) (d + i) := haddr.of_le (by nlinarith only [hi])
  have hinc : Fits (w + 2) (i + 1) := haddr.of_le (by nlinarith only [hi])
  refine WP.exists_execWithin ?_
  unfold cellBody cellSetup cellFinish
  wram_exec [hsrc, hcell, hn, hseven, hten, h10n, hpfit, hdivfit, htfit, hrfit, hp7, hp7n,
    hp7nr, hgroup]
  wram_call (exec_dispatch hw side (List.finRange 10) t (List.mem_finRange _) _ B
    (s + (p * 7 * n + r)) n v (by wram_simp; rfl)
    (by wram_simp; rfl) (by wram_simp [hn]) hzmem
    hB hv hval hspan (haddr.of_le (by omega))) with u ⟨huacc, humem, hureg⟩
  wram_exec * [hdfit, hinc, huacc]
  refine ⟨?_, by wram_simp, fun a ha hl => ?_⟩
  · wram_simp
    rw [humem]; rfl
  · simp only [CellLocal, not_or] at hl
    rcases hl with ⟨hc, hb, ht', hs, had, hac, hg, htmp⟩
    wram_simp
    rw [hureg a ha had hac htmp]; wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
