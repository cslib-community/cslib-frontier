/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Header
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Three charged original-input copies

The left and right raw matrices and every interleaved query occurrence are copied separately.
Sources lie below the actual producer heap end. Only the destination spans are written; no
caller catalogue, virtual window or unrelated allocation is cleared or copied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

/-- All three original arrays are copied with native loops, at fourteen instructions per
matrix cell/query pair plus constant argument and loop overhead. -/
theorem exec_copyInputs {W b A Q s t q : ℕ} (x : Data 320)
    (hb : x.regs Reg.base = b) (hA : x.regs Reg.area = A)
    (hQ : x.regs Reg.count = Q) (hs : x.regs Reg.left = s)
    (ht : x.regs Reg.right = t) (hq : x.regs Reg.queries = q)
    (hsb : s + A ≤ b) (htb : t + A ≤ b) (hqb : q + 2 * Q ≤ b)
    (hfit : Fits W (2 * b + 2 * A + 2 * Q + 64)) :
    ∃ y, ExecWithin W copyInputs x y (14 * A + 14 * Q + 21) ∧
      (∀ a < A, y.mem (b + 5 + a) = x.mem (s + a)) ∧
      (∀ a < A, y.mem (b + 5 + A + a) = x.mem (t + a)) ∧
      (∀ a < 2 * Q, y.mem (b + 5 + 2 * A + a) = x.mem (q + a)) ∧
      (∀ a, a < b + 5 ∨ b + 5 + 2 * A + 2 * Q ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 96 → i ≠ Reg.address → y.regs i = x.regs i := by
  refine WP.exists_execWithin ?_
  unfold copyInputs deliverLeft deliverRight deliverQueries
  wram_exec [hs, hb, hA]
  wram_call (exec_copy (s := s) (d := b + 5) (n := A) _
    (by wram_simp) (by wram_simp) (by wram_simp)
    (by omega) (hfit.of_le (by omega))) with a ⟨am, asrc, adst, alen, ar⟩
  wram_simp at am
  have aA : a.regs Reg.area = A := (ar _ (Or.inl (by decide))).trans (by wram_simp [hA])
  have aRight : a.regs Reg.right = t := (ar _ (Or.inl (by decide))).trans (by wram_simp [ht])
  have aq : a.regs Reg.queries = q := (ar _ (Or.inl (by decide))).trans (by wram_simp [hq])
  have aQ : a.regs Reg.count = Q := (ar _ (Or.inl (by decide))).trans (by wram_simp [hQ])
  wram_exec [aRight, adst, aA]
  wram_call (exec_copy (s := t) (d := b + 5 + A) (n := A) _
    (by wram_simp) (by wram_simp)
    (by wram_simp [alen]) (by omega) (hfit.of_le (by omega))) with c ⟨cm, csrc, cdst, clen, cr⟩
  wram_simp at cm
  have cA : c.regs Reg.area = A := (cr _ (Or.inl (by decide))).trans (by wram_simp [aA])
  have cq : c.regs Reg.queries = q := (cr _ (Or.inl (by decide))).trans (by wram_simp [aq])
  have cQ : c.regs Reg.count = Q := (cr _ (Or.inl (by decide))).trans (by wram_simp [aQ])
  wram_exec [cq, cdst, cA, cQ]
  wram_call (exec_copy (s := q) (d := b + 5 + A + A) (n := Q + Q) _
    (by wram_simp) (by wram_simp) (by wram_simp)
    (by omega) (hfit.of_le (by omega))) with y ⟨ym, ysrc, ydst, ylen, yr⟩
  wram_simp at ym
  refine ⟨by wram_simp; omega, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun i hi hne => ?_⟩
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), cm,
      ArrayCopy.copyPrefix_outside (by omega), am, ArrayCopy.copyPrefix_read hj]
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), cm, ArrayCopy.copyPrefix_read hj,
      am, ArrayCopy.copyPrefix_outside (by omega)]
  · rw [show b + 5 + 2 * A + j = b + 5 + A + A + j by omega, ym, ArrayCopy.copyPrefix_read
      (by omega), cm, ArrayCopy.copyPrefix_outside (by omega), am,
      ArrayCopy.copyPrefix_outside (by omega)]
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), cm, ArrayCopy.copyPrefix_outside
      (by omega), am, ArrayCopy.copyPrefix_outside (by omega)]
  · obtain ⟨hsource, hdest, hlen⟩ : i ≠ Reg.source ∧ i ≠ Reg.destination ∧ i ≠ Reg.length := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd hi (by decide)
    rw [yr i (Or.inl hi)]
    wram_simp [hsource, hdest, hlen, hne, cr i (Or.inl hi), ar i (Or.inl hi)]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
