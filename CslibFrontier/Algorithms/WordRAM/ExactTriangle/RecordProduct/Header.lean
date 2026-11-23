/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Decode
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Tactic.UpdateSimp

/-!
# Original callee header stores

The native stores place the payload length, computed tensor level and recovered inner depth,
outer dimension and actual occurrence count above the producer's heap. No encoded matrix or
query table is supplied by this header.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

private theorem writeHeader_preserves : ∀ i : Fin 320, i.val < 78 → writeHeader.Preserves i := by
  decide +kernel

/-- Fifteen actual arithmetic/copy/store instructions write the five original header words.
All metadata below register 78, including the complete producer bank, is preserved. -/
theorem exec_writeHeader {W b m n A Q : ℕ} (x : Data 320)
    (hb : x.regs Reg.base = b) (hm : x.regs Reg.destination = 2 * m)
    (hA : x.regs Reg.twiceArea = 2 * A) (hQ : x.regs Reg.count = Q)
    (hn : x.regs Reg.size = n) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (h19 : x.regs Reg.nineteen = 19) (h4 : x.regs Reg.four = 4)
    (hfit : Fits W (b + 19 * m + 2 * A + 2 * Q + 64)) :
    ∃ y, ExecWithin W writeHeader x y 15 ∧
      (Block.mk b 5).Realizes y.mem ![4 + 2 * A + 2 * Q, 19 * m, m, n, Q] ∧
      (∀ a, a < b ∨ b + 5 ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 78 → y.regs i = x.regs i := by
  have hquot : 2 * m / 2 = m := by omega
  refine WP.exists_execWithin_preserves (fun i hi => writeHeader_preserves i hi) ?_
  unfold writeHeader
  wram_exec [hb, hm, hA, hQ, hn, h1, h2, h19, h4, hquot]
  intro hpres
  refine ⟨?_, fun a ha => by update_simp, hpres⟩
  intro j
  change Data.mem _ (b + j.val) = _
  (fin_cases j <;> (dsimp; update_simp)) <;> omega

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
