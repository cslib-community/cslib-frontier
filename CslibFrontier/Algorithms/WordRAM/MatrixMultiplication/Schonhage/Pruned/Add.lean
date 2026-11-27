/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged consumption of a returned child value

## Main results

* `PrunedQuery.exec_addValue`: compute the child suffix address, load both signed words, call
  the existing signed-add kernel, and store the sum at the parent query address.

The instruction bound includes all indexed accesses and the native arithmetic kernel.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The signed workspace and two address-calculation registers used by one accumulation. -/
def AddValueLocal (i : Fin registers) : Prop := i.val < 9 ∨ i = address ∨ i = suffix

instance (i : Fin registers) : Decidable (AddValueLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = address ∨ i = suffix))

/-- All twenty-two instructions are native standard-basis operations. Both operands must fit
the source signed width; their sum is computed exactly by the existing two-extra-bit kernel. -/
theorem exec_addValue {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (h10 : x.regs ten = 10)
    (hleft : x.mem (x.regs valueBase + q) = encode a)
    (hright : x.mem (x.regs childValues + q / 10) = encode b)
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10)) :
    ∃ y, ExecWithin (w + 2) addValue x y 22 ∧
      y.mem = Function.update x.mem (x.regs valueBase + q) (encode (a + b)) ∧
      (∀ i, ¬AddValueLocal i → y.regs i = x.regs i) := by
  have hdiv : Fits (w + 2) (q / 10) := hc.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold addValue addValueLoad addValueStore
  wram_exec [hq, h10, hleft, hright, hp, hc, hdiv]
  wram_call (Signed.exec_add (r := 87) ha hb _ (by wram_simp) (by wram_simp))
    with u ⟨hsum, hmem, hreg⟩
  have huv : u.regs valueBase = x.regs valueBase := by
    rw [hreg valueBase (Or.inr (by decide))]
    wram_simp
  have huq : u.regs query = q := by
    rw [hreg query (Or.inr (by decide))]
    wram_simp [hq]
  wram_exec [huv, huq, show u.regs result = encode (a + b) from hsum, hp]
  refine ⟨by wram_simp [hmem], fun i hi => ?_⟩
  simp only [AddValueLocal, not_or, not_lt] at hi
  rcases hi with ⟨hi9, had, hsuf⟩
  wram_simp [hreg i (Or.inr hi9)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
