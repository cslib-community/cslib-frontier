/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Control
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual native leaf multiplication

## Main results

* `PrunedQuery.exec_leafProduct`: load the two encoded leaf words and store their exact signed
  product, within nineteen native instructions.
* `PrunedQuery.exec_leaf`: take the actual empty/nonempty branch and return to the parent.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The existing signed workspace and the indexed-load address register. -/
def LeafLocal (i : Fin registers) : Prop := i.val < 9 ∨ i = address

instance (i : Fin registers) : Decidable (LeafLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = address))

/-- Both loads, the existing fourteen-instruction signed multiplication kernel and the store
are charged. The ordinary mathematical product must fit the source signed width. -/
theorem exec_leafProduct {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers)
    (hleft : x.mem (x.regs arrayA + x.regs leafPrefix) = encode a)
    (hright : x.mem (x.regs arrayB + x.regs leafPrefix) = encode b)
    (hp : Fits (w + 2) (x.regs arrayA + x.regs leafPrefix))
    (hq : Fits (w + 2) (x.regs arrayB + x.regs leafPrefix)) :
    ∃ y, ExecWithin (w + 2) leafProduct x y 19 ∧
      y.mem = Function.update x.mem (x.regs valueBase) (encode (a * b)) ∧
      (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [leafProduct, leafLoad, hleft, hright, hp, hq]
  wram_call (Signed.exec_multiply (r := 87) ha hb hab _ (by wram_simp) (by wram_simp))
    with u ⟨hproduct, hmem, hreg⟩
  have hv : u.regs valueBase = x.regs valueBase := by
    rw [hreg valueBase (Or.inr (by decide))]
    wram_simp
  have hproduct' : u.regs result = encode (a * b) := hproduct
  wram_exec [hv, hproduct']
  refine ⟨?_, fun i hi => ?_⟩
  · wram_simp
    rw [hmem]
    rfl
  · simp only [LeafLocal, not_or, not_lt] at hi
    rcases hi with ⟨hi9, had⟩
    wram_simp
    rw [hreg i (Or.inr hi9)]
    wram_simp

/-- Registers used by the full leaf phase, including its actual parent-return decision. -/
def LeafReturnLocal (i : Fin registers) : Prop :=
  LeafLocal i ∨ PopLocal i ∨ i = temporary

instance (i : Fin registers) : Decidable (LeafReturnLocal i) :=
  inferInstanceAs (Decidable (LeafLocal i ∨ PopLocal i ∨ i = temporary))

/-- The empty leaf performs no operand loads or multiplication. A requested leaf computes
its signed product. Both execute the real return branch; root termination and parent
accumulation are decided by the stored depth register, not by an external call rule. -/
theorem exec_leaf {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers) (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hleft : x.mem (x.regs arrayA + x.regs leafPrefix) = encode a)
    (hright : x.mem (x.regs arrayB + x.regs leafPrefix) = encode b)
    (hp : Fits (w + 2) (x.regs arrayA + x.regs leafPrefix))
    (hq : Fits (w + 2) (x.regs arrayB + x.regs leafPrefix))
    (hd : Fits (w + 2) (x.regs level + 2)) :
    ∃ y, ExecWithin (w + 2) leaf x y 24 ∧
      y.mem = (if x.regs count = 0 then x.mem else
        Function.update x.mem (x.regs valueBase) (encode (a * b))) ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then x.regs mode else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else x.regs active) ∧
      (∀ i, ¬LeafReturnLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [leaf, h0]
  · have hne : x.regs count ≠ 0 := Nat.ne_of_gt hc
    wram_call (exec_leafProduct ha hb hab x hleft hright hp hq) with v ⟨hmem, hreg⟩
    have hvd : v.regs level = x.regs level := hreg level (by decide)
    have hvm : v.regs mode = x.regs mode := hreg mode (by decide)
    have hva : v.regs active = x.regs active := hreg active (by decide)
    wram_call (exec_pop v (by regs_frame) (by regs_frame) (by rwa [hvd]))
      with y ⟨hymem, hyl, hym, hya, hyr⟩
    refine ⟨by omega, ?_, by rwa [hvd] at hyl, by rwa [hvd, hvm] at hym, by rwa [hvd, hva] at hya,
      fun i hi => ?_⟩
    · simp only [hne, ↓reduceIte]
      exact hymem.trans hmem
    · simp only [LeafReturnLocal, not_or] at hi
      exact (hyr i hi.2.1).trans (hreg i hi.1)
  · have heq : x.regs count = 0 := Nat.eq_zero_of_not_pos hc
    wram_call (exec_pop _ (by wram_simp [h0]) (by wram_simp [h1]) (by wram_simp; exact hd))
      with y ⟨hymem, hyl, hym, hya, hyr⟩
    wram_simp at hymem hyl hym hya
    refine ⟨by omega, by simp only [heq, ↓reduceIte]; exact hymem, hyl, hym, hya, fun i hi => ?_⟩
    simp only [LeafReturnLocal, not_or] at hi
    rcases hi with ⟨_, hip, hit⟩
    rw [hyr i hip]
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
