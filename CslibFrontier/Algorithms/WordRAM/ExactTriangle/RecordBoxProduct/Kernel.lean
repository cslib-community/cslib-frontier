/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Program

/-!
# Checked production invocation of the physical pointer front

Physical pointers are delivered in four charged copies, outside the normalized source bank.
All raw readback and separation premises describe actual external memory. The callee computes
its layout, gathers and runs the existing product mathematics; no execution oracle is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open RecordProduct

private theorem pointerBank_injective : Function.Injective pointerBank := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change 128 + i.val = 128 + j.val at hv
  omega

/-- Invoke the actual pointer product with physically exact answers and the caller frame. -/
theorem exec_invoke {W b m t N s r q : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 320)
    (hb : x.regs Reg.base = b) (hs : x.regs Reg.left = s)
    (hr : x.regs Reg.right = r) (hq : x.regs Reg.queries = q)
    (hheader : ∀ a < 5, x.mem (b + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (b + QueriedProduct.inputEnd m N qs.length) = t)
    (hsb : s + N * D m ≤ b) (hrb : r + N * D m ≤ b) (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < N * D m, x.mem (s + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < N * D m, x.mem (r + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + N * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + 2 * (N * D m) + a))
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hfit : Fits W (2 * b + 4 * CallableProduct.windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W invoke x y (PointerBoxProduct.timeBound m t qs + 5) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize N qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 128 → i ≠ Reg.result → y.regs i = x.regs i := by
  refine WP.exists_execWithin ?_
  unfold invoke
  wram_exec [hb, hs, hr, hq]
  wram_call (PointerBoxProduct.exec X Y qs _
    rfl rfl rfl rfl
    hheader hthreshold hsb hrb hqb hleft hright hqueries hX hY ht hN hfit)
    renamed pointerBank_injective with c ⟨⟨cr, cv, -, cf, -, -, -⟩, hframe⟩
  change c.regs (pointerBank (PointerBoxProduct.callableBank CallableProduct.Reg.result)) = _ at cr
  wram_exec [cr]
  wram_simp
  refine ⟨cv, cf, fun i hi hne => ?_⟩
  have hbank (j) : pointerBank j ≠ i := fun hj => by
    have hv := congrArg Fin.val hj
    change 128 + j.val = i.val at hv
    omega
  wram_simp [hne, hframe i hbank]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
