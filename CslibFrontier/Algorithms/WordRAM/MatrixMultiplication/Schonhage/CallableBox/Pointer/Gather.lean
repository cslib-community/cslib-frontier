/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged physical gathering into the product snapshot

Only the destination snapshot is written. External sources may alias each other, with their
actual readback determining consistency. All one-past ends are checked; initial private memory
and unused registers may be arbitrary.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM

/-- Every native copy register has a distinct physical register. -/
theorem copyBank_injective : Function.Injective copyBank := by
  intro i j h
  have hv := congrArg (fun k : Fin 173 => k.val) h
  apply Fin.ext
  change 166 + i.val = 166 + j.val at hv
  omega

/-- Native copy execution with its disjoint physical scratch bank. -/
theorem exec_copy {W s d k : ℕ} (x : Data 173)
    (hs : x.regs Reg.source = s) (hd : x.regs Reg.destination = d)
    (hk : x.regs Reg.length = k) (hsep : s + k ≤ d)
    (hfit : Fits W (s + k + d + k + 1)) :
    ∃ y, ExecWithin W copy x y (7 * k + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem s d k ∧
      y.regs Reg.source = s ∧ y.regs Reg.destination = d ∧ y.regs Reg.length = k ∧
      ∀ i : Fin 173, i.val < 166 → y.regs i = x.regs i := by
  obtain ⟨y, he, ⟨ym, ys, yd, yk⟩, yf⟩ := ExecWithin.rename_post copyBank_injective
    (ArrayCopy.exec (x.comap copyBank) (hfit.of_le (by omega))
      (by change Fits W (x.regs Reg.source + x.regs Reg.length)
          rw [hs, hk]; exact hfit.of_le (by omega))
      (by change Fits W (x.regs Reg.destination + x.regs Reg.length)
          rw [hd, hk]; exact hfit.of_le (by omega))
      (by change x.regs Reg.source + x.regs Reg.length ≤ x.regs Reg.destination; omega))
  change y.regs Reg.source = _ at ys
  change y.regs Reg.destination = _ at yd
  change y.regs Reg.length = _ at yk
  refine ⟨y, ?_, ?_, ys.trans hs, yd.trans hd, yk.trans hk, ?_⟩
  · change ExecWithin W copy x y (7 * x.regs Reg.length + 4) at he
    simpa only [hk] using he
  · change y.mem = ArrayCopy.copyPrefix x.mem (x.regs Reg.source)
      (x.regs Reg.destination) (x.regs Reg.length) at ym
    simpa only [hs, hd, hk] using ym
  · intro i hi
    apply yf i
    intro j hj
    have hv := congrArg Fin.val hj
    change 166 + j.val = i.val at hv
    omega

/-- The actual memory meaning of the four destination blocks. -/
@[expose] def gatherMemory (mem : ℕ → ℕ) (b S A Q s t q : ℕ) : ℕ → ℕ :=
  let h := ArrayCopy.copyPrefix mem b (b + S) 5
  let l := ArrayCopy.copyPrefix h s (b + S + 5) A
  let r := ArrayCopy.copyPrefix l t (b + S + 5 + A) A
  ArrayCopy.copyPrefix r q (b + S + 5 + 2 * A) (2 * Q)

/-- Every physical header, address, load/store and loop step is included in the native charge. -/
theorem exec_gather {W b S A Q s t q : ℕ} (x : Data 173)
    (hb : x.regs Reg.base = b)
    (hS : x.regs (sourceBank QueriedProduct.Reg.snapshot) = S)
    (hA : x.regs (sourceBank QueriedProduct.Reg.matrixWords) = 2 * A)
    (hQ : x.regs (sourceBank QueriedProduct.Reg.queryCount) = Q)
    (h2 : x.regs (sourceBank QueriedProduct.Reg.two) = 2)
    (h5 : x.regs (sourceBank QueriedProduct.Reg.five) = 5)
    (hs : x.regs Reg.left = s) (ht : x.regs Reg.right = t)
    (hq : x.regs Reg.queries = q)
    (hS5 : 5 ≤ S) (hsb : s + A ≤ b) (htb : t + A ≤ b) (hqb : q + 2 * Q ≤ b)
    (hfit : Fits W (2 * b + 2 * S + 4 * A + 4 * Q + 32)) :
    ∃ y, ExecWithin W gather x y (gatherTime A Q) ∧
      y.mem = gatherMemory x.mem b S A Q s t q ∧
      ∀ i : Fin 173, i.val < 166 → y.regs i = x.regs i := by
  refine WP.exists_execWithin ?_
  unfold gather headerArguments leftArguments rightArguments queryArguments
  wram_exec *
  wram_call exec_copy with a ⟨am, _, adst, _, ar⟩
  wram_exec *
  wram_call exec_copy with c ⟨cm, _, cdst, clen, cr⟩
  wram_exec *
  wram_call exec_copy with d ⟨dm, _, ddst, dlen, dr⟩
  wram_exec *
  wram_call exec_copy with y ⟨ym, _, _, _, yr⟩
  wram_simp at am cm dm ym
  refine ⟨by unfold gatherTime; omega, ?_, ?_⟩
  · simpa only [gatherMemory, Nat.mul_comm Q 2, Nat.mul_div_cancel_left A (by decide : 0 < 2),
      show b + S + 5 + A + A = b + S + 5 + 2 * A by omega, dm, cm, am] using ym
  · intro i hi
    have hs' : i ≠ Reg.source := fun h => by subst h; exact absurd hi (by decide)
    have hd' : i ≠ Reg.destination := fun h => by subst h; exact absurd hi (by decide)
    have hl' : i ≠ Reg.length := fun h => by subst h; exact absurd hi (by decide)
    rw [yr i hi]
    wram_simp
    rw [dr i hi]
    wram_simp
    rw [cr i hi]
    wram_simp
    rw [ar i hi]
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
