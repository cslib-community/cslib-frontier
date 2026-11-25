/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Regs
public import CslibFrontier.Computability.WordRAM.CountingLoop
public import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.Matrix.PairChunks

/-!
# Internal scratch registers, phase memory invariants, and loop helpers

Internal support module for the `O(n³)` Word-RAM Hungarian implementation, providing scratch
register indices, `OuterMem`, `StepMem`, reduced-cost arithmetic, and `fillConst` / `exec_forLoop`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow

namespace Reg

/-- Current phase root row `r`. -/
abbrev rr : Fin 28 := ⟨16, by decide⟩
/-- Phase termination flag (`0` while growing the tree, `1` once augmented). -/
abbrev augmented : Fin 28 := ⟨17, by decide⟩
/-- Chosen minimum-slack unused column `j₁`. -/
abbrev rj1 : Fin 28 := ⟨18, by decide⟩
/-- Minimum slack `δ = minv[j₁]`. -/
abbrev rdelta : Fin 28 := ⟨19, by decide⟩
/-- Matched row `i₀ = colMate[j₁]`. -/
abbrev ri0 : Fin 28 := ⟨20, by decide⟩
/-- Primary loop index. -/
abbrev idx : Fin 28 := ⟨21, by decide⟩
/-- Secondary loop index / augmenting-path column cursor. -/
abbrev idx2 : Fin 28 := ⟨22, by decide⟩
/-- Scratch address register. -/
abbrev addr : Fin 28 := ⟨24, by decide⟩
/-- Scratch value register 1. -/
abbrev val : Fin 28 := ⟨25, by decide⟩
/-- Scratch value register 2. -/
abbrev val2 : Fin 28 := ⟨26, by decide⟩
/-- Scratch temporary register. -/
abbrev tmp : Fin 28 := ⟨27, by decide⟩

end Reg

open Reg

theorem BaseRegs.of_eq {n bC M : ℕ} {x y : Data 28} (h : BaseRegs n bC M x)
    (heq : ∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) : BaseRegs n bC M y where
  hzero := (heq zero (by decide)).trans h.hzero
  hone := (heq one (by decide)).trans h.hone
  htwo := (heq two (by decide)).trans h.htwo
  hrn := (heq rn (by decide)).trans h.hrn
  hrnn := (heq rnn (by decide)).trans h.hrnn
  hrM := (heq rM (by decide)).trans h.hrM
  hbaseC := (heq baseC (by decide)).trans h.hbaseC
  hbaseY := (heq baseY (by decide)).trans h.hbaseY
  hbaseNZ := (heq baseNZ (by decide)).trans h.hbaseNZ
  hbaseColMate := (heq baseColMate (by decide)).trans h.hbaseColMate
  hbaseUsed := (heq baseUsed (by decide)).trans h.hbaseUsed
  hbaseTree := (heq baseTree (by decide)).trans h.hbaseTree
  hbaseMinv := (heq baseMinv (by decide)).trans h.hbaseMinv
  hbaseBestRow := (heq baseBestRow (by decide)).trans h.hbaseBestRow
  houtBase := (heq outBase (by decide)).trans h.houtBase
  hbaseRowMate := (heq baseRowMate (by decide)).trans h.hbaseRowMate


theorem CostMem.of_outside {n bC : ℕ} {C : Fin n × Fin n → ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : CostMem bC C m₁) (hout : ∀ a, a < bC + n * n → m₂ a = m₁ a) : CostMem bC C m₂ := by
  intro u v
  have hlt : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  rw [hout _ (by omega)]
  exact h u v

/-- Encode `Option (Fin n)` as `n` for `none` and `i.val` for `some i`. -/
@[expose] def encodeOptFin {n : ℕ} : Option (Fin n) → ℕ
  | none => n
  | some i => i.val

/-- Between-phase memory representation of `(y, z, mate)` at layout `bC`. -/
structure OuterMem {n : ℕ} (bC : ℕ) (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n)
    (mem : ℕ → ℕ) : Prop where
  /-- `y` block stores `(vget y i).toNat`. -/
  hy : ∀ i : Fin n, mem (bC + n * n + i.val) = (vget y i).toNat
  /-- `nz` block stores `(-vget z j).toNat`. -/
  hnz : ∀ j : Fin n, mem (bC + n * n + n + j.val) = (-vget z j).toNat
  /-- `colMate` block stores `encodeOptFin (vget mate j)`. -/
  hcol : ∀ j : Fin n, mem (bC + n * n + 2 * n + j.val) = encodeOptFin (vget mate j)
  /-- Matched rows map to their matched column in `rowMate`. -/
  hrow_some : ∀ j i : Fin n, vget mate j = some i →
    mem (bC + n * n + 7 * n + 1 + i.val) = j.val
  /-- Unmatched rows hold sentinel `n` in `rowMate`. -/
  hrow_none : ∀ i : Fin n, (∀ j : Fin n, vget mate j ≠ some i) →
    mem (bC + n * n + 7 * n + 1 + i.val) = n

/-- Within-phase memory representation of `(s, bestRow)` at layout `bC`. -/
structure StepMem {n : ℕ} (bC : ℕ) (s : HgState n) (bestRow : Fin n → Fin n)
    (mem : ℕ → ℕ) : Prop extends OuterMem bC s.y s.z s.mate mem where
  /-- `used` block stores `0`/`1` flags for `s.used`. -/
  hused : ∀ j : Fin n, mem (bC + n * n + 3 * n + j.val) = if vget s.used j = true then 1 else 0
  /-- `tree` block stores `0`/`1` flags for `s.tree`. -/
  htree : ∀ i : Fin n, mem (bC + n * n + 4 * n + i.val) = if vget s.tree i = true then 1 else 0
  /-- `minv` block stores `(vget s.minv j).toNat`. -/
  hminv : ∀ j : Fin n, mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat
  /-- `bestRow` block stores `(bestRow j).val`. -/
  hbest : ∀ j : Fin n, mem (bC + n * n + 6 * n + j.val) = (bestRow j).val

theorem hgRed_nat_eq {n W : ℕ} {C : Fin n × Fin n → ℕ} {y z : Vector ℤ n} {i j : Fin n}
    (hCW : C (i, j) ≤ W)
    (hy : 0 ≤ vget y i ∧ vget y i ≤ W)
    (hz : -(W : ℤ) ≤ vget z j ∧ vget z j ≤ 0)
    (hfeas : 0 ≤ hgRed (fun p => (C p : ℤ)) y z i j) :
    (vget y i).toNat ≤ C (i, j) + (-vget z j).toNat ∧
      C (i, j) + (-vget z j).toNat ≤ 2 * W ∧
      C (i, j) + (-vget z j).toNat - (vget y i).toNat =
        (hgRed (fun p => (C p : ℤ)) y z i j).toNat := by
  unfold hgRed at hfeas ⊢
  dsimp only at hfeas ⊢
  omega

theorem exec_forLoop {w N T : ℕ} {idxReg limReg : Fin 28}
    {body : Code .standard 28} (P : ℕ → Data 28 → Prop)
    (hlim : ∀ y, P (y.regs idxReg) y → y.regs limReg = N)
    (hbody : ∀ y, P (y.regs idxReg) y → y.regs idxReg < N →
      ∃ z, ExecWithin w body y z T ∧ P (y.regs idxReg + 1) z ∧
        z.regs idxReg = y.regs idxReg + 1)
    {x : Data 28} (h0 : P 0 (x.set idxReg 0)) :
    ∃ y, ExecWithin w (.seq (ram[ idxReg ← #0 ]) (.loop (.lt idxReg limReg) body)) x y
      (N * (T + 2) + 3) ∧ P N y := by
  have hs₀ : ExecWithin w (ram[ idxReg ← #0 ] : Code .standard 28) x (x.set idxReg 0) 1 := by
    refine WP.execWithin ?_
    wram_exec
    rfl
  have hidx0 : (x.set idxReg 0).regs idxReg = 0 := Data.set_regs_self x idxReg 0
  have h0' : P ((x.set idxReg 0).regs idxReg) (x.set idxReg 0) := by
    rw [hidx0]
    exact h0
  obtain ⟨y, hl, hPN, _⟩ := ExecWithin.loop_count P hlim hbody
    (by rw [hidx0]; exact Nat.zero_le N) h0'
  refine ⟨y, (hs₀.seq hl).mono ?_, hPN⟩
  rw [hidx0, Nat.sub_zero]
  omega

/-! ### Reusable leaf loops -/

/-- Fill `[dst, dst + n)` with `valReg`. -/
abbrev fillConst (dst valReg : Fin 28) : Code .standard 28 :=
  Cslib.WordRAM.fillConst dst rn valReg one idx addr

theorem exec_fillConst {w n bC M : ℕ} (dst valReg : Fin 28)
    (hd_lt : dst.val < 21) (hv_lt : valReg.val < 21) (x : Data 28)
    (hb : BaseRegs n bC M x) (hdst : x.regs dst + n ≤ bC + n * n + 8 * n + 1)
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w (fillConst dst valReg) x y (5 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ k < n, y.mem (x.regs dst + k) = x.regs valReg) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + n) → y.mem a = x.mem a) := by
  have hne : ∀ j : Fin 28, j.val < 21 → idx ≠ j ∧ addr ≠ j := fun j hj =>
    ⟨fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
  obtain ⟨y, he, hr, _, hmem⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := dst) (len := rn) (val := valReg) (one := one) (idx := idx) (addr := addr)
    (hne dst hd_lt).1 (by decide) (hne valReg hv_lt).1 (by decide)
    (hne dst hd_lt).2 (by decide) (hne valReg hv_lt).2 (by decide) (by decide)
    hb.hone (by rw [hb.hrn]; exact hfit.of_le (by omega))
    (by rw [hb.hrn]; exact hfit.of_le (by omega))
  rw [hb.hrn] at he hmem
  exact ⟨y, he.within, fun i hi => hr i (hne i hi).1.symm (hne i hi).2.symm,
    fun k hk => by rw [hmem]; exact fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩,
    fun a ha => by rw [hmem]; exact fill_of_not_owns ha⟩


end Cslib.Algorithms.WordRAM.Hungarian
