/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.DataStructure.BTree.WordRAM.Loops
import CslibFrontier.DataStructure.BTree.WordRAM.CopyUpper
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Proactive Full-Root Split Subprogram (`splitRootCode`)

Internal Word-RAM subroutine used privately by `Insert` (never re-exported publicly by
`CslibFrontier.DataStructure.BTree.WordRAM`): splits a full `(2 * t - 1)`-key root `oldRoot` into
`oldRoot` and newly allocated sibling `cnt`, and writes a new `1`-key internal root at `cnt + 1`
(`memSplitRoot`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def splitRootPost : Code .standard 20 := ram[
  rCur ← rCnt + rOne;
  rDst ← rCur * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  *rDst ← rZero;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rOne;
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rLim ← rDeg - rOne;
  rTmp1 ← rSrc + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rOne;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rTmp2;
  rTmp1 ← rSrc + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rTmp2;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  *rTmp1 ← rChild;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rCnt;
  *rBase ← rCur;
  rCnt ← rCur + rOne;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rCnt ]

/-- Split full root `rChild = oldRoot` into `oldRoot` and `cnt`, creating a new `1`-key root at
`cnt + 1` (`memSplitRoot`). -/
def splitRootCode : Code .standard 20 := ram[
  ⟪copyUpperCode⟫;
  ⟪splitRootPost⟫ ]

/-- Specification of `splitRootCode`, realizing `memSplitRoot base t oldRoot cnt` in `21 * t + 88`
instructions. -/
theorem splitRootCode_spec {w base capNodes t oldRoot cnt : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hr_lt : oldRoot < cnt) (hcap : cnt + 2 ≤ capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hchild : x.regs rChild = oldRoot) (hcnt : x.regs rCnt = cnt) :
    ∃ y, ExecWithin w splitRootCode x y (21 * t + 88) ∧
      y.Bounded w ∧
      y.mem = memSplitRoot base t oldRoot cnt x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
      y.regs rCur = cnt + 1 ∧ y.regs rCnt = cnt + 2 := by
  obtain ⟨x₁, he1, hb₁, hmem₁, hmod₁, hz₁, hkeep₁⟩ :=
    copyUpperCode_spec ht (by omega) (by omega) (by omega) hbdd hfit hz0 ho hbase hdeg hstride
      hchild hcnt
  have ho₁ : x₁.regs rOne = 1 := (hkeep₁ rOne (by decide)).trans ho
  have hb₁_reg : x₁.regs rBase = base := (hkeep₁ rBase (by decide)).trans hbase
  have hd₁ : x₁.regs rDeg = t := (hkeep₁ rDeg (by decide)).trans hdeg
  have hst₁ : x₁.regs rStride = 6 * t := (hkeep₁ rStride (by decide)).trans hstride
  have hch₁ : x₁.regs rChild = oldRoot := (hkeep₁ rChild (by decide)).trans hchild
  have hcnt₁ : x₁.regs rCnt = cnt := (hkeep₁ rCnt (by decide)).trans hcnt
  have hk₁ : x₁.regs rKey = x.regs rKey := hkeep₁ rKey (by decide)
  have hv₁ : x₁.regs rVal = x.regs rVal := hkeep₁ rVal (by decide)
  have hsep_rc : nodeAddr base t oldRoot + 6 * t ≤ nodeAddr base t cnt := by
    have hmul : (oldRoot + 1) * nodeStride t ≤ cnt * nodeStride t := Nat.mul_le_mul_right _ hr_lt
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  have hsep_rn : nodeAddr base t oldRoot + 6 * t ≤ nodeAddr base t (cnt + 1) := by
    have hmul : (oldRoot + 1) * nodeStride t ≤ (cnt + 1) * nodeStride t :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  have hk_med_m1 : x₁.mem (nodeAddr base t oldRoot + 2 + (t - 1)) =
      keyAt base t x.mem oldRoot (t - 1) := by
    simp only [keyAt, hmem₁, Nat.add_assoc]
    exact memCopyUpper_at_c hsep_rc (2 + (t - 1)) (by omega) (by omega) x.mem
  have hv_med_m1 : x₁.mem (nodeAddr base t oldRoot + (2 * t + 1) + (t - 1)) =
      valAt base t x.mem oldRoot (t - 1) := by
    simp only [valAt, hmem₁, Nat.add_assoc]
    exact memCopyUpper_at_c hsep_rc (2 * t + (1 + (t - 1))) (by omega) (by omega) x.mem
  obtain ⟨ar, har_def⟩ : ∃ ar, nodeAddr base t (cnt + 1) = ar := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t oldRoot = ac := ⟨_, rfl⟩
  have har_le : ar + 6 * t ≤ base + arenaWords t capNodes :=
    har_def ▸ nodeAddr_add_le_arena (base := base) (u := cnt + 1)
      (by omega : cnt + 1 < capNodes) (o := 6 * t) le_rfl
  have hac_le : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) (u := oldRoot)
      (by omega : oldRoot < capNodes) (o := 6 * t) le_rfl
  rw [hac_def] at hk_med_m1 hv_med_m1 hsep_rc
  rw [hac_def, har_def] at hsep_rn
  have hna_r : base + (cnt + 1) * (6 * t) + 1 + 1 = ar := by
    simp only [← har_def, nodeAddr, nodeStride]; omega
  have hna_c : base + oldRoot * (6 * t) + 1 + 1 = ac := by
    simp only [← hac_def, nodeAddr, nodeStride]; omega
  have hcap_aw : base + 2 + capNodes ≤ base + arenaWords t capNodes := by
    have : capNodes ≤ capNodes * nodeStride t :=
      Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
    simp only [arenaWords]; omega
  have hf (k : ℕ) (hk : k ≤ base + arenaWords t capNodes) : Fits w k := hfit.of_le hk
  obtain ⟨y, he2, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcur_y, hcnt_y⟩ :
      ∃ y, ExecWithin w splitRootPost x₁ y 40 ∧
        y.mem = memSplitRoot base t oldRoot cnt x.mem ∧
        y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
        y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
        y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
        y.regs rCur = cnt + 1 ∧ y.regs rCnt = cnt + 2 := by
    unfold splitRootPost
    apply WP.exists_execWithin
    wram_exec [hz₁, ho₁, hb₁_reg, hd₁, hst₁, hch₁, hcnt₁, hna_r, hna_c, hk_med_m1, hv_med_m1,
      (by omega : ac + t + t + 1 = ac + (2 * t + 1)),
      (by omega : ar + t + t + 1 = ar + (2 * t + 1)),
      (by omega : ar + t + t + t + t = ar + 4 * t),
      (by omega : ac + 1 + 1 + (t - 1) = ac + 2 + (t - 1)),
      (by omega : ar + 1 + 1 = ar + 2),
      (by omega : cnt + 1 + 1 = cnt + 2),
      (by omega : ac + 2 + (t - 1) ≠ ar),
      (by omega : ac + 2 + (t - 1) ≠ ar + 1),
      (by omega : ac + (2 * t + 1) + (t - 1) ≠ ar),
      (by omega : ac + (2 * t + 1) + (t - 1) ≠ ar + 1),
      (by omega : ac + (2 * t + 1) + (t - 1) ≠ ar + 2),
      hf (cnt + 1) (by omega), hf (cnt + 1 + 1) (by omega), hf (base + 1) (by omega),
      hf (t - 1) (by omega), hf ((cnt + 1) * (6 * t)) (by omega),
      hf (base + (cnt + 1) * (6 * t)) (by omega), hf (base + (cnt + 1) * (6 * t) + 1) (by omega),
      hf (base + (cnt + 1) * (6 * t) + 1 + 1) (by omega),
      hf ar (by omega), hf (ar + 1) (by omega), hf (ar + 1 + 1) (by omega), hf (ar + 2) (by omega),
      hf (ar + t) (by omega), hf (ar + t + t) (by omega), hf (ar + t + t + 1) (by omega),
      hf (ar + (2 * t + 1)) (by omega), hf (ar + t + t + t) (by omega),
      hf (ar + t + t + t + t) (by omega), hf (ar + 4 * t) (by omega),
      hf (ar + 4 * t + 1) (by omega),
      hf (oldRoot * (6 * t)) (by omega), hf (base + oldRoot * (6 * t)) (by omega),
      hf (base + oldRoot * (6 * t) + 1) (by omega),
      hf (base + oldRoot * (6 * t) + 1 + 1) (by omega),
      hf ac (by omega), hf (ac + 1) (by omega), hf (ac + 1 + 1) (by omega),
      hf (ac + 1 + 1 + (t - 1)) (by omega), hf (ac + 2 + (t - 1)) (by omega),
      hf (ac + t) (by omega), hf (ac + t + t) (by omega), hf (ac + t + t + 1) (by omega),
      hf (ac + (2 * t + 1)) (by omega), hf (ac + (2 * t + 1) + (t - 1)) (by omega)]
    wram_simp [hz₁, ho₁, hb₁_reg, hd₁, hst₁, hk₁, hv₁]
    simp only [memSplitRoot, har_def, ← hmem₁]
  have hmod₂ : Modifies (Block.mk base (arenaWords t capNodes)).footprint x₁.mem y.mem := by
    intro addr hnot
    have hb_lo : base + 1 < ar := har_def ▸ base_lt_nodeAddr base t (cnt + 1) 0
    rw [hymem]
    dsimp only [memSplitRoot]
    rw [har_def]
    repeat rw [Function.update_of_ne fun heq => hnot <| by
      simp only [Block.mem_footprint, Block.Owns] at heq har_le ⊢; omega]
    rw [← hmem₁]
  have hfull : ExecWithin w splitRootCode x y (21 * t + 88) :=
    (he1.seq he2).mono (by omega)
  exact ⟨y, hfull, hfull.bounded hbdd, hymem,
    by simpa only [Finset.union_self] using hmod₁.trans hmod₂,
    hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcur_y, hcnt_y⟩

theorem not_readsWidth_splitRootCode : ¬splitRootCode.ReadsWidth := by
  simp [splitRootCode, splitRootPost, Code.ReadsWidth, Op.ReadsWidth, Op.bin,
    not_readsWidth_copyUpperCode]

theorem isRandFree_splitRootCode : splitRootCode.IsRandFree := by
  simp [splitRootCode, splitRootPost, Code.IsRandFree, isRandFree_copyUpperCode]

end Cslib.DataStructure.BTree.WordRAM
