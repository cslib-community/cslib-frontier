/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.DataStructure.BTree.WordRAM.Loops
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Single-Node Leaf, Value-Overwrite, and Singleton-Root Subprograms

Internal Word-RAM subroutines used privately by `InsertLoop` and `Insert` (never re-exported
publicly by `CslibFrontier.DataStructure.BTree.WordRAM`):

* `leafInsertCode` (`leafInsertCode_spec`): shift-inserts `(k, v)` into a non-full leaf node `u`
  (`memInsertLeaf`).
* `overwriteValCode` (`overwriteValCode_spec`): overwrites the value at slot `slot` of node `u` in
  place (`memOverwriteVal`).
* `initSingleCode` (`initSingleCode_spec`): initializes node `0` as a singleton leaf root `(k, v)`
  when inserting into an empty arena (`memInitSingle`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def leafInsertPre1 : Code .standard 20 := ram[
  rDst ← rNumK;
  rLim ← rNumK - rSlot ]

private def leafInsertPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne ]

private def leafInsertPost : Code .standard 20 := ram[
  rTmp1 ← rSrc + rSlot;
  *rTmp1 ← rVal;
  rSrc ← rSrc - rDeg;
  rSrc ← rSrc - rDeg;
  rSrc ← rSrc + rOne;
  rTmp1 ← rSrc + rSlot;
  *rTmp1 ← rKey;
  rSrc ← rSrc - rOne;
  rTmp1 ← rNumK + rOne;
  *rSrc ← rTmp1;
  rActive ← #0 ]

/-- Shift-insert `(rKey, rVal)` at `rSlot` in non-full leaf `rCur` (`memInsertLeaf`). -/
def leafInsertCode : Code .standard 20 := ram[
  ⟪leafInsertPre1⟫;
  ⟪shiftLoop⟫;
  ⟪leafInsertPre2⟫;
  ⟪shiftLoop⟫;
  ⟪leafInsertPost⟫ ]

/-- Specification of `leafInsertCode`, realizing `memInsertLeaf base t u m slot k v` in
`36 * t + 22` instructions. -/
theorem leafInsertCode_spec {w base capNodes t u m slot k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v)
    (hnk : x.regs rNumK = m) (hslot_reg : x.regs rSlot = slot)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) :
    ∃ y, ExecWithin w leafInsertCode x y (36 * t + 22) ∧
      y.Bounded w ∧
      y.mem = memInsertLeaf base t u m slot k v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = x.regs rZero ∧
      y.regs rActive = 0 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hsrc_au : x.regs rSrc = au + 2 := hau_def ▸ hsrc
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hf_ms : Fits w (m - slot) := hfit.of_le (by omega)
  let x₁ := (x.set rDst m).set rLim (m - slot)
  have hp1 : ExecWithin w leafInsertPre1 x x₁ 2 := by
    dsimp only [x₁]
    wram_exec [leafInsertPre1, hnk, hslot_reg, hf_ms]
  obtain ⟨x₂, hs1, hb₂, hmem₂, hreg₂⟩ :=
    shiftLoop_spec (arrBase := au + 2) (upper := m) (count := m - slot)
      (hp1.bounded hbdd) ho hsrc_au rfl rfl (by omega) (hfit.of_le (by omega))
  have hsrc₂ : x₂.regs rSrc = au + 2 := (hreg₂ rSrc (by decide)).trans hsrc_au
  have hdst₂ : x₂.regs rDst = m := hreg₂ rDst (by decide)
  have hlim₂ : x₂.regs rLim = m - slot := hreg₂ rLim (by decide)
  have ho₂ : x₂.regs rOne = 1 := (hreg₂ rOne (by decide)).trans ho
  have hd₂ : x₂.regs rDeg = t := (hreg₂ rDeg (by decide)).trans hdeg
  have hav_eq : au + 2 + t + t - 1 = au + (2 * t + 1) := by omega
  let x₃ := ((x₂.set rSrc (au + 2 + t)).set rSrc (au + 2 + t + t)).set rSrc (au + (2 * t + 1))
  have hp2 : ExecWithin w leafInsertPre2 x₂ x₃ 3 := by
    unfold leafInsertPre2; dsimp only [x₃]
    have hf1 : Fits w (au + 2 + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + 2 + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [ho₂, hd₂, hsrc₂, hav_eq, hf1, hf2, hf3]
  obtain ⟨x₄, hs2, hb₄, hmem₄, hreg₄⟩ :=
    shiftLoop_spec (arrBase := au + (2 * t + 1)) (upper := m) (count := m - slot)
      (hp2.bounded hb₂) ho₂ rfl hdst₂ hlim₂ (by omega) (hfit.of_le (by omega))
  have hsrc₄ : x₄.regs rSrc = au + (2 * t + 1) := hreg₄ rSrc (by decide)
  have ho₄ : x₄.regs rOne = 1 := (hreg₄ rOne (by decide)).trans ho₂
  have hd₄ : x₄.regs rDeg = t := (hreg₄ rDeg (by decide)).trans hd₂
  have hb₄_reg : x₄.regs rBase = base :=
    (hreg₄ rBase (by decide)).trans ((hreg₂ rBase (by decide)).trans hbase)
  have hz₄ : x₄.regs rZero = x.regs rZero :=
    (hreg₄ rZero (by decide)).trans (hreg₂ rZero (by decide))
  have hk₄ : x₄.regs rKey = k :=
    (hreg₄ rKey (by decide)).trans ((hreg₂ rKey (by decide)).trans hkey)
  have hv₄ : x₄.regs rVal = v :=
    (hreg₄ rVal (by decide)).trans ((hreg₂ rVal (by decide)).trans hval)
  have hnk₄ : x₄.regs rNumK = m :=
    (hreg₄ rNumK (by decide)).trans ((hreg₂ rNumK (by decide)).trans hnk)
  have hsl₄ : x₄.regs rSlot = slot :=
    (hreg₄ rSlot (by decide)).trans ((hreg₂ rSlot (by decide)).trans hslot_reg)
  have hak_back : au + (2 * t + 1) - t - t + 1 = au + 2 := by omega
  have hau1_back : au + 2 - 1 = au + 1 := by omega
  have hf_vs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf_sub1 : Fits w (au + (2 * t + 1) - t) := hfit.of_le (by omega)
  have hf_sub2 : Fits w (au + (2 * t + 1) - t - t) := hfit.of_le (by omega)
  have hf_sub21 : Fits w (au + (2 * t + 1) - t - t + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_ks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hf_au2m1 : Fits w (au + 2 - 1) := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_m1 : Fits w (m + 1) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  simp only [x₁, Data.set_mem] at hmem₂
  simp only [x₃, Data.set_mem] at hmem₄
  obtain ⟨y, hp3, hymem, hb_y, hd_y, hz_y, hact_y⟩ :
      ∃ y, ExecWithin w leafInsertPost x₄ y 11 ∧
        y.mem = memInsertLeaf base t u m slot k v x.mem ∧
        y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = x.regs rZero ∧
        y.regs rActive = 0 := by
    unfold leafInsertPost
    apply WP.exists_execWithin
    wram_exec [ho₄, hd₄, hsrc₄, hk₄, hv₄, hnk₄, hsl₄, hak_back, hau1_back,
      hf_vs, hf_sub1, hf_sub2, hf_sub21, hf_au2, hf_ks, hf_au2m1, hf_au1, hf_m1, hf0]
    wram_simp [hb₄_reg, hd₄, hz₄]
    simp only [memInsertLeaf, hau_def, ← hmem₂, ← hmem₄]
    funext a
    by_cases h1 : a = au + 1
    · subst h1; simp only [Function.update_self]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : a = au + (2 * t + 1) + slot
      · subst h2
        rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_of_ne h2]
        by_cases h3 : a = au + 2 + slot
        · subst h3; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h3]
  have hfull : ExecWithin w leafInsertCode x y (36 * t + 22) :=
    (hp1.seq (hs1.seq (hp2.seq (hs2.seq hp3)))).mono (by omega)
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    have hb_lo := base_lt_nodeAddr base t u 0
    apply memInsertLeaf_outside ht hm_le hslot
    by_contra h_in; apply hnot
    simp only [Block.mem_footprint, Block.Owns, nodeStride, hau_def] at h_in ⊢
    omega
  exact ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, hb_y, hd_y, hz_y, hact_y⟩

/-- Overwrite value slot `rSlot` of node `rCur` with `rVal` and stop the descent loop. -/
@[expose] def overwriteValCode : Code .standard 20 := ram[
  rTmp1 ← rCur * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rVal;
  rActive ← #0 ]

/-- Specification of `overwriteValCode`, realizing `memOverwriteVal base t u slot v` in `10`
instructions. -/
theorem overwriteValCode_spec {w base capNodes t u slot v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot < 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u)
    (hslot_reg : x.regs rSlot = slot) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w overwriteValCode x y 10 ∧
      y.Bounded w ∧
      y.mem = memOverwriteVal base t u slot v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = x.regs rZero ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      y.regs rActive = 0 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have h2t_u : au + t + t + 1 = au + (2 * t + 1) := by omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
  have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  obtain ⟨y, he, hymem, hz_y, hb_y, hd_y, hact_y⟩ :
      ∃ y, ExecWithin w overwriteValCode x y 10 ∧
        y.mem = memOverwriteVal base t u slot v x.mem ∧
        y.regs rZero = x.regs rZero ∧ y.regs rBase = base ∧ y.regs rDeg = t ∧
        y.regs rActive = 0 := by
    unfold overwriteValCode
    apply WP.exists_execWithin
    wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hval, hna_u, h2t_u,
      hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf0]
    wram_simp [hbase, hdeg]
    simp only [memOverwriteVal, hau_def]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    rw [hymem]
    have hb_lo : base + 1 < au := hau_def ▸ base_lt_nodeAddr base t u 0
    exact Modifies.write_of_owns (n := arenaWords t capNodes)
      ⟨by rw [hau_def]; omega, by rw [hau_def]; omega⟩ v
  exact ⟨y, he, he.bounded hbdd, hymem, hmod, hz_y, hb_y, hd_y, hact_y⟩

/-- Allocate node `0` as a singleton leaf root `(rKey, rVal)` when `cnt = 0` (`memInitSingle`). -/
def initSingleCode : Code .standard 20 := ram[
  rTmp1 ← rBase + rOne;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rOne;
  rTmp2 ← rTmp1 + rOne;
  *rTmp2 ← rOne;
  rTmp2 ← rTmp2 + rOne;
  *rTmp2 ← rKey;
  rTmp2 ← rTmp1 + rDeg;
  rTmp2 ← rTmp2 + rDeg;
  rTmp2 ← rTmp2 + rOne;
  *rTmp2 ← rVal;
  *rBase ← rZero;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rOne ]

/-- Specification of `initSingleCode`, realizing `memInitSingle base t k v` in `14` instructions. -/
theorem initSingleCode_spec {w base capNodes t k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hcap : 1 ≤ capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w initSingleCode x y 14 ∧
      y.Bounded w ∧
      y.mem = memInitSingle base t k v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rBase = base ∧
      y.regs rDeg = t := by
  obtain ⟨a0, ha0_def⟩ : ∃ a0, nodeAddr base t 0 = a0 := ⟨_, rfl⟩
  have ha0_eq : base + 1 + 1 = a0 := by rw [← ha0_def]; simp only [nodeAddr]; omega
  have ha0_le : a0 + 6 * t ≤ base + arenaWords t capNodes :=
    ha0_def ▸ nodeAddr_add_le_arena (base := base) (u := 0) (by omega : 0 < capNodes)
      (o := 6 * t) le_rfl
  have h2t1_eq : a0 + t + t + 1 = a0 + (2 * t + 1) := by omega
  have ha02_eq : a0 + 1 + 1 = a0 + 2 := by omega
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b11 : Fits w (base + 1 + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_a0 : Fits w a0 := hfit.of_le (by omega)
  have hf_a01 : Fits w (a0 + 1) := hfit.of_le (by omega)
  have hf_a011 : Fits w (a0 + 1 + 1) := hfit.of_le (by omega)
  have hf_a02 : Fits w (a0 + 2) := hfit.of_le (by omega)
  have hf_a0t : Fits w (a0 + t) := hfit.of_le (by omega)
  have hf_a02t : Fits w (a0 + t + t) := hfit.of_le (by omega)
  have hf_a02t10 : Fits w (a0 + t + t + 1) := hfit.of_le (by omega)
  have hf_a02t1 : Fits w (a0 + (2 * t + 1)) := hfit.of_le (by omega)
  obtain ⟨y, he, hymem, hb_y, hd_y⟩ :
      ∃ y, ExecWithin w initSingleCode x y 14 ∧
        y.mem = memInitSingle base t k v x.mem ∧
        y.regs rBase = base ∧ y.regs rDeg = t := by
    unfold initSingleCode
    apply WP.exists_execWithin
    wram_exec [hz, ho, hbase, hdeg, hkey, hval, ha0_eq, h2t1_eq, ha02_eq,
      hf_b1, hf_b11, hf_a0, hf_a01, hf_a011, hf_a02, hf_a0t, hf_a02t, hf_a02t10, hf_a02t1]
    wram_simp [hbase, hdeg]
    simp only [memInitSingle, ha0_def]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    dsimp only [memInitSingle]
    rw [ha0_def]
    have hb_lo : base + 1 < a0 := ha0_def ▸ base_lt_nodeAddr base t 0 0
    repeat rw [Function.update_of_ne (by
      intro heq; apply hnot
      simp only [Block.mem_footprint, Block.Owns] at heq ha0_le ⊢
      omega)]
  exact ⟨y, he, he.bounded hbdd, hymem, hmod, hb_y, hd_y⟩

theorem not_readsWidth_leafInsertCode : ¬leafInsertCode.ReadsWidth := by
  simp [leafInsertCode, leafInsertPre1, leafInsertPre2, leafInsertPost,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_shiftLoop]

theorem isRandFree_leafInsertCode : leafInsertCode.IsRandFree := by
  simp [leafInsertCode, leafInsertPre1, leafInsertPre2, leafInsertPost,
    Code.IsRandFree, isRandFree_shiftLoop]

theorem not_readsWidth_overwriteValCode : ¬overwriteValCode.ReadsWidth := by decide
theorem isRandFree_overwriteValCode : overwriteValCode.IsRandFree := by decide
theorem not_readsWidth_initSingleCode : ¬initSingleCode.ReadsWidth := by decide
theorem isRandFree_initSingleCode : initSingleCode.IsRandFree := by decide

end Cslib.DataStructure.BTree.WordRAM
