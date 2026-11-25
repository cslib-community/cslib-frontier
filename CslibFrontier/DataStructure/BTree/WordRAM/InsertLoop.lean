/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.DataStructure.BTree.WordRAM.Loops
import CslibFrontier.DataStructure.BTree.WordRAM.LeafInsert
import CslibFrontier.DataStructure.BTree.WordRAM.SplitChild
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Proactive Top-Down Non-Full Insertion Loop (`insertLoop`)

Internal Word-RAM downward-pass loop used privately by `Insert` (never re-exported publicly by
`CslibFrontier.DataStructure.BTree.WordRAM`): starting from any non-full node `u` (`numKeys u ≤
2 * t - 2`), scans `u`, overwrites in place if `k` is already in `u`, shift-inserts if `u` is a
leaf, or proactively splits a full child `c` via `splitChildCode` before descending (`insertLoop`,
`insertLoop_spec`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def insertDescendAfterSplit : Code .standard 20 := ram[
  rTmp1 ← rCur * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  rTmp2 ← *rTmp1;
  if rTmp2 = rKey then [
    ⟪overwriteValCode⟫
  ] else [
    if rKey < rTmp2 then [
      rCur ← rChild
    ] else [
      rCur ← rCnt - rOne
    ]
  ] ]

private def insertDescendOrLeaf : Code .standard 20 := ram[
  rTmp1 ← rSrc - rOne;
  rTmp1 ← rTmp1 - rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rSlot;
    rChild ← *rTmp1;
    rTmp1 ← rChild * rStride;
    rTmp1 ← rBase + rTmp1;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp2 ← *rTmp1;
    rTmp1 ← rDeg + rDeg;
    rTmp1 ← rTmp1 - rOne;
    if rTmp2 = rTmp1 then [
      ⟪splitChildCode⟫;
      ⟪insertDescendAfterSplit⟫
    ] else [
      rCur ← rChild
    ]
  ] else [
    ⟪leafInsertCode⟫
  ] ]

private def insertBranch : Code .standard 20 := ram[
  if rSlot < rNumK then [
    rTmp1 ← rSrc + rSlot;
    rTmp2 ← *rTmp1;
    if rTmp2 = rKey then [
      ⟪overwriteValCode⟫
    ] else [
      ⟪insertDescendOrLeaf⟫
    ]
  ] else [
    ⟪insertDescendOrLeaf⟫
  ] ]

private def insertStep : Code .standard 20 := ram[
  ⟪loadAndScan⟫;
  ⟪insertBranch⟫ ]

/-- Downward proactive-split insertion loop over non-full nodes (`while rZero < rActive`). -/
def insertLoop : Code .standard 20 := ram[
  while rZero < rActive do [⟪insertStep⟫] ]

private theorem insertDescendAfterSplit_spec {w base capNodes t u slot c cnt₁ k v : ℕ}
    {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot < 2 * t - 1) (hcnt_pos : 1 ≤ cnt₁)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u)
    (hslot_reg : x.regs rSlot = slot) (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = cnt₁)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧
      y.Bounded w ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
      (if keyAt base t x.mem u slot = k then
        y.mem = memOverwriteVal base t u slot v x.mem ∧ y.regs rActive = 0
      else if k < keyAt base t x.mem u slot then
        y.mem = x.mem ∧ y.regs rCur = c ∧ y.regs rActive = x.regs rActive
      else
        y.mem = x.mem ∧ y.regs rCur = cnt₁ - 1 ∧ y.regs rActive = x.regs rActive) := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hau2_eq : au + 1 + 1 = au + 2 := by omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au11 : Fits w (au + 1 + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_auks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hks_eq : x.mem (au + 2 + slot) = keyAt base t x.mem u slot := by
    simp only [keyAt, hau_def]
  by_cases heq_k : keyAt base t x.mem u slot = k
  · have he_full : ∃ y', ExecWithin w insertDescendAfterSplit x y' 20 ∧
        y'.mem = memOverwriteVal base t u slot v x.mem ∧
        y'.regs rZero = x.regs rZero ∧ y'.regs rOne = 1 ∧
        y'.regs rBase = base ∧ y'.regs rDeg = t ∧ y'.regs rStride = 6 * t ∧
        y'.regs rKey = k ∧ y'.regs rVal = v ∧ y'.regs rCnt = cnt₁ ∧ y'.regs rActive = 0 := by
      unfold insertDescendAfterSplit overwriteValCode
      have h2t_u : au + t + t + 1 = au + (2 * t + 1) := by omega
      have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
      have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
      have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
      have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
      have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
      have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      apply WP.exists_execWithin
      wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hkey, hval, hna_u, hau2_eq, h2t_u,
        hks_eq, heq_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11, hf_au2, hf_auks,
        hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf0]
      wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      simp only [memOverwriteVal, hau_def]
    obtain ⟨y', he', hymem', hz', ho', hb', hd', hst', hk', hv', hcnt', hact'⟩ := he_full
    have hmod' : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y'.mem := by
      rw [hymem']
      have hb_lo : base + 1 < au := hau_def ▸ base_lt_nodeAddr base t u 0
      exact Modifies.write_of_owns (n := arenaWords t capNodes)
        ⟨by rw [hau_def]; omega, by rw [hau_def]; omega⟩ v
    refine ⟨y', he', he'.bounded hbdd, hmod', hz', ho', hb', hd', hst', hk', hv', hcnt', ?_⟩
    simp only [heq_k, ↓reduceIte]
    exact ⟨hymem', hact'⟩
  · by_cases hlt_k : k < keyAt base t x.mem u slot
    · obtain ⟨y, he, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcnt_y, hcur_y, hact_y⟩ :
          ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧ y.mem = x.mem ∧
            y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
            y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
            y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
            y.regs rCur = c ∧ y.regs rActive = x.regs rActive := by
        unfold insertDescendAfterSplit
        apply WP.exists_execWithin
        wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hchild, hkey, hna_u, hau2_eq,
          hks_eq, heq_k, hlt_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11,
          hf_au2, hf_auks]
        wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      refine ⟨y, he, he.bounded hbdd, hymem ▸ Modifies.refl _ _, hz_y, ho_y, hb_y, hd_y, hst_y,
        hk_y, hv_y, hcnt_y, ?_⟩
      simp only [heq_k, hlt_k, ↓reduceIte]
      exact ⟨hymem, hcur_y, hact_y⟩
    · have hf_cm1 : Fits w (cnt₁ - 1) := (hbdd.1 rCnt).of_le (by rw [hcnt]; omega)
      obtain ⟨y, he, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcnt_y, hcur_y, hact_y⟩ :
          ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧ y.mem = x.mem ∧
            y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
            y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
            y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
            y.regs rCur = cnt₁ - 1 ∧ y.regs rActive = x.regs rActive := by
        unfold insertDescendAfterSplit
        apply WP.exists_execWithin
        wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hcnt, hkey, hna_u, hau2_eq,
          hks_eq, heq_k, hlt_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11,
          hf_au2, hf_auks, hf_cm1]
        wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      refine ⟨y, he, he.bounded hbdd, hymem ▸ Modifies.refl _ _, hz_y, ho_y, hb_y, hd_y, hst_y,
        hk_y, hv_y, hcnt_y, ?_⟩
      simp only [heq_k, hlt_k, ↓reduceIte]
      exact ⟨hymem, hcur_y, hact_y⟩

private theorem insertDescendOrLeaf_int_spec
    {w base capNodes t u m slot c cnt k v : ℕ} {mem₀ : ℕ → ℕ} {z : Data 20}
    (ht : 2 ≤ t) (hu_lt_cnt : u < cnt) (hc_lt_cnt : c < cnt) (huc : u ≠ c)
    (hcap_cnt1 : cnt + 1 ≤ capNodes) (hnonfull : m ≤ 2 * t - 2) (hslot_le : slot ≤ m)
    (hlf0 : leafFlag base t mem₀ u = 0) (hcid : childAt base t mem₀ u slot = c)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hbz : z.Bounded w) (hmz : z.mem = mem₀)
    (hzz : z.regs rZero = 0) (hoz : z.regs rOne = 1)
    (hbaz : z.regs rBase = base) (hdz : z.regs rDeg = t) (hstz : z.regs rStride = 6 * t)
    (hkz : z.regs rKey = k) (hvz : z.regs rVal = v)
    (hcurz : z.regs rCur = u) (hcntz : z.regs rCnt = cnt)
    (hnkz : z.regs rNumK = m) (hslz : z.regs rSlot = slot)
    (hsrcz : z.regs rSrc = nodeAddr base t u + 2) (hactz : z.regs rActive = 1) :
    ∃ x₃, ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) ∧
      x₃.Bounded w ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint mem₀ x₃.mem ∧
      x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
      x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
      x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
      (if numKeys base t mem₀ c = 2 * t - 1 then
        let mem₁ := memSplitChild base t u m slot c cnt mem₀
        x₃.regs rCnt = cnt + 1 ∧
        (if keyAt base t mem₁ u slot = k then
          x₃.mem = memOverwriteVal base t u slot v mem₁ ∧ x₃.regs rActive = 0
        else if k < keyAt base t mem₁ u slot then
          x₃.mem = mem₁ ∧ x₃.regs rCur = c ∧ x₃.regs rActive = 1
        else
          x₃.mem = mem₁ ∧ x₃.regs rCur = cnt ∧ x₃.regs rActive = 1)
      else
        x₃.mem = mem₀ ∧ x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1) := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hu_cap : u < capNodes := by omega
  have hc_cap : c < capNodes := by omega
  have hau_le' : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hac_le' : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
  have hsrcz_au : z.regs rSrc = au + 2 := hau_def ▸ hsrcz
  have hsub2 : au + 2 - 1 - 1 = au := by omega
  have hadd4 : au + t + t + t + t = au + 4 * t := by omega
  have hna_c : base + c * (6 * t) + 1 + 1 + 1 = ac + 1 := by
    rw [← hac_def]; simp only [nodeAddr, nodeStride]; omega
  have hlfz : z.mem au = 0 := by rw [hmz, ← hau_def]; exact hlf0
  have hcidz : z.mem (au + 4 * t + slot) = c := by
    rw [hmz, ← hau_def, ← hcid]; rfl
  have hnkc_z : z.mem (ac + 1) = numKeys base t mem₀ c := by
    rw [hmz, ← hac_def]; rfl
  have hcap_le : capNodes ≤ capNodes * nodeStride t :=
    Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
  have hf_au1 : Fits w (au + 2 - 1) := hfit.of_le (by omega)
  have hf_au22 : Fits w (au + 2 - 1 - 1) := hfit.of_le (by omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_t1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_t2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_t3 : Fits w (au + t + t + t) := hfit.of_le (by omega)
  have hf_t40 : Fits w (au + t + t + t + t) := hfit.of_le (by omega)
  have hf_t4 : Fits w (au + 4 * t) := hfit.of_le (by omega)
  have hf_cs : Fits w (au + 4 * t + slot) := hfit.of_le (by omega)
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_cb2 : Fits w (base + c * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_ac10 : Fits w (base + c * (6 * t) + 1 + 1 + 1) := hfit.of_le (by omega)
  have hf_ac1 : Fits w (ac + 1) := hfit.of_le (by omega)
  have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
  have hf_2tm10 : Fits w (t + t - 1) := hfit.of_le (by omega)
  have hf_2tm1 : Fits w (2 * t - 1) := hfit.of_le (by omega)
  have h2tm1_eq : t + t - 1 = 2 * t - 1 := by omega
  by_cases hfull_c : numKeys base t mem₀ c = 2 * t - 1
  · let z₁ : Data 20 :=
      ((((((((((((((((z.set rTmp1 (au + 2 - 1)).set rTmp1 au).set rTmp2 0).set rTmp1
        (au + t)).set rTmp1 (au + t + t)).set rTmp1 (au + t + t + t)).set rTmp1
        (au + 4 * t)).set rTmp1 (au + 4 * t + slot)).set rChild c).set rTmp1
        (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
        (base + c * (6 * t) + 1)).set rTmp1
        (base + c * (6 * t) + 1 + 1)).set rTmp1 (ac + 1)).set rTmp2
        (2 * t - 1)).set rTmp1 (t + t)).set rTmp1 (2 * t - 1)
    have hbz₁ : z₁.Bounded w := by
      dsimp only [z₁]
      exact ((((((((((((((((hbz.set hf_au1).set hf_au).set
        (hfit.of_le (Nat.zero_le _))).set hf_t1).set hf_t2).set hf_t3).set hf_t4).set
        hf_cs).set (hfit.of_le (by simp only [arenaWords]; omega))).set hf_cmul).set
        hf_cb0).set hf_cb1).set hf_cb2).set hf_ac1).set hf_2tm1).set hf_2t).set hf_2tm1
    obtain ⟨z₂, hsc_exec, hbz₂, hmem_z₂, hmod_sc, hz_z₂, ho_z₂, hb_z₂, hd_z₂, hst_z₂,
        hk_z₂, hv_z₂, hact_z₂, hcur_z₂, hsl_z₂, hch_z₂, _, hcnt_z₂⟩ :=
      splitChildCode_spec (x := z₁) (c := c) ht hu_lt_cnt hc_lt_cnt huc hcap_cnt1 hnonfull
        hslot_le hbz₁ hfit hzz hoz hbaz hdz hstz hcurz hnkz hslz rfl hcntz
    simp only [z₁, Data.set_mem] at hmem_z₂ hmod_sc
    dsimp only [z₁] at hk_z₂ hv_z₂ hact_z₂
    rw [hmz] at hmem_z₂ hmod_sc
    wram_simp at hk_z₂ hv_z₂ hact_z₂
    obtain ⟨x₃, hdas, hbx₃, hmod_das, hz_x₃, ho_x₃, hb_x₃, hd_x₃, hst_x₃, hk_x₃, hv_x₃,
        hcnt_x₃, hbr_das⟩ :=
      insertDescendAfterSplit_spec (x := z₂) ht hu_cap (by omega) (by omega) hbz₂ hfit
        ho_z₂ hb_z₂ hd_z₂ hst_z₂ hcur_z₂ hsl_z₂ hch_z₂ hcnt_z₂ (hk_z₂.trans hkz)
        (hv_z₂.trans hvz)
    have he_dl : ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) := by
      unfold insertDescendOrLeaf
      apply WP.execWithin
      wram_exec [hzz, hoz, hbaz, hdz, hstz, hslz, hsrcz_au, hsub2, hadd4, hna_c,
        hlfz, hcidz, hnkc_z, hfull_c, h2tm1_eq,
        hf_au1, hf_au22, hf_au, hf_t1, hf_t2, hf_t3, hf_t40, hf_t4, hf_cs,
        hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac10, hf_ac1, hf_2t, hf_2tm10, hf_2tm1]
      refine WP.of_execWithin hsc_exec ?_
      exact WP.of_execWithin hdas ⟨by omega, rfl⟩
    have hmod_all : Modifies (Block.mk base (arenaWords t capNodes)).footprint mem₀ x₃.mem :=
      by simpa using hmod_sc.trans hmod_das
    rw [hmem_z₂] at hbr_das
    rw [hact_z₂.trans hactz] at hbr_das
    simp only [Nat.add_sub_cancel] at hbr_das
    refine ⟨x₃, he_dl, hbx₃, hmod_all, hz_x₃.trans hz_z₂, ho_x₃,
      hb_x₃, hd_x₃, hst_x₃, hk_x₃, hv_x₃, ?_⟩
    simp only [hfull_c, ↓reduceIte]
    exact ⟨hcnt_x₃, hbr_das⟩
  · obtain ⟨x₃, he_dl, hmx₃, hzx₃, hox₃, hbx₃, hdx₃, hstx₃, hkx₃, hvx₃, hcurx₃, hcntx₃,
        hactx₃⟩ :
        ∃ x₃, ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) ∧
          x₃.mem = z.mem ∧ x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
          x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
          x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
          x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1 := by
      unfold insertDescendOrLeaf
      apply WP.exists_execWithin
      wram_exec [hzz, hoz, hbaz, hdz, hstz, hslz, hsrcz_au, hsub2, hadd4, hna_c,
        hlfz, hcidz, hnkc_z, hfull_c, h2tm1_eq,
        hf_au1, hf_au22, hf_au, hf_t1, hf_t2, hf_t3, hf_t40, hf_t4, hf_cs,
        hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac10, hf_ac1, hf_2t, hf_2tm10, hf_2tm1]
      wram_simp [hzz, hoz, hbaz, hdz, hstz, hkz, hvz, hcntz, hactz]
    refine ⟨x₃, he_dl, he_dl.bounded hbz, (hmx₃.trans hmz) ▸ Modifies.refl _ _, hzx₃,
      hox₃, hbx₃, hdx₃, hstx₃, hkx₃, hvx₃, ?_⟩
    simp only [hfull_c, ↓reduceIte]
    exact ⟨hmx₃.trans hmz, hcurx₃, hcntx₃, hactx₃⟩

/-- Shared non-hit `insertBranch` wrapper: whether `slot < m` (with `keyAt u slot ≠ k`) or
`slot = m`, `insertBranch` dispatches to `insertDescendOrLeaf` in `T + 7` steps, clobbering at most
`rTmp1` and `rTmp2` beforehand. -/
private theorem insertBranch_of_not_hit {w base capNodes t u m slot k T : ℕ} {mem₀ : ℕ → ℕ}
    {x₂ : Data 20} {P : Data 20 → Prop}
    (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 2)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hb₂ : x₂.Bounded w) (hmem₂ : x₂.mem = mem₀)
    (hk₂ : x₂.regs rKey = k) (hnk₂ : x₂.regs rNumK = m)
    (hslot₂ : x₂.regs rSlot = slot) (hsrc₂ : x₂.regs rSrc = nodeAddr base t u + 2)
    (hhit : ¬(slot < m ∧ keyAt base t mem₀ u slot = k))
    (hbody : ∀ z : Data 20, z.Bounded w → z.mem = mem₀ →
      (∀ reg : Fin 20, reg ≠ rTmp1 → reg ≠ rTmp2 → z.regs reg = x₂.regs reg) →
      ∃ y, ExecWithin w insertDescendOrLeaf z y T ∧ P y) :
    ∃ y, ExecWithin w insertBranch x₂ y (T + 7) ∧ P y := by
  have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  by_cases hlt_m : slot < m
  · have hne_k : keyAt base t mem₀ u slot ≠ k := fun heq => hhit ⟨hlt_m, heq⟩
    have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
    have hks_eq : x₂.mem (nodeAddr base t u + 2 + slot) = keyAt base t mem₀ u slot := by
      rw [hmem₂]; rfl
    let x₂' := (x₂.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 (keyAt base t mem₀ u slot)
    obtain ⟨y, hdl, hP⟩ := hbody x₂' ((hb₂.set hf_ks).set (hmem₂ ▸ hb₂.2 _)) hmem₂
      (fun reg h1 h2 => by
        dsimp only [x₂']
        simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _])
    have he_br : ExecWithin w insertBranch x₂ y (T + 7) := by
      unfold insertBranch
      apply WP.execWithin
      wram_exec [hnk₂, hsrc₂, hslot₂, hk₂, hlt_m, hks_eq, hne_k, hf_ks]
      exact WP.of_execWithin hdl ⟨by omega, rfl⟩
    exact ⟨y, he_br, hP⟩
  · obtain ⟨y, hdl, hP⟩ := hbody x₂ hb₂ hmem₂ (fun _ _ _ => rfl)
    have he_br : ExecWithin w insertBranch x₂ y (T + 7) := by
      unfold insertBranch
      apply WP.execWithin
      wram_exec [hnk₂, hslot₂, hlt_m]
      exact WP.of_execWithin hdl ⟨by omega, rfl⟩
    exact ⟨y, he_br, hP⟩

private theorem insertLoop_overwrite_spec {l w base capNodes t u cnt k v : ℕ} {x x₂ : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u) (hs : SortedNode l base t x.mem u)
    (hnonfull : numKeys base t x.mem u ≤ 2 * t - 2)
    (hcnt_mem : x.mem (base + 1) = cnt)
    (hcond_in : (Cond.lt rZero rActive).Holds x)
    (h12 : ExecWithin w loadAndScan x x₂ (8 * numKeys base t x.mem u + 12))
    (hb₂ : x₂.Bounded w) (hmem₂ : x₂.mem = x.mem)
    (hz₂ : x₂.regs rZero = 0) (ho₂ : x₂.regs rOne = 1)
    (hb₂_reg : x₂.regs rBase = base) (hd₂ : x₂.regs rDeg = t)
    (hst₂ : x₂.regs rStride = 6 * t)
    (hk₂ : x₂.regs rKey = k) (hv₂ : x₂.regs rVal = v) (hcur₂ : x₂.regs rCur = u)
    (hsrc₂ : x₂.regs rSrc = nodeAddr base t u + 2)
    (hnk₂ : x₂.regs rNumK = numKeys base t x.mem u)
    (hslot₂ : x₂.regs rSlot = slotCount base t x.mem u k (numKeys base t x.mem u))
    (hhit : slotCount base t x.mem u k (numKeys base t x.mem u) < numKeys base t x.mem u ∧
      keyAt base t x.mem u (slotCount base t x.mem u k (numKeys base t x.mem u)) = k) :
    ∃ y cnt',
      ExecWithin w insertLoop x y ((91 * t + 160) * (l + 1) + 2) ∧
      y.Bounded w ∧
      cnt ≤ cnt' ∧ cnt' ≤ cnt + l ∧
      y.mem base = x.mem base ∧
      y.mem (base + 1) = cnt' ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      (∀ w_id, w_id ∉ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' →
        ∀ o < nodeStride t, y.mem (nodeAddr base t w_id + o) = x.mem (nodeAddr base t w_id + o)) ∧
      ValidNode l base t y.mem u ∧
      SortedNode l base t y.mem u ∧
      numKeys base t x.mem u ≤ numKeys base t y.mem u ∧
      readNodeSet l base t y.mem u ⊆ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' ∧
      (readTree l base t y.mem u).toList =
        Cslib.SortedAssoc.insert k v (readTree l base t x.mem u).toList := by
  set m := numKeys base t x.mem u
  set slot := slotCount base t x.mem u k m
  have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hlt_m : slot < m := hhit.1
  have heq_k : keyAt base t x.mem u slot = k := hhit.2
  have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
  have hks_eq : x₂.mem (nodeAddr base t u + 2 + slot) = k := by rw [hmem₂]; exact heq_k
  let x₂' := (x₂.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 k
  obtain ⟨y, hov, _, hymem, hmod_y, hz_y, hb_y_reg, hd_y, hact_y⟩ :=
    overwriteValCode_spec (x := x₂') ht hu_cap (by omega)
      ((hb₂.set hf_ks).set (hk₂ ▸ hb₂.1 rKey))
      hfit ho₂ hb₂_reg hd₂ hst₂ hcur₂ hslot₂ hv₂
  have h3 : ExecWithin w insertBranch x₂ y 15 := by
    unfold insertBranch
    apply WP.execWithin
    wram_exec [hnk₂, hsrc₂, hslot₂, hk₂, hlt_m, hks_eq, hf_ks]
    exact WP.of_execWithin hov ⟨by omega, rfl⟩
  have hstep : ExecWithin w insertStep x y (91 * t + 158) :=
    (h12.seq h3).mono (by omega)
  have hz_y0 : y.regs rZero = 0 := hz_y.trans hz₂
  have hexit : ExecWithin w insertLoop y y 2 :=
    ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y0, hact_y, Nat.lt_irrefl,
      not_false_eq_true])
  have hiter_bound : (91 * t + 158) + 2 + 2 ≤ (91 * t + 160) * (l + 1) + 2 := by
    have hmul1 : 91 * t + 160 ≤ (91 * t + 160) * (l + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos l)
    omega
  have hymem' : y.mem = memOverwriteVal base t u slot v x.mem := by
    rw [hymem]; simp only [x₂', Data.set_mem, hmem₂]
  obtain ⟨hv', hs', hset', htr'⟩ := memOverwriteVal_spec ht hv hs hlt_m heq_k
  have hb_lo := base_lt_nodeAddr base t u (2 * t + 1 + slot)
  simp only [x₂', Data.set_mem, hmem₂] at hmod_y
  refine ⟨y, cnt, (hstep.loop_iter hcond_in hexit).mono hiter_bound,
    (hstep.loop_iter hcond_in hexit).bounded hbdd, le_rfl, Nat.le_add_right cnt l, ?_, ?_,
    hb_y_reg, hd_y, hmod_y, ?_, hymem' ▸ hv', hymem' ▸ hs', ?_, ?_, hymem' ▸ htr'⟩
  · rw [hymem']; dsimp only [memOverwriteVal]; rw [Function.update_of_ne (by omega)]
  · rw [hymem']; dsimp only [memOverwriteVal]; rw [Function.update_of_ne (by omega), hcnt_mem]
  · intro w_id hnot o ho_lt
    have hw_ne : w_id ≠ u := fun heq => hnot (by
      rw [heq]; exact Finset.mem_union_left _ (self_mem_readNodeSet l base t x.mem u))
    have hsep := nodeAddr_disjoint (base := base) (o₂ := (2 * t + 1) + slot) hw_ne ho_lt
      (by simp only [nodeStride]; omega)
    rw [← Nat.add_assoc] at hsep
    rw [hymem']; dsimp only [memOverwriteVal]
    exact Function.update_of_ne hsep _ _
  · rw [hymem']; dsimp only [numKeys, memOverwriteVal]
    have hst_eq : nodeStride t = 6 * t := rfl
    rw [Function.update_of_ne (by omega)]
    exact le_rfl
  · rw [hymem', hset']; exact Finset.subset_union_left

/-- Specification of `insertLoop` starting from non-full node `u` of height `l`: runs in at most
`(91 * t + 160) * (l + 1) + 2` instructions, allocating at most `l` nodes while preserving
`ValidNode`/`SortedNode` and realizing `Cslib.SortedAssoc.insert k v`. -/
theorem insertLoop_spec {l w base capNodes t u cnt k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t)
    (hbdd : x.Bounded w)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u)
    (hs : SortedNode l base t x.mem u)
    (hnonfull : numKeys base t x.mem u ≤ 2 * t - 2)
    (hrange : readNodeSet l base t x.mem u ⊆ Finset.range cnt)
    (hcap : cnt + l ≤ capNodes)
    (hcnt_mem : x.mem (base + 1) = cnt)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v)
    (hcur : x.regs rCur = u) (hcnt_reg : x.regs rCnt = cnt)
    (hact : x.regs rActive = 1) :
    ∃ y cnt',
      ExecWithin w insertLoop x y ((91 * t + 160) * (l + 1) + 2) ∧
      y.Bounded w ∧
      cnt ≤ cnt' ∧ cnt' ≤ cnt + l ∧
      y.mem base = x.mem base ∧
      y.mem (base + 1) = cnt' ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      (∀ w_id, w_id ∉ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' →
        ∀ o < nodeStride t, y.mem (nodeAddr base t w_id + o) = x.mem (nodeAddr base t w_id + o)) ∧
      ValidNode l base t y.mem u ∧
      SortedNode l base t y.mem u ∧
      numKeys base t x.mem u ≤ numKeys base t y.mem u ∧
      readNodeSet l base t y.mem u ⊆ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' ∧
      (readTree l base t y.mem u).toList =
        Cslib.SortedAssoc.insert k v (readTree l base t x.mem u).toList := by
  induction l generalizing u cnt x
  all_goals
    have hu_lt_cnt : u < cnt :=
      Finset.mem_range.mp (hrange (self_mem_readNodeSet _ base t x.mem u))
    have hu_cap : u < capNodes := by omega
    set m := numKeys base t x.mem u
    have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
    obtain ⟨x₂, h12, hb₂, hmem₂, hz₂, ho₂, hb₂_reg, hd₂, hst₂, hk₂, hcur₂, hsrc₂, hnk₂,
        hslot₂, hreg₂⟩ :=
      loadAndScan_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    have hv₂ : x₂.regs rVal = v := (hreg₂ rVal (by decide)).trans hval
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    have hslot_le : slot ≤ m := hsc.1
    have hcond_in : (Cond.lt rZero rActive).Holds x := by
      simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · exact insertLoop_overwrite_spec ht hu_cap hbdd hfit hv hs hnonfull hcnt_mem hcond_in
        h12 hb₂ hmem₂ hz₂ ho₂ hb₂_reg hd₂ hst₂ hk₂ hv₂ hcur₂ hsrc₂ hnk₂ hslot₂ hhit
    have hgt_all : ∀ i, slot ≤ i → i < m → k < keyAt base t x.mem u i :=
      keyAt_gt_of_slotCount_not_hit (fun _ _ => hs.keys_strict) hhit
  · have hf_au1 : Fits w (nodeAddr base t u + 2 - 1) := hfit.of_le (by omega)
    have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
    have hsub2 : nodeAddr base t u + 2 - 1 - 1 = nodeAddr base t u := by omega
    have h1_ne_0 : (1 : ℕ) ≠ 0 := by omega
    obtain ⟨y, h3, hymem, hmod_y, hb_y, hd_y, hz_y, hact_y⟩ :=
      insertBranch_of_not_hit hu_cap hnonfull hfit hb₂ hmem₂ hk₂ hnk₂ hslot₂ hsrc₂ hhit
        (P := fun y => y.mem = memInsertLeaf base t u m slot k v x.mem ∧
          Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
          y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = 0 ∧ y.regs rActive = 0)
        (T := 36 * t + 28) (fun z hbz hmz hreg_z => by
          have hzz : z.regs rZero = 0 := (hreg_z rZero (by decide) (by decide)).trans hz₂
          have hoz : z.regs rOne = 1 := (hreg_z rOne (by decide) (by decide)).trans ho₂
          have hbaz : z.regs rBase = base := (hreg_z rBase (by decide) (by decide)).trans hb₂_reg
          have hdz : z.regs rDeg = t := (hreg_z rDeg (by decide) (by decide)).trans hd₂
          have hkz : z.regs rKey = k := (hreg_z rKey (by decide) (by decide)).trans hk₂
          have hvz : z.regs rVal = v := (hreg_z rVal (by decide) (by decide)).trans hv₂
          have hnkz : z.regs rNumK = m := (hreg_z rNumK (by decide) (by decide)).trans hnk₂
          have hslz : z.regs rSlot = slot := (hreg_z rSlot (by decide) (by decide)).trans hslot₂
          have hsrcz : z.regs rSrc = nodeAddr base t u + 2 :=
            (hreg_z rSrc (by decide) (by decide)).trans hsrc₂
          have hlfz : z.mem (nodeAddr base t u) = 1 := by rw [hmz]; exact hv.leafFlag_eq
          let z' := ((z.set rTmp1 (nodeAddr base t u + 2 - 1)).set rTmp1
            (nodeAddr base t u)).set rTmp2 1
          obtain ⟨y, hli, _, hym, hmod_l, hby, hdy, hzy, hacty⟩ :=
            leafInsertCode_spec (x := z') ht hu_cap hnonfull hslot_le
              (((hbz.set hf_au1).set hf_au).set (hfit.of_le (by omega)))
              hfit hoz hbaz hdz hkz hvz hnkz hslz hsrcz
          have he_dl : ExecWithin w insertDescendOrLeaf z y (36 * t + 28) := by
            unfold insertDescendOrLeaf
            apply WP.execWithin
            wram_exec [hzz, hoz, hsrcz, hsub2, hlfz, h1_ne_0, hf_au1, hf_au]
            exact WP.of_execWithin hli ⟨by omega, rfl⟩
          simp only [z', Data.set_mem, Data.set_regs_of_ne (by decide : rZero ≠ rTmp2) _,
            Data.set_regs_of_ne (by decide : rZero ≠ rTmp1) _] at hym hmod_l hzy
          rw [hmz] at hym hmod_l
          exact ⟨y, he_dl, hym, hmod_l, hby, hdy, hzy.trans hzz, hacty⟩)
    have hstep : ExecWithin w insertStep x y (91 * t + 158) :=
      (h12.seq h3).mono (by omega)
    have hexit : ExecWithin w insertLoop y y 2 :=
      ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y, hact_y, Nat.lt_irrefl,
        not_false_eq_true])
    obtain ⟨hv', hs', hnk', htr'⟩ := memInsertLeaf_spec ht hv hs hnonfull hslot_le hsc.2.1 hgt_all
    have hb_lo := base_lt_nodeAddr base t u 0
    refine ⟨y, cnt, (hstep.loop_iter hcond_in hexit).mono (by omega),
      (hstep.loop_iter hcond_in hexit).bounded hbdd, le_rfl, le_rfl, ?_, ?_,
      hb_y, hd_y, hmod_y, ?_, hymem ▸ hv', hymem ▸ hs', ?_, ?_, hymem ▸ htr'⟩
    · rw [hymem]; exact memInsertLeaf_outside ht hnonfull hslot_le x.mem base (by omega)
    · rw [hymem, memInsertLeaf_outside ht hnonfull hslot_le x.mem (base + 1) (by omega),
        hcnt_mem]
    · intro w_id hnot o ho_lt
      have hw_ne : w_id ≠ u := fun heq => hnot (by
        rw [heq]; exact Finset.mem_union_left _ (self_mem_readNodeSet 0 base t x.mem u))
      have hsep := nodeAddr_sep base t hw_ne
      rw [hymem]
      exact memInsertLeaf_outside ht hnonfull hslot_le x.mem _ (by omega)
    · rw [hymem, hnk']; omega
    · simp only [readNodeSet_zero]; exact Finset.subset_union_left
  · rename_i l ih
    have hcnt₂ : x₂.regs rCnt = cnt := (hreg₂ rCnt (by decide)).trans hcnt_reg
    have hact₂ : x₂.regs rActive = 1 := (hreg₂ rActive (by decide)).trans hact
    have hmul_step : (91 * t + 160) * (l + 1 + 1) = (91 * t + 160) * (l + 1) + (91 * t + 160) :=
      Nat.mul_succ _ _
    obtain ⟨c, hc_def⟩ : ∃ c, childAt base t x.mem u slot = c := ⟨_, rfl⟩
    have hslot_lt1 : slot < m + 1 := by omega
    have hv_c : ValidNode l base t x.mem c := hc_def ▸ hv.child_valid hslot_lt1
    have hs_c : SortedNode l base t x.mem c := hc_def ▸ hs.child_sorted hslot_lt1
    have hrange_c : readNodeSet l base t x.mem c ⊆ Finset.range cnt :=
      (hc_def ▸ child_subset_readNodeSet l base t x.mem u slot hslot_lt1).trans hrange
    have hc_lt_cnt : c < cnt :=
      Finset.mem_range.mp (hrange_c (self_mem_readNodeSet l base t x.mem c))
    have hc_cap : c < capNodes := by omega
    have hac_le := nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
    have huc : u ≠ c := fun heq =>
      (hc_def ▸ hv.not_mem_child_readNodeSet hslot_lt1)
        (Eq.ndrec (motive := fun w_id => w_id ∈ readNodeSet l base t x.mem c)
          (self_mem_readNodeSet l base t x.mem c) heq.symm)
    obtain ⟨x₃, h3, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩ :=
      insertBranch_of_not_hit hu_cap hnonfull hfit hb₂ hmem₂ hk₂ hnk₂ hslot₂ hsrc₂ hhit
        (P := fun x₃ => x₃.Bounded w ∧
          Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem x₃.mem ∧
          x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
          x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
          x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
          (if numKeys base t x.mem c = 2 * t - 1 then
            let mem₁ := memSplitChild base t u m slot c cnt x.mem
            x₃.regs rCnt = cnt + 1 ∧
            (if keyAt base t mem₁ u slot = k then
              x₃.mem = memOverwriteVal base t u slot v mem₁ ∧ x₃.regs rActive = 0
            else if k < keyAt base t mem₁ u slot then
              x₃.mem = mem₁ ∧ x₃.regs rCur = c ∧ x₃.regs rActive = 1
            else
              x₃.mem = mem₁ ∧ x₃.regs rCur = cnt ∧ x₃.regs rActive = 1)
          else
            x₃.mem = x.mem ∧ x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1))
        (T := 75 * t + 155) (fun z hbz hmz hreg_z => by
          obtain ⟨x₃, hdl, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩ :=
            insertDescendOrLeaf_int_spec (z := z) ht hu_lt_cnt hc_lt_cnt huc (by omega) hnonfull
              hslot_le hv.leafFlag_eq hc_def hfit hbz hmz
              ((hreg_z rZero (by decide) (by decide)).trans hz₂)
              ((hreg_z rOne (by decide) (by decide)).trans ho₂)
              ((hreg_z rBase (by decide) (by decide)).trans hb₂_reg)
              ((hreg_z rDeg (by decide) (by decide)).trans hd₂)
              ((hreg_z rStride (by decide) (by decide)).trans hst₂)
              ((hreg_z rKey (by decide) (by decide)).trans hk₂)
              ((hreg_z rVal (by decide) (by decide)).trans hv₂)
              ((hreg_z rCur (by decide) (by decide)).trans hcur₂)
              ((hreg_z rCnt (by decide) (by decide)).trans hcnt₂)
              ((hreg_z rNumK (by decide) (by decide)).trans hnk₂)
              ((hreg_z rSlot (by decide) (by decide)).trans hslot₂)
              ((hreg_z rSrc (by decide) (by decide)).trans hsrc₂)
              ((hreg_z rActive (by decide) (by decide)).trans hact₂)
          exact ⟨x₃, hdl, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩)
    have hstep : ExecWithin w insertStep x x₃ (91 * t + 158) :=
      (h12.seq h3).mono (by omega)
    by_cases hfull_c : numKeys base t x.mem c = 2 * t - 1
    · simp only [hfull_c, ↓reduceIte] at hbr₃
      obtain ⟨hcnt₃, hbr₃⟩ := hbr₃
      obtain ⟨mem₁, hmem₁_def⟩ :
          ∃ mem₁, memSplitChild base t u m slot c cnt x.mem = mem₁ := ⟨_, rfl⟩
      rw [hmem₁_def] at hbr₃
      have hcnt_fresh : cnt ∉ readNodeSet (l + 1) base t x.mem u := fun hin => by
        have := Finset.mem_range.mp (hrange hin); omega
      have hmsc := memSplitChild_spec ht hv hs hnonfull hslot_le
        (hc_def.symm ▸ hfull_c) hcnt_fresh
      dsimp only at hmsc
      change (let m' := m; let c' := childAt base t x.mem u slot; _) at hmsc
      rw [hc_def, hmem₁_def] at hmsc
      obtain ⟨hm1_b1, hm1_b0, hv_u1, hs_u1, hnk_u1, hk_s1, hv_s1, hc_s1, hc_s11, hnk_c1, hnk_z1,
          hsub_u1, htr_u1⟩ := hmsc
      have hrange_u1 : readNodeSet (l + 1) base t mem₁ u ⊆ Finset.range (cnt + 1) := by
        intro w_id hwin
        rw [Finset.mem_range]
        rcases Finset.mem_insert.mp (hsub_u1 hwin) with rfl | hold
        · omega
        · have := Finset.mem_range.mp (hrange hold); omega
      have hframe_mem₁ : ∀ w_id, w_id ≠ u → w_id ≠ c → w_id ≠ cnt →
          ∀ o < nodeStride t, mem₁ (nodeAddr base t w_id + o) =
            x.mem (nodeAddr base t w_id + o) := by
        intro w_id hnu hnc hnz o ho_lt
        have hb_lo := base_lt_nodeAddr base t w_id o
        have hsu := nodeAddr_sep base t hnu
        have hsc_d := nodeAddr_sep base t hnc
        have hsz := nodeAddr_sep base t hnz
        rw [← hmem₁_def]
        exact memSplitChild_outside ht hnonfull hslot_le x.mem _ (by omega) (by omega)
          (by omega) (by omega)
      have hu_in_old : u ∈ readNodeSet (l + 1) base t x.mem u :=
        self_mem_readNodeSet (l + 1) base t x.mem u
      have hc_in_old : c ∈ readNodeSet (l + 1) base t x.mem u :=
        hc_def ▸ child_subset_readNodeSet l base t x.mem u slot hslot_lt1
          (self_mem_readNodeSet l base t x.mem (childAt base t x.mem u slot))
      by_cases heq_med : keyAt base t mem₁ u slot = k
      · simp only [heq_med, ↓reduceIte] at hbr₃
        obtain ⟨hmem₃_eq, hact₃⟩ := hbr₃
        have hexit : ExecWithin w insertLoop x₃ x₃ 2 :=
          ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz₃, hact₃, Nat.lt_irrefl,
            not_false_eq_true])
        have hslot_lt_u1 : slot < numKeys base t mem₁ u := by rw [hnk_u1]; omega
        obtain ⟨hv_u2, hs_u2, hset_u2, htr_u2⟩ :=
          memOverwriteVal_spec ht hv_u1 hs_u1 hslot_lt_u1 heq_med
        have hb_lo := base_lt_nodeAddr base t u (2 * t + 1 + slot)
        refine ⟨x₃, cnt + 1, (hstep.loop_iter hcond_in hexit).mono (by omega),
          (hstep.loop_iter hcond_in hexit).bounded hbdd, by omega, by omega, ?_, ?_,
          hb₃, hd₃, hmod₃, ?_, hmem₃_eq ▸ hv_u2, hmem₃_eq ▸ hs_u2, ?_, ?_, ?_⟩
        · rw [hmem₃_eq, memOverwriteVal, Function.update_of_ne (by omega), hm1_b0]
        · rw [hmem₃_eq, memOverwriteVal, Function.update_of_ne (by omega), hm1_b1]
        · intro w_id hnot o ho_lt
          simp only [Finset.mem_union, Finset.mem_Ico, not_or] at hnot
          have hnu : w_id ≠ u := fun heq => hnot.1 (heq ▸ hu_in_old)
          have hnc : w_id ≠ c := fun heq => hnot.1 (heq ▸ hc_in_old)
          have hnz : w_id ≠ cnt := by omega
          have hsep := nodeAddr_disjoint (base := base) (o₂ := (2 * t + 1) + slot) hnu ho_lt
            (by simp only [nodeStride]; omega)
          rw [← Nat.add_assoc] at hsep
          rw [hmem₃_eq]; dsimp only [memOverwriteVal]
          rw [Function.update_of_ne hsep]
          exact hframe_mem₁ w_id hnu hnc hnz o ho_lt
        · rw [hmem₃_eq]; dsimp only [numKeys, memOverwriteVal]
          have hst_eq : nodeStride t = 6 * t := rfl
          rw [Function.update_of_ne (by omega)]
          change m ≤ numKeys base t mem₁ u
          rw [hnk_u1]; omega
        · rw [hmem₃_eq, hset_u2]
          intro w_id hwin
          rcases Finset.mem_insert.mp (hsub_u1 hwin) with rfl | hold
          · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
          · exact Finset.mem_union_left _ hold
        · rw [hmem₃_eq, htr_u2, htr_u1]
      -- Otherwise the loop descends into the new child `d` at position `s ∈ {slot, slot + 1}`:
      simp only [heq_med, ↓reduceIte] at hbr₃
      obtain ⟨s, d, hs, hcd, hlt_s, hgt_s, hnk_d, hmem₃_eq, hcur₃, hact₃⟩ :
          ∃ s d, s ≤ numKeys base t mem₁ u ∧ childAt base t mem₁ u s = d ∧
            (∀ i < s, keyAt base t mem₁ u i < k) ∧
            (∀ i, s ≤ i → i < numKeys base t mem₁ u → k < keyAt base t mem₁ u i) ∧
            numKeys base t mem₁ d = t - 1 ∧
            x₃.mem = mem₁ ∧ x₃.regs rCur = d ∧ x₃.regs rActive = 1 := by
        by_cases hlt_med : k < keyAt base t mem₁ u slot
        · simp only [hlt_med, ↓reduceIte] at hbr₃
          refine ⟨slot, c, by omega, hc_s1, fun i hi => ?_, fun i hge hi => ?_, hnk_c1, hbr₃⟩
          · rw [← hmem₁_def, keyAt_memSplitChild_lt ht hnonfull hslot_le huc (by omega) hi]
            exact hsc.2.1 i hi
          · rcases eq_or_lt_of_le hge with rfl | hgt
            exacts [hlt_med, hlt_med.trans (hs_u1.keys_strict hgt hi)]
        · simp only [hlt_med, ↓reduceIte] at hbr₃
          have hmed_lt_k : keyAt base t mem₁ u slot < k := by omega
          refine ⟨slot + 1, cnt, by omega, hc_s11, fun i hi => ?_, fun i hge hi => ?_, hnk_z1,
            hbr₃⟩
          · rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hlt_s
            exacts [hmed_lt_k, (hs_u1.keys_strict hlt_s (by omega)).trans hmed_lt_k]
          · rw [hnk_u1] at hi
            rw [← hmem₁_def, keyAt_memSplitChild_gt ht hnonfull hslot_le huc (by omega) hge hi]
            exact hgt_all (i - 1) (by omega) (by omega)
      have hs1 : s < numKeys base t mem₁ u + 1 := by omega
      have hsub_d : readNodeSet l base t mem₁ d ⊆ readNodeSet (l + 1) base t mem₁ u := by
        rw [← hcd]; exact child_subset_readNodeSet l base t mem₁ u s hs1
      have hv_d : ValidNode l base t x₃.mem d := by
        rw [hmem₃_eq, ← hcd]; exact hv_u1.child_valid hs1
      have hs_d : SortedNode l base t x₃.mem d := by
        rw [hmem₃_eq, ← hcd]; exact hs_u1.child_sorted hs1
      obtain ⟨y, cnt', hy_rec, hby, hcnt1_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_rec, hfr_rec, hv_d', hs_d', hnk_d_le, hsub_d', htr_d'⟩ :=
        ih hbx₃ hv_d hs_d (by rw [hmem₃_eq, hnk_d]; omega)
          (by rw [hmem₃_eq]; exact hsub_d.trans hrange_u1) (by omega) (hmem₃_eq ▸ hm1_b1)
          hz₃ ho₃ hb₃ hd₃ hst₃ hk₃ hv₃ hcur₃ hcnt₃ hact₃
      rw [hmem₃_eq] at hfr_rec hnk_d_le hsub_d' htr_d' hmb0
      obtain ⟨hv_u', hs_u', hnk_u', hsub_u', htr_u'⟩ :=
        childInsert_spec (slot := s) (cnt := cnt + 1) (cnt' := cnt') ht hv_u1 hs_u1 hs hlt_s
          hgt_s hrange_u1 (by rwa [hcd]) (by rwa [hcd]) (by rwa [hcd]) (by rw [hcd]; omega)
          (by rwa [hcd]) (by rwa [hcd])
      have hsub_mid : readNodeSet (l + 1) base t mem₁ u ∪ Finset.Ico (cnt + 1) cnt' ⊆
          readNodeSet (l + 1) base t x.mem u ∪ Finset.Ico cnt cnt' := by
        intro w_id hw
        rcases Finset.mem_union.mp hw with hw | hw
        · rcases Finset.mem_insert.mp (hsub_u1 hw) with rfl | hw
          · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
          · exact Finset.mem_union_left _ hw
        · have := Finset.mem_Ico.mp hw
          exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, this.2⟩)
      refine ⟨y, cnt', (hstep.loop_iter hcond_in hy_rec).mono (by omega), hby,
        by omega, by omega, hmb0.trans hm1_b0, hmb1, hby_reg, hdy_reg,
        by simpa using hmod₃.trans hmod_rec, fun w_id hnot o ho_lt => ?_, hv_u',
        hs_u', by rw [hnk_u', hnk_u1]; omega, hsub_u'.trans hsub_mid, by rw [htr_u', htr_u1]⟩
      rw [hfr_rec w_id (fun hin => hnot (hsub_mid (Finset.union_subset_union hsub_d
        subset_rfl hin))) o ho_lt]
      simp only [Finset.mem_union, Finset.mem_Ico, not_or] at hnot
      exact hframe_mem₁ w_id (fun h => hnot.1 (h ▸ hu_in_old))
        (fun h => hnot.1 (h ▸ hc_in_old)) (by omega) o ho_lt
    · simp only [hfull_c, ↓reduceIte] at hbr₃
      obtain ⟨hmem₃_eq, hcur₃, hcnt₃, hact₃⟩ := hbr₃
      have hnf_c : numKeys base t x₃.mem c ≤ 2 * t - 2 := by
        rw [hmem₃_eq]
        have := hv_c.numKeys_le
        omega
      obtain ⟨y, cnt', hy_rec, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_rec, hfr_rec, hv_c', hs_c', hnk_c_le, hsub_c', htr_c'⟩ :=
        ih hbx₃ (hmem₃_eq ▸ hv_c) (hmem₃_eq ▸ hs_c) hnf_c (hmem₃_eq ▸ hrange_c) (by omega)
          (hmem₃_eq ▸ hcnt_mem) hz₃ ho₃ hb₃ hd₃ hst₃ hk₃ hv₃ hcur₃ hcnt₃ hact₃
      rw [hmem₃_eq] at hmb0 hfr_rec hnk_c_le hsub_c' htr_c'
      have hnk_c_ge : t - 1 ≤ numKeys base t y.mem c :=
        le_trans (hc_def ▸ hv.child_numKeys_ge hslot_lt1) hnk_c_le
      obtain ⟨hv_u', hs_u', hnk_u', hsub_u', htr_u'⟩ :=
        childInsert_spec (cnt := cnt) (cnt' := cnt') ht hv hs hslot_le hsc.2.1 hgt_all hrange
          (hc_def.symm ▸ hfr_rec) (hc_def.symm ▸ hv_c') (hc_def.symm ▸ hs_c')
          (hc_def.symm ▸ hnk_c_ge) (hc_def.symm ▸ hsub_c') (hc_def.symm ▸ htr_c')
      refine ⟨y, cnt', (hstep.loop_iter hcond_in hy_rec).mono (by omega), hby,
        hcnt_le, by omega, hmb0, hmb1, hby_reg, hdy_reg,
        by simpa using hmod₃.trans hmod_rec,
        fun w_id hnot o ho_lt => hfr_rec w_id (fun hin => hnot (Finset.union_subset_union
          (hc_def ▸ child_subset_readNodeSet l base t x.mem u slot hslot_lt1) subset_rfl hin))
          o ho_lt,
        hv_u', hs_u', by rw [hnk_u'], hsub_u', htr_u'⟩

theorem not_readsWidth_insertLoop : ¬insertLoop.ReadsWidth := by
  simp [insertLoop, insertStep, insertBranch, insertDescendOrLeaf, insertDescendAfterSplit,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_loadAndScan,
    not_readsWidth_overwriteValCode, not_readsWidth_splitChildCode, not_readsWidth_leafInsertCode]

theorem isRandFree_insertLoop : insertLoop.IsRandFree := by
  simp [insertLoop, insertStep, insertBranch, insertDescendOrLeaf, insertDescendAfterSplit,
    Code.IsRandFree, isRandFree_loadAndScan, isRandFree_overwriteValCode,
    isRandFree_splitChildCode, isRandFree_leafInsertCode]

end Cslib.DataStructure.BTree.WordRAM
