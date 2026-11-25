/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.DataStructure.BTree.WordRAM.Rep
import CslibFrontier.DataStructure.BTree.WordRAM.Loops
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Word-RAM B-Tree Lookup (`O(t log_t n)`)

Root-to-leaf B-tree lookup code `lookupCode` and complete halting flat program `lookupProgram` over
`Cslib.WordRAM.Basis.standard` (`20` registers), computing `BTree.lookup k tr` in at most
`(16 * t + 21) * tr.height + 16` (`O(t log_t n)`) instructions without modifying memory while
preserving `Rep`.

## Main definitions

* `Cslib.DataStructure.BTree.WordRAM.lookupCode`: structured B-tree lookup code over
  `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.lookupProgram`: halting flat program
  (`lookupCode.program rVal`).

## Main results

* `Cslib.DataStructure.BTree.WordRAM.lookupCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.lookupCode_log_spec`,
  `Cslib.DataStructure.BTree.WordRAM.lookupProgram_spec`: `O(t * tr.height)` and `O(t log_t n)`
  Word-RAM instruction bounds for `lookupCode` and `lookupProgram`.
* `Cslib.DataStructure.BTree.WordRAM.not_readsWidth_lookupCode`,
  `Cslib.DataStructure.BTree.WordRAM.isRandFree_lookupCode`,
  `Cslib.DataStructure.BTree.WordRAM.not_readsWidth_lookupProgram`,
  `Cslib.DataStructure.BTree.WordRAM.isRandFree_lookupProgram`: width-independence and
  determinism (`rand`-freedom) certificates.
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def lookupDescendOrStop : Code .standard 20 := ram[
  rTmp1 ← rSrc - rOne;
  rTmp1 ← rTmp1 - rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rSlot;
    rCur ← *rTmp1
  ] else [
    rActive ← #0
  ] ]

private def lookupBranch : Code .standard 20 := ram[
  if rSlot < rNumK then [
    rTmp1 ← rSrc + rSlot;
    rTmp2 ← *rTmp1;
    if rTmp2 = rKey then [
      rFound ← #1;
      rTmp1 ← rSrc + rDeg;
      rTmp1 ← rTmp1 + rDeg;
      rTmp1 ← rTmp1 - rOne;
      rTmp1 ← rTmp1 + rSlot;
      rVal ← *rTmp1;
      rActive ← #0
    ] else [
      ⟪lookupDescendOrStop⟫
    ]
  ] else [
    ⟪lookupDescendOrStop⟫
  ] ]

private def lookupStep : Code .standard 20 := ram[
  ⟪loadAndScan⟫;
  ⟪lookupBranch⟫ ]

private def lookupLoop : Code .standard 20 := ram[
  while rZero < rActive do [⟪lookupStep⟫] ]

/-- Look up key `rKey` in the arena at `rBase` of minimum degree `rDeg`, setting `rFound` (`1` or
`0`) and `rVal` (found value or `0`) without modifying memory. -/
def lookupCode : Code .standard 20 := ram[
  rZero ← #0;
  rOne ← #1;
  rFound ← #0;
  rVal ← #0;
  rTmp1 ← rBase + rOne;
  rCnt ← *rTmp1;
  if rCnt = rZero then [
    rZero ← #0
  ] else [
    rStride ← rDeg + rDeg;
    rTmp1 ← rStride + rStride;
    rStride ← rStride + rTmp1;
    rCur ← *rBase;
    rActive ← #1;
    ⟪lookupLoop⟫
  ] ]

private theorem lookupDescendOrStop_spec {w base capNodes t u slot : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot ≤ 2 * t - 1)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hdeg : x.regs rDeg = t)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) (hslot_reg : x.regs rSlot = slot) :
    ∃ y, ExecWithin w lookupDescendOrStop x y 10 ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = x.regs rBase ∧ y.regs rDeg = t ∧
      y.regs rStride = x.regs rStride ∧ y.regs rKey = x.regs rKey ∧
      y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal ∧
      (if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive
      else
        y.regs rActive = 0) := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hf_au1 : Fits w (nodeAddr base t u + 2 - 1) := hfit.of_le (by omega)
  have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hsub2 : nodeAddr base t u + 2 - 1 - 1 = nodeAddr base t u := by omega
  have hlf_eq : x.mem (nodeAddr base t u) = leafFlag base t x.mem u := rfl
  by_cases hlf0 : leafFlag base t x.mem u = 0
  · have hf_t1 : Fits w (nodeAddr base t u + t) := hfit.of_le (by omega)
    have hf_t2 : Fits w (nodeAddr base t u + t + t) := hfit.of_le (by omega)
    have hf_t3 : Fits w (nodeAddr base t u + t + t + t) := hfit.of_le (by omega)
    have hf_t4 : Fits w (nodeAddr base t u + 4 * t) := hfit.of_le (by omega)
    have hf_cs : Fits w (nodeAddr base t u + 4 * t + slot) := hfit.of_le (by omega)
    have hadd4 : nodeAddr base t u + t + t + t + t = nodeAddr base t u + 4 * t := by omega
    let y : Data 20 := ?childState
    have he : ExecWithin w lookupDescendOrStop x y 10 := by
      unfold lookupDescendOrStop
      dsimp only [y]
      wram_exec [hz, ho, hdeg, hsrc, hslot_reg, hsub2, hlf_eq, hlf0, hadd4,
        hf_au1, hf_au, hf_t1, hf_t2, hf_t3, hf_t4, hf_cs]
      rfl
    refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by simp only [hlf0, ↓reduceIte]; exact ⟨rfl, by dsimp only [y]; wram_simp⟩⟩ <;>
      dsimp only [y] <;> wram_simp <;> assumption
  · let y : Data 20 := ?leafState
    have he : ExecWithin w lookupDescendOrStop x y 10 := by
      unfold lookupDescendOrStop
      dsimp only [y]
      wram_exec [hz, ho, hsrc, hsub2, hlf_eq, hlf0, hf_au1, hf_au, hf0]
      rfl
    refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [hlf0, ↓reduceIte]; rfl⟩ <;>
      dsimp only [y] <;> wram_simp <;> assumption

private theorem lookupBranch_spec {w base capNodes t u k m slot : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 1) (hslot : slot ≤ m)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hnk : x.regs rNumK = m)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) (hslot_reg : x.regs rSlot = slot) :
    ∃ y, ExecWithin w lookupBranch x y 15 ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = x.regs rBase ∧ y.regs rDeg = t ∧
      y.regs rStride = x.regs rStride ∧ y.regs rKey = k ∧
      (if slot < m ∧ keyAt base t x.mem u slot = k then
        y.regs rFound = 1 ∧ y.regs rVal = valAt base t x.mem u slot ∧ y.regs rActive = 0
      else if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive ∧
          y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal
      else
        y.regs rActive = 0 ∧ y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal) := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  by_cases hlt_m : slot < m
  · have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
    have hks_eq : x.mem (nodeAddr base t u + 2 + slot) = keyAt base t x.mem u slot := rfl
    by_cases heq_k : keyAt base t x.mem u slot = k
    · have hf1 : Fits w 1 := hfit.of_le (by omega)
      have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      have hf_v1 : Fits w (nodeAddr base t u + 2 + t) := hfit.of_le (by omega)
      have hf_v2 : Fits w (nodeAddr base t u + 2 + t + t) := hfit.of_le (by omega)
      have hf_v3 : Fits w (nodeAddr base t u + (2 * t + 1)) := hfit.of_le (by omega)
      have hf_vs : Fits w (nodeAddr base t u + (2 * t + 1) + slot) := hfit.of_le (by omega)
      have hv_arith : nodeAddr base t u + 2 + t + t - 1 = nodeAddr base t u + (2 * t + 1) := by
        omega
      have hvs_eq : x.mem (nodeAddr base t u + (2 * t + 1) + slot) = valAt base t x.mem u slot :=
        rfl
      let y : Data 20 := ?hitState
      have he : ExecWithin w lookupBranch x y 15 := by
        unfold lookupBranch
        dsimp only [y]
        wram_exec [ho, hdeg, hkey, hnk, hsrc, hslot_reg, hlt_m, hks_eq, heq_k, hv_arith, hvs_eq,
          hf_ks, hf1, hf0, hf_v1, hf_v2, hf_v3, hf_vs]
        rfl
      refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      on_goal 7 => simp only [hlt_m, heq_k, and_self, ↓reduceIte]; refine ⟨?_, ?_, rfl⟩
      all_goals dsimp only [y]; wram_simp
      all_goals assumption
    · let x' := (x.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 (keyAt base t x.mem u slot)
      obtain ⟨y, hdesc, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hfnd_y, hval_y, hbr⟩ :=
        lookupDescendOrStop_spec (x := x') ht hu_cap (by omega) hfit hz ho hdeg hsrc hslot_reg
      have he : ExecWithin w lookupBranch x y 15 := by
        unfold lookupBranch
        apply WP.execWithin
        wram_exec [hnk, hsrc, hslot_reg, hkey, hlt_m, hks_eq, heq_k, hf_ks]
        exact WP.of_execWithin hdesc ⟨by omega, rfl⟩
      refine ⟨y, he, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y.trans hkey, ?_⟩
      simp only [hlt_m, heq_k, and_false, ↓reduceIte]
      change (if leafFlag base t x'.mem u = 0 then _ else _) at hbr
      dsimp only [x'] at hbr hb_y hst_y hfnd_y hval_y
      wram_simp at hbr hb_y hst_y hfnd_y hval_y
      split_ifs at hbr ⊢
      · exact ⟨hbr.1, hbr.2, hfnd_y, hval_y⟩
      · exact ⟨hbr, hfnd_y, hval_y⟩
  · obtain ⟨y, hdesc, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hfnd_y, hval_y, hbr⟩ :=
      lookupDescendOrStop_spec (x := x) ht hu_cap (by omega) hfit hz ho hdeg hsrc hslot_reg
    have he : ExecWithin w lookupBranch x y 15 := by
      unfold lookupBranch
      apply WP.execWithin
      wram_exec [hnk, hslot_reg, hlt_m]
      exact WP.of_execWithin hdesc ⟨by omega, rfl⟩
    refine ⟨y, he, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y.trans hkey, ?_⟩
    simp only [hlt_m, false_and, ↓reduceIte]
    split_ifs at hbr ⊢
    · exact ⟨hbr.1, hbr.2, hfnd_y, hval_y⟩
    · exact ⟨hbr, hfnd_y, hval_y⟩

private theorem lookupStep_spec {w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : numKeys base t x.mem u ≤ 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k) (hcur : x.regs rCur = u) :
    let m := numKeys base t x.mem u
    let slot := slotCount base t x.mem u k m
    ∃ y, ExecWithin w lookupStep x y (16 * t + 19) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧
      y.regs rStride = 6 * t ∧ y.regs rKey = k ∧
      (if slot < m ∧ keyAt base t x.mem u slot = k then
        y.regs rFound = 1 ∧ y.regs rVal = valAt base t x.mem u slot ∧ y.regs rActive = 0
      else if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive ∧
          y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal
      else
        y.regs rActive = 0 ∧ y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal) := by
  set m := numKeys base t x.mem u
  set slot := slotCount base t x.mem u k m
  have hslot_le := slotCount_le base t x.mem u k m
  obtain ⟨x₂, h12, _, hmem₂, hz₂, ho₂, hb₂_reg, hd₂, hst₂, hk₂, _, hsrc₂, hnk₂, hslot₂, hreg₂⟩ :=
    loadAndScan_spec ht hu_cap hm_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
  have hact₂ : x₂.regs rActive = x.regs rActive := hreg₂ rActive (by decide)
  have hfnd₂ : x₂.regs rFound = x.regs rFound := hreg₂ rFound (by decide)
  have hval₂ : x₂.regs rVal = x.regs rVal := hreg₂ rVal (by decide)
  obtain ⟨y, h3, hmem₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hbr₃⟩ :=
    lookupBranch_spec ht hu_cap hm_le hslot_le hfit hz₂ ho₂ hd₂ hk₂ hnk₂ hsrc₂ hslot₂
  have hfull : ExecWithin w lookupStep x y (16 * t + 19) :=
    (h12.seq h3).mono (by omega)
  rw [hmem₂] at hbr₃
  rw [hact₂, hfnd₂, hval₂] at hbr₃
  exact ⟨y, hfull, hfull.bounded hbdd, hmem₃.trans hmem₂, hz₃, ho₃, hb₃.trans hb₂_reg, hd₃,
    hst₃.trans hst₂, hk₃, hbr₃⟩

/-- A lookup step that clears `rActive` ends the descent loop after one iteration. -/
private theorem lookupLoop_of_stop {w t l : ℕ} {x y : Data 20}
    (hstep : ExecWithin w lookupStep x y (16 * t + 19))
    (hz : x.regs rZero = 0) (hact : x.regs rActive = 1)
    (hz_y : y.regs rZero = 0) (hact_y : y.regs rActive = 0) :
    ExecWithin w lookupLoop x y ((16 * t + 21) * (l + 1) + 2) := by
  have := Nat.le_mul_of_pos_right (16 * t + 21) (by omega : 0 < l + 1)
  exact (hstep.loop_iter (by simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one])
    (ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y, hact_y, Nat.lt_irrefl,
      not_false_eq_true]))).mono (by omega)

private theorem lookupLoop_spec {l w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u) (hs : SortedNode l base t x.mem u)
    (hcap : readNodeSet l base t x.mem u ⊆ Finset.range capNodes)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k)
    (hcur : x.regs rCur = u) (hact : x.regs rActive = 1)
    (hfound0 : x.regs rFound = 0) (hval0 : x.regs rVal = 0) :
    ∃ y, ExecWithin w lookupLoop x y ((16 * t + 21) * (l + 1) + 2) ∧
      y.mem = x.mem ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      y.regs rFound = (if (BTree.lookup k (readTree l base t x.mem u)).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k (readTree l base t x.mem u)).getD 0 := by
  induction l using Nat.strongRecOn generalizing u x with
  | ind l ih =>
    have hu_cap : u < capNodes :=
      Finset.mem_range.mp (hcap (self_mem_readNodeSet l base t x.mem u))
    obtain ⟨x₁, hstep, hb₁, hmem₁, hz₁, ho₁, hb₁_reg, hd₁, hst₁, hk₁, hbr⟩ :=
      lookupStep_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    set m := numKeys base t x.mem u
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · simp only [hhit] at hbr
      obtain ⟨hfnd₁, hval₁, hact₁⟩ := hbr
      have hlk := lookup_readTree_eq_some hs hhit.1 hhit.2
      refine ⟨x₁, lookupLoop_of_stop hstep hz hact hz₁ hact₁, hmem₁, hb₁_reg, hd₁, ?_, ?_⟩
      · rw [hlk, hfnd₁]; rfl
      · rw [hlk, hval₁]; rfl
    · have hgt_all := keyAt_gt_of_slotCount_not_hit (fun _ _ => hs.keys_strict) hhit
      rcases l with _ | l
      · have hlf_ne : leafFlag base t x.mem u ≠ 0 := by simp [hv.leafFlag_eq]
        simp only [hhit, hlf_ne, ↓reduceIte] at hbr
        obtain ⟨hact₁, hfnd₁, hval₁⟩ := hbr
        have hne_all : ∀ i < m, keyAt base t x.mem u i ≠ k := fun i hi =>
          (lt_or_ge i slot).elim (fun hlt => (hsc.2.1 i hlt).ne) fun hge => (hgt_all i hge hi).ne'
        have hlk := lookup_readTree_leaf_none hs hne_all
        refine ⟨x₁, lookupLoop_of_stop hstep hz hact hz₁ hact₁, hmem₁, hb₁_reg, hd₁, ?_, ?_⟩
        · rw [hlk, hfnd₁, hfound0]; rfl
        · rw [hlk, hval₁, hval0]; rfl
      · simp only [hhit, hv.leafFlag_eq, Nat.succ_ne_zero, ↓reduceIte] at hbr
        obtain ⟨hcur₁, hact₁, hfnd₁, hval₁⟩ := hbr
        have hslot_lt1 : slot < m + 1 := Nat.lt_succ_of_le hsc.1
        have hv_c : ValidNode l base t x₁.mem (childAt base t x.mem u slot) :=
          hmem₁ ▸ hv.child_valid hslot_lt1
        have hs_c : SortedNode l base t x₁.mem (childAt base t x.mem u slot) :=
          hmem₁ ▸ hs.child_sorted hslot_lt1
        have hcap_c : readNodeSet l base t x₁.mem (childAt base t x.mem u slot) ⊆
            Finset.range capNodes := by
          rw [hmem₁]
          exact (child_subset_readNodeSet l base t x.mem u slot hslot_lt1).trans hcap
        obtain ⟨y, hy_rec, hmem_y, hb_y, hd_y, hfnd_y, hval_y⟩ :=
          ih l (Nat.lt_succ_self l) hb₁ hv_c hs_c hcap_c hz₁ ho₁ hb₁_reg hd₁ hst₁ hk₁ hcur₁
            (hact₁.trans hact) (hfnd₁.trans hfound0) (hval₁.trans hval0)
        have hcond_in : (Cond.lt rZero rActive).Holds x := by
          simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
        have hlk := lookup_readTree_succ_eq_child hs hsc.1 hsc.2.1 hgt_all
        have : (16 * t + 21) * (l + 1 + 1) = (16 * t + 21) * (l + 1) + (16 * t + 21) :=
          Nat.mul_succ _ _
        rw [hmem₁] at hfnd_y hval_y
        refine ⟨y, (hstep.loop_iter hcond_in hy_rec).mono (by omega), hmem_y.trans hmem₁,
          hb_y, hd_y, ?_, ?_⟩
        · rwa [hlk]
        · rwa [hlk]

/-- `lookupCode` evaluates `BTree.lookup k tr` in at most `(16 * t + 21) * tr.height + 16`
standard Word-RAM instructions without modifying memory, preserving `Rep`. -/
theorem lookupCode_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y, ExecWithin w lookupCode x y ((16 * t + 21) * tr.height + 16) ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  have hfit := hr.fits_arena
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  rcases hr.tree_spec with ⟨hcnt0, rfl⟩ | ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩
  · let y : Data 20 := ?emptyState
    have he : ExecWithin w lookupCode x y 9 := by
      unfold lookupCode
      dsimp only [y]
      wram_exec [hr.base_eq, hcnt0, hf0, hf1, hf_b1]
      rfl
    have hrep : Rep base capNodes t w .leaf y := by
      refine ⟨he.bounded hr.bounded, hr.two_le, ?_, ?_, hfit, hr.cnt_le_cap, Or.inl ⟨hcnt0, rfl⟩⟩
      · dsimp only [y]; wram_simp; exact hr.base_eq
      · dsimp only [y]; wram_simp; exact hr.deg_eq
    refine ⟨y, he.mono (by omega), hrep, rfl, ?_, ?_⟩
    · simp only [BTree.lookup_leaf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      dsimp only [y]; wram_simp
    · simp only [BTree.lookup_leaf, Option.getD_none]
      dsimp only [y]; wram_simp
  · have hcap1 : 1 ≤ capNodes := by have := hr.cnt_le_cap; omega
    have hst_le := stride_le_arena (base := base) (t := t) hcap1
    have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
    have hf_4t : Fits w ((t + t) + (t + t)) := hfit.of_le (by omega)
    have hf_6t : Fits w (6 * t) := hfit.of_le hst_le
    have h6t : (t + t) + ((t + t) + (t + t)) = 6 * t := by omega
    have hcnt_ne : x.mem (base + 1) ≠ 0 := by omega
    let x₀ : Data 20 :=
      ((((((((((x.set rZero 0).set rOne 1).set rFound 0).set rVal 0).set rTmp1
        (base + 1)).set rCnt (x.mem (base + 1))).set rStride (t + t)).set rTmp1
        ((t + t) + (t + t))).set rStride (6 * t)).set rCur (x.mem base)).set rActive 1
    have hcap_sub : readNodeSet l base t x₀.mem (x.mem base) ⊆ Finset.range capNodes :=
      hrange.trans (Finset.range_mono hr.cnt_le_cap)
    obtain ⟨y, hloop, hmem_y, hb_y, hd_y, hfnd_y, hval_y⟩ :=
      lookupLoop_spec (x := x₀) (k := k) hr.two_le
        (((((((((((hr.bounded.set hf0).set hf1).set hf0).set hf0).set hf_b1).set
          (hr.bounded.2 _)).set hf_2t).set hf_4t).set hf_6t).set (hr.bounded.2 _)).set hf1)
        hfit hv hs hcap_sub rfl rfl
        (by dsimp only [x₀]; wram_simp; exact hr.base_eq)
        (by dsimp only [x₀]; wram_simp; exact hr.deg_eq)
        rfl
        (by dsimp only [x₀]; wram_simp; exact hkey)
        rfl rfl rfl rfl
    have he : ExecWithin w lookupCode x y ((16 * t + 21) * (l + 1) + 16) := by
      unfold lookupCode
      apply WP.execWithin
      wram_exec [hr.base_eq, hr.deg_eq, hcnt_ne, h6t, hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t]
      exact WP.of_execWithin hloop ⟨by omega, rfl⟩
    have hh_eq : (readTree l base t x.mem (x.mem base)).height = l + 1 :=
      hv.balanced_and_height.2
    have hrep : Rep base capNodes t w (readTree l base t x.mem (x.mem base)) y :=
      ⟨he.bounded hr.bounded, hr.two_le, hb_y, hd_y, hfit,
        by rw [hmem_y]; exact hr.cnt_le_cap,
        by rw [hmem_y]; exact Or.inr ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩⟩
    exact ⟨y, hh_eq ▸ he, hrep, hmem_y, hfnd_y, hval_y⟩

/-- Logarithmic `O(t log_t n)` Word-RAM instruction bound for `lookupCode`. -/
theorem lookupCode_log_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y, ExecWithin w lookupCode x y
        ((16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 16) ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  obtain ⟨y, he, hrep, hmem, hfnd, hval⟩ := lookupCode_spec hr hkey
  have hle := Nat.mul_le_mul_left (16 * t + 21) hr.height_le_log
  exact ⟨y, he.mono (by omega), hrep, hmem, hfnd, hval⟩

/-- Complete flat Word-RAM lookup program (`lookupCode` followed by `halt rVal`). -/
def lookupProgram : Program .standard 20 := lookupCode.program rVal

/-- `lookupCode` does not read the runtime word width `w`. -/
theorem not_readsWidth_lookupCode : ¬lookupCode.ReadsWidth := by
  simp [lookupCode, lookupLoop, lookupStep, lookupBranch, lookupDescendOrStop,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_loadAndScan]

/-- `lookupCode` is deterministic (`rand`-free). -/
theorem isRandFree_lookupCode : lookupCode.IsRandFree := by
  simp [lookupCode, lookupLoop, lookupStep, lookupBranch, lookupDescendOrStop,
    Code.IsRandFree, isRandFree_loadAndScan]

/-- `lookupProgram` does not read the runtime word width `w`. -/
theorem not_readsWidth_lookupProgram : ¬lookupProgram.ReadsWidth :=
  Code.not_readsWidth_program not_readsWidth_lookupCode rVal

/-- `lookupProgram` is deterministic (`rand`-free). -/
theorem isRandFree_lookupProgram : lookupProgram.IsRandFree :=
  Code.isRandFree_program.mpr isRandFree_lookupCode

/-- Complete halting flat-program specification of `lookupProgram`: runs in at most
`(16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 17` Word-RAM instructions (charging the
final `halt`), halting with `(BTree.lookup k tr).getD 0` in `rVal`, the hit/miss bit in `rFound`
(distinguishing `some 0` from `none`), unchanged memory `y.mem = x.mem`, and preserved `Rep`. -/
theorem lookupProgram_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y steps,
      Runs w lookupProgram ⟨0, x⟩ ⟨lookupCode.size, y⟩ steps ∧
      step w lookupProgram ⟨lookupCode.size, y⟩ = .halt ((BTree.lookup k tr).getD 0) ∧
      steps + 1 ≤ (16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 17 ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  obtain ⟨y, ⟨steps, hle, hexec⟩, hrep, hmem, hfnd, hval⟩ := lookupCode_log_spec hr hkey
  have hruns : Runs w lookupProgram ⟨0, x⟩ ⟨lookupCode.size, y⟩ steps := by
    simpa only [Nat.zero_add] using
      hexec.runs (pc := 0) (p := lookupProgram) (Program.Contains.self _).append_left
  have hhalt : step w lookupProgram ⟨0 + lookupCode.size, y⟩ = .halt (y.regs rVal) :=
    step_halt (by simp [lookupProgram, Code.program])
  rw [Nat.zero_add, hval] at hhalt
  exact ⟨y, steps, hruns, hhalt, by omega, hrep, hmem, hfnd, hval⟩

end Cslib.DataStructure.BTree.WordRAM
