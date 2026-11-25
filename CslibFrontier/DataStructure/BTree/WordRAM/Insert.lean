/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.DataStructure.BTree.WordRAM.Rep
import CslibFrontier.DataStructure.BTree.WordRAM.InsertLoop
import CslibFrontier.DataStructure.BTree.WordRAM.LeafInsert
import CslibFrontier.DataStructure.BTree.WordRAM.Loops
import CslibFrontier.DataStructure.BTree.WordRAM.SplitRoot
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Word-RAM B-Tree Proactive Top-Down Insertion (`O(t log_t n)`)

Proactive top-down B-tree insertion code `insertCode` and halting flat program `insertProgram` over
`Cslib.WordRAM.Basis.standard` (`20` registers), following [CLRS2009], Section 18.2: splits a full
root via `splitRootCode` and descends through non-full nodes via `insertLoop`, realizing
`Cslib.SortedAssoc.insert k v tr.toList` in `O(t log_t n)` Word-RAM instructions while preserving
`Rep` (`BTree.IsWF t`) and outside memory.

## Main definitions

* `Cslib.DataStructure.BTree.WordRAM.insertCode`: structured proactive top-down B-tree insertion
  code over `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.insertProgram`: halting flat program
  (`insertCode.program rBase`).

## Main results

* `Cslib.DataStructure.BTree.WordRAM.insertCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.insertCode_log_spec`,
  `Cslib.DataStructure.BTree.WordRAM.insertProgram_spec`: `O(t * (tr.height + 1))` and
  `O(t log_t n)` Word-RAM instruction bounds, `Rep` preservation, `SortedAssoc.insert` correctness,
  node-allocation bound, and memory framing for `insertCode` and `insertProgram`.
* `Cslib.DataStructure.BTree.WordRAM.not_readsWidth_insertCode`,
  `Cslib.DataStructure.BTree.WordRAM.isRandFree_insertCode`,
  `Cslib.DataStructure.BTree.WordRAM.not_readsWidth_insertProgram`,
  `Cslib.DataStructure.BTree.WordRAM.isRandFree_insertProgram`: width-independence and
  determinism (`rand`-freedom) certificates.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 18.2][CLRS2009]
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

/-- Insert `(rKey, rVal)` into the B-tree arena at `rBase` of minimum degree `rDeg` using proactive
top-down node splitting ([CLRS2009], Section 18.2). -/
def insertCode : Code .standard 20 := ram[
  rZero ← #0;
  rOne ← #1;
  rTmp1 ← rBase + rOne;
  rCnt ← *rTmp1;
  if rCnt = rZero then [
    ⟪initSingleCode⟫
  ] else [
    rStride ← rDeg + rDeg;
    rTmp1 ← rStride + rStride;
    rStride ← rStride + rTmp1;
    rChild ← *rBase;
    rTmp1 ← rChild * rStride;
    rTmp1 ← rBase + rTmp1;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rNumK ← *rTmp1;
    rTmp1 ← rDeg + rDeg;
    rTmp1 ← rTmp1 - rOne;
    if rNumK = rTmp1 then [
      ⟪splitRootCode⟫
    ] else [
      rCur ← rChild
    ];
    rActive ← #1;
    ⟪insertLoop⟫
  ] ]

/-- `insertCode` inserts `(k, v)` into `tr` in at most
`(91 * t + 160) * (tr.height + 1) + (21 * t + 120)` standard Word-RAM instructions, preserving
`Rep` (`BTree.IsWF t tr'`), realizing `Cslib.SortedAssoc.insert k v tr.toList`, allocating at most
`tr.height + 2` arena nodes, and modifying only `[base, base + arenaWords t capNodes)`. -/
theorem insertCode_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr',
      ExecWithin w insertCode x y ((91 * t + 160) * (tr.height + 1) + (21 * t + 120)) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  dsimp only [allocCount] at hcap ⊢
  have ht := hr.two_le
  have hfit := hr.fits_arena
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  rcases hr.tree_spec with ⟨hcnt0, rfl⟩ | ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩
  · let x₀ := (((x.set rZero 0).set rOne 1).set rTmp1 (base + 1)).set rCnt 0
    obtain ⟨y, his, hby, hymem, hmod, hb_y, hd_y⟩ :=
      initSingleCode_spec (x := x₀) (k := k) (v := v) ht (by omega)
        ((((hr.bounded.set hf0).set hf1).set hf_b1).set hf0) hfit rfl rfl
        ((by dsimp only [x₀]; wram_simp : x₀.regs rBase = _).trans hr.base_eq)
        ((by dsimp only [x₀]; wram_simp : x₀.regs rDeg = _).trans hr.deg_eq)
        ((by dsimp only [x₀]; wram_simp : x₀.regs rKey = _).trans hkey)
        ((by dsimp only [x₀]; wram_simp : x₀.regs rVal = _).trans hval)
    have he : ExecWithin w insertCode x y ((91 * t + 160) * ((.leaf : BTree ℕ ℕ).height + 1) +
        (21 * t + 120)) := by
      unfold insertCode
      apply WP.execWithin
      wram_exec [hr.base_eq, hcnt0, hf0, hf1, hf_b1]
      exact WP.of_execWithin his ⟨by omega, rfl⟩
    simp only [x₀, Data.set_mem] at hymem hmod
    obtain ⟨hb0_s, hb1_s, hv_s, hs_s, htl_s, hset_s⟩ := memInitSingle_spec (base := base)
      (k := k) (v := v) ht x.mem
    have hrep : Rep base capNodes t w (readTree 0 base t y.mem 0) y :=
      ⟨hby, ht, hb_y, hd_y, hfit, by rw [hymem, hb1_s]; omega,
        .inr ⟨by rw [hymem, hb1_s]; omega, 0, by rw [hymem, hb0_s],
          by rw [hymem, hb0_s]; exact hv_s,
          by rw [hymem, hb0_s]; exact hs_s,
          fun _ hw => by
            rw [hymem, hb0_s, hset_s] at hw
            rw [hymem, hb1_s]; simp_all⟩⟩
    exact ⟨y, readTree 0 base t y.mem 0, he, hrep, by rw [hymem, htl_s]; rfl,
      by rw [hymem, hb1_s]; omega, hmod⟩
  · obtain ⟨cnt, hcnt_def⟩ : ∃ cnt, x.mem (base + 1) = cnt := ⟨_, rfl⟩
    obtain ⟨oldRoot, holdRoot_def⟩ : ∃ oldRoot, x.mem base = oldRoot := ⟨_, rfl⟩
    rw [hcnt_def] at hcnt_pos hrange hcap
    rw [holdRoot_def] at hv hs hrange hcap ⊢
    have hh_eq : (readTree l base t x.mem oldRoot).height = l + 1 := hv.balanced_and_height.2
    have hcap' : cnt + (l + 1) + 2 ≤ capNodes := hh_eq ▸ hcap
    have hcnt_ne : cnt ≠ 0 := by omega
    have hr_lt_cnt : oldRoot < cnt :=
      Finset.mem_range.mp (hrange (self_mem_readNodeSet l base t x.mem oldRoot))
    have hcap1 : 1 ≤ capNodes := by omega
    have hst_le := stride_le_arena (base := base) (t := t) hcap1
    have har_old := nodeAddr_add_le_arena (base := base) (u := oldRoot)
      (by omega : oldRoot < capNodes) (o := 6 * t) le_rfl
    have hnk_old_eq : x.mem (nodeAddr base t oldRoot + 1) = numKeys base t x.mem oldRoot := rfl
    have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
    have hf_4t : Fits w ((t + t) + (t + t)) := hfit.of_le (by omega)
    have hf_6t : Fits w (6 * t) := hfit.of_le hst_le
    have hf_rmul : Fits w (oldRoot * (6 * t)) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb0 : Fits w (base + oldRoot * (6 * t)) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb1 : Fits w (base + oldRoot * (6 * t) + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb2 : Fits w (base + oldRoot * (6 * t) + 1 + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb3 : Fits w (base + oldRoot * (6 * t) + 1 + 1 + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_ar1 : Fits w (nodeAddr base t oldRoot + 1) := hfit.of_le (by omega)
    have hf_2tm10 : Fits w (t + t - 1) := hfit.of_le (by omega)
    have hf_2tm1 : Fits w (2 * t - 1) := hfit.of_le (by omega)
    have h6t : (t + t) + ((t + t) + (t + t)) = 6 * t := by omega
    have hna_r1 : base + oldRoot * (6 * t) + 1 + 1 + 1 = nodeAddr base t oldRoot + 1 := by
      simp only [nodeAddr, nodeStride]; omega
    have h2tm1_eq : t + t - 1 = 2 * t - 1 := by omega
    let x₁ : Data 20 :=
      (((((((((((((((x.set rZero 0).set rOne 1).set rTmp1 (base + 1)).set rCnt cnt).set rStride
        (t + t)).set rTmp1 ((t + t) + (t + t))).set rStride (6 * t)).set rChild oldRoot).set rTmp1
        (oldRoot * (6 * t))).set rTmp1 (base + oldRoot * (6 * t))).set rTmp1
        (base + oldRoot * (6 * t) + 1)).set rTmp1
        (base + oldRoot * (6 * t) + 1 + 1)).set rTmp1
        (nodeAddr base t oldRoot + 1)).set rNumK (numKeys base t x.mem oldRoot)).set rTmp1
        (t + t)).set rTmp1 (2 * t - 1)
    have hbx₁ : x₁.Bounded w := by
      dsimp only [x₁]
      exact (((((((((((((((hr.bounded.set hf0).set hf1).set hf_b1).set
        (hcnt_def ▸ hr.bounded.2 _)).set
        hf_2t).set hf_4t).set hf_6t).set (holdRoot_def ▸ hr.bounded.2 _)).set hf_rmul).set
        hf_rb0).set hf_rb1).set hf_rb2).set hf_ar1).set (hr.bounded.2 _)).set hf_2t).set hf_2tm1
    by_cases hfull_r : numKeys base t x.mem oldRoot = 2 * t - 1
    · obtain ⟨x₂, hsr, hbx₂, hmem_x₂, hmod_sr, hz_x₂, ho_x₂, hb_x₂, hd_x₂, hst_x₂,
          hk_x₂, hv_x₂, hcur_x₂, hcnt_x₂⟩ :=
        splitRootCode_spec (x := x₁) (oldRoot := oldRoot) (cnt := cnt)
          ht hr_lt_cnt (by rw [hh_eq] at hcap; omega) hbx₁ hfit
          rfl rfl
          ((by dsimp only [x₁]; wram_simp : x₁.regs rBase = _).trans hr.base_eq)
          ((by dsimp only [x₁]; wram_simp : x₁.regs rDeg = _).trans hr.deg_eq)
          rfl rfl rfl
      simp only [x₁, Data.set_mem] at hmem_x₂ hmod_sr
      dsimp only [x₁] at hk_x₂ hv_x₂
      wram_simp at hk_x₂ hv_x₂
      obtain ⟨hmr_b0, hmr_b1, hv_r1, hs_r1, hnk_r1, hrange_r1, htr_r1⟩ :=
        memSplitRoot_spec ht hv hs hfull_r hrange
      let x₃ := x₂.set rActive 1
      have hnf_r1 : numKeys base t x₃.mem (cnt + 1) ≤ 2 * t - 2 := by
        change numKeys base t x₂.mem (cnt + 1) ≤ 2 * t - 2
        rw [hmem_x₂, hnk_r1]; omega
      obtain ⟨y, cnt', hloop, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_loop, _, hv_y, hs_y, _, hsub_y, htr_y⟩ :=
        insertLoop_spec (x := x₃) (l := l + 1) (u := cnt + 1) (cnt := cnt + 2) (k := k) (v := v) ht
          (hbx₂.set hf1) hfit
          (by change ValidNode _ _ _ x₂.mem _; rwa [hmem_x₂])
          (by change SortedNode _ _ _ x₂.mem _; rwa [hmem_x₂])
          hnf_r1
          (by change readNodeSet _ _ _ x₂.mem _ ⊆ _; rwa [hmem_x₂])
          (by rw [hh_eq] at hcap; omega)
          (by change x₂.mem (base + 1) = cnt + 2; rw [hmem_x₂, hmr_b1])
          hz_x₂ ho_x₂ hb_x₂ hd_x₂ hst_x₂ (hk_x₂.trans hkey) (hv_x₂.trans hval)
          hcur_x₂ hcnt_x₂ rfl
      have he : ExecWithin w insertCode x y
          ((91 * t + 160) * ((readTree l base t x.mem oldRoot).height + 1) + (21 * t + 120)) := by
        rw [hh_eq]
        unfold insertCode
        apply WP.execWithin
        wram_exec [hr.base_eq, hr.deg_eq, hcnt_def, holdRoot_def, hnk_old_eq,
          hcnt_ne, h6t, hna_r1, h2tm1_eq, hfull_r,
          hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t,
          hf_rmul, hf_rb0, hf_rb1, hf_rb2, hf_rb3, hf_ar1, hf_2tm10, hf_2tm1]
        dsimp only [x₁] at hsr
        rw [hfull_r] at hsr
        refine WP.of_execWithin hsr ?_
        wram_exec [hf1]
        exact WP.of_execWithin hloop ⟨by omega, rfl⟩
      have hy_b0 : y.mem base = cnt + 1 := by
        rw [hmb0]
        change x₂.mem base = cnt + 1; rw [hmem_x₂, hmr_b0]
      have hrange_y : readNodeSet (l + 1) base t y.mem (cnt + 1) ⊆ Finset.range cnt' :=
        fun w_id hwin => Finset.mem_range.mpr <| by
          rcases Finset.mem_union.mp (hsub_y hwin) with hold | hico
          · change w_id ∈ readNodeSet (l + 1) base t x₂.mem (cnt + 1) at hold
            have := Finset.mem_range.mp (hrange_r1 (hmem_x₂ ▸ hold)); omega
          · exact (Finset.mem_Ico.mp hico).2
      have hrep : Rep base capNodes t w (readTree (l + 1) base t y.mem (cnt + 1)) y :=
        ⟨hby, ht, hby_reg, hdy_reg, hfit, by rw [hmb1]; omega,
          .inr ⟨by rw [hmb1]; omega, l + 1, by rw [hy_b0],
            by rw [hy_b0]; exact hv_y,
            by rw [hy_b0]; exact hs_y,
            by rw [hy_b0, hmb1]; exact hrange_y⟩⟩
      simp only [x₃, Data.set_mem] at hmod_loop htr_y
      exact ⟨y, readTree (l + 1) base t y.mem (cnt + 1), he, hrep,
        by rw [htr_y, hmem_x₂, htr_r1], by rw [hmb1, hh_eq]; omega,
        by simpa only [Finset.union_idempotent] using hmod_sr.trans hmod_loop⟩
    · let x₂ := (x₁.set rCur oldRoot).set rActive 1
      have hnf_r : numKeys base t x₂.mem oldRoot ≤ 2 * t - 2 := by
        have := hv.numKeys_le
        simp only [x₂, x₁, Data.set_mem]; omega
      obtain ⟨y, cnt', hloop, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_loop, _, hv_y, hs_y, _, hsub_y, htr_y⟩ :=
        insertLoop_spec (x := x₂) (l := l) (u := oldRoot) (cnt := cnt) (k := k) (v := v) ht
          ((hbx₁.set (holdRoot_def ▸ hr.bounded.2 _)).set hf1) hfit
          (by simpa only [x₂, x₁, Data.set_mem] using hv)
          (by simpa only [x₂, x₁, Data.set_mem] using hs) hnf_r
          (by simpa only [x₂, x₁, Data.set_mem] using hrange)
          (by omega)
          (by simp only [x₂, x₁, Data.set_mem, hcnt_def])
          rfl rfl
          ((by dsimp only [x₂, x₁]; wram_simp : x₂.regs rBase = _).trans hr.base_eq)
          ((by dsimp only [x₂, x₁]; wram_simp : x₂.regs rDeg = _).trans hr.deg_eq) rfl
          ((by dsimp only [x₂, x₁]; wram_simp : x₂.regs rKey = _).trans hkey)
          ((by dsimp only [x₂, x₁]; wram_simp : x₂.regs rVal = _).trans hval) rfl rfl rfl
      simp only [x₂, x₁, Data.set_mem] at hmb0 hmod_loop hsub_y htr_y
      have he : ExecWithin w insertCode x y
          ((91 * t + 160) * ((readTree l base t x.mem oldRoot).height + 1) + (21 * t + 120)) := by
        rw [hh_eq]
        unfold insertCode; apply WP.execWithin
        wram_exec [hr.base_eq, hr.deg_eq, hcnt_def, holdRoot_def, hnk_old_eq,
          hcnt_ne, h6t, hna_r1, h2tm1_eq, hfull_r,
          hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t,
          hf_rmul, hf_rb0, hf_rb1, hf_rb2, hf_rb3, hf_ar1, hf_2tm10, hf_2tm1]
        exact WP.of_execWithin hloop
          ⟨by have := Nat.mul_le_mul_left (91 * t + 160) (Nat.le_add_right (l + 1) 1); omega, rfl⟩
      have hy_b0 : y.mem base = oldRoot := hmb0.trans holdRoot_def
      have hrange_y : readNodeSet l base t y.mem oldRoot ⊆ Finset.range cnt' :=
        fun w_id hwin => Finset.mem_range.mpr <| by
          rcases Finset.mem_union.mp (hsub_y hwin) with hold | hico
          · have := Finset.mem_range.mp (hrange hold); omega
          · exact (Finset.mem_Ico.mp hico).2
      have hrep : Rep base capNodes t w (readTree l base t y.mem oldRoot) y :=
        ⟨hby, ht, hby_reg, hdy_reg, hfit, by rw [hmb1]; omega,
          .inr ⟨by rw [hmb1]; omega, l, by rw [hy_b0],
            by rw [hy_b0]; exact hv_y,
            by rw [hy_b0]; exact hs_y,
            by rw [hy_b0, hmb1]; exact hrange_y⟩⟩
      exact ⟨y, readTree l base t y.mem oldRoot, he, hrep, htr_y,
        by rw [hmb1, hh_eq]; omega, hmod_loop⟩

/-- Logarithmic `O(t log_t n)` Word-RAM instruction bound for `insertCode`. -/
theorem insertCode_log_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr',
      ExecWithin w insertCode x y
        ((91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 120)) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  obtain ⟨y, tr', he, hrep, htl, hcnt, hmod⟩ := insertCode_spec hr hkey hval hcap
  have h2 : tr.height + 1 ≤ Nat.log t ((tr.size + 1) / 2) + 2 := by
    have := hr.height_le_log; omega
  have hle := Nat.mul_le_mul_left (91 * t + 160) h2
  exact ⟨y, tr', he.mono (by omega), hrep, htl, hcnt, hmod⟩

/-- Complete flat Word-RAM insertion program (`insertCode` followed by `halt rBase`). -/
def insertProgram : Program .standard 20 := insertCode.program rBase

/-- `insertCode` does not read the runtime word width `w`. -/
theorem not_readsWidth_insertCode : ¬insertCode.ReadsWidth := by
  simp [insertCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_initSingleCode,
    not_readsWidth_splitRootCode, not_readsWidth_insertLoop]

/-- `insertCode` is deterministic (`rand`-free). -/
theorem isRandFree_insertCode : insertCode.IsRandFree := by
  simp [insertCode, Code.IsRandFree, isRandFree_initSingleCode,
    isRandFree_splitRootCode, isRandFree_insertLoop]

/-- `insertProgram` does not read the runtime word width `w`. -/
theorem not_readsWidth_insertProgram : ¬insertProgram.ReadsWidth :=
  Code.not_readsWidth_program not_readsWidth_insertCode rBase

/-- `insertProgram` is deterministic (`rand`-free). -/
theorem isRandFree_insertProgram : insertProgram.IsRandFree :=
  Code.isRandFree_program.mpr isRandFree_insertCode

/-- Complete halting flat-program specification of `insertProgram`: runs in at most
`(91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 121)` Word-RAM instructions
(charging the final `halt`), halting with `base` in `rBase` while preserving `Rep` on `tr'` with
`tr'.toList = Cslib.SortedAssoc.insert k v tr.toList`, bounding node allocation, and modifying only
`[base, base + arenaWords t capNodes)`. -/
theorem insertProgram_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr' steps,
      Runs w insertProgram ⟨0, x⟩ ⟨insertCode.size, y⟩ steps ∧
      step w insertProgram ⟨insertCode.size, y⟩ = .halt base ∧
      steps + 1 ≤ (91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 121) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  obtain ⟨y, tr', ⟨steps, hle, hexec⟩, hrep, htl, hcnt, hmod⟩ :=
    insertCode_log_spec hr hkey hval hcap
  have hruns : Runs w insertProgram ⟨0, x⟩ ⟨insertCode.size, y⟩ steps := by
    simpa only [Nat.zero_add] using
      hexec.runs (pc := 0) (p := insertProgram) (Program.Contains.self _).append_left
  have hhalt : step w insertProgram ⟨0 + insertCode.size, y⟩ = .halt (y.regs rBase) :=
    step_halt (by simp [insertProgram, Code.program])
  rw [Nat.zero_add, hrep.base_eq] at hhalt
  exact ⟨y, tr', steps, hruns, hhalt, by omega, hrep, htl, hcnt, hmod⟩

end Cslib.DataStructure.BTree.WordRAM
