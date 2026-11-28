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
# Proactive Full-Child Split Subprogram (`splitChildCode`)

Internal Word-RAM subroutine used privately by `InsertLoop` (never re-exported publicly by
`CslibFrontier.DataStructure.BTree.WordRAM`): splits a full `(2 * t - 1)`-key child `c` of a
non-full internal parent `u` at child index `slot`, shifting parent keys/values/children and
promoting the median key into `u` (`memSplitChild`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def splitChildPre1 : Code .standard 20 := ram[
  rSrc ← rCur * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rDst ← rNumK;
  rLim ← rNumK - rSlot ]

private def splitChildPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne ]

private def splitChildPre3 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne;
  rDst ← rNumK + rOne ]

private def splitChildPost : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rDst ← rCur * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rLim ← rDeg - rOne;
  rTmp1 ← rSrc + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rTmp2;
  rTmp1 ← rSrc + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rTmp2;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rSlot;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rCnt;
  rNumK ← rNumK + rOne;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rNumK;
  rCnt ← rCnt + rOne;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rCnt ]

private def splitChildShifts : Code .standard 20 := ram[
  ⟪splitChildPre1⟫;
  ⟪shiftLoop⟫;
  ⟪splitChildPre2⟫;
  ⟪shiftLoop⟫;
  ⟪splitChildPre3⟫;
  ⟪shiftLoop⟫ ]

/-- Split full child `rChild = c` of non-full internal parent `rCur = u` at child slot `rSlot`
(`memSplitChild`). -/
def splitChildCode : Code .standard 20 := ram[
  ⟪copyUpperCode⟫;
  ⟪splitChildShifts⟫;
  ⟪splitChildPost⟫ ]

private theorem splitChildPost_spec {w base capNodes t u m slot c cnt : ℕ}
    {mem₀ : ℕ → ℕ} {x₇ : Data 20}
    (ht : 2 ≤ t) (hu_lt : u < cnt) (hc_lt : c < cnt) (hcap : cnt + 1 ≤ capNodes)
    (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz₇ : x₇.regs rZero = 0) (ho₇ : x₇.regs rOne = 1)
    (hb₇_reg : x₇.regs rBase = base) (hd₇ : x₇.regs rDeg = t)
    (hst₇ : x₇.regs rStride = 6 * t)
    (hcur₇ : x₇.regs rCur = u) (hnk₇ : x₇.regs rNumK = m)
    (hsl₇ : x₇.regs rSlot = slot) (hch₇ : x₇.regs rChild = c) (hcnt₇ : x₇.regs rCnt = cnt)
    (hk_med : x₇.mem (nodeAddr base t c + 2 + (t - 1)) = keyAt base t mem₀ c (t - 1))
    (hv_med : x₇.mem (nodeAddr base t c + (2 * t + 1) + (t - 1)) = valAt base t mem₀ c (t - 1))
    (hsep_uc : nodeAddr base t u + 6 * t ≤ nodeAddr base t c ∨
      nodeAddr base t c + 6 * t ≤ nodeAddr base t u)
    (hmem₇_eq : x₇.mem =
      let au := nodeAddr base t u
      let m1 := memCopyUpper base t c cnt mem₀
      let m2 := shiftArrRight (au + 2) m (m - slot) m1
      let m3 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m2
      shiftArrRight (au + 4 * t) (m + 1) (m - slot) m3) :
    ∃ y, ExecWithin w splitChildPost x₇ y 40 ∧
      y.mem = memSplitChild base t u m slot c cnt mem₀ ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x₇.regs rKey ∧ y.regs rVal = x₇.regs rVal ∧
      y.regs rActive = x₇.regs rActive ∧
      y.regs rCur = u ∧ y.regs rSlot = slot ∧ y.regs rChild = c ∧
      y.regs rNumK = m + 1 ∧ y.regs rCnt = cnt + 1 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) (u := u) (by omega : u < capNodes)
      (o := 6 * t) le_rfl
  have hac_le : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) (u := c) (by omega : c < capNodes)
      (o := 6 * t) le_rfl
  rw [hau_def, hac_def] at hsep_uc
  rw [hac_def] at hk_med hv_med
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hna_c : base + c * (6 * t) + 1 + 1 = ac := by
    rw [← hac_def]; simp only [nodeAddr, nodeStride]; omega
  have hcap_le : capNodes ≤ capNodes * nodeStride t :=
    Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_au2' : Fits w (au + 1 + 1) := hfit.of_le (by omega)
  have hf_auks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
  have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf_aut3 : Fits w (au + t + t + t) := hfit.of_le (by omega)
  have hf_aut4 : Fits w (au + t + t + t + t) := hfit.of_le (by omega)
  have hf_au4t : Fits w (au + 4 * t) := hfit.of_le (by omega)
  have hf_aucs : Fits w (au + 4 * t + slot) := hfit.of_le (by omega)
  have hf_aucs10 : Fits w (au + 4 * t + slot + 1) := hfit.of_le (by omega)
  have hf_aucs1 : Fits w (au + 4 * t + (slot + 1)) := hfit.of_le (by omega)
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_cb2 : Fits w (base + c * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_ac : Fits w ac := hfit.of_le (by omega)
  have hf_ac1 : Fits w (ac + 1) := hfit.of_le (by omega)
  have hf_ac2 : Fits w (ac + 1 + 1) := hfit.of_le (by omega)
  have hf_ack0 : Fits w (ac + 1 + 1 + (t - 1)) := hfit.of_le (by omega)
  have hf_ack : Fits w (ac + 2 + (t - 1)) := hfit.of_le (by omega)
  have hf_act1 : Fits w (ac + t) := hfit.of_le (by omega)
  have hf_act2 : Fits w (ac + t + t) := hfit.of_le (by omega)
  have hf_act21 : Fits w (ac + t + t + 1) := hfit.of_le (by omega)
  have hf_ac2t1 : Fits w (ac + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_acv : Fits w (ac + (2 * t + 1) + (t - 1)) := hfit.of_le (by omega)
  have hf_tm1 : Fits w (t - 1) := hfit.of_le (by omega)
  have hf_m1 : Fits w (m + 1) := hfit.of_le (by omega)
  have hf_cnt1 : Fits w (cnt + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hack_eq : ac + 1 + 1 + (t - 1) = ac + 2 + (t - 1) := by omega
  have hau2_eq : au + 1 + 1 = au + 2 := by omega
  have h2tc_eq : ac + t + t + 1 = ac + (2 * t + 1) := by omega
  have h2tu_eq : au + t + t + 1 = au + (2 * t + 1) := by omega
  have h4tu_eq : au + t + t + t + t = au + 4 * t := by omega
  have hcs1_eq : au + 4 * t + slot + 1 = au + 4 * t + (slot + 1) := by omega
  have hv_ne_ks : ac + (2 * t + 1) + (t - 1) ≠ au + 2 + slot := by omega
  unfold splitChildPost
  apply WP.exists_execWithin
  wram_exec [ho₇, hb₇_reg, hd₇, hst₇, hcur₇, hnk₇, hsl₇, hch₇, hcnt₇,
    hna_c, hna_u, hack_eq, hau2_eq, h2tc_eq, h2tu_eq, h4tu_eq, hcs1_eq,
    hv_ne_ks, hk_med, hv_med,
    hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac, hf_ac1, hf_ac2, hf_ack0, hf_ack,
    hf_act1, hf_act2, hf_act21, hf_ac2t1, hf_acv,
    hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au2, hf_au2', hf_auks,
    hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf_aut3, hf_aut4, hf_au4t,
    hf_aucs, hf_aucs10, hf_aucs1, hf_tm1, hf_m1, hf_cnt1, hf_b1]
  wram_simp [hz₇, ho₇, hb₇_reg, hd₇, hst₇, hcur₇, hsl₇, hch₇]
  simp only [memSplitChild, hau_def, hmem₇_eq]

private theorem splitChildShifts_spec {w base capNodes t u m slot : ℕ} {x₁ : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hb₁ : x₁.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho₁ : x₁.regs rOne = 1) (hb₁_reg : x₁.regs rBase = base) (hd₁ : x₁.regs rDeg = t)
    (hst₁ : x₁.regs rStride = 6 * t) (hcur₁ : x₁.regs rCur = u)
    (hnk₁ : x₁.regs rNumK = m) (hsl₁ : x₁.regs rSlot = slot) :
    ∃ x₇, ExecWithin w splitChildShifts x₁ x₇ (54 * t + 24) ∧
      x₇.Bounded w ∧
      x₇.mem =
        (let au := nodeAddr base t u
         let m2 := shiftArrRight (au + 2) m (m - slot) x₁.mem
         let m3 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m2
         shiftArrRight (au + 4 * t) (m + 1) (m - slot) m3) ∧
      ∀ reg : Fin 20,
        reg ∉ ([rSrc, rDst, rLim, rIdx, rTmp1, rTmp2] : List (Fin 20)) →
          x₇.regs reg = x₁.regs reg := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_ms : Fits w (m - slot) := hfit.of_le (by omega)
  let x₂ : Data 20 :=
    (((((((x₁.set rSrc (u * (6 * t))).set rSrc (base + u * (6 * t))).set rSrc
      (base + u * (6 * t) + 1)).set rSrc au).set rSrc (au + 1)).set rSrc
      (au + 2)).set rDst m).set rLim (m - slot)
  have hp1 : ExecWithin w splitChildPre1 x₁ x₂ 8 := by
    dsimp only [x₂]
    wram_exec [splitChildPre1, ho₁, hb₁_reg, hst₁, hcur₁, hnk₁, hsl₁, hna_u,
      hf_umul, hf_ub0, hf_ub1, hf_au, hf_au1, hf_au2, hf_ms]
  obtain ⟨x₃, hs1, hb₃, hmem₃, hreg₃⟩ :=
    shiftLoop_spec (arrBase := au + 2) (upper := m) (count := m - slot)
      (hp1.bounded hb₁) ho₁ rfl rfl rfl (by omega) (hfit.of_le (by omega))
  have hsrc₃ : x₃.regs rSrc = au + 2 := hreg₃ rSrc (by decide)
  have hdst₃ : x₃.regs rDst = m := hreg₃ rDst (by decide)
  have hlim₃ : x₃.regs rLim = m - slot := hreg₃ rLim (by decide)
  have ho₃ : x₃.regs rOne = 1 := (hreg₃ rOne (by decide)).trans ho₁
  have hd₃ : x₃.regs rDeg = t := (hreg₃ rDeg (by decide)).trans hd₁
  have hav_eq : au + 2 + t + t - 1 = au + (2 * t + 1) := by omega
  let x₄ : Data 20 :=
    ((x₃.set rSrc (au + 2 + t)).set rSrc (au + 2 + t + t)).set rSrc (au + (2 * t + 1))
  have hp2 : ExecWithin w splitChildPre2 x₃ x₄ 3 := by
    unfold splitChildPre2; dsimp only [x₄]
    have hf1 : Fits w (au + 2 + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + 2 + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [ho₃, hd₃, hsrc₃, hav_eq, hf1, hf2, hf3]
  obtain ⟨x₅, hs2, hb₅, hmem₅, hreg₅⟩ :=
    shiftLoop_spec (arrBase := au + (2 * t + 1)) (upper := m) (count := m - slot)
      (hp2.bounded hb₃) ho₃ rfl hdst₃ hlim₃ (by omega) (hfit.of_le (by omega))
  have hsrc₅ : x₅.regs rSrc = au + (2 * t + 1) := hreg₅ rSrc (by decide)
  have hlim₅ : x₅.regs rLim = m - slot := (hreg₅ rLim (by decide)).trans hlim₃
  have ho₅ : x₅.regs rOne = 1 := (hreg₅ rOne (by decide)).trans ho₃
  have hd₅ : x₅.regs rDeg = t := (hreg₅ rDeg (by decide)).trans hd₃
  have hnk₅ : x₅.regs rNumK = m :=
    (hreg₅ rNumK (by decide)).trans ((hreg₃ rNumK (by decide)).trans hnk₁)
  have hac4_eq : au + (2 * t + 1) + t + t - 1 = au + 4 * t := by omega
  let x₆ : Data 20 :=
    (((x₅.set rSrc (au + (2 * t + 1) + t)).set rSrc (au + (2 * t + 1) + t + t)).set rSrc
      (au + 4 * t)).set rDst (m + 1)
  have hp3 : ExecWithin w splitChildPre3 x₅ x₆ 4 := by
    unfold splitChildPre3; dsimp only [x₆]
    have hf1 : Fits w (au + (2 * t + 1) + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + (2 * t + 1) + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + 4 * t) := hfit.of_le (by omega)
    have hf4 : Fits w (m + 1) := hfit.of_le (by omega)
    wram_exec [ho₅, hd₅, hsrc₅, hnk₅, hac4_eq, hf1, hf2, hf3, hf4]
  obtain ⟨x₇, hs3, hb₇, hmem₇, hreg₇⟩ :=
    shiftLoop_spec (arrBase := au + 4 * t) (upper := m + 1) (count := m - slot)
      (hp3.bounded hb₅) ho₅ rfl rfl hlim₅ (by omega) (hfit.of_le (by omega))
  simp only [x₂, Data.set_mem] at hmem₃
  simp only [x₄, Data.set_mem] at hmem₅
  simp only [x₆, Data.set_mem] at hmem₇
  have he : ExecWithin w splitChildShifts x₁ x₇ (54 * t + 24) :=
    (hp1.seq (hs1.seq (hp2.seq (hs2.seq (hp3.seq hs3))))).mono (by omega)
  refine ⟨x₇, he, hb₇, by simp only [hau_def, ← hmem₃, ← hmem₅, ← hmem₇], fun reg hnot => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnot
  have hnot3 : reg ∉ ([rIdx, rTmp1, rTmp2] : List (Fin 20)) := by simp [h4, h5, h6]
  rw [hreg₇ reg hnot3]
  dsimp only [x₆]; simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _]
  rw [hreg₅ reg hnot3]
  dsimp only [x₄]; simp only [Data.set_regs_of_ne h1 _]
  rw [hreg₃ reg hnot3]
  dsimp only [x₂]; simp only [Data.set_regs_of_ne h3 _, Data.set_regs_of_ne h2 _,
    Data.set_regs_of_ne h1 _]

/-- Specification of `splitChildCode`, realizing `memSplitChild base t u m slot c cnt` in
`75 * t + 115` instructions. -/
theorem splitChildCode_spec {w base capNodes t u m slot c cnt : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_lt : u < cnt) (hc_lt : c < cnt) (huc : u ≠ c) (hcap : cnt + 1 ≤ capNodes)
    (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hcur : x.regs rCur = u) (hnk : x.regs rNumK = m)
    (hslot_reg : x.regs rSlot = slot) (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = cnt) :
    ∃ y, ExecWithin w splitChildCode x y (75 * t + 115) ∧
      y.Bounded w ∧
      y.mem = memSplitChild base t u m slot c cnt x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
      y.regs rActive = x.regs rActive ∧
      y.regs rCur = u ∧ y.regs rSlot = slot ∧ y.regs rChild = c ∧
      y.regs rNumK = m + 1 ∧ y.regs rCnt = cnt + 1 := by
  have hsep_raw : nodeAddr base t u + 6 * t ≤ nodeAddr base t c ∨
      nodeAddr base t c + 6 * t ≤ nodeAddr base t u := nodeAddr_sep base t huc
  have hsep_cz : nodeAddr base t c + 6 * t ≤ nodeAddr base t cnt := by
    have hmul : (c + 1) * nodeStride t ≤ cnt * nodeStride t := Nat.mul_le_mul_right _ hc_lt
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  obtain ⟨x₁, he1, hb₁, hmem₁, _, hz₁, hkeep₁⟩ :=
    copyUpperCode_spec ht (by omega) (by omega) (by omega) hbdd hfit hz0 ho hbase hdeg hstride
      hchild hcnt
  obtain ⟨x₇, hshifts, _, hmem₇, hreg₇⟩ :=
    splitChildShifts_spec ht (by omega : u < capNodes) hm_le hslot hb₁ hfit
      ((hkeep₁ rOne (by decide)).trans ho)
      ((hkeep₁ rBase (by decide)).trans hbase)
      ((hkeep₁ rDeg (by decide)).trans hdeg)
      ((hkeep₁ rStride (by decide)).trans hstride)
      ((hkeep₁ rCur (by decide)).trans hcur)
      ((hkeep₁ rNumK (by decide)).trans hnk)
      ((hkeep₁ rSlot (by decide)).trans hslot_reg)
  have hmem₇_eq : x₇.mem =
      let au' := nodeAddr base t u
      let m1 := memCopyUpper base t c cnt x.mem
      let m2 := shiftArrRight (au' + 2) m (m - slot) m1
      let m3 := shiftArrRight (au' + (2 * t + 1)) m (m - slot) m2
      shiftArrRight (au' + 4 * t) (m + 1) (m - slot) m3 := by
    rw [hmem₇, hmem₁]
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hsep_uc : au + 6 * t ≤ ac ∨ ac + 6 * t ≤ au := by
    rw [← hau_def, ← hac_def]; exact hsep_raw
  have hk_med : x₇.mem (nodeAddr base t c + 2 + (t - 1)) = keyAt base t x.mem c (t - 1) := by
    rw [hmem₇_eq]; dsimp only
    rw [hau_def, hac_def,
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    dsimp only [keyAt]; rw [← hac_def]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_cz (2 + (t - 1)) (by omega) (by omega) x.mem
  have hv_med :
      x₇.mem (nodeAddr base t c + (2 * t + 1) + (t - 1)) = valAt base t x.mem c (t - 1) := by
    rw [hmem₇_eq]; dsimp only
    rw [hau_def, hac_def,
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    dsimp only [valAt]; rw [← hac_def]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_cz (2 * t + (1 + (t - 1))) (by omega) (by omega) x.mem
  obtain ⟨y, hp4, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hact_y, hcur_y, hsl_y,
      hch_y, hnk_y, hcnt_y⟩ :=
    splitChildPost_spec ht hu_lt hc_lt hcap hm_le hslot hfit
      ((hreg₇ rZero (by decide)).trans hz₁)
      ((hreg₇ rOne (by decide)).trans ((hkeep₁ rOne (by decide)).trans ho))
      ((hreg₇ rBase (by decide)).trans ((hkeep₁ rBase (by decide)).trans hbase))
      ((hreg₇ rDeg (by decide)).trans ((hkeep₁ rDeg (by decide)).trans hdeg))
      ((hreg₇ rStride (by decide)).trans ((hkeep₁ rStride (by decide)).trans hstride))
      ((hreg₇ rCur (by decide)).trans ((hkeep₁ rCur (by decide)).trans hcur))
      ((hreg₇ rNumK (by decide)).trans ((hkeep₁ rNumK (by decide)).trans hnk))
      ((hreg₇ rSlot (by decide)).trans ((hkeep₁ rSlot (by decide)).trans hslot_reg))
      ((hreg₇ rChild (by decide)).trans ((hkeep₁ rChild (by decide)).trans hchild))
      ((hreg₇ rCnt (by decide)).trans ((hkeep₁ rCnt (by decide)).trans hcnt))
      hk_med hv_med hsep_raw hmem₇_eq
  have hfull : ExecWithin w splitChildCode x y (75 * t + 115) :=
    (he1.seq (hshifts.seq hp4)).mono (by omega)
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    have hb_lo_u := base_lt_nodeAddr base t u 0
    have hb_lo_c := base_lt_nodeAddr base t c 0
    have hb_lo_z := base_lt_nodeAddr base t cnt 0
    have hau_le := nodeAddr_add_le_arena (base := base) (u := u) (by omega : u < capNodes)
      (o := 6 * t) le_rfl
    have hac_le := nodeAddr_add_le_arena (base := base) (u := c) (by omega : c < capNodes)
      (o := 6 * t) le_rfl
    have haz_le := nodeAddr_add_le_arena (base := base) (u := cnt) (by omega : cnt < capNodes)
      (o := 6 * t) le_rfl
    apply memSplitChild_outside ht hm_le hslot
    · intro heq; apply hnot
      simp only [Block.mem_footprint, Block.Owns, arenaWords]; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in hau_le ⊢; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in hac_le ⊢; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in haz_le ⊢; omega
  exact ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, hz_y, ho_y, hb_y, hd_y, hst_y,
    hk_y.trans ((hreg₇ rKey (by decide)).trans (hkeep₁ rKey (by decide))),
    hv_y.trans ((hreg₇ rVal (by decide)).trans (hkeep₁ rVal (by decide))),
    hact_y.trans ((hreg₇ rActive (by decide)).trans (hkeep₁ rActive (by decide))),
    hcur_y, hsl_y, hch_y, hnk_y, hcnt_y⟩

/-- Parent keys strictly before `slot` are unchanged by `memSplitChild`. -/
theorem keyAt_memSplitChild_lt {base t u m slot c cnt i : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (huc : u ≠ c) (huz : u ≠ cnt) (hi : i < slot) :
    keyAt base t (memSplitChild base t u m slot c cnt mem) u i = keyAt base t mem u i := by
  have hb_k := base_lt_nodeAddr base t u (2 + i)
  have hsu := nodeAddr_sep base t huc
  have hsz := nodeAddr_sep base t huz
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  simp only [nodeStride, hau_def, hac_def, haz_def] at hb_k hsu hsz
  dsimp only [keyAt, memSplitChild]
  simp only [hau_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
  exact memCopyUpper_outside ht mem _ (by rw [hac_def]; simp only [nodeStride]; omega)
    (by rw [haz_def]; simp only [nodeStride]; omega)

/-- Parent keys strictly after `slot` shift right by `1` under `memSplitChild`. -/
theorem keyAt_memSplitChild_gt {base t u m slot c cnt i : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (huc : u ≠ c) (huz : u ≠ cnt) (hge : slot + 1 ≤ i) (hi : i < m + 1) :
    keyAt base t (memSplitChild base t u m slot c cnt mem) u i = keyAt base t mem u (i - 1) := by
  have hb_k := base_lt_nodeAddr base t u (2 + i)
  have hsu := nodeAddr_sep base t huc
  have hsz := nodeAddr_sep base t huz
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  simp only [nodeStride, hau_def, hac_def, haz_def] at hb_k hsu hsz
  dsimp only [keyAt, memSplitChild]
  simp only [hau_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_shifted (au + 2) m (m - slot) _ (by omega) i (by omega) (by omega)]
  exact memCopyUpper_outside ht mem _ (by rw [hac_def]; simp only [nodeStride]; omega)
    (by rw [haz_def]; simp only [nodeStride]; omega)

theorem not_readsWidth_splitChildCode : ¬splitChildCode.ReadsWidth := by
  simp [splitChildCode, splitChildShifts, splitChildPre1, splitChildPre2, splitChildPre3,
    splitChildPost, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_copyUpperCode,
    not_readsWidth_shiftLoop]

theorem isRandFree_splitChildCode : splitChildCode.IsRandFree := by
  simp [splitChildCode, splitChildShifts, splitChildPre1, splitChildPre2, splitChildPre3,
    splitChildPost, Code.IsRandFree, isRandFree_copyUpperCode, isRandFree_shiftLoop]

end Cslib.DataStructure.BTree.WordRAM
