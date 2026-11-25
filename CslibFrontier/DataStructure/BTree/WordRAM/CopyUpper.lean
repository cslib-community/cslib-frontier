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
# Upper-Half Node Copy Subprogram (`copyUpperCode`)

Internal Word-RAM subroutine shared privately by `SplitRoot` and `SplitChild` (never re-exported
publicly by `CslibFrontier.DataStructure.BTree.WordRAM`): moves the upper `t - 1` keys/values (and
upper `t` child pointers when internal) of a full `(2 * t - 1)`-key node `c` into a fresh sibling
node `z` (`memCopyUpper`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

private def copyUpperPre1 : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rDeg;
  rDst ← rCnt * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rLim ← rDeg - rOne ]

private def copyUpperPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rLim;
  rSrc ← rSrc + rDeg;
  rDst ← rDst + rLim;
  rDst ← rDst + rDeg ]

private def copyUpperBranch : Code .standard 20 := ram[
  rTmp1 ← rChild * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rSrc ← rSrc + rLim;
    rSrc ← rSrc + rDeg;
    rDst ← rDst + rLim;
    rDst ← rDst + rDeg;
    rLim ← rDeg;
    ⟪copyArrayCode⟫
  ] else [
    rZero ← #0
  ] ]

private def copyUpperPost : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rTmp2 ← *rSrc;
  rDst ← rCnt * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  *rDst ← rTmp2;
  rLim ← rDeg - rOne;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rLim;
  rTmp1 ← rSrc + rOne;
  *rTmp1 ← rLim ]

/-- Copy the upper half of full node `rChild` into newly allocated sibling `rCnt` (`memCopyUpper`).
-/
def copyUpperCode : Code .standard 20 := ram[
  ⟪copyUpperPre1⟫;
  ⟪copyArrayCode⟫;
  ⟪copyUpperPre2⟫;
  ⟪copyArrayCode⟫;
  ⟪copyUpperBranch⟫;
  ⟪copyUpperPost⟫ ]

/-- Specification of `copyUpperCode`, realizing `memCopyUpper base t c z` in `21 * t + 48`
instructions. -/
theorem copyUpperCode_spec {w base capNodes t c z : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hc_cap : c < capNodes) (hz_cap : z < capNodes) (hcz : c ≠ z)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = z) :
    ∃ y, ExecWithin w copyUpperCode x y (21 * t + 48) ∧
      y.Bounded w ∧
      y.mem = memCopyUpper base t c z x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧
      ∀ reg : Fin 20,
        reg ∉ ([rSrc, rDst, rLim, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
          y.regs reg = x.regs reg := by
  have hac_le := nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
  have haz_le := nodeAddr_add_le_arena (base := base) hz_cap (o := 6 * t) le_rfl
  have hsep : nodeAddr base t c + 6 * t ≤ nodeAddr base t z ∨
      nodeAddr base t z + 6 * t ≤ nodeAddr base t c := nodeAddr_sep base t hcz
  have hna_c : base + c * (6 * t) + 1 + 1 = nodeAddr base t c := by
    simp only [nodeAddr, nodeStride]; omega
  have hna_z : base + z * (6 * t) + 1 + 1 = nodeAddr base t z := by
    simp only [nodeAddr, nodeStride]; omega
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_ac : Fits w (nodeAddr base t c) := hfit.of_le (by omega)
  have hf_ac1 : Fits w (nodeAddr base t c + 1) := hfit.of_le (by omega)
  have hf_ac2 : Fits w (nodeAddr base t c + 2) := hfit.of_le (by omega)
  have hf_ac2t : Fits w (nodeAddr base t c + 2 + t) := hfit.of_le (by omega)
  have hf_zmul : Fits w (z * (6 * t)) := hfit.of_le (by omega)
  have hf_zb0 : Fits w (base + z * (6 * t)) := hfit.of_le (by omega)
  have hf_zb1 : Fits w (base + z * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_az : Fits w (nodeAddr base t z) := hfit.of_le (by omega)
  have hf_az1 : Fits w (nodeAddr base t z + 1) := hfit.of_le (by omega)
  have hf_az2 : Fits w (nodeAddr base t z + 2) := hfit.of_le (by omega)
  have hf_tm1 : Fits w (t - 1) := hfit.of_le (by omega)
  -- Step 1: `copyUpperPre1` + `copyArrayCode` (keys)
  let x₁ : Data 20 :=
    (((((((((((((x.set rSrc (c * (6 * t))).set rSrc (base + c * (6 * t))).set rSrc
      (base + c * (6 * t) + 1)).set rSrc (nodeAddr base t c)).set rSrc
      (nodeAddr base t c + 1)).set rSrc (nodeAddr base t c + 2)).set rSrc
      (nodeAddr base t c + 2 + t)).set rDst (z * (6 * t))).set rDst
      (base + z * (6 * t))).set rDst (base + z * (6 * t) + 1)).set rDst
      (nodeAddr base t z)).set rDst (nodeAddr base t z + 1)).set rDst
      (nodeAddr base t z + 2)).set rLim (t - 1)
  have he1 : ExecWithin w copyUpperPre1 x x₁ 14 := by
    unfold copyUpperPre1
    dsimp only [x₁]
    wram_exec [ho, hbase, hdeg, hstride, hchild, hcnt, hna_c, hna_z,
      hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_ac1, hf_ac2, hf_ac2t,
      hf_zmul, hf_zb0, hf_zb1, hf_az, hf_az1, hf_az2, hf_tm1]
  obtain ⟨x₂, hc1, hb₂, hmem₂, hreg₂⟩ :=
    copyArrayCode_spec (srcBase := nodeAddr base t c + 2 + t)
      (dstBase := nodeAddr base t z + 2) (N := t - 1)
      (he1.bounded hbdd) ho rfl rfl rfl
      (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
  -- Step 2: `copyUpperPre2` + `copyArrayCode` (values)
  have hsrc₂ : x₂.regs rSrc = nodeAddr base t c + 2 + t := hreg₂ rSrc (by decide)
  have hdst₂ : x₂.regs rDst = nodeAddr base t z + 2 := hreg₂ rDst (by decide)
  have hlim₂ : x₂.regs rLim = t - 1 := hreg₂ rLim (by decide)
  have ho₂ : x₂.regs rOne = 1 := (hreg₂ rOne (by decide)).trans ho
  have hd₂ : x₂.regs rDeg = t := (hreg₂ rDeg (by decide)).trans hdeg
  have hv_c_eq : nodeAddr base t c + 2 + t + (t - 1) + t =
      nodeAddr base t c + (2 * t + 1) + t := by omega
  have hv_z_eq : nodeAddr base t z + 2 + (t - 1) + t =
      nodeAddr base t z + (2 * t + 1) := by omega
  let x₃ : Data 20 :=
    (((x₂.set rSrc (nodeAddr base t c + 2 + t + (t - 1))).set rSrc
      (nodeAddr base t c + (2 * t + 1) + t)).set rDst
      (nodeAddr base t z + 2 + (t - 1))).set rDst (nodeAddr base t z + (2 * t + 1))
  have he2 : ExecWithin w copyUpperPre2 x₂ x₃ 4 := by
    unfold copyUpperPre2
    dsimp only [x₃]
    have hf_s1 : Fits w (nodeAddr base t c + 2 + t + (t - 1)) := hfit.of_le (by omega)
    have hf_s2 : Fits w (nodeAddr base t c + (2 * t + 1) + t) := hfit.of_le (by omega)
    have hf_d1 : Fits w (nodeAddr base t z + 2 + (t - 1)) := hfit.of_le (by omega)
    have hf_d2 : Fits w (nodeAddr base t z + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [hsrc₂, hdst₂, hlim₂, hd₂, hv_c_eq, hv_z_eq, hf_s1, hf_s2, hf_d1, hf_d2]
  obtain ⟨x₄, hc2, hb₄, hmem₄, hreg₄⟩ :=
    copyArrayCode_spec (srcBase := nodeAddr base t c + (2 * t + 1) + t)
      (dstBase := nodeAddr base t z + (2 * t + 1)) (N := t - 1)
      (he2.bounded hb₂) ho₂ rfl rfl hlim₂
      (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
  have hkeep₄ : ∀ reg : Fin 20,
      reg ∉ ([rSrc, rDst, rLim, rIdx, rTmp1, rTmp2] : List (Fin 20)) →
        x₄.regs reg = x.regs reg := by
    intro reg hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hs1, hd1, hl1, hi1, ht1, ht2⟩ := hnot
    have hnot3 : reg ∉ ([rIdx, rTmp1, rTmp2] : List (Fin 20)) := by simp [hi1, ht1, ht2]
    rw [hreg₄ reg hnot3]
    dsimp only [x₃]
    simp only [Data.set_regs_of_ne hd1 _, Data.set_regs_of_ne hs1 _]
    rw [hreg₂ reg hnot3]
    dsimp only [x₁]
    simp only [Data.set_regs_of_ne hl1 _, Data.set_regs_of_ne hd1 _, Data.set_regs_of_ne hs1 _]
  have hlf₄ : x₄.mem (nodeAddr base t c) = x.mem (nodeAddr base t c) := by
    rw [hmem₄]; simp only [x₃, Data.set_mem]
    rw [ArrayCopy.copyPrefix_outside (by omega), hmem₂]; simp only [x₁, Data.set_mem]
    exact ArrayCopy.copyPrefix_outside (by omega)
  have hz₄ : x₄.regs rZero = 0 := (hkeep₄ rZero (by decide)).trans hz0
  have ho₄ : x₄.regs rOne = 1 := (hkeep₄ rOne (by decide)).trans ho
  have hb₄_reg : x₄.regs rBase = base := (hkeep₄ rBase (by decide)).trans hbase
  have hd₄ : x₄.regs rDeg = t := (hkeep₄ rDeg (by decide)).trans hdeg
  have hst₄ : x₄.regs rStride = 6 * t := (hkeep₄ rStride (by decide)).trans hstride
  have hch₄ : x₄.regs rChild = c := (hkeep₄ rChild (by decide)).trans hchild
  have hcnt₄ : x₄.regs rCnt = z := (hkeep₄ rCnt (by decide)).trans hcnt
  have hsrc₄ : x₄.regs rSrc = nodeAddr base t c + (2 * t + 1) + t := hreg₄ rSrc (by decide)
  have hdst₄ : x₄.regs rDst = nodeAddr base t z + (2 * t + 1) := hreg₄ rDst (by decide)
  have hlim₄ : x₄.regs rLim = t - 1 := (hreg₄ rLim (by decide)).trans hlim₂
  -- Step 3: `copyUpperBranch`
  have hmem₃_step : ∃ x₅, ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) ∧
      x₅.Bounded w ∧
      x₅.mem = (if x.mem (nodeAddr base t c) = 0 then
        ArrayCopy.copyPrefix x₄.mem (nodeAddr base t c + 4 * t + t) (nodeAddr base t z + 4 * t) t
      else x₄.mem) ∧
      x₅.regs rZero = 0 ∧
      ∀ reg : Fin 20,
        reg ∉ ([rSrc, rDst, rLim, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
          x₅.regs reg = x.regs reg := by
    by_cases hlf0 : x.mem (nodeAddr base t c) = 0
    · have hc_c_eq : nodeAddr base t c + (2 * t + 1) + t + (t - 1) + t =
          nodeAddr base t c + 4 * t + t := by omega
      have hc_z_eq : nodeAddr base t z + (2 * t + 1) + (t - 1) + t =
          nodeAddr base t z + 4 * t := by omega
      have hf_s1 : Fits w (nodeAddr base t c + (2 * t + 1) + t + (t - 1)) := hfit.of_le (by omega)
      have hf_s2 : Fits w (nodeAddr base t c + 4 * t + t) := hfit.of_le (by omega)
      have hf_d1 : Fits w (nodeAddr base t z + (2 * t + 1) + (t - 1)) := hfit.of_le (by omega)
      have hf_d2 : Fits w (nodeAddr base t z + 4 * t) := hfit.of_le (by omega)
      have hf_t : Fits w t := hfit.of_le (by omega)
      let x₄' : Data 20 :=
        (((((((((x₄.set rTmp1 (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
          (base + c * (6 * t) + 1)).set rTmp1 (nodeAddr base t c)).set rTmp2 0).set rSrc
          (nodeAddr base t c + (2 * t + 1) + t + (t - 1))).set rSrc
          (nodeAddr base t c + 4 * t + t)).set rDst
          (nodeAddr base t z + (2 * t + 1) + (t - 1))).set rDst
          (nodeAddr base t z + 4 * t)).set rLim t
      obtain ⟨x₅, hc3, hb₅, hmem₅, hreg₅⟩ :=
        copyArrayCode_spec (x := x₄') (srcBase := nodeAddr base t c + 4 * t + t)
          (dstBase := nodeAddr base t z + 4 * t) (N := t)
          ((((((((((hb₄.set hf_cmul).set hf_cb0).set hf_cb1).set hf_ac).set
            (hfit.of_le (Nat.zero_le _))).set hf_s1).set hf_s2).set hf_d1).set hf_d2).set hf_t)
          ho₄ rfl rfl rfl (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
      have he3 : ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) := by
        unfold copyUpperBranch
        apply WP.execWithin
        wram_exec [hz₄, ho₄, hb₄_reg, hd₄, hst₄, hch₄, hsrc₄, hdst₄, hlim₄,
          hna_c, hlf₄, hlf0, hc_c_eq, hc_z_eq,
          hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_s1, hf_s2, hf_d1, hf_d2, hf_t]
        exact WP.of_execWithin hc3 ⟨by omega, rfl⟩
      refine ⟨x₅, he3, hb₅, ?_, ?_, fun reg hnot => ?_⟩
      · simp only [hlf0, ↓reduceIte]; exact hmem₅
      · rw [hreg₅ rZero (by decide)]; exact hz₄
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
        obtain ⟨hs1, hd1, hl1, hi1, ht1, ht2, _⟩ := hnot
        rw [hreg₅ reg (by simp [hi1, ht1, ht2])]
        dsimp only [x₄']
        simp only [Data.set_regs_of_ne hl1 _, Data.set_regs_of_ne hd1 _,
          Data.set_regs_of_ne hs1 _, Data.set_regs_of_ne ht2 _, Data.set_regs_of_ne ht1 _]
        exact hkeep₄ reg (by simp [hs1, hd1, hl1, hi1, ht1, ht2])
    · have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      let x₅ : Data 20 :=
        (((((x₄.set rTmp1 (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
          (base + c * (6 * t) + 1)).set rTmp1 (nodeAddr base t c)).set rTmp2
          (x.mem (nodeAddr base t c))).set rZero 0
      have he3 : ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) := by
        unfold copyUpperBranch
        dsimp only [x₅]
        wram_exec [hz₄, ho₄, hb₄_reg, hst₄, hch₄, hna_c, hlf₄, hlf0,
          hf_cmul, hf_cb0, hf_cb1, hf_ac, hf0]
      refine ⟨x₅, he3, he3.bounded hb₄, ?_, rfl, fun reg hnot => ?_⟩
      · simp only [hlf0, ↓reduceIte]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
        obtain ⟨hs1, hd1, hl1, hi1, ht1, ht2, hzr⟩ := hnot
        dsimp only [x₅]
        simp only [Data.set_regs_of_ne hzr _, Data.set_regs_of_ne ht2 _,
          Data.set_regs_of_ne ht1 _]
        exact hkeep₄ reg (by simp [hs1, hd1, hl1, hi1, ht1, ht2])
  obtain ⟨x₅, he3, hb₅, hmem₅, hz₅, hkeep₅⟩ := hmem₃_step
  -- Step 4: `copyUpperPost`
  have hlf₅ : x₅.mem (nodeAddr base t c) = x.mem (nodeAddr base t c) := by
    rw [hmem₅]
    split_ifs
    · rw [ArrayCopy.copyPrefix_outside (by omega)]; exact hlf₄
    · exact hlf₄
  have ho₅ : x₅.regs rOne = 1 := (hkeep₅ rOne (by decide)).trans ho
  have hb₅_reg : x₅.regs rBase = base := (hkeep₅ rBase (by decide)).trans hbase
  have hd₅ : x₅.regs rDeg = t := (hkeep₅ rDeg (by decide)).trans hdeg
  have hst₅ : x₅.regs rStride = 6 * t := (hkeep₅ rStride (by decide)).trans hstride
  have hch₅ : x₅.regs rChild = c := (hkeep₅ rChild (by decide)).trans hchild
  have hcnt₅ : x₅.regs rCnt = z := (hkeep₅ rCnt (by decide)).trans hcnt
  let y : Data 20 :=
    ((((((((((((((x₅.set rSrc (c * (6 * t))).set rSrc (base + c * (6 * t))).set rSrc
      (base + c * (6 * t) + 1)).set rSrc (nodeAddr base t c)).set rTmp2
      (x.mem (nodeAddr base t c))).set rDst (z * (6 * t))).set rDst
      (base + z * (6 * t))).set rDst (base + z * (6 * t) + 1)).set rDst
      (nodeAddr base t z)).write (nodeAddr base t z) (x.mem (nodeAddr base t c))).set rLim
      (t - 1)).set rTmp1 (nodeAddr base t z + 1)).write (nodeAddr base t z + 1) (t - 1)).set rTmp1
      (nodeAddr base t c + 1)).write (nodeAddr base t c + 1) (t - 1)
  have he4 : ExecWithin w copyUpperPost x₅ y 15 := by
    unfold copyUpperPost
    dsimp only [y]
    wram_exec [ho₅, hb₅_reg, hd₅, hst₅, hch₅, hcnt₅, hna_c, hna_z, hlf₅,
      hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_ac1, hf_zmul, hf_zb0, hf_zb1, hf_az, hf_az1, hf_tm1]
  have hfull : ExecWithin w copyUpperCode x y (21 * t + 48) :=
    (he1.seq (hc1.seq (he2.seq (hc2.seq (he3.seq he4))))).mono (by omega)
  have hymem : y.mem = memCopyUpper base t c z x.mem := by
    simp only [x₁, Data.set_mem] at hmem₂
    simp only [x₃, Data.set_mem] at hmem₄
    dsimp only [y, memCopyUpper]
    wram_simp
    simp only [hmem₅, hmem₄, hmem₂]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    have := base_lt_nodeAddr base t c 0
    have := base_lt_nodeAddr base t z 0
    apply memCopyUpper_outside ht <;> by_contra h_in <;> apply hnot <;>
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in ⊢ <;> omega
  refine ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, ?_, fun reg hnot => ?_⟩
  · dsimp only [y]; wram_simp; exact hz₅
  · have hnot' := hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot'
    obtain ⟨hs1, hd1, hl1, _, ht1, ht2, _⟩ := hnot'
    dsimp only [y]
    simp only [Data.write_regs, Data.set_regs_of_ne ht1 _, Data.set_regs_of_ne hl1 _,
      Data.set_regs_of_ne hd1 _, Data.set_regs_of_ne ht2 _, Data.set_regs_of_ne hs1 _]
    exact hkeep₅ reg hnot

/-- `memCopyUpper` leaves every key, value, and child cell (`2 ≤ o < 6 * t`) of `c` unchanged when
`nodeAddr c + 6 * t ≤ nodeAddr cnt`. -/
theorem memCopyUpper_at_c {base t c cnt : ℕ}
    (hsep : nodeAddr base t c + 6 * t ≤ nodeAddr base t cnt)
    (o : ℕ) (ho_lo : 2 ≤ o) (ho_hi : o < 6 * t) (mem : ℕ → ℕ) :
    memCopyUpper base t c cnt mem (nodeAddr base t c + o) = mem (nodeAddr base t c + o) := by
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  rw [hac_def, haz_def] at hsep
  dsimp only [memCopyUpper]
  simp only [hac_def, haz_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]
  split_ifs
  · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
      ArrayCopy.copyPrefix_outside (by omega)]
  · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]

theorem not_readsWidth_copyUpperCode : ¬copyUpperCode.ReadsWidth := by
  simp [copyUpperCode, copyUpperPre1, copyUpperPre2, copyUpperBranch, copyUpperPost,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_copyArrayCode]

theorem isRandFree_copyUpperCode : copyUpperCode.IsRandFree := by
  simp [copyUpperCode, copyUpperPre1, copyUpperPre2, copyUpperBranch, copyUpperPost,
    Code.IsRandFree, isRandFree_copyArrayCode]

end Cslib.DataStructure.BTree.WordRAM
