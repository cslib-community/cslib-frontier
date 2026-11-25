/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.DataStructure.BTree.WordRAM.Rep
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Shared Word-RAM B-Tree Scratch Registers, Inner Loops, and Node-Header Scanner

Internal infrastructure shared privately across the B-tree lookup, split, and insertion modules
(never re-exported publicly by `CslibFrontier.DataStructure.BTree.WordRAM`):

* Scratch register indices `rZero..rTmp2` (`Fin 20` slots `5..19`).
* Arena address bounds (`stride_le_arena`, `nodeAddr_add_le_arena`) and slot-count order helpers
  (`slotCount_le`, `keyAt_gt_of_slotCount_not_hit`).
* Bounded array-copy wrapper `copyArrayCode` (`copyArrayCode_spec`), backward-shift loop
  `shiftLoop` (`shiftLoop_spec`), within-node key scan `slotScanLoop` (`slotScanLoop_spec`), and
  combined node-header + key-scan routine `loadAndScan` (`loadAndScan_spec`).
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure
open Reg

/-- Scratch register holding constant `0`. -/
abbrev rZero : Fin 20 := 5
/-- Scratch register holding constant `1`. -/
abbrev rOne : Fin 20 := 6
/-- Scratch register holding `nodeStride t = 6 * t`. -/
abbrev rStride : Fin 20 := 7
/-- Scratch register holding the current node index `u`. -/
abbrev rCur : Fin 20 := 8
/-- Scratch register holding the child node index `c`. -/
abbrev rChild : Fin 20 := 9
/-- Scratch register holding the allocated node count `cnt`. -/
abbrev rCnt : Fin 20 := 10
/-- Scratch register holding the scanned key slot `slot`. -/
abbrev rSlot : Fin 20 := 11
/-- Scratch register holding the current node's key count `m`. -/
abbrev rNumK : Fin 20 := 12
/-- Scratch register holding a source array address. -/
abbrev rSrc : Fin 20 := 13
/-- Scratch register holding a destination array address or upper bound. -/
abbrev rDst : Fin 20 := 14
/-- Scratch register holding a loop limit `N`. -/
abbrev rLim : Fin 20 := 15
/-- Scratch register holding a loop counter `j`. -/
abbrev rIdx : Fin 20 := 16
/-- Scratch register holding the loop-continuation flag (`1` active, `0` done). -/
abbrev rActive : Fin 20 := 17
/-- Temporary arithmetic/address scratch register 1. -/
abbrev rTmp1 : Fin 20 := 18
/-- Temporary arithmetic/address scratch register 2. -/
abbrev rTmp2 : Fin 20 := 19

/-- One node stride `6 * t` fits inside any non-empty arena capacity `1 ≤ capNodes`. -/
theorem stride_le_arena {base capNodes t : ℕ} (hcap : 1 ≤ capNodes) :
    6 * t ≤ base + arenaWords t capNodes := by
  have hmul : 1 * nodeStride t ≤ capNodes * nodeStride t := Nat.mul_le_mul_right _ hcap
  simp only [arenaWords, nodeStride, Nat.one_mul] at hmul ⊢
  omega

/-- Every offset `o ≤ 6 * t` within node `u < capNodes` lies within `base + arenaWords t capNodes`.
-/
theorem nodeAddr_add_le_arena {base capNodes t u o : ℕ}
    (hu : u < capNodes) (ho : o ≤ 6 * t) :
    nodeAddr base t u + o ≤ base + arenaWords t capNodes := by
  have hmul : (u + 1) * nodeStride t ≤ capNodes * nodeStride t :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [nodeAddr, arenaWords, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢
  omega

/-- `slotCount base t mem u k j` never exceeds the scan length `j`. -/
theorem slotCount_le (base t : ℕ) (mem : ℕ → ℕ) (u k j : ℕ) :
    slotCount base t mem u k j ≤ j := by
  induction j with
  | zero => simp [slotCount]
  | succ n ihn => rw [slotCount]; split_ifs <;> omega

/-- When `slot = slotCount base t mem u k m` is not an exact hit on a strictly sorted node, every
key at index `i ≥ slot` (`i < m`) is strictly greater than `k`. -/
theorem keyAt_gt_of_slotCount_not_hit {base t u k m : ℕ} {mem : ℕ → ℕ}
    (hstrict : ∀ ⦃i j⦄, i < j → j < m → keyAt base t mem u i < keyAt base t mem u j)
    (hhit : ¬(slotCount base t mem u k m < m ∧
      keyAt base t mem u (slotCount base t mem u k m) = k)) :
    ∀ i, slotCount base t mem u k m ≤ i → i < m → k < keyAt base t mem u i := by
  set slot := slotCount base t mem u k m
  have hsc := slotCount_spec (k := k) (fun _ _ h1 h2 => hstrict h1 h2) m le_rfl
  intro i hge hi
  rcases eq_or_lt_of_le hge with rfl | hgt
  · have hle_s := hsc.2.2 slot le_rfl hi
    have hne_s : keyAt base t mem u slot ≠ k := fun heq => hhit ⟨hi, heq⟩
    omega
  · have hle_s := hsc.2.2 slot le_rfl (by omega)
    have hne_s : keyAt base t mem u slot ≠ k := fun heq => hhit ⟨by omega, heq⟩
    exact (show k < keyAt base t mem u slot by omega).trans (hstrict hgt hi)

private abbrev copyRegMap : Fin 7 → Fin 20 :=
  ![rSrc, rDst, rLim, rIdx, rTmp1, rTmp2, rOne]

private theorem copyRegMap_injective : Function.Injective copyRegMap := by decide

/-- Copy `rLim` words from `rSrc` to `rDst` via `ArrayCopy.program`, restoring `rOne = 1`. -/
def copyArrayCode : Code .standard 20 := ram[
  ⟪ArrayCopy.program.rename copyRegMap⟫;
  rOne ← #1 ]

/-- Specification of `copyArrayCode` on separated or identical ranges of length `N`. -/
theorem copyArrayCode_spec {w srcBase dstBase N : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (ho : x.regs rOne = 1) (hsrc : x.regs rSrc = srcBase)
    (hdst : x.regs rDst = dstBase) (hlim : x.regs rLim = N)
    (hf_src : Fits w (srcBase + N)) (hf_dst : Fits w (dstBase + N))
    (hdisj : srcBase + N ≤ dstBase ∨ dstBase + N ≤ srcBase ∨ srcBase = dstBase) :
    ∃ y, ExecWithin w copyArrayCode x y (7 * N + 5) ∧
      y.Bounded w ∧
      y.mem = ArrayCopy.copyPrefix x.mem srcBase dstBase N ∧
      ∀ reg : Fin 20, reg ∉ ([rIdx, rTmp1, rTmp2] : List (Fin 20)) → y.regs reg = x.regs reg := by
  have h1 : Fits w 1 := by rw [← ho]; exact hbdd.1 rOne
  have hcs : (x.comap copyRegMap).regs ArrayCopy.src = srcBase := hsrc
  have hcd : (x.comap copyRegMap).regs ArrayCopy.dst = dstBase := hdst
  have hcl : (x.comap copyRegMap).regs ArrayCopy.len = N := hlim
  obtain ⟨z, hz_exec, ⟨hzm, hzs, hzd, hzl⟩, hframe⟩ :=
    ExecWithin.rename_post copyRegMap_injective
      (ArrayCopy.exec_of_separated_or_eq (x.comap copyRegMap) h1
        (by rw [hcs, hcl]; exact hf_src)
        (by rw [hcd, hcl]; exact hf_dst)
        (by rw [hcs, hcd, hcl]; exact hdisj))
  rw [hcl] at hz_exec hzm hzl
  rw [hcs] at hzm hzs
  rw [hcd] at hzm hzd
  let y := z.set rOne 1
  have hy_exec : ExecWithin w copyArrayCode x y (7 * N + 5) :=
    hz_exec.seq (ExecWithin.const h1)
  refine ⟨y, hy_exec, hy_exec.bounded hbdd, hzm, fun reg hnot => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
  obtain ⟨hi, ht1, ht2⟩ := hnot
  by_cases hor : reg = rOne
  · subst hor; exact ho.symm
  dsimp only [y]
  rw [Data.set_regs_of_ne hor]
  by_cases hs : reg = rSrc
  · subst hs; exact hzs.trans hsrc.symm
  by_cases hd : reg = rDst
  · subst hd; exact hzd.trans hdst.symm
  by_cases hl : reg = rLim
  · subst hl; exact hzl.trans hlim.symm
  refine hframe reg (fun j => ?_)
  rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | j, hj⟩
  exacts [Ne.symm hs, Ne.symm hd, Ne.symm hl, Ne.symm hi, Ne.symm ht1, Ne.symm ht2, Ne.symm hor,
    by omega]

private def shiftBody : Code .standard 20 := ram[
  rTmp1 ← rDst - rIdx;
  rTmp2 ← rTmp1 - rOne;
  rTmp2 ← rSrc + rTmp2;
  rTmp2 ← *rTmp2;
  rTmp1 ← rSrc + rTmp1;
  *rTmp1 ← rTmp2;
  rIdx ← rIdx + rOne ]

/-- Backward-shift `rLim` elements inside the array at `rSrc` from upper index `rDst`. -/
def shiftLoop : Code .standard 20 := ram[
  rIdx ← #0;
  while rIdx < rLim do [⟪shiftBody⟫] ]

/-- Specification of `shiftLoop`, matching `shiftArrRight arrBase upper count`. -/
theorem shiftLoop_spec {w arrBase upper count : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (ho : x.regs rOne = 1) (hsrc : x.regs rSrc = arrBase)
    (hdst : x.regs rDst = upper) (hlim : x.regs rLim = count)
    (hcount : count ≤ upper)
    (hf_arr : Fits w (arrBase + upper)) :
    ∃ y, ExecWithin w shiftLoop x y (9 * count + 3) ∧
      y.Bounded w ∧
      y.mem = shiftArrRight arrBase upper count x.mem ∧
      ∀ reg : Fin 20, reg ∉ ([rIdx, rTmp1, rTmp2] : List (Fin 20)) → y.regs reg = x.regs reg := by
  let x₀ := x.set rIdx 0
  have h0 : ExecWithin w (ram[ rIdx ← #0 ] : Code .standard 20) x x₀ 1 :=
    ExecWithin.const (hf_arr.of_le (Nat.zero_le _))
  let P (j : ℕ) (z : Data 20) : Prop :=
    z.Bounded w ∧
      z.mem = shiftArrRight arrBase upper j x.mem ∧
      ∀ reg : Fin 20, reg ∉ ([rIdx, rTmp1, rTmp2] : List (Fin 20)) → z.regs reg = x.regs reg
  have hP0 : P (x₀.regs rIdx) x₀ := by
    have hidx0 : x₀.regs rIdx = 0 := rfl
    rw [hidx0]
    refine ⟨hbdd.set (hf_arr.of_le (Nat.zero_le _)), rfl, fun reg hnot => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    dsimp only [x₀]
    exact Data.set_regs_of_ne hnot.1 _
  obtain ⟨y, hy_loop, ⟨hby, hymem, hyreg⟩, _⟩ := ExecWithin.loop_count (w := w) (N := count)
    (T := 7) (index := rIdx) (limit := rLim) (body := shiftBody) P
    (fun z ⟨_, _, hz⟩ => (hz rLim (by decide)).trans hlim)
    (fun z ⟨hb_z, hmem_z, hreg_z⟩ hj_lt => by
      set j := z.regs rIdx
      have ho_z : z.regs rOne = 1 := (hreg_z rOne (by decide)).trans ho
      have hsrc_z : z.regs rSrc = arrBase := (hreg_z rSrc (by decide)).trans hsrc
      have hdst_z : z.regs rDst = upper := (hreg_z rDst (by decide)).trans hdst
      have hf_d1 : Fits w (upper - j) := hf_arr.of_le (by omega)
      have hf_d2 : Fits w (upper - j - 1) := hf_arr.of_le (by omega)
      have hf_a2 : Fits w (arrBase + (upper - j - 1)) := hf_arr.of_le (by omega)
      have hf_a1 : Fits w (arrBase + (upper - j)) := hf_arr.of_le (by omega)
      have hf_j1 : Fits w (j + 1) := hf_arr.of_le (by omega)
      let z' : Data 20 :=
        ((((((z.set rTmp1 (upper - j)).set rTmp2 (upper - j - 1)).set rTmp2
          (arrBase + (upper - j - 1))).set rTmp2 (z.mem (arrBase + (upper - j - 1)))).set rTmp1
          (arrBase + (upper - j))).write (arrBase + (upper - j))
          (z.mem (arrBase + (upper - j - 1)))).set rIdx (j + 1)
      have he_b : ExecWithin w shiftBody z z' 7 := by
        unfold shiftBody
        dsimp only [z']
        wram_exec [ho_z, hsrc_z, hdst_z, hf_d1, hf_d2, hf_a2, hf_a1, hf_j1]
      have hz'_mem : z'.mem = shiftArrRight arrBase upper (j + 1) x.mem := by
        have hsub : upper - j - 1 = upper - 1 - j := by omega
        dsimp only [z', shiftArrRight]
        rw [hsub, ← hmem_z]
        wram_simp
      refine ⟨z', he_b, ⟨he_b.bounded hb_z, hz'_mem, fun reg hnot => ?_⟩, rfl⟩
      have hnot' := hnot
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot'
      obtain ⟨h1, h2, h3⟩ := hnot'
      dsimp only [z']
      simp only [Data.set_regs_of_ne h1 _, Data.write_regs, Data.set_regs_of_ne h2 _,
        Data.set_regs_of_ne h3 _]
      exact hreg_z reg hnot)
    (Nat.zero_le count) hP0
  have hfull : ExecWithin w shiftLoop x y (9 * count + 3) :=
    (h0.seq hy_loop).mono (by have : x₀.regs rIdx = 0 := rfl; rw [this]; omega)
  exact ⟨y, hfull, hby, hymem, hyreg⟩

private def slotScanBody : Code .standard 20 := ram[
  rTmp1 ← rSrc + rIdx;
  rTmp2 ← *rTmp1;
  if rTmp2 < rKey then [
    rSlot ← rSlot + rOne
  ] else [
    rZero ← #0
  ];
  rIdx ← rIdx + rOne ]

/-- Scan `rLim` keys starting at `rSrc`, counting keys strictly less than `rKey` into `rSlot`. -/
def slotScanLoop : Code .standard 20 := ram[
  rSlot ← #0;
  rIdx ← #0;
  while rIdx < rLim do [⟪slotScanBody⟫] ]

/-- Specification of `slotScanLoop`, computing `slotCount base t x.mem u k m` in `rSlot`. -/
theorem slotScanLoop_spec {w base t u k m : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hkey : x.regs rKey = k)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2)
    (hlim : x.regs rLim = m)
    (hf_keys : Fits w (nodeAddr base t u + 2 + m)) :
    ∃ y, ExecWithin w slotScanLoop x y (8 * m + 4) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rSlot = slotCount base t x.mem u k m ∧
      y.regs rZero = 0 ∧
      ∀ reg : Fin 20, reg ∉ ([rSlot, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
        y.regs reg = x.regs reg := by
  have hf0 : Fits w 0 := hf_keys.of_le (Nat.zero_le _)
  let x₀ := (x.set rSlot 0).set rIdx 0
  let P (j : ℕ) (z : Data 20) : Prop :=
    z.Bounded w ∧
      z.mem = x.mem ∧
      z.regs rSlot = slotCount base t x.mem u k j ∧
      z.regs rZero = 0 ∧
      ∀ reg : Fin 20, reg ∉ ([rSlot, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
        z.regs reg = x.regs reg
  have hP0 : P (x₀.regs rIdx) x₀ := by
    have hidx0 : x₀.regs rIdx = 0 := rfl
    rw [hidx0]
    refine ⟨(hbdd.set hf0).set hf0, rfl, rfl, hz, fun reg hnot => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    dsimp only [x₀]
    simp only [Data.set_regs_of_ne hnot.2.1 _, Data.set_regs_of_ne hnot.1 _]
  obtain ⟨y, hy_loop, ⟨hby, hymem, hyslot, hyz, hyreg⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (N := m) (T := 6)
      (index := rIdx) (limit := rLim) (body := slotScanBody) P
      (fun z ⟨_, _, _, _, hreg⟩ => (hreg rLim (by decide)).trans hlim)
      (fun z ⟨hb_z, hmem_z, hslot_z, hz_z, hreg_z⟩ hj_lt => by
        set j := z.regs rIdx
        have hj_eq : z.regs rIdx = j := rfl
        have ho_z : z.regs rOne = 1 := (hreg_z rOne (by decide)).trans ho
        have hk_z : z.regs rKey = k := (hreg_z rKey (by decide)).trans hkey
        have hsrc_z : z.regs rSrc = nodeAddr base t u + 2 := (hreg_z rSrc (by decide)).trans hsrc
        have hslot_le := slotCount_le base t x.mem u k j
        have hf_aj : Fits w (nodeAddr base t u + 2 + j) := hf_keys.of_le (by omega)
        have hf_j1 : Fits w (j + 1) := hf_keys.of_le (by omega)
        have hf_s1 : Fits w (slotCount base t x.mem u k j + 1) := hf_keys.of_le (by omega)
        have hkj_eq : z.mem (nodeAddr base t u + 2 + j) = keyAt base t x.mem u j := by
          rw [hmem_z]; rfl
        by_cases hlt : keyAt base t x.mem u j < k
        · let z' : Data 20 :=
            ((((z.set rTmp1 (nodeAddr base t u + 2 + j)).set rTmp2
              (keyAt base t x.mem u j)).set rSlot (slotCount base t x.mem u k j + 1)).set rIdx
              (j + 1))
          have he_b : ExecWithin w slotScanBody z z' 6 := by
            unfold slotScanBody
            dsimp only [z']
            wram_exec [hj_eq, ho_z, hk_z, hsrc_z, hslot_z, hkj_eq, hlt, hf_aj, hf_j1, hf_s1]
          refine ⟨z', he_b, ⟨he_b.bounded hb_z, hmem_z, ?_, hz_z, fun reg hnot => ?_⟩, rfl⟩
          · simp only [z', slotCount, hlt, ↓reduceIte]
            wram_simp
          · have hnot' := hnot
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot'
            obtain ⟨h1, h2, h3, h4, _⟩ := hnot'
            dsimp only [z']
            simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _,
              Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h3 _]
            exact hreg_z reg hnot
        · let z' : Data 20 :=
            ((((z.set rTmp1 (nodeAddr base t u + 2 + j)).set rTmp2
              (keyAt base t x.mem u j)).set rZero 0).set rIdx (j + 1))
          have he_b : ExecWithin w slotScanBody z z' 6 := by
            unfold slotScanBody
            dsimp only [z']
            wram_exec [hj_eq, ho_z, hk_z, hsrc_z, hslot_z, hkj_eq, hlt, hf_aj, hf_j1, hf0]
          refine ⟨z', he_b, ⟨he_b.bounded hb_z, hmem_z, ?_, ?_, fun reg hnot => ?_⟩, rfl⟩
          · simp only [z', slotCount, hlt, ↓reduceIte, Nat.add_zero]
            wram_simp
            exact hslot_z
          · dsimp only [z']; wram_simp
          · have hnot' := hnot
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot'
            obtain ⟨_, h2, h3, h4, h5⟩ := hnot'
            dsimp only [z']
            simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h5 _,
              Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h3 _]
            exact hreg_z reg hnot)
      (Nat.zero_le m) hP0
  have hfull : ExecWithin w slotScanLoop x y (8 * m + 4) :=
    ((ExecWithin.const hf0).seq ((ExecWithin.const hf0).seq hy_loop)).mono
      (by have : x₀.regs rIdx = 0 := rfl; rw [this]; omega)
  exact ⟨y, hfull, hby, hymem, hyslot, hyz, hyreg⟩

private def loadNodeHeader : Code .standard 20 := ram[
  rSrc ← rCur * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rTmp1 ← rSrc + rOne;
  rNumK ← *rTmp1;
  rSrc ← rTmp1 + rOne;
  rLim ← rNumK ]

private theorem loadNodeHeader_spec {w base capNodes t u : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes)
    (hbdd : x.Bounded w)
    (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u) :
    ∃ y, ExecWithin w loadNodeHeader x y 8 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rSrc = nodeAddr base t u + 2 ∧
      y.regs rNumK = numKeys base t x.mem u ∧
      y.regs rLim = numKeys base t x.mem u ∧
      ∀ reg : Fin 20, reg ∉ ([rSrc, rTmp1, rNumK, rLim] : List (Fin 20)) →
        y.regs reg = x.regs reg := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hna_eq : base + u * (6 * t) + 1 + 1 = nodeAddr base t u := by
    simp only [nodeAddr, nodeStride]; omega
  have hf_mul : Fits w (u * (6 * t)) := hfit.of_le (by omega)
  have hf_b0 : Fits w (base + u * (6 * t)) := hfit.of_le (by omega)
  have hf_b1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
  have hf_au1 : Fits w (nodeAddr base t u + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (nodeAddr base t u + 2) := hfit.of_le (by omega)
  let m := numKeys base t x.mem u
  let y : Data 20 :=
    (((((((x.set rSrc (u * (6 * t))).set rSrc (base + u * (6 * t))).set rSrc
      (base + u * (6 * t) + 1)).set rSrc (nodeAddr base t u)).set rTmp1
      (nodeAddr base t u + 1)).set rNumK m).set rSrc (nodeAddr base t u + 2)).set rLim m
  have he : ExecWithin w loadNodeHeader x y 8 := by
    unfold loadNodeHeader
    dsimp only [y, m, numKeys]
    wram_exec [ho, hbase, hstride, hcur, hna_eq, hf_mul, hf_b0, hf_b1, hf_au, hf_au1, hf_au2]
  refine ⟨y, he, he.bounded hbdd, rfl, rfl, ?_, rfl, fun reg hnot => ?_⟩
  · dsimp only [y, m]; wram_simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨h1, h2, h3, h4⟩ := hnot
    dsimp only [y]
    simp only [Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h1 _, Data.set_regs_of_ne h3 _,
      Data.set_regs_of_ne h2 _]

/-- Load `rNumK = numKeys u` and `rSrc = nodeAddr u + 2` for `rCur = u`, then scan `rSlot`. -/
def loadAndScan : Code .standard 20 := ram[
  ⟪loadNodeHeader⟫;
  ⟪slotScanLoop⟫ ]

/-- Specification of `loadAndScan` on node `u < capNodes`. -/
theorem loadAndScan_spec {w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : numKeys base t x.mem u ≤ 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k) (hcur : x.regs rCur = u) :
    let m := numKeys base t x.mem u
    ∃ y, ExecWithin w loadAndScan x y (8 * m + 12) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧
      y.regs rStride = 6 * t ∧ y.regs rKey = k ∧ y.regs rCur = u ∧
      y.regs rSrc = nodeAddr base t u + 2 ∧
      y.regs rNumK = m ∧
      y.regs rSlot = slotCount base t x.mem u k m ∧
      ∀ reg : Fin 20,
        reg ∉ ([rSrc, rNumK, rLim, rSlot, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
          y.regs reg = x.regs reg := by
  set m := numKeys base t x.mem u
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hf_keys : Fits w (nodeAddr base t u + 2 + m) := hfit.of_le (by omega)
  obtain ⟨x₁, h1, hb₁, hmem₁, hsrc₁, hnk₁, hlim₁, hreg₁⟩ :=
    loadNodeHeader_spec ht hu_cap hbdd hfit ho hbase hstride hcur
  have hz₁ : x₁.regs rZero = 0 := (hreg₁ rZero (by decide)).trans hz
  have ho₁ : x₁.regs rOne = 1 := (hreg₁ rOne (by decide)).trans ho
  have hk₁ : x₁.regs rKey = k := (hreg₁ rKey (by decide)).trans hkey
  obtain ⟨x₂, h2, hb₂, hmem₂, hslot₂, hz₂, hreg₂⟩ :=
    slotScanLoop_spec hb₁ hz₁ ho₁ hk₁ hsrc₁ hlim₁ hf_keys
  rw [hmem₁] at hslot₂ hmem₂
  have hkeep : ∀ reg : Fin 20,
      reg ∉ ([rSrc, rNumK, rLim, rSlot, rIdx, rTmp1, rTmp2, rZero] : List (Fin 20)) →
        x₂.regs reg = x.regs reg := by
    intro reg hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hs, hn, hl, hsl, hi, ht1, ht2, hzr⟩ := hnot
    refine (hreg₂ reg ?_).trans (hreg₁ reg ?_)
    · simp [hsl, hi, ht1, ht2, hzr]
    · simp [hs, ht1, hn, hl]
  refine ⟨x₂, (h1.seq h2).mono (by omega), hb₂, hmem₂, hz₂,
    (hkeep rOne (by decide)).trans ho,
    (hkeep rBase (by decide)).trans hbase,
    (hkeep rDeg (by decide)).trans hdeg,
    (hkeep rStride (by decide)).trans hstride,
    (hkeep rKey (by decide)).trans hkey,
    (hkeep rCur (by decide)).trans hcur,
    (hreg₂ rSrc (by decide)).trans hsrc₁,
    (hreg₂ rNumK (by decide)).trans hnk₁,
    hslot₂, hkeep⟩

theorem not_readsWidth_copyArrayCode : ¬copyArrayCode.ReadsWidth := by decide
theorem isRandFree_copyArrayCode : copyArrayCode.IsRandFree := by decide
theorem not_readsWidth_shiftLoop : ¬shiftLoop.ReadsWidth := by decide
theorem isRandFree_shiftLoop : shiftLoop.IsRandFree := by decide
theorem not_readsWidth_loadAndScan : ¬loadAndScan.ReadsWidth := by decide
theorem isRandFree_loadAndScan : loadAndScan.IsRandFree := by decide

end Cslib.DataStructure.BTree.WordRAM
