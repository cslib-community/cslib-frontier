/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TrimmedYates
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Triple
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Enumeration
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Trie
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Per-query dispatch for trimmed Yates on the word RAM

Answers one query `C = Cs[q]` from precomputed low-cardinality stage tables (`#C < s` directly by a
single trie lookup; `s ≤ #C` by enumerating subsets of `C` of size at most `#C - s`, complementing
in `C`, and running `runTransformTriple` at cutoff `s`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.queryStep`: per-query loop body for `solveFromTries`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_queryStep`: single-iteration `ExecWithin`
  specification advancing `QueryInv` from `q` to `q + 1`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

private theorem tripleSpace_mono {d a b : ℕ} (hab : a ≤ b) :
    tripleSpace d a ≤ tripleSpace d b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  dsimp only [tripleSpace]
  have hid :
      (3 * (d + 1 + d * (2 * d * a + 2)) + (2 + 2 * d * a)) + k * (6 * d ^ 2 + 2 * d) =
      3 * (d + 1 + d * (2 * d * (a + k) + 2)) + (2 + 2 * d * (a + k)) := by ring
  omega

private theorem shortBranch_budget_le {d H_pos : ℕ} (hH : 1 ≤ H_pos) {n_b : ℕ}
    (hn : n_b ≤ 2 + (9 * d + 8)) :
    n_b + 1 ≤ 180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3) := by
  have hpt := phaseTime_le (d := d) hH
  dsimp only [tripleTime] at hpt
  rw [sq] at hpt ⊢
  omega

private theorem longBranch_budget_le {d cl H_q H_pos : ℕ} (hH : 1 ≤ H_pos)
    (hcl : cl ≤ d) (hHq : H_q ≤ H_pos) {n_el : ℕ}
    (hn : n_el ≤ 2 + (cl * (20 * H_q + 12) + 8 +
      (12 * H_q + 3 + (5 + (tripleTime d H_q + (4 + (9 * d + 8))))))) :
    n_el + 2 ≤ 180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3) := by
  have hpt := phaseTime_le (d := d) hH
  have hcl_le : cl * (20 * H_q + 12) ≤ d * (20 * H_pos + 12) :=
    Nat.mul_le_mul hcl (by omega)
  have htr_le : tripleTime d H_q ≤ tripleTime d H_pos := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hHq
    dsimp only [tripleTime]
    have hid :
        (3 * (d * (H_q * (32 * d + 63) + 22) + 7) + (H_q * (32 * d + 53) + 9) + 15) +
        k * (96 * d ^ 2 + 221 * d + 53) =
        3 * (d * ((H_q + k) * (32 * d + 63) + 22) + 7) +
          ((H_q + k) * (32 * d + 53) + 9) + 15 := by ring
    omega
  omega

private theorem queryStep_base_le {d H_pos : ℕ} (hH : 1 ≤ H_pos) :
    5 + (11 * d + 5) + 3 ≤ 180 * (d + 1) ^ 2 * H_pos := by
  have hpt := phaseTime_le (d := d) hH
  dsimp only [tripleTime] at hpt
  omega

private def qLoadCode : Code .standard numRegs := ram[
  Reg.free ← rPreFree;
  rGenTmp ← Reg.queryPtr + rQueryIdx;
  rTrieKey ← *rGenTmp;
  rCoordsPtr ← Reg.free;
  Reg.free ← Reg.free + Reg.dim ]

private theorem qLoadCode_preserves (i : Fin numRegs) :
    i ≠ Reg.free ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr → qLoadCode.Preserves i := by
  decide +kernel +revert

private def qShortLoadCode : Code .standard numRegs := ram[
  rGenTmp ← rPreHsBase + Reg.dim;
  rTrieRoot ← *rGenTmp ]

private theorem qShortLoadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieRoot → qShortLoadCode.Preserves i := by
  decide +kernel +revert

private def qHighPrepCode : Code .standard numRegs := ram[
  Reg.entryPtr ← rDomPtr;
  Reg.entryCount ← rDomLen;
  rGenTmp ← rDomLen + rDomLen;
  Reg.free ← rDomPtr + rGenTmp;
  rStageCutoff ← Reg.thresh ]

private theorem qHighPrepCode_preserves (i : Fin numRegs) :
    i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff →
      qHighPrepCode.Preserves i := by
  decide +kernel +revert

private def qHighReadCode : Code .standard numRegs := ram[
  rGenTmp ← Reg.queryPtr + rQueryIdx;
  rTrieKey ← *rGenTmp;
  rGenTmp ← rRootsOut + Reg.dim;
  rTrieRoot ← *rGenTmp ]

private theorem qHighReadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rTrieRoot → qHighReadCode.Preserves i := by
  decide +kernel +revert

private def qBranchCode : Code .standard numRegs :=
  .branch (.lt rCoordsLen Reg.thresh)
    (.seq qShortLoadCode trieGet)
    (.seq (ram[ rMaxCard ← rCoordsLen - Reg.thresh; rDomPtr ← Reg.free ])
      (.seq genLowSubsets
        (.seq flipHighDom
          (.seq qHighPrepCode
            (.seq runTransformTriple
              (.seq qHighReadCode trieGet))))))

private theorem qBranchCode_preserves (i : Fin numRegs)
    (hshort : i ≠ rGenTmp ∧ i ≠ rTrieRoot)
    (hget : i.val < 18 ∨ 23 ≤ i.val)
    (hinit : i ≠ rMaxCard ∧ i ≠ rDomPtr)
    (hgen : i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val))
    (hflip : i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp)
    (hprep : i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff)
    (htriple : ¬ IsTripleMod i)
    (hread : i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rTrieRoot) :
    qBranchCode.Preserves i :=
  ⟨⟨qShortLoadCode_preserves i hshort, trieGet_preserves i hget⟩,
    ⟨by clear hshort hget hgen hflip hprep htriple hread; revert i hinit; decide +kernel,
      genLowSubsets_preserves i hgen, flipHighDom_preserves i hflip,
      qHighPrepCode_preserves i hprep, runTransformTriple_preserves i htriple,
      qHighReadCode_preserves i hread, trieGet_preserves i hget⟩⟩

private theorem qBranchCode_preserves_one : qBranchCode.Preserves rOne :=
  qBranchCode_preserves rOne (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
private theorem qBranchCode_preserves_out : qBranchCode.Preserves Reg.outPtr :=
  qBranchCode_preserves Reg.outPtr (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
private theorem qBranchCode_preserves_qi : qBranchCode.Preserves rQueryIdx :=
  qBranchCode_preserves rQueryIdx (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def qWriteCode : Code .standard numRegs := ram[
  rQueryIdx ← rQueryIdx + rOne;
  rGenTmp ← Reg.outPtr + rQueryIdx;
  *rGenTmp ← rTrieVal ]

/-- Evaluate query `rQueryIdx` (via direct lookup when `#C ≤ s` or high-domain Yates passes when
`s < #C`), write its encoded covering-product value to the output array, and advance `rQueryIdx`. -/
def queryStep : Code .standard numRegs :=
  .seq qLoadCode (.seq extractCoords (.seq qBranchCode qWriteCode))

private abbrev IsQueryKept (i : Fin numRegs) : Prop :=
  i = rZero ∨ i = rOne ∨ i = Reg.dim ∨ i = Reg.thresh ∨ i = Reg.outPtr ∨ i = rPreFree ∨
    i = Reg.trieF ∨ i = Reg.trieG ∨ i = Reg.queryPtr ∨ i = Reg.queryCount ∨
    i = rPreFsBase ∨ i = rPreGsBase ∨ i = rPreHsBase

private theorem queryStep_preserves (i : Fin numRegs) :
    IsQueryKept i → queryStep.Preserves i := by
  intro hi
  exact ⟨qLoadCode_preserves i (by revert i hi; decide +kernel),
    extractCoords_preserves i (by revert i hi; decide +kernel),
    qBranchCode_preserves i
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel)
      (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel⟩

private theorem HoldsTrie.congr_root {mem : ℕ → ℕ} {bound d r₁ r₂ : ℕ} {fn : ℕ → ℕ}
    (hr : r₁ = r₂) (h : HoldsTrie mem bound d r₂ fn) : HoldsTrie mem bound d r₁ fn :=
  hr ▸ h

private theorem exec_qLongBranch {w d s baseFree outBase qWorkStart rootF rootG qPtr q
    preFs preGs preHs W H_pos spVal : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ}
    {C : Finset (Fin d)} {cList : List (Fin d)}
    {initMem preMem stMem : ℕ → ℕ}
    (u₁ : Data numRegs)
    (hz : u₁.regs rZero = 0) (ho : u₁.regs rOne = 1) (hd : u₁.regs Reg.dim = d)
    (hs_reg : u₁.regs Reg.thresh = s) (hkey : u₁.regs rTrieKey = setMask C)
    (hcp : u₁.regs rCoordsPtr = qWorkStart) (hclen : u₁.regs rCoordsLen = #C)
    (hfr : u₁.regs Reg.free = qWorkStart + d)
    (htF_reg : u₁.regs Reg.trieF = rootF) (htG_reg : u₁.regs Reg.trieG = rootG)
    (hqp : u₁.regs Reg.queryPtr = qPtr) (hqi : u₁.regs rQueryIdx = q)
    (hpFs : u₁.regs rPreFsBase = preFs) (hpGs : u₁.regs rPreGsBase = preGs)
    (hpHs : u₁.regs rPreHsBase = preHs)
    (hcList_nd : cList.Nodup) (hcList_tf : cList.toFinset = C)
    (hcList_len : cList.length = #C)
    (hcmem : ∀ j (hj : j < cList.length), u₁.mem (qWorkStart + j) = cList[j].val)
    (hu₁_below_qw : ∀ a < qWorkStart, u₁.mem a = stMem a)
    (hs_pre : ∀ a < outBase, stMem a = preMem a)
    (hpre_below_bf : ∀ a < baseFree, preMem a = initMem a)
    (hob_gt_bf : baseFree < outBase) (hob_le_qw : outBase < qWorkStart)
    (hq_lt : qPtr + q < qWorkStart) (hread_q : stMem (qPtr + q) = setMask C)
    (htrieF : HoldsTrie initMem baseFree d rootF fnF)
    (htrieG : HoldsTrie initMem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hpFs_lt : preFs + d < outBase) (hpGs_lt : preGs + d < outBase)
    (hpHs_lt : preHs + d < outBase)
    (hpreF_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preFs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y))
    (hpreG_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preGs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y))
    (hpreH_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preHs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
          (fun S => subsetZeta f S * subsetZeta g S) Y))
    (hsC : s ≤ #C) (hH_pos1 : 1 ≤ H_pos) (hC_H : highCount #C s ≤ H_pos)
    (hqw_bound : qWorkStart + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal)
    (hfit_space : Fits w spVal) (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ u_ans,
      ExecWithin w qBranchCode u₁ u_ans
        (180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3)) ∧
      u_ans.regs rTrieVal = Signed.encode (coveringProduct f g C) ∧
      (∀ a < qWorkStart, u_ans.mem a = stMem a) := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  have hlt_Cs : ¬ #C < s := Nat.not_lt_of_ge hsC
  have hcond : ¬ (Cond.lt rCoordsLen Reg.thresh).Holds u₁ := by
    simp [Cond.holds_lt, hclen, hs_reg, hlt_Cs]
  let highDomBase := qWorkStart + d
  have hf_sub : Fits w (#C - s) :=
    hfit_d.of_le ((by have := Finset.card_le_univ C; simp at this; omega : #C - s ≤ d))
  have hw0_st : ∃ w₀, ExecWithin (B := .standard) w
      (ram[ rMaxCard ← rCoordsLen - Reg.thresh; rDomPtr ← Reg.free ]) u₁ w₀ 2 ∧
      w₀.regs rZero = 0 ∧ w₀.regs rOne = 1 ∧ w₀.regs Reg.thresh = s ∧
      w₀.regs rTrieKey = setMask C ∧ w₀.regs rCoordsPtr = qWorkStart ∧
      w₀.regs rCoordsLen = #C ∧ w₀.regs rMaxCard = #C - s ∧
      w₀.regs rDomPtr = highDomBase ∧ w₀.regs Reg.dim = d ∧
      w₀.regs Reg.trieF = rootF ∧ w₀.regs Reg.trieG = rootG ∧
      w₀.regs Reg.queryPtr = qPtr ∧ w₀.regs rQueryIdx = q ∧
      w₀.regs rPreFsBase = preFs ∧ w₀.regs rPreGsBase = preGs ∧
      w₀.regs rPreHsBase = preHs ∧ w₀.mem = u₁.mem := by
    wram_exec [hclen, hs_reg, hfr]
    wram_simp [hz, ho, hs_reg, hkey, hcp, hclen, hd, htF_reg, htG_reg, hqp, hqi,
      hpFs, hpGs, hpHs, highDomBase]
  obtain ⟨w₀, he_w0, hw₀z, hw₀o, hw₀s, hw₀key, hw₀cp, hw₀cl, hw₀mc, hw₀dp,
    hw₀d, hw₀tF, hw₀tG, hw₀qp, hw₀qi, hw₀pFs, hw₀pGs, hw₀pHs, hw₀mem⟩ := hw0_st
  obtain ⟨H_q, hHq_def⟩ : ∃ H_q, highCount #C s = H_q := ⟨_, rfl⟩
  have hHq_le : H_q ≤ H_pos := hHq_def ▸ hC_H
  have hts_mono : tripleSpace d H_q ≤ tripleSpace d H_pos := tripleSpace_mono hHq_le
  have hsum_Hq : ∑ j ∈ range (#C - s + 1), cList.length.choose j = H_q := by
    rw [hcList_len, sum_range_sub_eq_highCount hsC, hHq_def]
  clear hHq_def
  have hcList_le_d : cList.length ≤ d := by
    rw [hcList_len]; simpa using Finset.card_le_univ C
  obtain ⟨w₁, he_ghigh_raw, hw₁_dlen, hw₁_dom, hw₁_fr, hw₁_regs⟩ :=
    exec_genLowSubsets cList w₀ hw₀z hw₀o hw₀cp (hw₀cl.trans hcList_len.symm)
      hw₀mc hw₀dp hcList_nd (by rwa [hw₀mem]) (by dsimp only [highDomBase]; omega)
      (by rw [hsum_Hq]; exact hfit_space.of_le (by dsimp only [highDomBase]; omega))
      hfit_mask
  have he_ghigh : ExecWithin w genLowSubsets w₀ w₁ (cList.length * (20 * H_q + 12) + 8) := by
    rwa [hsum_Hq] at he_ghigh_raw
  clear he_ghigh_raw
  have hys_len_raw : (prefixesUpTo (#C - s) cList).length = H_q := by
    rw [length_prefixesUpTo (#C - s) hcList_nd, hsum_Hq]
  clear hsum_Hq
  have hys_spec_raw := prefixesUpTo_spec (#C - s) hcList_nd
  generalize hys_def : prefixesUpTo (#C - s) cList = ys
    at hw₁_dlen hw₁_dom hys_len_raw hys_spec_raw
  have hys_len : ys.length = H_q := hys_len_raw
  have hys_spec := hys_spec_raw
  have hys_sub : ∀ Y ∈ ys, Y ⊆ C := by
    intro Y hY
    have hsub := ((hys_spec.2 Y).mp hY).1
    rwa [hcList_tf] at hsub
  obtain ⟨w₂, he_flip, hw₂_dom, hw₂_fr, hw₂_regs⟩ :=
    exec_flipHighDom C ys w₁
      ((hw₁_regs rOne (by decide)).trans hw₀o)
      ((hw₁_regs rTrieKey (by decide)).trans hw₀key)
      ((hw₁_regs rCoordsLen (by decide)).trans hw₀cl)
      ((hw₁_regs rDomPtr (by decide)).trans hw₀dp)
      hw₁_dlen hys_sub hw₁_dom
      (by rw [hys_len]; exact hfit_space.of_le (by dsimp only [highDomBase]; omega))
      hfit_mask
  have hhigh_len_raw : (ys.map (C \ ·)).length = H_q := by simp [hys_len]
  have hhigh_nd_raw : (ys.map (C \ ·)).Nodup := by
    refine hys_spec.1.map_on fun Y₁ h₁ Y₂ h₂ heq => ?_
    have h₁C := hys_sub Y₁ h₁
    have h₂C := hys_sub Y₂ h₂
    calc Y₁ = C \ (C \ Y₁) := (Finset.sdiff_sdiff_eq_self h₁C).symm
      _ = C \ (C \ Y₂) := by rw [heq]
      _ = Y₂ := Finset.sdiff_sdiff_eq_self h₂C
  have hhigh_mem_raw : ∀ X, X ∈ ys.map (C \ ·) ↔ X ⊆ C ∧ s ≤ #X := by
    intro X
    simp only [List.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have hYC := hys_sub Y hY
      have hYcard := ((hys_spec.2 Y).mp hY).2
      rw [Finset.card_sdiff_of_subset hYC]
      exact ⟨sdiff_subset, by omega⟩
    · rintro ⟨hXC, hsX⟩
      refine ⟨C \ X, (hys_spec.2 _).mpr ⟨?_, ?_⟩, Finset.sdiff_sdiff_eq_self hXC⟩
      · rw [hcList_tf]; exact sdiff_subset
      · rw [Finset.card_sdiff_of_subset hXC]; omega
  generalize hhigh_def : ys.map (C \ ·) = highDom
    at hw₂_dom hhigh_len_raw hhigh_nd_raw hhigh_mem_raw
  have hhigh_len : highDom.length = H_q := hhigh_len_raw
  have hhigh_nd : highDom.Nodup := hhigh_nd_raw
  have hhigh_mem_iff : ∀ X, X ∈ highDom ↔ X ⊆ C ∧ s ≤ #X := hhigh_mem_raw
  let qTrStart := highDomBase + 2 * H_q
  have hf_2Hq : Fits w (H_q + H_q) := hfit_space.of_le (by omega)
  have hf_qts : Fits w (highDomBase + (H_q + H_q)) :=
    hfit_space.of_le (by dsimp only [highDomBase]; omega)
  have hw₂_dp : w₂.regs rDomPtr = highDomBase :=
    (hw₂_regs rDomPtr (by decide)).trans ((hw₁_regs rDomPtr (by decide)).trans hw₀dp)
  have hw₂_dl : w₂.regs rDomLen = H_q := by
    rw [hw₂_regs rDomLen (by decide), hw₁_dlen, hys_len]
  have hw₂_s : w₂.regs Reg.thresh = s :=
    (hw₂_regs Reg.thresh (by decide)).trans ((hw₁_regs Reg.thresh (by decide)).trans hw₀s)
  have hst3 : ∃ w₃, ExecWithin w qHighPrepCode w₂ w₃ 5 ∧
      w₃.regs Reg.entryPtr = highDomBase ∧ w₃.regs Reg.entryCount = highDom.length ∧
      w₃.regs Reg.free = qTrStart ∧ w₃.regs rStageCutoff = s ∧ w₃.mem = w₂.mem := by
    unfold qHighPrepCode
    wram_exec [hw₂_dp, hw₂_dl, hw₂_s]
    refine ⟨rfl, hhigh_len.symm, ?_, rfl, rfl⟩
    wram_simp [qTrStart]; omega
  obtain ⟨w₃, he_w3, hw₃_cdp, hw₃_cdl, hw₃_fr, hw₃_cut, hw₃_mem⟩ := hst3
  have hw₃_regs : ∀ i,
      i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff →
        w₃.regs i = w₂.regs i :=
    fun i hi => he_w3.regs_eq (qHighPrepCode_preserves i hi)
  have w₃_below_qw : ∀ a < qWorkStart, w₃.mem a = stMem a := fun a ha => by
    rw [hw₃_mem, hw₂_fr a (Or.inl (by dsimp only [highDomBase]; omega)),
      hw₁_fr a (Or.inl (by dsimp only [highDomBase]; omega)), hw₀mem]
    exact hu₁_below_qw a ha
  have w₃_below_ob : ∀ a < outBase, w₃.mem a = preMem a := fun a ha =>
    (w₃_below_qw a (by omega)).trans (hs_pre a ha)
  have w₃_below_bf : ∀ a < baseFree, w₃.mem a = initMem a := fun a ha =>
    (w₃_below_ob a (by omega)).trans (hpre_below_bf a ha)
  have hhigh_closed : ∀ X ∈ highDom, ∀ coord : Fin d, coord ∈ X →
      (s ≤ #(X.erase coord) → X.erase coord ∈ highDom) ∧
      (#(X.erase coord) < s → #(X.erase coord) ≤ s) := by
    intro X hX coord _
    have hXC := ((hhigh_mem_iff X).mp hX).1
    exact ⟨fun hge => (hhigh_mem_iff _).mpr ⟨(erase_subset _ _).trans hXC, hge⟩,
      fun _ => by omega⟩
  have hfb_q : 0 < s →
      preFs + d ≤ qTrStart ∧ preGs + d ≤ qTrStart ∧ preHs + d ≤ qTrStart ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preFs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
              (fun S => subsetZeta f S * subsetZeta g S) Y)) := by
    intro _
    have hlt_qts : outBase ≤ qTrStart := by dsimp only [qTrStart, highDomBase]; omega
    refine ⟨by omega, by omega, by omega, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreF_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preFs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreG_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preGs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreH_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preHs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
  have kw₃_w₀ (i : Fin numRegs)
      (h3 : i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff)
      (h2 : i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp)
      (h1g : i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      w₃.regs i = w₀.regs i :=
    (hw₃_regs i h3).trans ((hw₂_regs i h2).trans (hw₁_regs i h1g))
  obtain ⟨w₄, _, _, qHs, qEndFree, he_qtr, _, _, hw₄_ro, _, _, hqef_hi,
    _, _, hqHs_lt, _, _, _, ⟨qOutFn, hqOut_tr, hqOut_eq⟩, hw₄_frame, hw₄_regs⟩ :=
    exec_runTransformTriple (P_low := fun Y => #Y ≤ s) (W := W) w₃
      ((kw₃_w₀ rZero (by decide) (by decide) (by decide)).trans hw₀z)
      ((kw₃_w₀ rOne (by decide) (by decide) (by decide)).trans hw₀o)
      ((kw₃_w₀ Reg.dim (by decide) (by decide) (by decide)).trans hw₀d)
      hw₃_cdp hw₃_cdl hw₃_cut
      ((kw₃_w₀ Reg.trieF (by decide) (by decide) (by decide)).trans hw₀tF)
      ((kw₃_w₀ Reg.trieG (by decide) (by decide) (by decide)).trans hw₀tG)
      ((kw₃_w₀ rPreFsBase (by decide) (by decide) (by decide)).trans hw₀pFs)
      ((kw₃_w₀ rPreGsBase (by decide) (by decide) (by decide)).trans hw₀pGs)
      ((kw₃_w₀ rPreHsBase (by decide) (by decide) (by decide)).trans hw₀pHs)
      hw₃_fr (by dsimp only [qTrStart, highDomBase]; omega)
      hhigh_nd (by rwa [hw₃_mem]) (by rw [hhigh_len]) hhigh_closed
      ((htrieF.congr_below w₃_below_bf).mono_bound (by dsimp only [qTrStart, highDomBase]; omega))
      ((htrieG.congr_below w₃_below_bf).mono_bound (by dsimp only [qTrStart, highDomBase]; omega))
      hf_eq hg_eq hf_le hg_le hfb_q hfit_val
      (by
        rw [hhigh_len]
        refine hfit_space.of_le ?_
        dsimp only [qTrStart, highDomBase]
        omega)
  have hw₄_qp : w₄.regs Reg.queryPtr = qPtr :=
    (hw₄_regs Reg.queryPtr (by decide)).trans
      ((kw₃_w₀ Reg.queryPtr (by decide) (by decide) (by decide)).trans hw₀qp)
  have hw₄_qi : w₄.regs rQueryIdx = q :=
    (hw₄_regs rQueryIdx (by decide)).trans
      ((kw₃_w₀ rQueryIdx (by decide) (by decide) (by decide)).trans hw₀qi)
  have hw₄_d : w₄.regs Reg.dim = d :=
    (hw₄_regs Reg.dim (by decide)).trans
      ((kw₃_w₀ Reg.dim (by decide) (by decide) (by decide)).trans hw₀d)
  have hw₄_below_qw : ∀ a < qWorkStart, w₄.mem a = stMem a := fun a ha =>
    (hw₄_frame a (Or.inl (by dsimp only [qTrStart, highDomBase]; omega))).trans
      (w₃_below_qw a ha)
  have hw₄_read_q : w₄.mem (qPtr + q) = setMask C := by
    rw [hw₄_below_qw _ hq_lt]; exact hread_q
  have hf_qef : Fits w qEndFree := by
    rw [hhigh_len] at hqef_hi
    exact hfit_space.of_le (by dsimp only [qTrStart, highDomBase] at hqef_hi; omega)
  have hf_qhs_d : Fits w (qHs + d) := hf_qef.of_le (by omega)
  have hst5 : ∃ w₅, ExecWithin w qHighReadCode w₄ w₅ 4 ∧
      w₅.regs rTrieKey = setMask C ∧ w₅.regs rTrieRoot = w₄.mem (qHs + d) ∧
      w₅.mem = w₄.mem := by
    unfold qHighReadCode
    wram_exec [hw₄_qp, hw₄_qi, hw₄_ro, hw₄_d, hw₄_read_q]
    wram_simp [hw₄_read_q]
  obtain ⟨w₅, he_w5, hw₅_key, hw₅_root, hw₅_mem⟩ := hst5
  have hw₅_regs : ∀ i, i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rTrieRoot →
      w₅.regs i = w₄.regs i :=
    fun i hi => he_w5.regs_eq (qHighReadCode_preserves i hi)
  obtain ⟨w₆, he_get, hw₆_val, hw₆_mem, _⟩ :=
    exec_trieGet w₅
      ((hw₅_regs rZero (by decide)).trans ((hw₄_regs rZero (by decide)).trans
        ((kw₃_w₀ rZero (by decide) (by decide) (by decide)).trans hw₀z)))
      ((hw₅_regs rOne (by decide)).trans ((hw₄_regs rOne (by decide)).trans
        ((kw₃_w₀ rOne (by decide) (by decide) (by decide)).trans hw₀o)))
      ((hw₅_regs Reg.dim (by decide)).trans hw₄_d)
      hw₅_root hw₅_key (by rwa [hw₅_mem]) hf_qef hfit_d (hfit_mask.of_le (setMask_lt C).le)
  rw [hqOut_eq C ((hhigh_mem_iff C).mpr ⟨subset_rfl, hsC⟩)] at hw₆_val
  have helse_ex := he_w0.seq (he_ghigh.seq (he_flip.seq (he_w3.seq
    (he_qtr.seq (he_w5.seq he_get)))))
  obtain ⟨n_el, hn_el, hex_el⟩ := helse_ex
  rw [hys_len, hhigh_len] at hn_el
  refine ⟨w₆, ⟨n_el + 2, longBranch_budget_le hH_pos1 hcList_le_d hHq_le hn_el,
    Exec.branch_neg hcond hex_el⟩, hw₆_val,
    fun a ha => (congrFun (hw₆_mem.trans hw₅_mem) a).trans (hw₄_below_qw a ha)⟩

theorem exec_queryStep {w d s baseFree outBase rootF rootG qPtr preFs preGs preHs
    W H_pos spVal : ℕ}
    {fnF fnG preOutFn : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    {initMem preMem : ℕ → ℕ}
    (hob_gt_bf : baseFree < outBase)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), initMem (qPtr + j) = setMask Cs[j])
    (hpre_below_bf : ∀ a < baseFree, preMem a = initMem a)
    (htrieF : HoldsTrie initMem baseFree d rootF fnF)
    (htrieG : HoldsTrie initMem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hpFs_lt : preFs + d < outBase) (hpGs_lt : preGs + d < outBase)
    (hpHs_lt : preHs + d < outBase)
    (hpreF_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preFs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y))
    (hpreG_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preGs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y))
    (hpreH_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preHs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
          (fun S => subsetZeta f S * subsetZeta g S) Y))
    (hpreOut_tr : HoldsTrie preMem outBase d (preMem (preHs + d)) preOutFn)
    (hpreOut_eq : ∀ Y : Finset (Fin d), #Y ≤ s →
      preOutFn (setMask Y) = Signed.encode (coveringProduct f g Y))
    (hH_pos1 : 1 ≤ H_pos) (hCs_H : ∀ C ∈ Cs, highCount #C s ≤ H_pos)
    (hqw_bound : outBase + 1 + Cs.length + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal)
    (hfit_space : Fits w spVal)
    (hfit_val : Fits w (valueEnvelope d W))
    (st : Data numRegs)
    (hst : QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
      (st.regs rQueryIdx) st)
    (hq : st.regs rQueryIdx < Cs.length) :
    ∃ z, ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) ∧
      QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
        (st.regs rQueryIdx + 1) z ∧
      z.regs rQueryIdx = st.regs rQueryIdx + 1 := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let qWorkStart := outBase + 1 + Cs.length
  have hf_ob : Fits w outBase := hfit_space.of_le (by omega)
  have hf_qw : Fits w qWorkStart := hfit_space.of_le (by dsimp only [qWorkStart]; omega)
  generalize hq_eq : st.regs rQueryIdx = q at hst hq ⊢
  dsimp only [QueryInv] at hst
  obtain ⟨hsz, hso, hsd, hss, hsout, hspf, hstF, hstG, hsqp, hsqc,
    hspFs, hspGs, hspHs, hs_pre, hs_ob, hs_ans⟩ := hst
  generalize hC_def : Cs[q] = C
  have hC_mem : C ∈ Cs := hC_def ▸ List.getElem_mem hq
  have hread_q : st.mem (qPtr + q) = setMask C := by
    rw [hs_pre _ (by omega), hpre_below_bf _ (by omega), ← hC_def]; exact hq_mem q hq
  have hf_qp_q : Fits w (qPtr + q) := hfit_space.of_le (by omega)
  have hf_qw_d : Fits w (qWorkStart + d) := hfit_space.of_le (by dsimp only [qWorkStart]; omega)
  have hq0_st : ∃ u₀, ExecWithin w qLoadCode st u₀ 5 ∧
      u₀.regs rTrieKey = setMask C ∧ u₀.regs rCoordsPtr = qWorkStart ∧
      u₀.regs Reg.free = qWorkStart + d ∧ u₀.mem = st.mem := by
    unfold qLoadCode
    wram_exec [hspf, hsqp, hq_eq, hsd, hread_q]
    wram_simp [hread_q, qWorkStart]
  obtain ⟨u₀, he_q0, hu₀_key, hu₀_cp, hu₀_fr, hu₀_mem⟩ := hq0_st
  have hu₀_regs : ∀ i, i ≠ Reg.free ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr →
      u₀.regs i = st.regs i :=
    fun i hi => he_q0.regs_eq (qLoadCode_preserves i hi)
  obtain ⟨u₁, he_ext, hu₁_clen, hu₁_cmem, hu₁_cfr, hu₁_regs⟩ :=
    exec_extractCoords C u₀
      ((hu₀_regs rZero (by decide)).trans hsz)
      ((hu₀_regs rOne (by decide)).trans hso)
      ((hu₀_regs Reg.dim (by decide)).trans hsd)
      hu₀_key hu₀_cp hf_qw_d hfit_mask
  have hcList_nd_raw : ((List.finRange d).filter (· ∈ C)).Nodup :=
    (List.nodup_finRange d).filter _
  have hcList_tf_raw : ((List.finRange d).filter (· ∈ C)).toFinset = C := by ext i; simp
  generalize hcList_def : (List.finRange d).filter (· ∈ C) = cList
    at hu₁_clen hu₁_cmem hcList_nd_raw hcList_tf_raw
  have hcList_nd : cList.Nodup := hcList_nd_raw
  have hcList_toFinset : cList.toFinset = C := hcList_tf_raw
  have hcList_len : cList.length = #C := by
    rw [← List.toFinset_card_of_nodup hcList_nd, hcList_toFinset]
  rw [hcList_len] at hu₁_clen
  have keep_u₁ (i : Fin numRegs)
      (h1 : i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp)
      (h0 : i ≠ Reg.free ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr) :
      u₁.regs i = st.regs i :=
    (hu₁_regs i h1).trans (hu₀_regs i h0)
  have u₁_below_qw : ∀ a < qWorkStart, u₁.mem a = st.mem a :=
    fun a ha => (hu₁_cfr a (Or.inl ha)).trans (congrFun hu₀_mem a)
  have u₁_below_ob : ∀ a < outBase, u₁.mem a = preMem a :=
    fun a ha => (u₁_below_qw a (by dsimp only [qWorkStart]; omega)).trans (hs_pre a ha)
  have hu₁_s : u₁.regs Reg.thresh = s := (keep_u₁ Reg.thresh (by decide) (by decide)).trans hss
  have hbr_eval : ∃ u_ans,
      ExecWithin w qBranchCode u₁ u_ans
        (180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3)) ∧
      u_ans.regs rTrieVal = Signed.encode (coveringProduct f g C) ∧
      (∀ a < qWorkStart, u_ans.mem a = st.mem a) := by
    by_cases hlt_Cs : #C < s
    · have hcond : (Cond.lt rCoordsLen Reg.thresh).Holds u₁ := by
        simp [Cond.holds_lt, hu₁_clen, hu₁_s, hlt_Cs]
      have hf_phs_d : Fits w (preHs + d) := hfit_space.of_le (by omega)
      have hu₁_pHs : u₁.regs rPreHsBase = preHs :=
        (keep_u₁ rPreHsBase (by decide) (by decide)).trans hspHs
      have hu₁_d : u₁.regs Reg.dim = d :=
        (keep_u₁ Reg.dim (by decide) (by decide)).trans hsd
      have hread_phs : u₁.mem (preHs + d) = preMem (preHs + d) :=
        u₁_below_ob _ hpHs_lt
      have hst0 : ∃ v₀, ExecWithin w qShortLoadCode u₁ v₀ 2 ∧
          v₀.regs rTrieRoot = preMem (preHs + d) ∧ v₀.mem = u₁.mem := by
        unfold qShortLoadCode
        wram_exec [hu₁_pHs, hu₁_d, hread_phs]
        wram_simp [hread_phs]
      obtain ⟨v₀, he_ld, hv₀_root, hv₀_mem⟩ := hst0
      have hv₀_regs : ∀ i, i ≠ rGenTmp ∧ i ≠ rTrieRoot → v₀.regs i = u₁.regs i :=
        fun i hi => he_ld.regs_eq (qShortLoadCode_preserves i hi)
      have htr_v₀ : HoldsTrie v₀.mem outBase d (preMem (preHs + d)) preOutFn := by
        rw [hv₀_mem]; exact hpreOut_tr.congr_below u₁_below_ob
      have hv₀_key : v₀.regs rTrieKey = setMask C :=
        (hv₀_regs rTrieKey (by decide)).trans ((hu₁_regs rTrieKey (by decide)).trans hu₀_key)
      obtain ⟨v₁, he_get, hv₁_val, hv₁_mem, _⟩ :=
        exec_trieGet v₀
          ((hv₀_regs rZero (by decide)).trans
            ((keep_u₁ rZero (by decide) (by decide)).trans hsz))
          ((hv₀_regs rOne (by decide)).trans
            ((keep_u₁ rOne (by decide) (by decide)).trans hso))
          ((hv₀_regs Reg.dim (by decide)).trans hu₁_d)
          hv₀_root hv₀_key htr_v₀ hf_ob hfit_d (hfit_mask.of_le (setMask_lt C).le)
      rw [hpreOut_eq C (by omega)] at hv₁_val
      obtain ⟨n_b, hn_b, hex_b⟩ := he_ld.seq he_get
      refine ⟨v₁, ⟨n_b + 1, shortBranch_budget_le hH_pos1 hn_b,
        Exec.branch_pos hcond hex_b⟩, hv₁_val,
        fun a ha => (congrFun (hv₁_mem.trans hv₀_mem) a).trans (u₁_below_qw a ha)⟩
    · exact exec_qLongBranch u₁
        ((keep_u₁ rZero (by decide) (by decide)).trans hsz)
        ((keep_u₁ rOne (by decide) (by decide)).trans hso)
        ((keep_u₁ Reg.dim (by decide) (by decide)).trans hsd)
        hu₁_s
        ((hu₁_regs rTrieKey (by decide)).trans hu₀_key)
        ((hu₁_regs rCoordsPtr (by decide)).trans hu₀_cp)
        hu₁_clen
        ((hu₁_regs Reg.free (by decide)).trans hu₀_fr)
        ((keep_u₁ Reg.trieF (by decide) (by decide)).trans hstF)
        ((keep_u₁ Reg.trieG (by decide) (by decide)).trans hstG)
        ((keep_u₁ Reg.queryPtr (by decide) (by decide)).trans hsqp)
        ((keep_u₁ rQueryIdx (by decide) (by decide)).trans hq_eq)
        ((keep_u₁ rPreFsBase (by decide) (by decide)).trans hspFs)
        ((keep_u₁ rPreGsBase (by decide) (by decide)).trans hspGs)
        ((keep_u₁ rPreHsBase (by decide) (by decide)).trans hspHs)
        hcList_nd hcList_toFinset hcList_len hu₁_cmem u₁_below_qw hs_pre hpre_below_bf
        hob_gt_bf (by dsimp only [qWorkStart]; omega) (by dsimp only [qWorkStart]; omega) hread_q
        htrieF htrieG hf_eq hg_eq hf_le hg_le hpFs_lt hpGs_lt hpHs_lt
        hpreF_st hpreG_st hpreH_st
        (Nat.le_of_not_lt hlt_Cs) hH_pos1 (hCs_H C hC_mem) hqw_bound hfit_space hfit_val
  obtain ⟨u_ans, he_br, hu_val, hu_below⟩ := hbr_eval
  have hu_one : u_ans.regs rOne = 1 :=
    (he_br.regs_eq qBranchCode_preserves_one).trans
      ((keep_u₁ rOne (by decide) (by decide)).trans hso)
  have hu_out : u_ans.regs Reg.outPtr = outBase :=
    (he_br.regs_eq qBranchCode_preserves_out).trans
      ((keep_u₁ Reg.outPtr (by decide) (by decide)).trans hsout)
  have hu_qi : u_ans.regs rQueryIdx = q :=
    (he_br.regs_eq qBranchCode_preserves_qi).trans
      ((keep_u₁ rQueryIdx (by decide) (by decide)).trans hq_eq)
  have hf_q1 : Fits w (q + 1) := hfit_space.of_le (by omega)
  have hf_out_q1 : Fits w (outBase + (q + 1)) := hf_qw.of_le (by dsimp only [qWorkStart]; omega)
  have hst_w : ∃ z, ExecWithin w qWriteCode u_ans z 3 ∧
      z.regs rQueryIdx = q + 1 ∧
      z.mem = Function.update u_ans.mem (outBase + (q + 1))
        (Signed.encode (coveringProduct f g C)) := by
    unfold qWriteCode
    wram_exec [hu_qi, hu_one, hu_out, hu_val]
    wram_simp
  obtain ⟨z, he_wr, hz_qi, hz_mem⟩ := hst_w
  have hpt_pos := queryStep_base_le (d := d) hH_pos1
  have hqstep_tot : ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) :=
    (he_q0.seq (he_ext.seq (he_br.seq he_wr))).mono (by omega)
  have kq (i : Fin numRegs) (hi : IsQueryKept i) : z.regs i = st.regs i :=
    hqstep_tot.regs_eq (queryStep_preserves i hi)
  refine ⟨z, hqstep_tot, ?_, hz_qi⟩
  dsimp only [QueryInv]
  refine ⟨(kq rZero (by decide)).trans hsz,
    (kq rOne (by decide)).trans hso,
    (kq Reg.dim (by decide)).trans hsd,
    (kq Reg.thresh (by decide)).trans hss,
    (kq Reg.outPtr (by decide)).trans hsout,
    (kq rPreFree (by decide)).trans hspf,
    (kq Reg.trieF (by decide)).trans hstF,
    (kq Reg.trieG (by decide)).trans hstG,
    (kq Reg.queryPtr (by decide)).trans hsqp,
    (kq Reg.queryCount (by decide)).trans hsqc,
    (kq rPreFsBase (by decide)).trans hspFs,
    (kq rPreGsBase (by decide)).trans hspGs,
    (kq rPreHsBase (by decide)).trans hspHs,
    ?_, ?_, ?_⟩
  · intro a ha
    rw [hz_mem, Function.update_of_ne (by omega),
      hu_below a (by dsimp only [qWorkStart]; omega)]
    exact hs_pre a ha
  · rw [hz_mem, Function.update_of_ne (by omega),
      hu_below outBase (by dsimp only [qWorkStart]; omega)]
    exact hs_ob
  · intro j hj hj_lt
    by_cases hjq : j = q
    · subst hjq
      have : outBase + 1 + j = outBase + (j + 1) := by omega
      rw [this, hz_mem, Function.update_self, ← hC_def]
    · rw [hz_mem, Function.update_of_ne (by omega),
        hu_below (outBase + 1 + j) (by dsimp only [qWorkStart]; omega)]
      exact hs_ans j hj (by omega)

end Cslib.Algorithms.WordRAM.TrimmedYates
