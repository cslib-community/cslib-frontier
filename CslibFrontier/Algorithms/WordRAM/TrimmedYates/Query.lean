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
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

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
  unfold tripleSpace; gcongr

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
  have : cl * (20 * H_q + 12) + tripleTime d H_q ≤ d * (20 * H_pos + 12) + tripleTime d H_pos := by
    unfold tripleTime; gcongr
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

private theorem qBranchCode_preserves_one : qBranchCode.Preserves rOne := by
  apply qBranchCode_preserves <;> decide
private theorem qBranchCode_preserves_out : qBranchCode.Preserves Reg.outPtr := by
  apply qBranchCode_preserves <;> decide
private theorem qBranchCode_preserves_qi : qBranchCode.Preserves rQueryIdx := by
  apply qBranchCode_preserves <;> decide

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
  refine ⟨qLoadCode_preserves i ?_, extractCoords_preserves i ?_,
    qBranchCode_preserves i ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩ <;> revert i hi <;> decide +kernel

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
  have hcList_le_d : cList.length ≤ d := hcList_len ▸ by simpa using Finset.card_le_univ C
  obtain ⟨H_q, hHq_def⟩ : ∃ H_q, highCount #C s = H_q := ⟨_, rfl⟩
  have hHq_le : H_q ≤ H_pos := hHq_def ▸ hC_H
  have hts_mono : tripleSpace d H_q ≤ tripleSpace d H_pos := tripleSpace_mono hHq_le
  have hsum_Hq : ∑ j ∈ range (#C - s + 1), cList.length.choose j = H_q := by
    rw [hcList_len, sum_range_sub_eq_highCount hsC, hHq_def]
  -- Enumerate the subsets `Y ⊆ C` with `#Y ≤ #C - s` and complement them in `C`.
  let w₀ := (u₁.set rMaxCard (#C - s)).set rDomPtr (qWorkStart + d)
  have he_w0 : ExecWithin (B := .standard) w
      (ram[ rMaxCard ← rCoordsLen - Reg.thresh; rDomPtr ← Reg.free ]) u₁ w₀ 2 := by
    wram_exec [hclen, hs_reg, hfr]
  obtain ⟨w₁, he_low, hw₁_dlen, hw₁_dom, hw₁_fr, hw₁_regs⟩ :=
    exec_genLowSubsets cList w₀ (by regs_frame) (by regs_frame) (by regs_frame)
      (by rw [hcList_len]; regs_frame) (by regs_frame) (by regs_frame) hcList_nd hcmem (by omega)
      (by rw [hsum_Hq]; exact hfit_space.of_le (by omega)) hfit_mask
  have hys_spec := prefixesUpTo_spec (#C - s) hcList_nd
  have hys_len : (prefixesUpTo (#C - s) cList).length = H_q := by
    rw [length_prefixesUpTo (#C - s) hcList_nd, hsum_Hq]
  generalize prefixesUpTo (#C - s) cList = ys at hw₁_dlen hw₁_dom hys_spec hys_len
  have hys_sub : ∀ Y ∈ ys, Y ⊆ C := fun Y hY => hcList_tf ▸ ((hys_spec.2 Y).mp hY).1
  obtain ⟨w₂, he_flip, hw₂_dom, hw₂_fr, hw₂_regs⟩ :=
    exec_flipHighDom C ys w₁ (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      hw₁_dlen hys_sub hw₁_dom (by rw [hys_len]; exact hfit_space.of_le (by omega)) hfit_mask
  have hhigh_len : (ys.map (C \ ·)).length = H_q := by simp [hys_len]
  have hhigh_nd : (ys.map (C \ ·)).Nodup := hys_spec.1.map_on fun Y₁ h₁ Y₂ h₂ heq => by
    rw [← Finset.sdiff_sdiff_eq_self (hys_sub Y₁ h₁), heq,
      Finset.sdiff_sdiff_eq_self (hys_sub Y₂ h₂)]
  have hhigh_mem : ∀ X, X ∈ ys.map (C \ ·) ↔ X ⊆ C ∧ s ≤ #X := by
    intro X
    simp only [List.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have := ((hys_spec.2 Y).mp hY).2
      rw [Finset.card_sdiff_of_subset (hys_sub Y hY)]
      exact ⟨sdiff_subset, by omega⟩
    · rintro ⟨hXC, hsX⟩
      refine ⟨C \ X, (hys_spec.2 _).mpr ⟨hcList_tf ▸ sdiff_subset, ?_⟩,
        Finset.sdiff_sdiff_eq_self hXC⟩
      rw [Finset.card_sdiff_of_subset hXC]; omega
  -- Run the three high-domain Yates transforms with the precomputed low stages as fallback.
  obtain ⟨w₃, he_w3, hw₃_dp, hw₃_dl, hw₃_fr, hw₃_cut, hw₃_mem⟩ :
      ∃ w₃, ExecWithin w qHighPrepCode w₂ w₃ 5 ∧ w₃.regs Reg.entryPtr = qWorkStart + d ∧
        w₃.regs Reg.entryCount = H_q ∧ w₃.regs Reg.free = qWorkStart + d + 2 * H_q ∧
        w₃.regs rStageCutoff = s ∧ w₃.mem = w₂.mem := by
    unfold qHighPrepCode
    wram_exec *
    wram_simp [hys_len]; omega
  have hw₃_below : ∀ a < qWorkStart, w₃.mem a = stMem a := fun a ha => by
    rw [hw₃_mem, hw₂_fr a (.inl (by omega)), hw₁_fr a (.inl (by omega))]
    exact hu₁_below_qw a ha
  have hw₃_ob : ∀ a < outBase, w₃.mem a = preMem a := fun a ha =>
    (hw₃_below a (by omega)).trans (hs_pre a ha)
  have hw₃_bf : ∀ a < baseFree, w₃.mem a = initMem a := fun a ha =>
    (hw₃_ob a (by omega)).trans (hpre_below_bf a ha)
  have hfb : ∀ base (G : ℕ → Finset (Fin d) → ℤ), base + d < outBase →
      (∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (base + k)) stFn ∧
        ∀ Y : Finset (Fin d), #Y ≤ s → stFn (setMask Y) = Signed.encode (G k Y)) →
      ∀ k < d, ∃ fbFn, HoldsTrie w₃.mem (qWorkStart + d + 2 * H_q) d (w₃.mem (base + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s → fbFn (setMask Y) = Signed.encode (G k Y) := by
    intro base G hb h k hk
    obtain ⟨fbFn, htr, heq⟩ := h k hk.le
    exact ⟨fbFn, ((htr.congr_below hw₃_ob).mono_bound (by omega)).congr_root
      (hw₃_ob _ (by omega)), fun Y _ => heq Y⟩
  obtain ⟨w₄, -, -, qHs, qEndFree, he_qtr, -, -, hw₄_ro, -, -, hqef_hi, -, -, hqHs_lt, -, -, -,
      ⟨qOutFn, hqOut_tr, hqOut_eq⟩, hw₄_fr, hw₄_regs⟩ :=
    exec_runTransformTriple (P_low := fun Y => #Y ≤ s) (W := W) w₃ (by regs_frame)
      (by regs_frame) (by regs_frame) hw₃_dp (by rw [hhigh_len]; exact hw₃_dl) hw₃_cut
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) hw₃_fr
      (by omega) hhigh_nd (by rwa [hw₃_mem]) (by omega)
      (fun X hX coord _ => ⟨fun h => (hhigh_mem _).mpr
        ⟨(erase_subset _ _).trans ((hhigh_mem X).mp hX).1, h⟩, le_of_lt⟩)
      ((htrieF.congr_below hw₃_bf).mono_bound (by omega))
      ((htrieG.congr_below hw₃_bf).mono_bound (by omega)) hf_eq hg_eq hf_le hg_le
      (fun _ => ⟨by omega, by omega, by omega, hfb _ _ hpFs_lt hpreF_st,
        hfb _ _ hpGs_lt hpreG_st, hfb _ _ hpHs_lt hpreH_st⟩)
      hfit_val (by rw [hhigh_len]; exact hfit_space.of_le (by omega))
  -- Look up `C` in the output trie.
  rw [hhigh_len] at hqef_hi
  have hf_qef : Fits w qEndFree := hfit_space.of_le (by omega)
  have hf_qhs_d : Fits w (qHs + d) := hf_qef.of_le (by omega)
  have hw₄_below : ∀ a < qWorkStart, w₄.mem a = stMem a := fun a ha =>
    (hw₄_fr a (.inl (by omega))).trans (hw₃_below a ha)
  have hw₄_read_q : w₄.mem (qPtr + q) = setMask C := (hw₄_below _ hq_lt).trans hread_q
  obtain ⟨w₅, he_w5, hw₅_key, hw₅_root, hw₅_mem⟩ : ∃ w₅, ExecWithin w qHighReadCode w₄ w₅ 4 ∧
      w₅.regs rTrieKey = setMask C ∧ w₅.regs rTrieRoot = w₄.mem (qHs + d) ∧ w₅.mem = w₄.mem := by
    unfold qHighReadCode
    wram_exec * [hw₄_read_q]
    wram_simp
  obtain ⟨w₆, he_get, hw₆_val, hw₆_mem, -⟩ :=
    exec_trieGet w₅ (by regs_frame) (by regs_frame) (by regs_frame) hw₅_root hw₅_key
      (by rwa [hw₅_mem]) hf_qef hfit_d (hfit_mask.of_le (setMask_lt C).le)
  rw [hqOut_eq C ((hhigh_mem C).mpr ⟨subset_rfl, hsC⟩)] at hw₆_val
  obtain ⟨n_el, hn_el, hex_el⟩ :=
    he_w0.seq (he_low.seq (he_flip.seq (he_w3.seq (he_qtr.seq (he_w5.seq he_get)))))
  rw [hsum_Hq, hys_len, hhigh_len] at hn_el
  refine ⟨w₆, ⟨n_el + 2, longBranch_budget_le hH_pos1 hcList_le_d hHq_le hn_el,
    Exec.branch_neg (by simp [Cond.holds_lt, hclen, hs_reg, hsC]) hex_el⟩, hw₆_val, fun a ha => ?_⟩
  rw [hw₆_mem, hw₅_mem]
  exact hw₄_below a ha

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
  have hf_ob : Fits w outBase := hfit_space.of_le (by omega)
  obtain ⟨qWorkStart, hqw⟩ : ∃ n, n = outBase + 1 + Cs.length := ⟨_, rfl⟩
  rw [← hqw] at hqw_bound
  generalize hq_eq : st.regs rQueryIdx = q at hst hq ⊢
  obtain ⟨hsz, hso, hsd, hss, hsout, hspf, hstF, hstG, hsqp, hsqc,
    hspFs, hspGs, hspHs, hs_pre, hs_ob, hs_ans⟩ := hst
  rw [← hqw] at hspf
  generalize hC_def : Cs[q] = C
  have hC_mem : C ∈ Cs := hC_def ▸ List.getElem_mem hq
  have hread_q : st.mem (qPtr + q) = setMask C := by
    rw [hs_pre _ (by omega), hpre_below_bf _ (by omega), ← hC_def]; exact hq_mem q hq
  have hf_qp_q : Fits w (qPtr + q) := hfit_space.of_le (by omega)
  have hf_qw_d : Fits w (qWorkStart + d) := hfit_space.of_le (by omega)
  -- Load the query mask and extract its coordinates.
  obtain ⟨u₀, he_q0, hu₀_key, hu₀_cp, hu₀_fr, hu₀_mem⟩ : ∃ u₀, ExecWithin w qLoadCode st u₀ 5 ∧
      u₀.regs rTrieKey = setMask C ∧ u₀.regs rCoordsPtr = qWorkStart ∧
      u₀.regs Reg.free = qWorkStart + d ∧ u₀.mem = st.mem := by
    unfold qLoadCode
    wram_exec [hspf, hsqp, hq_eq, hsd, hread_q]
    wram_simp [hread_q]
  obtain ⟨u₁, he_ext, hu₁_clen, hu₁_cmem, hu₁_cfr, hu₁_regs⟩ :=
    exec_extractCoords C u₀ (by regs_frame) (by regs_frame) (by regs_frame) hu₀_key hu₀_cp hf_qw_d
      hfit_mask
  generalize hcList_def : (List.finRange d).filter (· ∈ C) = cList at hu₁_clen hu₁_cmem
  have hcList_nd : cList.Nodup := hcList_def ▸ (List.nodup_finRange d).filter _
  have hcList_tf : cList.toFinset = C := by rw [← hcList_def]; ext; simp
  have hcList_len : cList.length = #C := by
    rw [← List.toFinset_card_of_nodup hcList_nd, hcList_tf]
  rw [hcList_len] at hu₁_clen
  have hu₁_below : ∀ a < qWorkStart, u₁.mem a = st.mem a :=
    fun a ha => (hu₁_cfr a (.inl ha)).trans (congrFun hu₀_mem a)
  have hu₁_ob : ∀ a < outBase, u₁.mem a = preMem a :=
    fun a ha => (hu₁_below a (by omega)).trans (hs_pre a ha)
  have hu₁_s : u₁.regs Reg.thresh = s := by regs_frame
  -- Answer the query: by one lookup when `#C < s`, by the high-domain transforms otherwise.
  have hbr : ∃ u_ans, ExecWithin w qBranchCode u₁ u_ans
        (180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3)) ∧
      u_ans.regs rTrieVal = Signed.encode (coveringProduct f g C) ∧
      (∀ a < qWorkStart, u_ans.mem a = st.mem a) := by
    by_cases hlt_Cs : #C < s
    · obtain ⟨v₀, he_ld, hv₀_root, hv₀_mem⟩ : ∃ v₀, ExecWithin w qShortLoadCode u₁ v₀ 2 ∧
          v₀.regs rTrieRoot = preMem (preHs + d) ∧ v₀.mem = u₁.mem := by
        have hf_phs_d : Fits w (preHs + d) := hfit_space.of_le (by omega)
        unfold qShortLoadCode
        wram_exec * [hu₁_ob _ hpHs_lt]
        wram_simp [hu₁_ob _ hpHs_lt]
      obtain ⟨v₁, he_get, hv₁_val, hv₁_mem, -⟩ :=
        exec_trieGet v₀ (by regs_frame) (by regs_frame) (by regs_frame) hv₀_root (by regs_frame)
          (hv₀_mem ▸ hpreOut_tr.congr_below hu₁_ob) hf_ob hfit_d (hfit_mask.of_le (setMask_lt C).le)
      rw [hpreOut_eq C (by omega)] at hv₁_val
      obtain ⟨n_b, hn_b, hex_b⟩ := he_ld.seq he_get
      refine ⟨v₁, ⟨n_b + 1, shortBranch_budget_le hH_pos1 hn_b,
        Exec.branch_pos (by simp [Cond.holds_lt, hu₁_clen, hu₁_s, hlt_Cs]) hex_b⟩, hv₁_val,
        fun a ha => ?_⟩
      rw [hv₁_mem, hv₀_mem]
      exact hu₁_below a ha
    · exact exec_qLongBranch u₁ (by regs_frame) (by regs_frame) (by regs_frame) hu₁_s
        (by regs_frame) (by regs_frame) hu₁_clen (by regs_frame) (by regs_frame) (by regs_frame)
        (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
        hcList_nd hcList_tf hcList_len hu₁_cmem hu₁_below hs_pre hpre_below_bf hob_gt_bf
        (by omega) (by omega) hread_q htrieF htrieG hf_eq hg_eq hf_le hg_le hpFs_lt hpGs_lt hpHs_lt
        hpreF_st hpreG_st hpreH_st (by omega) hH_pos1 (hCs_H C hC_mem) hqw_bound hfit_space
        hfit_val
  -- Write the answer and advance the query index.
  obtain ⟨u_ans, he_br, hu_val, hu_below⟩ := hbr
  have hu_one : u_ans.regs rOne = 1 :=
    (he_br.regs_eq qBranchCode_preserves_one).trans (by regs_frame)
  have hu_out : u_ans.regs Reg.outPtr = outBase :=
    (he_br.regs_eq qBranchCode_preserves_out).trans (by regs_frame)
  have hu_qi : u_ans.regs rQueryIdx = q :=
    (he_br.regs_eq qBranchCode_preserves_qi).trans (by regs_frame)
  have hf_q1 : Fits w (q + 1) := hfit_space.of_le (by omega)
  have hf_out_q1 : Fits w (outBase + (q + 1)) := hfit_space.of_le (by omega)
  obtain ⟨z, he_wr, hz_qi, hz_mem⟩ : ∃ z, ExecWithin w qWriteCode u_ans z 3 ∧
      z.regs rQueryIdx = q + 1 ∧
      z.mem = Function.update u_ans.mem (outBase + (q + 1))
        (Signed.encode (coveringProduct f g C)) := by
    unfold qWriteCode
    wram_exec [hu_qi, hu_one, hu_out, hu_val]
    wram_simp
  have hqstep_tot : ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) :=
    (he_q0.seq (he_ext.seq (he_br.seq he_wr))).mono
      (by have := queryStep_base_le (d := d) hH_pos1; omega)
  have kq (i : Fin numRegs) (hi : IsQueryKept i) : z.regs i = st.regs i :=
    hqstep_tot.regs_eq (queryStep_preserves i hi)
  refine ⟨z, hqstep_tot, ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, fun a ha => ?_, ?_, fun j hj hj_lt => ?_⟩, hz_qi⟩
  · rw [hz_mem, Function.update_of_ne (by omega), hu_below a (by omega)]
    exact hs_pre a ha
  · rw [hz_mem, Function.update_of_ne (by omega), hu_below outBase (by omega)]
    exact hs_ob
  · by_cases hjq : j = q
    · subst hjq
      rw [show outBase + 1 + j = outBase + (j + 1) by omega, hz_mem, Function.update_self, ← hC_def]
    · rw [hz_mem, Function.update_of_ne (by omega), hu_below _ (by omega)]
      exact hs_ans j hj (by omega)

end Cslib.Algorithms.WordRAM.TrimmedYates
