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
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Low-cardinality preprocessing for trimmed Yates on the word RAM

Enumerates `{X ⊆ Fin d | #X ≤ s}` (`genLowSubsets` on `List.finRange d`), computes the three
stage-table families `preFs`, `preGs`, `preHs` via `runTransformTriple` at `cutoff = 0`, allocates
the length-prefixed answer array header, and establishes `QueryInv ... 0` (`preprocessCode`,
`exec_preprocessCode`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.preprocessCode`: preprocessing code block preceding the
  query loop in `solveFromTries`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.solve_total_time_le`: overall instruction budget combining
  `preprocessCode` and `nQ` iterations of `queryStep`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_preprocessCode`: `ExecWithin` specification producing
  the stage tables and initial `QueryInv` state.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

private theorem solveSpace_split {baseFree d s nQ L_low H_pk : ℕ} (hL : lowCount d s = L_low) :
    baseFree + (d + 2 * L_low + tripleSpace d L_low) + 1 + nQ +
      (d + 2 * max 1 H_pk + tripleSpace d (max 1 H_pk)) ≤
      solveSpace baseFree d s nQ H_pk := by
  have ht1 := tripleSpace_le d L_low
  have ht2 := tripleSpace_le d (max 1 H_pk)
  have hhp : max 1 H_pk ≤ H_pk + 1 := by omega
  have hsq : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow 2 (d + 1) (Nat.succ_pos d)
  dsimp only [solveSpace]
  rw [hL]
  generalize (d + 1) ^ 2 = sqVal at ht1 ht2 hsq ⊢
  nlinarith

theorem solve_total_time_le {d nQ L_low H_pos : ℕ} (hL : 1 ≤ L_low) (hH : 1 ≤ H_pos) :
    4 + (5 * d + 3 + (3 + (d * (20 * L_low + 12) + 8 +
      (5 + (tripleTime d L_low + (8 + (nQ * (180 * (d + 1) ^ 2 * H_pos + 2) + 2))))))) ≤
      200 * (d + 1) ^ 2 * (L_low + nQ * H_pos) := by
  have hpre := phaseTime_le (d := d) hL
  have hsq_pos : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow 2 (d + 1) (Nat.succ_pos d)
  have hq_step : nQ * (180 * (d + 1) ^ 2 * H_pos + 2) ≤
      nQ * (200 * (d + 1) ^ 2 * H_pos) :=
    Nat.mul_le_mul_left nQ (by nlinarith)
  nlinarith

private def preSaveCode : Code .standard numRegs := ram[
  rPreFsBase ← rQFsBase;
  rPreGsBase ← rQGsBase;
  rPreHsBase ← rRootsOut;
  Reg.outPtr ← Reg.free;
  *Reg.outPtr ← Reg.queryCount;
  rPreFree ← Reg.free + rOne;
  rPreFree ← rPreFree + Reg.queryCount;
  rQueryIdx ← #0 ]

private theorem preSaveCode_preserves (i : Fin numRegs) :
    i ≠ rPreFsBase ∧ i ≠ rPreGsBase ∧ i ≠ rPreHsBase ∧
      i ≠ Reg.outPtr ∧ i ≠ rPreFree ∧ i ≠ rQueryIdx → preSaveCode.Preserves i := by
  decide +kernel +revert

private def solvePreStageCode : Code .standard numRegs := ram[
  Reg.entryPtr ← rDomPtr;
  Reg.entryCount ← rDomLen;
  rGenTmp ← rDomLen + rDomLen;
  Reg.free ← rDomPtr + rGenTmp;
  rStageCutoff ← #0 ]

private theorem solvePreStageCode_preserves (i : Fin numRegs) :
    i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff →
      solvePreStageCode.Preserves i := by
  decide +kernel +revert

/-- Preprocessing phase of `solveFromTries`: enumerate all subsets of `Fin d` of size at most `s`,
run `runTransformTriple` at `cutoff = 0`, and initialize the output array header and query index. -/
def preprocessCode : Code .standard numRegs :=
  .seq (ram[
    rZero ← #0;
    rOne ← #1;
    rCoordsPtr ← Reg.free;
    Reg.free ← Reg.free + Reg.dim ])
  (.seq initIdentityCoords
    (.seq (ram[
        rCoordsLen ← Reg.dim;
        rMaxCard ← Reg.thresh;
        rDomPtr ← Reg.free ])
      (.seq genLowSubsets
        (.seq solvePreStageCode
          (.seq runTransformTriple preSaveCode)))))

theorem exec_preprocessCode {w d s baseFree rootF rootG qPtr W : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    (x : Data numRegs)
    (hd : x.regs Reg.dim = d) (hs : x.regs Reg.thresh = s)
    (hfree : x.regs Reg.free = baseFree)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hqptr : x.regs Reg.queryPtr = qPtr) (hqcnt : x.regs Reg.queryCount = Cs.length)
    (htrieF : HoldsTrie x.mem baseFree d rootF fnF)
    (htrieG : HoldsTrie x.mem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hfit_space : Fits w (solveSpace baseFree d s Cs.length (highPeak s Cs)))
    (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ s₆ preMem outBase preFs preGs preHs preOutFn,
      ExecWithin w preprocessCode x s₆
        (4 + (5 * d + 3 + (3 + (d * (20 * lowCount d s + 12) + 8 +
          (5 + (tripleTime d (lowCount d s) + 8)))))) ∧
      baseFree < outBase ∧
      outBase + 1 + Cs.length +
        (d + 2 * max 1 (highPeak s Cs) + tripleSpace d (max 1 (highPeak s Cs))) ≤
        solveSpace baseFree d s Cs.length (highPeak s Cs) ∧
      Fits w (outBase + 1 + Cs.length) ∧
      (∀ a < baseFree, preMem a = x.mem a) ∧
      (preFs + d < outBase ∧ preGs + d < outBase ∧ preHs + d < outBase) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preFs + k)) stFn ∧
        ∀ Y : Finset (Fin d), #Y ≤ s →
          stFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preGs + k)) stFn ∧
        ∀ Y : Finset (Fin d), #Y ≤ s →
          stFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preHs + k)) stFn ∧
        ∀ Y : Finset (Fin d), #Y ≤ s →
          stFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
            (fun S => subsetZeta f S * subsetZeta g S) Y)) ∧
      HoldsTrie preMem outBase d (preMem (preHs + d)) preOutFn ∧
      (∀ Y : Finset (Fin d), #Y ≤ s →
        preOutFn (setMask Y) = Signed.encode (coveringProduct f g Y)) ∧
      s₆.regs rQueryIdx = 0 ∧
      QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
        (s₆.regs rQueryIdx) s₆ := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  obtain ⟨L_low, hL_low_def⟩ : ∃ L_low, lowCount d s = L_low := ⟨_, rfl⟩
  obtain ⟨H_pk, hH_pk_def⟩ : ∃ H_pk, highPeak s Cs = H_pk := ⟨_, rfl⟩
  rw [hH_pk_def] at hfit_space
  obtain ⟨H_pos, hH_pos_def⟩ : ∃ H_pos, max 1 H_pk = H_pos := ⟨_, rfl⟩
  have hL_pos : 1 ≤ L_low := hL_low_def ▸ lowCount_pos d s
  have hH_pos1 : 1 ≤ H_pos := hH_pos_def ▸ le_max_left 1 H_pk
  have hH_pk_le : H_pk ≤ H_pos := hH_pos_def ▸ le_max_right 1 H_pk
  have hCs_H : ∀ C ∈ Cs, highCount #C s ≤ H_pos :=
    fun C hC => (hH_pk_def ▸ le_highPeak_of_mem s hC).trans hH_pk_le
  have hsp_bound : baseFree + (d + 2 * L_low + tripleSpace d L_low) + 1 + Cs.length +
      (d + 2 * H_pos + tripleSpace d H_pos) ≤
      solveSpace baseFree d s Cs.length H_pk := by
    rw [← hH_pos_def]
    exact solveSpace_split hL_low_def
  obtain ⟨spVal, hsp_val⟩ : ∃ spVal, solveSpace baseFree d s Cs.length H_pk = spVal := ⟨_, rfl⟩
  rw [hsp_val] at hfit_space hsp_bound
  -- Step 1: allocate coordsBuf [baseFree, baseFree + d)
  let lowDomBase := baseFree + d
  have hf_ldb : Fits w (baseFree + d) := hfit_space.of_le (by omega)
  have hsetup0 : ∃ s₀, ExecWithin (B := .standard) w (ram[
      rZero ← #0;
      rOne ← #1;
      rCoordsPtr ← Reg.free;
      Reg.free ← Reg.free + Reg.dim ]) x s₀ 4 ∧
      s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧ s₀.regs Reg.dim = d ∧ s₀.regs Reg.thresh = s ∧
      s₀.regs rCoordsPtr = baseFree ∧ s₀.regs Reg.free = lowDomBase ∧
      s₀.regs Reg.trieF = rootF ∧ s₀.regs Reg.trieG = rootG ∧
      s₀.regs Reg.queryPtr = qPtr ∧ s₀.regs Reg.queryCount = Cs.length ∧
      s₀.mem = x.mem := by
    wram_exec [hd, hfree]
    wram_simp [hd, hs, hfree, htF_reg, htG_reg, hqptr, hqcnt, lowDomBase]
  obtain ⟨s₀, he_s0, hs₀z, hs₀o, hs₀d, hs₀s, hs₀cp, hs₀fr,
    hs₀tF, hs₀tG, hs₀qp, hs₀qc, hs₀mem⟩ := hsetup0
  -- Step 2: initIdentityCoords at baseFree
  obtain ⟨s₁, he_ic, hs₁_coords, hs₁_fr, hs₁_regs⟩ :=
    exec_initIdentityCoords s₀ hs₀o hs₀d hs₀cp hf_ldb hfit_d
  -- Step 3: genLowSubsets on List.finRange d at lowDomBase
  have hs₁_d : s₁.regs Reg.dim = d := (hs₁_regs Reg.dim (by decide)).trans hs₀d
  have hs₁_s : s₁.regs Reg.thresh = s := (hs₁_regs Reg.thresh (by decide)).trans hs₀s
  have hs₁_f : s₁.regs Reg.free = lowDomBase := (hs₁_regs Reg.free (by decide)).trans hs₀fr
  have hp2_st : ∃ s₂, ExecWithin (B := .standard) w
      (ram[ rCoordsLen ← Reg.dim; rMaxCard ← Reg.thresh; rDomPtr ← Reg.free ]) s₁ s₂ 3 ∧
      s₂.regs rZero = 0 ∧ s₂.regs rOne = 1 ∧ s₂.regs Reg.dim = d ∧ s₂.regs Reg.thresh = s ∧
      s₂.regs rCoordsPtr = baseFree ∧ s₂.regs rCoordsLen = d ∧ s₂.regs rMaxCard = s ∧
      s₂.regs rDomPtr = lowDomBase ∧ s₂.regs Reg.trieF = rootF ∧ s₂.regs Reg.trieG = rootG ∧
      s₂.regs Reg.queryPtr = qPtr ∧ s₂.regs Reg.queryCount = Cs.length ∧ s₂.mem = s₁.mem := by
    wram_exec [hs₁_d, hs₁_s, hs₁_f]
    refine ⟨(hs₁_regs rZero (by decide)).trans hs₀z,
      (hs₁_regs rOne (by decide)).trans hs₀o, hs₁_d, hs₁_s,
      (hs₁_regs rCoordsPtr (by decide)).trans hs₀cp, ?_, ?_, ?_,
      (hs₁_regs Reg.trieF (by decide)).trans hs₀tF,
      (hs₁_regs Reg.trieG (by decide)).trans hs₀tG,
      (hs₁_regs Reg.queryPtr (by decide)).trans hs₀qp,
      (hs₁_regs Reg.queryCount (by decide)).trans hs₀qc, ?_⟩ <;> wram_simp
  obtain ⟨s₂, he_p2, hs₂z, hs₂o, hs₂d, hs₂s, hs₂cp, hs₂cl, hs₂mc, hs₂dp,
    hs₂tF, hs₂tG, hs₂qp, hs₂qc, hs₂mem⟩ := hp2_st
  have hfr_len : (List.finRange d).length = d := List.length_finRange
  obtain ⟨s₃, he_glow_raw, hs₃_dlen, hs₃_dom, hs₃_fr, hs₃_regs⟩ :=
    exec_genLowSubsets (List.finRange d) s₂ hs₂z hs₂o hs₂cp
      (hs₂cl.trans hfr_len.symm) hs₂mc hs₂dp
      (List.nodup_finRange d) (by rwa [hs₂mem]) (by simp [lowDomBase])
      (by
        rw [hfr_len, ← lowCount, hL_low_def]
        refine hfit_space.of_le ?_
        dsimp only [lowDomBase]
        omega)
      hfit_mask
  have he_glow : ExecWithin w genLowSubsets s₂ s₃ (d * (20 * L_low + 12) + 8) := by
    rwa [hfr_len, ← lowCount, hL_low_def] at he_glow_raw
  clear he_glow_raw
  have hlow_spec_raw := prefixesUpTo_spec s (List.nodup_finRange d)
  have hlow_len_raw : (prefixesUpTo s (List.finRange d)).length = L_low := by
    rw [length_prefixesUpTo s (List.nodup_finRange d), List.length_finRange, ← lowCount, hL_low_def]
  generalize hlowDom_def : prefixesUpTo s (List.finRange d) = lowDom
    at hs₃_dlen hs₃_dom hlow_spec_raw hlow_len_raw
  have hlow_len : lowDom.length = L_low := hlow_len_raw
  have hlow_mem_iff : ∀ X : Finset (Fin d), X ∈ lowDom ↔ #X ≤ s := by
    intro X
    rw [hlow_spec_raw.2 X]
    exact ⟨fun h => h.2, fun h => ⟨by intro a _; simp, h⟩⟩
  -- Step 4: runTransformTriple on lowDom
  let preStart := lowDomBase + 2 * L_low
  have hf_2L : Fits w (L_low + L_low) :=
    hfit_space.of_le (by omega)
  have hf_ps : Fits w (lowDomBase + (L_low + L_low)) :=
    hfit_space.of_le (by dsimp only [lowDomBase]; omega)
  have hs₃_dp : s₃.regs rDomPtr = lowDomBase :=
    (hs₃_regs rDomPtr (by decide)).trans hs₂dp
  have hdl_eq : s₃.regs rDomLen = L_low := hs₃_dlen.trans hlow_len
  have hp4_st : ∃ s₄, ExecWithin w solvePreStageCode s₃ s₄ 5 ∧
      s₄.regs Reg.entryPtr = lowDomBase ∧ s₄.regs Reg.entryCount = lowDom.length ∧
      s₄.regs Reg.free = preStart ∧ s₄.regs rStageCutoff = 0 ∧ s₄.mem = s₃.mem := by
    unfold solvePreStageCode
    wram_exec [hs₃_dp, hdl_eq]
    refine ⟨rfl, hlow_len.symm, ?_, rfl, rfl⟩
    wram_simp [preStart]; omega
  obtain ⟨s₄, he_p4, hs₄_cdp, hs₄_cdl, hs₄_fr, hs₄_cut, hs₄_mem⟩ := hp4_st
  have hs₄_regs : ∀ i,
      i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff →
        s₄.regs i = s₃.regs i :=
    fun i hi => he_p4.regs_eq (solvePreStageCode_preserves i hi)
  have keep_s₄_s₂ (i : Fin numRegs)
      (h4 : i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff)
      (h3 : i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      s₄.regs i = s₂.regs i :=
    (hs₄_regs i h4).trans (hs₃_regs i h3)
  have mem_s₄_below_bf : ∀ a < baseFree, s₄.mem a = x.mem a := fun a ha => by
    rw [hs₄_mem, hs₃_fr a (Or.inl (by dsimp [lowDomBase]; omega)), hs₂mem,
      hs₁_fr a (Or.inl ha), hs₀mem]
  have htrieF_s₄ : HoldsTrie s₄.mem preStart d rootF fnF :=
    (htrieF.congr_below mem_s₄_below_bf).mono_bound (by dsimp [preStart, lowDomBase]; omega)
  have htrieG_s₄ : HoldsTrie s₄.mem preStart d rootG fnG :=
    (htrieG.congr_below mem_s₄_below_bf).mono_bound (by dsimp [preStart, lowDomBase]; omega)
  have hlow_closed : ∀ X ∈ lowDom, ∀ coord : Fin d, coord ∈ X →
      (0 ≤ #(X.erase coord) → X.erase coord ∈ lowDom) ∧
      (#(X.erase coord) < 0 → False) := by
    intro X hX coord _
    have hXs := (hlow_mem_iff X).mp hX
    exact ⟨fun _ => (hlow_mem_iff _).mpr (card_erase_le.trans hXs), by omega⟩
  have hf_pre_tr : Fits w (preStart + tripleSpace d lowDom.length) := by
    rw [hlow_len]
    exact hfit_space.of_le (by dsimp only [preStart, lowDomBase]; omega)
  obtain ⟨s₅, preFs, preGs, preHs, outBase, he_pre, hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr,
    hpf_lo, hpf_hi, hpFs_lt, hpGs_lt, hpHs_lt, hpreF_st, hpreG_st, hpreH_st,
    ⟨preOutFn, hpreOut_tr, hpreOut_eq⟩, hs₅_frame, hs₅_regs⟩ :=
    exec_runTransformTriple (preFs := s₄.regs rPreFsBase) (preGs := s₄.regs rPreGsBase)
      (preHs := s₄.regs rPreHsBase) (P_low := fun _ => False) (W := W) s₄
      ((keep_s₄_s₂ rZero (by decide) (by decide)).trans hs₂z)
      ((keep_s₄_s₂ rOne (by decide) (by decide)).trans hs₂o)
      ((keep_s₄_s₂ Reg.dim (by decide) (by decide)).trans hs₂d)
      hs₄_cdp hs₄_cdl hs₄_cut
      ((keep_s₄_s₂ Reg.trieF (by decide) (by decide)).trans hs₂tF)
      ((keep_s₄_s₂ Reg.trieG (by decide) (by decide)).trans hs₂tG)
      rfl rfl rfl hs₄_fr (by dsimp [preStart, lowDomBase]; omega)
      hlow_spec_raw.1 (by rwa [hs₄_mem]) (by rw [hlow_len])
      hlow_closed htrieF_s₄ htrieG_s₄ hf_eq hg_eq hf_le hg_le
      (fun hpos => by omega) hfit_val hf_pre_tr
  -- Step 5: allocate output array at outBase and set qWorkStart = outBase + 1 + Cs.length
  let qWorkStart := outBase + 1 + Cs.length
  have hqw_bound : qWorkStart + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal := by
    rw [hlow_len] at hpf_hi
    dsimp only [qWorkStart, preStart, lowDomBase] at hpf_hi ⊢
    omega
  have hf_ob : Fits w outBase := hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have hf_ob1 : Fits w (outBase + 1) :=
    hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have hf_qw : Fits w (outBase + 1 + Cs.length) :=
    hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have keep_s₅_s₂ (i : Fin numRegs) (h5 : ¬ IsTripleMod i)
      (h4 : i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount ∧ i ≠ rGenTmp ∧ i ≠ Reg.free ∧ i ≠ rStageCutoff)
      (h3 : i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      s₅.regs i = s₂.regs i :=
    (hs₅_regs i h5).trans (keep_s₄_s₂ i h4 h3)
  have hs₅_o : s₅.regs rOne = 1 :=
    (keep_s₅_s₂ rOne (by decide) (by decide) (by decide)).trans hs₂o
  have hs₅_qc : s₅.regs Reg.queryCount = Cs.length :=
    (keep_s₅_s₂ Reg.queryCount (by decide) (by decide) (by decide)).trans hs₂qc
  have hp5_st : ∃ s₆, ExecWithin w preSaveCode s₅ s₆ 8 ∧
      s₆.regs rPreFsBase = preFs ∧ s₆.regs rPreGsBase = preGs ∧
      s₆.regs rPreHsBase = preHs ∧ s₆.regs Reg.outPtr = outBase ∧
      s₆.regs rPreFree = qWorkStart ∧ s₆.regs rQueryIdx = 0 ∧
      s₆.mem = Function.update s₅.mem outBase Cs.length := by
    unfold preSaveCode
    wram_exec [hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr, hs₅_o, hs₅_qc]
    wram_simp [qWorkStart]
  obtain ⟨s₆, he_p5, hs₆_pFs, hs₆_pGs, hs₆_pHs, hs₆_out, hs₆_pf, hs₆_qi, hs₆_mem⟩ := hp5_st
  have hs₆_regs : ∀ i, i ≠ rPreFsBase ∧ i ≠ rPreGsBase ∧ i ≠ rPreHsBase ∧
      i ≠ Reg.outPtr ∧ i ≠ rPreFree ∧ i ≠ rQueryIdx → s₆.regs i = s₅.regs i :=
    fun i hi => he_p5.regs_eq (preSaveCode_preserves i hi)
  have s₅_below_bf : ∀ a < baseFree, s₅.mem a = x.mem a := fun a ha =>
    (hs₅_frame a (Or.inl (by dsimp [preStart, lowDomBase]; omega))).trans (mem_s₄_below_bf a ha)
  -- Step 6: query loop
  have hob_gt_bf : baseFree < outBase := by dsimp only [preStart, lowDomBase] at hpf_lo; omega
  have hs₆P : QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs s₅.mem
      (s₆.regs rQueryIdx) s₆ := by
    dsimp only [QueryInv]
    rw [hs₆_qi]
    refine ⟨(hs₆_regs rZero (by decide)).trans
        ((keep_s₅_s₂ rZero (by decide) (by decide) (by decide)).trans hs₂z),
      (hs₆_regs rOne (by decide)).trans hs₅_o,
      (hs₆_regs Reg.dim (by decide)).trans
        ((keep_s₅_s₂ Reg.dim (by decide) (by decide) (by decide)).trans hs₂d),
      (hs₆_regs Reg.thresh (by decide)).trans
        ((keep_s₅_s₂ Reg.thresh (by decide) (by decide) (by decide)).trans hs₂s),
      hs₆_out, hs₆_pf,
      (hs₆_regs Reg.trieF (by decide)).trans
        ((keep_s₅_s₂ Reg.trieF (by decide) (by decide) (by decide)).trans hs₂tF),
      (hs₆_regs Reg.trieG (by decide)).trans
        ((keep_s₅_s₂ Reg.trieG (by decide) (by decide) (by decide)).trans hs₂tG),
      (hs₆_regs Reg.queryPtr (by decide)).trans
        ((keep_s₅_s₂ Reg.queryPtr (by decide) (by decide) (by decide)).trans hs₂qp),
      (hs₆_regs Reg.queryCount (by decide)).trans hs₅_qc,
      hs₆_pFs, hs₆_pGs, hs₆_pHs,
      fun a ha => by rw [hs₆_mem, Function.update_of_ne (by omega)],
      by simp [hs₆_mem],
      by simp⟩
  have hpre_tot : ExecWithin w preprocessCode x s₆
      (4 + (5 * d + 3 + (3 + (d * (20 * L_low + 12) + 8 +
        (5 + (tripleTime d L_low + 8)))))) := by
    unfold preprocessCode
    refine (he_s0.seq (he_ic.seq (he_p2.seq (he_glow.seq (he_p4.seq (he_pre.seq he_p5)))))).mono ?_
    rw [hlow_len]
  refine ⟨s₆, s₅.mem, outBase, preFs, preGs, preHs, preOutFn,
    by rwa [hL_low_def],
    hob_gt_bf,
    by rw [hH_pk_def, hH_pos_def, hsp_val]; exact hqw_bound,
    hf_qw, s₅_below_bf, ⟨hpFs_lt, hpGs_lt, hpHs_lt⟩,
    fun k hk => by
      obtain ⟨stFn, htr, heq⟩ := hpreF_st k hk
      exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩,
    fun k hk => by
      obtain ⟨stFn, htr, heq⟩ := hpreG_st k hk
      exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩,
    fun k hk => by
      obtain ⟨stFn, htr, heq⟩ := hpreH_st k hk
      exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩,
    hpreOut_tr,
    fun Y hY => hpreOut_eq Y ((hlow_mem_iff Y).mpr hY),
    hs₆_qi, hs₆P⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
