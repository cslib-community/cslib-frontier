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
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

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

private def solvePreStageCode : Code .standard numRegs := ram[
  Reg.entryPtr ← rDomPtr;
  Reg.entryCount ← rDomLen;
  rGenTmp ← rDomLen + rDomLen;
  Reg.free ← rDomPtr + rGenTmp;
  rStageCutoff ← #0 ]

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
  have hL_pos : 1 ≤ L_low := hL_low_def ▸ lowCount_pos d s
  have hsp_bound := solveSpace_split (baseFree := baseFree) (nQ := Cs.length)
    (H_pk := highPeak s Cs) hL_low_def
  -- Step 1: allocate the coordinate buffer `[baseFree, baseFree + d)`
  have hf_ldb : Fits w (baseFree + d) := hfit_space.of_le (by omega)
  let s₀ := (((x.set rZero 0).set rOne 1).set rCoordsPtr baseFree).set Reg.free (baseFree + d)
  have he_s0 : ExecWithin (B := .standard) w (ram[
      rZero ← #0;
      rOne ← #1;
      rCoordsPtr ← Reg.free;
      Reg.free ← Reg.free + Reg.dim ]) x s₀ 4 := by
    wram_exec [hd, hfree]
  -- Step 2: the identity coordinates at `baseFree`
  obtain ⟨s₁, he_ic, hs₁_coords, hs₁_fr, hs₁_regs⟩ :=
    exec_initIdentityCoords s₀ (by regs_frame) (by regs_frame) (by regs_frame) hf_ldb hfit_d
  -- Step 3: `genLowSubsets` on `List.finRange d` at `baseFree + d`
  let s₂ := ((s₁.set rCoordsLen d).set rMaxCard s).set rDomPtr (baseFree + d)
  have he_p2 : ExecWithin (B := .standard) w
      (ram[ rCoordsLen ← Reg.dim; rMaxCard ← Reg.thresh; rDomPtr ← Reg.free ]) s₁ s₂ 3 := by
    wram_exec [show s₁.regs Reg.dim = d by regs_frame, show s₁.regs Reg.thresh = s by regs_frame,
      show s₁.regs Reg.free = baseFree + d by regs_frame]
  have hfr_len : (List.finRange d).length = d := List.length_finRange
  obtain ⟨s₃, he_glow, hs₃_dlen, hs₃_dom, hs₃_fr, hs₃_regs⟩ :=
    exec_genLowSubsets (domPtr := baseFree + d) (k := s) (List.finRange d) s₂ (by regs_frame)
      (by regs_frame) (by regs_frame) (by simp [s₂]) (by regs_frame) (by regs_frame)
      (List.nodup_finRange d) hs₁_coords (by simp)
      (by rw [hfr_len, ← lowCount, hL_low_def]; exact hfit_space.of_le (by omega)) hfit_mask
  rw [hfr_len, ← lowCount, hL_low_def] at he_glow
  have hlow_spec := prefixesUpTo_spec s (List.nodup_finRange d)
  have hlow_len : (prefixesUpTo s (List.finRange d)).length = L_low := by
    rw [length_prefixesUpTo s (List.nodup_finRange d), hfr_len, ← lowCount, hL_low_def]
  generalize prefixesUpTo s (List.finRange d) = lowDom at hs₃_dlen hs₃_dom hlow_spec hlow_len
  have hlow_mem_iff (X : Finset (Fin d)) : X ∈ lowDom ↔ #X ≤ s := by simp [hlow_spec.2]
  -- Step 4: `runTransformTriple` on `lowDom` with cutoff `0`
  have hf_ps : Fits w (baseFree + d + (lowDom.length + lowDom.length)) :=
    hfit_space.of_le (by omega)
  have hf_2L : Fits w (lowDom.length + lowDom.length) := hf_ps.of_le (by omega)
  let s₄ := ((((s₃.set Reg.entryPtr (baseFree + d)).set Reg.entryCount lowDom.length).set rGenTmp
    (lowDom.length + lowDom.length)).set Reg.free
      (baseFree + d + (lowDom.length + lowDom.length))).set rStageCutoff 0
  have he_p4 : ExecWithin w solvePreStageCode s₃ s₄ 5 := by
    unfold solvePreStageCode
    wram_exec [show s₃.regs rDomPtr = baseFree + d by regs_frame, hs₃_dlen]
  have hbelow₄ : ∀ a < baseFree, s₄.mem a = x.mem a := fun a ha =>
    (hs₃_fr a (Or.inl (by omega))).trans (hs₁_fr a (Or.inl ha))
  obtain ⟨s₅, preFs, preGs, preHs, outBase, he_pre, hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr,
    hpf_lo, hpf_hi, hpFs_lt, hpGs_lt, hpHs_lt, hpreF_st, hpreG_st, hpreH_st,
    ⟨preOutFn, hpreOut_tr, hpreOut_eq⟩, hs₅_frame, hs₅_regs⟩ :=
    exec_runTransformTriple (free := baseFree + d + 2 * L_low) (cutoff := 0)
      (preFs := s₄.regs rPreFsBase) (preGs := s₄.regs rPreGsBase) (preHs := s₄.regs rPreHsBase)
      (P_low := fun _ => False) (W := W) s₄ (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) rfl rfl rfl
      (by simp [s₄]; omega) (by omega) hlow_spec.1 hs₃_dom (by omega)
      (fun X hX _ _ => ⟨fun _ => (hlow_mem_iff _).2 (card_erase_le.trans ((hlow_mem_iff X).1 hX)),
        fun h => (Nat.not_lt_zero _ h).elim⟩)
      ((htrieF.congr_below hbelow₄).mono_bound (by omega))
      ((htrieG.congr_below hbelow₄).mono_bound (by omega)) hf_eq hg_eq hf_le hg_le
      (fun hpos => by omega) hfit_val (by rw [hlow_len]; exact hfit_space.of_le (by omega))
  rw [hlow_len] at hpf_hi
  -- Step 5: the answer header at `outBase` and the query-loop state
  have hf_qw : Fits w (outBase + 1 + Cs.length) := hfit_space.of_le (by omega)
  obtain ⟨s₆, he_p5, hs₆_qi, hs₆P⟩ : ∃ s₆, ExecWithin w preSaveCode s₅ s₆ 8 ∧
      s₆.regs rQueryIdx = 0 ∧
      QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs s₅.mem 0 s₆ := by
    unfold preSaveCode
    wram_exec [hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr, show s₅.regs rOne = 1 by regs_frame,
      show s₅.regs Reg.queryCount = Cs.length by regs_frame]
    dsimp only [QueryInv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, ?_, by simp⟩
    all_goals first | regs_frame | wram_simp
  refine ⟨s₆, s₅.mem, outBase, preFs, preGs, preHs, preOutFn,
    (he_s0.seq (he_ic.seq (he_p2.seq (he_glow.seq (he_p4.seq (he_pre.seq he_p5)))))).mono
      (by rw [hlow_len, hL_low_def]),
    by omega, by omega, hf_qw, fun a ha => (hs₅_frame a (Or.inl (by omega))).trans (hbelow₄ a ha),
    ⟨hpFs_lt, hpGs_lt, hpHs_lt⟩,
    fun k hk => (hpreF_st k hk).imp fun _ h => ⟨h.1, fun Y hY => h.2 Y ((hlow_mem_iff Y).2 hY)⟩,
    fun k hk => (hpreG_st k hk).imp fun _ h => ⟨h.1, fun Y hY => h.2 Y ((hlow_mem_iff Y).2 hY)⟩,
    fun k hk => (hpreH_st k hk).imp fun _ h => ⟨h.1, fun Y hY => h.2 Y ((hlow_mem_iff Y).2 hY)⟩,
    hpreOut_tr, fun Y hY => hpreOut_eq Y ((hlow_mem_iff Y).2 hY), hs₆_qi, hs₆_qi ▸ hs₆P⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
