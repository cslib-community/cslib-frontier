/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochTable
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochTable
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `RealizesBounded .exact` and `ValidHistory` for `writeLargeParamTableProg`

Compiles `writeLargeParamTableProg` (from `DualEpochTable.lean`) over `Cslib.WordRAM.Basis.exact`
with `¬ReadsWidth` by proving `RealizesBounded .exact` and `(Memory.spec w).ValidHistory` modularly
for each of its nine tiny sub-programs (`writeCoreAProg`–`writeCoreEProg`, `writeOffHashProg`,
`writeOffBpProg`, `writeOffBtProg`, `writeOffTriePageProg`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM

/-- Static parameter validity bundle matching `writeLargeParamTableProg`'s `Fits w` checks. -/
@[expose] def WriteLargeParamPre (w : ℕ)
    (x : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))) (s : Memory.State) : Prop :=
  let ((base, pBase), ((N, metaBase), ((logN, ell), pgB))) := x
  ∃ c U V,
    (base + 10 ≤ pBase ∨ pBase + 63 ≤ base) ∧
    whpThreshold c ≤ N ∧ N ≤ U ∧ Fits w U ∧ 0 < V ∧ V ≤ 2 ^ w ∧
    logN = Nat.log 2 N ∧ ell = Dynamic.logLogFactor N ∧ pgB = pageSizeWhp N ∧
    Fits w (metaBase + epochMetaWordsWhp c w N) ∧
    redWidthWhp U ≤ w ∧
    base + 10 ≤ s.frontier ∧ pBase + 63 ≤ s.frontier ∧
    RootStaticHeader c U V w base s.mem

private theorem epochMeta_fits_parts {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp N) ≤
      epochMetaWordsWhp c w N ∧
    BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (bWhp N) ≤
      epochMetaWordsWhp c w N ∧
    BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (fpBitsWhp N) ≤
      epochMetaWordsWhp c w N ∧
    packedWords (16 * numBucketsWhp N) (globalPtrBits N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (numBucketsWhp N * maxSlabsPerBktWhp N) (globalPtrBits N) w ≤
      epochMetaWordsWhp c w N ∧
    packedWords (8 * numBucketsWhp N * slabSizeWhp N) (globalPtrBits N) w ≤
      epochMetaWordsWhp c w N ∧
    packedWords (4 * (N / slabSizeWhp N + 4)) (globalPtrBits N) w ≤
      epochMetaWordsWhp c w N ∧
    packedWords (16 * maxTailWhp N) (globalPtrBits N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (totalBTreeNodesWhp N) (nodeMetaBitsWhp N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (totalBTreeNodesWhp N) (keysWordBitsWhp N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (totalBTreeNodesWhp N) (valsWordBitsWhp N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (maxTrieNodesWhp c N * 2 ^ bCharWhp N) (globalPtrBits N) w ≤
      epochMetaWordsWhp c w N ∧
    packedWords (6 * maxTrieNodesWhp c N) (globalPtrBits N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (6 * qEpochWhp N + 6) (globalPtrBits N) w ≤ epochMetaWordsWhp c w N ∧
    packedWords (4 * (N / pageSizeWhp N + 4)) (globalPtrBits N) w ≤
      epochMetaWordsWhp c w N ∧
    packedWords (16 * pageSizeWhp N) (globalPtrBits N) w ≤ epochMetaWordsWhp c w N := by
  have hnot : ¬(N < whpThreshold c) := Nat.not_lt.mpr hth
  unfold epochMetaWordsWhp; rw [ite_eq_right hnot]
  dsimp only
  unfold BitPackedDoubleTabulation.space
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private def dummy_io : SlotIoLayout :=
  ⟨0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

private theorem vh_rd {w a : ℕ} {α : Type} {s : Memory.State} {f : ℕ → Memory.Prog α}
    (ha : a < s.frontier)
    (hf : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (f (s.mem a)))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s ((Memory.read a).bind f)) := by
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨⟨ha, trivial⟩, hf⟩

private theorem vh_wr {w a v : ℕ} {α : Type} {m : ℕ → ℕ} {fr : ℕ} {rest : Memory.Prog α}
    (ha : a < fr) (hv : Fits w v)
    (hrest : (Memory.spec w).ValidHistory ⟨Function.update m a v, fr⟩
      ((Memory.spec w).clientHistory ⟨Function.update m a v, fr⟩ rest)) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ ((Memory.write a v).bind fun _ => rest)) := by
  rw [validHistory_bind]
  exact ⟨⟨⟨ha, hv⟩, trivial⟩, hrest⟩

private theorem vh_wr_last {w a v : ℕ} {m : ℕ → ℕ} {fr : ℕ} (ha : a < fr) (hv : Fits w v) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ (Memory.write a v)) :=
  ⟨⟨ha, hv⟩, trivial⟩

private theorem tmin_val_eq (N : ℕ) :
    (if Nat.log 2 N / (160 * Dynamic.logLogFactor N) < 2 then 2
      else Nat.log 2 N / (160 * Dynamic.logLogFactor N)) = tMinWhp N := by
  unfold tMinWhp
  by_cases h : Nat.log 2 N / (160 * Dynamic.logLogFactor N) < 2
  · rw [ite_eq_left h, max_eq_left (by omega)]
  · rw [ite_eq_right h, max_eq_right (by omega)]

private theorem header_bounds {c U w N : ℕ} (hth : whpThreshold c ≤ N)
    (hNU : N ≤ U) (hU : Fits w U) :
    w < 2 ^ w ∧ cTabWhp c < w ∧ dTabWhp c ≤ N ∧ bCharWhp N < w ∧ bWhp N < w ∧
    fpBitsWhp N < w ∧ globalPtrBits N ≤ w ∧ numBucketsWhp N ≤ N ∧
    slabSizeWhp N ≤ N ∧ maxSlabsPerBktWhp N ≤ N ∧ N / slabSizeWhp N + 4 ≤ N ∧
    maxTailWhp N ≤ N ∧ nodeMetaBitsWhp N < w ∧ keysWordBitsWhp N < w ∧
    valsWordBitsWhp N < w ∧ valLaneBitsWhp N < w ∧ tMinWhp N < w ∧
    nSliceWhp N ≤ N ∧ maxTrieNodesWhp c N ≤ N ∧ qEpochWhp N ≤ N ∧
    sMaxWhp c N ≤ N ∧ 32 * slabScale N ^ 12 ≤ N ∧
    11 ≤ w ∧ 2 ^ bCharWhp N ≤ N ∧ 16 * numBucketsWhp N ≤ N ∧
    numBucketsWhp N * maxSlabsPerBktWhp N ≤ N ∧
    8 * numBucketsWhp N * slabSizeWhp N ≤ N ∧
    4 * (N / slabSizeWhp N + 4) ≤ N ∧ 16 * maxTailWhp N ≤ N ∧
    totalBTreeNodesWhp N ≤ N ∧ maxTrieNodesWhp c N * 2 ^ bCharWhp N ≤ N ∧
    6 * maxTrieNodesWhp c N ≤ N ∧ 6 * qEpochWhp N + 6 ≤ N ∧
    4 * (N / pageSizeWhp N + 4) ≤ N ∧ 16 * pageSizeWhp N ≤ N ∧
    cTabWhp c * bCharWhp N < 2 ^ w ∧ 4 * (cTabWhp c + 2) < w ∧
    BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp N) ≤ N ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp N) ≤ N ∧
    8 ≤ tMinWhp N ∧ Nat.log 2 N < w ∧ 1 ≤ Dynamic.logLogFactor N := by
  have hpb := largeEpoch_param_bounds hth hNU hU
  have hsb := param_scalar_bounds hth hNU hU
  obtain ⟨h32, hq, hpow_bc, hL8⟩ := scale12_mul_le_pow_bChar hth
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have hd_le : dTabWhp c ≤ N := by
    have hbot := hpb.2.2.2.2.2.2.2.2.2.2.1
    exact (Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)).trans hbot
  have hK_le : slabSizeWhp N ≤ N := by
    unfold slabSizeWhp
    exact ((Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 12)).trans
      (by omega : slabScale N ^ 12 ≤ 32 * slabScale N ^ 12)).trans (h32.trans hpow_bc)
  have hms_le : maxSlabsPerBktWhp N ≤ N := by
    unfold maxSlabsPerBktWhp
    have h1 : slabScale N ^ 10 ≤ slabScale N ^ 12 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact (by omega : 4 * slabScale N ^ 10 ≤ 32 * slabScale N ^ 12).trans (h32.trans hpow_bc)
  have hvl_lt : valLaneBitsWhp N < w := by
    have hv := hpb.2.2.2.2.2.2.2.2.1
    unfold valsWordBitsWhp at hv
    have ht := hsb.2.2.2.2.2.2.2.2.2.1
    have : valLaneBitsWhp N ≤ 2 * tMinWhp N * valLaneBitsWhp N :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have htm_lt : tMinWhp N < w := by
    unfold tMinWhp
    have hell := Dynamic.one_le_logLogFactor N
    have hdl : Nat.log 2 N / (160 * Dynamic.logLogFactor N) ≤ Nat.log 2 N := Nat.div_le_self _ _
    omega
  have hns_le : nSliceWhp N ≤ N := by
    have hM1 : 1 ≤ numBucketsWhp N := Nat.one_le_two_pow
    have hbt := hpb.2.2.2.2.2.2.2.2.2.2.2.1
    unfold totalBTreeNodesWhp at hbt
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < 3 * numBucketsWhp N)).trans hbt
  have h8t := eight_le_tMinWhp hth
  have hN_log := hpb.2.2.1
  refine ⟨hw_lt, by omega, hd_le, hpb.2.2.2.1, hpb.2.2.2.2.1, hpb.2.2.2.2.2.1,
    hpb.2.1, by omega, hK_le, hms_le,
    by have := hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega,
    by have := hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega,
    hpb.2.2.2.2.2.2.1, hpb.2.2.2.2.2.2.2.1, hpb.2.2.2.2.2.2.2.2.1,
    hvl_lt, htm_lt, hns_le,
    by have := hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega,
    hq.trans hpow_bc, hsb.2.2.1, h32.trans hpow_bc,
    hsb.2.2.2.2.2.1, hpow_bc, hsb.1, hsb.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hpb.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsb.2.2.2.1, hsb.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.1,
    hpb.2.2.2.2.2.2.2.2.2.2.1,
    h8t, hN_log, Dynamic.one_le_logLogFactor N⟩

private theorem realizesBounded_writeCoreA :
    RealizesBounded .exact writeCoreAProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, pBase), ((N, metaBase), logN)) s =>
        ∃ c U V, whpThreshold c ≤ N ∧ N ≤ U ∧ Fits w U ∧ 0 < V ∧ V ≤ 2 ^ w ∧
          logN = Nat.log 2 N ∧ Fits w metaBase ∧
          base + 10 ≤ s.frontier ∧ pBase + 48 ≤ s.frontier ∧
          RootStaticHeader c U V w base s.mem)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, logN⟩⟩
    obtain ⟨c, U, V, hth, hNU, hU, hV, hVpow, rfl, hmb, hbf, hpf, hhdr⟩ := h
    have hU_th : whpThreshold c ≤ U := hth.trans hNU
    have hb := header_bounds hth hNU hU
    have hfr_w := hmem.1
    have hct : s.mem (base + hdrCTab) = cTabWhp c := by
      rw [hhdr.2.2.2.2.2.2.1, ite_eq_left hU_th]
    try rw [hct]
    dsimp only [Fits, hdrU1, hdrV1, hdrW, hdrRedW, hdrCTab, bCharWhp] at *
    omega)

private theorem realizesBounded_writeCoreB :
    RealizesBounded .exact writeCoreBProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, pBase), (logN, ell)) s =>
        ∃ c U N, whpThreshold c ≤ N ∧ N ≤ U ∧ Fits w U ∧
          logN = Nat.log 2 N ∧ ell = Dynamic.logLogFactor N ∧
          base + 10 ≤ s.frontier ∧ pBase + 11 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, pBase⟩, ⟨logN, ell⟩⟩
    obtain ⟨c, U, N, hth, hNU, hU, rfl, rfl, hbf, hpf⟩ := h
    have hb := header_bounds hth hNU hU
    have hsb := param_scalar_bounds hth hNU hU
    have h60 := sixtyThousand_mul_ell_le_log hth
    have hfr_w := hmem.1
    dsimp only [Fits, hdrCTab, hdrDTab] at *
    omega)

private theorem realizesBounded_writeCoreC :
    RealizesBounded .exact writeCoreCProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, nCap), (bWhpv, ell)) s =>
        ∃ c U, whpThreshold c ≤ nCap ∧ nCap ≤ U ∧ Fits w U ∧
          bWhpv = bWhp nCap ∧ ell = Dynamic.logLogFactor nCap ∧
          pBase + 16 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨pBase, nCap⟩, ⟨bWhpv, ell⟩⟩
    obtain ⟨c, U, hth, hNU, hU, rfl, rfl, hpf⟩ := h
    have hb := header_bounds hth hNU hU
    have hsb := param_scalar_bounds hth hNU hU
    have hfr_w := hmem.1
    have h1 := shift_one_eq (bWhp nCap)
    have h2 := shift_one_eq (2 * Dynamic.logLogFactor nCap)
    have h10 := shift_one_eq (10 * Dynamic.logLogFactor nCap)
    have h1_eq : 2 ^ bWhp nCap = numBucketsWhp nCap := rfl
    have h2_eq : 2 ^ (2 * Dynamic.logLogFactor nCap) = slabSizeWhp nCap :=
      (slabScale_pow_eq_shift nCap 2).symm
    have h10_eq : 2 ^ (10 * Dynamic.logLogFactor nCap) = slabScale nCap ^ 10 :=
      (slabScale_pow_eq_shift nCap 10).symm
    have hK_pos : 0 < slabSizeWhp nCap := by unfold slabSizeWhp slabScale; positivity
    have hdiv : nCap / slabSizeWhp nCap ≤ nCap := Nat.div_le_self _ _
    have h8MK : 8 * numBucketsWhp nCap * slabSizeWhp nCap ≤ nCap :=
      (largeEpoch_param_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hMK : numBucketsWhp nCap * slabSizeWhp nCap ≤ nCap :=
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 8)).trans (by rw [← Nat.mul_assoc]; exact h8MK)
    have h4L : 4 * slabScale nCap ^ 10 = maxSlabsPerBktWhp nCap := rfl
    have hmt : numBucketsWhp nCap * slabSizeWhp nCap + 4 = maxTailWhp nCap := rfl
    have h1_lt : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    dsimp only [Fits] at *
    try simp only [h1, h2, h10, h1_eq, h2_eq, h10_eq, h4L, hmt]
    try omega)

private theorem realizesBounded_writeCoreD :
    RealizesBounded .exact writeCoreDProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, (logN, ell)) s =>
        ∃ c U N, whpThreshold c ≤ N ∧ N ≤ U ∧ Fits w U ∧
          logN = Nat.log 2 N ∧ ell = Dynamic.logLogFactor N ∧
          pBase + 21 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨logN, ell⟩⟩
    obtain ⟨c, U, N, hth, hNU, hU, rfl, rfl, hpf⟩ := h
    have hb := header_bounds hth hNU hU
    have hsb := param_scalar_bounds hth hNU hU
    have h60 := sixtyThousand_mul_ell_le_log hth
    have hfr_w := hmem.1
    have ht_eq := tmin_val_eq N
    have hdiv : Nat.log 2 N / (160 * Dynamic.logLogFactor N) ≤ Nat.log 2 N :=
      Nat.div_le_self _ _
    have hkl : 2 * tMinWhp N * (36 * Dynamic.logLogFactor N + 2) = keysWordBitsWhp N := rfl
    have hvl : 2 * tMinWhp N * (12 * Dynamic.logLogFactor N + 8) = valsWordBitsWhp N := rfl
    have h8t : 8 ≤ tMinWhp N := eight_le_tMinWhp hth
    have htm_eq : Nat.log 2 N / (160 * Dynamic.logLogFactor N) = tMinWhp N := by
      unfold tMinWhp at h8t ⊢; omega
    have hpos_v : 0 < 12 * Dynamic.logLogFactor N + 8 := by omega
    have h2t : 2 * tMinWhp N ≤ valsWordBitsWhp N := by
      rw [← hvl]; exact Nat.le_mul_of_pos_right _ hpos_v
    have hkl_le : 36 * Dynamic.logLogFactor N + 2 ≤ keysWordBitsWhp N := by
      rw [← hkl]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hvl_le : 12 * Dynamic.logLogFactor N + 8 ≤ valsWordBitsWhp N := by
      rw [← hvl]; exact Nat.le_mul_of_pos_left _ (by omega)
    dsimp only [Fits] at *
    try rw [htm_eq]
    omega)

private theorem realizesBounded_writeCoreE :
    RealizesBounded .exact writeCoreEProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, pBase), ell) s =>
        ∃ c U N, whpThreshold c ≤ N ∧ N ≤ U ∧ Fits w U ∧
          ell = Dynamic.logLogFactor N ∧
          base + 10 ≤ s.frontier ∧ pBase + 29 ≤ s.frontier ∧
          s.mem (base + hdrCEff) = cEff c ∧
          s.mem (pBase + 5) = cTabWhp c ∧
          s.mem (pBase + 20) = tMinWhp N)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, pBase⟩, ell⟩
    obtain ⟨c, U, N, hth, hNU, hU, rfl, hbf, hpf, hce, hct, htm⟩ := h
    have hb := header_bounds hth hNU hU
    have hsb := param_scalar_bounds hth hNU hU
    have h60 := sixtyThousand_mul_ell_le_log hth
    have hfr_w := hmem.1
    have h1 := shift_one_eq (Dynamic.logLogFactor N)
    have h12 := shift_one_eq (12 * Dynamic.logLogFactor N)
    have h18 := shift_one_eq (18 * Dynamic.logLogFactor N)
    have hs1 : 2 ^ Dynamic.logLogFactor N = slabScale N := rfl
    have hs12 : 2 ^ (12 * Dynamic.logLogFactor N) = slabScale N ^ 12 :=
      (slabScale_pow_eq_shift N 12).symm
    have hs18 : 2 ^ (18 * Dynamic.logLogFactor N) = qEpochWhp N :=
      (slabScale_pow_eq_shift N 18).symm
    have hmt : (cTabWhp c + 1) * qEpochWhp N + 2 = maxTrieNodesWhp c N := rfl
    have hsm : (cEff c + 4) * slabScale N = sMaxWhp c N := rfl
    have hdiv : (32 * slabScale N ^ 12) / (tMinWhp N - 1) ≤ 32 * slabScale N ^ 12 :=
      Nat.div_le_self _ _
    have hL_le : slabScale N ≤ qEpochWhp N := by
      unfold qEpochWhp; exact Nat.le_self_pow (by decide) _
    have h1_lt : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hns_le : (32 * slabScale N ^ 12) / (tMinWhp N - 1) + 64 ≤ N :=
      hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmt_le : (cTabWhp c + 1) * qEpochWhp N ≤ maxTrieNodesWhp c N := by
      unfold maxTrieNodesWhp; omega
    have hsm_le : (cEff c + 4) * slabScale N ≤ N := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hce_le : cEff c + 4 ≤ (cEff c + 4) * slabScale N :=
      Nat.le_mul_of_pos_right _ (by unfold slabScale; positivity)
    have h32_le : 32 * slabScale N ^ 12 ≤ N := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hdiv_ns : 0 < tMinWhp N - 1 := by omega
    have h64_le : (32 * slabScale N ^ 12) / (tMinWhp N - 1) ≤ N := hdiv.trans h32_le
    try rw [hce]
    try rw [hct]
    try rw [htm]
    try simp only [h1, h12, h18, hs1, hs12, hs18, hmt, hsm]
    dsimp only [Fits, hdrCEff] at *
    omega)

private theorem realizesBounded_writeOffHash :
    RealizesBounded .exact writeOffHashProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 63 ≤ s.frontier ∧
          s.mem (pBase + 1) = fl.metaBase ∧ s.mem (pBase + 2) = w ∧
          s.mem (pBase + 5) = cTabWhp fl.c ∧ s.mem (pBase + 6) = dTabWhp fl.c ∧
          s.mem (pBase + 7) = bCharWhp fl.N ∧ s.mem (pBase + 8) = bWhp fl.N ∧
          s.mem (pBase + 9) = fpBitsWhp fl.N)
      (fun _ _ => 0) := by
  have hpws := realizesBounded_packedWordsSafe
  realize
  all_goals (
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, hmf, hpf,
      hm1, hm2, hm5, hm6, hm7, hm8, hm9⟩ := h
    subst hp_eq; subst hw_eq
    have hb := header_bounds hth hNU hU
    have hparts := epochMeta_fits_parts (w := fl.w) hth
    have hmono := sublinear_word_fits_le (w := fl.w) hth
    have hfr_w := hmem.1
    have hw_pos : 0 < fl.w := by omega
    have hsh : (1 : ℕ) <<< bCharWhp fl.N = 2 ^ bCharWhp fl.N := shift_one_eq _
    have htop_mul : (cTabWhp fl.c + 1) * (dTabWhp fl.c * 2 ^ bCharWhp fl.N) =
        BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
      ring
    have hres_pw : ∀ n k st, (Memory.spec 0).clientResult st
        (packedWordsSafeProg ((n, k), fl.w)) = packedWords n k fl.w := fun _ _ _ =>
      packedWordsSafe_eq hw_pos
    have hst_pw : ∀ n k st, (Memory.spec 0).clientState st
        (packedWordsSafeProg ((n, k), fl.w)) = st := fun _ _ _ => rfl
    have hbot_eq : dTabWhp fl.c * 2 ^ bCharWhp fl.N =
        BitPackedDoubleTabulation.botEntries (dTabWhp fl.c) (bCharWhp fl.N) := rfl
    have hfp_eq : 32 + (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
        packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (bWhp fl.N) fl.w =
        offFpHash fl.c fl.w fl.N := by
      unfold offFpHash offBktHash BitPackedDoubleTabulation.space
        BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
        BitPackedDoubleTabulation.botEntries; omega
    have hbm_eq : offFpHash fl.c fl.w fl.N +
        (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
          (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
        packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (fpBitsWhp fl.N) fl.w =
        offBktMeta fl.c fl.w fl.N := by
      unfold offBktMeta BitPackedDoubleTabulation.space
        BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
        BitPackedDoubleTabulation.botEntries; omega
    have htw_le : packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N := hparts.1
    have hbb_le : packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (bWhp fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N := hparts.2.1
    have hbf_le : packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (fpBitsWhp fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N := hparts.2.2.1
    have hoff_dt : 32 + (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) ≤
        offFpHash fl.c fl.w fl.N := by omega
    have h1_lt : (1 : ℕ) < 2 ^ fl.w := Nat.one_lt_two_pow (by omega)
    dsimp only [Fits] at *
    try rw [hm1]
    try rw [hm2]
    try rw [hm5]
    try rw [hm6]
    try rw [hm7]
    try rw [hm8]
    try rw [hm9]
    try simp only [hsh, htop_mul, hres_pw, hst_pw]
    try rw [hfp_eq]
    try rw [hbm_eq])
  all_goals omega

private theorem realizesBounded_writeOffBp :
    RealizesBounded .exact writeOffBpProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 37 ≤ s.frontier ∧
          s.mem (pBase + 2) = w ∧ s.mem (pBase + 10) = globalPtrBits fl.N ∧
          s.mem (pBase + 11) = numBucketsWhp fl.N ∧ s.mem (pBase + 12) = slabSizeWhp fl.N ∧
          s.mem (pBase + 13) = maxSlabsPerBktWhp fl.N ∧
          s.mem (pBase + 14) = fl.N / slabSizeWhp fl.N + 4 ∧
          s.mem (pBase + 15) = maxTailWhp fl.N ∧
          s.mem (pBase + 31) = offBktMeta fl.c w fl.N)
      (fun _ _ => 0) := by
  have hap := realizesBounded_addPackedWrite
  realize
  all_goals (
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, hmf, hpf,
      hm2, hm10, hm11, hm12, hm13, hm14, hm15, hm31⟩ := h
    subst hp_eq; subst hw_eq
    have hb := header_bounds hth hNU hU
    have hmono := sublinear_word_fits_le (w := fl.w) hth
    have hw_pos : 0 < fl.w := by omega
    have hfr_w := hmem.1
    have hap_r : ∀ p o pv n k st, (Memory.spec 0).clientResult st
        (addPackedWriteProg (((p, o), (pv, n)), (k, fl.w))) = pv + packedWords n k fl.w :=
      fun p o pv n k st =>
        (addPackedWriteProg_spec (pBase := p) (off := o) (prev := pv) (n := n) (k := k)
          hw_pos st).1
    have hap_f : ∀ p o pv n k st, ((Memory.spec 0).clientState st
        (addPackedWriteProg (((p, o), (pv, n)), (k, fl.w)))).frontier = st.frontier :=
      fun p o pv n k st => by
        rw [(addPackedWriteProg_spec (pBase := p) (off := o) (prev := pv) (n := n) (k := k)
          hw_pos st).2.1]
    dsimp only [Fits] at *
    try simp only [hm2, hm10, hm11, hm12, hm13, hm14, hm15, hm31, hap_r, hap_f]
    all_goals try (
      have e32 : offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w =
          offSlabDir fl.c fl.w fl.N := rfl
      have e33 : offSlabDir fl.c fl.w fl.N +
          packedWords (numBucketsWhp fl.N * maxSlabsPerBktWhp fl.N) (globalPtrBits fl.N) fl.w =
          offTailDir fl.c fl.w fl.N := rfl
      have e34 : offTailDir fl.c fl.w fl.N +
          packedWords (8 * numBucketsWhp fl.N * slabSizeWhp fl.N) (globalPtrBits fl.N) fl.w =
          offSlabOwner fl.c fl.w fl.N := rfl
      have e35 : offSlabOwner fl.c fl.w fl.N +
          packedWords (4 * (fl.N / slabSizeWhp fl.N + 4)) (globalPtrBits fl.N) fl.w =
          offTailOwner fl.c fl.w fl.N := rfl
      have e36 : offTailOwner fl.c fl.w fl.N +
          packedWords (16 * maxTailWhp fl.N) (globalPtrBits fl.N) fl.w =
          offBTreeMeta fl.c fl.w fl.N := rfl
      have h8m : 8 * numBucketsWhp fl.N ≤ 8 * numBucketsWhp fl.N * slabSizeWhp fl.N := by
        have hK_pos : 0 < slabSizeWhp fl.N := by unfold slabSizeWhp slabScale; positivity
        exact Nat.le_mul_of_pos_right _ hK_pos
      try rw [e32]
      try rw [e33]
      try rw [e34]
      try rw [e35]
      try rw [e36]))
  all_goals omega

private theorem realizesBounded_writeOffBt :
    RealizesBounded .exact writeOffBtProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 40 ≤ s.frontier ∧
          s.mem (pBase + 2) = w ∧ s.mem (pBase + 11) = numBucketsWhp fl.N ∧
          s.mem (pBase + 16) = nodeMetaBitsWhp fl.N ∧
          s.mem (pBase + 17) = keysWordBitsWhp fl.N ∧
          s.mem (pBase + 18) = valsWordBitsWhp fl.N ∧
          s.mem (pBase + 21) = nSliceWhp fl.N ∧
          s.mem (pBase + 36) = offBTreeMeta fl.c w fl.N)
      (fun _ _ => 0) := by
  have hap := realizesBounded_addPackedWrite
  realize
  all_goals (
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, hmf, hpf,
      hm2, hm11, hm16, hm17, hm18, hm21, hm36⟩ := h
    subst hp_eq; subst hw_eq
    have hb := header_bounds hth hNU hU
    have hmono := sublinear_word_fits_le (w := fl.w) hth
    have hw_pos : 0 < fl.w := by omega
    have hfr_w := hmem.1
    have hap_r : ∀ p o pv n k st, (Memory.spec 0).clientResult st
        (addPackedWriteProg (((p, o), (pv, n)), (k, fl.w))) = pv + packedWords n k fl.w :=
      fun p o pv n k st =>
        (addPackedWriteProg_spec (pBase := p) (off := o) (prev := pv) (n := n) (k := k)
          hw_pos st).1
    have hap_f : ∀ p o pv n k st, ((Memory.spec 0).clientState st
        (addPackedWriteProg (((p, o), (pv, n)), (k, fl.w)))).frontier = st.frontier :=
      fun p o pv n k st => by
        rw [(addPackedWriteProg_spec (pBase := p) (off := o) (prev := pv) (n := n) (k := k)
          hw_pos st).2.1]
    have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
    dsimp only [Fits] at *
    try simp only [hm2, hm11, hm16, hm17, hm18, hm21, hm36, hap_r, hap_f, htot]
    all_goals try (
      have e37 : offBTreeMeta fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (nodeMetaBitsWhp fl.N) fl.w =
          offBTreeKeys fl.c fl.w fl.N := rfl
      have e38 : offBTreeKeys fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (keysWordBitsWhp fl.N) fl.w =
          offBTreeVals fl.c fl.w fl.N := rfl
      have e39 : offBTreeVals fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (valsWordBitsWhp fl.N) fl.w =
          offTrieChild fl.c fl.w fl.N 0 := by unfold offTrieChild; simp
      try rw [e37]
      try rw [e38]
      try rw [e39]))
  all_goals omega

private def writeOffPageEndProg :
    ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((pBase, pgB), (nCap, (wv, ptrB))), offPD) => do
    let wPD ← packedWordsSafeProg ((4 * (nCap / pgB + 4), ptrB), wv)
    let offPT := offPD + wPD
    let offEnd ← addPackedWriteProg (((pBase, 45), (offPT, 16 * pgB)), (ptrB, wv))
    pure ((offPD, offPT), offEnd)

private theorem realizesBounded_writeOffPageEnd :
    RealizesBounded .exact writeOffPageEndProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w (((pBase, pgB), (nCap, (wv, ptrB))), offPD) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧ fl.N = nCap ∧
          wv = w ∧ ptrB = globalPtrBits fl.N ∧ pgB = pageSizeWhp fl.N ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 46 ≤ s.frontier ∧ offPD = offPageDir fl.c w fl.N)
      (fun _ _ => 0) := by
  have hpws := realizesBounded_packedWordsSafe
  have hap := realizesBounded_addPackedWrite
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, pgB⟩, ⟨nCap, ⟨wv, ptrB⟩⟩⟩, offPD⟩
    obtain ⟨fl, hp_eq, hw_eq, hn_eq, rfl, rfl, rfl, hth, hNU, hU, hmf, hpf, rfl⟩ := h
    subst hp_eq; subst hw_eq; subst hn_eq
    have hb := header_bounds hth hNU hU
    have hmono := sublinear_word_fits_le (w := fl.w) hth
    have heq_end := offEpochEnd_eq_epochMetaWordsWhp (w := fl.w) hth
    have hw_pos : 0 < fl.w := by omega
    have hfr_w := hmem.1
    have hpg_pos : 0 < pageSizeWhp fl.N := by unfold pageSizeWhp; omega
    have hndiv : fl.N / pageSizeWhp fl.N ≤ fl.N := Nat.div_le_self _ _
    have hres_pw : ∀ n k st, (Memory.spec 0).clientResult st
        (packedWordsSafeProg ((n, k), fl.w)) = packedWords n k fl.w := fun _ _ _ =>
      packedWordsSafe_eq hw_pos
    have hst_pw : ∀ n k st, (Memory.spec 0).clientState st
        (packedWordsSafeProg ((n, k), fl.w)) = st := fun _ _ _ => rfl
    have ePT : offPageDir fl.c fl.w fl.N +
        packedWords (4 * (fl.N / pageSizeWhp fl.N + 4)) (globalPtrBits fl.N) fl.w =
        offPageTail fl.c fl.w fl.N := rfl
    have eEnd : offPageTail fl.c fl.w fl.N +
        packedWords (16 * pageSizeWhp fl.N) (globalPtrBits fl.N) fl.w =
        epochMetaWordsWhp fl.c fl.w fl.N := heq_end
    have hparts := epochMeta_fits_parts (w := fl.w) hth
    have hpw_pd : packedWords (4 * (fl.N / pageSizeWhp fl.N + 4)) (globalPtrBits fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N :=
      hparts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp only [Fits] at *
    try simp only [hres_pw, hst_pw]
    all_goals try rw [ePT]
    all_goals try rw [eEnd])
  all_goals omega

private def writeOffTriePageTailProg :
    ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((pBase, pgB), (nCap, (wv, ptrB))), ((offTC0, wTC), (wTN, wTI))) => do
    let offTC1 := offTC0 + wTC
    let offTN0 := offTC1 + wTC
    let offTN1 := offTN0 + wTN
    let offTI0 := offTN1 + wTN
    let offTI1 := offTI0 + wTI
    let offPD := offTI1 + wTI
    Memory.write (pBase + 40) offTC1
    Memory.write (pBase + 41) offTN0
    Memory.write (pBase + 42) offTN1
    Memory.write (pBase + 43) offTI0
    Memory.write (pBase + 44) offTI1
    writeOffPageEndProg (((pBase, pgB), (nCap, (wv, ptrB))), offPD)

private theorem mk_writeOffPageEnd_pre (fl : FastEpochLayout) {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U) (hU : Fits fl.w fl.U)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 46 ≤ s.frontier) :
    ∃ fl' : FastEpochLayout, fl'.pBase = fl.pBase ∧ fl'.w = fl.w ∧ fl'.N = fl.N ∧
      fl.w = fl.w ∧ globalPtrBits fl.N = globalPtrBits fl'.N ∧
      pageSizeWhp fl.N = pageSizeWhp fl'.N ∧
      whpThreshold fl'.c ≤ fl'.N ∧ fl'.N ≤ fl'.U ∧ Fits fl.w fl'.U ∧
      Fits fl.w (fl'.metaBase + epochMetaWordsWhp fl'.c fl.w fl'.N) ∧
      fl.pBase + 46 ≤ s.frontier ∧ offPageDir fl.c fl.w fl.N = offPageDir fl'.c fl.w fl'.N :=
  ⟨fl, rfl, rfl, rfl, rfl, rfl, rfl, hth, hNU, hU, hmf, hpf, rfl⟩

private theorem realizesBounded_writeOffTriePageTail :
    RealizesBounded .exact writeOffTriePageTailProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w (((pBase, pgB), (nCap, (wv, ptrB))), ((offTC0, wTC), (wTN, wTI))) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧ fl.N = nCap ∧
          wv = w ∧ ptrB = globalPtrBits fl.N ∧ pgB = pageSizeWhp fl.N ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 46 ≤ s.frontier ∧
          offTC0 = offTrieChild fl.c w fl.N 0 ∧
          wTC = trieChildWords fl.c w fl.N ∧
          wTN = trieNodeWords fl.c w fl.N ∧
          wTI = trieItemWords w fl.N)
      (fun _ _ => 0) := by
  have hpe := realizesBounded_writeOffPageEnd
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, pgB⟩, ⟨nCap, ⟨wv, ptrB⟩⟩⟩, ⟨⟨offTC0, wTC⟩, ⟨wTN, wTI⟩⟩⟩
    obtain ⟨fl, hp_eq, hw_eq, hn_eq, rfl, rfl, rfl, hth, hNU, hU, hmf, hpf,
      rfl, rfl, rfl, rfl⟩ := h
    subst hp_eq; subst hw_eq; subst hn_eq
    have hmono := sublinear_word_fits_le (w := fl.w) hth
    have hfr_w := hmem.1
    have e40 : offTrieChild fl.c fl.w fl.N 0 + trieChildWords fl.c fl.w fl.N =
        offTrieChild fl.c fl.w fl.N 1 := by unfold offTrieChild; omega
    have e41 : offTrieChild fl.c fl.w fl.N 1 + trieChildWords fl.c fl.w fl.N =
        offTrieNode fl.c fl.w fl.N 0 := by unfold offTrieNode offTrieChild; omega
    have e42 : offTrieNode fl.c fl.w fl.N 0 + trieNodeWords fl.c fl.w fl.N =
        offTrieNode fl.c fl.w fl.N 1 := by unfold offTrieNode; omega
    have e43 : offTrieNode fl.c fl.w fl.N 1 + trieNodeWords fl.c fl.w fl.N =
        offTrieItem fl.c fl.w fl.N 0 := by unfold offTrieItem offTrieNode; omega
    have e44 : offTrieItem fl.c fl.w fl.N 0 + trieItemWords fl.w fl.N =
        offTrieItem fl.c fl.w fl.N 1 := by unfold offTrieItem; omega
    have ePD : offTrieItem fl.c fl.w fl.N 1 + trieItemWords fl.w fl.N =
        offPageDir fl.c fl.w fl.N := by unfold offPageDir offTrieItem; omega
    try rw [e40]
    try rw [e41]
    try rw [e42]
    try rw [e43]
    try rw [e44]
    try rw [ePD]
    dsimp only [Fits] at *
    try apply mk_writeOffPageEnd_pre fl hth hNU hU hmf)
  all_goals omega

private theorem writeOffTriePageProg_eq :
    writeOffTriePageProg = (fun x =>
      match x with
      | (pBase, pgB) => do
        let nCap ← Memory.read pBase
        let wv ← Memory.read (pBase + 2)
        let bChar ← Memory.read (pBase + 7)
        let ptrB ← Memory.read (pBase + 10)
        let maxTrie ← Memory.read (pBase + 22)
        let qEp ← Memory.read (pBase + 23)
        let offTC0 ← Memory.read (pBase + 39)
        let b2 := 1 <<< bChar
        let wTC ← packedWordsSafeProg ((maxTrie * b2, ptrB), wv)
        let wTN ← packedWordsSafeProg ((6 * maxTrie, ptrB), wv)
        let wTI ← packedWordsSafeProg ((6 * qEp + 6, ptrB), wv)
        writeOffTriePageTailProg
          (((pBase, pgB), (nCap, (wv, ptrB))), ((offTC0, wTC), (wTN, wTI)))) :=
  funext fun ⟨_, _⟩ => rfl

private theorem mk_writeOffTriePageTail_pre (fl : FastEpochLayout) {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U) (hU : Fits fl.w fl.U)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 46 ≤ s.frontier) :
    ∃ fl' : FastEpochLayout, fl'.pBase = fl.pBase ∧ fl'.w = fl.w ∧ fl'.N = fl.N ∧
      True ∧ globalPtrBits fl.N = globalPtrBits fl'.N ∧
      pageSizeWhp fl.N = pageSizeWhp fl'.N ∧
      whpThreshold fl'.c ≤ fl'.N ∧ fl'.N ≤ fl'.U ∧ Fits fl.w fl'.U ∧
      Fits fl.w (fl'.metaBase + epochMetaWordsWhp fl'.c fl.w fl'.N) ∧
      fl.pBase + 46 ≤ s.frontier ∧
      offTrieChild fl.c fl.w fl.N 0 = offTrieChild fl'.c fl.w fl'.N 0 ∧
      packedWords (maxTrieNodesWhp fl.c fl.N * 2 ^ bCharWhp fl.N) (globalPtrBits fl.N) fl.w =
        trieChildWords fl'.c fl.w fl'.N ∧
      packedWords (6 * maxTrieNodesWhp fl.c fl.N) (globalPtrBits fl.N) fl.w =
        trieNodeWords fl'.c fl.w fl'.N ∧
      packedWords (6 * qEpochWhp fl.N + 6) (globalPtrBits fl.N) fl.w =
        trieItemWords fl.w fl'.N :=
  ⟨fl, rfl, rfl, rfl, trivial, rfl, rfl, hth, hNU, hU, hmf, hpf, rfl, rfl, rfl, rfl⟩

private theorem realizesBounded_writeOffTriePage :
    RealizesBounded .exact writeOffTriePageProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w (pBase, pgB) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          pgB = pageSizeWhp fl.N ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 46 ≤ s.frontier ∧
          s.mem pBase = fl.N ∧ s.mem (pBase + 2) = w ∧
          s.mem (pBase + 7) = bCharWhp fl.N ∧ s.mem (pBase + 10) = globalPtrBits fl.N ∧
          s.mem (pBase + 22) = maxTrieNodesWhp fl.c fl.N ∧
          s.mem (pBase + 23) = qEpochWhp fl.N ∧
          s.mem (pBase + 39) = offTrieChild fl.c w fl.N 0)
      (fun _ _ => 0) := by
  rw [writeOffTriePageProg_eq]
  have hpws := realizesBounded_packedWordsSafe
  have htail := realizesBounded_writeOffTriePageTail
  realize
  all_goals (
    rcases d with ⟨pBase, pgB⟩
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf,
      hm0, hm2, hm7, hm10, hm22, hm23, hm39⟩ := h
    subst hp_eq; subst hw_eq
    have hb := header_bounds hth hNU hU
    have hfr_w := hmem.1
    have hw_pos : 0 < fl.w := by omega
    have hsh : (1 : ℕ) <<< bCharWhp fl.N = 2 ^ bCharWhp fl.N := shift_one_eq _
    have h1_lt : (1 : ℕ) < 2 ^ fl.w := Nat.one_lt_two_pow (by omega)
    have hres_pw : ∀ n k st, (Memory.spec 0).clientResult st
        (packedWordsSafeProg ((n, k), fl.w)) = packedWords n k fl.w := fun _ _ _ =>
      packedWordsSafe_eq hw_pos
    have hst_pw : ∀ n k st, (Memory.spec 0).clientState st
        (packedWordsSafeProg ((n, k), fl.w)) = st := fun _ _ _ => rfl
    have hparts := epochMeta_fits_parts (w := fl.w) hth
    have hwtc : packedWords (maxTrieNodesWhp fl.c fl.N * 2 ^ bCharWhp fl.N)
        (globalPtrBits fl.N) fl.w ≤ epochMetaWordsWhp fl.c fl.w fl.N :=
      hparts.2.2.2.2.2.2.2.2.2.2.2.1
    have hwtn : packedWords (6 * maxTrieNodesWhp fl.c fl.N) (globalPtrBits fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N :=
      hparts.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hwti : packedWords (6 * qEpochWhp fl.N + 6) (globalPtrBits fl.N) fl.w ≤
        epochMetaWordsWhp fl.c fl.w fl.N :=
      hparts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp only [Fits] at *
    try simp only [hm0, hm2, hm7, hm10, hm22, hm23, hm39, hsh, hres_pw, hst_pw]
    all_goals try apply mk_writeOffTriePageTail_pre fl hth hNU hU hmf)
  all_goals omega

private theorem header_eq_after_A {c U V w base pBase N metaBase : ℕ}
    {s : Memory.State} (hdisj : base + 10 ≤ pBase ∨ pBase + 63 ≤ base)
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hhdr : RootStaticHeader c U V w base s.mem) :
    RootStaticHeader c U V w base
      ((Memory.spec 0).clientState s
        (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N)))).mem := by
  let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
  have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
  have heq : ∀ j < 10, ((Memory.spec 0).clientState s
      (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N)))).mem (base + j) =
      s.mem (base + j) := fun j hj =>
    sA.2.2.2.2.2 (base + j) (by dsimp only [fl]; rcases hdisj with h' | h' <;> omega)
  exact ⟨(heq 0 (by decide)).trans hhdr.1, (heq 1 (by decide)).trans hhdr.2.1,
    (heq 2 (by decide)).trans hhdr.2.2.1, (heq 3 (by decide)).trans hhdr.2.2.2.1,
    (heq 4 (by decide)).trans hhdr.2.2.2.2.1, (heq 5 (by decide)).trans hhdr.2.2.2.2.2.1,
    (heq 6 (by decide)).trans hhdr.2.2.2.2.2.2.1,
    (heq 7 (by decide)).trans hhdr.2.2.2.2.2.2.2.1,
    (heq 8 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.1,
    (heq 9 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.2⟩

private def writeLargeOffsProg : ℕ × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (pBase, pgB) => do
    writeOffHashProg pBase
    writeOffBpProg pBase
    writeOffBtProg pBase
    writeOffTriePageProg (pBase, pgB)

private def writeOffBtTrieProg : ℕ × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (pBase, pgB) => do
    writeOffBtProg pBase
    writeOffTriePageProg (pBase, pgB)

private theorem realizesBounded_writeOffBtTrie :
    RealizesBounded .exact writeOffBtTrieProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w (pBase, pgB) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          pgB = pageSizeWhp fl.N ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 46 ≤ s.frontier ∧
          (∀ k ≤ 28, s.mem (pBase + k) = fl.paramWord k) ∧
          s.mem (pBase + 36) = offBTreeMeta fl.c w fl.N)
      (fun _ _ => 0) := by
  have hBt := realizesBounded_writeOffBt
  have hTP := realizesBounded_writeOffTriePage
  realize
  · rcases d with ⟨pBase, pgB⟩
    dsimp only at *
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf, h28, hm36⟩ := h
    subst hp_eq; subst hw_eq
    exact ⟨fl, rfl, rfl, hth, hNU, hU, hmf, by omega,
      h28 2 (by decide), h28 11 (by decide), h28 16 (by decide),
      h28 17 (by decide), h28 18 (by decide), h28 21 (by decide), hm36⟩
  · rcases d with ⟨pBase, pgB⟩
    dsimp only at *
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf, h28, hm36⟩ := h
    subst hp_eq; subst hw_eq
    have hw_pos : 0 < fl.w := by
      have := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have sBt := writeOffBtProg_spec (fl := fl) (s := s) hw_pos
      (h28 2 (by decide)) (h28 11 (by decide)) (h28 16 (by decide))
      (h28 17 (by decide)) (h28 18 (by decide)) (h28 21 (by decide)) hm36
    have h28Bt : ∀ k ≤ 28, ((Memory.spec 0).clientState s (writeOffBtProg fl.pBase)).mem
        (fl.pBase + k) = fl.paramWord k := fun k hk =>
      (sBt.2.2.2 _ (by omega)).trans (h28 k hk)
    have h0 : ((Memory.spec 0).clientState s (writeOffBtProg fl.pBase)).mem fl.pBase = fl.N := by
      have hh := h28Bt 0 (by decide)
      simpa only [add_zero, FastEpochLayout.paramWord] using hh
    exact ⟨fl, rfl, rfl, hth, hNU, hU, rfl, hmf, by rw [sBt.1]; exact hpf,
      h0, h28Bt 2 (by decide), h28Bt 7 (by decide), h28Bt 10 (by decide),
      h28Bt 22 (by decide), h28Bt 23 (by decide), sBt.2.2.1 39 (by decide) (by decide)⟩

private theorem writeLargeOffsProg_eq :
    writeLargeOffsProg = (fun x =>
      match x with
      | (pBase, pgB) => do
        writeOffHashProg pBase
        writeOffBpProg pBase
        writeOffBtTrieProg (pBase, pgB)) :=
  funext fun ⟨_, _⟩ => rfl

private theorem realizesBounded_writeLargeOffs :
    RealizesBounded .exact writeLargeOffsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w (pBase, pgB) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ fl.w = w ∧
          whpThreshold fl.c ≤ fl.N ∧ fl.N ≤ fl.U ∧ Fits w fl.U ∧
          pgB = pageSizeWhp fl.N ∧
          Fits w (fl.metaBase + epochMetaWordsWhp fl.c w fl.N) ∧
          pBase + 63 ≤ s.frontier ∧
          (∀ k ≤ 28, s.mem (pBase + k) = fl.paramWord k))
      (fun _ _ => 0) := by
  rw [writeLargeOffsProg_eq]
  have hH := realizesBounded_writeOffHash
  have hBp := realizesBounded_writeOffBp
  have hBT := realizesBounded_writeOffBtTrie
  realize
  · rcases d with ⟨pBase, pgB⟩
    dsimp only at *
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf, h28⟩ := h
    subst hp_eq; subst hw_eq
    exact ⟨fl, rfl, rfl, hth, hNU, hU, hmf, hpf,
      h28 1 (by decide), h28 2 (by decide), h28 5 (by decide), h28 6 (by decide),
      h28 7 (by decide), h28 8 (by decide), h28 9 (by decide)⟩
  · rcases d with ⟨pBase, pgB⟩
    dsimp only at *
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf, h28⟩ := h
    subst hp_eq; subst hw_eq
    have hw_pos : 0 < fl.w := by
      have := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have sH := writeOffHashProg_spec (fl := fl) (s := s) hw_pos
      (h28 1 (by decide)) (h28 2 (by decide)) (h28 5 (by decide)) (h28 6 (by decide))
      (h28 7 (by decide)) (h28 8 (by decide)) (h28 9 (by decide))
    have h28H : ∀ k ≤ 28, ((Memory.spec 0).clientState s (writeOffHashProg fl.pBase)).mem
        (fl.pBase + k) = fl.paramWord k := fun k hk =>
      (sH.2.2.2.2.2.2.2 _ (by omega)).trans (h28 k hk)
    have hfr1 : ((Memory.spec 0).clientState s (writeOffHashProg fl.pBase)).frontier =
        s.frontier := sH.1
    exact ⟨fl, rfl, rfl, hth, hNU, hU, hmf, by rw [hfr1]; omega,
      h28H 2 (by decide), h28H 10 (by decide), h28H 11 (by decide),
      h28H 12 (by decide), h28H 13 (by decide), h28H 14 (by decide),
      h28H 15 (by decide), sH.2.2.2.2.1⟩
  · rcases d with ⟨pBase, pgB⟩
    dsimp only at *
    obtain ⟨fl, hp_eq, hw_eq, hth, hNU, hU, rfl, hmf, hpf, h28⟩ := h
    subst hp_eq; subst hw_eq
    have hw_pos : 0 < fl.w := by
      have := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hstep : ∀ s1 : Memory.State,
        s1 = (Memory.spec 0).clientState s (writeOffHashProg fl.pBase) →
        ∀ s2 : Memory.State,
        s2 = (Memory.spec 0).clientState s1 (writeOffBpProg fl.pBase) →
        ∃ fl' : FastEpochLayout, fl'.pBase = fl.pBase ∧ fl'.w = fl.w ∧
          whpThreshold fl'.c ≤ fl'.N ∧ fl'.N ≤ fl'.U ∧ Fits fl.w fl'.U ∧
          pageSizeWhp fl.N = pageSizeWhp fl'.N ∧
          Fits fl.w (fl'.metaBase + epochMetaWordsWhp fl'.c fl.w fl'.N) ∧
          fl.pBase + 46 ≤ s2.frontier ∧
          (∀ k ≤ 28, s2.mem (fl.pBase + k) = fl'.paramWord k) ∧
          s2.mem (fl.pBase + 36) = offBTreeMeta fl'.c fl.w fl'.N := by
      intro s1 hs1 s2 hs2
      have sH := writeOffHashProg_spec (fl := fl) (s := s) hw_pos
        (h28 1 (by decide)) (h28 2 (by decide)) (h28 5 (by decide)) (h28 6 (by decide))
        (h28 7 (by decide)) (h28 8 (by decide)) (h28 9 (by decide))
      rw [← hs1] at sH
      have h28H : ∀ k ≤ 28, s1.mem (fl.pBase + k) = fl.paramWord k := fun k hk =>
        (sH.2.2.2.2.2.2.2 _ (by omega)).trans (h28 k hk)
      have sBp := writeOffBpProg_spec (fl := fl) (s := s1) hw_pos
        (h28H 2 (by decide)) (h28H 10 (by decide)) (h28H 11 (by decide))
        (h28H 12 (by decide)) (h28H 13 (by decide)) (h28H 14 (by decide))
        (h28H 15 (by decide)) sH.2.2.2.2.1
      rw [← hs2] at sBp
      have h28Bp : ∀ k ≤ 28, s2.mem (fl.pBase + k) = fl.paramWord k := fun k hk =>
        (sBp.2.2.2 _ (by omega)).trans (h28H k hk)
      exact ⟨fl, rfl, rfl, hth, hNU, hU, rfl, hmf, by omega,
        h28Bp, sBp.2.2.1 36 (by decide) (by decide)⟩
    exact hstep _ rfl _ rfl

private theorem writeLargeParamTableProg_eq :
    writeLargeParamTableProg = (fun x =>
      match x with
      | ((base, pBase), ((N, metaBase), ((logN, ell), pgB))) => do
        writeCoreAProg ((base, pBase), ((N, metaBase), logN))
        writeCoreBProg ((base, pBase), (logN, ell))
        writeCoreCProg ((pBase, N), (logN - 12 * ell, ell))
        writeCoreDProg (pBase, (logN, ell))
        writeCoreEProg ((base, pBase), ell)
        writeLargeOffsProg (pBase, pgB)) :=
  funext fun ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ => rfl

/-- `RealizesBounded .exact` witness for `writeLargeParamTableProg` (`¬ReadsWidth`, overflow-free
up to `N = U = 2 ^ w - 1`). -/
theorem realizesBounded_writeLargeParamTable :
    RealizesBounded .exact writeLargeParamTableProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      WriteLargeParamPre
      (fun _ _ => 0) := by
  rw [writeLargeParamTableProg_eq]
  have hA := realizesBounded_writeCoreA
  have hB := realizesBounded_writeCoreB
  have hC := realizesBounded_writeCoreC
  have hD := realizesBounded_writeCoreD
  have hE := realizesBounded_writeCoreE
  have hO := realizesBounded_writeLargeOffs
  realize
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, _, hth, hNU, hU, hV, hVpow, rfl, rfl, rfl, hmf, _, hbf, hpf, hhdr⟩ := h
    exact ⟨c, U, V, hth, hNU, hU, hV, hVpow, rfl,
      lt_of_le_of_lt (Nat.le_add_right _ _) hmf, hbf, by omega, hhdr⟩
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, _, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, hbf, hpf, hhdr⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
    have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
    have hfr1 := sA.1
    dsimp only [fl] at hfr1
    exact ⟨c, U, N, hth, hNU, hU, rfl, rfl, by rw [hfr1]; exact hbf,
      by rw [hfr1]; omega⟩
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, _, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, _, _, _⟩ := h
    have hw11 := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hlog := (largeEpoch_param_bounds hth hNU hU).2.2.1
    have h60 := sixtyThousand_mul_ell_le_log hth
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    dsimp only [Fits] at *; omega
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, _, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, _, _, _⟩ := h
    have hw11 := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hlog := (largeEpoch_param_bounds hth hNU hU).2.2.1
    have h60 := sixtyThousand_mul_ell_le_log hth
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    dsimp only [Fits] at *; omega
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, hdisj, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, _, hpf, hhdr⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
    have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
    have hhdr1 := header_eq_after_A (metaBase := metaBase) hdisj hth hNU hhdr
    have sB := writeCoreBProg_spec (fl := fl) (s := _) hth hNU hhdr1
    have hfr : ((Memory.spec 0).clientState _ (writeCoreBProg _)).frontier = s.frontier :=
      sB.1.trans sA.1
    dsimp only [fl] at hfr
    exact ⟨c, U, hth, hNU, hU, rfl, rfl, by rw [hfr]; omega⟩
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, hdisj, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, _, hpf, hhdr⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
    have hgo : ∀ s1, s1 = (Memory.spec 0).clientState s
        (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N))) →
        ∀ s2, s2 = (Memory.spec 0).clientState s1
          (writeCoreBProg ((base, pBase), (Nat.log 2 N, Dynamic.logLogFactor N))) →
        ∀ s3, s3 = (Memory.spec 0).clientState s2
          (writeCoreCProg ((pBase, N), (bWhp N, Dynamic.logLogFactor N))) →
        ∃ c' U' N', whpThreshold c' ≤ N' ∧ N' ≤ U' ∧ Fits w U' ∧
          Nat.log 2 N = Nat.log 2 N' ∧ Dynamic.logLogFactor N = Dynamic.logLogFactor N' ∧
          pBase + 21 ≤ s3.frontier := by
      intro s1 hs1 s2 hs2 s3 hs3
      have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
      dsimp only [fl] at sA; rw [← hs1] at sA
      have hhdr1 : RootStaticHeader c U V w base s1.mem := by
        rw [hs1]; exact header_eq_after_A (metaBase := metaBase) hdisj hth hNU hhdr
      have sB := writeCoreBProg_spec (fl := fl) (s := s1) hth hNU hhdr1
      dsimp only [fl] at sB; rw [← hs2] at sB
      have sC := writeCoreCProg_spec (fl := fl) (s := s2)
      dsimp only [fl] at sC; rw [← hs3] at sC
      exact ⟨c, U, N, hth, hNU, hU, rfl, rfl, by omega⟩
    exact hgo _ rfl _ rfl _ rfl
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, hdisj, hth, hNU, hU, _, _, rfl, rfl, rfl, _, _, hbf, hpf, hhdr⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
    have hU_th : whpThreshold c ≤ U := hth.trans hNU
    have hgo : ∀ s1, s1 = (Memory.spec 0).clientState s
        (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N))) →
        ∀ s2, s2 = (Memory.spec 0).clientState s1
          (writeCoreBProg ((base, pBase), (Nat.log 2 N, Dynamic.logLogFactor N))) →
        ∀ s3, s3 = (Memory.spec 0).clientState s2
          (writeCoreCProg ((pBase, N), (bWhp N, Dynamic.logLogFactor N))) →
        ∀ s4, s4 = (Memory.spec 0).clientState s3
          (writeCoreDProg (pBase, (Nat.log 2 N, Dynamic.logLogFactor N))) →
        ∃ c' U' N', whpThreshold c' ≤ N' ∧ N' ≤ U' ∧ Fits w U' ∧
          Dynamic.logLogFactor N = Dynamic.logLogFactor N' ∧
          base + 10 ≤ s4.frontier ∧ pBase + 29 ≤ s4.frontier ∧
          s4.mem (base + hdrCEff) = cEff c' ∧
          s4.mem (pBase + 5) = cTabWhp c' ∧
          s4.mem (pBase + 20) = tMinWhp N' := by
      intro s1 hs1 s2 hs2 s3 hs3 s4 hs4
      have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
      dsimp only [fl] at sA; rw [← hs1] at sA
      have hhdr1 : RootStaticHeader c U V w base s1.mem := by
        rw [hs1]; exact header_eq_after_A (metaBase := metaBase) hdisj hth hNU hhdr
      have sB := writeCoreBProg_spec (fl := fl) (s := s1) hth hNU hhdr1
      dsimp only [fl] at sB; rw [← hs2] at sB
      have sC := writeCoreCProg_spec (fl := fl) (s := s2)
      dsimp only [fl] at sC; rw [← hs3] at sC
      have sD := writeCoreDProg_spec (fl := fl) (s := s3)
      dsimp only [fl] at sD; rw [← hs4] at sD
      have hce4 : s4.mem (base + hdrCEff) = cEff c := by
        rw [sD.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          sC.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          sB.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          hhdr1.2.2.2.2.2.2.2.2.2, ite_eq_left hU_th]
      have hct4 : s4.mem (pBase + 5) = cTabWhp c := by
        rw [sD.2.2.2 _ (by omega), sC.2.2.2 _ (by omega)]
        exact sB.2.2.1 5 (by decide) (by decide)
      have htm4 : s4.mem (pBase + 20) = tMinWhp N := sD.2.2.1 20 (by decide) (by decide)
      exact ⟨c, U, N, hth, hNU, hU, rfl, by omega, by omega, hce4, hct4, htm4⟩
    exact hgo _ rfl _ rfl _ rfl _ rfl
  · rcases d with ⟨⟨base, pBase⟩, ⟨⟨N, metaBase⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
    dsimp only [WriteLargeParamPre] at h; dsimp only at *
    obtain ⟨c, U, V, hdisj, hth, hNU, hU, _, _, rfl, rfl, rfl, hmf, _, _, hpf, hhdr⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
    have hU_th : whpThreshold c ≤ U := hth.trans hNU
    have hgo : ∀ s1, s1 = (Memory.spec 0).clientState s
        (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N))) →
        ∀ s2, s2 = (Memory.spec 0).clientState s1
          (writeCoreBProg ((base, pBase), (Nat.log 2 N, Dynamic.logLogFactor N))) →
        ∀ s3, s3 = (Memory.spec 0).clientState s2
          (writeCoreCProg ((pBase, N), (bWhp N, Dynamic.logLogFactor N))) →
        ∀ s4, s4 = (Memory.spec 0).clientState s3
          (writeCoreDProg (pBase, (Nat.log 2 N, Dynamic.logLogFactor N))) →
        ∀ s5, s5 = (Memory.spec 0).clientState s4
          (writeCoreEProg ((base, pBase), Dynamic.logLogFactor N)) →
        ∃ fl' : FastEpochLayout, fl'.pBase = pBase ∧ fl'.w = w ∧
          whpThreshold fl'.c ≤ fl'.N ∧ fl'.N ≤ fl'.U ∧ Fits w fl'.U ∧
          pageSizeWhp N = pageSizeWhp fl'.N ∧
          Fits w (fl'.metaBase + epochMetaWordsWhp fl'.c w fl'.N) ∧
          pBase + 63 ≤ s5.frontier ∧
          (∀ k ≤ 28, s5.mem (pBase + k) = fl'.paramWord k) := by
      intro s1 hs1 s2 hs2 s3 hs3 s4 hs4 s5 hs5
      have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
      dsimp only [fl] at sA; rw [← hs1] at sA
      have hhdr1 : RootStaticHeader c U V w base s1.mem := by
        rw [hs1]; exact header_eq_after_A (metaBase := metaBase) hdisj hth hNU hhdr
      have sB := writeCoreBProg_spec (fl := fl) (s := s1) hth hNU hhdr1
      dsimp only [fl] at sB; rw [← hs2] at sB
      have sC := writeCoreCProg_spec (fl := fl) (s := s2)
      dsimp only [fl] at sC; rw [← hs3] at sC
      have sD := writeCoreDProg_spec (fl := fl) (s := s3)
      dsimp only [fl] at sD; rw [← hs4] at sD
      have hce4 : s4.mem (base + hdrCEff) = cEff c := by
        rw [sD.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          sC.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          sB.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
          hhdr1.2.2.2.2.2.2.2.2.2, ite_eq_left hU_th]
      have hct4 : s4.mem (pBase + 5) = cTabWhp c := by
        rw [sD.2.2.2 _ (by omega), sC.2.2.2 _ (by omega)]
        exact sB.2.2.1 5 (by decide) (by decide)
      have htm4 : s4.mem (pBase + 20) = tMinWhp N := sD.2.2.1 20 (by decide) (by decide)
      have sE := writeCoreEProg_spec (fl := fl) (s := s4) hce4 hct4 htm4
      dsimp only [fl] at sE; rw [← hs5] at sE
      refine ⟨fl, rfl, rfl, hth, hNU, hU, rfl, hmf, by omega, fun k hk => ?_⟩
      by_cases h21 : 21 ≤ k
      · exact sE.2.2.1 k h21 hk
      · rw [sE.2.2.2 _ (by omega)]
        by_cases h16 : 16 ≤ k
        · exact sD.2.2.1 k h16 (by omega)
        · rw [sD.2.2.2 _ (by omega)]
          by_cases h11 : 11 ≤ k
          · exact sC.2.2.1 k h11 (by omega)
          · rw [sC.2.2.2 _ (by omega)]
            by_cases h5 : 5 ≤ k
            · exact sB.2.2.1 k h5 (by omega)
            · rw [sB.2.2.2 _ (by omega)]; exact sA.2.2.1 k (by omega)
    exact hgo _ rfl _ rfl _ rfl _ rfl _ rfl

private theorem vh_bind {α β : Type} {w : ℕ} {st : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState st p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState st p)
        (q ((Memory.spec 0).clientResult st p)))) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (p.bind q)) := by
  rw [validHistory_bind, clientResult_width, clientState_width]; exact ⟨hp, hq⟩

private theorem vh_writeCoreA {c U V w base pBase N metaBase : ℕ} {s : Memory.State}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : 0 < V) (hVpow : V ≤ 2 ^ w)
    (hmf : Fits w metaBase) (hred : redWidthWhp U ≤ w) (hbf : base + 10 ≤ s.frontier)
    (hpf : pBase + 48 ≤ s.frontier) (hhdr : RootStaticHeader c U V w base s.mem) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeCoreAProg ((base, pBase), ((N, metaBase), Nat.log 2 N)))) := by
  have hb := header_bounds hth hNU hU
  have hU_th : whpThreshold c ≤ U := hth.trans hNU
  have hU_m : Fits w (U - 1) := by dsimp only [Fits] at hU ⊢; omega
  have hV_m : Fits w (V - 1) := by dsimp only [Fits]; omega
  have hN_f : Fits w N := lt_of_le_of_lt hNU hU
  have hct_f : Fits w (cTabWhp c * bCharWhp N) :=
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold writeCoreAProg
  refine vh_rd (by unfold hdrU1; omega) <| vh_rd (by unfold hdrV1; omega) <|
    vh_rd (by unfold hdrW; omega) <| vh_rd (by unfold hdrRedW; omega) <|
    vh_rd (by unfold hdrCTab; omega) ?_
  rw [hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.2.2.2.2.2.1,
    hhdr.2.2.2.2.2.2.1, ite_eq_left hU_th]
  exact vh_wr (by omega) hN_f <| vh_wr (by omega) hmf <|
    vh_wr (by omega) hb.1 <| vh_wr (by omega) (lt_of_le_of_lt hred hb.1) <|
    vh_wr (by omega) hct_f <| vh_wr (by omega) hU_m <|
    vh_wr_last (by omega) hV_m

private theorem vh_writeCoreB {c U V w base pBase N : ℕ} {s : Memory.State}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hbf : base + 10 ≤ s.frontier) (hpf : pBase + 11 ≤ s.frontier)
    (hhdr : RootStaticHeader c U V w base s.mem) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeCoreBProg ((base, pBase), (Nat.log 2 N, Dynamic.logLogFactor N)))) := by
  have hb := header_bounds hth hNU hU
  have hU_th : whpThreshold c ≤ U := hth.trans hNU
  have hpt : Nat.log 2 N + 1 = globalPtrBits N :=
    (clog_succ_eq_of_log ((whpThreshold_pos c).trans_le hth)).symm
  have hcb_f : Fits w (cTabWhp c) := lt_trans hb.2.1 hb.1
  have hdt_f : Fits w (dTabWhp c) := lt_of_le_of_lt (hb.2.2.1.trans hNU) hU
  have hbc_f : Fits w (bCharWhp N) := lt_trans hb.2.2.2.1 hb.1
  have hbw_f : Fits w (bWhp N) := lt_trans hb.2.2.2.2.1 hb.1
  have hfp_f : Fits w (fpBitsWhp N) := lt_trans hb.2.2.2.2.2.1 hb.1
  have hgp_f : Fits w (Nat.log 2 N + 1) := by
    rw [hpt]; exact lt_of_le_of_lt hb.2.2.2.2.2.2.1 hb.1
  unfold writeCoreBProg
  refine vh_rd (by unfold hdrCTab; omega) <| vh_rd (by unfold hdrDTab; omega) ?_
  rw [hhdr.2.2.2.2.2.2.1, hhdr.2.2.2.2.2.2.2.1]
  simp only [ite_eq_left hU_th]
  exact vh_wr (by omega) hcb_f <| vh_wr (by omega) hdt_f <|
    vh_wr (by omega) hbc_f <| vh_wr (by omega) hbw_f <|
    vh_wr (by omega) hfp_f <| vh_wr_last (by omega) hgp_f

private theorem vh_writeCoreC {c U w pBase N : ℕ} {s : Memory.State}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hpf : pBase + 16 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeCoreCProg ((pBase, N), (bWhp N, Dynamic.logLogFactor N)))) := by
  have hb := header_bounds hth hNU hU
  have hfit_N : ∀ x, x ≤ N → Fits w x := fun x hx => lt_of_le_of_lt (hx.trans hNU) hU
  unfold writeCoreCProg; dsimp only
  simp only [shift_one_eq, ← slabScale_pow_eq_shift]
  exact vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr_last (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.2.1)

private theorem vh_writeCoreD {c U w pBase N : ℕ} {s : Memory.State}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hpf : pBase + 21 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeCoreDProg (pBase, (Nat.log 2 N, Dynamic.logLogFactor N)))) := by
  have hb := header_bounds hth hNU hU
  unfold writeCoreDProg; dsimp only; rw [tmin_val_eq]
  exact vh_wr (by omega) (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1) <|
    vh_wr (by omega) (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1) <|
    vh_wr (by omega) (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1) <|
    vh_wr (by omega) (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1) <|
    vh_wr_last (by omega) (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1)

private theorem vh_writeCoreE {c U w base pBase N : ℕ} {s : Memory.State}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hbf : base + 10 ≤ s.frontier) (hpf : pBase + 29 ≤ s.frontier)
    (hce : s.mem (base + hdrCEff) = cEff c)
    (hct : s.mem (pBase + 5) = cTabWhp c)
    (htm : s.mem (pBase + 20) = tMinWhp N) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeCoreEProg ((base, pBase), Dynamic.logLogFactor N))) := by
  have hb := header_bounds hth hNU hU
  have hfit_N : ∀ x, x ≤ N → Fits w x := fun x hx => lt_of_le_of_lt (hx.trans hNU) hU
  have h32 : 32 * slabScale N ^ 12 ≤ N :=
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold writeCoreEProg
  refine vh_rd (by unfold hdrCEff; omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  rw [hce, hct, htm]; dsimp only
  simp only [shift_one_eq, ← slabScale_pow_eq_shift]
  exact vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) <|
    vh_wr (by omega) (hfit_N _ (by omega)) <|
    vh_wr (by omega) (hfit_N _ (by omega)) <|
    vh_wr (by omega) (hfit_N _ (by omega)) <|
    vh_wr_last (by omega)
      (lt_trans hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb.1)

private theorem vh_writeOffHash {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U) (hU : Fits fl.w fl.U)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 63 ≤ s.frontier)
    (hm : ∀ k ≤ 28, s.mem (fl.pBase + k) = fl.paramWord k) :
    (Memory.spec fl.w).ValidHistory s
      ((Memory.spec fl.w).clientHistory s (writeOffHashProg fl.pBase)) := by
  have hb := header_bounds hth hNU hU
  have hmono := sublinear_word_fits_le (w := fl.w) hth
  have hw_pos : 0 < fl.w := by omega
  have hfit_M : ∀ x, x ≤ epochMetaWordsWhp fl.c fl.w fl.N → Fits fl.w x := fun x hx =>
    lt_of_le_of_lt (hx.trans (Nat.le_add_left _ _)) hmf
  unfold writeOffHashProg
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  rw [hm 1 (by decide), hm 2 (by decide), hm 5 (by decide), hm 6 (by decide),
    hm 7 (by decide), hm 8 (by decide), hm 9 (by decide), shift_one_eq]
  change (Memory.spec fl.w).ValidHistory s ((Memory.spec fl.w).clientHistory s
    ((packedWordsSafeProg _).bind fun topW =>
      (packedWordsSafeProg _).bind fun botWB =>
        (packedWordsSafeProg _).bind fun botWF => _))
  refine vh_bind trivial (vh_bind trivial (vh_bind trivial ?_))
  have hres : ∀ n k, (Memory.spec 0).clientResult s (packedWordsSafeProg ((n, k), fl.w)) =
      packedWords n k fl.w := fun _ _ => packedWordsSafe_eq hw_pos
  have hst : ∀ n k, (Memory.spec 0).clientState s (packedWordsSafeProg ((n, k), fl.w)) = s :=
    fun _ _ => rfl
  simp only [FastEpochLayout.paramWord, hres, hst]
  have hmul : (cTabWhp fl.c + 1) * (dTabWhp fl.c * 2 ^ bCharWhp fl.N) =
      BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
    ring
  rw [hmul]
  have hfp : 32 + (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
      (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
      packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (bWhp fl.N) fl.w =
      offFpHash fl.c fl.w fl.N := by
    unfold offFpHash offBktHash BitPackedDoubleTabulation.space
      BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
      BitPackedDoubleTabulation.botEntries; omega
  have hbm : offFpHash fl.c fl.w fl.N +
      (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
      packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (fpBitsWhp fl.N) fl.w =
      offBktMeta fl.c fl.w fl.N := by
    unfold offBktMeta BitPackedDoubleTabulation.space
      BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
      BitPackedDoubleTabulation.botEntries; omega
  have hdt : 1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N)) (bCharWhp fl.N) fl.w ≤ offFpHash fl.c fl.w fl.N := by
    unfold offFpHash offBktHash BitPackedDoubleTabulation.space
      BitPackedDoubleTabulation.topWords; omega
  rw [hfp, hbm]
  exact vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (by dsimp only [Fits] at hmf ⊢; omega) <|
    vh_wr_last (by omega) (by dsimp only [Fits] at hmf ⊢; omega)

private theorem vh_writeOffBp {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hw_pos : 0 < fl.w)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 37 ≤ s.frontier)
    (hm : ∀ k ≤ 28, s.mem (fl.pBase + k) = fl.paramWord k)
    (hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N) :
    (Memory.spec fl.w).ValidHistory s
      ((Memory.spec fl.w).clientHistory s (writeOffBpProg fl.pBase)) := by
  have hmono := sublinear_word_fits_le (w := fl.w) hth
  have hfit_M : ∀ x, x ≤ epochMetaWordsWhp fl.c fl.w fl.N → Fits fl.w x := fun x hx =>
    lt_of_le_of_lt (hx.trans (Nat.le_add_left _ _)) hmf
  have hstep : ∀ (st : Memory.State) (off prev n k : ℕ) (f : ℕ → Memory.Prog Unit),
      off ≤ 36 → st.frontier = s.frontier →
      Fits fl.w (prev + packedWords n k fl.w) →
      (Memory.spec fl.w).ValidHistory
        ⟨Function.update st.mem (fl.pBase + off) (prev + packedWords n k fl.w), st.frontier⟩
        ((Memory.spec fl.w).clientHistory
          ⟨Function.update st.mem (fl.pBase + off) (prev + packedWords n k fl.w), st.frontier⟩
          (f (prev + packedWords n k fl.w))) →
      (Memory.spec fl.w).ValidHistory st
        ((Memory.spec fl.w).clientHistory st
          ((addPackedWriteProg (((fl.pBase, off), (prev, n)), (k, fl.w))).bind f)) := by
    intro st off prev n k f hoff hfr hf hr
    refine vh_bind (validHistory_addPackedWrite hw_pos (by omega) hf) ?_
    have hsp := addPackedWriteProg_spec (pBase := fl.pBase) (off := off) (prev := prev) (n := n)
      (k := k) hw_pos st
    rw [hsp.1, hsp.2.1]; exact hr
  unfold writeOffBpProg
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  rw [hm 2 (by decide), hm 10 (by decide), hm 11 (by decide), hm 12 (by decide),
    hm 13 (by decide), hm 14 (by decide), hm 15 (by decide), hm31]
  dsimp only [FastEpochLayout.paramWord]
  exact hstep _ 32 _ _ _ _ (by decide) rfl
      (hfit_M _ (by change offSlabDir fl.c fl.w fl.N ≤ _; omega)) <|
    hstep _ 33 _ _ _ _ (by decide) rfl
      (hfit_M _ (by change offTailDir fl.c fl.w fl.N ≤ _; omega)) <|
    hstep _ 34 _ _ _ _ (by decide) rfl
      (hfit_M _ (by change offSlabOwner fl.c fl.w fl.N ≤ _; omega)) <|
    hstep _ 35 _ _ _ _ (by decide) rfl
      (hfit_M _ (by change offTailOwner fl.c fl.w fl.N ≤ _; omega)) <|
    hstep _ 36 _ _ _ _ (by decide) rfl
      (hfit_M _ (by change offBTreeMeta fl.c fl.w fl.N ≤ _; omega))
      trivial

private theorem vh_writeOffBt {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hw_pos : 0 < fl.w)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 40 ≤ s.frontier)
    (hm : ∀ k ≤ 28, s.mem (fl.pBase + k) = fl.paramWord k)
    (hm36 : s.mem (fl.pBase + 36) = offBTreeMeta fl.c fl.w fl.N) :
    (Memory.spec fl.w).ValidHistory s
      ((Memory.spec fl.w).clientHistory s (writeOffBtProg fl.pBase)) := by
  have hmono := sublinear_word_fits_le (w := fl.w) hth
  have hfit_M : ∀ x, x ≤ epochMetaWordsWhp fl.c fl.w fl.N → Fits fl.w x := fun x hx =>
    lt_of_le_of_lt (hx.trans (Nat.le_add_left _ _)) hmf
  have hm2 : s.mem (fl.pBase + 2) = fl.w := hm 2 (by decide)
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hm 11 (by decide)
  have hm16 : s.mem (fl.pBase + 16) = nodeMetaBitsWhp fl.N := hm 16 (by decide)
  have hm17 : s.mem (fl.pBase + 17) = keysWordBitsWhp fl.N := hm 17 (by decide)
  have hm18 : s.mem (fl.pBase + 18) = valsWordBitsWhp fl.N := hm 18 (by decide)
  have hm21 : s.mem (fl.pBase + 21) = nSliceWhp fl.N := hm 21 (by decide)
  have hstep : ∀ (st : Memory.State) (off prev n k : ℕ) (f : ℕ → Memory.Prog Unit),
      off ≤ 39 → st.frontier = s.frontier →
      Fits fl.w (prev + packedWords n k fl.w) →
      (Memory.spec fl.w).ValidHistory
        ⟨Function.update st.mem (fl.pBase + off) (prev + packedWords n k fl.w), st.frontier⟩
        ((Memory.spec fl.w).clientHistory
          ⟨Function.update st.mem (fl.pBase + off) (prev + packedWords n k fl.w), st.frontier⟩
          (f (prev + packedWords n k fl.w))) →
      (Memory.spec fl.w).ValidHistory st
        ((Memory.spec fl.w).clientHistory st
          ((addPackedWriteProg (((fl.pBase, off), (prev, n)), (k, fl.w))).bind f)) := by
    intro st off prev n k f hoff hfr hf hr
    refine vh_bind (validHistory_addPackedWrite hw_pos (by omega) hf) ?_
    have hsp := addPackedWriteProg_spec (pBase := fl.pBase) (off := off) (prev := prev) (n := n)
      (k := k) hw_pos st
    rw [hsp.1, hsp.2.1]; exact hr
  unfold writeOffBtProg
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  rw [hm2, hm11, hm16, hm17, hm18, hm21, hm36]
  have h37 : offBTreeMeta fl.c fl.w fl.N +
      packedWords (3 * numBucketsWhp fl.N * nSliceWhp fl.N) (nodeMetaBitsWhp fl.N) fl.w =
      offBTreeKeys fl.c fl.w fl.N := rfl
  have h38 : offBTreeKeys fl.c fl.w fl.N +
      packedWords (3 * numBucketsWhp fl.N * nSliceWhp fl.N) (keysWordBitsWhp fl.N) fl.w =
      offBTreeVals fl.c fl.w fl.N := rfl
  have h39 : offBTreeVals fl.c fl.w fl.N +
      packedWords (3 * numBucketsWhp fl.N * nSliceWhp fl.N) (valsWordBitsWhp fl.N) fl.w =
      offTrieChild fl.c fl.w fl.N 0 := by
    unfold offTrieChild totalBTreeNodesWhp; omega
  exact hstep _ 37 _ _ _ _ (by decide) rfl
      (hfit_M _ (by rw [h37]; omega)) <|
    hstep _ 38 _ _ _ _ (by decide) rfl
      (hfit_M _ (by rw [h37, h38]; omega)) <|
    hstep _ 39 _ _ _ _ (by decide) rfl
      (hfit_M _ (by rw [h37, h38, h39]; omega)) trivial

private theorem vh_writeOffTriePage {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hw_pos : 0 < fl.w)
    (hmf : Fits fl.w (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
    (hpf : fl.pBase + 46 ≤ s.frontier)
    (hm : ∀ k ≤ 28, s.mem (fl.pBase + k) = fl.paramWord k)
    (hm39 : s.mem (fl.pBase + 39) = offTrieChild fl.c fl.w fl.N 0) :
    (Memory.spec fl.w).ValidHistory s
      ((Memory.spec fl.w).clientHistory s
        (writeOffTriePageProg (fl.pBase, pageSizeWhp fl.N))) := by
  have hmono := sublinear_word_fits_le (w := fl.w) hth
  have heq_end := offEpochEnd_eq_epochMetaWordsWhp (w := fl.w) hth
  have hfit_M : ∀ x, x ≤ epochMetaWordsWhp fl.c fl.w fl.N → Fits fl.w x := fun x hx =>
    lt_of_le_of_lt (hx.trans (Nat.le_add_left _ _)) hmf
  have hm0 : s.mem fl.pBase = fl.N := by
    have h0 := hm 0 (by decide); simpa only [add_zero, FastEpochLayout.paramWord] using h0
  unfold writeOffTriePageProg
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  rw [hm0, hm 2 (by decide), hm 7 (by decide), hm 10 (by decide),
    hm 22 (by decide), hm 23 (by decide), hm39, shift_one_eq]
  dsimp only [FastEpochLayout.paramWord]
  refine vh_bind trivial (vh_bind trivial (vh_bind trivial ?_))
  have hcr : ∀ n k st, (Memory.spec 0).clientResult st (packedWordsSafeProg ((n, k), fl.w)) =
      packedWords n k fl.w := fun _ _ _ => packedWordsSafe_eq hw_pos
  have hcs : ∀ n k st, (Memory.spec 0).clientState st (packedWordsSafeProg ((n, k), fl.w)) = st :=
    fun _ _ _ => rfl
  simp only [hcr, hcs]
  have e40 : offTrieChild fl.c fl.w fl.N 0 + trieChildWords fl.c fl.w fl.N =
      offTrieChild fl.c fl.w fl.N 1 := by unfold offTrieChild; omega
  have e41 : offTrieChild fl.c fl.w fl.N 1 + trieChildWords fl.c fl.w fl.N =
      offTrieNode fl.c fl.w fl.N 0 := by unfold offTrieNode offTrieChild; omega
  have e42 : offTrieNode fl.c fl.w fl.N 0 + trieNodeWords fl.c fl.w fl.N =
      offTrieNode fl.c fl.w fl.N 1 := by unfold offTrieNode; omega
  have e43 : offTrieNode fl.c fl.w fl.N 1 + trieNodeWords fl.c fl.w fl.N =
      offTrieItem fl.c fl.w fl.N 0 := by unfold offTrieItem offTrieNode; omega
  have e44 : offTrieItem fl.c fl.w fl.N 0 + trieItemWords fl.w fl.N =
      offTrieItem fl.c fl.w fl.N 1 := by unfold offTrieItem; omega
  have ePD : offTrieItem fl.c fl.w fl.N 1 + trieItemWords fl.w fl.N =
      offPageDir fl.c fl.w fl.N := by unfold offPageDir offTrieItem; omega
  simp only [trieChildWords, trieNodeWords, trieItemWords] at e40 e41 e42 e43 e44 ePD
  rw [e40, e41, e42, e43, e44, ePD]
  refine vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) <|
    vh_wr (by omega) (hfit_M _ (by omega)) ?_
  refine vh_bind trivial ?_
  rw [hcr, hcs]
  exact vh_bind (validHistory_addPackedWrite hw_pos (by change fl.pBase + 45 < s.frontier; omega)
    (hfit_M _ (by change offEpochEnd fl.c fl.w fl.N ≤ _; rw [heq_end]))) trivial

private theorem vh_seq {w : ℕ} {α β : Type} {st : Memory.State} {p : Memory.Prog α}
    {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st p))
    (hq : ∀ st' : Memory.State, st' = (Memory.spec 0).clientState st p →
      ∀ r : α, r = (Memory.spec 0).clientResult st p →
      (Memory.spec w).ValidHistory st' ((Memory.spec w).clientHistory st' (q r))) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (p.bind q)) :=
  vh_bind hp (hq _ rfl _ rfl)

/-- Memory admissibility (`ValidHistory`) for `writeLargeParamTableProg`. -/
theorem validHistory_writeLargeParamTableProg {w base pBase N metaBase : ℕ}
    {s : Memory.State}
    (hpre : WriteLargeParamPre w
      ((base, pBase), ((N, metaBase), ((Nat.log 2 N, Dynamic.logLogFactor N), pageSizeWhp N)))
      s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeLargeParamTableProg ((base, pBase), ((N, metaBase),
          ((Nat.log 2 N, Dynamic.logLogFactor N), pageSizeWhp N))))) := by
  obtain ⟨c, U, V, hdisj, hth, hNU, hU, hV, hVpow, _, _, _, hmf, hred, hbf, hpf, hhdr⟩ := hpre
  have hw_pos : 0 < w := by
    have := (header_bounds hth hNU hU).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hmf_m : Fits w metaBase := lt_of_le_of_lt (Nat.le_add_right _ _) hmf
  let fl : FastEpochLayout := ⟨c, U, V, w, N, metaBase, pBase, dummy_io⟩
  have hU_th : whpThreshold c ≤ U := hth.trans hNU
  unfold writeLargeParamTableProg
  refine vh_seq (vh_writeCoreA hth hNU hU hV hVpow hmf_m hred hbf (by omega) hhdr)
    fun s1 hs1 _ _ => ?_
  have sA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
  dsimp only [fl] at sA; rw [← hs1] at sA
  have hhdr1 : RootStaticHeader c U V w base s1.mem := by
    rw [hs1]; exact header_eq_after_A (metaBase := metaBase) hdisj hth hNU hhdr
  have hfr1 : s1.frontier = s.frontier := sA.1
  refine vh_seq (vh_writeCoreB hth hNU hU (by omega) (by omega) hhdr1) fun s2 hs2 _ _ => ?_
  have sB := writeCoreBProg_spec (fl := fl) (s := s1) hth hNU hhdr1
  dsimp only [fl] at sB; rw [← hs2] at sB
  have hfr2 : s2.frontier = s.frontier := sB.1.trans hfr1
  refine vh_seq (vh_writeCoreC hth hNU hU (by omega)) fun s3 hs3 _ _ => ?_
  change s3 = (Memory.spec 0).clientState s2
    (writeCoreCProg ((pBase, N), (bWhp N, Dynamic.logLogFactor N))) at hs3
  have sC := writeCoreCProg_spec (fl := fl) (s := s2)
  dsimp only [fl] at sC; rw [← hs3] at sC
  have hfr3 : s3.frontier = s.frontier := sC.1.trans hfr2
  refine vh_seq (vh_writeCoreD hth hNU hU (by omega)) fun s4 hs4 _ _ => ?_
  have sD := writeCoreDProg_spec (fl := fl) (s := s3)
  dsimp only [fl] at sD; rw [← hs4] at sD
  have hfr4 : s4.frontier = s.frontier := sD.1.trans hfr3
  have hce4 : s4.mem (base + hdrCEff) = cEff c := by
    rw [sD.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
      sC.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
      sB.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h' | h' <;> omega),
      hhdr1.2.2.2.2.2.2.2.2.2, ite_eq_left hU_th]
  have hct4 : s4.mem (pBase + 5) = cTabWhp c := by
    rw [sD.2.2.2 _ (by omega), sC.2.2.2 _ (by omega)]
    exact sB.2.2.1 5 (by decide) (by decide)
  have htm4 : s4.mem (pBase + 20) = tMinWhp N := sD.2.2.1 20 (by decide) (by decide)
  refine vh_seq (vh_writeCoreE hth hNU hU (by omega) (by omega) hce4 hct4 htm4)
    fun s5 hs5 _ _ => ?_
  have sE := writeCoreEProg_spec (fl := fl) (s := s4) hce4 hct4 htm4
  dsimp only [fl] at sE; rw [← hs5] at sE
  have hfr5 : s5.frontier = s.frontier := sE.1.trans hfr4
  have h28 : ∀ k ≤ 28, s5.mem (pBase + k) = fl.paramWord k := fun k hk => by
    by_cases h21 : 21 ≤ k
    · exact sE.2.2.1 k h21 hk
    · rw [sE.2.2.2 _ (by omega)]
      by_cases h16 : 16 ≤ k
      · exact sD.2.2.1 k h16 (by omega)
      · rw [sD.2.2.2 _ (by omega)]
        by_cases h11 : 11 ≤ k
        · exact sC.2.2.1 k h11 (by omega)
        · rw [sC.2.2.2 _ (by omega)]
          by_cases h5 : 5 ≤ k
          · exact sB.2.2.1 k h5 (by omega)
          · rw [sB.2.2.2 _ (by omega)]; exact sA.2.2.1 k (by omega)
  refine vh_seq (vh_writeOffHash (fl := fl) hth hNU hU hmf (by dsimp only [fl]; omega) h28)
    fun s6 hs6 _ _ => ?_
  have sH := writeOffHashProg_spec (fl := fl) (s := s5) hw_pos
    (h28 1 (by decide)) (h28 2 (by decide)) (h28 5 (by decide)) (h28 6 (by decide))
    (h28 7 (by decide)) (h28 8 (by decide)) (h28 9 (by decide))
  dsimp only [fl] at sH; rw [← hs6] at sH
  have hfr6 : s6.frontier = s.frontier := sH.1.trans hfr5
  have h28H : ∀ k ≤ 28, s6.mem (pBase + k) = fl.paramWord k := fun k hk =>
    (sH.2.2.2.2.2.2.2 _ (by omega)).trans (h28 k hk)
  refine vh_seq (vh_writeOffBp (fl := fl) hth hw_pos hmf (by dsimp only [fl]; omega)
      h28H sH.2.2.2.2.1)
    fun s7 hs7 _ _ => ?_
  have sBp := writeOffBpProg_spec (fl := fl) (s := s6) hw_pos
    (h28H 2 (by decide)) (h28H 10 (by decide)) (h28H 11 (by decide))
    (h28H 12 (by decide)) (h28H 13 (by decide)) (h28H 14 (by decide))
    (h28H 15 (by decide)) sH.2.2.2.2.1
  dsimp only [fl] at sBp; rw [← hs7] at sBp
  have hfr7 : s7.frontier = s.frontier := sBp.1.trans hfr6
  have h28Bp : ∀ k ≤ 28, s7.mem (pBase + k) = fl.paramWord k := fun k hk =>
    (sBp.2.2.2 _ (by omega)).trans (h28H k hk)
  refine vh_seq (vh_writeOffBt (fl := fl) hth hw_pos hmf (by dsimp only [fl]; omega) h28Bp
    (sBp.2.2.1 36 (by decide) (by decide))) fun s8 hs8 _ _ => ?_
  have sBt := writeOffBtProg_spec (fl := fl) (s := s7) hw_pos
    (h28Bp 2 (by decide)) (h28Bp 11 (by decide)) (h28Bp 16 (by decide))
    (h28Bp 17 (by decide)) (h28Bp 18 (by decide)) (h28Bp 21 (by decide))
    (sBp.2.2.1 36 (by decide) (by decide))
  dsimp only [fl] at sBt; rw [← hs8] at sBt
  have hfr8 : s8.frontier = s.frontier := sBt.1.trans hfr7
  have h28Bt : ∀ k ≤ 28, s8.mem (pBase + k) = fl.paramWord k := fun k hk =>
    (sBt.2.2.2 _ (by omega)).trans (h28Bp k hk)
  exact vh_writeOffTriePage (fl := fl) hth hw_pos hmf (by dsimp only [fl]; omega) h28Bt
    (sBt.2.2.1 39 (by decide) (by decide))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
