/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Split-Pair Sliding, Word Zeroing, and `BoundedFrameProg` Combinators (`SplitPairProg`)

This module provides:
1. **Batched split-pair sliding and word zeroing (`splitPairWrite`, `splitPairReadProg`,
   `splitPairWriteProg`, `slideUpBatchProg`, `slideDownBatchProg`, `zeroWordsBatchProg`):**
   Overflow-free `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`) primitives for Phase 1
   upward pair sliding, Phase 1 incremental metadata word zeroing, and Phase 3 downward pair sliding
   on 2-slice `(q_bits, v_bits)` streams (`V ≤ 2 ^ w`, including `V = 2 ^ w`).
2. **Compositional `BoundedFrameProg` calculus:**
   Bundles `frontier` preservation, `memoryCost ≤ C`, and word-level frame preservation outside a
   modifiable address predicate `Mod : ℕ → Prop` across `pure`, `read`, `write`, `bind`, `ite`,
   `iterate`, packed-array, and 2-slice pair-stream operations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.splitPairWrite`,
  `splitPairReadProg`, `splitPairWriteProg`, `slideUpBatchProg`, `slideDownBatchProg`,
  `zeroWordsBatchProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.BoundedFrameProg`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
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
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Split-Pair Write, Batched Sliding, and Batched Word Zeroing -/

/-- Pure write of `(q, v)` at `idx` into a 2-slice split pair stream (`< s_split` at `lo`,
`≥ s_split` at `hi`). -/
@[expose] def splitPairWrite (cfg : SplitPairCfg) (s_split : ℕ) (mem : ℕ → ℕ)
    (idx q v : ℕ) : ℕ → ℕ :=
  if idx < s_split then
    writePair cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem idx q v
  else
    writePair cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem idx q v

theorem splitPairRead_splitPairWrite_self {cfg : SplitPairCfg} {s_split idx q v : ℕ}
    (hw : 0 < cfg.w) (mem : ℕ → ℕ)
    (hq : q < 2 ^ (if idx < s_split then cfg.qBitsLo else cfg.qBitsHi))
    (hv : v < 2 ^ (if idx < s_split then cfg.vBitsLo else cfg.vBitsHi)) :
    splitPairRead cfg s_split (splitPairWrite cfg s_split mem idx q v) idx = (q, v) := by
  unfold splitPairRead splitPairWrite
  split_ifs with hlt
  · simp only [hlt, ↓reduceIte] at hq hv
    exact Prod.ext (pairQuotAt_writePair_self hw mem hq) (pairValAt_writePair_self mem hv)
  · simp only [hlt, ↓reduceIte] at hq hv
    exact Prod.ext (pairQuotAt_writePair_self hw mem hq) (pairValAt_writePair_self mem hv)

theorem writePair_ne_of_lt {base qB vB w d q v addr : ℕ}
    (mem : ℕ → ℕ) (h1 : addr < base + wOffQ qB vB w d) (hle : wOffQ qB vB w d ≤ wOffV qB vB w d) :
    writePair base qB vB w mem d q v addr = mem addr := by
  unfold writePair writePairVal writePairQuot writeBitSlice
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem writePair_ne_of_gt {base qB vB w d q v addr : ℕ}
    (mem : ℕ → ℕ) (h1 : base + wOffV qB vB w d + 1 < addr)
    (hle : wOffQ qB vB w d ≤ wOffV qB vB w d) :
    writePair base qB vB w mem d q v addr = mem addr := by
  unfold writePair writePairVal writePairQuot writeBitSlice
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem splitPairRead_splitPairWrite_of_ne {cfg : SplitPairCfg} {s_split idx idx' q v : ℕ}
    (hw : 0 < cfg.w) (hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi)
    (hA : cfg.baseLo + 2 ≤ cfg.baseHi) (mem : ℕ → ℕ) (hne : idx' ≠ idx) :
    splitPairRead cfg s_split (splitPairWrite cfg s_split mem idx q v) idx' =
      splitPairRead cfg s_split mem idx' := by
  unfold splitPairRead splitPairWrite
  by_cases h1 : idx' < s_split <;> by_cases h2 : idx < s_split
  · simp only [h1, h2, ↓reduceIte]
    exact Prod.ext (pairQuotAt_writePair_of_ne hw mem hne) (pairValAt_writePair_of_ne hw mem hne)
  · simp only [h1, h2, ↓reduceIte]
    have hlt := splitPair_word_lt hw hsum hA h1 (Nat.le_of_not_lt h2)
    have hleL := wOffQ_le_wOffV cfg.qBitsLo cfg.vBitsLo cfg.w idx'
    have hleH := wOffQ_le_wOffV cfg.qBitsHi cfg.vBitsHi cfg.w idx
    unfold pairQuotAt pairValAt readBitSlice
    dsimp only
    rw [writePair_ne_of_lt mem (by omega) hleH, writePair_ne_of_lt mem (by omega) hleH,
      writePair_ne_of_lt mem (by omega) hleH, writePair_ne_of_lt mem (by omega) hleH]
  · simp only [h1, h2, ↓reduceIte]
    have hlt := splitPair_word_lt hw hsum hA h2 (Nat.le_of_not_lt h1)
    have hleL := wOffQ_le_wOffV cfg.qBitsLo cfg.vBitsLo cfg.w idx
    have hleH := wOffQ_le_wOffV cfg.qBitsHi cfg.vBitsHi cfg.w idx'
    unfold pairQuotAt pairValAt readBitSlice
    dsimp only
    rw [writePair_ne_of_gt mem (by omega) hleL, writePair_ne_of_gt mem (by omega) hleL,
      writePair_ne_of_gt mem (by omega) hleL, writePair_ne_of_gt mem (by omega) hleL]
  · simp only [h1, h2, ↓reduceIte]
    exact Prod.ext (pairQuotAt_writePair_of_ne hw mem hne) (pairValAt_writePair_of_ne hw mem hne)

theorem splitPairWrite_outside {cfg : SplitPairCfg} {s_split n_tot idx q v addr : ℕ}
    (hw : 0 < cfg.w) (hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi)
    (hA : cfg.baseLo ≤ cfg.baseHi) (hidx : idx < n_tot) (mem : ℕ → ℕ)
    (haddr : ¬(cfg.baseLo ≤ addr ∧
      addr < cfg.baseHi + pairStreamWords n_tot cfg.qBitsHi cfg.vBitsHi cfg.w)) :
    splitPairWrite cfg s_split mem idx q v addr = mem addr := by
  unfold splitPairWrite
  split_ifs with hlt
  · refine writePair_outside hw hidx mem fun ⟨hlo, hhi⟩ => haddr ⟨hlo, ?_⟩
    have hpw : pairStreamWords n_tot cfg.qBitsLo cfg.vBitsLo cfg.w ≤
        pairStreamWords n_tot cfg.qBitsHi cfg.vBitsHi cfg.w := by
      unfold pairStreamWords packedWords
      have hm : n_tot * (cfg.qBitsLo + cfg.vBitsLo) ≤ n_tot * (cfg.qBitsHi + cfg.vBitsHi) :=
        Nat.mul_le_mul_left n_tot hsum
      have hd : (n_tot * (cfg.qBitsLo + cfg.vBitsLo) + cfg.w - 1) / cfg.w ≤
          (n_tot * (cfg.qBitsHi + cfg.vBitsHi) + cfg.w - 1) / cfg.w :=
        Nat.div_le_div_right (by omega)
      omega
    omega
  · exact writePair_outside hw hidx mem fun ⟨hlo, hhi⟩ => haddr ⟨hA.trans hlo, hhi⟩

/-- Tuple encoding of `SplitPairCfg` for `RealizesBounded` `Memory.Prog` primitives. -/
abbrev SplitPairCtx := ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ℕ

/-- Pack `SplitPairCfg` into `SplitPairCtx`. -/
@[expose] def SplitPairCfg.toCtx (cfg : SplitPairCfg) : SplitPairCtx :=
  (((cfg.baseLo, (cfg.qBitsLo, cfg.vBitsLo)), (cfg.baseHi, (cfg.qBitsHi, cfg.vBitsHi))), cfg.w)

/-- Unpack `SplitPairCtx` into `SplitPairCfg`. -/
@[expose] def SplitPairCfg.ofCtx : SplitPairCtx → SplitPairCfg
  | (((bL, (qL, vL)), (bH, (qH, vH))), wv) => ⟨bL, qL, vL, bH, qH, vH, wv⟩

@[simp] theorem SplitPairCfg.ofCtx_toCtx (cfg : SplitPairCfg) :
    SplitPairCfg.ofCtx cfg.toCtx = cfg := by
  cases cfg; rfl

/-- Frontier and bit-width validity predicate for `SplitPairCfg` over `n_tot` pair slots. -/
@[expose] def SplitPairCfg.Valid (cfg : SplitPairCfg) (w_mach n_tot frontier : ℕ) : Prop :=
  0 < w_mach ∧ w_mach = cfg.w ∧
  cfg.qBitsLo ≤ w_mach ∧ cfg.vBitsLo ≤ w_mach ∧
  cfg.qBitsHi ≤ w_mach ∧ cfg.vBitsHi ≤ w_mach ∧
  cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi ∧
  cfg.baseLo + 2 ≤ cfg.baseHi ∧
  n_tot < 2 ^ w_mach ∧
  cfg.baseHi + pairStreamWords n_tot cfg.qBitsHi cfg.vBitsHi cfg.w ≤ frontier

private theorem valid_lo_frontier {cfg : SplitPairCfg} {w n_tot frontier d : ℕ}
    (hv : cfg.Valid w n_tot frontier) (hd : d < n_tot) :
    cfg.baseLo + wOffV cfg.qBitsLo cfg.vBitsLo w d + 1 < frontier := by
  obtain ⟨hw, rfl, _, _, _, _, hsum, hA, _, hfr⟩ := hv
  have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := cfg.qBitsLo) (v_bits := cfg.vBitsLo) hw hd
  have hpw : pairStreamWords n_tot cfg.qBitsLo cfg.vBitsLo cfg.w ≤
      pairStreamWords n_tot cfg.qBitsHi cfg.vBitsHi cfg.w := by
    unfold pairStreamWords packedWords
    have hm := Nat.mul_le_mul_left n_tot hsum
    have hd' : (n_tot * (cfg.qBitsLo + cfg.vBitsLo) + cfg.w - 1) / cfg.w ≤
        (n_tot * (cfg.qBitsHi + cfg.vBitsHi) + cfg.w - 1) / cfg.w :=
      Nat.div_le_div_right (by omega)
    omega
  omega

private theorem valid_hi_frontier {cfg : SplitPairCfg} {w n_tot frontier d : ℕ}
    (hv : cfg.Valid w n_tot frontier) (hd : d < n_tot) :
    cfg.baseHi + wOffV cfg.qBitsHi cfg.vBitsHi w d + 1 < frontier := by
  obtain ⟨hw, rfl, _, _, _, _, _, _, _, hfr⟩ := hv
  have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := cfg.qBitsHi) (v_bits := cfg.vBitsHi) hw hd
  omega

/-- Read `(q, v)` from a split 2-slice pair stream in `Memory.Prog` (`4` memory reads,
`¬ReadsWidth`). -/
def splitPairReadProg : (SplitPairCtx × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((((bL, (qL, vL)), (bH, (qH, vH))), wv), s_split), idx) =>
    if idx < s_split then
      readPairGenProg (((bL, (qL, vL)), wv), idx)
    else
      readPairGenProg (((bH, (qH, vH)), wv), idx)

/-- Precondition for `splitPairReadProg`. -/
@[expose] def SplitPairReadPre (w : ℕ) : (SplitPairCtx × ℕ) × ℕ → Memory.State → Prop
  | ((ctx, _s_split), idx), s =>
    ∃ n_tot, idx < n_tot ∧ (SplitPairCfg.ofCtx ctx).Valid w n_tot s.frontier

theorem realizesBounded_splitPairRead :
    RealizesBounded .exact splitPairReadProg
      (WordEncoding.encode (α := (SplitPairCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitPairReadPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_split⟩, idx⟩
    obtain ⟨n_tot, hidx, hv⟩ := h
    have hv' := hv
    obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, _, _, _⟩ := hv
    subst hwv)
  · exact ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' hidx⟩
  · exact ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' hidx⟩

theorem splitPairReadProg_spec (cfg : SplitPairCfg) (s_split idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (splitPairReadProg ((cfg.toCtx, s_split), idx)) =
      splitPairRead cfg s_split s.mem idx ∧
    (Memory.spec 0).clientState s (splitPairReadProg ((cfg.toCtx, s_split), idx)) = s ∧
    memoryCost (splitPairReadProg ((cfg.toCtx, s_split), idx)) s = 4 := by
  unfold splitPairReadProg splitPairRead
  dsimp only [SplitPairCfg.toCtx]
  split_ifs <;>
    exact ⟨clientResult_readPairGenProg .., clientState_readPairGenProg ..,
      memoryCost_readPairGenProg ..⟩

/-- Write `(q, v)` into a split 2-slice pair stream in `Memory.Prog` (`8` memory ops,
`¬ReadsWidth`). -/
def splitPairWriteProg : ((SplitPairCtx × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((((bL, (qL, vL)), (bH, (qH, vH))), wv), s_split), idx), qv) =>
    if idx < s_split then
      writePairGenProg ((((bL, (qL, vL)), wv), idx), qv)
    else
      writePairGenProg ((((bH, (qH, vH)), wv), idx), qv)

/-- Precondition for `splitPairWriteProg`. -/
@[expose] def SplitPairWritePre (w : ℕ) :
    ((SplitPairCtx × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((ctx, _s_split), idx), _qv), s =>
    ∃ n_tot, idx < n_tot ∧ (SplitPairCfg.ofCtx ctx).Valid w n_tot s.frontier

theorem realizesBounded_splitPairWrite :
    RealizesBounded .exact splitPairWriteProg
      (WordEncoding.encode (α := ((SplitPairCtx × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      SplitPairWritePre (fun _ _ => 0) := by
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_split⟩, idx⟩, qv⟩
    obtain ⟨n_tot, hidx, hv⟩ := h
    have hv' := hv
    obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, _, _, _⟩ := hv
    subst hwv)
  · exact ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' hidx⟩
  · exact ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' hidx⟩

theorem splitPairWriteProg_spec (cfg : SplitPairCfg) (s_split idx q v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (splitPairWriteProg (((cfg.toCtx, s_split), idx), (q, v))) =
      { mem := splitPairWrite cfg s_split s.mem idx q v, frontier := s.frontier } ∧
    memoryCost (splitPairWriteProg (((cfg.toCtx, s_split), idx), (q, v))) s = 8 := by
  unfold splitPairWriteProg splitPairWrite
  dsimp only [SplitPairCfg.toCtx]
  split_ifs <;>
    exact ⟨clientState_writePairGenProg .., memoryCost_writePairGenProg ..⟩

/-- Single-step upward pair slide (`s_cur ↦ s_cur - 1`, `1 ≤ memoryCost` unconditionally). -/
def slideUpStepProg : SplitPairCtx × ℕ → Memory.Prog ℕ
  | ((((bL, (qL, vL)), (bH, (qH, vH))), wv), s_cur) =>
    if s_cur = 0 then do
      let _ ← Memory.read bL
      pure 0
    else do
      let idx ← pure (s_cur - 1)
      let qv ← readPairGenProg (((bL, (qL, vL)), wv), idx)
      writePairGenProg ((((bH, (qH, vH)), wv), idx), qv)
      pure idx

private theorem memoryCost_slideUpStepProg_pos (x : SplitPairCtx × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (slideUpStepProg x) s := by
  rcases x with ⟨⟨⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩, _⟩, s_cur⟩
  unfold slideUpStepProg; dsimp only
  split_ifs <;>
    simp only [pure_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
      prog_memoryCost_read, prog_runClient_state_read, memoryCost_readPairGenProg,
      runClient_state_readPairGenProg, memoryCost_writePairGenProg, memoryCost_pure] <;>
    omega

/-- Precondition for `slideUpStepProg`. -/
@[expose] def SlideUpStepPre (w : ℕ) : SplitPairCtx × ℕ → Memory.State → Prop
  | (ctx, s_cur), s =>
    ∃ n_tot, s_cur ≤ n_tot ∧ (SplitPairCfg.ofCtx ctx).Valid w n_tot s.frontier

private theorem realizesBounded_slideUpStep :
    RealizesBounded .exact slideUpStepProg
      (WordEncoding.encode (α := SplitPairCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      SlideUpStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_cur⟩
    obtain ⟨n_tot, hle, hv⟩ := h
    have hv' := hv
    obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, hA, hn_w, hfr⟩ := hv
    subst hwv
    try dsimp only [Fits] at *)
  all_goals try (unfold pairStreamWords packedWords at hfr; omega)
  all_goals try (refine ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' (by omega)⟩)
  all_goals (
    simp only [StateTransitionSpec.clientState, runClient_state_readPairGenProg]
    exact ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' (by omega)⟩)

/-- Batched Phase-1 upward pair slide parameterized explicitly by `fuel : ℕ` (`¬ReadsWidth`). -/
def slideUpBatchProg : (SplitPairCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, s_split), fuel) => iterate slideUpStepProg ctx fuel s_split

theorem realizesBounded_slideUpBatch :
    RealizesBounded .exact slideUpBatchProg
      (WordEncoding.encode (α := (SplitPairCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, s_split), fuel) s =>
        iterationSafe slideUpStepProg SlideUpStepPre w ctx fuel s_split s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := SplitPairCtx))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_slideUpStep
    memoryCost_slideUpStepProg_pos

theorem slideUpBatchProg_spec {cfg : SplitPairCfg} {n_tot s_split : ℕ} {s : Memory.State}
    (hv : cfg.Valid cfg.w n_tot s.frontier) (hq_le : cfg.qBitsLo ≤ cfg.qBitsHi)
    (hv_le : cfg.vBitsLo ≤ cfg.vBitsHi) (hs : s_split ≤ n_tot) (fuel : ℕ) :
    iterationSafe slideUpStepProg SlideUpStepPre cfg.w cfg.toCtx fuel s_split s ∧
    (Memory.spec 0).clientResult s (slideUpBatchProg ((cfg.toCtx, s_split), fuel)) =
      s_split - fuel ∧
    ((Memory.spec 0).clientState s (slideUpBatchProg ((cfg.toCtx, s_split), fuel))).frontier =
      s.frontier ∧
    memoryCost (slideUpBatchProg ((cfg.toCtx, s_split), fuel)) s ≤ 12 * fuel ∧
    (∀ idx,
      splitPairRead cfg (s_split - fuel)
        ((Memory.spec 0).clientState s (slideUpBatchProg ((cfg.toCtx, s_split), fuel))).mem idx =
      splitPairRead cfg s_split s.mem idx) ∧
    (∀ addr,
      ¬(cfg.baseHi ≤ addr ∧
        addr < cfg.baseHi + pairStreamWords n_tot cfg.qBitsHi cfg.vBitsHi cfg.w) →
      ((Memory.spec 0).clientState s (slideUpBatchProg ((cfg.toCtx, s_split), fuel))).mem addr =
        s.mem addr) := by
  unfold slideUpBatchProg
  dsimp only
  induction fuel generalizing s s_split with
  | zero =>
    exact ⟨trivial, (Nat.sub_zero s_split).symm, rfl, Nat.zero_le 0,
      fun idx => by rw [Nat.sub_zero]; rfl, fun _ _ => rfl⟩
  | succ k ih =>
    have hpre0 : SlideUpStepPre cfg.w (cfg.toCtx, s_split) s := by
      refine ⟨n_tot, hs, ?_⟩
      simpa only [SplitPairCfg.ofCtx_toCtx] using hv
    by_cases hs0 : s_split = 0
    · subst hs0
      have hst1 : (Memory.spec 0).clientState s (slideUpStepProg (cfg.toCtx, 0)) = s := by
        unfold slideUpStepProg StateTransitionSpec.clientState
        dsimp only [SplitPairCfg.toCtx]; simp
      have hres1 : (Memory.spec 0).clientResult s (slideUpStepProg (cfg.toCtx, 0)) = 0 := by
        unfold slideUpStepProg; dsimp only [SplitPairCfg.toCtx]; simp
      have hcost1 : memoryCost (slideUpStepProg (cfg.toCtx, 0)) s = 1 := by
        unfold slideUpStepProg; dsimp only [SplitPairCfg.toCtx]; simp
      obtain ⟨hsafe, hres, hfr_eq, hcost, hread, hout⟩ := ih hv (Nat.zero_le n_tot)
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres]; omega
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro idx; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1]
        simpa only [Nat.zero_sub] using hread idx
      · intro addr ha; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1]
        exact hout addr ha
    · have hs_pos : 0 < s_split := Nat.pos_of_ne_zero hs0
      set s₁ : Memory.State :=
        { mem := slideUpPair cfg s_split s.mem, frontier := s.frontier }
      have hst1 : (Memory.spec 0).clientState s (slideUpStepProg (cfg.toCtx, s_split)) = s₁ := by
        unfold slideUpStepProg StateTransitionSpec.clientState
        dsimp only [SplitPairCfg.toCtx, s₁, slideUpPair]
        simp [hs0]
      have hres1 : (Memory.spec 0).clientResult s (slideUpStepProg (cfg.toCtx, s_split)) =
          s_split - 1 := by
        unfold slideUpStepProg; dsimp only [SplitPairCfg.toCtx]; simp [hs0]
      have hcost1 : memoryCost (slideUpStepProg (cfg.toCtx, s_split)) s = 12 := by
        unfold slideUpStepProg; dsimp only [SplitPairCfg.toCtx]; simp [hs0]
      have hv1 : cfg.Valid cfg.w n_tot s₁.frontier := hv
      obtain ⟨hsafe, hres, hfr_eq, hcost, hread, hout⟩ :=
        ih (s := s₁) (s_split := s_split - 1) hv1 (by omega)
      have hsub : s_split - 1 - k = s_split - (k + 1) := by omega
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres, hsub]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro idx; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, ← hsub, hread idx]
        exact splitPair_slideUpPair hv.1 hq_le hv_le hv.2.2.2.2.2.2.2.1 hs_pos s.mem idx
      · intro addr ha; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hout addr ha]
        exact writePair_outside hv.1 (by omega : s_split - 1 < n_tot) s.mem ha

/-- Single-step downward pair slide (`s_cur ↦ min n_tot (s_cur + 1)`, `1 ≤ memoryCost`
unconditionally). -/
def slideDownStepProg : (SplitPairCtx × ℕ) × ℕ → Memory.Prog ℕ
  | (((((bL, (qL, vL)), (bH, (qH, vH))), wv), n_tot), s_cur) =>
    if s_cur < n_tot then do
      let qv ← readPairGenProg (((bH, (qH, vH)), wv), s_cur)
      writePairGenProg ((((bL, (qL, vL)), wv), s_cur), qv)
      pure (s_cur + 1)
    else do
      let _ ← Memory.read bL
      pure s_cur

private theorem memoryCost_slideDownStepProg_pos (x : (SplitPairCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (slideDownStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩, _⟩, _⟩, s_cur⟩
  unfold slideDownStepProg; dsimp only
  split_ifs <;>
    simp only [Realization.memoryCost_bind', StateTransitionSpec.clientState,
      prog_memoryCost_read, prog_runClient_state_read, memoryCost_readPairGenProg,
      runClient_state_readPairGenProg, memoryCost_writePairGenProg, memoryCost_pure] <;>
    omega

/-- Precondition for `slideDownStepProg`. -/
@[expose] def SlideDownStepPre (w : ℕ) : (SplitPairCtx × ℕ) × ℕ → Memory.State → Prop
  | ((ctx, n_tot), s_cur), s =>
    s_cur ≤ n_tot ∧ (SplitPairCfg.ofCtx ctx).Valid w n_tot s.frontier

private theorem realizesBounded_slideDownStep :
    RealizesBounded .exact slideDownStepProg
      (WordEncoding.encode (α := (SplitPairCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      SlideDownStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, n_tot⟩, s_cur⟩
    obtain ⟨hle, hv⟩ := h
    have hv' := hv
    obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, hA, hn_w, hfr⟩ := hv
    subst hwv
    try dsimp only [Fits] at *)
  all_goals try exact ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' ‹s_cur < n_tot›⟩
  all_goals try (
    simp only [StateTransitionSpec.clientState, runClient_state_readPairGenProg]
    exact ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' ‹s_cur < n_tot›⟩)
  all_goals (have hlt : s_cur < n_tot := ‹s_cur < n_tot›; omega)

/-- Batched Phase-3 downward pair slide parameterized explicitly by `fuel : ℕ` (`¬ReadsWidth`). -/
def slideDownBatchProg : ((SplitPairCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((ctx, n_tot), s_split), fuel) => iterate slideDownStepProg (ctx, n_tot) fuel s_split

theorem realizesBounded_slideDownBatch :
    RealizesBounded .exact slideDownBatchProg
      (WordEncoding.encode (α := ((SplitPairCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((ctx, n_tot), s_split), fuel) s =>
        iterationSafe slideDownStepProg SlideDownStepPre w (ctx, n_tot) fuel s_split s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := SplitPairCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_slideDownStep
    memoryCost_slideDownStepProg_pos

theorem slideDownBatchProg_spec {cfg : SplitPairCfg} {n_tot s_split : ℕ} {s : Memory.State}
    (hv : cfg.Valid cfg.w n_tot s.frontier) (hs : s_split ≤ n_tot) (fuel : ℕ)
    (hfit : ∀ d, s_split ≤ d → d < min n_tot (s_split + fuel) →
      (splitPairRead cfg s_split s.mem d).1 < 2 ^ cfg.qBitsLo ∧
      (splitPairRead cfg s_split s.mem d).2 < 2 ^ cfg.vBitsLo) :
    iterationSafe slideDownStepProg SlideDownStepPre cfg.w (cfg.toCtx, n_tot) fuel s_split s ∧
    (Memory.spec 0).clientResult s (slideDownBatchProg (((cfg.toCtx, n_tot), s_split), fuel)) =
      min n_tot (s_split + fuel) ∧
    ((Memory.spec 0).clientState s
      (slideDownBatchProg (((cfg.toCtx, n_tot), s_split), fuel))).frontier = s.frontier ∧
    memoryCost (slideDownBatchProg (((cfg.toCtx, n_tot), s_split), fuel)) s ≤ 12 * fuel ∧
    (∀ idx,
      splitPairRead cfg (min n_tot (s_split + fuel))
        ((Memory.spec 0).clientState s
          (slideDownBatchProg (((cfg.toCtx, n_tot), s_split), fuel))).mem idx =
      splitPairRead cfg s_split s.mem idx) ∧
    (∀ addr,
      ¬(cfg.baseLo ≤ addr ∧
        addr < cfg.baseLo + pairStreamWords n_tot cfg.qBitsLo cfg.vBitsLo cfg.w) →
      ((Memory.spec 0).clientState s
        (slideDownBatchProg (((cfg.toCtx, n_tot), s_split), fuel))).mem addr = s.mem addr) := by
  unfold slideDownBatchProg
  dsimp only
  induction fuel generalizing s s_split with
  | zero =>
    have hmin : min n_tot (s_split + 0) = s_split := by omega
    exact ⟨trivial, hmin.symm, rfl, Nat.zero_le 0,
      fun idx => by rw [hmin]; rfl, fun _ _ => rfl⟩
  | succ k ih =>
    have hpre0 : SlideDownStepPre cfg.w ((cfg.toCtx, n_tot), s_split) s := by
      refine ⟨hs, ?_⟩
      simpa only [SplitPairCfg.ofCtx_toCtx] using hv
    by_cases hlt : s_split < n_tot
    · set s₁ : Memory.State :=
        { mem := slideDownPair cfg s_split s.mem, frontier := s.frontier }
      have hst1 : (Memory.spec 0).clientState s
          (slideDownStepProg ((cfg.toCtx, n_tot), s_split)) = s₁ := by
        unfold slideDownStepProg StateTransitionSpec.clientState
        dsimp only [SplitPairCfg.toCtx, s₁, slideDownPair]
        simp [hlt]
      have hres1 : (Memory.spec 0).clientResult s
          (slideDownStepProg ((cfg.toCtx, n_tot), s_split)) = s_split + 1 := by
        unfold slideDownStepProg; dsimp only [SplitPairCfg.toCtx]; simp [hlt]
      have hcost1 : memoryCost (slideDownStepProg ((cfg.toCtx, n_tot), s_split)) s = 12 := by
        unfold slideDownStepProg; dsimp only [SplitPairCfg.toCtx]; simp [hlt]
      have hfit0 := hfit s_split le_rfl (by omega)
      have hsp0 : splitPairRead cfg s_split s.mem s_split =
          (pairQuotAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w s.mem s_split,
           pairValAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w s.mem s_split) := by
        simp [splitPairRead]
      rw [hsp0] at hfit0
      have hslide_eq : ∀ idx,
          splitPairRead cfg (s_split + 1) s₁.mem idx = splitPairRead cfg s_split s.mem idx :=
        splitPair_slideDownPair hv.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.1 s.mem hfit0.1 hfit0.2
      have hmin_eq : min n_tot (s_split + 1 + k) = min n_tot (s_split + (k + 1)) := by omega
      have hfit1 : ∀ d, s_split + 1 ≤ d → d < min n_tot (s_split + 1 + k) →
          (splitPairRead cfg (s_split + 1) s₁.mem d).1 < 2 ^ cfg.qBitsLo ∧
          (splitPairRead cfg (s_split + 1) s₁.mem d).2 < 2 ^ cfg.vBitsLo := fun d hd1 hd2 => by
        rw [hslide_eq d]
        exact hfit d (by omega) (by omega)
      obtain ⟨hsafe, hres, hfr_eq, hcost, hread, hout⟩ :=
        ih (s := s₁) (s_split := s_split + 1) hv (by omega) hfit1
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres, hmin_eq]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro idx; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, ← hmin_eq, hread idx, hslide_eq idx]
      · intro addr ha; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hout addr ha]
        exact writePair_outside hv.1 hlt s.mem ha
    · have heq : s_split = n_tot := by omega
      subst heq
      have hst1 : (Memory.spec 0).clientState s
          (slideDownStepProg ((cfg.toCtx, s_split), s_split)) = s := by
        unfold slideDownStepProg StateTransitionSpec.clientState; dsimp only [SplitPairCfg.toCtx]
        simp
      have hres1 : (Memory.spec 0).clientResult s
          (slideDownStepProg ((cfg.toCtx, s_split), s_split)) = s_split := by
        unfold slideDownStepProg; dsimp only [SplitPairCfg.toCtx]; simp
      have hcost1 : memoryCost (slideDownStepProg ((cfg.toCtx, s_split), s_split)) s = 1 := by
        unfold slideDownStepProg; dsimp only [SplitPairCfg.toCtx]; simp
      have hfit1 : ∀ d, s_split ≤ d → d < min s_split (s_split + k) →
          (splitPairRead cfg s_split s.mem d).1 < 2 ^ cfg.qBitsLo ∧
          (splitPairRead cfg s_split s.mem d).2 < 2 ^ cfg.vBitsLo := fun d hd1 hd2 => by omega
      obtain ⟨hsafe, hres, hfr_eq, hcost, hread, hout⟩ := ih hv le_rfl hfit1
      have hmin_eq : min s_split (s_split + (k + 1)) = min s_split (s_split + k) := by omega
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres, hmin_eq]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro idx; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hmin_eq]
        exact hread idx
      · intro addr ha; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1]
        exact hout addr ha

/-- Single-word zeroing step (`1 = memoryCost` unconditionally). -/
def zeroWordsStepProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, limit), cur) =>
    if cur < limit then do
      Memory.write (base + cur) 0
      pure (cur + 1)
    else do
      let _ ← Memory.read base
      pure cur

private theorem memoryCost_zeroWordsStepProg_pos (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (zeroWordsStepProg x) s := by
  rcases x with ⟨⟨_, _⟩, _⟩
  unfold zeroWordsStepProg; dsimp only
  split_ifs <;> simp

/-- Precondition for `zeroWordsStepProg`. -/
@[expose] def ZeroWordsStepPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((base, limit), cur), s =>
    0 < w ∧ cur ≤ limit ∧ base < s.frontier ∧ base + limit ≤ s.frontier

private theorem realizesBounded_zeroWordsStep :
    RealizesBounded .exact zeroWordsStepProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      ZeroWordsStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, limit⟩, cur⟩
    obtain ⟨hw, hle, hb_lt, hfr⟩ := h
    have hfr_w := hmem.1
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try dsimp only [Fits] at *
    omega)

/-- Batched Phase-1 metadata word zeroing parameterized explicitly by `fuel : ℕ` (`¬ReadsWidth`). -/
def zeroWordsBatchProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((base, limit), cur), fuel) => iterate zeroWordsStepProg (base, limit) fuel cur

theorem realizesBounded_zeroWordsBatch :
    RealizesBounded .exact zeroWordsBatchProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((base, limit), cur), fuel) s =>
        iterationSafe zeroWordsStepProg ZeroWordsStepPre w (base, limit) fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_zeroWordsStep
    memoryCost_zeroWordsStepProg_pos

theorem zeroWordsBatchProg_spec {w base limit cur : ℕ} {s : Memory.State}
    (hw : 0 < w) (hle : cur ≤ limit) (hb_lt : base < s.frontier)
    (hfr : base + limit ≤ s.frontier) (fuel : ℕ) :
    let s' := (Memory.spec 0).clientState s (zeroWordsBatchProg (((base, limit), cur), fuel))
    iterationSafe zeroWordsStepProg ZeroWordsStepPre w (base, limit) fuel cur s ∧
    (Memory.spec 0).clientResult s (zeroWordsBatchProg (((base, limit), cur), fuel)) =
      min limit (cur + fuel) ∧
    s'.frontier = s.frontier ∧
    memoryCost (zeroWordsBatchProg (((base, limit), cur), fuel)) s ≤ fuel ∧
    (∀ addr,
      s'.mem addr =
        if base + cur ≤ addr ∧ addr < base + min limit (cur + fuel) then 0 else s.mem addr) := by
  dsimp only
  unfold zeroWordsBatchProg
  dsimp only
  induction fuel generalizing s cur with
  | zero =>
    have hmin : min limit (cur + 0) = cur := by omega
    refine ⟨trivial, hmin.symm, rfl, le_rfl, fun addr => ?_⟩
    rw [hmin, ite_eq_right (by omega)]
    rfl
  | succ k ih =>
    have hpre0 : ZeroWordsStepPre w ((base, limit), cur) s := ⟨hw, hle, hb_lt, hfr⟩
    by_cases hlt : cur < limit
    · set s₁ : Memory.State :=
        { mem := Function.update s.mem (base + cur) 0, frontier := s.frontier }
      have hst1 : (Memory.spec 0).clientState s (zeroWordsStepProg ((base, limit), cur)) = s₁ := by
        unfold zeroWordsStepProg StateTransitionSpec.clientState; dsimp only
        rw [ite_eq_left hlt]; simp [s₁]
      have hres1 : (Memory.spec 0).clientResult s (zeroWordsStepProg ((base, limit), cur)) =
          cur + 1 := by
        unfold zeroWordsStepProg; dsimp only; rw [ite_eq_left hlt]; simp
      have hcost1 : memoryCost (zeroWordsStepProg ((base, limit), cur)) s = 1 := by
        unfold zeroWordsStepProg; dsimp only; rw [ite_eq_left hlt]; simp
      obtain ⟨hsafe, hres, hfr_eq, hcost, hmem⟩ :=
        ih (s := s₁) (cur := cur + 1) (by omega) hb_lt hfr
      have hmin_eq : min limit (cur + 1 + k) = min limit (cur + (k + 1)) := by omega
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres, hmin_eq]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro addr; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hmem addr, hmin_eq]
        dsimp only [s₁]
        by_cases h1 : base + (cur + 1) ≤ addr ∧ addr < base + min limit (cur + (k + 1))
        · rw [ite_eq_left h1, ite_eq_left ⟨by omega, h1.2⟩]
        · rw [ite_eq_right h1]
          by_cases h0 : addr = base + cur
          · subst h0
            rw [Function.update_self, ite_eq_left ⟨le_rfl, by omega⟩]
          · rw [Function.update_of_ne h0, ite_eq_right (by omega)]
    · have heq : cur = limit := by omega
      subst heq
      have hst1 : (Memory.spec 0).clientState s (zeroWordsStepProg ((base, cur), cur)) = s := by
        unfold zeroWordsStepProg StateTransitionSpec.clientState; dsimp only; simp
      have hres1 : (Memory.spec 0).clientResult s (zeroWordsStepProg ((base, cur), cur)) = cur := by
        unfold zeroWordsStepProg; dsimp only; simp
      have hcost1 : memoryCost (zeroWordsStepProg ((base, cur), cur)) s = 1 := by
        unfold zeroWordsStepProg; dsimp only; simp
      obtain ⟨hsafe, hres, hfr_eq, hcost, hmem⟩ := ih le_rfl hb_lt hfr
      have hmin_eq : min cur (cur + (k + 1)) = min cur (cur + k) := by omega
      refine ⟨⟨hpre0, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hsafe
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1, hres, hmin_eq]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1]; exact hfr_eq
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1, hcost1]; omega
      · intro addr; unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hmem addr, hmin_eq]

/-! ## Section 2: Compositional `BoundedFrameProg` Calculus -/

/-- Compositional certificate bundling `frontier` preservation, deterministic `memoryCost ≤ C`, and
frame preservation outside a word-address predicate `Mod : ℕ → Prop` (`0` projection chains). -/
structure BoundedFrameProg {α : Type} (Mod : ℕ → Prop) (C : ℕ) (p : Memory.Prog α) : Prop where
  /-- Execution preserves `s.frontier`. -/
  frontier_eq : ∀ s, ((Memory.spec 0).clientState s p).frontier = s.frontier
  /-- Deterministic memory charge is at most `C`. -/
  cost_le : ∀ s, memoryCost p s ≤ C
  /-- Every word address outside `Mod` is unchanged. -/
  mem_outside : ∀ s addr, ¬Mod addr → ((Memory.spec 0).clientState s p).mem addr = s.mem addr

namespace BoundedFrameProg

theorem pure_prog {α : Type} {Mod : ℕ → Prop} (x : α) :
    BoundedFrameProg Mod 0 (pure x : Memory.Prog α) :=
  ⟨fun _ => rfl, fun _ => by simp [memoryCost_pure], fun _ _ _ => rfl⟩

theorem read_prog (Mod : ℕ → Prop) (a : ℕ) :
    BoundedFrameProg Mod 1 (Memory.read a) :=
  ⟨fun _ => rfl, fun _ => le_rfl, fun _ _ _ => rfl⟩

theorem write_prog {Mod : ℕ → Prop} {a : ℕ} (ha : Mod a) (v : ℕ) :
    BoundedFrameProg Mod 1 (Memory.write a v) where
  frontier_eq _ := rfl
  cost_le _ := le_rfl
  mem_outside s addr hnot := by
    change Function.update s.mem a v addr = s.mem addr
    exact Function.update_of_ne (fun heq : addr = a => hnot (heq ▸ ha)) v s.mem

theorem mono {α : Type} {Mod₁ Mod₂ : ℕ → Prop} {C₁ C₂ : ℕ} {p : Memory.Prog α}
    (hp : BoundedFrameProg Mod₁ C₁ p) (hMod : ∀ a, Mod₁ a → Mod₂ a) (hC : C₁ ≤ C₂) :
    BoundedFrameProg Mod₂ C₂ p where
  frontier_eq := hp.frontier_eq
  cost_le s := (hp.cost_le s).trans hC
  mem_outside s addr hnot := hp.mem_outside s addr (fun h1 => hnot (hMod addr h1))

theorem bind_prog {α β : Type} {Mod : ℕ → Prop} {C₁ C₂ : ℕ} {p : Memory.Prog α}
    {q : α → Memory.Prog β} (hp : BoundedFrameProg Mod C₁ p)
    (hq : ∀ x, BoundedFrameProg Mod C₂ (q x)) :
    BoundedFrameProg Mod (C₁ + C₂) (p >>= q) where
  frontier_eq s := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hq _).frontier_eq _).trans (hp.frontier_eq s)
  cost_le s := by
    rw [Realization.memoryCost_bind']
    exact Nat.add_le_add (hp.cost_le s) ((hq _).cost_le _)
  mem_outside s addr hnot := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hq _).mem_outside _ addr hnot).trans (hp.mem_outside s addr hnot)

theorem ite_prog {α : Type} {Mod : ℕ → Prop} {C : ℕ} (P : Prop) [Decidable P]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : P → BoundedFrameProg Mod C p₁) (h₂ : ¬P → BoundedFrameProg Mod C p₂) :
    BoundedFrameProg Mod C (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

theorem readOnly_of_state_eq {α : Type} (Mod : ℕ → Prop) {C : ℕ} {p : Memory.Prog α}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s) (hcost : ∀ s, memoryCost p s ≤ C) :
    BoundedFrameProg Mod C p where
  frontier_eq s := by rw [hst]
  cost_le := hcost
  mem_outside s _ _ := by rw [hst]

theorem iterate_prog {δ σ : Type} {Mod : ℕ → Prop} {C : ℕ} {body : δ × σ → Memory.Prog σ}
    (d : δ) (hb : ∀ a, BoundedFrameProg Mod C (body (d, a))) (fuel : ℕ) (a₀ : σ) :
    BoundedFrameProg Mod (C * fuel) (iterate body d fuel a₀) := by
  induction fuel generalizing a₀ with
  | zero =>
    unfold iterate
    simpa only [Nat.mul_zero] using pure_prog (Mod := Mod) a₀
  | succ k ih =>
    unfold iterate
    have hstep := bind_prog (hb a₀) (fun a₁ => ih a₁)
    exact hstep.mono (fun _ h => h) (by rw [Nat.mul_succ]; omega)

theorem readPackedComp_prog (Mod : ℕ → Prop) (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) :
    BoundedFrameProg Mod 2 (readPackedCompGenProg x) := by
  rcases x with ⟨⟨⟨b, o⟩, ⟨k, w⟩⟩, i⟩
  exact readOnly_of_state_eq Mod (fun s => by
    simpa only [StateTransitionSpec.clientState] using
      runClient_state_readPackedCompGenProg (((b, o), (k, w)), i) s)
    (fun s => by simp)

theorem writePackedComp_prog {Mod : ℕ → Prop} {base off k w idx val nMax : ℕ}
    (hw : 0 < w) (hidx : idx < nMax)
    (hsub : ∀ addr, base + off ≤ addr → addr < base + off + packedWords nMax k w → Mod addr) :
    BoundedFrameProg Mod 4 (writePackedCompGenProg ((((base, off), (k, w)), idx), val)) where
  frontier_eq s := by
    simpa only [StateTransitionSpec.clientState] using
      congrArg Memory.State.frontier
        (runClient_state_writePackedCompGenProg base off k w idx val s)
  cost_le s := by simp
  mem_outside s addr hnot := by
    have hst : ((Memory.spec 0).clientState s
        (writePackedCompGenProg ((((base, off), (k, w)), idx), val))).mem =
        writePacked (base + off) k w s.mem idx val :=
      congrArg Memory.State.mem
        (clientState_writePackedCompGenProg base off k w idx val s)
    rw [hst]
    exact writePacked_outside hw s.mem hidx val (fun h => hnot (hsub addr h.1 h.2))

theorem readPairGen_prog (Mod : ℕ → Prop) (x : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) :
    BoundedFrameProg Mod 4 (readPairGenProg x) :=
  readOnly_of_state_eq Mod (clientState_readPairGenProg x) (fun s => by simp)

theorem writePairGen_prog {Mod : ℕ → Prop} {ib qB vB w d q v nCap : ℕ}
    (hw : 0 < w) (hd : d < nCap)
    (hsub : ∀ addr, ib ≤ addr → addr < ib + pairStreamWords nCap qB vB w → Mod addr) :
    BoundedFrameProg Mod 8 (writePairGenProg ((((ib, (qB, vB)), w), d), (q, v))) where
  frontier_eq s := by rw [clientState_writePairGenProg]
  cost_le s := by simp
  mem_outside s addr hnot := by
    rw [clientState_writePairGenProg]
    exact writePair_outside hw hd s.mem (fun h => hnot (hsub addr h.1 h.2))

theorem swapPairGen_prog {Mod : ℕ → Prop} {ib qB vB w p₁ p₂ nCap : ℕ}
    (hw : 0 < w) (hp₁ : p₁ < nCap) (hp₂ : p₂ < nCap)
    (hsub : ∀ addr, ib ≤ addr → addr < ib + pairStreamWords nCap qB vB w → Mod addr) :
    BoundedFrameProg Mod 24 (swapPairGenProg (((ib, (qB, vB)), w), (p₁, p₂))) := by
  unfold swapPairGenProg; dsimp only
  refine ite_prog (p₁ = p₂) (fun _ => (pure_prog ()).mono (fun _ h => h) (by omega)) fun _ => ?_
  refine (bind_prog (readPairGen_prog Mod _) fun qv₁ =>
    bind_prog (readPairGen_prog Mod _) fun qv₂ =>
    bind_prog (writePairGen_prog hw hp₁ hsub) fun _ =>
    writePairGen_prog hw hp₂ hsub).mono (fun _ h => h) (by omega)

end BoundedFrameProg

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
