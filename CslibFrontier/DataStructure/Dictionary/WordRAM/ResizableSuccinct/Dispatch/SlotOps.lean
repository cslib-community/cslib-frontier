/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
-- Unfolds `compQOffsetProg` and `packedOffsetProg` in `Accessors` for `validProg_compItemWordsGen`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Slot Resolvers and `GlobalMeta` Pool Updates in `Memory.Prog`

This module implements the compacted slot-resolution and `GlobalMeta` pool-update subroutines in
`Memory.Prog` (`¬ReadsWidth`, certified via `by realize` with `RealizesBounded .exact`), bridging
them via `FixedCoupled` to their fixed-capacity counterparts in `Succinct`:
* overflow-free item-stream word-count evaluation (`compItemWordsGenProg`) and quotient extraction
  (`compExtractQuotGenProg`);
* ghost fixed-capacity parameter/envelope certificates (`ghostDictParamsWf`, `ghostDictEnvGen`) and
  `FixedCoupled` dense-to-physical lookup and in-place value-update bridges;
* compacted slot and overflow-search resolvers (`compLastSlotOfGenProg`,
  `compResolveIndexedSlotGenProg`, `compResolveOvfStepGenProg`, `compInitOvfSearchGenProg`);
* compacted `GlobalMeta` pool updates (`compAppendTailGMGenProg`, `compRemoveTailGMOnlyGenProg`,
  `compGmPushSlabGenProg`, `compGmPopSlabGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compItemWordsGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compExtractQuotGenProg`:
  overflow-free item-stream word-count evaluation and Feistel key-quotient extraction.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompEpochEnv`:
  parameter and frontier envelope covering compacted metadata and `m_items` dense item slots.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compLastSlotOfGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveIndexedSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveOvfStepGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInitOvfSearchGenProg`:
  compacted read-only slot and overflow-search resolvers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompGmFrame`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg`:
  compacted `GlobalMeta` tail and slab pool updates.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compItemWordsGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compExtractQuotGen`:
  `RealizesBounded .exact` certificates for `compItemWordsGenProg` and `compExtractQuotGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.quot_val_at_slotOf`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.writeVal_slotOf`:
  dense-to-physical lookup agreement and in-place value-update coupling preservation.
* `realizesBounded_compResolveIndexedSlotGen`, `realizesBounded_compResolveOvfStepGen`,
  `realizesBounded_compInitOvfSearchGen`:
  `RealizesBounded .exact` certificates for compacted indexed and overflow slot resolution.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg_effect`:
  exact `GlobalMeta` state effects and `CompGmFrame` preservation, paired with
  `RealizesBounded .exact` certificates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Overflow-Free `compactedItemWords` and Quotient Extraction -/

/-- Exact overflow-free decomposition of `compactedItemWords U V w N m` in terms of `wOffQ` and
`bOffQ` for all `0 < w`. -/
theorem compactedItemWords_eq_wOffQ_add {U V w N m : ℕ} (hw : 0 < w) :
    compactedItemWords U V w N m =
      wOffQ (quotientBits U N) (valBits V) w m +
        (if bOffQ (quotientBits U N) (valBits V) w m = 0 then 2 else 3) := by
  unfold compactedItemWords
  have hid := wOffQ_mul_add_bOffQ (q_bits := quotientBits U N) (v_bits := valBits V) (w := w)
    (d := m)
  have hb_lt : bOffQ (quotientBits U N) (valBits V) w m < w := bOffQ_lt hw
  rw [← hid]
  set W := wOffQ (quotientBits U N) (valBits V) w m
  set B := bOffQ (quotientBits U N) (valBits V) w m
  split_ifs with hB0
  · have heq : W * w + B + w - 1 = (w - 1) + W * w := by omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]
  · have hB_pos : 0 < B := Nat.pos_of_ne_zero hB0
    have heq : W * w + B + w - 1 = (B - 1) + (W + 1) * w := by
      rw [Nat.add_one_mul]; omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : B - 1 < w), Nat.zero_add]

/-- Evaluate `compactedItemWords U V w N m` overflow-free in `Memory.Prog` (`¬ReadsWidth`). -/
def compItemWordsGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, m) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compQOffsetProg (((q_bits, v_bits), wVal), m)
    let z0 ← pure 0
    if wb.2 = z0 then
      pure (wb.1 + 2)
    else
      pure (wb.1 + 3)

@[simp] theorem clientResult_compItemWordsGenProg {U V w N m : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compItemWordsGenProg (mkCompParams U V w N, m)) =
      compactedItemWords U V w N m := by
  rw [compactedItemWords_eq_wOffQ_add hw]
  dsimp only [compItemWordsGenProg, cpQuotBits_mk, cpValBits_mk, cpW_mk]
  simp only [pure_bind, prog_clientResult_bind, clientResult_compQOffsetProg]
  split_ifs <;> rfl

theorem clientState_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compItemWordsGenProg d) = s := by
  rcases d with ⟨cp, m⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compItemWordsGenProg]; simp only [pure_bind, prog_runClient_state_bind,
    StateTransitionSpec.clientState, runClient_state_compQOffsetProg]
  split_ifs <;> rfl

@[simp] theorem runClient_state_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compItemWordsGenProg d))) = s :=
  clientState_compItemWordsGenProg d s

@[simp] theorem memoryCost_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compItemWordsGenProg d) s = 0 := by
  rcases d with ⟨cp, m⟩
  dsimp only [compItemWordsGenProg]; simp only [pure_bind, Realization.memoryCost_bind',
    memoryCost_compQOffsetProg, zero_add]
  split_ifs <;> rfl

/-- Precondition for `compItemWordsGenProg`, independent of `s.frontier`. -/
@[expose] def CompItemWordsPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, m), _s =>
    ∃ U V N,
      0 < w ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      Fits w (wOffQ (quotientBits U N) (valBits V) w m + 3)

theorem realizesBounded_compItemWordsGen :
    RealizesBounded .exact compItemWordsGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompItemWordsPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  realize
  all_goals (
    rcases d with ⟨cp, m⟩
    obtain ⟨U, V, N, hw, _hnU, hU, hV, rfl, hfit⟩ := h
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, clientResult_compQOffsetProg] at *)
  all_goals try exact ⟨hw, rfl, hq, hv, hfit.of_le (by omega)⟩
  all_goals exact hfit.of_le (by omega)

/-- Extract the Feistel key quotient `keyQuotient (bucketBits N) u = u >>> cpBucketBits cp`
in `Memory.Prog` (`¬ReadsWidth`). -/
def compExtractQuotGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, u) => pure (u >>> cpBucketBits cp)

@[simp] theorem clientResult_compExtractQuotGenProg (U V w N u : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compExtractQuotGenProg (mkCompParams U V w N, u)) =
      keyQuotient (bucketBits N) u := by
  simp [compExtractQuotGenProg, keyQuotient, Nat.shiftRight_eq_div_pow]

theorem clientState_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compExtractQuotGenProg d) = s := by
  rcases d with ⟨cp, u⟩; rfl

@[simp] theorem runClient_state_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compExtractQuotGenProg d))) = s :=
  clientState_compExtractQuotGenProg d s

@[simp] theorem memoryCost_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compExtractQuotGenProg d) s = 0 := by
  rcases d with ⟨cp, u⟩; rfl

/-- Precondition for `compExtractQuotGenProg`. -/
@[expose] def CompExtractQuotPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, u), _s => Fits w u ∧ Fits w (cpBucketBits cp)

theorem realizesBounded_compExtractQuotGen :
    RealizesBounded .exact compExtractQuotGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompExtractQuotPre (fun _ _ => 0) := by
  realize

/-! ## Section 2: Ghost `DictEnvGen` at `(base = 0, ghostW w)` and `FixedCoupled` Bridges -/

private theorem packedWords_le_len_add_two {len k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) :
    packedWords len k w ≤ len + 2 := by
  unfold packedWords
  have hle : len * k + w - 1 ≤ (w - 1) + len * w := by
    have := Nat.mul_le_mul_left len hkw; omega
  calc (len * k + w - 1) / w + 2
      ≤ ((w - 1) + len * w) / w + 2 := Nat.add_le_add_right (Nat.div_le_div_right hle) 2
    _ = (w - 1) / w + len + 2 := by rw [Nat.add_mul_div_right _ _ hw]
    _ = len + 2 := by rw [Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]

/-- At ghost word width `ghostW w = w + 16`, `DictParamsWf U V (ghostW w) N` holds for all
`N ≤ U < 2 ^ w` and `V ≤ 2 ^ w`. -/
theorem ghostDictParamsWf {U V w N : ℕ} (_hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hV : V ≤ 2 ^ w) :
    DictParamsWf U V (ghostW w) N := by
  have hpow : 2 ^ w ≤ 2 ^ ghostW w := Nat.pow_le_pow_right two_pos (by unfold ghostW; omega)
  exact ⟨by unfold ghostW; omega, hnU, lt_of_lt_of_le hU hpow, hV.trans hpow⟩

/-- At `base = 0` and `ghostW w = w + 16`, `DictEnvGen` holds unconditionally for any
`0 < w`, `N ≤ U < 2 ^ w`, and `V ≤ 2 ^ w` (`totalSpace < 2 ^ (w + 16)`). -/
theorem ghostDictEnvGen {U V w N : ℕ} (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hV : V ≤ 2 ^ w) :
    DictEnvGen (ghostW w) (mkDictParams U V (ghostW w) N (hashSpace U (ghostW w) N)) 0 := by
  have hwf := ghostDictParamsWf hw hnU hU hV
  refine ⟨⟨U, V, ghostW w, N, hashSpace U (ghostW w) N, hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2,
    rfl⟩, rfl, ?_⟩
  simp only [p_U_mk, p_V_mk, p_w_mk, p_nMax_mk, p_hSpace_mk, Nat.zero_add]
  set wg := ghostW w
  have hwg : 0 < wg := hwf.1
  have hh := hashSpace_le hwg hnU hwf.2.2.1.le
  have hq : packedWords N (quotientBits U N) wg ≤ N + 2 :=
    packedWords_le_len_add_two hwg (quotientBits_le_of_le_pow hwf.2.2.1.le)
  have hv : packedWords N (valBits V) wg ≤ N + 2 :=
    packedWords_le_len_add_two hwg (Nat.clog_le_of_le_pow hwf.2.2.2)
  have hlm_sub : lmSubWords N wg ≤ max N 1 + 2 :=
    (packedWords_le_len_add_two hwg (effBucketPosBits_le_of_lt_pow hnU hwf.2.2.1)).trans
      (Nat.add_le_add_right (totalMicroBuckets_le N) 2)
  have hgm_len : globalMetaLen N ≤ max N 1 + 7 := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · unfold globalMetaLen globalMetaVarLen; simp [hb0]
    · have := globalMetaLen_le_of_bucketBits_pos hb_pos; omega
  have hgm : packedWords (globalMetaLen N) (globalPtrBits N) wg ≤ max N 1 + 9 :=
    (packedWords_le_len_add_two hwg (globalPtrBits_le_of_lt_pow hnU hwf.2.2.1)).trans
      (by omega)
  have hob : packedWords (2 * N) 1 wg ≤ 2 * N + 2 :=
    packedWords_le_len_add_two hwg hwg
  have hmax_lt : max N 1 < 2 ^ w := max_n_one_lt_two_pow_w hw hnU hU
  have h2w_pos : 2 ≤ 2 ^ w := Nat.le_self_pow hw.ne' 2
  have hpow16 : 2 ^ ghostW w = 2 ^ w * 65536 := by
    unfold ghostW; rw [Nat.pow_add]
  change totalSpace U V wg N (hashSpace U wg N) < 2 ^ ghostW w
  rw [hpow16]
  unfold totalSpace offGM offLM offVal offQuot
  omega

/-- Extract `TailDenseInv` from `FixedCoupled`. -/
theorem FixedCoupled.tailDenseInv {metaBase itemBase U V w N : ℕ} {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s) (hb_pos : 0 < bucketBits N) :
    TailDenseInv N (compGmAt metaBase U w N s.mem 0) (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
  have hwin := hcpl.win_inv
  simp only [hb_pos.ne', ↓reduceIte] at hwin
  exact hwin

/-- Concrete epoch parameter and frontier envelope at `(metaBase, itemBase)` covering `m_items`
dense `(quotient, value)` slots. -/
structure CompEpochEnv (U V w N metaBase itemBase m_items : ℕ) (s : Memory.State) : Prop where
  pos_w : 0 < w
  pos_N : 0 < N
  le_U : N ≤ U
  lt_pow_U : U < 2 ^ w
  le_pow_V : V ≤ 2 ^ w
  meta_le_item : metaBase + offCompItems U w N ≤ itemBase
  item_le_frontier : itemBase + compactedItemWords U V w N m_items ≤ s.frontier

theorem CompEpochEnv.meta_le_frontier {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    metaBase + offCompItems U w N ≤ s.frontier :=
  henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier)

theorem CompEpochEnv.compMetaEnv {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    CompMetaEnv w (mkCompParams U V w N) metaBase s :=
  ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.meta_le_frontier⟩

theorem CompEpochEnv.compItemEnv {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    CompItemEnv w (mkCompParams U V w N) itemBase m_items s :=
  ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.item_le_frontier⟩

theorem CompEpochEnv.of_mem_eq {U V w N metaBase itemBase m_items : ℕ} {s s' : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) (hfr : s.frontier ≤ s'.frontier) :
    CompEpochEnv U V w N metaBase itemBase m_items s' :=
  ⟨henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, henv.meta_le_item,
    henv.item_le_frontier.trans hfr⟩

/-- Establish `DenseOfPhysPre` at `g = slotOf N gm b j` for any `b < numBuckets N` and
`j < bCount N gm b` under `FixedCoupled` and `CompEpochEnv`. -/
theorem FixedCoupled.denseOfPhysPre_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    DenseOfPhysPre w ((mkCompParams U V w N, metaBase),
      slotOf N (compGmAt metaBase U w N s.mem) b j) s := by
  set gm := compGmAt metaBase U w N s.mem
  set g := slotOf N gm b j
  have hg_lt : g < N := (slotOf_lt_and_injective hslot).1 b hb j hj
  refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier),
    hg_lt, fun hb_pos => ?_⟩
  have hSN := hslot.multi_total_le hb_pos
  have htd := hcpl.tailDenseInv hb_pos
  have htail := hslot.multi_tail hb_pos
  have hM_le : gm 1 ≤ maxTailItems N := htail.ntails_eq.trans_le htail.ntails_le
  refine ⟨le_trans (Nat.le_add_right _ _) hSN, fun hg_ge => ?_⟩
  have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
  unfold bCount at hj; simp only [hb_ne, ↓reduceIte, hb] at hj
  have hj_ge : ¬(j < gm (gmQIdx b) * slabSize N) := fun hj_slab => hg_ge <| by
    have hs_lt : j / slabSize N < gm (gmQIdx b) :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
      rw [(hslot.multi_slab hb_pos).nslabs_eq]
      exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt
    have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j (slabSize_pos N)
    change g < gm 0 * slabSize N
    unfold g slotOf; rw [ite_eq_right hb_ne, ite_eq_left hj_slab]
    have h1 := Nat.mul_le_mul_right (slabSize N) hp_lt
    rw [Nat.add_one_mul] at h1; omega
  have hr_lt : j - gm (gmQIdx b) * slabSize N < gm (gmRIdx b) := by omega
  have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < gm 1 := by
    rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ hr_lt
  have hg_eq : g = N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
    unfold g slotOf; rw [ite_eq_right hb_ne, ite_eq_right hj_ge]
  have ht_eq : N - 1 - g = gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by omega
  rw [ht_eq]
  exact ⟨lt_of_lt_of_le ht_lt hM_le, htd.td_lt _ ht_lt,
    le_trans (le_of_lt (htd.dense_lt _ ht_lt)) hSN⟩

/-- Lookup agreement at `d = denseOfPhys N gm td (slotOf N gm b j)` under `FixedCoupled`. -/
theorem FixedCoupled.quot_val_at_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let g := slotOf N gm b j
    let d := denseOfPhys N gm td g
    d < epochTotalSlots N gm ∧
    compQuotAt itemBase U V w N m_items s.mem d =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g ∧
    compValAt itemBase U V w N m_items s.mem d =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g := by
  intro gm td g d
  have htd := fun hb_pos => hcpl.tailDenseInv hb_pos
  obtain ⟨hd_lt, _, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb hj
  have hvirt := physOfDense_denseOfPhys_slotOf hslot htd hb hj
  have hq0 := hcpl.quot_eq d hd_lt
  have hv0 := hcpl.val_eq d hd_lt
  change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d =
    quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physOfDense N gm (compDTAt metaBase U w N s.mem) d) at hq0
  change compValAt itemBase U V w N (epochTotalSlots N gm) s.mem d =
    valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physOfDense N gm (compDTAt metaBase U w N s.mem) d) at hv0
  rw [hvirt] at hq0 hv0
  exact ⟨hd_lt,
    (compQuotAt_of_lt s.mem (lt_of_lt_of_le hd_lt hm) hd_lt).trans hq0,
    (compValAt_of_lt s.mem (lt_of_lt_of_le hd_lt hm) hd_lt).trans hv0⟩

/-- In-place value update at `slotOf N gm b j` preserves `FixedCoupled`. -/
theorem FixedCoupled.writeVal_slotOf {metaBase itemBase U V w N b j v : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hv_lt : v < 2 ^ valBits V) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let g := slotOf N gm b j
    let d := denseOfPhys N gm td g
    let s' : Memory.State :=
      { mem := writeCompVal itemBase U V w N s.mem d v, frontier := s.frontier }
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g), v))
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro gm td g d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hg_lt : g < N := (slotOf_lt_and_injective hslot).1 b hb j hj
  have htd := fun hb_pos => hcpl.tailDenseInv hb_pos
  obtain ⟨hd_lt, _, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb hj
  have hvirt := physOfDense_denseOfPhys_slotOf hslot htd hb hj
  obtain ⟨hlm_f, hgm_f, htd_f, hdt_f⟩ :=
    writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N) (v := v)
      hw hitem hd_lt s.mem
  obtain ⟨_, _, hq_fix, hv_fix, hl_fix, hg_fix⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hv_lt s_fix
  unfold FixedCoupled
  dsimp only [s', s_fix']
  refine ⟨hgm_f.trans (hg_fix.symm ▸ hcpl.gm_eq),
    hlm_f.trans (hl_fix.symm ▸ hcpl.lm_eq),
    by rw [hgm_f, htd_f, hdt_f]; exact hcpl.win_inv,
    fun i => by rw [htd_f]; exact hcpl.td_lt i,
    fun i => by rw [hdt_f]; exact hcpl.dt_lt i,
    fun d' hd' => ?_,
    fun d' hd' => ?_⟩
  · rw [hgm_f] at hd' ⊢
    rw [compQuotAt_writeCompVal hw s.mem, hdt_f, hq_fix]
    exact hcpl.quot_eq d' hd'
  · rw [hgm_f] at hd' ⊢
    rw [hdt_f, hv_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      rw [compValAt_writeCompVal_self s.mem hd_lt hv_lt]
      change v = Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) g v (physOfDense N gm (compDTAt metaBase U w N s.mem) d)
      rw [hvirt, Function.update_self]
    · rw [compValAt_writeCompVal_of_ne hw s.mem hdeq]
      have hg_ne : physByBase N (gm 0 * slabSize N) (compDTAt metaBase U w N s.mem) d' ≠ g := by
        intro heq
        apply hdeq
        obtain ⟨hb'_lt, hj'_lt, hd'_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd'
        have hv' := physOfDense_eq_slotOf_owner hslot htd hd'
        change physOfDense N gm (compDTAt metaBase U w N s.mem) d' = g at heq
        rw [hv'] at heq
        obtain ⟨rfl, rfl⟩ := (slotOf_lt_and_injective hslot).2 _ hb'_lt _ hj'_lt b hb j hj heq
        exact hd'_eq.symm
      rw [Function.update_of_ne hg_ne]
      exact hcpl.val_eq d' hd'

/-! ## Section 3: Compacted Read-Only Slot & Count Resolvers (`RealizesBounded .exact`) -/

/-- Every entry read via `compGmAt` fits in `globalPtrBits N` bits. -/
private theorem compGmAt_lt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    compGmAt metaBase U w N mem idx < 2 ^ globalPtrBits N := by
  unfold compGmAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Shared index and value bounds for reading a bucket's tail pointer at logical offset
`j ≥ gm (gmQIdx b) * slabSize N`. -/
private theorem tailPtr_read_bounds {U w N metaBase b j : ℕ} {s : Memory.State}
    (hN : 0 < N) (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hj_not_slab : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) :
    let gm := compGmAt metaBase U w N s.mem
    let ptr_idx := gmTailPtrBase N + (b * tailCapPerBucket N + (j - gm (gmQIdx b) * slabSize N))
    ptr_idx < globalMetaLen N ∧ gm ptr_idx ≤ N - 1 := by
  intro gm ptr_idx
  obtain ⟨hr_lt, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hj_not_slab
  have hptr_lt : ptr_idx < globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
  have ht_lt := (hslot.multi_tail hb_pos).ptr_lt b hb _ hr_lt
  have ht_lt' : gm ptr_idx < gm 1 := by
    simpa only [ptr_idx, gm, gmTailPtrIdx, gmTailPtrFlatIdx, Nat.add_assoc,
      ← (hslot.multi_tail hb_pos).ntails_eq] using ht_lt
  have hSN := hslot.multi_total_le hb_pos
  exact ⟨hptr_lt, by dsimp only [gm, ptr_idx] at *; omega⟩

/-- Resolve physical slot `slotOf N gm b (bCount N gm b - 1)` of the last item in bucket `b`. -/
def compLastSlotOfGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let z0 ← pure 0
    if cpBucketBits cp = z0 then do
      let c ← readCompGMGenProg ((cp, metaBase), z0)
      pure (c - 1)
    else do
      let b3 := b + b + b
      let r_idx ← pure (4 + b3 + 1)
      let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
      let t_idx ← pure (cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1)))
      let t_last ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t_last)

theorem clientState_compLastSlotOfGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compLastSlotOfGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; dsimp only [compLastSlotOfGenProg]
  simp only [pure_bind]; split_ifs <;> simp

@[simp] theorem runClient_state_compLastSlotOfGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compLastSlotOfGenProg d))) = s :=
  clientState_compLastSlotOfGenProg d s

theorem memoryCost_compLastSlotOfGenProg_le (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compLastSlotOfGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compLastSlotOfGenProg]; simp only [pure_bind]; split_ifs <;> simp

theorem clientResult_compLastSlotOfGenProg {U V w N metaBase b : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (compLastSlotOfGenProg ((mkCompParams U V w N, metaBase), b)) =
      slotOf N (compGmAt metaBase U w N s.mem) b
        (bCount N (compGmAt metaBase U w N s.mem) b - 1) := by
  set gm := compGmAt metaBase U w N s.mem
  dsimp only [compLastSlotOfGenProg, cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk,
    cpNSubOne_mk]
  simp only [pure_bind]
  by_cases hb0 : bucketBits N = 0
  · have hb_eq : b = 0 := by simp only [numBuckets, hb0, pow_zero] at hb; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    rw [ite_eq_left hb0, prog_clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, prog_clientResult_pure]
    unfold slotOf bCount; simp [hb0, hb_eq, gm]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hr_pos : 1 ≤ gm (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hr_cap : gm (gmRIdx b) - 1 < tailCapPerBucket N :=
      Nat.sub_lt_of_lt (hslot.multi_r_bounds hb_pos b hb).1
    have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + (gm (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [ite_eq_right hb0, hr_eq, prog_clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, prog_clientResult_bind,
      clientResult_readCompGMGenProg hptr_lt, clientState_readCompGMGenProg,
      prog_clientResult_pure]
    unfold slotOf bCount; simp only [hb0, ↓reduceIte, hb]
    have hnot : ¬(gm (gmQIdx b) * slabSize N + gm (gmRIdx b) - 1 < gm (gmQIdx b) * slabSize N) :=
      by omega
    have hsub : gm (gmQIdx b) * slabSize N + gm (gmRIdx b) - 1 - gm (gmQIdx b) * slabSize N =
        gm (gmRIdx b) - 1 := by omega
    rw [ite_eq_right hnot, hsub]; rfl

/-- Precondition for retrieving the last physical slot of bucket `b`. -/
@[expose] def CompLastSlotOfPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b

theorem realizesBounded_compLastSlotOfGen :
    RealizesBounded .exact compLastSlotOfGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompLastSlotOfPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hbc⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  · have hb_eq : b = 0 := by simp only [numBuckets, hc, pow_zero] at hb; omega
    unfold bCount at hbc; simp only [hc, ↓reduceIte, hb_eq] at hbc; exact hbc
  all_goals (
    have hb_pos : 0 < bucketBits N := by omega
    have hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) :=
      pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      Nat.sub_lt_of_lt (hslot.multi_r_bounds hb_pos b hb).1
    have hptr_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    have ht_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrBase N + (b * tailCapPerBucket N +
          (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
        compGmAt metaBase U w N s.mem 1 :=
      (hslot.multi_tail hb_pos).ptr_lt b hb _ (by omega)
    have hSN := hslot.multi_total_le hb_pos
    simp only [hr_eq, clientResult_readCompGMGenProg hr_idx_lt,
      clientResult_readCompGMGenProg hptr_lt] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]
    omega)
  all_goals try omega
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrBase gmRIdx at *
    omega)

private def compResolveMultiSlotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, metaBase), b), j) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let qK := q_b * cpSlabSize cp
    if j < qK then do
      let dir_idx := cpGmSlabDirBase cp + (b * cpDirSlabs cp + j / cpSlabSize cp)
      let p ← readCompGMGenProg ((cp, metaBase), dir_idx)
      pure (p * cpSlabSize cp + (cpSlabSizeSubOne cp - j % cpSlabSize cp))
    else do
      let t_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (j - qK))
      let t ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t)

/-- Resolve indexed local slot `j < effBucketCap N` of bucket `b` to `slotOf N gm b j`. -/
def compResolveIndexedSlotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, metaBase), b), j) =>
    if cpBucketBits cp = 0 then
      pure j
    else
      compResolveMultiSlotGenProg (((cp, metaBase), b), j)

theorem clientState_compResolveIndexedSlotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compResolveIndexedSlotGenProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg]
  by_cases hb0 : cpBucketBits cp = 0
  · rw [ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, prog_runClient_state_bind]
    simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg]
    split_ifs <;> simp

@[simp] theorem runClient_state_compResolveIndexedSlotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compResolveIndexedSlotGenProg d))) = s :=
  clientState_compResolveIndexedSlotGenProg d s

theorem memoryCost_compResolveIndexedSlotGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compResolveIndexedSlotGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  dsimp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg]
  by_cases hb0 : cpBucketBits cp = 0
  · rw [ite_eq_left hb0]; simp
  · rw [ite_eq_right hb0, Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      clientState_readCompGMGenProg]
    split_ifs <;> simp

theorem clientResult_compResolveIndexedSlotGenProg {U V w N metaBase b j : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hj_cap : j < effBucketCap N) :
    (Memory.spec 0).clientResult s
        (compResolveIndexedSlotGenProg (((mkCompParams U V w N, metaBase), b), j)) =
      slotOf N (compGmAt metaBase U w N s.mem) b j := by
  set gm := compGmAt metaBase U w N s.mem
  by_cases hb0 : bucketBits N = 0
  · simp only [compResolveIndexedSlotGenProg, cpBucketBits_mk, hb0, ↓reduceIte,
      prog_clientResult_pure]
    unfold slotOf; simp [hb0]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hK : 0 < slabSize N := slabSize_pos N
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    simp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg, cpBucketBits_mk,
      cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpSlabSizeSubOne_mk, cpGmTailPtrBase_mk,
      cpTailCap_mk, cpNSubOne_mk, hb0, ↓reduceIte, hq_eq]
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_idx_lt,
      clientState_readCompGMGenProg]
    by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
    · have hs_lt_q : j / slabSize N < gm (gmQIdx b) := (Nat.div_lt_iff_lt_mul hK).2 hj_slab
      have hs_lt_dir : j / slabSize N < dirSlabsPerBucket N := by
        rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hj_cap
        exact (Nat.div_lt_iff_lt_mul hK).2 hj_cap
      have hdir_lt : gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N) <
          globalMetaLen N := by
        have := gmSlabDirIdx_lt hb_pos hb hs_lt_dir
        unfold gmSlabDirIdx at this; omega
      have hdir_eq : compGmAt metaBase U w N s.mem
          (gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N)) =
          slabPtrOf N gm b (j / slabSize N) := by
        have := (hslot.multi_slab hb_pos).dir_eq b hb _ hs_lt_q hs_lt_dir
        simpa [gm, gmSlabDirIdx, Nat.add_assoc] using this
      simp only [gm] at hj_slab
      simp only [hj_slab, ↓reduceIte]
      rw [prog_clientResult_bind, clientResult_readCompGMGenProg hdir_lt,
        clientState_readCompGMGenProg, prog_clientResult_pure, hdir_eq]
      unfold slotOf; simp only [hb0, gm, hj_slab, ↓reduceIte]
    · have hN : 0 < N := Nat.pos_of_ne_zero (by intro h0; subst h0; exact hb0 rfl)
      obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_slab
      simp only [gm] at hj_slab hptr_lt
      simp only [hj_slab, ↓reduceIte]
      rw [prog_clientResult_bind, clientResult_readCompGMGenProg hptr_lt,
        clientState_readCompGMGenProg, prog_clientResult_pure]
      unfold slotOf; simp only [hb0, gm, hj_slab, ↓reduceIte]; rfl

private def CompResolveMultiSlotPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), j), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      j < effBucketCap N

private theorem realizesBounded_compResolveMultiSlotGen :
    RealizesBounded .exact compResolveMultiSlotGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompResolveMultiSlotPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hslot, hb, hj_bc, hj_cap⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hK : 0 < slabSize N := slabSize_pos N
    have hmod_lt := Nat.mod_lt j hK
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpSlabSizeSubOne_mk,
      cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk, hq_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try exact hK.ne'
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hq_idx_lt⟩
  all_goals try (
    have hs_lt_dir : j / slabSize N < dirSlabsPerBucket N := by
      rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hj_cap
      exact (Nat.div_lt_iff_lt_mul hK).2 hj_cap
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hs_lt_dir
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
  all_goals try (
    have hc_neg : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N) := by assumption
    obtain ⟨hptr_lt, ht_le⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hc_neg
    try rw [clientResult_readCompGMGenProg hptr_lt]
    try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact hptr_lt⟩
    try omega)
  all_goals try omega
  all_goals try exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by unfold gmQIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    have hs_lt_dir : j / slabSize N < dirSlabsPerBucket N := by
      rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hj_cap
      exact (Nat.div_lt_iff_lt_mul hK).2 hj_cap
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hs_lt_dir
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabDirIdx gmSlabDirBase at *; omega)
  have hc_pos : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by assumption
  have hs_lt_q : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
    (Nat.div_lt_iff_lt_mul hK).2 hc_pos
  have hs_lt_dir : j / slabSize N < dirSlabsPerBucket N := by
    rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hj_cap
    exact (Nat.div_lt_iff_lt_mul hK).2 hj_cap
  have hdir_lt : gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N) <
      globalMetaLen N := by
    have := gmSlabDirIdx_lt hb_pos hb hs_lt_dir; unfold gmSlabDirIdx at this; omega
  rw [clientResult_readCompGMGenProg hdir_lt]
  have hdir_eq : compGmAt metaBase U w N s.mem
      (gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N)) =
      slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N) := by
    have := (hslot.multi_slab hb_pos).dir_eq b hb _ hs_lt_q hs_lt_dir
    simpa [gmSlabDirIdx, Nat.add_assoc] using this
  rw [hdir_eq]
  have hp_lt : slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N) <
      compGmAt metaBase U w N s.mem 0 := by
    rw [(hslot.multi_slab hb_pos).nslabs_eq]
    exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt_q
  have h1 := Nat.mul_le_mul_right (slabSize N) hp_lt
  rw [Nat.add_one_mul] at h1
  have hSN := hslot.multi_total_le hb_pos
  exact lt_of_le_of_lt (by omega) hU

/-- Precondition for resolving indexed slot entries. -/
@[expose] def CompResolveIndexedSlotPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), j), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      j < effBucketCap N

theorem realizesBounded_compResolveIndexedSlotGen :
    RealizesBounded .exact compResolveIndexedSlotGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompResolveIndexedSlotPre (fun _ _ => 0) := by
  have hm := realizesBounded_compResolveMultiSlotGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
  simp only [cpBucketBits_mk] at *
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, Nat.pos_of_ne_zero hc, hslot, hb, hj_bc, hj_cap⟩

private def compResolveOvfAdvanceGenProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), (j1, qK)), (phys, p_cur)) =>
    if j1 < qK then do
      let p2 := p_cur + p_cur
      let abv_idx := cpGmSlabMetaBase cp + (p2 + p2) + 3
      let p_next ← readCompGMGenProg ((cp, metaBase), abv_idx)
      pure (phys, p_next)
    else
      pure (phys, p_cur)

private def compResolveOvfInSlabGenProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), qK), (j, p_cur)) =>
    let off := cpSlabSizeSubOne cp - j % cpSlabSize cp
    let phys := p_cur * cpSlabSize cp + off
    if off = 0 then
      compResolveOvfAdvanceGenProg ((((cp, metaBase), (j + 1, qK)), (phys, p_cur)))
    else
      pure (phys, p_cur)

/-- Single-step overflow slot resolver on compacted metadata (`¬ReadsWidth`). -/
def compResolveOvfStepGenProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), (j, p_cur)) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let qK := q_b * cpSlabSize cp
    if j < qK then
      compResolveOvfInSlabGenProg (((cp, metaBase), qK), (j, p_cur))
    else do
      let r := j - qK
      let t_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + r)
      let t ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t, p_cur)

theorem clientState_compResolveOvfStepGenProg
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compResolveOvfStepGenProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readCompGMGenProg]
  split_ifs <;> simp

@[simp] theorem runClient_state_compResolveOvfStepGenProg
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compResolveOvfStepGenProg d))) = s :=
  clientState_compResolveOvfStepGenProg d s

theorem memoryCost_compResolveOvfStepGenProg_pos
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (compResolveOvfStepGenProg d) s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  dsimp only [compResolveOvfStepGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  omega

theorem memoryCost_compResolveOvfStepGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compResolveOvfStepGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

/-- Under `compGmAt = gmAt`, `compResolveOvfStepGenProg` returns the exact same `(phys, p_next)`
pair as `Succinct.resolveOvfStepProg` on `s_fix`. -/
theorem clientResult_compResolveOvfStepGenProg_eq {U V w w₀ N h_space metaBase b j p_cur : ℕ}
    {s_fix s : Memory.State}
    (hgm_eq : compGmAt metaBase U w N s.mem = gmAt 0 U V w₀ N h_space s_fix.mem)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hp : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
      p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N)) :
    (Memory.spec 0).clientResult s
        (compResolveOvfStepGenProg (((mkCompParams U V w N, metaBase), b), (j, p_cur))) =
      (Memory.spec 0).clientResult s_fix
        (resolveOvfStepProg U V w₀ N h_space ((0, b), (j, p_cur))) := by
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq1 : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hq_eq2 : 4 + 3 * b = gmQIdx b := rfl
  simp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg,
    resolveOvfStepProg, cpSlabSize_mk, cpSlabSizeSubOne_mk, cpGmSlabMetaBase_mk, cpGmTailPtrBase_mk,
    cpTailCap_mk, cpNSubOne_mk, pure_bind, hq_eq1, hq_eq2]
  rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s_fix hq_lt, ← hgm_eq]
  by_cases hj_slab : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
  · simp only [hj_slab, ↓reduceIte]
    by_cases hoff : slabSize N - 1 - j % slabSize N = 0
    · simp only [hoff, ↓reduceIte]
      by_cases hj1_slab : j + 1 < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
      · have hp_eq := hp hj_slab
        have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
          (Nat.div_lt_iff_lt_mul (slabSize_pos N)).2 hj_slab
        have hp_lt_max : p_cur < maxFullSlabs N :=
          hp_eq ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
        have habv_lt : gmSlabMetaBase N + 4 * p_cur + 3 < globalMetaLen N :=
          gmSlabAboveIdx_lt hb_pos hp_lt_max
        have habv_eq : gmSlabMetaBase N + (p_cur + p_cur + (p_cur + p_cur)) + 3 =
            gmSlabMetaBase N + 4 * p_cur + 3 := by omega
        simp only [hj1_slab, ↓reduceIte, habv_eq]
        rw [prog_clientResult_bind, clientResult_readCompGMGenProg habv_lt,
          clientState_readCompGMGenProg, prog_clientResult_pure,
          StateTransitionSpec.clientResult_bind, clientState_readGMProg,
          clientResult_readGMProg s_fix habv_lt, ← hgm_eq]
        rfl
      · simp only [hj1_slab, ↓reduceIte]; rfl
    · simp only [hoff, ↓reduceIte]; rfl
  · simp only [hj_slab, ↓reduceIte]
    obtain ⟨-, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hj_slab
    have hptr_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg hptr_lt,
      clientState_readCompGMGenProg, prog_clientResult_pure,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s_fix hptr_lt, ← hgm_eq]
    rfl

private def CompResolveOvfAdvancePre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), (_j1, _qK)), (_phys, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_cur < maxFullSlabs N

private theorem realizesBounded_compResolveOvfAdvanceGen :
    RealizesBounded .exact compResolveOvfAdvanceGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfAdvancePre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨j1, qK⟩⟩, ⟨phys, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt_max⟩ := h
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_lt_max
    simp only [cpGmSlabMetaBase_mk] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmSlabAboveIdx gmSlabMetaBase at *
  omega

private def CompResolveOvfInSlabPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), qK), (j, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      qK ≤ N ∧
      j < qK ∧
      p_cur < maxFullSlabs N ∧
      (p_cur + 1) * slabSize N ≤ N

private theorem realizesBounded_compResolveOvfInSlabGen :
    RealizesBounded .exact compResolveOvfInSlabGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfInSlabPre (fun _ _ => 0) := by
  have hadv := realizesBounded_compResolveOvfAdvanceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, qK⟩, ⟨j, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hqK_le, hj_lt, hp_lt_max, hpK_le⟩ := h
    have hK : 0 < slabSize N := slabSize_pos N
    have hmod_lt := Nat.mod_lt j hK
    simp only [cpSlabSize_mk, cpSlabSizeSubOne_mk] at *)
  all_goals try exact hK.ne'
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt_max⟩
  all_goals try omega
  all_goals (rw [Nat.add_one_mul] at hpK_le; exact lt_of_le_of_lt (by omega) hU)

/-- Precondition for stepping overflow resolution. -/
@[expose] def CompResolveOvfStepPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (j, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      (j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
        p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N))

theorem realizesBounded_compResolveOvfStepGen :
    RealizesBounded .exact compResolveOvfStepGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfStepPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have hins := realizesBounded_compResolveOvfInSlabGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hj_bc, hslot, hp⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hK : 0 < slabSize N := slabSize_pos N
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk, hq_eq,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hq_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hq_lt⟩
  all_goals try (
    have hc_pos : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by assumption
    have hp_eq := hp hc_pos
    have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul hK).2 hc_pos
    have hp_lt_max : p_cur < maxFullSlabs N :=
      hp_eq ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
    have hp_lt : p_cur < compGmAt metaBase U w N s.mem 0 := by
      rw [hp_eq, (hslot.multi_slab hb_pos).nslabs_eq]
      exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt
    have hSN := hslot.multi_total_le hb_pos
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, by omega, hc_pos, hp_lt_max,
      (Nat.mul_le_mul_right (slabSize N) hp_lt).trans (by omega)⟩)
  all_goals try (
    have hc_neg : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N) := by assumption
    obtain ⟨hptr_lt, ht_le⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hc_neg
    try rw [clientResult_readCompGMGenProg hptr_lt]
    try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact hptr_lt⟩
    try omega)
  all_goals try exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by unfold gmQIdx at *; omega)
  all_goals exact lt_of_le_of_lt (by omega) hU

private def compInitOvfFromDirGenProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), (qK, fuel)) =>
    if cpMinCap cp < qK then do
      let dir_idx := cpGmSlabDirBase cp + b * cpDirSlabs cp + cpDirSlabsSubOne cp
      let p_prev ← readCompGMGenProg ((cp, metaBase), dir_idx)
      let p2 := p_prev + p_prev
      let abv_idx := cpGmSlabMetaBase cp + (p2 + p2) + 3
      let p_init ← readCompGMGenProg ((cp, metaBase), abv_idx)
      pure (p_init, fuel)
    else
      pure (0, fuel)

/-- Initialize `(p_init, fuel)` for Phase 2 overflow search on compacted metadata
(`¬ReadsWidth`). -/
def compInitOvfSearchGenProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let r_b ← readCompGMGenProg ((cp, metaBase), q_idx + 1)
    let qK := q_b * cpSlabSize cp
    let c := qK + r_b
    let cap := cpMinCap cp
    if cap < c then
      compInitOvfFromDirGenProg (((cp, metaBase), b), (qK, c - cap))
    else
      pure (0, 0)

theorem clientState_compInitOvfSearchGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compInitOvfSearchGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readCompGMGenProg]
  split_ifs <;> simp

@[simp] theorem runClient_state_compInitOvfSearchGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compInitOvfSearchGenProg d))) = s :=
  clientState_compInitOvfSearchGenProg d s

theorem memoryCost_compInitOvfSearchGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compInitOvfSearchGenProg d) s ≤ 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

/-- Under `compGmAt = gmAt`, `compInitOvfSearchGenProg` returns the exact same `(p_init, fuel)`
pair as `Succinct.initOvfSearchProg` on `s_fix`. -/
theorem clientResult_compInitOvfSearchGenProg_eq {U V w w₀ N h_space metaBase b : ℕ}
    {s_fix s : Memory.State}
    (hgm_eq : compGmAt metaBase U w N s.mem = gmAt 0 U V w₀ N h_space s_fix.mem)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem)) :
    (Memory.spec 0).clientResult s
        (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b)) =
      (Memory.spec 0).clientResult s_fix
        (initOvfSearchProg U V w₀ N h_space (0, b)) := by
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hq_eq1 : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hq_eq2 : 4 + 3 * b = gmQIdx b := rfl
  have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
  simp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg, initOvfSearchProg, cpSlabSize_mk,
    cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpDirSlabsSubOne_mk, cpGmSlabMetaBase_mk,
    pure_bind, hq_eq1, hq_eq2, hr_eq]
  rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_lt,
    clientState_readCompGMGenProg, prog_clientResult_bind, clientResult_readCompGMGenProg hr_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s_fix hq_lt, StateTransitionSpec.clientResult_bind,
    clientState_readGMProg, clientResult_readGMProg s_fix hr_lt, ← hgm_eq]
  by_cases hcap : min N (effBucketCap N) <
      compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N +
        compGmAt metaBase U w N s.mem (gmRIdx b)
  · simp only [hcap, ↓reduceIte]
    by_cases hqK : min N (effBucketCap N) <
        compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
    · simp only [hqK, ↓reduceIte]
      have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
        by_cases hN_le : N ≤ effBucketCap N
        · have hbc_le : compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N +
              compGmAt metaBase U w N s.mem (gmRIdx b) ≤ N := by
            have h := bCount_le_n_max hslot b
            unfold bCount at h; simp only [hb_pos.ne', ↓reduceIte, hb] at h; exact h
          rw [min_eq_left hN_le] at hcap; omega
        · rw [min_eq_right (by omega)] at hqK; omega
      obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
      let p_prev := compGmAt metaBase U w N s.mem
        (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1))
      have hp_prev_lt : p_prev < maxFullSlabs N := by
        dsimp only [p_prev]; rw [hdir_eq]; exact hp_prev_max
      have habv_lt : gmSlabMetaBase N + 4 * p_prev + 3 < globalMetaLen N :=
        gmSlabAboveIdx_lt hb_pos hp_prev_lt
      have habv_eq : gmSlabMetaBase N +
          (compGmAt metaBase U w N s.mem
              (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
            compGmAt metaBase U w N s.mem
              (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
            (compGmAt metaBase U w N s.mem
                (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
              compGmAt metaBase U w N s.mem
                (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)))) + 3 =
          gmSlabMetaBase N + 4 * p_prev + 3 := by dsimp only [p_prev]; omega
      have hp_eq : gmAt 0 U V w₀ N h_space s_fix.mem
          (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) = p_prev := by
        dsimp only [p_prev]; rw [← hgm_eq]
      rw [prog_clientResult_bind, clientResult_readCompGMGenProg hdir_lt,
        clientState_readCompGMGenProg, habv_eq,
        prog_clientResult_bind, clientResult_readCompGMGenProg habv_lt,
        clientState_readCompGMGenProg, prog_clientResult_pure,
        StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix hdir_lt,
        StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        hp_eq, clientResult_readGMProg s_fix habv_lt,
        StateTransitionSpec.clientResult_pure,
        ← hgm_eq]
    · simp only [hqK, ↓reduceIte]; rfl
  · simp only [hcap, ↓reduceIte]; rfl

private def CompInitOvfFromDirPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (qK, _fuel)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      effBucketCap N < N ∧
      qK = compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem)

private theorem realizesBounded_compInitOvfFromDirGen :
    RealizesBounded .exact compInitOvfFromDirGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompInitOvfFromDirPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨qK, fuel⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hcapN, rfl, hslot⟩ := h
    simp only [cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpDirSlabsSubOne_mk,
      cpGmSlabMetaBase_mk] at *)
  all_goals (
    have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
      rw [min_eq_right hcapN.le] at hc; omega
    obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_prev_max
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg hdir_lt,
      runClient_state_readCompGMGenProg] at *
    rw [hdir_eq] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabDirBase gmSlabAboveIdx gmSlabMetaBase at *
    omega)

/-- Precondition for initializing overflow search. -/
@[expose] def CompInitOvfSearchPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem)

theorem realizesBounded_compInitOvfSearchGen :
    RealizesBounded .exact compInitOvfSearchGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompInitOvfSearchPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have hdir := realizesBounded_compInitOvfFromDirGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslot⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpMinCap_mk, hq_eq, hr_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_lt, clientResult_readCompGMGenProg hr_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals try (
    have hcapN : effBucketCap N < N := by
      by_contra hnot; rw [min_eq_left (by omega)] at hc; omega
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hcapN, rfl, hslot⟩)
  all_goals try omega
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx gmRIdx at *
    omega)

/-! ## Section 4: `CompGmFrame` and Compacted `GlobalMeta` Pool Updates -/

/-- Frame relation for operations that write exclusively to the compacted `GlobalMeta` slice
`[metaBase + offCompGM U w N, metaBase + offTailToDense U w N)`. -/
structure CompGmFrame (metaBase itemBase U V w N m_items : ℕ)
    (s s' : Memory.State) : Prop where
  frontier_eq : s'.frontier = s.frontier
  outside_eq : ∀ a, ¬(metaBase + offCompGM U w N ≤ a ∧ a < metaBase + offTailToDense U w N) →
    s'.mem a = s.mem a
  lm_eq : compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem
  td_eq : compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem
  dt_eq : compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem
  quot_eq : compQuotAt itemBase U V w N m_items s'.mem =
    compQuotAt itemBase U V w N m_items s.mem
  val_eq : compValAt itemBase U V w N m_items s'.mem =
    compValAt itemBase U V w N m_items s.mem

private theorem CompGmFrame.refl {metaBase itemBase U V w N m_items : ℕ} (s : Memory.State) :
    CompGmFrame metaBase itemBase U V w N m_items s s :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem CompGmFrame.trans {metaBase itemBase U V w N m_items : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : CompGmFrame metaBase itemBase U V w N m_items s₁ s₂)
    (h₂ : CompGmFrame metaBase itemBase U V w N m_items s₂ s₃) :
    CompGmFrame metaBase itemBase U V w N m_items s₁ s₃ :=
  ⟨h₂.frontier_eq.trans h₁.frontier_eq,
    fun a ha => (h₂.outside_eq a ha).trans (h₁.outside_eq a ha),
    h₂.lm_eq.trans h₁.lm_eq, h₂.td_eq.trans h₁.td_eq, h₂.dt_eq.trans h₁.dt_eq,
    h₂.quot_eq.trans h₁.quot_eq, h₂.val_eq.trans h₁.val_eq⟩

theorem compGmFrame_writeCompGMGenProg {metaBase itemBase U V w N m_items idx val : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : idx < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = Function.update (compGmAt metaBase U w N s.mem) idx val := by
  intro s'
  have hs' := clientState_writeCompGMGenProg U V w N metaBase idx val s
  obtain ⟨hgm, hlm, htd, hdt, hq, hv, hout⟩ :=
    writeCompGM_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (m_items := m_items) hw hitem hidx hval s.mem
  dsimp only [s']; rw [hs']
  exact ⟨⟨rfl, hout, hlm, htd, hdt, hq, hv⟩, hgm⟩

private theorem compGmFrame_writeCompGM_ite {metaBase itemBase U V w N m_items idx val : ℕ}
    (P : Prop) [Decidable P] (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : P → idx < globalMetaLen N) (hval : P → val < 2 ^ globalPtrBits N) (s : Memory.State) :
    let prog : Memory.Prog Unit :=
      if P then writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val) else pure ()
    let s' := (Memory.spec 0).clientState s prog
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem =
      if P then Function.update (compGmAt metaBase U w N s.mem) idx val
      else compGmAt metaBase U w N s.mem := by
  split_ifs with hP
  · exact compGmFrame_writeCompGMGenProg hw hitem (hidx hP) (hval hP) s
  · exact ⟨CompGmFrame.refl s, rfl⟩

private def compAppendTailReadGMProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let t_new ← readCompGMGenProg ((cp, metaBase), 1)
    pure (r_b, t_new)

private def compAppendTailWrite1Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (r_b, t_new)) => do
    let off_b := b * cpTailCap cp + r_b
    let ptr_idx := cpGmTailPtrBase cp + off_b
    let own_idx := cpGmTailOwnerBase cp + t_new
    writeCompGMGenProg (((cp, metaBase), ptr_idx), t_new)
    writeCompGMGenProg (((cp, metaBase), own_idx), off_b)

private def compAppendTailWrite2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), (r_b, t_new)) => do
    let r_idx := 4 + (b + b + b) + 1
    writeCompGMGenProg (((cp, metaBase), r_idx), r_b + 1)
    writeCompGMGenProg (((cp, metaBase), 1), t_new + 1)
    pure t_new

private def compAppendTailWriteGMProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), info) => do
    compAppendTailWrite1Prog ((((cp, metaBase), b), info))
    compAppendTailWrite2Prog ((((cp, metaBase), b), info))

private def CompAppendTailWriteGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (r_b, t_new)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      r_b < tailCapPerBucket N ∧
      t_new < maxTailItems N

private theorem realizesBounded_compAppendTailWrite1 :
    RealizesBounded .exact compAppendTailWrite1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
    have hown_lt := gmTailOwnerIdx_lt hb_pos ht_cap
    simp only [cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailOwnerIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    have := tailCapPerBucket_le_globalMetaLen hb_pos
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase at *
    omega)

private theorem realizesBounded_compAppendTailWrite2 :
    RealizesBounded .exact compAppendTailWrite2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hmax_le : maxTailItems N ≤ N := maxTailItems_le N
    try simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    have := tailCapPerBucket_le_globalMetaLen hb_pos
    unfold gmRIdx at *; omega)

private theorem realizesBounded_compAppendTailWriteGM :
    RealizesBounded .exact compAppendTailWriteGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hw1 := realizesBounded_compAppendTailWrite1
  have hw2 := realizesBounded_compAppendTailWrite2
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hr_lt, ht_cap⟩
    dsimp only [compAppendTailWrite1Prog, StateTransitionSpec.clientState]
    simp [runClient_state_writeCompGMGenProg, hfr]

/-- Append one tail descriptor to bucket `b` in compacted `GlobalMeta` (`gmAppendTail`), returning
`t_new = gm 1` (`¬ReadsWidth`). -/
def compAppendTailGMGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let info ← compAppendTailReadGMProg ((cp, metaBase), b)
    compAppendTailWriteGMProg (((cp, metaBase), b), info)

@[simp] theorem memoryCost_compAppendTailGMGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compAppendTailGMGenProg d) s = 20 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compAppendTailGMGenProg, compAppendTailReadGMProg, compAppendTailWriteGMProg,
    compAppendTailWrite1Prog, compAppendTailWrite2Prog]

theorem compAppendTailGMGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N) :
    let s' := (Memory.spec 0).clientState s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b))
    (Memory.spec 0).clientResult s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b)) =
      compGmAt metaBase U w N s.mem 1 ∧
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmAppendTail N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  set gm := compGmAt metaBase U w N s.mem
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + gm (gmRIdx b)) < globalMetaLen N :=
    gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap : gm 1 < maxTailItems N := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_le : maxTailItems N ≤ N := maxTailItems_le N
  have hown_lt : gmTailOwnerBase N + gm 1 < globalMetaLen N := gmTailOwnerIdx_lt hb_pos ht_cap
  have ht_val : gm 1 < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_val : b * tailCapPerBucket N + gm (gmRIdx b) < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by unfold gmTailPtrBase at hptr_lt; omega)
  have hr1_val : gm (gmRIdx b) + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_lt; omega)
  have ht1_val : gm 1 + 1 < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hrd_st : (Memory.spec 0).clientState s
      (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState; simp [compAppendTailReadGMProg]
  have hrd_res : (Memory.spec 0).clientResult s
      (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = (gm (gmRIdx b), gm 1) := by
    dsimp only [compAppendTailReadGMProg, gm]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]
    rfl
  have hres : (Memory.spec 0).clientResult s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b)) = gm 1 := by
    dsimp only [compAppendTailGMGenProg]
    rw [StateTransitionSpec.clientResult_bind, hrd_st, hrd_res]
    dsimp only [compAppendTailWriteGMProg, compAppendTailWrite1Prog, compAppendTailWrite2Prog]
    repeat rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              gmTailPtrBase N + (b * tailCapPerBucket N + gm (gmRIdx b))), gm 1)))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmTailOwnerBase N + gm 1), b * tailCapPerBucket N + gm (gmRIdx b))))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmRIdx b), gm (gmRIdx b) + 1)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 1), gm 1 + 1)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compAppendTailGMGenProg]
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
    dsimp only [compAppendTailWriteGMProg]
    rw [StateTransitionSpec.clientState_bind]
    dsimp only [compAppendTailWrite1Prog, compAppendTailWrite2Prog,
      cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    rw [hr_eq]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [StateTransitionSpec.clientState_pure]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hptr_lt ht_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hown_lt hd_val _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hr_idx_lt
    hr1_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h1_lt ht1_val _
  rw [hst]
  refine ⟨hres, hf1.trans (hf2.trans (hf3.trans hf4)), ?_⟩
  rw [hg4, hg3, hg2, hg1]; rfl

/-- Precondition for appending to the tail of global metadata. -/
@[expose] def CompAppendTailGMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compAppendTailReadGM :
    RealizesBounded .exact compAppendTailReadGMProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [hr_eq, StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmRIdx at *; omega)

theorem realizesBounded_compAppendTailGMGen :
    RealizesBounded .exact compAppendTailGMGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compAppendTailReadGM
  have hwr := realizesBounded_compAppendTailWriteGM
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
      ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
    have hrd_st : (Memory.spec 0).clientState s
        (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState; simp [compAppendTailReadGMProg]
    have hrd_res : (Memory.spec 0).clientResult s
        (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem (gmRIdx b), compGmAt metaBase U w N s.mem 1) := by
      dsimp only [compAppendTailReadGMProg]
      rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]
      rfl
    rw [hrd_st, hrd_res]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩

private def compRemoveTailReadGMProg : (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let ptr_del_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1))
    let t_del ← readCompGMGenProg ((cp, metaBase), ptr_del_idx)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    let own_last_idx := cpGmTailOwnerBase cp + (n_tails - 1)
    let d_last ← readCompGMGenProg ((cp, metaBase), own_last_idx)
    pure ((r_b - 1, t_del), (n_tails - 1, d_last))

private def compRemoveTailWriteGMProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), b), ((r_del, t_del), (t_last, d_last))) => do
    let r_idx := 4 + (b + b + b) + 1
    let ptr_last_idx := cpGmTailPtrBase cp + d_last
    let own_del_idx := cpGmTailOwnerBase cp + t_del
    writeCompGMGenProg (((cp, metaBase), ptr_last_idx), t_del)
    writeCompGMGenProg (((cp, metaBase), own_del_idx), d_last)
    writeCompGMGenProg (((cp, metaBase), r_idx), r_del)
    writeCompGMGenProg (((cp, metaBase), 1), t_last)

/-- Remove the last tail descriptor of bucket `b` in compacted `GlobalMeta` (`gmRemoveTail`)
without touching item arrays (`¬ReadsWidth`). -/
def compRemoveTailGMOnlyGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let info ← compRemoveTailReadGMProg ((cp, metaBase), b)
    compRemoveTailWriteGMProg (((cp, metaBase), b), info)

@[simp] theorem memoryCost_compRemoveTailGMOnlyGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compRemoveTailGMOnlyGenProg d) s = 24 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compRemoveTailGMOnlyGenProg, compRemoveTailReadGMProg, compRemoveTailWriteGMProg]

theorem compRemoveTailGMOnlyGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    let s' := (Memory.spec 0).clientState s
      (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmRemoveTail N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  have hnt_le : compGmAt metaBase U w N s.mem 1 ≤ N := htail.ntails_le.trans (maxTailItems_le N)
  let r_del := compGmAt metaBase U w N s.mem (gmRIdx b) - 1
  let t_del := compGmAt metaBase U w N s.mem (gmTailPtrIdx N b r_del)
  let t_last := compGmAt metaBase U w N s.mem 1 - 1
  let d_last := compGmAt metaBase U w N s.mem (gmTailOwnerIdx N t_last)
  have hr_del_lt : r_del < compGmAt metaBase U w N s.mem (gmRIdx b) := by
    dsimp only [r_del]; omega
  have hr_del_cap : r_del < tailCapPerBucket N := lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb r_del hr_del_lt
  have ht_last_lt : t_last < compGmAt metaBase U w N s.mem 1 := by
    dsimp only [t_last]; omega
  have hd_last_lt : d_last < maxTailItems N := htail.owner_lt_maxTailItems ht_last_lt
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hptr_del_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hown_last_lt : gmTailOwnerBase N + (compGmAt metaBase U w N s.mem 1 - 1) <
      globalMetaLen N := gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_last_lt htail.ntails_le)
  have hptr_last_lt : gmTailPtrBase N + d_last < globalMetaLen N :=
    gmTailPtrFlatIdx_lt hb_pos hd_last_lt
  have hown_del_lt : gmTailOwnerBase N + t_del < globalMetaLen N :=
    gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_del_lt htail.ntails_le)
  have ht_del_val : t_del < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [t_del] at *; omega)
  have hd_last_val : d_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase at hptr_last_lt; omega)
  have hr_del_val : r_del < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_del_lt; dsimp only [r_del]; omega)
  have ht_last_val : t_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [t_last]; omega)
  have hread_st : (Memory.spec 0).clientState s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState
    simp [compRemoveTailReadGMProg]
  have hread_res : (Memory.spec 0).clientResult s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      ((r_del, t_del), (t_last, d_last)) := by
    dsimp only [compRemoveTailReadGMProg, cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hptr_del_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h1_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hown_last_lt, clientState_readCompGMGenProg]
    rfl
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              gmTailPtrBase N + d_last), t_del)))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmTailOwnerBase N + t_del), d_last)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmRIdx b), r_del)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 1), t_last)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compRemoveTailGMOnlyGenProg]
    rw [StateTransitionSpec.clientState_bind, hread_st, hread_res]
    dsimp only [compRemoveTailWriteGMProg, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    rw [hr_eq]
    repeat rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hptr_last_lt
    ht_del_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hown_del_lt
    hd_last_val _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hr_idx_lt
    hr_del_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h1_lt
    ht_last_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans hf4)), ?_⟩
  rw [hg4, hg3, hg2, hg1]; rfl

/-- Precondition for removing only the tail descriptor in global metadata. -/
@[expose] def CompRemoveTailGMOnlyPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)

private theorem realizesBounded_compRemoveTailReadGM :
    RealizesBounded .exact compRemoveTailReadGMProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hptr_del_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have ht_last_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by
      omega
    have hown_last_lt : gmTailOwnerBase N + (compGmAt metaBase U w N s.mem 1 - 1) <
        globalMetaLen N := gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_last_lt htail.ntails_le)
    simp only [cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk, hr_eq,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg hr_idx_lt] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at *
    omega)
  all_goals try omega
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrBase at *
    unfold gmTailOwnerBase at *
    unfold gmRIdx at *
    omega)

private def CompRemoveTailWriteGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), b), ((_r_del, t_del), (_t_last, d_last))), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      t_del < maxTailItems N ∧
      d_last < maxTailItems N

private theorem realizesBounded_compRemoveTailWriteGM :
    RealizesBounded .exact compRemoveTailWriteGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompRemoveTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨⟨r_del, t_del⟩, ⟨t_last, d_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, ht_del_lt, hd_last_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_last_lt := gmTailPtrFlatIdx_lt hb_pos hd_last_lt
    have hown_del_lt := gmTailOwnerIdx_lt hb_pos ht_del_lt
    try simp only [cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrFlatIdx gmTailOwnerIdx gmRIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase gmRIdx at *
    omega)

theorem realizesBounded_compRemoveTailGMOnlyGen :
    RealizesBounded .exact compRemoveTailGMOnlyGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compRemoveTailReadGM
  have hwr := realizesBounded_compRemoveTailWriteGM
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hptr_del_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have ht_last_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by
      omega
    have hown_last_lt : gmTailOwnerBase N + (compGmAt metaBase U w N s.mem 1 - 1) <
        globalMetaLen N := gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_last_lt htail.ntails_le)
    have hread_st : (Memory.spec 0).clientState s
        (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGMProg]
    have hread_res : (Memory.spec 0).clientResult s
        (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
        ((compGmAt metaBase U w N s.mem (gmRIdx b) - 1,
          compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))),
         (compGmAt metaBase U w N s.mem 1 - 1,
          compGmAt metaBase U w N s.mem
            (gmTailOwnerIdx N (compGmAt metaBase U w N s.mem 1 - 1)))) := by
      dsimp only [compRemoveTailReadGMProg, cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
      rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg hptr_del_lt, clientState_readCompGMGenProg,
        StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h1_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg hown_last_lt, clientState_readCompGMGenProg]
      rfl
    rw [hread_st, hread_res]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb,
      lt_of_lt_of_le (htail.ptr_lt b hb _ hr_del_lt) htail.ntails_le,
      htail.owner_lt_maxTailItems ht_last_lt⟩

private def compGmPushReadProg :
    (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((cp, metaBase), b) => do
    let q_idx := 4 + (b + b + b)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    let top_old ← readCompGMGenProg ((cp, metaBase), q_idx + 2)
    pure ((q_b, p_new), top_old)

private def compGmPushWriteOwnerProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)) => do
    let p2 := p_new + p_new
    let ownB_idx := cpGmSlabMetaBase cp + (p2 + p2)
    writeCompGMGenProg (((cp, metaBase), ownB_idx), b)
    writeCompGMGenProg (((cp, metaBase), ownB_idx + 1), q_b)
    writeCompGMGenProg (((cp, metaBase), ownB_idx + 2), top_old)

private def compGmPushWriteLinksProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)) =>
    (if 0 < q_b then
      let t2 := top_old + top_old
      let abv_idx := cpGmSlabMetaBase cp + (t2 + t2) + 3
      writeCompGMGenProg (((cp, metaBase), abv_idx), p_new)
    else
      pure ()) >>= fun _ =>
      if q_b < cpDirSlabs cp then
        let dir_idx := cpGmSlabDirBase cp + b * cpDirSlabs cp + q_b
        writeCompGMGenProg (((cp, metaBase), dir_idx), p_new)
      else
        pure ()

private def compGmPushFinishProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), p_new) => do
    let q_idx := 4 + (b + b + b)
    let top_idx := q_idx + 2
    writeCompGMGenProg (((cp, metaBase), top_idx), p_new)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b + 1)
    writeCompGMGenProg (((cp, metaBase), 0), p_new + 1)

private def compGmPushApplyProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), ((q_b, p_new), top_old)) => do
    compGmPushWriteOwnerProg ((((cp, metaBase), (b, q_b)), (p_new, top_old)))
    compGmPushWriteLinksProg ((((cp, metaBase), (b, q_b)), (p_new, top_old)))
    compGmPushFinishProg ((((cp, metaBase), (b, q_b)), p_new))

/-- Push a new full slab `p_new = gm 0` onto bucket `b` in compacted `GlobalMeta` (`gmPushSlab`,
`¬ReadsWidth`). -/
def compGmPushSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let info ← compGmPushReadProg ((cp, metaBase), b)
    compGmPushApplyProg (((cp, metaBase), b), info)

theorem memoryCost_compGmPushSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPushSlabGenProg d) s ≤ 38 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPushSlabGenProg, compGmPushReadProg, compGmPushApplyProg,
    compGmPushWriteOwnerProg, compGmPushWriteLinksProg, compGmPushFinishProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg, memoryCost_pure]
  split_ifs <;> simp

/-- Precondition for pushing a slab in global metadata. -/
@[expose] def CompGmPushSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) ∧
      compGmAt metaBase U w N s.mem 0 < maxFullSlabs N

theorem compGmPushSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hp_lt : compGmAt metaBase U w N s.mem 0 < maxFullSlabs N) :
    let s' := (Memory.spec 0).clientState s
      (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmPushSlab N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  let gm := compGmAt metaBase U w N s.mem
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have hownB_lt : gmSlabOwnerBIdx N (gm 0) < globalMetaLen N := gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : gmSlabOwnerSIdx N (gm 0) < globalMetaLen N := gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hbel_lt : gmSlabBelowIdx N (gm 0) < globalMetaLen N := gmSlabBelowIdx_lt hb_pos hp_lt
  have habv_lt : 0 < gm (gmQIdx b) → gmSlabAboveIdx N (gm (gmSlabTopIdx b)) < globalMetaLen N :=
    fun hq_pos => gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)
  have hdir_lt : gm (gmQIdx b) < dirSlabsPerBucket N →
      gmSlabDirIdx N b (gm (gmQIdx b)) < globalMetaLen N :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb hdir
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hq_le_p : gm (gmQIdx b) ≤ gm 0 := q_le_nslabs_of_slabBijection hslab hb
  have hb_val : b < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by unfold gmQIdx at hq_idx_lt; omega)
  have hq_val : gm (gmQIdx b) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hp_val : gm 0 < 2 ^ globalPtrBits N := compGmAt_lt ..
  have htop_val : gm (gmSlabTopIdx b) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hq1_val : gm (gmQIdx b) + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm] at *; omega)
  have hp1_val : gm 0 + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm] at *; omega)
  have hp4 : gmSlabMetaBase N + (gm 0 + gm 0 + (gm 0 + gm 0)) =
      gmSlabOwnerBIdx N (gm 0) := by unfold gmSlabOwnerBIdx; omega
  have ht4 : gmSlabMetaBase N +
      (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b) +
        (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b))) + 3 =
      gmSlabAboveIdx N (gm (gmSlabTopIdx b)) := by unfold gmSlabAboveIdx; omega
  have hrd_st : (Memory.spec 0).clientState s
      (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState; simp [compGmPushReadProg]
  have hrd_res : (Memory.spec 0).clientResult s
      (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) =
      ((gm (gmQIdx b), gm 0), gm (gmSlabTopIdx b)) := by
    dsimp only [compGmPushReadProg, gm]
    rw [hq_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hq_idx_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg,
      htop_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg htop_idx_lt,
      clientState_readCompGMGenProg]
    rfl
  let s_own := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabOwnerBIdx N (gm 0)), b)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabOwnerSIdx N (gm 0)), gm (gmQIdx b))))
    (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
      gmSlabBelowIdx N (gm 0)), gm (gmSlabTopIdx b)))
  have hown_st : (Memory.spec 0).clientState s
      (compGmPushWriteOwnerProg ((((mkCompParams U V w N, metaBase), (b, gm (gmQIdx b))),
        (gm 0, gm (gmSlabTopIdx b))))) = s_own := by
    dsimp only [compGmPushWriteOwnerProg, cpGmSlabMetaBase_mk, gmSlabOwnerSIdx, gmSlabBelowIdx,
      s_own, gm]
    dsimp only [gm] at hp4
    rw [hp4]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  let s_lnk := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_own
      (if 0 < gm (gmQIdx b) then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N (gm (gmSlabTopIdx b))), gm 0)
      else pure ()))
    (if gm (gmQIdx b) < dirSlabsPerBucket N then
      writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabDirIdx N b (gm (gmQIdx b))), gm 0)
    else pure ())
  have hlnk_st : (Memory.spec 0).clientState s_own
      (compGmPushWriteLinksProg ((((mkCompParams U V w N, metaBase), (b, gm (gmQIdx b))),
        (gm 0, gm (gmSlabTopIdx b))))) = s_lnk := by
    dsimp only [compGmPushWriteLinksProg, cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk,
      gmSlabDirIdx, s_lnk, gm]
    dsimp only [gm] at ht4
    rw [ht4, StateTransitionSpec.clientState_bind]
    rfl
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s_lnk
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b), gm 0)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmQIdx b), gm (gmQIdx b) + 1)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm 0 + 1)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmPushSlabGenProg]
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
    dsimp only [compGmPushApplyProg]
    rw [StateTransitionSpec.clientState_bind, hown_st,
      StateTransitionSpec.clientState_bind, hlnk_st]
    dsimp only [compGmPushFinishProg, gm]
    rw [hq_eq, htop_eq]
    repeat rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_lt
    hb_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_lt
    hq_val _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_lt
    htop_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGM_ite (m_items := m_items) (0 < gm (gmQIdx b))
    hw hitem habv_lt (fun _ => hp_val) _
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (gm (gmQIdx b) < dirSlabsPerBucket N) hw hitem hdir_lt (fun _ => hp_val) _
  obtain ⟨hf6, hg6⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem htop_idx_lt
    hp_val _
  obtain ⟨hf7, hg7⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hq_idx_lt
    hq1_val _
  obtain ⟨hf8, hg8⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
    hp1_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans (hf6.trans (hf7.trans hf8)))))),
    ?_⟩
  rw [hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]; rfl

private def CompGmPushMetaPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      q_b ≤ p_new ∧
      p_new < maxFullSlabs N ∧
      (0 < q_b → top_old < maxFullSlabs N)

private theorem realizesBounded_compGmPushWriteOwner :
    RealizesBounded .exact compGmPushWriteOwnerProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, hp_lt, _⟩ := h
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_lt
    have hownS_lt : gmSlabOwnerBIdx N p_new + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_lt
    have hbel_lt : gmSlabOwnerBIdx N p_new + 2 < globalMetaLen N :=
      gmSlabBelowIdx_lt hb_pos hp_lt
    have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) =
        gmSlabOwnerBIdx N p_new := by unfold gmSlabOwnerBIdx; omega
    simp only [cpGmSlabMetaBase_mk, hp4,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

private theorem realizesBounded_compGmPushWriteLinks :
    RealizesBounded .exact compGmPushWriteLinksProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, hp_lt, htop_lt⟩ := h
    simp only [cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk,
      StateTransitionSpec.clientState] at *)
  all_goals try (
    have hc_pos : 0 < q_b := by assumption
    have habv_lt := gmSlabAboveIdx_lt hb_pos (htop_lt hc_pos)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
       simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabAboveIdx gmSlabMetaBase at *; omega))
  all_goals (
    have hc_dir : q_b < dirSlabsPerBucket N := by assumption
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hc_dir
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
       · by_cases hc0 : 0 < q_b
         · simp [hc0, runClient_state_writeCompGMGenProg, hfr]
         · simp [hc0, hfr]
       · simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabDirIdx gmSlabDirBase at *; omega))

private def CompGmPushFinishPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, q_b)), p_new), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      q_b ≤ p_new ∧
      p_new < maxFullSlabs N

private theorem realizesBounded_compGmPushFinish :
    RealizesBounded .exact compGmPushFinishProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushFinishPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, p_new⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
    simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabTopIdx gmQIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *; omega)

private def CompGmPushApplyPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), ((q_b, p_new), top_old)), s =>
    CompGmPushMetaPre w ((((cp, metaBase), (b, q_b)), (p_new, top_old))) s

private theorem realizesBounded_compGmPushApply :
    RealizesBounded .exact compGmPushApplyProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushApplyPre (fun _ _ => 0) := by
  have hown := realizesBounded_compGmPushWriteOwner
  have hlnk := realizesBounded_compGmPushWriteLinks
  have hfin := realizesBounded_compGmPushFinish
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨⟨q_b, p_new⟩, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt, htop_lt⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hq_le_p, hp_lt, htop_lt⟩
    dsimp only [compGmPushWriteOwnerProg, StateTransitionSpec.clientState]
    simp [runClient_state_writeCompGMGenProg, hfr]
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨⟨q_b, p_new⟩, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt, _⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hq_le_p, hp_lt⟩
    dsimp only [compGmPushWriteOwnerProg, compGmPushWriteLinksProg, cpDirSlabs_mk,
      StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg]
    by_cases hc0 : 0 < q_b
    · by_cases hc1 : q_b < dirSlabsPerBucket N
      · simp [hc0, hc1, runClient_state_writeCompGMGenProg, hfr]
      · simp [hc0, hc1, hfr]
    · by_cases hc1 : q_b < dirSlabsPerBucket N
      · simp [hc0, hc1, runClient_state_writeCompGMGenProg, hfr]
      · simp [hc0, hc1, hfr]

private theorem realizesBounded_compGmPushRead :
    RealizesBounded .exact compGmPushReadProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [hq_eq, htop_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *; omega)

theorem realizesBounded_compGmPushSlabGen :
    RealizesBounded .exact compGmPushSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compGmPushRead
  have happ := realizesBounded_compGmPushApply
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hq_le_p := q_le_nslabs_of_slabBijection hslab hb
    have hrd_st : (Memory.spec 0).clientState s
        (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState; simp [compGmPushReadProg]
    have hrd_res : (Memory.spec 0).clientResult s
        (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) =
        ((compGmAt metaBase U w N s.mem (gmQIdx b), compGmAt metaBase U w N s.mem 0),
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
      dsimp only [compGmPushReadProg]
      rw [hq_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hq_idx_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg,
        htop_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg htop_idx_lt,
        clientState_readCompGMGenProg]
      rfl
    rw [hrd_st, hrd_res]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt,
      fun hq_pos => (hslab.top_lt hb hq_pos).trans hp_lt⟩

private def compGmUnlinkWriteProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (bel_del, q_b)) => do
    let q_idx := 4 + (b + b + b)
    writeCompGMGenProg (((cp, metaBase), q_idx + 2), bel_del)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b - 1)

private def compGmUnlinkTopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let q_idx := 4 + (b + b + b)
    let p_del ← readCompGMGenProg ((cp, metaBase), q_idx + 2)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let p2 := p_del + p_del
    let bel_idx := cpGmSlabMetaBase cp + (p2 + p2) + 2
    let bel_del ← readCompGMGenProg ((cp, metaBase), bel_idx)
    compGmUnlinkWriteProg ((((cp, metaBase), b), (bel_del, q_b)))
    pure p_del

private def compGmRelinkWriteProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), ((b_last, s_last), q_last)) => do
    let q_idx := 4 + (b_last + b_last + b_last)
    (if s_last < cpDirSlabs cp then
      let dir_idx := cpGmSlabDirBase cp + b_last * cpDirSlabs cp + s_last
      writeCompGMGenProg (((cp, metaBase), dir_idx), p_del)
    else
      pure ()) >>= fun _ =>
      if s_last + 1 = q_last then
        writeCompGMGenProg (((cp, metaBase), q_idx + 2), p_del)
      else
        pure ()

private def compGmRelinkMovedSlabGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let pl2 := p_last + p_last
    let ownB_idx := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_idx)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_idx + 1)
    let q_idx := 4 + (b_last + b_last + b_last)
    let q_last ← readCompGMGenProg ((cp, metaBase), q_idx)
    compGmRelinkWriteProg ((((cp, metaBase), p_del), ((b_last, s_last), q_last)))

private def compGmReadMovedMetaProg :
    (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), p_last) => do
    let pl2 := p_last + p_last
    let ownB_last := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_last)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 1)
    let bel_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 2)
    let abv_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 3)
    pure ((b_last, s_last), (bel_last, abv_last))

private def compGmUpdateNeighborLinksProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), p_del), ((b_last, s_last), (bel_last, abv_last))) => do
    let q_idx := 4 + (b_last + b_last + b_last)
    let q_last ← readCompGMGenProg ((cp, metaBase), q_idx)
    (if 0 < s_last then
      let bl2 := bel_last + bel_last
      let bel_abv_idx := cpGmSlabMetaBase cp + (bl2 + bl2) + 3
      writeCompGMGenProg (((cp, metaBase), bel_abv_idx), p_del)
    else
      pure ()) >>= fun _ =>
      if s_last + 1 < q_last then
        let al2 := abv_last + abv_last
        let abv_bel_idx := cpGmSlabMetaBase cp + (al2 + al2) + 2
        writeCompGMGenProg (((cp, metaBase), abv_bel_idx), p_del)
      else
        pure ()

private def compGmCopyMovedMetaProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), p_del), ((b_last, s_last), (bel_last, abv_last))) => do
    let pd2 := p_del + p_del
    let ownB_del := cpGmSlabMetaBase cp + (pd2 + pd2)
    writeCompGMGenProg (((cp, metaBase), ownB_del), b_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 1), s_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 2), bel_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 3), abv_last)

private def compGmLinkMovedNeighborsGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let info ← compGmReadMovedMetaProg ((cp, metaBase), p_last)
    compGmUpdateNeighborLinksProg ((((cp, metaBase), p_del), info))
    compGmCopyMovedMetaProg ((((cp, metaBase), p_del), info))

private def compGmMoveLastSlabMetaProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    compGmRelinkMovedSlabGenProg (((cp, metaBase), p_del), p_last)
    compGmLinkMovedNeighborsGenProg (((cp, metaBase), p_del), p_last)

private def compGmCompactSlabStepProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    (if p_del < p_last then
      compGmMoveLastSlabMetaProg (((cp, metaBase), p_del), p_last)
    else
      pure ()) >>= fun _ =>
      writeCompGMGenProg (((cp, metaBase), 0), p_last)

private def compGmCompactSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), p_del) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    compGmCompactSlabStepProg (((cp, metaBase), p_del), n_slabs - 1)

/-- Pop the top slab of bucket `b` and compact the slab pool in `GlobalMeta` (`gmPopSlab`,
`¬ReadsWidth`). -/
def compGmPopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let p_del ← compGmUnlinkTopSlabGenProg ((cp, metaBase), b)
    compGmCompactSlabGenProg ((cp, metaBase), p_del)

private theorem memoryCost_compGmUnlinkTopSlabGenProg_eq
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmUnlinkTopSlabGenProg d) s = 14 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg]

private theorem memoryCost_compGmRelinkMovedSlabGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmRelinkMovedSlabGenProg d) s ≤ 14 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  dsimp only [compGmRelinkMovedSlabGenProg, compGmRelinkWriteProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

private theorem memoryCost_compGmLinkMovedNeighborsGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmLinkMovedNeighborsGenProg d) s ≤ 34 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  dsimp only [compGmLinkMovedNeighborsGenProg, compGmReadMovedMetaProg,
    compGmUpdateNeighborLinksProg, compGmCopyMovedMetaProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg, memoryCost_pure]
  split_ifs <;> simp

private theorem memoryCost_compGmCompactSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmCompactSlabGenProg d) s ≤ 54 := by
  rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
  dsimp only [compGmCompactSlabGenProg, compGmCompactSlabStepProg, compGmMoveLastSlabMetaProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg]
  split_ifs
  · simp only [Realization.memoryCost_bind']
    have h1 := memoryCost_compGmRelinkMovedSlabGenProg_le
      (((cp, metaBase), p_del),
        (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)
      ((Memory.spec 0).clientState s (readCompGMGenProg ((cp, metaBase), 0)))
    have h2 := memoryCost_compGmLinkMovedNeighborsGenProg_le
      (((cp, metaBase), p_del),
        (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (readCompGMGenProg ((cp, metaBase), 0)))
        (compGmRelinkMovedSlabGenProg
          (((cp, metaBase), p_del),
            (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)))
    omega
  · simp

theorem memoryCost_compGmPopSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPopSlabGenProg d) s ≤ 68 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPopSlabGenProg]
  rw [Realization.memoryCost_bind', memoryCost_compGmUnlinkTopSlabGenProg_eq]
  have h2 := memoryCost_compGmCompactSlabGenProg_le
    ((cp, metaBase),
      (Memory.spec 0).clientResult s (compGmUnlinkTopSlabGenProg ((cp, metaBase), b)))
    ((Memory.spec 0).clientState s (compGmUnlinkTopSlabGenProg ((cp, metaBase), b)))
  omega

/-- Precondition for popping a slab in global metadata. -/
@[expose] def CompGmPopSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)

private def PureMovedSlabInv (N : ℕ) (gm : ℕ → ℕ) (p_del p_last : ℕ) : Prop :=
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let bel_last := gm (gmSlabBelowIdx N p_last)
  let abv_last := gm (gmSlabAboveIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  p_del < maxFullSlabs N ∧
  p_last < maxFullSlabs N ∧
  b_last < numBuckets N ∧
  s_last + 1 ≤ N ∧
  (0 < s_last → bel_last < maxFullSlabs N) ∧
  (s_last + 1 < q_last → abv_last < maxFullSlabs N) ∧
  0 < bucketBits N

private def CompGmMovedSlabPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last

private def CompGmCompactSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), p_del), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      1 ≤ compGmAt metaBase U w N s.mem 0 ∧
      compGmAt metaBase U w N s.mem 0 ≤ maxFullSlabs N ∧
      p_del < compGmAt metaBase U w N s.mem 0 ∧
      (p_del < compGmAt metaBase U w N s.mem 0 - 1 →
        PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del
          (compGmAt metaBase U w N s.mem 0 - 1))

private theorem compGmUnlinkTopSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hq_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b))
    (Memory.spec 0).clientResult s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)) =
      gm (gmSlabTopIdx b) ∧
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmUnlinkTopSlab N gm b := by
  intro gm s'
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have hp_del_cap : gm (gmSlabTopIdx b) < maxFullSlabs N :=
    lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
  have hbel_idx_lt : gmSlabBelowIdx N (gm (gmSlabTopIdx b)) < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_del_cap
  have hbel_eq : gmSlabMetaBase N +
      (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b) +
        (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b))) + 2 =
      gmSlabBelowIdx N (gm (gmSlabTopIdx b)) := by unfold gmSlabBelowIdx; omega
  have hbel_val : gm (gmSlabBelowIdx N (gm (gmSlabTopIdx b))) < 2 ^ globalPtrBits N :=
    compGmAt_lt ..
  have hq1_val : gm (gmQIdx b) - 1 < 2 ^ globalPtrBits N :=
    lt_of_le_of_lt (Nat.sub_le _ _) (compGmAt_lt ..)
  have hres : (Memory.spec 0).clientResult s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)) =
      gm (gmSlabTopIdx b) := by
    dsimp only [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg, cpGmSlabMetaBase_mk, gm]
    dsimp only [gm] at hbel_eq
    rw [hq_eq, htop_eq, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg htop_idx_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b),
          gm (gmSlabBelowIdx N (gm (gmSlabTopIdx b))))))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmQIdx b), gm (gmQIdx b) - 1)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg, cpGmSlabMetaBase_mk, gm]
    dsimp only [gm] at hbel_eq
    rw [hq_eq, htop_eq, StateTransitionSpec.clientState_bind,
      clientResult_readCompGMGenProg htop_idx_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
      clientState_readCompGMGenProg, hbel_eq, StateTransitionSpec.clientState_bind,
      clientResult_readCompGMGenProg hbel_idx_lt, clientState_readCompGMGenProg]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem htop_idx_lt
    hbel_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hq_idx_lt
    hq1_val _
  rw [hst]
  refine ⟨hres, hf1.trans hf2, ?_⟩
  rw [hg2, hg1]; rfl

private def CompGmUnlinkWritePre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (_bel_del, q_b)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      1 ≤ q_b

private theorem realizesBounded_compGmUnlinkWrite :
    RealizesBounded .exact compGmUnlinkWriteProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmUnlinkWritePre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨bel_del, q_b⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_pos⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try exact hq_pos
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabTopIdx gmQIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *; omega)

private theorem realizesBounded_compGmUnlinkTopSlab :
    RealizesBounded .exact compGmUnlinkTopSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwr := realizesBounded_compGmUnlinkWrite
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
    have hp_del_cap : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N :=
      lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
    have hbel_idx_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
    have hbel_eq : gmSlabMetaBase N +
        (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
            compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 2 =
        gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
      unfold gmSlabBelowIdx; omega
    simp only [cpGmSlabMetaBase_mk, hq_eq, htop_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg htop_idx_lt] at *
    rw [hbel_eq] at *
    try rw [clientResult_readCompGMGenProg hq_idx_lt] at *
    try rw [clientResult_readCompGMGenProg hbel_idx_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_pos⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmSlabBelowIdx gmSlabMetaBase gmQIdx at *
    omega)

private theorem compGmRelinkMovedSlabGenProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmRelinkMovedSlabGenProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmRelinkMovedSlab N gm p_del p_last := by
  intro gm s'
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, _, _, _, hb_pos⟩
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  have hownB_lt : gmSlabOwnerBIdx N p_last < globalMetaLen N :=
    gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hq_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have htop_eq : gmQIdx b_last + 2 = gmSlabTopIdx b_last := rfl
  have hdir_lt : s_last < dirSlabsPerBucket N →
      gmSlabDirIdx N b_last s_last < globalMetaLen N :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb_last hdir
  have htop_lt : s_last + 1 = q_last → gmSlabTopIdx b_last < globalMetaLen N :=
    fun _ => gmSlabTopIdx_lt hb_pos hb_last
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val : p_del < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (if s_last < dirSlabsPerBucket N then
          writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmSlabDirIdx N b_last s_last), p_del)
        else pure ()))
      (if s_last + 1 = q_last then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b_last), p_del)
      else pure ()) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmRelinkMovedSlabGenProg, compGmRelinkWriteProg, cpGmSlabMetaBase_mk,
      cpDirSlabs_mk, cpGmSlabDirBase_mk, gmSlabDirIdx, gmSlabOwnerSIdx, b_last, s_last, q_last, gm]
    dsimp only [b_last, gm] at hq_eq htop_eq hq_lt
    rw [hpl4, StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hownB_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind,
      clientResult_readCompGMGenProg hownS_lt, clientState_readCompGMGenProg,
      hq_eq, StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_lt,
      clientState_readCompGMGenProg, htop_eq, StateTransitionSpec.clientState_bind]
    rfl
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last < dirSlabsPerBucket N) hw hitem hdir_lt (fun _ => hp_del_val) s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last + 1 = q_last) hw hitem htop_lt (fun _ => hp_del_val) _
  rw [hst]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1]; rfl

private def CompGmRelinkWritePre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (((cp, metaBase), _p_del), ((b_last, s_last), _q_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b_last < numBuckets N ∧
      s_last + 1 ≤ N

private theorem realizesBounded_compGmRelinkWrite :
    RealizesBounded .exact compGmRelinkWriteProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmRelinkWritePre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, q_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have htop_lt := gmSlabTopIdx_lt hb_pos hb_last
    simp only [cpDirSlabs_mk, cpGmSlabDirBase_mk, StateTransitionSpec.clientState] at *)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    have hc_dir : s_last < dirSlabsPerBucket N := by assumption
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb_last hc_dir
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
       simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabDirIdx gmSlabDirBase at *; omega))
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
    · by_cases hc : s_last < dirSlabsPerBucket N
      · simp [hc, runClient_state_writeCompGMGenProg, hfr]
      · simp [hc, hfr]
    · simp only [cpN_mk]; unfold gmSlabTopIdx at htop_lt; omega)
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmQIdx gmSlabTopIdx at *; omega

private theorem realizesBounded_compGmRelinkMovedSlab :
    RealizesBounded .exact compGmRelinkMovedSlabGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwr := realizesBounded_compGmRelinkWrite
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      hp_del_cap, hp_last_cap, hb_last, hs_le, _, _, hb_pos⟩ := h
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hq_eq : 4 + (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
        compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
        compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) =
        gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) := by
      unfold gmQIdx; omega
    simp only [cpGmSlabMetaBase_mk, hpl4, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg hownB_lt] at *
    try rw [clientResult_readCompGMGenProg hownS_lt] at *
    rw [hq_eq] at *
    try rw [clientResult_readCompGMGenProg hq_lt] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabOwnerBIdx gmQIdx at *; omega)
  all_goals try (
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase gmQIdx at *; omega)

private theorem compGmLinkMovedNeighborsGenProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmLinkMovedNeighborsGenProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmLinkMovedNeighbors N gm p_del p_last := by
  intro gm s'
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, _, hbel_cap, habv_cap, hb_pos⟩
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let bel_last := gm (gmSlabBelowIdx N p_last)
  let abv_last := gm (gmSlabAboveIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  have hownB_last_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last_lt : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hq_last_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hownB_del_lt := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del_lt := gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del_lt := gmSlabAboveIdx_lt hb_pos hp_del_cap
  have habv_bel_lt : 0 < s_last → gmSlabAboveIdx N bel_last < globalMetaLen N :=
    fun hs => gmSlabAboveIdx_lt hb_pos (hbel_cap hs)
  have hbel_abv_lt : s_last + 1 < q_last → gmSlabBelowIdx N abv_last < globalMetaLen N :=
    fun hs => gmSlabBelowIdx_lt hb_pos (habv_cap hs)
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val : p_del < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hb_val : b_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hs_val : s_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hbel_val : bel_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have habv_val : abv_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hpd4 : gmSlabMetaBase N + (p_del + p_del + (p_del + p_del)) =
      gmSlabOwnerBIdx N p_del := by unfold gmSlabOwnerBIdx; omega
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have hbl4 : gmSlabMetaBase N + (bel_last + bel_last + (bel_last + bel_last)) + 3 =
      gmSlabAboveIdx N bel_last := by unfold gmSlabAboveIdx; omega
  have hal4 : gmSlabMetaBase N + (abv_last + abv_last + (abv_last + abv_last)) + 2 =
      gmSlabBelowIdx N abv_last := by unfold gmSlabBelowIdx; omega
  have hrd_st : (Memory.spec 0).clientState s
      (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
    unfold StateTransitionSpec.clientState; simp [compGmReadMovedMetaProg]
  have hrd_res : (Memory.spec 0).clientResult s
      (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) =
      ((b_last, s_last), (bel_last, abv_last)) := by
    dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk, b_last, s_last, bel_last, abv_last,
      gm]
    rw [hpl4, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hownB_last_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hownS_last_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hbel_last_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg habv_last_lt, clientState_readCompGMGenProg]
    rfl
  let s_upd := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s
      (if 0 < s_last then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N bel_last), p_del)
      else pure ()))
    (if s_last + 1 < q_last then
      writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabBelowIdx N abv_last), p_del)
    else pure ())
  have hupd_st : (Memory.spec 0).clientState s
      (compGmUpdateNeighborLinksProg ((((mkCompParams U V w N, metaBase), p_del),
        ((b_last, s_last), (bel_last, abv_last))))) = s_upd := by
    dsimp only [compGmUpdateNeighborLinksProg, cpGmSlabMetaBase_mk, s_upd, q_last]
    dsimp only [b_last, bel_last, abv_last, gm] at hq_eq hq_last_lt hbl4 hal4 ⊢
    rw [hq_eq, StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_last_lt,
      clientState_readCompGMGenProg, hbl4, hal4, StateTransitionSpec.clientState_bind]
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_upd
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              gmSlabOwnerBIdx N p_del), b_last)))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmSlabOwnerSIdx N p_del), s_last)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabBelowIdx N p_del), bel_last)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabAboveIdx N p_del), abv_last)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmLinkMovedNeighborsGenProg]
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res,
      StateTransitionSpec.clientState_bind, hupd_st]
    dsimp only [compGmCopyMovedMetaProg, cpGmSlabMetaBase_mk,
      gmSlabOwnerSIdx, gmSlabBelowIdx, gmSlabAboveIdx]
    rw [hpd4]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (0 < s_last) hw hitem habv_bel_lt (fun _ => hp_del_val) s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last + 1 < q_last) hw hitem hbel_abv_lt (fun _ => hp_del_val) _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_del_lt
    hb_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_del_lt
    hs_val _
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_del_lt
    hbel_val _
  obtain ⟨hf6, hg6⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem habv_del_lt
    habv_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans hf6)))), ?_⟩
  rw [hg6, hg5, hg4, hg3, hg2, hg1]; rfl

private def CompGmReadMovedMetaPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_last < maxFullSlabs N

private theorem realizesBounded_compGmReadMovedMeta :
    RealizesBounded .exact compGmReadMovedMetaProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompGmReadMovedMetaPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hownB_last_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_last_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hbel_last_lt : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
      gmSlabBelowIdx_lt hb_pos hp_last_cap
    have habv_last_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
      gmSlabAboveIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    simp only [cpGmSlabMetaBase_mk, hpl4, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

private def CompGmUpdateNeighborLinksPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), _p_del), ((b_last, s_last), (bel_last, abv_last))), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b_last < numBuckets N ∧
      s_last + 1 ≤ N ∧
      (0 < s_last → bel_last < maxFullSlabs N) ∧
      (s_last + 1 < compGmAt metaBase U w N s.mem (gmQIdx b_last) → abv_last < maxFullSlabs N)

private theorem realizesBounded_compGmUpdateNeighborLinks :
    RealizesBounded .exact compGmUpdateNeighborLinksProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompGmUpdateNeighborLinksPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le,
      hbel_cap, habv_cap⟩ := h
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
    simp only [cpGmSlabMetaBase_mk, hq_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg hq_lt] at *)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmQIdx at *; omega)
  all_goals try (
    have hc_s : 0 < s_last := by assumption
    have hbel_abv := gmSlabAboveIdx_lt hb_pos (hbel_cap hc_s)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
       simp only [cpN_mk]; unfold gmSlabAboveIdx at hbel_abv; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabAboveIdx gmSlabMetaBase at *; omega))
  all_goals try (
    have hc_abv : s_last + 1 < compGmAt metaBase U w N s.mem (gmQIdx b_last) := by assumption
    have habv_bel := gmSlabBelowIdx_lt hb_pos (habv_cap hc_abv)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
       · by_cases hc0 : 0 < s_last
         · simp [hc0, runClient_state_writeCompGMGenProg, hfr]
         · simp [hc0, hfr]
       · simp only [cpN_mk]; unfold gmSlabBelowIdx at habv_bel; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabBelowIdx gmSlabMetaBase at *; omega))
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmQIdx at *; omega

private def CompGmCopyMovedMetaPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), p_del), _info), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_del < maxFullSlabs N

private theorem realizesBounded_compGmCopyMovedMeta :
    RealizesBounded .exact compGmCopyMovedMetaProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompGmCopyMovedMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
    have hownB_del_lt := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
    have hownS_del_lt : gmSlabOwnerBIdx N p_del + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_del_cap
    have hbel_del_lt : gmSlabOwnerBIdx N p_del + 2 < globalMetaLen N :=
      gmSlabBelowIdx_lt hb_pos hp_del_cap
    have habv_del_lt : gmSlabOwnerBIdx N p_del + 3 < globalMetaLen N :=
      gmSlabAboveIdx_lt hb_pos hp_del_cap
    have hpd4 : gmSlabMetaBase N + (p_del + p_del + (p_del + p_del)) =
        gmSlabOwnerBIdx N p_del := by unfold gmSlabOwnerBIdx; omega
    simp only [cpGmSlabMetaBase_mk, hpd4, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

private theorem realizesBounded_compGmLinkMovedNeighbors :
    RealizesBounded .exact compGmLinkMovedNeighborsGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compGmReadMovedMeta
  have hupd := realizesBounded_compGmUpdateNeighborLinks
  have hcpy := realizesBounded_compGmCopyMovedMeta
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, _, _, _, _, hb_pos⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩ := h
    have hownB_last_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_last_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hbel_last_lt : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
      gmSlabBelowIdx_lt hb_pos hp_last_cap
    have habv_last_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
      gmSlabAboveIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hrd_st : (Memory.spec 0).clientState s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
      unfold StateTransitionSpec.clientState; simp [compGmReadMovedMetaProg]
    have hrd_res : (Memory.spec 0).clientResult s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) =
        ((compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
          compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)),
         (compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last),
          compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last))) := by
      dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk]
      rw [hpl4, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hownB_last_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg hownS_last_lt, clientState_readCompGMGenProg,
        StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hbel_last_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg habv_last_lt, clientState_readCompGMGenProg]
      rfl
    rw [hrd_st, hrd_res]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le, hbel_cap, habv_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      hp_del_cap, _, _, _, _, _, hb_pos⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hp_del_cap⟩
    have hrd_st : (Memory.spec 0).clientState s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
      unfold StateTransitionSpec.clientState; simp [compGmReadMovedMetaProg]
    rw [hrd_st]
    rcases (Memory.spec 0).clientResult s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) with
      ⟨⟨bL, sL⟩, ⟨belL, abvL⟩⟩
    dsimp only [compGmUpdateNeighborLinksProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg]
    split_ifs <;> simp [runClient_state_writeCompGMGenProg, hfr]

private theorem pureMovedSlabInv_after_relink {N p_del p_last : ℕ} {gm : ℕ → ℕ}
    (hinv : PureMovedSlabInv N gm p_del p_last) :
    PureMovedSlabInv N (gmRelinkMovedSlab N gm p_del p_last) p_del p_last := by
  rcases hinv with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  rcases gmRelinkMovedSlab_preserves_meta gm (p_del := p_del) hb_last with ⟨_, hpQ, hpGe⟩
  have hB : gmSlabMetaBase N ≤ gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hS : gmSlabMetaBase N ≤ gmSlabOwnerSIdx N p_last := by unfold gmSlabOwnerSIdx; omega
  have hBel : gmSlabMetaBase N ≤ gmSlabBelowIdx N p_last := by unfold gmSlabBelowIdx; omega
  have hAbv : gmSlabMetaBase N ≤ gmSlabAboveIdx N p_last := by unfold gmSlabAboveIdx; omega
  unfold PureMovedSlabInv; dsimp only
  rw [hpGe _ hB, hpGe _ hS, hpGe _ hBel, hpGe _ hAbv, hpQ]
  exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩

private theorem compGmCompactSlabGenProg_effect {metaBase itemBase U V w N m_items p_del : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (h0_pos : 1 ≤ compGmAt metaBase U w N s.mem 0)
    (h0_le : compGmAt metaBase U w N s.mem 0 ≤ maxFullSlabs N)
    (hcond : p_del < compGmAt metaBase U w N s.mem 0 - 1 →
      PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del
        (compGmAt metaBase U w N s.mem 0 - 1)) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmCompactSlabGenProg ((mkCompParams U V w N, metaBase), p_del))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmCompactSlab N gm p_del := by
  intro gm s'
  let p_last := gm 0 - 1
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_last_val : p_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [p_last, gm] at *; omega)
  dsimp only [s', compGmCompactSlabGenProg, compGmCompactSlabStepProg, compGmMoveLastSlabMetaProg]
  rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind]
  by_cases hlt : p_del < p_last
  · have hm1 := hcond hlt
    obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect (m_items := m_items) hw hitem s hm1
    obtain ⟨hf2, hg2⟩ := compGmLinkMovedNeighborsGenProg_effect (m_items := m_items) hw hitem _
      (hg1.symm ▸ pureMovedSlabInv_after_relink hm1)
    obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val _
    rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind]
    refine ⟨hf1.trans (hf2.trans hf3), ?_⟩
    rw [hg3, hg2, hg1]
    exact gmCompactSlab_eq_parts gm hlt hm1.2.2.1
  · obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val s
    rw [ite_eq_right hlt, StateTransitionSpec.clientState_pure]
    refine ⟨hf1, ?_⟩
    unfold gmCompactSlab; rw [ite_eq_right hlt, hg1]

private theorem realizesBounded_compGmMoveLastSlabMeta :
    RealizesBounded .exact compGmMoveLastSlabMetaProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hrel := realizesBounded_compGmRelinkMovedSlab
  have hlnk := realizesBounded_compGmLinkMovedNeighbors
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hinv⟩ := h
    obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s hinv
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr,
      hg1.symm ▸ pureMovedSlabInv_after_relink hinv⟩

private def CompGmCompactSlabStepPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      (p_del < p_last → PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last)

private theorem realizesBounded_compGmCompactSlabStep :
    RealizesBounded .exact compGmCompactSlabStepProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCompactSlabStepPre (fun _ _ => 0) := by
  have hmov := realizesBounded_compGmMoveLastSlabMeta
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega)
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hcond hc⟩
  refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, h0_lt⟩
  by_cases hc : p_del < p_last
  · rw [ite_eq_left hc]
    dsimp only [compGmMoveLastSlabMetaProg]
    obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s (hcond hc)
    obtain ⟨hf2, _⟩ := compGmLinkMovedNeighborsGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl _ (hg1.symm ▸ pureMovedSlabInv_after_relink (hcond hc))
    rw [StateTransitionSpec.clientState_bind, hf2.frontier_eq, hf1.frontier_eq]
    exact hfr
  · simp [hc, hfr]

private theorem realizesBounded_compGmCompactSlab :
    RealizesBounded .exact compGmCompactSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCompactSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hstp := realizesBounded_compGmCompactSlabStep
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, h0_pos, h0_le, hp_lt, hcond⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  all_goals try exact h0_pos
  exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩

private theorem pureCompactSlab_of_slabBijection {N b : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslab : SlabBijection N gm (fun b' => gm (gmQIdx b')) (gm 0))
    (hq_pos : 1 ≤ gm (gmQIdx b)) :
    let p_del := gm (gmSlabTopIdx b)
    let gm' := gmUnlinkTopSlab N gm b
    1 ≤ gm' 0 ∧ gm' 0 ≤ maxFullSlabs N ∧ p_del < gm' 0 ∧
    (p_del < gm' 0 - 1 → PureMovedSlabInv N gm' p_del (gm' 0 - 1)) := by
  intro p_del gm'
  obtain ⟨hu0, _, _, huQ, _, huGe, _⟩ := gmUnlinkTopSlab_fields gm hb
  have hB_ge : ∀ p, gmSlabDirBase N ≤ gmSlabOwnerBIdx N p :=
    fun _ => by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hS_ge : ∀ p, gmSlabDirBase N ≤ gmSlabOwnerSIdx N p :=
    fun _ => by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hBel_ge : ∀ p, gmSlabDirBase N ≤ gmSlabBelowIdx N p :=
    fun _ => by unfold gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hAbv_ge : ∀ p, gmSlabDirBase N ≤ gmSlabAboveIdx N p :=
    fun _ => by unfold gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hp_del_lt : p_del < gm 0 := hslab.top_lt hb hq_pos
  dsimp only [gm']
  rw [hu0]
  refine ⟨by omega, hslab.nslabs_le, hp_del_lt, fun hlt => ?_⟩
  unfold PureMovedSlabInv; dsimp only
  rw [huGe _ (hB_ge _), huGe _ (hS_ge _), huGe _ (hBel_ge _), huGe _ (hAbv_ge _)]
  obtain ⟨hb_last, hs_last, hptr_last⟩ := hslab.owner_valid (gm 0 - 1) (by omega)
  have hq_last_le : gm (gmQIdx (gm (gmSlabOwnerBIdx N (gm 0 - 1)))) ≤ gm 0 :=
    q_le_nslabs_of_slabBijection hslab hb_last
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  refine ⟨lt_of_lt_of_le hp_del_lt hslab.nslabs_le,
    lt_of_lt_of_le (by omega : gm 0 - 1 < gm 0) hslab.nslabs_le,
    hb_last, by have := hslab.nslabs_le; omega, ?_, ?_, hb_pos⟩
  · intro hs_pos
    have hbel_eq := hslab.below_eq _ hb_last _ hs_last hs_pos
    rw [hptr_last] at hbel_eq
    rw [hbel_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last (by omega)
  · intro hs_lt_q
    rw [huQ _ hb_last] at hs_lt_q
    have hs1_lt : gm (gmSlabOwnerSIdx N (gm 0 - 1)) + 1 <
        gm (gmQIdx (gm (gmSlabOwnerBIdx N (gm 0 - 1)))) := by
      split_ifs at hs_lt_q with hbeq
      · subst hbeq; omega
      · exact hs_lt_q
    have habv_eq := hslab.above_eq _ hb_last _ hs_last hs1_lt
    rw [hptr_last] at habv_eq
    rw [habv_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last hs1_lt

theorem compGmPopSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hq_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)) :
    let s' := (Memory.spec 0).clientState s
      (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmPopSlab N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  obtain ⟨hres1, hf1, hg1⟩ :=
    compGmUnlinkTopSlabGenProg_effect (m_items := m_items) hw hitem hb_pos hb s hslab hq_pos
  obtain ⟨hc1, hc2, _, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
  obtain ⟨hf2, hg2⟩ := compGmCompactSlabGenProg_effect
    (p_del := (Memory.spec 0).clientResult s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)))
    (m_items := m_items) hw hitem
    ((Memory.spec 0).clientState s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)))
    (hg1.symm ▸ hc1) (hg1.symm ▸ hc2)
    (by rw [hg1, hres1]; exact hc4)
  dsimp only [s', compGmPopSlabGenProg]
  rw [StateTransitionSpec.clientState_bind]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1, hres1]; rfl

theorem realizesBounded_compGmPopSlabGen :
    RealizesBounded .exact compGmPopSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hunl := realizesBounded_compGmUnlinkTopSlab
  have hcmp := realizesBounded_compGmCompactSlab
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    obtain ⟨hres1, hf1, hg1⟩ :=
      compGmUnlinkTopSlabGenProg_effect (itemBase := metaBase + offCompItems U w N) (m_items := 0)
        hw le_rfl hb_pos hb s hslab hq_pos
    obtain ⟨hc1, hc2, hc3, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr, hb_pos, ?_⟩
    rw [hres1, hg1]
    exact ⟨hc1, hc2, hc3, hc4⟩

/-! ## Section 5: `ValidProg w 0` Admissibility for Slot and Pool Operations -/

theorem validProg_compItemWordsGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compItemWordsGenProg d) := by
  rcases d with ⟨cp, m⟩
  intro _; dsimp only [compItemWordsGenProg, compQOffsetProg, packedOffsetProg]
  simp only [pure_bind]
  split_ifs <;> trivial

theorem validProg_compExtractQuotGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compExtractQuotGenProg d) :=
  fun _ => trivial

theorem validProg_compLastSlotOfGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompLastSlotOfPre w d s) : ValidProg w 0 s (compLastSlotOfGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, _hbc⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compLastSlotOfGenProg]
  simp only [pure_bind, cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk]
  refine validProg_ite
    (fun _ => validProg_bind (validProg_readCompGMGen ⟨henv, h0_lt⟩) (validProg_pure _))
    (fun hb0 => ?_)
  have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
    Nat.sub_lt_of_lt (hslot.multi_r_bounds hb_pos b hb).1
  rw [hr_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hr_idx_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, gmTailPtrIdx_lt hb_pos hb hr_cap⟩)
    (validProg_pure _)

theorem validProg_compResolveIndexedSlotGen {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompResolveIndexedSlotPre w d s) :
    ValidProg w 0 s (compResolveIndexedSlotGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  dsimp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg]
  simp only [cpBucketBits_mk, cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk,
    cpGmTailPtrBase_mk, cpTailCap_mk]
  refine validProg_ite (fun _ => validProg_pure j) (fun hb0 => ?_)
  have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
  have hK : 0 < slabSize N := slabSize_pos N
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  rw [hq_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_idx_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_idx_lt]
  refine validProg_ite (fun _ => ?_) (fun hj_ge => ?_)
  · have hs_lt_dir : j / slabSize N < dirSlabsPerBucket N := by
      rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hj_cap
      exact (Nat.div_lt_iff_lt_mul hK).2 hj_cap
    have hdir_lt : gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N) <
        globalMetaLen N := by
      have := gmSlabDirIdx_lt hb_pos hb hs_lt_dir; unfold gmSlabDirIdx at this; omega
    exact validProg_bind (validProg_readCompGMGen ⟨henv, hdir_lt⟩) (validProg_pure _)
  · obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_ge
    exact validProg_bind (validProg_readCompGMGen ⟨henv, hptr_lt⟩) (validProg_pure _)

theorem validProg_compResolveOvfStepGen {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)}
    {s : Memory.State} (h : CompResolveOvfStepPre w d s) :
    ValidProg w 0 s (compResolveOvfStepGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hj_bc, hslot, hp⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [cpSlabSize_mk, cpSlabSizeSubOne_mk, cpGmSlabMetaBase_mk,
    cpGmTailPtrBase_mk, cpTailCap_mk, hq_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_ite (fun hj_slab => ?_) (fun hj_ge => ?_)
  · refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul (slabSize_pos N)).2 hj_slab
    have hp_lt_max : p_cur < maxFullSlabs N :=
      hp hj_slab ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
    have habv_lt : gmSlabMetaBase N + (p_cur + p_cur + (p_cur + p_cur)) + 3 < globalMetaLen N := by
      have := gmSlabAboveIdx_lt hb_pos hp_lt_max; unfold gmSlabAboveIdx at this; omega
    exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_lt⟩) (validProg_pure _)
  · obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_ge
    exact validProg_bind (validProg_readCompGMGen ⟨henv, hptr_lt⟩) (validProg_pure _)

theorem validProg_compInitOvfSearchGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompInitOvfSearchPre w d s) : ValidProg w 0 s (compInitOvfSearchGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslot⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [cpSlabSize_mk, cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk,
    cpDirSlabsSubOne_mk, cpGmSlabMetaBase_mk, hq_eq, hr_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hr_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_lt]
  refine validProg_ite (fun hcap => ?_) (fun _ => validProg_pure _)
  refine validProg_ite (fun hqK => ?_) (fun _ => validProg_pure _)
  have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
    by_cases hN_le : N ≤ effBucketCap N
    · have hbc_le := bCount_le_n_max hslot b
      unfold bCount at hbc_le; simp only [hb_pos.ne', ↓reduceIte, hb] at hbc_le
      rw [min_eq_left hN_le] at hcap; omega
    · rw [min_eq_right (by omega)] at hqK; omega
  obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hdir_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hdir_lt, hdir_eq]
  have habv_lt := gmSlabAboveIdx_lt hb_pos hp_prev_max
  have habv_eq : gmSlabMetaBase N + (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1))) + 3 =
      gmSlabAboveIdx N (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1)) := by unfold gmSlabAboveIdx; omega
  rw [habv_eq]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_lt⟩) (validProg_pure _)

private theorem validProg_writeCompGM_bind {α : Type} {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ℕ} {s : Memory.State} {k : Unit → Memory.Prog α}
    (hd : WriteCompGMPre w d s)
    (hk : ∀ s' : Memory.State, s'.frontier = s.frontier → ValidProg w 0 s' (k ())) :
    ValidProg w 0 s (writeCompGMGenProg d >>= k) := by
  refine validProg_bind (validProg_writeCompGMGen hd) (hk _ ?_)
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩
  obtain ⟨⟨U, V, N, _, _, _, _, _, rfl, _⟩, _⟩ := hd
  rw [clientState_writeCompGMGenProg]

private theorem validProg_writeCompGM_ite_bind {α : Type} (P : Prop) [Decidable P] {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ℕ} {s : Memory.State} {k : Unit → Memory.Prog α}
    (hd : P → WriteCompGMPre w d s)
    (hk : ∀ s' : Memory.State, s'.frontier = s.frontier → ValidProg w 0 s' (k ())) :
    ValidProg w 0 s ((if P then writeCompGMGenProg d else pure ()) >>= k) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact validProg_writeCompGM_bind (hd hP) hk
  · rw [ite_eq_right hP, pure_bind]; exact hk s rfl

theorem validProg_compAppendTailGMGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompAppendTailGMPre w d s) : ValidProg w 0 s (compAppendTailGMGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
  have hown_lt := gmTailOwnerIdx_lt hb_pos (ntails_lt_maxTailItems_of_r_lt hb hr_lt htail)
  have hrd_v : ValidProg w 0 s
      (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compAppendTailReadGMProg]; rw [hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h1_lt⟩) (validProg_pure _)
  have hrd_s : (Memory.spec 0).clientState s
      (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState; simp [compAppendTailReadGMProg]
  have hrd_r : (Memory.spec 0).clientResult s
      (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      (compGmAt metaBase U w N s.mem (gmRIdx b), compGmAt metaBase U w N s.mem 1) := by
    dsimp only [compAppendTailReadGMProg]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl
  dsimp only [compAppendTailGMGenProg]
  refine validProg_bind hrd_v ?_
  rw [hrd_s, hrd_r]
  dsimp only [compAppendTailWriteGMProg, compAppendTailWrite1Prog, compAppendTailWrite2Prog,
    cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
  simp only [bind_assoc, hr_eq]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hptr_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hown_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hr_idx_lt⟩ fun s3 hs3 =>
        validProg_writeCompGM_bind ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), h1_lt⟩ fun _ _ =>
          validProg_pure _

theorem validProg_compRemoveTailGMOnlyGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompRemoveTailGMOnlyPre w d s) : ValidProg w 0 s (compRemoveTailGMOnlyGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
      compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
    lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hptr_del_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have ht_last_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by
    omega
  have hown_last_lt : gmTailOwnerBase N + (compGmAt metaBase U w N s.mem 1 - 1) <
      globalMetaLen N := gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_last_lt htail.ntails_le)
  have hptr_last_lt := gmTailPtrFlatIdx_lt hb_pos (htail.owner_lt_maxTailItems ht_last_lt)
  have hown_del_lt :=
    gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le (htail.ptr_lt b hb _ hr_del_lt) htail.ntails_le)
  have hrd_v : ValidProg w 0 s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compRemoveTailReadGMProg, cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    rw [hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hptr_del_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h1_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h1_lt]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hown_last_lt⟩) (validProg_pure _)
  have hrd_s : (Memory.spec 0).clientState s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGMProg]
  have hrd_r : (Memory.spec 0).clientResult s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem (gmRIdx b) - 1,
        compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))),
       (compGmAt metaBase U w N s.mem 1 - 1,
        compGmAt metaBase U w N s.mem
          (gmTailOwnerIdx N (compGmAt metaBase U w N s.mem 1 - 1)))) := by
    dsimp only [compRemoveTailReadGMProg, cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hptr_del_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h1_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hown_last_lt, clientState_readCompGMGenProg]; rfl
  dsimp only [compRemoveTailGMOnlyGenProg]
  refine validProg_bind hrd_v ?_
  rw [hrd_s, hrd_r]
  dsimp only [compRemoveTailWriteGMProg, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
  rw [hr_eq]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hptr_last_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hown_del_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hr_idx_lt⟩ fun s3 hs3 =>
        validProg_writeCompGMGen ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), h1_lt⟩

theorem validProg_compGmPushSlabGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompGmPushSlabPre w d s) : ValidProg w 0 s (compGmPushSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : gmSlabOwnerBIdx N (compGmAt metaBase U w N s.mem 0) + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hbel_lt : gmSlabOwnerBIdx N (compGmAt metaBase U w N s.mem 0) + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_lt
  have hrd_v : ValidProg w 0 s (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compGmPushReadProg]; rw [hq_eq, htop_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, htop_lt⟩) (validProg_pure _)
  have hrd_s : (Memory.spec 0).clientState s
      (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState; simp [compGmPushReadProg]
  have hrd_r : (Memory.spec 0).clientResult s
      (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem (gmQIdx b), compGmAt metaBase U w N s.mem 0),
       compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
    dsimp only [compGmPushReadProg]
    rw [hq_eq, htop_eq, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hq_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg htop_lt, clientState_readCompGMGenProg]; rfl
  dsimp only [compGmPushSlabGenProg]
  refine validProg_bind hrd_v ?_
  rw [hrd_s, hrd_r]
  set q_b := compGmAt metaBase U w N s.mem (gmQIdx b)
  set p_new := compGmAt metaBase U w N s.mem 0
  set top_old := compGmAt metaBase U w N s.mem (gmSlabTopIdx b)
  have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) = gmSlabOwnerBIdx N p_new := by
    unfold gmSlabOwnerBIdx; omega
  have ht4 : gmSlabMetaBase N + (top_old + top_old + (top_old + top_old)) + 3 =
      gmSlabAboveIdx N top_old := by unfold gmSlabAboveIdx; omega
  dsimp only [compGmPushApplyProg, compGmPushWriteOwnerProg, compGmPushWriteLinksProg,
    compGmPushFinishProg, cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk]
  simp only [bind_assoc, hp4, ht4, hq_eq, htop_eq]
  refine validProg_writeCompGM_bind ⟨mkEnv s rfl, hownB_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hownS_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hbel_lt⟩ fun s3 hs3 => ?_
  have hs3_eq : s3.frontier = s.frontier := hs3.trans (hs2.trans hs1)
  refine validProg_writeCompGM_ite_bind (0 < q_b)
    (fun hq_pos =>
      ⟨mkEnv s3 hs3_eq, gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)⟩)
    fun s4 hs4 => ?_
  have hs4_eq : s4.frontier = s.frontier := hs4.trans hs3_eq
  refine validProg_writeCompGM_ite_bind (q_b < dirSlabsPerBucket N)
    (fun hdir => ⟨mkEnv s4 hs4_eq, gmSlabDirIdx_lt hb_pos hb hdir⟩)
    fun s5 hs5 => ?_
  have hs5_eq : s5.frontier = s.frontier := hs5.trans hs4_eq
  exact validProg_writeCompGM_bind ⟨mkEnv s5 hs5_eq, htop_lt⟩ fun s6 hs6 =>
    validProg_writeCompGM_bind ⟨mkEnv s6 (hs6.trans hs5_eq), hq_lt⟩ fun s7 hs7 =>
      validProg_writeCompGMGen ⟨mkEnv s7 (hs7.trans (hs6.trans hs5_eq)), h0_lt⟩

private theorem validProg_compGmUnlinkTopSlab {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmPopSlabPre w d s) :
    ValidProg w 0 s (compGmUnlinkTopSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have hp_del_max : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N :=
    lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
  have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_del_max
  have hp4 : gmSlabMetaBase N + (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 2 =
      gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
    unfold gmSlabBelowIdx; omega
  dsimp only [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg, cpGmSlabMetaBase_mk]
  rw [hq_eq, htop_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, htop_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg htop_lt]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, hp4]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hbel_lt⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind
    (validProg_writeCompGM_bind ⟨mkEnv s rfl, htop_lt⟩ fun s1 hs1 =>
      validProg_writeCompGMGen ⟨mkEnv s1 hs1, hq_lt⟩) ?_
  exact validProg_pure _

private theorem validProg_compGmRelinkMovedSlab {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmRelinkMovedSlabGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, _hp_del_cap, hp_last_cap, hb_last, _hs_le,
    _, _, hb_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hq_lt : gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) <
      globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have htop_lt : gmSlabTopIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) <
      globalMetaLen N := gmSlabTopIdx_lt hb_pos hb_last
  have hq_eq : 4 + (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
      compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
      compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) =
      gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) := by
    unfold gmQIdx; omega
  have htop_eq : gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) + 2 =
      gmSlabTopIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) := rfl
  dsimp only [compGmRelinkMovedSlabGenProg, compGmRelinkWriteProg, cpGmSlabMetaBase_mk,
    cpDirSlabs_mk, cpGmSlabDirBase_mk]
  rw [hpl4]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hownB_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hownB_lt]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hownS_lt⟩) ?_
  rw [clientState_readCompGMGenProg, hq_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, htop_eq]
  exact validProg_writeCompGM_ite_bind _
    (fun hdir => ⟨mkEnv s rfl, gmSlabDirIdx_lt hb_pos hb_last hdir⟩)
    fun s1 hs1 => validProg_ite
      (fun _ => validProg_writeCompGMGen ⟨mkEnv s1 hs1, htop_lt⟩)
      (fun _ => validProg_pure ())

private theorem validProg_compGmReadMovedMeta {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmReadMovedMetaPre w d s) :
    ValidProg w 0 s (compGmReadMovedMetaProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have hownB_last := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk]
  rw [hpl4]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hownB_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hownS_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hbel_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_last⟩) (validProg_pure _)

private theorem validProg_compGmUpdateNeighborLinks {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (h : CompGmUpdateNeighborLinksPre w d s) :
    ValidProg w 0 s (compGmUpdateNeighborLinksProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, _hs_le,
    hbel_cap, habv_cap⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hq_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have hbl4 : gmSlabMetaBase N + (bel_last + bel_last + (bel_last + bel_last)) + 3 =
      gmSlabAboveIdx N bel_last := by unfold gmSlabAboveIdx; omega
  have hal4 : gmSlabMetaBase N + (abv_last + abv_last + (abv_last + abv_last)) + 2 =
      gmSlabBelowIdx N abv_last := by unfold gmSlabBelowIdx; omega
  dsimp only [compGmUpdateNeighborLinksProg, cpGmSlabMetaBase_mk]
  rw [hq_eq, hbl4, hal4]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_writeCompGM_ite_bind (0 < s_last)
    (fun hs0 => ⟨mkEnv s rfl, gmSlabAboveIdx_lt hb_pos (hbel_cap hs0)⟩) fun s1 hs1 => ?_
  exact validProg_ite
    (fun hsa => validProg_writeCompGMGen ⟨mkEnv s1 hs1, gmSlabBelowIdx_lt hb_pos (habv_cap hsa)⟩)
    (fun _ => validProg_pure ())

private theorem validProg_compGmCopyMovedMeta {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (h : CompGmCopyMovedMetaPre w d s) :
    ValidProg w 0 s (compGmCopyMovedMetaProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hownB_del := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del : gmSlabOwnerBIdx N p_del + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del : gmSlabOwnerBIdx N p_del + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del : gmSlabOwnerBIdx N p_del + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_del_cap
  have hpd4 : gmSlabMetaBase N + (p_del + p_del + (p_del + p_del)) = gmSlabOwnerBIdx N p_del := by
    unfold gmSlabOwnerBIdx; omega
  dsimp only [compGmCopyMovedMetaProg, cpGmSlabMetaBase_mk]
  rw [hpd4]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hownB_del⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hownS_del⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hbel_del⟩ fun s3 hs3 =>
        validProg_writeCompGMGen ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), habv_del⟩

theorem validProg_bind_unit {β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog Unit} {q : Memory.Prog β}
    (hp : ValidProg w 0 s p)
    (hq : ∀ s' : Memory.State, s' = (Memory.spec 0).clientState s p → ValidProg w 0 s' q) :
    ValidProg w 0 s (p >>= fun _ => q) :=
  validProg_bind hp (hq _ rfl)

private theorem validProg_compGmLinkMovedNeighbors {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmLinkMovedNeighborsGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hp_del_cap, hp_last_cap, hb_last, hs_le,
    hbel_cap, habv_cap, hb_pos⟩ := h
  have hownB_last := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hrd_s : (Memory.spec 0).clientState s
      (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
    unfold StateTransitionSpec.clientState; simp [compGmReadMovedMetaProg]
  have hrd_r : (Memory.spec 0).clientResult s
      (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) =
      ((compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
        compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)),
       (compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last),
        compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last))) := by
    dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk]
    rw [hpl4, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hownB_last,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hownS_last, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hbel_last,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg habv_last, clientState_readCompGMGenProg]
    rfl
  dsimp only [compGmLinkMovedNeighborsGenProg]
  refine validProg_bind
    (validProg_compGmReadMovedMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩)
    ?_
  rw [hrd_s, hrd_r]
  refine validProg_bind_unit
    (validProg_compGmUpdateNeighborLinks
      ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le, hbel_cap, habv_cap⟩)
    fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier := by
    have hs1_fr : s1.frontier = s.frontier := by
      rw [hs1]
      dsimp only [compGmUpdateNeighborLinksProg, StateTransitionSpec.clientState]
      simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg]
      split_ifs <;> simp [runClient_state_writeCompGMGenProg]
    exact hs1_fr ▸ hfr
  exact validProg_compGmCopyMovedMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hb_pos, hp_del_cap⟩

private theorem pureMovedSlabInv_congr {N p_del p₁ p₂ : ℕ} {gm₁ gm₂ : ℕ → ℕ}
    (hgm : gm₁ = gm₂) (hp : p₁ = p₂) (hm : PureMovedSlabInv N gm₁ p_del p₁) :
    PureMovedSlabInv N gm₂ p_del p₂ := by
  subst hgm hp; exact hm

theorem validProg_bind_of_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {k : α → Memory.Prog β} {a : α}
    (hp : ValidProg w 0 s p)
    (hres : (Memory.spec 0).clientResult s p = a)
    (hk : ∀ s' : Memory.State, s' = (Memory.spec 0).clientState s p → ValidProg w 0 s' (k a)) :
    ValidProg w 0 s (p >>= k) := by
  refine validProg_bind hp ?_
  rw [hres]
  exact hk _ rfl

private theorem validProg_compGmMoveLastSlabMeta {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmMoveLastSlabMetaProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hm1⟩ := h
  obtain ⟨hf_r, hg_r⟩ := compGmRelinkMovedSlabGenProg_effect
    (itemBase := metaBase + offCompItems U w N) (m_items := 0) hw le_rfl s hm1
  refine validProg_bind_unit
    (validProg_compGmRelinkMovedSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hm1⟩)
    fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier :=
    hfr.trans_eq ((congrArg Memory.State.frontier hs1).trans hf_r.frontier_eq).symm
  have hgm1 := (congrArg (fun st : Memory.State => compGmAt metaBase U w N st.mem) hs1).trans hg_r
  have hm2 : PureMovedSlabInv N (compGmAt metaBase U w N s1.mem) p_del p_last :=
    pureMovedSlabInv_congr hgm1.symm rfl (pureMovedSlabInv_after_relink hm1)
  exact validProg_compGmLinkMovedNeighbors ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hm2⟩

private theorem validProg_compGmCompactSlabStep {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmCompactSlabStepPre w d s) :
    ValidProg w 0 s (compGmCompactSlabStepProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compGmCompactSlabStepProg]
  refine validProg_bind_unit
    (validProg_ite (fun hlt => ?_) (fun _ => validProg_pure ())) fun s1 hs1 => ?_
  · exact validProg_compGmMoveLastSlabMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hcond hlt⟩
  · have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier := by
      by_cases hlt : p_del < p_last
      · have hs1_eq : s1 = (Memory.spec 0).clientState s
            (compGmMoveLastSlabMetaProg (((mkCompParams U V w N, metaBase), p_del), p_last)) := by
          rw [hs1, ite_eq_left hlt]
        have hm1 := hcond hlt
        obtain ⟨hf_r, hg_r⟩ := compGmRelinkMovedSlabGenProg_effect
          (itemBase := metaBase + offCompItems U w N) (m_items := 0) hw le_rfl s hm1
        obtain ⟨hf_l, _⟩ := compGmLinkMovedNeighborsGenProg_effect
          (itemBase := metaBase + offCompItems U w N) (m_items := 0) hw le_rfl _
          (hg_r.symm ▸ pureMovedSlabInv_after_relink hm1)
        have hfr_eq : s1.frontier = s.frontier := by
          rw [hs1_eq]; dsimp only [compGmMoveLastSlabMetaProg]
          rw [StateTransitionSpec.clientState_bind, hf_l.frontier_eq, hf_r.frontier_eq]
        exact hfr.trans_eq hfr_eq.symm
      · have hs1_eq : s1 = s := by rw [hs1, ite_eq_right hlt]; rfl
        exact hs1_eq ▸ hfr
    exact validProg_writeCompGMGen ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1⟩, h0_lt⟩

private theorem validProg_compGmCompactSlab {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmCompactSlabPre w d s) :
    ValidProg w 0 s (compGmCompactSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, _, _, hcond⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compGmCompactSlabGenProg]
  refine validProg_bind_of_eq
    (validProg_readCompGMGen ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩)
    (clientResult_readCompGMGenProg (U := U) (V := V) (w := w) (metaBase := metaBase) h0_lt s)
    fun s1 hs1 => ?_
  have hs1_eq : s1 = s := hs1.trans (clientState_readCompGMGenProg _ s)
  subst hs1_eq
  exact validProg_compGmCompactSlabStep ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩

theorem validProg_compGmPopSlabGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompGmPopSlabPre w d s) : ValidProg w 0 s (compGmPopSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
  dsimp only [compGmPopSlabGenProg]
  obtain ⟨hres1, hf1, hg1⟩ :=
    compGmUnlinkTopSlabGenProg_effect (itemBase := metaBase + offCompItems U w N) (m_items := 0)
      hw le_rfl hb_pos hb s hslab hq_pos
  obtain ⟨hc1, hc2, hc3, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
  refine validProg_bind_of_eq
    (validProg_compGmUnlinkTopSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab,
      hq_pos⟩) hres1 fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier :=
    hfr.trans_eq ((congrArg Memory.State.frontier hs1).trans hf1.frontier_eq).symm
  have hgm1 : compGmAt metaBase U w N s1.mem =
      gmUnlinkTopSlab N (compGmAt metaBase U w N s.mem) b :=
    (congrArg (fun st : Memory.State => compGmAt metaBase U w N st.mem) hs1).trans hg1
  refine validProg_compGmCompactSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hb_pos,
    by rwa [hgm1], by rwa [hgm1], by rwa [hgm1], fun hlt => ?_⟩
  have hlt' : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
      gmUnlinkTopSlab N (compGmAt metaBase U w N s.mem) b 0 - 1 :=
    hlt.trans_eq (congrArg (· - 1) (congrFun hgm1 0))
  exact pureMovedSlabInv_congr hgm1.symm (congrArg (· - 1) (congrFun hgm1.symm 0)) (hc4 hlt')

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
