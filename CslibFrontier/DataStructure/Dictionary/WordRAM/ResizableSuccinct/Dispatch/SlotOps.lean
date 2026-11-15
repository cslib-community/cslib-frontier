/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Slot Resolvers and `GlobalMeta` Pool Updates in `Memory.Prog`

This internal module of `ResizableSuccinct.Dispatch` implements the compacted slot-resolution and
`GlobalMeta` pool-update subroutines in `Memory.Prog` (`¬ReadsWidth`, certified via `by realize`
with `RealizesBounded .exact`), bridging them via `FixedCoupled` to their fixed-capacity reference
counterparts in `Succinct`:
* overflow-free item-stream word-count evaluation (`compItemWordsGenProg`);
* ghost fixed-capacity parameter/envelope certificates (`ghostDictParamsWf`, `ghostDictEnvGen`) and
  `FixedCoupled` dense-to-physical lookup and in-place value-update bridges;
* compacted slot and count resolvers (`readCompTotalSlotsGenProg`, `compLastSlotOfGenProg`,
  `compResolveIndexedSlotGenProg`, `compResolveOvfStepGenProg`, `compInitOvfSearchGenProg`);
* compacted `GlobalMeta` pool updates (`compAppendTailGMGenProg`, `compRemoveTailGMOnlyGenProg`,
  `compGmPushSlabGenProg`, `compGmPopSlabGenProg`).
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

/-! ## Section 1: Overflow-Free `compactedItemWords` Evaluation (`compItemWordsGenProg`) -/

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

/-- Upper bound `wOffQ q v w (n + 1) ≤ compactedItemWords U V w N n` when `q ≤ w` and `v ≤ w`. -/
theorem wOffQ_succ_le_compactedItemWords {U V w N n : ℕ} (hw : 0 < w)
    (hq : quotientBits U N ≤ w) (hv : valBits V ≤ w) :
    wOffQ (quotientBits U N) (valBits V) w (n + 1) ≤ compactedItemWords U V w N n := by
  have hid1 := wOffQ_mul_add_bOffQ (q_bits := quotientBits U N) (v_bits := valBits V) (w := w)
    (d := n + 1)
  have hb1 : bOffQ (quotientBits U N) (valBits V) w (n + 1) < w := bOffQ_lt hw
  have hw1 : wOffQ (quotientBits U N) (valBits V) w (n + 1) =
      ((n + 1) * (quotientBits U N + valBits V)) / w := by
    rw [← hid1, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb1]; omega
  rw [hw1]
  unfold compactedItemWords
  have hle : (n + 1) * (quotientBits U N + valBits V) ≤
      (n * (quotientBits U N + valBits V) + w - 1) + 2 * w := by
    rw [Nat.add_one_mul]; omega
  calc ((n + 1) * (quotientBits U N + valBits V)) / w
      ≤ ((n * (quotientBits U N + valBits V) + w - 1) + 2 * w) / w := Nat.div_le_div_right hle
    _ = (n * (quotientBits U N + valBits V) + w - 1) / w + 2 := Nat.add_mul_div_right _ _ hw

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
    try simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, clientResult_compQOffsetProg] at *)
  all_goals try exact ⟨hw, rfl, hq, hv, hfit.of_le (by omega)⟩
  all_goals exact hfit.of_le (by omega)

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

theorem CompEpochEnv.compMetaEnv {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    CompMetaEnv w (mkCompParams U V w N) metaBase s :=
  ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier)⟩

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
theorem compGmAt_lt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    compGmAt metaBase U w N mem idx < 2 ^ globalPtrBits N := by
  unfold compGmAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Read `totalSlots N gm` (`= epochTotalSlots N gm`) at `metaBase` in `Memory.Prog`
(`¬ReadsWidth`). -/
def readCompTotalSlotsGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, metaBase) => do
    let z0 ← pure 0
    if cpBucketBits cp = z0 then
      readCompGMGenProg ((cp, metaBase), z0)
    else do
      let z1 ← pure 1
      let n_slabs ← readCompGMGenProg ((cp, metaBase), z0)
      let n_tails ← readCompGMGenProg ((cp, metaBase), z1)
      pure (n_slabs * cpSlabSize cp + n_tails)

theorem clientResult_readCompTotalSlotsGenProg {U V w N metaBase : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompTotalSlotsGenProg (mkCompParams U V w N, metaBase)) =
      totalSlots N (compGmAt metaBase U w N s.mem) := by
  dsimp only [readCompTotalSlotsGenProg, totalSlots, cpBucketBits_mk, cpSlabSize_mk]
  simp only [pure_bind]
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  by_cases hb0 : bucketBits N = 0
  · rw [ite_eq_left hb0, ite_eq_left hb0, clientResult_readCompGMGenProg h0_lt]
  · rw [ite_eq_right hb0, ite_eq_right hb0,
      prog_clientResult_bind, clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg,
      prog_clientResult_bind, clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      prog_clientResult_pure]

theorem clientState_readCompTotalSlotsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompTotalSlotsGenProg d) = s := by
  rcases d with ⟨cp, metaBase⟩
  unfold StateTransitionSpec.clientState; dsimp only [readCompTotalSlotsGenProg]
  simp only [pure_bind]; split_ifs <;> simp

@[simp] theorem runClient_state_readCompTotalSlotsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompTotalSlotsGenProg d))) = s :=
  clientState_readCompTotalSlotsGenProg d s

theorem memoryCost_readCompTotalSlotsGenProg_le (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (readCompTotalSlotsGenProg d) s ≤ 4 := by
  rcases d with ⟨cp, metaBase⟩
  dsimp only [readCompTotalSlotsGenProg]; simp only [pure_bind]; split_ifs <;> simp

/-- Precondition for reading total slots in compacted representation. -/
@[expose] def ReadCompTotalSlotsPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem)

theorem realizesBounded_readCompTotalSlotsGen :
    RealizesBounded .exact readCompTotalSlotsGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      ReadCompTotalSlotsPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpBucketBits_mk, cpSlabSize_mk, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg h0_lt, clientResult_readCompGMGenProg h1_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by assumption⟩
  all_goals (
    have hb_pos : 0 < bucketBits N := by omega
    have hSN := hslot.multi_total_le hb_pos
    exact lt_of_le_of_lt (by omega) hU)

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

/-- Precondition for retrieving the last slot of a generation. -/
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
    try simp only [cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk,
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
    try simp only [hr_eq, clientResult_readCompGMGenProg hr_idx_lt,
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

/-- Multi-bucket branch (`0 < bucketBits N`) of `compResolveIndexedSlotGenProg`. -/
def compResolveMultiSlotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
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
    · obtain ⟨_, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hj_slab
      have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + (j - gm (gmQIdx b) * slabSize N)) <
          globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
      simp only [gm] at hj_slab hptr_lt
      simp only [hj_slab, ↓reduceIte]
      rw [prog_clientResult_bind, clientResult_readCompGMGenProg hptr_lt,
        clientState_readCompGMGenProg, prog_clientResult_pure]
      unfold slotOf; simp only [hb0, gm, hj_slab, ↓reduceIte]; rfl

/-- Precondition for resolving multi-slot entries. -/
@[expose] def CompResolveMultiSlotPre (w : ℕ) :
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

theorem realizesBounded_compResolveMultiSlotGen :
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
    try simp only [cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpSlabSizeSubOne_mk,
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
    obtain ⟨_, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_cap
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; exact hptr_lt)
  all_goals try (
    obtain ⟨hr_lt, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [clientResult_readCompGMGenProg hptr_lt]
    have ht_lt := (hslot.multi_tail hb_pos).ptr_lt b hb _ hr_lt
    have ht_lt' : compGmAt metaBase U w N s.mem
        (gmTailPtrBase N + (b * tailCapPerBucket N +
          (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N))) <
        compGmAt metaBase U w N s.mem 1 := by
      simpa only [gmTailPtrIdx, gmTailPtrFlatIdx, Nat.add_assoc,
        ← (hslot.multi_tail hb_pos).ntails_eq] using ht_lt
    have hSN := hslot.multi_total_le hb_pos
    omega)
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
  all_goals try (
    have hs_lt_q : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul hK).2 hc
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
    exact lt_of_le_of_lt (by omega) hU)
  all_goals (
    obtain ⟨_, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_cap
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase at *
    omega)

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
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
    try simp only [cpBucketBits_mk] at *)
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, Nat.pos_of_ne_zero hc, hslot, hb, hj_bc, hj_cap⟩

/-- Advance slab pointer `p_cur` at a slab boundary (`off = 0`) when `j + 1 < qK`. -/
def compResolveOvfAdvanceGenProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), (j1, qK)), (phys, p_cur)) =>
    if j1 < qK then do
      let p2 := p_cur + p_cur
      let abv_idx := cpGmSlabMetaBase cp + (p2 + p2) + 3
      let p_next ← readCompGMGenProg ((cp, metaBase), abv_idx)
      pure (phys, p_next)
    else
      pure (phys, p_cur)

/-- In-slab branch (`j < qK`) of `compResolveOvfStepGenProg`. -/
def compResolveOvfInSlabGenProg :
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

/-- Precondition for advancing overflow resolution. -/
@[expose] def CompResolveOvfAdvancePre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), (_j1, _qK)), (_phys, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_cur < maxFullSlabs N

theorem realizesBounded_compResolveOvfAdvanceGen :
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
    try simp only [cpGmSlabMetaBase_mk] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabAboveIdx gmSlabMetaBase at *
    omega)

/-- Precondition for resolving overflow within a slab. -/
@[expose] def CompResolveOvfInSlabPre (w : ℕ) :
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

theorem realizesBounded_compResolveOvfInSlabGen :
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
    try simp only [cpSlabSize_mk, cpSlabSizeSubOne_mk] at *)
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
    try simp only [cpSlabSize_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk, hq_eq,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hq_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hq_lt⟩
  all_goals try (
    have hp_eq := hp hc
    have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul hK).2 hc
    have hp_lt_max : p_cur < maxFullSlabs N :=
      hp_eq ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
    have hp_lt : p_cur < compGmAt metaBase U w N s.mem 0 := by
      rw [hp_eq, (hslot.multi_slab hb_pos).nslabs_eq]
      exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt
    have hSN := hslot.multi_total_le hb_pos
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, by omega, hc, hp_lt_max,
      (Nat.mul_le_mul_right (slabSize N) hp_lt).trans (by omega)⟩)
  all_goals try (
    obtain ⟨-, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_cap
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; exact hptr_lt)
  all_goals try (
    obtain ⟨hr_lt, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [clientResult_readCompGMGenProg hptr_lt]
    have ht_lt := (hslot.multi_tail hb_pos).ptr_lt b hb _ hr_lt
    have ht_lt' : compGmAt metaBase U w N s.mem
        (gmTailPtrBase N + (b * tailCapPerBucket N +
          (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N))) <
        compGmAt metaBase U w N s.mem 1 := by
      simpa only [gmTailPtrIdx, gmTailPtrFlatIdx, Nat.add_assoc,
        ← (hslot.multi_tail hb_pos).ntails_eq] using ht_lt
    have hSN := hslot.multi_total_le hb_pos
    omega)
  all_goals try omega
  all_goals try exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by unfold gmQIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    obtain ⟨-, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hc
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_cap
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase at *
    omega)

/-- Inner directory branch (`cap < c`) of `compInitOvfSearchGenProg`. -/
def compInitOvfFromDirGenProg :
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

/-- Precondition for initializing overflow resolution from directory. -/
@[expose] def CompInitOvfFromDirPre (w : ℕ) :
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

theorem realizesBounded_compInitOvfFromDirGen :
    RealizesBounded .exact compInitOvfFromDirGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompInitOvfFromDirPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨qK, fuel⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hcapN, rfl, hslot⟩ := h
    try simp only [cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpDirSlabsSubOne_mk,
      cpGmSlabMetaBase_mk] at *)
  all_goals (
    have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
      rw [min_eq_right hcapN.le] at hc; omega
    obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_prev_max
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg hdir_lt,
      runClient_state_readCompGMGenProg] at *
    try rw [hdir_eq] at *)
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
    try simp only [cpSlabSize_mk, cpMinCap_mk, hq_eq, hr_eq, StateTransitionSpec.clientState,
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

theorem CompGmFrame.refl {metaBase itemBase U V w N m_items : ℕ} (s : Memory.State) :
    CompGmFrame metaBase itemBase U V w N m_items s s :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CompGmFrame.trans {metaBase itemBase U V w N m_items : ℕ} {s₁ s₂ s₃ : Memory.State}
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

theorem compGmFrame_writeCompGM_ite {metaBase itemBase U V w N m_items idx val : ℕ}
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

private def compAppendTailGM1Prog : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let t_new ← readCompGMGenProg ((cp, metaBase), 1)
    let ptr_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + r_b)
    writeCompGMGenProg (((cp, metaBase), ptr_idx), t_new)
    pure (r_b, t_new)

private def compAppendTailGM2Prog : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), (r_b, t_new)) => do
    let r_idx := 4 + (b + b + b) + 1
    let own_idx := cpGmTailOwnerBase cp + t_new
    writeCompGMGenProg (((cp, metaBase), own_idx), b * cpTailCap cp + r_b)
    writeCompGMGenProg (((cp, metaBase), r_idx), r_b + 1)
    writeCompGMGenProg (((cp, metaBase), 1), t_new + 1)
    pure t_new

/-- Append one tail descriptor to bucket `b` in compacted `GlobalMeta` (`gmAppendTail`), returning
`t_new = gm 1` (`¬ReadsWidth`). -/
def compAppendTailGMGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let rt ← compAppendTailGM1Prog ((cp, metaBase), b)
    compAppendTailGM2Prog (((cp, metaBase), b), rt)

@[simp] theorem memoryCost_compAppendTailGMGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compAppendTailGMGenProg d) s = 20 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compAppendTailGMGenProg, compAppendTailGM1Prog, compAppendTailGM2Prog]

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
  have hres : (Memory.spec 0).clientResult s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b)) = gm 1 := by
    dsimp only [compAppendTailGMGenProg, compAppendTailGM1Prog, compAppendTailGM2Prog,
      cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    simp only [hr_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hr_idx_lt, runClient_state_readCompGMGenProg,
      clientResult_readCompGMGenProg h1_lt, prog_clientResult_pure]
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
    unfold StateTransitionSpec.clientState
    dsimp only [compAppendTailGMGenProg, compAppendTailGM1Prog, compAppendTailGM2Prog,
      cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    simp only [hr_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hr_idx_lt,
      runClient_state_readCompGMGenProg, clientResult_readCompGMGenProg h1_lt,
      prog_clientResult_pure, prog_runClient_state_pure]
    rfl
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

private def CompAppendTailGM2Pre (w : ℕ) :
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

private theorem realizesBounded_compAppendTailGM1 :
    RealizesBounded .exact compAppendTailGM1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
    try simp only [cpTailCap_mk, cpGmTailPtrBase_mk, hr_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hr_idx_lt, clientResult_readCompGMGenProg h1_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrIdx gmTailPtrFlatIdx at *; omega)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase gmRIdx at *
    omega)

private theorem realizesBounded_compAppendTailGM2 :
    RealizesBounded .exact compAppendTailGM2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompAppendTailGM2Pre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
    have hmax_le : maxTailItems N ≤ N := maxTailItems_le N
    have hown_lt := gmTailOwnerIdx_lt hb_pos ht_cap
    try simp only [cpTailCap_mk, cpGmTailOwnerBase_mk, hr_eq, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailOwnerIdx at *; omega)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    have := tailCapPerBucket_le_globalMetaLen hb_pos
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase gmRIdx at *
    omega)

theorem realizesBounded_compAppendTailGMGen :
    RealizesBounded .exact compAppendTailGMGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have h1 := realizesBounded_compAppendTailGM1
  have h2 := realizesBounded_compAppendTailGM2
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    dsimp only
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
      ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
    have hres : (Memory.spec 0).clientResult s
        (compAppendTailGM1Prog ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem (gmRIdx b), compGmAt metaBase U w N s.mem 1) := by
      dsimp only [compAppendTailGM1Prog, cpTailCap_mk, cpGmTailPtrBase_mk]
      simp only [hr_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hr_idx_lt, clientResult_readCompGMGenProg h1_lt,
        runClient_state_readCompGMGenProg, runClient_state_writeCompGMGenProg,
        prog_clientResult_pure]
    have hfr1 : ((Memory.spec 0).clientState s
        (compAppendTailGM1Prog ((mkCompParams U V w N, metaBase), b))).frontier = s.frontier := by
      unfold StateTransitionSpec.clientState
      dsimp only [compAppendTailGM1Prog]
      simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg, runClient_state_writeCompGMGenProg,
        prog_runClient_state_pure]
    rw [hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1.symm ▸ hfr, hb_pos, hb, hr_lt, ht_cap⟩

private def compRemoveTailGMRead1Prog : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let r_del := r_b - 1
    let ptr_del_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + r_del)
    let t_del ← readCompGMGenProg ((cp, metaBase), ptr_del_idx)
    pure (r_del, t_del)

private def compRemoveTailGMRead2Prog : CompParams × ℕ → Memory.Prog (ℕ × ℕ)
  | (cp, metaBase) => do
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    let t_last := n_tails - 1
    let own_last_idx := cpGmTailOwnerBase cp + t_last
    let d_last ← readCompGMGenProg ((cp, metaBase), own_last_idx)
    pure (t_last, d_last)

private def compRemoveTailGMWrite1Prog : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (t_del, d_last)) => do
    writeCompGMGenProg (((cp, metaBase), cpGmTailPtrBase cp + d_last), t_del)
    writeCompGMGenProg (((cp, metaBase), cpGmTailOwnerBase cp + t_del), d_last)

private def compRemoveTailGMWrite2Prog : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (r_del, t_last)) => do
    let r_idx := 4 + (b + b + b) + 1
    writeCompGMGenProg (((cp, metaBase), r_idx), r_del)
    writeCompGMGenProg (((cp, metaBase), 1), t_last)

/-- Remove the last tail descriptor of bucket `b` in compacted `GlobalMeta` (`gmRemoveTail`)
without touching item arrays (`¬ReadsWidth`). -/
def compRemoveTailGMOnlyGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let rt ← compRemoveTailGMRead1Prog ((cp, metaBase), b)
    let td ← compRemoveTailGMRead2Prog (cp, metaBase)
    compRemoveTailGMWrite1Prog ((cp, metaBase), (rt.2, td.2))
    compRemoveTailGMWrite2Prog (((cp, metaBase), b), (rt.1, td.1))

@[simp] theorem memoryCost_compRemoveTailGMOnlyGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compRemoveTailGMOnlyGenProg d) s = 24 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compRemoveTailGMOnlyGenProg, compRemoveTailGMRead1Prog, compRemoveTailGMRead2Prog,
    compRemoveTailGMWrite1Prog, compRemoveTailGMWrite2Prog]

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
    unfold StateTransitionSpec.clientState
    dsimp only [compRemoveTailGMOnlyGenProg, compRemoveTailGMRead1Prog, compRemoveTailGMRead2Prog,
      compRemoveTailGMWrite1Prog, compRemoveTailGMWrite2Prog,
      cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
    simp only [hr_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hr_idx_lt,
      runClient_state_readCompGMGenProg, clientResult_readCompGMGenProg hptr_del_lt,
      clientResult_readCompGMGenProg h1_lt, clientResult_readCompGMGenProg hown_last_lt,
      prog_clientResult_pure, prog_runClient_state_pure]
    rfl
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

/-- Precondition for removing only the tail of global metadata. -/
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

private def CompRemoveTailGMRead2Pre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      1 ≤ compGmAt metaBase U w N s.mem 1 ∧
      compGmAt metaBase U w N s.mem 1 ≤ maxTailItems N

private def CompRemoveTailGMWrite1Pre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (t_del, d_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      t_del < maxTailItems N ∧
      d_last < maxTailItems N

private def CompRemoveTailGMWrite2Pre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (_r_del, _t_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N

private theorem realizesBounded_compRemoveTailGMRead1 :
    RealizesBounded .exact compRemoveTailGMRead1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hptr_del_lt := gmTailPtrIdx_lt hb_pos hb hr_del_cap
    try simp only [cpTailCap_mk, cpGmTailPtrBase_mk, hr_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hr_idx_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrIdx gmTailPtrFlatIdx at *; omega)
  all_goals try omega
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase gmRIdx at *
    omega)

private theorem realizesBounded_compRemoveTailGMRead2 :
    RealizesBounded .exact compRemoveTailGMRead2Prog
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailGMRead2Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, h1_pos, h1_le⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hown_lt := gmTailOwnerIdx_lt hb_pos (by omega : compGmAt metaBase U w N s.mem 1 - 1 < _)
    try simp only [cpGmTailOwnerBase_mk, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg h1_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailOwnerIdx at *; omega)
  all_goals try omega
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailOwnerIdx gmTailOwnerBase at *
    omega)

private theorem realizesBounded_compRemoveTailGMWrite1 :
    RealizesBounded .exact compRemoveTailGMWrite1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      CompRemoveTailGMWrite1Pre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨t_del, d_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, ht_del_lt, hd_last_lt⟩ := h
    have hptr_last_lt := gmTailPtrFlatIdx_lt hb_pos hd_last_lt
    have hown_del_lt := gmTailOwnerIdx_lt hb_pos ht_del_lt
    try simp only [cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrFlatIdx gmTailOwnerIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase at *
    omega)

private theorem realizesBounded_compRemoveTailGMWrite2 :
    RealizesBounded .exact compRemoveTailGMWrite2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompRemoveTailGMWrite2Pre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_del, t_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at *; omega)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmRIdx at *
    omega)

theorem realizesBounded_compRemoveTailGMOnlyGen :
    RealizesBounded .exact compRemoveTailGMOnlyGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hr1 := realizesBounded_compRemoveTailGMRead1
  have hr2 := realizesBounded_compRemoveTailGMRead2
  have hw1 := realizesBounded_compRemoveTailGMWrite1
  have hw2 := realizesBounded_compRemoveTailGMWrite2
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    dsimp only
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hst1 : (Memory.spec 0).clientState s
        (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compRemoveTailGMRead1Prog]; simp
    rw [hst1]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, by omega, htail.ntails_le⟩
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    dsimp only
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
    have hst1 : (Memory.spec 0).clientState s
        (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compRemoveTailGMRead1Prog]; simp
    have hst2 : (Memory.spec 0).clientState s
        (compRemoveTailGMRead2Prog (mkCompParams U V w N, metaBase)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compRemoveTailGMRead2Prog]; simp
    have hres1 : ((Memory.spec 0).clientResult s
        (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b))).2 =
        compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) := by
      dsimp only [compRemoveTailGMRead1Prog, cpTailCap_mk, cpGmTailPtrBase_mk]
      simp only [hr_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hr_idx_lt, clientResult_readCompGMGenProg hptr_del_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    have hres2 : ((Memory.spec 0).clientResult s
        (compRemoveTailGMRead2Prog (mkCompParams U V w N, metaBase))).2 =
        compGmAt metaBase U w N s.mem
          (gmTailOwnerIdx N (compGmAt metaBase U w N s.mem 1 - 1)) := by
      dsimp only [compRemoveTailGMRead2Prog, cpGmTailOwnerBase_mk]
      simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg h1_lt, clientResult_readCompGMGenProg hown_last_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    rw [hst1, hst2, hres1, hres2]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos,
      lt_of_lt_of_le (htail.ptr_lt b hb _ hr_del_lt) htail.ntails_le,
      htail.owner_lt_maxTailItems ht_last_lt⟩
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, _⟩ := h
    dsimp only
    have hfr_eq : ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b)))
          (compRemoveTailGMRead2Prog (mkCompParams U V w N, metaBase)))
        (compRemoveTailGMWrite1Prog ((mkCompParams U V w N, metaBase),
          (((Memory.spec 0).clientResult s
              (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b))).2,
           ((Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s
                (compRemoveTailGMRead1Prog ((mkCompParams U V w N, metaBase), b)))
              (compRemoveTailGMRead2Prog (mkCompParams U V w N, metaBase))).2)))).frontier =
        s.frontier := by
      unfold StateTransitionSpec.clientState
      dsimp only [compRemoveTailGMRead1Prog, compRemoveTailGMRead2Prog, compRemoveTailGMWrite1Prog]
      simp
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr_eq.symm ▸ hfr, hb_pos, hb⟩

private def compGmPushSlabInitAReadProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let b3 := b + b + b
    let q_b ← readCompGMGenProg ((cp, metaBase), 4 + b3)
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    pure (q_b, p_new)

private def compGmPushSlabInitW1Prog : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (q_b, p_new)) => do
    let p2 := p_new + p_new
    let ownB_idx := cpGmSlabMetaBase cp + (p2 + p2)
    writeCompGMGenProg (((cp, metaBase), ownB_idx), b)
    writeCompGMGenProg (((cp, metaBase), ownB_idx + 1), q_b)

private def compGmPushSlabInitAProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let qp ← compGmPushSlabInitAReadProg ((cp, metaBase), b)
    compGmPushSlabInitW1Prog (((cp, metaBase), b), qp)

private def compGmPushSlabInitBReadProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let b3 := b + b + b
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    let top_old ← readCompGMGenProg ((cp, metaBase), 4 + b3 + 2)
    pure (p_new, top_old)

private def compGmPushSlabInitBWProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (p_new, top_old)) => do
    let p2 := p_new + p_new
    let bel_idx := cpGmSlabMetaBase cp + (p2 + p2) + 2
    writeCompGMGenProg (((cp, metaBase), bel_idx), top_old)
    let q_b ← readCompGMGenProg ((cp, metaBase), 4 + (b + b + b))
    if 0 < q_b then do
      let t2 := top_old + top_old
      let abv_idx := cpGmSlabMetaBase cp + (t2 + t2) + 3
      writeCompGMGenProg (((cp, metaBase), abv_idx), p_new)
    else pure ()

private def compGmPushSlabInitBProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let pt ← compGmPushSlabInitBReadProg ((cp, metaBase), b)
    compGmPushSlabInitBWProg (((cp, metaBase), b), pt)

/-- First stage of `compGmPushSlabGenProg`: initializes slab metadata
`(ownerB, ownerS, below, above_of_old_top)` (`¬ReadsWidth`). -/
def compGmPushSlabInitProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | d => do
    compGmPushSlabInitAProg d
    compGmPushSlabInitBProg d

private def compGmPushSlabFinish1Prog : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let q_idx := 4 + (b + b + b)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    (if q_b < cpDirSlabs cp then do
      let dir_idx := cpGmSlabDirBase cp + b * cpDirSlabs cp + q_b
      writeCompGMGenProg (((cp, metaBase), dir_idx), p_new)
    else pure ()) >>= fun _ => pure (q_b, p_new)

private def compGmPushSlabFinish2Prog : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (q_b, p_new)) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let top_idx := 4 + b3 + 2
    writeCompGMGenProg (((cp, metaBase), top_idx), p_new)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b + 1)
    writeCompGMGenProg (((cp, metaBase), 0), p_new + 1)

/-- Second stage of `compGmPushSlabGenProg`: reads `(q_b, p_new)` and updates directory,
`slabTop`, `q_b`, and `gm 0`. -/
def compGmPushSlabFinishProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let qp ← compGmPushSlabFinish1Prog ((cp, metaBase), b)
    compGmPushSlabFinish2Prog (((cp, metaBase), b), qp)

/-- Push a new full slab `p_new = gm 0` onto bucket `b` in compacted `GlobalMeta` (`gmPushSlab`,
`¬ReadsWidth`). -/
def compGmPushSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    compGmPushSlabInitProg ((cp, metaBase), b)
    compGmPushSlabFinishProg ((cp, metaBase), b)

theorem memoryCost_compGmPushSlabInitProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPushSlabInitProg d) s ≤ 26 := by
  have hA : ∀ s0, memoryCost (compGmPushSlabInitAProg d) s0 = 12 := by
    intro s0; rcases d with ⟨⟨cp, metaBase⟩, b⟩
    simp [compGmPushSlabInitAProg, compGmPushSlabInitAReadProg, compGmPushSlabInitW1Prog]
  have hB : ∀ s0, memoryCost (compGmPushSlabInitBProg d) s0 ≤ 14 := by
    intro s0; rcases d with ⟨⟨cp, metaBase⟩, b⟩
    dsimp only [compGmPushSlabInitBProg, compGmPushSlabInitBReadProg, compGmPushSlabInitBWProg]
    simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      prog_clientResult_bind, prog_clientResult_pure]
    split_ifs <;> simp
  dsimp only [compGmPushSlabInitProg]
  rw [Realization.memoryCost_bind', hA]
  have := hB ((Memory.spec 0).clientState s (compGmPushSlabInitAProg d))
  omega

theorem memoryCost_compGmPushSlabFinishProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPushSlabFinishProg d) s ≤ 20 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPushSlabFinishProg, compGmPushSlabFinish1Prog, compGmPushSlabFinish2Prog]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg, prog_clientResult_bind,
    prog_clientResult_pure]
  split_ifs <;> simp

theorem memoryCost_compGmPushSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPushSlabGenProg d) s ≤ 46 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPushSlabGenProg]
  rw [Realization.memoryCost_bind']
  have h1 := memoryCost_compGmPushSlabInitProg_le ((cp, metaBase), b) s
  have h2 := memoryCost_compGmPushSlabFinishProg_le ((cp, metaBase), b)
    ((Memory.spec 0).clientState s (compGmPushSlabInitProg ((cp, metaBase), b)))
  omega

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

/-- Precondition for finishing a slab push in global metadata. -/
@[expose] def CompGmPushSlabFinishPre (w : ℕ) :
    (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      compGmAt metaBase U w N s.mem (gmQIdx b) ≤ compGmAt metaBase U w N s.mem 0 ∧
      compGmAt metaBase U w N s.mem 0 < maxFullSlabs N

private theorem compGmPushSlabInitAProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hp_lt : compGmAt metaBase U w N s.mem 0 < maxFullSlabs N) :
    let gm := compGmAt metaBase U w N s.mem
    let s₁ := (Memory.spec 0).clientState s
      (compGmPushSlabInitAProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s₁ ∧
    compGmAt metaBase U w N s₁.mem =
      Function.update
        (Function.update gm (gmSlabOwnerBIdx N (gm 0)) b)
        (gmSlabOwnerSIdx N (gm 0)) (gm (gmQIdx b)) := by
  intro gm s₁
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have hownB_lt : gmSlabOwnerBIdx N (gm 0) < globalMetaLen N := gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : gmSlabOwnerSIdx N (gm 0) < globalMetaLen N := gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hb_val : b < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by unfold gmQIdx at hq_idx_lt; omega)
  have hq_val : gm (gmQIdx b) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hp4 : gmSlabMetaBase N +
      (compGmAt metaBase U w N s.mem 0 + compGmAt metaBase U w N s.mem 0 +
        (compGmAt metaBase U w N s.mem 0 + compGmAt metaBase U w N s.mem 0)) =
      gmSlabOwnerBIdx N (gm 0) := by dsimp only [gm]; unfold gmSlabOwnerBIdx; omega
  have hownS_eq : gmSlabOwnerBIdx N (gm 0) + 1 = gmSlabOwnerSIdx N (gm 0) := rfl
  have hst : s₁ = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabOwnerBIdx N (gm 0)), b)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabOwnerSIdx N (gm 0)), gm (gmQIdx b))) := by
    change (Memory.spec 0).clientState s _ = _
    unfold StateTransitionSpec.clientState
    dsimp only [compGmPushSlabInitAProg, compGmPushSlabInitAReadProg,
      compGmPushSlabInitW1Prog, cpGmSlabMetaBase_mk, gm]
    simp only [hq_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hq_idx_lt,
      clientResult_readCompGMGenProg h0_lt, runClient_state_readCompGMGenProg,
      prog_clientResult_pure, prog_runClient_state_pure]
    dsimp only [gm] at hp4 hownS_eq
    simp only [hp4, hownS_eq]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_lt
    hb_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_lt
    hq_val _
  rw [hst]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1]

private theorem compGmPushSlabInitBProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hp_lt : compGmAt metaBase U w N s.mem 0 < maxFullSlabs N)
    (htop_cond : 0 < compGmAt metaBase U w N s.mem (gmQIdx b) →
      compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N) :
    let gm := compGmAt metaBase U w N s.mem
    let s₁ := (Memory.spec 0).clientState s
      (compGmPushSlabInitBProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s₁ ∧
    compGmAt metaBase U w N s₁.mem =
      (let gm1 := Function.update gm (gmSlabBelowIdx N (gm 0)) (gm (gmSlabTopIdx b))
        if 0 < gm (gmQIdx b) then
          Function.update gm1 (gmSlabAboveIdx N (gm (gmSlabTopIdx b))) (gm 0)
        else gm1) := by
  intro gm s₁
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have hbel_lt : gmSlabBelowIdx N (gm 0) < globalMetaLen N := gmSlabBelowIdx_lt hb_pos hp_lt
  have habv_lt : 0 < gm (gmQIdx b) → gmSlabAboveIdx N (gm (gmSlabTopIdx b)) < globalMetaLen N :=
    fun hq_pos => gmSlabAboveIdx_lt hb_pos (htop_cond hq_pos)
  have hp_val : gm 0 < 2 ^ globalPtrBits N := compGmAt_lt ..
  have htop_val : gm (gmSlabTopIdx b) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hp4 : gmSlabMetaBase N +
      ((compGmAt metaBase U w N s.mem 0 + compGmAt metaBase U w N s.mem 0) +
        (compGmAt metaBase U w N s.mem 0 + compGmAt metaBase U w N s.mem 0)) + 2 =
      gmSlabBelowIdx N (gm 0) := by dsimp only [gm]; unfold gmSlabBelowIdx; omega
  have ht4 : gmSlabMetaBase N +
      ((compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) +
        (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 3 =
      gmSlabAboveIdx N (gm (gmSlabTopIdx b)) := by dsimp only [gm]; unfold gmSlabAboveIdx; omega
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_lt
    htop_val s
  let s_bel := (Memory.spec 0).clientState s
    (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
      gmSlabBelowIdx N (gm 0)), gm (gmSlabTopIdx b)))
  have hsbel_q : compGmAt metaBase U w N s_bel.mem (gmQIdx b) = gm (gmQIdx b) := by
    rw [hg1, Function.update_of_ne
      (by unfold gmQIdx gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
          omega)]
  have hst : s₁ = (Memory.spec 0).clientState s_bel
      (if 0 < gm (gmQIdx b) then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N (gm (gmSlabTopIdx b))), gm 0)
      else pure ()) := by
    change (Memory.spec 0).clientState s _ = _
    unfold StateTransitionSpec.clientState
    dsimp only [compGmPushSlabInitBProg, compGmPushSlabInitBReadProg,
      compGmPushSlabInitBWProg, cpGmSlabMetaBase_mk, gm]
    simp only [hq_eq, htop_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      clientResult_readCompGMGenProg htop_idx_lt, runClient_state_readCompGMGenProg,
      prog_clientResult_pure, prog_runClient_state_pure]
    dsimp only [gm] at hp4 ht4 hsbel_q
    simp only [hp4, ht4, clientResult_readCompGMGenProg hq_idx_lt]
    change ((Memory.spec 0).runClient s_bel
      (if 0 < compGmAt metaBase U w N s_bel.mem (gmQIdx b) then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b))),
          compGmAt metaBase U w N s.mem 0)
      else pure ())).2.1 = _
    rw [hsbel_q]
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items) (0 < gm (gmQIdx b))
    hw hitem habv_lt (fun _ => hp_val) s_bel
  rw [hst]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1]

theorem compGmPushSlabInitProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hp_lt : compGmAt metaBase U w N s.mem 0 < maxFullSlabs N) :
    let gm := compGmAt metaBase U w N s.mem
    let s₁ := (Memory.spec 0).clientState s
      (compGmPushSlabInitProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s₁ ∧
    compGmAt metaBase U w N s₁.mem =
      (let gm3 := Function.update
          (Function.update
            (Function.update gm (gmSlabOwnerBIdx N (gm 0)) b)
            (gmSlabOwnerSIdx N (gm 0)) (gm (gmQIdx b)))
          (gmSlabBelowIdx N (gm 0)) (gm (gmSlabTopIdx b))
        if 0 < gm (gmQIdx b) then
          Function.update gm3 (gmSlabAboveIdx N (gm (gmSlabTopIdx b))) (gm 0)
        else gm3) := by
  intro gm s₁
  obtain ⟨hfA, hgA⟩ := compGmPushSlabInitAProg_effect (m_items := m_items) hw hitem hb_pos hb s
    hp_lt
  let sA := (Memory.spec 0).clientState s
    (compGmPushSlabInitAProg ((mkCompParams U V w N, metaBase), b))
  have hgA_0 : compGmAt metaBase U w N sA.mem 0 = gm 0 := by
    rw [hgA, Function.update_of_ne
        (by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
            omega),
      Function.update_of_ne
        (by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
            omega)]
  have hgA_q : compGmAt metaBase U w N sA.mem (gmQIdx b) = gm (gmQIdx b) := by
    rw [hgA, Function.update_of_ne
        (by unfold gmQIdx gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
            omega),
      Function.update_of_ne
        (by unfold gmQIdx gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
            omega)]
  have hgA_top : compGmAt metaBase U w N sA.mem (gmSlabTopIdx b) = gm (gmSlabTopIdx b) := by
    rw [hgA, Function.update_of_ne
        (by unfold gmSlabTopIdx gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase
              gmTailPtrBase gmSlabDirBase; omega),
      Function.update_of_ne
        (by unfold gmSlabTopIdx gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase
              gmTailPtrBase gmSlabDirBase; omega)]
  obtain ⟨hfB, hgB⟩ := compGmPushSlabInitBProg_effect (m_items := m_items) hw hitem hb_pos hb sA
    (hgA_0.symm ▸ hp_lt)
    (by rw [hgA_q, hgA_top]; exact fun hq_pos => (hslab.top_lt hb hq_pos).trans hp_lt)
  dsimp only [s₁, compGmPushSlabInitProg]
  rw [StateTransitionSpec.clientState_bind]
  refine ⟨hfA.trans hfB, ?_⟩
  rw [hgB]; dsimp only
  rw [hgA_0, hgA_q, hgA_top, hgA]

private def CompGmPushSlabInitBPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      compGmAt metaBase U w N s.mem 0 < maxFullSlabs N ∧
      (0 < compGmAt metaBase U w N s.mem (gmQIdx b) →
        compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N)

private def CompGmPushSlabInitW1Pre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), _b), (_q_b, p_new)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_new < maxFullSlabs N

private def CompGmPushSlabInitBWPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (p_new, top_old)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      p_new < maxFullSlabs N ∧
      (0 < compGmAt metaBase U w N s.mem (gmQIdx b) → top_old < maxFullSlabs N)

private theorem realizesBounded_compGmPushSlabInitARead :
    RealizesBounded .exact compGmPushSlabInitAReadProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, _⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmQIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx at *
    omega)

private theorem realizesBounded_compGmPushSlabInitW1 :
    RealizesBounded .exact compGmPushSlabInitW1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabInitW1Pre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨q_b, p_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt⟩ := h
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_lt
    have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_lt
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabOwnerBIdx gmSlabOwnerSIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabOwnerSIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmPushSlabInitA :
    RealizesBounded .exact compGmPushSlabInitAProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hr := realizesBounded_compGmPushSlabInitARead
  have hw1 := realizesBounded_compGmPushSlabInitW1
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, hp_lt⟩ := h
    dsimp only
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hst : (Memory.spec 0).clientState s
        (compGmPushSlabInitAReadProg ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmPushSlabInitAReadProg]; simp
    have hres : (Memory.spec 0).clientResult s
        (compGmPushSlabInitAReadProg ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem (gmQIdx b), compGmAt metaBase U w N s.mem 0) := by
      dsimp only [compGmPushSlabInitAReadProg]
      simp only [hq_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hq_idx_lt, clientResult_readCompGMGenProg h0_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
    rw [hst, hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt⟩

private theorem realizesBounded_compGmPushSlabInitBRead :
    RealizesBounded .exact compGmPushSlabInitBReadProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompGmPushSlabInitBPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, _⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabTopIdx gmQIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *
    omega)

private theorem realizesBounded_compGmPushSlabInitBW :
    RealizesBounded .exact compGmPushSlabInitBWProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabInitBWPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, _⟩ := h
    have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) + 2 =
        gmSlabBelowIdx N p_new := by unfold gmSlabBelowIdx; omega
    have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_lt
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    simp only [cpGmSlabMetaBase_mk, hp4]; exact hbel_lt.le
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, _⟩ := h
    have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) + 2 =
        gmSlabBelowIdx N p_new := by unfold gmSlabBelowIdx; omega
    have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_lt
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpGmSlabMetaBase_mk, cpN_mk, hp4]; exact hbel_lt
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, _⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    rw [hq_eq]; exact hq_idx_lt.le
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, _⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hfr' : metaBase + offCompItems U w N ≤
        ((Memory.spec 0).clientState s
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            cpGmSlabMetaBase (mkCompParams U V w N) + (p_new + p_new + (p_new + p_new)) + 2),
            top_old))).frontier := by
      rw [clientState_writeCompGMGenProg]; exact hfr
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr'⟩, ?_⟩
    simp only [cpN_mk, hq_eq]; exact hq_idx_lt
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, htop_cond⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have ht4 : gmSlabMetaBase N + (top_old + top_old + (top_old + top_old)) + 3 =
        gmSlabAboveIdx N top_old := by unfold gmSlabAboveIdx; omega
    have hres_q : (Memory.spec 0).clientResult
        ((Memory.spec 0).clientState s
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            cpGmSlabMetaBase (mkCompParams U V w N) + (p_new + p_new + (p_new + p_new)) + 2),
            top_old)))
        (readCompGMGenProg ((mkCompParams U V w N, metaBase), 4 + (b + b + b))) =
        compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [clientResult_readCompGMGenProg (by rw [hq_eq]; exact hq_idx_lt),
        clientState_writeCompGMGenProg]
      dsimp only
      unfold compGmAt
      rw [hq_eq]
      simp only [hq_idx_lt, ↓reduceIte]
      apply readPacked_writePacked_of_ne hw
      rw [cpGmSlabMetaBase_mk]
      unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
      omega
    rw [hres_q] at hc
    have habv_lt := gmSlabAboveIdx_lt hb_pos (htop_cond hc)
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    simp only [cpGmSlabMetaBase_mk, ht4]; exact habv_lt.le
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, htop_cond⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have ht4 : gmSlabMetaBase N + (top_old + top_old + (top_old + top_old)) + 3 =
        gmSlabAboveIdx N top_old := by unfold gmSlabAboveIdx; omega
    have hfr'' : metaBase + offCompItems U w N ≤
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              cpGmSlabMetaBase (mkCompParams U V w N) + (p_new + p_new + (p_new + p_new)) + 2),
              top_old)))
          (readCompGMGenProg ((mkCompParams U V w N, metaBase), 4 + (b + b + b)))).frontier := by
      rw [clientState_readCompGMGenProg, clientState_writeCompGMGenProg]; exact hfr
    have hres_q : (Memory.spec 0).clientResult
        ((Memory.spec 0).clientState s
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            cpGmSlabMetaBase (mkCompParams U V w N) + (p_new + p_new + (p_new + p_new)) + 2),
            top_old)))
        (readCompGMGenProg ((mkCompParams U V w N, metaBase), 4 + (b + b + b))) =
        compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [clientResult_readCompGMGenProg (by rw [hq_eq]; exact hq_idx_lt),
        clientState_writeCompGMGenProg]
      dsimp only
      unfold compGmAt
      rw [hq_eq]
      simp only [hq_idx_lt, ↓reduceIte]
      apply readPacked_writePacked_of_ne hw
      rw [cpGmSlabMetaBase_mk]
      unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
      omega
    rw [hres_q] at hc
    have habv_lt := gmSlabAboveIdx_lt hb_pos (htop_cond hc)
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr''⟩, ?_⟩
    simp only [cpGmSlabMetaBase_mk, cpN_mk, ht4]; exact habv_lt

private theorem realizesBounded_compGmPushSlabInitB :
    RealizesBounded .exact compGmPushSlabInitBProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabInitBPre (fun _ _ => 0) := by
  have hr := realizesBounded_compGmPushSlabInitBRead
  have hbw := realizesBounded_compGmPushSlabInitBW
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, htop_cond⟩ := h
    dsimp only
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
    have hst : (Memory.spec 0).clientState s
        (compGmPushSlabInitBReadProg ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmPushSlabInitBReadProg]; simp
    have hres : (Memory.spec 0).clientResult s
        (compGmPushSlabInitBReadProg ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
      dsimp only [compGmPushSlabInitBReadProg]
      simp only [htop_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg h0_lt, clientResult_readCompGMGenProg htop_idx_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
    rw [hst, hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hp_lt, htop_cond⟩

theorem realizesBounded_compGmPushSlabInit :
    RealizesBounded .exact compGmPushSlabInitProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hA := realizesBounded_compGmPushSlabInitA
  have hB := realizesBounded_compGmPushSlabInitB
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw_pos, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    obtain ⟨hfA, hgA⟩ := compGmPushSlabInitAProg_effect
      (itemBase := metaBase + offCompItems U w N) (m_items := 0) hw_pos le_rfl hb_pos hb s hp_lt
    have hgA_0 : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compGmPushSlabInitAProg ((mkCompParams U V w N, metaBase), b))).mem 0 =
        compGmAt metaBase U w N s.mem 0 := by
      rw [hgA, Function.update_of_ne
          (by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
              omega),
        Function.update_of_ne
          (by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
              omega)]
    have hgA_q : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compGmPushSlabInitAProg ((mkCompParams U V w N, metaBase), b))).mem (gmQIdx b) =
        compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hgA, Function.update_of_ne
          (by unfold gmQIdx gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase
                gmTailPtrBase gmSlabDirBase; omega),
        Function.update_of_ne
          (by unfold gmQIdx gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase
                gmTailPtrBase gmSlabDirBase; omega)]
    have hgA_top : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compGmPushSlabInitAProg ((mkCompParams U V w N, metaBase), b))).mem (gmSlabTopIdx b) =
        compGmAt metaBase U w N s.mem (gmSlabTopIdx b) := by
      rw [hgA, Function.update_of_ne
          (by unfold gmSlabTopIdx gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase
                gmTailPtrBase gmSlabDirBase; omega),
        Function.update_of_ne
          (by unfold gmSlabTopIdx gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase
                gmTailPtrBase gmSlabDirBase; omega)]
    refine ⟨U, V, N, hw_pos, hN, hnU, hU, hV, rfl, hfA.frontier_eq.symm ▸ hfr, hb_pos, hb, ?_, ?_⟩
    · rw [hgA_0]; exact hp_lt
    · rw [hgA_q, hgA_top]; exact fun hq_pos => (hslab.top_lt hb hq_pos).trans hp_lt

private def CompGmPushSlabFinish2Pre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (q_b, p_new)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      q_b ≤ p_new ∧
      p_new < maxFullSlabs N

private theorem realizesBounded_compGmPushSlabFinish1 :
    RealizesBounded .exact compGmPushSlabFinish1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompGmPushSlabFinishPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, _⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [cpDirSlabs_mk, cpGmSlabDirBase_mk, hq_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals try (
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hc
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
  all_goals try (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx at *
    omega)
  all_goals (
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hc
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabDirIdx gmSlabDirBase at *
    omega)

private theorem realizesBounded_compGmPushSlabFinish2 :
    RealizesBounded .exact compGmPushSlabFinish2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabFinish2Pre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨q_b, p_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
    try simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmQIdx gmSlabTopIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx gmSlabTopIdx at *
    omega)

theorem realizesBounded_compGmPushSlabFinish :
    RealizesBounded .exact compGmPushSlabFinishProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushSlabFinishPre (fun _ _ => 0) := by
  have hf1 := realizesBounded_compGmPushSlabFinish1
  have hf2 := realizesBounded_compGmPushSlabFinish2
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt⟩ := h
    dsimp only
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hres : (Memory.spec 0).clientResult s
        (compGmPushSlabFinish1Prog ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem (gmQIdx b), compGmAt metaBase U w N s.mem 0) := by
      dsimp only [compGmPushSlabFinish1Prog, cpDirSlabs_mk, cpGmSlabDirBase_mk]
      simp only [hq_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hq_idx_lt, clientResult_readCompGMGenProg h0_lt,
        runClient_state_readCompGMGenProg]
      split_ifs <;> simp
    have hfr1 : ((Memory.spec 0).clientState s
        (compGmPushSlabFinish1Prog ((mkCompParams U V w N, metaBase), b))).frontier =
        s.frontier := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmPushSlabFinish1Prog]
      simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg]
      split_ifs <;> simp
    rw [hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1.symm ▸ hfr, hb_pos, hb, hq_le_p, hp_lt⟩

private theorem gmPushSlabInit_preserves_header {N b : ℕ} (hb : b < numBuckets N)
    (gm : ℕ → ℕ) :
    let gm3 := Function.update
      (Function.update
        (Function.update gm (gmSlabOwnerBIdx N (gm 0)) b)
        (gmSlabOwnerSIdx N (gm 0)) (gm (gmQIdx b)))
      (gmSlabBelowIdx N (gm 0)) (gm (gmSlabTopIdx b))
    let gm₁ := if 0 < gm (gmQIdx b) then
        Function.update gm3 (gmSlabAboveIdx N (gm (gmSlabTopIdx b))) (gm 0)
      else gm3
    gm₁ (gmQIdx b) = gm (gmQIdx b) ∧ gm₁ 0 = gm 0 := by
  intro gm3 gm₁
  have hB : gmSlabDirBase N ≤ gmSlabOwnerBIdx N (gm 0) := by
    unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hS : gmSlabDirBase N ≤ gmSlabOwnerSIdx N (gm 0) := by
    unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hBel : gmSlabDirBase N ≤ gmSlabBelowIdx N (gm 0) := by
    unfold gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hAbv : gmSlabDirBase N ≤ gmSlabAboveIdx N (gm (gmSlabTopIdx b)) := by
    unfold gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hq_lt_dir : gmQIdx b < gmSlabDirBase N := by
    unfold gmQIdx gmSlabDirBase; omega
  have h0_lt_dir : 0 < gmSlabDirBase N := by unfold gmSlabDirBase; omega
  have hgm3_q : gm3 (gmQIdx b) = gm (gmQIdx b) := by
    dsimp only [gm3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hgm3_0 : gm3 0 = gm 0 := by
    dsimp only [gm3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  dsimp only [gm₁]
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [Function.update_of_ne (by omega), hgm3_q]
    · rw [Function.update_of_ne (by omega), hgm3_0]
  · exact ⟨hgm3_q, hgm3_0⟩

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
  obtain ⟨hf1, hg1⟩ :=
    compGmPushSlabInitProg_effect (m_items := m_items) hw hitem hb_pos hb s hslab hp_lt
  let s₁ := (Memory.spec 0).clientState s
    (compGmPushSlabInitProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨hgm1_q, hgm1_0⟩ := gmPushSlabInit_preserves_header hb gm
  have hs1_q : compGmAt metaBase U w N s₁.mem (gmQIdx b) = gm (gmQIdx b) := by
    rw [hg1]; exact hgm1_q
  have hs1_0 : compGmAt metaBase U w N s₁.mem 0 = gm 0 := by
    rw [hg1]; exact hgm1_0
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have hdir_lt : gm (gmQIdx b) < dirSlabsPerBucket N →
      gmSlabDirIdx N b (gm (gmQIdx b)) < globalMetaLen N :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb hdir
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hq_le_p : compGmAt metaBase U w N s.mem (gmQIdx b) ≤ compGmAt metaBase U w N s.mem 0 :=
    q_le_nslabs_of_slabBijection hslab hb
  have hp_val : gm 0 < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hq1_val : gm (gmQIdx b) + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm]; omega)
  have hp1_val : gm 0 + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm]; omega)
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s₁
            (if gm (gmQIdx b) < dirSlabsPerBucket N then
              writeCompGMGenProg (((mkCompParams U V w N, metaBase),
                gmSlabDirIdx N b (gm (gmQIdx b))), gm 0)
            else pure ()))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b), gm 0)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmQIdx b), gm (gmQIdx b) + 1)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm 0 + 1)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmPushSlabGenProg]
    rw [StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₁
      (compGmPushSlabFinishProg ((mkCompParams U V w N, metaBase), b)) = _
    unfold StateTransitionSpec.clientState
    dsimp only [compGmPushSlabFinishProg, compGmPushSlabFinish1Prog, compGmPushSlabFinish2Prog,
      cpDirSlabs_mk, cpGmSlabDirBase_mk, gmSlabDirIdx, gm]
    dsimp only [gm] at hs1_q hs1_0
    simp only [hq_eq, htop_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hq_idx_lt,
      clientResult_readCompGMGenProg h0_lt, runClient_state_readCompGMGenProg, hs1_q, hs1_0]
    split_ifs <;> simp
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (gm (gmQIdx b) < dirSlabsPerBucket N) hw hitem hdir_lt (fun _ => hp_val) s₁
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem htop_idx_lt
    hp_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hq_idx_lt
    hq1_val _
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
    hp1_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans (hf4.trans hf5))), ?_⟩
  rw [hg5, hg4, hg3, hg2, hg1]; rfl

theorem realizesBounded_compGmPushSlabGen :
    RealizesBounded .exact compGmPushSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hinit := realizesBounded_compGmPushSlabInit
  have hfin := realizesBounded_compGmPushSlabFinish
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    obtain ⟨hf1, hg1⟩ :=
      compGmPushSlabInitProg_effect (itemBase := metaBase + offCompItems U w N) (m_items := 0)
        hw le_rfl hb_pos hb s hslab hp_lt
    obtain ⟨hgm1_q, hgm1_0⟩ := gmPushSlabInit_preserves_header hb (compGmAt metaBase U w N s.mem)
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr, hb_pos, hb, ?_, ?_⟩
    · change compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compGmPushSlabInitProg ((mkCompParams U V w N, metaBase), b))).mem (gmQIdx b) ≤
        compGmAt metaBase U w N
          ((Memory.spec 0).clientState s
            (compGmPushSlabInitProg ((mkCompParams U V w N, metaBase), b))).mem 0
      rw [hg1, hgm1_q, hgm1_0]
      exact q_le_nslabs_of_slabBijection hslab hb
    · change compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compGmPushSlabInitProg ((mkCompParams U V w N, metaBase), b))).mem 0 < maxFullSlabs N
      rw [hg1, hgm1_0]
      exact hp_lt

private def compGmUnlinkTop1Prog : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let top_idx := 4 + (b + b + b) + 2
    let p_del ← readCompGMGenProg ((cp, metaBase), top_idx)
    let p2 := p_del + p_del
    let bel_idx := cpGmSlabMetaBase cp + (p2 + p2) + 2
    let bel_del ← readCompGMGenProg ((cp, metaBase), bel_idx)
    writeCompGMGenProg (((cp, metaBase), top_idx), bel_del)
    pure p_del

private def compGmUnlinkTop2Prog : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, metaBase), b), p_del) => do
    let q_idx := 4 + (b + b + b)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b - 1)
    pure p_del

/-- Unlink top slab of bucket `b` in compacted `GlobalMeta` (`gmUnlinkTopSlab`). -/
def compGmUnlinkTopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let p_del ← compGmUnlinkTop1Prog ((cp, metaBase), b)
    compGmUnlinkTop2Prog (((cp, metaBase), b), p_del)

private def compGmRelinkMovedReadProg : CompParams × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (cp, (metaBase, p_last)) => do
    let pl2 := p_last + p_last
    let ownB_idx := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_idx)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_idx + 1)
    pure (b_last, s_last)

private def compGmRelinkMovedW1Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), (b_last, s_last)) =>
    if s_last < cpDirSlabs cp then do
      let dir_idx := cpGmSlabDirBase cp + b_last * cpDirSlabs cp + s_last
      writeCompGMGenProg (((cp, metaBase), dir_idx), p_del)
    else pure ()

private def compGmRelinkMovedW2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), (b_last, s_last)) => do
    let b3 := b_last + b_last + b_last
    let q_last ← readCompGMGenProg ((cp, metaBase), 4 + b3)
    if s_last + 1 = q_last then
      writeCompGMGenProg (((cp, metaBase), 4 + b3 + 2), p_del)
    else pure ()

/-- Relink directory and top pointer of moved slab `p_last` into `p_del` (`gmRelinkMovedSlab`). -/
def compGmRelinkMovedSlabGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let bs ← compGmRelinkMovedReadProg (cp, (metaBase, p_last))
    compGmRelinkMovedW1Prog (((cp, metaBase), p_del), bs)
    compGmRelinkMovedW2Prog (((cp, metaBase), p_del), bs)

private def compGmLinkMovedRead1Prog : CompParams × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (cp, (metaBase, p_last)) => do
    let pl2 := p_last + p_last
    let ownB_last := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_last)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 1)
    pure (b_last, s_last)

private def compGmLinkMovedRead2Prog : CompParams × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (cp, (metaBase, p_last)) => do
    let pl2 := p_last + p_last
    let ownB_last := cpGmSlabMetaBase cp + (pl2 + pl2)
    let bel_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 2)
    let abv_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 3)
    pure (bel_last, abv_last)

private def compGmLinkMovedS1ReadProg : CompParams × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (cp, (metaBase, p_last)) => do
    let pl2 := p_last + p_last
    let ownB_last := cpGmSlabMetaBase cp + (pl2 + pl2)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 1)
    let bel_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 2)
    pure (s_last, bel_last)

private def compGmLinkMovedUpdBelProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), (s_last, bel_last)) =>
    if 0 < s_last then do
      let bl2 := bel_last + bel_last
      let bel_abv_idx := cpGmSlabMetaBase cp + (bl2 + bl2) + 3
      writeCompGMGenProg (((cp, metaBase), bel_abv_idx), p_del)
    else pure ()

private def compGmLinkMovedStep1Prog : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let sb ← compGmLinkMovedS1ReadProg (cp, (metaBase, p_last))
    compGmLinkMovedUpdBelProg (((cp, metaBase), p_del), sb)

private def compGmLinkMovedS2CondProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((cp, metaBase), (b_last, s_last)) => do
    let q_last ← readCompGMGenProg ((cp, metaBase), 4 + (b_last + b_last + b_last))
    if s_last + 1 < q_last then pure 1 else pure 0

private def compGmLinkMovedS2CheckProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), p_last) => do
    let bs ← compGmLinkMovedRead1Prog (cp, (metaBase, p_last))
    compGmLinkMovedS2CondProg ((cp, metaBase), bs)

private def compGmLinkMovedS2DoWriteProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let pl2 := p_last + p_last
    let abv_last ← readCompGMGenProg ((cp, metaBase), cpGmSlabMetaBase cp + (pl2 + pl2) + 3)
    let al2 := abv_last + abv_last
    writeCompGMGenProg (((cp, metaBase), cpGmSlabMetaBase cp + (al2 + al2) + 2), p_del)

private def compGmLinkMovedStep2Prog : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let flag ← compGmLinkMovedS2CheckProg ((cp, metaBase), p_last)
    if flag = 1 then
      compGmLinkMovedS2DoWriteProg (((cp, metaBase), p_del), p_last)
    else pure ()

private def compGmLinkMovedCopy1Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), (b_last, s_last)) => do
    let pd2 := p_del + p_del
    let ownB_del := cpGmSlabMetaBase cp + (pd2 + pd2)
    writeCompGMGenProg (((cp, metaBase), ownB_del), b_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 1), s_last)

private def compGmLinkMovedCopy2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), p_del), (bel_last, abv_last)) => do
    let pd2 := p_del + p_del
    let ownB_del := cpGmSlabMetaBase cp + (pd2 + pd2)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 2), bel_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 3), abv_last)

private def compGmLinkMovedStep3Prog : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let bs ← compGmLinkMovedRead1Prog (cp, (metaBase, p_last))
    compGmLinkMovedCopy1Prog (((cp, metaBase), p_del), bs)

private def compGmLinkMovedStep4Prog : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let ba ← compGmLinkMovedRead2Prog (cp, (metaBase, p_last))
    compGmLinkMovedCopy2Prog (((cp, metaBase), p_del), ba)

private def compGmLinkMovedUpdBothProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | d => do
    compGmLinkMovedStep1Prog d
    compGmLinkMovedStep2Prog d

private def compGmLinkMovedCopyBothProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | d => do
    compGmLinkMovedStep3Prog d
    compGmLinkMovedStep4Prog d

/-- Relink neighbor pointers and copy 4 metadata cells of `p_last` into `p_del`
(`gmLinkMovedNeighbors`). -/
def compGmLinkMovedNeighborsGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | d => do
    compGmLinkMovedUpdBothProg d
    compGmLinkMovedCopyBothProg d

/-- Move `p_last` into `p_del` by relinking directory/top and neighbor/metadata cells. -/
def compGmMoveLastSlabGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | d => do
    compGmRelinkMovedSlabGenProg d
    compGmLinkMovedNeighborsGenProg d

/-- Compact slab pool by moving `p_last = gm 0 - 1` into `p_del` (`gmCompactSlab`). -/
def compGmCompactSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), p_del) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let p_last := n_slabs - 1
    (if p_del < p_last then
      compGmMoveLastSlabGenProg (((cp, metaBase), p_del), p_last)
    else pure ()) >>= fun _ =>
      writeCompGMGenProg (((cp, metaBase), 0), p_last)

/-- Pop the top slab of bucket `b` and compact the slab pool in `GlobalMeta` (`gmPopSlab`,
`¬ReadsWidth`). -/
def compGmPopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let p_del ← compGmUnlinkTopSlabGenProg ((cp, metaBase), b)
    compGmCompactSlabGenProg ((cp, metaBase), p_del)

theorem memoryCost_compGmUnlinkTopSlabGenProg_eq
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmUnlinkTopSlabGenProg d) s = 14 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compGmUnlinkTopSlabGenProg, compGmUnlinkTop1Prog, compGmUnlinkTop2Prog]

theorem memoryCost_compGmRelinkMovedSlabGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmRelinkMovedSlabGenProg d) s ≤ 14 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  dsimp only [compGmRelinkMovedSlabGenProg, compGmRelinkMovedReadProg, compGmRelinkMovedW1Prog,
    compGmRelinkMovedW2Prog]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg, prog_clientResult_bind,
    prog_clientResult_pure]
  split_ifs <;> simp

theorem memoryCost_compGmLinkMovedNeighborsGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmLinkMovedNeighborsGenProg d) s ≤ 44 := by
  have h1 : ∀ s0, memoryCost (compGmLinkMovedStep1Prog d) s0 ≤ 8 := by
    intro s0; rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    dsimp only [compGmLinkMovedStep1Prog, compGmLinkMovedS1ReadProg, compGmLinkMovedUpdBelProg]
    simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      prog_clientResult_bind, prog_clientResult_pure]
    split_ifs <;> simp
  have h2 : ∀ s0, memoryCost (compGmLinkMovedStep2Prog d) s0 ≤ 12 := by
    intro s0; rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    dsimp only [compGmLinkMovedStep2Prog, compGmLinkMovedS2CheckProg, compGmLinkMovedRead1Prog,
      compGmLinkMovedS2CondProg, compGmLinkMovedS2DoWriteProg]
    simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      prog_clientResult_bind, prog_clientResult_pure]
    split_ifs <;> simp
  have h3 : ∀ s0, memoryCost (compGmLinkMovedStep3Prog d) s0 = 12 := by
    intro s0; rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    simp [compGmLinkMovedStep3Prog, compGmLinkMovedRead1Prog, compGmLinkMovedCopy1Prog]
  have h4 : ∀ s0, memoryCost (compGmLinkMovedStep4Prog d) s0 = 12 := by
    intro s0; rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    simp [compGmLinkMovedStep4Prog, compGmLinkMovedRead2Prog, compGmLinkMovedCopy2Prog]
  dsimp only [compGmLinkMovedNeighborsGenProg, compGmLinkMovedUpdBothProg,
    compGmLinkMovedCopyBothProg]
  simp only [Realization.memoryCost_bind', h3, h4]
  have ha := h1 s
  have hb := h2 ((Memory.spec 0).clientState s (compGmLinkMovedStep1Prog d))
  omega

theorem memoryCost_compGmMoveLastSlabGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmMoveLastSlabGenProg d) s ≤ 58 := by
  dsimp only [compGmMoveLastSlabGenProg]
  rw [Realization.memoryCost_bind']
  have h1 := memoryCost_compGmRelinkMovedSlabGenProg_le d s
  have h2 := memoryCost_compGmLinkMovedNeighborsGenProg_le d
    ((Memory.spec 0).clientState s (compGmRelinkMovedSlabGenProg d))
  omega

theorem memoryCost_compGmCompactSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmCompactSlabGenProg d) s ≤ 64 := by
  rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
  dsimp only [compGmCompactSlabGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg]
  split_ifs
  · have hm := memoryCost_compGmMoveLastSlabGenProg_le
      (((cp, metaBase), p_del),
        (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)
      ((Memory.spec 0).clientState s (readCompGMGenProg ((cp, metaBase), 0)))
    omega
  · simp

theorem memoryCost_compGmPopSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPopSlabGenProg d) s ≤ 78 := by
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

/-- Invariant for slab movement during compaction. -/
@[expose] def PureMovedSlabInv (N : ℕ) (gm : ℕ → ℕ) (p_del p_last : ℕ) : Prop :=
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let bel_last := gm (gmSlabBelowIdx N p_last)
  let abv_last := gm (gmSlabAboveIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  p_del < maxFullSlabs N ∧
  p_last < maxFullSlabs N ∧
  b_last < numBuckets N ∧
  s_last + 1 ≤ N ∧
  (0 < s_last → bel_last < maxFullSlabs N ∧ bel_last ≠ p_last) ∧
  (s_last + 1 < q_last → abv_last < maxFullSlabs N ∧ abv_last ≠ p_last) ∧
  0 < bucketBits N

/-- Precondition for moved slab metadata update. -/
@[expose] def CompGmMovedSlabPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last

/-- Precondition for compacting a slab in global metadata. -/
@[expose] def CompGmCompactSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
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

theorem compGmUnlinkTopSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
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
  have hbel_idx_lt : gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) <
      globalMetaLen N := gmSlabBelowIdx_lt hb_pos hp_del_cap
  have hbel_eq : gmSlabMetaBase N +
      (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
        compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
        (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 2 =
      gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
    unfold gmSlabBelowIdx; omega
  have hbel_val : gm (gmSlabBelowIdx N (gm (gmSlabTopIdx b))) < 2 ^ globalPtrBits N :=
    compGmAt_lt ..
  have hq1_val : gm (gmQIdx b) - 1 < 2 ^ globalPtrBits N :=
    lt_of_le_of_lt (Nat.sub_le _ _) (compGmAt_lt ..)
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem htop_idx_lt
    hbel_val s
  let s₁ := (Memory.spec 0).clientState s
    (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b),
      gm (gmSlabBelowIdx N (gm (gmSlabTopIdx b)))))
  have hs1_eq : (Memory.spec 0).clientState s
      (compGmUnlinkTop1Prog ((mkCompParams U V w N, metaBase), b)) = s₁ := by
    unfold StateTransitionSpec.clientState
    dsimp only [compGmUnlinkTop1Prog, cpGmSlabMetaBase_mk, s₁, gm]
    simp only [hq_eq, htop_eq, hbel_eq, prog_runClient_state_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg htop_idx_lt, clientResult_readCompGMGenProg hbel_idx_lt,
      runClient_state_readCompGMGenProg, prog_runClient_state_pure]
  have hs1_q : compGmAt metaBase U w N s₁.mem (gmQIdx b) = gm (gmQIdx b) := by
    rw [hg1, Function.update_of_ne (by unfold gmQIdx gmSlabTopIdx; omega)]
  have hres1 : (Memory.spec 0).clientResult s
      (compGmUnlinkTop1Prog ((mkCompParams U V w N, metaBase), b)) = gm (gmSlabTopIdx b) := by
    dsimp only [compGmUnlinkTop1Prog, cpGmSlabMetaBase_mk, gm]
    simp only [hq_eq, htop_eq, hbel_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg htop_idx_lt, clientResult_readCompGMGenProg hbel_idx_lt,
      runClient_state_readCompGMGenProg, runClient_state_writeCompGMGenProg, prog_clientResult_pure]
  have hres : (Memory.spec 0).clientResult s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)) =
      gm (gmSlabTopIdx b) := by
    dsimp only [compGmUnlinkTopSlabGenProg]
    rw [prog_clientResult_bind, hres1, hs1_eq]
    dsimp only [compGmUnlinkTop2Prog]
    simp only [hq_eq, prog_clientResult_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, runClient_state_readCompGMGenProg,
      runClient_state_writeCompGMGenProg, prog_clientResult_pure]
  have hst : s' = (Memory.spec 0).clientState s₁
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmQIdx b), gm (gmQIdx b) - 1)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmUnlinkTopSlabGenProg]
    rw [StateTransitionSpec.clientState_bind, hres1, hs1_eq]
    unfold StateTransitionSpec.clientState
    dsimp only [compGmUnlinkTop2Prog]
    simp only [hq_eq, prog_runClient_state_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, hs1_q, runClient_state_readCompGMGenProg,
      prog_runClient_state_pure]
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hq_idx_lt
    hq1_val s₁
  rw [hst]
  refine ⟨hres, hf1.trans hf2, ?_⟩
  rw [hg2, hg1]; rfl

private def CompGmUnlinkTop2Pre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), _p_del), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)

private theorem realizesBounded_compGmUnlinkTop1 :
    RealizesBounded .exact compGmUnlinkTop1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
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
    try simp only [cpGmSlabMetaBase_mk, htop_eq, hbel_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg htop_idx_lt, clientResult_readCompGMGenProg hbel_idx_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmSlabBelowIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmUnlinkTop2 :
    RealizesBounded .exact compGmUnlinkTop2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmUnlinkTop2Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, p_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_pos⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    try simp only [hq_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals try exact hq_pos
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx at *
    omega)

theorem realizesBounded_compGmUnlinkTopSlab :
    RealizesBounded .exact compGmUnlinkTopSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hu1 := realizesBounded_compGmUnlinkTop1
  have hu2 := realizesBounded_compGmUnlinkTop2
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    dsimp only
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
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
    have hbel_val : compGmAt metaBase U w N s.mem
        (gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) <
        2 ^ globalPtrBits N := compGmAt_lt ..
    obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl htop_idx_lt hbel_val s
    have hst1 : (Memory.spec 0).clientState s
        (compGmUnlinkTop1Prog ((mkCompParams U V w N, metaBase), b)) =
        (Memory.spec 0).clientState s
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b),
            compGmAt metaBase U w N s.mem
              (gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b))))) := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmUnlinkTop1Prog, cpGmSlabMetaBase_mk]
      simp only [htop_eq, hbel_eq, prog_runClient_state_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg htop_idx_lt, clientResult_readCompGMGenProg hbel_idx_lt,
        runClient_state_readCompGMGenProg, prog_runClient_state_pure]
    rw [hst1]
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr, hb_pos, hb, ?_⟩
    rw [hg1, Function.update_of_ne (by unfold gmQIdx gmSlabTopIdx; omega)]
    exact hq_pos

theorem compGmRelinkMovedSlabGenProg_effect
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
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last < dirSlabsPerBucket N) hw hitem hdir_lt (fun _ => hp_del_val) s
  let s₁ := (Memory.spec 0).clientState s
    (if s_last < dirSlabsPerBucket N then
      writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabDirIdx N b_last s_last), p_del)
    else pure ())
  have hs1_q : compGmAt metaBase U w N s₁.mem (gmQIdx b_last) = q_last := by
    rw [hg1]; split_ifs with hdir
    · rw [Function.update_of_ne
        (by dsimp only [b_last, gm]; unfold gmQIdx gmSlabDirIdx gmSlabDirBase; omega)]
    · rfl
  have hres_bs : (Memory.spec 0).clientResult s
      (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))) =
      (b_last, s_last) := by
    dsimp only [compGmRelinkMovedReadProg, cpGmSlabMetaBase_mk, b_last, s_last, gm]
    simp only [hpl4, prog_clientResult_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hownB_lt, clientResult_readCompGMGenProg hownS_lt,
      runClient_state_readCompGMGenProg, prog_clientResult_pure]
    rfl
  have hst_bs : (Memory.spec 0).clientState s
      (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))) = s := by
    unfold StateTransitionSpec.clientState
    dsimp only [compGmRelinkMovedReadProg]; simp
  have hst_w1 : (Memory.spec 0).clientState s
      (compGmRelinkMovedW1Prog (((mkCompParams U V w N, metaBase), p_del), (b_last, s_last))) =
      s₁ := by
    dsimp only [compGmRelinkMovedW1Prog, cpDirSlabs_mk, cpGmSlabDirBase_mk, gmSlabDirIdx, s₁]
    rfl
  have hst : s' = (Memory.spec 0).clientState s₁
      (if s_last + 1 = q_last then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmSlabTopIdx b_last), p_del)
      else pure ()) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmRelinkMovedSlabGenProg]
    rw [StateTransitionSpec.clientState_bind, hres_bs, hst_bs,
      StateTransitionSpec.clientState_bind, hst_w1]
    unfold StateTransitionSpec.clientState
    dsimp only [compGmRelinkMovedW2Prog]
    simp only [hq_eq, htop_eq, prog_runClient_state_bind, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_lt, hs1_q, runClient_state_readCompGMGenProg]
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last + 1 = q_last) hw hitem htop_lt (fun _ => hp_del_val) s₁
  rw [hst]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1]; rfl

private def CompGmSlabIdxPre (w : ℕ) : CompParams × (ℕ × ℕ) → Memory.State → Prop
  | (cp, (metaBase, p_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_last < maxFullSlabs N

private def CompGmOwnerPairPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), p_del), (b_last, s_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_del < maxFullSlabs N ∧
      b_last < numBuckets N ∧
      s_last + 1 ≤ N

private theorem realizesBounded_compGmRelinkMovedRead :
    RealizesBounded .exact compGmRelinkMovedReadProg
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      CompGmSlabIdxPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, ⟨metaBase, p_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabOwnerBIdx gmSlabOwnerSIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabOwnerSIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmRelinkMovedW1 :
    RealizesBounded .exact compGmRelinkMovedW1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmOwnerPairPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, hb_last, _⟩ := h
    try simp only [cpDirSlabs_mk, cpGmSlabDirBase_mk] at *)
  all_goals try (
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb_last hc
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
  all_goals (
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb_last hc
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabDirIdx gmSlabDirBase at *
    omega)

private theorem realizesBounded_compGmRelinkMovedW2 :
    RealizesBounded .exact compGmRelinkMovedW2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmOwnerPairPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, hb_last, hs_le⟩ := h
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have htop_lt := gmSlabTopIdx_lt hb_pos hb_last
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmQIdx gmSlabTopIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx gmSlabTopIdx at *
    omega)

theorem realizesBounded_compGmRelinkMovedSlab :
    RealizesBounded .exact compGmRelinkMovedSlabGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hr := realizesBounded_compGmRelinkMovedRead
  have hw1 := realizesBounded_compGmRelinkMovedW1
  have hw2 := realizesBounded_compGmRelinkMovedW2
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, _, _, _, _, hb_pos⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      hp_del_cap, hp_last_cap, hb_last, hs_le, _, _, hb_pos⟩ := h
    dsimp only
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hres : (Memory.spec 0).clientResult s
        (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))) =
        (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
         compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)) := by
      dsimp only [compGmRelinkMovedReadProg, cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hownB_lt, clientResult_readCompGMGenProg hownS_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    have hst : (Memory.spec 0).clientState s
        (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmRelinkMovedReadProg]; simp
    rw [hres, hst]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap, hb_last, hs_le⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      hp_del_cap, hp_last_cap, hb_last, hs_le, _, _, hb_pos⟩ := h
    dsimp only
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hres : (Memory.spec 0).clientResult s
        (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))) =
        (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
         compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)) := by
      dsimp only [compGmRelinkMovedReadProg, cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hownB_lt, clientResult_readCompGMGenProg hownS_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    have hfr_eq : ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last))))
        (compGmRelinkMovedW1Prog (((mkCompParams U V w N, metaBase), p_del),
          (Memory.spec 0).clientResult s
            (compGmRelinkMovedReadProg (mkCompParams U V w N, (metaBase, p_last)))))).frontier =
        s.frontier := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmRelinkMovedReadProg, compGmRelinkMovedW1Prog]
      simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg, prog_runClient_state_pure]
      split_ifs <;> simp
    rw [hres] at hfr_eq ⊢
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr_eq.symm ▸ hfr, hb_pos, hp_del_cap,
      hb_last, hs_le⟩

private theorem compGmLinkMovedStep1Prog_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s₁ := (Memory.spec 0).clientState s
      (compGmLinkMovedStep1Prog (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s₁ ∧
    compGmAt metaBase U w N s₁.mem =
      (if 0 < gm (gmSlabOwnerSIdx N p_last) then
        Function.update gm (gmSlabAboveIdx N (gm (gmSlabBelowIdx N p_last))) p_del
      else gm) ∧
    PureMovedSlabInv N (compGmAt metaBase U w N s₁.mem) p_del p_last := by
  intro gm s₁
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  have hownS_lt : gmSlabOwnerSIdx N p_last < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_lt : gmSlabBelowIdx N p_last < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_bel_lt : 0 < gm (gmSlabOwnerSIdx N p_last) →
      gmSlabAboveIdx N (gm (gmSlabBelowIdx N p_last)) < globalMetaLen N :=
    fun hs => gmSlabAboveIdx_lt hb_pos (hbel_cap hs).1
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val : p_del < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hs_eq : gmSlabOwnerBIdx N p_last + 1 = gmSlabOwnerSIdx N p_last := rfl
  have hbel_eq : gmSlabOwnerBIdx N p_last + 2 = gmSlabBelowIdx N p_last := rfl
  have hbl4 : gmSlabMetaBase N +
      ((gm (gmSlabBelowIdx N p_last) + gm (gmSlabBelowIdx N p_last)) +
        (gm (gmSlabBelowIdx N p_last) + gm (gmSlabBelowIdx N p_last))) + 3 =
      gmSlabAboveIdx N (gm (gmSlabBelowIdx N p_last)) := by unfold gmSlabAboveIdx; omega
  have hst : s₁ = (Memory.spec 0).clientState s
      (if 0 < gm (gmSlabOwnerSIdx N p_last) then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N (gm (gmSlabBelowIdx N p_last))), p_del)
      else pure ()) := by
    change (Memory.spec 0).clientState s _ = _
    unfold StateTransitionSpec.clientState
    dsimp only [compGmLinkMovedStep1Prog, compGmLinkMovedS1ReadProg, compGmLinkMovedUpdBelProg,
      cpGmSlabMetaBase_mk, gm]
    simp only [hpl4, hs_eq, hbel_eq, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hownS_lt,
      clientResult_readCompGMGenProg hbel_lt, runClient_state_readCompGMGenProg,
      prog_clientResult_pure, prog_runClient_state_pure]
    dsimp only [gm] at hbl4
    simp only [hbl4]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (0 < gm (gmSlabOwnerSIdx N p_last)) hw hitem habv_bel_lt (fun _ => hp_del_val) s
  rw [← hst] at hf1 hg1
  refine ⟨hf1, hg1, ?_⟩
  rw [hg1]
  by_cases hs : 0 < gm (gmSlabOwnerSIdx N p_last)
  · simp only [hs, ↓reduceIte]
    have hne_bel := (hbel_cap hs).2
    unfold PureMovedSlabInv; dsimp only
    rw [Function.update_of_ne (by unfold gmSlabOwnerBIdx gmSlabAboveIdx; omega),
      Function.update_of_ne (by unfold gmSlabOwnerSIdx gmSlabAboveIdx; omega),
      Function.update_of_ne (by unfold gmSlabBelowIdx gmSlabAboveIdx; omega),
      Function.update_of_ne
        (by unfold gmQIdx gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase
              gmTailPtrBase gmSlabDirBase; omega),
      Function.update_of_ne
        (by unfold gmSlabAboveIdx; intro heq
            dsimp only [gm] at heq
            have : compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last) = p_last := by
              omega
            exact hne_bel this)]
    exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  · simp only [hs, ↓reduceIte]
    exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩

private theorem compGmLinkMovedStep2Prog_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let b_last := gm (gmSlabOwnerBIdx N p_last)
    let s_last := gm (gmSlabOwnerSIdx N p_last)
    let s₂ := (Memory.spec 0).clientState s
      (compGmLinkMovedStep2Prog (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s₂ ∧
    compGmAt metaBase U w N s₂.mem =
      (if s_last + 1 < gm (gmQIdx b_last) then
        Function.update gm (gmSlabBelowIdx N (gm (gmSlabAboveIdx N p_last))) p_del
      else gm) ∧
    PureMovedSlabInv N (compGmAt metaBase U w N s₂.mem) p_del p_last := by
  intro gm b_last s_last s₂
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have habv_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hq_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hbel_abv_lt : s_last + 1 < gm (gmQIdx b_last) →
      gmSlabBelowIdx N (gm (gmSlabAboveIdx N p_last)) < globalMetaLen N :=
    fun hs => gmSlabBelowIdx_lt hb_pos (habv_cap hs).1
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val : p_del < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have hal4 : gmSlabMetaBase N +
      (gm (gmSlabAboveIdx N p_last) + gm (gmSlabAboveIdx N p_last) +
        (gm (gmSlabAboveIdx N p_last) + gm (gmSlabAboveIdx N p_last))) + 2 =
      gmSlabBelowIdx N (gm (gmSlabAboveIdx N p_last)) := by unfold gmSlabBelowIdx; omega
  have hrd1_st : (Memory.spec 0).clientState s
      (compGmLinkMovedRead1Prog (mkCompParams U V w N, (metaBase, p_last))) = s := by
    dsimp only [compGmLinkMovedRead1Prog]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
      StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
      StateTransitionSpec.clientState_pure]
  have hs_eq : gmSlabOwnerBIdx N p_last + 1 = gmSlabOwnerSIdx N p_last := rfl
  have hrd1_res : (Memory.spec 0).clientResult s
      (compGmLinkMovedRead1Prog (mkCompParams U V w N, (metaBase, p_last))) =
      (b_last, s_last) := by
    dsimp only [compGmLinkMovedRead1Prog]
    rw [StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg (by rw [cpGmSlabMetaBase_mk, hpl4]; exact hownB_lt),
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg (by rw [cpGmSlabMetaBase_mk, hpl4, hs_eq]; exact hownS_lt),
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_pure]
    simp only [cpGmSlabMetaBase_mk, hpl4, hs_eq, b_last, s_last, gm]
  have hchk_st : (Memory.spec 0).clientState s
      (compGmLinkMovedS2CheckProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
    dsimp only [compGmLinkMovedS2CheckProg]
    rw [StateTransitionSpec.clientState_bind, hrd1_res, hrd1_st]
    dsimp only [compGmLinkMovedS2CondProg]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg]
    split_ifs <;> rw [StateTransitionSpec.clientState_pure]
  have hchk_res : (Memory.spec 0).clientResult s
      (compGmLinkMovedS2CheckProg ((mkCompParams U V w N, metaBase), p_last)) =
      (if s_last + 1 < gm (gmQIdx b_last) then 1 else 0) := by
    dsimp only [compGmLinkMovedS2CheckProg]
    rw [StateTransitionSpec.clientResult_bind, hrd1_res, hrd1_st]
    dsimp only [compGmLinkMovedS2CondProg]
    rw [StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg (by rw [hq_eq]; exact hq_lt),
      clientState_readCompGMGenProg]
    dsimp only [gm]
    rw [hq_eq]
    split_ifs <;> rw [StateTransitionSpec.clientResult_pure]
  have hst : s₂ = (Memory.spec 0).clientState s
      (if s_last + 1 < gm (gmQIdx b_last) then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabBelowIdx N (gm (gmSlabAboveIdx N p_last))), p_del)
      else pure ()) := by
    dsimp only [s₂, compGmLinkMovedStep2Prog]
    rw [StateTransitionSpec.clientState_bind, hchk_st, hchk_res]
    by_cases hs : s_last + 1 < gm (gmQIdx b_last)
    · simp only [hs, ↓reduceIte]
      dsimp only [compGmLinkMovedS2DoWriteProg]
      have habv4 : gmSlabOwnerBIdx N p_last + 3 = gmSlabAboveIdx N p_last := rfl
      rw [StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
        clientResult_readCompGMGenProg (by rw [cpGmSlabMetaBase_mk, hpl4]; exact habv_lt)]
      dsimp only [cpGmSlabMetaBase_mk, gm]
      rw [hpl4, habv4, hal4]
    · simp only [hs, ↓reduceIte]; rfl
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last + 1 < gm (gmQIdx b_last)) hw hitem hbel_abv_lt (fun _ => hp_del_val) s
  rw [← hst] at hf2 hg2
  refine ⟨hf2, hg2, ?_⟩
  rw [hg2]
  by_cases hs : s_last + 1 < gm (gmQIdx b_last)
  · simp only [hs, ↓reduceIte]
    have hne_abv := (habv_cap hs).2
    unfold PureMovedSlabInv; dsimp only
    rw [Function.update_of_ne (by unfold gmSlabOwnerBIdx gmSlabBelowIdx; omega),
      Function.update_of_ne (by unfold gmSlabOwnerSIdx gmSlabBelowIdx; omega),
      Function.update_of_ne
        (by unfold gmSlabBelowIdx; intro heq
            dsimp only [gm] at heq
            have : compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last) = p_last := by
              omega
            exact hne_abv this),
      Function.update_of_ne
        (by unfold gmQIdx gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase
              gmTailPtrBase gmSlabDirBase; omega),
      Function.update_of_ne (by unfold gmSlabAboveIdx gmSlabBelowIdx; omega)]
    exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  · simp only [hs, ↓reduceIte]
    exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩

private theorem compGmLinkMovedCopyBothProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hp_del_cap : p_del < maxFullSlabs N)
    (hp_last_cap : p_last < maxFullSlabs N) (s : Memory.State) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmLinkMovedCopyBothProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem =
      Function.update
        (Function.update
          (Function.update
            (Function.update gm (gmSlabOwnerBIdx N p_del) (gm (gmSlabOwnerBIdx N p_last)))
            (gmSlabOwnerSIdx N p_del) (gm (gmSlabOwnerSIdx N p_last)))
          (gmSlabBelowIdx N p_del) (gm (gmSlabBelowIdx N p_last)))
        (gmSlabAboveIdx N p_del) (gm (gmSlabAboveIdx N p_last)) := by
  intro gm s'
  have hownB_last_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last_lt : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hownB_del_lt := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del_lt := gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del_lt := gmSlabAboveIdx_lt hb_pos hp_del_cap
  have hb_val : gm (gmSlabOwnerBIdx N p_last) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hs_val : gm (gmSlabOwnerSIdx N p_last) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hbel_val : gm (gmSlabBelowIdx N p_last) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have habv_val : gm (gmSlabAboveIdx N p_last) < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hpl4 : gmSlabMetaBase N + ((p_last + p_last) + (p_last + p_last)) =
      gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
  have hpd4 : gmSlabMetaBase N + ((p_del + p_del) + (p_del + p_del)) =
      gmSlabOwnerBIdx N p_del := by unfold gmSlabOwnerBIdx; omega
  have hs_del : gmSlabOwnerBIdx N p_del + 1 = gmSlabOwnerSIdx N p_del := rfl
  have hs_last : gmSlabOwnerBIdx N p_last + 1 = gmSlabOwnerSIdx N p_last := rfl
  have hbel_eq : gmSlabBelowIdx N p_del = gmSlabOwnerBIdx N p_del + 2 := rfl
  have habv_eq : gmSlabAboveIdx N p_del = gmSlabOwnerBIdx N p_del + 3 := rfl
  have hbel_l_eq : gmSlabBelowIdx N p_last = gmSlabOwnerBIdx N p_last + 2 := rfl
  have habv_l_eq : gmSlabAboveIdx N p_last = gmSlabOwnerBIdx N p_last + 3 := rfl
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_del_lt
    hb_val s
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_del_lt
    hs_val _
  let s₃ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabOwnerBIdx N p_del), gm (gmSlabOwnerBIdx N p_last))))
    (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
      gmSlabOwnerSIdx N p_del), gm (gmSlabOwnerSIdx N p_last)))
  have hs3_bel : compGmAt metaBase U w N s₃.mem (gmSlabBelowIdx N p_last) =
      gm (gmSlabBelowIdx N p_last) := by
    rw [hg4, hg3, Function.update_of_ne (by unfold gmSlabBelowIdx gmSlabOwnerSIdx; omega),
      Function.update_of_ne (by unfold gmSlabBelowIdx gmSlabOwnerBIdx; omega)]
  have hs3_abv : compGmAt metaBase U w N s₃.mem (gmSlabAboveIdx N p_last) =
      gm (gmSlabAboveIdx N p_last) := by
    rw [hg4, hg3, Function.update_of_ne (by unfold gmSlabAboveIdx gmSlabOwnerSIdx; omega),
      Function.update_of_ne (by unfold gmSlabAboveIdx gmSlabOwnerBIdx; omega)]
  have hst3 : (Memory.spec 0).clientState s
      (compGmLinkMovedStep3Prog (((mkCompParams U V w N, metaBase), p_del), p_last)) = s₃ := by
    have hownS_last_lt' : gmSlabOwnerSIdx N p_last < globalMetaLen N := by
      rw [← hs_last]; exact hownS_last_lt
    unfold StateTransitionSpec.clientState
    dsimp only [compGmLinkMovedStep3Prog, compGmLinkMovedRead1Prog, compGmLinkMovedCopy1Prog,
      cpGmSlabMetaBase_mk, gm, s₃]
    simp only [hpl4, hpd4, hs_del, hs_last, prog_runClient_state_bind, prog_clientResult_bind,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hownB_last_lt,
      clientResult_readCompGMGenProg hownS_last_lt', runClient_state_readCompGMGenProg,
      prog_clientResult_pure, prog_runClient_state_pure]
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s₃
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabBelowIdx N p_del), gm (gmSlabBelowIdx N p_last))))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabAboveIdx N p_del), gm (gmSlabAboveIdx N p_last))) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmLinkMovedCopyBothProg]
    rw [StateTransitionSpec.clientState_bind, hst3]
    dsimp only [compGmLinkMovedStep4Prog]
    have hrd2_st : (Memory.spec 0).clientState s₃
        (compGmLinkMovedRead2Prog (mkCompParams U V w N, (metaBase, p_last))) = s₃ := by
      dsimp only [compGmLinkMovedRead2Prog]
      rw [StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
        StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
        StateTransitionSpec.clientState_pure]
    have hrd2_res : (Memory.spec 0).clientResult s₃
        (compGmLinkMovedRead2Prog (mkCompParams U V w N, (metaBase, p_last))) =
        (gm (gmSlabBelowIdx N p_last), gm (gmSlabAboveIdx N p_last)) := by
      dsimp only [compGmLinkMovedRead2Prog]
      rw [StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg
          (by rw [cpGmSlabMetaBase_mk, hpl4, ← hbel_l_eq]; exact hbel_last_lt),
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg
          (by rw [cpGmSlabMetaBase_mk, hpl4, ← habv_l_eq]; exact habv_last_lt),
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_pure]
      simp only [cpGmSlabMetaBase_mk, hpl4, ← hbel_l_eq, ← habv_l_eq, hs3_bel, hs3_abv]
    rw [StateTransitionSpec.clientState_bind, hrd2_res, hrd2_st]
    dsimp only [compGmLinkMovedCopy2Prog]
    simp only [cpGmSlabMetaBase_mk, hpd4, ← hbel_eq, ← habv_eq]
    rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_del_lt
    hbel_val s₃
  obtain ⟨hf6, hg6⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem habv_del_lt
    habv_val _
  rw [hst]
  refine ⟨hf3.trans (hf4.trans (hf5.trans hf6)), ?_⟩
  rw [hg6, hg5, hg4, hg3]

theorem compGmLinkMovedNeighborsGenProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmLinkMovedNeighborsGenProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmLinkMovedNeighbors N gm p_del p_last := by
  intro gm s'
  obtain ⟨hf1, hg1, hinv1⟩ := compGmLinkMovedStep1Prog_effect (m_items := m_items) hw hitem s hpre
  let s₁ := (Memory.spec 0).clientState s
    (compGmLinkMovedStep1Prog (((mkCompParams U V w N, metaBase), p_del), p_last))
  obtain ⟨hf2, hg2, hinv2⟩ := compGmLinkMovedStep2Prog_effect (m_items := m_items) hw hitem s₁ hinv1
  let s₂ := (Memory.spec 0).clientState s₁
    (compGmLinkMovedStep2Prog (((mkCompParams U V w N, metaBase), p_del), p_last))
  obtain ⟨hf34, hg34⟩ := compGmLinkMovedCopyBothProg_effect (m_items := m_items) hw hitem
    hinv2.2.2.2.2.2.2 hinv2.1 hinv2.2.1 s₂
  have hg1_cells : compGmAt metaBase U w N s₁.mem (gmSlabOwnerBIdx N p_last) =
        gm (gmSlabOwnerBIdx N p_last) ∧
      compGmAt metaBase U w N s₁.mem (gmSlabOwnerSIdx N p_last) =
        gm (gmSlabOwnerSIdx N p_last) ∧
      compGmAt metaBase U w N s₁.mem (gmSlabBelowIdx N p_last) =
        gm (gmSlabBelowIdx N p_last) ∧
      compGmAt metaBase U w N s₁.mem (gmSlabAboveIdx N p_last) =
        gm (gmSlabAboveIdx N p_last) ∧
      compGmAt metaBase U w N s₁.mem (gmQIdx (gm (gmSlabOwnerBIdx N p_last))) =
        gm (gmQIdx (gm (gmSlabOwnerBIdx N p_last))) := by
    rw [hg1]; dsimp only [gm]; split_ifs with hs
    · have hne_bel := (hpre.2.2.2.2.1 hs).2
      have hb_last := hpre.2.2.1
      have hb_pos := hpre.2.2.2.2.2.2
      rw [Function.update_of_ne (by unfold gmSlabOwnerBIdx gmSlabAboveIdx; omega),
        Function.update_of_ne (by unfold gmSlabOwnerSIdx gmSlabAboveIdx; omega),
        Function.update_of_ne (by unfold gmSlabBelowIdx gmSlabAboveIdx; omega),
        Function.update_of_ne
          (by unfold gmSlabAboveIdx; intro heq
              have : compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last) = p_last := by
                omega
              exact hne_bel this),
        Function.update_of_ne
          (by unfold gmQIdx gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase
                gmTailPtrBase gmSlabDirBase; omega)]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hg2_cells : compGmAt metaBase U w N s₂.mem (gmSlabOwnerBIdx N p_last) =
        gm (gmSlabOwnerBIdx N p_last) ∧
      compGmAt metaBase U w N s₂.mem (gmSlabOwnerSIdx N p_last) =
        gm (gmSlabOwnerSIdx N p_last) ∧
      compGmAt metaBase U w N s₂.mem (gmSlabBelowIdx N p_last) =
        gm (gmSlabBelowIdx N p_last) ∧
      compGmAt metaBase U w N s₂.mem (gmSlabAboveIdx N p_last) =
        gm (gmSlabAboveIdx N p_last) := by
    rw [hg2]
    rw [hg1_cells.1, hg1_cells.2.1, hg1_cells.2.2.2.2]
    split_ifs with hs
    · have hne_abv := (hpre.2.2.2.2.2.1 hs).2
      rw [hg1_cells.2.2.2.1]
      rw [Function.update_of_ne (by unfold gmSlabOwnerBIdx gmSlabBelowIdx; omega),
        Function.update_of_ne (by unfold gmSlabOwnerSIdx gmSlabBelowIdx; omega),
        Function.update_of_ne
          (by unfold gmSlabBelowIdx; intro heq
              dsimp only [gm] at heq
              have : compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last) = p_last := by
                omega
              exact hne_abv this),
        Function.update_of_ne (by unfold gmSlabAboveIdx gmSlabBelowIdx; omega)]
      exact ⟨hg1_cells.1, hg1_cells.2.1, hg1_cells.2.2.1, hg1_cells.2.2.2.1⟩
    · exact ⟨hg1_cells.1, hg1_cells.2.1, hg1_cells.2.2.1, hg1_cells.2.2.2.1⟩
  dsimp only [s', compGmLinkMovedNeighborsGenProg, compGmLinkMovedUpdBothProg]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  refine ⟨hf1.trans (hf2.trans hf34), ?_⟩
  rw [hg34, hg2_cells.1, hg2_cells.2.1, hg2_cells.2.2.1, hg2_cells.2.2.2]
  rw [hg2]
  rw [hg1_cells.1, hg1_cells.2.1, hg1_cells.2.2.2.1, hg1_cells.2.2.2.2, hg1]
  rfl

private def CompGmUpdBelPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), _p_del), (s_last, bel_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      (0 < s_last → bel_last < maxFullSlabs N)

private def CompGmS2CondPre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_last, s_last)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b_last < numBuckets N ∧
      s_last + 1 ≤ N

private def CompGmS2CheckPre (w : ℕ) :
    (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_last < maxFullSlabs N ∧
      compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) < numBuckets N ∧
      compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last) + 1 ≤ N

private def CompGmS2WritePre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), _p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_last < maxFullSlabs N ∧
      compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last) < maxFullSlabs N

private def CompGmCopyDestPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), p_del), _pair), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_del < maxFullSlabs N

private def CompGmCopyPairPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_del < maxFullSlabs N ∧
      p_last < maxFullSlabs N

private theorem realizesBounded_compGmLinkMovedRead1 :
    RealizesBounded .exact compGmLinkMovedRead1Prog
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      CompGmSlabIdxPre (fun _ _ => 0) :=
  realizesBounded_compGmRelinkMovedRead

private theorem realizesBounded_compGmLinkMovedRead2 :
    RealizesBounded .exact compGmLinkMovedRead2Prog
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      CompGmSlabIdxPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, ⟨metaBase, p_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
    have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_last_cap
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_last_cap
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabBelowIdx gmSlabAboveIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabBelowIdx gmSlabAboveIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedS1Read :
    RealizesBounded .exact compGmLinkMovedS1ReadProg
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      CompGmSlabIdxPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, ⟨metaBase, p_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
    have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_last_cap
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabOwnerSIdx gmSlabBelowIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerSIdx gmSlabBelowIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedUpdBel :
    RealizesBounded .exact compGmLinkMovedUpdBelProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmUpdBelPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨s_last, bel_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hbel_cap⟩ := h
    have habv_lt := gmSlabAboveIdx_lt hb_pos (hbel_cap hc)
    try simp only [cpGmSlabMetaBase_mk] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabAboveIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedStep1 :
    RealizesBounded .exact compGmLinkMovedStep1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hr := realizesBounded_compGmLinkMovedS1Read
  have hbel := realizesBounded_compGmLinkMovedUpdBel
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, _, hp_last_cap, _, _, _, _, hb_pos⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, _, _, hbel_cap, _, hb_pos⟩ := h
    dsimp only
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hbel_lt : gmSlabOwnerBIdx N p_last + 2 < globalMetaLen N :=
      gmSlabBelowIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hst : (Memory.spec 0).clientState s
        (compGmLinkMovedS1ReadProg (mkCompParams U V w N, (metaBase, p_last))) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedS1ReadProg]; simp
    have hres : (Memory.spec 0).clientResult s
        (compGmLinkMovedS1ReadProg (mkCompParams U V w N, (metaBase, p_last))) =
        (compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last),
         compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last)) := by
      dsimp only [compGmLinkMovedS1ReadProg, cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hownS_lt, clientResult_readCompGMGenProg hbel_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    rw [hst, hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, fun hs => (hbel_cap hs).1⟩

private theorem realizesBounded_compGmLinkMovedS2Cond :
    RealizesBounded .exact compGmLinkMovedS2CondProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompGmS2CondPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  · rcases d with ⟨⟨cp, metaBase⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩ := h
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    rw [hq_eq]; exact hq_lt.le
  · rcases d with ⟨⟨cp, metaBase⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩ := h
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk, hq_eq]; exact hq_lt
  · rcases d with ⟨⟨cp, metaBase⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩ := h
    change s_last + 1 < 2 ^ w
    omega
  · rcases d with ⟨⟨cp, metaBase⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨_, _, _, hw, _⟩ := h
    exact Nat.one_lt_two_pow hw.ne'

private theorem realizesBounded_compGmLinkMovedS2Check :
    RealizesBounded .exact compGmLinkMovedS2CheckProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmS2CheckPre (fun _ _ => 0) := by
  have hr1 := realizesBounded_compGmLinkMovedRead1
  have hcnd := realizesBounded_compGmLinkMovedS2Cond
  realize
  · rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap, _, _⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap, hb_last, hs_le⟩ := h
    dsimp only
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hst : (Memory.spec 0).clientState s
        (compGmLinkMovedRead1Prog (mkCompParams U V w N, (metaBase, p_last))) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedRead1Prog]; simp
    have hres : (Memory.spec 0).clientResult s
        (compGmLinkMovedRead1Prog (mkCompParams U V w N, (metaBase, p_last))) =
        (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
         compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)) := by
      dsimp only [compGmLinkMovedRead1Prog, cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_clientResult_bind, StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hownB_lt, clientResult_readCompGMGenProg hownS_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure]
      rfl
    rw [hst, hres]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le⟩

private theorem realizesBounded_compGmLinkMovedS2DoWrite :
    RealizesBounded .exact compGmLinkMovedS2DoWriteProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmS2WritePre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap, habv_cap⟩ := h
    have habv_lt : gmSlabOwnerBIdx N p_last + 3 < globalMetaLen N :=
      gmSlabAboveIdx_lt hb_pos hp_last_cap
    have hbel_abv_lt := gmSlabBelowIdx_lt hb_pos habv_cap
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) + 3 =
        gmSlabOwnerBIdx N p_last + 3 := by unfold gmSlabOwnerBIdx; omega
    try simp only [cpGmSlabMetaBase_mk, hpl4, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg habv_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx gmSlabBelowIdx gmSlabOwnerBIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabAboveIdx gmSlabBelowIdx gmSlabOwnerBIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedStep2 :
    RealizesBounded .exact compGmLinkMovedStep2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hchk := realizesBounded_compGmLinkMovedS2Check
  have hwr := realizesBounded_compGmLinkMovedS2DoWrite
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, hb_last, hs_le, _, _, hb_pos⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap, hb_last, hs_le⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, _, _, _, _, rfl, _, _, _, _, _, _, _, _⟩ := h
    exact Nat.one_lt_two_pow hw.ne'
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, hb_last, _, _, habv_cap, hb_pos⟩ := h
    dsimp only at hc ⊢
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
    have hownS_lt : gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N :=
      gmSlabOwnerSIdx_lt hb_pos hp_last_cap
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hpl4 : gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) =
        gmSlabOwnerBIdx N p_last := by unfold gmSlabOwnerBIdx; omega
    have hs_eq : gmSlabOwnerSIdx N p_last = gmSlabOwnerBIdx N p_last + 1 := rfl
    have hq_eq : 4 + (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
        compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last) +
        compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) =
        gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) := by
      unfold gmQIdx; omega
    have hchk_st : (Memory.spec 0).clientState s
        (compGmLinkMovedS2CheckProg ((mkCompParams U V w N, metaBase), p_last)) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedS2CheckProg, compGmLinkMovedRead1Prog, compGmLinkMovedS2CondProg,
        cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg, prog_runClient_state_pure]
      split_ifs <;> simp
    have hchk_res : (Memory.spec 0).clientResult s
        (compGmLinkMovedS2CheckProg ((mkCompParams U V w N, metaBase), p_last)) =
        (if compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last) + 1 <
            compGmAt metaBase U w N s.mem
              (gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)))
          then 1 else 0) := by
      dsimp only [compGmLinkMovedS2CheckProg, compGmLinkMovedRead1Prog, compGmLinkMovedS2CondProg,
        cpGmSlabMetaBase_mk]
      simp only [hpl4, prog_clientResult_bind, prog_runClient_state_bind,
        StateTransitionSpec.clientState,
        clientResult_readCompGMGenProg hownB_lt, clientResult_readCompGMGenProg hownS_lt,
        runClient_state_readCompGMGenProg, prog_clientResult_pure, prog_runClient_state_pure]
      simp only [hq_eq, clientResult_readCompGMGenProg hq_lt, hs_eq]
      split_ifs <;> simp
    rw [hchk_res] at hc
    rw [hchk_st]
    have hs_lt : compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last) + 1 <
        compGmAt metaBase U w N s.mem
          (gmQIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last))) := by
      split_ifs at hc with hlt
      exact hlt
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap, (habv_cap hs_lt).1⟩

private theorem realizesBounded_compGmLinkMovedCopy1 :
    RealizesBounded .exact compGmLinkMovedCopy1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmCopyDestPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨b_last, s_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
    have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
    have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_del_cap
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabOwnerBIdx gmSlabOwnerSIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabOwnerSIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedCopy2 :
    RealizesBounded .exact compGmLinkMovedCopy2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmCopyDestPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨bel_last, abv_last⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
    have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_del_cap
    try simp only [cpGmSlabMetaBase_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabBelowIdx gmSlabAboveIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabBelowIdx gmSlabAboveIdx gmSlabMetaBase at *
    omega)

private theorem realizesBounded_compGmLinkMovedStep3 :
    RealizesBounded .exact compGmLinkMovedStep3Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCopyPairPre (fun _ _ => 0) := by
  have hr1 := realizesBounded_compGmLinkMovedRead1
  have hc1 := realizesBounded_compGmLinkMovedCopy1
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, hp_last_cap⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap, _⟩ := h
    dsimp only
    have hst : (Memory.spec 0).clientState s
        (compGmLinkMovedRead1Prog (mkCompParams U V w N, (metaBase, p_last))) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedRead1Prog]; simp
    rw [hst]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩

private theorem realizesBounded_compGmLinkMovedStep4 :
    RealizesBounded .exact compGmLinkMovedStep4Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCopyPairPre (fun _ _ => 0) := by
  have hr2 := realizesBounded_compGmLinkMovedRead2
  have hc2 := realizesBounded_compGmLinkMovedCopy2
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, hp_last_cap⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap, _⟩ := h
    dsimp only
    have hst : (Memory.spec 0).clientState s
        (compGmLinkMovedRead2Prog (mkCompParams U V w N, (metaBase, p_last))) = s := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedRead2Prog]; simp
    rw [hst]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩

private theorem realizesBounded_compGmLinkMovedUpdBoth :
    RealizesBounded .exact compGmLinkMovedUpdBothProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hs1 := realizesBounded_compGmLinkMovedStep1
  have hs2 := realizesBounded_compGmLinkMovedStep2
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hinv⟩ := h
    obtain ⟨hf1, _, hinv1⟩ := compGmLinkMovedStep1Prog_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s hinv
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr, hinv1⟩

private theorem realizesBounded_compGmLinkMovedCopyBoth :
    RealizesBounded .exact compGmLinkMovedCopyBothProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCopyPairPre (fun _ _ => 0) := by
  have hs3 := realizesBounded_compGmLinkMovedStep3
  have hs4 := realizesBounded_compGmLinkMovedStep4
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap, hp_last_cap⟩ := h
    dsimp only
    have hfr_eq : ((Memory.spec 0).clientState s
        (compGmLinkMovedStep3Prog (((mkCompParams U V w N, metaBase), p_del), p_last))).frontier =
        s.frontier := by
      unfold StateTransitionSpec.clientState
      dsimp only [compGmLinkMovedStep3Prog, compGmLinkMovedRead1Prog, compGmLinkMovedCopy1Prog]
      simp
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr_eq.symm ▸ hfr, hb_pos, hp_del_cap, hp_last_cap⟩

theorem realizesBounded_compGmLinkMovedNeighbors :
    RealizesBounded .exact compGmLinkMovedNeighborsGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hupd := realizesBounded_compGmLinkMovedUpdBoth
  have hcpy := realizesBounded_compGmLinkMovedCopyBoth
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hinv⟩ := h
    obtain ⟨hf1, _, hinv1⟩ := compGmLinkMovedStep1Prog_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s hinv
    obtain ⟨hf2, _, _⟩ := compGmLinkMovedStep2Prog_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl
      ((Memory.spec 0).clientState s
        (compGmLinkMovedStep1Prog (((mkCompParams U V w N, metaBase), p_del), p_last)))
      hinv1
    have hfr12 : ((Memory.spec 0).clientState s
        (compGmLinkMovedUpdBothProg (((mkCompParams U V w N, metaBase), p_del), p_last))).frontier =
        s.frontier := by
      dsimp only [compGmLinkMovedUpdBothProg]
      rw [StateTransitionSpec.clientState_bind, hf2.frontier_eq, hf1.frontier_eq]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr12.symm ▸ hfr,
      hinv.2.2.2.2.2.2, hinv.1, hinv.2.1⟩

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

theorem compGmMoveLastSlabGenProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmMoveLastSlabGenProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem =
      gmLinkMovedNeighbors N (gmRelinkMovedSlab N gm p_del p_last) p_del p_last := by
  intro gm s'
  obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect (m_items := m_items) hw hitem s hpre
  obtain ⟨hf2, hg2⟩ := compGmLinkMovedNeighborsGenProg_effect (m_items := m_items) hw hitem _
    (hg1.symm ▸ pureMovedSlabInv_after_relink hpre)
  dsimp only [s', compGmMoveLastSlabGenProg]
  rw [StateTransitionSpec.clientState_bind]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1]

theorem realizesBounded_compGmMoveLastSlab :
    RealizesBounded .exact compGmMoveLastSlabGenProg
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

theorem compGmCompactSlabGenProg_effect {metaBase itemBase U V w N m_items p_del : ℕ}
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
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [p_last, gm]; omega)
  dsimp only [s', compGmCompactSlabGenProg]
  rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
    clientState_readCompGMGenProg]
  by_cases hlt : p_del < p_last
  · have hm1 := hcond hlt
    obtain ⟨hf1, hg1⟩ := compGmMoveLastSlabGenProg_effect (m_items := m_items) hw hitem s hm1
    obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val _
    rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind]
    refine ⟨hf1.trans hf2, ?_⟩
    rw [hg2, hg1]
    exact gmCompactSlab_eq_parts gm hlt hm1.2.2.1
  · obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val s
    rw [ite_eq_right hlt, pure_bind]
    refine ⟨hf1, ?_⟩
    unfold gmCompactSlab; rw [ite_eq_right hlt, hg1]

theorem realizesBounded_compGmCompactSlab :
    RealizesBounded .exact compGmCompactSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCompactSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  have hmov := realizesBounded_compGmMoveLastSlab
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, h0_pos, h0_le, hp_lt, hcond⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  all_goals try exact h0_pos
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hcond hc⟩
  · by_cases hlt : p_del < compGmAt metaBase U w N s.mem 0 - 1
    · rw [ite_eq_left hlt]
      obtain ⟨hf1, _⟩ := compGmMoveLastSlabGenProg_effect
        (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
        hw le_rfl s (hcond hlt)
      exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr⟩, h0_lt⟩
    · rw [ite_eq_right hlt]
      exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩

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
    refine ⟨?_, ?_⟩
    · rw [hbel_eq]; exact hslab.ptr_lt_maxFullSlabs hb_last (by omega)
    · intro heq
      have hS := hslab.ownerS_ptr _ hb_last (gm (gmSlabOwnerSIdx N (gm 0 - 1)) - 1) (by omega)
      rw [← hbel_eq, heq] at hS
      omega
  · intro hs_lt_q
    rw [huQ _ hb_last] at hs_lt_q
    have hs1_lt : gm (gmSlabOwnerSIdx N (gm 0 - 1)) + 1 <
        gm (gmQIdx (gm (gmSlabOwnerBIdx N (gm 0 - 1)))) := by
      split_ifs at hs_lt_q with hbeq
      · subst hbeq; omega
      · exact hs_lt_q
    have habv_eq := hslab.above_eq _ hb_last _ hs_last hs1_lt
    rw [hptr_last] at habv_eq
    refine ⟨?_, ?_⟩
    · rw [habv_eq]; exact hslab.ptr_lt_maxFullSlabs hb_last hs1_lt
    · intro heq
      have hS := hslab.ownerS_ptr _ hb_last (gm (gmSlabOwnerSIdx N (gm 0 - 1)) + 1) hs1_lt
      rw [← habv_eq, heq] at hS
      omega

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

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
