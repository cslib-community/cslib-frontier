/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.MicroSearchOps
-- Unfolds `Memory.Prog` bodies in `ResizableSuccinct` and `Succinct*` for `FixedCoupled` proofs.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctBucketOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctHash
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Bucket-Level and Feistel-Dispatched Dictionary Operations in `Memory.Prog`

This module completes the `Memory.Prog` subroutine layer (`¬ReadsWidth`, certified via
`RealizesBounded .exact`) for in-epoch operations on the compacted resizable succinct dictionary,
coupling every mutating and read-only path via `FixedCoupled` to the fixed-capacity reference
operations in `SuccinctBucketOps.lean`, `SuccinctDeleteOps.lean`, and `SuccinctHash.lean`:
* `compGrowDeltaGenProg`, `compShrinkDeltaGenProg`: overflow-free `0..2`-word item-stream delta
  evaluators for pre-insert `growZeroCode` and post-delete `shrinkCode`;
* `compFeistelCoordsProg`: shared Feistel `(b, q, m)` coordinate extractor;
* `compQueryWithHashGenProg`: Feistel-dispatched lookup returning `s_abs u`;
* `compInsertSearchWithHashGenProg`, `compWritePhysValGenProg`, `compInsertAppendNewGenProg`:
  split two-phase insertion allowing the Resizable Word RAM caller to grow the hardware frontier by
  `compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n ≤ 2` words only on a miss
  (`found = 0`) before writing the new dense slot;
* `compDeletePrepWithHashGenProg`, `compDeleteFinishWithHashGenProg`: two-phase compacted deletion
  coupled to `deletePrepWithHashProg` and `deleteFinishWithHashProg` (via internal payload-copy and
  bucket-level helpers).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGrowDeltaGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compShrinkDeltaGenProg`:
  overflow-free word-delta evaluators for item-count transitions `n → n + 1` and `n → n - 1`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg`:
  compacted Feistel-dispatched dictionary lookup.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertSearchWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compWritePhysValGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertAppendNewGenProg`:
  compacted split insertion subroutines (search, in-place value update, and post-grow slot append).
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeletePrepWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteFinishWithHashGenProg`:
  compacted two-phase Feistel-dispatched deletion subroutines.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg_dict_spec`:
  dictionary-level lookup correctness and `O(1 + probeExcess)` `memoryCost` bound.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertHit_dict_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertMiss_dict_spec`:
  dictionary-level `DictStateInv` and `FixedCoupled` preservation and amortized `memoryCost` bounds
  for hit (in-place update) and miss (post-grow append) insertion paths.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteWithHashGenProg_dict_spec`:
  dictionary-level `DictStateInv` and `FixedCoupled` preservation and amortized `memoryCost` bound
  for two-phase compacted deletion.

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

/-- Found flag (`1` on hit, `0` on miss) of a bucket-search result `((found, j), phys)`. -/
abbrev sbFound (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.1

/-- Feistel bucket coordinate `b` of a `compFeistelCoordsProg` result `((b, q), m)`. -/
private abbrev fcBucket (c : (ℕ × ℕ) × ℕ) : ℕ := c.1.1

/-! ## Section 1: Overflow-Free Word-Delta Evaluators and Feistel Coordinate Extraction -/

/-- Bound `Fits w (wOffQ q v w m + 3)` whenever `4 + compactedItemWords U V w N m < 2 ^ w`
(satisfied automatically inside any addressable active epoch since `epochHdrWords = 225 ≥ 4`). -/
theorem fits_wOffQ_add_three_of_itemWords {U V w N m : ℕ} (hw : 0 < w)
    (hfit : Fits w (4 + compactedItemWords U V w N m)) :
    Fits w (wOffQ (quotientBits U N) (valBits V) w m + 3) := by
  have heq := compactedItemWords_eq_wOffQ_add (U := U) (V := V) (N := N) (m := m) hw
  refine hfit.of_le ?_
  rw [heq]
  split_ifs <;> omega

/-- Evaluate `compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n` (`∈ {0, 1, 2}`)
overflow-free in `Memory.Prog` (`¬ReadsWidth`). -/
def compGrowDeltaGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, n) => do
    let old_iw ← compItemWordsGenProg (cp, n)
    let new_iw ← compItemWordsGenProg (cp, n + 1)
    pure (new_iw - old_iw)

@[simp] theorem clientResult_compGrowDeltaGenProg {U V w N n : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compGrowDeltaGenProg (mkCompParams U V w N, n)) =
      compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n := by
  dsimp only [compGrowDeltaGenProg]
  rw [prog_clientResult_bind, clientResult_compItemWordsGenProg hw,
    clientState_compItemWordsGenProg, prog_clientResult_bind,
    clientResult_compItemWordsGenProg hw, clientState_compItemWordsGenProg,
    prog_clientResult_pure]

theorem clientState_compGrowDeltaGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compGrowDeltaGenProg d) = s := by
  rcases d with ⟨cp, n⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compGrowDeltaGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compItemWordsGenProg, prog_runClient_state_pure]

@[simp] theorem memoryCost_compGrowDeltaGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compGrowDeltaGenProg d) s = 0 := by
  rcases d with ⟨cp, n⟩
  dsimp only [compGrowDeltaGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_compItemWordsGenProg,
    runClient_state_compItemWordsGenProg, memoryCost_pure, zero_add]

/-- Precondition for `compGrowDeltaGenProg`. -/
@[expose] def CompGrowDeltaPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, n), _s =>
    ∃ U V N,
      0 < w ∧ n < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      Fits w (4 + compactedItemWords U V w N (n + 1))

theorem realizesBounded_compGrowDeltaGen :
    RealizesBounded .exact compGrowDeltaGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGrowDeltaPre (fun _ _ => 0) := by
  have hiw := realizesBounded_compItemWordsGen
  realize
  all_goals (
    rcases d with ⟨cp, n⟩
    obtain ⟨U, V, N, hw, hnN, hnU, hU, hV, rfl, hfit1⟩ := h
    have hfit0 : Fits w (4 + compactedItemWords U V w N n) :=
      hfit1.of_le (Nat.add_le_add_left (compactedItemWords_mono (Nat.le_succ n)) 4))
  · exact ⟨U, V, N, hw, hnU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit0⟩
  · exact lt_of_le_of_lt (by omega) hU
  · rw [clientState_compItemWordsGenProg]
    exact ⟨U, V, N, hw, hnU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit1⟩
  · rw [clientState_compItemWordsGenProg]
    dsimp only
    rw [clientResult_compItemWordsGenProg hw, clientResult_compItemWordsGenProg hw]
    exact compactedItemWords_mono (Nat.le_succ n)

theorem validProg_compGrowDeltaGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compGrowDeltaGenProg d) := by
  rcases d with ⟨cp, n⟩
  dsimp only [compGrowDeltaGenProg]
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  rw [clientState_compItemWordsGenProg]
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  exact validProg_pure _

/-- Evaluate `compactedItemWords U V w N n - compactedItemWords U V w N (n - 1)` (`∈ {0, 1, 2}`)
overflow-free in `Memory.Prog` (`¬ReadsWidth`). -/
def compShrinkDeltaGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, n) => do
    let old_iw ← compItemWordsGenProg (cp, n)
    let new_iw ← compItemWordsGenProg (cp, n - 1)
    pure (old_iw - new_iw)

@[simp] theorem clientResult_compShrinkDeltaGenProg {U V w N n : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compShrinkDeltaGenProg (mkCompParams U V w N, n)) =
      compactedItemWords U V w N n - compactedItemWords U V w N (n - 1) := by
  dsimp only [compShrinkDeltaGenProg]
  rw [prog_clientResult_bind, clientResult_compItemWordsGenProg hw,
    clientState_compItemWordsGenProg, prog_clientResult_bind,
    clientResult_compItemWordsGenProg hw, clientState_compItemWordsGenProg,
    prog_clientResult_pure]

theorem clientState_compShrinkDeltaGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compShrinkDeltaGenProg d) = s := by
  rcases d with ⟨cp, n⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compShrinkDeltaGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compItemWordsGenProg, prog_runClient_state_pure]

@[simp] theorem memoryCost_compShrinkDeltaGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compShrinkDeltaGenProg d) s = 0 := by
  rcases d with ⟨cp, n⟩
  dsimp only [compShrinkDeltaGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_compItemWordsGenProg,
    runClient_state_compItemWordsGenProg, memoryCost_pure, zero_add]

/-- Precondition for `compShrinkDeltaGenProg`. -/
@[expose] def CompShrinkDeltaPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, n), _s =>
    ∃ U V N,
      0 < w ∧ 1 ≤ n ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      Fits w (4 + compactedItemWords U V w N n)

theorem realizesBounded_compShrinkDeltaGen :
    RealizesBounded .exact compShrinkDeltaGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompShrinkDeltaPre (fun _ _ => 0) := by
  have hiw := realizesBounded_compItemWordsGen
  realize
  all_goals (
    rcases d with ⟨cp, n⟩
    obtain ⟨U, V, N, hw, hn1, hnU, hU, hV, rfl, hfit0⟩ := h
    have hfit1 : Fits w (4 + compactedItemWords U V w N (n - 1)) :=
      hfit0.of_le (Nat.add_le_add_left (compactedItemWords_mono (Nat.sub_le n 1)) 4))
  · exact ⟨U, V, N, hw, hnU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit0⟩
  · exact hn1
  · rw [clientState_compItemWordsGenProg]
    exact ⟨U, V, N, hw, hnU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit1⟩
  · rw [clientState_compItemWordsGenProg]
    dsimp only
    rw [clientResult_compItemWordsGenProg hw, clientResult_compItemWordsGenProg hw]
    exact compactedItemWords_mono (Nat.sub_le n 1)

theorem validProg_compShrinkDeltaGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compShrinkDeltaGenProg d) := by
  rcases d with ⟨cp, n⟩
  dsimp only [compShrinkDeltaGenProg]
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  rw [clientState_compItemWordsGenProg]
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  exact validProg_pure _

/-- Shared Feistel `(b, q, m)` coordinate extractor from `(u, h_q)` (`¬ReadsWidth`). -/
def compFeistelCoordsProg : CompParams × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (cp, (u, h_q)) => do
    let b_bits ← pure (cpBucketBits cp)
    let b_mask ← pure (cpBucketMask cp)
    let u_low ← pure (u &&& b_mask)
    let h_low ← pure (h_q &&& b_mask)
    let b ← pure (h_low ^^^ u_low)
    let q ← pure (u >>> b_bits)
    let m ← pure (h_q >>> b_bits)
    pure ((b, q), m)

theorem clientResult_compFeistelCoordsProg (U V w N u h_q : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compFeistelCoordsProg (mkCompParams U V w N, (u, h_q))) =
      ((feistelBucket (bucketBits N) (fun _ => h_q) u, keyQuotient (bucketBits N) u),
        h_q >>> bucketBits N) := by
  dsimp only [compFeistelCoordsProg, cpBucketBits_mk, cpBucketMask_mk]
  simp only [pure_bind, prog_clientResult_pure]
  rw [and_mask_xor_eq_feistelBucket (bucketBits N) u h_q, Nat.shiftRight_eq_div_pow]
  rfl

theorem clientState_compFeistelCoordsProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compFeistelCoordsProg d) = s := by
  rcases d with ⟨cp, ⟨u, h_q⟩⟩; rfl

@[simp] theorem runClient_state_compFeistelCoordsProg
    (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compFeistelCoordsProg d))) = s :=
  clientState_compFeistelCoordsProg d s

@[simp] theorem memoryCost_compFeistelCoordsProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compFeistelCoordsProg d) s = 0 := by
  rcases d with ⟨cp, ⟨u, h_q⟩⟩; rfl

/-- Precondition for `compFeistelCoordsProg`. -/
@[expose] def CompFeistelCoordsPre (w : ℕ) : CompParams × (ℕ × ℕ) → Memory.State → Prop
  | (cp, (u, h_q)), _s =>
    Fits w u ∧ Fits w h_q ∧ Fits w (cpBucketBits cp) ∧ Fits w (cpBucketMask cp)

theorem realizesBounded_compFeistelCoords :
    RealizesBounded .exact compFeistelCoordsProg
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompFeistelCoordsPre (fun _ _ => 0) := by
  realize
  rcases d with ⟨cp, ⟨u, h_q⟩⟩
  obtain ⟨hu, hhq, _, hmask⟩ := h
  refine Nat.xor_lt_two_pow ?_ ?_
  · exact lt_of_le_of_lt Nat.and_le_right hmask
  · exact lt_of_le_of_lt Nat.and_le_right hmask

theorem validProg_compFeistelCoords {w : ℕ} (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    ValidProg w 0 s (compFeistelCoordsProg d) := by
  rcases d with ⟨cp, ⟨u, h_q⟩⟩
  exact fun _ => trivial

theorem fits_compFeistelCoords {U V w N u h_q metaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hu : Fits w u) (hhq : h_q < 2 ^ totalMicroBits N) :
    CompFeistelCoordsPre w (mkCompParams U V w N, (u, h_q)) s := by
  have hcp := fits_mkCompParams (U := U) (V := V) (w := w) (N := N) hw hnU hU hV hfit_off
  have hmicro_le_w : totalMicroBits N ≤ w := by
    have htot_le : totalMicroBuckets N ≤ max N 1 := totalMicroBuckets_le N
    have hmax_lt : max N 1 < 2 ^ w := max_n_one_lt_two_pow_w hw hnU hU
    have hpow : 2 ^ totalMicroBits N ≤ max N 1 := htot_le
    by_contra hgt
    have hgt' : w < totalMicroBits N := Nat.lt_of_not_ge hgt
    have := Nat.pow_le_pow_right two_pos (Nat.succ_le_of_lt hgt')
    have : 2 ^ w < 2 ^ (w + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self w)
    omega
  exact ⟨hu, lt_of_lt_of_le hhq (Nat.pow_le_pow_right two_pos hmicro_le_w),
    hcp ⟨20, by decide⟩, hcp ⟨21, by decide⟩⟩

/-! ## Section 2: Physical Value Update and Last-Slot Payload Copy -/

/-- In-place quotient update at `slotOf N gm b j` preserves `FixedCoupled`. -/
private theorem FixedCoupled.writeQuot_slotOf {metaBase itemBase U V w N b j q : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hq_lt : q < 2 ^ quotientBits U N) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let g := slotOf N gm b j
    let d := denseOfPhys N gm td g
    let s' : Memory.State :=
      { mem := writeCompQuot itemBase U V w N s.mem d q, frontier := s.frontier }
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g), q))
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro gm td g d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hg_lt : g < N := (slotOf_lt_and_injective hslot).1 b hb j hj
  have htd := fun hb_pos => hcpl.tailDenseInv hb_pos
  obtain ⟨hd_lt, _, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb hj
  have hvirt := physOfDense_denseOfPhys_slotOf hslot htd hb hj
  obtain ⟨hlm_f, hgm_f, htd_f, hdt_f⟩ :=
    writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N) (q := q)
      hw hitem hd_lt s.mem
  obtain ⟨_, _, hq_fix, hv_fix, hl_fix, hg_fix⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hq_lt s_fix
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
    rw [hdt_f, hq_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      rw [compQuotAt_writeCompQuot_self s.mem hd_lt hq_lt]
      change q = Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) g q (physOfDense N gm (compDTAt metaBase U w N s.mem) d)
      rw [hvirt, Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq]
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
      exact hcpl.quot_eq d' hd'
  · rw [hgm_f] at hd' ⊢
    rw [compValAt_writeCompQuot hw s.mem, hdt_f, hv_fix]
    exact hcpl.val_eq d' hd'

/-- Resolve physical slot `phys` through `denseOfPhysGenProg` and overwrite its value with `v_new`
(`¬ReadsWidth`). -/
def compWritePhysValGenProg : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), phys), v_new) => do
    let d_idx ← denseOfPhysGenProg ((cp, metaBase), phys)
    writeCompValGenProg (((cp, itemBase), d_idx), v_new)

private theorem memoryCost_compWritePhysValGenProg_le
    (d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compWritePhysValGenProg d) s ≤ 8 := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
  dsimp only [compWritePhysValGenProg]
  simp only [Realization.memoryCost_bind', runClient_state_denseOfPhysGenProg,
    memoryCost_writeCompValGenProg]
  have h1 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase), phys) s
  omega

/-- Precondition for `compWritePhysValGenProg`. -/
@[expose] def CompWritePhysValPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), phys), _v_new), s =>
    CompReadPhysItemPre w ((cp, (metaBase, itemBase)), phys) s

private theorem compWritePhysValGenProg_effect {metaBase itemBase U V w N m_cap b j v_new : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hv_lt : v_new < 2 ^ valBits V) :
    let phys := slotOf N (compGmAt metaBase U w N s.mem) b j
    let s' := (Memory.spec 0).clientState s
      (compWritePhysValGenProg (((mkCompParams U V w N, (metaBase, itemBase)), phys), v_new))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, phys), v_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro phys s' s_fix'
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_cap hb hj
  have hd_cap : denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem)
      phys < m_cap := lt_of_lt_of_le hd_lt hm_cap
  have hs'_eq : s' = ⟨writeCompVal itemBase U V w N s.mem
      (denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) phys) v_new,
      s.frontier⟩ := by
    dsimp only [s', compWritePhysValGenProg, phys]
    rw [StateTransitionSpec.clientState_bind, clientState_denseOfPhysGenProg,
      clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj,
      clientState_writeCompValGenProg]
  rw [hs'_eq]
  exact ⟨⟨rfl, fun a _ hi => writeCompVal_outside henv.pos_w hd_cap s.mem hi⟩,
    hcpl.writeVal_slotOf henv.pos_w henv.meta_le_item hslot hb hj hv_lt⟩

theorem realizesBounded_compWritePhysValGen :
    RealizesBounded .exact compWritePhysValGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWritePhysValPre (fun _ _ => 0) := by
  have hdp := realizesBounded_denseOfPhysGen
  have hwv := realizesBounded_writeCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
    obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
      hb, hj, rfl⟩ := h)
  · exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj
  · rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
    obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
    exact ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

theorem validProg_compWritePhysValGen {w : ℕ} {d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ}
    {s : Memory.State} (h : CompWritePhysValPre w d s) :
    ValidProg w 0 s (compWritePhysValGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
  obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items, hb, hj, rfl⟩ := h
  dsimp only [compWritePhysValGenProg]
  refine validProg_bind (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  exact validProg_writeCompValGen ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

private def compResolveCopyPairProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), phys_del) => do
    let phys_last ← compLastSlotOfGenProg ((cp, metaBase), b)
    let d_src ← denseOfPhysGenProg ((cp, metaBase), phys_last)
    let d_dst ← denseOfPhysGenProg ((cp, metaBase), phys_del)
    pure (d_src, d_dst)

private theorem clientState_compResolveCopyPairProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compResolveCopyPairProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, phys_del⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compResolveCopyPairProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compLastSlotOfGenProg, runClient_state_denseOfPhysGenProg,
    prog_runClient_state_pure]

/-- Precondition for `compResolveCopyPairProg` and `compCopyLastPayloadGenProg`. -/
private def CompCopyLastPayloadPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), phys_del), s =>
    ∃ U V N m_items s_fix j_del,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      j_del < bCount N (compGmAt metaBase U w N s.mem) b ∧
      phys_del = slotOf N (compGmAt metaBase U w N s.mem) b j_del

private def CompResolveCopyPairPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), phys_del), s =>
    ∃ itemBase, CompCopyLastPayloadPre w (((cp, (metaBase, itemBase)), b), phys_del) s

private theorem realizesBounded_compResolveCopyPair :
    RealizesBounded .exact compResolveCopyPairProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveCopyPairPre (fun _ _ => 0) := by
  have hls := realizesBounded_compLastSlotOfGen
  have hdp := realizesBounded_denseOfPhysGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, phys_del⟩
    obtain ⟨itemBase, U, V, N, m_items, s_fix, j_del, rfl, henv, hcpl, hslot, hm_items,
      hb, hj_del, rfl⟩ := h
    have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hj_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
        bCount N (compGmAt metaBase U w N s.mem) b := by omega)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb, hbc⟩
  · rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
    exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj_last
  · rw [clientState_denseOfPhysGenProg, clientState_compLastSlotOfGenProg]
    exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj_del

/-- Copy `(quot, val)` from the last logical slot `bCount N gm b - 1` of bucket `b` into
`phys_del = slotOf N gm b j_del` in compacted representation (`¬ReadsWidth`). -/
private def compCopyLastPayloadGenProg : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), b), phys_del) => do
    let pair ← compResolveCopyPairProg (((cp, metaBase), b), phys_del)
    copyCompItemGenProg ((cp, itemBase), pair)

private theorem memoryCost_compCopyLastPayloadGenProg_le
    (d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compCopyLastPayloadGenProg d) s ≤ 24 := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, phys_del⟩
  dsimp only [compCopyLastPayloadGenProg, compResolveCopyPairProg]
  simp only [Realization.memoryCost_bind', runClient_state_compLastSlotOfGenProg,
    runClient_state_denseOfPhysGenProg, memoryCost_pure, memoryCost_copyCompItemGenProg]
  have h1 := memoryCost_compLastSlotOfGenProg_le ((cp, metaBase), b) s
  have h2 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase),
    (Memory.spec 0).clientResult s (compLastSlotOfGenProg ((cp, metaBase), b))) s
  have h3 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase), phys_del) s
  omega

private theorem clientResult_compResolveCopyPairProg {metaBase itemBase U V w N m_items b j_del : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj_del : j_del < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    (Memory.spec 0).clientResult s
        (compResolveCopyPairProg
          (((mkCompParams U V w N, metaBase), b), slotOf N gm b j_del)) =
      (denseOfPhys N gm td (slotOf N gm b (bCount N gm b - 1)),
        denseOfPhys N gm td (slotOf N gm b j_del)) := by
  intro gm td
  have hbc : 1 ≤ bCount N gm b := Nat.one_le_of_lt hj_del
  have hj_last : bCount N gm b - 1 < bCount N gm b := Nat.sub_lt hbc Nat.one_pos
  dsimp only [compResolveCopyPairProg, gm, td]
  rw [prog_clientResult_bind, clientResult_compLastSlotOfGenProg hslot hb hbc,
    clientState_compLastSlotOfGenProg, prog_clientResult_bind,
    clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_last,
    clientState_denseOfPhysGenProg, prog_clientResult_bind,
    clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_del,
    clientState_denseOfPhysGenProg, prog_clientResult_pure]

private theorem compCopyLastPayloadGenProg_effect {metaBase itemBase U V w N m_cap b j_del : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hj_del : j_del < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let phys_del := slotOf N gm b j_del
    let s' := (Memory.spec 0).clientState s
      (compCopyLastPayloadGenProg (((mkCompParams U V w N, (metaBase, itemBase)), b), phys_del))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (copyLastPayloadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), phys_del))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro gm phys_del s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hbc : 1 ≤ bCount N gm b := Nat.one_le_of_lt hj_del
  have hj_last : bCount N gm b - 1 < bCount N gm b := Nat.sub_lt hbc Nat.one_pos
  set j_last := bCount N gm b - 1
  set phys_last := slotOf N gm b j_last
  set td := compTDAt metaBase U w N s.mem
  set d_src := denseOfPhys N gm td phys_last
  set d_dst := denseOfPhys N gm td phys_del
  obtain ⟨hd_src_lt, hq_src, hv_src⟩ :=
    hcpl.quot_val_at_slotOf hslot (le_refl (epochTotalSlots N gm)) hb hj_last
  obtain ⟨hd_dst_lt, _, _⟩ :=
    hcpl.quot_val_at_slotOf hslot (le_refl (epochTotalSlots N gm)) hb hj_del
  have hd_src_cap : d_src < m_cap := lt_of_lt_of_le hd_src_lt hm_cap
  have hd_dst_cap : d_dst < m_cap := lt_of_lt_of_le hd_dst_lt hm_cap
  have hs'_eq : s' = ⟨writeCompVal itemBase U V w N
      (writeCompQuot itemBase U V w N s.mem d_dst
        (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last))
      d_dst (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last),
      s.frontier⟩ := by
    dsimp only [s', compCopyLastPayloadGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compResolveCopyPairProg,
      clientResult_compResolveCopyPairProg henv hcpl hslot hb hj_del,
      clientState_copyCompItemGenProg (m_items := epochTotalSlots N gm) hd_src_lt,
      hq_src, hv_src]
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hbc_fix : 1 ≤ bCount N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
    rw [← hcpl.gm_eq]; exact hbc
  have hphys_last_lt : phys_last < N := (slotOf_lt_and_injective hslot).1 b hb j_last hj_last
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, phys_del),
            quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)))
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((0, phys_del),
          valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)) := by
    dsimp only [s_fix']
    unfold copyLastPayloadProg copyLastPayloadGenProg
    simp only [lastSlotOfGenProg_mk, readQuotGenProg_mk, readValGenProg_mk,
      writeQuotGenProg_mk, writeValGenProg_mk]
    rw [StateTransitionSpec.clientState_bind, clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (0, b) s_fix hslot_fix hb hbc_fix]
    simp only [← hcpl.gm_eq]
    rw [StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s_fix hphys_last_lt,
      StateTransitionSpec.clientState_bind, clientState_readValProg,
      clientResult_readValProg s_fix hphys_last_lt,
      StateTransitionSpec.clientState_bind]
  have hq_lt : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last <
      2 ^ quotientBits U N := quotAt_lt _ _ _ _ _ _ _
  have hv_lt : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last <
      2 ^ valBits V := valAt_lt _ _ _ _ _ _ _ _
  have hcpl1 := hcpl.writeQuot_slotOf henv.pos_w henv.meta_le_item hslot hb hj_del hq_lt
  obtain ⟨_, hgm1, htd1, _⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N)
    (q := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)
    henv.pos_w henv.meta_le_item hd_dst_lt s.mem
  set s₁ : Memory.State := {
    mem := writeCompQuot itemBase U V w N s.mem d_dst
      (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last),
    frontier := s.frontier }
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hj_del1 : j_del < bCount N (compGmAt metaBase U w N s₁.mem) b := hgm1.symm ▸ hj_del
  have hcpl2 := hcpl1.writeVal_slotOf henv.pos_w henv.meta_le_item hslot1 hb hj_del1 hv_lt
  dsimp only [s₁] at hcpl2
  simp only [hgm1, htd1] at hcpl2
  rw [hs'_eq, hs_fix'_eq]
  refine ⟨⟨rfl, fun a _ hi => ?_⟩, hcpl2⟩
  exact (writeCompVal_outside henv.pos_w hd_dst_cap _ hi).trans
    (writeCompQuot_outside henv.pos_w hd_dst_cap s.mem hi)

private theorem realizesBounded_compCopyLastPayloadGen :
    RealizesBounded .exact compCopyLastPayloadGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompCopyLastPayloadPre (fun _ _ => 0) := by
  have hrp := realizesBounded_compResolveCopyPair
  have hcp := realizesBounded_copyCompItemGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, phys_del⟩
    obtain ⟨U, V, N, m_items, s_fix, j_del, rfl, henv, hcpl, hslot, hm_items,
      hb, hj_del, rfl⟩ := h)
  · exact ⟨itemBase, U, V, N, m_items, s_fix, j_del, rfl, henv, hcpl, hslot, hm_items,
      hb, hj_del, rfl⟩
  · rw [clientState_compResolveCopyPairProg,
      clientResult_compResolveCopyPairProg henv hcpl hslot hb hj_del]
    have hj_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
        bCount N (compGmAt metaBase U w N s.mem) b := by omega
    obtain ⟨hd_src_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj_last
    obtain ⟨hd_dst_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj_del
    exact ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_src_lt hm_items,
      lt_of_lt_of_le hd_dst_lt hm_items⟩

private theorem validProg_compCopyLastPayloadGen {w : ℕ} {d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ}
    {s : Memory.State} (h : CompCopyLastPayloadPre w d s) :
    ValidProg w 0 s (compCopyLastPayloadGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, phys_del⟩
  obtain ⟨U, V, N, m_items, s_fix, j_del, rfl, henv, hcpl, hslot, hm_items,
    hb, hj_del, rfl⟩ := h
  have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
  have hj_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
      bCount N (compGmAt metaBase U w N s.mem) b := by omega
  dsimp only [compCopyLastPayloadGenProg, compResolveCopyPairProg]
  simp only [bind_assoc]
  refine validProg_bind
    (validProg_compLastSlotOfGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb, hbc⟩) ?_
  rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
  refine validProg_bind
    (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj_last)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_last]
  refine validProg_bind
    (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj_del)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_del]
  simp only [pure_bind]
  obtain ⟨hd_src_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj_last
  obtain ⟨hd_dst_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj_del
  exact validProg_copyCompItemGen
    ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_src_lt hm_items,
      lt_of_lt_of_le hd_dst_lt hm_items⟩

/-! ## Section 3: Compacted Feistel-Dispatched Query and Split Insertion -/

/-- Feistel-dispatched compacted dictionary lookup (`¬ReadsWidth`):
`d = ((cp, (metaBase, itemBase)), (u, h_q))`, returning `Option ℕ`. -/
def compQueryWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (Option ℕ)
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    compQueryBodyGenProg (((cp, (metaBase, itemBase)), c.1), c.2)

/-- Precondition for `compQueryWithHashGenProg`, `compInsertSearchWithHashGenProg`, and
`compDeletePrepWithHashGenProg`. -/
@[expose] def CompQueryWithHashPre (w : ℕ) :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), (u, h_q)), s =>
    CompFeistelCoordsPre w (cp, (u, h_q)) s ∧
    CompSearchBucketPre w
      ((((cp, (metaBase, itemBase)),
        ((h_q &&& cpBucketMask cp) ^^^ (u &&& cpBucketMask cp), u >>> cpBucketBits cp)),
        h_q >>> cpBucketBits cp)) s

theorem realizesBounded_compQueryWithHashGen :
    RealizesBounded .exact compQueryWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Option ℕ))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hqb := realizesBounded_compQueryBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compQueryWithHashGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compQueryWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨hfc_pre, hsb_pre⟩ := h
  dsimp only [compQueryWithHashGenProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  exact validProg_compQueryBodyGen hsb_pre

private def compPackInsertSearchResProg :
    ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | (((found, _j), phys), ((b, _q), m)) => pure ((found, phys), (b, m))

private theorem clientState_compPackInsertSearchResProg
    (x : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compPackInsertSearchResProg x) = s := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

private theorem clientResult_compPackInsertSearchResProg
    (res : (ℕ × ℕ) × ℕ) (b q m : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compPackInsertSearchResProg (res, ((b, q), m))) =
      ((res.1.1, res.2), (b, m)) := by
  rcases res with ⟨⟨_, _⟩, _⟩; rfl

private theorem memoryCost_compPackInsertSearchResProg
    (x : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (compPackInsertSearchResProg x) s = 0 := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

private theorem realizesBounded_compPackInsertSearchRes :
    RealizesBounded .exact compPackInsertSearchResProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Phase 1 of split compacted insertion (`¬ReadsWidth`):
computes Feistel coordinates `(b, q, m)` from `(u, h_q)`, searches bucket `(b, m)` for `q`, and
returns `((found, phys), (b, m))`. -/
def compInsertSearchWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    let res ← compSearchBucketGenProg (((cp, (metaBase, itemBase)), c.1), c.2)
    compPackInsertSearchResProg (res, c)

theorem realizesBounded_compInsertSearchWithHashGen :
    RealizesBounded .exact compInsertSearchWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hsb := realizesBounded_compSearchBucketGen
  have hpk := realizesBounded_compPackInsertSearchRes
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compInsertSearchWithHashGen {w : ℕ}
    {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compInsertSearchWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨_, hsb_pre⟩ := h
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := hsb_pre
  have hst := (compSearchBucketGenProg_spec (q_target := u >>> cpBucketBits (mkCompParams U V w N))
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  dsimp only [compInsertSearchWithHashGenProg, compPackInsertSearchResProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  refine validProg_bind (validProg_compSearchBucketGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rcases (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)),
          ((h_q &&& cpBucketMask (mkCompParams U V w N)) ^^^
            (u &&& cpBucketMask (mkCompParams U V w N)),
            u >>> cpBucketBits (mkCompParams U V w N))),
          h_q >>> cpBucketBits (mkCompParams U V w N)))) with ⟨⟨found, j⟩, phys⟩
  rcases (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u, h_q))) with ⟨⟨b0, q0⟩, m0⟩
  exact validProg_pure _

/-- Phase 2b (miss path) of split compacted insertion (`¬ReadsWidth`):
after `growZeroCode` has extended `s.frontier` to cover `n + 1` dense items, appends `(q, v)` to
bucket `b` (`q = u >>> cpBucketBits cp`) and prepends the new slot to micro-chain `(b, m)` if
indexed. -/
def compInsertAppendNewGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), (b, m)), (u, v)) => do
    let q ← compExtractQuotGenProg (cp, u)
    let j_new ← readCompBucketCountGenProg ((cp, metaBase), b)
    compPushBackSlotGenProg ((((cp, (metaBase, itemBase)), b), q), v)
    compPrependIfIndexedGenProg (((cp, metaBase), (b, m)), j_new)

/-- Precondition for `compInsertAppendNewGenProg`. -/
@[expose] def CompInsertAppendNewPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), (b, m)), (u, v)), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      Fits w u ∧
      u >>> bucketBits N < 2 ^ quotientBits U N ∧
      v < 2 ^ valBits V ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N

private theorem gmAt_prependIfIndexedProg {U V w n_max h_space base b m j_new : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (s : Memory.State)
    (hold : lmHead n_max (lmAt base U V w n_max h_space s.mem) b m ≤ effBucketCap n_max) :
    gmAt base U V w n_max h_space
      ((Memory.spec 0).clientState s
        (prependIfIndexedProg U V w n_max h_space (((base, b), m), j_new))).mem =
      gmAt base U V w n_max h_space s.mem := by
  unfold prependIfIndexedProg prependIfIndexedGenProg
  simp only [p_minCap_mk, lmPrependGenProg_mk, pure_bind]
  split_ifs with hlt
  · obtain ⟨hj_n, hj_cap⟩ := lt_min_iff.mp hlt
    exact (lmPrependProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) hw hb hm hj_cap hj_n hold).2.2.2.2.1
  · rfl

private theorem compInsertAppendNewGenProg_effect {metaBase itemBase U V w N m_cap b m u v : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N)
    (hv_lt : v < 2 ^ valBits V)
    (hold : lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N) :
    let q := keyQuotient (bucketBits N) u
    let j_new := bCount N (compGmAt metaBase U w N s.mem) b
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), (b, m)), (u, v)))
    let s' := (Memory.spec 0).clientState s (compInsertAppendNewGenProg d)
    let s_fix' := (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v)))
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compInsertAppendNewGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 200 := by
  intro q j_new d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  obtain ⟨hfr_pb, hcpl_pb, hcost_pb⟩ :=
    compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt hv_lt
  set s₁ := (Memory.spec 0).clientState s
    (compPushBackSlotGenProg ((((mkCompParams U V w N, (metaBase, itemBase)), b), q), v))
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v))
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have htot_fix : totalSlots N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rw [← hcpl.gm_eq]; exact htot
  have eff_pb_fix := pushBackSlotProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (q_val := q) (v_val := v)
    hwg s_fix hslot_fix hb htot_fix hq_lt hv_lt
  have hlm_s₁ : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem :=
    hcpl_pb.lm_eq.trans (eff_pb_fix.2.2.1.trans hcpl.lm_eq.symm)
  have hold₁ : lmHead N (compLmAt metaBase U w N s₁.mem) b m ≤ effBucketCap N := by
    rw [hlm_s₁]; exact hold
  have hold_fix₁ :
      lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem) b m ≤
        effBucketCap N := by
    rw [← hcpl_pb.lm_eq]; exact hold₁
  obtain ⟨hfr_pr, hcpl_pr⟩ := compPrependIfIndexedGenProg_effect
    (m_cap := m_cap) (j_new := j_new) henv.pos_w henv.meta_le_item hcpl_pb hb hm hold₁
  have hgm_pr_fix := gmAt_prependIfIndexedProg (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (m := m) (j_new := j_new)
    hwg hb hm s_fix₁ hold_fix₁
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (compPrependIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_new)) := by
    dsimp only [s', d, compInsertAppendNewGenProg, s₁, q, j_new]
    rw [StateTransitionSpec.clientState_bind, clientState_compExtractQuotGenProg,
      clientResult_compExtractQuotGenProg, StateTransitionSpec.clientState_bind,
      clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb,
      StateTransitionSpec.clientState_bind]
  have hgm'_eq : compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s₁.mem := by
    rw [hs'_eq]
    exact hcpl_pr.gm_eq.trans (hgm_pr_fix.trans hcpl_pb.gm_eq.symm)
  have hcost_tot : memoryCost (compInsertAppendNewGenProg d) s ≤
      22 + memoryCost (compPushBackSlotGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), b), q), v)) s := by
    dsimp only [d, compInsertAppendNewGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compExtractQuotGenProg _ s) _,
      memoryCost_compExtractQuotGenProg, clientResult_compExtractQuotGenProg,
      memoryCost_bind_of_clientState_eq (clientState_readCompBucketCountGenProg _ s) _,
      clientResult_readCompBucketCountGenProg hb, Realization.memoryCost_bind']
    have hc1 := memoryCost_readCompBucketCountGenProg_le ((mkCompParams U V w N, metaBase), b) s
    have hc2 := memoryCost_compPrependIfIndexedGenProg_le
      (((mkCompParams U V w N, metaBase), (b, m)), j_new) s₁
    dsimp only [s₁, q, j_new] at hc2 ⊢
    omega
  rw [hgm'_eq]
  exact ⟨by rw [hs'_eq]; exact hfr_pb.trans hfr_pr,
    by rw [hs'_eq]; exact hcpl_pr,
    by dsimp only [s₁, q] at hcost_pb hcost_tot ⊢; omega⟩

theorem realizesBounded_compInsertAppendNewGen :
    RealizesBounded .exact compInsertAppendNewGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompInsertAppendNewPre (fun _ _ => 0) := by
  have heq := realizesBounded_compExtractQuotGen
  have hbc := realizesBounded_readCompBucketCountGen
  have hpb := realizesBounded_compPushBackSlotGen
  have hpr := realizesBounded_compPrependIfIndexedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, m⟩⟩, ⟨u, v⟩⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, hu_fit, hq_lt, hv_lt, henv, hcpl, hslot,
      hb, hm, htot, hm_cap, hold⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    have hcp_fit := fits_mkCompParams (U := U) (V := V) (w := w) (N := N)
      henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_meta
    have hq_eq : keyQuotient (bucketBits N) u = u >>> bucketBits N :=
      (Nat.shiftRight_eq_div_pow u (bucketBits N)).symm)
  · dsimp only; exact ⟨hu_fit, hcp_fit ⟨20, by decide⟩⟩
  · rw [clientState_compExtractQuotGenProg]
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb⟩
  · rw [clientState_readCompBucketCountGenProg, clientState_compExtractQuotGenProg,
      clientResult_compExtractQuotGenProg, hq_eq]
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩
  · rw [clientState_compExtractQuotGenProg, clientResult_compExtractQuotGenProg,
      clientState_readCompBucketCountGenProg]
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hq_lt' : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N := by rwa [hq_eq]
    obtain ⟨hfr_pb, hcpl_pb, _⟩ :=
      compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
    have hslot_fix : SlotStoreInv N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
      rw [← hcpl.gm_eq]; exact hslot
    have htot_fix : totalSlots N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
      rw [← hcpl.gm_eq]; exact htot
    have eff_pb_fix := pushBackSlotProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
      (q_val := keyQuotient (bucketBits N) u) (v_val := v)
      hwg s_fix hslot_fix hb htot_fix hq_lt' hv_lt
    set s₁ := (Memory.spec 0).clientState s
      (compPushBackSlotGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), b), keyQuotient (bucketBits N) u), v))
    have hlm_s₁ : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem :=
      hcpl_pb.lm_eq.trans (eff_pb_fix.2.2.1.trans hcpl.lm_eq.symm)
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr_pb.frontier_eq.symm ▸ henv.meta_le_frontier, hb, hm, by rw [hlm_s₁]; exact hold⟩

theorem validProg_compInsertAppendNewGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompInsertAppendNewPre w d s) :
    ValidProg w 0 s (compInsertAppendNewGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, m⟩⟩, ⟨u, v⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, _hu_fit, hq_lt, hv_lt, henv, hcpl, hslot,
    hb, hm, htot, hm_cap, hold⟩ := h
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hq_eq : keyQuotient (bucketBits N) u = u >>> bucketBits N :=
    (Nat.shiftRight_eq_div_pow u (bucketBits N)).symm
  have hq_lt' : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N := by rwa [hq_eq]
  dsimp only [compInsertAppendNewGenProg]
  refine validProg_bind (fun _ => trivial) ?_
  rw [clientState_compExtractQuotGenProg, clientResult_compExtractQuotGenProg]
  refine validProg_bind
    (validProg_readCompBucketCountGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb⟩) ?_
  rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb]
  refine validProg_bind
    (validProg_compPushBackSlotGen
      ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt', hv_lt⟩) ?_
  obtain ⟨hfr_pb, hcpl_pb, _⟩ :=
    compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have htot_fix : totalSlots N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rw [← hcpl.gm_eq]; exact htot
  have eff_pb_fix := pushBackSlotProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
    (q_val := keyQuotient (bucketBits N) u) (v_val := v)
    hwg s_fix hslot_fix hb htot_fix hq_lt' hv_lt
  set s₁ := (Memory.spec 0).clientState s
    (compPushBackSlotGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), b), keyQuotient (bucketBits N) u), v))
  have hlm_s₁ : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem :=
    hcpl_pb.lm_eq.trans (eff_pb_fix.2.2.1.trans hcpl.lm_eq.symm)
  exact validProg_compPrependIfIndexedGen
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr_pb.frontier_eq.symm ▸ henv.meta_le_frontier, hb, hm, by rw [hlm_s₁]; exact hold⟩

/-! ## Section 4: Compacted Two-Phase Deletion (`compDeletePrepWithHashGenProg`,
`compDeleteFinishWithHashGenProg`) -/

private def compDeletePrepFoundProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | (((cp, (metaBase, itemBase)), b), res) => do
    let phys_last ← compLastSlotOfGenProg ((cp, metaBase), b)
    let q_last ← compReadPhysQuotGenProg ((cp, (metaBase, itemBase)), phys_last)
    pure (res, q_last)

private def CompDeletePrepFoundPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), _res), s =>
    ∃ U V N m_items s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b

private theorem realizesBounded_compDeletePrepFound :
    RealizesBounded .exact compDeletePrepFoundProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompDeletePrepFoundPre (fun _ _ => 0) := by
  have hls := realizesBounded_compLastSlotOfGen
  have hrq := realizesBounded_compReadPhysQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, res⟩
    obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb, hbc⟩ := h)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb, hbc⟩
  · rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
    exact ⟨U, V, N, m_items, s_fix, b, bCount N (compGmAt metaBase U w N s.mem) b - 1,
      rfl, henv, hcpl, hslot, hm_items, hb, Nat.sub_lt hbc Nat.one_pos, rfl⟩

/-- Compacted Phase 1 of `delete` at bucket level (`¬ReadsWidth`):
searches bucket `(b, m)` for `q_target`, and if `found = 1`, reads `q_last` of the last slot in
bucket `b`; otherwise returns `(((0, 0), 0), 0)`. -/
private def compDeletePrepBodyGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | (((cp, (metaBase, itemBase)), (b, q_target)), m) => do
    let res ← compSearchBucketGenProg ((((cp, (metaBase, itemBase)), (b, q_target)), m))
    let z1 ← pure 1
    if sbFound res = z1 then
      compDeletePrepFoundProg (((cp, (metaBase, itemBase)), b), res)
    else do
      let z0 ← pure 0
      pure (((z0, z0), z0), z0)

private theorem compDeletePrepBodyGenProg_spec
    {metaBase itemBase U V w N m_items b q_target m : ℕ} {L : List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let prog := compDeletePrepBodyGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))
    let prog_fix := deletePrepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), m)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 20 + 12 * L.length + 10 * (bCount N gm b - effBucketCap N) := by
  intro gm prog prog_fix
  obtain ⟨hst_sb, hres_sb, hcost_sb⟩ := compSearchBucketGenProg_spec
    (q_target := q_target) henv hcpl hslot hm_items hb hm hchain hc_lt
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm hchain hc_lt
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hchain_fix : IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b) L := by
    change IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b) L
    rw [← hcpl.lm_eq]; exact hchain
  have hc_lt_fix : ∀ j ∈ L,
      j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b := by
    change ∀ j ∈ L,
      j < bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
    rw [← hcpl.gm_eq]; exact hc_lt
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_target), m)) = s_fix :=
    (searchBucketProg_spec
      (d := (((0, b), q_target), m))
      (ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V)
      hb hm hslot_fix hchain_fix hc_lt_fix).1
  rcases hres_eq : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres_eq] at hres_sb hfnd
  have hfix_eq : (Memory.spec 0).clientResult s_fix prog_fix =
      (Memory.spec 0).clientResult s_fix
        (if found = 1 then do
          let phys_last ← lastSlotOfProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)
          let q_last ← readQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) (0, phys_last)
          pure (((found, j_found), phys_found), q_last)
        else pure (((0, 0), 0), 0)) := by
    dsimp only [prog_fix, deletePrepProg, deletePrepGenProg]
    simp only [searchBucketGenProg_mk, lastSlotOfGenProg_mk, readQuotGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, hst_sb_fix, ← hres_sb]
  rw [hfix_eq]
  dsimp only [prog, compDeletePrepBodyGenProg, gm]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst_sb, hres_eq,
    StateTransitionSpec.clientResult_bind, hst_sb, hres_eq,
    memoryCost_bind_of_clientState_eq hst_sb _, hres_eq]
  dsimp only [sbFound]
  split_ifs with hf1
  · obtain ⟨hj_bc, _⟩ := hfnd hf1
    have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hj_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
        bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hbc_fix : 1 ≤ bCount N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
      rw [← hcpl.gm_eq]; exact hbc
    have hphys_last_lt : slotOf N (compGmAt metaBase U w N s.mem) b
        (bCount N (compGmAt metaBase U w N s.mem) b - 1) < N :=
      (slotOf_lt_and_injective hslot).1 b hb _ hj_last
    dsimp only [compDeletePrepFoundProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compLastSlotOfGenProg,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      StateTransitionSpec.clientState_bind, clientState_compReadPhysQuotGenProg,
      StateTransitionSpec.clientState_pure,
      StateTransitionSpec.clientResult_bind, clientState_compLastSlotOfGenProg,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      StateTransitionSpec.clientResult_bind, clientState_compReadPhysQuotGenProg,
      clientResult_compReadPhysQuot_slotOf hcpl henv hslot hm_items hb hj_last,
      StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_bind, clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (0, b) s_fix hslot_fix hb hbc_fix]
    simp only [← hcpl.gm_eq]
    rw [StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
      clientResult_readQuotProg s_fix hphys_last_lt,
      StateTransitionSpec.clientResult_pure,
      memoryCost_bind_of_clientState_eq (clientState_compLastSlotOfGenProg _ s) _,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      memoryCost_bind_of_clientState_eq (clientState_compReadPhysQuotGenProg _ s) _,
      memoryCost_pure]
    have hc1 := memoryCost_compLastSlotOfGenProg_le ((mkCompParams U V w N, metaBase), b) s
    have hc2 := memoryCost_compReadPhysQuotGenProg_le
      ((mkCompParams U V w N, (metaBase, itemBase)),
        slotOf N (compGmAt metaBase U w N s.mem) b
          (bCount N (compGmAt metaBase U w N s.mem) b - 1)) s
    exact ⟨trivial, rfl, by omega⟩
  · rw [StateTransitionSpec.clientState_pure, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_pure, memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩

private theorem realizesBounded_compDeletePrepBodyGen :
    RealizesBounded .exact compDeletePrepBodyGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompSearchBucketPre (fun _ _ => 0) := by
  have hsb := realizesBounded_compSearchBucketGen
  have hfd := realizesBounded_compDeletePrepFound
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
    obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
      hb, hm_lt, hchain, hc_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1)
  · exact ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩
  · exact fits_const_of_offCompItems hfit_meta (by decide)
  · have hst_b := (compSearchBucketGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
    have hfnd := searchBucket_found_slotOf (q_target := q_target)
      henv hcpl hslot hm_items hb hm_lt hchain hc_lt
    change CompDeletePrepFoundPre w _
      ((Memory.spec 0).clientState s
        (compSearchBucketGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))))
    rw [hst_b]
    dsimp only at hc
    rcases hres : (Memory.spec 0).clientResult s
        (compSearchBucketGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
      ⟨⟨found, j_found⟩, phys_found⟩
    rw [hres] at hfnd hc
    dsimp only [sbFound] at hc
    obtain ⟨hj_bc, _⟩ := hfnd hc
    exact ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb,
      Nat.one_le_of_lt hj_bc⟩

private theorem validProg_compDeletePrepBodyGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : CompSearchBucketPre w d s) : ValidProg w 0 s (compDeletePrepBodyGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := h
  have hst_sb := (compSearchBucketGenProg_spec (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt
  dsimp only [compDeletePrepBodyGenProg, compDeletePrepFoundProg]
  simp only [pure_bind]
  refine validProg_bind (validProg_compSearchBucketGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rw [hst_sb]
  rcases hres : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres] at hfnd
  dsimp only [sbFound]
  refine validProg_ite (fun hc => ?_) (fun _ => validProg_pure _)
  obtain ⟨hj_bc, _⟩ := hfnd hc
  have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
  refine validProg_bind
    (validProg_compLastSlotOfGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb, hbc⟩) ?_
  rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
  refine validProg_bind
    (validProg_compReadPhysQuotGen
      ⟨U, V, N, m_items, s_fix, b, bCount N (compGmAt metaBase U w N s.mem) b - 1,
        rfl, henv, hcpl, hslot, hm_items, hb, by omega, rfl⟩) ?_
  exact validProg_pure _

/-- Feistel-dispatched Phase 1 of compacted `delete` (`¬ReadsWidth`):
`d = ((cp, (metaBase, itemBase)), (u, h_q))`, returning `(((found, j_del), phys_del), q_last)`. -/
def compDeletePrepWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    compDeletePrepBodyGenProg (((cp, (metaBase, itemBase)), c.1), c.2)

theorem realizesBounded_compDeletePrepWithHashGen :
    RealizesBounded .exact compDeletePrepWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hdp := realizesBounded_compDeletePrepBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compDeletePrepWithHashGen {w : ℕ}
    {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compDeletePrepWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨_, hsb_pre⟩ := h
  dsimp only [compDeletePrepWithHashGenProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  exact validProg_compDeletePrepBodyGen hsb_pre

private def compDeleteSwapCopyProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), phys_del), (m_last, j_last)) => do
    compUnlinkIfIndexedGenProg (((cp, metaBase), (b, m_last)), j_last)
    compCopyLastPayloadGenProg (((cp, (metaBase, itemBase)), b), phys_del)

/-- Precondition for `compDeleteSwapGenProg`. -/
private def CompDeleteSwapPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m_last, j_last)), s =>
    ∃ U V N m_cap s_fix L,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap ∧
      b < numBuckets N ∧
      m_last < numMicroPerBucket N ∧
      j_del < j_last ∧
      j_last < bCount N (compGmAt metaBase U w N s.mem) b ∧
      phys_del = slotOf N (compGmAt metaBase U w N s.mem) b j_del ∧
      AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L ∧
      (j_last < effBucketCap N → j_last ∈ L b m_last)

private def CompDeleteSwapCopyPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), phys_del), (m_last, j_last)), s =>
    ∃ j_del, CompDeleteSwapPre w
      (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m_last, j_last))) s

private theorem realizesBounded_compDeleteSwapCopy :
    RealizesBounded .exact compDeleteSwapCopyProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompDeleteSwapCopyPre (fun _ _ => 0) := by
  have hu := realizesBounded_compUnlinkIfIndexedGen
  have hcp := realizesBounded_compCopyLastPayloadGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, phys_del⟩, ⟨m_last, j_last⟩⟩
    obtain ⟨j_del, U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩ := h
    have hbounds : j_last < effBucketCap N →
        lmPrev N (compLmAt metaBase U w N s.mem) b j_last ≤ effBucketCap N ∧
        lmNext N (compLmAt metaBase U w N s.mem) b j_last ≤ effBucketCap N := fun hj_cap => by
      rw [hcpl.lm_eq]
      exact ⟨(hval.1 b hb m_last hm_last).prev_le_cap (hmem_last hj_cap),
        (hval.1 b hb m_last hm_last).next_le_cap (hmem_last hj_cap)⟩)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb, hm_last, hbounds⟩
  · obtain ⟨hfr_u, hcpl_u⟩ := compUnlinkIfIndexedGenProg_effect
      (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm_last hbounds
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hj_last_n : j_last < N :=
      lt_of_lt_of_le hj_last_bc (bCount_le_n_max hslot b)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
      (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
      (m := m_last) (j_del := j_last) hwg hb hm_last hj_last_n hval hmem_last
    set s₁ := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m_last)), j_last))
    have hgm₁ : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
      hcpl_u.gm_eq.trans (eff_u.2.2.2.2.1.trans hcpl.gm_eq.symm)
    exact ⟨U, V, N, m_cap, _, j_del, rfl, henv.of_mem_eq (by rw [hfr_u.frontier_eq]), hcpl_u,
      hgm₁.symm ▸ hslot, hgm₁.symm ▸ hm_cap, hb, hgm₁.symm ▸ (lt_trans hj_lt hj_last_bc),
      by rw [hgm₁]⟩

/-- Compacted swap helper for `delete` when `j_del < j_last` (`¬ReadsWidth`). -/
private def compDeleteSwapGenProg :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m_last, j_last)) => do
    compDeleteSwapCopyProg (((((cp, (metaBase, itemBase)), b), phys_del), (m_last, j_last)))
    compPrependIfIndexedGenProg (((cp, metaBase), (b, m_last)), j_del)

private theorem memoryCost_compDeleteSwapGenProg_le
    (d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compDeleteSwapGenProg d) s ≤ 54 := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m_last, j_last⟩⟩
  dsimp only [compDeleteSwapGenProg, compDeleteSwapCopyProg]
  simp only [Realization.memoryCost_bind', prog_runClient_state_bind]
  have h1 := memoryCost_compUnlinkIfIndexedGenProg_le (((cp, metaBase), (b, m_last)), j_last) s
  set s₁ := (Memory.spec 0).clientState s
    (compUnlinkIfIndexedGenProg (((cp, metaBase), (b, m_last)), j_last))
  have h2 := memoryCost_compCopyLastPayloadGenProg_le
    (((cp, (metaBase, itemBase)), b), phys_del) s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (compCopyLastPayloadGenProg (((cp, (metaBase, itemBase)), b), phys_del))
  have h3 := memoryCost_compPrependIfIndexedGenProg_le
    (((cp, metaBase), (b, m_last)), j_del) s₂
  dsimp only [s₁, s₂] at h2 h3 ⊢
  omega

private theorem compDeleteSwap_stages
    {metaBase itemBase U V w N m_cap b j_del m_last j_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hm_last : m_last < numMicroPerBucket N)
    (hj_lt : j_del < j_last)
    (hj_last_bc : j_last < bCount N (compGmAt metaBase U w N s.mem) b)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_last : j_last < effBucketCap N → j_last ∈ L b m_last) :
    let phys_del := slotOf N (compGmAt metaBase U w N s.mem) b j_del
    let s₁ := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m_last)), j_last))
    let sf₁ := (Memory.spec 0).clientState s_fix
      (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), m_last), j_last))
    let s₂ := (Memory.spec 0).clientState s₁
      (compCopyLastPayloadGenProg (((mkCompParams U V w N, (metaBase, itemBase)), b), phys_del))
    let sf₂ := (Memory.spec 0).clientState sf₁
      (copyLastPayloadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), phys_del))
    CompOpFrame metaBase itemBase U V w N m_cap s s₁ ∧
    CompOpFrame metaBase itemBase U V w N m_cap s₁ s₂ ∧
    FixedCoupled metaBase itemBase U V w N sf₂ s₂ ∧
    lmHead N (compLmAt metaBase U w N s₂.mem) b m_last ≤ effBucketCap N ∧
    CompUnlinkIfIndexedPre w (((mkCompParams U V w N, metaBase), (b, m_last)), j_last) s ∧
    CompCopyLastPayloadPre w (((mkCompParams U V w N, (metaBase, itemBase)), b), phys_del) s₁ ∧
    CompPrependIfIndexedPre w (((mkCompParams U V w N, metaBase), (b, m_last)), j_del) s₂ := by
  intro phys_del s₁ sf₁ s₂ sf₂
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hj_del_bc : j_del < bCount N (compGmAt metaBase U w N s.mem) b := lt_trans hj_lt hj_last_bc
  have hj_last_n : j_last < N := lt_of_lt_of_le hj_last_bc (bCount_le_n_max hslot b)
  have hphys_del_lt : phys_del < N := (slotOf_lt_and_injective hslot).1 b hb j_del hj_del_bc
  have hbounds : j_last < effBucketCap N →
      lmPrev N (compLmAt metaBase U w N s.mem) b j_last ≤ effBucketCap N ∧
      lmNext N (compLmAt metaBase U w N s.mem) b j_last ≤ effBucketCap N := fun hj_cap => by
    rw [hcpl.lm_eq]
    exact ⟨(hval.1 b hb m_last hm_last).prev_le_cap (hmem_last hj_cap),
      (hval.1 b hb m_last hm_last).next_le_cap (hmem_last hj_cap)⟩
  obtain ⟨hfr1, hcpl1⟩ := compUnlinkIfIndexedGenProg_effect
    (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm_last hbounds
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
    (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
    (m := m_last) (j_del := j_last) hwg hb hm_last hj_last_n hval hmem_last
  have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
    hcpl1.gm_eq.trans (eff_u.2.2.2.2.1.trans hcpl.gm_eq.symm)
  have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hm_cap1 : epochTotalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := hgm1.symm ▸ hm_cap
  have hj_del_bc1 : j_del < bCount N (compGmAt metaBase U w N s₁.mem) b := hgm1.symm ▸ hj_del_bc
  obtain ⟨hfr2, hcpl2⟩ :=
    compCopyLastPayloadGenProg_effect henv1 hcpl1 hslot1 hm_cap1 hb hj_del_bc1
  have hphys_eq1 : slotOf N (compGmAt metaBase U w N s₁.mem) b j_del = phys_del := by rw [hgm1]
  rw [hphys_eq1] at hfr2 hcpl2
  have hslot_sf1 : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem) := by
    rw [eff_u.2.2.2.2.1, ← hcpl.gm_eq]; exact hslot
  have hbc_sf1 : 1 ≤ bCount N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem) b := by
    rw [eff_u.2.2.2.2.1, ← hcpl.gm_eq]; omega
  have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (phys_del := phys_del)
    hwg hslot_sf1 hb hbc_sf1 hphys_del_lt
  obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
  have hold2 : lmHead N (compLmAt metaBase U w N s₂.mem) b m_last ≤ effBucketCap N := by
    rw [hcpl2.lm_eq, eff_c.2.2.2.2.1]
    exact (hval₁.1 b hb m_last hm_last).head_le_cap
  refine ⟨hfr1, hfr2, hcpl2, hold2,
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb, hm_last, hbounds⟩,
    ⟨U, V, N, m_cap, sf₁, j_del, rfl, henv1, hcpl1, hslot1, hm_cap1, hb, hj_del_bc1,
      hphys_eq1.symm⟩,
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, ?_, hb, hm_last, hold2⟩⟩
  rw [hfr2.frontier_eq, hfr1.frontier_eq]; exact henv.meta_le_frontier

private theorem compDeleteSwapGenProg_effect
    {metaBase itemBase U V w N m_cap b j_del m_last j_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hm_last : m_last < numMicroPerBucket N)
    (hj_lt : j_del < j_last)
    (hj_last_bc : j_last < bCount N (compGmAt metaBase U w N s.mem) b)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_last : j_last < effBucketCap N → j_last ∈ L b m_last) :
    let phys_del := slotOf N (compGmAt metaBase U w N s.mem) b j_del
    let d := (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
      (m_last, j_last)))
    let s' := (Memory.spec 0).clientState s (compDeleteSwapGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (deleteSwapProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((((0, b), j_del), phys_del), (m_last, j_last)))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro phys_del d s' s_fix'
  obtain ⟨hfr1, hfr2, hcpl2, hold2, _, _, _⟩ :=
    compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
  obtain ⟨hfr3, hcpl3⟩ := compPrependIfIndexedGenProg_effect
    (m_cap := m_cap) (j_new := j_del) henv.pos_w henv.meta_le_item hcpl2 hb hm_last hold2
  have hs'_eq : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m_last)), j_last)))
        (compCopyLastPayloadGenProg (((mkCompParams U V w N, (metaBase, itemBase)), b), phys_del)))
      (compPrependIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m_last)), j_del)) := by
    dsimp only [s', d, compDeleteSwapGenProg, compDeleteSwapCopyProg]
    repeat rw [StateTransitionSpec.clientState_bind]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s_fix
          (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
            (((0, b), m_last), j_last)))
        (copyLastPayloadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), phys_del)))
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), m_last), j_del)) := by
    dsimp only [s_fix']; unfold deleteSwapProg deleteSwapGenProg
    simp only [unlinkIfIndexedGenProg_mk, copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]
    repeat rw [StateTransitionSpec.clientState_bind]
  rw [hs'_eq, hs_fix'_eq]
  exact ⟨hfr1.trans (hfr2.trans hfr3), hcpl3⟩

private theorem realizesBounded_compDeleteSwapGen :
    RealizesBounded .exact compDeleteSwapGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompDeleteSwapPre (fun _ _ => 0) := by
  have hsc := realizesBounded_compDeleteSwapCopy
  have hpr := realizesBounded_compPrependIfIndexedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m_last, j_last⟩⟩
    obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩ := h)
  · exact ⟨j_del, U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩
  · obtain ⟨_, _, _, _, _, _, hpre_p⟩ :=
      compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
    change CompPrependIfIndexedPre w _
      ((Memory.spec 0).clientState s
        (compDeleteSwapCopyProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), b),
            slotOf N (compGmAt metaBase U w N s.mem) b j_del), (m_last, j_last)))))
    dsimp only [compDeleteSwapCopyProg]
    rw [StateTransitionSpec.clientState_bind]
    exact hpre_p

private theorem validProg_compDeleteSwapGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDeleteSwapPre w d s) : ValidProg w 0 s (compDeleteSwapGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m_last, j_last⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
    hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩ := h
  obtain ⟨_, _, _, _, hpre_u, hpre_c, hpre_p⟩ :=
    compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
  dsimp only [compDeleteSwapGenProg, compDeleteSwapCopyProg]
  simp only [bind_assoc]
  exact validProg_bind (validProg_compUnlinkIfIndexedGen hpre_u) <|
    validProg_bind (validProg_compCopyLastPayloadGen hpre_c) <|
      validProg_compPrependIfIndexedGen hpre_p

private theorem compGmAt_compDeleteSwapGenProg
    {metaBase itemBase U V w N m_cap b j_del m_last j_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hm_last : m_last < numMicroPerBucket N)
    (hj_lt : j_del < j_last)
    (hj_last_bc : j_last < bCount N (compGmAt metaBase U w N s.mem) b)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_last : j_last < effBucketCap N → j_last ∈ L b m_last) :
    compGmAt metaBase U w N
      ((Memory.spec 0).clientState s
        (compDeleteSwapGenProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)),
            slotOf N (compGmAt metaBase U w N s.mem) b j_del),
            (m_last, j_last))))).mem =
      compGmAt metaBase U w N s.mem := by
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set phys_del := slotOf N (compGmAt metaBase U w N s.mem) b j_del
  have hj_del_bc : j_del < bCount N (compGmAt metaBase U w N s.mem) b := lt_trans hj_lt hj_last_bc
  have hj_last_n : j_last < N := lt_of_lt_of_le hj_last_bc (bCount_le_n_max hslot b)
  have hphys_del_lt : phys_del < N := (slotOf_lt_and_injective hslot).1 b hb j_del hj_del_bc
  obtain ⟨_, hcpl_sw⟩ := compDeleteSwapGenProg_effect
    henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
    (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
    (m := m_last) (j_del := j_last) hwg hb hm_last hj_last_n hval hmem_last
  set sf₁ := (Memory.spec 0).clientState s_fix
    (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), m_last), j_last))
  have hslot_sf1 : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem) := by
    rw [eff_u.2.2.2.2.1, ← hcpl.gm_eq]; exact hslot
  have hbc_sf1 : 1 ≤ bCount N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem) b := by
    rw [eff_u.2.2.2.2.1, ← hcpl.gm_eq]; exact Nat.one_le_of_lt hj_last_bc
  have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (phys_del := phys_del)
    hwg hslot_sf1 hb hbc_sf1 hphys_del_lt
  obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
  set sf₂ := (Memory.spec 0).clientState sf₁
    (copyLastPayloadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), phys_del))
  have hold_sf2 :
      lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₂.mem) b m_last ≤
        effBucketCap N := by
    rw [eff_c.2.2.2.2.1]
    exact (hval₁.1 b hb m_last hm_last).head_le_cap
  have hgm_pr := gmAt_prependIfIndexedProg (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (m := m_last) (j_new := j_del)
    hwg hb hm_last sf₂ hold_sf2
  have hst_fix_sw : (Memory.spec 0).clientState s_fix
      (deleteSwapProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((((0, b), j_del), phys_del), (m_last, j_last))) =
      (Memory.spec 0).clientState sf₂
        (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), m_last), j_del)) := by
    unfold deleteSwapProg deleteSwapGenProg
    simp only [unlinkIfIndexedGenProg_mk, copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]
    repeat rw [StateTransitionSpec.clientState_bind]
  rw [hcpl_sw.gm_eq, hst_fix_sw, hgm_pr, eff_c.2.2.2.2.2, eff_u.2.2.2.2.1, ← hcpl.gm_eq]

private def compDeleteFoundTailProg :
    ((((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), m_last), c_b) => do
    let j_last ← pure (c_b - 1)
    if j_del < j_last then do
      compDeleteSwapGenProg
        (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m_last, j_last)))
      compPopBackSlotGenProg ((cp, (metaBase, itemBase)), b)
    else
      compPopBackSlotGenProg ((cp, (metaBase, itemBase)), b)

private def CompDeleteFoundTailPre (w : ℕ) :
    ((((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), m_last), c_b), s =>
    ∃ U V N m_cap s_fix L,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap ∧
      b < numBuckets N ∧
      m_last < numMicroPerBucket N ∧
      c_b = bCount N (compGmAt metaBase U w N s.mem) b ∧
      j_del < c_b ∧
      phys_del = slotOf N (compGmAt metaBase U w N s.mem) b j_del ∧
      AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L ∧
      (j_del < c_b - 1 → c_b - 1 < effBucketCap N → c_b - 1 ∈ L b m_last)

private theorem compDeleteFoundTail_popPre {w : ℕ}
    {U V N m_cap metaBase itemBase b j_del m_last : ℕ}
    {s_fix s : Memory.State} {L : ℕ → ℕ → List ℕ}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hm_last : m_last < numMicroPerBucket N)
    (hj_del_bc : j_del < bCount N (compGmAt metaBase U w N s.mem) b)
    (hc : j_del < bCount N (compGmAt metaBase U w N s.mem) b - 1)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 < effBucketCap N →
      bCount N (compGmAt metaBase U w N s.mem) b - 1 ∈ L b m_last) :
    CompPopBackSlotPre w ((mkCompParams U V w N, (metaBase, itemBase)), b)
      ((Memory.spec 0).clientState s
        (compDeleteSwapGenProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)),
            slotOf N (compGmAt metaBase U w N s.mem) b j_del),
            (m_last, bCount N (compGmAt metaBase U w N s.mem) b - 1))))) := by
  have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := Nat.one_le_of_lt hj_del_bc
  have hj_last_bc : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
      bCount N (compGmAt metaBase U w N s.mem) b := Nat.sub_lt hbc_pos Nat.one_pos
  obtain ⟨hfr_sw, hcpl_sw⟩ := compDeleteSwapGenProg_effect
    henv hcpl hslot hm_cap hb hm_last hc hj_last_bc hval hmem_last
  have hgm_sw := compGmAt_compDeleteSwapGenProg
    henv hcpl hslot hm_cap hb hm_last hc hj_last_bc hval hmem_last
  exact ⟨U, V, N, m_cap, _, rfl, henv.of_mem_eq (by rw [hfr_sw.frontier_eq]), hcpl_sw,
    hgm_sw.symm ▸ hslot, hb, hgm_sw.symm ▸ hbc_pos, hgm_sw.symm ▸ hm_cap⟩

private theorem realizesBounded_compDeleteFoundTail :
    RealizesBounded .exact compDeleteFoundTailProg
      (WordEncoding.encode (α := ((((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompDeleteFoundTailPre (fun _ _ => 0) := by
  have hsw := realizesBounded_compDeleteSwapGen
  have hpop := realizesBounded_compPopBackSlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, m_last⟩, c_b⟩
    obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm_last, rfl, hj_del_bc, rfl, hval, hmem_last⟩ := h
    dsimp only at *
    have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := Nat.one_le_of_lt hj_del_bc
    have hj_last_bc : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
        bCount N (compGmAt metaBase U w N s.mem) b := Nat.sub_lt hbc_pos Nat.one_pos)
  · exact hbc_pos
  · exact ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm_last, hc, hj_last_bc, rfl, hval, hmem_last hc⟩
  · simp only [StateTransitionSpec.clientState]
    exact compDeleteFoundTail_popPre henv hcpl hslot hm_cap hb hm_last hj_del_bc hc hval
      (hmem_last hc)
  · exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, hbc_pos, hm_cap⟩

/-- Compacted found-branch helper for Phase 2 of `delete` (`¬ReadsWidth`). -/
private def compDeleteFoundGenProg :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m, m_last)) => do
    compUnlinkIfIndexedGenProg (((cp, metaBase), (b, m)), j_del)
    let c_b ← readCompBucketCountGenProg ((cp, metaBase), b)
    compDeleteFoundTailProg ((((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), m_last), c_b))

/-- Precondition for `compDeleteFoundGenProg`. -/
private def CompDeleteFoundPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m, m_last)), s =>
    ∃ U V N m_cap s_fix L,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      m_last < numMicroPerBucket N ∧
      j_del < bCount N (compGmAt metaBase U w N s.mem) b ∧
      phys_del = slotOf N (compGmAt metaBase U w N s.mem) b j_del ∧
      AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L ∧
      (j_del < effBucketCap N → j_del ∈ L b m) ∧
      (bCount N (compGmAt metaBase U w N s.mem) b - 1 < effBucketCap N →
        bCount N (compGmAt metaBase U w N s.mem) b - 1 ∈ L b m_last)

private theorem compDeleteFoundGenProg_effect {metaBase itemBase U V w N m_cap b j_del m m_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hm_last : m_last < numMicroPerBucket N)
    (hj_del_bc : j_del < bCount N (compGmAt metaBase U w N s.mem) b)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_del : j_del < effBucketCap N → j_del ∈ L b m)
    (hmem_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 < effBucketCap N →
      bCount N (compGmAt metaBase U w N s.mem) b - 1 ∈ L b m_last) :
    let phys_del := slotOf N (compGmAt metaBase U w N s.mem) b j_del
    let d := (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
      (m, m_last)))
    let s' := (Memory.spec 0).clientState s (compDeleteFoundGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (deleteFoundProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((((0, b), j_del), phys_del), (m, m_last)))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compDeleteFoundGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 312 := by
  intro phys_del d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
  have hj_del_n : j_del < N := lt_of_lt_of_le hj_del_bc (bCount_le_n_max hslot b)
  have hbounds_del : j_del < effBucketCap N →
      lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
      lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N := fun hj_cap => by
    rw [hcpl.lm_eq]
    exact ⟨(hval.1 b hb m hm).prev_le_cap (hmem_del hj_cap),
      (hval.1 b hb m hm).next_le_cap (hmem_del hj_cap)⟩
  obtain ⟨hfr1, hcpl1⟩ := compUnlinkIfIndexedGenProg_effect
    (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm hbounds_del
  have eff_u1 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
    (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
    (m := m) (j_del := j_del) hwg hb hm hj_del_n hval hmem_del
  set s₁ := (Memory.spec 0).clientState s
    (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
  set sf₁ := (Memory.spec 0).clientState s_fix
    (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), m), j_del))
  have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
    hcpl1.gm_eq.trans (eff_u1.2.2.2.2.1.trans hcpl.gm_eq.symm)
  have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := hgm1.symm ▸ hm_cap
  obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u1.2.2.2.2.2
  set c_b := bCount N (compGmAt metaBase U w N s.mem) b
  set j_last := c_b - 1
  by_cases hlt : j_del < j_last
  · have hj_last_bc1 : j_last < bCount N (compGmAt metaBase U w N s₁.mem) b := by
      rw [hgm1]; dsimp only [j_last, c_b]; omega
    have hmem_last₁ : j_last < effBucketCap N → j_last ∈ L₁ b m_last := fun hj_cap => by
      rw [hmem₁ b hb m_last hm_last j_last]
      exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
    obtain ⟨hfr_sw, hcpl_sw⟩ := compDeleteSwapGenProg_effect
      henv1 hcpl1 hslot1 hm_cap1 hb hm_last hlt hj_last_bc1 hval₁ hmem_last₁
    have hphys_eq1 : slotOf N (compGmAt metaBase U w N s₁.mem) b j_del = phys_del := by rw [hgm1]
    rw [hphys_eq1] at hfr_sw hcpl_sw
    set s₂ := (Memory.spec 0).clientState s₁
      (compDeleteSwapGenProg
        (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
          (m_last, j_last))))
    set sf₂ := (Memory.spec 0).clientState sf₁
      (deleteSwapProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((((0, b), j_del), phys_del), (m_last, j_last)))
    have hgm2 : compGmAt metaBase U w N s₂.mem = compGmAt metaBase U w N s.mem := by
      have hgm_step := compGmAt_compDeleteSwapGenProg
        henv1 hcpl1 hslot1 hm_cap1 hb hm_last hlt hj_last_bc1 hval₁ hmem_last₁
      rw [hphys_eq1] at hgm_step
      exact hgm_step.trans hgm1
    have henv2 := henv1.of_mem_eq (s' := s₂) (by rw [hfr_sw.frontier_eq])
    obtain ⟨hfr_pop, hcpl_pop, hcost_pop⟩ := compPopBackSlotGenProg_effect
      henv2 hcpl_sw (hgm2.symm ▸ hslot) hb (hgm2.symm ▸ hbc_pos) (hgm2.symm ▸ hm_cap)
    rw [hgm2] at hcost_pop
    have hs'_eq : s' = (Memory.spec 0).clientState s₂
        (compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) := by
      dsimp only [s', d, compDeleteFoundGenProg, compDeleteFoundTailProg, s₂, s₁, j_last, c_b]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb,
        hgm1, ite_eq_left hlt, StateTransitionSpec.clientState_bind]
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState sf₂
        (popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
      dsimp only [s_fix', sf₂, sf₁, j_last, c_b]; unfold deleteFoundProg deleteFoundGenProg
      simp only [unlinkIfIndexedGenProg_mk, readBucketCountGenProg_mk, deleteSwapGenProg_mk,
        popBackSlotGenProg_mk, pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readBucketCountProg, clientResult_readBucketCountProg (0, b) sf₁ hb,
        eff_u1.2.2.2.2.1, ← hcpl.gm_eq, ite_eq_left hlt, StateTransitionSpec.clientState_bind]
    have hcost_tot : memoryCost (compDeleteFoundGenProg d) s ≤
        70 + memoryCost (compPopBackSlotGenProg
          ((mkCompParams U V w N, (metaBase, itemBase)), b)) s₂ := by
      dsimp only [d, compDeleteFoundGenProg, compDeleteFoundTailProg]
      simp only [pure_bind]
      rw [Realization.memoryCost_bind',
        memoryCost_bind_of_clientState_eq (clientState_readCompBucketCountGenProg _ s₁) _,
        clientResult_readCompBucketCountGenProg hb, hgm1, ite_eq_left hlt,
        Realization.memoryCost_bind']
      have hc1 := memoryCost_compUnlinkIfIndexedGenProg_le
        (((mkCompParams U V w N, metaBase), (b, m)), j_del) s
      have hc2 := memoryCost_readCompBucketCountGenProg_le
        ((mkCompParams U V w N, metaBase), b) s₁
      have hc3 := memoryCost_compDeleteSwapGenProg_le
        (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
          (m_last, j_last))) s₁
      dsimp only [s₂, s₁, j_last, c_b] at hc2 hc3 ⊢
      omega
    refine ⟨by rw [hs'_eq]; exact hfr1.trans (hfr_sw.trans hfr_pop),
      by rw [hs'_eq, hs_fix'_eq]; exact hcpl_pop, ?_⟩
    rw [hs'_eq]
    dsimp only [s₂, s₁, j_last, c_b] at hcost_pop hcost_tot ⊢
    omega
  · obtain ⟨hfr_pop, hcpl_pop, hcost_pop⟩ := compPopBackSlotGenProg_effect
      henv1 hcpl1 hslot1 hb (hgm1.symm ▸ hbc_pos) hm_cap1
    rw [hgm1] at hcost_pop
    have hs'_eq : s' = (Memory.spec 0).clientState s₁
        (compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) := by
      dsimp only [s', d, compDeleteFoundGenProg, compDeleteFoundTailProg, s₁, j_last, c_b]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb,
        hgm1, ite_eq_right hlt]
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState sf₁
        (popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
      dsimp only [s_fix', sf₁, j_last, c_b]; unfold deleteFoundProg deleteFoundGenProg
      simp only [unlinkIfIndexedGenProg_mk, readBucketCountGenProg_mk, deleteSwapGenProg_mk,
        popBackSlotGenProg_mk, pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readBucketCountProg, clientResult_readBucketCountProg (0, b) sf₁ hb,
        eff_u1.2.2.2.2.1, ← hcpl.gm_eq, ite_eq_right hlt]
    have hcost_tot : memoryCost (compDeleteFoundGenProg d) s ≤
        16 + memoryCost (compPopBackSlotGenProg
          ((mkCompParams U V w N, (metaBase, itemBase)), b)) s₁ := by
      dsimp only [d, compDeleteFoundGenProg, compDeleteFoundTailProg]
      simp only [pure_bind]
      rw [Realization.memoryCost_bind',
        memoryCost_bind_of_clientState_eq (clientState_readCompBucketCountGenProg _ s₁) _,
        clientResult_readCompBucketCountGenProg hb, hgm1, ite_eq_right hlt]
      have hc1 := memoryCost_compUnlinkIfIndexedGenProg_le
        (((mkCompParams U V w N, metaBase), (b, m)), j_del) s
      have hc2 := memoryCost_readCompBucketCountGenProg_le
        ((mkCompParams U V w N, metaBase), b) s₁
      dsimp only [s₁, j_last, c_b] at hc2 ⊢
      omega
    refine ⟨by rw [hs'_eq]; exact hfr1.trans hfr_pop,
      by rw [hs'_eq, hs_fix'_eq]; exact hcpl_pop, ?_⟩
    rw [hs'_eq]
    dsimp only [s₁, j_last, c_b] at hcost_pop hcost_tot ⊢
    omega

private theorem realizesBounded_compDeleteFoundGen :
    RealizesBounded .exact compDeleteFoundGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompDeleteFoundPre (fun _ _ => 0) := by
  have hu := realizesBounded_compUnlinkIfIndexedGen
  have hbc := realizesBounded_readCompBucketCountGen
  have htl := realizesBounded_compDeleteFoundTail
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m, m_last⟩⟩
    obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
      hb, hm, hm_last, hj_del_bc, rfl, hval, hmem_del, hmem_last⟩ := h
    have hbounds_del : j_del < effBucketCap N →
        lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
        lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N := fun hj_cap => by
      rw [hcpl.lm_eq]
      exact ⟨(hval.1 b hb m hm).prev_le_cap (hmem_del hj_cap),
        (hval.1 b hb m hm).next_le_cap (hmem_del hj_cap)⟩)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb, hm, hbounds_del⟩
  · obtain ⟨hfr1, hcpl1⟩ := compUnlinkIfIndexedGenProg_effect
      (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm hbounds_del
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hj_del_n : j_del < N := lt_of_lt_of_le hj_del_bc (bCount_le_n_max hslot b)
    have eff_u1 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
      (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
      (m := m) (j_del := j_del) hwg hb hm hj_del_n hval hmem_del
    set s₁ := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
    have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
      hcpl1.gm_eq.trans (eff_u1.2.2.2.2.1.trans hcpl.gm_eq.symm)
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr1.frontier_eq.symm ▸ henv.meta_le_frontier, hgm1.symm ▸ hslot, hb⟩
  · obtain ⟨hfr1, hcpl1⟩ := compUnlinkIfIndexedGenProg_effect
      (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm hbounds_del
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hj_del_n : j_del < N := lt_of_lt_of_le hj_del_bc (bCount_le_n_max hslot b)
    have eff_u1 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
      (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
      (m := m) (j_del := j_del) hwg hb hm hj_del_n hval hmem_del
    set s₁ := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
    have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
      hcpl1.gm_eq.trans (eff_u1.2.2.2.2.1.trans hcpl.gm_eq.symm)
    obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u1.2.2.2.2.2
    rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb]
    refine ⟨U, V, N, m_cap, _, L₁, rfl, henv.of_mem_eq (by rw [hfr1.frontier_eq]), hcpl1,
      hgm1.symm ▸ hslot, hgm1.symm ▸ hm_cap, hb, hm_last, rfl, hgm1.symm ▸ hj_del_bc,
      by rw [hgm1], hval₁, fun hlt hj_cap => ?_⟩
    rw [hgm1] at hlt hj_cap ⊢
    dsimp only at hlt
    rw [hmem₁ b hb m_last hm_last _]
    exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩

private theorem validProg_compDeleteFoundGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDeleteFoundPre w d s) : ValidProg w 0 s (compDeleteFoundGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m, m_last⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
    hb, hm, hm_last, hj_del_bc, rfl, hval, hmem_del, hmem_last⟩ := h
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := Nat.one_le_of_lt hj_del_bc
  have hj_del_n : j_del < N := lt_of_lt_of_le hj_del_bc (bCount_le_n_max hslot b)
  have hbounds_del : j_del < effBucketCap N →
      lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
      lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N := fun hj_cap => by
    rw [hcpl.lm_eq]
    exact ⟨(hval.1 b hb m hm).prev_le_cap (hmem_del hj_cap),
      (hval.1 b hb m hm).next_le_cap (hmem_del hj_cap)⟩
  obtain ⟨hfr1, hcpl1⟩ := compUnlinkIfIndexedGenProg_effect
    (m_cap := m_cap) henv.pos_w henv.meta_le_item hcpl hb hm hbounds_del
  have eff_u1 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := ghostW w)
    (n_max := N) (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b)
    (m := m) (j_del := j_del) hwg hb hm hj_del_n hval hmem_del
  set s₁ := (Memory.spec 0).clientState s
    (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
  set sf₁ := (Memory.spec 0).clientState s_fix
    (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), m), j_del))
  have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem :=
    hcpl1.gm_eq.trans (eff_u1.2.2.2.2.1.trans hcpl.gm_eq.symm)
  have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := hgm1.symm ▸ hm_cap
  obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u1.2.2.2.2.2
  dsimp only [compDeleteFoundGenProg, compDeleteFoundTailProg]
  simp only [pure_bind]
  refine validProg_bind
    (validProg_compUnlinkIfIndexedGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hb, hm, hbounds_del⟩) ?_
  refine validProg_bind
    (validProg_readCompBucketCountGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv1.meta_le_frontier, hslot1, hb⟩) ?_
  rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb, hgm1]
  refine validProg_ite (fun hlt => ?_) (fun _ =>
    validProg_compPopBackSlotGen
      ⟨U, V, N, m_cap, sf₁, rfl, henv1, hcpl1, hslot1, hb, hgm1.symm ▸ hbc_pos, hm_cap1⟩)
  set j_last := bCount N (compGmAt metaBase U w N s.mem) b - 1
  have hj_last_bc : j_last < bCount N (compGmAt metaBase U w N s.mem) b :=
    Nat.sub_lt hbc_pos Nat.one_pos
  have hj_last_bc1 : j_last < bCount N (compGmAt metaBase U w N s₁.mem) b := hgm1.symm ▸ hj_last_bc
  have hmem_last₁ : j_last < effBucketCap N → j_last ∈ L₁ b m_last := fun hj_cap => by
    rw [hmem₁ b hb m_last hm_last j_last]
    exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
  have hphys_eq1 : slotOf N (compGmAt metaBase U w N s₁.mem) b j_del =
      slotOf N (compGmAt metaBase U w N s.mem) b j_del := by rw [hgm1]
  refine validProg_bind
    (validProg_compDeleteSwapGen
      ⟨U, V, N, m_cap, sf₁, L₁, rfl, henv1, hcpl1, hslot1, hm_cap1, hb, hm_last,
        hlt, hj_last_bc1, hphys_eq1.symm, hval₁, hmem_last₁⟩) ?_
  have hpop_pre := compDeleteFoundTail_popPre
    henv1 hcpl1 hslot1 hm_cap1 hb hm_last (hgm1.symm ▸ hj_del_bc)
    (by rw [hgm1]; exact hlt) hval₁ (by rw [hgm1]; exact hmem_last₁)
  rw [hphys_eq1, hgm1] at hpop_pre
  exact validProg_compPopBackSlotGen hpop_pre

/-- Compacted Phase 2 of `delete` at bucket level (`¬ReadsWidth`):
branches on `found = 1` to call `compDeleteFoundGenProg`, else returns `()`. -/
private def compDeleteFinishGenProg :
    (((((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((((cp, (metaBase, itemBase)), b), (found, j_del)), phys_del), m), m_last) => do
    let z1 ← pure 1
    if found = z1 then
      compDeleteFoundGenProg (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m, m_last)))
    else
      pure ()

/-- Precondition for `compDeleteFinishGenProg`. -/
private def CompDeleteFinishPre (w : ℕ) :
    (((((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((((cp, (metaBase, itemBase)), b), (found, j_del)), phys_del), m), m_last), s =>
    Fits w 1 ∧
    (found = 1 →
      CompDeleteFoundPre w
        (((((cp, (metaBase, itemBase)), (b, j_del)), phys_del), (m, m_last))) s)

private theorem realizesBounded_compDeleteFinishGen :
    RealizesBounded .exact compDeleteFinishGenProg
      (WordEncoding.encode (α := (((((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompDeleteFinishPre (fun _ _ => 0) := by
  have hdf := realizesBounded_compDeleteFoundGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨found, j_del⟩⟩, phys_del⟩, m⟩, m_last⟩
    obtain ⟨h1, hfound⟩ := h)
  · exact h1
  · exact hfound hc

private theorem validProg_compDeleteFinishGen {w : ℕ}
    {d : (((((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : CompDeleteFinishPre w d s) : ValidProg w 0 s (compDeleteFinishGenProg d) := by
  rcases d with ⟨⟨⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨found, j_del⟩⟩, phys_del⟩, m⟩, m_last⟩
  obtain ⟨_, hfound⟩ := h
  dsimp only [compDeleteFinishGenProg]
  simp only [pure_bind]
  exact validProg_ite (fun hc => validProg_compDeleteFoundGen (hfound hc))
    (fun _ => validProg_pure _)

/-- Feistel-dispatched Phase 2 of compacted `delete` (`¬ReadsWidth`):
`d = ((((cp, (metaBase, itemBase)), (u, h_q)), ((found, j_del), phys_del)), h_q_last)`. -/
def compDeleteFinishWithHashGenProg :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), (u, h_q)), prep_res), h_q_last) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    let m_last ← pure (h_q_last >>> cpBucketBits cp)
    compDeleteFinishGenProg
      ((((((cp, (metaBase, itemBase)), fcBucket c), prep_res.1), prep_res.2), c.2), m_last)

/-- Precondition for `compDeleteFinishWithHashGenProg`. -/
def CompDeleteFinishWithHashPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), (u, h_q)), prep_res), h_q_last), s =>
    CompFeistelCoordsPre w (cp, (u, h_q)) s ∧
    Fits w h_q_last ∧
    CompDeleteFinishPre w
      ((((((cp, (metaBase, itemBase)),
        (h_q &&& cpBucketMask cp) ^^^ (u &&& cpBucketMask cp)),
        prep_res.1), prep_res.2), h_q >>> cpBucketBits cp),
        h_q_last >>> cpBucketBits cp) s

theorem realizesBounded_compDeleteFinishWithHashGen :
    RealizesBounded .exact compDeleteFinishWithHashGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompDeleteFinishWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hdf := realizesBounded_compDeleteFinishGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩, ⟨⟨found, j_del⟩, phys_del⟩⟩,
      h_q_last⟩
    obtain ⟨hfc_pre, hhq_last, hdf_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hdf_pre

theorem validProg_compDeleteFinishWithHashGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ} {s : Memory.State}
    (h : CompDeleteFinishWithHashPre w d s) :
    ValidProg w 0 s (compDeleteFinishWithHashGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩, ⟨⟨found, j_del⟩, phys_del⟩⟩, h_q_last⟩
  obtain ⟨_, _, hdf_pre⟩ := h
  dsimp only [compDeleteFinishWithHashGenProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  simp only [pure_bind]
  exact validProg_compDeleteFinishGen hdf_pre

/-! ## Section 5: Dictionary-Level Specifications Coupled to `DictStateInv` -/

private theorem compDispatch_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let cp := mkCompParams U V w N
    (h_q &&& cpBucketMask cp) ^^^ (u.val &&& cpBucketMask cp) = b ∧
    u.val >>> cpBucketBits cp = q ∧
    h_q >>> cpBucketBits cp = m ∧
    b < numBuckets N ∧
    m < numMicroPerBucket N ∧
    SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
    CompQueryWithHashPre w ((cp, (metaBase, itemBase)), (u.val, h_q)) s := by
  intro q h_q b m cp
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_eq : (h_q &&& cpBucketMask cp) ^^^ (u.val &&& cpBucketMask cp) = b :=
    and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q
  have hq_eq : u.val >>> cpBucketBits cp = q := Nat.shiftRight_eq_div_pow u.val (bucketBits N)
  have hm_eq : h_q >>> cpBucketBits cp = m := rfl
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
  have hm_lt : m < numMicroPerBucket N := mOfSeed_lt U N θ q
  have hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem) := by
    rw [hcpl.gm_eq]; exact hb_inv.hslot
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  have hfc : CompFeistelCoordsPre w (cp, (u.val, h_q)) s :=
    fits_compFeistelCoords henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_off
      (u.isLt.trans henv.lt_pow_U) (hValOfSeed_lt U N θ q)
  refine ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hfc, ?_⟩
  rw [hb_eq, hq_eq, hm_eq]
  exact ⟨U, V, N, m_items, s_fix, L b m, rfl, henv, hcpl, hslot, hm_items,
    hb_lt, hm_lt, hchain, hc_lt⟩

/-- Dictionary-level specification of `compQueryWithHashGenProg`: establishes
`CompQueryWithHashPre`, leaves `s` unchanged, returns `s_abs u`, and bounds `memoryCost` by
`38 + 12 * probeExcess`. -/
theorem compQueryWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog := compQueryWithHashGenProg d
    CompQueryWithHashPre w d s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = s_abs u ∧
    memoryCost prog s ≤
      38 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q d prog
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hfix_spec := queryWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_qb, hres_qb, hcost_qb⟩ := compQueryBodyGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have hprog_eq : prog =
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compQueryBodyGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2)) := rfl
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  have hfix_eq : (Memory.spec 0).clientResult s_fix
      (queryWithHashProg U V (ghostW w) N ((0, u.val), h_q)) =
      (Memory.spec 0).clientResult s_fix
        (queryBodyProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) := by
    unfold queryWithHashProg queryWithHashGenProg
    simp only [p_bucketBits_mk, p_bucketMask_mk, queryBodyGenProg_mk, pure_bind]
    rw [and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q,
      Nat.shiftRight_eq_div_pow u.val (bucketBits N)]
    rfl
  refine ⟨hpre, ?_, ?_, ?_⟩
  · rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res]
    exact hst_qb
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg,
      hc_res, hres_qb, ← hfix_eq]
    exact hfix_spec.2.2.1
  · rw [hprog_eq, memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add]
    have hgm_eq : compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem := hcpl.gm_eq
    rw [hgm_eq] at hcost_qb
    dsimp only [b, q, m] at hcost_qb hlen_pr hovf_pr ⊢
    unfold probeExcess
    omega

/-- Dictionary-level specification of Phase 1 (`compInsertSearchWithHashGenProg`) of split
compacted insertion. -/
theorem compInsertSearchWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog := compInsertSearchWithHashGenProg d
    let res_sb := (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m))
    CompQueryWithHashPre w d s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = ((sbFound res_sb, res_sb.2), (b, m)) ∧
    (sbFound res_sb = 1 ↔ (s_abs u).isSome) ∧
    (sbFound res_sb = 1 →
      ∃ j < bCount N (compGmAt metaBase U w N s.mem) b,
        res_sb.2 = slotOf N (compGmAt metaBase U w N s.mem) b j) ∧
    memoryCost prog s ≤
      32 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q b m d prog res_sb
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_sb, hres_sb, hcost_sb⟩ := compSearchBucketGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  have hsb_fix := searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m)
    rfl hm_lt
  dsimp only at hsb_fix
  have hres_branch := hsb_fix.2.2
  have hbm := bucketMapOfState_feistelBucket henv.le_U (hValOfSeed U N θ) s_abs u
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have hprog_eq : prog =
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compSearchBucketGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2) >>=
          fun res => compPackInsertSearchResProg (res, c)) := rfl
  refine ⟨hpre, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res,
      StateTransitionSpec.clientState_bind, hst_sb, clientState_compPackInsertSearchResProg]
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg, hc_res,
      StateTransitionSpec.clientResult_bind, hst_sb, hres_sb,
      clientResult_compPackInsertSearchResProg]
  · by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hres_branch
      have hsome : (s_abs u).isSome := by
        rw [← hbm]; exact (hb_inv.hmap_dom b hb_lt q).mpr hex
      change res_sb.1.1 = 1 ↔ _
      exact ⟨fun _ => hsome, fun _ => hres_branch.1⟩
    · rw [ite_eq_right hex] at hres_branch
      have hnot : ¬(s_abs u).isSome := by
        rw [← hbm]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hex
      change res_sb.1.1 = 1 ↔ _
      exact ⟨fun h1 => False.elim (by change res_sb.1.1 = 0 at hres_branch; omega),
        fun hs => False.elim (hnot hs)⟩
  · intro hf1
    by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hres_branch
      obtain ⟨_, hj_lt, _, hphys_eq⟩ := hres_branch
      have hj_lt' : res_sb.1.2 <
          bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := hj_lt
      have hphys_eq' : res_sb.2 =
          slotOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
            res_sb.1.2 := hphys_eq
      rw [hcpl.gm_eq]
      exact ⟨res_sb.1.2, hj_lt', hphys_eq'⟩
    · rw [ite_eq_right hex] at hres_branch
      change sbFound res_sb = 0 at hres_branch
      omega
  · rw [hprog_eq, memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add,
      memoryCost_bind_of_clientState_eq hst_sb _, memoryCost_compPackInsertSearchResProg, add_zero]
    have hgm_eq : compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem := hcpl.gm_eq
    rw [hgm_eq] at hcost_sb
    dsimp only [b, q, m] at hcost_sb hlen_pr hovf_pr ⊢
    unfold probeExcess
    omega

private theorem insertWithHashProg_clientState_hit (U V w₀ n_max u v h_q : ℕ)
    (s_fix : Memory.State)
    (b q m : ℕ)
    (hb_eq : (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u &&& (2 ^ bucketBits n_max - 1)) = b)
    (hq_eq : u >>> bucketBits n_max = q)
    (hm_eq : h_q >>> bucketBits n_max = m)
    (res_sb : (ℕ × ℕ) × ℕ)
    (hres : (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = res_sb)
    (hst : (Memory.spec 0).clientState s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = s_fix)
    (hfound : res_sb.1.1 = 1) :
    (Memory.spec 0).clientState s_fix (insertWithHashProg U V w₀ n_max (((0, u), v), h_q)) =
      (Memory.spec 0).clientState s_fix
        (writeValProg U V w₀ n_max (hashSpace U w₀ n_max) ((0, res_sb.2), v)) := by
  unfold insertWithHashProg insertWithHashGenProg
  simp only [p_bucketBits_mk, p_bucketMask_mk, insertBodyGenProg_mk, pure_bind]
  rw [hb_eq, hq_eq, hm_eq]
  unfold insertBodyProg insertBodyGenProg
  simp only [searchBucketGenProg_mk, writeValGenProg_mk, insertNewGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst, hres, ite_eq_left hfound]

private theorem insertWithHashProg_clientState_miss (U V w₀ n_max u v h_q : ℕ)
    (s_fix : Memory.State) (b q m : ℕ)
    (hb_eq : (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u &&& (2 ^ bucketBits n_max - 1)) = b)
    (hq_eq : u >>> bucketBits n_max = q)
    (hm_eq : h_q >>> bucketBits n_max = m)
    (hst : (Memory.spec 0).clientState s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = s_fix)
    (hmiss : ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m))).1.1 ≠ 1)
    (htot : totalSlots n_max (gmAt 0 U V w₀ n_max (hashSpace U w₀ n_max) s_fix.mem) < n_max)
    (hb : b < numBuckets n_max) :
    (Memory.spec 0).clientState s_fix (insertWithHashProg U V w₀ n_max (((0, u), v), h_q)) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s_fix
          (pushBackSlotProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), v)))
        (prependIfIndexedProg U V w₀ n_max (hashSpace U w₀ n_max)
          (((0, b), m),
            bCount n_max (gmAt 0 U V w₀ n_max (hashSpace U w₀ n_max) s_fix.mem) b)) := by
  unfold insertWithHashProg insertWithHashGenProg
  simp only [p_bucketBits_mk, p_bucketMask_mk, insertBodyGenProg_mk, pure_bind]
  rw [hb_eq, hq_eq, hm_eq]
  unfold insertBodyProg insertBodyGenProg
  simp only [searchBucketGenProg_mk, writeValGenProg_mk, insertNewGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst, ite_eq_right hmiss]
  unfold insertNewProg insertNewGenProg
  simp only [readTotalSlotsGenProg_mk, p_nMax_mk, readBucketCountGenProg_mk,
    pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readTotalSlotsProg,
    clientResult_readTotalSlotsProg, ite_eq_left htot,
    StateTransitionSpec.clientState_bind, clientState_readBucketCountProg,
    clientResult_readBucketCountProg (0, b) s_fix hb,
    StateTransitionSpec.clientState_bind]

/-- Dictionary-level specification of Phase 2a (hit path: `found = 1`) of split compacted
insertion (`compWritePhysValGenProg`). -/
theorem compInsertHit_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) (v : ℕ) (hv : v < V)
    (hfound : sbFound ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val),
          keyQuotient (bucketBits N) u.val),
          mOfSeed U N θ (keyQuotient (bucketBits N) u.val)))) = 1) :
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let res_sb := (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m))
    let d_wv := (((mkCompParams U V w N, (metaBase, itemBase)), res_sb.2), v)
    let s' := (Memory.spec 0).clientState s (compWritePhysValGenProg d_wv)
    CompWritePhysValPre w d_wv s ∧
    CompOpFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    memoryCost (compWritePhysValGenProg d_wv) s ≤ 8 ∧
    ∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u (some v)) s_fix' ∧
      FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro q b m res_sb d_wv s'
  set h_q := hValOfSeed U N θ q
  have hsrch := compInsertSearchWithHashGenProg_dict_spec henv hfit_off hinv hcpl hm_items u
  obtain ⟨_, _, _, hf_iff, hf_slot, _⟩ := hsrch
  have hsome : (s_abs u).isSome := hf_iff.mp hfound
  obtain ⟨j_hit, hj_bc, hphys_eq⟩ := hf_slot hfound
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
  have hm_lt : m < numMicroPerBucket N := mOfSeed_lt U N θ q
  have hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem) := by
    rw [hcpl.gm_eq]; exact hb_inv.hslot
  have hv_lt : v < 2 ^ valBits V := hv.trans_le (Nat.le_pow_clog (by decide) V)
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hins_fix := insertWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u v
    ⟨Or.inr hsome, hv⟩
  set s_fix' := (Memory.spec 0).clientState s_fix
    (insertWithHashProg U V (ghostW w) N (((0, u.val), v), h_q))
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) =
        s_fix :=
    (searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m) rfl hm_lt).1
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, res_sb.2), v)) :=
    insertWithHashProg_clientState_hit U V (ghostW w) N u.val v h_q s_fix b q m
      (and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q)
      (Nat.shiftRight_eq_div_pow u.val (bucketBits N)) rfl res_sb rfl hst_sb_fix hfound
  obtain ⟨hfr_wv, hcpl_wv⟩ :=
    compWritePhysValGenProg_effect henv hcpl hslot hm_items hb_lt hj_bc hv_lt
  have hphys_lt : slotOf N (compGmAt metaBase U w N s.mem) b j_hit < N :=
    (slotOf_lt_and_injective hslot).1 b hb_lt j_hit hj_bc
  have eff_wv_fix := writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) hwf.1 hphys_lt hv_lt s_fix
  have hgm'_eq : compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s', d_wv]
    rw [hphys_eq]
    exact hcpl_wv.gm_eq.trans (eff_wv_fix.2.2.2.2.2.trans hcpl.gm_eq.symm)
  refine ⟨⟨U, V, N, m_items, s_fix, b, j_hit, rfl, henv, hcpl, hslot, hm_items,
      hb_lt, hj_bc, hphys_eq⟩,
    ?_, hgm'_eq, memoryCost_compWritePhysValGenProg_le _ s, s_fix', hins_fix.2.2.2.1, ?_⟩
  · dsimp only [s', d_wv]; rw [hphys_eq]; exact hfr_wv
  · dsimp only [s', d_wv]; rw [hs_fix'_eq, hphys_eq]; exact hcpl_wv

/-- Dictionary-level specification of Phase 2b (miss path: `found ≠ 1`, executed after
`growZeroCode` extends `s` to `s_grown` with `s_grown.mem = s.mem` and `n + 1 ≤ m_cap`) of split
compacted insertion (`compInsertAppendNewGenProg`). -/
theorem compInsertMiss_dict_spec {metaBase itemBase U V w N m_cap : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s s_grown : Memory.State}
    (henv_grown : CompEpochEnv U V w N metaBase itemBase m_cap s_grown)
    (hmem_grown : s_grown.mem = s.mem)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (htot_lt : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (u : Fin U) (v : ℕ) (hv : v < V)
    (hmiss : sbFound ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val),
          keyQuotient (bucketBits N) u.val),
          mOfSeed U N θ (keyQuotient (bucketBits N) u.val)))) ≠ 1) :
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let d_app := ((((mkCompParams U V w N, (metaBase, itemBase)), (b, m)), (u.val, v)))
    let s' := (Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app)
    CompInsertAppendNewPre w d_app s_grown ∧
    CompOpFrame metaBase itemBase U V w N m_cap s_grown s' ∧
    memoryCost (compInsertAppendNewGenProg d_app) s_grown +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 200 ∧
    ∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u (some v)) s_fix' ∧
      FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro q b m d_app s'
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
  have hm_lt : m < numMicroPerBucket N := mOfSeed_lt U N θ q
  have hwf := ghostDictParamsWf henv_grown.pos_w henv_grown.le_U henv_grown.lt_pow_U
    henv_grown.le_pow_V
  have hg_env := ghostDictEnvGen henv_grown.pos_w henv_grown.le_U henv_grown.lt_pow_U
    henv_grown.le_pow_V
  have hslot : SlotStoreInv N (compGmAt metaBase U w N s_grown.mem) := by
    rw [hmem_grown, hcpl.gm_eq]; exact hb_inv.hslot
  have hcpl_grown : FixedCoupled metaBase itemBase U V w N s_fix s_grown :=
    ⟨by simp only [hmem_grown]; exact hcpl.gm_eq,
     by simp only [hmem_grown]; exact hcpl.lm_eq,
     by simp only [hmem_grown]; exact hcpl.win_inv,
     fun i => by simp only [hmem_grown]; exact hcpl.td_lt i,
     fun i => by simp only [hmem_grown]; exact hcpl.dt_lt i,
     fun d hd => by simp only [hmem_grown] at hd ⊢; exact hcpl.quot_eq d hd,
     fun d hd => by simp only [hmem_grown] at hd ⊢; exact hcpl.val_eq d hd⟩
  have htot_grown : totalSlots N (compGmAt metaBase U w N s_grown.mem) < N := by
    rwa [hmem_grown]
  have hm_cap_grown : totalSlots N (compGmAt metaBase U w N s_grown.mem) + 1 ≤ m_cap := by
    rwa [hmem_grown]
  have hq_lt : q < 2 ^ quotientBits U N :=
    keyQuotient_lt_two_pow_quotientBits henv_grown.le_U u.isLt
  have hq_shift : u.val >>> bucketBits N < 2 ^ quotientBits U N := by
    rwa [Nat.shiftRight_eq_div_pow]
  have hv_lt : v < 2 ^ valBits V := hv.trans_le (Nat.le_pow_clog (by decide) V)
  have hold_grown : lmHead N (compLmAt metaBase U w N s_grown.mem) b m ≤ effBucketCap N := by
    rw [hmem_grown, hcpl.lm_eq]
    exact (hb_inv.hchains.1 b hb_lt m hm_lt).head_le_cap
  have hcard_lt : (Dictionary.dom s_abs).card < N := by
    rw [← hinv.htot]
    change totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N
    rwa [← hcpl.gm_eq]
  have hins_fix := insertWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u v
    ⟨Or.inl hcard_lt, hv⟩
  set h_q := hValOfSeed U N θ q
  set s_fix' := (Memory.spec 0).clientState s_fix
    (insertWithHashProg U V (ghostW w) N (((0, u.val), v), h_q))
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) =
        s_fix :=
    (searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m) rfl hm_lt).1
  have htot_fix :
      totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rwa [← hcpl.gm_eq]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v)))
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), m), bCount N (compGmAt metaBase U w N s_grown.mem) b)) := by
    rw [show bCount N (compGmAt metaBase U w N s_grown.mem) b =
        bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b from by
      rw [hmem_grown, hcpl.gm_eq]; rfl]
    exact insertWithHashProg_clientState_miss U V (ghostW w) N u.val v h_q s_fix b q m
      (and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q)
      (Nat.shiftRight_eq_div_pow u.val (bucketBits N)) rfl hst_sb_fix hmiss htot_fix hb_lt
  obtain ⟨hfr_app, hcpl_app, hcost_app⟩ := compInsertAppendNewGenProg_effect
    henv_grown hcpl_grown hslot hb_lt hm_lt htot_grown hm_cap_grown hq_lt hv_lt hold_grown
  rw [hmem_grown] at hcost_app
  refine ⟨⟨U, V, N, m_cap, s_fix, rfl, u.isLt.trans henv_grown.lt_pow_U, hq_shift, hv_lt,
      henv_grown, hcpl_grown, hslot, hb_lt, hm_lt, htot_grown, hm_cap_grown, hold_grown⟩,
    hfr_app, hcost_app, s_fix', hins_fix.2.2.2.1, ?_⟩
  rw [hs_fix'_eq]
  exact hcpl_app

/-- Dictionary-level specification of two-phase compacted deletion (`compDeletePrepWithHashGenProg`
on `s` followed by `compDeleteFinishWithHashGenProg` on `s_mid`, allowing the intermediate second
hash evaluation to overwrite limb scratch below `metaBase + offCompLM U w N`). -/
theorem compDeleteWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s s_mid : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hmid_fr : s_mid.frontier = s.frontier)
    (hmid_out : ∀ a, metaBase + offCompLM U w N ≤ a → s_mid.mem a = s.mem a)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let d_prep := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog_prep := compDeletePrepWithHashGenProg d_prep
    ∃ found j_del phys_del q_last : ℕ,
      let prep := (((found, j_del), phys_del), q_last)
      let h_q_last := hValOfSeed U N θ q_last
      let d_fin :=
        ((((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q)),
          ((found, j_del), phys_del)), h_q_last)
      let prog_fin := compDeleteFinishWithHashGenProg d_fin
      let s' := (Memory.spec 0).clientState s_mid prog_fin
      let gm₀ := compGmAt metaBase U w N s.mem
      let gm' := compGmAt metaBase U w N s'.mem
      (Memory.spec 0).clientResult s prog_prep = prep ∧
      (found = 1 ↔ (s_abs u).isSome) ∧
      CompQueryWithHashPre w d_prep s ∧
      (Memory.spec 0).clientState s prog_prep = s ∧
      q_last < 2 ^ quotientBits U N ∧
      CompDeleteFinishWithHashPre w d_fin s_mid ∧
      CompOpFrame metaBase itemBase U V w N m_items s_mid s' ∧
      (∃ s_fix' : Memory.State,
        DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u none) s_fix' ∧
        FixedCoupled metaBase itemBase U V w N s_fix' s') ∧
      memoryCost prog_prep s + memoryCost prog_fin s_mid + 98 * slotPotential N gm' ≤
        98 * slotPotential N gm₀ + 354 +
          12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q d_prep prog_prep
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre_prep⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  obtain ⟨found, j_del, phys_del, q_last, hdel_fix⟩ :=
    deleteWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u
  dsimp only at hdel_fix
  obtain ⟨hres_fix_prep, _, _, hq_last_lt, _, _, _, hinv_fix', _⟩ := hdel_fix
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_dp, hres_dp, hcost_dp⟩ := compDeletePrepBodyGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  have hc_res_mid : (Memory.spec 0).clientResult s_mid
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s_mid
  have hfix_prep_eq : (Memory.spec 0).clientResult s_fix
      (deletePrepWithHashProg U V (ghostW w) N ((0, u.val), h_q)) =
      (Memory.spec 0).clientResult s_fix
        (deletePrepProg U V (ghostW w) N (hashSpace U (ghostW w) N) (((0, b), q), m)) := by
    change (Memory.spec 0).clientResult s_fix
      (deletePrepProg U V (ghostW w) N (hashSpace U (ghostW w) N)
        (((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
          u.val >>> bucketBits N), h_q >>> bucketBits N)) = _
    rw [and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q,
      Nat.shiftRight_eq_div_pow u.val (bucketBits N)]
    rfl
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have henv_mid : CompEpochEnv U V w N metaBase itemBase m_items s_mid :=
    henv.of_mem_eq (by rw [hmid_fr])
  have h0_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have h_it : metaBase + offCompItems U w N ≤ itemBase := henv.meta_le_item
  have hlm_mid : compLmAt metaBase U w N s_mid.mem = compLmAt metaBase U w N s.mem :=
    compLmAt_congr henv.pos_w fun a ha => hmid_out a ha.1
  have hgm_mid : compGmAt metaBase U w N s_mid.mem = compGmAt metaBase U w N s.mem :=
    compGmAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have htd_mid : compTDAt metaBase U w N s_mid.mem = compTDAt metaBase U w N s.mem :=
    compTDAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hdt_mid : compDTAt metaBase U w N s_mid.mem = compDTAt metaBase U w N s.mem :=
    compDTAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hq_mid : ∀ m_i,
      compQuotAt itemBase U V w N m_i s_mid.mem = compQuotAt itemBase U V w N m_i s.mem :=
    fun _ => compQuotAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hv_mid : ∀ m_i,
      compValAt itemBase U V w N m_i s_mid.mem = compValAt itemBase U V w N m_i s.mem :=
    fun _ => compValAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hcpl_mid : FixedCoupled metaBase itemBase U V w N s_fix s_mid :=
    ⟨hgm_mid.trans hcpl.gm_eq, hlm_mid.trans hcpl.lm_eq,
      by rw [hgm_mid, htd_mid, hdt_mid]; exact hcpl.win_inv,
      fun i => by rw [htd_mid]; exact hcpl.td_lt i,
      fun i => by rw [hdt_mid]; exact hcpl.dt_lt i,
      fun d hd => by
        rw [hgm_mid, hq_mid, hdt_mid]
        exact hcpl.quot_eq d (by simpa only [epochTotalSlots, hgm_mid] using hd),
      fun d hd => by
        rw [hgm_mid, hv_mid, hdt_mid]
        exact hcpl.val_eq d (by simpa only [epochTotalSlots, hgm_mid] using hd)⟩
  refine ⟨found, j_del, phys_del, q_last, ?_⟩
  intro prep h_q_last d_fin prog_fin s' gm₀ gm'
  set m_last := mOfSeed U N θ q_last
  have hm_last_lt : m_last < numMicroPerBucket N := mOfSeed_lt U N θ q_last
  have hprep_comp_res : (Memory.spec 0).clientResult s prog_prep = prep := by
    change (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compDeletePrepBodyGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2)) = _
    rw [StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg, hc_res]
    exact (hres_dp.trans hfix_prep_eq.symm).trans hres_fix_prep
  have hprep_comp_st : (Memory.spec 0).clientState s prog_prep = s := by
    change (Memory.spec 0).clientState s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compDeletePrepBodyGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2)) = s
    rw [StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res]
    exact hst_dp
  have hprep_comp_cost : memoryCost prog_prep s ≤
      42 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
    change memoryCost
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compDeletePrepBodyGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2)) s ≤ _
    rw [memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add]
    have hgm_eq : compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem := hcpl.gm_eq
    rw [hgm_eq] at hcost_dp
    dsimp only [b, q, m] at hcost_dp hlen_pr hovf_pr ⊢
    unfold probeExcess
    omega
  have hfit_hq_last : Fits w h_q_last :=
    (fits_compFeistelCoords (s := s_mid) henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_off
      (u.isLt.trans henv.lt_pow_U) (hValOfSeed_lt U N θ q_last)).2.1
  have hfit1 : Fits w 1 := fits_const_of_offCompItems hfit_off (by decide)
  have hprep_spec_fix := deletePrepProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m)
    rfl hm_lt
  dsimp only at hprep_spec_fix
  rw [← hfix_prep_eq, hres_fix_prep] at hprep_spec_fix
  dsimp only [deletePrepFound, deletePrepIdx, deletePrepPhys] at hprep_spec_fix
  have hbm_eq := bucketMapOfState_feistelBucket henv.le_U (hValOfSeed U N θ) s_abs u
  have hfound_iff : found = 1 ↔ (s_abs u).isSome := by
    have hbr := hprep_spec_fix.2.2.2
    by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hbr
      have hsome : (s_abs u).isSome := by
        rw [← hbm_eq]; exact (hb_inv.hmap_dom b hb_lt q).mpr hex
      exact ⟨fun _ => hsome, fun _ => hbr.1⟩
    · rw [ite_eq_right hex] at hbr
      have hnot : ¬(s_abs u).isSome := by
        rw [← hbm_eq]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hex
      exact ⟨fun hf1 => False.elim (by omega), fun hs => False.elim (hnot hs)⟩
  have hfound_slot : found = 1 →
      j_del < bCount N gm₀ b ∧ phys_del = slotOf N gm₀ b j_del ∧
      (j_del < effBucketCap N → j_del ∈ L b m) ∧
      (bCount N gm₀ b - 1 < effBucketCap N → bCount N gm₀ b - 1 ∈ L b m_last) := fun hf1 => by
    have hbr := hprep_spec_fix.2.2.2
    by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hbr
      obtain ⟨_, hj_lt_fix, hq_del, hphys_eq_fix, hq_last_eq⟩ := hbr
      have hj_last_lt_fix :
          bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b - 1 <
          bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b := by omega
      have hmem_del : j_del < effBucketCap N → j_del ∈ L b m := fun hj_cap =>
        (hb_inv.hchain_mem b hb_lt m hm_lt j_del).mpr ⟨hj_lt_fix, hj_cap, by rw [hq_del]⟩
      have hmem_last :
          bCount N gm₀ b - 1 < effBucketCap N → bCount N gm₀ b - 1 ∈ L b m_last := fun hj_cap => by
        have hgm_eq : gm₀ = gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem :=
          hcpl.gm_eq
        rw [hgm_eq] at hj_cap ⊢
        exact (hb_inv.hchain_mem b hb_lt m_last hm_last_lt _).mpr
          ⟨hj_last_lt_fix, hj_cap, by dsimp only [m_last]; rw [← hq_last_eq]⟩
      have hgm_eq : gm₀ = gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem :=
        hcpl.gm_eq
      exact ⟨by rw [hgm_eq]; exact hj_lt_fix, by rw [hgm_eq]; exact hphys_eq_fix,
        hmem_del, hmem_last⟩
    · rw [ite_eq_right hex] at hbr
      omega
  have hslot_mid : SlotStoreInv N (compGmAt metaBase U w N s_mid.mem) := hgm_mid.symm ▸ hslot
  have hm_items_mid : totalSlots N (compGmAt metaBase U w N s_mid.mem) ≤ m_items :=
    hgm_mid.symm ▸ hm_items
  have hpre_fin : CompDeleteFinishWithHashPre w d_fin s_mid := by
    have hm_last_eq : h_q_last >>> cpBucketBits (mkCompParams U V w N) = m_last := by
      rw [cpBucketBits_mk]; rfl
    refine ⟨fits_compFeistelCoords henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_off
        (u.isLt.trans henv.lt_pow_U) (hValOfSeed_lt U N θ q),
      hfit_hq_last, hfit1, ?_⟩
    rw [hb_eq, hm_eq, hm_last_eq]
    intro hf1
    obtain ⟨hj_lt, hphys_eq, hmem_del, hmem_last⟩ := hfound_slot hf1
    exact ⟨U, V, N, m_items, s_fix, L, rfl, henv_mid, hcpl_mid, hslot_mid, hm_items_mid,
      hb_lt, hm_lt, hm_last_lt,
      by rw [hgm_mid]; exact hj_lt,
      by rw [hgm_mid]; exact hphys_eq,
      hb_inv.hchains, hmem_del,
      by rw [hgm_mid]; exact hmem_last⟩
  set s_fix' := (Memory.spec 0).clientState s_fix
    (deleteFinishWithHashProg U V (ghostW w) N
      ((((0, u.val), h_q), ((found, j_del), phys_del)), h_q_last))
  have hs_fix'_branch : s_fix' =
      if found = 1 then
        (Memory.spec 0).clientState s_fix
          (deleteFoundProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
            ((((0, b), j_del), phys_del), (m, m_last)))
      else s_fix := by
    dsimp only [s_fix']
    unfold deleteFinishWithHashProg deleteFinishWithHashGenProg
    simp only [p_bucketBits_mk, p_bucketMask_mk, deleteFinishGenProg_mk, pure_bind]
    rw [and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q]
    unfold deleteFinishProg deleteFinishGenProg
    simp only [deleteFoundGenProg_mk, pure_bind]
    split_ifs <;> rfl
  have hs'_branch : s' =
      if found = 1 then
        (Memory.spec 0).clientState s_mid
          (compDeleteFoundGenProg
            (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
              (m, m_last))))
      else s_mid := by
    dsimp only [s', prog_fin, d_fin, compDeleteFinishWithHashGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res_mid]
    simp only [pure_bind, compDeleteFinishGenProg, cpBucketBits_mk]
    split_ifs <;> rfl
  have hcost_fin_branch : memoryCost prog_fin s_mid =
      if found = 1 then
        memoryCost
          (compDeleteFoundGenProg
            (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
              (m, m_last)))) s_mid
      else 0 := by
    dsimp only [prog_fin, d_fin, compDeleteFinishWithHashGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s_mid) _,
      memoryCost_compFeistelCoordsProg, hc_res_mid, zero_add]
    simp only [pure_bind, compDeleteFinishGenProg, cpBucketBits_mk]
    split_ifs <;> rfl
  have hinv_fix'' : DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u none) s_fix' :=
    hinv_fix'
  refine ⟨hprep_comp_res, hfound_iff, hpre_prep, hprep_comp_st, hq_last_lt, hpre_fin, ?_⟩
  dsimp only [gm', gm₀]
  rw [hs'_branch, hcost_fin_branch]
  rw [hs_fix'_branch] at hinv_fix''
  by_cases hf1 : found = 1
  · obtain ⟨hj_lt, hphys_eq, hmem_del, hmem_last⟩ := hfound_slot hf1
    have hj_lt_mid : j_del < bCount N (compGmAt metaBase U w N s_mid.mem) b := by
      simpa only [hgm_mid] using hj_lt
    have hmem_last_mid : bCount N (compGmAt metaBase U w N s_mid.mem) b - 1 < effBucketCap N →
        bCount N (compGmAt metaBase U w N s_mid.mem) b - 1 ∈ L b m_last := by
      simpa only [hgm_mid] using hmem_last
    obtain ⟨hfr_fd, hcpl_fd, hcost_fd⟩ := compDeleteFoundGenProg_effect
      henv_mid hcpl_mid hslot_mid hm_items_mid hb_lt hm_lt hm_last_lt hj_lt_mid
      hb_inv.hchains hmem_del hmem_last_mid
    have hphys_eq_mid : slotOf N (compGmAt metaBase U w N s_mid.mem) b j_del = phys_del := by
      simpa only [hgm_mid] using hphys_eq.symm
    rw [hphys_eq_mid] at hfr_fd hcpl_fd hcost_fd
    rw [hgm_mid] at hcost_fd
    simp only [hf1, ↓reduceIte] at hinv_fix'' ⊢
    dsimp only [b, m, q] at hcost_fd ⊢
    exact ⟨hfr_fd, ⟨_, hinv_fix'', hcpl_fd⟩, by omega⟩
  · simp only [hf1, ↓reduceIte] at hinv_fix'' ⊢
    rw [hgm_mid]
    exact ⟨CompOpFrame.refl s_mid, ⟨s_fix, hinv_fix'', hcpl_mid⟩, by omega⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
