/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.MicroSearchOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Overflow-Free Word-Delta Evaluators, Feistel Coordinates, and Dispatch Helpers

Implements `compGrowDeltaGenProg`, `compShrinkDeltaGenProg`, `compFeistelCoordsProg`, the shared
precondition `CompQueryWithHashPre`, and internal `import all` helpers (`gmAt_prependIfIndexedProg`,
`compDispatch_spec`) shared across the bucket-level operations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.sbFound`: hit flag accessor.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGrowDeltaGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compShrinkDeltaGenProg`:
  overflow-free item-stream word-delta evaluators.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compFeistelCoordsProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompFeistelCoordsPre`:
  Feistel `(b, q, m)` coordinate extractor and precondition.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompQueryWithHashPre`:
  shared Feistel-dispatched query/search precondition.
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
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
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
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  rw [clientState_compItemWordsGenProg]
  exact validProg_bind (validProg_compItemWordsGen _ s) (validProg_pure _)

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
  refine validProg_bind (validProg_compItemWordsGen _ s) ?_
  rw [clientState_compItemWordsGenProg]
  exact validProg_bind (validProg_compItemWordsGen _ s) (validProg_pure _)

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
  exact Nat.xor_lt_two_pow (Nat.and_le_right.trans_lt h.2.2.2)
    (Nat.and_le_right.trans_lt h.2.2.2)

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
  have hpow : 2 ^ totalMicroBits N ≤ max N 1 := totalMicroBuckets_le N
  exact ⟨hu, hhq.trans (hpow.trans_lt (max_n_one_lt_two_pow_w hw hnU hU)),
    hcp ⟨20, by decide⟩, hcp ⟨21, by decide⟩⟩


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

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
