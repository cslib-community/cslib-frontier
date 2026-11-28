/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps
-- Unfolds `Memory.Prog` bodies in `ResizableSuccinct` and `Succinct*` for `FixedCoupled` proofs.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctMicroChain
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSearch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Doubly-Linked Micro-Chains, Two-Phase Bucket Search, and Lookup in `Memory.Prog`

This module implements the compacted `LocalMeta` doubly-linked chain primitives, Phase 1
micro-chain search, Phase 2 overflow search, combined two-phase bucket search, and lookup body in
`Memory.Prog` (`¬ReadsWidth`, certified via `by realize`, `RealizesBounded.while₀`, and
`RealizesBounded.iterate₀`), coupling every operation via `FixedCoupled` to the fixed-capacity
reference operations in `SuccinctMicroChain.lean`, `SuccinctSearch.lean`, and
`SuccinctChainOps.lean`:
* internal `LocalMeta` accessors and chain updates realizing `compPrependIfIndexedGenProg` and
  `compUnlinkIfIndexedGenProg`: `O(1)` doubly-linked micro-chain updates preserving `FixedCoupled`
  against `prependIfIndexedProg` and `unlinkIfIndexedProg`;
* `compReadPhysQuotGenProg`, `compSearchBucketGenProg`, `compQueryBodyGenProg`: read-only physical
  quotient lookup and two-phase bucket search and lookup (via internal Phase 1 micro-chain and
  Phase 2 overflow subroutines) returning the exact same results as their fixed-capacity
  counterparts on `s_fix`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPrependIfIndexedGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compUnlinkIfIndexedGenProg`:
  conditional micro-chain prepend and unlink on compacted `LocalMeta`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compReadPhysQuotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compSearchBucketGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryBodyGenProg`:
  compacted physical quotient read, two-phase bucket search, and lookup body.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPrependIfIndexedGenProg_effect`,
  `realizesBounded_compPrependIfIndexedGen`, `validProg_compPrependIfIndexedGen`:
  `FixedCoupled` equivalence to `prependIfIndexedProg` and `RealizesBounded` / `ValidProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compUnlinkIfIndexedGenProg_effect`,
  `realizesBounded_compUnlinkIfIndexedGen`, `validProg_compUnlinkIfIndexedGen`:
  `FixedCoupled` equivalence to `unlinkIfIndexedProg`, `RealizesBounded .exact`, and `ValidProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compSearchBucketGenProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compSearchBucketGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compSearchBucketGen`:
  exact result agreement with `searchBucketProg`, `O(1 + |L| + ovf)` `memoryCost`,
  `RealizesBounded .exact`, and `ValidProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryBodyGenProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compQueryBodyGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compQueryBodyGen`:
  exact result agreement with `queryBodyProg`, `RealizesBounded .exact`, and `ValidProg`.

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
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Compacted `LocalMeta` Accessors and Doubly-Linked Chain Updates -/

/-- Every entry read via `compLmAt` fits in `effBucketPosBits N` bits. -/
private theorem compLmAt_lt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) :
    compLmAt metaBase U w N mem p < 2 ^ effBucketPosBits N := by
  rcases p with ⟨c, idx⟩
  unfold compLmAt
  dsimp only
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

private theorem fits_of_lt_totalMicroBuckets_comp {N U w x : ℕ}
    (hN : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hx : x < totalMicroBuckets N) :
    Fits w x := by
  have hle : totalMicroBuckets N ≤ max N 1 := totalMicroBuckets_le N
  have hmax : max N 1 = N := max_eq_left hN
  exact lt_of_lt_of_le (lt_of_lt_of_le hx (hle.trans_eq hmax)) (hnU.trans hU.le) |>.trans_le le_rfl

/-- Writing `val < 2 ^ effBucketPosBits N` into `LocalMeta[c, idx]` preserves `CompOpFrame` and
couples directly to `writeLMProg` on `s_fix`. -/
private theorem fixedCoupled_writeCompLM (c : Fin 9)
    {metaBase itemBase U V w N m_cap idx val : ℕ} {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hidx : idx < totalMicroBuckets N) (hval : val < 2 ^ effBucketPosBits N) :
    let s' := (Memory.spec 0).clientState s
      (writeCompLMGenProg c (((mkCompParams U V w N, metaBase), idx), val))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeLMProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) c.val ((0, idx), val))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hs' := clientState_writeCompLMGenProg c U V w N metaBase idx val s
  obtain ⟨hlm_c, hgm_c, htd_c, hdt_c, hq_c, hv_c, hout_c⟩ :=
    writeCompLM_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (m_items := epochTotalSlots N (compGmAt metaBase U w N s.mem)) c hw hitem hidx hval s.mem
  obtain ⟨_, _, hq_f, hv_f, hlm_f, hgm_f⟩ :=
    writeLMProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) (c := c.val) (base := 0) (idx := idx) (val := val)
      hwg c.isLt hidx hval s_fix
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  dsimp only [s', s_fix']
  rw [hs']
  refine ⟨⟨rfl, fun a hm _ => hout_c a (by omega)⟩, ?_⟩
  unfold FixedCoupled
  dsimp only
  refine ⟨hgm_c.trans (hcpl.gm_eq.trans hgm_f.symm),
    hlm_c.trans (by rw [hcpl.lm_eq, hlm_f]),
    by rw [hgm_c, htd_c, hdt_c]; exact hcpl.win_inv,
    fun i => by rw [htd_c]; exact hcpl.td_lt i,
    fun i => by rw [hdt_c]; exact hcpl.dt_lt i,
    fun d hd => ?_,
    fun d hd => ?_⟩
  · rw [hgm_c] at hd ⊢
    rw [congrFun hq_c d, hdt_c, hq_f]
    exact hcpl.quot_eq d hd
  · rw [hgm_c] at hd ⊢
    rw [congrFun hv_c d, hdt_c, hv_f]
    exact hcpl.val_eq d hd

/-- Read `lmHead N (compLmAt metaBase U w N s.mem) b m` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compReadLMHeadGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((cp, metaBase), (b, m)) => do
    let idx ← pure (b * cpNumMicro cp + m)
    readCompLMGenProg ⟨0, by decide⟩ ((cp, metaBase), idx)

private theorem clientState_compReadLMHeadGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadLMHeadGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compReadLMHeadGenProg]; simp only [pure_bind]
  exact clientState_readCompLMGenProg ⟨0, by decide⟩ _ s

@[simp] private theorem runClient_state_compReadLMHeadGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadLMHeadGenProg d))) = s :=
  clientState_compReadLMHeadGenProg d s

@[simp] private theorem memoryCost_compReadLMHeadGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compReadLMHeadGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩
  dsimp only [compReadLMHeadGenProg]
  simp only [pure_bind, memoryCost_readCompLMGenProg]

private theorem clientResult_compReadLMHeadGenProg {U V w N metaBase b m : ℕ}
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compReadLMHeadGenProg ((mkCompParams U V w N, metaBase), (b, m))) =
      lmHead N (compLmAt metaBase U w N s.mem) b m := by
  dsimp only [compReadLMHeadGenProg, cpNumMicro_mk, lmHead]
  simp only [pure_bind]
  exact clientResult_readCompLMGenProg ⟨0, by decide⟩ (lmHeadIdx_lt hb hm) s

/-- Precondition for `compReadLMHeadGenProg`. -/
private def CompReadLMHeadPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b, m)), s =>
    CompMetaEnv w cp metaBase s ∧ b < numBuckets (cpN cp) ∧ m < numMicroPerBucket (cpN cp)

private theorem realizesBounded_compReadLMHeadGen :
    RealizesBounded .exact compReadLMHeadGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompReadLMHeadPre (fun _ _ => 0) := by
  have hrl := realizesBounded_readCompLMGen ⟨0, by decide⟩
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm⟩ := h
    simp only [cpNumMicro_mk, cpN_mk] at *)
  · exact fits_of_lt_totalMicroBuckets_comp hN hnU hU (lmHeadIdx_lt hb hm)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmHeadIdx_lt hb hm⟩

private theorem validProg_compReadLMHeadGen
    {w : ℕ} {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompReadLMHeadPre w d s) : ValidProg w 0 s (compReadLMHeadGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩
  rcases h with ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm⟩
  simp only [cpN_mk] at hb hm
  dsimp only [compReadLMHeadGenProg, cpNumMicro_mk]; simp only [pure_bind]
  exact validProg_readCompLMGen ⟨0, by decide⟩
    ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmHeadIdx_lt hb hm⟩

/-- Write `val` to `lmHead N` at `(b, m)` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compWriteLMHeadGenProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, m)), val) => do
    let idx ← pure (b * cpNumMicro cp + m)
    writeCompLMGenProg ⟨0, by decide⟩ (((cp, metaBase), idx), val)

@[simp] private theorem memoryCost_compWriteLMHeadGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compWriteLMHeadGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, val⟩
  dsimp only [compWriteLMHeadGenProg]
  simp only [pure_bind, memoryCost_writeCompLMGenProg]

private theorem frontier_compWriteLMHeadGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (compWriteLMHeadGenProg d)).frontier = s.frontier := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, val⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compWriteLMHeadGenProg, writeCompLMGenProg]
  simp [writePackedCompGenProg, writeBitSliceGenProg, writeBitSliceLowProg, writeBitSliceHighProg]

@[simp] private theorem runClient_frontier_compWriteLMHeadGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compWriteLMHeadGenProg d)))).frontier =
      s.frontier :=
  frontier_compWriteLMHeadGenProg d s

/-- Precondition for `compWriteLMHeadGenProg`. -/
private def CompWriteLMHeadPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, m)), _val), s =>
    CompMetaEnv w cp metaBase s ∧ b < numBuckets (cpN cp) ∧ m < numMicroPerBucket (cpN cp)

private theorem realizesBounded_compWriteLMHeadGen :
    RealizesBounded .exact compWriteLMHeadGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWriteLMHeadPre (fun _ _ => 0) := by
  have hwl := realizesBounded_writeCompLMGen ⟨0, by decide⟩
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, val⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm⟩ := h
    simp only [cpNumMicro_mk, cpN_mk] at *)
  · exact fits_of_lt_totalMicroBuckets_comp hN hnU hU (lmHeadIdx_lt hb hm)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmHeadIdx_lt hb hm⟩

private theorem validProg_compWriteLMHeadGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompWriteLMHeadPre w d s) :
    ValidProg w 0 s (compWriteLMHeadGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, val⟩
  rcases h with ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm⟩
  simp only [cpN_mk] at hb hm
  dsimp only [compWriteLMHeadGenProg, cpNumMicro_mk]; simp only [pure_bind]
  exact validProg_writeCompLMGen ⟨0, by decide⟩
    ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmHeadIdx_lt hb hm⟩

private theorem fixedCoupled_compWriteLMHead
    {metaBase itemBase U V w N m_cap b m val : ℕ} {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hval : val < 2 ^ effBucketPosBits N) :
    let s' := (Memory.spec 0).clientState s
      (compWriteLMHeadGenProg (((mkCompParams U V w N, metaBase), (b, m)), val))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeLMHeadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), val))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' :=
  fixedCoupled_writeCompLM ⟨0, by decide⟩ hw hitem hcpl (lmHeadIdx_lt hb hm) hval

/-- Read `compLmAt (c_base + j % 4, b * numMicroPerBucket N + j / 4)` in `Memory.Prog`. -/
private def compReadLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((cp, metaBase), (b, j)) => do
    let idx ← pure (b * cpNumMicro cp + j / 4)
    let r ← pure (j % 4)
    let c0 ← pure 0
    let c1 ← pure 1
    let c2 ← pure 2
    if r = c0 then
      readCompLMGenProg ⟨c_base, by omega⟩ ((cp, metaBase), idx)
    else if r = c1 then
      readCompLMGenProg ⟨c_base + 1, by omega⟩ ((cp, metaBase), idx)
    else if r = c2 then
      readCompLMGenProg ⟨c_base + 2, by omega⟩ ((cp, metaBase), idx)
    else
      readCompLMGenProg ⟨c_base + 3, by omega⟩ ((cp, metaBase), idx)

private theorem clientState_compReadLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadLMMod4GenProg c_base hc d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compReadLMMod4GenProg]; simp only [pure_bind]
  split_ifs <;> exact clientState_readCompLMGenProg _ _ s

@[simp] private theorem runClient_state_compReadLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadLMMod4GenProg c_base hc d))) = s :=
  clientState_compReadLMMod4GenProg c_base hc d s

@[simp] private theorem memoryCost_compReadLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compReadLMMod4GenProg c_base hc d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩
  dsimp only [compReadLMMod4GenProg]; simp only [pure_bind]
  split_ifs <;> simp only [memoryCost_readCompLMGenProg]

private theorem clientResult_compReadLMMod4GenProg {c_base : ℕ} (hc : c_base + 3 < 9)
    {U V w N metaBase b j : ℕ} (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compReadLMMod4GenProg c_base hc ((mkCompParams U V w N, metaBase), (b, j))) =
      compLmAt metaBase U w N s.mem (c_base + j % 4, b * numMicroPerBucket N + j / 4) := by
  have hidx := lmSlotIdx_lt hb hj
  have hmod : j % 4 < 4 := Nat.mod_lt j (by decide)
  dsimp only [compReadLMMod4GenProg, cpNumMicro_mk]
  simp only [pure_bind]
  split_ifs with h0 h1 h2
  · rw [h0, Nat.add_zero]
    exact clientResult_readCompLMGenProg ⟨c_base, by omega⟩ hidx s
  · rw [h1]
    exact clientResult_readCompLMGenProg ⟨c_base + 1, by omega⟩ hidx s
  · rw [h2]
    exact clientResult_readCompLMGenProg ⟨c_base + 2, by omega⟩ hidx s
  · have h3 : j % 4 = 3 := by omega
    rw [h3]
    exact clientResult_readCompLMGenProg ⟨c_base + 3, by omega⟩ hidx s

/-- Precondition for `compReadLMMod4GenProg`. -/
private def CompReadLMSlotPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b, j)), s =>
    CompMetaEnv w cp metaBase s ∧ b < numBuckets (cpN cp) ∧ j < effBucketCap (cpN cp)

private theorem realizesBounded_compReadLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) :
    RealizesBounded .exact (compReadLMMod4GenProg c_base hc)
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompReadLMSlotPre (fun _ _ => 0) := by
  have hrl0 := realizesBounded_readCompLMGen ⟨c_base, by omega⟩
  have hrl1 := realizesBounded_readCompLMGen ⟨c_base + 1, by omega⟩
  have hrl2 := realizesBounded_readCompLMGen ⟨c_base + 2, by omega⟩
  have hrl3 := realizesBounded_readCompLMGen ⟨c_base + 3, by omega⟩
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    simp only [cpNumMicro_mk, cpN_mk] at *)
  all_goals try decide
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals try exact fits_of_lt_totalMicroBuckets_comp hN hnU hU (lmSlotIdx_lt hb hj)
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmSlotIdx_lt hb hj⟩

private theorem validProg_compReadLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) {w : ℕ}
    {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State} (h : CompReadLMSlotPre w d s) :
    ValidProg w 0 s (compReadLMMod4GenProg c_base hc d) := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩
  rcases h with ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj⟩
  simp only [cpN_mk] at hb hj
  have hpre : CompLMPre w ((mkCompParams U V w N, metaBase), b * numMicroPerBucket N + j / 4) s :=
    ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmSlotIdx_lt hb hj⟩
  dsimp only [compReadLMMod4GenProg, cpNumMicro_mk]; simp only [pure_bind]
  refine validProg_ite (fun _ => validProg_readCompLMGen ⟨c_base, by omega⟩ hpre) (fun _ => ?_)
  refine validProg_ite (fun _ => validProg_readCompLMGen ⟨c_base + 1, by omega⟩ hpre) (fun _ => ?_)
  exact validProg_ite (fun _ => validProg_readCompLMGen ⟨c_base + 2, by omega⟩ hpre)
    (fun _ => validProg_readCompLMGen ⟨c_base + 3, by omega⟩ hpre)

/-- Write `val` to `compLmAt (c_base + j % 4, b * numMicroPerBucket N + j / 4)`. -/
private def compWriteLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, j)), val) => do
    let idx ← pure (b * cpNumMicro cp + j / 4)
    let r ← pure (j % 4)
    let c0 ← pure 0
    let c1 ← pure 1
    let c2 ← pure 2
    if r = c0 then
      writeCompLMGenProg ⟨c_base, by omega⟩ (((cp, metaBase), idx), val)
    else if r = c1 then
      writeCompLMGenProg ⟨c_base + 1, by omega⟩ (((cp, metaBase), idx), val)
    else if r = c2 then
      writeCompLMGenProg ⟨c_base + 2, by omega⟩ (((cp, metaBase), idx), val)
    else
      writeCompLMGenProg ⟨c_base + 3, by omega⟩ (((cp, metaBase), idx), val)

@[simp] private theorem memoryCost_compWriteLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compWriteLMMod4GenProg c_base hc d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩, val⟩
  dsimp only [compWriteLMMod4GenProg]; simp only [pure_bind]
  split_ifs <;> simp only [memoryCost_writeCompLMGenProg]

private theorem frontier_compWriteLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (compWriteLMMod4GenProg c_base hc d)).frontier = s.frontier := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩, val⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compWriteLMMod4GenProg]; simp only [pure_bind]
  split_ifs <;>
    simp [writeCompLMGenProg, writePackedCompGenProg, writeBitSliceGenProg,
      writeBitSliceLowProg, writeBitSliceHighProg]

/-- Precondition for `compWriteLMMod4GenProg`. -/
private def CompWriteLMSlotPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, j)), _val), s =>
    CompMetaEnv w cp metaBase s ∧ b < numBuckets (cpN cp) ∧ j < effBucketCap (cpN cp)

private theorem realizesBounded_compWriteLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) :
    RealizesBounded .exact (compWriteLMMod4GenProg c_base hc)
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWriteLMSlotPre (fun _ _ => 0) := by
  have hwl0 := realizesBounded_writeCompLMGen ⟨c_base, by omega⟩
  have hwl1 := realizesBounded_writeCompLMGen ⟨c_base + 1, by omega⟩
  have hwl2 := realizesBounded_writeCompLMGen ⟨c_base + 2, by omega⟩
  have hwl3 := realizesBounded_writeCompLMGen ⟨c_base + 3, by omega⟩
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩, val⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    simp only [cpNumMicro_mk, cpN_mk] at *)
  all_goals try decide
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals try exact fits_of_lt_totalMicroBuckets_comp hN hnU hU (lmSlotIdx_lt hb hj)
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmSlotIdx_lt hb hj⟩

private theorem validProg_compWriteLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) {w : ℕ}
    {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ} {s : Memory.State} (h : CompWriteLMSlotPre w d s) :
    ValidProg w 0 s (compWriteLMMod4GenProg c_base hc d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j⟩⟩, val⟩
  rcases h with ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj⟩
  simp only [cpN_mk] at hb hj
  have hpre : WriteCompLMPre w
      (((mkCompParams U V w N, metaBase), b * numMicroPerBucket N + j / 4), val) s :=
    ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, lmSlotIdx_lt hb hj⟩
  dsimp only [compWriteLMMod4GenProg, cpNumMicro_mk]; simp only [pure_bind]
  refine validProg_ite (fun _ => validProg_writeCompLMGen ⟨c_base, by omega⟩ hpre) (fun _ => ?_)
  refine validProg_ite (fun _ => validProg_writeCompLMGen ⟨c_base + 1, by omega⟩ hpre) (fun _ => ?_)
  exact validProg_ite (fun _ => validProg_writeCompLMGen ⟨c_base + 2, by omega⟩ hpre)
    (fun _ => validProg_writeCompLMGen ⟨c_base + 3, by omega⟩ hpre)

private theorem fixedCoupled_compWriteLMMod4 {c_base : ℕ} (hc : c_base + 3 < 9)
    {metaBase itemBase U V w N m_cap b j val : ℕ} {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hj : j < effBucketCap N)
    (hval : val < 2 ^ effBucketPosBits N) :
    let s' := (Memory.spec 0).clientState s
      (compWriteLMMod4GenProg c_base hc (((mkCompParams U V w N, metaBase), (b, j)), val))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeLMMod4Prog U V (ghostW w) N (epochHashSpace U (ghostW w) N) c_base (((0, b), j), val))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  have hidx := lmSlotIdx_lt hb hj
  change CompOpFrame _ _ _ _ _ _ _ _ _ ∧ FixedCoupled _ _ _ _ _ _ _ _
  dsimp only [compWriteLMMod4GenProg, writeLMMod4Prog, cpNumMicro_mk]
  simp only [pure_bind]
  split_ifs
  · exact fixedCoupled_writeCompLM ⟨c_base, by omega⟩ hw hitem hcpl hidx hval
  · exact fixedCoupled_writeCompLM ⟨c_base + 1, by omega⟩ hw hitem hcpl hidx hval
  · exact fixedCoupled_writeCompLM ⟨c_base + 2, by omega⟩ hw hitem hcpl hidx hval
  · exact fixedCoupled_writeCompLM ⟨c_base + 3, by omega⟩ hw hitem hcpl hidx hval

/-- Read `lmPrev N (compLmAt metaBase U w N s.mem) b j` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compReadLMPrevGenProg (d : (CompParams × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  compReadLMMod4GenProg 1 (by decide) d

/-- Write `val` to `lmPrev N` at `(b, j)` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compWriteLMPrevGenProg (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog Unit :=
  compWriteLMMod4GenProg 1 (by decide) d

/-- Read `lmNext N (compLmAt metaBase U w N s.mem) b j` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compReadLMNextGenProg (d : (CompParams × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  compReadLMMod4GenProg 5 (by decide) d

/-- Write `val` to `lmNext N` at `(b, j)` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compWriteLMNextGenProg (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog Unit :=
  compWriteLMMod4GenProg 5 (by decide) d

private theorem clientState_compReadLMPrevGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadLMPrevGenProg d) = s :=
  clientState_compReadLMMod4GenProg 1 (by decide) d s

private theorem clientState_compReadLMNextGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadLMNextGenProg d) = s :=
  clientState_compReadLMMod4GenProg 5 (by decide) d s

@[simp] private theorem runClient_state_compReadLMPrevGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadLMPrevGenProg d))) = s :=
  clientState_compReadLMPrevGenProg d s

@[simp] private theorem runClient_state_compReadLMNextGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadLMNextGenProg d))) = s :=
  clientState_compReadLMNextGenProg d s

@[simp] private theorem memoryCost_compReadLMPrevGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compReadLMPrevGenProg d) s = 2 :=
  memoryCost_compReadLMMod4GenProg 1 (by decide) d s

@[simp] private theorem memoryCost_compReadLMNextGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compReadLMNextGenProg d) s = 2 :=
  memoryCost_compReadLMMod4GenProg 5 (by decide) d s

@[simp] private theorem memoryCost_compWriteLMPrevGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compWriteLMPrevGenProg d) s = 4 :=
  memoryCost_compWriteLMMod4GenProg 1 (by decide) d s

@[simp] private theorem memoryCost_compWriteLMNextGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compWriteLMNextGenProg d) s = 4 :=
  memoryCost_compWriteLMMod4GenProg 5 (by decide) d s

@[simp] private theorem runClient_frontier_compWriteLMPrevGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compWriteLMPrevGenProg d)))).frontier =
      s.frontier :=
  frontier_compWriteLMMod4GenProg 1 (by decide) d s

@[simp] private theorem runClient_frontier_compWriteLMNextGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compWriteLMNextGenProg d)))).frontier =
      s.frontier :=
  frontier_compWriteLMMod4GenProg 5 (by decide) d s

private theorem clientState_frontier_compWriteLMPrevGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (compWriteLMPrevGenProg d)).frontier = s.frontier :=
  frontier_compWriteLMMod4GenProg 1 (by decide) d s

private theorem clientState_frontier_compWriteLMNextGenProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (compWriteLMNextGenProg d)).frontier = s.frontier :=
  frontier_compWriteLMMod4GenProg 5 (by decide) d s

private theorem clientResult_compReadLMPrevGenProg {U V w N metaBase b j : ℕ}
    (hb : b < numBuckets N) (hj : j < effBucketCap N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compReadLMPrevGenProg ((mkCompParams U V w N, metaBase), (b, j))) =
      lmPrev N (compLmAt metaBase U w N s.mem) b j :=
  clientResult_compReadLMMod4GenProg (by decide) hb hj s

private theorem clientResult_compReadLMNextGenProg {U V w N metaBase b j : ℕ}
    (hb : b < numBuckets N) (hj : j < effBucketCap N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compReadLMNextGenProg ((mkCompParams U V w N, metaBase), (b, j))) =
      lmNext N (compLmAt metaBase U w N s.mem) b j :=
  clientResult_compReadLMMod4GenProg (by decide) hb hj s

private theorem realizesBounded_compReadLMPrevGen :
    RealizesBounded .exact compReadLMPrevGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompReadLMSlotPre (fun _ _ => 0) :=
  realizesBounded_compReadLMMod4Gen (by decide)

private theorem realizesBounded_compWriteLMPrevGen :
    RealizesBounded .exact compWriteLMPrevGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWriteLMSlotPre (fun _ _ => 0) :=
  realizesBounded_compWriteLMMod4Gen (by decide)

private theorem realizesBounded_compReadLMNextGen :
    RealizesBounded .exact compReadLMNextGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompReadLMSlotPre (fun _ _ => 0) :=
  realizesBounded_compReadLMMod4Gen (by decide)

private theorem realizesBounded_compWriteLMNextGen :
    RealizesBounded .exact compWriteLMNextGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWriteLMSlotPre (fun _ _ => 0) :=
  realizesBounded_compWriteLMMod4Gen (by decide)

private theorem validProg_compReadLMPrevGen
    {w : ℕ} {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompReadLMSlotPre w d s) : ValidProg w 0 s (compReadLMPrevGenProg d) :=
  validProg_compReadLMMod4Gen (by decide) h

private theorem validProg_compWriteLMPrevGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompWriteLMSlotPre w d s) :
    ValidProg w 0 s (compWriteLMPrevGenProg d) :=
  validProg_compWriteLMMod4Gen (by decide) h

private theorem validProg_compReadLMNextGen
    {w : ℕ} {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompReadLMSlotPre w d s) : ValidProg w 0 s (compReadLMNextGenProg d) :=
  validProg_compReadLMMod4Gen (by decide) h

private theorem validProg_compWriteLMNextGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompWriteLMSlotPre w d s) :
    ValidProg w 0 s (compWriteLMNextGenProg d) :=
  validProg_compWriteLMMod4Gen (by decide) h

private def compLmPrependFinishProg :
    (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, metaBase), (b, m)), old_h), ptr_new) => do
    let z ← pure 0
    if z < old_h then do
      let old_idx ← pure (old_h - 1)
      compWriteLMPrevGenProg (((cp, metaBase), (b, old_idx)), ptr_new)
      compWriteLMHeadGenProg (((cp, metaBase), (b, m)), ptr_new)
    else
      compWriteLMHeadGenProg (((cp, metaBase), (b, m)), ptr_new)

private def CompLmPrependFinishPre (w : ℕ) :
    (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, metaBase), (b, m)), old_h), _ptr_new), s =>
    CompMetaEnv w cp metaBase s ∧
    b < numBuckets (cpN cp) ∧
    m < numMicroPerBucket (cpN cp) ∧
    old_h ≤ effBucketCap (cpN cp)

private theorem realizesBounded_compLmPrependFinish :
    RealizesBounded .exact compLmPrependFinishProg
      (WordEncoding.encode (α := (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmPrependFinishPre (fun _ _ => 0) := by
  have hwp := realizesBounded_compWriteLMPrevGen
  have hwh := realizesBounded_compWriteLMHeadGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, old_h⟩, ptr_new⟩
    dsimp only at *
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm, hold⟩ := h
    simp only [cpN_mk] at *)
  all_goals try omega
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, by simp only [cpN_mk]; omega⟩
  refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
  · rw [clientState_frontier_compWriteLMPrevGenProg]; exact hfr
  · simp only [cpN_mk]; exact ⟨hb, hm⟩

private def compLmWriteNodeLinksProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, j_new)), old_h) => do
    let z ← pure 0
    compWriteLMPrevGenProg (((cp, metaBase), (b, j_new)), z)
    compWriteLMNextGenProg (((cp, metaBase), (b, j_new)), old_h)

private theorem clientState_frontier_compLmWriteNodeLinksProg
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (compLmWriteNodeLinksProg d)).frontier = s.frontier := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j_new⟩⟩, old_h⟩
  dsimp only [compLmWriteNodeLinksProg]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_frontier_compWriteLMNextGenProg,
    clientState_frontier_compWriteLMPrevGenProg]

private def CompLmWriteNodeLinksPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, j_new)), _old_h), s =>
    CompMetaEnv w cp metaBase s ∧
    b < numBuckets (cpN cp) ∧
    j_new < effBucketCap (cpN cp)

private theorem realizesBounded_compLmWriteNodeLinks :
    RealizesBounded .exact compLmWriteNodeLinksProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmWriteNodeLinksPre (fun _ _ => 0) := by
  have hwp := realizesBounded_compWriteLMPrevGen
  have hwn := realizesBounded_compWriteLMNextGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, j_new⟩⟩, old_h⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩ := h)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩
  · refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, hb, hj_cap⟩
    rw [clientState_frontier_compWriteLMPrevGenProg]; exact hfr

/-- Prepend local slot `j_new` to micro-bucket chain `(b, m)` in compacted `LocalMeta`
(`¬ReadsWidth`). -/
private def compLmPrependGenProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, m)), j_new) => do
    let old_h ← compReadLMHeadGenProg ((cp, metaBase), (b, m))
    let ptr_new ← pure (j_new + 1)
    compLmWriteNodeLinksProg (((cp, metaBase), (b, j_new)), old_h)
    compLmPrependFinishProg ((((cp, metaBase), (b, m)), old_h), ptr_new)

private theorem memoryCost_compLmPrependGenProg_le
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compLmPrependGenProg d) s ≤ 18 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
  dsimp only [compLmPrependGenProg, compLmWriteNodeLinksProg, compLmPrependFinishProg]
  simp only [pure_bind, Realization.memoryCost_bind', memoryCost_compReadLMHeadGenProg,
    memoryCost_compWriteLMPrevGenProg, memoryCost_compWriteLMNextGenProg]
  split_ifs <;> simp

/-- Precondition for `compLmPrependGenProg`. -/
private def CompLmPrependPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, m)), j_new), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      j_new < effBucketCap N ∧
      j_new < N ∧
      lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N

private theorem compLmPrependGenProg_effect {metaBase itemBase U V w N m_cap b m j_new : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hj_cap : j_new < effBucketCap N) (hj_N : j_new < N)
    (hold : lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (compLmPrependGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_new))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (lmPrependProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro s' s_fix'
  set old_h := lmHead N (compLmAt metaBase U w N s.mem) b m
  have hold_fix : lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b m =
      old_h := by dsimp only [old_h]; rw [hcpl.lm_eq]
  have hval_lt : j_new + 1 < 2 ^ effBucketPosBits N :=
    (Nat.succ_le_of_lt (lt_min hj_N hj_cap)).trans_lt
      (min_effBucketCap_lt_two_pow_effBucketPosBits N)
  have h0_lt : 0 < 2 ^ effBucketPosBits N := Nat.two_pow_pos _
  have hold_lt : old_h < 2 ^ effBucketPosBits N := compLmAt_lt metaBase U w N s.mem _
  obtain ⟨hf1, hc1⟩ := fixedCoupled_compWriteLMMod4 (c_base := 1) (by decide)
    (m_cap := m_cap) hw hitem hcpl hb hj_cap h0_lt
  obtain ⟨hf2, hc2⟩ := fixedCoupled_compWriteLMMod4 (c_base := 5) (by decide)
    (m_cap := m_cap) hw hitem hc1 hb hj_cap hold_lt
  set s₂ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s
      (compWriteLMPrevGenProg (((mkCompParams U V w N, metaBase), (b, j_new)), 0)))
    (compWriteLMNextGenProg (((mkCompParams U V w N, metaBase), (b, j_new)), old_h))
  set sf₂ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_fix
      (writeLMPrevProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), j_new), 0)))
    (writeLMNextProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), j_new), old_h))
  have hs'_eq : s' = (Memory.spec 0).clientState s₂
      (compLmPrependFinishProg
        ((((mkCompParams U V w N, metaBase), (b, m)), old_h), j_new + 1)) := by
    dsimp only [s', s₂, compLmPrependGenProg, compLmWriteNodeLinksProg]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_compReadLMHeadGenProg,
      clientResult_compReadLMHeadGenProg hb hm s,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState sf₂
      (if 0 < old_h then do
        writeLMPrevProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), old_h - 1), j_new + 1)
        writeLMHeadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_new + 1)
      else
        writeLMHeadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), m), j_new + 1)) := by
    dsimp only [s_fix', sf₂]; unfold lmPrependProg lmPrependGenProg
    simp only [readLMHeadGenProg_mk, writeLMPrevGenProg_mk, writeLMNextGenProg_mk,
      writeLMHeadGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readLMHeadProg,
      clientResult_readLMHeadProg s_fix hb hm, hold_fix,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  rw [hs'_eq, hs_fix'_eq]
  dsimp only [compLmPrependFinishProg]; simp only [pure_bind]
  split_ifs with hpos
  · have hold_idx : old_h - 1 < effBucketCap N := by omega
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    obtain ⟨hf3, hc3⟩ := fixedCoupled_compWriteLMMod4 (c_base := 1) (by decide)
      (m_cap := m_cap) hw hitem hc2 hb hold_idx hval_lt
    obtain ⟨hf4, hc4⟩ := fixedCoupled_compWriteLMHead
      (m_cap := m_cap) hw hitem hc3 hb hm hval_lt
    exact ⟨hf1.trans (hf2.trans (hf3.trans hf4)), hc4⟩
  · obtain ⟨hf4, hc4⟩ := fixedCoupled_compWriteLMHead
      (m_cap := m_cap) hw hitem hc2 hb hm hval_lt
    exact ⟨hf1.trans (hf2.trans hf4), hc4⟩

private theorem realizesBounded_compLmPrependGen :
    RealizesBounded .exact compLmPrependGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmPrependPre (fun _ _ => 0) := by
  have hrh := realizesBounded_compReadLMHeadGen
  have hwl := realizesBounded_compLmWriteNodeLinks
  have hfin := realizesBounded_compLmPrependFinish
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, hj_N, hold⟩ := h
    have henv : ∀ s' : Memory.State, s'.frontier = s.frontier →
        CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
      fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩)
  · exact ⟨henv s rfl, by simp only [cpN_mk]; exact ⟨hb, hm⟩⟩
  · exact lt_of_le_of_lt (by omega) hU
  · rw [clientState_compReadLMHeadGenProg]
    exact ⟨henv s rfl, by simp only [cpN_mk]; exact ⟨hb, hj_cap⟩⟩
  · refine ⟨henv _ ?_, ?_⟩
    · rw [clientState_frontier_compLmWriteNodeLinksProg, clientState_compReadLMHeadGenProg]
    · dsimp only
      rw [clientResult_compReadLMHeadGenProg hb hm s]
      simp only [cpN_mk]
      exact ⟨hb, hm, hold⟩

private theorem validProg_compLmPrependGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompLmPrependPre w d s) :
    ValidProg w 0 s (compLmPrependGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, _hj_N, hold⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  dsimp only [compLmPrependGenProg, compLmWriteNodeLinksProg, compLmPrependFinishProg]
  simp only [pure_bind, bind_assoc]
  refine validProg_bind (validProg_compReadLMHeadGen ⟨mkEnv s rfl, hb, hm⟩) ?_
  rw [clientState_compReadLMHeadGenProg, clientResult_compReadLMHeadGenProg hb hm s]
  refine validProg_bind (validProg_compWriteLMPrevGen ⟨mkEnv s rfl, hb, hj_cap⟩) ?_
  set s₁ := (Memory.spec 0).clientState s
    (compWriteLMPrevGenProg (((mkCompParams U V w N, metaBase), (b, j_new)), 0))
  have hs₁ : s₁.frontier = s.frontier := frontier_compWriteLMMod4GenProg 1 (by decide) _ s
  refine validProg_bind (validProg_compWriteLMNextGen ⟨mkEnv s₁ hs₁, hb, hj_cap⟩) ?_
  set s₂ := (Memory.spec 0).clientState s₁
    (compWriteLMNextGenProg (((mkCompParams U V w N, metaBase), (b, j_new)),
      lmHead N (compLmAt metaBase U w N s.mem) b m))
  have hs₂ : s₂.frontier = s.frontier :=
    (frontier_compWriteLMMod4GenProg 5 (by decide) _ s₁).trans hs₁
  refine validProg_ite (fun hpos => ?_)
    (fun _ => validProg_compWriteLMHeadGen ⟨mkEnv s₂ hs₂, hb, hm⟩)
  have hold_idx : lmHead N (compLmAt metaBase U w N s.mem) b m - 1 < effBucketCap N := by omega
  refine validProg_bind (validProg_compWriteLMPrevGen ⟨mkEnv s₂ hs₂, hb, hold_idx⟩) ?_
  set s₃ := (Memory.spec 0).clientState s₂
    (compWriteLMPrevGenProg (((mkCompParams U V w N, metaBase),
      (b, lmHead N (compLmAt metaBase U w N s.mem) b m - 1)), j_new + 1))
  have hs₃ : s₃.frontier = s.frontier :=
    (frontier_compWriteLMMod4GenProg 1 (by decide) _ s₂).trans hs₂
  exact validProg_compWriteLMHeadGen ⟨mkEnv s₃ hs₃, hb, hm⟩

private def compLmUnlinkFirstProg :
    (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, metaBase), (b, m)), p), n) => do
    let z ← pure 0
    if z < p then
      compWriteLMNextGenProg (((cp, metaBase), (b, p - 1)), n)
    else
      compWriteLMHeadGenProg (((cp, metaBase), (b, m)), n)

private def CompLmUnlinkFirstPre (w : ℕ) :
    (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, metaBase), (b, m)), p), _n), s =>
    CompMetaEnv w cp metaBase s ∧
    b < numBuckets (cpN cp) ∧
    m < numMicroPerBucket (cpN cp) ∧
    p ≤ effBucketCap (cpN cp)

private theorem realizesBounded_compLmUnlinkFirst :
    RealizesBounded .exact compLmUnlinkFirstProg
      (WordEncoding.encode (α := (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmUnlinkFirstPre (fun _ _ => 0) := by
  have hwn := realizesBounded_compWriteLMNextGen
  have hwh := realizesBounded_compWriteLMHeadGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, p⟩, n⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm, hp_le⟩ := h
    simp only [cpN_mk] at *)
  all_goals try omega
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, by simp only [cpN_mk]; omega⟩
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hm⟩

private def compLmUnlinkSecondProg :
    (((CompParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, metaBase), b), p), n) => do
    let z ← pure 0
    if z < n then
      compWriteLMPrevGenProg (((cp, metaBase), (b, n - 1)), p)
    else
      pure ()

private def CompLmUnlinkSecondPre (w : ℕ) :
    (((CompParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, metaBase), b), _p), n), s =>
    CompMetaEnv w cp metaBase s ∧
    b < numBuckets (cpN cp) ∧
    n ≤ effBucketCap (cpN cp)

private theorem realizesBounded_compLmUnlinkSecond :
    RealizesBounded .exact compLmUnlinkSecondProg
      (WordEncoding.encode (α := (((CompParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmUnlinkSecondPre (fun _ _ => 0) := by
  have hwp := realizesBounded_compWriteLMPrevGen
  realize
  · omega
  · rcases d with ⟨⟨⟨⟨cp, metaBase⟩, b⟩, p⟩, n⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hn_le⟩ := h
    simp only [cpN_mk] at hb hn_le ⊢
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, by simp only [cpN_mk]; omega⟩

/-- Unlink local slot `j_del` from micro-bucket chain `(b, m)` in compacted `LocalMeta`
(`¬ReadsWidth`). -/
private def compLmUnlinkGenProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, m)), j_del) => do
    let p ← compReadLMPrevGenProg ((cp, metaBase), (b, j_del))
    let n ← compReadLMNextGenProg ((cp, metaBase), (b, j_del))
    compLmUnlinkFirstProg ((((cp, metaBase), (b, m)), p), n)
    compLmUnlinkSecondProg ((((cp, metaBase), b), p), n)

private theorem memoryCost_compLmUnlinkGenProg_le
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compLmUnlinkGenProg d) s ≤ 12 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
  dsimp only [compLmUnlinkGenProg, compLmUnlinkFirstProg, compLmUnlinkSecondProg]
  simp only [pure_bind, Realization.memoryCost_bind', memoryCost_compReadLMPrevGenProg,
    memoryCost_compReadLMNextGenProg]
  split_ifs <;> simp

/-- Precondition for `compLmUnlinkGenProg`. -/
private def CompLmUnlinkPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, m)), j_del), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      j_del < effBucketCap N ∧
      lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
      lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N

private theorem compLmUnlinkGenProg_effect {metaBase itemBase U V w N m_cap b m j_del : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hj_cap : j_del < effBucketCap N)
    (hp_le : lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N)
    (hn_le : lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (compLmUnlinkGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (lmUnlinkProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_del))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro s' s_fix'
  set p := lmPrev N (compLmAt metaBase U w N s.mem) b j_del
  set n := lmNext N (compLmAt metaBase U w N s.mem) b j_del
  have hp_fix : lmPrev N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b j_del
      = p := by dsimp only [p]; rw [hcpl.lm_eq]
  have hn_fix : lmNext N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b j_del
      = n := by dsimp only [n]; rw [hcpl.lm_eq]
  have hp_lt : p < 2 ^ effBucketPosBits N := compLmAt_lt metaBase U w N s.mem _
  have hn_lt : n < 2 ^ effBucketPosBits N := compLmAt_lt metaBase U w N s.mem _
  set s₁ := (Memory.spec 0).clientState s
    (compLmUnlinkFirstProg ((((mkCompParams U V w N, metaBase), (b, m)), p), n))
  set sf₁ := if 0 < p then
      (Memory.spec 0).clientState s_fix
        (writeLMNextProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), p - 1), n))
    else
      (Memory.spec 0).clientState s_fix
        (writeLMHeadProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), n))
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (if 0 < n then
        compWriteLMPrevGenProg (((mkCompParams U V w N, metaBase), (b, n - 1)), p)
      else pure ()) := by
    dsimp only [s', s₁, p, n, compLmUnlinkGenProg, compLmUnlinkSecondProg]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_compReadLMPrevGenProg,
      clientResult_compReadLMPrevGenProg hb hj_cap s,
      StateTransitionSpec.clientState_bind, clientState_compReadLMNextGenProg,
      clientResult_compReadLMNextGenProg hb hj_cap s,
      StateTransitionSpec.clientState_bind]
  have hs_fix'_eq : s_fix' = if 0 < n then
      (Memory.spec 0).clientState sf₁
        (writeLMPrevProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), n - 1), p))
    else sf₁ := by
    dsimp only [s_fix', sf₁]; unfold lmUnlinkProg lmUnlinkGenProg
    simp only [readLMPrevGenProg_mk, readLMNextGenProg_mk, writeLMNextGenProg_mk,
      writeLMHeadGenProg_mk, writeLMPrevGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readLMPrevProg,
      clientResult_readLMPrevProg s_fix hb hj_cap, hp_fix,
      StateTransitionSpec.clientState_bind, clientState_readLMNextProg,
      clientResult_readLMNextProg s_fix hb hj_cap, hn_fix]
    split_ifs <;> rw [StateTransitionSpec.clientState_bind] <;> rfl
  have hstep1 : CompOpFrame metaBase itemBase U V w N m_cap s s₁ ∧
      FixedCoupled metaBase itemBase U V w N sf₁ s₁ := by
    dsimp only [s₁, sf₁, compLmUnlinkFirstProg]; simp only [pure_bind]
    split_ifs with hp_pos
    · have hp_idx : p - 1 < effBucketCap N := by omega
      exact fixedCoupled_compWriteLMMod4 (c_base := 5) (by decide)
        hw hitem hcpl hb hp_idx hn_lt
    · exact fixedCoupled_compWriteLMHead hw hitem hcpl hb hm hn_lt
  obtain ⟨hf1, hc1⟩ := hstep1
  rw [hs'_eq, hs_fix'_eq]
  split_ifs with hn_pos
  · have hn_idx : n - 1 < effBucketCap N := by omega
    obtain ⟨hf2, hc2⟩ := fixedCoupled_compWriteLMMod4 (c_base := 1) (by decide)
      (m_cap := m_cap) hw hitem hc1 hb hn_idx hp_lt
    exact ⟨hf1.trans hf2, hc2⟩
  · exact ⟨hf1, hc1⟩

private theorem realizesBounded_compLmUnlinkGen :
    RealizesBounded .exact compLmUnlinkGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompLmUnlinkPre (fun _ _ => 0) := by
  have hrp := realizesBounded_compReadLMPrevGen
  have hrn := realizesBounded_compReadLMNextGen
  have hfst := realizesBounded_compLmUnlinkFirst
  have hsnd := realizesBounded_compLmUnlinkSecond
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, _, _⟩ := h
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, _, _⟩ := h
    rw [clientState_compReadLMPrevGenProg]
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, hp_le, _⟩ := h
    dsimp only
    rw [clientState_compReadLMPrevGenProg, clientResult_compReadLMPrevGenProg hb hj_cap s,
      clientState_compReadLMNextGenProg]
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact ⟨hb, hm, hp_le⟩⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, _, hn_le⟩ := h
    dsimp only
    rw [clientState_compReadLMPrevGenProg, clientResult_compReadLMNextGenProg hb hj_cap s,
      clientState_compReadLMNextGenProg]
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
    · dsimp only [compLmUnlinkFirstProg]; simp only [pure_bind]
      split_ifs
      · rw [clientState_frontier_compWriteLMNextGenProg]; exact hfr
      · rw [StateTransitionSpec.clientState, runClient_frontier_compWriteLMHeadGenProg]
        exact hfr
    · simp only [cpN_mk]; exact ⟨hb, hn_le⟩

private theorem validProg_compLmUnlinkGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompLmUnlinkPre w d s) :
    ValidProg w 0 s (compLmUnlinkGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, hp_le, hn_le⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  dsimp only [compLmUnlinkGenProg, compLmUnlinkFirstProg, compLmUnlinkSecondProg]
  simp only [pure_bind]
  refine validProg_bind (validProg_compReadLMPrevGen ⟨mkEnv s rfl, hb, hj_cap⟩) ?_
  rw [clientState_compReadLMPrevGenProg, clientResult_compReadLMPrevGenProg hb hj_cap s]
  refine validProg_bind (validProg_compReadLMNextGen ⟨mkEnv s rfl, hb, hj_cap⟩) ?_
  rw [clientState_compReadLMNextGenProg, clientResult_compReadLMNextGenProg hb hj_cap s]
  refine validProg_bind
    (validProg_ite
      (fun hp_pos => validProg_compWriteLMNextGen
        ⟨mkEnv s rfl, by simp only [cpN_mk]; exact ⟨hb, by omega⟩⟩)
      (fun _ => validProg_compWriteLMHeadGen ⟨mkEnv s rfl, hb, hm⟩)) ?_
  set s₁ := (Memory.spec 0).clientState s
    (if 0 < lmPrev N (compLmAt metaBase U w N s.mem) b j_del then
      compWriteLMNextGenProg (((mkCompParams U V w N, metaBase),
        (b, lmPrev N (compLmAt metaBase U w N s.mem) b j_del - 1)),
        lmNext N (compLmAt metaBase U w N s.mem) b j_del)
    else
      compWriteLMHeadGenProg (((mkCompParams U V w N, metaBase), (b, m)),
        lmNext N (compLmAt metaBase U w N s.mem) b j_del))
  have hs₁ : s₁.frontier = s.frontier := by
    dsimp only [s₁, StateTransitionSpec.clientState]
    split_ifs
    · exact runClient_frontier_compWriteLMNextGenProg _ s
    · exact runClient_frontier_compWriteLMHeadGenProg _ s
  exact validProg_ite
    (fun hn_pos => validProg_compWriteLMPrevGen
      ⟨mkEnv s₁ hs₁, by simp only [cpN_mk]; exact ⟨hb, by omega⟩⟩)
    (fun _ => validProg_pure ())

/-- Conditionally prepend `j_new` to micro-chain `(b, m)` when `j_new < min N (effBucketCap N)`. -/
def compPrependIfIndexedGenProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, m)), j_new) => do
    let cap ← pure (cpMinCap cp)
    if j_new < cap then
      compLmPrependGenProg (((cp, metaBase), (b, m)), j_new)
    else
      pure ()

theorem memoryCost_compPrependIfIndexedGenProg_le
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compPrependIfIndexedGenProg d) s ≤ 18 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
  dsimp only [compPrependIfIndexedGenProg]; simp only [pure_bind]
  split_ifs
  · exact memoryCost_compLmPrependGenProg_le _ s
  · simp

/-- Precondition for `compPrependIfIndexedGenProg`. -/
@[expose] def CompPrependIfIndexedPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, m)), _j_new), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N

theorem compPrependIfIndexedGenProg_effect {metaBase itemBase U V w N m_cap b m j_new : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hold : lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (compPrependIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_new))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  change CompOpFrame _ _ _ _ _ _ _ _ _ ∧ FixedCoupled _ _ _ _ _ _ _ _
  dsimp only [compPrependIfIndexedGenProg, prependIfIndexedProg, prependIfIndexedGenProg,
    cpMinCap_mk]
  simp only [p_minCap_mk, lmPrependGenProg_mk, pure_bind]
  split_ifs with hlt
  · obtain ⟨hj_N, hj_cap⟩ := lt_min_iff.mp hlt
    exact compLmPrependGenProg_effect hw hitem hcpl hb hm hj_cap hj_N hold
  · exact ⟨CompOpFrame.refl s, hcpl⟩

theorem realizesBounded_compPrependIfIndexedGen :
    RealizesBounded .exact compPrependIfIndexedGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPrependIfIndexedPre (fun _ _ => 0) := by
  have hp := realizesBounded_compLmPrependGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hold⟩ := h
  simp only [cpMinCap_mk] at *
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, by omega, by omega, hold⟩

theorem validProg_compPrependIfIndexedGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPrependIfIndexedPre w d s) :
    ValidProg w 0 s (compPrependIfIndexedGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_new⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hold⟩ := h
  dsimp only [compPrependIfIndexedGenProg, cpMinCap_mk]; simp only [pure_bind]
  exact validProg_ite
    (fun hlt => validProg_compLmPrependGen
      ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, by omega, by omega, hold⟩)
    (fun _ => validProg_pure ())

/-- Conditionally unlink `j_del` from micro-chain `(b, m)` when `j_del < min N (effBucketCap N)`. -/
def compUnlinkIfIndexedGenProg : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, m)), j_del) => do
    let cap ← pure (cpMinCap cp)
    if j_del < cap then
      compLmUnlinkGenProg (((cp, metaBase), (b, m)), j_del)
    else
      pure ()

theorem memoryCost_compUnlinkIfIndexedGenProg_le
    (d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compUnlinkIfIndexedGenProg d) s ≤ 12 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
  dsimp only [compUnlinkIfIndexedGenProg]; simp only [pure_bind]
  split_ifs
  · exact memoryCost_compLmUnlinkGenProg_le _ s
  · simp

/-- Precondition for `compUnlinkIfIndexedGenProg`. -/
@[expose] def CompUnlinkIfIndexedPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, m)), j_del), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      (j_del < effBucketCap N →
        lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
        lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N)

theorem compUnlinkIfIndexedGenProg_effect {metaBase itemBase U V w N m_cap b m j_del : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hbounds : j_del < effBucketCap N →
      lmPrev N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N ∧
      lmNext N (compLmAt metaBase U w N s.mem) b j_del ≤ effBucketCap N) :
    let s' := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_del))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  change CompOpFrame _ _ _ _ _ _ _ _ _ ∧ FixedCoupled _ _ _ _ _ _ _ _
  dsimp only [compUnlinkIfIndexedGenProg, unlinkIfIndexedProg, unlinkIfIndexedGenProg, cpMinCap_mk]
  simp only [p_minCap_mk, lmUnlinkGenProg_mk, pure_bind]
  split_ifs with hlt
  · have hj_cap : j_del < effBucketCap N := (lt_min_iff.mp hlt).2
    obtain ⟨hp_le, hn_le⟩ := hbounds hj_cap
    exact compLmUnlinkGenProg_effect hw hitem hcpl hb hm hj_cap hp_le hn_le
  · exact ⟨CompOpFrame.refl s, hcpl⟩

theorem realizesBounded_compUnlinkIfIndexedGen :
    RealizesBounded .exact compUnlinkIfIndexedGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompUnlinkIfIndexedPre (fun _ _ => 0) := by
  have hu := realizesBounded_compLmUnlinkGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hbounds⟩ := h
  simp only [cpMinCap_mk] at *
  · have hj_cap : j_del < effBucketCap N := by omega
    obtain ⟨hp_le, hn_le⟩ := hbounds hj_cap
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, hp_le, hn_le⟩

theorem validProg_compUnlinkIfIndexedGen {w : ℕ} {d : ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompUnlinkIfIndexedPre w d s) :
    ValidProg w 0 s (compUnlinkIfIndexedGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, m⟩⟩, j_del⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hbounds⟩ := h
  dsimp only [compUnlinkIfIndexedGenProg, cpMinCap_mk]; simp only [pure_bind]
  exact validProg_ite
    (fun hlt => by
      have hj_cap : j_del < effBucketCap N := by omega
      obtain ⟨hp_le, hn_le⟩ := hbounds hj_cap
      exact validProg_compLmUnlinkGen
        ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb, hm, hj_cap, hp_le, hn_le⟩)
    (fun _ => validProg_pure ())

/-! ## Section 2: Phase 1 Micro-Chain Search (`compSearchMicroChainGenProg`) -/

theorem memoryCost_denseOfPhysGenProg_le (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (denseOfPhysGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨cp, metaBase⟩, g⟩
  dsimp only [denseOfPhysGenProg]; simp only [pure_bind]
  split_ifs
  · simp
  · simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      runClient_state_readCompGMGenProg]
    split_ifs
    · simp
    · simp only [Realization.memoryCost_bind', memoryCost_readCompTDGenProg,
        runClient_state_readCompTDGenProg, memoryCost_denseOfCircGenProg]
      omega

theorem clientResult_denseOfPhys_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (_henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (denseOfPhysGenProg ((mkCompParams U V w N, metaBase),
          slotOf N (compGmAt metaBase U w N s.mem) b j)) =
      denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem)
        (slotOf N (compGmAt metaBase U w N s.mem) b j) := by
  set gm := compGmAt metaBase U w N s.mem
  set g := slotOf N gm b j
  refine clientResult_denseOfPhysGenProg fun hb_pos hg_ge => ?_
  have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
  have htd := hcpl.tailDenseInv hb_pos
  have htail := hslot.multi_tail hb_pos
  have hSN := hslot.multi_total_le hb_pos
  have hM_le : gm 1 ≤ maxTailItems N := htail.ntails_eq.trans_le htail.ntails_le
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
  exact ⟨lt_of_lt_of_le ht_lt hM_le, htd.td_lt _ ht_lt⟩

/-- Resolve physical slot `phys` through `denseOfPhysGenProg` and read its dense quotient. -/
def compReadPhysQuotGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((cp, (metaBase, itemBase)), phys) => do
    let d_idx ← denseOfPhysGenProg ((cp, metaBase), phys)
    readCompQuotGenProg ((cp, itemBase), d_idx)

theorem clientState_compReadPhysQuotGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadPhysQuotGenProg d) = s := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compReadPhysQuotGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_denseOfPhysGenProg, runClient_state_readCompQuotGenProg]

@[simp] theorem runClient_state_compReadPhysQuotGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadPhysQuotGenProg d))) = s :=
  clientState_compReadPhysQuotGenProg d s

theorem memoryCost_compReadPhysQuotGenProg_le
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compReadPhysQuotGenProg d) s ≤ 6 := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  dsimp only [compReadPhysQuotGenProg]
  simp only [Realization.memoryCost_bind', runClient_state_denseOfPhysGenProg,
    memoryCost_readCompQuotGenProg]
  have h1 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase), phys) s
  omega

theorem clientResult_compReadPhysQuot_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (compReadPhysQuotGenProg ((mkCompParams U V w N, (metaBase, itemBase)),
          slotOf N (compGmAt metaBase U w N s.mem) b j)) =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
        (slotOf N (compGmAt metaBase U w N s.mem) b j) := by
  obtain ⟨hd_lt, hq_eq, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  dsimp only [compReadPhysQuotGenProg]
  rw [prog_clientResult_bind, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj,
    clientState_denseOfPhysGenProg,
    clientResult_readCompQuotGenProg (lt_of_lt_of_le hd_lt hm_items), hq_eq]

/-- Precondition for `compReadPhysQuotGenProg` and `compReadPhysValGenProg`. -/
@[expose] def CompReadPhysItemPre (w : ℕ) :
    (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), phys), s =>
    ∃ U V N m_items s_fix b j,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      phys = slotOf N (compGmAt metaBase U w N s.mem) b j

theorem realizesBounded_compReadPhysQuotGen :
    RealizesBounded .exact compReadPhysQuotGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompReadPhysItemPre (fun _ _ => 0) := by
  have hdp := realizesBounded_denseOfPhysGen
  have hrq := realizesBounded_readCompQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
    obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
      hb, hj, rfl⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_denseOfPhysGenProg] at *)
  · exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj
  · rw [clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
    obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
    exact ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

theorem validProg_compReadPhysQuotGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompReadPhysItemPre w d s) :
    ValidProg w 0 s (compReadPhysQuotGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
    hb, hj, rfl⟩ := h
  dsimp only [compReadPhysQuotGenProg]
  refine validProg_bind (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  exact validProg_readCompQuotGen ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

/-- Resolve physical slot `phys` through `denseOfPhysGenProg` and read its dense value. -/
private def compReadPhysValGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((cp, (metaBase, itemBase)), phys) => do
    let d_idx ← denseOfPhysGenProg ((cp, metaBase), phys)
    readCompValGenProg ((cp, itemBase), d_idx)

private theorem clientState_compReadPhysValGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compReadPhysValGenProg d) = s := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compReadPhysValGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_denseOfPhysGenProg, runClient_state_readCompValGenProg]

@[simp] private theorem runClient_state_compReadPhysValGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compReadPhysValGenProg d))) = s :=
  clientState_compReadPhysValGenProg d s

private theorem memoryCost_compReadPhysValGenProg_le
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compReadPhysValGenProg d) s ≤ 6 := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  dsimp only [compReadPhysValGenProg]
  simp only [Realization.memoryCost_bind', runClient_state_denseOfPhysGenProg,
    memoryCost_readCompValGenProg]
  have h1 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase), phys) s
  omega

private theorem clientResult_compReadPhysVal_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (compReadPhysValGenProg ((mkCompParams U V w N, (metaBase, itemBase)),
          slotOf N (compGmAt metaBase U w N s.mem) b j)) =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
        (slotOf N (compGmAt metaBase U w N s.mem) b j) := by
  obtain ⟨hd_lt, _, hv_eq⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  dsimp only [compReadPhysValGenProg]
  rw [prog_clientResult_bind, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj,
    clientState_denseOfPhysGenProg,
    clientResult_readCompValGenProg (lt_of_lt_of_le hd_lt hm_items), hv_eq]

private theorem realizesBounded_compReadPhysValGen :
    RealizesBounded .exact compReadPhysValGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompReadPhysItemPre (fun _ _ => 0) := by
  have hdp := realizesBounded_denseOfPhysGen
  have hrv := realizesBounded_readCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
    obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
      hb, hj, rfl⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_denseOfPhysGenProg] at *)
  · exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj
  · rw [clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
    obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
    exact ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

private theorem validProg_compReadPhysValGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompReadPhysItemPre w d s) :
    ValidProg w 0 s (compReadPhysValGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
  obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
    hb, hj, rfl⟩ := h
  dsimp only [compReadPhysValGenProg]
  refine validProg_bind (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  exact validProg_readCompValGen ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

private def compMicroFetchProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), j) => do
    let next_ptr ← compReadLMNextGenProg ((cp, metaBase), (b, j))
    let phys ← compResolveIndexedSlotGenProg (((cp, metaBase), b), j)
    pure (next_ptr, phys)

private theorem clientState_compMicroFetchProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compMicroFetchProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compMicroFetchProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compReadLMNextGenProg, runClient_state_compResolveIndexedSlotGenProg,
    prog_runClient_state_pure]

@[simp] private theorem runClient_state_compMicroFetchProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compMicroFetchProg d))) = s :=
  clientState_compMicroFetchProg d s

private theorem clientResult_compMicroFetchProg {U V w N metaBase b j : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hj_cap : j < effBucketCap N) :
    (Memory.spec 0).clientResult s
        (compMicroFetchProg (((mkCompParams U V w N, metaBase), b), j)) =
      (lmNext N (compLmAt metaBase U w N s.mem) b j,
       slotOf N (compGmAt metaBase U w N s.mem) b j) := by
  dsimp only [compMicroFetchProg]
  rw [prog_clientResult_bind, clientResult_compReadLMNextGenProg hb hj_cap s,
    clientState_compReadLMNextGenProg,
    prog_clientResult_bind, clientResult_compResolveIndexedSlotGenProg hslot hb hj_bc hj_cap,
    clientState_compResolveIndexedSlotGenProg, prog_clientResult_pure]

private theorem realizesBounded_compMicroFetch :
    RealizesBounded .exact compMicroFetchProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveIndexedSlotPre (fun _ _ => 0) := by
  have hrn := realizesBounded_compReadLMNextGen
  have hrs := realizesBounded_compResolveIndexedSlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
    simp only [StateTransitionSpec.clientState,
      runClient_state_compReadLMNextGenProg] at *)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩

private theorem validProg_compMicroFetch {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompResolveIndexedSlotPre w d s) :
    ValidProg w 0 s (compMicroFetchProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
  dsimp only [compMicroFetchProg]
  refine validProg_bind
    (validProg_compReadLMNextGen ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb, hj_cap⟩) ?_
  rw [clientState_compReadLMNextGenProg]
  refine validProg_bind
    (validProg_compResolveIndexedSlotGen
      ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩) ?_
  exact validProg_pure _

/-- Context type `(((cp, (metaBase, itemBase)), (b, q_target)), z0)` for `compMicroLoopGenProg`. -/
private abbrev CompMicroCtx : Type := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ

/-- Accumulator type `(((ptr, found), j_found), phys_found)` for `compMicroLoopGenProg`. -/
private abbrev CompMicroAcc : Type := ((ℕ × ℕ) × ℕ) × ℕ

/-- Single step of compacted Phase 1 micro-chain traversal (`¬ReadsWidth`). -/
private def compMicroStepGenProg : CompMicroCtx × CompMicroAcc → Memory.Prog CompMicroAcc
  | ((((cp, (metaBase, itemBase)), (b, q_target)), _z0),
     (((ptr, _found), j_found), phys_found)) => do
    let j ← pure (ptr - 1)
    let np ← compMicroFetchProg (((cp, metaBase), b), j)
    let next_ptr ← pure np.1
    let phys ← pure np.2
    let q_val ← compReadPhysQuotGenProg ((cp, (metaBase, itemBase)), phys)
    let z0 ← pure 0
    let one ← pure 1
    if q_val = q_target then
      pure (((z0, one), j), phys)
    else
      pure (((next_ptr, z0), j_found), phys_found)

private theorem clientState_compMicroStepGenProg
    (x : CompMicroCtx × CompMicroAcc) (s : Memory.State) :
    (Memory.spec 0).clientState s (compMicroStepGenProg x) = s := by
  rcases x with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, z0⟩,
    ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compMicroStepGenProg]
  simp only [pure_bind, prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compMicroFetchProg, runClient_state_compReadPhysQuotGenProg]
  split_ifs <;> rfl

private theorem memoryCost_compMicroStepGenProg_pos
    (x : CompMicroCtx × CompMicroAcc) (s : Memory.State) :
    1 ≤ memoryCost (compMicroStepGenProg x) s := by
  rcases x with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, z0⟩,
    ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩⟩
  dsimp only [compMicroStepGenProg, compMicroFetchProg]
  simp only [pure_bind, Realization.memoryCost_bind', memoryCost_compReadLMNextGenProg]
  omega

private theorem memoryCost_compMicroStepGenProg_le
    (x : CompMicroCtx × CompMicroAcc) (s : Memory.State) :
    memoryCost (compMicroStepGenProg x) s ≤ 12 := by
  rcases x with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, z0⟩,
    ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩⟩
  dsimp only [compMicroStepGenProg]
  simp only [pure_bind, Realization.memoryCost_bind', runClient_state_compMicroFetchProg,
    runClient_state_compReadPhysQuotGenProg]
  have h1 : memoryCost (compMicroFetchProg (((cp, metaBase), b), ptr - 1)) s ≤ 6 := by
    dsimp only [compMicroFetchProg]
    simp only [Realization.memoryCost_bind', memoryCost_compReadLMNextGenProg,
      runClient_state_compReadLMNextGenProg, runClient_state_compResolveIndexedSlotGenProg,
      memoryCost_pure]
    have := memoryCost_compResolveIndexedSlotGenProg_le (((cp, metaBase), b), ptr - 1) s
    omega
  have h2 := memoryCost_compReadPhysQuotGenProg_le
    ((cp, (metaBase, itemBase)),
      ((Memory.spec 0).clientResult s (compMicroFetchProg (((cp, metaBase), b), ptr - 1))).2) s
  split_ifs <;> simp only [memoryCost_pure] <;> omega

/-- Precondition for `compMicroStepGenProg`. -/
private def CompMicroStepPre (w : ℕ) : CompMicroCtx × CompMicroAcc → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), (b, _q_target)), _z0),
     (((ptr, _found), _j_found), _phys_found)), s =>
    ∃ U V N m_items s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      0 < ptr ∧
      ptr - 1 < effBucketCap N ∧
      ptr - 1 < bCount N (compGmAt metaBase U w N s.mem) b

private theorem clientResult_compMicroStepGenProg_eq
    {metaBase itemBase U V w N m_items b q_target z0 : ℕ} {acc : CompMicroAcc}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N)
    (hstep : match acc with
      | (((ptr, _), _), _) =>
        0 < ptr ∧ ptr - 1 < effBucketCap N ∧ ptr - 1 < bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (compMicroStepGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), z0), acc)) =
      (Memory.spec 0).clientResult s_fix
        (microStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((((0, b), q_target), z0), acc)) := by
  rcases acc with ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩
  obtain ⟨_, hj_cap, hj_bc⟩ := hstep
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hj_bc_fix : ptr - 1 <
      bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
    rw [← hcpl.gm_eq]; exact hj_bc
  have hres_fix := clientResult_microStepProg
    (x := ((((0, b), q_target), z0), (((ptr, found), j_found), phys_found))) s_fix
    hslot_fix hb hj_bc_fix hj_cap
  dsimp only [compMicroStepGenProg]
  simp only [pure_bind]
  rw [prog_clientResult_bind, clientResult_compMicroFetchProg hslot hb hj_bc hj_cap,
    clientState_compMicroFetchProg]
  dsimp only
  rw [prog_clientResult_bind,
    clientResult_compReadPhysQuot_slotOf hcpl henv hslot hm_items hb hj_bc,
    clientState_compReadPhysQuotGenProg, hres_fix]
  dsimp only
  simp only [← hcpl.lm_eq, ← hcpl.gm_eq]
  split_ifs <;> rfl

private theorem realizesBounded_compMicroStepGen :
    RealizesBounded .exact compMicroStepGenProg
      (appendWords (WordEncoding.encode (α := CompMicroCtx))
        (WordEncoding.encode (α := CompMicroAcc)))
      (WordEncoding.encode (α := CompMicroAcc))
      CompMicroStepPre (fun _ _ => 0) := by
  have hmf := realizesBounded_compMicroFetch
  have hrq := realizesBounded_compReadPhysQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, z0⟩,
      ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩⟩
    obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items,
      hb, hptr_pos, hj_cap, hj_bc⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    try simp only [StateTransitionSpec.clientState, runClient_state_compMicroFetchProg] at *)
  · omega
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb, hj_bc, hj_cap⟩
  · rw [clientResult_compMicroFetchProg hslot hb hj_bc hj_cap]
    exact ⟨U, V, N, m_items, s_fix, b, ptr - 1, rfl, henv, hcpl, hslot, hm_items,
      hb, hj_bc, rfl⟩
  · exact fits_const_of_offCompItems hfit_meta (by decide)

private theorem validProg_compMicroStepGen
    {w : ℕ} {x : CompMicroCtx × CompMicroAcc} {s : Memory.State}
    (h : CompMicroStepPre w x s) : ValidProg w 0 s (compMicroStepGenProg x) := by
  rcases x with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, z0⟩,
    ⟨⟨⟨ptr, found⟩, j_found⟩, phys_found⟩⟩
  obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items,
    hb, _hptr_pos, hj_cap, hj_bc⟩ := h
  dsimp only [compMicroStepGenProg]; simp only [pure_bind]
  refine validProg_bind
    (validProg_compMicroFetch
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb, hj_bc, hj_cap⟩) ?_
  rw [clientState_compMicroFetchProg, clientResult_compMicroFetchProg hslot hb hj_bc hj_cap]
  dsimp only
  refine validProg_bind
    (validProg_compReadPhysQuotGen
      ⟨U, V, N, m_items, s_fix, b, ptr - 1, rfl, henv, hcpl, hslot, hm_items, hb, hj_bc, rfl⟩) ?_
  exact validProg_ite (fun _ => validProg_pure _) (fun _ => validProg_pure _)

/-- Native loop guard for `compMicroLoopGenProg`: tests `z0 < ptr` (`word 40 < word 41`). -/
private def compMicroLoopGuard (d : CompMicroCtx) (a : CompMicroAcc) : Prop :=
  test (Cond.lt (40 : Fin 45) (41 : Fin 45))
    ((appendWords (WordEncoding.encode (α := CompMicroCtx))
      (WordEncoding.encode (α := CompMicroAcc))) (d, a))

private instance (d : CompMicroCtx) (a : CompMicroAcc) : Decidable (compMicroLoopGuard d a) := by
  unfold compMicroLoopGuard; infer_instance

@[simp] private theorem compMicroLoopGuard_iff
    (cp : CompParams) (metaBase itemBase b q_target z0 ptr found j_found phys_found : ℕ) :
    compMicroLoopGuard (((cp, (metaBase, itemBase)), (b, q_target)), z0)
      (((ptr, found), j_found), phys_found) ↔ z0 < ptr := Iff.rfl

/-- Ghost step-count bound for `compMicroLoopGenProg`. -/
private def compMicroCutoff : CompMicroCtx × CompMicroAcc → ℕ
  | ((((cp, _), _), _), _) => effBucketCap (cpN cp)

/-- Phase 1 bounded while loop over a micro-bucket chain on compacted metadata. -/
private def compMicroLoopGenProg (x : CompMicroCtx × CompMicroAcc) : Memory.Prog CompMicroAcc :=
  boundedWhile compMicroLoopGuard compMicroStepGenProg x.1 (compMicroCutoff x) x.2

private theorem realizesBounded_compMicroLoopGen :
    RealizesBounded .exact compMicroLoopGenProg
      (appendWords (WordEncoding.encode (α := CompMicroCtx))
        (WordEncoding.encode (α := CompMicroAcc)))
      (WordEncoding.encode (α := CompMicroAcc))
      (fun w x s => whileSafe compMicroLoopGuard compMicroStepGenProg CompMicroStepPre w
        x.1 (compMicroCutoff x) x.2 s)
      (fun _ _ => 0) :=
  RealizesBounded.while₀
    (WordEncoding.encode (α := CompMicroCtx))
    (WordEncoding.encode (α := CompMicroAcc))
    (Cond.lt (40 : Fin 45) (41 : Fin 45))
    compMicroCutoff
    realizesBounded_compMicroStepGen
    memoryCost_compMicroStepGenProg_pos

private theorem boundedWhile_compMicroStep_spec
    {metaBase itemBase U V w N m_items b q_target prev_ptr : ℕ}
    {L : List ℕ} {k ptr found j_found phys_found : ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N)
    (hchain : IsDLChainAux N prev_ptr
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hk : L.length ≤ k)
    (hptr : ptr = (L.head?.map (· + 1)).getD 0) :
    let d : CompMicroCtx := (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), 0)
    let d_fix := (((0, b), q_target), 0)
    let a : CompMicroAcc := (((ptr, found), j_found), phys_found)
    let prog := boundedWhile compMicroLoopGuard compMicroStepGenProg d k a
    let prog_fix := boundedWhile microLoopGuard
      (microStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)) d_fix k a
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 12 * L.length ∧
    whileSafe compMicroLoopGuard compMicroStepGenProg CompMicroStepPre w d k a s := by
  induction L generalizing k prev_ptr ptr found j_found phys_found with
  | nil =>
    intro d d_fix a prog prog_fix
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at hptr
    subst hptr
    rcases k with _ | k' <;>
      refine ⟨by simp [prog, boundedWhile, d, a],
        by simp [prog, prog_fix, boundedWhile, d, d_fix, a],
        by simp [prog, boundedWhile, d, a],
        by simp [whileSafe, d, a]⟩
  | cons j rest ih =>
    intro d d_fix a prog prog_fix
    rcases k with _ | k'
    · simp at hk
    · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hptr
      subst hptr
      have hg : compMicroLoopGuard d a := by simp [d, a]
      have hg_fix : microLoopGuard d_fix a := by simp [d_fix, a]
      rcases hchain with ⟨hj_cap, _, _, hnj, hrest⟩
      have hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b := hc_lt j List.mem_cons_self
      have hrest_bc : ∀ x ∈ rest, x < bCount N (compGmAt metaBase U w N s.mem) b :=
        fun x hx => hc_lt x (List.mem_cons_of_mem j hx)
      have hpre : CompMicroStepPre w (d, a) s :=
        ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb,
          by omega, by simpa using hj_cap, by simpa using hj_bc⟩
      have hstep_eq : (Memory.spec 0).clientResult s (compMicroStepGenProg (d, a)) =
          (Memory.spec 0).clientResult s_fix
            (microStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (d_fix, a)) :=
        clientResult_compMicroStepGenProg_eq (q_target := q_target) (z0 := 0)
          (acc := a) henv hcpl hslot hm_items hb ⟨by omega, by simpa using hj_cap,
            by simpa using hj_bc⟩
      have hslot_fix : SlotStoreInv N
          (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
        rw [← hcpl.gm_eq]; exact hslot
      have hj_bc_fix : j <
          bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
        rw [← hcpl.gm_eq]; exact hj_bc
      have hstep_fix := clientResult_microStepProg (x := (d_fix, a)) s_fix hslot_fix hb
        (by simpa [a] using hj_bc_fix) (by simpa [a] using hj_cap)
      simp only [d_fix, a, microStepBase, microStepBucket, microStepQuot, microStepPtr,
        microStepMatchIdx, microStepPhys, Nat.add_sub_cancel] at hstep_fix
      have hstep_st := clientState_compMicroStepGenProg (d, a) s
      have hstep_st_fix := clientState_microStepProg U V (ghostW w) N
        (epochHashSpace U (ghostW w) N) (d_fix, a) s_fix
      have hstep_cost := memoryCost_compMicroStepGenProg_le (d, a) s
      unfold prog prog_fix boundedWhile
      rw [ite_eq_left hg, ite_eq_left hg_fix,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind,
        memoryCost_bind_of_clientState_eq hstep_st]
      simp only [whileSafe, hg, ↓reduceIte]
      rw [hstep_st, hstep_st_fix, hstep_eq, hstep_fix]
      by_cases hmatch :
          quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
            (slotOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b j) =
          q_target
      · set a' : CompMicroAcc :=
          (((0, 1), j),
           slotOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b j)
        have hbw0 : boundedWhile compMicroLoopGuard compMicroStepGenProg d k' a' = pure a' := by
          rcases k' with _ | k'' <;> simp [boundedWhile, d, a']
        have hbw0_fix : boundedWhile microLoopGuard
            (microStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)) d_fix k' a' =
            pure a' := by
          rcases k' with _ | k'' <;> simp [boundedWhile, d_fix, a']
        have hws0 : whileSafe compMicroLoopGuard compMicroStepGenProg CompMicroStepPre w
            d k' a' s := by
          rcases k' with _ | k'' <;> simp [whileSafe, d, a']
        rw [ite_eq_left hmatch, hbw0, hbw0_fix]
        refine ⟨rfl, rfl, ?_, ⟨hpre, hws0⟩⟩
        simp only [memoryCost_pure, List.length_cons]
        omega
      · have hk' : rest.length ≤ k' := by simp only [List.length_cons] at hk; omega
        have hnj_fix : lmNext N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
            b j = (rest.head?.map (· + 1)).getD 0 := by rw [← hcpl.lm_eq]; exact hnj
        obtain ⟨hih_st, hih_res, hih_cost, hih_safe⟩ :=
          ih hrest hrest_bc hk' hnj_fix (found := 0) (j_found := j_found) (phys_found := phys_found)
        rw [ite_eq_right hmatch]
        refine ⟨hih_st, hih_res, ?_, ⟨hpre, hih_safe⟩⟩
        simp only [List.length_cons]
        dsimp only [d] at hstep_cost hih_cost ⊢
        omega

/-- Phase 1 micro-chain search on compacted metadata:
`d = ((((cp, (metaBase, itemBase)), (b, q_target)), m))`, returning `(((0, found), j_found), phys)`.
-/
private def compSearchMicroChainGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog CompMicroAcc
  | (((cp, (metaBase, itemBase)), (b, q_target)), m) => do
    let h0 ← compReadLMHeadGenProg ((cp, metaBase), (b, m))
    let z0 ← pure 0
    compMicroLoopGenProg
      ((((cp, (metaBase, itemBase)), (b, q_target)), z0), (((h0, z0), z0), z0))

/-- Precondition for `compSearchBucketGenProg`. -/
@[expose] def CompSearchBucketPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), (b, _q_target)), m), s =>
    ∃ U V N m_items s_fix L,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
        (lmPrev N (compLmAt metaBase U w N s.mem) b)
        (lmNext N (compLmAt metaBase U w N s.mem) b) L ∧
      (∀ j ∈ L, j < bCount N (compGmAt metaBase U w N s.mem) b)

private theorem compSearchMicroChainGenProg_spec
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
    let prog := compSearchMicroChainGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))
    let prog_fix := searchMicroChainProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), m)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 2 + 12 * L.length ∧
    whileSafe compMicroLoopGuard compMicroStepGenProg CompMicroStepPre w
      (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), 0)
      (effBucketCap N)
      (((lmHead N (compLmAt metaBase U w N s.mem) b m, 0), 0), 0) s := by
  intro prog prog_fix
  have hlen := hchain.length_le
  obtain ⟨hh_eq, hchain_aux⟩ := hchain
  obtain ⟨hst, hres, hcost, hsafe⟩ := boundedWhile_compMicroStep_spec
    (q_target := q_target) (found := 0) (j_found := 0) (phys_found := 0)
    henv hcpl hslot hm_items hb hchain_aux hc_lt hlen hh_eq
  have hh_fix : lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b m =
      lmHead N (compLmAt metaBase U w N s.mem) b m := by rw [hcpl.lm_eq]
  dsimp only [prog, prog_fix, compSearchMicroChainGenProg, compMicroLoopGenProg, compMicroCutoff,
    cpN_mk]
  unfold searchMicroChainProg searchMicroChainGenProg microLoopGenProg
  simp only [lmWriteLoc, lmWriteVal, lmWriteHeadArg, microLoopCtxParams, readLMHeadGenProg_mk,
    p_nMax_mk, pure_bind, boundedWhile_microStepGenProg_mk]
  rw [StateTransitionSpec.clientState_bind, clientState_compReadLMHeadGenProg,
    clientResult_compReadLMHeadGenProg hb hm s,
    StateTransitionSpec.clientResult_bind, clientState_compReadLMHeadGenProg,
    clientResult_compReadLMHeadGenProg hb hm s,
    StateTransitionSpec.clientResult_bind, clientState_readLMHeadProg,
    clientResult_readLMHeadProg s_fix hb hm, hh_fix,
    Realization.memoryCost_bind', memoryCost_compReadLMHeadGenProg,
    clientState_compReadLMHeadGenProg, clientResult_compReadLMHeadGenProg hb hm s]
  exact ⟨hst, hres, by omega, hsafe⟩

private theorem realizesBounded_compSearchMicroChainGen :
    RealizesBounded .exact compSearchMicroChainGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := CompMicroAcc))
      CompSearchBucketPre (fun _ _ => 0) := by
  have hrh := realizesBounded_compReadLMHeadGen
  have hloop := realizesBounded_compMicroLoopGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
    obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
      hb, hm, hchain, hc_lt⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_compReadLMHeadGenProg] at *
    try rw [clientResult_compReadLMHeadGenProg hb hm s] at *)
  · exact ⟨henv.compMetaEnv, hb, hm⟩
  · simpa only [compMicroCutoff, cpN_mk] using
      (compSearchMicroChainGenProg_spec (q_target := q_target)
        henv hcpl hslot hm_items hb hm hchain hc_lt).2.2.2

private theorem validProg_compSearchMicroChainGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : CompSearchBucketPre w d s) : ValidProg w 0 s (compSearchMicroChainGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm, hchain, hc_lt⟩ := h
  have hsafe :=
    (compSearchMicroChainGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb hm hchain hc_lt).2.2.2
  dsimp only [compSearchMicroChainGenProg, compMicroLoopGenProg, compMicroCutoff, cpN_mk]
  simp only [pure_bind]
  refine validProg_bind (validProg_compReadLMHeadGen ⟨henv.compMetaEnv, hb, hm⟩) ?_
  rw [clientState_compReadLMHeadGenProg, clientResult_compReadLMHeadGenProg hb hm s]
  exact validProg_boundedWhile (effBucketCap N) _ s
    (fun _ _ hpre => validProg_compMicroStepGen hpre) hsafe

/-! ## Section 3: Phase 2 Overflow Search (`compSearchOverflowGenProg`) -/

/-- Context type `((cp, (metaBase, itemBase)), (b, q_target))` for `compOvfLoopGenProg`. -/
private abbrev CompOvfCtx : Type := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)

/-- Accumulator type `((((j, p_cur), found), j_found), phys_found)` for `compOvfLoopGenProg`. -/
private abbrev CompOvfAcc : Type := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ

/-- Single step of Phase 2 overflow search on compacted metadata (`¬ReadsWidth`). -/
private def compOvfStepGenProg : CompOvfCtx × CompOvfAcc → Memory.Prog CompOvfAcc
  | (((cp, (metaBase, itemBase)), (b, q_target)),
     ((((j, p_cur), found), j_found), phys_found)) => do
    let pair ← compResolveOvfStepGenProg (((cp, metaBase), b), (j, p_cur))
    let phys ← pure pair.1
    let p_next ← pure pair.2
    let q_val ← compReadPhysQuotGenProg ((cp, (metaBase, itemBase)), phys)
    let j1 ← pure (j + 1)
    let z0 ← pure 0
    if found = z0 then
      if q_val = q_target then do
        let z1 ← pure 1
        pure ((((j1, p_next), z1), j), phys)
      else
        pure ((((j1, p_next), z0), j_found), phys_found)
    else
      pure ((((j1, p_next), found), j_found), phys_found)

private theorem clientState_compOvfStepGenProg (x : CompOvfCtx × CompOvfAcc) (s : Memory.State) :
    (Memory.spec 0).clientState s (compOvfStepGenProg x) = s := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩,
    ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compOvfStepGenProg]
  simp only [pure_bind, prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_compResolveOvfStepGenProg, runClient_state_compReadPhysQuotGenProg]
  split_ifs <;> rfl

private theorem memoryCost_compOvfStepGenProg_pos (x : CompOvfCtx × CompOvfAcc) (s : Memory.State) :
    1 ≤ memoryCost (compOvfStepGenProg x) s := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩,
    ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩⟩
  dsimp only [compOvfStepGenProg]
  simp only [pure_bind, Realization.memoryCost_bind']
  have := memoryCost_compResolveOvfStepGenProg_pos (((cp, metaBase), b), (j, p_cur)) s
  omega

private theorem memoryCost_compOvfStepGenProg_le (x : CompOvfCtx × CompOvfAcc) (s : Memory.State) :
    memoryCost (compOvfStepGenProg x) s ≤ 10 := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩,
    ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩⟩
  dsimp only [compOvfStepGenProg]
  simp only [pure_bind, Realization.memoryCost_bind',
    runClient_state_compResolveOvfStepGenProg, runClient_state_compReadPhysQuotGenProg]
  have h1 := memoryCost_compResolveOvfStepGenProg_le (((cp, metaBase), b), (j, p_cur)) s
  have h2 := memoryCost_compReadPhysQuotGenProg_le
    ((cp, (metaBase, itemBase)),
      ((Memory.spec 0).clientResult s
        (compResolveOvfStepGenProg (((cp, metaBase), b), (j, p_cur)))).1) s
  split_ifs <;> simp only [memoryCost_pure] <;> omega

/-- Precondition for `compOvfStepGenProg`. -/
private def CompOvfStepPre (w : ℕ) : CompOvfCtx × CompOvfAcc → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), (b, _q_target)),
     ((((j, p_cur), _found), _j_found), _phys_found)), s =>
    ∃ U V N m_items s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      (j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
        p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N))

private theorem clientResult_compOvfStepGenProg_eq
    {metaBase itemBase U V w N m_items b q_target : ℕ} {acc : CompOvfAcc}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hstep : match acc with
      | ((((j, p_cur), _), _), _) =>
        j < bCount N (compGmAt metaBase U w N s.mem) b ∧
        (j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
          p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N))) :
    (Memory.spec 0).clientResult s
        (compOvfStepGenProg (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), acc)) =
      (Memory.spec 0).clientResult s_fix
        (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q_target), acc)) ∧
    (match acc with
      | ((((j, _), _), _), _) =>
        let res := (Memory.spec 0).clientResult s
          (compOvfStepGenProg (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), acc))
        match res with
        | ((((j_next, p_next), _), _), _) =>
          j_next = j + 1 ∧
          (j + 1 < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
            p_next = slabPtrOf N (compGmAt metaBase U w N s.mem) b ((j + 1) / slabSize N))) := by
  rcases acc with ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩
  obtain ⟨hj_bc, hp⟩ := hstep
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hj_bc_fix : j <
      bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
    rw [← hcpl.gm_eq]; exact hj_bc
  have hp_fix : j < gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (gmQIdx b) *
      slabSize N →
      p_cur = slabPtrOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
        (j / slabSize N) := by
    rw [← hcpl.gm_eq]; exact hp
  have hres_ovf_eq := clientResult_compResolveOvfStepGenProg_eq hcpl.gm_eq hb_pos hb hj_bc hslot hp
  obtain ⟨hphys_eq, hp_next⟩ := clientResult_resolveOvfStepProg
    (U := U) (V := V) (w := ghostW w) (n_max := N) (h_space := epochHashSpace U (ghostW w) N)
    (d := ((0, b), (j, p_cur))) s_fix hb_pos hb hj_bc_fix hslot_fix hp_fix
  dsimp only [ovfBucketBase, ovfBucketIdx, ovfResolveIdx] at hphys_eq hp_next
  have hphys_comp :
      ((Memory.spec 0).clientResult s
        (compResolveOvfStepGenProg (((mkCompParams U V w N, metaBase), b), (j, p_cur)))).1 =
      slotOf N (compGmAt metaBase U w N s.mem) b j := by
    rw [hres_ovf_eq, hphys_eq, hcpl.gm_eq]
  obtain ⟨hovf_fix, _⟩ := clientResult_ovfStepProg
    (x := (((0, b), q_target), ((((j, p_cur), found), j_found), phys_found))) s_fix
    hb_pos hb hj_bc_fix hslot_fix hp_fix
  dsimp only [ovfQueryLoc, ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfAccCursor,
    ovfAccSlotIdx, ovfAccFound, ovfAccMatchIdx, ovfAccPhys] at hovf_fix
  have hcomp_res :
      (Memory.spec 0).clientResult s
        (compOvfStepGenProg (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)),
          ((((j, p_cur), found), j_found), phys_found))) =
      (Memory.spec 0).clientResult s_fix
        (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_target), ((((j, p_cur), found), j_found), phys_found))) := by
    dsimp only [compOvfStepGenProg]
    simp only [pure_bind]
    rw [prog_clientResult_bind, clientState_compResolveOvfStepGenProg, hphys_comp,
      prog_clientResult_bind,
      clientResult_compReadPhysQuot_slotOf hcpl henv hslot hm_items hb hj_bc,
      clientState_compReadPhysQuotGenProg, hovf_fix, hres_ovf_eq]
    simp only [← hcpl.gm_eq]
    split_ifs <;> rfl
  refine ⟨hcomp_res, ?_⟩
  rw [hcomp_res, hovf_fix]
  dsimp only
  simp only [← hcpl.gm_eq] at hp_next
  split_ifs <;> exact ⟨rfl, hp_next⟩

private theorem realizesBounded_compOvfStepGen :
    RealizesBounded .exact compOvfStepGenProg
      (((WordEncoding.encode (α := CompOvfCtx)).prodMap
        (WordEncoding.encode (α := CompOvfAcc))).trans (Fin.appendEquiv _ _).toEmbedding)
      (WordEncoding.encode (α := CompOvfAcc))
      CompOvfStepPre (fun _ _ => 0) := by
  have hrs := realizesBounded_compResolveOvfStepGen
  have hrq := realizesBounded_compReadPhysQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩,
      ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩⟩
    obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items,
      hb_pos, hb, hj_bc, hp⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    have hslot_fix : SlotStoreInv N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
      rw [← hcpl.gm_eq]; exact hslot
    have hj_bc_fix : j <
        bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
      rw [← hcpl.gm_eq]; exact hj_bc
    have hp_fix : j < gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (gmQIdx b) *
        slabSize N →
        p_cur = slabPtrOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
          (j / slabSize N) := by
      rw [← hcpl.gm_eq]; exact hp
    have hphys_comp :
        ((Memory.spec 0).clientResult s
          (compResolveOvfStepGenProg (((mkCompParams U V w N, metaBase), b), (j, p_cur)))).1 =
        slotOf N (compGmAt metaBase U w N s.mem) b j := by
      rw [clientResult_compResolveOvfStepGenProg_eq hcpl.gm_eq hb_pos hb hj_bc hslot hp,
        (clientResult_resolveOvfStepProg (U := U) (V := V) (w := ghostW w) (n_max := N)
          (h_space := epochHashSpace U (ghostW w) N) (d := ((0, b), (j, p_cur))) s_fix
          hb_pos hb hj_bc_fix hslot_fix hp_fix).1,
        hcpl.gm_eq]
    simp only [StateTransitionSpec.clientState,
      runClient_state_compResolveOvfStepGenProg, hphys_comp] at *)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb_pos, hb, hj_bc, hslot, hp⟩
  · exact ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items, hb, hj_bc, rfl⟩
  · have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    have hNU := henv.le_U
    exact lt_of_le_of_lt (by omega) henv.lt_pow_U
  · exact fits_const_of_offCompItems hfit_meta (by decide)

private theorem validProg_compOvfStepGen {w : ℕ} {x : CompOvfCtx × CompOvfAcc} {s : Memory.State}
    (h : CompOvfStepPre w x s) : ValidProg w 0 s (compOvfStepGenProg x) := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩,
    ⟨⟨⟨⟨j, p_cur⟩, found⟩, j_found⟩, phys_found⟩⟩
  obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items,
    hb_pos, hb, hj_bc, hp⟩ := h
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hj_bc_fix : j <
      bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
    rw [← hcpl.gm_eq]; exact hj_bc
  have hp_fix : j < gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (gmQIdx b) *
      slabSize N →
      p_cur = slabPtrOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
        (j / slabSize N) := by
    rw [← hcpl.gm_eq]; exact hp
  have hphys_comp :
      ((Memory.spec 0).clientResult s
        (compResolveOvfStepGenProg (((mkCompParams U V w N, metaBase), b), (j, p_cur)))).1 =
      slotOf N (compGmAt metaBase U w N s.mem) b j := by
    rw [clientResult_compResolveOvfStepGenProg_eq hcpl.gm_eq hb_pos hb hj_bc hslot hp,
      (clientResult_resolveOvfStepProg (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) (d := ((0, b), (j, p_cur))) s_fix
        hb_pos hb hj_bc_fix hslot_fix hp_fix).1,
      hcpl.gm_eq]
  dsimp only [compOvfStepGenProg]; simp only [pure_bind]
  refine validProg_bind
    (validProg_compResolveOvfStepGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hb_pos, hb, hj_bc, hslot, hp⟩) ?_
  rw [clientState_compResolveOvfStepGenProg, hphys_comp]
  refine validProg_bind
    (validProg_compReadPhysQuotGen
      ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items, hb, hj_bc, rfl⟩) ?_
  exact validProg_ite
    (fun _ => validProg_ite (fun _ => validProg_pure _) (fun _ => validProg_pure _))
    (fun _ => validProg_pure _)

/-- Wrapper for `iterate compOvfStepGenProg` matching `RealizesBounded.iterate₀`. -/
private def compOvfLoopGenProg (x : (CompOvfCtx × CompOvfAcc) × ℕ) : Memory.Prog CompOvfAcc :=
  iterate compOvfStepGenProg x.1.1 x.2 x.1.2

private theorem realizesBounded_compOvfLoopGen :
    RealizesBounded .exact compOvfLoopGenProg
      (WordEncoding.encode (α := (CompOvfCtx × CompOvfAcc) × ℕ))
      (WordEncoding.encode (α := CompOvfAcc))
      (fun w x s =>
        iterationSafe compOvfStepGenProg CompOvfStepPre w x.1.1 x.2 x.1.2 s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := CompOvfCtx))
    (WordEncoding.encode (α := CompOvfAcc))
    realizesBounded_compOvfStepGen
    memoryCost_compOvfStepGenProg_pos

private def compOvfRunLoopProg : CompOvfCtx × (ℕ × ℕ) → Memory.Prog CompOvfAcc
  | (((cp, (metaBase, itemBase)), (b, q_target)), (p_init, fuel)) => do
    let z0 ← pure 0
    compOvfLoopGenProg
      ((((cp, (metaBase, itemBase)), (b, q_target)),
        ((((cpMinCap cp, p_init), z0), z0), z0)), fuel)

private theorem realizesBounded_compOvfRunLoop :
    RealizesBounded .exact compOvfRunLoopProg
      (WordEncoding.encode (α := CompOvfCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := CompOvfAcc))
      (fun w x s =>
        iterationSafe compOvfStepGenProg CompOvfStepPre w x.1
          x.2.2 ((((cpMinCap x.1.1.1, x.2.1), 0), 0), 0) s)
      (fun _ _ => 0) := by
  have hloop := realizesBounded_compOvfLoopGen
  realize
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, ⟨p_init, fuel⟩⟩
  exact h

private theorem iterate_compOvfStepGenProg_spec
    {metaBase itemBase U V w N m_items b q_target : ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) :
    ∀ fuel j p_cur found j_found phys_found,
      j + fuel ≤ bCount N (compGmAt metaBase U w N s.mem) b →
      (j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
        p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N)) →
      let ctx : CompOvfCtx := ((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target))
      let acc : CompOvfAcc := ((((j, p_cur), found), j_found), phys_found)
      let prog := iterate compOvfStepGenProg ctx fuel acc
      let prog_fix := iterate (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
        ((0, b), q_target) fuel acc
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
      memoryCost prog s ≤ 10 * fuel ∧
      iterationSafe compOvfStepGenProg CompOvfStepPre w ctx fuel acc s := by
  intro fuel
  induction fuel with
  | zero =>
    intro j p_cur found j_found phys_found _ _ ctx acc prog prog_fix
    exact ⟨rfl, rfl, by simp [prog, iterate], trivial⟩
  | succ fuel ih =>
    intro j p_cur found j_found phys_found hjf hp ctx acc prog prog_fix
    have hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hpre : CompOvfStepPre w (ctx, acc) s :=
      ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb_pos, hb, hj_bc, hp⟩
    obtain ⟨hstep_eq, hstep_inv⟩ := clientResult_compOvfStepGenProg_eq
      (q_target := q_target) (acc := acc) henv hcpl hslot hm_items hb_pos hb ⟨hj_bc, hp⟩
    have hstep_st := clientState_compOvfStepGenProg (ctx, acc) s
    have hstep_st_fix := clientState_ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), acc) s_fix
    have hstep_cost := memoryCost_compOvfStepGenProg_le (ctx, acc) s
    set acc1 := (Memory.spec 0).clientResult s (compOvfStepGenProg (ctx, acc))
    rcases h1 : acc1 with ⟨⟨⟨⟨j_next, p_next⟩, found1⟩, j_found1⟩, phys_found1⟩
    dsimp only at hstep_inv
    rw [h1] at hstep_inv
    obtain ⟨rfl, hp_next⟩ := hstep_inv
    obtain ⟨hih_st, hih_res, hih_cost, hih_safe⟩ :=
      ih (j + 1) p_next found1 j_found1 phys_found1 (by omega) hp_next
    dsimp only [prog, prog_fix]
    unfold iterate
    rw [iterationSafe, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq hstep_st, hstep_st, hstep_st_fix, ← hstep_eq]
    change (Memory.spec 0).clientState s (iterate compOvfStepGenProg ctx fuel acc1) = s ∧
      (Memory.spec 0).clientResult s (iterate compOvfStepGenProg ctx fuel acc1) =
        (Memory.spec 0).clientResult s_fix
          (iterate (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
            ((0, b), q_target) fuel acc1) ∧
      memoryCost (compOvfStepGenProg (ctx, acc)) s +
        memoryCost (iterate compOvfStepGenProg ctx fuel acc1) s ≤ 10 * (fuel + 1) ∧
      CompOvfStepPre w (ctx, acc) s ∧
      iterationSafe compOvfStepGenProg CompOvfStepPre w ctx fuel acc1 s
    rw [h1]
    dsimp only [ctx, acc] at hstep_cost hih_st hih_res hih_cost hih_safe ⊢
    exact ⟨hih_st, hih_res, by omega, ⟨hpre, hih_safe⟩⟩

private def compExtractOvfResultProg : CompOvfAcc → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((_, found), j_found), phys_found) => pure ((found, j_found), phys_found)

private theorem realizesBounded_compExtractOvfResult :
    RealizesBounded .exact compExtractOvfResultProg
      (WordEncoding.encode (α := CompOvfAcc))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def compSearchOverflowMultiGenProg : CompOvfCtx → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((cp, (metaBase, itemBase)), (b, q_target)) => do
    let init ← compInitOvfSearchGenProg ((cp, metaBase), b)
    let res ← compOvfRunLoopProg (((cp, (metaBase, itemBase)), (b, q_target)), init)
    compExtractOvfResultProg res

/-- Phase 2 overflow search on compacted metadata (`¬ReadsWidth`): scans overflow slots
`j ∈ [effBucketCap N, bCount N gm b)` in bucket `b` for `q_target`, returning
`((found, j_found), phys_found)`. -/
private def compSearchOverflowGenProg : CompOvfCtx → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((cp, (metaBase, itemBase)), (b, q_target)) => do
    let z0 ← pure 0
    if cpBucketBits cp = z0 then
      pure ((z0, z0), z0)
    else
      compSearchOverflowMultiGenProg (((cp, (metaBase, itemBase)), (b, q_target)))

/-- Precondition for `compSearchOverflowGenProg`. -/
private def CompSearchOverflowPre (w : ℕ) : CompOvfCtx → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), (b, _q_target)), s =>
    ∃ U V N m_items s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N

private theorem compSearchOverflowGenProg_spec
    {metaBase itemBase U V w N m_items b q_target : ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) :
    let gm := compGmAt metaBase U w N s.mem
    let prog := compSearchOverflowGenProg
      (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)))
    let prog_fix := searchOverflowProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      ((0, b), q_target)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 8 + 10 * (bCount N gm b - effBucketCap N) ∧
    (0 < bucketBits N →
      let init := (Memory.spec 0).clientResult s
        (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b))
      iterationSafe compOvfStepGenProg CompOvfStepPre w
        (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)))
        init.2 ((((min N (effBucketCap N), init.1), 0), 0), 0) s) := by
  intro gm prog prog_fix
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · simp only [prog, prog_fix, compSearchOverflowGenProg, cpBucketBits_mk, searchOverflowProg,
      searchOverflowGenProg, p_bucketBits_mk, hb0, ↓reduceIte, pure_bind]
    exact ⟨rfl, rfl, by simp, fun h => by omega⟩
  · have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hslot_fix : SlotStoreInv N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
      rw [← hcpl.gm_eq]; exact hslot
    have hinit_eq := clientResult_compInitOvfSearchGenProg_eq hcpl.gm_eq hb_pos hb hslot
    have hinit_fix := clientResult_initOvfSearchProg
      (U := U) (V := V) (w := ghostW w) (n_max := N) (h_space := epochHashSpace U (ghostW w) N)
      (d := (0, b)) s_fix hb_pos hb hslot_fix
    dsimp only at hinit_fix
    simp only [← hcpl.gm_eq] at hinit_fix
    rw [← hinit_eq] at hinit_fix
    have hcost_init := memoryCost_compInitOvfSearchGenProg_le
      ((mkCompParams U V w N, metaBase), b) s
    set init := (Memory.spec 0).clientResult s
      (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b))
    have hbc_le : bCount N gm b ≤ N := bCount_le_n_max hslot b
    have hprog_st : (Memory.spec 0).clientState s prog =
        (Memory.spec 0).clientState s
          (do
            let res ← iterate compOvfStepGenProg
              ((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target))
              init.2 ((((min N (effBucketCap N), init.1), 0), 0), 0)
            compExtractOvfResultProg res) := by
      dsimp only [prog, compSearchOverflowGenProg, compSearchOverflowMultiGenProg,
        compOvfRunLoopProg, compOvfLoopGenProg, cpBucketBits_mk, cpMinCap_mk]
      simp only [pure_bind, hb_ne, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, clientState_compInitOvfSearchGenProg]
    have hprog_res : (Memory.spec 0).clientResult s prog =
        (Memory.spec 0).clientResult s
          (do
            let res ← iterate compOvfStepGenProg
              ((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target))
              init.2 ((((min N (effBucketCap N), init.1), 0), 0), 0)
            compExtractOvfResultProg res) := by
      dsimp only [prog, compSearchOverflowGenProg, compSearchOverflowMultiGenProg,
        compOvfRunLoopProg, compOvfLoopGenProg, cpBucketBits_mk, cpMinCap_mk]
      simp only [pure_bind, hb_ne, ↓reduceIte]
      rw [StateTransitionSpec.clientResult_bind, clientState_compInitOvfSearchGenProg]
    have hprog_fix_res : (Memory.spec 0).clientResult s_fix prog_fix =
        (Memory.spec 0).clientResult s_fix
          (do
            let res ← iterate (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
              ((0, b), q_target) init.2 ((((min N (effBucketCap N), init.1), 0), 0), 0)
            pure ((res.1.1.2, res.1.2), res.2)) := by
      simp only [prog_fix, searchOverflowProg, searchOverflowGenProg, p_bucketBits_mk,
        hb_ne, ↓reduceIte, ovfSearchBucketLoc, p_minCap_mk, initOvfSearchGenProg_mk,
        ovfLoopGenProg_mk, ovfLoopProg, pure_bind]
      rw [StateTransitionSpec.clientResult_bind, clientState_initOvfSearchProg, ← hinit_eq]
    have hprog_cost : memoryCost prog s =
        memoryCost (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b)) s +
        memoryCost
          (do
            let res ← iterate compOvfStepGenProg
              ((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target))
              init.2 ((((min N (effBucketCap N), init.1), 0), 0), 0)
            compExtractOvfResultProg res) s := by
      dsimp only [prog, compSearchOverflowGenProg, compSearchOverflowMultiGenProg,
        compOvfRunLoopProg, compOvfLoopGenProg, cpBucketBits_mk, cpMinCap_mk]
      simp only [pure_bind, hb_ne, ↓reduceIte]
      exact memoryCost_bind_of_clientState_eq (clientState_compInitOvfSearchGenProg _ s) _
    rw [hprog_st, hprog_res, hprog_fix_res, hprog_cost]
    dsimp only [gm] at hbc_le ⊢
    by_cases hovf : effBucketCap N < bCount N (compGmAt metaBase U w N s.mem) b
    · have hmin_eq : min N (effBucketCap N) = effBucketCap N := by omega
      have hjf : effBucketCap N + init.2 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by
        rw [hinit_fix.1]; omega
      obtain ⟨hl_st, hl_res, hl_cost, hl_safe⟩ := iterate_compOvfStepGenProg_spec
        (q_target := q_target) henv hcpl hslot hm_items hb_pos hb
        init.2 (effBucketCap N) init.1 0 0 0 hjf (hinit_fix.2 hovf)
      rw [hmin_eq, StateTransitionSpec.clientState_bind, hl_st,
        StateTransitionSpec.clientResult_bind, hl_st,
        StateTransitionSpec.clientResult_bind,
        clientState_iterate_eq_of_step _ _ _ _ _ (fun x t => clientState_ovfStepProg _ _ _ _ _ x t),
        memoryCost_bind_of_clientState_eq hl_st, hl_res]
      rcases (Memory.spec 0).clientResult s_fix
          (iterate (ovfStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
            ((0, b), q_target) init.2 ((((effBucketCap N, init.1), 0), 0), 0)) with
        ⟨⟨⟨⟨_, _⟩, found⟩, j_found⟩, phys_found⟩
      dsimp only [compExtractOvfResultProg]
      rw [StateTransitionSpec.clientState_pure, StateTransitionSpec.clientResult_pure,
        StateTransitionSpec.clientResult_pure, memoryCost_pure, ← hinit_fix.1]
      exact ⟨rfl, rfl, by omega, fun _ => hl_safe⟩
    · have hfuel0 : init.2 = 0 := by rw [hinit_fix.1]; omega
      rw [hfuel0]
      dsimp only [iterate, compExtractOvfResultProg]
      rw [pure_bind, StateTransitionSpec.clientState_pure,
        StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientResult_pure,
        memoryCost_pure]
      exact ⟨rfl, rfl, by omega, fun _ => trivial⟩
where
  clientState_iterate_eq_of_step {δ σ : Type} (body : δ × σ → Memory.Prog σ)
      (ctx : δ) (fuel : ℕ) (acc : σ) (st : Memory.State)
      (hbody : ∀ x t, (Memory.spec 0).clientState t (body x) = t) :
      (Memory.spec 0).clientState st (iterate body ctx fuel acc) = st := by
    induction fuel generalizing acc with
    | zero => rfl
    | succ fuel ih =>
      unfold iterate
      rw [StateTransitionSpec.clientState_bind, hbody, ih]

private def CompSearchOverflowMultiPre (w : ℕ) : CompOvfCtx → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), (b, q_target)), s =>
    0 < cpBucketBits cp ∧
    CompSearchOverflowPre w (((cp, (metaBase, itemBase)), (b, q_target))) s

private theorem realizesBounded_compSearchOverflowMultiGen :
    RealizesBounded .exact compSearchOverflowMultiGenProg
      (WordEncoding.encode (α := CompOvfCtx))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompSearchOverflowMultiPre (fun _ _ => 0) := by
  have hinit := realizesBounded_compInitOvfSearchGen
  have hrun := realizesBounded_compOvfRunLoop
  have hext := realizesBounded_compExtractOvfResult
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩
    obtain ⟨hb_pos, U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩ := h
    rw [cpBucketBits_mk] at hb_pos)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb_pos, hb, hslot⟩
  · rw [clientState_compInitOvfSearchGenProg]
    dsimp only [cpMinCap_mk]
    exact (compSearchOverflowGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb).2.2.2 hb_pos

private theorem realizesBounded_compSearchOverflowGen :
    RealizesBounded .exact compSearchOverflowGenProg
      (WordEncoding.encode (α := CompOvfCtx))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompSearchOverflowPre (fun _ _ => 0) := by
  have hmul := realizesBounded_compSearchOverflowMultiGen
  realize
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩
  obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩ := h
  simp only [cpBucketBits_mk] at *
  · exact ⟨Nat.pos_of_ne_zero hc, U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩

private theorem validProg_compSearchOverflowGen {w : ℕ} {d : CompOvfCtx} {s : Memory.State}
    (h : CompSearchOverflowPre w d s) : ValidProg w 0 s (compSearchOverflowGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩
  obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩ := h
  have hspec := compSearchOverflowGenProg_spec (q_target := q_target) henv hcpl hslot hm_items hb
  dsimp only [compSearchOverflowGenProg, compSearchOverflowMultiGenProg,
    compOvfRunLoopProg, compOvfLoopGenProg, cpBucketBits_mk, cpMinCap_mk]
  simp only [pure_bind]
  refine validProg_ite (fun _ => validProg_pure _) (fun hb0 => ?_)
  have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
  refine validProg_bind
    (validProg_compInitOvfSearchGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hb_pos, hb, hslot⟩) ?_
  rw [clientState_compInitOvfSearchGenProg]
  refine validProg_bind
    (validProg_iterate _ _ s
      (fun _ _ hpre => validProg_compOvfStepGen hpre)
      (hspec.2.2.2 hb_pos)) ?_
  rcases ((Memory.spec 0).clientResult s
      (iterate compOvfStepGenProg
        ((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target))
        ((Memory.spec 0).clientResult s
          (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b))).2
        ((((min N (effBucketCap N),
          ((Memory.spec 0).clientResult s
            (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b))).1), 0), 0), 0)))
    with ⟨⟨⟨_, found⟩, j_found⟩, phys_found⟩
  exact validProg_pure _

/-! ## Section 4: Combined Bucket Search (`compSearchBucketGenProg`) and Lookup
(`compQueryBodyGenProg`) -/

private def compUnpackMicroResProg : CompMicroAcc → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((_, found), j_found), phys_found) => pure ((found, j_found), phys_found)

private theorem realizesBounded_compUnpackMicroRes :
    RealizesBounded .exact compUnpackMicroResProg
      (WordEncoding.encode (α := CompMicroAcc))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Combined two-phase bucket search on compacted metadata (`¬ReadsWidth`):
searches micro-chain `(b, m)` via `compSearchMicroChainGenProg`, and on miss searches overflow
slots via `compSearchOverflowGenProg`. Returns `((found, j_found), phys_found)`. -/
def compSearchBucketGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((cp, (metaBase, itemBase)), (b, q_target)), m) => do
    let res_raw ← compSearchMicroChainGenProg
      ((((cp, (metaBase, itemBase)), (b, q_target)), m))
    let res1 ← compUnpackMicroResProg res_raw
    let pair1 ← pure res1.1
    let found1 ← pure pair1.1
    let z1 ← pure 1
    if found1 = z1 then
      pure res1
    else
      compSearchOverflowGenProg (((cp, (metaBase, itemBase)), (b, q_target)))

private theorem fixedCoupled_bucketSearch_inv
    {metaBase itemBase U V w N b m : ℕ} {L : List ℕ} {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < bCount N (compGmAt metaBase U w N s.mem) b) :
    SlotStoreInv N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) ∧
    IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b) L ∧
    (∀ j ∈ L, j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b) := by
  refine ⟨?_, ?_, ?_⟩
  · change SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    rw [← hcpl.gm_eq]; exact hslot
  · change IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b) L
    rw [← hcpl.lm_eq]; exact hchain
  · change ∀ j ∈ L,
      j < bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
    rw [← hcpl.gm_eq]; exact hc_lt

theorem compSearchBucketGenProg_spec
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
    let prog := compSearchBucketGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))
    let prog_fix := searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), m)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 10 + 12 * L.length + 10 * (bCount N gm b - effBucketCap N) := by
  intro gm prog prog_fix
  obtain ⟨hst1, hres1, hcost1, _⟩ := compSearchMicroChainGenProg_spec
    (q_target := q_target) henv hcpl hslot hm_items hb hm hchain hc_lt
  obtain ⟨hst2, hres2, hcost2, _⟩ := compSearchOverflowGenProg_spec
    (q_target := q_target) henv hcpl hslot hm_items hb
  obtain ⟨hslot_fix, hchain_fix, hc_lt_fix⟩ :=
    fixedCoupled_bucketSearch_inv hcpl hslot hchain hc_lt
  have hst1_fix :
      (Memory.spec 0).clientState s_fix
        (searchMicroChainProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_target), m)) = s_fix :=
    (searchMicroChainProg_spec
      (d := (((0, b), q_target), m))
      (ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V)
      hb hm hslot_fix hchain_fix hc_lt_fix).1
  rcases hres_fix : (Memory.spec 0).clientResult s_fix
      (searchMicroChainProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_target), m)) with ⟨⟨⟨ptr1, found1⟩, j1⟩, phys1⟩
  rw [hres_fix] at hres1
  have hfix_eq : (Memory.spec 0).clientResult s_fix prog_fix =
      (Memory.spec 0).clientResult s_fix
        (if found1 = 1 then pure ((1, j1), phys1)
        else searchOverflowProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, b), q_target)) := by
    simp only [prog_fix, searchBucketProg, searchBucketGenProg, searchBucketGenQuery,
      searchMicroChainGenProg_mk, searchOverflowGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, hst1_fix, hres_fix]
  rw [hfix_eq]
  dsimp only [prog, compSearchBucketGenProg]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst1, hres1,
    StateTransitionSpec.clientResult_bind, hst1, hres1,
    memoryCost_bind_of_clientState_eq hst1, hres1]
  dsimp only [compUnpackMicroResProg, gm]
  simp only [pure_bind]
  split_ifs with hf1
  · subst hf1
    rw [StateTransitionSpec.clientState_pure, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_pure, memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩
  · exact ⟨hst2, hres2, by omega⟩

theorem realizesBounded_compSearchBucketGen :
    RealizesBounded .exact compSearchBucketGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompSearchBucketPre (fun _ _ => 0) := by
  have hm := realizesBounded_compSearchMicroChainGen
  have hunp := realizesBounded_compUnpackMicroRes
  have ho := realizesBounded_compSearchOverflowGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
    obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
      hb, hm_lt, hchain, hc_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    have hst1 := (compSearchMicroChainGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1)
  · exact ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩
  · exact fits_const_of_offCompItems hfit_meta (by decide)
  · have hst_unp :
        (Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (compSearchMicroChainGenProg
              (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m)))
          (compUnpackMicroResProg
            ((Memory.spec 0).clientResult s
              (compSearchMicroChainGenProg
                (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m)))) = s := by
      rw [hst1]
      rcases (Memory.spec 0).clientResult s _ with ⟨⟨⟨_, _⟩, _⟩, _⟩
      rfl
    change CompSearchOverflowPre w _
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (compSearchMicroChainGenProg
            (((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m)))
        (compUnpackMicroResProg _))
    rw [hst_unp]
    exact ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩

theorem validProg_compSearchBucketGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : CompSearchBucketPre w d s) : ValidProg w 0 s (compSearchBucketGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := h
  have hst1 := (compSearchMicroChainGenProg_spec (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  dsimp only [compSearchBucketGenProg]; simp only [pure_bind]
  refine validProg_bind (validProg_compSearchMicroChainGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rw [hst1]
  rcases (Memory.spec 0).clientResult s _ with ⟨⟨⟨_, found1⟩, j1⟩, phys1⟩
  dsimp only [compUnpackMicroResProg]; simp only [pure_bind]
  exact validProg_ite (fun _ => validProg_pure _)
    (fun _ => validProg_compSearchOverflowGen
      ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb⟩)

private def compQueryFoundValProg :
    (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog (Option ℕ)
  | ((cp, (metaBase, itemBase)), phys) => do
    let v ← compReadPhysValGenProg ((cp, (metaBase, itemBase)), phys)
    pure (some v)

private theorem realizesBounded_compQueryFoundVal :
    RealizesBounded .exact compQueryFoundValProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Option ℕ))
      CompReadPhysItemPre (fun _ _ => 0) := by
  have hrv := realizesBounded_compReadPhysValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩
    obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
      hb, hj, rfl⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1)
  · exact ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items, hb, hj, rfl⟩
  · exact fits_const_of_offCompItems hfit_meta (by decide)

/-- Compacted dictionary lookup body (`¬ReadsWidth`):
searches bucket `(b, m)` for `q_target`, and if found (`found = 1`), translates `phys` via
`denseOfPhysGenProg` and reads `some v` from the dense item stream. -/
def compQueryBodyGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog (Option ℕ)
  | (((cp, (metaBase, itemBase)), (b, q_target)), m) => do
    let res ← compSearchBucketGenProg ((((cp, (metaBase, itemBase)), (b, q_target)), m))
    let pair ← pure res.1
    let found ← pure pair.1
    let phys ← pure res.2
    let z1 ← pure 1
    if found = z1 then
      compQueryFoundValProg ((cp, (metaBase, itemBase)), phys)
    else
      pure none

open Classical in
theorem searchBucket_found_slotOf
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
    match (Memory.spec 0).clientResult s
      (compSearchBucketGenProg ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m)))
    with
    | ((found, j_found), phys_found) =>
      found = 1 →
        j_found < bCount N (compGmAt metaBase U w N s.mem) b ∧
        phys_found = slotOf N (compGmAt metaBase U w N s.mem) b j_found := by
  have hres_sb :
      (Memory.spec 0).clientResult s
        (compSearchBucketGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) =
      (Memory.spec 0).clientResult s_fix
        (searchBucketProg U V (ghostW w) N (hashSpace U (ghostW w) N)
          (((0, b), q_target), m)) :=
    (compSearchBucketGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb hm hchain hc_lt).2.1
  obtain ⟨hslot_fix, hchain_fix, hc_lt_fix⟩ :=
    fixedCoupled_bucketSearch_inv hcpl hslot hchain hc_lt
  have hres_spec := (searchBucketProg_spec
    (d := (((0, b), q_target), m))
    (ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V)
    hb hm hslot_fix hchain_fix hc_lt_fix).2.2
  dsimp only [ovfQueryBase, ovfQueryBucket, ovfQueryQuot] at hres_spec
  rw [hres_sb]
  rcases hres_eq : (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (hashSpace U (ghostW w) N)
        (((0, b), q_target), m)) with ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres_eq] at hres_spec
  dsimp only [ovfSearchFound, ovfSearchIdx] at hres_spec ⊢
  intro hf1
  by_cases hex :
      (∃ j ∈ L, quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
        (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) =
        q_target) ∨
      (∃ j, effBucketCap N ≤ j ∧
        j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b ∧
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) =
          q_target)
  · rw [ite_eq_left hex] at hres_spec
    obtain ⟨_, hj_bc_fix, _, _, hphys_eq⟩ := hres_spec
    change j_found < bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
      at hj_bc_fix
    change phys_found = slotOf N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
      b j_found at hphys_eq
    rw [← hcpl.gm_eq] at hj_bc_fix hphys_eq
    exact ⟨hj_bc_fix, hphys_eq⟩
  · rw [ite_eq_right hex] at hres_spec
    omega

open Classical in
theorem compQueryBodyGenProg_spec
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
    let prog := compQueryBodyGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))
    let prog_fix := queryBodyProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), m)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 16 + 12 * L.length + 10 * (bCount N gm b - effBucketCap N) := by
  intro gm prog prog_fix
  obtain ⟨hst_sb, hres_sb, hcost_sb⟩ := compSearchBucketGenProg_spec
    (q_target := q_target) henv hcpl hslot hm_items hb hm hchain hc_lt
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm hchain hc_lt
  obtain ⟨hslot_fix, hchain_fix, hc_lt_fix⟩ :=
    fixedCoupled_bucketSearch_inv hcpl hslot hchain hc_lt
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_target), m)) = s_fix :=
    (searchBucketProg_spec
      (d := (((0, b), q_target), m))
      (ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V)
      hb hm hslot_fix hchain_fix hc_lt_fix).1
  dsimp only [prog, prog_fix, compQueryBodyGenProg]
  simp only [queryBodyProg, queryBodyGenProg, searchBucketGenProg_mk, readValGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, memoryCost_bind_of_clientState_eq hst_sb,
    hst_sb, hst_sb_fix]
  rcases hres_eq : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres_eq] at hres_sb hfnd
  rw [← hres_sb]
  dsimp only [ovfSearchFound, ovfQueryBase] at hfnd ⊢
  dsimp only [gm]
  split_ifs with hf1
  · obtain ⟨hj_bc, hphys_comp⟩ := hfnd hf1
    have hphys_lt : phys_found < N := by
      rw [hphys_comp]; exact (slotOf_lt_and_injective hslot).1 b hb j_found hj_bc
    have hrv_cost := memoryCost_compReadPhysValGenProg_le
      ((mkCompParams U V w N, (metaBase, itemBase)), phys_found) s
    dsimp only [compQueryFoundValProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compReadPhysValGenProg,
      StateTransitionSpec.clientState_pure,
      StateTransitionSpec.clientResult_bind, clientState_compReadPhysValGenProg,
      StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_bind, clientState_readValProg,
      clientResult_readValProg s_fix hphys_lt, StateTransitionSpec.clientResult_pure,
      memoryCost_bind_of_clientState_eq (clientState_compReadPhysValGenProg _ s), memoryCost_pure,
      hphys_comp, clientResult_compReadPhysVal_slotOf hcpl henv hslot hm_items hb hj_bc]
    rw [hphys_comp] at hrv_cost
    exact ⟨rfl, rfl, by omega⟩
  · simp only [memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩

theorem realizesBounded_compQueryBodyGen :
    RealizesBounded .exact compQueryBodyGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Option ℕ))
      CompSearchBucketPre (fun _ _ => 0) := by
  have hsb := realizesBounded_compSearchBucketGen
  have hfv := realizesBounded_compQueryFoundVal
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
    change CompReadPhysItemPre w _
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
    dsimp only at hc
    obtain ⟨hj_bc, rfl⟩ := hfnd hc
    exact ⟨U, V, N, m_items, s_fix, b, j_found, rfl, henv, hcpl, hslot, hm_items, hb, hj_bc, rfl⟩

theorem validProg_compQueryBodyGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : CompSearchBucketPre w d s) : ValidProg w 0 s (compQueryBodyGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := h
  have hst_sb := (compSearchBucketGenProg_spec (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt
  dsimp only [compQueryBodyGenProg, compQueryFoundValProg]; simp only [pure_bind]
  refine validProg_bind (validProg_compSearchBucketGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rw [hst_sb]
  rcases hres : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres] at hfnd
  dsimp only
  refine validProg_ite (fun hc => ?_) (fun _ => validProg_pure _)
  obtain ⟨hj_bc, rfl⟩ := hfnd hc
  refine validProg_bind
    (validProg_compReadPhysValGen
      ⟨U, V, N, m_items, s_fix, b, j_found, rfl, henv, hcpl, hslot, hm_items, hb, hj_bc, rfl⟩) ?_
  exact validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
