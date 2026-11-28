/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `gmAt_prependIfIndexedProg` in `compGmAt_compDeleteSwapGenProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Internal Last-Slot Payload Copy and Swap Machinery for Compacted Deletion

Private payload-copy (`compResolveCopyPairProg`, `compCopyLastPayloadGenProg`) and swap
(`compDeleteSwapCopyProg`, `compDeleteSwapGenProg`) subroutines and effect lemmas imported via
`import all` by `DeleteFinish.lean`.
-/

-- This proof-only companion is intentionally private; `DeleteFinish.lean` imports all.
set_option linter.privateModule false

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
    hgm_f.symm ▸ htd_f.symm ▸ hdt_f.symm ▸ hcpl.win_inv,
    fun i => htd_f.symm ▸ hcpl.td_lt i,
    fun i => hdt_f.symm ▸ hcpl.dt_lt i,
    fun d' hd' => ?_,
    fun d' hd' => ?_⟩
  · rw [hgm_f] at hd' ⊢
    rw [hdt_f, hq_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      dsimp only [physOfDense] at hvirt
      rw [compQuotAt_writeCompQuot_self s.mem hd_lt hq_lt, hvirt, Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq]
      have hg_ne : physByBase N (gm 0 * slabSize N) (compDTAt metaBase U w N s.mem) d' ≠ g :=
        fun heq => by
          obtain ⟨hb'_lt, hj'_lt, hd'_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd'
          obtain ⟨rfl, rfl⟩ := (slotOf_lt_and_injective hslot).2 _ hb'_lt _ hj'_lt b hb j hj
            ((physOfDense_eq_slotOf_owner hslot htd hd').symm.trans heq)
          exact hdeq hd'_eq.symm
      exact Function.update_of_ne hg_ne _ _ ▸ hcpl.quot_eq d' hd'
  · rw [hgm_f] at hd' ⊢
    rw [compValAt_writeCompQuot hw s.mem, hdt_f, hv_fix]
    exact hcpl.val_eq d' hd'


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
  simp only [StateTransitionSpec.clientState, compResolveCopyPairProg, prog_runClient_state_bind,
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
  simp only [compCopyLastPayloadGenProg, compResolveCopyPairProg, Realization.memoryCost_bind',
    runClient_state_compLastSlotOfGenProg, runClient_state_denseOfPhysGenProg, memoryCost_pure,
    memoryCost_copyCompItemGenProg]
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
  simp only [client_simps, StateTransitionSpec.clientState, runClient_state_compLastSlotOfGenProg,
    runClient_state_denseOfPhysGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc,
    clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_del]
  rw [clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj_last]

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
  have hphys_last_lt : phys_last < N := (slotOf_lt_and_injective hslot).1 b hb j_last hj_last
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, phys_del),
            quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)))
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((0, phys_del),
          valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)) := by
    simp only [s_fix', copyLastPayloadProg, copyLastPayloadGenProg, lastSlotOfGenProg_mk,
      readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk]
    rw [StateTransitionSpec.clientState_bind, clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (0, b) s_fix (hcpl.gm_eq ▸ hslot) hb (hcpl.gm_eq ▸ hbc),
      ← hcpl.gm_eq, StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s_fix hphys_last_lt, StateTransitionSpec.clientState_bind,
      clientState_readValProg, clientResult_readValProg s_fix hphys_last_lt,
      StateTransitionSpec.clientState_bind]
  have hcpl1 := hcpl.writeQuot_slotOf henv.pos_w henv.meta_le_item hslot hb hj_del
    (quotAt_lt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)
  obtain ⟨_, hgm1, htd1, _⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N)
    (q := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)
    henv.pos_w henv.meta_le_item hd_dst_lt s.mem
  have hcpl2 := hcpl1.writeVal_slotOf henv.pos_w henv.meta_le_item (hgm1.symm ▸ hslot) hb
    (hgm1.symm ▸ hj_del)
    (valAt_lt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem phys_last)
  simp only [hgm1, htd1] at hcpl2
  rw [hs'_eq, hs_fix'_eq]
  exact ⟨⟨rfl, fun a _ hi => (writeCompVal_outside henv.pos_w hd_dst_cap _ hi).trans
    (writeCompQuot_outside henv.pos_w hd_dst_cap s.mem hi)⟩, hcpl2⟩

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
  simp only [compCopyLastPayloadGenProg, compResolveCopyPairProg, bind_assoc]
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
    gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₂.mem =
      compGmAt metaBase U w N s.mem ∧
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
  have hgm_sf1 := eff_u.2.2.2.2.1.trans hcpl.gm_eq.symm
  have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (phys_del := phys_del)
    hwg (hgm_sf1.symm ▸ hslot) hb (hgm_sf1.symm ▸ Nat.one_le_of_lt hj_last_bc) hphys_del_lt
  obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
  have hold2 : lmHead N (compLmAt metaBase U w N s₂.mem) b m_last ≤ effBucketCap N := by
    rw [hcpl2.lm_eq, eff_c.2.2.2.2.1]
    exact (hval₁.1 b hb m_last hm_last).head_le_cap
  refine ⟨hfr1, hfr2, hcpl2, hold2, eff_c.2.2.2.2.2.trans hgm_sf1,
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hb, hm_last, hbounds⟩,
    ⟨U, V, N, m_cap, sf₁, j_del, rfl, henv1, hcpl1, hslot1, hm_cap1, hb, hj_del_bc1,
      hphys_eq1.symm⟩,
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr2.frontier_eq ▸ hfr1.frontier_eq ▸ henv.meta_le_frontier, hb, hm_last, hold2⟩⟩

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
      hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩ := h)
  · exact (compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc
      hval hmem_last).2.2.2.2.2.1
  · exact (compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc
      hval hmem_last).2.2.2.2.2.2.1

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
  simp only [compDeleteSwapGenProg, compDeleteSwapCopyProg, Realization.memoryCost_bind',
    prog_runClient_state_bind]
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
  have hstg :=
    compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
  obtain ⟨hfr3, hcpl3⟩ := compPrependIfIndexedGenProg_effect
    (m_cap := m_cap) (j_new := j_del) henv.pos_w henv.meta_le_item hstg.2.2.1 hb hm_last
    hstg.2.2.2.1
  simp only [s', s_fix', d, phys_del, compDeleteSwapGenProg, compDeleteSwapCopyProg,
    deleteSwapProg, deleteSwapGenProg, unlinkIfIndexedGenProg_mk, copyLastPayloadGenProg_mk,
    prependIfIndexedGenProg_mk]
  repeat rw [StateTransitionSpec.clientState_bind]
  exact ⟨hstg.1.trans (hstg.2.1.trans hfr3), hcpl3⟩

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
  · change CompPrependIfIndexedPre w _
      ((Memory.spec 0).clientState s
        (compDeleteSwapCopyProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), b),
            slotOf N (compGmAt metaBase U w N s.mem) b j_del), (m_last, j_last)))))
    dsimp only [compDeleteSwapCopyProg]
    rw [StateTransitionSpec.clientState_bind]
    exact (compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc
      hval hmem_last).2.2.2.2.2.2.2

private theorem validProg_compDeleteSwapGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDeleteSwapPre w d s) : ValidProg w 0 s (compDeleteSwapGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m_last, j_last⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
    hb, hm_last, hj_lt, hj_last_bc, rfl, hval, hmem_last⟩ := h
  have hpre := (compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc
    hval hmem_last).2.2.2.2.2
  simp only [compDeleteSwapGenProg, compDeleteSwapCopyProg, bind_assoc]
  exact validProg_bind (validProg_compUnlinkIfIndexedGen hpre.1) <|
    validProg_bind (validProg_compCopyLastPayloadGen hpre.2.1) <|
      validProg_compPrependIfIndexedGen hpre.2.2

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
  have hstg := (compDeleteSwap_stages henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc
    hval hmem_last).2.2
  obtain ⟨_, hcpl_sw⟩ := compDeleteSwapGenProg_effect
    henv hcpl hslot hm_cap hb hm_last hj_lt hj_last_bc hval hmem_last
  have hgm_pr := gmAt_prependIfIndexedProg (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (m := m_last) (j_new := j_del)
    hwg hb hm_last _ (hstg.1.lm_eq ▸ hstg.2.1)
  rw [hcpl_sw.gm_eq]
  simp only [deleteSwapProg, deleteSwapGenProg, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]
  repeat rw [StateTransitionSpec.clientState_bind]
  exact hgm_pr.trans hstg.2.2.1


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
