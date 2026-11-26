/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `fcBucket` and unfolds `compFeistelCoordsProg` in `DeleteFinish` obligations.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `compDeleteSwapGenProg` and its effect, validity, and `compGmAt` lemmas.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeleteSwap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Deletion Phase 2: Tail Pop, Found Branch, and Finish (`Memory.Prog`)

Implements `compDeleteFinishWithHashGenProg`, `CompDeleteFinishWithHashPre`, and their
`RealizesBounded .exact` and `ValidProg` certificates, plus internal found-branch helpers.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteFinishWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompDeleteFinishWithHashPre`:
  Feistel-dispatched Phase 2 of compacted deletion and its precondition.
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

private theorem compUnlinkIfIndexed_step {metaBase itemBase U V w N m_cap b j_del m m_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hm_last : m_last < numMicroPerBucket N)
    (hj_del_bc : j_del < bCount N (compGmAt metaBase U w N s.mem) b)
    (hval : AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) L)
    (hmem_del : j_del < effBucketCap N → j_del ∈ L b m)
    (hmem_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 < effBucketCap N →
      bCount N (compGmAt metaBase U w N s.mem) b - 1 ∈ L b m_last) :
    let s₁ := (Memory.spec 0).clientState s
      (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
    let sf₁ := (Memory.spec 0).clientState s_fix
      (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_del))
    CompUnlinkIfIndexedPre w (((mkCompParams U V w N, metaBase), (b, m)), j_del) s ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s₁ ∧
    CompEpochEnv U V w N metaBase itemBase m_cap s₁ ∧
    FixedCoupled metaBase itemBase U V w N sf₁ s₁ ∧
    compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem ∧
    ∃ L₁, AllChainsValid N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem) L₁ ∧
      (j_del < bCount N (compGmAt metaBase U w N s.mem) b - 1 →
        bCount N (compGmAt metaBase U w N s.mem) b - 1 < effBucketCap N →
        bCount N (compGmAt metaBase U w N s.mem) b - 1 ∈ L₁ b m_last) := by
  have hwg : 0 < ghostW w := by grind [ghostW]
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
  obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u1.2.2.2.2.2
  exact ⟨⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb, hm, hbounds_del⟩,
    hfr1, henv.of_mem_eq (by rw [hfr1.frontier_eq]), hcpl1,
    hcpl1.gm_eq.trans (eff_u1.2.2.2.2.1.trans hcpl.gm_eq.symm), L₁, hval₁,
    fun hlt hj_cap => (hmem₁ b hb m_last hm_last _).2 ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩⟩

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
  have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := Nat.one_le_of_lt hj_del_bc
  obtain ⟨_, hfr1, henv1, hcpl1, hgm1, L₁, hval₁, hmem_last₁⟩ :=
    compUnlinkIfIndexed_step henv hcpl hslot hb hm hm_last hj_del_bc hval hmem_del hmem_last
  set s₁ := (Memory.spec 0).clientState s
    (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
  set sf₁ := (Memory.spec 0).clientState s_fix
    (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_del))
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := hgm1.symm ▸ hm_cap
  set c_b := bCount N (compGmAt metaBase U w N s.mem) b
  set j_last := c_b - 1
  have hs'_tail : s' = (Memory.spec 0).clientState s₁
      (if j_del < j_last then do
        compDeleteSwapGenProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
            (m_last, j_last)))
        compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
      else
        compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) := by
    dsimp only [s', d, compDeleteFoundGenProg, compDeleteFoundTailProg, s₁, j_last, c_b]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb, hgm1]
  have hs_fix'_tail : s_fix' = (Memory.spec 0).clientState sf₁
      (if j_del < j_last then do
        deleteSwapProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((((0, b), j_del), phys_del), (m_last, j_last))
        popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)
      else
        popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
    dsimp only [s_fix', sf₁, j_last, c_b]
    unfold deleteFoundProg deleteFoundGenProg
    simp only [unlinkIfIndexedGenProg_mk, readBucketCountGenProg_mk, deleteSwapGenProg_mk,
      popBackSlotGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readBucketCountProg, clientResult_readBucketCountProg (0, b) sf₁ hb,
      ← hcpl1.gm_eq, hgm1]
  have hcost_pre : memoryCost (compDeleteFoundGenProg d) s ≤ 16 +
      memoryCost (if j_del < j_last then do
        compDeleteSwapGenProg
          (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
            (m_last, j_last)))
        compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
      else
        compPopBackSlotGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) s₁ := by
    dsimp only [d, compDeleteFoundGenProg, compDeleteFoundTailProg, j_last, c_b]
    simp only [pure_bind]
    rw [Realization.memoryCost_bind',
      memoryCost_bind_of_clientState_eq (clientState_readCompBucketCountGenProg _ s₁) _,
      clientResult_readCompBucketCountGenProg hb, hgm1]
    have hc1 := memoryCost_compUnlinkIfIndexedGenProg_le
      (((mkCompParams U V w N, metaBase), (b, m)), j_del) s
    have hc2 := memoryCost_readCompBucketCountGenProg_le
      ((mkCompParams U V w N, metaBase), b) s₁
    dsimp only [s₁, j_last, c_b] at hc2 ⊢
    omega
  by_cases hlt : j_del < j_last
  · have hj_last_bc1 : j_last < bCount N (compGmAt metaBase U w N s₁.mem) b :=
      hgm1.symm ▸ Nat.sub_lt hbc_pos Nat.one_pos
    obtain ⟨hfr_sw, hcpl_sw⟩ := compDeleteSwapGenProg_effect
      henv1 hcpl1 hslot1 hm_cap1 hb hm_last hlt hj_last_bc1 hval₁ (hmem_last₁ hlt)
    have hphys_eq1 : slotOf N (compGmAt metaBase U w N s₁.mem) b j_del = phys_del := by rw [hgm1]
    rw [hphys_eq1] at hfr_sw hcpl_sw
    set s₂ := (Memory.spec 0).clientState s₁
      (compDeleteSwapGenProg
        (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
          (m_last, j_last))))
    have hgm2 : compGmAt metaBase U w N s₂.mem = compGmAt metaBase U w N s.mem :=
      (hphys_eq1 ▸ compGmAt_compDeleteSwapGenProg
        henv1 hcpl1 hslot1 hm_cap1 hb hm_last hlt hj_last_bc1 hval₁ (hmem_last₁ hlt)).trans hgm1
    have henv2 := henv1.of_mem_eq (s' := s₂) (by rw [hfr_sw.frontier_eq])
    obtain ⟨hfr_pop, hcpl_pop, hcost_pop⟩ := compPopBackSlotGenProg_effect
      henv2 hcpl_sw (hgm2.symm ▸ hslot) hb (hgm2.symm ▸ hbc_pos) (hgm2.symm ▸ hm_cap)
    rw [hgm2] at hcost_pop
    rw [hs'_tail, hs_fix'_tail, ite_eq_left hlt, ite_eq_left hlt,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    refine ⟨hfr1.trans (hfr_sw.trans hfr_pop), hcpl_pop, ?_⟩
    rw [ite_eq_left hlt, Realization.memoryCost_bind'] at hcost_pre
    have hc3 := memoryCost_compDeleteSwapGenProg_le
      (((((mkCompParams U V w N, (metaBase, itemBase)), (b, j_del)), phys_del),
        (m_last, j_last))) s₁
    dsimp only [s₂, s₁, j_last, c_b] at hc3 hcost_pre hcost_pop ⊢
    omega
  · obtain ⟨hfr_pop, hcpl_pop, hcost_pop⟩ := compPopBackSlotGenProg_effect
      henv1 hcpl1 hslot1 hb (hgm1.symm ▸ hbc_pos) hm_cap1
    rw [hgm1] at hcost_pop
    rw [hs'_tail, hs_fix'_tail, ite_eq_right hlt, ite_eq_right hlt]
    rw [ite_eq_right hlt] at hcost_pre
    refine ⟨hfr1.trans hfr_pop, hcpl_pop, ?_⟩
    dsimp only [s₁, j_last, c_b] at hcost_pop hcost_pre ⊢
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
    obtain ⟨hpre_u, _, henv1, hcpl1, hgm1, L₁, hval₁, hmem_last₁⟩ :=
      compUnlinkIfIndexed_step henv hcpl hslot hb hm hm_last hj_del_bc hval hmem_del hmem_last)
  · exact hpre_u
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv1.meta_le_frontier, hgm1.symm ▸ hslot, hb⟩
  · rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb]
    exact ⟨U, V, N, m_cap, _, L₁, rfl, henv1, hcpl1,
      hgm1.symm ▸ hslot, hgm1.symm ▸ hm_cap, hb, hm_last, rfl, hgm1.symm ▸ hj_del_bc,
      by rw [hgm1], hval₁, hgm1.symm ▸ hmem_last₁⟩

private theorem validProg_compDeleteFoundGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDeleteFoundPre w d s) : ValidProg w 0 s (compDeleteFoundGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, j_del⟩⟩, phys_del⟩, ⟨m, m_last⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, L, rfl, henv, hcpl, hslot, hm_cap,
    hb, hm, hm_last, hj_del_bc, rfl, hval, hmem_del, hmem_last⟩ := h
  have hbc_pos : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := Nat.one_le_of_lt hj_del_bc
  obtain ⟨hpre_u, _, henv1, hcpl1, hgm1, L₁, hval₁, hmem_last₁⟩ :=
    compUnlinkIfIndexed_step henv hcpl hslot hb hm hm_last hj_del_bc hval hmem_del hmem_last
  set s₁ := (Memory.spec 0).clientState s
    (compUnlinkIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_del))
  set sf₁ := (Memory.spec 0).clientState s_fix
    (unlinkIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_del))
  have hslot1 : SlotStoreInv N (compGmAt metaBase U w N s₁.mem) := hgm1.symm ▸ hslot
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := hgm1.symm ▸ hm_cap
  dsimp only [compDeleteFoundGenProg, compDeleteFoundTailProg]
  simp only [pure_bind]
  refine validProg_bind (validProg_compUnlinkIfIndexedGen hpre_u)
    (validProg_bind (validProg_readCompBucketCountGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv1.meta_le_frontier, hslot1, hb⟩) ?_)
  rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb, hgm1]
  refine validProg_ite (fun hlt => ?_) (fun _ =>
    validProg_compPopBackSlotGen
      ⟨U, V, N, m_cap, sf₁, rfl, henv1, hcpl1, hslot1, hb, hgm1.symm ▸ hbc_pos, hm_cap1⟩)
  set j_last := bCount N (compGmAt metaBase U w N s.mem) b - 1
  have hj_last_bc1 : j_last < bCount N (compGmAt metaBase U w N s₁.mem) b :=
    hgm1.symm ▸ Nat.sub_lt hbc_pos Nat.one_pos
  refine validProg_bind
    (validProg_compDeleteSwapGen
      ⟨U, V, N, m_cap, sf₁, L₁, rfl, henv1, hcpl1, hslot1, hm_cap1, hb, hm_last,
        hlt, hj_last_bc1, by rw [hgm1], hval₁, hmem_last₁ hlt⟩) ?_
  have hpop_pre := compDeleteFoundTail_popPre
    henv1 hcpl1 hslot1 hm_cap1 hb hm_last (hgm1.symm ▸ hj_del_bc)
    (hgm1.symm ▸ hlt) hval₁ (hgm1.symm ▸ hmem_last₁ hlt)
  rw [hgm1] at hpop_pre
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


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
