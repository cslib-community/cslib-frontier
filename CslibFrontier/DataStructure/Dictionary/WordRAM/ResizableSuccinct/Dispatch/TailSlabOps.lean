/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps
-- Unfolds `Memory.Prog` bodies in `Accessors` and `Succinct*` for `FixedCoupled` simulation.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Tail Allocation, `K`-Step Slab Promotion/Demotion, and Amortized Slot Operations

This module implements the compacted tail-allocation, `K`-step (`K = slabSize N`) circular-window
slab promotion/demotion, and amortized `O(1)` slot push/pop subroutines in `Memory.Prog`
(`¬ReadsWidth`, certified via `by realize` and `RealizesBounded.iterate₀`), coupling every step via
`WindowCoupled` and `FixedCoupled` to the fixed-capacity reference operations in
`SuccinctTailOps.lean`, `SuccinctSlabMove.lean`, `SuccinctSlabDemote.lean`, and
`SuccinctSlabOps.lean`:
* `CompOpFrame`: memory frame relation for operations modifying only compacted metadata in
  `[metaBase + offCompLM U w N, metaBase + offCompItems U w N)` and dense items in
  `[itemBase, itemBase + compactedItemWords U V w N m_cap)`;
* `compPushBackSlotGenProg`: appends `(q_val, v_val)` at logical slot `bCount N gm b` of bucket
  `b`, promoting `K` tail items into a full slab when `r_b + 1 = 2 * K`, with `O(1)` amortized
  `memoryCost` against `98 * slotPotential N gm`;
* `compPopBackSlotGenProg`: removes the last logical slot `bCount N gm b - 1` of bucket `b`,
  demoting the top full slab into `K` tail items when `r_b - 1 = 0 ∧ 0 < q_b`, with `O(1)`
  amortized `memoryCost` against `98 * slotPotential N gm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompOpFrame`:
  frame predicate preserving outside memory, root header, stored parameters, and hash tables.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompPushBackSlotPre`:
  compacted bucket-append operation and its parameter-free realization precondition.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompPopBackSlotPre`:
  compacted bucket-pop operation and its parameter-free realization precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compPushBackSlotGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compPushBackSlotGen`:
  `FixedCoupled` equivalence to `pushBackSlotProg`, `O(1)` amortized cost bound,
  `RealizesBounded .exact` certificate, and `ValidProg` admissibility.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compPopBackSlotGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compPopBackSlotGen`:
  `FixedCoupled` equivalence to `popBackSlotProg`, `O(1)` amortized cost bound,
  `RealizesBounded .exact` certificate, and `ValidProg` admissibility.

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

/-! ## Section 1: `CompOpFrame` and `WindowCoupled` Bijection / Update Lemmas -/

/-- Memory frame relation for compacted operations modifying only metadata in
`[metaBase + offCompLM U w N, metaBase + offCompItems U w N)` and dense items in
`[itemBase, itemBase + compactedItemWords U V w N m_cap)`. -/
structure CompOpFrame (metaBase itemBase U V w N m_cap : ℕ) (s s' : Memory.State) : Prop where
  frontier_eq : s'.frontier = s.frontier
  outside_eq : ∀ a,
    ¬(metaBase + offCompLM U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
    ¬(itemBase ≤ a ∧ a < itemBase + compactedItemWords U V w N m_cap) →
    s'.mem a = s.mem a

theorem CompOpFrame.refl {metaBase itemBase U V w N m_cap : ℕ} (s : Memory.State) :
    CompOpFrame metaBase itemBase U V w N m_cap s s :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem CompOpFrame.trans {metaBase itemBase U V w N m_cap : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : CompOpFrame metaBase itemBase U V w N m_cap s₁ s₂)
    (h₂ : CompOpFrame metaBase itemBase U V w N m_cap s₂ s₃) :
    CompOpFrame metaBase itemBase U V w N m_cap s₁ s₃ :=
  ⟨h₂.frontier_eq.trans h₁.frontier_eq,
    fun a hm hi => (h₂.outside_eq a hm hi).trans (h₁.outside_eq a hm hi)⟩

private theorem CompOpFrame.of_gmFrame {metaBase itemBase U V w N m_items m_cap : ℕ}
    {s s' : Memory.State} (h : CompGmFrame metaBase itemBase U V w N m_items s s') :
    CompOpFrame metaBase itemBase U V w N m_cap s s' := by
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h2 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨h.frontier_eq, fun a hm _ => h.outside_eq a (by omega)⟩

private theorem tailBijection_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (htail : TailBijection N gm₂ (fun b' => gm₂ (gmRIdx b')) (gm₂ 1)) :
    TailBijection N gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) := by
  rw [h]; exact htail

private theorem slabBijection_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (hslab : SlabBijection N gm₂ (fun b' => gm₂ (gmQIdx b')) (gm₂ 0)) :
    SlabBijection N gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) := by
  rw [h]; exact hslab

private theorem slotStoreInv_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (hs : SlotStoreInv N gm₂) :
    SlotStoreInv N gm₁ := by
  rw [h]; exact hs

private theorem compOpFrame_writeCompQuot {metaBase itemBase U V w N m_cap d q : ℕ}
    (hw : 0 < w) (hd : d < m_cap) (s : Memory.State) :
    CompOpFrame metaBase itemBase U V w N m_cap s
      ((Memory.spec 0).clientState s
        (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), d), q))) := by
  rw [clientState_writeCompQuotGenProg]
  exact ⟨rfl, fun a _ hi => writeCompQuot_outside hw hd s.mem hi⟩

private theorem compOpFrame_writeCompVal {metaBase itemBase U V w N m_cap d v : ℕ}
    (hw : 0 < w) (hd : d < m_cap) (s : Memory.State) :
    CompOpFrame metaBase itemBase U V w N m_cap s
      ((Memory.spec 0).clientState s
        (writeCompValGenProg (((mkCompParams U V w N, itemBase), d), v))) := by
  rw [clientState_writeCompValGenProg]
  exact ⟨rfl, fun a _ hi => writeCompVal_outside hw hd s.mem hi⟩

private theorem compOpFrame_copyCompItem {metaBase itemBase U V w N m_cap src dst : ℕ}
    (hw : 0 < w) (hsrc : src < m_cap) (hdst : dst < m_cap) (s : Memory.State) :
    CompOpFrame metaBase itemBase U V w N m_cap s
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst)))) := by
  rw [clientState_copyCompItemGenProg hsrc]
  exact ⟨rfl, fun a _ hi =>
    (writeCompVal_outside hw hdst _ hi).trans (writeCompQuot_outside hw hdst s.mem hi)⟩

private theorem compOpFrame_tailWindow {metaBase itemBase U V w N m_cap : ℕ} {s s' : Memory.State}
    (hfr : s'.frontier = s.frontier)
    (hout : ∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      s'.mem a = s.mem a) :
    CompOpFrame metaBase itemBase U V w N m_cap s s' := by
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  exact ⟨hfr, fun a hm _ => hout a (by omega)⟩

private theorem maxTailItems_pos_of_bucketBits_pos {N : ℕ} (hb_pos : 0 < bucketBits N) :
    0 < maxTailItems N := by
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hB : 0 < numBuckets N := numBuckets_pos N
  have hK : 0 < slabSize N := slabSize_pos N
  unfold maxTailItems tailCapPerBucket
  rw [ite_eq_right hb0]
  exact Nat.mul_pos hB (by omega)

private theorem physByBase_slab {N b_win : ℕ} (dt : ℕ → ℕ) {g : ℕ} (hg : g < b_win) :
    physByBase N b_win dt g = g := by
  unfold physByBase; split_ifs <;> rfl

private theorem physByBase_tail_denseOfCirc {N b_win n_win : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b_win n_win td dt)
    {t : ℕ} (ht : t < n_win) :
    let d := denseOfCirc (maxTailItems N) b_win (td t)
    b_win ≤ d ∧ d < b_win + n_win ∧ physByBase N b_win dt d = N - 1 - t := by
  intro d
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hc_lt : td t < maxTailItems N := hw.td_lt t ht
  have hge : b_win ≤ d := denseOfCirc_ge (maxTailItems N) b_win (td t)
  have hlt : d < b_win + n_win := hw.dense_lt t ht
  refine ⟨hge, hlt, ?_⟩
  unfold physByBase
  rw [ite_eq_right hb0, ite_eq_right (by omega : ¬d < b_win),
    denseOfCirc_mod hM_pos hc_lt, hw.dt_td t ht]

private theorem physByBase_range_and_inj {N b_win n_win : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hbn : b_win + n_win ≤ N) (hM : n_win ≤ maxTailItems N)
    (hw : WindowInv (maxTailItems N) b_win n_win td dt) :
    (∀ d < b_win + n_win,
      (d < b_win ∧ physByBase N b_win dt d = d) ∨
      (b_win ≤ d ∧ N - n_win ≤ physByBase N b_win dt d ∧ physByBase N b_win dt d < N)) ∧
    (∀ d₁ < b_win + n_win, ∀ d₂ < b_win + n_win,
      physByBase N b_win dt d₁ = physByBase N b_win dt d₂ → d₁ = d₂) := by
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hrng : ∀ d < b_win + n_win,
      (d < b_win ∧ physByBase N b_win dt d = d) ∨
      (b_win ≤ d ∧ N - n_win ≤ physByBase N b_win dt d ∧ physByBase N b_win dt d < N) := by
    intro d hd
    by_cases hlt : d < b_win
    · exact Or.inl ⟨hlt, physByBase_slab dt hlt⟩
    · refine Or.inr ⟨by omega, ?_, ?_⟩
      · obtain ⟨ht_lt, _⟩ := hw.owner_valid d (by omega) hd
        unfold physByBase; rw [ite_eq_right hb0, ite_eq_right hlt]; omega
      · obtain ⟨ht_lt, _⟩ := hw.owner_valid d (by omega) hd
        unfold physByBase; rw [ite_eq_right hb0, ite_eq_right hlt]; omega
  refine ⟨hrng, fun d₁ hd₁ d₂ hd₂ heq => ?_⟩
  rcases hrng d₁ hd₁ with ⟨h1, hp1⟩ | ⟨h1, hlo1, _⟩ <;>
    rcases hrng d₂ hd₂ with ⟨h2, hp2⟩ | ⟨h2, hlo2, _⟩
  · omega
  · omega
  · omega
  · obtain ⟨ht1, htd1⟩ := hw.owner_valid d₁ h1 hd₁
    obtain ⟨ht2, htd2⟩ := hw.owner_valid d₂ h2 hd₂
    unfold physByBase at heq
    rw [ite_eq_right hb0, ite_eq_right (by omega : ¬d₁ < b_win),
      ite_eq_right hb0, ite_eq_right (by omega : ¬d₂ < b_win)] at heq
    have hdt_eq : dt (d₁ % maxTailItems N) = dt (d₂ % maxTailItems N) := by omega
    have hmod_eq : d₁ % maxTailItems N = d₂ % maxTailItems N := by
      rw [← htd1, hdt_eq, htd2]
    rw [← denseOfCirc_mod_self hM_pos h1 (by omega : d₁ < b_win + maxTailItems N),
      ← denseOfCirc_mod_self hM_pos h2 (by omega : d₂ < b_win + maxTailItems N), hmod_eq]

/-- Writing `(q, v)` to dense slot `d < b_win + n_win` in `s` preserves `WindowCoupled` against
updating `(quotAt, valAt)` at `g = physByBase N b_win dt d` in `s_fix`. -/
private theorem windowCoupled_write_at {metaBase itemBase U V w N b_win n_win d g q v : ℕ}
    {s_fix s_fix' s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hbn : b_win + n_win ≤ N) (hM : n_win ≤ maxTailItems N)
    (hcpl : WindowCoupled metaBase itemBase U V w N b_win n_win (b_win + n_win) s_fix s)
    (hd : d < b_win + n_win)
    (hg : physByBase N b_win (compDTAt metaBase U w N s.mem) d = g)
    (hq_lt : q < 2 ^ quotientBits U N) (hv_lt : v < 2 ^ valBits V)
    (hgm_fix : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hlm_fix : lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hq_fix : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) g q)
    (hv_fix : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) g v) :
    let s' : Memory.State :=
      { mem := writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s.mem d q) d v,
        frontier := s.frontier }
    WindowCoupled metaBase itemBase U V w N b_win n_win (b_win + n_win) s_fix' s' := by
  intro s'
  obtain ⟨hlm1, hgm1, htd1, hdt1⟩ :=
    writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N) (q := q)
      hw hitem hd s.mem
  obtain ⟨hlm2, hgm2, htd2, hdt2⟩ :=
    writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N) (v := v)
      hw hitem hd (writeCompQuot itemBase U V w N s.mem d q)
  have hgm_s : compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem := hgm2.trans hgm1
  have hlm_s : compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem := hlm2.trans hlm1
  have htd_s : compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem := htd2.trans htd1
  have hdt_s : compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem := hdt2.trans hdt1
  have hinj := (physByBase_range_and_inj hb_pos hbn hM hcpl.win_inv).2
  refine ⟨hgm_s.trans (hcpl.gm_eq.trans hgm_fix.symm),
    hlm_s.trans (hcpl.lm_eq.trans hlm_fix.symm),
    by rw [htd_s, hdt_s]; exact hcpl.win_inv,
    fun i => by rw [htd_s]; exact hcpl.td_lt i,
    fun i => by rw [hdt_s]; exact hcpl.dt_lt i,
    fun d' hd' => ?_,
    fun d' hd' => ?_⟩
  · dsimp only [s']
    rw [compQuotAt_writeCompVal hw, hdt_s, hq_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      rw [compQuotAt_writeCompQuot_self s.mem hd hq_lt, hg, Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq,
        Function.update_of_ne (fun hp => hdeq (hinj d' hd' d hd (hp.trans hg.symm)))]
      exact hcpl.quot_eq d' hd'
  · dsimp only [s']
    rw [hdt_s, hv_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      rw [compValAt_writeCompVal_self _ hd hv_lt, hg, Function.update_self]
    · rw [compValAt_writeCompVal_of_ne hw _ hdeq, compValAt_writeCompQuot hw s.mem,
        Function.update_of_ne (fun hp => hdeq (hinj d' hd' d hd (hp.trans hg.symm)))]
      exact hcpl.val_eq d' hd'

/-- Copying dense slot `src → dst` in `s` preserves `WindowCoupled` against copying `g_src → g_dst`
in `(quotAt, valAt)` of `s_fix`. -/
private theorem windowCoupled_copyCompItem {metaBase itemBase U V w N b_win n_win src dst
    g_src g_dst : ℕ} {s_fix s_fix' s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hbn : b_win + n_win ≤ N) (hM : n_win ≤ maxTailItems N)
    (hcpl : WindowCoupled metaBase itemBase U V w N b_win n_win (b_win + n_win) s_fix s)
    (hsrc : src < b_win + n_win) (hdst : dst < b_win + n_win)
    (hg_src : physByBase N b_win (compDTAt metaBase U w N s.mem) src = g_src)
    (hg_dst : physByBase N b_win (compDTAt metaBase U w N s.mem) dst = g_dst)
    (hgm_fix : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hlm_fix : lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hq_fix : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) g_dst
        (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src))
    (hv_fix : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) g_dst
        (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src)) :
    WindowCoupled metaBase itemBase U V w N b_win n_win (b_win + n_win) s_fix'
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst)))) := by
  rw [clientState_copyCompItemGenProg hsrc]
  have hq_eq : compQuotAt itemBase U V w N (b_win + n_win) s.mem src =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src := by
    rw [hcpl.quot_eq src hsrc, hg_src]
  have hv_eq : compValAt itemBase U V w N (b_win + n_win) s.mem src =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src := by
    rw [hcpl.val_eq src hsrc, hg_src]
  have hq_lt : compQuotAt itemBase U V w N (b_win + n_win) s.mem src < 2 ^ quotientBits U N := by
    rw [hq_eq]; exact quotAt_lt _ _ _ _ _ _ _
  have hv_lt : compValAt itemBase U V w N (b_win + n_win) s.mem src < 2 ^ valBits V := by
    rw [hv_eq]; exact valAt_lt _ _ _ _ _ _ _ _
  exact windowCoupled_write_at hw hitem hb_pos hbn hM hcpl hdst hg_dst hq_lt hv_lt
    hgm_fix hlm_fix (hq_eq.symm ▸ hq_fix) (hv_eq.symm ▸ hv_fix)

/-- Copying `(b_win + n') → d_last` followed by `winShrinkRight` transitions `WindowCoupled`
from `(b_win, n' + 1, b_win + n' + 1)` to `(b_win, n', b_win + n')` against the same `s_fix`. -/
private theorem windowCoupled_shrinkRight {metaBase itemBase U V w N b_win n' : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hM : n' + 1 ≤ maxTailItems N)
    (hcpl : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1)) s_fix s) :
    let d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
    let s₁ := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win + n', d_last)))
    let s₂ := (Memory.spec 0).clientState s₁
      (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    WindowCoupled metaBase itemBase U V w N b_win n' (b_win + n') s_fix s₂ := by
  intro d_last s₁ s₂
  set M := maxTailItems N
  have hM_pos : 0 < M := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max M 1 = M := Nat.max_eq_left hM_pos
  have hbn_lt : b_win + n' < b_win + (n' + 1) := by omega
  have hd_last_lt : d_last < b_win + (n' + 1) := hcpl.win_inv.dense_lt n' (Nat.lt_succ_self n')
  have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := b_win + (n' + 1)) (itemBase := itemBase) (dst := d_last) hbn_lt s
  obtain ⟨hlm_c1, hgm_c1, htd_c1, hdt_c1⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N)
    (q := compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem (b_win + n'))
    hw hitem hd_last_lt s.mem
  obtain ⟨hlm_c2, hgm_c2, htd_c2, hdt_c2⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N)
    (v := compValAt itemBase U V w N (b_win + (n' + 1)) s.mem (b_win + n'))
    hw hitem hd_last_lt _
  have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hgm_c2.trans hgm_c1
  have hlm1 : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hlm_c2.trans hlm_c1
  have htd1 : compTDAt metaBase U w N s₁.mem = compTDAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact htd_c2.trans htd_c1
  have hdt1 : compDTAt metaBase U w N s₁.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hdt_c2.trans hdt_c1
  have htd_b : ∀ i, compTDAt metaBase U w N s.mem i < M := fun i => hmax_eq ▸ hcpl.td_lt i
  have hdt_b : ∀ i, compDTAt metaBase U w N s.mem i < M := fun i => hmax_eq ▸ hcpl.dt_lt i
  obtain ⟨_, htd2, hdt2, hlm2, hgm2, hq2, hv2, _⟩ :=
    winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + n') (b_win := b_win) (n_win := n')
      hw hitem (by omega) s₁ (by rw [hdt1]; exact hdt_b _) (by rw [htd1]; exact htd_b _)
  have hspec := winShrinkRight_spec hcpl.win_inv hM htd_b hdt_b
  have hp := physByBase_winShrinkRight hb_pos hcpl.win_inv hM
  dsimp only [winShrinkRight] at htd2 hdt2 hspec hp
  rw [htd1, hdt1] at htd2 hdt2
  have hq_bn_lt : compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem (b_win + n') <
      2 ^ quotientBits U N := by
    rw [hcpl.quot_eq _ hbn_lt]; exact quotAt_lt _ _ _ _ _ _ _
  have hv_bn_lt : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem (b_win + n') <
      2 ^ valBits V := by
    rw [hcpl.val_eq _ hbn_lt]; exact valAt_lt _ _ _ _ _ _ _ _
  refine ⟨hgm2.trans (hgm1.trans hcpl.gm_eq),
    hlm2.trans (hlm1.trans hcpl.lm_eq),
    by rw [htd2, hdt2]; exact hspec.1,
    fun i => by rw [htd2, hmax_eq]; exact hspec.2.1 i,
    fun i => by rw [hdt2, hmax_eq]; exact hspec.2.2 i,
    fun d hd => ?_,
    fun d hd => ?_⟩
  · rw [congrFun hq2 d, hdt2]
    have hd' : d < b_win + (n' + 1) := by omega
    rw [compQuotAt_of_lt s₁.mem hd hd']
    dsimp only [s₁]; rw [hs1_eq, compQuotAt_writeCompVal hw]
    by_cases hdeq : d = d_last
    · subst d
      rw [compQuotAt_writeCompQuot_self s.mem hd_last_lt hq_bn_lt, hp.2.1]
      exact hcpl.quot_eq (b_win + n') hbn_lt
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq, hp.2.2 d hd hdeq]
      exact hcpl.quot_eq d hd'
  · rw [congrFun hv2 d, hdt2]
    have hd' : d < b_win + (n' + 1) := by omega
    rw [compValAt_of_lt s₁.mem hd hd']
    dsimp only [s₁]; rw [hs1_eq]
    by_cases hdeq : d = d_last
    · subst d
      rw [compValAt_writeCompVal_self _ hd_last_lt hv_bn_lt, hp.2.1]
      exact hcpl.val_eq (b_win + n') hbn_lt
    · rw [compValAt_writeCompVal_of_ne hw _ hdeq, compValAt_writeCompQuot hw s.mem,
        hp.2.2 d hd hdeq]
      exact hcpl.val_eq d hd'

/-- Copying `b_win → d_last`, calling `winShrinkLeft`, and writing `(q, v)` to `b_win` transitions
`WindowCoupled` from `(b_win, n' + 1, m)` to `(b_win + 1, n', m)` against updating `(quotAt, valAt)`
at `b_win` to `(q, v)`. -/
private theorem windowCoupled_shrinkLeft_write {metaBase itemBase U V w N b_win n' q v : ℕ}
    {s_fix s_fix' s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hbn : b_win + (n' + 1) ≤ N) (hM : n' + 1 ≤ maxTailItems N)
    (hcpl : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1)) s_fix s)
    (hq_lt : q < 2 ^ quotientBits U N) (hv_lt : v < 2 ^ valBits V)
    (hgm_fix : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hlm_fix : lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
    (hq_fix : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b_win q)
    (hv_fix : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
      Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
        b_win v) :
    let d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
    let s₁ := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last)))
    let s₂ := (Memory.spec 0).clientState s₁
      (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    let s₃ : Memory.State :=
      { mem := writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s₂.mem b_win q)
          b_win v,
        frontier := s₂.frontier }
    WindowCoupled metaBase itemBase U V w N (b_win + 1) n' ((b_win + 1) + n') s_fix' s₃ := by
  intro d_last s₁ s₂ s₃
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have hm_eq : (b_win + 1) + n' = b_win + (n' + 1) := by omega
  have hb_lt : b_win < b_win + (n' + 1) := by omega
  have hd_last_lt : d_last < b_win + (n' + 1) := hcpl.win_inv.dense_lt n' (Nat.lt_succ_self n')
  have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := b_win + (n' + 1)) (itemBase := itemBase) (dst := d_last) hb_lt s
  obtain ⟨hlm_c1, hgm_c1, htd_c1, hdt_c1⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (q := compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win)
    hw hitem hd_last_lt s.mem
  obtain ⟨hlm_c2, hgm_c2, htd_c2, hdt_c2⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (v := compValAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win)
    hw hitem hd_last_lt _
  have hgm1 : compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hgm_c2.trans hgm_c1
  have hlm1 : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hlm_c2.trans hlm_c1
  have htd1 : compTDAt metaBase U w N s₁.mem = compTDAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact htd_c2.trans htd_c1
  have hdt1 : compDTAt metaBase U w N s₁.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [hs1_eq]; exact hdt_c2.trans hdt_c1
  have htd_b : ∀ i, compTDAt metaBase U w N s.mem i < maxTailItems N :=
    fun i => by have := hcpl.td_lt i; rw [hmax_eq] at this; exact this
  have hdt_b : ∀ i, compDTAt metaBase U w N s.mem i < maxTailItems N :=
    fun i => by have := hcpl.dt_lt i; rw [hmax_eq] at this; exact this
  obtain ⟨_, htd2, hdt2, hlm2, hgm2, hq2, hv2, _⟩ :=
    winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + (n' + 1)) (b_win := b_win) (n_win := n')
      hw hitem (by omega) s₁ (by rw [hdt1]; exact hdt_b _) (by rw [htd1]; exact htd_b _)
  rw [htd1, hdt1] at htd2 hdt2
  obtain ⟨hlm3, hgm3, htd3, hdt3⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (q := q) hw hitem hb_lt s₂.mem
  obtain ⟨hlm4, hgm4, htd4, hdt4⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (v := v) hw hitem hb_lt
    (writeCompQuot itemBase U V w N s₂.mem b_win q)
  have hspec := winShrinkLeft_spec hcpl.win_inv hM htd_b hdt_b
  have hp := physByBase_winShrinkLeft hb_pos hcpl.win_inv hM
  dsimp only [winShrinkLeft] at htd2 hdt2 hspec hp
  have hgm_s3 : compGmAt metaBase U w N s₃.mem = compGmAt metaBase U w N s.mem :=
    hgm4.trans (hgm3.trans (hgm2.trans hgm1))
  have hlm_s3 : compLmAt metaBase U w N s₃.mem = compLmAt metaBase U w N s.mem :=
    hlm4.trans (hlm3.trans (hlm2.trans hlm1))
  have htd_s3 := htd4.trans (htd3.trans htd2)
  have hdt_s3 := hdt4.trans (hdt3.trans hdt2)
  have hq_b_lt : compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win <
      2 ^ quotientBits U N := by
    rw [hcpl.quot_eq _ hb_lt]; exact quotAt_lt _ _ _ _ _ _ _
  have hv_b_lt : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win < 2 ^ valBits V := by
    rw [hcpl.val_eq _ hb_lt]; exact valAt_lt _ _ _ _ _ _ _ _
  have hp_ne_bwin : ∀ d < (b_win + 1) + n', d ≠ b_win →
      physByBase N (b_win + 1) (compDTAt metaBase U w N s₃.mem) d ≠ b_win := by
    intro d hd hneb
    rw [hdt_s3]
    have hrng := (physByBase_range_and_inj hb_pos (by omega : (b_win + 1) + n' ≤ N)
      (by omega : n' ≤ maxTailItems N) hspec.1).1 d hd
    rcases hrng with ⟨hlt, hp_eq⟩ | ⟨hge, hlo, _⟩
    · rw [hp_eq]; omega
    · omega
  refine ⟨hgm_s3.trans (hcpl.gm_eq.trans hgm_fix.symm),
    hlm_s3.trans (hcpl.lm_eq.trans hlm_fix.symm),
    by rw [htd_s3, hdt_s3]; exact hspec.1,
    fun i => by rw [htd_s3, hmax_eq]; exact hspec.2.1 i,
    fun i => by rw [hdt_s3, hmax_eq]; exact hspec.2.2 i,
    fun d hd => ?_,
    fun d hd => ?_⟩
  · rw [hm_eq] at hd ⊢
    dsimp only [s₃]
    rw [compQuotAt_writeCompVal hw, hq_fix]
    by_cases hdeb : d = b_win
    · subst d
      rw [compQuotAt_writeCompQuot_self s₂.mem hb_lt hq_lt,
        physByBase_slab _ (Nat.lt_succ_self b_win), Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s₂.mem hdeb,
        Function.update_of_ne (hp_ne_bwin d (by omega) hdeb), congrFun hq2 d, hdt_s3]
      dsimp only [s₁]; rw [hs1_eq, compQuotAt_writeCompVal hw]
      by_cases hdel : d = d_last
      · subst d
        have hgt : b_win < d_last := lt_of_le_of_ne hp.1 (Ne.symm hdeb)
        rw [compQuotAt_writeCompQuot_self s.mem hd_last_lt hq_b_lt, hp.2.2.1 hgt]
        have hp_b : physByBase N b_win (compDTAt metaBase U w N s.mem) b_win =
            N - 1 - compDTAt metaBase U w N s.mem (b_win % maxTailItems N) := by
          unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (Nat.lt_irrefl b_win)]
        rw [← hp_b]; exact hcpl.quot_eq b_win hb_lt
      · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdel, hp.2.2.2 d (by omega) hdeb hdel]
        exact hcpl.quot_eq d hd
  · rw [hm_eq] at hd ⊢
    dsimp only [s₃]
    rw [hv_fix]
    by_cases hdeb : d = b_win
    · subst d
      rw [compValAt_writeCompVal_self _ hb_lt hv_lt,
        physByBase_slab _ (Nat.lt_succ_self b_win), Function.update_self]
    · rw [compValAt_writeCompVal_of_ne hw _ hdeb, compValAt_writeCompQuot hw s₂.mem,
        Function.update_of_ne (hp_ne_bwin d (by omega) hdeb), congrFun hv2 d, hdt_s3]
      dsimp only [s₁]; rw [hs1_eq]
      by_cases hdel : d = d_last
      · subst d
        have hgt : b_win < d_last := lt_of_le_of_ne hp.1 (Ne.symm hdeb)
        rw [compValAt_writeCompVal_self _ hd_last_lt hv_b_lt, hp.2.2.1 hgt]
        have hp_b : physByBase N b_win (compDTAt metaBase U w N s.mem) b_win =
            N - 1 - compDTAt metaBase U w N s.mem (b_win % maxTailItems N) := by
          unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (Nat.lt_irrefl b_win)]
        rw [← hp_b]; exact hcpl.val_eq b_win hb_lt
      · rw [compValAt_writeCompVal_of_ne hw _ hdel, compValAt_writeCompQuot hw s.mem,
          hp.2.2.2 d (by omega) hdeb hdel]
        exact hcpl.val_eq d hd

/-! ## Section 2: Compacted Tail Push and Remove Operations -/

private def writeCompItemGenProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, itemBase), dst), (q_val, v_val)) => do
    writeCompQuotGenProg (((cp, itemBase), dst), q_val)
    writeCompValGenProg (((cp, itemBase), dst), v_val)

private def WriteCompItemPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, itemBase), dst), _qv), s =>
    ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ dst < m_items

private theorem realizesBounded_writeCompItemGen :
    RealizesBounded .exact writeCompItemGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      WriteCompItemPre (fun _ _ => 0) := by
  have hwq := realizesBounded_writeCompQuotGen
  have hwv := realizesBounded_writeCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, dst⟩, ⟨q_val, v_val⟩⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdst⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_writeCompQuotGenProg] at *)
  all_goals exact ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdst⟩

private theorem validProg_writeCompItemGen {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)}
    {s : Memory.State} (h : WriteCompItemPre w d s) :
    ValidProg w 0 s (writeCompItemGenProg d) := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, dst⟩, ⟨q_val, v_val⟩⟩
  obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdst⟩ := h
  dsimp only [writeCompItemGenProg]
  refine validProg_bind_unit
    (validProg_writeCompQuotGen ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdst⟩)
    fun s1 hs1 => ?_
  have hfr1 : itemBase + compactedItemWords U V w N m_items ≤ s1.frontier := by
    rw [hs1, clientState_writeCompQuotGenProg]; exact hfr
  exact validProg_writeCompValGen ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1⟩, hdst⟩

private def compPushBackReadWinProg : CompParams × ℕ → Memory.Prog (ℕ × ℕ)
  | (cp, metaBase) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    pure (n_slabs * cpSlabSize cp, n_tails)

private def compPushBackGrowGMProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), (b_win, n_tails)) => do
    winGrowRightGenProg ((cp, metaBase), (b_win, n_tails))
    let t_new ← compAppendTailGMGenProg ((cp, metaBase), b)
    pure (b_win + t_new)

private def compPushBackWriteReadProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((cp, (metaBase, itemBase)), b), d_new), (q_val, v_val)) => do
    writeCompItemGenProg (((cp, itemBase), d_new), (q_val, v_val))
    let r_idx := 4 + (b + b + b) + 1
    readCompGMGenProg ((cp, metaBase), r_idx)

private def compPushBackTailWriteGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) => do
    let wn ← compPushBackReadWinProg (cp, metaBase)
    let d_new ← compPushBackGrowGMProg (((cp, metaBase), b), wn)
    compPushBackWriteReadProg ((((cp, (metaBase, itemBase)), b), d_new), (q_val, v_val))

@[simp] private theorem memoryCost_compPushBackTailWriteGenProg
    (d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compPushBackTailWriteGenProg d) s = 42 := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  simp [compPushBackTailWriteGenProg, compPushBackReadWinProg, compPushBackGrowGMProg,
    compPushBackWriteReadProg, writeCompItemGenProg]

private def CompPushBackTailWritePre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      q_val < 2 ^ quotientBits U N ∧
      v_val < 2 ^ valBits V

private theorem compPushBackTailWrite_effect {metaBase itemBase U V w N m_cap b q_val v_val : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V) :
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (compPushBackTailWriteGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    (Memory.spec 0).clientResult s (compPushBackTailWriteGenProg d) =
      compGmAt metaBase U w N s.mem (gmRIdx b) + 1 ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro d s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
  have htot_eq : totalSlots N gm₀ = gm₀ 0 * slabSize N + gm₀ 1 := by
    unfold totalSlots; rw [ite_eq_right hb0]
  have hSN_lt : gm₀ 0 * slabSize N + gm₀ 1 < N := by rw [← htot_eq]; exact htot
  have htail₀ := hslot.multi_tail hb_pos
  have hr_lt : gm₀ (gmRIdx b) < tailCapPerBucket N := (hslot.multi_r_bounds hb_pos b hb).1
  have ht_cap : gm₀ 1 < maxTailItems N := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  set b_win := gm₀ 0 * slabSize N
  set n_win := gm₀ 1
  set s₁ := (Memory.spec 0).clientState s
    (winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
  obtain ⟨hf_w1, htd_w1, hdt_w1, hlm_w1, hgm_w1, hq_w1, hv_w1, hout_w1⟩ :=
    winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + n_win) (b_win := b_win) (n_win := n_win)
      henv.pos_w henv.meta_le_item ht_cap s
  set s₂ := (Memory.spec 0).clientState s₁
    (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨hres_app, hfr_app, hgm_app⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + n_win) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb s₁ (by rw [hgm_w1]; exact htail₀)
      (by rw [hgm_w1]; exact hr_lt)
  rw [hgm_w1] at hres_app hgm_app
  set d_new := b_win + n_win
  have hd_new_cap : d_new < m_cap := by dsimp only [d_new, b_win, n_win]; omega
  set s₃ := (Memory.spec 0).clientState s₂
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), d_new), q_val))
  set s₄ := (Memory.spec 0).clientState s₃
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), d_new), v_val))
  have hs'_eq : s' = s₄ := by
    dsimp only [s', d, compPushBackTailWriteGenProg, compPushBackReadWinProg,
      compPushBackGrowGMProg, compPushBackWriteReadProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, hres_app,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readCompGMGenProg]
  have hd_new_lt1 : d_new < b_win + n_win + 1 := Nat.lt_succ_self d_new
  obtain ⟨hlm_q, hgm_q, htd_q, hdt_q⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (m_items := b_win + n_win + 1) (q := q_val)
    henv.pos_w henv.meta_le_item hd_new_lt1 s₂.mem
  obtain ⟨hlm_v, hgm_v, htd_v, hdt_v⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (m_items := b_win + n_win + 1) (v := v_val)
    henv.pos_w henv.meta_le_item hd_new_lt1 s₃.mem
  have hs3_mem : s₃.mem = writeCompQuot itemBase U V w N s₂.mem d_new q_val := by
    dsimp only [s₃]; rw [clientState_writeCompQuotGenProg]
  have hs4_mem : s₄.mem = writeCompVal itemBase U V w N s₃.mem d_new v_val := by
    dsimp only [s₄]; rw [clientState_writeCompValGenProg]
  have hgm4 : compGmAt metaBase U w N s₄.mem = gmAppendTail N gm₀ b := by
    rw [hs4_mem, hgm_v, hs3_mem, hgm_q, hgm_app]
  have hpres_gm := gmAppendTail_preserves_nonTail gm₀ hb hr_lt ht_cap
  have hres_eq : (Memory.spec 0).clientResult s (compPushBackTailWriteGenProg d) =
      gm₀ (gmRIdx b) + 1 := by
    dsimp only [d, compPushBackTailWriteGenProg, compPushBackReadWinProg,
      compPushBackGrowGMProg, compPushBackWriteReadProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      hr_eq, clientResult_readCompGMGenProg hr_idx_lt, hgm4, hpres_gm.2.2.1]
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hs'_eq]
    exact (compOpFrame_tailWindow hf_w1 hout_w1).trans
      ((CompOpFrame.of_gmFrame hfr_app).trans
        ((compOpFrame_writeCompQuot henv.pos_w hd_new_cap s₂).trans
          (compOpFrame_writeCompVal henv.pos_w hd_new_cap s₃)))
  obtain ⟨_, _, _, hl_fix, hgm_fix, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix hq_lt hv_lt
  have hfix_q_v :
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
        Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
          (N - 1 - n_win) q_val ∧
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
        Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
          (N - 1 - n_win) v_val := by
    obtain ⟨hr_fa, _, _, hq_fa, hv_fa, _, _⟩ :=
      appendTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
        (hslot_fix.multi_tail hb_pos) (hslot_fix.multi_r_bounds hb_pos b hb).1
    have hg_lt : N - 1 - n_win < N := by omega
    have hr_fa' : (Memory.spec 0).clientResult s_fix
        (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) = n_win := by
      rw [hr_fa]; exact congrFun hcpl.gm_eq.symm 1
    obtain ⟨_, _, hq_fq, hv_fq, _, _⟩ :=
      writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hq_lt
        ((Memory.spec 0).clientState s_fix
          (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)))
    obtain ⟨_, _, hq_fv, hv_fv, _, _⟩ :=
      writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hv_lt _
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_fix
            (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)))
          (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
            ((0, N - 1 - n_win), q_val)))
        (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, N - 1 - n_win), v_val)) := by
      dsimp only [s_fix', pushBackTailWriteProg, pushBackTailWriteGenProg]
      simp only [appendTailItemGenProg_mk, p_nMaxSubOne_mk, writeQuotGenProg_mk,
        writeValGenProg_mk, readGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, hr_fa',
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readGMProg]
    rw [hs_fix'_eq, hq_fv, hq_fq, hq_fa, hv_fv, hv_fq, hv_fa]
    exact ⟨rfl, rfl⟩
  have hwin0 : WindowInv (maxTailItems N) b_win n_win
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have hwspec := winGrowRight_spec hwin0 (by omega : n_win + 1 ≤ maxTailItems N)
    (fun i => by have := hcpl.td_lt i; rw [hmax_eq] at this; exact this)
    (fun i => by have := hcpl.dt_lt i; rw [hmax_eq] at this; exact this)
  have hp_grow := physByBase_winGrowRight (N := N) (b := b_win) (n := n_win)
    (td := compTDAt metaBase U w N s.mem) (dt := compDTAt metaBase U w N s.mem)
    hb_pos (by omega)
  dsimp only [winGrowRight] at hwspec hp_grow htd_w1 hdt_w1
  set td_new := Function.update (compTDAt metaBase U w N s.mem) n_win
    ((b_win + n_win) % maxTailItems N)
  set dt_new := Function.update (compDTAt metaBase U w N s.mem)
    ((b_win + n_win) % maxTailItems N) n_win
  have htd4' : compTDAt metaBase U w N s₄.mem = td_new := by
    rw [hs4_mem, htd_v, hs3_mem, htd_q, hfr_app.td_eq]; exact htd_w1
  have hdt4' : compDTAt metaBase U w N s₄.mem = dt_new := by
    rw [hs4_mem, hdt_v, hs3_mem, hdt_q, hfr_app.dt_eq]; exact hdt_w1
  have hlm4 : compLmAt metaBase U w N s₄.mem = compLmAt metaBase U w N s.mem := by
    rw [hs4_mem, hlm_v, hs3_mem, hlm_q, hfr_app.lm_eq, hlm_w1]
  refine ⟨hres_eq, hframe, ?_⟩
  rw [hs'_eq]
  unfold FixedCoupled
  have hgm4_0 : compGmAt metaBase U w N s₄.mem 0 = gm₀ 0 := by rw [hgm4, hpres_gm.1]
  have hgm4_1 : compGmAt metaBase U w N s₄.mem 1 = n_win + 1 := by rw [hgm4, hpres_gm.2.1]
  have htot4 : epochTotalSlots N (compGmAt metaBase U w N s₄.mem) = b_win + n_win + 1 := by
    unfold epochTotalSlots; rw [ite_eq_right hb0, hgm4_0, hgm4_1]; dsimp only [b_win]; omega
  refine ⟨hgm4.trans ((congrArg (fun g => gmAppendTail N g b) hcpl.gm_eq).trans hgm_fix.symm),
    hlm4.trans (hcpl.lm_eq.trans hl_fix.symm),
    by simp only [hb0, ↓reduceIte, hgm4_0, hgm4_1, htd4', hdt4']; exact hwspec.1,
    fun i => by rw [htd4', hmax_eq]; exact hwspec.2.1 i,
    fun i => by rw [hdt4', hmax_eq]; exact hwspec.2.2 i,
    fun idx hidx => ?_,
    fun idx hidx => ?_⟩
  · rw [htot4] at hidx ⊢
    rw [hgm4_0, hdt4', hs4_mem, compQuotAt_writeCompVal henv.pos_w, hs3_mem, hfix_q_v.1]
    change compQuotAt itemBase U V w N (b_win + n_win + 1)
        (writeCompQuot itemBase U V w N s₂.mem d_new q_val) idx =
      Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
        (N - 1 - n_win) q_val (physByBase N b_win dt_new idx)
    by_cases heq : idx = d_new
    · subst idx
      rw [compQuotAt_writeCompQuot_self s₂.mem hd_new_lt1 hq_lt, hp_grow.1, Function.update_self]
    · have hlt0 : idx < b_win + n_win := by dsimp only [d_new] at heq; omega
      have hne_g : physByBase N b_win (compDTAt metaBase U w N s.mem) idx ≠ N - 1 - n_win := by
        have hrng := (physByBase_range_and_inj hb_pos (by omega : b_win + n_win ≤ N)
          (by omega : n_win ≤ maxTailItems N) hwin0).1 idx hlt0
        rcases hrng with ⟨hlt_b, hp_eq⟩ | ⟨_, hlo, _⟩ <;> omega
      rw [compQuotAt_writeCompQuot_of_ne henv.pos_w s₂.mem heq,
        compQuotAt_of_lt s₂.mem hidx hlt0, congrFun hfr_app.quot_eq idx,
        congrFun hq_w1 idx, hp_grow.2 idx hlt0, Function.update_of_ne hne_g]
      have hq0 := hcpl.quot_eq idx (by unfold epochTotalSlots; rw [ite_eq_right hb0]; exact hlt0)
      unfold epochTotalSlots at hq0; rw [ite_eq_right hb0] at hq0
      exact hq0
  · rw [htot4] at hidx ⊢
    rw [hgm4_0, hdt4', hs4_mem, hs3_mem, hfix_q_v.2]
    change compValAt itemBase U V w N (b_win + n_win + 1)
        (writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s₂.mem d_new q_val)
          d_new v_val) idx =
      Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
        (N - 1 - n_win) v_val (physByBase N b_win dt_new idx)
    by_cases heq : idx = d_new
    · subst idx
      rw [compValAt_writeCompVal_self _ hd_new_lt1 hv_lt, hp_grow.1, Function.update_self]
    · have hlt0 : idx < b_win + n_win := by dsimp only [d_new] at heq; omega
      have hne_g : physByBase N b_win (compDTAt metaBase U w N s.mem) idx ≠ N - 1 - n_win := by
        have hrng := (physByBase_range_and_inj hb_pos (by omega : b_win + n_win ≤ N)
          (by omega : n_win ≤ maxTailItems N) hwin0).1 idx hlt0
        rcases hrng with ⟨hlt_b, hp_eq⟩ | ⟨_, hlo, _⟩ <;> omega
      rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq,
        compValAt_writeCompQuot henv.pos_w s₂.mem,
        compValAt_of_lt s₂.mem hidx hlt0, congrFun hfr_app.val_eq idx,
        congrFun hv_w1 idx, hp_grow.2 idx hlt0, Function.update_of_ne hne_g]
      have hv0 := hcpl.val_eq idx (by unfold epochTotalSlots; rw [ite_eq_right hb0]; exact hlt0)
      unfold epochTotalSlots at hv0; rw [ite_eq_right hb0] at hv0
      exact hv0

private def CompPushBackReadWinPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      compGmAt metaBase U w N s.mem 0 * slabSize N ≤ N

private theorem realizesBounded_compPushBackReadWin :
    RealizesBounded .exact compPushBackReadWinProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompPushBackReadWinPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, _hb_pos, hb_le⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpSlabSize_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try exact fits_const_of_offCompItems hfit_meta (by omega)
  exact lt_of_le_of_lt (by omega) hU

private def CompPushBackGrowGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (b_win, n_tails)), s =>
    ∃ U V N m_cap itemBase,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      b_win + n_tails ≤ N ∧
      n_tails < maxTailItems N ∧
      b_win + compGmAt metaBase U w N s.mem 1 ≤ N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compPushBackGrowGM :
    RealizesBounded .exact compPushBackGrowGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompPushBackGrowGMPre (fun _ _ => 0) := by
  have hwgr := realizesBounded_winGrowRightGen
  have happ := realizesBounded_compAppendTailGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨b_win, n_tails⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hb_N, ht_cap, hbn_N,
      htail, hr_lt⟩ := h)
  · exact ⟨henv.compMetaEnv, ht_cap, by simp only [cpN_mk]; exact hb_N⟩
  · obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n_tails)
        henv.pos_w henv.meta_le_item ht_cap s
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by rw [hf_w1]; exact henv.meta_le_frontier, hb_pos, hb,
      tailBijection_of_gm_eq hgm_w1 htail, by rw [hgm_w1]; exact hr_lt⟩
  · obtain ⟨_, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n_tails)
        henv.pos_w henv.meta_le_item ht_cap s
    obtain ⟨hres_app, _, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm_w1 htail) (by rw [hgm_w1]; exact hr_lt)
    rw [hres_app, hgm_w1]
    exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U

private def CompPushBackWriteReadPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), d_new), _qv), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      d_new < m_cap

private theorem realizesBounded_compPushBackWriteRead :
    RealizesBounded .exact compPushBackWriteReadProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompPushBackWriteReadPre (fun _ _ => 0) := by
  have hwit := realizesBounded_writeCompItemGen
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, d_new⟩, ⟨q_val, v_val⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hd_cap⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1)
  · exact ⟨m_cap, henv.compItemEnv, hd_cap⟩
  all_goals try {
    change Fits w _
    refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
    unfold gmRIdx at hr_idx_lt; omega
  }
  · refine ⟨(henv.of_mem_eq ?_).compMetaEnv,
      by simp only [cpN_mk]; unfold gmRIdx at hr_idx_lt; omega⟩
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]

private theorem realizesBounded_compPushBackTailWriteGen :
    RealizesBounded .exact compPushBackTailWriteGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompPushBackTailWritePre (fun _ _ => 0) := by
  have hrw := realizesBounded_compPushBackReadWin
  have hgg := realizesBounded_compPushBackGrowGM
  have hwr := realizesBounded_compPushBackWriteRead
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, _s_fix, rfl, henv, hb_pos, _hcpl, hslot, hb, htot, hm_cap,
      _hq_lt, _hv_lt⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have htail₀ := hslot.multi_tail hb_pos
    have hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N :=
      (hslot.multi_r_bounds hb_pos b hb).1
    have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
      ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
    have htot_eq : totalSlots N (compGmAt metaBase U w N s.mem) =
        compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
      unfold totalSlots; rw [ite_eq_right hb0]
    have hrw_s : (Memory.spec 0).clientState s
        (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) = s := by
      unfold StateTransitionSpec.clientState; simp [compPushBackReadWinProg]
    have hrw_r : (Memory.spec 0).clientResult s
        (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) =
        (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1) := by
      dsimp only [compPushBackReadWinProg, cpSlabSize_mk]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, by omega⟩
  · rw [hrw_s, hrw_r]
    exact ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, by omega, ht_cap, by omega,
      htail₀, hr_lt⟩
  · rw [hrw_s, hrw_r]
    obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap)
        (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
        (n_win := compGmAt metaBase U w N s.mem 1)
        henv.pos_w henv.meta_le_item ht_cap s
    obtain ⟨hres_app, hfr_app, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm_w1 htail₀) (by rw [hgm_w1]; exact hr_lt)
    refine ⟨U, V, N, m_cap, rfl, henv.of_mem_eq ?_, hb_pos, hb, ?_⟩
    · dsimp only [compPushBackGrowGMProg]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_pure, hfr_app.frontier_eq, hf_w1]
    · dsimp only [compPushBackGrowGMProg]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
        StateTransitionSpec.clientResult_pure, hgm_w1]
      omega

private theorem validProg_compPushBackTailWriteGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPushBackTailWritePre w d s) :
    ValidProg w 0 s (compPushBackTailWriteGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  obtain ⟨U, V, N, m_cap, _s_fix, rfl, henv, hb_pos, _hcpl, hslot, hb, htot, hm_cap,
    _hq_lt, _hv_lt⟩ := h
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have htail₀ := hslot.multi_tail hb_pos
  have hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N :=
    (hslot.multi_r_bounds hb_pos b hb).1
  have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
    ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  have htot_eq : totalSlots N (compGmAt metaBase U w N s.mem) =
      compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
    unfold totalSlots; rw [ite_eq_right hb0]
  obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
    winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap)
      (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
      (n_win := compGmAt metaBase U w N s.mem 1)
      henv.pos_w henv.meta_le_item ht_cap s
  obtain ⟨hres_app, hfr_app, _⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb _
      (tailBijection_of_gm_eq hgm_w1 htail₀) (by rw [hgm_w1]; exact hr_lt)
  rw [hgm_w1] at hres_app
  have hv_rw : ValidProg w 0 s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) := by
    dsimp only [compPushBackReadWinProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)
  have hrw_s : (Memory.spec 0).clientState s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) = s := by
    unfold StateTransitionSpec.clientState; simp [compPushBackReadWinProg]
  have hrw_r : (Memory.spec 0).clientResult s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) =
      (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1) := by
    dsimp only [compPushBackReadWinProg, cpSlabSize_mk]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl
  dsimp only [compPushBackTailWriteGenProg]
  refine validProg_bind_of_eq hv_rw hrw_r fun s1 hs1 => ?_
  rw [hs1, hrw_s]
  set wn := (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1)
  have hv_gg : ValidProg w 0 s
      (compPushBackGrowGMProg (((mkCompParams U V w N, metaBase), b), wn)) := by
    dsimp only [compPushBackGrowGMProg]
    refine validProg_bind_unit
      (validProg_winGrowRightGen ⟨henv.compMetaEnv,
        by dsimp only [wn]; simp only [cpMaxTail_mk]; exact ht_cap,
        by dsimp only [wn]; simp only [cpN_mk]; omega⟩)
      fun sg1 hsg1 => ?_
    refine validProg_bind
      (validProg_compAppendTailGMGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
        henv.le_pow_V, rfl, by rw [hsg1, hf_w1]; exact henv.meta_le_frontier, hb_pos, hb,
        by rw [hsg1]; exact tailBijection_of_gm_eq hgm_w1 htail₀,
        by rw [hsg1, hgm_w1]; exact hr_lt⟩) ?_
    exact validProg_pure _
  have hgg_r : (Memory.spec 0).clientResult s
      (compPushBackGrowGMProg (((mkCompParams U V w N, metaBase), b), wn)) =
      compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
    dsimp only [compPushBackGrowGMProg]
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_pure]
  refine validProg_bind_of_eq hv_gg hgg_r fun s2 hs2 => ?_
  have hs2_fr : s2.frontier = s.frontier := by
    rw [hs2]; dsimp only [compPushBackGrowGMProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr_app.frontier_eq, hf_w1]
  have henv2 := henv.of_mem_eq (s' := s2) (by rw [hs2_fr])
  dsimp only [compPushBackWriteReadProg]
  rw [hr_eq]
  refine validProg_bind_unit
    (validProg_writeCompItemGen ⟨m_cap, henv2.compItemEnv, by omega⟩)
    fun s3 hs3 => ?_
  have hs3_fr : s3.frontier = s2.frontier := by
    rw [hs3]; dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
  exact validProg_readCompGMGen ⟨(henv2.of_mem_eq (by rw [hs3_fr])).compMetaEnv, hr_idx_lt⟩

private def compRemoveTailReadGM1Prog : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    pure (n_slabs, r_b)

private def compRemoveTailReadGM2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((cp, metaBase), b), (n_slabs, r_b)) => do
    let ptr_del_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1))
    let t_del ← readCompGMGenProg ((cp, metaBase), ptr_del_idx)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    pure ((n_slabs * cpSlabSize cp, n_tails - 1), t_del)

private def compRemoveTailReadTDProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), (t_del, n')) => do
    let c_del ← readCompTDGenProg ((cp, metaBase), t_del)
    let c_last ← readCompTDGenProg ((cp, metaBase), n')
    pure (c_del, c_last)

private def compRemoveTailCalcDenseProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((cp, b_win), (c_del, c_last)) => do
    let d_del ← denseOfCircGenProg (cp, (b_win, c_del))
    let d_last ← denseOfCircGenProg (cp, (b_win, c_last))
    pure (d_del, d_last)

private def compRemoveTailLocateProg : (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), b) => do
    let gm1 ← compRemoveTailReadGM1Prog ((cp, metaBase), b)
    let gm2 ← compRemoveTailReadGM2Prog (((cp, metaBase), b), gm1)
    let cs ← compRemoveTailReadTDProg ((cp, metaBase), (gm2.2, gm2.1.2))
    let ds ← compRemoveTailCalcDenseProg ((cp, gm2.1.1), cs)
    pure (gm2.1, ds)

private def compRemoveTailApplyProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), b), ((b_win, n'), (d_del, d_last))) => do
    copyCompItemGenProg ((cp, itemBase), (d_last, d_del))
    copyCompItemGenProg ((cp, itemBase), (b_win + n', d_last))
    winShrinkRightGenProg ((cp, metaBase), (b_win, n'))
    compRemoveTailGMOnlyGenProg ((cp, metaBase), b)

private def compRemoveLastTailItemGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    let loc ← compRemoveTailLocateProg ((cp, metaBase), b)
    compRemoveTailApplyProg ((((cp, (metaBase, itemBase)), b), loc))

@[simp] private theorem memoryCost_compRemoveLastTailItemGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compRemoveLastTailItemGenProg d) s = 72 := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  simp [compRemoveLastTailItemGenProg, compRemoveTailLocateProg, compRemoveTailReadGM1Prog,
    compRemoveTailReadGM2Prog, compRemoveTailReadTDProg, compRemoveTailCalcDenseProg,
    compRemoveTailApplyProg]

private def CompRemoveLastTailPre (w : ℕ) :
    (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

private def CompRemoveTailApplyPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), ((b_win, n'), (d_del, d_last))), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) ∧
      b_win + n' + 1 ≤ N ∧
      b_win + n' + 1 ≤ m_cap ∧
      d_del < b_win + n' + 1 ∧
      d_last < b_win + n' + 1 ∧
      n' < maxTailItems N ∧
      compDTAt metaBase U w N s.mem ((b_win + n') % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n' < maxTailItems N

private theorem compRemoveTailLocate_spec {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let b_win := gm 0 * slabSize N
    let n' := gm 1 - 1
    let t_del := gm (gmTailPtrIdx N b (gm (gmRIdx b) - 1))
    let d_del := denseOfCirc (maxTailItems N) b_win (td t_del)
    let d_last := denseOfCirc (maxTailItems N) b_win (td n')
    (Memory.spec 0).clientState s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) = s ∧
    (Memory.spec 0).clientResult s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) =
      ((b_win, n'), (d_del, d_last)) ∧
    ValidProg w 0 s (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) := by
  intro gm td b_win n' t_del d_del d_last
  dsimp only [gm, td, b_win, n', t_del, d_del, d_last] at *
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
      compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
    lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have hptr_del_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have ht_del_lt : compGmAt metaBase U w N s.mem
      (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ hr_del_lt
  have ht_del_max : compGmAt metaBase U w N s.mem
      (gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
      maxTailItems N := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
    lt_of_lt_of_le hn'_lt htail.ntails_le
  have hwin0 : WindowInv (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have ht_del_lt' : compGmAt metaBase U w N s.mem
      (gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
      compGmAt metaBase U w N s.mem 1 := ht_del_lt
  have hst : (Memory.spec 0).clientState s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState
    simp [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
  have hres : (Memory.spec 0).clientResult s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1 - 1),
       (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
         (compTDAt metaBase U w N s.mem
           (compGmAt metaBase U w N s.mem
             (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))),
        denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
          (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))) := by
    dsimp only [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
    simp only [bind_assoc, pure_bind, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hptr_del_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg ht_del_max,
      clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompTDGenProg hn'_max, clientState_readCompTDGenProg,
      StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hwin0.td_lt _ ht_del_lt'),
      clientState_denseOfCircGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hwin0.td_lt _ hn'_lt),
      clientState_denseOfCircGenProg]
    rfl
  have hv : ValidProg w 0 s (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
    simp only [bind_assoc, pure_bind, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk, hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h0_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_del_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hptr_del_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h1_lt]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, ht_del_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, hn'_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_denseOfCircGen _ _) ?_
    rw [clientState_denseOfCircGenProg]
    exact validProg_bind (validProg_denseOfCircGen _ _) (validProg_pure _)
  exact ⟨hst, hres, hv⟩

private theorem compRemoveLastTailItem_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let s' := (Memory.spec 0).clientState s
      (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set dt := compDTAt metaBase U w N s.mem
  set b_win := gm 0 * slabSize N
  set n' := gm 1 - 1
  set t_del := gm (gmTailPtrIdx N b (gm (gmRIdx b) - 1))
  set d_del := denseOfCirc (maxTailItems N) b_win (td t_del)
  set d_last := denseOfCirc (maxTailItems N) b_win (td n')
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hn1_eq : n' + 1 = gm 1 := by dsimp only [n']; omega
  have hSN : b_win + (n' + 1) ≤ N := by rw [hn1_eq]; exact hslot.multi_total_le hb_pos
  have hm_le : b_win + (n' + 1) ≤ m_cap := by
    rw [hn1_eq]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; exact hm_cap
  have hM_le : n' + 1 ≤ maxTailItems N := by rw [hn1_eq]; exact htail.ntails_le
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  obtain ⟨hloc_s, hloc_r, _⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
  have hwin0 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc
    simpa only [hn1_eq] using hc
  have ht_del_lt : t_del < n' + 1 := by rw [hn1_eq]; exact htail.ptr_lt b hb _ (by omega)
  have hp_del := physByBase_tail_denseOfCirc hb_pos hwin0.win_inv ht_del_lt
  have hp_last := physByBase_tail_denseOfCirc hb_pos hwin0.win_inv (Nat.lt_succ_self n')
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  obtain ⟨_, _, hq_fix, hv_fix, hl_fix, hgm_fix⟩ :=
    removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
      (hslot_fix.multi_tail hb_pos) (by rw [← hcpl.gm_eq]; exact hr_pos)
  set s_fix_mid : Memory.State := {
    mem := writePacked (0 + offVal U (ghostW w) N (epochHashSpace U (ghostW w) N)) (valBits V)
      (ghostW w)
      (writePacked (0 + offQuot (epochHashSpace U (ghostW w) N)) (quotientBits U N) (ghostW w)
        s_fix.mem (N - 1 - t_del)
        (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')))
      (N - 1 - t_del)
      (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')),
    frontier := s_fix.frontier }
  have hg_del_lt : N - 1 - t_del < N := by omega
  obtain ⟨_, _, hq_m1, hv_m1, hl_m1, hg_m1⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_del_lt (quotAt_lt _ _ _ _ _ _ _) s_fix
  obtain ⟨_, _, hq_m2, hv_m2, hl_m2, hg_m2⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_del_lt (valAt_lt _ _ _ _ _ _ _ _)
      ((Memory.spec 0).clientState s_fix
        (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, N - 1 - t_del),
            quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n'))))
  set s_mid_fix := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_fix
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((0, N - 1 - t_del),
          quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n'))))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      ((0, N - 1 - t_del),
        valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')))
  set s₁ := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_del)))
  have hcpl1 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_mid_fix s₁ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos hSN hM_le hwin0
      hp_last.2.1 hp_del.2.1 hp_last.2.2 hp_del.2.2
      (hg_m2.trans hg_m1) (hl_m2.trans hl_m1) (hq_m2.trans hq_m1)
      (hv_m2.trans (congrArg (fun f => Function.update f _ _) hv_m1))
  have htd1_eq : compTDAt metaBase U w N s₁.mem = td := by
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 s.mem).2.2.1
  have hd_last1 : denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s₁.mem n') =
      d_last := by rw [htd1_eq]
  set s₂ := (Memory.spec 0).clientState s₁
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win + n', d_last)))
  set s₃ := (Memory.spec 0).clientState s₂
    (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
  have hcpl3 : WindowCoupled metaBase itemBase U V w N b_win n' (b_win + n') s_mid_fix s₃ := by
    simpa only [hd_last1] using
      windowCoupled_shrinkRight henv.pos_w henv.meta_le_item hb_pos hM_le hcpl1
  have hgm3_eq : compGmAt metaBase U w N s₃.mem = gm :=
    hcpl3.gm_eq.trans ((hg_m2.trans hg_m1).trans hcpl.gm_eq.symm)
  set s₄ := (Memory.spec 0).clientState s₃
    (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨hfr4, hgm4⟩ := compRemoveTailGMOnlyGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := b_win + n') (b := b)
    henv.pos_w henv.meta_le_item hb_pos hb s₃
    (tailBijection_of_gm_eq hgm3_eq htail) (by rw [hgm3_eq]; exact hr_pos)
  rw [hgm3_eq] at hgm4
  have hs'_eq : s' = s₄ := by
    dsimp only [s', compRemoveLastTailItemGenProg]
    rw [StateTransitionSpec.clientState_bind, hloc_s, hloc_r]
    dsimp only [compRemoveTailApplyProg]
    repeat rw [StateTransitionSpec.clientState_bind]
  have hdt2_eq : compDTAt metaBase U w N s₂.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.2.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₁.mem).2.2.2.trans ?_
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 s.mem).2.2.2
  have htd2_eq : compTDAt metaBase U w N s₂.mem = td := by
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    exact ((writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₁.mem).2.2.1).trans
      htd1_eq
  obtain ⟨hf_w3, _, _, _, _, _, _, hout_w3⟩ :=
    winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item (by omega) s₂
      (by rw [hdt2_eq, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd2_eq, ← hmax_eq]; exact hcpl.td_lt _)
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hs'_eq]
    exact (compOpFrame_copyCompItem henv.pos_w (lt_of_lt_of_le hp_last.2.1 hm_le)
        (lt_of_lt_of_le hp_del.2.1 hm_le) s).trans
      ((compOpFrame_copyCompItem henv.pos_w (by omega) (lt_of_lt_of_le hp_last.2.1 hm_le) s₁).trans
        ((compOpFrame_tailWindow hf_w3 hout_w3).trans (CompOpFrame.of_gmFrame hfr4)))
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  have hgm4_0 : compGmAt metaBase U w N s₄.mem 0 = gm 0 := by rw [hgm4, hpres.1]
  have hgm4_1 : compGmAt metaBase U w N s₄.mem 1 = n' := by rw [hgm4, hpres.2.1]
  have htot4 : epochTotalSlots N (compGmAt metaBase U w N s₄.mem) = b_win + n' := by
    unfold epochTotalSlots; rw [ite_eq_right hb0, hgm4_0, hgm4_1]
  have hgm_fix_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = gm :=
    hcpl.gm_eq.symm
  refine ⟨hframe, ?_⟩
  rw [hs'_eq]
  unfold FixedCoupled
  refine ⟨hgm4.trans (by rw [← hgm_fix_eq]; exact hgm_fix.symm),
    hfr4.lm_eq.trans (hcpl3.lm_eq.trans ((hl_m2.trans hl_m1).trans hl_fix.symm)),
    by simp only [hb0, ↓reduceIte]; rw [hgm4_0, hgm4_1, hfr4.td_eq, hfr4.dt_eq]
       exact hcpl3.win_inv,
    fun i => by rw [hfr4.td_eq]; exact hcpl3.td_lt i,
    fun i => by rw [hfr4.dt_eq]; exact hcpl3.dt_lt i,
    fun idx hidx => ?_,
    fun idx hidx => ?_⟩
  · rw [htot4] at hidx ⊢
    rw [congrFun hfr4.quot_eq idx, hgm4_0, hfr4.dt_eq, hcpl3.quot_eq idx hidx,
      hq_m2, hq_m1, hq_fix, hgm_fix_eq]
  · rw [htot4] at hidx ⊢
    rw [congrFun hfr4.val_eq idx, hgm4_0, hfr4.dt_eq, hcpl3.val_eq idx hidx,
      hv_m2, hv_m1, hv_fix, hgm_fix_eq]

private def CompRemoveTailLocatePre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N m_cap itemBase s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)

private def CompRemoveTailReadGM1Pre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N

private theorem realizesBounded_compRemoveTailReadGM1 :
    RealizesBounded .exact compRemoveTailReadGM1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailReadGM1Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at hr_idx_lt; omega)
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmRIdx at hr_idx_lt; omega

private def CompRemoveTailReadGM2Pre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (n_slabs, r_b)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      n_slabs * slabSize N ≤ N ∧
      1 ≤ r_b ∧ r_b ≤ tailCapPerBucket N ∧
      1 ≤ compGmAt metaBase U w N s.mem 1

private theorem realizesBounded_compRemoveTailReadGM2 :
    RealizesBounded .exact compRemoveTailReadGM2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompRemoveTailReadGM2Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨n_slabs, r_b⟩⟩
    try dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hns_le, hr_pos, hr_le,
      hnt_pos⟩ := h
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + (r_b - 1)) < globalMetaLen N :=
      gmTailPtrIdx_lt hb_pos hb (by omega)
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by omega)
      | exact Fits.of_le hU (by omega)
  }
  all_goals omega

private def CompRemoveTailReadTDPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (t_del, n')), s =>
    CompMetaEnv w cp metaBase s ∧ t_del < cpMaxTail cp ∧ n' < cpMaxTail cp

private theorem realizesBounded_compRemoveTailReadTD :
    RealizesBounded .exact compRemoveTailReadTDProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailReadTDPre (fun _ _ => 0) := by
  have hrtd := realizesBounded_readCompTDGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨t_del, n'⟩⟩
    dsimp only at *
    obtain ⟨hmeta, ht, hn'⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompTDGenProg] at *)
  · exact ⟨hmeta, ht⟩
  · exact ⟨hmeta, hn'⟩

private def CompRemoveTailCalcDensePre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, b_win), (c_del, c_last)), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      b_win ≤ N ∧
      (0 < maxTailItems N →
        c_del < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_del ≤ N ∧
        c_last < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_last ≤ N)

private theorem realizesBounded_compRemoveTailCalcDense :
    RealizesBounded .exact compRemoveTailCalcDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailCalcDensePre (fun _ _ => 0) := by
  have hdoc := realizesBounded_denseOfCircGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, b_win⟩, ⟨c_del, c_last⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le, hcond⟩ := h)
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).1, (hcond hb).2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.1, (hcond hb).2.2.2⟩⟩

private theorem realizesBounded_compRemoveTailLocate :
    RealizesBounded .exact compRemoveTailLocateProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompRemoveTailLocatePre (fun _ _ => 0) := by
  have hg1 := realizesBounded_compRemoveTailReadGM1
  have hg2 := realizesBounded_compRemoveTailReadGM2
  have htd := realizesBounded_compRemoveTailReadTD
  have hdc := realizesBounded_compRemoveTailCalcDense
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have htail := hslot.multi_tail hb_pos
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hSN := hslot.multi_total_le hb_pos
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
    have hptr_del_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
    have ht_del_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ hr_del_lt
    have ht_del_max : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        maxTailItems N := lt_of_lt_of_le ht_del_lt htail.ntails_le
    have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
    have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
      lt_of_lt_of_le hn'_lt htail.ntails_le
    have hwin0 : WindowInv (maxTailItems N)
        (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compGmAt metaBase U w N s.mem 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
      have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
    have hg1_s : (Memory.spec 0).clientState s
        (compRemoveTailReadGM1Prog ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGM1Prog]
    have hg1_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadGM1Prog ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)) := by
      dsimp only [compRemoveTailReadGM1Prog]; rw [hr_eq]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg]; rfl
    have hg2_s : (Memory.spec 0).clientState s
        (compRemoveTailReadGM2Prog (((mkCompParams U V w N, metaBase), b),
          (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)))) = s := by
      unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGM2Prog]
    have hg2_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadGM2Prog (((mkCompParams U V w N, metaBase), b),
          (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)))) =
        ((compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1 - 1),
         compGmAt metaBase U w N s.mem
           (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) := by
      dsimp only [compRemoveTailReadGM2Prog, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hptr_del_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, hb⟩
  · rw [hg1_s, hg1_r]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, hb, by omega, hr_pos, htail.r_le b hb, by omega⟩
  · rw [hg1_s, hg1_r, hg2_s, hg2_r]
    exact ⟨henv.compMetaEnv, by simp only [cpMaxTail_mk]; exact ht_del_max,
      by simp only [cpMaxTail_mk]; exact hn'_max⟩
  · rw [hg1_s, hg1_r, hg2_s, hg2_r]
    have htd_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadTDProg ((mkCompParams U V w N, metaBase),
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)),
           compGmAt metaBase U w N s.mem 1 - 1))) =
        (compTDAt metaBase U w N s.mem
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))),
         compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)) := by
      dsimp only [compRemoveTailReadTDProg]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg ht_del_max,
        clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompTDGenProg hn'_max, clientState_readCompTDGenProg]; rfl
    rw [htd_r]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by omega, fun _ => ⟨hwin0.td_lt _ ht_del_lt,
        le_trans (le_of_lt (hwin0.dense_lt _ ht_del_lt)) hSN,
        hwin0.td_lt _ hn'_lt,
        le_trans (le_of_lt (hwin0.dense_lt _ hn'_lt)) hSN⟩⟩

private theorem realizesBounded_compRemoveTailApply :
    RealizesBounded .exact compRemoveTailApplyProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompRemoveTailApplyPre (fun _ _ => 0) := by
  have hcpy := realizesBounded_copyCompItemGen
  have hwsr := realizesBounded_winShrinkRightGen
  have hrm := realizesBounded_compRemoveTailGMOnlyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨b_win, n'⟩, ⟨d_del, d_last⟩⟩⟩
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, htail, hr_pos, hbn_N, hbn_cap,
      hd_del, hd_last, hn'_max, hdt_lt, htd_lt⟩ := h
    dsimp only at *
    set s1 := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_del)))
    set s2 := (Memory.spec 0).clientState s1
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win + n', d_last)))
    set s3 := (Memory.spec 0).clientState s2
      (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_del) (by omega : d_last < m_cap) s
    have hs2_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_last) (by omega : b_win + n' < m_cap) s1
    have hgm2 : compGmAt metaBase U w N s2.mem = compGmAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.1.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.1.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.1.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.1
    have htd2 : compTDAt metaBase U w N s2.mem = compTDAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.1.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.2.1.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.1.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.2.1
    have hdt2 : compDTAt metaBase U w N s2.mem = compDTAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.2.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.2.2.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.2.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.2.2)
  · exact ⟨m_cap, henv.compItemEnv, by omega, by omega⟩
  · exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U
  · refine ⟨m_cap, (henv.of_mem_eq ?_).compItemEnv, by omega, by omega⟩
    dsimp only [s1]; rw [hs1_eq]
  · refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hn'_max, by omega, by rw [hdt2]; exact hdt_lt, by rw [htd2]; exact htd_lt⟩
    dsimp only [s2]; rw [hs2_eq]; dsimp only [s1]; rw [hs1_eq]
    exact henv.meta_le_frontier
  · obtain ⟨hf3, _, _, _, hgm3, _, _, _⟩ :=
      winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s2
        (by rw [hdt2]; exact hdt_lt) (by rw [htd2]; exact htd_lt)
    have hgm3' : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem :=
      hgm3.trans hgm2
    change CompRemoveTailGMOnlyPre w ((mkCompParams U V w N, metaBase), b) s3
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hb, tailBijection_of_gm_eq hgm3' htail, by rw [hgm3']; exact hr_pos⟩
    rw [hf3]; dsimp only [s2]; rw [hs2_eq]; dsimp only [s1]; rw [hs1_eq]
    exact henv.meta_le_frontier

private theorem realizesBounded_compRemoveLastTailItemGen :
    RealizesBounded .exact compRemoveLastTailItemGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompRemoveLastTailPre (fun _ _ => 0) := by
  have hloc := realizesBounded_compRemoveTailLocate
  have happ := realizesBounded_compRemoveTailApply
  realize
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, _⟩ := h
    exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos⟩
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
    dsimp only at *
    obtain ⟨hloc_s, hloc_r, _⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
    rw [hloc_s, hloc_r]
    dsimp only
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have htail := hslot.multi_tail hb_pos
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hSN := hslot.multi_total_le hb_pos
    have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
    have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
    have hwin0 : WindowInv (maxTailItems N)
        (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compGmAt metaBase U w N s.mem 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
      have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
    have ht_del_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ (by omega)
    have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
    unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
    refine ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, htail, hr_pos, by omega, by omega, ?_, ?_,
      lt_of_lt_of_le hn'_lt htail.ntails_le,
      by rw [← hmax_eq]; exact hcpl.dt_lt _,
      by rw [← hmax_eq]; exact hcpl.td_lt _⟩
    · have := hwin0.dense_lt _ ht_del_lt; omega
    · have := hwin0.dense_lt _ hn'_lt; omega

private theorem validProg_compRemoveLastTailItemGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompRemoveLastTailPre w d s) :
    ValidProg w 0 s (compRemoveLastTailItemGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
  obtain ⟨hloc_s, hloc_r, hloc_v⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
  dsimp only [compRemoveLastTailItemGenProg]
  refine validProg_bind hloc_v ?_
  rw [hloc_s, hloc_r]
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have hwin0 : WindowInv (maxTailItems N)
      (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have ht_del_lt := htail.ptr_lt b hb (compGmAt metaBase U w N s.mem (gmRIdx b) - 1) (by omega)
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have hd_del_lt := hwin0.dense_lt _ ht_del_lt
  have hd_last_lt := hwin0.dense_lt _ hn'_lt
  unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
  dsimp only [compRemoveTailApplyProg]
  refine validProg_bind
    (validProg_copyCompItemGen ⟨m_cap, henv.compItemEnv, by omega, by omega⟩) ?_
  set s1 := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase),
      (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)),
       denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))))))
  have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase)
    (src := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))
    (dst := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))))
    (by omega) s
  have henv1 := henv.of_mem_eq (s' := s1) (by dsimp only [s1]; rw [hs1_eq])
  refine validProg_bind
    (validProg_copyCompItemGen ⟨m_cap, henv1.compItemEnv, by omega, by omega⟩) ?_
  set s2 := (Memory.spec 0).clientState s1
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase),
      (compGmAt metaBase U w N s.mem 0 * slabSize N + (compGmAt metaBase U w N s.mem 1 - 1),
       denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))))
  have hs2_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase)
    (src := compGmAt metaBase U w N s.mem 0 * slabSize N + (compGmAt metaBase U w N s.mem 1 - 1))
    (dst := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))
    (by omega) s1
  have henv2 := henv1.of_mem_eq (s' := s2) (by dsimp only [s2]; rw [hs2_eq])
  have hgm2 : compGmAt metaBase U w N s2.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.1.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.1.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.1
  have htd2 : compTDAt metaBase U w N s2.mem = compTDAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.1.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.2.1.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.2.1
  have hdt2 : compDTAt metaBase U w N s2.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.2.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.2.2.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.2.2
  have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
    lt_of_lt_of_le hn'_lt htail.ntails_le
  have hSN := hslot.multi_total_le hb_pos
  refine validProg_bind (validProg_winShrinkRightGen ⟨U, V, N, henv2.pos_w, henv2.pos_N,
    henv2.le_U, henv2.lt_pow_U, henv2.le_pow_V, rfl, henv2.meta_le_frontier,
    hn'_max, by omega,
    by rw [hdt2, ← hmax_eq]; exact hcpl.dt_lt _,
    by rw [htd2, ← hmax_eq]; exact hcpl.td_lt _⟩) ?_
  obtain ⟨hf3, _, _, _, hgm3, _, _, _⟩ :=
    winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap)
      (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
      (n_win := compGmAt metaBase U w N s.mem 1 - 1)
      henv.pos_w henv.meta_le_item hn'_max s2
      (by rw [hdt2, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd2, ← hmax_eq]; exact hcpl.td_lt _)
  have hgm3' := hgm3.trans hgm2
  exact validProg_compRemoveTailGMOnlyGen ⟨U, V, N, henv2.pos_w, henv2.pos_N, henv2.le_U,
    henv2.lt_pow_U, henv2.le_pow_V, rfl, by rw [hf3]; exact henv2.meta_le_frontier, hb_pos, hb,
    tailBijection_of_gm_eq hgm3' htail, by rw [hgm3']; exact hr_pos⟩

/-! ## Section 3: Compacted `K`-Step Slab Promotion (`compPromoteSlabGenProg`) -/

private def compPromoteReadPtrsProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), k) => do
    let u := cpSlabSizeSubOne cp - k
    let r_top := cpSlabSize cp + u
    let ptr_u_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + u)
    let ptr_top_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + r_top)
    let t_u ← readCompGMGenProg ((cp, metaBase), ptr_u_idx)
    let t_top ← readCompGMGenProg ((cp, metaBase), ptr_top_idx)
    pure (t_u, t_top)

private def compPromoteReadCountsProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), k) => do
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    pure (p_new * cpSlabSize cp + k, n_tails - 1)

private def compPromoteReadGMProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | (((cp, metaBase), b), k) => do
    let ts ← compPromoteReadPtrsProg (((cp, metaBase), b), k)
    let wn ← compPromoteReadCountsProg ((cp, metaBase), k)
    pure (wn, ts)

private def compPromoteReadTDProg :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((cp, metaBase), (n', (t_u, t_top))) => do
    let c_u ← readCompTDGenProg ((cp, metaBase), t_u)
    let c_top ← readCompTDGenProg ((cp, metaBase), t_top)
    let c_last ← readCompTDGenProg ((cp, metaBase), n')
    pure (c_u, (c_top, c_last))

private def compPromoteCalcDenseProg :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((cp, b_win), (c_u, (c_top, c_last))) => do
    let d_u ← denseOfCircGenProg (cp, (b_win, c_u))
    let d_top ← denseOfCircGenProg (cp, (b_win, c_top))
    let d_last ← denseOfCircGenProg (cp, (b_win, c_last))
    pure (d_u, (d_top, d_last))

private def compPromoteReadDenseProg :
    (CompParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((cp, metaBase), ((b_win, n'), (t_u, t_top))) => do
    let cs ← compPromoteReadTDProg ((cp, metaBase), (n', (t_u, t_top)))
    compPromoteCalcDenseProg ((cp, b_win), cs)

private def compPromoteMoveItemsProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × ℕ)
  | (((cp, itemBase), b_win), (d_u, (d_top, d_last))) => do
    let q_u ← readCompQuotGenProg ((cp, itemBase), d_u)
    let v_u ← readCompValGenProg ((cp, itemBase), d_u)
    copyCompItemGenProg ((cp, itemBase), (d_top, d_u))
    copyCompItemGenProg ((cp, itemBase), (d_last, d_top))
    copyCompItemGenProg ((cp, itemBase), (b_win, d_last))
    pure (q_u, v_u)

private def compPromoteFinishStepProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), (b_win, n')), (q_u, v_u)) => do
    winShrinkLeftGenProg ((cp, metaBase), (b_win, n'))
    writeCompQuotGenProg (((cp, itemBase), b_win), q_u)
    writeCompValGenProg (((cp, itemBase), b_win), v_u)
    compRemoveTailGMOnlyGenProg ((cp, metaBase), b)

private def compPromoteStepGenProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, (metaBase, itemBase)), b), k) => do
    let gmInfo ← compPromoteReadGMProg (((cp, metaBase), b), k)
    let ds ← compPromoteReadDenseProg ((cp, metaBase), gmInfo)
    let qv ← compPromoteMoveItemsProg (((cp, itemBase), gmInfo.1.1), ds)
    compPromoteFinishStepProg (((((cp, (metaBase, itemBase)), b), gmInfo.1), qv))
    pure (k + 1)

@[simp] private theorem memoryCost_compPromoteStepGenProg
    (x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compPromoteStepGenProg x) s = 98 := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  simp [compPromoteStepGenProg, compPromoteReadGMProg, compPromoteReadPtrsProg,
    compPromoteReadCountsProg, compPromoteReadDenseProg, compPromoteReadTDProg,
    compPromoteCalcDenseProg, compPromoteMoveItemsProg, compPromoteFinishStepProg]

private theorem one_le_memoryCost_compPromoteStepGenProg
    (x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (compPromoteStepGenProg x) s := by
  rw [memoryCost_compPromoteStepGenProg]; omega

private def CompPromoteStepPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), k), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix ∧
      WindowCoupled metaBase itemBase U V w N
        (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
        (compGmAt metaBase U w N s.mem 1)
        ((compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1)
        s_fix s ∧
      (compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1 ≤ m_cap

private def CompPromoteReadDensePre (w : ℕ) :
    (CompParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | ((cp, metaBase), ((b_win, n'), (t_u, t_top))), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b_win + (n' + 1) ≤ N ∧
      t_u < n' + 1 ∧ t_top < n' + 1 ∧ n' + 1 ≤ maxTailItems N ∧
      WindowInv (maxTailItems N) b_win (n' + 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem)

private def CompPromoteMoveItemsPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, itemBase), b_win), (d_u, (d_top, d_last))), s =>
    ∃ m_cap,
      CompItemEnv w cp itemBase m_cap s ∧
      b_win < m_cap ∧ d_u < m_cap ∧ d_top < m_cap ∧ d_last < m_cap

private def CompPromoteFinishStepPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), (b_win, n')), (_q_u, _v_u)), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      b_win ≤ N ∧
      b_win < m_cap ∧
      n' < maxTailItems N ∧
      compDTAt metaBase U w N s.mem (b_win % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n' < maxTailItems N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)

private theorem compPromoteStep_read_spec {metaBase itemBase U V w N m_cap b k : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hstep : PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix)
    (hcpl : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1)
      s_fix s) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let u := (slabSize N - 1) - k
    let r_top := slabSize N + u
    let b_win := gm 0 * slabSize N + k
    let n' := gm 1 - 1
    let t_u := gm (gmTailPtrIdx N b u)
    let t_top := gm (gmTailPtrIdx N b r_top)
    let d_u := denseOfCirc (maxTailItems N) b_win (td t_u)
    let d_top := denseOfCirc (maxTailItems N) b_win (td t_top)
    let d_last := denseOfCirc (maxTailItems N) b_win (td n')
    (Memory.spec 0).clientState s
      (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) = s ∧
    (Memory.spec 0).clientResult s
      (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) =
      ((b_win, n'), (t_u, t_top)) ∧
    (Memory.spec 0).clientState s
      (compPromoteReadDenseProg ((mkCompParams U V w N, metaBase), ((b_win, n'), (t_u, t_top)))) =
      s ∧
    (Memory.spec 0).clientResult s
      (compPromoteReadDenseProg ((mkCompParams U V w N, metaBase), ((b_win, n'), (t_u, t_top)))) =
      (d_u, (d_top, d_last)) ∧
    ValidProg w 0 s (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) ∧
    ValidProg w 0 s
      (compPromoteReadDenseProg
        ((mkCompParams U V w N, metaBase), ((b_win, n'), (t_u, t_top)))) := by
  intro gm td u r_top b_win n' t_u t_top d_u d_top d_last
  dsimp only [gm, td, u, r_top, b_win, n', t_u, t_top, d_u, d_top, d_last] at *
  rcases hstep with ⟨hb, hk_lt, htail_fix, _, hrb_fix, htot_fix⟩
  have htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
    (congrFun hcpl.gm_eq (gmRIdx b)).trans hrb_fix
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hTcap : tailCapPerBucket N = 2 * slabSize N := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hu_lt_r : (slabSize N - 1) - k < compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  have hr_top_lt_r : slabSize N + ((slabSize N - 1) - k) <
      compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  have hu_cap : (slabSize N - 1) - k < tailCapPerBucket N := by omega
  have hr_top_cap : slabSize N + ((slabSize N - 1) - k) < tailCapPerBucket N := by omega
  have hptr_u_lt : gmTailPtrBase N + (b * tailCapPerBucket N + ((slabSize N - 1) - k)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hu_cap
  have hptr_top_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (slabSize N + ((slabSize N - 1) - k))) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_top_cap
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have htu_lt := htail.ptr_lt b hb _ hu_lt_r
  have httop_lt := htail.ptr_lt b hb _ hr_top_lt_r
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have htu_max := lt_of_lt_of_le htu_lt htail.ntails_le
  have httop_max := lt_of_lt_of_le httop_lt htail.ntails_le
  have hn'_max := lt_of_lt_of_le hn'_lt htail.ntails_le
  have hst1 : (Memory.spec 0).clientState s
      (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) = s := by
    unfold StateTransitionSpec.clientState
    simp [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
  have hres1 : (Memory.spec 0).clientResult s
      (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) =
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + k, compGmAt metaBase U w N s.mem 1 - 1),
       (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k)),
        compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k))))) := by
    dsimp only [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
    simp only [bind_assoc, pure_bind, cpSlabSizeSubOne_mk, cpSlabSize_mk, cpGmTailPtrBase_mk,
      cpTailCap_mk]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hptr_u_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hptr_top_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]
    rfl
  have hst2 : (Memory.spec 0).clientState s
      (compPromoteReadDenseProg ((mkCompParams U V w N, metaBase),
        ((compGmAt metaBase U w N s.mem 0 * slabSize N + k, compGmAt metaBase U w N s.mem 1 - 1),
         (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k)),
          compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k))))))) = s := by
    unfold StateTransitionSpec.clientState
    simp [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
  have hres2 : (Memory.spec 0).clientResult s
      (compPromoteReadDenseProg ((mkCompParams U V w N, metaBase),
        ((compGmAt metaBase U w N s.mem 0 * slabSize N + k, compGmAt metaBase U w N s.mem 1 - 1),
         (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k)),
          compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k))))))) =
      (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
         (compTDAt metaBase U w N s.mem
           (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k)))),
       (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
          (compTDAt metaBase U w N s.mem
            (compGmAt metaBase U w N s.mem
              (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k))))),
        denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
          (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))) := by
    dsimp only [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
    simp only [bind_assoc, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg htu_max,
      clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompTDGenProg httop_max, clientState_readCompTDGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg hn'_max,
      clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ htu_lt),
      clientState_denseOfCircGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ httop_lt),
      clientState_denseOfCircGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ hn'_lt),
      clientState_denseOfCircGenProg]
    rfl
  have hv1 : ValidProg w 0 s
      (compPromoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) := by
    dsimp only [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
    simp only [bind_assoc, pure_bind, cpSlabSizeSubOne_mk, cpSlabSize_mk, cpGmTailPtrBase_mk,
      cpTailCap_mk]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_u_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_top_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)
  have hv2 : ValidProg w 0 s
      (compPromoteReadDenseProg ((mkCompParams U V w N, metaBase),
        ((b_win, n'), (t_u, t_top)))) := by
    dsimp only [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
    simp only [bind_assoc, pure_bind]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, htu_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, httop_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, hn'_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_denseOfCircGen _ _) ?_
    rw [clientState_denseOfCircGenProg]
    refine validProg_bind (validProg_denseOfCircGen _ _) ?_
    rw [clientState_denseOfCircGenProg]
    exact validProg_bind (validProg_denseOfCircGen _ _) (validProg_pure _)
  exact ⟨hst1, hres1, hst2, hres2, hv1, hv2⟩

private theorem compPromoteStep_effect {metaBase itemBase U V w N m_cap b k : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hstep : PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix)
    (hcpl : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1)
      s_fix s)
    (hm_cap : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap) :
    let d := (((mkCompParams U V w N, (metaBase, itemBase)), b), k)
    let s' := (Memory.spec 0).clientState s (compPromoteStepGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), k))
    (Memory.spec 0).clientResult s (compPromoteStepGenProg d) = k + 1 ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1))
      (compGmAt metaBase U w N s'.mem 1)
      ((compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1)) +
        compGmAt metaBase U w N s'.mem 1)
      s_fix' s' ∧
    (compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1)) +
      compGmAt metaBase U w N s'.mem 1 ≤ m_cap := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, _⟩ :=
    compPromoteStep_read_spec henv hb_pos hstep hcpl
  rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set u := (slabSize N - 1) - k
  set r_top := slabSize N + u
  set b_win := gm 0 * slabSize N + k
  set n' := gm 1 - 1
  set t_u := gm (gmTailPtrIdx N b u)
  set t_top := gm (gmTailPtrIdx N b r_top)
  set d_u := denseOfCirc (maxTailItems N) b_win (td t_u)
  set d_top := denseOfCirc (maxTailItems N) b_win (td t_top)
  set d_last := denseOfCirc (maxTailItems N) b_win (td n')
  have hgm_fix_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = gm :=
    hcpl.gm_eq.symm
  have htail : TailBijection N gm (fun b' => gm (gmRIdx b')) (gm 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hrb : gm (gmRIdx b) = 2 * slabSize N - k := by
    dsimp only [gm]; rw [hcpl.gm_eq]; exact hrb_fix
  have htot_N : b_win + gm 1 ≤ N := by
    dsimp only [b_win, gm]; rw [hcpl.gm_eq]; exact htot_fix
  have hr_le_nt : gm (gmRIdx b) ≤ gm 1 := r_le_ntails_of_tailBijection htail hb
  have hn1_eq : n' + 1 = gm 1 := by dsimp only [n']; omega
  have hr_top_eq : r_top = gm (gmRIdx b) - 1 := by dsimp only [r_top, u]; omega
  have htu_lt : t_u < n' + 1 := by rw [hn1_eq]; exact htail.ptr_lt b hb u (by dsimp only [u]; omega)
  have httop_lt : t_top < n' + 1 := by
    rw [hn1_eq]; exact htail.ptr_lt b hb r_top (by dsimp only [r_top, u]; omega)
  have hM_le : n' + 1 ≤ maxTailItems N := by rw [hn1_eq]; exact htail.ntails_le
  have hcpl0 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_fix s := by simpa only [hn1_eq] using hcpl
  have hp_u := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv htu_lt
  have hp_top := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv httop_lt
  have hp_last := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv (Nat.lt_succ_self n')
  set qA := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  set vA := valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  set g_u := N - 1 - t_u
  set g_top := N - 1 - t_top
  set g_last := N - 1 - n'
  have hqu_eq : compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem d_u = qA g_u := by
    rw [hcpl0.quot_eq d_u hp_u.2.1, hp_u.2.2]
  have hvu_eq : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem d_u = vA g_u := by
    rw [hcpl0.val_eq d_u hp_u.2.1, hp_u.2.2]
  have hdu_cap : d_u < m_cap := lt_of_lt_of_le hp_u.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hdtop_cap : d_top < m_cap := lt_of_lt_of_le hp_top.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hdlast_cap : d_last < m_cap := lt_of_lt_of_le hp_last.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hbwin_cap : b_win < m_cap := by omega
  set s₁ := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u)))
  set s₂ := (Memory.spec 0).clientState s₁
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top)))
  set s₃ := (Memory.spec 0).clientState s₂
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last)))
  have hmv_res : (Memory.spec 0).clientResult s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last)))) = (qA g_u, vA g_u) := by
    dsimp only [compPromoteMoveItemsProg]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompQuotGenProg hp_u.2.1,
      clientState_readCompQuotGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompValGenProg hp_u.2.1, clientState_readCompValGenProg,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure,
      hqu_eq, hvu_eq]
  have hmv_st : (Memory.spec 0).clientState s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last)))) = s₃ := by
    dsimp only [compPromoteMoveItemsProg]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg,
      StateTransitionSpec.clientState_bind, clientState_readCompValGenProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  set s₄ := (Memory.spec 0).clientState s₃
    (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
  set s₅ := (Memory.spec 0).clientState s₄
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), b_win), qA g_u))
  set s₆ := (Memory.spec 0).clientState s₅
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), b_win), vA g_u))
  set s₇ := (Memory.spec 0).clientState s₆
    (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
  have hres_all : (Memory.spec 0).clientResult s (compPromoteStepGenProg d) = k + 1 := by
    dsimp only [d, compPromoteStepGenProg]
    rw [StateTransitionSpec.clientResult_bind, hst_gm, hres_gm,
      StateTransitionSpec.clientResult_bind, hst_ds, hres_ds,
      StateTransitionSpec.clientResult_bind]
    dsimp only [compPromoteFinishStepProg]
    repeat rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hst_all : s' = s₇ := by
    dsimp only [s', d, compPromoteStepGenProg]
    rw [StateTransitionSpec.clientState_bind, hst_gm, hres_gm,
      StateTransitionSpec.clientState_bind, hst_ds, hres_ds,
      StateTransitionSpec.clientState_bind, hmv_st, hmv_res,
      StateTransitionSpec.clientState_bind]
    dsimp only [compPromoteFinishStepProg]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [StateTransitionSpec.clientState_pure]
  have hgu_lt : g_u < N := by dsimp only [g_u]; omega
  have hgtop_lt : g_top < N := by dsimp only [g_top]; omega
  have hbwin_lt_N : b_win < N := by omega
  set sf₁ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_fix
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_u), qA g_top)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_u), vA g_top))
  obtain ⟨_, _, hq_f1a, hv_f1a, hl_f1a, hg_f1a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgu_lt (quotAt_lt _ _ _ _ _ _ _) s_fix
  obtain ⟨_, _, hq_f1b, hv_f1b, hl_f1b, hg_f1b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgu_lt (valAt_lt _ _ _ _ _ _ _ _) _
  have hcpl1 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      sf₁ s₁ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos (by rw [hn1_eq]; exact htot_N)
      hM_le hcpl0 hp_top.2.1 hp_u.2.1 hp_top.2.2 hp_u.2.2
      (hg_f1b.trans hg_f1a) (hl_f1b.trans hl_f1a) (hq_f1b.trans hq_f1a)
      (hv_f1b.trans (congrArg (fun f => Function.update f _ _) hv_f1a))
  set qA₁ := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem
  set vA₁ := valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem
  set sf₂ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState sf₁
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_top), qA₁ g_last)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_top), vA₁ g_last))
  obtain ⟨_, _, hq_f2a, hv_f2a, hl_f2a, hg_f2a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgtop_lt (quotAt_lt _ _ _ _ _ _ _) sf₁
  obtain ⟨_, _, hq_f2b, hv_f2b, hl_f2b, hg_f2b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgtop_lt (valAt_lt _ _ _ _ _ _ _ _) _
  have hdt1_eq : compDTAt metaBase U w N s₁.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_top.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_u.2.1 _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_u.2.1 s.mem).2.2.2
  have hcpl2 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      sf₂ s₂ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos (by rw [hn1_eq]; exact htot_N)
      hM_le hcpl1 hp_last.2.1 hp_top.2.1
      (by rw [hdt1_eq]; exact hp_last.2.2) (by rw [hdt1_eq]; exact hp_top.2.2)
      (hg_f2b.trans hg_f2a) (hl_f2b.trans hl_f2a) (hq_f2b.trans hq_f2a)
      (hv_f2b.trans (congrArg (fun f => Function.update f _ _) hv_f2a))
  set sf₃ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState sf₂
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b_win), qA g_u)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b_win), vA g_u))
  obtain ⟨_, _, hq_f3a, hv_f3a, hl_f3a, hg_f3a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hbwin_lt_N (quotAt_lt _ _ _ _ _ _ _) sf₂
  obtain ⟨_, _, hq_f3b, hv_f3b, hl_f3b, hg_f3b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hbwin_lt_N (valAt_lt _ _ _ _ _ _ _ _) _
  have htd2_eq : compTDAt metaBase U w N s₂.mem = td := by
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_top.2.1 _).2.2.1.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_top.2.1 s₁.mem).2.2.1.trans ?_
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_top.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_u.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_u.2.1 s.mem).2.2.1
  have hd_last2_eq : denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s₂.mem n') =
      d_last := by rw [htd2_eq]
  have hs6_eq : s₆ = {
      mem := writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s₄.mem b_win (qA g_u))
        b_win (vA g_u),
      frontier := s₄.frontier } := by
    dsimp only [s₆, s₅]
    rw [clientState_writeCompValGenProg, clientState_writeCompQuotGenProg]
  have hcpl6 : WindowCoupled metaBase itemBase U V w N (b_win + 1) n' ((b_win + 1) + n')
      sf₃ s₆ := by
    have h := windowCoupled_shrinkLeft_write henv.pos_w henv.meta_le_item hb_pos
      (by rw [hn1_eq]; exact htot_N) hM_le hcpl2
      (quotAt_lt _ _ _ _ _ _ _) (valAt_lt _ _ _ _ _ _ _ _)
      (hg_f3b.trans hg_f3a) (hl_f3b.trans hl_f3a) (hq_f3b.trans hq_f3a)
      (hv_f3b.trans (congrArg (fun f => Function.update f _ _) hv_f3a))
    dsimp only at h
    rw [hd_last2_eq] at h
    change WindowCoupled metaBase itemBase U V w N (b_win + 1) n' ((b_win + 1) + n') sf₃
      { mem := writeCompVal itemBase U V w N
          (writeCompQuot itemBase U V w N s₄.mem b_win (qA g_u)) b_win (vA g_u),
        frontier := s₄.frontier } at h
    rw [← hs6_eq] at h
    exact h
  have hgm6_eq : compGmAt metaBase U w N s₆.mem = gm :=
    hcpl6.gm_eq.trans ((hg_f3b.trans (hg_f3a.trans (hg_f2b.trans (hg_f2a.trans
      (hg_f1b.trans hg_f1a))))).trans hgm_fix_eq)
  obtain ⟨hfr7, hgm7⟩ := compRemoveTailGMOnlyGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := (b_win + 1) + n')
    (b := b) henv.pos_w henv.meta_le_item hb_pos hb s₆
    (tailBijection_of_gm_eq hgm6_eq htail) (by rw [hgm6_eq]; omega)
  rw [hgm6_eq] at hgm7
  have hdt3_eq : compDTAt metaBase U w N s₃.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₃]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.2.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₂.mem).2.2.2.trans ?_
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    exact ((writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_top.2.1 _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_top.2.1 s₁.mem).2.2.2).trans
      hdt1_eq
  have htd3_eq : compTDAt metaBase U w N s₃.mem = td := by
    dsimp only [s₃]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    exact ((writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₂.mem).2.2.1).trans
      htd2_eq
  obtain ⟨hf_w4, _, _, _, _, _, _, hout_w4⟩ :=
    winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item (by omega) s₃
      (by rw [hdt3_eq, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd3_eq, ← hmax_eq]; exact hcpl.td_lt _)
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hst_all]
    exact (compOpFrame_copyCompItem henv.pos_w hdtop_cap hdu_cap s).trans <|
      (compOpFrame_copyCompItem henv.pos_w hdlast_cap hdtop_cap s₁).trans <|
      (compOpFrame_copyCompItem henv.pos_w hbwin_cap hdlast_cap s₂).trans <|
      (compOpFrame_tailWindow hf_w4 hout_w4).trans <|
      (compOpFrame_writeCompQuot henv.pos_w hbwin_cap s₄).trans <|
      (compOpFrame_writeCompVal henv.pos_w hbwin_cap s₅).trans <|
      CompOpFrame.of_gmFrame hfr7
  obtain ⟨_, _, _, hq_ps, hv_ps, hl_ps, hgm_ps⟩ :=
    promoteStepProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  have hpres := gmRemoveTail_preserves_nonTail hb (by omega : 1 ≤ gm (gmRIdx b)) htail
  have hgm7_0 : compGmAt metaBase U w N s₇.mem 0 = gm 0 := by rw [hgm7, hpres.1]
  have hgm7_1 : compGmAt metaBase U w N s₇.mem 1 = n' := by rw [hgm7, hpres.2.1]
  have hbwin1_eq : compGmAt metaBase U w N s₇.mem 0 * slabSize N + (k + 1) = b_win + 1 := by
    rw [hgm7_0]; dsimp only [b_win]; omega
  have hq_sf3_eq : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    have hq_sf1 : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem =
        Function.update qA g_u (qA g_top) := by
      dsimp only [qA₁] at hq_f1b; exact hq_f1b.trans hq_f1a
    dsimp only [sf₃, sf₂]
    rw [hq_f3b, hq_f3a, hq_ps, hgm_fix_eq, ← hr_top_eq, hq_f2b, hq_f2a, hq_sf1]
  have hv_sf3_eq : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    have hv_sf1 : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem =
        Function.update vA g_u (vA g_top) := by
      dsimp only [vA₁] at hv_f1b; rw [hv_f1b, hv_f1a]
    dsimp only [sf₃, sf₂]
    rw [hv_f3b, hv_f3a, hv_ps, hgm_fix_eq, ← hr_top_eq, hv_f2b, hv_f2a, hv_sf1]
  have hl_sf3_eq : lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    dsimp only [sf₃, sf₂, sf₁]
    rw [hl_f3b, hl_f3a, hl_f2b, hl_f2a, hl_f1b, hl_f1a, hl_ps]
  refine ⟨hres_all, hframe, ?_, ?_⟩
  · rw [hst_all]
    refine ⟨hgm7.trans (by rw [← hgm_fix_eq]; exact hgm_ps.symm),
      hfr7.lm_eq.trans (hcpl6.lm_eq.trans hl_sf3_eq),
      by rw [hbwin1_eq, hgm7_1, hfr7.td_eq, hfr7.dt_eq]; exact hcpl6.win_inv,
      fun i => by rw [hfr7.td_eq]; exact hcpl6.td_lt i,
      fun i => by rw [hfr7.dt_eq]; exact hcpl6.dt_lt i,
      fun idx hidx => ?_,
      fun idx hidx => ?_⟩
    · rw [hbwin1_eq, hgm7_1] at hidx ⊢
      rw [congrFun hfr7.quot_eq idx, hfr7.dt_eq, hcpl6.quot_eq idx hidx, hq_sf3_eq]
    · rw [hbwin1_eq, hgm7_1] at hidx ⊢
      rw [congrFun hfr7.val_eq idx, hfr7.dt_eq, hcpl6.val_eq idx hidx, hv_sf3_eq]
  · rw [hst_all, hbwin1_eq, hgm7_1]; omega

private def CompPromoteReadGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), k), s =>
    ∃ U V N m_cap itemBase s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix ∧
      compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem

private theorem copyCompItem_meta_frame {metaBase itemBase U V w N m_cap src dst : ℕ}
    (hw : 0 < w) (h_order : metaBase + offCompItems U w N ≤ itemBase)
    (hsrc : src < m_cap) (hdst : dst < m_cap) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst)))
    s'.frontier = s.frontier ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem ∧
    compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem := by
  intro s'
  have hs' := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase) (dst := dst) hsrc s
  obtain ⟨hlm1, hgm1, htd1, hdt1⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (q := compQuotAt itemBase U V w N m_cap s.mem src)
    hw h_order hdst s.mem
  obtain ⟨hlm2, hgm2, htd2, hdt2⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (v := compValAt itemBase U V w N m_cap s.mem src)
    hw h_order hdst
    (writeCompQuot itemBase U V w N s.mem dst (compQuotAt itemBase U V w N m_cap s.mem src))
  dsimp only [s']
  rw [hs']
  exact ⟨rfl, hlm2.trans hlm1, hgm2.trans hgm1, htd2.trans htd1, hdt2.trans hdt1⟩

private theorem realizesBounded_compPromoteReadPtrs :
    RealizesBounded .exact compPromoteReadPtrsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteReadGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, _, _, _, _⟩, _hgm_eq⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hTcap : tailCapPerBucket N = 2 * slabSize N := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0]
    have hu_cap : (slabSize N - 1) - k < tailCapPerBucket N := by omega
    have hr_top_cap : slabSize N + ((slabSize N - 1) - k) < tailCapPerBucket N := by omega
    have hptr_u_lt : gmTailPtrBase N + (b * tailCapPerBucket N + ((slabSize N - 1) - k)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hu_cap
    have hptr_top_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (slabSize N + ((slabSize N - 1) - k))) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_top_cap
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, cpGmTailPtrBase_mk, cpTailCap_mk,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    exact fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U (by omega)
  }
  omega

private def CompPromoteReadCountsPre (w : ℕ) :
    (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), k), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      compGmAt metaBase U w N s.mem 0 * slabSize N + k ≤ N ∧
      1 ≤ compGmAt metaBase U w N s.mem 1

private theorem realizesBounded_compPromoteReadCounts :
    RealizesBounded .exact compPromoteReadCountsProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteReadCountsPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, k⟩
    try dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, htot, hnt_pos⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpSlabSize_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | exact Fits.of_le hU (by omega)
  }
  omega

private theorem realizesBounded_compPromoteReadGM :
    RealizesBounded .exact compPromoteReadGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompPromoteReadGMPre (fun _ _ => 0) := by
  have hpt := realizesBounded_compPromoteReadPtrs
  have hct := realizesBounded_compPromoteReadCounts
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, _, hrb_fix, htot_fix⟩, hgm_eq⟩ := h
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hgm_eq htail_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
      (congrFun hgm_eq (gmRIdx b)).trans hrb_fix
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have htot : compGmAt metaBase U w N s.mem 0 * slabSize N + k +
        compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hgm_eq]; exact htot_fix
    have hst_pt : (Memory.spec 0).clientState s
        (compPromoteReadPtrsProg (((mkCompParams U V w N, metaBase), b), k)) = s := by
      unfold StateTransitionSpec.clientState; simp [compPromoteReadPtrsProg]
    rw [hst_pt]
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, by omega, by omega⟩

private def CompPromoteReadTDPre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((cp, metaBase), (n', (t_u, t_top))), s =>
    CompMetaEnv w cp metaBase s ∧ t_u < cpMaxTail cp ∧ t_top < cpMaxTail cp ∧ n' < cpMaxTail cp

private theorem realizesBounded_compPromoteReadTD :
    RealizesBounded .exact compPromoteReadTDProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteReadTDPre (fun _ _ => 0) := by
  have hrtd := realizesBounded_readCompTDGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨n', ⟨t_u, t_top⟩⟩⟩
    dsimp only at *
    obtain ⟨hmeta, htu, httop, hn'⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompTDGenProg] at *)
  · exact ⟨hmeta, htu⟩
  · exact ⟨hmeta, httop⟩
  · exact ⟨hmeta, hn'⟩

private def CompPromoteCalcDensePre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((cp, b_win), (c_u, (c_top, c_last))), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      b_win ≤ N ∧
      (0 < maxTailItems N →
        c_u < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_u ≤ N ∧
        c_top < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_top ≤ N ∧
        c_last < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_last ≤ N)

private theorem realizesBounded_compPromoteCalcDense :
    RealizesBounded .exact compPromoteCalcDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteCalcDensePre (fun _ _ => 0) := by
  have hdoc := realizesBounded_denseOfCircGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, b_win⟩, ⟨c_u, ⟨c_top, c_last⟩⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le, hcond⟩ := h)
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).1, (hcond hb).2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.1, (hcond hb).2.2.2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.2.2.1, (hcond hb).2.2.2.2.2⟩⟩

private theorem realizesBounded_compPromoteReadDense :
    RealizesBounded .exact compPromoteReadDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteReadDensePre (fun _ _ => 0) := by
  have hrtd := realizesBounded_compPromoteReadTD
  have hdoc := realizesBounded_compPromoteCalcDense
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨⟨b_win, n'⟩, ⟨t_u, t_top⟩⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hbn_N, htu_lt, httop_lt,
      hM_le, hwin⟩ := h
    have htu_max : t_u < maxTailItems N := lt_of_lt_of_le htu_lt hM_le
    have httop_max : t_top < maxTailItems N := lt_of_lt_of_le httop_lt hM_le
    have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (Nat.lt_succ_self n') hM_le)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩,
      by simp only [cpMaxTail_mk]; exact htu_max,
      by simp only [cpMaxTail_mk]; exact httop_max,
      by simp only [cpMaxTail_mk]; exact hn'_max⟩
  · have htd_r : (Memory.spec 0).clientResult s
        (compPromoteReadTDProg ((mkCompParams U V w N, metaBase), (n', (t_u, t_top)))) =
        (compTDAt metaBase U w N s.mem t_u,
         (compTDAt metaBase U w N s.mem t_top, compTDAt metaBase U w N s.mem n')) := by
      dsimp only [compPromoteReadTDProg]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg htu_max,
        clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompTDGenProg httop_max, clientState_readCompTDGenProg,
        StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg hn'_max,
        clientState_readCompTDGenProg]; rfl
    rw [htd_r]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, by omega,
      fun _ => ⟨hwin.td_lt _ htu_lt, le_trans (le_of_lt (hwin.dense_lt _ htu_lt)) hbn_N,
        hwin.td_lt _ httop_lt, le_trans (le_of_lt (hwin.dense_lt _ httop_lt)) hbn_N,
        hwin.td_lt _ (Nat.lt_succ_self n'),
        le_trans (le_of_lt (hwin.dense_lt _ (Nat.lt_succ_self n'))) hbn_N⟩⟩

private theorem realizesBounded_compPromoteMoveItems :
    RealizesBounded .exact compPromoteMoveItemsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteMoveItemsPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  have hcpy := realizesBounded_copyCompItemGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, b_win⟩, ⟨d_u, ⟨d_top, d_last⟩⟩⟩
    dsimp only at *
    obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb_lt, hdu, hdtop, hdlast⟩ := h)
  · exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdu⟩
  · rw [clientState_readCompQuotGenProg]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdu⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdtop, hdu⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg,
      clientState_copyCompItemGenProg hdtop]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdlast, hdtop⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg]
    set s1 := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u)))
    have hs2 := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_top) hdlast s1
    have hs1 := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_u) hdtop s
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl,
      by rw [hs2]; dsimp only [s1]; rw [hs1]; exact hfr⟩, hb_lt, hdlast⟩

private theorem realizesBounded_compPromoteFinishStep :
    RealizesBounded .exact compPromoteFinishStepProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompPromoteFinishStepPre (fun _ _ => 0) := by
  have hwsl := realizesBounded_winShrinkLeftGen
  have hwq := realizesBounded_writeCompQuotGen
  have hwv := realizesBounded_writeCompValGen
  have hrm := realizesBounded_compRemoveTailGMOnlyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨b_win, n'⟩⟩, ⟨q_u, v_u⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hb_N, hb_cap, hn'_max, hdt_lt, htd_lt,
      htail, hr_pos⟩ := h)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hn'_max, hb_N, hdt_lt, htd_lt⟩
  · obtain ⟨hf1, _, _, _, _, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    exact ⟨m_cap, (henv.of_mem_eq (by rw [hf1])).compItemEnv, hb_cap⟩
  · obtain ⟨hf1, _, _, _, _, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    exact ⟨m_cap, (henv.of_mem_eq (by rw [clientState_writeCompQuotGenProg, hf1])).compItemEnv,
      hb_cap⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    set s1 := (Memory.spec 0).clientState s
      (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    set s2 := (Memory.spec 0).clientState s1
      (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), b_win), q_u))
    set s3 := (Memory.spec 0).clientState s2
      (writeCompValGenProg (((mkCompParams U V w N, itemBase), b_win), v_u))
    have hs2_eq := clientState_writeCompQuotGenProg U V w N itemBase b_win q_u s1
    have hs3_eq := clientState_writeCompValGenProg U V w N itemBase b_win v_u s2
    have hgm3 : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem := by
      dsimp only [s3]; rw [hs3_eq]
      refine (writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
        (m_items := m_cap) (v := v_u) henv.pos_w henv.meta_le_item hb_cap s2.mem).2.1.trans ?_
      dsimp only [s2]; rw [hs2_eq]
      exact (writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
        (m_items := m_cap) (q := q_u) henv.pos_w henv.meta_le_item hb_cap s1.mem).2.1.trans hgm1
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hb, tailBijection_of_gm_eq hgm3 htail, by rw [hgm3]; exact hr_pos⟩
    dsimp only [s3]; rw [hs3_eq]; dsimp only [s2]; rw [hs2_eq, hf1]
    exact henv.meta_le_frontier

private theorem realizesBounded_compPromoteStep :
    RealizesBounded .exact compPromoteStepGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompPromoteStepPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_compPromoteReadGM
  have hrds := realizesBounded_compPromoteReadDense
  have hmv := realizesBounded_compPromoteMoveItems
  have hfin := realizesBounded_compPromoteFinishStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
    obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, _⟩ :=
      compPromoteStep_read_spec henv hb_pos hstep hcpl
    rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hcpl.gm_eq htail_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
      (congrFun hcpl.gm_eq (gmRIdx b)).trans hrb_fix
    have htot_N : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
        compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hcpl.gm_eq]; exact htot_fix
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
    have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
    have hn1_eq : compGmAt metaBase U w N s.mem 1 - 1 + 1 = compGmAt metaBase U w N s.mem 1 := by
      omega
    have htu_lt := htail.ptr_lt b hb ((slabSize N - 1) - k) (by omega)
    have httop_lt := htail.ptr_lt b hb (slabSize N + ((slabSize N - 1) - k)) (by omega))
  · exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩, hcpl.gm_eq⟩
  · rw [hst_gm, hres_gm]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, by omega, by omega, by omega,
      by rw [hn1_eq]; exact htail.ntails_le, by rw [hn1_eq]; exact hcpl.win_inv⟩
  · rw [hst_gm, hres_gm, hst_ds, hres_ds]; dsimp only
    have hd_u := hcpl.win_inv.dense_lt _ htu_lt
    have hd_top := hcpl.win_inv.dense_lt _ httop_lt
    have hd_last := hcpl.win_inv.dense_lt (compGmAt metaBase U w N s.mem 1 - 1) (by omega)
    exact ⟨m_cap, henv.compItemEnv, by omega, by omega, by omega, by omega⟩
  · rw [hst_gm, hres_gm, hst_ds, hres_ds]; dsimp only
    set b_win := compGmAt metaBase U w N s.mem 0 * slabSize N + k
    set n' := compGmAt metaBase U w N s.mem 1 - 1
    set d_u := denseOfCirc (maxTailItems N) b_win
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k))))
    set d_top := denseOfCirc (maxTailItems N) b_win
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k)))))
    set d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
    have hd_u : d_u < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ htu_lt) hm_cap
    have hd_top : d_top < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ httop_lt) hm_cap
    have hd_last : d_last < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt n' (by omega)) hm_cap
    have hb_cap : b_win < m_cap := by dsimp only [b_win]; omega
    set sm := (Memory.spec 0).clientState s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last))))
    have hsm_eq : sm = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last))) := by
      dsimp only [sm, compPromoteMoveItemsProg]
      rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg,
        StateTransitionSpec.clientState_bind, clientState_readCompValGenProg,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have fc1 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hd_top hd_u s
    have fc2 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hd_last hd_top
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
    have fc3 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hb_cap hd_last
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
    have hsm_fr : sm.frontier = s.frontier := by rw [hsm_eq]; exact fc3.1.trans (fc2.1.trans fc1.1)
    have hsm_gm : compGmAt metaBase U w N sm.mem = compGmAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.1.trans (fc2.2.2.1.trans fc1.2.2.1)
    have hsm_td : compTDAt metaBase U w N sm.mem = compTDAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.2.1.trans (fc2.2.2.2.1.trans fc1.2.2.2.1)
    have hsm_dt : compDTAt metaBase U w N sm.mem = compDTAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.2.2.trans (fc2.2.2.2.2.trans fc1.2.2.2.2)
    have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (by dsimp only [n']; omega) htail.ntails_le
    exact ⟨U, V, N, m_cap, rfl, henv.of_mem_eq (by rw [hsm_fr]), hb_pos, hb,
      by dsimp only [b_win]; omega, hb_cap, hn'_max,
      by rw [hsm_dt, ← hmax_eq]; exact hcpl.dt_lt _,
      by rw [hsm_td, ← hmax_eq]; exact hcpl.td_lt _,
      tailBijection_of_gm_eq hsm_gm htail, by rw [hsm_gm]; omega⟩
  · have hK_le := slabSize_le_max_n_one N
    exact fits_of_le_max_N_one henv.pos_w henv.le_U henv.lt_pow_U (by omega)

private theorem validProg_compPromoteMoveItems {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (h : CompPromoteMoveItemsPre w d s) :
    ValidProg w 0 s (compPromoteMoveItemsProg d) := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, b_win⟩, ⟨d_u, ⟨d_top, d_last⟩⟩⟩
  obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb_cap, hdu, hdtop, hdlast⟩ := h
  have mkIt : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompItemEnv w (mkCompParams U V w N) itemBase m_cap s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  dsimp only [compPromoteMoveItemsProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, mkIt s rfl, hdu⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, mkIt s rfl, hdu⟩) ?_
  rw [clientState_readCompValGenProg]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s rfl, hdtop, hdu⟩) fun s1 hs1 => ?_
  have hf1 : s1.frontier = s.frontier := by
    rw [hs1, clientState_copyCompItemGenProg hdtop]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s1 hf1, hdlast, hdtop⟩) fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2, clientState_copyCompItemGenProg hdlast, hf1]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s2 hf2, hb_cap, hdlast⟩) fun _ _ => ?_
  exact validProg_pure _

private theorem validProg_compPromoteFinishStep {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompPromoteFinishStepPre w d s) :
    ValidProg w 0 s (compPromoteFinishStepProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨b_win, n'⟩⟩, ⟨q_u, v_u⟩⟩
  obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hb_N, hb_cap, hn'_max, hdt_lt, htd_lt,
    htail, hr_pos⟩ := h
  obtain ⟨hf_w, _, _, _, hgm_w, _, _, _⟩ :=
    winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
  dsimp only [compPromoteFinishStepProg]
  refine validProg_bind_unit
    (validProg_winShrinkLeftGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
      henv.le_pow_V, rfl, henv.meta_le_frontier, hn'_max, hb_N, hdt_lt, htd_lt⟩) fun s1 hs1 => ?_
  have hf1 : s1.frontier = s.frontier := (congrArg Memory.State.frontier hs1).trans hf_w
  refine validProg_bind_unit
    (validProg_writeCompQuotGen ⟨m_cap, (henv.of_mem_eq (by rw [hf1])).compItemEnv, hb_cap⟩)
    fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2, clientState_writeCompQuotGenProg, hf1]
  refine validProg_bind_unit
    (validProg_writeCompValGen ⟨m_cap, (henv.of_mem_eq (by rw [hf2])).compItemEnv, hb_cap⟩)
    fun s3 hs3 => ?_
  have hf3 : s3.frontier = s.frontier := by
    rw [hs3, clientState_writeCompValGenProg, hf2]
  have hgm3 : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem := by
    rw [hs3, clientState_writeCompValGenProg]
    refine (writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := m_cap) (v := v_u) henv.pos_w henv.meta_le_item hb_cap s2.mem).2.1.trans ?_
    rw [hs2, clientState_writeCompQuotGenProg]
    refine (writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := m_cap) (q := q_u) henv.pos_w henv.meta_le_item hb_cap s1.mem).2.1.trans ?_
    rw [hs1]; exact hgm_w
  exact validProg_compRemoveTailGMOnlyGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U,
    henv.lt_pow_U, henv.le_pow_V, rfl, by rw [hf3]; exact henv.meta_le_frontier, hb_pos, hb,
    tailBijection_of_gm_eq hgm3 htail, by rw [hgm3]; exact hr_pos⟩

private theorem validProg_compPromoteStep {w : ℕ}
    {x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPromoteStepPre w x s) :
    ValidProg w 0 s (compPromoteStepGenProg x) := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
  obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, hv_gm, hv_ds⟩ :=
    compPromoteStep_read_spec henv hb_pos hstep hcpl
  rcases hstep with ⟨hb, hk_lt, htail_fix, _, hrb_fix, htot_fix⟩
  have htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
    (congrFun hcpl.gm_eq (gmRIdx b)).trans hrb_fix
  have htot_N : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
      compGmAt metaBase U w N s.mem 1 ≤ N := by
    rw [hcpl.gm_eq]; exact htot_fix
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have htu_lt := htail.ptr_lt b hb ((slabSize N - 1) - k) (by omega)
  have httop_lt := htail.ptr_lt b hb (slabSize N + ((slabSize N - 1) - k)) (by omega)
  set b_win := compGmAt metaBase U w N s.mem 0 * slabSize N + k
  set n' := compGmAt metaBase U w N s.mem 1 - 1
  set d_u := denseOfCirc (maxTailItems N) b_win
    (compTDAt metaBase U w N s.mem
      (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k))))
  set d_top := denseOfCirc (maxTailItems N) b_win
    (compTDAt metaBase U w N s.mem
      (compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k)))))
  set d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
  have hd_u : d_u < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ htu_lt) hm_cap
  have hd_top : d_top < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ httop_lt) hm_cap
  have hd_last : d_last < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt n' (by omega)) hm_cap
  have hb_cap : b_win < m_cap := by dsimp only [b_win]; omega
  dsimp only [compPromoteStepGenProg]
  refine validProg_bind_of_eq hv_gm hres_gm fun s1 hs1 => ?_
  rw [hs1, hst_gm]
  refine validProg_bind_of_eq hv_ds hres_ds fun s2 hs2 => ?_
  rw [hs2, hst_ds]
  set qv := (Memory.spec 0).clientResult s
    (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
      (d_u, (d_top, d_last))))
  refine validProg_bind_of_eq
    (validProg_compPromoteMoveItems ⟨m_cap, henv.compItemEnv, hb_cap, hd_u, hd_top, hd_last⟩)
    (rfl : _ = qv) fun sm hsm => ?_
  have hsm_eq : sm = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last))) := by
    rw [hsm]; dsimp only [compPromoteMoveItemsProg]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg,
      StateTransitionSpec.clientState_bind, clientState_readCompValGenProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have fc1 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hd_top hd_u s
  have fc2 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hd_last hd_top
    ((Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
  have fc3 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hb_cap hd_last
    ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
  have hsm_fr : sm.frontier = s.frontier := by rw [hsm_eq]; exact fc3.1.trans (fc2.1.trans fc1.1)
  have hsm_gm : compGmAt metaBase U w N sm.mem = compGmAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.1.trans (fc2.2.2.1.trans fc1.2.2.1)
  have hsm_td : compTDAt metaBase U w N sm.mem = compTDAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.2.1.trans (fc2.2.2.2.1.trans fc1.2.2.2.1)
  have hsm_dt : compDTAt metaBase U w N sm.mem = compDTAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.2.2.trans (fc2.2.2.2.2.trans fc1.2.2.2.2)
  have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (by dsimp only [n']; omega) htail.ntails_le
  refine validProg_bind_unit
    (validProg_compPromoteFinishStep ⟨U, V, N, m_cap, rfl,
      henv.of_mem_eq (by rw [hsm_fr]), hb_pos, hb, by dsimp only [b_win]; omega, hb_cap, hn'_max,
      by rw [hsm_dt, ← hmax_eq]; exact hcpl.dt_lt _,
      by rw [hsm_td, ← hmax_eq]; exact hcpl.td_lt _,
      tailBijection_of_gm_eq hsm_gm htail, by rw [hsm_gm]; omega⟩)
    fun _ _ => validProg_pure _

private def compPromoteLoopGenProg (x : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) :
    Memory.Prog ℕ :=
  iterate compPromoteStepGenProg x.1.1 x.2 x.1.2

private theorem realizesBounded_compPromoteLoopGen :
    RealizesBounded .exact compPromoteLoopGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w x s =>
        iterationSafe compPromoteStepGenProg CompPromoteStepPre w x.1.1 x.2 x.1.2 s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_compPromoteStep
    one_le_memoryCost_compPromoteStepGenProg

private theorem iterate_compPromoteStep_spec {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix₀ : Memory.State} (hb_pos : 0 < bucketBits N) :
    ∀ m k (s_fix s : Memory.State),
      k + m ≤ slabSize N →
      CompEpochEnv U V w N metaBase itemBase m_cap s →
      PromoteLoopInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix₀ k s_fix →
      WindowCoupled metaBase itemBase U V w N
        (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
        (compGmAt metaBase U w N s.mem 1)
        ((compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1)
        s_fix s →
      (compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1 ≤
        m_cap →
      let d_env := ((mkCompParams U V w N, (metaBase, itemBase)), b)
      let s_end := (Memory.spec 0).clientState s (iterate compPromoteStepGenProg d_env m k)
      let s_fix_end := (Memory.spec 0).clientState s_fix
        (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)) (0, b) m k)
      CompOpFrame metaBase itemBase U V w N m_cap s s_end ∧
      WindowCoupled metaBase itemBase U V w N
        (compGmAt metaBase U w N s_end.mem 0 * slabSize N + (k + m))
        (compGmAt metaBase U w N s_end.mem 1)
        ((compGmAt metaBase U w N s_end.mem 0 * slabSize N + (k + m)) +
          compGmAt metaBase U w N s_end.mem 1)
        s_fix_end s_end ∧
      memoryCost (iterate compPromoteStepGenProg d_env m k) s = 98 * m ∧
      iterationSafe compPromoteStepGenProg CompPromoteStepPre w d_env m k s := by
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  intro m
  induction m with
  | zero =>
    intro k s_fix s _ _ _ hcpl _
    simp only [iterate, Nat.add_zero, memoryCost_pure, Nat.mul_zero, iterationSafe]
    exact ⟨CompOpFrame.refl s, hcpl, trivial, trivial⟩
  | succ m ih =>
    intro k s_fix s hkm henv hloop hcpl hm_cap
    have hk_lt : k < slabSize N := by omega
    have hstep := promoteStepInv_of_loopInv hloop hk_lt
    obtain ⟨hres_fix, hloop'⟩ := promoteLoopInv_step hwg hb_pos hloop hk_lt
    obtain ⟨hres_s, hfr1, hcpl1, hm_cap1⟩ :=
      compPromoteStep_effect henv hb_pos hstep hcpl hm_cap
    set d_env := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    set s₁ := (Memory.spec 0).clientState s (compPromoteStepGenProg (d_env, k))
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), k))
    have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
    obtain ⟨hfr_m, hcpl_m, hcost_m, hsafe_m⟩ :=
      ih (k + 1) s_fix₁ s₁ (by omega) henv1 hloop' hcpl1 hm_cap1
    have hkm_eq : (k + 1) + m = k + (m + 1) := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold iterate; rw [StateTransitionSpec.clientState_bind, hres_s]
      exact hfr1.trans hfr_m
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres_s,
        StateTransitionSpec.clientState_bind, hres_fix, ← hkm_eq]
      exact hcpl_m
    · dsimp only [s₁] at hcost_m
      simp only [iterate, Realization.memoryCost_bind', memoryCost_compPromoteStepGenProg,
        hres_s, hcost_m]
      omega
    · simp only [iterationSafe, hres_s]
      exact ⟨⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩, hsafe_m⟩

private def compPromoteSlabGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    let k0 ← pure 0
    let K ← pure (cpSlabSize cp)
    let _ ← compPromoteLoopGenProg ((((cp, (metaBase, itemBase)), b), k0), K)
    compGmPushSlabGenProg ((cp, metaBase), b)

private def CompPromoteSlabPre (w : ℕ) : (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

private theorem compPromoteSlab_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hpre : PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    let s' := (Memory.spec 0).clientState s (compPromoteSlabGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (promoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compPromoteSlabGenProg d) s ≤ 98 * slabSize N + 38 := by
  intro d s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hloop0 := promoteLoopInv_zero hpre
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + 0)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + 0) + compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc
    simpa only [Nat.add_zero] using hc
  have hm_cap0 : (compGmAt metaBase U w N s.mem 0 * slabSize N + 0) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; omega
  obtain ⟨hfr_loop, hcpl_loop, hcost_loop, _⟩ :=
    iterate_compPromoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_promoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add] at hcpl_loop hloopK
  set s₁ := (Memory.spec 0).clientState s
    (compPromoteLoopGenProg ((d, 0), slabSize N))
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (promoteLoopProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), 0), slabSize N))
  have hs1_eq : s₁ = (Memory.spec 0).clientState s
      (iterate compPromoteStepGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
        (slabSize N) 0) := rfl
  have hs_fix1_eq : s_fix₁ = (Memory.spec 0).clientState s_fix
      (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
        (0, b) (slabSize N) 0) := rfl
  rw [← hs1_eq] at hcpl_loop hfr_loop
  rw [← hs_fix1_eq] at hloopK hcpl_loop
  have htot1 : (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem 0 + 1) *
      slabSize N ≤ N := by
    have := hloopK.tot_le; rw [Nat.add_one_mul]; omega
  have hp_lt1 := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  have hslab1 : SlabBijection N (compGmAt metaBase U w N s₁.mem)
      (fun b' => compGmAt metaBase U w N s₁.mem (gmQIdx b'))
      (compGmAt metaBase U w N s₁.mem 0) :=
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij
  have hp_lt1_s : compGmAt metaBase U w N s₁.mem 0 < maxFullSlabs N := by
    rw [hcpl_loop.gm_eq]; exact hp_lt1
  obtain ⟨hfr_push, hgm_push⟩ := compGmPushSlabGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N)
    (m_items := (compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N) +
      compGmAt metaBase U w N s₁.mem 1) (b := b)
    henv.pos_w henv.meta_le_item hb_pos hloopK.b_lt s₁ hslab1 hp_lt1_s
  obtain ⟨_, _, hq_fpush, hv_fpush, hl_fpush, hgm_fpush⟩ :=
    gmPushSlabProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hloopK.b_lt s_fix₁
      hloopK.slab_bij hp_lt1
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [s', d, compPromoteSlabGenProg]
    simp only [pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientState_bind]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
      (gmPushSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
    dsimp only [s_fix', promoteSlabProg, promoteSlabGenProg]
    simp only [promoteLoopGenProg_mk, p_slabSize_mk, gmPushSlabGenProg_mk]
    rw [StateTransitionSpec.clientState_bind]
  have hf_fields := gmPushSlab_fields (compGmAt metaBase U w N s₁.mem) hloopK.b_lt
  refine ⟨by rw [hs'_eq]; exact hfr_loop.trans (CompOpFrame.of_gmFrame hfr_push), ?_, ?_⟩
  · rw [hs'_eq, hs_fix'_eq]
    unfold FixedCoupled
    have hgm0' : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s₁
          (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem 0 =
        compGmAt metaBase U w N s₁.mem 0 + 1 := by rw [hgm_push, hf_fields.1]
    have hgm1' : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s₁
          (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem 1 =
        compGmAt metaBase U w N s₁.mem 1 := by rw [hgm_push, hf_fields.2.1]
    have hbwin_eq : (compGmAt metaBase U w N s₁.mem 0 + 1) * slabSize N =
        compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N := Nat.add_one_mul _ _
    have htot_eq' : epochTotalSlots N
        (compGmAt metaBase U w N
          ((Memory.spec 0).clientState s₁
            (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem) =
        (compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N) +
          compGmAt metaBase U w N s₁.mem 1 := by
      unfold epochTotalSlots; rw [ite_eq_right hb0, hgm0', hgm1', hbwin_eq]
    refine ⟨hgm_push.trans ((congrArg (fun g => gmPushSlab N g b) hcpl_loop.gm_eq).trans
        hgm_fpush.symm),
      hfr_push.lm_eq.trans (hcpl_loop.lm_eq.trans hl_fpush.symm),
      by simp only [hb0, ↓reduceIte, hgm0', hgm1', hbwin_eq, hfr_push.td_eq, hfr_push.dt_eq]
         exact hcpl_loop.win_inv,
      fun i => by rw [hfr_push.td_eq]; exact hcpl_loop.td_lt i,
      fun i => by rw [hfr_push.dt_eq]; exact hcpl_loop.dt_lt i,
      fun idx hidx => ?_,
      fun idx hidx => ?_⟩
    · rw [htot_eq'] at hidx ⊢
      rw [congrFun hfr_push.quot_eq idx, hgm0', hbwin_eq, hfr_push.dt_eq, hq_fpush]
      exact hcpl_loop.quot_eq idx hidx
    · rw [htot_eq'] at hidx ⊢
      rw [congrFun hfr_push.val_eq idx, hgm0', hbwin_eq, hfr_push.dt_eq, hv_fpush]
      exact hcpl_loop.val_eq idx hidx
  · dsimp only [d, compPromoteSlabGenProg]
    simp only [pure_bind, cpSlabSize_mk, Realization.memoryCost_bind']
    change memoryCost (iterate compPromoteStepGenProg
        ((mkCompParams U V w N, (metaBase, itemBase)), b) (slabSize N) 0) s +
      memoryCost (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b)) s₁ ≤
      98 * slabSize N + 38
    rw [hcost_loop]
    have hpush_cost := memoryCost_compGmPushSlabGenProg_le
      ((mkCompParams U V w N, metaBase), b) s₁
    omega

private theorem realizesBounded_compPromoteSlabGen :
    RealizesBounded .exact compPromoteSlabGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPromoteSlabPre (fun _ _ => 0) := by
  have hloop := realizesBounded_compPromoteLoopGen
  have hpush := realizesBounded_compGmPushSlabGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hpre, hcpl, hm_cap⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hloop0 := promoteLoopInv_zero hpre
    have hcpl0 : WindowCoupled metaBase itemBase U V w N
        (compGmAt metaBase U w N s.mem 0 * slabSize N + 0)
        (compGmAt metaBase U w N s.mem 1)
        ((compGmAt metaBase U w N s.mem 0 * slabSize N + 0) + compGmAt metaBase U w N s.mem 1)
        s_fix s := by
      have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
      simp only [hb0, ↓reduceIte] at hc; simpa only [Nat.add_zero] using hc
    have hm_cap0 : (compGmAt metaBase U w N s.mem 0 * slabSize N + 0) +
        compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
      unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; omega
    obtain ⟨hfr_loop, hcpl_loop, _, hsafe_loop⟩ :=
      iterate_compPromoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0
        hm_cap0)
  · simpa only [cpSlabSize_mk] using hsafe_loop
  · simp only [cpSlabSize_mk, compPromoteLoopGenProg]
    obtain ⟨hloopK, _, _⟩ :=
      iterate_promoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega)
        hloop0
    rw [Nat.zero_add] at hcpl_loop hloopK
    have htot1 : (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((Memory.spec 0).clientState s_fix
          (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
            (0, b) (slabSize N) 0)).mem 0 + 1) * slabSize N ≤ N := by
      have := hloopK.tot_le; rw [Nat.add_one_mul]; omega
    have hp_lt1 := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hloopK.b_lt,
      slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij, ?_⟩
    · rw [hfr_loop.frontier_eq]; exact henv.meta_le_frontier
    · rw [hcpl_loop.gm_eq]; exact hp_lt1

private theorem validProg_compPromoteSlabGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPromoteSlabPre w d s) :
    ValidProg w 0 s (compPromoteSlabGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hpre, hcpl, hm_cap⟩ := h
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hloop0 := promoteLoopInv_zero hpre
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + 0)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + 0) + compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc; simpa only [Nat.add_zero] using hc
  have hm_cap0 : (compGmAt metaBase U w N s.mem 0 * slabSize N + 0) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; omega
  obtain ⟨hfr_loop, hcpl_loop, _, hsafe_loop⟩ :=
    iterate_compPromoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_promoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add] at hcpl_loop hloopK
  have htot1 : (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      ((Memory.spec 0).clientState s_fix
        (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
          (0, b) (slabSize N) 0)).mem 0 + 1) * slabSize N ≤ N := by
    have := hloopK.tot_le; rw [Nat.add_one_mul]; omega
  have hp_lt1 := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  dsimp only [compPromoteSlabGenProg]
  simp only [pure_bind, cpSlabSize_mk]
  refine validProg_bind
    (validProg_iterate (slabSize N) 0 s (fun _ _ hs => validProg_compPromoteStep hs) hsafe_loop)
    ?_
  dsimp only [compPromoteLoopGenProg]
  exact validProg_compGmPushSlabGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
    henv.le_pow_V, rfl,
    by rw [hfr_loop.frontier_eq]; exact henv.meta_le_frontier,
    hb_pos, hloopK.b_lt,
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij,
    by rw [hcpl_loop.gm_eq]; exact hp_lt1⟩

/-! ## Section 4: Compacted `K`-Step Slab Demotion (`compDemoteSlabGenProg`) -/

private def compDemoteReadGMProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((cp, metaBase), b), k) => do
    let u := cpSlabSizeSubOne cp - k
    let top_idx := 4 + (b + b + b) + 2
    let p_del ← readCompGMGenProg ((cp, metaBase), top_idx)
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    let g_del := p_del * cpSlabSize cp + u
    let g_last := (n_slabs - 1) * cpSlabSize cp + u
    pure ((g_del, g_last), n_tails)

private def compDemoteReadItemsProg :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, itemBase), (g_del, g_last)) => do
    let q_del ← readCompQuotGenProg ((cp, itemBase), g_del)
    let v_del ← readCompValGenProg ((cp, itemBase), g_del)
    let q_last ← readCompQuotGenProg ((cp, itemBase), g_last)
    let v_last ← readCompValGenProg ((cp, itemBase), g_last)
    pure ((q_del, v_del), (q_last, v_last))

private def compDemoteWinAppendProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (g_last, n_tails)) => do
    winGrowLeftGenProg ((cp, metaBase), (g_last, n_tails))
    let _ ← compAppendTailGMGenProg ((cp, metaBase), b)
    pure ()

private def compDemoteSwapItemsProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, itemBase), (g_del, g_last)), ((q_del, v_del), (q_last, v_last))) => do
    writeCompItemGenProg (((cp, itemBase), g_del), (q_last, v_last))
    writeCompItemGenProg (((cp, itemBase), g_last), (q_del, v_del))

private def compDemoteFinishStepProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), ((g_del, g_last), n_tails)), qv) => do
    compDemoteWinAppendProg (((cp, metaBase), b), (g_last, n_tails))
    compDemoteSwapItemsProg (((cp, itemBase), (g_del, g_last)), qv)

private def compDemoteStepGenProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, (metaBase, itemBase)), b), k) => do
    let gmInfo ← compDemoteReadGMProg (((cp, metaBase), b), k)
    let qv ← compDemoteReadItemsProg ((cp, itemBase), gmInfo.1)
    compDemoteFinishStepProg (((((cp, (metaBase, itemBase)), b), gmInfo), qv))
    pure (k + 1)

@[simp] private theorem memoryCost_compDemoteStepGenProg
    (x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compDemoteStepGenProg x) s = 58 := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  simp [compDemoteStepGenProg, compDemoteReadGMProg, compDemoteReadItemsProg,
    compDemoteFinishStepProg, compDemoteWinAppendProg, compDemoteSwapItemsProg,
    writeCompItemGenProg]

private theorem one_le_memoryCost_compDemoteStepGenProg
    (x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (compDemoteStepGenProg x) s := by
  rw [memoryCost_compDemoteStepGenProg]; omega

private def CompDemoteStepPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), k), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      DemoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix ∧
      WindowCoupled metaBase itemBase U V w N
        ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k))
        (compGmAt metaBase U w N s.mem 1)
        (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
          compGmAt metaBase U w N s.mem 1)
        s_fix s ∧
      ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
        compGmAt metaBase U w N s.mem 1 ≤ m_cap

private def CompDemoteReadGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), k), s =>
    ∃ U V N m_cap itemBase s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      DemoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix ∧
      compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem

private def CompDemoteReadItemsPre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, itemBase), (g_del, g_last)), s =>
    ∃ m_cap, CompItemEnv w cp itemBase m_cap s ∧ g_del < m_cap ∧ g_last < m_cap

private def CompDemoteFinishStepPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), ((g_del, g_last), n_tails)), _qv), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      g_del < m_cap ∧ g_last < m_cap ∧ g_last ≤ N ∧
      n_tails < maxTailItems N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem compDemoteStep_read_spec {metaBase itemBase U V w N m_cap b k : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hstep : DemoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix)
    (_hgm_eq : compGmAt metaBase U w N s.mem =
      gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) :
    let gm := compGmAt metaBase U w N s.mem
    let u := (slabSize N - 1) - k
    let g_del := gm (gmSlabTopIdx b) * slabSize N + u
    let g_last := (gm 0 - 1) * slabSize N + u
    (Memory.spec 0).clientState s
      (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) = s ∧
    (Memory.spec 0).clientResult s
      (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) =
      ((g_del, g_last), gm 1) ∧
    ValidProg w 0 s (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) := by
  intro gm u g_del g_last
  rcases hstep with ⟨hb, _, _, hslab_fix, _, hqb_fix, _⟩
  have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hst : (Memory.spec 0).clientState s
      (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) = s := by
    unfold StateTransitionSpec.clientState; simp [compDemoteReadGMProg]
  have hres : (Memory.spec 0).clientResult s
      (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) =
      ((g_del, g_last), gm 1) := by
    dsimp only [compDemoteReadGMProg]
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, htop_eq]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg htop_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h1_lt,
      clientState_readCompGMGenProg]
    rfl
  have hv : ValidProg w 0 s
      (compDemoteReadGMProg (((mkCompParams U V w N, metaBase), b), k)) := by
    dsimp only [compDemoteReadGMProg]
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, htop_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, htop_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)
  exact ⟨hst, hres, hv⟩

private theorem compDemoteStep_effect {metaBase itemBase U V w N m_cap b k : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hstep : DemoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix)
    (hcpl : WindowCoupled metaBase itemBase U V w N
      ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k))
      (compGmAt metaBase U w N s.mem 1)
      (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
        compGmAt metaBase U w N s.mem 1)
      s_fix s)
    (hm_cap : ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap) :
    let d := (((mkCompParams U V w N, (metaBase, itemBase)), b), k)
    let s' := (Memory.spec 0).clientState s (compDemoteStepGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (demoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), k))
    (Memory.spec 0).clientResult s (compDemoteStepGenProg d) = k + 1 ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    WindowCoupled metaBase itemBase U V w N
      ((compGmAt metaBase U w N s'.mem 0 - 1) * slabSize N + (slabSize N - (k + 1)))
      (compGmAt metaBase U w N s'.mem 1)
      (((compGmAt metaBase U w N s'.mem 0 - 1) * slabSize N + (slabSize N - (k + 1))) +
        compGmAt metaBase U w N s'.mem 1)
      s_fix' s' ∧
    ((compGmAt metaBase U w N s'.mem 0 - 1) * slabSize N + (slabSize N - (k + 1))) +
      compGmAt metaBase U w N s'.mem 1 ≤ m_cap := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  obtain ⟨hst_gm, hres_gm, _⟩ := compDemoteStep_read_spec henv hb_pos hstep hcpl.gm_eq
  rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  set gm := compGmAt metaBase U w N s.mem
  have hgm_fix_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = gm :=
    hcpl.gm_eq.symm
  have htail : TailBijection N gm (fun b' => gm (gmRIdx b')) (gm 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hslab : SlabBijection N gm (fun b' => gm (gmQIdx b')) (gm 0) :=
    slabBijection_of_gm_eq hcpl.gm_eq hslab_fix
  have hrb : gm (gmRIdx b) = k := by dsimp only [gm]; rw [hcpl.gm_eq]; exact hrb_fix
  have hqb : 1 ≤ gm (gmQIdx b) := by dsimp only [gm]; rw [hcpl.gm_eq]; exact hqb_fix
  have htot_N : (gm 0 - 1) * slabSize N + (slabSize N - k) + gm 1 ≤ N := by
    dsimp only [gm]; rw [hcpl.gm_eq]; exact htot_fix
  set u := (slabSize N - 1) - k
  set g_del := gm (gmSlabTopIdx b) * slabSize N + u
  set g_last := (gm 0 - 1) * slabSize N + u
  set m := ((gm 0 - 1) * slabSize N + (slabSize N - k)) + gm 1
  have hbwin_eq : (gm 0 - 1) * slabSize N + (slabSize N - k) = g_last + 1 := by
    dsimp only [g_last, u]; omega
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := hslab.top_lt hb (by omega)
  have hg_del_le_last : g_del ≤ g_last := by
    have hmul : gm (gmSlabTopIdx b) * slabSize N ≤ (gm 0 - 1) * slabSize N :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp only [g_del, g_last]; omega
  have hg_del_lt_b : g_del < g_last + 1 := by omega
  have hg_last_lt_b : g_last < g_last + 1 := Nat.lt_succ_self g_last
  have hg_del_m : g_del < m := by dsimp only [m]; omega
  have hg_last_m : g_last < m := by dsimp only [m]; omega
  have hg_del_cap : g_del < m_cap := lt_of_lt_of_le hg_del_m hm_cap
  have hg_last_cap : g_last < m_cap := lt_of_lt_of_le hg_last_m hm_cap
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket N := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have ht_cap : gm 1 < maxTailItems N := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  set qA := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  set vA := valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  have hcpl0 : WindowCoupled metaBase itemBase U V w N (g_last + 1) (gm 1) m s_fix s := by
    simpa only [hbwin_eq] using hcpl
  have hq_del_eq : compQuotAt itemBase U V w N m s.mem g_del = qA g_del := by
    rw [hcpl0.quot_eq g_del hg_del_m, physByBase_slab _ hg_del_lt_b]
  have hv_del_eq : compValAt itemBase U V w N m s.mem g_del = vA g_del := by
    rw [hcpl0.val_eq g_del hg_del_m, physByBase_slab _ hg_del_lt_b]
  have hq_last_eq : compQuotAt itemBase U V w N m s.mem g_last = qA g_last := by
    rw [hcpl0.quot_eq g_last hg_last_m, physByBase_slab _ hg_last_lt_b]
  have hv_last_eq : compValAt itemBase U V w N m s.mem g_last = vA g_last := by
    rw [hcpl0.val_eq g_last hg_last_m, physByBase_slab _ hg_last_lt_b]
  have hrd_st : (Memory.spec 0).clientState s
      (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last))) = s := by
    unfold StateTransitionSpec.clientState; simp [compDemoteReadItemsProg]
  have hrd_res : (Memory.spec 0).clientResult s
      (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last))) =
      ((qA g_del, vA g_del), (qA g_last, vA g_last)) := by
    dsimp only [compDemoteReadItemsProg]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompQuotGenProg hg_del_m,
      clientState_readCompQuotGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompValGenProg hg_del_m, clientState_readCompValGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompQuotGenProg hg_last_m,
      clientState_readCompQuotGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompValGenProg hg_last_m, clientState_readCompValGenProg,
      StateTransitionSpec.clientResult_pure, hq_del_eq, hv_del_eq, hq_last_eq, hv_last_eq]
  set s₁ := (Memory.spec 0).clientState s
    (winGrowLeftGenProg ((mkCompParams U V w N, metaBase), (g_last, gm 1)))
  obtain ⟨hf_w1, htd_w1, hdt_w1, hlm_w1, hgm_w1, hq_w1, hv_w1, hout_w1⟩ :=
    winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m) (b_win := g_last) (n_win := gm 1)
      henv.pos_w henv.meta_le_item ht_cap s
  set s₂ := (Memory.spec 0).clientState s₁
    (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨_, hfr2, hgm2⟩ := compAppendTailGMGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := m) (b := b)
    henv.pos_w henv.meta_le_item hb_pos hb s₁
    (tailBijection_of_gm_eq hgm_w1 htail) (by rw [hgm_w1]; exact hr_cap)
  rw [hgm_w1] at hgm2
  set s₃ := (Memory.spec 0).clientState s₂
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), g_del), qA g_last))
  set s₄ := (Memory.spec 0).clientState s₃
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), g_del), vA g_last))
  set s₅ := (Memory.spec 0).clientState s₄
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), g_last), qA g_del))
  set s₆ := (Memory.spec 0).clientState s₅
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), g_last), vA g_del))
  have hres_all : (Memory.spec 0).clientResult s (compDemoteStepGenProg d) = k + 1 := by
    dsimp only [d, compDemoteStepGenProg, compDemoteFinishStepProg, compDemoteWinAppendProg,
      compDemoteSwapItemsProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, hst_gm, hres_gm,
      StateTransitionSpec.clientResult_bind]
    repeat rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hst_all : s' = s₆ := by
    dsimp only [s', d, compDemoteStepGenProg, compDemoteFinishStepProg, compDemoteWinAppendProg,
      compDemoteSwapItemsProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind]
    rw [StateTransitionSpec.clientState_bind, hst_gm, hres_gm,
      StateTransitionSpec.clientState_bind, hrd_st, hrd_res,
      StateTransitionSpec.clientState_bind]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [StateTransitionSpec.clientState_pure]
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hst_all]
    exact (compOpFrame_tailWindow hf_w1 hout_w1).trans <|
      (CompOpFrame.of_gmFrame hfr2).trans <|
      (compOpFrame_writeCompQuot henv.pos_w hg_del_cap s₂).trans <|
      (compOpFrame_writeCompVal henv.pos_w hg_del_cap s₃).trans <|
      (compOpFrame_writeCompQuot henv.pos_w hg_last_cap s₄).trans <|
      compOpFrame_writeCompVal henv.pos_w hg_last_cap s₅
  obtain ⟨_, _, _, hq_ds, hv_ds, hl_ds, hgm_ds⟩ :=
    demoteStepProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  have hs6_mem : s₆.mem =
      writeCompVal itemBase U V w N
        (writeCompQuot itemBase U V w N
          (writeCompVal itemBase U V w N
            (writeCompQuot itemBase U V w N s₂.mem g_del (qA g_last)) g_del (vA g_last))
          g_last (qA g_del)) g_last (vA g_del) := by
    dsimp only [s₆, s₅, s₄, s₃]
    rw [clientState_writeCompValGenProg, clientState_writeCompQuotGenProg,
      clientState_writeCompValGenProg, clientState_writeCompQuotGenProg]
  have f1 := writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    (m_items := m) (q := qA g_last) henv.pos_w henv.meta_le_item hg_del_m s₂.mem
  have f2 := writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    (m_items := m) (v := vA g_last) henv.pos_w henv.meta_le_item hg_del_m
    (writeCompQuot itemBase U V w N s₂.mem g_del (qA g_last))
  have f3 := writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    (m_items := m) (q := qA g_del) henv.pos_w henv.meta_le_item hg_last_m
    (writeCompVal itemBase U V w N
      (writeCompQuot itemBase U V w N s₂.mem g_del (qA g_last)) g_del (vA g_last))
  have f4 := writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    (m_items := m) (v := vA g_del) henv.pos_w henv.meta_le_item hg_last_m
    (writeCompQuot itemBase U V w N
      (writeCompVal itemBase U V w N
        (writeCompQuot itemBase U V w N s₂.mem g_del (qA g_last)) g_del (vA g_last))
      g_last (qA g_del))
  have hgm6 : compGmAt metaBase U w N s₆.mem = gmAppendTail N gm b := by
    rw [hs6_mem]; exact f4.2.1.trans (f3.2.1.trans (f2.2.1.trans (f1.2.1.trans hgm2)))
  have hlm6 : compLmAt metaBase U w N s₆.mem = compLmAt metaBase U w N s.mem := by
    rw [hs6_mem]
    exact f4.1.trans (f3.1.trans (f2.1.trans (f1.1.trans (hfr2.lm_eq.trans hlm_w1))))
  have htd6 : compTDAt metaBase U w N s₆.mem =
      (winGrowLeft (maxTailItems N) g_last (gm 1)
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).1 := by
    rw [hs6_mem]
    exact f4.2.2.1.trans (f3.2.2.1.trans (f2.2.2.1.trans (f1.2.2.1.trans
      (hfr2.td_eq.trans htd_w1))))
  have hdt6 : compDTAt metaBase U w N s₆.mem =
      (winGrowLeft (maxTailItems N) g_last (gm 1)
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).2 := by
    rw [hs6_mem]
    exact f4.2.2.2.trans (f3.2.2.2.trans (f2.2.2.2.trans (f1.2.2.2.trans
      (hfr2.dt_eq.trans hdt_w1))))
  have hpres := gmAppendTail_preserves_nonTail gm hb hr_cap ht_cap
  have hgm6_0 : compGmAt metaBase U w N s₆.mem 0 = gm 0 := by rw [hgm6, hpres.1]
  have hgm6_1 : compGmAt metaBase U w N s₆.mem 1 = gm 1 + 1 := by rw [hgm6, hpres.2.1]
  have hbwin6_eq : (compGmAt metaBase U w N s₆.mem 0 - 1) * slabSize N +
      (slabSize N - (k + 1)) = g_last := by
    rw [hgm6_0]; dsimp only [g_last, u]; omega
  have hm6_eq : g_last + (gm 1 + 1) = m := by dsimp only [m]; rw [hbwin_eq]; omega
  have hwspec := winGrowLeft_spec hcpl0.win_inv (by omega : gm 1 + 1 ≤ maxTailItems N)
    (fun i => by rw [← hmax_eq]; exact hcpl0.td_lt i)
    (fun i => by rw [← hmax_eq]; exact hcpl0.dt_lt i)
  have hp_gl := physByBase_winGrowLeft (N := N) (b := g_last) (n := gm 1)
    (td := compTDAt metaBase U w N s.mem) (dt := compDTAt metaBase U w N s.mem)
    hb_pos (by omega)
  have htot_g : g_last + 1 + gm 1 ≤ N := by rw [← hbwin_eq]; exact htot_N
  refine ⟨hres_all, hframe, ?_, ?_⟩
  · rw [hst_all]
    refine ⟨hgm6.trans (by rw [← hgm_fix_eq]; exact hgm_ds.symm),
      hlm6.trans (hcpl0.lm_eq.trans hl_ds.symm),
      by rw [hbwin6_eq, hgm6_1, htd6, hdt6]; exact hwspec.1,
      fun i => by rw [htd6, hmax_eq]; exact hwspec.2.1 i,
      fun i => by rw [hdt6, hmax_eq]; exact hwspec.2.2 i,
      fun idx hidx => ?_,
      fun idx hidx => ?_⟩
    · rw [hbwin6_eq, hgm6_1, hm6_eq] at hidx ⊢
      have hidx_g : idx < g_last + 1 + gm 1 := by dsimp only [m] at hidx; omega
      have hg_del_g : g_del < g_last + 1 + gm 1 := by omega
      rw [hdt6, hs6_mem, compQuotAt_writeCompVal henv.pos_w, hq_ds, hgm_fix_eq]
      unfold winGrowLeft; dsimp only
      by_cases heq_last : idx = g_last
      · subst heq_last
        rw [compQuotAt_writeCompQuot_self _ hg_last_m (quotAt_lt _ _ _ _ _ _ _),
          hp_gl.1, Function.update_self]
      · rw [compQuotAt_writeCompQuot_of_ne henv.pos_w _ heq_last,
          compQuotAt_writeCompVal henv.pos_w,
          hp_gl.2 idx (by omega) heq_last]
        have hp_ne_tail : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) idx ≠
            N - 1 - gm 1 := by
          have hrng := (physByBase_range_and_inj hb_pos htot_g
            (le_of_lt ht_cap) hcpl0.win_inv).1 idx hidx_g
          rcases hrng with ⟨hlt, hp_eq⟩ | ⟨_, _, _⟩
          · rw [hp_eq]; omega
          · obtain ⟨ht_idx, _⟩ := hcpl0.win_inv.owner_valid idx (by omega) hidx_g
            unfold physByBase
            rw [ite_eq_right hb0, ite_eq_right (by omega : ¬idx < g_last + 1)]
            omega
        rw [Function.update_of_ne hp_ne_tail]
        by_cases heq_del : idx = g_del
        · subst heq_del
          rw [compQuotAt_writeCompQuot_self s₂.mem hg_del_m (quotAt_lt _ _ _ _ _ _ _),
            physByBase_slab _ hg_del_lt_b, Function.update_self]
        · have hp_ne_del : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) idx ≠
              g_del := by
            intro hp_eq
            have h1 : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) g_del = g_del :=
              physByBase_slab _ hg_del_lt_b
            exact heq_del ((physByBase_range_and_inj hb_pos htot_g
              (le_of_lt ht_cap) hcpl0.win_inv).2 idx hidx_g g_del hg_del_g (hp_eq.trans h1.symm))
          rw [compQuotAt_writeCompQuot_of_ne henv.pos_w s₂.mem heq_del,
            congrFun hfr2.quot_eq idx, congrFun hq_w1 idx,
            Function.update_of_ne hp_ne_del]
          exact hcpl0.quot_eq idx hidx
    · rw [hbwin6_eq, hgm6_1, hm6_eq] at hidx ⊢
      have hidx_g : idx < g_last + 1 + gm 1 := by dsimp only [m] at hidx; omega
      have hg_del_g : g_del < g_last + 1 + gm 1 := by omega
      rw [hdt6, hs6_mem, hv_ds, hgm_fix_eq]
      unfold winGrowLeft; dsimp only
      by_cases heq_last : idx = g_last
      · subst heq_last
        rw [compValAt_writeCompVal_self _ hg_last_m (valAt_lt _ _ _ _ _ _ _ _),
          hp_gl.1, Function.update_self]
      · rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq_last,
          compValAt_writeCompQuot henv.pos_w,
          hp_gl.2 idx (by omega) heq_last]
        have hp_ne_tail : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) idx ≠
            N - 1 - gm 1 := by
          have hrng := (physByBase_range_and_inj hb_pos htot_g
            (le_of_lt ht_cap) hcpl0.win_inv).1 idx hidx_g
          rcases hrng with ⟨hlt, hp_eq⟩ | ⟨_, _, _⟩
          · rw [hp_eq]; omega
          · obtain ⟨ht_idx, _⟩ := hcpl0.win_inv.owner_valid idx (by omega) hidx_g
            unfold physByBase
            rw [ite_eq_right hb0, ite_eq_right (by omega : ¬idx < g_last + 1)]
            omega
        rw [Function.update_of_ne hp_ne_tail]
        by_cases heq_del : idx = g_del
        · subst heq_del
          rw [compValAt_writeCompVal_self _ hg_del_m (valAt_lt _ _ _ _ _ _ _ _),
            physByBase_slab _ hg_del_lt_b, Function.update_self]
        · have hp_ne_del : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) idx ≠
              g_del := by
            intro hp_eq
            have h1 : physByBase N (g_last + 1) (compDTAt metaBase U w N s.mem) g_del = g_del :=
              physByBase_slab _ hg_del_lt_b
            exact heq_del ((physByBase_range_and_inj hb_pos htot_g
              (le_of_lt ht_cap) hcpl0.win_inv).2 idx hidx_g g_del hg_del_g (hp_eq.trans h1.symm))
          rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq_del,
            compValAt_writeCompQuot henv.pos_w s₂.mem,
            congrFun hfr2.val_eq idx, congrFun hv_w1 idx,
            Function.update_of_ne hp_ne_del]
          exact hcpl0.val_eq idx hidx
  · rw [hst_all, hbwin6_eq, hgm6_1, hm6_eq]; exact hm_cap

private theorem realizesBounded_compDemoteReadGM :
    RealizesBounded .exact compDemoteReadGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompDemoteReadGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    try dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, _, hslab_fix, _, hqb_fix, htot_fix⟩, hgm_eq⟩ := h
    have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) :=
      slabBijection_of_gm_eq hgm_eq hslab_fix
    have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hgm_eq]; exact hqb_fix
    have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
        (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hgm_eq]; exact htot_fix
    have hp_del_lt : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
        compGmAt metaBase U w N s.mem 0 := hslab.top_lt hb (by omega)
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hnU : N ≤ U := henv.le_U
    have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, htop_eq,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg htop_lt] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  all_goals try exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | { refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
          unfold gmSlabTopIdx at *; omega }
      | { have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
              (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N :=
            Nat.mul_le_mul_right _ (by omega)
          exact Fits.of_le henv.lt_pow_U (by omega) }
  }
  all_goals omega

private theorem realizesBounded_compDemoteReadItems :
    RealizesBounded .exact compDemoteReadItemsProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompDemoteReadItemsPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩
    obtain ⟨m_cap, hitem_env, hg_del, hg_last⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_readCompQuotGenProg,
      runClient_state_readCompValGenProg] at *)
  · exact ⟨m_cap, hitem_env, hg_del⟩
  · exact ⟨m_cap, hitem_env, hg_del⟩
  · exact ⟨m_cap, hitem_env, hg_last⟩
  · exact ⟨m_cap, hitem_env, hg_last⟩

private def CompDemoteWinAppendPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (g_last, n_tails)), s =>
    ∃ U V N m_cap itemBase,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      g_last ≤ N ∧
      n_tails < maxTailItems N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compDemoteWinAppend :
    RealizesBounded .exact compDemoteWinAppendProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompDemoteWinAppendPre (fun _ _ => 0) := by
  have hwgl := realizesBounded_winGrowLeftGen
  have happ := realizesBounded_compAppendTailGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨g_last, n_tails⟩⟩
    obtain ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hg_last_N, hnt_max,
      htail, hr_cap⟩ := h)
  · exact ⟨henv.compMetaEnv, hnt_max, by simp only [cpN_mk]; exact hg_last_N⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
        henv.pos_w henv.meta_le_item hnt_max s
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by rw [hf1]; exact henv.meta_le_frontier, hb_pos, hb,
      tailBijection_of_gm_eq hgm1 htail, by rw [hgm1]; exact hr_cap⟩

private def CompDemoteSwapItemsPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, itemBase), (g_del, g_last)), _qv), s =>
    ∃ m_cap, CompItemEnv w cp itemBase m_cap s ∧ g_del < m_cap ∧ g_last < m_cap

private theorem realizesBounded_compDemoteSwapItems :
    RealizesBounded .exact compDemoteSwapItemsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompDemoteSwapItemsPre (fun _ _ => 0) := by
  have hwit := realizesBounded_writeCompItemGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩, ⟨⟨q_del, v_del⟩, ⟨q_last, v_last⟩⟩⟩
    obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hg_del, hg_last⟩ := h)
  · exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hg_del⟩
  · refine ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, hg_last⟩
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
    exact hfr

private theorem realizesBounded_compDemoteFinishStep :
    RealizesBounded .exact compDemoteFinishStepProg
      (WordEncoding.encode
        (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompDemoteFinishStepPre (fun _ _ => 0) := by
  have hwa := realizesBounded_compDemoteWinAppend
  have hsw := realizesBounded_compDemoteSwapItems
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨g_del, g_last⟩, n_tails⟩⟩, qv⟩
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del, hg_last, hg_last_N, hnt_max,
      htail, hr_cap⟩ := h)
  · exact ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hg_last_N, hnt_max, htail, hr_cap⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
        henv.pos_w henv.meta_le_item hnt_max s
    obtain ⟨_, hfr2, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm1 htail) (by rw [hgm1]; exact hr_cap)
    refine ⟨m_cap, (henv.of_mem_eq ?_).compItemEnv, hg_del, hg_last⟩
    dsimp only [compDemoteWinAppendProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr2.frontier_eq, hf1]

private theorem realizesBounded_compDemoteStep :
    RealizesBounded .exact compDemoteStepGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompDemoteStepPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_compDemoteReadGM
  have hrit := realizesBounded_compDemoteReadItems
  have hfin := realizesBounded_compDemoteFinishStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
    obtain ⟨hst_gm, hres_gm, _⟩ := compDemoteStep_read_spec henv hb_pos hstep hcpl.gm_eq
    rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hcpl.gm_eq htail_fix
    have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) :=
      slabBijection_of_gm_eq hcpl.gm_eq hslab_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = k := by
      rw [hcpl.gm_eq]; exact hrb_fix
    have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hcpl.gm_eq]; exact hqb_fix
    have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
        (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hcpl.gm_eq]; exact htot_fix
    have hp_del_lt := hslab.top_lt hb (by omega)
    have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
        (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N := Nat.mul_le_mul_right _ (by omega)
    have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
    have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail)
  · exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩, hcpl.gm_eq⟩
  · rw [hst_gm, hres_gm]; dsimp only
    exact ⟨m_cap, henv.compItemEnv, by omega, by omega⟩
  · rw [hst_gm, hres_gm]; dsimp only
    set gd := compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N + ((slabSize N - 1) - k)
    set gl := (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + ((slabSize N - 1) - k)
    have hrd_st : (Memory.spec 0).clientState s
        (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (gd, gl))) = s := by
      unfold StateTransitionSpec.clientState; simp [compDemoteReadItemsProg]
    rw [hrd_st]
    exact ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, by dsimp only [gd]; omega,
      by dsimp only [gl]; omega, by dsimp only [gl]; omega, ht_cap, htail, hr_cap⟩
  · have hK_le := slabSize_le_max_n_one N
    exact fits_of_le_max_N_one henv.pos_w henv.le_U henv.lt_pow_U (by omega)

private theorem validProg_compDemoteReadItems {w : ℕ}
    {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDemoteReadItemsPre w d s) :
    ValidProg w 0 s (compDemoteReadItemsProg d) := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩
  obtain ⟨m_cap, hitem, hg_del, hg_last⟩ := h
  dsimp only [compDemoteReadItemsProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, hitem, hg_del⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, hitem, hg_del⟩) ?_
  rw [clientState_readCompValGenProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, hitem, hg_last⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, hitem, hg_last⟩) ?_
  exact validProg_pure _

private theorem validProg_compDemoteFinishStep {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))}
    {s : Memory.State} (h : CompDemoteFinishStepPre w d s) :
    ValidProg w 0 s (compDemoteFinishStepProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨g_del, g_last⟩, n_tails⟩⟩, qv⟩
  obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del, hg_last, hg_last_N, hnt_max,
    htail, hr_cap⟩ := h
  obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
    winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
      henv.pos_w henv.meta_le_item hnt_max s
  obtain ⟨_, hfr2, _⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb _
      (tailBijection_of_gm_eq hgm1 htail) (by rw [hgm1]; exact hr_cap)
  have hv_wa : ValidProg w 0 s
      (compDemoteWinAppendProg (((mkCompParams U V w N, metaBase), b), (g_last, n_tails))) := by
    dsimp only [compDemoteWinAppendProg]
    refine validProg_bind_unit
      (validProg_winGrowLeftGen ⟨henv.compMetaEnv, hnt_max,
        by simp only [cpN_mk]; exact hg_last_N⟩) fun s1 hs1 => ?_
    refine validProg_bind
      (validProg_compAppendTailGMGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
        henv.le_pow_V, rfl, by rw [hs1, hf1]; exact henv.meta_le_frontier, hb_pos, hb,
        by rw [hs1]; exact tailBijection_of_gm_eq hgm1 htail,
        by rw [hs1, hgm1]; exact hr_cap⟩) ?_
    exact validProg_pure ()
  dsimp only [compDemoteFinishStepProg]
  refine validProg_bind_unit hv_wa fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2]; dsimp only [compDemoteWinAppendProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr2.frontier_eq, hf1]
  have henv2 := henv.of_mem_eq (s' := s2) (by rw [hf2])
  rcases qv with ⟨⟨q_del, v_del⟩, ⟨q_last, v_last⟩⟩
  dsimp only [compDemoteSwapItemsProg]
  refine validProg_bind_unit
    (validProg_writeCompItemGen ⟨m_cap, henv2.compItemEnv, hg_del⟩) fun s3 hs3 => ?_
  have hf3 : s3.frontier = s2.frontier := by
    rw [hs3]; dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
  exact validProg_writeCompItemGen ⟨m_cap, (henv2.of_mem_eq (by rw [hf3])).compItemEnv, hg_last⟩

private theorem validProg_compDemoteStep {w : ℕ}
    {x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ} {s : Memory.State}
    (h : CompDemoteStepPre w x s) :
    ValidProg w 0 s (compDemoteStepGenProg x) := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
  obtain ⟨hst_gm, hres_gm, hv_gm⟩ := compDemoteStep_read_spec henv hb_pos hstep hcpl.gm_eq
  rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0) :=
    slabBijection_of_gm_eq hcpl.gm_eq hslab_fix
  have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = k := by
    rw [hcpl.gm_eq]; exact hrb_fix
  have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
    rw [hcpl.gm_eq]; exact hqb_fix
  have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
      (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
    rw [hcpl.gm_eq]; exact htot_fix
  have hp_del_lt := hslab.top_lt hb (by omega)
  have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
      (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N := Nat.mul_le_mul_right _ (by omega)
  have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  set u := (slabSize N - 1) - k
  set g_del := compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N + u
  set g_last := (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + u
  have hg_del_cap : g_del < m_cap := by dsimp only [g_del, u]; omega
  have hg_last_cap : g_last < m_cap := by dsimp only [g_last, u]; omega
  have hg_last_N : g_last ≤ N := by dsimp only [g_last, u]; omega
  dsimp only [compDemoteStepGenProg]
  refine validProg_bind_of_eq hv_gm hres_gm fun s1 hs1 => ?_
  rw [hs1, hst_gm]
  dsimp only
  set qv := (Memory.spec 0).clientResult s
    (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last)))
  have hrd_st : (Memory.spec 0).clientState s
      (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last))) = s := by
    unfold StateTransitionSpec.clientState; simp [compDemoteReadItemsProg]
  refine validProg_bind_of_eq
    (validProg_compDemoteReadItems ⟨m_cap, henv.compItemEnv, hg_del_cap, hg_last_cap⟩)
    (rfl : _ = qv) fun s2 hs2 => ?_
  rw [hs2, hrd_st]
  refine validProg_bind_unit
    (validProg_compDemoteFinishStep ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del_cap,
      hg_last_cap, hg_last_N, ht_cap, htail, hr_cap⟩)
    fun _ _ => validProg_pure _

private def compDemoteLoopGenProg (x : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) :
    Memory.Prog ℕ :=
  iterate compDemoteStepGenProg x.1.1 x.2 x.1.2

private theorem realizesBounded_compDemoteLoopGen :
    RealizesBounded .exact compDemoteLoopGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w x s =>
        iterationSafe compDemoteStepGenProg CompDemoteStepPre w x.1.1 x.2 x.1.2 s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_compDemoteStep
    one_le_memoryCost_compDemoteStepGenProg

private theorem iterate_compDemoteStep_spec {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix₀ : Memory.State} (hb_pos : 0 < bucketBits N) :
    ∀ m k (s_fix s : Memory.State),
      k + m ≤ slabSize N →
      CompEpochEnv U V w N metaBase itemBase m_cap s →
      DemoteLoopInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix₀ k s_fix →
      WindowCoupled metaBase itemBase U V w N
        ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k))
        (compGmAt metaBase U w N s.mem 1)
        (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
          compGmAt metaBase U w N s.mem 1)
        s_fix s →
      ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - k)) +
        compGmAt metaBase U w N s.mem 1 ≤ m_cap →
      let d_env := ((mkCompParams U V w N, (metaBase, itemBase)), b)
      let s_end := (Memory.spec 0).clientState s (iterate compDemoteStepGenProg d_env m k)
      let s_fix_end := (Memory.spec 0).clientState s_fix
        (iterate (demoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)) (0, b) m k)
      CompOpFrame metaBase itemBase U V w N m_cap s s_end ∧
      WindowCoupled metaBase itemBase U V w N
        ((compGmAt metaBase U w N s_end.mem 0 - 1) * slabSize N + (slabSize N - (k + m)))
        (compGmAt metaBase U w N s_end.mem 1)
        (((compGmAt metaBase U w N s_end.mem 0 - 1) * slabSize N + (slabSize N - (k + m))) +
          compGmAt metaBase U w N s_end.mem 1)
        s_fix_end s_end ∧
      memoryCost (iterate compDemoteStepGenProg d_env m k) s = 58 * m ∧
      iterationSafe compDemoteStepGenProg CompDemoteStepPre w d_env m k s := by
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  intro m
  induction m with
  | zero =>
    intro k s_fix s _ _ _ hcpl _
    simp only [iterate, Nat.add_zero, memoryCost_pure, Nat.mul_zero, iterationSafe]
    exact ⟨CompOpFrame.refl s, hcpl, trivial, trivial⟩
  | succ m ih =>
    intro k s_fix s hkm henv hloop hcpl hm_cap
    have hk_lt : k < slabSize N := by omega
    have hstep := demoteLoopInv_to_stepInv hloop hk_lt
    obtain ⟨hres_fix, hloop'⟩ := demoteLoopInv_step hwg hb_pos hloop hk_lt
    obtain ⟨hres_s, hfr1, hcpl1, hm_cap1⟩ :=
      compDemoteStep_effect henv hb_pos hstep hcpl hm_cap
    set d_env := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    set s₁ := (Memory.spec 0).clientState s (compDemoteStepGenProg (d_env, k))
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (demoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), k))
    have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
    obtain ⟨hfr_m, hcpl_m, hcost_m, hsafe_m⟩ :=
      ih (k + 1) s_fix₁ s₁ (by omega) henv1 hloop' hcpl1 hm_cap1
    have hkm_eq : (k + 1) + m = k + (m + 1) := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold iterate; rw [StateTransitionSpec.clientState_bind, hres_s]
      exact hfr1.trans hfr_m
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres_s,
        StateTransitionSpec.clientState_bind, hres_fix, ← hkm_eq]
      exact hcpl_m
    · dsimp only [s₁] at hcost_m
      simp only [iterate, Realization.memoryCost_bind', memoryCost_compDemoteStepGenProg,
        hres_s, hcost_m]
      omega
    · simp only [iterationSafe, hres_s]
      exact ⟨⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩, hsafe_m⟩

private def compDemoteSlabGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    let k0 ← pure 0
    let K ← pure (cpSlabSize cp)
    let _ ← compDemoteLoopGenProg ((((cp, (metaBase, itemBase)), b), k0), K)
    compGmPopSlabGenProg ((cp, metaBase), b)

private def CompDemoteSlabPre (w : ℕ) : (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

private theorem compDemoteSlab_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hpre : DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    let s' := (Memory.spec 0).clientState s (compDemoteSlabGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (demoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compDemoteSlabGenProg d) s ≤ 58 * slabSize N + 68 := by
  intro d s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hloop0 := demoteLoopInv_zero hpre
  have hslab0 := slabBijection_of_gm_eq hcpl.gm_eq hpre.2.2.1
  have hqb0 : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
    rw [hcpl.gm_eq]; exact hpre.2.2.2.2.1
  have hp_del_lt : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
      compGmAt metaBase U w N s.mem 0 :=
    hslab0.top_lt hpre.1 (by omega)
  have hgm0_mul : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0) =
      compGmAt metaBase U w N s.mem 0 * slabSize N := by
    rw [Nat.sub_zero, ← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0))
      (compGmAt metaBase U w N s.mem 1)
      (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
        compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc
    simpa only [hgm0_mul] using hc
  have hm_cap0 : ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    rw [hgm0_mul]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; exact hm_cap
  obtain ⟨hfr_loop, hcpl_loop, hcost_loop, _⟩ :=
    iterate_compDemoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_demoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add, Nat.sub_self, Nat.add_zero] at hcpl_loop
  rw [Nat.zero_add] at hloopK
  set s₁ := (Memory.spec 0).clientState s
    (compDemoteLoopGenProg ((d, 0), slabSize N))
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (demoteLoopProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), 0), slabSize N))
  have hs1_eq : s₁ = (Memory.spec 0).clientState s
      (iterate compDemoteStepGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
        (slabSize N) 0) := rfl
  have hs_fix1_eq : s_fix₁ = (Memory.spec 0).clientState s_fix
      (iterate (demoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
        (0, b) (slabSize N) 0) := rfl
  rw [← hs1_eq] at hcpl_loop hfr_loop
  rw [← hs_fix1_eq] at hloopK hcpl_loop
  have hslab1 : SlabBijection N (compGmAt metaBase U w N s₁.mem)
      (fun b' => compGmAt metaBase U w N s₁.mem (gmQIdx b'))
      (compGmAt metaBase U w N s₁.mem 0) :=
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij
  have hqb1 : 1 ≤ compGmAt metaBase U w N s₁.mem (gmQIdx b) := by
    rw [hcpl_loop.gm_eq]; exact hloopK.qb_pos
  obtain ⟨hfr_pop, hgm_pop⟩ := compGmPopSlabGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N)
    (m_items := (compGmAt metaBase U w N s₁.mem 0 - 1) * slabSize N +
      compGmAt metaBase U w N s₁.mem 1) (b := b)
    henv.pos_w henv.meta_le_item hb_pos hloopK.b_lt s₁ hslab1 hqb1
  obtain ⟨_, _, hq_fpop, hv_fpop, hl_fpop, hgm_fpop⟩ :=
    gmPopSlabProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hloopK.b_lt s_fix₁
      hloopK.slab_bij hloopK.qb_pos
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [s', d, compDemoteSlabGenProg]
    simp only [pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientState_bind]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
      (gmPopSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
    dsimp only [s_fix', demoteSlabProg, demoteSlabGenProg]
    simp only [demoteLoopGenProg_mk, p_slabSize_mk, gmPopSlabGenProg_mk]
    rw [StateTransitionSpec.clientState_bind]
  have hf_fields := gmPopSlab_preserves_tail hloopK.b_lt hslab1
  refine ⟨by rw [hs'_eq]; exact hfr_loop.trans (CompOpFrame.of_gmFrame hfr_pop), ?_, ?_⟩
  · rw [hs'_eq, hs_fix'_eq]
    unfold FixedCoupled
    have hgm0' : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s₁
          (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem 0 =
        compGmAt metaBase U w N s₁.mem 0 - 1 := by rw [hgm_pop, hf_fields.1]
    have hgm1' : compGmAt metaBase U w N
        ((Memory.spec 0).clientState s₁
          (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem 1 =
        compGmAt metaBase U w N s₁.mem 1 := by rw [hgm_pop, hf_fields.2.1]
    have htot_eq' : epochTotalSlots N
        (compGmAt metaBase U w N
          ((Memory.spec 0).clientState s₁
            (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b))).mem) =
        (compGmAt metaBase U w N s₁.mem 0 - 1) * slabSize N +
          compGmAt metaBase U w N s₁.mem 1 := by
      unfold epochTotalSlots; rw [ite_eq_right hb0, hgm0', hgm1']
    refine ⟨hgm_pop.trans ((congrArg (fun g => gmPopSlab N g b) hcpl_loop.gm_eq).trans
        hgm_fpop.symm),
      hfr_pop.lm_eq.trans (hcpl_loop.lm_eq.trans hl_fpop.symm),
      by simp only [hb0, ↓reduceIte, hgm0', hgm1', hfr_pop.td_eq, hfr_pop.dt_eq]
         exact hcpl_loop.win_inv,
      fun i => by rw [hfr_pop.td_eq]; exact hcpl_loop.td_lt i,
      fun i => by rw [hfr_pop.dt_eq]; exact hcpl_loop.dt_lt i,
      fun idx hidx => ?_,
      fun idx hidx => ?_⟩
    · rw [htot_eq'] at hidx ⊢
      rw [congrFun hfr_pop.quot_eq idx, hgm0', hfr_pop.dt_eq, hq_fpop]
      exact hcpl_loop.quot_eq idx hidx
    · rw [htot_eq'] at hidx ⊢
      rw [congrFun hfr_pop.val_eq idx, hgm0', hfr_pop.dt_eq, hv_fpop]
      exact hcpl_loop.val_eq idx hidx
  · dsimp only [d, compDemoteSlabGenProg]
    simp only [pure_bind, cpSlabSize_mk, Realization.memoryCost_bind']
    change memoryCost (iterate compDemoteStepGenProg
        ((mkCompParams U V w N, (metaBase, itemBase)), b) (slabSize N) 0) s +
      memoryCost (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b)) s₁ ≤
      58 * slabSize N + 68
    rw [hcost_loop]
    have hpop_cost := memoryCost_compGmPopSlabGenProg_le
      ((mkCompParams U V w N, metaBase), b) s₁
    omega

private theorem realizesBounded_compDemoteSlabGen :
    RealizesBounded .exact compDemoteSlabGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompDemoteSlabPre (fun _ _ => 0) := by
  have hloop := realizesBounded_compDemoteLoopGen
  have hpop := realizesBounded_compGmPopSlabGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hpre, hcpl, hm_cap⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hloop0 := demoteLoopInv_zero hpre
    have hslab0 := slabBijection_of_gm_eq hcpl.gm_eq hpre.2.2.1
    have hqb0 : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hcpl.gm_eq]; exact hpre.2.2.2.2.1
    have hp_del_lt : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
        compGmAt metaBase U w N s.mem 0 :=
      hslab0.top_lt hpre.1 (by omega)
    have hgm0_mul : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0) =
        compGmAt metaBase U w N s.mem 0 * slabSize N := by
      rw [Nat.sub_zero, ← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
    have hcpl0 : WindowCoupled metaBase itemBase U V w N
        ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0))
        (compGmAt metaBase U w N s.mem 1)
        (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
          compGmAt metaBase U w N s.mem 1)
        s_fix s := by
      have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
      simp only [hb0, ↓reduceIte] at hc; simpa only [hgm0_mul] using hc
    have hm_cap0 : ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
        compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
      rw [hgm0_mul]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; exact hm_cap
    obtain ⟨hfr_loop, hcpl_loop, _, hsafe_loop⟩ :=
      iterate_compDemoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0
        hm_cap0)
  · simpa only [cpSlabSize_mk] using hsafe_loop
  · simp only [cpSlabSize_mk, compDemoteLoopGenProg]
    obtain ⟨hloopK, _, _⟩ :=
      iterate_demoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega)
        hloop0
    rw [Nat.zero_add] at hcpl_loop hloopK
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hloopK.b_lt,
      slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij, ?_⟩
    · rw [hfr_loop.frontier_eq]; exact henv.meta_le_frontier
    · rw [hcpl_loop.gm_eq]; exact hloopK.qb_pos

private theorem validProg_compDemoteSlabGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompDemoteSlabPre w d s) :
    ValidProg w 0 s (compDemoteSlabGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hpre, hcpl, hm_cap⟩ := h
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hloop0 := demoteLoopInv_zero hpre
  have hslab0 := slabBijection_of_gm_eq hcpl.gm_eq hpre.2.2.1
  have hqb0 : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
    rw [hcpl.gm_eq]; exact hpre.2.2.2.2.1
  have hp_del_lt : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
      compGmAt metaBase U w N s.mem 0 :=
    hslab0.top_lt hpre.1 (by omega)
  have hgm0_mul : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0) =
      compGmAt metaBase U w N s.mem 0 * slabSize N := by
    rw [Nat.sub_zero, ← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0))
      (compGmAt metaBase U w N s.mem 1)
      (((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
        compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc; simpa only [hgm0_mul] using hc
  have hm_cap0 : ((compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + (slabSize N - 0)) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    rw [hgm0_mul]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; exact hm_cap
  obtain ⟨hfr_loop, hcpl_loop, _, hsafe_loop⟩ :=
    iterate_compDemoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_demoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add] at hcpl_loop hloopK
  dsimp only [compDemoteSlabGenProg]
  simp only [pure_bind, cpSlabSize_mk]
  refine validProg_bind
    (validProg_iterate (slabSize N) 0 s (fun _ _ hs => validProg_compDemoteStep hs) hsafe_loop)
    ?_
  dsimp only [compDemoteLoopGenProg]
  exact validProg_compGmPopSlabGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
    henv.le_pow_V, rfl,
    by rw [hfr_loop.frontier_eq]; exact henv.meta_le_frontier,
    hb_pos, hloopK.b_lt,
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij,
    by rw [hcpl_loop.gm_eq]; exact hloopK.qb_pos⟩

/-! ## Section 5: Amortized `O(1)` Slot Push and Pop -/

private def compPushBackSingleGenProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), q_val), v_val) => do
    let c ← readCompGMGenProg ((cp, metaBase), 0)
    writeCompItemGenProg (((cp, itemBase), c), (q_val, v_val))
    writeCompGMGenProg (((cp, metaBase), 0), c + 1)

private def compPushBackMultiGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) => do
    let r_b_new ← compPushBackTailWriteGenProg
      ((((cp, (metaBase, itemBase)), b), q_val), v_val)
    if r_b_new = cpTwoSlabSize cp then
      compPromoteSlabGenProg ((cp, (metaBase, itemBase)), b)
    else
      pure ()

/-- Append `(q_val, v_val)` at logical slot `bCount N gm b` of bucket `b` in compacted layout
`(metaBase, itemBase)`, promoting `K = slabSize N` tail items into a full slab when
`r_b + 1 = 2 * K` (`¬ReadsWidth`). -/
def compPushBackSlotGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) =>
    if cpBucketBits cp = 0 then
      compPushBackSingleGenProg (((cp, (metaBase, itemBase)), q_val), v_val)
    else
      compPushBackMultiGenProg ((((cp, (metaBase, itemBase)), b), q_val), v_val)

/-- Precondition for `compPushBackSlotGenProg`. -/
@[expose] def CompPushBackSlotPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      q_val < 2 ^ quotientBits U N ∧
      v_val < 2 ^ valBits V

/-- `compPushBackSlotGenProg` maintains `FixedCoupled` with `pushBackSlotProg`, preserves outside
memory via `CompOpFrame`, and satisfies the `O(1)` amortized `memoryCost` bound against
`98 * slotPotential N gm`. -/
theorem compPushBackSlotGenProg_effect {metaBase itemBase U V w N m_cap b q_val v_val : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V) :
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (compPushBackSlotGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compPushBackSlotGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 178 := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
  by_cases hb0 : bucketBits N = 0
  · have hb_eq : b = 0 := by
      have hnb : numBuckets N = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    unfold totalSlots at htot hm_cap; rw [ite_eq_left hb0] at htot hm_cap
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hc_cap : gm₀ 0 < m_cap := by omega
    have hc1_pow : gm₀ 0 + 1 < 2 ^ globalPtrBits N :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set s₁ := (Memory.spec 0).clientState s
      (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), gm₀ 0), q_val))
    set s₂ := (Memory.spec 0).clientState s₁
      (writeCompValGenProg (((mkCompParams U V w N, itemBase), gm₀ 0), v_val))
    set s₃ := (Memory.spec 0).clientState s₂
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm₀ 0 + 1))
    have hs'_eq : s' = s₃ := by
      dsimp only [s', d, compPushBackSlotGenProg, compPushBackSingleGenProg, writeCompItemGenProg]
      simp only [bind_assoc, cpBucketBits_mk, hb0, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind]
    obtain ⟨hfr3, hgm3⟩ := compGmFrame_writeCompGMGenProg (metaBase := metaBase)
      (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := gm₀ 0 + 1)
      (idx := 0) (val := gm₀ 0 + 1) henv.pos_w henv.meta_le_item h0_lt hc1_pow s₂
    have hs1_mem : s₁.mem = writeCompQuot itemBase U V w N s.mem (gm₀ 0) q_val := by
      dsimp only [s₁]; rw [clientState_writeCompQuotGenProg]
    have hs2_mem : s₂.mem = writeCompVal itemBase U V w N s₁.mem (gm₀ 0) v_val := by
      dsimp only [s₂]; rw [clientState_writeCompValGenProg]
    have fq := writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := gm₀ 0 + 1) (q := q_val) henv.pos_w henv.meta_le_item (Nat.lt_succ_self _) s.mem
    have fv := writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := gm₀ 0 + 1) (v := v_val) henv.pos_w henv.meta_le_item (Nat.lt_succ_self _) s₁.mem
    have hgm2 : compGmAt metaBase U w N s₂.mem = gm₀ := by
      rw [hs2_mem]; refine fv.2.1.trans ?_; rw [hs1_mem]; exact fq.2.1
    rw [hgm2] at hgm3
    have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
      rw [hs'_eq]
      exact (compOpFrame_writeCompQuot henv.pos_w hc_cap s).trans
        ((compOpFrame_writeCompVal henv.pos_w hc_cap s₁).trans (CompOpFrame.of_gmFrame hfr3))
    obtain ⟨_, _, hq_f1, hv_f1, hl_f1, hg_f1⟩ :=
      writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg htot hq_lt s_fix
    obtain ⟨_, _, hq_f2, hv_f2, hl_f2, hg_f2⟩ :=
      writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg htot hv_lt _
    obtain ⟨_, _, hq_f3, hv_f3, hl_f3, hg_f3⟩ :=
      writeGMProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg h0_lt hc1_pow _
    have hgm_fix0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 =
        gm₀ 0 := congrFun hcpl.gm_eq.symm 0
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_fix
            (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, gm₀ 0), q_val)))
          (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, gm₀ 0), v_val)))
        (writeGMProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, 0), gm₀ 0 + 1)) := by
      dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
      simp only [p_bucketBits_mk, hb0, ↓reduceIte, readGMGenProg_mk, writeQuotGenProg_mk,
        writeValGenProg_mk, writeGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix h0_lt, hgm_fix0]
      repeat rw [StateTransitionSpec.clientState_bind]
    have hK1 : slabSize N = 1 := by simp [slabSize, slabBits, hb0]
    refine ⟨hframe, ?_, ?_⟩
    · rw [hs'_eq, hs_fix'_eq]
      unfold FixedCoupled
      have hgm3_0 : compGmAt metaBase U w N s₃.mem 0 = gm₀ 0 + 1 := by
        rw [hgm3, Function.update_self]
      have htot3 : epochTotalSlots N (compGmAt metaBase U w N s₃.mem) = gm₀ 0 + 1 := by
        unfold epochTotalSlots; rw [ite_eq_left hb0, hgm3_0]
      have htd3 : compTDAt metaBase U w N s₃.mem = compTDAt metaBase U w N s.mem := by
        refine hfr3.td_eq.trans ?_; rw [hs2_mem]; refine fv.2.2.1.trans ?_
        rw [hs1_mem]; exact fq.2.2.1
      have hdt3 : compDTAt metaBase U w N s₃.mem = compDTAt metaBase U w N s.mem := by
        refine hfr3.dt_eq.trans ?_; rw [hs2_mem]; refine fv.2.2.2.trans ?_
        rw [hs1_mem]; exact fq.2.2.2
      have hlm3 : compLmAt metaBase U w N s₃.mem = compLmAt metaBase U w N s.mem := by
        refine hfr3.lm_eq.trans ?_; rw [hs2_mem]; refine fv.1.trans ?_
        rw [hs1_mem]; exact fq.1
      refine ⟨hgm3.trans (by rw [hg_f3, hg_f2, hg_f1, ← hcpl.gm_eq]),
        hlm3.trans (by rw [hl_f3, hl_f2, hl_f1, ← hcpl.lm_eq]),
        by simp only [hb0, ↓reduceIte]; exact windowInv_zero _ _ _ _,
        fun i => by rw [htd3]; exact hcpl.td_lt i,
        fun i => by rw [hdt3]; exact hcpl.dt_lt i,
        fun idx hidx => ?_,
        fun idx hidx => ?_⟩
      · rw [htot3] at hidx ⊢
        rw [congrFun hfr3.quot_eq idx, hs2_mem, compQuotAt_writeCompVal henv.pos_w, hs1_mem,
          hq_f3, hq_f2, hq_f1]
        have hp_idx : physByBase N (compGmAt metaBase U w N s₃.mem 0 * slabSize N)
            (compDTAt metaBase U w N s₃.mem) idx = idx := by unfold physByBase; simp [hb0]
        rw [hp_idx]
        by_cases heq : idx = gm₀ 0
        · subst heq
          rw [compQuotAt_writeCompQuot_self s.mem (Nat.lt_succ_self _) hq_lt, Function.update_self]
        · have hlt0 : idx < gm₀ 0 := by omega
          rw [compQuotAt_writeCompQuot_of_ne henv.pos_w s.mem heq,
            compQuotAt_of_lt s.mem (by omega : idx < gm₀ 0 + 1) hlt0, Function.update_of_ne heq]
          have hq0 := hcpl.quot_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
          unfold epochTotalSlots physByBase at hq0; simp only [hb0, ↓reduceIte] at hq0
          exact hq0
      · rw [htot3] at hidx ⊢
        rw [congrFun hfr3.val_eq idx, hs2_mem, hs1_mem, hv_f3, hv_f2, hv_f1]
        have hp_idx : physByBase N (compGmAt metaBase U w N s₃.mem 0 * slabSize N)
            (compDTAt metaBase U w N s₃.mem) idx = idx := by unfold physByBase; simp [hb0]
        rw [hp_idx]
        by_cases heq : idx = gm₀ 0
        · subst heq
          rw [compValAt_writeCompVal_self _ (Nat.lt_succ_self _) hv_lt, Function.update_self]
        · have hlt0 : idx < gm₀ 0 := by omega
          rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq,
            compValAt_writeCompQuot henv.pos_w s.mem,
            compValAt_of_lt s.mem (by omega : idx < gm₀ 0 + 1) hlt0, Function.update_of_ne heq]
          have hv0 := hcpl.val_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
          unfold epochTotalSlots physByBase at hv0; simp only [hb0, ↓reduceIte] at hv0
          exact hv0
    · have hcost : memoryCost (compPushBackSlotGenProg d) s = 14 := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackSingleGenProg, writeCompItemGenProg]
        simp [hb0]
      have hpot' : slotPotential N (compGmAt metaBase U w N s'.mem) = 0 := by
        unfold slotPotential; simp [hb0]
      have hpot0 : slotPotential N gm₀ = 0 := by unfold slotPotential; simp [hb0]
      rw [hcost, hpot', hpot0]; omega
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    obtain ⟨hres_f1, _, _, _, _, htail_f1, hslab_f1, htot_f1, hqb_f1, hrb_f1, hother_f1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix
        hq_lt hv_lt
    set s₁ := (Memory.spec 0).clientState s (compPushBackTailWriteGenProg d)
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    have hgm0_rb_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
        (gmRIdx b) = gm₀ (gmRIdx b) := congrFun hcpl.gm_eq.symm (gmRIdx b)
    rw [hgm0_rb_eq] at hres_f1 hrb_f1
    by_cases hprom : gm₀ (gmRIdx b) + 1 = 2 * slabSize N
    · have hs'_eq : s' = (Memory.spec 0).clientState s₁
          (compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) := by
        dsimp only [s', d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1]
        change (Memory.spec 0).clientState s₁
          (if gm₀ (gmRIdx b) + 1 = 2 * slabSize N then
            compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
          else pure ()) = _
        rw [ite_eq_left hprom]
      have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
          (promoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
        dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, pushBackTailWriteGenProg_mk,
          p_twoSlabSize_mk, promoteSlabGenProg_mk]
        rw [StateTransitionSpec.clientState_bind, hres_f1, ite_eq_left hprom]
      have htot_f0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 *
          slabSize N + gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 < N := by
        unfold totalSlots at htot_fix; rw [ite_eq_right hb0] at htot_fix; exact htot_fix
      have hpre_prom : PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          0 b s_fix₁ := by
        refine ⟨hb, htail_f1, hslab_f1, by rw [hrb_f1, hprom], fun b' hb' hne => ?_, by omega⟩
        rw [(hother_f1 b' hb' hne).1, (hother_f1 b' hb' hne).2]
        exact hslot_fix.multi_r_bounds hb_pos b' hb'
      have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := by
        rw [hcpl1.gm_eq]; unfold totalSlots; rw [ite_eq_right hb0, htot_f1]
        have : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 * slabSize N +
            gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 + 1 ≤ m_cap := by
          rw [← hcpl.gm_eq]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
          exact hm_cap
        omega
      obtain ⟨hfr2, hcpl2, hcost2⟩ :=
        compPromoteSlab_effect (henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq]))
          hb_pos hpre_prom hcpl1 hm_cap1
      obtain ⟨_, _, _, _, hqb_f2, hrb_f2, hother_f2, _, _, _⟩ :=
        promoteSlabProg_effect hwg hb_pos s_fix₁ hpre_prom
      have hcost_tot : memoryCost (compPushBackSlotGenProg d) s ≤ 42 + (98 * slabSize N + 38) := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte,
          Realization.memoryCost_bind', memoryCost_compPushBackTailWriteGenProg]
        rw [hres1]
        change 42 + memoryCost (if gm₀ (gmRIdx b) + 1 = 2 * slabSize N then
            compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
          else pure ()) s₁ ≤ _
        rw [ite_eq_left hprom]
        omega
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_left hprom]
        rw [hs'_eq, hcpl2.gm_eq]
        exact ⟨hqb_f2.trans
          (congrArg (· + 1) (hqb_f1.trans (congrFun hcpl.gm_eq.symm (gmQIdx b)))), hrb_f2⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        rw [hs'_eq, hcpl2.gm_eq]
        exact ⟨(hother_f2 b' hb' hne).1.trans ((hother_f1 b' hb' hne).1.trans
            (congrFun hcpl.gm_eq.symm _)),
          (hother_f2 b' hb' hne).2.trans ((hother_f1 b' hb' hne).2.trans
            (congrFun hcpl.gm_eq.symm _))⟩
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize N) (gm₀ (gmRIdx b)) = slabSize N := by
        unfold pushBackWork; rw [ite_eq_left hprom]
      rw [hwork] at hpot
      exact ⟨by rw [hs'_eq]; exact hfr1.trans hfr2,
        by rw [hs'_eq, hs_fix'_eq]; exact hcpl2,
        by omega⟩
    · have hs'_eq : s' = s₁ := by
        dsimp only [s', d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1]
        change (Memory.spec 0).clientState s₁
          (if gm₀ (gmRIdx b) + 1 = 2 * slabSize N then
            compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
          else pure ()) = _
        rw [ite_eq_right hprom, StateTransitionSpec.clientState_pure]
      have hs_fix'_eq : s_fix' = s_fix₁ := by
        dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, pushBackTailWriteGenProg_mk,
          p_twoSlabSize_mk, promoteSlabGenProg_mk]
        rw [StateTransitionSpec.clientState_bind, hres_f1, ite_eq_right hprom,
          StateTransitionSpec.clientState_pure]
      have hcost_tot : memoryCost (compPushBackSlotGenProg d) s = 42 := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte,
          Realization.memoryCost_bind', memoryCost_compPushBackTailWriteGenProg]
        rw [hres1]
        change 42 + memoryCost (if gm₀ (gmRIdx b) + 1 = 2 * slabSize N then
            compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)
          else pure ()) s₁ = 42
        rw [ite_eq_right hprom, memoryCost_pure, Nat.add_zero]
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_right hprom, hs'_eq, hcpl1.gm_eq]
        exact ⟨hqb_f1.trans (congrFun hcpl.gm_eq.symm _), hrb_f1⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        rw [hs'_eq, hcpl1.gm_eq]
        exact ⟨(hother_f1 b' hb' hne).1.trans (congrFun hcpl.gm_eq.symm _),
          (hother_f1 b' hb' hne).2.trans (congrFun hcpl.gm_eq.symm _)⟩
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize N) (gm₀ (gmRIdx b)) = 0 := by
        unfold pushBackWork; rw [ite_eq_right hprom]
      rw [hwork, Nat.add_zero] at hpot
      exact ⟨by rw [hs'_eq]; exact hfr1,
        by rw [hs'_eq, hs_fix'_eq]; exact hcpl1,
        by omega⟩

private theorem realizesBounded_compPushBackMultiGen :
    RealizesBounded .exact compPushBackMultiGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackTailWritePre (fun _ _ => 0) := by
  have htw := realizesBounded_compPushBackTailWriteGen
  have hpr := realizesBounded_compPromoteSlabGen
  realize
  · exact h
  · rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, htot, hm_cap,
      hq_lt, hv_lt⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
    have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
    obtain ⟨_, _, _, _, _, htail_f1, hslab_f1, htot_f1, _, hrb_f1, hother_f1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix
        hq_lt hv_lt
    rw [hres1, cpTwoSlabSize_mk] at hc
    have htot_f0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 *
        slabSize N + gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 < N := by
      unfold totalSlots at htot_fix; rw [ite_eq_right hb0] at htot_fix; exact htot_fix
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    have hpre_prom : PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        0 b s_fix₁ := by
      refine ⟨hb, htail_f1, hslab_f1, ?_, fun b' hb' hne => ?_, by omega⟩
      · rw [hrb_f1, congrFun hcpl.gm_eq.symm (gmRIdx b), hc]
      · rw [(hother_f1 b' hb' hne).1, (hother_f1 b' hb' hne).2]
        exact hslot_fix.multi_r_bounds hb_pos b' hb'
    have hm_cap1 : totalSlots N (compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compPushBackTailWriteGenProg
            ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val))).mem) ≤ m_cap := by
      rw [hcpl1.gm_eq]; unfold totalSlots; rw [ite_eq_right hb0, htot_f1]
      have : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 * slabSize N +
          gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 + 1 ≤ m_cap := by
        rw [← hcpl.gm_eq]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
        exact hm_cap
      omega
    exact ⟨U, V, N, m_cap, s_fix₁, rfl,
      henv.of_mem_eq (by rw [hfr1.frontier_eq]),
      hb_pos, hpre_prom, hcpl1, hm_cap1⟩

private def CompPushBackSinglePre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), _q_val), _v_val), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      compGmAt metaBase U w N s.mem 0 < N ∧
      compGmAt metaBase U w N s.mem 0 < m_cap

private theorem realizesBounded_compPushBackSingleGen :
    RealizesBounded .exact compPushBackSingleGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackSinglePre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwit := realizesBounded_writeCompItemGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hc_lt_N, hc_lt_cap⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  · exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; exact h0_lt⟩
  all_goals try {
    change Fits w _
    exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U
  }
  · exact ⟨m_cap, henv.compItemEnv, hc_lt_cap⟩
  · refine ⟨(henv.of_mem_eq ?_).compMetaEnv, by simp only [cpN_mk]; exact h0_lt⟩
    change s.frontier ≤ ((Memory.spec 0).clientState s _).frontier
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]

theorem realizesBounded_compPushBackSlotGen :
    RealizesBounded .exact compPushBackSlotGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackSlotPre (fun _ _ => 0) := by
  have hsng := realizesBounded_compPushBackSingleGen
  have hmul := realizesBounded_compPushBackMultiGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩ := h)
  · rw [cpBucketBits_mk] at hc
    unfold totalSlots at htot hm_cap; rw [ite_eq_left hc] at htot hm_cap
    exact ⟨U, V, N, m_cap, rfl, henv, htot, by omega⟩
  · rw [cpBucketBits_mk] at hc
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, Nat.pos_of_ne_zero hc, hcpl, hslot, hb, htot,
      hm_cap, hq_lt, hv_lt⟩

theorem validProg_compPushBackSlotGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPushBackSlotPre w d s) :
    ValidProg w 0 s (compPushBackSlotGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compPushBackSlotGenProg, compPushBackSingleGenProg, compPushBackMultiGenProg]
  simp only [cpBucketBits_mk, cpTwoSlabSize_mk]
  refine validProg_ite (fun hb0 => ?_) (fun hb0 => ?_)
  · unfold totalSlots at hm_cap; rw [ite_eq_left hb0] at hm_cap
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h0_lt]
    set c0 := compGmAt metaBase U w N s.mem 0
    refine validProg_bind_unit
      (validProg_writeCompItemGen ⟨m_cap, henv.compItemEnv, by omega⟩) fun s2 hs2 => ?_
    have hf2 : s2.frontier = s.frontier := by
      rw [hs2]; dsimp only [writeCompItemGenProg]
      rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
        clientState_writeCompQuotGenProg]
    exact validProg_writeCompGMGen ⟨(henv.of_mem_eq (by rw [hf2])).compMetaEnv, h0_lt⟩
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    refine validProg_bind
      (validProg_compPushBackTailWriteGen
        ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩)
      ?_
    rw [hres1]
    refine validProg_ite (fun hprom => ?_) (fun _ => validProg_pure ())
    have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
    have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
    obtain ⟨_, _, _, _, _, htail_f1, hslab_f1, htot_f1, _, hrb_f1, hother_f1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix
        hq_lt hv_lt
    have htot_f0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 *
        slabSize N + gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 < N := by
      unfold totalSlots at htot_fix; rw [ite_eq_right hb0] at htot_fix; exact htot_fix
    have hpre_prom : PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b
        ((Memory.spec 0).clientState s_fix
          (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
            (((0, b), q_val), v_val))) := by
      refine ⟨hb, htail_f1, hslab_f1, ?_, fun b' hb' hne => ?_, by omega⟩
      · rw [hrb_f1, congrFun hcpl.gm_eq.symm (gmRIdx b), hprom]
      · rw [(hother_f1 b' hb' hne).1, (hother_f1 b' hb' hne).2]
        exact hslot_fix.multi_r_bounds hb_pos b' hb'
    have hm_cap1 : totalSlots N (compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compPushBackTailWriteGenProg
            ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val))).mem) ≤ m_cap := by
      rw [hcpl1.gm_eq]; unfold totalSlots; rw [ite_eq_right hb0, htot_f1]
      have : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 * slabSize N +
          gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 + 1 ≤ m_cap := by
        rw [← hcpl.gm_eq]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
        exact hm_cap
      omega
    exact validProg_compPromoteSlabGen ⟨U, V, N, m_cap, _, rfl,
      henv.of_mem_eq (by rw [hfr1.frontier_eq]), hb_pos, hpre_prom, hcpl1, hm_cap1⟩

private def compPopBackSingleGenProg : CompParams × ℕ → Memory.Prog Unit
  | (cp, metaBase) => do
    let c ← readCompGMGenProg ((cp, metaBase), 0)
    writeCompGMGenProg (((cp, metaBase), 0), c - 1)

private def compPopBackFinishProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), b), (r_b_new, q_b)) =>
    if r_b_new = 0 then
      if 0 < q_b then
        compDemoteSlabGenProg ((cp, (metaBase, itemBase)), b)
      else
        pure ()
    else
      pure ()

private def compPopBackMultiGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    compRemoveLastTailItemGenProg ((cp, (metaBase, itemBase)), b)
    let q_idx := 4 + (b + b + b)
    let r_b_new ← readCompGMGenProg ((cp, metaBase), q_idx + 1)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    compPopBackFinishProg (((cp, (metaBase, itemBase)), b), (r_b_new, q_b))

/-- Remove the last logical slot `bCount N gm b - 1` of non-empty bucket `b` in compacted layout
`(metaBase, itemBase)`, demoting the top full slab into `K = slabSize N` tail items when
`r_b - 1 = 0 ∧ 0 < q_b` (`¬ReadsWidth`). -/
def compPopBackSlotGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) =>
    if cpBucketBits cp = 0 then
      compPopBackSingleGenProg (cp, metaBase)
    else
      compPopBackMultiGenProg ((cp, (metaBase, itemBase)), b)

/-- Precondition for `compPopBackSlotGenProg`. -/
@[expose] def CompPopBackSlotPre (w : ℕ) : (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

/-- `compPopBackSlotGenProg` maintains `FixedCoupled` with `popBackSlotProg`, preserves outside
memory via `CompOpFrame`, and satisfies the `O(1)` amortized `memoryCost` bound against
`98 * slotPotential N gm`. -/
theorem compPopBackSlotGenProg_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    let s' := (Memory.spec 0).clientState s (compPopBackSlotGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compPopBackSlotGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 242 := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  by_cases hb0 : bucketBits N = 0
  · have hb_eq : b = 0 := by
      have hnb : numBuckets N = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    unfold bCount at hbc; simp only [hb0, ↓reduceIte] at hbc
    have hgm0_le : gm₀ 0 ≤ N := hslot.single_valid hb0
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hc_pow : gm₀ 0 - 1 < 2 ^ globalPtrBits N :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set s₁ := (Memory.spec 0).clientState s
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm₀ 0 - 1))
    have hs'_eq : s' = s₁ := by
      dsimp only [s', d, compPopBackSlotGenProg, compPopBackSingleGenProg]
      simp only [cpBucketBits_mk, hb0, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg]
    obtain ⟨hfr1, hgm1⟩ := compGmFrame_writeCompGMGenProg (metaBase := metaBase)
      (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := gm₀ 0)
      (idx := 0) (val := gm₀ 0 - 1) henv.pos_w henv.meta_le_item h0_lt hc_pow s
    obtain ⟨_, _, hq_f1, hv_f1, hl_f1, hg_f1⟩ :=
      writeGMProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg h0_lt hc_pow s_fix
    have hgm_fix0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 =
        gm₀ 0 := congrFun hcpl.gm_eq.symm 0
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix
        (writeGMProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, 0), gm₀ 0 - 1)) := by
      dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
      simp only [p_bucketBits_mk, hb0, ↓reduceIte, readGMGenProg_mk, writeGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix h0_lt, hgm_fix0]
    refine ⟨by rw [hs'_eq]; exact CompOpFrame.of_gmFrame hfr1, ?_, ?_⟩
    · rw [hs'_eq, hs_fix'_eq]
      unfold FixedCoupled
      have hgm1_0 : compGmAt metaBase U w N s₁.mem 0 = gm₀ 0 - 1 := by
        rw [hgm1, Function.update_self]
      have htot1 : epochTotalSlots N (compGmAt metaBase U w N s₁.mem) = gm₀ 0 - 1 := by
        unfold epochTotalSlots; rw [ite_eq_left hb0, hgm1_0]
      refine ⟨hgm1.trans (by rw [hg_f1, ← hcpl.gm_eq]),
        hfr1.lm_eq.trans (by rw [hl_f1, ← hcpl.lm_eq]),
        by simp only [hb0, ↓reduceIte]; exact windowInv_zero _ _ _ _,
        fun i => by rw [hfr1.td_eq]; exact hcpl.td_lt i,
        fun i => by rw [hfr1.dt_eq]; exact hcpl.dt_lt i,
        fun idx hidx => ?_,
        fun idx hidx => ?_⟩
      · rw [htot1] at hidx ⊢
        have hlt0 : idx < gm₀ 0 := by omega
        rw [compQuotAt_of_lt s₁.mem hidx hlt0, congrFun hfr1.quot_eq idx, hq_f1]
        have hq0 := hcpl.quot_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
        unfold epochTotalSlots at hq0
        unfold physByBase at hq0 ⊢
        simp only [hb0, ↓reduceIte] at hq0 ⊢
        exact hq0
      · rw [htot1] at hidx ⊢
        have hlt0 : idx < gm₀ 0 := by omega
        rw [compValAt_of_lt s₁.mem hidx hlt0, congrFun hfr1.val_eq idx, hv_f1]
        have hv0 := hcpl.val_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
        unfold epochTotalSlots at hv0
        unfold physByBase at hv0 ⊢
        simp only [hb0, ↓reduceIte] at hv0 ⊢
        exact hv0
    · have hcost : memoryCost (compPopBackSlotGenProg d) s = 6 := by
        dsimp only [d, compPopBackSlotGenProg, compPopBackSingleGenProg]; simp [hb0]
      have hpot' : slotPotential N (compGmAt metaBase U w N s'.mem) = 0 := by
        unfold slotPotential; simp [hb0]
      have hpot0 : slotPotential N gm₀ = 0 := by unfold slotPotential; simp [hb0]
      rw [hcost, hpot', hpot0]; omega
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hr_pos : 1 ≤ gm₀ (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    have hr2_lt : gm₀ (gmRIdx b) < 2 * slabSize N := by
      have := (hslot.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this; rw [ite_eq_right hb0] at this; exact this
    obtain ⟨hfr1, hcpl1⟩ :=
      compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    obtain ⟨_, _, _, _, _, hgm_f1⟩ :=
      removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
        (hslot_fix.multi_tail hb_pos) (by rw [← hcpl.gm_eq]; exact hr_pos)
    set s₁ := (Memory.spec 0).clientState s (compRemoveLastTailItemGenProg d)
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    have hgm1_eq : compGmAt metaBase U w N s₁.mem = gmRemoveTail N gm₀ b :=
      hcpl1.gm_eq.trans (hgm_f1.trans (congrArg (fun g => gmRemoveTail N g b) hcpl.gm_eq.symm))
    have htail₀ := hslot.multi_tail hb_pos
    have hslab₀ := hslot.multi_slab hb_pos
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr_pos htail₀
    have htail1 := tailBijection_gmRemoveTail hb hr_pos htail₀
    have ⟨_, hslab1⟩ := slabBijection_gmRemoveTail hb hr_pos htail₀ hslab₀
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    have hq_eq_fix : 4 + 3 * b = gmQIdx b := rfl
    have hr_eq_fix : gmQIdx b + 1 = gmRIdx b := rfl
    have hrb1_s : compGmAt metaBase U w N s₁.mem (gmRIdx b) = gm₀ (gmRIdx b) - 1 := by
      rw [hgm1_eq, hpres1.2.2.1]
    have hqb1_s : compGmAt metaBase U w N s₁.mem (gmQIdx b) = gm₀ (gmQIdx b) := by
      rw [hgm1_eq, hpres1.2.2.2.2.1 b hb]
    have hrb1_f : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem (gmRIdx b) =
        gm₀ (gmRIdx b) - 1 := by rw [← hcpl1.gm_eq, hrb1_s]
    have hqb1_f : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem (gmQIdx b) =
        gm₀ (gmQIdx b) := by rw [← hcpl1.gm_eq, hqb1_s]
    by_cases hr0 : gm₀ (gmRIdx b) - 1 = 0
    · by_cases hq_pos : 0 < gm₀ (gmQIdx b)
      · have hs'_eq : s' = (Memory.spec 0).clientState s₁ (compDemoteSlabGenProg d) := by
          dsimp only [s', d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
          simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
            StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
            clientState_readCompGMGenProg, hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_left hq_pos]
        have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
            (demoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
          dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
          simp only [p_bucketBits_mk, hb0, ↓reduceIte, removeLastTailItemGenProg_mk,
            readGMGenProg_mk, demoteSlabGenProg_mk, hq_eq_fix, hr_eq_fix]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            clientState_readGMProg, clientResult_readGMProg s_fix₁ hr_idx_lt,
            StateTransitionSpec.clientState_bind, clientState_readGMProg,
            clientResult_readGMProg s_fix₁ hq_idx_lt, hrb1_f, hqb1_f,
            ite_eq_left hr0, ite_eq_left hq_pos]
        have hSN0 := hslot.multi_total_le hb_pos
        have hpre_dem : DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N)
            0 b s_fix₁ := by
          refine ⟨hb, ?_, ?_, ?_, ?_, fun b' hb' hne => ?_, ?_⟩
          · rw [← hcpl1.gm_eq, hgm1_eq]; exact htail1
          · rw [← hcpl1.gm_eq, hgm1_eq]; exact hslab1
          · rw [hrb1_f, hr0]
          · rw [hqb1_f]; omega
          · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.1 b' hb' hne, hpres1.2.2.2.2.1 b' hb']
            exact hslot.multi_r_bounds hb_pos b' hb'
          · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.1, hpres1.2.1]; omega
        have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := by
          unfold totalSlots at hm_cap ⊢; rw [ite_eq_right hb0] at hm_cap ⊢
          rw [hgm1_eq, hpres1.1, hpres1.2.1]; omega
        obtain ⟨hfr2, hcpl2, hcost2⟩ :=
          compDemoteSlab_effect (henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq]))
            hb_pos hpre_dem hcpl1 hm_cap1
        obtain ⟨_, _, _, _, hqb_f2, hrb_f2, hother_f2, _, _, _⟩ :=
          demoteSlabProg_effect hwg hb_pos s_fix₁ hpre_dem
        have hcost_tot : memoryCost (compPopBackSlotGenProg d) s ≤ 76 + (58 * slabSize N + 68) := by
          dsimp only [d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
          simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq,
            Realization.memoryCost_bind', memoryCost_compRemoveLastTailItemGenProg,
            memoryCost_readCompGMGenProg]
          rw [clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
            clientResult_readCompGMGenProg hq_idx_lt, clientState_readCompGMGenProg,
            hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_left hq_pos]
          dsimp only [s₁, d] at hcost2
          omega
        have hr1_eq : gm₀ (gmRIdx b) = 1 := by omega
        have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
              (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
            compGmAt metaBase U w N s'.mem (gmRIdx b) =
              (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
          unfold popBackCounts
          rw [hr1_eq, ite_eq_left ⟨rfl, hq_pos⟩, hs'_eq, hcpl2.gm_eq]
          exact ⟨hqb_f2.trans (congrArg (· - 1) hqb1_f), hrb_f2⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
            compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
          intro b' hb' hne
          rw [hs'_eq, hcpl2.gm_eq]
          exact ⟨(hother_f2 b' hb' hne).1.trans (by
              rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.2.1 b' hb']),
            (hother_f2 b' hb' hne).2.trans (by
              rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.1 b' hb' hne])⟩
        have hpot := slotPotential_popBack_le hb_pos hb hr_pos hr2_lt hupd hother_all
        have hwork : popBackWork (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b)) = slabSize N := by
          unfold popBackWork; rw [hr1_eq, ite_eq_left ⟨rfl, hq_pos⟩]
        rw [hwork] at hpot
        have h58_le : 58 * slabSize N ≤ 98 * slabSize N := Nat.mul_le_mul_right _ (by decide)
        exact ⟨by rw [hs'_eq]; exact hfr1.trans hfr2,
          by rw [hs'_eq, hs_fix'_eq]; exact hcpl2,
          by omega⟩
      · have hs'_eq : s' = s₁ := by
          dsimp only [s', d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
          simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
            StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
            clientState_readCompGMGenProg, hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_right hq_pos,
            StateTransitionSpec.clientState_pure]
        have hs_fix'_eq : s_fix' = s_fix₁ := by
          dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
          simp only [p_bucketBits_mk, hb0, ↓reduceIte, removeLastTailItemGenProg_mk,
            readGMGenProg_mk, demoteSlabGenProg_mk, hq_eq_fix, hr_eq_fix]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            clientState_readGMProg, clientResult_readGMProg s_fix₁ hr_idx_lt,
            StateTransitionSpec.clientState_bind, clientState_readGMProg,
            clientResult_readGMProg s_fix₁ hq_idx_lt, hrb1_f, hqb1_f,
            ite_eq_left hr0, ite_eq_right hq_pos, StateTransitionSpec.clientState_pure]
        have hcost_tot : memoryCost (compPopBackSlotGenProg d) s = 76 := by
          dsimp only [d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
          simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq,
            Realization.memoryCost_bind', memoryCost_compRemoveLastTailItemGenProg,
            memoryCost_readCompGMGenProg]
          rw [clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
            clientResult_readCompGMGenProg hq_idx_lt, clientState_readCompGMGenProg,
            hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_right hq_pos, memoryCost_pure, Nat.add_zero]
        have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
              (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
            compGmAt metaBase U w N s'.mem (gmRIdx b) =
              (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
          unfold popBackCounts
          rw [ite_eq_right (fun h => hq_pos h.2), hs'_eq, hqb1_s, hrb1_s]; exact ⟨rfl, rfl⟩
        have hother_all : ∀ b' < numBuckets N, b' ≠ b →
            compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
            compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
          intro b' hb' hne
          rw [hs'_eq, hgm1_eq]
          exact ⟨hpres1.2.2.2.2.1 b' hb', hpres1.2.2.2.1 b' hb' hne⟩
        have hpot := slotPotential_popBack_le hb_pos hb hr_pos hr2_lt hupd hother_all
        have hwork : popBackWork (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b)) = 0 := by
          unfold popBackWork; rw [ite_eq_right (fun h => hq_pos h.2)]
        rw [hwork, Nat.add_zero] at hpot
        exact ⟨by rw [hs'_eq]; exact hfr1,
          by rw [hs'_eq, hs_fix'_eq]; exact hcpl1,
          by omega⟩
    · have hs'_eq : s' = s₁ := by
        dsimp only [s', d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
          clientState_readCompGMGenProg, hrb1_s, ite_eq_right hr0,
          StateTransitionSpec.clientState_pure]
      have hs_fix'_eq : s_fix' = s_fix₁ := by
        dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, removeLastTailItemGenProg_mk,
          readGMGenProg_mk, demoteSlabGenProg_mk, hq_eq_fix, hr_eq_fix]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientState_readGMProg, clientResult_readGMProg s_fix₁ hr_idx_lt,
          StateTransitionSpec.clientState_bind, clientState_readGMProg,
          clientResult_readGMProg s_fix₁ hq_idx_lt, hrb1_f,
          ite_eq_right hr0, StateTransitionSpec.clientState_pure]
      have hcost_tot : memoryCost (compPopBackSlotGenProg d) s = 76 := by
        dsimp only [d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq,
          Realization.memoryCost_bind', memoryCost_compRemoveLastTailItemGenProg,
          memoryCost_readCompGMGenProg]
        rw [clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          clientResult_readCompGMGenProg hq_idx_lt, clientState_readCompGMGenProg,
          hrb1_s, ite_eq_right hr0, memoryCost_pure, Nat.add_zero]
      have hne1 : gm₀ (gmRIdx b) ≠ 1 := fun h1 => hr0 (by omega)
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold popBackCounts
        rw [ite_eq_right (fun h => hne1 h.1), hs'_eq, hqb1_s, hrb1_s]; exact ⟨rfl, rfl⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        rw [hs'_eq, hgm1_eq]
        exact ⟨hpres1.2.2.2.2.1 b' hb', hpres1.2.2.2.1 b' hb' hne⟩
      have hpot := slotPotential_popBack_le hb_pos hb hr_pos hr2_lt hupd hother_all
      have hwork : popBackWork (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b)) = 0 := by
        unfold popBackWork; rw [ite_eq_right (fun h => hne1 h.1)]
      rw [hwork, Nat.add_zero] at hpot
      exact ⟨by rw [hs'_eq]; exact hfr1,
        by rw [hs'_eq, hs_fix'_eq]; exact hcpl1,
        by omega⟩

private def CompPopBackFinishPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), (r_b_new, q_b)), s =>
    CompMetaEnv w cp metaBase s ∧
    (r_b_new = 0 → 0 < q_b → CompDemoteSlabPre w ((cp, (metaBase, itemBase)), b) s)

private theorem realizesBounded_compPopBackFinish :
    RealizesBounded .exact compPopBackFinishProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompPopBackFinishPre (fun _ _ => 0) := by
  have hdm := realizesBounded_compDemoteSlabGen
  realize
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨r_b_new, q_b⟩⟩
  dsimp only at *
  exact h.2 ‹r_b_new = 0› ‹0 < q_b›

private theorem compDemoteSlabPre_of_removeTail {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hr0_eq : compGmAt metaBase U w N
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))).mem
      (gmRIdx b) = 0)
    (hq_pos_eq : 0 < compGmAt metaBase U w N
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))).mem
      (gmQIdx b)) :
    CompDemoteSlabPre w ((mkCompParams U V w N, (metaBase, itemBase)), b)
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))) := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  obtain ⟨hfr1, hcpl1⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
  set s₁ := (Memory.spec 0).clientState s
    (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  obtain ⟨_, _, _, _, _, hgm_f1⟩ :=
    removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
      (hslot_fix.multi_tail hb_pos) (by rw [← hcpl.gm_eq]; exact hr_pos)
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
  have hgm1_eq : compGmAt metaBase U w N s₁.mem =
      gmRemoveTail N (compGmAt metaBase U w N s.mem) b :=
    hcpl1.gm_eq.trans (hgm_f1.trans (congrArg (fun g => gmRemoveTail N g b) hcpl.gm_eq.symm))
  have htail₀ := hslot.multi_tail hb_pos
  have hslab₀ := hslot.multi_slab hb_pos
  have hpres1 := gmRemoveTail_preserves_nonTail hb hr_pos htail₀
  have htail1 := tailBijection_gmRemoveTail hb hr_pos htail₀
  have ⟨_, hslab1⟩ := slabBijection_gmRemoveTail hb hr_pos htail₀ hslab₀
  have hSN0 := hslot.multi_total_le hb_pos
  have hpre_dem : DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix₁ := by
    refine ⟨hb, ?_, ?_, ?_, ?_, fun b' hb' hne => ?_, ?_⟩
    · rw [← hcpl1.gm_eq, hgm1_eq]; exact htail1
    · rw [← hcpl1.gm_eq, hgm1_eq]; exact hslab1
    · rw [← hcpl1.gm_eq]; exact hr0_eq
    · rw [← hcpl1.gm_eq]; exact hq_pos_eq
    · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.1 b' hb' hne, hpres1.2.2.2.2.1 b' hb']
      exact hslot.multi_r_bounds hb_pos b' hb'
    · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.1, hpres1.2.1]; omega
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := by
    unfold totalSlots at hm_cap ⊢; rw [ite_eq_right hb0] at hm_cap ⊢
    rw [hgm1_eq, hpres1.1, hpres1.2.1]; omega
  exact ⟨U, V, N, m_cap, s_fix₁, rfl, henv.of_mem_eq (by rw [hfr1.frontier_eq]),
    hb_pos, hpre_dem, hcpl1, hm_cap1⟩

private theorem realizesBounded_compPopBackMultiGen :
    RealizesBounded .exact compPopBackMultiGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompRemoveLastTailPre (fun _ _ => 0) := by
  have hrm := realizesBounded_compRemoveLastTailItemGen
  have hrgm := realizesBounded_readCompGMGen
  have hfin := realizesBounded_compPopBackFinish
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hr_lt := gmRIdx_lt hb_pos hb
    have hq_lt := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl)
  · exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩
  all_goals try {
    change Fits w _
    refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
    unfold gmRIdx gmQIdx at *; omega
  }
  · obtain ⟨hfr1, _⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    exact ⟨(henv.of_mem_eq (by rw [hfr1.frontier_eq])).compMetaEnv,
      by simp only [cpN_mk, hq_eq, hr_eq]; exact hr_lt⟩
  · obtain ⟨hfr1, _⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    exact ⟨(henv.of_mem_eq (by
      rw [clientState_readCompGMGenProg, hfr1.frontier_eq])).compMetaEnv,
      by simp only [cpN_mk, hq_eq]; exact hq_lt⟩
  · obtain ⟨hfr1, _⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    simp only [hq_eq, hr_eq]
    rw [clientResult_readCompGMGenProg hr_lt, clientState_readCompGMGenProg,
      clientResult_readCompGMGenProg hq_lt, clientState_readCompGMGenProg]
    exact ⟨(henv.of_mem_eq (by rw [hfr1.frontier_eq])).compMetaEnv, fun hr0_eq hq_pos_eq =>
      compDemoteSlabPre_of_removeTail henv hb_pos hcpl hslot hb hr_pos hm_cap hr0_eq hq_pos_eq⟩

private def CompPopBackSinglePre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      1 ≤ compGmAt metaBase U w N s.mem 0

private theorem realizesBounded_compPopBackSingleGen :
    RealizesBounded .exact compPopBackSingleGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := Unit))
      CompPopBackSinglePre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hc_pos⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact h0_lt⟩
  · rw [clientResult_readCompGMGenProg h0_lt]; exact hc_pos
  · rw [clientState_readCompGMGenProg]
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact h0_lt⟩

theorem realizesBounded_compPopBackSlotGen :
    RealizesBounded .exact compPopBackSlotGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPopBackSlotPre (fun _ _ => 0) := by
  have hsng := realizesBounded_compPopBackSingleGen
  have hmul := realizesBounded_compPopBackMultiGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, hbc, hm_cap⟩ := h)
  · rw [cpBucketBits_mk] at hc
    have hb_eq : b = 0 := by
      have hnb : numBuckets N = 1 := by simp [numBuckets, hc]
      omega
    subst hb_eq
    unfold bCount at hbc; simp only [hc, ↓reduceIte] at hbc
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hbc⟩
  · rw [cpBucketBits_mk] at hc
    have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hc
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb,
      pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc, hm_cap⟩

theorem validProg_compPopBackSlotGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPopBackSlotPre w d s) :
    ValidProg w 0 s (compPopBackSlotGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, hbc, hm_cap⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compPopBackSlotGenProg, compPopBackSingleGenProg, compPopBackMultiGenProg,
    compPopBackFinishProg]
  simp only [cpBucketBits_mk]
  refine validProg_ite (fun _ => ?_) (fun hb0 => ?_)
  · refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_writeCompGMGen ⟨henv.compMetaEnv, h0_lt⟩
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hwg : 0 < ghostW w := by unfold ghostW; omega
    have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    obtain ⟨hfr1, hcpl1⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    refine validProg_bind
      (validProg_compRemoveLastTailItemGen
        ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩)
      ?_
    set s₁ := (Memory.spec 0).clientState s
      (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
    have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
    have hq_lt := gmQIdx_lt hb_pos hb
    have hr_lt := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    rw [hq_eq, hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨henv1.compMetaEnv, hr_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv1.compMetaEnv, hq_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
    refine validProg_ite (fun hr0_eq => ?_) (fun _ => validProg_pure ())
    refine validProg_ite (fun hq_pos_eq => ?_) (fun _ => validProg_pure ())
    exact validProg_compDemoteSlabGen
      (compDemoteSlabPre_of_removeTail henv hb_pos hcpl hslot hb hr_pos hm_cap hr0_eq hq_pos_eq)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
