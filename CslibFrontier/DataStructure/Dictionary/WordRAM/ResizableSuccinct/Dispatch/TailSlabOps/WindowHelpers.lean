/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Internal `WindowCoupled` Bijection, Frame, and Dense Item Write Helpers

Shared internal `CompOpFrame` constructors, `TailBijection` / `SlabBijection` / `SlotStoreInv`
congruence helpers, `WindowCoupled` circular-window write/copy/shrink lemmas, and
`writeCompItemGenProg`.
-/

-- This proof-only companion is intentionally private; sibling `TailSlabOps` modules use
-- `import all`.
set_option linter.privateModule false

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

private theorem CompOpFrame.of_gmFrame {metaBase itemBase U V w N m_items m_cap : ℕ}
    {s s' : Memory.State} (h : CompGmFrame metaBase itemBase U V w N m_items s s') :
    CompOpFrame metaBase itemBase U V w N m_cap s s' := by
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h2 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨h.frontier_eq, fun a hm _ => h.outside_eq a (by omega)⟩

private theorem tailBijection_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (htail : TailBijection N gm₂ (fun b' => gm₂ (gmRIdx b')) (gm₂ 1)) :
    TailBijection N gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) := h ▸ htail

private theorem slabBijection_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (hslab : SlabBijection N gm₂ (fun b' => gm₂ (gmQIdx b')) (gm₂ 0)) :
    SlabBijection N gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) := h ▸ hslab

private theorem slotStoreInv_of_gm_eq {N : ℕ} {gm₁ gm₂ : ℕ → ℕ} (h : gm₁ = gm₂)
    (hs : SlotStoreInv N gm₂) :
    SlotStoreInv N gm₁ := h ▸ hs

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
  have hK : 0 < slabSize N := slabSize_pos N
  unfold maxTailItems tailCapPerBucket
  rw [ite_eq_right hb_pos.ne']
  exact Nat.mul_pos (numBuckets_pos N) (by omega)

private theorem physByBase_slab {N b_win : ℕ} (dt : ℕ → ℕ) {g : ℕ} (hg : g < b_win) :
    physByBase N b_win dt g = g := by
  unfold physByBase; split_ifs <;> rfl

private theorem physByBase_tail_denseOfCirc {N b_win n_win : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b_win n_win td dt)
    {t : ℕ} (ht : t < n_win) :
    let d := denseOfCirc (maxTailItems N) b_win (td t)
    b_win ≤ d ∧ d < b_win + n_win ∧ physByBase N b_win dt d = N - 1 - t := by
  intro d
  refine ⟨denseOfCirc_ge (maxTailItems N) b_win (td t), hw.dense_lt t ht, ?_⟩
  unfold physByBase
  rw [ite_eq_right hb_pos.ne', ite_eq_right (Nat.not_lt.mpr (denseOfCirc_ge _ _ _)),
    denseOfCirc_mod (maxTailItems_pos_of_bucketBits_pos hb_pos) (hw.td_lt t ht), hw.dt_td t ht]

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
    · obtain ⟨ht_lt, _⟩ := hw.owner_valid d (by omega) hd
      unfold physByBase
      rw [ite_eq_right hb0, ite_eq_right hlt]
      exact Or.inr ⟨by omega, by omega, by omega⟩
  refine ⟨hrng, fun d₁ hd₁ d₂ hd₂ heq => ?_⟩
  rcases hrng d₁ hd₁ with ⟨h1, hp1⟩ | ⟨h1, hlo1, _⟩ <;>
    rcases hrng d₂ hd₂ with ⟨h2, hp2⟩ | ⟨h2, hlo2, _⟩ <;> try omega
  obtain ⟨ht1, htd1⟩ := hw.owner_valid d₁ h1 hd₁
  obtain ⟨ht2, htd2⟩ := hw.owner_valid d₂ h2 hd₂
  unfold physByBase at heq
  rw [ite_eq_right hb0, ite_eq_right (Nat.not_lt.mpr h1),
    ite_eq_right hb0, ite_eq_right (Nat.not_lt.mpr h2)] at heq
  have hdt_eq : dt (d₁ % maxTailItems N) = dt (d₂ % maxTailItems N) := by omega
  have hmod_eq : d₁ % maxTailItems N = d₂ % maxTailItems N :=
    htd1.symm.trans ((congrArg td hdt_eq).trans htd2)
  rw [← denseOfCirc_mod_self hM_pos h1 (hd₁.trans_le (Nat.add_le_add_left hM b_win)),
    ← denseOfCirc_mod_self hM_pos h2 (hd₂.trans_le (Nat.add_le_add_left hM b_win)), hmod_eq]

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
  have htd_s : compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem := htd2.trans htd1
  have hdt_s : compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem := hdt2.trans hdt1
  have hinj := (physByBase_range_and_inj hb_pos hbn hM hcpl.win_inv).2
  refine ⟨hgm2.trans (hgm1.trans (hcpl.gm_eq.trans hgm_fix.symm)),
    hlm2.trans (hlm1.trans (hcpl.lm_eq.trans hlm_fix.symm)),
    htd_s.symm ▸ hdt_s.symm ▸ hcpl.win_inv,
    fun i => htd_s.symm ▸ hcpl.td_lt i,
    fun i => hdt_s.symm ▸ hcpl.dt_lt i,
    fun d' hd' => ?_,
    fun d' hd' => ?_⟩
  · dsimp only [s']
    rw [compQuotAt_writeCompVal hw, hdt_s, hq_fix]
    by_cases hdeq : d' = d
    · rw [hdeq, compQuotAt_writeCompQuot_self s.mem hd hq_lt, hg, Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq,
        Function.update_of_ne (fun hp => hdeq (hinj d' hd' d hd (hp.trans hg.symm)))]
      exact hcpl.quot_eq d' hd'
  · dsimp only [s']
    rw [hdt_s, hv_fix]
    by_cases hdeq : d' = d
    · rw [hdeq, compValAt_writeCompVal_self _ hd hv_lt, hg, Function.update_self]
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
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src :=
    (hcpl.quot_eq src hsrc).trans (congrArg _ hg_src)
  have hv_eq : compValAt itemBase U V w N (b_win + n_win) s.mem src =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_src :=
    (hcpl.val_eq src hsrc).trans (congrArg _ hg_src)
  exact windowCoupled_write_at hw hitem hb_pos hbn hM hcpl hdst hg_dst
    (hq_eq.trans_lt (quotAt_lt _ _ _ _ _ _ _)) (hv_eq.trans_lt (valAt_lt _ _ _ _ _ _ _ _))
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
  have hmax_eq : max M 1 = M := Nat.max_eq_left (maxTailItems_pos_of_bucketBits_pos hb_pos)
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
  have hs1_mem : s₁.mem = _ := congrArg Memory.State.mem hs1_eq
  have hgm1 := (congrArg (compGmAt metaBase U w N) hs1_mem).trans (hgm_c2.trans hgm_c1)
  have hlm1 := (congrArg (compLmAt metaBase U w N) hs1_mem).trans (hlm_c2.trans hlm_c1)
  have htd1 := (congrArg (compTDAt metaBase U w N) hs1_mem).trans (htd_c2.trans htd_c1)
  have hdt1 := (congrArg (compDTAt metaBase U w N) hs1_mem).trans (hdt_c2.trans hdt_c1)
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
      2 ^ quotientBits U N :=
    (hcpl.quot_eq _ hbn_lt).trans_lt (quotAt_lt _ _ _ _ _ _ _)
  have hv_bn_lt : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem (b_win + n') <
      2 ^ valBits V :=
    (hcpl.val_eq _ hbn_lt).trans_lt (valAt_lt _ _ _ _ _ _ _ _)
  refine ⟨hgm2.trans (hgm1.trans hcpl.gm_eq),
    hlm2.trans (hlm1.trans hcpl.lm_eq),
    by rw [htd2, hdt2]; exact hspec.1,
    fun i => by rw [htd2, hmax_eq]; exact hspec.2.1 i,
    fun i => by rw [hdt2, hmax_eq]; exact hspec.2.2 i,
    fun d hd => ?_,
    fun d hd => ?_⟩
  · have hd' : d < b_win + (n' + 1) := by omega
    rw [congrFun hq2 d, hdt2, compQuotAt_of_lt s₁.mem hd hd', hs1_mem, compQuotAt_writeCompVal hw]
    by_cases hdeq : d = d_last
    · rw [hdeq, compQuotAt_writeCompQuot_self s.mem hd_last_lt hq_bn_lt, hp.2.1]
      exact hcpl.quot_eq (b_win + n') hbn_lt
    · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdeq, hp.2.2 d hd hdeq]
      exact hcpl.quot_eq d hd'
  · have hd' : d < b_win + (n' + 1) := by omega
    rw [congrFun hv2 d, hdt2, compValAt_of_lt s₁.mem hd hd', hs1_mem]
    by_cases hdeq : d = d_last
    · rw [hdeq, compValAt_writeCompVal_self _ hd_last_lt hv_bn_lt, hp.2.1]
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
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N :=
    Nat.max_eq_left (maxTailItems_pos_of_bucketBits_pos hb_pos)
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
  have hs1_mem : s₁.mem = _ := congrArg Memory.State.mem hs1_eq
  have hgm1 := (congrArg (compGmAt metaBase U w N) hs1_mem).trans (hgm_c2.trans hgm_c1)
  have hlm1 := (congrArg (compLmAt metaBase U w N) hs1_mem).trans (hlm_c2.trans hlm_c1)
  have htd1 := (congrArg (compTDAt metaBase U w N) hs1_mem).trans (htd_c2.trans htd_c1)
  have hdt1 := (congrArg (compDTAt metaBase U w N) hs1_mem).trans (hdt_c2.trans hdt_c1)
  have htd_b (i) : compTDAt metaBase U w N s.mem i < maxTailItems N := hmax_eq ▸ hcpl.td_lt i
  have hdt_b (i) : compDTAt metaBase U w N s.mem i < maxTailItems N := hmax_eq ▸ hcpl.dt_lt i
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
  have htd_s3 := htd4.trans (htd3.trans htd2)
  have hdt_s3 := hdt4.trans (hdt3.trans hdt2)
  have hq_b_lt : compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win <
      2 ^ quotientBits U N :=
    (hcpl.quot_eq _ hb_lt).trans_lt (quotAt_lt _ _ _ _ _ _ _)
  have hv_b_lt : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem b_win < 2 ^ valBits V :=
    (hcpl.val_eq _ hb_lt).trans_lt (valAt_lt _ _ _ _ _ _ _ _)
  have hp_ne_bwin : ∀ d < (b_win + 1) + n', d ≠ b_win →
      physByBase N (b_win + 1) (compDTAt metaBase U w N s₃.mem) d ≠ b_win := fun d hd hneb => by
    rw [hdt_s3]
    rcases (physByBase_range_and_inj hb_pos (hm_eq.symm ▸ hbn) (Nat.le_of_succ_le hM) hspec.1).1
      d hd with ⟨_, hp_eq⟩ | ⟨_, _, _⟩ <;> omega
  have hp_b : physByBase N b_win (compDTAt metaBase U w N s.mem) b_win =
      N - 1 - compDTAt metaBase U w N s.mem (b_win % maxTailItems N) := by
    unfold physByBase
    rw [ite_eq_right hb_pos.ne', ite_eq_right (Nat.lt_irrefl b_win)]
  refine ⟨hgm4.trans (hgm3.trans (hgm2.trans (hgm1.trans (hcpl.gm_eq.trans hgm_fix.symm)))),
    hlm4.trans (hlm3.trans (hlm2.trans (hlm1.trans (hcpl.lm_eq.trans hlm_fix.symm)))),
    by rw [htd_s3, hdt_s3]; exact hspec.1,
    fun i => by rw [htd_s3, hmax_eq]; exact hspec.2.1 i,
    fun i => by rw [hdt_s3, hmax_eq]; exact hspec.2.2 i,
    fun d hd => ?_,
    fun d hd => ?_⟩
  · rw [hm_eq] at hd ⊢
    dsimp only [s₃]
    rw [compQuotAt_writeCompVal hw, hq_fix]
    by_cases hdeb : d = b_win
    · rw [hdeb, compQuotAt_writeCompQuot_self s₂.mem hb_lt hq_lt,
        physByBase_slab _ (Nat.lt_succ_self b_win), Function.update_self]
    · rw [compQuotAt_writeCompQuot_of_ne hw s₂.mem hdeb,
        Function.update_of_ne (hp_ne_bwin d (by omega) hdeb), congrFun hq2 d, hdt_s3, hs1_mem,
        compQuotAt_writeCompVal hw]
      by_cases hdel : d = d_last
      · rw [hdel, compQuotAt_writeCompQuot_self s.mem hd_last_lt hq_b_lt,
          hp.2.2.1 (lt_of_le_of_ne hp.1 (hdel.symm.trans_ne hdeb).symm), ← hp_b]
        exact hcpl.quot_eq b_win hb_lt
      · rw [compQuotAt_writeCompQuot_of_ne hw s.mem hdel, hp.2.2.2 d (by omega) hdeb hdel]
        exact hcpl.quot_eq d hd
  · rw [hm_eq] at hd ⊢
    dsimp only [s₃]
    rw [hv_fix]
    by_cases hdeb : d = b_win
    · rw [hdeb, compValAt_writeCompVal_self _ hb_lt hv_lt,
        physByBase_slab _ (Nat.lt_succ_self b_win), Function.update_self]
    · rw [compValAt_writeCompVal_of_ne hw _ hdeb, compValAt_writeCompQuot hw s₂.mem,
        Function.update_of_ne (hp_ne_bwin d (by omega) hdeb), congrFun hv2 d, hdt_s3, hs1_mem]
      by_cases hdel : d = d_last
      · rw [hdel, compValAt_writeCompVal_self _ hd_last_lt hv_b_lt,
          hp.2.2.1 (lt_of_le_of_ne hp.1 (hdel.symm.trans_ne hdeb).symm), ← hp_b]
        exact hcpl.val_eq b_win hb_lt
      · rw [compValAt_writeCompVal_of_ne hw _ hdel, compValAt_writeCompQuot hw s.mem,
          hp.2.2.2 d (by omega) hdeb hdel]
        exact hcpl.val_eq d hd


/-- Write `(q_val, v_val)` to dense compacted item slot `dst` at `itemBase`. -/
private def writeCompItemGenProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, itemBase), dst), (q_val, v_val)) => do
    writeCompQuotGenProg (((cp, itemBase), dst), q_val)
    writeCompValGenProg (((cp, itemBase), dst), v_val)

/-- Precondition for `writeCompItemGenProg`. -/
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
  obtain ⟨m_items, hce, hdst⟩ := h
  refine validProg_bind_unit (validProg_writeCompQuotGen ⟨m_items, hce, hdst⟩) fun s1 hs1 => ?_
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩ := hce
  rw [hs1, clientState_writeCompQuotGenProg]
  exact validProg_writeCompValGen ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
