/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
-- `import all`: shares private internal helpers within the `TailSlabOps` split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.DemoteRead
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.WindowHelpers
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `WindowCoupled` Simulation for One Slab-Demotion Step (`compDemoteStep_effect`)

Proves `WindowCoupled` and `CompOpFrame` preservation for a single step `compDemoteStepGenProg`
against `demoteStepProg`.
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
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

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

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
