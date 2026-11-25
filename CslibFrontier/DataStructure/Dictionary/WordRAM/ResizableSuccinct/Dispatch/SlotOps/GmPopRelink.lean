/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Env
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Internal
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Internal Top-Slab Unlink and Moved-Slab Relink Helpers for `compGmPopSlabGenProg`

Internal subroutines, cost bounds, `CompGmFrame` effects, `RealizesBounded .exact`, and
`ValidProg w 0` certificates for top-slab unlinking (`compGmUnlinkTopSlabGenProg`) and moved-slab
relinking (`compGmRelinkMovedSlabGenProg`), used privately by `Dispatch.SlotOps.GmPopSlab`.
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

/-- Write the new top slab pointer `bel_del` and decremented count `q_b - 1` for bucket `b`. -/
@[expose] def compGmUnlinkWriteProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (bel_del, q_b)) => do
    let q_idx := 4 + (b + b + b)
    writeCompGMGenProg (((cp, metaBase), q_idx + 2), bel_del)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b - 1)

/-- Unlink the top slab of bucket `b` and return its pool index `p_del`. -/
@[expose] def compGmUnlinkTopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
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

/-- Relink owner directory and top pointer from vacated slot `p_last` to `p_del`. -/
def compGmRelinkMovedSlabGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let pl2 := p_last + p_last
    let ownB_idx := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_idx)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_idx + 1)
    let q_idx := 4 + (b_last + b_last + b_last)
    let q_last ← readCompGMGenProg ((cp, metaBase), q_idx)
    compGmRelinkWriteProg ((((cp, metaBase), p_del), ((b_last, s_last), q_last)))

theorem memoryCost_compGmUnlinkTopSlabGenProg_eq
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmUnlinkTopSlabGenProg d) s = 14 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg]

theorem memoryCost_compGmRelinkMovedSlabGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmRelinkMovedSlabGenProg d) s ≤ 14 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  dsimp only [compGmRelinkMovedSlabGenProg, compGmRelinkWriteProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

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

/-- Precondition for `compGmUnlinkWriteProg`. -/
@[expose] def CompGmUnlinkWritePre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (_bel_del, q_b)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      1 ≤ q_b

theorem realizesBounded_compGmUnlinkWrite :
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

/-- Index facts for the three `GlobalMeta` reads of `compGmRelinkMovedSlabGenProg`. -/
private theorem compGmRelinkRead_idx {N p_last b_last : ℕ} (hb_pos : 0 < bucketBits N)
    (hp_last_cap : p_last < maxFullSlabs N) (hb_last : b_last < numBuckets N) :
    gmSlabOwnerBIdx N p_last < globalMetaLen N ∧
      gmSlabOwnerBIdx N p_last + 1 < globalMetaLen N ∧
      gmSlabMetaBase N + (p_last + p_last + (p_last + p_last)) = gmSlabOwnerBIdx N p_last ∧
      gmQIdx b_last < globalMetaLen N ∧
      4 + (b_last + b_last + b_last) = gmQIdx b_last :=
  ⟨gmSlabOwnerBIdx_lt hb_pos hp_last_cap, gmSlabOwnerSIdx_lt hb_pos hp_last_cap,
    by unfold gmSlabOwnerBIdx; omega, gmQIdx_lt hb_pos hb_last, by unfold gmQIdx; omega⟩

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
  obtain ⟨hownB_lt, hownS_lt, hpl4, hq_lt, hq_eq⟩ :=
    compGmRelinkRead_idx (b_last := b_last) hb_pos hp_last_cap hb_last
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

theorem realizesBounded_compGmRelinkMovedSlab :
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
    obtain ⟨hownB_lt, hownS_lt, hpl4, hq_lt, hq_eq⟩ :=
      compGmRelinkRead_idx hb_pos hp_last_cap hb_last
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

theorem pureMovedSlabInv_after_relink {N p_del p_last : ℕ} {gm : ℕ → ℕ}
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

theorem validProg_compGmRelinkMovedSlab {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmRelinkMovedSlabGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, _hp_del_cap, hp_last_cap, hb_last, _hs_le,
    _, _, hb_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  obtain ⟨hownB_lt, hownS_lt, hpl4, hq_lt, hq_eq⟩ :=
    compGmRelinkRead_idx hb_pos hp_last_cap hb_last
  have htop_lt : gmSlabTopIdx (compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last)) <
      globalMetaLen N := gmSlabTopIdx_lt hb_pos hb_last
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

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
