/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
-- `import all`: shares private internal helpers within the `TailSlabOps` split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.WindowHelpers
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Slab Promotion Step Definitions and Read Specification (`compPromoteStepGenProg`)

Defines the per-coordinate promotion step `compPromoteStepGenProg` and its metadata/dense-index read
specification `compPromoteStep_read_spec`.
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

/-- Single step `k` of `K`-step compacted slab promotion for bucket `b`. -/
private def compPromoteStepGenProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, (metaBase, itemBase)), b), k) => do
    let gmInfo ← compPromoteReadGMProg (((cp, metaBase), b), k)
    let ds ← compPromoteReadDenseProg ((cp, metaBase), gmInfo)
    let (wn, _) := gmInfo
    let qv ← compPromoteMoveItemsProg (((cp, itemBase), wn.1), ds)
    compPromoteFinishStepProg (((((cp, (metaBase, itemBase)), b), wn), qv))
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

/-- Precondition for `compPromoteStepGenProg`. -/
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
  have hptr_u_lt : gmTailPtrBase N + (b * tailCapPerBucket N + ((slabSize N - 1) - k)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb (by omega)
  have hptr_top_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (slabSize N + ((slabSize N - 1) - k))) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb (by omega)
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have htu_lt := htail.ptr_lt b hb _ hu_lt_r
  have httop_lt := htail.ptr_lt b hb _ hr_top_lt_r
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have htu_max := lt_of_lt_of_le htu_lt htail.ntails_le
  have httop_max := lt_of_lt_of_le httop_lt htail.ntails_le
  have hn'_max := lt_of_lt_of_le hn'_lt htail.ntails_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold StateTransitionSpec.clientState
    simp [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
  · dsimp only [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
    simp only [bind_assoc, pure_bind, succinct_param_simps]
    simp only [client_simps, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hptr_u_lt, runClient_state_readCompGMGenProg,
      clientResult_readCompGMGenProg hptr_top_lt, clientResult_readCompGMGenProg h0_lt,
      clientResult_readCompGMGenProg h1_lt]
    rfl
  · unfold StateTransitionSpec.clientState
    simp [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
  · dsimp only [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
    simp only [bind_assoc, pure_bind]
    simp only [client_simps, StateTransitionSpec.clientState,
      clientResult_readCompTDGenProg htu_max, runClient_state_readCompTDGenProg,
      clientResult_readCompTDGenProg httop_max, clientResult_readCompTDGenProg hn'_max,
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ htu_lt),
      runClient_state_denseOfCircGenProg,
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ httop_lt),
      clientResult_denseOfCircGenProg (fun _ => hcpl.win_inv.td_lt _ hn'_lt)]
  · dsimp only [compPromoteReadGMProg, compPromoteReadPtrsProg, compPromoteReadCountsProg]
    simp only [bind_assoc, pure_bind, succinct_param_simps]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_u_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_top_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)
  · dsimp only [compPromoteReadDenseProg, compPromoteReadTDProg, compPromoteCalcDenseProg]
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

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
