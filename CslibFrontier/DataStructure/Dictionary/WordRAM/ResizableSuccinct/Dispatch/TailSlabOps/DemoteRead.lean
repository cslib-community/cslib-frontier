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
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Slab Demotion Step Definitions and Read Specification (`compDemoteStepGenProg`)

Defines the per-coordinate demotion step `compDemoteStepGenProg` and its metadata read specification
`compDemoteStep_read_spec`.
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

/-- Single step `k` of `K`-step compacted slab demotion for bucket `b`. -/
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

/-- Precondition for `compDemoteStepGenProg`. -/
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
  refine ⟨?_, ?_, ?_⟩
  · unfold StateTransitionSpec.clientState
    simp [compDemoteReadGMProg]
  · dsimp only [compDemoteReadGMProg]
    simp only [succinct_param_simps, htop_eq]
    simp only [client_simps, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg htop_lt, runClient_state_readCompGMGenProg,
      clientResult_readCompGMGenProg h0_lt, clientResult_readCompGMGenProg h1_lt]
    rfl
  · dsimp only [compDemoteReadGMProg]
    simp only [succinct_param_simps, htop_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, htop_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
