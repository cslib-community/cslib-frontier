/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrlBase
-- Unfolds foreground DualEpochCtrlBase programs to expose pure state/result/cost equations.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrlBase

/-!
# Foreground `DualEpochCtrlBase` Program Evaluation Equations (`DualEpochCtrlEval`)

Exposes pure `clientState`, `clientResult`, and `memoryCost` equations for `userQueryProg`,
`prepGrowProg`, `syncLiveCountsProg`, `userMutateRawProg`, and `userMutateProg` so downstream
invariant modules require zero `import all` on `DualEpochCtrlBase`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-- Evaluates the header dispatch of `userQueryProg` down to its active-slot subprogram. -/
theorem userQueryProg_eval (base u_val : ℕ) (s : Memory.State) :
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc := if stg = 0 then p0 else p1
    let pDst := if stg = 0 then p1 else p0
    (Memory.spec 0).clientState s (userQueryProg (base, u_val)) =
      (Memory.spec 0).clientState s
        (if ph = 8 then
           epochQueryProg (pDst, u_val) >>= fun rDst =>
             if rDst.1 = 0 then epochQueryProg (pSrc, u_val) else pure rDst
         else if ph = 9 then epochQueryProg (pDst, u_val)
         else if 3 < ph then
           if ph < 8 then epochQueryProg (pSrc, u_val) else epochQueryProg (p0, u_val)
         else epochQueryProg (p0, u_val)) ∧
    (Memory.spec 0).clientResult s (userQueryProg (base, u_val)) =
      (Memory.spec 0).clientResult s
        (if ph = 8 then
           epochQueryProg (pDst, u_val) >>= fun rDst =>
             if rDst.1 = 0 then epochQueryProg (pSrc, u_val) else pure rDst
         else if ph = 9 then epochQueryProg (pDst, u_val)
         else if 3 < ph then
           if ph < 8 then epochQueryProg (pSrc, u_val) else epochQueryProg (p0, u_val)
         else epochQueryProg (p0, u_val)) ∧
    memoryCost (userQueryProg (base, u_val)) s =
      2 + memoryCost
        (if ph = 8 then
           epochQueryProg (pDst, u_val) >>= fun rDst =>
             if rDst.1 = 0 then epochQueryProg (pSrc, u_val) else pure rDst
         else if ph = 9 then epochQueryProg (pDst, u_val)
         else if 3 < ph then
           if ph < 8 then epochQueryProg (pSrc, u_val) else epochQueryProg (p0, u_val)
         else epochQueryProg (p0, u_val)) s := by
  dsimp only
  unfold userQueryProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    prog_clientResult_bind, cstate_rd, cres_rd,
    prog_clientResult_bind, cstate_rd, cres_rd,
    prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
    clientResult_selectEq0Prog,
    Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
    clientResult_selectEq0Prog]
  exact ⟨rfl, rfl, by omega⟩

/-- Evaluates `prepGrowProg` state, `k_grow` word count, and `memoryCost ≤ 40`. -/
theorem prepGrowProg_eval {w base opTag u_val : ℕ} {s : Memory.State}
    (hop : opTag ≠ 0) (hw_pos : 0 < w) (hwv : s.mem (base + hdrW) = w)
    (_hu1 : s.mem (base + hdrU1) + 1 ≤ 2 ^ w)
    (hnL_le : s.mem (base + hdrLive) ≤ s.mem (base + hdrU1) + 1) :
    let U_v := s.mem (base + hdrU1) + 1
    let nL := s.mem (base + hdrLive)
    let nAlloc := if opTag = 1 then min (nL + 1) U_v else nL
    let ph := s.mem (base + hdrPhase)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := s.mem (base + hdrValBits)
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u_val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val))
    s_prep =
      { mem :=
          if opTag = 1 then
            Function.update (Function.update s.mem (base + hdrPBase0 + 60) nAlloc)
              (base + hdrPBase1 + 60) nAlloc
          else s.mem
        frontier := s.frontier } ∧
    k_grow = (if ph < 2 then (ibLo + pairStreamWords nAlloc qLo vB w) - s.frontier
      else if ph = 11 then (ibLo + pairStreamWords nAlloc qLo vB w) - s.frontier
      else if ph = 2 then min ((ibHi + pairStreamWords nAlloc qHi vB w) - s.frontier) bulkBatchWhp
      else (ibHi + pairStreamWords nAlloc qHi vB w) - s.frontier) ∧
    memoryCost (prepGrowProg (((base, s.frontier), opTag), u_val)) s ≤ 40 := by
  dsimp only
  unfold prepGrowProg; dsimp only
  rw [ite_eq_right hop]
  have hu_ev :
      (Memory.spec 0).clientState s (prepGrowUpdateCapProg (base, opTag)) =
        { mem :=
            if opTag = 1 then
              Function.update (Function.update s.mem (base + hdrPBase0 + 60)
                (min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1)))
                (base + hdrPBase1 + 60)
                (min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1))
            else s.mem
          frontier := s.frontier } ∧
      (Memory.spec 0).clientResult s (prepGrowUpdateCapProg (base, opTag)) =
        (if opTag = 1 then min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1)
         else s.mem (base + hdrLive)) ∧
      memoryCost (prepGrowUpdateCapProg (base, opTag)) s ≤ 6 := by
    unfold prepGrowUpdateCapProg incCapSafeProg; dsimp only
    rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
      prog_clientResult_bind, cstate_rd, cres_rd,
      prog_clientResult_bind, cstate_rd, cres_rd,
      Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
      Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    by_cases h1 : opTag = 1
    · iterate 3 rw [ite_eq_left h1]
      split_ifs with hlt
      · simp only [pure_bind, prog_clientResult_bind, prog_clientResult_pure,
          Realization.memoryCost_bind', mcost_wr, memoryCost_pure]
        have hm : s.mem (base + hdrLive) =
            min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1) := by omega
        rw [← hm]; exact ⟨rfl, rfl, by omega⟩
      · simp only [pure_bind, prog_clientResult_bind, prog_clientResult_pure,
          Realization.memoryCost_bind', mcost_wr, memoryCost_pure]
        have hm : s.mem (base + hdrLive) + 1 =
            min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1) := by omega
        rw [← hm]; exact ⟨rfl, rfl, by omega⟩
    · iterate 3 rw [ite_eq_right h1]
      exact ⟨rfl, rfl, by simp only [memoryCost_pure]; omega⟩
  set s1 := (Memory.spec 0).clientState s (prepGrowUpdateCapProg (base, opTag))
  set nAlloc := if opTag = 1 then min (s.mem (base + hdrLive) + 1) (s.mem (base + hdrU1) + 1)
    else s.mem (base + hdrLive)
  have hs1_eq : s1 =
      { mem :=
          if opTag = 1 then
            Function.update (Function.update s.mem (base + hdrPBase0 + 60) nAlloc)
              (base + hdrPBase1 + 60) nAlloc
          else s.mem
        frontier := s.frontier } := by
    rw [hu_ev.1]; dsimp only [nAlloc]; split_ifs <;> rfl
  have hs1_low : ∀ off < 60, s1.mem (base + off) = s.mem (base + off) := fun off hoff => by
    rw [hu_ev.1]; dsimp only
    split_ifs
    · unfold hdrPBase0 hdrPBase1
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  have hw1 : s1.mem (base + hdrW) = w := (hs1_low hdrW (by decide)).trans hwv
  have hvb1 : s1.mem (base + hdrValBits) = s.mem (base + hdrValBits) :=
    hs1_low hdrValBits (by decide)
  have hph1 : s1.mem (base + hdrPhase) = s.mem (base + hdrPhase) := hs1_low hdrPhase (by decide)
  have hibL1 : s1.mem (base + hdrItemLo) = s.mem (base + hdrItemLo) := hs1_low hdrItemLo (by decide)
  have hibH1 : s1.mem (base + hdrItemHi) = s.mem (base + hdrItemHi) := hs1_low hdrItemHi (by decide)
  have hqL1 : s1.mem (base + hdrQLo) = s.mem (base + hdrQLo) := hs1_low hdrQLo (by decide)
  have hqH1 : s1.mem (base + hdrQHi) = s.mem (base + hdrQHi) := hs1_low hdrQHi (by decide)
  have hpw_cost : ∀ n qb vb, memoryCost (pairStreamWordsSafeProg (((n, qb), vb), w)) s1 = 0 :=
    fun n qb vb => (pairStreamWordsSafeProg_spec n qb vb w hw_pos s1).2.2
  rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, Realization.memoryCost_bind',
    hu_ev.2.1]
  change (Memory.spec 0).clientState s1 (prepGrowWordsProg ((base, s.frontier), nAlloc)) = _ ∧
    (Memory.spec 0).clientResult s1 (prepGrowWordsProg ((base, s.frontier), nAlloc)) = _ ∧
    memoryCost (prepGrowUpdateCapProg (base, opTag)) s +
      memoryCost (prepGrowWordsProg ((base, s.frontier), nAlloc)) s1 ≤ 40
  unfold prepGrowWordsProg; dsimp only
  iterate 7 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 7 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  iterate 7 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [hw1, hvb1, hph1, hibL1, hibH1, hqL1, hqH1]
  have hc_u := hu_ev.2.2
  by_cases hlt2 : s.mem (base + hdrPhase) < 2
  · rw [ite_eq_left hlt2, ite_eq_left hlt2,
      StateTransitionSpec.clientState_bind, clientState_pairStreamWordsSafeProg,
      pairStreamWordsSafeProg_res hw_pos, clientState_clampSubProg,
      prog_clientResult_bind, clientState_pairStreamWordsSafeProg,
      pairStreamWordsSafeProg_res hw_pos, clientResult_clampSubProg,
      Realization.memoryCost_bind', hpw_cost, clientState_pairStreamWordsSafeProg,
      memoryCost_clampSubProg]
    exact ⟨hs1_eq, rfl, by omega⟩
  · rw [ite_eq_right hlt2, ite_eq_right hlt2]
    by_cases hp11 : s.mem (base + hdrPhase) = 11
    · rw [ite_eq_left hp11, ite_eq_left hp11,
        StateTransitionSpec.clientState_bind, clientState_pairStreamWordsSafeProg,
        pairStreamWordsSafeProg_res hw_pos, clientState_clampSubProg,
        prog_clientResult_bind, clientState_pairStreamWordsSafeProg,
        pairStreamWordsSafeProg_res hw_pos, clientResult_clampSubProg,
        Realization.memoryCost_bind', hpw_cost, clientState_pairStreamWordsSafeProg,
        memoryCost_clampSubProg]
      exact ⟨hs1_eq, rfl, by omega⟩
    · rw [ite_eq_right hp11, ite_eq_right hp11]
      by_cases hp2 : s.mem (base + hdrPhase) = 2
      · rw [ite_eq_left hp2, ite_eq_left hp2,
          StateTransitionSpec.clientState_bind, clientState_pairStreamWordsSafeProg,
          pairStreamWordsSafeProg_res hw_pos,
          StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
          clientState_min2Prog,
          prog_clientResult_bind, clientState_pairStreamWordsSafeProg,
          pairStreamWordsSafeProg_res hw_pos,
          prog_clientResult_bind, clientState_clampSubProg, clientResult_clampSubProg,
          clientResult_min2Prog,
          Realization.memoryCost_bind', hpw_cost, clientState_pairStreamWordsSafeProg,
          Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
          memoryCost_min2Prog]
        exact ⟨hs1_eq, rfl, by omega⟩
      · rw [ite_eq_right hp2, ite_eq_right hp2,
          StateTransitionSpec.clientState_bind, clientState_pairStreamWordsSafeProg,
          pairStreamWordsSafeProg_res hw_pos, clientState_clampSubProg,
          prog_clientResult_bind, clientState_pairStreamWordsSafeProg,
          pairStreamWordsSafeProg_res hw_pos, clientResult_clampSubProg,
          Realization.memoryCost_bind', hpw_cost, clientState_pairStreamWordsSafeProg,
          memoryCost_clampSubProg]
        exact ⟨hs1_eq, rfl, by omega⟩

/-- Evaluates `syncLiveCountsProg` state update and `memoryCost ≤ 22`. -/
theorem syncLiveCountsProg_eval {base : ℕ} (s : Memory.State) :
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc := if stg = 0 then p0 else p1
    let pDst := if stg = 0 then p1 else p0
    let nLive' :=
      if ph = 8 then
        (Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
          (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
      else if ph = 9 then (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
      else if 4 ≤ ph ∧ ph ≤ 7 then (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)
      else (Memory.spec 0).clientResult s (epochReadNSideProg p0)
    let m3 := Function.update
      (Function.update (Function.update s.mem (base + hdrLive) nLive') (p0 + 60) nLive')
      (p1 + 60) nLive'
    let m_fin :=
      if (ph = 3 ∨ ph = 10) ∧ nLive' < m3 (base + hdrSplit) then
        Function.update m3 (base + hdrSplit) nLive'
      else m3
    (Memory.spec 0).clientState s (syncLiveCountsProg base) =
      { mem := m_fin, frontier := s.frontier } ∧
    memoryCost (syncLiveCountsProg base) s ≤ 20 := by
  dsimp only
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if stg = 0 then p1 else p0
  have hrn_cost : ∀ pB, memoryCost (epochReadNSideProg pB) s = 2 := fun pB => by
    unfold epochReadNSideProg
    rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, mcost_rd]
  have hrl_ev :
      (Memory.spec 0).clientResult s (readLiveCountProg ((ph, p0), (pSrc, pDst))) =
        (if ph = 8 then
           (Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
             (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
         else if ph = 9 then (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
         else if 4 ≤ ph ∧ ph ≤ 7 then (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)
         else (Memory.spec 0).clientResult s (epochReadNSideProg p0)) ∧
      memoryCost (readLiveCountProg ((ph, p0), (pSrc, pDst))) s ≤ 6 := by
    unfold readLiveCountProg; dsimp only
    by_cases h8 : ph = 8
    · rw [ite_eq_left h8, ite_eq_left h8, prog_clientResult_bind, clientState_epochReadNSideProg,
        prog_clientResult_bind, clientState_epochReadNSideProg, clientResult_max2Prog, Nat.max_self,
        Realization.memoryCost_bind', hrn_cost, clientState_epochReadNSideProg,
        Realization.memoryCost_bind', hrn_cost, clientState_epochReadNSideProg, memoryCost_max2Prog]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right h8, ite_eq_right h8]
      by_cases h9 : ph = 9
      · rw [ite_eq_left h9, ite_eq_left h9]; exact ⟨rfl, by rw [hrn_cost]; omega⟩
      · rw [ite_eq_right h9, ite_eq_right h9]
        by_cases h3 : 3 < ph
        · rw [ite_eq_left h3]
          by_cases hlt8 : ph < 8
          · rw [ite_eq_left hlt8, ite_eq_left (show 4 ≤ ph ∧ ph ≤ 7 by omega)]
            exact ⟨rfl, by rw [hrn_cost]; omega⟩
          · rw [ite_eq_right hlt8, ite_eq_right (show ¬(4 ≤ ph ∧ ph ≤ 7) by omega)]
            exact ⟨rfl, by rw [hrn_cost]; omega⟩
        · rw [ite_eq_right h3, ite_eq_right (show ¬(4 ≤ ph ∧ ph ≤ 7) by omega)]
          exact ⟨rfl, by rw [hrn_cost]; omega⟩
  unfold syncLiveCountsProg
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
    StateTransitionSpec.clientState_bind, clientState_readLiveCountProg, hrl_ev.1,
    StateTransitionSpec.clientState_bind, cstate_wr,
    StateTransitionSpec.clientState_bind, cstate_wr,
    StateTransitionSpec.clientState_bind, cstate_wr,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
    clientResult_slotPairProg,
    Realization.memoryCost_bind', clientState_readLiveCountProg, hrl_ev.1,
    Realization.memoryCost_bind', mcost_wr, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr]
  set nLive' := if ph = 8 then
      (Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
        (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
    else if ph = 9 then (Memory.spec 0).clientResult s (epochReadNSideProg pDst)
    else if 4 ≤ ph ∧ ph ≤ 7 then (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)
    else (Memory.spec 0).clientResult s (epochReadNSideProg p0)
  set m3 := Function.update
    (Function.update (Function.update s.mem (base + hdrLive) nLive') (p0 + 60) nLive')
    (p1 + 60) nLive'
  have hc_rl : memoryCost (readLiveCountProg ((s.mem (base + hdrPhase), base + hdrPBase0),
      (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1,
       if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0))) s ≤ 6 :=
    hrl_ev.2
  unfold clampSplitIfSlideProg; dsimp only
  by_cases h3 : ph = 3
  · rw [ite_eq_left h3, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
      Realization.memoryCost_bind', Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    dsimp only
    by_cases hlt : nLive' < m3 (base + hdrSplit)
    · rw [ite_eq_left hlt, ite_eq_left ⟨Or.inl h3, hlt⟩, StateTransitionSpec.clientState_bind,
        cstate_wr]
      simp only [mcost_wr, memoryCost_pure]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt h.2)]
      simp only [memoryCost_pure]
      exact ⟨rfl, by omega⟩
  · rw [ite_eq_right h3]
    by_cases h10 : ph = 10
    · rw [ite_eq_left h10, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
        Realization.memoryCost_bind', Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
      dsimp only
      by_cases hlt : nLive' < m3 (base + hdrSplit)
      · rw [ite_eq_left hlt, ite_eq_left ⟨Or.inr h10, hlt⟩, StateTransitionSpec.clientState_bind,
          cstate_wr]
        simp only [mcost_wr, memoryCost_pure]
        exact ⟨rfl, by omega⟩
      · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt h.2)]
        simp only [memoryCost_pure]
        exact ⟨rfl, by omega⟩
    · rw [ite_eq_right h10, ite_eq_right (fun h => h.1.elim h3 h10),
        Realization.memoryCost_bind', memoryCost_pure, memoryCost_pure]
      exact ⟨rfl, by omega⟩

/-- Evaluates the header dispatch of `userMutateRawProg` down to its active-slot subprogram. -/
theorem userMutateRawProg_eval {base opTag u_val v_val ph stg : ℕ} (st : Memory.State)
    (hph_st : st.mem (base + hdrPhase) = ph) (hstg_st : st.mem (base + hdrStage) = stg) :
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc := if stg = 0 then p0 else p1
    let pDst_raw := if stg = 0 then p1 else p0
    (Memory.spec 0).clientState st (userMutateRawProg ((base, opTag), (u_val, v_val))) =
      (Memory.spec 0).clientState st
        (if opTag = 1 then
           if ph = 8 then
             epochDeleteProg (pSrc, u_val) >>= fun _ => epochInsertProg ((pDst_raw, u_val), v_val)
           else if ph = 9 then epochInsertProg ((pDst_raw, u_val), v_val)
           else if 3 < ph then
             if ph < 8 then epochInsertProg ((pSrc, u_val), v_val)
             else epochInsertProg ((p0, u_val), v_val)
           else epochInsertProg ((p0, u_val), v_val)
         else
           if ph = 8 then
             epochDeleteProg (pSrc, u_val) >>= fun _ => epochDeleteProg (pDst_raw, u_val)
           else if ph = 9 then epochDeleteProg (pDst_raw, u_val)
           else if 3 < ph then
             if ph < 8 then epochDeleteProg (pSrc, u_val)
             else epochDeleteProg (p0, u_val)
           else epochDeleteProg (p0, u_val)) ∧
    memoryCost (userMutateRawProg ((base, opTag), (u_val, v_val))) st =
      2 + memoryCost
        (if opTag = 1 then
           if ph = 8 then
             epochDeleteProg (pSrc, u_val) >>= fun _ => epochInsertProg ((pDst_raw, u_val), v_val)
           else if ph = 9 then epochInsertProg ((pDst_raw, u_val), v_val)
           else if 3 < ph then
             if ph < 8 then epochInsertProg ((pSrc, u_val), v_val)
             else epochInsertProg ((p0, u_val), v_val)
           else epochInsertProg ((p0, u_val), v_val)
         else
           if ph = 8 then
             epochDeleteProg (pSrc, u_val) >>= fun _ => epochDeleteProg (pDst_raw, u_val)
           else if ph = 9 then epochDeleteProg (pDst_raw, u_val)
           else if 3 < ph then
             if ph < 8 then epochDeleteProg (pSrc, u_val)
             else epochDeleteProg (p0, u_val)
           else epochDeleteProg (p0, u_val)) st := by
  dsimp only
  unfold userMutateRawProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hph_st,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hstg_st,
    StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd, hph_st,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd, hstg_st,
    Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
    clientResult_selectEq0Prog,
    Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
    clientResult_selectEq0Prog]
  exact ⟨rfl, by omega⟩

/-- Decomposes `userMutateProg` into `userMutateRawProg` followed by `syncLiveCountsProg`. -/
theorem userMutateProg_eval (base opTag u_val v_val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (userMutateProg ((base, opTag), (u_val, v_val))) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (userMutateRawProg ((base, opTag), (u_val, v_val))))
        (syncLiveCountsProg base) ∧
    memoryCost (userMutateProg ((base, opTag), (u_val, v_val))) s =
      memoryCost (userMutateRawProg ((base, opTag), (u_val, v_val))) s +
        memoryCost (syncLiveCountsProg base)
          ((Memory.spec 0).clientState s (userMutateRawProg ((base, opTag), (u_val, v_val)))) :=
  ⟨StateTransitionSpec.clientState_bind .., Realization.memoryCost_bind' ..⟩

/-- Evaluates `prepGrowProg` on `opTag = 0` (`query`) as a zero-cost `pure 0`. -/
theorem prepGrowProg_query_eval (base curFr u_val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (prepGrowProg (((base, curFr), 0), u_val)) = s ∧
    (Memory.spec 0).clientResult s (prepGrowProg (((base, curFr), 0), u_val)) = 0 ∧
    memoryCost (prepGrowProg (((base, curFr), 0), u_val)) s = 0 := by
  unfold prepGrowProg; dsimp only
  exact ⟨rfl, rfl, memoryCost_pure 0 s⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
