/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochTableRealize
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.ValidHistoryEpoch
-- Unfolds `pageInitDirBatchProg` / `pageInitTailBatchProg` for functional specifications.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageBaseProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageCoreProg
-- Unfolds `pairStreamWordsSafeProg` for `0`-query pure evaluation.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochTable
-- Unfolds `migrateStepProg` / `migrateBatchProg` for `ValidHistory` and `epochReadNSideProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochProgs
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base Control Helpers, Trigger Check, `prepGrowProg`, and Active User Operations

This module provides the foundational `Memory.Prog` control primitives and active user-operation
dispatchers (`query`, `insert`, `delete`, `prepGrowProg`, `syncLiveCountsProg`) for the deamortized
dual-epoch resizable succinct worst-case WHP dictionary ([Bender, Farach-Colton, J. Kuszmaul, and
W. Kuszmaul, SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **`pageInitDirBatchProg_spec`, `pageInitTailBatchProg_spec`, `validHistory_migrateBatchProg`:**
   Functional specifications for batched `PageArenaLayout` directory and tail initialization plus
   `ValidHistory` for `migrateBatchProg`.
2. **Overflow-free control helpers & slot-I/O configurators:** `clampSubProg`, `max2Prog`,
   `min2Prog`, `selectEq0Prog`, `selectEq0PairProg`, `metaDstAddrProg`, `slotPairProg`,
   `pageCtxScalarsProg`, `checkTriggerProg`, `copyDstToSrcHostProg`, `setDirectSlotIoProg`,
   `setSplitSlotIoProg`, `loadSplitPairCtxProg`, and `loadHostCtxProg`.
3. **`prepGrowProg` and active user operations:** `prepGrowProg`, `userQueryProg`,
   `syncLiveCountsProg`, `userMutateRawProg`, and `userMutateProg` (`RealizesBounded .exact`,
   `¬ReadsWidth`, and `ValidHistory`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

theorem cstate_rd (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.read a) = s := rfl

theorem cres_rd (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl

theorem cstate_wr (a v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.write a v) =
      { mem := Function.update s.mem a v, frontier := s.frontier } := rfl

theorem mcost_rd (a : ℕ) (s : Memory.State) :
    memoryCost (Memory.read a) s = 1 := rfl

theorem mcost_wr (a v : ℕ) (s : Memory.State) :
    memoryCost (Memory.write a v) s = 1 := rfl

theorem shift_one_eq (k : ℕ) : (1 : ℕ) <<< k = 2 ^ k := by
  rw [Nat.shiftLeft_eq, one_mul]

theorem runClient0_state {α : Type} (s : Memory.State) (p : Memory.Prog α) :
    clientOutState ((Memory.spec 0).runClient s p) = (Memory.spec 0).clientState s p := rfl

theorem runClient0_res {α : Type} (s : Memory.State) (p : Memory.Prog α) :
    ((Memory.spec 0).runClient s p).1 = (Memory.spec 0).clientResult s p := rfl

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

theorem pairStreamWords_ge_two (n qb vb w : ℕ) : 2 ≤ pairStreamWords n qb vb w := by
  unfold pairStreamWords packedWords; exact Nat.le_add_left 2 _

theorem four_le_of_frontier16 {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 16 ≤ s.frontier) : 4 ≤ w := by
  have hfr : s.frontier < 2 ^ w := hwf.1
  by_contra hlt
  have hle : 2 ^ w ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem six_le_of_frontier48 {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 48 ≤ s.frontier) : 6 ≤ w := by
  have hfr : s.frontier < 2 ^ w := hwf.1
  by_contra hlt
  have hle : 2 ^ w ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem pageArenaValid_meta32 {L : PageArenaLayout} {w fr : ℕ} (hv : L.Valid w fr) :
    L.metaBase + 32 ≤ fr := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := hv
  omega

theorem pageArenaValid_pg16_lt {L : PageArenaLayout} {w fr : ℕ} (hv : L.Valid w fr) :
    16 * L.pgB < 2 ^ w := by
  obtain ⟨_, _, hpb, _, _, _, hpg16, _, _, _, _, _, _, _, _⟩ := hv
  exact lt_of_lt_of_le hpg16 (Nat.pow_le_pow_right (by decide) hpb)

theorem pageArenaValid_mp4_lt {L : PageArenaLayout} {w fr : ℕ} (hv : L.Valid w fr) :
    4 * L.maxPages < 2 ^ w := by
  obtain ⟨_, _, hpb, _, _, _, _, _, hmp4, _, _, _, _, _, _⟩ := hv
  exact lt_of_lt_of_le hmp4 (Nat.pow_le_pow_right (by decide) hpb)

theorem vh_seq {w : ℕ} {α β : Type} {st : Memory.State} {p : Memory.Prog α}
    {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st p))
    (hq : ∀ st' : Memory.State, st' = (Memory.spec 0).clientState st p →
      ∀ r : α, r = (Memory.spec 0).clientResult st p →
      (Memory.spec w).ValidHistory st' ((Memory.spec w).clientHistory st' (q r))) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (p >>= q)) := by
  change (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq _ rfl _ rfl⟩

theorem wf_step {w : ℕ} {α : Type} {s : Memory.State} {p : Memory.Prog α}
    (hwf : Memory.WellFormed w s)
    (vh : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run vh

theorem vh_rd {w a : ℕ} {α : Type} {s : Memory.State} {q : ℕ → Memory.Prog α}
    (ha : a < s.frontier)
    (hq : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  vh_seq ⟨ha, trivial⟩ fun _ hst _ hr => by rw [hst, hr]; exact hq

theorem vh_wr {w a v : ℕ} {α : Type} {m : ℕ → ℕ} {fr : ℕ} {q : Unit → Memory.Prog α}
    (ha : a < fr) (hv : Fits w v)
    (hq : (Memory.spec w).ValidHistory ⟨Function.update m a v, fr⟩
      ((Memory.spec w).clientHistory ⟨Function.update m a v, fr⟩ (q ()))) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ (Memory.write a v >>= q)) :=
  vh_seq ⟨⟨ha, hv⟩, trivial⟩ fun _ hst _ _ => by rw [hst]; exact hq

theorem vh_wr_only {w a v : ℕ} {m : ℕ → ℕ} {fr : ℕ}
    (ha : a < fr) (hv : Fits w v) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ (Memory.write a v)) :=
  ⟨⟨ha, hv⟩, trivial⟩

theorem vh_ite {w : ℕ} {α : Type} {s : Memory.State} (P : Prop) [Decidable P]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : P → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬P → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (if P then p₁ else p₂)) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

/-! ## Section 1: `pageInitDirBatchProg_spec`, `pageInitTailBatchProg_spec`, and `migrateBatchProg`
-/

/-- Functional specification of a single `pageInitDirStepProg` step. -/
theorem pageInitDirStepProg_spec {L : PageArenaLayout} {cur : ℕ} {s : Memory.State}
    (hv : L.Valid L.w s.frontier) (hcur : cur ≤ L.maxPages) :
    let s' := (Memory.spec 0).clientState s (pageInitDirStepProg (L.toCtx, cur))
    let u := extractPageUnperm L s.mem
    let u' := extractPageUnperm L s'.mem
    (PageArenaLayout.ofCtx L.toCtx).Valid L.w s.frontier ∧
    (Memory.spec 0).clientResult s (pageInitDirStepProg (L.toCtx, cur)) =
      min L.maxPages (cur + 1) ∧
    s'.frontier = s.frontier ∧
    memoryCost (pageInitDirStepProg (L.toCtx, cur)) s ≤ 18 ∧
    (∀ addr, ¬(L.metaBase + L.offDir ≤ addr ∧
      addr < L.metaBase + L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w) →
      s'.mem addr = s.mem addr) ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem ∧
    u'.cleanPhase = u.cleanPhase ∧ u'.cleanVp = u.cleanVp ∧ u'.cleanOff = u.cleanOff ∧
    u'.st.pageSize = u.st.pageSize ∧ u'.st.fullPages = u.st.fullPages ∧
    u'.st.tailCount = u.st.tailCount ∧ u'.st.tailHead = u.st.tailHead ∧ u'.st.job = u.st.job ∧
    u'.st.tailRes = u.st.tailRes ∧ u'.st.tailOwnerSide = u.st.tailOwnerSide ∧
    u'.st.tailOwnerRing = u.st.tailOwnerRing ∧
    (∀ side vp, vp < L.maxPages →
      u'.st.pageOf side vp = if vp = cur then (if side then 0 else cur) else u.st.pageOf side vp) ∧
    (∀ P, P < L.maxPages →
      (u'.st.ownerSide P = if P = cur then false else u.st.ownerSide P) ∧
      (u'.st.ownerVp P = if P = cur then cur else u.st.ownerVp P)) := by
  dsimp only
  have hv_ctx : (PageArenaLayout.ofCtx L.toCtx).Valid L.w s.frontier := by
    rwa [PageArenaLayout.ofCtx_toCtx]
  obtain ⟨hw, _, _, _, _, hpg32, hpg16, _, hmp4, _, _, ho1, ho2, hm_ib, _⟩ := hv
  have hptr1 : 1 < 2 ^ L.ptrB := by omega
  have hfrm := pageInitDirBatchProg_frame (L := L) hw cur 1
  have hmc : memoryCost (pageInitDirStepProg (L.toCtx, cur)) s ≤ 18 := by
    have hc := hfrm.cost_le s
    unfold pageInitDirBatchProg at hc; dsimp only at hc
    unfold iterate at hc
    rw [Realization.memoryCost_bind'] at hc
    exact le_trans (Nat.le_add_right _ _) (hc.trans (by omega))
  by_cases hlt : cur < L.maxPages
  · have hmin : min L.maxPages (cur + 1) = cur + 1 := min_eq_right (by omega)
    have hcur_ptr : cur < 2 ^ L.ptrB := by omega
    have h0_ptr : 0 < 2 ^ L.ptrB := by positivity
    set m1 := writePacked (L.metaBase + L.offDir) L.ptrB L.w s.mem (4 * cur + 0) cur
    set m2 := writePacked (L.metaBase + L.offDir) L.ptrB L.w m1 (4 * cur + 1) 0
    set m3 := writePacked (L.metaBase + L.offDir) L.ptrB L.w m2 (4 * cur + 2) 0
    set m4 := writePacked (L.metaBase + L.offDir) L.ptrB L.w m3 (4 * cur + 3) cur
    have hst_eq : (Memory.spec 0).clientState s (pageInitDirStepProg (L.toCtx, cur)) =
        { mem := m4, frontier := s.frontier } := by
      unfold pageInitDirStepProg pageWritePageOfProg pageWriteOwnerProg
      dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_left hlt]
      simp [StateTransitionSpec.clientState, pure_bind, ite_eq_left hlt,
        runClient_state_writePackedCompGenProg, m1, m2, m3, m4]
    have hres_eq : (Memory.spec 0).clientResult s (pageInitDirStepProg (L.toCtx, cur)) =
        cur + 1 := by
      unfold pageInitDirStepProg pageWritePageOfProg pageWriteOwnerProg
      dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_left hlt]
      simp [StateTransitionSpec.clientResult, pure_bind, ite_eq_left hlt]
    rw [hst_eq, hres_eq, hmin]
    obtain ⟨hu1, ha1⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib s.mem false hlt hcur_ptr
    obtain ⟨hu2, ha2⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib m1 true hlt h0_ptr
    obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeOwnerSide hw hptr1 ho1 ho2 hm_ib m2 hlt false
    obtain ⟨hu4, ha4⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib m3 hlt hcur_ptr
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1 hu2 hu3
    change _ ∧ _ ∧ _ ∧ _ ∧
      (∀ addr, _ → m4 addr = s.mem addr) ∧ arenaPairAt L m4 = arenaPairAt L s.mem ∧ _
    have hout : ∀ addr, ¬(L.metaBase + L.offDir ≤ addr ∧
        addr < L.metaBase + L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w) →
        m4 addr = s.mem addr := fun addr ha => by
      dsimp only [m4, m3, m2, m1]
      rw [writePacked_outside hw _ (by omega) _ ha,
        writePacked_outside hw _ (by omega) _ ha,
        writePacked_outside hw _ (by omega) _ ha,
        writePacked_outside hw _ (by omega) _ ha]
    have hu_all : extractPageUnperm L m4 =
        { (extractPageUnperm L s.mem) with
          st := { (extractPageUnperm L s.mem).st with
            pageOf := PagePairState.set2
              (PagePairState.set2 (extractPageUnperm L s.mem).st.pageOf false cur cur)
              true cur 0
            ownerSide := Function.update (extractPageUnperm L s.mem).st.ownerSide cur false
            ownerVp := Function.update (extractPageUnperm L s.mem).st.ownerVp cur cur } } := by
      dsimp only [m4]; rw [hu4]; dsimp only [m3]; rw [hu3]; dsimp only [m2]; rw [hu2]
      dsimp only [m1]; rw [hu1]
    refine ⟨hv_ctx, rfl, rfl, hmc, hout, ha4.trans (ha3.trans (ha2.trans ha1)), ?_⟩
    rw [hu_all]; dsimp only
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun side vp _ => ?_,
      fun P _ => ⟨?_, ?_⟩⟩
    · by_cases hv_eq : vp = cur
      · subst vp
        cases side
        · rw [ite_eq_left rfl, PagePairState.set2_of_ne _ _ _ _ _ _ (by simp),
            PagePairState.set2_self]; simp
        · rw [ite_eq_left rfl, PagePairState.set2_self]; simp
      · rw [ite_eq_right hv_eq, PagePairState.set2_of_ne _ _ _ _ _ _ (by simp [hv_eq]),
          PagePairState.set2_of_ne _ _ _ _ _ _ (by simp [hv_eq])]
    · by_cases hP : P = cur
      · subst P; simp
      · simp [hP]
    · by_cases hP : P = cur
      · subst P; simp
      · simp [hP]
  · have heq : cur = L.maxPages := by omega
    subst cur
    have hmin : min L.maxPages (L.maxPages + 1) = L.maxPages := min_eq_left (by omega)
    have hst : (Memory.spec 0).clientState s (pageInitDirStepProg (L.toCtx, L.maxPages)) = s := by
      unfold pageInitDirStepProg; dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_right (Nat.lt_irrefl _)]; rfl
    have hres : (Memory.spec 0).clientResult s (pageInitDirStepProg (L.toCtx, L.maxPages)) =
        L.maxPages := by
      unfold pageInitDirStepProg; dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_right (Nat.lt_irrefl _)]; rfl
    rw [hst, hres, hmin]
    exact ⟨hv_ctx, rfl, rfl, hmc, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, fun _ _ h => by rw [ite_eq_right h.ne],
      fun _ h => ⟨by rw [ite_eq_right h.ne], by rw [ite_eq_right h.ne]⟩⟩

theorem pageInitDirStepProg_fr (ctx : PageArenaCtx) (c0 w : ℕ) (st : Memory.State)
    (hv_st : (PageArenaLayout.ofCtx ctx).Valid w st.frontier) :
    ((Memory.spec 0).clientState st (pageInitDirStepProg (ctx, c0))).frontier = st.frontier := by
  have hce : (PageArenaLayout.ofCtx ctx).toCtx = ctx := by
    rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
  have hw_c : 0 < (PageArenaLayout.ofCtx ctx).w := by rw [← hv_st.2.1]; exact hv_st.1
  have hfrm := pageInitDirBatchProg_frame (L := PageArenaLayout.ofCtx ctx) hw_c c0 1
  rw [hce] at hfrm
  have hf1 := hfrm.frontier_eq st
  unfold pageInitDirBatchProg at hf1; dsimp only at hf1; unfold iterate at hf1
  rw [StateTransitionSpec.clientState_bind] at hf1; exact hf1

attribute [local irreducible] pageInitDirStepProg

/-- Batched specification of `pageInitDirBatchProg` across `fuel` entries. -/
theorem pageInitDirBatchProg_spec {L : PageArenaLayout} {cur : ℕ} {s : Memory.State}
    (hv : L.Valid L.w s.frontier) (hcur : cur ≤ L.maxPages) (fuel : ℕ) :
    let s' := (Memory.spec 0).clientState s (pageInitDirBatchProg ((L.toCtx, cur), fuel))
    let u := extractPageUnperm L s.mem
    let u' := extractPageUnperm L s'.mem
    iterationSafe pageInitDirStepProg
      (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
      L.w L.toCtx fuel cur s ∧
    (Memory.spec 0).clientResult s (pageInitDirBatchProg ((L.toCtx, cur), fuel)) =
      min L.maxPages (cur + fuel) ∧
    s'.frontier = s.frontier ∧
    memoryCost (pageInitDirBatchProg ((L.toCtx, cur), fuel)) s ≤ 18 * fuel ∧
    (∀ addr, ¬(L.metaBase + L.offDir ≤ addr ∧
      addr < L.metaBase + L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w) →
      s'.mem addr = s.mem addr) ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem ∧
    u'.cleanPhase = u.cleanPhase ∧ u'.cleanVp = u.cleanVp ∧ u'.cleanOff = u.cleanOff ∧
    u'.st.pageSize = u.st.pageSize ∧ u'.st.fullPages = u.st.fullPages ∧
    u'.st.tailCount = u.st.tailCount ∧ u'.st.tailHead = u.st.tailHead ∧ u'.st.job = u.st.job ∧
    u'.st.tailRes = u.st.tailRes ∧ u'.st.tailOwnerSide = u.st.tailOwnerSide ∧
    u'.st.tailOwnerRing = u.st.tailOwnerRing ∧
    (∀ side vp, vp < L.maxPages →
      u'.st.pageOf side vp =
        if cur ≤ vp ∧ vp < min L.maxPages (cur + fuel) then (if side then 0 else vp)
        else u.st.pageOf side vp) ∧
    (∀ P, P < L.maxPages →
      (u'.st.ownerSide P =
        if cur ≤ P ∧ P < min L.maxPages (cur + fuel) then false else u.st.ownerSide P) ∧
      (u'.st.ownerVp P =
        if cur ≤ P ∧ P < min L.maxPages (cur + fuel) then P else u.st.ownerVp P)) := by
  dsimp only
  unfold pageInitDirBatchProg; dsimp only
  induction fuel generalizing s cur with
  | zero =>
    unfold iterate
    have hmin : min L.maxPages (cur + 0) = cur := min_eq_right (by omega)
    rw [hmin]
    have hf_vp : ∀ vp, ¬(cur ≤ vp ∧ vp < cur) := fun _ => by omega
    exact ⟨trivial, rfl, rfl, Nat.zero_le _, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl,
      fun _ vp _ => by rw [ite_eq_right (hf_vp vp)]; rfl,
      fun P _ => ⟨by rw [ite_eq_right (hf_vp P)]; rfl, by rw [ite_eq_right (hf_vp P)]; rfl⟩⟩
  | succ k ih =>
    obtain ⟨hv1, hres1, hfr1, hc1, hout1, har1, hcp1, hcv1, hco1, hps1, hfp1, htc1, hth1, hj1,
      htr1, htos1, htor1, hpo1, how1⟩ := pageInitDirStepProg_spec hv hcur
    set s1 := (Memory.spec 0).clientState s (pageInitDirStepProg (L.toCtx, cur))
    set c1 := min L.maxPages (cur + 1)
    obtain ⟨hsafe, hres2, hfr2, hc2, hout2, har2, hcp2, hcv2, hco2, hps2, hfp2, htc2, hth2, hj2,
      htr2, htos2, htor2, hpo2, how2⟩ :=
      ih (s := s1) (cur := c1) (hfr1.symm ▸ hv) (min_le_left _ _)
    have hmin_eq : min L.maxPages (c1 + k) = min L.maxPages (cur + (k + 1)) := by
      dsimp only [c1]; omega
    have hcost_tot : memoryCost (iterate pageInitDirStepProg L.toCtx (k + 1) cur) s ≤
        18 * (k + 1) := by
      unfold iterate
      rw [Realization.memoryCost_bind', hres1]
      change memoryCost (pageInitDirStepProg (L.toCtx, cur)) s +
        memoryCost (iterate pageInitDirStepProg L.toCtx k c1) s1 ≤ 18 * (k + 1)
      omega
    have hsafe_tot : iterationSafe pageInitDirStepProg
        (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
        L.w L.toCtx (k + 1) cur s := by
      unfold iterationSafe
      rw [clientResult_width, clientState_width, hres1]
      exact ⟨hv1, hsafe⟩
    have hst_tot : (Memory.spec 0).clientState s
        (iterate pageInitDirStepProg L.toCtx (k + 1) cur) =
        (Memory.spec 0).clientState s1 (iterate pageInitDirStepProg L.toCtx k c1) := by
      conv_lhs => unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres1]
    have hres_tot : (Memory.spec 0).clientResult s
        (iterate pageInitDirStepProg L.toCtx (k + 1) cur) =
        min L.maxPages (cur + (k + 1)) := by
      unfold iterate
      rw [prog_clientResult_bind, hres1]
      exact hres2.trans hmin_eq
    rw [hst_tot]
    refine ⟨hsafe_tot, hres_tot, hfr2.trans hfr1, hcost_tot,
      fun addr ha => (hout2 addr ha).trans (hout1 addr ha),
      har2.trans har1, hcp2.trans hcp1, hcv2.trans hcv1, hco2.trans hco1,
      hps2.trans hps1, hfp2.trans hfp1, htc2.trans htc1,
      hth2.trans hth1, hj2.trans hj1,
      htr2.trans htr1, htos2.trans htos1, htor2.trans htor1,
      fun side vp hvp => ?_, fun P hP => ⟨?_, ?_⟩⟩
    · rw [hpo2 side vp hvp, hmin_eq]
      by_cases h2 : c1 ≤ vp ∧ vp < min L.maxPages (cur + (k + 1))
      · have h2' : cur ≤ vp ∧ vp < min L.maxPages (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, hpo1 side vp hvp]
        by_cases h0 : vp = cur
        · subst vp
          have h0' : cur ≤ cur ∧ cur < min L.maxPages (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ vp ∧ vp < min L.maxPages (cur + (k + 1))) := by
            dsimp only [c1] at h2; omega
          rw [ite_eq_right h0, ite_eq_right hn0']
    · rw [(how2 P hP).1, hmin_eq]
      by_cases h2 : c1 ≤ P ∧ P < min L.maxPages (cur + (k + 1))
      · have h2' : cur ≤ P ∧ P < min L.maxPages (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, (how1 P hP).1]
        by_cases h0 : P = cur
        · subst P
          have h0' : cur ≤ cur ∧ cur < min L.maxPages (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ P ∧ P < min L.maxPages (cur + (k + 1))) := by
            dsimp only [c1] at h2; omega
          rw [ite_eq_right h0, ite_eq_right hn0']
    · rw [(how2 P hP).2, hmin_eq]
      by_cases h2 : c1 ≤ P ∧ P < min L.maxPages (cur + (k + 1))
      · have h2' : cur ≤ P ∧ P < min L.maxPages (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, (how1 P hP).2]
        by_cases h0 : P = cur
        · subst P
          have h0' : cur ≤ cur ∧ cur < min L.maxPages (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ P ∧ P < min L.maxPages (cur + (k + 1))) := by
            dsimp only [c1] at h2; omega
          rw [ite_eq_right h0, ite_eq_right hn0']

private theorem pageInitTailStep_state {L : PageArenaLayout} {n_0 cur : ℕ} (s : Memory.State)
    (hn0 : n_0 ≤ L.nCap) (hlt : cur < 8 * L.pgB) :
    let q₀ := if n_0 < L.pgB + (L.pgB + L.pgB / 2) then 0 else (n_0 - (L.pgB + L.pgB / 2)) / L.pgB
    let qbm := (q₀ * L.pgB) % (8 * L.pgB)
    let rv := (cur + 8 * L.pgB - qbm) % (8 * L.pgB)
    let res_v := (qbm + cur) % (8 * L.pgB)
    (Memory.spec 0).clientState s (pageInitTailStepProg ((L.toCtx, n_0), cur)) =
      { mem := if cur < 4 * L.pgB then
          writePacked (L.metaBase + L.offTail) L.ptrB L.w
            (writePacked (L.metaBase + L.offTail) L.ptrB L.w
              (writePacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (0 + cur) res_v)
              (4 * L.pgB + cur) res_v)
            (8 * L.pgB + cur) (0 + 2 * rv)
        else
          writePacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (8 * L.pgB + cur) (0 + 2 * rv)
        frontier := s.frontier } ∧
    (Memory.spec 0).clientResult s (pageInitTailStepProg ((L.toCtx, n_0), cur)) = cur + 1 := by
  dsimp only
  have hcond : n_0 ≤ L.nCap ∧ cur < 8 * L.pgB := ⟨hn0, hlt⟩
  have hrv_lt : ∀ x : ℕ, x % (8 * L.pgB) < 8 * L.pgB := fun x => Nat.mod_lt x (by omega)
  unfold pageInitTailStepProg pageInitTailResSubProg pageWriteTailResProg pageWriteTailOwnerProg
  dsimp only [PageArenaLayout.toCtx]
  rw [ite_eq_left hcond]
  simp only [pure_bind]
  by_cases hc4 : cur < 4 * L.pgB
  · exact ⟨by simp [StateTransitionSpec.clientState, hlt, hrv_lt, hc4,
      runClient_state_writePackedCompGenProg],
      by simp [StateTransitionSpec.clientResult, hlt, hc4]⟩
  · exact ⟨by simp [StateTransitionSpec.clientState, hlt, hrv_lt, hc4,
      runClient_state_writePackedCompGenProg],
      by simp [StateTransitionSpec.clientResult, hlt, hc4]⟩

/-- Functional specification of a single `pageInitTailStepProg` step. -/
theorem pageInitTailStepProg_spec {L : PageArenaLayout} {n_0 cur : ℕ} {s : Memory.State}
    (hv : L.Valid L.w s.frontier) (hn0 : n_0 ≤ L.nCap) (hcur : cur ≤ 8 * L.pgB) :
    let q₀ := if n_0 < L.pgB + (L.pgB + L.pgB / 2) then 0 else (n_0 - (L.pgB + L.pgB / 2)) / L.pgB
    let qbm := (q₀ * L.pgB) % (8 * L.pgB)
    let s' := (Memory.spec 0).clientState s (pageInitTailStepProg ((L.toCtx, n_0), cur))
    let u := extractPageUnperm L s.mem
    let u' := extractPageUnperm L s'.mem
    (PageArenaLayout.ofCtx L.toCtx).Valid L.w s.frontier ∧
    (Memory.spec 0).clientResult s (pageInitTailStepProg ((L.toCtx, n_0), cur)) =
      min (8 * L.pgB) (cur + 1) ∧
    s'.frontier = s.frontier ∧
    memoryCost (pageInitTailStepProg ((L.toCtx, n_0), cur)) s ≤ 14 ∧
    (∀ addr, ¬(L.metaBase + L.offTail ≤ addr ∧
      addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w) →
      s'.mem addr = s.mem addr) ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem ∧
    u'.cleanPhase = u.cleanPhase ∧ u'.cleanVp = u.cleanVp ∧ u'.cleanOff = u.cleanOff ∧
    u'.st.pageSize = u.st.pageSize ∧ u'.st.fullPages = u.st.fullPages ∧
    u'.st.tailCount = u.st.tailCount ∧ u'.st.tailHead = u.st.tailHead ∧ u'.st.job = u.st.job ∧
    u'.st.pageOf = u.st.pageOf ∧ u'.st.ownerSide = u.st.ownerSide ∧
    u'.st.ownerVp = u.st.ownerVp ∧
    (∀ side k, k < 4 * L.pgB →
      u'.st.tailRes side k =
        if k = cur then (q₀ * L.pgB + k) % (8 * L.pgB) else u.st.tailRes side k) ∧
    (∀ res, res < 8 * L.pgB →
      (u'.st.tailOwnerSide res = if res = cur then false else u.st.tailOwnerSide res) ∧
      (u'.st.tailOwnerRing res =
        if res = cur then (res + 8 * L.pgB - qbm) % (8 * L.pgB)
        else u.st.tailOwnerRing res)) := by
  dsimp only
  set q₀ := if n_0 < L.pgB + (L.pgB + L.pgB / 2) then 0 else (n_0 - (L.pgB + L.pgB / 2)) / L.pgB
  set qbm := (q₀ * L.pgB) % (8 * L.pgB)
  have hv_ctx : (PageArenaLayout.ofCtx L.toCtx).Valid L.w s.frontier := by
    rwa [PageArenaLayout.ofCtx_toCtx]
  obtain ⟨hw, _, _, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hv
  have hfrm := pageInitTailBatchProg_frame (L := L) hw n_0 cur 1
  have hmc : memoryCost (pageInitTailStepProg ((L.toCtx, n_0), cur)) s ≤ 14 := by
    have hc := hfrm.cost_le s
    unfold pageInitTailBatchProg at hc; dsimp only at hc
    unfold iterate at hc
    rw [Realization.memoryCost_bind'] at hc
    exact le_trans (Nat.le_add_right _ _) (hc.trans (by omega))
  by_cases hlt : cur < 8 * L.pgB
  · obtain ⟨hst_eq, hcr_eq⟩ := pageInitTailStep_state s hn0 hlt
    have hmin : min (8 * L.pgB) (cur + 1) = cur + 1 := min_eq_right (by omega)
    set rv := (cur + 8 * L.pgB - qbm) % (8 * L.pgB)
    have hrv_lt : rv < 8 * L.pgB := Nat.mod_lt _ (by omega)
    rw [hst_eq, hcr_eq, hmin]
    by_cases hc4 : cur < 4 * L.pgB
    · rw [ite_eq_left hc4]
      set res_v := (qbm + cur) % (8 * L.pgB)
      have hres_mod : res_v = (q₀ * L.pgB + cur) % (8 * L.pgB) := by
        dsimp only [res_v, qbm]; rw [Nat.mod_add_mod]
      have hres_ptr : res_v < 2 ^ L.ptrB := by
        have : res_v < 8 * L.pgB := Nat.mod_lt _ (by omega)
        omega
      set m1 := writePacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (0 + cur) res_v
      set m2 := writePacked (L.metaBase + L.offTail) L.ptrB L.w m1 (4 * L.pgB + cur) res_v
      set m3 := writePacked (L.metaBase + L.offTail) L.ptrB L.w m2 (8 * L.pgB + cur) (0 + 2 * rv)
      obtain ⟨hu1, ha1⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib s.mem false hc4 hres_ptr
      obtain ⟨hu2, ha2⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib m1 true hc4 hres_ptr
      obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib m2
        hlt hrv_lt false
      simp only [Bool.false_eq_true, ↓reduceIte] at hu1 hu2 hu3
      have hout : ∀ addr, ¬(L.metaBase + L.offTail ≤ addr ∧
          addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w) →
          m3 addr = s.mem addr := fun addr ha => by
        dsimp only [m3, m2, m1]
        rw [writePacked_outside hw _ (by omega) _ ha,
          writePacked_outside hw _ (by omega) _ ha,
          writePacked_outside hw _ (by omega) _ ha]
      have hu_all : extractPageUnperm L m3 =
          { (extractPageUnperm L s.mem) with
            st := { (extractPageUnperm L s.mem).st with
              tailRes := PagePairState.set2
                (PagePairState.set2 (extractPageUnperm L s.mem).st.tailRes false cur res_v)
                true cur res_v
              tailOwnerSide := Function.update (extractPageUnperm L s.mem).st.tailOwnerSide cur
                false
              tailOwnerRing := Function.update (extractPageUnperm L s.mem).st.tailOwnerRing cur
                rv } } := by
        dsimp only [m3]; rw [hu3]; dsimp only [m2]; rw [hu2]; dsimp only [m1]; rw [hu1]
      refine ⟨hv_ctx, rfl, rfl, hmc, hout, ha3.trans (ha2.trans ha1), ?_⟩
      dsimp only
      change (let u' := extractPageUnperm L m3; _)
      rw [hu_all]; dsimp only
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun side k _ => ?_, fun res _ => ⟨?_, ?_⟩⟩
      · by_cases hk : k = cur
        · subst k; rw [ite_eq_left rfl, ← hres_mod]
          cases side
          · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (by simp), PagePairState.set2_self]
          · rw [PagePairState.set2_self]
        · rw [ite_eq_right hk, PagePairState.set2_of_ne _ _ _ _ _ _ (by simp [hk]),
            PagePairState.set2_of_ne _ _ _ _ _ _ (by simp [hk])]
      · by_cases hr : res = cur
        · subst res; simp
        · simp [hr]
      · by_cases hr : res = cur
        · subst res; simp [rv]
        · simp [hr]
    · rw [ite_eq_right hc4]
      set m3 := writePacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (8 * L.pgB + cur) (0 + 2 * rv)
      obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib s.mem
        hlt hrv_lt false
      simp only [Bool.false_eq_true, ↓reduceIte] at hu3
      have hout : ∀ addr, ¬(L.metaBase + L.offTail ≤ addr ∧
          addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w) →
          m3 addr = s.mem addr := fun addr ha =>
        writePacked_outside hw _ (by omega) _ ha
      refine ⟨hv_ctx, rfl, rfl, hmc, hout, ha3, ?_⟩
      dsimp only
      change (let u' := extractPageUnperm L m3; _)
      rw [hu3]; dsimp only
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ k hk => by rw [ite_eq_right (by omega)],
        fun res _ => ⟨?_, ?_⟩⟩
      · by_cases hr : res = cur
        · subst res; simp
        · simp [hr]
      · by_cases hr : res = cur
        · subst res; simp [rv]
        · simp [hr]
  · have heq : cur = 8 * L.pgB := by omega
    subst cur
    have hnc : ¬(n_0 ≤ L.nCap ∧ 8 * L.pgB < 8 * L.pgB) := by omega
    have hmin : min (8 * L.pgB) (8 * L.pgB + 1) = 8 * L.pgB := min_eq_left (by omega)
    have hst : (Memory.spec 0).clientState s
        (pageInitTailStepProg ((L.toCtx, n_0), 8 * L.pgB)) = s := by
      unfold pageInitTailStepProg; dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_right hnc]; rfl
    have hcr : (Memory.spec 0).clientResult s
        (pageInitTailStepProg ((L.toCtx, n_0), 8 * L.pgB)) = 8 * L.pgB := by
      unfold pageInitTailStepProg; dsimp only [PageArenaLayout.toCtx]
      rw [ite_eq_right hnc]; rfl
    rw [hst, hcr, hmin]
    exact ⟨hv_ctx, rfl, rfl, hmc, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl,
      fun _ _ hk => by rw [ite_eq_right (by omega)],
      fun _ hr => ⟨by rw [ite_eq_right hr.ne], by rw [ite_eq_right hr.ne]⟩⟩

theorem pageInitTailStepProg_fr (ctx : PageArenaCtx) (nSnap c0 w : ℕ) (st : Memory.State)
    (hv_st : (PageArenaLayout.ofCtx ctx).Valid w st.frontier) :
    ((Memory.spec 0).clientState st (pageInitTailStepProg ((ctx, nSnap), c0))).frontier =
      st.frontier := by
  have hce : (PageArenaLayout.ofCtx ctx).toCtx = ctx := by
    rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
  have hw_c : 0 < (PageArenaLayout.ofCtx ctx).w := by rw [← hv_st.2.1]; exact hv_st.1
  have hfrm := pageInitTailBatchProg_frame (L := PageArenaLayout.ofCtx ctx) hw_c nSnap c0 1
  rw [hce] at hfrm
  have hf1 := hfrm.frontier_eq st
  unfold pageInitTailBatchProg at hf1; dsimp only at hf1; unfold iterate at hf1
  rw [StateTransitionSpec.clientState_bind] at hf1; exact hf1

attribute [local irreducible] pageInitTailStepProg

/-- Batched specification of `pageInitTailBatchProg` across `fuel` entries. -/
theorem pageInitTailBatchProg_spec {L : PageArenaLayout} {n_0 cur : ℕ} {s : Memory.State}
    (hv : L.Valid L.w s.frontier) (hn0 : n_0 ≤ L.nCap) (hcur : cur ≤ 8 * L.pgB) (fuel : ℕ) :
    let q₀ := if n_0 < L.pgB + (L.pgB + L.pgB / 2) then 0 else (n_0 - (L.pgB + L.pgB / 2)) / L.pgB
    let qbm := (q₀ * L.pgB) % (8 * L.pgB)
    let s' := (Memory.spec 0).clientState s (pageInitTailBatchProg (((L.toCtx, n_0), cur), fuel))
    let u := extractPageUnperm L s.mem
    let u' := extractPageUnperm L s'.mem
    iterationSafe pageInitTailStepProg
      (fun w' ((c', _), _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
      L.w (L.toCtx, n_0) fuel cur s ∧
    (Memory.spec 0).clientResult s (pageInitTailBatchProg (((L.toCtx, n_0), cur), fuel)) =
      min (8 * L.pgB) (cur + fuel) ∧
    s'.frontier = s.frontier ∧
    memoryCost (pageInitTailBatchProg (((L.toCtx, n_0), cur), fuel)) s ≤ 14 * fuel ∧
    (∀ addr, ¬(L.metaBase + L.offTail ≤ addr ∧
      addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w) →
      s'.mem addr = s.mem addr) ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem ∧
    u'.cleanPhase = u.cleanPhase ∧ u'.cleanVp = u.cleanVp ∧ u'.cleanOff = u.cleanOff ∧
    u'.st.pageSize = u.st.pageSize ∧ u'.st.fullPages = u.st.fullPages ∧
    u'.st.tailCount = u.st.tailCount ∧ u'.st.tailHead = u.st.tailHead ∧ u'.st.job = u.st.job ∧
    u'.st.pageOf = u.st.pageOf ∧ u'.st.ownerSide = u.st.ownerSide ∧
    u'.st.ownerVp = u.st.ownerVp ∧
    (∀ side k, k < 4 * L.pgB →
      u'.st.tailRes side k =
        if cur ≤ k ∧ k < min (8 * L.pgB) (cur + fuel) then (q₀ * L.pgB + k) % (8 * L.pgB)
        else u.st.tailRes side k) ∧
    (∀ res, res < 8 * L.pgB →
      (u'.st.tailOwnerSide res =
        if cur ≤ res ∧ res < min (8 * L.pgB) (cur + fuel) then false
        else u.st.tailOwnerSide res) ∧
      (u'.st.tailOwnerRing res =
        if cur ≤ res ∧ res < min (8 * L.pgB) (cur + fuel) then
          (res + 8 * L.pgB - qbm) % (8 * L.pgB)
        else u.st.tailOwnerRing res)) := by
  dsimp only
  unfold pageInitTailBatchProg; dsimp only
  induction fuel generalizing s cur with
  | zero =>
    unfold iterate
    have hmin : min (8 * L.pgB) (cur + 0) = cur := min_eq_right (by omega)
    rw [hmin]
    have hf_r : ∀ r, ¬(cur ≤ r ∧ r < cur) := fun _ => by omega
    exact ⟨trivial, rfl, rfl, Nat.zero_le _, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl,
      fun _ j _ => by rw [ite_eq_right (hf_r j)]; rfl,
      fun res _ => ⟨by rw [ite_eq_right (hf_r res)]; rfl,
        by rw [ite_eq_right (hf_r res)]; rfl⟩⟩
  | succ k ih =>
    obtain ⟨hv1, hres1, hfr1, hc1, hout1, har1, hcp1, hcv1, hco1, hps1, hfp1, htc1, hth1, hj1,
      hpo1, hos1, hov1, htr1, hto1⟩ := pageInitTailStepProg_spec hv hn0 hcur
    set s1 := (Memory.spec 0).clientState s (pageInitTailStepProg ((L.toCtx, n_0), cur))
    set c1 := min (8 * L.pgB) (cur + 1)
    obtain ⟨hsafe, hres2, hfr2, hc2, hout2, har2, hcp2, hcv2, hco2, hps2, hfp2, htc2, hth2, hj2,
      hpo2, hos2, hov2, htr2, hto2⟩ :=
      ih (s := s1) (cur := c1) (hfr1.symm ▸ hv) (min_le_left _ _)
    have hmin_eq : min (8 * L.pgB) (c1 + k) = min (8 * L.pgB) (cur + (k + 1)) := by
      dsimp only [c1]; omega
    have hcost_tot : memoryCost (iterate pageInitTailStepProg (L.toCtx, n_0) (k + 1) cur) s ≤
        14 * (k + 1) := by
      unfold iterate
      rw [Realization.memoryCost_bind', hres1]
      change memoryCost (pageInitTailStepProg ((L.toCtx, n_0), cur)) s +
        memoryCost (iterate pageInitTailStepProg (L.toCtx, n_0) k c1) s1 ≤ 14 * (k + 1)
      omega
    have hsafe_tot : iterationSafe pageInitTailStepProg
        (fun w' ((c', _), _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
        L.w (L.toCtx, n_0) (k + 1) cur s := by
      unfold iterationSafe
      rw [clientResult_width, clientState_width, hres1]
      exact ⟨hv1, hsafe⟩
    have hst_tot : (Memory.spec 0).clientState s
        (iterate pageInitTailStepProg (L.toCtx, n_0) (k + 1) cur) =
        (Memory.spec 0).clientState s1 (iterate pageInitTailStepProg (L.toCtx, n_0) k c1) := by
      conv_lhs => unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres1]
    have hres_tot : (Memory.spec 0).clientResult s
        (iterate pageInitTailStepProg (L.toCtx, n_0) (k + 1) cur) =
        min (8 * L.pgB) (cur + (k + 1)) := by
      unfold iterate
      rw [prog_clientResult_bind, hres1]
      exact hres2.trans hmin_eq
    rw [hst_tot]
    refine ⟨hsafe_tot, hres_tot, hfr2.trans hfr1, hcost_tot,
      fun addr ha => (hout2 addr ha).trans (hout1 addr ha),
      har2.trans har1, hcp2.trans hcp1, hcv2.trans hcv1, hco2.trans hco1,
      hps2.trans hps1, hfp2.trans hfp1, htc2.trans htc1, hth2.trans hth1, hj2.trans hj1,
      hpo2.trans hpo1, hos2.trans hos1, hov2.trans hov1,
      fun side j hj => ?_, fun res hr => ⟨?_, ?_⟩⟩
    · rw [htr2 side j hj, hmin_eq]
      by_cases h2 : c1 ≤ j ∧ j < min (8 * L.pgB) (cur + (k + 1))
      · have h2' : cur ≤ j ∧ j < min (8 * L.pgB) (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, htr1 side j hj]
        by_cases h0 : j = cur
        · subst j
          have h0' : cur ≤ cur ∧ cur < min (8 * L.pgB) (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ j ∧ j < min (8 * L.pgB) (cur + (k + 1))) := by
            have hj8 : j < 8 * L.pgB := by omega
            dsimp only [c1, Nat.min_def] at h2 ⊢; split_ifs at h2 ⊢ <;> omega
          rw [ite_eq_right h0, ite_eq_right hn0']
    · rw [(hto2 res hr).1, hmin_eq]
      by_cases h2 : c1 ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1))
      · have h2' : cur ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, (hto1 res hr).1]
        by_cases h0 : res = cur
        · subst res
          have h0' : cur ≤ cur ∧ cur < min (8 * L.pgB) (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1))) := by
            dsimp only [c1] at h2; omega
          rw [ite_eq_right h0, ite_eq_right hn0']
    · rw [(hto2 res hr).2, hmin_eq]
      by_cases h2 : c1 ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1))
      · have h2' : cur ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1)) :=
          ⟨by dsimp only [c1] at h2; omega, h2.2⟩
        rw [ite_eq_left h2, ite_eq_left h2']
      · rw [ite_eq_right h2, (hto1 res hr).2]
        by_cases h0 : res = cur
        · subst res
          have h0' : cur ≤ cur ∧ cur < min (8 * L.pgB) (cur + (k + 1)) := ⟨le_rfl, by omega⟩
          rw [ite_eq_left rfl, ite_eq_left h0']
        · have hn0' : ¬(cur ≤ res ∧ res < min (8 * L.pgB) (cur + (k + 1))) := by
            dsimp only [c1] at h2; omega
          rw [ite_eq_right h0, ite_eq_right hn0']

/-- Memory history admissibility for `migrateStepProg`. -/
theorem validHistory_migrateStepProg {w pSrc pDst moved : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : MigrateStepPre w ((pSrc, pDst), moved) s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (migrateStepProg ((pSrc, pDst), moved))) := by
  obtain ⟨hsrc, hdst⟩ := hpre
  unfold migrateStepProg
  refine vh_seq (validHistory_epochReadNSideProg hsrc) fun s1 hs1 nS hnS => ?_
  rw [hs1, clientState_epochReadNSideProg]
  refine vh_ite (0 < nS) (fun hpos => ?_) (fun _ => trivial)
  have hpa := validHistory_epochPopAnyProg hwf hsrc
  refine vh_seq hpa fun s2 hs2 _ _ => ?_
  have hwf2 := wf_step hwf hpa
  rw [hs2]
  exact vh_seq (validHistory_epochInsertProg hwf2 (hdst (hnS ▸ hpos))) fun _ _ _ _ => trivial

/-- Memory history admissibility for `migrateBatchProg` under `iterationSafe`. -/
theorem validHistory_migrateBatchProg {w pSrc pDst moved fuel : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hsafe : iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) fuel moved s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (migrateBatchProg (((pSrc, pDst), moved), fuel))) := by
  unfold migrateBatchProg
  induction fuel generalizing s moved with
  | zero => exact trivial
  | succ k ih =>
    unfold iterationSafe at hsafe
    rw [clientResult_width, clientState_width] at hsafe
    obtain ⟨h1, hrest⟩ := hsafe
    have vh1 := validHistory_migrateStepProg hwf h1
    exact vh_seq vh1 fun s1 hs1 r1 hr1 => by
      rw [hs1, hr1]
      exact ih (wf_step hwf vh1) hrest


/-! ## Section 2: Overflow-Free Trigger and Slot-I/O Control Helpers -/

/-- The result of `epochReadNSideProg` always fits in `w` bits on a well-formed state. -/
theorem epochReadNSideProg_fits {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) :
    Fits w ((Memory.spec 0).clientResult s (epochReadNSideProg pBase)) := by
  unfold epochReadNSideProg
  rw [prog_clientResult_bind, cstate_rd, cres_rd, cres_rd]
  exact hwf.2 _

/-- Pure evaluation of `pairStreamWordsSafeProg` (`0` queries). -/
theorem pairStreamWordsSafeProg_res {n q v w : ℕ} (hw : 0 < w) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pairStreamWordsSafeProg (((n, q), v), w)) =
      pairStreamWords n q v w :=
  (pairStreamWordsSafeProg_spec n q v w hw s).2.1

@[simp] theorem runClient_state_pairStreamWordsSafeProg (x : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pairStreamWordsSafeProg x)) = s := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

@[simp] theorem clientState_pairStreamWordsSafeProg (x : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (pairStreamWordsSafeProg x) = s :=
  runClient_state_pairStreamWordsSafeProg x s

theorem validHistory_pairStreamWordsSafeProg (w : ℕ) (x : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pairStreamWordsSafeProg x)) := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, _⟩; exact trivial

attribute [local irreducible] pageInitDirBatchProg pageInitTailBatchProg
attribute [local irreducible] migrateStepProg migrateBatchProg pairStreamWordsSafeProg
attribute [local irreducible] setSlotIoProg writeSmallParamTableProg
attribute [local irreducible] writeLargeParamTableProg WriteLargeParamPre
attribute [local irreducible] epochQueryProg epochInsertProg epochDeleteProg
attribute [local irreducible] epochPopAnyProg epochInitZeroedProg epochReadNSideProg

/-- Extract `(metaBase, (pgB, maxPages))` from a `PageArenaCtx` register tuple (`0` queries). -/
def pageCtxScalarsProg : PageArenaCtx → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((mb, _), _), ((_, pg), (mp, _))), _) => pure (mb, (pg, mp))

@[simp] theorem runClient_state_pageCtxScalarsProg (c : PageArenaCtx) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageCtxScalarsProg c)) = s := by
  rcases c with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

@[simp] theorem clientState_pageCtxScalarsProg (c : PageArenaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (pageCtxScalarsProg c) = s :=
  runClient_state_pageCtxScalarsProg c s

@[simp] theorem clientResult_pageCtxScalarsProg (c : PageArenaCtx) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pageCtxScalarsProg c) =
      ((PageArenaLayout.ofCtx c).metaBase,
       ((PageArenaLayout.ofCtx c).pgB, (PageArenaLayout.ofCtx c).maxPages)) := by
  rcases c with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

@[simp] theorem memoryCost_pageCtxScalarsProg (c : PageArenaCtx) (s : Memory.State) :
    memoryCost (pageCtxScalarsProg c) s = 0 := by
  rcases c with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

theorem validHistory_pageCtxScalarsProg (w : ℕ) (c : PageArenaCtx) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (pageCtxScalarsProg c)) := by
  rcases c with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; exact trivial

theorem realizesBounded_pageCtxScalars :
    RealizesBounded .exact pageCtxScalarsProg
      (WordEncoding.encode (α := PageArenaCtx))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Truncating subtraction `a - b` in `Basis.exact` (`0` queries, `0` preconditions). -/
def clampSubProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if b < a then pure (a - b) else pure 0

@[simp] theorem runClient_state_clampSubProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (clampSubProg x)) = s := by
  rcases x with ⟨a, b⟩; unfold clampSubProg; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_clampSubProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (clampSubProg x) = s :=
  runClient_state_clampSubProg x s

@[simp] theorem clientResult_clampSubProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (clampSubProg (a, b)) = a - b := by
  unfold clampSubProg; dsimp only
  split_ifs <;> (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure]; try omega)

@[simp] theorem memoryCost_clampSubProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (clampSubProg x) s = 0 := by
  rcases x with ⟨a, b⟩; unfold clampSubProg; dsimp only; split_ifs <;> rfl

theorem validHistory_clampSubProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (clampSubProg x)) := by
  rcases x with ⟨a, b⟩; unfold clampSubProg; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_clampSub :
    RealizesBounded .exact clampSubProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  all_goals (rcases d with ⟨a, b⟩; dsimp only [Fits] at *; omega)

/-- Exact `max a b` in `Basis.exact` (`0` queries, `0` preconditions). -/
def max2Prog : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure b else pure a

@[simp] theorem runClient_state_max2Prog (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (max2Prog x)) = s := by
  rcases x with ⟨a, b⟩; unfold max2Prog; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_max2Prog (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (max2Prog x) = s :=
  runClient_state_max2Prog x s

@[simp] theorem clientResult_max2Prog (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (max2Prog (a, b)) = max a b := by
  unfold max2Prog; dsimp only
  split_ifs <;>
    (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure, Nat.max_def]
     split_ifs <;> omega)

@[simp] theorem memoryCost_max2Prog (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (max2Prog x) s = 0 := by
  rcases x with ⟨a, b⟩; unfold max2Prog; dsimp only; split_ifs <;> rfl

theorem validHistory_max2Prog (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (max2Prog x)) := by
  rcases x with ⟨a, b⟩; unfold max2Prog; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_max2 :
    RealizesBounded .exact max2Prog
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Exact `min a b` in `Basis.exact` (`0` queries, `0` preconditions). -/
def min2Prog : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure a else pure b

@[simp] theorem runClient_state_min2Prog (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (min2Prog x)) = s := by
  rcases x with ⟨a, b⟩; unfold min2Prog; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_min2Prog (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (min2Prog x) = s :=
  runClient_state_min2Prog x s

@[simp] theorem clientResult_min2Prog (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (min2Prog (a, b)) = min a b := by
  unfold min2Prog; dsimp only
  split_ifs <;>
    (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure, Nat.min_def]
     split_ifs <;> omega)

@[simp] theorem memoryCost_min2Prog (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (min2Prog x) s = 0 := by
  rcases x with ⟨a, b⟩; unfold min2Prog; dsimp only; split_ifs <;> rfl

theorem validHistory_min2Prog (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (min2Prog x)) := by
  rcases x with ⟨a, b⟩; unfold min2Prog; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_min2 :
    RealizesBounded .exact min2Prog
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Word selector `if flag = 0 then v0 else v1` (`0` queries, `0` preconditions). -/
def selectEq0Prog : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (flag, (v0, v1)) => if flag = 0 then pure v0 else pure v1

@[simp] theorem runClient_state_selectEq0Prog (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (selectEq0Prog x)) = s := by
  rcases x with ⟨f, ⟨v0, v1⟩⟩; unfold selectEq0Prog; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_selectEq0Prog (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (selectEq0Prog x) = s :=
  runClient_state_selectEq0Prog x s

@[simp] theorem clientResult_selectEq0Prog (f v0 v1 : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (selectEq0Prog (f, (v0, v1))) = if f = 0 then v0 else v1 := by
  unfold selectEq0Prog; dsimp only; split_ifs <;> rfl

@[simp] theorem memoryCost_selectEq0Prog (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (selectEq0Prog x) s = 0 := by
  rcases x with ⟨f, ⟨v0, v1⟩⟩; unfold selectEq0Prog; dsimp only; split_ifs <;> rfl

theorem validHistory_selectEq0Prog (w : ℕ) (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (selectEq0Prog x)) := by
  rcases x with ⟨f, ⟨v0, v1⟩⟩; unfold selectEq0Prog; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_selectEq0 :
    RealizesBounded .exact selectEq0Prog
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Pair selector `if flag = 0 then p0 else p1` (`0` queries, `0` preconditions). -/
def selectEq0PairProg : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog (ℕ × ℕ)
  | (flag, (p0, p1)) => if flag = 0 then pure p0 else pure p1

@[simp] theorem runClient_state_selectEq0PairProg (x : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)))
    (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (selectEq0PairProg x)) = s := by
  rcases x with ⟨f, ⟨p0, p1⟩⟩; unfold selectEq0PairProg; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_selectEq0PairProg (x : ℕ × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (selectEq0PairProg x) = s :=
  runClient_state_selectEq0PairProg x s

@[simp] theorem clientResult_selectEq0PairProg (f : ℕ) (p0 p1 : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (selectEq0PairProg (f, (p0, p1))) =
      if f = 0 then p0 else p1 := by
  unfold selectEq0PairProg; dsimp only; split_ifs <;> rfl

@[simp] theorem memoryCost_selectEq0PairProg (x : ℕ × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (selectEq0PairProg x) s = 0 := by
  rcases x with ⟨f, ⟨p0, p1⟩⟩; unfold selectEq0PairProg; dsimp only; split_ifs <;> rfl

theorem validHistory_selectEq0PairProg (w : ℕ) (x : ℕ × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (selectEq0PairProg x)) := by
  rcases x with ⟨f, ⟨p0, p1⟩⟩; unfold selectEq0PairProg; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_selectEq0Pair :
    RealizesBounded .exact selectEq0PairProg
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Destination metadata base `if stg = 0 then base + 192 + pad else base + 192` (`0` queries). -/
def metaDstAddrProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (stg, (base, pad)) => if stg = 0 then pure (base + 192 + pad) else pure (base + 192)

@[simp] theorem runClient_state_metaDstAddrProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (metaDstAddrProg x)) = s := by
  rcases x with ⟨stg, ⟨b, p⟩⟩; unfold metaDstAddrProg; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_metaDstAddrProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (metaDstAddrProg x) = s :=
  runClient_state_metaDstAddrProg x s

@[simp] theorem clientResult_metaDstAddrProg (stg base pad : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (metaDstAddrProg (stg, (base, pad))) =
      if stg = 0 then base + 192 + pad else base + 192 := by
  unfold metaDstAddrProg; dsimp only; split_ifs <;> rfl

@[simp] theorem memoryCost_metaDstAddrProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (metaDstAddrProg x) s = 0 := by
  rcases x with ⟨stg, ⟨b, p⟩⟩; unfold metaDstAddrProg; dsimp only; split_ifs <;> rfl

theorem validHistory_metaDstAddrProg (w : ℕ) (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (metaDstAddrProg x)) := by
  rcases x with ⟨stg, ⟨b, p⟩⟩; unfold metaDstAddrProg; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_metaDstAddr :
    RealizesBounded .exact metaDstAddrProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (stg, (base, pad)) _ => Fits w (if stg = 0 then base + 192 + pad else base + 192))
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨stg, ⟨base, pad⟩⟩
    dsimp only [Fits] at *
    split_ifs at *; omega)

/-- Active `(pSrc, pDst)` parameter-table bases for `stage ∈ {0, 1}` (`0` queries). -/
def slotPairProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (stg, base) =>
    if stg = 0 then pure (base + hdrPBase0, base + hdrPBase1)
    else pure (base + hdrPBase1, base + hdrPBase0)

@[simp] theorem runClient_state_slotPairProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (slotPairProg x)) = s := by
  rcases x with ⟨stg, b⟩; unfold slotPairProg; dsimp only; split_ifs <;> rfl

@[simp] theorem clientState_slotPairProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (slotPairProg x) = s :=
  runClient_state_slotPairProg x s

@[simp] theorem clientResult_slotPairProg (stg base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (slotPairProg (stg, base)) =
      (if stg = 0 then base + hdrPBase0 else base + hdrPBase1,
       if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
  unfold slotPairProg; dsimp only; split_ifs <;> rfl

@[simp] theorem memoryCost_slotPairProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (slotPairProg x) s = 0 := by
  rcases x with ⟨stg, b⟩; unfold slotPairProg; dsimp only; split_ifs <;> rfl

theorem validHistory_slotPairProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (slotPairProg x)) := by
  rcases x with ⟨stg, b⟩; unfold slotPairProg; dsimp only; split_ifs <;> exact trivial

theorem realizesBounded_slotPair :
    RealizesBounded .exact slotPairProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (_, base) _ => Fits w (base + 128))
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨stg, base⟩
    dsimp only [hdrPBase0, hdrPBase1, Fits] at *
    omega)

/-- Overflow-free computation of `min (2 * nLive) (u1 + 1)`. -/
private def capDoubleProg : ℕ × ℕ → Memory.Prog ℕ
  | (u1, nLive) =>
    if u1 < nLive then pure (u1 + 1)
    else if u1 - nLive < nLive then pure (u1 + 1)
    else pure (2 * nLive)

@[simp] private theorem runClient_state_capDoubleProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (capDoubleProg x)) = s := by
  rcases x with ⟨u1, nL⟩; unfold capDoubleProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_capDoubleProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (capDoubleProg x) = s :=
  runClient_state_capDoubleProg x s

@[simp] private theorem clientResult_capDoubleProg (u1 nLive : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (capDoubleProg (u1, nLive)) = min (2 * nLive) (u1 + 1) := by
  unfold capDoubleProg; dsimp only
  split_ifs <;>
    (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure, Nat.min_def]
     split_ifs <;> omega)

@[simp] private theorem memoryCost_capDoubleProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (capDoubleProg x) s = 0 := by
  rcases x with ⟨u1, nL⟩; unfold capDoubleProg; dsimp only; split_ifs <;> rfl

private theorem validHistory_capDoubleProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (capDoubleProg x)) := by
  rcases x with ⟨u1, nL⟩; unfold capDoubleProg; dsimp only; split_ifs <;> exact trivial

private theorem realizesBounded_capDouble :
    RealizesBounded .exact capDoubleProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (u1, _) _ => 2 ≤ w ∧ Fits w (u1 + 1)) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨u1, nLive⟩
    dsimp only [Fits] at *
    obtain ⟨hw2, hu1⟩ := h
    have h4 : 4 ≤ 2 ^ w := (by decide : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide) hw2
    omega)

/-- Pure decision helper for `checkTriggerProg` once `(u1, th, nLive, nSrc, ops, m2, remBit)` are
loaded (native `<` / `=` tests only, `0` branch duplication). -/
private def decideTriggerProg :
    ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((u1, th), (nLive, nSrc)), ((ops, m2), remBit)) =>
    if nSrc = 0 then
      if 0 < th then
        if nLive < th then pure (0, 0) else pure (1, m2)
      else pure (0, 0)
    else if u1 < nSrc then
      if 2 * (nSrc / 5) + (2 * (nSrc % 5)) / 5 < nLive then
        if ops < nSrc / 4 + remBit then pure (0, 0) else pure (1, nSrc)
      else if nLive < th / 2 then pure (1, 0) else pure (1, m2)
    else if nLive < 3 * (nSrc / 4) + nSrc % 4 then
      if 2 * (nSrc / 5) + (2 * (nSrc % 5)) / 5 < nLive then
        if ops < nSrc / 4 + remBit then pure (0, 0) else pure (1, nSrc)
      else if nLive < th / 2 then pure (1, 0) else pure (1, m2)
    else
      pure (1, m2)

@[simp] private theorem runClient_state_decideTriggerProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (decideTriggerProg x)) = s := by
  rcases x with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold decideTriggerProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_decideTriggerProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (decideTriggerProg x) = s :=
  runClient_state_decideTriggerProg x s

@[simp] private theorem memoryCost_decideTriggerProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (decideTriggerProg x) s = 0 := by
  rcases x with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold decideTriggerProg; dsimp only; split_ifs <;> rfl

private theorem validHistory_decideTriggerProg (w : ℕ)
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (decideTriggerProg x)) := by
  rcases x with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold decideTriggerProg; dsimp only; split_ifs <;> exact trivial

private theorem realizesBounded_decideTrigger :
    RealizesBounded .exact decideTriggerProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (((u1, _), (nLive, nSrc)), ((_, _), remBit)) _ =>
        4 ≤ w ∧ Fits w (u1 + 1) ∧ nLive ≤ u1 + 1 ∧ nSrc ≤ u1 + 1 ∧ remBit ≤ 1)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨u1, th⟩, ⟨nLive, nSrc⟩⟩, ⟨⟨ops, m2⟩, remBit⟩⟩
    dsimp only [Fits] at *
    obtain ⟨hw4, hu1, hnl, hns, hrb⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hns_d4 : nSrc / 4 * 4 + nSrc % 4 = nSrc := by have := Nat.div_add_mod nSrc 4; omega
    have hns_d5 : nSrc / 5 * 5 + nSrc % 5 = nSrc := by have := Nat.div_add_mod nSrc 5; omega
    have hm5 : nSrc % 5 < 5 := Nat.mod_lt _ (by decide)
    omega)

/-- Overflow-free trigger check matching `dualTriggerCap` (`(0, 0)` = `none`, `(1, nDst)` =
`some nDst`). -/
def checkTriggerProg (base : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let u1 ← Memory.read (base + hdrU1)
  let th ← Memory.read (base + hdrThresh)
  let nLive ← Memory.read (base + hdrLive)
  let nSrc ← Memory.read (base + hdrNSrc)
  let ops ← Memory.read (base + hdrEpochOps)
  let m2 ← capDoubleProg (u1, nLive)
  let remBit ← selectEq0Prog (nSrc % 4, (0, 1))
  decideTriggerProg (((u1, th), (nLive, nSrc)), ((ops, m2), remBit))

@[simp] theorem runClient_state_checkTriggerProg (base : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (checkTriggerProg base)) = s := by
  simp [checkTriggerProg]

@[simp] theorem clientState_checkTriggerProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (checkTriggerProg base) = s :=
  runClient_state_checkTriggerProg base s

theorem checkTriggerProg_res2_fits {w base : ℕ} {s : Memory.State}
    (hu1 : Fits w (s.mem (base + hdrU1) + 1))
    (hns : s.mem (base + hdrNSrc) ≤ s.mem (base + hdrU1) + 1) :
    Fits w ((Memory.spec 0).clientResult s (checkTriggerProg base)).2 := by
  unfold checkTriggerProg
  iterate 5 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  rw [prog_clientResult_bind, clientState_capDoubleProg, clientResult_capDoubleProg,
    prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog]
  unfold decideTriggerProg; dsimp only [Fits] at *
  split_ifs <;>
    (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure, Nat.min_def]
     (try split_ifs) <;> omega)

theorem checkTriggerProg_spec {c U V w base : ℕ} {s : Memory.State}
    (hU : 0 < U) (hhdr : RootStaticHeader c U V w base s.mem)
    (hsrc_ok : s.mem (base + hdrNSrc) = 0 ∨
      (whpThreshold c ≤ s.mem (base + hdrNSrc) ∧ s.mem (base + hdrNSrc) ≤ U)) :
    (Memory.spec 0).clientState s (checkTriggerProg base) = s ∧
    memoryCost (checkTriggerProg base) s = 5 ∧
    (Memory.spec 0).clientResult s (checkTriggerProg base) =
      match dualTriggerCap c U (s.mem (base + hdrNSrc)) (s.mem (base + hdrLive))
        (s.mem (base + hdrEpochOps)) with
      | none => (0, 0)
      | some d => (1, d) := by
  have hu1 : s.mem (base + hdrU1) = U - 1 := hhdr.1
  have hu1_succ : s.mem (base + hdrU1) + 1 = U := by omega
  have hth_m : s.mem (base + hdrThresh) = if whpThreshold c ≤ U then whpThreshold c else 0 :=
    hhdr.2.2.2.2.2.1
  set nLive := s.mem (base + hdrLive)
  set nSrc := s.mem (base + hdrNSrc)
  set ops := s.mem (base + hdrEpochOps)
  have hmc : memoryCost (checkTriggerProg base) s = 5 := by
    simp [checkTriggerProg]
  refine ⟨clientState_checkTriggerProg base s, hmc, ?_⟩
  unfold checkTriggerProg
  iterate 5 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  rw [prog_clientResult_bind, clientState_capDoubleProg, clientResult_capDoubleProg,
    prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog, hu1_succ]
  unfold decideTriggerProg dualTriggerCap
  dsimp only
  by_cases h0 : nSrc = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hth_pos := whpThreshold_pos c
    by_cases hleU : whpThreshold c ≤ U
    · rw [hth_m, ite_eq_left hleU, ite_eq_left hth_pos]
      by_cases hleL : whpThreshold c ≤ nLive
      · rw [ite_eq_right (show ¬nLive < whpThreshold c by omega), ite_eq_left ⟨hleU, hleL⟩]; rfl
      · rw [ite_eq_left (show nLive < whpThreshold c by omega),
          ite_eq_right (show ¬(whpThreshold c ≤ U ∧ whpThreshold c ≤ nLive) by omega)]; rfl
    · rw [hth_m, ite_eq_right hleU, ite_eq_right (Nat.lt_irrefl 0),
        ite_eq_right (show ¬(whpThreshold c ≤ U ∧ whpThreshold c ≤ nLive) by omega)]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    rcases hsrc_ok with habs | ⟨hth_src, hsrcU⟩
    · exact absurd habs h0
    have hU_th : whpThreshold c ≤ U := hth_src.trans hsrcU
    have hth_val : s.mem (base + hdrThresh) = whpThreshold c := by rw [hth_m, ite_eq_left hU_th]
    have hth_even : whpThreshold c % 2 = 0 := by
      rw [whpThreshold_eq]
      have hb : 1 ≤ bMinWhp c := (by decide : 1 ≤ 6553600).trans (le_bMinWhp c)
      rw [show bMinWhp c = (bMinWhp c - 1) + 1 by omega, Nat.pow_succ]; omega
    rw [hu1, hth_val]
    have hd4 := Nat.div_add_mod nSrc 4
    have hd5 := Nat.div_add_mod nSrc 5
    have hd2 := Nat.div_add_mod (whpThreshold c) 2
    by_cases hltU : nSrc < U
    · rw [ite_eq_right (show ¬(U - 1 < nSrc) by omega)]
      by_cases hg : 3 * nSrc ≤ 4 * nLive
      · rw [ite_eq_right (show ¬(nLive < 3 * (nSrc / 4) + nSrc % 4) by omega),
          ite_eq_left ⟨hltU, hg⟩]; rfl
      · rw [ite_eq_left (show nLive < 3 * (nSrc / 4) + nSrc % 4 by omega),
          ite_eq_right (show ¬(nSrc < U ∧ 3 * nSrc ≤ 4 * nLive) by omega)]
        by_cases hs : 5 * nLive ≤ 2 * nSrc
        · rw [ite_eq_right (show ¬(2 * (nSrc / 5) + 2 * (nSrc % 5) / 5 < nLive) by omega),
            ite_eq_left hs]
          by_cases hsm : 2 * nLive < whpThreshold c
          · rw [ite_eq_left (show nLive < whpThreshold c / 2 by omega), ite_eq_left hsm]; rfl
          · rw [ite_eq_right (show ¬nLive < whpThreshold c / 2 by omega), ite_eq_right hsm]; rfl
        · rw [ite_eq_left (show 2 * (nSrc / 5) + 2 * (nSrc % 5) / 5 < nLive by omega),
            ite_eq_right hs]
          by_cases hr : nSrc ≤ 4 * ops
          · have hr' : ¬(ops < nSrc / 4 + (if nSrc % 4 = 0 then 0 else 1)) := by split_ifs <;> omega
            rw [ite_eq_right hr', ite_eq_left hr]; rfl
          · have hnr' : ops < nSrc / 4 + (if nSrc % 4 = 0 then 0 else 1) := by split_ifs <;> omega
            rw [ite_eq_left hnr', ite_eq_right hr]; rfl
    · rw [ite_eq_left (show U - 1 < nSrc by omega),
        ite_eq_right (show ¬(nSrc < U ∧ 3 * nSrc ≤ 4 * nLive) by omega)]
      by_cases hs : 5 * nLive ≤ 2 * nSrc
      · rw [ite_eq_right (show ¬(2 * (nSrc / 5) + 2 * (nSrc % 5) / 5 < nLive) by omega),
          ite_eq_left hs]
        by_cases hsm : 2 * nLive < whpThreshold c
        · rw [ite_eq_left (show nLive < whpThreshold c / 2 by omega), ite_eq_left hsm]; rfl
        · rw [ite_eq_right (show ¬nLive < whpThreshold c / 2 by omega), ite_eq_right hsm]; rfl
      · rw [ite_eq_left (show 2 * (nSrc / 5) + 2 * (nSrc % 5) / 5 < nLive by omega),
          ite_eq_right hs]
        by_cases hr : nSrc ≤ 4 * ops
        · have hr' : ¬(ops < nSrc / 4 + (if nSrc % 4 = 0 then 0 else 1)) := by split_ifs <;> omega
          rw [ite_eq_right hr', ite_eq_left hr]; rfl
        · have hnr' : ops < nSrc / 4 + (if nSrc % 4 = 0 then 0 else 1) := by split_ifs <;> omega
          rw [ite_eq_left hnr', ite_eq_right hr]; rfl

theorem validHistory_checkTriggerProg {w base : ℕ} {s : Memory.State}
    (hfr : base + 16 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (checkTriggerProg base)) := by
  unfold checkTriggerProg
  refine vh_rd (by unfold hdrU1; omega) <| vh_rd (by unfold hdrThresh; omega) <|
    vh_rd (by unfold hdrLive; omega) <| vh_rd (by unfold hdrNSrc; omega) <|
    vh_rd (by unfold hdrEpochOps; omega) ?_
  refine vh_seq (validHistory_capDoubleProg w _ s) fun s1 hs1 _ _ => ?_
  rw [hs1, clientState_capDoubleProg]
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s2 hs2 _ _ => ?_
  rw [hs2, clientState_selectEq0Prog]
  exact validHistory_decideTriggerProg w _ s

theorem realizesBounded_checkTrigger :
    RealizesBounded .exact checkTriggerProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w base s =>
        4 ≤ w ∧ base + 16 ≤ s.frontier ∧ Fits w (s.mem (base + hdrU1) + 1) ∧
        s.mem (base + hdrLive) ≤ s.mem (base + hdrU1) + 1 ∧
        s.mem (base + hdrNSrc) ≤ s.mem (base + hdrU1) + 1)
      (fun _ _ => 0) := by
  have hcd := realizesBounded_capDouble
  have hse := realizesBounded_selectEq0
  have hdt := realizesBounded_decideTrigger
  realize
  all_goals (
    obtain ⟨hw4, hfr, hu1_f, hnl, hns⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hfr_w := hmem.1
    repeat rw [clientState_capDoubleProg] at *
    repeat rw [clientResult_selectEq0Prog] at *
    have hrem_le : (if s.mem (d + hdrNSrc) % 4 = 0 then 0 else 1) ≤ 1 := by
      split_ifs <;> decide
    try simp only [hdrU1, hdrThresh, hdrLive, hdrNSrc, hdrEpochOps, Fits] at *
    omega)

attribute [local irreducible] checkTriggerProg

/-- Copy the 5 cached page-arena static words `[base + 43..48)` into `[base + 38..43)`. -/
def copyDstToSrcHostProg (base : ℕ) : Memory.Prog Unit := do
  let v0 ← Memory.read (base + hdrDstOd)
  let v1 ← Memory.read (base + hdrDstOt)
  let v2 ← Memory.read (base + hdrDstPb)
  let v3 ← Memory.read (base + hdrDstPg)
  let v4 ← Memory.read (base + hdrDstMp)
  Memory.write (base + hdrSrcOd) v0
  Memory.write (base + hdrSrcOt) v1
  Memory.write (base + hdrSrcPb) v2
  Memory.write (base + hdrSrcPg) v3
  Memory.write (base + hdrSrcMp) v4

theorem copyDstToSrcHostProg_spec (base : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (copyDstToSrcHostProg base)
    s'.frontier = s.frontier ∧
    memoryCost (copyDstToSrcHostProg base) s = 10 ∧
    s'.mem (base + hdrSrcOd) = s.mem (base + hdrDstOd) ∧
    s'.mem (base + hdrSrcOt) = s.mem (base + hdrDstOt) ∧
    s'.mem (base + hdrSrcPb) = s.mem (base + hdrDstPb) ∧
    s'.mem (base + hdrSrcPg) = s.mem (base + hdrDstPg) ∧
    s'.mem (base + hdrSrcMp) = s.mem (base + hdrDstMp) ∧
    (∀ addr, ¬(base + 38 ≤ addr ∧ addr < base + 43) → s'.mem addr = s.mem addr) := by
  dsimp only
  have hmc : memoryCost (copyDstToSrcHostProg base) s = 10 := by
    unfold copyDstToSrcHostProg
    iterate 5 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    iterate 4 rw [Realization.memoryCost_bind', mcost_wr]
    rw [mcost_wr]
  have hst : (Memory.spec 0).clientState s (copyDstToSrcHostProg base) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update s.mem (base + 38) (s.mem (base + 43)))
            (base + 39) (s.mem (base + 44)))
            (base + 40) (s.mem (base + 45)))
            (base + 41) (s.mem (base + 46)))
            (base + 42) (s.mem (base + 47)),
        frontier := s.frontier } := rfl
  rw [hst]; dsimp only
  unfold hdrSrcOd hdrSrcOt hdrSrcPb hdrSrcPg hdrSrcMp hdrDstOd hdrDstOt hdrDstPb hdrDstPg hdrDstMp
  refine ⟨rfl, hmc, ?_, ?_, ?_, ?_, ?_, fun addr ha => ?_⟩
  · iterate 4 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · iterate 3 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · iterate 2 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
  · exact Function.update_self _ _ _
  · iterate 5 rw [Function.update_of_ne (by omega)]

theorem validHistory_copyDstToSrcHostProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfr : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (copyDstToSrcHostProg base)) := by
  unfold copyDstToSrcHostProg hdrDstOd hdrDstOt hdrDstPb hdrDstPg hdrDstMp
    hdrSrcOd hdrSrcOt hdrSrcPb hdrSrcPg hdrSrcMp
  exact vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <|
    vh_wr (by omega) (hwf.2 _) <| vh_wr (by omega) (hwf.2 _) <|
    vh_wr (by omega) (hwf.2 _) <| vh_wr (by omega) (hwf.2 _) <|
    vh_wr_only (by omega) (hwf.2 _)

theorem realizesBounded_copyDstToSrcHost :
    RealizesBounded .exact copyDstToSrcHostProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun _ base s => base + 48 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    have hfr_w := hmem.1
    try simp only [hdrDstOd, hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrSrcOd, hdrSrcOt,
      hdrSrcPb, hdrSrcPg, hdrSrcMp, Fits] at *
    omega)

attribute [local irreducible] copyDstToSrcHostProg

/-- Configure `pBase` in direct (`usePaged = 0, sideBit = 0`) mode at `(ib, qb, nc)`. -/
def setDirectSlotIoProg : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((base, pBase), ((ib, qb), nc)) => do
    let wv ← Memory.read (base + hdrW)
    let vb ← Memory.read (base + hdrValBits)
    setSlotIoProg (pBase, ((0, 0), ((((base + hdrSplit, ib), (qb, 1)), ((wv, 32), (4, ib))),
      ((qb, vb), nc))))

theorem setDirectSlotIoProg_fr (x : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (setDirectSlotIoProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨base, pBase⟩, ⟨⟨ib, qb⟩, nc⟩⟩
  unfold setDirectSlotIoProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  exact runClient_frontier_setSlotIoProg _ _

theorem validHistory_setDirectSlotIoProg {w base pBase ib qb nc : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 192 ≤ s.frontier) (hp : pBase + 61 ≤ s.frontier)
    (hw6 : 6 ≤ w) (hib : Fits w ib) (hqb : Fits w qb) (hnc : Fits w nc) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (setDirectSlotIoProg ((base, pBase), ((ib, qb), nc)))) := by
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hfr_w : s.frontier < 2 ^ w := hwf.1
  unfold setDirectSlotIoProg hdrW hdrValBits
  refine vh_rd (by omega) <| vh_rd (by omega) ?_
  refine validHistory_setSlotIoProg
    (io := ⟨0, 0, ⟨base + hdrSplit, ib, qb, 1, s.mem (base + 2), 32, 4, ib, qb,
      s.mem (base + 4), nc⟩⟩) hp ?_
  unfold hdrSplit; dsimp only [Fits] at *
  exact ⟨by omega, by omega, by omega, hib, hqb, by omega, hwf.2 (base + 2), by omega, by omega,
    hib, hqb, hwf.2 (base + 4), hnc⟩

theorem realizesBounded_setDirectSlotIo :
    RealizesBounded .exact setDirectSlotIoProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, pBase), _) s => 6 ≤ w ∧ base + 192 ≤ s.frontier ∧ pBase + 61 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hsio := realizesBounded_setSlotIo
  realize
  all_goals (
    rcases d with ⟨⟨base, pBase⟩, ⟨⟨ib, qb⟩, nc⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw6, hb, hp⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    try simp only [hdrW, hdrValBits, hdrSplit, Fits] at *
    omega)

attribute [local irreducible] setDirectSlotIoProg

/-- Configure `pBase` in `SplitPair` (`usePaged = 0, sideBit = 1`) mode reading `(ibLo, qLo, ibHi,
qHi)` from `base`. -/
def setSplitSlotIoProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, pBase), nc) => do
    let wv ← Memory.read (base + hdrW)
    let vb ← Memory.read (base + hdrValBits)
    let ibLo ← Memory.read (base + hdrItemLo)
    let ibHi ← Memory.read (base + hdrItemHi)
    let qLo ← Memory.read (base + hdrQLo)
    let qHi ← Memory.read (base + hdrQHi)
    setSlotIoProg (pBase, ((0, 1), ((((base + hdrSplit, ibLo), (qHi, 1)), ((wv, 32), (4, ibHi))),
      ((qLo, vb), nc))))

theorem setSplitSlotIoProg_fr (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (setSplitSlotIoProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨base, pBase⟩, nc⟩
  unfold setSplitSlotIoProg
  iterate 6 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  exact runClient_frontier_setSlotIoProg _ _

theorem validHistory_setSplitSlotIoProg {w base pBase nc : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 192 ≤ s.frontier) (hp : pBase + 61 ≤ s.frontier)
    (hw6 : 6 ≤ w) (hnc : Fits w nc) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (setSplitSlotIoProg ((base, pBase), nc))) := by
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hfr_w : s.frontier < 2 ^ w := hwf.1
  unfold setSplitSlotIoProg hdrW hdrValBits hdrItemLo hdrItemHi hdrQLo hdrQHi
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  refine validHistory_setSlotIoProg
    (io := ⟨0, 1, ⟨base + hdrSplit, s.mem (base + 22), s.mem (base + 25), 1, s.mem (base + 2), 32,
      4, s.mem (base + 23), s.mem (base + 24), s.mem (base + 4), nc⟩⟩) hp ?_
  unfold hdrSplit; dsimp only [Fits] at *
  exact ⟨by omega, by omega, by omega, hwf.2 _, hwf.2 _, by omega, hwf.2 _, by omega, by omega,
    hwf.2 _, hwf.2 _, hwf.2 _, hnc⟩

theorem realizesBounded_setSplitSlotIo :
    RealizesBounded .exact setSplitSlotIoProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, pBase), _) s => 6 ≤ w ∧ base + 192 ≤ s.frontier ∧ pBase + 61 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hsio := realizesBounded_setSlotIo
  realize
  all_goals (
    rcases d with ⟨⟨base, pBase⟩, nc⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw6, hb, hp⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    try simp only [hdrW, hdrValBits, hdrItemLo, hdrItemHi, hdrQLo, hdrQHi, hdrSplit, Fits] at *
    omega)

attribute [local irreducible] setSplitSlotIoProg

/-- Load `SplitPairCtx` `(((ibLo, (qLo, vb)), (ibHi, (qHi, vb))), wv)` from `base`. -/
def loadSplitPairCtxProg (base : ℕ) : Memory.Prog SplitPairCtx := do
  let wv ← Memory.read (base + hdrW)
  let vb ← Memory.read (base + hdrValBits)
  let ibLo ← Memory.read (base + hdrItemLo)
  let ibHi ← Memory.read (base + hdrItemHi)
  let qLo ← Memory.read (base + hdrQLo)
  let qHi ← Memory.read (base + hdrQHi)
  pure (((ibLo, (qLo, vb)), (ibHi, (qHi, vb))), wv)

@[simp] theorem runClient_state_loadSplitPairCtxProg (base : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadSplitPairCtxProg base)) = s := by
  simp [loadSplitPairCtxProg]

@[simp] theorem clientState_loadSplitPairCtxProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadSplitPairCtxProg base) = s :=
  runClient_state_loadSplitPairCtxProg base s

theorem validHistory_loadSplitPairCtxProg {w base : ℕ} {s : Memory.State}
    (hb : base + 26 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadSplitPairCtxProg base)) := by
  unfold loadSplitPairCtxProg hdrW hdrValBits hdrItemLo hdrItemHi hdrQLo hdrQHi
  exact vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) trivial

theorem realizesBounded_loadSplitPairCtx :
    RealizesBounded .exact loadSplitPairCtxProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := SplitPairCtx))
      (fun _ base s => base + 26 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    have hfr_w := hmem.1
    try simp only [hdrW, hdrValBits, hdrItemLo, hdrItemHi, hdrQLo, hdrQHi, Fits] at *
    omega)

attribute [local irreducible] loadSplitPairCtxProg

/-- First half of `loadHostCtxProg`: loads `(wv, vb, nLive, mbHost, nHost, off0)` (`7` reads). -/
private def loadHostPartAProg (base : ℕ) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) := do
  let wv ← Memory.read (base + hdrW)
  let vb ← Memory.read (base + hdrValBits)
  let nLive ← Memory.read (base + hdrLive)
  let stg ← Memory.read (base + hdrStage)
  let nSrc ← Memory.read (base + hdrNSrc)
  let nDst ← Memory.read (base + hdrNDst)
  let pad ← Memory.read (base + hdrPad)
  let off0 ← selectEq0Prog (nDst, (hdrSrcOd, hdrDstOd))
  let mbStg ← selectEq0Prog (stg, (base + 192 + pad, base + 192))
  let mbHost ← selectEq0Prog (nDst, (base + 192, mbStg))
  let nHost ← selectEq0Prog (nDst, (nSrc, nDst))
  pure (((wv, vb), nLive), ((mbHost, nHost), off0))

@[simp] private theorem runClient_state_loadHostPartAProg (base : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadHostPartAProg base)) = s := by
  simp [loadHostPartAProg]

@[simp] private theorem clientState_loadHostPartAProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadHostPartAProg base) = s :=
  runClient_state_loadHostPartAProg base s

private theorem off0_loadHostPartAProg (base : ℕ) (s : Memory.State) :
    let (_, (_, off0)) := (Memory.spec 0).clientResult s (loadHostPartAProg base)
    off0 ≤ 43 := by
  change ((Memory.spec 0).clientResult s (loadHostPartAProg base)).2.2 ≤ 43
  unfold loadHostPartAProg
  simp only [prog_clientResult_bind, cres_rd, runClient_state_selectEq0Prog,
    clientResult_selectEq0Prog, StateTransitionSpec.clientResult,
    prog_clientResult_pure, hdrSrcOd, hdrDstOd]
  split_ifs <;> decide

private theorem validHistory_loadHostPartAProg {w base : ℕ} {s : Memory.State}
    (hb : base + 25 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (loadHostPartAProg base)) := by
  unfold loadHostPartAProg hdrW hdrValBits hdrLive hdrStage hdrNSrc hdrNDst hdrPad
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s1 hs1 _ _ => ?_
  rw [hs1, clientState_selectEq0Prog]
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s2 hs2 _ _ => ?_
  rw [hs2, clientState_selectEq0Prog]
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s3 hs3 _ _ => ?_
  rw [hs3, clientState_selectEq0Prog]
  exact vh_seq (validHistory_selectEq0Prog w _ s) fun _ _ _ _ => trivial

private theorem realizesBounded_loadHostPartA :
    RealizesBounded .exact loadHostPartAProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (fun w base s =>
        base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)))
      (fun _ _ => 0) := by
  have hse := realizesBounded_selectEq0
  realize
  all_goals (
    obtain ⟨hb, hpad⟩ := h
    have hfr_w := hmem.1
    try simp only [hdrW, hdrValBits, hdrLive, hdrStage, hdrNSrc, hdrNDst, hdrPad, hdrSrcOd,
      hdrDstOd, Fits] at *
    omega)

attribute [local irreducible] loadHostPartAProg

/-- Second half of `loadHostCtxProg`: loads `(ibHi, qHi, od..mp)` and assembles `PageArenaCtx`. -/
private def loadHostPartBProg :
    (ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) → Memory.Prog PageArenaCtx
  | ((base, metaOnly), (((wv, vb), nLive), ((mbHost, nHost), off0))) => do
    let ibHi ← Memory.read (base + hdrItemHi)
    let qHi ← Memory.read (base + hdrQHi)
    let od ← Memory.read (base + off0)
    let ot ← Memory.read (base + off0 + 1)
    let pb ← Memory.read (base + off0 + 2)
    let pg ← Memory.read (base + off0 + 3)
    let mp ← Memory.read (base + off0 + 4)
    let qv ← selectEq0PairProg (metaOnly, ((qHi, vb), (0, 0)))
    let nc ← selectEq0Prog (metaOnly, (nLive, nHost))
    pure ((((mbHost, od), (ot, pb)), ((wv, pg), (mp, ibHi))), (qv, nc))

@[simp] private theorem runClient_state_loadHostPartBProg
    (x : (ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ))) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadHostPartBProg x)) = s := by
  rcases x with ⟨⟨_, _⟩, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩
  simp [loadHostPartBProg]

@[simp] private theorem clientState_loadHostPartBProg
    (x : (ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadHostPartBProg x) = s :=
  runClient_state_loadHostPartBProg x s

private theorem validHistory_loadHostPartBProg {w base metaOnly : ℕ}
    {partA : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)} {s : Memory.State}
    (hb : base + 48 ≤ s.frontier) (hoff : let (_, (_, off0)) := partA; off0 ≤ 43) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadHostPartBProg ((base, metaOnly), partA))) := by
  rcases partA with ⟨⟨⟨wv, vb⟩, nLive⟩, ⟨⟨mbHost, nHost⟩, off0⟩⟩
  dsimp only at hoff
  unfold loadHostPartBProg hdrItemHi hdrQHi
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_seq (validHistory_selectEq0PairProg w _ s) fun s1 hs1 _ _ => ?_
  rw [hs1, clientState_selectEq0PairProg]
  exact vh_seq (validHistory_selectEq0Prog w _ s) fun _ _ _ _ => trivial

private theorem realizesBounded_loadHostPartB :
    RealizesBounded .exact loadHostPartBProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ))))
      (WordEncoding.encode (α := PageArenaCtx))
      (fun _ ((base, _), (_, (_, off0))) s => base + 48 ≤ s.frontier ∧ off0 ≤ 43)
      (fun _ _ => 0) := by
  have hsp := realizesBounded_selectEq0Pair
  have hse := realizesBounded_selectEq0
  realize
  all_goals (
    rcases d with ⟨⟨base, metaOnly⟩, ⟨⟨⟨wv, vb⟩, nLive⟩, ⟨⟨mbHost, nHost⟩, off0⟩⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hb, hoff⟩ := h
    have hfr_w := hmem.1
    try simp only [hdrItemHi, hdrQHi, Fits] at *
    omega)

attribute [local irreducible] loadHostPartBProg

/-- Load the active `pgHost` `PageArenaCtx` (`metaOnly = 1` sets `(qb, vb, nc) = (0, 0, N_host)` for
`initDir`/`initTail`; `metaOnly = 0` sets `(qb, vb, nc) = (qHi, vb, nLive)` for `migrate`/`unperm`).
-/
def loadHostCtxProg : ℕ × ℕ → Memory.Prog PageArenaCtx
  | (base, metaOnly) => do
    let partA ← loadHostPartAProg base
    loadHostPartBProg ((base, metaOnly), partA)

@[simp] theorem runClient_state_loadHostCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadHostCtxProg x)) = s := by
  rcases x with ⟨base, metaOnly⟩
  simp [loadHostCtxProg]

@[simp] theorem clientState_loadHostCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadHostCtxProg x) = s :=
  runClient_state_loadHostCtxProg x s

theorem validHistory_loadHostCtxProg {w base metaOnly : ℕ} {s : Memory.State}
    (hb : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadHostCtxProg (base, metaOnly))) := by
  unfold loadHostCtxProg
  refine vh_seq (validHistory_loadHostPartAProg (by omega)) fun s1 hs1 partA hpa => ?_
  rw [hs1, clientState_loadHostPartAProg]
  refine validHistory_loadHostPartBProg hb ?_
  rw [hpa]; exact off0_loadHostPartAProg base s

theorem realizesBounded_loadHostCtx :
    RealizesBounded .exact loadHostCtxProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := PageArenaCtx))
      (fun w (base, _) s =>
        base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)))
      (fun _ _ => 0) := by
  have ha := realizesBounded_loadHostPartA
  have hb := realizesBounded_loadHostPartB
  realize
  all_goals (
    rcases d with ⟨base, metaOnly⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hfr, hpad⟩ := h
    have hfr_w := hmem.1
    have hoff := off0_loadHostPartAProg base s
    repeat rw [clientState_loadHostPartAProg] at *
    rcases hp_eq : (Memory.spec 0).clientResult s (loadHostPartAProg base) with
      ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, off0⟩⟩
    rw [hp_eq] at hoff; dsimp only [Fits] at *
    omega)

attribute [local irreducible] loadHostCtxProg

/-! ## Section 3: `prepGrowProg` and Active User Operations (`query`, `insert`, `delete`) -/

/-- Overflow-free capped increment `if u1 < nLive then nLive else nLive + 1` (`0` queries). -/
private def incCapSafeProg : ℕ × ℕ → Memory.Prog ℕ
  | (u1, nLive) => if u1 < nLive then pure nLive else pure (nLive + 1)

@[simp] private theorem runClient_state_incCapSafeProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (incCapSafeProg x)) = s := by
  rcases x with ⟨u1, nL⟩; unfold incCapSafeProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_incCapSafeProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (incCapSafeProg x) = s :=
  runClient_state_incCapSafeProg x s

private theorem clientResult_incCapSafeProg_le (u1 nLive : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (incCapSafeProg (u1, nLive)) ≤ nLive + 1 := by
  unfold incCapSafeProg; dsimp only
  split_ifs <;> simp only [StateTransitionSpec.clientResult, prog_clientResult_pure] <;> omega

private theorem validHistory_incCapSafeProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (incCapSafeProg x)) := by
  rcases x with ⟨u1, nL⟩; unfold incCapSafeProg; dsimp only; split_ifs <;> exact trivial

private theorem realizesBounded_incCapSafe :
    RealizesBounded .exact incCapSafeProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (u1, _) _ => Fits w (u1 + 1)) (fun _ _ => 0) := by
  realize
  all_goals (rcases d with ⟨u1, nLive⟩; dsimp only [Fits] at *; omega)

/-- Update `pBase0 + 60` and `pBase1 + 60` to `nAlloc = min (nLive + 1) (u1 + 1)` when `opTag = 1`,
returning `nAlloc` (`nLive` when `opTag ≠ 1`). -/
private def prepGrowUpdateCapProg : ℕ × ℕ → Memory.Prog ℕ
  | (base, opTag) => do
    let u1 ← Memory.read (base + hdrU1)
    let nLive ← Memory.read (base + hdrLive)
    if opTag = 1 then do
      let nInc ← incCapSafeProg (u1, nLive)
      Memory.write (base + hdrPBase0 + 60) nInc
      Memory.write (base + hdrPBase1 + 60) nInc
      pure nInc
    else
      pure nLive

private theorem validHistory_prepGrowUpdateCapProg {w base opTag : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 192 ≤ s.frontier)
    (hu1 : Fits w (s.mem (base + hdrU1) + 1)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (prepGrowUpdateCapProg (base, opTag))) := by
  unfold prepGrowUpdateCapProg hdrU1 hdrLive hdrPBase0 hdrPBase1 at *
  refine vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_ite (opTag = 1) (fun _ => ?_) (fun _ => trivial)
  refine vh_seq (validHistory_incCapSafeProg w _ s) fun s1 hs1 nInc hnInc => ?_
  rw [hs1, clientState_incCapSafeProg]
  have hnl := hwf.2 (base + 10)
  have hfit : Fits w nInc := by
    rw [hnInc]; unfold incCapSafeProg; dsimp only [Fits] at hu1 hnl ⊢
    split_ifs <;> simp only [StateTransitionSpec.clientResult, prog_clientResult_pure] <;> omega
  rcases s with ⟨m, fr⟩; dsimp only at hb ⊢
  exact vh_wr (by omega) hfit <| vh_wr (by omega) hfit trivial

private theorem realizesBounded_prepGrowUpdateCap :
    RealizesBounded .exact prepGrowUpdateCapProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (base, _) s =>
        1 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (s.mem (base + hdrU1) + 1))
      (fun _ _ => 0) := by
  have hic := realizesBounded_incCapSafe
  realize
  all_goals (
    rcases d with ⟨base, opTag⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw1, hb, hu1⟩ := h
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hfr_w := hmem.1
    try simp only [hdrU1, hdrLive, hdrPBase0, hdrPBase1, Fits] at *
    omega)

private theorem prepGrowUpdateCap_frame {base opTag : ℕ} (s : Memory.State) :
    let s1 := (Memory.spec 0).clientState s (prepGrowUpdateCapProg (base, opTag))
    s1.frontier = s.frontier ∧
    (∀ off < 60, s1.mem (base + off) = s.mem (base + off)) ∧
    (Memory.spec 0).clientResult s (prepGrowUpdateCapProg (base, opTag)) ≤
      s.mem (base + hdrLive) + 1 := by
  dsimp only
  unfold prepGrowUpdateCapProg; dsimp only
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  by_cases hop : opTag = 1
  · rw [ite_eq_left hop,
      StateTransitionSpec.clientState_bind, clientState_incCapSafeProg,
      StateTransitionSpec.clientState_bind, cstate_wr,
      StateTransitionSpec.clientState_bind, cstate_wr]
    rw [prog_clientResult_bind, clientState_incCapSafeProg,
      prog_clientResult_bind, cstate_wr,
      prog_clientResult_bind, cstate_wr, prog_clientResult_pure]
    have hc_pure : ∀ (st : Memory.State) (v : ℕ),
        (Memory.spec 0).clientState st (pure v) = st := fun _ _ => rfl
    rw [hc_pure]
    unfold hdrPBase0 hdrPBase1
    refine ⟨rfl, fun off hoff => ?_, clientResult_incCapSafeProg_le _ _ s⟩
    change (Function.update (Function.update s.mem _ _) _ _) (base + off) = s.mem (base + off)
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [ite_eq_right hop]
    exact ⟨rfl, fun _ _ => rfl, Nat.le_succ _⟩

attribute [local irreducible] prepGrowUpdateCapProg

/-- Compute `k_grow ≤ bulkBatchWhp` from `(base, curFr, nAlloc)` using `pairStreamWordsSafeProg`. -/
private def prepGrowWordsProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, curFr), nAlloc) => do
    let wv ← Memory.read (base + hdrW)
    let vb ← Memory.read (base + hdrValBits)
    let ph ← Memory.read (base + hdrPhase)
    let ibLo ← Memory.read (base + hdrItemLo)
    let ibHi ← Memory.read (base + hdrItemHi)
    let qLo ← Memory.read (base + hdrQLo)
    let qHi ← Memory.read (base + hdrQHi)
    if ph < 2 then do
      let pw ← pairStreamWordsSafeProg (((nAlloc, qLo), vb), wv)
      clampSubProg (ibLo + pw, curFr)
    else if ph = 11 then do
      let pw ← pairStreamWordsSafeProg (((nAlloc, qLo), vb), wv)
      clampSubProg (ibLo + pw, curFr)
    else if ph = 2 then do
      let pw ← pairStreamWordsSafeProg (((nAlloc, qHi), vb), wv)
      let diff ← clampSubProg (ibHi + pw, curFr)
      min2Prog (diff, bulkBatchWhp)
    else do
      let pw ← pairStreamWordsSafeProg (((nAlloc, qHi), vb), wv)
      clampSubProg (ibHi + pw, curFr)

private theorem validHistory_prepGrowWordsProg {w base curFr nAlloc : ℕ} {s : Memory.State}
    (hb : base + 26 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (prepGrowWordsProg ((base, curFr), nAlloc))) := by
  unfold prepGrowWordsProg hdrW hdrValBits hdrPhase hdrItemLo hdrItemHi hdrQLo hdrQHi
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_ite _
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _)
      fun _ _ _ _ => validHistory_clampSubProg w _ _) fun _ => ?_
  refine vh_ite _
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _)
      fun _ _ _ _ => validHistory_clampSubProg w _ _) fun _ => ?_
  refine vh_ite _
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _) fun s1 hs1 _ _ => ?_)
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _)
      fun _ _ _ _ => validHistory_clampSubProg w _ _)
  rw [hs1, clientState_pairStreamWordsSafeProg]
  exact vh_seq (validHistory_clampSubProg w _ _) fun _ _ _ _ => validHistory_min2Prog w _ _

private theorem realizesBounded_prepGrowWords :
    RealizesBounded .exact prepGrowWordsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((base, _), nAlloc) s =>
        11 ≤ w ∧ s.mem (base + hdrW) = w ∧ base + 26 ≤ s.frontier ∧
        s.mem (base + hdrValBits) ≤ w ∧ s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
        Fits w (s.mem (base + hdrItemLo) +
          pairStreamWords nAlloc (s.mem (base + hdrQLo)) (s.mem (base + hdrValBits)) w) ∧
        Fits w (s.mem (base + hdrItemHi) +
          pairStreamWords nAlloc (s.mem (base + hdrQHi)) (s.mem (base + hdrValBits)) w))
      (fun _ _ => 0) := by
  have hps := realizesBounded_pairStreamWordsSafe
  have hcs := realizesBounded_clampSub
  have hmn := realizesBounded_min2
  realize
  all_goals (
    rcases d with ⟨⟨base, curFr⟩, nAlloc⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw11, hwv, hb, hvb, hqL, hqH, hfL, hfH⟩ := h
    have hw_pos : 0 < w := by omega
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    subst hwv
    repeat rw [pairStreamWordsSafeProg_res hw_pos] at *
    try simp only [hdrW, hdrValBits, hdrPhase, hdrItemLo, hdrItemHi, hdrQLo, hdrQHi,
      bulkBatchWhp, Fits] at *
    try omega)

attribute [local irreducible] prepGrowWordsProg

/-- Compute pre-operation frontier growth `k_grow ≤ bulkBatchWhp` (`0` on `query`) and set
`pBase0 + 60` / `pBase1 + 60` to `nAlloc` before `insert`. -/
def prepGrowProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((base, curFr), opTag), _u) =>
    if opTag = 0 then
      pure 0
    else do
      let nAlloc ← prepGrowUpdateCapProg (base, opTag)
      prepGrowWordsProg ((base, curFr), nAlloc)

/-- Precondition for `prepGrowProg`. -/
@[expose] def PrepGrowPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((base, _curFr), opTag), _u), s =>
    opTag = 0 ∨
    (11 ≤ w ∧ s.mem (base + hdrW) = w ∧ base + 192 ≤ s.frontier ∧
      s.mem (base + hdrValBits) ≤ w ∧ s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
      Fits w (s.mem (base + hdrU1) + 1) ∧
      Fits w (s.mem (base + hdrItemLo) +
        pairStreamWords (s.mem (base + hdrLive) + 1) (s.mem (base + hdrQLo))
          (s.mem (base + hdrValBits)) w) ∧
      Fits w (s.mem (base + hdrItemHi) +
        pairStreamWords (s.mem (base + hdrLive) + 1) (s.mem (base + hdrQHi))
          (s.mem (base + hdrValBits)) w))

theorem validHistory_prepGrowProg {w : ℕ} {x : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : PrepGrowPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (prepGrowProg x)) := by
  rcases x with ⟨⟨⟨base, curFr⟩, opTag⟩, u⟩
  unfold prepGrowProg; dsimp only
  refine vh_ite (opTag = 0) (fun _ => trivial) fun hne => ?_
  rcases hpre with h0 | ⟨_, _, hb, _, _, _, hu1, _, _⟩
  · exact absurd h0 hne
  refine vh_seq (validHistory_prepGrowUpdateCapProg hwf hb hu1) fun s1 hs1 _ _ => ?_
  have hfr1 := (prepGrowUpdateCap_frame (base := base) (opTag := opTag) s).1
  rw [hs1]; exact validHistory_prepGrowWordsProg (by rw [hfr1]; omega)

theorem realizesBounded_prepGrow :
    RealizesBounded .exact prepGrowProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PrepGrowPre
      (fun _ _ => 0) := by
  have hu := realizesBounded_prepGrowUpdateCap
  have hw_p := realizesBounded_prepGrowWords
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, curFr⟩, opTag⟩, u⟩
    dsimp only [Prod.fst, Prod.snd] at *
    rcases h with h0 | ⟨hw11, hwv, hb, hvb, hqL, hqH, hu1, hfL, hfH⟩
    · exfalso; exact ‹¬opTag = 0› h0
    obtain ⟨hfr1, hmem1, hres_le⟩ :=
      prepGrowUpdateCap_frame (base := base) (opTag := opTag) s
    have hmono : ∀ n1 n2 qb, n1 ≤ n2 →
        pairStreamWords n1 qb (s.mem (base + hdrValBits)) w ≤
          pairStreamWords n2 qb (s.mem (base + hdrValBits)) w := fun n1 n2 qb hle => by
      unfold pairStreamWords packedWords
      have hm := Nat.mul_le_mul_right (qb + s.mem (base + hdrValBits)) hle
      have hd := Nat.div_le_div_right (c := w)
        (show n1 * (qb + s.mem (base + hdrValBits)) + w - 1 ≤
          n2 * (qb + s.mem (base + hdrValBits)) + w - 1 by omega)
      omega
    have hmL := hmono _ _ (s.mem (base + hdrQLo)) hres_le
    have hmH := hmono _ _ (s.mem (base + hdrQHi)) hres_le
    try rw [hfr1]
    try rw [hmem1 hdrW (by decide)]
    try rw [hmem1 hdrValBits (by decide)]
    try rw [hmem1 hdrItemLo (by decide)]
    try rw [hmem1 hdrItemHi (by decide)]
    try rw [hmem1 hdrQLo (by decide)]
    try rw [hmem1 hdrQHi (by decide)]
    dsimp only [Fits] at hu1 hfL hfH ⊢
    omega)

/-- Read-only user `query u` across all 12 phases (`0` writes, `0` background ticks). -/
def userQueryProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (base, u_val) => do
    let ph ← Memory.read (base + hdrPhase)
    let stg ← Memory.read (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc ← selectEq0Prog (stg, (p0, p1))
    let pDst ← selectEq0Prog (stg, (p1, p0))
    if ph = 8 then do
      let rDst ← epochQueryProg (pDst, u_val)
      if rDst.1 = 0 then epochQueryProg (pSrc, u_val) else pure rDst
    else if ph = 9 then
      epochQueryProg (pDst, u_val)
    else if 3 < ph then
      if ph < 8 then epochQueryProg (pSrc, u_val) else epochQueryProg (p0, u_val)
    else
      epochQueryProg (p0, u_val)

/-- Precondition for `userQueryProg`. -/
@[expose] def UserQueryPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (base, u_val), s =>
    base + 192 ≤ s.frontier ∧
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc := if stg = 0 then p0 else p1
    let pDst := if stg = 0 then p1 else p0
    if ph = 8 then
      EpochProgPre w pDst s ∧
      EpochProgPre w pSrc ((Memory.spec 0).clientState s (epochQueryProg (pDst, u_val)))
    else if ph = 9 then EpochProgPre w pDst s
    else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
    else EpochProgPre w p0 s

theorem validHistory_userQueryProg {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (hpre : UserQueryPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (userQueryProg x)) := by
  rcases x with ⟨base, u_val⟩
  obtain ⟨hb, hdisp⟩ := hpre
  dsimp only at hdisp
  unfold userQueryProg
  unfold hdrPhase hdrStage at hdisp ⊢
  refine vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s1 hs1 pSrc hpSrc => ?_
  rw [hs1, clientState_selectEq0Prog, hpSrc, clientResult_selectEq0Prog]
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun s2 hs2 pDst hpDst => ?_
  rw [hs2, clientState_selectEq0Prog, hpDst, clientResult_selectEq0Prog]
  by_cases h8 : s.mem (base + 11) = 8
  · rw [ite_eq_left h8] at hdisp ⊢
    refine vh_seq (validHistory_epochQueryProg hdisp.1) fun s3 hs3 rDst _ => ?_
    rw [hs3]
    exact vh_ite (rDst.1 = 0) (fun _ => validHistory_epochQueryProg hdisp.2) fun _ => trivial
  · rw [ite_eq_right h8] at hdisp ⊢
    by_cases h9 : s.mem (base + 11) = 9
    · rw [ite_eq_left h9] at hdisp ⊢; exact validHistory_epochQueryProg hdisp
    · rw [ite_eq_right h9] at hdisp ⊢
      by_cases h3 : 3 < s.mem (base + 11)
      · rw [ite_eq_left h3]
        by_cases hlt8 : s.mem (base + 11) < 8
        · rw [ite_eq_left hlt8]
          rw [ite_eq_left (show 4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7 by omega)] at hdisp
          exact validHistory_epochQueryProg hdisp
        · rw [ite_eq_right hlt8]
          rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7)
            by omega)] at hdisp
          exact validHistory_epochQueryProg hdisp
      · rw [ite_eq_right h3]
        rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7) by omega)] at hdisp
        exact validHistory_epochQueryProg hdisp

theorem realizesBounded_userQuery :
    RealizesBounded .exact userQueryProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      UserQueryPre (fun _ _ => 0) := by
  have hse := realizesBounded_selectEq0
  have hq := realizesBounded_epochQuery
  realize
  all_goals (
    rcases d with ⟨base, u_val⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hb, hdisp⟩ := h
    dsimp (config := { proj := false, iota := false }) only [Prod.fst, Prod.snd] at hdisp
    have hfr_w := hmem.1
    repeat rw [clientState_selectEq0Prog] at *
    repeat rw [clientResult_selectEq0Prog] at *
    unfold hdrPhase hdrStage hdrPBase0 hdrPBase1 at *
    dsimp only [Fits] at *
    by_cases h8 : s.mem (base + 11) = 8
    · rw [ite_eq_left h8] at hdisp
      first | exact hdisp.1 | exact hdisp.2 | omega
    · rw [ite_eq_right h8] at hdisp
      by_cases h9 : s.mem (base + 11) = 9
      · rw [ite_eq_left h9] at hdisp; first | exact hdisp | omega
      · rw [ite_eq_right h9] at hdisp
        by_cases h47 : 4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7
        · rw [ite_eq_left h47] at hdisp; first | exact hdisp | omega
        · rw [ite_eq_right h47] at hdisp; first | exact hdisp | omega)

attribute [local irreducible] userQueryProg

/-- Optional clamp of `hdrSplit` to `nLive'` during `slideUp`/`slideDown` (`ph = 3` or `ph = 10`).
-/
private def clampSplitIfSlideProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, ph), nLive') =>
    if ph = 3 then do
      let sp ← Memory.read (base + hdrSplit)
      if nLive' < sp then Memory.write (base + hdrSplit) nLive' else pure ()
    else if ph = 10 then do
      let sp ← Memory.read (base + hdrSplit)
      if nLive' < sp then Memory.write (base + hdrSplit) nLive' else pure ()
    else
      pure ()

private theorem validHistory_clampSplitIfSlideProg {w base ph nLive' : ℕ} {s : Memory.State}
    (hb : base + 20 ≤ s.frontier) (hf : Fits w nLive') :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (clampSplitIfSlideProg ((base, ph), nLive'))) := by
  unfold clampSplitIfSlideProg hdrSplit
  refine vh_ite (ph = 3) (fun _ => ?_) fun _ => vh_ite (ph = 10) (fun _ => ?_) fun _ => trivial
  · refine vh_rd (by omega) ?_; rcases s with ⟨_, _⟩
    exact vh_ite _ (fun _ => vh_wr_only (by dsimp only at hb ⊢; omega) hf) fun _ => trivial
  · refine vh_rd (by omega) ?_; rcases s with ⟨_, _⟩
    exact vh_ite _ (fun _ => vh_wr_only (by dsimp only at hb ⊢; omega) hf) fun _ => trivial

private theorem realizesBounded_clampSplitIfSlide :
    RealizesBounded .exact clampSplitIfSlideProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun _ ((base, _), _) s => base + 20 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, ph⟩, nLive'⟩
    dsimp only [Prod.fst, Prod.snd] at *
    have hfr_w := hmem.1
    try simp only [hdrSplit, Fits] at *; omega)

attribute [local irreducible] clampSplitIfSlideProg

/-- Reads the current live item count across active epoch slots (`0` writes). -/
private def readLiveCountProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((ph, p0), (pSrc, pDst)) =>
    if ph = 8 then do
      let nS ← epochReadNSideProg pSrc
      let nD ← epochReadNSideProg pDst
      max2Prog (nS + nD, nS + nD)
    else if ph = 9 then
      epochReadNSideProg pDst
    else if 3 < ph then
      if ph < 8 then epochReadNSideProg pSrc else epochReadNSideProg p0
    else
      epochReadNSideProg p0

@[simp] private theorem runClient_state_readLiveCountProg
    (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (readLiveCountProg x)) = s := by
  rcases x with ⟨⟨ph, p0⟩, ⟨pSrc, pDst⟩⟩
  unfold readLiveCountProg; dsimp only
  split_ifs <;> simp

@[simp] private theorem clientState_readLiveCountProg (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readLiveCountProg x) = s :=
  runClient_state_readLiveCountProg x s

private theorem validHistory_readLiveCountProg {w ph p0 pSrc pDst : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hdisp :
      if ph = 8 then
        EpochProgPre w pSrc s ∧ EpochProgPre w pDst s ∧
        Fits w ((Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
          (Memory.spec 0).clientResult s (epochReadNSideProg pDst))
      else if ph = 9 then EpochProgPre w pDst s
      else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
      else EpochProgPre w p0 s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readLiveCountProg ((ph, p0), (pSrc, pDst)))) ∧
    Fits w ((Memory.spec 0).clientResult s (readLiveCountProg ((ph, p0), (pSrc, pDst)))) := by
  have hfit_nS : ∀ pB, Fits w ((Memory.spec 0).clientResult s (epochReadNSideProg pB)) :=
    fun pB => epochReadNSideProg_fits hwf
  unfold readLiveCountProg; dsimp only
  by_cases h8 : ph = 8
  · rw [ite_eq_left h8] at hdisp ⊢
    refine ⟨vh_seq (validHistory_epochReadNSideProg hdisp.1) fun s1 hs1 _ _ => ?_, ?_⟩
    · rw [hs1, clientState_epochReadNSideProg]
      exact vh_seq (validHistory_epochReadNSideProg hdisp.2.1)
        fun _ _ _ _ => validHistory_max2Prog w _ _
    · rw [prog_clientResult_bind, clientState_epochReadNSideProg, prog_clientResult_bind,
        clientState_epochReadNSideProg, clientResult_max2Prog, Nat.max_self]
      exact hdisp.2.2
  · rw [ite_eq_right h8] at hdisp ⊢
    by_cases h9 : ph = 9
    · rw [ite_eq_left h9] at hdisp ⊢
      exact ⟨validHistory_epochReadNSideProg hdisp, hfit_nS _⟩
    · rw [ite_eq_right h9] at hdisp ⊢
      by_cases h3 : 3 < ph
      · rw [ite_eq_left h3]
        by_cases hlt8 : ph < 8
        · rw [ite_eq_left hlt8]
          rw [ite_eq_left (show 4 ≤ ph ∧ ph ≤ 7 by omega)] at hdisp
          exact ⟨validHistory_epochReadNSideProg hdisp, hfit_nS _⟩
        · rw [ite_eq_right hlt8]
          rw [ite_eq_right (show ¬(4 ≤ ph ∧ ph ≤ 7) by omega)] at hdisp
          exact ⟨validHistory_epochReadNSideProg hdisp, hfit_nS _⟩
      · rw [ite_eq_right h3]
        rw [ite_eq_right (show ¬(4 ≤ ph ∧ ph ≤ 7) by omega)] at hdisp
        exact ⟨validHistory_epochReadNSideProg hdisp, hfit_nS _⟩

private theorem realizesBounded_readLiveCount :
    RealizesBounded .exact readLiveCountProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ph, p0), (pSrc, pDst)) s =>
        4 ≤ w ∧
        if ph = 8 then
          EpochProgPre w pSrc s ∧ EpochProgPre w pDst s ∧
          Fits w ((Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
            (Memory.spec 0).clientResult s (epochReadNSideProg pDst))
        else if ph = 9 then EpochProgPre w pDst s
        else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
        else EpochProgPre w p0 s)
      (fun _ _ => 0) := by
  have hrn := realizesBounded_epochReadNSide
  have hmx := realizesBounded_max2
  realize
  all_goals (
    rcases d with ⟨⟨ph, p0⟩, ⟨pSrc, pDst⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw4, hdisp⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    repeat rw [clientState_epochReadNSideProg] at *
    dsimp only [Fits] at *
    try split_ifs at hdisp)
  all_goals (first | exact hdisp | exact hdisp.1 | exact hdisp.2.1 | exact hdisp.2.2 | omega)

attribute [local irreducible] readLiveCountProg

/-- Refresh `hdrLive`, `pBase0 + 60`, `pBase1 + 60`, and clamp `hdrSplit` after a mutation. -/
def syncLiveCountsProg (base : ℕ) : Memory.Prog ℕ := do
  let ph ← Memory.read (base + hdrPhase)
  let stg ← Memory.read (base + hdrStage)
  let p0 := base + hdrPBase0
  let p1 := base + hdrPBase1
  let slots ← slotPairProg (stg, base)
  let nLive' ← readLiveCountProg ((ph, p0), slots)
  Memory.write (base + hdrLive) nLive'
  Memory.write (p0 + 60) nLive'
  Memory.write (p1 + 60) nLive'
  clampSplitIfSlideProg ((base, ph), nLive')
  pure nLive'

/-- Precondition for `syncLiveCountsProg`. -/
@[expose] def SyncLivePre (w : ℕ) (base : ℕ) (s : Memory.State) : Prop :=
  base + 192 ≤ s.frontier ∧
  let ph := s.mem (base + hdrPhase)
  let stg := s.mem (base + hdrStage)
  let p0 := base + hdrPBase0
  let p1 := base + hdrPBase1
  let pSrc := if stg = 0 then p0 else p1
  let pDst := if stg = 0 then p1 else p0
  if ph = 8 then
    EpochProgPre w pSrc s ∧ EpochProgPre w pDst s ∧
    Fits w ((Memory.spec 0).clientResult s (epochReadNSideProg pSrc) +
      (Memory.spec 0).clientResult s (epochReadNSideProg pDst))
  else if ph = 9 then EpochProgPre w pDst s
  else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
  else EpochProgPre w p0 s

theorem validHistory_syncLiveCountsProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : SyncLivePre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (syncLiveCountsProg base)) := by
  obtain ⟨hb, hdisp⟩ := hpre
  dsimp only at hdisp
  unfold syncLiveCountsProg
  refine vh_rd (by unfold hdrPhase; omega) <| vh_rd (by unfold hdrStage; omega) ?_
  refine vh_seq (validHistory_slotPairProg w _ s) fun sa hsa slots hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  obtain ⟨vhr, hfit⟩ := validHistory_readLiveCountProg hwf hdisp
  refine vh_seq vhr fun s1 hs1 nLive' hnL => ?_
  rw [hs1, clientState_readLiveCountProg]
  rw [← hnL] at hfit
  rcases s with ⟨m, fr⟩; dsimp only at hb ⊢
  unfold hdrLive hdrPBase0 hdrPBase1
  refine vh_wr (by omega) hfit <| vh_wr (by omega) hfit <| vh_wr (by omega) hfit ?_
  exact vh_seq (validHistory_clampSplitIfSlideProg (by dsimp only; omega) hfit)
    fun _ _ _ _ => trivial

theorem realizesBounded_syncLiveCounts :
    RealizesBounded .exact syncLiveCountsProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      SyncLivePre (fun _ _ => 0) := by
  have hsl := realizesBounded_slotPair
  have hrl := realizesBounded_readLiveCount
  have hcs := realizesBounded_clampSplitIfSlide
  realize
  all_goals (
    obtain ⟨hb, hdisp⟩ := h
    dsimp (config := { proj := false, iota := false }) only [Prod.fst, Prod.snd] at hdisp
    have hw4 := four_le_of_frontier16 hmem (by omega)
    have hfr_w := hmem.1
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [clientState_readLiveCountProg] at *
    unfold hdrPhase hdrStage hdrPBase0 hdrPBase1 at *
    try unfold hdrLive at *
    dsimp only [Fits] at *
    by_cases h8 : s.mem (d + 11) = 8
    · rw [ite_eq_left h8] at hdisp
      first | exact hdisp.1 | exact hdisp.2.1 | exact hdisp.2.2 | omega
    · rw [ite_eq_right h8] at hdisp
      by_cases h9 : s.mem (d + 11) = 9
      · rw [ite_eq_left h9] at hdisp; first | exact hdisp | omega
      · rw [ite_eq_right h9] at hdisp
        by_cases h47 : 4 ≤ s.mem (d + 11) ∧ s.mem (d + 11) ≤ 7
        · rw [ite_eq_left h47] at hdisp; first | exact hdisp | omega
        · rw [ite_eq_right h47] at hdisp; first | exact hdisp | omega)

attribute [local irreducible] syncLiveCountsProg

/-- Raw user mutation (`insert` when `opTag = 1`, `delete` when `opTag ≠ 1`) before syncing live
counts. -/
def userMutateRawProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((base, opTag), (u_val, v_val)) => do
    let ph ← Memory.read (base + hdrPhase)
    let stg ← Memory.read (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc ← selectEq0Prog (stg, (p0, p1))
    let pDst ← selectEq0Prog (stg, (p1, p0))
    if opTag = 1 then
      if ph = 8 then do
        epochDeleteProg (pSrc, u_val)
        epochInsertProg ((pDst, u_val), v_val)
      else if ph = 9 then
        epochInsertProg ((pDst, u_val), v_val)
      else if 3 < ph then
        if ph < 8 then epochInsertProg ((pSrc, u_val), v_val)
        else epochInsertProg ((p0, u_val), v_val)
      else
        epochInsertProg ((p0, u_val), v_val)
    else
      if ph = 8 then do
        epochDeleteProg (pSrc, u_val)
        epochDeleteProg (pDst, u_val)
      else if ph = 9 then
        epochDeleteProg (pDst, u_val)
      else if 3 < ph then
        if ph < 8 then epochDeleteProg (pSrc, u_val)
        else epochDeleteProg (p0, u_val)
      else
        epochDeleteProg (p0, u_val)

/-- Precondition for `userMutateRawProg`. -/
@[expose] def UserMutateRawPre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((base, opTag), (u_val, _)), s =>
    base + 192 ≤ s.frontier ∧
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let p0 := base + hdrPBase0
    let p1 := base + hdrPBase1
    let pSrc := if stg = 0 then p0 else p1
    let pDst := if stg = 0 then p1 else p0
    if opTag = 1 then
      if ph = 8 then
        EpochProgPre w pSrc s ∧
        EpochInsertProgPre w pDst ((Memory.spec 0).clientState s (epochDeleteProg (pSrc, u_val)))
      else if ph = 9 then EpochInsertProgPre w pDst s
      else if 4 ≤ ph ∧ ph ≤ 7 then EpochInsertProgPre w pSrc s
      else EpochInsertProgPre w p0 s
    else
      if ph = 8 then
        EpochProgPre w pSrc s ∧
        EpochProgPre w pDst ((Memory.spec 0).clientState s (epochDeleteProg (pSrc, u_val)))
      else if ph = 9 then EpochProgPre w pDst s
      else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
      else EpochProgPre w p0 s

theorem validHistory_userMutateRawProg {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : UserMutateRawPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (userMutateRawProg x)) := by
  rcases x with ⟨⟨base, opTag⟩, ⟨u_val, v_val⟩⟩
  obtain ⟨hb, hdisp⟩ := hpre
  dsimp only at hdisp
  unfold userMutateRawProg
  unfold hdrPhase hdrStage at hdisp ⊢
  refine vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun sa hsa pSrc hpSrc => ?_
  rw [hsa, clientState_selectEq0Prog, hpSrc, clientResult_selectEq0Prog]
  refine vh_seq (validHistory_selectEq0Prog w _ s) fun sb hsb pDst hpDst => ?_
  rw [hsb, clientState_selectEq0Prog, hpDst, clientResult_selectEq0Prog]
  by_cases hop : opTag = 1
  · rw [ite_eq_left hop] at hdisp ⊢
    by_cases h8 : s.mem (base + 11) = 8
    · rw [ite_eq_left h8] at hdisp ⊢
      have hd := validHistory_epochDeleteProg (u_val := u_val) hwf hdisp.1
      exact vh_seq hd fun s1 hs1 _ _ => by
        rw [hs1]; exact validHistory_epochInsertProg (wf_step hwf hd) hdisp.2
    · rw [ite_eq_right h8] at hdisp ⊢
      by_cases h9 : s.mem (base + 11) = 9
      · rw [ite_eq_left h9] at hdisp ⊢; exact validHistory_epochInsertProg hwf hdisp
      · rw [ite_eq_right h9] at hdisp ⊢
        by_cases h3 : 3 < s.mem (base + 11)
        · rw [ite_eq_left h3]
          by_cases hlt8 : s.mem (base + 11) < 8
          · rw [ite_eq_left hlt8]
            rw [ite_eq_left (show 4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7 by omega)] at hdisp
            exact validHistory_epochInsertProg hwf hdisp
          · rw [ite_eq_right hlt8]
            rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7)
              by omega)] at hdisp
            exact validHistory_epochInsertProg hwf hdisp
        · rw [ite_eq_right h3]
          rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7)
            by omega)] at hdisp
          exact validHistory_epochInsertProg hwf hdisp
  · rw [ite_eq_right hop] at hdisp ⊢
    by_cases h8 : s.mem (base + 11) = 8
    · rw [ite_eq_left h8] at hdisp ⊢
      have hd := validHistory_epochDeleteProg (u_val := u_val) hwf hdisp.1
      exact vh_seq hd fun s1 hs1 _ _ => by
        rw [hs1]; exact validHistory_epochDeleteProg (wf_step hwf hd) hdisp.2
    · rw [ite_eq_right h8] at hdisp ⊢
      by_cases h9 : s.mem (base + 11) = 9
      · rw [ite_eq_left h9] at hdisp ⊢; exact validHistory_epochDeleteProg hwf hdisp
      · rw [ite_eq_right h9] at hdisp ⊢
        by_cases h3 : 3 < s.mem (base + 11)
        · rw [ite_eq_left h3]
          by_cases hlt8 : s.mem (base + 11) < 8
          · rw [ite_eq_left hlt8]
            rw [ite_eq_left (show 4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7 by omega)] at hdisp
            exact validHistory_epochDeleteProg hwf hdisp
          · rw [ite_eq_right hlt8]
            rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7)
              by omega)] at hdisp
            exact validHistory_epochDeleteProg hwf hdisp
        · rw [ite_eq_right h3]
          rw [ite_eq_right (show ¬(4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7)
            by omega)] at hdisp
          exact validHistory_epochDeleteProg hwf hdisp

theorem realizesBounded_userMutateRaw :
    RealizesBounded .exact userMutateRawProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      UserMutateRawPre (fun _ _ => 0) := by
  have hse := realizesBounded_selectEq0
  have hin := realizesBounded_epochInsert
  have hdl := realizesBounded_epochDelete
  realize
  all_goals (
    rcases d with ⟨⟨base, opTag⟩, ⟨u_val, v_val⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hb, hdisp⟩ := h
    dsimp (config := { proj := false, iota := false }) only [Prod.fst, Prod.snd] at hdisp
    have hfr_w := hmem.1
    repeat rw [clientState_selectEq0Prog] at *
    repeat rw [clientResult_selectEq0Prog] at *
    unfold hdrPhase hdrStage hdrPBase0 hdrPBase1 at *
    dsimp only [Fits] at *
    by_cases hop : opTag = 1 <;>
      [rw [ite_eq_left hop] at hdisp; rw [ite_eq_right hop] at hdisp] <;>
      (by_cases h8 : s.mem (base + 11) = 8
       · rw [ite_eq_left h8] at hdisp
         first | exact hdisp.1 | exact hdisp.2 | omega
       · rw [ite_eq_right h8] at hdisp
         by_cases h9 : s.mem (base + 11) = 9
         · rw [ite_eq_left h9] at hdisp; first | exact hdisp | omega
         · rw [ite_eq_right h9] at hdisp
           by_cases h47 : 4 ≤ s.mem (base + 11) ∧ s.mem (base + 11) ≤ 7
           · rw [ite_eq_left h47] at hdisp; first | exact hdisp | omega
           · rw [ite_eq_right h47] at hdisp; first | exact hdisp | omega))

attribute [local irreducible] userMutateRawProg

/-- Combined user mutation (`insert` or `delete`) followed by `syncLiveCountsProg`. -/
def userMutateProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((base, opTag), (u_val, v_val)) => do
    userMutateRawProg ((base, opTag), (u_val, v_val))
    syncLiveCountsProg base

/-- Precondition for `userMutateProg`. -/
@[expose] def UserMutatePre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((base, opTag), (u_val, v_val)), s =>
    UserMutateRawPre w ((base, opTag), (u_val, v_val)) s ∧
    SyncLivePre w base ((Memory.spec 0).clientState s
      (userMutateRawProg ((base, opTag), (u_val, v_val))))

theorem validHistory_userMutateProg {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : UserMutatePre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (userMutateProg x)) := by
  rcases x with ⟨⟨base, opTag⟩, ⟨u_val, v_val⟩⟩
  have vh1 := validHistory_userMutateRawProg hwf hpre.1
  exact vh_seq vh1 fun s1 hs1 _ _ => by
    rw [hs1]; exact validHistory_syncLiveCountsProg (wf_step hwf vh1) hpre.2

theorem realizesBounded_userMutate :
    RealizesBounded .exact userMutateProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      UserMutatePre (fun _ _ => 0) := by
  have hm := realizesBounded_userMutateRaw
  have hs := realizesBounded_syncLiveCounts
  realize
  · rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩; exact h.1
  · rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩; exact h.2

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
