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
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.PromoteRead
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.PromoteStepEffect
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.PromoteStepRealize
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted `K`-Step Slab Promotion (`compPromoteSlabGenProg`)

Assembles the `K`-iteration loop (`RealizesBounded.iterate₀`) and `compGmPushSlabGenProg` into
`compPromoteSlabGenProg` coupled to `promoteSlabProg`.
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

/-- Promote `K = slabSize N` tail items of bucket `b` into a newly allocated full slab. -/
private def compPromoteSlabGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    let k0 ← pure 0
    let K ← pure (cpSlabSize cp)
    let _ ← compPromoteLoopGenProg ((((cp, (metaBase, itemBase)), b), k0), K)
    compGmPushSlabGenProg ((cp, metaBase), b)

/-- Precondition for `compPromoteSlabGenProg`. -/
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
  have hwg : 0 < ghostW w := by
    unfold ghostW
    omega
  have hloop0 := promoteLoopInv_zero hpre
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + 0)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + 0) + compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    simpa only [FixedCoupled, epochTotalSlots, hb0, ↓reduceIte, Nat.add_zero] using hcpl
  have hm_cap0 : (compGmAt metaBase U w N s.mem 0 * slabSize N + 0) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    simpa only [totalSlots, hb0, ↓reduceIte, Nat.add_zero] using hm_cap
  obtain ⟨hfr_loop, hcpl_loop, hcost_loop, _⟩ :=
    iterate_compPromoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_promoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add] at hcpl_loop hloopK
  set s₁ := (Memory.spec 0).clientState s (iterate compPromoteStepGenProg d (slabSize N) 0)
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
      (0, b) (slabSize N) 0)
  have htot1 : (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem 0 + 1) *
      slabSize N ≤ N := by
    simpa only [Nat.add_one_mul] using Nat.le_of_add_right_le hloopK.tot_le
  have hp_lt1 := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  have hslab1 : SlabBijection N (compGmAt metaBase U w N s₁.mem)
      (fun b' => compGmAt metaBase U w N s₁.mem (gmQIdx b'))
      (compGmAt metaBase U w N s₁.mem 0) :=
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij
  obtain ⟨hfr_push, hgm_push⟩ := compGmPushSlabGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N)
    (m_items := (compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N) +
      compGmAt metaBase U w N s₁.mem 1) (b := b)
    henv.pos_w henv.meta_le_item hb_pos hloopK.b_lt s₁ hslab1 (hcpl_loop.gm_eq ▸ hp_lt1)
  obtain ⟨_, _, hq_fpush, hv_fpush, hl_fpush, hgm_fpush⟩ :=
    gmPushSlabProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hloopK.b_lt s_fix₁
      hloopK.slab_bij hp_lt1
  set s₂ := (Memory.spec 0).clientState s₁
    (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))
  have hs'_eq : s' = s₂ := by
    simp [s', d, compPromoteSlabGenProg, compPromoteLoopGenProg, cpSlabSize_mk, s₁, s₂]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
      (gmPushSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
    simp [s_fix', promoteSlabProg, promoteSlabGenProg, p_slabSize_mk,
      gmPushSlabGenProg_mk, promoteLoopGenProg, s_fix₁]
  have hf_fields := gmPushSlab_fields (compGmAt metaBase U w N s₁.mem) hloopK.b_lt
  refine ⟨hs'_eq ▸ hfr_loop.trans (CompOpFrame.of_gmFrame hfr_push), ?_, ?_⟩
  · rw [hs'_eq, hs_fix'_eq]
    unfold FixedCoupled
    have hgm0' : compGmAt metaBase U w N s₂.mem 0 = compGmAt metaBase U w N s₁.mem 0 + 1 := by
      rw [hgm_push, hf_fields.1]
    have hgm1' : compGmAt metaBase U w N s₂.mem 1 = compGmAt metaBase U w N s₁.mem 1 := by
      rw [hgm_push, hf_fields.2.1]
    have hbwin_eq : (compGmAt metaBase U w N s₁.mem 0 + 1) * slabSize N =
        compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N := Nat.add_one_mul _ _
    have htot_eq' : epochTotalSlots N (compGmAt metaBase U w N s₂.mem) =
        (compGmAt metaBase U w N s₁.mem 0 * slabSize N + slabSize N) +
          compGmAt metaBase U w N s₁.mem 1 := by
      unfold epochTotalSlots
      rw [ite_eq_right hb0, hgm0', hgm1', hbwin_eq]
    refine ⟨hgm_push.trans ((congrArg (fun g => gmPushSlab N g b) hcpl_loop.gm_eq).trans
        hgm_fpush.symm),
      hfr_push.lm_eq.trans (hcpl_loop.lm_eq.trans hl_fpush.symm),
      by simp only [hb0, ↓reduceIte, hgm0', hgm1', hbwin_eq, hfr_push.td_eq, hfr_push.dt_eq]
         exact hcpl_loop.win_inv,
      fun i => by rw [hfr_push.td_eq]; exact hcpl_loop.td_lt i,
      fun i => by rw [hfr_push.dt_eq]; exact hcpl_loop.dt_lt i,
      fun idx hidx => ?_,
      fun idx hidx => ?_⟩
    · rw [htot_eq', congrFun hfr_push.quot_eq idx, hgm0', hbwin_eq, hfr_push.dt_eq, hq_fpush]
      exact hcpl_loop.quot_eq idx (htot_eq' ▸ hidx)
    · rw [htot_eq', congrFun hfr_push.val_eq idx, hgm0', hbwin_eq, hfr_push.dt_eq, hv_fpush]
      exact hcpl_loop.val_eq idx (htot_eq' ▸ hidx)
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

private theorem compPromoteSlab_subgoals {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPromoteSlabPre w d s) :
    iterationSafe compPromoteStepGenProg CompPromoteStepPre w d (cpSlabSize d.1.1) 0 s ∧
    CompGmPushSlabPre w ((d.1.1, d.1.2.1), d.2)
      ((Memory.spec 0).clientState s (compPromoteLoopGenProg ((d, 0), cpSlabSize d.1.1))) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hpre, hcpl, hm_cap⟩ := h
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by
    unfold ghostW
    omega
  have hloop0 := promoteLoopInv_zero hpre
  have hcpl0 : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + 0)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + 0) + compGmAt metaBase U w N s.mem 1)
      s_fix s := by
    simpa only [FixedCoupled, epochTotalSlots, hb0, ↓reduceIte, Nat.add_zero] using hcpl
  have hm_cap0 : (compGmAt metaBase U w N s.mem 0 * slabSize N + 0) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap := by
    simpa only [totalSlots, hb0, ↓reduceIte, Nat.add_zero] using hm_cap
  obtain ⟨hfr_loop, hcpl_loop, _, hsafe_loop⟩ :=
    iterate_compPromoteStep_spec hb_pos (slabSize N) 0 s_fix s (by omega) henv hloop0 hcpl0 hm_cap0
  obtain ⟨hloopK, _, _⟩ :=
    iterate_promoteStepProg_spec (w := ghostW w) hwg hb_pos (slabSize N) 0 s_fix (by omega) hloop0
  rw [Nat.zero_add] at hcpl_loop hloopK
  have htot1 : (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      ((Memory.spec 0).clientState s_fix
        (iterate (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N))
          (0, b) (slabSize N) 0)).mem 0 + 1) * slabSize N ≤ N := by
    simpa only [Nat.add_one_mul] using Nat.le_of_add_right_le hloopK.tot_le
  have hp_lt1 := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  simp only [cpSlabSize_mk, compPromoteLoopGenProg]
  exact ⟨hsafe_loop, U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    hfr_loop.frontier_eq ▸ henv.meta_le_frontier, hb_pos, hloopK.b_lt,
    slabBijection_of_gm_eq hcpl_loop.gm_eq hloopK.slab_bij, hcpl_loop.gm_eq ▸ hp_lt1⟩

private theorem realizesBounded_compPromoteSlabGen :
    RealizesBounded .exact compPromoteSlabGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPromoteSlabPre (fun _ _ => 0) := by
  have hloop := realizesBounded_compPromoteLoopGen
  have hpush := realizesBounded_compGmPushSlabGen
  realize
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    exact (compPromoteSlab_subgoals h).1
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    exact (compPromoteSlab_subgoals h).2

private theorem validProg_compPromoteSlabGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPromoteSlabPre w d s) :
    ValidProg w 0 s (compPromoteSlabGenProg d) := by
  obtain ⟨hsafe, hpush⟩ := compPromoteSlab_subgoals h
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  dsimp only [compPromoteSlabGenProg]
  simp only [pure_bind]
  exact validProg_bind
    (validProg_iterate (cpSlabSize cp) 0 s (fun _ _ hs => validProg_compPromoteStep hs) hsafe)
    (validProg_compGmPushSlabGen hpush)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
