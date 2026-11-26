/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.WorkPotential
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.TickStages
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.FastDeleteClean
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.FastInsertClean
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.EpochClock

/-!
# Clean-Window Stepping and Burn-In Countdown for `SuccinctWhpFastProb`

Internal closure (`CleanWindowFast.step`) and bounded burn-in convergence
(`HasBurnInBudget.run`) along the trailing window `windowSuffix`,
plus small-regime invariance `whpRunFrom_small` (not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

/-- Inside the trailing window under `GoodSeedOnWindow`, every admissible operation `op` from a
`CleanWindowFast` state succeeds with `fastStepPure = some (fs', res)` and preserves
`CleanWindowFast`. -/
theorem CleanWindowFast.step {c U V n_max : ℕ} (hnU : n_max ≤ U) {θ : SeedWhp c U n_max}
    {W_keys W_ins BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hcw : CleanWindowFast c U V n_max θ W_keys BadIns fs dict)
    {op : Dynamic.Op U} (hval : Dynamic.valid V n_max dict op)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hdom_nxt : (Dictionary.dom (Dynamic.step dict op).1 : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict op).1))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * sMaxWhp c n_max) :
    ∃ fs' res,
      fastStepPure c U n_max θ fs op = some (fs', res) ∧
      CleanWindowFast c U V n_max θ W_keys BadIns fs' (Dynamic.step dict op).1 := by
  have hv := hcw.valid
  cases op with
  | query u =>
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hv.toCore hv.overmars_valid hv.stage_valid.toPreTick
        hdom_sub hsalt_all hcw.salt_bound hcw.work_le
    exact ⟨fs', fastQuery c U n_max θ fs u, by simp only [fastStepPure, htick],
      ⟨hv', hbuf_or.elim (fun h => h ▸ hcw.buf_alloc) fun h => h ▸ Nat.zero_le _, hw', hs'⟩⟩
  | delete u =>
    obtain ⟨hc1, hom1, hpre1, _⟩ := hv.fastDelete_spec u
    obtain ⟨hclk1, hep1, hia1, hev1, hw1_le, hs1⟩ :=
      fastDelete_clean_props hv hdom_sub hcw.salt_bound u
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hc1 hom1 hpre1 hdom_nxt hsalt_all hs1
        (by have := hcw.work_le; omega)
    refine ⟨fs', none, by simp only [fastStepPure, htick], ⟨hv', ?_, hw', hs'⟩⟩
    rcases hbuf_or with hbeq | hia0
    · rw [hbeq, hia1]
      exact hcw.buf_alloc.trans_eq (congrArg card (filter_congr fun x _ => by
        rw [hev1 _ (fpReducedKey_lt c U n_max θ.2 x)]))
    · exact hia0 ▸ Nat.zero_le _
  | insert u v =>
    obtain ⟨hu_ins, hu_W⟩ := hop_ins u v rfl
    obtain ⟨fs1, hins, hclk1, hba1, hw1_eq, hs1⟩ :=
      fastInsert_some_and_clean_props hcw hval hu_ins hdom_sub hu_W hinj_rkey hbal_nxt
        hbad_def hbad_lt
    obtain ⟨hc1, hom1, hst1, _⟩ := hv.fastInsert_spec hnU hval hins
    obtain ⟨fs', htick, hv', hw', hs', hbuf_or⟩ :=
      epochTick_some_of_work_bound hc1 hom1 hst1.toPreTick hdom_nxt hsalt_all hs1
        (by rw [hclk1, hw1_eq]; exact hcw.work_le)
    exact ⟨fs', none, by simp only [fastStepPure, hins, htick],
      ⟨hv', hbuf_or.elim (fun h => h ▸ hba1) fun h => h ▸ Nat.zero_le _, hw', hs'⟩⟩

/-- Burn-in countdown budget to reach `CleanWindowFast` within the trailing window. -/
@[expose] def HasBurnInBudget (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (W_keys BadIns : Finset (Fin U)) (st : WhpDictState) (dict : State U) (b : ℕ) : Prop :=
  (∃ fs, st = .fast fs ∧ CleanWindowFast c U V n_max θ W_keys BadIns fs dict) ∨
  (1 ≤ b ∧ ValidWhpState c U V n_max θ st dict ∧
    match st with
    | .small _ => False
    | .fallback _ => True
    | .fast fs => qEpochWhp n_max - fs.epochClock ≤ b)

theorem HasBurnInBudget.of_validWhpState {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict) :
    HasBurnInBudget c U V n_max θ W_keys BadIns st dict (qEpochWhp n_max) := by
  have hq_pos : 1 ≤ qEpochWhp n_max := by
    unfold qEpochWhp; exact Nat.one_le_pow 18 _ (slabScale_pos n_max)
  right
  refine ⟨hq_pos, hv, ?_⟩
  cases st with
  | small sm => exact absurd hv.1 (not_lt.mpr hth)
  | fallback _ => trivial
  | fast fs => exact Nat.sub_le _ _

private theorem HasBurnInBudget.step {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {W_keys W_ins BadIns : Finset (Fin U)}
    {st : WhpDictState} {dict : State U} {b : ℕ}
    (hbud : HasBurnInBudget c U V n_max θ W_keys BadIns st dict b)
    {op : Dynamic.Op U} (hval : Dynamic.valid V n_max dict op)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hdom_nxt : (Dictionary.dom (Dynamic.step dict op).1 : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys)
    (hgood_nxt : GoodSeedOnState c U n_max θ (Dynamic.step dict op).1)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict op).1))
    (hsalt_all : ∀ bk : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = bk.val) : Set (Fin U)))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * sMaxWhp c n_max) :
    HasBurnInBudget c U V n_max θ W_keys BadIns
      (whpStepPure c U n_max θ st op).1 (Dynamic.step dict op).1 (b - 1) := by
  rcases hbud with ⟨fs, rfl, hcw⟩ | ⟨hb_pos, hv, hrem⟩
  · obtain ⟨fs', res, hf, hcw'⟩ := CleanWindowFast.step hnU hcw hval hdom_sub hdom_nxt hop_ins
      hinj_rkey hbal_nxt hsalt_all hbad_def hbad_lt
    exact Or.inl ⟨fs', by simp only [whpStepPure, hf], hcw'⟩
  · cases st with
    | small _ => exact absurd hrem id
    | fallback csr0 =>
      obtain ⟨hth, hcsr0, hqv0⟩ := hv
      dsimp only [whpStepPure]
      obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hval
      obtain ⟨fs', hsh, hcw'⟩ := trySelfHeal_clean hth hcsr1 hqv1 hgood_nxt
      exact Or.inl ⟨fs', hsh, hcw'⟩
    | fast fs =>
      change qEpochWhp n_max - fs.epochClock ≤ b at hrem
      dsimp only [whpStepPure]
      cases hf : fastStepPure c U n_max θ fs op with
      | none =>
        obtain ⟨hcsr0, hqv0⟩ := hv.fastToCsr_spec
        obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hval
        obtain ⟨fs', hsh, hcw'⟩ := trySelfHeal_clean hv.hth hcsr1 hqv1 hgood_nxt
        exact Or.inl ⟨fs', hsh, hcw'⟩
      | some p =>
        rcases p with ⟨fs', res⟩
        dsimp only
        have hv' := (hv.fastStepPure_spec hnU hval hf).1
        have hor : CleanWindowFast c U V n_max θ W_keys BadIns fs' (Dynamic.step dict op).1 ∨
            (fs'.epochClock = fs.epochClock + 1 ∧ fs.epochClock + 1 < qEpochWhp n_max) := by
          cases op with
          | query u =>
            dsimp only [fastStepPure] at hf
            split at hf <;> cases hf
            exact epochTick_clean_or_clock hv.toCore hv' ‹_›
          | delete u =>
            dsimp only [fastStepPure] at hf
            split at hf <;> cases hf
            exact (epochTick_clean_or_clock (hv.fastDelete_spec u).1 hv' ‹_›).imp_right
              fun h => by rwa [fastDelete_epochClock] at h
          | insert u v =>
            dsimp only [fastStepPure] at hf
            cases hi : fastInsert c U n_max θ fs u v with
            | none => rw [hi] at hf; cases hf
            | some fs1 =>
              rw [hi] at hf; dsimp only at hf
              split at hf <;> cases hf
              exact (epochTick_clean_or_clock (hv.fastInsert_spec hnU hval hi).1 hv' ‹_›).imp_right
                fun h => by rwa [fastInsert_epochClock hi] at h
        rcases hor with hcw' | ⟨hclk', hlt_q⟩
        · exact Or.inl ⟨fs', rfl, hcw'⟩
        · exact Or.inr ⟨by omega, hv', by dsimp only; omega⟩

theorem validHistory_take {U V n_max : ℕ} {s : State U}
    {ops : List (Dynamic.Op U)} (k : ℕ)
    (hvh : (Dynamic.spec U V n_max).ValidHistory s ops) :
    (Dynamic.spec U V n_max).ValidHistory s (ops.take k) := by
  induction ops generalizing s k with
  | nil => simp
  | cons o rest ih =>
    cases k with
    | zero => trivial
    | succ k => exact ⟨hvh.1, ih k hvh.2⟩

theorem mem_stateSeq_append_left {U : ℕ} (s₀ : State U)
    (l₁ l₂ : List (Dynamic.Op U)) :
    ∀ s ∈ stateSeq s₀ l₁, s ∈ stateSeq s₀ (l₁ ++ l₂) := by
  induction l₁ generalizing s₀ with
  | nil => simp [stateSeq, self_mem_stateSeq]
  | cons o rest ih =>
    intro s hs
    simp only [stateSeq, List.cons_append, List.mem_cons] at hs ⊢
    exact hs.imp id (ih (Dynamic.step s₀ o).1 s)

theorem opInsKeys_append {U : ℕ} (l₁ l₂ : List (Dynamic.Op U)) :
    opInsKeys (l₁ ++ l₂) = opInsKeys l₁ ∪ opInsKeys l₂ := by
  induction l₁ with
  | nil => simp [opInsKeys]
  | cons o rest ih =>
    cases o <;> simp [opInsKeys, ih, insert_union]

theorem HasBurnInBudget.run {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {ops : List (Dynamic.Op U)} {θ : SeedWhp c U n_max}
    (hg : GoodSeedOnWindow c U n_max ops θ)
    {BadIns : Finset (Fin U)}
    (hbad_def : ∀ x ∈ opInsKeys (windowSuffix U n_max ops),
      (∃ y ∈ (Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops)).filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * sMaxWhp c n_max) :
    ∀ (l : List (Dynamic.Op U)) {st : WhpDictState} {dict : State U} {b : ℕ},
      HasBurnInBudget c U V n_max θ
        (Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops))
        BadIns st dict b →
      (Dynamic.spec U V n_max).ValidHistory dict l →
      (∀ s ∈ stateSeq dict l,
        s ∈ stateSeq (windowStartState U n_max ops) (windowSuffix U n_max ops)) →
      opInsKeys l ⊆ opInsKeys (windowSuffix U n_max ops) →
      HasBurnInBudget c U V n_max θ
        (Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops))
        BadIns (whpRunFrom c U n_max θ st l)
        (((Dynamic.spec U V n_max).run dict l).1) (b - l.length) := by
  intro l
  induction l with
  | nil =>
    intro st dict b hbud _ _ _
    simpa [whpRunFrom] using hbud
  | cons o rest ih =>
    intro st dict b hbud hv_l hseq_sub hins_sub
    have hdict_mem := hseq_sub dict (self_mem_stateSeq dict (o :: rest))
    have hnxt_mem := hseq_sub (Dynamic.step dict o).1
      (List.mem_cons_of_mem dict (self_mem_stateSeq _ rest))
    have hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆
        ((Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) : Finset (Fin U)) : Set (Fin U)) := by
      exact_mod_cast dom_subset_union_opInsKeys _ _ dict hdict_mem
    have hdom_nxt : (Dictionary.dom (Dynamic.step dict o).1 : Set (Fin U)) ⊆
        ((Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) : Finset (Fin U)) : Set (Fin U)) := by
      exact_mod_cast dom_subset_union_opInsKeys _ _ _ hnxt_mem
    have hop_ins : ∀ u v, o = .insert u v →
        u ∈ opInsKeys (windowSuffix U n_max ops) ∧
        u ∈ Dictionary.dom (windowStartState U n_max ops) ∪
          opInsKeys (windowSuffix U n_max ops) := by
      rintro u v rfl
      have hu : u ∈ opInsKeys (windowSuffix U n_max ops) :=
        hins_sub (mem_insert_self u _)
      exact ⟨hu, mem_union_right _ hu⟩
    have hstep := HasBurnInBudget.step hnU hbud hv_l.1 hdom_sub hdom_nxt hop_ins
      (hg.goodSeedOnState_of_mem hnxt_mem) hg.1 (hg.2.1 _ hnxt_mem) hg.2.2.2.1 hbad_def hbad_lt
    have hins_rest : opInsKeys rest ⊆ opInsKeys (windowSuffix U n_max ops) := by
      refine Subset.trans ?_ hins_sub
      cases o <;> simp [opInsKeys, subset_insert]
    have hres := ih hstep hv_l.2
      (fun s hs => hseq_sub s (List.mem_cons_of_mem dict hs)) hins_rest
    change HasBurnInBudget c U V n_max θ _ BadIns
      (whpRunFrom c U n_max θ (whpStepPure c U n_max θ st o).1 rest)
      ((Dynamic.spec U V n_max).run (Dynamic.step dict o).1 rest).1
      (b - (rest.length + 1))
    simpa only [Nat.add_comm, Nat.sub_sub] using hres

theorem whpRunFrom_small {c U n_max : ℕ} (θ : SeedWhp c U n_max) :
    ∀ (ops : List (Dynamic.Op U)) (sm : SmallDictState),
      ∃ sm', whpRunFrom c U n_max θ (.small sm) ops = .small sm' := by
  intro ops
  induction ops with
  | nil => exact fun sm => ⟨sm, rfl⟩
  | cons o _ ih => exact fun _ => by cases o <;> exact ih _

end Cslib.DataStructure.Dictionary.SuccinctWhp
