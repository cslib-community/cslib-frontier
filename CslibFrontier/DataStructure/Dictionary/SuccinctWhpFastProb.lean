/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.BurnIn

/-!
# Per-Operation Fast-Path Hit Probability for the WHP Succinct Dynamic Dictionary

This module connects the trailing-window hash-seed event `GoodSeedOnWindow` (proved to hold with
probability at least `1 - (max n_max 1)⁻¹ ^ c` in `SuccinctWhpProb`) to the deterministic pure
transition machine `whpRunPure` / `whpStepPure` (`SuccinctWhpModelTick`):

1. **Epoch rebuild potential (`stageWorkRemaining`)**: tracks remaining background ticks across
   Stages `0 .. 5` of `epochTick`. Under `GoodSeedOnWindow`, every dirty bucket admits a
   collision-free salt `< sMaxWhp c n_max`, bounding total rebuild ticks per epoch by
   `stageWorkMax c n_max < qEpochWhp n_max` so `epochTick` never aborts at rollover.
2. **Clean-epoch invariant (`CleanWindowFast`)**: bounds `(fs.buf fs.curEp).itemAlloc` by the
   number of colliding window insertions already encountered (`< 2 * sMaxWhp c n_max`), ensuring
   none of the capacity, backyard-pool, Stage-1 `rKey`, buffer-cap, or rollover guards in
   `fastStepPure` ever fires inside a clean epoch.
3. **Self-healing / rollover burn-in (`HasBurnInBudget`)**: within at most `qEpochWhp n_max`
   operations of entering the trailing window `windowSuffix` (`length = 2 * qEpochWhp n_max + 2`),
   either `trySelfHeal` or an epoch rollover deterministically places `whpRunPure` into
   `CleanWindowFast`, where it remains through the target operation `op`.
4. **Master per-operation fast-branch probability theorem (`toOuterMeasure_not_isFastStepHit_le`)**:
   for every `c, U, V, n_max` with `n_max ≤ U` and every admissible oblivious sequence
   `ops_prev ++ [op]`, the probability over `θ ~ seedLawWhp c U n_max` that step `op` fails to take
   the fast branch (`.small` below `whpThreshold c`, or `.fast` with `fastStepPure = some _` at or
   above `whpThreshold c`) is at most `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.IsFastStepHit`: predicate indicating that
  `whpStepPure` takes the fast branch (`.small` or `.fast` hit).

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.isFastStepHit_of_goodSeedOnWindow`: deterministic
  fast-branch hit guarantee whenever `GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ` holds.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.toOuterMeasure_not_isFastStepHit_le`:
  `(seedLawWhp c U n_max).toOuterMeasure {θ | ¬ IsFastStepHit ...} ≤ (max n_max 1)⁻¹ ^ c`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators ENNReal

/-- Predicate stating that on seed `θ` after history `ops_prev`, executing `op` takes the
fast branch (either `.small` mode when `n_max < whpThreshold c`, or `.fast` mode with
`fastStepPure = some _` when `whpThreshold c ≤ n_max`). -/
@[expose] def IsFastStepHit (c U n_max : ℕ) (ops_prev : List (Dynamic.Op U))
    (op : Dynamic.Op U) (θ : SeedWhp c U n_max) : Prop :=
  match whpRunPure c U n_max θ ops_prev with
  | .small _ => True
  | .fast fs => (fastStepPure c U n_max θ fs op).isSome = true
  | .fallback _ => False

/-- Deterministic bridge: for every `whpThreshold c ≤ n_max`, if `θ` satisfies `GoodSeedOnWindow`
on `ops_prev ++ [op]`, then `whpRunPure` reaches `.fast fs` after `ops_prev` and `fastStepPure`
succeeds (`some _`) on `op`. -/
theorem isFastStepHit_of_goodSeedOnWindow {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (hnU : n_max ≤ U)
    {ops_prev : List (Dynamic.Op U)} {op : Dynamic.Op U}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops_prev ++ [op]))
    {θ : SeedWhp c U n_max}
    (hg : GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ) :
    IsFastStepHit c U n_max ops_prev op θ := by
  classical
  set ops := ops_prev ++ [op]
  set s_start := windowStartState U n_max ops
  set suf := windowSuffix U n_max ops
  set W_ins := opInsKeys suf
  set W_keys := Dictionary.dom s_start ∪ W_ins
  let BadIns : Finset (Fin U) := W_ins.filter fun u =>
    ∃ v ∈ W_keys.filter (fun w =>
      feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val),
      u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
        fpHash c U n_max θ.2 salt u = fpHash c U n_max θ.2 salt v
  have hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns := fun _ hx hex => mem_filter.mpr ⟨hx, hex⟩
  have hbad_lt : #BadIns < 2 * sMaxWhp c n_max := hg.2.2.2.2
  obtain ⟨hv_prev, hv_op_singleton⟩ :=
    ((Dynamic.spec U V n_max).validHistory_append _ ops_prev [op]).mp hvh
  set dict_prev := ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops_prev).1
  have hval_op : Dynamic.valid V n_max dict_prev op := hv_op_singleton.1
  set k := ops.length - windowLenWhp n_max
  have hlen : ops.length = ops_prev.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hk_le : k ≤ ops_prev.length := by dsimp only [k, windowLenWhp]; omega
  have htake_eq : ops.take k = ops_prev.take k := List.take_append_of_le_length hk_le
  have hsuf_eq : suf = ops_prev.drop k ++ [op] := List.drop_append_of_le_length hk_le
  have hs_eq : s_start =
      ((Dynamic.spec U V n_max).run (Dictionary.empty U) (ops_prev.take k)).1 := by
    dsimp only [s_start, windowStartState]
    rw [htake_eq]
    exact spec_run_fst_irrel (V₁ := 0) (n₁ := 0) (V₂ := V) (n₂ := n_max) _ _
  have hvh_take : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops_prev.take k) := htake_eq ▸ validHistory_take k hvh
  -- Short histories start from the clean initial state with budget `0`; long ones start from
  -- any valid state with the full epoch budget, which the `≥ qEpochWhp` window suffix exhausts.
  obtain ⟨b, hbud0, hb⟩ : ∃ b, HasBurnInBudget c U V n_max θ W_keys BadIns
      (whpRunPure c U n_max θ (ops_prev.take k)) s_start b ∧
      b - (ops_prev.drop k).length = 0 := by
    by_cases hle : ops.length ≤ windowLenWhp n_max
    · have hk0 : k = 0 := Nat.sub_eq_zero_of_le hle
      refine ⟨0, Or.inl ⟨emptyFastState n_max, ?_, ?_⟩, Nat.zero_sub _⟩
      · rw [hk0, List.take_zero]
        exact ite_eq_right (not_lt.mpr hth)
      · rw [hs_eq, hk0, List.take_zero]
        exact CleanWindowFast.of_clean_fast (validFastState_empty hth θ) rfl rfl nofun
    · refine ⟨_, HasBurnInBudget.of_validWhpState hth (V := V)
        (hs_eq ▸ whpRunPure_spec hnU θ hvh_take), ?_⟩
      rw [List.length_drop]
      dsimp only [k, windowLenWhp] at hle ⊢
      omega
  have hv_drop : (Dynamic.spec U V n_max).ValidHistory s_start (ops_prev.drop k) :=
    hs_eq ▸ (((Dynamic.spec U V n_max).validHistory_append _ _ _).mp
      (by rwa [List.take_append_drop])).2
  have hbud_end := HasBurnInBudget.run hnU hg hbad_def hbad_lt (ops_prev.drop k) hbud0 hv_drop
    (fun s hs => by
      change s ∈ stateSeq s_start suf
      rw [hsuf_eq]
      exact mem_stateSeq_append_left _ _ _ s hs)
    (by
      change opInsKeys (ops_prev.drop k) ⊆ W_ins
      simp only [W_ins, hsuf_eq, opInsKeys_append]
      exact subset_union_left)
  have hrun_eq : whpRunFrom c U n_max θ
      (whpRunPure c U n_max θ (ops_prev.take k)) (ops_prev.drop k) =
      whpRunPure c U n_max θ ops_prev := by
    dsimp only [whpRunPure]
    rw [← whpRunFrom_append, List.take_append_drop]
  have hdict_eq : ((Dynamic.spec U V n_max).run s_start (ops_prev.drop k)).1 = dict_prev := by
    rw [hs_eq, ← spec_run_fst_append, List.take_append_drop]
  rw [hb, hrun_eq, hdict_eq] at hbud_end
  obtain ⟨fs, hfs, hcw⟩ := hbud_end.resolve_right fun h => by omega
  have hprev_mem : dict_prev ∈ stateSeq s_start suf := by
    rw [← hdict_eq, hsuf_eq]
    exact mem_stateSeq_append_left _ _ _ _
      (spec_run_fst_mem_stateSeq (V := V) (n_max := n_max) s_start (ops_prev.drop k))
  have hnxt_mem : (Dynamic.step dict_prev op).1 ∈ stateSeq s_start suf := by
    have h := spec_run_fst_mem_stateSeq (V := V) (n_max := n_max) s_start suf
    rwa [hsuf_eq, spec_run_fst_append, hdict_eq, ← hsuf_eq] at h
  have hdom_prev : (Dictionary.dom dict_prev : Set (Fin U)) ⊆ (W_keys : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys s_start suf _ hprev_mem
  have hdom_nxt :
      (Dictionary.dom (Dynamic.step dict_prev op).1 : Set (Fin U)) ⊆ (W_keys : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys s_start suf _ hnxt_mem
  have hop_ins : ∀ u v, op = .insert u v → u ∈ W_ins ∧ u ∈ W_keys := by
    rintro u v rfl
    have hu : u ∈ W_ins := by
      simp only [W_ins, hsuf_eq, opInsKeys_append]
      exact mem_union_right _ (mem_insert_self u ∅)
    exact ⟨hu, mem_union_right _ hu⟩
  obtain ⟨fs', res, hf, _⟩ := CleanWindowFast.step hnU hcw hval_op hdom_prev hdom_nxt hop_ins
    hg.1 (hg.2.1 _ hnxt_mem) hg.2.2.2.1 hbad_def hbad_lt
  simp only [IsFastStepHit, hfs, hf, Option.isSome_some]

/-- **Master per-operation slow-fallback probability bound**:
Across **all** capacities `n_max ≤ U` (both `< whpThreshold c` and `≥ whpThreshold c`), on any
admissible oblivious operation history `ops_prev ++ [op]`, the probability over `θ ~ seedLawWhp`
that `op` fails to take the fast branch (`IsFastStepHit`) is at most
`(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem toOuterMeasure_not_isFastStepHit_le {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {ops_prev : List (Dynamic.Op U)} {op : Dynamic.Op U}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops_prev ++ [op])) :
    (seedLawWhp c U n_max).toOuterMeasure
      {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} ≤
      (max n_max 1 : ℝ≥0∞)⁻¹ ^ c := by
  by_cases hth : whpThreshold c ≤ n_max
  · have hsub : {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} ⊆
        {θ | ¬ GoodSeedOnWindow c U n_max (ops_prev ++ [op]) θ} :=
      fun _ hnot hg => hnot (isFastStepHit_of_goodSeedOnWindow hth hnU hvh hg)
    exact (MeasureTheory.measure_mono hsub).trans
      (toOuterMeasure_not_goodSeedOnWindow_le hth hvh)
  · have hemp : {θ | ¬ IsFastStepHit c U n_max ops_prev op θ} = ∅ := by
      ext θ
      obtain ⟨sm', hsm'⟩ := whpRunFrom_small θ ops_prev emptySmallState
      simp [IsFastStepHit, whpRunPure, whpInitPure, Nat.lt_of_not_ge hth, hsm']
    simp only [hemp, MeasureTheory.measure_empty, zero_le]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
