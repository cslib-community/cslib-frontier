/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
public import CslibFrontier.Computability.WordRAM.Realization.Structure
public import CslibFrontier.DataStructure.Memory.Copy
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Reusable verified Word-RAM array primitives over `Memory.Prog`

This module provides reusable verified array and block primitives over `Memory.Prog`, equipping
both newly defined array routines (`fillConstProg`, `prefixSumProg`) and the existing memory
operations (`Memory.copy`, `Memory.allocBlock`, `Memory.allocBlockDirty`) with uniform
`Realizes .exact` certificates (`work := 0`) and `Memory.FramedTriple` specifications.

## Main definitions

* `fillConstProg`: fill `[base, base + count)` with a constant `val`.
* `prefixSumProg`: in-place exclusive prefix sum over `[base, base + count)` storing
  `[0, a₀, a₀ + a₁, ...]` and returning the total sum.

## Main results

* `fillConstProg_spec`, `realizes_fillConstProg`: framed triple and `Realizes .exact`
  certificate for `fillConstProg`.
* `realizes_copy`: uniform `Realizes .exact` certificate for `Memory.copy` (paired with
  `Memory.FramedTriple.copy`).
* `prefixSumProg_spec`, `realizes_prefixSumProg`: framed triple and `Realizes .exact`
  certificate for `prefixSumProg`.
* `allocBlock_spec`, `realizes_allocBlock`, `allocBlockDirty_spec`, `realizes_allocBlockDirty`:
  framed triples and `Realizes .exact` certificates for `Memory.allocBlock` and
  `Memory.allocBlockDirty`.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Constant fill (`fillConstProg`) -/

private def fillConstStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, val), idx) => do
    Memory.write (base + idx) val
    pure (idx + 1)

private def fillConstStepSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (_ : Memory.State) : Prop :=
  Fits w (d.2 + 1)

private theorem realizes_fillConstStep_history : Realizes .exact
    fillConstStep WordEncoding.encode WordEncoding.encode
    (fun w d s => fillConstStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillConstStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => do
        Memory.write (d.1.1 + d.2) d.1.2
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => fillConstStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillConstStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨⟨_, _⟩, _⟩
      obtain ⟨hfit, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, fillConstStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)

private theorem realizes_fillConstStep :
    Realizes .exact fillConstStep WordEncoding.encode WordEncoding.encode fillConstStepSafe
      (fun _ _ => 0) :=
  realizes_fillConstStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Fill `count` consecutive cells `[base, base + count)` with `val`. -/
def fillConstProg (base val count : ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillConstStep (base, val) count 0
  pure ()

private theorem fillConst_loop_spec {w base val count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hval : Fits w val) (hcount : Fits w count)
    (hbound : base + count ≤ s.frontier) :
    iterationSafe fillConstStep fillConstStepSafe w (base, val) count 0 s ∧
    Memory.FramedTriple w s (fillConstProg base val count) count (Set.Ico base (base + count))
      fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = val := by
  let S : Set ℕ := Set.Ico base (base + count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∀ j < k, t.mem (base + j) = val
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      fillConstStepSafe w ((base, val), a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (fillConstStep ((base, val), a))) ∧
      let a' := (Memory.spec 0).clientResult t (fillConstStep ((base, val), a))
      let t' := (Memory.spec 0).clientState t (fillConstStep ((base, val), a))
      memoryCost (fillConstStep ((base, val), a)) t + 0 ≤ 0 + 1 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hfill⟩
    subst a
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (fillConstStep ((base, val), k))) := by
      dsimp only [fillConstStep]
      exact validHistory_write_bind (by rw [htfr]; omega) hval (validHistory_pure w _ _)
    have hcost : memoryCost (fillConstStep ((base, val), k)) t ≤ 1 := by
      dsimp only [fillConstStep]
      simp only [memoryCost_bind', memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult t (fillConstStep ((base, val), k)) = k + 1 := by
      dsimp only [fillConstStep]
      simp only [clientResult_bind_write, StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (fillConstStep ((base, val), k)) =
        ⟨Function.update t.mem (base + k) val, t.frontier⟩ := rfl
    have hmod : Memory.Modifies S t ⟨Function.update t.mem (base + k) val, t.frontier⟩ :=
      Memory.Modifies.set t ⟨base, count⟩ hk val
    refine ⟨hcount.of_le (by omega), hvh, by omega, by rw [hst]; exact hmod,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh, fun j hj => ?_⟩
    rw [hst]
    dsimp only
    by_cases hjk : j = k
    · rw [hjk, Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact hfill j (by omega)
  obtain ⟨hsafe, hv, hcost, hmod, _, htfr, hwf', hvals⟩ :=
    iterate_potential_spec fillConstStep fillConstStepSafe w (base, val) 1 count
      inv (fun _ _ _ => 0) S hstep 0 s ⟨rfl, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hloop : Memory.FramedTriple w s (iterate fillConstStep (base, val) count 0) count S
      fun _ s' => s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = val :=
    framedTriple_iff_realization.mpr ⟨hv, by simpa using hcost, hmod, htfr, hwf', hvals⟩
  have hres : Memory.FramedTriple w s (fillConstProg base val count) count S
      fun _ s' => s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = val :=
    ((hloop.mono le_rfl fun _ _ h =>
      Memory.FramedTriple.pure (c := 0) (a := ()) h).bind_same).mono
      (Nat.add_zero count).le fun _ _ h => h
  exact ⟨hsafe, hres⟩

/-- Framed specification for `fillConstProg`: fills `[base, base + count)` with `val`, preserves
frontier and all cells outside `[base, base + count)`, costs at most `count`, and preserves
`WellFormed`. -/
theorem fillConstProg_spec {w base val count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hval : Fits w val) (hcount : Fits w count)
    (hbound : base + count ≤ s.frontier) :
    Memory.FramedTriple w s (fillConstProg base val count) count (Set.Ico base (base + count))
      fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = val :=
  (fillConst_loop_spec hwf hval hcount hbound).2

/-- Uniform `Realizes .exact` certificate for `fillConstProg` with `work = 0`. -/
theorem realizes_fillConstProg :
    Realizes .exact (fun ((base, val), count) => fillConstProg base val count)
      WordEncoding.encode WordEncoding.encode
      (fun _ ((base, _), count) s => base + count ≤ s.frontier) (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : (ℕ × ℕ) × ℕ => fillConstProg d.1.1 d.1.2 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : ((ℕ × ℕ) × ℕ) × ℕ =>
          fillConstStep ((x.1.1.1, x.1.1.2), x.2))
        (fun w d s => fillConstStepSafe w ((d.1.1.1, d.1.1.2), d.2) s) w d d.2 0 s)
      (fun _ _ => 0) := by
    unfold fillConstProg
    realize [realizes_fillConstStep]
    exact h
  refine (hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)).consequence (fun w d s hwords hmem hbound => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨⟨base, val⟩, count⟩
  have hval : Fits w val := hwords 1
  have hcnt : Fits w count := hwords 2
  exact iterationSafe_imp (fillConst_loop_spec hmem hval hcnt hbound).1
    (fun _ => rfl) (fun _ _ hs => hs)

/-! ## Uniform realization of `Memory.copy` -/

private def copySliceStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((src, dst), idx) => do
    let v ← Memory.read (src + idx)
    Memory.write (dst + idx) v
    pure (idx + 1)

private def copySliceStepSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (_ : Memory.State) : Prop :=
  Fits w (d.2 + 1)

private theorem realizes_copySliceStep_history : Realizes .exact
    copySliceStep WordEncoding.encode WordEncoding.encode
    (fun w d s => copySliceStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copySliceStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => do
        let v ← Memory.read (d.1.1 + d.2)
        Memory.write (d.1.2 + d.2) v
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => copySliceStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copySliceStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨⟨_, _⟩, _⟩
      obtain ⟨hfit, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, copySliceStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
        Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)

private theorem realizes_copySliceStep :
    Realizes .exact copySliceStep WordEncoding.encode WordEncoding.encode copySliceStepSafe
      (fun _ _ => 0) :=
  realizes_copySliceStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem iterate_succ_last {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (d : δ) (n : ℕ) (a : σ) :
    iterate body d (n + 1) a = (iterate body d n a >>= fun s => body (d, s)) := by
  induction n generalizing a with
  | zero => simp [iterate]
  | succ n ih =>
    change (body (d, a) >>= fun s' => iterate body d (n + 1) s') =
      ((body (d, a) >>= fun s' => iterate body d n s') >>= fun s => body (d, s))
    rw [bind_assoc]
    congr 1 with s' : 1
    exact ih s'

private theorem copySliceStep_bind {β : Type} (src dst k : ℕ) (q : ℕ → Memory.Prog β) :
    (copySliceStep ((src, dst), k) >>= q) =
      (Memory.read (src + k) >>= fun v => Memory.write (dst + k) v >>= fun _ => q (k + 1)) := by
  simp only [copySliceStep, bind_assoc, pure_bind]

private theorem iterate_copySliceStep_bind {β : Type} (src dst n k : ℕ)
    (q : ℕ → Memory.Prog β) :
    (iterate copySliceStep (src, dst) n k >>= q) =
      (iterate copySliceStep (src, dst) n k >>= fun _ => q (k + n)) := by
  induction n generalizing k with
  | zero => simp [iterate]
  | succ n ih =>
    change (copySliceStep ((src, dst), k) >>= fun a => iterate copySliceStep (src, dst) n a) >>= q =
      (copySliceStep ((src, dst), k) >>= fun a => iterate copySliceStep (src, dst) n a) >>=
        fun _ => q (k + (n + 1))
    rw [bind_assoc, copySliceStep_bind, show k + (n + 1) = k + 1 + n from by omega,
      bind_assoc, copySliceStep_bind]
    congr 1 with v : 1
    congr 1 with u : 1
    exact ih (k + 1)

private theorem copy_eq_iterate (src dst count : ℕ) :
    Memory.copy src dst count =
      (iterate copySliceStep (src, dst) count 0 >>= fun _ => pure ()) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    have hunit : (fun _ : Unit => (Pure.pure () : Memory.Prog Unit)) = Pure.pure :=
      funext fun () => rfl
    rw [Memory.copy_succ, ih, iterate_succ_last,
      iterate_copySliceStep_bind (q := fun s => copySliceStep ((src, dst), s)), Nat.zero_add]
    simp only [bind_assoc, copySliceStep_bind, pure_bind, hunit, bind_pure]

private theorem copySlice_iterationSafe {w src dst count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count)
    (hsrc : src + count ≤ s.frontier) (hdst : dst + count ≤ s.frontier) :
    iterationSafe copySliceStep copySliceStepSafe w (src, dst) count 0 s := by
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t
  refine (iterate_potential_spec copySliceStep copySliceStepSafe w (src, dst) 2
    count inv (fun _ _ _ => 0) Set.univ (fun k hk a t ⟨ha, htfr, hwt⟩ => by
      subst a
      have hvh : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (copySliceStep ((src, dst), k))) := by
        dsimp only [copySliceStep]
        exact validHistory_read_bind (by rw [htfr]; omega)
          (validHistory_write_bind (by rw [htfr]; omega) (hwt.mem_fits _)
            (validHistory_pure w _ _))
      have hcost : memoryCost (copySliceStep ((src, dst), k)) t ≤ 2 := by
        dsimp only [copySliceStep]
        simp only [memoryCost_bind', memoryCost_read, memoryCost_write, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult t (copySliceStep ((src, dst), k)) = k + 1 := by
        dsimp only [copySliceStep]
        simp only [clientResult_bind_read, clientResult_bind_write,
          StateTransitionSpec.clientResult_pure]
      have hst : (Memory.spec 0).clientState t (copySliceStep ((src, dst), k)) =
          ⟨Function.update t.mem (dst + k) (t.mem (src + k)), t.frontier⟩ := rfl
      refine ⟨hcnt.of_le (by omega), hvh, by omega,
        ⟨by rw [hst], fun _ _ hx => absurd (Set.mem_univ _) hx⟩,
        hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh⟩)
    0 s ⟨rfl, rfl, hwf⟩).1

/-- Uniform `Realizes .exact` certificate for `Memory.copy` with `work = 0`. -/
theorem realizes_copy :
    Realizes .exact (fun ((src, dst), count) => Memory.copy src dst count)
      WordEncoding.encode WordEncoding.encode
      (fun _ ((src, dst), count) s => src + count ≤ s.frontier ∧ dst + count ≤ s.frontier)
      (fun _ _ => 0) := by
  let copyProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit := fun d => do
    let _ ← iterate copySliceStep (d.1.1, d.1.2) d.2 0
    pure ()
  have hraw : Realizes .exact copyProg
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : ((ℕ × ℕ) × ℕ) × ℕ =>
          copySliceStep ((x.1.1.1, x.1.1.2), x.2))
        (fun w d s => copySliceStepSafe w ((d.1.1.1, d.1.1.2), d.2) s) w d d.2 0 s)
      (fun _ _ => 0) := by
    dsimp only [copyProg]
    realize [realizes_copySliceStep]
    exact h
  refine (hraw.congr (fun ⟨⟨src, dst⟩, count⟩ =>
    (copy_eq_iterate src dst count).symm)).consequence
      (fun w d s hwords hmem hbound => ?_) (fun _ _ => le_rfl)
  rcases d with ⟨⟨src, dst⟩, count⟩
  exact iterationSafe_imp (copySlice_iterationSafe hmem (hwords 2) hbound.1 hbound.2)
    (fun _ => rfl) (fun _ _ hs => hs)

/-! ## In-place exclusive prefix sum (`prefixSumProg`) -/

private def prefixSumStep : ℕ × ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (base, idx, acc) => do
    let x ← Memory.read (base + idx)
    Memory.write (base + idx) acc
    pure (idx + 1, acc + x)

private def prefixSumStepSafe (w : ℕ) : ℕ × ℕ × ℕ → Memory.State → Prop
  | (base, idx, acc), s => Fits w (idx + 1) ∧ Fits w (acc + s.mem (base + idx))

private theorem realizes_prefixSumStep_history : Realizes .exact
    prefixSumStep WordEncoding.encode WordEncoding.encode
    (fun w d s => prefixSumStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (prefixSumStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : ℕ × ℕ × ℕ => do
        let x ← Memory.read (d.1 + d.2.1)
        Memory.write (d.1 + d.2.1) d.2.2
        pure (d.2.1 + 1, d.2.2 + x))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => prefixSumStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (prefixSumStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨_, _, _⟩
      obtain ⟨⟨hfit1, hfit2⟩, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, prefixSumStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
        Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨_, _, _⟩ => rfl)

private theorem realizes_prefixSumStep :
    Realizes .exact prefixSumStep WordEncoding.encode WordEncoding.encode prefixSumStepSafe
      (fun _ _ => 0) :=
  realizes_prefixSumStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- In-place exclusive prefix sum over `[base, base + count)`: overwrites `mem (base + j)` with
`∑ i ∈ Finset.range j, mem (base + i)` for `j < count`, and returns the total sum
`∑ i ∈ Finset.range count, mem (base + i)`. -/
def prefixSumProg (base count : ℕ) : Memory.Prog ℕ := do
  let res ← iterate prefixSumStep base count (0, 0)
  pure res.2

private theorem prefixSum_loop_spec {w base count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count) (hbound : base + count ≤ s.frontier)
    (hsum : Fits w (∑ i ∈ Finset.range count, s.mem (base + i))) :
    iterationSafe prefixSumStep prefixSumStepSafe w base count (0, 0) s ∧
    Memory.FramedTriple w s (prefixSumProg base count) (2 * count) (Set.Ico base (base + count))
      fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) := by
  let S : Set ℕ := Set.Ico base (base + count)
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a.1 = k ∧
    a.2 = (∑ i ∈ Finset.range k, s.mem (base + i)) ∧
    t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧
    (∀ j < k, t.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i)) ∧
    (∀ i, k ≤ i → i < count → t.mem (base + i) = s.mem (base + i))
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      prefixSumStepSafe w (base, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (prefixSumStep (base, a))) ∧
      let a' := (Memory.spec 0).clientResult t (prefixSumStep (base, a))
      let t' := (Memory.spec 0).clientState t (prefixSumStep (base, a))
      memoryCost (prefixSumStep (base, a)) t + 0 ≤ 0 + 2 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk ⟨idx, acc⟩ t ⟨hidx, hacc, htfr, hwt, hpref, hrest⟩
    dsimp only at hidx hacc
    subst idx
    have hcur : t.mem (base + k) = s.mem (base + k) := hrest k (le_refl k) hk
    have hacc_next : acc + t.mem (base + k) = ∑ i ∈ Finset.range (k + 1), s.mem (base + i) := by
      rw [hacc, hcur, Finset.sum_range_succ]
    have hfit_acc : Fits w acc :=
      hsum.of_le (hacc ▸ Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    have hfit_next : Fits w (acc + t.mem (base + k)) :=
      hsum.of_le (hacc_next ▸ Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (prefixSumStep (base, (k, acc)))) := by
      dsimp only [prefixSumStep]
      exact validHistory_read_bind (by rw [htfr]; omega)
        (validHistory_write_bind (by rw [htfr]; omega) hfit_acc (validHistory_pure w _ _))
    have hcost : memoryCost (prefixSumStep (base, (k, acc))) t ≤ 2 := by
      dsimp only [prefixSumStep]
      simp only [memoryCost_bind', memoryCost_read, memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult t (prefixSumStep (base, (k, acc))) =
        (k + 1, acc + t.mem (base + k)) := by
      dsimp only [prefixSumStep]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (prefixSumStep (base, (k, acc))) =
        ⟨Function.update t.mem (base + k) acc, t.frontier⟩ := rfl
    have hmod : Memory.Modifies S t ⟨Function.update t.mem (base + k) acc, t.frontier⟩ :=
      Memory.Modifies.set t ⟨base, count⟩ hk acc
    have hfit_k1 : Fits w (k + 1) := hcnt.of_le (by omega)
    refine ⟨⟨hfit_k1, hfit_next⟩, hvh, by omega, by rw [hst]; exact hmod, ?_⟩
    rw [hres, hst]
    refine ⟨rfl, hacc_next, htfr, wellFormed_clientState hwt hvh, fun j hj => ?_,
      fun i hik hic => ?_⟩
    · dsimp only
      by_cases hjk : j = k
      · rw [hjk, Function.update_self, hacc]
      · rw [Function.update_of_ne (by omega)]
        exact hpref j (by omega)
    · dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hrest i (by omega) hic
  obtain ⟨hsafe, hv, hcost, hmod, _, hres, htfr, hwf', hpref, _⟩ :=
    iterate_potential_spec prefixSumStep prefixSumStepSafe w base 2 count
      inv (fun _ _ _ => 0) S hstep (0, 0) s
      ⟨rfl, by simp, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  have hloop : Memory.FramedTriple w s (iterate prefixSumStep base count (0, 0)) (2 * count) S
      fun res s' =>
        res.2 = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
    framedTriple_iff_realization.mpr ⟨hv, by simpa using hcost, hmod, hres, htfr, hwf', hpref⟩
  have hret : Memory.FramedTriple w s (prefixSumProg base count) (2 * count) S
      fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
    ((hloop.mono le_rfl fun res _ h =>
      Memory.FramedTriple.pure (c := 0) (a := res.2) h).bind_same).mono
      (Nat.add_zero _).le fun _ _ h => h
  exact ⟨hsafe, hret⟩

/-- Framed specification for `prefixSumProg`: computes the in-place exclusive prefix sum over
`[base, base + count)`, returns the total sum `∑ i ∈ Finset.range count, s.mem (base + i)`,
preserves frontier and all cells outside `[base, base + count)`, costs at most `2 * count`, and
preserves `WellFormed`. -/
theorem prefixSumProg_spec {w base count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count) (hbound : base + count ≤ s.frontier)
    (hsum : Fits w (∑ i ∈ Finset.range count, s.mem (base + i))) :
    Memory.FramedTriple w s (prefixSumProg base count) (2 * count) (Set.Ico base (base + count))
      fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
  (prefixSum_loop_spec hwf hcnt hbound hsum).2

/-- Uniform `Realizes .exact` certificate for `prefixSumProg` with `work = 0`. -/
theorem realizes_prefixSumProg :
    Realizes .exact (fun d : ℕ × ℕ => prefixSumProg d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => d.1 + d.2 ≤ s.frontier ∧
        Fits w (∑ i ∈ Finset.range d.2, s.mem (d.1 + i)))
      (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : ℕ × ℕ => prefixSumProg d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : (ℕ × ℕ) × ℕ × ℕ => prefixSumStep (x.1.1, x.2))
        (fun w d s => prefixSumStepSafe w (d.1.1, d.2.1, d.2.2) s) w d d.2 (0, 0) s)
      (fun _ _ => 0) := by
    unfold prefixSumProg
    realize [realizes_prefixSumStep]
    exact h
  exact hraw.consequence (fun w d s hwords hmem ⟨hbound, hsum⟩ =>
    iterationSafe_imp (prefixSum_loop_spec hmem (hwords 1) hbound hsum).1
      (fun _ => rfl) (fun _ _ hs => hs)) (fun _ _ => le_rfl)

/-! ## Uniform realization and framed specs for `Memory.allocBlock` / `Memory.allocBlockDirty` -/

/-- Uniform `Realizes .exact` certificate for `Memory.allocBlock` with `work = 0`. -/
theorem realizes_allocBlock :
    Realizes .exact Memory.allocBlock WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold Memory.allocBlock
  realize

/-- Framed specification for `Memory.allocBlock`: costs `size + 1`, preserves all cells below
`s.frontier` (`Memory.Modifies ∅`), returns `⟨s.frontier, size⟩` allocated and zeroed, preserves
`WellFormed`, and guarantees disjointness from every block previously allocated in `s`. -/
theorem allocBlock_spec {w size : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + size)) :
    Memory.FramedTriple w s (Memory.allocBlock size) (size + 1) ∅ fun b s' =>
      b = ⟨s.frontier, size⟩ ∧
      b.Allocated s' ∧
      Memory.WellFormed w s' ∧
      (∀ j < size, s'.mem (b.base + j) = 0) ∧
      ∀ b' : Block, b'.Allocated s → b'.Disjoint b := by
  refine Memory.FramedTriple.mono
    (Memory.FramedTriple.allocBlock_bind (c := 0) hfit (Memory.FramedTriple.pure ?_))
    (Nat.zero_add _).le fun _ _ h => h
  refine ⟨rfl, le_rfl, hwf.step (o := .alloc size) hfit, fun j hj => ?_, fun b' hb' => ?_⟩
  · exact clear_of_owns (Block.owns_add (b := ⟨s.frontier, size⟩) hj)
  · exact Block.disjoint_of_allocated_frontier hb' size

/-- Uniform `Realizes .exact` certificate for `Memory.allocBlockDirty` with `work = 0`. -/
theorem realizes_allocBlockDirty :
    Realizes .exact Memory.allocBlockDirty WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold Memory.allocBlockDirty
  realize

/-- Framed specification for `Memory.allocBlockDirty` under `Memory.ZeroAbove s`: costs `1`,
modifies nothing below `s.frontier` (`Memory.Modifies ∅`), returns `⟨s.frontier, size⟩` allocated
and zeroed, preserves `WellFormed` and `ZeroAbove`, and guarantees disjointness from every block
previously allocated in `s`. -/
theorem allocBlockDirty_spec {w size : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hz : Memory.ZeroAbove s) (hfit : Fits w (s.frontier + size)) :
    Memory.FramedTriple w s (Memory.allocBlockDirty size) 1 ∅ fun b s' =>
      b = ⟨s.frontier, size⟩ ∧
      b.Allocated s' ∧
      Memory.WellFormed w s' ∧
      Memory.ZeroAbove s' ∧
      (∀ j < size, s'.mem (b.base + j) = 0) ∧
      ∀ b' : Block, b'.Allocated s → b'.Disjoint b := by
  refine Memory.FramedTriple.allocBlockDirty_bind (c := 0) hfit (Memory.FramedTriple.pure ?_)
  refine ⟨rfl, le_rfl, hwf.step (o := .allocDirty size) hfit, hz.allocDirty size,
    fun j hj => hz (s.frontier + j) (by omega), fun b' hb' => ?_⟩
  exact Block.disjoint_of_allocated_frontier hb' size

end Cslib.WordRAM.Realization
