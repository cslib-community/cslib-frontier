/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.StepFacts
import Mathlib.Data.Finset.Max

/-!
# Internal trace write-step monotonicity and last-idle-step helpers

Internal trace predicates (`isWriteStep`, `lastIdleStep`) and register-sequence monotonicity lemmas
shared across `ScanLoopInv`, `TraceInv`, `TracePreservation`, `LinearizationChunks`, and
`Linearizability`; never re-exported through `AtomicSnapshot`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotTrace.isWriteStep`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.lastIdleStep`: trace write and last-idle steps.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.reg_step_iff`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.seq_mono_and_const_of_eq`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.exists_writeStep_of_seq_ne`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.exists_last_writeStep_of_seq_pos`: register
  monotonicity and write lookup.
* `Cslib.Distributed.SetAgreement.getElem_completeHistoryAt_of_status_ne`: preserved non-matching
  history entries.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Predicate identifying when event `t < τ.events.length` is the atomic register write of
`update_j` (`proc j = .readyToWrite ...` and `events[t] = .step j`). -/
@[expose]
def isWriteStep (τ : SnapshotTrace ord dInit) (j : P) (t : ℕ) : Prop :=
  ∃ (ht : t < τ.events.length) (opId : ℕ) (val : Data) (snap : P → Data),
    τ.events[t]'ht = .step j ∧ (τ.stateAt t).proc j = .readyToWrite opId val snap

/-- Single-step register change characterization: `reg j` changes at step `t` **if and only if**
`isWriteStep τ j t` holds, in which case `(reg j).seq` increments by `1`. -/
theorem reg_step_iff (τ : SnapshotTrace ord dInit) (j : P) {t : ℕ}
    (ht : t < τ.events.length) :
    ((τ.stateAt (t + 1)).reg j = (τ.stateAt t).reg j ∧ ¬ τ.isWriteStep j t) ∨
      ∃ opId val snap,
        τ.events[t] = .step j ∧
        (τ.stateAt t).proc j = .readyToWrite opId val snap ∧
        (τ.stateAt (t + 1)).reg j = ⟨val, ((τ.stateAt t).reg j).seq + 1, snap⟩ ∧
        (τ.stateAt (t + 1)).proc j = .idle := by
  rcases (stepSnapshot_effect (τ.stateAt_step ht)).2 with
      ⟨i, opId, val, snap, hev, hpi, hs'⟩ | ⟨hnw, hreg, -⟩
  · by_cases hij : j = i
    · subst hij
      right
      refine ⟨opId, val, snap, hev, hpi, ?_, ?_⟩ <;> simp only [hs', Function.update_self]
    · left
      refine ⟨by simp only [hs', Function.update_of_ne hij], ?_⟩
      rintro ⟨_, _, _, _, h1, _⟩
      exact hij (SnapshotEvent.step.inj (h1.symm.trans hev))
  · exact Or.inl ⟨congrFun hreg j, fun ⟨_, id, v, sn, he, hp⟩ => hnw ⟨j, id, v, sn, he, hp⟩⟩

/-- Sequence numbers on `reg j` are monotone along any trace, and equal across `[t₁, t₂]` iff
`reg j` is constant across `[t₁, t₂]`. -/
theorem seq_mono_and_const_of_eq (τ : SnapshotTrace ord dInit) (j : P) {t₁ t₂ : ℕ}
    (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ τ.events.length) :
    ((τ.stateAt t₁).reg j).seq ≤ ((τ.stateAt t₂).reg j).seq ∧
      (((τ.stateAt t₁).reg j).seq = ((τ.stateAt t₂).reg j).seq →
        ∀ v, t₁ ≤ v → v ≤ t₂ → (τ.stateAt v).reg j = (τ.stateAt t₂).reg j) := by
  induction t₂ with
  | zero =>
    have ht₁ : t₁ = 0 := Nat.eq_zero_of_le_zero hle
    subst ht₁
    refine ⟨le_rfl, fun _ v _ hv => ?_⟩
    rw [Nat.eq_zero_of_le_zero hv]
  | succ t₂ ih =>
    by_cases hlt : t₁ ≤ t₂
    · obtain ⟨hmono, hconst⟩ := ih hlt (Nat.le_of_succ_le ht₂)
      rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht₂) with ⟨hreg_eq, -⟩ |
          ⟨_, _, _, -, -, hreg_upd, -⟩
      · refine ⟨hreg_eq ▸ hmono, fun hseq v hv₁ hv₂ => ?_⟩
        rw [hreg_eq] at hseq ⊢
        rcases Nat.of_le_succ hv₂ with hv₂' | rfl
        · exact hconst hseq v hv₁ hv₂'
        · exact hreg_eq
      · have hseq_succ : ((τ.stateAt (t₂ + 1)).reg j).seq = ((τ.stateAt t₂).reg j).seq + 1 := by
          rw [hreg_upd]
        exact ⟨by omega, fun hseq => absurd hseq (by omega)⟩
    · have heq : t₁ = t₂ + 1 := by omega
      subst heq
      exact ⟨le_rfl, fun _ v hv₁ hv₂ => by rw [Nat.le_antisymm hv₂ hv₁]⟩

/-- If `((τ.stateAt t₁).reg j).seq ≠ ((τ.stateAt t₂).reg j).seq` for `t₁ ≤ t₂ ≤ τ.events.length`,
then `j` executed an atomic register write `isWriteStep τ j w` at some step `t₁ ≤ w < t₂`. -/
theorem exists_writeStep_of_seq_ne (τ : SnapshotTrace ord dInit) (j : P) {t₁ t₂ : ℕ}
    (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ τ.events.length)
    (hne : ((τ.stateAt t₁).reg j).seq ≠ ((τ.stateAt t₂).reg j).seq) :
    ∃ w, t₁ ≤ w ∧ w < t₂ ∧ τ.isWriteStep j w := by
  induction t₂ with
  | zero =>
    rw [Nat.eq_zero_of_le_zero hle] at hne
    exact absurd rfl hne
  | succ t₂ ih =>
    by_cases hlt : t₁ ≤ t₂
    · rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht₂) with ⟨hreg_eq, -⟩ |
          ⟨opId, val, snap, hev, hproc, -, -⟩
      · rw [hreg_eq] at hne
        obtain ⟨w, hw₁, hw₂, hw⟩ := ih hlt (Nat.le_of_succ_le ht₂) hne
        exact ⟨w, hw₁, Nat.lt_succ_of_lt hw₂, hw⟩
      · exact ⟨t₂, hlt, Nat.lt_succ_self t₂,
          ⟨Nat.lt_of_succ_le ht₂, opId, val, snap, hev, hproc⟩⟩
    · have heq : t₁ = t₂ + 1 := by omega
      subst heq
      exact absurd rfl hne

/-- If `(τ.stateAt t).reg j` has `.seq > 0` (`t ≤ τ.events.length`), there is a most recent
`isWriteStep τ j w` with `w < t` such that `(τ.stateAt t).reg j = (τ.stateAt (w + 1)).reg j` and
no write by `j` occurred in `[w + 1, t)`. -/
theorem exists_last_writeStep_of_seq_pos (τ : SnapshotTrace ord dInit) (j : P) {t : ℕ}
    (ht : t ≤ τ.events.length) (hpos : 0 < ((τ.stateAt t).reg j).seq) :
    ∃ w, w < t ∧ τ.isWriteStep j w ∧
      (τ.stateAt t).reg j = (τ.stateAt (w + 1)).reg j ∧
      ∀ m, w + 1 ≤ m → m < t → ¬ τ.isWriteStep j m := by
  induction t with
  | zero =>
    rw [stateAt_zero] at hpos
    exact absurd hpos (Nat.not_lt_zero _)
  | succ t ih =>
    rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht) with ⟨hreg_eq, hnotw⟩ |
        ⟨opId, val, snap, hev, hproc, -, -⟩
    · rw [hreg_eq] at hpos
      obtain ⟨w, hwt, hw, hreg_w, hnow⟩ := ih (Nat.le_of_succ_le ht) hpos
      refine ⟨w, Nat.lt_succ_of_lt hwt, hw, hreg_w ▸ hreg_eq, fun m hm₁ hm₂ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm₂ with hm₂' | rfl
      · exact hnow m hm₁ hm₂'
      · exact hnotw
    · exact ⟨t, Nat.lt_succ_self t, ⟨Nat.lt_of_succ_le ht, opId, val, snap, hev, hproc⟩,
        rfl, fun _ hm₁ hm₂ => by omega⟩

/-- Zero is always in the idle-step filter up to step `t`. -/
private theorem zero_mem_idleFilter (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) :
    0 ∈ (range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle :=
  mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ t), by rw [stateAt_zero]; rfl⟩

/-- Proof-only helper: the largest step index `m ≤ t` at which `(τ.stateAt m).proc i = .idle`
(well-defined since `m = 0` always has `(τ.stateAt 0).proc i = .idle`). -/
noncomputable def lastIdleStep (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) : ℕ :=
  ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle).max'
    ⟨0, τ.zero_mem_idleFilter i t⟩

/-- Upper bound `lastIdleStep i t ≤ t`. -/
private theorem lastIdleStep_le (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) :
    τ.lastIdleStep i t ≤ t := by
  have hmem := Finset.max'_mem
    ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle)
    ⟨0, τ.zero_mem_idleFilter i t⟩
  exact Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hmem).1)

/-- Monotonicity of `lastIdleStep` with respect to any earlier idle step `m ≤ t`. -/
theorem le_lastIdleStep_of_idle (τ : SnapshotTrace ord dInit) (i : P) {m t : ℕ}
    (hle : m ≤ t) (hidle : (τ.stateAt m).proc i = .idle) :
    m ≤ τ.lastIdleStep i t := by
  apply Finset.le_max'
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle),
    (ProcSnapshotState.isIdle_eq_true _).mpr hidle⟩

/-- Recurrence for `lastIdleStep i (t + 1)` when `proc i` is non-idle at step `t + 1`. -/
theorem lastIdleStep_eq_of_step_not_idle (τ : SnapshotTrace ord dInit) (i : P) {t : ℕ}
    (hnot : (τ.stateAt (t + 1)).proc i ≠ .idle) :
    τ.lastIdleStep i (t + 1) =
      if ((τ.stateAt t).proc i).isIdle then t else τ.lastIdleStep i t := by
  apply le_antisymm
  · have hmem := Finset.max'_mem
      ((range (t + 2)).filter fun m => ((τ.stateAt m).proc i).isIdle)
      ⟨0, τ.zero_mem_idleFilter i (t + 1)⟩
    obtain ⟨hr, hid⟩ := mem_filter.mp hmem
    rw [ProcSnapshotState.isIdle_eq_true] at hid
    have hlt : τ.lastIdleStep i (t + 1) ≤ t := by
      have hle := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rcases Nat.of_le_succ hle with h | h
      · exact h
      · change _ = t + 1 at h
        rw [h] at hid
        exact absurd hid hnot
    split_ifs with htidle
    · exact hlt
    · exact τ.le_lastIdleStep_of_idle i hlt hid
  · split_ifs with htidle
    · exact τ.le_lastIdleStep_of_idle i (Nat.le_succ t)
        ((ProcSnapshotState.isIdle_eq_true _).mp htidle)
    · exact τ.le_lastIdleStep_of_idle i
        (le_trans (τ.lastIdleStep_le i t) (Nat.le_succ t))
        (by
          have hmem := Finset.max'_mem
            ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle)
            ⟨0, τ.zero_mem_idleFilter i t⟩
          exact (ProcSnapshotState.isIdle_eq_true _).mp (mem_filter.mp hmem).2)

end SnapshotTrace

/-- History entry lookup when its updated status differs from `newSt`. -/
theorem getElem_completeHistoryAt_of_status_ne {P Data : Type*}
    {hist : List (SnapshotOpRecord P Data)} {opId k : ℕ} {newSt st : SnapshotOpStatus P Data}
    (hne : st ≠ newSt) (hk : k < (completeHistoryAt hist opId newSt).length)
    (hst : ((completeHistoryAt hist opId newSt)[k]'hk).status = st) :
    ∃ hk₀ : k < hist.length, (completeHistoryAt hist opId newSt)[k]'hk = hist[k]'hk₀ := by
  have hk₀ : k < hist.length := (length_completeHistoryAt hist opId newSt) ▸ hk
  refine ⟨hk₀, ?_⟩
  by_cases hko : k = opId
  · subst hko
    by_cases hop : k < hist.length
    · have hset : completeHistoryAt hist k newSt =
          hist.set k { hist[k] with status := newSt } := by
        simp only [completeHistoryAt, List.getElem?_eq_getElem hop]
      rw [List.getElem_of_eq hset hk, List.getElem_set_self] at hst
      exact absurd hst.symm hne
    · exact absurd hk₀ hop
  · exact getElem_completeHistoryAt_ne hko hk

end Cslib.Distributed.SetAgreement
