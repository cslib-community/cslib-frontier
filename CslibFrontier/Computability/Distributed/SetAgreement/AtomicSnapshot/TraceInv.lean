/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceWrites
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.ScanLoopInv

/-!
# Internal global trace invariant and per-actor frame lemma

Defines the trace invariant `TraceInv` and its shared per-actor frame specialization
`TraceInv.of_actor_step`; never re-exported through `AtomicSnapshot`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotTrace.TraceInv`: global invariant over `SnapshotTrace`.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.lastIdleStep_keep`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.TraceInv.of_actor_step`: idle-step invariance and
  per-actor transition frame lemma.
-/

public section

namespace Cslib.Distributed.SetAgreement

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Combined trace invariant at step `t ≤ τ.events.length` powering Lemmas 3.1–3.3 and Theorem 1:
1. `(τ.stateAt t).stepCount = t`.
2. For every register `j` with `((τ.stateAt t).reg j).seq > 0` whose most recent write occurred at
   `w < t`, there exists a serialization state `v` with `τ.lastIdleStep j w + 1 ≤ v ≤ w` such that
   `memSnapshot (τ.stateAt v).reg = ((τ.stateAt t).reg j).view`.
3. For every active process `i`:
   - if `proc i = .readyToWrite opId val snap`: `opId < history.length`, `history[opId]` is pending
     `update val` by `i` with `invStep = τ.lastIdleStep i t < t`, and there exists `v` with
     `invStep + 1 ≤ v ≤ t` and `memSnapshot (τ.stateAt v).reg = snap`;
   - if `proc i = .scanning st`: `opId < history.length`, `history[opId]` is pending (`scan` or
     `update val` matching `st.mode`) by `i` with `invStep = τ.lastIdleStep i t < t`, and
     `ScanLoopInv τ (τ.lastIdleStep i t) t st` holds.
4. For every history index `id < history.length` with record `rec`:
   - if `rec.status = .pending`, then `proc rec.caller` is active with `opId = id` and
     `rec.invStep = τ.lastIdleStep rec.caller t < t`;
   - if `rec.status = .doneScan resp snap`, then `rec.kind = .scan`, `rec.invStep < resp < t`, and
     there exists `v` with `rec.invStep + 1 ≤ v ≤ resp` and
     `memSnapshot (τ.stateAt v).reg = snap`;
   - if `rec.status = .doneUpdate resp`, then `rec.kind = .update val` (for some `val`),
     `rec.invStep < resp < t`, `τ.isWriteStep rec.caller resp`, and
     `((τ.stateAt (resp + 1)).reg rec.caller).data = val`;
   - conversely, EVERY `isWriteStep τ j w` with `w < t` has a unique `id < history.length` with
     `caller = j` and `status = .doneUpdate w`. -/
structure TraceInv (τ : SnapshotTrace ord dInit) (t : ℕ) : Prop where
  stepCount_eq : (τ.stateAt t).stepCount = t
  reg_view_valid : ∀ j w, w < t → τ.isWriteStep j w →
    ∃ v, τ.lastIdleStep j w + 1 ≤ v ∧ v ≤ w ∧
      memSnapshot (τ.stateAt v).reg = ((τ.stateAt (w + 1)).reg j).view
  proc_ready : ∀ i opId val snap,
    (τ.stateAt t).proc i = .readyToWrite opId val snap →
    ∃ (hId : opId < (τ.stateAt t).history.length),
      (τ.stateAt t).history[opId]'hId =
        ⟨i, .update val, τ.lastIdleStep i t, .pending⟩ ∧
      τ.lastIdleStep i t < t ∧
      ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ t ∧ memSnapshot (τ.stateAt v).reg = snap
  proc_scan : ∀ i st,
    (τ.stateAt t).proc i = .scanning st →
    ∃ (hId : st.opId < (τ.stateAt t).history.length),
      (τ.stateAt t).history[st.opId]'hId =
        ⟨i, match st.mode with | .external => .scan | .embedded val => .update val,
          τ.lastIdleStep i t, .pending⟩ ∧
      τ.lastIdleStep i t < t ∧
      ScanLoopInv τ (τ.lastIdleStep i t) t st
  hist_pending : ∀ id (hId : id < (τ.stateAt t).history.length),
    ((τ.stateAt t).history[id]'hId).status = .pending →
    ((τ.stateAt t).history[id]'hId).invStep =
      τ.lastIdleStep ((τ.stateAt t).history[id]'hId).caller t ∧
    ((τ.stateAt t).history[id]'hId).invStep < t ∧
      HasActiveOpId ((τ.stateAt t).proc ((τ.stateAt t).history[id]'hId).caller) id
  hist_doneScan : ∀ id (hId : id < (τ.stateAt t).history.length) resp snap,
    ((τ.stateAt t).history[id]'hId).status = .doneScan resp snap →
    ((τ.stateAt t).history[id]'hId).kind = .scan ∧
    ((τ.stateAt t).history[id]'hId).invStep < resp ∧ resp < t ∧
      ∃ v, ((τ.stateAt t).history[id]'hId).invStep + 1 ≤ v ∧ v ≤ resp ∧
        memSnapshot (τ.stateAt v).reg = snap
  hist_doneUpdate : ∀ id (hId : id < (τ.stateAt t).history.length) resp,
    ((τ.stateAt t).history[id]'hId).status = .doneUpdate resp →
    ∃ val, ((τ.stateAt t).history[id]'hId).kind = .update val ∧
      ((τ.stateAt t).history[id]'hId).invStep < resp ∧ resp < t ∧
      τ.isWriteStep ((τ.stateAt t).history[id]'hId).caller resp ∧
      (τ.stateAt (resp + 1)).reg ((τ.stateAt t).history[id]'hId).caller =
        ⟨val, ((τ.stateAt resp).reg ((τ.stateAt t).history[id]'hId).caller).seq + 1,
          ((τ.stateAt (resp + 1)).reg ((τ.stateAt t).history[id]'hId).caller).view⟩
  writeStep_in_hist : ∀ j w, w < t → τ.isWriteStep j w →
    ∃ (id : ℕ) (hId : id < (τ.stateAt t).history.length),
      ((τ.stateAt t).history[id]'hId).caller = j ∧
      ((τ.stateAt t).history[id]'hId).status = .doneUpdate w

/-- If `proc i` stays non-idle across `t → t + 1`, `lastIdleStep i` is unchanged. -/
theorem lastIdleStep_keep (τ : SnapshotTrace ord dInit) (i : P) {t : ℕ}
    (h0 : (τ.stateAt t).proc i ≠ .idle) (h1 : (τ.stateAt (t + 1)).proc i ≠ .idle) :
    τ.lastIdleStep i (t + 1) = τ.lastIdleStep i t := by
  rw [τ.lastIdleStep_eq_of_step_not_idle i h1]
  exact ite_eq_right fun hid => h0 ((ProcSnapshotState.isIdle_eq_true _).mp hid)

/-- Per-actor frame lemma for `TraceInv`: given `TraceInv τ t`, if actor `i` transitions from `t`
to `t + 1` leaving every other process `p ≠ i` unchanged and modifying `history` at most at a
single index `modId` (either `modId = history.length` for an append/no-op, or an existing pending
entry of `i`), then all frame obligations for `p ≠ i`, `id ≠ modId`, and `w < t` follow
automatically from `TraceInv τ t`. -/
theorem TraceInv.of_actor_step {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (i : P) (modId : ℕ)
    (hstepCount : (τ.stateAt (t + 1)).stepCount = t + 1)
    (hproc_other : ∀ p, p ≠ i → (τ.stateAt (t + 1)).proc p = (τ.stateAt t).proc p)
    (hhist_len : (τ.stateAt t).history.length ≤ (τ.stateAt (t + 1)).history.length)
    (hbound_unchanged : ∀ id, id < (τ.stateAt (t + 1)).history.length → id ≠ modId →
      id < (τ.stateAt t).history.length)
    (hhist_unchanged : ∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
      (h₀ : id < (τ.stateAt t).history.length), id ≠ modId →
        (τ.stateAt (t + 1)).history[id]'h₁ = (τ.stateAt t).history[id]'h₀)
    (hmod_old : ∀ (h₀ : modId < (τ.stateAt t).history.length),
      ((τ.stateAt t).history[modId]'h₀).caller = i ∧
        ((τ.stateAt t).history[modId]'h₀).status = .pending)
    (hreg_t : ∀ j, τ.isWriteStep j t →
      ∃ v, τ.lastIdleStep j t + 1 ≤ v ∧ v ≤ t ∧
        memSnapshot (τ.stateAt v).reg = ((τ.stateAt (t + 1)).reg j).view)
    (hready_i : ∀ opId val snap,
      (τ.stateAt (t + 1)).proc i = .readyToWrite opId val snap →
      ∃ (hId : opId < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[opId]'hId =
          ⟨i, .update val, τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ∃ v, τ.lastIdleStep i (t + 1) + 1 ≤ v ∧ v ≤ t + 1 ∧
          memSnapshot (τ.stateAt v).reg = snap)
    (hscan_i : ∀ st,
      (τ.stateAt (t + 1)).proc i = .scanning st →
      ∃ (hId : st.opId < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[st.opId]'hId =
          ⟨i, match st.mode with | .external => .scan | .embedded val => .update val,
            τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ScanLoopInv τ (τ.lastIdleStep i (t + 1)) (t + 1) st)
    (hpending_i : ∀ id (hId : id < (τ.stateAt (t + 1)).history.length),
      (id = modId ∨ ((τ.stateAt (t + 1)).history[id]'hId).caller = i) →
      ((τ.stateAt (t + 1)).history[id]'hId).status = .pending →
      ((τ.stateAt (t + 1)).history[id]'hId).invStep =
        τ.lastIdleStep ((τ.stateAt (t + 1)).history[id]'hId).caller (t + 1) ∧
      ((τ.stateAt (t + 1)).history[id]'hId).invStep < t + 1 ∧
        HasActiveOpId ((τ.stateAt (t + 1)).proc ((τ.stateAt (t + 1)).history[id]'hId).caller) id)
    (hdoneScan_mod : ∀ (hId : modId < (τ.stateAt (t + 1)).history.length) resp snap,
      ((τ.stateAt (t + 1)).history[modId]'hId).status = .doneScan resp snap →
      ((τ.stateAt (t + 1)).history[modId]'hId).kind = .scan ∧
      ((τ.stateAt (t + 1)).history[modId]'hId).invStep < resp ∧ resp < t + 1 ∧
        ∃ v, ((τ.stateAt (t + 1)).history[modId]'hId).invStep + 1 ≤ v ∧ v ≤ resp ∧
          memSnapshot (τ.stateAt v).reg = snap)
    (hdoneUpdate_mod : ∀ (hId : modId < (τ.stateAt (t + 1)).history.length) resp,
      ((τ.stateAt (t + 1)).history[modId]'hId).status = .doneUpdate resp →
      ∃ val, ((τ.stateAt (t + 1)).history[modId]'hId).kind = .update val ∧
        ((τ.stateAt (t + 1)).history[modId]'hId).invStep < resp ∧ resp < t + 1 ∧
        τ.isWriteStep ((τ.stateAt (t + 1)).history[modId]'hId).caller resp ∧
        (τ.stateAt (resp + 1)).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller =
          ⟨val, ((τ.stateAt resp).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller).seq + 1,
            ((τ.stateAt (resp + 1)).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller).view⟩)
    (hwrite_t : ∀ j, τ.isWriteStep j t →
      ∃ (id : ℕ) (hId : id < (τ.stateAt (t + 1)).history.length),
        ((τ.stateAt (t + 1)).history[id]'hId).caller = j ∧
        ((τ.stateAt (t + 1)).history[id]'hId).status = .doneUpdate t) :
    TraceInv τ (t + 1) where
  stepCount_eq := hstepCount
  reg_view_valid j w hw hwrite := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
    exacts [inv.reg_view_valid j w hw' hwrite, hreg_t j hwrite]
  proc_ready p opId val snap hp := by
    by_cases hpi : p = i
    · subst hpi; exact hready_i opId val snap hp
    · have hp_old : (τ.stateAt t).proc p = .readyToWrite opId val snap :=
        (hproc_other p hpi) ▸ hp
      have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
      obtain ⟨hId₀, hrec₀, hlt₀, v, hv₁, hv₂, hsnap⟩ := inv.proc_ready p opId val snap hp_old
      have hId₁ : opId < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : opId ≠ modId := by
        intro heq; subst heq
        exact hpi ((congrArg SnapshotOpRecord.caller hrec₀).symm.trans (hmod_old hId₀).1)
      refine ⟨hId₁, ?_, by omega, v, by omega, by omega, hsnap⟩
      rw [hhist_unchanged opId hId₁ hId₀ hne_mod, hkeep]; exact hrec₀
  proc_scan p st hp := by
    by_cases hpi : p = i
    · subst hpi; exact hscan_i st hp
    · have hp_old : (τ.stateAt t).proc p = .scanning st := (hproc_other p hpi) ▸ hp
      have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
      obtain ⟨hId₀, hrec₀, hlt₀, hloop⟩ := inv.proc_scan p st hp_old
      have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : st.opId ≠ modId := by
        intro heq
        have hidx : (τ.stateAt t).history[st.opId]'hId₀ =
            (τ.stateAt t).history[modId]'(heq ▸ hId₀) := _root_.getElem_congr_idx heq
        exact hpi ((congrArg SnapshotOpRecord.caller (hrec₀.symm.trans hidx)).trans
          (hmod_old (heq ▸ hId₀)).1)
      refine ⟨hId₁, ?_, by omega, hkeep ▸ hloop.mono_hi (Nat.le_succ t)⟩
      rw [hhist_unchanged st.opId hId₁ hId₀ hne_mod, hkeep]; exact hrec₀
  hist_pending id hId₁ hpend := by
    by_cases hcase : id = modId ∨ ((τ.stateAt (t + 1)).history[id]'hId₁).caller = i
    · exact hpending_i id hId₁ hcase hpend
    · push Not at hcase
      have hId₀ := hbound_unchanged id hId₁ hcase.1
      have hrec_eq := hhist_unchanged id hId₁ hId₀ hcase.1
      rw [hrec_eq] at hpend hcase ⊢
      obtain ⟨hinv, hlt₀, hact_old⟩ := inv.hist_pending id hId₀ hpend
      have hnot_old : (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId₀).caller ≠ .idle := by
        rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hp] <;> nofun
      have hproc_same := hproc_other _ hcase.2
      have hkeep := τ.lastIdleStep_keep _ hnot_old (hproc_same ▸ hnot_old)
      rw [hkeep, hproc_same]; exact ⟨hinv, by omega, hact_old⟩
  hist_doneScan id hId₁ resp snap hdone := by
    by_cases hid : id = modId
    · subst hid; exact hdoneScan_mod hId₁ resp snap hdone
    · have hId₀ := hbound_unchanged id hId₁ hid
      rw [hhist_unchanged id hId₁ hId₀ hid] at hdone ⊢
      obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hId₀ resp snap hdone
      exact ⟨hk, hi, by omega, v, hv⟩
  hist_doneUpdate id hId₁ resp hdone := by
    by_cases hid : id = modId
    · subst hid; exact hdoneUpdate_mod hId₁ resp hdone
    · have hId₀ := hbound_unchanged id hId₁ hid
      rw [hhist_unchanged id hId₁ hId₀ hid] at hdone ⊢
      obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hId₀ resp hdone
      exact ⟨val', hk, hi, by omega, hw, hd⟩
  writeStep_in_hist j w hw hwrite := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
    · obtain ⟨id, hId₀, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
      have hId₁ : id < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : id ≠ modId := by
        intro heq; subst heq
        exact absurd ((hmod_old hId₀).2.symm.trans hs) nofun
      refine ⟨id, hId₁, ?_, ?_⟩ <;> rw [hhist_unchanged id hId₁ hId₀ hne_mod] <;> assumption
    · exact hwrite_t j hwrite

end SnapshotTrace

end Cslib.Distributed.SetAgreement
