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
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceInv
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.StepFacts

/-!
# Internal transition-kind specializations of `TraceInv`

Specializes `TraceInv.of_actor_step` to invocation (`of_invoke`), local active scan steps
(`of_local_active`), and operation completion (`of_complete`); never re-exported through
`AtomicSnapshot`.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.TraceInv.of_invoke`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.TraceInv.of_local_active`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.TraceInv.of_complete`: frame specializations.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Specialization of `TraceInv.of_actor_step` for `.invokeScan i` and `.invokeUpdate i val`. -/
theorem TraceInv.of_invoke {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (i : P) (mode : ScanMode Data)
    (hpi : (τ.stateAt t).proc i = .idle)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    (hs₁ :
      let opId := (τ.stateAt t).history.length
      let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
      let st : ActiveScan P Data := ⟨mode, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
      let kind := match mode with | .external => .scan | .embedded v => .update v
      ({ reg := (τ.stateAt t).reg
         proc := Function.update (τ.stateAt t).proc i (.scanning st)
         history := (τ.stateAt t).history ++ [⟨i, kind, (τ.stateAt t).stepCount, .pending⟩]
         stepCount := (τ.stateAt t).stepCount + 1 } : SnapshotState P Data) =
        τ.stateAt (t + 1)) :
    TraceInv τ (t + 1) := by
  let kind : SnapshotOpKind Data := match mode with | .external => .scan | .embedded v => .update v
  let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
  let st_new : ActiveScan P Data :=
    ⟨mode, (τ.stateAt t).history.length, ∅, .collectA, ord.elems, dummy, dummy⟩
  have hlast_i : τ.lastIdleStep i (t + 1) = t := by
    have hnot : (τ.stateAt (t + 1)).proc i ≠ .idle := by
      rw [← hs₁]; simp only [Function.update_self]; nofun
    rw [τ.lastIdleStep_eq_of_step_not_idle i hnot, (ProcSnapshotState.isIdle_eq_true _).mpr hpi]
    simp only [↓reduceIte]
  have hhist_eq : (τ.stateAt (t + 1)).history =
      (τ.stateAt t).history ++ [⟨i, kind, t, .pending⟩] := by
    rw [← hs₁, inv.stepCount_eq]; cases mode <;> rfl
  have hlen1 : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length + 1 := by
    rw [hhist_eq, List.length_append, List.length_singleton]
  have hget_new : ∀ hId : (τ.stateAt t).history.length < (τ.stateAt (t + 1)).history.length,
      (τ.stateAt (t + 1)).history[(τ.stateAt t).history.length]'hId = ⟨i, kind, t, .pending⟩ := by
    intro hId
    rw [List.getElem_of_eq hhist_eq hId]
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]
  refine inv.of_actor_step i (τ.stateAt t).history.length
    (by rw [← hs₁, inv.stepCount_eq])
    (fun p hp => by rw [← hs₁]; exact Function.update_of_ne hp _ _)
    (by omega)
    (fun id h₁ hne => by omega)
    (fun id h₁ h₀ _ => by
      rw [List.getElem_of_eq hhist_eq h₁, List.getElem_append_left h₀])
    (fun h₀ => absurd h₀ (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
    (fun _ _ _ hp => by rw [← hs₁] at hp; simp only [Function.update_self] at hp; cases hp)
    ?_ ?_
    (fun hId _ _ hdone => by rw [hget_new hId] at hdone; cases hdone)
    (fun hId _ hdone => by rw [hget_new hId] at hdone; cases hdone)
    (fun j hw => absurd ⟨j, hw⟩ hnow)
  · intro st hp
    rw [← hs₁] at hp
    simp only [Function.update_self, ProcSnapshotState.scanning.injEq] at hp
    subst hp
    dsimp only [st_new]
    refine ⟨by omega, ?_, by omega, t + 1, by omega, le_rfl,
      fun k hk => absurd hk (notMem_empty k),
      fun _ k hk => absurd (ord.complete k) hk, fun hph => by cases hph⟩
    rw [hget_new (by omega), hlast_i]; cases mode <;> rfl
  · intro id hId hcase hpend
    by_cases hid : id = (τ.stateAt t).history.length
    · subst hid
      simp only [hget_new hId, hlast_i, Nat.lt_succ_self, true_and]
      exact Or.inl ⟨st_new, by rw [← hs₁]; exact Function.update_self _ _ _, rfl⟩
    · have hId₀ : id < (τ.stateAt t).history.length := by omega
      have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId = (τ.stateAt t).history[id]'hId₀ := by
        rw [List.getElem_of_eq hhist_eq hId, List.getElem_append_left hId₀]
      have hci : ((τ.stateAt t).history[id]'hId₀).caller = i := hrec_eq ▸ hcase.resolve_left hid
      rw [hrec_eq] at hpend
      obtain ⟨-, -, hact_old⟩ := inv.hist_pending id hId₀ hpend
      rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hci, hpi] at hp <;> cases hp

/-- Specialization of `TraceInv.of_actor_step` when active scan `st` of `i` transitions to a
non-idle local state `ps_new` without modifying `reg` or `history`. -/
theorem TraceInv.of_local_active {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {st : ActiveScan P Data}
    (hpi : (τ.stateAt t).proc i = .scanning st)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    (ps_new : ProcSnapshotState P Data) (hps_ne : ps_new ≠ .idle)
    (hs_eq : { (τ.stateAt t) with
                proc := Function.update (τ.stateAt t).proc i ps_new
                stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1))
    (hact_new : HasActiveOpId ps_new st.opId)
    (hready_i : ∀ id' v' sn', ps_new = .readyToWrite id' v' sn' →
      id' = st.opId ∧ st.mode = .embedded v' ∧
        ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ t + 1 ∧ memSnapshot (τ.stateAt v).reg = sn')
    (hscan_i : ∀ st', ps_new = .scanning st' →
      st'.opId = st.opId ∧ st'.mode = st.mode ∧
        ScanLoopInv τ (τ.lastIdleStep i t) (t + 1) st') :
    TraceInv τ (t + 1) := by
  obtain ⟨hId, hrec_i, hlt_t, _⟩ := inv.proc_scan i st hpi
  have hhist_eq : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs_eq]
  have hpi_new : (τ.stateAt (t + 1)).proc i = ps_new := by
    rw [← hs_eq]; exact Function.update_self _ _ _
  have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) (hpi_new ▸ hps_ne)
  refine inv.of_actor_step i (τ.stateAt t).history.length
    (by rw [← hs_eq, inv.stepCount_eq])
    (fun p hp => by rw [← hs_eq]; exact Function.update_of_ne hp _ _)
    (by rw [hhist_eq])
    (fun id h₁ _ => hhist_eq ▸ h₁)
    (fun id h₁ h₀ _ => List.getElem_of_eq hhist_eq h₁)
    (fun h₀ => absurd h₀ (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
    (fun id' v' sn' hp => by
      obtain ⟨rfl, hmode, hsnap⟩ := hready_i id' v' sn' (hpi_new ▸ hp)
      have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId
      refine ⟨hId₁, ?_, by omega, hkeep ▸ hsnap⟩
      rw [List.getElem_of_eq hhist_eq hId₁, hrec_i, hmode, hkeep])
    (fun st' hp => by
      obtain ⟨hop, hmode, hloop⟩ := hscan_i st' (hpi_new ▸ hp)
      have hId₁ : st'.opId < (τ.stateAt (t + 1)).history.length := by
        rw [hhist_eq, hop]; exact hId
      refine ⟨hId₁, ?_, by omega, hkeep ▸ hloop⟩
      rw [List.getElem_of_eq hhist_eq hId₁, _root_.getElem_congr_idx hop, hrec_i, hmode, hkeep])
    ?_
    (fun h₁ => absurd (hhist_eq ▸ h₁) (lt_irrefl _))
    (fun h₁ => absurd (hhist_eq ▸ h₁) (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
  intro id hId₁ hcase hpend
  have hId₀ : id < (τ.stateAt t).history.length := hhist_eq ▸ hId₁
  have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId₁ = (τ.stateAt t).history[id]'hId₀ :=
    List.getElem_of_eq hhist_eq hId₁
  have hci : ((τ.stateAt t).history[id]'hId₀).caller = i :=
    hrec_eq ▸ hcase.resolve_left (Nat.ne_of_lt hId₀)
  rw [hrec_eq] at hpend ⊢
  obtain ⟨hinv, hlt₀, hact_old⟩ := inv.hist_pending id hId₀ hpend
  have hid_eq : id = st.opId :=
    active_opId_unique (hci ▸ hact_old) (Or.inl ⟨st, hpi, rfl⟩)
  subst id
  rw [hci] at hinv ⊢
  rw [hkeep, hpi_new]
  exact ⟨hinv, by omega, hact_new⟩

/-- Specialization of `TraceInv.of_actor_step` when active operation `activeId` of `i` completes
(`newSt ≠ .pending`) and `proc i` returns to `.idle`. -/
theorem TraceInv.of_complete {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {activeId : ℕ} (hId : activeId < (τ.stateAt t).history.length)
    (oldKind : SnapshotOpKind Data) (newSt : SnapshotOpStatus P Data) (hnew_ne : newSt ≠ .pending)
    (hrec_i : (τ.stateAt t).history[activeId]'hId = ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩)
    (hact_i : HasActiveOpId ((τ.stateAt t).proc i) activeId)
    (hstepCount : (τ.stateAt (t + 1)).stepCount = t + 1)
    (hproc_eq : (τ.stateAt (t + 1)).proc = Function.update (τ.stateAt t).proc i .idle)
    (hhist_upd : (τ.stateAt (t + 1)).history =
      completeHistoryAt (τ.stateAt t).history activeId newSt)
    (hreg_t : ∀ j, τ.isWriteStep j t →
      ∃ v, τ.lastIdleStep j t + 1 ≤ v ∧ v ≤ t ∧
        memSnapshot (τ.stateAt v).reg = ((τ.stateAt (t + 1)).reg j).view)
    (hdoneScan_new : ∀ resp snap, newSt = .doneScan resp snap →
      oldKind = .scan ∧ τ.lastIdleStep i t < resp ∧ resp < t + 1 ∧
        ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap)
    (hdoneUpdate_new : ∀ resp, newSt = .doneUpdate resp →
      ∃ val, oldKind = .update val ∧ τ.lastIdleStep i t < resp ∧ resp < t + 1 ∧
        τ.isWriteStep i resp ∧
        (τ.stateAt (resp + 1)).reg i =
          ⟨val, ((τ.stateAt resp).reg i).seq + 1, ((τ.stateAt (resp + 1)).reg i).view⟩)
    (hwrite_t : ∀ j, τ.isWriteStep j t → j = i ∧ newSt = .doneUpdate t) :
    TraceInv τ (t + 1) := by
  have hget_op : (τ.stateAt t).history[activeId]? =
      some ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩ := by
    rw [List.getElem?_eq_getElem hId, hrec_i]
  have hset : (τ.stateAt (t + 1)).history =
      (τ.stateAt t).history.set activeId ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩ := by
    rw [hhist_upd]; simp only [completeHistoryAt, hget_op]
  have hlen_eq : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length := by
    rw [hset, List.length_set]
  have hnew_at : ∀ h₁ : activeId < (τ.stateAt (t + 1)).history.length,
      (τ.stateAt (t + 1)).history[activeId]'h₁ = ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩ :=
    fun h₁ => (List.getElem_of_eq hset h₁).trans (List.getElem_set_self _)
  have hunch : ∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
      (h₀ : id < (τ.stateAt t).history.length), id ≠ activeId →
      (τ.stateAt (t + 1)).history[id]'h₁ = (τ.stateAt t).history[id]'h₀ :=
    fun id h₁ _ hne => (List.getElem_of_eq hset h₁).trans (List.getElem_set_ne (Ne.symm hne) _)
  refine inv.of_actor_step i activeId hstepCount
    (fun p hp => by rw [hproc_eq, Function.update_of_ne hp])
    (by omega)
    (fun id h₁ _ => hlen_eq ▸ h₁)
    hunch
    (fun h₀ => by rw [hrec_i]; exact ⟨rfl, rfl⟩)
    hreg_t
    (fun _ _ _ hp => by rw [hproc_eq, Function.update_self] at hp; cases hp)
    (fun _ hp => by rw [hproc_eq, Function.update_self] at hp; cases hp)
    ?_
    (fun h₁ resp snap hdone => by rw [hnew_at h₁] at hdone ⊢; exact hdoneScan_new resp snap hdone)
    (fun h₁ resp hdone => by rw [hnew_at h₁] at hdone ⊢; exact hdoneUpdate_new resp hdone)
    (fun j hw => by
      obtain ⟨rfl, hst⟩ := hwrite_t j hw
      have h₁ : activeId < (τ.stateAt (t + 1)).history.length := hlen_eq.symm ▸ hId
      exact ⟨activeId, h₁, by rw [hnew_at h₁], by rw [hnew_at h₁]; exact hst⟩)
  intro id hId₁ hcase hpend
  by_cases hid : id = activeId
  · subst hid; rw [hnew_at hId₁] at hpend; exact absurd hpend hnew_ne
  · have hId₀ : id < (τ.stateAt t).history.length := hlen_eq ▸ hId₁
    have hrec_eq := hunch id hId₁ hId₀ hid
    have hci : ((τ.stateAt t).history[id]'hId₀).caller = i := hrec_eq ▸ hcase.resolve_left hid
    rw [hrec_eq] at hpend
    obtain ⟨-, -, hact_old⟩ := inv.hist_pending id hId₀ hpend
    exact absurd (active_opId_unique (hci ▸ hact_old) hact_i) hid

end SnapshotTrace

end Cslib.Distributed.SetAgreement
