/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Machine

/-!
# Internal history-update and single-step inversion lemmas

Internal transition inversion helpers (`SnapshotEvent.actor`, `stepSnapshot_effect`,
`getElem_completeHistoryAt_ne`) shared by `WaitFree`, `TraceWrites`, `TraceSteps`,
`LinearizationChunks`, and `TracePreservation`; never re-exported through `AtomicSnapshot`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotEvent.actor`: process performing a `SnapshotEvent`.

## Main results

* `Cslib.Distributed.SetAgreement.length_completeHistoryAt`,
  `Cslib.Distributed.SetAgreement.getElem_completeHistoryAt_ne`: history update preservation.
* `Cslib.Distributed.SetAgreement.stepSnapshot_invokeScan_eq`,
  `Cslib.Distributed.SetAgreement.stepSnapshot_invokeUpdate_eq`,
  `Cslib.Distributed.SetAgreement.stepSnapshot_effect`: transition inversion lemmas.
-/

public section

namespace Cslib.Distributed.SetAgreement

/-- Length preservation for `completeHistoryAt`. -/
@[simp]
theorem length_completeHistoryAt {P Data : Type*} (hist : List (SnapshotOpRecord P Data))
    (opId : ℕ) (st : SnapshotOpStatus P Data) :
    (completeHistoryAt hist opId st).length = hist.length := by
  unfold completeHistoryAt
  cases hist[opId]? with
  | none => rfl
  | some _ => exact List.length_set

/-- Updating entry `opId` via `completeHistoryAt` leaves every entry `k ≠ opId` unchanged. -/
theorem getElem_completeHistoryAt_ne {P Data : Type*}
    {hist : List (SnapshotOpRecord P Data)} {opId k : ℕ} {newSt : SnapshotOpStatus P Data}
    (hne : k ≠ opId) (hk : k < (completeHistoryAt hist opId newSt).length) :
    (completeHistoryAt hist opId newSt)[k]'hk =
      hist[k]'((length_completeHistoryAt hist opId newSt) ▸ hk) := by
  have hk₀ : k < hist.length := (length_completeHistoryAt hist opId newSt) ▸ hk
  suffices ∀ ys, completeHistoryAt hist opId newSt = ys →
      ∀ (hy : k < ys.length), ys[k]'hy = hist[k]'hk₀ from this _ rfl hk
  intro ys hys hy
  subst hys
  by_cases hop : opId < hist.length
  · simp only [completeHistoryAt, List.getElem?_eq_getElem hop, List.getElem_set_ne (Ne.symm hne)]
  · simp only [completeHistoryAt, List.getElem?_eq_none (Nat.le_of_not_lt hop)]

/-- Acting process identifier for any `SnapshotEvent`. -/
@[expose]
def SnapshotEvent.actor {P Data : Type*} : SnapshotEvent P Data → P
  | .invokeScan j | .invokeUpdate j _ | .step j => j

/-- Inversion characterization of a `.invokeScan` transition in `stepSnapshot`. -/
theorem stepSnapshot_invokeScan_eq {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.invokeScan i) = some s') :
    s.proc i = .idle ∧
      (let opId := s.history.length
       let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
       let st : ActiveScan P Data := ⟨.external, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
       ({ s with
           proc := Function.update s.proc i (.scanning st)
           history := s.history ++ [⟨i, .scan, s.stepCount, .pending⟩]
           stepCount := s.stepCount + 1 } : SnapshotState P Data) = s') := by
  unfold stepSnapshot at h
  cases hpi : s.proc i <;> simp only [hpi, Option.some.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

/-- Inversion characterization of a `.invokeUpdate` transition in `stepSnapshot`. -/
theorem stepSnapshot_invokeUpdate_eq {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {i : P} {val : Data}
    (h : stepSnapshot ord dInit s (.invokeUpdate i val) = some s') :
    s.proc i = .idle ∧
      (let opId := s.history.length
       let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
       let st : ActiveScan P Data := ⟨.embedded val, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
       ({ s with
           proc := Function.update s.proc i (.scanning st)
           history := s.history ++ [⟨i, .update val, s.stepCount, .pending⟩]
           stepCount := s.stepCount + 1 } : SnapshotState P Data) = s') := by
  unfold stepSnapshot at h
  cases hpi : s.proc i <;> simp only [hpi, Option.some.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

/-- Every transition `stepSnapshot ord dInit s ev = some s'` updates `proc` only at `ev.actor`,
and either performs a `readyToWrite` register write or leaves `s.reg` unchanged while modifying
`s.history` by at most appending a `.pending` record or completing a `.scan` record. -/
theorem stepSnapshot_effect {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data}
    (h : stepSnapshot ord dInit s ev = some s') :
    (∃ ps, s'.proc = Function.update s.proc ev.actor ps) ∧
      ((∃ j opId val snap,
          ev = .step j ∧
          s.proc j = .readyToWrite opId val snap ∧
          s' = { reg := Function.update s.reg j ⟨val, (s.reg j).seq + 1, snap⟩
                 proc := Function.update s.proc j .idle
                 history := completeHistoryAt s.history opId (.doneUpdate s.stepCount)
                 stepCount := s.stepCount + 1 }) ∨
        ((¬∃ j opId val snap, ev = .step j ∧ s.proc j = .readyToWrite opId val snap) ∧
          s'.reg = s.reg ∧
          (s'.history = s.history ∨
            (∃ rec, rec.status = .pending ∧ s'.history = s.history ++ [rec]) ∨
            (∃ j st snap, ev = .step j ∧ s.proc j = .scanning st ∧ st.mode = .external ∧
              s'.history =
                completeHistoryAt s.history st.opId (.doneScan s.stepCount snap))))) := by
  have finishScan_eff : ∀ {j : P} {st : ActiveScan P Data} (snap : P → Data)
      (hscan : s.proc j = .scanning st) (hfin : finishScan s j st.mode st.opId snap = s'),
      (∃ ps, s'.proc = Function.update s.proc j ps) ∧
        s'.reg = s.reg ∧
        (s'.history = s.history ∨
          (∃ rec, rec.status = .pending ∧ s'.history = s.history ++ [rec]) ∨
          (∃ j' st' snap', SnapshotEvent.step (Data := Data) j = .step j' ∧
            s.proc j' = .scanning st' ∧ st'.mode = .external ∧
            s'.history = completeHistoryAt s.history st'.opId (.doneScan s.stepCount snap'))) := by
    intro j st snap hscan hfin
    subst hfin
    cases hm : st.mode with
    | external =>
      exact ⟨⟨.idle, rfl⟩, rfl, Or.inr (Or.inr ⟨j, st, snap, rfl, hscan, hm, rfl⟩)⟩
    | embedded val =>
      exact ⟨⟨.readyToWrite st.opId val snap, rfl⟩, rfl, Or.inl rfl⟩
  rcases ev with j | ⟨j, val⟩ | j
  iterate 2
    first
    | obtain ⟨-, rfl⟩ := stepSnapshot_invokeScan_eq h
    | obtain ⟨-, rfl⟩ := stepSnapshot_invokeUpdate_eq h
    exact ⟨⟨_, rfl⟩, Or.inr ⟨(by rintro ⟨_, _, _, _, h1, _⟩; cases h1), rfl,
      Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩⟩
  · unfold stepSnapshot at h
    cases hpj : s.proc j with
    | idle => simp only [hpj] at h; nomatch h
    | readyToWrite opId val snap =>
      simp only [hpj, Option.some.injEq] at h
      subst h
      exact ⟨⟨.idle, rfl⟩, Or.inl ⟨j, opId, val, snap, rfl, hpj, rfl⟩⟩
    | scanning st =>
      simp only [hpj] at h
      have hnw : ¬∃ j' opId val snap,
          SnapshotEvent.step (Data := Data) j = .step j' ∧
            s.proc j' = .readyToWrite opId val snap := by
        rintro ⟨_, _, _, _, h1, h2⟩; cases h1; rw [hpj] at h2; cases h2
      cases hph : st.phase <;> cases hrem : st.rem <;> simp only [hph, hrem] at h
      all_goals try
        (injection h with hs'; subst hs'; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩)
      split_ifs at h with hclean
      · injection h with hs'
        obtain ⟨hp, hr, hh⟩ := finishScan_eff _ hpj hs'
        exact ⟨hp, Or.inr ⟨hnw, hr, hh⟩⟩
      · cases hfind : (ord.elems.find? fun k =>
            decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
          simp only [hfind, Option.some.injEq] at h
        · subst h; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩
        · obtain ⟨hp, hr, hh⟩ := finishScan_eff _ hpj h
          exact ⟨hp, Or.inr ⟨hnw, hr, hh⟩⟩

end Cslib.Distributed.SetAgreement
