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
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.CleanCollect
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceSteps

/-!
# Internal inductive preservation of `TraceInv`

Proves `traceInv_holds` for every prefix of a `SnapshotTrace` via clean double collects
(`Lemma 3.1`), twice-moved borrowed views (`Lemma 3.2`), and atomic register writes; never
re-exported through `AtomicSnapshot`.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.traceInv_holds`: inductive proof of `TraceInv`.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-! ### Inductive preservation of `TraceInv` (`Lemmas 3.2–3.3`) -/

/-- A clean double collect (`∀ k, (collectAVal k).seq = (collectBVal k).seq`) returns the
instantaneous memory state `memSnapshot (τ.stateAt u).reg` at the midpoint `u` between `collectA`
and `collectB` (after Lemma 3.1 of [AfekAttiyaDolevGafniMerrittShavit1993]). -/
private theorem clean_double_collect_memSnapshot (τ : SnapshotTrace ord dInit)
    {st : ActiveScan P Data} {iterS u t : ℕ} (ht : t ≤ τ.events.length)
    (ha_all : ∀ k, ∃ tA, iterS ≤ tA ∧ tA ≤ u ∧ st.collectAVal k = (τ.stateAt tA).reg k)
    (hb_all : ∀ k, ∃ tB, u ≤ tB ∧ tB ≤ t ∧ st.collectBVal k = (τ.stateAt tB).reg k)
    (hclean : ∀ k, (st.collectAVal k).seq = (st.collectBVal k).seq) :
    memSnapshot (τ.stateAt u).reg = fun k => (st.collectBVal k).data := by
  choose tA _ htA₂ htA_eq using ha_all
  choose tB htB₁ htB₂ htB_eq using hb_all
  have hseq_eq : ∀ k, ((τ.stateAt (tA k)).reg k).seq = ((τ.stateAt (tB k)).reg k).seq :=
    fun k => by rw [← htA_eq k, ← htB_eq k]; exact hclean k
  have h31 := τ.memSnapshot_eq_of_clean_double_collect htA₂ le_rfl htB₁
    (fun k => le_trans (htB₂ k) ht) hseq_eq le_rfl le_rfl
  rw [h31]; funext k; rw [htB_eq k]

/-- Borrowed-view validity (after Lemma 3.2 of [AfekAttiyaDolevGafniMerrittShavit1993]): if
updater `k` wrote at `w₁ ∈ [lo + 1, iterS)` during an earlier double collect and its register
sequence number changed between `collectA` (`tA ∈ [iterS, u]`) and `collectB` (`tB ∈ [u, t]`), then
`(st.collectBVal k).view` equals `memSnapshot (τ.stateAt v).reg` for some `v ∈ [lo + 1, t]`. -/
private theorem borrowed_view_memSnapshot {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (ht : t ≤ τ.events.length)
    {lo iterS u w₁ : ℕ} {st : ActiveScan P Data} {k : P}
    (hw₁_lo : lo + 1 ≤ w₁) (hw₁_hi : w₁ < iterS) (hw₁_write : τ.isWriteStep k w₁)
    (ha_k : ∃ tA, iterS ≤ tA ∧ tA ≤ u ∧ st.collectAVal k = (τ.stateAt tA).reg k)
    (hb_k : ∃ tB, u ≤ tB ∧ tB ≤ t ∧ st.collectBVal k = (τ.stateAt tB).reg k)
    (hne : (st.collectAVal k).seq ≠ (st.collectBVal k).seq) :
    ∃ v, lo + 1 ≤ v ∧ v ≤ t ∧ memSnapshot (τ.stateAt v).reg = (st.collectBVal k).view := by
  obtain ⟨tA, htA₁, htA₂, htA_eq⟩ := ha_k
  obtain ⟨tB, htB₁, htB₂, htB_eq⟩ := hb_k
  have hseq_ne : ((τ.stateAt tA).reg k).seq ≠ ((τ.stateAt tB).reg k).seq := by
    rwa [htA_eq, htB_eq] at hne
  obtain ⟨w₂, hw₂_lo, hw₂_hi, hw₂_write⟩ :=
    τ.exists_writeStep_of_seq_ne k (le_trans htA₂ htB₁) (le_trans htB₂ ht) hseq_ne
  -- A write occurred at `w₂ < tB`, so `((τ.stateAt tB).reg k).seq > 0`.
  have hpos : 0 < ((τ.stateAt tB).reg k).seq := by
    rcases τ.reg_step_iff (t := w₂) k (by omega) with
        ⟨-, hnw⟩ | ⟨_, _, _, -, -, hreg', -⟩
    · exact absurd hw₂_write hnw
    · have hmono := (τ.seq_mono_and_const_of_eq (t₁ := w₂ + 1) k hw₂_hi
        (le_trans htB₂ ht)).1
      have hseq_w₂ : ((τ.stateAt (w₂ + 1)).reg k).seq =
          ((τ.stateAt w₂).reg k).seq + 1 := by rw [hreg']
      omega
  obtain ⟨w_star, hw_star_lt, hw_star_write, hw_star_reg, hnow_after⟩ :=
    τ.exists_last_writeStep_of_seq_pos k (le_trans htB₂ ht) hpos
  have hw₂_le_star : w₂ ≤ w_star :=
    by_contra fun _ => hnow_after w₂ (by omega) hw₂_hi hw₂_write
  -- After its earlier write `w₁`, process `k` returned to `.idle` before `w_star`, so the
  -- `update_k` writing at `w_star` started strictly after `w₁` (inside `[lo + 1, t]`).
  have hidle_w₁ : (τ.stateAt (w₁ + 1)).proc k = .idle := by
    rcases τ.reg_step_iff (t := w₁) k (by omega) with
        ⟨-, hnw⟩ | ⟨_, _, _, -, -, -, hidle'⟩
    exacts [absurd hw₁_write hnw, hidle']
  have hlast_ge : w₁ + 1 ≤ τ.lastIdleStep k w_star :=
    τ.le_lastIdleStep_of_idle k (by omega) hidle_w₁
  obtain ⟨v_k, hv_k_lo, hv_k_hi, hv_k_snap⟩ :=
    inv.reg_view_valid k w_star (by omega) hw_star_write
  exact ⟨v_k, by omega, by omega, hv_k_snap.trans (by rw [htB_eq, hw_star_reg])⟩

/-- Finishing a scan (`finishScan`) with an interval-valid `snap` preserves `TraceInv`. -/
private theorem TraceInv.of_finishScan {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {st : ActiveScan P Data}
    (hpi : (τ.stateAt t).proc i = .scanning st)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    (snap : P → Data)
    (hsnap : ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ t ∧ memSnapshot (τ.stateAt v).reg = snap)
    (hfin : finishScan (τ.stateAt t) i st.mode st.opId snap = τ.stateAt (t + 1)) :
    TraceInv τ (t + 1) := by
  obtain ⟨hId, hrec_i, hlt_t, _⟩ := inv.proc_scan i st hpi
  obtain ⟨v_snap, hv₁, hv₂, hsnap_eq⟩ := hsnap
  cases hm : st.mode with
  | embedded val =>
    rw [hm] at hfin
    unfold finishScan at hfin
    exact inv.of_local_active hpi hnow (.readyToWrite st.opId val snap) nofun hfin
      (Or.inr ⟨val, snap, rfl⟩)
      (fun _ _ _ heq => by
        injection heq with h1 h2 h3; subst h1 h2 h3
        exact ⟨rfl, hm, v_snap, hv₁, by omega, hsnap_eq⟩)
      (fun _ h => nomatch h)
  | external =>
    rw [hm] at hfin hrec_i
    unfold finishScan at hfin
    exact inv.of_complete hId .scan (.doneScan t snap) nofun hrec_i
      (Or.inl ⟨st, hpi, rfl⟩)
      (by rw [← hfin, inv.stepCount_eq])
      (by rw [← hfin])
      (by rw [← hfin, inv.stepCount_eq])
      (fun j hw => absurd ⟨j, hw⟩ hnow)
      (fun resp sn hdone => by
        injection hdone with hresp hsn; subst hresp hsn
        exact ⟨rfl, hlt_t, Nat.lt_succ_self t, v_snap, hv₁, hv₂, hsnap_eq⟩)
      (fun _ h => nomatch h)
      (fun j hw => absurd ⟨j, hw⟩ hnow)

/-- Advancing an active scan to `st_next` (same `opId` and `mode`, unchanged history) preserves
`TraceInv`. -/
private theorem TraceInv.of_continueScan {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {st : ActiveScan P Data}
    (hpi : (τ.stateAt t).proc i = .scanning st)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    {st_next : ActiveScan P Data}
    (hs_eq : { (τ.stateAt t) with
                proc := Function.update (τ.stateAt t).proc i (.scanning st_next)
                stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1))
    (hop_eq : st_next.opId = st.opId) (hmode_eq : st_next.mode = st.mode)
    (hnext : ScanLoopInv τ (τ.lastIdleStep i t) (t + 1) st_next) :
    TraceInv τ (t + 1) :=
  inv.of_local_active hpi hnow (.scanning st_next) nofun hs_eq
    (Or.inl ⟨st_next, rfl, hop_eq⟩) (fun _ _ _ h => nomatch h)
    fun _ heq => by injection heq with h1; subst h1; exact ⟨hop_eq, hmode_eq, hnext⟩

/-- Single-writer atomic register write (`readyToWrite → idle`) preserves `TraceInv`. -/
private theorem TraceInv.of_writeStep {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (ht_lt : t < τ.events.length) {i : P}
    {opId : ℕ} {val : Data} {snap : P → Data}
    (hev : τ.events[t]'ht_lt = .step i)
    (hpi : (τ.stateAt t).proc i = .readyToWrite opId val snap)
    (hstep :
      { reg := Function.update (τ.stateAt t).reg i ⟨val, ((τ.stateAt t).reg i).seq + 1, snap⟩
        proc := Function.update (τ.stateAt t).proc i .idle
        history := completeHistoryAt (τ.stateAt t).history opId
          (.doneUpdate (τ.stateAt t).stepCount)
        stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1)) :
    TraceInv τ (t + 1) := by
  obtain ⟨hId, hrec_i, hlt_t, v_snap, hv₁, hv₂, hsnap_eq⟩ := inv.proc_ready i opId val snap hpi
  have hji_of_write : ∀ {j}, τ.isWriteStep j t → j = i := by
    rintro j ⟨_, _, _, _, h1, _⟩
    exact SnapshotEvent.step.inj (h1.symm.trans hev)
  exact inv.of_complete hId (.update val) (.doneUpdate t) nofun hrec_i
    (Or.inr ⟨val, snap, hpi⟩)
    (by rw [← hstep, inv.stepCount_eq])
    (by rw [← hstep])
    (by rw [← hstep, inv.stepCount_eq])
    (fun j hw => by
      obtain rfl := hji_of_write hw
      exact ⟨v_snap, hv₁, hv₂, hsnap_eq.trans (by simp only [← hstep, Function.update_self])⟩)
    (fun _ _ h => nomatch h)
    (fun resp hdone => by
      injection hdone with hresp; subst hresp
      refine ⟨val, rfl, hlt_t, Nat.lt_succ_self t, ⟨ht_lt, opId, val, snap, hev, hpi⟩, ?_⟩
      simp only [← hstep, Function.update_self])
    (fun j hw => ⟨hji_of_write hw, rfl⟩)

/-- One atomic `.step i` of a process executing an active `scan` preserves `TraceInv`. -/
private theorem TraceInv.of_scanning {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (ht_lt : t < τ.events.length) {i : P} {st : ActiveScan P Data}
    (hev : τ.events[t]'ht_lt = .step i)
    (hpi : (τ.stateAt t).proc i = .scanning st)
    (hstep : stepSnapshot ord dInit (τ.stateAt t) (.step i) = some (τ.stateAt (t + 1))) :
    TraceInv τ (t + 1) := by
  have ht_le : t ≤ τ.events.length := Nat.le_of_lt ht_lt
  have hnow : ¬∃ j, τ.isWriteStep j t := by
    rintro ⟨j, _, _, _, _, h1, h2⟩
    rw [hev] at h1; injection h1 with hji; subst hji
    rw [hpi] at h2; cases h2
  obtain ⟨-, -, -, hloop⟩ := inv.proc_scan i st hpi
  unfold stepSnapshot at hstep
  simp only [hpi] at hstep
  cases hph : st.phase with
  | collectA =>
    cases hrem : st.rem <;> simp only [hph, hrem, Option.some.injEq] at hstep
    · exact inv.of_continueScan hpi hnow hstep rfl rfl (hloop.finishA hph hrem)
    · exact inv.of_continueScan hpi hnow hstep rfl rfl (hloop.readA hph hrem)
  | collectB =>
    cases hrem : st.rem with
    | cons j rest =>
      simp only [hph, hrem, Option.some.injEq] at hstep
      exact inv.of_continueScan hpi hnow hstep rfl rfl (hloop.readB hph hrem)
    | nil =>
      simp only [hph, hrem] at hstep
      have hloop_copy := hloop
      obtain ⟨iterS, hi₁, _, hmov, _, hcB⟩ := hloop
      obtain ⟨u, hu₁, hu₂, ha_all, hb_rem⟩ := hcB hph
      have hb_all : ∀ k, ∃ tB, u ≤ tB ∧ tB ≤ t ∧ st.collectBVal k = (τ.stateAt tB).reg k :=
        fun k => hb_rem k (by simp only [hrem, List.not_mem_nil, not_false_eq_true])
      split_ifs at hstep with hclean
      · -- Clean double collect (`Lemma 3.1`): serialize at midpoint `u`.
        injection hstep with hs₁
        exact inv.of_finishScan hpi hnow _
          ⟨u, le_trans hi₁ hu₁, hu₂,
            τ.clean_double_collect_memSnapshot ht_le ha_all hb_all hclean⟩ hs₁
      · cases hfind : (ord.elems.find? fun k =>
            decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
        | some k =>
          -- Process `k` moved twice (`Lemma 3.2`): borrow `(st.collectBVal k).view`.
          simp only [hfind, Option.some.injEq] at hstep
          have hk_bool := List.find?_some hfind
          have hk_pred : (st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved :=
            of_decide_eq_true hk_bool
          obtain ⟨w₁, hw₁_lo, hw₁_hi, hw₁_write⟩ := hmov k hk_pred.2
          exact inv.of_finishScan hpi hnow _
            (borrowed_view_memSnapshot inv ht_le hw₁_lo hw₁_hi hw₁_write
              (ha_all k) (hb_all k) hk_pred.1) hstep
        | none =>
          -- Unsuccessful collect without repeat mover: record `changed` and restart.
          simp only [hfind, Option.some.injEq] at hstep
          exact inv.of_continueScan hpi hnow hstep rfl rfl (hloop_copy.restart ht_le hph hrem)

/-- Key inductive proof of `TraceInv τ t` for every `t ≤ τ.events.length`. -/
theorem traceInv_holds (τ : SnapshotTrace ord dInit) :
    ∀ t ≤ τ.events.length, TraceInv τ t := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨by simp only [stateAt_zero, SnapshotState.init], fun _ w hw => by omega, ?_, ?_, ?_, ?_,
      ?_, fun _ w hw => by omega⟩
    · intro i _ _ _ hp; rw [stateAt_zero] at hp; cases hp
    · intro i _ hp; rw [stateAt_zero] at hp; cases hp
    all_goals intro id hId; rw [stateAt_zero] at hId; cases hId
  | succ t ih =>
    have ht_lt : t < τ.events.length := Nat.lt_of_succ_le ht
    have inv := ih (Nat.le_of_succ_le ht)
    have hstep := τ.stateAt_step ht_lt
    rcases hev : τ.events[t] with i | ⟨i, val⟩ | i
    · rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeScan_eq hstep
      exact inv.of_invoke i .external hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeUpdate_eq hstep
      exact inv.of_invoke i (.embedded val) hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · rw [hev] at hstep
      cases hpi : (τ.stateAt t).proc i with
      | idle => unfold stepSnapshot at hstep; simp only [hpi] at hstep; nomatch hstep
      | readyToWrite opId val snap =>
        unfold stepSnapshot at hstep
        simp only [hpi, Option.some.injEq] at hstep
        exact inv.of_writeStep ht_lt hev hpi hstep
      | scanning st => exact inv.of_scanning ht_lt hev hpi hstep

end SnapshotTrace

end Cslib.Distributed.SetAgreement
