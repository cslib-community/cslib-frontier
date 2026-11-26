/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Model
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceInv
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.StepFacts
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceWrites

/-!
# Internal linearization chunk construction and prefix validity

Constructs step-indexed linearization chunks (`linScansAt`, `linUpdatesAt`, `linChunk`, `linPrefix`)
from `TraceInv` and proves duplicate-freeness, sequential validity, and real-time chunk ordering;
never re-exported through `AtomicSnapshot`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotTrace.linScanPoint`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linScansAt`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linUpdatesAt`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linChunk`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linPrefix`: step-indexed linearization chunks.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.nodup_linPrefix`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linPrefix_valid`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.linChunk_lt_of_realTime`: duplicate-freeness,
  sequential replay soundness, and real-time precedence across chunks.
-/

public section

namespace Cslib.Distributed.SetAgreement

/-- Sequential memory state across appended index lists. -/
private theorem seqSnapshotMemAfter_append {P Data : Type*} [DecidableEq P] (mem : P → Data)
    (hist : List (SnapshotOpRecord P Data)) (xs ys : List ℕ) :
    seqSnapshotMemAfter mem hist (xs ++ ys) =
      seqSnapshotMemAfter (seqSnapshotMemAfter mem hist xs) hist ys := by
  induction xs generalizing mem with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- Distinct history entries never carry the same `.doneUpdate w` completion step. -/
private theorem doneUpdate_inj_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit)
    (hinv : ∀ m ≤ τ.events.length, τ.TraceInv m) :
    ∀ t ≤ τ.events.length,
      ∀ id₁ id₂ (h₁ : id₁ < (τ.stateAt t).history.length)
        (h₂ : id₂ < (τ.stateAt t).history.length) w,
        ((τ.stateAt t).history[id₁]'h₁).status = .doneUpdate w →
        ((τ.stateAt t).history[id₂]'h₂).status = .doneUpdate w →
        id₁ = id₂ := by
  intro t ht
  induction t with
  | zero =>
    intro id₁ _ h₁; rw [SnapshotTrace.stateAt_zero] at h₁; cases h₁
  | succ t ih =>
    have ht_lt : t < τ.events.length := Nat.lt_of_succ_le ht
    have inv := hinv t (Nat.le_of_succ_le ht)
    have ih_t := ih (Nat.le_of_succ_le ht)
    intro id₁ id₂ h₁ h₂ w hst₁ hst₂
    have transfer : ∀ opId st, (τ.stateAt (t + 1)).history =
        completeHistoryAt (τ.stateAt t).history opId st → .doneUpdate w ≠ st → id₁ = id₂ := by
      intro opId st hhist hne_st
      rw [List.getElem_of_eq hhist h₁] at hst₁
      rw [List.getElem_of_eq hhist h₂] at hst₂
      obtain ⟨hk₁, heq₁⟩ := getElem_completeHistoryAt_of_status_ne hne_st (hhist ▸ h₁) hst₁
      obtain ⟨hk₂, heq₂⟩ := getElem_completeHistoryAt_of_status_ne hne_st (hhist ▸ h₂) hst₂
      exact ih_t id₁ id₂ hk₁ hk₂ w (heq₁ ▸ hst₁) (heq₂ ▸ hst₂)
    rcases (stepSnapshot_effect (τ.stateAt_step ht_lt)).2 with
        ⟨_, opId, _, _, -, -, hs₁⟩ |
        ⟨-, -, hhist | ⟨rec, hpend, hhist⟩ | ⟨_, _, _, -, -, -, hhist⟩⟩
    · have hhist : (τ.stateAt (t + 1)).history =
          completeHistoryAt (τ.stateAt t).history opId (.doneUpdate t) := by
        rw [hs₁, inv.stepCount_eq]
      by_cases hwt : w = t
      · subst w
        have eq_opId : ∀ {k} (hk : k < (τ.stateAt (t + 1)).history.length),
            ((τ.stateAt (t + 1)).history[k]'hk).status = .doneUpdate t → k = opId := by
          intro k hk hst
          by_contra hne
          have hk' := hhist ▸ hk
          rw [List.getElem_of_eq hhist hk, getElem_completeHistoryAt_ne hne hk'] at hst
          obtain ⟨_, -, -, hlt_w, -⟩ := inv.hist_doneUpdate k _ t hst
          omega
        exact (eq_opId h₁ hst₁).trans (eq_opId h₂ hst₂).symm
      · exact transfer _ _ hhist fun h => hwt (SnapshotOpStatus.doneUpdate.inj h)
    · exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
        (by rwa [List.getElem_of_eq hhist h₁] at hst₁)
        (by rwa [List.getElem_of_eq hhist h₂] at hst₂)
    · have lt_old : ∀ {k} (hk : k < (τ.stateAt (t + 1)).history.length),
          ((τ.stateAt (t + 1)).history[k]'hk).status = .doneUpdate w →
          ∃ hk₀ : k < (τ.stateAt t).history.length,
            ((τ.stateAt t).history[k]'hk₀).status = .doneUpdate w := by
        intro k hk hst
        rw [List.getElem_of_eq hhist hk, List.getElem_append] at hst
        split_ifs at hst with hk₀
        · exact ⟨hk₀, hst⟩
        · obtain rfl : k = (τ.stateAt t).history.length := by simp [hhist] at hk; omega
          simp only [Nat.sub_self, List.getElem_singleton, hpend, reduceCtorEq] at hst
      obtain ⟨hk₁, hs₁'⟩ := lt_old h₁ hst₁
      obtain ⟨hk₂, hs₂'⟩ := lt_old h₂ hst₂
      exact ih_t id₁ id₂ hk₁ hk₂ w hs₁' hs₂'
    · exact transfer _ _ hhist nofun

namespace SnapshotTrace

section Linearization

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Witness serialization step in `(invStep, resp]` selected for a completed scan returning `snap`
(returns `0` when no such witness exists). -/
noncomputable def linScanPoint (τ : SnapshotTrace ord dInit) (invStep resp : ℕ)
    (snap : P → Data) : ℕ :=
  open Classical in
  if h : ∃ v, invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap then
    Classical.choose h
  else 0

/-- Specification satisfied by `linScanPoint` when a witnessing snapshot step exists. -/
theorem linScanPoint_spec (τ : SnapshotTrace ord dInit) {invStep resp : ℕ}
    {snap : P → Data}
    (hex : ∃ v, invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap) :
    invStep + 1 ≤ τ.linScanPoint invStep resp snap ∧
      τ.linScanPoint invStep resp snap ≤ resp ∧
      memSnapshot (τ.stateAt (τ.linScanPoint invStep resp snap)).reg = snap := by
  simpa only [linScanPoint, hex, ↓reduceDIte] using Classical.choose_spec hex

/-- Final-history indices of completed scans serialized at step `t`. -/
noncomputable def linScansAt (τ : SnapshotTrace ord dInit) (t : ℕ) : List ℕ :=
  let hist := (τ.stateAt τ.events.length).history
  (List.range hist.length).filter fun id =>
    match hist[id]? with
    | some rec =>
      match rec.status with
      | .doneScan r sn => decide (τ.linScanPoint rec.invStep r sn = t)
      | _ => false
    | none => false

/-- Final-history indices of completed updates that wrote at step `t`. -/
def linUpdatesAt (τ : SnapshotTrace ord dInit) (t : ℕ) : List ℕ :=
  let hist := (τ.stateAt τ.events.length).history
  (List.range hist.length).filter fun id =>
    match hist[id]? with
    | some rec =>
      match rec.status with
      | .doneUpdate w => decide (w = t)
      | _ => false
    | none => false

/-- Completed operations linearized at trace step `t` (scans before the atomic write at `t`). -/
@[expose]
noncomputable def linChunk (τ : SnapshotTrace ord dInit) (t : ℕ) : List ℕ :=
  τ.linScansAt t ++ τ.linUpdatesAt t

/-- Linearization prefix covering trace steps `0, …, k - 1`. -/
@[expose]
noncomputable def linPrefix (τ : SnapshotTrace ord dInit) (k : ℕ) : List ℕ :=
  (List.range k).flatMap τ.linChunk

/-- Membership characterization for `linScansAt`. -/
theorem mem_linScansAt_iff (τ : SnapshotTrace ord dInit) (t id : ℕ) :
    id ∈ τ.linScansAt t ↔
      ∃ (hId : id < (τ.stateAt τ.events.length).history.length) (r : ℕ) (sn : P → Data),
        ((τ.stateAt τ.events.length).history[id]'hId).status = .doneScan r sn ∧
        τ.linScanPoint ((τ.stateAt τ.events.length).history[id]'hId).invStep r sn = t := by
  simp only [linScansAt, List.mem_filter, List.mem_range]
  refine ⟨?_, fun ⟨hId, r, sn, hst, hsp⟩ =>
    ⟨hId, by simp only [List.getElem?_eq_getElem hId, hst, hsp, decide_true]⟩⟩
  rintro ⟨hId, hpred⟩
  simp only [List.getElem?_eq_getElem hId] at hpred
  cases hst : ((τ.stateAt τ.events.length).history[id]'hId).status with
  | pending | doneUpdate _ => simp only [hst, Bool.false_eq_true] at hpred
  | doneScan r sn => exact ⟨hId, r, sn, hst, by simpa only [hst, decide_eq_true_eq] using hpred⟩

/-- Membership characterization for `linUpdatesAt`. -/
theorem mem_linUpdatesAt_iff (τ : SnapshotTrace ord dInit) (t id : ℕ) :
    id ∈ τ.linUpdatesAt t ↔
      ∃ hId : id < (τ.stateAt τ.events.length).history.length,
        ((τ.stateAt τ.events.length).history[id]'hId).status = .doneUpdate t := by
  simp only [linUpdatesAt, List.mem_filter, List.mem_range]
  refine ⟨?_, fun ⟨hId, hst⟩ =>
    ⟨hId, by simp only [List.getElem?_eq_getElem hId, hst, decide_true]⟩⟩
  rintro ⟨hId, hpred⟩
  simp only [List.getElem?_eq_getElem hId] at hpred
  cases hst : ((τ.stateAt τ.events.length).history[id]'hId).status with
  | pending | doneScan _ _ => simp only [hst, Bool.false_eq_true] at hpred
  | doneUpdate w => exact ⟨hId, (by simpa only [hst, decide_eq_true_eq] using hpred) ▸ hst⟩

private theorem disjoint_linScansAt_linUpdatesAt (τ : SnapshotTrace ord dInit) {t₁ t₂ x : ℕ}
    (h₁ : x ∈ τ.linScansAt t₁) (h₂ : x ∈ τ.linUpdatesAt t₂) : False := by
  obtain ⟨_, _, _, hs₁, -⟩ := (τ.mem_linScansAt_iff t₁ x).mp h₁
  obtain ⟨_, hs₂⟩ := (τ.mem_linUpdatesAt_iff t₂ x).mp h₂
  cases hs₁.symm.trans hs₂

/-- Every linearized index appears in at most one step chunk `linChunk τ t`. -/
theorem eq_of_mem_linChunk (τ : SnapshotTrace ord dInit) {t₁ t₂ x : ℕ}
    (h₁ : x ∈ τ.linChunk t₁) (h₂ : x ∈ τ.linChunk t₂) : t₁ = t₂ := by
  rcases List.mem_append.mp h₁ with h₁ | h₁ <;> rcases List.mem_append.mp h₂ with h₂ | h₂
  · obtain ⟨_, r₁, sn₁, hs₁, hp₁⟩ := (τ.mem_linScansAt_iff t₁ x).mp h₁
    obtain ⟨_, r₂, sn₂, hs₂, hp₂⟩ := (τ.mem_linScansAt_iff t₂ x).mp h₂
    obtain ⟨rfl, rfl⟩ := SnapshotOpStatus.doneScan.inj (hs₁.symm.trans hs₂)
    exact hp₁.symm.trans hp₂
  · exact (τ.disjoint_linScansAt_linUpdatesAt h₁ h₂).elim
  · exact (τ.disjoint_linScansAt_linUpdatesAt h₂ h₁).elim
  · obtain ⟨_, hs₁⟩ := (τ.mem_linUpdatesAt_iff t₁ x).mp h₁
    obtain ⟨_, hs₂⟩ := (τ.mem_linUpdatesAt_iff t₂ x).mp h₂
    exact SnapshotOpStatus.doneUpdate.inj (hs₁.symm.trans hs₂)

/-- `linPrefix τ k` is duplicate-free for every `k`. -/
theorem nodup_linPrefix (τ : SnapshotTrace ord dInit) (k : ℕ) :
    (τ.linPrefix k).Nodup := by
  rw [linPrefix, List.nodup_flatMap]
  refine ⟨fun t _ => ?_,
    List.Pairwise.imp (fun {t₁ t₂} hne x hx₁ hx₂ => hne (τ.eq_of_mem_linChunk hx₁ hx₂))
      List.nodup_range⟩
  rw [linChunk, List.nodup_append]
  exact ⟨List.nodup_range.filter _, List.nodup_range.filter _,
    fun a ha _ hb hab => τ.disjoint_linScansAt_linUpdatesAt ha (hab ▸ hb)⟩

/-- All scans linearized at `t` validate against and preserve `memSnapshot (τ.stateAt t).reg`. -/
private theorem linScansAt_valid (τ : SnapshotTrace ord dInit)
    (inv : TraceInv τ τ.events.length) (t : ℕ) :
    seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg)
        (τ.stateAt τ.events.length).history (τ.linScansAt t) =
      memSnapshot (τ.stateAt t).reg ∧
    seqSnapshotValid (memSnapshot (τ.stateAt t).reg)
      (τ.stateAt τ.events.length).history (τ.linScansAt t) := by
  suffices ∀ xs : List ℕ,
      (∀ id ∈ xs,
        ∃ (hId : id < (τ.stateAt τ.events.length).history.length) (resp : ℕ) (snap : P → Data),
          ((τ.stateAt τ.events.length).history[id]'hId).kind = .scan ∧
          ((τ.stateAt τ.events.length).history[id]'hId).status = .doneScan resp snap ∧
          snap = memSnapshot (τ.stateAt t).reg) →
      seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg)
          (τ.stateAt τ.events.length).history xs =
        memSnapshot (τ.stateAt t).reg ∧
      seqSnapshotValid (memSnapshot (τ.stateAt t).reg)
        (τ.stateAt τ.events.length).history xs by
    refine this (τ.linScansAt t) fun id hid => ?_
    obtain ⟨hId, r, sn, hstat, hsp⟩ := (τ.mem_linScansAt_iff t id).mp hid
    have hscan := inv.hist_doneScan id hId r sn hstat
    exact ⟨hId, r, sn, hscan.1, hstat, hsp ▸ (τ.linScanPoint_spec hscan.2.2.2).2.2.symm⟩
  intro xs hpred
  induction xs with
  | nil => exact ⟨rfl, trivial⟩
  | cons id rest ih_s =>
    obtain ⟨hId, resp, snap, hkind, hstat, hsnap⟩ := hpred id List.mem_cons_self
    obtain ⟨hm_rest, hv_rest⟩ := ih_s fun x hx => hpred x (List.mem_cons_of_mem id hx)
    simp only [seqSnapshotMemAfter, seqSnapshotValid, List.getElem?_eq_getElem hId, hkind, hstat]
    exact ⟨hm_rest, hsnap, hv_rest⟩

/-- For each transition `t < τ.events.length`, `linUpdatesAt τ t` contains at most the unique write
occurring at `t`, validates sequentially, and advances `memSnapshot` to `t + 1`. -/
private theorem linUpdatesAt_valid (τ : SnapshotTrace ord dInit)
    (hinv : ∀ m ≤ τ.events.length, τ.TraceInv m) {t : ℕ} (ht_lt : t < τ.events.length) :
    seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg)
        (τ.stateAt τ.events.length).history (τ.linUpdatesAt t) =
      memSnapshot (τ.stateAt (t + 1)).reg ∧
    seqSnapshotValid (memSnapshot (τ.stateAt t).reg)
      (τ.stateAt τ.events.length).history (τ.linUpdatesAt t) := by
  have inv := hinv _ le_rfl
  have hinj := doneUpdate_inj_of_trace τ hinv τ.events.length le_rfl
  by_cases hw : ∃ j, τ.isWriteStep j t
  · obtain ⟨j, hjw⟩ := hw
    obtain ⟨id₀, hId₀, hcaller₀, hstat₀⟩ := inv.writeStep_in_hist j t ht_lt hjw
    have hget₀ := List.getElem?_eq_getElem (l := (τ.stateAt τ.events.length).history) hId₀
    have hupd_eq : τ.linUpdatesAt t = [id₀] := by
      refine List.perm_singleton.mp <| (List.perm_ext_iff_of_nodup (l₁ := τ.linUpdatesAt t)
        (List.nodup_range.filter _) (List.nodup_singleton _)).mpr fun x => ?_
      rw [τ.mem_linUpdatesAt_iff, List.mem_singleton]
      exact ⟨fun ⟨hx, hs⟩ => hinj x id₀ hx hId₀ t hs hstat₀, fun h => h ▸ ⟨hId₀, hstat₀⟩⟩
    rw [hupd_eq]
    obtain ⟨val, hkind₀, -, -, -, hreg₀⟩ := inv.hist_doneUpdate id₀ hId₀ t hstat₀
    refine ⟨?_, by simp only [seqSnapshotValid, hget₀, hkind₀, hstat₀]⟩
    simp only [seqSnapshotMemAfter, hget₀, hkind₀, hcaller₀]
    funext p
    rcases eq_or_ne p j with rfl | hpj
    · rw [Function.update_self, memSnapshot, ← hcaller₀, hreg₀]
    · rw [Function.update_of_ne hpj, memSnapshot]
      rcases τ.reg_step_iff p ht_lt with ⟨hreg_eq, -⟩ | ⟨_, _, _, hev_p, -, -, -⟩
      · exact (congrArg SnapshotReg.data hreg_eq).symm
      · obtain ⟨_, _, _, _, hev_j, -⟩ := hjw
        exact absurd (SnapshotEvent.step.inj (hev_p.symm.trans hev_j)) hpj
  · have hupd_nil : τ.linUpdatesAt t = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      obtain ⟨hx_lt, hstat⟩ := (τ.mem_linUpdatesAt_iff t x).mp hx
      obtain ⟨_, -, -, -, hw_x, -⟩ := inv.hist_doneUpdate x hx_lt t hstat
      exact hw ⟨_, hw_x⟩
    rw [hupd_nil]
    refine ⟨funext fun p => ?_, trivial⟩
    rcases τ.reg_step_iff p ht_lt with ⟨hreg_eq, -⟩ | ⟨opId, val, snap, hev_p, hproc_p, -, -⟩
    · exact (congrArg SnapshotReg.data hreg_eq).symm
    · exact absurd ⟨p, ht_lt, opId, val, snap, hev_p, hproc_p⟩ hw

/-- By induction on `k ≤ τ.events.length + 1`, `linPrefix τ k` is valid against `seqSnapshotValid`
and replays to `memSnapshot (τ.stateAt k).reg` for `k ≤ τ.events.length`. -/
theorem linPrefix_valid (τ : SnapshotTrace ord dInit)
    (hinv : ∀ m ≤ τ.events.length, τ.TraceInv m) :
    ∀ k ≤ τ.events.length + 1,
      seqSnapshotValid (fun _ => dInit) (τ.stateAt τ.events.length).history (τ.linPrefix k) ∧
      (k ≤ τ.events.length →
        seqSnapshotMemAfter (fun _ => dInit) (τ.stateAt τ.events.length).history (τ.linPrefix k) =
          memSnapshot (τ.stateAt k).reg) := by
  have inv := hinv _ le_rfl
  have updatesAt_T : τ.linUpdatesAt τ.events.length = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      obtain ⟨hx_lt, hstat⟩ := (τ.mem_linUpdatesAt_iff τ.events.length x).mp hx
      obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate x hx_lt τ.events.length hstat
      omega
  intro k hk
  induction k with
  | zero => simp [linPrefix, seqSnapshotValid, seqSnapshotMemAfter, stateAt_zero]; rfl
  | succ k ih_k =>
    obtain ⟨hv_k, hm_k⟩ := ih_k (Nat.le_of_succ_le hk)
    have hk_le_T : k ≤ τ.events.length := Nat.le_of_succ_le_succ hk
    have hflat : τ.linPrefix (k + 1) = τ.linPrefix k ++ τ.linScansAt k ++ τ.linUpdatesAt k := by
      simp only [linPrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, linChunk]
    obtain ⟨hm_sc, hv_sc⟩ := τ.linScansAt_valid inv k
    simp only [hflat, seqSnapshotValid_append, seqSnapshotMemAfter_append, hm_k hk_le_T, hm_sc]
    rcases Nat.lt_or_eq_of_le hk_le_T with hk_lt | rfl
    · obtain ⟨hm_up, hv_up⟩ := τ.linUpdatesAt_valid hinv hk_lt
      exact ⟨⟨⟨hv_k, hv_sc⟩, hv_up⟩, fun _ => hm_up⟩
    · rw [updatesAt_T]
      exact ⟨⟨⟨hv_k, hv_sc⟩, trivial⟩, fun h => absurd h (by omega)⟩

/-- Real-time precedence between linearization chunks: if `i` completes by step `r` and `j` is
invoked at or after step `r`, then `i`'s chunk index is strictly smaller than `j`'s. -/
theorem linChunk_lt_of_realTime (τ : SnapshotTrace ord dInit)
    (inv : TraceInv τ τ.events.length) {t₁ t₂ i j r : ℕ} {recJ : SnapshotOpRecord P Data}
    (hi : i ∈ τ.linChunk t₁) (hj : j ∈ τ.linChunk t₂)
    (hresp_i : ((τ.stateAt τ.events.length).history[i]?.bind SnapshotOpRecord.respStep?) = some r)
    (hget_j : (τ.stateAt τ.events.length).history[j]? = some recJ)
    (hr_le : r ≤ recJ.invStep) : t₁ < t₂ := by
  have ht₁_le_r : t₁ ≤ r := by
    obtain ⟨recI, hget_i, hresp_eq⟩ := Option.bind_eq_some_iff.mp hresp_i
    obtain ⟨hId_i, rfl⟩ := List.getElem?_eq_some_iff.mp hget_i
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨_, resp, snap, hst, hsp⟩ := (τ.mem_linScansAt_iff t₁ i).mp hi
      simp only [SnapshotOpRecord.respStep?, hst, Option.some.injEq] at hresp_eq
      have := τ.linScanPoint_spec (inv.hist_doneScan i hId_i resp snap hst).2.2.2
      omega
    · obtain ⟨_, hst⟩ := (τ.mem_linUpdatesAt_iff t₁ i).mp hi
      simp only [SnapshotOpRecord.respStep?, hst, Option.some.injEq] at hresp_eq; omega
  have hinv_lt_t₂ : recJ.invStep + 1 ≤ t₂ := by
    obtain ⟨hId_j, rfl⟩ := List.getElem?_eq_some_iff.mp hget_j
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨_, resp, snap, hst, hsp⟩ := (τ.mem_linScansAt_iff t₂ j).mp hj
      have := τ.linScanPoint_spec (inv.hist_doneScan j hId_j resp snap hst).2.2.2
      omega
    · obtain ⟨_, hst⟩ := (τ.mem_linUpdatesAt_iff t₂ j).mp hj
      obtain ⟨_, -, hinv_lt, -⟩ := inv.hist_doneUpdate j hId_j t₂ hst
      omega
  omega

end Linearization

end SnapshotTrace

end Cslib.Distributed.SetAgreement
