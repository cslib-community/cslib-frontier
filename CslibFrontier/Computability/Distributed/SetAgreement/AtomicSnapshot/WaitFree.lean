/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Machine
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.StepFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Wait-free `O(n²)` step and shared-register operation complexity

Defines `remainingSteps`, `remainingRegOps`, and `isRegAccessStep`, proving unconditional
`O(n²)` per-process wait-free completion bounds (`exists_solo_completion`,
[AfekAttiyaDolevGafniMerrittShavit1993], Lemma 3.4, p. 10).

## Main definitions

* `Cslib.Distributed.SetAgreement.remainingSteps`,
  `Cslib.Distributed.SetAgreement.remainingRegOps`,
  `Cslib.Distributed.SetAgreement.isRegAccessStep`: per-process termination potentials (`O(n²)`).

## Main results

* `Cslib.Distributed.SetAgreement.remainingSteps_le_quad`: `2n² + 4n + 3` upper bound.
* `Cslib.Distributed.SetAgreement.remainingRegOps_invokeScan`,
  `Cslib.Distributed.SetAgreement.remainingRegOps_invokeUpdate`: initial register-operation counts.
* `Cslib.Distributed.SetAgreement.proc_eq_of_other_event`,
  `Cslib.Distributed.SetAgreement.remainingSteps_eq_of_other`,
  `Cslib.Distributed.SetAgreement.remainingSteps_lt_of_step`,
  `Cslib.Distributed.SetAgreement.step_enabled_of_not_idle`,
  `Cslib.Distributed.SetAgreement.exists_solo_completion`: non-interference and solo termination.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

/-! ### Wait-free `O(n²)` step complexity (`Lemma 3.4`) -/

/-- Remaining protocol steps (including local loop-boundary evaluations) for process `i` to finish
its current operation (`0` when `idle`). -/
@[expose]
def remainingSteps {P Data : Type*} (ord : ScanOrder P) :
    ProcSnapshotState P Data → ℕ
  | .idle => 0
  | .readyToWrite _ _ _ => 1
  | .scanning st =>
    let n := ord.elems.length
    let remIters := n - #st.moved
    let iterRem :=
      match st.phase with
      | .collectA => st.rem.length + n + 2
      | .collectB => st.rem.length + 1
    let writeStep := match st.mode with | .external => 0 | .embedded _ => 1
    remIters * (2 * n + 2) + iterRem + writeStep

/-- Remaining shared-register operations (`Read` or `Write`, excluding purely local transitions)
for process `i` to finish its current operation (`0` when `idle`). -/
@[expose]
def remainingRegOps {P Data : Type*} (ord : ScanOrder P) :
    ProcSnapshotState P Data → ℕ
  | .idle => 0
  | .readyToWrite _ _ _ => 1
  | .scanning st =>
    let n := ord.elems.length
    let remIters := n - #st.moved
    let iterReads :=
      match st.phase with
      | .collectA => st.rem.length + n
      | .collectB => st.rem.length
    let writeOp := match st.mode with | .external => 0 | .embedded _ => 1
    remIters * (2 * n) + iterReads + writeOp

/-- Whether transition `stepSnapshot ord dInit s (.step i)` performs a shared-register `Read` or
`Write` (`true`) versus a local loop evaluation (`false`). -/
@[expose]
def isRegAccessStep {P Data : Type*} (s : SnapshotState P Data) (i : P) : Bool :=
  match s.proc i with
  | .idle => false
  | .readyToWrite _ _ _ => true
  | .scanning st =>
    match st.rem with
    | _ :: _ => true
    | [] => false

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): in every state with
`st.rem.length ≤ n`, `remainingSteps` is at most `(2n + 2)(n + 1) + 1 = 2n² + 4n + 3` where
`n = Fintype.card P`. -/
theorem remainingSteps_le_quad {P Data : Type*} [Fintype P] (ord : ScanOrder P)
    (ps : ProcSnapshotState P Data)
    (hrem : ∀ st, ps = .scanning st → st.rem.length ≤ ord.elems.length) :
    remainingSteps ord ps ≤
      (2 * Fintype.card P + 2) * (Fintype.card P + 1) + 1 := by
  have hn := ord.length_eq_card
  cases ps with
  | idle | readyToWrite _ _ _ => simp only [remainingSteps]; omega
  | scanning st =>
    have hr := hrem st rfl
    simp only [remainingSteps]
    have hmul : (ord.elems.length - #st.moved) * (2 * ord.elems.length + 2) ≤
        ord.elems.length * (2 * ord.elems.length + 2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    cases st.phase <;> cases st.mode <;> dsimp only <;> nlinarith

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): immediately after
`invokeScan i`, `remainingRegOps` equals `2 * n * (n + 1)` (`O(n²)` shared-register reads, bounded
across subsequent steps by `remainingSteps_lt_of_step`). -/
theorem remainingRegOps_invokeScan {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.invokeScan i) = some s') :
    remainingRegOps ord (s'.proc i) = 2 * Fintype.card P * (Fintype.card P + 1) := by
  obtain ⟨-, rfl⟩ := stepSnapshot_invokeScan_eq h
  simp only [Function.update_self, remainingRegOps, card_empty, Nat.sub_zero,
    ord.length_eq_card]
  ring

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): immediately after
`invokeUpdate i val`, `remainingRegOps` equals `2 * n * (n + 1) + 1` (`O(n²)` shared-register reads
plus `1` write, bounded across subsequent steps by `remainingSteps_lt_of_step`). -/
theorem remainingRegOps_invokeUpdate {P Data : Type*} [Fintype P] [DecidableEq P]
    (ord : ScanOrder P) (dInit : Data) {s s' : SnapshotState P Data} {i : P} {val : Data}
    (h : stepSnapshot ord dInit s (.invokeUpdate i val) = some s') :
    remainingRegOps ord (s'.proc i) = 2 * Fintype.card P * (Fintype.card P + 1) + 1 := by
  obtain ⟨-, rfl⟩ := stepSnapshot_invokeUpdate_eq h
  simp only [Function.update_self, remainingRegOps, card_empty, Nat.sub_zero,
    ord.length_eq_card]
  ring

/-- Any event performed by another process `j ≠ i` leaves `i`'s local state and `remainingSteps`
completely unchanged. -/
theorem proc_eq_of_other_event {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data} {i : P}
    (hne : ev ≠ .invokeScan i ∧ (∀ v, ev ≠ .invokeUpdate i v) ∧ ev ≠ .step i)
    (h : stepSnapshot ord dInit s ev = some s') :
    s'.proc i = s.proc i := by
  obtain ⟨⟨ps, hproc⟩, -⟩ := stepSnapshot_effect h
  rw [hproc, Function.update_of_ne]
  rcases ev with j | ⟨j, v⟩ | j <;> rintro rfl
  exacts [hne.1 rfl, hne.2.1 v rfl, hne.2.2 rfl]

theorem remainingSteps_eq_of_other {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data} {i : P}
    (hne : ev ≠ .invokeScan i ∧ (∀ v, ev ≠ .invokeUpdate i v) ∧ ev ≠ .step i)
    (h : stepSnapshot ord dInit s ev = some s') :
    remainingSteps ord (s'.proc i) = remainingSteps ord (s.proc i) :=
  congrArg (remainingSteps ord) (proc_eq_of_other_event ord dInit hne h)

/-- An unsuccessful double collect with no second-move process adds at least one new process to
`st.moved`, strictly increasing `#st.moved`. -/
private theorem card_moved_lt_of_restart {P Data : Type*} [Fintype P] [DecidableEq P]
    (ord : ScanOrder P) (st : ActiveScan P Data)
    (hdirty : ¬ ∀ k : P, (st.collectAVal k).seq = (st.collectBVal k).seq)
    (hfind : (ord.elems.find? fun k =>
        decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) = none) :
    #st.moved <
      #(st.moved ∪ univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq) := by
  push Not at hdirty
  obtain ⟨k₀, hk₀_ne⟩ := hdirty
  have hk₀_not_moved : k₀ ∉ st.moved := by
    have hnone := List.find?_eq_none.mp hfind k₀ (ord.complete k₀)
    simp only [decide_eq_true_eq, not_and] at hnone; exact hnone hk₀_ne
  have hsub : insert k₀ st.moved ⊆
      st.moved ∪ univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ x, hk₀_ne⟩)
    · exact mem_union_left _ hx
  calc #st.moved < #(insert k₀ st.moved) := by rw [card_insert_of_notMem hk₀_not_moved]; omega
    _ ≤ _ := card_le_card hsub

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): every atomic `.step i` of
an active process `i` strictly decreases `remainingSteps ord (s.proc i)`, and decreases
`remainingRegOps` whenever a shared register is accessed (`isRegAccessStep`). -/
theorem remainingSteps_lt_of_step {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.step i) = some s') :
    remainingSteps ord (s'.proc i) < remainingSteps ord (s.proc i) ∧
      remainingRegOps ord (s'.proc i) + (if isRegAccessStep s i then 1 else 0) ≤
        remainingRegOps ord (s.proc i) := by
  unfold stepSnapshot at h
  cases hpi : s.proc i with
  | idle => simp only [hpi] at h; nomatch h
  | readyToWrite opId val snap =>
    simp only [hpi, Option.some.injEq] at h; subst h
    simp only [isRegAccessStep, hpi, ↓reduceIte, Function.update_self, remainingSteps,
      remainingRegOps, Nat.zero_lt_one, le_refl, and_self]
  | scanning st =>
    simp only [hpi] at h
    cases hrem : st.rem with
    | cons j rest =>
      cases hph : st.phase
      all_goals
        simp only [hph, hrem, Option.some.injEq] at h
        subst h
        simp only [isRegAccessStep, hpi, hrem, ↓reduceIte, Function.update_self,
          remainingSteps, remainingRegOps, hph, List.length_cons]
        cases st.mode <;> dsimp only <;> constructor <;> omega
    | nil =>
      cases hph : st.phase with
      | collectA =>
        simp only [hph, hrem, Option.some.injEq] at h
        subst h
        simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
          Function.update_self, remainingSteps, remainingRegOps, hph, List.length_nil]
        cases st.mode <;> dsimp only <;> constructor <;> omega
      | collectB =>
        have hfinish : ∀ snap,
            finishScan s i st.mode st.opId snap = s' →
            remainingSteps ord (s'.proc i) < remainingSteps ord (.scanning st) ∧
              remainingRegOps ord (s'.proc i) +
                (if isRegAccessStep s i then 1 else 0) ≤ remainingRegOps ord (.scanning st) := by
          intro snap hs'; subst hs'
          simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
            remainingSteps, remainingRegOps, hph, List.length_nil]
          unfold finishScan
          cases st.mode <;> simp only [Function.update_self] <;> constructor <;> omega
        simp only [hph, hrem] at h
        split_ifs at h with hclean
        · exact hfinish _ (Option.some.inj h)
        · cases hfind : (ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
          | some k => simp only [hfind, Option.some.injEq] at h; exact hfinish _ h
          | none =>
            simp only [hfind, Option.some.injEq] at h; subst h
            set changed := univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq
            have hcard_lt : #st.moved < #(st.moved ∪ changed) :=
              card_moved_lt_of_restart ord st hclean hfind
            have hcard_ub : #(st.moved ∪ changed) ≤ ord.elems.length := by
              rw [ord.length_eq_card]; exact card_le_univ _
            have hrem_lt : ord.elems.length - #(st.moved ∪ changed) + 1 ≤
                ord.elems.length - #st.moved := by omega
            have hmul₁ := Nat.mul_le_mul_right (2 * ord.elems.length + 2) hrem_lt
            have hmul₂ := Nat.mul_le_mul_right (2 * ord.elems.length) hrem_lt
            simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
              Function.update_self, remainingSteps, remainingRegOps, hph, List.length_nil,
              Nat.add_zero]
            cases st.mode <;> dsimp only <;> constructor <;> nlinarith

/-- Whenever `s.proc i ≠ .idle`, `.step i` is enabled (`stepSnapshot ord dInit s (.step i)` returns
`some s'`). -/
theorem step_enabled_of_not_idle {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) (s : SnapshotState P Data) (i : P) (hact : s.proc i ≠ .idle) :
    ∃ s', stepSnapshot ord dInit s (.step i) = some s' := by
  unfold stepSnapshot
  cases hpi : s.proc i with
  | idle => exact absurd hpi hact
  | readyToWrite opId val snap => simp only [hpi]; exact ⟨_, rfl⟩
  | scanning st =>
    simp only [hpi]
    cases st.phase <;> cases st.rem <;> first | exact ⟨_, rfl⟩ | split_ifs
    · exact ⟨_, rfl⟩
    · cases (ord.elems.find? fun k =>
          decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
        exact ⟨_, rfl⟩

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): from any state `s`, running
process `i` alone drives `i` to `.idle` in at most `remainingSteps ord (s.proc i)` transitions. -/
theorem exists_solo_completion {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) (s : SnapshotState P Data) (i : P) :
    ∃ (k : ℕ) (s' : SnapshotState P Data),
      k ≤ remainingSteps ord (s.proc i) ∧
      (snapshotLTS ord dInit).MTr s (List.replicate k (.step i)) s' ∧
      s'.proc i = .idle := by
  by_cases hact : s.proc i = .idle
  · exact ⟨0, s, Nat.zero_le _, Cslib.LTS.MTr.refl, hact⟩
  · obtain ⟨s₁, hs₁⟩ := step_enabled_of_not_idle ord dInit s i hact
    have hlt := (remainingSteps_lt_of_step ord dInit hs₁).1
    obtain ⟨k, s', hk_le, hmtr, hidle⟩ := exists_solo_completion ord dInit s₁ i
    exact ⟨k + 1, s', by omega, List.replicate_succ .. ▸ Cslib.LTS.MTr.stepL hs₁ hmtr, hidle⟩
termination_by remainingSteps ord (s.proc i)

end Cslib.Distributed.SetAgreement
