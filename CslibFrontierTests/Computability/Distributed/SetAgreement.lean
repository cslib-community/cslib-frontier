/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot
import CslibFrontier.Computability.Distributed.SetAgreement.ImmediateSnapshot
import CslibFrontier.Computability.Distributed.SetAgreement.Impossibility
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases

/-! Client tests for `Cslib.Distributed.SetAgreement` (`module` client with ordinary imports):
* executable `Fin 3` traces of Afek et al.'s wait-free single-writer atomic snapshot algorithm
  exercising both the clean double-collect path (Lemma 3.1) and the concurrent twice-moved
  borrowed-view handoff path (Lemma 3.2), plus positive and negative `SnapshotLinearizable`
  histories and wait-free step/register-operation bounds;
* `decide`-checked ordered-partition (`ISSchedule`) counts (`1, 3, 13`), round-trip equivalence,
  and independence witnesses for all three Borowsky–Gafni axioms (`self_mem`, `containment`,
  `immediacy`);
* `decide`-checked panchromatic `IIS` execution counts on `Fin 2` (`R = 1, 2`) and `Fin 3`
  (`R = 1`) illustrating `odd_card_panchromatic_iis`, plus concrete `flipIISExec` checks;
* instantiations of wait-free `k`-set agreement impossibility (`k = 1` binary consensus on `Fin 2`,
  `k = 2` on `Fin 3`), positive `k ≥ min(|V|, |Val|)` protocols (`exists_iis_setAgreement_iff`),
  and positive `(n - t)`-quorum `k`-set agreement when `t < k` (`exists_quorumSetAgreement_of_lt`).
-/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.SetAgreement

open Finset Cslib.Distributed.SetAgreement

/-! ### 1. Wait-free single-writer atomic snapshot (`AtomicSnapshot.lean`) -/

/-- Canonical scan order `[0, 1, 2]` on `Fin 3`. -/
def ordFin3 : ScanOrder (Fin 3) where
  elems := [0, 1, 2]
  nodup := by decide
  complete p := by fin_cases p <;> decide

/-- Replay a list of `SnapshotEvent`s from `s`, returning `none` if any transition is disabled. -/
def replayEvents {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P) (dInit : Data) :
    SnapshotState P Data → List (SnapshotEvent P Data) → Option (SnapshotState P Data)
  | s, [] => some s
  | s, ev :: rest =>
    match stepSnapshot ord dInit s ev with
    | none => none
    | some s' => replayEvents ord dInit s' rest

theorem mtr_of_replayEvents {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) :
    ∀ {s s' : SnapshotState P Data} {evs : List (SnapshotEvent P Data)},
      replayEvents ord dInit s evs = some s' →
      (snapshotLTS ord dInit).MTr s evs s'
  | s, _, [], h => by
    injection h with hs
    subst hs
    exact Cslib.LTS.MTr.refl
  | s, _, ev :: rest, h => by
    dsimp only [replayEvents] at h
    cases hstep : stepSnapshot ord dInit s ev with
    | none => simp only [hstep] at h; nomatch h
    | some s₁ =>
      simp only [hstep] at h
      exact Cslib.LTS.MTr.stepL hstep (mtr_of_replayEvents ord dInit h)

/-- Helper executing a full solo completion (`k` `.step i` events) for process `i`. -/
def soloSteps {P Data : Type*} (i : P) (k : ℕ) : List (SnapshotEvent P Data) :=
  List.replicate k (.step i)

/-- In `Fin 3`, a solo scan or embedded scan takes `3` reads in `collectA` + `1` phase switch +
`3` reads in `collectB` + `1` clean-check finish = `8` `.step` transitions (`9` for an `update`,
including the final register write). -/
def cleanTraceEvents : List (SnapshotEvent (Fin 3) ℕ) :=
  [.invokeUpdate 0 10] ++ soloSteps 0 9 ++
  [.invokeUpdate 2 20] ++ soloSteps 2 9 ++
  [.invokeScan 1] ++ soloSteps 1 8

/-- Clean double-collect trace: `0` writes `10`, `2` writes `20`, and `1` scans `(10, 0, 20)`. -/
theorem cleanTrace_returns_expected_snapshot :
    (match replayEvents ordFin3 0 (SnapshotState.init 0) cleanTraceEvents with
     | none => false
     | some s =>
       (s.history.length == 3) &&
       ((s.reg 0).data == 10) && ((s.reg 1).data == 0) && ((s.reg 2).data == 20) &&
       match s.history[2]? with
       | some rec =>
         (match rec.kind with | .scan => true | .update _ => false) &&
         match rec.status with
         | .doneScan _ snap => (snap 0 == 10) && (snap 1 == 0) && (snap 2 == 20)
         | _ => false
       | none => false) = true := by
  decide

/-- Apply Theorem 1 step (`unbounded_snapshotLinearizable_of_reachable`) to `cleanTraceEvents`. -/
theorem cleanTrace_is_linearizable :
    ∃ s : SnapshotState (Fin 3) ℕ,
      replayEvents ordFin3 0 (SnapshotState.init 0) cleanTraceEvents = some s ∧
      SnapshotLinearizable 0 s.history := by
  cases h : replayEvents ordFin3 0 (SnapshotState.init 0) cleanTraceEvents with
  | none =>
    have hcon := cleanTrace_returns_expected_snapshot
    simp only [h] at hcon
    nomatch hcon
  | some s =>
    exact ⟨s, rfl, unbounded_snapshotLinearizable_of_reachable ⟨cleanTraceEvents,
      mtr_of_replayEvents ordFin3 0 h⟩⟩

/-- Concurrent trace forcing the **borrowed-view branch (`Lemma 3.2`)**:
1. Scanner `1` invokes `scan` and completes `collectA` (`4` steps: `3` reads of initial `(0,0,0)`
   at `seq = 0`, plus phase switch to `collectB`).
2. Updater `0` runs a full `update(10)` (`invokeUpdate 0 10` + `9` steps), incrementing
   `(reg 0).seq` to `1` and storing embedded view `(0, 0, 0)`.
3. Scanner `1` runs `collectB` (`3` reads) and its end-of-`collectB` check (`1` step): cell `0`
   changed (`0 ≠ 1`) with `0 ∉ moved = ∅`, so `scan_1` records `moved = {0}` and restarts
   `collectA`!
4. Scanner `1` runs `collectA` (`4` steps), reading `(reg 0).seq = 1`.
5. Updater `0` runs a SECOND full `update(20)` (`invokeUpdate 0 20` + `9` steps), scanning
   `(10, 0, 0)` during its embedded scan and writing `(data := 20, seq := 2, view := (10, 0, 0))`!
6. Scanner `1` runs `collectB` (`3` reads, observing `(reg 0).seq = 2` while `memSnapshot` is now
   `(20, 0, 0)`) and its end-of-`collectB` check (`1` step): since `0 ∈ moved` moved a SECOND time
   (`1 ≠ 2`), `scan_1` borrows `(reg 0).view = (10, 0, 0)` (an intermediate state strictly inside
   `scan_1`'s interval!) instead of `(20, 0, 0)`! -/
def borrowedViewTraceEvents : List (SnapshotEvent (Fin 3) ℕ) :=
  [.invokeScan 1] ++ soloSteps 1 4 ++
  [.invokeUpdate 0 10] ++ soloSteps 0 9 ++
  soloSteps 1 4 ++
  soloSteps 1 4 ++
  [.invokeUpdate 0 20] ++ soloSteps 0 9 ++
  soloSteps 1 4

theorem borrowedViewTrace_borrows_intermediate_snapshot :
    (match replayEvents ordFin3 0 (SnapshotState.init 0) borrowedViewTraceEvents with
     | none => false
     | some s =>
       ((s.reg 0).data == 20) && ((s.reg 0).seq == 2) &&
       (s.proc 1).isIdle &&
       match s.history[0]? with
       | some rec =>
         (rec.caller == 1) &&
         (match rec.kind with | .scan => true | .update _ => false) &&
         match rec.status with
         | .doneScan _ snap => (snap 0 == 10) && (snap 1 == 0) && (snap 2 == 0)
         | _ => false
       | none => false) = true := by
  decide

/-- Initial `remainingRegOps` bounds (`2 * n * (n + 1) = 24` for `scan`, `25` for `update` on
`Fin 3`) and solo wait-free completion from an arbitrary mid-scan state. -/
theorem regOps_bounds_fin3 :
    (∃ s₁, stepSnapshot ordFin3 0 (SnapshotState.init 0) (.invokeScan 1) = some s₁ ∧
      remainingRegOps ordFin3 (s₁.proc 1) = 24) ∧
    (∃ s₂, stepSnapshot ordFin3 0 (SnapshotState.init 0) (.invokeUpdate 0 42) = some s₂ ∧
      remainingRegOps ordFin3 (s₂.proc 0) = 25) := by
  constructor
  · obtain ⟨s₁, hs₁⟩ : ∃ s₁,
        stepSnapshot ordFin3 0 (SnapshotState.init 0) (.invokeScan 1) = some s₁ := ⟨_, rfl⟩
    exact ⟨s₁, hs₁, remainingRegOps_invokeScan ordFin3 0 hs₁⟩
  · obtain ⟨s₂, hs₂⟩ : ∃ s₂,
        stepSnapshot ordFin3 0 (SnapshotState.init 0) (.invokeUpdate 0 42) = some s₂ := ⟨_, rfl⟩
    exact ⟨s₂, hs₂, remainingRegOps_invokeUpdate ordFin3 0 hs₂⟩

/-- Negative `SnapshotLinearizable` test: if `update_0(10)` runs across `[0, 1]` and `scan_1` is
invoked strictly later (`invStep = 2 ≥ 1 = respStep`) yet returns stale `(0, 0, 0)`, the history is
**not** linearizable! -/
def staleHistory : List (SnapshotOpRecord (Fin 3) ℕ) :=
  [ { caller := 0, kind := .update 10, invStep := 0, status := .doneUpdate 1 },
    { caller := 1, kind := .scan, invStep := 2, status := .doneScan 3 (fun _ => 0) } ]

theorem not_linearizable_staleHistory : ¬ SnapshotLinearizable 0 staleHistory := by
  rintro ⟨seq, hlin⟩
  have h0_in : 0 ∈ seq := hlin.complete 0 (by decide) (by decide)
  have h1_in : 1 ∈ seq := hlin.complete 1 (by decide) (by decide)
  -- Real-time precedence forces `seq.idxOf 0 < seq.idxOf 1` (`respStep 0 = 1 ≤ 2 = invStep 1`)
  have hrt : seq.idxOf 0 < seq.idxOf 1 :=
    hlin.realTime 0 h0_in 1 h1_in 1 rfl (staleHistory[1]'(by decide)) rfl (by decide)
  -- Every `x ∈ seq` is `< 2`, so `Nodup`, `0, 1 ∈ seq`, and `idxOf 0 < idxOf 1`
  -- force `seq = [0, 1]`.
  rcases seq with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩
  · nomatch h0_in
  · rcases List.mem_singleton.mp h0_in with rfl
    rcases List.mem_singleton.mp h1_in with hcon
    nomatch hcon
  · have ha_lt := hlin.index_lt a List.mem_cons_self
    have hb_lt := hlin.index_lt b (List.mem_cons_of_mem a List.mem_cons_self)
    have hnd := hlin.nodup
    have hvalid := hlin.valid
    have hab : a = 0 ∧ b = 1 := by
      change a < 2 at ha_lt
      change b < 2 at hb_lt
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
        rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · simp at hnd
      · exact ⟨rfl, rfl⟩
      · simp at hrt
      · simp at hnd
    rcases hab with ⟨rfl, rfl⟩
    dsimp only [seqSnapshotValid, staleHistory] at hvalid
    have hzero : (0 : ℕ) = Function.update (fun _ : Fin 3 => (0 : ℕ)) 0 10 0 :=
      congrFun hvalid.1 0
    simp only [Function.update_self] at hzero
    omega
  · have hnd := hlin.nodup
    have ha := hlin.index_lt a List.mem_cons_self
    have hb := hlin.index_lt b (List.mem_cons_of_mem a List.mem_cons_self)
    have hc := hlin.index_lt c (List.mem_cons_of_mem a (List.mem_cons_of_mem b List.mem_cons_self))
    change a < 2 at ha; change b < 2 at hb; change c < 2 at hc
    simp only [List.nodup_cons, List.mem_cons] at hnd
    omega

/-! ### 2. One-shot `IS` schedules and Borowsky–Gafni axioms (`ImmediateSnapshot.lean`) -/

/-- Ordered Bell (Fubini) numbers for `n = 1, 2, 3`: `1`, `3`, and `13` immediate-snapshot
schedules. -/
theorem card_isSchedule_fin1 : Fintype.card (ISSchedule (univ : Finset (Fin 1))) = 1 := by
  decide

theorem card_isSchedule_fin2 : Fintype.card (ISSchedule (univ : Finset (Fin 2))) = 3 := by
  decide

theorem card_isSchedule_fin3 : Fintype.card (ISSchedule (univ : Finset (Fin 3))) = 13 := by
  decide

/-- Concrete valid `IsImmediateSnapshot` map on `Fin 3` (`{1}` followed by `{0, 2}`) round-tripping
through `ISSchedule.equivImmediateSnapshot`. -/
def sampleSnapFin3 : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1, 2}
  | 1 => {1}
  | 2 => {0, 1, 2}

theorem isImmediateSnapshot_sampleSnapFin3 : IsImmediateSnapshot sampleSnapFin3 where
  self_mem p := by fin_cases p <;> decide
  containment p q := by fin_cases p <;> fin_cases q <;> decide
  immediacy p q := by fin_cases p <;> fin_cases q <;> decide

theorem reconstructed_blocks_sampleSnapFin3 :
    let π := ISSchedule.equivImmediateSnapshot.symm
      ⟨sampleSnapFin3, isImmediateSnapshot_sampleSnapFin3⟩
    π.blocks = [{1}, {0, 2}] := by
  let π₀ : ISSchedule (univ : Finset (Fin 3)) :=
    { blocks := [{1}, {0, 2}]
      blocks_nonempty := by decide
      blocks_pairwise_disjoint := by decide
      union_blocks := by decide }
  suffices ISSchedule.equivImmediateSnapshot.symm
      ⟨sampleSnapFin3, isImmediateSnapshot_sampleSnapFin3⟩ = π₀ from
    congrArg ISSchedule.blocks this
  apply ISSchedule.snapshot_injective
  rw [ISSchedule.snapshot_equivImmediateSnapshot_symm]
  funext p
  fin_cases p <;> decide

/-- Axiom independence 1: fails **self-inclusion** while satisfying containment and immediacy
(`S p = ∅`). -/
theorem not_isImmediateSnapshot_empty :
    ¬ IsImmediateSnapshot (fun _ : Fin 2 => (∅ : Finset (Fin 2))) := by
  intro h
  exact notMem_empty 0 (h.self_mem 0)

/-- Axiom independence 2: satisfies self-inclusion and immediacy (`S p = {p}`), but fails
**containment**. -/
theorem not_isImmediateSnapshot_disjoint_singletons :
    let S : Fin 2 → Finset (Fin 2) := fun p => {p}
    (∀ p, p ∈ S p) ∧ (∀ p q, p ∈ S q → S p ⊆ S q) ∧ ¬ IsImmediateSnapshot S := by
  refine ⟨fun p => mem_singleton_self p, fun p q hpq => by rw [mem_singleton.mp hpq], ?_⟩
  intro h
  rcases h.containment 0 1 with h01 | h10
  · have : (0 : Fin 2) = 1 := mem_singleton.mp (h01 (mem_singleton_self 0))
    omega
  · have : (1 : Fin 2) = 0 := mem_singleton.mp (h10 (mem_singleton_self 1))
    omega

/-- Axiom independence 3: satisfies self-inclusion and containment (`{0, 1} ⊆ {0, 1, 2}`), but
fails **immediacy** (`0 ∈ S 1 = {0, 1}` yet `S 0 = {0, 1, 2} ⊈ S 1`)! -/
def nonImmediateMap : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1, 2}
  | 1 => {0, 1}
  | 2 => {0, 1, 2}

theorem nonImmediateMap_fails_only_immediacy :
    (∀ p, p ∈ nonImmediateMap p) ∧
    (∀ p q, nonImmediateMap p ⊆ nonImmediateMap q ∨ nonImmediateMap q ⊆ nonImmediateMap p) ∧
    ¬ IsImmediateSnapshot nonImmediateMap := by
  refine ⟨by intro p; fin_cases p <;> decide,
    by intro p q; fin_cases p <;> fin_cases q <;> decide, ?_⟩
  intro h
  have hsub := h.immediacy 0 1 (by decide)
  have h2 : (2 : Fin 3) ∈ nonImmediateMap 1 := hsub (by decide)
  revert h2
  decide

/-! ### 3. `IIS` involution and Odd Panchromatic Execution Parity (`Impossibility.lean`) -/

/-- Canonical carrier-valid coloring on `Fin n`: pick the minimum process ID in `v.carrier`! -/
def minCarrierColor {n R : ℕ} (v : IISView (Fin (n + 1)) (Fin (n + 1)) R) : Fin (n + 1) :=
  v.carrier.min' v.carrier_nonempty

theorem isCarrierColoring_minCarrierColor {n R : ℕ} :
    IsCarrierColoring (minCarrierColor (n := n) (R := R)) :=
  fun v => Finset.min'_mem v.carrier v.carrier_nonempty

/-- On `Fin 2`, `minCarrierColor` chooses `0` whenever `0 ∈ v.carrier`, and `1` only when `1` ran
strictly before `0` in every round (`carrier = {1}`). Thus in `R` rounds there is **1** (odd!)
panchromatic execution out of `3^R` (`[{1}, {0}]` in every round: `1` decides `1`, `0` sees `{0, 1}`
and decides `0`). -/
theorem panchromatic_count_fin2_R1 :
    #{E : Fin 1 → ISSchedule (univ : Finset (Fin 2)) |
      IsPanchromaticIIS univ id (minCarrierColor (n := 1) (R := 1)) E} = 1 := by
  decide

theorem panchromatic_count_fin2_R2 :
    #{E : Fin 2 → ISSchedule (univ : Finset (Fin 2)) |
      IsPanchromaticIIS univ id (minCarrierColor (n := 1) (R := 2)) E} = 1 := by
  decide

/-- Non-symmetric carrier-valid coloring on `Fin 2` (`R = 1`): process `0` picks `max'` of its
carrier while process `1` picks `min'` of its carrier!
* `[{0}, {1}]`: `0` has `{0} ↦ 0`, `1` has `{0, 1} ↦ 0` (not panchromatic);
* `[{1}, {0}]`: `1` has `{1} ↦ 1`, `0` has `{0, 1} ↦ 1` (not panchromatic);
* `[{0, 1}]`: `0` has `{0, 1} ↦ 1`, `1` has `{0, 1} ↦ 0` (**panchromatic**, swapped!).
And if instead `0` picks `min'` on singleton `{0}` (`0`), `max'` on `{0, 1}` (`1`), while `1`
ALWAYS picks `1` (`1 ∈ carrier` since `v.proc = 1`? Wait: `c` depends only on `v`, and `v.proc` is
part of `v`!), let's test `cSwap` where `v.proc = 0` picks `max'` and `v.proc = 1` picks `max'`?
Wait: if `v.proc = 0` picks `min'` (`0` on `{0}` and `{0, 1}`) and `v.proc = 1` picks `max'` (`1`
on `{1}` and `{0, 1}`), then ALL **3** schedules (`3`, odd!) are panchromatic! -/
def allThreePanchromaticColor (v : IISView (Fin 2) (Fin 2) 1) : Fin 2 :=
  if v.proc = 0 then v.carrier.min' v.carrier_nonempty
  else v.carrier.max' v.carrier_nonempty

theorem isCarrierColoring_allThree : IsCarrierColoring allThreePanchromaticColor := by
  intro v
  unfold allThreePanchromaticColor
  split_ifs
  · exact Finset.min'_mem _ _
  · exact Finset.max'_mem _ _

theorem panchromatic_count_allThree_fin2_R1 :
    #{E : Fin 1 → ISSchedule (univ : Finset (Fin 2)) |
      IsPanchromaticIIS univ id allThreePanchromaticColor E} = 3 := by
  decide

/-- Direct computable minimum-ID carrier coloring on `Fin 3` avoiding `WellFounded` recursion in
kernel `decide`: on `R = 1` (`13` schedules), its panchromatic count is `1` (odd: only
`[{2}, {1}, {0}]` makes `2 ↦ 2`, `1 ↦ 1`, `0 ↦ 0`), and `odd_card_panchromatic_iis` applies to
arbitrary `R` without enumeration! -/
def minFin3Color {R : ℕ} (v : IISView (Fin 3) (Fin 3) R) : Fin 3 :=
  if 0 ∈ v.carrier then 0 else if 1 ∈ v.carrier then 1 else 2

theorem isCarrierColoring_minFin3Color {R : ℕ} :
    IsCarrierColoring (minFin3Color (R := R)) := by
  intro v
  unfold minFin3Color
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · obtain ⟨x, hx⟩ := v.carrier_nonempty
    fin_cases x
    · exact absurd hx h0
    · exact absurd hx h1
    · exact hx

/-- Positive and negative `Fin 3` (`R = 1`) schedules for `IsPanchromaticIIS` under `minFin3Color`:
`[{2}, {1}, {0}]` is panchromatic (`2 ↦ 2`, `1 ↦ 1`, `0 ↦ 0`), whereas simultaneous `[{0, 1, 2}]`
is monochromatic (`0, 1, 2 ↦ 0`). -/
def schedDescFin3 : ISSchedule (univ : Finset (Fin 3)) where
  blocks := [{2}, {1}, {0}]
  blocks_nonempty := by decide
  blocks_pairwise_disjoint := by decide
  union_blocks := by decide

def schedAllFin3 : ISSchedule (univ : Finset (Fin 3)) where
  blocks := [{0, 1, 2}]
  blocks_nonempty := by decide
  blocks_pairwise_disjoint := by decide
  union_blocks := by decide

theorem panchromatic_fin3_positive_and_negative :
    IsPanchromaticIIS univ id (minFin3Color (R := 1)) (fun _ : Fin 1 => schedDescFin3) ∧
    ¬ IsPanchromaticIIS univ id (minFin3Color (R := 1)) (fun _ : Fin 1 => schedAllFin3) := by
  decide

theorem odd_panchromatic_fin3_any_round (R : ℕ) :
    Odd #{E : Fin R → ISSchedule (univ : Finset (Fin 3)) |
      IsPanchromaticIIS univ id (minFin3Color (R := R)) E} :=
  odd_card_panchromatic_iis isCarrierColoring_minFin3Color univ id

theorem odd_panchromatic_fin4_any_round (R : ℕ) :
    Odd #{E : Fin R → ISSchedule (univ : Finset (Fin 4)) |
      IsPanchromaticIIS univ id (minCarrierColor (n := 3) (R := R)) E} :=
  odd_card_panchromatic_iis isCarrierColoring_minCarrierColor univ id

/-- Concrete check of `flipIISExec` on `Fin 3` across `R = 2` rounds: when round `1` (the last
round) has `{2}` running last alone (`IsBoundaryAt 2`), `flipIISExec` leaves round `1` untouched
and flips round `0` (`[{0, 2}, {1}] ↦ [{2}, {0}, {1}]`) while preserving `iisRun` for `0` and
`1`! -/
def schedRound0 : ISSchedule (univ : Finset (Fin 3)) where
  blocks := [{0, 2}, {1}]
  blocks_nonempty := by decide
  blocks_pairwise_disjoint := by decide
  union_blocks := by decide

def schedRound1Boundary : ISSchedule (univ : Finset (Fin 3)) where
  blocks := [{0, 1}, {2}]
  blocks_nonempty := by decide
  blocks_pairwise_disjoint := by decide
  union_blocks := by decide

def twoRoundExec : Fin 2 → ISSchedule (univ : Finset (Fin 3))
  | 0 => schedRound0
  | 1 => schedRound1Boundary

theorem flipIISExec_skips_boundary_last_round :
    let h2 : (2 : Fin 3) ∈ (univ : Finset (Fin 3)) := mem_univ 2
    let E' := flipIISExec h2 twoRoundExec
    (E' 1).blocks = [{0, 1}, {2}] ∧
    (E' 0).blocks = [{2}, {0}, {1}] ∧
    iisRun id E' 0 = iisRun id twoRoundExec 0 ∧
    iisRun id E' 1 = iisRun id twoRoundExec 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · change ((schedRound0.flip (mem_univ 2)).blocks = [{2}, {0}, {1}])
    rw [ISSchedule.blocks_flip]
    decide
  · exact iisRun_flipIISExec_of_ne (mem_univ 2) id twoRoundExec (by decide)
  · exact iisRun_flipIISExec_of_ne (mem_univ 2) id twoRoundExec (by decide)

/-! ### 4. Wait-free `k`-set agreement impossibility & `t < k` positive resilience -/

/-- **Wait-free binary consensus (`k = 1`) is impossible in `R`-round `IIS`** on `2` processes for
every round bound `R`. -/
theorem binary_consensus_impossible_iis (R : ℕ) (P : IISProtocol (Fin 2) Bool R) :
    ¬ P.SolvesSetAgreement 1 :=
  not_solvesSetAgreement_iis (by decide) (by decide) P

/-- **Wait-free `2`-set agreement is impossible in `R`-round `IIS`** on `3` processes over `3`
input values for every round bound `R`. -/
theorem two_set_agreement_impossible_fin3 (R : ℕ) (P : IISProtocol (Fin 3) (Fin 3) R) :
    ¬ P.SolvesSetAgreement 2 :=
  not_solvesSetAgreement_iis (by decide) (by decide) P

/-- Positive side of `exists_iis_setAgreement_iff`: `2`-set agreement IS solvable in `IIS` when
either `|V| ≤ 2` (`Fin 2` over `Fin 5`) or `|Val| ≤ 2` (`Fin 5` over `Bool`), and `0`-set agreement
is solvable on `Empty`. -/
theorem two_set_agreement_solvable_small_procs_or_vals :
    (∃ (R : ℕ) (P : IISProtocol (Fin 2) (Fin 5) R), P.SolvesSetAgreement 2) ∧
    (∃ (R : ℕ) (P : IISProtocol (Fin 5) Bool R), P.SolvesSetAgreement 2) ∧
    (∃ (R : ℕ) (P : IISProtocol Empty Bool R), P.SolvesSetAgreement 0) :=
  ⟨(exists_iis_setAgreement_iff (Fin 2) (Fin 5) 2).mpr (Or.inl (by decide)),
   (exists_iis_setAgreement_iff (Fin 5) Bool 2).mpr (Or.inr (by decide)),
   (exists_iis_setAgreement_iff Empty Bool 0).mpr (Or.inl (by decide))⟩

/-- **Quorum sharpness (`t < k` vs wait-free `t = n - 1`):** on `4` processes over `Fin 10`
proposals, wait-free `2`-set agreement is impossible in `IIS` for every `R`, whereas
`(n - 1)`-quorum (`t = 1 < k = 2`) `2`-set agreement IS solvable in a single quorum round! -/
theorem quorum_sharpness_fin4 :
    (∀ (R : ℕ) (P : IISProtocol (Fin 4) (Fin 10) R), ¬ P.SolvesSetAgreement 2) ∧
    (∃ P : QuorumProtocol (Fin 4) (Fin 10), P.SolvesSetAgreement 1 2) :=
  ⟨fun _ P => not_solvesSetAgreement_iis (by decide) (by decide) P,
   exists_quorumSetAgreement_of_lt (Fin 4) (Fin 10) (by omega)⟩

end CslibFrontierTests.Distributed.SetAgreement
