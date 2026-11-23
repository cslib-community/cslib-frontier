/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Tactic.FinsetCard

/-!
# Quorum-phase model and deterministic safety for Ben-Or's binary consensus

Fischer, Lynch, and Paterson (`Cslib.FLP.Consensus.ge_one_not_exists`) proved that no deterministic
asynchronous consensus protocol can tolerate even a single crash fault on two or more processes.
Ben-Or ([BenOr1983], §3, Protocol A, printed p. 28) introduced a two-stage binary consensus
protocol for `2 * t < Fintype.card P` using quorums of size `n - t` (`n = Fintype.card P`) and a
Stage-2 coin flip when no concrete proposal arrives.

This module formalizes **quorum-phase deterministic safety** after [BenOr1983], §3, Protocol A
(printed p. 28; compare Theorem 1(ii)–(iii) on printed p. 29): it defines the two-stage phase
transition over per-recipient `n - t` quorums (`PhaseSchedule.Valid`), connects quorum-phase runs to
phased dynamic mid-stage crashes (`CrashSchedule.Valid`, `crashRun`), proves that deterministic
safety (Stage-1 proposal uniqueness, 1-phase unanimous validity without coin use, single-phase
estimate lock-in, cross-phase uniform agreement, and input integrity) holds unconditionally for
**every** coin sequence, and exhibits an explicit non-terminating execution on `Fin 3, t = 1` for
every static deterministic coin fallback.

**Model scope (#7120):** `PhaseSchedule` and `CrashSchedule` group execution by synchronous phase
boundaries over `n - t` Stage-1/Stage-2 sender sets, rather than modeling the primitive
message-buffer and arbitrary cross-round step-interleaving scheduler of [BenOr1983], §2 (printed
pp. 27–28). Companion module `CslibFrontier.Computability.Distributed.BenOr.Liveness` proves a
**pre-coin phase-scheduler termination step** (`probRun`) toward Theorem 1(i) of [BenOr1983] (and
for a separate common-coin variant), while termination against full §2 asynchronous schedulers
remains open in #7120.

## Quorum-phase abstraction and non-halting write-once decisions

In [BenOr1983], §3, Protocol A (printed p. 28), messages carry their round number `r` and stage tag
(`(1, r, x_P)` in step 1; `(2, r, v, D)` or `(2, r, ?)` in step 2), and each process waits for
`n - t` messages of the matching `(stage, r)` tag before advancing. Here a single phase is modeled
by a per-recipient quorum pair `PhaseSchedule P` (`q1`, `q2 : P → Finset P`) satisfying
`PhaseSchedule.Valid t` (`n - t ≤ (q1 p).card` and `n - t ≤ (q2 p).card`).

Each process maintains `ProcState` (`est : Bool`, write-once `decided : Option Bool`, matching §2
printed p. 27) and continues executing subsequent phases after deciding (`step 4` of Protocol A,
printed p. 28) so slower processes still collect `n - t` messages. `CrashSchedule` and
`crashRun_eq_run` verify that phased mid-stage crashes—where processes in `crashed1 r ⊆ crashed2 r`
stop sending and freeze their local states—coincide on all surviving processes with `run` on a
valid `PhaseSchedule`, giving uniform agreement even across processes that crash immediately after
deciding (`crashRun_agreement`).

In each phase `r` on state `st : P → ProcState` with `n = Fintype.card P` (matching steps 1–3 of
Protocol A, [BenOr1983], §3, printed p. 28, with `0`-indexed `r : ℕ`):

1. **Stage 1 (`stage1Proposal`, Protocol A steps 1–2):** process `j` collects reports from `q1 j`.
   If strictly more than `n / 2` (`majorityThreshold n = n / 2 + 1`) senders in `q1 j` reported
   `b`, `j` proposes `some b` (`(2, r, b, D)`); otherwise `j` proposes `none` (`(2, r, ?)`).
2. **Stage 2 (`stage2Update`, Protocol A step 3):** process `p` collects Stage-2 proposals from
   `q2 p`.
   - **Adopt (step 3(a)):** if at least `1` sender in `q2 p` proposed `some b`, set next estimate
     `est := b`; otherwise (step 3(c): all proposals in `q2 p` are `none`) set `est := coins r p`.
   - **Decide (step 3(b)):** if `decided = none` and strictly more than `t` (`t + 1`) senders in
     `q2 p` proposed `some b`, set `decided := some b`.

## Main definitions

* `Cslib.Distributed.BenOr.ProcState`: per-process estimate and write-once decision register.
* `Cslib.Distributed.BenOr.PhaseSchedule`, `Cslib.Distributed.BenOr.PhaseSchedule.Valid`:
  per-recipient Stage-1 and Stage-2 phase quorums of size at least `|P| - t`.
* `Cslib.Distributed.BenOr.majorityThreshold`: strict majority threshold `n / 2 + 1`.
* `Cslib.Distributed.BenOr.reportCount`, `Cslib.Distributed.BenOr.stage1Proposal`: Stage-1 report
  tally and proposal rule.
* `Cslib.Distributed.BenOr.proposalCount`, `Cslib.Distributed.BenOr.stage2Update`: Stage-2 proposal
  tally and local state update.
* `Cslib.Distributed.BenOr.initState`, `Cslib.Distributed.BenOr.phaseStep`,
  `Cslib.Distributed.BenOr.run`, `Cslib.Distributed.BenOr.adaptiveRun`: phase execution against
  fixed and adaptive state-based schedules.
* `Cslib.Distributed.BenOr.IsUnanimous`, `Cslib.Distributed.BenOr.AllDecided`,
  `Cslib.Distributed.BenOr.EstimateLocked`: unanimous-estimate, global-decision, and
  decision-locks-estimate predicates.
* `Cslib.Distributed.BenOr.CrashSchedule`, `Cslib.Distributed.BenOr.crashRun`: dynamic mid-stage
  crash executions with frozen post-crash states.

## Main results

* `Cslib.Distributed.BenOr.adaptiveRun_eq_run`: an adaptive state-based scheduler produces the same
  trace as the fixed sequence of quorums it selects along the run.
* `Cslib.Distributed.BenOr.stage1Proposal_unique`: at most one value `b` is proposed as `some b` in
  Stage 1 across the entire network, for any quorums.
* `Cslib.Distributed.BenOr.phaseStep_lucky_coin`: for any state and Stage-1/Stage-2 quorums, there
  exists a bit `b` such that coin assignment `fun _ => b` aligns every process's next estimate to
  `b`.
* `Cslib.Distributed.BenOr.phaseStep_lock_in`: when `2 * t < |P|` and `sched.Valid t`, if any
  process newly decides `b` in Stage 2, every process sets its next estimate to `b` regardless of
  the coins.
* `Cslib.Distributed.BenOr.run_validity`: unanimous input `b` causes every process to decide `b` at
  the end of phase `0`, without reading any coin.
* `Cslib.Distributed.BenOr.run_decide_next_phase`: once any process has decided `b` by phase `r`,
  every process has decided `b` by phase `r + 1`.
* `Cslib.Distributed.BenOr.run_agreement`: no two processes ever decide conflicting values, in the
  same phase or across different phases.
* `Cslib.Distributed.BenOr.run_exists_inp_eq_of_decided`: any value decided in any phase was the
  initial input of at least one process.
* `Cslib.Distributed.BenOr.crashRun_eq_run`, `Cslib.Distributed.BenOr.crashRun_agreement`:
  simulation of dynamic mid-stage crash executions and uniform agreement across crashed and
  surviving processes.
* `Cslib.Distributed.BenOr.exists_nonterminating_of_fixed_coin`: on `Fin 3, t = 1`, every static
  deterministic coin fallback `Fin 3 → Bool` admits an input and a valid crash-free schedule under
  which no process ever decides.

## References

* [M. Ben-Or, *Another advantage of free choice: completely asynchronous agreement
  protocols*][BenOr1983]
-/

public section

namespace Cslib.Distributed.BenOr

/-! ### Process states and asynchronous phase schedules -/

/-- Local state of a process at a phase boundary in Ben-Or's binary consensus protocol. -/
@[ext]
structure ProcState where
  /-- Current binary estimate carried into the next phase. -/
  est : Bool
  /-- Write-once decision register (`some b` once decided, `none` otherwise). -/
  decided : Option Bool
  deriving @[expose] DecidableEq

/-- Initial process states for input assignment `inp : P → Bool`. -/
@[expose] def initState {P : Type*} (inp : P → Bool) (p : P) : ProcState :=
  ⟨inp p, none⟩

/-- Initial estimate of process `p` equals its input `inp p`. -/
@[simp]
theorem initState_est {P : Type*} (inp : P → Bool) (p : P) :
    (initState inp p).est = inp p := rfl

/-- Initial decision register of process `p` is `none`. -/
@[simp]
theorem initState_decided {P : Type*} (inp : P → Bool) (p : P) :
    (initState inp p).decided = none := rfl

/-- Per-recipient quorum schedule for one two-stage phase of Ben-Or's protocol.
In Stage 1, process `p` receives reports from `q1 p`; in Stage 2, `p` receives proposals from
`q2 p`. Allowing distinct sender sets per recipient captures recipient-varying quorum delivery
within a phase boundary. -/
@[ext]
structure PhaseSchedule (P : Type*) where
  /-- Senders whose Stage-1 (`report`) messages arrive at process `p` before `p` advances. -/
  q1 : P → Finset P
  /-- Senders whose Stage-2 (`propose`) messages arrive at process `p` before `p` advances. -/
  q2 : P → Finset P

/-- A phase schedule is valid for fault bound `t` if every process receives Stage-1 and Stage-2
messages from at least `|P| - t` distinct senders. -/
structure PhaseSchedule.Valid {P : Type*} [Fintype P] (sched : PhaseSchedule P) (t : ℕ) :
    Prop where
  /-- Stage-1 quorum size bound. -/
  card_q1 : ∀ p, Fintype.card P - t ≤ (sched.q1 p).card
  /-- Stage-2 quorum size bound. -/
  card_q2 : ∀ p, Fintype.card P - t ≤ (sched.q2 p).card

/-- A schedule valid for fault threshold `t` is valid for any larger threshold `t' ≥ t`. -/
theorem PhaseSchedule.Valid.mono {P : Type*} [Fintype P] {sched : PhaseSchedule P} {t t' : ℕ}
    (h : sched.Valid t) (ht : t ≤ t') : sched.Valid t' where
  card_q1 p := (Nat.sub_le_sub_left ht _).trans (h.card_q1 p)
  card_q2 p := (Nat.sub_le_sub_left ht _).trans (h.card_q2 p)

/-- Static quorum schedule in which every process hears from all non-faulty processes `univ \ F`. -/
@[expose] def PhaseSchedule.honestQuorum {P : Type*} [Fintype P] [DecidableEq P]
    (F : Finset P) : PhaseSchedule P where
  q1 _ := Finset.univ \ F
  q2 _ := Finset.univ \ F

/-- Whenever at most `t` processes are faulty, `honestQuorum F` is a valid `n - t` schedule. -/
theorem PhaseSchedule.valid_honestQuorum {P : Type*} [Fintype P] [DecidableEq P]
    {F : Finset P} {t : ℕ} (hF : F.card ≤ t) : (PhaseSchedule.honestQuorum F).Valid t := by
  have hcard : Fintype.card P - t ≤ (Finset.univ \ F).card := by finset_card
  exact ⟨fun _ => hcard, fun _ => hcard⟩

/-! ### Threshold arithmetic -/

/-- Strict majority threshold `⌊n / 2⌋ + 1`. -/
@[expose] def majorityThreshold (n : ℕ) : ℕ := n / 2 + 1

private lemma majorityThreshold_le_sub {n t : ℕ} (h : 2 * t < n) :
    majorityThreshold n ≤ n - t := by
  simp only [majorityThreshold]; omega

private lemma add_one_le_sub {n t : ℕ} (h : 2 * t < n) : t + 1 ≤ n - t := by
  omega

/-! ### Stage 1 (`report`) and proposal uniqueness -/

/-- Number of senders in `S` whose current estimate equals `b`. -/
@[expose] def reportCount {P : Type*} (st : P → ProcState) (S : Finset P) (b : Bool) : ℕ :=
  (S.filter fun j => (st j).est = b).card

/-- Stage-1 proposal computed from received reports in `S`: propose `some b` if at least
`majorityThreshold |P|` senders in `S` reported `b`, and `none` otherwise. -/
@[expose] def stage1Proposal {P : Type*} [Fintype P] (st : P → ProcState)
    (S : Finset P) : Option Bool :=
  if majorityThreshold (Fintype.card P) ≤ reportCount st S true then some true
  else if majorityThreshold (Fintype.card P) ≤ reportCount st S false then some false
  else none

/-- Symmetric characterization of when `stage1Proposal` emits `some b`. -/
@[simp]
theorem stage1Proposal_eq_some_iff {P : Type*} [Fintype P] (st : P → ProcState)
    (S : Finset P) (b : Bool) :
    stage1Proposal st S = some b ↔
      majorityThreshold (Fintype.card P) ≤ reportCount st S b := by
  cases b
  · simp only [stage1Proposal]
    split_ifs with ht hf
    · exact ⟨(fun h => nomatch h), fun _ => by finset_card [reportCount, majorityThreshold]⟩
    · exact ⟨fun _ => hf, fun _ => rfl⟩
    · exact ⟨(fun h => nomatch h), fun hf' => (hf hf').elim⟩
  · simp only [stage1Proposal]
    split_ifs with ht hf
    · exact ⟨fun _ => ht, fun _ => rfl⟩
    · exact ⟨(fun h => nomatch h), fun ht' => (ht ht').elim⟩
    · exact ⟨(fun h => nomatch h), fun ht' => (ht ht').elim⟩

/-- Symmetric characterization of when `stage1Proposal` emits `none`. -/
theorem stage1Proposal_eq_none_iff {P : Type*} [Fintype P] (st : P → ProcState)
    (S : Finset P) :
    stage1Proposal st S = none ↔
      ∀ b : Bool, reportCount st S b < majorityThreshold (Fintype.card P) := by
  rw [Option.eq_none_iff_forall_ne_some]
  simp only [ne_eq, stage1Proposal_eq_some_iff, not_le]

/-- **Stage-1 proposal uniqueness:** across the entire network, no two Stage-1 quorums `S₁` and
`S₂` can produce conflicting `some` proposals from the same state `st`, because two strict
majorities cannot be disjoint in `P`. -/
theorem stage1Proposal_unique {P : Type*} [Fintype P] (st : P → ProcState)
    (S₁ S₂ : Finset P) {b₁ b₂ : Bool}
    (h₁ : stage1Proposal st S₁ = some b₁) (h₂ : stage1Proposal st S₂ = some b₂) :
    b₁ = b₂ := by
  finset_card [stage1Proposal_eq_some_iff, reportCount, majorityThreshold]

private lemma stage1Proposal_of_forall_est {P : Type*} [Fintype P] {st : P → ProcState}
    {S : Finset P} {t : ℕ} {b : Bool} (ht : 2 * t < Fintype.card P)
    (hS : Fintype.card P - t ≤ S.card) (hest : ∀ j ∈ S, (st j).est = b) :
    stage1Proposal st S = some b := by
  rw [stage1Proposal_eq_some_iff, reportCount, Finset.filter_true_of_mem hest]
  exact (majorityThreshold_le_sub ht).trans hS

/-! ### Stage 2 (`propose`) and phase execution -/

/-- Number of senders in `S` whose Stage-2 proposal equals `some b`. -/
@[expose] def proposalCount {P : Type*} (prop : P → Option Bool) (S : Finset P) (b : Bool) : ℕ :=
  (S.filter fun j => prop j = some b).card

private lemma proposalCount_pos_iff {P : Type*} (prop : P → Option Bool) (S : Finset P)
    (b : Bool) : 1 ≤ proposalCount prop S b ↔ ∃ j ∈ S, prop j = some b :=
  Finset.card_pos.trans Finset.filter_nonempty_iff

/-- Stage-2 local state transition for a process in state `cur` receiving Stage-2 proposals from
senders `S` with coin bit `coin` under fault threshold `t`. -/
@[expose] def stage2Update {P : Type*} (t : ℕ) (prop : P → Option Bool)
    (S : Finset P) (coin : Bool) (cur : ProcState) : ProcState where
  est :=
    if 1 ≤ proposalCount prop S true then true
    else if 1 ≤ proposalCount prop S false then false
    else coin
  decided :=
    match cur.decided with
    | some d => some d
    | none =>
      if t + 1 ≤ proposalCount prop S true then some true
      else if t + 1 ≤ proposalCount prop S false then some false
      else none

private lemma stage2Update_est_of_unique {P : Type*} {t : ℕ} {prop : P → Option Bool}
    (huniq : ∀ j₁ j₂ b₁ b₂, prop j₁ = some b₁ → prop j₂ = some b₂ → b₁ = b₂)
    {S : Finset P} {coin : Bool} {cur : ProcState} {b : Bool}
    (hex : ∃ j ∈ S, prop j = some b) :
    (stage2Update t prop S coin cur).est = b := by
  obtain ⟨j, hjS, hjb⟩ := hex
  have hpos : 1 ≤ proposalCount prop S b := (proposalCount_pos_iff prop S b).mpr ⟨j, hjS, hjb⟩
  cases b
  · have hno : ¬ 1 ≤ proposalCount prop S true := by
      rw [proposalCount_pos_iff]
      rintro ⟨j', _, hj't⟩
      cases huniq j j' false true hjb hj't
    simp only [stage2Update, hno, ↓reduceIte, hpos]
  · simp only [stage2Update, hpos, ↓reduceIte]

private lemma stage2Update_est_of_all_none {P : Type*} {t : ℕ} {prop : P → Option Bool}
    {S : Finset P} {coin : Bool} {cur : ProcState}
    (hnone : ∀ j ∈ S, prop j = none) :
    (stage2Update t prop S coin cur).est = coin := by
  have hnt : ¬ 1 ≤ proposalCount prop S true := by
    rw [proposalCount_pos_iff]; rintro ⟨j, hj, hjt⟩; rw [hnone j hj] at hjt; cases hjt
  have hnf : ¬ 1 ≤ proposalCount prop S false := by
    rw [proposalCount_pos_iff]; rintro ⟨j, hj, hjf⟩; rw [hnone j hj] at hjf; cases hjf
  simp only [stage2Update, hnt, hnf, ↓reduceIte]

private lemma stage2Update_decided_of_some {P : Type*} {t : ℕ} {prop : P → Option Bool}
    {S : Finset P} {coin : Bool} {cur : ProcState} {d : Bool} (hd : cur.decided = some d) :
    (stage2Update t prop S coin cur).decided = some d := by
  simp only [stage2Update, hd]

private lemma stage2Update_decided_eq_some_iff_of_none {P : Type*} {t : ℕ} {prop : P → Option Bool}
    (huniq : ∀ j₁ j₂ b₁ b₂, prop j₁ = some b₁ → prop j₂ = some b₂ → b₁ = b₂)
    {S : Finset P} {coin : Bool} {cur : ProcState} (hd : cur.decided = none) (b : Bool) :
    (stage2Update t prop S coin cur).decided = some b ↔
      t + 1 ≤ proposalCount prop S b := by
  have not_both : ¬ (t + 1 ≤ proposalCount prop S true ∧ t + 1 ≤ proposalCount prop S false) := by
    rintro ⟨ht, hf⟩
    obtain ⟨j₁, _, hj₁⟩ := (proposalCount_pos_iff prop S true).mp (by omega)
    obtain ⟨j₂, _, hj₂⟩ := (proposalCount_pos_iff prop S false).mp (by omega)
    cases huniq j₁ j₂ true false hj₁ hj₂
  cases b
  · simp only [stage2Update, hd]
    split_ifs with ht hf
    · exact ⟨(fun h => nomatch h), fun hf' => (not_both ⟨ht, hf'⟩).elim⟩
    · exact ⟨fun _ => hf, fun _ => rfl⟩
    · exact ⟨(fun h => nomatch h), fun hf' => (hf hf').elim⟩
  · simp only [stage2Update, hd]
    split_ifs with ht hf
    · exact ⟨fun _ => ht, fun _ => rfl⟩
    · exact ⟨(fun h => nomatch h), fun ht' => (ht ht').elim⟩
    · exact ⟨(fun h => nomatch h), fun ht' => (ht ht').elim⟩

/-- Execute one two-stage phase of Ben-Or's protocol on global state `st` under quorum-phase
schedule `sched` and coin assignment `coins`. -/
@[expose] def phaseStep {P : Type*} [Fintype P] (t : ℕ) (sched : PhaseSchedule P)
    (coins : P → Bool) (st : P → ProcState) (p : P) : ProcState :=
  stage2Update t (fun j => stage1Proposal st (sched.q1 j)) (sched.q2 p) (coins p) (st p)

/-- Execute `r` phases of Ben-Or's protocol from initial inputs `inp` under schedule sequence
`sched` and coin sequence `coins`. -/
@[expose] def run {P : Type*} [Fintype P] (t : ℕ) (sched : ℕ → PhaseSchedule P)
    (coins : ℕ → P → Bool) (inp : P → Bool) : ℕ → P → ProcState
  | 0 => initState inp
  | r + 1 => phaseStep t (sched r) (coins r) (run t sched coins inp r)

/-- Execute `r` phases against an adaptive state-based scheduler `strat` that inspects the global
state at the start of each phase before choosing that phase's quorums. -/
@[expose] def adaptiveRun {P : Type*} [Fintype P] (t : ℕ)
    (strat : ℕ → (P → ProcState) → PhaseSchedule P)
    (coins : ℕ → P → Bool) (inp : P → Bool) : ℕ → P → ProcState
  | 0 => initState inp
  | r + 1 =>
    let st := adaptiveRun t strat coins inp r
    phaseStep t (strat r st) (coins r) st

/-- An adaptive scheduler produces the same trace as the fixed schedule sequence of quorums it
chooses along the run. -/
theorem adaptiveRun_eq_run {P : Type*} [Fintype P] (t : ℕ)
    (strat : ℕ → (P → ProcState) → PhaseSchedule P)
    (coins : ℕ → P → Bool) (inp : P → Bool) :
    ∀ r, adaptiveRun t strat coins inp r =
      run t (fun k => strat k (adaptiveRun t strat coins inp k)) coins inp r
  | 0 => rfl
  | r + 1 => by
    simp only [adaptiveRun, run]
    rw [← adaptiveRun_eq_run t strat coins inp r]

/-- Every process currently carries the same binary estimate. -/
@[expose] def IsUnanimous {P : Type*} (st : P → ProcState) : Prop :=
  ∃ b : Bool, ∀ p : P, (st p).est = b

/-- Every process has decided, and all decided values coincide. -/
@[expose] def AllDecided {P : Type*} (st : P → ProcState) : Prop :=
  ∃ b : Bool, ∀ p : P, (st p).decided = some b

/-! ### Lucky coin, unanimous progress, lock-in, and deterministic safety -/

/-- **Lucky-coin alignment:** for any state `st` and schedule `sched` (even without quorum size
bounds), there exists a bit `b : Bool` such that if every process's coin in this phase equals `b`,
every process ends the phase with estimate `b`. -/
theorem phaseStep_lucky_coin {P : Type*} [Fintype P] (t : ℕ) (sched : PhaseSchedule P)
    (st : P → ProcState) :
    ∃ b : Bool, ∀ p : P, (phaseStep t sched (fun _ => b) st p).est = b := by
  classical
  let prop : P → Option Bool := fun j => stage1Proposal st (sched.q1 j)
  have huniq : ∀ j₁ j₂ b₁ b₂, prop j₁ = some b₁ → prop j₂ = some b₂ → b₁ = b₂ :=
    fun j₁ j₂ _ _ h₁ h₂ => stage1Proposal_unique st (sched.q1 j₁) (sched.q1 j₂) h₁ h₂
  by_cases hex : ∃ j b, prop j = some b
  · obtain ⟨j₀, b, hjb⟩ := hex
    refine ⟨b, fun p => ?_⟩
    by_cases hp : ∃ j ∈ sched.q2 p, ∃ b', prop j = some b'
    · obtain ⟨j, hjS, b', hjb'⟩ := hp
      have hbb' : b' = b := huniq j j₀ b' b hjb' hjb
      subst hbb'
      exact stage2Update_est_of_unique huniq ⟨j, hjS, hjb'⟩
    · have hnone : ∀ j ∈ sched.q2 p, prop j = none := fun j hj =>
        Option.eq_none_iff_forall_ne_some.mpr fun b' hb' => hp ⟨j, hj, b', hb'⟩
      exact stage2Update_est_of_all_none hnone
  · refine ⟨false, fun p => ?_⟩
    have hnone : ∀ j ∈ sched.q2 p, prop j = none := fun j _ =>
      Option.eq_none_iff_forall_ne_some.mpr fun b' hb' => hex ⟨j, b', hb'⟩
    exact stage2Update_est_of_all_none hnone

/-- From any state where all processes hold estimate `b`, one valid phase preserves estimate `b` on
every process and sets every undecided process's decision register to `some b`, independent of
`coins`. -/
theorem phaseStep_of_est_eq {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) (hv : sched.Valid t) (coins : P → Bool)
    {st : P → ProcState} {b : Bool} (hest : ∀ p, (st p).est = b) (p : P) :
    (phaseStep t sched coins st p).est = b ∧
      ((st p).decided = none → (phaseStep t sched coins st p).decided = some b) := by
  let prop : P → Option Bool := fun j => stage1Proposal st (sched.q1 j)
  have hprop : ∀ j, prop j = some b := fun j =>
    stage1Proposal_of_forall_est ht (hv.card_q1 j) (fun k _ => hest k)
  have huniq : ∀ j₁ j₂ b₁ b₂, prop j₁ = some b₁ → prop j₂ = some b₂ → b₁ = b₂ := by
    intro j₁ j₂ b₁ b₂ h₁ h₂
    rw [hprop j₁, Option.some.injEq] at h₁
    rw [hprop j₂, Option.some.injEq] at h₂
    exact h₁.symm.trans h₂
  have hcnt : proposalCount prop (sched.q2 p) b = (sched.q2 p).card := by
    simp only [proposalCount, hprop, Finset.filter_true]
  have hge : t + 1 ≤ proposalCount prop (sched.q2 p) b := by
    rw [hcnt]; exact (add_one_le_sub ht).trans (hv.card_q2 p)
  have hex : ∃ j ∈ sched.q2 p, prop j = some b :=
    (proposalCount_pos_iff prop (sched.q2 p) b).mp (by omega)
  refine ⟨stage2Update_est_of_unique huniq hex, fun hd => ?_⟩
  exact (stage2Update_decided_eq_some_iff_of_none huniq hd b).mpr hge

/-- `IsUnanimous` is preserved across any valid phase under arbitrary coins. -/
theorem IsUnanimous.phaseStep {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    {st : P → ProcState} (hu : IsUnanimous st) (ht : 2 * t < Fintype.card P)
    (hv : sched.Valid t) (coins : P → Bool) :
    IsUnanimous (BenOr.phaseStep t sched coins st) := by
  obtain ⟨b, hb⟩ := hu
  exact ⟨b, fun p => (phaseStep_of_est_eq ht hv coins hb p).1⟩

/-- **Single-phase lock-in:** if process `p` newly decides `b` in Stage 2 of a valid phase (when
`2 * t < |P|`), then **every** process `q` adopts next estimate `b` in that phase, regardless of
`coins`. -/
theorem phaseStep_lock_in {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) (hv : sched.Valid t) {coins : P → Bool}
    {st : P → ProcState} {p : P} {b : Bool}
    (hnone : (st p).decided = none)
    (hdec : (phaseStep t sched coins st p).decided = some b) (q : P) :
    (phaseStep t sched coins st q).est = b := by
  classical
  let prop : P → Option Bool := fun j => stage1Proposal st (sched.q1 j)
  have huniq : ∀ j₁ j₂ b₁ b₂, prop j₁ = some b₁ → prop j₂ = some b₂ → b₁ = b₂ :=
    fun j₁ j₂ _ _ h₁ h₂ => stage1Proposal_unique st (sched.q1 j₁) (sched.q1 j₂) h₁ h₂
  have hcnt : t + 1 ≤ proposalCount prop (sched.q2 p) b :=
    (stage2Update_decided_eq_some_iff_of_none huniq hnone b).mp hdec
  have hQ : Fintype.card P - t ≤ (sched.q2 q).card := hv.card_q2 q
  obtain ⟨j, hj⟩ : ∃ j, j ∈ ((sched.q2 p).filter fun j => prop j = some b) ∩ sched.q2 q := by
    finset_card [proposalCount]
  rw [Finset.mem_inter, Finset.mem_filter] at hj
  exact stage2Update_est_of_unique huniq ⟨j, hj.2, hj.1.2⟩

private lemma phaseStep_decided_stable {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    {coins : P → Bool} {st : P → ProcState} {p : P} {b : Bool}
    (hd : (st p).decided = some b) :
    (phaseStep t sched coins st p).decided = some b :=
  stage2Update_decided_of_some hd

private lemma run_decided_stable_add {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    {coins : ℕ → P → Bool} {inp : P → Bool} {r₁ : ℕ} {p : P} {b : Bool}
    (hd : (run t sched coins inp r₁ p).decided = some b) :
    ∀ d : ℕ, (run t sched coins inp (r₁ + d) p).decided = some b
  | 0 => hd
  | d + 1 => phaseStep_decided_stable (run_decided_stable_add hd d)

/-- Write-once monotonicity of `decided` across any number of phases. -/
theorem run_decided_stable {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    {coins : ℕ → P → Bool} {inp : P → Bool} {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) {p : P} {b : Bool}
    (hd : (run t sched coins inp r₁ p).decided = some b) :
    (run t sched coins inp r₂ p).decided = some b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  exact run_decided_stable_add hd d

/-- Lock invariant: whenever any process has decided `b`, every process carries estimate `b`.
Preserved across all valid phases once `2 * t < |P|`. -/
@[expose] def EstimateLocked {P : Type*} (st : P → ProcState) : Prop :=
  ∀ p b, (st p).decided = some b → ∀ q, (st q).est = b

/-- `EstimateLocked` holds vacuously in the initial state before any process has decided. -/
theorem estimateLocked_initState {P : Type*} (inp : P → Bool) :
    EstimateLocked (initState inp) := by
  intro p b hd; cases hd

/-- `EstimateLocked` is preserved across any valid phase when `2 * t < |P|`. -/
theorem EstimateLocked.phaseStep {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    {st : P → ProcState} (hinv : EstimateLocked st)
    (ht : 2 * t < Fintype.card P) (hv : sched.Valid t) (coins : P → Bool) :
    EstimateLocked (BenOr.phaseStep t sched coins st) := by
  intro p b hd q
  cases hcur : (st p).decided with
  | none => exact phaseStep_lock_in ht hv hcur hd q
  | some d =>
    have hprev := phaseStep_decided_stable (sched := sched) (coins := coins) (t := t) hcur
    rw [hd] at hprev; cases hprev
    exact (phaseStep_of_est_eq ht hv coins (hinv p b hcur) q).1

private lemma estimateLocked_run {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) (coins : ℕ → P → Bool) (inp : P → Bool) :
    ∀ r, (∀ k < r, (sched k).Valid t) → EstimateLocked (run t sched coins inp r)
  | 0, _ => estimateLocked_initState inp
  | r + 1, hv =>
    (estimateLocked_run ht coins inp r (fun k hk => hv k (Nat.lt_succ_of_lt hk))).phaseStep
      ht (hv r (Nat.lt_succ_self r)) (coins r)

/-- When `EstimateLocked st` holds and all processes share estimate `b`, one valid phase leaves
every process with `decided = some b`. -/
theorem phaseStep_allDecided_of_est_eq {P : Type*} [Fintype P] {t : ℕ} {sched : PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) (hv : sched.Valid t) (coins : P → Bool)
    {st : P → ProcState} (hlock : EstimateLocked st)
    {b : Bool} (hest : ∀ p, (st p).est = b) (p : P) :
    (phaseStep t sched coins st p).decided = some b := by
  cases hd : (st p).decided with
  | none => exact (phaseStep_of_est_eq ht hv coins hest p).2 hd
  | some d =>
    have hdb : b = d := (hest p).symm.trans (hlock p d hd p)
    subst hdb
    exact phaseStep_decided_stable hd

/-- **Quorum-phase unanimous validity** (quorum-phase counterpart of Theorem 1(ii), [BenOr1983],
§3, printed p. 29): if all processes start with input `b`, every process decides `b` after phase
`0` (`r = 1`), without depending on any coin value. -/
theorem run_validity {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) (hv₀ : (sched 0).Valid t) (coins : ℕ → P → Bool)
    {inp : P → Bool} {b : Bool} (hinp : ∀ p, inp p = b) (p : P) :
    (run t sched coins inp 1 p).decided = some b :=
  (phaseStep_of_est_eq ht hv₀ (coins 0) hinp p).2 rfl

/-- **Quorum-phase next-phase global decision** (quorum-phase counterpart of Theorem 1(iii),
[BenOr1983], §3, printed p. 29): once any process `p` has decided `b` by phase `r`, every process
`q` has decided `b` by phase `r + 1`. -/
theorem run_decide_next_phase {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) {r : ℕ} (hv : ∀ k ≤ r, (sched k).Valid t)
    {coins : ℕ → P → Bool} {inp : P → Bool} {p : P} {b : Bool}
    (hd : (run t sched coins inp r p).decided = some b) (q : P) :
    (run t sched coins inp (r + 1) q).decided = some b := by
  have hlock := estimateLocked_run ht coins inp r (fun k hk => hv k (Nat.le_of_lt hk))
  exact phaseStep_allDecided_of_est_eq ht (hv r le_rfl) (coins r) hlock (hlock p b hd) q

/-- **Cross-phase agreement:** in any valid execution with `2 * t < |P|` and arbitrary coins, no
two processes ever decide different values, whether in the same phase or in different phases. -/
theorem run_agreement {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) {r₁ r₂ : ℕ}
    (hv : ∀ k < max r₁ r₂, (sched k).Valid t)
    {coins : ℕ → P → Bool} {inp : P → Bool} {p₁ p₂ : P} {b₁ b₂ : Bool}
    (hd₁ : (run t sched coins inp r₁ p₁).decided = some b₁)
    (hd₂ : (run t sched coins inp r₂ p₂).decided = some b₂) :
    b₁ = b₂ := by
  have hd₁' := run_decided_stable (Nat.le_max_left r₁ r₂) hd₁
  have hd₂' := run_decided_stable (Nat.le_max_right r₁ r₂) hd₂
  have hlock := estimateLocked_run ht coins inp (max r₁ r₂) hv
  exact (hlock p₁ b₁ hd₁' p₁).symm.trans (hlock p₂ b₂ hd₂' p₁)

/-- **Input integrity (strong binary validity):** whenever any process decides `b` in any phase,
at least one process started with initial input `b`. -/
theorem run_exists_inp_eq_of_decided {P : Type*} [Fintype P] {t : ℕ} {sched : ℕ → PhaseSchedule P}
    (ht : 2 * t < Fintype.card P) {r : ℕ} (hv : ∀ k < r, (sched k).Valid t)
    {coins : ℕ → P → Bool} {inp : P → Bool} {p : P} {b : Bool}
    (hd : (run t sched coins inp r p).decided = some b) :
    ∃ q : P, inp q = b := by
  rcases r with _ | r
  · cases hd
  · have hpos : 0 < Fintype.card P := by omega
    obtain ⟨q₀⟩ := Fintype.card_pos_iff.mp hpos
    by_cases hunan : ∀ q : P, inp q = inp q₀
    · have hdec₀ := run_validity ht (hv 0 (Nat.zero_lt_succ r)) coins hunan p
      have heq := run_agreement ht (r₁ := 1) (r₂ := r + 1)
        (fun k hk => hv k (by omega)) hdec₀ hd
      exact ⟨q₀, heq⟩
    · have hex : ∃ q₁, inp q₁ ≠ inp q₀ := by
        by_contra hall
        exact hunan fun q => Classical.not_not.mp fun hne => hall ⟨q, hne⟩
      obtain ⟨q₁, hq₁⟩ := hex
      cases hb : b <;> cases h0 : inp q₀ <;> cases h1 : inp q₁
      · exact ⟨q₀, h0⟩
      · exact ⟨q₀, h0⟩
      · exact ⟨q₁, h1⟩
      · exact (hq₁ (h1.trans h0.symm)).elim
      · exact (hq₁ (h1.trans h0.symm)).elim
      · exact ⟨q₁, h1⟩
      · exact ⟨q₀, h0⟩
      · exact ⟨q₀, h0⟩

/-! ### Dynamic mid-stage crash simulation and uniform agreement -/

/-- Phased schedule with cumulative mid-stage crashes: `crashed1 r` is the set of
processes that have crashed before completing Stage 1 of phase `r`, and `crashed2 r` is the set of
processes that have crashed before completing Stage 2 of phase `r`. Crashed processes stop sending
in subsequent stages and freeze their local state. -/
structure CrashSchedule (P : Type*) where
  /-- Cumulative processes crashed prior to completing Stage 1 of phase `r`. -/
  crashed1 : ℕ → Finset P
  /-- Cumulative processes crashed prior to completing Stage 2 of phase `r`. -/
  crashed2 : ℕ → Finset P
  /-- Stage-1 sender quorums for processes completing Stage 1 of phase `r`. -/
  q1 : ℕ → P → Finset P
  /-- Stage-2 sender quorums for processes completing Stage 2 of phase `r`. -/
  q2 : ℕ → P → Finset P

/-- Validity of a dynamic crash schedule for fault bound `t`: crashes grow monotonically with at
most `t` crashes in any phase, surviving processes receive at least `|P| - t` messages per stage,
Stage-1 quorums in phase `r + 1` exclude processes already crashed in phase `r`, and Stage-2
quorums exclude processes crashed before completing Stage 1. -/
structure CrashSchedule.Valid {P : Type*} [Fintype P] (cs : CrashSchedule P) (t : ℕ) : Prop where
  /-- Processes crashed before Stage 1 remain crashed through Stage 2. -/
  crashed1_subset : ∀ r, cs.crashed1 r ⊆ cs.crashed2 r
  /-- Processes crashed in phase `r` remain crashed in phase `r + 1`. -/
  crashed2_subset : ∀ r, cs.crashed2 r ⊆ cs.crashed1 (r + 1)
  /-- At most `t` processes crash in total by Stage 2 of any phase. -/
  card_crashed2 : ∀ r, (cs.crashed2 r).card ≤ t
  /-- Surviving Stage-1 recipients collect at least `|P| - t` reports. -/
  card_q1 : ∀ r, ∀ p ∉ cs.crashed1 r, Fintype.card P - t ≤ (cs.q1 r p).card
  /-- Surviving Stage-2 recipients collect at least `|P| - t` proposals. -/
  card_q2 : ∀ r, ∀ p ∉ cs.crashed2 r, Fintype.card P - t ≤ (cs.q2 r p).card
  /-- Stage-1 quorums in phase `r + 1` exclude senders that crashed in phase `r`. -/
  disjoint_q1 : ∀ r, ∀ p ∉ cs.crashed1 (r + 1), Disjoint (cs.q1 (r + 1) p) (cs.crashed2 r)
  /-- Stage-2 quorums exclude senders that crashed before completing Stage 1. -/
  disjoint_q2 : ∀ r, ∀ p ∉ cs.crashed2 r, Disjoint (cs.q2 r p) (cs.crashed1 r)

/-- One phase of Ben-Or's protocol with mid-stage crashes: processes in `crashed1` emit no Stage-2
proposal, and processes in `crashed2` freeze their local state (including any prior decision). -/
@[expose] def crashStep {P : Type*} [Fintype P] [DecidableEq P] (t : ℕ)
    (crashed1 crashed2 : Finset P) (q1 q2 : P → Finset P)
    (coins : P → Bool) (st : P → ProcState) (p : P) : ProcState :=
  if p ∈ crashed2 then st p
  else
    let prop : P → Option Bool := fun j =>
      if j ∈ crashed1 then none else stage1Proposal st (q1 j)
    stage2Update t prop (q2 p) (coins p) (st p)

/-- Execute `r` phases under a dynamic mid-stage crash schedule `cs`. -/
@[expose] def crashRun {P : Type*} [Fintype P] [DecidableEq P] (t : ℕ) (cs : CrashSchedule P)
    (coins : ℕ → P → Bool) (inp : P → Bool) : ℕ → P → ProcState
  | 0 => initState inp
  | r + 1 => crashStep t (cs.crashed1 r) (cs.crashed2 r) (cs.q1 r) (cs.q2 r) (coins r)
      (crashRun t cs coins inp r)

/-- Total `PhaseSchedule` sequence extending `cs` by assigning the surviving set `univ \ crashed2 r`
as a dummy quorum for already-crashed processes (whose states no surviving recipient ever reads). -/
@[expose] def CrashSchedule.toSchedule {P : Type*} [Fintype P] [DecidableEq P]
    (cs : CrashSchedule P) (r : ℕ) : PhaseSchedule P where
  q1 p := if p ∈ cs.crashed1 r then Finset.univ \ cs.crashed2 r else cs.q1 r p
  q2 p := if p ∈ cs.crashed2 r then Finset.univ \ cs.crashed2 r else cs.q2 r p

/-- Extending a valid dynamic crash schedule via `toSchedule` yields a valid `PhaseSchedule` in
every phase. -/
theorem CrashSchedule.Valid.valid_toSchedule {P : Type*} [Fintype P] [DecidableEq P]
    {cs : CrashSchedule P} {t : ℕ} (hv : cs.Valid t) (r : ℕ) :
    (cs.toSchedule r).Valid t := by
  have hsdiff : Fintype.card P - t ≤ (Finset.univ \ cs.crashed2 r).card := by
    finset_card [hv.card_crashed2 r]
  refine ⟨fun p => ?_, fun p => ?_⟩ <;> simp only [toSchedule]
  · split_ifs with hp
    · exact hsdiff
    · exact hv.card_q1 r p hp
  · split_ifs with hp
    · exact hsdiff
    · exact hv.card_q2 r p hp

private lemma crashStep_eq_phaseStep_toSchedule {P : Type*} [Fintype P] [DecidableEq P]
    {t : ℕ} {cs : CrashSchedule P} {r : ℕ} {coins : P → Bool}
    {stC stR : P → ProcState} {p : P} (hp2 : p ∉ cs.crashed2 r)
    (hd2 : Disjoint (cs.q2 r p) (cs.crashed1 r))
    (hpEq : stC p = stR p)
    (hq1Eq : ∀ j ∉ cs.crashed1 r, ∀ k ∈ cs.q1 r j, stC k = stR k) :
    crashStep t (cs.crashed1 r) (cs.crashed2 r) (cs.q1 r) (cs.q2 r) coins stC p =
      phaseStep t (cs.toSchedule r) coins stR p := by
  have hprop : ∀ j ∈ cs.q2 r p,
      (if j ∈ cs.crashed1 r then none else stage1Proposal stC (cs.q1 r j)) =
        stage1Proposal stR ((cs.toSchedule r).q1 j) := by
    intro j hj
    have hj1 : j ∉ cs.crashed1 r := Finset.disjoint_left.mp hd2 hj
    simp only [CrashSchedule.toSchedule, hj1, ↓reduceIte]
    have hrc : ∀ b, reportCount stC (cs.q1 r j) b = reportCount stR (cs.q1 r j) b := by
      intro b
      simp only [reportCount]
      congr 1
      exact Finset.filter_congr fun k hk => by rw [hq1Eq j hj1 k hk]
    simp only [stage1Proposal, hrc]
  have hfilt (b : Bool) :
      proposalCount (fun j => if j ∈ cs.crashed1 r then none else stage1Proposal stC (cs.q1 r j))
        (cs.q2 r p) b =
      proposalCount (fun j => stage1Proposal stR ((cs.toSchedule r).q1 j))
        ((cs.toSchedule r).q2 p) b := by
    have hq2 : (cs.toSchedule r).q2 p = cs.q2 r p := ite_eq_right hp2
    rw [hq2]
    refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
    dsimp only
    rw [hprop j hj]
  simp only [crashStep, phaseStep, hp2, ↓reduceIte, hpEq, stage2Update, hfilt]

/-- **Dynamic crash simulation:** at phase `0` on all processes, and after phase `r + 1` on every
process `p ∉ cs.crashed2 r`, `crashRun` coincides identically with `run` on `cs.toSchedule`. -/
theorem crashRun_eq_run {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {cs : CrashSchedule P}
    (hv : cs.Valid t) (coins : ℕ → P → Bool) (inp : P → Bool) :
    (∀ p, crashRun t cs coins inp 0 p = run t cs.toSchedule coins inp 0 p) ∧
    ∀ r, ∀ p ∉ cs.crashed2 r,
      crashRun t cs coins inp (r + 1) p = run t cs.toSchedule coins inp (r + 1) p := by
  refine ⟨fun _ => rfl, ?_⟩
  intro r
  induction r with
  | zero =>
    intro p hp2
    exact crashStep_eq_phaseStep_toSchedule hp2 (hv.disjoint_q2 0 p hp2) rfl (fun _ _ _ _ => rfl)
  | succ r ih =>
    intro p hp2
    have hpPrev : p ∉ cs.crashed2 r :=
      fun h => hp2 (hv.crashed1_subset (r + 1) (hv.crashed2_subset r h))
    exact crashStep_eq_phaseStep_toSchedule hp2 (hv.disjoint_q2 (r + 1) p hp2) (ih p hpPrev)
      (fun j hj1 k hk => ih k (Finset.disjoint_left.mp (hv.disjoint_q1 r j hj1) hk))

private lemma crashRun_decided_origin {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
    {cs : CrashSchedule P} (hv : cs.Valid t) {coins : ℕ → P → Bool} {inp : P → Bool}
    {r : ℕ} {p : P} {b : Bool} (hd : (crashRun t cs coins inp r p).decided = some b) :
    ∃ r₀ < r, p ∉ cs.crashed2 r₀ ∧
      (run t cs.toSchedule coins inp (r₀ + 1) p).decided = some b := by
  induction r with
  | zero => cases hd
  | succ r ih =>
    by_cases hp : p ∈ cs.crashed2 r
    · simp only [crashRun, crashStep, hp, ↓reduceIte] at hd
      obtain ⟨r₀, hr₀, hnp, hrun⟩ := ih hd
      exact ⟨r₀, Nat.lt_succ_of_lt hr₀, hnp, hrun⟩
    · refine ⟨r, Nat.lt_succ_self r, hp, ?_⟩
      rw [← (crashRun_eq_run hv coins inp).2 r p hp]
      exact hd

/-- **Uniform agreement under dynamic crashes:** even if a process decides in some phase and
immediately crashes afterward, its decision agrees with the decision of every other process across
all phases. -/
theorem crashRun_agreement {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {cs : CrashSchedule P}
    (ht : 2 * t < Fintype.card P) (hv : cs.Valid t)
    {coins : ℕ → P → Bool} {inp : P → Bool} {r₁ r₂ : ℕ} {p₁ p₂ : P} {b₁ b₂ : Bool}
    (hd₁ : (crashRun t cs coins inp r₁ p₁).decided = some b₁)
    (hd₂ : (crashRun t cs coins inp r₂ p₂).decided = some b₂) :
    b₁ = b₂ := by
  obtain ⟨k₁, _, _, hrun₁⟩ := crashRun_decided_origin hv hd₁
  obtain ⟨k₂, _, _, hrun₂⟩ := crashRun_decided_origin hv hd₂
  exact run_agreement ht (fun k _ => hv.valid_toSchedule k) hrun₁ hrun₂

/-! ### Non-termination under deterministic static coin fallbacks (`Fin 3, t = 1`) -/

/-- Adversarial quorum-phase schedule on `Fin 3` (`t = 1`, quorum size `2 = 3 - 1`, zero crashes):
processes `1` and `2` always observe one `some` proposal from `1` (adopting it without reaching
the decision threshold `2`), while process `0` observes two `none` proposals and invokes its
fallback coin. -/
private def fin3SplitSchedule : PhaseSchedule (Fin 3) where
  q1
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {0, 2}
  q2
    | 0 => {0, 2}
    | 1 => {1, 2}
    | 2 => {1, 2}

private lemma valid_fin3SplitSchedule : fin3SplitSchedule.Valid 1 :=
  ⟨by decide, by decide⟩

private def fin3SplitInput (c₀ : Bool) : Fin 3 → Bool
  | 0 => c₀
  | 1 => !c₀
  | 2 => !c₀

private lemma phaseStep_fin3SplitSchedule_three :
    ∀ (c₀ c₁ c₂ : Bool) (p : Fin 3),
      phaseStep 1 fin3SplitSchedule
          (fun i => if i = 0 then c₀ else if i = 1 then c₁ else c₂)
          (initState (fin3SplitInput c₀)) p =
        initState (fin3SplitInput c₀) p := by
  decide

private lemma phaseStep_fin3SplitSchedule_fixed (fallback : Fin 3 → Bool) :
    phaseStep 1 fin3SplitSchedule fallback (initState (fin3SplitInput (fallback 0))) =
      initState (fin3SplitInput (fallback 0)) := by
  have hfb : fallback = fun i : Fin 3 =>
      if i = 0 then fallback 0 else if i = 1 then fallback 1 else fallback 2 := by
    funext ⟨k, hk⟩
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  funext p
  conv_lhs => rw [hfb]
  exact phaseStep_fin3SplitSchedule_three (fallback 0) (fallback 1) (fallback 2) p

/-- **Necessity of fresh randomization (`Fin 3, t = 1`):** for every static deterministic coin
fallback `fallback : Fin 3 → Bool`, there exist an input assignment `inp` and a valid crash-free
quorum-phase schedule `sched` (`sched.Valid 1`) such that **no process ever decides** in any phase
`r : ℕ`. -/
theorem exists_nonterminating_of_fixed_coin (fallback : Fin 3 → Bool) :
    ∃ (inp : Fin 3 → Bool) (sched : PhaseSchedule (Fin 3)),
      sched.Valid 1 ∧
        ∀ (r : ℕ) (p : Fin 3),
          (run 1 (fun _ => sched) (fun _ => fallback) inp r p).decided = none := by
  refine ⟨fin3SplitInput (fallback 0), fin3SplitSchedule, valid_fin3SplitSchedule, ?_⟩
  have hfix : ∀ r : ℕ,
      run 1 (fun _ => fin3SplitSchedule) (fun _ => fallback) (fin3SplitInput (fallback 0)) r =
        initState (fin3SplitInput (fallback 0)) := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [run, ih]
      exact phaseStep_fin3SplitSchedule_fixed fallback
  intro r p
  rw [hfix r]
  rfl

end Cslib.Distributed.BenOr
