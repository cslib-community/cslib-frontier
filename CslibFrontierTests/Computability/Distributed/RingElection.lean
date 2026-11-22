/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.RingElection.Anonymous
import CslibFrontier.Computability.Distributed.RingElection.ChangRoberts
import CslibFrontier.Computability.Distributed.RingElection.Peterson
import Mathlib.Tactic.NormNum

/-! Ring leader-election steps (checked as a `module` client with ordinary imports):
1. Rotational symmetry steps on anonymous rings `Fin 3` (steps towards `[Angluin1980b]`) in both
   synchronous bidirectional/unidirectional models (`AnonProtocol`) and asynchronous FIFO models
   (`AnonAsyncProtocol`), demonstrating rotational symmetry preservation (`card ∈ {0, 3} ≠ 1`) even
   when the ring size `n = 3` is baked into the protocol;
2. Simultaneous all-initiator unidirectional FIFO ring election steps (steps towards
   `[ChangRoberts1979]`): concrete asynchronous FIFO execution on `Fin 5` attaining `15 = 5 * 6 / 2`
   messages on `Fin.rev` and `9 = 2 * 5 - 1` on `id`, exact `n H_n` permutation-average checks on
   `Fin 3` (`11 / 2`) and `Fin 4` (`25 / 3`), and instantiations of safety, termination, worst-case,
   and average-case steps;
3. All-initially-active basic two-hop unidirectional FIFO ring election steps (steps towards
   `[Peterson1982]`): concrete runs on `Fin 1`, `Fin 6`, and `Fin 8` (`Fin.rev` taking `24 < 36`
   messages, beating `crAllInitTotalMsgs`, and bit-reversal `[0, 4, 2, 6, 1, 5, 3, 7]` halving
   `8 → 4 → 2 → 1` across `3 = log₂ 8` phases in `56 = 2 * 8 * 3 + 8` messages under two distinct
   asynchronous FIFO schedules), together with step theorem instantiations. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.RingElection

open Cslib Cslib.Distributed.RingElection

/-! ### 1. Rotational symmetry steps on anonymous rings (`Fin 3`, synchronous & asynchronous) -/

/-- Synchronous bidirectional anonymous protocol tuned specifically for `n = 3`: every node counts
rounds while combining messages from both neighbours, declaring leadership once `10 ≤ s`. -/
def anonRing3Proto : AnonProtocol ℕ ℕ where
  init := 0
  toPred r s := s + r + 1
  toSucc _ s := 2 * s + 1
  recv _ s mPred mSucc := s + mPred + mSucc
  isLeader s := decide (10 ≤ s)

-- Before threshold, `0` nodes lead; once threshold is reached, ALL `3` nodes lead simultaneously.
example : (anonRing3Proto.leaders 3 0).card = 0 := by decide
example : (anonRing3Proto.leaders 3 1).card = 0 := by decide
example : (anonRing3Proto.leaders 3 2).card = 3 := by decide
example : (List.finRange 3).map (anonRing3Proto.run 3 2) = [11, 11, 11] := by decide

-- Unidirectional anonymous protocol (`AnonProtocol.unidir`) on `Fin 3` also yields `0` or `3`.
def anonUnidir3Proto : AnonProtocol ℕ ℕ :=
  AnonProtocol.unidir 1 (fun r s => s + r) (fun _ s m => s + m) (fun s => decide (4 ≤ s))

example : (anonUnidir3Proto.leaders 3 1).card = 0 ∧ (anonUnidir3Proto.leaders 3 2).card = 3 := by
  decide

-- Synchronous symmetry step instantiated on `Fin 3` and for arbitrary state/message types.
example (r : ℕ) : ¬ anonRing3Proto.ElectsUniqueLeader 3 r :=
  anonRing3Proto.not_electsUniqueLeader_sync_of_two_le (by decide) r

example (P : AnonProtocol ℕ String) (r : ℕ) : ¬ P.ElectsUniqueLeader 3 r :=
  P.not_electsUniqueLeader_sync_of_two_le (by decide) r

example (P : AnonProtocol ℕ ℕ) (r : ℕ) (i k : Fin 5) : P.run 5 r (i + k) = P.run 5 r i :=
  P.state_shift_eq 5 r i k

/-- Asynchronous bidirectional anonymous protocol on `Fin 3` injecting messages both ways. -/
def anonAsync3Proto : AnonAsyncProtocol ℕ ℕ where
  init := 0
  initToPred := [1]
  initToSucc := [2]
  recvFromPred s m := ⟨s + m, [], if s == 0 then [m + 1] else []⟩
  recvFromSucc s m := ⟨s + 2 * m, [], []⟩
  isLeader s := decide (4 ≤ s)

-- Delivering `clockwiseWave 3` then `counterWave 3` preserves exact rotational uniformity.
example : (anonAsync3Proto.configLeaders
    (anonAsync3Proto.exec (anonAsync3Proto.initConfig 3) (clockwiseWave 3))).card = 0 := by
  decide

example : (anonAsync3Proto.configLeaders
    (anonAsync3Proto.exec (anonAsync3Proto.initConfig 3)
      (rotSchedule 3 [.clockwise, .counter]))).card = 3 := by
  decide

-- Shifting the global state after any `rotSchedule` leaves node states and FIFO queues identical.
example :
    let cfg := anonAsync3Proto.exec (anonAsync3Proto.initConfig 3)
      (rotSchedule 3 [.clockwise, .counter, .clockwise])
    (List.finRange 3).map (cfg.shift 1).node = (List.finRange 3).map cfg.node := by
  decide

-- Asynchronous shift equivariance and rotational-wave symmetry step on `Fin 3`.
example (sched : List (AnonEvent 3)) (k : Fin 3) :
    anonAsync3Proto.exec ((anonAsync3Proto.initConfig 3).shift k) sched =
      (anonAsync3Proto.exec (anonAsync3Proto.initConfig 3)
        (sched.map (AnonEvent.shift k))).shift k :=
  anonAsync3Proto.exec_shift_eq (anonAsync3Proto.initConfig 3) k sched

example (W : ℕ) :
    ∃ sched cfg,
      (anonAsync3Proto.lts 3).MTr (anonAsync3Proto.initConfig 3) sched cfg ∧
      (W * 3 ≤ sched.length ∨ (anonAsync3Proto.lts 3).IsTerminal cfg) ∧
      (anonAsync3Proto.configLeaders cfg).card ≠ 1 :=
  anonAsync3Proto.exists_rotWave_trace_leaders_card_ne_one (by decide) W

/-! ### 2. All-initiator unidirectional FIFO ring election: `n(n + 1)/2`, `2n - 1`, and `n H_n` -/

-- On `Fin 5` with `Fin.rev`, tokens travel `5, 4, 3, 2, 1` hops = `15 = 5 * 6 / 2`.
example : (List.finRange 5).map (crHops (Fin.rev : Fin 5 → Fin 5)) = [5, 4, 3, 2, 1] := by decide
example : crAllInitTotalMsgs (Fin.rev : Fin 5 → Fin 5) = 15 :=
  crAllInit_totalMsgs_rev_eq 5

-- On `Fin 5` with `id`, tokens travel `1, 1, 1, 1, 5` hops = `9 = 2 * 5 - 1`.
example : (List.finRange 5).map (crHops (id : Fin 5 → Fin 5)) = [1, 1, 1, 1, 5] := by decide
example : crAllInitTotalMsgs (id : Fin 5 → Fin 5) = 9 :=
  crAllInit_totalMsgs_id_eq 5

/-- Explicit 15-step asynchronous FIFO schedule draining `Fin.rev` on `Fin 5`. -/
def crWorstSched5 : List (Fin 5) :=
  [0, 1, 2, 3, 4, 0, 2, 3, 4, 0, 3, 4, 0, 4, 0]

/-- Executable boolean check that every step in a `crLTS` schedule is enabled. -/
def crAllEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U) :
    CRConfig n U → List (Fin n) → Bool
  | _, [] => true
  | cfg, target :: rest =>
    (!(cfg.chan (target - 1)).isEmpty) && crAllEnabled uid (crStep uid target cfg) rest

theorem crMTr_of_crAllEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U) :
    ∀ (cfg : CRConfig n U) (sched : List (Fin n)),
      crAllEnabled uid cfg sched = true →
      (crLTS uid).MTr cfg sched (crExec uid cfg sched)
  | _, [], _ => LTS.MTr.refl
  | cfg, target :: rest, h => by
    simp only [crAllEnabled, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at h
    exact LTS.MTr.stepL ⟨h.1, rfl⟩ (crMTr_of_crAllEnabled uid (crStep uid target cfg) rest h.2)

-- Concrete FIFO run on `Fin 5`: `15` messages transmitted, unique leader at node `0` (`uid = 4`).
example :
    let uid := (Fin.rev : Fin 5 → Fin 5)
    let finalCfg := crExec uid (crAllInit uid) crWorstSched5
    crAllEnabled uid (crAllInit uid) crWorstSched5 = true ∧
      crAllInitMsgs uid crWorstSched5 = 15 ∧
      (List.finRange 5).map finalCfg.isLeader = [true, false, false, false, false] ∧
      (List.finRange 5).all (fun i => (finalCfg.chan i).isEmpty) = true := by
  decide

-- Operational bound instantiated on the concrete 15-step trace (`15 ≤ 5 * 6 / 2`).
example : crAllInitMsgs (Fin.rev : Fin 5 → Fin 5) crWorstSched5 ≤ 5 * (5 + 1) / 2 :=
  crAllInit_messages_le Fin.rev_injective
    (crMTr_of_crAllEnabled Fin.rev (crAllInit Fin.rev) crWorstSched5 (by decide))

-- Safety, termination, and complete-run message steps on injective `uid : Fin 5 → ℕ`.
example {uid : Fin 5 → ℕ} (huid : Function.Injective uid) {sched : List (Fin 5)}
    {cfg : CRConfig 5 ℕ} (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) :
    (∀ i, cfg.isLeader i = true → ∀ j, uid j ≤ uid i) ∧
    ((crLTS uid).IsTerminal cfg →
      (∀ i, cfg.isLeader i = true ↔ ∀ j, uid j ≤ uid i) ∧
      crAllInitMsgs uid sched = crAllInitTotalMsgs uid) ∧
    (∃ tail cfg', (crLTS uid).MTr cfg tail cfg' ∧ (crLTS uid).IsTerminal cfg') :=
  ⟨fun _ hi j => crAllInit_isLeader_le huid hmtr hi j,
    fun hterm => ⟨fun i => crAllInit_isLeader_iff_max huid hmtr hterm i,
      (crAllInit_execMsgs_eq_totalMsgs huid hmtr hterm).1⟩,
    (crAllInit_terminates huid).1 sched cfg hmtr⟩

-- Exact `n H_n` permutation-average checks on `Fin 3` (`3 * (1 + 1/2 + 1/3) = 11/2`, sum = 33)
-- and `Fin 4` (`4 * (1 + 1/2 + 1/3 + 1/4) = 25/3`, sum = 200).
example : (∑ σ : Equiv.Perm (Fin 3), crAllInitTotalMsgs (⇑σ)) = 33 := by decide
example : (∑ σ : Equiv.Perm (Fin 4), crAllInitTotalMsgs (⇑σ)) = 200 := by decide

example :
    (∑ σ : Equiv.Perm (Fin 3), (crAllInitTotalMsgs (⇑σ) : ℚ)) / (Nat.factorial 3 : ℚ) =
      11 / 2 := by
  rw [crAllInit_avg_totalMsgs_eq 3]
  have h13 : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [h13]
  norm_num

example :
    (∑ σ : Equiv.Perm (Fin 4), (crAllInitTotalMsgs (⇑σ) : ℚ)) / (Nat.factorial 4 : ℚ) =
      25 / 3 := by
  rw [crAllInit_avg_totalMsgs_eq 4]
  have h14 : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [h14]
  norm_num

/-! ### 3. All-active basic two-hop unidirectional FIFO ring election -/

/-- Executable FIFO scheduler draining up to `fuel` enabled deliveries by scanning `0, …, n - 1`
(or in reverse when `rev = true`, exercising asynchronous schedule independence). -/
def twoHopDrain {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (rev : Bool) :
    ℕ → TwoHopConfig n U → List (Fin n)
  | 0, _ => []
  | fuel + 1, cfg =>
    let order := if rev then (List.finRange n).reverse else List.finRange n
    match order.find? (fun i => !(cfg.chan (i - 1)).isEmpty) with
    | none => []
    | some target => target :: twoHopDrain rev fuel (twoHopStep target cfg)

/-- Executable boolean check that every step in a `twoHopLTS` schedule is enabled. -/
def twoHopAllEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] :
    TwoHopConfig n U → List (Fin n) → Bool
  | _, [] => true
  | cfg, target :: rest =>
    (!(cfg.chan (target - 1)).isEmpty) && twoHopAllEnabled (twoHopStep target cfg) rest

theorem twoHopMTr_of_allEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] :
    ∀ (cfg : TwoHopConfig n U) (sched : List (Fin n)),
      twoHopAllEnabled cfg sched = true →
      (twoHopLTS n U).MTr cfg sched (twoHopExec cfg sched)
  | _, [], _ => LTS.MTr.refl
  | cfg, target :: rest, h => by
    simp only [twoHopAllEnabled, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at h
    exact LTS.MTr.stepL ⟨h.1, rfl⟩ (twoHopMTr_of_allEnabled (twoHopStep target cfg) rest h.2)

-- Base case `Fin 1`: `0` elimination phases, `1` message (`≤ 2 * 1 * 0 + 1 = 1`).
example : twoHopAllActivePhases (id : Fin 1 → Fin 1) = 0 := by decide
example :
    let init := twoHopAllActiveInit (id : Fin 1 → Fin 1)
    let sched := twoHopDrain false 5 init
    twoHopAllEnabled init sched = true ∧
      twoHopAllActiveExecMsgs (id : Fin 1 → Fin 1) sched = 1 ∧
      (twoHopExec init sched).node 0 = .leader 0 := by
  decide

-- On reverse-sorted `Fin 6` (`Fin.rev`), `crAllInitTotalMsgs` is `6 * 7 / 2 = 21`, whereas the
-- all-active basic two-hop protocol finishes in `1` phase sending `2 * 6 * 1 + 6 = 18 < 21`
-- messages (electing node `1` with global maximum `5` shifted by one clockwise peak hop from `0`).
example :
    let uid := (Fin.rev : Fin 6 → Fin 6)
    let init := twoHopAllActiveInit uid
    let sched := twoHopDrain false 30 init
    crAllInitTotalMsgs uid = 21 ∧
      twoHopAllActivePhases uid = 1 ∧
      twoHopAllActiveExecMsgs uid sched = 18 ∧
      (twoHopExec init sched).node 1 = .leader 5 := by
  decide

-- On reverse-sorted `Fin 8` (`Fin.rev`), `crAllInitTotalMsgs` is `8 * 9 / 2 = 36`, whereas the
-- all-active basic two-hop protocol finishes in `1` phase sending `24 < 36` messages.
example :
    let uid := (Fin.rev : Fin 8 → Fin 8)
    let init := twoHopAllActiveInit uid
    let sched := twoHopDrain false 40 init
    crAllInitTotalMsgs uid = 36 ∧
      twoHopAllActivePhases uid = 1 ∧
      twoHopAllActiveExecMsgs uid sched = 24 ∧
      (twoHopExec init sched).node 1 = .leader 7 ∧
      (List.finRange 8).all (fun e => ((twoHopExec init sched).chan e).isEmpty) = true := by
  decide

/-- Bit-reversal identifier assignment on `Fin 8` forcing all `log₂ 8 = 3` halving phases
(`8 → 4 → 2 → 1`). -/
def bitRev8 : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 3
  | ⟨7, _⟩ => 7

-- Active processors halve strictly `8 → 4 → 2 → 1` across `3 = Nat.log 2 8` phases.
example :
    [(twoHopAllActivePhase bitRev8 0).active.card,
     (twoHopAllActivePhase bitRev8 1).active.card,
     (twoHopAllActivePhase bitRev8 2).active.card,
     (twoHopAllActivePhase bitRev8 3).active.card] = [8, 4, 2, 1] ∧
    twoHopAllActivePhases bitRev8 = 3 := by
  decide

-- Forward and reverse asynchronous FIFO schedules on `Fin 8` (`bitRev8`) converge to the exact
-- same quiescent state (`.leader 7` at node `6`, `.relay` elsewhere) with `56 = 2 * 8 * 3 + 8`
-- messages, matching `twoHopAllActive_messages_le` tightly.
example :
    let init := twoHopAllActiveInit bitRev8
    let schedFwd := twoHopDrain false 70 init
    let schedRev := twoHopDrain true 70 init
    let finFwd := twoHopExec init schedFwd
    let finRev := twoHopExec init schedRev
    schedFwd ≠ schedRev ∧
      twoHopAllEnabled init schedFwd = true ∧
      twoHopAllEnabled init schedRev = true ∧
      twoHopAllActiveExecMsgs bitRev8 schedFwd = 56 ∧
      twoHopAllActiveExecMsgs bitRev8 schedRev = 56 ∧
      2 * 8 * Nat.log 2 8 + 8 = 56 ∧
      (List.finRange 8).map finFwd.node = (List.finRange 8).map finRev.node ∧
      finFwd.node 6 = .leader 7 ∧
      (List.finRange 8).all (fun e => (finFwd.chan e).isEmpty) = true := by
  decide

-- Instantiate the all-active basic two-hop step theorems on `bitRev8 : Fin 8 → ℕ`.
theorem bitRev8_injective : Function.Injective bitRev8 := by decide

example (k : ℕ) (hk : 2 ≤ (twoHopAllActivePhase bitRev8 k).active.card) :
    2 * (twoHopAllActivePhase bitRev8 (k + 1)).active.card ≤
      (twoHopAllActivePhase bitRev8 k).active.card :=
  twoHopAllActive_phase_halving bitRev8 k hk

example : twoHopAllActivePhases bitRev8 ≤ Nat.log 2 8 :=
  (twoHopAllActive_phases_le_log bitRev8_injective).1

example {sched : List (Fin 8)} {cfg : TwoHopConfig 8 ℕ}
    (hmtr : (twoHopLTS 8 ℕ).MTr (twoHopAllActiveInit bitRev8) sched cfg) :
    twoHopAllActiveExecMsgs bitRev8 sched ≤ 2 * 8 * Nat.log 2 8 + 8 :=
  twoHopAllActive_messages_le bitRev8_injective hmtr

example {sched : List (Fin 8)} {cfg : TwoHopConfig 8 ℕ}
    (hmtr : (twoHopLTS 8 ℕ).MTr (twoHopAllActiveInit bitRev8) sched cfg)
    (hterm : (twoHopLTS 8 ℕ).IsTerminal cfg) :
    twoHopAllActiveExecMsgs bitRev8 sched = 2 * 8 * twoHopAllActivePhases bitRev8 + 8 ∧
    ∃! iStar : Fin 8,
      cfg.isLeader iStar = true ∧
      (∃ maxUid, cfg.node iStar = .leader maxUid ∧
        (∀ j, bitRev8 j ≤ maxUid) ∧ ∃ j₀, bitRev8 j₀ = maxUid) ∧
      ∀ j, j ≠ iStar → cfg.node j = .relay :=
  ⟨twoHopAllActive_execMsgs_eq bitRev8_injective hmtr hterm,
    (twoHopAllActive_elects_leader bitRev8_injective).2 sched cfg hmtr hterm⟩

end CslibFrontierTests.Distributed.RingElection
