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

/-! Ring leader election (checked as a `module` client with ordinary imports):
1. Angluin's anonymous ring impossibility (`[Angluin1980b]`) on `Fin 3` in both synchronous
   bidirectional/unidirectional models (`AnonProtocol`) and asynchronous FIFO models
   (`AnonAsyncProtocol`), demonstrating rotational symmetry preservation (`card ∈ {0, 3} ≠ 1`) even
   when the ring size `n = 3` is baked into the protocol;
2. Chang–Roberts (`[ChangRoberts1979]`) concrete asynchronous FIFO execution on `Fin 5` attaining
   the tight worst-case `15 = 5 * 6 / 2` messages on `Fin.rev` and best-case `9 = 2 * 5 - 1` on
   `id`, exact `n H_n` average-case checks on `Fin 3` (`11 / 2`) and `Fin 4` (`25 / 3`), and
   instantiations of safety, termination, worst-case, and average-case theorems;
3. Peterson's `O(n log n)` unidirectional asynchronous FIFO algorithm (`[Peterson1982]`): concrete
   runs on `Fin 1`, `Fin 6`, and `Fin 8` (both `Fin.rev` taking `24 < 36` messages, beating
   Chang–Roberts, and bit-reversal `[0, 4, 2, 6, 1, 5, 3, 7]` halving `8 → 4 → 2 → 1` across
   `3 = log₂ 8` phases in `56 = 2 * 8 * 3 + 8` messages under two distinct asynchronous FIFO
   schedules), together with theorem instantiations. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.RingElection

open Cslib Cslib.Distributed.RingElection

/-! ### 1. Angluin's anonymous ring impossibility (`Fin 3`, synchronous & asynchronous) -/

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

-- Synchronous impossibility theorem instantiated on `Fin 3` and for arbitrary state/message types.
example (r : ℕ) : ¬ anonRing3Proto.ElectsUniqueLeader 3 r :=
  anonRing3Proto.not_leaderElection_anonymous_ring (by decide) r

example (P : AnonProtocol ℕ String) (r : ℕ) : ¬ P.ElectsUniqueLeader 3 r :=
  P.not_leaderElection_anonymous_ring (by decide) r

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

-- Asynchronous shift equivariance and Angluin's asynchronous impossibility on `Fin 3`.
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
  anonAsync3Proto.not_leaderElection_anonymous_async (by decide) W

/-! ### 2. Chang–Roberts: worst-case `n(n + 1)/2`, best-case `2n - 1`, and exact `n H_n` -/

-- On `Fin 5` with `Fin.rev`, tokens travel `5, 4, 3, 2, 1` hops = `15 = 5 * 6 / 2`.
example : (List.finRange 5).map (crHops (Fin.rev : Fin 5 → Fin 5)) = [5, 4, 3, 2, 1] := by decide
example : changRobertsTotalMsgs (Fin.rev : Fin 5 → Fin 5) = 15 :=
  changRoberts_messages_sorted_eq 5

-- On `Fin 5` with `id`, tokens travel `1, 1, 1, 1, 5` hops = `9 = 2 * 5 - 1`.
example : (List.finRange 5).map (crHops (id : Fin 5 → Fin 5)) = [1, 1, 1, 1, 5] := by decide
example : changRobertsTotalMsgs (id : Fin 5 → Fin 5) = 9 :=
  changRoberts_messages_id_eq 5

/-- Explicit 15-step asynchronous FIFO schedule draining `Fin.rev` on `Fin 5`. -/
def crWorstSched5 : List (Fin 5) :=
  [0, 1, 2, 3, 4, 0, 2, 3, 4, 0, 3, 4, 0, 4, 0]

/-- Executable boolean check that every step in a Chang–Roberts schedule is enabled. -/
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
    let finalCfg := crExec uid (crInit uid) crWorstSched5
    crAllEnabled uid (crInit uid) crWorstSched5 = true ∧
      crExecMsgs uid crWorstSched5 = 15 ∧
      (List.finRange 5).map finalCfg.isLeader = [true, false, false, false, false] ∧
      (List.finRange 5).all (fun i => (finalCfg.chan i).isEmpty) = true := by
  decide

-- Operational bound instantiated on the concrete 15-step trace (`15 ≤ 5 * 6 / 2`).
example : crExecMsgs (Fin.rev : Fin 5 → Fin 5) crWorstSched5 ≤ 5 * (5 + 1) / 2 :=
  changRoberts_messages_le Fin.rev_injective
    (crMTr_of_crAllEnabled Fin.rev (crInit Fin.rev) crWorstSched5 (by decide))

-- Safety & termination theorems instantiated on injective `uid : Fin 5 → ℕ`.
example {uid : Fin 5 → ℕ} (huid : Function.Injective uid) {sched : List (Fin 5)}
    {cfg : CRConfig 5 ℕ} (hmtr : (crLTS uid).MTr (crInit uid) sched cfg) :
    (∀ i, cfg.isLeader i = true → ∀ j, uid j ≤ uid i) ∧
    ((crLTS uid).IsTerminal cfg → ∀ i, cfg.isLeader i = true ↔ ∀ j, uid j ≤ uid i) ∧
    (∃ tail cfg', (crLTS uid).MTr cfg tail cfg' ∧ (crLTS uid).IsTerminal cfg') :=
  ⟨fun _ hi j => changRoberts_isLeader_le huid hmtr hi j,
    fun hterm i => changRoberts_isLeader_iff_max huid hmtr hterm i,
    (changRoberts_terminates huid).1 sched cfg hmtr⟩

-- Exact `n H_n` average-case checks on `Fin 3` (`3 * (1 + 1/2 + 1/3) = 11/2`, sum over `S_3` = 33)
-- and `Fin 4` (`4 * (1 + 1/2 + 1/3 + 1/4) = 25/3`, sum over `S_4` = 200).
example : (∑ σ : Equiv.Perm (Fin 3), changRobertsTotalMsgs (⇑σ)) = 33 := by decide
example : (∑ σ : Equiv.Perm (Fin 4), changRobertsTotalMsgs (⇑σ)) = 200 := by decide

example :
    (∑ σ : Equiv.Perm (Fin 3), (changRobertsTotalMsgs (⇑σ) : ℚ)) / (Nat.factorial 3 : ℚ) =
      11 / 2 := by
  rw [changRoberts_avg_messages_eq 3]
  have h13 : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [h13]
  norm_num

example :
    (∑ σ : Equiv.Perm (Fin 4), (changRobertsTotalMsgs (⇑σ) : ℚ)) / (Nat.factorial 4 : ℚ) =
      25 / 3 := by
  rw [changRoberts_avg_messages_eq 4]
  have h14 : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [h14]
  norm_num

/-! ### 3. Peterson's `O(n log n)` asynchronous unidirectional ring election -/

/-- Executable FIFO scheduler draining up to `fuel` enabled deliveries by scanning `0, …, n - 1`
(or in reverse when `rev = true`, exercising asynchronous schedule independence). -/
def petersonDrain {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (rev : Bool) :
    ℕ → PetersonConfig n U → List (Fin n)
  | 0, _ => []
  | fuel + 1, cfg =>
    let order := if rev then (List.finRange n).reverse else List.finRange n
    match order.find? (fun i => !(cfg.chan (i - 1)).isEmpty) with
    | none => []
    | some target => target :: petersonDrain rev fuel (petersonStep target cfg)

/-- Executable boolean check that every step in a Peterson schedule is enabled. -/
def petersonAllEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] :
    PetersonConfig n U → List (Fin n) → Bool
  | _, [] => true
  | cfg, target :: rest =>
    (!(cfg.chan (target - 1)).isEmpty) && petersonAllEnabled (petersonStep target cfg) rest

theorem petersonMTr_of_allEnabled {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] :
    ∀ (cfg : PetersonConfig n U) (sched : List (Fin n)),
      petersonAllEnabled cfg sched = true →
      (petersonLTS n U).MTr cfg sched (petersonExec cfg sched)
  | _, [], _ => LTS.MTr.refl
  | cfg, target :: rest, h => by
    simp only [petersonAllEnabled, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at h
    exact LTS.MTr.stepL ⟨h.1, rfl⟩ (petersonMTr_of_allEnabled (petersonStep target cfg) rest h.2)

-- Base case `Fin 1`: `0` elimination phases, `1` message (`≤ 2 * 1 * 0 + 1 = 1`).
example : petersonPhases (id : Fin 1 → Fin 1) = 0 := by decide
example :
    let sched := petersonDrain false 5 (petersonInit (id : Fin 1 → Fin 1))
    petersonAllEnabled (petersonInit (id : Fin 1 → Fin 1)) sched = true ∧
      petersonExecMsgs (id : Fin 1 → Fin 1) sched = 1 ∧
      (petersonExec (petersonInit (id : Fin 1 → Fin 1)) sched).node 0 = .leader 0 := by
  decide

-- On reverse-sorted `Fin 6` (`Fin.rev`), Chang–Roberts sends `6 * 7 / 2 = 21` messages, whereas
-- Peterson finishes in `1` phase sending `2 * 6 * 1 + 6 = 18 < 21` messages (electing node `1`
-- with the global maximum `5` shifted by one clockwise peak hop from node `0`).
example :
    let uid := (Fin.rev : Fin 6 → Fin 6)
    let sched := petersonDrain false 30 (petersonInit uid)
    changRobertsTotalMsgs uid = 21 ∧
      petersonPhases uid = 1 ∧
      petersonExecMsgs uid sched = 18 ∧
      (petersonExec (petersonInit uid) sched).node 1 = .leader 5 := by
  decide

-- On reverse-sorted `Fin 8` (`Fin.rev`), Chang–Roberts sends `8 * 9 / 2 = 36` messages, whereas
-- Peterson finishes in `1` phase sending only `24 < 36` messages!
example :
    let uid := (Fin.rev : Fin 8 → Fin 8)
    let sched := petersonDrain false 40 (petersonInit uid)
    changRobertsTotalMsgs uid = 36 ∧
      petersonPhases uid = 1 ∧
      petersonExecMsgs uid sched = 24 ∧
      (petersonExec (petersonInit uid) sched).node 1 = .leader 7 ∧
      (List.finRange 8).all
        (fun e => ((petersonExec (petersonInit uid) sched).chan e).isEmpty) = true := by
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
    [(petersonPhase bitRev8 0).active.card,
     (petersonPhase bitRev8 1).active.card,
     (petersonPhase bitRev8 2).active.card,
     (petersonPhase bitRev8 3).active.card] = [8, 4, 2, 1] ∧
    petersonPhases bitRev8 = 3 := by
  decide

-- Forward and reverse asynchronous FIFO schedules on `Fin 8` (`bitRev8`) converge to the EXACT
-- SAME quiescent state (`.leader 7` at node `6`, `.relay` elsewhere) with `56 = 2 * 8 * 3 + 8`
-- messages, matching `peterson_messages_le` tightly!
example :
    let init := petersonInit bitRev8
    let schedFwd := petersonDrain false 70 init
    let schedRev := petersonDrain true 70 init
    let finFwd := petersonExec init schedFwd
    let finRev := petersonExec init schedRev
    schedFwd ≠ schedRev ∧
      petersonAllEnabled init schedFwd = true ∧
      petersonAllEnabled init schedRev = true ∧
      petersonExecMsgs bitRev8 schedFwd = 56 ∧
      petersonExecMsgs bitRev8 schedRev = 56 ∧
      2 * 8 * Nat.log 2 8 + 8 = 56 ∧
      (List.finRange 8).map finFwd.node = (List.finRange 8).map finRev.node ∧
      finFwd.node 6 = .leader 7 ∧
      (List.finRange 8).all (fun e => (finFwd.chan e).isEmpty) = true := by
  decide

-- Instantiate Peterson's main theorems on `bitRev8 : Fin 8 → ℕ`.
theorem bitRev8_injective : Function.Injective bitRev8 := by decide

example (k : ℕ) (hk : 2 ≤ (petersonPhase bitRev8 k).active.card) :
    2 * (petersonPhase bitRev8 (k + 1)).active.card ≤ (petersonPhase bitRev8 k).active.card :=
  peterson_phase_halving bitRev8 k hk

example : petersonPhases bitRev8 ≤ Nat.log 2 8 :=
  (peterson_phases_le_log bitRev8_injective).1

example {sched : List (Fin 8)} {cfg : PetersonConfig 8 ℕ}
    (hmtr : (petersonLTS 8 ℕ).MTr (petersonInit bitRev8) sched cfg) :
    petersonExecMsgs bitRev8 sched ≤ 2 * 8 * Nat.log 2 8 + 8 :=
  peterson_messages_le bitRev8_injective hmtr

example {sched : List (Fin 8)} {cfg : PetersonConfig 8 ℕ}
    (hmtr : (petersonLTS 8 ℕ).MTr (petersonInit bitRev8) sched cfg)
    (hterm : (petersonLTS 8 ℕ).IsTerminal cfg) :
    ∃! iStar : Fin 8,
      cfg.isLeader iStar = true ∧
      (∃ maxUid, cfg.node iStar = .leader maxUid ∧
        (∀ j, bitRev8 j ≤ maxUid) ∧ ∃ j₀, bitRev8 j₀ = maxUid) ∧
      ∀ j, j ≠ iStar → cfg.node j = .relay :=
  (peterson_elects_leader bitRev8_injective).2 sched cfg hmtr hterm

end CslibFrontierTests.Distributed.RingElection
