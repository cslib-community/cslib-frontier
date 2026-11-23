/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.FailureDetectors.Consensus

/-! Unreliable failure detectors, gossip completeness boosting, and asynchronous-round `◇S`
consensus (checked as a `module` client with ordinary imports):
* 8-class Chandra–Toueg lattice (`DetectorClass.forall_sat_imp_iff_le`), raw separating histories on
  `Fin 3`, completeness collapse on `Fin 2`, and `Ω → ◇S` eventual-leader complement reduction;
* `decide`-checked suspect-forwarding `gossipHistory` traces on `Fin 3` (including delayed packets
  and false-suspicion clearing) and `W → S` / `◇W → ◇S` reductions;
* `decide`-checked 2-round `Fin 3, t = 1` execution of `ctRoundProtocol` with pre-stabilization
  lying suspicions, split timestamp adoption without lock in Round `0`, highest-timestamp selection
  and unanimous decision in Round `1`, plus proof of `AdmissibleFDNetwork` and `IsEventuallyStrong`
  for that concrete run;
* unconditional safety on infinite `V = ℕ`, full `SolvesFDAsyncRoundConsensus` and gossip-composed
  `◇W` termination instances, `2 ≤ |P| ≤ 2t` impossibility under `◇P`, and sharp `iff` thresholds.
-/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.FailureDetectors

open Cslib.Distributed.FailureDetectors Finset

/-! ### 8-class raw-history lattice, separating witnesses, and `Ω → ◇S` -/

-- Lattice order and non-implications in the 3-cube `DetectorClass`.
example :
    DetectorClass.P ≤ .S ∧
    DetectorClass.S ≤ .W ∧
    DetectorClass.W ≤ .EW ∧
    DetectorClass.P ≤ .EP ∧
    DetectorClass.EP ≤ .ES ∧
    DetectorClass.ES ≤ .EW ∧
    ¬ (DetectorClass.EP ≤ .S) ∧
    ¬ (DetectorClass.S ≤ .EP) ∧
    ¬ (DetectorClass.Q ≤ .ES) ∧
    ¬ (DetectorClass.W ≤ .S) := by
  decide

-- Exact completeness of the 8-class raw-history lattice on `Fin 3`: `◇W` does not imply `◇S` and
-- `S` and `◇P` are incomparable prior to gossip reduction.
example :
    ¬ (∀ (F : FailurePattern (Fin 3)), F.Correct.Nonempty →
        ∀ H, DetectorClass.EW.Sat F H → DetectorClass.ES.Sat F H) := by
  rw [DetectorClass.forall_sat_imp_iff_le (by decide)]
  decide

example :
    (∃ (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)),
      F.Correct.Nonempty ∧ IsStrong F H ∧ ¬ IsEventuallyPerfect F H) ∧
    (∃ (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)),
      F.Correct.Nonempty ∧ IsEventuallyPerfect F H ∧ ¬ IsStrong F H) := by
  obtain ⟨F₁, H₁, hc₁, hS, hnESA⟩ := exists_isStrong_not_isEventualStrongAccuracy (P := Fin 3)
  obtain ⟨F₂, H₂, hc₂, hEP, hnWA⟩ := exists_isEventuallyPerfect_not_isWeakAccuracy (P := Fin 3)
  exact ⟨⟨F₁, H₁, hc₁, hS, fun h => hnESA h.2⟩, ⟨F₂, H₂, hc₂, hEP, fun h => hnWA h.2⟩⟩

example :
    ∃ (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)),
      F.Correct.Nonempty ∧ IsQuasiPerfect F H ∧ ¬ StrongCompleteness F H :=
  exists_isQuasiPerfect_not_isStrongCompleteness (by decide)

-- On `Fin 2`, weak completeness collapses to strong completeness whenever `F.Correct.Nonempty`.
example (F : FailurePattern (Fin 2)) (hcorr : F.Correct.Nonempty) (H : DetectorHistory (Fin 2)) :
    WeakCompleteness F H ↔ StrongCompleteness F H :=
  weakCompleteness_iff_strongCompleteness_of_card_le_two (by decide) hcorr H

/-- Concrete `Ω` eventual-leader history on `Fin 3` that flips before `t = 4` (`0` trusts `2`,
others trust `0`) and stabilizes to correct process `1` from `t = 4` onward. -/
def fin3Leader : LeaderHistory (Fin 3) := fun p t =>
  if t < 4 then (if p = 0 then 2 else 0) else 1

theorem fin3Leader_isEventuallyLeader :
    IsEventuallyLeader (FailurePattern.const ({2} : Finset (Fin 3))) fin3Leader := by
  refine ⟨4, 1, ?_, fun p _ t' ht' => ?_⟩
  · simp only [FailurePattern.correct_const, Set.mem_compl_iff, mem_coe, mem_singleton]
    decide
  · have hlt : ¬ t' < 4 := by omega
    simp only [fin3Leader, hlt, ↓reduceIte]

-- Pure history-map step `LeaderHistory.toDetectorHistory` yields `IsEventuallyStrong` (`◇S`),
-- while violating perpetual `StrongAccuracy` because correct process `1` is suspected at `t = 0`.
example :
    let F := FailurePattern.const ({2} : Finset (Fin 3))
    IsEventuallyStrong F fin3Leader.toDetectorHistory ∧
    ¬ StrongAccuracy F fin3Leader.toDetectorHistory := by
  refine ⟨fin3Leader_isEventuallyLeader.toDetectorHistory_isEventuallyStrong, fun hSA => ?_⟩
  have hmem : (1 : Fin 3) ∈ fin3Leader.toDetectorHistory 0 0 := by decide
  exact hSA 0 1 (by decide) 0 (by decide) hmem

/-! ### Suspect-forwarding gossip transducer (`Reduction.lean`) on `Fin 3` -/

/-- Failure pattern on `Fin 3` where process `2` crashes at `t = 0` and `{0, 1}` are correct. -/
def fin3Crash2 : FailurePattern (Fin 3) := FailurePattern.const {2}

/-- Raw detector history on `Fin 3`: at `t = 0`, process `0` falsely suspects correct process `1`;
for `t ≥ 1`, process `0` suspects crashed `2` while process `1` never suspects anyone
(`◇W \ ◇S`). -/
def fin3RawEW : DetectorHistory (Fin 3) := fun p t =>
  if t = 0 then (if p = 0 then {1} else ∅)
  else if p = 0 then {2} else ∅

/-- Asynchronous delayed gossip schedule for process `1`:
* Tick `0`: receives `⟨0, 0⟩` (carrying the false suspicion `{1}`).
* Tick `1`: receives `⟨1, 0⟩` (heartbeat from `1` clearing the false suspicion of `1`!).
* Tick `2`: network delay — no packets arrive (`[]`).
* Tick `3` onward: receives `⟨0, t - 1⟩` (delayed by 1 tick, carrying `{2}`). -/
def fin3DelayedGossip (p : Fin 3) (t : ℕ) : List (GossipPacket (Fin 3)) :=
  if p = 1 then
    if t = 0 then [⟨0, 0⟩]
    else if t = 1 then [⟨1, 0⟩]
    else if t = 2 then []
    else [⟨0, t - 1⟩]
  else []

-- Executable trace of `gossipHistory`:
-- * After tick `0` (`G 1 1`), `1` falsely suspects `{1}` from `⟨0, 0⟩`.
-- * After tick `1` (`G 1 2`), `1`'s own packet `⟨1, 0⟩` clears `1` (`\ {1} = ∅`).
-- * After tick `2` (`G 1 3`), silence preserves `∅`.
-- * After tick `3` (`G 1 4`), delayed packet `⟨0, 2⟩` forwards suspicion `{2}`!
example :
    let G := gossipHistory fin3RawEW fin3DelayedGossip
    G 1 0 = ∅ ∧
    G 1 1 = {1} ∧
    G 1 2 = ∅ ∧
    G 1 3 = ∅ ∧
    G 1 4 = {2} := by
  decide

-- `gossipHistory` along `syncGossipSchedule` upgrades `W → S` and `◇W → ◇S` on `Fin 3`.
example (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)) (hW : IsWeak F H) :
    IsStrong F (gossipHistory H (syncGossipSchedule F (List.finRange 3))) :=
  gossipHistory_isStrong_of_isWeak (admissible_syncGossipSchedule F List.mem_finRange) hW

example (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)) (hEW : IsEventuallyWeak F H) :
    IsEventuallyStrong F (gossipHistory H (syncGossipSchedule F (List.finRange 3))) :=
  gossipHistory_isEventuallyStrong_of_isEventuallyWeak
    (admissible_syncGossipSchedule F List.mem_finRange) hEW

/-! ### 2-round `Fin 3, t = 1` execution of `ctRoundProtocol`: lying detector, split ts, decision -/

/-- Concrete `t`-oblivious `ctRoundProtocol` instance on `Fin 3` (`qSize = 3 / 2 + 1 = 2`). -/
def fin3CTProto : FDAsyncRoundProtocol (Fin 3) Bool (CTState Bool) (CTMsg Bool) :=
  ctRoundProtocol (Fin 3) Bool (List.finRange 3) 0

/-- Initial inputs: `0 ↦ true`, `1 ↦ false`, `2 ↦ false`. -/
def fin3Inputs : Fin 3 → Bool
  | 0 => true
  | 1 => false
  | 2 => false

/-- Failure pattern on `Fin 3` where `{0, 1, 2}` are alive in ticks `0, 1` and process `2` crashes
at tick `2` (`F.Correct = {0, 1}`, `∀ s, (F s).card ≤ 1`). -/
def fin3LateCrash2 : FailurePattern (Fin 3) :=
  FailurePattern.ofSucc (fun s => if s < 2 then ∅ else {2}) fun s => by
    by_cases hs : s + 1 < 2
    · have hs0 : s < 2 := by omega
      simp only [hs0, hs, ↓reduceIte, Subset.rfl]
    · by_cases hs0 : s < 2
      · simp only [hs0, hs, ↓reduceIte, empty_subset]
      · simp only [hs0, hs, ↓reduceIte, Subset.rfl]

/-- `◇S` detector history for `fin3LateCrash2`:
* At ticks `0, 1`, suspects `{0}` on process `1` at tick `1` (falsely suspecting coordinator `0` in
  Round `0`, Subround `1`!).
* From tick `2` onward, suspects `{2}` on all processes (never suspecting correct `{0, 1}`). -/
def fin3Detector : DetectorHistory (Fin 3) := fun p s =>
  if s < 2 then (if p = 1 ∧ s = 1 then {0} else ∅) else {2}

/-- Adversarial link delivery for `fin3LateCrash2` (`tick = id`):
* At ticks `0, 1`: delivers from all `{0, 1, 2}` except `0 → 1` at `k = 1` (`1` still receives from
  `{1, 2}`, size `2 = 3 - 1`, while `0 ∈ fin3Detector 1 1`!).
* From tick `2` onward: delivers among `{0, 1}` (size `2 = 3 - 1`, while `2 ∈ fin3Detector p k`). -/
def fin3Deliver (k : ℕ) (q p : Fin 3) : Bool :=
  if k < 2 then decide (¬ (k = 1 ∧ q = 0 ∧ p = 1))
  else decide (q ≠ 2)

-- Verify that `(fin3LateCrash2, fin3Detector, id, fin3Deliver)` is a genuine `AdmissibleFDNetwork`
-- AND satisfies `IsEventuallyStrong` (`◇S`).
theorem fin3Network_admissible :
    AdmissibleFDNetwork fin3LateCrash2 fin3Detector 1 id fin3Deliver := by
  refine ⟨strictMono_id, fun k p hp q => ?_, fun k p hp => ?_⟩
  · clear hp
    by_cases hk : k < 2
    · have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl
      · revert p q; decide
      · revert p q; decide
    · simp only [fin3LateCrash2, FailurePattern.ofSucc_apply, id_eq, hk, ↓reduceIte,
        fin3Deliver, fin3Detector]
      revert p q; decide
  · clear hp
    by_cases hk : k < 2
    · have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl
      · revert p; decide
      · revert p; decide
    · simp only [fin3LateCrash2, FailurePattern.ofSucc_apply, id_eq, hk, ↓reduceIte,
        fin3Deliver]
      revert p; decide

theorem fin3Detector_isEventuallyStrong : IsEventuallyStrong fin3LateCrash2 fin3Detector := by
  refine ⟨⟨2, fun q hq p _ s hs => ?_⟩, ⟨2, 0, ?_, fun s hs p _ => ?_⟩⟩
  · obtain ⟨t_c, ht_c⟩ := hq
    simp only [fin3LateCrash2, FailurePattern.ofSucc_apply] at ht_c
    have hq2 : q = 2 := by
      by_cases hlt : t_c < 2
      · simp only [hlt, ↓reduceIte, notMem_empty] at ht_c
      · simpa only [hlt, ↓reduceIte, mem_singleton] using ht_c
    subst hq2
    have hslt : ¬ s < 2 := by omega
    simp only [fin3Detector, hslt, ↓reduceIte, mem_singleton]
  · intro s
    simp only [fin3LateCrash2, FailurePattern.ofSucc_apply]
    split
    · exact notMem_empty 0
    · decide
  · have hslt : ¬ s < 2 := by omega
    simp only [fin3Detector, hslt, ↓reduceIte, mem_singleton]
    decide

-- Round `0` (`k = 0..4`): coordinator `0` gathers `{0, 1, 2}`'s estimates and proposes `(0, true)`.
-- `0` adopts `(est = true, ts = 1)` and `ack`s (`some (0, true)`), `2` also adopts and crashes at
-- `k = 2`, while `1`'s false suspicion drops `0 → 1` so `1` `nack`s (`est = false, ts = 0,
-- reply = some (0, false)`), leaving `0` with only `1 < 2` `ack` (`decided = none` at `k = 4`)!
example :
    let st := fin3CTProto.state fin3LateCrash2 fin3Detector id fin3Deliver fin3Inputs
    (st 1 0).proposal = some (0, true) ∧
    (st 2 0).est = true ∧ (st 2 0).ts = 1 ∧ (st 2 0).reply = some (0, true) ∧
    (st 2 1).est = false ∧ (st 2 1).ts = 0 ∧ (st 2 1).reply = some (0, false) ∧
    (∀ p : Fin 3, p ≠ 2 → (st 4 p).decided = none) := by
  decide

-- Round `1` (`k = 4..8`): coordinator `1` gathers `{0, 1}`'s estimates `[(true, 1), (false, 0)]`,
-- selects the highest-timestamp estimate `true` (`proposal = some (1, true)`), receives `2` `ack`s
-- once stabilized, and both correct processes `{0, 1}` decide `some true` at `k = 8`!
example :
    let st := fin3CTProto.state fin3LateCrash2 fin3Detector id fin3Deliver fin3Inputs
    let dec := fin3CTProto.decision fin3LateCrash2 fin3Detector id fin3Deliver fin3Inputs
    (st 5 1).proposal = some (1, true) ∧
    dec 8 0 = some true ∧
    dec 8 1 = some true := by
  decide

/-! ### Non-vacuity, blocking witness, infinite `V = ℕ`, and tight resilience thresholds -/

-- `StrongCompleteness` yields an `AdmissibleFDNetwork`, whereas the blind detector `fun _ _ => ∅`
-- admits none when process `2` crashes in `fin3Crash2`.
example :
    ∃ tick deliver, AdmissibleFDNetwork fin3LateCrash2 fin3Detector 1 tick deliver :=
  exists_admissibleFDNetwork_of_strongCompleteness
    (fun s => by
      simp only [fin3LateCrash2, FailurePattern.ofSucc_apply]
      split <;> decide)
    fin3Detector_isEventuallyStrong.1

example (tick : ℕ → ℕ) (deliver : ℕ → Fin 3 → Fin 3 → Bool) :
    ¬ AdmissibleFDNetwork fin3Crash2 (fun _ _ => ∅) 1 tick deliver :=
  not_admissibleFDNetwork_emptyDetector_of_crashed
    ⟨0, fun _ => by simp only [fin3Crash2, FailurePattern.const_apply, mem_singleton]; decide⟩
    ⟨2, 0, by simp only [fin3Crash2, FailurePattern.const_apply, mem_singleton]⟩

-- Unconditional uniform agreement and validity of `t`-oblivious `ctRoundProtocol` over infinite
-- `V = ℕ` (requiring no fault-count bound, e.g. even on `Fin 2` where `2 * 1 = 2`!) and even under
-- the maximally Byzantine failure detector `fun _ _ => Finset.univ` that suspects everyone!
example (F : FailurePattern (Fin 2)) (tick : ℕ → ℕ) (deliver : ℕ → Fin 2 → Fin 2 → Bool)
    (x : Fin 2 → ℕ) (k₁ k₂ : ℕ) (p₁ p₂ : Fin 2) (v₁ v₂ : ℕ)
    (h₁ : (ctRoundProtocol (Fin 2) ℕ (List.finRange 2) 0).decision
      F (fun _ _ => Finset.univ) tick deliver x k₁ p₁ = some v₁)
    (h₂ : (ctRoundProtocol (Fin 2) ℕ (List.finRange 2) 0).decision
      F (fun _ _ => Finset.univ) tick deliver x k₂ p₂ = some v₂) :
    v₁ = v₂ ∧ (∃ q, x q = v₁) :=
  ⟨ctRoundProtocol_uniform_agreement F (fun _ _ => Finset.univ) tick deliver x h₁ h₂,
    ctRoundProtocol_validity F (fun _ _ => Finset.univ) tick deliver x h₁⟩

-- Full `SolvesFDAsyncRoundConsensus` instances: the single `t`-oblivious `ctRoundProtocol` on
-- `Fin 5` solves consensus simultaneously for `t = 0`, `t = 1`, and `t = 2`!
example : fin3CTProto.SolvesFDAsyncRoundConsensus 1 IsEventuallyStrong :=
  solvesFDAsyncRoundConsensus_ctRoundProtocol List.mem_finRange 0 (by decide)

example :
    let π := ctRoundProtocol (Fin 5) ℕ (List.finRange 5) 0
    π.SolvesFDAsyncRoundConsensus 1 IsEventuallyStrong ∧
    π.SolvesFDAsyncRoundConsensus 2 IsEventuallyStrong :=
  ⟨solvesFDAsyncRoundConsensus_ctRoundProtocol List.mem_finRange 0 (by decide),
    solvesFDAsyncRoundConsensus_ctRoundProtocol List.mem_finRange 0 (by decide)⟩

-- End-to-end termination under `◇W` (`IsEventuallyWeak`) composed with `syncGossipSchedule`.
example (F : FailurePattern (Fin 3)) (H : DetectorHistory (Fin 3)) (hEW : IsEventuallyWeak F H)
    (tick : ℕ → ℕ) (deliver : ℕ → Fin 3 → Fin 3 → Bool)
    (hadm : AdmissibleFDNetwork F
      (gossipHistory H (syncGossipSchedule F (List.finRange 3))) 1 tick deliver)
    (x : Fin 3 → ℕ) :
    ∃ kStar, ∀ p ∈ F.Correct,
      ((ctRoundProtocol (Fin 3) ℕ (List.finRange 3) 0).decision F
        (gossipHistory H (syncGossipSchedule F (List.finRange 3))) tick deliver x
        kStar p).isSome = true :=
  ctRoundProtocol_terminates_of_isEventuallyWeak_gossip List.mem_finRange 0 (by decide) hEW
    (admissible_syncGossipSchedule F List.mem_finRange) hadm x

-- `2 ≤ |P| ≤ 2t` impossibility even under `◇P` (`IsEventuallyPerfect`) on `Fin 2, t = 1` and
-- `Fin 4, t = 2`.
example {S M : Type} (π : FDAsyncRoundProtocol (Fin 2) Bool S M) :
    ¬ π.SolvesFDAsyncRoundConsensus 1 IsEventuallyPerfect :=
  not_solvesFDAsyncRoundConsensus_eventuallyPerfect π (by decide) (by decide)

example {S M : Type} (π : FDAsyncRoundProtocol (Fin 4) ℕ S M) :
    ¬ π.SolvesFDAsyncRoundConsensus 2 IsEventuallyPerfect :=
  not_solvesFDAsyncRoundConsensus_eventuallyPerfect π (by decide) (by decide)

-- Sharp `iff` characterizations on concrete finite process sets.
example : (∃ (S M : Type) (π : FDAsyncRoundProtocol (Fin 1) Bool S M),
    π.SolvesFDAsyncRoundConsensus 5 IsEventuallyStrong) ↔ True := by
  rw [exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff]
  decide

example : (∃ (S M : Type) (π : FDAsyncRoundProtocol (Fin 2) Bool S M),
    π.SolvesFDAsyncRoundConsensus 1 IsEventuallyPerfect) ↔ False := by
  rw [exists_solvesFDAsyncRoundConsensus_eventuallyPerfect_iff]
  decide

example : (∃ (S M : Type) (π : FDAsyncRoundProtocol (Fin 3) Bool S M),
    π.SolvesFDAsyncRoundConsensus 1 IsEventuallyStrong) ↔ True := by
  rw [exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff]
  decide

example : (∃ (S M : Type) (π : FDAsyncRoundProtocol (Fin 4) Bool S M),
    π.SolvesFDAsyncRoundConsensus 2 IsEventuallyPerfect) ↔ False := by
  rw [exists_solvesFDAsyncRoundConsensus_eventuallyPerfect_iff]
  decide

end CslibFrontierTests.Distributed.FailureDetectors
