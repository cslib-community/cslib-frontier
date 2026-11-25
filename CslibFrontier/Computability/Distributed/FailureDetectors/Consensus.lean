/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.FailureDetectors.Reduction
public import CslibFrontier.Computability.Distributed.RoundRobin
import Mathlib.Order.WellFounded

/-!
# Asynchronous-Round `◇S` Consensus and `|P| ≤ 2t` Resilience Lower Bound

Formalizes asynchronous-round consensus steps with unreliable failure detectors after
[Chandra and Toueg, §§6.2–6.3, Figure 6, Theorem 6.2.3, Corollary 6.2.4, and Theorem 6.3.1,
pp. 242–248][ChandraToueg1996] (part of #7503).

## Model scope relative to primary sources

[Chandra and Toueg, §6.2, Figure 6, p. 243][ChandraToueg1996] and
[Chandra, Hadzilacos and Toueg, §§2.3–2.4, pp. 690–692][ChandraHadzilacosToueg1996] model
event-driven asynchronous automata `(F, H_D, I, S, T)` in which processes may occupy arbitrarily
skewed asynchronous round numbers concurrently while running background diffusion `R-broadcast`.
Here we formalize an explicit **asynchronous-round** model (`FDAsyncRoundProtocol`,
`AdmissibleFDNetwork`) in which subround `k` completes at global tick `tick k` (`StrictMono tick`)
under adversarial per-subround link delivery `deliver : ℕ → P → P → Bool` subject to:

1. **`wait_or_suspect`:** for every subround `k`, correct recipient `p ∈ F.Correct`, and sender `q`,
   either `q` is alive at `tick k` and its subround-`k` message reaches `p`
   (`q ∉ F (tick k) ∧ deliver k q p = true`), or `p`'s failure detector suspects `q` at `tick k`
   (`q ∈ H p (tick k)`). When `StrongCompleteness F H` fails (e.g. `H = ∅` with a crashed process),
   no `AdmissibleFDNetwork` exists (`not_admissibleFDNetwork_emptyDetector_of_crashed`), capturing
   Phase-3 blocking on crashed coordinators.
2. **`quorum_delivery`:** in every subround `k`, every correct process receives messages from at
   least `Fintype.card P - t` non-crashed senders (while an adversary freely chooses *which* subset
   of size `≥ |P| - t` arrives).

Within this unified `FDAsyncRoundProtocol` interface we prove both directions of the `2 * t < |P|`
resilience threshold:

* **`t`-oblivious 4-stage rotating-coordinator `◇S` protocol (`ctRoundProtocol`):**
  Matches [Chandra and Toueg, §6.2, Figure 6, p. 243, and remark on p. 244][ChandraToueg1996] in
  being `t`-oblivious, waiting for strict-majority quorums of size `Fintype.card P / 2 + 1`
  (`⌈(n + 1)/2⌉`). Relative to Figure 6, this asynchronous-round realization incorporates two
  intentional adaptations: (i) `0`-indexed rounds `r = k / 4` storing updated timestamps
  `ts := r + 1` so `0` remains the unupdated initial timestamp (`ts_p ← 0`), and (ii) lockstep
  global subrounds `k` with a Subround-`3` (`k % 4 = 3`) `.phase4 s.decided` broadcast by all
  decided processes in place of skewed-round execution and Figure 4's asynchronous diffusion
  `R-broadcast`.
  * **Unconditional safety (`ctRoundProtocol_irrevocable`, `ctRoundProtocol_validity`,
    `ctRoundProtocol_lock_preservation`, `ctRoundProtocol_uniform_agreement`):** holds without any
    fault-count assumption across **all** `P`, **all** failure patterns `F`, **all** detector
    histories `H` (including arbitrarily Byzantine/lying detectors that suspect everyone or no one),
    **all** clock maps `tick`, and **all** delivery tables `deliver`, because any two strict
    majorities of size `≥ |P| / 2 + 1` intersect (`|Q₁ ∩ Q₂| ≥ 1`).
  * **Conditional termination under `◇S` and `◇W` (`2 * t < Fintype.card P`,
    `ctRoundProtocol_terminates_of_isEventuallyStrong`,
    `ctRoundProtocol_terminates_of_isEventuallyWeak_gossip`):** when `2 * t < Fintype.card P`, we
    have `Fintype.card P / 2 + 1 ≤ Fintype.card P - t`, so once global time passes crash
    stabilization and eventual-weak-accuracy stabilization for an unsuspected correct process `q*`,
    the next coordinator turn of `q*` gathers `≥ |P| / 2 + 1` `ack`s and decides across all
    `F.Correct`. Thus a single `t`-oblivious `ctRoundProtocol P V procs fallback` solves
    `SolvesFDAsyncRoundConsensus t IsEventuallyStrong` simultaneously for every `t` with
    `2 * t < Fintype.card P`.
* **Resilience tightness (`not_solvesFDAsyncRoundConsensus_eventuallyPerfect`):** when
  `2 ≤ Fintype.card P ≤ 2 * t` and `[Nontrivial V]`, partitioning `P` into `A₀` and `A₁` of size
  `≤ t` (each of size `≥ |P| - t`) shows that **no** `FDAsyncRoundProtocol` solves `t`-resilient
  consensus even under `◇P` (`IsEventuallyPerfect`), yielding the exact threshold
  `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`
  (`exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff`,
  `exists_solvesFDAsyncRoundConsensus_eventuallyPerfect_iff`).

Event-driven step-schedule realizations of Figures 5–6 and the valence-DAG necessity reduction
`D ⪰ Ω ⪰ ◇W` of [Chandra, Hadzilacos and Toueg, §6][ChandraHadzilacosToueg1996] remain open in
#7503.

## Main definitions

* `Cslib.Distributed.FailureDetectors.FDAsyncRoundProtocol`: deterministic asynchronous-round
  consensus protocol querying a failure detector history `H`.
* `Cslib.Distributed.FailureDetectors.AdmissibleFDNetwork`: asynchronous network admissibility
  (`StrictMono tick`, `wait_or_suspect`, and `quorum_delivery`).
* `Cslib.Distributed.FailureDetectors.FDAsyncRoundProtocol.SolvesFDAsyncRoundConsensus`:
  `t`-crash-tolerant consensus specification parameterized by a detector class predicate.
* `Cslib.Distributed.FailureDetectors.ownInputFDProtocol`: zero-communication protocol for
  `Fintype.card P ≤ 1`.
* `Cslib.Distributed.FailureDetectors.CTState`, `CTMsg`,
  `ctRoundProtocol`: `t`-oblivious 4-subround rotating-coordinator `◇S` consensus protocol after
  Figure 6 (using `Cslib.Distributed.rotatingCoordinator`).
* `Cslib.Distributed.FailureDetectors.LockedInRound`: round-`r` strict-majority quorum-locking
  invariant on `(r, v)`.

## Main results

* `Cslib.Distributed.FailureDetectors.exists_admissibleFDNetwork_of_strongCompleteness`,
  `Cslib.Distributed.FailureDetectors.not_admissibleFDNetwork_emptyDetector_of_crashed`:
  `StrongCompleteness` suffices for admissible schedules, whereas `H = ∅` admits none once any
  process crashes.
* `Cslib.Distributed.FailureDetectors.ctRoundProtocol_irrevocable`,
  `Cslib.Distributed.FailureDetectors.ctRoundProtocol_validity`,
  `Cslib.Distributed.FailureDetectors.ctRoundProtocol_lock_preservation`,
  `Cslib.Distributed.FailureDetectors.ctRoundProtocol_uniform_agreement`: unconditional safety of
  `ctRoundProtocol` under arbitrary `F, H, tick, deliver` without any `t` bound (step after Lemma
  6.2.1, pp. 244–245).
* `Cslib.Distributed.FailureDetectors.ctRoundProtocol_terminates_of_isEventuallyStrong`,
  `Cslib.Distributed.FailureDetectors.solvesFDAsyncRoundConsensus_ctRoundProtocol`,
  `Cslib.Distributed.FailureDetectors.ctRoundProtocol_terminates_of_isEventuallyWeak_gossip`:
  termination under `◇S` and gossip-boosted `◇W` for `2 * t < Fintype.card P` (steps after Lemma
  6.2.2, Theorem 6.2.3, and Corollary 6.2.4, pp. 245–247).
* `Cslib.Distributed.FailureDetectors.not_solvesFDAsyncRoundConsensus_eventuallyPerfect`,
  `Cslib.Distributed.FailureDetectors.exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff`,
  `Cslib.Distributed.FailureDetectors.exists_solvesFDAsyncRoundConsensus_eventuallyPerfect_iff`:
  `2 ≤ |P| ≤ 2t` impossibility step under `◇P` (after Theorem 6.3.1, p. 247) and exact resilience
  characterizations.

## References

* [T. D. Chandra and S. Toueg, *Unreliable Failure Detectors for Reliable Distributed
  Systems*][ChandraToueg1996]
* [T. D. Chandra, V. Hadzilacos and S. Toueg, *The Weakest Failure Detector for Solving
  Consensus*][ChandraHadzilacosToueg1996]
-/

public section

namespace Cslib.Distributed.FailureDetectors

open Finset

/-! ### Asynchronous-round failure-detector protocol model -/

/-- A deterministic consensus protocol in the asynchronous-round model with failure detector queries
(step model for #7503, after [Chandra and Toueg, §§2.5, 6.2][ChandraToueg1996]).

In subround `k` (occurring at global clock tick `tick k`), each non-crashed process `p ∉ F (tick k)`
sends `send k p s q` to each recipient `q`, queries its local failure detector `H p (tick k)`, and
updates its state via `update k p s (H p (tick k)) recv`. Crashed processes stutter in their last
pre-crash state and emit no messages. -/
structure FDAsyncRoundProtocol (P V State Msg : Type*) where
  /-- Initial local state of process `p` with proposed value `v`. -/
  init : P → V → State
  /-- Message sent by non-crashed process `p` in state `s` to `q` in subround `k`. -/
  send : ℕ → P → State → P → Msg
  /-- Next local state of `p` after subround `k` given suspected set `H p (tick k)` and delivered
  messages `P → Option Msg`. -/
  update : ℕ → P → State → Finset P → (P → Option Msg) → State
  /-- Optional decision read from local state (`none` while undecided). -/
  output : P → State → Option V

/-- Asynchronous network admissibility for subround clock `tick` and link schedule `deliver` under
failure pattern `F`, detector history `H`, and fault budget `t` (step network model for #7503):
* `tick_strictMono`: subround completion ticks advance strictly (`k ≤ tick k`).
* `wait_or_suspect`: for each correct recipient `p ∈ F.Correct` and process `q`, either `q` is
  non-crashed at `tick k` and delivers to `p`, or `p` suspects `q` at `tick k` (`q ∈ H p (tick k)`).
* `quorum_delivery`: every correct recipient receives messages from at least `|P| - t` non-crashed
  processes in every subround. -/
structure AdmissibleFDNetwork {P : Type*} [Fintype P] [DecidableEq P]
    (F : FailurePattern P) (H : DetectorHistory P) (t : ℕ)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) : Prop where
  /-- Subrounds occur at strictly increasing global clock ticks. -/
  tick_strictMono : StrictMono tick
  /-- A correct process skips waiting for `q`'s subround-`k` message only if `q ∈ H p (tick k)`. -/
  wait_or_suspect : ∀ k, ∀ p ∈ F.Correct, ∀ q : P,
    (q ∉ F (tick k) ∧ deliver k q p = true) ∨ q ∈ H p (tick k)
  /-- At least `|P| - t` non-crashed processes deliver to each correct process in each subround. -/
  quorum_delivery : ∀ k, ∀ p ∈ F.Correct,
    Fintype.card P - t ≤
      (Finset.univ.filter fun q => decide (q ∉ F (tick k) ∧ deliver k q p = true)).card

/-- Immediate corollary of `wait_or_suspect`: if `q` is not suspected by `p ∈ F.Correct` at
`tick k`, then `q`'s subround-`k` message is delivered to `p`. -/
theorem AdmissibleFDNetwork.deliver_of_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {F : FailurePattern P} {H : DetectorHistory P} {t : ℕ}
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool}
    (hadm : AdmissibleFDNetwork F H t tick deliver)
    {k : ℕ} {p q : P} (hp : p ∈ F.Correct) (hns : q ∉ H p (tick k)) :
    deliver k q p = true := by
  rcases hadm.wait_or_suspect k p hp q with ⟨_, hdel⟩ | hsusp
  · exact hdel
  · exact absurd hsusp hns

/-- Asynchronous-round step for #7503 (after [Chandra and Toueg, §6.2, p. 243][ChandraToueg1996]):
whenever `∀ s, (F s).card ≤ t` and `StrongCompleteness F H` holds, shifting `tick k := T_sc + k`
with full delivery between alive processes yields an `AdmissibleFDNetwork`. -/
theorem exists_admissibleFDNetwork_of_strongCompleteness {P : Type*} [Fintype P] [DecidableEq P]
    {F : FailurePattern P} {H : DetectorHistory P} {t : ℕ}
    (hF : ∀ s, (F s).card ≤ t) (hSC : StrongCompleteness F H) :
    ∃ tick deliver, AdmissibleFDNetwork F H t tick deliver := by
  obtain ⟨T_sc, hT_sc⟩ := hSC
  refine ⟨fun k => T_sc + k, fun _ _ _ => true, ?_⟩
  refine ⟨fun a b hab => by omega, fun k p hp q => ?_, fun k p _ => ?_⟩
  · by_cases hqk : q ∈ F (T_sc + k)
    · exact Or.inr (hT_sc q ⟨T_sc + k, hqk⟩ p hp (T_sc + k) (by omega))
    · exact Or.inl ⟨hqk, rfl⟩
  · have hsub : F (T_sc + k) ⊆ Finset.univ := subset_univ _
    have hcard := card_sdiff_add_card_eq_card hsub
    have hle := hF (T_sc + k)
    have heq : (Finset.univ.filter fun q => decide (q ∉ F (T_sc + k) ∧ true = true)) =
        Finset.univ \ F (T_sc + k) := by
      ext q
      simp only [mem_filter, mem_univ, true_and, and_true, decide_eq_true_eq, mem_sdiff]
    rw [heq]
    simp only [card_univ] at hcard
    omega

/-- Asynchronous-round step for #7503: if any process crashes in `F` while `F.Correct.Nonempty`,
the blind detector `fun _ _ => ∅` admits no `AdmissibleFDNetwork` (every correct process eventually
blocks waiting for the crashed process). -/
theorem not_admissibleFDNetwork_emptyDetector_of_crashed {P : Type*} [Fintype P] [DecidableEq P]
    {F : FailurePattern P} {t : ℕ} (hcorr : F.Correct.Nonempty) (hcrash : F.Crashed.Nonempty)
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool} :
    ¬ AdmissibleFDNetwork F (fun _ _ => ∅) t tick deliver := by
  intro hadm
  obtain ⟨p, hp⟩ := hcorr
  obtain ⟨q, t_c, hq_c⟩ := hcrash
  have hge : t_c ≤ tick t_c := hadm.tick_strictMono.id_le t_c
  have hq_dead : q ∈ F (tick t_c) := F.mem_of_le hge hq_c
  rcases hadm.wait_or_suspect t_c p hp q with ⟨hq_alive, _⟩ | hsusp
  · exact hq_alive hq_dead
  · exact notMem_empty q hsusp

namespace FDAsyncRoundProtocol

variable {P V S M : Type*} [DecidableEq P] (π : FDAsyncRoundProtocol P V S M)

/-- Incoming message map delivered to `p` in subround `k` from alive senders. -/
@[expose] def incoming (F : FailurePattern P) (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool)
    (st : P → S) (k : ℕ) (p : P) (q : P) : Option M :=
  if q ∉ F (tick k) ∧ deliver k q p = true then some (π.send k q (st q) p) else none

/-- Local state of process `p` after `k` subrounds under `(F, H, tick, deliver)` and inputs `x`. -/
@[expose] def state (F : FailurePattern P) (H : DetectorHistory P)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V) : ℕ → P → S
  | 0, p => π.init p (x p)
  | k + 1, p =>
    let prev := state F H tick deliver x k
    if p ∈ F (tick k) then prev p
    else π.update k p (prev p) (H p (tick k)) (π.incoming F tick deliver prev k p)

/-- Optional decision of process `p` after `k` subrounds. -/
@[expose] def decision (F : FailurePattern P) (H : DetectorHistory P)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V) (k : ℕ) (p : P) : Option V :=
  π.output p (π.state F H tick deliver x k p)

/-- `π` solves `t`-crash-tolerant consensus in the asynchronous-round model using failure detectors
satisfying `DetPred` (step specification for #7503, after
[Chandra and Toueg, §5, p. 239][ChandraToueg1996]). -/
structure SolvesFDAsyncRoundConsensus [Fintype P] (t : ℕ)
    (DetPred : FailurePattern P → DetectorHistory P → Prop) : Prop where
  /-- Decisions of correct processes are irrevocable across subrounds. -/
  irrevocable : ∀ F : FailurePattern P, (∀ s, (F s).card ≤ t) →
    ∀ H tick deliver x, AdmissibleFDNetwork F H t tick deliver → DetPred F H →
      ∀ k₁ k₂, k₁ ≤ k₂ → ∀ p ∈ F.Correct, ∀ v,
        π.decision F H tick deliver x k₁ p = some v →
        π.decision F H tick deliver x k₂ p = some v
  /-- No two correct processes ever decide distinct values. -/
  agreement : ∀ F : FailurePattern P, (∀ s, (F s).card ≤ t) →
    ∀ H tick deliver x, AdmissibleFDNetwork F H t tick deliver → DetPred F H →
      ∀ k₁ k₂, ∀ p₁ ∈ F.Correct, ∀ p₂ ∈ F.Correct, ∀ v₁ v₂,
        π.decision F H tick deliver x k₁ p₁ = some v₁ →
        π.decision F H tick deliver x k₂ p₂ = some v₂ → v₁ = v₂
  /-- Every decided value was proposed by some process (`Uniform validity`). -/
  validity : ∀ F : FailurePattern P, (∀ s, (F s).card ≤ t) →
    ∀ H tick deliver x, AdmissibleFDNetwork F H t tick deliver → DetPred F H →
      ∀ k, ∀ p ∈ F.Correct, ∀ v,
        π.decision F H tick deliver x k p = some v → ∃ q, x q = v
  /-- Every correct process eventually decides under any admissible schedule and `DetPred`
  detector. -/
  termination : ∀ F : FailurePattern P, (∀ s, (F s).card ≤ t) →
    ∀ H tick deliver x, AdmissibleFDNetwork F H t tick deliver → DetPred F H →
      ∀ p ∈ F.Correct, ∃ k, (π.decision F H tick deliver x k p).isSome = true

/-- Monotonicity in the detector predicate: if `DetPred₁` implies `DetPred₂` (e.g. `◇P → ◇S`), any
protocol solving consensus under the weaker class `DetPred₂` also solves it under `DetPred₁`. -/
theorem SolvesFDAsyncRoundConsensus.mono [Fintype P] {π : FDAsyncRoundProtocol P V S M} {t : ℕ}
    {DetPred₁ DetPred₂ : FailurePattern P → DetectorHistory P → Prop}
    (h : π.SolvesFDAsyncRoundConsensus t DetPred₂)
    (himp : ∀ F, F.Correct.Nonempty → ∀ H, DetPred₁ F H → DetPred₂ F H) :
    π.SolvesFDAsyncRoundConsensus t DetPred₁ where
  irrevocable F hF H tick deliver x hadm hdet k₁ k₂ hk p hp v hdec :=
    h.irrevocable F hF H tick deliver x hadm (himp F ⟨p, hp⟩ H hdet) k₁ k₂ hk p hp v hdec
  agreement F hF H tick deliver x hadm hdet k₁ k₂ p₁ hp₁ p₂ hp₂ v₁ v₂ h₁ h₂ :=
    h.agreement F hF H tick deliver x hadm (himp F ⟨p₁, hp₁⟩ H hdet) k₁ k₂ p₁ hp₁ p₂ hp₂ v₁ v₂ h₁ h₂
  validity F hF H tick deliver x hadm hdet k p hp v hdec :=
    h.validity F hF H tick deliver x hadm (himp F ⟨p, hp⟩ H hdet) k p hp v hdec
  termination F hF H tick deliver x hadm hdet p hp :=
    h.termination F hF H tick deliver x hadm (himp F ⟨p, hp⟩ H hdet) p hp

end FDAsyncRoundProtocol

/-- Trivial zero-communication protocol deciding each process's own initial value when `|P| ≤ 1`. -/
@[expose] def ownInputFDProtocol (P V : Type*) : FDAsyncRoundProtocol P V V PUnit where
  init _ v := v
  send _ _ _ _ := PUnit.unit
  update _ _ s _ _ := s
  output _ s := some s

private theorem ownInputFDProtocol_state {P V : Type*} [DecidableEq P]
    (F : FailurePattern P) (H : DetectorHistory P) (tick : ℕ → ℕ)
    (deliver : ℕ → P → P → Bool) (x : P → V) :
    ∀ k p, (ownInputFDProtocol P V).state F H tick deliver x k p = x p
  | 0, _ => rfl
  | k + 1, p => by
    simp only [FDAsyncRoundProtocol.state, ownInputFDProtocol]
    split <;> exact ownInputFDProtocol_state F H tick deliver x k p

private theorem ownInputFDProtocol_decision {P V : Type*} [DecidableEq P]
    (F : FailurePattern P) (H : DetectorHistory P) (tick : ℕ → ℕ)
    (deliver : ℕ → P → P → Bool) (x : P → V) (k : ℕ) (p : P) :
    (ownInputFDProtocol P V).decision F H tick deliver x k p = some (x p) := by
  simp only [FDAsyncRoundProtocol.decision, ownInputFDProtocol_state]
  rfl

/-- Original base-case helper for #7503: when `P` is a subsingleton (`Fintype.card P ≤ 1`),
`ownInputFDProtocol` solves `SolvesFDAsyncRoundConsensus` for any fault budget `t` and detector
predicate `DetPred`. -/
theorem solvesFDAsyncRoundConsensus_ownInput {P V : Type*} [Fintype P] [DecidableEq P]
    [Subsingleton P] (t : ℕ) (DetPred : FailurePattern P → DetectorHistory P → Prop) :
    (ownInputFDProtocol P V).SolvesFDAsyncRoundConsensus t DetPred where
  irrevocable F _ H tick deliver x _ _ k₁ k₂ _ p _ v hdec := by
    rw [ownInputFDProtocol_decision] at hdec ⊢
    exact hdec
  agreement F _ H tick deliver x _ _ k₁ k₂ p₁ _ p₂ _ v₁ v₂ h₁ h₂ := by
    rw [ownInputFDProtocol_decision, Option.some.injEq] at h₁ h₂
    rw [← h₁, ← h₂, Subsingleton.elim p₁ p₂]
  validity F _ H tick deliver x _ _ k p _ v hdec := by
    rw [ownInputFDProtocol_decision, Option.some.injEq] at hdec
    exact ⟨p, hdec⟩
  termination F _ H tick deliver x _ _ p _ := by
    refine ⟨0, ?_⟩
    rw [ownInputFDProtocol_decision]
    rfl

/-! ### Maximum-timestamp selector -/

/-- Deterministic selector returning an `(estimate, timestamp)` pair maximizing the timestamp in a
nonempty list ([Chandra and Toueg, §6.2, Figure 6, Phase 2, p. 243][ChandraToueg1996]). -/
@[expose] def selectMaxTs {V : Type*} : List (V × ℕ) → Option (V × ℕ)
  | [] => none
  | [vt] => some vt
  | vt :: rest =>
    match selectMaxTs rest with
    | none => some vt
    | some best => if best.2 ≤ vt.2 then some vt else some best

private theorem selectMaxTs_isSome_of_ne_nil {V : Type*} :
    ∀ {l : List (V × ℕ)}, l ≠ [] → (selectMaxTs l).isSome = true
  | [], h => absurd rfl h
  | [_], _ => rfl
  | vt :: b :: rest, _ => by
    simp only [selectMaxTs]
    cases selectMaxTs (b :: rest) with
    | none => rfl
    | some best =>
      by_cases hle : best.2 ≤ vt.2 <;> simp only [hle, ↓reduceIte, Option.isSome_some]

private theorem selectMaxTs_mem_and_max {V : Type*} :
    ∀ {l : List (V × ℕ)} {v : V} {ts : ℕ},
      selectMaxTs l = some (v, ts) → (v, ts) ∈ l ∧ ∀ w ts', (w, ts') ∈ l → ts' ≤ ts
  | [], _, _, h => by nomatch h
  | [vt], v, ts, h => by
    simp only [selectMaxTs, Option.some.injEq] at h
    subst h
    refine ⟨List.mem_singleton_self _, fun w ts' hmem => ?_⟩
    simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    omega
  | vt :: b :: rest, v, ts, h => by
    simp only [selectMaxTs] at h
    cases hrest : selectMaxTs (b :: rest) with
    | none =>
      exact absurd (Option.isSome_none ▸ hrest ▸
        selectMaxTs_isSome_of_ne_nil (List.cons_ne_nil b rest)) Bool.false_ne_true
    | some best =>
      rw [hrest] at h
      obtain ⟨hb_mem, hb_max⟩ := selectMaxTs_mem_and_max hrest
      by_cases hle : best.2 ≤ vt.2
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, fun w ts' hmem => ?_⟩
        rcases List.mem_cons.mp hmem with heq | htail
        · cases heq; exact le_rfl
        · exact (hb_max w ts' htail).trans hle
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_of_mem vt hb_mem, fun w ts' hmem => ?_⟩
        rcases List.mem_cons.mp hmem with heq | htail
        · cases heq; omega
        · exact hb_max w ts' htail

/-! ### The 4-stage Chandra–Toueg `◇S` rotating-coordinator round protocol -/

/-- Local process state for `ctRoundProtocol`
(after [Chandra and Toueg, §6.2, Figure 6, p. 243][ChandraToueg1996]). -/
structure CTState (V : Type*) where
  /-- Current estimate of the decision value (`estimate_p`, initially `input_p`). -/
  est : V
  /-- Round number (`r + 1`) in which `est` was last adopted (`ts_p`, initially `0`). -/
  ts : ℕ
  /-- Round-tagged coordinator proposal `(r, v)` selected in Subround `0` of round `r`. -/
  proposal : Option (ℕ × V)
  /-- Round-tagged Phase-3 reply `(r, true)` (`ack`) or `(r, false)` (`nack`). -/
  reply : Option (ℕ × Bool)
  /-- Write-once Consensus decision (`none` while undecided). -/
  decided : Option V
  deriving @[expose] DecidableEq

/-- Subround messages of `ctRoundProtocol` across the four stages of round `r = k / 4`. -/
inductive CTMsg (V : Type*) where
  /-- Subround `0` (Phase 1): process sends `(est, ts)` to coordinator `c`. -/
  | phase1 (est : V) (ts : ℕ)
  /-- Subround `1` (Phase 2): coordinator broadcasts round-tagged `proposal`. -/
  | phase2 (proposal : Option (ℕ × V))
  /-- Subround `2` (Phase 3): process sends round-tagged `ack`/`nack` reply to `c`. -/
  | phase3 (reply : Option (ℕ × Bool))
  /-- Subround `3` (Phase 4): processes broadcast any latched `decided` value. -/
  | phase4 (decided : Option V)
  deriving @[expose] DecidableEq

/-- Extracts `(est, ts)` from a Subround-`0` `.phase1` message. -/
@[expose] def extractPhase1 {V : Type*} : Option (CTMsg V) → Option (V × ℕ)
  | some (.phase1 v ts) => some (v, ts)
  | _ => none

/-- Checks whether `m j` is a Subround-`2` `ack` (`true`) for round `r`. -/
@[expose] def isRoundAck {V : Type*} (r : ℕ) : Option (CTMsg V) → Bool
  | some (.phase3 (some (r', true))) => decide (r' = r)
  | _ => false

/-- Extracts a latched decision from a Subround-`3` `.phase4` message. -/
@[expose] def extractDecide {V : Type*} : Option (CTMsg V) → Option V
  | some (.phase4 (some d)) => some d
  | _ => none

/-- Outgoing subround message of `ctRoundProtocol`. -/
@[expose] def ctSend {P V : Type*} (k : ℕ) (_p : P) (s : CTState V) (_dst : P) : CTMsg V :=
  match k % 4 with
  | 0 => .phase1 s.est s.ts
  | 1 => .phase2 s.proposal
  | 2 => .phase3 s.reply
  | _ => .phase4 s.decided

/-- State transition of `ctRoundProtocol` in subround `k` (`r = k / 4`, phase `k % 4`), using the
`t`-oblivious strict-majority quorum threshold `Fintype.card P / 2 + 1`. -/
@[expose] def ctUpdate {P V : Type*} [Fintype P] [DecidableEq P]
    (procs : List P) (fallback : P) (k : ℕ) (p : P) (s : CTState V)
    (suspected : Finset P) (m : P → Option (CTMsg V)) : CTState V :=
  let r := k / 4
  let c := rotatingCoordinator procs fallback r
  let qSize := Fintype.card P / 2 + 1
  if k % 4 = 0 then
    if p = c then
      let pairs := procs.dedup.filterMap fun j => extractPhase1 (m j)
      if qSize ≤ pairs.length then
        match selectMaxTs pairs with
        | some (v, _) => { s with proposal := some (r, v), reply := none }
        | none => { s with proposal := none, reply := none }
      else { s with proposal := none, reply := none }
    else { s with proposal := none, reply := none }
  else if k % 4 = 1 then
    match m c with
    | some (.phase2 (some (r', v))) =>
      if r' = r then { s with est := v, ts := r + 1, reply := some (r, true) }
      else if c ∈ suspected then { s with reply := some (r, false) }
      else { s with reply := none }
    | _ =>
      if c ∈ suspected then { s with reply := some (r, false) }
      else { s with reply := none }
  else if k % 4 = 2 then
    if p = c then
      match s.proposal with
      | some (r', v) =>
        if r' = r ∧ qSize ≤ (procs.dedup.filter fun j => isRoundAck r (m j)).length then
          { s with decided := s.decided.or (some v) }
        else s
      | none => s
    else s
  else
    let inc := procs.dedup.findSome? fun j => extractDecide (m j)
    { s with decided := s.decided.or inc }

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, §6.2, Figure 6, p. 243, and remark on p. 244][ChandraToueg1996]):
`t`-oblivious 4-subround rotating-coordinator `◇S` consensus protocol waiting for strict-majority
quorums of size `Fintype.card P / 2 + 1`. Relative to Figure 6, this asynchronous-round realization
uses `0`-indexed rounds `r = k / 4` storing updated timestamps `ts := r + 1` (so `0` remains the
unupdated initial timestamp) and lockstep global subrounds `k` with a Subround-`3` (`k % 4 = 3`)
`.phase4 s.decided` broadcast by all decided processes in place of skewed-round execution and
Figure 4's asynchronous diffusion `R-broadcast`. -/
@[expose] def ctRoundProtocol (P V : Type*) [Fintype P] [DecidableEq P]
    (procs : List P) (fallback : P) : FDAsyncRoundProtocol P V (CTState V) (CTMsg V) where
  init _ v := ⟨v, 0, none, none, none⟩
  send := ctSend
  update := ctUpdate procs fallback
  output _ s := s.decided

/-! ### Unconditional safety of `ctRoundProtocol` -/

/-- Round-`r` strict-majority quorum-locking predicate for `ctRoundProtocol`: coordinator `c_r`
proposed `(r, v)` at the end of Subround `0`, and at least `Fintype.card P / 2 + 1` processes
recorded `ack` (`some (r, true)`) at the end of Subround `1`. -/
@[expose] def LockedInRound {P V : Type*} [Fintype P] [DecidableEq P]
    (procs : List P) (fallback : P)
    (F : FailurePattern P) (H : DetectorHistory P)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V) (r : ℕ) (v : V) : Prop :=
  let st := (ctRoundProtocol P V procs fallback).state F H tick deliver x
  (st (4 * r + 1) (rotatingCoordinator procs fallback r)).proposal = some (r, v) ∧
    ∃ Q : Finset P, Fintype.card P / 2 + 1 ≤ Q.card ∧
      ∀ j ∈ Q, (st (4 * r + 2) j).reply = some (r, true)

section Safety

variable {P V : Type*} [Fintype P] [DecidableEq P]
  {procs : List P} {fallback : P}
  (F : FailurePattern P) (H : DetectorHistory P)
  (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V)

private abbrev ctSt (procs : List P) (fallback : P) :=
  (ctRoundProtocol P V procs fallback).state F H tick deliver x

/-- Messages delivered to `p` in subround `k` of `ctRoundProtocol`. -/
private abbrev ctIn (procs : List P) (fallback : P) (k : ℕ) (p : P) : P → Option (CTMsg V) :=
  (ctRoundProtocol P V procs fallback).incoming F tick deliver
    (ctSt F H tick deliver x procs fallback k) k p

private theorem ctSt_zero (p : P) :
    ctSt F H tick deliver x procs fallback 0 p = ⟨x p, 0, none, none, none⟩ :=
  rfl

private theorem ctSt_succ (k : ℕ) (p : P) :
    ctSt F H tick deliver x procs fallback (k + 1) p =
      if p ∈ F (tick k) then ctSt F H tick deliver x procs fallback k p
      else ctUpdate procs fallback k p (ctSt F H tick deliver x procs fallback k p)
        (H p (tick k)) (ctIn F H tick deliver x procs fallback k p) :=
  rfl

/-- A message delivered to `p` from `q` in subround `k` is `q`'s `ctSend`. -/
private theorem ctIn_eq_some {k : ℕ} {p q : P} {msg : CTMsg V}
    (h : ctIn F H tick deliver x procs fallback k p q = some msg) :
    msg = ctSend k q (ctSt F H tick deliver x procs fallback k q) p := by
  unfold ctIn FDAsyncRoundProtocol.incoming at h
  split_ifs at h
  exact (Option.some.inj h).symm

/-- One subround either keeps `(est, ts)`, or (Subround `1`) adopts the round-`k / 4`
coordinator's proposal with `ts := k / 4 + 1`. -/
private theorem ctSt_succ_est_ts (k : ℕ) (p : P) :
    (ctSt F H tick deliver x procs fallback (k + 1) p).est =
        (ctSt F H tick deliver x procs fallback k p).est ∧
      (ctSt F H tick deliver x procs fallback (k + 1) p).ts =
        (ctSt F H tick deliver x procs fallback k p).ts ∨
    k % 4 = 1 ∧ (ctSt F H tick deliver x procs fallback (k + 1) p).ts = k / 4 + 1 ∧
      ctIn F H tick deliver x procs fallback k p (rotatingCoordinator procs fallback (k / 4)) =
        some (.phase2 (some (k / 4, (ctSt F H tick deliver x procs fallback (k + 1) p).est))) := by
  rw [ctSt_succ]
  generalize ctIn F H tick deliver x procs fallback k p = m
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h4 | h4 | h4 | h4 <;>
    simp only [ctUpdate, h4, Nat.reduceEqDiff, ↓reduceIte] <;> grind

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, §6.2, Figure 6, p. 243][ChandraToueg1996]): once `decided = some v` at any
process `p` (correct or faulty) in `ctRoundProtocol`, `decided` remains `some v` at all subsequent
subrounds under arbitrary `F, H, tick, deliver`. -/
theorem ctRoundProtocol_irrevocable {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (p : P) (v : V)
    (hdec : (ctRoundProtocol P V procs fallback).decision F H tick deliver x k₁ p = some v) :
    (ctRoundProtocol P V procs fallback).decision F H tick deliver x k₂ p = some v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => simpa only [Nat.add_zero] using hdec
  | succ d ih =>
    change (ctSt F H tick deliver x procs fallback (k₁ + d) p).decided = some v at ih
    change (ctSt F H tick deliver x procs fallback ((k₁ + d) + 1) p).decided = some v
    rw [ctSt_succ]
    generalize ctIn F H tick deliver x procs fallback (k₁ + d) p = m
    unfold ctUpdate
    grind

/-- Upper bound `(state k p).ts ≤ (k + 2) / 4` (so `(state (4 * r) p).ts ≤ r`). -/
private theorem ctSt_ts_le :
    ∀ (k : ℕ) (p : P), (ctSt F H tick deliver x procs fallback k p).ts ≤ (k + 2) / 4
  | 0, _ => Nat.zero_le _
  | k + 1, p => by
    have : (ctSt F H tick deliver x procs fallback k p).ts ≤ (k + 2) / 4 := ctSt_ts_le k p
    rcases ctSt_succ_est_ts F H tick deliver x (procs := procs) (fallback := fallback) k p
      with h | ⟨h1, h2, -⟩ <;> omega

/-- Step-wise monotonicity of local timestamps `ts` in `ctRoundProtocol`. -/
private theorem ctSt_ts_mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (p : P) :
    (ctSt F H tick deliver x procs fallback k₁ p).ts ≤
      (ctSt F H tick deliver x procs fallback k₂ p).ts := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    refine ih.trans ?_
    rw [← Nat.add_assoc]
    have := ctSt_ts_le F H tick deliver x (procs := procs) (fallback := fallback) (k₁ + d) p
    rcases ctSt_succ_est_ts F H tick deliver x (procs := procs) (fallback := fallback)
      (k₁ + d) p with h | ⟨h1, h2, -⟩ <;> omega

/-- Any `proposal = some (r, v)` stored at `(k, p)` was created at `k = 4 * r + 1` on
`p = rotatingCoordinator procs fallback r`. -/
private theorem ctSt_proposal_inv :
    ∀ (k : ℕ) (p : P) (r : ℕ) (v : V),
      (ctSt F H tick deliver x procs fallback k p).proposal = some (r, v) →
      p = rotatingCoordinator procs fallback r ∧ 4 * r + 1 ≤ k ∧
        (ctSt F H tick deliver x procs fallback (4 * r + 1) p).proposal = some (r, v)
  | 0, _, _, _, h => by rw [ctSt_zero] at h; nomatch h
  | k + 1, p, r, v, h => by
    obtain h' | ⟨h0, rfl, rfl⟩ :
        (ctSt F H tick deliver x procs fallback k p).proposal = some (r, v) ∨
          k % 4 = 0 ∧ p = rotatingCoordinator procs fallback (k / 4) ∧ r = k / 4 := by
      rw [ctSt_succ] at h
      generalize ctIn F H tick deliver x procs fallback k p = m at h
      rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h4 | h4 | h4 | h4 <;>
        simp only [ctUpdate, h4, Nat.reduceEqDiff, ↓reduceIte] at h <;> grind
    · obtain ⟨hp_eq, hk_le, hprop⟩ := ctSt_proposal_inv k p r v h'
      exact ⟨hp_eq, by omega, hprop⟩
    · exact ⟨rfl, by omega, by rwa [show 4 * (k / 4) + 1 = k + 1 by omega]⟩

private theorem length_filterMap_eq_length_filter {α β : Type*} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).length = (l.filter fun a => (f a).isSome).length
  | [] => rfl
  | a :: rest => by
    cases hf : f a <;>
      simp [List.filterMap, List.filter, hf, length_filterMap_eq_length_filter f rest]

/-- Unpacks the Phase-2 maximum-timestamp selection witnessing
`(state (4 * r + 1) (coordinator r)).proposal = some (r, v)`. -/
private theorem ctSt_roundProposal_quorum {r : ℕ} {v : V}
    (hprop : (ctSt F H tick deliver x procs fallback (4 * r + 1)
      (rotatingCoordinator procs fallback r)).proposal = some (r, v)) :
    ∃ (Q_est : Finset P) (ts_max : ℕ) (j₀ : P),
      Fintype.card P / 2 + 1 ≤ Q_est.card ∧
      j₀ ∈ Q_est ∧
      (ctSt F H tick deliver x procs fallback (4 * r) j₀).est = v ∧
      (ctSt F H tick deliver x procs fallback (4 * r) j₀).ts = ts_max ∧
      ∀ j ∈ Q_est, (ctSt F H tick deliver x procs fallback (4 * r) j).ts ≤ ts_max := by
  generalize hc : rotatingCoordinator procs fallback r = c at hprop
  have hm0 : 4 * r % 4 = 0 := by omega
  set m₀ := ctIn F H tick deliver x procs fallback (4 * r) c with hm₀
  -- The coordinator was alive and selected `(v, ts_max)` from a quorum of Phase-1 pairs.
  obtain ⟨hq, ts_max, hsel⟩ :
      Fintype.card P / 2 + 1 ≤ (procs.dedup.filterMap fun j => extractPhase1 (m₀ j)).length ∧
        ∃ ts_max, selectMaxTs (procs.dedup.filterMap fun j => extractPhase1 (m₀ j)) =
          some (v, ts_max) := by
    rw [ctSt_succ] at hprop
    split_ifs at hprop with hc_dead
    · have := ctSt_proposal_inv F H tick deliver x (4 * r) c r v hprop
      omega
    · rw [← hm₀] at hprop
      clear_value m₀
      clear hm₀
      unfold ctUpdate at hprop
      simp only [hm0, Nat.mul_div_cancel_left r (by omega : 0 < 4), hc, ↓reduceIte] at hprop
      grind
  obtain ⟨hmem, hmax⟩ := selectMaxTs_mem_and_max hsel
  have hextract : ∀ j w ts', extractPhase1 (m₀ j) = some (w, ts') →
      (ctSt F H tick deliver x procs fallback (4 * r) j).est = w ∧
        (ctSt F H tick deliver x procs fallback (4 * r) j).ts = ts' := by
    intro j w ts' hex
    cases hm : m₀ j with
    | none => simp [hm, extractPhase1] at hex
    | some msg =>
      rw [hm, ctIn_eq_some F H tick deliver x hm] at hex
      simpa [ctSend, hm0, extractPhase1] using hex
  let Q_est : Finset P := (procs.dedup.filter fun j => (extractPhase1 (m₀ j)).isSome).toFinset
  obtain ⟨j₀, hj₀_dedup, hj₀_ex⟩ := List.mem_filterMap.mp hmem
  obtain ⟨hj₀_est, hj₀_ts⟩ := hextract j₀ v ts_max hj₀_ex
  refine ⟨Q_est, ts_max, j₀, ?_, ?_, hj₀_est, hj₀_ts, fun j hj => ?_⟩
  · rwa [List.toFinset_card_of_nodup (procs.nodup_dedup.filter _),
      ← length_filterMap_eq_length_filter]
  · exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hj₀_dedup, by simp [hj₀_ex]⟩)
  · simp only [Q_est, List.mem_toFinset, List.mem_filter, Option.isSome_iff_exists] at hj
    obtain ⟨hj_dedup, ⟨w, ts'⟩, hw⟩ := hj
    rw [(hextract j w ts' hw).2]
    exact hmax w ts' (List.mem_filterMap.mpr ⟨j, hj_dedup, hw⟩)

/-- Simultaneous provenance of `(state k p).est` (every estimate is an initial input `x q`) and
positive timestamps `(state k p).ts = r₀ + 1` (witnessed by `coordinator r₀`'s round-`r₀`
proposal). -/
private theorem ctSt_est_ts_origin (k : ℕ) :
    ∀ p : P,
      (∃ q, x q = (ctSt F H tick deliver x procs fallback k p).est) ∧
      (∀ r₀, (ctSt F H tick deliver x procs fallback k p).ts = r₀ + 1 →
        (ctSt F H tick deliver x procs fallback (4 * r₀ + 1)
          (rotatingCoordinator procs fallback r₀)).proposal =
          some (r₀, (ctSt F H tick deliver x procs fallback k p).est)) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => exact fun p => ⟨⟨p, rfl⟩, fun _ h => by nomatch h⟩
    | succ k =>
      intro p
      rcases ctSt_succ_est_ts F H tick deliver x k p with ⟨hest, hts⟩ | ⟨h1, hts, hm⟩
      · rw [hest, hts]
        exact ih k (Nat.lt_succ_self k) p
      · -- `p` adopted the round-`k / 4` coordinator's proposal.
        have hc_prop : (ctSt F H tick deliver x procs fallback (4 * (k / 4) + 1)
            (rotatingCoordinator procs fallback (k / 4))).proposal =
              some (k / 4, (ctSt F H tick deliver x procs fallback (k + 1) p).est) := by
          have := ctIn_eq_some F H tick deliver x hm
          rw [show 4 * (k / 4) + 1 = k by omega]
          simpa [ctSend, h1] using this.symm
        obtain ⟨_, _, j₀, _, _, hj₀_est, _, _⟩ :=
          ctSt_roundProposal_quorum F H tick deliver x hc_prop
        obtain ⟨⟨q, hq⟩, _⟩ := ih (4 * (k / 4)) (by omega) j₀
        refine ⟨⟨q, hq.trans hj₀_est⟩, fun r₀ hr₀ => ?_⟩
        obtain rfl : r₀ = k / 4 := by omega
        exact hc_prop

/-- Any `(state k p).reply = some (r, true)` was recorded at `k = 4 * r + 2` alongside
`(state (4 * r + 2) p).ts = r + 1`. -/
private theorem ctSt_reply_origin :
    ∀ (k : ℕ) (p : P) (r : ℕ),
      (ctSt F H tick deliver x procs fallback k p).reply = some (r, true) →
      4 * r + 2 ≤ k ∧ (ctSt F H tick deliver x procs fallback (4 * r + 2) p).ts = r + 1
  | 0, _, _, h => by rw [ctSt_zero] at h; nomatch h
  | k + 1, p, r, h => by
    obtain h' | ⟨h1, rfl, hts⟩ :
        (ctSt F H tick deliver x procs fallback k p).reply = some (r, true) ∨
          k % 4 = 1 ∧ r = k / 4 ∧
            (ctSt F H tick deliver x procs fallback (k + 1) p).ts = r + 1 := by
      rw [ctSt_succ] at h ⊢
      generalize ctIn F H tick deliver x procs fallback k p = m at h ⊢
      rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h4 | h4 | h4 | h4 <;>
        simp only [ctUpdate, h4, Nat.reduceEqDiff, ↓reduceIte] at h ⊢ <;> grind
    · obtain ⟨hk_le, hts⟩ := ctSt_reply_origin k p r h'
      exact ⟨by omega, hts⟩
    · exact ⟨by omega, by rwa [show 4 * (k / 4) + 2 = k + 1 by omega]⟩

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Lemma 6.2.1, pp. 244–245][ChandraToueg1996]): once `LockedInRound` holds for
`(r, v)`, every coordinator proposal `(r', w)` in any later round `r' > r` satisfies `w = v`,
unconditionally across all `P, F, H, tick, deliver`. -/
theorem ctRoundProtocol_lock_preservation {r : ℕ} {v : V}
    (hlock : LockedInRound procs fallback F H tick deliver x r v) :
    ∀ {r' : ℕ}, r < r' → ∀ {w : V},
      ((ctRoundProtocol P V procs fallback).state F H tick deliver x (4 * r' + 1)
        (rotatingCoordinator procs fallback r')).proposal = some (r', w) → w = v := by
  obtain ⟨hprop_r, Q_ack, hQ_ack_card, hQ_ack⟩ := hlock
  intro r'
  induction r' using Nat.strongRecOn with
  | ind r' ih =>
    intro hlt w hprop_r'
    obtain ⟨Q_est, ts_max, j₀, hQ_est_card, hj₀_mem, hj₀_est, hj₀_ts, hQ_est_max⟩ :=
      ctSt_roundProposal_quorum F H tick deliver x hprop_r'
    -- Strict-majority quorum intersection: `|Q_ack| ≥ |P|/2 + 1` and `|Q_est| ≥ |P|/2 + 1`.
    have hinter_nonempty : (Q_ack ∩ Q_est).Nonempty := by
      have hunion := card_union_add_card_inter Q_ack Q_est
      have hle_univ : (Q_ack ∪ Q_est).card ≤ Fintype.card P := card_le_univ _
      have hpos : 0 < (Q_ack ∩ Q_est).card := by omega
      exact card_pos.mp hpos
    obtain ⟨jStar, hjStar⟩ := hinter_nonempty
    obtain ⟨hj_ack, hj_est⟩ := mem_inter.mp hjStar
    obtain ⟨_, hts_jStar⟩ := ctSt_reply_origin F H tick deliver x (4 * r + 2) jStar r
      (hQ_ack jStar hj_ack)
    have hts_mono := ctSt_ts_mono F H tick deliver x (procs := procs) (fallback := fallback)
      (show 4 * r + 2 ≤ 4 * r' by omega) jStar
    have hts_ge : r + 1 ≤ ts_max := by
      have hmax := hQ_est_max jStar hj_est
      omega
    have hts_le_r' : ts_max ≤ r' := by
      have hle := ctSt_ts_le F H tick deliver x (procs := procs) (fallback := fallback)
        (4 * r') j₀
      omega
    obtain ⟨r₀, hr₀_eq⟩ : ∃ r₀, ts_max = r₀ + 1 := ⟨ts_max - 1, by omega⟩
    have hr_le_r₀ : r ≤ r₀ := by omega
    have hr₀_lt_r' : r₀ < r' := by omega
    have hprop_r₀ := (ctSt_est_ts_origin F H tick deliver x (4 * r') j₀).2 r₀
      (hj₀_ts.trans hr₀_eq)
    rw [hj₀_est] at hprop_r₀
    rcases eq_or_lt_of_le hr_le_r₀ with rfl | hr_lt_r₀
    · rw [hprop_r] at hprop_r₀
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hprop_r₀
      exact hprop_r₀.symm
    · exact ih r₀ hr₀_lt_r' hr_lt_r₀ hprop_r₀

/-- Every decided value in `ctRoundProtocol` originates from a `LockedInRound` event. -/
private theorem ctSt_decided_locked :
    ∀ (k : ℕ) (p : P) (d : V),
      (ctSt F H tick deliver x procs fallback k p).decided = some d →
      ∃ r, LockedInRound procs fallback F H tick deliver x r d
  | 0, _, _, h => by rw [ctSt_zero] at h; nomatch h
  | k + 1, p, d, h => by
    set m := ctIn F H tick deliver x procs fallback k p with hm
    obtain h' | ⟨h2, rfl, hprop, hq⟩ | ⟨h3, hfind⟩ :
        (ctSt F H tick deliver x procs fallback k p).decided = some d ∨
          k % 4 = 2 ∧ p = rotatingCoordinator procs fallback (k / 4) ∧
            (ctSt F H tick deliver x procs fallback k p).proposal = some (k / 4, d) ∧
            Fintype.card P / 2 + 1 ≤ (procs.dedup.filter fun j => isRoundAck (k / 4) (m j)).length ∨
          k % 4 = 3 ∧ procs.dedup.findSome? (fun j => extractDecide (m j)) = some d := by
      rw [ctSt_succ, ← hm] at h
      clear_value m
      clear hm
      rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h4 | h4 | h4 | h4 <;>
        simp only [ctUpdate, h4, Nat.reduceEqDiff, ↓reduceIte] at h <;>
        grind [Option.or_eq_some_iff]
    · exact ctSt_decided_locked k p d h'
    · -- The coordinator decided on a quorum of round-`k / 4` acks.
      obtain ⟨_, _, hprop_round⟩ := ctSt_proposal_inv F H tick deliver x k _ (k / 4) d hprop
      refine ⟨k / 4, hprop_round, (procs.dedup.filter fun j => isRoundAck (k / 4) (m j)).toFinset,
        by rwa [List.toFinset_card_of_nodup (procs.nodup_dedup.filter _)], fun j hj => ?_⟩
      simp only [List.mem_toFinset, List.mem_filter] at hj
      cases hm : m j with
      | none => simp [hm, isRoundAck] at hj
      | some msg =>
        rw [hm, ctIn_eq_some F H tick deliver x hm] at hj
        rw [show 4 * (k / 4) + 2 = k by omega]
        simp only [ctSend, h2, isRoundAck] at hj
        grind
    · -- `p` adopted a decision broadcast in Subround `3`.
      obtain ⟨j, _, hj⟩ := List.exists_of_findSome?_eq_some hfind
      cases hm : m j with
      | none => simp [hm, extractDecide] at hj
      | some msg =>
        rw [hm, ctIn_eq_some F H tick deliver x hm] at hj
        simp only [ctSend, h3, extractDecide] at hj
        exact ctSt_decided_locked k j d (by grind)

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Theorem 6.2.3, p. 246][ChandraToueg1996]): any value decided by any process in
`ctRoundProtocol` under any `(F, H, tick, deliver)` was proposed as some process's initial input
`x q`. -/
theorem ctRoundProtocol_validity {k : ℕ} {p : P} {v : V}
    (hdec : (ctRoundProtocol P V procs fallback).decision F H tick deliver x k p = some v) :
    ∃ q, x q = v := by
  obtain ⟨r, hprop_r, _⟩ := ctSt_decided_locked F H tick deliver x k p v hdec
  obtain ⟨_, _, j₀, _, _, hj₀_est, _, _⟩ := ctSt_roundProposal_quorum F H tick deliver x hprop_r
  obtain ⟨⟨q, hq⟩, _⟩ := ctSt_est_ts_origin F H tick deliver x (4 * r) j₀
  exact ⟨q, hq.trans hj₀_est⟩

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Lemma 6.2.1, pp. 244–245][ChandraToueg1996]): no two processes (correct or
faulty) ever decide distinct values in `ctRoundProtocol` under any `(F, H, tick, deliver)` (even if
any number of processes crash or `H` is an arbitrarily lying failure detector). -/
theorem ctRoundProtocol_uniform_agreement
    {k₁ k₂ : ℕ} {p₁ p₂ : P} {v₁ v₂ : V}
    (h₁ : (ctRoundProtocol P V procs fallback).decision F H tick deliver x k₁ p₁ = some v₁)
    (h₂ : (ctRoundProtocol P V procs fallback).decision F H tick deliver x k₂ p₂ = some v₂) :
    v₁ = v₂ := by
  obtain ⟨r₁, hlock₁⟩ := ctSt_decided_locked F H tick deliver x k₁ p₁ v₁ h₁
  obtain ⟨r₂, hlock₂⟩ := ctSt_decided_locked F H tick deliver x k₂ p₂ v₂ h₂
  rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
  · exact (ctRoundProtocol_lock_preservation F H tick deliver x hlock₁ hlt hlock₂.1).symm
  · have heq := hlock₁.1.symm.trans hlock₂.1
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at heq
    exact heq
  · exact ctRoundProtocol_lock_preservation F H tick deliver x hlock₂ hgt hlock₁.1

end Safety

/-! ### Conditional termination under `◇S` (`IsEventuallyStrong`) and `◇W` (`IsEventuallyWeak`) -/

section Liveness

variable {P V : Type*} [Fintype P] [DecidableEq P]

private theorem length_filter_ge_card {α : Type*} {l : List α} {p : α → Bool}
    {S : Finset α} (hl : ∀ x ∈ S, x ∈ l ∧ p x = true) :
    S.card ≤ (l.filter p).length := by
  classical
  have hsub : S ⊆ (l.dedup.filter p).toFinset := fun x hx => by
    obtain ⟨hmem, hp⟩ := hl x hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_dedup]
    exact ⟨hmem, hp⟩
  calc S.card
      ≤ (l.dedup.filter p).toFinset.card := card_le_card hsub
    _ = (l.dedup.filter p).length := List.toFinset_card_of_nodup (l.nodup_dedup.filter p)
    _ ≤ (l.filter p).length := (l.dedup_sublist.filter p).length_le

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Lemma 6.2.2, pp. 245–246][ChandraToueg1996]): under `2 * t < Fintype.card P`, if
`rStar` is coordinated by `qStar ∈ F.Correct`, all faulty processes have crashed by
`tick (4 * rStar)`, and no correct process suspects `qStar` from `tick (4 * rStar)` onward, then
every `p ∈ F.Correct` has decided in `ctRoundProtocol` by subround `4 * (rStar + 1)`. -/
theorem ctRoundProtocol_decides_in_good_round
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {t : ℕ} (ht : 2 * t < Fintype.card P)
    {F : FailurePattern P} {H : DetectorHistory P}
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool}
    (hadm : AdmissibleFDNetwork F H t tick deliver) (x : P → V)
    {rStar : ℕ} {qStar : P} (hqStar : qStar ∈ F.Correct)
    (hcoord : rotatingCoordinator procs fallback rStar = qStar)
    (hstab : ∀ k, 4 * rStar ≤ k → ∀ j, j ∉ F (tick k) → j ∈ F.Correct)
    (hunsusp : ∀ k, 4 * rStar ≤ k → ∀ p ∈ F.Correct, qStar ∉ H p (tick k)) :
    ∀ p ∈ F.Correct,
      ((ctRoundProtocol P V procs fallback).decision F H tick deliver x
        (4 * (rStar + 1)) p).isSome = true := by
  let π := ctRoundProtocol P V procs fallback
  let st := π.state F H tick deliver x
  have hstate_succ (k : ℕ) (p : P) :
      st (k + 1) p =
        if p ∈ F (tick k) then st k p
        else ctUpdate procs fallback k p (st k p) (H p (tick k))
          (π.incoming F tick deliver (st k) k p) := rfl
  have hsend (k : ℕ) (q : P) (s : CTState V) (p : P) : π.send k q s p = ctSend k q s p := rfl
  -- Subround `0` (`4 * rStar`): `qStar` gathers `≥ |P|/2 + 1` estimates and sets `proposal`.
  have hprop : ∃ vStar, (st (4 * rStar + 1) qStar).proposal = some (rStar, vStar) := by
    have hq_alive : qStar ∉ F (tick (4 * rStar)) := hqStar (tick (4 * rStar))
    have hm0 : (4 * rStar) % 4 = 0 := by omega
    have hd0 : (4 * rStar) / 4 = rStar := by omega
    let m₀ := π.incoming F tick deliver (st (4 * rStar)) (4 * rStar) qStar
    let pairs := procs.dedup.filterMap fun j => extractPhase1 (m₀ j)
    let S₀ := Finset.univ.filter fun j =>
      decide (j ∉ F (tick (4 * rStar)) ∧ deliver (4 * rStar) j qStar = true)
    have hS₀_card : Fintype.card P - t ≤ S₀.card := hadm.quorum_delivery (4 * rStar) qStar hqStar
    have hpairs_len : Fintype.card P / 2 + 1 ≤ pairs.length := by
      rw [length_filterMap_eq_length_filter]
      refine (show Fintype.card P / 2 + 1 ≤ Fintype.card P - t by omega).trans
        (hS₀_card.trans (length_filter_ge_card fun j hj => ?_))
      simp only [S₀, mem_filter, mem_univ, true_and, decide_eq_true_eq] at hj
      refine ⟨List.mem_dedup.mpr (hprocs j), ?_⟩
      simp only [m₀, FDAsyncRoundProtocol.incoming, hj, not_false_eq_true, and_self, ↓reduceIte,
        hsend, ctSend, hm0, extractPhase1, Option.isSome_some]
    obtain ⟨⟨vStar, ts_max⟩, hsel⟩ := Option.isSome_iff_exists.mp
      (selectMaxTs_isSome_of_ne_nil (List.ne_nil_of_length_pos (by omega) : pairs ≠ []))
    refine ⟨vStar, ?_⟩
    rw [hstate_succ]
    simp only [hq_alive, ↓reduceIte, ctUpdate, hm0, hd0, hcoord]
    simp only [pairs, m₀] at hpairs_len hsel
    simp only [hpairs_len, ↓reduceIte, hsel]
  obtain ⟨vStar, hvStar⟩ := hprop
  -- Subround `1` (`4 * rStar + 1`): `qStar`'s proposal stays `some (rStar, vStar)` and every
  -- `j ∈ F.Correct` receives it (since `qStar ∉ H j`) and sets `reply = some (rStar, true)`.
  have hm1 : (4 * rStar + 1) % 4 = 1 := by omega
  have hd1 : (4 * rStar + 1) / 4 = rStar := by omega
  have hprop_2 : (st (4 * rStar + 2) qStar).proposal = some (rStar, vStar) := by
    change (st ((4 * rStar + 1) + 1) qStar).proposal = some (rStar, vStar)
    rw [hstate_succ]
    simp only [hqStar (tick (4 * rStar + 1)), ↓reduceIte, ctUpdate, hm1, hd1, Nat.reduceEqDiff]
    repeat' split
    all_goals exact hvStar
  have hack_all : ∀ j ∈ F.Correct, (st (4 * rStar + 2) j).reply = some (rStar, true) := by
    intro j hj
    have hj_alive : j ∉ F (tick (4 * rStar + 1)) := hj (tick (4 * rStar + 1))
    have hq_alive : qStar ∉ F (tick (4 * rStar + 1)) := hqStar (tick (4 * rStar + 1))
    have hdel : deliver (4 * rStar + 1) qStar j = true :=
      hadm.deliver_of_notMem hj (hunsusp (4 * rStar + 1) (by omega) j hj)
    have hinc1 : π.incoming F tick deliver (st (4 * rStar + 1)) (4 * rStar + 1) j qStar =
        some (.phase2 (some (rStar, vStar))) := by
      simp only [FDAsyncRoundProtocol.incoming, hq_alive, not_false_eq_true, hdel, and_self,
        ↓reduceIte, hsend, ctSend, hm1, hvStar]
    change (st ((4 * rStar + 1) + 1) j).reply = some (rStar, true)
    rw [hstate_succ]
    simp only [hj_alive, ↓reduceIte, ctUpdate, hm1, hd1, hcoord, hinc1, Nat.reduceEqDiff]
  -- Subround `2` (`4 * rStar + 2`): every alive sender is in `F.Correct`, so `qStar` receives
  -- `≥ |P|/2 + 1` `ack`s and sets `decided.isSome = true`.
  have hm2 : (4 * rStar + 2) % 4 = 2 := by omega
  have hd2 : (4 * rStar + 2) / 4 = rStar := by omega
  have hq_dec : (st (4 * rStar + 3) qStar).decided.isSome = true := by
    have hq_alive : qStar ∉ F (tick (4 * rStar + 2)) := hqStar (tick (4 * rStar + 2))
    let m₂ := π.incoming F tick deliver (st (4 * rStar + 2)) (4 * rStar + 2) qStar
    let S₂ := Finset.univ.filter fun j =>
      decide (j ∉ F (tick (4 * rStar + 2)) ∧ deliver (4 * rStar + 2) j qStar = true)
    have hS₂_card : Fintype.card P - t ≤ S₂.card :=
      hadm.quorum_delivery (4 * rStar + 2) qStar hqStar
    have hacks_len : Fintype.card P / 2 + 1 ≤
        (procs.dedup.filter fun j => isRoundAck rStar (m₂ j)).length := by
      refine (show Fintype.card P / 2 + 1 ≤ Fintype.card P - t by omega).trans
        (hS₂_card.trans (length_filter_ge_card fun j hj => ?_))
      simp only [S₂, mem_filter, mem_univ, true_and, decide_eq_true_eq] at hj
      have hj_corr : j ∈ F.Correct := hstab (4 * rStar + 2) (by omega) j hj.1
      refine ⟨List.mem_dedup.mpr (hprocs j), ?_⟩
      simp only [m₂, FDAsyncRoundProtocol.incoming, hj, not_false_eq_true, and_self, ↓reduceIte,
        hsend, ctSend, hm2, hack_all j hj_corr, isRoundAck, decide_true]
    change (st ((4 * rStar + 2) + 1) qStar).decided.isSome = true
    rw [hstate_succ]
    simp only [m₂] at hacks_len
    simp only [hq_alive, ↓reduceIte, ctUpdate, hm2, hd2, hcoord, hprop_2, hacks_len, and_self,
      Nat.reduceEqDiff, Option.isSome_or, Option.isSome_some, Bool.or_true]
  -- Subround `3` (`4 * rStar + 3`): `qStar` broadcasts `decided` and every `p ∈ F.Correct`
  -- receives it (`qStar ∉ H p`) and decides!
  obtain ⟨dStar, hdStar⟩ := Option.isSome_iff_exists.mp hq_dec
  have hm3 : (4 * rStar + 3) % 4 = 3 := by omega
  intro p hp
  have hp_alive : p ∉ F (tick (4 * rStar + 3)) := hp (tick (4 * rStar + 3))
  have hq_alive : qStar ∉ F (tick (4 * rStar + 3)) := hqStar (tick (4 * rStar + 3))
  have hdel : deliver (4 * rStar + 3) qStar p = true :=
    hadm.deliver_of_notMem hp (hunsusp (4 * rStar + 3) (by omega) p hp)
  let m₃ := π.incoming F tick deliver (st (4 * rStar + 3)) (4 * rStar + 3) p
  have hq_extract : extractDecide (m₃ qStar) = some dStar := by
    simp only [m₃, FDAsyncRoundProtocol.incoming, hq_alive, not_false_eq_true, hdel, and_self,
      ↓reduceIte, hsend, ctSend, hm3, hdStar, extractDecide]
  have hinc_some : (procs.dedup.findSome? fun j => extractDecide (m₃ j)).isSome = true :=
    List.findSome?_isSome_iff.mpr
      ⟨qStar, List.mem_dedup.mpr (hprocs qStar), by rw [hq_extract]; rfl⟩
  rw [show 4 * (rStar + 1) = (4 * rStar + 3) + 1 by omega]
  change (st ((4 * rStar + 3) + 1) p).decided.isSome = true
  rw [hstate_succ]
  simp only [m₃] at hinc_some
  simp only [hp_alive, ↓reduceIte, ctUpdate, hm3, Nat.reduceEqDiff, Option.isSome_or, hinc_some,
    Bool.or_true]

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Lemma 6.2.2, pp. 245–246][ChandraToueg1996]): under `2 * t < Fintype.card P` and
`IsEventuallyStrong F H` (`◇S`), every correct process eventually decides in `ctRoundProtocol`. -/
theorem ctRoundProtocol_terminates_of_isEventuallyStrong
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {t : ℕ} (ht : 2 * t < Fintype.card P)
    {F : FailurePattern P} {H : DetectorHistory P}
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool}
    (hadm : AdmissibleFDNetwork F H t tick deliver) (hES : IsEventuallyStrong F H)
    (x : P → V) :
    ∃ kStar, ∀ p ∈ F.Correct,
      ((ctRoundProtocol P V procs fallback).decision F H tick deliver x kStar p).isSome =
        true := by
  obtain ⟨t_stab, hstab⟩ := F.exists_stabilize
  obtain ⟨t_ewa, qStar, hqStar, h_unsusp⟩ := hES.2
  let r₀ := max t_stab t_ewa
  obtain ⟨rStar, hr₀_le, _, hcoord⟩ := exists_rotatingCoordinator_eq hprocs fallback qStar r₀
  refine ⟨4 * (rStar + 1), ctRoundProtocol_decides_in_good_round hprocs fallback ht hadm x hqStar
    hcoord (fun k hk j hj => ?_) (fun k hk p hp => ?_)⟩
  · have htk : t_stab ≤ tick k := by
      have hid : k ≤ tick k := hadm.tick_strictMono.id_le k
      have h1 : t_stab ≤ r₀ := le_max_left t_stab t_ewa
      omega
    exact (hstab (tick k) htk).2 j |>.mp hj
  · have htk : t_ewa ≤ tick k := by
      have hid : k ≤ tick k := hadm.tick_strictMono.id_le k
      have h2 : t_ewa ≤ r₀ := le_max_right t_stab t_ewa
      omega
    exact h_unsusp (tick k) htk p hp

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Theorem 6.2.3, p. 246][ChandraToueg1996]): the `t`-oblivious protocol
`ctRoundProtocol P V procs fallback` solves `t`-resilient consensus under `IsEventuallyStrong`
(`◇S`) for every `t` with `2 * t < Fintype.card P`. -/
theorem solvesFDAsyncRoundConsensus_ctRoundProtocol
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {t : ℕ} (ht : 2 * t < Fintype.card P) :
    (ctRoundProtocol P V procs fallback).SolvesFDAsyncRoundConsensus t IsEventuallyStrong where
  irrevocable F _ H tick deliver x _ _ _ _ hk p _ v hdec :=
    ctRoundProtocol_irrevocable F H tick deliver x hk p v hdec
  agreement F _ H tick deliver x _ _ _ _ _ _ _ _ _ _ h₁ h₂ :=
    ctRoundProtocol_uniform_agreement F H tick deliver x h₁ h₂
  validity F _ H tick deliver x _ _ _ _ _ _ hdec :=
    ctRoundProtocol_validity F H tick deliver x hdec
  termination F _ H tick deliver x hadm hES p hp := by
    obtain ⟨kStar, hkStar⟩ :=
      ctRoundProtocol_terminates_of_isEventuallyStrong hprocs fallback ht hadm hES x
    exact ⟨kStar, hkStar p hp⟩

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Corollary 6.2.4, pp. 246–247][ChandraToueg1996]): given any `◇W` history `H`
(`IsEventuallyWeak F H`) and `AdmissibleGossipSchedule F gSched`, running `ctRoundProtocol` over the
gossip-boosted history `gossipHistory H gSched` terminates across all `F.Correct` under any
`AdmissibleFDNetwork` (which exists by `exists_admissibleFDNetwork_of_strongCompleteness`) whenever
`2 * t < Fintype.card P`. -/
theorem ctRoundProtocol_terminates_of_isEventuallyWeak_gossip
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {t : ℕ} (ht : 2 * t < Fintype.card P)
    {F : FailurePattern P} {H : DetectorHistory P} (hEW : IsEventuallyWeak F H)
    {gSched : P → ℕ → List (GossipPacket P)} (hgossip : AdmissibleGossipSchedule F gSched)
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool}
    (hadm : AdmissibleFDNetwork F (gossipHistory H gSched) t tick deliver) (x : P → V) :
    ∃ kStar, ∀ p ∈ F.Correct,
      ((ctRoundProtocol P V procs fallback).decision F (gossipHistory H gSched) tick deliver x
        kStar p).isSome = true :=
  ctRoundProtocol_terminates_of_isEventuallyStrong hprocs fallback ht hadm
    (gossipHistory_isEventuallyStrong_of_isEventuallyWeak hgossip hEW) x

end Liveness

/-! ### `2 ≤ Fintype.card P ≤ 2 * t` Impossibility Even Under `◇P` (`IsEventuallyPerfect`) -/

/-- Prefix indistinguishability on a closed group `S : P → Prop` for `FDAsyncRoundProtocol.state`:
if `x₁` and `x₂` agree on `S`, and before subround `N` every `p` in `S` is non-crashed in both
runs, observes identical failure-detector sets, and receives messages from the exact same set of
non-crashed senders (all belonging to `S`), then `state` agrees on `S` for all `k ≤ N`. -/
private theorem fdState_eq_of_prefix {P V State Msg : Type*} [DecidableEq P]
    (π : FDAsyncRoundProtocol P V State Msg)
    {F₁ F₂ : FailurePattern P} {H₁ H₂ : DetectorHistory P}
    {tick : ℕ → ℕ} {d₁ d₂ : ℕ → P → P → Bool} {x₁ x₂ : P → V}
    {S : P → Prop} {N : ℕ}
    (hx : ∀ p, S p → x₁ p = x₂ p)
    (hstep : ∀ k < N, ∀ p, S p →
      p ∉ F₁ (tick k) ∧ p ∉ F₂ (tick k) ∧ H₁ p (tick k) = H₂ p (tick k) ∧
      ∀ q, ((q ∉ F₁ (tick k) ∧ d₁ k q p = true) ↔ (q ∉ F₂ (tick k) ∧ d₂ k q p = true)) ∧
        ((q ∉ F₂ (tick k) ∧ d₂ k q p = true) → S q)) :
    ∀ k ≤ N, ∀ p, S p →
      π.state F₁ H₁ tick d₁ x₁ k p = π.state F₂ H₂ tick d₂ x₂ k p
  | 0, _, p, hp => by simp only [FDAsyncRoundProtocol.state, hx p hp]
  | k + 1, hk, p, hp => by
    obtain ⟨hp₁, hp₂, hH, hdel⟩ := hstep k (by omega) p hp
    simp only [FDAsyncRoundProtocol.state, hp₁, hp₂, ↓reduceIte]
    have hprev := fdState_eq_of_prefix π hx hstep k (by omega) p hp
    have hinc : π.incoming F₁ tick d₁ (π.state F₁ H₁ tick d₁ x₁ k) k p =
        π.incoming F₂ tick d₂ (π.state F₂ H₂ tick d₂ x₂ k) k p := by
      funext q
      obtain ⟨hiff, hclosed⟩ := hdel q
      simp only [FDAsyncRoundProtocol.incoming]
      by_cases hq₂ : q ∉ F₂ (tick k) ∧ d₂ k q p = true
      · have hq₁ : q ∉ F₁ (tick k) ∧ d₁ k q p = true := hiff.mpr hq₂
        simp only [hq₁, hq₂, not_false_eq_true, and_self, ↓reduceIte]
        rw [fdState_eq_of_prefix π hx hstep k (by omega) q (hclosed hq₂)]
      · have hq₁ : ¬ (q ∉ F₁ (tick k) ∧ d₁ k q p = true) := fun h1 => hq₂ (hiff.mp h1)
        simp only [hq₁, hq₂, ↓reduceIte]
    rw [hprev, hH, hinc]

/-- In a partitioned `◇P` scenario where `C = univ \ A` crashes at `t = 0`, `H = fun _ _ => C`, and
all inputs equal `v`, any protocol solving `SolvesFDAsyncRoundConsensus t IsEventuallyPerfect` leads
`a ∈ A` to decide `some v` at some subround `K`. -/
private theorem isolated_half_decides {P V S M : Type*} [Fintype P] [DecidableEq P]
    {π : FDAsyncRoundProtocol P V S M} {t : ℕ}
    (hsol : π.SolvesFDAsyncRoundConsensus t IsEventuallyPerfect)
    {A C : Finset P} (hC : ∀ p, p ∈ C ↔ p ∉ A)
    (hC_le : C.card ≤ t) (hA_quorum : Fintype.card P - t ≤ A.card)
    {a : P} (ha : a ∈ A) (partDeliver : ℕ → P → P → Bool)
    (hdel : ∀ k q p, partDeliver k q p = true ↔ (q ∈ A ↔ p ∈ A)) (v : V) :
    ∃ K, π.decision (FailurePattern.const C) (fun _ _ => C) id partDeliver (fun _ => v) K a =
      some v := by
  let F_c : FailurePattern P := FailurePattern.const C
  let H_c : DetectorHistory P := fun _ _ => C
  have hEP : IsEventuallyPerfect F_c H_c := by
    refine ⟨⟨0, fun p hp _ _ _ _ => ?_⟩, ⟨0, fun _ _ p hp _ _ => ?_⟩⟩
    · simpa only [F_c, FailurePattern.crashed_const, mem_coe] using hp
    · simpa only [F_c, H_c, FailurePattern.correct_const, Set.mem_compl_iff, mem_coe] using hp
  have hadm : AdmissibleFDNetwork F_c H_c t id partDeliver := by
    refine ⟨strictMono_id, fun k p hp q => ?_, fun k p hp => ?_⟩
    · have hp_A : p ∈ A := by by_contra hnA; exact hp k ((hC p).mpr hnA)
      by_cases hq_A : q ∈ A
      · exact Or.inl ⟨fun hq_C => ((hC q).mp hq_C) hq_A, (hdel k q p).mpr (iff_of_true hq_A hp_A)⟩
      · exact Or.inr ((hC q).mpr hq_A)
    · have hp_A : p ∈ A := by by_contra hnA; exact hp k ((hC p).mpr hnA)
      have heq : (Finset.univ.filter fun q =>
          decide (q ∉ F_c (id k) ∧ partDeliver k q p = true)) = A := by
        ext q
        simp only [F_c, FailurePattern.const_apply, mem_filter, mem_univ, true_and,
          decide_eq_true_eq, hC q, Classical.not_not, hdel k q p, hp_A, iff_true, and_self]
      rw [heq]
      exact hA_quorum
  have ha_corr : a ∈ F_c.Correct := fun _ hc => ((hC a).mp hc) ha
  obtain ⟨K, hK⟩ := hsol.termination F_c (fun _ => hC_le) H_c id partDeliver (fun _ => v)
    hadm hEP a ha_corr
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hK
  obtain ⟨_, hw_eq⟩ := hsol.validity F_c (fun _ => hC_le) H_c id partDeliver (fun _ => v)
    hadm hEP K a ha_corr w hw
  exact ⟨K, hw_eq ▸ hw⟩

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Theorem 6.3.1, pp. 247–248][ChandraToueg1996]): when
`2 ≤ Fintype.card P ≤ 2 * t` and `V` has at least two distinct values, no `FDAsyncRoundProtocol`
solves `SolvesFDAsyncRoundConsensus t IsEventuallyPerfect` (and hence none solves it under `◇S` or
`◇W`). -/
theorem not_solvesFDAsyncRoundConsensus_eventuallyPerfect {P V S M : Type*}
    [Fintype P] [DecidableEq P] [Nontrivial V]
    (π : FDAsyncRoundProtocol P V S M) {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h2t : Fintype.card P ≤ 2 * t) :
    ¬ π.SolvesFDAsyncRoundConsensus t IsEventuallyPerfect := by
  intro hsol
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let n := Fintype.card P
  let half := n / 2
  let e := Fintype.equivFin P
  let A₀ : Finset P := Finset.univ.filter fun p => (e p : ℕ) < half
  let A₁ : Finset P := Finset.univ \ A₀
  have hA₀_card : A₀.card = half := by
    rw [← card_map (e.toEmbedding.trans Fin.valEmbedding), ← card_range half]
    congr 1; ext m
    simp only [A₀, mem_map, mem_filter, mem_univ, true_and, mem_range,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply]
    exact ⟨fun ⟨p, hp, hpm⟩ => hpm ▸ hp, fun hm => ⟨e.symm ⟨m, by omega⟩, by simpa using hm,
      by simp⟩⟩
  have hA₁_card : A₁.card = n - half := by
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A₀)
    simp only [A₁, Finset.card_univ, n] at hs ⊢
    omega
  have hA₀_le : A₀.card ≤ t := by omega
  have hA₁_le : A₁.card ≤ t := by omega
  have hA₀_quorum : n - t ≤ A₀.card := by omega
  have hA₁_quorum : n - t ≤ A₁.card := by omega
  let a₀ : P := e.symm ⟨0, by omega⟩
  let a₁ : P := e.symm ⟨n - 1, by omega⟩
  have ha₀ : a₀ ∈ A₀ := by
    simp only [a₀, A₀, mem_filter, mem_univ, Equiv.apply_symm_apply, true_and]
    omega
  have ha₁_not_A₀ : a₁ ∉ A₀ := by
    simp only [a₁, A₀, mem_filter, mem_univ, Equiv.apply_symm_apply, true_and]
    omega
  have ha₁ : a₁ ∈ A₁ := mem_sdiff.mpr ⟨mem_univ a₁, ha₁_not_A₀⟩
  let partDeliver : ℕ → P → P → Bool := fun _ q p => decide (q ∈ A₀ ↔ p ∈ A₀)
  -- Scenario 0 (`A₁` crashes at `t = 0`, inputs `v₀`) and Scenario 1 (`A₀` crashes, inputs `v₁`):
  let F₀ : FailurePattern P := FailurePattern.const A₁
  let H₀ : DetectorHistory P := fun _ _ => A₁
  obtain ⟨K₀, hw₀⟩ := isolated_half_decides hsol
    (fun p => by simp only [A₁, mem_sdiff, mem_univ, true_and]) hA₁_le hA₀_quorum ha₀
    partDeliver (fun _ _ _ => decide_eq_true_iff) v₀
  let F₁ : FailurePattern P := FailurePattern.const A₀
  let H₁ : DetectorHistory P := fun _ _ => A₀
  obtain ⟨K₁, hw₁⟩ := isolated_half_decides hsol
    (fun p => by simp only [A₁, mem_sdiff, mem_univ, true_and, Classical.not_not]) hA₀_le hA₁_quorum
    ha₁ partDeliver (fun _ q p => by
      simp only [partDeliver, decide_eq_true_eq, A₁, mem_sdiff, mem_univ, true_and]
      exact Decidable.not_iff_not.symm) v₁
  -- Scenario A: zero crashes (`F_A = const ∅`), partition heals at `G = max K₀ K₁` while `H_A`
  -- suspects the opposite half before `G` and `∅` from `G` onward (`IsEventuallyPerfect F_A H_A`).
  let G := max K₀ K₁
  let F_A : FailurePattern P := FailurePattern.const ∅
  let H_A : DetectorHistory P := fun p s =>
    if s < G then (if p ∈ A₀ then A₁ else A₀) else ∅
  let deliver_A : ℕ → P → P → Bool := fun k q p =>
    if k < G then partDeliver k q p else true
  let x_A : P → V := fun p => if p ∈ A₀ then v₀ else v₁
  have hEP_A : IsEventuallyPerfect F_A H_A := by
    refine ⟨⟨0, fun p hp => ?_⟩, ⟨G, fun s hs p _ q _ => ?_⟩⟩
    · simp only [F_A, FailurePattern.crashed_const, coe_empty, Set.mem_empty_iff_false] at hp
    · have hlt : ¬ s < G := by omega
      simp only [H_A, hlt, ↓reduceIte, notMem_empty, not_false_eq_true]
  have hadm_A : AdmissibleFDNetwork F_A H_A t id deliver_A := by
    refine ⟨strictMono_id, fun k p _ q => ?_, fun k p _ => ?_⟩
    · by_cases hk : k < G <;> by_cases hp : p ∈ A₀ <;> by_cases hq : q ∈ A₀ <;>
        simp [deliver_A, H_A, F_A, partDeliver, A₁, hk, hp, hq]
    · have heq : (Finset.univ.filter fun q => decide (q ∉ F_A (id k) ∧ deliver_A k q p = true)) =
          if k < G then (if p ∈ A₀ then A₀ else A₁) else Finset.univ := by
        ext q
        by_cases hk : k < G <;> by_cases hp : p ∈ A₀ <;> by_cases hq : q ∈ A₀ <;>
          simp [F_A, deliver_A, partDeliver, A₁, hk, hp, hq]
      rw [heq]
      split_ifs
      exacts [hA₀_quorum, hA₁_quorum, by rw [card_univ]; omega]
  -- Indistinguishability on `A₀` up to `K₀ ≤ G` and on `A₁` up to `K₁ ≤ G`:
  have hdec_a₀ : π.decision F_A H_A id deliver_A x_A K₀ a₀ = some v₀ := by
    change π.output a₀ (π.state F_A H_A id deliver_A x_A K₀ a₀) = some v₀
    rw [fdState_eq_of_prefix π (F₂ := F₀) (H₂ := H₀) (d₂ := partDeliver) (x₂ := fun _ => v₀)
      (S := fun p => p ∈ A₀)
      (fun p hp => by simp only [x_A, hp, ↓reduceIte])
      (fun k hk p hp => by
        have hkG : k < G := lt_of_lt_of_le hk (le_max_left K₀ K₁)
        have hp_not_A₁ : p ∉ A₁ := fun h => (mem_sdiff.mp h).2 hp
        refine ⟨by simp [F_A], hp_not_A₁, by simp [H_A, H₀, hkG, hp], fun q => ⟨?_, ?_⟩⟩
        · simp only [F_A, F₀, FailurePattern.const_apply, notMem_empty, not_false_eq_true, true_and,
            deliver_A, hkG, ↓reduceIte, partDeliver, hp, iff_true, decide_eq_true_eq, A₁, mem_sdiff,
            mem_univ, Classical.not_not, and_self]
        · intro hq
          simp only [partDeliver, hp, iff_true, decide_eq_true_eq] at hq
          exact hq.2)
      K₀ le_rfl a₀ ha₀]
    exact hw₀
  have hdec_a₁ : π.decision F_A H_A id deliver_A x_A K₁ a₁ = some v₁ := by
    change π.output a₁ (π.state F_A H_A id deliver_A x_A K₁ a₁) = some v₁
    rw [fdState_eq_of_prefix π (F₂ := F₁) (H₂ := H₁) (d₂ := partDeliver) (x₂ := fun _ => v₁)
      (S := fun p => p ∉ A₀)
      (fun p hp => by simp only [x_A, hp, ↓reduceIte])
      (fun k hk p hp => by
        have hkG : k < G := lt_of_lt_of_le hk (le_max_right K₀ K₁)
        refine ⟨by simp [F_A], hp, by simp [H_A, H₁, hkG, hp], fun q => ⟨?_, ?_⟩⟩
        · simp only [F_A, F₁, FailurePattern.const_apply, notMem_empty, not_false_eq_true, true_and,
            deliver_A, hkG, ↓reduceIte, partDeliver, hp, iff_false, decide_eq_true_eq, and_self]
        · exact fun hq => hq.1)
      K₁ le_rfl a₁ ha₁_not_A₀]
    exact hw₁
  have hag := hsol.agreement F_A (fun _ => by simp [F_A]) H_A id deliver_A x_A hadm_A hEP_A
    K₀ K₁ a₀ (by simp [F_A]) a₁ (by simp [F_A]) v₀ v₁ hdec_a₀ hdec_a₁
  exact hne hag

/-! ### Exact asynchronous-round resilience characterizations -/

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Theorems 6.2.3 and 6.3.1, pp. 246–248][ChandraToueg1996]): over
`[Nontrivial V]`, `t`-resilient consensus in `FDAsyncRoundProtocol` under `IsEventuallyStrong`
(`◇S`) is solvable if and only if `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`. -/
theorem exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff.{u, v} (P : Type u) (V : Type v)
    [Fintype P] [DecidableEq P] [Nontrivial V] (t : ℕ) :
    (∃ (S M : Type v) (π : FDAsyncRoundProtocol P V S M),
      π.SolvesFDAsyncRoundConsensus t IsEventuallyStrong) ↔
      Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P := by
  constructor
  · rintro ⟨S, M, π, hsol⟩
    by_contra! h
    exact not_solvesFDAsyncRoundConsensus_eventuallyPerfect π (by omega) h.2
      (hsol.mono fun _ hcorr _ hEP => hEP.toEventuallyStrong hcorr)
  · rintro (h1 | h2t)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1
      exact ⟨V, PUnit.{v + 1}, ownInputFDProtocol P V,
        solvesFDAsyncRoundConsensus_ownInput t IsEventuallyStrong⟩
    · let e := Fintype.equivFin P
      let procs : List P := List.ofFn e.symm
      have hprocs : ∀ p : P, p ∈ procs := fun p =>
        List.mem_ofFn.mpr ⟨e p, Equiv.symm_apply_apply e p⟩
      let fallback : P := e.symm ⟨0, by omega⟩
      exact ⟨CTState V, CTMsg V, ctRoundProtocol P V procs fallback,
        solvesFDAsyncRoundConsensus_ctRoundProtocol hprocs fallback h2t⟩

/-- Asynchronous-round step for #7503 (after
[Chandra and Toueg, Theorems 6.2.3 and 6.3.1, pp. 246–248][ChandraToueg1996]): over
`[Nontrivial V]`, strengthening `◇S` to `◇P` (`IsEventuallyPerfect`) yields the identical
asynchronous-round resilience threshold `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`. -/
theorem exists_solvesFDAsyncRoundConsensus_eventuallyPerfect_iff.{u, v} (P : Type u) (V : Type v)
    [Fintype P] [DecidableEq P] [Nontrivial V] (t : ℕ) :
    (∃ (S M : Type v) (π : FDAsyncRoundProtocol P V S M),
      π.SolvesFDAsyncRoundConsensus t IsEventuallyPerfect) ↔
      Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P := by
  constructor
  · rintro ⟨S, M, π, hsol⟩
    by_contra! h
    exact not_solvesFDAsyncRoundConsensus_eventuallyPerfect π (by omega) h.2 hsol
  · rintro (h1 | h2t)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1
      exact ⟨V, PUnit.{v + 1}, ownInputFDProtocol P V,
        solvesFDAsyncRoundConsensus_ownInput t IsEventuallyPerfect⟩
    · obtain ⟨S, M, π, hsol⟩ :=
        (exists_solvesFDAsyncRoundConsensus_eventuallyStrong_iff P V t).mpr (Or.inr h2t)
      exact ⟨S, M, π, hsol.mono fun _ hcorr _ hEP => hEP.toEventuallyStrong hcorr⟩

end Cslib.Distributed.FailureDetectors
