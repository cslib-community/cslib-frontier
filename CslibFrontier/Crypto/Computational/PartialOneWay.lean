/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.QueryCount.Expected
public import CslibFrontier.Languages.Probabilistic.Expect
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState

/-!
# Partial one-wayness games

Partial-guessing one-wayness (PGOW) gives an adversary a public function image and an adaptive
classical oracle that recognizes one distinguished part of the sampled preimage. Partial-domain
one-wayness (PDOW) gives the same public challenge without that oracle. In both games the
challenger checks the adversary's final candidate separately; that check is not an adversary
query.

`partialGuessingToDomainAt` is the executable core of the classical reduction in
[KosugeXagawa2026, Appendix C, Lemma C.1, pp. 33--34]. It runs the PGOW adversary once with false
answers and returns either one selected query or the final output. `partialGuessingToDomain`
samples the paper's exactly uniform slot in `Fin (queryBound + 1)`. This semantic finite-uniform
sampler has no strict fair-coin runtime certificate in general.

`partialGuessingToDomainDyadic` is the fixed-clock-compatible slot-sampling variant. It uses
`ProbComp.sampleDyadicIndex queryBound`, so every source slot has mass
`1 / dyadicSize queryBound`; padding slots return the fixed fallback. Its loss is therefore
`dyadicSize queryBound`, not the paper's `queryBound + 1`. The checked bounds
`queryBound < dyadicSize queryBound ≤ 2 * (queryBound + 1)` keep the asymptotic loss polynomial.

This module defines the exact challenges, games and executable reductions. The adaptive coupling
inequality and machine-resource compiler are deliberately not asserted here: the former must show
that the all-false execution agrees through the first correct query, and the latter must charge
request/reply marshalling and each installed finite table exactly once.

## Main definitions

* `Cslib.Crypto.PartialOneWayChallenge`, `.PartialOneWayDistributionValid`: the sampled triple
  and its support-level relation to an indexed function family.
* `Cslib.Crypto.PartialGuessingAdversary`, `.PartialDomainAdversary`: PGOW and PDOW adversaries.
* `Cslib.Crypto.partialGuessingExperiment`, `.partialDomainExperiment`: the source games.
* `Cslib.Crypto.partialGuessingAllFalsePotential`: expected correct queries plus a correct final
  output in the shared-randomness all-false execution.
* `Cslib.Crypto.partialGuessingToDomain`: the paper's semantic uniform-slot reduction.
* `Cslib.Crypto.partialGuessingToDomainDyadic`: the strict fair-coin slot sampler variant.

## References

* [H. Kosuge, K. Xagawa, *Towards Formal Security Proofs of MQOM*][KosugeXagawa2026],
  Appendix C, Definitions C.2--C.3 and Lemma C.1, pp. 33--34.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped NNReal

/-- A challenge sampled from the source distribution `D_F`: public index `index`, hidden
preimage `secret`, and public image `image`. Distribution validity below states the source's
requirement `image = family index secret` without putting proof data in the executable sample. -/
structure PartialOneWayChallenge (Index Domain Image : Type) where
  /-- Public index of the sampled function. -/
  index : Index
  /-- Hidden sampled preimage. -/
  secret : Domain
  /-- Public function image. -/
  image : Image

/-- Every supported challenge has the required public image. Keeping this predicate separate
from the challenge makes the relation an auditable property of `D_F`, not runtime proof data. -/
def PartialOneWayDistributionValid {Index Domain Image : Type}
    (family : Index → Domain → Image)
    (sample : ProbComp (PartialOneWayChallenge Index Domain Image)) : Prop :=
  ∀ challenge ∈ (ProbComp.eval sample).support,
    family challenge.index challenge.secret = challenge.image

/-- The classical PGOW validation interface returns one Boolean for every candidate. -/
abbrev PartialGuessingResponse (Prefix : Type) : Prefix → Type := fun _ => Bool

/-- A classical PGOW adversary receives the public function index and image, makes adaptive
validation queries, and finally returns a candidate prefix. -/
abbrev PartialGuessingAdversary (Index Image Prefix : Type) :=
  Index → Image → ProbOracleComp (PartialGuessingResponse Prefix) Prefix

/-- A PDOW adversary receives the same public challenge without a validation oracle. -/
abbrev PartialDomainAdversary (Index Image Prefix : Type) :=
  Index → Image → ProbComp Prefix

/-- The exact validation oracle: accept precisely the distinguished part of the sampled secret. -/
def partialGuessingReply {Prefix : Type} [DecidableEq Prefix]
    (secret candidate : Prefix) : Bool :=
  decide (candidate = secret)

theorem partialGuessingReply_eq_true_iff {Prefix : Type} [DecidableEq Prefix]
    {secret candidate : Prefix} : partialGuessingReply secret candidate = true ↔
      candidate = secret := by
  simp only [partialGuessingReply, decide_eq_true_eq]

/-- The source's classical PGOW experiment. The final equality is checked after the oracle run
and is not included in its query count. -/
noncomputable def partialGuessingExperiment {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix)
    (adversary : PartialGuessingAdversary Index Image Prefix) : ProbComp Bool := do
  let challenge ← sample
  let candidate ← (adversary challenge.index challenge.image).run fun guess =>
    pure (partialGuessingReply (part challenge.secret) guess)
  return partialGuessingReply (part challenge.secret) candidate

/-- The source's PDOW experiment on exactly the same challenge distribution. -/
noncomputable def partialDomainExperiment {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix)
    (adversary : PartialDomainAdversary Index Image Prefix) : ProbComp Bool := do
  let challenge ← sample
  let candidate ← adversary challenge.index challenge.image
  return partialGuessingReply (part challenge.secret) candidate

/-- Concrete PGOW success probability. -/
noncomputable def partialGuessingAdvantage {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix)
    (adversary : PartialGuessingAdversary Index Image Prefix) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (partialGuessingExperiment sample part adversary))

/-- Concrete PDOW success probability. -/
noncomputable def partialDomainAdvantage {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix)
    (adversary : PartialDomainAdversary Index Image Prefix) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (partialDomainExperiment sample part adversary))

namespace PartialGuessingAdversary

/-- One bound applies to every public challenge supplied to an adversary. -/
def IsQueryBounded {Index Image Prefix : Type}
    (adversary : PartialGuessingAdversary Index Image Prefix) (queryBound : Nat) : Prop :=
  ∀ index image, (adversary index image).IsQueryBounded queryBound

end PartialGuessingAdversary

/-! ### Adaptive first divergence -/

/-- The law of the real PGOW run on the combined private-sampling and validation interface. The
private-sampling component is unchanged between the real and all-false runs. -/
noncomputable def partialGuessingLaw {Prefix : Type} [DecidableEq Prefix] (secret : Prefix) :
    (q : Nat ⊕ Prefix) → PMF (probOracleSpec (PartialGuessingResponse Prefix) q) :=
  OracleComp.sumHandler ProbComp.unifOracle fun candidate =>
    PMF.pure (partialGuessingReply secret candidate)

/-- The shared-randomness comparison law: preserve every private sample and answer each
validation call with false. -/
noncomputable def partialGuessingFalseLaw {Prefix : Type} :
    (q : Nat ⊕ Prefix) → PMF (probOracleSpec (PartialGuessingResponse Prefix) q) :=
  OracleComp.sumHandler ProbComp.unifOracle fun _ => PMF.pure false

/-- Charge one precisely when an external validation call asks the secret. Private-sampling calls
cost zero. -/
def partialGuessingCorrectCost {Prefix : Type} [DecidableEq Prefix] (secret : Prefix) :
    Nat ⊕ Prefix → ℝ≥0∞ :=
  Sum.elim (fun _ => 0) fun candidate => if candidate = secret then 1 else 0

/-- The all-false potential: the expected number of correct validation calls in the all-false
execution, plus the probability that its final output is correct. Later calls after the first
correct real query are harmless nonnegative slack; this is why the executable full-run reducer
need not pretend to stop early. -/
noncomputable def partialGuessingAllFalsePotential {Prefix : Type} [DecidableEq Prefix]
    (secret : Prefix) (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) : ℝ≥0∞ :=
  OracleComp.expectedCost (partialGuessingFalseLaw (Prefix := Prefix))
      (partialGuessingCorrectCost secret) program +
    OracleComp.evalWith (partialGuessingFalseLaw (Prefix := Prefix)) program secret

/-- **Adaptive first-divergence coupling.** A real PGOW run can succeed only by crossing its first
correct validation query, or by reaching a correct final output without any correct query. Before
that first divergence the real and all-false executions use the same private samples and false
answers. Induction on the adaptive oracle program therefore bounds real success by the all-false
potential.

When the current query is correct, its unit cost alone bounds the remaining real acceptance mass;
the all-false continuation contributes only nonnegative slack. When it is wrong, both executions
take the false continuation and the induction hypothesis applies. Private samples average the
same pointwise inequality in both executions. -/
theorem evalWith_partialGuessingLaw_apply_le_allFalsePotential {Prefix : Type}
    [DecidableEq Prefix] (secret : Prefix)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    OracleComp.evalWith (partialGuessingLaw secret) program secret ≤
      partialGuessingAllFalsePotential secret program := by
  classical
  induction program using OracleComp.induction with
  | pure output =>
      simp [partialGuessingAllFalsePotential]
  | query_bind query cont ih =>
      cases query with
      | inl n =>
          simp only [partialGuessingAllFalsePotential, partialGuessingLaw,
            partialGuessingFalseLaw, partialGuessingCorrectCost,
            OracleComp.sumHandler_inl, OracleComp.evalWith_bind,
            OracleComp.evalWith_query, OracleComp.expectedCost_query_bind, PMF.bind_apply,
            zero_add]
          calc
            (∑' answer, ProbComp.unifOracle n answer *
                OracleComp.evalWith (partialGuessingLaw secret) (cont answer) secret) ≤
                ∑' answer, ProbComp.unifOracle n answer *
                  partialGuessingAllFalsePotential secret (cont answer) :=
              tsum_le_tsum fun answer => mul_le_mul_left' (ih answer) _
            _ = (∑' answer, ProbComp.unifOracle n answer *
                  OracleComp.expectedCost (partialGuessingFalseLaw (Prefix := Prefix))
                    (partialGuessingCorrectCost secret) (cont answer)) +
                ∑' answer, ProbComp.unifOracle n answer *
                  OracleComp.evalWith (partialGuessingFalseLaw (Prefix := Prefix))
                    (cont answer) secret := by
              simp only [partialGuessingAllFalsePotential, mul_add, tsum_add]
      | inr candidate =>
          by_cases hcandidate : candidate = secret
          · subst candidate
            simp [partialGuessingAllFalsePotential, partialGuessingLaw,
              partialGuessingFalseLaw, partialGuessingCorrectCost,
              partialGuessingReply, OracleComp.expectedCost_query_bind]
            calc
              OracleComp.evalWith (partialGuessingLaw secret) (cont true) secret ≤ 1 :=
                PMF.coe_le_one _ _
              _ ≤ 1 + OracleComp.expectedCost
                    (partialGuessingFalseLaw (Prefix := Prefix))
                    (partialGuessingCorrectCost secret) (cont false) +
                  OracleComp.evalWith (partialGuessingFalseLaw (Prefix := Prefix))
                    (cont false) secret :=
                le_add_right (le_add_right le_rfl)
          · simpa [partialGuessingAllFalsePotential, partialGuessingLaw,
              partialGuessingFalseLaw, partialGuessingCorrectCost, hcandidate,
              partialGuessingReply, OracleComp.expectedCost_query_bind] using ih false

/-- The same first-divergence bound for the public `ProbOracleComp.run` interface used by the
PGOW experiment. This is still a full all-false execution: later locally answered calls are
included in the nonnegative potential and must be charged by subsequent resource bounds. -/
theorem eval_run_partialGuessingReply_apply_le_allFalsePotential {Prefix : Type}
    [DecidableEq Prefix] (secret : Prefix)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    ProbComp.eval (program.run fun candidate =>
        pure (partialGuessingReply secret candidate)) secret ≤
      partialGuessingAllFalsePotential secret program := by
  rw [ProbOracleComp.eval_run]
  simpa only [partialGuessingLaw, ProbComp.eval_pure] using
    evalWith_partialGuessingLaw_apply_le_allFalsePotential secret program

/-! ### Executable query selection -/

/-- Private state of the all-false validation handler. It retains only the selected candidate,
not a transcript of all validation queries. -/
structure PartialGuessingSelectionState (Prefix : Type) where
  /-- Number of validation calls already answered. -/
  count : Nat
  /-- Candidate asked at the selected call, if that call occurred. -/
  selected : Option Prefix

namespace PartialGuessingSelectionState

/-- No validation call has occurred and no candidate has been selected. -/
def empty {Prefix : Type} : PartialGuessingSelectionState Prefix :=
  { count := 0, selected := none }

end PartialGuessingSelectionState

/-- Answer every validation call with false while retaining the candidate at `slot`. Calls are
numbered from zero. Continuing after the selected call costs at most one full adversary run and
does not require storing later candidates. -/
def selectFalseOracle {Prefix : Type} (slot : Nat) (candidate : Prefix) :
    StateT (PartialGuessingSelectionState Prefix) ProbComp Bool := fun state =>
  pure (false,
    { count := state.count + 1
      selected := if state.count = slot then some candidate else state.selected })

@[simp] theorem selectFalseOracle_run {Prefix : Type} (slot : Nat) (candidate : Prefix)
    (state : PartialGuessingSelectionState Prefix) :
    (selectFalseOracle slot candidate).run state =
      pure (false,
        { count := state.count + 1
          selected := if state.count = slot then some candidate else state.selected }) := rfl

/-- Extract the selected query for slots below `queryBound`, or the adversary's separately
checked final output for slot `queryBound`. A missing selected query yields `fallback`. -/
def partialGuessingSelectedCandidate {Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (result : Prefix × PartialGuessingSelectionState Prefix) : Prefix :=
  if slot < queryBound then result.2.selected.getD fallback else result.1

@[simp] theorem partialGuessingSelectedCandidate_of_lt {Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (result : Prefix × PartialGuessingSelectionState Prefix)
    (hslot : slot < queryBound) :
    partialGuessingSelectedCandidate fallback queryBound slot result =
      result.2.selected.getD fallback := by
  simp only [partialGuessingSelectedCandidate, hslot, if_true]

@[simp] theorem partialGuessingSelectedCandidate_of_not_lt {Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (result : Prefix × PartialGuessingSelectionState Prefix)
    (hslot : ¬ slot < queryBound) :
    partialGuessingSelectedCandidate fallback queryBound slot result = result.1 := by
  simp only [partialGuessingSelectedCandidate, hslot, if_false]

/-- One deterministic slot of the PGOW-to-PDOW reduction. It runs the adversary once, answers
all validation calls locally with false, and returns either the selected call or final output. -/
def partialGuessingToDomainAt {Index Image Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (adversary : PartialGuessingAdversary Index Image Prefix) :
    PartialDomainAdversary Index Image Prefix := fun index image => do
  let result ← ((adversary index image).runState (selectFalseOracle slot)).run
    PartialGuessingSelectionState.empty
  return partialGuessingSelectedCandidate fallback queryBound slot result

/-- Lemma C.1's semantic reduction: choose exactly one of the `queryBound` validation positions
or the final output, uniformly. `ProbComp.uniform` specifies the exact finite distribution but is
not claimed to have a strict fair-coin clock for arbitrary `queryBound + 1`. -/
noncomputable def partialGuessingToDomain {Index Image Prefix : Type} (fallback : Prefix)
    (queryBound : Nat) (adversary : PartialGuessingAdversary Index Image Prefix) :
    PartialDomainAdversary Index Image Prefix := fun index image => do
  let slot ← ProbComp.uniform (Fin (queryBound + 1))
  partialGuessingToDomainAt fallback queryBound slot adversary index image

/-- Fixed-clock fair-coin slot-sampling variant. The power-of-two sampler covers source slots `0`
through `queryBound`; any remaining padding slot returns `fallback` without running the adversary.
An operational certificate for the composed reduction still has to account for the installed
adversary, local handler and marshalling. -/
noncomputable def partialGuessingToDomainDyadic {Index Image Prefix : Type} (fallback : Prefix)
    (queryBound : Nat) (adversary : PartialGuessingAdversary Index Image Prefix) :
    PartialDomainAdversary Index Image Prefix := fun index image => do
  let slot ← ProbComp.sampleDyadicIndex queryBound
  if slot ≤ queryBound then
    partialGuessingToDomainAt fallback queryBound slot adversary index image
  else
    pure fallback

/-- Every paper slot `0,...,queryBound` lies in the executable sampler's range. -/
theorem partialGuessing_sourceSlot_lt_dyadicSize (queryBound slot : Nat)
    (hslot : slot ≤ queryBound) : slot < Probability.dyadicSize queryBound :=
  hslot.trans_lt (Probability.lt_dyadicSize queryBound)

/-- The exact executable loss is at most twice the paper's `queryBound + 1` loss. -/
theorem partialGuessing_dyadicSize_le (queryBound : Nat) :
    Probability.dyadicSize queryBound ≤ 2 * (queryBound + 1) :=
  Probability.dyadicSize_le queryBound

end Cslib.Crypto
