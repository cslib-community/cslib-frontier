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
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Expect

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

The adaptive first-divergence proof bounds real PGOW success by the number of correct all-false
queries plus a correct final output. A global query budget converts this potential into the
executable slot sum, yielding the paper's exact `queryBound + 1` semantic loss and the dyadic
variant's exact `dyadicSize queryBound` loss. The machine-resource compiler remains separate: it
must charge the complete all-false run, request/reply marshalling and each installed finite table
exactly once.

## Main definitions

* `Cslib.Crypto.PartialOneWayChallenge`, `.PartialOneWayDistributionValid`: the sampled triple
  and its support-level relation to an indexed function family.
* `Cslib.Crypto.PartialGuessingAdversary`, `.PartialDomainAdversary`: PGOW and PDOW adversaries.
* `Cslib.Crypto.partialGuessingExperiment`, `.partialDomainExperiment`: the source games.
* `Cslib.Crypto.partialGuessingAllFalsePotential`: expected correct queries plus a correct final
  output in the shared-randomness all-false execution.
* `Cslib.Crypto.partialGuessingToDomain`: the paper's semantic uniform-slot reduction.
* `Cslib.Crypto.partialGuessingToDomainDyadic`: the strict fair-coin slot sampler variant.

## Main results

* `Cslib.Crypto.evalWith_partialGuessingLaw_apply_le_allFalsePotential`: adaptive
  first-divergence coupling under shared private coins.
* `Cslib.Crypto.partialGuessingAdvantage_le_mul_partialDomainAdvantage`: Lemma C.1 with the
  paper's exact `queryBound + 1` semantic loss.
* `Cslib.Crypto.partialGuessingAdvantage_le_dyadicSize_mul_partialDomainAdvantage`,
  `Cslib.Crypto.partialGuessingAdvantage_le_two_mul_partialDomainAdvantage`: exact and coarse
  strict-fair-coin loss bounds.

## References

* [H. Kosuge, K. Xagawa, *Towards Formal Security Proofs of MQOM*][KosugeXagawa2026],
  Appendix C, Definitions C.2--C.3 and Lemma C.1, pp. 33--34.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal NNReal

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

private theorem partialGuessingAllFalsePotential_pure {Prefix : Type} [DecidableEq Prefix]
    (secret output : Prefix) :
    partialGuessingAllFalsePotential secret
        (pure output : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) =
      if output = secret then 1 else 0 := by
  simp [partialGuessingAllFalsePotential]

private theorem partialGuessingAllFalsePotential_sample_bind {Prefix : Type}
    [DecidableEq Prefix] (secret : Prefix) (n : Nat)
    (cont : Fin (n + 1) → ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    partialGuessingAllFalsePotential secret
        (ProbOracleComp.sample (ProbComp.unifFin n) >>= cont) =
      ∑' answer, ProbComp.unifOracle n answer *
        partialGuessingAllFalsePotential secret (cont answer) := by
  rw [ProbOracleComp.sample_unifFin]
  simp only [partialGuessingAllFalsePotential, partialGuessingFalseLaw,
    partialGuessingCorrectCost, OracleComp.sumHandler_inl,
    OracleComp.expectedCost_query_bind, OracleComp.evalWith_bind,
    OracleComp.evalWith_query, zero_add, PMF.bind_apply]
  simp only [mul_add, tsum_add]

private theorem partialGuessingAllFalsePotential_query_bind {Prefix : Type}
    [DecidableEq Prefix] (secret candidate : Prefix)
    (cont : Bool → ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    partialGuessingAllFalsePotential secret (ProbOracleComp.query candidate >>= cont) =
      (if candidate = secret then 1 else 0) +
        partialGuessingAllFalsePotential secret (cont false) := by
  simp [partialGuessingAllFalsePotential, partialGuessingFalseLaw,
    partialGuessingCorrectCost, OracleComp.expectedCost_query_bind]

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
            have hreply : partialGuessingReply secret secret = true :=
              partialGuessingReply_eq_true_iff.mpr rfl
            rw [partialGuessingAllFalsePotential_query_bind]
            simp only [if_pos rfl, partialGuessingAllFalsePotential, partialGuessingLaw,
              OracleComp.evalWith_bind, OracleComp.evalWith_query,
              OracleComp.sumHandler_inr, hreply, PMF.pure_bind]
            rw [← add_assoc]
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
  /-- Number of validation calls still to skip before retaining a candidate. -/
  remaining : Nat
  /-- Candidate asked at the selected call, if that call occurred. -/
  selected : Option Prefix

namespace PartialGuessingSelectionState

/-- Initialize the one-candidate state for a selected validation slot. -/
def at {Prefix : Type} (slot : Nat) : PartialGuessingSelectionState Prefix :=
  { remaining := slot, selected := none }

end PartialGuessingSelectionState

/-- Answer every validation call with false. Before the selected call, decrement the remaining
skip count; at that call retain its candidate; afterward preserve the retained candidate while the
adversary completes. -/
def selectFalseOracle {Prefix : Type} (candidate : Prefix) :
    StateT (PartialGuessingSelectionState Prefix) ProbComp Bool := fun state =>
  match state.selected with
  | some _ => pure (false, state)
  | none => match state.remaining with
    | 0 => pure (false, { remaining := 0, selected := some candidate })
    | remaining + 1 => pure (false, { remaining, selected := none })

@[simp] theorem selectFalseOracle_run {Prefix : Type} (candidate : Prefix)
    (state : PartialGuessingSelectionState Prefix) :
    (selectFalseOracle candidate).run state = match state.selected with
      | some _ => pure (false, state)
      | none => match state.remaining with
        | 0 => pure (false, { remaining := 0, selected := some candidate })
        | remaining + 1 => pure (false, { remaining, selected := none }) := rfl

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

/-- Execute one fixed source slot against an already instantiated PGOW program. Keeping this
closed-program core separate makes the bounded-slot proof independent of the public challenge
parameters. -/
private def partialGuessingAt {Prefix : Type} (fallback : Prefix) (queryBound slot : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) : ProbComp Prefix := do
  let result ← (program.runState selectFalseOracle).run
    (PartialGuessingSelectionState.at slot)
  return partialGuessingSelectedCandidate fallback queryBound slot result

/-- Success mass of one fixed all-false source slot. -/
private noncomputable def partialGuessingSlotMass {Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (secret : Prefix)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) : ℝ≥0∞ :=
  (ProbOracleComp.runWith
      (fun candidate state => ProbComp.eval ((selectFalseOracle candidate).run state))
      program (PartialGuessingSelectionState.at slot)).map
    (partialGuessingSelectedCandidate fallback queryBound slot) secret

/-- The state-machine definition of a fixed slot has exactly the slot mass above. -/
private theorem eval_partialGuessingAt {Prefix : Type} (fallback : Prefix) (queryBound slot : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    ProbComp.eval (partialGuessingAt fallback queryBound slot program) =
      (ProbOracleComp.runWith
        (fun candidate state => ProbComp.eval ((selectFalseOracle candidate).run state))
        program (PartialGuessingSelectionState.at slot)).map
      (partialGuessingSelectedCandidate fallback queryBound slot) := by
  simp only [partialGuessingAt, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_runState, PMF.bind_pure_comp, Function.comp_def]
  rfl

/-- Once a candidate has been retained, the all-false handler preserves it while the adversary
completes. The remaining execution is the ordinary memoryless all-false run paired with the
unchanged one-candidate state. -/
private theorem runState_selectFalseOracle_selected {Prefix : Type}
    (selected : Prefix) (remaining : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    (program.runState selectFalseOracle).run
        { remaining, selected := some selected } =
      (fun output => (output,
        { remaining, selected := some selected })) <$>
        program.run (fun _ => pure false) := by
  induction program using ProbOracleComp.induction with
  | pure output => rfl
  | sample_bind n cont ih =>
      simp only [ProbOracleComp.runState_bind, ProbOracleComp.runState_sample,
        StateT.run_bind, StateT.lift, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
        ih, bind_pure_comp, Function.comp_def]
  | query_bind candidate cont ih =>
      simp only [ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
        selectFalseOracle, StateT.run_bind, ProbOracleComp.run_bind,
        ProbOracleComp.run_query, pure_bind, ih]

/-- PMF form of `runState_selectFalseOracle_selected`. -/
private theorem runWith_selectFalseOracle_selected {Prefix : Type}
    (selected : Prefix) (remaining : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    ProbOracleComp.runWith
        (fun candidate state => ProbComp.eval ((selectFalseOracle candidate).run state))
        program { remaining, selected := some selected } =
      (ProbComp.eval (program.run fun _ => pure false)).map fun output =>
        (output, { remaining, selected := some selected }) := by
  have h := congrArg ProbComp.eval
    (runState_selectFalseOracle_selected selected remaining program)
  simpa only [ProbOracleComp.eval_runState, ProbComp.eval_map] using h

@[simp] private theorem partialGuessingSlotMass_pure_final {Prefix : Type} [DecidableEq Prefix]
    (fallback secret output : Prefix) (queryBound : Nat) :
    partialGuessingSlotMass fallback queryBound queryBound secret
        (pure output : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) =
      if output = secret then 1 else 0 := by
  simp [partialGuessingSlotMass, PartialGuessingSelectionState.at,
    partialGuessingSelectedCandidate]

private theorem partialGuessingSlotMass_sample_bind {Prefix : Type} (fallback secret : Prefix)
    (queryBound slot n : Nat)
    (cont : Fin (n + 1) → ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    partialGuessingSlotMass fallback queryBound slot secret
        (ProbOracleComp.sample (ProbComp.unifFin n) >>= cont) =
      ∑' answer, ProbComp.unifOracle n answer *
        partialGuessingSlotMass fallback queryBound slot secret (cont answer) := by
  simp only [partialGuessingSlotMass, ProbOracleComp.runWith_sample_bind,
    ProbComp.eval_unifFin, PMF.map_apply, PMF.bind_apply, PMF.map_apply,
    Function.comp_def]
  rfl

@[simp] private theorem partialGuessingSlotMass_query_zero {Prefix : Type} [DecidableEq Prefix]
    (fallback secret candidate : Prefix) (queryBound : Nat)
    (cont : Bool → ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    partialGuessingSlotMass fallback (queryBound + 1) 0 secret
        (ProbOracleComp.query candidate >>= cont) =
      if candidate = secret then 1 else 0 := by
  simp only [partialGuessingSlotMass, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, PartialGuessingSelectionState.at, selectFalseOracle,
    ProbComp.eval_pure, PMF.pure_bind]
  rw [runWith_selectFalseOracle_selected candidate 0 (cont false)]
  simp [partialGuessingSelectedCandidate]

@[simp] private theorem partialGuessingSlotMass_query_succ {Prefix : Type}
    (fallback secret candidate : Prefix)
    (queryBound slot : Nat) (hslot : slot ≤ queryBound)
    (cont : Bool → ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    partialGuessingSlotMass fallback (queryBound + 1) (slot + 1) secret
        (ProbOracleComp.query candidate >>= cont) =
      partialGuessingSlotMass fallback queryBound slot secret (cont false) := by
  simp only [partialGuessingSlotMass, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, PartialGuessingSelectionState.at, selectFalseOracle,
    ProbComp.eval_pure, PMF.pure_bind]
  congr 2 with result
  simp only [partialGuessingSelectedCandidate]
  split_ifs <;> omega

/-- A global query budget turns the all-false potential into the sum of the `queryBound` query
slots and the final-output slot. The proof follows the executable countdown state: an external
call contributes slot zero and shifts every remaining slot into its false continuation, while a
private sample averages the pointwise induction hypothesis under the same coins. -/
private theorem partialGuessingAllFalsePotential_le_sum_slotMass {Prefix : Type}
    [DecidableEq Prefix] (fallback secret : Prefix) (queryBound : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix)
    (hbound : program.IsQueryBounded queryBound) :
    partialGuessingAllFalsePotential secret program ≤
      ∑ slot : Fin (queryBound + 1),
        partialGuessingSlotMass fallback queryBound slot secret program := by
  induction program using ProbOracleComp.induction generalizing queryBound with
  | pure output =>
      rw [partialGuessingAllFalsePotential_pure]
      calc
        (if output = secret then 1 else 0) =
            partialGuessingSlotMass fallback queryBound queryBound secret
              (pure output : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) := by
          rw [partialGuessingSlotMass_pure_final]
        _ ≤ ∑ slot : Fin (queryBound + 1),
              partialGuessingSlotMass fallback queryBound slot secret
                (pure output : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :=
          Finset.single_le_sum (fun _ _ => zero_le)
            (Finset.mem_univ ⟨queryBound, Nat.lt_succ_self queryBound⟩)
  | sample_bind n cont ih =>
      obtain ⟨_, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp hbound
      rw [partialGuessingAllFalsePotential_sample_bind]
      calc
        (∑' answer, ProbComp.unifOracle n answer *
            partialGuessingAllFalsePotential secret (cont answer)) ≤
            ∑' answer, ProbComp.unifOracle n answer *
              (∑ slot : Fin (queryBound + 1),
                partialGuessingSlotMass fallback queryBound slot secret (cont answer)) :=
          tsum_le_tsum fun answer => mul_le_mul_left'
            (ih answer queryBound (by simpa using hcont answer)) _
        _ = ∑' answer, ∑' slot : Fin (queryBound + 1),
              ProbComp.unifOracle n answer *
                partialGuessingSlotMass fallback queryBound slot secret (cont answer) := by
          congr 1 with answer
          rw [tsum_fintype, Finset.mul_sum]
        _ = ∑' slot : Fin (queryBound + 1), ∑' answer,
              ProbComp.unifOracle n answer *
                partialGuessingSlotMass fallback queryBound slot secret (cont answer) :=
          tsum_comm
        _ = ∑ slot : Fin (queryBound + 1),
              partialGuessingSlotMass fallback queryBound slot secret
                (ProbOracleComp.sample (ProbComp.unifFin n) >>= cont) := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro slot _
          rw [partialGuessingSlotMass_sample_bind]
  | query_bind candidate cont ih =>
      obtain ⟨hpositive, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp hbound
      obtain ⟨queryBound, rfl⟩ : ∃ previous, queryBound = previous + 1 :=
        ⟨queryBound - 1, by simp only [Sum.elim_inr] at hpositive; omega⟩
      rw [partialGuessingAllFalsePotential_query_bind, Fin.sum_univ_succ,
        partialGuessingSlotMass_query_zero]
      apply add_le_add_left
      calc
        partialGuessingAllFalsePotential secret (cont false) ≤
            ∑ slot : Fin (queryBound + 1),
              partialGuessingSlotMass fallback queryBound slot secret (cont false) :=
          ih false queryBound (by
            simpa only [Sum.elim_inr, Nat.add_sub_cancel] using hcont false)
        _ = ∑ slot : Fin (queryBound + 1),
              partialGuessingSlotMass fallback (queryBound + 1) slot.succ secret
                (ProbOracleComp.query candidate >>= cont) := by
          apply Finset.sum_congr rfl
          intro slot _
          rw [partialGuessingSlotMass_query_succ fallback secret candidate queryBound slot
            (Nat.le_of_lt_succ slot.isLt) cont]

/-- One deterministic slot of the PGOW-to-PDOW reduction. It runs the adversary once, answers
all validation calls locally with false, and returns either the selected call or final output. -/
def partialGuessingToDomainAt {Index Image Prefix : Type} (fallback : Prefix)
    (queryBound slot : Nat) (adversary : PartialGuessingAdversary Index Image Prefix) :
    PartialDomainAdversary Index Image Prefix := fun index image =>
  partialGuessingAt fallback queryBound slot (adversary index image)

/-- Lemma C.1's semantic reduction: choose exactly one of the `queryBound` validation positions
or the final output, uniformly. `ProbComp.uniform` specifies the exact finite distribution but is
not claimed to have a strict fair-coin clock for arbitrary `queryBound + 1`. -/
noncomputable def partialGuessingToDomain {Index Image Prefix : Type} (fallback : Prefix)
    (queryBound : Nat) (adversary : PartialGuessingAdversary Index Image Prefix) :
    PartialDomainAdversary Index Image Prefix := fun index image => do
  let slot ← ProbComp.uniform (Fin (queryBound + 1))
  partialGuessingToDomainAt fallback queryBound slot adversary index image

private theorem eval_partialGuessingToDomain_apply {Index Image Prefix : Type}
    (fallback secret : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix) (index : Index) (image : Image) :
    ProbComp.eval (partialGuessingToDomain fallback queryBound adversary index image) secret =
      (∑ slot : Fin (queryBound + 1),
        partialGuessingSlotMass fallback queryBound slot secret (adversary index image)) /
        (queryBound + 1 : ℝ≥0∞) := by
  simp only [partialGuessingToDomain, partialGuessingToDomainAt, ProbComp.eval_bind,
    PMF.bind_apply, eval_partialGuessingAt]
  change ProbComp.expect (ProbComp.uniform (Fin (queryBound + 1)))
      (fun slot => partialGuessingSlotMass fallback queryBound slot secret
        (adversary index image)) = _
  rw [ProbComp.expect_uniform]

/-- **Exact bounded-slot reduction, pointwise form.** If one global budget bounds every public
challenge supplied to the PGOW adversary, its real success mass on each challenge is at most
`queryBound + 1` times the success mass of the paper's exactly uniform semantic reduction. This
combines the adaptive first-divergence coupling with the executable query/final-slot sum. -/
theorem eval_run_partialGuessingReply_apply_le_mul_eval_toDomain
    {Index Image Prefix : Type} [DecidableEq Prefix]
    (fallback secret : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix)
    (hbound : adversary.IsQueryBounded queryBound) (index : Index) (image : Image) :
    ProbComp.eval ((adversary index image).run fun candidate =>
        pure (partialGuessingReply secret candidate)) secret ≤
      (queryBound + 1 : ℝ≥0∞) *
        ProbComp.eval (partialGuessingToDomain fallback queryBound adversary index image) secret := by
  calc
    ProbComp.eval ((adversary index image).run fun candidate =>
        pure (partialGuessingReply secret candidate)) secret ≤
        partialGuessingAllFalsePotential secret (adversary index image) :=
      eval_run_partialGuessingReply_apply_le_allFalsePotential secret (adversary index image)
    _ ≤ ∑ slot : Fin (queryBound + 1),
          partialGuessingSlotMass fallback queryBound slot secret (adversary index image) :=
      partialGuessingAllFalsePotential_le_sum_slotMass fallback secret queryBound
        (adversary index image) (hbound index image)
    _ = (queryBound + 1 : ℝ≥0∞) *
          ProbComp.eval (partialGuessingToDomain fallback queryBound adversary index image) secret := by
      have hne : (queryBound + 1 : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero queryBound
      rw [eval_partialGuessingToDomain_apply, mul_div_cancel₀ _ hne]

private theorem eval_partialGuessingExperiment_true {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix) (adversary : PartialGuessingAdversary Index Image Prefix) :
    ProbComp.eval (partialGuessingExperiment sample part adversary) true =
      ∑' challenge, ProbComp.eval sample challenge *
        ProbComp.eval ((adversary challenge.index challenge.image).run fun candidate =>
          pure (partialGuessingReply (part challenge.secret) candidate))
            (part challenge.secret) := by
  simp only [partialGuessingExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    partialGuessingReply]
  rw [PMF.bind_apply]
  congr 1 with challenge
  rw [PMF.bind_pure_decide_eq_apply_true']

private theorem eval_partialDomainExperiment_true {Index Domain Image Prefix : Type}
    [DecidableEq Prefix] (sample : ProbComp (PartialOneWayChallenge Index Domain Image))
    (part : Domain → Prefix) (adversary : PartialDomainAdversary Index Image Prefix) :
    ProbComp.eval (partialDomainExperiment sample part adversary) true =
      ∑' challenge, ProbComp.eval sample challenge *
        ProbComp.eval (adversary challenge.index challenge.image) (part challenge.secret) := by
  simp only [partialDomainExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    partialGuessingReply]
  rw [PMF.bind_apply]
  congr 1 with challenge
  rw [PMF.bind_pure_decide_eq_apply_true']

/-- **Classical PGOW-to-PDOW reduction** ([KosugeXagawa2026, Appendix C, Lemma C.1,
pp. 33--34]). A PGOW adversary making at most `queryBound` validation calls is bounded by
`queryBound + 1` times the PDOW success of the exact-uniform all-false reduction. The hypothesis is
global over public indices and images, as required for the same slot set to cover every supported
challenge. -/
theorem partialGuessingAdvantage_le_mul_partialDomainAdvantage
    {Index Domain Image Prefix : Type} [DecidableEq Prefix]
    (sample : ProbComp (PartialOneWayChallenge Index Domain Image)) (part : Domain → Prefix)
    (fallback : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix)
    (hbound : adversary.IsQueryBounded queryBound) :
    partialGuessingAdvantage sample part adversary ≤
      (queryBound + 1 : ℝ≥0) *
        partialDomainAdvantage sample part
          (partialGuessingToDomain fallback queryBound adversary) := by
  have htotal :
      ProbComp.eval (partialGuessingExperiment sample part adversary) true ≤
        (queryBound + 1 : ℝ≥0∞) *
          ProbComp.eval (partialDomainExperiment sample part
            (partialGuessingToDomain fallback queryBound adversary)) true := by
    rw [eval_partialGuessingExperiment_true, eval_partialDomainExperiment_true]
    calc
      (∑' challenge, ProbComp.eval sample challenge *
          ProbComp.eval ((adversary challenge.index challenge.image).run fun candidate =>
            pure (partialGuessingReply (part challenge.secret) candidate))
              (part challenge.secret)) ≤
          ∑' challenge, ProbComp.eval sample challenge *
            ((queryBound + 1 : ℝ≥0∞) *
              ProbComp.eval
                (partialGuessingToDomain fallback queryBound adversary
                  challenge.index challenge.image) (part challenge.secret)) :=
        tsum_le_tsum fun challenge => mul_le_mul_left'
          (eval_run_partialGuessingReply_apply_le_mul_eval_toDomain fallback
            (part challenge.secret) queryBound adversary hbound challenge.index challenge.image) _
      _ = (queryBound + 1 : ℝ≥0∞) *
          ∑' challenge, ProbComp.eval sample challenge *
            ProbComp.eval
              (partialGuessingToDomain fallback queryBound adversary
                challenge.index challenge.image) (part challenge.secret) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1 with challenge
        ac_rfl
  simpa only [partialGuessingAdvantage, partialDomainAdvantage, Game.succProbability,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _)) htotal

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

private noncomputable def partialGuessingDyadicTrialMass {Prefix : Type}
    [DecidableEq Prefix] (fallback secret : Prefix) (queryBound slot : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) : ℝ≥0∞ :=
  if slot ≤ queryBound then
    partialGuessingSlotMass fallback queryBound slot secret program
  else if fallback = secret then 1 else 0

private theorem eval_partialGuessingToDomainDyadic_apply {Index Image Prefix : Type}
    [DecidableEq Prefix] (fallback secret : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix) (index : Index) (image : Image) :
    ProbComp.eval (partialGuessingToDomainDyadic fallback queryBound adversary index image) secret =
      (∑ slot : Fin (Probability.dyadicSize queryBound),
        partialGuessingDyadicTrialMass fallback secret queryBound slot
          (adversary index image)) /
        (Probability.dyadicSize queryBound : ℝ≥0∞) := by
  simp only [partialGuessingToDomainDyadic, ProbComp.eval_bind,
    ProbComp.eval_sampleDyadicIndex, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_apply]
  have htrial (slot : Fin (Probability.dyadicSize queryBound)) :
      (if slot.val ≤ queryBound then
          ProbComp.eval (partialGuessingToDomainAt fallback queryBound slot.val adversary
            index image)
        else PMF.pure fallback) secret =
        partialGuessingDyadicTrialMass fallback secret queryBound slot.val
          (adversary index image) := by
    by_cases hslot : slot.val ≤ queryBound
    · simp only [hslot, if_true, partialGuessingDyadicTrialMass,
        partialGuessingToDomainAt, eval_partialGuessingAt]
    · simp only [hslot, if_false, partialGuessingDyadicTrialMass, PMF.pure_apply]
  simp_rw [htrial]
  rw [← ProbComp.eval_uniform]
  change ProbComp.expect (ProbComp.uniform (Fin (Probability.dyadicSize queryBound)))
      (fun slot => partialGuessingDyadicTrialMass fallback secret queryBound slot
        (adversary index image)) = _
  rw [ProbComp.expect_uniform]

private theorem sum_slotMass_le_sum_dyadicTrialMass {Prefix : Type}
    [DecidableEq Prefix] (fallback secret : Prefix) (queryBound : Nat)
    (program : ProbOracleComp (PartialGuessingResponse Prefix) Prefix) :
    (∑ slot : Fin (queryBound + 1),
        partialGuessingSlotMass fallback queryBound slot secret program) ≤
      ∑ slot : Fin (Probability.dyadicSize queryBound),
        partialGuessingDyadicTrialMass fallback secret queryBound slot program := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  have hsource :
      (∑ slot ∈ Finset.range (queryBound + 1),
          partialGuessingSlotMass fallback queryBound slot secret program) =
        ∑ slot ∈ Finset.range (queryBound + 1),
          partialGuessingDyadicTrialMass fallback secret queryBound slot program := by
    apply Finset.sum_congr rfl
    intro slot hslot
    simp only [partialGuessingDyadicTrialMass,
      (Nat.le_of_lt_succ (Finset.mem_range.mp hslot)), if_true]
  rw [hsource]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_of_lt (Probability.lt_dyadicSize queryBound)))
    (fun _ _ _ => zero_le)

/-- **Fixed-clock bounded-slot reduction, pointwise form.** The strict fair-coin sampler loses
exactly `dyadicSize queryBound`; padding slots return the declared fallback and can only add
success mass. -/
theorem eval_run_partialGuessingReply_apply_le_dyadicSize_mul_eval_toDomainDyadic
    {Index Image Prefix : Type} [DecidableEq Prefix]
    (fallback secret : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix)
    (hbound : adversary.IsQueryBounded queryBound) (index : Index) (image : Image) :
    ProbComp.eval ((adversary index image).run fun candidate =>
        pure (partialGuessingReply secret candidate)) secret ≤
      (Probability.dyadicSize queryBound : ℝ≥0∞) *
        ProbComp.eval
          (partialGuessingToDomainDyadic fallback queryBound adversary index image) secret := by
  calc
    ProbComp.eval ((adversary index image).run fun candidate =>
        pure (partialGuessingReply secret candidate)) secret ≤
        partialGuessingAllFalsePotential secret (adversary index image) :=
      eval_run_partialGuessingReply_apply_le_allFalsePotential secret (adversary index image)
    _ ≤ ∑ slot : Fin (queryBound + 1),
          partialGuessingSlotMass fallback queryBound slot secret (adversary index image) :=
      partialGuessingAllFalsePotential_le_sum_slotMass fallback secret queryBound
        (adversary index image) (hbound index image)
    _ ≤ ∑ slot : Fin (Probability.dyadicSize queryBound),
          partialGuessingDyadicTrialMass fallback secret queryBound slot
            (adversary index image) :=
      sum_slotMass_le_sum_dyadicTrialMass fallback secret queryBound (adversary index image)
    _ = (Probability.dyadicSize queryBound : ℝ≥0∞) *
          ProbComp.eval
            (partialGuessingToDomainDyadic fallback queryBound adversary index image) secret := by
      have hne : (Probability.dyadicSize queryBound : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Probability.dyadicSize_pos queryBound).ne'
      rw [eval_partialGuessingToDomainDyadic_apply, mul_div_cancel₀ _ hne]

/-- Concrete fixed-clock advantage bound with the exact dyadic loss. -/
theorem partialGuessingAdvantage_le_dyadicSize_mul_partialDomainAdvantage
    {Index Domain Image Prefix : Type} [DecidableEq Prefix]
    (sample : ProbComp (PartialOneWayChallenge Index Domain Image)) (part : Domain → Prefix)
    (fallback : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix)
    (hbound : adversary.IsQueryBounded queryBound) :
    partialGuessingAdvantage sample part adversary ≤
      (Probability.dyadicSize queryBound : ℝ≥0) *
        partialDomainAdvantage sample part
          (partialGuessingToDomainDyadic fallback queryBound adversary) := by
  have htotal :
      ProbComp.eval (partialGuessingExperiment sample part adversary) true ≤
        (Probability.dyadicSize queryBound : ℝ≥0∞) *
          ProbComp.eval (partialDomainExperiment sample part
            (partialGuessingToDomainDyadic fallback queryBound adversary)) true := by
    rw [eval_partialGuessingExperiment_true, eval_partialDomainExperiment_true]
    calc
      (∑' challenge, ProbComp.eval sample challenge *
          ProbComp.eval ((adversary challenge.index challenge.image).run fun candidate =>
            pure (partialGuessingReply (part challenge.secret) candidate))
              (part challenge.secret)) ≤
          ∑' challenge, ProbComp.eval sample challenge *
            ((Probability.dyadicSize queryBound : ℝ≥0∞) *
              ProbComp.eval
                (partialGuessingToDomainDyadic fallback queryBound adversary
                  challenge.index challenge.image) (part challenge.secret)) :=
        tsum_le_tsum fun challenge => mul_le_mul_left'
          (eval_run_partialGuessingReply_apply_le_dyadicSize_mul_eval_toDomainDyadic fallback
            (part challenge.secret) queryBound adversary hbound challenge.index challenge.image) _
      _ = (Probability.dyadicSize queryBound : ℝ≥0∞) *
          ∑' challenge, ProbComp.eval sample challenge *
            ProbComp.eval
              (partialGuessingToDomainDyadic fallback queryBound adversary
                challenge.index challenge.image) (part challenge.secret) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1 with challenge
        ac_rfl
  simpa only [partialGuessingAdvantage, partialDomainAdvantage, Game.succProbability,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _)) htotal

/-- The fixed-clock loss is at most twice the paper's exact `queryBound + 1` factor. -/
theorem partialGuessingAdvantage_le_two_mul_partialDomainAdvantage
    {Index Domain Image Prefix : Type} [DecidableEq Prefix]
    (sample : ProbComp (PartialOneWayChallenge Index Domain Image)) (part : Domain → Prefix)
    (fallback : Prefix) (queryBound : Nat)
    (adversary : PartialGuessingAdversary Index Image Prefix)
    (hbound : adversary.IsQueryBounded queryBound) :
    partialGuessingAdvantage sample part adversary ≤
      (2 * (queryBound + 1) : ℝ≥0) *
        partialDomainAdvantage sample part
          (partialGuessingToDomainDyadic fallback queryBound adversary) :=
  (partialGuessingAdvantage_le_dyadicSize_mul_partialDomainAdvantage sample part fallback
    queryBound adversary hbound).trans <| by
      gcongr
      exact_mod_cast Probability.dyadicSize_le queryBound

end Cslib.Crypto
