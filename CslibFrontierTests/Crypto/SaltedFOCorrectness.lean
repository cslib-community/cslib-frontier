/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness

/-!
# Tests for the salted joint-oracle FO correctness hop

The fixtures below keep the direct joint-oracle witness and the decapsulation-only witness
separate. Their exact query bounds detect counting the two projections of a joint reply twice or
dropping the `qD` contribution. The connected explicit-coin PKE has one good and one bad Boolean
coin for every message, so both local bad-event probabilities and its global correctness error are
exactly `1 / 2` rather than vacuous endpoints. Distinct key and coin types make projection order a
type-level regression, and a randomized challenge-aware client checks the public averaged theorem.
-/

namespace CslibFrontierTests.SaltedFOCorrectness

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open scoped ENNReal

/-- Boolean explicit-coin PKE with failure exactly when the sampled coin is `true`. -/
noncomputable def halfErrorPKE : ExplicitCoinPKE Unit Unit Bool Bool Bool where
  keyGen := pure ((), ())
  sampleCoins := ProbComp.uniform Bool
  encDet _ message coins := message ^^ coins
  dec _ ciphertext := some ciphertext

/-- Each message has one failing coin among the two uniform Boolean coins. -/
theorem halfErrorPKE_msgFailProb (message : Bool) :
    halfErrorPKE.msgFailProb () () message = 1 / 2 := by
  cases message <;>
    simp [ExplicitCoinPKE.msgFailProb, halfErrorPKE, PMF.toOuterMeasure_apply,
      Set.indicator, tsum_fintype, PMF.uniformOfFintype_apply, Fintype.card_bool]

theorem halfErrorPKE_keyPairMaxFailProb :
    halfErrorPKE.keyPairMaxFailProb () () = 1 / 2 := by
  rw [ExplicitCoinPKE.keyPairMaxFailProb]
  simp [halfErrorPKE_msgFailProb]

/-- The fixture's expected worst-message failure is exactly `1 / 2`. -/
theorem halfErrorPKE_deltaCorrect_half : halfErrorPKE.DeltaCorrect (1 / 2) := by
  rw [ExplicitCoinPKE.DeltaCorrect, ProbComp.expect]
  simp [halfErrorPKE, halfErrorPKE_keyPairMaxFailProb]

/-- Concrete salted-FO handler fixture backed by `halfErrorPKE`. -/
noncomputable def halfErrorScheme :
    Scheme Unit Unit Bool Bool Bool Unit Bool Unit Unit Unit where
  pke := halfErrorPKE
  sampleKey := pure ()
  jointPrefix _ := ()
  rejectionPrefix _ := ()
  rejectionSecret _ := ()

/-! ### Connected nonzero-error handler clients -/

abbrev HalfQuery := Query Unit Bool Bool Unit Unit Bool
abbrev HalfResponse := Response (JointPrefix := Unit) (M := Bool) (Salt := Bool)
  (RejectPrefix := Unit) (Sigma := Unit) (CT := Bool) Unit Bool
abbrev HalfState := CacheState Unit Bool Bool Unit Unit Bool Unit Bool

def halfJointInput : JointInput Unit Bool Bool := ⟨(), false, false⟩

def halfCiphertext : Ciphertext Bool Bool := ⟨false, false⟩

def halfChallenge : Ciphertext Bool Bool := ⟨true, true⟩

/-- This client consumes both projections of one fused reply. The projections have distinct types,
so reversing the source order is rejected rather than hidden by a symmetric Boolean predicate. -/
def halfDirectProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.joint halfJointInput)
  return (reply.key == ()) && (reply.coins == false)

/-- The decapsulation-only client exercises the concrete real decrypt/re-encrypt path and the
keyless patched-cache path with no external joint query. -/
def halfDecapsProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.decaps halfCiphertext)
  return reply.isSome

/-- A nontrivial completion client: decapsulation prefetches the decoded joint coordinate in the
proof-only world, then a direct query consumes both the cached key and coin. -/
def halfDecapsThenJointProgram : OracleComp HalfResponse Bool := do
  let decapsReply ← OracleComp.query (Query.decaps halfCiphertext)
  let jointReply ← OracleComp.query (Query.joint halfJointInput)
  return (decapsReply == some jointReply.key) && (jointReply.coins == false)

theorem halfDirectProgram_bounds : QueryBounds halfDirectProgram 1 0 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.joint halfJointInput)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem halfDecapsProgram_bounds : QueryBounds halfDecapsProgram 0 1 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.decaps halfCiphertext)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem halfDecapsThenJointProgram_bounds : QueryBounds halfDecapsThenJointProgram 1 1 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.decaps halfCiphertext)).bind fun _ =>
      (OracleComp.IsCostBounded.query (Query.joint halfJointInput)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

/-- Local correctness-bad predicate for the connected fixture. -/
def halfBad (st : HalfState) : Prop := ¬halfErrorScheme.GoodCache () () st

/-- One direct joint query creates the concrete `CORR` witness with probability exactly `1 / 2`.
This is the nonvacuous `(qRO,qD) = (1,0)` execution. -/
theorem halfDirect_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.joint halfJointInput)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = 1 / 2 := by
  simp [Scheme.realHandler, Query.dispatch, Scheme.realJoint, halfErrorScheme, halfErrorPKE,
    halfJointInput, halfChallenge, halfBad, Scheme.GoodCache, Scheme.coinCache,
    ExplicitCoinPKE.GoodCache, PMF.toOuterMeasure_apply, Set.indicator, tsum_fintype,
    PMF.uniformOfFintype_apply, Fintype.card_bool]

/-- One nonchallenge decapsulation performs the implicit joint lookup and creates the same
concrete witness with probability exactly `1 / 2`. This is the nonvacuous `(0,1)` execution. -/
theorem halfDecaps_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.decaps halfCiphertext)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = 1 / 2 := by
  simp [Scheme.realHandler, Query.dispatch, Scheme.realDecaps, Scheme.realJoint,
    Scheme.decapsKey, halfErrorScheme, halfErrorPKE, halfJointInput, halfCiphertext,
    halfChallenge, halfBad, Scheme.GoodCache, Scheme.coinCache, ExplicitCoinPKE.GoodCache,
    PMF.toOuterMeasure_apply, Set.indicator, tsum_fintype, PMF.uniformOfFintype_apply,
    Fintype.card_bool]

/-- Direct-query execution under the real concrete handler. -/
noncomputable def halfDirectReal : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
    halfDirectProgram).run ({} : HalfState)).map Prod.fst

/-- Direct-query execution under the keyless concrete handler. -/
noncomputable def halfDirectSimulated : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
    halfDirectProgram).run ({} : HalfState)).map Prod.fst

/-- Decapsulation-only execution under the real concrete handler. -/
noncomputable def halfDecapsReal : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
    halfDecapsProgram).run ({} : HalfState)).map Prod.fst

/-- Decapsulation-only execution under the keyless concrete handler. -/
noncomputable def halfDecapsSimulated : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
    halfDecapsProgram).run ({} : HalfState)).map Prod.fst

/-- The concrete direct-query hop uses the direct `qRO` coefficient and the fixture's exact
fixed-key error `1 / 2`. -/
theorem halfDirectConcrete_closeTo :
    CloseTo halfDirectReal halfDirectSimulated
      (((1 + 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfDirectReal, halfDirectSimulated, halfErrorScheme,
    halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge halfDirectProgram
      halfDirectProgram_bounds)

/-- The concrete decapsulation-only hop uses the independent `qD` coefficient. -/
theorem halfDecapsConcrete_closeTo :
    CloseTo halfDecapsReal halfDecapsSimulated
      (((0 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfDecapsReal, halfDecapsSimulated, halfErrorScheme,
    halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge halfDecapsProgram
      halfDecapsProgram_bounds)

/-- The decaps-then-joint client checks the completion-valued relation rather than equality of
the private lazy caches. -/
example :
    CloseTo
      (((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
        halfDecapsThenJointProgram).run ({} : HalfState)).map Prod.fst)
      (((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
        halfDecapsThenJointProgram).run ({} : HalfState)).map Prod.fst)
      (((1 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfErrorScheme, halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge
      halfDecapsThenJointProgram halfDecapsThenJointProgram_bounds)

/-- Challenge decapsulation is rejected by the dispatcher before either concrete decapsulation
implementation changes its caches. -/
example (st : HalfState) :
    halfErrorScheme.realHandler () () halfChallenge (Query.decaps halfChallenge) st =
      PMF.pure (none, st) := by
  simp [Scheme.realHandler, Query.dispatch]

def halfRejectionInput : RejectionInput Unit Unit Bool Bool := ⟨(), (), halfCiphertext⟩

/-- The post-secret-seed-guessing `J` query is executed by the concrete handler and cannot
create a local PKE correctness witness. -/
theorem halfRejection_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.rejection halfRejectionInput)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = 0 := by
  simp [Scheme.realHandler, Query.dispatch, Scheme.rejection, halfErrorScheme,
    halfRejectionInput, halfBad, Scheme.GoodCache, Scheme.coinCache,
    ExplicitCoinPKE.GoodCache]

/-- `J` remains a distinct source-shaped query and costs nothing in the correctness accounting. -/
example : Query.jointCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

example : Query.decapsCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

/-! ### Challenge-aware randomized client -/

/-- A genuinely randomized public challenge setup; both games sample this same law. -/
noncomputable def halfChallengeSetup (_ : Unit) :
    ProbComp (Ciphertext Bool Bool × Unit) := do
  let salt ← ProbComp.uniform Bool
  return (⟨true, salt⟩, ())

/-- Fixed-tape program that inspects all three public challenge fields. -/
def halfChallengeProgram (challenge : KEM.Challenge Unit (Ciphertext Bool Bool) Unit) :
    OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query
    (Query.joint (⟨(), false, challenge.ct.salt⟩ : JointInput Unit Bool Bool))
  return (challenge.pk == ()) && (reply.key == challenge.key) &&
    (reply.coins == challenge.ct.salt)

/-- Explicit-coin adversary with a challenge-aware deterministic program on each tape. -/
noncomputable def halfRandomizedAdversary :
    RandomizedAdversary Unit Unit Bool Bool Unit Unit Bool Unit Bool where
  Coins := Unit
  coins := pure ()
  run _ challenge := halfChallengeProgram challenge

theorem halfRandomizedAdversary_bounded : halfRandomizedAdversary.QueryBounded 1 0 := by
  intro _ challenge
  change QueryBounds (halfChallengeProgram challenge) 1 0
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query
      (Query.joint (⟨(), false, challenge.ct.salt⟩ : JointInput Unit Bool Bool))).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

/-- The public randomized theorem accepts a full challenge-aware adversary and a common
randomized challenge setup without charging challenge construction as an oracle query. -/
example :
    (Game.advantage
      (halfErrorScheme.randomizedRealHandlerGame halfChallengeSetup halfRandomizedAdversary)
      (halfErrorScheme.randomizedSimHandlerGame halfChallengeSetup halfRandomizedAdversary) : ℝ) ≤
      ((1 + 0 : ℕ) : ℝ) * (1 / 2 : ℝ) := by
  exact halfErrorScheme.advantage_randomizedRealHandler_simHandler_le
    halfChallengeSetup halfRandomizedAdversary halfRandomizedAdversary_bounded
    halfErrorPKE_deltaCorrect_half

end CslibFrontierTests.SaltedFOCorrectness
