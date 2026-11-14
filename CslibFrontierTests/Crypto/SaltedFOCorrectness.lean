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
coin for every message, so its exact correctness error is `1 / 2` rather than a vacuous endpoint.
-/

namespace CslibFrontierTests.SaltedFOCorrectness

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open scoped ENNReal

abbrev ToyQuery := Query Unit Unit Unit Unit Unit Unit
abbrev ToyResponse := Response (JointPrefix := Unit) (M := Unit) (Salt := Unit)
  (RejectPrefix := Unit) (Sigma := Unit) (CT := Unit) Bool Unit

def jointInput : JointInput Unit Unit Unit := ⟨(), (), ()⟩

def ciphertext : Ciphertext Unit Unit := ⟨(), ()⟩

def rejectionInput : RejectionInput Unit Unit Unit Unit := ⟨(), (), ciphertext⟩

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
    Scheme Unit Unit Bool Bool Bool Unit Bool Unit Unit Bool where
  pke := halfErrorPKE
  sampleKey := ProbComp.uniform Bool
  jointPrefix _ := ()
  rejectionPrefix _ := ()
  rejectionSecret _ := ()

/-- Synthetic identical-until-bad handler whose one joint query exposes the direct-query witness.
The Boolean argument is the answer key; the joint transition latches `CORR`. -/
def directHandler (answer : Bool) (q : ToyQuery) : StateT Bool PMF (ToyResponse q) :=
  fun bad => match q with
    | .joint _ => PMF.pure (⟨answer, ()⟩, true)
    | .rejection _ => PMF.pure (false, bad)
    | .decaps _ => PMF.pure (none, bad)

/-- Synthetic handler whose one decapsulation query exposes the decapsulation-only witness. -/
def decapsHandler (answer : Bool) (q : ToyQuery) : StateT Bool PMF (ToyResponse q) :=
  fun bad => match q with
    | .joint _ => PMF.pure (⟨false, ()⟩, bad)
    | .rejection _ => PMF.pure (false, bad)
    | .decaps _ => PMF.pure (some answer, true)

theorem identicalUntilBad_direct :
    OracleComp.IdenticalUntilBad (directHandler false) (directHandler true) (· = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q s hs answer s' hs'
    cases q <;> simp [directHandler, hs']
  · intro q s hs x hx
    subst s
    cases q <;> simp only [directHandler, PMF.mem_support_pure_iff] at hx <;> subst x <;> rfl
  · intro q s hs x hx
    subst s
    cases q <;> simp only [directHandler, PMF.mem_support_pure_iff] at hx <;> subst x <;> rfl

theorem identicalUntilBad_decaps :
    OracleComp.IdenticalUntilBad (decapsHandler false) (decapsHandler true) (· = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q s hs answer s' hs'
    cases q <;> simp [decapsHandler, hs']
  · intro q s hs x hx
    subst s
    cases q <;> simp only [decapsHandler, PMF.mem_support_pure_iff] at hx <;> subst x <;> rfl
  · intro q s hs x hx
    subst s
    cases q <;> simp only [decapsHandler, PMF.mem_support_pure_iff] at hx <;> subst x <;> rfl

def directProgram : OracleComp ToyResponse Bool := do
  let reply ← OracleComp.query (Query.joint jointInput)
  return reply.key

def decapsProgram : OracleComp ToyResponse Bool := do
  let reply ← OracleComp.query (Query.decaps ciphertext)
  return reply.getD false

/-- The two projections in the direct reply still cost exactly one joint-oracle query. -/
theorem directProgram_bounds : QueryBounds directProgram 1 0 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.joint jointInput)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- The decapsulation-only witness has `qRO = 0` and `qD = 1`. -/
theorem decapsProgram_bounds : QueryBounds decapsProgram 0 1 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.decaps ciphertext)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- Direct-query regression: the exact fixed-key coefficient specializes to `(1 + 0) * 1`. -/
theorem direct_closeTo :
    CloseTo
      (((OracleComp.interpret (directHandler false) directProgram).run false).map Prod.fst)
      (((OracleComp.interpret (directHandler true) directProgram).run false).map Prod.fst)
      (((1 + 0 : ℕ) : ℝ≥0∞) * 1) := by
  have hstep : ∀ q s, s ≠ true →
      (directHandler false q s).toOuterMeasure {x | x.2 = true} ≤
        (Query.jointCost q : ℝ≥0∞) * 1 + (Query.decapsCost q : ℝ≥0∞) * 1 := by
    intro q s hs
    cases q <;> simp [directHandler, hs]
  simpa only [PMF.bind_pure_comp, PMF.map_id] using
    (closeTo_run_corr identicalUntilBad_direct hstep directProgram directProgram_bounds
      (by simp) (fun out => PMF.pure out.1))

/-- Decapsulation-only regression: omitting `qD` would incorrectly give a zero bound here. -/
theorem decaps_closeTo :
    CloseTo
      (((OracleComp.interpret (decapsHandler false) decapsProgram).run false).map Prod.fst)
      (((OracleComp.interpret (decapsHandler true) decapsProgram).run false).map Prod.fst)
      (((0 + 1 : ℕ) : ℝ≥0∞) * 1) := by
  have hstep : ∀ q s, s ≠ true →
      (decapsHandler false q s).toOuterMeasure {x | x.2 = true} ≤
        (Query.jointCost q : ℝ≥0∞) * 1 + (Query.decapsCost q : ℝ≥0∞) * 1 := by
    intro q s hs
    cases q <;> simp [decapsHandler, hs]
  simpa only [PMF.bind_pure_comp, PMF.map_id] using
    (closeTo_run_corr identicalUntilBad_decaps hstep decapsProgram decapsProgram_bounds
      (by simp) (fun out => PMF.pure out.1))

/-- Decapsulation of the challenge is rejected before the supplied handler runs. -/
example :
    Query.dispatch (m := Id) (K := Bool) (R := Unit)
      (fun _ => ⟨false, ()⟩) (fun _ => true) (fun _ => some true) ciphertext
      (Query.decaps ciphertext) = none := by
  simp

/-- The separate rejection fallback is preserved and has zero `CORR` cost. -/
example :
    Query.dispatch (m := Id) (K := Bool) (R := Unit)
      (fun _ => ⟨false, ()⟩) (fun _ => true) (fun _ => some false) ciphertext
      (Query.rejection rejectionInput) = true := rfl

example : Query.jointCost (Query.rejection rejectionInput : ToyQuery) = 0 := rfl

example : Query.decapsCost (Query.rejection rejectionInput : ToyQuery) = 0 := rfl

/-! ### Connected nonzero-error handler clients -/

abbrev HalfQuery := Query Unit Bool Bool Unit Unit Bool
abbrev HalfResponse := Response (JointPrefix := Unit) (M := Bool) (Salt := Bool)
  (RejectPrefix := Unit) (Sigma := Unit) (CT := Bool) Bool Bool
abbrev HalfState := CacheState Unit Bool Bool Unit Unit Bool Bool Bool

def halfJointInput : JointInput Unit Bool Bool := ⟨(), false, false⟩

def halfCiphertext : Ciphertext Bool Bool := ⟨false, false⟩

def halfChallenge : Ciphertext Bool Bool := ⟨true, true⟩

/-- This client consumes both projections of one fused reply. -/
def halfDirectProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.joint halfJointInput)
  return reply.key == reply.coins

/-- The decapsulation-only client exercises the concrete real decrypt/re-encrypt path and the
keyless patched-cache path with no external joint query. -/
def halfDecapsProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.decaps halfCiphertext)
  return reply.getD false

/-- A nontrivial completion client: decapsulation prefetches the decoded joint coordinate in the
proof-only world, then a direct query consumes both the cached key and coin. -/
def halfDecapsThenJointProgram : OracleComp HalfResponse Bool := do
  let decapsReply ← OracleComp.query (Query.decaps halfCiphertext)
  let jointReply ← OracleComp.query (Query.joint halfJointInput)
  return (decapsReply.getD false == jointReply.key) && (jointReply.key == jointReply.coins)

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

/-- `J` remains a distinct source-shaped query and costs nothing in the correctness accounting. -/
example : Query.jointCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

example : Query.decapsCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

end CslibFrontierTests.SaltedFOCorrectness
