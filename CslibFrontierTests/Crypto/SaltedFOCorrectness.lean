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
dropping the `qD` contribution. The underlying explicit-coin PKE always fails decryption and is
therefore `1`-correct in the quantitative sense; this supplies a deliberately nonzero correctness
parameter rather than testing the theorem only at `δ = 0`.
-/

namespace CslibFrontierTests.SaltedFOCorrectness

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open scoped ENNReal

abbrev ToyQuery := Query Unit Unit Unit Unit Unit
abbrev ToyResponse := Response (Prefix := Unit) (M := Unit) (Salt := Unit)
  (JInput := Unit) (CT := Unit) Bool Unit

def jointInput : JointInput Unit Unit Unit := ⟨(), (), ()⟩

def ciphertext : Ciphertext Unit Unit := ⟨(), ()⟩

/-- An explicit-coin PKE whose only honest encryption always fails to decrypt. -/
def failingPKE : ExplicitCoinPKE Unit Unit Unit Unit Unit where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ _ _ := ()
  dec _ _ := none

/-- Every explicit-coin PKE is at most `1`-incorrect; for this fixture the nonzero bound is the
intended one. -/
theorem failingPKE_deltaCorrect_one : failingPKE.DeltaCorrect 1 := by
  have hle : failingPKE.keyGen.expect (fun keys =>
      ENNReal.ofReal (failingPKE.keyPairMaxFailProb keys.1 keys.2)) ≤ 1 := by
    rw [ProbComp.expect]
    calc ∑' keys, ProbComp.eval failingPKE.keyGen keys *
          ENNReal.ofReal (failingPKE.keyPairMaxFailProb keys.1 keys.2)
        ≤ ∑' keys, ProbComp.eval failingPKE.keyGen keys * 1 := by
          gcongr with keys
          exact ENNReal.ofReal_le_one.mpr
            (failingPKE.keyPairMaxFailProb_le_one keys.1 keys.2)
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact ENNReal.toReal_mono ENNReal.one_ne_top hle

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
      (Query.rejection ()) = true := rfl

example : Query.jointCost (Query.rejection () : ToyQuery) = 0 := rfl

example : Query.decapsCost (Query.rejection () : ToyQuery) = 0 := rfl

end CslibFrontierTests.SaltedFOCorrectness
