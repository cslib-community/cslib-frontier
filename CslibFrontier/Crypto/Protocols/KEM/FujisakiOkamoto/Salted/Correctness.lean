/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
public import CslibFrontier.Probability.StatisticalDistance.CloseTo

/-!
# Correctness hop for salted joint-oracle FO transforms

This module isolates the `CORR` hop in the classical-ROM decapsulation simulation for an
implicit-rejection salted Fujisaki--Okamoto transform. A direct query receives the session key and
encryption coins in one `JointReply`; it therefore costs one `joint` query, not one query per
projection. The rejection oracle is a separate channel and does not create a PKE correctness
witness. Decapsulation is punctured at the challenge ciphertext and has its own cost.

The protocol-specific real and simulated handlers remain parameters. They must prove that they
are identical until their `CORR` predicate and that a good-state transition becomes bad with
probability at most one fixed-key decryption-error term for each joint-oracle or decapsulation
query. `closeTo_run_corr` then gives the exact fixed-key loss `(qRO + qD) * ε`.
`advantage_keyedGame_corr_le` averages this result over PKE key generation using
`ExplicitCoinPKE.DeltaCorrect δ`, giving `(qRO + qD) * δ` without a challenge `+1` term.

This is the single-user, single-challenge specialization of the `CORR` step in Theorem 11 and
Figure 11 of [GlabushHoevelmannsStebila2025]. In HQC v5.1, Section 6.2.2, Theorem 6.4, the source
coin and key oracles are fused as `G(H(ekKEM) || m || salt) = (K, θ)`, so their direct-query
contribution is counted once. The full passive salted-FO lift, its message-guessing and collision
terms, and the HQC instantiation are outside this module.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointInput`: public prefix, message and salt of a
  joint random-oracle query.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointReply`: named key and encryption-coin
  projections of one joint reply.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Query`: joint-oracle, rejection-oracle and
  punctured-decapsulation queries.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.QueryBounds`: separate `qRO` and `qD` bounds.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.keyedGame`: average a fixed-key handler game over
  the PKE key generator.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.closeTo_run_corr`: exact fixed-key
  `(qRO + qD) * ε` all-events bound.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.advantage_keyedGame_corr_le`: exact
  `(qRO + qD) * δ` two-world advantage bound under `ExplicitCoinPKE.DeltaCorrect δ`.

## References

* [L. Glabush, K. Hövelmanns, D. Stebila, *Tight Multi-challenge Security Reductions for Key
  Encapsulation Mechanisms*][GlabushHoevelmannsStebila2025], Theorem 11 and Figure 11.
* *Hamming Quasi-Cyclic (HQC), version 5.1*, Section 6.2.2, Definition 6.2.1 and Theorem 6.4.
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open scoped ENNReal NNReal

/-- Input of the salted joint random oracle: a public-key prefix, message and salt. HQC uses
`H(ekKEM)` as the prefix. -/
structure JointInput (Prefix M Salt : Type) where
  /-- Public prefix selecting the target encapsulation key. -/
  prefix : Prefix
  /-- PKE plaintext whose encryption coins are derived by the oracle. -/
  message : M
  /-- Public salt carried by the KEM ciphertext. -/
  salt : Salt

/-- One reply of the joint random oracle. Named projections prevent silently swapping the source
orders `(key, coins)` and `(coins, key)`. -/
structure JointReply (K R : Type) where
  /-- Session key derived by the joint oracle. -/
  key : K
  /-- Explicit PKE encryption coins derived by the same oracle call. -/
  coins : R

/-- Ciphertext of the salted transform: an underlying PKE ciphertext and its public salt. -/
structure Ciphertext (CT Salt : Type) where
  /-- Underlying PKE ciphertext. -/
  pke : CT
  /-- Salt used by the joint-oracle input. -/
  salt : Salt

/-- Oracle queries of the salted implicit-rejection CCA experiment. `joint` returns both the KEM
key and encryption coins in one response. `rejection` is the separate `J` channel. `decaps` is
punctured at the challenge by `Query.dispatch`. -/
inductive Query (Prefix M Salt JInput CT : Type) where
  /-- One query to the fused key-and-coin random oracle. -/
  | joint (input : JointInput Prefix M Salt)
  /-- One query to the separate implicit-rejection oracle `J`. -/
  | rejection (input : JInput)
  /-- One query to the decapsulation oracle. -/
  | decaps (ciphertext : Ciphertext CT Salt)

/-- Response family for `Query`. -/
abbrev Response {Prefix M Salt JInput CT : Type} (K R : Type) :
    Query Prefix M Salt JInput CT → Type
  | .joint _ => JointReply K R
  | .rejection _ => K
  | .decaps _ => Option K

namespace Query

variable {Prefix M Salt JInput CT K R : Type}

/-- Dispatch a salted-FO query. A decapsulation query equal to the challenge is rejected before
the supplied decapsulation handler runs. The rejection oracle is kept separate from the joint
oracle, matching HQC's `J` fallback. -/
@[simp] def dispatch [DecidableEq (Ciphertext CT Salt)] {m : Type → Type} [Monad m]
    (joint : JointInput Prefix M Salt → m (JointReply K R)) (rejection : JInput → m K)
    (decaps : Ciphertext CT Salt → m (Option K)) (challenge : Ciphertext CT Salt) :
    (q : Query Prefix M Salt JInput CT) → m (Response K R q)
  | .joint input => joint input
  | .rejection input => rejection input
  | .decaps ciphertext => if ciphertext = challenge then pure none else decaps ciphertext

/-- Cost counting direct joint-oracle queries. One response containing both `key` and `coins`
costs exactly one. -/
@[simp] def jointCost : Query Prefix M Salt JInput CT → ℕ
  | .joint _ => 1
  | .rejection _ => 0
  | .decaps _ => 0

/-- Cost counting decapsulation queries. -/
@[simp] def decapsCost : Query Prefix M Salt JInput CT → ℕ
  | .joint _ => 0
  | .rejection _ => 0
  | .decaps _ => 1

end Query

/-- Separate source-shaped query bounds: at most `qRO` calls to the joint oracle and at most `qD`
calls to decapsulation. Rejection-oracle calls do not enter the `CORR` loss. -/
def QueryBounds {Prefix M Salt JInput CT K R α : Type}
    (program : OracleComp (Response (Prefix := Prefix) (M := M) (Salt := Salt)
      (JInput := JInput) (CT := CT) K R) α) (qRO qD : ℕ) : Prop :=
  OracleComp.IsCostBounded Query.jointCost program qRO ∧
    OracleComp.IsCostBounded Query.decapsCost program qD

/-- **Fixed-key salted-FO `CORR` hop.** Suppose the real and simulated handlers agree until
`bad`, and from any good state each joint-oracle or decapsulation query creates `bad` with
probability at most `ε`. A program bounded by `qRO` joint queries and `qD` decapsulation queries
then has output laws within `(qRO + qD) * ε`, after any shared randomized postprocessing.

The cost of `Query.rejection` is zero in both channels, so a shared `J` fallback contributes no
correctness term. `Query.joint` has cost one even though its reply has two projections. -/
theorem closeTo_run_corr {Prefix M Salt JInput CT K R State α β : Type}
    {first second : (q : Query Prefix M Salt JInput CT) →
      StateT State PMF (Response K R q)} {bad : State → Prop} {ε : ℝ≥0∞}
    (hident : OracleComp.IdenticalUntilBad first second bad)
    (hstep : ∀ q s, ¬bad s →
      (first q s).toOuterMeasure {x | bad x.2} ≤
        (Query.jointCost q : ℝ≥0∞) * ε + (Query.decapsCost q : ℝ≥0∞) * ε)
    (program : OracleComp (Response (Prefix := Prefix) (M := M) (Salt := Salt)
      (JInput := JInput) (CT := CT) K R) α) {qRO qD : ℕ}
    (hbounds : QueryBounds program qRO qD) {initial : State} (hinitial : ¬bad initial)
    (next : α × State → PMF β) :
    CloseTo (((OracleComp.interpret first program).run initial).bind next)
      (((OracleComp.interpret second program).run initial).bind next)
      (((qRO + qD : ℕ) : ℝ≥0∞) * ε) := by
  have hreach :
      ((OracleComp.interpret first program).run initial).toOuterMeasure {x | bad x.2} ≤
        (qRO : ℝ≥0∞) * ε + (qD : ℝ≥0∞) * ε := by
    simpa only [mul_zero, add_zero] using
      (OracleComp.toOuterMeasure_bad_le_two Query.jointCost Query.decapsCost (fun _ => ε)
        0 0 ε hstep (fun _ _ _ _ _ _ => by simp) hbounds.1 hbounds.2 hinitial)
  refine (hident.closeTo_bind program initial next).mono (hreach.trans_eq ?_)
  rw [← add_mul, ← Nat.cast_add]

/-- Average a fixed-key stateful oracle game over the key generator of an explicit-coin PKE. The
simulated handler may ignore its `sk` argument; retaining the common parameter lets the generic
`IdenticalUntilBad` proof compare both handlers on one state space. -/
noncomputable def keyedGame {PK SK M R CT Prefix Salt JInput K State α : Type}
    (P : ExplicitCoinPKE PK SK M R CT)
    (handler : PK → SK → (q : Query Prefix M Salt JInput CT) →
      StateT State PMF (Response K R q))
    (program : PK → SK → OracleComp (Response (Prefix := Prefix) (M := M) (Salt := Salt)
      (JInput := JInput) (CT := CT) K R) α)
    (initial : PK → SK → State) (next : PK → SK → α × State → PMF Bool) : PMF Bool :=
  (ProbComp.eval P.keyGen).bind fun keys =>
    ((OracleComp.interpret (handler keys.1 keys.2) (program keys.1 keys.2)).run
      (initial keys.1 keys.2)).bind (next keys.1 keys.2)

/-- **Key-averaged salted-FO `CORR` hop.** If the fixed-key real/simulated handlers satisfy
`closeTo_run_corr` with error equal to the worst-message decryption-failure probability of their
key pair, `ExplicitCoinPKE.DeltaCorrect δ` yields the exact two-world advantage loss
`(qRO + qD) * δ`.

There is no challenge `+1`: challenge construction is not one of the handler queries in this hop,
and `Query.dispatch` rejects decapsulation of the challenge before the handler is invoked. -/
theorem advantage_keyedGame_corr_le [Fintype M] [Nonempty M]
    {PK SK M R CT Prefix Salt JInput K State α : Type}
    (P : ExplicitCoinPKE PK SK M R CT)
    (first second : PK → SK → (q : Query Prefix M Salt JInput CT) →
      StateT State PMF (Response K R q))
    (bad : PK → SK → State → Prop)
    (hident : ∀ pk sk, OracleComp.IdenticalUntilBad (first pk sk) (second pk sk) (bad pk sk))
    (hstep : ∀ pk sk q s, ¬bad pk sk s →
      (first pk sk q s).toOuterMeasure {x | bad pk sk x.2} ≤
        (Query.jointCost q : ℝ≥0∞) * ENNReal.ofReal (P.keyPairMaxFailProb pk sk) +
          (Query.decapsCost q : ℝ≥0∞) * ENNReal.ofReal (P.keyPairMaxFailProb pk sk))
    (program : PK → SK → OracleComp (Response (Prefix := Prefix) (M := M) (Salt := Salt)
      (JInput := JInput) (CT := CT) K R) α)
    {qRO qD : ℕ} (hbounds : ∀ pk sk, QueryBounds (program pk sk) qRO qD)
    (initial : PK → SK → State) (hinitial : ∀ pk sk, ¬bad pk sk (initial pk sk))
    (next : PK → SK → α × State → PMF Bool) {δ : ℝ} (hδ : P.DeltaCorrect δ) :
    (Game.advantage (keyedGame P first program initial next)
        (keyedGame P second program initial next) : ℝ) ≤
      ((qRO + qD : ℕ) : ℝ) * δ := by
  set E : ℝ≥0∞ := P.keyGen.expect fun keys =>
    ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2) with hE
  have hclose : CloseTo (keyedGame P first program initial next)
      (keyedGame P second program initial next) (((qRO + qD : ℕ) : ℝ≥0∞) * E) := by
    unfold keyedGame
    refine (CloseTo.bind_right_tsum _ (err := fun keys : PK × SK =>
      ((qRO + qD : ℕ) : ℝ≥0∞) * ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2))
      fun keys _ => ?_).mono (le_of_eq ?_)
    · exact closeTo_run_corr (hident keys.1 keys.2) (hstep keys.1 keys.2)
        (program keys.1 keys.2) (hbounds keys.1 keys.2) (hinitial keys.1 keys.2)
        (next keys.1 keys.2)
    · rw [hE, ProbComp.expect, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun keys => ?_
      ring
  have hadv := Game.closeTo_iff_coe_advantage_le.mp hclose
  have hEtop : E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hE, ProbComp.expect]
    calc ∑' keys, ProbComp.eval P.keyGen keys *
          ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2)
        ≤ ∑' keys, ProbComp.eval P.keyGen keys * 1 := by
          gcongr with keys
          exact ENNReal.ofReal_le_one.mpr (P.keyPairMaxFailProb_le_one keys.1 keys.2)
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc (Game.advantage (keyedGame P first program initial next)
        (keyedGame P second program initial next) : ℝ)
      = ((Game.advantage (keyedGame P first program initial next)
          (keyedGame P second program initial next) : ℝ≥0∞)).toReal := by
            rw [ENNReal.coe_toReal]
    _ ≤ (((qRO + qD : ℕ) : ℝ≥0∞) * E).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hEtop) hadv
    _ = ((qRO + qD : ℕ) : ℝ) * E.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ ≤ ((qRO + qD : ℕ) : ℝ) * δ :=
      mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
