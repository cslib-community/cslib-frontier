/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.KEM
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Correctness
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Foundations.Control.Monad.StateT
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Represented
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Concrete-only correctness hop for salted joint-oracle FO transforms

This module isolates the `CORR` hop in the classical-ROM decapsulation simulation for an
implicit-rejection salted Fujisaki--Okamoto transform. A direct query receives the session key and
encryption coins in one `JointReply`; it therefore costs one `joint` query, not one query per
projection. The rejection oracle is a separate channel and does not create a PKE correctness
witness. Decapsulation is punctured at the challenge ciphertext and has its own cost.

`Scheme.realHandler` constructs the decrypt/re-encrypt path and `Scheme.simHandler` constructs the
secret-key-free patched-cache path. These handlers begin after the source proof's secret rejection
seed has been guessed: the adversary-visible `J` table and the proof-only `LD` table are therefore
independent here, rather than a model of the original pre-guessing HQC fallback oracle. The proof
inserts a private prefetch handler: real and prefetch are identical until one cached encryption coin
fails to decrypt, while prefetch and keyless have exactly the same output law after completing their
four independent coordinates: joint coins for every full input, off-target joint keys by full
input, target-prefix `LD` keys by ciphertext, and `J` keys. The concrete fixed-key theorem
therefore loses exactly
`(qRO + qD) * ε`; the randomized theorem averages a challenge-aware public adversary over a common
challenge law and key generation using `ExplicitCoinPKE.DeltaCorrect δ`.

This is the single-user, single-challenge specialization of the `CORR` step in Theorem 11 and
Figure 11 of [GlabushHoevelmannsStebila2025]. In HQC v5.1, Section 6.2.2, Theorem 6.4, the source
coin and key oracles are fused as `G(H(ekKEM) || m || salt) = (K, θ)`, so their direct-query
contribution is counted once. The full passive salted-FO lift, its message-guessing and collision
terms, and the HQC instantiation are outside this module.

This module is deliberately **concrete-only**: it proves a finite typed probability-level game hop
and introduces no encoding, parameter family or efficiency predicate. The word-family simulator
witness and HQC-specific executable reduction remain owned by
[cslib-frontier#5279](https://github.com/cslib-community/cslib-frontier/issues/5279). That later
theorem must reuse the existing `WordPKE`/`WordReduction` and `AttackResources`/OracleTM layers,
rather than adding a parallel efficiency bundle to this finite leaf. Accordingly, this module does
not claim a native implementation, strict-PPT closure, running-time, gate-count,
static-description-size or other resource bound for either handler.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointInput`: public prefix, message and salt of a
  joint random-oracle query.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointReply`: named key and encryption-coin
  projections of one joint reply.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.RejectionInput`: the public-key prefix, secret
  rejection seed and full ciphertext supplied to `J`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Query`: joint-oracle, rejection-oracle and
  punctured-decapsulation queries.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.CacheState`: lazy joint, rejection and
  decapsulation caches used by the concrete handlers.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.realHandler` and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simHandler`: the decrypt/re-encrypt and
  keyless cached handlers.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.QueryBounds`: separate `qRO` and `qD` bounds.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.RandomizedAdversary`: randomized programs whose
  external query bounds hold for each fixed coin value and public challenge.

## Main results

* `Scheme.realHandler_joint_bad_eq_msgFailProb` and
  `Scheme.realHandler_decaps_bad_eq_msgFailProb`: exact one-query `CORR` probabilities for fresh
  target-prefix direct and decapsulation inputs.
* `Scheme.realHandler_rejection_bad_eq_zero`: the separate `J` channel creates no correctness
  witness.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.closeTo_run_realHandler_simHandler`:
  concrete real-to-keyless fixed-key hop.
* `Scheme.advantage_randomizedRealHandler_simHandler_le`: concrete challenge-aware randomized
  real-to-keyless advantage bound.

## References

* [L. Glabush, K. Hövelmanns, D. Stebila, *Tight Multi-challenge Security Reductions for Key
  Encapsulation Mechanisms*][GlabushHoevelmannsStebila2025], Definition 1 (printed p. 6),
  Theorem 11 and Figure 11.
* [*Hamming Quasi-Cyclic (HQC), version 5.1*][HQC2026], Section 6.2.2,
  Definition 6.2.1 and Theorem 6.4.
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open scoped Cslib ENNReal NNReal

/-! ### Query types, cost model, and scheme data -/

/-- Input of the salted joint random oracle: a public-key prefix, message and salt. HQC uses
`H(ekKEM)` as the prefix. -/
structure JointInput (Prefix M Salt : Type) where
  /-- Public prefix. For a fixed scheme key, the matching target prefix uses the ciphertext-indexed
  `LD` key; every other prefix uses an independent key indexed by the full joint input. -/
  keyPrefix : Prefix
  /-- PKE plaintext whose encryption coins are derived by the oracle. -/
  message : M
  /-- Public salt carried by the KEM ciphertext. -/
  salt : Salt
  deriving DecidableEq, Fintype

/-- One reply of the joint random oracle. Named projections prevent silently swapping the source
orders `(key, coins)` and `(coins, key)`. -/
structure JointReply (K R : Type) where
  /-- Session key derived by the joint oracle. -/
  key : K
  /-- Explicit PKE encryption coins derived by the same oracle call. -/
  coins : R
  deriving DecidableEq

/-- Ciphertext of the salted transform: an underlying PKE ciphertext and its public salt. -/
structure Ciphertext (CT Salt : Type) where
  /-- Underlying PKE ciphertext. -/
  pke : CT
  /-- Salt used by the joint-oracle input. -/
  salt : Salt
  deriving DecidableEq, Fintype

/-- Source-shaped input of the implicit-rejection oracle. HQC instantiates these fields as
`H(ekPKE)`, the secret rejection seed `σ`, and `cKEM`, respectively. Keeping the fields explicit
prevents a generic opaque oracle domain from hiding the secret-prefix boundary used by the
preceding guessing hop. -/
structure RejectionInput (Prefix Sigma CT Salt : Type) where
  /-- Public prefix selecting the PKE public key. -/
  keyPrefix : Prefix
  /-- Secret implicit-rejection seed. -/
  secret : Sigma
  /-- Full salted KEM ciphertext. -/
  ciphertext : Ciphertext CT Salt
  deriving DecidableEq, Fintype

/-- Oracle queries of the salted implicit-rejection CCA experiment. `joint` returns both the KEM
key and encryption coins in one response. `rejection` is the separate `J` channel. `decaps` is
punctured at the challenge by `Query.dispatch`. -/
inductive Query (JointPrefix M Salt RejectPrefix Sigma CT : Type) where
  /-- One query to the fused key-and-coin random oracle. -/
  | joint (input : JointInput JointPrefix M Salt)
  /-- One query to the separate implicit-rejection oracle `J`. -/
  | rejection (input : RejectionInput RejectPrefix Sigma CT Salt)
  /-- One query to the decapsulation oracle. -/
  | decaps (ciphertext : Ciphertext CT Salt)

/-- Response family for `Query`. -/
abbrev Response {JointPrefix M Salt RejectPrefix Sigma CT : Type} (K R : Type) :
    Query JointPrefix M Salt RejectPrefix Sigma CT → Type
  | .joint _ => JointReply K R
  | .rejection _ => K
  | .decaps _ => Option K

namespace Query

variable {JointPrefix M Salt RejectPrefix Sigma CT K R : Type}

/-- Dispatch a salted-FO query. A decapsulation query equal to the challenge is rejected before
the supplied decapsulation handler runs. The rejection oracle is kept separate from the joint
oracle, matching HQC's `J` fallback. -/
@[simp] def dispatch [DecidableEq (Ciphertext CT Salt)] {m : Type → Type} [Monad m]
    (joint : JointInput JointPrefix M Salt → m (JointReply K R))
    (rejection : RejectionInput RejectPrefix Sigma CT Salt → m K)
    (decaps : Ciphertext CT Salt → m (Option K)) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) → m (Response K R q)
  | .joint input => joint input
  | .rejection input => rejection input
  | .decaps ciphertext => if ciphertext = challenge then pure none else decaps ciphertext

/-- Cost counting direct joint-oracle queries. One response containing both `key` and `coins`
costs exactly one. -/
@[expose, simp] def jointCost : Query JointPrefix M Salt RejectPrefix Sigma CT → ℕ
  | .joint _ => 1
  | .rejection _ => 0
  | .decaps _ => 0

/-- Cost counting decapsulation queries. -/
@[expose, simp] def decapsCost : Query JointPrefix M Salt RejectPrefix Sigma CT → ℕ
  | .joint _ => 0
  | .rejection _ => 0
  | .decaps _ => 1

end Query

/-- Single-user salted FO data needed by the correctness simulation. The public-prefix maps make
the two oracle domains explicit without fixing a byte encoding. -/
structure Scheme (PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type) where
  /-- Underlying explicit-coin public-key encryption scheme. -/
  pke : ExplicitCoinPKE PK SK M R CT
  /-- Source of joint-oracle keys and implicit-rejection keys. -/
  sampleKey : ProbComp K
  /-- Public-key prefix of the joint `G` domain. -/
  jointPrefix : PK → JointPrefix
  /-- Public-key prefix of the rejection `J` domain. -/
  rejectionPrefix : PK → RejectPrefix
  /-- Secret seed used only in the rejection `J` domain. -/
  rejectionSecret : SK → Sigma

/-- Lazy state shared by the concrete salted-FO handlers after the secret-seed guessing hop.
`jointCache` is the fused `G` table, `rejectionCache` is the now-independent adversary-visible `J`
table, and `decapsCache` is Figure 11's patched decapsulation table `LD`. -/
structure CacheState (JointPrefix M Salt RejectPrefix Sigma CT K R : Type) where
  /-- Lazy fused-oracle table. -/
  jointCache : List (JointInput JointPrefix M Salt × JointReply K R) := []
  /-- Lazy rejection-oracle table. -/
  rejectionCache : List (RejectionInput RejectPrefix Sigma CT Salt × K) := []
  /-- Lazy patched decapsulation table. -/
  decapsCache : List (Ciphertext CT Salt × K) := []

/-! ### Erased completion tables and lazy projections -/

/-- The four independent tables visible after erasing target-prefix cached joint keys: joint
coins, off-target joint keys, patched decapsulation keys and rejection keys. -/
private abbrev CompletionSpec (JointPrefix M Salt RejectPrefix Sigma CT K R : Type) :=
  (((fun _ : JointInput JointPrefix M Salt => R) ⊕ₒ
      (fun _ : JointInput JointPrefix M Salt => K)) ⊕ₒ
    (fun _ : Ciphertext CT Salt => K)) ⊕ₒ
  (fun _ : RejectionInput RejectPrefix Sigma CT Salt => K)

/-- Project the independent keys of off-target joint inputs from a concrete fused-oracle table. -/
private def offTargetKeyCache {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK) :
    List (JointInput JointPrefix M Salt × JointReply K R) →
      List (JointInput JointPrefix M Salt × K)
  | [] => []
  | (input, reply) :: rest =>
    if input = ⟨S.jointPrefix pk, input.message, input.salt⟩ then
      offTargetKeyCache S pk rest
    else
      (input, reply.key) :: offTargetKeyCache S pk rest

/-- Joined partial table represented by a concrete salted-handler cache. -/
private def completionCache {JointPrefix M Salt RejectPrefix Sigma CT K R : Type}
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {PK SK : Type} (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    RandomOracle.Cache (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) :=
  RandomOracle.Cache.sum
    (RandomOracle.Cache.sum
      (RandomOracle.Cache.sum
        (RandomOracle.ofList (st.jointCache.map fun entry => (entry.1, entry.2.coins)))
        (RandomOracle.ofList (offTargetKeyCache S pk st.jointCache)))
      (RandomOracle.ofList st.decapsCache))
    (RandomOracle.ofList st.rejectionCache)

namespace Scheme

variable {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}

/-- Independent sampling laws of the coin, off-target joint-key, `LD` and `J` tables. -/
private noncomputable abbrev completionDistribution
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) :
    (q : ((JointInput JointPrefix M Salt ⊕ JointInput JointPrefix M Salt) ⊕
      Ciphertext CT Salt) ⊕
      RejectionInput RejectPrefix Sigma CT Salt) →
      PMF (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R q) :=
  OracleComp.sumHandler
    (OracleComp.sumHandler
      (OracleComp.sumHandler (fun _ => ProbComp.eval S.pke.sampleCoins)
        (fun _ => ProbComp.eval S.sampleKey))
      (fun _ => ProbComp.eval S.sampleKey))
    (fun _ => ProbComp.eval S.sampleKey)

/-- Construct the joint-oracle input selected by a public key, message and salt. -/
def jointInput (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (m : M) (salt : Salt) : JointInput JointPrefix M Salt :=
  ⟨S.jointPrefix pk, m, salt⟩

private theorem lookup_offTargetKeyCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (entries : List (JointInput JointPrefix M Salt × JointReply K R))
    (input : JointInput JointPrefix M Salt) :
    (offTargetKeyCache S pk entries).lookup input =
      if input = ⟨S.jointPrefix pk, input.message, input.salt⟩ then none
      else (entries.lookup input).map JointReply.key := by
  fun_induction offTargetKeyCache S pk entries with
  | case1 => simp only [List.lookup_nil, Option.map_none]; split <;> rfl -- []
  | case2 cached reply rest hcached ih => -- on-target entry: dropped
    rw [ih]
    by_cases hinput : input = ⟨S.jointPrefix pk, input.message, input.salt⟩
    · simp only [ite_eq_left hinput]
    · have hne : input ≠ cached := by rintro rfl; exact hinput hcached
      simp only [ite_eq_right hinput, List.lookup_cons, beq_eq_false_iff_ne.mpr hne]
  | case3 cached reply rest hcached ih => -- off-target entry: kept
    rcases eq_or_ne input cached with rfl | heq
    · simp only [ite_eq_right hcached, List.lookup_cons, beq_self_eq_true, Option.map_some]
    · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr heq, ih]

/-- Construct the source-shaped `J(H(ekPKE) ∥ σ ∥ cKEM)` input. -/
def rejectionInput (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    RejectionInput RejectPrefix Sigma CT Salt :=
  ⟨S.rejectionPrefix pk, S.rejectionSecret sk, ciphertext⟩

/-! ### Completion programs over the erased tables -/

/-- Patched joint reply as a program over the erased coin and `LD` tables. -/
private def completionJointProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt) :
    OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (JointReply K R) := do
  let coins ← OracleComp.query (spec :=
    CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inl (.inl input)))
  let key ← if input = S.jointInput pk input.message input.salt then
    let ciphertext : Ciphertext CT Salt :=
      ⟨S.pke.encDet pk input.message coins, input.salt⟩
    OracleComp.query (spec :=
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))
  else
    OracleComp.query (spec :=
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inl (.inr input)))
  return ⟨key, coins⟩

open Classical in
/-- Prefetch decapsulation as a program over the erased independent tables. -/
private noncomputable def completionPrefetchDecapsProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (Option K) := do
  match S.pke.dec sk ciphertext.pke with
  | none => some <$> OracleComp.query (spec :=
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))
  | some message =>
    let reply ← S.completionJointProgram pk (S.jointInput pk message ciphertext.salt)
    if S.pke.encDet pk message reply.coins = ciphertext.pke then
      return some reply.key
    else
      some <$> OracleComp.query (spec :=
        CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))

open Classical in
/-- One prefetch-handler call as a program over the erased independent tables. -/
private noncomputable def completionPrefetchProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)
        (Response K R q) :=
  Query.dispatch
    (S.completionJointProgram pk)
    (fun input => OracleComp.query (Sum.inr input))
    (S.completionPrefetchDecapsProgram pk sk) challenge

open Classical in
/-- One keyless-handler call as a program over the erased independent tables. -/
private noncomputable def completionSimProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)
        (Response K R q) :=
  Query.dispatch
    (S.completionJointProgram pk)
    (fun input => OracleComp.query (Sum.inr input))
    (fun ciphertext => some <$> OracleComp.query (Sum.inl (Sum.inr ciphertext))) challenge

/-- On a completed table, prefetch decapsulation and keyless `LD` lookup return the same answer. -/
private theorem interpret_completionPrefetchProgram_eq_simProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (table : (q : ((JointInput JointPrefix M Salt ⊕ JointInput JointPrefix M Salt) ⊕
      Ciphertext CT Salt) ⊕
      RejectionInput RejectPrefix Sigma CT Salt) →
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R q)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) :
    OracleComp.interpret (fun query => PMF.pure (table query))
        (S.completionPrefetchProgram pk sk challenge q) =
      OracleComp.interpret (fun query => PMF.pure (table query))
        (S.completionSimProgram pk challenge q) := by
  classical
  rcases q with input | input | ⟨pkeCiphertext, salt⟩ <;> try rfl
  by_cases hc : (⟨pkeCiphertext, salt⟩ : Ciphertext CT Salt) = challenge
  · simp [completionPrefetchProgram, completionSimProgram, Query.dispatch, hc]
  · simp only [completionPrefetchProgram, completionSimProgram, Query.dispatch, hc, ↓reduceIte]
    cases hdec : S.pke.dec sk pkeCiphertext with
    | none => simp only [completionPrefetchDecapsProgram, hdec]
    | some message =>
      simp only [completionPrefetchDecapsProgram, completionJointProgram, jointInput, hdec,
        interp_norm, pmf_norm, ite_true]
      split_ifs with h
      · rw [h]
        simp only [OracleComp.interpret_pure, PMF.monad_pure_eq_pure]
      · simp only [interp_norm, pmf_norm]

/-! ### Concrete real, prefetch, and keyless handlers -/

private noncomputable def cacheJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) :=
  fun st =>
    match st.jointCache.lookup input with
    | some reply => PMF.pure (reply, st)
    | none =>
      (ProbComp.eval S.pke.sampleCoins).bind fun coins =>
        if input = S.jointInput pk input.message input.salt then
          let ciphertext : Ciphertext CT Salt :=
            ⟨S.pke.encDet pk input.message coins, input.salt⟩
          if valid input.message coins then
            match st.decapsCache.lookup ciphertext with
            | some key =>
              let reply := ⟨key, coins⟩
              PMF.pure (reply, { st with jointCache := (input, reply) :: st.jointCache })
            | none =>
              (ProbComp.eval S.sampleKey).map fun key =>
                let reply := ⟨key, coins⟩
                (reply, { st with
                  jointCache := (input, reply) :: st.jointCache
                  decapsCache := (ciphertext, key) :: st.decapsCache })
          else
            (ProbComp.eval S.sampleKey).map fun key =>
              let reply := ⟨key, coins⟩
              (reply, { st with jointCache := (input, reply) :: st.jointCache })
        else
          (ProbComp.eval S.sampleKey).map fun key =>
            let reply := ⟨key, coins⟩
            (reply, { st with jointCache := (input, reply) :: st.jointCache })

open Classical in
/-- Coupled real joint oracle. A correctly decrypting target-prefix encryption patches the
decapsulation cache, while a failing one is left unpatched and is exactly a `CORR` witness.
An off-target query instead samples an independent key indexed by its full joint input and does
not inspect or change the decapsulation cache. -/
noncomputable def realJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) :=
  S.cacheJoint pk
    (fun m coins => S.pke.dec sk (S.pke.encDet pk m coins) = some m) input

/-- Keyless simulated joint oracle. A fresh target-prefix query patches the decapsulation cache;
a fresh off-target query samples an independent key indexed by its full joint input without
inspecting or changing that cache. It contains no secret-key argument. -/
noncomputable def simJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) :=
  S.cacheJoint pk (fun _ _ => True) input

/-- Post-secret-seed-guessing adversary-visible rejection oracle. It is independent of `LD`, is
shared by both games, and never changes the correctness cache. -/
noncomputable def rejection [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (input : RejectionInput RejectPrefix Sigma CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF K :=
  fun st =>
    match st.rejectionCache.lookup input with
    | some key => PMF.pure (key, st)
    | none => (ProbComp.eval S.sampleKey).map fun key =>
      (key, { st with rejectionCache := (input, key) :: st.rejectionCache })

/-- Figure-11 decapsulation table. This is independent of the adversary-visible `J` table after
the preceding secret-seed guessing hop. -/
noncomputable def decapsKey [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF K :=
  fun st =>
    match st.decapsCache.lookup ciphertext with
    | some key => PMF.pure (key, st)
    | none => (ProbComp.eval S.sampleKey).map fun key =>
      (key, { st with decapsCache := (ciphertext, key) :: st.decapsCache })

open Classical in
/-- Shared decrypt/re-encrypt/fallback decapsulation path parameterized by the joint lookup
oracle (`realJoint` in `realDecaps`, `simJoint` in `prefetchDecaps`). -/
private noncomputable def decapsWithJoint [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK)
    (joint : JointInput JointPrefix M Salt →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R))
    (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) := do
  match S.pke.dec sk ciphertext.pke with
  | none => some <$> S.decapsKey ciphertext
  | some message =>
    let reply ← joint (S.jointInput pk message ciphertext.salt)
    if S.pke.encDet pk message reply.coins = ciphertext.pke then
      return some reply.key
    else
      some <$> S.decapsKey ciphertext

/-- Real decrypt/re-encrypt decapsulation path. Its implicit call to the fused joint oracle is
why a decapsulation query contributes one further correctness opportunity. -/
noncomputable def realDecaps [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) :=
  S.decapsWithJoint pk sk (S.realJoint pk sk) ciphertext

/-- Proof-only prefetch decapsulation path. It decrypts and re-encrypts exactly as `realDecaps`,
but uses `simJoint`, so every joint reply it creates is linked to the patched `LD` table. -/
private noncomputable def prefetchDecaps [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) :=
  S.decapsWithJoint pk sk (S.simJoint pk) ciphertext

/-- Keyless cached decapsulation simulator. Target-prefix direct joint queries patch
`decapsCache`; a fresh decapsulation query samples the same independent fallback table without
decrypting. Off-target joint keys do not use this table. -/
noncomputable def simDecaps [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) :=
  some <$> S.decapsKey ciphertext

/-- Concrete punctured post-secret-seed-guessing real handler. Challenge rejection happens in the
common dispatcher before `realDecaps` can decrypt or query the joint oracle. -/
noncomputable def realHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.realJoint pk sk) S.rejection (S.realDecaps pk sk) challenge

/-- Proof-only prefetch handler used between the real and keyless games. Its direct joint queries
use `simJoint`; decapsulation still decrypts, but its implicit joint query also uses `simJoint`.
Thus it has the real handler's cache evolution on good executions and the keyless handler's
lookup-visible joint/`LD` invariant. -/
private noncomputable def prefetchHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.simJoint pk) S.rejection (S.prefetchDecaps pk sk) challenge

/-- Concrete punctured post-secret-seed-guessing keyless handler. Its type has no secret key; the
independent `J` table remains a source-shaped adversary query, while decapsulation uses only
`decapsCache`. -/
noncomputable def simHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.simJoint pk) S.rejection S.simDecaps challenge

/-! ### Cache invariants (`GoodCache` and `Linked`) -/

/-- Message/coin projection of the target-prefix entries in the fused joint-oracle cache. -/
private def coinCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : List (M × R) :=
  (st.jointCache.filter fun entry =>
    entry.1 = S.jointInput pk entry.1.message entry.1.salt).map fun entry =>
      (entry.1.message, entry.2.coins)

/-- Every target-prefix fused-oracle entry in the cache decrypts correctly for its message. -/
def GoodCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : Prop :=
  S.pke.GoodCache pk sk (S.coinCache pk st)

/-- The empty salted-FO cache contains no correctness witness. -/
@[simp] theorem GoodCache.empty
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK) (sk : SK) :
    S.GoodCache pk sk ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) := by
  simp [GoodCache, coinCache, ExplicitCoinPKE.GoodCache]

/-- Every cached target-prefix joint reply carries the `LD` key of its derived ciphertext. -/
private def Linked [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : Prop :=
  ∀ input reply, (input, reply) ∈ st.jointCache →
    input = S.jointInput pk input.message input.salt →
    st.decapsCache.lookup ⟨S.pke.encDet pk input.message reply.coins, input.salt⟩ =
      some reply.key

/-- Goodness is inherited by a state whose joint cache is a subcache. -/
private theorem GoodCache.of_subset
    [DecidableEq (JointInput JointPrefix M Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK}
    {st st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (h : S.GoodCache pk sk st')
    (hsub : ∀ entry ∈ st.jointCache, entry ∈ st'.jointCache) : S.GoodCache pk sk st := by
  refine ExplicitCoinPKE.GoodCache.of_subset h fun entry hentry => ?_
  obtain ⟨cached, hcached, rfl⟩ := List.mem_map.mp hentry
  exact List.mem_map.mpr ⟨cached, List.mem_filter.mpr
    ⟨hsub cached (List.mem_filter.mp hcached).1, (List.mem_filter.mp hcached).2⟩, rfl⟩

/-! ### Per-oracle completion projections -/

private theorem simJoint_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.simJoint pk input st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionJointProgram pk input)).run (completionCache S pk st) := by
  simp only [simJoint, cacheJoint, completionCache, completionJointProgram,
    completionDistribution, OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
  rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl]
  cases hlookup : st.jointCache.lookup input with
  | some reply =>
    have hmem : (input, reply) ∈ st.jointCache := by
      obtain ⟨_, _, htable, -⟩ := List.lookup_eq_some_iff.mp hlookup
      simp [htable]
    simp only [hlookup, RandomOracle.answer, RandomOracle.ofList,
      List.lookup_map_snd, Option.map_some, PMF.monad_bind_eq_bind, PMF.pure_map, PMF.pure_bind]
    by_cases htarget : input = S.jointInput pk input.message input.salt
    · rw [ite_eq_left htarget]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.run_interpret_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr]
      simp only [RandomOracle.answer, RandomOracle.ofList, hlinked input reply hmem htarget,
        PMF.pure_map, PMF.pure_bind]
    · have hkey : (offTargetKeyCache S pk st.jointCache).lookup input = some reply.key := by
        simpa [lookup_offTargetKeyCache, jointInput, hlookup] using htarget
      rw [ite_eq_right htarget]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.run_interpret_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr]
      simp only [RandomOracle.answer, RandomOracle.ofList, hkey, PMF.pure_map, PMF.pure_bind]
  | none =>
    have hcoins : RandomOracle.ofList
        (st.jointCache.map fun e => (e.1, e.2.coins)) input = none := by
      simp only [RandomOracle.ofList, List.lookup_map_snd, hlookup, Option.map_none]
    simp only [RandomOracle.answer_of_none _ _ _ hcoins, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
    by_cases htarget : input = S.jointInput pk input.message input.salt
    · have hoff : ∀ r, offTargetKeyCache S pk ((input, r) :: st.jointCache) =
          offTargetKeyCache S pk st.jointCache := fun _ => by
        rw [offTargetKeyCache, ite_eq_left (by simpa only [jointInput] using htarget)]
      rw [ite_eq_left htarget, ite_eq_left htarget]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.run_interpret_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp]
      cases hdec : st.decapsCache.lookup ⟨S.pke.encDet pk input.message coins, input.salt⟩ <;>
        simp only [ite_true, RandomOracle.answer, RandomOracle.ofList, hdec, hoff,
          RandomOracle.ofList_cons, List.map_cons, Function.comp_def,
          PMF.map, PMF.bind_bind, PMF.pure_bind]
    · have hoff : ∀ r, offTargetKeyCache S pk ((input, r) :: st.jointCache) =
          (input, r.key) :: offTargetKeyCache S pk st.jointCache := fun _ => by
        rw [offTargetKeyCache, ite_eq_right (by simpa only [jointInput] using htarget)]
      have hkey : RandomOracle.ofList (offTargetKeyCache S pk st.jointCache) input = none := by
        simp [RandomOracle.ofList, lookup_offTargetKeyCache, hlookup]
      rw [ite_eq_right htarget, ite_eq_right htarget]
      simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.run_interpret_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl,
        RandomOracle.answer_sum_inr, PMF.map_comp, RandomOracle.answer_of_none _ _ _ hkey]
      simp only [RandomOracle.ofList_cons, hoff,
        PMF.map, List.map_cons, Function.comp_def, PMF.bind_bind, PMF.pure_bind]

private theorem rejection_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (S.rejection input st).map (fun z => (z.1, completionCache S pk z.2)) =
      RandomOracle.answer S.completionDistribution (.inr input) (completionCache S pk st) := by
  simp only [completionCache]
  rw [RandomOracle.answer_sum_inr, ← RandomOracle.memoize_map_ofList, PMF.map_comp]
  cases hlookup : st.rejectionCache.lookup input <;>
    simp only [rejection, memoize, hlookup, PMF.map, pmf_norm]

private theorem simDecaps_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK)
    (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    ((some <$> S.decapsKey ciphertext) st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (some <$> OracleComp.query (.inl (.inr ciphertext)))).run (completionCache S pk st) := by
  have hkey : (S.decapsKey ciphertext st).map (fun z => (z.1, completionCache S pk z.2)) =
      RandomOracle.answer S.completionDistribution (.inl (.inr ciphertext))
        (completionCache S pk st) := by
    simp only [completionCache]
    rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp,
      ← RandomOracle.memoize_map_ofList, PMF.map_comp]
    cases hlookup : st.decapsCache.lookup ciphertext <;>
      simp only [decapsKey, memoize, hlookup, PMF.map, pmf_norm]
  simpa only [StateT.map_apply, PMF.monad_map_eq_map, OracleComp.run_interpret_map,
    OracleComp.run_interpret_query, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq] using
    congrArg (PMF.map (Prod.map some id)) hkey

/-! ### Support characterizations and `Linked` preservation -/

private theorem mem_support_cacheJoint_iff
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (reply : JointReply K R)
    (st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (reply, st') ∈ (S.cacheJoint pk valid input st).support ↔
      (st.jointCache.lookup input = some reply ∧ st' = st) ∨
      (st.jointCache.lookup input = none ∧
        reply.coins ∈ (ProbComp.eval S.pke.sampleCoins).support ∧
        ((input = S.jointInput pk input.message input.salt ∧
            valid input.message reply.coins ∧
            st.decapsCache.lookup ⟨S.pke.encDet pk input.message reply.coins, input.salt⟩ =
              some reply.key ∧
            st' = { st with jointCache := (input, reply) :: st.jointCache }) ∨
          (input = S.jointInput pk input.message input.salt ∧
            valid input.message reply.coins ∧
            st.decapsCache.lookup ⟨S.pke.encDet pk input.message reply.coins, input.salt⟩ = none ∧
            reply.key ∈ (ProbComp.eval S.sampleKey).support ∧
            st' = { st with
              jointCache := (input, reply) :: st.jointCache
              decapsCache :=
                (⟨S.pke.encDet pk input.message reply.coins, input.salt⟩, reply.key) ::
                  st.decapsCache }) ∨
          (¬(input = S.jointInput pk input.message input.salt ∧ valid input.message reply.coins) ∧
            reply.key ∈ (ProbComp.eval S.sampleKey).support ∧
            st' = { st with jointCache := (input, reply) :: st.jointCache }))) := by
  rcases reply with ⟨key, coins⟩
  cases hlookup : st.jointCache.lookup input with
  | some cached =>
    simp [cacheJoint, hlookup, Prod.ext_iff, eq_comm]
  | none =>
    constructor
    · intro hz
      refine Or.inr ⟨rfl, ?_⟩
      supp_cases hz [cacheJoint, hlookup] with
        ⟨c, hc, (⟨htarget, ⟨hvalid, hz⟩ | ⟨hnvalid, k, hk, ⟨rfl, rfl⟩, rfl⟩⟩ |
          ⟨hntarget, k, hk, ⟨rfl, rfl⟩, rfl⟩)⟩
      · cases hdec : st.decapsCache.lookup ⟨S.pke.encDet pk input.message c, input.salt⟩ with
        | some k =>
          supp_cases hz [hdec] with ⟨⟨rfl, rfl⟩, rfl⟩
          exact ⟨hc, Or.inl ⟨htarget, hvalid, hdec, rfl⟩⟩
        | none =>
          supp_cases hz [hdec] with ⟨k, hk, ⟨rfl, rfl⟩, rfl⟩
          exact ⟨hc, Or.inr (Or.inl ⟨htarget, hvalid, hdec, hk, rfl⟩)⟩
      · exact ⟨hc, Or.inr (Or.inr ⟨fun h => hnvalid h.2, hk, rfl⟩)⟩
      · exact ⟨hc, Or.inr (Or.inr ⟨fun h => hntarget h.1, hk, rfl⟩)⟩
    · rintro (⟨h, -⟩ | ⟨-, hc, hbranch⟩)
      · cases h
      · rw [cacheJoint, hlookup, PMF.mem_support_bind_iff]
        refine ⟨coins, hc, ?_⟩
        rcases hbranch with ⟨htarget, hvalid, hdec, rfl⟩ |
            ⟨htarget, hvalid, hdec, hk, rfl⟩ | ⟨hn, hk, rfl⟩
        · simp [ite_eq_left htarget, hvalid, hdec]
        · simp [ite_eq_left htarget, hvalid, hdec, (PMF.mem_support_iff _ _).mp hk]
        · by_cases htarget : input = S.jointInput pk input.message input.salt
          · have hnv : ¬valid input.message coins := fun hv => hn ⟨htarget, hv⟩
            simp [hnv, (PMF.mem_support_iff _ _).mp hk]
          · simp [ite_eq_right htarget, (PMF.mem_support_iff _ _).mp hk]

private theorem mem_support_rejection_iff
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (key : K) (st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (key, st') ∈ (S.rejection input st).support ↔
      (st.rejectionCache.lookup input = some key ∧ st' = st) ∨
      (st.rejectionCache.lookup input = none ∧ key ∈ (ProbComp.eval S.sampleKey).support ∧
        st' = { st with rejectionCache := (input, key) :: st.rejectionCache }) := by
  cases h : st.rejectionCache.lookup input <;> simp [rejection, h, Prod.ext_iff, eq_comm]

private theorem mem_support_decapsKey_iff [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (key : K) (st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (key, st') ∈ (S.decapsKey ciphertext st).support ↔
      (st.decapsCache.lookup ciphertext = some key ∧ st' = st) ∨
      (st.decapsCache.lookup ciphertext = none ∧ key ∈ (ProbComp.eval S.sampleKey).support ∧
        st' = { st with decapsCache := (ciphertext, key) :: st.decapsCache }) := by
  cases h : st.decapsCache.lookup ciphertext <;> simp [decapsKey, h, Prod.ext_iff, eq_comm]

private theorem stateT_ite_apply {σ α : Type} (c : Prop) [Decidable c]
    (x y : StateT σ PMF α) (s : σ) :
    (if c then x else y) s = if c then x s else y s := by
  split_ifs <;> rfl

private theorem lookup_cons_of_lookup_eq_none {α β : Type} [DecidableEq α]
    {l : List (α × β)} {k k' : α} {v v' : β}
    (h : l.lookup k = some v) (hnone : l.lookup k' = none) :
    ((k', v') :: l).lookup k = some v := by
  rcases eq_or_ne k k' with rfl | hk
  · cases h.symm.trans hnone
  · simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using h

private theorem Linked.of_simJoint
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {input : JointInput JointPrefix M Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.simJoint pk input st).support) : S.Linked pk z.2 := by
  rcases z with ⟨z₁, st'⟩
  rcases (S.mem_support_cacheJoint_iff pk (fun _ _ => True) input st z₁ st').mp hz with
    ⟨-, rfl⟩ | ⟨-, -, hbranch⟩
  · exact hlinked
  · intro cached reply hmem hcached
    rcases hbranch with ⟨-, -, hdec, rfl⟩ | ⟨-, -, hnone, -, rfl⟩ | ⟨hn, -, rfl⟩ <;>
      rcases List.mem_cons.mp hmem with ⟨rfl, rfl⟩ | hold
    · exact hdec
    · exact hlinked cached reply hold hcached
    · simp
    · exact lookup_cons_of_lookup_eq_none (hlinked cached reply hold hcached) hnone
    · exact (hn ⟨hcached, trivial⟩).elim
    · exact hlinked cached reply hold hcached

private theorem Linked.of_decapsKey
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {ciphertext : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.decapsKey ciphertext st).support) : S.Linked pk z.2 := by
  rcases z with ⟨key, st'⟩
  rcases (S.mem_support_decapsKey_iff ciphertext st key st').mp hz with
    ⟨-, rfl⟩ | ⟨hlookup, -, rfl⟩
  · exact hlinked
  · exact fun input reply hmem htarget =>
      lookup_cons_of_lookup_eq_none (hlinked input reply hmem htarget) hlookup

private theorem Linked.of_rejection
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {input : RejectionInput RejectPrefix Sigma CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.rejection input st).support) : S.Linked pk z.2 := by
  rcases z with ⟨key, st'⟩
  rcases (S.mem_support_rejection_iff input st key st').mp hz with
    ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> exact hlinked

private theorem prefetchDecaps_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.prefetchDecaps pk sk ciphertext st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionPrefetchDecapsProgram pk sk ciphertext)).run (completionCache S pk st) := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    simpa only [prefetchDecaps, decapsWithJoint, completionPrefetchDecapsProgram, hdec] using
      S.simDecaps_map_completionCache pk ciphertext st
  | some message =>
    simp only [prefetchDecaps, decapsWithJoint, completionPrefetchDecapsProgram, hdec,
      StateT.bind_apply, PMF.monad_bind_eq_bind, PMF.map_bind, OracleComp.run_interpret_bind,
      ← S.simJoint_map_completionCache pk (S.jointInput pk message ciphertext.salt) st hlinked,
      PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun z _ => ?_
    split <;> rename_i henc
    · simp only [henc, ↓reduceIte, interp_norm, pmf_norm]
      exact PMF.pure_map (fun y => (y.1, completionCache S pk y.2)) (some z.1.key, z.2)
    · simpa only [henc, ↓reduceIte, Function.comp_def] using
        S.simDecaps_map_completionCache pk ciphertext z.2

private theorem Linked.of_prefetchDecaps
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK} {ciphertext : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.prefetchDecaps pk sk ciphertext st).support) : S.Linked pk z.2 := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    supp_cases hz [prefetchDecaps, decapsWithJoint, hdec, StateT.map_apply] with ⟨x, hx, rfl⟩
    exact hlinked.of_decapsKey hx
  | some message =>
    supp_cases hz [prefetchDecaps, decapsWithJoint, hdec, StateT.bind_apply, stateT_ite_apply,
      StateT.pure_apply, StateT.map_apply] with ⟨reply, hreply, ⟨-, rfl⟩ | ⟨-, x, hx, rfl⟩⟩
    · exact hlinked.of_simJoint hreply
    · exact (hlinked.of_simJoint hreply).of_decapsKey hx

private theorem Linked.of_dispatch
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {challenge : Ciphertext CT Salt}
    {decaps : Ciphertext CT Salt →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K)}
    (hdecaps : ∀ ciphertext (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
      (z : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R),
      S.Linked pk st → z ∈ (decaps ciphertext st).support → S.Linked pk z.2)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st) (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {z : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (Query.dispatch (S.simJoint pk) S.rejection decaps challenge q st).support) :
    S.Linked pk z.2 := by
  rcases q with input | input | ciphertext
  · exact hlinked.of_simJoint hz
  · exact hlinked.of_rejection hz
  · supp_cases hz [Query.dispatch, stateT_ite_apply, StateT.pure_apply] with ⟨-, rfl⟩ | ⟨-, hz⟩
    · exact hlinked
    · exact hdecaps ciphertext st z hlinked hz

/-! ### Lifting completion projections and full-run equivalence -/

private theorem dispatch_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt)
    {decaps : Ciphertext CT Salt →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K)}
    {decapsProg : Ciphertext CT Salt →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (Option K)}
    (hdecaps : ∀ ciphertext (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R),
      S.Linked pk st →
      (decaps ciphertext st).map (fun z => (z.1, completionCache S pk z.2)) =
        (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
          (decapsProg ciphertext)).run (completionCache S pk st))
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (Query.dispatch (S.simJoint pk) S.rejection decaps challenge q st).map
        (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (Query.dispatch (S.completionJointProgram pk) (fun i => OracleComp.query (Sum.inr i))
          decapsProg challenge q)).run (completionCache S pk st) := by
  rcases q with input | input | ciphertext
  · exact S.simJoint_map_completionCache pk input st hlinked
  · simpa only [Query.dispatch, OracleComp.run_interpret_query] using
      S.rejection_map_completionCache pk input st
  · by_cases hc : ciphertext = challenge
    · simp [Query.dispatch, hc, StateT.run_pure, StateT.pure_apply, PMF.monad_pure_eq_pure]
    · simpa only [Query.dispatch, hc, ↓reduceIte] using hdecaps ciphertext st hlinked

private theorem run_completionHandler_eq_pi
    [Fintype JointPrefix] [Fintype M] [Fintype Salt] [Fintype RejectPrefix]
    [Fintype Sigma] [Fintype CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (handler : (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q))
    (prog : (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (Response K R q))
    (hinv : ∀ q (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R), S.Linked pk st →
      ∀ a st', (a, st') ∈ (handler q st).support → S.Linked pk st')
    (hmap : ∀ q (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R),
      S.Linked pk st →
      (handler q st).map (fun z => (z.1, completionCache S pk z.2)) =
        (OracleComp.interpret (RandomOracle.answer S.completionDistribution) (prog q)).run
          (completionCache S pk st))
    {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A) :
    ((OracleComp.interpret handler program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst =
      (PMF.pi S.completionDistribution).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q))
          (OracleComp.interpret prog program) := by
  have hempty : completionCache S pk
      ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) = fun _ => none :=
    funext fun | .inl (.inl (.inl _)) | .inl (.inl (.inr _)) | .inl (.inr _) | .inr _ => rfl
  have hout := congrArg (PMF.map Prod.fst) <|
    OracleComp.run_interpret_map_state_of_invariant handler
      (fun q => OracleComp.interpret (RandomOracle.answer S.completionDistribution) (prog q))
      (completionCache S pk) (S.Linked pk) hinv hmap program {} (by simp [Linked])
  simp only [PMF.map_comp, Function.comp_def, hempty] at hout
  rw [hout, ← OracleComp.interpret_interpret]
  exact (RandomOracle.interpret_eq_lazy S.completionDistribution _).symm

/-- The proof-only prefetch handler and observable keyless handler have exactly the same output
law from empty caches. Their private final caches are deliberately marginalized. -/
private theorem run_prefetchHandler_eq_simHandler
    [Finite JointPrefix] [Finite M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A) :
    ((OracleComp.interpret (S.prefetchHandler pk sk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst =
      ((OracleComp.interpret (S.simHandler pk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst := by
  let _ : Fintype JointPrefix := Fintype.ofFinite JointPrefix
  let _ : Fintype M := Fintype.ofFinite M
  let _ : Fintype Salt := Fintype.ofFinite Salt
  let _ : Fintype RejectPrefix := Fintype.ofFinite RejectPrefix
  let _ : Fintype Sigma := Fintype.ofFinite Sigma
  let _ : Fintype CT := Fintype.ofFinite CT
  dsimp only [prefetchHandler, completionPrefetchProgram, simHandler, completionSimProgram]
  rw [S.run_completionHandler_eq_pi pk _ _
      (fun q _ hl _ _ hm => hl.of_dispatch (fun _ _ _ h h' => h.of_prefetchDecaps h') q hm)
      (fun q st hl => S.dispatch_map_completionCache pk challenge
        (fun c s h => S.prefetchDecaps_map_completionCache pk sk c s h) q st hl),
    S.run_completionHandler_eq_pi pk _ _
      (fun q _ hl _ _ hm => hl.of_dispatch (fun _ _ _ h h' => by
        supp_cases h' [simDecaps, StateT.map_apply] with ⟨x, hx, rfl⟩
        exact h.of_decapsKey hx) q hm)
      (fun q st hl => S.dispatch_map_completionCache pk challenge (decaps := S.simDecaps)
        (fun c s _ => S.simDecaps_map_completionCache pk c s) q st hl)]
  congr 1 with table : 1
  simp only [OracleComp.interpret_interpret]
  congr 1 with q : 1
  convert S.interpret_completionPrefetchProgram_eq_simProgram pk sk challenge table q using 2 <;>
    · dsimp only [completionPrefetchProgram, completionSimProgram]
      congr 1
      exact Subsingleton.elim _ _

/-! ### Joint-cache monotonicity and `GoodCache` preservation -/

private theorem cacheJoint_jointCache_of_none
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlookup : st.jointCache.lookup input = none)
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.cacheJoint pk valid input st).support) :
    z.2.jointCache = (input, z.1) :: st.jointCache := by
  rcases z with ⟨reply, st'⟩
  rcases (S.mem_support_cacheJoint_iff pk valid input st reply st').mp hz with
    ⟨h, -⟩ | ⟨-, -, ⟨-, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩
  · rw [hlookup] at h; cases h
  all_goals rfl

private theorem cacheJoint_jointCache_eq_or_cons
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.cacheJoint pk valid input st).support) :
    z.2.jointCache = st.jointCache ∨
      z.2.jointCache = (input, z.1) :: st.jointCache := by
  rcases z with ⟨reply, st'⟩
  cases h : st.jointCache.lookup input with
  | some cached =>
    rcases (S.mem_support_cacheJoint_iff pk valid input st reply st').mp hz with
      ⟨-, rfl⟩ | ⟨hn, -⟩
    · exact Or.inl rfl
    · rw [h] at hn; cases hn
  | none => exact Or.inr (S.cacheJoint_jointCache_of_none pk valid input h hz)

private theorem coinCache_cons [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R)
    {st st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (h : st'.jointCache = (input, reply) :: st.jointCache) :
    S.coinCache pk st' =
      if input = S.jointInput pk input.message input.salt then
        (input.message, reply.coins) :: S.coinCache pk st
      else S.coinCache pk st := by
  unfold coinCache
  rw [h, List.filter_cons]
  by_cases ht : input = S.jointInput pk input.message input.salt
  · rw [ite_eq_left ht, decide_eq_true ht]; rfl
  · rw [ite_eq_right ht, decide_eq_false ht]; rfl

private theorem rejection_jointCache_eq
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.rejection input st).support) : z.2.jointCache = st.jointCache := by
  rcases z with ⟨key, st'⟩
  rcases (S.mem_support_rejection_iff input st key st').mp hz with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

private theorem decapsKey_jointCache_eq [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.decapsKey ciphertext st).support) : z.2.jointCache = st.jointCache := by
  rcases z with ⟨key, st'⟩
  rcases (S.mem_support_decapsKey_iff ciphertext st key st').mp hz with
    ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

private theorem toOuterMeasure_notGood_eq_zero
    [DecidableEq (JointInput JointPrefix M Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK} {A : Type}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R} (hs : S.GoodCache pk sk st)
    {μ : PMF (A × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)}
    (hsub : ∀ x ∈ μ.support, ∀ entry ∈ x.2.jointCache, entry ∈ st.jointCache) :
    μ.toOuterMeasure {x | ¬S.GoodCache pk sk x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  exact fun x hx hbad => hbad (hs.of_subset (hsub x hx))

/-! ### Direct joint-query bad-event bounds -/

/-- From a good cache with a fresh target-prefix input, one real joint query creates a bad cache
with exactly the underlying message's decryption-failure probability. This is the direct-query
execution property behind the `qRO` term. -/
private theorem realJoint_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hlookup : st.jointCache.lookup input = none)
    (htarget : input = S.jointInput pk input.message input.salt) :
    (S.realJoint pk sk input st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) := by
  classical
  let μ := S.realJoint pk sk input st
  have hmarg : μ.map (fun z => z.1.coins) = ProbComp.eval S.pke.sampleCoins := by
    simp only [μ, realJoint, cacheJoint, hlookup, ite_eq_left htarget, PMF.map_bind]
    conv_rhs => rw [← PMF.bind_pure (ProbComp.eval S.pke.sampleCoins)]
    refine PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
    split_ifs with hcoins
    · cases st.decapsCache.lookup ⟨S.pke.encDet pk input.message coins, input.salt⟩
      · exact (PMF.map_comp _ _ _).trans (PMF.map_const (ProbComp.eval S.sampleKey) coins)
      · exact PMF.pure_map _ _
    · exact (PMF.map_comp _ _ _).trans (PMF.map_const (ProbComp.eval S.sampleKey) coins)
  have hbad : μ.toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      μ.toOuterMeasure ((fun z => z.1.coins) ⁻¹' {coins |
        S.pke.dec sk (S.pke.encDet pk input.message coins) ≠ some input.message}) := by
    refine μ.toOuterMeasure_apply_eq_of_inter_support_eq (Set.ext fun z => and_congr_left fun hz =>
      not_congr ?_)
    have hcache := S.cacheJoint_jointCache_of_none pk _ input hlookup
      (by simpa only [μ, realJoint] using hz)
    rw [GoodCache, ExplicitCoinPKE.GoodCache, S.coinCache_cons pk input z.1 hcache,
      ite_eq_left htarget]
    exact ⟨fun h => h _ List.mem_cons_self, fun hc e he =>
      (List.mem_cons.mp he).elim (fun h => h ▸ hc) (hs e)⟩
  rw [hbad, ← PMF.toOuterMeasure_map_apply, hmarg, ExplicitCoinPKE.msgFailProb,
    ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)]

/-- From a good cache, one real joint query creates a bad cache with probability at most the
worst-message decryption-failure probability of the fixed key pair. -/
private theorem realJoint_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realJoint pk sk input st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  classical
  by_cases htarget : input = S.jointInput pk input.message input.salt
  · cases hlookup : st.jointCache.lookup input with
    | some _ =>
      refine le_of_eq_of_le (toOuterMeasure_notGood_eq_zero hs fun z hz _ hentry => ?_) zero_le
      supp_cases hz [realJoint, cacheJoint, hlookup]
      exact hentry
    | none =>
      exact (S.realJoint_bad_eq_msgFailProb pk sk input hs hlookup htarget).trans_le
        (ENNReal.ofReal_le_ofReal (S.pke.msgFailProb_le_keyPairMaxFailProb pk sk input.message))
  · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      (Set.disjoint_left.mpr fun z hz hbad => hbad ?_)) zero_le
    rcases S.cacheJoint_jointCache_eq_or_cons pk _ input (by simpa only [realJoint] using hz)
      with heq | heq
    · simpa only [GoodCache, coinCache, heq] using hs
    · simpa only [GoodCache, S.coinCache_cons pk input z.1 heq, ite_eq_right htarget] using hs

/-! ### Identical-until-bad coupling: real versus prefetch handler -/

/-- Real and patched joint sampling assign the same mass to every outcome whose final joint cache
is good. -/
private theorem realJoint_apply_eq_simJoint
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (y : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hy : S.GoodCache pk sk y.2) :
    S.realJoint pk sk input st y = S.simJoint pk input st y := by
  unfold realJoint simJoint cacheJoint
  cases hlookup : st.jointCache.lookup input with
  | some _ => rfl
  | none =>
    by_cases htarget : input = S.jointInput pk input.message input.salt
    · simp only [PMF.bind_apply, ite_eq_left htarget]
      refine tsum_congr fun coins => congrArg ((ProbComp.eval S.pke.sampleCoins coins) * ·) ?_
      by_cases hcoins : S.pke.dec sk (S.pke.encDet pk input.message coins) = some input.message
      · simp only [hcoins, ↓reduceIte]
      · have hzero {μ : PMF (JointReply K R ×
            CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)}
            (hmem_jc : ∀ z ∈ μ.support, ∃ key, z.1 = ⟨key, coins⟩ ∧
              z.2.jointCache = (input, ⟨key, coins⟩) :: st.jointCache) : μ y = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr fun hy_mem => by
            obtain ⟨key, _, hjc⟩ := hmem_jc y hy_mem
            exact hcoins (hy (input.message, coins) (List.mem_map.mpr
              ⟨(input, ⟨key, coins⟩),
                List.mem_filter.mpr ⟨hjc ▸ List.mem_cons_self, decide_eq_true htarget⟩, rfl⟩))
        simp only [hcoins, ↓reduceIte]
        rw [hzero fun z hz => by
          supp_cases hz with ⟨key, -, rfl⟩
          exact ⟨key, rfl, rfl⟩]
        cases st.decapsCache.lookup ⟨S.pke.encDet pk input.message coins, input.salt⟩ <;>
          refine (hzero fun z hz => ?_).symm
        · supp_cases hz with ⟨k, -, rfl⟩
          exact ⟨k, rfl, rfl⟩
        · supp_cases hz
          exact ⟨_, rfl, rfl⟩
    · simp only [ite_eq_right htarget]

/-- The continuation after a successful joint lookup leaves the joint cache unchanged, whether
re-encryption succeeds or decapsulation falls back to `decapsKey`. -/
private theorem decapsContinuation_jointCache_eq
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    (z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    {condition : Prop} [Decidable condition]
    {y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ ((if condition then
        pure (some z.1.key)
      else
        some <$> S.decapsKey ciphertext) z.2).support) :
    y.2.jointCache = z.2.jointCache := by
  supp_cases hy [stateT_ite_apply, StateT.pure_apply, StateT.map_apply] with
    ⟨-, rfl⟩ | ⟨-, x, hx, rfl⟩
  · rfl
  · exact S.decapsKey_jointCache_eq ciphertext hx

/-- Real decapsulation and proof-only prefetch decapsulation assign the same mass to outcomes
whose final joint cache is good. -/
private theorem realDecaps_apply_eq_prefetchDecaps
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hy : S.GoodCache pk sk y.2) :
    S.realDecaps pk sk ciphertext st y = S.prefetchDecaps pk sk ciphertext st y := by
  classical
  unfold realDecaps prefetchDecaps decapsWithJoint
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none => rfl
  | some message =>
    simp only
    refine tsum_congr fun z => ?_
    by_cases hz : S.GoodCache pk sk z.2
    · rw [S.realJoint_apply_eq_simJoint pk sk _ st z hz]
    · have hcont : ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
          pure (some z.1.key)
        else
          some <$> S.decapsKey ciphertext) z.2) y = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr fun hmem => hz <| hy.of_subset fun _ hentry => by
          rwa [S.decapsContinuation_jointCache_eq ciphertext z hmem]
      rw [hcont, mul_zero, mul_zero]

private theorem dispatch_cacheJoint_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (Query.dispatch (S.cacheJoint pk valid) S.rejection
      (S.decapsWithJoint pk sk (S.cacheJoint pk valid)) challenge q st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ y.2.jointCache := by
  have hjoint {input} {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
      {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
      (hz : z ∈ (S.cacheJoint pk valid input st).support) :
      ∀ entry ∈ st.jointCache, entry ∈ z.2.jointCache := by
    rcases S.cacheJoint_jointCache_eq_or_cons pk valid input hz with h | h <;>
      intro entry hentry <;> simp [h, hentry]
  rcases q with input | input | ciphertext
  · exact hjoint hy
  · exact fun entry hentry => S.rejection_jointCache_eq input hy ▸ hentry
  · supp_cases hy [Query.dispatch, stateT_ite_apply, StateT.pure_apply] with ⟨-, rfl⟩ | ⟨-, hy⟩
    · exact fun _ hentry => hentry
    · cases hdec : S.pke.dec sk ciphertext.pke with
      | none =>
        supp_cases hy [decapsWithJoint, hdec, StateT.map_apply] with ⟨x, hx, rfl⟩
        exact fun entry hentry => S.decapsKey_jointCache_eq ciphertext hx ▸ hentry
      | some message =>
        classical
        supp_cases hy [decapsWithJoint, hdec, StateT.bind_apply] with ⟨z, hz, hy⟩
        exact fun entry hentry =>
          S.decapsContinuation_jointCache_eq ciphertext z hy ▸ hjoint hz entry hentry

private theorem identicalUntilBad_realHandler_prefetchHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    OracleComp.IdenticalUntilBad (S.realHandler pk sk challenge)
      (S.prefetchHandler pk sk challenge) (fun st => ¬S.GoodCache pk sk st) where
  agree q st _ answer st' hst' := by
    rcases q with input | input | ciphertext
    · exact S.realJoint_apply_eq_simJoint pk sk input st (answer, st') (of_not_not hst')
    · rfl
    · by_cases hc : ciphertext = challenge
      · simp [realHandler, prefetchHandler, Query.dispatch, hc]
      · simpa only [realHandler, prefetchHandler, Query.dispatch, hc, ↓reduceIte] using
          S.realDecaps_apply_eq_prefetchDecaps pk sk ciphertext st (answer, st')
            (of_not_not hst')
  absorb_first q st hbad y hy hgood := by
    classical
    exact hbad (hgood.of_subset (S.dispatch_cacheJoint_jointCache_subset pk sk _ challenge q hy))
  absorb_second q st hbad y hy hgood :=
    hbad (hgood.of_subset (S.dispatch_cacheJoint_jointCache_subset pk sk _ challenge q hy))

/-! ### Decapsulation and per-handler bad-event probabilities -/

/-- A successful real decapsulation preserves exactly the bad-cache probability of its implicit
joint query: its remaining continuation never changes the joint cache. -/
private theorem realDecaps_bad_eq_realJoint_bad
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hdec : S.pke.dec sk ciphertext.pke = some message) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      (S.realJoint pk sk (S.jointInput pk message ciphertext.salt) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} := by
  classical
  unfold realDecaps decapsWithJoint
  simp only [hdec, StateT.bind_apply, PMF.monad_bind_eq_bind]
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun z => ?_
  let cont := (if S.pke.encDet pk message z.1.coins = ciphertext.pke then
    pure (some z.1.key) else some <$> S.decapsKey ciphertext) z.2
  have hmem_jc {y} (hy : y ∈ cont.support) : y.2.jointCache = z.2.jointCache :=
    S.decapsContinuation_jointCache_eq ciphertext z hy
  by_cases hbad : ¬S.GoodCache pk sk z.2
  · rw [(PMF.toOuterMeasure_apply_eq_one_iff cont {y | ¬S.GoodCache pk sk y.2}).mpr
        fun y hy hgood => hbad (hgood.of_subset fun _ h => (hmem_jc hy) ▸ h),
      mul_one, Set.indicator_of_mem hbad]
  · rw [toOuterMeasure_notGood_eq_zero (μ := cont) (not_not.mp hbad)
        fun y hy _ h => (hmem_jc hy) ▸ h,
      mul_zero, Set.indicator_of_notMem hbad]

/-- From a good cache with a fresh implicit joint input, one successful real decapsulation creates
a bad cache with exactly the decoded message's decryption-failure probability. This is the
decapsulation execution property behind the independent `qD` term. -/
private theorem realDecaps_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hdec : S.pke.dec sk ciphertext.pke = some message)
    (hlookup : st.jointCache.lookup (S.jointInput pk message ciphertext.salt) = none) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk message) := by
  rw [S.realDecaps_bad_eq_realJoint_bad pk sk ciphertext message hdec]
  exact S.realJoint_bad_eq_msgFailProb pk sk
    (S.jointInput pk message ciphertext.salt) hs hlookup rfl

/-- A fresh target-prefix joint query through the real handler has exactly the underlying
message's decryption-failure probability of creating a bad cache. -/
theorem realHandler_joint_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hlookup : st.jointCache.lookup input = none)
    (htarget : input = S.jointInput pk input.message input.salt) :
    (S.realHandler pk sk challenge (.joint input) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) := by
  simpa only [realHandler, Query.dispatch] using
    S.realJoint_bad_eq_msgFailProb pk sk input hs hlookup htarget

/-- A fresh nonchallenge decapsulation query through the real handler has exactly the decoded
message's decryption-failure probability of creating a bad cache. -/
theorem realHandler_decaps_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hne : ciphertext ≠ challenge) (hs : S.GoodCache pk sk st)
    (hdec : S.pke.dec sk ciphertext.pke = some message)
    (hlookup : st.jointCache.lookup (S.jointInput pk message ciphertext.salt) = none) :
    (S.realHandler pk sk challenge (.decaps ciphertext) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk message) := by
  simpa only [realHandler, Query.dispatch, hne, ↓reduceIte] using
    S.realDecaps_bad_eq_msgFailProb pk sk ciphertext message hs hdec hlookup

/-- The punctured real handler rejects its challenge ciphertext without changing the state. -/
@[simp] theorem realHandler_decaps_challenge
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    S.realHandler pk sk challenge (.decaps challenge) st = PMF.pure (none, st) := by
  simp [realHandler, Query.dispatch, StateT.pure_apply]

/-- A rejection-oracle query through the real handler cannot create a PKE correctness witness. -/
theorem realHandler_rejection_bad_eq_zero
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realHandler pk sk challenge (.rejection input) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} = 0 :=
  toOuterMeasure_notGood_eq_zero hs fun z hz _ hentry => by
    rwa [S.rejection_jointCache_eq input hz] at hentry

private theorem realDecaps_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    refine le_of_eq_of_le (toOuterMeasure_notGood_eq_zero hs fun z hz _ hentry => ?_) zero_le
    supp_cases hz [realDecaps, decapsWithJoint, hdec, StateT.map_apply] with ⟨x, hx, rfl⟩
    rwa [S.decapsKey_jointCache_eq ciphertext hx] at hentry
  | some message =>
    rw [S.realDecaps_bad_eq_realJoint_bad pk sk ciphertext message hdec]
    exact S.realJoint_bad_le pk sk (S.jointInput pk message ciphertext.salt) hs

private theorem realHandler_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realHandler pk sk challenge q st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      (Query.jointCost q : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) +
        (Query.decapsCost q : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  rcases q with input | input | ciphertext
  · simpa only [realHandler, Query.dispatch, Query.jointCost, Query.decapsCost, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, add_zero] using S.realJoint_bad_le pk sk input hs
  · simp [S.realHandler_rejection_bad_eq_zero pk sk challenge input hs]
  · rcases eq_or_ne ciphertext challenge with rfl | hc
    · simp [hs]
    · simpa only [realHandler, Query.dispatch, hc, ↓reduceIte, Query.jointCost,
        Query.decapsCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add] using
        S.realDecaps_bad_le pk sk ciphertext hs

end Scheme

/-! ### Query bounds, randomized adversaries, and main `CORR` hop theorems -/

/-- Separate source-shaped query bounds: at most `qRO` calls to the joint oracle and at most `qD`
calls to decapsulation. Rejection-oracle calls do not enter the `CORR` loss. -/
@[expose] def QueryBounds {JointPrefix M Salt RejectPrefix Sigma CT K R α : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α) (qRO qD : ℕ) : Prop :=
  OracleComp.IsCostBounded Query.jointCost program qRO ∧
    OracleComp.IsCostBounded Query.decapsCost program qD

/-- A randomized single-user, single-challenge adversary for the correctness hop. Its oracle
program is selected by private coins and the full public KEM challenge; in particular, the program
can depend on the public key, challenge ciphertext and challenge key, but not on `sk`. Query bounds
are stated separately and required for every random tape and challenge. -/
structure RandomizedAdversary
    (PK JointPrefix M Salt RejectPrefix Sigma CT K R : Type) where
  /-- Type of the adversary's private random tape. -/
  Coins : Type
  /-- Distribution of private random tapes. -/
  coins : ProbComp Coins
  /-- Deterministic oracle program after fixing the private tape and public challenge. -/
  run : Coins → KEM.Challenge PK (Ciphertext CT Salt) K → OracleComp
    (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) Bool

namespace RandomizedAdversary

variable {PK JointPrefix M Salt RejectPrefix Sigma CT K R : Type}

/-- Per-random-tape and per-challenge joint-oracle and decapsulation bounds. -/
@[expose] def QueryBounded
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (qRO qD : ℕ) : Prop :=
  ∀ coins challenge, QueryBounds (A.run coins challenge) qRO qD

end RandomizedAdversary

variable {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}

/-- **Fixed-key salted-FO `CORR` hop.** Suppose the real and simulated handlers agree until
`bad`, and from any good state each joint-oracle or decapsulation query creates `bad` with
probability at most `ε`. A program bounded by `qRO` joint queries and `qD` decapsulation queries
then has output laws within `(qRO + qD) * ε`, after any shared randomized postprocessing.

The cost of `Query.rejection` is zero in both channels, so a shared `J` fallback contributes no
correctness term. `Query.joint` has cost one even though its reply has two projections. -/
private theorem closeTo_run_corr {JointPrefix M Salt RejectPrefix Sigma CT K R State α β : Type}
    {first second : (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT State PMF (Response K R q)} {bad : State → Prop} {ε : ℝ≥0∞}
    (hident : OracleComp.IdenticalUntilBad first second bad)
    (hstep : ∀ q s, ¬bad s →
      (first q s).toOuterMeasure {x | bad x.2} ≤
        (Query.jointCost q : ℝ≥0∞) * ε + (Query.decapsCost q : ℝ≥0∞) * ε)
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α) {qRO qD : ℕ}
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

/-- **Concrete fixed-key salted-FO `CORR` hop.** The decrypt/re-encrypt real handler and the
secret-key-free keyless handler have output laws within `(qRO + qD)` times the fixed key pair's
worst-message decryption-failure probability. Private final caches are not observable. -/
theorem Scheme.closeTo_run_realHandler_simHandler
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A)
    {qRO qD : ℕ} (hbounds : QueryBounds program qRO qD) :
    CloseTo
      (((OracleComp.interpret (S.realHandler pk sk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst)
      (((OracleComp.interpret (S.simHandler pk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst)
      (((qRO + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) := by
  rw [← S.run_prefetchHandler_eq_simHandler pk sk challenge program]
  simpa only [PMF.bind_pure_comp] using
    closeTo_run_corr (S.identicalUntilBad_realHandler_prefetchHandler pk sk challenge)
      (fun q st hst => S.realHandler_bad_le pk sk challenge q (of_not_not hst))
      program hbounds (not_not.mpr (GoodCache.empty S pk sk)) (PMF.pure ∘ Prod.fst)

/-- Run a challenge-aware randomized adversary against the post-secret-seed-guessing real
handler. The adversary's coins are sampled before the common public challenge. -/
noncomputable def Scheme.randomizedRealHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.realHandler keys.1 keys.2 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- Run the same challenge-aware randomized adversary against the post-secret-seed-guessing
keyless handler, using the identical key, coin and challenge setup laws. -/
noncomputable def Scheme.randomizedSimHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.simHandler keys.1 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- **Concrete randomized-adversary salted-FO `CORR` hop.** For a randomized adversary that
receives the full public KEM challenge and has `qRO`/`qD` bounds for every tape and challenge, the
concrete real and keyless-handler games differ by at most `(qRO + qD) * δ` under
`ExplicitCoinPKE.DeltaCorrect δ`. Both games sample the same challenge law after key generation;
challenge construction is outside the counted handler queries and therefore adds no `+1`. -/
theorem Scheme.advantage_randomizedRealHandler_simHandler_le
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    {qRO qD : ℕ} (hbounds : A.QueryBounded qRO qD)
    {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) :
    (Game.advantage
      (S.randomizedRealHandlerGame challengeSetup A)
      (S.randomizedSimHandlerGame challengeSetup A) : ℝ) ≤
      ((qRO + qD : ℕ) : ℝ) * δ := by
  unfold randomizedRealHandlerGame randomizedSimHandlerGame
  exact S.pke.advantage_bind_keyGen_le
    (fun pk sk => (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup pk)).bind fun challenge =>
        ((OracleComp.interpret (S.realHandler pk sk challenge.1)
          (A.run coins ⟨pk, challenge.1, challenge.2⟩)).run {}).map Prod.fst)
    (fun pk _ => (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup pk)).bind fun challenge =>
        ((OracleComp.interpret (S.simHandler pk challenge.1)
          (A.run coins ⟨pk, challenge.1, challenge.2⟩)).run {}).map Prod.fst)
    (qRO + qD) (fun pk sk => CloseTo.bind_right _ fun coins _ =>
      CloseTo.bind_right _ fun challenge _ => S.closeTo_run_realHandler_simHandler pk sk
        challenge.1 _ (hbounds coins ⟨pk, challenge.1, challenge.2⟩)) hδ

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
