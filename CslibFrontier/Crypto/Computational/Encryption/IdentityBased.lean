/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Identity-based encryption and its semantic, private and selective security

An identity-based encryption scheme `IBE MPK MSK ID SK M C` has a setup algorithm drawing a
master public key and a master secret key, a key generation algorithm deriving a secret key for
an identity from the master secret key, encryption to an identity under the master public key,
and deterministic decryption with a secret key, where `none` is the source's `reject`
([BonehShoup2023], Section 15.6.1, Definition 15.8, p. 644). `IBE.Correct` is the correctness
requirement of that definition. The record is for one fixed scheme, as `PKE` and `FE` are.

The three security notions of [BonehShoup2023], Sections 15.6.1–15.6.2, are asymptotic and
word-level: they take a family `WordIBE Msg` of schemes whose identities, keys and ciphertexts are
bit words, and adversaries whose stages query the key oracle `ibeKeyOracle` through
`WordOracleComp Unit` with the efficiency predicate `IsOraclePPT`. Adversaries with a typed key
oracle need a typed oracle-PPT predicate, which is not yet in the library (#4894).

There is one experiment, `privateIBEGameOn`: experiment `bit` of Attack Game 15.6 (p. 646), in
which the adversary names two (identity, message) pairs and receives an encryption of the message
of pair `bit` to the identity of pair `bit`. The other two games are this experiment run on mapped
adversaries:

* Attack Game 15.5 (semantic security, pp. 645–646) is Attack Game 15.6 with `id₀ = id₁`, as the
  source says on p. 646. `IBEAdversaryOf.toPrivate` names the identity twice, and
  `privateIBEGameOn_toPrivate` shows that the result is literally Attack Game 15.5.
* Attack Game 15.7 (selective security, p. 647) has the adversary name its target identity before
  it sees the master public key. `SelectiveIBEAdversaryOf.toAdaptive` draws the target from the
  security parameter alone, and `eval_privateIBEGameOn_toAdaptive` shows that the law is that of
  Attack Game 15.7, with the target drawn before the setup.

Conventions of the experiment:

* The key oracle logs every identity it is asked, in both stages, and the experiment returns the
  adversary's guess only when neither challenge identity is in the log; otherwise it returns
  `false` in both experiments. This is how `FE.ssExperiment` enforces its restriction: a key query
  made before the encryption query cannot be refused when it is made. An adversary that obeys the
  source's restriction has the same advantage, so security in this sense implies the source's; the
  converse, an adversary that polices its own queries, is not formalized.
* The adversary makes exactly one encryption query, where the source says "at most one".
* The source's identity space and equal-length rule are the challenge-admissibility predicate
  `valid`; an inadmissible challenge gives `false` before any encryption, as in `cca2GameOn`.
* Identities are compared as words. A scheme family with a structured identity space puts
  membership into `valid` and must make sure that no key issued for a word outside the space
  decrypts a challenge: two words for one identity make such a scheme insecure in this game.
  Correctness is stated on the typed record, so a client states `IBE.Correct` for its scheme there.

`IBEPrivateOn.ibeSemanticOn` and `IBESemanticOn.ibeSelectiveOn` are the implications the source
states in words ("a special case", p. 646; "a weaker notion", p. 647). Each applies its hypothesis
to the mapped adversary, through the certificates `IBEAdversaryOf.IsPPT.toPrivate` and
`SelectiveIBEAdversaryOf.IsPPT.toAdaptive`.

Not formalized here: several encryption queries (Remark 15.12), the hashed-identity construction
of Theorem 15.5, chosen-ciphertext security (p. 648), identity-based encryption as functional
encryption (Example 15.2), and the constructions of Section 15.6.3.

## Main definitions

* `Cslib.Crypto.IBE`, `Cslib.Crypto.IBE.Correct`: the scheme and its correctness (Definition 15.8).
* `Cslib.Crypto.Encryption.WordIBE`: a family of schemes on bit words.
* `Cslib.Crypto.Encryption.PrivateIBEAdversaryOf`, `Cslib.Crypto.Encryption.IBEAdversaryOf`,
  `Cslib.Crypto.Encryption.SelectiveIBEAdversaryOf`: the adversaries of Attack Games 15.6, 15.5 and
  15.7, each with its `IsPPT` predicate.
* `Cslib.Crypto.Encryption.ibeKeyOracle`, `Cslib.Crypto.Encryption.privateIBEGameOn`: the logging
  key oracle and experiment `bit` of Attack Game 15.6.
* `Cslib.Crypto.Encryption.IBEAdversaryOf.toPrivate`,
  `Cslib.Crypto.Encryption.SelectiveIBEAdversaryOf.toAdaptive`: the adversary maps.
* `Cslib.Crypto.Encryption.IBEPrivateOn`, `Cslib.Crypto.Encryption.IBESemanticOn`,
  `Cslib.Crypto.Encryption.IBESelectiveOn`: Definitions 15.10, 15.9 and 15.11.

## Main results

* `Cslib.Crypto.Encryption.privateIBEGameOn_toPrivate`: the experiment on `A.toPrivate` is Attack
  Game 15.5.
* `Cslib.Crypto.Encryption.eval_privateIBEGameOn_toAdaptive`: the experiment on
  `A.toAdaptive.toPrivate` has the law of Attack Game 15.7.
* `Cslib.Crypto.Encryption.IBEAdversaryOf.IsPPT.toPrivate`,
  `Cslib.Crypto.Encryption.SelectiveIBEAdversaryOf.IsPPT.toAdaptive`: the maps preserve the
  efficiency predicates.
* `Cslib.Crypto.Encryption.IBEPrivateOn.ibeSemanticOn`: a private scheme is semantically secure.
* `Cslib.Crypto.Encryption.IBESemanticOn.ibeSelectiveOn`: a semantically secure scheme is
  selectively secure.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 15.6.1–15.6.2 (Definition 15.8, p. 644; Attack Games
  15.5–15.7 and Definitions 15.9–15.11, pp. 645–647).
-/

public section

namespace Cslib.Crypto

open Probability

/-- An identity-based encryption scheme ([BonehShoup2023], Section 15.6.1, Definition 15.8,
p. 644) with master public keys `MPK`, master secret keys `MSK`, identities `ID`, secret keys
`SK`, messages `M` and ciphertexts `C`. Decryption returns `none` for the source's `reject`. -/
structure IBE (MPK MSK ID SK M C : Type) where
  /-- Setup algorithm `S`: draw a master public key and a master secret key. -/
  setup : ProbComp (MPK × MSK)
  /-- Key generation algorithm `G`: derive a secret key for an identity from the master secret
  key. -/
  keyGen : MSK → ID → ProbComp SK
  /-- Encryption algorithm `E`: encrypt a message to an identity under the master public key. -/
  encrypt : MPK → ID → M → ProbComp C
  /-- Deterministic decryption algorithm `D`, with `none` for `reject`. -/
  decrypt : SK → C → Option M

namespace IBE

variable {MPK MSK ID SK M C : Type}

/-- Correctness of an identity-based encryption scheme ([BonehShoup2023], Section 15.6.1,
Definition 15.8, p. 644): for every supported master key pair, every identity `id` and every
message `m`, decrypting any supported encryption of `m` to `id` with any supported secret key for
`id` gives `some m`. -/
@[expose]
def Correct (E : IBE MPK MSK ID SK M C) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.setup).support, ∀ id m,
    ∀ sk ∈ (ProbComp.eval (E.keyGen keys.2 id)).support,
      ∀ c ∈ (ProbComp.eval (E.encrypt keys.1 id m)).support, E.decrypt sk c = some m

end IBE

namespace Encryption

open Turing.MultiTapeTM

/-- A family of identity-based encryption schemes indexed by the security parameter, whose master
keys, identities, secret keys and ciphertexts are bit words and whose messages have type `Msg`. -/
abbrev WordIBE (Msg : Type) : Type :=
  ℕ → IBE (List Bool) (List Bool) (List Bool) (List Bool) Msg (List Bool)

/-- Output `((id, m₀, m₁), state)` of the first stage of a semantic-security adversary: the
identity word, the two messages under `encMsg`, then the saved state word. The triple, the
identity and `m₀` are framed. -/
abbrev encIBEChoice {Msg : Type} (encMsg : Msg ↪ List Bool) :
    (List Bool × Msg × Msg) × List Bool ↪ List Bool :=
  encPair (encPair encBits (encPair encMsg encMsg)) encBits

/-- Output `(((id₀, m₀), (id₁, m₁)), state)` of the first stage of a private-IBE adversary: the two
(identity word, message) pairs, then the saved state word. The two pairs together, the first pair
and both identities are framed; the second pair is not. -/
abbrev encIBEPairChoice {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ((List Bool × Msg) × (List Bool × Msg)) × List Bool ↪ List Bool :=
  encPair (encPair (encPair encBits encMsg) (encPair encBits encMsg)) encBits

/-- An adversary in Attack Game 15.6 (private IBE, [BonehShoup2023], Section 15.6.2, p. 646). Both
stages query the key oracle: a query is an identity word and its reply is a secret-key word. -/
structure PrivateIBEAdversaryOf (Msg : Type) where
  /-- Given the security parameter and the master public key, make key queries and choose the
  two pairs `((id₀, m₀), (id₁, m₁))` and a saved state. -/
  choose : ℕ → List Bool →
    WordOracleComp Unit (((List Bool × Msg) × (List Bool × Msg)) × List Bool)
  /-- Given the security parameter, the saved state and the challenge ciphertext, make key
  queries and output a guess. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a private-IBE adversary. -/
structure PrivateIBEAdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : PrivateIBEAdversaryOf Msg) : Prop where
  /-- The first stage is uniform strict oracle PPT on `(n, mpk)`. -/
  choose : IsOraclePPT (Operation := Unit) (encIBEPairChoice encMsg) adversary.choose
  /-- The second stage is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) encGuessInput encBool
    (fun ⟨n, state, ct⟩ => adversary.guess n state ct)

/-- An adversary in Attack Game 15.5 (semantic security, [BonehShoup2023], Section 15.6.1,
pp. 645–646): it chooses the challenge identity adaptively, after its key queries. -/
structure IBEAdversaryOf (Msg : Type) where
  /-- Given the security parameter and the master public key, make key queries and choose the
  challenge `(id, m₀, m₁)` and a saved state. -/
  choose : ℕ → List Bool → WordOracleComp Unit ((List Bool × Msg × Msg) × List Bool)
  /-- Given the security parameter, the saved state and the challenge ciphertext, make key
  queries and output a guess. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a semantic-security adversary. -/
structure IBEAdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : IBEAdversaryOf Msg) : Prop where
  /-- The first stage is uniform strict oracle PPT on `(n, mpk)`. -/
  choose : IsOraclePPT (Operation := Unit) (encIBEChoice encMsg) adversary.choose
  /-- The second stage is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) encGuessInput encBool
    (fun ⟨n, state, ct⟩ => adversary.guess n state ct)

/-- An adversary in Attack Game 15.7 (selective security, [BonehShoup2023], Section 15.6.2,
p. 647): it names its target identity from the security parameter alone, before it receives the
master public key. -/
structure SelectiveIBEAdversaryOf (Msg : Type) where
  /-- Given the security parameter only, choose the target identity and a saved state. -/
  target : ℕ → ProbComp (List Bool × List Bool)
  /-- Given the security parameter, the saved state and the master public key, make key queries
  and choose the two messages and a new saved state. -/
  choose : ℕ → List Bool → List Bool → WordOracleComp Unit ((Msg × Msg) × List Bool)
  /-- Given the security parameter, the saved state and the challenge ciphertext, make key
  queries and output a guess. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict (oracle) PPT admissibility of the three stages of a selective adversary. -/
structure SelectiveIBEAdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : SelectiveIBEAdversaryOf Msg) : Prop where
  /-- The target stage is uniform strict PPT on `n`. -/
  target : IsPPTOn encUnary (encPair encBits encBits) adversary.target
  /-- The message stage is uniform strict oracle PPT on `(n, state, mpk)`. -/
  choose : IsOraclePPTOn (Operation := Unit) (encPair encUnary (encPair encBits encBits))
    (encChoiceOut encMsg) (fun ⟨n, state, mpk⟩ => adversary.choose n state mpk)
  /-- The guessing stage is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) encGuessInput encBool
    (fun ⟨n, state, ct⟩ => adversary.guess n state ct)

/-- The key oracle of [BonehShoup2023], Attack Game 15.5: answer the identity word `request.2`
with a fresh secret key from `(E n).keyGen msk`, and add the identity to the log of queried
identities. It is the answer-and-log oracle `SignatureScheme.signingOracleOf` at `(E n).keyGen`. -/
@[expose]
def ibeKeyOracle {Msg : Type} (E : WordIBE Msg) (n : ℕ) (msk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  SignatureScheme.signingOracleOf (E n).keyGen msk request

@[simp]
theorem run_ibeKeyOracle {Msg : Type} (E : WordIBE Msg) (n : ℕ) (msk : List Bool)
    (request : Unit × List Bool) (queried : List (List Bool)) :
    (ibeKeyOracle E n msk request).run queried = (do
      let sk ← (E n).keyGen msk request.2
      return (sk, request.2 :: queried)) := rfl

/-- Experiment `bit` of Attack Game 15.6 (private IBE, [BonehShoup2023], Section 15.6.2, p. 646)
with challenge-admissibility predicate `valid`: draw `(mpk, msk)`; run the first stage on `mpk`
against the logging key oracle, from the empty log; if `valid n mpk (id₀, m₀) (id₁, m₁)`, encrypt
the message of pair `bit` to the identity of pair `bit`, run the second stage on the ciphertext
with the same log, and return the guess when neither `id₀` nor `id₁` was queried, and `false`
otherwise; if the challenge is inadmissible, return `false`.

A scheme family with a structured identity space states membership in `valid`; since identities
are compared as words, no key issued for a word outside the space may decrypt a challenge. -/
@[expose]
noncomputable def privateIBEGameOn {Msg : Type}
    (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (E : WordIBE Msg) (adversary : PrivateIBEAdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp Bool := do
  let keys ← (E n).setup
  let out₁ ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (ibeKeyOracle E n keys.2))
    (adversary.choose n keys.1)).run []
  match out₁.1 with
  | (((id₀, m₀), (id₁, m₁)), state) =>
    if valid n keys.1 (id₀, m₀) (id₁, m₁) then
      let ct ← (E n).encrypt keys.1 (if bit then id₁ else id₀) (if bit then m₁ else m₀)
      let out₂ ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (ibeKeyOracle E n keys.2))
        (adversary.guess n state ct)).run out₁.2
      return out₂.1 && !(out₂.2.contains id₀) && !(out₂.2.contains id₁)
    else
      return false

/-- A semantic-security adversary as a private-IBE adversary that names its challenge identity in
both pairs ([BonehShoup2023], p. 646: Attack Game 15.5 is Attack Game 15.6 with `id₀ = id₁`). -/
@[expose]
def IBEAdversaryOf.toPrivate {Msg : Type} (adversary : IBEAdversaryOf Msg) :
    PrivateIBEAdversaryOf Msg where
  choose n mpk := (fun c => match c with
    | ((id, m₀, m₁), state) => (((id, m₀), (id, m₁)), state)) <$> adversary.choose n mpk
  guess := adversary.guess

/-- A selective adversary as an adaptive one: its first stage draws the target identity from the
security parameter alone, without looking at the master public key, and then chooses the
messages. -/
@[expose]
def SelectiveIBEAdversaryOf.toAdaptive {Msg : Type} (adversary : SelectiveIBEAdversaryOf Msg) :
    IBEAdversaryOf Msg where
  choose n mpk := do
    let t ← ProbOracleComp.sample (adversary.target n)
    let c ← adversary.choose n t.2 mpk
    return ((t.1, c.1), c.2)
  guess := adversary.guess

/-- The experiment on `adversary.toPrivate` is Attack Game 15.5 ([BonehShoup2023], Section 15.6.1,
pp. 645–646): one challenge identity, an encryption of `m_bit` to it, and a final check that the
identity was not queried. -/
theorem privateIBEGameOn_toPrivate {Msg : Type}
    (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (E : WordIBE Msg) (adversary : IBEAdversaryOf Msg) (bit : Bool) (n : ℕ) :
    privateIBEGameOn valid E adversary.toPrivate bit n = (do
      let keys ← (E n).setup
      let out₁ ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (ibeKeyOracle E n keys.2)) (adversary.choose n keys.1)).run []
      match out₁.1 with
      | ((ident, m₀, m₁), state) =>
        if valid n keys.1 (ident, m₀) (ident, m₁) then do
          let ct ← (E n).encrypt keys.1 ident (if bit then m₁ else m₀)
          let out₂ ← (OracleComp.interpret
            (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
              (ibeKeyOracle E n keys.2)) (adversary.guess n state ct)).run out₁.2
          return out₂.1 && !(out₂.2.contains ident)
        else
          return false) := by
  simp only [privateIBEGameOn, IBEAdversaryOf.toPrivate, OracleComp.run_interpret_map,
    bind_map_left]
  refine congrArg _ (funext fun keys => congrArg _ (funext fun out₁ => ?_))
  obtain ⟨⟨⟨ident, m₀, m₁⟩, state⟩, log⟩ := out₁
  simp only [Prod.map, id, ite_self]
  split
  · refine congrArg _ (funext fun ct => congrArg _ (funext fun out₂ => ?_))
    simp
  · rfl

/-- The experiment on `adversary.toAdaptive.toPrivate` has the law of Attack Game 15.7
([BonehShoup2023], Section 15.6.2, p. 647): the target identity is drawn first, from the security
parameter alone, then the master keys; the message stage runs on the master public key. -/
theorem eval_privateIBEGameOn_toAdaptive {Msg : Type}
    (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (E : WordIBE Msg) (adversary : SelectiveIBEAdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn valid E adversary.toAdaptive.toPrivate bit n) =
      ProbComp.eval (do
        let t ← adversary.target n
        let keys ← (E n).setup
        let out₁ ← (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (ibeKeyOracle E n keys.2)) (adversary.choose n t.2 keys.1)).run []
        match out₁.1 with
        | ((m₀, m₁), state) =>
          if valid n keys.1 (t.1, m₀) (t.1, m₁) then do
            let ct ← (E n).encrypt keys.1 t.1 (if bit then m₁ else m₀)
            let out₂ ← (OracleComp.interpret
              (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
                (ibeKeyOracle E n keys.2)) (adversary.guess n state ct)).run out₁.2
            return out₂.1 && !(out₂.2.contains t.1)
          else
            return false) := by
  rw [privateIBEGameOn_toPrivate]
  simp only [SelectiveIBEAdversaryOf.toAdaptive, OracleComp.run_interpret_bind,
    ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift, ProbComp.interpret_unifFin,
    OracleComp.run_interpret_pure, bind_assoc, bind_map_left, pure_bind, ProbComp.eval_bind]
  rw [PMF.bind_comm]

/-- `toPrivate` preserves the efficiency predicate: its first stage reshapes the output of the
adversary's first stage by a polynomial-time map. -/
theorem IBEAdversaryOf.IsPPT.toPrivate {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : IBEAdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    adversary.toPrivate.IsPPT encMsg where
  choose := by
    have hpost : ComputableInPolyTime
        (fun c : (List Bool × Msg × Msg) × List Bool => match c with
          | ((id, m₀, m₁), state) => (((id, m₀), (id, m₁)), state))
        (encIBEChoice encMsg) (encIBEPairChoice encMsg) := by
      have h : (fun c : (List Bool × Msg × Msg) × List Bool => match c with
          | ((id, m₀, m₁), state) => (((id, m₀), (id, m₁)), state)) =
          fun c => (((c.1.1, c.1.2.1), (c.1.1, c.1.2.2)), c.2) := rfl
      rw [h]
      fun_prop
    exact (hA.choose.on.map' hpost).isOraclePPT
  guess := hA.guess

/-- `toAdaptive` preserves the efficiency predicate: its first stage samples the target stage and
runs the message stage on the target state and the master public key. -/
theorem SelectiveIBEAdversaryOf.IsPPT.toAdaptive {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : SelectiveIBEAdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    adversary.toAdaptive.IsPPT encMsg where
  choose := by
    have htarget : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits)
        (encPair encBits encBits)
        (fun x : ℕ × List Bool => ProbOracleComp.sample (adversary.target x.1)) :=
      (hA.target.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn
    have hchoose : IsOraclePPTOn (Operation := Unit)
        (encPair (encPair encUnary encBits) (encPair encBits encBits)) (encChoiceOut encMsg)
        (fun p : (ℕ × List Bool) × (List Bool × List Bool) =>
          adversary.choose p.1.1 p.2.2 p.1.2) :=
      hA.choose.preprocess'
        (prepare := fun p : (ℕ × List Bool) × (List Bool × List Bool) => (p.1.1, p.2.2, p.1.2))
        (by fun_prop)
    have hpost : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × (List Bool × List Bool)) × ((Msg × Msg) × List Bool) =>
          ((q.1.2.1, q.2.1), q.2.2))
        (encPair (encPair (encPair encUnary encBits) (encPair encBits encBits))
          (encChoiceOut encMsg)) (encIBEChoice encMsg) := by
      fun_prop
    exact (htarget.bind_with (hchoose.bind_with hpost.isOraclePPTOn)).isOraclePPT
  guess := hA.guess

/-- Semantically secure and private identity-based encryption ([BonehShoup2023], Section 15.6.2,
Attack Game 15.6 and Definition 15.10, p. 646) for a scheme family `E` with challenge-admissibility
predicate `valid`: the two experiments of `privateIBEGameOn` are indistinguishable for every
uniform strict oracle PPT private-IBE adversary. -/
@[expose]
def IBEPrivateOn {Msg : Type} (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (encMsg : Msg ↪ List Bool) (E : WordIBE Msg) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (privateIBEGameOn valid E adversary false n))
    (fun adversary n => ProbComp.eval (privateIBEGameOn valid E adversary true n))
    (PrivateIBEAdversaryOf.IsPPT encMsg)

/-- Semantically secure (adaptively secure) identity-based encryption ([BonehShoup2023],
Section 15.6.1, Attack Game 15.5 and Definition 15.9, pp. 645–646): the experiments of
`privateIBEGameOn` on `adversary.toPrivate`, which are Attack Game 15.5
(`privateIBEGameOn_toPrivate`), are indistinguishable for every uniform strict oracle PPT
semantic-security adversary. -/
@[expose]
def IBESemanticOn {Msg : Type}
    (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (encMsg : Msg ↪ List Bool) (E : WordIBE Msg) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (privateIBEGameOn valid E (IBEAdversaryOf.toPrivate adversary) false n))
    (fun adversary n =>
      ProbComp.eval (privateIBEGameOn valid E (IBEAdversaryOf.toPrivate adversary) true n))
    (IBEAdversaryOf.IsPPT encMsg)

/-- Selectively secure identity-based encryption ([BonehShoup2023], Section 15.6.2, Attack
Game 15.7 and Definition 15.11, p. 647): the experiments of `privateIBEGameOn` on
`adversary.toAdaptive.toPrivate`, which have the laws of Attack Game 15.7
(`eval_privateIBEGameOn_toAdaptive`), are indistinguishable for every uniform strict (oracle) PPT
selective adversary. -/
@[expose]
def IBESelectiveOn {Msg : Type}
    (valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool)
    (encMsg : Msg ↪ List Bool) (E : WordIBE Msg) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (privateIBEGameOn valid E
      (SelectiveIBEAdversaryOf.toAdaptive adversary).toPrivate false n))
    (fun adversary n => ProbComp.eval (privateIBEGameOn valid E
      (SelectiveIBEAdversaryOf.toAdaptive adversary).toPrivate true n))
    (SelectiveIBEAdversaryOf.IsPPT encMsg)

/-- **A private identity-based encryption scheme is semantically secure** ([BonehShoup2023],
Section 15.6.2, p. 646: Attack Game 15.5 is the special case `id₀ = id₁` of Attack Game 15.6). -/
theorem IBEPrivateOn.ibeSemanticOn {Msg : Type}
    {valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool}
    {encMsg : Msg ↪ List Bool} {E : WordIBE Msg} (h : IBEPrivateOn valid encMsg E) :
    IBESemanticOn valid encMsg E :=
  fun adversary hA => h adversary.toPrivate hA.toPrivate

/-- **A semantically secure identity-based encryption scheme is selectively secure**
([BonehShoup2023], Section 15.6.2, p. 647: selective security is "a weaker notion"). -/
theorem IBESemanticOn.ibeSelectiveOn {Msg : Type}
    {valid : ℕ → List Bool → List Bool × Msg → List Bool × Msg → Bool}
    {encMsg : Msg ↪ List Bool} {E : WordIBE Msg} (h : IBESemanticOn valid encMsg E) :
    IBESelectiveOn valid encMsg E :=
  fun adversary hA => h adversary.toAdaptive hA.toAdaptive

end Encryption

end Cslib.Crypto
