/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Multi
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.Encryption.DecryptionBound
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Iteration.Chain
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Probability.PMF.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.Negligible

/-!
# Fully adaptive interleaved-query multi-challenge CCA security (Attack Game 12.1)

`Cslib.Crypto.Encryption.CCA2AdversaryOf` and `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf` in
`CslibFrontier.Crypto.Computational.Encryption.CCA` formalize the single-challenge (**1CCA**,
Definition 12.2) and two-phase batch-challenge (**Phased Multi-CCA2**) chosen-ciphertext security
experiments. In full generality, [Boneh and Shoup, Section 12.1, Attack Game 12.1, Definition 12.1,
and Theorem 12.1, printed pp. 467–469][BonehShoup2023] (see also [Katz and Lindell, Section
12.2][KatzLindell2020]) allow the adversary to **adaptively interleave** encryption (challenge)
queries and decryption queries in arbitrary order:

* The challenger generates `(pk, sk) ← keyGen n`, fixes the secret challenge bit `bit : Bool`, and
  initializes the forbidden challenge-ciphertext list `S = []`.
* In each adaptive round, the adversary (given `pk`, its saved state, and the previous oracle
  response, and with adaptive access to the current decryption oracle rejecting ciphertexts in `S`)
  submits a combined query `q : CCAQuery Msg (List Bool)` to `interleavedCcaOracle`:
  - **Encryption / challenge query** (`.challenge m₀ m₁`): if `valid n pk m₀ m₁` holds, the
    challenger encrypts `if bit then m₁ else m₀` (`ct ← encrypt n pk (if bit then m₁ else m₀)`),
    prepends `ct` to the forbidden set `S`, and returns `Sum.inl (some ct)` (encoded as
    `encOption encBits (some ct) = true :: ct`); otherwise it returns `Sum.inl none` (`[]`) with `S`
    unchanged.
  - **Decryption query** (`.decrypt c`): if `c ∈ S` (where `S` is the list of challenge ciphertexts
    produced *so far*), the challenger rejects with `Sum.inr none` (`[]`); otherwise it returns
    `Sum.inr (decrypt n sk c)` (encoded as `encOption encOut (decrypt n sk c)`) with `S` unchanged.
    Crucially, a ciphertext `c` queried to `.decrypt c` *before* `c` happens to be produced by a
    later `.challenge` query is decrypted normally, whereas any `.decrypt c` query *after* `c` was
    returned by `.challenge` is rejected.
* After `adversary.numRounds n` adaptive rounds, the adversary runs a final guessing stage `finish`
  (with access to the decryption oracle rejecting `S`) and outputs a bit `Bool`.

## Main definitions

* `Cslib.Crypto.Encryption.CCAQuery`, `Cslib.Crypto.Encryption.CCAResponse`,
  `Cslib.Crypto.Encryption.encCCAQuery`, `Cslib.Crypto.Encryption.encodeCCAResponseWord`:
  sum-like query and response types for the combined encryption-and-decryption CCA oracle, the
  injective bit-string encoding of queries, and the bit-word encoding of response payloads, which
  drops the `Sum` tag and is not injective.
* `Cslib.Crypto.Encryption.interleavedCcaOracle`,
  `Cslib.Crypto.Encryption.interleavedCcaWordOracle`: stateful interleaved CCA oracle tracking the
  list `S : List (List Bool)` of challenge ciphertexts generated so far.
* `Cslib.Crypto.Encryption.InterleavedCCA2AdversaryOf`,
  `Cslib.Crypto.Encryption.InterleavedCCA2Adversary`,
  `Cslib.Crypto.Encryption.WordInterleavedCCA2Adversary`,
  `Cslib.Crypto.Encryption.InterleavedCCA2AdversaryOf.IsPPT`,
  `Cslib.Crypto.Encryption.InterleavedCCA2AdversaryOf.IsQueryBounded`:
  adaptive interleaved-query multi-challenge CCA adversaries, uniform strict PPT certificates, and
  per-stage query bounds.
* `Cslib.Crypto.Encryption.interleavedCca2Exp`, `Cslib.Crypto.Encryption.interleavedCca2GameOn`,
  `Cslib.Crypto.Encryption.interleavedCca2Game`: the interleaved-query multi-challenge CCA
  experiment and `Game`.
* `Cslib.Crypto.Encryption.INDCCA2InterleavedOn`, `Cslib.Crypto.Encryption.INDCCA2InterleavedOf`,
  `Cslib.Crypto.Encryption.INDCCA2Interleaved`, `Cslib.Crypto.Encryption.WordINDCCA2Interleaved`:
  interleaved multi-challenge CCA security predicates.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.toInterleaved`,
  `Cslib.Crypto.Encryption.interleavedHybridGameOn`,
  `Cslib.Crypto.Encryption.interleavedToSingleAt`,
  `Cslib.Crypto.Encryption.interleavedToSingle`:
  the direct embedding of single-challenge 1CCA adversaries into 1-round interleaved adversaries,
  the `split`-hybrid game, and the Boneh–Shoup Theorem 12.1 hybrid reduction to single-challenge
  1CCA.

## Main results

* `Cslib.Crypto.Encryption.eval_interleavedCca2GameOn_toInterleaved`,
  `Cslib.Crypto.Encryption.INDCCA2InterleavedOn.indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2InterleavedOn.indcca2MultiOn`:
  interleaved multi-challenge CCA security implies single-challenge 1CCA security (by embedding
  1CCA adversaries as 1-round interleaved adversaries) and, whenever `valid`, `keyGen`, `encrypt`,
  and `decrypt` are polynomial-time / strict PPT, phased batch-challenge multi-challenge CCA
  security (through 1CCA security and the hybrid reduction `INDCCA2On.indcca2MultiOn`).
* `Cslib.Crypto.Encryption.interleavedHybridGameOn_step_gap`,
  `Cslib.Crypto.Encryption.interleavedCca2GameOn_gap`,
  `Cslib.Crypto.Encryption.advantage_interleavedCca2GameOn`,
  `Cslib.Crypto.Encryption.INDCCA2On.indcca2InterleavedOn`,
  `Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2On`,
  `Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2MultiOn`:
  single-challenge 1CCA security implies fully adaptive interleaved-query multi-challenge CCA
  security ([BonehShoup2023], Theorem 12.1), with exact hybrid advantage scaling `dyadicSize (Q n)`.

The Multiplicative Cramer–Shoup instance
`Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup` is in
`CslibFrontier.Crypto.Computational.CramerShoup.Interleaved`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2, and
  Theorem 12.1, printed pp. 467–469) and Section 12.5 (Theorem 12.9, printed pp. 490–491).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 12.2.
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

attribute [local fun_prop]
  ComputableInPolyTime.cons'
  ComputableInPolyTime.unary_lt'
  ComputableInPolyTime.bool_and'

/-! ### Combined encryption-and-decryption CCA queries and responses -/

/-- A single query to the combined interleaved CCA challenger ([BonehShoup2023], Section 12.1,
Attack Game 12.1, printed pp. 467–468): either an encryption / challenge query
`.challenge m₀ m₁` on a pair of candidate plaintexts, or a decryption query `.decrypt c` on a
candidate ciphertext. -/
inductive CCAQuery (Plaintext Ciphertext : Type) : Type
  /-- Submit a challenge plaintext pair `(m₀, m₁)` to the left-or-right encryption oracle. -/
  | challenge (m₀ m₁ : Plaintext)
  /-- Submit a candidate ciphertext `c` to the decryption oracle. -/
  | decrypt (c : Ciphertext)
  deriving DecidableEq, Repr

/-- Response from the combined interleaved CCA challenger: `Sum.inl (some c*)` (or `Sum.inl none`
on an inadmissible challenge pair) for an encryption query, and `Sum.inr (some m)` (or
`Sum.inr none` on decryption rejection or a forbidden challenge ciphertext `c ∈ S`) for a
decryption query. -/
abbrev CCAResponse (Plaintext Ciphertext : Type) : Type :=
  Option Ciphertext ⊕ Option Plaintext

/-- Represent a `CCAQuery Msg (List Bool)` as `Option (Msg × Msg) × List Bool`, mapping
`.challenge m₀ m₁` to `(some (m₀, m₁), [])` and `.decrypt c` to `(none, c)`. -/
@[expose] def CCAQuery.toOptionPair {Msg : Type} :
    CCAQuery Msg (List Bool) → Option (Msg × Msg) × List Bool
  | .challenge m₀ m₁ => (some (m₀, m₁), [])
  | .decrypt c => (none, c)

/-- Test whether a `CCAQuery` is an encryption / challenge query. -/
@[expose] def CCAQuery.isChallenge {Plaintext Ciphertext : Type} :
    CCAQuery Plaintext Ciphertext → Bool
  | .challenge _ _ => true
  | .decrypt _ => false

/-- Extract the challenge message pair `(m₀, m₁)` from `.challenge m₀ m₁`, or `(default, default)`
on `.decrypt _`. -/
@[expose] def CCAQuery.challengePair {Plaintext Ciphertext : Type} [Inhabited Plaintext] :
    CCAQuery Plaintext Ciphertext → Plaintext × Plaintext
  | .challenge m₀ m₁ => (m₀, m₁)
  | .decrypt _ => (default, default)

/-- Extract the ciphertext `c` from `.decrypt c`, or `[]` on `.challenge _ _`. -/
@[expose] def CCAQuery.decryptCiphertext {Plaintext : Type} :
    CCAQuery Plaintext (List Bool) → List Bool
  | .challenge _ _ => []
  | .decrypt c => c

@[simp] theorem CCAQuery.isChallenge_challenge {Plaintext Ciphertext : Type}
    (m₀ m₁ : Plaintext) :
    (CCAQuery.challenge m₀ m₁ : CCAQuery Plaintext Ciphertext).isChallenge = true := rfl

@[simp] theorem CCAQuery.isChallenge_decrypt {Plaintext Ciphertext : Type}
    (c : Ciphertext) :
    (CCAQuery.decrypt c : CCAQuery Plaintext Ciphertext).isChallenge = false := rfl

@[simp] theorem CCAQuery.challengePair_challenge {Plaintext Ciphertext : Type}
    [Inhabited Plaintext] (m₀ m₁ : Plaintext) :
    (CCAQuery.challenge m₀ m₁ : CCAQuery Plaintext Ciphertext).challengePair = (m₀, m₁) := rfl

@[simp] theorem CCAQuery.challengePair_decrypt {Plaintext Ciphertext : Type}
    [Inhabited Plaintext] (c : Ciphertext) :
    (CCAQuery.decrypt c : CCAQuery Plaintext Ciphertext).challengePair = (default, default) := rfl

@[simp] theorem CCAQuery.decryptCiphertext_challenge {Plaintext : Type}
    (m₀ m₁ : Plaintext) :
    (CCAQuery.challenge m₀ m₁ : CCAQuery Plaintext (List Bool)).decryptCiphertext = [] := rfl

@[simp] theorem CCAQuery.decryptCiphertext_decrypt {Plaintext : Type}
    (c : List Bool) :
    (CCAQuery.decrypt c : CCAQuery Plaintext (List Bool)).decryptCiphertext = c := rfl

/-- Injective bit-string encoding of `CCAQuery Msg (List Bool)` via `CCAQuery.toOptionPair` and
`encPair (encOption (encPair encMsg encMsg)) encBits`. -/
@[expose] def encCCAQuery {Msg : Type} (encMsg : Msg ↪ List Bool) :
    CCAQuery Msg (List Bool) ↪ List Bool where
  toFun q := encPair (encOption (encPair encMsg encMsg)) encBits q.toOptionPair
  inj' := by
    intro q₁ q₂ h
    have hinj := (encPair (encOption (encPair encMsg encMsg)) encBits).inj' h
    cases q₁ <;> cases q₂ <;>
      simp only [CCAQuery.toOptionPair, Prod.mk.injEq, Option.some.injEq, reduceCtorEq] at hinj
    · obtain ⟨⟨rfl, rfl⟩, _⟩ := hinj
      rfl
    · exact False.elim hinj.1
    · exact False.elim hinj.1
    · obtain ⟨_, rfl⟩ := hinj
      rfl

@[simp] theorem encCCAQuery_apply {Msg : Type} (encMsg : Msg ↪ List Bool)
    (q : CCAQuery Msg (List Bool)) :
    encCCAQuery encMsg q =
      encPair (encOption (encPair encMsg encMsg)) encBits q.toOptionPair := rfl

/-- Encode the payload of a `CCAResponse Out (List Bool)` as an optional bit word
(`encOption encBits` on encryption responses and `encOption encOut` on decryption responses). -/
@[expose] def encodeCCAResponseWord {Out : Type} (encOut : Out ↪ List Bool) :
    CCAResponse Out (List Bool) → List Bool
  | Sum.inl ctOpt => encOption encBits ctOpt
  | Sum.inr outOpt => encOption encOut outOpt

@[simp] theorem encodeCCAResponseWord_inl_some {Out : Type} (encOut : Out ↪ List Bool)
    (ct : List Bool) :
    encodeCCAResponseWord encOut (Sum.inl (some ct)) = true :: ct := rfl

@[simp] theorem encodeCCAResponseWord_inl_none {Out : Type} (encOut : Out ↪ List Bool) :
    encodeCCAResponseWord encOut (Sum.inl none) = [] := rfl

@[simp] theorem encodeCCAResponseWord_inr {Out : Type} (encOut : Out ↪ List Bool)
    (outOpt : Option Out) :
    encodeCCAResponseWord encOut (Sum.inr outOpt) = encOption encOut outOpt := rfl

/-- `CCAQuery.toOptionPair` is computable in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toOptionPair {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime (CCAQuery.toOptionPair (Msg := Msg))
      (encCCAQuery encMsg) (encPair (encOption (encPair encMsg encMsg)) encBits) :=
  .of_eq fun _ => rfl

/-- Constructing `.challenge m₀ m₁` from `(m₀, m₁)` is computable in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ccaQuery_challenge {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime
      (fun p : Msg × Msg => (CCAQuery.challenge p.1 p.2 : CCAQuery Msg (List Bool)))
      (encPair encMsg encMsg) (encCCAQuery encMsg) :=
  ((ComputableInPolyTime.optionSome (encPair encMsg encMsg)).prod
    (ComputableInPolyTime.const ([] : List Bool))).of_enc_eq fun _ => rfl

/-- Constructing `.decrypt c` from `c : List Bool` is computable in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ccaQuery_decrypt {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime
      (CCAQuery.decrypt (Plaintext := Msg) (Ciphertext := List Bool))
      encBits (encCCAQuery encMsg) :=
  ((ComputableInPolyTime.const (none : Option (Msg × Msg))).prod
    ComputableInPolyTime.id').of_enc_eq fun _ => rfl

/-- `CCAQuery.isChallenge` is computable in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isChallenge {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime (CCAQuery.isChallenge (Plaintext := Msg) (Ciphertext := List Bool))
      (encCCAQuery encMsg) encBool :=
  (((computableInPolyTime_toOptionPair encMsg).fst').optionIsSome).of_enc_eq
    fun q => by cases q <;> rfl

/-- `CCAQuery.challengePair` is computable in plain polynomial time when `[Inhabited Msg]`. -/
@[fun_prop]
theorem computableInPolyTime_challengePair {Msg : Type} [Inhabited Msg]
    (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime
      (CCAQuery.challengePair (Plaintext := Msg) (Ciphertext := List Bool))
      (encCCAQuery encMsg) (encPair encMsg encMsg) :=
  (((computableInPolyTime_toOptionPair encMsg).fst').optionGetDWithInput
    (ComputableInPolyTime.const (default, default))).of_enc_eq fun q => by cases q <;> rfl

/-- `CCAQuery.decryptCiphertext` is computable in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_decryptCiphertext {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ComputableInPolyTime (CCAQuery.decryptCiphertext (Plaintext := Msg))
      (encCCAQuery encMsg) encBits :=
  ((computableInPolyTime_toOptionPair encMsg).snd').of_enc_eq fun q => by cases q <;> rfl

/-! ### Stateful interleaved CCA oracle (`interleavedCcaOracle`) -/

/-- On the empty challenge-ciphertext list `[]`, `cca2MultiPhase2Oracle` coincides with the
unrestricted Phase 1 decryption oracle `cca2Phase1Oracle`. -/
@[simp] theorem cca2MultiPhase2Oracle_nil {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) :
    cca2MultiPhase2Oracle encOut decrypt n sk [] =
      cca2Phase1Oracle encOut decrypt n sk := by
  funext request s
  simp only [cca2MultiPhase2Oracle, cca2Phase1Oracle, List.not_mem_nil, decide_false,
    Bool.false_eq_true, ↓reduceIte]

/-- Stateful combined encryption-and-decryption oracle for the interleaved multi-challenge CCA
experiment ([BonehShoup2023], Section 12.1, Attack Game 12.1, printed pp. 467–468), tracking the
list `S : List (List Bool)` of challenge ciphertexts produced *so far*:
* On `.challenge m₀ m₁`: if `valid n pk m₀ m₁` holds, encrypt `if bit then m₁ else m₀` under `pk`,
  prepend the resulting challenge ciphertext `ct` to `S`, and return `Sum.inl (some ct)`;
  otherwise return `Sum.inl none` with `S` unchanged.
* On `.decrypt c`: if `c ∈ S` (among challenge ciphertexts generated so far), reject with
  `Sum.inr none` and leave `S` unchanged; otherwise return `Sum.inr (decrypt n sk c)` with `S`
  unchanged. -/
@[expose] noncomputable def interleavedCcaOracle {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool)
    (query : CCAQuery Msg (List Bool)) :
    StateT (List (List Bool)) ProbComp (CCAResponse Out (List Bool)) := fun S =>
  match query with
  | .challenge m₀ m₁ =>
    if valid n pk m₀ m₁ then do
      let ct ← encrypt n pk (if bit then m₁ else m₀)
      return (Sum.inl (some ct), ct :: S)
    else
      return (Sum.inl none, S)
  | .decrypt c =>
    if decide (c ∈ S) then
      return (Sum.inr none, S)
    else
      return (Sum.inr (decrypt n sk c), S)

/-- Word-encoded response wrapper around `interleavedCcaOracle`, returning the bit-encoded reply
`encodeCCAResponseWord encOut resp` alongside the updated challenge-ciphertext list `S'`. -/
@[expose] noncomputable def interleavedCcaWordOracle {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool)
    (query : CCAQuery Msg (List Bool)) :
    StateT (List (List Bool)) ProbComp (List Bool) := fun S => do
  let out ← interleavedCcaOracle valid encrypt decrypt n pk sk bit query S
  return (encodeCCAResponseWord encOut out.1, out.2)

@[simp] theorem interleavedCcaOracle_challenge_valid {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool) (m₀ m₁ : Msg) (S : List (List Bool))
    (hvalid : valid n pk m₀ m₁ = true) :
    interleavedCcaOracle valid encrypt decrypt n pk sk bit (.challenge m₀ m₁) S =
      (do
        let ct ← encrypt n pk (if bit then m₁ else m₀)
        return (Sum.inl (some ct), ct :: S)) := by
  simp only [interleavedCcaOracle, hvalid, ↓reduceIte]

@[simp] theorem interleavedCcaOracle_challenge_invalid {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool) (m₀ m₁ : Msg) (S : List (List Bool))
    (hvalid : valid n pk m₀ m₁ = false) :
    interleavedCcaOracle valid encrypt decrypt n pk sk bit (.challenge m₀ m₁) S =
      pure (Sum.inl none, S) := by
  simp only [interleavedCcaOracle, hvalid, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem interleavedCcaOracle_decrypt_mem {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool) (c : List Bool) (S : List (List Bool))
    (hmem : c ∈ S) :
    interleavedCcaOracle valid encrypt decrypt n pk sk bit (.decrypt c) S =
      pure (Sum.inr none, S) := by
  simp only [interleavedCcaOracle, hmem, decide_true, ↓reduceIte]

@[simp] theorem interleavedCcaOracle_decrypt_not_mem {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (pk sk : List Bool) (bit : Bool) (c : List Bool) (S : List (List Bool))
    (hmem : c ∉ S) :
    interleavedCcaOracle valid encrypt decrypt n pk sk bit (.decrypt c) S =
      pure (Sum.inr (decrypt n sk c), S) := by
  simp only [interleavedCcaOracle, hmem, decide_false, Bool.false_eq_true, ↓reduceIte]

/-! ### Adaptive interleaved-query multi-challenge CCA adversaries and experiments -/

/-- An adaptive interleaved-query multi-challenge CCA adversary over challenge message space `Msg`
([BonehShoup2023], Section 12.1, Attack Game 12.1, printed pp. 467–468):
* `numRounds n` is the number of adaptive combined-oracle rounds at security parameter `n`.
* In each round, `step n pk state lastReply` receives the unary security parameter `n`, the public
  key `pk`, the adversary's saved state word `state`, and the encoded response `lastReply` from the
  previous round (`[]` in round `0`), may make adaptive decryption queries against the current
  forbidden challenge-ciphertext list `S`, and outputs `(query, nextState) :
  CCAQuery Msg (List Bool) × List Bool`, where `query` is either `.challenge m₀ m₁` or `.decrypt c`.
* After `numRounds n` rounds, `finish n pk state lastReply` receives `(n, pk, state, lastReply)`,
  may make adaptive decryption queries against the final forbidden list `S`, and outputs a
  distinguishing bit `Bool`. -/
structure InterleavedCCA2AdversaryOf (Msg : Type) where
  /-- Number of adaptive combined-oracle rounds at security parameter `n`. -/
  numRounds : ℕ → ℕ
  /-- One adaptive round: given `(n, pk, state, lastReply)`, interact with the current decryption
  oracle (rejecting `S`) and emit a combined query `CCAQuery Msg (List Bool)` together with the
  updated state word. -/
  step : ℕ → List Bool → List Bool → List Bool →
    WordOracleComp Unit (CCAQuery Msg (List Bool) × List Bool)
  /-- Final guessing stage: given `(n, pk, state, lastReply)`, interact with the current decryption
  oracle (rejecting `S`) and output a distinguishing bit `Bool`. -/
  finish : ℕ → List Bool → List Bool → List Bool → WordOracleComp Unit Bool

/-- An adaptive interleaved-query multi-challenge CCA adversary for single-bit messages (`Bool`). -/
abbrev InterleavedCCA2Adversary : Type := InterleavedCCA2AdversaryOf Bool

/-- An adaptive interleaved-query multi-challenge CCA adversary for bit-word messages
(`List Bool`). -/
abbrev WordInterleavedCCA2Adversary : Type := InterleavedCCA2AdversaryOf (List Bool)

/-- Uniform strict PPT admissibility for an `InterleavedCCA2AdversaryOf Msg` over message encoding
`encMsg`:
* `numRounds` is computable in polynomial time on the unary security parameter `n`.
* `step` is uniformly strict oracle PPT on `(n, pk, state, lastReply)`.
* `finish` is uniformly strict oracle PPT on `(n, pk, state, lastReply)`.
* `step_length_le`: the encoded `(query, nextState)` output of `step n pk state lastReply`
  is bounded by a polynomial in `(n, pk.length)` (ensuring that the state passed across polynomially
  many adaptive rounds remains polynomially bounded without telescope blowup). -/
structure InterleavedCCA2AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : InterleavedCCA2AdversaryOf Msg) : Prop where
  /-- The round budget `numRounds` is computable in polynomial time on unary `n`. -/
  numRounds : ComputableInPolyTime adversary.numRounds encUnary encUnary
  /-- Each adaptive round `step` is uniformly strict oracle PPT. -/
  step : IsOraclePPTOn
    (encPair encUnary (encPair encBits (encPair encBits encBits)))
    (encPair (encCCAQuery encMsg) encBits)
    (fun ⟨n, pk, state, lastReply⟩ => adversary.step n pk state lastReply)
  /-- The final guessing stage `finish` is uniformly strict oracle PPT. -/
  finish : IsOraclePPTOn
    (encPair encUnary (encPair encBits (encPair encBits encBits)))
    encBool
    (fun ⟨n, pk, state, lastReply⟩ => adversary.finish n pk state lastReply)
  /-- Uniform polynomial bound on the encoded `(query, nextState)` output of `step` across rounds in
  terms of `(n, pk.length)`. -/
  step_length_le : ∃ cs ds : ℕ, ∀ n pk state lastReply out,
    out ∈ OracleComp.support (adversary.step n pk state lastReply) →
    (encPair (encCCAQuery encMsg) encBits out).length ≤ cs * (n + pk.length + 2) ^ ds

/-- Native uniform strict oracle PPT admissibility for a bit interleaved CCA adversary. -/
abbrev InterleavedCCA2Adversary.IsPPT (adversary : InterleavedCCA2Adversary) : Prop :=
  InterleavedCCA2AdversaryOf.IsPPT encBool adversary

/-- Native uniform strict oracle PPT admissibility for a bit-word interleaved CCA adversary. -/
abbrev WordInterleavedCCA2Adversary.IsPPT (adversary : WordInterleavedCCA2Adversary) : Prop :=
  InterleavedCCA2AdversaryOf.IsPPT encBits adversary

/-- Per-stage query bound for an `InterleavedCCA2AdversaryOf Msg`: at security parameter `n`, the
number of rounds is at most `qRounds n`, each `step` call makes at most `qStep n` inner decryption
queries, and `finish` makes at most `qFinish n` inner decryption queries. -/
@[expose] def InterleavedCCA2AdversaryOf.IsQueryBounded {Msg : Type}
    (adversary : InterleavedCCA2AdversaryOf Msg) (qRounds qStep qFinish : ℕ → ℕ) : Prop :=
  (∀ n, adversary.numRounds n ≤ qRounds n) ∧
  (∀ n pk state lastReply,
    ProbOracleComp.IsQueryBounded (adversary.step n pk state lastReply) (qStep n)) ∧
  (∀ n pk state lastReply,
    ProbOracleComp.IsQueryBounded (adversary.finish n pk state lastReply) (qFinish n))

/-- Loop state `(state, lastReply, S)` carried between adaptive rounds of `interleavedCca2Exp`:
* `state : List Bool` is the adversary's saved state word,
* `lastReply : List Bool` is the encoded oracle response from the previous round, and
* `S : List (List Bool)` is the list of challenge ciphertexts generated so far. -/
abbrev InterleavedLoopState : Type := List Bool × List Bool × List (List Bool)

/-- The adversary's saved state word in an `InterleavedLoopState`. -/
abbrev InterleavedLoopState.state (st : InterleavedLoopState) : List Bool := st.1

/-- The encoded oracle response from the previous round in an `InterleavedLoopState`. -/
abbrev InterleavedLoopState.lastReply (st : InterleavedLoopState) : List Bool := st.2.1

/-- The list of forbidden challenge ciphertexts generated so far in an `InterleavedLoopState`. -/
abbrev InterleavedLoopState.forbidden (st : InterleavedLoopState) : List (List Bool) := st.2.2

/-- Standard bit-string encoding of `InterleavedLoopState`. -/
@[expose] def encInterleavedLoopState : InterleavedLoopState ↪ List Bool :=
  encPair encBits (encPair encBits (encList encBits))

/-- Initial loop state `([], [], [])` before round `0`. -/
@[expose] def initInterleavedLoopState : InterleavedLoopState := ([], [], [])

/-- One closed adaptive round of the interleaved CCA experiment at challenge bit `roundBit`:
1. Run `adversary.step n pk st.state st.lastReply` against
   `cca2MultiPhase2Oracle encOut decrypt n sk st.forbidden` (which rejects any decryption query in
   the current forbidden challenge set `S = st.forbidden`).
2. Execute the returned combined query `q : CCAQuery Msg (List Bool)` against
   `interleavedCcaWordOracle valid encOut encrypt decrypt n pk sk roundBit q st.forbidden` to obtain
   the encoded response `reply` and updated forbidden challenge set `S'`.
3. Return the updated loop state `(state', reply, S')`. -/
@[expose] noncomputable def interleavedRoundStep {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (n : ℕ) (pk sk : List Bool) (roundBit : Bool)
    (st : InterleavedLoopState) : ProbComp InterleavedLoopState := do
  let stepRun ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n sk st.forbidden))
    (adversary.step n pk st.state st.lastReply)).run ()
  let stepOut := stepRun.1
  let orcOut ← interleavedCcaWordOracle valid encOut encrypt decrypt n pk sk roundBit
    stepOut.1 st.forbidden
  return (stepOut.2, orcOut.1, orcOut.2)

/-- The fully adaptive interleaved-query multi-challenge CCA experiment
([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.1, printed pp. 467–468):
sample `(pk, sk) ← keyGen n`, iterate `interleavedRoundStep` for `adversary.numRounds n` rounds
from `([], [], [])`, and run `adversary.finish` against `cca2MultiPhase2Oracle` with the final
forbidden challenge-ciphertext set `S`. -/
@[expose] noncomputable def interleavedCca2Exp {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let finalSt ← OracleComp.iterate (adversary.numRounds n)
    (interleavedRoundStep valid encOut encrypt decrypt adversary n keys.1 keys.2 bit)
    initInterleavedLoopState
  let guessOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n keys.2 finalSt.forbidden))
    (adversary.finish n keys.1 finalSt.state finalSt.lastReply)).run ()
  return guessOut.1

/-- Alias for `interleavedCca2Exp` matching the `cca2GameOn` / `cca2MultiGameOn` naming
convention. -/
noncomputable abbrev interleavedCca2GameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  interleavedCca2Exp valid encOut keyGen encrypt decrypt adversary bit n

/-- Unrestricted interleaved-query multi-challenge CCA experiment
(`valid := fun _ _ _ _ => true`). -/
noncomputable abbrev interleavedCca2Game {Msg Out : Type}
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  interleavedCca2GameOn (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- Fully adaptive interleaved-query multi-challenge CCA security
([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.1, printed pp. 467–468;
[KatzLindell2020], Section 12.2) with respect to challenge-pair admissibility predicate `valid`,
message encoding `encMsg`, and decryption output encoding `encOut`: every round-structured
`InterleavedCCA2AdversaryOf Msg` satisfying `InterleavedCCA2AdversaryOf.IsPPT encMsg` has
negligible advantage between the two experiments of `interleavedCca2GameOn`. -/
@[expose] def INDCCA2InterleavedOn {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary true n))
    (InterleavedCCA2AdversaryOf.IsPPT encMsg)

/-- Unrestricted interleaved-query multi-challenge CCA security (`valid := fun _ _ _ _ => true`). -/
abbrev INDCCA2InterleavedOf {Msg Out : Type} (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  INDCCA2InterleavedOn (fun _ _ _ _ => true) encMsg encOut keyGen encrypt decrypt

/-- Interleaved-query multi-challenge CCA security for single-bit encryption (`Msg = Bool`,
`Out = Bool`). -/
abbrev INDCCA2Interleaved (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Bool) : Prop :=
  INDCCA2InterleavedOf encBool encBool keyGen encrypt decrypt

/-- Interleaved-query multi-challenge CCA security for bit-word encryption (`Msg = List Bool`,
`Out = List Bool`) under Attack Game 12.1's equal-length challenge rule
`m₀.length == m₁.length`. -/
abbrev WordINDCCA2Interleaved (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) : Prop :=
  INDCCA2InterleavedOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encBits
    keyGen encrypt decrypt

/-! ### Relationship 1: Interleaved CCA2 implies single-challenge 1CCA and phased Multi-CCA2 -/

/-- Embed a single-challenge `CCA2AdversaryOf Msg` as a 1-round `InterleavedCCA2AdversaryOf Msg`
([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468):
* In Round 0 (`S = []`), `step` runs `adversary.choose n pk` (which makes Phase 1 decryption queries
  against `cca2MultiPhase2Oracle ... [] = cca2Phase1Oracle`) and submits
  `.challenge (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice)` along with the saved state
  `ChoiceOut.state choice`.
* In `finish` (`S = [ct]` when `valid n pk m₀ m₁ = true`), if `lastReply` begins with `true`
  (`lastReply = true :: ct`), `finish` runs `adversary.guess n state lastReply.tail` against
  `cca2MultiPhase2Oracle ... [ct] = cca2Phase2Oracle ... ct`; otherwise (`lastReply = []`), `finish`
  returns `false`. -/
@[expose] def CCA2AdversaryOf.toInterleaved {Msg : Type}
    (adversary : CCA2AdversaryOf Msg) : InterleavedCCA2AdversaryOf Msg where
  numRounds _ := 1
  step n pk _ _ := do
    let choice ← adversary.choose n pk
    return (.challenge (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice), ChoiceOut.state choice)
  finish n _ state lastReply :=
    if lastReply.headD false then
      adversary.guess n state lastReply.tail
    else
      pure false

/-- `CCA2AdversaryOf.toInterleaved` preserves uniform strict oracle PPT admissibility. -/
theorem isPPT_toInterleaved {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : CCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    adversary.toInterleaved.IsPPT encMsg where
  numRounds := ComputableInPolyTime.const 1
  step := by
    have := hA.choose.on
    dsimp only [CCA2AdversaryOf.toInterleaved, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state,
      ChoiceOut.msgs]
    fun_prop
  finish := by
    have := hA.guess
    dsimp only [CCA2AdversaryOf.toInterleaved]
    fun_prop
  step_length_le := by
    have hstepOn : IsOraclePPTOn (encPair encUnary encBits)
        (encPair (encCCAQuery encMsg) encBits)
        (fun p : ℕ × List Bool => do
          let choice ← adversary.choose p.1 p.2
          return (CCAQuery.challenge choice.1.1 choice.1.2, choice.2)) := by
      have := hA.choose.on
      fun_prop
    obtain ⟨cs, ds, hlen⟩ := hstepOn.length_le
    refine ⟨cs * 2 ^ ds, ds, fun n pk _ _ out hout => ?_⟩
    obtain ⟨State, oracle, s, s', hmem⟩ :=
      (ProbOracleComp.mem_support_iff_exists (hne := fun _ => ⟨[]⟩)).mp hout
    rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
    have hsize : (encPair encUnary encBits (n, pk)).length + 1 ≤ 2 * (n + pk.length + 2) := by
      enc_len
    have hpoly := Nat.mul_le_mul_left cs (Nat.pow_le_pow_left hsize ds)
    rw [Nat.mul_pow, ← Nat.mul_assoc] at hpoly
    exact (hlen (n, pk) State oracle s s' out hmem).trans hpoly

/-- Running `interleavedCca2GameOn` on `adversary.toInterleaved` has the exact same output
distribution as running `cca2GameOn` on `adversary`. -/
theorem eval_interleavedCca2GameOn_toInterleaved {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary.toInterleaved bit n) =
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  simp only [interleavedCca2GameOn, interleavedCca2Exp, cca2GameOn, CCA2AdversaryOf.toInterleaved,
    OracleComp.iterate_succ, OracleComp.iterate_zero, initInterleavedLoopState,
    interleavedRoundStep, interleavedCcaWordOracle, interleavedCcaOracle,
    InterleavedLoopState.state, InterleavedLoopState.lastReply, InterleavedLoopState.forbidden,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state, cca2MultiPhase2Oracle_nil,
    runWith_norm, pmf_norm]
  apply PMF.bind_congr_on_support
  intro keys _
  apply PMF.bind_congr_on_support
  intro choiceOut _
  by_cases hvalid : valid n keys.1 choiceOut.1.1.1 choiceOut.1.1.2 = true
  · simp only [hvalid, ↓reduceIte, encodeCCAResponseWord_inl_some, List.headD_cons,
      List.tail_cons, cca2MultiPhase2Oracle_singleton, runWith_norm, pmf_norm]
  · simp only [hvalid, Bool.false_eq_true, ↓reduceIte, encodeCCAResponseWord_inl_none,
      List.headD_nil, runWith_norm, pmf_norm]

/-- **Interleaved multi-challenge CCA security implies single-challenge 1CCA security**
([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468). -/
theorem INDCCA2InterleavedOn.indcca2On {Msg Out : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2InterleavedOn valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  have hneg := h adversary.toInterleaved (isPPT_toInterleaved hA)
  simpa only [eval_interleavedCca2GameOn_toInterleaved] using hneg

/-- **Interleaved multi-challenge CCA security implies phased batch-challenge multi-challenge CCA
security** ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Theorem 12.1, printed pp.
467–468) whenever `valid`, `keyGen`, `encrypt`, and `decrypt` are polynomial-time / strict PPT:
the proof passes through single-challenge 1CCA security (`INDCCA2InterleavedOn.indcca2On`) and
the hybrid reduction `INDCCA2On.indcca2MultiOn`. -/
theorem INDCCA2InterleavedOn.indcca2MultiOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2InterleavedOn valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt :=
  h.indcca2On.indcca2MultiOn hvalid hkeyGen hencrypt hdecrypt

/-! ### Relationship 2: Single-challenge 1CCA implies Interleaved Multi-CCA2 (Theorem 12.1) -/

/-- Saved state passed from Phase 1 (`choose`) to Phase 2 (`guess`) of `interleavedToSingleAt`. -/
private structure InterleavedSingleState where
  /-- Whether round `split < adversary.numRounds n` submitted an admissible challenge pair. -/
  active : Bool
  /-- Saved public key `pk` for running remaining rounds and `finish` in Phase 2. -/
  pk : List Bool
  /-- Number of remaining rounds `adversary.numRounds n - 1 - split` after round `split`. -/
  remRounds : ℕ
  /-- Saved adversary state word `state'` emitted by round `split`. -/
  state : List Bool
  /-- Forbidden challenge-ciphertext list `S` prior to round `split`. -/
  forbidden : List (List Bool)

/-- Standard bit-string encoding of `InterleavedSingleState` as the framed tuple
`(active, pk, remRounds, state, forbidden)`. -/
private enc_structure encInterleavedSingleState : InterleavedSingleState where
  active : encBool, pk : encBits, remRounds : encUnary, state : encBits,
  forbidden : (encList encBits)

private example (s : InterleavedSingleState) :
    encInterleavedSingleState s =
      encPair encBool (encPair encBits (encPair encUnary (encPair encBits (encList encBits))))
        (s.active, s.pk, s.remRounds, s.state, s.forbidden) := rfl

/-- Total polynomial-time decoder for `encInterleavedSingleState`. -/
private def interleavedSingleStateDecoder : Decoder encInterleavedSingleState :=
  (Decoder.bool.pair (Decoder.bits.pair (Decoder.unary.pair
    (Decoder.bits.pair (Decoder.list Decoder.bits))))).map
    (fun (active, pk, remRounds, state, forbidden) =>
      ⟨active, pk, remRounds, state, forbidden⟩)
    (fun s => (s.active, s.pk, s.remRounds, s.state, s.forbidden))
    (fun _ => rfl) (fun _ => rfl)

/-- Inactive state returned when `split ≥ adversary.numRounds n` or round `split` does not submit an
admissible challenge pair. -/
private def rejectInterleavedSingleState : List Bool :=
  encInterleavedSingleState ⟨false, [], 0, [], []⟩

@[simp] private theorem decode_rejectInterleavedSingleState :
    interleavedSingleStateDecoder.decode rejectInterleavedSingleState =
      ⟨false, [], 0, [], []⟩ :=
  interleavedSingleStateDecoder.decode_enc ⟨false, [], 0, [], []⟩

/-- Inner single-round program for `interleavedOpenRoundStep`, where external queries
`List.take (decBound n q.decryptCiphertext) <$> ProbOracleComp.query ((), q.decryptCiphertext)`
represent bounded-prefix queries to `cca2MultiPhase2Oracle` on the current forbidden ciphertext list
`st.forbidden`. -/
private noncomputable def interleavedInnerRound {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk : List Bool)
    (st : InterleavedLoopState) : WordOracleComp Unit InterleavedLoopState := do
  let stepOut ← adversary.step n pk st.state st.lastReply
  let q := stepOut.1
  let state' := stepOut.2
  if q.isChallenge then
    let pair := q.challengePair
    if valid n pk pair.1 pair.2 then do
      let ct ← ProbOracleComp.sample (encrypt n pk (if roundBit then pair.2 else pair.1))
      return (state', true :: ct, ct :: st.forbidden)
    else
      return (state', [], st.forbidden)
  else do
    let reply ←
      List.take (decBound n q.decryptCiphertext) <$>
        ProbOracleComp.query ((), q.decryptCiphertext)
    return (state', reply, st.forbidden)

/-- Open single-round step for the interleaved-to-single CCA reduction: run `interleavedInnerRound`
through `multiPhase2FilterHandler (decBound n) st.forbidden`. -/
private noncomputable def interleavedOpenRoundStep {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk : List Bool)
    (st : InterleavedLoopState) : WordOracleComp Unit InterleavedLoopState :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
      (multiPhase2FilterHandler (decBound n) st.forbidden))
    (interleavedInnerRound valid encrypt decBound adversary roundBit n pk st)).run ()

/-- Hybrid interleaved CCA experiment at round index `split : ℕ` ([BonehShoup2023], Section 12.1,
Theorem 12.1, printed p. 468): run the first `min split (adversary.numRounds n)` rounds with
`roundBit = true`, the remaining `adversary.numRounds n - split` rounds with `roundBit = false`, and
`adversary.finish` against the resulting forbidden challenge set `S`. -/
@[expose] noncomputable def interleavedHybridGameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let stMid ← OracleComp.iterate (min split (adversary.numRounds n))
    (interleavedRoundStep valid encOut encrypt decrypt adversary n keys.1 keys.2 true)
    initInterleavedLoopState
  let finalSt ← OracleComp.iterate (adversary.numRounds n - split)
    (interleavedRoundStep valid encOut encrypt decrypt adversary n keys.1 keys.2 false)
    stMid
  let guessOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n keys.2 finalSt.forbidden))
    (adversary.finish n keys.1 finalSt.state finalSt.lastReply)).run ()
  return guessOut.1

/-- At `split = 0`, `interleavedHybridGameOn` coincides with `interleavedCca2GameOn ... false`. -/
@[simp] theorem eval_interleavedHybridGameOn_zero {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval
      (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary 0 n) =
    ProbComp.eval
      (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary false n) := by
  simp [interleavedHybridGameOn, interleavedCca2GameOn, interleavedCca2Exp]

/-- Whenever `adversary.numRounds n ≤ split`, `interleavedHybridGameOn` at `split` coincides with
`interleavedCca2GameOn ... true`. -/
theorem eval_interleavedHybridGameOn_of_le {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ)
    (hle : adversary.numRounds n ≤ split) :
    ProbComp.eval
      (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) =
    ProbComp.eval
      (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary true n) := by
  simp [interleavedHybridGameOn, interleavedCca2GameOn, interleavedCca2Exp,
    Nat.min_eq_right hle, Nat.sub_eq_zero_of_le hle]

/-- Single-challenge `CCA2AdversaryOf Msg` reduction at fixed hybrid round index `split : ℕ`
([BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468):
* In Phase 1 (`choose`), if `split < adversary.numRounds n`, simulate the first `split` rounds using
  `roundBit = true` (`interleavedOpenRoundStep ... true`), then run `adversary.step` for round
  `split` through `multiPhase2FilterHandler`: if round `split` emits `.challenge m₀ m₁` with
  `valid n pk m₀ m₁ = true`, output `((m₀, m₁), encInterleavedSingleState ⟨true, pk,
  adversary.numRounds n - 1 - split, state', S⟩)`; otherwise output `rejectInterleavedSingleState`.
* In Phase 2 (`guess`), if `active = true`, prepend the external challenge ciphertext `ct` to `S`,
  simulate the remaining `remRounds` rounds using `roundBit = false`
  (`interleavedOpenRoundStep ... false`) starting from `(state', true :: ct, ct :: S)`, and run
  `adversary.finish` through `multiPhase2FilterHandler`. -/
noncomputable def interleavedToSingleAt {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split : ℕ) : CCA2AdversaryOf Msg where
  choose n pk := do
    if decide (split < adversary.numRounds n) then do
      let stMid ← OracleComp.iterate split
        (interleavedOpenRoundStep valid encrypt decBound adversary true n pk)
        initInterleavedLoopState
      let stepOut ← Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler (decBound n) stMid.forbidden))
        (adversary.step n pk stMid.state stMid.lastReply)).run ()
      let q := stepOut.1
      let state' := stepOut.2
      let pair := q.challengePair
      if q.isChallenge && valid n pk pair.1 pair.2 then
        return (pair,
          encInterleavedSingleState
            ⟨true, pk, adversary.numRounds n - 1 - split, state', stMid.forbidden⟩)
      else
        return ((default, default), rejectInterleavedSingleState)
    else
      return ((default, default), rejectInterleavedSingleState)
  guess n state ct :=
    let decoded := interleavedSingleStateDecoder.decode state
    if decoded.active then do
      let pk := decoded.pk
      let remRounds := decoded.remRounds
      let state' := decoded.state
      let S := decoded.forbidden
      let finalSt ← OracleComp.iterate remRounds
        (interleavedOpenRoundStep valid encrypt decBound adversary false n pk)
        (state', true :: ct, ct :: S)
      let guessOut ← (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler (decBound n) finalSt.forbidden))
        (adversary.finish n pk finalSt.state finalSt.lastReply)).run ()
      return guessOut.1
    else
      pure false

/-- Single-challenge `CCA2AdversaryOf Msg` reduction that samples a uniform dyadic round index
`split ← ProbOracleComp.sample (sampleDyadicIndex (Q n))` in Phase 1 and runs
`interleavedToSingleAt valid encrypt decBound adversary split`
([BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468). -/
noncomputable def interleavedToSingle {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := do
    let split ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
    (interleavedToSingleAt valid encrypt decBound adversary split).choose n pk
  guess n state ct :=
    (interleavedToSingleAt valid encrypt decBound adversary 0).guess n state ct

private theorem isOraclePPTOn_filterInterleaved {α β : Type}
    {Eα : α ↪ List Bool} {EOut : β ↪ List Bool}
    {decBound : ℕ → List Bool → ℕ} {nOf : α → ℕ}
    {prog : α × InterleavedLoopState → WordOracleComp Unit β}
    (hn : ComputableInPolyTime nOf Eα encUnary)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hprog : IsOraclePPTOn (encPair Eα encInterleavedLoopState) EOut prog) :
    IsOraclePPTOn (Operation := Unit) (encPair Eα encInterleavedLoopState) EOut
      (fun a =>
        Prod.fst <$> (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (decBound (nOf a.1)) a.2.2.2))
          (prog a)).run ()) :=
  (isOraclePPTOn_run_multiPhase2FilterHandler
    (ECaller := encPair Eα encInterleavedLoopState) (EOut := EOut)
    (cap := fun a req => decBound (nOf a.1) req) (cts := fun a => a.2.2.2)
    (by fun_prop) (by dsimp only [encInterleavedLoopState]; fun_prop) hprog).map
    (ComputableInPolyTime.fst _ _)

private theorem mem_support_of_mem_support_run_interpret {α : Type}
    (handler : Unit × List Bool → StateT Unit (WordOracleComp Unit) (List Bool))
    (prog : WordOracleComp Unit α) {result : α}
    (h : (result, ()) ∈ OracleComp.support ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        handler)
      prog).run ())) :
    result ∈ OracleComp.support prog := by
  obtain ⟨State, oracle, s, s', hrun⟩ := ProbOracleComp.mem_support_iff_exists.mp h
  rw [ProbOracleComp.run_interpret_run_interpret, PMF.mem_support_map_iff] at hrun
  obtain ⟨⟨r, u, s''⟩, hmem, heq⟩ := hrun
  obtain rfl : r = result := (Prod.mk.inj (Prod.mk.inj heq).1).1
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  exact ProbOracleComp.mem_support_of_mem _ hmem

/-- `interleavedInnerRound` is uniformly strict oracle PPT on `((n, pk), st)`. -/
private theorem isOraclePPTOn_interleavedInnerRound {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (roundBit : Bool) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits) encInterleavedLoopState)
      encInterleavedLoopState
      (fun p : (ℕ × List Bool) × InterleavedLoopState =>
        interleavedInnerRound valid encrypt decBound adversary roundBit p.1.1 p.1.2 p.2) := by
  have := hA.step
  dsimp only [interleavedInnerRound, encInterleavedLoopState, InterleavedLoopState.state,
    InterleavedLoopState.lastReply, InterleavedLoopState.forbidden]
  cases roundBit <;> fun_prop

/-- `interleavedOpenRoundStep` is uniformly strict oracle PPT on `((n, pk), st)`. -/
private theorem isOraclePPTOn_interleavedOpenRoundStep {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (roundBit : Bool) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits) encInterleavedLoopState)
      encInterleavedLoopState
      (fun p : (ℕ × List Bool) × InterleavedLoopState =>
        interleavedOpenRoundStep valid encrypt decBound adversary roundBit p.1.1 p.1.2 p.2) :=
  isOraclePPTOn_filterInterleaved (nOf := Prod.fst) (by fun_prop) hdecBound
    (isOraclePPTOn_interleavedInnerRound hvalid hencrypt hdecBound hA roundBit)

/-- Input encoding for the round-iteration tuple `(count, (n, pk), initSt)`. -/
private abbrev EInterleavedLoop :
    (ℕ × (ℕ × List Bool) × InterleavedLoopState) ↪ List Bool :=
  encPair encUnary (encPair (encPair encUnary encBits) encInterleavedLoopState)

/-- Per-round state-length growth bound for `interleavedOpenRoundStep`. -/
private def interleavedLoopGrowth (cs ds ce de cd dd : ℕ)
    (q : ℕ × (ℕ × List Bool) × InterleavedLoopState) : ℕ :=
  let B := cs * (q.2.1.1 + q.2.1.2.length + 2) ^ ds
  let ctMax := ce * (2 * q.2.1.1 + 2 * q.2.1.2.length + B + 5) ^ de
  let decMax := cd * (2 * q.2.1.1 + B + 3) ^ dd
  2 * B + 4 * ctMax + 2 * decMax + 8

private theorem polyBounded_interleavedLoopGrowth (cs ds ce de cd dd : ℕ) :
    PolyBounded (fun q => (EInterleavedLoop q).length)
      (interleavedLoopGrowth cs ds ce de cd dd) := by
  have hnPoly : PolyBounded (fun q => (EInterleavedLoop q).length) (fun q => q.2.1.1) :=
    PolyBounded.self.mono fun q => by enc_len [EInterleavedLoop]
  have hpkPoly : PolyBounded (fun q => (EInterleavedLoop q).length) (fun q => q.2.1.2.length) :=
    PolyBounded.self.mono fun q => by enc_len [EInterleavedLoop]
  unfold interleavedLoopGrowth
  growth_poly

/-- Single-step encoded state growth bound for `interleavedOpenRoundStep` in terms of concrete
component bounds `(B, ctMax, decMax)`. -/
private theorem length_interleavedOpenRoundStep_le_aux {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    {roundBit : Bool} {n : ℕ} {pk : List Bool} {st : InterleavedLoopState}
    {B ctMax decMax : ℕ}
    (hlenStep : ∀ out ∈ OracleComp.support (adversary.step n pk st.1 st.2.1),
      (encPair (encCCAQuery encMsg) encBits out).length ≤ B)
    (hlenEnc : ∀ m : Msg, (encMsg m).length ≤ B →
      ∀ ct ∈ (ProbComp.eval (encrypt n pk m)).support, ct.length ≤ ctMax)
    (hlenDec : ∀ c : List Bool, c.length ≤ B → decBound n c ≤ decMax) :
    ∀ next ∈ OracleComp.support
        (interleavedOpenRoundStep valid encrypt decBound adversary roundBit n pk st),
      (encInterleavedLoopState next).length ≤
        (encInterleavedLoopState st).length + (2 * B + 4 * ctMax + 2 * decMax + 8) := by
  intro next hnext
  unfold interleavedOpenRoundStep at hnext
  supp_cases hnext with ⟨⟨next', ⟨⟩⟩, hmemRun, rfl⟩
  have hmemInner := mem_support_of_mem_support_run_interpret
    (multiPhase2FilterHandler (decBound n) st.2.2)
    (interleavedInnerRound valid encrypt decBound adversary roundBit n pk st) hmemRun
  unfold interleavedInnerRound at hmemInner
  obtain ⟨⟨q, state'⟩, hstepOut, hbranch⟩ := OracleComp.mem_supportWith_bind_iff.mp hmemInner
  have hstepLen := hlenStep (q, state') hstepOut
  have hs'Len : state'.length ≤ B := by enc_len at hstepLen
  have hqLen : (encCCAQuery encMsg q).length ≤ B := by enc_len at hstepLen
  cases q with
  | challenge m₀ m₁ =>
    simp only [CCAQuery.isChallenge, ↓reduceIte, CCAQuery.challengePair] at hbranch
    have hmLen : (encMsg (if roundBit then m₁ else m₀)).length ≤ B := by
      simp only [encCCAQuery_apply, CCAQuery.toOptionPair, length_encPair, encOption,
        Function.Embedding.coeFn_mk, Option.elim, List.length_cons, encBits_apply,
        List.length_nil] at hqLen
      cases roundBit <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    by_cases hv : valid n pk m₀ m₁ = true
    · simp only [hv, ↓reduceIte] at hbranch
      supp_cases hbranch with ⟨ct, hctSample, rfl⟩
      have hctLen := hlenEnc _ hmLen ct ((ProbOracleComp.support_sample _).subset hctSample)
      enc_len [encInterleavedLoopState, InterleavedLoopState.forbidden]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hbranch
      supp_cases hbranch
      enc_len [encInterleavedLoopState, InterleavedLoopState.forbidden]
  | decrypt c =>
    simp only [CCAQuery.isChallenge, Bool.false_eq_true, ↓reduceIte,
      CCAQuery.decryptCiphertext] at hbranch
    supp_cases hbranch with ⟨_, ⟨rawReply, -, rfl⟩, rfl⟩
    have hcLen : c.length ≤ B := by
      enc_len [encCCAQuery_apply, CCAQuery.toOptionPair, encOption, Function.Embedding.coeFn_mk,
        Option.elim] at hqLen
    have := (List.length_take_le (decBound n c) rawReply).trans (hlenDec c hcLen)
    enc_len [encInterleavedLoopState, InterleavedLoopState.forbidden]

/-- Single-step encoded state growth bound for `interleavedOpenRoundStep` in terms of polynomial
coefficients `(cs, ds, ce, de, cd, dd)`. -/
private theorem length_interleavedOpenRoundStep_le {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (roundBit : Bool) {cs ds ce de cd dd : ℕ}
    (q : ℕ × (ℕ × List Bool) × InterleavedLoopState) (st : InterleavedLoopState)
    (hlenStep : ∀ out ∈ OracleComp.support (adversary.step q.2.1.1 q.2.1.2 st.1 st.2.1),
      (encPair (encCCAQuery encMsg) encBits out).length ≤
        cs * (q.2.1.1 + q.2.1.2.length + 2) ^ ds)
    (hlenEnc : ∀ (a : ℕ × List Bool × Msg) (result : List Bool),
      result ∈ (ProbComp.eval (encrypt a.1 a.2.1 a.2.2)).support →
      (encBits result).length ≤
        ce * ((encPair encUnary (encPair encBits encMsg) a).length + 1) ^ de)
    (hlenDec : ∀ a : ℕ × List Bool,
      (encUnary (decBound a.1 a.2)).length ≤
        cd * ((encPair encUnary encBits a).length + 1) ^ dd) :
    ∀ next ∈ OracleComp.support
        (interleavedOpenRoundStep valid encrypt decBound adversary roundBit q.2.1.1 q.2.1.2 st),
      (encInterleavedLoopState next).length ≤
        (encInterleavedLoopState st).length + interleavedLoopGrowth cs ds ce de cd dd q := by
  refine length_interleavedOpenRoundStep_le_aux hlenStep (fun m hm ct hct => ?_) (fun c hc => ?_)
  · have he := hlenEnc (q.2.1.1, q.2.1.2, m) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at he
    have hbase :
        2 * q.2.1.1 + 1 + (2 * q.2.1.2.length + 1 + (encMsg m).length) + 1 ≤
          2 * q.2.1.1 + 2 * q.2.1.2.length + cs * (q.2.1.1 + q.2.1.2.length + 2) ^ ds + 5 := by
      omega
    exact he.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left hbase de))
  · have hd := hlenDec (q.2.1.1, c)
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hd
    have hbase :
        2 * q.2.1.1 + 1 + c.length + 1 ≤
          2 * q.2.1.1 + cs * (q.2.1.1 + q.2.1.2.length + 2) ^ ds + 3 := by
      omega
    exact hd.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left hbase dd))

/-- Iterating `interleavedOpenRoundStep` `q.1` times from `q.2.2` is uniformly strict oracle PPT in
`q = (count, (n, pk), initSt)`. -/
private theorem isOraclePPTOn_iterate_interleavedOpenRoundStep {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (roundBit : Bool) :
    IsOraclePPTOn (Operation := Unit)
      (encPair encUnary (encPair (encPair encUnary encBits) encInterleavedLoopState))
      encInterleavedLoopState
      (fun q : ℕ × (ℕ × List Bool) × InterleavedLoopState =>
        OracleComp.iterate q.1
          (interleavedOpenRoundStep valid encrypt decBound adversary roundBit q.2.1.1 q.2.1.2)
          q.2.2) := by
  obtain ⟨cs, ds, hlenStep⟩ := hA.step_length_le
  obtain ⟨ce, de, hlenEnc⟩ := hencrypt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := hdecBound.polyBounded_length.exists_le
  exact IsOraclePPTOn.iterateWith_of_bounded_growth
    (initial := fun q : ℕ × (ℕ × List Bool) × InterleavedLoopState => q.2.2)
    (count := fun q : ℕ × (ℕ × List Bool) × InterleavedLoopState => q.1)
    (step := fun q : ℕ × (ℕ × List Bool) × InterleavedLoopState =>
      interleavedOpenRoundStep valid encrypt decBound adversary roundBit q.2.1.1 q.2.1.2)
    (by fun_prop) (by fun_prop)
    ((isOraclePPTOn_interleavedOpenRoundStep hvalid hencrypt hdecBound hA roundBit).preprocess
      (prepare := fun pair : (ℕ × (ℕ × List Bool) × InterleavedLoopState) × InterleavedLoopState =>
        (pair.1.2.1, pair.2)) (by fun_prop))
    (polyBounded_interleavedLoopGrowth cs ds ce de cd dd)
    (fun q st => length_interleavedOpenRoundStep_le valid roundBit q st
      (hlenStep q.2.1.1 q.2.1.2 st.1 st.2.1) hlenEnc hlenDec)

/-- Phase 1 (`choose`) of `interleavedToSingleAt` is uniformly strict oracle PPT in
`((n, pk), split)`. -/
private theorem isOraclePPTOn_interleavedToSingleAt_choose {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits) encUnary)
      (encChoiceOut encMsg)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (interleavedToSingleAt valid encrypt decBound adversary caller.2).choose
          caller.1.1 caller.1.2) := by
  have := hA.numRounds
  let ECaller := encPair (encPair encUnary encBits) encUnary
  let E2 := encPair ECaller encInterleavedLoopState
  have hiter : IsOraclePPTOn (Operation := Unit) ECaller encInterleavedLoopState
      (fun caller : (ℕ × List Bool) × ℕ =>
        OracleComp.iterate caller.2
          (interleavedOpenRoundStep valid encrypt decBound adversary true caller.1.1 caller.1.2)
          initInterleavedLoopState) :=
    (isOraclePPTOn_iterate_interleavedOpenRoundStep hvalid hencrypt hdecBound hA true).preprocess
      (prepare := fun c : (ℕ × List Bool) × ℕ => (c.2, c.1, initInterleavedLoopState))
      (by dsimp only [ECaller]; fun_prop)
  have hstepFiltered : IsOraclePPTOn (Operation := Unit) E2
      (encPair (encCCAQuery encMsg) encBits)
      (fun p : ((ℕ × List Bool) × ℕ) × InterleavedLoopState =>
        Prod.fst <$> (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (decBound p.1.1.1) p.2.2.2))
          (adversary.step p.1.1.1 p.1.1.2 p.2.1 p.2.2.1)).run ()) :=
    isOraclePPTOn_filterInterleaved (Eα := ECaller) (nOf := fun c => c.1.1)
      (by dsimp only [ECaller]; fun_prop) hdecBound
      (hA.step.preprocess
        (prepare := fun p : ((ℕ × List Bool) × ℕ) × InterleavedLoopState =>
          (p.1.1.1, p.1.1.2, p.2.1, p.2.2.1))
        (by dsimp only [ECaller, encInterleavedLoopState]; fun_prop))
  dsimp only [interleavedToSingleAt, InterleavedLoopState.state, InterleavedLoopState.lastReply,
    InterleavedLoopState.forbidden]
  refine IsOraclePPTOn.cond (by fun_prop)
    (hiter.bind_with (hstepFiltered.bind_with ?_)) (by fun_prop)
  dsimp only [E2, ECaller, encInterleavedLoopState]
  fun_prop

/-- Phase 2 (`guess`) of `interleavedToSingleAt` is uniformly strict oracle PPT in
`(n, state, ct)`. -/
private theorem isOraclePPTOn_interleavedToSingleAt_guess {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    IsOraclePPTOn (Operation := Unit)
      encGuessInput encBool
      (fun p : ℕ × List Bool × List Bool =>
        (interleavedToSingleAt valid encrypt decBound adversary split).guess
          p.1 p.2.1 p.2.2) := by
  have hiter : IsOraclePPTOn (Operation := Unit) encGuessInput encInterleavedLoopState
      (fun p : ℕ × List Bool × List Bool =>
        OracleComp.iterate (interleavedSingleStateDecoder.decode p.2.1).remRounds
          (interleavedOpenRoundStep valid encrypt decBound adversary false
            p.1 (interleavedSingleStateDecoder.decode p.2.1).pk)
          ((interleavedSingleStateDecoder.decode p.2.1).state,
            true :: p.2.2,
            p.2.2 :: (interleavedSingleStateDecoder.decode p.2.1).forbidden)) :=
    (isOraclePPTOn_iterate_interleavedOpenRoundStep hvalid hencrypt hdecBound hA false).preprocess
      (prepare := fun p : ℕ × List Bool × List Bool =>
        ((interleavedSingleStateDecoder.decode p.2.1).remRounds,
          (p.1, (interleavedSingleStateDecoder.decode p.2.1).pk),
          ((interleavedSingleStateDecoder.decode p.2.1).state,
            true :: p.2.2,
            p.2.2 :: (interleavedSingleStateDecoder.decode p.2.1).forbidden)))
      (by dsimp only [encInterleavedLoopState]; fun_prop)
  have hfinishFiltered : IsOraclePPTOn (Operation := Unit)
      (encPair encGuessInput encInterleavedLoopState) encBool
      (fun q : (ℕ × List Bool × List Bool) × InterleavedLoopState =>
        Prod.fst <$> (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (decBound q.1.1) q.2.2.2))
          (adversary.finish q.1.1
            (interleavedSingleStateDecoder.decode q.1.2.1).pk
            q.2.1 q.2.2.1)).run ()) :=
    isOraclePPTOn_filterInterleaved (nOf := Prod.fst) (by fun_prop) hdecBound
      (hA.finish.preprocess
        (prepare := fun q : (ℕ × List Bool × List Bool) × InterleavedLoopState =>
          (q.1.1, (interleavedSingleStateDecoder.decode q.1.2.1).pk, q.2.1, q.2.2.1))
        (by dsimp only [encInterleavedLoopState]; fun_prop))
  dsimp only [interleavedToSingleAt, InterleavedLoopState.state, InterleavedLoopState.lastReply,
    InterleavedLoopState.forbidden]
  exact IsOraclePPTOn.cond (by fun_prop)
    (by simpa only [bind_pure_comp] using hiter.bind_with hfinishFiltered) (by fun_prop)

/-- `interleavedToSingleAt` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_interleavedToSingleAt {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    (interleavedToSingleAt valid encrypt decBound adversary split).IsPPT encMsg where
  choose := by
    have h := (isOraclePPTOn_interleavedToSingleAt_choose
      hvalid hencrypt hdecBound hA).preprocess
      (ComputableInPolyTime.prod ComputableInPolyTime.id' (ComputableInPolyTime.const split))
    exact h.isOraclePPT
  guess :=
    isOraclePPTOn_interleavedToSingleAt_guess valid encrypt hvalid hencrypt hdecBound hA split

/-- `interleavedToSingle` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_interleavedToSingle {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ} {Q : ℕ → ℕ}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime (fun ⟨n, req⟩ => decBound n req)
      (encPair encUnary encBits) encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hA : adversary.IsPPT encMsg) :
    (interleavedToSingle valid encrypt decBound Q adversary).IsPPT encMsg where
  choose := by
    have hsample : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encUnary
        (fun caller : ℕ × List Bool =>
          ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q caller.1))) :=
      (isPPTOn_sampleDyadicIndex (hQ.comp (by fun_prop))).isOraclePPTOn (Operation := Unit)
    exact (hsample.bind_with
      (isOraclePPTOn_interleavedToSingleAt_choose hvalid hencrypt hdecBound hA)).isOraclePPT
  guess := isOraclePPTOn_interleavedToSingleAt_guess valid encrypt hvalid hencrypt hdecBound hA 0

/-- Interpreting `interleavedInnerRound` against `cca2MultiPhase2Oracle` has the same distribution
as `interleavedRoundStep`. -/
private theorem eval_interpret_interleavedInnerRound {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk sk : List Bool) (st : InterleavedLoopState)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk st.2.2))
      (interleavedInnerRound valid encrypt decBound adversary roundBit n pk st)).run ()) =
    (ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st)).map
      (fun st' => (st', ())) := by
  unfold interleavedInnerRound interleavedRoundStep
  simp only [runWith_norm, pmf_norm]
  apply PMF.bind_congr_on_support
  rintro ⟨⟨q, state'⟩, ⟨⟩⟩ _
  cases q with
  | challenge m₀ m₁ =>
    simp only [CCAQuery.isChallenge, ↓reduceIte, CCAQuery.challengePair,
      interleavedCcaWordOracle, interleavedCcaOracle]
    by_cases hv : valid n pk m₀ m₁ = true
    · simp only [hv, ↓reduceIte, encodeCCAResponseWord_inl_some, runWith_norm, pmf_norm]
    · simp [hv, runWith_norm, pmf_norm]
  | decrypt c =>
    simp only [CCAQuery.isChallenge, Bool.false_eq_true, ↓reduceIte, CCAQuery.decryptCiphertext,
      cca2MultiPhase2Oracle, interleavedCcaWordOracle, interleavedCcaOracle, runWith_norm, pmf_norm]
    by_cases hmem : c ∈ st.2.2
    · simp [hmem, ProbComp.eval_pure, encOption]
    · simp [hmem, ProbComp.eval_pure, List.take_of_length_le (hdecBound c)]

/-- Interpreting `interleavedOpenRoundStep` against `cca2Phase1Oracle` has the same distribution as
`interleavedRoundStep`. -/
private theorem eval_interpret_interleavedOpenRoundStep_phase1 {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk sk : List Bool) (st : InterleavedLoopState)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (interleavedOpenRoundStep valid encrypt decBound adversary roundBit n pk st)).run ()) =
    (ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st)).map
      (fun st' => (st', ())) := by
  unfold interleavedOpenRoundStep
  rw [eval_run_multiPhase2FilterHandler_phase1 encOut decrypt (decBound n) n sk st.2.2 hdecBound,
    eval_interpret_interleavedInnerRound valid encOut encrypt decrypt decBound adversary
      roundBit n pk sk st hdecBound]

/-- Interpreting `interleavedOpenRoundStep` against `cca2Phase2Oracle` on `ct ∈ st.2.2` has the
same distribution as `interleavedRoundStep`. -/
private theorem eval_interpret_interleavedOpenRoundStep_phase2 {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk sk ct : List Bool) (st : InterleavedLoopState)
    (hct : ct ∈ st.2.2)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n sk ct))
      (interleavedOpenRoundStep valid encrypt decBound adversary roundBit n pk st)).run ()) =
    (ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st)).map
      (fun st' => (st', ())) := by
  unfold interleavedOpenRoundStep
  rw [eval_run_multiPhase2FilterHandler encOut decrypt (decBound n) n sk ct st.2.2
      hct hdecBound,
    eval_interpret_interleavedInnerRound valid encOut encrypt decrypt decBound adversary
      roundBit n pk sk st hdecBound]

/-- Every supported transition of `interleavedRoundStep` preserves membership in the forbidden
challenge-ciphertext list `S`. -/
private theorem mem_S_of_mem_support_interleavedRoundStep {Msg Out : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encOut : Out ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : InterleavedCCA2AdversaryOf Msg}
    {n : ℕ} {pk sk : List Bool} {roundBit : Bool}
    {st st' : InterleavedLoopState} {ct : List Bool}
    (hst' : st' ∈ (ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st)).support)
    (hct : ct ∈ st.2.2) :
    ct ∈ st'.2.2 := by
  unfold interleavedRoundStep interleavedCcaWordOracle interleavedCcaOracle at hst'
  rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hst'
  obtain ⟨⟨⟨q, state'⟩, ⟨⟩⟩, -, hreply⟩ := hst'
  cases q with
  | challenge m₀ m₁ =>
    dsimp only at hreply
    by_cases hv : valid n pk m₀ m₁ = true
    · simp only [hv, ↓reduceIte] at hreply
      supp_cases hreply
      exact List.mem_cons_of_mem _ hct
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hreply
      supp_cases hreply
      exact hct
  | decrypt c =>
    dsimp only at hreply
    by_cases hmem : c ∈ st.2.2 <;>
      simp only [hmem, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at hreply <;>
      supp_cases hreply <;> exact hct

/-- Iterating `interleavedOpenRoundStep` `k` times under `cca2Phase1Oracle` has the same
distribution as iterating `interleavedRoundStep` `k` times. -/
private theorem eval_interpret_iterate_interleavedOpenRoundStep_phase1 {Msg Out : Type}
    [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk sk : List Bool) (k : ℕ) (st : InterleavedLoopState)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (OracleComp.iterate k
        (interleavedOpenRoundStep valid encrypt decBound adversary roundBit n pk) st)).run ()) =
    (ProbComp.eval (OracleComp.iterate k
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit) st)).map
      (fun st' => (st', ())) := by
  simp only [OracleComp.run_interpret_iterate, ProbComp.eval_iterate]
  symm
  apply Probability.PMF.RepInv.map_eq (inv := fun _ => True)
  exact Probability.PMF.RepInv.iterate (fun _ _ => True) rfl trivial
    fun _ _ st' _ => .of_eq (eval_interpret_interleavedOpenRoundStep_phase1 valid encOut encrypt
      decrypt decBound adversary roundBit n pk sk st' hdecBound).symm

/-- Iterating `interleavedOpenRoundStep` `k` times under `cca2Phase2Oracle` on `ct ∈ st.2.2` has the
same distribution as iterating `interleavedRoundStep` `k` times. -/
private theorem eval_interpret_iterate_interleavedOpenRoundStep_phase2 {Msg Out : Type}
    [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg)
    (roundBit : Bool) (n : ℕ) (pk sk ct : List Bool) (k : ℕ) (st : InterleavedLoopState)
    (hct : ct ∈ st.2.2)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n sk ct))
      (OracleComp.iterate k
        (interleavedOpenRoundStep valid encrypt decBound adversary roundBit n pk) st)).run ()) =
    (ProbComp.eval (OracleComp.iterate k
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit) st)).map
      (fun st' => (st', ())) := by
  simp only [OracleComp.run_interpret_iterate, ProbComp.eval_iterate]
  symm
  apply Probability.PMF.RepInv.map_eq (inv := fun st' => ct ∈ st'.2.2)
  apply Probability.PMF.RepInv.iterate (fun (_ : ℕ) (st' : InterleavedLoopState) => ct ∈ st'.2.2)
  · rfl
  · exact hct
  intro _ _ st' hst'
  exact ⟨(eval_interpret_interleavedOpenRoundStep_phase2 valid encOut encrypt decrypt decBound
    adversary roundBit n pk sk ct st' hst' hdecBound).symm,
    fun _ h => mem_S_of_mem_support_interleavedRoundStep h hst'⟩

/-- Continuation of `interleavedHybridGameOn` after round `split` has emitted `stepOut` from state
`stMid`, parameterized by the challenge bit `roundBit` used in round `split`. -/
private noncomputable def interleavedHybridAfterStep {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ)
    (pk sk : List Bool) (roundBit : Bool)
    (stMid : InterleavedLoopState)
    (stepOut : CCAQuery Msg (List Bool) × List Bool) : ProbComp Bool := do
  let replyOut ←
    interleavedCcaWordOracle valid encOut encrypt decrypt n pk sk roundBit
      stepOut.1 stMid.forbidden
  let finalSt ← OracleComp.iterate (adversary.numRounds n - 1 - split)
    (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk false)
    (stepOut.2, replyOut.1, replyOut.2)
  let guessOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n sk finalSt.forbidden))
    (adversary.finish n pk finalSt.state finalSt.lastReply)).run ()
  return guessOut.1

private theorem interleavedHybridAfterStep_eq_of_not_chalValid {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ)
    (pk sk : List Bool) (stMid : InterleavedLoopState)
    (stepOut : CCAQuery Msg (List Bool) × List Bool)
    (hnot : (stepOut.1.isChallenge &&
      valid n pk stepOut.1.challengePair.1 stepOut.1.challengePair.2) = false) :
    interleavedHybridAfterStep valid encOut encrypt decrypt adversary split n pk sk true
      stMid stepOut =
    interleavedHybridAfterStep valid encOut encrypt decrypt adversary split n pk sk false
      stMid stepOut := by
  rcases stepOut with ⟨m₀ | c, state'⟩
  · simp only [CCAQuery.isChallenge, Bool.true_and, CCAQuery.challengePair] at hnot
    simp [interleavedHybridAfterStep, interleavedCcaWordOracle, interleavedCcaOracle, hnot]
  · simp [interleavedHybridAfterStep, interleavedCcaWordOracle, interleavedCcaOracle]

private theorem eval_interleavedToSingleAt_guess_active {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n remRounds : ℕ)
    (pk sk state' ct : List Bool) (S : List (List Bool))
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval (do
      let guessOut ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase2Oracle encOut decrypt n sk ct))
        ((interleavedToSingleAt valid encrypt decBound adversary split).guess n
          (encInterleavedSingleState ⟨true, pk, remRounds, state', S⟩) ct)).run ()
      return guessOut.1) =
    ProbComp.eval (do
      let finalSt ← OracleComp.iterate remRounds
        (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk false)
        (state', true :: ct, ct :: S)
      let guessOut ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2MultiPhase2Oracle encOut decrypt n sk finalSt.2.2))
        (adversary.finish n pk finalSt.1 finalSt.2.1)).run ()
      return guessOut.1) := by
  unfold interleavedToSingleAt
  dsimp only
  rw [interleavedSingleStateDecoder.decode_enc]
  simp only [↓reduceIte, OracleComp.interpret_bind, StateT.run_bind, OracleComp.interpret_pure,
    StateT.run_pure, pmf_norm]
  rw [eval_interpret_iterate_interleavedOpenRoundStep_phase2 valid encOut encrypt decrypt decBound
    adversary false n pk sk ct remRounds (state', true :: ct, ct :: S) (List.mem_cons_self ..)
    hdecBound]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro finalSt hfinalSt
  have hctFinal : ct ∈ finalSt.2.2 :=
    ProbComp.iterate_invariant remRounds
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk false)
      (state', true :: ct, ct :: S) (fun _ st => ct ∈ st.2.2) (List.mem_cons_self ..)
      (fun _ _ _ hs _ hnext => mem_S_of_mem_support_interleavedRoundStep hnext hs)
      finalSt hfinalSt
  have hfin := eval_run_multiPhase2FilterHandler encOut decrypt (decBound n) n sk ct
    finalSt.2.2 hctFinal hdecBound (adversary.finish n pk finalSt.1 finalSt.2.1)
  have hmap := congrArg (fun p : PMF (Bool × Unit) => p.bind (fun x => PMF.pure x.1)) hfin
  simpa only [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def, PMF.bind_pure] using hmap

@[simp] private theorem interleavedToSingleAt_guess_reject {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ) (ct : List Bool) :
    (interleavedToSingleAt valid encrypt decBound adversary split).guess n
      rejectInterleavedSingleState ct = pure false := by
  dsimp only [interleavedToSingleAt]
  rw [decode_rejectInterleavedSingleState]
  rfl

/-- In `cca2GameOn`, running `interleavedToSingleAt ... split` when `split < adversary.numRounds n`
evaluates the first `split` rounds via `interleavedRoundStep ... true`, runs round `split`'s
`adversary.step`, and either continues as `interleavedHybridAfterStep ... bit` (when round `split`
emits an admissible `.challenge` query) or outputs `false`. -/
private theorem eval_cca2GameOn_interleavedToSingleAt_of_lt {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split : ℕ) (bit : Bool) (n : ℕ)
    (hlt : split < adversary.numRounds n)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (interleavedToSingleAt valid encrypt decBound adversary split) bit n) =
    (ProbComp.eval (keyGen n)).bind fun keys =>
      (ProbComp.eval (OracleComp.iterate split
        (interleavedRoundStep valid encOut encrypt decrypt adversary n keys.1 keys.2 true)
        initInterleavedLoopState)).bind fun stMid =>
        (ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2MultiPhase2Oracle encOut decrypt n keys.2 stMid.2.2))
          (adversary.step n keys.1 stMid.1 stMid.2.1)).run ())).bind fun stepOut =>
          if stepOut.1.1.isChallenge &&
              valid n keys.1 stepOut.1.1.challengePair.1 stepOut.1.1.challengePair.2 then
            ProbComp.eval
              (interleavedHybridAfterStep valid encOut encrypt decrypt adversary split n
                keys.1 keys.2 bit stMid stepOut.1)
          else
            PMF.pure false := by
  have hltDec : decide (split < adversary.numRounds n) = true := decide_eq_true hlt
  conv_lhs =>
    unfold cca2GameOn
    simp only [ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  set G := (interleavedToSingleAt valid encrypt decBound adversary split).guess with hG
  dsimp only [interleavedToSingleAt]
  simp only [hltDec, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind, ProbComp.eval_bind,
    PMF.bind_bind]
  rw [eval_interpret_iterate_interleavedOpenRoundStep_phase1 valid encOut encrypt decrypt decBound
    adversary true n keys.1 keys.2 split initInterleavedLoopState (hdecBound keys hkeys)]
  simp only [PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun stMid _ => ?_
  rw [eval_run_multiPhase2FilterHandler_phase1 encOut decrypt (decBound n) n keys.2
    stMid.2.2 (hdecBound keys hkeys) (adversary.step n keys.1 stMid.1 stMid.2.1)]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨q, state'⟩, ⟨⟩⟩ _ => ?_
  by_cases hcond : (q.isChallenge && valid n keys.1 q.challengePair.1 q.challengePair.2) = true
  · obtain ⟨hisC, hval⟩ := Bool.and_eq_true_iff.mp hcond
    cases q with
    | decrypt c => cases hisC
    | challenge m₀ m₁ =>
      simp only [CCAQuery.isChallenge, CCAQuery.challengePair] at hval ⊢
      simp only [hval, Bool.and_self, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state, interleavedHybridAfterStep,
        interleavedCcaWordOracle, interleavedCcaOracle, encodeCCAResponseWord_inl_some, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun ct _ => ?_
      rw [hG]
      simpa only [ProbComp.eval_bind, ProbComp.eval_pure] using
        eval_interleavedToSingleAt_guess_active valid encOut encrypt decrypt decBound
          adversary split n (adversary.numRounds n - 1 - split) keys.1 keys.2 state' ct stMid.2.2
          (hdecBound keys hkeys)
  · rw [hG]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
      ProbComp.eval_pure, PMF.pure_bind, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state,
      interleavedToSingleAt_guess_reject]
    by_cases hv : valid n keys.1 default default = true
    · simp only [hv, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
        PMF.bind_const]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

/-- When `adversary.numRounds n ≤ split`, `interleavedToSingleAt ... split` always outputs `false`
in `cca2GameOn`. -/
private theorem eval_cca2GameOn_interleavedToSingleAt_of_le {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split : ℕ) (bit : Bool) (n : ℕ)
    (hle : adversary.numRounds n ≤ split) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (interleavedToSingleAt valid encrypt decBound adversary split) bit n) =
    PMF.pure false := by
  have hltFalse : decide (split < adversary.numRounds n) = false :=
    decide_eq_false (Nat.not_lt_of_ge hle)
  conv_lhs =>
    unfold cca2GameOn
    simp only [ProbComp.eval_bind]
  rw [← PMF.bind_const (ProbComp.eval (keyGen n)) (PMF.pure false)]
  refine PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  set G := (interleavedToSingleAt valid encrypt decBound adversary split).guess with hG
  dsimp only [interleavedToSingleAt]
  rw [hG]
  simp only [hltFalse, Bool.false_eq_true, ↓reduceIte, ChoiceOut.msg₀, ChoiceOut.msg₁,
    ChoiceOut.state, interleavedToSingleAt_guess_reject, runWith_norm, pmf_norm]
  by_cases hv : valid n keys.1 default default = true
  · simp only [hv, ↓reduceIte, PMF.bind_const, runWith_norm, pmf_norm]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

/-- Decomposition of `interleavedHybridGameOn ... (if roundBit then split + 1 else split)` at round
`split < adversary.numRounds n` through `interleavedHybridAfterStep`. -/
private theorem eval_interleavedHybridGameOn_split_of_lt {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split : ℕ) (roundBit : Bool) (n : ℕ)
    (hlt : split < adversary.numRounds n) :
    ProbComp.eval
      (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary
        (if roundBit then split + 1 else split) n) =
    (ProbComp.eval (keyGen n)).bind fun keys =>
      (ProbComp.eval (OracleComp.iterate split
        (interleavedRoundStep valid encOut encrypt decrypt adversary n keys.1 keys.2 true)
        initInterleavedLoopState)).bind fun stMid =>
        (ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2MultiPhase2Oracle encOut decrypt n keys.2 stMid.2.2))
          (adversary.step n keys.1 stMid.1 stMid.2.1)).run ())).bind fun stepOut =>
          ProbComp.eval
            (interleavedHybridAfterStep valid encOut encrypt decrypt adversary split n
              keys.1 keys.2 roundBit stMid stepOut.1) := by
  cases roundBit
  · have hmin : min split (adversary.numRounds n) = split := Nat.min_eq_left (Nat.le_of_lt hlt)
    have hsub : adversary.numRounds n - split = (adversary.numRounds n - 1 - split) + 1 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, interleavedHybridGameOn, hmin, hsub,
      OracleComp.iterate_succ_bind, ProbComp.eval_bind, PMF.bind_bind]
    apply PMF.bind_congr_on_support
    intro keys _
    apply PMF.bind_congr_on_support
    intro stMid _
    dsimp only [interleavedHybridAfterStep]
    rw [interleavedRoundStep]
    simp only [pmf_norm]
  · have hmin : min (split + 1) (adversary.numRounds n) = split + 1 := Nat.min_eq_left hlt
    have hsub : adversary.numRounds n - (split + 1) = adversary.numRounds n - 1 - split := by omega
    simp only [↓reduceIte, interleavedHybridGameOn, hmin, hsub,
      OracleComp.iterate_succ, ProbComp.eval_bind, PMF.bind_bind]
    apply PMF.bind_congr_on_support
    intro keys _
    apply PMF.bind_congr_on_support
    intro stMid _
    dsimp only [interleavedHybridAfterStep]
    rw [interleavedRoundStep]
    simp only [pmf_norm]

/-- **Single-step hybrid identity for interleaved multi-challenge CCA** ([BonehShoup2023],
Theorem 12.1, printed p. 468): at any round index `split : ℕ`, the signed success-probability gap
between `interleavedHybridGameOn ... split` and `interleavedHybridGameOn ... (split + 1)` equals the
signed 1CCA gap of `interleavedToSingleAt ... split`. -/
theorem interleavedHybridGameOn_step_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (split n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    Pr[interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary split n] -
        Pr[interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n] =
      Pr[cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) false n] -
        Pr[cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) true n] := by
  have hadd :
      ProbComp.eval
        (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) true n) true =
      ProbComp.eval
        (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) false n) true := by
    by_cases hlt : split < adversary.numRounds n
    · have hH0 := eval_interleavedHybridGameOn_split_of_lt valid encOut keyGen encrypt decrypt
        adversary split false n hlt
      have hH1 := eval_interleavedHybridGameOn_split_of_lt valid encOut keyGen encrypt decrypt
        adversary split true n hlt
      simp only [Bool.false_eq_true, ↓reduceIte] at hH0 hH1
      rw [hH0, hH1,
        eval_cca2GameOn_interleavedToSingleAt_of_lt valid encOut keyGen encrypt decrypt decBound
          adversary split true n hlt hdecBound,
        eval_cca2GameOn_interleavedToSingleAt_of_lt valid encOut keyGen encrypt decrypt decBound
          adversary split false n hlt hdecBound]
      refine PMF.bind_apply_add_eq_on_support fun keys _ =>
        PMF.bind_apply_add_eq_on_support fun stMid _ =>
        PMF.bind_apply_add_eq_on_support fun stepOut _ => ?_
      by_cases hcond :
          (stepOut.1.1.isChallenge &&
            valid n keys.1 stepOut.1.1.challengePair.1 stepOut.1.1.challengePair.2) = true
      · simp only [hcond, ↓reduceIte, add_comm]
      · simp only [Bool.not_eq_true] at hcond
        rw [hcond, interleavedHybridAfterStep_eq_of_not_chalValid valid encOut encrypt decrypt
          adversary split n keys.1 keys.2 stMid stepOut.1 hcond]
    · have hle : adversary.numRounds n ≤ split := Nat.le_of_not_lt hlt
      have hle1 : adversary.numRounds n ≤ split + 1 := Nat.le_add_right_of_le hle
      rw [eval_interleavedHybridGameOn_of_le valid encOut keyGen encrypt decrypt adversary
          split n hle,
        eval_interleavedHybridGameOn_of_le valid encOut keyGen encrypt decrypt adversary
          (split + 1) n hle1,
        eval_cca2GameOn_interleavedToSingleAt_of_le valid encOut keyGen encrypt decrypt decBound
          adversary split true n hle,
        eval_cca2GameOn_interleavedToSingleAt_of_le valid encOut keyGen encrypt decrypt decBound
          adversary split false n hle]
  have hreal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hreal
  linarith

/-- Running `interleavedToSingle` in `cca2GameOn` averages `interleavedToSingleAt` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_cca2GameOn_interleavedToSingle {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (interleavedToSingle valid encrypt decBound Q adversary) bit n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (interleavedToSingleAt valid encrypt decBound adversary i.val) bit n)) := by
  have hguess (i : ℕ) :
      (interleavedToSingleAt valid encrypt decBound adversary i).guess =
        (interleavedToSingleAt valid encrypt decBound adversary 0).guess := rfl
  simp only [cca2GameOn, interleavedToSingle, ProbComp.eval_sampleDyadicIndex, hguess,
    runWith_norm, pmf_norm]
  exact PMF.bind_comm _ _ _

/-- **Quantitative signed hybrid gap for interleaved multi-challenge CCA** ([BonehShoup2023],
Theorem 12.1, printed p. 468): when `adversary.numRounds n ≤ Q n`, the signed success-probability
gap of `interleavedCca2GameOn` equals `dyadicSize (Q n)` times the signed 1CCA gap of
`interleavedToSingle`. -/
theorem interleavedCca2GameOn_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : adversary.numRounds n ≤ Q n) :
    Pr[interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary false n] -
        Pr[interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary true n] =
      dyadicSize (Q n) *
        (Pr[cca2GameOn valid encOut keyGen encrypt decrypt
            (interleavedToSingle valid encrypt decBound Q adversary) false n] -
          Pr[cca2GameOn valid encOut keyGen encrypt decrypt
            (interleavedToSingle valid encrypt decBound Q adversary) true n]) := by
  have : NeZero (dyadicSize (Q n)) := ⟨(dyadicSize_pos (Q n)).ne'⟩
  have h0 := eval_interleavedHybridGameOn_zero valid encOut keyGen encrypt decrypt adversary n
  have htop := eval_interleavedHybridGameOn_of_le valid encOut keyGen encrypt decrypt adversary
    (dyadicSize (Q n)) n (hQ.trans (Nat.le_of_lt (lt_dyadicSize (Q n))))
  have hred := Game.succProbability_hybrid_reduction
    (games := fun split =>
      ProbComp.eval
        (interleavedHybridGameOn valid encOut keyGen encrypt decrypt adversary split n))
    (game1 := fun split =>
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) false n))
    (game2 := fun split =>
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (interleavedToSingleAt valid encrypt decBound adversary split) true n))
    (dyadicSize (Q n)) (dyadicSize (Q n)) le_rfl 1
    (fun split _ => by
      rw [one_mul]
      exact interleavedHybridGameOn_step_gap valid encOut keyGen encrypt decrypt decBound adversary
        split n hdecBound)
  simp only [Game.coe_succProbability] at hred
  rw [← h0, ← htop, hred, mul_one, eval_cca2GameOn_interleavedToSingle,
    eval_cca2GameOn_interleavedToSingle]
  simp only [Fin.is_lt, ↓reduceIte]

/-- **Quantitative hybrid advantage bound for interleaved multi-challenge CCA** ([BonehShoup2023],
Theorem 12.1, printed p. 468): when `adversary.numRounds n ≤ Q n`, the interleaved multi-challenge
CCA advantage equals `dyadicSize (Q n)` times the single-challenge 1CCA advantage of
`interleavedToSingle`. -/
theorem advantage_interleavedCca2GameOn {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : InterleavedCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : adversary.numRounds n ≤ Q n) :
    Game.advantage
      (ProbComp.eval
        (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
      (ProbComp.eval
        (interleavedCca2GameOn valid encOut keyGen encrypt decrypt adversary true n)) =
      dyadicSize (Q n) *
        Game.advantage
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (interleavedToSingle valid encrypt decBound Q adversary) false n))
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (interleavedToSingle valid encrypt decBound Q adversary) true n)) := by
  apply NNReal.eq
  simp only [NNReal.coe_mul, Game.coe_advantage, Game.coe_succProbability, NNReal.coe_natCast]
  rw [interleavedCca2GameOn_gap valid encOut keyGen encrypt decrypt decBound Q adversary n
      hdecBound hQ, abs_mul, Nat.abs_cast]

/-- **Single-challenge 1CCA security implies fully adaptive interleaved-query multi-challenge CCA
security** ([BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468) whenever `valid`,
`keyGen`, `encrypt`, and `decrypt` are polynomial-time / strict PPT. -/
theorem INDCCA2On.indcca2InterleavedOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2InterleavedOn valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := exists_decryption_length_bound hkeyGen hdecrypt
  obtain ⟨cq, dq, hlenQ⟩ := hA.numRounds.polyBounded_length.exists_le
  let Q : ℕ → ℕ := fun n => cq * (n + 1) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; exact (by fun_prop)
  have hQ (n : ℕ) : adversary.numRounds n ≤ Q n := by
    simpa [Q, encUnary_apply] using hlenQ n
  have hsingleNeg := h (interleavedToSingle valid encrypt decBound Q adversary)
    (isPPT_interleavedToSingle hvalid hencrypt hdecBoundPoly hQPoly hA)
  negligible using fun n => (advantage_interleavedCca2GameOn valid encOut keyGen encrypt decrypt
    decBound Q adversary n (hdecBound n) (hQ n)).le

/-- **Equivalence of single-challenge 1CCA and fully adaptive interleaved-query multi-challenge CCA
security** ([BonehShoup2023], Section 12.1, Theorem 12.1 together with Definition 12.2, printed
p. 468). -/
theorem indcca2InterleavedOn_iff_indcca2On {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2InterleavedOn valid encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2On valid encMsg encOut keyGen encrypt decrypt :=
  ⟨INDCCA2InterleavedOn.indcca2On,
    INDCCA2On.indcca2InterleavedOn hvalid hkeyGen hencrypt hdecrypt⟩

/-- **Equivalence of phased batch-challenge multi-challenge CCA and fully adaptive interleaved-query
multi-challenge CCA security** ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Theorem 12.1,
printed pp. 467–468). -/
theorem indcca2InterleavedOn_iff_indcca2MultiOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2InterleavedOn valid encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt :=
  (indcca2InterleavedOn_iff_indcca2On hvalid hkeyGen hencrypt hdecrypt).trans
    (indcca2MultiOn_iff_indcca2On hvalid hkeyGen hencrypt hdecrypt).symm

/-- **Unrestricted single-challenge 1CCA security implies unrestricted interleaved multi-challenge
CCA security** ([BonehShoup2023], Theorem 12.1). -/
theorem INDCCA2Of.indcca2InterleavedOf {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCCA2InterleavedOf encMsg encOut keyGen encrypt decrypt :=
  INDCCA2On.indcca2InterleavedOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt h

/-- **Bit single-challenge 1CCA security implies bit interleaved multi-challenge CCA security**
([BonehShoup2023], Theorem 12.1). -/
theorem INDCCA2.indcca2Interleaved
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBool))
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCCA2Interleaved keyGen encrypt decrypt :=
  INDCCA2Of.indcca2InterleavedOf hkeyGen hencrypt hdecrypt h

/-- **Word single-challenge 1CCA security implies word interleaved multi-challenge CCA security**
([BonehShoup2023], Theorem 12.1). -/
theorem WordINDCCA2.wordINDCCA2Interleaved
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBits))
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCCA2Interleaved keyGen encrypt decrypt :=
  INDCCA2On.indcca2InterleavedOn (by fun_prop) hkeyGen hencrypt hdecrypt h

end Cslib.Crypto.Encryption
