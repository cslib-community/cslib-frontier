/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.Encryption.CCA
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Crypto.Encoding
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Replay
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
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
  security (by directly simulating a batch adversary across `Q n + 1` interleaved rounds via
  saved-coin replay of Phase 1).
* `Cslib.Crypto.Encryption.interleavedHybridGameOn_step_gap`,
  `Cslib.Crypto.Encryption.interleavedCca2GameOn_gap`,
  `Cslib.Crypto.Encryption.advantage_interleavedCca2GameOn`,
  `Cslib.Crypto.Encryption.INDCCA2On.indcca2InterleavedOn`,
  `Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2On.indcca2MultiOn`,
  `Cslib.Crypto.Encryption.indcca2MultiOn_iff_indcca2On`,
  `Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2MultiOn`:
  single-challenge 1CCA security implies fully adaptive interleaved-query multi-challenge CCA
  security ([BonehShoup2023], Theorem 12.1), with exact hybrid advantage scaling `dyadicSize (Q n)`,
  and consequently implies phased batch-challenge multi-challenge CCA security as a corollary.

The Multiplicative Cramer–Shoup instances
`Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup` and
`Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup` are in
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
  ComputableInPolyTime.bitsTakeWithInput
  ComputableInPolyTime.cons'
  ComputableInPolyTime.listAppend'
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

/-! ### Direct simulation of phased batch-challenge CCA inside interleaved CCA -/

private abbrev RawDecSpec : OracleSpec (Unit × List Bool) := fun _ => List Bool

private def liftRawDec {α : Type} (T : OracleComp RawDecSpec α) : WordOracleComp Unit α :=
  OracleComp.interpret (fun q => ProbOracleComp.query q) T

private theorem liftRawDec_liftBind {α : Type} (q : Unit × List Bool)
    (cont : List Bool → OracleComp RawDecSpec α) :
    liftRawDec (.liftBind q cont) =
      (ProbOracleComp.query q >>= fun r => liftRawDec (cont r)) := by
  change OracleComp.interpret (fun q => ProbOracleComp.query q)
    (OracleComp.query (spec := RawDecSpec) q >>= cont) = _
  rw [OracleComp.interpret_bind, OracleComp.interpret_query]
  rfl

private def evalAndRecord {α : Type} (f : Unit × List Bool → List Bool) :
    OracleComp RawDecSpec α → α × List (List Bool)
  | .pure a => (a, [])
  | .liftBind q cont =>
    let out := evalAndRecord f (cont (f q))
    (out.1, f q :: out.2)

private def replayWithReplies {α : Type} :
    OracleComp RawDecSpec α → List (List Bool) → α
  | .pure a, _ => a
  | .liftBind _ cont, rs => replayWithReplies (cont (rs.headD [])) rs.tail

private theorem replayWithReplies_evalAndRecord {α : Type}
    (f : Unit × List Bool → List Bool) (T : OracleComp RawDecSpec α) :
    replayWithReplies T (evalAndRecord f T).2 = (evalAndRecord f T).1 := by
  induction T with
  | pure _ => rfl
  | liftBind q cont ih => exact ih (f q)

private theorem replayWithReplies_mem_support {α : Type}
    (T : OracleComp RawDecSpec α) (rs : List (List Bool)) :
    replayWithReplies T rs ∈ OracleComp.support (liftRawDec T) := by
  induction T generalizing rs with
  | pure a => simp [replayWithReplies, liftRawDec]
  | liftBind q cont ih =>
    rw [replayWithReplies, liftRawDec_liftBind]
    exact OracleComp.mem_supportWith_bind_iff.mpr
      ⟨rs.headD [], by simp [ProbOracleComp.query], ih (rs.headD []) rs.tail⟩

private theorem runCoins_eq_liftRawDec {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit) (coins input : List Bool) :
    (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins input :
      WordOracleComp Unit (List Bool)) =
      liftRawDec (machine.runCoins
        (fun op word => OracleComp.query (spec := RawDecSpec) (op, word)) coins input) := by
  simp only [liftRawDec, Turing.MultiTapePTM.interpret_runCoins, OracleComp.interpret_query]

private def popReplyHandler (_request : Unit × List Bool) :
    StateT (List (List Bool)) ProbComp (List Bool) := fun rem =>
  pure (rem.headD [], rem.tail)

private theorem run_interpret_popReplyHandler_liftRawDec {α : Type}
    (T : OracleComp RawDecSpec α) (rs : List (List Bool)) :
    Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) popReplyHandler)
      (liftRawDec T)).run rs =
    (pure (replayWithReplies T rs) : ProbComp α) := by
  induction T generalizing rs with
  | pure a => rfl
  | liftBind q cont ih =>
    rw [liftRawDec_liftBind, OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.query, OracleComp.interpret_query, OracleComp.sumHandler_inr]
    dsimp only [StateT.run, popReplyHandler, replayWithReplies]
    rw [pure_bind]
    exact ih (rs.headD []) rs.tail

private def recordDecHandler (decBound : List Bool → ℕ) (request : Unit × List Bool) :
    StateT (List (List Bool)) (WordOracleComp Unit) (List Bool) := fun revReplies =>
  (fun reply => (reply, reply :: revReplies)) <$>
    (List.take (decBound request.2) <$> ProbOracleComp.query ((), request.2))

private theorem run_interpret_recordDecHandler_liftRawDec {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ) (n : ℕ) (sk : List Bool)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (T : OracleComp RawDecSpec α) (revReplies : List (List Bool)) (u : Unit) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (recordDecHandler decBound))
        (liftRawDec T)).run revReplies)).run u =
    pure (let out := evalAndRecord (fun q => encOption encOut (decrypt n sk q.2)) T
          ((out.1, out.2.reverse ++ revReplies), u)) := by
  induction T generalizing revReplies u with
  | pure a => simp [liftRawDec, evalAndRecord]
  | liftBind q cont ih =>
    rcases q with ⟨⟨⟩, req⟩
    rw [liftRawDec_liftBind, OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.query, OracleComp.interpret_query, OracleComp.sumHandler_inr]
    have hq : (recordDecHandler decBound (PUnit.unit, req)).run revReplies =
        ((fun reply => (List.take (decBound req) reply,
          List.take (decBound req) reply :: revReplies)) <$>
          ProbOracleComp.query ((), req)) := by
      simp only [recordDecHandler, StateT.run, Functor.map_map]
    rw [hq, OracleComp.interpret_bind, StateT.run_bind,
      OracleComp.interpret_map, StateT.run_map, ProbOracleComp.query, OracleComp.interpret_query]
    have hsum :
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n sk) (Sum.inr ((), req))).run u =
        pure (encOption encOut (decrypt n sk req), u) := rfl
    rw [hsum, map_pure, pure_bind]
    simp only [List.take_of_length_le (hdecBound req), evalAndRecord, List.reverse_cons,
      List.append_assoc, List.singleton_append]
    exact ih (encOption encOut (decrypt n sk req))
      (encOption encOut (decrypt n sk req) :: revReplies) u

private theorem mem_support_of_mem_support_run_interpret_state {State α : Type}
    (handler : Unit × List Bool → StateT State (WordOracleComp Unit) (List Bool))
    (prog : WordOracleComp Unit α) (init : State) {result : α} {final : State}
    (h : (result, final) ∈ OracleComp.support ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        handler)
      prog).run init)) :
    result ∈ OracleComp.support prog := by
  obtain ⟨Ext, oracle, s, s', hrun⟩ := ProbOracleComp.mem_support_iff_exists.mp h
  rw [ProbOracleComp.run_interpret_run_interpret, PMF.mem_support_map_iff] at hrun
  obtain ⟨⟨r, _, _⟩, hmem, heq⟩ := hrun
  obtain rfl : r = result := (Prod.mk.inj (Prod.mk.inj heq).1).1
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  exact ProbOracleComp.mem_support_of_mem _ hmem

private def padCoins (m : ℕ) (coins : List Bool) : List Bool :=
  (coins ++ encUnary m).take m

private theorem length_padCoins (m : ℕ) (coins : List Bool) :
    (padCoins m coins).length = m := by
  simp only [padCoins, encUnary_apply, List.length_take, List.length_append,
    List.length_replicate]
  omega

private theorem padCoins_of_length_eq {m : ℕ} {coins : List Bool} (h : coins.length = m) :
    padCoins m coins = coins := by
  simp only [padCoins, List.take_append_of_le_length h.ge, List.take_of_length_le h.le]

private def chooseClock (c d n : ℕ) (pk : List Bool) : ℕ :=
  c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d

private noncomputable def decodeChoiceWord {Msg : Type}
    (encMsg : Msg ↪ List Bool) (w : List Bool) : List (Msg × Msg) × List Bool := by
  classical
  exact if h : ∃ ch : List (Msg × Msg) × List Bool,
      encPair (encList (encPair encMsg encMsg)) encBits ch = w then
    Classical.choose h
  else
    ([], [])

private theorem decodeChoiceWord_enc {Msg : Type} (encMsg : Msg ↪ List Bool)
    (ch : List (Msg × Msg) × List Bool) :
    decodeChoiceWord encMsg (encPair (encList (encPair encMsg encMsg)) encBits ch) = ch := by
  unfold decodeChoiceWord
  split_ifs with hex
  · exact (encPair (encList (encPair encMsg encMsg)) encBits).inj' (Classical.choose_spec hex)
  · exact False.elim (hex ⟨ch, rfl⟩)

private theorem enc_decodeChoiceWord_of_exists {Msg : Type} (encMsg : Msg ↪ List Bool)
    {w : List Bool}
    (hw : ∃ ch : List (Msg × Msg) × List Bool,
      encPair (encList (encPair encMsg encMsg)) encBits ch = w) :
    encPair (encList (encPair encMsg encMsg)) encBits (decodeChoiceWord encMsg w) = w := by
  obtain ⟨ch, rfl⟩ := hw
  rw [decodeChoiceWord_enc]

private theorem exists_choice_of_mem_support_runCoins {Msg : Type}
    {encMsg : Msg ↪ List Bool} {adversary : MultiCCA2AdversaryOf Msg}
    {k : ℕ} {Control : Type} {machine : Turing.MultiTapePTM k Bool Control Unit} {c d : ℕ}
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s)
    (n : ℕ) (pk coins : List Bool) {w : List Bool}
    (hw : w ∈ OracleComp.support
      (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
        (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk)) :
        WordOracleComp Unit (List Bool))) :
    ∃ ch : List (Msg × Msg) × List Bool,
      encPair (encList (encPair encMsg encMsg)) encBits ch = w := by
  obtain ⟨Store, oracle, s, s', hmem⟩ :=
    (ProbOracleComp.mem_support_iff_exists (hne := fun _ => ⟨[]⟩)).mp hw
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  have hcoins : padCoins (chooseClock c d n pk) coins ∈
      (BitString.uniformList (chooseClock c d n pk)).support :=
    BitString.mem_support_uniformList_iff.mpr (length_padCoins _ _)
  have hbind : (w, s') ∈ ((BitString.uniformList (chooseClock c d n pk)).bind fun cs =>
      ProbOracleComp.runWith oracle
        (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
          cs (encPair encUnary encBits (n, pk))) s).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, hcoins, hmem⟩
  rw [chooseClock, ← hCoinsEq (n, pk) Store oracle s, ProbOracleComp.runWith_map,
    PMF.mem_support_map_iff] at hbind
  obtain ⟨⟨ch, _⟩, -, heq⟩ := hbind
  exact ⟨ch, (Prod.mk.inj heq).1⟩

private noncomputable def chooseAndRecordWord {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decBound : ℕ → List Bool → ℕ) (n : ℕ) (pk : List Bool) :
    WordOracleComp Unit (List Bool × List Bool × List (List Bool)) := do
  let m := chooseClock c d n pk
  let coins ← ProbOracleComp.sample (BitString.sampleList m)
  (fun out => (out.1, coins, out.2.reverse)) <$>
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
        (recordDecHandler (decBound n)))
      (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
        (padCoins m coins) (encPair encUnary encBits (n, pk)))).run []

private noncomputable def chooseAndRecord {Msg : Type} {k : ℕ} {Control : Type}
    (encMsg : Msg ↪ List Bool) (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decBound : ℕ → List Bool → ℕ) (n : ℕ) (pk : List Bool) :
    WordOracleComp Unit ((List (Msg × Msg) × List Bool) × List Bool × List (List Bool)) :=
  (fun (w, coins, replies) => (decodeChoiceWord encMsg w, coins, replies)) <$>
    chooseAndRecordWord machine c d decBound n pk

private theorem isOraclePPTOn_chooseAndRecordWord {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary) :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits)
      (encPair encBits (encPair encBits (encList encBits)))
      (fun p : ℕ × List Bool => chooseAndRecordWord machine c d decBound p.1 p.2) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hclock : ComputableInPolyTime (fun p : ℕ × List Bool => chooseClock c d p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    have hin : ComputableInPolyTime
        (fun p : ℕ × List Bool => encPair encUnary encBits p)
        (encPair encUnary encBits) encBits := ComputableInPolyTime.id'.encoding_comp
    dsimp only [chooseClock]
    fun_prop
  have hsample : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        ProbOracleComp.sample (BitString.sampleList (chooseClock c d p.1 p.2))) := by
    fun_prop
  have hprep : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List Bool =>
        (padCoins (chooseClock c d q.1.1 q.1.2) q.2, encPair encUnary encBits q.1))
      ECaller (encPair encBits encBits) := by
    have hin : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × List Bool => encPair encUnary encBits q.1)
        ECaller encBits := (ComputableInPolyTime.fst _ _).encoding_comp
    have hcut : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × List Bool => chooseClock c d q.1.1 q.1.2)
        ECaller encUnary := hclock.comp (ComputableInPolyTime.fst _ _)
    have hpad : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × List Bool => padCoins (chooseClock c d q.1.1 q.1.2) q.2)
        ECaller encBits := by
      have hrep : ComputableInPolyTime
          (fun q : (ℕ × List Bool) × List Bool => encUnary (chooseClock c d q.1.1 q.1.2))
          ECaller encBits := hcut.encoding_comp
      dsimp only [padCoins]
      exact ComputableInPolyTime.bitsTakeWithInput (by fun_prop) hcut
    exact hpad.prod hin
  have hres : ComputableInPolyTime
      (fun x : ((ℕ × List Bool) × List Bool) × List Bool => 2 * decBound x.1.1.1 x.2 + 2)
      (encPair ECaller encBits) encUnary := by
    have hd : ComputableInPolyTime
        (fun x : ((ℕ × List Bool) × List Bool) × List Bool => decBound x.1.1.1 x.2)
        (encPair ECaller encBits) encUnary :=
      hdecBound.comp (show ComputableInPolyTime (fun x => (x.1.1.1, x.2))
        (encPair ECaller encBits) _ by dsimp only [ECaller]; fun_prop)
    fun_prop
  have hrec : IsOraclePPTOn (Operation := Unit) ECaller
      (encPair encBits (encList encBits))
      (fun q : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
            (recordDecHandler (decBound q.1.1)))
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            (padCoins (chooseClock c d q.1.1 q.1.2) q.2)
            (encPair encUnary encBits q.1))).run []) := by
    refine machine.isOraclePPTOn_runCoins.run_interpret_preprocess_open
      (operationEncoding := encFinEnum Unit) (stateEncoding := encList encBits)
      (prepare := fun q : (ℕ × List Bool) × List Bool =>
        (padCoins (chooseClock c d q.1.1 q.1.2) q.2, encPair encUnary encBits q.1))
      (initial := fun _ => [])
      (resources := fun q req => 2 * decBound q.1.1 req + 2)
      hprep
      (by
        have hlim : ComputableInPolyTime
            (fun x : ((ℕ × List Bool) × List Bool) × (Unit × List Bool) × List (List Bool) =>
              decBound x.1.1.1 x.2.1.2)
            (encHandlerCall ECaller (encFinEnum Unit) (encList encBits)) encUnary :=
          hdecBound.comp (show ComputableInPolyTime (fun x => (x.1.1.1, x.2.1.2))
            (encHandlerCall ECaller (encFinEnum Unit) (encList encBits)) _ by
              dsimp only [ECaller]; fun_prop)
        dsimp only [recordDecHandler]
        exact (IsOraclePPTOn.query_take (Operation := Unit) () (by fun_prop) hlim).map_with
          (by fun_prop))
      (by fun_prop) (fun _ _ => True) (fun _ => trivial) hres
      fun q req revReplies _ result hresult => ?_
    dsimp only [recordDecHandler] at hresult
    supp_cases hresult with ⟨_, ⟨rawReply, -, rfl⟩, rfl⟩
    have htake := List.length_take_le (decBound q.1.1 req.2) rawReply
    dsimp only
    refine ⟨trivial, by omega, ?_⟩
    enc_len
  dsimp only [chooseAndRecordWord]
  exact hsample.bind_with (hrec.map_with
    (output := encPair encBits (encPair encBits (encList encBits)))
    (by dsimp only [ECaller]; fun_prop))

private theorem isOraclePPTOn_chooseAndRecord {Msg : Type}
    {encMsg : Msg ↪ List Bool} {adversary : MultiCCA2AdversaryOf Msg}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s) :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits)
      (encPair (encPair (encList (encPair encMsg encMsg)) encBits)
        (encPair encBits (encList encBits)))
      (fun p : ℕ × List Bool => chooseAndRecord encMsg machine c d decBound p.1 p.2) := by
  apply IsOraclePPTOn.iff_encoded.mpr
  refine (IsOraclePPTOn.iff_encoded.mp
    (isOraclePPTOn_chooseAndRecordWord machine c d hdecBound)).congr ?_
  intro ⟨n, pk⟩ State oracle s
  rw [chooseAndRecord, Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
    PMF.map, PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨w, coins, replies⟩, s'⟩ hmem => ?_
  have hsupp : (w, coins, replies) ∈
      OracleComp.support (chooseAndRecordWord machine c d decBound n pk) :=
    ProbOracleComp.mem_support_of_mem _ hmem
  unfold chooseAndRecordWord at hsupp
  obtain ⟨coins', -, hrec⟩ := OracleComp.mem_supportWith_bind_iff.mp hsupp
  obtain ⟨⟨w', _⟩, hrun, heq⟩ := OracleComp.mem_supportWith_map_iff.mp hrec
  obtain rfl : w = w' := ((Prod.mk.inj heq).1).symm
  have hw := mem_support_of_mem_support_run_interpret_state (recordDecHandler (decBound n)) _ []
    hrun
  have hex := exists_choice_of_mem_support_runCoins hCoinsEq n pk coins' hw
  dsimp only [Function.comp_def, Prod.map_apply, id_eq]
  change PMF.pure (encPair encBits (encPair encBits (encList encBits)) (w, coins, replies), s') =
    PMF.pure (encPair encBits (encPair encBits (encList encBits))
      (encPair (encList (encPair encMsg encMsg)) encBits (decodeChoiceWord encMsg w),
        coins, replies), s')
  rw [enc_decodeChoiceWord_of_exists encMsg hex]

private abbrev encReplayTuple :
    (ℕ × List Bool × List Bool × List (List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits (encList encBits)))

private noncomputable def replayChooseWord {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (n : ℕ) (pk coins : List Bool) (replies : List (List Bool)) :
    WordOracleComp Unit (List Bool) :=
  ProbOracleComp.sample (Prod.fst <$>
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) popReplyHandler)
      (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
        (padCoins (chooseClock c d n pk) coins)
        (encPair encUnary encBits (n, pk)))).run replies)

private noncomputable def replayTypedChoose {Msg : Type} {k : ℕ} {Control : Type}
    (encMsg : Msg ↪ List Bool) (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (n : ℕ) (pk coins : List Bool) (replies : List (List Bool)) :
    WordOracleComp Unit (List (Msg × Msg) × List Bool) :=
  decodeChoiceWord encMsg <$> replayChooseWord machine c d n pk coins replies

private theorem replayTypedChoose_eq_pure {Msg : Type} {k : ℕ} {Control : Type}
    (encMsg : Msg ↪ List Bool) (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (n : ℕ) (pk coins : List Bool) (replies : List (List Bool)) :
    replayTypedChoose encMsg machine c d n pk coins replies =
      pure (decodeChoiceWord encMsg (replayWithReplies
        (machine.runCoins (fun op word => OracleComp.query (spec := RawDecSpec) (op, word))
          (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk)))
        replies)) := by
  simp only [replayTypedChoose, replayChooseWord, runCoins_eq_liftRawDec,
    run_interpret_popReplyHandler_liftRawDec, ProbOracleComp.sample_pure, map_pure]

private theorem isOraclePPTOn_replayChooseWord {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ) :
    IsOraclePPTOn (Operation := Unit) encReplayTuple encBits
      (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
        replayChooseWord machine c d p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hclock : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List (List Bool) => chooseClock c d p.1 p.2.1)
      encReplayTuple encUnary := by
    have hin : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
          encPair encUnary encBits (p.1, p.2.1))
        encReplayTuple encBits := by
      apply ComputableInPolyTime.encoding_comp
      dsimp only [encReplayTuple]; fun_prop
    dsimp only [chooseClock]
    fun_prop
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
        (padCoins (chooseClock c d p.1 p.2.1) p.2.2.1,
          encPair encUnary encBits (p.1, p.2.1)))
      encReplayTuple (encPair encBits encBits) := by
    have hin : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
          encPair encUnary encBits (p.1, p.2.1))
        encReplayTuple encBits := by
      apply ComputableInPolyTime.encoding_comp
      dsimp only [encReplayTuple]; fun_prop
    have hrep : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
          encUnary (chooseClock c d p.1 p.2.1))
        encReplayTuple encBits := hclock.encoding_comp
    have hpad : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
          padCoins (chooseClock c d p.1 p.2.1) p.2.2.1)
        encReplayTuple encBits := by
      dsimp only [padCoins, encReplayTuple]
      exact ComputableInPolyTime.bitsTakeWithInput (by fun_prop) hclock
    exact hpad.prod hin
  have hclosed : IsPPTOn encReplayTuple (encPair encBits (encList encBits))
      (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) popReplyHandler)
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            (padCoins (chooseClock c d p.1 p.2.1) p.2.2.1)
            (encPair encUnary encBits (p.1, p.2.1)))).run p.2.2.2) := by
    refine machine.isOraclePPTOn_runCoins.run_interpret_preprocess
      (operationEncoding := encFinEnum Unit) (stateEncoding := encList encBits)
      (prepare := fun p : ℕ × List Bool × List Bool × List (List Bool) =>
        (padCoins (chooseClock c d p.1 p.2.1) p.2.2.1,
          encPair encUnary encBits (p.1, p.2.1)))
      (initial := fun p => p.2.2.2)
      (resources := fun p _ => (encList encBits p.2.2.2).length)
      hprep
      (by dsimp only [popReplyHandler, encReplayTuple]; fun_prop)
      (by dsimp only [encReplayTuple]; fun_prop)
      (fun p rem => (encList encBits rem).length ≤ (encList encBits p.2.2.2).length)
      (fun _ => le_rfl)
      (by dsimp only [encReplayTuple]; fun_prop)
      fun p _ rem hinv result hresult => ?_
    dsimp only [popReplyHandler] at hresult
    supp_cases hresult
    cases rem with
    | nil => simp
    | cons r rs =>
      simp only [List.headD_cons, List.tail_cons]
      have hhead : r.length ≤ (encList encBits (r :: rs)).length := by enc_len
      have htail : (encList encBits rs).length ≤ (encList encBits (r :: rs)).length := by enc_len
      exact ⟨htail.trans hinv, hhead.trans hinv, (htail.trans (Nat.le_add_right _ _))⟩
  dsimp only [replayChooseWord]
  exact (hclosed.map (ComputableInPolyTime.fst _ _)).isOraclePPTOn

private theorem isOraclePPTOn_replayTypedChoose {Msg : Type}
    {encMsg : Msg ↪ List Bool} {adversary : MultiCCA2AdversaryOf Msg}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ)
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s) :
    IsOraclePPTOn (Operation := Unit) encReplayTuple
      (encPair (encList (encPair encMsg encMsg)) encBits)
      (fun p : ℕ × List Bool × List Bool × List (List Bool) =>
        replayTypedChoose encMsg machine c d p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply IsOraclePPTOn.iff_encoded.mpr
  refine (isOraclePPTOn_replayChooseWord machine c d).congr ?_
  intro ⟨n, pk, coins, replies⟩ State oracle s
  dsimp only
  rw [replayTypedChoose_eq_pure, replayChooseWord, runCoins_eq_liftRawDec,
    run_interpret_popReplyHandler_liftRawDec, ProbOracleComp.sample_pure, map_pure]
  have hmem := replayWithReplies_mem_support
    (machine.runCoins (fun op word => OracleComp.query (spec := RawDecSpec) (op, word))
      (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk))) replies
  rw [← runCoins_eq_liftRawDec] at hmem
  rw [enc_decodeChoiceWord_of_exists encMsg
    (exists_choice_of_mem_support_runCoins hCoinsEq n pk coins hmem)]

/-- Saved inter-round state for `multiToInterleaved` after Round 0. -/
private structure MultiToInterleavedState where
  /-- Whether Phase 1 produced an admissible batch of challenge pairs. -/
  active : Bool
  /-- Whether the immediately preceding round submitted a `.challenge` query. -/
  awaitingReply : Bool
  /-- Index of the next challenge pair to submit (`0 ≤ nextIdx ≤ Q n`). -/
  nextIdx : ℕ
  /-- Saved fair-coin tape for replaying `adversary.choose`. -/
  coins : List Bool
  /-- Saved Phase 1 decryption replies for replaying `adversary.choose`. -/
  replies : List (List Bool)
  /-- Challenge ciphertexts collected prior to the latest pending reply, in reverse order. -/
  revCts : List (List Bool)
  /-- Saved state word `choice.2` from `adversary.choose`. -/
  stateA : List Bool

private enc_structure encMultiToInterleavedState : MultiToInterleavedState where
  active : encBool, awaitingReply : encBool, nextIdx : encUnary, coins : encBits,
  replies : (encList encBits), revCts : (encList encBits), stateA : encBits

private def multiToInterleavedStateDecoder : Decoder encMultiToInterleavedState :=
  (Decoder.bool.pair (Decoder.bool.pair (Decoder.unary.pair (Decoder.bits.pair
    ((Decoder.list Decoder.bits).pair
      ((Decoder.list Decoder.bits).pair Decoder.bits)))))).map
    (fun (active, awaitingReply, nextIdx, coins, replies, revCts, stateA) =>
      ⟨active, awaitingReply, nextIdx, coins, replies, revCts, stateA⟩)
    (fun s => (s.active, s.awaitingReply, s.nextIdx, s.coins, s.replies, s.revCts, s.stateA))
    (fun _ => rfl) (fun _ => rfl)

private def rejectMultiToInterleavedWord : List Bool :=
  true :: encMultiToInterleavedState ⟨false, false, 0, [], [], [], []⟩

@[simp] private theorem isEmpty_rejectMultiToInterleavedWord :
    rejectMultiToInterleavedWord.isEmpty = false := rfl

@[simp] private theorem decode_rejectMultiToInterleavedWord_tail :
    multiToInterleavedStateDecoder.decode rejectMultiToInterleavedWord.tail =
      ⟨false, false, 0, [], [], [], []⟩ :=
  multiToInterleavedStateDecoder.decode_enc ⟨false, false, 0, [], [], [], []⟩

private abbrev EMultiStepIn :
    (ℕ × List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))

private noncomputable def rawMultiStep {Msg : Type} [Inhabited Msg]
    (encMsg : Msg ↪ List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decBound : ℕ → List Bool → ℕ)
    (p : ℕ × List Bool × List Bool × List Bool) :
    WordOracleComp Unit (CCAQuery Msg (List Bool) × List Bool) :=
  let n := p.1
  let pk := p.2.1
  let state := p.2.2.1
  let lastReply := p.2.2.2
  if state.isEmpty then do
    let recOut ← chooseAndRecord encMsg machine c d decBound n pk
    if recOut.1.1.all (fun q => valid n pk q.1 q.2) then
      return (.decrypt [],
        true :: encMultiToInterleavedState
          ⟨true, false, 0, recOut.2.1, recOut.2.2, [], recOut.1.2⟩)
    else
      return (.decrypt [], rejectMultiToInterleavedWord)
  else
    let decoded := multiToInterleavedStateDecoder.decode state.tail
    let revCts := if decoded.awaitingReply then lastReply.tail :: decoded.revCts else decoded.revCts
    if decoded.active then do
      let choice ← replayTypedChoose encMsg machine c d n pk decoded.coins decoded.replies
      if decide (decoded.nextIdx < choice.1.length) then
        let pair := choice.1.getD decoded.nextIdx (default, default)
        return (.challenge pair.1 pair.2,
          true :: encMultiToInterleavedState
            ⟨true, true, decoded.nextIdx + 1, decoded.coins, decoded.replies, revCts,
              decoded.stateA⟩)
      else
        return (.decrypt [],
          true :: encMultiToInterleavedState
            ⟨true, false, decoded.nextIdx + 1, decoded.coins, decoded.replies, revCts,
              decoded.stateA⟩)
    else
      pure (.decrypt [], rejectMultiToInterleavedWord)

/-- Embed a phased batch-challenge `MultiCCA2AdversaryOf Msg` as a `(Q n + 1)`-round
`InterleavedCCA2AdversaryOf Msg`:
* Round `0` (`state.isEmpty`) runs `chooseAndRecord` (executing `adversary.choose` against
  `cca2MultiPhase2Oracle ... [] = cca2Phase1Oracle` while recording its coins and replies), checks
  batch admissibility `choice.1.all (valid n pk ...)`, and emits `.decrypt []` (leaving `S = []`).
* Rounds `1 .. Q n` deterministically replay `adversary.choose` from the saved coins and replies,
  submit each pair in `choice.1` one by one as `.challenge m₀ m₁` (accumulating the returned
  ciphertexts in reverse order), and pad any remaining rounds `< Q n` with `.decrypt []`.
* `finish` reverses the accumulated ciphertexts `cts` (so `cts` matches `List.mapM (encrypt ...)`
  and has the same elements as `S`) and runs `adversary.guess n stateA cts`. -/
private noncomputable def multiToInterleaved {Msg : Type} [Inhabited Msg]
    (encMsg : Msg ↪ List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decBound stateCap ctBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) : InterleavedCCA2AdversaryOf Msg where
  numRounds n := Q n + 1
  step n pk state lastReply :=
    rawMultiStep encMsg valid machine c d decBound
      (n, pk, state.take (stateCap n pk), lastReply.take (ctBound n pk + 1))
  finish n pk state lastReply :=
    if state.isEmpty then
      pure false
    else
      let decoded := multiToInterleavedStateDecoder.decode state.tail
      if decoded.active then
        let revCts :=
          if decoded.awaitingReply then
            (lastReply.take (ctBound n pk + 1)).tail :: decoded.revCts
          else
            decoded.revCts
        adversary.guess n decoded.stateA revCts.reverse
      else
        pure false

private theorem isOraclePPTOn_rawMultiStep {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {adversary : MultiCCA2AdversaryOf Msg}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) {decBound : ℕ → List Bool → ℕ}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s) :
    IsOraclePPTOn (Operation := Unit) EMultiStepIn
      (encPair (encCCAQuery encMsg) encBits)
      (rawMultiStep encMsg valid machine c d decBound) := by
  have hrec := (isOraclePPTOn_chooseAndRecord machine c d hdecBound hCoinsEq).preprocess
    (input := EMultiStepIn)
    (prepare := fun p : ℕ × List Bool × List Bool × List Bool => (p.1, p.2.1))
    (by dsimp only [EMultiStepIn]; fun_prop)
  have hrep := (isOraclePPTOn_replayTypedChoose machine c d hCoinsEq).preprocess
    (input := EMultiStepIn)
    (prepare := fun p : ℕ × List Bool × List Bool × List Bool =>
      let decoded := multiToInterleavedStateDecoder.decode p.2.2.1.tail
      (p.1, p.2.1, decoded.coins, decoded.replies))
    (by dsimp only [EMultiStepIn, encReplayTuple]; fun_prop)
  unfold rawMultiStep
  refine IsOraclePPTOn.cond (by dsimp only [EMultiStepIn]; fun_prop) (hrec.bind_with ?_) ?_
  · refine IsOraclePPTOn.cond (by dsimp only [EMultiStepIn]; fun_prop)
      (by dsimp only [EMultiStepIn]; fun_prop) (by dsimp only [EMultiStepIn]; fun_prop)
  · refine IsOraclePPTOn.cond (by dsimp only [EMultiStepIn]; fun_prop)
      (hrep.bind_with ?_) (by dsimp only [EMultiStepIn]; fun_prop)
    refine IsOraclePPTOn.cond (by dsimp only [EMultiStepIn]; fun_prop)
      (by dsimp only [EMultiStepIn]; fun_prop) (by dsimp only [EMultiStepIn]; fun_prop)

private theorem isPPT_multiToInterleaved {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ)
    {decBound stateCap ctBound : ℕ → List Bool → ℕ} {Q : ℕ → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hstateCap : ComputableInPolyTime (fun p : ℕ × List Bool => stateCap p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hctBound : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hA : adversary.IsPPT encMsg)
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s) :
    (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q
      adversary).IsPPT encMsg where
  numRounds := by
    dsimp only [multiToInterleaved]
    fun_prop
  step := by
    have hraw := isOraclePPTOn_rawMultiStep machine c d hvalid hdecBound hCoinsEq
    exact hraw.preprocess (input := EMultiStepIn)
      (prepare := fun p : ℕ × List Bool × List Bool × List Bool =>
        (p.1, p.2.1, p.2.2.1.take (stateCap p.1 p.2.1), p.2.2.2.take (ctBound p.1 p.2.1 + 1)))
      (by dsimp only [EMultiStepIn]; fun_prop)
  finish := by
    have hguess := hA.guess.preprocess (input := EMultiStepIn)
      (prepare := fun p : ℕ × List Bool × List Bool × List Bool =>
        let decoded := multiToInterleavedStateDecoder.decode p.2.2.1.tail
        let revCts :=
          if decoded.awaitingReply then
            (p.2.2.2.take (ctBound p.1 p.2.1 + 1)).tail :: decoded.revCts
          else
            decoded.revCts
        (p.1, decoded.stateA, revCts.reverse))
      (by dsimp only [EMultiStepIn]; fun_prop)
    dsimp only [multiToInterleaved]
    exact IsOraclePPTOn.cond (by fun_prop) (by fun_prop)
      (IsOraclePPTOn.cond (by fun_prop) hguess (by fun_prop))
  step_length_le := by
    obtain ⟨cS, dS, hlenS⟩ :=
      (isOraclePPTOn_rawMultiStep machine c d hvalid hdecBound hCoinsEq).length_le
    obtain ⟨cCap, dCap, hsc⟩ := hstateCap.polyBounded_length.exists_le
    obtain ⟨cCt, dCt, hct⟩ := hctBound.polyBounded_length.exists_le
    let stepCap (npk : ℕ × List Bool) : ℕ :=
      cS * (2 * npk.1 + 2 * npk.2.length +
        2 * (cCap * (2 * npk.1 + npk.2.length + 2) ^ dCap) +
        cCt * (2 * npk.1 + npk.2.length + 2) ^ dCt + 10) ^ dS
    have hpoly : PolyBounded (fun npk : ℕ × List Bool => npk.1 + npk.2.length) stepCap := by
      have hn : PolyBounded (fun npk : ℕ × List Bool => npk.1 + npk.2.length) Prod.fst :=
        PolyBounded.self.mono fun npk => Nat.le_add_right _ _
      have hpk : PolyBounded (fun npk : ℕ × List Bool => npk.1 + npk.2.length)
          (fun npk => npk.2.length) :=
        PolyBounded.self.mono fun npk => Nat.le_add_left _ _
      unfold stepCap
      growth_poly
    obtain ⟨cs, ds, hcs⟩ := hpoly.exists_le
    refine ⟨cs * 2 ^ ds, ds, fun n pk state lastReply out hout => ?_⟩
    have hcapLe : stepCap (n, pk) ≤ cs * 2 ^ ds * (n + pk.length + 2) ^ ds := by
      have h1 := hcs (n, pk)
      have h2 : n + pk.length + 1 ≤ 2 * (n + pk.length + 2) := by omega
      have h3 := Nat.mul_le_mul_left cs (Nat.pow_le_pow_left h2 ds)
      rw [Nat.mul_pow, ← Nat.mul_assoc] at h3
      exact h1.trans h3
    refine le_trans ?_ hcapLe
    dsimp only [multiToInterleaved] at hout
    obtain ⟨State, oracle, s, s', hmem⟩ :=
      (ProbOracleComp.mem_support_iff_exists (hne := fun _ => ⟨[]⟩)).mp hout
    rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
    have h0 := hlenS (n, pk, state.take (stateCap n pk), lastReply.take (ctBound n pk + 1))
      State oracle s s' out hmem
    have hsc0 := hsc (n, pk)
    have hct0 := hct (n, pk)
    simp only [EMultiStepIn, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply] at h0 hsc0 hct0 ⊢
    have hts := List.length_take_le (stateCap n pk) state
    have htr := List.length_take_le (ctBound n pk + 1) lastReply
    have hsc1 : stateCap n pk ≤ cCap * (2 * n + pk.length + 2) ^ dCap :=
      hsc0.trans (Nat.mul_le_mul_left cCap (Nat.pow_le_pow_left (by omega) dCap))
    have hct1 : ctBound n pk ≤ cCt * (2 * n + pk.length + 2) ^ dCt :=
      hct0.trans (Nat.mul_le_mul_left cCt (Nat.pow_le_pow_left (by omega) dCt))
    dsimp only [stepCap]
    refine h0.trans (Nat.mul_le_mul_left cS (Nat.pow_le_pow_left ?_ dS))
    omega

private theorem runWith_phase1_liftRawDec {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (T : OracleComp RawDecSpec α) (u : Unit) :
    ProbOracleComp.runWith
      (fun q s => ProbComp.eval (cca2Phase1Oracle encOut decrypt n sk q s))
      (liftRawDec T) u =
    PMF.pure ((evalAndRecord (fun q => encOption encOut (decrypt n sk q.2)) T).1, u) := by
  induction T generalizing u with
  | pure a => simp [liftRawDec, evalAndRecord]
  | liftBind q cont ih =>
    rcases q with ⟨⟨⟩, req⟩
    rw [liftRawDec_liftBind, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    simp only [cca2Phase1Oracle, ProbComp.eval_pure, PMF.pure_bind, evalAndRecord]
    exact ih (encOption encOut (decrypt n sk req)) u

private theorem eval_chooseAndRecord_eq_bind_coins {Msg Out : Type}
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (pk sk : List Bool)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (chooseAndRecord encMsg machine c d decBound n pk)).run ()) =
    (BitString.uniformList (chooseClock c d n pk)).map fun coins =>
      let T := machine.runCoins (fun op word => OracleComp.query (spec := RawDecSpec) (op, word))
        (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk))
      let out := evalAndRecord (fun q => encOption encOut (decrypt n sk q.2)) T
      ((decodeChoiceWord encMsg out.1, coins, out.2), ()) := by
  unfold chooseAndRecord chooseAndRecordWord
  simp only [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map,
    OracleComp.interpret_bind, StateT.run_bind, ProbComp.eval_bind,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_sample,
    BitString.eval_sampleList, PMF.bind_map, PMF.map_bind]
  rw [PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
  dsimp only [Function.comp_def]
  rw [← ProbOracleComp.eval_run_interpret_eq_runWith, runCoins_eq_liftRawDec,
    run_interpret_recordDecHandler_liftRawDec encOut decrypt (decBound n) n sk hdecBound]
  simp only [ProbComp.eval_pure, PMF.pure_map, List.append_nil, List.reverse_reverse]

private theorem map_fst_eval_chooseAndRecord_eq {Msg Out : Type}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {adversary : MultiCCA2AdversaryOf Msg}
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (pk sk : List Bool)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req)
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s) :
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (chooseAndRecord encMsg machine c d decBound n pk)).run ())).map (fun x => x.1.1) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (adversary.choose n pk)).run ())).map Prod.fst := by
  have heq := congrArg (PMF.map (fun x => decodeChoiceWord encMsg x.1))
    (hCoinsEq (n, pk) Unit (fun q s => ProbComp.eval (cca2Phase1Oracle encOut decrypt n sk q s)) ())
  rw [ProbOracleComp.runWith_map, PMF.map_comp] at heq
  have hlhs :
      ((ProbOracleComp.runWith (fun q s => ProbComp.eval (cca2Phase1Oracle encOut decrypt n sk q s))
        (adversary.choose n pk) ()).map
        ((fun x => decodeChoiceWord encMsg x.1) ∘
          Prod.map (encPair (encList (encPair encMsg encMsg)) encBits) id)) =
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n sk))
        (adversary.choose n pk)).run ())).map Prod.fst := by
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    refine congrArg (fun f => PMF.map f _) (funext fun ⟨ch, ⟨⟩⟩ => ?_)
    dsimp only [Function.comp_def, Prod.map_apply, id_eq]
    exact decodeChoiceWord_enc encMsg ch
  rw [hlhs, PMF.map_bind] at heq
  rw [eval_chooseAndRecord_eq_bind_coins encMsg encOut machine c d decrypt decBound n pk sk
    hdecBound, PMF.map_comp, heq, PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
  have hlen : coins.length = chooseClock c d n pk :=
    BitString.length_of_mem_support_uniformList hcoins
  dsimp only [Function.comp_def]
  rw [chooseClock] at hlen ⊢
  rw [padCoins_of_length_eq hlen, runCoins_eq_liftRawDec, runWith_phase1_liftRawDec, PMF.pure_map]

private theorem eval_iterate_rejectMultiToInterleavedWord {Msg Out : Type} [Inhabited Msg]
    (encMsg : Msg ↪ List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound stateCap ctBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg)
    (n : ℕ) (pk sk : List Bool) (bit : Bool)
    (hrejCap : rejectMultiToInterleavedWord.length ≤ stateCap n pk)
    (rounds : ℕ) (lastReply : List Bool) :
    ProbComp.eval (do
      let finalSt ← OracleComp.iterate rounds
        (interleavedRoundStep valid encOut encrypt decrypt
          (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
          n pk sk bit)
        (rejectMultiToInterleavedWord, lastReply, [])
      let guessOut ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2MultiPhase2Oracle encOut decrypt n sk finalSt.forbidden))
        ((multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary).finish
          n pk finalSt.state finalSt.lastReply)).run ()
      return guessOut.1) =
    PMF.pure false := by
  induction rounds generalizing lastReply with
  | zero =>
    rw [OracleComp.iterate_zero, pure_bind]
    dsimp only [multiToInterleaved, InterleavedLoopState.state]
    rw [isEmpty_rejectMultiToInterleavedWord, decode_rejectMultiToInterleavedWord_tail]
    simp [OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure]
  | succ rounds ih =>
    rw [OracleComp.iterate_succ_bind, bind_assoc]
    have hstep : interleavedRoundStep valid encOut encrypt decrypt
        (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
        n pk sk bit (rejectMultiToInterleavedWord, lastReply, []) =
      pure (rejectMultiToInterleavedWord, encOption encOut (decrypt n sk []), []) := by
      unfold interleavedRoundStep multiToInterleaved rawMultiStep
      dsimp only [InterleavedLoopState.state, InterleavedLoopState.lastReply,
        InterleavedLoopState.forbidden]
      rw [List.take_of_length_le hrejCap, isEmpty_rejectMultiToInterleavedWord,
        decode_rejectMultiToInterleavedWord_tail]
      simp [OracleComp.interpret_pure, StateT.run_pure, interleavedCcaWordOracle,
        interleavedCcaOracle]
    rw [hstep, pure_bind]
    exact ih _

private theorem mapM_length_and_cap {α : Type} {f : α → ProbComp (List Bool)} {cap : ℕ}
    {xs : List α} {cts : List (List Bool)}
    (hcap : ∀ x ∈ xs, ∀ ct ∈ (ProbComp.eval (f x)).support, ct.length ≤ cap)
    (hcts : cts ∈ (ProbComp.eval (xs.mapM f)).support) :
    cts.length = xs.length ∧ ∀ c ∈ cts, c.length ≤ cap := by
  induction xs generalizing cts with
  | nil =>
    simp only [List.mapM_nil, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hcts
    subst hcts
    exact ⟨rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons x xs ih =>
    rw [List.mapM_cons, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcts
    obtain ⟨ct, hct, hcts1⟩ := hcts
    rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcts1
    obtain ⟨cts', hcts', heq⟩ := hcts1
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at heq
    subst heq
    obtain ⟨hlen, hmem⟩ := ih (fun y hy => hcap y (List.mem_cons_of_mem _ hy)) hcts'
    refine ⟨by simp [hlen], fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hcap x (List.mem_cons_self ..) c hct
    · exact hmem c hc'

private def decodeRevCts (ctCap : ℕ) (decoded : MultiToInterleavedState)
    (lastReply : List Bool) : List (List Bool) :=
  if decoded.awaitingReply then
    (lastReply.take (ctCap + 1)).tail :: decoded.revCts
  else
    decoded.revCts

private theorem eval_iterate_active_multiToInterleaved {Msg Out : Type} [Inhabited Msg]
    (encMsg : Msg ↪ List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound stateCap ctBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg)
    (n : ℕ) (pk sk : List Bool) (bit : Bool)
    (choice : List (Msg × Msg) × List Bool)
    (coins : List Bool) (replies : List (List Bool))
    (hall : choice.1.all (fun p => valid n pk p.1 p.2) = true)
    (hstateCap : ∀ (aw : Bool) (idx : ℕ) (rev : List (List Bool)),
      idx ≤ Q n → (encList encBits rev).length ≤ (2 * ctBound n pk + 2) * Q n →
        (true :: encMultiToInterleavedState
          ⟨true, aw, idx, coins, replies, rev, choice.2⟩).length ≤ stateCap n pk)
    (hreplay : decodeChoiceWord encMsg (replayWithReplies
      (machine.runCoins (fun op word => OracleComp.query (spec := RawDecSpec) (op, word))
        (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk)))
      replies) = choice)
    (hctCap : ∀ p ∈ choice.1,
      ∀ ct ∈ (ProbComp.eval (encrypt n pk (if bit then p.2 else p.1))).support,
        ct.length ≤ ctBound n pk)
    (r : ℕ) (hr : r ≤ Q n) (initReply : List Bool) :
    ∃ stateOf : List (List Bool) → List Bool × List Bool,
      (∀ cts ∈ (ProbComp.eval
          ((choice.1.take r).mapM (fun p => encrypt n pk (if bit then p.2 else p.1)))).support,
        let sr := stateOf cts
        sr.1.isEmpty = false ∧
        sr.1.length ≤ stateCap n pk ∧
        (multiToInterleavedStateDecoder.decode sr.1.tail).active = true ∧
        (multiToInterleavedStateDecoder.decode sr.1.tail).nextIdx = r ∧
        (multiToInterleavedStateDecoder.decode sr.1.tail).coins = coins ∧
        (multiToInterleavedStateDecoder.decode sr.1.tail).replies = replies ∧
        (multiToInterleavedStateDecoder.decode sr.1.tail).stateA = choice.2 ∧
        decodeRevCts (ctBound n pk)
          (multiToInterleavedStateDecoder.decode sr.1.tail) sr.2 = cts.reverse) ∧
      ProbComp.eval (OracleComp.iterate r
        (interleavedRoundStep valid encOut encrypt decrypt
          (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
          n pk sk bit)
        (true :: encMultiToInterleavedState ⟨true, false, 0, coins, replies, [], choice.2⟩,
          initReply, [])) =
      (ProbComp.eval
        ((choice.1.take r).mapM (fun p => encrypt n pk (if bit then p.2 else p.1)))).map
        fun cts => ((stateOf cts).1, (stateOf cts).2, cts.reverse) := by
  induction r with
  | zero =>
    refine ⟨fun _ =>
      (true :: encMultiToInterleavedState ⟨true, false, 0, coins, replies, [], choice.2⟩,
        initReply), ?_, ?_⟩
    · intro cts hcts
      simp only [List.take_zero, List.mapM_nil, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hcts
      subst hcts
      dsimp only
      rw [List.tail_cons, multiToInterleavedStateDecoder.decode_enc]
      exact ⟨rfl, hstateCap false 0 [] (Nat.zero_le _) (by simp), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [OracleComp.iterate_zero, ProbComp.eval_pure]
  | succ r ih =>
    obtain ⟨stateOf, hprops, heval⟩ := ih (Nat.le_of_succ_le hr)
    have hrLt : r < Q n := hr
    have hrevTake {ctsPrev : List (List Bool)}
        (hprev : ctsPrev ∈ (ProbComp.eval
          ((choice.1.take r).mapM (fun p => encrypt n pk (if bit then p.2 else p.1)))).support) :
        (encList encBits ctsPrev.reverse).length ≤ (2 * ctBound n pk + 2) * Q n := by
      obtain ⟨hlen, hcap⟩ := mapM_length_and_cap
        (fun p hp => hctCap p (List.mem_of_mem_take hp)) hprev
      rw [length_encList_reverse, Nat.mul_comm]
      exact (length_encList_le encBits ctsPrev hcap).trans (Nat.mul_le_mul
        (hlen.le.trans ((List.length_take_le r choice.1).trans (Nat.le_of_lt hrLt)))
        (by omega))
    by_cases hltCh : r < choice.1.length
    · refine ⟨fun cts =>
        (true :: encMultiToInterleavedState
          ⟨true, true, r + 1, coins, replies, cts.reverse.tail, choice.2⟩,
         true :: cts.reverse.headD []), ?_, ?_⟩
      · intro cts hcts
        rw [List.take_add_one, List.getElem?_eq_getElem hltCh, Option.toList_some,
          List.mapM_append, List.mapM_cons, List.mapM_nil] at hcts
        simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
          PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hcts
        obtain ⟨ctsPrev, hprev, _, ⟨ct, hct, rfl⟩, rfl⟩ := hcts
        have hctLen : ct.length ≤ ctBound n pk :=
          hctCap choice.1[r] (List.getElem_mem hltCh) ct hct
        have hrevApp : (ctsPrev ++ [ct]).reverse = ct :: ctsPrev.reverse := by simp
        dsimp only
        rw [hrevApp, List.tail_cons, List.headD_cons, List.tail_cons,
          multiToInterleavedStateDecoder.decode_enc]
        refine ⟨rfl, hstateCap true (r + 1) ctsPrev.reverse hr (hrevTake hprev),
          rfl, rfl, rfl, rfl, rfl, ?_⟩
        dsimp only [decodeRevCts]
        have htakeReply : (true :: ct).take (ctBound n pk + 1) = true :: ct :=
          List.take_of_length_le (by simp [hctLen])
        rw [htakeReply]
        rfl
      · rw [OracleComp.iterate_succ, ProbComp.eval_bind, heval, PMF.bind_map]
        rw [List.take_add_one, List.getElem?_eq_getElem hltCh, Option.toList_some,
          List.mapM_append, List.mapM_cons, List.mapM_nil]
        simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.map_bind,
          PMF.pure_map, Function.comp_def]
        refine PMF.bind_congr_on_support _ _ _ fun cts hcts => ?_
        obtain ⟨hne, hsrLen, hact, hidx, hcoins, hrep, hstA, heff⟩ := hprops cts hcts
        have hvalPair : valid n pk choice.1[r].1 choice.1[r].2 = true :=
          List.all_eq_true.mp hall choice.1[r] (List.getElem_mem hltCh)
        unfold interleavedRoundStep multiToInterleaved rawMultiStep
        dsimp only [Function.comp_def, InterleavedLoopState.state, InterleavedLoopState.lastReply,
          InterleavedLoopState.forbidden]
        rw [List.take_of_length_le hsrLen]
        change (ProbComp.eval (do
          let stepRun ← (OracleComp.interpret
            (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
              (cca2MultiPhase2Oracle encOut decrypt n sk cts.reverse))
            (if (stateOf cts).1.isEmpty then _ else
              let decoded := multiToInterleavedStateDecoder.decode (stateOf cts).1.tail
              let revCts := decodeRevCts (ctBound n pk) decoded (stateOf cts).2
              if decoded.active then do
                let ch ← replayTypedChoose encMsg machine c d n pk decoded.coins decoded.replies
                if decide (decoded.nextIdx < ch.1.length) then
                  let pair := ch.1.getD decoded.nextIdx (default, default)
                  return (CCAQuery.challenge pair.1 pair.2,
                    true :: encMultiToInterleavedState
                      ⟨true, true, decoded.nextIdx + 1, decoded.coins, decoded.replies, revCts,
                        decoded.stateA⟩)
                else _
              else _)).run ()
          let orcOut ← interleavedCcaWordOracle valid encOut encrypt decrypt n pk sk bit
            stepRun.1.1 cts.reverse
          return (stepRun.1.2, orcOut.1, orcOut.2))) = _
        simp only [hne, Bool.false_eq_true, ↓reduceIte, hact, hidx, heff, hcoins, hrep, hstA,
          replayTypedChoose_eq_pure, hreplay, pure_bind, decide_eq_true hltCh,
          List.getD_eq_getElem _ _ hltCh, OracleComp.interpret_pure, StateT.run_pure,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, interleavedCcaWordOracle,
          interleavedCcaOracle, hvalPair, PMF.bind_bind, encodeCCAResponseWord_inl_some,
          List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.tail_cons, List.headD_cons]
    · have hleCh : choice.1.length ≤ r := Nat.le_of_not_lt hltCh
      have htakeEq : choice.1.take (r + 1) = choice.1.take r := by
        rw [List.take_of_length_le (Nat.le_succ_of_le hleCh), List.take_of_length_le hleCh]
      refine ⟨fun cts =>
        (true :: encMultiToInterleavedState
          ⟨true, false, r + 1, coins, replies, cts.reverse, choice.2⟩,
         if decide ([] ∈ cts.reverse) then [] else encOption encOut (decrypt n sk [])), ?_, ?_⟩
      · intro cts hcts
        rw [htakeEq] at hcts
        dsimp only
        rw [List.tail_cons, multiToInterleavedStateDecoder.decode_enc]
        exact ⟨rfl, hstateCap false (r + 1) cts.reverse hr (hrevTake hcts),
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [OracleComp.iterate_succ, ProbComp.eval_bind, heval, PMF.bind_map, htakeEq, PMF.map]
        refine PMF.bind_congr_on_support _ _ _ fun cts hcts => ?_
        obtain ⟨hne, hsrLen, hact, hidx, hcoins, hrep, hstA, heff⟩ := hprops cts hcts
        unfold interleavedRoundStep multiToInterleaved rawMultiStep
        dsimp only [Function.comp_def, InterleavedLoopState.state, InterleavedLoopState.lastReply,
          InterleavedLoopState.forbidden]
        rw [List.take_of_length_le hsrLen]
        change (ProbComp.eval (do
          let stepRun ← (OracleComp.interpret
            (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
              (cca2MultiPhase2Oracle encOut decrypt n sk cts.reverse))
            (if (stateOf cts).1.isEmpty then _ else
              let decoded := multiToInterleavedStateDecoder.decode (stateOf cts).1.tail
              let revCts := decodeRevCts (ctBound n pk) decoded (stateOf cts).2
              if decoded.active then do
                let ch ← replayTypedChoose encMsg machine c d n pk decoded.coins decoded.replies
                if decide (decoded.nextIdx < ch.1.length) then _
                else
                  return (CCAQuery.decrypt [],
                    true :: encMultiToInterleavedState
                      ⟨true, false, decoded.nextIdx + 1, decoded.coins, decoded.replies, revCts,
                        decoded.stateA⟩)
              else _)).run ()
          let orcOut ← interleavedCcaWordOracle valid encOut encrypt decrypt n pk sk bit
            stepRun.1.1 cts.reverse
          return (stepRun.1.2, orcOut.1, orcOut.2))) = _
        simp only [hne, Bool.false_eq_true, ↓reduceIte, hact, hidx, heff, hcoins, hrep, hstA,
          replayTypedChoose_eq_pure, hreplay, pure_bind, decide_eq_false hltCh,
          OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure,
          interleavedCcaWordOracle, interleavedCcaOracle]
        by_cases hmemNil : [] ∈ cts.reverse
        · simp [hmemNil, ProbComp.eval_pure, encOption]
        · simp [hmemNil, ProbComp.eval_pure]

private theorem cca2MultiPhase2Oracle_reverse {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (cts : List (List Bool)) :
    cca2MultiPhase2Oracle encOut decrypt n sk cts.reverse =
      cca2MultiPhase2Oracle encOut decrypt n sk cts := by
  funext request s
  simp [cca2MultiPhase2Oracle, List.mem_reverse]

private theorem replay_of_mem_support_chooseAndRecord {Msg Out : Type}
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ) (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (pk sk : List Bool)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound n req)
    {choice : List (Msg × Msg) × List Bool} {coins : List Bool} {replies : List (List Bool)}
    (hmem : ((choice, coins, replies), ()) ∈ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (chooseAndRecord encMsg machine c d decBound n pk)).run ())).support) :
    decodeChoiceWord encMsg (replayWithReplies
      (machine.runCoins (fun op word => OracleComp.query (spec := RawDecSpec) (op, word))
        (padCoins (chooseClock c d n pk) coins) (encPair encUnary encBits (n, pk)))
      replies) = choice := by
  rw [eval_chooseAndRecord_eq_bind_coins encMsg encOut machine c d decrypt decBound n pk sk
    hdecBound, PMF.mem_support_map_iff] at hmem
  obtain ⟨coins', -, heq⟩ := hmem
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).1
  rw [replayWithReplies_evalAndRecord]

private theorem eval_interleavedCca2GameOn_multiToInterleaved {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {k : ℕ} {Control : Type} (machine : Turing.MultiTapePTM k Bool Control Unit)
    (c d : ℕ)
    {decBound stateCap ctBound : ℕ → List Bool → ℕ} {Q : ℕ → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hCoinsEq : ∀ (a : ℕ × List Bool) (Store : Type)
      (oracle : Unit × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith oracle
        (encPair (encList (encPair encMsg encMsg)) encBits <$> adversary.choose a.1 a.2) s =
      (BitString.uniformList (c * ((encPair encUnary encBits a).length + 1) ^ d)).bind fun coins =>
        ProbOracleComp.runWith oracle
          (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
            coins (encPair encUnary encBits a)) s)
    (bit : Bool) (n : ℕ)
    (hrejCap : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      rejectMultiToInterleavedWord.length ≤ stateCap n keys.1)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hbounds : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ recOut ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (chooseAndRecord encMsg machine c d decBound n keys.1)).run ())).support,
      (∀ (aw : Bool) (idx : ℕ) (rev : List (List Bool)),
        idx ≤ Q n → (encList encBits rev).length ≤ (2 * ctBound n keys.1 + 2) * Q n →
          (true :: encMultiToInterleavedState
            ⟨true, aw, idx, recOut.1.2.1, recOut.1.2.2, rev, recOut.1.1.2⟩).length ≤
            stateCap n keys.1) ∧
      recOut.1.1.1.length ≤ Q n ∧
      ∀ p ∈ recOut.1.1.1,
        ∀ ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then p.2 else p.1))).support,
          ct.length ≤ ctBound n keys.1) :
    ProbComp.eval
      (interleavedCca2GameOn valid encOut keyGen encrypt decrypt
        (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
        bit n) =
    ProbComp.eval
      (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  have hnum : (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q
      adversary).numRounds n = Q n + 1 := rfl
  simp only [interleavedCca2GameOn, interleavedCca2Exp, cca2MultiGameOn, hnum,
    OracleComp.iterate_succ_bind, ProbComp.eval_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  let chooseCont : (List (Msg × Msg) × List Bool) → PMF Bool := fun choice =>
    if choice.1.all (fun p => valid n keys.1 p.1 p.2) then
      (ProbComp.eval
        (choice.1.mapM (fun p => encrypt n keys.1 (if bit then p.2 else p.1)))).bind fun cts =>
        (ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2MultiPhase2Oracle encOut decrypt n keys.2 cts))
          (adversary.guess n choice.2 cts)).run ())).bind fun guessOut =>
          PMF.pure guessOut.1
    else
      PMF.pure false
  have hrhs :
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).bind (fun choiceOut => chooseCont choiceOut.1) =
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (chooseAndRecord encMsg machine c d decBound n keys.1)).run ())).bind
        (fun recOut => chooseCont recOut.1.1) := by
    have hmap := map_fst_eval_chooseAndRecord_eq machine c d decrypt decBound n keys.1 keys.2
      (hdecBound keys hkeys) hCoinsEq
    have hb := congrArg (fun p => p.bind chooseCont) hmap
    simpa only [PMF.bind_map, Function.comp_def] using hb.symm
  trans (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n keys.2))
      (chooseAndRecord encMsg machine c d decBound n keys.1)).run ())).bind
      (fun recOut => chooseCont recOut.1.1)
  · have hround0 :
        interleavedRoundStep valid encOut encrypt decrypt
          (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
          n keys.1 keys.2 bit initInterleavedLoopState =
        (do
          let stepRun ← (OracleComp.interpret
            (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
              (cca2Phase1Oracle encOut decrypt n keys.2))
            (do
              let recOut ← chooseAndRecord encMsg machine c d decBound n keys.1
              if recOut.1.1.all (fun p => valid n keys.1 p.1 p.2) then
                return (CCAQuery.decrypt [],
                  true :: encMultiToInterleavedState
                    ⟨true, false, 0, recOut.2.1, recOut.2.2, [], recOut.1.2⟩)
              else
                return (CCAQuery.decrypt [], rejectMultiToInterleavedWord))).run ()
          let orcOut ← interleavedCcaWordOracle valid encOut encrypt decrypt n keys.1 keys.2 bit
            stepRun.1.1 []
          return (stepRun.1.2, orcOut.1, orcOut.2)) := by
      unfold interleavedRoundStep multiToInterleaved rawMultiStep initInterleavedLoopState
      simp only [InterleavedLoopState.state, InterleavedLoopState.forbidden, List.take_nil,
        List.isEmpty_nil, ↓reduceIte, cca2MultiPhase2Oracle_nil]
    rw [hround0]
    simp only [OracleComp.interpret_bind, StateT.run_bind, ProbComp.eval_bind, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨choice, coins, replies⟩, ⟨⟩⟩ hrecOut => ?_
    obtain ⟨hstateCapLe, hlenLeQ, hctCap⟩ := hbounds keys hkeys _ hrecOut
    have hreplay := replay_of_mem_support_chooseAndRecord encMsg encOut machine c d decrypt
      decBound n keys.1 keys.2 (hdecBound keys hkeys) hrecOut
    by_cases hall : choice.1.all (fun p => valid n keys.1 p.1 p.2) = true
    · simp only [hall, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure,
        PMF.pure_bind, interleavedCcaWordOracle, interleavedCcaOracle, List.not_mem_nil,
        decide_false, Bool.false_eq_true, pure_bind, encodeCCAResponseWord_inr, chooseCont]
      obtain ⟨stateOf, hprops, heval⟩ := eval_iterate_active_multiToInterleaved encMsg valid
        encOut machine c d encrypt decrypt decBound stateCap ctBound Q adversary n keys.1 keys.2
        bit choice coins replies hall hstateCapLe hreplay hctCap (Q n) le_rfl
        (encOption encOut (decrypt n keys.2 []))
      rw [heval, List.take_of_length_le hlenLeQ, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun cts hcts => ?_
      obtain ⟨hne, -, hact, -, -, -, hstA, heff⟩ := hprops cts
        (by simpa only [List.take_of_length_le hlenLeQ] using hcts)
      dsimp only [Function.comp_def, multiToInterleaved, InterleavedLoopState.state,
        InterleavedLoopState.lastReply, InterleavedLoopState.forbidden]
      change (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2MultiPhase2Oracle encOut decrypt n keys.2 cts.reverse))
        (if (stateOf cts).1.isEmpty then pure false else
          let decoded := multiToInterleavedStateDecoder.decode (stateOf cts).1.tail
          if decoded.active then
            adversary.guess n decoded.stateA
              (decodeRevCts (ctBound n keys.1) decoded (stateOf cts).2).reverse
          else pure false)).run ())).bind _ = _
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hact, hstA, heff, List.reverse_reverse,
        cca2MultiPhase2Oracle_reverse]
    · simp only [hall, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        ProbComp.eval_pure, PMF.pure_bind, interleavedCcaWordOracle, interleavedCcaOracle,
        List.not_mem_nil, decide_false, pure_bind, encodeCCAResponseWord_inr, chooseCont]
      simpa only [ProbComp.eval_bind, ProbComp.eval_pure] using
        eval_iterate_rejectMultiToInterleavedWord encMsg valid encOut machine c d encrypt decrypt
          decBound stateCap ctBound Q adversary n keys.1 keys.2 bit (hrejCap keys hkeys) (Q n)
          (encOption encOut (decrypt n keys.2 []))
  · rw [← hrhs]
    refine PMF.bind_congr_on_support _ _ _ fun choiceOut _ => ?_
    dsimp only [chooseCont]
    by_cases hall : choiceOut.1.1.all (fun p => valid n keys.1 p.1 p.2) = true
    · simp only [hall, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    · simp [hall, ProbComp.eval_pure]

/-- **Interleaved multi-challenge CCA security implies phased batch-challenge multi-challenge CCA
security** ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.1, printed
pp. 467–468): proved directly by simulating a batch adversary across `Q n + 1` adaptive rounds via
`multiToInterleaved` (without routing back through single-challenge 1CCA). -/
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
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  obtain ⟨k, Control, hfinite, machine, c, d, -, hCoinsEq⟩ := hA.choose.on.exists_savedCoins
  let := hfinite
  obtain ⟨ck, dk, hlenKey⟩ := hkeyGen.length_le
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := exists_decryption_length_bound hkeyGen hdecrypt
  obtain ⟨ci, di, hlenRec⟩ :=
    (isOraclePPTOn_chooseAndRecord machine c d hdecBoundPoly hCoinsEq).length_le
  obtain ⟨ce, de, hlenEnc⟩ := hencrypt.length_le
  let initBound : ℕ → List Bool → ℕ := fun n pk => ci * (2 * n + pk.length + 3) ^ di
  let ctBound : ℕ → List Bool → ℕ :=
    fun n pk => ce * (2 * n + 2 * pk.length + initBound n pk + 5) ^ de
  let Q : ℕ → ℕ := fun n => ci * (2 * n + ck * (n + 1) ^ dk + 3) ^ di
  let stateCap : ℕ → List Bool → ℕ :=
    fun n pk => 4 * Q n + 6 * initBound n pk + 2 * ((2 * ctBound n pk + 2) * Q n) + 30
  have hctPoly : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    dsimp only [ctBound, initBound]; fun_prop
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hstateCapPoly : ComputableInPolyTime (fun p : ℕ × List Bool => stateCap p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    have hq : ComputableInPolyTime (fun p : ℕ × List Bool => Q p.1)
        (encPair encUnary encBits) encUnary := hQPoly.comp (ComputableInPolyTime.fst _ _)
    have hi : ComputableInPolyTime (fun p : ℕ × List Bool => initBound p.1 p.2)
        (encPair encUnary encBits) encUnary := by dsimp only [initBound]; fun_prop
    have harith : ComputableInPolyTime
        (fun t : ℕ × ℕ × ℕ => 4 * t.1 + 6 * t.2.1 + 2 * ((2 * t.2.2 + 2) * t.1) + 30)
        (encPair encUnary (encPair encUnary encUnary)) encUnary := by
      have h1 : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => 4 * t.1 + 6 * t.2.1)
          (encPair encUnary (encPair encUnary encUnary)) encUnary := by fun_prop
      have h2 : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => 2 * ((2 * t.2.2 + 2) * t.1) + 30)
          (encPair encUnary (encPair encUnary encUnary)) encUnary := by
        have h2a : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => 2 * t.2.2 + 2)
            (encPair encUnary (encPair encUnary encUnary)) encUnary := by fun_prop
        exact (ComputableInPolyTime.unary_add.comp
          ((ComputableInPolyTime.unary_mul.comp
            ((ComputableInPolyTime.const 2).prod
              (ComputableInPolyTime.unary_mul.comp (h2a.prod (by fun_prop))))).prod
            (ComputableInPolyTime.const 30)))
      exact ComputableInPolyTime.unary_add.comp (h1.prod h2)
    exact harith.comp (hq.prod (hi.prod hctPoly))
  have hrejLen : rejectMultiToInterleavedWord.length ≤ 30 := by
    unfold rejectMultiToInterleavedWord
    enc_len [encMultiToInterleavedState_apply]
  have hbounds (bit : Bool) (n : ℕ) (keys : List Bool × List Bool)
      (hkeys : keys ∈ (ProbComp.eval (keyGen n)).support)
      (recOut : ((List (Msg × Msg) × List Bool) × List Bool × List (List Bool)) × Unit)
      (hrecOut : recOut ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (chooseAndRecord encMsg machine c d decBound n keys.1)).run ())).support) :
      (∀ (aw : Bool) (idx : ℕ) (rev : List (List Bool)),
        idx ≤ Q n → (encList encBits rev).length ≤ (2 * ctBound n keys.1 + 2) * Q n →
          (true :: encMultiToInterleavedState
            ⟨true, aw, idx, recOut.1.2.1, recOut.1.2.2, rev, recOut.1.1.2⟩).length ≤
            stateCap n keys.1) ∧
      recOut.1.1.1.length ≤ Q n ∧
      ∀ p ∈ recOut.1.1.1,
        ∀ ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then p.2 else p.1))).support,
          ct.length ≤ ctBound n keys.1 := by
    have hk := hlenKey n keys hkeys
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hk
    rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hrecOut
    have hrecLen := hlenRec (n, keys.1) Unit _ () recOut.2 recOut.1 hrecOut
    have hbaseRec : (encPair encUnary encBits (n, keys.1)).length + 1 ≤
        2 * n + keys.1.length + 3 := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      omega
    have hrecCap :
        (encPair (encPair (encList (encPair encMsg encMsg)) encBits)
          (encPair encBits (encList encBits)) recOut.1).length ≤ initBound n keys.1 :=
      hrecLen.trans (Nat.mul_le_mul_left ci (Nat.pow_le_pow_left hbaseRec di))
    have hcoinsLe : recOut.1.2.1.length ≤ initBound n keys.1 := by
      refine le_trans ?_ hrecCap; enc_len
    have hrepLe : (encList encBits recOut.1.2.2).length ≤ initBound n keys.1 := by
      refine le_trans ?_ hrecCap; enc_len
    have hstALe : recOut.1.1.2.length ≤ initBound n keys.1 := by
      refine le_trans ?_ hrecCap; enc_len
    have hlistLe : (encList (encPair encMsg encMsg) recOut.1.1.1).length ≤ initBound n keys.1 := by
      refine le_trans ?_ hrecCap; enc_len
    have hsc (aw : Bool) (idx : ℕ) (rev : List (List Bool)) (hidx : idx ≤ Q n)
        (hrev : (encList encBits rev).length ≤ (2 * ctBound n keys.1 + 2) * Q n) :
        (true :: encMultiToInterleavedState
          ⟨true, aw, idx, recOut.1.2.1, recOut.1.2.2, rev, recOut.1.1.2⟩).length ≤
          stateCap n keys.1 := by
      dsimp only [stateCap]
      enc_len [encMultiToInterleavedState_apply]
    have hlenLeQ : recOut.1.1.1.length ≤ Q n := by
      have h1 := (length_le_length_encList (encPair encMsg encMsg) recOut.1.1.1).trans hlistLe
      exact h1.trans (Nat.mul_le_mul_left ci (Nat.pow_le_pow_left (by omega) di))
    refine ⟨hsc, hlenLeQ, fun p hp ct hct => ?_⟩
    rcases p with ⟨m₀, m₁⟩
    have hpLen : (encPair encMsg encMsg (m₀, m₁)).length ≤ initBound n keys.1 :=
      (length_le_encList_of_mem (encPair encMsg encMsg) hp).trans hlistLe
    have hmLen : (encMsg (if bit then m₁ else m₀)).length ≤ initBound n keys.1 := by
      simp only [length_encPair] at hpLen
      cases bit <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    have he := hlenEnc (n, keys.1, if bit then m₁ else m₀) ct hct
    have hbaseEnc : (encKeyedInput encMsg (n, keys.1, if bit then m₁ else m₀)).length + 1 ≤
        2 * n + 2 * keys.1.length + initBound n keys.1 + 5 := by
      simp only [encKeyedInput, length_encPair, encUnary_apply, List.length_replicate,
        encBits_apply]
      omega
    exact he.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left hbaseEnc de))
  have hneg := h
    (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
    (isPPT_multiToInterleaved machine c d hvalid hdecBoundPoly hstateCapPoly hctPoly hQPoly hA
      hCoinsEq)
  have heq (bit : Bool) (n : ℕ) :
      ProbComp.eval
        (interleavedCca2GameOn valid encOut keyGen encrypt decrypt
          (multiToInterleaved encMsg valid machine c d decBound stateCap ctBound Q adversary)
          bit n) =
      ProbComp.eval
        (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary bit n) :=
    eval_interleavedCca2GameOn_multiToInterleaved machine c d hCoinsEq bit n
      (fun _ _ => by dsimp only [stateCap]; omega)
      (hdecBound n) (hbounds bit n)
  simpa only [heq] using hneg

/-! ### Relationship 2: Single-challenge 1CCA implies Interleaved Multi-CCA2 (Theorem 12.1) -/

/-- Stateless Phase 2 filter handler for the multi-to-single CCA reduction: reject any decryption
query `request.2 ∈ cts` with `[]`, and forward all other queries `request.2 ∉ cts` to the external
single-challenge decryption oracle (truncating the reply to `decBound request.2` bits for strict
oracle PPT certification). -/
private def multiPhase2FilterHandler (decBound : List Bool → ℕ) (cts : List (List Bool))
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) := fun s =>
  if decide (request.2 ∈ cts) then
    pure ([], s)
  else
    (fun reply => (reply, s)) <$>
      (List.take (decBound request.2) <$> ProbOracleComp.query ((), request.2))

/-- Running a strict oracle PPT program through `multiPhase2FilterHandler` is uniformly strict
oracle PPT whenever the reply-length cap and forbidden ciphertext list are computable in polynomial
time from the caller's input. -/
private theorem isOraclePPTOn_run_multiPhase2FilterHandler {Caller β : Type}
    {ECaller : Caller ↪ List Bool} {EOut : β ↪ List Bool}
    {cap : Caller → List Bool → ℕ} {cts : Caller → List (List Bool)}
    {prog : Caller → WordOracleComp Unit β}
    (hcap : ComputableInPolyTime (fun p : Caller × List Bool => cap p.1 p.2)
      (encPair ECaller encBits) encUnary)
    (hcts : ComputableInPolyTime cts ECaller (encList encBits))
    (hprog : IsOraclePPTOn (Operation := Unit) ECaller EOut prog) :
    IsOraclePPTOn (Operation := Unit) ECaller (encPair EOut (encFinEnum Unit))
      (fun a =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (cap a) (cts a)))
          (prog a)).run ()) := by
  refine hprog.run_interpret_preprocess_open (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (prepare := id) (initial := fun _ => ()) (resources := cap)
    ComputableInPolyTime.id'
    (by
      have hlim : ComputableInPolyTime
          (fun x : Caller × (Unit × List Bool) × Unit => cap x.1 x.2.1.2)
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) encUnary :=
        hcap.comp (show ComputableInPolyTime (fun x => (x.1, x.2.1.2))
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) _ by fun_prop)
      dsimp only [multiPhase2FilterHandler]
      exact IsOraclePPTOn.cond (by fun_prop) (by fun_prop)
        ((IsOraclePPTOn.query_take (Operation := Unit) () (by fun_prop) hlim).map_with
          (by fun_prop)))
    (by fun_prop) (fun _ _ => True) (fun _ => trivial) hcap
    fun _ _ _ _ _ hresult => ?_
  dsimp only [multiPhase2FilterHandler] at hresult
  split_ifs at hresult
  · supp_cases hresult; exact ⟨trivial, Nat.zero_le _, Nat.le_add_right _ _⟩
  · supp_cases hresult; exact ⟨trivial, List.length_take_le _ _, Nat.le_add_right _ _⟩

/-- Interpreting `multiPhase2FilterHandler` against `cca2Phase2Oracle` on `ct ∈ cts` has the exact
same output distribution as running directly against `cca2MultiPhase2Oracle` on `cts`, whenever
`decBound` upper-bounds every encoded decryption output length. -/
private theorem eval_run_multiPhase2FilterHandler {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ)
    (n : ℕ) (sk ct : List Bool) (cts : List (List Bool))
    (hct : ct ∈ cts)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n sk ct))
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) := by
  rw [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_run_interpret_map (multiPhase2FilterHandler decBound cts)
      (fun q s => ProbComp.eval (cca2Phase2Oracle encOut decrypt n sk ct q s))
      (fun q s => ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts q s))
      (fun _ => ()) (fun _ => ()) (by
      intro ⟨⟨⟩, req⟩ ⟨⟩
      change (ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts ((), req) ())).map
          (fun x => (x.1, (), ())) =
        (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (cca2Phase2Oracle encOut decrypt n sk ct q s))
            (multiPhase2FilterHandler decBound cts ((), req) ()) ()).map
          (fun result => (result.1.1, result.1.2, result.2))
      by_cases hmem : req ∈ cts
      · simp [cca2MultiPhase2Oracle, multiPhase2FilterHandler, hmem, ProbComp.eval_pure]
      · have hne : (req == ct) = false :=
          beq_eq_false_iff_ne.mpr fun heq => hmem (heq ▸ hct)
        unfold cca2MultiPhase2Oracle multiPhase2FilterHandler
        simp only [hmem, decide_false, Bool.false_eq_true, ↓reduceIte, Functor.map_map,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, cca2Phase2Oracle, hne,
          ProbComp.eval_pure, PMF.pure_map]
        simp only [Prod.map_apply, id_eq, List.take_of_length_le (hdecBound req)])
      prog (), PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

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
  have hmemInner := mem_support_of_mem_support_run_interpret_state
    (multiPhase2FilterHandler (decBound n) st.2.2)
    (interleavedInnerRound valid encrypt decBound adversary roundBit n pk st) () hmemRun
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

/-- Interpreting `multiPhase2FilterHandler` against `cca2Phase1Oracle` has the exact same output
distribution as running directly against `cca2MultiPhase2Oracle` on `cts`, whenever `decBound`
upper-bounds every encoded decryption output length. -/
private theorem eval_run_multiPhase2FilterHandler_phase1 {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ)
    (n : ℕ) (sk : List Bool) (cts : List (List Bool))
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) := by
  rw [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_run_interpret_map (multiPhase2FilterHandler decBound cts)
      (fun q s => ProbComp.eval (cca2Phase1Oracle encOut decrypt n sk q s))
      (fun q s => ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts q s))
      (fun _ => ()) (fun _ => ()) (by
      intro ⟨⟨⟩, req⟩ ⟨⟩
      dsimp only [StateT.run]
      by_cases hmem : req ∈ cts
      · simp [cca2MultiPhase2Oracle, multiPhase2FilterHandler, hmem, ProbComp.eval_pure]
      · unfold cca2MultiPhase2Oracle multiPhase2FilterHandler
        simp only [hmem, decide_false, Bool.false_eq_true, ↓reduceIte, cca2Phase1Oracle,
          List.take_of_length_le (hdecBound req), runWith_norm, pmf_norm])
      prog (), PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

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
  refine (Probability.PMF.map_iterate_bind_of_invariant
    (fun st' => ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st'))
    _ (fun st' => (st', ())) (fun _ _ => True) k st trivial
    fun _ _ st' _ => ⟨?_, fun _ _ => trivial⟩).1.symm
  exact (eval_interpret_interleavedOpenRoundStep_phase1 valid encOut encrypt decrypt decBound
    adversary roundBit n pk sk st' hdecBound).symm

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
  refine (Probability.PMF.map_iterate_bind_of_invariant
    (fun st' => ProbComp.eval
      (interleavedRoundStep valid encOut encrypt decrypt adversary n pk sk roundBit st'))
    _ (fun st' => (st', ())) (fun _ st' => ct ∈ st'.2.2) k st hct
    fun _ _ st' hst' => ⟨?_, fun _ h => mem_S_of_mem_support_interleavedRoundStep h hst'⟩).1.symm
  exact (eval_interpret_interleavedOpenRoundStep_phase2 valid encOut encrypt decrypt decBound
    adversary roundBit n pk sk ct st' hst' hdecBound).symm

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
  simp only [↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
    OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
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
        ProbComp.eval_pure, PMF.pure_bind, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state,
        ProbComp.eval_bind, interleavedHybridAfterStep, interleavedCcaWordOracle,
        interleavedCcaOracle, PMF.bind_bind, encodeCCAResponseWord_inl_some]
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
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
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
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]

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

/-- **Single-challenge 1CCA security implies phased batch-challenge multi-challenge CCA security**
(corollary of `INDCCA2On.indcca2InterleavedOn` and `INDCCA2InterleavedOn.indcca2MultiOn`;
batch-challenge restriction of [BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468). -/
theorem INDCCA2On.indcca2MultiOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt :=
  (h.indcca2InterleavedOn hvalid hkeyGen hencrypt hdecrypt).indcca2MultiOn
    hvalid hkeyGen hencrypt hdecrypt

/-- Batch-challenge restriction of [BonehShoup2023], Section 12.1, Theorem 12.1 with Definition
12.2 (printed p. 468): single-challenge 1CCA security and phased batch-challenge multi-challenge
CCA security are equivalent under any polynomial-time challenge-pair admissibility predicate
`valid`. The equivalence for adaptively interleaved queries is `indcca2InterleavedOn_iff_indcca2On`.
-/
theorem indcca2MultiOn_iff_indcca2On {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2On valid encMsg encOut keyGen encrypt decrypt :=
  ⟨INDCCA2MultiOn.indcca2On,
    INDCCA2On.indcca2MultiOn hvalid hkeyGen hencrypt hdecrypt⟩

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
  ⟨INDCCA2InterleavedOn.indcca2MultiOn hvalid hkeyGen hencrypt hdecrypt,
    fun h => h.indcca2On.indcca2InterleavedOn hvalid hkeyGen hencrypt hdecrypt⟩

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

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1: unrestricted single-challenge
1CCA security implies unrestricted batch-challenge multi-challenge CCA security. Theorem 12.1 for
interleaved queries is `INDCCA2Of.indcca2InterleavedOf`. -/
theorem INDCCA2Of.indcca2MultiOf {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt h

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1 with Definition 12.2:
unrestricted 1CCA and batch-challenge multi-challenge CCA security are equivalent. -/
theorem indcca2MultiOf_iff_indcca2Of {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2Of encMsg encOut keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1: bit single-challenge 1CCA
security implies bit batch-challenge multi-challenge CCA security. Theorem 12.1 for interleaved
queries is `INDCCA2.indcca2Interleaved`. -/
theorem INDCCA2.indcca2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBool))
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2Of.indcca2MultiOf hkeyGen hencrypt hdecrypt h

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1 with Definition 12.2: bit 1CCA
and bit batch-challenge multi-challenge CCA security are equivalent. -/
theorem indcca2Multi_iff_indcca2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBool)) :
    INDCCA2Multi keyGen encrypt decrypt ↔ INDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOf_iff_indcca2Of hkeyGen hencrypt hdecrypt

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1: word single-challenge 1CCA
security implies word batch-challenge multi-challenge CCA security. Theorem 12.1 for interleaved
queries is `WordINDCCA2.wordINDCCA2Interleaved`. -/
theorem WordINDCCA2.wordINDCCA2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBits))
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn (by fun_prop) hkeyGen hencrypt hdecrypt h

/-- Batch-challenge restriction of [BonehShoup2023], Theorem 12.1 with Definition 12.2: word 1CCA
and word batch-challenge multi-challenge CCA security are equivalent. -/
theorem wordINDCCA2Multi_iff_wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBits)) :
    WordINDCCA2Multi keyGen encrypt decrypt ↔ WordINDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On (by fun_prop) hkeyGen hencrypt hdecrypt

end Cslib.Crypto.Encryption
