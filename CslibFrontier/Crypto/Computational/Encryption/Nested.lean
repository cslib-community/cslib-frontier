/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Finite
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Nested encryption

Given a symmetric cipher `E : Cipher K M M` whose ciphertexts lie in its plaintext space `M`,
`E.nested n` ([BonehShoup2023], §2.4, p. 37) composes `n` encryption layers with independent keys
`k 0, ..., k (n - 1)`, applying `k 0` innermost and `k (n - 1)` outermost. Decryption peels the
keys in reverse order. `Cipher.nested_correct` proves that `n`-way nesting preserves correctness.

`Cipher.nestedExperiment` states the `n`-way nested security game of [BonehShoup2023], §2.4, p. 37:
the adversary chooses a message pair and the index `withheld : Fin n` of one hidden key, and
receives the nested ciphertext together with the remaining `n - 1` keys (`revealKeys`).

Relative to [BonehShoup2023], §2.4, this module has the following differences:
* Ciphertexts share the plaintext type `M` (`Cipher K M M`) so `n`-way composition is well-typed for
  every `n`.
* Keys are indexed `0`-based by `Fin n` rather than `1, ..., n`; `n = 0` is vacuous because
  `Fin 0` is empty.
* The challenger draws all `n` keys before calling `A.choose` rather than after (identical output
  law), and an inadmissible pair makes both experiments output `false`.
* Key sampling `sampleKey` and challenge admissibility `valid` are parameters where the book fixes
  uniform keys and equal message length. The theorems below also assume `Cipher.PreservesValid`,
  so that prefix-encrypted challenge pairs stay admissible for the outer single-key game. The book
  does not state this hypothesis, and Theorem 2.12 fails without it: a one-time secure cipher can
  have nested advantage one (`tagCipher_no_wrapper` in the tests). They are a corrected form of
  Theorem 2.12.

`nestedToSingleAdversary` gives the reduction for Theorem 2.12: it samples a `Fin n → K` key vector
via `OracleComp.replicateFin` (never reading the `withheld` coordinate), encrypts both messages
through the prefix layers `0, ..., withheld - 1`, delegates the `withheld` layer to
`oneTimeExperiment`, and applies the suffix layers `withheld + 1, ..., n - 1` before calling
`A.guess` when `st.admissible` holds. `eval_oneTimeExperiment_nestedToSingleAdversary` and
`advantage_nestedExperiment_eq` prove exact distribution and advantage equality,
`isPPT_nestedToSingleAdversary` proves uniform strict polynomial-time efficiency of the reduction,
and `indistinguishable_nestedExperiment_of_oneTimeExperiment` derives `Game.Indistinguishable` for
`n`-way nesting from single-key semantic security.

## Main definitions

* `Cslib.Crypto.Cipher.nestedEncrypt`, `Cslib.Crypto.Cipher.nestedDecrypt`,
  `Cslib.Crypto.Cipher.nested`: `n`-way nested encryption and decryption.
* `Cslib.Crypto.Cipher.PreservesValid`: preservation of challenge-pair admissibility under
  encryption.
* `Cslib.Crypto.NestedRequest`, `Cslib.Crypto.NestedChallenge`, `Cslib.Crypto.revealKeys`,
  `Cslib.Crypto.Cipher.nestedExperiment`: adversary request/challenge records and multi-key
  security experiment for Theorem 2.12.
* `Cslib.Crypto.NestedReductionState`, `Cslib.Crypto.nestedToSingleAdversary`: single-key
  reduction adversary.
* `Cslib.Crypto.encNestedRequest`, `Cslib.Crypto.encNestedChallenge`,
  `Cslib.Crypto.encNestedReductionState`: computable encodings of the request, challenge, and
  reduction state.

## Main results

* `Cslib.Crypto.Cipher.nested_correct`: correctness of `E.nested n` from `E.Correct`.
* `Cslib.Crypto.eval_oneTimeExperiment_nestedToSingleAdversary`: exact distribution equality
  between `E.oneTimeExperiment` against `nestedToSingleAdversary` and `E.nestedExperiment`.
* `Cslib.Crypto.advantage_nestedExperiment_eq`: exact advantage equality for Theorem 2.12.
* `Cslib.Crypto.isPPT_nestedToSingleAdversary`: uniform strict polynomial-time efficiency
  certificate for `nestedToSingleAdversary`.
* `Cslib.Crypto.indistinguishable_nestedExperiment_of_oneTimeExperiment`: Theorem 2.12 semantic
  security for `n`-way nesting from single-key semantic security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §2.4 (Theorem 2.12, p. 37).
-/

public section

open Cslib Cslib.Probability

namespace Cslib.Crypto

section NestedDef

variable {K M : Type}

/-- `n`-way nested encryption applying keys `k 0, ..., k (n - 1)` from innermost to outermost. -/
@[expose] def Cipher.nestedEncrypt (E : Cipher K M M) :
    ∀ n : ℕ, (Fin n → K) → M → ProbComp M
  | 0, _, m => pure m
  | n + 1, k, m => do
    let c ← E.encrypt (k 0) m
    E.nestedEncrypt n (Fin.tail k) c

@[simp] theorem Cipher.nestedEncrypt_zero (E : Cipher K M M) (k : Fin 0 → K) (m : M) :
    E.nestedEncrypt 0 k m = pure m := rfl

@[simp] theorem Cipher.nestedEncrypt_succ (E : Cipher K M M) (n : ℕ) (k : Fin (n + 1) → K)
    (m : M) :
    E.nestedEncrypt (n + 1) k m = (E.encrypt (k 0) m >>= E.nestedEncrypt n (Fin.tail k)) := rfl

/-- `n`-way nested decryption peeling keys `k (n - 1), ..., k 0` from outermost to innermost. -/
def Cipher.nestedDecrypt (E : Cipher K M M) : ∀ n : ℕ, (Fin n → K) → M → Option M
  | 0, _, c => some c
  | n + 1, k, c => (E.nestedDecrypt n (Fin.tail k) c).bind (E.decrypt (k 0))

@[simp] theorem Cipher.nestedDecrypt_zero (E : Cipher K M M) (k : Fin 0 → K) (c : M) :
    E.nestedDecrypt 0 k c = some c := by
  simp [Cipher.nestedDecrypt]

@[simp] theorem Cipher.nestedDecrypt_succ (E : Cipher K M M) (n : ℕ) (k : Fin (n + 1) → K)
    (c : M) :
    E.nestedDecrypt (n + 1) k c = (E.nestedDecrypt n (Fin.tail k) c).bind (E.decrypt (k 0)) := by
  simp [Cipher.nestedDecrypt]

/-- The `n`-way nested cipher `E_n` ([BonehShoup2023], §2.4, p. 37). Unlike the book's `1`-based
indexing, keys are indexed by `Fin n` with `k 0` applied innermost; `n = 0` is the identity. -/
@[expose] def Cipher.nested (E : Cipher K M M) (n : ℕ) : Cipher (Fin n → K) M M where
  encrypt := E.nestedEncrypt n
  decrypt := E.nestedDecrypt n

/-- `n`-way nested encryption of a correct cipher is correct. -/
theorem Cipher.nested_correct {E : Cipher K M M} (hE : E.Correct) (n : ℕ) :
    (E.nested n).Correct := by
  intro k m c hc
  simp only [Cipher.nested] at hc ⊢
  induction n generalizing m c with
  | zero =>
    simp only [Cipher.nestedEncrypt, Cipher.nestedDecrypt, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hc ⊢
    exact congrArg some hc
  | succ n ih =>
    simp only [Cipher.nestedEncrypt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc
    obtain ⟨c₀, hc₀, hc⟩ := hc
    simp only [Cipher.nestedDecrypt]
    rw [ih (Fin.tail k) c₀ c hc, Option.bind_some]
    exact hE (k 0) m c₀ hc₀

/-- Admissibility preservation under encryption: encrypting an admissible pair `(m₀, m₁)` under any
supported key produces an admissible ciphertext pair `(c₀, c₁)`. [BonehShoup2023] Theorem 2.12
does not state this condition, and the theorem fails without it (`tagCipher_no_wrapper` in the
tests); the corrected form here assumes it so prefix-encrypted pairs stay admissible for the outer
game. -/
@[expose] def Cipher.PreservesValid (E : Cipher K M M) (sampleKey : ProbComp K)
    (valid : M → M → Bool) : Prop :=
  ∀ k ∈ (ProbComp.eval sampleKey).support, ∀ m₀ m₁, valid m₀ m₁ = true →
    ∀ c₀ ∈ (ProbComp.eval (E.encrypt k m₀)).support,
    ∀ c₁ ∈ (ProbComp.eval (E.encrypt k m₁)).support,
    valid c₀ c₁ = true

/-- Challenge request of an `n`-way nested encryption adversary: a message pair and the
`0`-indexed withheld key position `withheld : Fin n` (empty when `n = 0`). -/
structure NestedRequest (M : Type) (n : ℕ) where
  /-- Pair of challenge plaintexts chosen by the adversary. -/
  pair : MessagePair M
  /-- `0`-based index of the single key withheld from the adversary (`Fin 0` is empty). -/
  withheld : Fin n

/-- Second-stage challenge received by an `n`-way nested encryption adversary: the nested
ciphertext and every key except the withheld index. -/
structure NestedChallenge (K M : Type) (n : ℕ) where
  /-- Challenge ciphertext returned by the `n`-way nested cipher. -/
  ciphertext : M
  /-- Partial key vector revealing `some (k i)` for `i ≠ withheld` and `none` at `withheld`. -/
  revealedKeys : Fin n → Option K

/-- Reveal every key in `k` except at `0`-based index `d`. -/
def revealKeys {n : ℕ} (d : Fin n) (k : Fin n → K) : Fin n → Option K :=
  fun i => if i = d then none else some (k i)

@[simp] theorem revealKeys_self {n : ℕ} (d : Fin n) (k : Fin n → K) :
    revealKeys d k d = none := by
  simp [revealKeys]

@[simp] theorem revealKeys_of_ne {n : ℕ} {d i : Fin n} (h : i ≠ d) (k : Fin n → K) :
    revealKeys d k i = some (k i) := by
  simp [revealKeys, h]

theorem revealKeys_apply {n : ℕ} (d i : Fin n) (k : Fin n → K) :
    revealKeys d k i = if i = d then none else some (k i) := by
  simp [revealKeys]

private theorem revealKeys_update {n : ℕ} (d : Fin n) (k : Fin n → K) (kd : K) :
    revealKeys d (Function.update k d kd) = revealKeys d k := by
  funext i
  by_cases h : i = d <;> simp [h]

/-- The `n`-way nested encryption security experiment ([BonehShoup2023], §2.4, p. 37). Differs from
the book by indexing keys from `0` via `Fin n` and permitting the vacuous `n = 0` case. -/
@[expose] def Cipher.nestedExperiment {σ : Type} (E : Cipher K M M) (sampleKey : ProbComp K)
    (valid : M → M → Bool) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ)
    (b : Bool) : Experiment := do
  let keys ← OracleComp.replicateFin n sampleKey
  let (req, state) ← A.choose ()
  if valid req.pair.msg₀ req.pair.msg₁ then
    let c ← (E.nested n).encrypt keys (req.pair.select b)
    A.guess state ⟨c, revealKeys req.withheld keys⟩
  else
    return false

end NestedDef

section Splitting

variable {K M : Type}

/-- Piece of the reduction: encrypt under prefix layers `0, ..., d - 1` (reads only `k i` for
`i < d`). -/
@[expose] def Cipher.nestedPrefix (E : Cipher K M M) :
    ∀ {n : ℕ}, Fin n → (Fin n → K) → M → ProbComp M
  | 0, d, _, _ => d.elim0
  | _ + 1, d, k, m => Fin.cases (pure m)
      (fun i => do
        let c ← E.encrypt (k 0) m
        E.nestedPrefix i (Fin.tail k) c) d

/-- Piece of the reduction: encrypt under suffix layers `d + 1, ..., n - 1` (reads only `k i` for
`d < i`). -/
@[expose] def Cipher.nestedSuffix (E : Cipher K M M) :
    ∀ {n : ℕ}, Fin n → (Fin n → K) → M → ProbComp M
  | 0, d, _, _ => d.elim0
  | n + 1, d, k, c => Fin.cases (E.nestedEncrypt n (Fin.tail k) c)
      (fun i => E.nestedSuffix i (Fin.tail k) c) d

private theorem nestedEncrypt_update (E : Cipher K M M) :
    ∀ {n : ℕ} (d : Fin n) (k : Fin n → K) (kd : K) (m : M),
      E.nestedEncrypt n (Function.update k d kd) m = do
        let mid ← E.nestedPrefix d k m
        let c ← E.encrypt kd mid
        E.nestedSuffix d k c
  | 0, d, _, _, _ => d.elim0
  | n + 1, d, k, kd, m => by
    induction d using Fin.cases with
    | zero =>
      simp [Cipher.nestedEncrypt, Cipher.nestedPrefix, Cipher.nestedSuffix, Fin.tail_update_zero]
    | succ i =>
      simp only [Cipher.nestedEncrypt, Cipher.nestedPrefix, Cipher.nestedSuffix, Fin.cases_succ,
        bind_assoc, Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      exact bind_congr fun c => nestedEncrypt_update E i (Fin.tail k) kd c

private theorem nestedPrefix_preservesValid {E : Cipher K M M} {sampleKey : ProbComp K}
    {valid : M → M → Bool} (hpres : E.PreservesValid sampleKey valid) :
    ∀ {n : ℕ} (d : Fin n) {k : Fin n → K} (_ : ∀ i, k i ∈ (ProbComp.eval sampleKey).support)
      {m₀ m₁ : M}, valid m₀ m₁ = true → ∀ {c₀ c₁ : M},
        c₀ ∈ (ProbComp.eval (E.nestedPrefix d k m₀)).support →
        c₁ ∈ (ProbComp.eval (E.nestedPrefix d k m₁)).support → valid c₀ c₁ = true
  | 0, d, _, _, _, _, _, _, _, _, _ => d.elim0
  | n + 1, d, k, hk, m₀, m₁, hm, c₀, c₁, hc₀, hc₁ => by
    induction d using Fin.cases with
    | zero =>
      simp only [Cipher.nestedPrefix, Fin.cases_zero, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hc₀ hc₁
      simpa [hc₀, hc₁] using hm
    | succ i =>
      simp only [Cipher.nestedPrefix, Fin.cases_succ, ProbComp.eval_bind,
        PMF.mem_support_bind_iff] at hc₀ hc₁
      obtain ⟨x₀, hx₀, hc₀⟩ := hc₀
      obtain ⟨x₁, hx₁, hc₁⟩ := hc₁
      exact nestedPrefix_preservesValid hpres i (fun j => hk j.succ)
        (hpres _ (hk 0) _ _ hm _ hx₀ _ hx₁) hc₀ hc₁

end Splitting

section Reduction

variable {K M : Type}

/-- Internal state of the reduction from `n`-way nested encryption to single-key encryption. -/
structure NestedReductionState (K σ : Type) (n : ℕ) where
  /-- Saved state of the underlying `n`-way nested adversary `A`. -/
  innerState : σ
  /-- Withheld key index chosen by `A`. -/
  withheld : Fin n
  /-- Keys drawn by the reduction; coordinate `withheld` is never read. -/
  keys : Fin n → K
  /-- Whether `A`'s original message pair satisfies `valid`. -/
  admissible : Bool

/-- Single-key reduction adversary for Theorem 2.12: draws `n` keys (ignoring coordinate
`withheld`), encrypts `msg₀` and `msg₁` under the prefix `0, ..., withheld - 1`, delegates the
`withheld` layer to `oneTimeExperiment`, and finishes with the suffix `withheld + 1, ..., n - 1`
when `st.admissible` holds. -/
def nestedToSingleAdversary {σ : Type} (E : Cipher K M M) (sampleKey : ProbComp K)
    (valid : M → M → Bool) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) :
    TwoStage Unit (MessagePair M) M Bool (NestedReductionState K σ n) where
  choose _ := do
    let (req, aState) ← A.choose ()
    let keys ← OracleComp.replicateFin n sampleKey
    let m₀' ← E.nestedPrefix req.withheld keys req.pair.msg₀
    let m₁' ← E.nestedPrefix req.withheld keys req.pair.msg₁
    return (⟨m₀', m₁'⟩, ⟨aState, req.withheld, keys, valid req.pair.msg₀ req.pair.msg₁⟩)
  guess st challenge :=
    if st.admissible then do
      let c ← E.nestedSuffix st.withheld st.keys challenge
      A.guess st.innerState ⟨c, revealKeys st.withheld st.keys⟩
    else
      return false

/-- Exact output-distribution equality between the outer single-key experiment running
`nestedToSingleAdversary` and the `n`-way nested experiment running `A`, under
`E.PreservesValid sampleKey valid`. -/
theorem eval_oneTimeExperiment_nestedToSingleAdversary {σ : Type} (E : Cipher K M M)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (hpres : E.PreservesValid sampleKey valid) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) (b : Bool) :
    ProbComp.eval
        (E.oneTimeExperiment sampleKey valid (nestedToSingleAdversary E sampleKey valid n A) b) =
      ProbComp.eval (E.nestedExperiment sampleKey valid n A b) := by
  simp only [Cipher.oneTimeExperiment, Cipher.nestedExperiment, Cipher.nested, eval_lrExperiment,
    nestedToSingleAdversary, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm, PMF.bind_comm (ProbComp.eval (OracleComp.replicateFin n sampleKey))]
  refine congrArg _ (funext fun ⟨req, aState⟩ => ?_)
  by_cases hadm : valid req.pair.msg₀ req.pair.msg₁ = true
  · have hresample := (ProbComp.eval_bind_pi_update (fun _ : Fin n => sampleKey) req.withheld).symm
    simp only [hadm, ↓reduceIte, ProbComp.eval_bind]
    conv_rhs => rw [OracleComp.replicateFin_eq_pi, hresample]
    simp only [← OracleComp.replicateFin_eq_pi, PMF.bind_bind, PMF.bind_map, Function.comp_def,
      nestedEncrypt_update, revealKeys_update, ProbComp.eval_bind]
    refine congrArg _ (funext fun kd => ?_)
    refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
    have hk := (ProbComp.mem_support_replicateFin_iff n sampleKey keys).1 hkeys
    trans (ProbComp.eval (E.nestedPrefix req.withheld keys req.pair.msg₀)).bind fun m₀' =>
      (ProbComp.eval (E.nestedPrefix req.withheld keys req.pair.msg₁)).bind fun m₁' =>
        (ProbComp.eval (E.encrypt kd ((⟨m₀', m₁'⟩ : MessagePair M).select b))).bind fun c =>
          (ProbComp.eval (E.nestedSuffix req.withheld keys c)).bind fun c' =>
            ProbComp.eval (A.guess aState ⟨c', revealKeys req.withheld keys⟩)
    · refine PMF.bind_congr_on_support _ _ _ fun m₀' hm₀' => ?_
      refine PMF.bind_congr_on_support _ _ _ fun m₁' hm₁' => ?_
      simp [nestedPrefix_preservesValid hpres req.withheld hk hadm hm₀' hm₁']
    · cases b
      · simp [PMF.bind_const]
      · rw [PMF.bind_comm]
        simp [PMF.bind_const]
  · simp [hadm, PMF.bind_const]

/-- Exact advantage equality for the corrected form of Theorem 2.12 ([BonehShoup2023], §2.4,
p. 37): under `E.PreservesValid sampleKey valid`, a hypothesis the book does not state and without
which the equality fails (`tagCipher_no_wrapper`), the `n`-way nested advantage of `A` equals the
one-time advantage of `nestedToSingleAdversary`. -/
theorem advantage_nestedExperiment_eq {σ : Type} (E : Cipher K M M)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (hpres : E.PreservesValid sampleKey valid) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) :
    Experiment.advantage (E.nestedExperiment sampleKey valid n A false)
        (E.nestedExperiment sampleKey valid n A true) =
      Experiment.advantage
        (E.oneTimeExperiment sampleKey valid
          (nestedToSingleAdversary E sampleKey valid n A) false)
        (E.oneTimeExperiment sampleKey valid
          (nestedToSingleAdversary E sampleKey valid n A) true) := by
  simp only [Experiment.advantage,
    eval_oneTimeExperiment_nestedToSingleAdversary E sampleKey valid hpres]

end Reduction

section Efficiency

open Turing.MultiTapeTM

variable {K M σ : Type}

/-- Computable encoding of a `NestedRequest M n` as `(pair, withheld)`. -/
enc_structure encNestedRequest (encM : M ↪ List Bool) (n : ℕ) : NestedRequest M n where
  pair : (encMessagePair encM),
  withheld : (encFinEnum (Fin n))

/-- Computable encoding of a `NestedChallenge K M n` as `(ciphertext, revealedKeys)`. -/
enc_structure encNestedChallenge (encK : K ↪ List Bool) (encM : M ↪ List Bool) (n : ℕ) :
    NestedChallenge K M n where
  ciphertext : encM,
  revealedKeys : (encFinFn n (encOption encK))

/-- Computable encoding of `NestedReductionState K σ n`. -/
enc_structure encNestedReductionState (encK : K ↪ List Bool) (encσ : σ ↪ List Bool) (n : ℕ) :
    NestedReductionState K σ n where
  innerState : encσ,
  withheld : (encFinEnum (Fin n)),
  keys : (encFinFn n encK),
  admissible : encBool

private theorem computable_finTail {α K : Type} {encIn : α ↪ List Bool} {encK : K ↪ List Bool}
    {n : ℕ} {ks : α → Fin (n + 1) → K}
    (hks : ComputableInPolyTime ks encIn (encFinFn (n + 1) encK)) :
    ComputableInPolyTime (fun a => Fin.tail (ks a)) encIn (encFinFn n encK) :=
  ComputableInPolyTime.finFn fun i => (ComputableInPolyTime.finFn_apply encK i.succ).comp hks

@[local fun_prop]
private theorem computable_revealKeys {α K : Type} {encIn : α ↪ List Bool} {encK : K ↪ List Bool}
    {n : ℕ} {d : α → Fin n} {ks : α → Fin n → K}
    (hd : ComputableInPolyTime d encIn (encFinEnum (Fin n)))
    (hks : ComputableInPolyTime ks encIn (encFinFn n encK)) :
    ComputableInPolyTime (fun a => revealKeys (d a) (ks a)) encIn
      (encFinFn n (encOption encK)) := by
  refine ComputableInPolyTime.finFn fun i => ?_
  have h : ComputableInPolyTime (fun a => if i = d a then none else some (ks a i)) encIn
      (encOption encK) := by
    refine (ComputableInPolyTime.finite_cases hd
      (branch := fun d0 a => if i = d0 then none else some (ks a i))
      fun d0 => ?_)
    by_cases hi : i = d0
    · simpa [hi] using ComputableInPolyTime.const (none : Option K)
    · simpa [hi, Function.comp_def] using
        (ComputableInPolyTime.optionSome encK).comp
          ((ComputableInPolyTime.finFn_apply encK i).comp hks)
  simpa only [← revealKeys_apply] using h

private theorem isPPTOn_nestedEncrypt {α K M : Type} {encIn : α ↪ List Bool}
    {encK : K ↪ List Bool} {encM : M ↪ List Bool} {E : α → Cipher K M M}
    (hencrypt : IsPPTOn (encPair encIn (encPair encK encM)) encM
      fun ⟨a, k, m⟩ => (E a).encrypt k m) :
    ∀ (n : ℕ) {β : Type} {encB : β ↪ List Bool}
      {toA : β → α} {ks : β → Fin n → K} {msg : β → M},
      ComputableInPolyTime toA encB encIn →
      ComputableInPolyTime ks encB (encFinFn n encK) →
      ComputableInPolyTime msg encB encM →
      IsPPTOn encB encM fun b => (E (toA b)).nestedEncrypt n (ks b) (msg b)
  | 0, _, _, _, _, _, _, _, hmsg => hmsg.isPPTOn
  | n + 1, _, encB, toA, ks, msg, hA, hks, hmsg => by
    have hhead : IsPPTOn encB encM fun b => (E (toA b)).encrypt (ks b 0) (msg b) :=
      hencrypt.preprocess (hA.prod (((ComputableInPolyTime.finFn_apply encK 0).comp hks).prod hmsg))
    have htail : IsPPTOn (encPair encB encM) encM fun p =>
        (E (toA p.1)).nestedEncrypt n (Fin.tail (ks p.1)) p.2 :=
      isPPTOn_nestedEncrypt hencrypt n (hA.comp (ComputableInPolyTime.fst _ _))
        (computable_finTail (hks.comp (ComputableInPolyTime.fst _ _)))
        (ComputableInPolyTime.snd _ _)
    exact IsPPTOn.bind_pair hhead htail

private theorem isPPTOn_nestedPrefix_const {α K M : Type} {encIn : α ↪ List Bool}
    {encK : K ↪ List Bool} {encM : M ↪ List Bool} {E : α → Cipher K M M}
    (hencrypt : IsPPTOn (encPair encIn (encPair encK encM)) encM
      fun ⟨a, k, m⟩ => (E a).encrypt k m) :
    ∀ {n : ℕ} (d : Fin n) {β : Type} {encB : β ↪ List Bool}
      {toA : β → α} {ks : β → Fin n → K} {msg : β → M},
      ComputableInPolyTime toA encB encIn →
      ComputableInPolyTime ks encB (encFinFn n encK) →
      ComputableInPolyTime msg encB encM →
      IsPPTOn encB encM fun b => (E (toA b)).nestedPrefix d (ks b) (msg b)
  | 0, d, _, _, _, _, _, _, _, _ => d.elim0
  | n + 1, d, _, encB, toA, ks, msg, hA, hks, hmsg => by
    induction d using Fin.cases with
    | zero => simpa [Cipher.nestedPrefix] using hmsg.isPPTOn
    | succ i =>
      have hhead : IsPPTOn encB encM fun b => (E (toA b)).encrypt (ks b 0) (msg b) :=
        hencrypt.preprocess
          (hA.prod (((ComputableInPolyTime.finFn_apply encK 0).comp hks).prod hmsg))
      have htail : IsPPTOn (encPair encB encM) encM fun p =>
          (E (toA p.1)).nestedPrefix i (Fin.tail (ks p.1)) p.2 :=
        isPPTOn_nestedPrefix_const hencrypt i (hA.comp (ComputableInPolyTime.fst _ _))
          (computable_finTail (hks.comp (ComputableInPolyTime.fst _ _)))
          (ComputableInPolyTime.snd _ _)
      simpa [Cipher.nestedPrefix] using IsPPTOn.bind_pair hhead htail

@[local fun_prop]
private theorem isPPTOn_nestedPrefix {ι α K M : Type} {n : ℕ} {encIdx : ι ↪ List Bool}
    {encIn : α ↪ List Bool} {encK : K ↪ List Bool} {encM : M ↪ List Bool}
    {E : ι → Cipher K M M} {idx : α → ι} {d : α → Fin n} {ks : α → Fin n → K} {msg : α → M}
    (hencrypt : IsPPTOn (encPair encIdx (encPair encK encM)) encM
      fun ⟨i, k, m⟩ => (E i).encrypt k m)
    (hidx : ComputableInPolyTime idx encIn encIdx)
    (hd : ComputableInPolyTime d encIn (encFinEnum (Fin n)))
    (hks : ComputableInPolyTime ks encIn (encFinFn n encK))
    (hmsg : ComputableInPolyTime msg encIn encM) :
    IsPPTOn encIn encM fun a => (E (idx a)).nestedPrefix (d a) (ks a) (msg a) :=
  IsPPTOn.finite_cases hd fun choice =>
    isPPTOn_nestedPrefix_const hencrypt choice hidx hks hmsg

private theorem isPPTOn_nestedSuffix_const {α K M : Type} {encIn : α ↪ List Bool}
    {encK : K ↪ List Bool} {encM : M ↪ List Bool} {E : α → Cipher K M M}
    (hencrypt : IsPPTOn (encPair encIn (encPair encK encM)) encM
      fun ⟨a, k, m⟩ => (E a).encrypt k m) :
    ∀ {n : ℕ} (d : Fin n) {β : Type} {encB : β ↪ List Bool}
      {toA : β → α} {ks : β → Fin n → K} {c : β → M},
      ComputableInPolyTime toA encB encIn →
      ComputableInPolyTime ks encB (encFinFn n encK) →
      ComputableInPolyTime c encB encM →
      IsPPTOn encB encM fun b => (E (toA b)).nestedSuffix d (ks b) (c b)
  | 0, d, _, _, _, _, _, _, _, _ => d.elim0
  | n + 1, d, _, _, toA, ks, c, hA, hks, hc => by
    induction d using Fin.cases with
    | zero =>
      simpa [Cipher.nestedSuffix] using
        isPPTOn_nestedEncrypt hencrypt n hA (computable_finTail hks) hc
    | succ i =>
      simpa [Cipher.nestedSuffix] using
        isPPTOn_nestedSuffix_const hencrypt i hA (computable_finTail hks) hc

@[local fun_prop]
private theorem isPPTOn_nestedSuffix {ι α K M : Type} {n : ℕ} {encIdx : ι ↪ List Bool}
    {encIn : α ↪ List Bool} {encK : K ↪ List Bool} {encM : M ↪ List Bool}
    {E : ι → Cipher K M M} {idx : α → ι} {d : α → Fin n} {ks : α → Fin n → K} {c : α → M}
    (hencrypt : IsPPTOn (encPair encIdx (encPair encK encM)) encM
      fun ⟨i, k, m⟩ => (E i).encrypt k m)
    (hidx : ComputableInPolyTime idx encIn encIdx)
    (hd : ComputableInPolyTime d encIn (encFinEnum (Fin n)))
    (hks : ComputableInPolyTime ks encIn (encFinFn n encK))
    (hc : ComputableInPolyTime c encIn encM) :
    IsPPTOn encIn encM fun a => (E (idx a)).nestedSuffix (d a) (ks a) (c a) :=
  IsPPTOn.finite_cases hd fun choice =>
    isPPTOn_nestedSuffix_const hencrypt choice hidx hks hc

/-- Uniform strict polynomial-time efficiency of `nestedToSingleAdversary`: for a fixed `n`, when
`sampleKey` and `encrypt` are strict PPT and `valid` is computable in polynomial time (each
uniformly in the security parameter), the reductions of any uniform strict PPT family `A` (with
revealed keys encoded as an `encFinFn` table) form a uniform strict PPT family. -/
theorem isPPT_nestedToSingleAdversary {K M σ : Type} {encK : K ↪ List Bool}
    {encM : M ↪ List Bool} {encσ : σ ↪ List Bool}
    {E : ℕ → Cipher K M M} {sampleKey : ℕ → ProbComp K} {valid : ℕ → M → M → Bool}
    (hsampleKey : IsPPTOn encUnary encK sampleKey)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encK encM)) encM
      fun ⟨sec, k, m⟩ => (E sec).encrypt k m)
    (hvalid : ComputableInPolyTime (fun ⟨sec, m₀, m₁⟩ => valid sec m₀ m₁)
      (encPair encUnary (encPair encM encM)) encBool)
    (n : ℕ)
    {A : ℕ → TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ}
    (hA : TwoStage.IsPPT encUnit (encNestedRequest encM n) (encNestedChallenge encK encM n)
      encBool encσ A) :
    TwoStage.IsPPT encUnit (encMessagePair encM) encM encBool
      (encNestedReductionState encK encσ n)
      (fun sec => nestedToSingleAdversary (E sec) (sampleKey sec) (valid sec) n (A sec)) where
  choose := by
    have hchoose := hA.choose
    ppt [nestedToSingleAdversary]
  guess := by
    have hguess := hA.guess
    ppt [nestedToSingleAdversary]

/-- Corrected form of Theorem 2.12 ([BonehShoup2023], §2.4, p. 37), with the admissibility
hypothesis `PreservesValid` that the book does not state and without which the theorem fails
(`tagCipher_no_wrapper` in the tests): for every constant `n : ℕ`, if `sampleKey` and
`encrypt` are strict PPT, `valid` is computable in polynomial time (each uniformly in the security
parameter), `E` preserves admissibility (`PreservesValid`) at every security parameter, and `E` is
one-time semantically secure (`Game.Indistinguishable` against uniform strict PPT `TwoStage`
adversaries for every state type and encoding), then `E` is semantically secure for `n`-way nesting
with all keys but one revealed. -/
theorem indistinguishable_nestedExperiment_of_oneTimeExperiment
    {K M : Type} {encK : K ↪ List Bool} {encM : M ↪ List Bool}
    (E : ℕ → Cipher K M M) (sampleKey : ℕ → ProbComp K) (valid : ℕ → M → M → Bool)
    (hsampleKey : IsPPTOn encUnary encK sampleKey)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encK encM)) encM
      fun ⟨sec, k, m⟩ => (E sec).encrypt k m)
    (hvalid : ComputableInPolyTime (fun ⟨sec, m₀, m₁⟩ => valid sec m₀ m₁)
      (encPair encUnary (encPair encM encM)) encBool)
    (hpres : ∀ sec, (E sec).PreservesValid (sampleKey sec) (valid sec))
    (n : ℕ)
    (hsec : ∀ {σ' : Type} (encσ' : σ' ↪ List Bool),
      Game.Indistinguishable
        (fun (B : ℕ → TwoStage Unit (MessagePair M) M Bool σ') sec =>
          ProbComp.eval ((E sec).oneTimeExperiment (sampleKey sec) (valid sec) (B sec) false))
        (fun B sec =>
          ProbComp.eval ((E sec).oneTimeExperiment (sampleKey sec) (valid sec) (B sec) true))
        (TwoStage.IsPPT encUnit (encMessagePair encM) encM encBool encσ')) :
    ∀ {σ : Type} (encσ : σ ↪ List Bool),
      Game.Indistinguishable
        (fun (A : ℕ → TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) sec =>
          ProbComp.eval ((E sec).nestedExperiment (sampleKey sec) (valid sec) n (A sec) false))
        (fun A sec =>
          ProbComp.eval ((E sec).nestedExperiment (sampleKey sec) (valid sec) n (A sec) true))
        (TwoStage.IsPPT encUnit (encNestedRequest encM n) (encNestedChallenge encK encM n)
          encBool encσ) := by
  intro σ encσ
  refine Game.Indistinguishable.of_reduction
    (hsec (encNestedReductionState encK encσ n))
    (fun A sec => nestedToSingleAdversary (E sec) (sampleKey sec) (valid sec) n (A sec))
    (fun A hA => isPPT_nestedToSingleAdversary hsampleKey hencrypt hvalid n hA)
    (fun A _ => ⟨fun _ => 1, fun _ => 0, .const 1, negligible_zero, fun sec => ?_⟩)
  have heq :=
    advantage_nestedExperiment_eq (E sec) (sampleKey sec) (valid sec) (hpres sec) n (A sec)
  simp only [Experiment.advantage] at heq
  simpa only [Nat.cast_one, one_mul, add_zero] using le_of_eq heq

end Efficiency

end Cslib.Crypto
