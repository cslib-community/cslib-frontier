/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# Nested encryption

Given a symmetric cipher `E : Cipher K M M` whose ciphertext space equals its message space,
`E.nested n` (`Cipher.nested`) encrypts a message sequentially under `n` keys
`k 0, ..., k (n - 1)` and decrypts in reverse order ([BonehShoup2023], §2.4, p. 37).
`Cipher.nested_correct` shows that `E.nested n` is correct whenever `E` is.

`Cipher.nestedExperiment` formalizes the multi-key security game of Theorem 2.12 in
[BonehShoup2023] (§2.4, p. 37): `n` independent keys are drawn from `sampleKey`, the adversary
selects a challenge message pair together with a withheld key index `withheld : Fin n`, and if
`valid msg₀ msg₁` holds, the challenger encrypts the selected message under `E.nested n` and
passes the ciphertext together with every key except `withheld` (`revealKeys`) to the guessing
stage.

For any cipher preserving `valid` on supported keys (`Cipher.PreservesValid`),
`nestedToSingleAdversary` reduces `E.nestedExperiment` to `E.oneTimeExperiment`, preserving the
exact output distribution on each challenge bit (`eval_oneTimeExperiment_nestedToSingleAdversary`)
and therefore the exact advantage (`advantage_nestedExperiment_eq`). Asymptotic polynomial-time
certificates for `nestedToSingleAdversary` sit on top of this module and are not included here.

Differences from [BonehShoup2023] (§2.4, p. 37):
* Ciphertexts share the message type `M` so layers compose uniformly for any `n : ℕ`.
* Keys are indexed from `0` via `Fin n` rather than `1, ..., n`, with `k 0` applied innermost.
* `n = 0` is permitted as a vacuous boundary case (`NestedRequest M 0` is uninhabited).
* The book leaves implicit that inner encryption layers keep pairs admissible; here
  `Cipher.PreservesValid` makes this condition explicit.

## Main definitions

* `Cslib.Crypto.nestedEncrypt`, `Cslib.Crypto.nestedDecrypt`, `Cslib.Crypto.Cipher.nested`:
  `n`-way nested encryption and decryption.
* `Cslib.Crypto.Cipher.PreservesValid`: preservation of challenge-pair admissibility under
  encryption.
* `Cslib.Crypto.NestedRequest`, `Cslib.Crypto.NestedChallenge`, `Cslib.Crypto.revealKeys`,
  `Cslib.Crypto.Cipher.nestedExperiment`: adversary request/challenge records and multi-key
  security experiment for Theorem 2.12.
* `Cslib.Crypto.NestedReductionState`, `Cslib.Crypto.nestedToSingleAdversary`: single-key
  reduction adversary.

## Main results

* `Cslib.Crypto.Cipher.nested_correct`: correctness of `E.nested n` from `E.Correct`.
* `Cslib.Crypto.eval_oneTimeExperiment_nestedToSingleAdversary`: exact distribution equality
  between `E.oneTimeExperiment` against `nestedToSingleAdversary` and `E.nestedExperiment`.
* `Cslib.Crypto.advantage_nestedExperiment_eq`: exact advantage equality for Theorem 2.12.

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
@[expose] def nestedEncrypt (E : Cipher K M M) : ∀ n : ℕ, (Fin n → K) → M → ProbComp M
  | 0, _, m => pure m
  | n + 1, k, m => do
    let c ← E.encrypt (k 0) m
    nestedEncrypt E n (Fin.tail k) c

/-- `n`-way nested decryption peeling keys `k (n - 1), ..., k 0` from outermost to innermost. -/
def nestedDecrypt (E : Cipher K M M) : ∀ n : ℕ, (Fin n → K) → M → Option M
  | 0, _, c => some c
  | n + 1, k, c => (nestedDecrypt E n (Fin.tail k) c).bind (E.decrypt (k 0))

/-- The `n`-way nested cipher `E_n` ([BonehShoup2023], §2.4, p. 37). Unlike the book's `1`-based
indexing, keys are indexed by `Fin n` with `k 0` applied innermost; `n = 0` is the identity. -/
@[expose] def Cipher.nested (E : Cipher K M M) (n : ℕ) : Cipher (Fin n → K) M M where
  encrypt := nestedEncrypt E n
  decrypt := nestedDecrypt E n

/-- `n`-way nested encryption of a correct cipher is correct. -/
theorem Cipher.nested_correct {E : Cipher K M M} (hE : E.Correct) (n : ℕ) :
    (E.nested n).Correct := by
  intro k m c hc
  simp only [Cipher.nested] at hc ⊢
  induction n generalizing m c with
  | zero =>
    simp only [nestedEncrypt, nestedDecrypt, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hc ⊢
    exact congrArg some hc
  | succ n ih =>
    simp only [nestedEncrypt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc
    obtain ⟨c₀, hc₀, hc⟩ := hc
    simp only [nestedDecrypt]
    rw [ih (Fin.tail k) c₀ c hc, Option.bind_some]
    exact hE (k 0) m c₀ hc₀

/-- Admissibility preservation under encryption: encrypting an admissible pair `(m₀, m₁)` under any
supported key produces an admissible ciphertext pair `(c₀, c₁)`. The book leaves this condition
implicit; Theorem 2.12 requires it so prefix-encrypted pairs stay admissible for the outer game. -/
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

/-- Piece of the reduction: sample `n` independent keys except at index `d`. -/
@[expose] def sampleRevealedKeys (sampleKey : ProbComp K) :
    ∀ {n : ℕ}, Fin n → ProbComp (Fin n → Option K)
  | 0, d => d.elim0
  | n + 1, d => Fin.cases
    (do
      let ks ← OracleComp.replicateFin n sampleKey
      return Fin.cons none (fun i => some (ks i)))
    (fun i => do
      let k₀ ← sampleKey
      let rest ← sampleRevealedKeys sampleKey i
      return Fin.cons (some k₀) rest)
    d

private def fillKey {n : ℕ} (_d : Fin n) (revealed : Fin n → Option K) (kd : K) : Fin n → K :=
  fun i => (revealed i).getD kd

private theorem replicateFin_eq_bind_sampleRevealedKeys (sampleKey : ProbComp K) :
    ∀ {n : ℕ} (d : Fin n),
      ProbComp.eval (OracleComp.replicateFin n sampleKey) =
        (ProbComp.eval (sampleRevealedKeys sampleKey d)).bind fun revealed =>
          (ProbComp.eval sampleKey).map (fillKey d revealed)
  | 0, d => d.elim0
  | n + 1, d => by
    induction d using Fin.cases with
    | zero =>
      simp only [OracleComp.replicateFin_succ, sampleRevealedKeys, Fin.cases_zero,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map,
        PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      rw [PMF.bind_comm]
      congr 1; funext k₀
      congr 1; funext ks
      congr 1
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    | succ i =>
      simp only [OracleComp.replicateFin_succ, sampleRevealedKeys, Fin.cases_succ,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
      rw [replicateFin_eq_bind_sampleRevealedKeys sampleKey i]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      congr 1; funext k₀
      congr 1; funext rest
      congr 1; funext kd
      congr 1
      funext j
      induction j using Fin.cases with
      | zero => rfl
      | succ j' => rfl

private theorem revealKeys_fillKey_of_support (sampleKey : ProbComp K) :
    ∀ {n : ℕ} (d : Fin n) {revealed : Fin n → Option K}
      (_ : revealed ∈ (ProbComp.eval (sampleRevealedKeys sampleKey d)).support) (kd : K),
      revealKeys d (fillKey d revealed kd) = revealed
  | 0, d, _, _, _ => d.elim0
  | n + 1, d, revealed, h, kd => by
    induction d using Fin.cases generalizing revealed with
    | zero =>
      simp only [sampleRevealedKeys, Fin.cases_zero, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at h
      obtain ⟨ks, -, rfl⟩ := h
      funext j
      induction j using Fin.cases with
      | zero => simp [revealKeys]
      | succ j' => simp [revealKeys, fillKey, Fin.succ_ne_zero]
    | succ i =>
      simp only [sampleRevealedKeys, Fin.cases_succ, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at h
      obtain ⟨k₀, -, rest, hrest, rfl⟩ := h
      have ih := revealKeys_fillKey_of_support sampleKey i hrest kd
      funext j
      induction j using Fin.cases with
      | zero => simp [revealKeys, fillKey, (Fin.succ_ne_zero i).symm]
      | succ j' =>
        have h' := congrFun ih j'
        simp only [revealKeys, fillKey, Fin.cons_succ, Fin.succ_inj] at h' ⊢
        exact h'

/-- Piece of the reduction: encrypt under the prefix keys `0, ..., d - 1`. -/
@[expose] def nestedPrefixOpt (E : Cipher K M M) :
    ∀ {n : ℕ}, Fin n → (Fin n → Option K) → M → ProbComp M
  | 0, d, _, _ => d.elim0
  | _ + 1, d, revealed, m => Fin.cases
    (pure m)
    (fun i => do
      let c ← match revealed 0 with | some k => E.encrypt k m | none => pure m
      nestedPrefixOpt E i (Fin.tail revealed) c)
    d

/-- Piece of the reduction: encrypt under a partial key table, skipping `none`. -/
@[expose] def nestedEncryptOpt (E : Cipher K M M) : ∀ n : ℕ, (Fin n → Option K) → M → ProbComp M
  | 0, _, m => pure m
  | n + 1, k, m => do
    let c ← match k 0 with | some key => E.encrypt key m | none => pure m
    nestedEncryptOpt E n (Fin.tail k) c

/-- Piece of the reduction: encrypt under the suffix keys `d + 1, ..., n - 1`. -/
@[expose] def nestedSuffixOpt (E : Cipher K M M) :
    ∀ {n : ℕ}, Fin n → (Fin n → Option K) → M → ProbComp M
  | 0, d, _, _ => d.elim0
  | n + 1, d, revealed, c => Fin.cases
    (nestedEncryptOpt E n (Fin.tail revealed) c)
    (fun i => nestedSuffixOpt E i (Fin.tail revealed) c)
    d

end Splitting

section Reduction

variable {K M : Type}

private theorem nestedEncryptOpt_some (E : Cipher K M M) :
    ∀ (n : ℕ) (k : Fin n → K) (m : M),
      nestedEncryptOpt E n (fun i => some (k i)) m = nestedEncrypt E n k m
  | 0, _, _ => rfl
  | n + 1, k, m => by
    simp only [nestedEncryptOpt, nestedEncrypt]
    congr 1; funext c
    exact nestedEncryptOpt_some E n (Fin.tail k) c

private theorem nestedEncrypt_eq_split (E : Cipher K M M) (sampleKey : ProbComp K) :
    ∀ {n : ℕ} (d : Fin n) {revealed : Fin n → Option K}
      (_ : revealed ∈ (ProbComp.eval (sampleRevealedKeys sampleKey d)).support)
      (kd : K) (m : M),
      ProbComp.eval (nestedEncrypt E n (fillKey d revealed kd) m) =
        ProbComp.eval do
          let mid ← nestedPrefixOpt E d revealed m
          let c ← E.encrypt kd mid
          nestedSuffixOpt E d revealed c
  | 0, d, _, _, _, _ => d.elim0
  | n + 1, d, revealed, h, kd, m => by
    induction d using Fin.cases generalizing revealed m with
    | zero =>
      simp only [sampleRevealedKeys, Fin.cases_zero, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at h
      obtain ⟨ks, -, rfl⟩ := h
      simp only [nestedEncrypt, fillKey, Fin.cons_zero, Option.getD_none,
        nestedPrefixOpt, nestedSuffixOpt, Fin.cases_zero,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      congr 1; funext c
      rw [show Fin.tail (fillKey 0
          (Fin.cons (none : Option K) (fun j => some (ks j)) : Fin (n + 1) → Option K) kd) =
          ks from by funext j; rfl]
      rw [show Fin.tail
          (Fin.cons (none : Option K) (fun j => some (ks j)) : Fin (n + 1) → Option K) =
          fun j => some (ks j) from by funext j; rfl]
      rw [nestedEncryptOpt_some]
    | succ i =>
      simp only [sampleRevealedKeys, Fin.cases_succ, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at h
      obtain ⟨k₀, -, rest, hrest, rfl⟩ := h
      simp only [nestedEncrypt, fillKey, Fin.cons_zero, Option.getD_some,
        nestedPrefixOpt, nestedSuffixOpt, Fin.cases_succ,
        ProbComp.eval_bind, PMF.bind_bind]
      congr 1; funext c₀
      rw [show Fin.tail (fillKey i.succ
          (Fin.cons (some k₀) rest : Fin (n + 1) → Option K) kd) = fillKey i rest kd from by
        funext j; rfl]
      rw [show Fin.tail (Fin.cons (some k₀) rest : Fin (n + 1) → Option K) = rest from by
        funext j; rfl]
      simpa only [ProbComp.eval_bind] using
        nestedEncrypt_eq_split E sampleKey i hrest kd c₀

private theorem nestedPrefixOpt_preservesValid {E : Cipher K M M} {sampleKey : ProbComp K}
    {valid : M → M → Bool} (hpres : E.PreservesValid sampleKey valid) :
    ∀ {n : ℕ} (d : Fin n) {revealed : Fin n → Option K}
      (_ : revealed ∈ (ProbComp.eval (sampleRevealedKeys sampleKey d)).support)
      {m₀ m₁ : M}, valid m₀ m₁ = true →
      ∀ {c₀ c₁ : M},
        c₀ ∈ (ProbComp.eval (nestedPrefixOpt E d revealed m₀)).support →
        c₁ ∈ (ProbComp.eval (nestedPrefixOpt E d revealed m₁)).support →
        valid c₀ c₁ = true
  | 0, d, _, _, _, _, _, _, _, _, _ => d.elim0
  | n + 1, d, revealed, h, m₀, m₁, hm, c₀, c₁, hc₀, hc₁ => by
    induction d using Fin.cases generalizing revealed m₀ m₁ with
    | zero =>
      simp only [nestedPrefixOpt, Fin.cases_zero, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hc₀ hc₁
      simpa [hc₀, hc₁] using hm
    | succ i =>
      simp only [sampleRevealedKeys, Fin.cases_succ, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at h
      obtain ⟨k₀, hk₀, rest, hrest, rfl⟩ := h
      simp only [nestedPrefixOpt, Fin.cases_succ, Fin.cons_zero, ProbComp.eval_bind,
        PMF.mem_support_bind_iff] at hc₀ hc₁
      obtain ⟨x₀, hx₀, hc₀'⟩ := hc₀
      obtain ⟨x₁, hx₁, hc₁'⟩ := hc₁
      have htailOpt : Fin.tail (Fin.cons (some k₀) rest : Fin (n + 1) → Option K) = rest := by
        funext j; rfl
      rw [htailOpt] at hc₀' hc₁'
      have hx : valid x₀ x₁ = true := hpres k₀ hk₀ m₀ m₁ hm x₀ hx₀ x₁ hx₁
      exact nestedPrefixOpt_preservesValid hpres i hrest hx hc₀' hc₁'

/-- Internal state of the reduction from `n`-way nested encryption to single-key encryption. -/
structure NestedReductionState (K : Type) (σ : Type) (n : ℕ) where
  /-- Saved state of the underlying `n`-way nested adversary `A`. -/
  innerState : σ
  /-- Withheld key index chosen by `A`. -/
  withheld : Fin n
  /-- Keys sampled and revealed by the reduction (`none` at `withheld`). -/
  revealedKeys : Fin n → Option K
  /-- Whether `A`'s original message pair satisfies `valid`. -/
  admissible : Bool

/-- Reduction adversary `B` for [BonehShoup2023], Theorem 2.12 (p. 37). Samples all keys except
`req.withheld`, encrypts both challenge plaintexts through the prefix layers `0, ..., d - 1`, and
in `guess` applies the suffix layers `d + 1, ..., n - 1` before calling `A.guess` whenever the
original pair was admissible. -/
@[expose] def nestedToSingleAdversary {σ : Type} (E : Cipher K M M) (sampleKey : ProbComp K)
    (valid : M → M → Bool) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) :
    TwoStage Unit (MessagePair M) M Bool (NestedReductionState K σ n) where
  choose _ := do
    let (req, aState) ← A.choose ()
    let revealed ← sampleRevealedKeys sampleKey req.withheld
    let m₀' ← nestedPrefixOpt E req.withheld revealed req.pair.msg₀
    let m₁' ← nestedPrefixOpt E req.withheld revealed req.pair.msg₁
    let adm := valid req.pair.msg₀ req.pair.msg₁
    return (⟨m₀', m₁'⟩, ⟨aState, req.withheld, revealed, adm⟩)
  guess st challenge := do
    if st.admissible then
      let c ← nestedSuffixOpt E st.withheld st.revealedKeys challenge
      A.guess st.innerState ⟨c, st.revealedKeys⟩
    else
      return false

/-- Running `E.oneTimeExperiment` against `nestedToSingleAdversary` induces the exact same output
distribution as `E.nestedExperiment` against `A` when `E` preserves admissibility under
`sampleKey`. -/
theorem eval_oneTimeExperiment_nestedToSingleAdversary {σ : Type} (E : Cipher K M M)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (hpres : E.PreservesValid sampleKey valid) (n : ℕ)
    (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) (b : Bool) :
    ProbComp.eval
        (E.oneTimeExperiment sampleKey valid (nestedToSingleAdversary E sampleKey valid n A) b) =
      ProbComp.eval (E.nestedExperiment sampleKey valid n A b) := by
  simp only [Cipher.oneTimeExperiment, Cipher.nestedExperiment, lrExperiment,
    nestedToSingleAdversary, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm, PMF.bind_comm (ProbComp.eval (OracleComp.replicateFin n sampleKey))]
  congr 1; funext ⟨req, aState⟩
  by_cases hadm : valid req.pair.msg₀ req.pair.msg₁ = true
  · simp only [hadm, ↓reduceIte]
    rw [PMF.bind_comm (ProbComp.eval sampleKey)]
    trans ((ProbComp.eval (sampleRevealedKeys sampleKey req.withheld)).bind fun revealed =>
      (ProbComp.eval sampleKey).bind fun kd =>
        (ProbComp.eval (nestedPrefixOpt E req.withheld revealed (req.pair.select b))).bind
          fun mid =>
            (ProbComp.eval (E.encrypt kd mid)).bind fun c₀ =>
              (ProbComp.eval (nestedSuffixOpt E req.withheld revealed c₀)).bind fun c =>
                ProbComp.eval (A.guess aState ⟨c, revealed⟩))
    · refine PMF.bind_congr_on_support _ _ _ fun revealed hrev => ?_
      congr 1; funext kd
      have hdrop :
          ((ProbComp.eval (nestedPrefixOpt E req.withheld revealed req.pair.msg₀)).bind fun m₀' =>
            (ProbComp.eval (nestedPrefixOpt E req.withheld revealed req.pair.msg₁)).bind fun m₁' =>
              ProbComp.eval (if valid m₀' m₁' = true then do
                let c ← E.encrypt kd (({ msg₀ := m₀', msg₁ := m₁' } : MessagePair M).select b)
                let c_1 ← nestedSuffixOpt E req.withheld revealed c
                A.guess aState ⟨c_1, revealed⟩
              else pure false)) =
          ((ProbComp.eval (nestedPrefixOpt E req.withheld revealed req.pair.msg₀)).bind fun m₀' =>
            (ProbComp.eval (nestedPrefixOpt E req.withheld revealed req.pair.msg₁)).bind fun m₁' =>
              (ProbComp.eval (E.encrypt kd (if b = true then m₁' else m₀'))).bind fun c₀ =>
                (ProbComp.eval (nestedSuffixOpt E req.withheld revealed c₀)).bind fun c =>
                  ProbComp.eval (A.guess aState ⟨c, revealed⟩)) := by
        refine PMF.bind_congr_on_support _ _ _ fun m₀' hm₀' => ?_
        refine PMF.bind_congr_on_support _ _ _ fun m₁' hm₁' => ?_
        simp only [nestedPrefixOpt_preservesValid hpres req.withheld hrev hadm hm₀' hm₁',
          ↓reduceIte, ProbComp.eval_bind, MessagePair.select, Bool.cond_eq_ite]
      rw [hdrop]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, MessagePair.select, Bool.cond_false]
        congr 1; funext m₀'
        exact PMF.bind_const _ _
      · rw [PMF.bind_comm]
        simp only [↓reduceIte, MessagePair.select, Bool.cond_true]
        congr 1; funext m₁'
        exact PMF.bind_const _ _
    · have hleft :
          ((ProbComp.eval (sampleRevealedKeys sampleKey req.withheld)).bind fun revealed =>
            (ProbComp.eval sampleKey).bind fun kd =>
              (ProbComp.eval (nestedPrefixOpt E req.withheld revealed (req.pair.select b))).bind
                fun mid =>
                  (ProbComp.eval (E.encrypt kd mid)).bind fun c₀ =>
                    (ProbComp.eval (nestedSuffixOpt E req.withheld revealed c₀)).bind fun c =>
                      ProbComp.eval (A.guess aState ⟨c, revealed⟩)) =
          ((ProbComp.eval (sampleRevealedKeys sampleKey req.withheld)).bind fun revealed =>
            (ProbComp.eval sampleKey).bind fun kd =>
              (ProbComp.eval (nestedEncrypt E n (fillKey req.withheld revealed kd)
                (req.pair.select b))).bind fun c =>
                  ProbComp.eval (A.guess aState ⟨c, revealKeys req.withheld
                    (fillKey req.withheld revealed kd)⟩)) := by
        refine PMF.bind_congr_on_support _ _ _ fun revealed hrev => ?_
        congr 1; funext kd
        have hsplit := nestedEncrypt_eq_split E sampleKey req.withheld hrev kd (req.pair.select b)
        simp only [ProbComp.eval_bind] at hsplit
        rw [hsplit, revealKeys_fillKey_of_support sampleKey req.withheld hrev kd]
        simp only [PMF.bind_bind]
      rw [hleft, replicateFin_eq_bind_sampleRevealedKeys sampleKey req.withheld]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, Cipher.nested,
        ProbComp.eval_bind]
  · simp only [hadm, Bool.false_eq_true, ↓reduceIte]
    have hfalse : ∀ (c : Bool) (p : ProbComp M),
        ProbComp.eval (if c = true then (do let _ ← p; pure false) else pure false) =
          PMF.pure false := by
      intro c p
      split_ifs <;>
        simp [ProbComp.eval_pure, ProbComp.eval_map, PMF.map, Function.comp_def, PMF.bind_const]
    simp_rw [hfalse, PMF.bind_const]
    simp [ProbComp.eval_pure]

/-- Exact advantage equality of [BonehShoup2023], Theorem 2.12 (p. 37): when `E` preserves
admissibility under `sampleKey`, every `n`-way nested encryption adversary `A` has the exact same
advantage as the single-key reduction adversary `nestedToSingleAdversary E sampleKey valid n A`. -/
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

end Cslib.Crypto
