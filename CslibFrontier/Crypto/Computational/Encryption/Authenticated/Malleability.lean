/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Ciphertext-mauling attacks on symmetric ciphers

A symmetric cipher fails ciphertext integrity as soon as an adversary can transform (*maul*) an
honest ciphertext into a different word that still decrypts ([BonehShoup2023], Section 9.1). It
fails chosen-ciphertext security when, in addition, what the mauled word decrypts to reveals which
message was encrypted ([BonehShoup2023], Section 9.2.1). A mauled word that decrypts to the same
plaintext in both worlds breaks ciphertext integrity but not CCA security. This module packages the
two attacks that the cipher counterexamples of the library share. Each result here is an attack
theorem: it concludes that a cipher is *not* secure.

`maulCIAdversary maul bit ctBound` asks for an encryption of `bit^n`, reads the first `ctBound n`
bits of the reply and outputs `maul n` of them. If, on every honest key and ciphertext, the mauled
word differs from the ciphertext and decrypts, it wins the ciphertext-integrity games with
probability `1`.

`maulCCAAdversary maul target ctBound` asks for the challenge encryption of `(0^n, 1^n)`, asks the
decryption oracle on `maul n` of the (truncated) ciphertext, and outputs whether the first `n + 1`
bits of the oracle's reply equal `encOption encBits (some target^n)`, which is `n + 1` bits long.
The CCA hypothesis is world-dependent: in world `bit` the mauled word must differ from the
challenge and decrypt to `(cond target bit !bit)^n`, the challenge message itself when
`target = true` and its complement when `target = false`. The adversary then outputs `bit` for
`n ≥ 1`. A variant allows any other outcome on a bad event of negligible probability in each
world.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.maulCIAdversary`: the one-query mauling forger.
* `Cslib.Crypto.SymmetricCipher.maulCCAAdversary`: the two-query mauling distinguisher.

## Main results

* `Cslib.Crypto.SymmetricCipher.isOraclePPT_maulCIAdversary`,
  `Cslib.Crypto.SymmetricCipher.isOraclePPT_maulCCAAdversary`: both adversaries are oracle PPT
  when the maul and the reply bound are polynomial-time.
* `Cslib.Crypto.SymmetricCipher.eval_ciOneTimeGame_maulCIAdversary`,
  `Cslib.Crypto.SymmetricCipher.eval_ciGame_maulCIAdversary`: the forger wins with probability `1`.
* `Cslib.Crypto.SymmetricCipher.not_oneTimeCiphertextIntegrity_of_maul`: a polynomial-time maul
  that works from some parameter on breaks one-time ciphertext integrity.
* `Cslib.Crypto.SymmetricCipher.eval_ccaOneTimeGame_maulCCAAdversary`,
  `Cslib.Crypto.SymmetricCipher.eval_ccaOneTimeGame_maulCCAAdversary_eq_pure`: when the mauled
  word decrypts to a fixed message, the distinguisher outputs the result of the Boolean test of
  that message against `target^n`, which may fail; when it decrypts to `(cond target bit !bit)^n`,
  it outputs `bit`.
* `Cslib.Crypto.SymmetricCipher.not_oneTimeINDCCA_of_maul`,
  `Cslib.Crypto.SymmetricCipher.not_oneTimeINDCCA_of_maul_or_bad`: a polynomial-time maul with the
  world-dependent decryption above from some parameter on, exactly or outside a negligible bad
  event, breaks one-time CCA security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 9.1 and 9.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace SymmetricCipher

/-! ### The mauling forger -/

/-- **One-query ciphertext-mauling forger**: it asks for an encryption of `bit^n`, reads the first
`ctBound n` bits of the reply and outputs `maul n` of them. -/
def maulCIAdversary (maul : ℕ → List Bool → List Bool) (bit : Bool) (ctBound : ℕ → ℕ) :
    CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n bit)
    return maul n ct

/-- The mauling forger is oracle PPT when the maul and the reply bound are polynomial-time. -/
theorem isOraclePPT_maulCIAdversary {maul : ℕ → List Bool → List Bool}
    (hmaul : ComputableInPolyTime (fun p : ℕ × List Bool => maul p.1 p.2)
      (encPair encUnary encBits) encBits)
    (bit : Bool) {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (maulCIAdversary maul bit ctBound) := by
  ppt [maulCIAdversary]

private theorem singleton_contains_eq_false_of_ne {ct ct' : List Bool} (hne : ct' ≠ ct) :
    [ct].contains ct' = false := by
  rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_singleton]
  exact hne

/-- The mauling forger wins `ciOneTimeGame` with probability `1` at a parameter `n` where
`ctBound n` bounds the ciphertext lengths and, on every honest key and ciphertext of `bit^n`, the
mauled word differs from the ciphertext and decrypts. -/
theorem eval_ciOneTimeGame_maulCIAdversary (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧ (E.decrypt n k (maul n ct)).isSome = true) :
    ProbComp.eval (E.ciOneTimeGame (maulCIAdversary maul bit ctBound) n) = PMF.pure true := by
  simp only [ciOneTimeGame, maulCIAdversary, oneTimeCIEncryptionOracle, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hne, hdec⟩ := hmaul k hk ct hct
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct),
    singleton_contains_eq_false_of_ne hne, hdec]
  rfl

/-- The mauling forger wins `ciGame` with probability `1` under the conditions of
`eval_ciOneTimeGame_maulCIAdversary`. -/
theorem eval_ciGame_maulCIAdversary (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧ (E.decrypt n k (maul n ct)).isSome = true) :
    ProbComp.eval (E.ciGame (maulCIAdversary maul bit ctBound) n) = PMF.pure true := by
  rw [← E.eval_ciOneTimeGame_maulCIAdversary bit ctBound n hctBound hmaul]
  simp only [ciGame, ciOneTimeGame, maulCIAdversary, ciEncryptionOracle,
    oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate, beq_self_eq_true,
    Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]

/-- **A polynomial-time ciphertext maul breaks one-time ciphertext integrity.** If, for every
`n ≥ n₀`, on every honest key and ciphertext of `bit^n`, `maul n` changes the ciphertext into a
word that decrypts, then `E` is not `OneTimeCiphertextIntegrity`. -/
theorem not_oneTimeCiphertextIntegrity_of_maul (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool}
    (hmaulPoly : ComputableInPolyTime (fun p : ℕ × List Bool => maul p.1 p.2)
      (encPair encUnary encBits) encBits)
    (bit : Bool) (n₀ : ℕ)
    (hmaul : ∀ n, n₀ ≤ n → ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧ (E.decrypt n k (maul n ct)).isSome = true) :
    ¬ E.OneTimeCiphertextIntegrity := by
  intro hci
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have := hci.negligible (maulCIAdversary maul bit ctBound)
    (isOraclePPT_maulCIAdversary hmaulPoly bit hctBoundPoly)
  have hle : ∀ᶠ n in Filter.atTop, (1 : ℝ≥0) ≤
      Game.succProbability (ProbComp.eval (E.ciOneTimeGame (maulCIAdversary maul bit ctBound) n)) :=
    Filter.eventually_atTop.mpr ⟨n₀, fun n hn => by
      rw [E.eval_ciOneTimeGame_maulCIAdversary bit ctBound n (hctBound n) (hmaul n hn)]
      simp [Game.succProbability]⟩
  exact not_negligible_const one_ne_zero (by negligible eventually hle)

/-! ### The mauling distinguisher -/

/-- **Two-query ciphertext-mauling distinguisher**: it asks for the challenge encryption of
`(0^n, 1^n)`, reads the first `ctBound n` bits of the reply, asks the decryption oracle on
`maul n` of them, and outputs whether the first `n + 1` bits of the reply encode `target^n`. -/
def maulCCAAdversary (maul : ℕ → List Bool → List Bool) (target : Bool) (ctBound : ℕ → ℕ) :
    CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$> ProbOracleComp.query (true, maul n ct)
    return (reply == encOption encBits (some (List.replicate n target)))

/-- The mauling distinguisher is oracle PPT when the maul and the reply bound are
polynomial-time. -/
theorem isOraclePPT_maulCCAAdversary {maul : ℕ → List Bool → List Bool}
    (hmaul : ComputableInPolyTime (fun p : ℕ × List Bool => maul p.1 p.2)
      (encPair encUnary encBits) encBits)
    (target : Bool) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (maulCCAAdversary maul target ctBound) := by
  ppt [maulCCAAdversary]

/-- The joint distribution of an honest key and a ciphertext of `bit^n` under it. -/
private noncomputable abbrev encDist (E : SymmetricCipher) (bit : Bool) (n : ℕ) :
    PMF (List Bool × List Bool) := do
  let k ← ProbComp.eval (E.keyGen n)
  let ct ← ProbComp.eval (E.encrypt n k (List.replicate n bit))
  return (k, ct)

private theorem mem_support_encDist {E : SymmetricCipher} {bit : Bool} {n : ℕ}
    {p : List Bool × List Bool} (hp : p ∈ (E.encDist bit n).support) :
    p.1 ∈ (ProbComp.eval (E.keyGen n)).support ∧
      p.2 ∈ (ProbComp.eval (E.encrypt n p.1 (List.replicate n bit))).support := by
  simp only [encDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hp
  obtain ⟨k, hk, ct, hct, rfl⟩ := hp
  exact ⟨hk, hct⟩

private theorem eval_ccaOneTimeGame_maulCCAAdversary_eq_bind (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (target bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hne : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support, maul n ct ≠ ct) :
    ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) bit n) =
      (E.encDist bit n).bind fun p => PMF.pure
        (List.take (n + 1) (encOption encBits (E.decrypt n p.1 (maul n p.2))) ==
          encOption encBits (some (List.replicate n target))) := by
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by cases bit <;> rfl
  simp only [ccaOneTimeGame, maulCCAAdversary, oneTimeCCAOracle, encDist,
    unframe_encPair_encBits, dropFrame_encPair_encBits, hbit, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
    runWith_norm, pmf_norm]
  peel_binds k ct
  simp [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem),
    hne k k_mem ct ct_mem, pmf_norm]

/-- The mauling distinguisher's output in world `bit` at a parameter `n` where `ctBound n` bounds
the ciphertext lengths and, on every honest key and ciphertext of `bit^n`, the mauled word differs
from the ciphertext and decrypts to `msg`: it is the test of the first `n + 1` bits of the
encoding of `msg` against `target^n`. -/
theorem eval_ccaOneTimeGame_maulCCAAdversary (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (target bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) (msg : List Bool)
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧ E.decrypt n k (maul n ct) = some msg) :
    ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) bit n) =
      PMF.pure (List.take (n + 1) (encOption encBits (some msg)) ==
        encOption encBits (some (List.replicate n target))) := by
  rw [E.eval_ccaOneTimeGame_maulCCAAdversary_eq_bind target bit ctBound n hctBound
    fun k hk ct hct => (hmaul k hk ct hct).1]
  refine PMF.bind_eq_pure_of_forall_mem_support fun p hp => ?_
  obtain ⟨hk, hct⟩ := mem_support_encDist hp
  rw [(hmaul p.1 hk p.2 hct).2]

/-- The reply that world `bit` decrypts to, `(cond target bit !bit)^n`, passes the test against
`target^n` exactly when `bit = true`, unless `n = 0`. -/
private theorem take_encOption_replicate_beq {n : ℕ} (target bit : Bool)
    (hn : bit = true ∨ 1 ≤ n) :
    (List.take (n + 1) (encOption encBits (some (List.replicate n (cond target bit !bit)))) ==
      encOption encBits (some (List.replicate n target))) = bit := by
  rw [List.take_of_length_le (by simp [encOption_some, encBits_apply])]
  rcases hn with rfl | hn
  · cases target <;> simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    cases target <;> cases bit <;> simp [encOption_some, encBits_apply]

/-- The mauling distinguisher outputs the challenge bit with probability `1` in world `bit`, for
`bit = true` or `n ≥ 1`, when on every honest key and ciphertext of `bit^n` the mauled word differs
from the ciphertext and decrypts to `(cond target bit !bit)^n`. -/
theorem eval_ccaOneTimeGame_maulCCAAdversary_eq_pure (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (target bit : Bool) (ctBound : ℕ → ℕ) {n : ℕ}
    (hn : bit = true ∨ 1 ≤ n) (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧
          E.decrypt n k (maul n ct) = some (List.replicate n (cond target bit !bit))) :
    ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) bit n) =
      PMF.pure bit := by
  rw [E.eval_ccaOneTimeGame_maulCCAAdversary target bit ctBound n hctBound _ hmaul,
    take_encOption_replicate_beq target bit hn]

private theorem le_ccaAdvantage_of_maul (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool} (target : Bool) (ctBound : ℕ → ℕ)
    (bad : Bool → List Bool × List Bool → Bool) (n : ℕ) (hn : 1 ≤ n)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ bit k, k ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧
          (E.decrypt n k (maul n ct) = some (List.replicate n (cond target bit !bit)) ∨
            bad bit (k, ct) = true)) :
    (1 : ℝ≥0) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad false p)) +
      Game.advantage
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) false n))
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad true p)) := by
  have hworld (bit : Bool) := E.eval_ccaOneTimeGame_maulCCAAdversary_eq_bind target bit ctBound n
    hctBound fun k hk ct hct => (hmaul bit k hk ct hct).1
  have htrue : (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad true p)) := by
    have h1 : (1 : ℝ≥0) =
        Game.succProbability ((E.encDist true n).bind fun _ => PMF.pure true) := by
      simp [Game.succProbability]
    rw [h1, hworld true]
    refine Game.succProbability_bind_pure_le_add _ fun p hp _ => ?_
    obtain ⟨hk, hct⟩ := mem_support_encDist hp
    rcases (hmaul true p.1 hk p.2 hct).2 with hdec | hbad
    · rw [hdec]
      exact Or.inl (take_encOption_replicate_beq target true (Or.inr hn))
    · exact Or.inr hbad
  have hfalse :
      Game.succProbability
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) false n)) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad false p)) := by
    rw [hworld false]
    refine Game.succProbability_mono (Probability.PMF.map_true_mono _ fun p hp hwin => ?_)
    obtain ⟨hk, hct⟩ := mem_support_encDist hp
    rcases (hmaul false p.1 hk p.2 hct).2 with hdec | hbad
    · rw [hdec, take_encOption_replicate_beq target false (Or.inr hn)] at hwin
      contradiction
    · exact hbad
  have hadv := Game.succProbability_le_add_of_advantage_le
    (g₀ := ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) true n))
    (g₁ := ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) false n))
    (Game.advantage_comm _ _).le
  exact htrue.trans (by gcongr; exact hadv.trans (by gcongr))

/-- **A polynomial-time ciphertext maul breaks one-time CCA security, up to a bad event.** If, for
every `n ≥ n₀` and world `bit`, on every honest key `k` and ciphertext `ct` of `bit^n`, `maul n`
changes `ct` into a word that decrypts to `(cond target bit !bit)^n` unless `bad n bit k ct`
holds, and the bad event has negligible probability in each world, then `E` is not
`OneTimeINDCCA`. -/
theorem not_oneTimeINDCCA_of_maul_or_bad (E : SymmetricCipher)
    {maul : ℕ → List Bool → List Bool}
    (hmaulPoly : ComputableInPolyTime (fun p : ℕ × List Bool => maul p.1 p.2)
      (encPair encUnary encBits) encBits)
    (target : Bool) (bad : ℕ → Bool → List Bool → List Bool → Bool)
    (hbadNeg : ∀ bit, Negligible fun n => Game.succProbability (do
        let k ← ProbComp.eval (E.keyGen n)
        let ct ← ProbComp.eval (E.encrypt n k (List.replicate n bit))
        return bad n bit k ct))
    (n₀ : ℕ)
    (hmaul : ∀ n, n₀ ≤ n → ∀ bit, ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧
          (E.decrypt n k (maul n ct) = some (List.replicate n (cond target bit !bit)) ∨
            bad n bit k ct = true)) :
    ¬ E.OneTimeINDCCA := by
  intro hcca
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have := hcca (maulCCAAdversary maul target ctBound)
    (isOraclePPT_maulCCAAdversary hmaulPoly target hctBoundPoly)
  have hbad (bit : Bool) : Negligible fun n => Game.succProbability
      ((E.encDist bit n).bind fun p => PMF.pure (bad n bit p.1 p.2)) := by
    refine (hbadNeg bit).congr fun n => ?_
    simp only [encDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
  have := hbad false
  have := hbad true
  have hle : ∀ᶠ n in Filter.atTop, (1 : ℝ≥0) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad n false p.1 p.2)) +
      Game.advantage
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) false n))
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul target ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad n true p.1 p.2)) :=
    Filter.eventually_atTop.mpr ⟨max n₀ 1, fun n hn =>
      E.le_ccaAdvantage_of_maul target ctBound (fun bit p => bad n bit p.1 p.2) n
        ((le_max_right n₀ 1).trans hn) (hctBound n)
        fun bit k hk ct hct => hmaul n ((le_max_left n₀ 1).trans hn) bit k hk ct hct⟩
  exact not_negligible_const one_ne_zero (by negligible eventually hle)

/-- **A polynomial-time ciphertext maul breaks one-time CCA security.** If, for every `n ≥ n₀` and
world `bit`, on every honest key and ciphertext of `bit^n`, `maul n` changes the ciphertext into a
word that decrypts to `(cond target bit !bit)^n`, then `E` is not `OneTimeINDCCA`. -/
theorem not_oneTimeINDCCA_of_maul (E : SymmetricCipher) {maul : ℕ → List Bool → List Bool}
    (hmaulPoly : ComputableInPolyTime (fun p : ℕ × List Bool => maul p.1 p.2)
      (encPair encUnary encBits) encBits)
    (target : Bool) (n₀ : ℕ)
    (hmaul : ∀ n, n₀ ≤ n → ∀ bit, ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul n ct ≠ ct ∧
          E.decrypt n k (maul n ct) = some (List.replicate n (cond target bit !bit))) :
    ¬ E.OneTimeINDCCA :=
  E.not_oneTimeINDCCA_of_maul_or_bad hmaulPoly target (fun _ _ _ _ => false)
    (fun _ => by simp [Game.succProbability]) n₀
    fun n hn bit k hk ct hct => (hmaul n hn bit k hk ct hct).imp_right Or.inl

end SymmetricCipher

end Cslib.Crypto
