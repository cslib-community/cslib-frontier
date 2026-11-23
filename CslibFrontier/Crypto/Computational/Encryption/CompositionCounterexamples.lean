/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
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
# Generic Composition Counterexamples for Authenticated Encryption

This module formalizes the generic composition separations and counterexamples of
[Katz and Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020], Chapter 5.
They are stated in terms of fresh-message encryption unforgeability (`SymmetricCipher.EncForge`),
which is defined, with its positive results, in
`CslibFrontier/Crypto/Computational/Encryption/EncForge.lean`.

1. **Separation of `INDCPA ∧ EncForge` from `INDCCA` and `CiphertextIntegrity`
   (`SymmetricCipher.tailFallback`, `INDCPA.tailFallback`, `EncForge.tailFallback`,
   `not_ciphertextIntegrity_tailFallback`, `not_indcca_tailFallback`)**
   ([KatzLindell2020], Exercise 5.10, printed p. 165): for any `E : SymmetricCipher`,
   `E.tailFallback` keeps `keyGen` and `encrypt` unchanged and modifies `decrypt n k ct` to fall
   back to `E.decrypt n k ct.tail` whenever `E.decrypt n k ct = none` and `!ct.isEmpty`. This
   preserves `INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
   `OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (by prepending `false` to a queried
   ciphertext) and breaking `OneTimeINDCCA` and `INDCCA` whenever `E.EncForge` holds.
2. **Encrypt-then-MAC under a non-strong MAC (`MACScheme.redundantTag`, `EUFCMA.redundantTag`,
   `not_sufCma_redundantTag`, `not_indcca_encryptThenMAC_redundantTag`,
   `encryptThenMAC_redundantTag_counterexample`)** ([KatzLindell2020], Exercise 5.4, printed
   p. 164): for any `M : MACScheme`, `M.redundantTag` keeps `keyGen`, `msgLen`, and `sign`
   unchanged while accepting either `M.verify sk msg tag` or `!tag.isEmpty && M.verify sk msg
   tag.tail`. This preserves `EUFCMA` and `OneTimeEUFCMA` while breaking `OneTimeSUFCMA` and
   `SUFCMA`; when combined with any cipher `E` via `encryptThenMAC E M.redundantTag hctLen`, the
   resulting cipher satisfies `INDCPA` and `EncForge` (under `E.INDCPA` and `M.EUFCMA`) yet fails
   `OneTimeCiphertextIntegrity` and `CiphertextIntegrity` with adversary advantage `1`, and
   `OneTimeINDCCA` and `INDCCA` with advantage `1` for every `n ≥ 1`.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.tailFallback`, `tailCIAdversary`, `prependFalseBitCIAdversary`,
  `tailFallbackCCAAdversary`: Exercise 5.10 ciphertext-tail fallback transformation and reductions /
  attackers ([KatzLindell2020], Exercise 5.10).
* `Cslib.Crypto.MACScheme.redundantTag`, `tailTagForger`, `redundantTagForger`,
  `etmRedundantCIAdversary`, `etmRedundantCCAAdversary`: Exercise 5.4 redundant-tag MAC
  transformation and reductions / attackers ([KatzLindell2020], Exercise 5.4).

## Main results

* `Cslib.Crypto.SymmetricCipher.INDCPA.tailFallback`,
  `Cslib.Crypto.SymmetricCipher.EncForge.tailFallback`,
  `Cslib.Crypto.SymmetricCipher.not_ciphertextIntegrity_tailFallback`,
  `Cslib.Crypto.SymmetricCipher.not_indcca_tailFallback`,
  `Cslib.Crypto.SymmetricCipher.tailFallback_counterexample`: Exercise 5.10
  separation of `INDCPA ∧ EncForge` from `INDCCA` and `CiphertextIntegrity`.
* `Cslib.Crypto.MACScheme.EUFCMA.redundantTag`,
  `Cslib.Crypto.MACScheme.not_sufCma_redundantTag`,
  `Cslib.Crypto.not_ciphertextIntegrity_encryptThenMAC_redundantTag`,
  `Cslib.Crypto.not_indcca_encryptThenMAC_redundantTag`,
  `Cslib.Crypto.encryptThenMAC_redundantTag_counterexample`: Exercise 5.4 counterexample to
  Encrypt-then-MAC CCA security under a non-strong MAC.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Exercises 5.4 and 5.10 (pp. 164–165).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 9.1 and 9.4.1 (pp. 358–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

private theorem succProbability_bind_pure_bool_le {α : Type} (p : PMF α) (f g : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g a))) := by
  unfold Game.succProbability
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) (Probability.PMF.map_true_mono p hfg)

private theorem succProbability_bind_pure_bool_le_add {α : Type} (p : PMF α) (f g₁ g₂ : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g₁ a = true ∨ g₂ a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g₁ a))) +
        Game.succProbability (p.bind (fun a => PMF.pure (g₂ a))) := by
  unfold Game.succProbability
  rw [← ENNReal.toNNReal_add (PMF.apply_ne_top _ true) (PMF.apply_ne_top _ true)]
  exact ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ true, PMF.apply_ne_top _ true⟩)
    (Probability.PMF.map_true_le_add p hfg)

/-! ### Katz–Lindell Exercise 5.10: `INDCPA ∧ EncForge` Does Not Imply `INDCCA`

Given any symmetric cipher `E`, `E.tailFallback` has the same `keyGen` and `encrypt` as `E`, and
decrypts `ct` by returning `E.decrypt n k ct` when it is `some msg`, or falling back to
`E.decrypt n k ct.tail` when `ct` is non-empty and `E.decrypt n k ct = none`. This preserves
`INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
`OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (and breaking `OneTimeINDCCA` and `INDCCA`
whenever `E.EncForge` holds, by querying decryption on `false :: ct`). -/

namespace SymmetricCipher

/-! ### Generic Ciphertext-Mauling Attack Combinators -/

private abbrev maulCIAdversary (maul : List Bool → List Bool) (bit : Bool) (ctBound : ℕ → ℕ) :
    CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n bit)
    return maul ct

private theorem isOraclePPT_maulCIAdversary {maul : List Bool → List Bool}
    (hmaul : ComputableInPolyTime maul encBits encBits) (bit : Bool) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (maulCIAdversary maul bit ctBound) := by
  ppt [maulCIAdversary]

private abbrev maulCCAAdversary (maul : List Bool → List Bool) (ctBound : ℕ → ℕ) :
    CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$>
      ProbOracleComp.query (true, maul ct)
    return (reply == encOption encBits (some m1))

private theorem isOraclePPT_maulCCAAdversary {maul : List Bool → List Bool}
    (hmaul : ComputableInPolyTime maul encBits encBits) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (maulCCAAdversary maul ctBound) := by
  ppt [maulCCAAdversary]

private theorem singleton_contains_eq_false_of_ne {ct ct' : List Bool} (hne : ct' ≠ ct) :
    [ct].contains ct' = false := by
  rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_singleton]
  exact hne

private theorem eval_ciOneTimeGame_maulCIAdversary (E : SymmetricCipher)
    {maul : List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧ (E.decrypt n k (maul ct)).isSome = true) :
    ProbComp.eval (E.ciOneTimeGame (maulCIAdversary maul bit ctBound) n) = PMF.pure true := by
  simp only [ciOneTimeGame, maulCIAdversary, oneTimeCIEncryptionOracle, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hne, hdec⟩ := hmaul k hk ct hct
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct),
    singleton_contains_eq_false_of_ne hne, hdec]
  rfl

private theorem eval_ciGame_maulCIAdversary (E : SymmetricCipher)
    {maul : List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧ (E.decrypt n k (maul ct)).isSome = true) :
    ProbComp.eval (E.ciGame (maulCIAdversary maul bit ctBound) n) = PMF.pure true := by
  rw [← E.eval_ciOneTimeGame_maulCIAdversary bit ctBound n hctBound hmaul]
  simp only [ciGame, ciOneTimeGame, maulCIAdversary, ciEncryptionOracle,
    oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate, beq_self_eq_true,
    Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]

private theorem le_ciAdvantage_of_maul (E : SymmetricCipher)
    {maul : List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧ (E.decrypt n k (maul ct)).isSome = true) :
    (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval (E.ciOneTimeGame (maulCIAdversary maul bit ctBound) n)) := by
  rw [E.eval_ciOneTimeGame_maulCIAdversary bit ctBound n hctBound hmaul]
  simp [Game.succProbability]

private theorem not_oneTimeCiphertextIntegrity_of_maul (E : SymmetricCipher)
    {maul : List Bool → List Bool} (hmaulPoly : ComputableInPolyTime maul encBits encBits)
    (bit : Bool)
    (hmaul : ∀ n, ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧ (E.decrypt n k (maul ct)).isSome = true) :
    ¬ E.OneTimeCiphertextIntegrity := by
  intro hci
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have := hci.negligible (maulCIAdversary maul bit ctBound)
    (isOraclePPT_maulCIAdversary hmaulPoly bit hctBoundPoly)
  exact not_negligible_const one_ne_zero (by
    negligible using fun n => E.le_ciAdvantage_of_maul bit ctBound n (hctBound n) (hmaul n))

private noncomputable abbrev encDist (E : SymmetricCipher) (bit : Bool) (n : ℕ) :
    PMF (List Bool × List Bool) :=
  (ProbComp.eval (E.keyGen n)).bind fun k =>
    (ProbComp.eval (E.encrypt n k (List.replicate n bit))).map fun ct => (k, ct)

private theorem eval_ccaOneTimeGame_maulCCAAdversary (E : SymmetricCipher)
    {maul : List Bool → List Bool} (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hne : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support, maul ct ≠ ct) :
    ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) bit n) =
      (E.encDist bit n).bind fun p => PMF.pure
        (List.take (n + 1) (encOption encBits (E.decrypt n p.1 (maul p.2))) ==
          encOption encBits (some (List.replicate n true))) := by
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by cases bit <;> rfl
  simp only [ccaOneTimeGame, maulCCAAdversary, oneTimeCCAOracle, encDist,
    unframe_encPair_encBits, dropFrame_encPair_encBits, hbit, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
    runWith_norm, pmf_norm]
  peel_binds k ct
  simp [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem),
    hne k k_mem ct ct_mem, pmf_norm]

private theorem take_encOption_some_replicate (n : ℕ) (b : Bool) :
    List.take (n + 1) (encOption encBits (some (List.replicate n b))) =
      encOption encBits (some (List.replicate n b)) := by
  apply List.take_of_length_le
  simp [encOption_some, encBits_apply]

private theorem encOption_some_replicate_false_beq_true {n : ℕ} (hn : 1 ≤ n) :
    (encOption encBits (some (List.replicate n false)) ==
      encOption encBits (some (List.replicate n true))) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have heq := Option.some.inj ((encOption encBits).injective (beq_iff_eq.mp h))
  cases n with
  | zero => contradiction
  | succ m => simp at heq

private theorem le_ccaAdvantage_of_maul (E : SymmetricCipher)
    {maul : List Bool → List Bool} (ctBound : ℕ → ℕ)
    (bad : Bool → List Bool × List Bool → Bool) (n : ℕ) (hn : 1 ≤ n)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hmaul : ∀ bit k, k ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧
          (E.decrypt n k (maul ct) = some (List.replicate n bit) ∨ bad bit (k, ct) = true)) :
    (1 : ℝ≥0) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad false p)) +
      Game.advantage
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) false n))
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad true p)) := by
  have htrue : (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad true p)) := by
    have h1 : (1 : ℝ≥0) =
        Game.succProbability ((E.encDist true n).bind fun _ => PMF.pure true) := by
      simp [Game.succProbability]
    rw [h1, E.eval_ccaOneTimeGame_maulCCAAdversary true ctBound n hctBound
      fun k hk ct hct => (hmaul true k hk ct hct).1]
    refine succProbability_bind_pure_bool_le_add _ _ _ _ fun ⟨k, ct⟩ hp _ => ?_
    simp only [encDist, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, Prod.mk.injEq] at hp
    obtain ⟨k, hk, ct, hct, rfl, rfl⟩ := hp
    rcases (hmaul true k hk ct hct).2 with hdec | hbad
    · rw [hdec, take_encOption_some_replicate, beq_self_eq_true]
      exact Or.inl rfl
    · exact Or.inr hbad
  have hfalse :
      Game.succProbability
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) false n)) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad false p)) := by
    rw [E.eval_ccaOneTimeGame_maulCCAAdversary false ctBound n hctBound
      fun k hk ct hct => (hmaul false k hk ct hct).1]
    refine succProbability_bind_pure_bool_le _ _ _ fun ⟨k, ct⟩ hp hwin => ?_
    simp only [encDist, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, Prod.mk.injEq] at hp
    obtain ⟨k, hk, ct, hct, rfl, rfl⟩ := hp
    rcases (hmaul false k hk ct hct).2 with hdec | hbad
    · rw [hdec, take_encOption_some_replicate, encOption_some_replicate_false_beq_true hn] at hwin
      contradiction
    · exact hbad
  have hadv := Game.succProbability_le_add_of_advantage_le
    (g₀ := ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) true n))
    (g₁ := ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) false n))
    (Game.advantage_comm _ _).le
  exact htrue.trans (by gcongr; exact hadv.trans (by gcongr))

private theorem not_oneTimeINDCCA_of_maul (E : SymmetricCipher)
    {maul : List Bool → List Bool} (hmaulPoly : ComputableInPolyTime maul encBits encBits)
    (bad : ℕ → Bool → List Bool × List Bool → Bool)
    (hbadNeg : ∀ bit ctBound, ComputableInPolyTime ctBound encUnary encUnary →
      (∀ n, E.CiphertextLengthLE n (ctBound n)) →
      Negligible fun n =>
        Game.succProbability ((E.encDist bit n).bind fun p => PMF.pure (bad n bit p)))
    (hmaul : ∀ n, 1 ≤ n → ∀ bit k, k ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k (List.replicate n bit))).support,
        maul ct ≠ ct ∧
          (E.decrypt n k (maul ct) = some (List.replicate n bit) ∨ bad n bit (k, ct) = true)) :
    ¬ E.OneTimeINDCCA := by
  intro hcca
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have := hcca (maulCCAAdversary maul ctBound) (isOraclePPT_maulCCAAdversary hmaulPoly hctBoundPoly)
  have := hbadNeg false ctBound hctBoundPoly hctBound
  have := hbadNeg true ctBound hctBoundPoly hctBound
  have hle : ∀ᶠ n in Filter.atTop, (1 : ℝ≥0) ≤
      Game.succProbability ((E.encDist false n).bind fun p => PMF.pure (bad n false p)) +
      Game.advantage
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) false n))
        (ProbComp.eval (E.ccaOneTimeGame (maulCCAAdversary maul ctBound) true n)) +
      Game.succProbability ((E.encDist true n).bind fun p => PMF.pure (bad n true p)) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn =>
      E.le_ccaAdvantage_of_maul ctBound (bad n) n hn (hctBound n) (hmaul n hn)⟩
  exact not_negligible_const one_ne_zero (by negligible eventually hle)

/-- Modified symmetric cipher `E.tailFallback` ([KatzLindell2020], Exercise 5.10, printed p. 165):
`keyGen` and `encrypt` are identical to `E`, while `decrypt n k ct` returns `E.decrypt n k ct`
whenever that succeeds and otherwise falls back to `E.decrypt n k ct.tail` on non-empty `ct`.
Its ciphertext space is `E.ctSpace` together with the nonempty words whose tail lies in it. -/
noncomputable def tailFallback (E : SymmetricCipher) : SymmetricCipher where
  keyGen := E.keyGen
  encrypt := E.encrypt
  decrypt n k ct :=
    if (E.decrypt n k ct).isSome then
      E.decrypt n k ct
    else if ct.isEmpty then
      none
    else
      E.decrypt n k ct.tail
  ctSpace n ct := E.ctSpace n ct || (!ct.isEmpty && E.ctSpace n ct.tail)
  decrypt_eq_none_of_ctSpace_eq_false n k ct h := by
    have hct : E.decrypt n k ct = none := E.decrypt_eq_none_of_ctSpace_eq_false n k ct (by simp_all)
    cases ct with
    | nil => simp [hct]
    | cons b ct => simp [hct, E.decrypt_eq_none_of_ctSpace_eq_false n k ct (by simp_all)]
  keyGen_ppt := E.keyGen_ppt
  encrypt_ppt := E.encrypt_ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp [E.decrypt_encrypt n k hk msg hmsg ct hct]

/-- `E.tailFallback` has the exact same `cpaGame` as `E`. -/
@[simp]
theorem cpaGame_tailFallback (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) :
    E.tailFallback.cpaGame adversary bit n = E.cpaGame adversary bit n :=
  rfl

/-- `E.tailFallback` has the exact same `cpaOneTimeGame` as `E`. -/
@[simp]
theorem cpaOneTimeGame_tailFallback (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) :
    E.tailFallback.cpaOneTimeGame adversary bit n = E.cpaOneTimeGame adversary bit n :=
  rfl

/-- `tailFallback` preserves `INDCPA` ([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem INDCPA.tailFallback {E : SymmetricCipher} (h : E.INDCPA) :
    E.tailFallback.INDCPA :=
  h

/-- `tailFallback` preserves `OneTimeINDCPA`. -/
theorem OneTimeINDCPA.tailFallback {E : SymmetricCipher} (h : E.OneTimeINDCPA) :
    E.tailFallback.OneTimeINDCPA :=
  h

/-- Reduction adversary that runs `adversary` and drops the leading bit of its candidate
ciphertext (`List.tail`). -/
def tailCIAdversary (adversary : CIAdversary) : CIAdversary :=
  fun n aux => List.tail <$> adversary n aux

/-- `tailCIAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_tailCIAdversary {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (tailCIAdversary adversary) :=
  (hadversary.on.map (by fun_prop)).isOraclePPT

/-- `tailCIAdversary` preserves any per-input query-count bound `IsQueryBounded Q`. -/
theorem isQueryBounded_tailCIAdversary (adversary : CIAdversary) (n : ℕ) (aux : List Bool)
    {Q : ℕ} (hq : (adversary n aux).IsQueryBounded Q) :
    (tailCIAdversary adversary n aux).IsQueryBounded Q := by
  simpa only [tailCIAdversary, OracleComp.isCostBounded_map_iff] using hq

/-- **Quantitative `EncForge` bound for `E.tailFallback`** ([KatzLindell2020], Exercise 5.10,
printed p. 165): any fresh-message forgery against `E.tailFallback` either already succeeds
directly against `E` on `ct` or succeeds against `E` on `ct.tail` via `tailCIAdversary`. -/
theorem succProbability_encForgeGame_tailFallback_le (E : SymmetricCipher)
    (adversary : CIAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval (E.tailFallback.encForgeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (E.encForgeGame adversary n)) +
        Game.succProbability
          (ProbComp.eval (E.encForgeGame (tailCIAdversary adversary) n)) := by
  have horacle (k : List Bool) :
      E.tailFallback.encForgeOracle n k = E.encForgeOracle n k := rfl
  have hkeyGen : E.tailFallback.keyGen = E.keyGen := rfl
  let runDist : PMF (List Bool × List Bool × List (List Bool)) :=
    (ProbComp.eval (E.keyGen n)).bind fun k =>
      (ProbOracleComp.runWith (fun req s => ProbComp.eval (E.encForgeOracle n k req s))
        (adversary n []) []).map fun out => (k, out)
  suffices Game.succProbability (runDist.bind fun p => PMF.pure
      ((E.tailFallback.decrypt n p.1 p.2.1).isSome &&
        !p.2.2.contains ((E.tailFallback.decrypt n p.1 p.2.1).getD []))) ≤
    Game.succProbability (runDist.bind fun p => PMF.pure
      ((E.decrypt n p.1 p.2.1).isSome &&
        !p.2.2.contains ((E.decrypt n p.1 p.2.1).getD []))) +
    Game.succProbability (runDist.bind fun p => PMF.pure
      ((E.decrypt n p.1 p.2.1.tail).isSome &&
        !p.2.2.contains ((E.decrypt n p.1 p.2.1.tail).getD []))) by
    simpa only [encForgeGame, tailCIAdversary, hkeyGen, horacle, runDist, runWith_norm,
      pmf_norm] using this
  refine succProbability_bind_pure_bool_le_add runDist _ _ _ fun p _ hwin => ?_
  dsimp only [tailFallback] at hwin
  split_ifs at hwin with h1 h2
  · exact Or.inl hwin
  · simp at hwin
  · exact Or.inr hwin

/-- `tailFallback` preserves `EncForge` ([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem EncForge.tailFallback {E : SymmetricCipher} (h : E.EncForge) :
    E.tailFallback.EncForge := by
  refine EncForge.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailCIAdversary adversary) (isOraclePPT_tailCIAdversary hadversary)
  negligible using E.succProbability_encForgeGame_tailFallback_le adversary

/-- One-query ciphertext-integrity / `EncForge` adversary that queries encryption on `bit^n`
(truncating the reply to `ctBound n`) and prepends `false` to the returned ciphertext. -/
def prependFalseBitCIAdversary (bit : Bool) (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n bit)
    return (false :: ct)

/-- `prependFalseBitCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_prependFalseBitCIAdversary (bit : Bool) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (prependFalseBitCIAdversary bit ctBound) := by
  ppt [prependFalseBitCIAdversary]

private theorem tailFallback_false_cons_maul (E : SymmetricCipher) (n : ℕ)
    (k msg ct : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support) (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) :
    false :: ct ≠ ct ∧ (E.tailFallback.decrypt n k (false :: ct)).isSome = true := by
  refine ⟨List.ne_cons_self.symm, ?_⟩
  dsimp only [tailFallback]
  split_ifs with h1 h2
  · exact h1
  · simp at h2
  · simp [E.decrypt_encrypt n k hk msg hmsg ct hct]

/-- In `ciOneTimeGame` against `E.tailFallback`, `prependFalseBitCIAdversary bit ctBound` wins
with probability `1` at every security parameter `n` where `ctBound n` bounds ciphertext lengths. -/
theorem eval_ciOneTimeGame_tailFallback_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval
      (E.tailFallback.ciOneTimeGame (prependFalseBitCIAdversary bit ctBound) n) =
        PMF.pure true :=
  E.tailFallback.eval_ciOneTimeGame_maulCIAdversary bit ctBound n hctBound fun k hk ct hct =>
    tailFallback_false_cons_maul E n k _ ct hk List.length_replicate hct

/-- In `ciGame` against `E.tailFallback`, `prependFalseBitCIAdversary bit ctBound` wins with
probability `1` at every security parameter `n` where `ctBound n` bounds ciphertext lengths. -/
theorem eval_ciGame_tailFallback_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval
      (E.tailFallback.ciGame (prependFalseBitCIAdversary bit ctBound) n) =
        PMF.pure true :=
  E.tailFallback.eval_ciGame_maulCIAdversary bit ctBound n hctBound fun k hk ct hct =>
    tailFallback_false_cons_maul E n k _ ct hk List.length_replicate hct

/-- `E.tailFallback` never satisfies `OneTimeCiphertextIntegrity` ([KatzLindell2020],
Exercise 5.10, printed p. 165). -/
theorem not_oneTimeCiphertextIntegrity_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.OneTimeCiphertextIntegrity :=
  E.tailFallback.not_oneTimeCiphertextIntegrity_of_maul (by fun_prop) false fun n k hk ct hct =>
    tailFallback_false_cons_maul E n k _ ct hk List.length_replicate hct

/-- `E.tailFallback` never satisfies `CiphertextIntegrity` ([KatzLindell2020], Exercise 5.10,
printed p. 165). -/
theorem not_ciphertextIntegrity_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.CiphertextIntegrity :=
  fun h => not_oneTimeCiphertextIntegrity_tailFallback E h.oneTimeCiphertextIntegrity

/-- `E.tailFallback` never satisfies `OneTimeAuthenticatedEncryption`. -/
theorem not_oneTimeAuthenticatedEncryption_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.OneTimeAuthenticatedEncryption :=
  fun h => not_oneTimeCiphertextIntegrity_tailFallback E h.2

/-- `E.tailFallback` never satisfies `AuthenticatedEncryption`. -/
theorem not_authenticatedEncryption_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.AuthenticatedEncryption :=
  fun h => not_ciphertextIntegrity_tailFallback E h.2

/-- Two-query CCA adversary against `E.tailFallback` ([KatzLindell2020], Exercise 5.10,
printed p. 165): queries left-or-right encryption on `(0^n, 1^n)` to obtain `ct`, queries
decryption on `false :: ct`, and outputs whether the decrypted message equals `some 1^n`. -/
def tailFallbackCCAAdversary (ctBound : ℕ → ℕ) : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$>
      ProbOracleComp.query (true, false :: ct)
    return (reply == encOption encBits (some m1))

/-- `tailFallbackCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_tailFallbackCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (tailFallbackCCAAdversary ctBound) := by
  ppt [tailFallbackCCAAdversary]

private theorem eval_encForgeGame_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary bit ctBound) n) =
      (E.encDist bit n).bind (fun p => PMF.pure
        ((E.decrypt n p.1 (false :: p.2)).isSome &&
          !([List.replicate n bit].contains ((E.decrypt n p.1 (false :: p.2)).getD [])))) := by
  simp only [encForgeGame, prependFalseBitCIAdversary, encForgeOracle, encDist,
    List.length_replicate, beq_self_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  peel_binds k ct
  rw [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem)]

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `OneTimeINDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem not_oneTimeINDCCA_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.OneTimeINDCCA := by
  refine E.tailFallback.not_oneTimeINDCCA_of_maul (maul := (false :: ·)) (by fun_prop)
    (fun n bit p => (E.decrypt n p.1 (false :: p.2)).isSome &&
      !([List.replicate n bit].contains ((E.decrypt n p.1 (false :: p.2)).getD [])))
    (fun bit ctBound hctBoundPoly hctBound => ?_)
    fun n _ bit k hk ct hct => ⟨List.ne_cons_self.symm, ?_⟩
  · have h := hforge.negligible (prependFalseBitCIAdversary bit ctBound)
      (isOraclePPT_prependFalseBitCIAdversary bit hctBoundPoly)
    refine h.congr fun n => ?_
    rw [eval_encForgeGame_prependFalseBitCIAdversary E bit ctBound n (hctBound n)]
    rfl
  · have hdecCt := E.decrypt_encrypt n k hk (List.replicate n bit) List.length_replicate ct hct
    cases hdec : E.decrypt n k (false :: ct) with
    | none => exact Or.inl (by simp [tailFallback, hdec, hdecCt])
    | some msg =>
      by_cases hmsg : msg = List.replicate n bit
      · exact Or.inl (by simp [tailFallback, hdec, hmsg])
      · exact Or.inr (by simp [hmsg])

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `INDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem not_indcca_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.INDCCA :=
  fun hcca => not_oneTimeINDCCA_tailFallback hforge hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.10 counterexample**
([KatzLindell2020], Exercise 5.10, printed p. 165): from any `INDCPA` and `EncForge` symmetric
cipher `E`, `E.tailFallback` simultaneously satisfies `INDCPA` and `EncForge` while failing
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem tailFallback_counterexample {E : SymmetricCipher} (hcpa : E.INDCPA)
    (hforge : E.EncForge) :
    E.tailFallback.INDCPA ∧ E.tailFallback.EncForge ∧
      ¬ E.tailFallback.OneTimeCiphertextIntegrity ∧ ¬ E.tailFallback.CiphertextIntegrity ∧
      ¬ E.tailFallback.OneTimeINDCCA ∧ ¬ E.tailFallback.INDCCA :=
  ⟨hcpa.tailFallback, hforge.tailFallback, E.not_oneTimeCiphertextIntegrity_tailFallback,
    E.not_ciphertextIntegrity_tailFallback, not_oneTimeINDCCA_tailFallback hforge,
    not_indcca_tailFallback hforge⟩

end SymmetricCipher

/-! ### Katz–Lindell Exercise 5.4: Encrypt-then-MAC Under a Non-Strong MAC

Given any `M : MACScheme`, `M.redundantTag` keeps `msgLen`, `keyGen`, and `sign` unchanged, while
`verify` accepts `tag` whenever either `M.verify sk msg tag` holds or `tag` is non-empty and
`M.verify sk msg tag.tail` holds. Consequently:

* `M.redundantTag` preserves `EUFCMA` and `OneTimeEUFCMA` (any fresh-message forgery `(msg, tag)`
  against `M.redundantTag` yields a fresh-message forgery against `M` on either `(msg, tag)` or
  `(msg, tag.tail)`),
* `M.redundantTag` fails `OneTimeSUFCMA` and `SUFCMA` (`redundantTagForger` queries `0^(M.msgLen n)`
  to obtain `tag` and outputs `(0^(M.msgLen n), false :: tag)`),
* when composed with any `E : SymmetricCipher` via `encryptThenMAC E M.redundantTag hctLen`, the
  resulting cipher satisfies `INDCPA` (if `E.INDCPA`) and `EncForge` (if `M.EUFCMA`), yet fails
  `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`
  ([KatzLindell2020], Exercise 5.4, printed p. 164). -/

namespace MACScheme

/-- **Redundant-tag MAC transformation** ([KatzLindell2020], Exercise 5.4, printed p. 164):
`M.redundantTag` keeps `msgLen`, `keyGen`, and `sign` unchanged, while `verify` accepts `tag` when
either `M.verify sk msg tag` holds or `tag` is non-empty and `M.verify sk msg tag.tail` holds. -/
noncomputable def redundantTag (M : MACScheme) : MACScheme where
  msgLen := M.msgLen
  msgLen_polyTime := M.msgLen_polyTime
  keyGen := M.keyGen
  sign := M.sign
  verify sk msg tag := M.verify sk msg tag || (!tag.isEmpty && M.verify sk msg tag.tail)
  keyGen_ppt := M.keyGen_ppt
  sign_ppt := M.sign_ppt
  verify_polyTime := by fun_prop
  verify_sign n sk hsk msg hmsg tag htag := by
    simp [M.verify_sign n sk hsk msg hmsg tag htag]

/-- Forger reduction that strips the leading bit of the candidate forgery tag. -/
noncomputable def tailTagForger (adversary : Forger) : Forger :=
  fun n aux => (fun p : List Bool × List Bool => (p.1, p.2.tail)) <$> adversary n aux

/-- `tailTagForger` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_tailTagForger {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (tailTagForger adversary) :=
  (hadversary.on.map (by fun_prop)).isOraclePPT

private theorem succProbability_redundantTag_runDist_le (M : MACScheme)
    (oracle :
      List Bool → Unit × List Bool → List (List Bool) → ProbComp (List Bool × List (List Bool)))
    (adversary : Forger) (n : ℕ) :
    let runDist : PMF (List Bool × (List Bool × List Bool) × List (List Bool)) :=
      (ProbComp.eval (M.keyGen n)).bind fun sk =>
        (ProbOracleComp.runWith (fun req s => ProbComp.eval (oracle sk req s))
          (adversary n []) []).map fun out => (sk, out)
    Game.succProbability (runDist.bind fun p => PMF.pure
        ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
          M.redundantTag.verify p.1 p.2.1.1 p.2.1.2)) ≤
      Game.succProbability (runDist.bind fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2)) +
        Game.succProbability (runDist.bind fun p => PMF.pure
            ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
              M.verify p.1 p.2.1.1 p.2.1.2.tail)) := by
  refine succProbability_bind_pure_bool_le_add _ _ _ _ fun p _ hwin => ?_
  dsimp only [redundantTag] at hwin
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hwin ⊢
  rcases hwin with ⟨⟨hlen, hfresh⟩, hver | ⟨_, hverTail⟩⟩
  · exact Or.inl ⟨⟨hlen, hfresh⟩, hver⟩
  · exact Or.inr ⟨⟨hlen, hfresh⟩, hverTail⟩

/-- **Quantitative `EUFCMA` bound for `M.redundantTag`** ([KatzLindell2020], Exercise 5.4,
printed p. 164): any fresh-message forgery against `M.redundantTag` either succeeds directly
against `M` or succeeds after stripping the leading bit of the tag via `tailTagForger`. -/
theorem succProbability_eufCmaGame_redundantTag_le (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.redundantTag.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) +
        Game.succProbability (ProbComp.eval (M.eufCmaGame (tailTagForger adversary) n)) := by
  have horacle (sk : List Bool) : M.redundantTag.signingOracle n sk = M.signingOracle n sk := rfl
  have hkeyGen : M.redundantTag.keyGen = M.keyGen := rfl
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simpa only [eufCmaGame, tailTagForger, hkeyGen, horacle, hmsgLen, runWith_norm, pmf_norm] using
    succProbability_redundantTag_runDist_le M (M.signingOracle n) adversary n

/-- **Quantitative `OneTimeEUFCMA` bound for `M.redundantTag`**. -/
theorem succProbability_eufOneTimeGame_redundantTag_le (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.redundantTag.eufOneTimeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)) +
        Game.succProbability (ProbComp.eval (M.eufOneTimeGame (tailTagForger adversary) n)) := by
  have horacle (sk : List Bool) :
      M.redundantTag.oneTimeSigningOracle n sk = M.oneTimeSigningOracle n sk := rfl
  have hkeyGen : M.redundantTag.keyGen = M.keyGen := rfl
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simpa only [eufOneTimeGame, tailTagForger, hkeyGen, horacle, hmsgLen, runWith_norm,
    pmf_norm] using
    succProbability_redundantTag_runDist_le M (M.oneTimeSigningOracle n) adversary n

/-- `redundantTag` preserves `EUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem EUFCMA.redundantTag {M : MACScheme} (h : M.EUFCMA) : M.redundantTag.EUFCMA := by
  refine EUFCMA.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  negligible using M.succProbability_eufCmaGame_redundantTag_le adversary

/-- `redundantTag` preserves `OneTimeEUFCMA`. -/
theorem OneTimeEUFCMA.redundantTag {M : MACScheme} (h : M.OneTimeEUFCMA) :
    M.redundantTag.OneTimeEUFCMA := by
  refine OneTimeEUFCMA.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  negligible using M.succProbability_eufOneTimeGame_redundantTag_le adversary

/-- One-query strong-MAC forger against `M.redundantTag`: queries `0^(M.msgLen n)` (truncating the
reply to `tagBound n`) and prepends `false` to the returned tag. -/
noncomputable def redundantTagForger (M : MACScheme) (tagBound : ℕ → ℕ) : Forger :=
  fun n _ => do
    let msg := List.replicate (M.msgLen n) false
    let tag ← List.take (tagBound n) <$> ProbOracleComp.query ((), msg)
    return (msg, false :: tag)

/-- `redundantTagForger` is strict oracle-PPT whenever `tagBound` is computable in plain polynomial
time. -/
theorem isOraclePPT_redundantTagForger (M : MACScheme) {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPT (encPair encBits encBits) (M.redundantTagForger tagBound) := by
  ppt [redundantTagForger]

/-- In `sufOneTimeGame` against `M.redundantTag`, `M.redundantTagForger tagBound` wins with
probability `1` at every security parameter `n` where `tagBound n` bounds tag lengths. -/
theorem eval_sufOneTimeGame_redundantTag_redundantTagForger (M : MACScheme)
    (tagBound : ℕ → ℕ) (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.redundantTag.sufOneTimeGame (M.redundantTagForger tagBound) n) =
      PMF.pure true := by
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simp only [sufOneTimeGame, redundantTagForger, oneTimeSigningPairOracle, signingPairOracleOn,
    hmsgLen, List.length_replicate, beq_self_eq_true, List.isEmpty_nil, Bool.and_self, ↓reduceIte,
    runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun sk hsk =>
    PMF.bind_eq_pure_of_forall_mem_support fun tag htag => ?_
  have htake : List.take (tagBound n) tag = tag :=
    List.take_of_length_le (htagBound sk hsk _ List.length_replicate tag htag)
  have hver := M.verify_sign n sk hsk _ List.length_replicate tag htag
  simp [redundantTag, htake, hver]

/-- In `sufCmaGame` against `M.redundantTag`, `M.redundantTagForger tagBound` wins with probability
`1` at every security parameter `n` where `tagBound n` bounds tag lengths. -/
theorem eval_sufCmaGame_redundantTag_redundantTagForger (M : MACScheme)
    (tagBound : ℕ → ℕ) (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.redundantTag.sufCmaGame (M.redundantTagForger tagBound) n) =
      PMF.pure true := by
  rw [← M.eval_sufOneTimeGame_redundantTag_redundantTagForger tagBound n htagBound]
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simp only [sufCmaGame, sufOneTimeGame, redundantTagForger, signingPairOracle,
    oneTimeSigningPairOracle, signingPairOracleOn, hmsgLen, List.length_replicate,
    beq_self_eq_true, List.isEmpty_nil, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]

/-- `M.redundantTag` never satisfies `OneTimeSUFCMA` ([KatzLindell2020], Exercise 5.4,
printed p. 164). -/
theorem not_oneTimeSUFCMA_redundantTag (M : MACScheme) :
    ¬ M.redundantTag.OneTimeSUFCMA := by
  intro hsuf
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := M.exists_tag_length_bound_of_length_eq
  have := hsuf.negligible (M.redundantTagForger tagBound)
    (M.isOraclePPT_redundantTagForger htagBoundPoly)
  have h1 (n : ℕ) : (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval (M.redundantTag.sufOneTimeGame (M.redundantTagForger tagBound) n)) := by
    rw [M.eval_sufOneTimeGame_redundantTag_redundantTagForger tagBound n (htagBound n)]
    simp [Game.succProbability]
  exact not_negligible_const one_ne_zero (by negligible using h1)

/-- `M.redundantTag` never satisfies `SUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_sufCma_redundantTag (M : MACScheme) :
    ¬ M.redundantTag.SUFCMA :=
  fun h => M.not_oneTimeSUFCMA_redundantTag h.oneTimeSUFCMA

end MACScheme

/-- If `M.EUFCMA` holds, then `encryptThenMAC E M.redundantTag hctLen` satisfies `EncForge`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem encForge_encryptThenMAC_redundantTag (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (heuf : M.EUFCMA) :
    (encryptThenMAC E M.redundantTag hctLen).EncForge :=
  encForge_encryptThenMAC E M.redundantTag hctLen heuf.redundantTag

/-- One-query ciphertext-integrity adversary against `encryptThenMAC E M.redundantTag hctLen`
([KatzLindell2020], Exercise 5.4, printed p. 164): queries encryption on `0^n` (truncating the
reply to `ctBound n`) to obtain `ct = encPair encBits encBits (c, tag)`, and outputs
`encPair encBits encBits (unframe ct, false :: dropFrame ct)`. -/
def etmRedundantCIAdversary (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n false)
    return encPair encBits encBits (unframe ct, false :: dropFrame ct)

/-- `etmRedundantCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (etmRedundantCIAdversary ctBound) := by
  ppt [etmRedundantCIAdversary]

private abbrev etmRedundantMaul (ct : List Bool) : List Bool :=
  encPair encBits encBits (unframe ct, false :: dropFrame ct)

private theorem decrypt_encryptThenMAC_redundantTag_of_mem_support (E : SymmetricCipher)
    (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    {n : ℕ} {k msg ct : List Bool}
    (hk : k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈
      (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n k msg)).support) :
    etmRedundantMaul ct ≠ ct ∧
      (encryptThenMAC E M.redundantTag hctLen).decrypt n k (etmRedundantMaul ct) = some msg := by
  simp only [encryptThenMAC, MACScheme.redundantTag, etmRedundantMaul, pmf_norm,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk hct ⊢
  obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
  obtain ⟨c, hc, tag, htag, rfl⟩ := hct
  rw [unframe_encPair_encBits] at hc; rw [dropFrame_encPair_encBits] at htag
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  refine ⟨fun h => List.ne_cons_self.symm (Prod.mk.inj ((encPair encBits encBits).injective h)).2,
    ?_⟩
  have hcLen : c.length = M.msgLen n := hctLen n ke hke msg hmsg c hc
  have hver : M.verify km c tag = true := M.verify_sign n km hkm c hcLen tag htag
  have hdec : E.decrypt n ke c = some msg := E.decrypt_encrypt n ke hke msg hmsg c hc
  simp [hcLen, hver, hdec]

/-- In `ciOneTimeGame` against `encryptThenMAC E M.redundantTag hctLen`,
`etmRedundantCIAdversary ctBound` wins with probability `1` at every security parameter `n` where
`ctBound n` bounds ciphertext lengths. -/
theorem eval_ciOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : (encryptThenMAC E M.redundantTag hctLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ciOneTimeGame
        (etmRedundantCIAdversary ctBound) n) = PMF.pure true :=
  (encryptThenMAC E M.redundantTag hctLen).eval_ciOneTimeGame_maulCIAdversary
    (maul := etmRedundantMaul) false ctBound n hctBound fun _ hk _ hct =>
      (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
        List.length_replicate hct).imp_right fun h => by rw [h]; rfl

/-- In `ciGame` against `encryptThenMAC E M.redundantTag hctLen`,
`etmRedundantCIAdversary ctBound` wins with probability `1` at every security parameter `n` where
`ctBound n` bounds ciphertext lengths. -/
theorem eval_ciGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : (encryptThenMAC E M.redundantTag hctLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ciGame
        (etmRedundantCIAdversary ctBound) n) = PMF.pure true :=
  (encryptThenMAC E M.redundantTag hctLen).eval_ciGame_maulCIAdversary
    (maul := etmRedundantMaul) false ctBound n hctBound fun _ hk _ hct =>
      (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
        List.length_replicate hct).imp_right fun h => by rw [h]; rfl

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeCiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeCiphertextIntegrity :=
  (encryptThenMAC E M.redundantTag hctLen).not_oneTimeCiphertextIntegrity_of_maul
    (maul := etmRedundantMaul) (by fun_prop) false fun _ _ hk _ hct =>
      (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
        List.length_replicate hct).imp_right fun h => by rw [h]; rfl

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `CiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_ciphertextIntegrity_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).CiphertextIntegrity :=
  fun h =>
    not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen
      h.oneTimeCiphertextIntegrity

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeAuthenticatedEncryption`. -/
theorem not_oneTimeAuthenticatedEncryption_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeAuthenticatedEncryption :=
  fun h => not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen h.2

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `AuthenticatedEncryption`. -/
theorem not_authenticatedEncryption_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).AuthenticatedEncryption :=
  fun h => not_ciphertextIntegrity_encryptThenMAC_redundantTag E M hctLen h.2

/-- Two-query CCA adversary against `encryptThenMAC E M.redundantTag hctLen`
([KatzLindell2020], Exercise 5.4, printed p. 164): queries left-or-right encryption on
`(0^n, 1^n)` to obtain `ct`, queries decryption on
`encPair encBits encBits (unframe ct, false :: dropFrame ct)`, and outputs whether the decrypted
message equals `some 1^n`. -/
def etmRedundantCCAAdversary (ctBound : ℕ → ℕ) : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$>
      ProbOracleComp.query (true, encPair encBits encBits (unframe ct, false :: dropFrame ct))
    return (reply == encOption encBits (some m1))

/-- `etmRedundantCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (etmRedundantCCAAdversary ctBound) := by
  ppt [etmRedundantCCAAdversary]

/-- In `ccaOneTimeGame` against `encryptThenMAC E M.redundantTag hctLen` at challenge bit `bit`,
`etmRedundantCCAAdversary ctBound` outputs `true` iff `some (List.replicate n bit)` encodes to
`encOption encBits (some (List.replicate n true))`. -/
theorem eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : (encryptThenMAC E M.redundantTag hctLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ccaOneTimeGame
        (etmRedundantCCAAdversary ctBound) bit n) =
      PMF.pure
        (List.take (n + 1) (encOption encBits (some (List.replicate n bit))) ==
          encOption encBits (some (List.replicate n true))) := by
  refine Eq.trans ((encryptThenMAC E M.redundantTag hctLen).eval_ccaOneTimeGame_maulCCAAdversary
    (maul := etmRedundantMaul) bit ctBound n hctBound fun _ hk _ hct =>
      (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
        List.length_replicate hct).1) ?_
  refine PMF.bind_eq_pure_of_forall_mem_support fun ⟨k, ct⟩ hp => ?_
  simp only [SymmetricCipher.encDist, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
    Prod.mk.injEq] at hp
  obtain ⟨k, hk, ct, hct, rfl, rfl⟩ := hp
  have hdec := (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
    List.length_replicate hct).2
  exact congrArg PMF.pure (congrArg
    (fun opt => List.take (n + 1) (encOption encBits opt) ==
      encOption encBits (some (List.replicate n true))) hdec)

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeINDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeINDCCA_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA :=
  (encryptThenMAC E M.redundantTag hctLen).not_oneTimeINDCCA_of_maul
    (maul := etmRedundantMaul) (by fun_prop)
    (fun _ _ _ => false)
    (fun _ _ _ _ => by simp [Game.succProbability])
    fun _ _ _ _ hk _ hct => by
      obtain ⟨hne, hdec⟩ :=
        decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct
      exact ⟨hne, Or.inl hdec⟩

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `INDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_indcca_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).INDCCA :=
  fun hcca =>
    not_oneTimeINDCCA_encryptThenMAC_redundantTag E M hctLen hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.4 counterexample** ([KatzLindell2020], Exercise 5.4, printed p. 164):
for any `INDCPA` symmetric cipher `E` and any `EUFCMA` message authentication code `M`,
`M.redundantTag` is `EUFCMA`-secure yet not `SUFCMA`-secure, and
`encryptThenMAC E M.redundantTag hctLen` satisfies `INDCPA` and `EncForge` while failing
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem encryptThenMAC_redundantTag_counterexample
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (hcpa : E.INDCPA) (heuf : M.EUFCMA) :
    M.redundantTag.EUFCMA ∧ ¬ M.redundantTag.OneTimeSUFCMA ∧ ¬ M.redundantTag.SUFCMA ∧
      (encryptThenMAC E M.redundantTag hctLen).INDCPA ∧
      (encryptThenMAC E M.redundantTag hctLen).EncForge ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeCiphertextIntegrity ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).CiphertextIntegrity ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).INDCCA :=
  ⟨heuf.redundantTag, M.not_oneTimeSUFCMA_redundantTag, M.not_sufCma_redundantTag,
    indcpa_encryptThenMAC E M.redundantTag hctLen hcpa,
    encForge_encryptThenMAC_redundantTag E M hctLen heuf,
    not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen,
    not_ciphertextIntegrity_encryptThenMAC_redundantTag E M hctLen,
    not_oneTimeINDCCA_encryptThenMAC_redundantTag E M hctLen,
    not_indcca_encryptThenMAC_redundantTag E M hctLen⟩

/-! ### Concrete Non-Vacuous PRF-Based Instantiations -/

/-- **End-to-end PRF-based instantiation of Exercise 5.10**: for any secure
`PseudorandomFunction family`,
`(prfEncryptThenMAC family hprf.polyTime hprf.length_eq).tailFallback` satisfies `INDCPA` and
`EncForge` while failing `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and
`INDCCA`. -/
theorem PseudorandomFunction.tailFallback_prfEncryptThenMAC_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let E := (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).tailFallback
    E.INDCPA ∧ E.EncForge ∧ ¬ E.OneTimeCiphertextIntegrity ∧ ¬ E.CiphertextIntegrity ∧
      ¬ E.OneTimeINDCCA ∧ ¬ E.INDCCA :=
  SymmetricCipher.tailFallback_counterexample
    hprf.authenticatedEncryption_prfEncryptThenMAC.1
    hprf.authenticatedEncryption_prfEncryptThenMAC.2.encForge

/-- **Concrete PRF-based Encrypt-then-MAC cipher with a non-strong redundant-tag MAC**
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
noncomputable def prfEncryptThenMACRedundantTag (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    SymmetricCipher :=
  encryptThenMAC
    (prfCipher family hpoly hlen)
    (((prfMAC family hpoly).reindex (fun n => 2 * n) (by fun_prop)).redundantTag)
    (prfCipher_ciphertext_length family hpoly hlen)

/-- **End-to-end PRF-based instantiation of Exercise 5.4**: for any secure
`PseudorandomFunction family`, `prfEncryptThenMACRedundantTag` satisfies `INDCPA` and `EncForge`
while failing `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem PseudorandomFunction.prfEncryptThenMACRedundantTag_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let M := (prfMAC family hprf.polyTime).reindex (fun n => 2 * n) (by fun_prop)
    let ETM := prfEncryptThenMACRedundantTag family hprf.polyTime hprf.length_eq
    M.redundantTag.EUFCMA ∧ ¬ M.redundantTag.OneTimeSUFCMA ∧ ¬ M.redundantTag.SUFCMA ∧
      ETM.INDCPA ∧ ETM.EncForge ∧ ¬ ETM.OneTimeCiphertextIntegrity ∧
      ¬ ETM.CiphertextIntegrity ∧ ¬ ETM.OneTimeINDCCA ∧ ¬ ETM.INDCCA :=
  encryptThenMAC_redundantTag_counterexample
    (prfCipher family hprf.polyTime hprf.length_eq)
    ((prfMAC family hprf.polyTime).reindex (fun n => 2 * n) (by fun_prop))
    (prfCipher_ciphertext_length family hprf.polyTime hprf.length_eq)
    hprf.indcpa_prfCipher
    (hprf.eufCma_prfMAC.reindex (by fun_prop) (strictMono_mul_left_of_pos two_pos))

end Cslib.Crypto
