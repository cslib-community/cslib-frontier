/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated.Malleability
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

/-! ### Katz–Lindell Exercise 5.10: `INDCPA ∧ EncForge` Does Not Imply `INDCCA`

Given any symmetric cipher `E`, `E.tailFallback` has the same `keyGen` and `encrypt` as `E`, and
decrypts `ct` by returning `E.decrypt n k ct` when it is `some msg`, or falling back to
`E.decrypt n k ct.tail` when `ct` is non-empty and `E.decrypt n k ct = none`. This preserves
`INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
`OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (and breaking `OneTimeINDCCA` and `INDCCA`
whenever `E.EncForge` holds, by querying decryption on `false :: ct`). -/

namespace SymmetricCipher

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
  refine Game.succProbability_bind_pure_le_add runDist fun p _ hwin => ?_
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
  maulCIAdversary (fun _ ct => false :: ct) bit ctBound

/-- `prependFalseBitCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_prependFalseBitCIAdversary (bit : Bool) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (prependFalseBitCIAdversary bit ctBound) :=
  isOraclePPT_maulCIAdversary (by fun_prop) bit hctBound

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
  E.tailFallback.not_oneTimeCiphertextIntegrity_of_maul (maul := fun _ ct => false :: ct)
    (by fun_prop) false 0 fun n _ k hk ct hct =>
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
  maulCCAAdversary (fun _ ct => false :: ct) true ctBound

/-- `tailFallbackCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_tailFallbackCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (tailFallbackCCAAdversary ctBound) :=
  isOraclePPT_maulCCAAdversary (by fun_prop) true hctBound

private theorem eval_encForgeGame_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary bit ctBound) n) = do
      let k ← ProbComp.eval (E.keyGen n)
      let ct ← ProbComp.eval (E.encrypt n k (List.replicate n bit))
      return (E.decrypt n k (false :: ct)).isSome &&
        !([List.replicate n bit].contains ((E.decrypt n k (false :: ct)).getD [])) := by
  simp only [encForgeGame, prependFalseBitCIAdversary, maulCIAdversary, encForgeOracle,
    List.length_replicate, beq_self_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  peel_binds k ct
  rw [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem)]

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `OneTimeINDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem not_oneTimeINDCCA_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.OneTimeINDCCA := by
  refine E.tailFallback.not_oneTimeINDCCA_of_maul_or_bad (maul := fun _ ct => false :: ct)
    (by fun_prop) true
    (fun n bit k ct => (E.decrypt n k (false :: ct)).isSome &&
      !([List.replicate n bit].contains ((E.decrypt n k (false :: ct)).getD [])))
    (fun bit => ?_) 0 fun n _ bit k hk ct hct => ⟨List.ne_cons_self.symm, ?_⟩
  · obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
    have h := hforge.negligible (prependFalseBitCIAdversary bit ctBound)
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
  refine Game.succProbability_bind_pure_le_add _ fun p _ hwin => ?_
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
  SymmetricCipher.maulCIAdversary
    (fun _ ct => encPair encBits encBits (unframe ct, false :: dropFrame ct)) false ctBound

/-- `etmRedundantCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (etmRedundantCIAdversary ctBound) :=
  SymmetricCipher.isOraclePPT_maulCIAdversary (by fun_prop) false hctBound

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
    (maul := fun _ => etmRedundantMaul) false ctBound n hctBound fun _ hk _ hct =>
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
    (maul := fun _ => etmRedundantMaul) false ctBound n hctBound fun _ hk _ hct =>
      (decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk
        List.length_replicate hct).imp_right fun h => by rw [h]; rfl

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeCiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeCiphertextIntegrity :=
  (encryptThenMAC E M.redundantTag hctLen).not_oneTimeCiphertextIntegrity_of_maul
    (maul := fun _ => etmRedundantMaul) (by fun_prop) false 0 fun _ _ _ hk _ hct =>
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
  SymmetricCipher.maulCCAAdversary
    (fun _ ct => encPair encBits encBits (unframe ct, false :: dropFrame ct)) true ctBound

/-- `etmRedundantCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (etmRedundantCCAAdversary ctBound) :=
  SymmetricCipher.isOraclePPT_maulCCAAdversary (by fun_prop) true hctBound

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
          encOption encBits (some (List.replicate n true))) :=
  (encryptThenMAC E M.redundantTag hctLen).eval_ccaOneTimeGame_maulCCAAdversary
    (maul := fun _ => etmRedundantMaul) true bit ctBound n hctBound _ fun _ hk _ hct =>
      decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeINDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeINDCCA_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n)) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA :=
  (encryptThenMAC E M.redundantTag hctLen).not_oneTimeINDCCA_of_maul
    (maul := fun _ => etmRedundantMaul) (by fun_prop) true 0 fun _ _ _ _ hk _ hct =>
      decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct

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
