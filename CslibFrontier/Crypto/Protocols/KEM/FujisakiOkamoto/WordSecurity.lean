/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordBridge
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# ROM IND-CCA security of the word-level Fujisaki–Okamoto families from IND-CPA

This module proves that the word-level KEMs of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordGame` are IND-CCA secure in the random
oracle model when the underlying word-level PKE family is IND-CPA secure:

* `WordPKE.INDCPA.romINDCCA` for the implicit-rejection transform `FO-notbot = U-notbot ∘ T` of
  [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021),
  which composes Theorem 3.2 (§3.1, IND-CPA to OW-PCVA, used in its OW-PCA form from the remark
  on p. 13) and Theorem 3.4 (§3.2.2). As in the source, the PKE need not be `γ`-spread (§1.1.2
  table and the text below it, p. 6; remark after the proof of Theorem 3.2, p. 13; `KEM-notbot`
  row of the §3.3 table, p. 22).
* `WordPKE.INDCPA.romINDCCABot` for the explicit-rejection transform `FO^⊥ = U^⊥ ∘ T` (§3.3,
  p. 21, and Fig. 18, p. 22), which composes Theorem 3.2 (p. 12) and Theorem 3.3 (§3.2.1, p. 14).
  As in the source, the PKE must be `γ`-spread (§1.1.2 table, p. 6; Theorem 3.2).

**Assumptions.** `P.INDCPA` is the hardness assumption: IND-CPA security of the PKE family
against uniform strict PPT adversaries, with challenge messages in its message space. The other
premises are properties of the PKE family and the key length: efficiency (`WordPKE.IsEfficient`
and a polynomial-time `keyLen`), ciphertexts in the ciphertext space (`WordPKE.CiphertextFits`),
`δ`-correctness at every parameter with `δ` negligible, a message space of size `2 ^ msgLen n`
whose inverse is negligible, and for `FO^⊥` `γ`-spreadness at every parameter with `2 ^ (-γ n)`
negligible. These are the asymptotic form of the requirements `δ ≤ 2^{-κ}`, `γ ≥ κ` and
`|M| ≥ 2^κ` of the source's "Concrete parameters" (p. 22). Nothing is assumed about the
reductions.

**Proof.** For an adversary `A` with `IsOraclePPT encBool A`, the typed bridge
`WordPKE.IsEfficient.exists_typedAdversary` gives at each parameter a typed adversary with a
polynomial bound `q` on its `G`, `H` and decapsulation queries, whose typed games are the word
games and whose typed reductions have the IND-CPA advantages of `romCpaReductionWord A` and
`romBotCpaReductionWord A`. The concrete bounds `Scheme.indCcaRomAdvantage_le` and
`Scheme.indCcaBotAdvantage_le` then bound the IND-CCA advantage at `n` by a sum of twice the
IND-CPA advantage of the reduction and terms polynomial in `q n` times `2 ^ (-msgLen n)`, `δ n`
and, for `FO^⊥`, `2 ^ (-γ n)`. The reductions are uniform strict PPT
(`WordPKE.IsEfficient.isPPT_romCpaReductionWord`,
`WordPKE.IsEfficient.isPPT_romBotCpaReductionWord`), so the IND-CPA assumption makes their
advantages negligible, and so is the sum.

**Query counts.** The source counts every evaluation of `G` and `H` in the experiment, the
experiment's own included (§2.1, p. 9). The theorems here state no query counts: a uniform strict
oracle PPT adversary makes polynomially many queries, and the concrete steps count its explicit
queries. Their bounds differ from the source's in every term, and each term is negligible under
the premises.

**Scope.** The games are the word games `romIndCcaGameWord` and `romIndCcaBotGameWord`, whose
deviations from the source are documented in `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto`
`.WordGame` and `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA.romINDCCA`: IND-CPA security of an
  efficient, `δ`-correct word-level PKE family implies ROM IND-CCA security of its `FO-notbot`
  KEM.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA.romINDCCABot`: IND-CPA security of an
  efficient, `δ`-correct and `γ`-spread word-level PKE family implies ROM IND-CCA security of its
  `FO^⊥` KEM.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), Theorems 3.2, 3.3 and 3.4; the requirements table of §1.1.2 (p. 6), the
  remark after the proof of Theorem 3.2 (p. 13), and §3.3 with Fig. 18, the bounds table and
  "Concrete parameters" (pp. 21–22).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace WordPKE

/-- **ROM IND-CCA security of the word-level `FO-notbot` family from IND-CPA**
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), Theorems 3.2 and 3.4, composed).
Let `P` be an efficient word-level PKE family whose ciphertexts lie in its ciphertext space, which
is `δ`-correct with `δ` negligible and has messages of length `msgLen n` with `2 ^ (-msgLen n)`
negligible, and let `keyLen` be polynomial-time. If `P` is IND-CPA secure, its `FO-notbot` KEM
with keys of length `keyLen n` is IND-CCA secure in the random oracle model against uniform strict
oracle PPT adversaries, with any number of decapsulation queries. The proof applies the IND-CPA
assumption to the explicit reduction `romCpaReductionWord A`, certified by
`IsEfficient.isPPT_romCpaReductionWord`. As in the source, the PKE need not be `γ`-spread (§1.1.2
table, p. 6; remark after the proof of Theorem 3.2, p. 13; `KEM-notbot` row of the §3.3 table,
p. 22). -/
theorem INDCPA.romINDCCA {P : WordPKE} {keyLen : ℕ → ℕ} (hcpa : P.INDCPA)
    (hP : P.IsEfficient) (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hfit : P.CiphertextFits) {δ : ℕ → ℝ≥0} (hδ : P.DeltaCorrect δ) (hδneg : Negligible δ)
    (hmsg : Negligible fun n => ((2 : ℝ≥0) ^ P.msgLen n)⁻¹) :
    P.ROMINDCCA keyLen := by
  intro A hA
  obtain ⟨B, q, hq, hqueries, hbridge⟩ := hP.exists_typedAdversary hkeyLen hA
  let cpa : ℕ → ℝ≥0 := Encryption.advantage
    (Encryption.gameOn P.IsMessagePair P.keyGen P.encrypt (P.romCpaReductionWord keyLen A))
  have hcpa' : Negligible cpa :=
    hcpa (P.romCpaReductionWord keyLen A) (hP.isPPT_romCpaReductionWord hkeyLen hA)
  have hbound (n : ℕ) : Game.advantage (ProbComp.eval (P.romIndCcaGameWord keyLen A false n))
      (ProbComp.eval (P.romIndCcaGameWord keyLen A true n)) ≤
      2 * cpa n + ((6 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ +
        ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n := by
    obtain ⟨hgame, hadv, -, -⟩ := hbridge hfit n
    have hle := (P.finiteScheme keyLen n).indCcaRomAdvantage_le (B n) (fun ω => (hqueries n ω).1)
      (by simp [ProbComp.eval_uniform]) (hδ n)
    have hword : Game.advantage (ProbComp.eval (P.romIndCcaGameWord keyLen A false n))
        (ProbComp.eval (P.romIndCcaGameWord keyLen A true n)) =
        (P.finiteScheme keyLen n).indCcaRomAdvantage (B n) := by
      simp only [Scheme.indCcaRomAdvantage, Experiment.advantage, hgame]
    rw [← NNReal.coe_le_coe, hword]
    refine hle.trans (le_of_eq ?_)
    simp only [finiteScheme_pke] at hadv ⊢
    rw [← hadv]
    simp only [cpa, coe_nndist, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
      NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one]
    ring
  refine negligible_of_le ?_ hbound
  have h₁ : Negligible fun n => 2 * cpa n := hcpa'.const_mul 2
  have h₂ : Negligible fun n => ((6 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ :=
    hmsg.polynomiallyBounded_mul (by fun_prop)
  have h₃ : Negligible fun n => ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n :=
    hδneg.polynomiallyBounded_mul (by fun_prop)
  exact (h₁.add_fun h₂).add_fun h₃

/-- **ROM IND-CCA security of the word-level `FO^⊥` family from IND-CPA**
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), Theorems 3.2 and 3.3, composed as
in §3.3, pp. 21–22). Let `P` be an efficient word-level PKE family whose ciphertexts lie in its
ciphertext space, which is `δ`-correct with `δ` negligible and `γ`-spread with `2 ^ (-γ n)`
negligible, and has messages of length `msgLen n` with `2 ^ (-msgLen n)` negligible, and let
`keyLen` be polynomial-time. If `P` is IND-CPA secure, its explicit-rejection `FO^⊥` KEM with keys
of length `keyLen n` is IND-CCA secure in the random oracle model against uniform strict oracle PPT
adversaries, with any number of decapsulation queries. The proof applies the IND-CPA assumption
to the explicit reduction `romBotCpaReductionWord A`, certified by
`IsEfficient.isPPT_romBotCpaReductionWord`.

The premises on `δ`, `γ` and the message length are the asymptotic form of the source's
"Concrete parameters" (p. 22). The source states a concrete bound, with `G` and `H` queries
counted over the whole experiment (§2.1, p. 9). This theorem states none; its concrete step,
`Scheme.indCcaBotAdvantage_le`, counts the adversary's explicit queries and has a bound that
differs from the source's in every term. The game `romIndCcaBotGameWord` reads `H(m, c)` as the
canonical word encoding `H(false, m, c)`, answers requests outside the oracles' word domains with
the empty word, rejects words longer than `ctLen n` with `⊥` and measures the two-world advantage,
twice the source's `|Pr[b' = b] - 1/2|`. -/
theorem INDCPA.romINDCCABot {P : WordPKE} {keyLen : ℕ → ℕ} (hcpa : P.INDCPA)
    (hP : P.IsEfficient) (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hfit : P.CiphertextFits) {δ : ℕ → ℝ≥0} (hδ : P.DeltaCorrect δ) (hδneg : Negligible δ)
    {γ : ℕ → ℝ} (hγ : P.GammaSpread γ) (hγneg : Negligible fun n => (2 : ℝ≥0) ^ (-γ n))
    (hmsg : Negligible fun n => ((2 : ℝ≥0) ^ P.msgLen n)⁻¹) :
    P.ROMINDCCABot keyLen := by
  intro A hA
  obtain ⟨B, q, hq, hqueries, hbridge⟩ := hP.exists_typedAdversary hkeyLen hA
  let cpa : ℕ → ℝ≥0 := Encryption.advantage
    (Encryption.gameOn P.IsMessagePair P.keyGen P.encrypt (P.romBotCpaReductionWord keyLen A))
  have hcpa' : Negligible cpa :=
    hcpa (P.romBotCpaReductionWord keyLen A) (hP.isPPT_romBotCpaReductionWord hkeyLen hA)
  have hbound (n : ℕ) : Game.advantage (ProbComp.eval (P.romIndCcaBotGameWord keyLen A false n))
      (ProbComp.eval (P.romIndCcaBotGameWord keyLen A true n)) ≤
      2 * cpa n + ((4 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ +
        ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n + ((6 * q n : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ (-γ n) := by
    obtain ⟨-, -, hgame, hadv⟩ := hbridge hfit n
    have hle := (P.finiteScheme keyLen n).indCcaBotAdvantage_le (B n) (hqueries n)
      (by simp [ProbComp.eval_uniform]) (hδ n) (hγ n)
    have hword : Game.advantage (ProbComp.eval (P.romIndCcaBotGameWord keyLen A false n))
        (ProbComp.eval (P.romIndCcaBotGameWord keyLen A true n)) =
        (P.finiteScheme keyLen n).indCcaBotAdvantage (B n) := by
      simp only [Scheme.indCcaBotAdvantage, Experiment.advantage, hgame]
    rw [← NNReal.coe_le_coe, hword]
    refine hle.trans (le_of_eq ?_)
    simp only [finiteScheme_pke] at hadv ⊢
    rw [← hadv]
    simp only [cpa, coe_nndist, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
      NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one, NNReal.coe_rpow]
    ring
  refine negligible_of_le ?_ hbound
  have h₁ : Negligible fun n => 2 * cpa n := hcpa'.const_mul 2
  have h₂ : Negligible fun n => ((4 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ :=
    hmsg.polynomiallyBounded_mul (by fun_prop)
  have h₃ : Negligible fun n => ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n :=
    hδneg.polynomiallyBounded_mul (by fun_prop)
  have h₄ : Negligible fun n => ((6 * q n : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ (-γ n) :=
    hγneg.polynomiallyBounded_mul (by fun_prop)
  exact ((h₁.add_fun h₂).add_fun h₃).add_fun h₄

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
