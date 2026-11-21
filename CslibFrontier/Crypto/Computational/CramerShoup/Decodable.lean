/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.Interleaved
public import CslibFrontier.Crypto.Computational.DiscreteLog.Decodable

/-!
# Multiplicative Cramer–Shoup over decodable prime-order group families

The core Cramer–Shoup modules (`CramerShoup.Scheme`, `CramerShoup.Reductions`, `CramerShoup`, and
`CramerShoup.Interleaved`) accept an explicit group-membership test `isElem : F.Desc × List Bool →
Bool`, a polynomial-time certificate `hisElem`, and the range characterization `hmem` so that they
remain valid over any `PrimeOrderGroupFamily`, and the native games draw a uniform hash key
`keyLen n` passed via `F.withKey`.

When the underlying family is a `DecodablePrimeOrderGroupFamily`, `F.isElem`,
`F.computableInPolyTime_isElem`, and `F.isElem_eq_true_iff` supply all three group-membership
arguments automatically. This module exposes those specialized operations and IND-CCA2 security
theorems without `isElem`, `hisElem`, or `hmem` parameters.

## Main definitions

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupValid`: challenge-pair group-membership
  admissibility using `F.isElem`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.decodeCramerShoup`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupADDecryptOpt`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupDecryptOpt`: Cramer–Shoup decryption
  using `F.isElem`.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2ADOn_cramerShoup_bitStringAD`: native
  `Encryption.INDCCA2ADOn` security with associated data in $\{0,1\}^*$ without external
  `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2On_cramerShoup`: native
  `Encryption.INDCCA2On` security without external `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup`: batch-challenge
  multi-challenge `Encryption.INDCCA2MultiOn` security without external `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup`: interleaved
  multi-challenge `Encryption.INDCCA2InterleavedOn` security without external `isElem` premises.

## Scope

* **Fixed group family, standard model**: as in `CramerShoup` and `CramerShoup.Interleaved`, the
  theorems fix a polynomial-time computable group family `d : ℕ → F.Desc`; the group at parameter
  `n` is `d n` and is not sampled. DDH is assumed for the point-mass setup
  `fun n => PMF.pure (d n)`. The hash key is a uniform `keyLen n`-bit word drawn at key generation
  and published in the public key ([CramerShoup2003], Section 6.1, Figure 1), and collision
  resistance is assumed for `F.withKey.cramerShoupHashMod H` under
  `F.withKeySetup (fun n => PMF.pure (d n)) keyLen` on its well-formed inputs.
* **Hash assumption**: following [BonehShoup2023], Exercise 12.27, which declares
  $H' : \mathbb{G}^3 \times \mathcal{D} \to \mathbb{Z}_q$, the theorems assume collision
  resistance of the keyed hash on the words that `isCramerShoupHashInput` accepts with
  `isElemWithKey F.isElem`, the encodings of $\mathbb{G}^3 \times \mathcal{D}$. With associated
  data, $\mathcal{D} = \{0,1\}^*$, because decryption hashes any associated-data word; a general
  $\mathcal{D}$ is open (#5293).
  [CramerShoup2003], Theorem 1 (Section 6.2), needs only target collision resistance, which is
  weaker, so these theorems use a stronger hash assumption than the original paper.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1 and Theorem 12.1, printed
  pp. 467–469), Section 12.5 (Theorem 12.9, printed pp. 489–490) and Exercise 12.27 (printed
  pp. 521–522).
* [R. Cramer, V. Shoup, *Design and Analysis of Practical Public-Key Encryption Schemes Secure
  against Adaptive Chosen Ciphertext Attack*][CramerShoup2003], Sections 6.1–6.2.
-/

public section

namespace Cslib.Crypto.DecodablePrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption PrimeOrderGroupFamily
open scoped NNReal

variable (F : DecodablePrimeOrderGroupFamily)

/-- Challenge-pair group-membership admissibility predicate for native Cramer–Shoup CCA games over
a decodable family. -/
abbrev cramerShoupValid (d : ℕ → F.Desc) : ℕ → List Bool → List Bool → List Bool → Bool :=
  F.toPrimeOrderGroupFamily.cramerShoupValid F.isElem d

/-- Word-level Cramer–Shoup decryption with associated data using `F.isElem`. -/
abbrev decodeCramerShoup (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.decodeCramerShoup H F.isElem d sk ct ad

/-- Deterministic polynomial-time Cramer–Shoup decryption with associated data and a keyed hash,
using `F.isElem`. -/
abbrev cramerShoupADDecryptOpt (H : F.withKey.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (skBits ct ad : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.cramerShoupADDecryptOpt H F.isElem d n skBits ct ad

/-- Deterministic polynomial-time Cramer–Shoup decryption with a keyed hash, using `F.isElem`. -/
abbrev cramerShoupDecryptOpt (H : F.withKey.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (skBits ct : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.cramerShoupDecryptOpt H F.isElem d n skBits ct

/-- **Multiplicative Cramer–Shoup with associated data in $\mathcal{D} = \{0,1\}^*$ is 1CCA
secure** ([BonehShoup2023], Exercise 12.27, printed pp. 521–522, by the method of Theorem 12.9,
printed pp. 489–493) under DDH and collision resistance of $H'$ on
$\mathbb{G}^3 \times \{0,1\}^*$. The associated-data space is all words because decryption
hashes whatever associated-data word it is given. A general space $\mathcal{D}$ is open (#5293);
it needs decryption to reject associated data outside $\mathcal{D}$. This is
`PrimeOrderGroupFamily.DDH.indcca2ADOn_cramerShoup_bitStringAD` over a
`DecodablePrimeOrderGroupFamily`, whose `F.isElem` supplies the group-membership test (no external
`isElem`, `hisElem`, or `hmem` parameters). -/
theorem DDH.indcca2ADOn_cramerShoup_bitStringAD
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput true (F.isElemWithKey F.isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2ADOn (F.cramerShoupValid d) encBits encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupADEncryptProb encBits H d)
      (F.cramerShoupADDecryptOpt H d) :=
  hDDH.indcca2ADOn_cramerShoup_bitStringAD hH F.computableInPolyTime_isElem hd hkeyLen
    F.isElem_eq_true_iff hCR hm0 hm hinv

/-- **Multiplicative Cramer–Shoup is 1CCA secure** ([BonehShoup2023], Exercise 12.27, printed
pp. 521–522, without associated data, proved by the method of Theorem 12.9, printed pp. 489–493)
under DDH and collision resistance of $H'$ on its well-formed inputs
$\mathbb{G}^3 \times \mathcal{D}$, here with $\mathcal{D} = \{[]\}$:
`PrimeOrderGroupFamily.DDH.indcca2On_cramerShoup` over a `DecodablePrimeOrderGroupFamily`, whose
`F.isElem` supplies the group-membership test (no external `isElem`, `hisElem`, or `hmem`
parameters). -/
theorem DDH.indcca2On_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey F.isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2On (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  hDDH.indcca2On_cramerShoup hH F.computableInPolyTime_isElem hd hkeyLen F.isElem_eq_true_iff hCR
    hm0 hm hinv

/-- **Multiplicative Cramer–Shoup is CCA secure in the batch-challenge game** ([BonehShoup2023],
Exercise 12.27, printed pp. 521–522, proved by the method of Theorem 12.9, printed pp. 489–493,
and the batch-challenge specialization of Theorem 12.1, printed p. 468) under DDH and collision
resistance of $H'$ on its well-formed inputs $\mathbb{G}^3 \times \mathcal{D}$, here with
$\mathcal{D} = \{[]\}$: `PrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup` over a
`DecodablePrimeOrderGroupFamily`. -/
theorem DDH.indcca2MultiOn_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey F.isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2MultiOn (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  hDDH.indcca2MultiOn_cramerShoup hH F.computableInPolyTime_isElem hd hkeyLen F.isElem_eq_true_iff
    hCR hm0 hm hinv

/-- **Multiplicative Cramer–Shoup is CCA secure** ([BonehShoup2023], Exercise 12.27, printed
pp. 521–522, in the fully adaptive multi-challenge Attack Game 12.1, printed p. 467, proved by the
method of Theorem 12.9, printed pp. 489–493, and Theorem 12.1, printed p. 468) under DDH and
collision resistance of $H'$ on its well-formed inputs $\mathbb{G}^3 \times \mathcal{D}$, here with
$\mathcal{D} = \{[]\}$: `PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup` over a
`DecodablePrimeOrderGroupFamily`. -/
theorem DDH.indcca2InterleavedOn_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey F.isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2InterleavedOn (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  hDDH.indcca2InterleavedOn_cramerShoup hH F.computableInPolyTime_isElem hd hkeyLen
    F.isElem_eq_true_iff hCR hm0 hm hinv

end Cslib.Crypto.DecodablePrimeOrderGroupFamily
