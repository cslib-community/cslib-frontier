/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved

/-!
# Interleaved and batch multi-challenge CCA security of Cramer–Shoup

Multiplicative Cramer–Shoup is secure in both the fully adaptive interleaved-query multi-challenge
CCA game ([Boneh and Shoup, Section 12.1, Attack Game 12.1][BonehShoup2023]) and its two-phase
batch-challenge specialization. The proof composes its single-challenge 1CCA security,
`DDH.indcca2On_cramerShoup` ([BonehShoup2023], Theorem 12.9), with the generic hybrid reduction
`Encryption.INDCCA2On.indcca2InterleavedOn` ([BonehShoup2023], Theorem 12.1) and the batch-to-
interleaved simulation `Encryption.INDCCA2InterleavedOn.indcca2MultiOn`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup`: Multiplicative
  Cramer–Shoup, with its hash key drawn at key generation, satisfies
  `Encryption.INDCCA2InterleavedOn` under DDH and collision resistance of the keyed hash on its
  well-formed inputs.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup`: Multiplicative Cramer–Shoup
  likewise satisfies batch-challenge `Encryption.INDCCA2MultiOn` under the same hypotheses.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1 and Theorem 12.1, printed
  pp. 467–469), Section 12.5 (Theorem 12.9, printed pp. 489–493) and Exercise 12.27 (printed
  pp. 521–522).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption
open scoped NNReal

/-- **Multiplicative Cramer–Shoup is CCA secure** ([BonehShoup2023], Exercise 12.27, printed
pp. 521–522, in the fully adaptive multi-challenge Attack Game 12.1, printed p. 467, proved by the
method of Theorem 12.9, printed pp. 489–493, and Theorem 12.1, printed p. 468) under DDH and
collision resistance of $H'$ on its well-formed inputs $\mathbb{G}^3 \times \mathcal{D}$, here with
$\mathcal{D} = \{[]\}$. Under the hypotheses of `DDH.indcca2On_cramerShoup`, the probabilistic
polynomial-time scheme
`(cramerShoupKeyGenProb d keyLen, cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)`
satisfies the fully adaptive interleaved-query multi-challenge `Encryption.INDCCA2InterleavedOn`
notion with respect to `cramerShoupValid isElem d`. Key generation draws a uniform
`keyLen n`-bit hash key and publishes it in the public key, and the hash assumption is collision
resistance of the keyed family `F.withKey.cramerShoupHashMod H` under
`withKeySetup (fun n => PMF.pure (d n)) keyLen` on the words that `isCramerShoupHashInput false`
accepts. -/
theorem DDH.indcca2InterleavedOn_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2InterleavedOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (hDDH.indcca2On_cramerShoup hH hisElem hd hkeyLen hmem hCR hm0 hm hinv).indcca2InterleavedOn
    (F.computableInPolyTime_cramerShoupValid hisElem hd)
    (F.isPPTOn_cramerShoupKeyGenProb hd hkeyLen)
    (F.isPPTOn_cramerShoupEncryptProb hH hd)
    (F.computableInPolyTime_cramerShoupDecryptOpt hH hisElem hd)

/-- **Multiplicative Cramer–Shoup is CCA secure in the batch-challenge game** ([BonehShoup2023],
Exercise 12.27, printed pp. 521–522, proved by the method of Theorem 12.9, printed pp. 489–493,
and the batch-challenge specialization of Theorem 12.1, printed p. 468) under DDH and collision
resistance of $H'$ on its well-formed inputs $\mathbb{G}^3 \times \mathcal{D}$, here with
$\mathcal{D} = \{[]\}$. Under the hypotheses of `DDH.indcca2On_cramerShoup`, the scheme
`(cramerShoupKeyGenProb d keyLen, cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)`
satisfies the two-phase batch-challenge multi-challenge `Encryption.INDCCA2MultiOn` notion with
respect to `cramerShoupValid isElem d`. The hash key is drawn at key generation and published in
the public key. -/
theorem DDH.indcca2MultiOn_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2MultiOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (hDDH.indcca2InterleavedOn_cramerShoup hH hisElem hd hkeyLen hmem hCR hm0 hm hinv).indcca2MultiOn
    (F.computableInPolyTime_cramerShoupValid hisElem hd)
    (F.isPPTOn_cramerShoupKeyGenProb hd hkeyLen)
    (F.isPPTOn_cramerShoupEncryptProb hH hd)
    (F.computableInPolyTime_cramerShoupDecryptOpt hH hisElem hd)

end Cslib.Crypto.PrimeOrderGroupFamily
