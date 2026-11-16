/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.CramerShoup
import CslibFrontier.Crypto.Computational.Encryption.CCA.NonAdaptive
import CslibFrontierTests.Crypto.AssumptionNonvacuity

/-! Clients of non-adaptive 1CCA security (`Encryption.INDCCA1On`): the two implications compose
to the existing `INDCCA2On.indcpaOn`; the zero decryption budget of the guessing stage excludes
an adversary that decrypts after the challenge; sending the plaintext is not non-adaptive 1CCA
secure; and keyed-hash Cramer–Shoup is, under the hypotheses of `DDH.indcca2On_cramerShoup`. -/

namespace CslibFrontierTests.Crypto.NonAdaptiveCCA

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM
open CslibFrontierTests.Crypto.AssumptionNonvacuity
open scoped NNReal

/-! The two implications compose to the existing `INDCCA2On.indcpaOn`. -/
example {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCPAOn valid encMsg keyGen encrypt :=
  h.indcca1On.indcpaOn

/-! The restriction excludes something: a guessing stage that asks for one decryption does not
have decryption budget `0`. -/
example (ct : List Bool) :
    ¬ ((do
      let reply ← ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), ct)
      return reply.isEmpty) : WordOracleComp Unit Bool).IsQueryBounded 0 := by
  intro h
  have := (OracleComp.IsCostBounded.liftBind_iff.mp h).1
  simp at this

/-- **Sending the plaintext bit is not non-adaptive 1CCA secure**, for any decryption, since
non-adaptive 1CCA security implies IND-CPA. -/
theorem not_indcca1On_plaintext (decrypt : ℕ → List Bool → List Bool → Option Bool) :
    ¬ INDCCA1On (fun _ _ _ _ => true) encBool encBool emptyKeys plaintext decrypt :=
  fun h => not_indcpa_plaintext h.indcpaOn

/-! A caller instance: keyed-hash Cramer–Shoup is non-adaptive 1CCA secure under the hypotheses
of `DDH.indcca2On_cramerShoup`. -/
example {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA1On (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (PrimeOrderGroupFamily.DDH.indcca2On_cramerShoup hH hisElem hd hkeyLen hmem hDDH hCR hm0 hm
    hinv).indcca1On

end CslibFrontierTests.Crypto.NonAdaptiveCCA
