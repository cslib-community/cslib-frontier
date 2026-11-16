/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CramerShoup
import CslibFrontier.Crypto.Computational.Encryption.CCA.NonAdaptive

/-! Clients of non-adaptive 1CCA security (`Encryption.INDCCA1On`) under module encapsulation: a
caller hands an adversary with its certificate and zero Phase 2 budget to `INDCCA1On`; a first
stage that decrypts does not break the budget condition, a guessing stage that decrypts does;
the two implications compose to the existing `INDCCA2On.indcpaOn`; and keyed-hash Cramer–Shoup
is non-adaptive 1CCA secure under the hypotheses of `DDH.indcca2On_cramerShoup`. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM
open scoped NNReal

namespace CslibFrontierTests.Crypto.NonAdaptiveCCAModule

variable {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
  {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
  {keyGen : ℕ → ProbComp (List Bool × List Bool)}
  {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
  {decrypt : ℕ → List Bool → List Bool → Option Out}

-- A caller applies `INDCCA1On` to an adversary with its certificate and zero Phase 2 budget, as a
-- reduction to non-adaptive 1CCA security does.
example (h : INDCCA1On valid encMsg encOut keyGen encrypt decrypt)
    (adversary : CCA2AdversaryOf Msg) (hA : adversary.IsPPT encMsg)
    (hguess : ∀ n state ct, (adversary.guess n state ct).IsQueryBounded 0) :
    Negligible fun n => Game.advantage
      (ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
      (ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary true n)) :=
  h adversary ⟨hA, hguess⟩

-- The budget condition constrains only the guessing stage: a first stage that asks for a
-- decryption, followed by a guessing stage that never queries the oracle, meets it. (This shows the
-- budget half of the class condition only; the `IsPPT` half is not checked here.)
example (c : List Bool) (g : ℕ → List Bool → List Bool → ProbComp Bool) (n : ℕ)
    (state ct : List Bool) :
    (({ choose := fun _ _ => do
          let reply ← ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), c)
          return ((false, true), reply)
        guess := fun n state ct => ProbOracleComp.sample (g n state ct) } :
      CCA2AdversaryOf Bool).guess n state ct).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample _

-- Decryption after the challenge is excluded: a guessing stage that asks for one decryption does
-- not have budget `0`.
example (ct : List Bool) :
    ¬ ((do
      let reply ← ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), ct)
      return reply.isEmpty) : WordOracleComp Unit Bool).IsQueryBounded 0 := by
  intro h
  have := (OracleComp.IsCostBounded.liftBind_iff.mp h).1
  simp at this

-- The two implications compose to the existing `INDCCA2On.indcpaOn`.
example (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCPAOn valid encMsg keyGen encrypt :=
  h.indcca1On.indcpaOn

-- Keyed-hash Cramer–Shoup is non-adaptive 1CCA secure under the hypotheses of
-- `DDH.indcca2On_cramerShoup`.
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

end CslibFrontierTests.Crypto.NonAdaptiveCCAModule
