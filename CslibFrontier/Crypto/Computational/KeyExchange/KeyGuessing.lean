/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.KeyExchange
import CslibFrontier.Probability.PMF.Bind

/-!
# Key-guessing security for anonymous key exchange

[BonehShoup2023], Section 10.1 (Attack Game 10.1 and Definition 10.1, p. 400), defines key-guessing
security for an anonymous (unauthenticated) two-party key-exchange protocol: after an honest
execution outputs its public transcript and key, a PPT adversary given the transcript tries to
output the exact shared key. Section 10.4.2 (pp. 407–408) observes that Diffie–Hellman key
exchange satisfies this notion if and only if the Computational Diffie–Hellman assumption holds.

## Main definitions

* `Cslib.Crypto.KeyExchange.KeyGuesser`, `Cslib.Crypto.KeyExchange.KeyGuesser.IsPPT`: typed
  key-guessing adversaries reading a transcript `t` and returning a guess in `K t`, together with
  their uniform strict-PPT predicate on encodings.
* `Cslib.Crypto.KeyExchange.anonKEGame`, `Cslib.Crypto.KeyExchange.AnonKESecure`: the
  key-guessing game and security notion ([BonehShoup2023], Section 10.1, Attack Game 10.1,
  Definition 10.1, p. 400).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhToCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.cdhToDHKeyGuesser`: mutually inverse conversions between
  Diffie–Hellman key guessers and CDH adversaries.

## Main results

* `Cslib.Crypto.KeyExchange.Correct.anonKEGame_eq_bobKey`: for a `Correct` protocol, guessing
  Alice's key agrees with guessing Bob's key.
* `Cslib.Crypto.PrimeOrderGroupFamily.anonKEGame_dhKeyExchange`,
  `Cslib.Crypto.PrimeOrderGroupFamily.cdhGame_eq_anonKEGame_dhKeyExchange`: game-level identities
  between Diffie–Hellman key guessing and `cdhGame`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_dhToCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_cdhToDHKeyGuesser`: the two conversions preserve
  polynomial-time efficiency.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange_anonKESecure_iff_cdh`: Diffie–Hellman key
  exchange satisfies `AnonKESecure` if and only if `CDH` holds ([BonehShoup2023], Section 10.4.2,
  pp. 407–408).

## Implementation notes

* **Correctness is unbundled from `KeyExchange`:** [BonehShoup2023] defines key-exchange
  protocols to be correct, so Attack Game 10.1 does not distinguish Alice's output key from Bob's.
  Here `Cslib.Crypto.KeyExchange.Correct` is unbundled on `KeyExchange`, matching
  `Cslib.Crypto.KeyExchange.EavSecure`, and `anonKEGame` checks `guess = outcome.aliceKey`. For a
  non-`Correct` protocol this can differ from checking `outcome.bobKey`, so the book's property is
  `protocol.Correct ∧ protocol.AnonKESecure encT encK`, and `Correct.anonKEGame_eq_bobKey`
  connects the two keys under `protocol.Correct`. Honest-party efficiency is also unbundled.
* **Terminology (`AnonKESecure` vs `EavSecure`):** [BonehShoup2023], Definition 10.1 (p. 400),
  calls key-guessing security "secure against an eavesdropper", whereas
  `Cslib.Crypto.KeyExchange.EavSecure` in `KeyExchange.lean` is the Katz–Lindell
  real-versus-ideal indistinguishability notion (`realView` vs `idealView`), which gives
  key-guessing security only when the ideal key is hard to guess (no implication is proved here).
  The name `AnonKESecure` follows Boneh–Shoup's advantage notation `AnonKEadv[A, P]`.
* **Diffie–Hellman and CDH over a setup law:** [BonehShoup2023], Section 10.4.2 (pp. 407–408),
  fixes cyclic group parameters as system parameters and bounds concrete advantages (`AnonKEadv`
  and `CDHadv`). Here `DHTranscript` includes `groupParameters : F.Desc`, and `dhKeyExchange setup`
  draws parameters from an arbitrary `setup : ℕ → PMF F.Desc` (matching `CDH`, which requires no
  efficient sampler); the asymptotic equivalence `dhKeyExchange_anonKESecure_iff_cdh` follows from
  the exact per-parameter game equalities `anonKEGame_dhKeyExchange` and
  `cdhGame_eq_anonKEGame_dhKeyExchange`. Only unauthenticated passive key-guessing security is
  formalized here.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.1 (Attack Game 10.1, Definition 10.1, p. 400) and Section 10.4.2 (pp. 407–408).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace KeyExchange

variable {T : Type} {K : T → Type}

/-- A key-guessing adversary against an anonymous key-exchange protocol
([BonehShoup2023], Section 10.1, Attack Game 10.1, p. 400): given the security parameter and the
public transcript `t`, it outputs a candidate key in `K t`. -/
abbrev KeyGuesser (T : Type) (K : T → Type) : Type :=
  ℕ → (t : T) → ProbComp (K t)

/-- A key-guessing adversary is PPT when one uniform strict PPT machine reads `(1ⁿ, transcript)`
encoded by `encPair encUnary encT` and writes `encK transcript guess`. -/
@[expose]
def KeyGuesser.IsPPT (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool)
    (adversary : KeyGuesser T K) : Prop :=
  IsPPTOn (encPair encUnary encT) encBits fun input =>
    encK input.2 <$> adversary input.1 input.2

/-- The key-guessing game ([BonehShoup2023], Section 10.1, Attack Game 10.1, p. 400): run the
honest protocol execution, hand `outcome.transcript` to `adversary`, and accept when its guess
equals `outcome.aliceKey`. For `Correct` protocols this equals checking `outcome.bobKey`
(`Correct.anonKEGame_eq_bobKey`). -/
@[expose]
noncomputable def anonKEGame [∀ t, DecidableEq (K t)] (protocol : KeyExchange T K)
    (adversary : KeyGuesser T K) (n : ℕ) : Game :=
  Game.withSetup (protocol.execute n) fun outcome => do
    let guess ← adversary n outcome.transcript
    return decide (guess = outcome.aliceKey)

/-- Key-guessing security for anonymous key exchange ([BonehShoup2023], Section 10.1,
Definition 10.1, p. 400): every PPT key-guessing adversary guesses the session key with negligible
probability in `anonKEGame`.

The book builds correctness into protocols, whereas `KeyExchange.Correct` is unbundled here, so the
book's notion corresponds to `protocol.Correct ∧ protocol.AnonKESecure encT encK`. Called
"secure against an eavesdropper" in Boneh–Shoup; distinct from `KeyExchange.EavSecure`, which is
the Katz–Lindell real-versus-ideal indistinguishability notion (it gives key-guessing security
only when the ideal key is hard to guess, and no implication is proved here). -/
@[expose]
def AnonKESecure [∀ t, DecidableEq (K t)] (protocol : KeyExchange T K)
    (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) : Prop :=
  ∀ adversary : KeyGuesser T K, adversary.IsPPT encT encK →
    Negligible fun n => Game.succProbability (protocol.anonKEGame adversary n)

/-- For a correct key-exchange protocol, winning `anonKEGame` (matching Alice's key) has the same
law as matching Bob's key. -/
theorem Correct.anonKEGame_eq_bobKey [∀ t, DecidableEq (K t)] {protocol : KeyExchange T K}
    (hcorr : protocol.Correct) (adversary : KeyGuesser T K) (n : ℕ) :
    protocol.anonKEGame adversary n =
      Game.withSetup (protocol.execute n) fun outcome => do
        let guess ← adversary n outcome.transcript
        return decide (guess = outcome.bobKey) := by
  refine PMF.bind_congr_on_support _ _ _ fun outcome ho => ?_
  dsimp only
  rw [hcorr n outcome ho]

end KeyExchange

namespace PrimeOrderGroupFamily

open KeyExchange

variable (F : PrimeOrderGroupFamily)

/-- View a Diffie–Hellman key-guessing adversary as a CDH adversary over `F`
([BonehShoup2023], Section 10.4.2, pp. 407–408). -/
@[expose]
def dhToCDHAdversary (adversary : KeyGuesser F.DHTranscript F.DHKey) : F.CDHAdversary :=
  fun n d u v => adversary n ⟨d, u, v⟩

/-- View a CDH adversary over `F` as a Diffie–Hellman key-guessing adversary
([BonehShoup2023], Section 10.4.2, pp. 407–408). -/
@[expose]
def cdhToDHKeyGuesser (adversary : F.CDHAdversary) : KeyGuesser F.DHTranscript F.DHKey :=
  fun n t => adversary n t.groupParameters t.aliceShare t.bobShare

/-- Running `anonKEGame` on `F.dhKeyExchange setup` with `adversary` gives the exact same game
as running `F.cdhGame setup` with `F.dhToCDHAdversary adversary`
([BonehShoup2023], Section 10.4.2, pp. 407–408). -/
theorem anonKEGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : KeyGuesser F.DHTranscript F.DHKey) (n : ℕ) :
    (F.dhKeyExchange setup).anonKEGame adversary n =
      F.cdhGame setup (F.dhToCDHAdversary adversary) n := by
  simp only [anonKEGame, dhKeyExchange, cdhGame, Game.withSetup, dhExecution, cdhExperiment,
    dhToCDHAdversary, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, smul_smul]

/-- Running `F.cdhGame setup` with `adversary` gives the exact same game as running `anonKEGame`
on `F.dhKeyExchange setup` with `F.cdhToDHKeyGuesser adversary`
([BonehShoup2023], Section 10.4.2, p. 408). -/
theorem cdhGame_eq_anonKEGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n : ℕ) :
    F.cdhGame setup adversary n =
      (F.dhKeyExchange setup).anonKEGame (F.cdhToDHKeyGuesser adversary) n :=
  (F.anonKEGame_dhKeyExchange setup (F.cdhToDHKeyGuesser adversary) n).symm

open scoped PrimeOrderGroupFamily in
/-- `dhToCDHAdversary` preserves polynomial-time efficiency. -/
theorem isPPT_dhToCDHAdversary {adversary : KeyGuesser F.DHTranscript F.DHKey}
    (hA : adversary.IsPPT F.encDHTranscript F.encDHKey) :
    (F.dhToCDHAdversary adversary).IsPPT := by
  have hprep : ComputableInPolyTime
      (fun x : F.CDHInput =>
        (x.secParam, (⟨x.groupParameters, x.leftPublic, x.rightPublic⟩ : F.DHTranscript)))
      F.encCDHInput (encPair encUnary F.encDHTranscript) := by
    fun_prop
  refine (IsPPTOn.preprocess hA hprep).congr fun x => ?_
  simp only [dhToCDHAdversary, ProbComp.eval_map]
  rfl

open scoped PrimeOrderGroupFamily in
/-- `cdhToDHKeyGuesser` preserves polynomial-time efficiency. -/
theorem isPPT_cdhToDHKeyGuesser {adversary : F.CDHAdversary} (hA : adversary.IsPPT) :
    (F.cdhToDHKeyGuesser adversary).IsPPT F.encDHTranscript F.encDHKey := by
  have hprep : ComputableInPolyTime
      (fun input : ℕ × F.DHTranscript =>
        (⟨input.1, input.2.groupParameters, input.2.aliceShare, input.2.bobShare⟩ : F.CDHInput))
      (encPair encUnary F.encDHTranscript) F.encCDHInput := by
    fun_prop
  refine (IsPPTOn.preprocess hA hprep).congr fun input => ?_
  simp only [cdhToDHKeyGuesser, ProbComp.eval_map]
  rfl

/-- **Diffie–Hellman key exchange is key-guessing secure iff CDH holds**
([BonehShoup2023], Section 10.4.2, pp. 407–408). -/
theorem dhKeyExchange_anonKESecure_iff_cdh (setup : ℕ → PMF F.Desc) :
    (F.dhKeyExchange setup).AnonKESecure F.encDHTranscript F.encDHKey ↔ F.CDH setup := by
  constructor
  · intro h anonA hA
    simpa only [cdhGame_eq_anonKEGame_dhKeyExchange] using
      h _ (F.isPPT_cdhToDHKeyGuesser hA)
  · intro h A hA
    simpa only [anonKEGame_dhKeyExchange] using
      h _ (F.isPPT_dhToCDHAdversary hA)

end PrimeOrderGroupFamily

end Cslib.Crypto
