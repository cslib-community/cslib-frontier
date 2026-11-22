/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.KeyExchange
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Bind

/-!
# Key-guessing security for anonymous key exchange

[BonehShoup2023], Section 10.1 (Attack Game 10.1 and Definition 10.1, p. 400), defines key-guessing
security for an anonymous (unauthenticated) two-party key-exchange protocol: after an honest
execution outputs its public transcript and key, a PPT adversary given the transcript tries to
output the exact shared key. Section 10.4.2 (p. 408) states that Diffie–Hellman key exchange
satisfies this notion if and only if the Computational Diffie–Hellman assumption holds.

In Section 10.1 (pp. 399–400) Alice and Bob are probabilistic machines whose transcript is a
function of their random bits. `PrimeOrderGroupFamily.dhKeyExchangeProb` runs `dhExecutionProb`, in
which Alice and Bob sample their exponents with `PrimeOrderGroupFamily.sampleExp` (certified
uniform strict PPT in `isPPTOn_dhExecutionProb` and correct in `dhKeyExchangeProb_correct`, within
statistical distance `1 / 2 ^ n` of uniform on `ZMod q` per party). Its `anonKEGame` is within
`2 / 2 ^ n` of `cdhGame` (`advantage_anonKEGame_dhKeyExchangeProb_cdhGame_le`), yielding the
faithful equivalence `dhKeyExchangeProb_anonKESecure_iff_cdh` from the exact-uniform step
`dhKeyExchange_anonKESecure_iff_cdh_ideal`.

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
  between ideal-sampling Diffie–Hellman key guessing and `cdhGame`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_dhToCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_cdhToDHKeyGuesser`: the two conversions preserve
  polynomial-time efficiency.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_anonKEGame_dhKeyExchangeProb_cdhGame_le`: explicit
  `2 / 2 ^ n` exponent-sampling bound between fair-coin Diffie–Hellman `anonKEGame` and `cdhGame`.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchangeProb_anonKESecure_iff_cdh`: the fair-coin
  Diffie–Hellman protocol `dhKeyExchangeProb` satisfies `AnonKESecure` if and only if `CDH` holds
  ([BonehShoup2023], Section 10.4.2, p. 408).

## Ideal-sampling steps

* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange_anonKESecure_iff_cdh_ideal`: the
  ideal-sampling protocol `dhKeyExchange` satisfies `AnonKESecure` if and only if `CDH` holds,
  consumed by `dhKeyExchangeProb_anonKESecure_iff_cdh`.

## Implementation notes

* **Correctness and party efficiency are unbundled from `KeyExchange`:** [BonehShoup2023] defines
  key-exchange protocols to be correct probabilistic machines, so Attack Game 10.1 does not
  distinguish Alice's output key from Bob's. Here `Cslib.Crypto.KeyExchange.Correct` is unbundled
  on `KeyExchange`, matching `Cslib.Crypto.KeyExchange.EavSecure`, and `anonKEGame` checks
  `guess = outcome.aliceKey` (`Correct.anonKEGame_eq_bobKey` connects the two keys under
  `protocol.Correct`). For `dhKeyExchangeProb`, correctness and uniform strict-PPT execution are
  `dhKeyExchangeProb_correct` and `isPPTOn_dhExecutionProb`.
* **Terminology (`AnonKESecure` vs `EavSecure`):** [BonehShoup2023], Definition 10.1 (p. 400),
  calls key-guessing security "secure against an eavesdropper", whereas
  `Cslib.Crypto.KeyExchange.EavSecure` in `KeyExchange.lean` is the Katz–Lindell
  real-versus-ideal indistinguishability notion (`realView` vs `idealView`), which gives
  key-guessing security only when the ideal key is hard to guess (no implication is proved here).
  The name `AnonKESecure` follows Boneh–Shoup's advantage notation `AnonKEadv[A, P]`.
* **Diffie–Hellman and CDH over a setup law:** [BonehShoup2023], Section 10.4.2 (pp. 407–408),
  fixes cyclic group parameters as system parameters (or draws them via an efficient system
  parameterization algorithm in Section 10.5.2, Definition 10.9, p. 413). Here `DHTranscript`
  includes `groupParameters : F.Desc`, and `dhKeyExchangeProb setup` draws parameters from an
  arbitrary `setup : ℕ → PMF F.Desc` (matching `CDH`, which requires no efficient sampler). Only
  unauthenticated passive key-guessing security is formalized here.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.1 (Attack Game 10.1, Definition 10.1, p. 400) and Section 10.4.2 (pp. 407–408).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

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

/-- Ideal-sampling step toward [BonehShoup2023], Section 10.4.2, p. 408, not the cited result:
`dhKeyExchange setup`, whose parties draw their exponents exactly uniformly on `ZMod q` at the
`PMF` level rather than as probabilistic machines on random bits (Section 10.1, pp. 399–400), is
key-guessing secure (`AnonKESecure`, Definition 10.1) if and only if `CDH` holds for `setup`.
Consumed by `dhKeyExchangeProb_anonKESecure_iff_cdh`, which proves the equivalence for the
fair-coin protocol `dhKeyExchangeProb`. -/
theorem dhKeyExchange_anonKESecure_iff_cdh_ideal (setup : ℕ → PMF F.Desc) :
    (F.dhKeyExchange setup).AnonKESecure F.encDHTranscript F.encDHKey ↔ F.CDH setup := by
  constructor
  · intro h anonA hA
    simpa only [cdhGame_eq_anonKEGame_dhKeyExchange] using
      h _ (F.isPPT_cdhToDHKeyGuesser hA)
  · intro h A hA
    simpa only [anonKEGame_dhKeyExchange] using
      h _ (F.isPPT_dhToCDHAdversary hA)

/-- The key-guessing game `anonKEGame` against the fair-coin Diffie–Hellman protocol
`dhKeyExchangeProb` and the CDH game `cdhGame` on `dhToCDHAdversary adversary` differ in success
probability by at most `2 / 2 ^ n` (`1 / 2 ^ n` for each party's `sampleExp` draw). Because
`dhToCDHAdversary (cdhToDHKeyGuesser B) = B` is definitional, instantiating `adversary` with
`cdhToDHKeyGuesser B` gives the same `2 / 2 ^ n` bound in the converse direction. -/
theorem advantage_anonKEGame_dhKeyExchangeProb_cdhGame_le (setup : ℕ → PMF F.Desc)
    (adversary : KeyGuesser F.DHTranscript F.DHKey) (n : ℕ) :
    Game.advantage
      ((F.dhKeyExchangeProb setup).anonKEGame adversary n)
      (F.cdhGame setup (F.dhToCDHAdversary adversary) n) ≤
      2 / 2 ^ n := by
  rw [← F.anonKEGame_dhKeyExchange]
  exact F.advantage_bind_dhKeyExchangeProb_le setup n _

/-- **Diffie–Hellman anonymous key exchange is key-guessing secure if and only if CDH holds**
([BonehShoup2023], Section 10.4.2, p. 408, with Attack Game 10.1 and Definition 10.1, Section 10.1,
p. 400, and Attack Game 10.5 and Definition 10.7, Section 10.5, pp. 409–410): the fair-coin
protocol `dhKeyExchangeProb setup`, whose parties sample their exponents with `sampleExp`
(`isPPTOn_dhExecutionProb`, `dhKeyExchangeProb_correct`), satisfies `AnonKESecure` against uniform
strict PPT key guessers if and only if `F.CDH setup` holds. Derived from
`dhKeyExchange_anonKESecure_iff_cdh_ideal` and `advantage_bind_dhKeyExchangeProb_le` with sampling
loss at most `2 / 2 ^ n`. -/
theorem dhKeyExchangeProb_anonKESecure_iff_cdh (setup : ℕ → PMF F.Desc) :
    (F.dhKeyExchangeProb setup).AnonKESecure F.encDHTranscript F.encDHKey ↔ F.CDH setup := by
  refine Iff.trans ⟨fun h A hA => ?_, fun h A hA => ?_⟩
    (F.dhKeyExchange_anonKESecure_iff_cdh_ideal setup)
  · refine negligible_of_le ((h A hA).add (negligible_const_div_two_pow 2)) fun n => ?_
    exact Game.succProbability_le_add_of_advantage_le
      ((Game.advantage_comm _ _).trans_le (F.advantage_bind_dhKeyExchangeProb_le setup n _))
  · refine negligible_of_le ((h A hA).add (negligible_const_div_two_pow 2)) fun n => ?_
    exact Game.succProbability_le_add_of_advantage_le
      (F.advantage_bind_dhKeyExchangeProb_le setup n _)

end PrimeOrderGroupFamily

end Cslib.Crypto
