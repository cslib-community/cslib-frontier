/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Probability.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases

/-!
# Key exchange secure against eavesdroppers

A two-party key-exchange protocol is described here by the law of its honest execution: the
transcript of messages that an eavesdropper sees, the key output by Alice and the key output by
Bob. Keys may live in a set named by the transcript, such as the group chosen in Diffie–Hellman,
so the key type is a family `K : T → Type`. The protocol is correct when the two keys agree on
every execution.

Security against a passive eavesdropper ([KatzLindell2020], Section 11.3, Definition 11.1,
p. 392; compare the session-key indistinguishability remark in [BonehShoup2023], Section 10.1,
p. 400) compares a real experiment, in which the adversary receives the view made of the transcript
and Alice's key, with an ideal experiment, in which the view pairs the transcript with an
independently drawn ideal key. Saying that an adversary guesses a hidden uniform bit with
probability at most `1 / 2 + negl(n)` is the same as requiring negligible advantage between the
real and the ideal experiment. Both experiments are "draw a view, then run the eavesdropper on it"
(`Game.withSetup`), for the view laws `realView` and `idealView` of an execution law. The ideal key
may depend on the transcript through `idealKey : ℕ → (t : T) → PMF (K t)`; Definition 11.1 draws a
uniform `n`-bit word (`EavSecureBits`), while [KatzLindell2020], Theorem 11.3 (p. 394, locator not
verified) uses a uniform element of the group named in the transcript (`dhIdealKey`).

Eavesdroppers are typed: an `Eavesdropper T K` receives the security parameter and a `View T K`.
Encodings appear only in its efficiency predicate `Eavesdropper.IsPPT`, which reads the view
through `encView`, and in `encOutcome` for certifying honest execution programs.

We formalize:

* the Diffie–Hellman protocol ([BonehShoup2023], Section 10.4.1, Figure 10.2, pp. 407–408;
  [KatzLindell2020], Construction 11.2, pp. 392–393, locator not verified) over a
  `PrimeOrderGroupFamily`, in two forms:
  * the fair-coin execution `dhExecutionProb` and protocol `dhKeyExchangeProb`, whose parties
    sample their exponents with `PrimeOrderGroupFamily.sampleExp` (`isPPTOn_dhExecutionProb`),
    always agree on the shared key (`dhKeyExchangeProb_correct`), stay within statistical distance
    `2 / 2 ^ n` of exact-uniform execution (`advantage_bind_dhKeyExchangeProb_le`), satisfy the
    explicit `4 / 2 ^ n` passive-eavesdropping bound `advantage_eavGame_dhKeyExchangeProb_le`, and
    are `EavSecure` against `dhIdealKey` under `DDH` (`DDH.dhKeyExchangeProb_eavSecure`,
    [KatzLindell2020], Theorem 11.3, p. 394, locator not verified; registration pending source
    check, #5657);
  * the ideal-sampling execution `dhExecution` and protocol `dhKeyExchange`, whose parties draw
    exponents from `PMF.uniformOfFintype (ZMod q)`, giving exact game identities with `ddhRealGame`
    and `ddhRandomGame` via `dhEavToDDH` and the ideal-sampling step
    `DDH.dhKeyExchange_eavSecure_ideal` consumed by `DDH.dhKeyExchangeProb_eavSecure`;
* the man-in-the-middle attack of [KatzLindell2020], Exercise 11.3 (p. 399): at a fixed group, an
  active adversary that replaces both public shares shares Alice's key with Alice and Bob's key
  with Bob, while each party's view has exactly the law of the eavesdropper's view of an honest
  execution;
* the protocol of [KatzLindell2020], Exercise 11.4 (p. 400), built from one-time XOR masks: Alice
  and Bob output the same key, yet the XOR of the three transcript words is the key, so the
  protocol is not secure against eavesdroppers.

Honest-party efficiency is unbundled from `KeyExchange`; for `dhExecutionProb`, uniform strict PPT
efficiency on `(1ⁿ, d)` (or on `1ⁿ` along a polynomial-time group schedule) is proved separately in
`isPPTOn_dhExecutionProb`.

## Main definitions

* `Cslib.Crypto.KeyExchange`, `Cslib.Crypto.KeyExchange.Outcome`,
  `Cslib.Crypto.KeyExchange.encOutcome`: protocols as honest-execution laws and outcome encodings.
* `Cslib.Crypto.KeyExchange.View`, `Cslib.Crypto.KeyExchange.encView`,
  `Cslib.Crypto.KeyExchange.Eavesdropper`, `Cslib.Crypto.KeyExchange.Eavesdropper.IsPPT`: typed
  eavesdroppers and their efficiency on encoded views.
* `Cslib.Crypto.KeyExchange.realView`, `Cslib.Crypto.KeyExchange.idealView`,
  `Cslib.Crypto.KeyExchange.realGame`, `Cslib.Crypto.KeyExchange.idealGame`,
  `Cslib.Crypto.KeyExchange.EavSecure`, `Cslib.Crypto.KeyExchange.EavSecureBits`: security against
  eavesdroppers ([KatzLindell2020], Definition 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.DHTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhExecutionProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchangeProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhIdealKey`: the fair-coin and ideal-sampling Diffie–Hellman
  protocols and their group-element ideal key ([KatzLindell2020], Construction 11.2, Theorem 11.3,
  locators not verified).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhEavToDDH`: the reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhMitmExecution`: the man-in-the-middle attack
  (Exercise 11.3).
* `Cslib.Crypto.KeyExchange.xorKeyExchange`, `Cslib.Crypto.KeyExchange.xorEavesdropper`: the XOR
  protocol of Exercise 11.4 and the eavesdropper that recovers its key.

## Main results

* `Cslib.Crypto.KeyExchange.withSetup_realView_bind`,
  `Cslib.Crypto.KeyExchange.withSetup_idealView_bind`: a protocol that draws public parameters
  first is attacked by drawing them, then running the fixed experiment.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_dhExecutionProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchangeProb_correct`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange_correct`: honest fair-coin execution is uniform
  strict PPT, and Alice and Bob output the same key.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_dhKeyExchangeProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_eavGame_dhKeyExchangeProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.dhKeyExchangeProb_eavSecure`: explicit `2 / 2 ^ n` and
  `4 / 2 ^ n` exponent-sampling bounds and passive eavesdropper security of `dhKeyExchangeProb`
  under `DDH` ([KatzLindell2020], Theorem 11.3, p. 394, locator not verified; registration pending
  source check, #5657).
* `Cslib.Crypto.PrimeOrderGroupFamily.withSetup_realView_dhExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.withSetup_idealView_dhExecution`: at a fixed group the
  ideal-sampling experiments are the DDH experiments; `realGame_dhKeyExchange` and
  `idealGame_dhKeyExchange` are the family versions.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhMitmExecution_keys`,
  `Cslib.Crypto.PrimeOrderGroupFamily.map_aliceView_dhMitmExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.map_bobView_dhMitmExecution`: the attack of Exercise 11.3.
* `Cslib.Crypto.KeyExchange.xorKeyExchange_correct`,
  `Cslib.Crypto.KeyExchange.not_eavSecureBits_xorKeyExchange`: the analysis of Exercise 11.4.

## Ideal-sampling steps

* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.dhKeyExchange_eavSecure_ideal`: DDH implies security of
  the ideal-sampling protocol `dhKeyExchange` against eavesdroppers, a step toward
  [KatzLindell2020], Theorem 11.3 (locator not verified) consumed by
  `DDH.dhKeyExchangeProb_eavSecure`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 10.1 (pp. 399–400), Section 10.4.1 (pp. 407–408), and
  Exercise 10.3 (p. 424).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 11.3 (pp. 390–396) and Exercises 11.3–11.4 (pp. 399–400).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- The result of one honest execution of a two-party key-exchange protocol: the transcript seen
by an eavesdropper and the keys output by Alice and by Bob, which lie in the key set `K transcript`
named by the transcript. -/
structure KeyExchange.Outcome (T : Type) (K : T → Type) where
  /-- All messages sent between the parties. -/
  transcript : T
  /-- The key output by Alice. -/
  aliceKey : K transcript
  /-- The key output by Bob. -/
  bobKey : K transcript

/-- A two-party key-exchange protocol with transcripts in `T` and keys in `K transcript`, described
by the law of its honest execution at each security parameter. -/
structure KeyExchange (T : Type) (K : T → Type) where
  /-- The law of the transcript and both keys when Alice and Bob run the protocol honestly. -/
  execute : ℕ → PMF (KeyExchange.Outcome T K)

namespace KeyExchange

variable {T : Type} {K : T → Type}

/-- A key-exchange protocol is correct when Alice and Bob output the same key on every honest
execution ([KatzLindell2020], Section 11.3, p. 391). -/
@[expose]
def Correct (protocol : KeyExchange T K) : Prop :=
  ∀ n, ∀ outcome ∈ (protocol.execute n).support, outcome.aliceKey = outcome.bobKey

/-- The encoding of an honest-execution outcome: the transcript encoded by `encT`, Alice's key
encoded by `encK transcript`, and Bob's key encoded by `encK transcript`, each framed except the
last (`encOutcome_apply`). -/
enc_structure encOutcome (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) :
    Outcome T K where
  transcript : encT,
  aliceKey : (encK transcript) using ((encK transcript).injective),
  bobKey : (encK transcript) using ((encK transcript).injective)

/-- What an eavesdropper is given: a transcript and a candidate key for it. -/
structure View (T : Type) (K : T → Type) where
  /-- All messages sent between the parties. -/
  transcript : T
  /-- The candidate key: Alice's key in the real experiment, an ideal key in the ideal one. -/
  key : K transcript

/-- The encoding of a view: the transcript encoded by `encT`, framed, then the key encoded by
`encK transcript` (`encView_apply`). -/
enc_structure encView (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) : View T K where
  transcript : encT, key : (encK transcript) using ((encK transcript).injective)

/-- The real view: run the protocol honestly and pair the transcript with Alice's key. This is
what the adversary sees in `KE^eav` with hidden bit `0` ([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def realView (execution : PMF (Outcome T K)) : PMF (View T K) := do
  let outcome ← execution
  return ⟨outcome.transcript, outcome.aliceKey⟩

/-- The ideal view: run the protocol honestly and pair the transcript with a fresh key drawn from
`idealKey transcript`. This is what the adversary sees in `KE^eav` with hidden bit `1`
([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def idealView (idealKey : (t : T) → PMF (K t)) (execution : PMF (Outcome T K)) :
    PMF (View T K) := do
  let outcome ← execution
  let key ← idealKey outcome.transcript
  return ⟨outcome.transcript, key⟩

/-- An eavesdropper: given the security parameter and a view, it outputs a bit.
`Eavesdropper.IsPPT` states its efficiency on encodings. -/
abbrev Eavesdropper (T : Type) (K : T → Type) : Type :=
  ℕ → View T K → ProbComp Bool

/-- Eavesdropper input `(1ⁿ, view)`: the security parameter in unary, then the view encoded by
`encView encT encK`. For a constant key encoding these are the words of
`encPair encUnary (encPair encT encK)` on `(n, (transcript, key))`. -/
abbrev encEavInput (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) :
    ℕ × View T K ↪ List Bool :=
  encPair encUnary (encView encT encK)

/-- An eavesdropper is PPT when one uniform strict PPT machine reads `encEavInput encT encK` and
writes the adversary's bit. -/
@[expose]
def Eavesdropper.IsPPT (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool)
    (adversary : Eavesdropper T K) : Prop :=
  IsPPTOn (encEavInput encT encK) encBool fun input => adversary input.1 input.2

/-- The real eavesdropping experiment `KE^eav` with hidden bit `0`: draw the real view, then run
the eavesdropper on it. -/
@[expose]
noncomputable def realGame (protocol : KeyExchange T K) (adversary : Eavesdropper T K) (n : ℕ) :
    Game :=
  Game.withSetup (realView (protocol.execute n)) (adversary n)

/-- The ideal eavesdropping experiment `KE^eav` with hidden bit `1`: draw the ideal view with key
law `idealKey n`, then run the eavesdropper on it. -/
@[expose]
noncomputable def idealGame (protocol : KeyExchange T K) (idealKey : ℕ → (t : T) → PMF (K t))
    (adversary : Eavesdropper T K) (n : ℕ) : Game :=
  Game.withSetup (idealView (idealKey n) (protocol.execute n)) (adversary n)

/-- Security against eavesdroppers with ideal-key law `idealKey`: every uniform strict PPT
eavesdropper has negligible advantage between `realGame` and `idealGame`. -/
@[expose]
def EavSecure (protocol : KeyExchange T K) (encT : T ↪ List Bool)
    (encK : (t : T) → K t ↪ List Bool) (idealKey : ℕ → (t : T) → PMF (K t)) : Prop :=
  Game.Indistinguishable protocol.realGame (protocol.idealGame idealKey)
    (Eavesdropper.IsPPT encT encK)

/-- Security against eavesdroppers for bit-word keys ([KatzLindell2020], Definition 11.1, p. 392):
the ideal key is a uniform `n`-bit word, independent of the transcript. -/
abbrev EavSecureBits (protocol : KeyExchange T fun _ => List Bool) (encT : T ↪ List Bool) :
    Prop :=
  protocol.EavSecure encT (fun _ => encBits) fun n _ => BitString.uniformList n

/-- For a protocol that first draws public parameters `p` from `setup`, then runs the execution
`execution p`, the real experiment draws `p` and then runs the fixed real experiment of
`execution p`. -/
theorem withSetup_realView_bind {P : Type} (setup : PMF P) (execution : P → PMF (Outcome T K))
    (exp : View T K → Experiment) :
    Game.withSetup (realView (setup.bind execution)) exp =
      setup.bind fun p => Game.withSetup (realView (execution p)) exp := by
  simp only [pmf_norm, Game.withSetup, realView]

/-- For a protocol that first draws public parameters `p` from `setup`, then runs the execution
`execution p`, the ideal experiment draws `p` and then runs the fixed ideal experiment of
`execution p`. -/
theorem withSetup_idealView_bind {P : Type} (setup : PMF P) (execution : P → PMF (Outcome T K))
    (idealKey : (t : T) → PMF (K t)) (exp : View T K → Experiment) :
    Game.withSetup (idealView idealKey (setup.bind execution)) exp =
      setup.bind fun p => Game.withSetup (idealView idealKey (execution p)) exp := by
  simp only [pmf_norm, Game.withSetup, idealView]

end KeyExchange

/-! ### The Diffie–Hellman protocol -/

namespace PrimeOrderGroupFamily

open KeyExchange (Eavesdropper View realView idealView)

variable (F : PrimeOrderGroupFamily)

/-- A Diffie–Hellman transcript: the group parameters chosen by Alice and the public shares
`hA = x • g` of Alice and `hB = y • g` of Bob in that group. -/
structure DHTranscript where
  /-- The group parameters sent by Alice. -/
  groupParameters : F.Desc
  /-- Alice's public share `hA = x • g`. -/
  aliceShare : F.Carrier groupParameters
  /-- Bob's public share `hB = y • g`. -/
  bobShare : F.Carrier groupParameters

/-- The encoding of a Diffie–Hellman transcript: the group parameters and the words
`F.encode d hA`, `F.encode d hB` of the shares, each framed except the last
(`encDHTranscript_apply`). -/
enc_structure encDHTranscript (F : PrimeOrderGroupFamily) : DHTranscript F where
  groupParameters : F.encDesc,
  aliceShare : (F.encode groupParameters) using (F.encode_injective groupParameters),
  bobShare : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- A Diffie–Hellman key is an element of the group named in the transcript. -/
abbrev DHKey (transcript : F.DHTranscript) : Type :=
  F.Carrier transcript.groupParameters

/-- A Diffie–Hellman key is encoded as an element of the group named in the transcript. -/
@[expose]
def encDHKey (transcript : F.DHTranscript) : F.DHKey transcript ↪ List Bool :=
  ⟨F.encode transcript.groupParameters, F.encode_injective _⟩

@[simp]
theorem encDHKey_apply (transcript : F.DHTranscript) (key : F.DHKey transcript) :
    F.encDHKey transcript key = F.encode transcript.groupParameters key :=
  rfl

variable {F} in
/-- A computed Diffie–Hellman key is encoded by the word of the computed group element. -/
@[fun_prop] theorem computableInPolyTime_encDHKey {α : Type} {enc : α ↪ List Bool}
    {t : α → F.DHTranscript} {key : (a : α) → F.DHKey (t a)}
    (h : ComputableInPolyTime (fun a => F.encode (t a).groupParameters (key a)) enc encBits) :
    ComputableInPolyTime (fun a => F.encDHKey (t a) (key a)) enc encBits :=
  h

/-- The honest Diffie–Hellman execution in the group `d` ([KatzLindell2020], Construction 11.2,
pp. 392–393). Alice draws a uniform exponent `x` and sends `d` and `hA = x • g`; Bob draws a
uniform exponent `y` and sends `hB = y • g`. Alice outputs `x • hB` and Bob outputs `y • hA`.
Both exponents are drawn exactly uniformly on `ZMod q` at the `PMF` level, an ideal sampler that
no fair-coin machine with a strict polynomial time bound realizes exactly when `q` is not a power of
two (#5293). -/
@[expose]
noncomputable def dhExecution (d : F.Desc) : PMF (KeyExchange.Outcome F.DHTranscript F.DHKey) := do
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let hA := x • F.generator d
  let hB := y • F.generator d
  return { transcript := ⟨d, hA, hB⟩, aliceKey := x • hB, bobKey := y • hA }

/-- The Diffie–Hellman key-exchange protocol ([KatzLindell2020], Construction 11.2): Alice draws
the group parameters `d` from `setup n`, then the parties run `dhExecution d`. -/
@[expose]
noncomputable def dhKeyExchange (setup : ℕ → PMF F.Desc) :
    KeyExchange F.DHTranscript F.DHKey where
  execute n := (setup n).bind F.dhExecution

/-- Every honest Diffie–Hellman execution in the group `d` is `(d, x • g, y • g)` with both keys
equal to `(x * y) • g`. -/
theorem mem_support_dhExecution {d : F.Desc} {outcome : KeyExchange.Outcome F.DHTranscript F.DHKey}
    (h : outcome ∈ (F.dhExecution d).support) :
    ∃ x y : ZMod (F.order d), outcome = {
      transcript := ⟨d, x • F.generator d, y • F.generator d⟩
      aliceKey := (x * y) • F.generator d
      bobKey := (x * y) • F.generator d } := by
  supp_cases h [dhExecution] with ⟨x, y, rfl⟩
  exact ⟨x, y, by rw [smul_smul, smul_smul, mul_comm y x]⟩

/-- Alice and Bob output the same key, `(x * y) • g` ([KatzLindell2020], p. 393). -/
theorem dhKeyExchange_correct (setup : ℕ → PMF F.Desc) : (F.dhKeyExchange setup).Correct := by
  intro n outcome h
  supp_cases h [dhKeyExchange] with ⟨d, -, h⟩
  obtain ⟨x, y, rfl⟩ := F.mem_support_dhExecution h
  rfl

/-- The ideal key of [KatzLindell2020], Theorem 11.3 (p. 394): a uniform element of the group
named in the transcript. -/
@[expose]
noncomputable def dhIdealKey (transcript : F.DHTranscript) : PMF (F.DHKey transcript) :=
  (PMF.uniformOfFintype (ZMod (F.order transcript.groupParameters))).map
    fun z => z • F.generator transcript.groupParameters

/-- Run an eavesdropper on Diffie–Hellman views as a DDH distinguisher: the elements `(u, v, w)`
of the group `d` are passed on as the transcript `(d, u, v)` with key `w`. -/
@[expose]
def dhEavToDDH (adversary : Eavesdropper F.DHTranscript F.DHKey) : F.DDHDistinguisher :=
  fun n d u v w => adversary n ⟨⟨d, u, v⟩, w⟩

/-- At a fixed group, the real eavesdropping experiment on Diffie–Hellman is the real DDH
experiment. -/
theorem withSetup_realView_dhExecution (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ)
    (d : F.Desc) :
    Game.withSetup (realView (F.dhExecution d)) (adversary n) =
      ProbComp.eval
        (ddhRealExperiment (F.order d) (F.generator d) (F.dhEavToDDH adversary n d)) := by
  simp only [pmf_norm, Game.withSetup, realView, dhExecution, eval_ddhRealExperiment, dhEavToDDH,
    smul_smul]

/-- At a fixed group and with the uniform group element as ideal key, the ideal eavesdropping
experiment on Diffie–Hellman is the random DDH experiment. -/
theorem withSetup_idealView_dhExecution (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ)
    (d : F.Desc) :
    Game.withSetup (idealView F.dhIdealKey (F.dhExecution d)) (adversary n) =
      ProbComp.eval
        (ddhRandomExperiment (F.order d) (F.generator d) (F.dhEavToDDH adversary n d)) := by
  simp only [pmf_norm, Game.withSetup, idealView, dhExecution, dhIdealKey, eval_ddhRandomExperiment,
    dhEavToDDH]

/-- The real eavesdropping experiment on Diffie–Hellman is the real DDH experiment. -/
theorem realGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ) :
    (F.dhKeyExchange setup).realGame adversary n =
      F.ddhRealGame setup (F.dhEavToDDH adversary) n := by
  rw [ddhRealGame, Game.withSetup]
  simp only [KeyExchange.realGame, dhKeyExchange, KeyExchange.withSetup_realView_bind,
    withSetup_realView_dhExecution]

/-- With the uniform group element as ideal key, the ideal eavesdropping experiment on
Diffie–Hellman is the random DDH experiment. -/
theorem idealGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ) :
    (F.dhKeyExchange setup).idealGame (fun _ => F.dhIdealKey) adversary n =
      F.ddhRandomGame setup (F.dhEavToDDH adversary) n := by
  rw [ddhRandomGame, Game.withSetup]
  simp only [KeyExchange.idealGame, dhKeyExchange, KeyExchange.withSetup_idealView_bind,
    withSetup_idealView_dhExecution]

open scoped KeyExchange in
/-- The distinguisher `dhEavToDDH` is uniform strict PPT when the eavesdropper is. -/
theorem isPPT_dhEavToDDH {adversary : Eavesdropper F.DHTranscript F.DHKey}
    (hA : adversary.IsPPT F.encDHTranscript F.encDHKey) :
    (F.dhEavToDDH adversary).IsPPT :=
  IsPPTOn.preprocess hA (prepare := fun x : F.DDHInput =>
    (x.secParam, (⟨⟨x.groupParameters, x.leftPublic, x.rightPublic⟩, x.candidateShared⟩ :
      View F.DHTranscript F.DHKey)))
    (by fun_prop)

/-- Ideal-sampling step toward [KatzLindell2020], Theorem 11.3, p. 394 (locator not verified), not
the cited result: if the Decisional Diffie–Hellman assumption holds for `setup`, then no uniform
strict PPT eavesdropper distinguishes the transcript and Alice's key of `dhKeyExchange setup`,
whose parties draw their exponents exactly uniformly on `ZMod q` at the `PMF` level, from the
transcript and a uniform element of the same group. Consumed by `DDH.dhKeyExchangeProb_eavSecure`,
which replaces exact uniform exponent draws with the fair-coin sampler `sampleExp`. -/
theorem DDH.dhKeyExchange_eavSecure_ideal {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    (F.dhKeyExchange setup).EavSecure F.encDHTranscript F.encDHKey fun _ => F.dhIdealKey := by
  intro adversary hA
  simpa only [realGame_dhKeyExchange, idealGame_dhKeyExchange] using
    hDDH _ (F.isPPT_dhEavToDDH hA)

/-! ### Fair-coin Diffie–Hellman execution -/

/-- The honest fair-coin Diffie–Hellman execution in the group `d` at security parameter `n`
([BonehShoup2023], Section 10.4.1, Figure 10.2, pp. 407–408). Alice and Bob each sample an exponent
with `F.sampleExp n d` (within statistical distance `1 / 2 ^ n` of uniform on `ZMod (F.order d)`);
Alice sends `hA = x • g` and Bob sends `hB = y • g`, and Alice outputs `x • hB` while Bob outputs
`y • hA`. -/
@[expose]
noncomputable def dhExecutionProb (n : ℕ) (d : F.Desc) :
    ProbComp (KeyExchange.Outcome F.DHTranscript F.DHKey) := do
  let x ← F.sampleExp n d
  let y ← F.sampleExp n d
  let hA := (x : ZMod (F.order d)) • F.generator d
  let hB := (y : ZMod (F.order d)) • F.generator d
  return {
    transcript := ⟨d, hA, hB⟩
    aliceKey := (x : ZMod (F.order d)) • hB
    bobKey := (y : ZMod (F.order d)) • hA }

/-- The fair-coin Diffie–Hellman key-exchange protocol ([BonehShoup2023], Section 10.4.1,
Figure 10.2, pp. 407–408): public group parameters `d` are drawn from `setup n`, then Alice and Bob
run `dhExecutionProb n d` using `sampleExp`. -/
@[expose]
noncomputable def dhKeyExchangeProb (setup : ℕ → PMF F.Desc) :
    KeyExchange F.DHTranscript F.DHKey where
  execute n := (setup n).bind fun d => ProbComp.eval (F.dhExecutionProb n d)

open scoped KeyExchange PrimeOrderGroupFamily in
/-- `dhExecutionProb` is uniform strict PPT whenever `n` and `d` are computable in polynomial
time. -/
theorem isPPTOn_dhExecutionProb {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn (KeyExchange.encOutcome F.encDHTranscript F.encDHKey)
      (fun a => F.dhExecutionProb (n a) (d a)) := by
  have hfst : ComputableInPolyTime Prod.fst (encPair encIn encNat) encIn := .fst _ _
  exact (F.isPPTOn_sampleExp hn hd).bind_with
    ((F.isPPTOn_sampleExp (hn.comp hfst) (hd.comp hfst)).bind_with
      (ComputableInPolyTime.isPPTOn (by fun_prop)))

/-- In every honest fair-coin Diffie–Hellman execution, Alice and Bob output the same key
`((x : ZMod q) * y) • g`. -/
theorem dhKeyExchangeProb_correct (setup : ℕ → PMF F.Desc) :
    (F.dhKeyExchangeProb setup).Correct := by
  intro n outcome h
  supp_cases h [dhKeyExchangeProb, dhExecutionProb] with ⟨d, -, x, -, y, -, rfl⟩
  rw [smul_smul, smul_smul, mul_comm (y : ZMod (F.order d)) x]

/-- Replacing `dhKeyExchangeProb` by the exact-uniform `dhKeyExchange` before any Boolean game
continuation `k` changes `Game.advantage` by at most `2 / 2 ^ n` (`1 / 2 ^ n` for each party's
`sampleExp` draw). -/
theorem advantage_bind_dhKeyExchangeProb_le (setup : ℕ → PMF F.Desc) (n : ℕ)
    (k : KeyExchange.Outcome F.DHTranscript F.DHKey → Game) :
    Game.advantage
      (((F.dhKeyExchangeProb setup).execute n).bind k)
      (((F.dhKeyExchange setup).execute n).bind k) ≤
      2 / 2 ^ n := by
  simp only [dhKeyExchangeProb, dhKeyExchange, PMF.bind_bind]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  let outcomeOf (d : F.Desc) (α β : ZMod (F.order d)) :
      KeyExchange.Outcome F.DHTranscript F.DHKey :=
    { transcript := ⟨d, α • F.generator d, β • F.generator d⟩
      aliceKey := α • (β • F.generator d)
      bobKey := β • (α • F.generator d) }
  have hprob : (ProbComp.eval (F.dhExecutionProb n d)).bind k =
      (ProbComp.eval (F.sampleExp n d)).bind fun x =>
        (ProbComp.eval (F.sampleExp n d)).bind fun y =>
          k (outcomeOf d x y) := by
    simp only [dhExecutionProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, outcomeOf]
  have hideal : (F.dhExecution d).bind k =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          k (outcomeOf d α β) := by
    simp only [dhExecution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind, outcomeOf]
  rw [hprob, hideal]
  exact F.advantage_bind_sampleExp_pair_le n d (fun α β => k (outcomeOf d α β))

/-- Against `dhKeyExchangeProb`, any eavesdropper's advantage between the real key and the uniform
group-element ideal key `dhIdealKey` is at most its DDH advantage via `dhEavToDDH` plus the
`4 / 2 ^ n` fair-coin sampling loss (`2 / 2 ^ n` in each of the real and ideal games). -/
theorem advantage_eavGame_dhKeyExchangeProb_le (setup : ℕ → PMF F.Desc)
    (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ) :
    Game.advantage
      ((F.dhKeyExchangeProb setup).realGame adversary n)
      ((F.dhKeyExchangeProb setup).idealGame (fun _ => F.dhIdealKey) adversary n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.dhEavToDDH adversary) n)
        (F.ddhRandomGame setup (F.dhEavToDDH adversary) n) +
      4 / 2 ^ n := by
  have hreal : Game.advantage ((F.dhKeyExchangeProb setup).realGame adversary n)
      ((F.dhKeyExchange setup).realGame adversary n) ≤ 2 / 2 ^ n := by
    simpa only [KeyExchange.realGame, Game.withSetup, KeyExchange.realView, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind] using
      F.advantage_bind_dhKeyExchangeProb_le setup n
        (fun outcome => ProbComp.eval (adversary n ⟨outcome.transcript, outcome.aliceKey⟩))
  have hideal : Game.advantage
      ((F.dhKeyExchangeProb setup).idealGame (fun _ => F.dhIdealKey) adversary n)
      ((F.dhKeyExchange setup).idealGame (fun _ => F.dhIdealKey) adversary n) ≤ 2 / 2 ^ n := by
    simpa only [KeyExchange.idealGame, Game.withSetup, KeyExchange.idealView,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind] using
      F.advantage_bind_dhKeyExchangeProb_le setup n
        (fun outcome => (F.dhIdealKey outcome.transcript).bind
          fun key => ProbComp.eval (adversary n ⟨outcome.transcript, key⟩))
  have h4 := Game.advantage_four_hop_le hreal hideal
  rw [F.realGame_dhKeyExchange, F.idealGame_dhKeyExchange] at h4
  refine h4.trans_eq ?_
  ext
  push_cast
  ring

/-- **Under DDH, Diffie–Hellman key exchange is secure against passive eavesdroppers**
([KatzLindell2020], Section 11.3, Theorem 11.3, p. 394, locator not verified; registration pending
a source check against [KatzLindell2020] Chapter 11, #5657; compare the session-key
indistinguishability remark of [BonehShoup2023], Section 10.1, p. 400): if `F.DDH setup` holds,
then the fair-coin protocol `dhKeyExchangeProb setup` satisfies `KeyExchange.EavSecure` against
uniform strict PPT eavesdroppers when the ideal key is the uniform group element `dhIdealKey`.
Derived from `DDH.dhKeyExchange_eavSecure_ideal` and `advantage_bind_dhKeyExchangeProb_le` with
fair-coin sampling loss at most `4 / 2 ^ n`. -/
theorem DDH.dhKeyExchangeProb_eavSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    (F.dhKeyExchangeProb setup).EavSecure F.encDHTranscript F.encDHKey fun _ => F.dhIdealKey := by
  intro adversary hA
  have hideal := hDDH.dhKeyExchange_eavSecure_ideal adversary hA
  have h4 : Negligible fun n => (4 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 4
  refine negligible_of_le (hideal.add h4) fun n => ?_
  dsimp only [Pi.add_apply]
  rw [F.realGame_dhKeyExchange, F.idealGame_dhKeyExchange]
  exact F.advantage_eavGame_dhKeyExchangeProb_le setup adversary n

/-! ### The man-in-the-middle attack -/

/-- The outcome of the man-in-the-middle attack of [KatzLindell2020], Exercise 11.3 (p. 399):
the view of Alice and of Bob, each made of the transcript that party sees and the key it outputs,
and the keys the adversary computes for its sessions with each of them. -/
structure DHMitmOutcome where
  /-- Alice's view: the transcript `(d, hA, hB')` with the substituted share `hB'`, and her key. -/
  aliceView : View F.DHTranscript F.DHKey
  /-- Bob's view: the transcript `(d, hA', hB)` with the substituted share `hA'`, and his key. -/
  bobView : View F.DHTranscript F.DHKey
  /-- The key the adversary computes for its session with Alice. -/
  adversaryAliceKey : F.DHKey aliceView.transcript
  /-- The key the adversary computes for its session with Bob. -/
  adversaryBobKey : F.DHKey bobView.transcript

/-- The man-in-the-middle attack on Diffie–Hellman in the group `d` ([KatzLindell2020],
Exercise 11.3, p. 399). Alice and Bob run Construction 11.2 honestly with exponents `x` and `y`.
The adversary draws its own exponents `x'` and `y'`, delivers `hB' = y' • g` to Alice in place of
`hB` and `hA' = x' • g` to Bob in place of `hA`, and computes `y' • hA` and `x' • hB`. Over a setup
law, the attack draws `d` first. -/
@[expose]
noncomputable def dhMitmExecution (d : F.Desc) : PMF F.DHMitmOutcome := do
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let x' ← PMF.uniformOfFintype (ZMod (F.order d))
  let y' ← PMF.uniformOfFintype (ZMod (F.order d))
  let hA := x • F.generator d
  let hB := y • F.generator d
  let hA' := x' • F.generator d
  let hB' := y' • F.generator d
  return {
    aliceView := ⟨⟨d, hA, hB'⟩, x • hB'⟩
    bobView := ⟨⟨d, hA', hB⟩, y • hA'⟩
    adversaryAliceKey := y' • hA
    adversaryBobKey := x' • hB }

/-- In the man-in-the-middle attack the adversary knows the key Alice outputs and the key Bob
outputs. -/
theorem dhMitmExecution_keys (d : F.Desc) :
    ∀ outcome ∈ (F.dhMitmExecution d).support,
      outcome.adversaryAliceKey = outcome.aliceView.key ∧
        outcome.adversaryBobKey = outcome.bobView.key := by
  intro outcome h
  supp_cases h [dhMitmExecution]
  exact ⟨smul_comm _ _ _, smul_comm _ _ _⟩

/-- Alice cannot detect the attack: her view has exactly the law of the eavesdropper's view of an
honest Diffie–Hellman execution. -/
theorem map_aliceView_dhMitmExecution (d : F.Desc) :
    (F.dhMitmExecution d).map DHMitmOutcome.aliceView = realView (F.dhExecution d) := by
  simp only [pmf_norm, dhMitmExecution, realView, dhExecution, PMF.bind_const]

/-- Bob cannot detect the attack: his view has exactly the law of the eavesdropper's view of an
honest Diffie–Hellman execution. -/
theorem map_bobView_dhMitmExecution (d : F.Desc) :
    (F.dhMitmExecution d).map DHMitmOutcome.bobView = realView (F.dhExecution d) := by
  simp only [pmf_norm, dhMitmExecution, realView, dhExecution, PMF.bind_const]
  pmf_hoist (occ := 2) (PMF.uniformOfFintype (ZMod (F.order d)))
  pmf_swap with x y
  rw [smul_comm y x]

end PrimeOrderGroupFamily

/-! ### A protocol built from XOR masks -/

namespace KeyExchange

/-- A transcript of the protocol of [KatzLindell2020], Exercise 11.4: three bit words. -/
structure XorTranscript where
  /-- Alice's first message `s = k ⊕ r`. -/
  aliceFirst : List Bool
  /-- Bob's reply `u = s ⊕ t`. -/
  bobReply : List Bool
  /-- Alice's second message `w = u ⊕ r`. -/
  aliceSecond : List Bool

/-- The encoding of an XOR transcript: its three words, each framed except the last
(`encXorTranscript_apply`). -/
enc_structure encXorTranscript : XorTranscript where
  aliceFirst : encBits, bobReply : encBits, aliceSecond : encBits

/-- The XOR `w ⊕ (s ⊕ u)` of the three words of an XOR transcript. -/
@[expose]
def XorTranscript.xorAll (transcript : XorTranscript) : List Bool :=
  List.zipWith Bool.xor transcript.aliceSecond
    (List.zipWith Bool.xor transcript.aliceFirst transcript.bobReply)

/-- The protocol of [KatzLindell2020], Exercise 11.4 (p. 400). Alice draws uniform `n`-bit words
`k` and `r` and sends `s = k ⊕ r`; Bob draws a uniform `n`-bit word `t` and sends `u = s ⊕ t`;
Alice sends `w = u ⊕ r`. Alice outputs `k` and Bob outputs `w ⊕ t`. -/
@[expose]
noncomputable def xorKeyExchange : KeyExchange XorTranscript fun _ => List Bool where
  execute n := do
    let k ← BitString.uniformList n
    let r ← BitString.uniformList n
    let t ← BitString.uniformList n
    let s := List.zipWith Bool.xor k r
    let u := List.zipWith Bool.xor s t
    let w := List.zipWith Bool.xor u r
    return { transcript := ⟨s, u, w⟩, aliceKey := k, bobKey := List.zipWith Bool.xor w t }

/-- For equal-length words, Bob's key `w ⊕ t` equals `k`, and so does `w ⊕ (s ⊕ u)`. -/
private theorem xor_identities : ∀ k r t : List Bool, r.length = k.length → t.length = k.length →
    let s := List.zipWith Bool.xor k r
    let u := List.zipWith Bool.xor s t
    let w := List.zipWith Bool.xor u r
    List.zipWith Bool.xor w t = k ∧ List.zipWith Bool.xor w (List.zipWith Bool.xor s u) = k
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, hr, _ => by simp at hr
  | _ :: _, _ :: _, [], _, ht => by simp at ht
  | a :: k, b :: r, c :: t, hr, ht => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hr ht
    obtain ⟨h₁, h₂⟩ := xor_identities k r t hr ht
    simp only [List.zipWith_cons_cons, h₁, h₂, List.cons.injEq, and_true]
    cases a <;> cases b <;> cases c <;> decide

/-- Every honest execution of the XOR protocol comes from `n`-bit words `k`, `r` and `t`. -/
theorem mem_support_xorKeyExchange {n : ℕ} {outcome : Outcome XorTranscript fun _ => List Bool}
    (h : outcome ∈ (xorKeyExchange.execute n).support) :
    ∃ k r t : List Bool, k.length = n ∧ r.length = n ∧ t.length = n ∧
      outcome = {
        transcript := ⟨List.zipWith Bool.xor k r,
          List.zipWith Bool.xor (List.zipWith Bool.xor k r) t,
          List.zipWith Bool.xor (List.zipWith Bool.xor (List.zipWith Bool.xor k r) t) r⟩
        aliceKey := k
        bobKey := List.zipWith Bool.xor
          (List.zipWith Bool.xor (List.zipWith Bool.xor (List.zipWith Bool.xor k r) t) r) t } := by
  supp_cases h [xorKeyExchange] with ⟨k, hk, r, hr, t, ht, rfl⟩
  exact ⟨k, r, t, BitString.length_of_mem_support_uniformList hk,
    BitString.length_of_mem_support_uniformList hr,
    BitString.length_of_mem_support_uniformList ht, rfl⟩

/-- Alice and Bob output the same key ([KatzLindell2020], Exercise 11.4, p. 400). -/
theorem xorKeyExchange_correct : xorKeyExchange.Correct := by
  intro n outcome h
  obtain ⟨k, r, t, hk, hr, ht, rfl⟩ := mem_support_xorKeyExchange h
  exact ((xor_identities k r t (hr.trans hk.symm) (ht.trans hk.symm)).1).symm

/-- The eavesdropper that accepts exactly when the candidate key is the XOR `w ⊕ (s ⊕ u)` of the
three transcript words. -/
@[expose]
def xorEavesdropper : Eavesdropper XorTranscript fun _ => List Bool :=
  fun _ view => return decide (view.key = view.transcript.xorAll)

/-- On the real key the eavesdropper always accepts. -/
theorem realGame_xorEavesdropper (n : ℕ) :
    xorKeyExchange.realGame xorEavesdropper n = PMF.pure true := by
  simp only [pmf_norm, realGame, Game.withSetup, realView]
  rw [← PMF.bind_const (xorKeyExchange.execute n) (PMF.pure true)]
  peel_binds outcome
  obtain ⟨k, r, t, hk, hr, ht, rfl⟩ := mem_support_xorKeyExchange outcome_mem
  simp only [xorEavesdropper, XorTranscript.xorAll, ProbComp.eval_pure,
    (xor_identities k r t (hr.trans hk.symm) (ht.trans hk.symm)).2, decide_true]

/-- On a uniform `n`-bit key the eavesdropper accepts with probability at most `1 / 2 ^ n`. -/
theorem idealGame_xorEavesdropper_true_le (n : ℕ) :
    xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n true ≤
      1 / 2 ^ n := by
  simp only [pmf_norm, idealGame, Game.withSetup, idealView, xorEavesdropper, PMF.bind_apply,
    PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq, mul_ite, mul_one, mul_zero,
    tsum_ite_eq]
  calc ∑' outcome, xorKeyExchange.execute n outcome *
        BitString.uniformList n outcome.transcript.xorAll
      ≤ ∑' outcome, xorKeyExchange.execute n outcome * (1 / 2 ^ n) :=
        tsum_le_tsum fun _ => mul_le_mul_of_nonneg_left (BitString.uniformList_apply_le _ _)
          zero_le
    _ = 1 / 2 ^ n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- From `n = 1` on, the eavesdropper's advantage is at least `1 / 2`. -/
theorem half_le_advantage_xorEavesdropper {n : ℕ} (hn : n ≠ 0) :
    (1 / 2 : ℝ≥0) ≤ Game.advantage (xorKeyExchange.realGame xorEavesdropper n)
      (xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n) := by
  have hle : xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n
      true ≤ 2⁻¹ :=
    (idealGame_xorEavesdropper_true_le n).trans (by
      rw [one_div]
      exact ENNReal.inv_le_inv.mpr (le_self_pow₀ (by norm_num) hn))
  have hreal := ENNReal.toReal_mono (by simp) hle
  rw [← NNReal.coe_le_coe, Game.coe_advantage, realGame_xorEavesdropper]
  simp only [Game.coe_succProbability, PMF.pure_apply, ite_true, ENNReal.toReal_one,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal ⊢
  rw [abs_of_nonneg (by linarith)]
  push_cast
  linarith

/-- The XOR eavesdropper is uniform strict PPT. -/
theorem isPPT_xorEavesdropper : xorEavesdropper.IsPPT encXorTranscript fun _ => encBits := by
  have hkey : ComputableInPolyTime (fun input : ℕ × View XorTranscript (fun _ => List Bool) =>
      input.2.key) (encEavInput encXorTranscript fun _ => encBits) encBits :=
    encView_key_polyTime encXorTranscript (fun _ => encBits) (.snd _ _)
  have hrec : ComputableInPolyTime (fun input : ℕ × View XorTranscript (fun _ => List Bool) =>
      input.2.transcript.xorAll) (encEavInput encXorTranscript fun _ => encBits) encBits := by
    unfold XorTranscript.xorAll
    fun_prop
  exact (hkey.decide_eq' hrec).isPPTOn

/-- **The XOR protocol is not secure against eavesdroppers** ([KatzLindell2020], Exercise 11.4,
p. 400): the XOR of the three transcript words is the key, so the eavesdropper
`xorEavesdropper` has advantage at least `1 / 2` at every parameter `n ≥ 1`. -/
theorem not_eavSecureBits_xorKeyExchange : ¬ xorKeyExchange.EavSecureBits encXorTranscript := by
  intro h
  refine not_negligible_const (c := (1 / 2 : ℝ≥0)) (by norm_num) ?_
  exact negligible_of_le ((h xorEavesdropper isPPT_xorEavesdropper).shift 1)
    fun n => half_le_advantage_xorEavesdropper n.succ_ne_zero

end KeyExchange

end Cslib.Crypto
