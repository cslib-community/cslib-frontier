/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.KeyExchange.KeyGuessing
import CslibFrontier.Probability.PMF.Bind

/-!
# Trapdoor function schemes and anonymous key exchange

[BonehShoup2023], Section 10.2 (Definition 10.2, pp. 400–401), defines a trapdoor function scheme
`(G, F, I)` with key generation `G`, public evaluation `F(pk, ·)` and secret-key inversion
`I(sk, ·)` satisfying `I(sk, F(pk, x)) = x`, together with its one-wayness game and security
notion (Attack Game 10.2 and Definition 10.3, p. 401; asymptotic form in Definition 10.4,
pp. 402–403). Section 10.2.1 and Figure 10.1 (pp. 401–402) construct an anonymous two-party
key-exchange protocol from any trapdoor function scheme: Alice samples `(pk, sk) ← G()` and sends
`pk`; Bob samples `x ← X` uniformly, sends `y ← F(pk, x)` and outputs `x`; Alice outputs
`I(sk, y)`. Section 10.2.1 (p. 402) shows that for a correct scheme, one-wayness
(`TrapdoorFunction.OneWay`) implies key-guessing security (`KeyExchange.AnonKESecure`), since any
key-guessing adversary directly breaks one-wayness with the exact same advantage; we also prove the
converse direction, which is original here and immediate because the two adversary conversions are
mutually inverse, giving the equivalence `keyExchange_anonKESecure_iff_oneWay`. The RSA
instantiation (§10.3 and §10.3.1) is in
`CslibFrontier/Crypto/Computational/TrapdoorFunction/RSA.lean`.

## Main definitions

* `Cslib.Crypto.TrapdoorFunction`, `Cslib.Crypto.TrapdoorFunction.Correct`: trapdoor function
  schemes with key-dependent domain `X pk` and range `Y pk`, and their inversion correctness
  ([BonehShoup2023], Definition 10.2, pp. 400–401).
* `Cslib.Crypto.TrapdoorFunction.Transcript`, `Cslib.Crypto.TrapdoorFunction.encTranscript`:
  public pairs `(pk, y)` and their framed tuple encoding.
* `Cslib.Crypto.TrapdoorFunction.Inverter`, `Cslib.Crypto.TrapdoorFunction.Inverter.IsPPT`,
  `Cslib.Crypto.TrapdoorFunction.owGame`, `Cslib.Crypto.TrapdoorFunction.OneWay`: typed inverters,
  their uniform strict-PPT predicate, Attack Game 10.2 and one-wayness ([BonehShoup2023], p. 401
  and pp. 402–403).
* `Cslib.Crypto.TrapdoorFunction.keyExchangeExecution`,
  `Cslib.Crypto.TrapdoorFunction.keyExchange`: the Figure 10.1 anonymous key-exchange protocol
  ([BonehShoup2023], Section 10.2.1, pp. 401–402).
* `Cslib.Crypto.TrapdoorFunction.keGuesserToInverter`,
  `Cslib.Crypto.TrapdoorFunction.inverterToKEGuesser`: mutually inverse conversions between
  key-guessing adversaries against `keyExchange` and `Inverter`s (with PPT preservation
  `Cslib.Crypto.TrapdoorFunction.isPPT_keGuesserToInverter` and
  `Cslib.Crypto.TrapdoorFunction.isPPT_inverterToKEGuesser`).

## Main results

* `Cslib.Crypto.TrapdoorFunction.keyExchange_correct`: `keyExchange T` is `KeyExchange.Correct`
  when every `T n` is `Correct` ([BonehShoup2023], Section 10.2.1, p. 402).
* `Cslib.Crypto.TrapdoorFunction.Correct.anonKEGame_keyExchange`: for a `Correct` scheme,
  `anonKEGame` on `keyExchange T` with `adversary` equals `owGame` on `T n` with
  `keGuesserToInverter adversary n` ([BonehShoup2023], Section 10.2.1, p. 402).
* `Cslib.Crypto.TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay`: for a `Correct` family `T`,
  `keyExchange T` satisfies `AnonKESecure` if and only if `T` satisfies `OneWay` (the
  `OneWay → AnonKESecure` direction is [BonehShoup2023], Section 10.2.1, p. 402; the converse is
  original here via `inverterToKEGuesser`).

## Implementation notes

* **Key-dependent domain and range:** [BonehShoup2023], Definition 10.2 (p. 400), fixes two sets
  `X` and `Y`, then notes in Section 10.3 (pp. 404–405) that RSA requires sets indexed by the
  public key (`Fin pk.N`) and leaves that generalization unstated. Here `X Y : PK → Type` are
  key-dependent throughout, so `rsaTrapdoor` is a direct instance without auxiliary wrappers;
  constant families `fun _ => X₀` recover Definition 10.2 verbatim.
* **Key distribution and `domain_nonempty`:** `keyGen : PMF SK` represents the key law directly
  (matching `RSAGen`, `PrimeOrderGroupFamily` setup laws and `KeyExchange.execute`), and
  `publicKey : SK → PK` projects the public key (a pair-outputting generator `G` corresponds to
  `SK = PK × SK₀` with `publicKey = Prod.fst`). `domain_nonempty` requires `X (publicKey sk)` to
  be nonempty for keys `sk : SK`, rather than at arbitrary malformed `pk : PK` (such as RSA's
  `N = 0`). `owGame` and `keyExchangeExecution` take `[∀ pk, Fintype (X pk)]`.
* **Unbundled correctness and honest-party efficiency:** `Correct` is unbundled from
  `TrapdoorFunction`, matching `KeyExchange.Correct`. Moreover, Definition 10.4's items 1–5
  (pp. 402–403)—efficient recognizability and sampleability of `X`, efficient recognizability of
  `Y`, and polynomial-time algorithms `G`, `F`, `I`—are not bundled here and remain tracked under
  #5657.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.2 (Definitions 10.2–10.4, Attack Game 10.2, Section 10.2.1, Figure 10.1,
  pp. 400–403) and Section 10.3 (key-dependent domain remark, pp. 404–405).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped Cslib.Probability.PMF

/-- A trapdoor function scheme `(G, F, I)` ([BonehShoup2023], Section 10.2, Definition 10.2,
pp. 400–401) with public keys `PK`, secret keys `SK`, and key-dependent domain `X pk` and range
`Y pk` (Section 10.3, pp. 404–405). -/
structure TrapdoorFunction (PK SK : Type) (X Y : PK → Type) where
  /-- Key-generation distribution `G` over secret keys. -/
  keyGen : PMF SK
  /-- The public key determined by a secret key. -/
  publicKey : SK → PK
  /-- Evaluation `F(pk, ·)` on the domain of `pk`. -/
  eval : (pk : PK) → X pk → Y pk
  /-- Trapdoor inversion `I(sk, ·)` recovering an element of `X (publicKey sk)`. -/
  invert : (sk : SK) → Y (publicKey sk) → X (publicKey sk)
  /-- Every public key arising from a secret key has a nonempty domain. -/
  domain_nonempty : ∀ sk, Nonempty (X (publicKey sk))

namespace TrapdoorFunction

section Correctness

/-- Inversion correctness ([BonehShoup2023], Section 10.2, Definition 10.2, p. 401):
`I(sk, F(pk, x)) = x` for every secret key in the support of `keyGen` and every `x` in the
domain. -/
@[expose]
def Correct {PK SK : Type} {X Y : PK → Type} (T : TrapdoorFunction PK SK X Y) : Prop :=
  ∀ sk ∈ T.keyGen.support, ∀ x, T.invert sk (T.eval (T.publicKey sk) x) = x

/-- For a `Correct` trapdoor function scheme, `F(pk, ·)` is injective for every `sk` in the
support of `keyGen` ([BonehShoup2023], Section 10.2, p. 401). -/
theorem Correct.injective {PK SK : Type} {X Y : PK → Type} {T : TrapdoorFunction PK SK X Y}
    (h : T.Correct) {sk : SK} (hsk : sk ∈ T.keyGen.support) :
    Function.Injective (T.eval (T.publicKey sk)) :=
  Function.LeftInverse.injective (h sk hsk)

end Correctness

/-- The public pair `(pk, y)` seen by an inverter in Attack Game 10.2 and by a passive
eavesdropper in Figure 10.1 ([BonehShoup2023], Section 10.2 and Section 10.2.1, pp. 401–402). -/
structure Transcript (PK : Type) (Y : PK → Type) where
  /-- Alice's public key `pk`. -/
  publicKey : PK
  /-- The image `y = F(pk, x)` under `publicKey`. -/
  ciphertext : Y publicKey

section TranscriptEncoding

variable {PK : Type} {Y : PK → Type}

/-- The encoding of a trapdoor-function `Transcript`: framed `encPK publicKey` followed by
`encY publicKey ciphertext` (`encTranscript_apply`). -/
enc_structure encTranscript (encPK : PK ↪ List Bool)
    (encY : (pk : PK) → Y pk ↪ List Bool) : Transcript PK Y where
  publicKey : encPK, ciphertext : (encY publicKey) using ((encY publicKey).injective)

end TranscriptEncoding

/-- A typed inverter for Attack Game 10.2 ([BonehShoup2023], Section 10.2, p. 401, with security
parameter `n` as in Definition 10.4, pp. 402–403): given `n`, a public key `pk` and `y : Y pk`,
it outputs a candidate preimage in `X pk`. -/
abbrev Inverter (PK : Type) (X Y : PK → Type) : Type :=
  ℕ → (pk : PK) → Y pk → ProbComp (X pk)

section Inverter

variable {PK : Type} {X Y : PK → Type}

/-- An inverter is PPT when one uniform strict PPT machine reads `(1ⁿ, pk, y)` encoded by
`encPair encUnary (encTranscript encPK encY)` and writes `encX pk x'`. -/
@[expose]
def Inverter.IsPPT (encPK : PK ↪ List Bool) (encX : (pk : PK) → X pk ↪ List Bool)
    (encY : (pk : PK) → Y pk ↪ List Bool) (inverter : Inverter PK X Y) : Prop :=
  IsPPTOn (encPair encUnary (encTranscript encPK encY)) encBits fun input =>
    encX input.2.publicKey <$> inverter input.1 input.2.publicKey input.2.ciphertext

/-- View a key-guessing adversary against trapdoor-function key exchange as an `Inverter` in
Attack Game 10.2 ([BonehShoup2023], Section 10.2.1, p. 402). -/
@[expose]
def keGuesserToInverter
    (adversary : KeyExchange.KeyGuesser (Transcript PK Y) (fun t => X t.publicKey)) :
    Inverter PK X Y :=
  fun n pk y => adversary n ⟨pk, y⟩

/-- View an `Inverter` in Attack Game 10.2 as a key-guessing adversary against trapdoor-function
key exchange (the inverse of `keGuesserToInverter`, added here for the converse direction of
`keyExchange_anonKESecure_iff_oneWay`). -/
@[expose]
def inverterToKEGuesser (inverter : Inverter PK X Y) :
    KeyExchange.KeyGuesser (Transcript PK Y) (fun t => X t.publicKey) :=
  fun n t => inverter n t.publicKey t.ciphertext

/-- `keGuesserToInverter` preserves uniform strict PPT efficiency. -/
theorem isPPT_keGuesserToInverter {encPK : PK ↪ List Bool}
    {encX : (pk : PK) → X pk ↪ List Bool} {encY : (pk : PK) → Y pk ↪ List Bool}
    {adversary : KeyExchange.KeyGuesser (Transcript PK Y) (fun t => X t.publicKey)}
    (hA : adversary.IsPPT (encTranscript encPK encY) (fun t => encX t.publicKey)) :
    (keGuesserToInverter adversary).IsPPT encPK encX encY :=
  hA

/-- `inverterToKEGuesser` preserves uniform strict PPT efficiency. -/
theorem isPPT_inverterToKEGuesser {encPK : PK ↪ List Bool}
    {encX : (pk : PK) → X pk ↪ List Bool} {encY : (pk : PK) → Y pk ↪ List Bool}
    {inverter : Inverter PK X Y} (hI : inverter.IsPPT encPK encX encY) :
    (inverterToKEGuesser inverter).IsPPT (encTranscript encPK encY)
      (fun t => encX t.publicKey) :=
  hI

end Inverter

section SecurityAndKeyExchange

variable {PK SK : Type} {X Y : PK → Type}

/-- Attack Game 10.2 ([BonehShoup2023], Section 10.2, p. 401): draw `sk ← T.keyGen`, draw `x`
uniformly from `X (T.publicKey sk)`, run `step (T.publicKey sk) (T.eval (T.publicKey sk) x)` and
accept when its output equals `x`. Its advantage `OWadv[A, T]` is
`(T.owGame (A n)).succProbability`. -/
@[expose]
noncomputable def owGame [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    (T : TrapdoorFunction PK SK X Y) (step : (pk : PK) → Y pk → ProbComp (X pk)) : Game := do
  let sk ← T.keyGen
  have := T.domain_nonempty sk
  let x ← PMF.uniformOfFintype (X (T.publicKey sk))
  let x' ← ProbComp.eval (step (T.publicKey sk) (T.eval (T.publicKey sk) x))
  return decide (x' = x)

/-- One-wayness of a family of trapdoor function schemes ([BonehShoup2023], Section 10.2,
Attack Game 10.2 and Definition 10.3, p. 401, with Definition 10.4, pp. 402–403): every PPT
inverter recovers a uniform preimage from `(pk, F(pk, x))` with negligible probability.

Deviations from the source: the domain `X pk` and range `Y pk` may depend on the public key
(the form Section 10.3 names for RSA and does not adopt, pp. 404–405); keys come from any
`PMF SK` family without bundling the efficient recognizability, sampleability or polynomial-time
`G`, `F`, `I` conditions of Definition 10.4, items 1–5 (#5657); and inverters are uniform strict
PPT machines reading `(1ⁿ, pk, y)` via `encPair encUnary (encTranscript encPK encY)` and writing
`encX pk x`. -/
@[expose]
def OneWay [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    (T : ℕ → TrapdoorFunction PK SK X Y) (encPK : PK ↪ List Bool)
    (encX : (pk : PK) → X pk ↪ List Bool) (encY : (pk : PK) → Y pk ↪ List Bool) : Prop :=
  ∀ inverter : Inverter PK X Y, inverter.IsPPT encPK encX encY →
    Negligible fun n => Game.succProbability ((T n).owGame (inverter n))

/-! ### Anonymous key exchange from a trapdoor function scheme -/

/-- Honest execution of anonymous key exchange using a trapdoor function scheme `T`
([BonehShoup2023], Section 10.2.1 and Figure 10.1, pp. 401–402): Alice draws `sk ← T.keyGen` and
sends `pk = T.publicKey sk`; Bob draws `x` uniformly from `X pk`, computes `y = T.eval pk x`,
sends `y` and outputs `x`; Alice computes and outputs `T.invert sk y`. -/
@[expose]
noncomputable def keyExchangeExecution [∀ pk, Fintype (X pk)]
    (T : TrapdoorFunction PK SK X Y) :
    PMF (KeyExchange.Outcome (Transcript PK Y) (fun t => X t.publicKey)) := do
  let sk ← T.keyGen
  have := T.domain_nonempty sk
  let x ← PMF.uniformOfFintype (X (T.publicKey sk))
  let y := T.eval (T.publicKey sk) x
  return { transcript := ⟨T.publicKey sk, y⟩, aliceKey := T.invert sk y, bobKey := x }

/-- Anonymous two-party key exchange built from a family `T` of trapdoor function schemes
([BonehShoup2023], Section 10.2.1 and Figure 10.1, pp. 401–402). -/
@[expose]
noncomputable def keyExchange [∀ pk, Fintype (X pk)]
    (T : ℕ → TrapdoorFunction PK SK X Y) :
    KeyExchange (Transcript PK Y) (fun t => X t.publicKey) :=
  ⟨fun n => (T n).keyExchangeExecution⟩

/-- When every `T n` is `Correct`, Alice's inverted key `I(sk, F(pk, x))` equals Bob's chosen `x`
([BonehShoup2023], Section 10.2.1, p. 402). -/
theorem keyExchange_correct [∀ pk, Fintype (X pk)] {T : ℕ → TrapdoorFunction PK SK X Y}
    (hcorr : ∀ n, (T n).Correct) : (keyExchange T).Correct := by
  intro n outcome h
  simp only [keyExchange, keyExchangeExecution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨sk, hsk, x, -, rfl⟩ := h
  exact hcorr n sk hsk x

/-- For a scheme family `T` that is `Correct` at parameter `n`, running `anonKEGame` on
`keyExchange T` with `adversary` gives the exact same game as running `(T n).owGame` with
`keGuesserToInverter adversary n` ([BonehShoup2023], Section 10.2.1, p. 402). -/
theorem Correct.anonKEGame_keyExchange [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    {T : ℕ → TrapdoorFunction PK SK X Y} {n : ℕ} (hcorr : (T n).Correct)
    (adversary : KeyExchange.KeyGuesser (Transcript PK Y) (fun t => X t.publicKey)) :
    (keyExchange T).anonKEGame adversary n = (T n).owGame (keGuesserToInverter adversary n) := by
  simp only [KeyExchange.anonKEGame, keyExchange, Game.withSetup, keyExchangeExecution, owGame,
    keGuesserToInverter, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  congr 1
  funext x
  rw [hcorr sk hsk x]

/-- **Anonymous key exchange from a correct trapdoor function scheme is key-guessing secure if
and only if the scheme is one-way.**

[BonehShoup2023], Section 10.2.1 (p. 402), proves the `OneWay → AnonKESecure` direction (`mpr`),
observing that any adversary guessing `x` from `(pk, y)` breaks Attack Game 10.2 with the exact
same advantage (`Correct.anonKEGame_keyExchange`). The converse direction (`mp`), and hence the
equivalence, is original here and follows immediately because `keGuesserToInverter` and
`inverterToKEGuesser` are mutually inverse. -/
theorem keyExchange_anonKESecure_iff_oneWay [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    {T : ℕ → TrapdoorFunction PK SK X Y} (hcorr : ∀ n, (T n).Correct)
    (encPK : PK ↪ List Bool) (encX : (pk : PK) → X pk ↪ List Bool)
    (encY : (pk : PK) → Y pk ↪ List Bool) :
    (keyExchange T).AnonKESecure (encTranscript encPK encY) (fun t => encX t.publicKey) ↔
      OneWay T encPK encX encY := by
  constructor
  · intro h inverter hPPT
    have hgame (n : ℕ) : (T n).owGame (inverter n) =
        (keyExchange T).anonKEGame (inverterToKEGuesser inverter) n :=
      ((hcorr n).anonKEGame_keyExchange (inverterToKEGuesser inverter)).symm
    simpa only [hgame] using h (inverterToKEGuesser inverter) (isPPT_inverterToKEGuesser hPPT)
  · intro h adversary hPPT
    simpa only [fun n => (hcorr n).anonKEGame_keyExchange adversary] using
      h (keGuesserToInverter adversary) (isPPT_keGuesserToInverter hPPT)

end SecurityAndKeyExchange

end TrapdoorFunction

end Cslib.Crypto
