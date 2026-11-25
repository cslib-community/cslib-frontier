/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature.Double
public import CslibFrontier.Crypto.Computational.NaorYungUOWHF
public import CslibFrontier.Crypto.Computational.OneWayToSignature
public import CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid
import CslibFrontier.Crypto.Computational.TreeSignature.Security
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Option
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.OptionMatch
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases

/-!
# Target collision-resistant hash-and-sign and stateless signatures from one-way permutations

When hashing messages before signing under a target collision-resistant hash family (UOWHF), placing
a single hash key in the public verification key fails: an adversary seeing `k` in `pk` before
choosing its signing query and forgery could search for full collisions rather than target
collisions. Instead, construction `(13.2)` of [BonehShoup2023], Section 13.2.1 (p. 533) samples a
**fresh hash key `k` inside every signature** and signs the pair `(k, H(k, m))`:

* **Source mapping**: [BonehShoup2023], Section 13.2.1 states construction `(13.2)` and Theorem 13.2
  for extending the message space of an unrestricted many-time EUF-CMA base signature scheme. Here
  `TCRSignature.scheme S H` instantiates the same per-signature fresh-hash-key construction over a
  **one-time** signature scheme `S` (`OneTimeEUFCMA` on fixed-length bit strings) and an
  unrestricted `KeyedHashFamily` `H`, yielding an `IndexedSignatureScheme` of capacity `1` on
  arbitrary-length `List Bool` messages without storing a hash key in `pk`:
  1. Key generation samples `(otvk, otsk) ← S.keyGen (otsParam H n)` at an injective parameter
     `otsParam H n > H.keyLen n + H.digestLen n` (`TreeSignature.coinParam`) and bundles `n` with
     each key (`encPair encUnary encBits`).
  2. Signing `msg` at index `0` samples `k ← {0, 1}^{H.keyLen n}`, pads `(k, H.eval n k msg)` to an
     `otsParam H n`-bit word `otsMsg H n k (H.eval n k msg)`, signs that word under `S.sign otsk` to
     obtain `ots`, and returns `encPair encBits encBits (k, ots)`.
  3. Verification at index `0` checks `k.length == H.keyLen n` and verifies `ots` on
     `otsMsg H n k (H.eval n k msg)` under `otvk`, rejecting every index `u ≥ 1`.

* **Two-branch security reduction (`exists_reduction_indexedEufCmaGame_le`,
  `SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`)**: following the case split in the
  proof of [BonehShoup2023], Theorem 13.2, every valid forgery `(0, m₁, (k', ots'))` against
  `TCRSignature.scheme S H` either:
  1. produces a valid one-time signature `ots'` on an `otsParam H n`-bit word
     `M* = otsMsg H n k' (H.eval n k' m₁)` never signed by `S` (either no valid index-`0` signing
     query occurred, or `M* ≠ otsMsg H n k (H.eval n k m₀)`), winning `S.eufOneTimeGame` via
     `oneTimeForger`; or
  2. satisfies `M* = otsMsg H n k (H.eval n k m₀)` for the unique valid index-`0` signing query
     `m₀ ≠ m₁`, which by injectivity of `otsMsg` on `(H.keyLen n, H.digestLen n)`-bit pairs forces
     `k' = k` and `H.eval n k m₀ = H.eval n k m₁`, winning `targetCollisionGame` via the two-stage
     adversary `tcrAdversary` (`simRun` dry-runs the clocked oracle machine on pre-sampled fair
     coins before `k` is chosen to commit `m₀`, then replays on the same coins once `k` arrives).

* **Upgrading to stateless many-time `EUFCMA` (`OneWay.exists_eufCMA_of_targetCollisionResistant`,
  `OneWayPermutation.exists_eufCMA`)**:
  1. Given `OneWay f` and a target collision-resistant `KeyedHashFamily` `H`, Lamport's scheme
     (`OneWay.exists_oneTimeSignature`) supplies a `OneTimeEUFCMA` base scheme `S`,
     `TCRSignature.scheme S H` gives a capacity-`1` `IndexedEUFCMA` scheme on all `List Bool`,
     `IndexedSignatureScheme.double` upgrades capacity from `1` to `2`, and
     `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay` (`TreeSignature.scheme` with
     PRFs from `OneWay f`) yields a stateless many-time `SignatureScheme` satisfying `EUFCMA`.
  2. Combining `OneWayPermutation.oneWay` with Naor–Yung's target collision-resistant
     `KeyedHashFamily` (`OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`) proves
     that **every one-way permutation implies the existence of a stateless many-time EUF-CMA secure
     digital signature scheme (`OneWayPermutation.exists_eufCMA`)**, with no separate hash-family
     assumption. Both results are steps toward [NaorYung1989], not the cited result: no inspection
     of the primary source is recorded (#5293). Many-time extension to unrestricted `List Bool`
     messages (`WordSignatureScheme`) and instantiation from general `OneWay` functions
     ([Rompel1990]) are proved in
     `CslibFrontier.Crypto.Computational.TCRSignature.ManyTime` and
     `CslibFrontier.Crypto.Computational.Rompel`.

## Main definitions

* `Cslib.Crypto.TCRSignature.otsBudget`, `Cslib.Crypto.TCRSignature.otsParam`,
  `Cslib.Crypto.TCRSignature.otsParamInv`, `Cslib.Crypto.TCRSignature.otsMsg`,
  `Cslib.Crypto.TCRSignature.otsForgeryOf`: injective one-time parameter schedule, fixed-length
  `(k, digest)` message encoding, and fixed-length forgery translator.
* `Cslib.Crypto.TCRSignature.keyDecoder`, `Cslib.Crypto.TCRSignature.sigDecoder`,
  `Cslib.Crypto.TCRSignature.keyGen`, `Cslib.Crypto.TCRSignature.sign`,
  `Cslib.Crypto.TCRSignature.verify`, `Cslib.Crypto.TCRSignature.scheme`: the fresh-key TCR
  hash-and-sign capacity-`1` indexed signature scheme.
* `Cslib.Crypto.TCRSignature.simStep`, `Cslib.Crypto.TCRSignature.simRun`,
  `Cslib.Crypto.TCRSignature.simPkOf`, `Cslib.Crypto.TCRSignature.simWordOf`,
  `Cslib.Crypto.TCRSignature.simFuelOf`: deterministic finite-configuration step, coin-driven run,
  and encoded input/fuel helpers used to commit the first valid signing query before sampling the
  hash key `k` and replay with a reply afterward.
* `Cslib.Crypto.TCRSignature.oneTimeForger`, `Cslib.Crypto.TCRSignature.tcrAdversary`: the one-time
  signature forger and two-stage target-collision adversary.

## Main results

* `Cslib.Crypto.TCRSignature.computableInPolyTime_simRun_comp`: `simRun` is computable in plain
  polynomial time for every finite-control `MultiTapePTM`.
* `Cslib.Crypto.TCRSignature.isOraclePPT_oneTimeForger`,
  `Cslib.Crypto.TCRSignature.isPPT_tcrAdversary`: uniform strict PPT certificates for both
  reductions.
* `Cslib.Crypto.TCRSignature.succProbability_indexedEufCmaGame_le_of_machine`,
  `Cslib.Crypto.TCRSignature.exists_reduction_indexedEufCmaGame_le`: the one-time form of the
  Theorem 13.2 bound, splitting indexed forgeries into one-time signature forgeries and target
  collisions.
* `Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`: `TCRSignature.scheme S H`
  is `IndexedEUFCMA`-secure whenever `S` is `OneTimeEUFCMA` and `H` is target collision-resistant
  (a step: the one-time form of Theorem 13.2, which the source states for many-time schemes).
* `Cslib.Crypto.OneWay.exists_indexedEUFCMA_of_targetCollisionResistant`,
  `Cslib.Crypto.OneWay.exists_eufCMA_of_targetCollisionResistant`: capacity-`2` indexed and
  stateless many-time `EUFCMA` signatures from a one-way function and a target collision-resistant
  `KeyedHashFamily` (the second a step toward [NaorYung1989], Section 4).
* `Cslib.Crypto.OneWayPermutation.exists_eufCMA`: stateless many-time `EUFCMA` signatures from a
  one-way permutation alone.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 13.2.1 (construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534) and Section 14.6.
* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic
  Applications*][NaorYung1989], Sections 2–4.
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990].
-/

public section

namespace Cslib.Crypto

open Probability _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TCRSignature

/-! ### Injective one-time parameter schedule and `(k, digest)` message encoding -/

/-- Total bit budget `H.keyLen n + H.digestLen n` signed under the one-time signature scheme at
security parameter `n`. -/
@[expose]
def otsBudget (H : KeyedHashFamily) (n : ℕ) : ℕ :=
  H.keyLen n + H.digestLen n

/-- Injective one-time signature security parameter strictly above `otsBudget H n`. -/
@[expose]
def otsParam (H : KeyedHashFamily) : ℕ → ℕ :=
  TreeSignature.coinParam (otsBudget H)

/-- Polynomial-time bounded-search left inverse of `otsParam H`. -/
@[expose]
def otsParamInv (H : KeyedHashFamily) : ℕ → ℕ :=
  TreeSignature.coinParamInv (otsBudget H)

theorem le_otsParam (H : KeyedHashFamily) (n : ℕ) : n ≤ otsParam H n :=
  TreeSignature.le_coinParam (otsBudget H) n

theorem otsBudget_lt_otsParam (H : KeyedHashFamily) (n : ℕ) :
    otsBudget H n < otsParam H n :=
  TreeSignature.lt_coinParam (otsBudget H) n

@[simp]
theorem otsParamInv_otsParam (H : KeyedHashFamily) (n : ℕ) :
    otsParamInv H (otsParam H n) = n :=
  TreeSignature.coinParamInv_coinParam (otsBudget H) n

theorem computableInPolyTime_otsBudget (H : KeyedHashFamily) :
    ComputableInPolyTime (otsBudget H) encUnary encUnary :=
  H.keyLen_polyTime.unary_add' H.digestLen_polyTime

theorem computableInPolyTime_otsParam (H : KeyedHashFamily) :
    ComputableInPolyTime (otsParam H) encUnary encUnary :=
  TreeSignature.computableInPolyTime_coinParam (computableInPolyTime_otsBudget H)

theorem computableInPolyTime_otsParamInv (H : KeyedHashFamily) :
    ComputableInPolyTime (otsParamInv H) encUnary encUnary :=
  TreeSignature.computableInPolyTime_coinParamInv (computableInPolyTime_otsBudget H)

attribute [local fun_prop] computableInPolyTime_otsBudget computableInPolyTime_otsParam
  computableInPolyTime_otsParamInv

/-- Encode `(k, d)` as an exact `otsParam H n`-bit word by concatenating the `H.keyLen n`-bit fixed
view of `k`, the `H.digestLen n`-bit fixed view of `d`, and `otsParam H n - otsBudget H n` trailing
`false` bits. -/
@[expose]
def otsMsg (H : KeyedHashFamily) (n : ℕ) (k d : List Bool) : List Bool :=
  BitString.listRow (H.keyLen n) 0 k ++
    BitString.listRow (H.digestLen n) 0 d ++
    List.replicate (otsParam H n - otsBudget H n) false

@[simp]
theorem length_otsMsg (H : KeyedHashFamily) (n : ℕ) (k d : List Bool) :
    (otsMsg H n k d).length = otsParam H n := by
  have := otsBudget_lt_otsParam H n
  simp only [otsMsg, otsBudget, List.length_append, BitString.length_listRow,
    List.length_replicate] at this ⊢
  omega

theorem otsMsg_inj (H : KeyedHashFamily) {n : ℕ} {k₁ d₁ k₂ d₂ : List Bool}
    (hk₁ : k₁.length = H.keyLen n) (hd₁ : d₁.length = H.digestLen n)
    (hk₂ : k₂.length = H.keyLen n) (hd₂ : d₂.length = H.digestLen n)
    (heq : otsMsg H n k₁ d₁ = otsMsg H n k₂ d₂) :
    k₁ = k₂ ∧ d₁ = d₂ := by
  simp only [otsMsg, BitString.listRow, Nat.zero_mul, List.drop_zero, List.take_left' hk₁,
    List.take_left' hd₁, List.take_left' hk₂, List.take_left' hd₂] at heq
  exact List.append_inj (List.append_inj_left heq (by simp [hk₁, hd₁, hk₂, hd₂]))
    (hk₁.trans hk₂.symm)

theorem computableInPolyTime_otsMsg_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {k d : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hd : ComputableInPolyTime d input encBits) :
    ComputableInPolyTime (fun a => otsMsg H (n a) (k a) (d a)) input encBits := by
  polytime [otsMsg]

/-- Compose `otsMsg H` with `H.eval` in polynomial time. -/
theorem computableInPolyTime_otsMsg_eval_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {k msg : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime
      (fun a => otsMsg H (n a) (k a) (H.eval (n a) (k a) (msg a))) input encBits :=
  computableInPolyTime_otsMsg_comp H hn hk ((hn.prod (hk.prod hmsg)).trans H.polyTime)

attribute [local fun_prop] computableInPolyTime_otsMsg_eval_comp

/-! ### The capacity-`1` fresh-key TCR hash-and-sign scheme -/

/-- Total decoder for `(n, key)` words encoded with `encPair encUnary encBits`. -/
@[expose]
def keyDecoder : Decoder (encPair encUnary encBits) :=
  Decoder.unary.pair Decoder.bits

/-- Total decoder for `(k, ots)` signature words encoded with `encPair encBits encBits`. -/
@[expose]
def sigDecoder : Decoder (encPair encBits encBits) :=
  Decoder.bits.pair Decoder.bits

/-- Translate a `(msg, sig)` word pair at parameter `n` into the underlying fixed-length
`(otsMsg H n k (H.eval n k msg), ots)` forgery candidate for `S`. -/
@[expose]
def otsForgeryOf (H : KeyedHashFamily) (n : ℕ) (msg sig : List Bool) :
    List Bool × List Bool :=
  let parsedSig := sigDecoder.decode sig
  (otsMsg H n parsedSig.1 (H.eval n parsedSig.1 msg), parsedSig.2)

theorem computableInPolyTime_otsForgeryOf_comp (H : KeyedHashFamily) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {msg sig : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hmsg : ComputableInPolyTime msg input encBits)
    (hsig : ComputableInPolyTime sig input encBits) :
    ComputableInPolyTime
      (fun a => otsForgeryOf H (n a) (msg a) (sig a))
      input (encPair encBits encBits) := by
  have hparsed := hsig.trans sigDecoder.computableInPolyTime
  exact ((computableInPolyTime_otsMsg_eval_comp H hn hparsed.fst' hmsg).prod
    hparsed.snd').of_enc_eq fun _ => rfl

attribute [local fun_prop] computableInPolyTime_otsForgeryOf_comp

/-- Sample a one-time key pair `(otvk, otsk) ← S.keyGen (otsParam H n)` and bundle `n` with each
half via `encPair encUnary encBits`. -/
@[expose]
def keyGen (S : SignatureScheme) (H : KeyedHashFamily) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let keys ← S.keyGen (otsParam H n)
  return (encPair encUnary encBits (n, keys.1), encPair encUnary encBits (n, keys.2))

/-- Sign `msg` at index `0` by sampling a fresh `H.keyLen n`-bit key `k`, signing
`otsMsg H n k (H.eval n k msg)` under `S.sign`, and returning `encPair encBits encBits (k, ots)`.
Returns `[]` for every index `u ≥ 1`. -/
@[expose]
noncomputable def sign (S : SignatureScheme) (H : KeyedHashFamily) (sk : List Bool) (u : ℕ)
    (msg : List Bool) : ProbComp (List Bool) :=
  let parsed := keyDecoder.decode sk
  if u = 0 then do
    let k ← BitString.sampleList (H.keyLen parsed.1)
    let ots ← S.sign parsed.2 (otsMsg H parsed.1 k (H.eval parsed.1 k msg))
    return encPair encBits encBits (k, ots)
  else
    pure []

/-- Verify `sig` on `msg` at index `u` under `pk`: require `u == 0`, `k.length == H.keyLen n`, and
`S.verify otvk (otsMsg H n k (H.eval n k msg)) ots`. -/
@[expose]
def verify (S : SignatureScheme) (H : KeyedHashFamily) (pk : List Bool) (u : ℕ)
    (msg sig : List Bool) : Bool :=
  let parsedPk := keyDecoder.decode pk
  let parsedSig := sigDecoder.decode sig
  (u == 0) && (parsedSig.1.length == H.keyLen parsedPk.1) &&
    S.verify parsedPk.2
      (otsMsg H parsedPk.1 parsedSig.1 (H.eval parsedPk.1 parsedSig.1 msg))
      parsedSig.2

theorem keyGen_ppt (S : SignatureScheme) (H : KeyedHashFamily) :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen S H) := by
  ppt [keyGen]

theorem sign_ppt (S : SignatureScheme) (H : KeyedHashFamily) :
    IsPPTOn encIndexedSignInput encBits
      (fun p => sign S H p.1 p.2.1 p.2.2) := by
  ppt [sign]

theorem verify_polyTime (S : SignatureScheme) (H : KeyedHashFamily) :
    ComputableInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => verify S H p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits encIndexedSignedMessage) encBool := by
  polytime [verify]

theorem verify_sign (S : SignatureScheme) (H : KeyedHashFamily)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (keyGen S H n)).support)
    (u : ℕ) (hu : u < 1) (msg sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (sign S H keys.2 u msg)).support) :
    verify S H keys.1 u msg sig = true := by
  obtain rfl : u = 0 := by omega
  supp_cases hkeys [keyGen] with ⟨otKeys, hotKeys, rfl⟩
  supp_cases hsig [sign, keyDecoder.decode_enc, BitString.eval_sampleList] with
    ⟨k, hk, ots, hots, rfl⟩
  have hv := S.verify_sign (otsParam H n) otKeys hotKeys _ (length_otsMsg H n k _) ots hots
  simp only [verify, keyDecoder.decode_enc, sigDecoder.decode_enc, beq_self_eq_true,
    BitString.length_of_mem_support_uniformList hk, hv, Bool.and_self]

/-- **Fresh-key TCR hash-and-sign capacity-`1` indexed signature scheme** ([BonehShoup2023],
Section 13.2.1, construction `(13.2)` instantiated over a one-time signature scheme `S` and an
unrestricted `KeyedHashFamily` `H`): signs arbitrary-length `List Bool` messages at index `0` by
sampling a fresh hash key `k` per signature and signing `(k, H.eval n k msg)` under `S` at
`otsParam H n`. -/
@[expose]
noncomputable def scheme (S : SignatureScheme) (H : KeyedHashFamily) : IndexedSignatureScheme where
  capacity _ := 1
  keyGen := keyGen S H
  sign := sign S H
  verify := verify S H
  capacity_polyTime := ComputableInPolyTime.const 1
  keyGen_ppt := keyGen_ppt S H
  sign_ppt := sign_ppt S H
  verify_polyTime := verify_polyTime S H
  verify_sign := verify_sign S H

/-- `scheme S H` has capacity `1` at every security parameter. -/
@[simp] theorem scheme_capacity (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).capacity = fun _ => 1 := rfl

/-- Key generation of `scheme S H` is `keyGen S H`. -/
@[simp] theorem scheme_keyGen (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).keyGen = keyGen S H := rfl

/-- Signing of `scheme S H` is `sign S H`. -/
@[simp] theorem scheme_sign (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).sign = sign S H := rfl

/-- Verification of `scheme S H` is `verify S H`. -/
@[simp] theorem scheme_verify (S : SignatureScheme) (H : KeyedHashFamily) :
    (scheme S H).verify = verify S H := rfl

/-! ### Deterministic coin-driven simulator for capacity-`1` indexed runs -/

section Simulator

theorem computableInPolyTime_finiteConfig_reqWord {k : ℕ} {Control α : Type} [Finite Control]
    {encIn : α ↪ List Bool} {cfg : α → FiniteConfig k Bool Control Unit}
    (hcfg : ComputableInPolyTime cfg encIn encFiniteConfig) :
    ComputableInPolyTime (fun a => ((cfg a).channels ()).1) encIn encBits :=
  ((ComputableInPolyTime.pi_apply (encPair encBits (encBiTape encBool)) ()).comp
    (ComputableInPolyTime.finiteConfig_channels.comp hcfg)).fst'

attribute [local fun_prop] computableInPolyTime_finiteConfig_reqWord

/-- Finite-tag transition dispatch on `FiniteConfig`: given polynomial-time projections for a
`FiniteConfig` `cfg` and a coin `coin`, plus polynomial-time handlers for the halted branch, each
`(action, symbol, move)` step branch, and each `next` query branch, the full transition is
computable in polynomial time. -/
theorem computableInPolyTime_finiteConfig_cases {k : ℕ} {Control α β : Type} [Finite Control]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {cfg : α → FiniteConfig k Bool Control Unit}
    {coin : α → Bool}
    (hcfg : ComputableInPolyTime cfg encIn encFiniteConfig)
    (hcoin : ComputableInPolyTime coin encIn encBool)
    {onHalt : α → β}
    (hHalt : ComputableInPolyTime onHalt encIn encOut)
    {onStep : Action k Bool Control → (Unit → Option Bool) → (Unit → SignType) → α → β}
    (hStep : ∀ action symbol move,
      ComputableInPolyTime (onStep action symbol move) encIn encOut)
    {onQuery : Control → α → β}
    (hQuery : ∀ next, ComputableInPolyTime (onQuery next) encIn encOut) :
    ComputableInPolyTime
      (fun a =>
        match (cfg a).tapes.state with
        | none => onHalt a
        | some state =>
          match machine.tr state (cfg a).tapes.inputSymbol (cfg a).tapes.workTapeSymbols
              (cfg a).answerSymbols (coin a) with
          | .step action symbol move => onStep action symbol move a
          | .query () next => onQuery next a)
      encIn encOut := by
  refine (ComputableInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite (Option Control))
      (encPair (encFinEnum (Option Bool))
        (encPair (encFinEnum (Fin k → Option Bool))
          (encPair (encFinite (Unit → Option Bool)) encBool))))
    (tag := fun a => ((cfg a).tapes.state, (cfg a).tapes.inputSymbol,
      (cfg a).tapes.workTapeSymbols, (cfg a).answerSymbols, coin a))
    (branch := fun choice a =>
      match choice.1 with
      | none => onHalt a
      | some state =>
        match machine.tr state choice.2.1 choice.2.2.1 choice.2.2.2.1 choice.2.2.2.2 with
        | .step action symbol move => onStep action symbol move a
        | .query () next => onQuery next a)
    (by fun_prop) ?_).of_enc_eq fun _ => rfl
  rintro ⟨_ | state, inSym, workSyms, ansSyms, coinVal⟩
  · exact hHalt
  · dsimp only
    rcases machine.tr state inSym workSyms ansSyms coinVal with
      ⟨action, symbol, move⟩ | ⟨⟨⟩, next⟩
    · exact hStep action symbol move
    · exact hQuery next

/-- One deterministic transition of `machine` on finite storage `(cfg, qOpt)` using fair coin `coin`
and pre-supplied `reply` for the **first** query at index `0` (`r.1 == 0 && qOpt.isNone`). Every
other query (`r.1 ≠ 0` or after `qOpt = some m₀`) receives the empty reply `[]`, matching
`indexedSigningOracle` at capacity `1`. -/
def simStep {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (acc : FiniteConfig k Bool Control Unit × Option (List Bool))
    (coin : Bool) : FiniteConfig k Bool Control Unit × Option (List Bool) :=
  match acc.1.tapes.state with
  | none => acc
  | some state =>
    match machine.tr state acc.1.tapes.inputSymbol acc.1.tapes.workTapeSymbols
        acc.1.answerSymbols coin with
    | .step action symbol move => (acc.1.step action symbol move, acc.2)
    | .query () next =>
      let r := IndexedSignatureScheme.requestDecoder.decode (acc.1.channels ()).1
      if r.1 == 0 && acc.2.isNone then
        (acc.1.receive () next reply, some r.2)
      else
        (acc.1.receive () next [], acc.2)

/-- Run `machine` deterministically on `word` over `coins` using `reply` for the first valid
index-`0` signing query, returning `(finalOutput, recordedQuery)`. -/
def simRun {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (word reply coins : List Bool) : List Bool × Option (List Bool) :=
  let final := coins.foldl (simStep machine reply) (FiniteConfig.init machine.initial word, none)
  (final.1.tapes.output, final.2)

private theorem computableInPolyTime_simStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun q : (List Bool × (FiniteConfig k Bool Control Unit × Option (List Bool))) × Bool =>
        simStep machine q.1.1 q.1.2 q.2)
      (encPair
        (encPair encBits (encPair encFiniteConfig (encOption encBits)))
        encBool)
      (encPair encFiniteConfig (encOption encBits)) := by
  unfold simStep
  refine (computableInPolyTime_finiteConfig_cases machine (by fun_prop) (by fun_prop)
    (by fun_prop) (fun _ _ _ => by fun_prop) (fun _ => ?_)).of_enc_eq fun _ => rfl
  have := IndexedSignatureScheme.requestDecoder.computableInPolyTime
  simp only [← Option.not_isSome]
  polytime

private theorem computableInPolyTime_simRun_raw {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => simRun machine p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits))
      (encPair encBits (encOption encBits)) := by
  obtain ⟨cCfg, hcCfg⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let inv (p : List Bool × List Bool × List Bool) (consumed : List Bool)
      (acc : FiniteConfig k Bool Control Unit × Option (List Bool)) : Prop :=
    FiniteConfig.SpaceBound p.1.length consumed.length p.2.1.length acc.1 ∧
      ∀ m₀, acc.2 = some m₀ → m₀.length ≤ consumed.length
  have hfold := (ComputableInPolyTime.foldlWith_spec
    (encIn := encPair encBits (encPair encBits encBits))
    (encP := encBits) (encA := encBool) (encL := encBits)
    (encB := encPair encFiniteConfig (encOption encBits))
    (par := fun p => p.2.1) (list := fun p => p.2.2)
    (init := fun p => (FiniteConfig.init machine.initial p.1, none))
    (step := simStep machine)
    (by fun_prop) (by fun_prop) (by fun_prop) (computableInPolyTime_simStep machine)
    inv
    (fun p => ⟨FiniteConfig.spaceBound_init machine.initial p.1 p.2.1.length,
      by rintro _ ⟨⟩⟩)
    (fun p consumed ⟨cfg, qOpt⟩ coin _ ⟨hcfg, hq⟩ => by
      dsimp only [inv, simStep] at hcfg hq ⊢
      simp only [List.length_append, List.length_singleton]
      have hq' : ∀ m₀, qOpt = some m₀ → m₀.length ≤ consumed.length + 1 :=
        fun m₀ hm => (hq m₀ hm).trans (Nat.le_succ _)
      cases cfg.tapes.state with
      | none => exact ⟨hcfg.mono le_rfl (Nat.le_succ _) le_rfl, hq'⟩
      | some state =>
        dsimp only
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move => exact ⟨hcfg.step action symbol move, hq'⟩
        | query ch next =>
          cases ch
          dsimp only
          split_ifs
          · refine ⟨hcfg.receive () next p.2.1 le_rfl, ?_⟩
            rintro _ ⟨rfl⟩
            have hdrop :
                (IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1).2.length ≤
                  ((cfg.channels ()).1).length := by
              simpa only [IndexedSignatureScheme.requestDecoder, Decoder.pair, Decoder.bits,
                id_eq] using length_dropFrame_le (cfg.channels ()).1
            exact (hdrop.trans (hcfg.query ())).trans (Nat.le_succ _)
          · exact ⟨hcfg.receive () next [] (Nat.zero_le _), hq'⟩)
    (size := fun p => (2 * cCfg + 2) * (p.1.length + p.2.2.length + p.2.1.length + 1) + 2)
    (ComputableInPolyTime.polyBounded (by fun_prop))
    (fun ⟨w, r, cs⟩ consumed ⟨cfg, qOpt⟩ hpre ⟨hcfg, hq⟩ => by
      dsimp only [inv] at hpre hcfg hq ⊢
      have hlenPre : consumed.length ≤ cs.length := hpre.length_le
      have hcfgLen : (encFiniteConfig cfg).length ≤
          cCfg * (w.length + cs.length + r.length + 1) :=
        (hcCfg w.length consumed.length r.length cfg hcfg).trans
          (Nat.mul_le_mul_left cCfg (by omega))
      have hcfgLen2 := Nat.mul_le_mul_left 2 hcfgLen
      rw [← Nat.mul_assoc] at hcfgLen2
      rcases qOpt with _ | m₀
      · enc_len [Nat.add_mul]
      · have := (hq m₀ rfl).trans hlenPre
        enc_len [Nat.add_mul])).1
  have hout : ComputableInPolyTime
      (fun acc : FiniteConfig k Bool Control Unit × Option (List Bool) =>
        (acc.1.tapes.output, acc.2))
      (encPair encFiniteConfig (encOption encBits))
      (encPair encBits (encOption encBits)) := by fun_prop
  exact (hfold.trans hout).of_enc_eq fun _ => rfl

/-- `simRun` is computable in plain polynomial time for every finite-control `MultiTapePTM`. -/
theorem computableInPolyTime_simRun_comp {k : ℕ} {Control α : Type} [Finite Control]
    {input : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {word reply coins : α → List Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hreply : ComputableInPolyTime reply input encBits)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime (fun a => simRun machine (word a) (reply a) (coins a))
      input (encPair encBits (encOption encBits)) :=
  ((hword.prod (hreply.prod hcoins)).trans
    (computableInPolyTime_simRun_raw machine)).of_enc_eq fun _ => rfl

/-! ### Exact coupling between `finiteStep` and `simStep` -/

private theorem simStep_some {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (cfg : FiniteConfig k Bool Control Unit) (m₀ : List Bool) (coin : Bool) :
    simStep machine reply (cfg, some m₀) coin =
      ((simStep machine [] (cfg, some m₀) coin).1, some m₀) := by
  dsimp only [simStep]
  rcases cfg.tapes.state with _ | state; · rfl
  dsimp only
  rcases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
      cfg.answerSymbols coin with _ | ⟨⟨⟩, _⟩
  · rfl
  · simp only [Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private theorem simFold_some {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (reply : List Bool) (coins : List Bool) (cfg : FiniteConfig k Bool Control Unit)
    (m₀ : List Bool) :
    coins.foldl (simStep machine reply) (cfg, some m₀) =
      coins.foldl (simStep machine []) (cfg, some m₀) ∧
    (coins.foldl (simStep machine []) (cfg, some m₀)).2 = some m₀ := by
  induction coins generalizing cfg with
  | nil => exact ⟨rfl, rfl⟩
  | cons coin rest ih =>
    rw [List.foldl_cons, List.foldl_cons, simStep_some machine reply, simStep_some machine []]
    exact ih _

private theorem run_interpret_finiteStep {k : ℕ} {Control State : Type}
    (machine : MultiTapePTM k Bool Control Unit)
    (oracle : Unit × List Bool → State → PMF (List Bool × State))
    (limit : ℕ) (cfg : FiniteConfig k Bool Control Unit) (s : State) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
      (machine.finiteStep
        (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => List.take limit <$> ProbOracleComp.query (op, word)) cfg)).run s =
    match cfg.tapes.state with
    | none => PMF.pure (cfg, s)
    | some state =>
      (PMF.uniformOfFintype Bool).bind fun bit =>
        match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols bit with
        | .step action symbol move => PMF.pure (cfg.step action symbol move, s)
        | .query () next =>
          (oracle ((), (cfg.channels ()).1) s).map fun (ans, s') =>
            (cfg.receive () next (ans.take limit), s') := by
  cases hs : cfg.tapes.state with
  | none =>
    simp only [finiteStep, hs, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure]
  | some state =>
    simp only [finiteStep, hs, bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    congr 1; funext bit
    rcases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with ⟨action, symbol, move⟩ | ⟨⟨⟩, next⟩
    · simp only [OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure]
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_pure,
        ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, _root_.PMF.map]
      rfl

private theorem iterate_finiteStep_from_opt {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit)
    (n : ℕ) (otsk : List Bool) (limit steps : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) (qOpt : Option (List Bool)) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun req s => ProbComp.eval
          ((scheme S H).indexedSigningOracle n (encPair encUnary encBits (n, otsk)) req s)))
      (OracleComp.iterate steps
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => List.take limit <$> ProbOracleComp.query (op, word)))
        cfg)).run (qOpt.map (0, ·)).toList =
    (BitString.uniformList steps).bind fun coins =>
      let r0 := coins.foldl (simStep machine []) (cfg, qOpt)
      match qOpt, r0.2 with
      | some m₀, _ => PMF.pure (r0.1, [(0, m₀)])
      | none, none => PMF.pure (r0.1, [])
      | none, some m₀ =>
        (BitString.uniformList (H.keyLen n)).bind fun hashKey =>
          (ProbComp.eval (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey m₀)))).map fun ots =>
            ((coins.foldl (simStep machine ((encPair encBits encBits (hashKey, ots)).take limit))
              (cfg, none)).1, [(0, m₀)]) := by
  induction steps generalizing cfg qOpt with
  | zero => cases qOpt <;> simp [BitString.uniformList_zero, Probability.PMF.monad_pure_eq_pure]
  | succ steps ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, run_interpret_finiteStep,
      BitString.uniformList_succ, PMF.bind_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [PMF.pure_bind, ih cfg qOpt, PMF.bind_map, Function.comp_def, List.foldl_cons,
        simStep, hs, PMF.bind_const]
    | some state =>
      simp only [PMF.bind_bind]
      congr 1; funext bit
      rcases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with ⟨action, symbol, move⟩ | ⟨⟨⟩, next⟩
      · simp only [PMF.pure_bind, ih (cfg.step action symbol move) qOpt, PMF.bind_map,
          Function.comp_def, List.foldl_cons, simStep, hs, htr]
      · let r := IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1
        have hrefuse (s : List (ℕ × List Bool)) (hnot : ¬ (r.1 < 1 ∧ r.1 ∉ s.map Prod.fst)) :
            ProbComp.eval ((scheme S H).indexedSigningOracle n
              (encPair encUnary encBits (n, otsk)) ((), (cfg.channels ()).1) s) =
            PMF.pure ([], s) := by
          simp only [IndexedSignatureScheme.indexedSigningOracle,
            show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
            scheme_capacity, hnot, ↓reduceIte, ProbComp.eval_pure]
        rcases qOpt with _ | m₀
        · simp only [Option.map_none, Option.toList_none]
          by_cases hr0 : r.1 = 0
          · have hq : ProbComp.eval ((scheme S H).indexedSigningOracle n
                (encPair encUnary encBits (n, otsk)) ((), (cfg.channels ()).1) []) =
              (BitString.uniformList (H.keyLen n)).bind fun hashKey =>
                (ProbComp.eval (S.sign otsk (otsMsg H n hashKey (H.eval n hashKey r.2)))).bind
                  fun ots => PMF.pure (encPair encBits encBits (hashKey, ots), [(0, r.2)]) := by
              have hrPair : (0, r.2) = r := Prod.ext hr0.symm rfl
              simp only [IndexedSignatureScheme.indexedSigningOracle,
                show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
                scheme_capacity, scheme_sign, hr0, Nat.zero_lt_one, List.map_nil, List.not_mem_nil,
                not_false_eq_true, and_self, ↓reduceIte, sign, keyDecoder.decode_enc,
                BitString.eval_sampleList, hrPair, pmf_norm]
            have hrhs (cs : List Bool) :
                ((bit :: cs).foldl (simStep machine []) (cfg, none)).2 = some r.2 := by
              simp only [List.foldl_cons, simStep, hs, htr,
                show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
                hr0, beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
              exact (simFold_some machine [] cs (cfg.receive () next []) r.2).2
            have hlhs (hashKey ots cs : List Bool) :
                (cs.foldl (simStep machine [])
                  (cfg.receive () next ((encPair encBits encBits (hashKey, ots)).take limit),
                    some r.2)).1 =
                ((bit :: cs).foldl
                  (simStep machine ((encPair encBits encBits (hashKey, ots)).take limit))
                  (cfg, none)).1 := by
              simp only [List.foldl_cons, simStep, hs, htr,
                show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
                hr0, beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte,
                (simFold_some machine ((encPair encBits encBits (hashKey, ots)).take limit) cs _
                  r.2).1]
            have hih (cfg' : FiniteConfig k Bool Control Unit) := ih cfg' (some r.2)
            simp only [Option.map_some, Option.toList_some] at hih
            rw [hq]
            simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def, hih, hlhs, hrhs,
              _root_.PMF.map]
            pmf_swap
          · rw [hrefuse [] (by simp [hr0])]
            have hih := ih (cfg.receive () next []) none
            simp only [Option.map_none, Option.toList_none] at hih
            simp only [PMF.pure_map, PMF.pure_bind, List.take_nil, hih, PMF.bind_map,
              Function.comp_def, List.foldl_cons, simStep, hs, htr,
              show IndexedSignatureScheme.requestDecoder.decode (cfg.channels ()).1 = r from rfl,
              beq_false_of_ne hr0, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        · simp only [Option.map_some, Option.toList_some]
          rw [hrefuse [(0, m₀)] (by simp)]
          have hih := ih (cfg.receive () next []) (some m₀)
          simp only [Option.map_some, Option.toList_some] at hih
          simp only [PMF.pure_map, PMF.pure_bind, List.take_nil, hih, PMF.bind_map,
            Function.comp_def, List.foldl_cons, simStep, hs, htr, Option.isNone_some,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte]

end Simulator

/-! ### The two reductions: `oneTimeForger` and `tcrAdversary` -/

section Reductions

/-- Total decoder for raw `IndexedForger` outputs `(u, msg, sig)`. -/
@[expose]
def outDecoder : Decoder encIndexedSignedMessage :=
  Decoder.unary.pair (Decoder.bits.pair Decoder.bits)

/-- Total decoder for `tcrAdversary` saved state `(keys, coins)`. -/
@[expose]
def stateDecoder : Decoder (encPair (encPair encBits encBits) encBits) :=
  (Decoder.bits.pair Decoder.bits).pair Decoder.bits

/-- Bundled public key `(n, otvk)` passed to an adversary against `scheme` or `wordScheme`. -/
@[expose]
def simPkOf (n : ℕ) (otvk : List Bool) : List Bool :=
  encPair encUnary encBits (n, otvk)

/-- Encoded machine input `(n, simPkOf n otvk)` for a simulated adversary run. -/
@[expose]
def simWordOf (n : ℕ) (otvk : List Bool) : List Bool :=
  encPair encUnary encBits (n, simPkOf n otvk)

/-- Polynomial step/reply budget `c * ((simWordOf n otvk).length + 1) ^ d` on `(n, otvk)`. -/
@[expose]
def simFuelOf (c d n : ℕ) (otvk : List Bool) : ℕ :=
  c * ((simWordOf n otvk).length + 1) ^ d

/-- One-time signature forger at security parameter `M = otsParam H n`: recovers
`n := otsParamInv H M`, samples coins and a uniform hash key `k`, dry-runs `simRun` on `[]`,
queries its external one-time signing oracle at most once on `otsMsg H n k (H.eval n k m₀)` (with
reply truncated to `sigBound n`), replays `simRun`, and outputs `(otsMsg H n k' (H.eval n k' m₁),
ots')`. -/
noncomputable def oneTimeForger {k : ℕ} {Control : Type}
    (H : KeyedHashFamily) (sigBound : ℕ → ℕ)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) : Forger :=
  fun M otvk =>
    let n := otsParamInv H M
    if otsParam H n = M then do
      let word := simWordOf n otvk
      let fuel := simFuelOf c d n otvk
      let coins ← ProbOracleComp.sample (BitString.sampleList fuel)
      let hashKey ← ProbOracleComp.sample (BitString.sampleList (H.keyLen n))
      let r0 := simRun machine word [] coins
      match r0.2 with
      | none =>
        let (_, msg, sig) := outDecoder.decode r0.1
        return otsForgeryOf H n msg sig
      | some m₀ =>
        let ots ← List.take (sigBound n) <$>
          ProbOracleComp.query ((), otsMsg H n hashKey (H.eval n hashKey m₀))
        let reply := (encPair encBits encBits (hashKey, ots)).take fuel
        let r1 := simRun machine word reply coins
        let (_, msg, sig) := outDecoder.decode r1.1
        return otsForgeryOf H n msg sig
    else
      pure ([], [])

/-- Two-stage target-collision adversary against `H`: `choose n` samples `keys ← S.keyGen
(otsParam H n)` and `coins`, dry-runs `simRun` on `[]` to commit the first valid signing query `m₀`
before `k` is chosen, and saves `(keys, coins)`; `find n state k` signs `(k, H.eval n k m₀)`
locally using `keys.2`, replays `simRun` on the same `coins`, and outputs the forged message `m₁`.
-/
noncomputable def tcrAdversary {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) : TargetCollisionFinder where
  choose n := do
    let keys ← S.keyGen (otsParam H n)
    let word := simWordOf n keys.1
    let fuel := simFuelOf c d n keys.1
    let coins ← BitString.sampleList fuel
    let r0 := simRun machine word [] coins
    return (r0.2.getD [], encPair (encPair encBits encBits) encBits (keys, coins))
  find n stateWord hashKey := do
    let saved := stateDecoder.decode stateWord
    let keys := saved.1
    let coins := saved.2
    let word := simWordOf n keys.1
    let fuel := simFuelOf c d n keys.1
    let r0 := simRun machine word [] coins
    match r0.2 with
    | none =>
      let (_, m₁, _) := outDecoder.decode r0.1
      return m₁
    | some m₀ =>
      let ots ← S.sign keys.2 (otsMsg H n hashKey (H.eval n hashKey m₀))
      let reply := (encPair encBits encBits (hashKey, ots)).take fuel
      let r1 := simRun machine word reply coins
      let (_, m₁, _) := outDecoder.decode r1.1
      return m₁

theorem computableInPolyTime_wordOf {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {pk : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits) :
    ComputableInPolyTime (fun a => simWordOf (n a) (pk a)) input encBits := by
  polytime [simWordOf, simPkOf]

attribute [local fun_prop] computableInPolyTime_wordOf

theorem computableInPolyTime_fuelOf {α : Type} {input : α ↪ List Bool}
    (c d : ℕ) {n : α → ℕ} {pk : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits) :
    ComputableInPolyTime (fun a => simFuelOf c d (n a) (pk a)) input encUnary := by
  polytime [simFuelOf]

attribute [local fun_prop] computableInPolyTime_simRun_comp computableInPolyTime_fuelOf

/-- `oneTimeForger` is uniformly strict oracle PPT whenever `sigBound` is computable in plain
polynomial time on unary `n`. -/
theorem isOraclePPT_oneTimeForger {k : ℕ} {Control : Type} [Finite Control]
    (H : KeyedHashFamily) {sigBound : ℕ → ℕ}
    (hsigBound : ComputableInPolyTime sigBound encUnary encUnary)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) :
    IsOraclePPT (encPair encBits encBits) (oneTimeForger H sigBound machine c d) := by
  apply IsOraclePPTOn.isOraclePPT
  unfold oneTimeForger
  option_match_to_elim
  simp only [Option.elim_eq_if_isSome ([] : List Bool)]
  ppt

/-- Both stages of `tcrAdversary` are uniformly strict PPT. -/
theorem isPPT_tcrAdversary {k : ℕ} {Control : Type} [Finite Control]
    (S : SignatureScheme) (H : KeyedHashFamily)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ) :
    (tcrAdversary S H machine c d).IsPPT where
  choose := by
    ppt [tcrAdversary]
  find := by
    unfold tcrAdversary
    dsimp only
    option_match_to_elim
    simp only [Option.elim_eq_if_isSome ([] : List Bool)]
    ppt

/-! ### Security bound and existential upgrades -/

/-- `verify S H` accepts only at index `0`, below the capacity `1` of `scheme S H`, so the index
guard of the indexed game is redundant for this scheme. -/
private theorem capacity_guard_verify (S : SignatureScheme) (H : KeyedHashFamily) (n u : ℕ)
    (b : Bool) (pk msg sig : List Bool) :
    (decide (u < (scheme S H).capacity n) && b && verify S H pk u msg sig) =
      (b && verify S H pk u msg sig) := by
  cases u with
  | zero => simp
  | succ u => simp [verify]

/-- **Concrete security bound for `TCRSignature.scheme` with an explicit realizing machine**
([BonehShoup2023], Section 13.2.1, Theorem 13.2): at every security parameter `n`, the indexed
forging probability against `scheme S H` is at most the one-time forging probability of
`oneTimeForger` against `S` at `otsParam H n` plus the target-collision probability of
`tcrAdversary` against `H` at `n`. -/
theorem succProbability_indexedEufCmaGame_le_of_machine {k : ℕ} {Control : Type}
    (S : SignatureScheme) (H : KeyedHashFamily)
    (sigBound : ℕ → ℕ)
    (hsigBound : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
      ∀ msg, msg.length = otsParam H n →
      ∀ ots ∈ (ProbComp.eval (S.sign keys.2 msg)).support, ots.length ≤ sigBound n)
    (adversary : IndexedForger)
    (machine : MultiTapePTM k Bool Control Unit) (c d : ℕ)
    (hmachine : ∀ (input : ℕ × List Bool) (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          (encIndexedSignedMessage <$> adversary input.1 input.2)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
          (machine.runOracle
            (c * ((encPair encUnary encBits input).length + 1) ^ d)
            (encPair encUnary encBits input))).run s)
    (n : ℕ) :
    Game.succProbability (ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (S.eufOneTimeGame (oneTimeForger H sigBound machine c d) (otsParam H n))) +
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
            (tcrAdversary S H machine c d) n)) := by
  let pkOf := simPkOf n
  let wordOf := simWordOf n
  let fuelOf := simFuelOf c d n
  let otsDist (keys : List Bool × List Bool) (coins hashKey : List Bool) : PMF (List Bool) :=
    match (simRun machine (wordOf keys.1) [] coins).2 with
    | none => PMF.pure []
    | some m₀ => ProbComp.eval (S.sign keys.2 (otsMsg H n hashKey (H.eval n hashKey m₀)))
  let μ : PMF ((List Bool × List Bool) × List Bool × List Bool × List Bool) := do
    let keys ← ProbComp.eval (S.keyGen (otsParam H n))
    let coins ← BitString.uniformList (fuelOf keys.1)
    let hashKey ← BitString.uniformList (H.keyLen n)
    (otsDist keys coins hashKey).map fun ots => (keys, coins, hashKey, ots)
  let finalOut (keys : List Bool × List Bool) (coins hashKey ots : List Bool) :
      ℕ × List Bool × List Bool :=
    let r0 := simRun machine (wordOf keys.1) [] coins
    match r0.2 with
    | none => outDecoder.decode r0.1
    | some _ =>
      outDecoder.decode
        (simRun machine (wordOf keys.1)
          ((encPair encBits encBits (hashKey, ots)).take (fuelOf keys.1)) coins).1
  let winIdx : (List Bool × List Bool) × List Bool × List Bool × List Bool → Bool :=
    fun (keys, coins, hashKey, ots) =>
      let out := finalOut keys coins hashKey ots
      let signed := ((simRun machine (wordOf keys.1) [] coins).2.map ((0, ·))).toList
      !signed.contains (out.1, out.2.1) && verify S H (pkOf keys.1) out.1 out.2.1 out.2.2
  let winOts : (List Bool × List Bool) × List Bool × List Bool × List Bool → Bool :=
    fun (keys, coins, hashKey, ots) =>
      let out := finalOut keys coins hashKey ots
      let parsedSig := sigDecoder.decode out.2.2
      let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 out.2.1)
      let queried := ((simRun machine (wordOf keys.1) [] coins).2.map
        fun m₀ => otsMsg H n hashKey (H.eval n hashKey m₀)).toList
      (MStar.length == otsParam H n) && !queried.contains MStar && S.verify keys.1 MStar parsedSig.2
  let winTcr : (List Bool × List Bool) × List Bool × List Bool × List Bool → Bool :=
    fun (keys, coins, hashKey, ots) =>
      let m₀ := (simRun machine (wordOf keys.1) [] coins).2.getD []
      let out := finalOut keys coins hashKey ots
      isCollision (H.eval n) (fun _ _ => true) n hashKey m₀ out.2.1
  have hidxEq :
      ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n) = μ.map winIdx := by
    have hdecodeAdv (pk : List Bool) : adversary n pk =
        outDecoder.decode <$> (encIndexedSignedMessage <$> adversary n pk) := by
      simp only [Functor.map_map, outDecoder.decode_enc]
      exact (id_map _).symm
    simp only [IndexedSignatureScheme.indexedEufCmaGame, scheme_keyGen, scheme_verify,
      capacity_guard_verify, keyGen, ProbOracleComp.eval_run_interpret, μ, pmf_norm]
    congr 1; funext keys
    rw [hdecodeAdv (encPair encUnary encBits (n, keys.1)), OracleComp.interpret_map,
      StateT.run_map, _root_.PMF.monad_map_eq_map,
      hmachine (n, encPair encUnary encBits (n, keys.1)) _ _ []]
    erw [← machine.finiteRunFrom_take_runOracle (fuelOf keys.1) (wordOf keys.1)]
    have hiter := iterate_finiteStep_from_opt S H machine n keys.2 (fuelOf keys.1) (fuelOf keys.1)
      (FiniteConfig.init machine.initial (wordOf keys.1)) none
    simp only [Option.map_none, Option.toList_none] at hiter
    simp only [finiteRunFrom, OracleComp.interpret_map, StateT.run_map, hiter, pmf_norm]
    congr 1; funext coins
    dsimp only [otsDist, winIdx, finalOut, simRun, wordOf, pkOf, fuelOf,
      simWordOf, simPkOf, simFuelOf]
    cases ((coins.foldl (simStep machine [])
        (FiniteConfig.init machine.initial
          (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))), none)).2) <;>
      simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
        PMF.bind_const, _root_.PMF.map, pmf_norm]
  have hotsEq :
      ProbComp.eval (S.eufOneTimeGame (oneTimeForger H sigBound machine c d) (otsParam H n)) =
        μ.map winOts := by
    simp only [SignatureScheme.eufOneTimeGame, oneTimeForger, otsParamInv_otsParam, ↓reduceIte,
      BitString.eval_sampleList, μ, fuelOf, runWith_norm, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun keys keys_mem => ?_
    congr 1; funext coins; congr 1; funext hashKey
    dsimp only [otsDist, winOts, finalOut, wordOf, pkOf, fuelOf, simWordOf, simPkOf, simFuelOf,
      otsForgeryOf]
    cases (simRun machine
        (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))) [] coins).2 with
    | none => simp only [Option.map_none, Option.toList_none, runWith_norm, pmf_norm]
    | some m₀ =>
      simp only [Option.map_some, Option.toList_some, SignatureScheme.oneTimeSigningOracle,
        SignatureScheme.oneTimeSigningOracleOn, length_otsMsg, beq_self_eq_true, List.isEmpty_nil,
        Bool.and_self, ↓reduceIte, _root_.PMF.map, runWith_norm, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun ots ots_mem => ?_
      rw [List.take_of_length_le (hsigBound n keys keys_mem _ (length_otsMsg H n hashKey _)
        ots ots_mem)]
  have htcrEq :
      ProbComp.eval
        (targetCollisionGame H.keyLen H.eval (fun _ _ => true)
          (tcrAdversary S H machine c d) n) = μ.map winTcr := by
    simp only [targetCollisionGame, tcrAdversary, BitString.eval_sampleList,
      stateDecoder.decode_enc, μ, fuelOf, pmf_norm]
    congr 1; funext keys; congr 1; funext coins; congr 1; funext hashKey
    dsimp only [otsDist, winTcr, finalOut, wordOf, pkOf, fuelOf, simWordOf, simPkOf, simFuelOf]
    cases (simRun machine
        (encPair encUnary encBits (n, encPair encUnary encBits (n, keys.1))) [] coins).2 <;>
      simp only [_root_.PMF.map, pmf_norm]
  have hpointwise : ∀ sample ∈ μ.support,
      winIdx sample = true → winOts sample = true ∨ winTcr sample = true := by
    intro sample hsupp hwin
    supp_cases hsupp [μ] with ⟨keys, -, coins, -, hashKey, hhk, ots, -, rfl⟩
    have hhkLen := BitString.length_of_mem_support_uniformList hhk
    dsimp only [winIdx, pkOf, simPkOf] at hwin
    simp only [Bool.and_eq_true, Bool.not_eq_true', verify, keyDecoder.decode_enc, Bool.and_assoc,
      beq_iff_eq] at hwin
    obtain ⟨hnotSigned, hu0, hk'Len, hverifyS⟩ := hwin
    let out := finalOut keys coins hashKey ots
    let parsedSig := sigDecoder.decode out.2.2
    let MStar := otsMsg H n parsedSig.1 (H.eval n parsedSig.1 out.2.1)
    dsimp only [winOts, winTcr]
    cases hopt : (simRun machine (wordOf keys.1) [] coins).2 with
    | none => simp [length_otsMsg, hverifyS]
    | some m₀ =>
      rw [hopt] at hnotSigned
      have hmNe : m₀ ≠ out.2.1 := fun hEq => by simp [out, ← hu0, hEq] at hnotSigned
      by_cases hMEq : MStar = otsMsg H n hashKey (H.eval n hashKey m₀)
      · right
        obtain ⟨hkEq, hdEq⟩ := otsMsg_inj H hk'Len (H.length_eq n _ _ hk'Len)
          hhkLen (H.length_eq n _ _ hhkLen) hMEq
        rw [hkEq] at hdEq
        simp [out, isCollision, hdEq.symm, hmNe]
      · left
        simp [MStar, parsedSig, out, length_otsMsg, hMEq, hverifyS]
  unfold Game.succProbability
  rw [hidxEq, hotsEq, htcrEq]
  have hne_top : (μ.map winOts) true + (μ.map winTcr) true ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  simpa only [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] using
    ENNReal.toNNReal_mono hne_top (μ.map_true_le_add hpointwise)

/-- Polynomial-time upper bounds on one-time verification keys and signatures sampled at
`otsParam H n`. -/
theorem exists_ots_bounds (S : SignatureScheme) (H : KeyedHashFamily) :
    ∃ (ckg dkg : ℕ) (sigBound : ℕ → ℕ),
      ComputableInPolyTime sigBound encUnary encUnary ∧
      (∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
        keys.1.length ≤ ckg * (otsParam H n + 1) ^ dkg) ∧
      (∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen (otsParam H n))).support,
        ∀ msg, msg.length = otsParam H n →
        ∀ ots ∈ (ProbComp.eval (S.sign keys.2 msg)).support, ots.length ≤ sigBound n) := by
  obtain ⟨ckg, dkg, hkgLen⟩ := S.keyGen_ppt.length_le
  obtain ⟨bound, hboundPoly, hbound⟩ := S.exists_sign_length_bound_of_length_eq
  refine ⟨ckg, dkg, fun n => bound (otsParam H n),
    hboundPoly.comp (computableInPolyTime_otsParam H), fun n keys hkeys => ?_,
    fun n => hbound (otsParam H n)⟩
  have hkPair := hkgLen (otsParam H n) keys hkeys
  enc_len at hkPair

/-- **Existential reduction for `TCRSignature.scheme`**, after the proof of [BonehShoup2023],
Theorem 13.2, with one signing query: every strict oracle-PPT indexed forger `adversary` induces a
strict oracle-PPT one-time forger `otForger` and a strict PPT two-stage `TargetCollisionFinder`
`tcrAdv` bounding `adversary`'s indexed forging probability at every security parameter `n`. -/
theorem exists_reduction_indexedEufCmaGame_le (S : SignatureScheme) (H : KeyedHashFamily)
    {adversary : IndexedForger}
    (hadversary : IsOraclePPT encIndexedSignedMessage adversary) :
    ∃ (otForger : Forger) (tcrAdv : TargetCollisionFinder),
      IsOraclePPT (encPair encBits encBits) otForger ∧
      tcrAdv.IsPPT ∧
      ∀ n, Game.succProbability (ProbComp.eval ((scheme S H).indexedEufCmaGame adversary n)) ≤
        Game.succProbability (ProbComp.eval (S.eufOneTimeGame otForger (otsParam H n))) +
          Game.succProbability
            (ProbComp.eval (targetCollisionGame H.keyLen H.eval (fun _ _ => true) tcrAdv n)) := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, hmachine⟩ := hadversary.on
  obtain ⟨_, _, sigBound, hsigBoundPoly, _, hsigBoundLe⟩ := exists_ots_bounds S H
  exact ⟨oneTimeForger H sigBound machine c d,
    tcrAdversary S H machine c d,
    isOraclePPT_oneTimeForger H hsigBoundPoly machine c d,
    isPPT_tcrAdversary S H machine c d,
    succProbability_indexedEufCmaGame_le_of_machine S H sigBound hsigBoundLe adversary
      machine c d fun input State oracle s => by
        simpa only [← ProbOracleComp.runWith_eq_run_interpret] using
          hmachine input State oracle s⟩

end Reductions

/-- Any `Negligible` function remains `Negligible` after precomposing with `otsParam H`. -/
theorem negligible_comp_otsParam {f : ℕ → ℝ≥0} (hf : Negligible f) (H : KeyedHashFamily) :
    Negligible (fun n => f (otsParam H n)) :=
  hf.comp_polynomiallyLowerBounded (.mono_of_le .id (le_otsParam H))

end TCRSignature

/-- One-time form of [BonehShoup2023], Theorem 13.2 (Section 13.2.1, p. 534): a step, not the
cited result. The source states Theorem 13.2 for a many-time secure `S` and concludes many-time
security of the derived scheme; that statement is `SignatureScheme.EUFCMA.eufCMA_wordScheme`. For
one-time signatures it only remarks that short messages suffice "as discussed in Section 13.2"
(p. 584). Here, if `S` is one-time EUF-CMA secure (`OneTimeEUFCMA`, Definition 14.1) and `H` is
target collision resistant on every word, then construction `(13.2)` over `S`, as the capacity-`1`
indexed scheme `TCRSignature.scheme S H` on messages of any length, is one-time secure
(`IndexedEUFCMA` at the single index `0`). The proof is the source's case split with one signing
query. As in `eufCMA_wordScheme`, `S` runs at the parameter `otsParam H n` on the zero-padded word
of `(r, H(r, m))`. This is the first step of the route from one-way functions and target collision
resistant hashing to many-time signatures (`OneWay.exists_eufCMA_of_targetCollisionResistant`;
#5686). -/
theorem SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature
    {S : SignatureScheme} (hS : S.OneTimeEUFCMA)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    (TCRSignature.scheme S H).IndexedEUFCMA := by
  refine IndexedSignatureScheme.IndexedEUFCMA.of_negligible fun adversary hadversary => ?_
  obtain ⟨otForger, tcrAdv, hotPPT, htcrPPT, hbound⟩ :=
    TCRSignature.exists_reduction_indexedEufCmaGame_le S H hadversary
  have := TCRSignature.negligible_comp_otsParam (hS.negligible otForger hotPPT) H
  have := hH.negligible tcrAdv htcrPPT
  negligible using hbound

/-- **Capacity-`2` indexed signatures from one-way functions and target collision-resistant hash
families**: combining Lamport's one-time signature scheme (`OneWay.exists_oneTimeSignature`),
`TCRSignature.scheme`, and `IndexedSignatureScheme.double` yields a capacity-`2` `IndexedEUFCMA`
scheme without collision-resistant hashing. -/
theorem OneWay.exists_indexedEUFCMA_of_targetCollisionResistant
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA := by
  obtain ⟨S₀, hS₀⟩ := hf.exists_oneTimeSignature
  have hcap₁ : ∀ n, 1 ≤ (TCRSignature.scheme S₀ H).capacity n := fun _ => le_rfl
  exact ⟨(TCRSignature.scheme S₀ H).double hcap₁,
    fun _ => rfl,
    (hS₀.indexedEUFCMA_tcrSignature hH).double hcap₁⟩

/-- Step toward the signatures of [NaorYung1989], Section 4, not the cited result: no inspection of
the primary source is recorded (`manual/sources.md` lists the authors' manuscript without a check),
so this statement has not been checked against it (#5293). [BonehShoup2023], Sections 13.2.1 and
14.6, give the route but state no theorem of this form.

Any one-way function and any unrestricted target collision-resistant `KeyedHashFamily` yield a
stateless many-time `SignatureScheme` satisfying `EUFCMA`. -/
theorem OneWay.exists_eufCMA_of_targetCollisionResistant
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : KeyedHashFamily} (hH : H.TargetCollisionResistant) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨S, hcapS, hS⟩ := hf.exists_indexedEUFCMA_of_targetCollisionResistant hH
  exact hS.exists_eufCMA_of_oneWay (fun n => by rw [hcapS n]) hf

/-- Step toward the Naor–Yung signature theorem ([NaorYung1989], Theorem 2 / Section 4), not the
cited result: no inspection of the primary source is recorded (`manual/sources.md` lists the
authors' manuscript without a check), so this statement has not been checked against it (#5293).

Every one-way permutation implies the existence of a stateless many-time `EUFCMA`-secure digital
signature scheme, with no separate hash-family assumption. -/
theorem OneWayPermutation.exists_eufCMA
    {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.oneWay.exists_eufCMA_of_targetCollisionResistant hH

end Cslib.Crypto
