/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.LoRCPA
public import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Multi-query left-or-right CPA security from single-challenge semantic security

In [BonehShoup2023], Section 11.3.2, Theorem 11.1 (printed pp. 439–440), any `Q`-query
left-or-right CPA adversary `A` against a public-key encryption scheme yields a single-challenge
semantic-security adversary `B` such that `CPAadv[A, E] = Q · SSadv[B, E]`.

A machine that flips a bounded number of fair coins outputs each value with a dyadic probability,
so the certified adversary `lorToSingle` draws its cut index from `Fin (dyadicSize (Q n))` with
`ProbComp.sampleDyadicIndex (Q n)` and outputs `false` on indices `≥ Q n`. Here
`Q n < dyadicSize (Q n) ≤ 2 * (Q n + 1)` (`lt_dyadicSize`, `dyadicSize_le`). The identity stays
exact with the factor `dyadicSize (Q n)` (`advantage_lorGameOn_eq`), which gives `LoRINDCPAOn` for
polynomial `Q`. `advantage_lorGameOn_eq_uniform` is the printed equality with the factor `Q n`,
for `0 < Q n`: its right side is the uniform mixture over `Fin (Q n)` of the games of
`lorToSingleAt`, not the game of one `AdversaryOf`, and it carries no PPT certificate.

## Main definitions

* `Cslib.Crypto.Encryption.lorToSingleAt`: single-challenge adversary fixing the embedded query
  index.
* `Cslib.Crypto.Encryption.lorToSingle`: strict-PPT reduction sampling the index via
  `ProbComp.sampleDyadicIndex (Q n)`.
* `Cslib.Crypto.Encryption.lorHybridDistinguisherOn`, `Cslib.Crypto.Encryption.lorHybridGameOn`:
  hybrid experiment encrypting the first `split` queries under `bit = true` and the remaining
  queries under `bit = false`.

## Main results

* `Cslib.Crypto.Encryption.isPPT_lorToSingleAt`, `Cslib.Crypto.Encryption.isPPT_lorToSingle`:
  uniform strict-PPT certificates for `lorToSingleAt` and `lorToSingle`.
* `Cslib.Crypto.Encryption.lorHybridGameOn_step_gap`: single-step hybrid gap identity.
* `Cslib.Crypto.Encryption.eval_gameOn_lorToSingle`: mixture decomposition of `lorToSingle`.
* `Cslib.Crypto.Encryption.advantage_lorGameOn_eq`: exact strict-PPT identity
  `CPAadv[A, E] = dyadicSize (Q n) · SSadv[lorToSingle, E]`.
* `Cslib.Crypto.Encryption.advantage_lorGameOn_eq_uniform`: literal `Q n` book equality when
  `0 < Q n` and the index is sampled uniformly over `Fin (Q n)`.
* `Cslib.Crypto.Encryption.INDCPAOn.lorINDCPAOn`,
  `Cslib.Crypto.Encryption.INDCPAOf.lorINDCPAOf`, `Cslib.Crypto.Encryption.INDCPA.lorINDCPA`,
  `Cslib.Crypto.Encryption.WordINDCPA.wordLoRINDCPA`: asymptotic Theorem 11.1.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.3.2, Theorem 11.1 (pp. 439–440).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Saved state and hybrid reduction -/

/-- Saved state passed from `choose` to `guess` in `lorToSingleAt` and `lorToSingle`. -/
private structure LoRToSingleState where
  /-- Whether the sampled cut index `split` was strictly less than `Q n`. -/
  active : Bool
  /-- Public key forwarded to the suffix simulation. -/
  pk : List Bool
  /-- Embedded challenge query index (`0`-based). -/
  split : ℕ
  /-- Saved adversary state after query `split`. -/
  stateA : List Bool
  /-- Prefix ciphertext transcript returned to the adversary up to query `split`. -/
  transcript : List (List Bool)

/-- Framing encoding of `LoRToSingleState`. -/
private enc_structure encLoRToSingleState : LoRToSingleState where
  active : encBool, pk : encBits, split : encUnary, stateA : encBits,
  transcript : (encList encBits)

/-- Total polynomial-time decoder for `encLoRToSingleState`. -/
private def lorToSingleStateDecoder : Decoder encLoRToSingleState :=
  (Decoder.bool.pair (Decoder.bits.pair (Decoder.unary.pair (Decoder.bits.pair
    (Decoder.list Decoder.bits))))).map
    (fun (active, pk, split, stateA, transcript) => ⟨active, pk, split, stateA, transcript⟩)
    (fun s => (s.active, s.pk, s.split, s.stateA, s.transcript)) (fun _ => rfl) (fun _ => rfl)

/-- Encoded inactive state returned when `split ≥ Q n`. -/
private def rejectLoRToSingleState : List Bool :=
  encLoRToSingleState ⟨false, [], 0, [], []⟩

@[simp] private theorem decode_rejectLoRToSingleState :
    lorToSingleStateDecoder.decode rejectLoRToSingleState = ⟨false, [], 0, [], []⟩ :=
  lorToSingleStateDecoder.decode_enc ⟨false, [], 0, [], []⟩

private noncomputable def dummyMsg {Msg : Type} (adversary : LoRAdversaryOf Msg) : Msg :=
  (PMF.support_nonempty (ProbComp.eval (adversary.query 0 [] []))).some.msg₀

/-- Single-challenge semantic-security adversary wrapping `adversary : LoRAdversaryOf Msg` at a
fixed hybrid index `split : ℕ` (0-based; corresponds to `ω = split + 1` in [BonehShoup2023],
Theorem 11.1, p. 440). -/
noncomputable def lorToSingleAt {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (split : ℕ) : AdversaryOf Msg where
  choose n pk :=
    if decide (split < Q n) then do
      let st₀ ← adversary.start n pk
      let mid ← lorRunOn valid encrypt adversary n pk true split (st₀, [])
      let choice ← adversary.query n mid.1 mid.2
      return ((ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice),
        encLoRToSingleState ⟨true, pk, split, ChoiceOut.state choice, mid.2⟩)
    else
      let m := dummyMsg adversary
      return ((m, m), rejectLoRToSingleState)
  guess n state ct :=
    let decoded := lorToSingleStateDecoder.decode state
    if decoded.active then do
      let final ← lorRunOn valid encrypt adversary n decoded.pk false
        (Q n - decoded.split - 1) (decoded.stateA, ct :: decoded.transcript)
      adversary.guess n final.1 final.2
    else
      pure false

/-- Strict-PPT single-challenge semantic-security adversary wrapping `adversary : LoRAdversaryOf`,
sampling the embedded query index via `ProbComp.sampleDyadicIndex (Q n)` so the sampler runs in
strict fair-coin polynomial time with zero approximation error. -/
noncomputable def lorToSingle {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) : AdversaryOf Msg where
  choose n pk := do
    let split ← ProbComp.sampleDyadicIndex (Q n)
    (lorToSingleAt valid encrypt Q adversary split).choose n pk
  guess n state ct :=
    (lorToSingleAt valid encrypt Q adversary 0).guess n state ct

/-! ### Uniform strict PPT certificates -/

private theorem isPPTOn_lorToSingleAt_choose {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg} {ctBound : ℕ → ℕ}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary)
      (encPair (encPair encMsg encMsg) encBits)
      (fun p => (lorToSingleAt valid encrypt Q adversary p.2).choose p.1.1 p.1.2) := by
  let EIn := encPair (encPair encUnary encBits) encUnary
  let E1 := encPair EIn encBits
  let E2 := encPair E1 encLoRLoopState
  let E3 := encPair E2 (encChoiceOut encMsg)
  have hcondPair : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ => (p.2, Q p.1.1)) EIn (encPair encUnary encUnary) := by
    dsimp only [EIn]; fun_prop
  have hcond := (ComputableInPolyTime.unary_lt).comp hcondPair
  have hstart : IsPPTOn EIn encBits
      (fun p : (ℕ × List Bool) × ℕ => adversary.start p.1.1 p.1.2) :=
    hadversary.start.on.preprocess (by dsimp only [EIn]; fun_prop)
  have hrun : IsPPTOn E1 encLoRLoopState
      (fun q : ((ℕ × List Bool) × ℕ) × List Bool =>
        lorRunOn valid encrypt adversary q.1.1.1 q.1.1.2 true q.1.2 (q.2, [])) :=
    isPPTOn_lorRunOn hvalid hencrypt hctBound hctLen hadversary
      (by dsimp only [E1, EIn]; fun_prop) (by dsimp only [E1, EIn]; fun_prop)
      (ComputableInPolyTime.const true) (by dsimp only [E1, EIn]; fun_prop)
      (by dsimp only [E1, encLoRLoopState]; fun_prop)
  have hqArg : ComputableInPolyTime
      (fun r : (((ℕ × List Bool) × ℕ) × List Bool) × (List Bool × List (List Bool)) =>
        (r.1.1.1.1, r.2)) E2 encLoRStageInput := by
    dsimp only [E2, E1, EIn, encLoRStageInput, encLoRLoopState]; fun_prop
  have hquery := hadversary.query.preprocess hqArg
  have hrec : ComputableInPolyTime
      (fun s : ((((ℕ × List Bool) × ℕ) × List Bool) × (List Bool × List (List Bool))) ×
          ChoiceOut Msg =>
        (⟨true, s.1.1.1.1.2, s.1.1.1.2, ChoiceOut.state s.2, s.1.2.2⟩ : LoRToSingleState))
      E3 encLoRToSingleState :=
    encLoRToSingleState_mk_polyTime (ComputableInPolyTime.const true)
      (by dsimp only [E3, E2, E1, EIn]; fun_prop) (by dsimp only [E3, E2, E1, EIn]; fun_prop)
      (by dsimp only [E3, encChoiceOut]; fun_prop)
      (by dsimp only [E3, E2, encLoRLoopState]; fun_prop)
  let fPost : (((ℕ × List Bool) × ℕ) × List Bool) × (List Bool × List (List Bool)) →
      ChoiceOut Msg → (Msg × Msg) × List Bool :=
    fun r choice => ((ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice),
      encLoRToSingleState ⟨true, r.1.1.1.2, r.1.1.2, ChoiceOut.state choice, r.2.2⟩)
  have hpost : ComputableInPolyTime (fun s : _ × ChoiceOut Msg => fPost s.1 s.2)
      E3 (encPair (encPair encMsg encMsg) encBits) :=
    ComputableInPolyTime.prod (by
      dsimp only [E3, encChoiceOut]
      fun_prop) hrec.encoding_comp
  have hyes : IsPPTOn EIn (encPair (encPair encMsg encMsg) encBits)
      (fun p : (ℕ × List Bool) × ℕ => do
        let st₀ ← adversary.start p.1.1 p.1.2
        let mid ← lorRunOn valid encrypt adversary p.1.1 p.1.2 true p.2 (st₀, [])
        let choice ← adversary.query p.1.1 mid.1 mid.2
        return fPost ((p, st₀), mid) choice) :=
    hstart.bind_with (hrun.bind_with (by simpa only [bind_pure_comp] using hquery.map_with hpost))
  have hno : IsPPTOn EIn (encPair (encPair encMsg encMsg) encBits)
      (fun _ => let m := dummyMsg adversary; return ((m, m), rejectLoRToSingleState)) :=
    (ComputableInPolyTime.const ((dummyMsg adversary, dummyMsg adversary),
      rejectLoRToSingleState)).isPPTOn
  exact IsPPTOn.cond hcond hyes hno

/-- `lorToSingleAt` is uniformly strict PPT in `AdversaryOf.IsPPT encMsg`: `hvalid`, `hencrypt`,
`hctBound`/`hctLen`, and `hQ` certify the prefix/suffix simulation (`valid`, `encrypt`, bounded
ciphertext lengths across adaptive queries, and the iteration count `Q n`). -/
theorem isPPT_lorToSingleAt {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg} {ctBound : ℕ → ℕ}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg) (split : ℕ) :
    (lorToSingleAt valid encrypt Q adversary split).IsPPT encMsg where
  choose :=
    (isPPTOn_lorToSingleAt_choose hvalid hencrypt hctBound hctLen hQ hadversary).preprocess
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const split))
  guess := by
    have hdecoded : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => lorToSingleStateDecoder.decode p.2.1)
        encGuessInput encLoRToSingleState :=
      lorToSingleStateDecoder.computableInPolyTime.comp (by dsimp only [encGuessInput]; fun_prop)
    have hrun : IsPPTOn encGuessInput encLoRLoopState
        (fun p : ℕ × List Bool × List Bool =>
          lorRunOn valid encrypt adversary p.1 (lorToSingleStateDecoder.decode p.2.1).pk false
            (Q p.1 - (lorToSingleStateDecoder.decode p.2.1).split - 1)
            ((lorToSingleStateDecoder.decode p.2.1).stateA,
              p.2.2 :: (lorToSingleStateDecoder.decode p.2.1).transcript)) :=
      isPPTOn_lorRunOn hvalid hencrypt hctBound hctLen hadversary
        (by dsimp only [encGuessInput]; fun_prop)
        (encLoRToSingleState_pk_polyTime hdecoded)
        (ComputableInPolyTime.const false)
        (by
          have := encLoRToSingleState_split_polyTime hdecoded
          dsimp only [encGuessInput]
          fun_prop)
        (by
          have := encLoRToSingleState_stateA_polyTime hdecoded
          have := encLoRToSingleState_transcript_polyTime hdecoded
          dsimp only [encGuessInput, encLoRLoopState]
          fun_prop)
    have harg : ComputableInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × (List Bool × List (List Bool)) => (q.1.1, q.2))
        (encPair encGuessInput encLoRLoopState) encLoRStageInput := by
      dsimp only [encLoRStageInput, encGuessInput, encLoRLoopState]; fun_prop
    simpa only [lorToSingleAt] using IsPPTOn.cond (encLoRToSingleState_active_polyTime hdecoded)
      (hrun.bind_with (hadversary.guess.preprocess harg)) (ComputableInPolyTime.const false).isPPTOn

/-- `lorToSingle` is uniformly strict PPT in `AdversaryOf.IsPPT encMsg`: `hvalid`, `hencrypt`,
`hctBound`/`hctLen`, and `hQ` certify the dyadic sampler and simulated prefix/suffix queries. -/
theorem isPPT_lorToSingle {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg} {ctBound : ℕ → ℕ}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg) :
    (lorToSingle valid encrypt Q adversary).IsPPT encMsg where
  choose := (isPPTOn_sampleDyadicIndex
    (hQ.comp (ComputableInPolyTime.fst encUnary encBits))).bind_with
      (isPPTOn_lorToSingleAt_choose hvalid hencrypt hctBound hctLen hQ hadversary)
  guess := (isPPT_lorToSingleAt hvalid hencrypt hctBound hctLen hQ hadversary 0).guess

/-! ### Hybrid games and exact advantage identity -/

/-- Hybrid `split`-step distinguisher for `Q`-query left-or-right security: encrypt the first
`min split (Q n)` queries under `bit = true` and the remaining `Q n - split` queries under
`bit = false`. -/
noncomputable def lorHybridDistinguisherOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (split : ℕ) : Distinguisher :=
  fun n pk => do
    let st₀ ← adversary.start n pk
    let mid ← lorRunOn valid encrypt adversary n pk true (min split (Q n)) (st₀, [])
    let final ← lorRunOn valid encrypt adversary n pk false (Q n - split) mid
    adversary.guess n final.1 final.2

/-- Hybrid `Q`-query left-or-right chosen-plaintext experiment at index `split : ℕ`. -/
noncomputable def lorHybridGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (split n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  lorHybridDistinguisherOn valid encrypt Q adversary split n keys.1

@[simp] theorem eval_lorHybridGameOn_zero {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (n : ℕ) :
    ProbComp.eval (lorHybridGameOn valid keyGen encrypt Q adversary 0 n) =
      ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary false n) := by
  simp only [lorHybridGameOn, lorHybridDistinguisherOn, lorGameOn, lorDistinguisherOn,
    Nat.zero_min, Nat.sub_zero, lorRunOn, OracleComp.iterate_zero, pure_bind]

@[simp] theorem eval_lorHybridGameOn_of_le {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) {split n : ℕ} (hle : Q n ≤ split) :
    ProbComp.eval (lorHybridGameOn valid keyGen encrypt Q adversary split n) =
      ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary true n) := by
  simp only [lorHybridGameOn, lorHybridDistinguisherOn, lorGameOn, lorDistinguisherOn,
    Nat.min_eq_right hle, Nat.sub_eq_zero_of_le hle, lorRunOn, OracleComp.iterate_zero, pure_bind]

/-- **Single-step hybrid identity for adaptive left-or-right CPA**
([BonehShoup2023], Section 11.3.2, Theorem 11.1, printed p. 440): for every `split : ℕ`, the
signed gap between `lorHybridGameOn ... split n` and `lorHybridGameOn ... (split + 1) n` equals
the signed single-challenge gap of `lorToSingleAt ... split`. -/
theorem lorHybridGameOn_step_gap {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (split n : ℕ) :
    (Game.succProbability
        (ProbComp.eval (lorHybridGameOn valid keyGen encrypt Q adversary split n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval (lorHybridGameOn valid keyGen encrypt Q adversary (split + 1) n)) =
      (Game.succProbability
        (ProbComp.eval
          (gameOn valid keyGen encrypt
            (lorToSingleAt valid encrypt Q adversary split) false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (gameOn valid keyGen encrypt
            (lorToSingleAt valid encrypt Q adversary split) true n)) := by
  by_cases hlt : split < Q n
  · have hrem0 : Q n - split = (Q n - split - 1) + 1 := by omega
    have lhs_eq (bit : Bool) :
        ProbComp.eval
          (lorHybridGameOn valid keyGen encrypt Q adversary (if bit then split + 1 else split) n) =
          (do
            let keys ← ProbComp.eval (keyGen n)
            let st₀ ← ProbComp.eval (adversary.start n keys.1)
            let mid ← ProbComp.eval (lorRunOn valid encrypt adversary n keys.1 true split (st₀, []))
            let choice ← ProbComp.eval (adversary.query n mid.1 mid.2)
            let c ← ProbComp.eval
              (if valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
                encrypt n keys.1 (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
              else pure [])
            let final ← ProbComp.eval
              (lorRunOn valid encrypt adversary n keys.1 false (Q n - split - 1)
                (ChoiceOut.state choice, c :: mid.2))
            ProbComp.eval (adversary.guess n final.1 final.2)) := by
      cases bit
      · simp only [Bool.false_eq_true, ↓reduceIte, lorHybridGameOn, lorHybridDistinguisherOn,
          Nat.min_eq_left hlt.le]
        have htail (pk : List Bool) (mid : List Bool × List (List Bool)) :
            lorRunOn valid encrypt adversary n pk false (Q n - split) mid =
              lorStepOn valid encrypt adversary n pk false mid >>=
                lorRunOn valid encrypt adversary n pk false (Q n - split - 1) := by
          unfold lorRunOn; conv_lhs => rw [hrem0, OracleComp.iterate_succ_bind]
        simp_rw [htail]
        simp only [lorStepOn, pmf_norm, Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte, lorHybridGameOn, lorHybridDistinguisherOn, Nat.min_eq_left hlt,
          Nat.sub_add_eq (Q n) split 1]
        have hfront (pk st₀ : List Bool) :
            lorRunOn valid encrypt adversary n pk true (split + 1) (st₀, []) =
              lorRunOn valid encrypt adversary n pk true split (st₀, []) >>=
                lorStepOn valid encrypt adversary n pk true := by
          unfold lorRunOn; rw [OracleComp.iterate_succ]
        simp_rw [hfront]
        simp only [lorStepOn, pmf_norm, ↓reduceIte]
    have rhs_eq (bit : Bool) :
        ProbComp.eval
          (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary split) bit n) =
          (do
            let keys ← ProbComp.eval (keyGen n)
            let st₀ ← ProbComp.eval (adversary.start n keys.1)
            let mid ← ProbComp.eval (lorRunOn valid encrypt adversary n keys.1 true split (st₀, []))
            let choice ← ProbComp.eval (adversary.query n mid.1 mid.2)
            if valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
              let c ← ProbComp.eval
                (encrypt n keys.1 (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
              let final ← ProbComp.eval
                (lorRunOn valid encrypt adversary n keys.1 false (Q n - split - 1)
                  (ChoiceOut.state choice, c :: mid.2))
              ProbComp.eval (adversary.guess n final.1 final.2)
            else PMF.pure false) := by
      simp only [gameOn, lorToSingleAt, decide_eq_true hlt, ↓reduceIte, pmf_norm,
        apply_ite ProbComp.eval, lorToSingleStateDecoder.decode_enc]
    have h0 := lhs_eq false
    have h1 := lhs_eq true
    simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
    rw [h0, h1, rhs_eq false, rhs_eq true]
    simp only [PMF.monad_bind_eq_bind]
    rw [sub_eq_sub_iff_add_eq_add, Game.coe_succProbability, Game.coe_succProbability,
      Game.coe_succProbability, Game.coe_succProbability,
      ← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
      ← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    refine congrArg ENNReal.toReal ?_
    refine PMF.bind_apply_add_eq_on_support fun keys _ =>
      PMF.bind_apply_add_eq_on_support fun st₀ _ =>
      PMF.bind_apply_add_eq_on_support fun mid _ =>
      PMF.bind_apply_add_eq_on_support fun choice _ => ?_
    by_cases hv : valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) = true
    · simp [hv]
    · simp [hv, add_comm]
  · have hle : Q n ≤ split := Nat.le_of_not_lt hlt
    have heqR (bit : Bool) :
        ProbComp.eval
          (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary split) bit n) =
          PMF.pure false := by
      simp only [gameOn, lorToSingleAt, decide_eq_false hlt, Bool.false_eq_true,
        ↓reduceIte, pmf_norm, apply_ite ProbComp.eval, decode_rejectLoRToSingleState,
        PMF.bind_const, ite_self]
    rw [eval_lorHybridGameOn_of_le valid keyGen encrypt Q adversary hle,
      eval_lorHybridGameOn_of_le valid keyGen encrypt Q adversary (Nat.le_succ_of_le hle),
      sub_self, heqR false, heqR true, sub_self]

/-- Running `lorToSingle` in `gameOn` averages `lorToSingleAt` uniformly over
`Fin (dyadicSize (Q n))`, padding indices `i.val ≥ Q n` with `PMF.pure false`. -/
theorem eval_gameOn_lorToSingle {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (gameOn valid keyGen encrypt (lorToSingle valid encrypt Q adversary) bit n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind fun i =>
        if i.val < Q n then
          ProbComp.eval
            (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary i.val) bit n)
        else PMF.pure false := by
  simp only [gameOn, lorToSingle, pmf_norm]
  rw [PMF.bind_comm]
  simp only [ProbComp.eval_sampleDyadicIndex, PMF.bind_map, Function.comp_def]
  congr 1 with i
  by_cases hi : i.val < Q n
  · simp only [hi, ↓reduceIte]; rfl
  · rw [ite_eq_right_of_eq_false (c := i.val < Q n) (h := eq_false hi)]
    simp only [lorToSingleAt, decide_eq_false hi, Bool.false_eq_true, ↓reduceIte,
      ProbComp.eval_pure, PMF.pure_bind, apply_ite ProbComp.eval, ProbComp.eval_bind,
      decode_rejectLoRToSingleState, PMF.bind_const, ite_self]

/-- Both exact identities at once: the cut index is uniform on `Fin capacity` with
`Q n ≤ capacity`, and indices `≥ Q n` output `false`. -/
private theorem advantage_lorGameOn_eq_mixture {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (n capacity : ℕ) [NeZero capacity] (hle : Q n ≤ capacity) :
    Game.advantage
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary false n))
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary true n)) =
      capacity *
        Game.advantage
          ((PMF.uniformOfFintype (Fin capacity)).bind fun i =>
            if i.val < Q n then
              ProbComp.eval
                (gameOn valid keyGen encrypt
                  (lorToSingleAt valid encrypt Q adversary i.val) false n)
            else PMF.pure false)
          ((PMF.uniformOfFintype (Fin capacity)).bind fun i =>
            if i.val < Q n then
              ProbComp.eval
                (gameOn valid keyGen encrypt
                  (lorToSingleAt valid encrypt Q adversary i.val) true n)
            else PMF.pure false) := by
  have hred := Game.succProbability_hybrid_reduction
    (games := fun split => ProbComp.eval (lorHybridGameOn valid keyGen encrypt Q adversary split n))
    (game1 := fun split => ProbComp.eval
      (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary split) false n))
    (game2 := fun split => ProbComp.eval
      (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary split) true n))
    (Q n) capacity hle 1
    (fun split _ => by
      rw [one_mul]; exact lorHybridGameOn_step_gap valid keyGen encrypt Q adversary split n)
  rw [eval_lorHybridGameOn_zero, eval_lorHybridGameOn_of_le valid keyGen encrypt Q adversary le_rfl,
    mul_one] at hred
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, NNReal.coe_natCast, hred,
    abs_mul, Nat.abs_cast]

/-- **Quantitative Theorem 11.1 (exact strict-PPT reduction equality):** for every `n`, the
`Q`-query left-or-right CPA advantage of `adversary` equals `dyadicSize (Q n)` times the
single-challenge semantic-security advantage of the certified adversary `lorToSingle valid encrypt
Q adversary`. The factor is `dyadicSize (Q n) ≤ 2 * (Q n + 1)` (`dyadicSize_le`) instead of the
printed `Q n`, so that sampling the embedded query index runs in strict fair-coin polynomial time
([BonehShoup2023], Section 11.3.2, Theorem 11.1, printed pp. 439–440). -/
theorem advantage_lorGameOn_eq {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary false n))
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary true n)) =
      dyadicSize (Q n) *
        Game.advantage
          (ProbComp.eval
            (gameOn valid keyGen encrypt (lorToSingle valid encrypt Q adversary) false n))
          (ProbComp.eval
            (gameOn valid keyGen encrypt (lorToSingle valid encrypt Q adversary) true n)) := by
  rw [eval_gameOn_lorToSingle, eval_gameOn_lorToSingle]
  exact advantage_lorGameOn_eq_mixture valid keyGen encrypt Q adversary n _
    (lt_dyadicSize (Q n)).le

/-- **Quantitative Theorem 11.1 (exact printed equality `CPAadv[A, E] = Q · SSadv[B, E]`):**
when `0 < Q n` (`[NeZero (Q n)]`), the `Q`-query left-or-right CPA advantage of `adversary` equals
`Q n` times the advantage between the two uniform mixtures over `i : Fin (Q n)` of the
single-challenge games of `lorToSingleAt valid encrypt Q adversary i`. The mixture is the book's
`B`; it is not the game of one `AdversaryOf` and has no PPT certificate here
([BonehShoup2023], Section 11.3.2, Theorem 11.1, printed pp. 439–440). -/
theorem advantage_lorGameOn_eq_uniform {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (n : ℕ) [NeZero (Q n)] :
    Game.advantage
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary false n))
      (ProbComp.eval (lorGameOn valid keyGen encrypt Q adversary true n)) =
      Q n *
        Game.advantage
          ((PMF.uniformOfFintype (Fin (Q n))).bind fun i =>
            ProbComp.eval
              (gameOn valid keyGen encrypt (lorToSingleAt valid encrypt Q adversary i.val) false n))
          ((PMF.uniformOfFintype (Fin (Q n))).bind fun i =>
            ProbComp.eval
              (gameOn valid keyGen encrypt
                (lorToSingleAt valid encrypt Q adversary i.val) true n)) := by
  simpa only [Fin.is_lt, ↓reduceIte] using
    advantage_lorGameOn_eq_mixture valid keyGen encrypt Q adversary n (Q n) le_rfl

/-! ### Asymptotic Theorem 11.1 -/

/-- **Theorem 11.1 ([BonehShoup2023], §11.3.2, printed p. 439):** single-challenge semantic
security under admissibility predicate `valid` implies `Q`-query left-or-right CPA security.
- `hvalid`: `valid` must be computable in polynomial time because `lorToSingle` evaluates it to
  filter simulated prefix and suffix queries.
- `hencrypt`: `encrypt` must be uniformly strict PPT because `lorToSingle` directly encrypts
  simulated prefix and suffix queries under `pk`.
- `hctBound` and `hctLen`: under every key word and for every `msg : Msg`, admissible or not,
  every ciphertext has length at most `ctBound n`, a polynomial in `n` alone, so that the
  transcript stays polynomially bounded over `Q n` rounds. This global output-length bound is a
  convention of this library and is stronger than the source's. [BonehShoup2023], Definition 2.9
  (p. 30), bounds the lengths of the members of each space, and Definition 11.3(4) (p. 438) asks
  that encryption land in the ciphertext space only for generated keys and for messages in the
  message space. A total `encrypt` that copies a long input from outside the source's message
  space fails `hctLen` without changing any experiment of the source. Every source scheme has a
  bounded-output extension that agrees with it on the source's domain and truncates or rejects
  other inputs; that extension satisfies `hctLen`. On an infinite message type no scheme that
  decrypts every message satisfies `hctLen`, since there are finitely many ciphertexts of length at
  most `ctBound n`.
- `hQ`: `Q` must be computable in unary polynomial time so `lorToSingle` can sample the hybrid cut,
  iterate `Q n` steps in strict PPT, and bound `dyadicSize (Q n)` polynomially. -/
theorem INDCPAOn.lorINDCPAOn {Msg : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)} {Q : ℕ → ℕ}
    {ctBound : ℕ → ℕ}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (h : INDCPAOn valid encMsg keyGen encrypt) :
    LoRINDCPAOn valid encMsg keyGen encrypt Q := by
  intro adversary hadversary
  have hsingleNeg := h (lorToSingle valid encrypt Q adversary)
    (isPPT_lorToSingle hvalid hencrypt hctBound hctLen hQ hadversary)
  negligible using fun n => (advantage_lorGameOn_eq valid keyGen encrypt Q adversary n).le

/-- **Theorem 11.1 (unrestricted messages):** unrestricted `INDCPAOf` implies `LoRINDCPAOf`.
- `hencrypt`: `encrypt` must be uniformly strict PPT so `lorToSingle` can simulate prefix/suffix
  queries.
- `hctBound` and `hctLen`: every ciphertext of every `msg : Msg` has length at most `ctBound n`,
  as in `INDCPAOn.lorINDCPAOn` (on an infinite message type, `encrypt` must truncate or reject
  inputs beyond a polynomial length).
- `hQ`: `Q` must be computable in unary polynomial time to execute and certify the reduction. -/
theorem INDCPAOf.lorINDCPAOf {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)} {Q : ℕ → ℕ}
    {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (h : INDCPAOf encMsg keyGen encrypt) :
    LoRINDCPAOf encMsg keyGen encrypt Q :=
  h.lorINDCPAOn (ComputableInPolyTime.const true) hencrypt hctBound hctLen hQ

/-- **Theorem 11.1 (single-bit messages):** `INDCPA` implies `LoRINDCPA`.
- `hencrypt`: `encrypt` must be uniformly strict PPT so `lorToSingle` can simulate prefix/suffix
  queries.
- `hctBound` and `hctLen`: every ciphertext of every `msg : Bool` has length at most `ctBound n`,
  as in `INDCPAOn.lorINDCPAOn`.
- `hQ`: `Q` must be computable in unary polynomial time to execute and certify the reduction. -/
theorem INDCPA.lorINDCPA
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)} {Q : ℕ → ℕ}
    {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (h : INDCPA keyGen encrypt) :
    LoRINDCPA keyGen encrypt Q :=
  h.lorINDCPAOn (ComputableInPolyTime.const true) hencrypt hctBound hctLen hQ

/-- **Theorem 11.1 (bit-word messages, equal-length rule):** `WordINDCPA` implies `WordLoRINDCPA`.
- `hencrypt`: `encrypt` must be uniformly strict PPT so `lorToSingle` can simulate prefix/suffix
  queries.
- `hctBound` and `hctLen`: every ciphertext of every `msg : List Bool` (admissible or not) has
  length at most `ctBound n`, as in `INDCPAOn.lorINDCPAOn`; `encrypt` must truncate or reject
  words beyond a polynomial length.
- `hQ`: `Q` must be computable in unary polynomial time to execute and certify the reduction. -/
theorem WordINDCPA.wordLoRINDCPA
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)} {Q : ℕ → ℕ}
    {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (h : WordINDCPA keyGen encrypt) :
    WordLoRINDCPA keyGen encrypt Q :=
  h.lorINDCPAOn ((by polytime)) hencrypt hctBound hctLen hQ

end Cslib.Crypto.Encryption

end
