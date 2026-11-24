/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT

/-!
# Yao's protocol over the DDH transfer with the key-derivation mask: a concrete bound

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It instantiates the concrete bound of
`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT.lean` at the groups of a
`PrimeOrderGroupFamily` `F` with the key-derivation mask of
`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/KDF.lean`, and replaces the pad-hiding term of every
transfer by the advantage of an explicit distinguisher in the key-derivation games `F.kdfRealGame`
and `F.kdfIdealGame` ([BonehShoup2023], Section 11.5.2, Attack Game 11.3), the games of
`F.SecureKDF`.

## What is proved

All statements are concrete and per instance: a fixed security parameter `n`, fixed group
parameters `d`, a fixed input tuple and one distinguisher. The mask is `F.kdfMask H d`, the pads
are `F.kdfPads d`, the group is `F.Carrier d` with generator `F.generator d`, and the simulator of
the masked transfer for a corrupted receiver is `maskedOTReceiverSim` with a uniform
`msgLen n`-bit word in the unchosen component. The only hypotheses on the components are that the
keys `H (d, F.encode d r)` have length `msgLen n` and that the transferred values have that
length. There is no hypothesis on any reduction.

* `F.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdfAt`: for one test `D` at the parameters `d`,
  the advantage against a corrupted receiver of the masked transfer with the ideal pad transfer
  *equals* the advantage of the explicit distinguisher `F.maskedOTReceiverToKDFDistinguisherAt`
  between `F.kdfIdealGame` and `F.kdfRealGame` under the setup that returns `d`.
* `F.semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le`: one masked transfer over the DDH transfer,
  corrupted receiver: the advantage of `D` is at most that key-derivation advantage plus the
  expectation over the sender's pads of the fixed-group DDH advantage of
  `maskedOTToDDHDistinguisher`.
* `Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_evaluator_le`: Yao's protocol over the
  batched masked transfer over the DDH transfer, corrupted evaluator: the advantage of `D` is at
  most the `prv.sim` advantage of `Yao.evaluatorDistinguisherToPrvSim` plus the expectation over
  the parties' coins of `Composition.replacementCost` of `F.kdfDDHMaskedOTReceiverCost` along the
  `c.evaluatorLen` transfers. So the bound has one garbling term and, for each transfer, one
  key-derivation term and one expected DDH term, each the advantage of an explicit program built
  from `D`.
* `Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_garbler_eq_zero`: the same protocol,
  corrupted garbler: the advantage is exactly zero, with no hardness term. The statement of
  `CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT.lean` for an arbitrary mask asks that
  unmasking invert masking on all values and does not apply to `F.kdfMask`; here the length of the
  offered values is used instead.

## What is not proved

* **The length of the labels is a hypothesis.** The mask works at the width of the key, so the
  statements for Yao's protocol ask that both values offered in every transfer
  (`Yao.transferQueries`) have length `msgLen n`, on the given inputs and for all coins. This is
  not derived from a property of the garbling scheme, and no garbling scheme is exhibited for
  which it holds together with the other hypotheses.
* The key-derivation terms are advantages under the *point* setup `fun _ => PMF.pure d`, of a
  distinguisher that depends on `d`, on the garbler's coins, on the outcomes of the earlier
  transfers and, for the DDH terms, on the sender's pads. The bound is an expectation of such
  advantages, with the absolute value inside the expectation. An assumption such as `F.SecureKDF`
  or `F.DDH` bounds the advantage of one efficient distinguisher that samples these itself, with
  the absolute value outside, and that does not bound this expectation. No hardness assumption is
  applied here.
* No efficiency certificate for any reduction, and no asymptotic statement
  (`ProtocolFamily.SemiHonestSecure`).
* The exponents of the pads and of the DDH transfer are exactly uniform, and the DDH transfer is
  the fixed-group protocol `ddhOTProtocol`, not the bit-string protocol `ddhOTProbProtocol`.

The locators for [LindellPinkas2009] and [BonehShoup2023] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean` and
`CslibFrontier/Crypto/Computational/ElGamal.lean`; they were not re-verified against the sources.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.maskedOTReceiverToKDFDistinguisherAt`: the key-derivation
  distinguisher of one test of a corrupted receiver's view at fixed group parameters.
* `Cslib.Crypto.PrimeOrderGroupFamily.kdfDDHMaskedOTReceiverCost`: the bound on the advantage
  against one transfer for a corrupted receiver, as a key-derivation advantage plus an expected
  DDH advantage.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le`: the
  bound for one transfer.
* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_evaluator_le`:
  the bound for a corrupted evaluator.
* `Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_garbler_eq_zero` (in
  `Cslib.Crypto.Protocols.MPC`): advantage zero for a corrupted garbler.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5.2 (Attack Game 11.3), as formalized by `kdfRealGame`
  and `kdfIdealGame`.
* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto.Protocols.MPC
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

variable (F : PrimeOrderGroupFamily)

/-! ### One test at fixed group parameters -/

open scoped Classical in
/-- **The key-derivation distinguisher of one test of a corrupted receiver's view at the group
parameters `d`**: `F.maskedOTReceiverToKDFDistinguisher H` for the inputs `x` at every parameter
and the family of tests that is `D` at `d` and answers `false` at every other description. A
`KDFDistinguisher` is a family over all descriptions; under the setup that returns `d` only its
member at `d` is run (`semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdfAt`). No efficiency is
claimed for it. -/
@[expose] noncomputable def maskedOTReceiverToKDFDistinguisherAt
    (H : F.Desc × List Bool → List Bool) (d : F.Desc) (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) : F.KDFDistinguisher :=
  F.maskedOTReceiverToKDFDistinguisher H (fun _ _ => x)
    fun _ => Function.update (fun _ _ => pure false) d D

open scoped Classical in
/-- Concrete per-instance step toward #6045 criterion 2, not an asymptotic security theorem; no
efficiency (PPT) certificate for the reduction is proved here. At fixed group parameters `d` and
security parameter `n`, when every key `H (d, F.encode d r)` and the receiver's output have length
`msgLen n`, the semi-honest advantage of one test `D` against `maskedOT` with the key-derivation
mask `F.kdfMask H d` and the pads `F.kdfPads d`, with the ideal pad transfer, for the corrupted
receiver `{1}` and the simulator that fills the unchosen component with a uniform `msgLen n`-bit
word, *equals* the advantage of the explicit key-derivation distinguisher
`F.maskedOTReceiverToKDFDistinguisherAt H d x D` between `F.kdfIdealGame` and `F.kdfRealGame`
under the setup that returns `d`. This is `semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf` for
one test instead of a family of tests. -/
theorem semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdfAt (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (x : (i : Fin 2) → OTIn (List Bool) i)
    (hout : (otOutputs x 1 : List Bool).length = msgLen n)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    semiHonestAdvantage (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
        (otWorld (F.Carrier d)) (otFunctionality (List Bool)) {1}
        (maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
          (Cslib.BitString.sampleList (msgLen n))) x D =
      Game.advantage
        (F.kdfIdealGame (fun _ => PMF.pure d) msgLen
          (F.maskedOTReceiverToKDFDistinguisherAt H d x D) n)
        (F.kdfRealGame (fun _ => PMF.pure d) H
          (F.maskedOTReceiverToKDFDistinguisherAt H d x D) n) := by
  have h := F.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf H msgLen (fun _ _ => x)
    (fun _ => Function.update (fun _ _ => pure false) d D) n d hH hout
  rw [Function.update_self] at h
  exact h

/-! ### One transfer over the DDH transfer -/

/-- **The masked transfer with the key-derivation mask over the DDH transfer, corrupted receiver,
for one distinguisher.** Step towards [LindellPinkas2009], Theorem 7, not the cited result
(#6045): a concrete bound at a fixed security parameter, fixed group parameters and a fixed
instance, with no efficiency certificate for the reductions and no hardness assumption applied.

At the group parameters `d`, when every key `H (d, F.encode d r)` and the receiver's output have
length `msgLen n`, the semi-honest advantage of `D` against `ddhMaskedOT` with the mask
`F.kdfMask H d` and the pads `F.kdfPads d` over the DDH transfer in `F.Carrier d`, for the
coalition `{1}`, with the simulator composed from simulators `S₁` of `maskedOT` whose member at
`{1}` is `maskedOTReceiverSim` with a uniform `msgLen n`-bit word and simulators `S₂` of the DDH
transfer whose member at `{1}` is `ddhOTReceiverSim`, is at most

* the advantage of the explicit key-derivation distinguisher
  `F.maskedOTReceiverToKDFDistinguisherAt`, applied to `composeDistinguisher` of `D`, between
  `F.kdfIdealGame` and `F.kdfRealGame` under the setup that returns `d`, plus
* the expectation, over the coins `c` of `maskedOT` (the sender's pads), of the fixed-group DDH
  advantage of `maskedOTToDDHDistinguisher`.

Nothing is assumed about either reduction, and neither term is bounded here. -/
theorem semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hS₁ : S₁ {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {1} = ddhOTReceiverSim (F.generator d) (F.order d))
    (x : (i : Fin 2) → OTIn (List Bool) i)
    (hout : (otOutputs x 1 : List Bool).length = msgLen n)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    (semiHonestAdvantage
        (ddhMaskedOT (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
        noOracleWorld (otFunctionality (List Bool)) {1}
        (ddhMaskedOTSim (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂ {1}) x D : ℝ≥0∞) ≤
      (Game.advantage
          (F.kdfIdealGame (fun _ => PMF.pure d) msgLen
            (F.maskedOTReceiverToKDFDistinguisherAt H d x
              (composeDistinguisher (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
                (fun _ => S₂) {1} x D)) n)
          (F.kdfRealGame (fun _ => PMF.pure d) H
            (F.maskedOTReceiverToKDFDistinguisherAt H d x
              (composeDistinguisher (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
                (fun _ => S₂) {1} x D)) n) : ℝ≥0∞) +
        ∑' c, ProbComp.eval (OracleComp.pi
            (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).sampleCoins) c *
          (ddhAdvantage (F.order d) (F.generator d)
            (maskedOTToDDHDistinguisher (F.generator d) (F.order d) (F.kdfMask H d)
              (F.kdfMask H d) S₂ x c D) : ℝ≥0∞) := by
  refine (semiHonestAdvantage_maskedOT_ddhOT_receiver_le (F.generator d) (F.order d)
    (F.smul_generator_surjective d) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂ hS₂ x
    D).trans (add_le_add (le_of_eq ?_) le_rfl)
  rw [hS₁, F.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdfAt H msgLen n d hH x hout]

/-! ### The cost of one transfer for a corrupted receiver -/

/-- **The bound on the advantage against one masked transfer with the key-derivation mask over the
DDH transfer, for a corrupted receiver.** For a test `D` of the views of a coalition `J` equal to
`{1}` on the inputs `x`: the advantage of the explicit key-derivation distinguisher
`F.maskedOTReceiverToKDFDistinguisherAt` between `F.kdfIdealGame` and `F.kdfRealGame` under the
setup that returns `d`, plus the expectation, over the coins `c` of `maskedOT` (the sender's
pads), of the fixed-group DDH advantage of `maskedOTToDDHDistinguisher`. For every other coalition
it is `⊤`: the bound is stated for a corrupted receiver only. It bounds the advantage against the
transfer only on inputs whose chosen value has length `msgLen n`
(`semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le`); on other inputs the mask, which works at
the width of the key, does not recover the value. It has the argument order of a per-round cost of
`Composition.replacementCost` for the single-transfer oracle `otSpec (List Bool)`. -/
@[expose] noncomputable def kdfDDHMaskedOTReceiverCost (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (_ : Unit) (J : Finset (Fin 2)) (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : J) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) : ℝ≥0∞ :=
  if h : J = {1} then
    (Game.advantage
        (F.kdfIdealGame (fun _ => PMF.pure d) msgLen
          (F.maskedOTReceiverToKDFDistinguisherAt H d x
            (composeDistinguisher (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
              (fun _ => S₂) {1} x fun r => D (fun s => r.1 ⟨s.1, h.symm ▸ s.2⟩, r.2))) n)
        (F.kdfRealGame (fun _ => PMF.pure d) H
          (F.maskedOTReceiverToKDFDistinguisherAt H d x
            (composeDistinguisher (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
              (fun _ => S₂) {1} x fun r => D (fun s => r.1 ⟨s.1, h.symm ▸ s.2⟩, r.2))) n) :
        ℝ≥0∞) +
      ∑' c, ProbComp.eval (OracleComp.pi
          (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).sampleCoins) c *
        (ddhAdvantage (F.order d) (F.generator d)
          (maskedOTToDDHDistinguisher (F.generator d) (F.order d) (F.kdfMask H d)
            (F.kdfMask H d) S₂ x c fun r => D (fun s => r.1 ⟨s.1, h.symm ▸ s.2⟩, r.2)) : ℝ≥0∞)
  else ⊤

/-- The cost `ddhMaskedOTReceiverCost` of one transfer, at the key-derivation mask and the
simulator `maskedOTReceiverSim` with a uniform `msgLen n`-bit word, is at most
`F.kdfDDHMaskedOTReceiverCost`, for every coalition, on inputs whose chosen value has length
`msgLen n`. -/
private theorem ddhMaskedOTReceiverCost_le_kdfDDHMaskedOTReceiverCost
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hS₁ : S₁ {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (J : Finset (Fin 2)) (x : (i : Fin 2) → OTIn (List Bool) i)
    (hout : (otOutputs x 1 : List Bool).length = msgLen n)
    (D : ((i : J) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    ddhMaskedOTReceiverCost (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d)
        (F.kdfPads d) S₁ S₂ () J x D ≤
      F.kdfDDHMaskedOTReceiverCost H msgLen n d S₂ () J x D := by
  by_cases h : J = {1}
  · subst h
    rw [kdfDDHMaskedOTReceiverCost, dite_eq_left rfl, ddhMaskedOTReceiverCost, dite_eq_left rfl,
      hS₁, F.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdfAt H msgLen n d hH x hout]
  · rw [kdfDDHMaskedOTReceiverCost, dite_eq_right h]
    exact le_top

end Cslib.Crypto.PrimeOrderGroupFamily

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

/-! ### Yao's protocol, corrupted evaluator -/

/-- Along `k` sequential single transfers the cost sum `Composition.replacementCost` is monotone
in the cost on the queries that the transfers make: the queries of transfer `j` are those of the
initial states, so a bound of `cost` by `cost'` at these `k` query pairs, for every coalition and
test, suffices. `Composition.replacementCost_mono` asks for the bound at all queries. -/
private theorem replacementCost_seqOTSteps_mono {M : Type} {Out : Fin 2 → Type}
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    {cost cost' : Unit → (J : Finset (Fin 2)) → ((s : Fin 2) → OTIn M s) →
      ((((s : J) → PartyView (OTIn M) Coins₂ sc₂ s) × ((s : Fin 2) → OTOut M s)) →
        ProbComp Bool) → ℝ≥0∞}
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (k : ℕ) {State : Fin 2 → Type}
    (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s) (st : (i : Fin 2) → State i)
    (h : ∀ j J D', cost () J (fun s => query j s (st s)) D' ≤
      cost' () J (fun s => query j s (st s)) D')
    (D : ((i : I) → Schedule.SubCoins (fun _ => Coins₂) (seqBatchOTSchedule k M) i.1 ×
        Schedule.Received (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i.1) ×
      ((i : Fin 2) → Out i) → ProbComp Bool) :
    replacementCost cost (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I
        (seqOTSteps k query output) st D ≤
      replacementCost cost' (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I
        (seqOTSteps k query output) st D := by
  induction k generalizing State with
  | zero => rw [seqOTSteps, replacementCost, replacementCost]
  | succ k ih =>
    rw [seqOTSteps, replacementCost, replacementCost]
    refine add_le_add (h 0 _ _) (tsum_le_tsum fun r => mul_le_mul' le_rfl ?_)
    refine ih _ _ _ ?_ _
    exact fun j J D' => h j.succ J D'

/-- When both values offered in every transfer of a batch have length `ℓ`, so does the value that
the receiver obtains in transfer `j`. -/
private theorem length_otOutputs_batchOTQueryAt {k : ℕ}
    (q : (s : Fin 2) → (batchOTSpec k (List Bool)).Query () s) (ℓ : ℕ)
    (h : ∀ (j : Fin k) (b : Bool), (q 0 j b).length = ℓ) (j : Fin k) :
    (otOutputs (fun s => batchOTQueryAt j s (q s)) 1 : List Bool).length = ℓ :=
  (congrArg List.length (congrFun (otOutputs_batchOTQueryAt q 1) j)).trans (h j (q 1 j))

namespace Yao

open Cslib.Crypto.Garbling

variable {Fn Λ : Type} {Gs : Scheme Fn}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed security parameter, fixed group parameters and a fixed
instance, with no efficiency certificate for any reduction and no hardness assumption applied. The
`prv.sim` advantage, the key-derivation advantages and the DDH advantages are left as explicit
terms, and nothing is assumed about them.

At every parameter `n ≥ 1` and group parameters `d` of the family `F`, when the garbling scheme
`Gs` is correct with a projective encoding, every key `H (d, F.encode d r)` has length `msgLen n`
and so do the values offered in the transfers (`hlen`), the semi-honest advantage of `D` against
Yao's protocol over the batched masked transfer with the key-derivation mask `F.kdfMask H d` and
the pads `F.kdfPads d` over the DDH transfer in `F.Carrier d`, for the coalition `{1}`, with the
simulator composed from `Yao.evaluatorSim Gs Φ S`, simulators `S₁` of `maskedOT` whose member at
`{1}` is `maskedOTReceiverSim` with a uniform `msgLen n`-bit word and simulators `S₂` of the DDH
transfer whose member at `{1}` is `ddhOTReceiverSim`, is at most

* the `prv.sim` advantage of the explicit reduction `Yao.evaluatorDistinguisherToPrvSim`, plus
* the expectation, over the parties' coins `r`, of `Composition.replacementCost` of the
  per-transfer cost `F.kdfDDHMaskedOTReceiverCost` along the `c.evaluatorLen` sequential transfers
  on the queries `Yao.transferQueries n c x r`, for the test `Yao.transferDistinguisher`: the sum
  over the transfers of the expected advantage of the explicit key-derivation distinguisher
  `F.maskedOTReceiverToKDFDistinguisherAt` between `F.kdfIdealGame` and `F.kdfRealGame` under the
  setup that returns `d`, plus the expected fixed-group DDH advantage of
  `maskedOTToDDHDistinguisher`, the expectation being over the real executions of the earlier
  transfers and over the sender's pads.

The hypothesis `hlen` says that, on the inputs `x` and for all coins, both values that the garbler
offers in every transfer (`Yao.transferQueries`) have length `msgLen n`: the mask works at the
width of the key, so a transfer of values of another length is not correct. It is a hypothesis on
the labels of `Gs` at these inputs and is not derived from a property of the scheme here. -/
theorem semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_evaluator_le
    (F : PrimeOrderGroupFamily) (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params Gs) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (x : (i : Fin 2) → Input c i)
    (hlen : ∀ (r : (i : Fin 2) → Coins i) (j : Fin c.evaluatorLen) (b : Bool),
      (transferQueries n c x r 0 j b).length = msgLen n)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {1} = evaluatorSim Gs Φ S n c)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hS₁ : S₁ {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {1} = ddhOTReceiverSim (F.generator d) (F.order d))
    (D : ((i : ({1} : Finset (Fin 2))) →
      PartyView (Input c)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          Coins (schedule c))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          (schedule c)) i) × ((i : Fin 2) → List Bool) → ProbComp Bool) :
    (semiHonestAdvantage
        (composedProtocol Gs n c (ddhMaskedBatchOT c.evaluatorLen (F.generator d) (F.order d)
          (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)))
        noOracleWorld (functionality Gs c) {1}
        (composeSim (protocol Gs n c) T₁
          (fun _ => ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d)
            (F.kdfPads d) S₁ S₂) {1})
        x D : ℝ≥0∞) ≤
      prvSimAdvantage Gs Φ n (S n) (evaluatorDistinguisherToPrvSim c x
          (composeDistinguisher (protocol Gs n c)
            (fun _ => ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d)
              (F.kdfPads d) S₁ S₂) {1} x D)) +
        ∑' r, ProbComp.eval (OracleComp.pi (protocol Gs n c).sampleCoins) r *
          replacementCost (F.kdfDDHMaskedOTReceiverCost H msgLen n d S₂)
            (otWorld (List Bool)) noOracleWorld
            (fun _ => ddhMaskedOT (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d)
              (F.kdfPads d))
            (fun _ => ddhMaskedOTSim (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂)
            (subCoalition (Function.Embedding.refl (Fin 2)) {1})
            (seqBatchOT c.evaluatorLen (List Bool)).steps
            (fun i => (transferQueries n c x r i, ()))
            (fun res => transferDistinguisher n c
              (fun _ => ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d)
                (F.kdfPads d) S₁ S₂) {1} x r D
              (fun i => ⟨transferQueries n c x r i.1, ((), (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  refine (semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le hproj hcorrect hn c Φ S
    (F.generator d) (F.order d) (F.smul_generator_surjective d) (F.kdfMask H d) (F.kdfMask H d)
    (F.kdfPads d) T₁ hT₁ S₁ S₂ hS₂ x D).trans
    (add_le_add le_rfl (tsum_le_tsum fun r => mul_le_mul' le_rfl ?_))
  -- The costs, world, subprotocol and simulators are given by name, as in
  -- `semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le`.
  refine replacementCost_seqOTSteps_mono
    (cost := ddhMaskedOTReceiverCost (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d)
      (F.kdfPads d) S₁ S₂)
    (cost' := F.kdfDDHMaskedOTReceiverCost H msgLen n d S₂)
    noOracleWorld
    (ddhMaskedOT (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
    (ddhMaskedOTSim (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂)
    (subCoalition (Function.Embedding.refl (Fin 2)) {1}) c.evaluatorLen _ _ _
    (fun j J D' => ?_) _
  exact F.ddhMaskedOTReceiverCost_le_kdfDDHMaskedOTReceiverCost H msgLen n d hH S₁ hS₁ S₂ J _
    (length_otOutputs_batchOTQueryAt (transferQueries n c x r) (msgLen n) (hlen r) j) D'

end Yao

/-! ### Yao's protocol, corrupted garbler -/

/-- Along `k` sequential single transfers the hybrid bound `Composition.replacementBound` is zero
when every test has advantage zero against `Sub`, for the coalition `I`, on the queries that the
transfers make: the queries of transfer `j` are those of the initial states.
`replacementBound_seqOTSteps_le` asks for the bound at all queries. -/
private theorem replacementBound_seqOTSteps_eq_zero {M : Type} {Out : Fin 2 → Type}
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (k : ℕ) {State : Fin 2 → Type}
    (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s) (st : (i : Fin 2) → State i)
    (h : ∀ j D', semiHonestAdvantage Sub W₂ (otFunctionality M) I (S₂ I)
      (fun s => query j s (st s)) D' = 0)
    (D : ((i : I) → Schedule.SubCoins (fun _ => Coins₂) (seqBatchOTSchedule k M) i.1 ×
        Schedule.Received (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i.1) ×
      ((i : Fin 2) → Out i) → ProbComp Bool) :
    replacementBound (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I (seqOTSteps k query output) st
      D = 0 := by
  refine nonpos_iff_eq_zero.mp ?_
  induction k generalizing State with
  | zero => rw [seqOTSteps, replacementBound]
  | succ k ih =>
    rw [seqOTSteps, replacementBound]
    -- The coalition of the transfer is `subCoalition _ I`, which is `I` only propositionally.
    have h0 : ∀ J, J = I → ∀ D', (semiHonestAdvantage Sub W₂ (otFunctionality M) J (S₂ J)
        (fun s => query 0 s (st s)) D' : ℝ≥0∞) = 0 := by
      rintro J rfl D'
      rw [h 0 D', ENNReal.coe_zero]
    calc _ ≤ 0 + ∑' r, (Sub.realJoint W₂ (subCoalition (Function.Embedding.refl (Fin 2)) I)
            (fun s => query 0 s (st s))) r * 0 := by
          refine add_le_add (le_of_eq (h0 _ (Finset.ext fun _ => mem_subCoalition) _))
            (tsum_le_tsum fun r => mul_le_mul' le_rfl ?_)
          refine ih _ _ _ ?_ _
          exact fun j D' => h j.succ D'
      _ = 0 := by simp

/-- The batched masked transfer over the DDH transfer with the key-derivation mask has advantage
zero against a corrupted sender, on a query tuple `q` in which both values offered in every
transfer have the length `ℓ` of the keys: on words of that length the mask inverts itself. -/
private theorem semiHonestAdvantage_kdfDDHMaskedBatchOT_sender (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (ℓ : ℕ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = ℓ) (k : ℕ)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hS₁ : S₁ {0} = maskedOTSenderSim (F.kdfPads d))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {0} = ddhOTSenderSim (F.generator d) (F.order d))
    (q : (s : Fin 2) → (batchOTSpec k (List Bool)).Query () s)
    (hq : ∀ (j : Fin k) (b : Bool), (q 0 j b).length = ℓ)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView ((batchOTSpec k (List Bool)).Query ())
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d))
            (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
          (fun _ => Unit) (seqBatchOTSchedule k (List Bool)))
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
            (maskedOTSchedule (F.Carrier d) (List Bool)))
          (seqBatchOTSchedule k (List Bool))) i) ×
      ((i : Fin 2) → (batchOTSpec k (List Bool)).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage
      (ddhMaskedBatchOT k (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d)
        (F.kdfPads d))
      noOracleWorld (batchOTFunctionality k (List Bool)) {0}
      (ddhMaskedBatchOTSim k (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂ {0}) q D =
      0 := by
  have h := semiHonestAdvantage_seqBatchOT_compose_le k (List Bool) noOracleWorld
    (ddhMaskedOT (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
    (ddhMaskedOTSim (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂) {0} q D
  refine ENNReal.coe_eq_zero.mp (nonpos_iff_eq_zero.mp (h.trans (le_of_eq ?_)))
  -- The world, subprotocol and simulators are given by name, so that the goal fixes the queries
  -- before the hypothesis on them is elaborated.
  refine replacementBound_seqOTSteps_eq_zero noOracleWorld
    (ddhMaskedOT (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
    (ddhMaskedOTSim (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂) {0} k _ _ _
    (fun j D' => ?_) _
  exact semiHonestAdvantage_ddhMaskedOT_sender (F.generator d) (F.order d) (F.kdfMask H d)
    (F.kdfMask H d) (F.kdfPads d) S₁ S₂ hS₁ hS₂ _
    (fun r => F.kdfMask_kdfMask H d r
      ((length_otOutputs_batchOTQueryAt q ℓ hq j).trans (hH r).symm)) D'

namespace Yao

open Cslib.Crypto.Garbling

variable {Fn : Type} {Gs : Scheme Fn}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete statement at a fixed security parameter, fixed group parameters and a fixed
instance, with no efficiency certificate for the simulator.

At every parameter `n ≥ 1`, when the garbling scheme `Gs` is correct with a projective encoding and
the keys `H (d, F.encode d r)` have length `msgLen n`, the semi-honest advantage of `D` against
Yao's protocol over the batched masked transfer over the DDH transfer with the key-derivation mask,
`Yao.composedProtocol Gs n c (ddhMaskedBatchOT …)` with the mask `F.kdfMask H d` and the pads
`F.kdfPads d` over the group `F.Carrier d` with generator `F.generator d`, for the coalition `{0}`,
is zero. The simulator is composed from simulators `T₁` of `Yao.protocol` whose member at `{0}` is
`Yao.garblerSim Gs n c`, simulators `S₁` of `maskedOT` whose member at `{0}` is
`maskedOTSenderSim (F.kdfPads d)` and simulators `S₂` of the DDH transfer whose member at `{0}` is
`ddhOTSenderSim (F.generator d) (F.order d)`.

The advantage is zero, with no hardness assumption, because the garbler is the sender of every
transfer. `Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_garbler_eq_zero` does not apply:
it asks that unmasking invert masking on every word, and `F.kdfMask H d` inverts itself only on
words of the key's length.

The hypothesis `hlen` says that, on the inputs `x` and for all coins, both values that the garbler
offers in every transfer (`Yao.transferQueries`) have length `msgLen n`: the mask works at the
width of the key, so a transfer of values of another length is not correct. It is a hypothesis on
the labels of `Gs` at these inputs and is not derived from a property of the scheme here. -/
theorem semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_garbler_eq_zero
    (F : PrimeOrderGroupFamily) (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params Gs) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (x : (i : Fin 2) → Input c i)
    (hlen : ∀ (r : (i : Fin 2) → Coins i) (j : Fin c.evaluatorLen) (b : Bool),
      (transferQueries n c x r 0 j b).length = msgLen n)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {0} = garblerSim Gs n c)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hS₁ : S₁ {0} = maskedOTSenderSim (F.kdfPads d))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {0} = ddhOTSenderSim (F.generator d) (F.order d))
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoins (F.order d))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          Coins (schedule c))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          (schedule c)) i) × ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage
        (composedProtocol Gs n c (ddhMaskedBatchOT c.evaluatorLen (F.generator d) (F.order d)
          (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)))
        noOracleWorld (functionality Gs c) {0}
        (composeSim (protocol Gs n c) T₁
          (fun _ => ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d)
            (F.kdfPads d) S₁ S₂) {0})
        x D = 0 := by
  have h := semiHonestAdvantage_composedProtocol_garbler_le_transfer hproj hcorrect hn c
    (ddhMaskedBatchOT c.evaluatorLen (F.generator d) (F.order d) (F.kdfMask H d) (F.kdfMask H d)
      (F.kdfPads d)) noOracleWorld T₁ hT₁
    (fun _ => ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)
      S₁ S₂) x D
  -- The coalition of the transfer is `subCoalition _ {0}`, which is `{0}` only propositionally.
  -- The query tuple is a variable here, so that `Yao.transferQueries` is never unfolded.
  have h0 : ∀ J, J = ({0} : Finset (Fin 2)) →
      ∀ q : (s : Fin 2) → (batchOTSpec c.evaluatorLen (List Bool)).Query () s,
      (∀ (j : Fin c.evaluatorLen) (b : Bool), (q 0 j b).length = msgLen n) → ∀ D',
      (semiHonestAdvantage
        (ddhMaskedBatchOT c.evaluatorLen (F.generator d) (F.order d) (F.kdfMask H d)
          (F.kdfMask H d) (F.kdfPads d))
        noOracleWorld (batchOTFunctionality c.evaluatorLen (List Bool)) J
        (ddhMaskedBatchOTSim c.evaluatorLen (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) S₁ S₂ J)
        q D' : ℝ≥0∞) = 0 := by
    rintro J rfl q hq D'
    rw [semiHonestAdvantage_kdfDDHMaskedBatchOT_sender F H (msgLen n) d hH c.evaluatorLen S₁ hS₁
      S₂ hS₂ q hq D', ENNReal.coe_zero]
  rw [tsum_eq_zero_iff.mpr fun r => by
    rw [h0 _ (Finset.ext fun _ => mem_subCoalition) (transferQueries n c x r) (hlen r), mul_zero],
    nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h
  exact h

end Yao

end Cslib.Crypto.Protocols.MPC
