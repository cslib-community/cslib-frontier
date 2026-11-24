/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.Yao.Family

/-!
# Yao's protocol over an oblivious-transfer subprotocol: first composition step

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. `Yao.oneSidedProtocol` and
`Yao.protocol` run in the ideal `batchOTWorld` oblivious-transfer hybrid model. Here the ideal
transfer round is replaced by an arbitrary two-party subprotocol `OT` for the batched transfer
(`Protocol.compose`), which gives the protocols whose security Theorem 7 states when `OT` is a
plain-model oblivious-transfer protocol:

* `Yao.composedOneSidedProtocol G n c OT`: the one-sided protocol over `OT`;
* `Yao.composedProtocol G n c OT`: the two-output protocol over `OT`.

The first property proved is for a corrupted garbler, at a fixed parameter, input tuple and
distinguisher. With the composed simulator built from the hybrid garbler simulator (`Yao.garblerSim`
or `Yao.oneSidedGarblerSim`) and any simulators `S₂` for `OT`, the semi-honest advantage against the
composed protocol is at most the oblivious-transfer replacement gap: the distance between the
hybrid execution in `batchOTWorld`, with the garbler's view of the transfer produced by `S₂`, and
the real execution over `OT` (`Yao.semiHonestAdvantage_composedProtocol_garbler_le`,
`Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le`). The hybrid garbler simulators are
exact, so the hybrid term of `semiHonestAdvantage_compose_le` vanishes.

## What is not proved

These bounds are concrete and leave the replacement gap as an explicit term. The following parts of
Theorem 7 remain open (#6045):

* bounding the replacement gap by the semi-honest security of a concrete oblivious-transfer
  protocol, such as the DDH protocol of
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure`, which transfers one
  group element rather than a batch of token words;
* a corrupted evaluator, where the hybrid term is the garbling scheme's simulation privacy;
* the asymptotic statement `ProtocolFamily.SemiHonestSecure` for the composed family, with strict
  PPT certificates for the composed simulators and for the reductions.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; locator not re-verified against primary PDF.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.composedOneSidedProtocol`,
  `Cslib.Crypto.Protocols.MPC.Yao.composedProtocol`: Yao's protocols with the batched transfer run
  by a subprotocol.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_garbler_le`: against a
  corrupted garbler, the advantage is at most the oblivious-transfer replacement gap.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling Cslib.Probability

variable {Fn : Type} (G : Scheme Fn)

/-- **One-sided Yao's protocol over a transfer subprotocol**: `Yao.oneSidedProtocol G n c` with its
batched oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedOneSidedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c)) (fun _ => List Bool) :=
  (oneSidedProtocol G n c).compose fun _ => OT

/-- **Yao's protocol over a transfer subprotocol** (Protocol 2 of [LindellPinkas2009], with the
transfers run by one subprotocol for the whole batch): `Yao.protocol G n c` with its batched
oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (schedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c)) (fun _ => List Bool) :=
  (protocol G n c).compose fun _ => OT

variable {G}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete bound that leaves the oblivious-transfer replacement gap as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedOneSidedProtocol G n c OT` for the coalition `{0}`, with the
simulator composed from `Yao.oneSidedGarblerSim` and any simulators `S₂` for `OT`, is at most the
distance between the hybrid execution in `batchOTWorld` against the reduction
`composeDistinguisher`, which produces the garbler's view of the transfer with `S₂`, and the real
execution over `OT`. -/
theorem semiHonestAdvantage_composedOneSidedProtocol_garbler_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (oneSidedSchedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {0} = oneSidedGarblerSim G n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedOneSidedProtocol G n c OT) W₂ (oneSidedFunctionality G c) {0}
        (composeSim (oneSidedProtocol G n c) S₁ S₂ {0}) x D ≤
      Game.advantage
        (((oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x).bind
          fun r => ProbComp.eval (composeDistinguisher (oneSidedProtocol G n c) S₂ {0} x D r))
        (((composedOneSidedProtocol G n c OT).realJoint W₂ {0} x).bind fun r =>
          ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (oneSidedProtocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (oneSidedFunctionality G c) S₁ (fun _ => OT) S₂
    {0} x D
  have h0 : semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (oneSidedFunctionality G c) {0} (S₁ {0}) x
      (composeDistinguisher (oneSidedProtocol G n c) S₂ {0} x D) = 0 := by
    rw [hS₁]
    exact (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
      (idealJoint_oneSidedGarblerSim hproj hcorrect hn c x) _
  rwa [h0, zero_add] at h

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete bound that leaves the oblivious-transfer replacement gap as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedProtocol G n c OT` for the coalition `{0}`, with the simulator
composed from `Yao.garblerSim` and any simulators `S₂` for `OT`, is at most the distance between
the hybrid execution in `batchOTWorld` against the reduction `composeDistinguisher`, which
produces the garbler's view of the transfer with `S₂`, and the real execution over `OT`. -/
theorem semiHonestAdvantage_composedProtocol_garbler_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {0} = garblerSim G n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) {0}
        (composeSim (protocol G n c) S₁ S₂ {0}) x D ≤
      Game.advantage
        (((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x).bind
          fun r => ProbComp.eval (composeDistinguisher (protocol G n c) S₂ {0} x D r))
        (((composedProtocol G n c OT).realJoint W₂ {0} x).bind fun r => ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (protocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (functionality G c) S₁ (fun _ => OT) S₂ {0} x D
  have h0 : semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (functionality G c) {0} (S₁ {0}) x
      (composeDistinguisher (protocol G n c) S₂ {0} x D) = 0 := by
    rw [hS₁]
    exact (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
      (idealJoint_garblerSim hproj hcorrect hn c x) _
  rwa [h0, zero_add] at h

end Cslib.Crypto.Protocols.MPC.Yao
