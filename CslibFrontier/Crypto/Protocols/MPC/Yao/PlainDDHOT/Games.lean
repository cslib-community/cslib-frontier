/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT.SequentialProg
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDFDDHProb
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainChallenge
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.GarblerSetup
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.LabelLength
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Setup

/-!
# Yao's protocol in the plain model as a protocol family: bounds in library games

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It packages the plain-model protocol

* Yao's protocol `Yao.protocol Gs n (c n)`, with its batched transfer run by `seqBatchOT`,
* every single transfer run by `maskedOT` with the key-derivation mask `F.kdfMask H d` and the
  fair-coin pads `F.kdfPadsProb n d`,
* the pad transfer run by the fair-coin DDH transfer `F.ddhOTProbProtocol n d`,

as a `ProtocolFamily` whose public parameters are the group descriptions of `F`, and bounds, at
every security parameter, the advantage of an `Environment` between `ProtocolFamily.idealGame`,
with the composed simulators, and `ProtocolFamily.realGame`, for each corrupted party. The group
description is drawn by the setup, the environment chooses the inputs with a program that sees it,
and every adversary of a bound is one explicit program.

## What is proved

* `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le` (corrupted evaluator): at every
  parameter `n ≥ 1`, the advantage of an environment `Z` is at most
  * the `prv.sim` advantage of the adversary `Yao.kdfDDHProbEnvToPrvSim`, which draws `d` with the
    setup program, runs the choosing stage of `Z` and then `composeDistinguisher`, plus
  * for every transfer `j < (c n).evaluatorLen`,
    * the advantage between `F.kdfIdealGame` and `F.kdfRealGame` (the games of `F.SecureKDF`) of
      the distinguisher `F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)`,
    * the advantage between `F.ddhRealGame` and `F.ddhRandomGame` (the games of `F.DDH`) of the
      distinguisher `F.roundEnvToDDHDistinguisher (F.padTransferEnv H F.kdfPadsProb S₂ E)`, and
    * `18 / 2 ^ n`,

    where `E = Yao.kdfDDHTransferEnv … Z j` is the environment program of transfer `j`: it runs
    the choosing stage of `Z`, garbles, runs the earlier transfers with the real protocol and stops
    at transfer `j`.

  The setup law of the key-derivation and DDH games is the distribution of the setup program. The
  absolute value of each of these advantages is outside the expectation over the setup, the
  choice of the environment, the garbler's coins and the earlier transfers. The label length is
  the property `Gs.HasTokenLength` of the garbling scheme.
* `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le` (corrupted garbler): at every
  parameter `n ≥ 1` and for every setup law, the advantage of an environment is at most
  `(c n).evaluatorLen * (2 / 2 ^ n)`, a statistical bound.

## What is not proved

* **No efficiency certificate and no asymptotic statement.** None of the three adversaries of the
  evaluator bound is shown to be uniform strict PPT, no hardness assumption (`F.DDH`,
  `F.SecureKDF`, `prv.sim` security of `Gs`) is applied, the composed simulators are not shown to
  be PPT, no `ProtocolFamily.Encoding` of the family is given, and
  `ProtocolFamily.SemiHonestSecure` is not stated for it (#6045). The number of transfers is
  `(c n).evaluatorLen`; nothing here bounds it.
* The sum over the transfers has one key-derivation and one DDH distinguisher per transfer `j`;
  no single distinguisher that samples `j` is built here (#6045).

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; they were not re-verified against the source.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbFamily`: the plain-model protocol as a family.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbSim`: its composed simulator family.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbEnvToPrvSim`: the `prv.sim` adversary of an
  environment.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHTransferEnv`: the environment program of one transfer.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le`
* `Cslib.Crypto.Protocols.MPC.Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le`

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Garbling
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

variable {Fn Λ : Type} {Gs : Scheme Fn}

/-- **Yao's protocol in the plain model as a protocol family**: at the security parameter `n` and
the group description `d` of `F`, Yao's protocol `Yao.protocol Gs n (c n)` with its batched
transfer run by `seqBatchOT`, every single transfer run by `maskedOT` with the key-derivation mask
`F.kdfMask H d` and the fair-coin pads `F.kdfPadsProb n d`, and the pad transfer run by the
fair-coin DDH transfer `F.ddhOTProbProtocol n d`, with no oracle, for the functionality
`Yao.functionality Gs (c n)`. The exponents of the pads and of the DDH transfer are reduced
fair-coin bit strings. -/
noncomputable abbrev kdfDDHProbFamily (Gs : Scheme Fn) (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs) : ProtocolFamily 2 where
  Desc := F.Desc
  spec _ _ := noOracleSpec
  sc n d := Schedule.compose
    (fun _ => Schedule.compose
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
    (schedule (c n))
  In n _ := Input (c n)
  Coins n d := Schedule.ComposedCoins
    (fun _ => Schedule.ComposedCoins
      (fun _ => Schedule.ComposedCoins
        (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
    Yao.Coins (schedule (c n))
  Out _ _ _ := List Bool
  protocol n d := (protocol Gs n (c n)).compose fun _ =>
    (seqBatchOT (c n).evaluatorLen (List Bool)).compose fun _ =>
      (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)).compose fun _ =>
        F.ddhOTProbProtocol n d
  world _ _ := noOracleWorld
  functionality n _ := functionality Gs (c n)

/-- **The composed simulator family** of `Yao.kdfDDHProbFamily` for the coalition `I`:
`composeSim` of the simulators `T₁ n` of Yao's protocol, `seqBatchOTSim`, the simulators `Sm n d`
of the masked transfer and the simulators `S₂ n d` of the DDH transfer. No efficiency is claimed
for it. -/
@[expose] noncomputable def kdfDDHProbSim (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2)) : SimulatorFamily (kdfDDHProbFamily Gs F H c) I :=
  fun n d => composeSim (protocol Gs n (c n)) (T₁ n)
    (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
      (seqBatchOTSim (c n).evaluatorLen (List Bool))
      (fun _ J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d))
        (Sm n d) (fun _ => S₂ n d) J) J) I

/-- **The `prv.sim` adversary of an environment** against `Yao.kdfDDHProbFamily` with a corrupted
evaluator, at the parameter `n`: `Yao.evaluatorEnvToPrvSim` whose first stage draws the group
description `d` with the setup program and runs the choosing stage of `Z`, and whose guess is
`composeDistinguisher` of Yao's protocol applied to the guessing stage of `Z`, which simulates the
batched transfer. No efficiency is claimed for it. -/
@[expose] noncomputable def kdfDDHProbEnvToPrvSim (F : PrimeOrderGroupFamily)
    (setup : ℕ → ProbComp F.Desc) (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {1}) (n : ℕ) :
    PrvSimAdversary Fn (Σ d : F.Desc, InputChoice (kdfDDHProbFamily Gs F H c) n d) :=
  evaluatorEnvToPrvSim (c n)
    (do
      let d ← setup n
      let ch ← Z.choose n d
      return ⟨d, ch⟩)
    (fun a => a.2.inputs) fun a =>
      composeDistinguisher (protocol Gs n (c n))
        (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
          (seqBatchOTSim (c n).evaluatorLen (List Bool))
          (fun _ J => composeSim
            (maskedOT (F.kdfMask H a.1) (F.kdfMask H a.1) (F.kdfPadsProb n a.1)) (Sm n a.1)
            (fun _ => S₂ n a.1) J) J)
        {1} a.2.inputs (Z.guess n a.1 a.2.state)

/-- **The environment program of transfer `j`** of `Yao.kdfDDHProbFamily` at the parameter `n` and
the group description `d`, for a corrupted evaluator and an environment `Z`: the choosing stage of
`Z` followed by `composeSeqBatchOTRoundEnvProg` of `Yao.protocol` at its one batched call. It
chooses the inputs, samples the garbler's coins, runs the transfers before `j` with the real
protocol in the plain model and stops at transfer `j` with a challenge whose guessing stage
simulates the later transfers and runs the guessing stage of `Z`. No efficiency is claimed for
it. -/
@[expose] noncomputable def kdfDDHTransferEnv (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {1}) (j n : ℕ) (d : F.Desc) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))) := do
  let ch ← Z.choose n d
  composeSeqBatchOTRoundEnvProg (c n).evaluatorLen (List Bool) (protocol Gs n (c n)) noOracleWorld
    ((maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)).compose fun _ =>
      F.ddhOTProbProtocol n d)
    (fun J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)) (Sm n d)
      (fun _ => S₂ n d) J)
    {1} ch.inputs (Z.guess n d ch.state) 0 j

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a bound on advantages at each parameter, with no efficiency certificate for any of the
three adversaries and no hardness assumption applied.

Let the group description `d` be drawn by the setup program `setup n`, and let `Z` be an
environment against the plain-model family `Yao.kdfDDHProbFamily Gs F H c` with a corrupted
evaluator. At every parameter `n ≥ 1`, when the garbling scheme `Gs` is correct with a projective
encoding and tokens of length `msgLen n` (`Gs.HasTokenLength`), every derived key
`H (d, F.encode d r)` has length `msgLen n`, and the simulators at the coalition `{1}` are
`Yao.evaluatorSim Gs Φ S n (c n)` for Yao's protocol, `maskedOTReceiverSim` with the fair-coin pads
and a uniform `msgLen n`-bit word for the masked transfer and `F.ddhOTReceiverSimProb n d` for the
DDH transfer, the advantage of `Z` between `ProtocolFamily.idealGame` with the composed simulator
family `Yao.kdfDDHProbSim` and `ProtocolFamily.realGame` is at most

* the `prv.sim` advantage against `S n` of the one adversary `Yao.kdfDDHProbEnvToPrvSim`, which
  runs the setup program, the choosing stage of `Z` and `composeDistinguisher`, plus
* the sum over the transfers `j < (c n).evaluatorLen` of the advantage between `F.kdfIdealGame`
  and `F.kdfRealGame` of the one distinguisher built from `Yao.kdfDDHTransferEnv … Z j` by
  `F.padHidingEnv` and `F.roundEnvToKDFDistinguisher`, the advantage between `F.ddhRealGame` and
  `F.ddhRandomGame` of the one distinguisher built from it by `F.padTransferEnv` and
  `F.roundEnvToDDHDistinguisher`, and `18 / 2 ^ n`: `4 / 2 ^ n` for the fair-coin exponents of the
  pads and `14 / 2 ^ n` for those of the DDH transfer.

The setup law of the key-derivation and DDH games is the distribution of the setup program. Each
of these advantages is the absolute difference of two acceptance probabilities of one adversary,
outside the expectation over the setup, the choice of the environment, the garbler's coins and
the earlier transfers. -/
theorem advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → ProbComp F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (c : ℕ → Params Gs) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {1})
    {n : ℕ} (hn : 0 < n)
    (hT₁ : T₁ n {1} = evaluatorSim Gs Φ S n (c n))
    (hSm : ∀ d, Sm n d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPadsProb n d)
      (Cslib.BitString.sampleList (msgLen n)))
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hlabel : Gs.HasTokenLength n (c n).fn (msgLen n)) :
    Game.advantage
        ((kdfDDHProbFamily Gs F H c).idealGame (fun n => ProbComp.eval (setup n)) {1}
          (kdfDDHProbSim F H c T₁ Sm S₂ {1}) Z n)
        ((kdfDDHProbFamily Gs F H c).realGame (fun n => ProbComp.eval (setup n)) {1} Z n) ≤
      prvSimAdvantage Gs Φ n (S n) (kdfDDHProbEnvToPrvSim F setup H c Sm S₂ Z n) +
        ∑ j ∈ Finset.range (c n).evaluatorLen,
          (Game.advantage
              (F.kdfIdealGame (fun n => ProbComp.eval (setup n)) msgLen
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H F.kdfPadsProb S₂ (kdfDDHTransferEnv F H c Sm S₂ Z j))) n)
              (F.kdfRealGame (fun n => ProbComp.eval (setup n)) H
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H F.kdfPadsProb S₂ (kdfDDHTransferEnv F H c Sm S₂ Z j))) n) +
            (Game.advantage
                (F.ddhRealGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H F.kdfPadsProb S₂ (kdfDDHTransferEnv F H c Sm S₂ Z j))) n)
                (F.ddhRandomGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H F.kdfPadsProb S₂ (kdfDDHTransferEnv F H c Sm S₂ Z j))) n) +
              18 / 2 ^ n)) := by
  have h := advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_sum hproj hcorrect hn
    (c n) Φ S
    (do
      let d ← setup n
      let ch ← Z.choose n d
      return (⟨d, ch⟩ : Σ d : F.Desc, InputChoice (kdfDDHProbFamily Gs F H c) n d))
    (fun a => F.kdfMask H a.1) (fun a => F.kdfMask H a.1) (fun a => F.kdfPadsProb n a.1)
    (fun _ => noOracleWorld) (fun a => F.ddhOTProbProtocol n a.1) (fun a => Sm n a.1)
    (fun a => S₂ n a.1) (T₁ n) hT₁ (fun a => a.2.inputs) (fun a => Z.guess n a.1 a.2.state)
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_))
  have hE : ∀ d c',
      Sum.inr c' ∈ (ProbComp.eval (kdfDDHTransferEnv F H c Sm S₂ Z j n d)).support →
        c'.coalition = ({1} : Finset (Fin 2)) ∧
          (otOutputs (M := List Bool) c'.query 1 : List Bool).length = msgLen n := by
    intro d c' hc'
    rw [kdfDDHTransferEnv, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc'
    obtain ⟨ch, -, hc'⟩ := hc'
    rw [eval_composeSeqBatchOTRoundEnvProg] at hc'
    exact coalition_length_of_mem_support_composeSeqBatchOTRoundEnv _ _ _ _ _ _ _ _ _ _ _ (msgLen n)
      (fun r hr => forallChallenge_protocol_evaluator n (c n) (msgLen n) ch.inputs r
        (length_transferQueries_garbler hlabel ch.inputs r hr)) hc'
  have hA := F.advantage_bind_padHiding_le_kdf (fun n => ProbComp.eval (setup n)) H msgLen n
    (Sm n) hSm S₂ hH (kdfDDHTransferEnv F H c Sm S₂ Z j) hE
  have hB := F.advantage_bind_padTransfer_le_ddh (fun n => ProbComp.eval (setup n)) H
    F.kdfPadsProb n S₂ hS₂ (kdfDDHTransferEnv F H c Sm S₂ Z j) fun d c' hc' => (hE d c' hc').1
  simp only [kdfDDHTransferEnv, ProbComp.eval_bind, PMF.bind_bind,
    eval_composeSeqBatchOTRoundEnvProg] at hA hB
  have h18 : (18 : ℝ≥0) / 2 ^ n = 4 / 2 ^ n + 14 / 2 ^ n := by
    rw [← add_div]
    norm_num
  refine (add_le_add hA hB).trans_eq ?_
  rw [h18]
  ring

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a statistical bound at each parameter; the composed simulator is not shown to be
efficient and no asymptotic statement is made.

Let the group description be drawn from any setup law, and let `Z` be an environment against the
plain-model family `Yao.kdfDDHProbFamily Gs F H c` with a corrupted garbler. At every parameter
`n ≥ 1`, when the garbling scheme `Gs` is correct with a projective encoding and tokens of length
`msgLen n` (`Gs.HasTokenLength`), every derived key `H (d, F.encode d r)` has length `msgLen n`,
and the simulators at the coalition `{0}` are `Yao.garblerSim Gs n (c n)` for Yao's protocol,
`maskedOTSenderSim` with the fair-coin pads for the masked transfer and `F.ddhOTSenderSimProb n d`
for the DDH transfer, the advantage of `Z` between `ProtocolFamily.idealGame` with the composed
simulator family `Yao.kdfDDHProbSim` and `ProtocolFamily.realGame` is at most
`(c n).evaluatorLen * (2 / 2 ^ n)`: `2 / 2 ^ n` for the fair-coin exponents of the receiver in
each transfer. No hardness assumption is involved, and the bound holds for every environment. -/
theorem advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (c : ℕ → Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {0})
    {n : ℕ} (hn : 0 < n)
    (hT₁ : T₁ n {0} = garblerSim Gs n (c n))
    (hSm : ∀ d, Sm n d {0} = maskedOTSenderSim (F.kdfPadsProb n d))
    (hS₂ : ∀ d, S₂ n d {0} = F.ddhOTSenderSimProb n d)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hlabel : Gs.HasTokenLength n (c n).fn (msgLen n)) :
    Game.advantage
        ((kdfDDHProbFamily Gs F H c).idealGame setup {0} (kdfDDHProbSim F H c T₁ Sm S₂ {0}) Z n)
        ((kdfDDHProbFamily Gs F H c).realGame setup {0} Z n) ≤
      (c n).evaluatorLen * (2 / 2 ^ n) := by
  simp only [ProtocolFamily.idealGame, ProtocolFamily.realGame, PMF.monad_bind_eq_bind]
  refine Game.advantage_bind_le_nnreal _ _ _ fun d =>
    Game.advantage_bind_le_nnreal _ _ _ fun ch => ?_
  have h := advantage_setup_composedProtocol_maskedOT_ddhOTProb_garbler_le
    (hproj := hproj) (hcorrect := hcorrect) (F := F) (setup := fun _ => pure d)
    (mask := fun d => F.kdfMask H d) (unmask := fun d => F.kdfMask H d)
    (samplePads := fun d => F.kdfPadsProb n d) (c := c) (T₁ := T₁) (Sm := Sm) (S₂ := S₂)
    (hn := hn) (x := fun _ => ch.inputs) (D := fun d' => Z.guess n d' ch.state) (L := msgLen n)
    (hmask := fun d r m hm => F.kdfMask_kdfMask H d r (hm.trans (hH d r).symm))
    (hT₁ := hT₁) (hSm := hSm) (hS₂ := hS₂)
    (hlen := fun _ r hr t b => length_transferQueries_garbler hlabel ch.inputs r hr t b)
  simp only [ProbComp.eval_pure, PMF.pure_bind] at h
  exact h

end Cslib.Crypto.Protocols.MPC.Yao
