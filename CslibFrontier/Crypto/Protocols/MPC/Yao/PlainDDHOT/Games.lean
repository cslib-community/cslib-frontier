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
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Setup

/-!
# Yao's protocol over the masked DDH transfer under a sampled setup: a bound in library games

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It specializes the bound of
`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/Setup.lean` to the plain-model protocol

* Yao's protocol `Yao.protocol Gs n (c n)`, with its batched transfer run by `seqBatchOT`,
* every single transfer run by `maskedOT` with the key-derivation mask `F.kdfMask H d` and the
  pads `F.kdfPads d`,
* the pad transfer run by the fair-coin DDH transfer `F.ddhOTProbProtocol n d`,

for a corrupted evaluator, with the group description `d` drawn by a setup program `setup n`, and
with every term a game of the library against one explicit adversary that runs the setup program or
is given its outcome and samples everything else itself.

## What is proved

`Yao.advantage_setup_composedProtocol_kdfDDHProb_evaluator_le`: at every parameter `n ≥ 1`, the
advantage between the ideal game, with the composed simulator, and the real game, both after
`d ← setup n` with inputs `x n d` and distinguisher `D n d`, is at most

* the `prv.sim` advantage of the adversary `Yao.evaluatorEnvToPrvSim`, which draws `d` with the
  setup program and runs `composeDistinguisher`, plus
* for every transfer `j < (c n).evaluatorLen`,
  * the advantage between `F.kdfIdealGame` and `F.kdfRealGame` (the games of `F.SecureKDF`) of the
    distinguisher `F.roundEnvToKDFDistinguisher H (F.padHidingEnv H S₂ E)`,
  * the advantage between `F.ddhRealGame` and `F.ddhRandomGame` (the games of `F.DDH`) of the
    distinguisher `F.roundEnvToDDHDistinguisher (F.padTransferEnv H S₂ E)`, and
  * `14 / 2 ^ n`,

  where `E = Yao.kdfDDHTransferEnv … j` is the environment program of transfer `j`: it garbles,
  runs the earlier transfers with the real protocol and stops at transfer `j`.

The setup law of the key-derivation and DDH games is the distribution of the setup program. Every
absolute value is outside the expectation over the setup, the garbler's coins and the earlier
transfers.

## What is not proved

* **No efficiency certificate and no asymptotic statement.** None of the three adversaries is
  shown to be uniform strict PPT, no hardness assumption (`F.DDH`, `F.SecureKDF`, `prv.sim`
  security of `Gs`) is applied, and `ProtocolFamily.SemiHonestSecure` is not stated for the composed
  protocol (#6045). The number of transfers is `(c n).evaluatorLen`; nothing here bounds it.
* **The length of the labels is a hypothesis** (`hlen`): both words offered in every transfer
  (`Yao.transferQueries`) have length `msgLen n`, for all group descriptions and all coins in the
  support of the coin sampler. It is not derived from the garbling scheme, and no scheme is
  exhibited that satisfies it with the other
  hypotheses (#6045).
* The pads `F.kdfPads d` have exactly uniform exponents, not fair-coin ones, so the composed
  protocol is not yet a fair-coin program.
* Only the corrupted evaluator is treated here; the corrupted garbler is in
  `CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/KDF.lean` at a fixed group.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; they were not re-verified against the source.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHTransferEnv`: the environment program of one transfer.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.advantage_setup_composedProtocol_kdfDDHProb_evaluator_le`

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

/-- **The environment program of transfer `j`** of Yao's protocol over `seqBatchOT` over `maskedOT`
with the key-derivation mask over the fair-coin DDH transfer, at the parameter `n` and the group
description `d`, for a corrupted evaluator: `composeSeqBatchOTRoundEnvProg` of `Yao.protocol` at
its one batched call. It samples the garbler's coins, runs the transfers before `j` with the real
protocol in the plain model and stops at transfer `j` with a challenge whose guessing stage
simulates the later transfers and runs `D n d`. No efficiency is claimed for it. -/
@[expose] noncomputable def kdfDDHTransferEnv (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (x : (n : ℕ) → F.Desc → (i : Fin 2) → Input (c n) i)
    (D : (n : ℕ) → (d : F.Desc) → ((i : ({1} : Finset (Fin 2))) → PartyView (Input (c n))
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins
              (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          Coins (schedule (c n)))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          (schedule (c n))) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool)
    (j n : ℕ) (d : F.Desc) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))) :=
  composeSeqBatchOTRoundEnvProg (c n).evaluatorLen (List Bool) (protocol Gs n (c n)) noOracleWorld
    ((maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).compose fun _ =>
      F.ddhOTProbProtocol n d)
    (fun J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)) (Sm n d)
      (fun _ => S₂ n d) J)
    {1} (x n d) (D n d) 0 j

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a bound on advantages at each parameter, with no efficiency certificate for any of the
three adversaries, no hardness assumption applied, and the length of the labels as a hypothesis.

Let the group description `d` be drawn by the setup program `setup n`, and let the inputs `x n d`
and the distinguisher `D n d` depend on it. At every parameter `n ≥ 1`, when the garbling scheme
`Gs` is correct with a projective encoding, every derived key `H (d, F.encode d r)` has length
`msgLen n`, both words offered in every transfer have length `msgLen n` for every group
description and all coins in the support of the coin sampler (`hlen`; no scheme satisfying it is
exhibited, #6045), and the simulators at the coalition `{1}` are
`Yao.evaluatorSim Gs Φ S n (c n)` for Yao's protocol, `maskedOTReceiverSim` with a uniform
`msgLen n`-bit word for the masked transfer and `F.ddhOTReceiverSimProb n d` for the DDH transfer,
the advantage between the ideal game with the composed simulator and the real game of Yao's
protocol over `seqBatchOT` over `maskedOT` with the key-derivation mask over
`F.ddhOTProbProtocol n d`, in the plain model, is at most

* the `prv.sim` advantage against `S n` of the one adversary `Yao.evaluatorEnvToPrvSim`, which runs
  the setup program and `composeDistinguisher`, plus
* the sum over the transfers `j < (c n).evaluatorLen` of the advantage between `F.kdfIdealGame`
  and `F.kdfRealGame` of the one distinguisher built from `Yao.kdfDDHTransferEnv … j` by
  `F.padHidingEnv` and `F.roundEnvToKDFDistinguisher`, the advantage between `F.ddhRealGame` and
  `F.ddhRandomGame` of the one distinguisher built from it by `F.padTransferEnv` and
  `F.roundEnvToDDHDistinguisher`, and `14 / 2 ^ n`.

The setup law of the key-derivation and DDH games is the distribution of the setup program. Every
advantage is the absolute difference of two acceptance probabilities of one adversary, outside the
expectation over the setup, the garbler's coins and the earlier transfers. -/
theorem advantage_setup_composedProtocol_kdfDDHProb_evaluator_le
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
    (x : (n : ℕ) → F.Desc → (i : Fin 2) → Input (c n) i)
    (D : (n : ℕ) → (d : F.Desc) → ((i : ({1} : Finset (Fin 2))) → PartyView (Input (c n))
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins
              (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          Coins (schedule (c n)))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          (schedule (c n))) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool)
    {n : ℕ} (hn : 0 < n)
    (hT₁ : T₁ n {1} = evaluatorSim Gs Φ S n (c n))
    (hSm : ∀ d, Sm n d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hlen : ∀ d, ∀ r ∈ (ProbComp.eval (OracleComp.pi (protocol Gs n (c n)).sampleCoins)).support,
      ∀ (t : Fin (c n).evaluatorLen) (b : Bool),
        (transferQueries n (c n) (x n d) r 0 t b).length = msgLen n) :
    Game.advantage
        ((ProbComp.eval (setup n)).bind fun d =>
          (ProbComp.eval (idealJoint (functionality Gs (c n)) {1}
            (composeSim (protocol Gs n (c n)) (T₁ n)
              (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
                (seqBatchOTSim (c n).evaluatorLen (List Bool))
                (fun _ J => composeSim
                  (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)) (Sm n d)
                  (fun _ => S₂ n d) J) J)
              {1}) (x n d))).bind fun r => ProbComp.eval (D n d r))
        ((ProbComp.eval (setup n)).bind fun d =>
          (((protocol Gs n (c n)).compose fun _ =>
            (seqBatchOT (c n).evaluatorLen (List Bool)).compose fun _ =>
              (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).compose fun _ =>
                F.ddhOTProbProtocol n d).realJoint
                  noOracleWorld {1} (x n d)).bind fun r => ProbComp.eval (D n d r)) ≤
      prvSimAdvantage Gs Φ n (S n) (evaluatorEnvToPrvSim (c n) (setup n) (x n) fun d =>
          composeDistinguisher (protocol Gs n (c n))
            (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
              (seqBatchOTSim (c n).evaluatorLen (List Bool))
              (fun _ J => composeSim
                (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)) (Sm n d)
                (fun _ => S₂ n d) J) J)
            {1} (x n d) (D n d)) +
        ∑ j ∈ Finset.range (c n).evaluatorLen,
          (Game.advantage
              (F.kdfIdealGame (fun n => ProbComp.eval (setup n)) msgLen
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H S₂ (kdfDDHTransferEnv F H c Sm S₂ x D j))) n)
              (F.kdfRealGame (fun n => ProbComp.eval (setup n)) H
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H S₂ (kdfDDHTransferEnv F H c Sm S₂ x D j))) n) +
            (Game.advantage
                (F.ddhRealGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H S₂ (kdfDDHTransferEnv F H c Sm S₂ x D j))) n)
                (F.ddhRandomGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H S₂ (kdfDDHTransferEnv F H c Sm S₂ x D j))) n) +
              14 / 2 ^ n)) := by
  have h := advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_sum hproj hcorrect hn
    (c n) Φ S (setup n) (fun d => F.kdfMask H d) (fun d => F.kdfMask H d) (fun d => F.kdfPads d)
    (fun _ => noOracleWorld) (fun d => F.ddhOTProbProtocol n d) (fun d => Sm n d)
    (fun d => S₂ n d) (T₁ n) hT₁ (x n) (D n)
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_))
  have hE : ∀ d c',
      Sum.inr c' ∈ (ProbComp.eval (kdfDDHTransferEnv F H c Sm S₂ x D j n d)).support →
        c'.coalition = ({1} : Finset (Fin 2)) ∧
          (otOutputs (M := List Bool) c'.query 1 : List Bool).length = msgLen n := by
    intro d c' hc'
    rw [kdfDDHTransferEnv, eval_composeSeqBatchOTRoundEnvProg] at hc'
    exact coalition_length_of_mem_support_composeSeqBatchOTRoundEnv _ _ _ _ _ _ _ _ _ _ (msgLen n)
      (fun r hr => forallChallenge_protocol_evaluator n (c n) (msgLen n) (x n d) r (hlen d r hr))
      hc'
  have hA := F.advantage_bind_padHiding_eq_kdf (fun n => ProbComp.eval (setup n)) H msgLen n
    (Sm n) hSm S₂ hH (kdfDDHTransferEnv F H c Sm S₂ x D j) hE
  have hB := F.advantage_bind_padTransfer_le_ddh (fun n => ProbComp.eval (setup n)) H n S₂ hS₂
    (kdfDDHTransferEnv F H c Sm S₂ x D j) fun d c' hc' => (hE d c' hc').1
  simp only [kdfDDHTransferEnv, eval_composeSeqBatchOTRoundEnvProg] at hA hB
  exact add_le_add hA.le hB

end Cslib.Crypto.Protocols.MPC.Yao
