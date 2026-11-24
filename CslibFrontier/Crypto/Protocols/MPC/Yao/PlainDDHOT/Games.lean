/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT.SequentialProg
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDFDDHProb
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.GarblerSetup
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.LabelLength

/-!
# Yao's protocol in the plain model as a protocol family: the family and the corrupted garbler

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It packages the plain-model protocol

* Yao's protocol `Yao.protocol Gs n (c n)`, with its batched transfer run by `seqBatchOT`,
* every single transfer run by `maskedOT` with the key-derivation mask `F.kdfMask H d` and the
  fair-coin pads `F.kdfPadsProb n d`,
* the pad transfer run by the fair-coin DDH transfer `F.ddhOTProbProtocol n d`,

as a `ProtocolFamily` whose public parameters are the group descriptions of `F`, together with its
composed simulator family and, for a corrupted evaluator, the adversary programs built from an
`Environment`. For a corrupted garbler it bounds, at every security parameter, the advantage of an
environment between `ProtocolFamily.idealGame`, with the composed simulators, and
`ProtocolFamily.realGame`. The group description is drawn by the setup, and the environment
chooses the inputs with a program that sees it.

## What is proved

* `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le` (corrupted garbler): at every
  parameter `n ≥ 1` and for every setup law, the advantage of an environment is at most
  `(c n).evaluatorLen * (2 / 2 ^ n)`, a statistical bound. The label length is the property
  `Gs.HasTokenLength` of the garbling scheme.

## What is not proved

* **No bound for a corrupted evaluator is proved in this module.** It defines the two programs
  that such a bound uses: the `prv.sim` adversary `Yao.kdfDDHProbEnvToPrvSim`, which draws `d`
  with the setup program, runs the choosing stage of the environment and then
  `composeDistinguisher`, and the environment program `Yao.kdfDDHTransferEnv` of one transfer `j`,
  which runs the choosing stage of the environment, garbles, runs the earlier transfers with the
  real protocol and stops at transfer `j`. The bound is
  `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul` in
  `CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/DrawnTransfer.lean`, with one key-derivation
  and one DDH distinguisher, built from a program that draws the transfer.
* **No efficiency certificate and no asymptotic statement.** Neither the composed simulators nor
  the two programs above are shown to be uniform strict PPT, no hardness assumption (`F.DDH`,
  `F.SecureKDF`, `prv.sim` security of `Gs`) is applied, no `ProtocolFamily.Encoding` of the
  family is given in this module, and `ProtocolFamily.SemiHonestSecure` is not stated for it
  (#6045). The number of transfers is `(c n).evaluatorLen`; nothing here bounds it.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; they were not re-verified against the source.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbFamily`: the plain-model protocol as a family.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbSim`: its composed simulator family.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbEnvToPrvSim`: the `prv.sim` adversary of an
  environment.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHTransferEnv`: the environment program of one transfer.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le`

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Garbling
open _root_.Cslib.Crypto.Protocols.MPC.Composition

variable {Fn : Type} {Gs : Scheme Fn}

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
  fun n d => composeSim (protocol Gs n (c n)) (T₁ n I)
    (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
      (seqBatchOTSim (c n).evaluatorLen (List Bool) J)
      (fun _ J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d))
        (Sm n d J) (fun _ => S₂ n d)))

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
          (seqBatchOTSim (c n).evaluatorLen (List Bool) J)
          (fun _ J => composeSim
            (maskedOT (F.kdfMask H a.1) (F.kdfMask H a.1) (F.kdfPadsProb n a.1)) (Sm n a.1 J)
            (fun _ => S₂ n a.1)))
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
    (fun J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)) (Sm n d J)
      (fun _ => S₂ n d))
    {1} ch.inputs (Z.guess n d ch.state) 0 j

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a statistical bound at each parameter; the composed simulator is not shown to be
efficient and no asymptotic statement is made.

Let the group description be drawn from any setup law, and let `Z` be an environment against the
plain-model family `Yao.kdfDDHProbFamily Gs F H c` with a corrupted garbler. At every parameter
`n ≥ 1`, when the garbling scheme `Gs` is correct with a projective encoding and tokens of length
`msgLen n` (`Gs.HasTokenLength`), every derived key `H (d, F.encode d r)` has length `msgLen n`
for every group description `d` that the setup law can draw at `n`, and the simulators at the
coalition `{0}` are `Yao.garblerSim Gs n (c n)` for Yao's protocol, `maskedOTSenderSim` with the
fair-coin pads for the masked transfer and `F.ddhOTSenderSimProb n d` for the DDH transfer, the
advantage of `Z` between `ProtocolFamily.idealGame` with the composed simulator family
`Yao.kdfDDHProbSim` and `ProtocolFamily.realGame` is at most `(c n).evaluatorLen * (2 / 2 ^ n)`:
`2 / 2 ^ n` for the fair-coin exponents of the receiver in each transfer. No hardness assumption is
involved, and the bound holds for every environment.

The length of the keys is asked only on the support of `setup n`, so one key derivation `H` can
have keys of a length that grows with `n`, read from the group description. -/
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
    (hH : ∀ d ∈ (setup n).support, ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (hlabel : Gs.HasTokenLength n (c n).fn (msgLen n)) :
    Game.advantage
        ((kdfDDHProbFamily Gs F H c).idealGame setup {0} (kdfDDHProbSim F H c T₁ Sm S₂ {0}) Z n)
        ((kdfDDHProbFamily Gs F H c).realGame setup {0} Z n) ≤
      (c n).evaluatorLen * (2 / 2 ^ n) := by
  simp only [ProtocolFamily.idealGame, ProtocolFamily.realGame, PMF.monad_bind_eq_bind]
  refine Game.advantage_bind_le_of_support _ _ _ fun d hd =>
    Game.advantage_bind_le_nnreal _ _ _ fun ch => ?_
  -- `H'` cuts or pads every key to `msgLen n` bits, and is `H` at the drawn description `d`.
  let H' : F.Desc × List Bool → List Bool :=
    fun p => (H p ++ List.replicate (msgLen n) false).take (msgLen n)
  have hH' (d' : F.Desc) (r : F.Carrier d') : (H' (d', F.encode d' r)).length = msgLen n := by
    simp only [H', List.length_take, List.length_append, List.length_replicate]
    omega
  have hmask : F.kdfMask H' d = F.kdfMask H d := by
    funext r m
    have hkey : H' (d, F.encode d r) = H (d, F.encode d r) := List.take_left' (hH d hd r)
    simp only [PrimeOrderGroupFamily.kdfMask, hkey]
  have h := advantage_setup_composedProtocol_maskedOT_ddhOTProb_garbler_le
    (hproj := hproj) (hcorrect := hcorrect) (F := F) (setup := fun _ => pure d)
    (mask := fun d => F.kdfMask H' d) (unmask := fun d => F.kdfMask H' d)
    (samplePads := fun d => F.kdfPadsProb n d) (c := c) (T₁ := T₁) (Sm := Sm) (S₂ := S₂)
    (hn := hn) (x := fun _ => ch.inputs) (D := fun d' => Z.guess n d' ch.state) (L := msgLen n)
    (hmask := fun d r m hm => F.kdfMask_kdfMask H' d r (hm.trans (hH' d r).symm))
    (hT₁ := hT₁) (hSm := hSm) (hS₂ := hS₂)
    (hlen := fun _ r hr t b => length_transferQueries_garbler hlabel ch.inputs r hr t b)
  simp only [ProbComp.eval_pure, PMF.pure_bind, hmask] at h
  exact h

end Cslib.Crypto.Protocols.MPC.Yao
