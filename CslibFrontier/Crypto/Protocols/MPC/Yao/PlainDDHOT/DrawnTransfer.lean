/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Games
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.Mixture
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainChallenge

/-!
# Yao's protocol in the plain model: one key-derivation and one DDH distinguisher

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] for a corrupted evaluator (#6045, criterion 2), not that theorem. It bounds,
at every security parameter, the advantage of an `Environment` with a corrupted evaluator between
`ProtocolFamily.idealGame`, with the composed simulators, and `ProtocolFamily.realGame` of the
plain-model family `Yao.kdfDDHProbFamily`
(`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/Games.lean`). The group description is drawn
by the setup, the environment chooses the inputs with a program that sees it, and every adversary
of the bound is one explicit program.

A hybrid argument over the transfers that takes one absolute value per transfer bounds this
advantage by a sum with one key-derivation and one DDH distinguisher per transfer `j`, built from
`Yao.kdfDDHTransferEnv … Z j`. A sum of absolute values is not bounded by a multiple of the
advantage of one distinguisher, so `F.SecureKDF` and `F.DDH` do not apply to it when the number of
transfers grows with the security parameter. No such sum is stated for the family.

Here the hybrids over the transfers telescope before any absolute value is taken
(`advantage_bind_compose_seqBatchOT_maskedOT_le_add_mul_roundGame`): the environment program
`Yao.kdfDDHDrawnTransferEnv` draws the transfer `j` below `2 ^ L n` with `L n` fair coins and runs
`Yao.kdfDDHTransferEnv … Z j`, and the bound has one key-derivation distinguisher and one DDH
distinguisher, built from that one program, with the factor `2 ^ L n` for any `L` with
`(c n).evaluatorLen ≤ 2 ^ L n`.

## What is proved

* `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul`: at every parameter `n ≥ 1`
  with `(c n).evaluatorLen ≤ 2 ^ L n`, the advantage of an environment `Z` with a corrupted
  evaluator is at most
  * the `prv.sim` advantage of the adversary `Yao.kdfDDHProbEnvToPrvSim`, which draws `d` with the
    setup program, runs the choosing stage of `Z` and then `composeDistinguisher`, plus
  * `2 ^ L n` times the sum of
    * the advantage between `F.kdfIdealGame` and `F.kdfRealGame` (the games of `F.SecureKDF`) of
      the distinguisher `F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)`,
    * the advantage between `F.ddhRealGame` and `F.ddhRandomGame` (the games of `F.DDH`) of the
      distinguisher `F.roundEnvToDDHDistinguisher (F.padTransferEnv H F.kdfPadsProb S₂ E)`, and
    * `18 / 2 ^ n`,

    where `E = Yao.kdfDDHDrawnTransferEnv F H c Sm S₂ Z L` does not depend on a transfer: it draws
    a transfer `j`, runs the choosing stage of `Z`, garbles, runs the transfers before `j` with
    the real protocol and stops at transfer `j`.

  The setup law of the key-derivation and DDH games is the distribution of the setup program. The
  absolute value of each of the three advantages is outside the expectation over the setup, the
  drawn transfer, the choice of the environment, the garbler's coins and the earlier transfers.
  The label length is the property `Gs.HasTokenLength` of the garbling scheme.

## What is not proved

* **The factor is `2 ^ L n`, not the number of transfers.** A program of fair coins draws an
  exactly uniform index only below a power of two; a transfer drawn at or past
  `(c n).evaluatorLen` challenges nothing and contributes nothing, so the count is exact and
  there is no rounding term. With `L n = Nat.clog 2 (c n).evaluatorLen` the factor is less than
  `2 * (c n).evaluatorLen` when there is a transfer, and `1` when there is none.
* **No efficiency certificate and no asymptotic statement.** None of the three adversaries is
  shown to be uniform strict PPT, no hardness assumption (`F.DDH`, `F.SecureKDF`, `prv.sim`
  security of `Gs`) is applied, the composed simulators are not shown to be PPT, and
  `ProtocolFamily.SemiHonestSecure` is not proved for the family (#6045). Nothing here bounds
  `(c n).evaluatorLen` or `2 ^ L n` by a polynomial.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; they were not re-verified against the source.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHDrawnTransferEnv`: the environment program of a transfer
  drawn with fair coins.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul`

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Garbling
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

variable {Fn Λ : Type} {Gs : Scheme Fn} {δ : Type} {G : δ → Type} {spec₂ : δ → MultiOracleSpec}
  {sc₂ : (a : δ) → Schedule 2 (spec₂ a)} {Coins₂ : δ → Fin 2 → Type}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed security parameter under a sampled first stage, with no
efficiency certificate for any reduction, no hardness assumption applied and the terms of the
transfers left unbounded.

Let `e` sample an index `a`, such as a group description, on which the type `G a` of the pads, the
masks, the distribution of the pads, the protocol `Sub a` for the pad transfer in the world
`W₂ a`, its simulators `S₂ a`, the simulators `Sm a` of `maskedOT`, the inputs `x a` and the
distinguisher `D a` may depend. At every parameter `n ≥ 1` and for `c.evaluatorLen ≤ 2 ^ L`, when
`Gs` is correct with a projective encoding, the advantage between the ideal game of
`Yao.protocol Gs n c` over `seqBatchOT` over `maskedOT` over `Sub a` for the coalition `{1}`, with
the simulator composed from `T₁ {1} = Yao.evaluatorSim Gs Φ S n c`, `seqBatchOTSim`, `Sm a` and
`S₂ a`, and its real game, both after the first stage, is at most the `prv.sim` advantage against
the garbling simulator `S n` of the adversary `Yao.evaluatorEnvToPrvSim` applied to
`composeDistinguisher`, which runs `e` itself, plus `2 ^ L` times the sum of two advantages of the
one environment that draws a transfer `j` below `2 ^ L` with `L` fair coins
(`ProbComp.sampleBinaryNat`), runs `e` and then `composeSeqBatchOTRoundEnv` of transfer `j` of the
only call, followed by one further stage:

* between the ideal and the real game of `maskedOT` with the ideal pad transfer, against
  `composeDistinguisher`;
* between the ideal game of the pad transfer, with the simulator `S₂ a`, and its real game with
  `Sub a` (`composeRoundEnv` of `maskedOT`).

Every absolute value is outside the expectation over the drawn transfer and the first stage: the
signed differences of the hybrids over the transfers telescope before it is taken
(`advantage_bind_compose_seqBatchOT_maskedOT_le_add_mul_roundGame`). Nothing is assumed about `S`,
`e`, the masks, the pad transfer, the simulators or the distinguishers. -/
private theorem advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_mul
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params Gs) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (e : ProbComp δ)
    (mask unmask : (a : δ) → G a → List Bool → List Bool)
    (samplePads : (a : δ) → ProbComp (G a × G a))
    (W₂ : (a : δ) → MultiOracleWorld (spec₂ a))
    (Sub : (a : δ) → Protocol 2 (spec₂ a) (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)))
    (Sm : (a : δ) → (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (G a) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (G a)) (OTOut (List Bool)) J)
    (S₂ : (a : δ) → (J : Finset (Fin 2)) →
      CoalitionSimulator (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)) J)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {1} = evaluatorSim Gs Φ S n c)
    (x : (a : δ) → (i : Fin 2) → Input c i)
    (D : (a : δ) → ((i : ({1} : Finset (Fin 2))) → PartyView (Input c)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => Coins₂ a) (MaskedOTCoins (G a))
              (maskedOTSchedule (G a) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule c.evaluatorLen (List Bool))) Coins (schedule c))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => sc₂ a) (maskedOTSchedule (G a) (List Bool)))
            (seqBatchOTSchedule c.evaluatorLen (List Bool))) (schedule c)) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) (L : ℕ)
    (hL : c.evaluatorLen ≤ 2 ^ L) :
    Game.advantage
        ((ProbComp.eval e).bind fun a =>
          (ProbComp.eval (idealJoint (functionality Gs c) {1}
            (composeSim (protocol Gs n c) (T₁ {1})
              (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
                (seqBatchOTSim c.evaluatorLen (List Bool) J)
                (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                  (fun _ => S₂ a)))) (x a))).bind fun r => ProbComp.eval (D a r))
        ((ProbComp.eval e).bind fun a =>
          (((protocol Gs n c).compose fun _ =>
            (seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
              (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a).realJoint
                (W₂ a) {1} (x a)).bind fun r => ProbComp.eval (D a r)) ≤
      prvSimAdvantage Gs Φ n (S n) (evaluatorEnvToPrvSim c e x fun a =>
          composeDistinguisher (protocol Gs n c)
            (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
              (seqBatchOTSim c.evaluatorLen (List Bool) J)
              (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                (fun _ => S₂ a)))
            {1} (x a) (D a)) +
        2 ^ L *
          (Game.advantage
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                (ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (ProbComp.eval (idealJoint (otFunctionality (List Bool)) c.coalition
                  (Sm a c.coalition) c.query)).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r)))
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                (ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                ((maskedOT (mask a) (unmask a) (samplePads a)).realJoint (otWorld (G a))
                  c.coalition c.query).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r))) +
            Game.advantage
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                (ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun op J q =>
                      ProbComp.eval (idealJoint (otWorld (G a) op) J (S₂ a J) q))))
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                (ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q)))) := by
  have h := advantage_bind_compose_seqBatchOT_maskedOT_le_add_mul_roundGame
    ((ProbComp.eval e).map Sum.inr) c.evaluatorLen (fun _ => protocol Gs n c) mask unmask
    samplePads W₂ Sub Sm S₂ (fun _ => functionality Gs c) (fun _ => T₁) (fun _ => {1}) x D 1
    (fun _ => le_rfl) L hL
  simp only [PMF.bind_map, Function.comp_def, Sum.elim_inr, Finset.sum_range_one, hT₁] at h
  rw [hT₁]
  exact h.trans (add_le_add (le_of_eq (congrArg₂ Game.advantage
    ((congrArg (PMF.bind _) (funext fun a => (ProbComp.eval_bind ..).symm)).trans
      (bind_idealJoint_evaluatorSim_eq_prvSimExperiment n c Φ S e x _))
    (bind_realJoint_protocol_evaluator_eq_prvSimExperiment hproj hcorrect hn c Φ S e x _))) le_rfl)

/-- **The environment program of a transfer drawn with fair coins**, for `Yao.kdfDDHProbFamily`
with a corrupted evaluator: at the parameter `n` it draws a transfer `j` below `2 ^ L n` with
`L n` fair coins (`ProbComp.sampleBinaryNat`) and runs `Yao.kdfDDHTransferEnv … Z j`. A transfer
`j ≥ (c n).evaluatorLen` challenges nothing: the program then runs the whole protocol and decides.
No efficiency is claimed for it. -/
@[expose] noncomputable def kdfDDHDrawnTransferEnv (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {1}) (L : ℕ → ℕ) (n : ℕ) (d : F.Desc) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))) := do
  let j ← ProbComp.sampleBinaryNat (L n)
  kdfDDHTransferEnv F H c Sm S₂ Z j n d

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a bound on advantages at each parameter with one key-derivation and one DDH
distinguisher, with no efficiency certificate for any of the three adversaries and no hardness
assumption applied.

Let the group description `d` be drawn by the setup program `setup n`, let `Z` be an environment
against the plain-model family `Yao.kdfDDHProbFamily Gs F H c` with a corrupted evaluator, and let
`L n` fair coins index the transfers: `(c n).evaluatorLen ≤ 2 ^ L n`. At every parameter `n ≥ 1`,
when the garbling scheme `Gs` is correct with a projective encoding and tokens of length
`msgLen n` (`Gs.HasTokenLength`), every derived key `H (d, F.encode d r)` has length `msgLen n`,
and the simulators at the coalition `{1}` are `Yao.evaluatorSim Gs Φ S n (c n)` for Yao's protocol,
`maskedOTReceiverSim` with the fair-coin pads and a uniform `msgLen n`-bit word for the masked
transfer and `F.ddhOTReceiverSimProb n d` for the DDH transfer, the advantage of `Z` between
`ProtocolFamily.idealGame` with the composed simulator family `Yao.kdfDDHProbSim` and
`ProtocolFamily.realGame` is at most

* the `prv.sim` advantage against `S n` of the one adversary `Yao.kdfDDHProbEnvToPrvSim`, which
  runs the setup program, the choosing stage of `Z` and `composeDistinguisher`, plus
* `2 ^ L n` times the sum of the advantage between `F.kdfIdealGame` and `F.kdfRealGame` of the one
  distinguisher built from `Yao.kdfDDHDrawnTransferEnv … Z L` by `F.padHidingEnv` and
  `F.roundEnvToKDFDistinguisher`, the advantage between `F.ddhRealGame` and `F.ddhRandomGame` of
  the one distinguisher built from it by `F.padTransferEnv` and `F.roundEnvToDDHDistinguisher`, and
  `18 / 2 ^ n`: `4 / 2 ^ n` for the fair-coin exponents of the pads and `14 / 2 ^ n` for those of
  the DDH transfer.

Neither distinguisher depends on a transfer: the program `Yao.kdfDDHDrawnTransferEnv` draws the
transfer itself, and the signed differences of the hybrids over the transfers telescope before the
absolute value is taken. The factor is `2 ^ L n`, not `(c n).evaluatorLen`, because fair coins draw
an exactly uniform index only below a power of two; there is no rounding term, and for
`L n = Nat.clog 2 (c n).evaluatorLen` the factor is below `2 * (c n).evaluatorLen` when there is a
transfer. The setup law of the key-derivation and DDH games is the distribution of the setup
program. Each of the three advantages is the absolute difference of two acceptance probabilities
of one adversary, outside the expectation over the setup, the drawn transfer, the choice of the
environment, the garbler's coins and the earlier transfers. -/
theorem advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul
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
    (Z : Environment (kdfDDHProbFamily Gs F H c) {1}) (L : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n)
    (hT₁ : T₁ n {1} = evaluatorSim Gs Φ S n (c n))
    (hSm : ∀ d, Sm n d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPadsProb n d)
      (Cslib.BitString.sampleList (msgLen n)))
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hlabel : Gs.HasTokenLength n (c n).fn (msgLen n))
    (hL : (c n).evaluatorLen ≤ 2 ^ L n) :
    Game.advantage
        ((kdfDDHProbFamily Gs F H c).idealGame (fun n => ProbComp.eval (setup n)) {1}
          (kdfDDHProbSim F H c T₁ Sm S₂ {1}) Z n)
        ((kdfDDHProbFamily Gs F H c).realGame (fun n => ProbComp.eval (setup n)) {1} Z n) ≤
      prvSimAdvantage Gs Φ n (S n) (kdfDDHProbEnvToPrvSim F setup H c Sm S₂ Z n) +
        2 ^ L n *
          (Game.advantage
              (F.kdfIdealGame (fun n => ProbComp.eval (setup n)) msgLen
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H F.kdfPadsProb S₂ (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L))) n)
              (F.kdfRealGame (fun n => ProbComp.eval (setup n)) H
                (F.roundEnvToKDFDistinguisher H
                  (F.padHidingEnv H F.kdfPadsProb S₂ (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L))) n) +
            (Game.advantage
                (F.ddhRealGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H F.kdfPadsProb S₂
                      (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L))) n)
                (F.ddhRandomGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv H F.kdfPadsProb S₂
                      (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L))) n) +
              18 / 2 ^ n)) := by
  have h := advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_mul hproj hcorrect hn
    (c n) Φ S
    (do
      let d ← setup n
      let ch ← Z.choose n d
      return (⟨d, ch⟩ : Σ d : F.Desc, InputChoice (kdfDDHProbFamily Gs F H c) n d))
    (fun a => F.kdfMask H a.1) (fun a => F.kdfMask H a.1) (fun a => F.kdfPadsProb n a.1)
    (fun _ => noOracleWorld) (fun a => F.ddhOTProbProtocol n a.1) (fun a => Sm n a.1)
    (fun a => S₂ n a.1) (T₁ n) hT₁ (fun a => a.2.inputs) (fun a => Z.guess n a.1 a.2.state)
    (L n) hL
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind] at h
  refine h.trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))
  have hE : ∀ d c',
      Sum.inr c' ∈ (ProbComp.eval (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L n d)).support →
        c'.coalition = ({1} : Finset (Fin 2)) ∧
          (otOutputs (M := List Bool) c'.query 1 : List Bool).length = msgLen n := by
    intro d c' hc'
    simp only [kdfDDHDrawnTransferEnv, kdfDDHTransferEnv, ProbComp.eval_bind,
      PMF.mem_support_bind_iff, eval_composeSeqBatchOTRoundEnvProg] at hc'
    obtain ⟨_, -, ch, -, hc'⟩ := hc'
    exact coalition_length_of_mem_support_composeSeqBatchOTRoundEnv _ _ _ _ _ _ _ _ _ _ _ (msgLen n)
      (fun r hr => forallChallenge_protocol_evaluator n (c n) (msgLen n) ch.inputs r
        (length_transferQueries_garbler hlabel ch.inputs r hr)) hc'
  have hA := F.advantage_bind_padHiding_le_kdf (fun n => ProbComp.eval (setup n)) H msgLen n
    (Sm n) hSm S₂ hH (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L) hE
  have hB := F.advantage_bind_padTransfer_le_ddh (fun n => ProbComp.eval (setup n)) H
    F.kdfPadsProb n S₂ hS₂ (kdfDDHDrawnTransferEnv F H c Sm S₂ Z L) fun d c' hc' => (hE d c' hc').1
  simp only [kdfDDHDrawnTransferEnv, kdfDDHTransferEnv, ProbComp.eval_bind, PMF.bind_bind,
    eval_composeSeqBatchOTRoundEnvProg] at hA hB
  rw [PMF.bind_comm (ProbComp.eval (setup n)), PMF.bind_comm (ProbComp.eval (setup n))] at hA hB
  have h18 : (18 : ℝ≥0) / 2 ^ n = 4 / 2 ^ n + 14 / 2 ^ n := by
    rw [← add_div]
    norm_num
  refine (add_le_add hA hB).trans_eq ?_
  rw [h18]
  ring

end Cslib.Crypto.Protocols.MPC.Yao
