/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.Mixture
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# Yao's protocol over masked transfers under a sampled first stage: the corrupted evaluator

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045), not that theorem. It specializes the three-level bound of
`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/Mixture.lean` to Yao's protocol `Yao.protocol` with
its batched transfer run by `seqBatchOT` over `maskedOT` over a pad-transfer protocol, for a
corrupted evaluator, when the pad transfer and the masks depend on an index `a` sampled by a first
stage `e`, such as a group description drawn by a setup algorithm. The leading term of the bound
is the `prv.sim` advantage of one adversary, `Yao.evaluatorEnvToPrvSim`, which runs `e` itself, so
every absolute value is outside the expectation over the first stage.

The statement is a concrete bound at a fixed security parameter. The terms of the transfers are
not bounded here, no hardness assumption is applied, and no efficiency of the adversary or of the
environments is claimed.

## Main results

* `Yao.advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_sum`: the advantage
  against the composed protocol for a corrupted evaluator, after the first stage, is at most the
  `prv.sim` advantage of
  `Yao.evaluatorEnvToPrvSim` plus, per transfer, the advantage of one environment against
  `maskedOT` with the ideal pad transfer and against the pad transfer.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Garbling
open _root_.Cslib.Crypto.Protocols.MPC.Composition

variable {Fn Λ : Type} {Gs : Scheme Fn} {δ : Type} {G : δ → Type} {spec₂ : δ → MultiOracleSpec}
  {sc₂ : (a : δ) → Schedule 2 (spec₂ a)} {Coins₂ : δ → Fin 2 → Type}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed security parameter under a sampled first stage, with no
efficiency certificate for any reduction, no hardness assumption applied and the terms of the
transfers left unbounded.

Let `e` sample an index `a`, such as a group description, on which the type `G a` of the pads, the
masks, the distribution of the pads, the protocol `Sub a` for the pad transfer in the world
`W₂ a`, its simulators `S₂ a`, the simulators `Sm a` of `maskedOT`, the inputs `x a` and the
distinguisher `D a` may depend. At every parameter `n ≥ 1`, when `Gs` is correct with a projective
encoding, the advantage between the ideal game of `Yao.protocol Gs n c` over `seqBatchOT` over
`maskedOT` over `Sub a` for the coalition `{1}`, with the simulator composed from
`T₁ {1} = Yao.evaluatorSim Gs Φ S n c`, `seqBatchOTSim`, `Sm a` and `S₂ a`, and its real game, both
after the first stage, is at most the `prv.sim` advantage against the garbling simulator `S n` of
the adversary `Yao.evaluatorEnvToPrvSim` applied to `composeDistinguisher`, which runs `e` itself,
plus, for every transfer `j < c.evaluatorLen`, two advantages of the environment that runs `e` and
then `composeSeqBatchOTRoundEnv` of transfer `j` of the only call, followed by one further stage:

* between the ideal and the real game of `maskedOT` with the ideal pad transfer, against
  `composeDistinguisher`;
* between the ideal game of the pad transfer, with the simulator `S₂ a`, and its real game with
  `Sub a` (`composeRoundEnv` of `maskedOT`).

Every absolute value is outside the expectation over the first stage. Nothing is assumed about
`S`, `e`, the masks, the pad transfer, the simulators or the distinguishers. -/
theorem advantage_bind_composedProtocol_maskedOT_evaluator_le_prvSim_add_sum
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
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    Game.advantage
        ((ProbComp.eval e).bind fun a =>
          (ProbComp.eval (idealJoint (functionality Gs c) {1}
            (composeSim (protocol Gs n c) T₁
              (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
                (seqBatchOTSim c.evaluatorLen (List Bool))
                (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                  (fun _ => S₂ a) J) J)
              {1}) (x a))).bind fun r => ProbComp.eval (D a r))
        ((ProbComp.eval e).bind fun a =>
          (((protocol Gs n c).compose fun _ =>
            (seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
              (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a).realJoint
                (W₂ a) {1} (x a)).bind fun r => ProbComp.eval (D a r)) ≤
      prvSimAdvantage Gs Φ n (S n) (evaluatorEnvToPrvSim c e x fun a =>
          composeDistinguisher (protocol Gs n c)
            (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
              (seqBatchOTSim c.evaluatorLen (List Bool))
              (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                (fun _ => S₂ a) J) J)
            {1} (x a) (D a)) +
        ∑ j ∈ Finset.range c.evaluatorLen,
          (Game.advantage
              ((ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                    (fun _ => S₂ a) J)
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (ProbComp.eval (idealJoint (otFunctionality (List Bool)) c.coalition
                  (Sm a c.coalition) c.query)).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r)))
              ((ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                    (fun _ => S₂ a) J)
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                ((maskedOT (mask a) (unmask a) (samplePads a)).realJoint (otWorld (G a))
                  c.coalition c.query).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r))) +
            Game.advantage
              ((ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                    (fun _ => S₂ a) J)
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun op J q =>
                      ProbComp.eval (idealJoint (otWorld (G a) op) J (S₂ a J) q))))
              ((ProbComp.eval e).bind fun a =>
                (composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (protocol Gs n c) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a)
                    (fun _ => S₂ a) J)
                  {1} (x a) (D a) 0 j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q)))) := by
  have h := advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame
    ((ProbComp.eval e).map Sum.inr) c.evaluatorLen (fun _ => protocol Gs n c) mask unmask
    samplePads W₂ Sub Sm S₂ (fun _ => functionality Gs c) (fun _ => T₁) (fun _ => {1}) x D 1
    (fun _ => le_rfl)
  simp only [PMF.bind_map, Function.comp_def, Sum.elim_inr, Finset.sum_range_one, hT₁] at h
  refine h.trans (add_le_add (le_of_eq ?_) le_rfl)
  exact congrArg₂ Game.advantage
    ((congrArg (PMF.bind _) (funext fun a => (ProbComp.eval_bind ..).symm)).trans
      (bind_idealJoint_evaluatorSim_eq_prvSimExperiment n c Φ S e x _))
    (bind_realJoint_protocol_evaluator_eq_prvSimExperiment hproj hcorrect hn c Φ S e x _)

end Cslib.Crypto.Protocols.MPC.Yao
