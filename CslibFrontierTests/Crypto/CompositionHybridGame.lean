/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.BatchOT.Sequential
import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridIndex
import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# Tests for the round hybrids of a composed protocol as games of one environment

A client of `CslibFrontier.Crypto.Protocols.MPC.Composition.HybridGame` under module encapsulation.

* `Schedule.oracleRounds` counts oracle rounds only: a schedule with one oracle round between two
  message rounds has one, and `k` sequential transfers have `k`. Counting the message rounds, or
  an off-by-one in the number of hops, fails these checks.
* On every challenge, the advantage between the round game on the ideal and on the real joint
  distributions of the subprotocols is `semiHonestAdvantage` of the guessing stage against the
  challenged subprotocol on the challenged query tuple. So the two round games are the ideal and
  the real semi-honest game of that subprotocol; a round game that ignored the guessing stage or
  the query tuple would fail the check. An environment that has decided its bit returns it.
* The boundary with no oracle round: against the empty batch the environment of hop `0` challenges
  nothing, and its game on any kernel is the real game.
* `semiHonestAdvantage_seqBatchOT_compose_le_sum_roundGame` is applied to the batched transfer
  over the fair-coin DDH transfer `ddhOTProbProtocol` at a fixed group description.
* `advantage_bind_compose_le_add_sum_roundGame` is applied to the same protocol with the group
  description drawn from a setup law, on which the types of the protocol depend. The outer term
  vanishes because the batch is perfectly private with the ideal single transfer, and every
  summand is the advantage of one environment that draws the description and runs the earlier
  transfers.
* `advantage_bind_compose_le_add_mul_roundGame` is applied in the same setting: one environment
  that draws the transfer with fair coins, and the factor `2 ^ L` for `k ≤ 2 ^ L`.
* `semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame` is applied to Yao's protocol
  `Yao.composedProtocol` with its batched transfer run by `seqBatchOT` over any single transfer of
  words: the advantage against the hybrid protocol `Yao.protocol` plus one environment per
  transfer.
* `semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame` is applied to Yao's
  protocol over `seqBatchOT` over `maskedOT` with the key-derivation mask `F.kdfMask` and the pads
  `F.kdfPads`, over the fair-coin DDH transfer `ddhOTProbProtocol`, in the plain model: the
  composed protocol and its composed simulator are an instance of the theorem.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.CompositionHybridGame

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Composition
open Cslib.Probability

/-- Message rounds are not counted: one oracle round between two message rounds. -/
example : Schedule.oracleRounds (m := 2) (spec := otSpec Bool)
    [.message 0 1 Bool, .oracle () (Function.Embedding.refl (Fin 2)), .message 1 0 ℕ] = 1 := rfl

/-- The empty batch has no oracle round. -/
example (M : Type) : (seqBatchOTSchedule 0 M).oracleRounds = 0 := rfl

/-- Three transfers have three oracle rounds. -/
example (M : Type) : (seqBatchOTSchedule 3 M).oracleRounds = 3 := rfl

/-- **The round games of a challenge are the semi-honest games of the subprotocol.** For every
challenge `c`, the advantage between the round game on the ideal joint distributions and on the
real joint distributions is the semi-honest advantage of the guessing stage `c.guess` against
`Sub c.op`, for the corrupted slots `c.coalition`, on the query tuple `c.query`. -/
example {spec₁ spec₂ : MultiOracleSpec}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (c : RoundChallenge sc₂ Coins₂) :
    Game.advantage
        (roundGame (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) (.inr c))
        (roundGame (fun op J q => (Sub op).realJoint W₂ J q) (.inr c)) =
      semiHonestAdvantage (Sub c.op) W₂ (W₁ c.op) c.coalition (S₂ c.op c.coalition) c.query
        c.guess := by
  simp only [roundGame, Sum.elim_inr, semiHonestAdvantage, ProbComp.eval_bind]

/-- An environment that has decided its bit returns it, on every kernel. -/
example {spec₁ spec₂ : MultiOracleSpec}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s))) (b : Bool) :
    roundGame κ (.inl b) = PMF.pure b := rfl

/-- **No oracle round.** Against the empty batch over any single transfer, the environment of hop
`0` challenges no round: its game on any kernel is the real game of the composed protocol. -/
example (M : Type) {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec 0 M).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec 0 M).Query ())
        (Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit) (seqBatchOTSchedule 0 M))
        (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule 0 M)) i) ×
      ((i : Fin 2) → (batchOTSpec 0 M).Answer () i) → ProbComp Bool)
    (κ : (op : (otSpec M).Op) → (J : Finset (Fin ((otSpec M).arity op))) →
      ((s : Fin ((otSpec M).arity op)) → (otSpec M).Query op s) →
      PMF (((s : J) → PartyView ((otSpec M).Query op) Coins₂ sc₂ s) ×
        ((s : Fin ((otSpec M).arity op)) → (otSpec M).Answer op s))) :
    (composeRoundEnv (seqBatchOT 0 M) (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I x D 0).bind
        (roundGame κ) =
      (((seqBatchOT 0 M).compose fun _ => Sub).realJoint W₂ I x).bind fun r =>
        ProbComp.eval (D r) :=
  composeRoundEnv_bind_roundGame_of_oracleRounds_le (seqBatchOT 0 M) (otWorld M) W₂ (fun _ => Sub)
    (fun _ => S₂) I x D κ le_rfl

/-- **The batched transfer over the fair-coin DDH transfer, one environment per transfer.** At a
fixed security parameter `n` and group description `d`, the advantage against `k` sequential
transfers over `ddhOTProbProtocol` is at most the sum over the transfers of the advantage of one
environment between the ideal and the real game of that transfer, for any simulators of the DDH
transfer. -/
example (F : PrimeOrderGroupFamily) (k n : ℕ) (d : F.Desc)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec k (F.Carrier d)).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k (F.Carrier d)).Query ())
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (fun _ => Unit) (seqBatchOTSchedule k (F.Carrier d)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (seqBatchOTSchedule k (F.Carrier d))) i) ×
      ((i : Fin 2) → (batchOTSpec k (F.Carrier d)).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage ((seqBatchOT k (F.Carrier d)).compose fun _ => F.ddhOTProbProtocol n d)
        noOracleWorld (batchOTFunctionality k (F.Carrier d)) I
        (composeSim (seqBatchOT k (F.Carrier d)) (seqBatchOTSim k (F.Carrier d) I) (fun _ => S₂))
        x D ≤
      ∑ j ∈ Finset.range k,
        Game.advantage
          ((composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
            (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂) I x D j).bind
              (roundGame fun op J q =>
                ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ J) q)))
          ((composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
            (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂) I x D j).bind
              (roundGame fun _ J q => (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)) :=
  semiHonestAdvantage_seqBatchOT_compose_le_sum_roundGame k (F.Carrier d) noOracleWorld
    (F.ddhOTProbProtocol n d) S₂ I x D

/-- **The batched transfer over the fair-coin DDH transfer with a sampled group description.** The
group description `d` is drawn from the setup law `setup n`, and the protocol, the simulators, the
inputs and the distinguisher depend on `d`. The advantage between the ideal game, with the composed
simulator, and the real game of `k` sequential transfers over `ddhOTProbProtocol` is at most the
sum over the transfers of the advantage of one environment, which draws `d` and runs the earlier
transfers itself, between the ideal and the real game of the challenged transfer. The outer term of
`advantage_bind_compose_le_add_sum_roundGame` vanishes: with the ideal single transfer the batch is
perfectly private. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (k n : ℕ)
    (S₂ : (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2))
    (x : (d : F.Desc) → (i : Fin 2) → (batchOTSpec k (F.Carrier d)).Query () i)
    (D : (d : F.Desc) → ((i : I) → PartyView ((batchOTSpec k (F.Carrier d)).Query ())
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (fun _ => Unit) (seqBatchOTSchedule k (F.Carrier d)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (seqBatchOTSchedule k (F.Carrier d))) i) ×
      ((i : Fin 2) → (batchOTSpec k (F.Carrier d)).Answer () i) → ProbComp Bool) :
    Game.advantage
        ((setup n).bind fun d => ProbComp.eval
          (idealJoint (batchOTFunctionality k (F.Carrier d)) I
            (composeSim (seqBatchOT k (F.Carrier d)) (seqBatchOTSim k (F.Carrier d) I)
              (fun _ => S₂ d)) (x d) >>= D d))
        ((setup n).bind fun d =>
          (((seqBatchOT k (F.Carrier d)).compose fun _ => F.ddhOTProbProtocol n d).realJoint
            noOracleWorld I (x d)).bind fun r => ProbComp.eval (D d r)) ≤
      ∑ j ∈ Finset.range k,
        Game.advantage
          ((setup n).bind fun d =>
            (composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
              (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂ d) I (x d) (D d) j).bind
                (roundGame fun op J q =>
                  ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ d J) q)))
          ((setup n).bind fun d =>
            (composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
              (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂ d) I (x d) (D d) j).bind
                (roundGame fun _ J q =>
                  (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)) := by
  have h := advantage_bind_compose_le_add_sum_roundGame ((setup n).map Sum.inr)
    (fun d => seqBatchOT k (F.Carrier d)) (fun d => otWorld (F.Carrier d))
    (fun _ => noOracleWorld) (fun d => batchOTFunctionality k (F.Carrier d))
    (fun d => seqBatchOTSim k (F.Carrier d)) (fun d _ => F.ddhOTProbProtocol n d)
    (fun d _ => S₂ d) (fun _ => I) x D k
    fun d => (oracleRounds_seqBatchOTSchedule k (F.Carrier d)).le
  have h₀ (d : F.Desc) := perfectSemiHonestPrivate_seqBatchOT k (F.Carrier d) I (x d)
  simpa only [PMF.bind_map, Function.comp_def, Sum.elim_inr, ← ProbComp.eval_bind, h₀,
    Game.advantage_self, zero_add] using h

/-- **The batched transfer under a sampled group description, with one environment that draws the
transfer.** In the setting of the previous example and for `k ≤ 2 ^ L`
(`advantage_bind_compose_le_add_mul_roundGame`), the advantage is at most `2 ^ L` times the
advantage of the one environment that draws the transfer `j` below `2 ^ L` with `L` fair coins,
draws `d` and runs the earlier transfers, between the ideal and the real game of the challenged
transfer: one absolute value instead of one per transfer. The hypothesis holds for `k = 0` with
any `L`, in particular with no coin. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (k n : ℕ) (L : ℕ)
    (hL : k ≤ 2 ^ L)
    (S₂ : (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2))
    (x : (d : F.Desc) → (i : Fin 2) → (batchOTSpec k (F.Carrier d)).Query () i)
    (D : (d : F.Desc) → ((i : I) → PartyView ((batchOTSpec k (F.Carrier d)).Query ())
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (fun _ => Unit) (seqBatchOTSchedule k (F.Carrier d)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (seqBatchOTSchedule k (F.Carrier d))) i) ×
      ((i : Fin 2) → (batchOTSpec k (F.Carrier d)).Answer () i) → ProbComp Bool) :
    Game.advantage
        ((setup n).bind fun d => ProbComp.eval
          (idealJoint (batchOTFunctionality k (F.Carrier d)) I
            (composeSim (seqBatchOT k (F.Carrier d)) (seqBatchOTSim k (F.Carrier d) I)
              (fun _ => S₂ d)) (x d) >>= D d))
        ((setup n).bind fun d =>
          (((seqBatchOT k (F.Carrier d)).compose fun _ => F.ddhOTProbProtocol n d).realJoint
            noOracleWorld I (x d)).bind fun r => ProbComp.eval (D d r)) ≤
      2 ^ L *
        Game.advantage
          ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j => (setup n).bind fun d =>
            (composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
              (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂ d) I (x d) (D d) j).bind
                (roundGame fun op J q =>
                  ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ d J) q)))
          ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j => (setup n).bind fun d =>
            (composeRoundEnv (seqBatchOT k (F.Carrier d)) (otWorld (F.Carrier d)) noOracleWorld
              (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂ d) I (x d) (D d) j).bind
                (roundGame fun _ J q =>
                  (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)) := by
  have h := advantage_bind_compose_le_add_mul_roundGame ((setup n).map Sum.inr)
    (fun d => seqBatchOT k (F.Carrier d)) (fun d => otWorld (F.Carrier d))
    (fun _ => noOracleWorld) (fun d => batchOTFunctionality k (F.Carrier d))
    (fun d => seqBatchOTSim k (F.Carrier d)) (fun d _ => F.ddhOTProbProtocol n d)
    (fun d _ => S₂ d) (fun _ => I) x D k L
    (fun d => (oracleRounds_seqBatchOTSchedule k (F.Carrier d)).le) hL
  have h₀ (d : F.Desc) := perfectSemiHonestPrivate_seqBatchOT k (F.Carrier d) I (x d)
  simpa only [PMF.bind_map, Function.comp_def, Sum.elim_inr, ← ProbComp.eval_bind, h₀,
    Game.advantage_self, zero_add] using h

/-- **Yao's protocol over sequential single transfers, one environment per transfer.** For every
garbling scheme and every protocol `Sub` for a single transfer of words, the advantage against
`Yao.composedProtocol` with the batch run by `seqBatchOT` over `Sub` is at most the advantage of
`composeDistinguisher` against the hybrid protocol `Yao.protocol` with the ideal batched transfer,
plus the sum over the transfers of the advantage of one environment, which garbles and runs the
earlier transfers itself, between the ideal and the real game of the challenged transfer. -/
example {Fn : Type} (G : Garbling.Scheme Fn) (n : ℕ) (c : Yao.Params G)
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (W₂ : MultiOracleWorld spec₂)
    (Sub : Protocol 2 spec₂ sc₂ (OTIn (List Bool)) Coins₂ (OTOut (List Bool)))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ (OTIn (List Bool)) Coins₂ (OTOut (List Bool)) J)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Yao.Input c i)
    (D : ((i : I) → PartyView (Yao.Input c)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule c.evaluatorLen (List Bool))) Yao.Coins (Yao.schedule c))
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂)
            (seqBatchOTSchedule c.evaluatorLen (List Bool))) (Yao.schedule c)) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage
        (Yao.composedProtocol G n c
          ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ => Sub))
        W₂ (Yao.functionality G c) I
        (composeSim (Yao.protocol G n c) (S₁ I)
          (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
            (seqBatchOTSim c.evaluatorLen (List Bool) J) (fun _ => S₂))) x D ≤
      semiHonestAdvantage (Yao.protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
          (Yao.functionality G c) I (S₁ I) x
          (composeDistinguisher (Yao.protocol G n c)
            (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
              (seqBatchOTSim c.evaluatorLen (List Bool) J) (fun _ => S₂)) I x D) +
        ∑ i ∈ Finset.range (Yao.schedule c).oracleRounds,
          ∑ j ∈ Finset.range c.evaluatorLen,
            Game.advantage
              ((composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (Yao.protocol G n c) W₂ Sub
                S₂ I x D i j).bind (roundGame fun op J q =>
                  ProbComp.eval (idealJoint (otWorld (List Bool) op) J (S₂ J) q)))
              ((composeSeqBatchOTRoundEnv c.evaluatorLen (List Bool) (Yao.protocol G n c) W₂ Sub
                S₂ I x D i j).bind (roundGame fun _ J q => Sub.realJoint W₂ J q)) :=
  semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame c.evaluatorLen (List Bool)
    (Yao.protocol G n c) W₂ Sub S₂ (Yao.functionality G c) S₁ I x D

/-- **Yao's protocol over sequential masked transfers over the fair-coin DDH transfer.** At a fixed
security parameter `n` and group description `d`, Yao's protocol with its batch run by `seqBatchOT`
over `maskedOT` with the mask `F.kdfMask H d` and the pads `F.kdfPads d`, and the pad transfer run
by `F.ddhOTProbProtocol n d`, is a plain-model protocol to which
`semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame` applies, for any
simulators: the right-hand side is the advantage against the hybrid protocol `Yao.protocol` plus,
for every transfer, the two advantages of one environment that the theorem states. -/
example {Fn : Type} (Gs : Garbling.Scheme Fn) (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (n : ℕ) (d : F.Desc) (c : Yao.Params Gs)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (Sm : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Yao.Input c i) (D : _) :=
  (semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame c.evaluatorLen
    (Yao.protocol Gs n c) (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d) noOracleWorld
    (F.ddhOTProbProtocol n d) Sm S₂ (Yao.functionality Gs c) S₁ I x D :
    semiHonestAdvantage
        (Yao.composedProtocol Gs n c
          ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
            (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).compose fun _ =>
              F.ddhOTProbProtocol n d))
        noOracleWorld (Yao.functionality Gs c) I
        (composeSim (Yao.protocol Gs n c) (S₁ I)
          (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
            (seqBatchOTSim c.evaluatorLen (List Bool) J)
            (fun _ J => composeSim (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)) (Sm J)
              (fun _ => S₂)))) x D ≤ _)

/-- Yao's protocol calls the batched transfer once. -/
example {Fn : Type} (G : Garbling.Scheme Fn) (c : Yao.Params G) :
    (Yao.schedule c).oracleRounds = 1 := rfl

end CslibFrontierTests.Crypto.CompositionHybridGame
