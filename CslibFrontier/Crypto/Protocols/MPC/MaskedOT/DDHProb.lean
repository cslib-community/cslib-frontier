/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDH

/-!
# The masked transfer over the fair-coin DDH transfer of a group family, per distinguisher

`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/DDH.lean` bounds one distinguisher of a corrupted
receiver of `maskedOT` over the fixed-group DDH transfer `ddhOTProtocol`, whose coins are exact
uniform exponents. This module gives the same bound over the bit-string protocol
`ddhOTProbProtocol` of a `PrimeOrderGroupFamily` `F`, at a fixed security parameter `n` and group
description `d`: the parties' coins are the raw fair-coin bit strings of `sampleExpBits n d`, the
simulator of the pad transfer is `ddhOTReceiverSimProb n d`, and the DDH reduction draws fair coins
only.

This is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem; it is original bookkeeping and no
cited statement is claimed.

## What is proved

All statements are concrete, at a fixed security parameter `n`. The first two are per instance:
a fixed group description `d`, a fixed input pair and one distinguisher `D`. The third is over a
setup law for `d` and an environment that is sampled after `d`.

* For a corrupted receiver of `ddhOTProbProtocol n d` with the simulator `ddhOTReceiverSimProb n d`,
  the advantage of `D` is at most the fixed-group DDH advantage of the explicit fair-coin
  distinguisher `ddhOTProbReduction n d x D` plus `14 / 2 ^ n`
  (`semiHonestAdvantage_ddhOTProb_receiver_le`). This is the form at a fixed input and
  distinguisher of `advantage_ddhOTProbReceiverGame_le`, whose reduction
  `ddhOTReceiverToDDHDistinguisher Z` runs `ddhOTProbReduction` on the inputs that `Z` chooses.
* For a corrupted receiver of `maskedOT` over `ddhOTProbProtocol n d`, the advantage of `D` is at
  most the advantage of `composeDistinguisher` against `maskedOT` with the ideal pad transfer, plus
  the expectation over the sender's pads of the fixed-group DDH advantage of the explicit
  distinguisher `maskedOTToDDHProbDistinguisher`, plus `14 / 2 ^ n`
  (`semiHonestAdvantage_maskedOT_ddhOTProb_receiver_le`).
* For an environment `E` that is sampled after the setup and either decides a bit or stops at a
  challenged transfer with the receiver corrupted, the advantage between the ideal and the real
  round game, taken over the setup law and the environment with the absolute value outside both
  expectations, is at most the DDH advantage of the one distinguisher
  `roundEnvToDDHDistinguisher E` plus `14 / 2 ^ n` (`advantage_bind_roundGame_ddhOTProb_le`).

## What is not proved

* No asymptotic statement (`ProtocolFamily.SemiHonestSecure`) and no efficiency certificate for
  `maskedOTToDDHProbDistinguisher`, `roundEnvToDDHDistinguisher` or `composeDistinguisher`. In the
  masked-transfer bound the DDH term is an expectation over the sender's pads of advantages of
  distinguishers that depend on the pads, which an asymptotic reduction has to sample itself or fix
  as advice.
* Nothing about the first term of the masked-transfer bound beyond
  `semiHonestAdvantage_maskedOT_receiver_eq`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTProbReduction`: the fair-coin DDH reduction of a
  corrupted receiver of `ddhOTProbProtocol` at a fixed input and distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.maskedOTToDDHProbDistinguisher`: the reduction from a
  distinguisher of a corrupted receiver of the masked transfer over `ddhOTProbProtocol` to a DDH
  distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.roundEnvToDDHDistinguisher`: the DDH distinguisher that
  samples an environment of a challenged transfer and runs `ddhOTProbReduction` on its challenge.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.semiHonestAdvantage_ddhOTProb_receiver_le`: the bound for a
  corrupted receiver of `ddhOTProbProtocol`.
* `Cslib.Crypto.PrimeOrderGroupFamily.semiHonestAdvantage_maskedOT_ddhOTProb_receiver_le`: the
  bound for a corrupted receiver of the masked transfer over `ddhOTProbProtocol`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_roundGame_ddhOTProb_le`: the bound for a
  sampled environment of a challenged transfer, under the setup law, with the absolute value
  outside the expectation.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Protocols.MPC
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily) {M : Type}

/-! ### A corrupted receiver of the fair-coin DDH transfer -/

/-- **The fair-coin DDH reduction of a corrupted receiver of `ddhOTProbProtocol n d`**, on the
inputs `x` with the distinguisher `D`: given a DDH triple `(u, v, w)`, draw the receiver's raw coin
bit string `bBits` and two chosen-branch bit strings `rBits`, `sBits` with `sampleExpBits n d`, and
run `ddhOTReductionWithCoinsOf`, which records `bBits` unreduced in the receiver's view and embeds
the triple into the unchosen branch. `ddhOTReceiverToDDHDistinguisher Z` runs it on the inputs and
with the guessing stage of the environment `Z`. -/
@[expose] noncomputable def ddhOTProbReduction (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool)
    (u v w : F.Carrier d) : ProbComp Bool := do
  let bBits ← F.sampleExpBits n d
  let rBits ← F.sampleExpBits n d
  let sBits ← F.sampleExpBits n d
  ddhOTReductionWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
    (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D bBits
    (BitString.binaryValue rBits : ZMod (F.order d))
    (BitString.binaryValue sBits : ZMod (F.order d)) u v w

/-- On every triple, the reduction `ddhOTReductionOf` with exact uniform chosen-branch exponents
and `ddhOTProbReduction` accept with probabilities within `2 / 2 ^ n`: only the two chosen-branch
coins differ. -/
private theorem advantage_ddhOTReductionOf_ddhOTProbReduction_le (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool)
    (u v w : F.Carrier d) :
    Game.advantage
        (ProbComp.eval (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
          (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D u v w))
        (ProbComp.eval (F.ddhOTProbReduction n d x D u v w)) ≤ 2 / 2 ^ n := by
  simp only [ddhOTReductionOf, ddhOTProbReduction, ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun bBits => ?_
  rw [Game.advantage_comm]
  have h₁ := F.advantage_bind_sampleExpBits_le n d fun r =>
    (ProbComp.eval (F.sampleExpBits n d)).bind fun sBits =>
      ProbComp.eval (ddhOTReductionWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
        (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D bBits r
        (BitString.binaryValue sBits : ZMod (F.order d)) u v w)
  have h₂ := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun r =>
    F.advantage_bind_sampleExpBits_le n d fun s =>
      ProbComp.eval (ddhOTReductionWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
        (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D bBits r s u v w)
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n :=
        (Game.advantage_triangle _ _ _).trans (add_le_add h₁ h₂)
    _ = 2 / 2 ^ n := by rw [← add_div, one_add_one_eq_two]

/-- The ideal game of a corrupted receiver of `ddhOTProbProtocol n d` with the simulator
`ddhOTReceiverSimProb n d` is within `7 / 2 ^ n` of the random DDH experiment of
`ddhOTProbReduction n d x D`: `5 / 2 ^ n` for the simulator's five bit strings and `2 / 2 ^ n` for
the reduction's two chosen-branch bit strings. -/
private theorem advantage_idealJoint_ddhRandomExperiment_ddhOTProbReduction_le (n : ℕ)
    (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool) :
    Game.advantage
        (ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) {1}
          (F.ddhOTReceiverSimProb n d) x >>= D))
        (ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d)
          (F.ddhOTProbReduction n d x D))) ≤ 7 / 2 ^ n := by
  have hideal := ideal_receiver_eq_ddhRandomExperiment_of (C₀ := DDHOTSenderBitCoins)
    (F.generator d) (F.order d) (F.smul_generator_surjective d) (F.sampleExpBits n d)
    (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D
  have h₁ : Game.advantage
      (ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) {1}
        (F.ddhOTReceiverSimProb n d) x >>= D))
      (ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) {1}
        (ddhOTReceiverSimOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
          (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) x >>= D)) ≤
      5 / 2 ^ n := by
    rw [Game.advantage_comm]
    simp only [ProbComp.eval_bind, eval_idealJoint, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
    exact Game.advantage_bind_le_nnreal _ _ _ fun y =>
      F.advantage_bind_ddhOTReceiverSimProb_le n d _ _ _
  have h₂ : Game.advantage
      (ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d)
        (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
          (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D)))
      (ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d)
        (F.ddhOTProbReduction n d x D))) ≤ 2 / 2 ^ n := by
    simp only [eval_ddhRandomExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun a =>
      Game.advantage_bind_le_nnreal _ _ _ fun b => Game.advantage_bind_le_nnreal _ _ _ fun c =>
        F.advantage_ddhOTReductionOf_ddhOTProbReduction_le n d x D _ _ _
  calc _ ≤ (5 : ℝ≥0) / 2 ^ n + 2 / 2 ^ n := by
        refine (Game.advantage_triangle _ _ _).trans (add_le_add h₁ ?_)
        rw [hideal]
        exact h₂
    _ = _ := by ring

/-- The real DDH experiment of `ddhOTProbReduction n d x D` is within `7 / 2 ^ n` of the real game
of a corrupted receiver of `ddhOTProbProtocol n d`: `2 / 2 ^ n` for the reduction's two
chosen-branch bit strings and `5 / 2 ^ n` for the honest sender's five bit strings. -/
private theorem advantage_ddhRealExperiment_ddhOTProbReduction_realJoint_le (n : ℕ)
    (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool) :
    Game.advantage
        (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d)
          (F.ddhOTProbReduction n d x D)))
        (((F.ddhOTProbProtocol n d).realJoint noOracleWorld {1} x).bind fun r =>
          ProbComp.eval (D r)) ≤ 7 / 2 ^ n := by
  have hreal := real_receiver_eq_ddhRealExperiment_of (C₀ := DDHOTSenderBitCoins)
    (F.generator d) (F.order d) (F.sampleExpBits n d)
    (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D
  have h₄ : Game.advantage
      (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d)
        (F.ddhOTProbReduction n d x D)))
      (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d)
        (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
          (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D))) ≤
      2 / 2 ^ n := by
    rw [Game.advantage_comm]
    simp only [eval_ddhRealExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun a =>
      Game.advantage_bind_le_nnreal _ _ _ fun b =>
        F.advantage_ddhOTReductionOf_ddhOTProbReduction_le n d x D _ _ _
  have h₅ : Game.advantage
      (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d)
        (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
          (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x D)))
      (((F.ddhOTProbProtocol n d).realJoint noOracleWorld {1} x).bind fun r =>
        ProbComp.eval (D r)) ≤ 5 / 2 ^ n := by
    rw [Game.advantage_comm, ← hreal]
    simp only [ddhOTProbProtocol, Protocol.realJoint, evalWith_ddhOTProtocolWith,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
      PMF.pure_map, Prod.map, id, restrict_singleton]
    exact F.advantage_bind_sampleDDHOTSenderBitCoins_le n d fun c₀ =>
      (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
        ProbComp.eval (D (singletonView (ddhOTReceiverViewWith (x 1) bBits
          (c₀.exponent • F.generator d)
          (ddhOTSenderReplyUnchecked (F.generator d) (x 0) c₀
            (ddhOTReceiverMsg (F.generator d) (x 1)
              (BitString.binaryValue bBits : ZMod (F.order d))
              (c₀.exponent • F.generator d)))), otOutputs x))
  calc _ ≤ (2 : ℝ≥0) / 2 ^ n + 5 / 2 ^ n :=
        (Game.advantage_triangle _ _ _).trans (add_le_add h₄ h₅)
    _ = _ := by ring

/-- **Privacy against a corrupted receiver of `ddhOTProbProtocol`, as a concrete bound at a fixed
instance.** For fixed `n`, `d`, inputs `x` and distinguisher `D`, the advantage of `D` between the
ideal joint distribution with `ddhOTReceiverSimProb n d` and the real one is at most the
fixed-group DDH advantage of the explicit fair-coin distinguisher `ddhOTProbReduction n d x D` plus
`14 / 2 ^ n`: `5 / 2 ^ n` for the honest sender's five bit strings, `5 / 2 ^ n` for the simulator's,
and `2 / 2 ^ n` for the reduction's two chosen-branch bit strings in each DDH world. Nothing is
assumed about `D` or the reduction. This is not a computational privacy theorem: `D` is unbounded
and `ddhOTProbReduction` has no efficiency certificate here. `advantage_ddhOTProbReceiverGame_le`
is the game form over a setup law and an environment, with the certified reduction
`ddhOTReceiverToDDHDistinguisher`. -/
theorem semiHonestAdvantage_ddhOTProb_receiver_le (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool) :
    semiHonestAdvantage (F.ddhOTProbProtocol n d) noOracleWorld (otFunctionality (F.Carrier d))
        {1} (F.ddhOTReceiverSimProb n d) x D ≤
      ddhAdvantage (F.order d) (F.generator d) (F.ddhOTProbReduction n d x D) + 14 / 2 ^ n := by
  calc semiHonestAdvantage (F.ddhOTProbProtocol n d) noOracleWorld
        (otFunctionality (F.Carrier d)) {1} (F.ddhOTReceiverSimProb n d) x D
      ≤ 7 / 2 ^ n +
        (ddhAdvantage (F.order d) (F.generator d) (F.ddhOTProbReduction n d x D) + 7 / 2 ^ n) := by
        rw [semiHonestAdvantage, ddhAdvantage]
        exact (Game.advantage_triangle _ _ _).trans (add_le_add
          (F.advantage_idealJoint_ddhRandomExperiment_ddhOTProbReduction_le n d x D)
          ((Game.advantage_triangle _ _ _).trans (add_le_add (Game.advantage_comm _ _).le
            (F.advantage_ddhRealExperiment_ddhOTProbReduction_realJoint_le n d x D))))
    _ = _ := by ring

/-! ### A corrupted receiver of the masked transfer over the fair-coin DDH transfer -/

/-- **The DDH distinguisher of a corrupted receiver of the masked transfer over
`ddhOTProbProtocol n d`**, on the inputs `x` with the coins `c` of `maskedOT` (the sender's pads):
the fair-coin DDH reduction `ddhOTProbReduction`, on the pads and the receiver's choice bit,
applied to the pad-transfer distinguisher `maskedOTTransferDistinguisher` of `D`. -/
@[expose] noncomputable def maskedOTToDDHProbDistinguisher (n : ℕ) (d : F.Desc)
    (mask unmask : F.Carrier d → M → M)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (x : (i : Fin 2) → OTIn M i) (c : (i : Fin 2) → MaskedOTCoins (F.Carrier d) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) M))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    F.Carrier d → F.Carrier d → F.Carrier d → ProbComp Bool :=
  F.ddhOTProbReduction n d (fun s => maskedOTQuery s (x s, c s)) fun r =>
    maskedOTTransferDistinguisher mask unmask S₂ {1} x c D
      (fun s => r.1 ⟨s.val, mem_subCoalition.1 s.property⟩, r.2)

/-- **The masked transfer over the fair-coin DDH transfer of a group family, corrupted receiver,
for one distinguisher.** Step towards [LindellPinkas2009], Theorem 7, not the cited result (#6045):
a concrete bound at a fixed security parameter, group description and instance, with no efficiency
certificate for the reductions and no asymptotic statement.

The semi-honest advantage of `D` against
`(maskedOT mask unmask samplePads).compose fun _ => F.ddhOTProbProtocol n d` for the coalition
`{1}`, with the simulator composed from any simulators `S₁` of `maskedOT` and simulators `S₂` of
the DDH transfer whose member at `{1}` is `F.ddhOTReceiverSimProb n d`, is at most the advantage of
`composeDistinguisher` against `maskedOT` with the ideal pad transfer and `S₁ {1}`, plus the
expectation, over the coins `c` of `maskedOT` (the sender's pads), of the fixed-group DDH advantage
of the explicit fair-coin distinguisher `maskedOTToDDHProbDistinguisher`, plus `14 / 2 ^ n` for the
bit-string exponents (`semiHonestAdvantage_ddhOTProb_receiver_le`). Nothing is assumed about
either advantage. For `S₁ {1} = maskedOTReceiverSim mask samplePads pad` the first term is the
pad-hiding advantage of `maskedOTPadTest` (`semiHonestAdvantage_maskedOT_receiver_eq`). -/
theorem semiHonestAdvantage_maskedOT_ddhOTProb_receiver_le (n : ℕ) (d : F.Desc)
    (mask unmask : F.Carrier d → M → M) (samplePads : ProbComp (F.Carrier d × F.Carrier d))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (F.Carrier d) M) (OTIn M)
        (MaskedOTCoins (F.Carrier d)) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {1} = F.ddhOTReceiverSimProb n d) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) M))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (semiHonestAdvantage
        ((maskedOT mask unmask samplePads).compose fun _ => F.ddhOTProbProtocol n d)
        noOracleWorld (otFunctionality M) {1}
        (composeSim (maskedOT mask unmask samplePads) (S₁ {1}) (fun _ => S₂)) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld (F.Carrier d))
          (otFunctionality M) {1} (S₁ {1}) x
          (composeDistinguisher (maskedOT mask unmask samplePads) (fun _ => S₂) {1} x D) +
        ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
          (ddhAdvantage (F.order d) (F.generator d)
            (F.maskedOTToDDHProbDistinguisher n d mask unmask S₂ x c D) : ℝ≥0∞) +
        14 / 2 ^ n := by
  have hcast : ((14 / 2 ^ n : ℝ≥0) : ℝ≥0∞) = 14 / 2 ^ n := by
    rw [ENNReal.coe_div (pow_ne_zero n two_ne_zero), ENNReal.coe_pow, ENNReal.coe_ofNat,
      ENNReal.coe_ofNat]
  have hc (c : (i : Fin 2) → MaskedOTCoins (F.Carrier d) i) :
      (semiHonestAdvantage (F.ddhOTProbProtocol n d) noOracleWorld
          (otFunctionality (F.Carrier d)) (subCoalition (Function.Embedding.refl (Fin 2)) {1})
          (S₂ (subCoalition (Function.Embedding.refl (Fin 2)) {1}))
          (fun s => maskedOTQuery s (x s, c s))
          (maskedOTTransferDistinguisher mask unmask S₂ {1} x c D) : ℝ≥0∞) ≤
        (ddhAdvantage (F.order d) (F.generator d)
          (F.maskedOTToDDHProbDistinguisher n d mask unmask S₂ x c D) : ℝ≥0∞) + 14 / 2 ^ n := by
    rw [semiHonestAdvantage_of_coalition_eq (F.ddhOTProbProtocol n d) noOracleWorld
      (otFunctionality (F.Carrier d)) S₂ (Finset.ext fun _ => mem_subCoalition), hS₂, ← hcast,
      ← ENNReal.coe_add, ENNReal.coe_le_coe]
    exact F.semiHonestAdvantage_ddhOTProb_receiver_le n d _ _
  refine (semiHonestAdvantage_maskedOT_compose_le_transfer mask unmask samplePads noOracleWorld
    (F.ddhOTProbProtocol n d) S₁ S₂ {1} x D).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  calc _ ≤ ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
        ((ddhAdvantage (F.order d) (F.generator d)
          (F.maskedOTToDDHProbDistinguisher n d mask unmask S₂ x c D) : ℝ≥0∞) + 14 / 2 ^ n) :=
        tsum_le_tsum fun c => mul_le_mul' le_rfl (hc c)
    _ = _ := by
        simp only [mul_add]
        rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### A sampled environment of a challenged transfer -/

/-- **The DDH distinguisher of a sampled environment of a challenged transfer.** Given a DDH triple
`(u, v, w)` in the group of `d`, run the environment `E n d`. If it has already decided a bit,
return it. If it stops at a challenged transfer `c` whose corrupted slots are `{1}` (the receiver),
run the fair-coin reduction `ddhOTProbReduction n d` on the query `c.query` with the guessing stage
`c.guess` and the triple; for any other coalition return `false`.

Step towards #6045, not a cited result. No efficiency certificate is claimed: `E n d` is an
arbitrary program and nothing bounds it or the guessing stage it outputs. -/
@[expose] noncomputable def roundEnvToDDHDistinguisher
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (F.Carrier d))
      (fun _ => ddhOTSchedule (F.Carrier d))
      (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)))) : F.DDHDistinguisher :=
  fun n d u v w => do
    match ← E n d with
    | .inl b => pure b
    | .inr c =>
      if h : c.coalition = {1} then
        F.ddhOTProbReduction n d c.query (fun r => c.guess
            (fun s => r.1 ⟨s.val, h ▸ s.property⟩, r.2)) u v w
      else pure false

/-- **The challenged fair-coin DDH transfer against a sampled environment, corrupted receiver,
under a setup law.** Step towards #6045, not a cited result: original bookkeeping, a concrete bound
at a fixed security parameter with no asymptotic statement and no efficiency certificate for
`roundEnvToDDHDistinguisher E`.

Let the environment `E n d`, sampled after the group description `d`, either decide a bit or stop
at a challenged transfer, and let every challenge in its support have the corrupted slots `{1}`
(`hE`). Then the advantage between the ideal round game, on the ideal transfer with simulators
`S₂ d` whose member at `{1}` is `F.ddhOTReceiverSimProb n d`, and the real round game, on
`F.ddhOTProbProtocol n d`, both taken over `setup n` and the environment, is at most the advantage
of the one distinguisher `F.roundEnvToDDHDistinguisher E` between `F.ddhRealGame setup` and
`F.ddhRandomGame setup`, plus `14 / 2 ^ n` for the bit-string exponents. The absolute value is
outside the expectation over the setup and the environment on both sides. Nothing is assumed about
either advantage. -/
theorem advantage_bind_roundGame_ddhOTProb_le (setup : ℕ → PMF F.Desc) (n : ℕ)
    (S₂ : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : ∀ d, S₂ d {1} = F.ddhOTReceiverSimProb n d)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (F.Carrier d))
      (fun _ => ddhOTSchedule (F.Carrier d))
      (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))))
    (hE : ∀ d c, Sum.inr c ∈ (ProbComp.eval (E n d)).support → c.coalition = {1}) :
    Game.advantage
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun op J q =>
            ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ d J) q)))
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun _ J q => (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)) ≤
      Game.advantage (F.ddhRealGame setup (F.roundEnvToDDHDistinguisher E) n)
        (F.ddhRandomGame setup (F.roundEnvToDDHDistinguisher E) n) + 14 / 2 ^ n := by
  have hI : Game.advantage
      ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
        (roundGame fun op J q =>
          ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ d J) q)))
      (F.ddhRandomGame setup (F.roundEnvToDDHDistinguisher E) n) ≤ 7 / 2 ^ n := by
    simp only [ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment, roundEnvToDDHDistinguisher,
      ProbComp.eval_bind]
    refine Game.advantage_bind_le_nnreal _ _ _ fun d => ?_
    simp only [← PMF.bind_comm (ProbComp.eval (E n d))]
    refine Game.advantage_bind_le_of_support _ _ _ fun e he => ?_
    cases e with
    | inl b =>
      simp only [roundGame, Sum.elim_inl, ProbComp.eval_pure, PMF.bind_const,
        Game.advantage_self, zero_le]
    | inr c =>
      obtain ⟨op, J, x, g⟩ := c
      obtain rfl : J = {1} := hE d _ he
      have h := F.advantage_idealJoint_ddhRandomExperiment_ddhOTProbReduction_le n d x g
      rw [ProbComp.eval_bind, eval_ddhRandomExperiment, ← hS₂ d] at h
      simp only [↓reduceDIte]
      exact h
  have hR : Game.advantage (F.ddhRealGame setup (F.roundEnvToDDHDistinguisher E) n)
      ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
        (roundGame fun _ J q => (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)) ≤
      7 / 2 ^ n := by
    simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment, roundEnvToDDHDistinguisher,
      ProbComp.eval_bind]
    refine Game.advantage_bind_le_nnreal _ _ _ fun d => ?_
    simp only [← PMF.bind_comm (ProbComp.eval (E n d))]
    refine Game.advantage_bind_le_of_support _ _ _ fun e he => ?_
    cases e with
    | inl b =>
      simp only [roundGame, Sum.elim_inl, ProbComp.eval_pure, PMF.bind_const,
        Game.advantage_self, zero_le]
    | inr c =>
      obtain ⟨op, J, x, g⟩ := c
      obtain rfl : J = {1} := hE d _ he
      have h := F.advantage_ddhRealExperiment_ddhOTProbReduction_realJoint_le n d x g
      rw [eval_ddhRealExperiment] at h
      simp only [↓reduceDIte]
      exact h
  calc _ ≤ 7 / 2 ^ n +
        (Game.advantage (F.ddhRealGame setup (F.roundEnvToDDHDistinguisher E) n)
          (F.ddhRandomGame setup (F.roundEnvToDDHDistinguisher E) n) + 7 / 2 ^ n) :=
        (Game.advantage_triangle _
          (F.ddhRandomGame setup (F.roundEnvToDDHDistinguisher E) n) _).trans (add_le_add hI
            ((Game.advantage_triangle _
              (F.ddhRealGame setup (F.roundEnvToDDHDistinguisher E) n) _).trans
                (add_le_add (Game.advantage_comm _ _).le hR)))
    _ = _ := by ring


end Cslib.Crypto.PrimeOrderGroupFamily
