/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridChallenge
public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridProg
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDHProb
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF

/-!
# One masked transfer over the fair-coin DDH transfer under a sampled setup: the library games

The hybrid argument for an outer protocol over sequential masked transfers over a pad transfer
(`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/Mixture.lean`) leaves, for every transfer, two
advantages of one environment that stops at a challenged masked transfer: the *pad-hiding* term,
between the ideal and the real game of `maskedOT` with the ideal pad transfer against
`composeDistinguisher`, and the *pad-transfer* term, between the ideal and the real game of the pad
transfer. This module bounds both by games of the library, for the key-derivation mask
`F.kdfMask H d` over the groups of a `PrimeOrderGroupFamily` `F`, with the sender's pads drawn
with fair-coin exponents (`F.kdfPadsProb n d`) and the pad transfer run by the fair-coin DDH
transfer `F.ddhOTProbProtocol n d`, when the group description `d` is drawn from a setup law
`setup n` and the environment is a program `E n d : ProbComp _`.

* `F.advantage_bind_kdfPadsProb_le`: the fair-coin pads are within `2 / 2 ^ n` of the exactly
  uniform pads `F.kdfPads d` against every test.
* `F.advantage_bind_padHiding_le_kdf`: the pad-hiding term is at most the advantage of the one
  distinguisher `F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)` between
  `F.kdfIdealGame` and `F.kdfRealGame` under `setup`, the games of `F.SecureKDF`, plus
  `4 / 2 ^ n` for the fair-coin exponents of the pads in the two games.
* `F.advantage_bind_padTransfer_le_ddh`: for any sampler of the pads, the pad-transfer term is at
  most the advantage of the one distinguisher
  `F.roundEnvToDDHDistinguisher (F.padTransferEnv H samplePads S₂ E)` between `F.ddhRealGame` and
  `F.ddhRandomGame` under `setup`, the games of `F.DDH`, plus `14 / 2 ^ n`.

In both bounds the absolute value of the game advantage is outside the expectation over the setup
and the environment, and the distinguisher runs the environment itself; the additive terms are
statistical.

This is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem; it is original bookkeeping and no cited
statement is claimed.

## What is not proved

* No efficiency certificate: neither distinguisher is shown to be uniform strict PPT, so neither
  `F.SecureKDF` nor `F.DDH` is applied here (#6045).
* The hypotheses on the environment are about the challenges in its support: the corrupted slots
  are the receiver `{1}`, and for the pad-hiding term the receiver's output has the length
  `msgLen n` of the derived keys. `Composition.ForallChallenge` supplies them for the environments
  of the hybrid argument.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfPadsProb`: two pads with independent fair-coin exponents.
* `Cslib.Crypto.PrimeOrderGroupFamily.padHidingEnv`: an environment of the masked transfer over the
  DDH transfer, as an environment of `maskedOT` with the ideal pad transfer.
* `Cslib.Crypto.PrimeOrderGroupFamily.padTransferEnv`: the same environment followed by the masked
  transfer up to its pad transfer, as an environment of the DDH transfer.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_kdfPadsProb_le`
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_padHiding_le_kdf`
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_padTransfer_le_ddh`

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Attack Games 10.6 and 11.3, as formalized by `ddhRealGame`,
  `ddhRandomGame`, `kdfRealGame` and `kdfIdealGame`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Protocols.MPC
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- The sender's pads at group parameters `d` with fair-coin exponents: `c₀ • g` and `c₁ • g` for
the generator `g` and the residues `c₀, c₁ : ZMod (F.order d)` of two independent raw fair-coin bit
strings drawn by `F.sampleExpBits n d`. They are within `2 / 2 ^ n` of the exactly uniform pads
`F.kdfPads d` (`advantage_bind_kdfPadsProb_le`). -/
@[expose] noncomputable def kdfPadsProb (n : ℕ) (d : F.Desc) :
    ProbComp (F.Carrier d × F.Carrier d) := do
  let b₀ ← F.sampleExpBits n d
  let b₁ ← F.sampleExpBits n d
  return ((Cslib.BitString.binaryValue b₀ : ZMod (F.order d)) • F.generator d,
    (Cslib.BitString.binaryValue b₁ : ZMod (F.order d)) • F.generator d)

/-- Replacing the fair-coin pads `F.kdfPadsProb n d` by the exactly uniform pads `F.kdfPads d`
changes `Game.advantage` by at most `2 / 2 ^ n`: `1 / 2 ^ n` for each exponent
(`advantage_bind_sampleExpBits_le`). -/
theorem advantage_bind_kdfPadsProb_le (n : ℕ) (d : F.Desc)
    (k : F.Carrier d × F.Carrier d → Game) :
    Game.advantage ((ProbComp.eval (F.kdfPadsProb n d)).bind k)
      ((ProbComp.eval (F.kdfPads d)).bind k) ≤ 2 / 2 ^ n := by
  have h₁ := F.advantage_bind_sampleExpBits_le n d fun c₀ =>
    (ProbComp.eval (F.sampleExpBits n d)).bind fun b₁ =>
      k (c₀ • F.generator d,
        (Cslib.BitString.binaryValue b₁ : ZMod (F.order d)) • F.generator d)
  have h₂ := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun c₀ =>
    F.advantage_bind_sampleExpBits_le n d fun c₁ => k (c₀ • F.generator d, c₁ • F.generator d)
  simp only [kdfPadsProb, kdfPads, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n :=
        (Game.advantage_triangle _ _ _).trans (add_le_add h₁ h₂)
    _ = 2 / 2 ^ n := by rw [← add_div, one_add_one_eq_two]

/-- **The pad-hiding environment.** An environment `E n d` that stops at a challenged masked
transfer over the DDH transfer becomes an environment of `maskedOT` with the ideal pad transfer:
the challenge keeps its corrupted slots and queries, and its guessing stage becomes
`composeDistinguisher`, which simulates the pad transfer with `S₂ n d` and runs the given guess.
The sender's pads are drawn by `samplePads n d`. -/
@[expose] noncomputable def padHidingEnv (H : F.Desc × List Bool → List Bool)
    (samplePads : (n : ℕ) → (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d))
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))))
    (n : ℕ) (d : F.Desc) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d))) :=
  (Sum.map id fun c =>
    { op := c.op
      coalition := c.coalition
      query := c.query
      guess := composeDistinguisher (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
        (fun _ => S₂ n d) c.coalition c.query c.guess }) <$> E n d

/-- **The pad-transfer environment.** An environment `E n d` that stops at a challenged masked
transfer over the DDH transfer, followed by the masked transfer up to its pad transfer
(`composeRoundEnvProg` of `maskedOT` at hop `0`: it samples the sender's pads with
`samplePads n d`), is an environment of the DDH transfer: it stops at the challenged pad transfer,
and its guessing stage simulates the rest of the masked transfer and runs the given guess. -/
@[expose] noncomputable def padTransferEnv (H : F.Desc × List Bool → List Bool)
    (samplePads : (n : ℕ) → (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d))
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))))
    (n : ℕ) (d : F.Desc) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (F.Carrier d))
      (fun _ => ddhOTSchedule (F.Carrier d))
      (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))) :=
  E n d >>= Sum.elim (fun b => pure (Sum.inl b)) fun c =>
    composeRoundEnvProg (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
      (otWorld (F.Carrier d))
      (fun _ J q => (F.ddhOTProbProtocol n d).realJointProg noOracleWorld J q)
      (fun _ => S₂ n d) c.coalition c.query c.guess 0

/-- Step towards [LindellPinkas2009], Theorem 7, not the cited result (#6045): the pad-hiding term
is at most a key-derivation advantage plus `4 / 2 ^ n`; no efficiency certificate for the
distinguisher is proved and `F.SecureKDF` is not applied.

Let the group description `d` be drawn from `setup n` and let `E n d` be an environment program
whose challenges are masked transfers with the corrupted slots `{1}` and a receiver's output of
length `msgLen n`. When every derived key has length `msgLen n`, the sender's pads are the
fair-coin pads `F.kdfPadsProb n d` and the simulator of `maskedOT` for the receiver is
`maskedOTReceiverSim` with these pads and a uniform `msgLen n`-bit word, the advantage of the
environment between the ideal and the real game of `maskedOT` with the key-derivation mask and the
ideal pad transfer, against `composeDistinguisher`, is at most the advantage of the one
distinguisher `F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)` between
`F.kdfIdealGame setup msgLen` and `F.kdfRealGame setup H`, plus `4 / 2 ^ n`: `2 / 2 ^ n` in each
of the two games for replacing the fair-coin exponents of the pads by the exactly uniform ones of
the key-derivation games. Both absolute values of the game advantages are outside the expectation
over the setup and the environment. -/
theorem advantage_bind_padHiding_le_kdf (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPadsProb n d)
      (Cslib.BitString.sampleList (msgLen n)))
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))))
    (hE : ∀ d c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2)) ∧
        (otOutputs (M := List Bool) c.query 1 : List Bool).length = msgLen n) :
    Game.advantage
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind (Sum.elim PMF.pure fun c =>
          (ProbComp.eval (idealJoint (otFunctionality (List Bool)) c.coalition
            (Sm d c.coalition) c.query)).bind fun r =>
              ProbComp.eval (composeDistinguisher
                (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)) (fun _ => S₂ n d)
                c.coalition c.query c.guess r)))
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind (Sum.elim PMF.pure fun c =>
          ((maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)).realJoint
            (otWorld (F.Carrier d)) c.coalition c.query).bind fun r =>
              ProbComp.eval (composeDistinguisher
                (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPadsProb n d)) (fun _ => S₂ n d)
                c.coalition c.query c.guess r))) ≤
      Game.advantage
          (F.kdfIdealGame setup msgLen
            (F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)) n)
          (F.kdfRealGame setup H
            (F.roundEnvToKDFDistinguisher H (F.padHidingEnv H F.kdfPadsProb S₂ E)) n) +
        4 / 2 ^ n := by
  have hE' : ∀ d c',
      Sum.inr c' ∈ (ProbComp.eval (F.padHidingEnv H F.kdfPadsProb S₂ E n d)).support →
        c'.coalition = ({1} : Finset (Fin 2)) ∧
          (otOutputs (M := List Bool) c'.query 1 : List Bool).length = msgLen n := by
    rintro d c' hc'
    rw [padHidingEnv, ProbComp.eval_map, PMF.support_map] at hc'
    rcases hc' with ⟨_ | c, hz, ⟨⟩⟩
    exact hE d c hz
  have h := F.advantage_bind_roundGame_kdfMaskedOT_le_kdf setup H msgLen n
    (fun d => F.kdfPadsProb n d) (fun d k => F.advantage_bind_kdfPadsProb_le n d k) Sm hSm
    (F.padHidingEnv H F.kdfPadsProb S₂ E) hH hE'
  rw [← add_div, show (2 : ℝ≥0) + 2 = 4 by norm_num] at h
  refine le_of_eq_of_le ?_ h
  simp only [padHidingEnv, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  refine congrArg₂ Game.advantage ?_ ?_ <;>
    exact congrArg (PMF.bind _) (funext fun d => congrArg (PMF.bind _) (funext fun z => by
      cases z <;> rfl))

/-- Step towards [LindellPinkas2009], Theorem 7, not the cited result (#6045): the pad-transfer
term is a DDH advantage up to `14 / 2 ^ n`; no efficiency certificate for the distinguisher is
proved and `F.DDH` is not applied.

Let the group description `d` be drawn from `setup n` and let `E n d` be an environment program
whose challenges are masked transfers with the corrupted slots `{1}`, and let the sender's pads be
drawn by any sampler `samplePads n d`. When the simulator of the DDH transfer for the receiver is
`F.ddhOTReceiverSimProb n d`, the advantage of the environment that runs `E n d` and then the
masked transfer up to its pad transfer, between the ideal and the real game of the pad transfer
run by `F.ddhOTProbProtocol n d`, is at most the advantage of the one distinguisher
`F.roundEnvToDDHDistinguisher (F.padTransferEnv H samplePads S₂ E)` between `F.ddhRealGame` and
`F.ddhRandomGame` under `setup`, plus `14 / 2 ^ n` for the bit-string exponents. Every absolute
value is outside the expectation over the setup and the environment. -/
theorem advantage_bind_padTransfer_le_ddh (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (samplePads : (n : ℕ) → (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d)) (n : ℕ)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)))
      (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))))
    (hE : ∀ d c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2))) :
    Game.advantage
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind (Sum.elim PMF.pure fun c =>
          (composeRoundEnv (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
            (otWorld (F.Carrier d)) noOracleWorld (fun _ => F.ddhOTProbProtocol n d)
            (fun _ => S₂ n d) c.coalition c.query c.guess 0).bind
              (roundGame fun op J q =>
                ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ n d J) q))))
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind (Sum.elim PMF.pure fun c =>
          (composeRoundEnv (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
            (otWorld (F.Carrier d)) noOracleWorld (fun _ => F.ddhOTProbProtocol n d)
            (fun _ => S₂ n d) c.coalition c.query c.guess 0).bind
              (roundGame fun _ J q => (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q))) ≤
      Game.advantage
          (F.ddhRealGame setup
            (F.roundEnvToDDHDistinguisher (F.padTransferEnv H samplePads S₂ E)) n)
          (F.ddhRandomGame setup
            (F.roundEnvToDDHDistinguisher (F.padTransferEnv H samplePads S₂ E)) n) +
        14 / 2 ^ n := by
  have heval (d : F.Desc) : ProbComp.eval (F.padTransferEnv H samplePads S₂ E n d) =
      (ProbComp.eval (E n d)).bind (Sum.elim (fun b => PMF.pure (Sum.inl b)) fun c =>
        composeRoundEnv (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
          (otWorld (F.Carrier d)) noOracleWorld (fun _ => F.ddhOTProbProtocol n d)
          (fun _ => S₂ n d) c.coalition c.query c.guess 0) := by
    rw [padTransferEnv, ProbComp.eval_bind]
    refine congrArg _ (funext fun z => ?_)
    cases z with
    | inl b => exact ProbComp.eval_pure _
    | inr c =>
      exact eval_composeRoundEnvProg (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads n d))
        (otWorld (F.Carrier d)) noOracleWorld (fun _ => F.ddhOTProbProtocol n d)
        (fun _ J q => Protocol.eval_realJointProg _ _ J q) (fun _ => S₂ n d) c.coalition c.query
        c.guess 0
  have hsupp : ∀ d c, Sum.inr c ∈ (ProbComp.eval (F.padTransferEnv H samplePads S₂ E n d)).support →
      c.coalition = {1} := by
    rintro d c hc
    rw [heval, PMF.mem_support_bind_iff] at hc
    rcases hc with ⟨b | c₀, hz, hzc⟩
    · simp at hzc
    · rw [Sum.elim_inr] at hzc
      refine ForallChallenge.of_mem_support_composeRoundEnv
        (Q := fun _ J _ => J = ({1} : Finset (Fin 2))) _ _ _ _ _ _ _ _ _ (fun c₁ _ => ?_) hzc
      refine ⟨?_, fun _ => trivial⟩
      rw [hE d c₀ hz]
      exact Finset.ext fun _ => mem_subCoalition
  simpa only [heval, bind_elim_bind_roundGame] using
    F.advantage_bind_roundGame_ddhOTProb_le setup n (S₂ n) hS₂
      (F.padTransferEnv H samplePads S₂ E) hsupp

end Cslib.Crypto.PrimeOrderGroupFamily
