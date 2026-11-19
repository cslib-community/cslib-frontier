/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Tactic.Negligible

/-! # Fair-coin DDH oblivious transfer as a protocol family: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family` and of the asymptotic notion in
`CslibFrontier.Crypto.Protocols.MPC.Asymptotic`, under module encapsulation:
* exact correctness of the fair-coin protocol `ddhOTProbProtocol` in every supported execution;
* the encoded words of a guessing-stage input, and the words of a receiver's view under
  `ddhOTEncoding`, including preservation of distinct raw coin bit strings (`[]` vs `[false]`) that
  have the same `ZMod q` residue `0`;
* a receiver-corrupting environment for `ddhOTProbFamily` that satisfies `Environment.IsPPT`, so
  the class of admitted environments is not empty;
* the concrete `9 / 2 ^ n` bound for a corrupted receiver against `ddhOTReceiverSimOf`, and its
  asymptotic consequence under DDH through the reduction's certificate. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTFamily

-- Every supported execution of the fair-coin protocol `ddhOTProbProtocol` computes `otOutputs`.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i)
    {r : ((i : Fin 2) → PartyView (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i)}
    (hr : r ∈ ((F.ddhOTProbProtocol n d).evalWith noOracleWorld x).support) :
    r.2 = otOutputs x :=
  ddhOTProtocolWith_output_of_mem_support (F.generator d) (F.order d) x hr

-- The encoded words of a guessing-stage input: the unary security parameter, the group
-- parameters, the state, the word of the corrupted receiver's view and the word of the outputs,
-- all but the last framed.
example (F : PrimeOrderGroupFamily) (y : GuessInput F.ddhOTProbFamily {1}) :
    encGuessInput F.ddhOTEncoding y =
      encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
        (y.secParam, y.desc, y.state,
          F.ddhOTEncoding.view.encCoalition y.secParam y.desc {1} y.views,
          F.ddhOTEncoding.output.encAll y.secParam y.desc y.outputs) :=
  encGuessInput_apply _ y

-- Under `ddhOTEncoding`, a receiver's view is written as its view words, preserving raw coin bits.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc)
    (v : PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
      (ddhOTSchedule (F.Carrier d)) 1) :
    F.ddhOTEncoding.view.enc 1 (F.ddhOTEncoding.view.rep n d 1 v) =
      encDDHOTReceiverViewWords (F.ddhOTReceiverViewWords d v) :=
  rfl

-- Distinct raw coin bit strings (`[]` vs `[false]`) with identical `ZMod (F.order d)` residue `0`
-- remain distinct in `PartyView` and under `ddhOTEncoding.view`.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) (u : F.Carrier d)
    (reply : (F.Carrier d × F.Carrier d) × (F.Carrier d × F.Carrier d)) :
    (BitString.binaryValue ([] : List Bool) : ZMod (F.order d)) =
      (BitString.binaryValue [false] : ZMod (F.order d)) ∧
    F.ddhOTEncoding.view.enc 1
      (F.ddhOTEncoding.view.rep n d 1
        (ddhOTReceiverViewWith (C₀ := DDHOTSenderBitCoins) false [] u reply)) ≠
    F.ddhOTEncoding.view.enc 1
      (F.ddhOTEncoding.view.rep n d 1
        (ddhOTReceiverViewWith (C₀ := DDHOTSenderBitCoins) false [false] u reply)) := by
  refine ⟨rfl, fun h => ?_⟩
  have hv := (F.ddhOTEncoding.view.rep n d 1).injective
    ((F.ddhOTEncoding.view.enc 1).injective h)
  cases hv

/-- The inputs of the environment below: the messages `0` and `g` and the choice bit `false`. -/
noncomputable def constantInputs (F : PrimeOrderGroupFamily) (d : F.Desc) :
    (i : Fin 2) → OTIn (F.Carrier d) i :=
  fun i => Fin.cases (motive := fun i => OTIn (F.Carrier d) i) (0, F.generator d) (fun _ => false) i

/-- A receiver-corrupting environment for `ddhOTProbFamily` that sends the messages `0` and `g`
with choice bit `false`, and always guesses `true`. -/
noncomputable def constantProbEnvironment (F : PrimeOrderGroupFamily) :
    Environment F.ddhOTProbFamily {1} where
  choose _ d := pure ⟨constantInputs F d, []⟩
  guess _ _ _ _ := pure true

-- The class of PPT environments for `ddhOTProbFamily` is not empty.
example (F : PrimeOrderGroupFamily) : (constantProbEnvironment F).IsPPT F.ddhOTEncoding where
  choose := by
    refine (ComputableInPolyTime.isPPTOn (f := fun p : ℕ × F.Desc =>
      ((fun i => F.ddhOTEncoding.input.rep p.1 p.2 i (constantInputs F p.2 i)), ([] : List Bool)))
      ((ComputableInPolyTime.dpi fun i => ?_).prod (.const []))).congr fun _ => rfl
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · exact (computableInPolyTime_encode_zero (d := fun p : ℕ × F.Desc => p.2) (by fun_prop)).prod
        (computableInPolyTime_encode_generator (d := fun p : ℕ × F.Desc => p.2) (by fun_prop))
    · exact ComputableInPolyTime.const false
  guess := (ComputableInPolyTime.const true).isPPTOn

-- Against a corrupted receiver and `ddhOTReceiverSimOf`, the advantage is bounded by the DDH
-- advantage of `ddhOTReceiverToDDHDistinguisher` plus `9 / 2 ^ n`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
        (F.ddhOTProbFamily.idealGame setup {1}
          (fun n d => ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
            (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 9 / 2 ^ n :=
  F.advantage_ddhOTReceiverGame_le setup Z n

-- Under DDH, every PPT receiver-corrupting environment has negligible advantage against
-- `ddhOTReceiverSimOf`: the reduction's certificate lets `F.DDH setup` apply to it.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup)
    (Z : Environment F.ddhOTProbFamily {1}) (hZ : Z.IsPPT F.ddhOTEncoding) :
    Negligible fun n => Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
      (F.ddhOTProbFamily.idealGame setup {1}
        (fun n d => ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) Z n) := by
  have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hZ)
  negligible using F.advantage_ddhOTReceiverGame_le setup Z

end CslibFrontierTests.Crypto.DDHOTFamily
