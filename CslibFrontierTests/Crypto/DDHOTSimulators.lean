/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators

/-! # Fair-coin semi-honest security of DDH oblivious transfer: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators` under module encapsulation:
* the encoded words of a simulator's input, and of a receiver's view words;
* the PPT certificates of the `sampleExp` simulator families, and the predicate
  `SimulatorFamily.IsPPT` introduced from a machine certificate and consumed as one;
* the statistical distance of the `sampleExp` simulators from the exact-sampling ones, and the
  concrete game bounds `advantage_ddhOTProbSenderGame_le` and `advantage_ddhOTProbReceiverGame_le`;
* unconditional sender security `ddhOTProbFamily_semiHonestSecure_sender` and full-coalition DDH
  security `DDH.ddhOTSemiHonestSecure`, unfolded to their witnesses. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTSimulators

-- The encoded words of a simulator's input: the unary security parameter, the group parameters
-- and the words of the coalition's inputs and outputs, all but the last framed.
example (F : PrimeOrderGroupFamily) (x : SimInput F.ddhOTProbFamily {1}) :
    encSimInput F.ddhOTEncoding x =
      encPair encUnary (encPair F.encDesc (encPair encBits encBits))
        (x.secParam, x.desc, F.ddhOTEncoding.input.encCoalition x.secParam x.desc {1} x.inputs,
          F.ddhOTEncoding.output.encCoalition x.secParam x.desc {1} x.outputs) :=
  encSimInput_apply _ x

-- The encoded words of a receiver's view.
example (w : DDHOTReceiverViewWords) :
    encDDHOTReceiverViewWords w =
      encPair encBool (encPair encNat (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))
        (w.choiceBit, w.coin, w.firstMessage, w.ephemeral₀, w.body₀, w.ephemeral₁, w.body₁) :=
  encDDHOTReceiverViewWords_apply w

-- The words of a receiver's view determine it.
example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) :=
  F.ddhOTReceiverViewWords_injective d

-- Both `sampleExp` simulator families are PPT for `ddhOTProbFamily`.
example (F : PrimeOrderGroupFamily) :
    (F.ddhOTSenderSimSampleExp (proto := F.ddhOTProbProtocol)).IsPPT F.ddhOTEncoding ∧
      (F.ddhOTReceiverSimSampleExp (proto := F.ddhOTProbProtocol)).IsPPT F.ddhOTEncoding :=
  ⟨F.isPPT_ddhOTSenderSimSampleExp, F.isPPT_ddhOTReceiverSimSampleExp⟩

-- Introducing the predicate: a sender simulator family for `ddhOTProbFamily` with the same output
-- laws as `ddhOTSenderSimSampleExp` is PPT, through the latter's machine certificate.
example (F : PrimeOrderGroupFamily) (S : SimulatorFamily F.ddhOTProbFamily {0})
    (hS : ∀ n d xI yI,
      ProbComp.eval (S n d xI yI) = ProbComp.eval (F.ddhOTSenderSimSampleExp n d xI yI)) :
    S.IsPPT F.ddhOTEncoding :=
  IsPPTOn.congr F.isPPT_ddhOTSenderSimSampleExp fun x => by
    simp only [ProbComp.eval_map, hS]

-- Consuming the predicate: the receiver simulator family that `DDH.ddhOTSemiHonestSecure` provides
-- at `{1}` writes view words of polynomially bounded length.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ (S : SimulatorFamily F.ddhOTProbFamily {1}) (c d : ℕ),
      ∀ (x : SimInput F.ddhOTProbFamily {1}) v,
        v ∈ (ProbComp.eval (S x.secParam x.desc x.inputs x.outputs)).support →
        (F.ddhOTEncoding.view.encCoalition x.secParam x.desc {1} v).length ≤
          c * ((encSimInput F.ddhOTEncoding x).length + 1) ^ d := by
  obtain ⟨S, hS, -⟩ := hDDH.ddhOTSemiHonestSecure {1}
  obtain ⟨c, d, h⟩ := IsPPTOn.length_le hS
  exact ⟨S, c, d, fun x v hv => h x _ (by
    simpa only [ProbComp.eval_map, PMF.support_map] using Set.mem_image_of_mem _ hv)⟩

-- Against a corrupted receiver, the ideal games with the exact-sampling and the `sampleExp`
-- simulators differ by at most `6 / 2 ^ n`, for every environment.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage
        (F.ddhOTProbFamily.idealGame setup {1}
          (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n)
        (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimSampleExp Z n) ≤ 6 / 2 ^ n :=
  ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTReceiverSimSampleExp_le n) Z

-- Concrete bounds for `ddhOTProbFamily` against unbounded environments at `{0}` and `{1}`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (Z₀ : Environment F.ddhOTProbFamily {0}) (Z₁ : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {0} Z₀ n)
        (F.ddhOTProbFamily.idealGame setup {0} F.ddhOTSenderSimSampleExp Z₀ n) ≤ 12 / 2 ^ n ∧
      Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z₁ n)
          (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimSampleExp Z₁ n) ≤
        Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z₁) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z₁) n) + 18 / 2 ^ n :=
  ⟨F.advantage_ddhOTProbSenderGame_le setup Z₀ n, F.advantage_ddhOTProbReceiverGame_le setup Z₁ n⟩

-- Unconditional semi-honest sender security of `ddhOTProbFamily` (no DDH assumption needed).
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) :
    ∃ S : SimulatorFamily F.ddhOTProbFamily {0}, S.IsPPT F.ddhOTEncoding ∧
      Game.Indistinguishable (F.ddhOTProbFamily.realGame setup {0})
        (F.ddhOTProbFamily.idealGame setup {0} S) (Environment.IsPPT F.ddhOTEncoding) :=
  F.ddhOTProbFamily_semiHonestSecure_sender setup

-- Under DDH, `ddhOTProbFamily` is semi-honest secure for all four static coalitions: `∅`, `{0}`,
-- `{1}` and `Finset.univ`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    F.ddhOTProbFamily.SemiHonestSecure setup ∅ F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup {0} F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup {1} F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup Finset.univ F.ddhOTEncoding :=
  ⟨hDDH.ddhOTSemiHonestSecure ∅, hDDH.ddhOTSemiHonestSecure {0}, hDDH.ddhOTSemiHonestSecure {1},
    hDDH.ddhOTSemiHonestSecure Finset.univ⟩

end CslibFrontierTests.Crypto.DDHOTSimulators
