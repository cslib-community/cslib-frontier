/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators

/-! # Stand-alone semi-honest security of fair-coin DDH oblivious transfer: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators` under module encapsulation:
* the encoded words of a simulator's input, and of a receiver's view words (with raw coin bits);
* the PPT certificates of the `sampleExpBits` simulator families, and the predicate
  `SimulatorFamily.IsPPT` introduced from a machine certificate and consumed as one;
* the `5 / 2 ^ n` statistical distance of `ddhOTReceiverSimProb` from `ddhOTReceiverSimOf`, and the
  concrete game bounds `advantage_ddhOTProbSenderGame_le` (`≤ 2 / 2 ^ n`) and
  `advantage_ddhOTProbReceiverGame_le` (`≤ ddhAdv + 14 / 2 ^ n`);
* unconditional stand-alone sender security `ddhOTProbFamily_semiHonestSecure_sender` and
  all-coalition stand-alone security `DDH.ddhOTProbFamily_semiHonestSecure` (step toward
  [BonehShoup2023], Theorem 23.7), unfolded to their witnesses. -/

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

-- The encoded words of a receiver's view, with `coinBits` encoded directly via `encBits`.
example (w : DDHOTReceiverViewWords) :
    encDDHOTReceiverViewWords w =
      encPair encBool (encPair encBits (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))
        (w.choiceBit, w.coinBits, w.firstMessage, w.ephemeral₀, w.body₀, w.ephemeral₁, w.body₁) :=
  encDDHOTReceiverViewWords_apply w

-- The words of a receiver's view determine it, including the raw coin bit string.
example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) :=
  F.ddhOTReceiverViewWords_injective d

-- Both `sampleExpBits` simulator families are PPT for `ddhOTProbFamily`.
example (F : PrimeOrderGroupFamily) :
    F.ddhOTSenderSimProb.IsPPT F.ddhOTEncoding ∧
      F.ddhOTReceiverSimProb.IsPPT F.ddhOTEncoding :=
  ⟨F.isPPT_ddhOTSenderSimProb, F.isPPT_ddhOTReceiverSimProb⟩

-- Introducing the predicate: a sender simulator family for `ddhOTProbFamily` with the same output
-- laws as `ddhOTSenderSimProb` is PPT, through the latter's machine certificate.
example (F : PrimeOrderGroupFamily) (S : SimulatorFamily F.ddhOTProbFamily {0})
    (hS : ∀ n d xI yI,
      ProbComp.eval (S n d xI yI) = ProbComp.eval (F.ddhOTSenderSimProb n d xI yI)) :
    S.IsPPT F.ddhOTEncoding :=
  IsPPTOn.congr F.isPPT_ddhOTSenderSimProb fun x => by
    simp only [ProbComp.eval_map, hS]

-- Consuming the predicate: the receiver simulator family that
-- `DDH.ddhOTProbFamily_semiHonestSecure` provides at `{1}` writes view words of polynomially
-- bounded length.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ (S : SimulatorFamily F.ddhOTProbFamily {1}) (c d : ℕ),
      ∀ (x : SimInput F.ddhOTProbFamily {1}) v,
        v ∈ (ProbComp.eval (S x.secParam x.desc x.inputs x.outputs)).support →
        (F.ddhOTEncoding.view.encCoalition x.secParam x.desc {1} v).length ≤
          c * ((encSimInput F.ddhOTEncoding x).length + 1) ^ d := by
  obtain ⟨S, hS, -⟩ := hDDH.ddhOTProbFamily_semiHonestSecure {1}
  obtain ⟨c, d, h⟩ := IsPPTOn.length_le hS
  exact ⟨S, c, d, fun x v hv => h x _ (by
    simpa only [ProbComp.eval_map, PMF.support_map] using Set.mem_image_of_mem _ hv)⟩

-- Against a corrupted receiver, the ideal games with `ddhOTReceiverSimOf` and
-- `ddhOTReceiverSimProb` differ by at most `5 / 2 ^ n`, for every environment.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage
        (F.ddhOTProbFamily.idealGame setup {1}
          (fun n d => ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
            (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) Z n)
        (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimProb Z n) ≤ 5 / 2 ^ n :=
  ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTReceiverSimProb_le n) Z

-- Concrete bounds for `ddhOTProbFamily` against unbounded environments at `{0}` and `{1}`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (Z₀ : Environment F.ddhOTProbFamily {0}) (Z₁ : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {0} Z₀ n)
        (F.ddhOTProbFamily.idealGame setup {0} F.ddhOTSenderSimProb Z₀ n) ≤ 2 / 2 ^ n ∧
      Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z₁ n)
          (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimProb Z₁ n) ≤
        Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z₁) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z₁) n) + 14 / 2 ^ n :=
  ⟨F.advantage_ddhOTProbSenderGame_le setup Z₀ n, F.advantage_ddhOTProbReceiverGame_le setup Z₁ n⟩

-- Unconditional semi-honest sender security of `ddhOTProbFamily` (no DDH assumption needed).
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) :
    ∃ S : SimulatorFamily F.ddhOTProbFamily {0}, S.IsPPT F.ddhOTEncoding ∧
      Game.Indistinguishable (F.ddhOTProbFamily.realGame setup {0})
        (F.ddhOTProbFamily.idealGame setup {0} S) (Environment.IsPPT F.ddhOTEncoding) :=
  F.ddhOTProbFamily_semiHonestSecure_sender setup

-- Under DDH, `ddhOTProbFamily` satisfies stand-alone `SemiHonestSecure` for all four static
-- coalitions: `∅`, `{0}`, `{1}` and `Finset.univ`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    F.ddhOTProbFamily.SemiHonestSecure setup ∅ F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup {0} F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup {1} F.ddhOTEncoding ∧
      F.ddhOTProbFamily.SemiHonestSecure setup Finset.univ F.ddhOTEncoding :=
  ⟨hDDH.ddhOTProbFamily_semiHonestSecure ∅, hDDH.ddhOTProbFamily_semiHonestSecure {0},
    hDDH.ddhOTProbFamily_semiHonestSecure {1}, hDDH.ddhOTProbFamily_semiHonestSecure Finset.univ⟩

end CslibFrontierTests.Crypto.DDHOTSimulators
