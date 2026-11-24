/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainChallenge
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.DrawnTransfer
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Games
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.LabelLength

/-!
# Tests for the token length of a garbling scheme (`Garbling.Scheme.HasTokenLength`)

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.LabelLength` under module
encapsulation.

* The hypotheses on the garbling scheme hold together. Point-and-permute garbling over any keyed
  family has the encoding `projectiveEncode`, is correct (`Scheme.Correct`) and has tokens of
  `k + 2` bits at every parameter `k` for every circuit (`Scheme.HasTokenLength`): a positive
  length, for a scheme of the library and not a degenerate one.
* The definition fixes the width: on the AND gate the same scheme does not have tokens of `k + 3`
  bits.
* `Yao.length_transferQueries_garbler` at this scheme is the length hypothesis on the words of the
  transfer, in the shape in which the plain-model statements ask for it: for a sequence of public
  parameters, indexed inputs and all coins in the support of the protocol's coin sampling, with the
  length `n + 2` at the parameter `n`.
* The conclusion is about a transfer that happens: on the AND gate whose second input the evaluator
  holds, there are coins in the support, and both words of the one transfer have `n + 2` bits.
* `Yao.forallChallenge_protocol_evaluator` consumes it.
* The hypotheses of `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul` hold
  together: the theorem is applied over point-and-permute garbling with keys and tokens of `n + 2`
  bits and `Nat.clog 2 (c n).evaluatorLen` index coins, and every hypothesis that is a proposition
  is proved. The bound has one key-derivation and one DDH distinguisher and the factor
  `2 ^ Nat.clog 2 (c n).evaluatorLen`, which is `1` with no transfer and below twice the number of
  transfers otherwise. The group family, the setup program, the public parameters, the side
  information, the garbling simulator, the environment and the simulators at the coalitions other
  than `{1}` are arbitrary.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoLabelLength

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC

/-- Point-and-permute garbling has tokens of `k + 2` bits at every parameter `k`, for every
circuit and all coins: its encoding information lists `2 n` labels of `k + 2` bits
(`PointPermute.length_encInfoWord`). -/
theorem hasTokenLength_pointPermute (family : List Bool → List Bool → List Bool) (k : ℕ)
    (f : ValidCircuit) : (PointPermute.scheme family).HasTokenLength k f (k + 2) := by
  intro g hg
  obtain ⟨coins, -, rfl⟩ := (PointPermute.scheme family).mem_support_eval_garble_iff.mp hg
  exact PointPermute.length_encInfoWord k f.val coins

/-- **The hypotheses on the garbling scheme are jointly satisfiable.** Point-and-permute garbling
has the projective encoding, is correct and has tokens of the positive length `k + 2`. -/
example (family : List Bool → List Bool → List Bool) :
    (PointPermute.scheme family).encode = projectiveEncode ∧
      (PointPermute.scheme family).Correct ∧
      ∀ (k : ℕ) (f : ValidCircuit), (PointPermute.scheme family).HasTokenLength k f (k + 2) :=
  ⟨rfl, (PointPermute.scheme_isValid family).correct, hasTokenLength_pointPermute family⟩

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ValidCircuit := ⟨⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩, by decide⟩

/-- **The definition fixes the width.** On the AND gate, point-and-permute garbling does not have
tokens of `k + 3` bits: the garbling from the all-`false` coins has `2 * 2 * (k + 2)` bits of
encoding information. -/
example (family : List Bool → List Bool → List Bool) (k : ℕ) :
    ¬ (PointPermute.scheme family).HasTokenLength k andGate (k + 3) := by
  intro h
  have h₁ : (PointPermute.encInfoWord k andGate.val
      (List.replicate ((PointPermute.scheme family).coins k andGate) false)).length =
        2 * 2 * (k + 3) :=
    h _ ((PointPermute.scheme family).mem_support_eval_garble_iff.mpr
      ⟨_, List.length_replicate, rfl⟩)
  have h₂ : (PointPermute.encInfoWord k andGate.val
      (List.replicate ((PointPermute.scheme family).coins k andGate) false)).length =
        2 * 2 * (k + 2) :=
    PointPermute.length_encInfoWord k andGate.val _
  omega

/-- **The length hypothesis of the plain-model statements**, in their shape: for a sequence `c` of
public parameters and inputs indexed by `d`, both words that the garbler offers in every transfer
have `n + 2` bits, for all coins in the support of the protocol's coin sampling. -/
example (family : List Bool → List Bool → List Bool) {D : Type}
    (c : ℕ → Yao.Params (PointPermute.scheme family))
    (x : (n : ℕ) → D → (i : Fin 2) → Yao.Input (c n) i) (n : ℕ) :
    ∀ d, ∀ r ∈ (ProbComp.eval (OracleComp.pi
        (Yao.protocol (PointPermute.scheme family) n (c n)).sampleCoins)).support,
      ∀ (t : Fin (c n).evaluatorLen) (b : Bool),
        (Yao.transferQueries n (c n) (x n d) r 0 t b).length = n + 2 :=
  fun d => Yao.length_transferQueries_garbler (hasTokenLength_pointPermute family n (c n).fn)
    (x n d)

/-- The public parameters: the AND gate, with the garbler holding its first input. -/
def andParams (family : List Bool → List Bool → List Bool) :
    Yao.Params (PointPermute.scheme family) := ⟨andGate, 1, (by decide : 1 ≤ 2)⟩

/-- The evaluator holds one input bit of the AND gate, so the batch has a transfer. -/
example (family : List Bool → List Bool → List Bool) : (andParams family).evaluatorLen = 1 := rfl

/-- **The conclusion is about a transfer that happens.** On the AND gate there are coins in the
support of the protocol's coin sampling, and for them both words of the evaluator's one transfer
have `n + 2` bits. -/
example (family : List Bool → List Bool → List Bool) (n : ℕ)
    (x : (i : Fin 2) → Yao.Input (andParams family) i) :
    ∃ r ∈ (ProbComp.eval (OracleComp.pi
        (Yao.protocol (PointPermute.scheme family) n (andParams family)).sampleCoins)).support,
      ∀ (t : Fin (andParams family).evaluatorLen) (b : Bool),
        (Yao.transferQueries n (andParams family) x r 0 t b).length = n + 2 := by
  obtain ⟨r, hr⟩ := (ProbComp.eval (OracleComp.pi
    (Yao.protocol (PointPermute.scheme family) n (andParams family)).sampleCoins)).support_nonempty
  exact ⟨r, hr, Yao.length_transferQueries_garbler
    (hasTokenLength_pointPermute family n (andParams family).fn) x r hr⟩

/-- **The oracle round for a corrupted evaluator.** `Yao.forallChallenge_protocol_evaluator`
consumes the length: over point-and-permute garbling, every oracle round of `Yao.protocol` has the
corrupted slots `{1}` and a sender's query whose words have `n + 2` bits, for all coins in the
support of the protocol's coin sampling. -/
example (family : List Bool → List Bool → List Bool) (n : ℕ)
    (c : Yao.Params (PointPermute.scheme family)) (x : (i : Fin 2) → Yao.Input c i)
    (r : (i : Fin 2) → Yao.Coins i)
    (hr : r ∈ (ProbComp.eval (OracleComp.pi
      (Yao.protocol (PointPermute.scheme family) n c).sampleCoins)).support) :
    Composition.ForallChallenge ({1} : Finset (Fin 2))
      (fun _ J q => J = ({1} : Finset (Fin 2)) ∧
        ∀ (t : Fin c.evaluatorLen) (b : Bool), (q 0 t b).length = n + 2)
      (Yao.protocol (PointPermute.scheme family) n c).steps (fun i => (x i, r i)) :=
  Yao.forallChallenge_protocol_evaluator n c (n + 2) x r
    (Yao.length_transferQueries_garbler (hasTokenLength_pointPermute family n c.fn) x r hr)

/-! ### The plain-model bound for a corrupted evaluator, with its hypotheses proved -/

/-- A key derivation with keys of `L` bits: every key is the all-`false` word. -/
def constKey (F : PrimeOrderGroupFamily) (L : ℕ) : F.Desc × List Bool → List Bool :=
  fun _ => List.replicate L false

/-- Simulators of Yao's protocol over point-and-permute garbling: the given family `T₁`, with
`Yao.evaluatorSim` at the coalition `{1}`. -/
noncomputable def yaoSims {Λ : Type} (family : List Bool → List Bool → List Bool)
    (c : ℕ → Yao.Params (PointPermute.scheme family)) (Φ : SideInfo ValidCircuit Λ)
    (S : ℕ → PrvSimulator Λ)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) → CoalitionSimulator (Yao.schedule (c n))
      (Yao.Input (c n)) Yao.Coins (fun _ => List Bool) I)
    (n : ℕ) : (I : Finset (Fin 2)) → CoalitionSimulator (Yao.schedule (c n))
      (Yao.Input (c n)) Yao.Coins (fun _ => List Bool) I :=
  Function.update (T₁ n) {1} (Yao.evaluatorSim (PointPermute.scheme family) Φ S n (c n))

/-- Simulators of the masked transfer: the given family `Sm`, with `maskedOTReceiverSim` for the
key-derivation mask, the fair-coin pads and a uniform word of `n + 2` bits at the coalition
`{1}`. -/
noncomputable def maskedSims (F : PrimeOrderGroupFamily) (H : F.Desc × List Bool → List Bool)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (n : ℕ) (d : F.Desc) : (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J :=
  Function.update (Sm n d) {1}
    (maskedOTReceiverSim (F.kdfMask H d) (F.kdfPadsProb n d) (BitString.sampleList (n + 2)))

/-- Simulators of the DDH transfer: the given family `S₂`, with `F.ddhOTReceiverSimProb` at the
coalition `{1}`. -/
noncomputable def ddhSims (F : PrimeOrderGroupFamily)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (n : ℕ) (d : F.Desc) : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J :=
  Function.update (S₂ n d) {1} (F.ddhOTReceiverSimProb n d)

/-- The number of fair coins that index the transfers at the parameter `n`: the least `L` with
`(c n).evaluatorLen ≤ 2 ^ L`. -/
abbrev clogLen {G : Scheme ValidCircuit} (c : ℕ → Yao.Params G) (n : ℕ) : ℕ :=
  Nat.clog 2 (c n).evaluatorLen

/-- With no transfer there is no index coin and the factor of the drawn-transfer bound is `1`. -/
example : 2 ^ Nat.clog 2 0 = 1 := by simp

/-- With `k ≥ 1` transfers the factor `2 ^ Nat.clog 2 k` of the drawn-transfer bound is below
`2 * k`. -/
example (k : ℕ) (hk : 0 < k) : 2 ^ Nat.clog 2 k < 2 * k := by
  rcases Nat.lt_or_ge 1 k with h | h
  · have hlt := Nat.pow_pred_clog_lt_self 2 h
    have hpos : 0 < Nat.clog 2 k := Nat.clog_pos one_lt_two h
    obtain ⟨L, hL⟩ : ∃ L, Nat.clog 2 k = L + 1 := ⟨Nat.clog 2 k - 1, by omega⟩
    rw [hL, Nat.pred_succ] at hlt
    rw [hL, pow_succ]
    omega
  · obtain rfl : k = 1 := by omega
    simp

/-- **The hypotheses of `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul` hold
together.** The theorem is applied at a parameter `n ≥ 1` over point-and-permute garbling, with
the key derivation `constKey F (n + 2)`, the length `n + 2` and `Nat.clog 2 (c n).evaluatorLen`
index coins. Every hypothesis that is a proposition is proved here: the encoding is projective,
the scheme is correct, the simulators at the coalition `{1}` are the required ones (`yaoSims`,
`maskedSims`, `ddhSims`), every key has `n + 2` bits, the scheme has tokens of `n + 2` bits
(`hasTokenLength_pointPermute`), and `(c n).evaluatorLen ≤ 2 ^ L n` is `Nat.le_pow_clog`, which
also covers a circuit with no evaluator input. The right-hand side has one key-derivation and one
DDH distinguisher, built from `Yao.kdfDDHDrawnTransferEnv`, and no sum over the transfers.

The group family `F`, the setup program, the public parameters `c`, the side information `Φ`, the
garbling simulator `S`, the environment `Z` and the simulators `T₁`, `Sm`, `S₂` at the other
coalitions are arbitrary; none is constructed here. -/
example {Λ : Type} (family : List Bool → List Bool → List Bool) (F : PrimeOrderGroupFamily)
    (setup : ℕ → ProbComp F.Desc) (c : ℕ → Yao.Params (PointPermute.scheme family))
    (Φ : SideInfo ValidCircuit Λ) (S : ℕ → PrvSimulator Λ)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) → CoalitionSimulator (Yao.schedule (c n))
      (Yao.Input (c n)) Yao.Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    {n : ℕ} (hn : 0 < n)
    (Z : Environment (Yao.kdfDDHProbFamily (PointPermute.scheme family) F (constKey F (n + 2)) c)
      {1}) :
    Game.advantage
        ((Yao.kdfDDHProbFamily (PointPermute.scheme family) F (constKey F (n + 2)) c).idealGame
          (fun n => ProbComp.eval (setup n)) {1}
          (Yao.kdfDDHProbSim F (constKey F (n + 2)) c (yaoSims family c Φ S T₁)
            (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) {1}) Z n)
        ((Yao.kdfDDHProbFamily (PointPermute.scheme family) F (constKey F (n + 2)) c).realGame
          (fun n => ProbComp.eval (setup n)) {1} Z n) ≤
      prvSimAdvantage (PointPermute.scheme family) Φ n (S n)
          (Yao.kdfDDHProbEnvToPrvSim F setup (constKey F (n + 2)) c
            (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z n) +
        2 ^ Nat.clog 2 (c n).evaluatorLen *
          (Game.advantage
              (F.kdfIdealGame (fun n => ProbComp.eval (setup n)) (fun n => n + 2)
                (F.roundEnvToKDFDistinguisher (constKey F (n + 2))
                  (F.padHidingEnv (constKey F (n + 2)) F.kdfPadsProb (ddhSims F S₂)
                    (Yao.kdfDDHDrawnTransferEnv F (constKey F (n + 2)) c
                      (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z (clogLen c)))) n)
              (F.kdfRealGame (fun n => ProbComp.eval (setup n)) (constKey F (n + 2))
                (F.roundEnvToKDFDistinguisher (constKey F (n + 2))
                  (F.padHidingEnv (constKey F (n + 2)) F.kdfPadsProb (ddhSims F S₂)
                    (Yao.kdfDDHDrawnTransferEnv F (constKey F (n + 2)) c
                      (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z (clogLen c)))) n) +
            (Game.advantage
                (F.ddhRealGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv (constKey F (n + 2)) F.kdfPadsProb (ddhSims F S₂)
                      (Yao.kdfDDHDrawnTransferEnv F (constKey F (n + 2)) c
                        (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z (clogLen c)))) n)
                (F.ddhRandomGame (fun n => ProbComp.eval (setup n))
                  (F.roundEnvToDDHDistinguisher
                    (F.padTransferEnv (constKey F (n + 2)) F.kdfPadsProb (ddhSims F S₂)
                      (Yao.kdfDDHDrawnTransferEnv F (constKey F (n + 2)) c
                        (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z (clogLen c)))) n) +
              18 / 2 ^ n)) :=
  Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul rfl
    (PointPermute.scheme_isValid family).correct F setup (constKey F (n + 2)) (fun n => n + 2) c
    Φ S (yaoSims family c Φ S T₁) (maskedSims F (constKey F (n + 2)) Sm) (ddhSims F S₂) Z
    (clogLen c) hn (Function.update_self ..) (fun _ => Function.update_self ..)
    (fun _ => Function.update_self ..) (fun _ _ => List.length_replicate)
    (hasTokenLength_pointPermute family n (c n).fn) (Nat.le_pow_clog one_lt_two _)

end CslibFrontierTests.Crypto.YaoLabelLength
