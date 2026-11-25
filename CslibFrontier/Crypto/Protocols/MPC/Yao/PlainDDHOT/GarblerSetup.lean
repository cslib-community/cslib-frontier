/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT.SequentialProg
public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainChallenge
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.Mixture

/-!
# Yao's protocol over masked fair-coin DDH transfers under a sampled setup: the corrupted garbler

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045), not that theorem. It treats a corrupted garbler of the plain-model
protocol

* Yao's protocol `Yao.protocol Gs n (c n)`, with its batched transfer run by `seqBatchOT`,
* every single transfer run by `maskedOT` with masks and a pad sampler that may depend on the
  group description,
* the pad transfer run by the fair-coin DDH transfer `F.ddhOTProbProtocol n d`,

with the group description `d` drawn by a setup program `setup n`. The garbler is the sender of
every transfer. Its simulator for Yao's protocol and its simulator for `maskedOT` are exact, and
its simulator `F.ddhOTSenderSimProb n d` for the fair-coin DDH transfer is within `2 / 2 ^ n` of the
real execution, because the exponents are reduced fair-coin bit strings. So the bound is
statistical: `2 / 2 ^ n` for each of the `(c n).evaluatorLen` transfers, with no hardness
assumption.

The masks need only be inverted by unmasking on words of one length `L`, the length of the words
offered in the transfers, so that the statement applies to masks such as a key-derivation mask
that is its own inverse only on words of the key's length. That both words offered in every
transfer (`Yao.transferQueries`) have length `L` is the hypothesis `hlen`;
`Yao.length_transferQueries_garbler` in
`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/LabelLength.lean` derives it from
`Scheme.HasTokenLength`.

## What is not proved

* **No asymptotic statement and no efficiency certificate.** The bound is stated at each
  parameter; `ProtocolFamily.SemiHonestSecure` is not stated for the composed protocol, the
  composed simulator is not shown to be uniform strict PPT, and nothing bounds
  `(c n).evaluatorLen` (#6045).
* Only the corrupted garbler is treated here; the corrupted evaluator is in
  `CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/DrawnTransfer.lean`.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; they were not re-verified against the source.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.advantage_setup_composedProtocol_maskedOT_ddhOTProb_garbler_le`:
  the advantage against the composed protocol for a corrupted garbler, after the setup, is at most
  `(c n).evaluatorLen * (2 / 2 ^ n)`.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Garbling
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

variable {Fn : Type} {Gs : Scheme Fn}

/-- With the ideal pad transfer, `maskedOTSenderSim` is exact for the sender slot, when unmasking
recovers the receiver's output under every pad. -/
private theorem eval_idealJoint_maskedOT_of_eq_sender {G M : Type} (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G))
    (Sm : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (hSm : Sm {0} = maskedOTSenderSim samplePads) {J : Finset (Fin 2)} (hJ : J = {0})
    (q : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs q 1)) = otOutputs q 1) :
    ProbComp.eval (idealJoint (otFunctionality M) J (Sm J) q) =
      (maskedOT mask unmask samplePads).realJoint (otWorld G) J q := by
  subst hJ
  exact hSm ▸ idealJoint_maskedOT_sender mask unmask samplePads q hmask

/-- The sender's simulator of the fair-coin DDH transfer at a fixed group description, inputs and
test: `advantage_ddhOTProbSenderGame_le` for the environment that chooses the inputs `q` and
guesses with `g` at the description `d`. -/
private theorem advantage_idealJoint_ddhOTSenderSimProb_le (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc) (q : (i : Fin 2) → OTIn (F.Carrier d) i)
    (g : ((i : ({0} : Finset (Fin 2))) → PartyView (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (ddhOTSchedule (F.Carrier d)) i) ×
      ((i : Fin 2) → OTOut (F.Carrier d) i) → ProbComp Bool) :
    Game.advantage
        ((ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) {0}
          (F.ddhOTSenderSimProb n d) q)).bind fun r => ProbComp.eval (g r))
        (((F.ddhOTProbProtocol n d).realJoint noOracleWorld {0} q).bind fun r =>
          ProbComp.eval (g r)) ≤ 2 / 2 ^ n := by
  classical
  let Z : Environment F.ddhOTProbFamily {0} :=
    { choose := fun _ d' =>
        if h : d' = d then pure ⟨h ▸ q, []⟩
        else pure ⟨fun i => Fin.cases (motive := fun i => OTIn (F.Carrier d') i)
          (F.generator d', F.generator d') (fun _ => false) i, []⟩
      guess := fun _ d' _ r => if h : d' = d then g (h ▸ r) else pure false }
  have h := F.advantage_ddhOTProbSenderGame_le (fun _ => PMF.pure d) Z n
  rw [Game.advantage_comm] at h
  simpa only [ProtocolFamily.realGame, ProtocolFamily.idealGame, PMF.monad_bind_eq_bind,
    PMF.pure_bind, show Z.choose n d = pure ⟨q, []⟩ from dite_eq_left rfl,
    show ∀ s r, Z.guess n d s r = g r from fun _ _ => dite_eq_left rfl, ProbComp.eval_pure] using h

/-- A challenged fair-coin DDH transfer that corrupts the sender slot alone: the ideal round game,
with simulators whose member at `{0}` is `F.ddhOTSenderSimProb n d`, and the real round game are
within `2 / 2 ^ n`. -/
private theorem advantage_roundGame_ddhOTProb_sender_le (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : S₂ {0} = F.ddhOTSenderSimProb n d)
    (c : RoundChallenge (spec₁ := otSpec (F.Carrier d)) (fun _ => ddhOTSchedule (F.Carrier d))
      (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)))
    (hc : c.coalition = {0}) :
    Game.advantage
        (roundGame (fun op J q =>
          ProbComp.eval (idealJoint (otWorld (F.Carrier d) op) J (S₂ J) q)) (Sum.inr c))
        (roundGame (fun _ J q => (F.ddhOTProbProtocol n d).realJoint noOracleWorld J q)
          (Sum.inr c)) ≤ 2 / 2 ^ n := by
  obtain ⟨op, J, q, g⟩ := c
  obtain rfl : J = {0} := hc
  dsimp only [roundGame, Sum.elim_inr, otWorld]
  exact hS₂.symm ▸ advantage_idealJoint_ddhOTSenderSimProb_le F n d q g

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a statistical bound at each parameter, with no asymptotic statement
(`ProtocolFamily.SemiHonestSecure` is not claimed) and no efficiency certificate for the composed
simulator.

Let the group description `d` be drawn by the setup program `setup n`, and let the inputs `x d`
and the distinguisher `D d` depend on it. At every parameter `n ≥ 1`, when the garbling scheme
`Gs` is correct with a projective encoding, unmasking inverts masking on every word of length `L`
under every pad (`hmask`; the masks need not be inverses on words of other lengths), both words
offered in every transfer have length `L` for every group description and all coins in the
support of the coin sampler (`hlen`, which `Yao.length_transferQueries_garbler` derives from
`Scheme.HasTokenLength`), and the simulators at the coalition `{0}` are
`Yao.garblerSim Gs n (c n)` for Yao's protocol,
`maskedOTSenderSim (samplePads d)` for the masked transfer and `F.ddhOTSenderSimProb n d` for the
DDH transfer, the advantage between the ideal game with the composed simulator and the real game of
Yao's protocol over `seqBatchOT` over `maskedOT` with the masks `mask d`, `unmask d` and the pads
`samplePads d` over `F.ddhOTProbProtocol n d`, in the plain model, both after `d ← setup n`, is at
most `(c n).evaluatorLen * (2 / 2 ^ n)`: `2 / 2 ^ n` for the fair-coin exponents of each transfer.

No hardness assumption is used: the garbler is the sender of every transfer, its simulators for
Yao's protocol and for `maskedOT` are exact, and its simulator for the fair-coin DDH transfer is
statistically close (`advantage_ddhOTProbSenderGame_le`). The absolute value is outside the
expectation over the setup. Nothing is assumed about the setup program, the pad sampler or the
distinguisher. -/
theorem advantage_setup_composedProtocol_maskedOT_ddhOTProb_garbler_le
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → ProbComp F.Desc)
    (mask unmask : (d : F.Desc) → F.Carrier d → List Bool → List Bool)
    (samplePads : (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d))
    (c : ℕ → Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    {n : ℕ} (hn : 0 < n)
    (x : F.Desc → (i : Fin 2) → Input (c n) i)
    (D : (d : F.Desc) → ((i : ({0} : Finset (Fin 2))) → PartyView (Input (c n))
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins
              (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          Coins (schedule (c n)))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          (schedule (c n))) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool)
    (L : ℕ)
    (hmask : ∀ d r (m : List Bool), m.length = L → unmask d r (mask d r m) = m)
    (hT₁ : T₁ n {0} = garblerSim Gs n (c n))
    (hSm : ∀ d, Sm n d {0} = maskedOTSenderSim (samplePads d))
    (hS₂ : ∀ d, S₂ n d {0} = F.ddhOTSenderSimProb n d)
    (hlen : ∀ d, ∀ r ∈ (ProbComp.eval (OracleComp.pi (protocol Gs n (c n)).sampleCoins)).support,
      ∀ (t : Fin (c n).evaluatorLen) (b : Bool),
        (transferQueries n (c n) (x d) r 0 t b).length = L) :
    Game.advantage
        ((ProbComp.eval (setup n)).bind fun d =>
          (ProbComp.eval (idealJoint (functionality Gs (c n)) {0}
            (composeSim (protocol Gs n (c n)) (T₁ n {0})
              (fun _ J => composeSim (seqBatchOT (c n).evaluatorLen (List Bool))
                (seqBatchOTSim (c n).evaluatorLen (List Bool) J)
                (fun _ J => composeSim
                  (maskedOT (mask d) (unmask d) (samplePads d)) (Sm n d J)
                  (fun _ => S₂ n d)))) (x d))).bind fun r => ProbComp.eval (D d r))
        ((ProbComp.eval (setup n)).bind fun d =>
          (((protocol Gs n (c n)).compose fun _ =>
            (seqBatchOT (c n).evaluatorLen (List Bool)).compose fun _ =>
              (maskedOT (mask d) (unmask d) (samplePads d)).compose fun _ =>
                F.ddhOTProbProtocol n d).realJoint
                  noOracleWorld {0} (x d)).bind fun r => ProbComp.eval (D d r)) ≤
      (c n).evaluatorLen * (2 / 2 ^ n) := by
  have h := advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame
    ((ProbComp.eval (setup n)).map Sum.inr) (c n).evaluatorLen (fun _ => protocol Gs n (c n))
    mask unmask samplePads (fun _ => noOracleWorld) (fun d => F.ddhOTProbProtocol n d)
    (fun d => Sm n d) (fun d => S₂ n d) (fun _ => functionality Gs (c n)) (fun _ => T₁ n)
    (fun _ => {0}) x D 1 (fun _ => le_rfl)
  simp only [PMF.bind_map, Function.comp_def, Sum.elim_inr, Finset.sum_range_one, hT₁,
    idealJoint_garblerSim hproj hcorrect hn, Game.advantage_self, zero_add] at h
  rw [hT₁]
  refine h.trans ((Finset.sum_le_sum fun j _ => ?_).trans_eq
    (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
  have hE (d c') (hc' : Sum.inr c' ∈ (composeSeqBatchOTRoundEnv (c n).evaluatorLen (List Bool)
      (protocol Gs n (c n)) noOracleWorld
      ((maskedOT (mask d) (unmask d) (samplePads d)).compose fun _ => F.ddhOTProbProtocol n d)
      (fun J => composeSim (maskedOT (mask d) (unmask d) (samplePads d)) (Sm n d J)
        (fun _ => S₂ n d)) {0} (x d) (D d) 0 j).support) :=
    coalition_length_of_mem_support_composeSeqBatchOTRoundEnv _ _ _ _ _ _ _ _ _ _ {0} L
      (fun r hr => (forallChallenge_protocol_iff n (c n) {0} _ (x d) r).mpr
        ⟨Finset.ext fun _ => mem_subCoalition, hlen d r hr⟩) hc'
  refine (add_le_add (b := 0) ?_ ?_).trans_eq (zero_add _)
  · refine Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_of_support _ _ _ ?_
    rintro (_ | c') he
    · simp
    · simp only [Sum.elim_inr, eval_idealJoint_maskedOT_of_eq_sender (mask d) (unmask d)
        (samplePads d) (Sm n d) (hSm d) (hE d c' he).1 c'.query fun r =>
          hmask d r _ (hE d c' he).2, Game.advantage_self, le_rfl]
  · refine Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_of_support _ _ _ ?_
    rintro (_ | c') he
    · simp
    · simp only [Sum.elim_inr]
      refine Game.advantage_bind_le_of_support _ _ _ ?_
      rintro (_ | c₂) he₂
      · simp [roundGame]
      · refine advantage_roundGame_ddhOTProb_sender_le F n d (S₂ n d) (hS₂ d) c₂
          (ForallChallenge.of_mem_support_composeRoundEnv (Q := fun _ J _ => J = {0})
            _ _ _ _ _ _ _ _ _ (fun _ _ => ?_) he₂)
        refine ⟨?_, fun _ => trivial⟩
        rw [(hE d c' he).1]
        exact Finset.ext fun _ => mem_subCoalition

end Cslib.Crypto.Protocols.MPC.Yao
