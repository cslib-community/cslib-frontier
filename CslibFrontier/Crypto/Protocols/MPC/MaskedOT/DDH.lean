/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT

/-!
# The masked transfer over a pad transfer, per distinguisher, and over the DDH transfer

`semiHonestAdvantage_maskedOT_compose_le_add` bounds the advantage against `maskedOT` over a
substituted pad transfer under hypotheses that range over all tests, so it applies to
statistically secure components only. This module gives the bound for one distinguisher, with
explicit reductions and no hypothesis on them, and instantiates the pad transfer with the
three-message DDH transfer `ddhOTProtocol`.

This is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem; it is original bookkeeping and no
cited statement is claimed.

## What is proved

All statements are concrete and per instance: a fixed input pair and one distinguisher `D`.

* `maskedOT` calls the pad transfer once, so the hybrid bound of
  `semiHonestAdvantage_compose_le_replacementBound` has one term: for every coalition, the
  advantage of `D` against `(maskedOT mask unmask samplePads).compose fun _ => Sub` is at most the
  advantage of `composeDistinguisher` against `maskedOT` with the ideal pad transfer, plus the
  expectation over the sender's pads of the advantage of the explicit distinguisher
  `maskedOTTransferDistinguisher` against `Sub` on the pads and the receiver's choice bit
  (`semiHonestAdvantage_maskedOT_compose_le_transfer`).
* For `Sub = ddhOTProtocol g q` and a corrupted receiver, the second term is the expectation over
  the sender's pads of the fixed-group DDH advantage `ddhAdvantage q g` of the explicit DDH
  distinguisher `maskedOTToDDHDistinguisher` (`semiHonestAdvantage_maskedOT_ddhOT_receiver_le`).
  The first term is the pad-hiding advantage of `maskedOTPadTest`
  (`semiHonestAdvantage_maskedOT_receiver_eq`); for the mask that xors a derived key it is a
  key-derivation advantage (`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/KDF.lean`).

## What is not proved

* No efficiency certificate for `maskedOTTransferDistinguisher`, `maskedOTToDDHDistinguisher` or
  `composeDistinguisher`, and no asymptotic statement (`ProtocolFamily.SemiHonestSecure`). The
  DDH term is an expectation over the sender's pads of advantages of distinguishers that depend
  on the pads, which an asymptotic reduction has to sample itself or fix as advice.
* The DDH transfer is the fixed-group protocol `ddhOTProtocol` with exponents as coins. The
  bit-string protocol `ddhOTProbProtocol` over a group family is treated in
  `CslibFrontier/Crypto/Protocols/MPC/MaskedOT/DDHProb.lean`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.maskedOTTransferDistinguisher`: the reduction from a distinguisher
  of the composed protocol to a distinguisher of the pad transfer.
* `Cslib.Crypto.Protocols.MPC.maskedOTToDDHDistinguisher`: the reduction from a distinguisher of a
  corrupted receiver of the masked transfer over the DDH transfer to a DDH distinguisher.

## Main results

* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_maskedOT_compose_le_transfer`: the bound for one
  distinguisher over any pad transfer.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_maskedOT_ddhOT_receiver_le`: the bound for a
  corrupted receiver over the DDH transfer.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

variable {G M : Type}

/-! ### One distinguisher over any pad transfer -/

section Transfer

variable {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}

/-- **The reduction to the pad transfer**, for `maskedOT mask unmask samplePads` on the inputs `x`
with the coins `c`: from a distinguisher `D` of the coalition `I`'s views of the composed protocol
and the outputs, the distinguisher of the views of the corrupted slots and the answers of the pad
transfer that finishes the protocol from the answers (the sender's message of masked values and the
outputs), puts the given views of the pad transfer into the coalition's views and runs `D`. It is
`Composition.roundDistinguisher` at the one oracle round of `maskedOT`. -/
@[expose] noncomputable def maskedOTTransferDistinguisher (mask unmask : G → M → M)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn G) Coins₂ (OTOut G) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → OTIn M i) (c : (i : Fin 2) → MaskedOTCoins G i)
    (D : ((i : I) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => Coins₂) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => sc₂) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    ((s : subCoalition (Function.Embedding.refl (Fin 2)) I) → PartyView (OTIn G) Coins₂ sc₂ s) ×
      ((s : Fin 2) → OTOut G s) → ProbComp Bool :=
  roundDistinguisher (sc₂ := fun _ => sc₂) (Coins₂ := fun _ => Coins₂) (otWorld G) (fun _ => S₂) I
    (State := fun i => OTIn M i × MaskedOTCoins G i)
    (op := ()) (parties := Function.Embedding.refl (Fin 2))
    (.message (fun ((m, r), _) => maskedOTMsg mask m r) (.done (maskedOTOutput unmask)))
    (fun i => (x i, c i))
    (fun res => D (fun i : I => ⟨x i.1, (c i.1, (res.1 i).1), (res.1 i).2⟩, res.2))

/-- **The masked transfer over a substituted pad transfer, for one distinguisher.** Step towards
[LindellPinkas2009], Theorem 7, not the cited result (#6045): a concrete bound at a fixed instance
with both advantages left as terms.

For every coalition `I`, the semi-honest advantage of `D` against
`(maskedOT mask unmask samplePads).compose fun _ => Sub` with the simulator composed from any
simulators `S₁` of `maskedOT` and `S₂` of `Sub` is at most the advantage of `composeDistinguisher`
against `maskedOT` with the ideal pad transfer and `S₁ I`, plus the expectation, over the coins `c`
of `maskedOT` (the sender's pads), of the semi-honest advantage of
`maskedOTTransferDistinguisher` against `Sub`, for the pad transfer `otFunctionality G` with the
simulator `S₂`, on the sender's pads and the receiver's choice bit. Nothing is assumed about
`mask`, `Sub`, the simulators or `D`, and no efficiency of the reductions is claimed. -/
theorem semiHonestAdvantage_maskedOT_compose_le_transfer (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (W₂ : MultiOracleWorld spec₂)
    (Sub : Protocol 2 spec₂ sc₂ (OTIn G) Coins₂ (OTOut G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn G) Coins₂ (OTOut G) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : I) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => Coins₂) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => sc₂) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (semiHonestAdvantage ((maskedOT mask unmask samplePads).compose fun _ => Sub) W₂
        (otFunctionality M) I
        (composeSim (maskedOT mask unmask samplePads) (S₁ I) (fun _ => S₂)) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G) (otFunctionality M) I
          (S₁ I) x
          (composeDistinguisher (maskedOT mask unmask samplePads) (fun _ => S₂) I x D) +
        ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
          (semiHonestAdvantage Sub W₂ (otFunctionality G)
            (subCoalition (Function.Embedding.refl (Fin 2)) I)
            (S₂ (subCoalition (Function.Embedding.refl (Fin 2)) I))
            (fun s => maskedOTQuery s (x s, c s))
            (maskedOTTransferDistinguisher mask unmask S₂ I x c D) : ℝ≥0∞) := by
  refine (semiHonestAdvantage_compose_le_replacementBound (maskedOT mask unmask samplePads)
    (otWorld G) W₂ (otFunctionality M) I (S₁ I) (fun _ => Sub) (fun _ => S₂) x D).trans
    (add_le_add le_rfl (le_of_eq (tsum_congr fun c =>
      congrArg (ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c * ·)
        ?_)))
  simp only [maskedOT, replacementBound, mul_zero, tsum_zero, add_zero]
  rfl

end Transfer

/-! ### A corrupted receiver over the DDH transfer -/

/-- The semi-honest advantage at a coalition `J` equal to `I` is the advantage at `I` of the test
that reads the views of `I` as views of `J`. -/
theorem semiHonestAdvantage_of_coalition_eq {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In Coins Out : Fin m → Type} (P : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out)
    (S : (J : Finset (Fin m)) → CoalitionSimulator sc In Coins Out J) {J I : Finset (Fin m)}
    (h : J = I) (x : (i : Fin m) → In i)
    (D : ((i : J) → PartyView In Coins sc i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage P W f J (S J) x D =
      semiHonestAdvantage P W f I (S I) x fun r => D (fun s => r.1 ⟨s.1, h ▸ s.2⟩, r.2) := by
  subst h
  rfl

variable [AddCommGroup G] [DecidableEq G]

/-- **The DDH distinguisher of a corrupted receiver of the masked transfer over the DDH
transfer**, on the inputs `x` with the coins `c` of `maskedOT` (the sender's pads): the DDH
reduction `ddhOTReduction` of the DDH transfer, on the pads and the receiver's choice bit, applied
to the pad-transfer distinguisher `maskedOTTransferDistinguisher` of `D`. -/
@[expose] noncomputable def maskedOTToDDHDistinguisher (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (mask unmask : G → M → M)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (x : (i : Fin 2) → OTIn M i) (c : (i : Fin 2) → MaskedOTCoins G i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) : G → G → G → ProbComp Bool :=
  ddhOTReduction g q (fun s => maskedOTQuery s (x s, c s)) fun r =>
    maskedOTTransferDistinguisher mask unmask S₂ {1} x c D
      (fun s => r.1 ⟨s.1, mem_subCoalition.1 s.2⟩, r.2)

/-- **The masked transfer over the DDH transfer, corrupted receiver, for one distinguisher.** Step
towards [LindellPinkas2009], Theorem 7, not the cited result (#6045): a concrete bound at a fixed
instance and group, with no security parameter and no efficiency certificate for the reductions.

When `g` generates `G`, the semi-honest advantage of `D` against
`(maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol g q` for the coalition `{1}`,
with the simulator composed from any simulators `S₁` of `maskedOT` and simulators `S₂` of the DDH
transfer whose member at `{1}` is `ddhOTReceiverSim g q`, is at most the advantage of
`composeDistinguisher` against `maskedOT` with the ideal pad transfer and `S₁ {1}`, plus the
expectation, over the coins `c` of `maskedOT` (the sender's pads), of the fixed-group DDH advantage
of `maskedOTToDDHDistinguisher`. Nothing is assumed about either term. For
`S₁ {1} = maskedOTReceiverSim mask samplePads pad` the first term is the pad-hiding advantage of
`maskedOTPadTest` (`semiHonestAdvantage_maskedOT_receiver_eq`). -/
theorem semiHonestAdvantage_maskedOT_ddhOT_receiver_le (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y) (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (hS₂ : S₂ {1} = ddhOTReceiverSim g q) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (semiHonestAdvantage ((maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol g q)
        noOracleWorld (otFunctionality M) {1}
        (composeSim (maskedOT mask unmask samplePads) (S₁ {1}) (fun _ => S₂)) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G) (otFunctionality M) {1}
          (S₁ {1}) x
          (composeDistinguisher (maskedOT mask unmask samplePads) (fun _ => S₂) {1} x D) +
        ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
          (ddhAdvantage q g (maskedOTToDDHDistinguisher g q mask unmask S₂ x c D) : ℝ≥0∞) := by
  refine (semiHonestAdvantage_maskedOT_compose_le_transfer mask unmask samplePads noOracleWorld
    (ddhOTProtocol g q) S₁ S₂ {1} x D).trans (add_le_add le_rfl (le_of_eq (tsum_congr fun c =>
      congrArg (fun a : NNReal => ProbComp.eval
        (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c * (a : ℝ≥0∞)) ?_)))
  rw [semiHonestAdvantage_of_coalition_eq (ddhOTProtocol g q) noOracleWorld (otFunctionality G) S₂
    (Finset.ext fun _ => mem_subCoalition), hS₂, semiHonestAdvantage_ddhOT_receiver_eq g q hgen]
  rfl

end Cslib.Crypto.Protocols.MPC
