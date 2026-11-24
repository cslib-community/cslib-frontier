/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.Cost
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDH
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# Yao's protocol over the batched masked transfer over the DDH transfer: a concrete bound

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It names the plain-model protocol that
`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainComposition.lean` left open, and bounds the advantage
of one distinguisher of a corrupted evaluator by advantages of explicit reductions.

* `ddhMaskedOT g q mask unmask samplePads` is the single transfer of values in `M` without
  oracles: `maskedOT` with its pad transfer run by the three-message DDH transfer
  `ddhOTProtocol g q`.
* `ddhMaskedBatchOT k g q mask unmask samplePads` is the batched transfer of `k` values:
  `seqBatchOT` with every transfer run by `ddhMaskedOT`. For words it is a transfer subprotocol of
  `Yao.composedProtocol`.

## What is proved

One statement, concrete and per instance (a fixed parameter, input tuple, group and
distinguisher). For a corrupted evaluator, the semi-honest advantage of `D` against Yao's protocol
over `ddhMaskedBatchOT` is at most the `prv.sim` advantage of the explicit reduction
`Yao.evaluatorDistinguisherToPrvSim`, plus the expectation over the parties' coins of
`Composition.replacementCost` of the per-transfer cost `ddhMaskedOTReceiverCost` along the
`c.evaluatorLen` sequential transfers
(`Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le`). The cost of one
transfer is the pad-hiding advantage of that transfer's distinguisher against `maskedOT` with the
ideal pad transfer, plus the expectation over the sender's pads of the fixed-group DDH advantage of
`maskedOTToDDHDistinguisher`. So the bound has one garbling term and, for each of the
`c.evaluatorLen` transfers, one pad-hiding term and one expected DDH term, each the advantage of an
explicit program built from `D`, with no hypothesis on any of them.

The sum over the transfers is not a sum of advantages at fixed inputs: the distinguisher of a
transfer depends on the real executions of the earlier transfers, and `Composition.replacementCost`
takes the expectation over them.

## What is not proved

* The pad-hiding terms are advantages against `maskedOT` in the hybrid model, for an arbitrary
  mask. For the mask that xors a derived key they are key-derivation advantages at fixed group
  parameters (`CslibFrontier/Crypto/Protocols/MPC/MaskedOT/KDF.lean`), but that identification is
  for families of distinguishers indexed by the group parameters and is not substituted into this
  bound, whose distinguishers live at one group.
* No efficiency certificate for any reduction, and no asymptotic statement
  (`ProtocolFamily.SemiHonestSecure`). The reductions of a transfer depend on the garbler's coins,
  on the outcomes of the earlier transfers and on the sender's pads, which an asymptotic reduction
  has to sample itself or fix as advice.
* A corrupted garbler is not treated here.
* The DDH transfer is the fixed-group protocol `ddhOTProtocol` with exponents as coins, not the
  bit-string protocol `ddhOTProbProtocol` over a group family.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; locator not re-verified against primary PDF.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ddhMaskedOT`, `Cslib.Crypto.Protocols.MPC.ddhMaskedBatchOT`: the
  single and the batched transfer without oracles, with their composed simulators
  `Cslib.Crypto.Protocols.MPC.ddhMaskedOTSim` and `Cslib.Crypto.Protocols.MPC.ddhMaskedBatchOTSim`.
* `Cslib.Crypto.Protocols.MPC.ddhMaskedOTReceiverCost`: the bound on the advantage against one
  transfer for a corrupted receiver.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le`:
  the bound for a corrupted evaluator.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

variable {G M : Type} [AddCommGroup G] [DecidableEq G]

/-! ### The transfers without oracles -/

/-- **The masked transfer over the DDH transfer**: `maskedOT mask unmask samplePads` with its one
transfer of a pad in `G` run by the three-message DDH transfer `ddhOTProtocol g q`. It is a
protocol for the single transfer `otFunctionality M` without oracles. -/
noncomputable abbrev ddhMaskedOT (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (mask unmask : G → M → M) (samplePads : ProbComp (G × G)) :
    Protocol 2 noOracleSpec
      (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M)) (OTIn M)
      (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
      (OTOut M) :=
  (maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol g q

/-- The simulators of `ddhMaskedOT`, composed from simulators `S₁` of `maskedOT` and `S₂` of the
DDH transfer. -/
noncomputable abbrev ddhMaskedOTSim {q : ℕ} (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (J : Finset (Fin 2)) :
    CoalitionSimulator (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M))
      (OTIn M)
      (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
      (OTOut M) J :=
  composeSim (maskedOT mask unmask samplePads) S₁ (fun _ => S₂) J

/-- **The batched masked transfer over the DDH transfer**: `seqBatchOT k M` with each of its `k`
single transfers run by `ddhMaskedOT g q mask unmask samplePads`. It is a protocol for the batched
transfer `batchOTFunctionality k M` without oracles. -/
noncomputable abbrev ddhMaskedBatchOT (k : ℕ) (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (mask unmask : G → M → M) (samplePads : ProbComp (G × G)) :=
  (seqBatchOT k M).compose fun _ => ddhMaskedOT g q mask unmask samplePads

/-- The simulators of `ddhMaskedBatchOT`, composed from `seqBatchOTSim` and `ddhMaskedOTSim`. -/
noncomputable abbrev ddhMaskedBatchOTSim {q : ℕ} (k : ℕ) (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (J : Finset (Fin 2)) :=
  composeSim (seqBatchOT k M) (seqBatchOTSim k M)
    (fun _ => ddhMaskedOTSim mask unmask samplePads S₁ S₂) J

/-! ### The cost of one transfer for a corrupted receiver -/

/-- **The bound on the advantage against one masked transfer over the DDH transfer, for a
corrupted receiver.** For a test `D` of the views of a coalition `J` equal to `{1}` on the inputs
`x`: the advantage of `composeDistinguisher` against `maskedOT` with the ideal pad transfer and the
simulator `S₁ {1}`, plus the expectation, over the coins `c` of `maskedOT` (the sender's pads), of
the fixed-group DDH advantage of `maskedOTToDDHDistinguisher`. For every other coalition it is `⊤`:
the bound is stated for a corrupted receiver only. It has the argument order of a per-round cost of
`Composition.replacementCost` for the single-transfer oracle `otSpec M`. -/
@[expose] noncomputable def ddhMaskedOTReceiverCost (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (mask unmask : G → M → M) (samplePads : ProbComp (G × G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (_ : Unit) (J : Finset (Fin 2)) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : J) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) : ℝ≥0∞ :=
  if h : J = {1} then
    semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G) (otFunctionality M) {1}
        (S₁ {1}) x
        (composeDistinguisher (maskedOT mask unmask samplePads) (fun _ => S₂) {1} x
          fun r => D (fun s => r.1 ⟨s.1, h.symm ▸ s.2⟩, r.2)) +
      ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
        (ddhAdvantage q g (maskedOTToDDHDistinguisher g q mask unmask S₂ x c
          fun r => D (fun s => r.1 ⟨s.1, h.symm ▸ s.2⟩, r.2)) : ℝ≥0∞)
  else ⊤

/-- The advantage against `ddhMaskedOT` is at most `ddhMaskedOTReceiverCost`, for every
coalition. -/
private theorem semiHonestAdvantage_ddhMaskedOT_le_receiverCost (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y) (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (hS₂ : S₂ {1} = ddhOTReceiverSim g q) (J : Finset (Fin 2)) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : J) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => ddhOTSchedule G) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (semiHonestAdvantage (ddhMaskedOT g q mask unmask samplePads) noOracleWorld
        (otFunctionality M) J (ddhMaskedOTSim mask unmask samplePads S₁ S₂ J) x D : ℝ≥0∞) ≤
      ddhMaskedOTReceiverCost g q mask unmask samplePads S₁ S₂ () J x D := by
  unfold ddhMaskedOTReceiverCost
  split_ifs with h
  · subst h
    exact semiHonestAdvantage_maskedOT_ddhOT_receiver_le g q hgen mask unmask samplePads S₁ S₂
      hS₂ x D
  · exact le_top

namespace Yao

open Cslib.Crypto.Garbling

variable {Fn Λ : Type} {Gs : Scheme Fn}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed instance and group, with no security parameter and no
efficiency certificate for any reduction. The `prv.sim` advantage, the pad-hiding advantages and
the DDH advantages are left as explicit terms, and nothing is assumed about them.

At every parameter `n ≥ 1`, when the garbling scheme `Gs` is correct with a projective encoding and
`g` generates `G`, the semi-honest advantage of `D` against Yao's protocol over the batched masked
transfer over the DDH transfer, `Yao.composedProtocol Gs n c (ddhMaskedBatchOT …)`, for the
coalition `{1}`, with the simulator composed from `Yao.evaluatorSim Gs Φ S`, any simulators `S₁` of
`maskedOT` and simulators `S₂` of the DDH transfer whose member at `{1}` is `ddhOTReceiverSim g q`,
is at most

* the `prv.sim` advantage against the garbling simulator `S n` of the explicit reduction
  `Yao.evaluatorDistinguisherToPrvSim` applied to `composeDistinguisher`, plus
* the expectation, over the parties' coins `r`, of `Composition.replacementCost` of the
  per-transfer cost `ddhMaskedOTReceiverCost` along the `c.evaluatorLen` sequential transfers on
  the queries `Yao.transferQueries n c x r`, for the test `Yao.transferDistinguisher`: the sum over
  the transfers of the expected pad-hiding advantage against `maskedOT` with `S₁ {1}` plus the
  expected fixed-group DDH advantage of `maskedOTToDDHDistinguisher`, the expectation being over
  the real executions of the earlier transfers and over the sender's pads. -/
theorem semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params Gs) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    (mask unmask : G → List Bool → List Bool) (samplePads : ProbComp (G × G))
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {1} = evaluatorSim Gs Φ S n c)
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G (List Bool)) (OTIn (List Bool)) (MaskedOTCoins G)
        (OTOut (List Bool)) J)
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) J)
    (hS₂ : S₂ {1} = ddhOTReceiverSim g q) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) →
      PartyView (Input c)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoins q) (MaskedOTCoins G)
              (maskedOTSchedule G (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          Coins (schedule c))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule G)
              (maskedOTSchedule G (List Bool)))
            (seqBatchOTSchedule c.evaluatorLen (List Bool)))
          (schedule c)) i) × ((i : Fin 2) → List Bool) → ProbComp Bool) :
    (semiHonestAdvantage
        (composedProtocol Gs n c (ddhMaskedBatchOT c.evaluatorLen g q mask unmask samplePads))
        noOracleWorld (functionality Gs c) {1}
        (composeSim (protocol Gs n c) T₁
          (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) {1})
        x D : ℝ≥0∞) ≤
      prvSimAdvantage Gs Φ n (S n) (evaluatorDistinguisherToPrvSim c x
          (composeDistinguisher (protocol Gs n c)
            (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) {1} x D)) +
        ∑' r, ProbComp.eval (OracleComp.pi (protocol Gs n c).sampleCoins) r *
          replacementCost (ddhMaskedOTReceiverCost g q mask unmask samplePads S₁ S₂)
            (otWorld (List Bool)) noOracleWorld
            (fun _ => ddhMaskedOT g q mask unmask samplePads)
            (fun _ => ddhMaskedOTSim mask unmask samplePads S₁ S₂)
            (subCoalition (Function.Embedding.refl (Fin 2)) {1})
            (seqBatchOT c.evaluatorLen (List Bool)).steps
            (fun i => (transferQueries n c x r i, ()))
            (fun res => transferDistinguisher n c
              (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) {1} x r D
              (fun i => ⟨transferQueries n c x r i.1, ((), (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  refine (semiHonestAdvantage_composedProtocol_evaluator_le_transfer hproj hcorrect hn c Φ S
    (ddhMaskedBatchOT c.evaluatorLen g q mask unmask samplePads) noOracleWorld T₁ hT₁
    (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) x D).trans
    (add_le_add le_rfl (tsum_le_tsum fun r => mul_le_mul' le_rfl ?_))
  have hA := semiHonestAdvantage_seqBatchOT_compose_le c.evaluatorLen (List Bool) noOracleWorld
    (ddhMaskedOT g q mask unmask samplePads) (ddhMaskedOTSim mask unmask samplePads S₁ S₂)
    (subCoalition (Function.Embedding.refl (Fin 2)) {1}) (transferQueries n c x r)
    (transferDistinguisher n c
      (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) {1} x r D)
  -- The worlds, subprotocol, simulators and cost are given by name: left to unification, the
  -- hypothesis below is elaborated before they are known and the search does not terminate.
  exact hA.trans (replacementBound_le_replacementCost
    (W₁ := otWorld (List Bool)) (W₂ := noOracleWorld)
    (Sub := fun _ => ddhMaskedOT g q mask unmask samplePads)
    (S₂ := fun _ => ddhMaskedOTSim mask unmask samplePads S₁ S₂)
    (cost := ddhMaskedOTReceiverCost g q mask unmask samplePads S₁ S₂)
    (fun _ J q' D' => semiHonestAdvantage_ddhMaskedOT_le_receiverCost g q hgen mask unmask
      samplePads S₁ S₂ hS₂ J q' D') _ _ _ _)

end Yao

end Cslib.Crypto.Protocols.MPC
