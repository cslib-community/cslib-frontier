/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.Yao.Security
import CslibFrontier.Probability.PMF.Bind

/-!
# Yao's protocol over an oblivious-transfer subprotocol: first composition step

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. `Yao.oneSidedProtocol` and
`Yao.protocol` run in the ideal `batchOTWorld` oblivious-transfer hybrid model. Here the ideal
transfer round is replaced by an arbitrary two-party subprotocol `OT` for the batched transfer
(`Protocol.compose`), which gives the protocols whose security Theorem 7 states when `OT` is a
plain-model oblivious-transfer protocol:

* `Yao.composedOneSidedProtocol G n c OT`: the one-sided protocol over `OT`;
* `Yao.composedProtocol G n c OT`: the two-output protocol over `OT`.

The first property proved is for a corrupted garbler, at a fixed parameter, input tuple and
distinguisher. With the composed simulator built from the hybrid garbler simulator (`Yao.garblerSim`
or `Yao.oneSidedGarblerSim`) and any simulators `S₂` for `OT`, the semi-honest advantage against the
composed protocol is at most the oblivious-transfer replacement gap: the distance between the
hybrid execution in `batchOTWorld`, with the garbler's view of the transfer produced by `S₂`, and
the real execution over `OT` (`Yao.semiHonestAdvantage_composedProtocol_garbler_le`,
`Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le`). The hybrid garbler simulators are
exact, so the hybrid term of `semiHonestAdvantage_compose_le` vanishes.

For a corrupted evaluator, again at a fixed parameter, input tuple and distinguisher, the hybrid
term does not vanish: with the hybrid evaluator simulator built from a garbling simulator `S` for
side information `Φ` (`Yao.evaluatorSim G Φ S` or `Yao.oneSidedEvaluatorSim G Φ S`), it equals the
`prv.sim` advantage against `S n` of an explicit adversary that queries the function on the two
parties' bits and runs the distinguisher on the evaluator's view read from the garbled view
(`Yao.evaluatorDistinguisherToPrvSim`, `Yao.oneSidedEvaluatorDistinguisherToPrvSim`;
`Yao.semiHonestAdvantage_protocol_evaluator_eq`,
`Yao.semiHonestAdvantage_oneSidedProtocol_evaluator_eq`). So the advantage against the composed
protocol is at most this `prv.sim` advantage, for the reduction applied to `composeDistinguisher`,
plus the replacement gap (`Yao.semiHonestAdvantage_composedProtocol_evaluator_le`,
`Yao.semiHonestAdvantage_composedOneSidedProtocol_evaluator_le`). No hypothesis bounds either
term.

## What is not proved

These bounds are concrete and stated per instance (a fixed parameter, input tuple and
distinguisher). They leave the replacement gap and, for a corrupted evaluator, the `prv.sim`
advantage of the reduction as explicit terms. The following parts of Theorem 7 remain open (#6045):

* bounding the replacement gap by the semi-honest security of a concrete oblivious-transfer
  protocol, such as the DDH protocol of
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure`, which transfers one
  group element rather than a batch of token words. `advantage_replacement_eq_kernelRun`
  expresses the gap through the ideal and the real joint distributions of the transfer
  subprotocol, on the queries of the one transfer round, but the bound by the subprotocol's
  `semiHonestAdvantage` against an explicit distinguisher is not derived;
* the asymptotic statement `ProtocolFamily.SemiHonestSecure` for the composed family, with strict
  PPT certificates for the composed simulators and for the reductions. In particular the
  per-instance reductions `Yao.evaluatorDistinguisherToPrvSim` and
  `Yao.oneSidedEvaluatorDistinguisherToPrvSim` come with no efficiency certificate here, and no
  negligible bound on their `prv.sim` advantage is derived from an assumption on `G`; the uniform
  reduction with a PPT certificate in the hybrid model is `Yao.evaluatorToPrvSim`.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`; locator not re-verified against primary PDF.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.composedOneSidedProtocol`,
  `Cslib.Crypto.Protocols.MPC.Yao.composedProtocol`: Yao's protocols with the batched transfer run
  by a subprotocol.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedEvaluatorDistinguisherToPrvSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.evaluatorDistinguisherToPrvSim`: the reductions from a
  distinguisher of a corrupted evaluator's view at a fixed instance to a `prv.sim` adversary.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_garbler_le`: against a
  corrupted garbler, the advantage is at most the oblivious-transfer replacement gap.
* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_oneSidedProtocol_evaluator_eq`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_protocol_evaluator_eq`: against a corrupted
  evaluator of the hybrid protocols, the advantage at a fixed instance is the `prv.sim` advantage
  of the reduction.
* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedOneSidedProtocol_evaluator_le`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_evaluator_le`: against a
  corrupted evaluator, the advantage is at most the `prv.sim` advantage of the reduction plus the
  oblivious-transfer replacement gap.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling Cslib.Probability

variable {Fn Λ : Type} (G : Scheme Fn)

/-- **One-sided Yao's protocol over a transfer subprotocol**: `Yao.oneSidedProtocol G n c` with its
batched oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedOneSidedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c)) (fun _ => List Bool) :=
  (oneSidedProtocol G n c).compose fun _ => OT

/-- **Yao's protocol over a transfer subprotocol** (Protocol 2 of [LindellPinkas2009], with the
transfers run by one subprotocol for the whole batch): `Yao.protocol G n c` with its batched
oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (schedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c)) (fun _ => List Bool) :=
  (protocol G n c).compose fun _ => OT

variable {G}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete bound that leaves the oblivious-transfer replacement gap as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedOneSidedProtocol G n c OT` for the coalition `{0}`, with the
simulator composed from `Yao.oneSidedGarblerSim` and any simulators `S₂` for `OT`, is at most the
distance between the hybrid execution in `batchOTWorld` against the reduction
`composeDistinguisher`, which produces the garbler's view of the transfer with `S₂`, and the real
execution over `OT`. -/
theorem semiHonestAdvantage_composedOneSidedProtocol_garbler_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (oneSidedSchedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {0} = oneSidedGarblerSim G n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedOneSidedProtocol G n c OT) W₂ (oneSidedFunctionality G c) {0}
        (composeSim (oneSidedProtocol G n c) S₁ S₂ {0}) x D ≤
      Game.advantage
        (((oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x).bind
          fun r => ProbComp.eval (composeDistinguisher (oneSidedProtocol G n c) S₂ {0} x D r))
        (((composedOneSidedProtocol G n c OT).realJoint W₂ {0} x).bind fun r =>
          ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (oneSidedProtocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (oneSidedFunctionality G c) S₁ (fun _ => OT) S₂
    {0} x D
  have h0 : semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (oneSidedFunctionality G c) {0} (S₁ {0}) x
      (composeDistinguisher (oneSidedProtocol G n c) S₂ {0} x D) = 0 := by
    rw [hS₁]
    exact (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
      (idealJoint_oneSidedGarblerSim hproj hcorrect hn c x) _
  rwa [h0, zero_add] at h

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete bound that leaves the oblivious-transfer replacement gap as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedProtocol G n c OT` for the coalition `{0}`, with the simulator
composed from `Yao.garblerSim` and any simulators `S₂` for `OT`, is at most the distance between
the hybrid execution in `batchOTWorld` against the reduction `composeDistinguisher`, which
produces the garbler's view of the transfer with `S₂`, and the real execution over `OT`. -/
theorem semiHonestAdvantage_composedProtocol_garbler_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {0} = garblerSim G n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) {0}
        (composeSim (protocol G n c) S₁ S₂ {0}) x D ≤
      Game.advantage
        (((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x).bind
          fun r => ProbComp.eval (composeDistinguisher (protocol G n c) S₂ {0} x D r))
        (((composedProtocol G n c OT).realJoint W₂ {0} x).bind fun r => ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (protocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (functionality G c) S₁ (fun _ => OT) S₂ {0} x D
  have h0 : semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (functionality G c) {0} (S₁ {0}) x
      (composeDistinguisher (protocol G n c) S₂ {0} x D) = 0 := by
    rw [hS₁]
    exact (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
      (idealJoint_garblerSim hproj hcorrect hn c x) _
  rwa [h0, zero_add] at h

/-! ### Corrupted evaluator: the hybrid term is simulation privacy of the garbling scheme -/

/-- **The reduction to simulation privacy at a fixed instance**, for a corrupted evaluator of
`Yao.protocol G n c`: from a distinguisher `D` of the evaluator's view and the outputs on the input
tuple `x`, the `prv.sim` adversary that queries `c.fn` on the garbler's bits followed by the
evaluator's, reads the evaluator's view from the view `(F, X, d)` that it is given
(`viewOfPrvView`) and runs `D` on this view with the function's output as both parties' outputs.
It keeps no state. This is `Yao.evaluatorToPrvSim` at fixed public parameters and inputs. -/
@[expose] noncomputable def evaluatorDistinguisherToPrvSim (c : Params G)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) : PrvSimAdversary Fn Unit where
  choose _ := pure (⟨c.fn, circuitInput x⟩, ())
  guess _ V := D (singletonView (viewOfPrvView c (x 1) (V.getD ⟨[], [], []⟩)),
    fun _ => G.ev c.fn (circuitInput x))

/-- **The one-sided reduction to simulation privacy at a fixed instance**, for a corrupted
evaluator of `Yao.oneSidedProtocol G n c`: from a distinguisher `D` of the evaluator's view and the
outputs on the input tuple `x`, the `prv.sim` adversary that queries `c.fn` on the garbler's bits
followed by the evaluator's, reads the evaluator's view from the view `(F, X, d)` that it is given
(`oneSidedViewOfPrvView`) and runs `D` on this view with `oneSidedOutputs` of the function's output
(`[]` for the garbler). It keeps no state. This is `Yao.oneSidedEvaluatorToPrvSim` at fixed public
parameters and inputs. -/
@[expose] noncomputable def oneSidedEvaluatorDistinguisherToPrvSim (c : Params G)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (oneSidedSchedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) : PrvSimAdversary Fn Unit where
  choose _ := pure (⟨c.fn, circuitInput x⟩, ())
  guess _ V := D (singletonView (oneSidedViewOfPrvView c (x 1) (V.getD ⟨[], [], []⟩)),
    oneSidedOutputs (G.ev c.fn (circuitInput x)))

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): the transfers are the ideal `batchOTWorld` and the statement is at a fixed instance.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage of any distinguisher `D` against the hybrid protocol `Yao.protocol G n c` for the
coalition `{1}`, with the simulator `Yao.evaluatorSim G Φ S` built from a garbling simulator `S`
for the side information `Φ`, equals the `prv.sim` advantage of the reduction
`Yao.evaluatorDistinguisherToPrvSim c x D` against `S n`. Nothing is assumed about `S` or `D`. -/
theorem semiHonestAdvantage_protocol_evaluator_eq (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (Φ : SideInfo Fn Λ)
    (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
        (functionality G c) {1} (evaluatorSim G Φ S n c) x D =
      prvSimAdvantage G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) := by
  have hideal : ProbComp.eval
      (idealJoint (functionality G c) {1} (evaluatorSim G Φ S n c) x >>= D) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) false) := by
    simp only [prvSimExperiment, evaluatorDistinguisherToPrvSim, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    simp only [length_circuitInput, ↓reduceIte, Bool.false_eq_true]
    simp only [idealJoint, functionality, Functionality.ofDeterministic, evaluatorSim,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, Option.getD_some]
    rfl
  have hreal : ((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x).bind
      (fun r => ProbComp.eval (D r)) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) true) := by
    simp only [prvSimExperiment, evaluatorDistinguisherToPrvSim, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    simp only [length_circuitInput, ↓reduceIte]
    simp only [realJoint_evaluator, Scheme.prvView, Scheme.garble, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind, PMF.pure_bind,
      Option.getD_some]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
    simp only [Function.comp_apply, viewOfPrvView_gb hproj,
      runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  rw [semiHonestAdvantage, hideal, hreal]
  rfl

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): the transfers are the ideal `batchOTWorld`, the protocol is the one-sided one and the
statement is at a fixed instance.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage of any distinguisher `D` against the hybrid protocol `Yao.oneSidedProtocol G n c` for
the coalition `{1}`, with the simulator `Yao.oneSidedEvaluatorSim G Φ S` built from a garbling
simulator `S` for the side information `Φ`, equals the `prv.sim` advantage of the reduction
`Yao.oneSidedEvaluatorDistinguisherToPrvSim c x D` against `S n`. Nothing is assumed about `S` or
`D`. -/
theorem semiHonestAdvantage_oneSidedProtocol_evaluator_eq (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (Φ : SideInfo Fn Λ)
    (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (oneSidedSchedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
        (oneSidedFunctionality G c) {1} (oneSidedEvaluatorSim G Φ S n c) x D =
      prvSimAdvantage G Φ n (S n) (oneSidedEvaluatorDistinguisherToPrvSim c x D) := by
  have hideal : ProbComp.eval
      (idealJoint (oneSidedFunctionality G c) {1} (oneSidedEvaluatorSim G Φ S n c) x >>= D) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (oneSidedEvaluatorDistinguisherToPrvSim c x D) false) := by
    simp only [prvSimExperiment, oneSidedEvaluatorDistinguisherToPrvSim, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    simp only [length_circuitInput, ↓reduceIte, Bool.false_eq_true]
    simp only [idealJoint, oneSidedFunctionality, Functionality.ofDeterministic,
      oneSidedEvaluatorSim, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
      Option.getD_some]
    rfl
  have hreal :
      ((oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x).bind
        (fun r => ProbComp.eval (D r)) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (oneSidedEvaluatorDistinguisherToPrvSim c x D) true) := by
    simp only [prvSimExperiment, oneSidedEvaluatorDistinguisherToPrvSim, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    simp only [length_circuitInput, ↓reduceIte]
    simp only [realJoint_oneSided_evaluator, Scheme.prvView, Scheme.garble, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind, PMF.pure_bind,
      Option.getD_some]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
    simp only [Function.comp_apply, oneSidedViewOfPrvView_gb hproj,
      runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  rw [semiHonestAdvantage, hideal, hreal]
  rfl

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed instance that leaves the oblivious-transfer replacement gap as
a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedOneSidedProtocol G n c OT` for the coalition `{1}`, with the
simulator composed from `Yao.oneSidedEvaluatorSim G Φ S` and any simulators `S₂` for `OT`, is at
most the `prv.sim` advantage against the garbling simulator `S n` of the explicit reduction
`Yao.oneSidedEvaluatorDistinguisherToPrvSim` applied to `composeDistinguisher`, which produces the
evaluator's view of the transfer with `S₂`, plus the distance between the hybrid execution in
`batchOTWorld` against `composeDistinguisher` and the real execution over `OT`. Nothing is assumed
about `S`, `S₂`, `OT` or `D`. -/
theorem semiHonestAdvantage_composedOneSidedProtocol_evaluator_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (oneSidedSchedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {1} = oneSidedEvaluatorSim G Φ S n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedOneSidedProtocol G n c OT) W₂ (oneSidedFunctionality G c) {1}
        (composeSim (oneSidedProtocol G n c) S₁ S₂ {1}) x D ≤
      prvSimAdvantage G Φ n (S n) (oneSidedEvaluatorDistinguisherToPrvSim c x
          (composeDistinguisher (oneSidedProtocol G n c) S₂ {1} x D)) +
        Game.advantage
          (((oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1}
            x).bind fun r =>
              ProbComp.eval (composeDistinguisher (oneSidedProtocol G n c) S₂ {1} x D r))
          (((composedOneSidedProtocol G n c OT).realJoint W₂ {1} x).bind fun r =>
            ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (oneSidedProtocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (oneSidedFunctionality G c) S₁ (fun _ => OT) S₂
    {1} x D
  have h1 : semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (oneSidedFunctionality G c) {1} (S₁ {1}) x
      (composeDistinguisher (oneSidedProtocol G n c) S₂ {1} x D) =
      prvSimAdvantage G Φ n (S n) (oneSidedEvaluatorDistinguisherToPrvSim c x
        (composeDistinguisher (oneSidedProtocol G n c) S₂ {1} x D)) := by
    rw [hS₁]
    exact semiHonestAdvantage_oneSidedProtocol_evaluator_eq hproj hcorrect hn c Φ S x _
  rwa [h1] at h

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed instance that leaves the oblivious-transfer replacement gap as
a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedProtocol G n c OT` for the coalition `{1}`, with the simulator
composed from `Yao.evaluatorSim G Φ S` and any simulators `S₂` for `OT`, is at most the `prv.sim`
advantage against the garbling simulator `S n` of the explicit reduction
`Yao.evaluatorDistinguisherToPrvSim` applied to `composeDistinguisher`, which produces the
evaluator's view of the transfer with `S₂`, plus the distance between the hybrid execution in
`batchOTWorld` against `composeDistinguisher` and the real execution over `OT`. Nothing is assumed
about `S`, `S₂`, `OT` or `D`. -/
theorem semiHonestAdvantage_composedProtocol_evaluator_le
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (hS₁ : S₁ {1} = evaluatorSim G Φ S n c)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) {1}
        (composeSim (protocol G n c) S₁ S₂ {1}) x D ≤
      prvSimAdvantage G Φ n (S n) (evaluatorDistinguisherToPrvSim c x
          (composeDistinguisher (protocol G n c) S₂ {1} x D)) +
        Game.advantage
          (((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x).bind
            fun r => ProbComp.eval (composeDistinguisher (protocol G n c) S₂ {1} x D r))
          (((composedProtocol G n c OT).realJoint W₂ {1} x).bind fun r =>
            ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (protocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (functionality G c) S₁ (fun _ => OT) S₂ {1} x D
  have h1 : semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (functionality G c) {1} (S₁ {1}) x
      (composeDistinguisher (protocol G n c) S₂ {1} x D) =
      prvSimAdvantage G Φ n (S n) (evaluatorDistinguisherToPrvSim c x
        (composeDistinguisher (protocol G n c) S₂ {1} x D)) := by
    rw [hS₁]
    exact semiHonestAdvantage_protocol_evaluator_eq hproj hcorrect hn c Φ S x _
  rwa [h1] at h

end Cslib.Crypto.Protocols.MPC.Yao
