/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Game.Mixture
import CslibFrontier.Crypto.Protocols.MPC.Yao.Instances
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient

/-!
# Tests for two-stage game mixtures, multi-round hybrid composition, and Yao over a transfer

A client of `CslibFrontier.Crypto.Game.Mixture`,
`CslibFrontier.Crypto.Protocols.MPC.Composition.Hybrid` and
`CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition` under module encapsulation.

* `Game.coe_advantage_bind_le_tsum` and `Game.coe_advantage_bind_bind_le` are checked on two-stage
  games under `module` encapsulation.
* The hybrid bound `Composition.replacementBound` is zero on the GMW circuit composition, whose
  subprotocols are perfectly private, and `semiHonestAdvantage_compose_le_replacementBound` then
  reproduces the zero advantage of that composition with a single-coalition simulator.
* On the steps of `Yao.protocol`, `Composition.kernelRun` depends on the kernel family only through
  the one batched transfer at the corrupted slots.
* `Yao.transferQueries` is checked at both slots: the garbler offers `Yao.garblerOffer` on its
  coins and the evaluator chooses with its input bits.
* `clearTransfer` is a plain-model protocol for the batched transfer that sends every offered value
  in the clear. For point-and-permute garbling on one AND gate, it witnesses
  `Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer`,
  `Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer`,
  `Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer` and
  `Yao.semiHonestAdvantage_composedOneSidedProtocol_le_transfer` directly with single-coalition
  outer simulators (`Yao.garblerSim`, `Yao.oneSidedGarblerSim`, `Yao.evaluatorSim`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainComposition

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC
  Cslib.Probability
open scoped ENNReal

/-- **Mixture advantage bounds.** Both `Game.coe_advantage_bind_le_tsum` and
`Game.coe_advantage_bind_bind_le` apply over an arbitrary first-stage type under `module`
encapsulation, and collapse to `0` on identical second-stage games. -/
example {α : Type*} (d : PMF α) (g : α → Game) :
    Game.advantage (d.bind g) (d.bind g) = 0 ∧
      (Game.advantage (d.bind g) (d.bind g) : ℝ≥0∞) ≤
        ∑' a, d a * (Game.advantage (g a) (g a) : ℝ≥0∞) :=
  ⟨Game.advantage_self _, Game.coe_advantage_bind_le_tsum d g g⟩

example {α : Type*} (p q : PMF α) (g₁ g₂ : α → Game) :
    (Game.advantage (p.bind g₁) (q.bind g₂) : ℝ≥0∞) ≤
      Game.advantage (p.bind g₁) (q.bind g₁) +
        ∑' a, q a * (Game.advantage (g₁ a) (g₂ a) : ℝ≥0∞) :=
  Game.coe_advantage_bind_bind_le p q g₁ g₂

/-- **The hybrid bound vanishes for perfectly private subprotocols.** On the steps of the GMW
circuit protocol over the pairwise multiplication protocol, `Composition.replacementBound` is zero
from every state and for every test. -/
example (m n k : ℕ) [NeZero m] (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m)) (st) (D) :
    Composition.replacementBound (sharedMulWorld m) (sharedMulWorld 2)
      (fun _ => multiPartyMulProtocol m) (fun _ => multiPartyMulSim m) I
      (gmwCircuitProtocol m n k C).steps st D = 0 :=
  Composition.replacementBound_eq_zero (fun _ => perfectSemiHonestPrivate_multiPartyMul m) I _ st D

/-- **The concrete composition theorem on a composition that the library has.** For the GMW
circuit protocol over the pairwise multiplication protocol, both terms of
`semiHonestAdvantage_compose_le_replacementBound` vanish: the outer protocol is perfectly private,
and so are the subprotocols of all its oracle rounds. The bound gives advantage zero. -/
example (m n k : ℕ) [NeZero m] (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m)) (x) (D) :
    semiHonestAdvantage ((gmwCircuitProtocol m n k C).compose fun _ => multiPartyMulProtocol m)
      (sharedMulWorld 2) (Functionality.ofDeterministic (circuitFunctionality m n k C)) I
      (composeSim (gmwCircuitProtocol m n k C) (gmwCircuitSim m n k C I)
        (fun _ => multiPartyMulSim m)) x D = 0 := by
  have h := semiHonestAdvantage_compose_le_replacementBound (gmwCircuitProtocol m n k C)
    (sharedMulWorld m) (sharedMulWorld 2)
    (Functionality.ofDeterministic (circuitFunctionality m n k C)) I (gmwCircuitSim m n k C I)
    (fun _ => multiPartyMulProtocol m) (fun _ => multiPartyMulSim m) x D
  rw [(perfectSemiHonestPrivate_gmwCircuit m n k C).semiHonestAdvantage_eq_zero I x] at h
  simpa only [Composition.replacementBound_eq_zero (W₁ := sharedMulWorld m)
    (fun _ => perfectSemiHonestPrivate_multiPartyMul m), mul_zero, tsum_zero, add_zero,
    ENNReal.coe_zero, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] using h

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ValidCircuit := ⟨⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩, by decide⟩

/-- A keyed family on words: the tweak XORed with copies of the key. -/
def xorFamily (key t : List Bool) : List Bool := List.zipWith xor (key ++ key) (t ++ t ++ t)

/-- The public parameters: the AND gate, with the garbler holding its first input. -/
def andParams : Yao.Params (PointPermute.scheme xorFamily) := ⟨andGate, 1, by decide⟩

/-- The inputs: the garbler's bit `a` and the evaluator's bit `b`. -/
def inputs (a b : Bool) : (i : Fin 2) → Yao.Input andParams i :=
  fun i => Fin.cases (motive := fun i => Yao.Input andParams i) (fun _ => a) (fun _ _ => b) i

/-- The batched transfer in the clear, in the plain model: the sender sends every offered value and
the receiver outputs the values that its choice bits select. Nothing is proved about it here; it
witnesses that a plain-model subprotocol of the type `Yao.composedProtocol` takes exists. -/
def clearTransfer (k : ℕ) (L : Type) :
    Protocol 2 noOracleSpec [Round.message 0 1 (Fin k → Bool → L)]
      ((batchOTSpec k L).Query ()) (fun _ => Unit) ((batchOTSpec k L).Answer ()) where
  sampleCoins _ := pure ()
  steps := .message (sender := 0) (receiver := 1) (fun st => st.1)
    (.done fun i => Fin.cases
      (motive := fun i => (((batchOTSpec k L).Query () i × Unit) ×
        (Round.message (spec := noOracleSpec) 0 1 (Fin k → Bool → L)).Received i) →
          (batchOTSpec k L).Answer () i)
      (fun _ => ())
      (fun j st t => st.2 (Fin.fin_one_eq_zero j ▸ rfl) t (st.1.1 t)) i)

/-- **The kernel program of Yao's protocol draws from the transfer kernel once.** On the steps of
`Yao.protocol`, `Composition.kernelRun` depends on the kernel family only through the joint
distribution of the one batched transfer at the corrupted slots: two families that agree there give
the same program, whatever the transfer subprotocol's schedule and coins. -/
example {n : ℕ} {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (I : Finset (Fin 2))
    (μ ν : (_ : Unit) → (J : Finset (Fin 2)) →
      ((s : Fin 2) → (batchOTSpec andParams.evaluatorLen (List Bool)).Query () s) →
      PMF (((s : J) →
          PartyView ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) Coins₂ sc₂ s) ×
        ((s : Fin 2) → (batchOTSpec andParams.evaluatorLen (List Bool)).Answer () s)))
    (h : ∀ q, μ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I) q =
      ν () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I) q)
    (st) :
    Composition.kernelRun (sc₂ := fun _ => sc₂) (Coins₂ := fun _ => Coins₂) μ I
        (Yao.protocol (PointPermute.scheme xorFamily) n andParams).steps st =
      Composition.kernelRun (sc₂ := fun _ => sc₂) (Coins₂ := fun _ => Coins₂) ν I
        (Yao.protocol (PointPermute.scheme xorFamily) n andParams).steps st := by
  simp only [Yao.protocol, Composition.kernelRun, h]

/-- **The transfer queries, receiver slot.** The evaluator (slot `1`) chooses with its input
bits. -/
example (n : ℕ) (a b : Bool) (r : (i : Fin 2) → Yao.Coins i) :
    Yao.transferQueries n andParams (inputs a b) r 1 = inputs a b 1 :=
  rfl

/-- **The transfer queries, sender slot.** The garbler (slot `0`) offers both tokens of each of the
evaluator's input bits, computed from its own coins. -/
example (n : ℕ) (a b : Bool) (r : (i : Fin 2) → Yao.Coins i) :
    Yao.transferQueries n andParams (inputs a b) r 0 =
      Yao.garblerOffer (PointPermute.scheme xorFamily) n andParams (r 0) :=
  rfl

/-- **Witness for `Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer`.** On the fixtures
above, for a corrupted garbler with `Yao.garblerSim` directly (no dummy family): the advantage
against the composed protocol is at most the expected advantage of `Yao.transferDistinguisher`
against `clearTransfer` on the transfer queries. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    (semiHonestAdvantage
        (Yao.composedProtocol _ n andParams (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.functionality _ andParams) {0}
        (composeSim (Yao.protocol _ n andParams) (Yao.garblerSim _ n andParams) S₂)
        (inputs a b) D : ℝ≥0∞) ≤
      ∑' r, ProbComp.eval (OracleComp.pi
          (Yao.protocol (PointPermute.scheme xorFamily) n andParams).sampleCoins) r *
        (semiHonestAdvantage (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld
          (batchOTFunctionality andParams.evaluatorLen (List Bool))
          (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0}) (S₂ () _)
          (Yao.transferQueries n andParams (inputs a b) r)
          (Yao.transferDistinguisher n andParams S₂ {0} (inputs a b) r D) : ℝ≥0∞) :=
  Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld S₂ (inputs a b) D

/-- **Witness for `Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer`.** Same
fixtures for the one-sided protocol with `Yao.oneSidedGarblerSim` directly. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    (semiHonestAdvantage
        (Yao.composedOneSidedProtocol _ n andParams
          (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.oneSidedFunctionality _ andParams) {0}
        (composeSim (Yao.oneSidedProtocol _ n andParams)
          (Yao.oneSidedGarblerSim _ n andParams) S₂) (inputs a b) D : ℝ≥0∞) ≤
      ∑' r, ProbComp.eval (OracleComp.pi
          (Yao.oneSidedProtocol (PointPermute.scheme xorFamily) n andParams).sampleCoins) r *
        (semiHonestAdvantage (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld
          (batchOTFunctionality andParams.evaluatorLen (List Bool))
          (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0}) (S₂ () _)
          (Yao.transferQueries n andParams (inputs a b) r)
          (Yao.oneSidedTransferDistinguisher n andParams S₂ {0} (inputs a b) r D) : ℝ≥0∞) :=
  Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld S₂ (inputs a b) D

/-- **Witness for `Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer`.** On the
fixtures above, for a corrupted evaluator, any side information `Φ` and any garbling simulator `S`,
plugging `Yao.evaluatorSim _ Φ S n andParams` directly into `composeSim`. -/
example {Λ : Type} (Φ : SideInfo ValidCircuit Λ) (S : ℕ → PrvSimulator Λ) {n : ℕ} (hn : 0 < n)
    (a b : Bool)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    (semiHonestAdvantage
        (Yao.composedProtocol _ n andParams (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.functionality _ andParams) {1}
        (composeSim (Yao.protocol _ n andParams) (Yao.evaluatorSim _ Φ S n andParams) S₂)
        (inputs a b) D : ℝ≥0∞) ≤
      prvSimAdvantage (PointPermute.scheme xorFamily) Φ n (S n)
          (Yao.evaluatorDistinguisherToPrvSim andParams (inputs a b)
            (composeDistinguisher (Yao.protocol _ n andParams) S₂ {1} (inputs a b) D)) +
        ∑' r, ProbComp.eval (OracleComp.pi
            (Yao.protocol (PointPermute.scheme xorFamily) n andParams).sampleCoins) r *
          (semiHonestAdvantage (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld
            (batchOTFunctionality andParams.evaluatorLen (List Bool))
            (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {1}) (S₂ () _)
            (Yao.transferQueries n andParams (inputs a b) r)
            (Yao.transferDistinguisher n andParams S₂ {1} (inputs a b) r D) : ℝ≥0∞) :=
  Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams Φ S
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld S₂ (inputs a b) D

/-- **Witness for `Yao.semiHonestAdvantage_composedOneSidedProtocol_le_transfer`.** On the
fixtures above, for every coalition `I` and any single-coalition simulator `S₁`, with no hypothesis
on the garbling scheme. -/
example (n : ℕ) (a b : Bool) (I : Finset (Fin 2))
    (S₁ : CoalitionSimulator (Yao.oneSidedSchedule andParams)
      (Yao.Input andParams) Yao.Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    (semiHonestAdvantage
        (Yao.composedOneSidedProtocol _ n andParams
          (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.oneSidedFunctionality _ andParams) I
        (composeSim (Yao.oneSidedProtocol _ n andParams) S₁ S₂) (inputs a b) D : ℝ≥0∞) ≤
      semiHonestAdvantage (Yao.oneSidedProtocol _ n andParams)
          (batchOTWorld andParams.evaluatorLen (List Bool))
          (Yao.oneSidedFunctionality _ andParams) I S₁ (inputs a b)
          (composeDistinguisher (Yao.oneSidedProtocol _ n andParams) S₂ I (inputs a b) D) +
        ∑' r, ProbComp.eval (OracleComp.pi
            (Yao.oneSidedProtocol (PointPermute.scheme xorFamily) n andParams).sampleCoins) r *
          (semiHonestAdvantage (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld
            (batchOTFunctionality andParams.evaluatorLen (List Bool))
            (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I) (S₂ () _)
            (Yao.transferQueries n andParams (inputs a b) r)
            (Yao.oneSidedTransferDistinguisher n andParams S₂ I (inputs a b) r D) : ℝ≥0∞) :=
  Yao.semiHonestAdvantage_composedOneSidedProtocol_le_transfer n andParams
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld I S₁ S₂ (inputs a b) D

end CslibFrontierTests.Crypto.YaoPlainComposition
