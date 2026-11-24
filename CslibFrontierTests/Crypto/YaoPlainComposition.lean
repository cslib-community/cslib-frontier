/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Yao.Instances
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient

/-!
# Tests for Yao's protocol over a transfer subprotocol

A client of `CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage` and
`CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition` under module encapsulation.

* `semiHonestAdvantage_compose` is applied to a composition that the library already has: the GMW
  circuit protocol over the pairwise multiplication protocol, whose subprotocols are perfectly
  private. The composed advantage is that of the outer protocol and so vanishes.
* `clearTransfer` is a plain-model protocol for the batched transfer that sends every offered value
  in the clear, so it is not private. It shows that `Yao.composedProtocol` is defined over a
  concrete plain-model subprotocol and that the bound
  `Yao.semiHonestAdvantage_composedProtocol_garbler_le` asks nothing of the subprotocol: its
  hypotheses hold for point-and-permute garbling on one AND gate, for any base family of hybrid
  simulators and any transfer simulators, and the replacement gap on the right is the only term.
* The same fixtures witness `Yao.semiHonestAdvantage_composedProtocol_evaluator_le` and
  `Yao.semiHonestAdvantage_composedOneSidedProtocol_evaluator_le` for a corrupted evaluator, for
  any side information and any garbling simulator: the right-hand side is the `prv.sim` advantage
  of the explicit reduction plus the replacement gap.
* On the steps of `Yao.protocol`, `Composition.kernelRun` depends on the kernel family only through
  the one batched transfer at the corrupted slots. By `advantage_replacement_eq_kernelRun` the
  replacement gap in these bounds is therefore a gap between the ideal and the real joint
  distributions of the transfer subprotocol; no bound on it is checked here.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainComposition

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC
  Cslib.Probability

/-- **Composition with perfectly private subprotocols.** The GMW circuit protocol composed with the
pairwise multiplication protocol has advantage zero against every distinguisher: by
`semiHonestAdvantage_compose` it is the advantage of the reduction against the outer protocol,
which is perfectly private. -/
example (m n k : ℕ) [NeZero m] (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m)) (x) (D) :
    semiHonestAdvantage ((gmwCircuitProtocol m n k C).compose fun _ => multiPartyMulProtocol m)
      (sharedMulWorld 2) (Functionality.ofDeterministic (circuitFunctionality m n k C)) I
      (composeSim (gmwCircuitProtocol m n k C) (gmwCircuitSim m n k C)
        (fun _ => multiPartyMulSim m) I) x D = 0 := by
  rw [semiHonestAdvantage_compose (W₁ := sharedMulWorld m)
    fun _ => perfectSemiHonestPrivate_multiPartyMul m]
  exact (perfectSemiHonestPrivate_gmwCircuit m n k C).semiHonestAdvantage_eq_zero I x _

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

/-- **Witness for `Yao.semiHonestAdvantage_composedProtocol_garbler_le`.** For point-and-permute
garbling of one AND gate over the plain-model `clearTransfer`, at every parameter `n ≥ 1`, with any
base family `S₀` of hybrid simulators whose garbler component is `Yao.garblerSim` and any transfer
simulators `S₂`: the advantage against the composed protocol for a corrupted garbler is at most the
replacement gap. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    (S₀ : (I : Finset (Fin 2)) → CoalitionSimulator (Yao.schedule andParams)
      (Yao.Input andParams) Yao.Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    semiHonestAdvantage
        (Yao.composedProtocol _ n andParams (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.functionality _ andParams) {0}
        (composeSim (Yao.protocol _ n andParams)
          (Function.update S₀ {0} (Yao.garblerSim _ n andParams)) S₂ {0}) (inputs a b) D ≤
      Game.advantage
        (((Yao.protocol _ n andParams).realJoint
          (batchOTWorld andParams.evaluatorLen (List Bool)) {0} (inputs a b)).bind fun r =>
            ProbComp.eval (composeDistinguisher (Yao.protocol _ n andParams) S₂ {0}
              (inputs a b) D r))
        (((Yao.composedProtocol _ n andParams
          (clearTransfer andParams.evaluatorLen (List Bool))).realJoint noOracleWorld {0}
            (inputs a b)).bind fun r => ProbComp.eval (D r)) :=
  Yao.semiHonestAdvantage_composedProtocol_garbler_le rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld _
    (Function.update_self ..) S₂ (inputs a b) D

/-- **Witness for `Yao.semiHonestAdvantage_composedProtocol_evaluator_le`.** For point-and-permute
garbling of one AND gate over the plain-model `clearTransfer`, at every parameter `n ≥ 1`, with any
side information `Φ`, any garbling simulator `S`, any base family `S₀` of hybrid simulators whose
evaluator component is `Yao.evaluatorSim _ Φ S` and any transfer simulators `S₂`: the advantage
against the composed protocol for a corrupted evaluator is at most the `prv.sim` advantage of the
reduction against `S n` plus the replacement gap. -/
example {Λ : Type} (Φ : SideInfo ValidCircuit Λ) (S : ℕ → PrvSimulator Λ) {n : ℕ} (hn : 0 < n)
    (a b : Bool)
    (S₀ : (I : Finset (Fin 2)) → CoalitionSimulator (Yao.schedule andParams)
      (Yao.Input andParams) Yao.Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    semiHonestAdvantage
        (Yao.composedProtocol _ n andParams (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.functionality _ andParams) {1}
        (composeSim (Yao.protocol _ n andParams)
          (Function.update S₀ {1} (Yao.evaluatorSim _ Φ S n andParams)) S₂ {1}) (inputs a b) D ≤
      prvSimAdvantage (PointPermute.scheme xorFamily) Φ n (S n)
          (Yao.evaluatorDistinguisherToPrvSim andParams (inputs a b)
            (composeDistinguisher (Yao.protocol _ n andParams) S₂ {1} (inputs a b) D)) +
        Game.advantage
          (((Yao.protocol _ n andParams).realJoint
            (batchOTWorld andParams.evaluatorLen (List Bool)) {1} (inputs a b)).bind fun r =>
              ProbComp.eval (composeDistinguisher (Yao.protocol _ n andParams) S₂ {1}
                (inputs a b) D r))
          (((Yao.composedProtocol _ n andParams
            (clearTransfer andParams.evaluatorLen (List Bool))).realJoint noOracleWorld {1}
              (inputs a b)).bind fun r => ProbComp.eval (D r)) :=
  Yao.semiHonestAdvantage_composedProtocol_evaluator_le rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams Φ S
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld _
    (Function.update_self ..) S₂ (inputs a b) D

/-- **Witness for `Yao.semiHonestAdvantage_composedOneSidedProtocol_evaluator_le`**, on the same
fixtures: the one-sided protocol over `clearTransfer`, with the evaluator component of the base
family `Yao.oneSidedEvaluatorSim _ Φ S`. -/
example {Λ : Type} (Φ : SideInfo ValidCircuit Λ) (S : ℕ → PrvSimulator Λ) {n : ℕ} (hn : 0 < n)
    (a b : Bool)
    (S₀ : (I : Finset (Fin 2)) → CoalitionSimulator (Yao.oneSidedSchedule andParams)
      (Yao.Input andParams) Yao.Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    semiHonestAdvantage
        (Yao.composedOneSidedProtocol _ n andParams
          (clearTransfer andParams.evaluatorLen (List Bool)))
        noOracleWorld (Yao.oneSidedFunctionality _ andParams) {1}
        (composeSim (Yao.oneSidedProtocol _ n andParams)
          (Function.update S₀ {1} (Yao.oneSidedEvaluatorSim _ Φ S n andParams)) S₂ {1})
        (inputs a b) D ≤
      prvSimAdvantage (PointPermute.scheme xorFamily) Φ n (S n)
          (Yao.oneSidedEvaluatorDistinguisherToPrvSim andParams (inputs a b)
            (composeDistinguisher (Yao.oneSidedProtocol _ n andParams) S₂ {1} (inputs a b) D)) +
        Game.advantage
          (((Yao.oneSidedProtocol _ n andParams).realJoint
            (batchOTWorld andParams.evaluatorLen (List Bool)) {1} (inputs a b)).bind fun r =>
              ProbComp.eval (composeDistinguisher (Yao.oneSidedProtocol _ n andParams) S₂ {1}
                (inputs a b) D r))
          (((Yao.composedOneSidedProtocol _ n andParams
            (clearTransfer andParams.evaluatorLen (List Bool))).realJoint noOracleWorld {1}
              (inputs a b)).bind fun r => ProbComp.eval (D r)) :=
  Yao.semiHonestAdvantage_composedOneSidedProtocol_evaluator_le rfl
    (PointPermute.scheme_isValid xorFamily).correct hn andParams Φ S
    (clearTransfer andParams.evaluatorLen (List Bool)) noOracleWorld _
    (Function.update_self ..) S₂ (inputs a b) D

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

end CslibFrontierTests.Crypto.YaoPlainComposition
