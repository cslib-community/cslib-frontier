/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage
import CslibFrontier.Crypto.Protocols.MPC.Yao.Family
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient

/-!
# Tests for concrete semi-honest advantage and kernel factorization under protocol composition

A client of `CslibFrontier.Crypto.Protocols.MPC.Composition` and
`CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage` under module encapsulation.

* `semiHonestAdvantage_compose` is applied to the GMW circuit protocol composed with the pairwise
  multiplication protocol, whose subprotocols are perfectly private: the composed advantage equals
  that of the outer protocol and so vanishes.
* `semiHonestAdvantage_compose_le` is applied directly to `Yao.protocol` with its single-coalition
  garbler simulator `Yao.garblerSim` (defined for `{0}` without dummy simulators on other
  coalitions) composed with a plain-model `clearTransfer` subprotocol on one AND gate.
* `Composition.kernelRun` on `(Yao.protocol _ n andParams).steps` depends on the kernel family only
  through the single batched-transfer call at the corrupted slots, and
  `advantage_replacement_eq_kernelRun` rewrites the replacement gap of a concrete composed transfer
  protocol into one kernel-program advantage.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MPCCompositionAdvantage

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC
  Cslib.Probability

/-- **Composition with perfectly private subprotocols.** The GMW circuit protocol composed with the
pairwise multiplication protocol has advantage zero against every distinguisher: by
`semiHonestAdvantage_compose` it equals the advantage of `composeDistinguisher` against the outer
protocol, which is perfectly private. -/
example (m n k : ℕ) [NeZero m] (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m)) (x) (D) :
    semiHonestAdvantage ((gmwCircuitProtocol m n k C).compose fun _ => multiPartyMulProtocol m)
      (sharedMulWorld 2) (Functionality.ofDeterministic (circuitFunctionality m n k C)) I
      (composeSim (gmwCircuitProtocol m n k C) (gmwCircuitSim m n k C I)
        (fun _ => multiPartyMulSim m)) x D = 0 := by
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
the receiver outputs the values that its choice bits select. -/
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

/-- **Single-coalition outer simulator in `semiHonestAdvantage_compose_le`.** `Yao.garblerSim` is
typed at `{0}` alone; `composeSim` and `semiHonestAdvantage_compose_le` accept it directly without
any total coalition-simulator family, and exactness of `Yao.garblerSim` zeroes the outer term. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator [Round.message 0 1 (Fin andParams.evaluatorLen → Bool → List Bool)]
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Query ()) (fun _ => Unit)
        ((batchOTSpec andParams.evaluatorLen (List Bool)).Answer ()) J)
    (D) :
    semiHonestAdvantage
        ((Yao.protocol _ n andParams).compose
          fun _ => clearTransfer andParams.evaluatorLen (List Bool))
        noOracleWorld (Yao.functionality _ andParams) {0}
        (composeSim (Yao.protocol _ n andParams) (Yao.garblerSim _ n andParams) S₂) (inputs a b)
        D ≤
      Game.advantage
        (((Yao.protocol _ n andParams).realJoint
          (batchOTWorld andParams.evaluatorLen (List Bool)) {0} (inputs a b)).bind fun r =>
            ProbComp.eval (composeDistinguisher (Yao.protocol _ n andParams) S₂ {0}
              (inputs a b) D r))
        ((((Yao.protocol _ n andParams).compose
          fun _ => clearTransfer andParams.evaluatorLen (List Bool)).realJoint noOracleWorld {0}
            (inputs a b)).bind fun r => ProbComp.eval (D r)) := by
  have h := semiHonestAdvantage_compose_le (Yao.protocol _ n andParams)
    (batchOTWorld andParams.evaluatorLen (List Bool)) noOracleWorld (Yao.functionality _ andParams)
    {0} (Yao.garblerSim _ n andParams)
    (fun _ => clearTransfer andParams.evaluatorLen (List Bool)) S₂ (inputs a b) D
  have h0 : semiHonestAdvantage (Yao.protocol _ n andParams)
      (batchOTWorld andParams.evaluatorLen (List Bool)) (Yao.functionality _ andParams) {0}
      (Yao.garblerSim _ n andParams) (inputs a b)
      (composeDistinguisher (Yao.protocol _ n andParams) S₂ {0} (inputs a b) D) = 0 :=
    (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
      (Yao.idealJoint_garblerSim rfl (PointPermute.scheme_isValid xorFamily).correct hn andParams
        (inputs a b)) _
  rwa [h0, zero_add] at h

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

/-- **Kernel factorization of the replacement gap (`advantage_replacement_eq_kernelRun`).** On
`multiPartyMulProtocol 3` composed with `twoPartyMulProtocol`, the subprotocol-replacement gap
equals the advantage between the ideal-kernel and real-kernel runs of `Composition.kernelRun`. -/
example (I : Finset (Fin 3))
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator twoPartyMulSchedule
        ((sharedMulSpec 2).Query ()) (fun i => Fin.cases Bool (fun _ => Unit) i)
        ((sharedMulSpec 2).Answer ()) J)
    (x : Fin 3 → Bool × Bool) (D) :
    Game.advantage
        (((multiPartyMulProtocol 3).realJoint (sharedMulWorld 2) I x).bind fun r =>
          ProbComp.eval (composeDistinguisher (multiPartyMulProtocol 3) S₂ I x D r))
        ((((multiPartyMulProtocol 3).compose fun _ => twoPartyMulProtocol).realJoint ot14World I
          x).bind fun r => ProbComp.eval (D r)) =
      Game.advantage
        ((ProbComp.eval (OracleComp.pi (multiPartyMulProtocol 3).sampleCoins)).bind fun c₁ =>
          (Composition.kernelRun
            (fun op J q => ProbComp.eval (idealJoint (sharedMulWorld 2 op) J (S₂ op J) q))
            I (multiPartyMulProtocol 3).steps (fun i => (x i, c₁ i))).bind fun res =>
              ProbComp.eval
                (D (fun i : I => ⟨x i.val, (c₁ i.val, (res.1 i).1), (res.1 i).2⟩, res.2)))
        ((ProbComp.eval (OracleComp.pi (multiPartyMulProtocol 3).sampleCoins)).bind fun c₁ =>
          (Composition.kernelRun
            (fun _ J q => twoPartyMulProtocol.realJoint ot14World J q)
            I (multiPartyMulProtocol 3).steps (fun i => (x i, c₁ i))).bind fun res =>
              ProbComp.eval
                (D (fun i : I => ⟨x i.val, (c₁ i.val, (res.1 i).1), (res.1 i).2⟩, res.2))) :=
  advantage_replacement_eq_kernelRun (multiPartyMulProtocol 3) (sharedMulWorld 2) ot14World
    (fun _ => twoPartyMulProtocol) S₂ I x D

end CslibFrontierTests.Crypto.MPCCompositionAdvantage
