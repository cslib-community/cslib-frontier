/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Quantum.Interactive
public import CslibFrontier.Computability.Circuit.Quantum.Input

/-!
# Uniform quantum multiprover interactions

Each prover acts only on its own message and private qubits. The verifier acts on
all the message qubits and its own private qubits. The prover count, message widths
and verifier turns are generated in polynomial time from the input length. There is
no size bound on the private registers of the provers. They start in an arbitrary
joint unit vector, allowing prior entanglement across any finite private dimensions.

The register layout and alternation follow [KobayashiMatsumoto2003, §3.2, arXiv:cs/0102013v5].
Local registers are padded to equal widths. Mixed shared states and nonunitary local
operations can be represented by purification with additional private qubits. The
verifier receives the instance in its initial basis state, as in the single-prover model.

## Main definitions

* `Cslib.Quantum.UniformMultiproverVerifier`: the verifier and its partition of message qubits.
* `Cslib.Quantum.UniformMultiproverVerifier.interaction` and
  `Cslib.Quantum.UniformMultiproverVerifier.acceptProb`: the complete joint experiment.
## Main results

* `Cslib.Quantum.UniformMultiproverVerifier.proverWires_ne`: distinct provers' wires are disjoint.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- A uniform interactive verifier with one equal-width message block per prover. -/
structure UniformMultiproverVerifier extends UniformInteractiveVerifier where
  /-- The number of provers on inputs of the given length. -/
  proverCount : ℕ → ℕ
  /-- The width of each prover's message block. -/
  messagePerProver : ℕ → ℕ
  computableInPolyTime_proverCount : ComputableInPolyTime proverCount encUnary encUnary
  computableInPolyTime_messagePerProver : ComputableInPolyTime messagePerProver encUnary encUnary
  proverCount_pos : ∀ n, 0 < proverCount n
  messageWidth_eq : ∀ n, messageWidth n = proverCount n * messagePerProver n

namespace UniformMultiproverVerifier

variable (V : UniformMultiproverVerifier)

/-- One response operation per prover per turn, each on a local register. -/
abbrev Strategy (n p : ℕ) :=
  Fin (V.turns n).1.length → Fin (V.proverCount n) → Gate (V.messagePerProver n + p)

/-- Place every pair of prover index and local wire index in the joint register.
The message blocks precede all private blocks. -/
@[expose] def allProverWires (n p : ℕ) :
    Fin (V.proverCount n) × Fin (V.messagePerProver n + p) ↪
      Fin (V.privateWidth n + V.messageWidth n + V.proverCount n * p) :=
  let message := finProdFinEquiv.trans (finCongr (V.messageWidth_eq n).symm)
  let split := (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv.symm).trans
    (Equiv.prodSumDistrib (Fin (V.proverCount n)) (Fin (V.messagePerProver n)) (Fin p))
  let slots := split.trans ((Equiv.sumCongr message finProdFinEquiv).trans finSumFinEquiv)
  slots.toEmbedding.trans (V.toUniformInteractiveVerifier.proverWires n (V.proverCount n * p))

/-- The local message and private qubits of prover `i` in the joint register. -/
@[expose] def proverWires (n p : ℕ) (i : Fin (V.proverCount n)) :
    Fin (V.messagePerProver n + p) ↪
      Fin (V.privateWidth n + V.messageWidth n + V.proverCount n * p) :=
  ⟨fun a => V.allProverWires n p (i, a), fun _ _ h =>
    congrArg Prod.snd ((V.allProverWires n p).injective h)⟩

/-- Prover operations at distinct indices act on disjoint wires. -/
theorem proverWires_ne {n p : ℕ} {i j : Fin (V.proverCount n)} (hij : i ≠ j)
    (a b : Fin (V.messagePerProver n + p)) :
    V.proverWires n p i a ≠ V.proverWires n p j b :=
  fun h => hij (congrArg Prod.fst ((V.allProverWires n p).injective h))

/-- Apply all local response operations in prover index order between consecutive verifier turns. -/
@[expose] noncomputable def interaction (n : ℕ) {p : ℕ} (strategy : V.Strategy n p) :
    Circuit (V.privateWidth n + V.messageWidth n + V.proverCount n * p) :=
  V.toUniformInteractiveVerifier.composeTurns n (V.proverCount n * p) fun j =>
    List.ofFn fun i : Fin (V.proverCount n) => ⟨_, strategy j i, V.proverWires n p i⟩

/-- The verifier's probability of acceptance from a joint unit vector on the prover registers.
The verifier and the message registers start in the basis state specified by the input and zeros. -/
@[expose] noncomputable def acceptProb (x : List Bool) {p : ℕ}
    (state : Qubits (V.proverCount x.length * p)) (strategy : V.Strategy x.length p) : ℝ :=
  let initial := embedState (Fin.natAddEmb (V.privateWidth x.length + V.messageWidth x.length))
    (inputState _ x) state
  measureProb ((V.interaction x.length strategy).eval initial) (accepting _)

/-- The initial embedding and the joint circuit preserve norm. -/
theorem acceptProb_le_one (x : List Bool) {p : ℕ}
    (state : Qubits (V.proverCount x.length * p)) (strategy : V.Strategy x.length p)
    (hstate : ‖state‖ = 1) : V.acceptProb x state strategy ≤ 1 := by
  refine (measureProb_le_measureProb_univ _ _).trans_eq ?_
  rw [measureProb_univ, Circuit.norm_eval, LinearIsometry.norm_map, hstate, one_pow]

end UniformMultiproverVerifier
end Cslib.Quantum
