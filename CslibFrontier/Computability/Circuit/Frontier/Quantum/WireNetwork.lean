/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.CompiledNet

/-!
# Wire-segment tensor-network compilation for quantum circuits

This module compiles active wires of a quantum circuit `C : Cslib.Quantum.Circuit N` into a finite
loopless degree-`d` wire-segment multigraph (`CompiledQuantumNet`) in which zero-qubit and
single-qubit `U(2)` gates (`g.arity ≤ 1`), as well as idle or one-qubit-only ancillas, contribute
**zero** vertices and **zero** edges:

1. **Gate locality and bond-rank-two predicates** (`twoQubitCount`, `TwoLocal`, `HasBondRankTwo`,
   `AllBondRankTwo`). Every `Quantum.Gate.cnot` (`cnot_hasBondRankTwo`) and every controlled
   single-qubit gate `Quantum.Gate.controlled V` (`controlled_hasBondRankTwo`) has Schmidt / bond
   rank at most two, splitting into two degree-`3` vertices (`d = 3`), whereas an arbitrary
   two-qubit `U(4)` gate forms one degree-`4` vertex (`d = 4`).
2. **Active-qubit decoupling and degree-capped tensor networks** (`exists_compiledQuantumNet`).
   Decoupling qubits touched only by `≤ 1`-qubit gates leaves an active wire network on `Aset` of
   size `|V| ≤ 2 n + 6 · twoQubitCount C + 2` whose closed components `Comp` satisfy
   `cycleRankOn Comp + |leafIn ∩ Comp| ≤ twoQubitCount C + 1` (and analogously for `leafOut` and
   the joint `2 n` input/output leaves `leaf2n`).
3. **Single-cut rank, correlation, and fidelity bounds** (`CompiledQuantumNet`). Cutting `P ⊆ V`
   factors transition amplitudes into `2 ^ |G.edgeCut P|` rank-`1` complex terms and single-qubit
   acceptance probabilities into `2 · 4 ^ |G.edgeCut P|` real bilinear terms, yielding single-cut
   bounds for `BQP` correlation, `UQP` sign-rank, quadratic phase-state fidelity, and coherent
   `𝔽₂` linear synthesis (`linBlockMatrix`).

## Main definitions

* `Cslib.Circuits.Frontier.twoQubitCount`: number of two-qubit gates (`g.arity = 2`) in a circuit.
* `Cslib.Circuits.Frontier.TwoLocal`, `Cslib.Circuits.Frontier.HasBondRankTwo`,
  `Cslib.Circuits.Frontier.AllBondRankTwo`: two-qubit locality and bond-rank-two predicates
  (defined via `Cslib.Quantum.Circuit.IsOver`).
* `Cslib.Circuits.Frontier.quantumAcceptProb`, `Cslib.Circuits.Frontier.quantumCorrelation`,
  `Cslib.Circuits.Frontier.phaseState`, `Cslib.Circuits.Frontier.boolMulVec`,
  `Cslib.Circuits.Frontier.linBlockMatrix`: quantum acceptance probability (via
  `Cslib.Quantum.glue`), correlation, quadratic phase states (via `Cslib.Quantum.embedState`), and
  bipartite linear polar block matrices.
* `Cslib.Circuits.Frontier.CompiledQuantumNet`: packaged finite degree-`d` wire network compiled
  from `C : Quantum.Circuit N` together with its component cycle-rank and single-cut bounds.

## Main results

* `Cslib.Circuits.Frontier.cnot_hasBondRankTwo`,
  `Cslib.Circuits.Frontier.controlled_hasBondRankTwo`: `Gate.cnot` and `Gate.controlled V` have
  bond rank at most two.
* `Cslib.Circuits.Frontier.quantumAcceptProb_nonneg`,
  `Cslib.Circuits.Frontier.quantumAcceptProb_le_one`,
  `Cslib.Circuits.Frontier.norm_phaseState`: range and unit-norm properties of quantum observables.
* `Cslib.Circuits.Frontier.half_le_cutRank_linBlockMatrix`: bisection cut-rank lower bound for
  `linBlockMatrix n R` of a submatrix-robust matrix `R`.
* `Cslib.Circuits.Frontier.exists_compiledQuantumNet`: compiles any `AllBondRankTwo` (`d = 3`) or
  `TwoLocal` (`d = 4`) quantum circuit into a `CompiledQuantumNet`.
-/
