/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Code
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Layered quantum circuits

In one layer the gates act on pairwise disjoint wire sets. A family's circuits are indexed
by input length, with a polynomial bound on the number of wires.

## Main definitions

* `Cslib.Quantum.LayeredCircuitFamily`: nonuniform families of layered finite circuits.
* `Cslib.Quantum.LayeredCircuitFamily.acceptProb`: final measurement of wire zero.
* `Cslib.Quantum.LayeredCircuitFamily.HasBoundedArity`: one arity bound across the family.
* `Cslib.Quantum.PlacedGate.IsQACGate`: single-qubit and multi-controlled Toffoli gates.
-/

@[expose] public section

namespace Cslib.Quantum

/-- A nonuniform, polynomial-width family of layered quantum circuits. Gates in a layer
act on pairwise disjoint nonempty sets of wires, so the width bounds the gates per layer.
Input bits occupy the first wires and the remaining wires start at zero. -/
structure LayeredCircuitFamily where
  /-- Register width at input length `n`. -/
  width : ℕ → ℕ
  /-- The disjoint gate layers, in execution order. -/
  layers : (n : ℕ) → List (Circuit (width n))
  width_bound : ∃ p : Polynomial ℕ, ∀ n, width n ≤ p.eval n
  input_le_width : ∀ n, n ≤ width n
  width_pos : ∀ n, 0 < width n
  arity_pos : ∀ n, ∀ layer ∈ layers n, ∀ g ∈ layer, 0 < g.arity
  disjoint_wires : ∀ n, ∀ layer ∈ layers n,
    layer.Pairwise fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)

/-- The probability of measuring one on wire zero at the end of the layered circuit. -/
noncomputable def LayeredCircuitFamily.acceptProb (F : LayeredCircuitFamily)
    (x : List Bool) : ℝ :=
  measureProb (Circuit.run (F.layers x.length).flatten (inputState (F.width x.length) x))
    (accepting (F.width x.length))

/-- All gates of the family have arity bounded by a single constant. -/
def LayeredCircuitFamily.HasBoundedArity (F : LayeredCircuitFamily) : Prop :=
  ∃ k : ℕ, ∀ n, ∀ layer ∈ F.layers n, ∀ g ∈ layer, g.arity ≤ k

/-- A QAC gate is a single-qubit gate or a Toffoli gate with arbitrarily many controls.
The target is flipped exactly when all its other wires are one. -/
def PlacedGate.IsQACGate {n : ℕ} (g : PlacedGate n) : Prop :=
  g.arity = 1 ∨ ∃ target : Fin g.arity,
    g.gate = Gate.ofPerm (Equiv.swap (fun _ => true) (fun i => decide (i ≠ target)))

end Cslib.Quantum
