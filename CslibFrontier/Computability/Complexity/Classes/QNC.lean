/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Layered

/-!
# Shallow quantum circuit classes

The nonuniform decision version of `QNC` uses bounded-arity gates, polynomial width,
and polylogarithmically many layers of gates on disjoint wires. This is the Zoo's
bounded-error decision convention (`BQNC`), using the layering of
[Moore, Nilsson][MooreNilsson2001]. For the constant-depth `QNC0` decision class we
use exact output, in keeping with the distinction between exact and bounded-error
shallow circuits in [Høyer, Špalek][HoyerSpalek2005].

`QAC0` uses exact decision and allows unbounded-control Toffoli gates in addition
to single-qubit gates [Moore][Moore1999QuantumCircuits]. These are decision classes
defined through a measured answer bit, with no condition on the unmeasured output.

## Main definitions

* `Cslib.Complexity.QNC`, `Cslib.Complexity.BQNC`: bounded-error polylogarithmic depth.
* `Cslib.Complexity.QNC0`, `Cslib.Complexity.QAC0`: exact constant depth.
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum

variable {α : Type}

/-- Bounded-error decision by nonuniform polynomial-size quantum circuits of bounded gate
arity and polylogarithmic depth. -/
def QNC (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : LayeredCircuitFamily, F.HasBoundedArity ∧
    (∃ c k : ℕ, ∀ n, (F.layers n).length ≤ c * (Nat.log 2 n + 1) ^ k) ∧
    ∀ a, (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧
      (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3)}

/-- The Zoo's alternate name for bounded-error `QNC`. -/
abbrev BQNC (enc : α ↪ List Bool) : Set (Set α) := QNC enc

/-- Exact decision by nonuniform constant-depth quantum circuits of bounded gate arity. -/
def QNC0 (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : LayeredCircuitFamily, F.HasBoundedArity ∧
    (∃ c : ℕ, ∀ n, (F.layers n).length ≤ c) ∧
    ∀ a, (a ∈ A → F.acceptProb (enc a) = 1) ∧
      (a ∉ A → F.acceptProb (enc a) = 0)}

/-- Exact decision by nonuniform constant-depth quantum circuits with single-qubit and
unbounded-control Toffoli gates. -/
def QAC0 (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : LayeredCircuitFamily,
    (∀ n, ∀ layer ∈ F.layers n, ∀ g ∈ layer, g.IsQACGate) ∧
    (∃ c : ℕ, ∀ n, (F.layers n).length ≤ c) ∧
    ∀ a, (a ∈ A → F.acceptProb (enc a) = 1) ∧
      (a ∉ A → F.acceptProb (enc a) = 0)}

/-- Exact constant-depth decision is bounded-error polylogarithmic-depth decision. -/
theorem QNC0_subset_QNC {enc : α ↪ List Bool} : QNC0 enc ⊆ QNC enc := by
  rintro A ⟨F, hArity, ⟨c, hc⟩, hF⟩
  refine ⟨F, hArity, ⟨c, 0, fun n => ?_⟩, fun a => ⟨?_, ?_⟩⟩
  · simpa using hc n
  · intro ha
    rw [(hF a).1 ha]
    norm_num
  · intro ha
    rw [(hF a).2 ha]
    norm_num

end Cslib.Complexity
