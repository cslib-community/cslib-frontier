/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Evaluate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Tests for the `SYM ∘ AND` evaluation algorithm

Concrete instances of `CslibFrontier.Computability.Circuit.Boolean.SymAnd.Evaluate`:

* the AND count as a zeta transform on one input;
* the pure truth table of `x₀ ⊕ x₁` and three-input majority (`truthTable`, `truthTable_eq`),
  plus edge cases (empty gates, evaluator wrong above circuit size);
* multi-tape Turing-machine encoding `SymAndInstance` / `encSymAndInstance`, `truthTableList`,
  boundary witness for gate masks longer than `n`, and Williams's Evaluation Lemma
  `computableInO_truthTableList` instantiated on parity and threshold-majority symmetric gates.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.Evaluate

open Cslib Cslib.BitString Cslib.Circuits.Boolean Cslib.Circuits.Boolean.SymAnd
  Cslib.Algorithms.Lean Turing.MultiTapeTM

/-! ### Parity of two bits (pure specification) -/

/-- The AND gates `x₀`, `x₀ ∧ x₁`, `x₁`. -/
def xorGates : List (Finset (Fin 2)) := [{0}, {0, 1}, {1}]

/-- `x₀ ⊕ x₁`: exactly one of the three AND gates is satisfied. -/
def xorCircuit : SymAnd (Fin 2) where
  gates := xorGates
  out j := j == 1

/-- At `x = (1, 1)` all three AND gates are satisfied: `∑_{S ⊆ {0, 1}} f S = 1 + 1 + 1`. -/
example : xorCircuit.count (fun i => decide (i ∈ ({0, 1} : Finset (Fin 2)))) = 3 := by
  rw [count_eq_subsetZeta]
  decide +kernel

/-- The pure truth table, in the order `00, 10, 01, 11` (coordinate `0` first). -/
example : truthTable xorGates (fun j => j == 1) = #v[false, true, true, false] := by
  decide +kernel

/-- Correctness of `truthTable` on `xorCircuit`. -/
theorem xor_pure_spec :
    truthTable xorGates (fun j => j == 1) =
      Vector.ofFn (fun k => xorCircuit.eval ((BitString.equivFin 2).symm k)) :=
  truthTable_eq xorCircuit xorGates rfl _ (fun _ _ => rfl)

/-- Non-vacuity: the circuit takes both values. -/
example : xorCircuit.eval ![true, false] = true ∧ xorCircuit.eval ![true, true] = false := by
  decide +kernel

/-! ### Majority of three bits (pure specification) -/

/-- Three fan-in-one gates below the threshold `≥ 2`. -/
def majGates : List (Finset (Fin 3)) := [{0}, {1}, {2}]

/-- Majority of three bits; cells in the order of `BitString.equivFin` (coordinate `0` first). -/
example : truthTable majGates (fun j => decide (2 ≤ j)) =
    #v[false, false, false, true, false, true, true, true] := by decide +kernel

/-! ### Edge cases (pure specification) -/

/-- No AND gates: every count is `0`, so the table is constant `out 0`. -/
example : truthTable ([] : List (Finset (Fin 2))) (fun j => j == 0) =
    #v[true, true, true, true] := by decide +kernel

/-- An evaluator agreeing with the symmetric gate only on `0, …, 3` (the circuit has `3` AND
gates) still yields the truth table. -/
example : truthTable xorGates (fun j => if j ≤ 3 then j == 1 else true) =
    Vector.ofFn (fun k => xorCircuit.eval ((BitString.equivFin 2).symm k)) :=
  truthTable_eq xorCircuit xorGates rfl _ fun j hj => by
    have : j ≤ 3 := hj
    simp only [this, ite_true]
    rfl

/-! ### Multi-tape Turing-machine instances and Williams's Evaluation Lemma -/

/-- `SymAndInstance` for two-bit parity `x₀ ⊕ x₁`. -/
def xorInst : SymAndInstance where
  n := 2
  gates := [[true, false], [true, true], [false, true]]

/-- `SymAndInstance` for three-input majority. -/
def majInst : SymAndInstance where
  n := 3
  gates := [[true, false, false], [false, true, false], [false, false, true]]

/-- Edge case: circuit with no AND gates. -/
def emptyInst : SymAndInstance where
  n := 2
  gates := []

/-- Boundary witness: gate masks longer than `n = 2` (trailing bits at index `≥ n` are ignored). -/
def paddedInst : SymAndInstance where
  n := 2
  gates := [[true, false, true], [true, true, true], [false, true, false]]

example : xorInst.truthTableList (· == 1) = [false, true, true, false] := by decide +kernel

example : majInst.truthTableList (fun j => decide (2 ≤ j)) =
    [false, false, false, true, false, true, true, true] := by decide +kernel

example : emptyInst.truthTableList (· == 0) = [true, true, true, true] := by decide +kernel

example : paddedInst.truthTableList (· == 1) = xorInst.truthTableList (· == 1) := by
  decide +kernel

example : (encSymAndInstance xorInst).length ≤ (xorInst.gates.length + 2) * (2 * xorInst.n + 2) :=
  length_encSymAndInstance_le xorInst (by decide)

/-- The symmetric gate `j == 1` is polynomial-time on binary naturals. -/
theorem computableInPolyTime_xorOut :
    ComputableInPolyTime (fun j : ℕ => j == 1) encNat encBool := by
  fun_prop

/-- The symmetric threshold gate `decide (2 ≤ j)` is polynomial-time on binary naturals. -/
theorem computableInPolyTime_majOut :
    ComputableInPolyTime (fun j : ℕ => decide (2 ≤ j)) encNat encBool := by
  fun_prop

/-- **Williams's Evaluation Lemma instantiated on parity**: evaluating `x.truthTableList (· == 1)`
runs in multi-tape Turing-machine time and space `O((2 ^ n + (|enc x| + 1) ^ c) * (n + 1) ^ c)`. -/
theorem xor_tm_eval :
    ∃ c, ComputableInO (fun x : SymAndInstance => x.truthTableList (· == 1))
      encSymAndInstance encBits
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) :=
  computableInO_truthTableList computableInPolyTime_xorOut

/-- **Williams's Evaluation Lemma instantiated on threshold majority**. -/
theorem maj_tm_eval :
    ∃ c, ComputableInO (fun x : SymAndInstance => x.truthTableList (fun j => decide (2 ≤ j)))
      encSymAndInstance encBits
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) :=
  computableInO_truthTableList computableInPolyTime_majOut

end CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.Evaluate
