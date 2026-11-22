/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Inversion.Markov

/-! Boundary clients for Markov's inversion theorem. Coordinatewise complementation on three
bits needs two shared NOT gates, and duplicating one complemented input still costs one. Zero
inputs, zero outputs and monotone systems have zero negation complexity. -/

namespace CslibFrontierTests.MarkovInversion

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def complement3 (x : BitString 3) : BitString 3 := fun i => !x i

private theorem complement3_decrease : decrease complement3 = 3 := by
  apply Nat.le_antisymm (decrease_le_numInputs complement3)
  let xs : List (BitString 3) :=
    [![false, false, false], ![true, false, false], ![true, true, false], ![true, true, true]]
  have hchain : xs.IsChain (· ≤ ·) := by decide
  have hcount : chainDecrease complement3 xs = 3 := by
    simp [xs, chainDecrease, complement3, Pi.le_def, Fin.forall_fin_succ, Bool.le_iff_imp]
  simpa only [hcount] using chainDecrease_le_decrease complement3 hchain

/-- The system cost is determined by simultaneous decreases, and the optimum is attained. -/
example : ecomplexityFrom interpretation negationCost complement3 id = 2 ∧
    ∃ c : Circuit signature 3 3, c.Computes interpretation complement3 ∧
      c.program.cost negationCost = 2 := by
  constructor
  · rw [ecomplexityFrom_negationCost_eq_clog, complement3_decrease]
    decide
  · simpa only [complement3_decrease, show Nat.clog 2 (3 + 1) = 2 by decide] using
      exists_computes_negationCost_eq_clog complement3

private def repeatedComplement (x : BitString 1) : BitString 2 := fun _ => !x 0

private def repeatedNot : Circuit signature 1 2 :=
  (Circuit.oneGate (σ := signature) .not id).comapOutputs (fun _ => 0)

/-- Two designated outputs may share a single internal negation gate. -/
example : repeatedNot.Computes interpretation repeatedComplement ∧
    repeatedNot.program.cost negationCost = 1 := by
  constructor
  · intro x
    funext i
    simp [repeatedNot, repeatedComplement, interpretation]
  · change (Circuit.oneGate (σ := signature) .not id).program.cost negationCost = 1
    rw [Circuit.cost_program_oneGate, negationCost_not]

/-- Duplicating the output preserves the exact one-negation optimum. -/
example : ecomplexityFrom interpretation negationCost repeatedComplement id = 1 := by
  have hd : decrease repeatedComplement = 1 := by
    apply Nat.le_antisymm (decrease_le_numInputs repeatedComplement)
    have hchain : ([fun _ => false, fun _ => true] : List (BitString 1)).IsChain (· ≤ ·) := by
      decide
    have h := chainDecrease_le_decrease repeatedComplement hchain
    simpa [chainDecrease, repeatedComplement, Pi.le_def, Bool.le_iff_imp] using h
  rw [ecomplexityFrom_negationCost_eq_clog, hd]
  decide

/-- A monotone multioutput system needs no NOT gates. -/
example {n m : ℕ} (target : BitString n → BitString m) (h : Monotone target) :
    ecomplexityFrom interpretation negationCost target id = 0 := by
  rw [ecomplexityFrom_negationCost_eq_clog, (decrease_eq_zero_iff target).mpr h]
  simp

/-- The theorem includes systems of constants on an empty input family. -/
example {m : ℕ} (target : BitString 0 → BitString m) :
    ecomplexityFrom interpretation negationCost target id = 0 := by
  have hd : decrease target = 0 := Nat.eq_zero_of_le_zero (decrease_le_numInputs target)
  rw [ecomplexityFrom_negationCost_eq_clog, hd]
  simp

/-- An empty output family has no decreases or negation cost. -/
example {n : ℕ} (target : BitString n → BitString 0) :
    ecomplexityFrom interpretation negationCost target id = 0 := by
  have hm : Monotone target := fun _ _ _ i => i.elim0
  rw [ecomplexityFrom_negationCost_eq_clog, (decrease_eq_zero_iff target).mpr hm]
  simp

end CslibFrontierTests.MarkovInversion
