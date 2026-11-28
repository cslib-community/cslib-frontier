/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.Quantum.Search
import CslibFrontier.Computability.QueryComplexity.Quantum.Composition
import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary
import CslibFrontier.Computability.QueryComplexity.Quantum.Simon
import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQueryUpdate
import Mathlib.Algebra.Ring.BooleanRing

/-! The quantum query model: the oracle, the `phaseStep` bridge to `ValueQuery` / `ValueAdversary`,
named `QueryBasis` and `SimonWork` workspace records, and a satisfiable instance of the search
hypothesis. -/

namespace CslibFrontierTests.QuantumSearch

open Cslib.Quantum

/-- The unit state `|0, 1, ()⟩` with one query index, control bit `1` and a trivial workspace. -/
noncomputable def ψ₀ : State 1 Unit := EuclideanSpace.single (0, (true, ())) 1

theorem norm_ψ₀ : ‖ψ₀‖ = 1 := by simp [ψ₀]

-- With a single index, the zero-query identity algorithm outputs it with probability one, so the
-- hypothesis of `card_sub_two_le` is satisfiable.
example : ∀ z, 2 / 3 ≤ regProb (run (fun _ => LinearIsometry.id) ψ₀ (marked z) 0) z := by
  intro z
  fin_cases z
  simp [run, regProb_eq_sum, ψ₀, Fintype.sum_prod_type]
  norm_num

example : ((1 : ℕ) : ℝ) - 2 ≤ 144 * ((0 : ℕ) : ℝ) ^ 2 :=
  card_sub_two_le (fun _ => LinearIsometry.id) norm_ψ₀ 0 (by
    intro z
    fin_cases z
    simp [run, regProb_eq_sum, ψ₀, Fintype.sum_prod_type]
    norm_num)

-- The controlled phase oracle flips the sign on marked indices with control bit `1`, and leaves
-- the control-`0` part alone.
example (ψ : State 3 Unit) :
    (phaseOracle (marked 1) ψ).ofLp (1, (true, ())) = -ψ.ofLp (1, (true, ())) := by
  simp [marked]

example (ψ : State 3 Unit) :
    (phaseOracle (marked 1) ψ).ofLp (1, (false, ())) = ψ.ofLp (1, (false, ())) := by
  simp

-- A single coherent XOR query records the old table entry. Reading it against an
-- independently refreshed bit succeeds with probability 1/2, and with the old bit surely.
private noncomputable def readBit (bit : Bool) : ValueState Unit Bool Unit :=
  runValue addStep (fun _ => LinearIsometry.id) (ket ((), false, ())) (fun _ => bit) 1

private theorem storedBit (old current : Bool) :
    measureProb (readBit old) {((), current, ())} = if old = current then 1 else 0 := by
  cases old <;> cases current <;>
    simp [readBit, runValue, measureProb, valueOracle_apply, addStep_apply, Bool.zero_eq_false]

open scoped BigOperators in
example (old : Bool) :
    (𝔼 fresh : Bool, measureProb (readBit old) {((), fresh, ())}) = (1 / 2 : ℝ) ∧
      measureProb (readBit old) {((), old, ())} = 1 := by
  cases old <;> norm_num [Fintype.expect_eq_sum_div_card, storedBit, Fintype.sum_bool]

-- The retained response now chooses the address to refresh. A false response selects the
-- previously queried address, while a true response selects the untouched second address.
private noncomputable def readFirst (old : Bool) : ValueState Bool Bool Unit :=
  runValue addStep (fun _ => LinearIsometry.id) (ket (false, false, ())) (fun _ => old) 1

private theorem branchScore (old msg current : Bool) :
    measureProb (projOutcomes (fun x => x.2.1 = msg) (readFirst old)) {(false, current, ())} =
      if old = msg ∧ old = current then 1 else 0 := by
  cases old <;> cases msg <;> cases current <;>
    simp [readFirst, runValue, measureProb, valueOracle_apply, addStep_apply, Bool.zero_eq_false]

open scoped BigOperators in
example (old : Bool) :
    (𝔼 fresh : Bool, ∑ msg : Bool,
      measureProb (projOutcomes (fun x => x.2.1 = msg) (readFirst old))
        {(false, Function.update (fun _ => old) msg fresh false, ())}) =
      if old then 1 else (1 / 2 : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.sum_bool, branchScore]
  cases old <;> norm_num [Function.update]

/-! ### Phase-step bridge, named `QueryBasis` / `SimonWork` records, and `twice` -/

-- `phaseStep`, `valueOracle phaseStep`, and `runValue phaseStep` on concrete basis states.
example : (phaseStep true (ket true)).ofLp true = -1 := by simp

example :
    (runValue phaseStep (fun _ => LinearIsometry.id) ψ₀ (fun _ : Fin 1 => true) 1).ofLp
      (0, true, ()) = -1 := by
  rw [runValue_phaseStep]
  simp [run, ψ₀]

-- Concrete `QueryBasis` and `twice` check on the 0-query identity algorithm.
private def q₀ : QueryBasis 1 Unit := ⟨0, true, ()⟩

example : QueryBasis.equiv q₀ = (0, true, ()) := rfl

example (x : Fin 1 → Bool) :
    (run (twice 0 fun _ => LinearIsometry.id) (twiceInit ψ₀) x 0).ofLp (0, true, (), q₀) = 1 := by
  have h := run_twice 0 (fun _ => LinearIsometry.id) ψ₀ x 0 true () q₀
  simpa [run, q₀, ψ₀] using h

example (x : Fin 1 → Bool) :
    measureProb (run (twice 0 fun _ => LinearIsometry.id) (twiceInit ψ₀) x (0 + 0))
      (Finset.univ.filter fun (i, b, w, q) =>
        (i, b, w) ∈ ({(0, true, ())} : Finset _) ∨
          QueryBasis.equiv q ∈ ({(0, true, ())} : Finset _)) = 1 := by
  rw [measureProb_run_twice norm_ψ₀]
  have hp : measureProb (run (fun _ => LinearIsometry.id) ψ₀ x 0) {(0, true, ())} = 1 := by
    simp [run, measureProb, ψ₀]
  rw [hp]
  norm_num

-- Concrete `SimonWork` record check.
private def sw₀ : SimonWork 2 1 := ⟨fun _ => true, fun _ => false⟩

example : simonEquiv (N := 2) (0, false, sw₀) = (fun _ => true, 0, false, fun _ => false) := rfl

end CslibFrontierTests.QuantumSearch
