/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
import CslibFrontier.Algorithms.WordRAM.Hungarian
meta import CslibFrontier.Algorithms.WordRAM.Hungarian
-- Compiled `Code.eval` runs below use the fast structured interpreter.
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Hungarian Method Tests

Kernel-checked examples (without `native_decide`) and Word-RAM execution checks for
`CslibFrontier.Algorithms.Lean.MaxFlow.WeightedMatching`,
`CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian`, and
`CslibFrontier.Algorithms.WordRAM.Hungarian`:

1. **Greedy trap (`2 × 2`):** taking the cheapest entry of row `0` first costs `1 + 100`, while the
   optimum is `2 + 2 = 4`. The solver returns the anti-diagonal with potentials summing to `4`.
2. **A `3 × 3` instance:** the returned matching costs `5`, the potentials are feasible and sum to
   `5`, and every permutation costs at least `5` (checked by enumeration).
3. **Dual adjustments with negative costs (`4 × 4`):** `c (i, j) = (i + 1) (j + 1) - 6` has all row
   minima in column `0`, so the phases have to adjust potentials. The optimum `-4` is the
   anti-diagonal, by the rearrangement inequality.
4. **Edge cases and the structures:** `n = 0` and `n = 1`, positive and negative
   `IsPerfectMatching` and `IsFeasiblePotential` instances, and `permMatching`.
5. **Word-RAM `O(n³)` execution (`Cslib.Algorithms.WordRAM.Hungarian`):** non-vacuous client
   instantiations of `executesList_assignment` and `executes_minCost` through ordinary `module`
   imports, plus concrete `Code.eval` runs across `n = 0, 1, 2, 3, 4`, width invariance, and
   narrow-width fault checks.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Hungarian

open Cslib.Algorithms.Lean.MaxFlow
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Hungarian

/-! ### 1. Greedy trap -/

/-- Costs `[[1, 2], [2, 100]]`. -/
def trapCost : Fin 2 × Fin 2 → ℤ := fun e => ![![1, 2], ![2, 100]] e.1 e.2

example : (hungarian trapCost).matching = {(0, 1), (1, 0)} := by decide

example : matchingCost trapCost (hungarian trapCost).matching = 4 := by decide

/-- The greedy assignment `{(0, 0), (1, 1)}` is a perfect matching costing `101`. -/
example : IsPerfectMatching (fun _ => true) ({(0, 0), (1, 1)} : Finset (Fin 2 × Fin 2)) ∧
    matchingCost trapCost {(0, 0), (1, 1)} = 101 := by
  unfold IsPerfectMatching
  decide

example : ∑ u, (hungarian trapCost).y u + ∑ v, (hungarian trapCost).z v = 4 := by
  decide

/-! ### 2. A `3 × 3` instance -/

/-- Costs `[[4, 1, 3], [2, 0, 5], [3, 2, 2]]`. -/
def cost3 : Fin 3 × Fin 3 → ℤ := fun e => ![![4, 1, 3], ![2, 0, 5], ![3, 2, 2]] e.1 e.2

example : (hungarian cost3).matching = {(0, 1), (1, 0), (2, 2)} := by decide

example : matchingCost cost3 (hungarian cost3).matching = 5 := by decide

/-- Independent certificate check: the output potentials are feasible and sum to the cost. -/
example : IsFeasiblePotential (fun _ => true) cost3 (hungarian cost3).y
      (hungarian cost3).z ∧
    ∑ u, (hungarian cost3).y u + ∑ v, (hungarian cost3).z v = 5 := by
  unfold IsFeasiblePotential
  decide

/-- Brute force: every permutation costs at least the optimum `5`. -/
example : ∀ σ : Equiv.Perm (Fin 3), 5 ≤ ∑ u, cost3 (u, σ u) := by decide

/-- The general theorem applied to the instance. -/
example : IsMinCostPerfectMatching (fun _ => true) cost3 (hungarian cost3).matching :=
  (hungarian_correct cost3).1

/-! ### 3. Dual adjustments with negative costs -/

/-- Costs `(i + 1) (j + 1) - 6`: every row minimum lies in column `0`. -/
def cost4 : Fin 4 × Fin 4 → ℤ := fun e => ((e.1 : ℤ) + 1) * ((e.2 : ℤ) + 1) - 6

example : (hungarian cost4).matching = {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide

example : matchingCost cost4 (hungarian cost4).matching = -4 := by decide

example : IsFeasiblePotential (fun _ => true) cost4 (hungarian cost4).y
      (hungarian cost4).z ∧
    ∑ u, (hungarian cost4).y u + ∑ v, (hungarian cost4).z v = -4 := by
  unfold IsFeasiblePotential
  decide +kernel

/-- Row reduction alone does not give tight potentials here: the row minima sum to `-14`. -/
example : ∑ u, hgRowMin cost4 u = -14 := by decide

/-! ### 4. Edge cases and the structures -/

example : (hungarian (n := 0) fun _ => 0).matching = ∅ := by decide

example : (hungarian (n := 1) fun _ => 7).matching = {(0, 0)} := by decide

example : ¬ IsPerfectMatching (fun _ => true) ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by
  unfold IsPerfectMatching
  decide

example : ¬ IsPerfectMatching (fun _ => true) ({(0, 0), (1, 0)} : Finset (Fin 2 × Fin 2)) := by
  unfold IsPerfectMatching
  decide

/-- Row maxima are not feasible potentials for `trapCost`. -/
example : ¬ IsFeasiblePotential (fun _ => true) trapCost ![2, 100] ![0, 0] := by
  unfold IsFeasiblePotential
  decide

example : IsPerfectMatching (fun _ => true) (permMatching (Equiv.swap (0 : Fin 3) 2)) :=
  isPerfectMatching_permMatching _

example : matchingCost cost3 (permMatching (Equiv.swap (0 : Fin 3) 2)) = 3 + 0 + 3 := by
  rw [matchingCost_permMatching]
  decide

/-! ### 5. Word-RAM `O(n³)` solver checks -/

private def emptyInst : Instance := ⟨0, fun _ => 0⟩
private def singleInst : Instance := ⟨1, fun _ => -7⟩
private def trapInst : Instance := ⟨2, trapCost⟩
private def cost3Inst : Instance := ⟨3, cost3⟩
private def cost4Inst : Instance := ⟨4, cost4⟩

/-- Non-involution `3 × 3` 3-cycle optimum `[1, 2, 0]` (`σ ≠ σ⁻¹`), distinguishing row-to-column
`rowMate` orientation from `colMate`. -/
private def cycle3Inst : Instance where
  n := 3
  cost
    | (0, 1) => 1
    | (1, 2) => 1
    | (2, 0) => 1
    | _ => 10

/-- Tied `2 × 2` optimum where both perfect matchings `[0, 1]` and `[1, 0]` achieve cost `10`. -/
private def tiedInst : Instance where
  n := 2
  cost _ := 5

example : trapInst.assignment = [1, 0] ∧ trapInst.encodedMinCost = Signed.encode 4 := by decide

example : cost3Inst.assignment = [1, 0, 2] ∧ cost3Inst.encodedMinCost = Signed.encode 5 := by
  decide

example : cost4Inst.assignment = [3, 2, 1, 0] ∧
    cost4Inst.encodedMinCost = Signed.encode (-4) := by
  decide +kernel

/-- Ordinary `module` client instantiation of `executesList_assignment` on `cost4` (`4 × 4` signed
costs) at word width `16`, discharging `Fits 16 cost4Inst.wordBound` concretely. -/
example : ∃ steps,
    ExecutesList 16 assignmentProgram (.init cost4Inst.encode) [3, 2, 1, 0] steps ∧
      steps ≤ hungarianTime 4 := by
  have hassn : cost4Inst.assignment = [3, 2, 1, 0] := by decide +kernel
  rw [← hassn]
  exact executesList_assignment cost4Inst (by decide)

/-- Ordinary `module` client instantiation of `executes_minCost` on `cost4` at word width `16`. -/
example : ∃ steps,
    Executes 16 minCostProgram (.init cost4Inst.encode) (Signed.encode (-4)) steps ∧
      steps ≤ hungarianTime 4 := by
  have hcost : cost4Inst.encodedMinCost = Signed.encode (-4) := by decide +kernel
  rw [← hcost]
  exact executes_minCost cost4Inst (by decide)

/-- Boundary `n = 0` client instantiation at word width `8` (`hungarianTime 0 = 52`). -/
example : ∃ steps,
    ExecutesList 8 assignmentProgram (.init emptyInst.encode) [] steps ∧
      steps ≤ 52 :=
  executesList_assignment emptyInst (w := 8) (by decide)

private meta def observeHungarian (w : ℕ) (inst : Instance) :
    Option (List ℕ × ℤ × ℕ) :=
  (inputCode.eval w (hungarianTime inst.n) (Data.init inst.encode)).map
    fun (x, steps) =>
      (outputList x.mem (x.regs Reg.outBase),
        Signed.decode (x.regs Reg.acc),
        steps + 1)

private meta def checkHungarian (w : ℕ) (inst : Instance)
    (expectedAssn : List ℕ) (expectedCost : ℤ) : Bool :=
  match observeHungarian w inst with
  | some (assn, c, totalSteps) =>
    assn == expectedAssn && c == expectedCost && totalSteps ≤ hungarianTime inst.n
  | none => false

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 emptyInst [] 0

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 singleInst [0] (-7)

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 trapInst [1, 0] 4

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 cost3Inst [1, 0, 2] 5

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 cost4Inst [3, 2, 1, 0] (-4)

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 cycle3Inst [1, 2, 0] 3

/-- info: true -/
#guard_msgs in
#eval checkHungarian 16 tiedInst [0, 1] 10

-- Width invariance: running `cost4Inst` at `w = 16` and `w = 64` produces identical outputs and
-- charged instruction counts.
/-- info: true -/
#guard_msgs in
#eval decide (observeHungarian 16 cost4Inst = observeHungarian 64 cost4Inst)

-- Narrow word width (`w = 2`) faults cleanly during setup/address arithmetic.
/-- info: true -/
#guard_msgs in
#eval decide (observeHungarian 2 trapInst = none)

end CslibFrontierTests.Hungarian
