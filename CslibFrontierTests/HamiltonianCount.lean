/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount
import CslibFrontier.Algorithms.WordRAM.HamiltonianCount
import Mathlib.Data.Fin.VecNotation

/-!
# Worked inclusion–exclusion Hamiltonian-path counting examples

These kernel-checked examples (using `decide +kernel`, never `native_decide`) exercise
`Cslib.Algorithms.Lean.TSP` (`countHamPaths`, `decideHamPath`) and
`Cslib.Algorithms.WordRAM.HamiltonianCount` (`program_spec`, `decideProgram_spec`):

1. A directed path `0 → 1 → 2` on `Fin 3` with a unique Hamiltonian path.
2. A directed branching graph `0 → 1, 0 → 2` on `Fin 3` with no Hamiltonian path (`count = 0`).
3. Complete loopless directed graphs on `Fin 3` (`3! = 6` Hamiltonian paths) and `Fin 4`
   (`4! = 24` Hamiltonian paths).
4. A 4-vertex diamond digraph (`0 → 1, 0 → 2, 1 ↔ 2, 1 → 3, 2 → 3`) with exactly `2` Hamiltonian
   paths.
5. Edge cases on `0` and `1` vertices.
6. Standard-basis word-RAM certificates (`≤ 64 * ((n ^ 3 + 1) * 2 ^ n)` instructions) at
   explicit fitting word widths (`FitsWidth`).
-/

namespace CslibFrontierTests.HamiltonianCount

open Cslib.Algorithms.Lean.TSP
open Cslib.Algorithms.WordRAM.HamiltonianCount Cslib.WordRAM

/-! ### 1. A directed path on three vertices -/

/-- The directed path `0 → 1 → 2` on `Fin 3`. -/
def path3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, false], ![false, false, true], ![false, false, false]]

example : countHamPaths path3 = 1 := by decide +kernel
example : (hamPaths path3).card = 1 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel
example : decideHamPath path3 = true := by decide +kernel
example : (hamPaths path3).Nonempty := (decideHamPath_eq_true_iff path3).1 (by decide +kernel)

/-! ### 2. A digraph on three vertices without a Hamiltonian path -/

/-- Out-branching `0 → 1` and `0 → 2` with no arcs between `1` and `2`. -/
def noHam3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, true], ![false, false, false], ![false, false, false]]

example : countHamPaths noHam3 = 0 := by decide +kernel
example : decideHamPath noHam3 = false := by decide +kernel
example : ¬ (hamPaths noHam3).Nonempty := fun h => by
  have := (decideHamPath_eq_true_iff noHam3).2 h
  revert this
  decide +kernel

/-! ### 3. Complete loopless directed graphs `K₃` and `K₄` -/

/-- Complete loopless directed graph on `Fin n`: an arc between every pair of distinct vertices. -/
def completeDigraph (n : ℕ) (u v : Fin n) : Bool := u != v

example : countHamPaths (completeDigraph 3) = 6 := by decide +kernel
example : (hamPaths (completeDigraph 3)).card = 6 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel

example : countHamPaths (completeDigraph 4) = 24 := by decide +kernel
example : (hamPaths (completeDigraph 4)).card = 24 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel

/-! ### 4. A 4-vertex diamond digraph with two Hamiltonian paths -/

/-- `0` reaches `1` and `2`, `1` and `2` have arcs both ways, and both reach `3`: the two
Hamiltonian paths are `0 → 1 → 2 → 3` and `0 → 2 → 1 → 3`. -/
def diamond4 : Fin 4 → Fin 4 → Bool :=
  ![![false, true, true, false],
    ![false, false, true, true],
    ![false, true, false, true],
    ![false, false, false, false]]

example : countHamPaths diamond4 = 2 := by decide +kernel
example : (hamPaths diamond4).card = 2 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel
example : decideHamPath diamond4 = true := by decide +kernel

/-! ### 5. Edge cases (`n = 0` and `n = 1`) -/

example : countHamPaths (n := 0) (fun _ _ => false) = 1 := by decide +kernel
example : countHamPaths (n := 1) (fun _ _ => false) = 1 := by decide +kernel
example : countHamPaths (n := 1) (fun _ _ => true) = 1 := by decide +kernel

/-! ### 6. Word-RAM execution certificates (`O(n³ · 2 ^ n)`) -/

def path3Inst : Instance := ⟨3, path3⟩
def noHam3Inst : Instance := ⟨3, noHam3⟩
def k3Inst : Instance := ⟨3, completeDigraph 3⟩
def diamond4Inst : Instance := ⟨4, diamond4⟩
def empty0Inst : Instance := ⟨0, fun _ _ => false⟩
def one1Inst : Instance := ⟨1, fun _ _ => false⟩

example : path3Inst.FitsWidth 12 := by
  unfold Instance.FitsWidth Instance.wordBound
  decide +kernel

example : ∃ steps ≤ 64 * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 program (.init path3Inst.encode) 1 steps := by
  have h := program_spec (I := path3Inst) (w := 12) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hcard : (hamPaths path3).card = 1 := by
    rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel
  simpa [path3Inst, hcard] using h

example : ∃ steps ≤ 64 * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 decideProgram (.init noHam3Inst.encode) 0 steps := by
  have h := decideProgram_spec (I := noHam3Inst) (w := 12) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hne : ¬ (hamPaths noHam3).Nonempty := fun h' => by
    have := (decideHamPath_eq_true_iff noHam3).2 h'
    revert this; decide +kernel
  simpa [noHam3Inst, hne] using h

example : ∃ steps ≤ 64 * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 program (.init k3Inst.encode) 6 steps := by
  have h := program_spec (I := k3Inst) (w := 12) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hcard : (hamPaths (completeDigraph 3)).card = 6 := by
    rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel
  simpa [k3Inst, hcard] using h

example : ∃ steps ≤ 64 * ((4 ^ 3 + 1) * 2 ^ 4),
    Executes 16 decideProgram (.init diamond4Inst.encode) 1 steps := by
  have h := decideProgram_spec (I := diamond4Inst) (w := 16) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hne : (hamPaths diamond4).Nonempty :=
    (decideHamPath_eq_true_iff diamond4).1 (by decide +kernel)
  simpa [diamond4Inst, hne] using h

example : ∃ steps ≤ 64 * ((0 ^ 3 + 1) * 2 ^ 0),
    Executes 7 program (.init empty0Inst.encode) 1 steps := by
  have h := program_spec (I := empty0Inst) (w := 7) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hcard : (hamPaths (fun _ _ : Fin 0 => false)).card = 1 := by
    rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel
  simpa [empty0Inst, hcard] using h

example : ∃ steps ≤ 64 * ((1 ^ 3 + 1) * 2 ^ 1),
    Executes 7 program (.init one1Inst.encode) 1 steps := by
  have h := program_spec (I := one1Inst) (w := 7) (by
    unfold Instance.FitsWidth Instance.wordBound; decide +kernel)
  have hcard : (hamPaths (fun _ _ : Fin 1 => false)).card = 1 := by
    rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel
  simpa [one1Inst, hcard] using h

end CslibFrontierTests.HamiltonianCount
