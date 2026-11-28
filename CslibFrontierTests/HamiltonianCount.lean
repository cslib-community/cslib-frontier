/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount
public import CslibFrontier.Algorithms.WordRAM.HamiltonianCount
public import Mathlib.Data.Fin.VecNotation

/-!
# Worked inclusion–exclusion Hamiltonian-path counting examples

These kernel-checked examples (using `decide +kernel`, never `native_decide`) exercise both the
pure Karp–Bax specification (`Cslib.Algorithms.Lean.TSP.countHamPaths`, `decideHamPath`) and the
standard-basis Word-RAM realizations (`Cslib.Algorithms.WordRAM.HamiltonianCount.program` and
`decideProgram`):

1. A directed path `0 → 1 → 2` on `Fin 3` (`count = 1`).
2. A directed branching graph `0 → 1, 0 → 2` on `Fin 3` with no Hamiltonian path (`count = 0`).
3. Complete loopless directed graphs on `Fin 3` (`3! = 6`) and `Fin 4` (`4! = 24`).
4. A 4-vertex diamond digraph (`0 → 1, 0 → 2, 1 ↔ 2, 1 → 3, 2 → 3`) with `2` Hamiltonian paths.
5. Edge cases on `0` and `1` vertices, including a `1`-vertex graph with a self-loop.
-/

public section

namespace CslibFrontierTests.HamiltonianCount

open Cslib.Algorithms.Lean.TSP
open Cslib.Algorithms.WordRAM.HamiltonianCount
open Cslib.WordRAM

private theorem executes_count (I : Instance) (w : ℕ) (hfit : I.FitsWidth w)
    {c : ℕ} (hc : (hamPaths I.adj).card = c) :
    ∃ steps ≤ countTimeFactor * ((I.n ^ 3 + 1) * 2 ^ I.n),
      Executes w program (.init I.encode) c steps := by
  obtain ⟨steps, hexec, hbound⟩ := computesInTime_program I w hfit (I.inputFits hfit)
  exact ⟨steps, hbound, hc ▸ hexec⟩

private theorem executes_decide (I : Instance) (w : ℕ) (hfit : I.FitsWidth w)
    {b : ℕ} (hb : (if (hamPaths I.adj).Nonempty then 1 else 0) = b) :
    ∃ steps ≤ decideTimeFactor * ((I.n ^ 3 + 1) * 2 ^ I.n),
      Executes w decideProgram (.init I.encode) b steps := by
  obtain ⟨steps, hexec, hbound⟩ := computesInTime_decideProgram I w hfit (I.inputFits hfit)
  exact ⟨steps, hbound, hb ▸ hexec⟩

example : ¬ program.ReadsWidth := not_readsWidth_program
example : ¬ decideProgram.ReadsWidth := not_readsWidth_decideProgram

/-! ### 1. A directed path on three vertices -/

/-- The directed path `0 → 1 → 2` on `Fin 3`. -/
def path3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, false], ![false, false, true], ![false, false, false]]

/-- Word-RAM instance for `path3`. -/
abbrev path3Inst : Instance := ⟨3, path3⟩

example : countHamPaths path3 = 1 := by decide +kernel
example : (hamPaths path3).card = 1 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel
example : decideHamPath path3 = true := by decide +kernel
example : (hamPaths path3).Nonempty := (decideHamPath_eq_true_iff path3).1 (by decide +kernel)

example : path3Inst.encode = [3, 0, 1, 0, 0, 0, 1, 0, 0, 0] := by decide +kernel
example : ∃ steps ≤ countTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 program (.init path3Inst.encode) 1 steps :=
  executes_count path3Inst 12 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 decideProgram (.init path3Inst.encode) 1 steps :=
  executes_decide path3Inst 12 (by decide +kernel) (by
    have hne : (hamPaths path3).Nonempty :=
      (decideHamPath_eq_true_iff path3).1 (by decide +kernel)
    simp [hne])

/-! ### 2. A digraph on three vertices without a Hamiltonian path -/

/-- Out-branching `0 → 1` and `0 → 2` with no arcs between `1` and `2`. -/
def noHam3 : Fin 3 → Fin 3 → Bool :=
  ![![false, true, true], ![false, false, false], ![false, false, false]]

/-- Word-RAM instance for `noHam3`. -/
abbrev noHam3Inst : Instance := ⟨3, noHam3⟩

example : countHamPaths noHam3 = 0 := by decide +kernel
example : decideHamPath noHam3 = false := by decide +kernel
example : ¬ (hamPaths noHam3).Nonempty := fun h => by
  have := (decideHamPath_eq_true_iff noHam3).2 h
  revert this
  decide +kernel

example : ∃ steps ≤ countTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 program (.init noHam3Inst.encode) 0 steps :=
  executes_count noHam3Inst 12 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 decideProgram (.init noHam3Inst.encode) 0 steps :=
  executes_decide noHam3Inst 12 (by decide +kernel) (by
    have hne : ¬ (hamPaths noHam3).Nonempty := fun h => by
      have := (decideHamPath_eq_true_iff noHam3).2 h
      revert this
      decide +kernel
    simp [hne])

/-! ### 3. Complete loopless directed graphs `K₃` and `K₄` -/

/-- Complete loopless directed graph on `Fin n`: an arc between every pair of distinct vertices. -/
def completeDigraph (n : ℕ) (u v : Fin n) : Bool := u != v

/-- Word-RAM instance for `K₃`. -/
abbrev k3Inst : Instance := ⟨3, completeDigraph 3⟩

example : countHamPaths (completeDigraph 3) = 6 := by decide +kernel
example : (hamPaths (completeDigraph 3)).card = 6 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel
example : ∃ steps ≤ countTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 program (.init k3Inst.encode) 6 steps :=
  executes_count k3Inst 12 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((3 ^ 3 + 1) * 2 ^ 3),
    Executes 12 decideProgram (.init k3Inst.encode) 1 steps :=
  executes_decide k3Inst 12 (by decide +kernel) (by
    have hne : (hamPaths (completeDigraph 3)).Nonempty :=
      (decideHamPath_eq_true_iff (completeDigraph 3)).1 (by decide +kernel)
    simp [hne])

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

/-- Word-RAM instance for `diamond4`. -/
abbrev diamond4Inst : Instance := ⟨4, diamond4⟩

example : countHamPaths diamond4 = 2 := by decide +kernel
example : (hamPaths diamond4).card = 2 := by
  rw [card_hamPaths_eq_toNat_countHamPaths]
  decide +kernel
example : decideHamPath diamond4 = true := by decide +kernel
example : ∃ steps ≤ countTimeFactor * ((4 ^ 3 + 1) * 2 ^ 4),
    Executes 16 program (.init diamond4Inst.encode) 2 steps :=
  executes_count diamond4Inst 16 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((4 ^ 3 + 1) * 2 ^ 4),
    Executes 16 decideProgram (.init diamond4Inst.encode) 1 steps :=
  executes_decide diamond4Inst 16 (by decide +kernel) (by
    have hne : (hamPaths diamond4).Nonempty :=
      (decideHamPath_eq_true_iff diamond4).1 (by decide +kernel)
    simp [hne])

/-! ### 5. Edge cases (`n = 0` and `n = 1`) -/

/-- Empty digraph on `0` vertices. -/
abbrev empty0Inst : Instance := ⟨0, fun _ _ => false⟩

/-- Loopless digraph on `1` vertex. -/
abbrev one1Inst : Instance := ⟨1, fun _ _ => false⟩

/-- Digraph on `1` vertex with a self-loop. -/
abbrev oneLoopInst : Instance := ⟨1, fun _ _ => true⟩

example : countHamPaths (n := 0) (fun _ _ => false) = 1 := by decide +kernel
example : countHamPaths (n := 1) (fun _ _ => false) = 1 := by decide +kernel
example : countHamPaths (n := 1) (fun _ _ => true) = 1 := by decide +kernel

example : ∃ steps ≤ countTimeFactor * ((0 ^ 3 + 1) * 2 ^ 0),
    Executes 7 program (.init empty0Inst.encode) 1 steps :=
  executes_count empty0Inst 7 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((0 ^ 3 + 1) * 2 ^ 0),
    Executes 7 decideProgram (.init empty0Inst.encode) 1 steps :=
  executes_decide empty0Inst 7 (by decide +kernel) (by
    have hne : (hamPaths empty0Inst.adj).Nonempty :=
      (decideHamPath_eq_true_iff empty0Inst.adj).1 (by decide +kernel)
    simp [hne])

example : ∃ steps ≤ countTimeFactor * ((1 ^ 3 + 1) * 2 ^ 1),
    Executes 7 program (.init one1Inst.encode) 1 steps :=
  executes_count one1Inst 7 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((1 ^ 3 + 1) * 2 ^ 1),
    Executes 7 decideProgram (.init one1Inst.encode) 1 steps :=
  executes_decide one1Inst 7 (by decide +kernel) (by
    have hne : (hamPaths one1Inst.adj).Nonempty :=
      (decideHamPath_eq_true_iff one1Inst.adj).1 (by decide +kernel)
    simp [hne])

example : ∃ steps ≤ countTimeFactor * ((1 ^ 3 + 1) * 2 ^ 1),
    Executes 7 program (.init oneLoopInst.encode) 1 steps :=
  executes_count oneLoopInst 7 (by decide +kernel)
    (by rw [card_hamPaths_eq_toNat_countHamPaths]; decide +kernel)
example : ∃ steps ≤ decideTimeFactor * ((1 ^ 3 + 1) * 2 ^ 1),
    Executes 7 decideProgram (.init oneLoopInst.encode) 1 steps :=
  executes_decide oneLoopInst 7 (by decide +kernel) (by
    have hne : (hamPaths oneLoopInst.adj).Nonempty :=
      (decideHamPath_eq_true_iff oneLoopInst.adj).1 (by decide +kernel)
    simp [hne])

end CslibFrontierTests.HamiltonianCount
