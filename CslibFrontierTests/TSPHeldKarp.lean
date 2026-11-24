/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.HeldKarp
public import CslibFrontier.Computability.Complexity.Problems.TSP.HeldKarp
import Mathlib.Data.Fin.VecNotation

/-!
# Worked Bellman–Held–Karp examples

These kernel-checked examples (using `decide`, never `native_decide`) exercise
`Cslib.Algorithms.Lean.TSP.heldKarp`, its Word-RAM realization
`Cslib.Algorithms.WordRAM.HeldKarp`, and its multi-tape Turing-machine `TSP`/`HamCycle` deciders:

1. An asymmetric instance on three cities with optimal tour `0 → 1 → 2 → 0` of cost `3`, whose
   reverse costs `15`, and its Word-RAM execution within `80 · (2² · 2² + 1)` instructions at word
   width `w = 5`.
2. The four-city instance with optimum `21`, checked against brute force over all `3!` orderings,
   and its Word-RAM execution within `80 · (3² · 2³ + 1)` instructions at word width `w = 6`.
3. Integer costs, including negative ones: `W` need not be `ℕ`.
4. Edge cases: one city (`n = 0`) costs its self-loop in pure Lean and Word-RAM (`w = 3`), and the
   empty `TSP` instance is accepted.
5. The `TSP` and `HamCycle` deciders on concrete inputs, together with their `DecidableInExpTime`
   multi-tape Turing-machine certificates.
-/

public section

namespace CslibFrontierTests.TSPHeldKarp

open Cslib.Algorithms.Lean.TSP Cslib.Complexity
open Cslib.Algorithms.WordRAM.HeldKarp (Instance program executes_program)

/-! ### 1. An asymmetric three-city instance -/

/-- Going around `0 → 1 → 2 → 0` costs `1` per step; the other direction costs `5` per step. -/
def d3 : Fin 3 → Fin 3 → ℕ := ![![0, 1, 5], ![5, 0, 1], ![1, 5, 0]]

example : heldKarp d3 = 3 := by decide
example : walkCost d3 0 [1, 2] 0 = 3 := by decide
example : walkCost d3 0 [2, 1] 0 = 15 := by decide

/-- Word-RAM execution witness on `d3` at tight fitting word width `w = 5`. -/
def inst3 : Instance := ⟨2, d3⟩

example : inst3.FitsWidth 5 := ⟨by decide, by decide⟩
example : ∃ m ≤ 80 * (2 ^ 2 * 2 ^ 2 + 1),
    Cslib.WordRAM.Executes 5 program (.init inst3.encode) 3 m := by
  simpa [inst3, show heldKarp d3 = 3 from by decide] using
    executes_program (I := inst3) (w := 5) ⟨by decide, by decide⟩

/-! ### 2. A four-city instance against brute force -/

/-- An asymmetric four-city cost matrix with optimal tour `0 → 2 → 3 → 1 → 0` of cost `21`. -/
def d4 : Fin 4 → Fin 4 → ℕ := ![![0, 2, 9, 10], ![1, 0, 6, 4], ![15, 7, 0, 8], ![6, 3, 12, 0]]

example : heldKarp d4 = 21 := by decide
example : walkCost d4 0 [2, 3, 1] 0 = 21 := by decide

/-- Brute force: the costs of all `3!` orderings of the cities `1, 2, 3` (kernel reduction does
not unfold `List.permutations`, so they are listed explicitly). -/
example :
    ([[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] : List (List (Fin 3))).map
      (fun L => walkCost d4 0 (L.map Fin.succ) 0) = [22, 33, 26, 21, 34, 30] := by decide

/-- Word-RAM execution witness on `d4` at tight fitting word width `w = 6`. -/
def inst4 : Instance := ⟨3, d4⟩

example : inst4.FitsWidth 6 := ⟨by decide, by decide⟩
example : ∃ m ≤ 80 * (3 ^ 2 * 2 ^ 3 + 1),
    Cslib.WordRAM.Executes 6 program (.init inst4.encode) 21 m := by
  simpa [inst4, show heldKarp d4 = 21 from by decide] using
    executes_program (I := inst4) (w := 6) ⟨by decide, by decide⟩

/-! ### 3. Integer costs -/

/-- A cost matrix with negative entries; the optimal tour `0 → 2 → 1 → 0` costs `-6`. -/
def dZ : Fin 3 → Fin 3 → ℤ := ![![0, 4, -2], ![-3, 0, 1], ![2, -1, 0]]

example : heldKarp dZ = -6 := by decide
example : walkCost dZ 0 [1, 2] 0 = 7 := by decide

/-! ### 4. Edge cases -/

/-- One city: the only tour is the self-loop, in both pure Lean and Word-RAM (`w = 3`). -/
example : heldKarp (n := 0) (fun _ _ => (7 : ℕ)) = 7 := by decide

def inst1 : Instance := ⟨0, fun _ _ => 7⟩

example : inst1.FitsWidth 3 := ⟨by decide, by decide⟩
example : ∃ m ≤ 80,
    Cslib.WordRAM.Executes 3 program (.init inst1.encode) 7 m := by
  simpa [inst1, show heldKarp (n := 0) (fun _ _ => (7 : ℕ)) = 7 from by decide] using
    executes_program (I := inst1) (w := 3) ⟨by decide, by decide⟩

/-- The empty instance has the empty tour of length `0`. -/
example : TSP.heldKarpDecide ⟨[], 0⟩ = true := by decide
example : (⟨[], 0⟩ : TSPInstance) ∈ TSP :=
  (TSP.heldKarpDecide_eq_true_iff _).1 (by decide)

/-! ### 5. Deciding `TSP` and `HamCycle` -/

/-- The three-city instance of §1 as a distance matrix: budget `3` suffices, budget `2` does not. -/
def D3 : List (List ℕ) := [[0, 1, 5], [5, 0, 1], [1, 5, 0]]

example : (⟨D3, 3⟩ : TSPInstance) ∈ TSP := (TSP.heldKarpDecide_eq_true_iff _).1 (by decide)
example : (⟨D3, 2⟩ : TSPInstance) ∉ TSP := fun h => by
  have := (TSP.heldKarpDecide_eq_true_iff _).2 h
  revert this
  decide

/-- A triangle has a Hamiltonian cycle. -/
example : (⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩ : Graph) ∈ HamCycle :=
  (HamCycle.heldKarpDecide_toTSP_eq_true_iff _).1 (by decide)

/-- A path on three vertices has none. -/
example : (⟨[0, 1, 2], [(0, 1), (1, 2)]⟩ : Graph) ∉ HamCycle := fun h => by
  have := (HamCycle.heldKarpDecide_toTSP_eq_true_iff _).2 h
  revert this
  decide

/-- Multi-tape Turing-machine exponential-time decidability certificates for `TSP` and
`HamCycle`. -/
example : DecidableInExpTime TSP encTSP (fun x => x.dist.length - 1) 1 :=
  TSP.decidableInExpTime

example : DecidableInExpTime HamCycle encGraph (fun G => G.distinctVertices.length - 1) 1 :=
  HamCycle.decidableInExpTime

end CslibFrontierTests.TSPHeldKarp
