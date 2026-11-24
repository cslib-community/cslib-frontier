/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.FineGrained.CliqueGrouping

/-! # Clause-grouping reduction from 3-SAT to Clique tests

Kernel-checked tests (with no `native_decide`) exercising `Cslib.Complexity.SAT.groupClique`:

1. Satisfiable 2-clause 3-CNF `[(0 ∨ ¬1), (¬0 ∨ 2)]` grouped into `r = 2` blocks (`bound = 8`),
   checking exact output target `2`, vertex-count bound `≤ 16`, membership in `Clique` via a
   concrete `Finset` clique witness and `groupClique_mem_Clique_iff`.
2. Unsatisfiable 2-clause formula `[(0), (¬0)]` grouped into `r = 2` blocks: zero cross-block
   edges are produced (`edges = []`), so `groupClique 2 unsat2 ∉ Clique` and `unsat2 ∉ ThreeSAT`.
3. Boundary inputs (`[]`, `[[]]`, a width-4 clause `non3CNF`, and `r = 0`), verifying
   `groupClique_snd`, `length_groupClique_vertices_le`, and `groupClique_mem_Clique_iff`.
-/

public section

namespace Cslib.Complexity.Tests.CliqueGrouping

open Cslib.Logic.PL Cslib.Complexity

/-- Satisfiable 2-clause formula with shared variable `0`. -/
@[expose] def sat2 : CNF ℕ :=
  [[(0, true), (1, false)], [(0, false), (2, true)]]

/-- Unsatisfiable 2-clause formula forcing contradicting values for variable `0`. -/
@[expose] def unsat2 : CNF ℕ :=
  [[(0, true)], [(0, false)]]

/-- Width-4 formula outside `ThreeSAT`. -/
@[expose] def non3CNF : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true)]]

example : (SAT.groupClique 2 sat2).m = 2 := by decide
example : (SAT.groupClique 2 sat2).graph.vertices.length ≤ 16 :=
  SAT.length_groupClique_vertices_le 2 sat2
example : (SAT.groupClique 2 sat2).graph.vertices.toFinset.card ≤ 16 :=
  SAT.card_groupClique_vertices_le 2 sat2

/-- Witness `τ = (fun _ => true)` satisfies `sat2`, so `SAT.groupClique 2 sat2 ∈ Clique`. -/
example : SAT.groupClique 2 sat2 ∈ Clique :=
  (SAT.groupClique_mem_Clique_iff (by decide : 1 ≤ 2) sat2).mpr
    ⟨by decide, fun _ => true, by decide⟩

/-- Conflicting unit clauses produce no edges between block `0` and block `1`. -/
example : (SAT.groupClique 2 unsat2).graph.edges = [] := by decide

example : SAT.groupClique 2 unsat2 ∉ Clique := by
  rw [SAT.groupClique_mem_Clique_iff (by decide : 1 ≤ 2) unsat2]
  rintro ⟨_, τ, hτ⟩
  simp [unsat2, CNF.eval, Clause.eval, Literal.eval] at hτ

/-- Boundary cases: empty CNF `[]`, empty clause `[[]]`, non-3-CNF, and `r = 0`. -/
example : SAT.groupClique 2 ([] : CNF ℕ) ∈ Clique :=
  (SAT.groupClique_mem_Clique_iff (by decide : 1 ≤ 2) []).mpr
    ⟨by decide, fun _ => false, by decide⟩

example : SAT.groupClique 2 ([[]] : CNF ℕ) ∉ Clique := by
  rw [SAT.groupClique_mem_Clique_iff (by decide : 1 ≤ 2) [[]]]
  rintro ⟨_, τ, hτ⟩
  simp [CNF.eval, Clause.eval] at hτ

example : SAT.groupClique 2 non3CNF = ⟨⟨[], []⟩, 2⟩ := by decide
example : SAT.groupClique 2 non3CNF ∉ Clique := by
  rw [SAT.groupClique_mem_Clique_iff (by decide : 1 ≤ 2) non3CNF]
  rintro ⟨h3, _⟩
  exact absurd (h3 [(0, true), (1, true), (2, true), (3, true)] (by simp [non3CNF])) (by decide)

example : SAT.groupClique 0 sat2 = ⟨⟨[], []⟩, 1⟩ := by decide

end Cslib.Complexity.Tests.CliqueGrouping
