/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.MaxCSP.UpperBounds

/-! Checked clients of the upper bounds for gap 2CSP. They cover Goldreich's `gapCSP^{0,1}_τ`
with an arbitrary threshold function `τ` (Exercise 9.24) and the constant-gap promise class
`PCP(log n, 1)` (Exercise 9.25). A decision problem is in the promise PCP class exactly when it is
in `PCP`. Both sides of the Exercise 9.25 promise problem are inhabited by well-formed graphs. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GapTwoCSPUpperBounds

open Cslib Cslib.Complexity Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- Goldreich's `gapCSP^{0,1}_τ` for an arbitrary threshold `τ` on the number of edges. The
yes-instances have `vlt = 0`. The no-instances have `vlt ≥ τ(|E|)` and `0 < τ(|E|)`. -/
example (τ : ℕ → ℝ) :
    PromiseProblem.gapMin (fun g : Graph (Bool → Bool → Bool) => (g.toGraph id).unsatVal)
        (fun _ => 0) (fun g => τ g.edges.length) ∈
      PromiseP (Graph.encoding encConstraintTable) := by
  refine mem_PromiseP_of_satisfiable_bool (fun g hg => ?_) (fun g hg hsat => ?_)
  · exact (g.toGraph id).unsatVal_eq_zero_iff.1 (le_antisymm hg (g.toGraph id).unsatVal_nonneg)
  · have h := (g.toGraph id).unsatVal_eq_zero_iff.2 hsat
    obtain ⟨hτ, hpos⟩ := hg
    linarith

/-- In contrast with `GapTwoCSP_notMem_PromiseP` over `128` symbols, every soundness level is
tractable over Boolean labels. -/
example (s : ℝ) : GapTwoCSP Bool s ∈ PromiseP (Graph.encoding encConstraintTable) := by
  refine mem_PromiseP_of_satisfiable_bool (fun g hg => mem_yes_GapTwoCSP.1 hg)
    (fun g hg hsat => ?_)
  have h := (g.toGraph id).unsatVal_eq_zero_iff.2 hsat
  obtain ⟨hv, hs⟩ := hg
  simp only [h] at hv
  linarith

example : (GapTwoCSP Bool (1 - 1 / 2)).restrict {g | g.WellFormed} ∈
    PromisePCP (fun n => Nat.log 2 n + 1) (fun _ => 1) (Graph.encoding encConstraintTable) :=
  GapTwoCSP_restrict_mem_PromisePCP (by norm_num)

example {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    PromiseProblem.ofSet A ∈ PromisePCP (fun n => Nat.log 2 n + 1) (fun _ => 1) enc ↔
      A ∈ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) enc :=
  ofSet_mem_PromisePCP

/-- A well-formed loop forbidding every pair of labels: every labelling violates it. -/
private def unsatGraph : Graph (Bool → Bool → Bool) := ⟨1, [⟨0, 0, fun _ _ => false⟩]⟩

example : unsatGraph ∈ ((GapTwoCSP Bool (1 - 1 / 2)).restrict {g | g.WellFormed}).no := by
  refine ⟨(mem_no_GapTwoCSP (by norm_num)).2 ?_, (Graph.isWellFormed_eq_true _).1 rfl⟩
  have h := (unsatGraph.toGraph id).inv_card_le_unsatVal fun ⟨σ, hσ⟩ => by
    simpa [ConstraintGraph.Satisfies, Graph.toGraph, unsatGraph] using hσ ⟨0, by decide⟩
  have h1 : (1 : ℝ) ≤ (unsatGraph.toGraph id).unsatVal := by simpa [unsatGraph] using h
  linarith

example : (⟨1, [⟨0, 0, fun a b => a == b⟩]⟩ : Graph (Bool → Bool → Bool)) ∈
    ((GapTwoCSP Bool (1 - 1 / 2)).restrict {g | g.WellFormed}).yes :=
  ⟨mem_yes_GapTwoCSP.2 ⟨fun _ => true, fun i => by
    simp [ConstraintGraph.Satisfies, Graph.toGraph]⟩, (Graph.isWellFormed_eq_true _).1 rfl⟩

end CslibFrontierTests.GapTwoCSPUpperBounds
