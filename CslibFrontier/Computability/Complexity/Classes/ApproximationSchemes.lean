/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-!
# Polynomial-time approximation schemes

An `NPOptimizationProblem` has typed instances and solutions, polynomially bounded feasible
solutions, and polynomial-time feasibility and objective evaluation. Its instance type
supplies the valid inputs. The feasibility certificate starts with a typed instance and
candidate solution. [Kann, Definition 1][Kann2000NPOCompendium] additionally requires
recognizing valid encoded instances in polynomial time. The typed model permits zero
objective values and requires a feasible solution for every instance.

We use [Williamson and Shmoys, Definitions 3.3–3.4][WilliamsonShmoys2011]. A solution at
accuracy `1 / k` for positive integer `k` is within the factor `1 + 1 / k` for minimization,
or achieves at least the fraction `1 - 1 / k` for maximization. Comparing with every
feasible solution avoids division and also covers zero-valued optima. Reciprocal integer
accuracies suffice since for any positive error one can choose a reciprocal no larger
than that error. A `PTAS` supplies a polynomial-time solver for each fixed accuracy.
An `FPTAS` supplies one polynomial-time solver on the instance paired with unary `k`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The direction of an optimization objective. -/
inductive OptimizationGoal
  /-- Minimize the objective value. -/
  | minimize
  /-- Maximize the objective value. -/
  | maximize

/-- A typed NP optimization problem with natural-valued objective. -/
structure NPOptimizationProblem {α β : Type} (encI : α ↪ List Bool) (encS : β ↪ List Bool) where
  /-- Whether a solution is feasible for an instance. -/
  Feasible : α → β → Prop
  /-- Every instance has a feasible solution. -/
  exists_feasible : ∀ a, ∃ b, Feasible a b
  /-- Feasibility can be checked in polynomial time. -/
  feasible_mem_P : {ab : α × β | Feasible ab.1 ab.2} ∈ P (encPair encI encS)
  /-- All feasible solutions have polynomially bounded encoded length. -/
  solution_length_bound : ∃ p : Polynomial ℕ, ∀ a b, Feasible a b →
    (encS b).length ≤ p.eval (encI a).length
  /-- The objective value of a candidate solution. -/
  value : α × β → ℕ
  /-- Evaluating the objective takes polynomial time. -/
  computableInPolyTime_value : ComputableInPolyTime value (encPair encI encS) encNat
  /-- The direction of optimization. -/
  goal : OptimizationGoal

namespace NPOptimizationProblem

variable {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
  (problem : NPOptimizationProblem encI encS)

/-- The solution is feasible and satisfies the multiplicative error guarantee at accuracy
`1 / k`. The approximation schemes use this predicate only for positive `k`. -/
@[expose] def IsApproximate (k : ℕ) (a : α) (b : β) : Prop :=
  problem.Feasible a b ∧ ∀ other, problem.Feasible a other →
    match problem.goal with
    | .minimize => k * problem.value (a, b) ≤ (k + 1) * problem.value (a, other)
    | .maximize => (k - 1) * problem.value (a, other) ≤ k * problem.value (a, b)

/-- A polynomial-time approximation scheme with a separate solver for each fixed accuracy. -/
@[expose] def PTAS : Prop :=
  ∀ k : ℕ, 0 < k → ∃ solve : α → β, ComputableInPolyTime solve encI encS ∧
    ∀ a, problem.IsApproximate k a (solve a)

/-- A fully polynomial-time approximation scheme with one solver polynomial in the instance
length and the unary inverse accuracy. -/
@[expose] def FPTAS : Prop :=
  ∃ solve : ℕ × α → β, ComputableInPolyTime solve (encPair encUnary encI) encS ∧
    ∀ k : ℕ, 0 < k → ∀ a, problem.IsApproximate k a (solve (k, a))

/-- Fixing the unary accuracy gives a polynomial-time solver for that accuracy. -/
theorem FPTAS.toPTAS (h : problem.FPTAS) : problem.PTAS := by
  obtain ⟨solve, hsolve, hcorrect⟩ := h
  intro k hk
  refine ⟨fun a => solve (k, a), ?_, hcorrect k hk⟩
  exact hsolve.comp (ComputableInPolyTime.pair (enc₁ := encUnary) (ComputableInPolyTime.const k)
    ComputableInPolyTime.id')

end NPOptimizationProblem

end Cslib.Complexity
