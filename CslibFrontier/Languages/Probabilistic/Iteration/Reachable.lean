/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# Finite enclosures for a bounded probabilistic loop

A list of successors for each state gives a finite enclosure of the states that a bounded
iteration can reach. If it contains every supported one-step result under a stateful oracle,
the iterated enclosure contains every supported final result under the same oracle. Different
iterations may change the oracle state. The state space and the oracle replies can be infinite.
-/

public section

namespace Cslib.ProbOracleComp

universe u v s

variable {α : Type v}

/-- Enumerate an enclosure of the states after exactly `n` steps. -/
@[expose] def reachableIn (next : α → List α) (initial : α) (n : ℕ) : List α :=
  (List.flatMap next)^[n] [initial]

/-- Extending a path by one arbitrarily selected successor stays in the next enclosure. -/
theorem mem_reachableIn_succ {next : α → List α} {initial middle final : α} {n : ℕ}
    (hmiddle : middle ∈ reachableIn next initial n) (hfinal : final ∈ next middle) :
    final ∈ reachableIn next initial (n + 1) := by
  rw [reachableIn, Function.iterate_succ_apply']
  exact List.mem_flatMap.mpr ⟨middle, hmiddle, hfinal⟩

/-- Enclose the states that occur at any iteration from zero through `n`, inclusively. -/
def reachableThrough (next : α → List α) (initial : α) (n : ℕ) : List α :=
  (List.range (n + 1)).flatMap (reachableIn next initial)

/-- The enclosure through `n` contains every member of an enclosure at an earlier iteration. -/
theorem mem_reachableThrough {next : α → List α} {initial current : α} {i n : ℕ}
    (hi : i ≤ n) (hcurrent : current ∈ reachableIn next initial i) :
    current ∈ reachableThrough next initial n :=
  List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega), hcurrent⟩

/-- A one-step enclosure for all reachable oracle states encloses every supported loop result. -/
theorem mem_reachableIn_of_runWith_iterate {α : Type} {Q : Type u} {spec : Q → Type}
    {σ : Type s} (step : α → ProbOracleComp spec α)
    (next : α → List α) (oracle : (q : Q) → σ → PMF (spec q × σ))
    (hstep : ∀ a b s t, (b, t) ∈ (runWith oracle (step a) s).support → b ∈ next a)
    (initial : α) (n : ℕ) (s : σ) {final : α} {t : σ}
    (hfinal : (final, t) ∈ (runWith oracle (OracleComp.iterate n step initial) s).support) :
    final ∈ reachableIn next initial n := by
  induction n generalizing final t with
  | zero =>
      simp only [OracleComp.iterate_zero, runWith_pure, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at hfinal
      exact List.mem_singleton.mpr hfinal.1
  | succ n ih =>
      rw [OracleComp.iterate_succ, runWith_bind] at hfinal
      obtain ⟨⟨middle, state⟩, hmiddle, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
      exact mem_reachableIn_succ (ih hmiddle) (hstep middle final state t hfinal)

end Cslib.ProbOracleComp
