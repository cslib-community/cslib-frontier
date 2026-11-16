/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import CslibFrontier.Languages.Probabilistic.QueriesWith.Cost

/-!
# Tests for `List.findSomeM?` oracle rules and `QueriesWith.Cost`

Exercises `OracleComp.evalPure_findSomeM?`, `OracleComp.IsCostBounded.findSomeM?`,
`OracleComp.IsCostBounded.sum_map_queriesWith_le`, `OracleComp.queriesWith_liftLeft`,
`OracleComp.queriesWith_findSomeM?_cons`, and `OracleComp.queriesWith_findSomeM?_of_forall_eq_none`
under `module` encapsulation, including attainment and failing cases.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.OracleFindSomeM

open Cslib

/-- One oracle step: query at `x` and keep `some (2 * reply)` when `0 < reply`. -/
private def probe (x : ℕ) : OracleComp (fun _ : ℕ => ℕ) (Option ℕ) :=
  (fun y => if 0 < y then some (2 * y) else none) <$>
    OracleComp.query (spec := fun _ : ℕ => ℕ) x

/-- Against any pure oracle, `probe x` issues the single query `[x]`. -/
private theorem queriesWith_probe (o : ℕ → ℕ) (x : ℕ) :
    OracleComp.queriesWith o (probe x) = [x] := by
  simp only [probe, OracleComp.queriesWith_map, OracleComp.queriesWith_query]

/-- First kept answer: returns the doubled reply for the first candidate with `0 < reply`. -/
example : OracleComp.evalPure (fun n => if 3 ≤ n then n + 10 else 0)
    ([1, 2, 3, 4].findSomeM? probe) = some 26 := by
  rw [OracleComp.evalPure_findSomeM?]
  decide

/-- No kept answer: returns `none` when every step returns `none`. -/
example : OracleComp.evalPure (fun _ => 0) ([1, 2].findSomeM? probe) = none := by
  rw [OracleComp.evalPure_findSomeM?]
  decide

/-- Empty list: returns `none` and satisfies the zero cost budget. -/
example (h : ℕ → ℕ) :
    OracleComp.evalPure h (([] : List ℕ).findSomeM? probe) = none ∧
      OracleComp.IsQueryBounded (([] : List ℕ).findSomeM? probe) 0 :=
  ⟨by rw [OracleComp.evalPure_findSomeM?]; rfl,
    OracleComp.IsCostBounded.findSomeM? (n := 0) fun _ ha => by cases ha⟩

/-- One call per candidate: `probe` costs `1`, so searching `xs` stays within `xs.length`. -/
example (xs : List ℕ) :
    OracleComp.IsQueryBounded (xs.findSomeM? probe) xs.length := by
  have h := OracleComp.IsCostBounded.findSomeM? (cost := fun _ : ℕ => 1) (f := probe)
    (n := 1) (xs := xs) fun x _ =>
      (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query x)
  rwa [Nat.mul_one] at h

/-- Against the zero oracle, `probe` always returns `none` and `findSomeM? probe` queries every
element of `xs` in order. -/
private theorem queriesWith_probe_zero (xs : List ℕ) :
    OracleComp.queriesWith (fun _ => 0) (xs.findSomeM? probe) = xs := by
  rw [OracleComp.queriesWith_findSomeM?_of_forall_eq_none]
  · simp only [queriesWith_probe, List.flatMap_singleton']
  · intro x _
    simp only [probe, OracleComp.evalPure_map, OracleComp.evalPure_query]
    rfl

/-- Run that finds nothing: against the zero oracle, `queriesWith` records every query in order. -/
example :
    OracleComp.queriesWith (fun _ => 0) ([1, 2, 3].findSomeM? probe) = [1, 2, 3] :=
  queriesWith_probe_zero [1, 2, 3]

/-- Plain budget attained: searching `[0, 1]` cannot have query budget `1`, proved via
`IsCostBounded.sum_map_queriesWith_le` against an oracle returning `0`. -/
example : ¬ OracleComp.IsQueryBounded ([0, 1].findSomeM? probe) 1 := by
  intro h
  have hle := OracleComp.IsCostBounded.sum_map_queriesWith_le (fun _ => 0) h
  rw [queriesWith_probe_zero [0, 1]] at hle
  revert hle
  decide

/-- Weighted budget attained: charging `q + 1` on `[2, 2]` fits budget `2 * 3` and fails `5`. -/
example :
    OracleComp.IsCostBounded (fun q => q + 1) ([2, 2].findSomeM? probe) (2 * 3) ∧
      ¬ OracleComp.IsCostBounded (fun q => q + 1) ([2, 2].findSomeM? probe) 5 := by
  refine ⟨?_, ?_⟩
  · have hstep : ∀ x ∈ ([2, 2] : List ℕ),
        OracleComp.IsCostBounded (fun q => q + 1) (probe x) 3 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
          (OracleComp.IsCostBounded.query 2)
      · rcases List.mem_singleton.mp hx with rfl
        exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
          (OracleComp.IsCostBounded.query 2)
    exact OracleComp.IsCostBounded.findSomeM? hstep
  · intro h
    have hle := OracleComp.IsCostBounded.sum_map_queriesWith_le (fun _ => 0) h
    rw [queriesWith_probe_zero [2, 2]] at hle
    revert hle
    decide

/-- Early exit: when the first step keeps an answer, `queriesWith_findSomeM?_cons` stops after
the first query `[1]` without reaching `2` or `3`. -/
example :
    OracleComp.queriesWith (fun _ => 5) ([1, 2, 3].findSomeM? probe) = [1] := by
  rw [OracleComp.queriesWith_findSomeM?_cons, queriesWith_probe]
  have h1 : (OracleComp.evalPure (fun _ => 5) (probe 1)).isSome = true := by
    simp only [probe, OracleComp.evalPure_map, OracleComp.evalPure_query]
    decide
  rw [h1]
  simp only [↓reduceIte, List.append_nil]

/-- Failing case for "no step finds anything": when the first step returns `some`, the request
trace is strictly shorter than concatenating all steps. -/
example :
    OracleComp.queriesWith (fun n => if n = 1 then 5 else 0) ([1, 2, 3].findSomeM? probe) ≠
      ([1, 2, 3].flatMap fun x =>
        OracleComp.queriesWith (fun n => if n = 1 then 5 else 0) (probe x)) := by
  intro h
  have hleft :
      OracleComp.queriesWith (fun n => if n = 1 then 5 else 0) ([1, 2, 3].findSomeM? probe) =
        [1] := by
    rw [OracleComp.queriesWith_findSomeM?_cons, queriesWith_probe]
    have h1 : (OracleComp.evalPure (fun n => if n = 1 then 5 else 0) (probe 1)).isSome = true := by
      simp only [probe, OracleComp.evalPure_map, OracleComp.evalPure_query]
      decide
    rw [h1]
    simp only [↓reduceIte, List.append_nil]
  have hright :
      ([1, 2, 3].flatMap fun x =>
        OracleComp.queriesWith (fun n => if n = 1 then 5 else 0) (probe x)) = [1, 2, 3] := by
    simp only [queriesWith_probe]
    rfl
  rw [hleft, hright] at h
  exact absurd h (by decide)

/-- `queriesWith_liftLeft` lifts a search over the left interface into `sumPure`. -/
example (o₂ : ℕ → Bool) :
    OracleComp.queriesWith
        (OracleComp.sumPure (spec₁ := fun _ : ℕ => ℕ) (spec₂ := fun _ : ℕ => Bool)
          (fun _ => 5) o₂)
        (OracleComp.liftLeft (spec₂ := fun _ : ℕ => Bool) ([1, 2].findSomeM? probe)) =
      [Sum.inl 1] := by
  rw [OracleComp.queriesWith_liftLeft, OracleComp.queriesWith_findSomeM?_cons, queriesWith_probe]
  have h1 : (OracleComp.evalPure (fun _ => 5) (probe 1)).isSome = true := by
    simp only [probe, OracleComp.evalPure_map, OracleComp.evalPure_query]
    decide
  rw [h1]
  simp only [↓reduceIte, List.append_nil]
  rfl

end CslibFrontierTests.OracleFindSomeM
