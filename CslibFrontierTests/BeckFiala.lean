/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Combinatorics.SetFamily.BeckFiala
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Regression, module-encapsulation, and boundary witnesses for
`Cslib.Combinatorics.beckFiala` and `Cslib.Combinatorics.beckFiala_rounding`. -/

set_option linter.privateModule false

open Cslib.Combinatorics Finset

-- Boundary case `t = 0`: every set must be empty and the discrepancy bound `2 * 0 - 1 = 0` holds.
example :
    ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : Fin 2, (∑ v ∈ (fun _ : Fin 2 => (∅ : Finset (Fin 3))) i, χ v).natAbs ≤ 0 :=
  beckFiala (fun _ : Fin 2 => (∅ : Finset (Fin 3))) (t := 0) (fun _ => by simp)

-- Tightness at `t = 1`: a singleton family achieves discrepancy `1 = 2 * 1 - 1` under every
-- coloring.
example :
    (∀ χ : Fin 1 → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) →
      (∑ v ∈ ({0} : Finset (Fin 1)), χ v).natAbs = 1) ∧
    (∃ χ : Fin 1 → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : Fin 1, (∑ v ∈ (fun _ : Fin 1 => ({0} : Finset (Fin 1))) i, χ v).natAbs ≤ 1) :=
  ⟨fun χ hχ => by
    rcases hχ 0 with h | h <;> simp [h],
   beckFiala (fun _ : Fin 1 => ({0} : Finset (Fin 1))) (t := 1)
     (fun v => by fin_cases v; decide)⟩

-- Degree-2 triangle family: Beck–Fiala guarantees discrepancy `≤ 3`, while dropping the degree
-- bound to `t = 1` fails cleanly (every ±1 coloring hits `2 > 1`).
private def triSets : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {2, 0}

example :
    ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : Fin 3, (∑ v ∈ triSets i, χ v).natAbs ≤ 3 :=
  beckFiala triSets (t := 2) (fun v => by fin_cases v <;> decide)

example :
    ¬ ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : Fin 3, (∑ v ∈ triSets i, χ v).natAbs ≤ 1 := by
  rintro ⟨χ, hχ, hbound⟩
  have h0 : (χ 0 + χ 1).natAbs ≤ 1 := by
    simpa [triSets, Finset.sum_insert, Finset.sum_singleton] using hbound 0
  have h1 : (χ 1 + χ 2).natAbs ≤ 1 := by
    simpa [triSets, Finset.sum_insert, Finset.sum_singleton] using hbound 1
  have h2 : (χ 2 + χ 0).natAbs ≤ 1 := by
    simpa [triSets, Finset.sum_insert, Finset.sum_singleton] using hbound 2
  rcases hχ 0 with c0 | c0 <;> rcases hχ 1 with c1 | c1 <;> rcases hχ 2 with c2 | c2 <;>
    simp [c0, c1, c2] at h0 h1 h2

-- Infinite ground type `κ = ℕ` (no `[Fintype κ]` needed) and repeated sets in the family.
example :
    ∃ χ : ℕ → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : Fin 2, (∑ v ∈ (fun _ : Fin 2 => ({0, 1, 2} : Finset ℕ)) i, χ v).natAbs ≤ 3 :=
  beckFiala (fun _ : Fin 2 => ({0, 1, 2} : Finset ℕ)) (t := 2)
    (fun _ => (Finset.card_filter_le _ _).trans (by decide))

private def triWeight : Fin 3 → ℚ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1

-- Fractional rounding over `ℚ` preserves exact `0`/`1` coordinates and achieves `< t`.
example :
    ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 0 ∨ χ v = 1) ∧ χ 0 = 0 ∧ χ 2 = 1 ∧
      ∀ i : Fin 3, |∑ v ∈ triSets i, ((χ v : ℚ) - triWeight v)| < 2 := by
  obtain ⟨χ, hχ, h0, h1, hb⟩ := beckFiala_rounding triSets (t := 2) (by decide)
    (fun v => by fin_cases v <;> decide) triWeight
    (fun v => by fin_cases v <;> norm_num [triWeight])
    (fun v => by fin_cases v <;> norm_num [triWeight])
  exact ⟨χ, hχ, h0 0 rfl, h1 2 rfl, hb⟩

private noncomputable def triWeightReal : Fin 3 → ℝ
  | 0 => 0
  | 1 => Real.sqrt 2 - 1
  | 2 => 1

-- Fractional rounding over `ℝ` rounds irrational weights while fixing `0`/`1` coordinates.
example :
    ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 0 ∨ χ v = 1) ∧ χ 0 = 0 ∧ χ 2 = 1 ∧
      ∀ i : Fin 3, |∑ v ∈ triSets i, ((χ v : ℝ) - triWeightReal v)| < 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by simp
  have h2 : Real.sqrt 2 ≤ 2 := by simp
  obtain ⟨χ, hχ, h0, h1', hb⟩ := beckFiala_rounding triSets (t := 2) (by decide)
    (fun v => by fin_cases v <;> decide) triWeightReal
    (fun v => by fin_cases v <;> dsimp only [triWeightReal] <;> linarith)
    (fun v => by fin_cases v <;> dsimp only [triWeightReal] <;> linarith)
  exact ⟨χ, hχ, h0 0 rfl, h1' 2 rfl, hb⟩

-- Generic linearly ordered field usability under `module` encapsulation.
example {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (x : Fin 3 → 𝕜) (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∀ v, x v ≤ 1)
    (h0eq : x 0 = 0) (h2eq : x 2 = 1) :
    ∃ χ : Fin 3 → ℤ, (∀ v, χ v = 0 ∨ χ v = 1) ∧ χ 0 = 0 ∧ χ 2 = 1 ∧
      ∀ i : Fin 3, |∑ v ∈ triSets i, ((χ v : 𝕜) - x v)| < 2 := by
  obtain ⟨χ, hχ, h0, h1, hb⟩ := beckFiala_rounding triSets (t := 2) (by decide)
    (fun v => by fin_cases v <;> decide) x hx0 hx1
  exact ⟨χ, hχ, h0 0 h0eq, h1 2 h2eq, hb⟩
