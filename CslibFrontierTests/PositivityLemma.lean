/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the positivity_lemma attribute)

public import CslibFrontier.Tactic.PositivityLemma
public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyRankEnvironment
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Tests for `@[positivity_lemma]`

The sign lemmas the library registers are used by `positivity`, and through it by the side goals of
`gcongr` and `grw` and by `field_simp`. The attribute rejects a statement that is not a sign
statement, a lemma with a hypothesis, and a lemma about a variable.
-/

public section

namespace CslibFrontierTests.PositivityLemma

open Cslib Matrix Matrix.HierarchyParams.H4RankEnvironment

/-! ### Lemmas the library registers -/

/-- `rate_pos`, under the operations `positivity` knows. -/
example (k : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 < (rate k + x) / rate k ^ 2 := by positivity

/-- The sign tree `mul_nonneg (Nat.cast_nonneg _) (rate_pos k).le`. -/
example (P k : ℕ) : 0 ≤ (P : ℝ) * rate k := by positivity

/-- `0 < e` also gives `e ≠ 0`. -/
example (k : ℕ) : rate k ≠ 0 := by positivity

example (k : ℕ) (a b : ℝ) (h : a ≤ b) : rate k * a ≤ rate k * b := by gcongr

example (k : ℕ) (a b : ℝ) (h : a ≤ b) : rate k ^ 2 * a ≤ rate k ^ 2 * b := by grw [h]

example (k : ℕ) (x : ℝ) : x / rate k * rate k = x := by field_simp

/-- `RotationMap.spectralExpansion_nonneg`: a lemma about a structure with instance arguments,
all determined by the expression. -/
example {V D : Type*} [DecidableEq V] [Fintype V] [Fintype D] (G : RotationMap V D) (t : ℕ)
    {c x : ℝ} (hG : G.spectralExpansion ≤ c) (hx : 0 ≤ x) :
    G.spectralExpansion ^ t * x ≤ c ^ t * x := by gcongr

/-- Fields of `HierarchyParams`, also through the projection from an extending structure. -/
example {q cπ Cπ Cpair Cvar : ℝ} (HP : FourthRootHierarchyParams q cπ Cπ Cpair Cvar)
    (s t : ℝ) : 0 ≤ 2 * HP.Q s * HP.γ t * HP.ρ t / (HP.η * HP.θ) := by positivity

/-- A lemma concluding `0 ≤ e` does not make `positivity` claim `0 < e`. -/
example {V D : Type*} [DecidableEq V] [Fintype V] [Fintype D] (G : RotationMap V D) :
    0 < G.spectralExpansion + 1 := by
  fail_if_success (have : 0 < G.spectralExpansion := by positivity)
  positivity

/-- A registered `0 ≤ e` does not hide a stronger hypothesis about `e`. -/
example {V D : Type*} [DecidableEq V] [Fintype V] [Fintype D] (G : RotationMap V D)
    (h : 0 < G.spectralExpansion) : 0 < 2 * G.spectralExpansion := by positivity

/-! ### Rejected registrations -/

/-- A quantity that is positive only on nonnegative arguments. -/
noncomputable def shifted (x : ℝ) : ℝ := x / 2 + 1

theorem shifted_le (x : ℝ) : shifted x ≤ x + 1 ∨ x < 0 := by
  unfold shifted
  rcases le_or_gt 0 x with h | h
  · exact .inl (by linarith)
  · exact .inr h

/--
error: `@[positivity_lemma]` needs a lemma concluding `0 < e` or `0 ≤ e`, but shifted_le concludes
  shifted x ≤ x + 1 ∨ x < 0
-/
#guard_msgs in
attribute [positivity_lemma] shifted_le

theorem shifted_pos {x : ℝ} (hx : 0 ≤ x) : 0 < shifted x := by
  unfold shifted
  positivity

/--
error: `@[positivity_lemma]`: the argument of shifted_pos of type
  0 ≤ x
is not determined by
  shifted x
-/
#guard_msgs in
attribute [positivity_lemma] shifted_pos

theorem nnreal_nonneg (x : NNReal) : 0 ≤ x := x.2

/--
error: `@[positivity_lemma]`: nnreal_nonneg states the sign of a variable, which `positivity` would have to try on every expression
-/
#guard_msgs in
attribute [positivity_lemma] nnreal_nonneg

end CslibFrontierTests.PositivityLemma
