/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the positivity_lemma attribute)

import CslibFrontier.Tactic.PositivityLemma
import CslibFrontier.Foundations.Combinatorics.Expander.Basic
import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyRankEnvironment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Tests for `@[positivity_lemma]`

The sign lemmas the library registers are used by `positivity`, and through it by the side goals of
`gcongr` and `grw` and by `field_simp`. Typeclass instances and propositional side conditions
determined by the target expression are synthesized or discharged automatically, while undetermined
data or type arguments, non-sign conclusions, and variable heads are rejected.
-/

set_option linter.privateModule false

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

/-! ### Synthesized instances and discharged side conditions -/

/-- A quantity whose positivity depends on `[NeZero P]`, which does not appear in `modScale P`. -/
private def modScale (P : ℕ) : ℝ := P

@[local positivity_lemma]
private theorem modScale_pos {P : ℕ} [NeZero P] : 0 < modScale P :=
  Nat.cast_pos.mpr (NeZero.pos P)

/-- Instance synthesis directly and through `[Fact P.Prime]`. -/
example (P : ℕ) [NeZero P] : 0 < modScale P := by positivity
example (P : ℕ) [Fact P.Prime] (x : ℝ) : x / modScale P * modScale P = x := by field_simp

/-- Soundness when the required instance is absent. -/
example (P : ℕ) : 0 ≤ modScale P ^ 2 := by
  fail_if_success (have : 0 < modScale P := by positivity)
  positivity

/-- A quantity that is positive only on nonnegative arguments. -/
private noncomputable def shifted (x : ℝ) : ℝ := x / 2 + 1

@[local positivity_lemma]
private theorem shifted_pos {x : ℝ} (hx : 0 ≤ x) : 0 < shifted x := by
  unfold shifted
  positivity

/-- Side condition discharged by `assumption`, recursive `positivity`, and nested sign lemmas. -/
example (x : ℝ) (hx : 0 ≤ x) : 0 < shifted x := by positivity
example (a : ℝ) : 0 < shifted (a ^ 2) := by positivity
example (a : ℝ) : 0 < shifted (shifted (a ^ 2)) := by positivity

/-- Soundness when the real side condition does not hold. -/
example (x : ℝ) : 0 ≤ shifted x ^ 2 := by
  fail_if_success (have : 0 < shifted x := by positivity)
  positivity

/-- A quantity whose positivity requires a linear `ℕ` comparison. -/
private noncomputable def slackGap (r H : ℕ) : ℝ := (H : ℝ) - r + 1

@[local positivity_lemma]
private theorem slackGap_pos {r H : ℕ} (hr : r ≤ H) : 0 < slackGap r H := by
  unfold slackGap
  have : (r : ℝ) ≤ H := by exact_mod_cast hr
  linarith

/-- Arithmetic side condition discharged by `omega` from a strict bound or successor. -/
example {r H : ℕ} (hr : r < H) : 0 < slackGap r H := by positivity
example (n : ℕ) : 0 < slackGap n (n + 1) := by positivity

/-- Soundness when the arithmetic side condition is unavailable. -/
example (r H : ℕ) : 0 ≤ slackGap r H ^ 2 := by
  fail_if_success (have : 0 < slackGap r H := by positivity)
  positivity

/-- Cyclic sign-lemma hypothesis terminates cleanly when unprovable and succeeds from context. -/
private noncomputable def mystery (x : ℝ) : ℝ := x

@[local positivity_lemma]
private theorem mystery_pos_of_pos {x : ℝ} (hx : 0 < mystery x) : 0 < mystery x := hx

example (x : ℝ) (hx : 0 < mystery x) : 0 < 2 * mystery x := by positivity

example (x : ℝ) : 0 ≤ mystery x ^ 2 := by
  fail_if_success (have : 0 < mystery x := by positivity)
  positivity

/-! ### Rejected registrations -/

private theorem shifted_le (x : ℝ) : shifted x ≤ x + 1 ∨ x < 0 := by
  unfold shifted
  rcases le_or_gt 0 x with h | h
  · exact .inl (by linarith)
  · exact .inr h

/--
error: `@[positivity_lemma]` needs a lemma concluding `0 < e` or `0 ≤ e`, but shifted_le concludes
  shifted x ≤ x + 1 ∨ x < 0
-/
#guard_msgs in
attribute [local positivity_lemma] shifted_le

private theorem shifted_undetermined {x y : ℝ} (hy : 0 ≤ y) : 0 < shifted (x ^ 2) := by
  have _ := hy
  positivity

/--
error: `@[positivity_lemma]`: the argument of shifted_undetermined of type
  ℝ
is not determined by
  shifted (x ^ 2)
-/
#guard_msgs in
attribute [local positivity_lemma] shifted_undetermined

private theorem shifted_inst_undetermined {α : Type*} [inst : Nonempty α] (x : ℝ) :
    0 < shifted (x ^ 2) := by
  have _ := inst
  positivity

/--
error: `@[positivity_lemma]`: the argument of shifted_inst_undetermined of type
  Type ?u.1
is not determined by
  shifted (x ^ 2)
-/
#guard_msgs in
attribute [local positivity_lemma] shifted_inst_undetermined

private theorem nnreal_nonneg (x : NNReal) : 0 ≤ x := x.property

/--
error: `@[positivity_lemma]`: nnreal_nonneg states the sign of a variable, which `positivity` would have to try on every expression
-/
#guard_msgs in
attribute [local positivity_lemma] nnreal_nonneg

end CslibFrontierTests.PositivityLemma
