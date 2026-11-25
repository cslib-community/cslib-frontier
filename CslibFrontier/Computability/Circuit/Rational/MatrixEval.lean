/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.MatrixEval.Defs
public import CslibFrontier.Computability.Circuit.Rational.Eval

/-!
# Exact matrix evaluation and consequences of hitting lists

These deductions use OpenAI's rational-formula semantics. Inverse is partial: every evaluated
inverse node must have a genuine two-sided inverse.

A hitting list detects nonzeroness by an invertible value. With two extra syntax nodes in the
node-count bound, it also detects admissibility, including for identically zero formulas: at a
defined point, either `f` or `f + 1` is nonzero. The executable tests here have correctness
proofs; no polynomial bound for their rational arithmetic is asserted.

## Main results

* `Cslib.Circuits.Rational.Formula.evalMatrix?_eq_some_iff`: the executable evaluation returns
  exactly the values of the evaluation relation.
* `Cslib.Circuits.Rational.admissible_nonzero_or_add_one`: at a defined point, `f` or `f + 1` is
  nonzero.
* `Cslib.Circuits.Rational.Hits.nonzero_iff`, `Cslib.Circuits.Rational.Hits.admissible_iff`,
  `Cslib.Circuits.Rational.Hits.admissible_inv_iff_nonzero`: a hitting list detects nonzeroness
  and admissibility.
* `Cslib.Circuits.Rational.Hits.admissibilityTest_eq_true_iff`,
  `Cslib.Circuits.Rational.Hits.nonzeroTest_eq_true_iff`: the finite tests decide admissibility
  and nonzeroness.

## References

* From the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787 (files Complexitylib/RationalHitting/Evaluation.lean
  and Complexitylib/RationalHitting/Internal/Detection.lean),
  built on OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

public section

namespace Cslib.Circuits.Rational

open Rational.Formula Rational.Output

private theorem evalMatrix?_sound {n d : ℕ} (f : Formula n) (X : Tuple n d)
    {v : Mat d} (h : f.evalMatrix? X = some v) : Evaluates f X v := by
  induction f using inductionOn generalizing v with
  | var i => exact Option.some.inj h ▸ .var i
  | const q => exact Option.some.inj h ▸ .const q
  | add f g ihf ihg =>
    simp only [evalMatrix?_add, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h; exact Eval.add (ihf ha) (ihg hb)
  | mul f g ihf ihg =>
    simp only [evalMatrix?_mul, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h; exact Eval.mul (ihf ha) (ihg hb)
  | inv f ih =>
    simp only [evalMatrix?_inv, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hb⟩ := h
    by_cases hd : a.det = 0
    · simp [hd] at hb
    · obtain rfl : a.det⁻¹ • a.adjugate = v := by simpa [hd] using hb
      have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr hd
      rw [← Ring.inverse_eq_inv', ← Matrix.inv_def]
      exact Eval.inv (ih ha) (a.mul_nonsing_inv hu) (a.nonsing_inv_mul hu)

private theorem evalMatrix?_complete {n d : ℕ} {f : Formula n} {X : Tuple n d}
    {v : Mat d} (h : Evaluates f X v) : f.evalMatrix? X = some v := by
  induction f using inductionOn generalizing v with
  | var i => rw [eval_var_iff.mp h]; rfl
  | const q => rw [eval_const_iff.mp h]; rfl
  | add f g ihf ihg => obtain ⟨_, _, ha, hb, rfl⟩ := eval_add_iff.mp h; simp [ihf ha, ihg hb]
  | mul f g ihf ihg => obtain ⟨_, _, ha, hb, rfl⟩ := eval_mul_iff.mp h; simp [ihf ha, ihg hb]
  | inv f ih =>
    obtain ⟨a, ha, hab, hba⟩ := eval_inv_iff.mp h
    have hu : IsUnit a.det := (Matrix.isUnit_iff_isUnit_det a).mp ⟨⟨a, v, hab, hba⟩, rfl⟩
    have hi : Evaluates (.inv f) X (a.det⁻¹ • a.adjugate) := by
      rw [← Ring.inverse_eq_inv', ← Matrix.inv_def]
      exact Eval.inv ha (a.mul_nonsing_inv hu) (a.nonsing_inv_mul hu)
    simp [ih ha, hu.ne_zero, Eval.unique hi h]

/-- The executable evaluator returns exactly the values admitted by the evaluation relation. -/
theorem Formula.evalMatrix?_eq_some_iff {n d : ℕ} (f : Formula n) (X : Tuple n d)
    (v : Mat d) : f.evalMatrix? X = some v ↔ Evaluates f X v :=
  ⟨evalMatrix?_sound f X, evalMatrix?_complete⟩

/-- A nonzero evaluation already supplies a point in the formula's domain. -/
theorem Nonzero.admissible {n : ℕ} {f : Formula n} (hf : Nonzero f) : Admissible f :=
  let ⟨d, hd, X, v, he, _⟩ := hf; ⟨d, hd, X, v, he⟩

/-- Positive dimension makes an invertible hitting value a nonzero witness. -/
theorem Hits.nonzero_iff {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.nodeCount ≤ s) :
    Nonzero f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  have : NeZero H.dimension := ⟨H.dimension_pos.ne'⟩
  exact ⟨fun h => hH f hf h.admissible h,
    fun ⟨X, _, v, he, hu⟩ => ⟨H.dimension, H.dimension_pos, X, v, he, hu.ne_zero⟩⟩

/-- At any defined point, either the value of `f` or the value of `f + 1` is nonzero. -/
theorem admissible_nonzero_or_add_one {n : ℕ} (f : Formula n) (hf : Admissible f) :
    Nonzero f ∨ Nonzero (.add f (.const 1)) := by
  obtain ⟨d, hd, X, v, he⟩ := hf
  by_cases hv : v = 0
  · have : NeZero d := ⟨hd.ne'⟩
    exact Or.inr ⟨d, hd, X, v + 1,
      by simpa only [Evaluates, map_one] using Eval.add he (Eval.const 1),
      by simpa only [hv, zero_add] using (one_ne_zero : (1 : Mat d) ≠ 0)⟩
  · exact Or.inl ⟨d, hd, X, v, he, hv⟩

/-- A hitting list with an allowance of two more nodes also detects the domain of every formula. -/
theorem Hits.admissible_iff {n s : ℕ} {H : Output n} (hH : Hits (s + 2) H)
    (f : Formula n) (hf : f.nodeCount ≤ s) :
    Admissible f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  refine ⟨fun ha => ?_, fun ⟨X, _, v, he⟩ => ⟨H.dimension, H.dimension_pos, X, v, he⟩⟩
  rcases admissible_nonzero_or_add_one f ha with hn | hn
  · obtain ⟨X, hX, v, he, _⟩ := hH f (by lia) ha hn; exact ⟨X, hX, v, he⟩
  · obtain ⟨X, hX, _, he, _⟩ := hH (.add f (.const 1))
      (by simp only [nodeCount_add, nodeCount_const]; lia) hn.admissible hn
    obtain ⟨a, _, hleft, _⟩ := eval_add_iff.mp he; exact ⟨X, hX, a, hleft⟩

/-- An invertible hit turns a nonzero formula into one with an admissible inverse. -/
theorem Hits.admissible_inv_iff_nonzero {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.nodeCount ≤ s) : Admissible (.inv f) ↔ Nonzero f := by
  refine ⟨fun ⟨d, hd, X, v, he⟩ => ?_, fun hn => ?_⟩
  · have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨a, he, hab, hba⟩ := eval_inv_iff.mp he
    exact ⟨d, hd, X, a, he, IsUnit.ne_zero ⟨⟨a, v, hab, hba⟩, rfl⟩⟩
  · obtain ⟨X, _, _, he, ⟨u, rfl⟩⟩ := (hH.nonzero_iff f hf).mp hn
    exact ⟨H.dimension, H.dimension_pos, X, ↑u⁻¹, Eval.inv he u.mul_inv u.inv_mul⟩

/-- The executable domain test searches exactly the defined evaluations on the list. -/
theorem Output.admissibilityTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.admissibilityTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  simp only [admissibilityTest, List.any_eq_true, Option.isSome_iff_exists, evalMatrix?_eq_some_iff]

/-- The executable determinant test searches exactly the invertible evaluations on the list. -/
theorem Output.nonzeroTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.nonzeroTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  simp only [nonzeroTest, List.any_eq_true, Option.any_eq_true, decide_eq_true_eq,
    evalMatrix?_eq_some_iff, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]

/-- A hitting list for `s + 2` nodes decides admissibility of formulas with at most `s` nodes. -/
theorem Hits.admissibilityTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits (s + 2) H) (f : Formula n) (hf : f.nodeCount ≤ s) :
    H.admissibilityTest f = true ↔ Admissible f := by
  rw [H.admissibilityTest_iff f, hH.admissible_iff f hf]

/-- A hitting list for `s` nodes decides nonzeroness of formulas with at most `s` nodes. -/
theorem Hits.nonzeroTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits s H) (f : Formula n) (hf : f.nodeCount ≤ s) :
    H.nonzeroTest f = true ↔ Nonzero f := by
  rw [H.nonzeroTest_iff f, hH.nonzero_iff f hf]

end Cslib.Circuits.Rational
