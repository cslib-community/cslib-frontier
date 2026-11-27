/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Tactic.ENNRealToReal

/-! # `ennreal_to_real`: reading finite `ℝ≥0∞` statements in `ℝ` -/

namespace CslibFrontierTests.ENNRealToReal

open scoped ENNReal

variable {α β : Type*}

/-! ### The goal -/

-- A closed identity: both sides are finite by their shape, and `norm_num` finishes in `ℝ`.
example : (2 : ℝ≥0∞)⁻¹ + 4⁻¹ = 3 / 4 := by
  ennreal_to_real
  norm_num

-- A strict inequality.
example : (1 / 2 : ℝ≥0∞) < 2 / 3 := by
  ennreal_to_real
  norm_num

-- A goal that is already real: `toReal` is pushed through `∑'` and `*`.
example (p : PMF α) (f : α → PMF β) (s : Set β) :
    (∑' a, p a * (f a).toOuterMeasure s).toReal =
      ∑' a, (p a).toReal * ((f a).toOuterMeasure s).toReal := by
  ennreal_to_real

/-! ### Hypotheses -/

-- `ENNReal.ofReal ε` becomes `ε` when `0 ≤ ε` is a hypothesis. The tactic is not terminal.
example (p q : PMF α) (s : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : p.toOuterMeasure s ≤ q.toOuterMeasure s + ENNReal.ofReal ε)
    (h₂ : q.toOuterMeasure s ≤ p.toOuterMeasure s + ENNReal.ofReal ε) :
    |(p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal| ≤ ε := by
  ennreal_to_real at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

-- A hypothesis `a ≤ b` needs only `b` finite: `x` is arbitrary here.
example (x : ℝ≥0∞) (p : PMF α) (a : α) (h : x ≤ 2 * p a) : x.toReal ≤ 2 * (p a).toReal := by
  ennreal_to_real at h
  exact h

-- A strict hypothesis, with a bound `δ : ℝ≥0`.
example (p : PMF α) (s t : Set α) (δ : NNReal) (h : p.toOuterMeasure s + δ < p.toOuterMeasure t) :
    (p.toOuterMeasure s).toReal + δ < (p.toOuterMeasure t).toReal := by
  ennreal_to_real at h
  exact h

/-! ### `using` -/

-- The usual shape: an `ℝ≥0∞` bound read as a real one.
example (p q : PMF α) (s : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (h : p.toOuterMeasure s ≤ q.toOuterMeasure s + ENNReal.ofReal ε) :
    (p.toOuterMeasure s).toReal ≤ (q.toOuterMeasure s).toReal + ε := by
  ennreal_to_real using h

-- A finite sum.
example {k : ℕ} (p : PMF α) (q : Fin k → PMF α) (s : Set α) (t : Fin k → Set α)
    (h : p.toOuterMeasure s ≤ ∑ i, (q i).toOuterMeasure (t i)) :
    (p.toOuterMeasure s).toReal ≤ ∑ i, ((q i).toOuterMeasure (t i)).toReal := by
  ennreal_to_real using h

-- From `ℝ` to `ℝ≥0∞`: the goal is transferred, and the real fact closes it.
example (p : PMF α) (s : Set α) {ε : ℝ} (hε : 0 ≤ ε) (h : (p.toOuterMeasure s).toReal ≤ ε) :
    p.toOuterMeasure s ≤ ENNReal.ofReal ε := by
  ennreal_to_real using h

-- The term after `using` is elaborated on its own, so a bound that the goal would otherwise
-- determine is given explicitly (`b := ENNReal.ofReal ε` here).
example (p : PMF α) (s : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (bound : ∀ b : ℝ≥0∞, (∀ a, p a ≤ b) → p.toOuterMeasure s ≤ b + b)
    (h : ∀ a, (p a).toReal ≤ ε) : (p.toOuterMeasure s).toReal ≤ ε + ε := by
  ennreal_to_real using bound (ENNReal.ofReal ε) fun a => by ennreal_to_real using h a

/-! ### Side conditions that are not found stay visible -/

-- Truncated subtraction is rewritten when `b ≤ a` is a hypothesis.
example (p : PMF α) (a : α) (x : ℝ≥0∞) (hx : x ≤ 1) (h : p a ≤ 1 - x) :
    (p a).toReal ≤ 1 - x.toReal := by
  ennreal_to_real using h

-- The hypothesis may be about `ℝ≥0`, as for a success probability `c`.
example (p : PMF α) (a : α) (c : NNReal) (hc : c ≤ 1) (k : ℕ) (h : p a ≤ (1 - (c : ℝ≥0∞)) ^ k) :
    (p a).toReal ≤ (1 - (c : ℝ)) ^ k := by
  ennreal_to_real using h

-- Without it, `(1 - x).toReal` is left as it is.
example (p : PMF α) (a : α) (x : ℝ≥0∞) (h : p a ≤ 2 * (1 - x)) :
    (p a).toReal ≤ 2 * (1 - x).toReal := by
  ennreal_to_real at h
  exact h

-- `ENNReal.ofReal r` without `0 ≤ r` is left as it is.
example (p : PMF α) (a : α) (r : ℝ) (h : p a ≤ 2 * ENNReal.ofReal r) :
    (p a).toReal ≤ 2 * (ENNReal.ofReal r).toReal := by
  ennreal_to_real at h
  exact h

-- Under `∑'` each term must be finite by its shape. A probability of a bind is; the `∑'` it
-- unfolds to is not. So push `toReal` through the outer sum first, then unfold the inner one.
example (p : PMF α) (f : α → PMF β) (g : β → PMF Bool) :
    (∑' a, p a * ((f a).bind g).toOuterMeasure {true}).toReal =
      ∑' a, (p a).toReal * ∑' b, (f a b).toReal * ((g b).toOuterMeasure {true}).toReal := by
  ennreal_to_real
  simp only [PMF.toOuterMeasure_bind_apply]
  ennreal_to_real

/-! ### Failures -/

/--
error: ennreal_to_real: could not show that
  x * p a + 1
is finite. `finiteness` is left with
  x * p a ≠ ∞
Add the missing fact as a hypothesis, or register it as a `finiteness` rule.
-/
#guard_msgs in
example (x : ℝ≥0∞) (p : PMF α) (a : α) : x * p a + 1 ≤ 3 := by
  ennreal_to_real

-- With the missing fact as a hypothesis, the same call succeeds.
example (x : ℝ≥0∞) (hx : x ≠ ∞) (p : PMF α) (a : α) (h : 3 ≤ x * p a + 1) :
    3 ≤ x.toReal * (p a).toReal + 1 := by
  ennreal_to_real using h

-- A real sum under `toReal` that cannot be split: the error names the summand.
/--
error: ennreal_to_real: could not show that
  x + 1
is finite. `finiteness` is left with
  x ≠ ∞
Add the missing fact as a hypothesis, or register it as a `finiteness` rule.
-/
#guard_msgs in
example (x : ℝ≥0∞) : (x + 1).toReal = x.toReal + 1 := by
  ennreal_to_real

/--
error: ennreal_to_real made no progress: no `ℝ≥0∞` relation to transfer and no `toReal` to push.
A `toReal` stays in place when its side condition is not found:
`(a - b).toReal` needs `b ≤ a`, and `(ENNReal.ofReal r).toReal` needs `0 ≤ r`.
-/
#guard_msgs in
example (x y : ℝ) (h : x ≤ y) : x ≤ y := by
  ennreal_to_real

/-- error: ennreal_to_real: `at *` is not supported; name the hypotheses -/
#guard_msgs in
example (x y : ℝ≥0∞) (h : x ≤ y) : x ≤ y := by
  ennreal_to_real at *

end CslibFrontierTests.ENNRealToReal
