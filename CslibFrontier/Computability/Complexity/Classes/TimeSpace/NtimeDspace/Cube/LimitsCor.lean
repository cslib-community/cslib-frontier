/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Limits
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Consequences of Propositions 8.1 and 8.2

This file formalizes the three consequences that `separating-ntime-from-space.tex`, §8, draws from
Proposition 8.1 (`prop_boolean`) and Proposition 8.2 (`prop_barrier`). Here `log N` is `Real.logb 2
N`, and the
numbers of bits `r i`, `c i` are those of `Limits.lean` (`FactorsThroughOr`, `FactorsThrough`).

* After Proposition 8.1, "some Boolean piece has `r_i² + c_i² ≥ ½(r_i + c_i)² ≥ 8λ² − o(λ²)`"
  for `log N = o(λ)`. `prop_boolean_sq` proves, for the same piece, the exact inequalities
  `r_i + c_i ≥ 4λ − 2 log N`, `r_i² + c_i² ≥ ½ max(4λ − 2 log N, 0)²`, and
  `r_i² + c_i² ≥ 8λ² − 8λ log N`. The last is the `o(λ²)` reading made explicit: the error term
  `8λ log N` is `o(λ²)` exactly when `log N = o(λ)`.
* After Proposition 8.2, "some piece passes nearly all `a` bits through each cut, and its squared
  widths add up to `2a² − o(a²)`". `prop_barrier_sq` proves `min(r_i, c_i) ≥ a − log N`,
  `r_i² + c_i² ≥ 2 max(a − log N, 0)²` and `r_i² + c_i² ≥ 2a² − 4a log N`.
* "Fixing `y = u = 0^λ` turns the equal-width crossing into the equality matrix of
  Proposition 8.2, since both cuts then separate `x` from `v` and the factorizations restrict.
  Some piece therefore has `r_i + c_i ≥ 2λ − 2 log N`, and polynomially many pieces need
  `ρ ≥ ½`." `equalWidth_barrier` is the restriction argument: integer pieces `P i` of the
  crossing `[x = v][y = u]` of strings of `λ` bits, each factoring through `r i` bits across the
  row cut and `c i` bits across the column cut (the same two factorizations as in
  `prop_boolean`, now over the integers), have a piece with `2^λ ≤ N · 2^min(r i, c i)`.
  `equalWidth_sum` gives `2^(2λ) ≤ N² · 2^(r i + c i)` and `r i + c i ≥ 2λ − 2 log N`, and
  `equalWidth_rho` the bound on `ρ`: if every piece has `r i + c i ≤ 4ρλ + E`, then
  `2λ − 2 log N ≤ 4ρλ + E`, so `ρ ≥ ½ − (2 log N + E)/(4λ)`.

## Main results

* `logb_le_of_pow_le`: the multiplicative bounds of `Limits.lean` in logarithmic form.
* `prop_boolean_sq`, `prop_barrier_sq`: the squared forms.
* `equalWidth_barrier`, `equalWidth_sum`, `equalWidth_rho`: the restriction argument.

## Differences from the paper

* The paper's `r_i² + c_i² ≥ ½(r_i + c_i)²` needs no hypothesis, but the next step squares
  `4λ − 2 log N`, which is only sound when it is nonnegative; the exact statements use
  `max(·, 0)`, or the always-valid linear error terms `8λ log N` and `4a log N`.
* The equal-width pieces of `equalWidth_barrier` take integer values and sum to the crossing,
  as in Proposition 8.2; their factorizations are `FactorsThrough` of
  `fun (x, y) (u, v) => P i x y u v` (row cut) and of `fun (x, u) (y, v) => P i x y u v`
  (column cut). The restriction to `y = u = 0^λ` is `fun x v => P i x 0 0 v`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### From powers to logarithms -/

/-- A bound `2^A ≤ N^k · 2^B` in logarithmic form: `A − k log N ≤ B`. -/
theorem logb_le_of_pow_le {A B N k : ℕ} (h : 2 ^ A ≤ N ^ k * 2 ^ B) (hN : 0 < N) :
    (A : ℝ) - k * Real.logb 2 N ≤ B := by
  have hR : ((2 : ℝ) ^ A) ≤ (N : ℝ) ^ k * 2 ^ B := by exact_mod_cast h
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl
  linarith

/-- `N` is positive when `2^A ≤ N^(k+1) · 2^B`. -/
theorem pos_of_pow_le {A B N k : ℕ} (h : 2 ^ A ≤ N ^ (k + 1) * 2 ^ B) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : 0 < 2 ^ A := by positivity
    simp at h
  · exact hN

/-- `log N ≥ 0` for `N ≥ 1`. -/
theorem logb_nonneg_of_pos {N : ℕ} (hN : 0 < N) : 0 ≤ Real.logb 2 N :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)

/-! ### Squared widths -/

/-- `r² + c² ≥ ½ max(B, 0)²` when `r + c ≥ B` and `r, c ≥ 0`. -/
theorem sq_add_sq_ge_of_add_ge {r c B : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (h : B ≤ r + c) :
    max B 0 ^ 2 / 2 ≤ r ^ 2 + c ^ 2 := by
  rcases le_total B 0 with hB | hB
  · rw [max_eq_right hB]; nlinarith [sq_nonneg r, sq_nonneg c]
  · rw [max_eq_left hB]; nlinarith [sq_nonneg (r - c)]

/-- **After Proposition 8.1.** For Boolean pieces as in `prop_boolean`, some piece has
`r_i + c_i ≥ 4λ − 2 log N`, `r_i² + c_i² ≥ ½ max(4λ − 2 log N, 0)²` and
`r_i² + c_i² ≥ 8λ² − 8λ log N`. -/
theorem prop_boolean_sq {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) →
      Bool)
    (hP : ∀ x y u v, (∃ i, P i x y u v = true) ↔ (x = v ∧ y = u))
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i)) :
    ∃ i, (4 * lam : ℝ) - 2 * Real.logb 2 N ≤ r i + c i ∧
      max ((4 * lam : ℝ) - 2 * Real.logb 2 N) 0 ^ 2 / 2 ≤ (r i : ℝ) ^ 2 + (c i : ℝ) ^ 2 ∧
      8 * (lam : ℝ) ^ 2 - 8 * lam * Real.logb 2 N ≤ (r i : ℝ) ^ 2 + (c i : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ := prop_boolean P hP r c hr hc
  have hN := pos_of_pow_le (k := 1) hi
  have hL := logb_nonneg_of_pos hN
  have h1 := logb_le_of_pow_le hi hN
  push_cast at h1
  have hrc : (4 * lam : ℝ) - 2 * Real.logb 2 N ≤ r i + c i := h1
  have hr0 : (0 : ℝ) ≤ r i := by positivity
  have hc0 : (0 : ℝ) ≤ c i := by positivity
  have hl0 : (0 : ℝ) ≤ lam := by positivity
  refine ⟨i, hrc, sq_add_sq_ge_of_add_ge hr0 hc0 hrc, ?_⟩
  rcases le_total ((4 * lam : ℝ) - 2 * Real.logb 2 N) 0 with hB | hB
  · nlinarith
  · nlinarith [sq_nonneg ((r i : ℝ) - c i), sq_nonneg (Real.logb 2 N)]

/-- **After Proposition 8.2.** For integer pieces of the equality matrix as in `prop_barrier`,
some piece has `min(r_i, c_i) ≥ a − log N`, `r_i² + c_i² ≥ 2 max(a − log N, 0)²` and
`r_i² + c_i² ≥ 2a² − 4a log N`. -/
theorem prop_barrier_sq {a N : ℕ} (P : Fin N → (Fin a → Bool) → (Fin a → Bool) → ℤ)
    (hP : ∀ x v, ∑ i, P i x v = if x = v then 1 else 0)
    (r c : Fin N → ℕ) (hr : ∀ i, FactorsThrough (P i) (r i))
    (hc : ∀ i, FactorsThrough (P i) (c i)) :
    ∃ i, (a : ℝ) - Real.logb 2 N ≤ min (r i : ℝ) (c i) ∧
      2 * max ((a : ℝ) - Real.logb 2 N) 0 ^ 2 ≤ (r i : ℝ) ^ 2 + (c i : ℝ) ^ 2 ∧
      2 * (a : ℝ) ^ 2 - 4 * a * Real.logb 2 N ≤ (r i : ℝ) ^ 2 + (c i : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ := prop_barrier P hP r c hr hc
  have hi' : 2 ^ a ≤ N ^ 1 * 2 ^ min (r i) (c i) := by rwa [pow_one]
  have hN := pos_of_pow_le (k := 0) (by rwa [zero_add])
  have hL := logb_nonneg_of_pos hN
  have h1 := logb_le_of_pow_le hi' hN
  push_cast at h1
  have hmin : (a : ℝ) - Real.logb 2 N ≤ min (r i : ℝ) (c i) := by
    linarith
  have hr' : (a : ℝ) - Real.logb 2 N ≤ r i := hmin.trans (min_le_left _ _)
  have hc' : (a : ℝ) - Real.logb 2 N ≤ c i := hmin.trans (min_le_right _ _)
  have hr0 : (0 : ℝ) ≤ r i := by positivity
  have hc0 : (0 : ℝ) ≤ c i := by positivity
  have ha0 : (0 : ℝ) ≤ a := by positivity
  refine ⟨i, hmin, ?_, ?_⟩
  · rcases le_total ((a : ℝ) - Real.logb 2 N) 0 with hB | hB
    · rw [max_eq_right hB]; nlinarith [sq_nonneg (r i : ℝ), sq_nonneg (c i : ℝ)]
    · rw [max_eq_left hB]; nlinarith
  · rcases le_total ((a : ℝ) - Real.logb 2 N) 0 with hB | hB
    · nlinarith
    · nlinarith [sq_nonneg (Real.logb 2 N)]

/-! ### The equal-width crossing restricted to `y = u = 0^λ` -/

/-- **The restriction argument.** Let integer pieces `P i` of the equal-width crossing
`[x = v][y = u]` of strings of `λ` bits, `∑_i P i x y u v = [x = v][y = u]`, factor through
`r i` bits across the row cut and `c i` bits across the column cut. Fixing `y = u = 0^λ`, the
pieces `fun x v => P i x 0 0 v` sum to the equality matrix and factor through `r i` and through
`c i` bits, so by Proposition 8.2 some piece has `2^λ ≤ N · 2^min(r i, c i)`. -/
theorem equalWidth_barrier {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → ℤ)
    (hP : ∀ x y u v, ∑ i, P i x y u v = if x = v ∧ y = u then 1 else 0)
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i)) :
    ∃ i, 2 ^ lam ≤ N * 2 ^ min (r i) (c i) := by
  let o : Fin lam → Bool := fun _ => false
  refine prop_barrier (fun i x v => P i x o o v) (fun x v => ?_) r c (fun i => ?_) (fun i => ?_)
  · rw [hP]; simp
  · obtain ⟨φ, φ', h⟩ := hr i
    exact ⟨fun x => φ (x, o), fun v => φ' (o, v), fun x v => h (x, o) (o, v)⟩
  · obtain ⟨φ, φ', h⟩ := hc i
    exact ⟨fun x => φ (x, o), fun v => φ' (o, v), fun x v => h (x, o) (o, v)⟩

/-- **After the restriction argument.** For integer pieces of the equal-width crossing, some
piece has `2^(2λ) ≤ N² · 2^(r i + c i)`, that is, `r i + c i ≥ 2λ − 2 log N`. -/
theorem equalWidth_sum {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → ℤ)
    (hP : ∀ x y u v, ∑ i, P i x y u v = if x = v ∧ y = u then 1 else 0)
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i)) :
    ∃ i, 2 ^ (2 * lam) ≤ N ^ 2 * 2 ^ (r i + c i) ∧
      (2 * lam : ℝ) - 2 * Real.logb 2 N ≤ r i + c i := by
  obtain ⟨i, hi⟩ := equalWidth_barrier P hP r c hr hc
  have hpow : 2 ^ (2 * lam) ≤ N ^ 2 * 2 ^ (r i + c i) :=
    calc 2 ^ (2 * lam) = 2 ^ lam * 2 ^ lam := by rw [two_mul, pow_add]
      _ ≤ (N * 2 ^ min (r i) (c i)) * (N * 2 ^ min (r i) (c i)) := Nat.mul_le_mul hi hi
      _ = N ^ 2 * 2 ^ (min (r i) (c i) + min (r i) (c i)) := by rw [pow_add]; ring
      _ ≤ N ^ 2 * 2 ^ (r i + c i) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
          (Nat.add_le_add (min_le_left _ _) (min_le_right _ _)))
  have hN := pos_of_pow_le (k := 1) hpow
  have h1 := logb_le_of_pow_le hpow hN
  push_cast at h1
  exact ⟨i, hpow, h1⟩

/-- **The bound on `ρ`.** If every integer piece of the equal-width crossing has
`r i + c i ≤ 4ρλ + E`, then `2λ − 2 log N ≤ 4ρλ + E`; so with `N` and `E` polynomial and
logarithmic in `λ`, `ρ ≥ ½ − O(log λ / λ)`. -/
theorem equalWidth_rho {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → ℤ)
    (hP : ∀ x y u v, ∑ i, P i x y u v = if x = v ∧ y = u then 1 else 0)
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThrough
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i))
    (ρ E : ℝ) (hρ : ∀ i, (r i + c i : ℝ) ≤ 4 * ρ * lam + E) :
    (2 * lam : ℝ) - 2 * Real.logb 2 N ≤ 4 * ρ * lam + E := by
  obtain ⟨i, -, hi⟩ := equalWidth_sum P hP r c hr hc
  exact hi.trans (hρ i)

end Cslib.Complexity.NtimeDspace.Cube
