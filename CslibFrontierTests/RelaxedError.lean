/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.RelaxedError

/-! Checked instances of the error thresholds of `BPP`, `RP` and `ZPP`: the hypotheses of the
Goldreich and Arora–Barak statements are satisfiable, a weak verifier with success probability
`5 / 8` meets the weak-gap hypothesis, and the all-lengths scaled form `1 / 2 + (n + 1) ^ (-c)` of
Arora–Barak, Lemma 7.9 is an instance of the general theorem but is empty over `encBits`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.RelaxedError

open Cslib Cslib.Complexity Polynomial Filter Turing.MultiTapeTM

/-- Goldreich, Exercise 6.4(1), at `p = X + 3`. -/
example : BPPWithError encBits (fun n => 1 / 2 - 1 / ((((X + 3 : ℕ[X]).eval n : ℕ) : ℝ))) =
    BPP encBits :=
  BPPWithError_eq_BPP fun n => by simp; omega

/-- Goldreich, Exercise 6.5(1), at `p = 2`. -/
example : RPWithSuccess encBits (fun n => 1 / ((((2 : ℕ[X]).eval n : ℕ) : ℝ))) = RP encBits :=
  RPWithSuccess_inv_eq_RP fun n => by simp

/-- Goldreich, Exercise 6.6(1), at `p = X + 2`. -/
example : ZPPWithSuccess encBits (fun n => 1 / ((((X + 2 : ℕ[X]).eval n : ℕ) : ℝ))) =
    ZPP encBits :=
  ZPPWithSuccess_inv_eq_ZPP fun n => by simp

/-- Goldreich, Exercise 6.6(2), at `p = X + 1`. -/
example : ZPP encBits =
    ZPPWithSuccess encBits (fun n => 1 - ((2 : ℝ) ^ (X + 1 : ℕ[X]).eval n)⁻¹) :=
  ZPP_eq_ZPPWithSuccess fun n => by simp

/-- Arora–Barak, Lemma 7.9, at `c = 1 / 2`, over binary strings. -/
example : {A | ∃ N : ℕ, A ∈ BPPWithError encBits
      (fun n => if n < N then 1 else 1 / 2 - (n : ℝ) ^ (-(1 / 2 : ℝ)))} = BPP encBits :=
  setOf_exists_BPPWithError_rpow_eq_BPP (by norm_num)

/-- The scaled bound `1 / 2 + (n + 1) ^ (-1)` at all lengths gives `BPP`: an instance of
`BPPWithError_subset_BPP` with `q = X + 1`. -/
example {α : Type} (enc : α ↪ List Bool) :
    BPPWithError enc (fun n => 1 / 2 - ((n : ℝ) + 1)⁻¹) ⊆ BPP enc :=
  BPPWithError_subset_BPP (X + 1) (Eventually.of_forall fun n => ⟨by simp, by simp⟩)

/-- Over `encBits`, the scaled all-lengths class is empty: on the empty string it would need
success probability `3 / 2`. This is why Lemma 7.9 is stated from some length on. -/
example : BPPWithError encBits (fun n => 1 / 2 - ((n : ℝ) + 1)⁻¹) = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, V, -, h⟩
  have hle := (Nat.cast_le (α := ℝ)).2
    (acceptCount_le_two_pow (V := V) (a := []) (n := p.eval (encBits []).length))
  push_cast at hle
  have hpos : (0 : ℝ) < 2 ^ p.eval (encBits []).length := by positivity
  have h0 : (encBits []).length = 0 := rfl
  by_cases hA : [] ∈ A
  · have := (h []).1 hA
    rw [h0] at this hle hpos
    norm_num at this
    linarith
  · have := (h []).2 hA
    rw [h0] at this hle hpos
    norm_num at this
    have : (0 : ℝ) ≤ acceptCount V [] (p.eval 0) := Nat.cast_nonneg _
    linarith

/-! ### A weak verifier -/

/-- The one-element instance type, encoded by the empty string. -/
def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- On three random bits, accept unless the bits are `000`, `001` or `010`: success probability
`5 / 8 = 1 / 2 + 1 / 8`. -/
def fiveEighths (x : Unit × List Bool) : Bool :=
  !(x.2 == [false, false, false] || x.2 == [false, false, true] || x.2 == [false, true, false])

/-- The weak-gap hypothesis holds with `q = 8`, so `2 · 8 ^ 2` majority votes on `384` random bits
answer `true` with bounded error. -/
example : BoundedErrorAt encUnit (2 * 8 ^ 2 * 3) (repeatMajority encUnit (8 ^ 2) 3 fiveEighths)
    () true :=
  boundedErrorAt_repeatMajority_sq (by
    change 2 * 2 ^ _ ≤
      _ * (2 * acceptCount fiveEighths () ((3 : ℕ[X]).eval (encUnit ()).length) - _)
    simp only [eval_ofNat]
    decide)

/-- The same verifier accepts on at least an eighth of the random strings, so `8` repetitions
accept on at least half. -/
example : 2 ^ (8 * 3 : ℕ[X]).eval (encUnit ()).length ≤
    2 * acceptCount (repeatAny encUnit 8 3 fiveEighths) () ((8 * 3 : ℕ[X]).eval
      (encUnit ()).length) :=
  two_pow_le_two_mul_acceptCount_repeatAny (by simp only [eval_ofNat]; decide)

end CslibFrontierTests.RelaxedError
