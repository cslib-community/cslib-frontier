/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
public import Mathlib.Basic.Real.Basic

/-!
# The limit of average-case hardness

Every Boolean function `f` on `n` bits is approximated by small circuits a little better than by
coin flips: for every `t` with `2 t ≤ 2 ^ n` there is a Boolean function of De Morgan circuit
complexity at most `t (2 n + 3) + 1` that agrees with `f` on at least a `1 / 2 + t / 2 ^ n`
fraction of the inputs (`exists_complexity_le_and_add_le_card_agree`). The circuit outputs the
majority value of `f`, except on at most `t` hard-wired inputs where `f` takes the other value
(fewer when `f` has fewer minority inputs). For `t = 1` this is a circuit of size `2 n + 4` with
agreement `1 / 2 + 2 ^ (-n)`.

This is Exercise 7.10 of Goldreich [Goldreich2007DraftR4]. The text after his Definition 7.9 cites
it for the limit of inapproximability: no predicate is `(S, ρ)`-inapproximable, that is
`Pr [C (U_n) ≠ f (U_n)] ≥ ρ (n) / 2` for every circuit of size `S (n)`, with `ρ (n) = 1 - 2 ^ (-n)`,
even for linear `S`. The source's warning that `Pr [f (U_n) = 1]` need not be `1 / 2` is the
reason for the majority value.

## Main results

* `Cslib.Circuits.Boolean.exists_complexity_le_and_add_le_card_agree`: Goldreich, Exercise 7.10.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` (March
  2007)][Goldreich2007DraftR4], Definition 7.9 and Exercise 7.10
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- **Small circuits beat coin flips** [Goldreich, Exercise 7.10][Goldreich2007DraftR4]: for every
`f : {0,1}ⁿ → {0,1}` and every `t` with `2 t ≤ 2 ^ n` (that is, `t ≤ 2 ^ (n - 1)`; for `n = 0`
only `t = 0`), some Boolean function of circuit complexity at most `t (2 n + 3) + 1`, a circuit of
size `O(t n + 1)` (so `O(t n)` for positive `t` and `n`), agrees with `f` on at least a
`1 / 2 + t / 2 ^ n` fraction of the inputs. It outputs the majority value of `f`, corrected on at
most `t` inputs. For `t = 1` and `n ≥ 1` this is the first claim of the exercise: a circuit of size
`2 n + 4` with agreement `1 / 2 + 2 ^ (-n)`. (At `n = 0` that claim would need agreement `3 / 2`.)
Sizes are counted as in `Cslib.Circuits.complexity`, and agreement as in `IsAverageCaseHard`. -/
theorem exists_complexity_le_and_add_le_card_agree (f : BooleanFunction n) {t : ℕ}
    (ht : 2 * t ≤ 2 ^ n) :
    ∃ g : BooleanFunction n, complexity interpretation (single g) ≤ t * (2 * n + 3) + 1 ∧
      1 / 2 + (t : ℝ) / 2 ^ n ≤ (#{x | g x = f x} : ℝ) / 2 ^ n := by
  classical
  -- the majority value `b` of `f`
  set b : Bool := decide (2 ^ n ≤ 2 * #{x | f x = true}) with hb_def
  have htf : #{x | f x = true} + #{x | f x = false} = 2 ^ n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (BitString n)))
      fun x => f x = true
    simpa only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using h
  have hsplit : #{x | f x = b} + #{x | f x ≠ b} = 2 ^ n := by
    cases b <;> simpa [add_comm] using htf
  have hmaj : 2 ^ n ≤ 2 * #{x | f x = b} := by
    by_cases h : 2 ^ n ≤ 2 * #{x | f x = true}
    · have hb : b = true := by simp [hb_def, h]
      rw [hb]
      exact h
    · have hb : b = false := by simp [hb_def, h]
      rw [hb]
      omega
  obtain ⟨T, hTD, hT⟩ := exists_subset_card_eq (min_le_right t #{x | f x ≠ b})
  refine ⟨fun x => if x ∈ T then !b else b, ?_, ?_⟩
  · exact (complexity_ite_mem_le (fun _ => !b) T b).trans
      (by gcongr; rw [hT]; exact min_le_left _ _)
  · -- `g` agrees with `f` where `f = b`, and on `T`, where `f = !b`
    have hagree : #{x | (if x ∈ T then !b else b) = f x} = #{x | f x = b} + #T := by
      rw [← card_union_of_disjoint]
      · congr 1
        ext x
        have hxT : x ∈ T → f x ≠ b := fun hx => (mem_filter.1 (hTD hx)).2
        by_cases hx : x ∈ T
        · have hfx : f x = !b := Bool.eq_not_iff.2 (hxT hx)
          simp [hx, hfx]
        · simp [hx, eq_comm]
      · exact disjoint_left.2 fun x hx hxT => (mem_filter.1 (hTD hxT)).2 (mem_filter.1 hx).2
    rw [hagree]
    have hcount : 2 ^ n + 2 * t ≤ 2 * (#{x | f x = b} + #T) := by
      rw [hT]
      rcases le_total t #{x | f x ≠ b} with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have hc : (2 : ℝ) ^ n + 2 * t ≤ 2 * ((#{x | f x = b} : ℝ) + #T) := by exact_mod_cast hcount
    rw [le_div_iff₀ hpos]
    have e : (1 / 2 + (t : ℝ) / 2 ^ n) * 2 ^ n = 2 ^ n / 2 + t := by field_simp
    rw [e]
    push_cast
    linarith

end Cslib.Circuits.Boolean
