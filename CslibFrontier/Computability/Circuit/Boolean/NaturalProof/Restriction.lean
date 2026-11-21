/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Data.BitString.PartialAssignment.Counting
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Largeness of the restriction property

Arora–Barak's January 8, 2007 web draft asks in Chapter 22, Exercise §2 (printed p. 443,
PDF p. 459), for the probability that a random Boolean function satisfies the property from
Example 22.5 (printed p. 439, PDF p. 455) to tend to one. The function is sampled uniformly
from all truth tables, and for each fixed real `ε ∈ (0,1)` the property rules out a constant
restriction fixing at most `n - n^ε` coordinates, with subtraction in the reals.

On a subcube with `k` free coordinates the restricted truth table is uniform on `2^k`
entries. Two such tables are constant. A union bound ranges over at most `3^n` partial
assignments, and the double exponential in the denominator dominates that factor.

## Main results

* `Cslib.Circuits.Boolean.prob_exists_constant_restriction_le`: finite failure bound.
* `Cslib.Circuits.Boolean.tendsto_prob_no_constant_restriction`: Exercise 22 §2.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

open BitString Finset Filter Probability
open scoped Topology

private theorem prob_constant_restriction {n : ℕ} (ρ : PartialAssignment (Fin n)) :
    ((PMF.uniformOfFintype (BitString n → Bool)).toOuterMeasure
      {f | ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}).toReal =
        2 / (2 : ℝ) ^ (2 ^ ρ.free.card) := by
  classical
  let S : Finset (BitString n) := univ.filter (ρ.Agrees ·)
  have hS : S.card = 2 ^ ρ.free.card := by
    rw [← PartialAssignment.card_filter_outside_eq ρ]
    congr 1
    ext x
    simp only [S, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      funext i
      cases hi : ρ i with
      | none => simp [PartialAssignment.outside, hi]
      | some b => simp [PartialAssignment.outside, hi, hx i b hi]
    · intro hx i b hi
      simpa [PartialAssignment.outside, hi] using congrFun hx i
  let c (b : Bool) : S → Bool := fun _ => b
  have hset : {f : BitString n → Bool | ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b} =
      S.restrict ⁻¹' (({c false} : Set (S → Bool)) ∪ ({c true} : Set (S → Bool))) := by
    ext f
    simp [S, c, Bool.exists_bool, or_comm, funext_iff, Finset.restrict]
  have hne : c false ≠ c true := by
    intro h
    have hx : (ρ.fill (fun _ => false)) ∈ S := mem_filter.mpr ⟨mem_univ _, ρ.agrees_fill _⟩
    exact Bool.false_ne_true (congrFun h ⟨_, hx⟩)
  rw [hset, ← PMF.toOuterMeasure_map_apply, Probability.PMF.uniformOfFintype_pi_map_restrict,
    Probability.PMF.toOuterMeasure_union_of_disjoint _ (Set.disjoint_singleton.mpr hne)]
  rw [ENNReal.toReal_add (Probability.PMF.toOuterMeasure_ne_top _ _)
    (Probability.PMF.toOuterMeasure_ne_top _ _)]
  simp [PMF.uniformOfFintype_apply, hS, div_eq_mul_inv, two_mul]

/-- The probability of a constant restriction leaving at least `k` coordinates free is bounded
by the number of restrictions times the probability for a single `k`-dimensional subcube. -/
theorem prob_exists_constant_restriction_le (n k : ℕ) :
    ((PMF.uniformOfFintype (BitString n → Bool)).toOuterMeasure
      {f | ∃ ρ : PartialAssignment (Fin n), k ≤ ρ.free.card ∧
        ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}).toReal ≤
        (3 : ℝ) ^ n * (2 / (2 : ℝ) ^ (2 ^ k)) := by
  classical
  let J := (univ : Finset (PartialAssignment (Fin n))).filter (fun ρ => k ≤ ρ.free.card)
  let B (ρ : PartialAssignment (Fin n)) : Set (BitString n → Bool) :=
    {f | ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}
  have hset : {f | ∃ ρ : PartialAssignment (Fin n), k ≤ ρ.free.card ∧
      ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b} = ⋃ ρ ∈ J, B ρ := by
    ext f
    simp [J, B]
  rw [hset]
  refine (Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le _ J B).trans ?_
  calc
    _ ≤ ∑ _ρ ∈ J, (2 / (2 : ℝ) ^ (2 ^ k)) := by
      apply sum_le_sum
      intro ρ hρ
      rw [show B ρ = _ from rfl, prob_constant_restriction]
      have hk := (mem_filter.mp hρ).2
      gcongr
      norm_num
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      have hcard : J.card ≤ 3 ^ n := by
        simpa [PartialAssignment, Fintype.card_fun] using
          (card_filter_le (univ : Finset (PartialAssignment (Fin n)))
            (fun ρ => k ≤ ρ.free.card))
      gcongr
      exact_mod_cast hcard

private theorem eventually_four_mul_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 4 * n ≤ 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (tendsto_exp_mul_div_rpow_atTop (1 / ε) (Real.log 2) hlog).comp
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)
  filter_upwards [h.eventually_ge_atTop 4, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn₀
  change 4 ≤ Real.exp (Real.log 2 * (n : ℝ) ^ ε) / ((n : ℝ) ^ ε) ^ (1 / ε) at hn
  rw [← Real.rpow_mul hpos.le, mul_one_div_cancel hε.ne', Real.rpow_one] at hn
  have hle : (4 : ℝ) * n ≤ (2 : ℝ) ^ ⌈(n : ℝ) ^ ε⌉₊ := calc
    _ ≤ Real.exp (Real.log 2 * (n : ℝ) ^ ε) := (le_div_iff₀ hpos).mp hn
    _ = (2 : ℝ) ^ ((n : ℝ) ^ ε) := (Real.rpow_def_of_pos (by norm_num) _).symm
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  exact_mod_cast hle

/-- Arora–Barak, 2007 web draft, Chapter 22, Exercise §2. For every fixed `0 < ε < 1`,
the probability that no assignment to at most `n - n^ε` inputs makes the uniform Boolean
function constant tends to one as the number of inputs tends to infinity. -/
theorem tendsto_prob_no_constant_restriction (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ((PMF.uniformOfFintype (BitString n → Bool)).toOuterMeasure
      {f | ∀ ρ : PartialAssignment (Fin n), (ρ.support.card : ℝ) ≤ n - (n : ℝ) ^ ε →
        ¬ ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}).toReal) atTop (𝓝 1) := by
  classical
  let bad (n : ℕ) : Set (BitString n → Bool) :=
    {f | ∃ ρ : PartialAssignment (Fin n), ⌈(n : ℝ) ^ ε⌉₊ ≤ ρ.free.card ∧
      ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}
  have hbad : Tendsto (fun n => ((PMF.uniformOfFintype (BitString n → Bool)).toOuterMeasure
      (bad n)).toReal) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n => 2 * (1 / 4 : ℝ) ^ n)
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_ ?_
    · filter_upwards [eventually_four_mul_le ε hε.1] with n hn
      refine (prob_exists_constant_restriction_le n _).trans ?_
      calc
        _ ≤ (4 : ℝ) ^ n * (2 / (2 : ℝ) ^ (4 * n)) := by gcongr <;> norm_num
        _ = 2 * (1 / 4 : ℝ) ^ n := by
          rw [pow_mul, div_eq_mul_inv, ← mul_assoc, mul_comm ((4 : ℝ) ^ n), mul_assoc,
            ← div_eq_mul_inv, ← div_pow]
          norm_num
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num)).const_mul 2
  have hgood := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  rw [sub_zero] at hgood
  refine hgood.congr fun n => ?_
  have hset : (bad n)ᶜ = {f | ∀ ρ : PartialAssignment (Fin n),
      (ρ.support.card : ℝ) ≤ n - (n : ℝ) ^ ε →
      ¬ ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b} := by
    ext f
    simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, Nat.ceil_le]
    have hcard (ρ : PartialAssignment (Fin n)) :
        (ρ.free.card : ℝ) + ρ.support.card = n := by
      exact_mod_cast (show ρ.free.card + ρ.support.card = n by
        rw [← ρ.compl_free, card_add_card_compl, Fintype.card_fin])
    exact forall_congr' fun ρ => by
      rw [show ((n : ℝ) ^ ε ≤ ρ.free.card) ↔
        (ρ.support.card : ℝ) ≤ n - (n : ℝ) ^ ε by constructor <;> intro h <;> linarith [hcard ρ]]
  rw [← hset]
  have h := Probability.PMF.toOuterMeasure_toReal_add_compl
    (PMF.uniformOfFintype (BitString n → Bool)) (bad n)
  linarith

end Cslib.Circuits.Boolean
