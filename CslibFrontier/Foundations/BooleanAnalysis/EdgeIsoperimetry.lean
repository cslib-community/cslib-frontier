/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith

/-!
# The edge-isoperimetric inequality for the Hamming cube

A set `A` of the Hamming cube spans few edges: counting each edge from both of its endpoints,
summing over the points of `A` their numbers of neighbours in `A` gives at most `|A| log₂ |A|`
(`BitString.sum_card_filter_update_mem_le`). This is the classical bound behind the
edge-isoperimetric inequality, first proved by Harper (1964) [O'Donnell, Section 2.6][ODonnell2014],
proved here by induction on the dimension:
splitting the cube along one coordinate into halves with `a` and `b` points of `A`, the edges
across the cut number at most `min a b`, and
`a log₂ a + b log₂ b + 2 min a b ≤ (a + b) log₂ (a + b)`.

Read through the total influence, which counts the edges leaving `A`, this is the
**edge-isoperimetric inequality**: a Boolean function with
`α = min (Pr[f = 1], Pr[f = -1])` has `2 α log₂ (1 / α) ≤ I[f]`
(`BitString.two_mul_min_mul_logb_inv_le_totalInfluence`) [O'Donnell, Theorem 2.39][ODonnell2014].
As in Proposition 1.15 (`BitString.two_mul_min_le_expect_sub_expect_sq_signVal`), `α` is
written as the relative Hamming distance to the nearer constant: `signVal false = 1`, so
`Pr[f = 1]` is `hammingDist f (fun _ => true) / 2 ^ n`, and `log` is `log₂` as in the book.
Equivalently, the bound holds with `α` the relative distance to either constant
(`BitString.two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence`). The book notes the bound
is optimal for `α` a power of `1/2` (subcubes); the tests check the conjunction of two bits. The
book states the theorem without proof; its Exercises 10.25 and 11.21 derive weaker forms.

## Main results

* `Cslib.BitString.sum_card_filter_update_mem_le`: a set of the cube spans at most
  `|A| log₂ |A|` directed edges.
* `Cslib.BitString.two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence`,
  `Cslib.BitString.two_mul_min_mul_logb_inv_le_totalInfluence`: the edge-isoperimetric
  inequality.

## Usage

Apply `two_mul_min_mul_logb_inv_le_totalInfluence f` to `f : (ι → Bool) → Bool` over any finite
coordinate type `ι`. Its `α` is the same minimum of relative Hamming distances as in
`two_mul_min_le_expect_sub_expect_sq_signVal`, so the two bounds compose. When the distance to
one constant `b` is known, `two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence f b` gives the
bound for that distance directly; `b = true` gives the book's `Pr[f = 1]`. For a set `A` of the
cube, `sum_card_filter_update_mem_le A` bounds the directed edges inside `A`. The checked clients in
[CslibFrontierTests/BooleanAnalysisEdgeIsoperimetry.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisEdgeIsoperimetry.lean)
count the edges spanned by the square and by three of its corners, apply the inequality to a
dictator on three bits, and show it is attained by the conjunction of two bits, with `α = 1/4` and
total influence `1`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function

/-! ### An inequality of entropies -/

/-- `n log₂ n ≥ 0` for a natural number `n`. -/
private theorem natCast_mul_logb_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * Real.logb 2 n :=
  mul_nonneg n.cast_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Real.log_nonneg one_le_two))

/-- **The splitting inequality**: `a log₂ a + b log₂ b + 2 min a b ≤ (a + b) log₂ (a + b)` for
`a, b ≥ 0`. -/
private theorem mul_logb_add_mul_logb_add_two_mul_min_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.logb 2 a + b * Real.logb 2 b + 2 * min a b ≤ (a + b) * Real.logb 2 (a + b) := by
  wlog hab : a ≤ b generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    rwa [min_comm, add_comm b a, add_comm (b * _)] at this
  rw [min_eq_left hab]
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have hb' : 0 < b := ha.trans_le hab
  have h₁ : 1 ≤ Real.logb 2 ((a + b) / a) :=
    (Real.le_logb_iff_rpow_le one_lt_two (by positivity)).2 <| by
      rw [Real.rpow_one, le_div_iff₀ ha]; linarith
  have h₂ : a / b ≤ Real.logb 2 ((a + b) / b) :=
    (Real.le_logb_iff_rpow_le one_lt_two (by positivity)).2 <| by
      have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num)
        (div_nonneg ha.le hb'.le) ((div_le_one hb').2 hab)
      rw [add_div, div_self hb'.ne']
      norm_num at this ⊢
      linarith
  have hsplit (c : ℝ) (hc : 0 < c) :
      Real.logb 2 (a + b) = Real.logb 2 c + Real.logb 2 ((a + b) / c) := by
    rw [Real.logb_div (by positivity) hc.ne']
    ring
  have hA := hsplit a ha
  have hB := hsplit b hb'
  have : b * (a / b) = a := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h₁ ha.le, mul_le_mul_of_nonneg_left h₂ hb'.le]

/-! ### Edges spanned by a set of the cube -/

/-- The directed edges spanned by `{g = true}`: the pairs `(x, i)` with `x` and its neighbour across
coordinate `i` both in the set. -/
private noncomputable def edges {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) : ℝ :=
  ∑ x, ∑ i, if g x = true ∧ g (update x i !x i) = true then 1 else 0

/-- The size of `{g = true}`. -/
private noncomputable def size {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) : ℝ :=
  ∑ x, if g x = true then 1 else 0

private theorem size_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → Bool) :
    size g = #{x | g x = true} := by
  simp only [size, sum_boole]

/-- The induction on the dimension, on `Fin n`. -/
private theorem edges_le_fin : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool),
    edges g ≤ size g * Real.logb 2 (size g)
  | 0, g => by
    rw [size_eq_card]
    simpa [edges] using natCast_mul_logb_nonneg _
  | n + 1, g => by
    set g₀ : (Fin n → Bool) → Bool := fun y => g (Fin.cons false y)
    set g₁ : (Fin n → Bool) → Bool := fun y => g (Fin.cons true y)
    have hsize : size g = size g₀ + size g₁ := by
      unfold size
      exact Fin.sum_univ_cons_bool _
    have hedges : edges g = edges g₀ + edges g₁ +
        2 * ∑ y, if g₀ y = true ∧ g₁ y = true then (1 : ℝ) else 0 := by
      simp only [edges, Fin.sum_univ_cons_bool, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.update_cons_zero, Fin.cons_succ, ← Fin.cons_update, Bool.not_false, Bool.not_true,
        sum_add_distrib, g₀, g₁]
      rw [sum_congr rfl fun y _ => (if_congr and_comm rfl rfl :
        (if g (Fin.cons true y) = true ∧ g (Fin.cons false y) = true then (1 : ℝ) else 0) = _)]
      ring
    have hc₀ : (∑ y, if g₀ y = true ∧ g₁ y = true then (1 : ℝ) else 0) ≤ size g₀ := by
      unfold size
      exact sum_le_sum fun y _ => by split_ifs <;> simp_all
    have hc₁ : (∑ y, if g₀ y = true ∧ g₁ y = true then (1 : ℝ) else 0) ≤ size g₁ := by
      unfold size
      exact sum_le_sum fun y _ => by split_ifs <;> simp_all
    have h₀ := edges_le_fin n g₀
    have h₁ := edges_le_fin n g₁
    have hs₀ : 0 ≤ size g₀ := by rw [size_eq_card]; positivity
    have hs₁ : 0 ≤ size g₁ := by rw [size_eq_card]; positivity
    have hsplit := mul_logb_add_mul_logb_add_two_mul_min_le hs₀ hs₁
    rw [hedges, hsize]
    have := le_min hc₀ hc₁
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relabelling the coordinates preserves the edges spanned by a set. -/
private theorem edges_le (g : (ι → Bool) → Bool) : edges g ≤ size g * Real.logb 2 (size g) := by
  set e := Fintype.equivFin ι
  set E := (e.arrowCongr (Equiv.refl Bool)).symm
  have hE (y) : E y = y ∘ e := rfl
  have hsize : size (g ∘ E) = size g := Fintype.sum_equiv E _ _ fun _ => rfl
  have hedges : edges (g ∘ E) = edges g :=
    Fintype.sum_equiv E _ _ fun y => Fintype.sum_equiv e.symm _ _ fun j => by
      simp only [comp_apply, hE, update_comp_equiv, e.apply_symm_apply]
  rw [← hsize, ← hedges]
  exact edges_le_fin _ _

/-- **Sets of the cube span few edges**: summing over the points `x` of a set `A` of the Hamming
cube the number of neighbours of `x` in `A` gives at most `|A| log₂ |A|`. -/
theorem sum_card_filter_update_mem_le (A : Finset (ι → Bool)) :
    ∑ x ∈ A, (#{i | update x i (!x i) ∈ A} : ℝ) ≤ #A * Real.logb 2 #A := by
  have h := edges_le (fun x => decide (x ∈ A))
  simp only [edges, size_eq_card, decide_eq_true_eq, filter_mem_eq_inter, univ_inter, ite_and,
    sum_ite_irrel, sum_const_zero, Fintype.sum_ite_mem, ← natCast_card_filter] at h
  exact h

/-! ### The edge-isoperimetric inequality -/

/-- **The edge-isoperimetric inequality**, for either constant: a Boolean function read as signs
at relative Hamming distance `α` from the constant `b` has `2 α log₂ (1 / α) ≤ I[f]`, a form of
[O'Donnell, Theorem 2.39][ODonnell2014]. Here `α = Pr[f ≠ b] = Pr[f = !b]`. -/
theorem two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence (f : (ι → Bool) → Bool) (b : Bool) :
    2 * ((hammingDist f (fun _ => b) : ℝ) / 2 ^ Fintype.card ι) *
        Real.logb 2 ((hammingDist f (fun _ => b) : ℝ) / 2 ^ Fintype.card ι)⁻¹ ≤
      totalInfluence (fun x => signVal (f x)) := by
  set g : (ι → Bool) → Bool := fun x => decide (f x ≠ b)
  set n := Fintype.card ι
  have hcard : (Fintype.card (ι → Bool) : ℝ) = 2 ^ n := by simp [n]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hdist : (hammingDist f (fun _ => b) : ℝ) = size g := by
    rw [size_eq_card]
    simp [g, hammingDist]
  -- The total influence counts the edges leaving `{g = true}`, from both sides.
  have hflip (x : ι → Bool) (i : ι) : (if f (update x i !x i) = f x then (0 : ℝ) else 1) =
      (if g x = true then 1 else 0) + (if g (update x i !x i) = true then 1 else 0) -
        2 * (if g x = true ∧ g (update x i !x i) = true then 1 else 0) := by
    simp only [g, decide_eq_true_eq]
    cases f x <;> cases f (update x i !x i) <;> cases b <;> norm_num
  have hI : totalInfluence (fun x => signVal (f x)) = 2 * (n * size g - edges g) / 2 ^ n := by
    simp only [totalInfluence, influence_signVal, Fintype.expect_eq_sum_div_card, hcard,
      ← sum_div]
    congr 1
    rw [show edges g = ∑ i, ∑ x,
        (if g x = true ∧ g (update x i !x i) = true then (1 : ℝ) else 0) from sum_comm]
    simp only [hflip, sum_sub_distrib, sum_add_distrib, ← mul_sum,
      sum_update_not (F := fun y => if g y = true then (1 : ℝ) else 0), sum_const, card_univ,
      nsmul_eq_mul, size]
    ring
  rcases (show (0 : ℝ) ≤ size g by rw [size_eq_card]; positivity).eq_or_lt with hs | hs
  · rw [hdist, ← hs, zero_div, mul_zero, zero_mul]
    exact totalInfluence_nonneg _
  have hE := edges_le g
  rw [hI, hdist, inv_div, Real.logb_div h2.ne' hs.ne', Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]
  rw [mul_one, mul_div_assoc', div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by linarith) h2.le

/-- **The edge-isoperimetric inequality**: a Boolean function read as signs with
`α = min (Pr[f = 1], Pr[f = -1])` has `2 α log₂ (1 / α) ≤ I[f]`
[O'Donnell, Theorem 2.39][ODonnell2014]. As in
`BitString.two_mul_min_le_expect_sub_expect_sq_signVal`, `α` is the relative Hamming distance to
the nearer constant. -/
theorem two_mul_min_mul_logb_inv_le_totalInfluence (f : (ι → Bool) → Bool) :
    2 * min ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
          (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) *
        Real.logb 2 (min ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
          (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι))⁻¹ ≤
      totalInfluence (fun x => signVal (f x)) := by
  rcases min_choice ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
      (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) with h | h <;>
    rw [h]
  · exact two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence f false
  · exact two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence f true

end Cslib.BitString
