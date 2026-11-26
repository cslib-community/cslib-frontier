/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/LinearProgramming.lean`)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear-programming duality over linearly ordered fields

For a matrix `A : Matrix ι κ K`, a right-hand side `b` and an objective `c` over a linearly
ordered field `K`, the primal linear program in inequality form maximizes `c ⬝ᵥ x` subject to
`A *ᵥ x ≤ b`. Its dual minimizes `y ⬝ᵥ b` subject to `0 ≤ y` and `y ᵥ* A = c`. The proofs use
Fourier–Motzkin elimination (`Matrix.FourierMotzkin.exists_projection`) and Farkas' lemma
(`Matrix.not_exists_mulVec_le_iff`), so they hold over every linearly ordered field, including
`ℚ`. See also [DvorakKolmogorov2024] for an independent Lean 4 formalization of
linear-programming duality over linearly ordered fields. The closed `leanprover-community/mathlib4`
pull requests 7386, 9693, 10026 and 10159 (opened 2023–24) take other approaches to linear
programming; nothing here is copied from them or from [DvorakKolmogorov2024].

## Main results

* `Matrix.dotProduct_le_dotProduct_add_parts_of_mulVec_le`: residual-corrected weak duality,
  with bounds required only on the relevant end of each variable's range.
* `Matrix.dotProduct_le_dotProduct_add_max_of_mulVec_le`: residual-corrected weak duality
  for bounded variables.
* `Matrix.dotProduct_le_dotProduct_of_mulVec_le`: weak duality.
* `Matrix.exists_dual_eq_of_bddAbove`: a feasible primal with objective bounded above has a
  primal solution and a dual solution of equal value.
* `Matrix.exists_isGreatest_of_bddAbove`: a feasible primal with objective bounded above attains
  its maximum.
* `Matrix.exists_isGreatest_isLeast_dotProduct`: strong duality. If both programs are feasible,
  both optima are attained and they are equal.
* `Matrix.bddAbove_image_dotProduct_iff`, `Matrix.bddBelow_image_dotProduct_iff`: a feasible
  program is bounded iff the other program is feasible, so a feasible program whose dual is
  infeasible is unbounded.
* `Matrix.dotProduct_eq_dotProduct_iff_of_mulVec_le`: complementary slackness.
* `Matrix.exists_dual_le_of_forall_le`: the affine Farkas lemma.
* `Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg`: strong duality for the canonical pair
  `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}` and `min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}`.

## References

* [DvorakKolmogorov2024]
* [MatousekGartner2007], Chapter 6
* [Schrijver1986], Sections 7.4, 7.6 and 7.9
-/

public section

open Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

section OrderedRing

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Residual-corrected weak duality. For the residual `d = c - y ᵥ* A`, only the upper
bound on a variable with positive residual and the lower bound on a variable with negative
residual are needed. This is the exact-coefficient step towards interval LP bounds (#6981). -/
theorem dotProduct_le_dotProduct_add_parts_of_mulVec_le {A : Matrix ι κ K}
    {b : ι → K} {c x l u : κ → K} {y : ι → K}
    (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y)
    (hl : ∀ j, (c - y ᵥ* A) j < 0 → l j ≤ x j)
    (hu : ∀ j, 0 < (c - y ᵥ* A) j → x j ≤ u j) :
    c ⬝ᵥ x ≤ y ⬝ᵥ b +
      ((c - y ᵥ* A)⁺ ⬝ᵥ u - (c - y ᵥ* A)⁻ ⬝ᵥ l) := by
  let d := c - y ᵥ* A
  have hpos : d⁺ ⬝ᵥ x ≤ d⁺ ⬝ᵥ u := Finset.sum_le_sum fun j _ => by
    rw [Pi.posPart_apply]
    by_cases hj : 0 < d j
    · exact mul_le_mul_of_nonneg_left (hu j hj) (posPart_nonneg _)
    · simp [posPart_eq_zero.mpr (le_of_not_gt hj)]
  have hneg : d⁻ ⬝ᵥ l ≤ d⁻ ⬝ᵥ x := Finset.sum_le_sum fun j _ => by
    rw [Pi.negPart_apply]
    by_cases hj : d j < 0
    · exact mul_le_mul_of_nonneg_left (hl j hj) (negPart_nonneg _)
    · simp [negPart_eq_zero.mpr (le_of_not_gt hj)]
  have hd : d ⬝ᵥ x = d⁺ ⬝ᵥ x - d⁻ ⬝ᵥ x := by rw [← sub_dotProduct, posPart_sub_negPart]
  have hres : d ⬝ᵥ x = c ⬝ᵥ x - y ⬝ᵥ (A *ᵥ x) := by
    rw [show d = c - y ᵥ* A from rfl, sub_dotProduct, ← dotProduct_mulVec]
  linarith [dotProduct_le_dotProduct_of_nonneg_left hx hy]

/-- With two-sided variable bounds, the residual correction can equivalently be written
as the sum of the worse endpoint products. The vector `y` need not be dual feasible. -/
theorem dotProduct_le_dotProduct_add_max_of_mulVec_le {A : Matrix ι κ K}
    {b : ι → K} {c x l u : κ → K} {y : ι → K}
    (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hl : l ≤ x) (hu : x ≤ u) :
    c ⬝ᵥ x ≤ y ⬝ᵥ b +
      ∑ j, max ((c - y ᵥ* A) j * l j) ((c - y ᵥ* A) j * u j) := by
  refine (dotProduct_le_dotProduct_add_parts_of_mulVec_le (c := c) hx hy
    (fun j _ => hl j) (fun j _ => hu j)).trans_eq (congrArg (y ⬝ᵥ b + ·) ?_)
  simp only [dotProduct, ← Finset.sum_sub_distrib, Pi.posPart_apply, Pi.negPart_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases le_total 0 ((c - y ᵥ* A) j) with hj | hj
  · rw [posPart_eq_self.mpr hj, negPart_eq_zero.mpr hj, zero_mul, sub_zero,
      max_eq_right (mul_le_mul_of_nonneg_left ((hl j).trans (hu j)) hj)]
  · rw [posPart_eq_zero.mpr hj, negPart_eq_neg.mpr hj, zero_mul, zero_sub, neg_mul, neg_neg,
      max_eq_left (mul_le_mul_of_nonpos_left ((hl j).trans (hu j)) hj)]

end OrderedRing

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Weak duality**: the value of a primal solution `A *ᵥ x ≤ b` is at most the value of any dual
solution `0 ≤ y`, `y ᵥ* A = c` [Schrijver1986, Section 7.4]. -/
theorem dotProduct_le_dotProduct_of_mulVec_le {A : Matrix ι κ K} {b : ι → K} {c : κ → K}
    {x : κ → K} {y : ι → K} (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hyA : y ᵥ* A = c) :
    c ⬝ᵥ x ≤ y ⬝ᵥ b := by
  simpa using dotProduct_le_dotProduct_add_parts_of_mulVec_le (c := c) (l := 0) (u := 0) hx hy
    (fun _ hj => by simp [hyA] at hj)
    (fun _ hj => by simp [hyA] at hj)

/-- A linear objective bounded above on a nonempty polyhedron `A *ᵥ x ≤ b` attains its maximum at
a point `x`, certified by a dual solution `y` of the same value [Schrijver1986, Section 7.4]. -/
theorem exists_dual_eq_of_bddAbove (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hbdd : BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b})) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ y ᵥ* A = c ∧ y ⬝ᵥ b = c ⬝ᵥ x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hP
  obtain ⟨M, hM⟩ := hbdd
  -- project the system `A x ≤ b`, `t - c ⬝ᵥ x ≤ 0` in the variables `x` and `t` onto `t`
  let A' : Matrix (ι ⊕ Unit) κ K := fromRows A (replicateRow Unit (-c))
  let B' : Matrix (ι ⊕ Unit) Unit K := fromRows 0 1
  let b' : ι ⊕ Unit → K := Sum.elim b 0
  obtain ⟨ρ, _, T, hT, hTA, hiff⟩ := FourierMotzkin.exists_projection A' B' b'
  set β : ρ → K := fun r => T r (.inr ())
  set γ : ρ → K := T *ᵥ b'
  have hTB : ∀ t : K, (T * B') *ᵥ (fun _ => t) = fun r => β r * t := by
    intro t
    rw [← mulVec_mulVec, fromRows_mulVec, zero_mulVec, one_mulVec]
    funext r
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, PUnit.default_eq_unit, β]
  have hfeas (t : K) : (∃ x, A *ᵥ x ≤ b ∧ t ≤ c ⬝ᵥ x) ↔ ∀ r, β r * t ≤ γ r := by
    refine Iff.trans (exists_congr fun x => ?_) (hTB t ▸ hiff fun _ => t)
    rw [fromRows_mulVec, fromRows_mulVec, zero_mulVec, one_mulVec, ← Sum.elim_add_add,
      Sum.elim_le_elim_iff, add_zero, replicateRow_mulVec_eq_const]
    refine and_congr Iff.rfl ?_
    simp only [Pi.le_def, forall_const, Pi.zero_apply, Pi.add_apply, Function.const_apply,
      neg_dotProduct, neg_add_le_iff_le_add, add_zero]
  -- some row of the projection bounds `t` from above
  have h₀ := (hfeas (c ⬝ᵥ x₀)).1 ⟨x₀, hx₀, le_rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r, 0 < β r := by
    by_contra! hneg
    obtain ⟨x, hx, htx⟩ := (hfeas (max (c ⬝ᵥ x₀) M + 1)).2 fun r =>
      (mul_le_mul_of_nonpos_left (by linarith [le_max_left (c ⬝ᵥ x₀) M]) (hneg r)).trans (h₀ r)
    linarith [hM ⟨x, hx, rfl⟩, le_max_right (c ⬝ᵥ x₀) M]
  have : Nonempty {r // 0 < β r} := ⟨⟨r₀, hr₀⟩⟩
  obtain ⟨⟨r, hr⟩, hmin⟩ := Finite.exists_min fun r : {r // 0 < β r} => γ r / β r
  have ht₀ : c ⬝ᵥ x₀ ≤ γ r / β r := (le_div_iff₀ hr).2 (mul_comm (c ⬝ᵥ x₀) _ ▸ h₀ r)
  obtain ⟨x, hx, htx⟩ := (hfeas (γ r / β r)).2 fun s => by
    rcases lt_or_ge 0 (β s) with hs | hs
    · exact mul_comm (β s) _ ▸ (le_div_iff₀ hs).1 (hmin ⟨s, hs⟩)
    · exact (mul_le_mul_of_nonpos_left ht₀ hs).trans (h₀ s)
  have hxt : c ⬝ᵥ x ≤ γ r / β r :=
    (le_div_iff₀ hr).2 (mul_comm (c ⬝ᵥ x) _ ▸ (hfeas (c ⬝ᵥ x)).1 ⟨x, hx, le_rfl⟩ r)
  -- the row `r` of `T`, rescaled, is the dual solution
  set u : ι → K := fun i => T r (.inl i)
  have hγ : γ r = u ⬝ᵥ b := by
    simp only [γ, b', u, mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have huA : u ᵥ* A = β r • c := by
    have h : T r ᵥ* A' = 0 := congr_fun hTA r
    rw [vecMul_fromRows] at h
    ext j
    have hj := congr_fun h j
    simp only [Pi.add_apply, Pi.zero_apply, vecMul, dotProduct, replicateRow_apply,
      Finset.univ_unique, Finset.sum_singleton, Function.comp_apply, PUnit.default_eq_unit,
      Pi.neg_apply, mul_neg, Pi.smul_apply, smul_eq_mul, u, β] at hj ⊢
    linarith
  refine ⟨x, (β r)⁻¹ • u, hx, fun i => smul_nonneg (inv_nonneg.2 hr.le) (hT r _), ?_, ?_⟩
  · rw [smul_vecMul, huA, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rw [smul_dotProduct, ← hγ, smul_eq_mul, inv_mul_eq_div]
    exact le_antisymm htx hxt

omit [Fintype ι] in
/-- A linear objective bounded above on a nonempty polyhedron attains its supremum
[Schrijver1986, Section 7.4]. -/
theorem exists_isGreatest_of_bddAbove [Finite ι] (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hbdd : BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b})) :
    ∃ x, A *ᵥ x ≤ b ∧ IsGreatest ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) (c ⬝ᵥ x) := by
  have := Fintype.ofFinite ι
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ := exists_dual_eq_of_bddAbove A b c hP hbdd
  exact ⟨x, hx, ⟨x, hx, rfl⟩,
    Set.forall_mem_image.2 fun _ hx' => hxy ▸ dotProduct_le_dotProduct_of_mulVec_le hx' hy hyA⟩

/-- **Strong duality**: if the primal `max {c ⬝ᵥ x | A *ᵥ x ≤ b}` and the dual
`min {y ⬝ᵥ b | 0 ≤ y, y ᵥ* A = c}` are both feasible, then both optima are attained and equal
[Schrijver1986, Corollary 7.1g]. -/
theorem exists_isGreatest_isLeast_dotProduct (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) v ∧
      IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) v := by
  obtain ⟨y₀, hy₀, hy₀A⟩ := hD
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ := exists_dual_eq_of_bddAbove A b c hP
    ⟨y₀ ⬝ᵥ b, Set.forall_mem_image.2 fun _ hx => dotProduct_le_dotProduct_of_mulVec_le hx hy₀ hy₀A⟩
  exact ⟨c ⬝ᵥ x,
    ⟨⟨x, hx, rfl⟩,
      Set.forall_mem_image.2 fun _ hx' => hxy ▸ dotProduct_le_dotProduct_of_mulVec_le hx' hy hyA⟩,
    ⟨⟨y, ⟨hy, hyA⟩, hxy⟩,
      Set.forall_mem_image.2 fun _ h => dotProduct_le_dotProduct_of_mulVec_le hx h.1 h.2⟩⟩

/-- A feasible primal program is bounded above iff its dual is feasible. In particular a feasible
primal program with infeasible dual is unbounded [Schrijver1986, Section 7.4]. -/
theorem bddAbove_image_dotProduct_iff (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hP : ∃ x, A *ᵥ x ≤ b) :
    BddAbove ((c ⬝ᵥ ·) '' {x | A *ᵥ x ≤ b}) ↔ ∃ y, 0 ≤ y ∧ y ᵥ* A = c := by
  refine ⟨fun h => ?_, fun ⟨y, hy, hyA⟩ =>
    ⟨y ⬝ᵥ b, Set.forall_mem_image.2 fun _ hx => dotProduct_le_dotProduct_of_mulVec_le hx hy hyA⟩⟩
  obtain ⟨_, y, -, hy, hyA, -⟩ := exists_dual_eq_of_bddAbove A b c hP h
  exact ⟨y, hy, hyA⟩

/-- A feasible dual program is bounded below iff the primal is feasible. In particular a feasible
dual program with infeasible primal is unbounded [Schrijver1986, Section 7.4]. -/
theorem bddBelow_image_dotProduct_iff (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) :
    BddBelow ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) ↔ ∃ x, A *ᵥ x ≤ b := by
  refine ⟨fun ⟨m, hm⟩ => ?_, fun ⟨x, hx⟩ => ⟨c ⬝ᵥ x, fun _ ⟨y, ⟨hy, hyA⟩, hyb⟩ =>
    hyb ▸ dotProduct_le_dotProduct_of_mulVec_le hx hy hyA⟩⟩
  · by_contra hP
    -- move along the Farkas ray `y₀ + s • z` until the value drops below `m`
    obtain ⟨z, hz, hzA, hzb⟩ := (not_exists_mulVec_le_iff A b).1 hP
    obtain ⟨y₀, hy₀, hy₀A⟩ := hD
    set s := (|y₀ ⬝ᵥ b - m| + 1) / -(z ⬝ᵥ b)
    have hs : s * -(z ⬝ᵥ b) = |y₀ ⬝ᵥ b - m| + 1 := div_mul_cancel₀ _ (by linarith)
    have hs0 : 0 ≤ s := div_nonneg (by positivity) (by linarith)
    have := hm ⟨y₀ + s • z, ⟨add_nonneg hy₀ (smul_nonneg hs0 hz), by
      rw [add_vecMul, smul_vecMul, hzA, smul_zero, add_zero, hy₀A]⟩, rfl⟩
    change m ≤ (y₀ + s • z) ⬝ᵥ b at this
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
    linarith [le_abs_self (y₀ ⬝ᵥ b - m)]

omit [Fintype κ] in
/-- A dual objective bounded below on a nonempty dual polyhedron attains its infimum
[Schrijver1986, Section 7.4]. -/
theorem exists_isLeast_of_bddBelow [Finite κ] (A : Matrix ι κ K) (b : ι → K) (c : κ → K)
    (hD : ∃ y, 0 ≤ y ∧ y ᵥ* A = c) (hbdd : BddBelow ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c})) :
    ∃ v, IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ y ᵥ* A = c}) v := by
  have := Fintype.ofFinite κ
  exact (exists_isGreatest_isLeast_dotProduct A b c
    ((bddBelow_image_dotProduct_iff A b c hD).1 hbdd) hD).imp fun _ h => h.2

/-- **Complementary slackness**: a primal solution `x` and a dual solution `y` have equal values
iff every constraint `i` with `y i ≠ 0` is tight at `x` [Schrijver1986, Section 7.9]. -/
theorem dotProduct_eq_dotProduct_iff_of_mulVec_le {A : Matrix ι κ K} {b : ι → K} {c : κ → K}
    {x : κ → K} {y : ι → K} (hx : A *ᵥ x ≤ b) (hy : 0 ≤ y) (hyA : y ᵥ* A = c) :
    c ⬝ᵥ x = y ⬝ᵥ b ↔ ∀ i, y i = 0 ∨ (A *ᵥ x) i = b i := by
  have hgap : y ⬝ᵥ b - c ⬝ᵥ x = ∑ i, y i * (b i - (A *ᵥ x) i) := by
    rw [← hyA, ← dotProduct_mulVec, ← dotProduct_sub]; rfl
  rw [eq_comm, ← sub_eq_zero, hgap,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hy i) (sub_nonneg.2 (hx i))]
  simp [mul_eq_zero, sub_eq_zero, eq_comm]

/-- **Affine Farkas lemma**: if the inequality `c ⬝ᵥ x ≤ δ` holds on a nonempty polyhedron
`A *ᵥ x ≤ b`, then it is implied by a nonnegative combination of the constraints
[Schrijver1986, Corollary 7.1h]. -/
theorem exists_dual_le_of_forall_le (A : Matrix ι κ K) (b : ι → K) (c : κ → K) (δ : K)
    (hP : ∃ x, A *ᵥ x ≤ b) (h : ∀ x, A *ᵥ x ≤ b → c ⬝ᵥ x ≤ δ) :
    ∃ y, 0 ≤ y ∧ y ᵥ* A = c ∧ y ⬝ᵥ b ≤ δ := by
  obtain ⟨x, y, hx, hy, hyA, hxy⟩ :=
    exists_dual_eq_of_bddAbove A b c hP ⟨δ, by rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩
  exact ⟨y, hy, hyA, hxy ▸ h x hx⟩

/-! ### The canonical pair `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}`, `min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}` -/

/-- **Weak duality** for the canonical pair [MatousekGartner2007, Chapter 6]. -/
theorem dotProduct_le_dotProduct_of_nonneg_of_mulVec_le {A : Matrix ι κ K} {b : ι → K}
    {c : κ → K} {x : κ → K} {y : ι → K} (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ b) (hy : 0 ≤ y)
    (hc : c ≤ y ᵥ* A) : c ⬝ᵥ x ≤ y ⬝ᵥ b := by
  simpa using dotProduct_le_dotProduct_add_parts_of_mulVec_le (c := c) (l := 0) (u := 0) hAx hy
    (fun j _ => hx j) fun j hj => (not_lt_of_ge (sub_nonpos.mpr (hc j)) hj).elim

omit [Fintype ι] in
private theorem fromRows_neg_one_mulVec_le_iff [DecidableEq κ] (A : Matrix ι κ K) (b : ι → K)
    (x : κ → K) : fromRows A (-1 : Matrix κ κ K) *ᵥ x ≤ Sum.elim b 0 ↔ A *ᵥ x ≤ b ∧ 0 ≤ x := by
  rw [fromRows_mulVec, Sum.elim_le_elim_iff, neg_mulVec, one_mulVec, neg_nonpos]

/-- **Strong duality** for the canonical pair `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}` and
`min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}`: if both are feasible, both optima are attained and equal
[MatousekGartner2007, Chapter 6]. -/
theorem exists_isGreatest_isLeast_dotProduct_of_nonneg (A : Matrix ι κ K) (b : ι → K)
    (c : κ → K) (hP : ∃ x, 0 ≤ x ∧ A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ c ≤ y ᵥ* A) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x ≤ b}) v ∧
      IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ c ≤ y ᵥ* A}) v := by
  classical
  obtain ⟨x₀, hx₀, hAx₀⟩ := hP
  obtain ⟨y₀, hy₀, hcy₀⟩ := hD
  obtain ⟨x, w, hx, hw, hwM, hxw⟩ :=
    exists_dual_eq_of_bddAbove (fromRows A (-1 : Matrix κ κ K)) (Sum.elim b 0) c
    ⟨x₀, (fromRows_neg_one_mulVec_le_iff A b x₀).2 ⟨hAx₀, hx₀⟩⟩
    ⟨y₀ ⬝ᵥ b, fun _ ⟨x, hx, hxc⟩ => ((fromRows_neg_one_mulVec_le_iff A b x).1 hx).elim
      fun hAx hx => hxc ▸ dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx hy₀ hcy₀⟩
  obtain ⟨hAx, hx⟩ := (fromRows_neg_one_mulVec_le_iff A b x).1 hx
  have hc : c ≤ (w ∘ Sum.inl) ᵥ* A := fun k => by
    rw [← hwM, vecMul_fromRows, vecMul_neg, vecMul_one, Pi.add_apply, Pi.neg_apply]
    exact add_le_of_nonpos_right (neg_nonpos.2 (hw _))
  have hval : (w ∘ Sum.inl) ⬝ᵥ b = c ⬝ᵥ x := by
    simpa [dotProduct] using hxw
  refine ⟨c ⬝ᵥ x, ⟨⟨x, ⟨hx, hAx⟩, rfl⟩, ?_⟩,
    ⟨⟨w ∘ Sum.inl, ⟨fun i => hw _, hc⟩, hval⟩, ?_⟩⟩
  · rintro _ ⟨x', ⟨hx', hAx'⟩, rfl⟩
    exact hval ▸ dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx' hAx' (fun i => hw _) hc
  · rintro _ ⟨y', ⟨hy', hc'⟩, rfl⟩
    exact dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx hy' hc'

end Matrix
