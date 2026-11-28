/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Random vectors orthogonal to a fixed string determine it

Let `a ∈ GF(2)^n` be nonzero and draw `n - 1` vectors `y_1, …, y_{n-1}` independently and uniformly
from the strings orthogonal to `a`, i.e. uniformly among the tuples with `y_i ⬝ a = 0` for every
`i`. With probability at least `1 / 4`, the only strings orthogonal to all of them are `0` and `a`
(`Cslib.LinearAlgebra.one_div_four_le_card_determines_div_card`).

This is Exercise 5 of Chapter 20 of the Arora–Barak web draft (2007-01-08, p. 431/447), which the
text uses for Simon's algorithm (p. 422/438). The exercise asks for probability at least `1 / 10`;
`1 / 4 ≥ 1 / 10`. The exercise does not exclude `a = 0`, but for `a = 0` the claim fails: `n - 1`
vectors always have a nonzero common orthogonal string when `n ≥ 1`. So the statement assumes
`a ≠ 0`.

**Proof.** The dot product is a nondegenerate reflexive bilinear form on `GF(2)^n`, so Mathlib's
orthogonality API applies (`LinearMap.BilinForm.orthogonal`). The strings orthogonal to `a` form
the orthogonal complement `a^⊥` of `span {a}`, of dimension `n - 1`
(`LinearMap.BilinForm.finrank_orthogonal`). By the count of linearly independent families over a
finite field (`card_linearIndependent`), exactly `∏_{i < n - 1} (2^{n-1} - 2^i)` of the
`2^{(n-1)^2}` tuples are linearly independent. Independent tuples span `a^⊥`, so every string `w`
orthogonal to all of them lies in `(a^⊥)^⊥ = span {a} = {0, a}`
(`LinearMap.BilinForm.orthogonal_orthogonal`). Finally
`∏_{i < n - 1} (1 - 2^{i - (n-1)}) = ∏_{j = 1}^{n - 1} (1 - 2^{-j}) ≥ 1 / 4`.

## Main results

* `Cslib.LinearAlgebra.one_div_four_le_card_determines_div_card`: Arora–Barak, Exercise 20.5.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007-01-08,
  Exercise 20.5][AroraBarak07]
-/

public section

namespace Cslib.LinearAlgebra

open Finset Module Matrix

/-- `∏_{j = 1}^m (1 - 2^{-j}) ≥ 1 / 4 + 2^{-(m+1)}` for `m ≥ 1`. -/
private theorem prod_one_sub_inv_two_pow_ge (m : ℕ) (hm : 1 ≤ m) :
    1 / 4 + 1 / 2 ^ (m + 1) ≤ ∏ j ∈ range m, (1 - 1 / (2 : ℝ) ^ (j + 1)) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [prod_range_succ]
    have hp : (0 : ℝ) ≤ 1 - 1 / 2 ^ (m + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hy : (1 : ℝ) / 2 ^ (m + 1) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc 1 / 4 + 1 / (2 : ℝ) ^ (m + 1 + 1)
        ≤ (1 / 4 + 1 / 2 ^ (m + 1)) * (1 - 1 / 2 ^ (m + 1)) := by
          have h2 : (1 : ℝ) / 2 ^ (m + 1 + 1) = 1 / 2 ^ (m + 1) / 2 := by
            rw [pow_succ]; field_simp
          rw [h2]
          nlinarith [hy, show (0 : ℝ) ≤ 1 / 2 ^ (m + 1) by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hp

/-- `∏_{i < m} (1 - 2^i / 2^m) ≥ 1 / 4`: the fraction of linearly independent `m`-tuples in an
`m`-dimensional space over `GF(2)`. -/
private theorem one_div_four_le_prod_one_sub (m : ℕ) :
    (1 / 4 : ℝ) ≤ ∏ i ∈ range m, (1 - (2 : ℝ) ^ i / 2 ^ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  have h : ∏ i ∈ range m, (1 - (2 : ℝ) ^ i / 2 ^ m) =
      ∏ j ∈ range m, (1 - 1 / (2 : ℝ) ^ (j + 1)) := by
    rw [← prod_range_reflect]
    refine prod_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    congr 1
    omega
  rw [h]
  exact le_trans (le_add_of_nonneg_right (by positivity)) (prod_one_sub_inv_two_pow_ge m hm)

variable {n : ℕ}

/-- The dot product on `GF(2)^n` as a bilinear form. -/
private abbrev dotForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

/-- The dot product is nondegenerate (`dotProduct_eq_zero`), unlike `a ⬝ᵥ a ≠ 0`, which fails for
nonzero strings of even weight in characteristic `2`. -/
private theorem nondegenerate_dotForm : (dotForm n).Nondegenerate :=
  ⟨fun x hx => dotProduct_eq_zero x hx,
    fun y hy => dotProduct_eq_zero y fun x => by rw [dotProduct_comm]; exact hy x⟩

private theorem isRefl_dotForm : (dotForm n).IsRefl := fun x y h => by
  simpa [dotProduct_comm] using h

/-- The strings orthogonal to `a`: the orthogonal complement of `span {a}`. -/
private abbrev orth (a : Fin n → ZMod 2) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  (dotForm n).orthogonal (ZMod 2 ∙ a)

private theorem mem_orth {a y : Fin n → ZMod 2} : y ∈ orth a ↔ y ⬝ᵥ a = 0 := by
  rw [orth, LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker, LinearMap.mem_ker,
    dotProduct_comm]
  rfl

/-- For nonzero `a`, the strings orthogonal to `a` form a subspace of dimension `n - 1`. -/
private theorem finrank_orth {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    finrank (ZMod 2) (orth a) = n - 1 := by
  rw [orth, LinearMap.BilinForm.finrank_orthogonal nondegenerate_dotForm, finrank_fin_fun,
    finrank_span_singleton ha]

/-- A string orthogonal to every string orthogonal to a nonzero `a` lies in `span {a} = {0, a}`. -/
private theorem eq_zero_or_eq_of_forall_mem_orth {a w : Fin n → ZMod 2}
    (hw : ∀ v ∈ orth a, v ⬝ᵥ w = 0) : w = 0 ∨ w = a := by
  have hw' : w ∈ (dotForm n).orthogonal (orth a) := LinearMap.BilinForm.mem_orthogonal_iff.2 hw
  rw [orth, LinearMap.BilinForm.orthogonal_orthogonal nondegenerate_dotForm isRefl_dotForm,
    Submodule.mem_span_singleton] at hw'
  obtain ⟨c, rfl⟩ := hw'
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp

/-- **Arora–Barak, Exercise 20.5** (web draft 2007-01-08, p. 431/447), with the hypothesis
`a ≠ 0` it needs. For nonzero `a ∈ GF(2)^n`, if `y_1, …, y_{n-1}` are drawn uniformly at random
subject to `y_i ⬝ a = 0` for every `i`, then with probability at least `1 / 4` (the exercise asks
for `1 / 10`) no string other than `0` and `a` is orthogonal to all of them. Here the probability
is the fraction of the tuples with `y_i ⬝ a = 0` for every `i`. -/
theorem one_div_four_le_card_determines_div_card {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    (1 / 4 : ℝ) ≤
      (#{y : Fin (n - 1) → Fin n → ZMod 2 |
          (∀ i, y i ⬝ᵥ a = 0) ∧ ∀ w, (∀ i, y i ⬝ᵥ w = 0) → w = 0 ∨ w = a} : ℝ) /
        #{y : Fin (n - 1) → Fin n → ZMod 2 | ∀ i, y i ⬝ᵥ a = 0} := by
  classical
  set K := orth a
  have hK := finrank_orth ha
  -- the uniform space: tuples of vectors of `K`
  have hall : #{y : Fin (n - 1) → Fin n → ZMod 2 | ∀ i, y i ⬝ᵥ a = 0} =
      (2 ^ (n - 1)) ^ (n - 1) := by
    rw [← Fintype.card_coe, Fintype.card_congr ((Equiv.subtypeEquivRight fun y => by
      simp only [mem_filter, mem_univ, true_and]
      exact forall_congr' fun i => (mem_orth (a := a) (y := y i)).symm).trans
        (Equiv.subtypePiEquivPi (p := fun _ v => v ∈ K))),
      Fintype.card_fun, Fintype.card_fin, card_eq_pow_finrank (K := ZMod 2) (V := K), hK, ZMod.card]
  -- the linearly independent tuples determine `a`
  have hgood : ∏ i : Fin (n - 1), (2 ^ (n - 1) - 2 ^ i.val) ≤
      #{y : Fin (n - 1) → Fin n → ZMod 2 |
        (∀ i, y i ⬝ᵥ a = 0) ∧ ∀ w, (∀ i, y i ⬝ᵥ w = 0) → w = 0 ∨ w = a} := by
    have hli := card_linearIndependent (K := ZMod 2) (V := K) (k := n - 1) hK.ge
    rw [ZMod.card, hK] at hli
    rw [← hli, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun s => ⟨fun i => (s.val i : Fin n → ZMod 2),
      mem_filter.2 ⟨mem_univ _, fun i => mem_orth.1 (s.val i).property, fun w hw =>
        eq_zero_or_eq_of_forall_mem_orth fun v hv => ?_⟩⟩) fun s t hst =>
          Subtype.ext (funext fun i => Subtype.ext (congrFun (congrArg Subtype.val hst) i))
    suffices ∀ x ∈ Submodule.span (ZMod 2) (Set.range s.val), (x : Fin n → ZMod 2) ⬝ᵥ w = 0 from
      this ⟨v, hv⟩ (s.property.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hK]) ▸
        Submodule.mem_top)
    intro x hx
    induction hx using Submodule.span_induction with
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      exact hw i
    | zero => simp
    | add _ _ _ _ hx hy => simp [add_dotProduct, hx, hy]
    | smul _ _ _ hx => simp [smul_dotProduct, hx]
  rw [hall, le_div_iff₀ (by positivity)]
  refine le_trans ?_ (Nat.cast_le.2 hgood)
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((2 ^ (n - 1) - 2 ^ i : ℕ) : ℝ))]
  have hprod : ∏ i ∈ range (n - 1), ((2 ^ (n - 1) - 2 ^ i : ℕ) : ℝ) =
      (∏ i ∈ range (n - 1), (1 - (2 : ℝ) ^ i / 2 ^ (n - 1))) * ((2 : ℝ) ^ (n - 1)) ^ (n - 1) := by
    rw [show ((2 : ℝ) ^ (n - 1)) ^ (n - 1) = ∏ _i ∈ range (n - 1), (2 : ℝ) ^ (n - 1) by
      rw [prod_const, card_range], ← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (mem_range.1 hi).le)]
    field_simp
    push_cast
    ring
  rw [hprod]
  push_cast
  exact mul_le_mul_of_nonneg_right (one_div_four_le_prod_one_sub _) (by positivity)

end Cslib.LinearAlgebra
