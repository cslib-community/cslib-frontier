/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, bilinear complexity: 0-1 indicator tensors and rank counting)

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# `0-1` indicator tensors, coordinate-factoring rank, and high-rank existence

General constructions and rank bounds for `0-1` order-three tensors (`Cslib.Tensor`):

1. **Coordinate-factoring rank bound** (`rank_of_factors_left_mid`): any order-three tensor over a
   commutative semiring `K` factoring on its first two legs through finite types `Y₀, Y₁` has rank
   at most `|Y₀| * |Y₁|`.
2. **High-rank `0-1` order-three tensors over arbitrary fields**
   (`card_rank_indicatorThreeTensor_le`, `exists_not_rank_indicatorThreeTensor`): over any field `K`
   (finite or infinite, including `ZMod 2` and `ℚ`), multilinear Lagrange interpolation on
   `{0, 1} ^ (X₀ × X₁ × X₂)` composed with the degree-`3` CP-rank parameterization shows that at
   most `(3 * N + 1) ^ (r * (|X₀| + |X₁| + |X₂|))` subsets `S : Finset (X₀ × X₁ × X₂)` have
   CP-rank `≤ r` (where `N = |X₀| * |X₁| * |X₂|`). Whenever that bound is strictly below `2 ^ N`,
   some subset `T ⊆ X₀ × X₁ × X₂` satisfies `¬Tensor.Rank r (indicatorThreeTensor K T)`. Note that
   this witness is a nonconstructive finite dimension/counting result, not an explicit tensor
   family.

## Main definitions

* `Cslib.Tensor.indicatorThreeTensor`: the `0-1` order-three tensor of a subset
  `T ⊆ X₀ × X₁ × X₂` over `K`.

## Main results

* `Cslib.Tensor.rank_of_factors_left_mid`: rank `≤ |Y₀| * |Y₁|` when the first two legs factor
  through `Y₀` and `Y₁`.
* `Cslib.Tensor.card_rank_indicatorThreeTensor_le`: upper bound on the number of `0-1` subsets
  `S : Finset (X₀ × X₁ × X₂)` whose indicator tensor has CP-rank `≤ r` over `K`.
* `Cslib.Tensor.exists_not_rank_indicatorThreeTensor`: dimension/degree counting bound producing a
  `0-1` tensor of CP-rank strictly greater than `r` over any field `K`.
-/

public section

namespace Cslib.Tensor

/-! ### `0-1` indicator tensors and coordinate factoring -/

/-- The `0-1` order-three tensor over `K` indicating membership in `T ⊆ X₀ × X₁ × X₂`. -/
@[expose] noncomputable def indicatorThreeTensor (K : Type*) [Zero K] [One K]
    {X₀ X₁ X₂ : Type*} (T : Set (X₀ × X₁ × X₂)) : Tensor K X₀ X₁ X₂ :=
  open Classical in
  fun x₀ x₁ x₂ => if (x₀, x₁, x₂) ∈ T then 1 else 0

@[simp] theorem indicatorThreeTensor_apply (K : Type*) [Zero K] [One K]
    {X₀ X₁ X₂ : Type*} (T : Set (X₀ × X₁ × X₂)) [DecidablePred (· ∈ T)]
    (x₀ : X₀) (x₁ : X₁) (x₂ : X₂) :
    indicatorThreeTensor K T x₀ x₁ x₂ = if (x₀, x₁, x₂) ∈ T then 1 else 0 := by
  simp only [indicatorThreeTensor]
  split_ifs <;> rfl

/-- Any order-three tensor factoring on its first two legs through finite types `Y₀, Y₁` has rank at
most `|Y₀| * |Y₁|` over any commutative semiring `K`. -/
theorem rank_of_factors_left_mid {K X₀ X₁ X₂ Y₀ Y₁ : Type*} [CommSemiring K]
    [Fintype Y₀] [Fintype Y₁] (π₀ : X₀ → Y₀) (π₁ : X₁ → Y₁) (g : Y₀ → Y₁ → X₂ → K) :
    Rank (Fintype.card Y₀ * Fintype.card Y₁)
      (fun x₀ x₁ x₂ => g (π₀ x₀) (π₁ x₁) x₂) := by
  classical
  let e : Y₀ × Y₁ ≃ Fin (Fintype.card Y₀ * Fintype.card Y₁) :=
    Fintype.equivFinOfCardEq (by simp)
  refine ⟨Matrix.of fun k x₀ => if (e.symm k).1 = π₀ x₀ then 1 else 0,
    Matrix.of fun k x₁ => if (e.symm k).2 = π₁ x₁ then 1 else 0,
    Matrix.of fun x₂ k => g (e.symm k).1 (e.symm k).2 x₂, ?_⟩
  funext x₀ x₁ x₂
  rw [restrict_unit]
  refine (Fintype.sum_equiv e.symm _
    (fun w : Y₀ × Y₁ => (if w.1 = π₀ x₀ then (1 : K) else 0) *
      (if w.2 = π₁ x₁ then 1 else 0) * g w.1 w.2 x₂)
    fun _ => rfl).trans ?_
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single (π₀ x₀) (fun y₀ hy₀ =>
    Finset.sum_eq_zero fun _ _ => by simp [hy₀])]
  rw [Fintype.sum_eq_single (π₁ x₁) (fun y₁ hy₁ => by simp [hy₁])]
  simp

/-! ### High-rank `0-1` order-three tensors over arbitrary fields -/

private theorem totalDegree_sum_le {K ι α : Type*} [CommSemiring K] (s : Finset α)
    (f : α → MvPolynomial ι K) {d : ℕ} (hf : ∀ a ∈ s, (f a).totalDegree ≤ d) :
    (∑ a ∈ s, f a).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private theorem totalDegree_prod_le {K ι α : Type*} [CommSemiring K] (s : Finset α)
    (f : α → MvPolynomial ι K) :
    (∏ a ∈ s, f a).totalDegree ≤ ∑ a ∈ s, (f a).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

open Classical in
/-- **Number of `0-1` order-three tensors of CP-rank at most `r`.** Over any field `K` (finite or
infinite), the number of subsets `S : Finset (X₀ × X₁ × X₂)` whose indicator tensor
`indicatorThreeTensor K (S : Set _)` has CP-rank at most `r` is at most
`(3 * N + 1) ^ (r * (|X₀| + |X₁| + |X₂|))`, where `N = |X₀| * |X₁| * |X₂|`. -/
theorem card_rank_indicatorThreeTensor_le (K : Type*) [Field K]
    (X₀ X₁ X₂ : Type*) [Fintype X₀] [Fintype X₁] [Fintype X₂] (r : ℕ) :
    (Finset.univ.filter fun S : Finset (X₀ × X₁ × X₂) =>
        Rank r (indicatorThreeTensor K (S : Set (X₀ × X₁ × X₂)))).card ≤
      (3 * (Fintype.card X₀ * Fintype.card X₁ * Fintype.card X₂) + 1) ^
        (r * (Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂)) := by
  classical
  let P3 := X₀ × X₁ × X₂
  let N := Fintype.card X₀ * Fintype.card X₁ * Fintype.card X₂
  have hcard_P3 : Fintype.card P3 = N := by simp [P3, N, mul_assoc]
  let GoodFin := Finset.univ.filter fun S : Finset P3 =>
    Rank r (indicatorThreeTensor K (S : Set P3))
  let Good := {S : Finset P3 // S ∈ GoodFin}
  let Idx := (Fin r × X₀) ⊕ (Fin r × X₁) ⊕ (Fin r × X₂)
  have hcard_Idx : Fintype.card Idx =
      r * (Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂) := by
    simp [Idx]; ring
  let entryPoly (p : P3) : MvPolynomial Idx K :=
    ∑ k : Fin r, MvPolynomial.X (Sum.inl (k, p.1)) *
      MvPolynomial.X (Sum.inr (Sum.inl (k, p.2.1))) *
      MvPolynomial.X (Sum.inr (Sum.inr (k, p.2.2)))
  have hdeg_entry (p : P3) : (entryPoly p).totalDegree ≤ 3 := by
    refine totalDegree_sum_le _ _ fun k _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h12 : (MvPolynomial.X (Sum.inl (k, p.1)) *
        MvPolynomial.X (Sum.inr (Sum.inl (k, p.2.1))) : MvPolynomial Idx K).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
    have h3 : (MvPolynomial.X (Sum.inr (Sum.inr (k, p.2.2))) :
        MvPolynomial Idx K).totalDegree ≤ 1 := by
      simp [MvPolynomial.totalDegree_X]
    omega
  have hex_z (S : Good) : ∃ z : Idx → K, ∀ p : P3,
      MvPolynomial.eval z (entryPoly p) = if p ∈ S.1 then 1 else 0 := by
    have hmem : Rank r (indicatorThreeTensor K (S.1 : Set P3)) :=
      (Finset.mem_filter.mp S.2).2
    obtain ⟨α, β, γ, hres⟩ := hmem
    refine ⟨Sum.elim (fun kx => α kx.1 kx.2)
      (Sum.elim (fun ky => β ky.1 ky.2) (fun kz => γ kz.2 kz.1)), fun p => ?_⟩
    have hval := congrFun (congrFun (congrFun hres p.1) p.2.1) p.2.2
    rw [restrict_unit, indicatorThreeTensor_apply] at hval
    simp only [entryPoly, map_sum, map_mul, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
    exact hval.trans (by simp)
  choose z hz using hex_z
  let Q (S : Good) : MvPolynomial Idx K :=
    ∏ p : P3, if p ∈ S.1 then entryPoly p else (1 - entryPoly p)
  have hQ_eval (S S' : Good) :
      MvPolynomial.eval (z S') (Q S) = if S = S' then 1 else 0 := by
    simp only [Q, map_prod]
    split_ifs with heq
    · subst heq
      refine Finset.prod_eq_one fun p _ => ?_
      split_ifs with hp <;> simp [hz S p, hp]
    · have hne : ∃ p : P3, (p ∈ S.1) ≠ (p ∈ S'.1) := by
        by_contra! hall_eq
        exact heq (Subtype.ext (Finset.ext fun p => eq_iff_iff.mp (hall_eq p)))
      obtain ⟨p₀, hp₀⟩ := hne
      refine Finset.prod_eq_zero (Finset.mem_univ p₀) ?_
      by_cases hpS : p₀ ∈ S.1
      · have hpS' : p₀ ∉ S'.1 := fun h => hp₀ (by simp [hpS, h])
        simp [hpS, hpS', hz S' p₀]
      · have hpS' : p₀ ∈ S'.1 := by by_contra h; exact hp₀ (by simp [hpS, h])
        simp [hpS, hpS', hz S' p₀]
  have hQ_deg (S : Good) : (Q S).totalDegree ≤ 3 * N := by
    refine (totalDegree_prod_le _ _).trans ?_
    have hterm (p : P3) : (if p ∈ S.1 then entryPoly p else 1 - entryPoly p).totalDegree ≤ 3 := by
      split_ifs
      · exact hdeg_entry p
      · have h1sub : (1 - entryPoly p : MvPolynomial Idx K) =
            1 + MvPolynomial.C (-1 : K) * entryPoly p := by simp [sub_eq_add_neg]
        rw [h1sub]
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        have hC : (MvPolynomial.C (-1 : K) : MvPolynomial Idx K).totalDegree = 0 :=
          MvPolynomial.totalDegree_C (-1 : K)
        have hd := hdeg_entry p
        omega
    calc (∑ p : P3, (if p ∈ S.1 then entryPoly p else 1 - entryPoly p).totalDegree)
        ≤ ∑ _p : P3, 3 := Finset.sum_le_sum fun p _ => hterm p
      _ = 3 * N := by simp [hcard_P3, Nat.mul_comm]
  let Box := Idx → Fin (3 * N + 1)
  let toFinsupp (g : Box) : Idx →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (g j : ℕ)
  let L : MvPolynomial Idx K →ₗ[K] (Box → K) :=
    { toFun := fun f g => f.coeff (toFinsupp g)
      map_add' := fun f₁ f₂ => funext fun g => by simp
      map_smul' := fun c f => funext fun g => by simp [smul_eq_mul] }
  have hlin_indep : LinearIndependent K (L ∘ Q) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc S₀
    set P_comb : MvPolynomial Idx K := ∑ S : Good, c S • Q S
    have hP_deg : P_comb.totalDegree ≤ 3 * N :=
      totalDegree_sum_le _ _ fun S _ =>
        (MvPolynomial.totalDegree_smul_le (c S) (Q S)).trans (hQ_deg S)
    have hLP : L P_comb = 0 := by
      simpa [P_comb, map_sum, map_smul, Function.comp_def] using hc
    have hP_zero : P_comb = 0 := by
      ext m
      change P_comb.coeff m = 0
      by_cases hm : m ∈ P_comb.support
      · have hm_le : ∀ j : Idx, m j ≤ 3 * N := fun j => by
          have hsum_le : m.sum (fun _ e => e) ≤ P_comb.totalDegree :=
            Finset.le_sup (f := fun s : Idx →₀ ℕ => s.sum fun _ e => e) hm
          have hj_le : m j ≤ m.sum (fun _ e => e) := by
            by_cases hj0 : m j = 0
            · omega
            · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                (Finsupp.mem_support_iff.mpr hj0)
          exact hj_le.trans (hsum_le.trans hP_deg)
        let g : Box := fun j => ⟨m j, Nat.lt_succ_of_le (hm_le j)⟩
        have hfg : toFinsupp g = m := by
          ext j
          simp [toFinsupp, g]
        rw [← hfg]
        exact congrFun hLP g
      · exact MvPolynomial.notMem_support_iff.mp hm
    have hev := congrArg (MvPolynomial.eval (z S₀)) hP_zero
    simp_rw [P_comb, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hQ_eval]
      at hev
    simpa [mul_ite] using hev
  have hcard_le : Fintype.card Good ≤ Fintype.card Box :=
    (Pi.basisFun K Box).card_le_card_of_linearIndependent hlin_indep
  have hcard_Good : Fintype.card Good = GoodFin.card := Fintype.card_coe GoodFin
  have hcard_Box : Fintype.card Box =
      (3 * N + 1) ^ (r * (Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂)) := by
    simp [Box, hcard_Idx]
  rw [hcard_Good, hcard_Box] at hcard_le
  exact hcard_le

/-- **Existence of high-rank `0-1` order-three tensors over any field.** Let `X₀, X₁, X₂` be finite
index types with `N = |X₀| * |X₁| * |X₂|` and `d = r * (|X₀| + |X₁| + |X₂|)`. If
`(3 * N + 1) ^ d < 2 ^ N`, then over *any* field `K` (finite or infinite) there exists a subset
`T ⊆ X₀ × X₁ × X₂` whose `0-1` tensor `indicatorThreeTensor K T` does not have CP-rank `≤ r`. -/
theorem exists_not_rank_indicatorThreeTensor (K : Type*) [Field K]
    {X₀ X₁ X₂ : Type*} [Fintype X₀] [Fintype X₁] [Fintype X₂] {r : ℕ}
    (hcount :
      (3 * (Fintype.card X₀ * Fintype.card X₁ * Fintype.card X₂) + 1) ^
          (r * (Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂)) <
        2 ^ (Fintype.card X₀ * Fintype.card X₁ * Fintype.card X₂)) :
    ∃ T : Set (X₀ × X₁ × X₂), ¬Rank r (indicatorThreeTensor K T) := by
  classical
  by_contra! hall
  have hle := card_rank_indicatorThreeTensor_le K X₀ X₁ X₂ r
  have hfilter : (Finset.univ.filter fun S : Finset (X₀ × X₁ × X₂) =>
      Rank r (indicatorThreeTensor K (S : Set (X₀ × X₁ × X₂)))) = Finset.univ :=
    Finset.filter_eq_self.mpr fun S _ => hall (S : Set (X₀ × X₁ × X₂))
  rw [hfilter, Finset.card_univ, Fintype.card_finset, Fintype.card_prod, Fintype.card_prod,
    ← mul_assoc] at hle
  exact absurd hle (not_le.mpr hcount)

end Cslib.Tensor
