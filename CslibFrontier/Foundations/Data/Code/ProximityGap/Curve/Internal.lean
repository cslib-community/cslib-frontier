/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
public import Mathlib.Algebra.Order.Ring.Rat
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.BigOperators.Field

/-!
# Shared Internal Helpers for Parameterized-Curve Proximity Gaps

Algebraic, counting, and Hamming-distance helpers shared by at least two submodules under
`CslibFrontier.Foundations.Data.Code.ProximityGap.Curve` (imported privately so downstream clients
of the umbrella `Curve` module do not see these internal lemmas).

## Main results

* `Cslib.Code.line_sum_fin2`: expands a degree-1 curve as `u₀ + z • u₁`.
* `Cslib.Code.hammingDist_le_of_ratWeightedAgree_ge`: links weighted agreement to Hamming distance.
* `Cslib.Code.curve_dichotomy_of_ca`: converts correlated agreement into a curve dichotomy.
* `Cslib.Code.lt_card_field_of_density_threshold`: extracts the field-size lower bound from a strict
  affine density hypothesis.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

theorem line_sum_fin2 {F ι : Type*} [Field F] (u₀ u₁ : ι → F) (z : F) :
    (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem subset_filter_affine_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i) (z : Fin ℓ → F) :
    D' ⊆ Finset.univ.filter fun i =>
      (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    obtain ⟨h0, hj⟩ := hagree i hi
    simp [h0, hj]⟩

theorem subset_filter_line_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {D' : Finset ι} {u₀ v₀ u₁ v₁ : ι → F}
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) (z : F) :
    D' ⊆ Finset.univ.filter fun i => (u₀ + z • u₁) i = (v₀ + z • v₁) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    obtain ⟨h0, h1⟩ := hagree i hi; simp only [Pi.add_apply, Pi.smul_apply, h0, h1]⟩

theorem hammingDist_le_of_card_filter_eq
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F}
    (hcard : Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card) :
    hammingDist x y ≤ e := by
  have htot := card_filter_eq_add_hammingDist x y; omega

theorem card_filter_eq_of_hammingDist_le
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F} (hdist : hammingDist x y ≤ e) :
    Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card := by
  have htot := card_filter_eq_add_hammingDist x y; omega

/-- Pointwise conversion from signed `ℚ`-weighted agreement (`∀ i, μ i ≤ 1`) above
`((|ι| - e : ℕ) : ℚ) - 1` to unweighted Hamming distance at most `e`. -/
theorem hammingDist_le_of_ratWeightedAgree_ge
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    {x c : ι → F}
    (hμ_ge : θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i) :
    hammingDist x c ≤ e := by
  refine hammingDist_le_of_card_filter_eq ?_
  set A := Finset.univ.filter fun i => x i = c i
  have hlt : Fintype.card ι - e < A.card + 1 := Nat.cast_lt (α := ℚ).1 (by
    have := hθ.trans_le (hμ_ge.trans
      ((Finset.sum_le_sum fun i _ => hμ_le i).trans_eq (by simp : ∑ _ ∈ A, (1 : ℚ) = A.card)))
    push_cast; linarith)
  omega

theorem nat_le_sum_iff_div {ι : Type*} {W : ι → ℕ} {M B : ℕ} (hM : 0 < M)
    (S : Finset ι) : B ≤ ∑ i ∈ S, W i ↔ (B : ℚ) / M ≤ ∑ i ∈ S, (W i : ℚ) / M := by
  rw [← Finset.sum_div, div_le_div_iff_of_pos_right (Nat.cast_pos.2 hM), ← Nat.cast_sum,
    Nat.cast_le]

/-- Counting lemma: in `Fin ℓ → F` with `1 ≤ ℓ`, the hyperplane `{z | z j₀ = 0}` has cardinality
`|F| ^ (ℓ - 1)`. -/
theorem card_filter_coord_eq_zero
    {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ} (j₀ : Fin ℓ) :
    (Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0).card =
      (Fintype.card F) ^ (ℓ - 1) := by
  classical
  have hbij := Finset.card_bij (s := (Finset.univ : Finset ({j : Fin ℓ // j ≠ j₀} → F)))
    (t := Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0)
    (fun g _ j => if h : j = j₀ then 0 else g ⟨j, h⟩)
    (fun _ _ => by simp)
    (fun g₁ _ g₂ _ heq => funext fun ⟨j, hj⟩ => by simpa [hj] using congrFun heq j)
    (fun z hz => ⟨fun j => z j.1, mem_univ _, funext fun j => by
      by_cases h : j = j₀ <;> simp [h, (mem_filter.1 hz).2]⟩)
  rw [← hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_subtype]
  congr 1
  have hf : (Finset.univ.filter fun j : Fin ℓ => j ≠ j₀) = Finset.univ.erase j₀ := by
    ext
    simp
  rw [hf, Finset.card_erase_of_mem (mem_univ j₀), Finset.card_univ, Fintype.card_fin]

/-- Integer-to-rational weight threshold: with `t = ⌈B / M⌉ = (B + M - 1) / M`, the
unique-decoding agreement count `n - (n - t)` satisfies `n - (n - t) - 1 < B / M`. -/
theorem card_sub_sub_ceilDiv_sub_one_lt {n B M : ℕ} (hM : 0 < M) :
    ((n - (n - (B + M - 1) / M) : ℕ) : ℚ) - 1 < (B : ℚ) / (M : ℚ) := by
  have hdiv : M * ((B + M - 1) / M) ≤ B + M - 1 := Nat.mul_div_le (B + M - 1) M
  generalize (B + M - 1) / M = t at hdiv ⊢
  have ht_le : n - (n - t) ≤ t := by omega
  have hq_lt : (M : ℚ) * ((n - (n - t) : ℕ) : ℚ) < (B : ℚ) + (M : ℚ) := by
    exact_mod_cast (Nat.mul_le_mul_left M ht_le).trans_lt (by omega)
  rw [lt_div_iff₀ (Nat.cast_pos.2 hM)]
  linarith

theorem curve_dichotomy_of_ca {F ι : Type*} [Field F] [Fintype F] {d : ℕ}
    {C : Submodule F (ι → F)} {u : Fin (d + 1) → (ι → F)}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop) {B : ℕ}
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v : Fin (d + 1) → (ι → F)},
      (∀ i ∈ D', ∀ j, u j i = v j i) →
      ∀ z : F, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j))
    [DecidablePred fun z : F => ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c]
    (hca : ∀ S : Finset F, B < S.card →
      (∀ z ∈ S, ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i) :
    (∀ z : F, ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c) ∨
      (Finset.univ.filter fun z : F =>
        ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c).card ≤ B := by
  by_cases hcard : (Finset.univ.filter fun z : F =>
      ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c).card ≤ B
  · exact Or.inr hcard
  · obtain ⟨D', hD', v, hvC, hag⟩ :=
      hca _ (Nat.lt_of_not_ge hcard) fun _ hz => (mem_filter.1 hz).2
    exact Or.inl fun z => ⟨∑ j : Fin (d + 1), z ^ (j : ℕ) • v j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvC j), hgood hD' hag z⟩

/-- Internal helper: the exact affine density threshold `K * |F| ^ ℓ < |F| * #T` for
`T ⊆ (Fin ℓ → F)` forces `K < |F|`. -/
theorem lt_card_field_of_density_threshold
    {F : Type*} [Fintype F] {K ℓ : ℕ} {T : Finset (Fin ℓ → F)}
    (hT : K * (Fintype.card F) ^ ℓ < Fintype.card F * T.card) :
    K < Fintype.card F := by
  have hT_le : T.card ≤ (Fintype.card F) ^ ℓ := by
    calc T.card ≤ Fintype.card (Fin ℓ → F) := Finset.card_le_univ T
      _ = (Fintype.card F) ^ ℓ := by
          rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Nat.lt_of_mul_lt_mul_right (hT.trans_le (Nat.mul_le_mul_left _ hT_le))

end Cslib.Code
