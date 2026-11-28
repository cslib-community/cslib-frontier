/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource
public import CslibFrontier.Foundations.Data.BitString.LinearEquiv
import CslibFrontier.Foundations.Data.BitString.ZModSpace
import CslibFrontier.Tactic.FinIndex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear affine somewhere condensers from dimension expanders

This module formalizes the linear affine somewhere condenser construction from Section 3 of
[Li and Zhong, CCC 2024][LiZhong2024]:

* `Cslib.AffineDisperser.Li.IsAffineSomewhereCondenser`: a `(δ, γ)` affine somewhere condenser
  mapping every affine source of rate `≥ δ` to a tuple of outputs at least one of which is an
  affine source of rate `≥ γ` (`[LiZhong2024, Def. 21]`).
* `Cslib.AffineDisperser.Li.IsDimensionExpander`: an `α`-dimension expander of degree `d` over
  `𝔽₂` (`[LiZhong2024, Def. 22]`).
* `Cslib.AffineDisperser.Li.basicCond`: the single-step halving condenser (`[LiZhong2024, Alg. 1]`)
  sending `(x₁, x₂)` to `(x₁, x₂, x₁ + T₁ x₂, x₂ + T₁ x₁, …, x₁ + T_d x₂, x₂ + T_d x₁)`.
* `Cslib.AffineDisperser.Li.sCond`: the iterated linear somewhere condenser
  (`[LiZhong2024, Alg. 2]`).

## Main results

* `Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_basicCond`: **Rate-boosting lemma**
  (`[LiZhong2024, Lemma 20]`), proving `basicCond T` is a `(δ, (1 + α / (4 * d)) * δ)` affine
  somewhere condenser for any `0 < δ ≤ 1 / 2`, `3 ≤ d`, `0 < α ≤ 1`.
* `Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_sCond`: **Iterated linear condenser**
  (`[LiZhong2024, Thm. 18]`), amplifying any affine entropy rate `0 < δ ≤ 1 / 2` to rate
  `1 / 2 + α / (8 * d)` in `h + 1` halving rounds when `1 / 2 ≤ δ * (1 + α / (4 * d)) ^ h`.

## References

* [X. Li and Y. Zhong, *Explicit Directional Affine Extractors and Improved Hardness for Linear
  Branching Programs*][LiZhong2024], Section 3 (Definitions 21–22, Lemma 20, Theorem 18)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Module

/-! ### Definitions -/

/-- A **`(δ, γ)` affine somewhere condenser**: for every `(n, k)` affine source `X` with
`k ≥ δ * n`, some output coordinate `f · i` distributes as an affine source of dimension
`k' ≥ γ * m` ([LiZhong2024, Def. 21]). -/
@[expose] def IsAffineSomewhereCondenser {n m ℓ : ℕ}
    (f : BitString n → Fin ℓ → BitString m) (δ γ : ℝ) : Prop :=
  ∀ (X : PMF (BitString n)) (k : ℕ), IsAffineSource X k → δ * n ≤ k →
    ∃ (i : Fin ℓ) (k' : ℕ), IsAffineSource (X.map fun x => f x i) k' ∧ γ * m ≤ k'

/-- An **`α`-dimension expander** of degree `d` over `𝔽₂`: a family of `d` linear maps
`T : Fin d → BitString n →ₗ[Bool] BitString n` expanding every subspace of dimension at most `n / 2`
by a factor `(1 + α)` ([LiZhong2024, Def. 22]). -/
@[expose] def IsDimensionExpander {n d : ℕ}
    (T : Fin d → BitString n →ₗ[Bool] BitString n) (α : ℝ) : Prop :=
  ∀ V : Submodule Bool (BitString n), 2 * finrank Bool V ≤ n →
    (1 + α) * (finrank Bool V : ℝ) ≤ (finrank Bool ↥(⨆ i : Fin d, V.map (T i)) : ℝ)

/-! ### Bit-splitting projections and basic condenser -/

private def projLeft (m : ℕ) : BitString (m + m) →ₗ[Bool] BitString m :=
  (LinearMap.fst Bool (BitString m) (BitString m)).comp (appendLinearEquiv m m).symm.toLinearMap

private def projRight (m : ℕ) : BitString (m + m) →ₗ[Bool] BitString m :=
  (LinearMap.snd Bool (BitString m) (BitString m)).comp (appendLinearEquiv m m).symm.toLinearMap

/-- **Single-step basic affine somewhere condenser** (`BasicCond`, [LiZhong2024, Alg. 1]):
splits `x ∈ BitString (m + m)` into `(x₁, x₂)` and outputs the `2 * d + 2` linear projections
`(x₁, x₂, x₁ + T₀ x₂, x₂ + T₀ x₁, …)`. -/
@[expose] def basicCond {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m) :
    BitString (m + m) →ₗ[Bool] (Fin (2 * d + 2) → BitString m) where
  toFun x idx :=
    let p := (appendLinearEquiv m m).symm x
    if h0 : idx.val = 0 then p.1
    else if h1 : idx.val = 1 then p.2
    else
      if (idx.val - 2) % 2 = 0 then p.1 + T ⟨(idx.val - 2) / 2, by have := idx.isLt; omega⟩ p.2
      else p.2 + T ⟨(idx.val - 2) / 2, by have := idx.isLt; omega⟩ p.1
  map_add' x y := by
    funext idx
    have hxy : (appendLinearEquiv m m).symm (x + y) =
        (((appendLinearEquiv m m).symm x).1 + ((appendLinearEquiv m m).symm y).1,
         ((appendLinearEquiv m m).symm x).2 + ((appendLinearEquiv m m).symm y).2) := by
      rw [map_add]; rfl
    dsimp only
    rw [hxy]
    by_cases h0 : idx.val = 0
    · simp only [h0, ↓reduceDIte, Pi.add_apply]
    · by_cases h1 : idx.val = 1
      · simp only [h1, one_ne_zero, ↓reduceDIte, Pi.add_apply]
      · simp only [h0, h1, ↓reduceDIte, Pi.add_apply]
        split_ifs <;> simp only [map_add] <;> abel
  map_smul' c x := by
    funext idx
    have hsmul : (appendLinearEquiv m m).symm (c • x) =
        (c • ((appendLinearEquiv m m).symm x).1, c • ((appendLinearEquiv m m).symm x).2) := by
      rw [map_smul]; rfl
    dsimp only
    rw [hsmul]
    by_cases h0 : idx.val = 0
    · simp only [h0, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
    · by_cases h1 : idx.val = 1
      · simp only [h1, one_ne_zero, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
      · simp only [h0, h1, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
        split_ifs <;> simp only [map_smul, smul_add]

private theorem basicCond_zero {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) :
    basicCond T x 0 = projLeft m x := by
  simp only [basicCond, projLeft, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_zero, ↓reduceDIte]
  rfl

private theorem basicCond_one {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) :
    basicCond T x ⟨1, by omega⟩ = projRight m x := by
  simp only [basicCond, projRight, LinearMap.coe_mk, AddHom.coe_mk, one_ne_zero, ↓reduceDIte]
  rfl

private theorem basicCond_even {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) (i : Fin d) :
    basicCond T x ⟨2 + 2 * i.val, by omega⟩ = projLeft m x + T i (projRight m x) := by
  simp only [basicCond, projLeft, projRight, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega))]
  split_ifs
  · exact congrArg (fun k => ((appendLinearEquiv m m).symm x).1 +
      T k ((appendLinearEquiv m m).symm x).2) (by fin_index)
  · omega

private theorem basicCond_odd {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) (i : Fin d) :
    basicCond T x ⟨2 + 2 * i.val + 1, by omega⟩ = projRight m x + T i (projLeft m x) := by
  simp only [basicCond, projLeft, projRight, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega))]
  split_ifs
  · omega
  · exact congrArg (fun k => ((appendLinearEquiv m m).symm x).2 +
      T k ((appendLinearEquiv m m).symm x).1) (by fin_index)

private def basicCondAt {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (idx : Fin (2 * d + 2)) : BitString (m + m) →ₗ[Bool] BitString m :=
  (LinearMap.proj idx).comp (basicCond T)

private theorem isAffine_of_linearMap {n m : ℕ} (L : BitString n →ₗ[Bool] BitString m) :
    IsAffine L := fun x y z => by
  simp only [map_add]

private theorem toAffineMap_linear_of_isAffine_linearMap {n m : ℕ}
    (L : BitString n →ₗ[Bool] BitString m) :
    (isAffine_of_linearMap L).toAffineMap.linear = L :=
  LinearMap.ext fun x => by
    simpa only [vsub_eq_sub, sub_zero, map_zero, IsAffine.coe_toAffineMap] using
      (isAffine_of_linearMap L).toAffineMap.linear_apply_vsub x 0

private theorem isAffineSource_map_of_linear {n m : ℕ}
    (A : AffineSubspace Bool (BitString n)) (hA : (A : Set (BitString n)).Nonempty)
    (L : BitString n →ₗ[Bool] BitString m) :
    IsAffineSource ((uniformAffine A hA).map L) (finrank Bool ↥(A.direction.map L)) := by
  have hL : IsAffine L := isAffine_of_linearMap L
  refine ⟨A.map hL.toAffineMap, ?_, ?_, uniformAffine_map_of_isAffine A hA hL⟩
  · obtain ⟨x₀, hx₀⟩ := hA
    exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩
  · rw [AffineSubspace.map_direction, toAffineMap_linear_of_isAffine_linearMap]

/-! ### Subspace dimension lemmas for `basicCond` -/

/-- Sum-of-excess dimension inequality over a `Finset` of `Bool`-submodules:
`finrank (B ⊔ ⨆ i ∈ s, S i) ≤ finrank B + ∑ i ∈ s, (finrank (B ⊔ S i) - finrank B)`. -/
private theorem finrank_sup_biSup_le {m : ℕ} (B : Submodule Bool (BitString m))
    {d : ℕ} (S : Fin d → Submodule Bool (BitString m)) (s : Finset (Fin d)) :
    finrank Bool ↥(B ⊔ ⨆ i ∈ s, S i) ≤
      finrank Bool B + ∑ i ∈ s, (finrank Bool ↥(B ⊔ S i) - finrank Bool B) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset (Fin d)), S i) = ⊥ from
      eq_bot_iff.mpr (iSup₂_le fun i hi => absurd hi (Finset.notMem_empty i)), sup_bot_eq,
      Finset.sum_empty, add_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.iSup_insert]
    have hB_W : finrank Bool B ≤ finrank Bool ↥(B ⊔ S j) := Submodule.finrank_mono le_sup_left
    have hle1 : finrank Bool ↥(B ⊔ (S j ⊔ ⨆ i ∈ s, S i)) + finrank Bool B ≤
        finrank Bool ↥(B ⊔ ⨆ i ∈ s, S i) + finrank Bool ↥(B ⊔ S j) := by
      rw [sup_sup_distrib_left, sup_comm (B ⊔ S j)]
      exact (Nat.add_le_add_left (Submodule.finrank_mono (le_inf le_sup_left le_sup_left)) _).trans
        (finrank_sup_add_finrank_inf_bool _ _).le
    omega

/-- Pigeonhole over `[d]`: `finrank (⨆ j, S j) ≤ finrank B + d * (finrank (B ⊔ S i) - finrank B)`
for some `i : Fin d`. -/
private theorem exists_finrank_sup_ge_of_finrank_iSup {m d : ℕ} (hd : 0 < d)
    (B : Submodule Bool (BitString m)) (S : Fin d → Submodule Bool (BitString m)) :
    ∃ i : Fin d, finrank Bool ↥(⨆ j : Fin d, S j) ≤
      finrank Bool B + d * (finrank Bool ↥(B ⊔ S i) - finrank Bool B) := by
  have hsum := finrank_sup_biSup_le B S Finset.univ
  rw [show (⨆ j ∈ Finset.univ, S j) = ⨆ j, S j by simp only [Finset.mem_univ, iSup_pos]] at hsum
  have := Submodule.finrank_mono (le_sup_right : ⨆ j, S j ≤ B ⊔ ⨆ j, S j)
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    (f := fun _ => ∑ j, (finrank Bool ↥(B ⊔ S j) - finrank Bool B))
    (g := fun i => d * (finrank Bool ↥(B ⊔ S i) - finrank Bool B)) (by simp [Finset.mul_sum])
  exact ⟨i, by omega⟩

/-- Algebraic core of [LiZhong2024, Lemma 20]: from `(1 + α) * x ≤ y + d * (M + t - y)` with
`x + y = k`, `2 * x ≤ k`, `t ≤ α / (4 * d) * k`, `d ≥ 3`, and `0 < α ≤ 1`, deduce
`(1 / 2 + α / (8 * d)) * k ≤ M`. -/
private theorem basicCond_rate_algebra {d : ℕ} (hd : 3 ≤ d) {α : ℝ} (hα0 : 0 < α) (_hα1 : α ≤ 1)
    {k x y M t : ℝ} (hk0 : 0 ≤ k) (hx_half : 2 * x ≤ k) (hxy : x + y = k)
    (ht : t ≤ α / (4 * (d : ℝ)) * k)
    (hexp : (1 + α) * x ≤ y + (d : ℝ) * (M + t - y)) :
    (1 / 2 + α / (8 * (d : ℝ))) * k ≤ M := by
  have hd_real : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < d := by linarith
  have h1 : (1 + α) * x + ((d : ℝ) - 1) * y = ((d : ℝ) - 1) * k + (2 + α - (d : ℝ)) * x := by
    rw [← hxy]; ring
  have hneg : 2 + α - (d : ℝ) ≤ 0 := by linarith
  have h3 : (2 + α - (d : ℝ)) * (k / 2) ≤ (2 + α - (d : ℝ)) * x := by nlinarith
  have hmul : (d : ℝ) * ((1 / 2 + 4 * (α / (8 * (d : ℝ)))) * k) =
      ((d : ℝ) - 1) * k + (2 + α - (d : ℝ)) * (k / 2) := by field_simp; ring
  have h6 : (1 / 2 + 4 * (α / (8 * (d : ℝ)))) * k ≤ M + t :=
    (mul_le_mul_iff_left₀ hd_pos).mp (by linarith)
  have hsplit : (1 / 2 + 4 * (α / (8 * (d : ℝ)))) * k =
      (1 / 2 + α / (8 * (d : ℝ))) * k + α / (4 * (d : ℝ)) * k + α / (8 * (d : ℝ)) * k := by ring
  have hpos : 0 ≤ α / (8 * (d : ℝ)) * k := by positivity
  linarith

private theorem finrank_sup_le_add_of_le_sup {m : ℕ} {A B C : Submodule Bool (BitString m)}
    {t : ℕ} (hle : A ≤ B ⊔ C) (hC : finrank Bool C ≤ t) :
    finrank Bool A ≤ finrank Bool B + t :=
  calc finrank Bool A ≤ finrank Bool ↥(B ⊔ C) := Submodule.finrank_mono hle
    _ ≤ finrank Bool ↥(B ⊔ C) + finrank Bool ↥(B ⊓ C) := Nat.le_add_right _ _
    _ = finrank Bool B + finrank Bool C := finrank_sup_add_finrank_inf_bool B C
    _ ≤ finrank Bool B + t := Nat.add_le_add_left hC _

/-- Shared arithmetic finale for `basicCond_subspace_boost_case1` and `_case2`. -/
private theorem basicCond_subspace_boost_step {m d k : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {T : Fin d → BitString m →ₗ[Bool] BitString m}
    (A₀ B₀ M C : Submodule Bool (BitString m))
    (hA_half : 2 * finrank Bool A₀ ≤ k) (hsum : finrank Bool A₀ + finrank Bool B₀ = k)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (k : ℝ))
    (hexpand : (1 + α) * (finrank Bool A₀ : ℝ) ≤ (finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) : ℝ))
    (hi_pig : finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) ≤
      finrank Bool B₀ + d * (finrank Bool M + finrank Bool C - finrank Bool B₀))
    (hB_le : finrank Bool B₀ ≤ finrank Bool M + finrank Bool C) :
    (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (finrank Bool M : ℝ) := by
  have hpig := (Nat.cast_le (α := ℝ)).mpr hi_pig
  push_cast [hB_le] at hpig
  exact basicCond_rate_algebra hd hα0 hα1 (Nat.cast_nonneg k)
    (by exact_mod_cast hA_half) (by exact_mod_cast hsum) ht_lt (hexpand.trans hpig)

/-- Case 1 of `basicCond_subspace_boost` (`2 * s ≤ k`). -/
private theorem basicCond_subspace_boost_case1 {m d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m))) (B C : Submodule Bool (BitString m))
    (hB_eq : B = (V ⊓ LinearMap.ker (projLeft m)).map (projRight m))
    (hP2_eq : V.map (projRight m) = B ⊔ C)
    (hm_bound : 2 * finrank Bool ↥(V.map (projLeft m)) ≤ m)
    (hsr : finrank Bool ↥(V.map (projLeft m)) + finrank Bool B = finrank Bool V)
    (hs_half : 2 * finrank Bool ↥(V.map (projLeft m)) ≤ finrank Bool V)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (finrank Bool V : ℝ)) :
    ∃ idx : Fin (2 * d + 2),
      (1 / 2 + α / (8 * (d : ℝ))) * (finrank Bool V : ℝ) ≤
        (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  set r := finrank Bool B
  set t := finrank Bool C
  have hexpand := hT A' hm_bound
  obtain ⟨i, hi_pig⟩ := exists_finrank_sup_ge_of_finrank_iSup (by omega : 0 < d) B
    (fun j => A'.map (T j))
  let idx : Fin (2 * d + 2) := ⟨2 + 2 * i.val + 1, by omega⟩
  let M : Submodule Bool (BitString m) := V.map (basicCondAt T idx)
  have hB_le_M : B ≤ M := by
    rw [hB_eq]
    rintro y ⟨w, ⟨hwV, hwker⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨w, hwV, ?_⟩
    change basicCond T w idx = projRight m w
    rw [basicCond_odd, LinearMap.mem_ker.mp hwker, map_zero, add_zero]
  have hsup_le : B ⊔ A'.map (T i) ≤ M ⊔ C := by
    refine sup_le (hB_le_M.trans le_sup_left) ?_
    rintro z ⟨a', ⟨v, hvV, rfl⟩, rfl⟩
    have hv_M : projRight m v + T i (projLeft m v) ∈ M :=
      Submodule.mem_map.mpr ⟨v, hvV, by change basicCond T v idx = _; exact basicCond_odd T v i⟩
    have hv_P2 : projRight m v ∈ B ⊔ C := by rw [← hP2_eq]; exact Submodule.mem_map_of_mem hvV
    have hadd := (M ⊔ C).add_mem ((le_sup_left : M ≤ M ⊔ C) hv_M)
      (sup_le_sup_right hB_le_M C hv_P2)
    rwa [add_right_comm, BitString.add_self, zero_add] at hadd
  have hfin_sup : finrank Bool ↥(B ⊔ A'.map (T i)) ≤ finrank Bool M + t :=
    finrank_sup_le_add_of_le_sup hsup_le le_rfl
  have hB_le_sup : r ≤ finrank Bool ↥(B ⊔ A'.map (T i)) := Submodule.finrank_mono le_sup_left
  refine ⟨idx, basicCond_subspace_boost_step hd hα0 hα1 A' B M C hs_half hsr ht_lt hexpand
    (hi_pig.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d (by omega)) r))
    (hB_le_sup.trans hfin_sup)⟩

/-- Case 2 of `basicCond_subspace_boost` (`2 * r ≤ k`). -/
private theorem basicCond_subspace_boost_case2 {m d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m))) (B C : Submodule Bool (BitString m))
    (hB_eq : B = (V ⊓ LinearMap.ker (projLeft m)).map (projRight m))
    (hP2_eq : V.map (projRight m) = B ⊔ C)
    (hm_bound : 2 * finrank Bool B ≤ m)
    (hsr : finrank Bool ↥(V.map (projLeft m)) + finrank Bool B = finrank Bool V)
    (hr_half : 2 * finrank Bool B ≤ finrank Bool V)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (finrank Bool V : ℝ)) :
    ∃ idx : Fin (2 * d + 2),
      (1 / 2 + α / (8 * (d : ℝ))) * (finrank Bool V : ℝ) ≤
        (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  set s := finrank Bool A'
  set t := finrank Bool C
  have hexpand := hT B hm_bound
  obtain ⟨i, hi_pig⟩ := exists_finrank_sup_ge_of_finrank_iSup (by omega : 0 < d) A'
    (fun j => B.map (T j))
  let idx : Fin (2 * d + 2) := ⟨2 + 2 * i.val, by omega⟩
  let M : Submodule Bool (BitString m) := V.map (basicCondAt T idx)
  have hTB_le_M : B.map (T i) ≤ M := by
    rw [hB_eq]
    rintro y ⟨_, ⟨w, ⟨hwV, hwker⟩, rfl⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨w, hwV, ?_⟩
    change basicCond T w idx = T i (projRight m w)
    rw [basicCond_even, LinearMap.mem_ker.mp hwker, zero_add]
  have hsup_le : A' ⊔ B.map (T i) ≤ M ⊔ C.map (T i) := by
    refine sup_le ?_ (hTB_le_M.trans le_sup_left)
    rintro z ⟨v, hvV, rfl⟩
    have hv_M : projLeft m v + T i (projRight m v) ∈ M :=
      Submodule.mem_map.mpr ⟨v, hvV, by change basicCond T v idx = _; exact basicCond_even T v i⟩
    have hv_P2 : T i (projRight m v) ∈ (B ⊔ C).map (T i) := by
      rw [← hP2_eq]; exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hvV)
    rw [Submodule.map_sup] at hv_P2
    have hadd := (M ⊔ C.map (T i)).add_mem ((le_sup_left : M ≤ M ⊔ C.map (T i)) hv_M)
      (sup_le_sup_right hTB_le_M _ hv_P2)
    rwa [add_assoc, BitString.add_self, add_zero] at hadd
  have hCt_le : finrank Bool ↥(C.map (T i)) ≤ t := by
    have hrank := finrank_map_add_finrank_inf_ker_bool (T i) C
    change finrank Bool ↥(C.map (T i)) + _ = t at hrank
    omega
  have hfin_sup : finrank Bool ↥(A' ⊔ B.map (T i)) ≤ finrank Bool M + t :=
    finrank_sup_le_add_of_le_sup hsup_le hCt_le
  have hA_le_sup : s ≤ finrank Bool ↥(A' ⊔ B.map (T i)) := Submodule.finrank_mono le_sup_left
  refine ⟨idx, basicCond_subspace_boost_step hd hα0 hα1 B A' M C hr_half (by omega) ht_lt hexpand
    (hi_pig.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d (by omega)) s))
    (hA_le_sup.trans hfin_sup)⟩

/-- Key subspace dimension boost of `basicCond` for a subspace `V` of `BitString (m + m)` of
dimension `k ≤ m` with `δ * (2 * m) ≤ k` and `0 < m`. -/
private theorem basicCond_subspace_boost {m d : ℕ} (hm : 0 < m) (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (_hδhalf : δ ≤ 1 / 2)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m)))
    (hk_le : finrank Bool V ≤ m) (hk_ge : δ * ((m + m : ℕ) : ℝ) ≤ finrank Bool V) :
    ∃ idx : Fin (2 * d + 2),
      (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤ (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  set k := finrank Bool V
  let W : Submodule Bool (BitString (m + m)) := V ⊓ LinearMap.ker (projLeft m)
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  let B : Submodule Bool (BitString m) := W.map (projRight m)
  let P2 : Submodule Bool (BitString m) := V.map (projRight m)
  set s := finrank Bool A'
  set r := finrank Bool B
  have hB_le_P2 : B ≤ P2 := Submodule.map_mono inf_le_left
  have hdim_W : finrank Bool W = r := by
    have hkerW : W ⊓ LinearMap.ker (projRight m) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨_, hx1⟩, hx2⟩
      refine (appendLinearEquiv m m).symm.injective ?_
      rw [map_zero]
      exact Prod.ext (LinearMap.mem_ker.mp hx1) (LinearMap.mem_ker.mp hx2)
    have hrank := finrank_map_add_finrank_inf_ker_bool (projRight m) W
    rw [hkerW, finrank_bot, add_zero] at hrank
    exact hrank.symm
  have hsr : s + r = k := by
    have hrank := finrank_map_add_finrank_inf_ker_bool (projLeft m) V
    change s + finrank Bool W = k at hrank
    rwa [hdim_W] at hrank
  obtain ⟨C, hC_le, hC_inf, hC_sup⟩ := exists_isCompl_submodule_bool hB_le_P2
  set t := finrank Bool C
  have hP2_dim : finrank Bool P2 = r + t := by
    have hsum := finrank_sup_add_finrank_inf_bool C B
    rwa [hC_inf, hC_sup, finrank_bot, add_zero, add_comm] at hsum
  have hd_pos : (0 : ℝ) < d := by positivity
  have hk_2m : δ * (2 * (m : ℝ)) ≤ (k : ℝ) := by rw [two_mul]; exact_mod_cast hk_ge
  have htarget_le : (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤
      (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) := by
    have : (1 / 2 + α / (8 * (d : ℝ))) * (2 * (m : ℝ)) =
        (1 + α / (4 * (d : ℝ))) * (m : ℝ) := by field_simp; ring
    have hcoef_pos : 0 < 1 / 2 + α / (8 * (d : ℝ)) := by positivity
    nlinarith
  by_cases hs_big : (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (s : ℝ)
  · refine ⟨0, htarget_le.trans ?_⟩
    have hmap0 : V.map (basicCondAt T 0) = A' := by
      ext y; simp only [basicCondAt, basicCond_zero, A', Submodule.mem_map, LinearMap.comp_apply,
        LinearMap.proj_apply]
    rwa [hmap0]
  push Not at hs_big
  by_cases hP2_big : (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (finrank Bool P2 : ℝ)
  · refine ⟨⟨1, by omega⟩, htarget_le.trans ?_⟩
    have hmap1 : V.map (basicCondAt T ⟨1, by omega⟩) = P2 := by
      ext y
      simp only [basicCondAt, P2, Submodule.mem_map, LinearMap.comp_apply, LinearMap.proj_apply,
        basicCond_one]
    rwa [hmap1]
  push Not at hP2_big
  have ht_lt : (t : ℝ) ≤ α / (4 * (d : ℝ)) * (k : ℝ) := by
    have hsr_r : (s : ℝ) + (r : ℝ) = k := by exact_mod_cast hsr
    have hP2_r : (finrank Bool P2 : ℝ) = (r : ℝ) + (t : ℝ) := by exact_mod_cast hP2_dim
    linarith [show α / (4 * (d : ℝ)) * k = 2 * (α / (8 * (d : ℝ)) * k) by ring]
  have hP2_eq : V.map (projRight m) = B ⊔ C := hC_sup.symm.trans (sup_comm C B)
  rcases le_or_gt (2 * s) k with hs_half | hr_half
  · obtain ⟨idx, hidx⟩ := basicCond_subspace_boost_case1 hd hα0 hα1 hT V B C rfl hP2_eq
      (hs_half.trans hk_le) hsr hs_half ht_lt
    exact ⟨idx, htarget_le.trans hidx⟩
  · have hr_half' : 2 * r ≤ k := by omega
    obtain ⟨idx, hidx⟩ := basicCond_subspace_boost_case2 hd hα0 hα1 hT V B C rfl hP2_eq
      (hr_half'.trans hk_le) hsr hr_half' ht_lt
    exact ⟨idx, htarget_le.trans hidx⟩

/-- **Rate-boosting lemma for `basicCond`** ([LiZhong2024, Lemma 20]):
if `T` is an `α`-dimension expander of degree `d ≥ 3` (`0 < α ≤ 1`), then `basicCond T` is a
`(δ, (1 + α / (4 * d)) * δ)` affine somewhere condenser for every `0 < δ ≤ 1 / 2`. -/
theorem isAffineSomewhereCondenser_basicCond {m d : ℕ} (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α) :
    IsAffineSomewhereCondenser (basicCond T) δ ((1 + α / (4 * (d : ℝ))) * δ) := by
  intro X k hX hk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨k', -, -, hXk'⟩ := isAffineSource_map_of_isAffine hX
      (isAffine_of_linearMap (basicCondAt T 0))
    exact ⟨0, k', hXk', by simp only [Nat.cast_zero, mul_zero, Nat.cast_nonneg]⟩
  rcases hX with ⟨A, hA, hdim, rfl⟩
  have hboost : ∃ idx : Fin (2 * d + 2),
      (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤
        (finrank Bool ↥(A.direction.map (basicCondAt T idx)) : ℝ) := by
    by_cases hk_le : finrank Bool A.direction ≤ m
    · exact basicCond_subspace_boost hm hd hα0 hα1 hδ0 hδhalf hT A.direction hk_le
        (by rw [hdim]; exact hk)
    · push Not at hk_le
      obtain ⟨V', hV'_le, hV'_dim⟩ :=
        exists_submodule_finrank_eq_bool A.direction m hk_le.le
      have hge' : δ * ((m + m : ℕ) : ℝ) ≤ finrank Bool V' := by
        rw [hV'_dim]; push_cast; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      obtain ⟨idx, hidx⟩ := basicCond_subspace_boost hm hd hα0 hα1 hδ0 hδhalf hT V'
        hV'_dim.le hge'
      exact ⟨idx, hidx.trans (by exact_mod_cast Submodule.finrank_mono (Submodule.map_mono hV'_le))⟩
  obtain ⟨idx, hidx⟩ := hboost
  exact ⟨idx, _, isAffineSource_map_of_linear A hA (basicCondAt T idx), hidx⟩

/-! ### Iterated linear affine somewhere condenser (`SCond`, [LiZhong2024, Alg. 2 & Thm. 18]) -/

/-- **Iterated linear affine somewhere condenser** (`SCond`, [LiZhong2024, Alg. 2]):
applies `basicCond` across `h` halving rounds from `m * 2 ^ h` down to `m`, producing
`(2 * d + 2) ^ h` linear projections of length `m`. -/
@[expose] def sCond {d : ℕ} (T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m) :
    ∀ (h m : ℕ), BitString (m * 2 ^ h) →ₗ[Bool] (Fin ((2 * d + 2) ^ h) → BitString m)
  | 0, m =>
    { toFun := fun x _ => congrLinearEquiv (by ring) x
      map_add' := fun x y => by funext _; rw [map_add]; rfl
      map_smul' := fun c x => by funext _; rw [map_smul]; rfl }
  | h + 1, m =>
    let split : BitString (m * 2 ^ (h + 1)) →ₗ[Bool] BitString (m * 2 ^ h + m * 2 ^ h) :=
      (congrLinearEquiv (by ring)).toLinearMap
    let step1 := (basicCond (T (m * 2 ^ h))).comp split
    { toFun := fun x idx =>
        let p := finProdFinEquiv.symm (idx.cast (@Nat.pow_succ' (2 * d + 2) h))
        sCond T h m (step1 x p.1) p.2
      map_add' := fun x y => by
        funext idx
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c x => by
        funext idx
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }

private noncomputable def condStepRate (α : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  if r ≤ 1 / 2 then (1 + α / (4 * (d : ℝ))) * r else 1 / 2 + α / (8 * (d : ℝ))

private theorem condStepRate_ge_of_ge_half {α r : ℝ} {d : ℕ} (hr : 1 / 2 ≤ r) :
    1 / 2 + α / (8 * (d : ℝ)) ≤ condStepRate α d r := by
  unfold condStepRate
  split_ifs with h
  · obtain rfl := le_antisymm h hr
    exact le_of_eq (by ring)
  · exact le_rfl

private theorem isAffineSomewhereCondenser_sCond_aux {d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m}
    (hT : ∀ m, IsDimensionExpander (T m) α) :
    ∀ (h m : ℕ) (r : ℝ), 0 < r →
      IsAffineSomewhereCondenser (sCond T h m) r ((condStepRate α d)^[h] r)
  | 0, m, r, hr => by
    intro X k hX hk
    refine ⟨0, k, ?_, ?_⟩
    · let e : BitString (m * 2 ^ 0) ≃ₗ[Bool] BitString m := congrLinearEquiv (by ring)
      obtain ⟨A, hA, hdim, rfl⟩ := hX
      have hfn : (fun x => sCond T 0 m x 0) = ⇑e.toLinearMap := by
        funext x; rfl
      rw [hfn, ← hdim, (e.submoduleMap A.direction).finrank_eq]
      exact isAffineSource_map_of_linear A hA e.toLinearMap
    · simpa only [Function.iterate_zero, id_eq, pow_zero, mul_one] using hk
  | h + 1, m, r, hr => by
    intro X k hX hk
    have hr' : 0 < condStepRate α d r := by
      unfold condStepRate
      split_ifs <;> positivity
    let eCongr : BitString (m * 2 ^ (h + 1)) ≃ₗ[Bool] BitString (m * 2 ^ h + m * 2 ^ h) :=
      congrLinearEquiv (by ring)
    let r₀ : ℝ := min r (1 / 2)
    have hr₀_pos : 0 < r₀ := lt_min hr (by norm_num)
    have hr₀_half : r₀ ≤ 1 / 2 := min_le_right _ _
    have hX_congr : IsAffineSource (X.map eCongr) k := by
      obtain ⟨A, hA, hdim, rfl⟩ := hX
      change IsAffineSource ((uniformAffine A hA).map eCongr.toLinearMap) k
      rw [← hdim, (eCongr.submoduleMap A.direction).finrank_eq]
      exact isAffineSource_map_of_linear A hA eCongr.toLinearMap
    have hk_congr : r₀ * ((m * 2 ^ h + m * 2 ^ h : ℕ) : ℝ) ≤ (k : ℝ) := by
      rw [show m * 2 ^ h + m * 2 ^ h = m * 2 ^ (h + 1) by ring]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans hk
    obtain ⟨i₁, k₁, hX₁, hk₁⟩ :=
      isAffineSomewhereCondenser_basicCond hd hα0 hα1 hr₀_pos hr₀_half (hT (m * 2 ^ h))
        (X.map eCongr) k hX_congr hk_congr
    have hk₁' : condStepRate α d r * ((m * 2 ^ h : ℕ) : ℝ) ≤ (k₁ : ℝ) := by
      refine (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)).trans hk₁
      unfold condStepRate
      split_ifs with hle
      · simp only [r₀, min_eq_left hle, le_refl]
      · rw [show r₀ = 1 / 2 from min_eq_right (lt_of_not_ge hle).le]
        exact le_of_eq (by ring)
    have hX₁_eq : (X.map eCongr).map (fun y => basicCond (T (m * 2 ^ h)) y i₁) =
        X.map (fun x => basicCond (T (m * 2 ^ h)) (eCongr x) i₁) := by
      rw [PMF.map_comp]; rfl
    rw [hX₁_eq] at hX₁
    obtain ⟨i₂, k₂, hX₂, hk₂⟩ :=
      isAffineSomewhereCondenser_sCond_aux hd hα0 hα1 hT h m (condStepRate α d r) hr'
        _ k₁ hX₁ hk₁'
    rw [Function.iterate_succ_apply]
    let idx : Fin ((2 * d + 2) ^ (h + 1)) :=
      (finProdFinEquiv (i₁, i₂)).cast (@Nat.pow_succ' (2 * d + 2) h).symm
    refine ⟨idx, k₂, ?_, hk₂⟩
    have hmap : X.map (fun x => sCond T (h + 1) m x idx) =
        (X.map (fun x => basicCond (T (m * 2 ^ h)) (eCongr x) i₁)).map
          (fun y => sCond T h m y i₂) := by
      rw [PMF.map_comp]
      congr 1 with x
      have hcast : idx.cast (@Nat.pow_succ' (2 * d + 2) h) = finProdFinEquiv (i₁, i₂) := by
        ext; simp only [idx, Fin.val_cast]
      simp only [sCond, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hcast, finProdFinEquiv.symm_apply_apply]
      rfl
    rw [hmap]
    exact hX₂

/-- **Iterated linear affine somewhere condenser** ([LiZhong2024, Thm. 18]):
given any family `T` of `α`-dimension expanders of degree `d ≥ 3` (`0 < α ≤ 1`), for every
`0 < δ ≤ 1 / 2` and every `h` satisfying `1 / 2 ≤ δ * (1 + α / (4 * d)) ^ h`, iterating
`basicCond` for `h + 1` steps gives a linear `(δ, 1 / 2 + α / (8 * d))` affine somewhere
condenser `sCond T (h + 1) m`. -/
theorem isAffineSomewhereCondenser_sCond {d : ℕ} (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ)
    {h : ℕ} (hh : 1 / 2 ≤ δ * (1 + α / (4 * (d : ℝ))) ^ h)
    {T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m}
    (hT : ∀ m, IsDimensionExpander (T m) α) (m : ℕ) :
    IsAffineSomewhereCondenser (sCond T (h + 1) m) δ (1 / 2 + α / (8 * (d : ℝ))) := by
  have hhalf {x : ℝ} (hx : 1 / 2 ≤ x) : 1 / 2 ≤ condStepRate α d x :=
    (le_add_of_nonneg_right (by positivity)).trans (condStepRate_ge_of_ge_half hx)
  have hge_half : 1 / 2 ≤ (condStepRate α d)^[h] δ := by
    have hiter : ∀ j : ℕ, 1 / 2 ≤ (condStepRate α d)^[j] δ ∨
        (condStepRate α d)^[j] δ = δ * (1 + α / (4 * (d : ℝ))) ^ j := by
      intro j
      induction j with
      | zero => right; simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with hj | hj
        · exact .inl (hhalf hj)
        rw [hj]
        by_cases hle : δ * (1 + α / (4 * (d : ℝ))) ^ j ≤ 1 / 2
        · right
          rw [condStepRate, ite_eq_left hle, pow_succ]
          ring
        · exact .inl (hhalf (lt_of_not_ge hle).le)
    exact (hiter h).elim id fun h2 => by rwa [h2]
  have hstep : 1 / 2 + α / (8 * (d : ℝ)) ≤ (condStepRate α d)^[h + 1] δ := by
    rw [Function.iterate_succ_apply']
    exact condStepRate_ge_of_ge_half hge_half
  intro X k hX hk
  obtain ⟨i, k', hX', hk'⟩ :=
    isAffineSomewhereCondenser_sCond_aux hd hα0 hα1 hT (h + 1) m δ hδ0 X k hX hk
  exact ⟨i, k', hX', (mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg m)).trans hk'⟩

end Cslib.AffineDisperser.Li
