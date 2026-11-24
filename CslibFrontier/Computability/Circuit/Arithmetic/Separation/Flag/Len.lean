/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.InnerProductSpace.PiL2
public import Cslib.Tactic.Membership
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
# Length functions on groups, and averages over pairs of invertible matrices

`Flag.Len G`: a length function on a group (`val 1 = 0`, symmetric, subadditive). Over `F₂`,
`Flag.DM f M` sums `f (p M q)²` over all pairs of invertible matrices `p, q`, and `Flag.dg S`
is the diagonal matrix of a set `S` of indices; `DM` depends on `dg S` only through `|S|`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Len`.

## Main definitions

* `Flag.Len` (group seminorms), `Flag.GLM`, `Flag.DM`, `Flag.dg`, `Flag.permU`.

## Main results

* `Flag.Len.conj`; `Flag.sqrt_sum_le` (Minkowski for square sums).
* `Flag.DM_dg_congr`, `Flag.DM_dg_le`: averages over diagonal matrices.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

/-- Length functions on a group, such as `g ↦ dist z (g • z)` for an isometric action: Mathlib's
group seminorms. The abbreviation keeps the Flag-specific quantities (`Len.S`, `Len.T`,
`Len.rms`) available by dot notation; the laws are `map_one_eq_zero`, `map_inv_eq_map`,
`map_mul_le_add` and `apply_nonneg`. -/
abbrev Len (G : Type*) [Group G] := GroupSeminorm G

namespace Len
variable {G : Type*} [Group G] (l : Len G)

theorem conj (g h : G) : l (g * h * g⁻¹) ≤ 2 * l g + l h := by
  have h1 := map_mul_le_add l (g * h) g⁻¹
  have h2 := map_mul_le_add l g h
  rw [map_inv_eq_map l] at h1
  linarith

end Len

/-- Minkowski's inequality for square sums over a finset, after a coordinatewise bound
`0 ≤ c ≤ a + b`: the triangle inequality in `EuclideanSpace ℝ s`. -/
theorem sqrt_sum_le {α : Type*} (s : Finset α) (a b c : α → ℝ)
    (hc : ∀ i, 0 ≤ c i) (h : ∀ i, c i ≤ a i + b i) :
    √(∑ i ∈ s, c i ^ 2) ≤ √(∑ i ∈ s, a i ^ 2) + √(∑ i ∈ s, b i ^ 2) := by
  refine (Real.sqrt_le_sqrt (sum_le_sum fun i _ => pow_le_pow_left₀ (hc i) (h i) 2)).trans ?_
  have hn := norm_add_le (WithLp.toLp 2 fun i : s => a i : EuclideanSpace ℝ s)
    (WithLp.toLp 2 fun i : s => b i)
  simp only [EuclideanSpace.norm_eq, ← WithLp.toLp_add, Pi.add_apply,
    Real.norm_eq_abs, sq_abs] at hn
  simpa only [Finset.sum_coe_sort s (fun i => (a i + b i) ^ 2),
    Finset.sum_coe_sort s (fun i => a i ^ 2), Finset.sum_coe_sort s (fun i => b i ^ 2)] using hn

/-- The field with two elements. -/
abbrev F2 := ZMod 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invertible matrices. -/
abbrev GLM (ι : Type*) [Fintype ι] [DecidableEq ι] := (Matrix ι ι F2)ˣ

noncomputable instance : Fintype (GLM ι) := Fintype.ofFinite _

/-- The sum of `f(PMQ)²` over invertible `P`, `Q`. -/
@[expose] noncomputable def DM (f : Matrix ι ι F2 → ℝ) (M : Matrix ι ι F2) : ℝ :=
  ∑ p : GLM ι, ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2

theorem DM_mul (f : Matrix ι ι F2 → ℝ) (a b : GLM ι) (M : Matrix ι ι F2) :
    DM f ((a : Matrix ι ι F2) * M * (b : Matrix ι ι F2)) = DM f M := by
  unfold DM
  rw [← Equiv.sum_comp (Equiv.mulRight a)
    (fun p : GLM ι => ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun p _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft b)
    (fun q : GLM ι => f (((Equiv.mulRight a p : GLM ι) : Matrix ι ι F2) * M *
      (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.coe_mulLeft, Units.val_mul, Matrix.mul_assoc]

/-- The diagonal idempotent of a set of indices. -/
@[expose] def dg (S : Finset ι) : Matrix ι ι F2 := Matrix.diagonal fun i => if i ∈ S then 1 else 0

omit [Fintype ι] in
theorem dg_empty : dg (∅ : Finset ι) = 0 := by
  simp [dg]

omit [Fintype ι] in
theorem dg_union {S T : Finset ι} (h : Disjoint S T) : dg (S ∪ T) = dg S + dg T := by
  unfold dg
  rw [Matrix.diagonal_add]
  congr 1
  funext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.1 h hS
    simp [hS, hT]
  · simp [hS]

/-- The unit of a permutation. -/
def permU (σ : Equiv.Perm ι) : GLM ι where
  val := (1 : Matrix ι ι F2).submatrix σ id
  inv := (1 : Matrix ι ι F2).submatrix id σ
  val_inv := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]
  inv_val := by
    rw [Matrix.submatrix_mul_equiv (1 : Matrix ι ι F2) (1 : Matrix ι ι F2) id σ id]
    simp

theorem permU_conj (σ : Equiv.Perm ι) (M : Matrix ι ι F2) :
    (permU σ : Matrix ι ι F2) * M * ((permU σ)⁻¹ : GLM ι) = M.submatrix σ σ := by
  ext i j
  simp [permU, Matrix.mul_apply, Matrix.one_apply]

theorem DM_dg_congr (f : Matrix ι ι F2 → ℝ) {S T : Finset ι} (h : S.card = T.card) :
    DM f (dg S) = DM f (dg T) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, ∀ i, σ i ∈ S ↔ i ∈ T := by
    have e : {i // i ∈ T} ≃ {i // i ∈ S} := Fintype.equivOfCardEq (by simp [h])
    refine ⟨e.extendSubtype, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · by_contra hT
      exact e.extendSubtype_not_mem i hT hi
    · exact e.extendSubtype_mem i hi
  rw [← DM_mul f (permU σ) ((permU σ)⁻¹) (dg S), permU_conj]
  congr 1
  ext i j
  simp only [dg, Matrix.submatrix_apply, Matrix.diagonal_apply, σ.injective.eq_iff, hσ]

theorem DM_dg_le (f : Matrix ι ι F2 → ℝ) (hf : ∀ M, 0 ≤ f M)
    (hadd : ∀ M N, f (M + N) ≤ f M + f N) {S T : Finset ι} (h : Disjoint S T) :
    √(DM f (dg (S ∪ T))) ≤ √(DM f (dg S)) + √(DM f (dg T)) := by
  unfold DM
  simp only [← Fintype.sum_prod_type']
  refine sqrt_sum_le univ _ _ _ (fun _ => hf _) fun x => ?_
  rw [dg_union h, Matrix.mul_add, Matrix.add_mul]
  exact hadd _ _

end Cslib.Circuits.Arithmetic.Separation.Flag
