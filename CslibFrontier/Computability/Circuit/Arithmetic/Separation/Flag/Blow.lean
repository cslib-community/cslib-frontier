/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Len

/-!
# Blow-ups `N ↦ N ⊗ 1` of matrices over `F₂`

An embedding `e : μ × κ ↪ ι` blows a matrix over `μ` up to a block matrix over `ι`
(`Flag.blow`), with a complement (`Flag.blowC`) and the invertible blow-ups `Flag.blowU`.
`Flag.Contr l μ s` says that a length `l` contracts by the factor `s` under blowing up.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Blow`.

## Main definitions

* `Flag.incl` (inclusion matrices of embeddings), `Flag.inc`, `Flag.blow`, `Flag.blowC`,
`Flag.blowU`, `Flag.Contr`.

## Main results

* `Flag.blow_mul`, `Flag.blow_dg`, `Flag.blowU_mul`: blow-ups are multiplicative.
* `Flag.DM_blow`, `Flag.DM_digit`: averages of blown-up matrices.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

section Incl

variable {α β γ : Type*} [DecidableEq β]

/-- The inclusion matrix of an embedding `e : α ↪ β`: the columns `e x` of the identity. -/
@[expose] def incl (e : α ↪ β) : Matrix β α F2 := (1 : Matrix β β F2).submatrix id e

theorem incl_apply (e : α ↪ β) (i : β) (x : α) : incl e i x = if i = e x then 1 else 0 :=
  Matrix.one_apply

theorem incl_t_mul_incl [Fintype β] (e : α ↪ β) (e' : γ ↪ β) :
    (incl e)ᵀ * incl e' = (1 : Matrix β β F2).submatrix e e' := by
  rw [incl, incl, Matrix.transpose_submatrix, Matrix.transpose_one,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  simp

theorem incl_t_mul [Fintype β] [DecidableEq α] (e : α ↪ β) : (incl e)ᵀ * incl e = 1 := by
  rw [incl_t_mul_incl, Matrix.submatrix_one_embedding]

/-- Embeddings with disjoint ranges have orthogonal inclusion matrices. -/
theorem incl_t_mul_eq_zero [Fintype β] (e : α ↪ β) (e' : γ ↪ β) (h : ∀ x y, e x ≠ e' y) :
    (incl e)ᵀ * incl e' = 0 := by
  ext x y
  simp [incl_t_mul_incl, h x y]

end Incl

variable {μ κ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- The inclusion matrix of the embedding `μ × κ ↪ ι` of a blow-up. -/
abbrev inc (e : μ × κ ↪ ι) : Matrix ι (μ × κ) F2 := incl e

omit [Fintype μ] [Fintype κ] in
theorem inc_t_mul (e : μ × κ ↪ ι) : (inc e)ᵀ * inc e = 1 := incl_t_mul e

omit [Fintype ι] in
theorem inc_mul_diag (e : μ × κ ↪ ι) (T : Finset (μ × κ)) :
    inc e * dg T * (inc e)ᵀ = dg (T.map e) := by
  ext i j
  simp only [Matrix.mul_apply, inc, incl_apply, dg, Matrix.transpose_apply, Matrix.diagonal_apply,
    Finset.mem_map, mul_ite, mul_one, mul_zero]
  by_cases hi : ∃ x, e x = i
  · obtain ⟨x, rfl⟩ := hi
    by_cases hj : ∃ y, e y = j
    · obtain ⟨y, rfl⟩ := hj
      by_cases hxy : x = y <;> simp [e.injective.eq_iff, hxy]
    · simp [not_exists.mp hj, fun y => Ne.symm (not_exists.mp hj y)]
  · simp [not_exists.mp hi, fun y => Ne.symm (not_exists.mp hi y)]

/-- The blow-up of a matrix along an embedding. -/
def blow (e : μ × κ ↪ ι) (N : Matrix μ μ F2) : Matrix ι ι F2 :=
  inc e * (Matrix.kroneckerMap (· * ·) N (1 : Matrix κ κ F2)) * (inc e)ᵀ

omit [DecidableEq μ] [Fintype ι] in
theorem blow_add (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M + N) = blow e M + blow e N := by
  unfold blow
  rw [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq μ] in
theorem blow_mul (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M * N) = blow e M * blow e N := by
  classical
  simp only [blow, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (inc e)ᵀ (inc e), inc_t_mul, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.kroneckerMap _ M 1), ← Matrix.mul_kronecker_mul, Matrix.mul_one]

omit [Fintype ι] in
theorem blow_dg (e : μ × κ ↪ ι) (T : Finset μ) :
    blow e (dg T) = dg ((T ×ˢ (univ : Finset κ)).map e) := by
  unfold blow
  rw [← inc_mul_diag]
  congr 2
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.kroneckerMap_apply, dg, Matrix.diagonal_apply, Matrix.one_apply,
    Finset.mem_product, Finset.mem_univ, and_true, Prod.mk.injEq]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- The complement of the blow-up of one. -/
def blowC (e : μ × κ ↪ ι) : Matrix ι ι F2 := 1 - blow e 1

theorem blow_mul_blowC (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blow e M * blowC e = 0 := by
  rw [blowC, Matrix.mul_sub, ← blow_mul, Matrix.mul_one, Matrix.mul_one, sub_self]

theorem blowC_mul_blow (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blowC e * blow e M = 0 := by
  rw [blowC, Matrix.sub_mul, ← blow_mul, Matrix.one_mul, Matrix.one_mul, sub_self]

theorem blowC_sq (e : μ × κ ↪ ι) : blowC e * blowC e = blowC e := by
  conv_lhs => rw [blowC, Matrix.sub_mul, ← blowC, blow_mul_blowC, Matrix.one_mul, sub_zero]

theorem blow_unit_aux (e : μ × κ ↪ ι) {M N : Matrix μ μ F2} (h : M * N = 1) :
    (blow e M + blowC e) * (blow e N + blowC e) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ← blow_mul, h, blow_mul_blowC,
    blowC_mul_blow, blowC_sq, add_zero, zero_add, blowC]
  abel

/-- Blow-ups of invertible matrices, extended by the identity. -/
def blowU (e : μ × κ ↪ ι) (p : GLM μ) : GLM ι where
  val := blow e p + blowC e
  inv := blow e (p⁻¹ : GLM μ) + blowC e
  val_inv := blow_unit_aux e (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  inv_val := blow_unit_aux e (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

theorem blowU_mul (e : μ × κ ↪ ι) (p q : GLM μ) (M : Matrix μ μ F2) :
    (blowU e p : Matrix ι ι F2) * blow e M * (blowU e q : Matrix ι ι F2) =
      blow e ((p : Matrix μ μ F2) * M * (q : Matrix μ μ F2)) := by
  change (blow e p + blowC e) * blow e M * (blow e q + blowC e) = _
  rw [Matrix.add_mul, blowC_mul_blow, add_zero, Matrix.mul_add, ← blow_mul, blow_mul_blowC,
    add_zero, ← blow_mul]

/-- The contraction hypothesis of the contracting case for a function on a group: along every
additive map
from μ×μ matrices, full rank is only `s²` times as far as rank one. -/
@[expose] def Contr {G : Type*} [Group G] (l : Len G) (μ : ℕ) (s : ℝ) : Prop :=
  ∀ τ : Matrix (Fin μ) (Fin μ) F2 → G, (∀ M N, τ (M + N) = τ M * τ N) →
    ∀ i, DM (fun M => l (τ M)) (dg univ) ≤ s ^ 2 * DM (fun M => l (τ M)) (dg {i})

theorem DM_blow (e : μ × κ ↪ ι) (f : Matrix ι ι F2 → ℝ) (M : Matrix μ μ F2) :
    ∑ p : GLM ι, ∑ q : GLM ι,
      DM (fun N => f ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2))) M =
      (Fintype.card (GLM μ) : ℝ) ^ 2 * DM f (blow e M) := by
  have h (a b : GLM μ) : ∑ p : GLM ι, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 = DM f (blow e M) := by
    rw [← blowU_mul, ← DM_mul f (blowU e a) (blowU e b) (blow e M)]; rfl
  simp only [DM] at h ⊢
  calc _ = ∑ a : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι, ∑ b : GLM μ, _ :=
        (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
    _ = ∑ a : GLM μ, ∑ b : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι, _ :=
        sum_congr rfl fun _ _ => (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
    _ = _ := by simp only [h, sum_const, card_univ, nsmul_eq_mul]; ring

variable {G : Type*} [Group G]

omit [DecidableEq κ] in
theorem DM_digit (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) (e : Fin m × κ ↪ ι) (i : Fin m) :
    DM (fun M => l (τ M)) (dg ((univ : Finset (Fin m × κ)).map e)) ≤
      s ^ 2 * DM (fun M => l (τ M)) (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e)) := by
  classical
  have : 0 < Fintype.card (GLM (Fin m)) := Fintype.card_pos
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < (Fintype.card (GLM (Fin m)) : ℝ) ^ 2)
  rw [mul_left_comm, ← univ_product_univ, ← blow_dg, ← blow_dg, ← DM_blow, ← DM_blow]
  simp_rw [mul_sum]
  exact sum_le_sum fun p _ => sum_le_sum fun q _ =>
    hC (fun N => τ ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2)))
      (fun M N => by rw [blow_add, Matrix.mul_add, Matrix.add_mul, hτ]) i

end Cslib.Circuits.Arithmetic.Separation.Flag
