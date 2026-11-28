/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The flattening bound for matrix multiplication

A bilinear algorithm for `p × q` by `q × r` matrix multiplication, over a nontrivial commutative
ring, needs at least `p r` multiplications (`Cslib.Tensor.mul_le_of_rank_mm`), one for each entry
of the product. The `p r` output coordinates of `⟨p, q, r⟩` are bilinear forms, and each is a
combination of the `s` rank-one forms of a decomposition. The matrix of the output coordinates has
a right inverse that reads entry `(i, k)` off the inputs `e_{i 0}` and `e_{0 k}`, so its rank is
`p r`, and it factors through `s` coordinates.

## Main results

* `Cslib.Tensor.mul_le_of_rank_mm`: `Rank s (mm p q r)` with `0 < q` gives `p * r ≤ s`.
* `Cslib.Tensor.mul_self_le_of_rank_mm`: `Rank s (mm v v v)` gives `v * v ≤ s`.
-/

public section

namespace Cslib.Tensor

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- **The flattening bound.** A rank decomposition of `⟨p, q, r⟩` with `q ≥ 1` has at least `p r`
terms. -/
theorem mul_le_of_rank_mm {p q r s : ℕ} (hq : 0 < q) (h : Rank s (mm p q r : Tensor K _ _ _)) :
    p * r ≤ s := by
  classical
  obtain ⟨α, β, γ, h⟩ := h
  -- the `s` rank-one bilinear forms of the decomposition
  let W : Matrix (Fin s) ((Fin p × Fin q) × (Fin q × Fin r)) K :=
    Matrix.of fun ν xy => α ν xy.1 * β ν xy.2
  -- a right inverse of the output flattening of `⟨p, q, r⟩`
  let j₀ : Fin q := ⟨0, hq⟩
  let S : Matrix ((Fin p × Fin q) × (Fin q × Fin r)) (Fin p × Fin r) K :=
    Matrix.of fun xy c => if ((c.1, j₀), (j₀, c.2)) = xy then 1 else 0
  have hγW (c : Fin p × Fin r) (xy : (Fin p × Fin q) × (Fin q × Fin r)) :
      (γ * W) c xy = (mm p q r : Tensor K _ _ _) xy.1 xy.2 c := by
    rw [← h, restrict_unit, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun ν _ => by simp only [W, Matrix.of_apply]; ring
  have hone : γ * W * S = 1 := by
    ext c c'
    rw [Matrix.mul_apply]
    simp only [hγW, S, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mm_apply, Matrix.one_apply]
    by_cases hc : c = c' <;> grind [Prod.ext_iff]
  calc p * r = (1 : Matrix (Fin p × Fin r) (Fin p × Fin r) K).rank := by simp [Matrix.rank_one]
    _ = (γ * W * S).rank := by rw [hone]
    _ ≤ (γ * W).rank := Matrix.rank_mul_le_left _ _
    _ ≤ γ.rank := Matrix.rank_mul_le_left _ _
    _ ≤ s := by simpa using Matrix.rank_le_card_width γ

/-- A rank decomposition of `⟨v, v, v⟩` has at least `v ^ 2` terms. -/
theorem mul_self_le_of_rank_mm {v s : ℕ} (h : Rank s (mm v v v : Tensor K _ _ _)) : v * v ≤ s := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · exact mul_le_of_rank_mm hv h

end Cslib.Tensor
