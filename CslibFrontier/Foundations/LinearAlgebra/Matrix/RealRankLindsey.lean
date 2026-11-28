/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real-rank Lindsey lemma over `𝔽₂`

Strengthens Lindsey's character-sum bound (`CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey`)
from combinatorial rectangles to real-weighted `ℓ²` vectors and arbitrary real matrices of low
rank: orthogonal projection onto non-zero columns decomposes any `M : Matrix (α → ZMod 2)
(β → ZMod 2) ℝ` into `M.rank` orthogonal rank-one pieces whose squared Frobenius norms sum to
`∑ p, ∑ q, M p q ^ 2`.

## Main results

* `Matrix.sq_sum_bilinear_mul_two_pow_rank_le_l2`: `ℓ²`-weighted Lindsey's lemma over `𝔽₂`.
* `Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le`: real-rank Lindsey's lemma over `𝔽₂`.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
-/

public section

namespace Matrix

open Finset

variable {α β : Type*}

/-- **`ℓ²`-weighted Lindsey's lemma over `𝔽₂`.** For any matrix `B : Matrix α β (ZMod 2)` and real
weight vectors `g` and `h`,
`(∑_{p, q} g(p) h(q) (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ (∑_p g(p)²) (∑_q h(q)²) 2^{|α|} 2^{|β|}`. -/
theorem sq_sum_bilinear_mul_two_pow_rank_le_l2 [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (B : Matrix α β (ZMod 2)) (g : (α → ZMod 2) → ℝ) (h : (β → ZMod 2) → ℝ) :
    (∑ p, ∑ q, g p * h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2 * 2 ^ B.rank ≤
      (∑ p, g p ^ 2) * (∑ q, h q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β := by
  classical
  set H : (α → ZMod 2) → ℝ := fun p => ∑ q, h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val
  set K := #{z : β → ZMod 2 | B *ᵥ z = 0}
  have hsum : ∑ p, ∑ q, g p * h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val = ∑ p, g p * H p := by
    refine Fintype.sum_congr _ _ fun p => ?_
    simp only [H, Finset.mul_sum, mul_assoc]
  have hCS : (∑ p, g p * H p) ^ 2 ≤ (∑ p, g p ^ 2) * ∑ p, H p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq univ g H
  have hexp : ∑ p, H p ^ 2 = ∑ q, ∑ q', h q * h q' *
      (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) := by
    calc ∑ p, H p ^ 2
        = ∑ p, ∑ q, ∑ q', h q * h q' * (-1 : ℝ) ^ (p ⬝ᵥ (B *ᵥ q + B *ᵥ q')).val := by
          refine Fintype.sum_congr _ _ fun p => ?_
          simp only [H, sq, Finset.sum_mul_sum, dotProduct_add, ZMod.neg_one_pow_val_add]
          refine Fintype.sum_congr _ _ fun q => Fintype.sum_congr _ _ fun q' => ?_
          ring
      _ = ∑ q, ∑ q', ∑ p, h q * h q' * (-1 : ℝ) ^ (p ⬝ᵥ (B *ᵥ q + B *ᵥ q')).val := by
          rw [Finset.sum_comm]
          exact Fintype.sum_congr _ _ fun q => Finset.sum_comm
      _ = _ := by
          refine Fintype.sum_congr _ _ fun q => Fintype.sum_congr _ _ fun q' => ?_
          rw [← Finset.mul_sum, sum_neg_one_pow_val_dotProduct]
          have heq : B *ᵥ q + B *ᵥ q' = 0 ↔ B *ᵥ q' = B *ᵥ q := by
            rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self, eq_comm]
          rw [if_congr heq rfl rfl]
  set I : (β → ZMod 2) → (β → ZMod 2) → ℝ := fun q q' =>
    if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0
  have hfibre : ∑ p, H p ^ 2 ≤ (∑ q, h q ^ 2) * K * (2 : ℝ) ^ Fintype.card α := by
    have hrow (q) : ∑ q', I q q' = K * 2 ^ Fintype.card α := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        card_filter_mulVec_eq B q]
    have hswap : ∑ q, ∑ q', h q' ^ 2 * I q q' = ∑ q, ∑ q', h q ^ 2 * I q q' := by
      rw [Finset.sum_comm]; simp only [I, eq_comm]
    rw [hexp]
    have h2 : 2 * ∑ q, ∑ q', h q * h q' * I q q' ≤
        ∑ q, ∑ q', h q ^ 2 * I q q' + ∑ q, ∑ q', h q' ^ 2 * I q q' := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      gcongr with q _ q' _
      have : 0 ≤ I q q' := by simp only [I]; split_ifs <;> positivity
      linarith [mul_nonneg (sq_nonneg (h q - h q')) this]
    simp only [hswap, ← Finset.mul_sum, hrow, ← Finset.sum_mul] at h2
    linarith
  have hK : (K : ℝ) * 2 ^ B.rank = 2 ^ Fintype.card β := by
    exact_mod_cast card_ker_mul_two_pow_rank B
  have hg0 : 0 ≤ ∑ p, g p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg (g p)
  have hpow : (0 : ℝ) ≤ 2 ^ B.rank := by positivity
  rw [hsum]
  calc (∑ p, g p * H p) ^ 2 * 2 ^ B.rank
      ≤ (∑ p, g p ^ 2) * ((∑ q, h q ^ 2) * K * (2 : ℝ) ^ Fintype.card α) * 2 ^ B.rank :=
        mul_le_mul_of_nonneg_right (hCS.trans (mul_le_mul_of_nonneg_left hfibre hg0)) hpow
    _ = (∑ p, g p ^ 2) * (∑ q, h q ^ 2) * 2 ^ Fintype.card α * ((K : ℝ) * 2 ^ B.rank) := by ring
    _ = _ := by rw [hK]

/-- Induction helper for `sq_sum_matrix_bilinear_mul_two_pow_rank_le`: any matrix `M` of rank at
most `r` satisfies `(∑ M_{p, q} (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ r ‖M‖_F² 2^{|α| + |β|}`. -/
private theorem sq_sum_matrix_bilinear_le_of_rank_le [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (B : Matrix α β (ZMod 2)) :
    ∀ (r : ℕ) (M : Matrix (α → ZMod 2) (β → ZMod 2) ℝ), M.rank ≤ r →
      (∑ p, ∑ q, M p q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2 * 2 ^ B.rank ≤
        r * (∑ p, ∑ q, M p q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β
  | 0, M, hr => by
    classical
    obtain rfl : M = 0 := Matrix.toLin'.injective <| by
      rw [map_zero, Matrix.toLin'_apply']
      exact LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 (Nat.eq_zero_of_le_zero hr))
    simp
  | r + 1, M, hr => by
    classical
    by_cases hzero : ∀ p q, M p q = 0
    · simp only [hzero, zero_mul, sum_const_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      positivity
    · push Not at hzero
      obtain ⟨p₀, q₀, hpq₀⟩ := hzero
      set v : (α → ZMod 2) → ℝ := fun p => M p q₀
      set s : ℝ := ∑ p, v p ^ 2
      have hs : 0 < s := lt_of_lt_of_le (sq_pos_of_ne_zero hpq₀)
        (Finset.single_le_sum (fun p _ => sq_nonneg (v p)) (mem_univ p₀))
      set c : (β → ZMod 2) → ℝ := fun q => (∑ p, v p * M p q) / s
      set N : Matrix (α → ZMod 2) (β → ZMod 2) ℝ := Matrix.of fun p q => M p q - v p * c q
      have horth (q : β → ZMod 2) : ∑ p, v p * N p q = 0 := by
        have hsub : ∀ p, v p * N p q = v p * M p q - c q * v p ^ 2 := fun p => by
          simp only [N, of_apply]; ring
        simp_rw [hsub, Finset.sum_sub_distrib, ← Finset.mul_sum]
        dsimp [c, s]
        rw [div_mul_cancel₀ _ hs.ne', sub_self]
      have hpyth : ∑ p, ∑ q, M p q ^ 2 = s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2 := by
        have hcol (q : β → ZMod 2) : ∑ p, M p q ^ 2 = c q ^ 2 * s + ∑ p, N p q ^ 2 := by
          have hpt : ∀ p, M p q ^ 2 =
              c q ^ 2 * v p ^ 2 + 2 * c q * (v p * N p q) + N p q ^ 2 := fun p => by
            simp only [N, of_apply]; ring
          simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, horth q]
          dsimp [s]; ring
        rw [Finset.sum_comm (f := fun p q => M p q ^ 2),
          Finset.sum_comm (f := fun p q => N p q ^ 2)]
        simp_rw [hcol, Finset.sum_add_distrib, ← Finset.sum_mul]
        ring
      let e₀ : (β → ZMod 2) → ℝ := Pi.single q₀ 1
      have hN_le : LinearMap.range N.mulVecLin ≤ LinearMap.range M.mulVecLin := by
        rintro _ ⟨x, rfl⟩
        refine ⟨x - (c ⬝ᵥ x) • Pi.single q₀ 1, ?_⟩
        rw [mulVecLin_apply, mulVecLin_apply, mulVec_sub, mulVec_smul, mulVec_single_one]
        ext p
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, col_apply, mulVec, dotProduct, N, v,
          of_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
        congr 1; exact Finset.sum_congr rfl fun q _ => by ring
      have hN_lt : LinearMap.range N.mulVecLin < LinearMap.range M.mulVecLin := by
        refine lt_of_le_of_ne hN_le fun heq => ?_
        obtain ⟨x, hx⟩ : v ∈ LinearMap.range N.mulVecLin := by
          rw [heq]; exact ⟨e₀, funext fun p => by simp [e₀, mulVec_single, v]⟩
        have hdot := dotProduct_mulVec v N x
        rw [mulVecLin_apply] at hx
        rw [hx, show v ᵥ* N = 0 from funext horth, zero_dotProduct] at hdot
        have hvv : v ⬝ᵥ v = s := by simp [dotProduct, s, sq]
        linarith
      have hrank_lt : N.rank < M.rank := Submodule.finrank_lt_finrank_of_lt hN_lt
      have hNrank : N.rank ≤ r := by omega
      set S₁ := ∑ p, ∑ q, v p * c q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val
      set S₂ := ∑ p, ∑ q, N p q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val
      have hSM : ∑ p, ∑ q, M p q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val = S₁ + S₂ := by
        have hpt : ∀ p q, M p q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val =
            v p * c q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val +
              N p q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val := fun p q => by
          simp only [N, of_apply]; ring
        simp_rw [hpt, Finset.sum_add_distrib]
        rfl
      have hI₁ : S₁ ^ 2 * 2 ^ B.rank ≤
          s * (∑ q, c q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β :=
        sq_sum_bilinear_mul_two_pow_rank_le_l2 B v c
      have hI₂ : S₂ ^ 2 * 2 ^ B.rank ≤
          r * (∑ p, ∑ q, N p q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β :=
        sq_sum_matrix_bilinear_le_of_rank_le B r N hNrank
      rw [hSM, hpyth]
      have hpow : (0 : ℝ) < 2 ^ B.rank := by positivity
      have hNW : 0 ≤ (∑ p, ∑ q, N p q ^ 2) * (2 ^ Fintype.card α * 2 ^ Fintype.card β) := by
        positivity
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · have hS₂ : S₂ = 0 := pow_eq_zero_iff two_ne_zero |>.1 <| le_antisymm
          (nonpos_of_mul_nonpos_left (by simpa using hI₂) hpow) (sq_nonneg S₂)
        rw [hS₂, zero_add, Nat.cast_one, one_mul, add_zero]
        linarith
      · have hr : (0 : ℝ) < r := by exact_mod_cast hrpos
        push_cast
        refine le_of_mul_le_mul_left ?_ hr
        linarith [mul_le_mul_of_nonneg_left hI₁ (by positivity : (0 : ℝ) ≤ r * (r + 1)),
          mul_le_mul_of_nonneg_left hI₂ (by positivity : (0 : ℝ) ≤ r + 1),
          mul_nonneg (sq_nonneg ((r : ℝ) * S₁ - S₂)) hpow.le]

/-- **Real-rank Lindsey's lemma over `𝔽₂`.** For any matrix `B : Matrix α β (ZMod 2)`, any real
matrix `M : Matrix (α → ZMod 2) (β → ZMod 2) ℝ`, and any weights `|g(p)| ≤ 1`, `|h(q)| ≤ 1`,
`(∑_{p, q} M_{p, q} g(p) h(q) (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ rank M · ‖M‖_F² · 2^{|α|} 2^{|β|}`.
-/
theorem sq_sum_matrix_bilinear_mul_two_pow_rank_le [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (B : Matrix α β (ZMod 2)) (M : Matrix (α → ZMod 2) (β → ZMod 2) ℝ)
    (g : (α → ZMod 2) → ℝ) (h : (β → ZMod 2) → ℝ)
    (hg : ∀ p, |g p| ≤ 1) (hh : ∀ q, |h q| ≤ 1) :
    (∑ p, ∑ q, M p q * g p * h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2 * 2 ^ B.rank ≤
      M.rank * (∑ p, ∑ q, M p q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β := by
  classical
  set M' := Matrix.diagonal g * M * Matrix.diagonal h
  have hM'_apply (p : α → ZMod 2) (q : β → ZMod 2) : M' p q = M p q * g p * h q := by
    simp only [M', mul_diagonal, diagonal_mul]
    ring
  have hrank : M'.rank ≤ M.rank :=
    (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hnorm : ∑ p, ∑ q, M' p q ^ 2 ≤ ∑ p, ∑ q, M p q ^ 2 := by
    refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
    have hgp := hg p
    have hhq := hh q
    calc M' p q ^ 2 = (|M p q| * |g p| * |h q|) ^ 2 := by
          rw [hM'_apply, ← sq_abs (M p q * g p * h q), abs_mul, abs_mul]
      _ ≤ (|M p q| * 1 * 1) ^ 2 := by gcongr
      _ = M p q ^ 2 := by simp
  simp_rw [← hM'_apply]
  refine (sq_sum_matrix_bilinear_le_of_rank_le B M.rank M' hrank).trans ?_
  have := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (α := ℝ) M.rank)
  gcongr

end Matrix
