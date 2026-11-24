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
  have hfibre : ∑ p, H p ^ 2 ≤ (∑ q, h q ^ 2) * K * (2 : ℝ) ^ Fintype.card α := by
    rw [hexp]
    have hpt : ∀ q q', h q * h q' * (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) ≤
        ((h q ^ 2 + h q' ^ 2) / 2) *
          (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) := by
      intro q q'
      refine mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> positivity)
      nlinarith [sq_nonneg (h q - h q')]
    have hcard_row (q : β → ZMod 2) :
        ∑ q' : β → ZMod 2, (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) =
          K * (2 : ℝ) ^ Fintype.card α := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        card_filter_mulVec_eq B q]
    have hcard_col (q' : β → ZMod 2) :
        ∑ q : β → ZMod 2, (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) =
          K * (2 : ℝ) ^ Fintype.card α := by
      have hsymm : ∀ q, (B *ᵥ q' = B *ᵥ q) ↔ (B *ᵥ q = B *ᵥ q') := fun _ => eq_comm
      simp_rw [hsymm]
      exact hcard_row q'
    calc ∑ q, ∑ q', h q * h q' * (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0)
        ≤ ∑ q, ∑ q', ((h q ^ 2 + h q' ^ 2) / 2) *
            (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun q' _ => hpt q q'
      _ = (1 / 2) * (∑ q, h q ^ 2 * ∑ q',
              if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) +
            (1 / 2) * (∑ q', h q' ^ 2 * ∑ q,
              if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) := by
          have hsplit : ∀ q q', ((h q ^ 2 + h q' ^ 2) / 2) *
              (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) =
              (1 / 2) * (h q ^ 2 * (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0)) +
              (1 / 2) * (h q' ^ 2 *
                (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0)) := by
            intro q q'; ring
          simp_rw [hsplit, Finset.sum_add_distrib]
          have h1 : ∑ q, ∑ q', (1 / 2) * (h q ^ 2 *
              if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) =
              (1 / 2) * ∑ q, h q ^ 2 * ∑ q',
                if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            simp_rw [Finset.mul_sum]
          have h2 : ∑ q, ∑ q', (1 / 2) * (h q' ^ 2 *
              if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) =
              (1 / 2) * ∑ q', h q' ^ 2 * ∑ q,
                if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0 := by
            rw [Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q' _ => ?_
            simp_rw [Finset.mul_sum]
          rw [h1, h2]
      _ = (∑ q, h q ^ 2) * K * (2 : ℝ) ^ Fintype.card α := by
          simp_rw [hcard_row, hcard_col, ← Finset.sum_mul]
          ring
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
    have hr0 : M.rank = 0 := Nat.eq_zero_of_le_zero hr
    have hbot : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hr0
    have hM0 : ∀ p q, M p q = 0 := by
      intro p q
      have hmem : M.mulVecLin (Pi.single q 1) ∈ (⊥ : Submodule ℝ ((α → ZMod 2) → ℝ)) :=
        hbot ▸ LinearMap.mem_range_self M.mulVecLin (Pi.single q 1)
      have hcol : M *ᵥ Pi.single q 1 = 0 := (Submodule.mem_bot ℝ).mp hmem
      simpa [mulVec_single] using congrFun hcol p
    simp [hM0]
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
        refine ⟨x - (c ⬝ᵥ x) • e₀, ?_⟩
        ext p
        simp only [mulVecLin_apply, mulVec, dotProduct, N, of_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
        have hv : ∑ q, v p * c q * x q = (∑ q, c q * x q) * M p q₀ := by
          simp_rw [show ∀ q, v p * c q * x q = (c q * x q) * v p from fun q => by ring,
            ← Finset.sum_mul]
          rfl
        have hsingle : ∑ q, M p q * e₀ q = M p q₀ := by
          rw [Fintype.sum_eq_single q₀ fun q hq => by simp [e₀, hq]]
          simp [e₀]
        rw [hv]
        simp_rw [show ∀ q, M p q * (x q - (∑ i, c i * x i) * e₀ q) =
            M p q * x q - (∑ i, c i * x i) * (M p q * e₀ q) from fun q => by ring,
          Finset.sum_sub_distrib, ← Finset.mul_sum, hsingle]
      have hN_lt : LinearMap.range N.mulVecLin < LinearMap.range M.mulVecLin := by
        refine lt_of_le_of_ne hN_le fun heq => ?_
        have hv_mem : v ∈ LinearMap.range M.mulVecLin := by
          refine ⟨e₀, ?_⟩
          ext p
          simp [e₀, mulVec_single, v]
        rw [← heq] at hv_mem
        obtain ⟨x, hx⟩ := hv_mem
        have hdot : v ⬝ᵥ (N *ᵥ x) = 0 := by
          calc v ⬝ᵥ (N *ᵥ x)
              = ∑ p, v p * ∑ q, N p q * x q := rfl
            _ = ∑ q, x q * ∑ p, v p * N p q := by
                simp_rw [Finset.mul_sum, show ∀ p q, v p * (N p q * x q) = x q * (v p * N p q)
                  from fun _ _ => by ring]
                exact Finset.sum_comm
            _ = 0 := by simp [horth]
        rw [mulVecLin_apply] at hx
        rw [hx] at hdot
        have hvv : v ⬝ᵥ v = s := by
          simp [dotProduct, s, sq]
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
      set W : ℝ := (2 : ℝ) ^ Fintype.card α * 2 ^ Fintype.card β
      have hW : 0 ≤ W := by positivity
      have hpow : (0 : ℝ) < 2 ^ B.rank := by positivity
      have hI₁' : S₁ ^ 2 * 2 ^ B.rank ≤ s * (∑ q, c q ^ 2) * W := by
        dsimp only [W]; linarith
      have hI₂' : S₂ ^ 2 * 2 ^ B.rank ≤ (r : ℝ) * (∑ p, ∑ q, N p q ^ 2) * W := by
        dsimp only [W]; linarith
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · simp only [Nat.cast_zero, zero_mul] at hI₂'
        have hS₂_sq : S₂ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_left hI₂' hpow
        have hS₂ : S₂ = 0 := sq_eq_zero_iff.mp (le_antisymm hS₂_sq (sq_nonneg S₂))
        have hN2 : 0 ≤ ∑ p, ∑ q, N p q ^ 2 :=
          Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg (N p q)
        rw [hS₂, add_zero, Nat.zero_add, Nat.cast_one, one_mul]
        calc S₁ ^ 2 * 2 ^ B.rank
            ≤ s * (∑ q, c q ^ 2) * W := hI₁'
          _ ≤ (s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2) * W :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN2) hW
          _ = _ := by dsimp only [W]; ring
      · have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hrpos
        have hcs : (r : ℝ) * (S₁ + S₂) ^ 2 ≤ ((r : ℝ) + 1) * ((r : ℝ) * S₁ ^ 2 + S₂ ^ 2) := by
          nlinarith [sq_nonneg ((r : ℝ) * S₁ - S₂)]
        have hmul := mul_le_mul_of_nonneg_right hcs hpow.le
        have hcomb : ((r : ℝ) * S₁ ^ 2 + S₂ ^ 2) * 2 ^ B.rank ≤
            (r : ℝ) * (s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2) * W := by
          have h1 : (r : ℝ) * (S₁ ^ 2 * 2 ^ B.rank) ≤ (r : ℝ) * (s * (∑ q, c q ^ 2) * W) :=
            mul_le_mul_of_nonneg_left hI₁' hr'.le
          linarith
        have hstep : (r : ℝ) * ((S₁ + S₂) ^ 2 * 2 ^ B.rank) ≤
            (r : ℝ) * (((r : ℝ) + 1) * (s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2) * W) := by
          calc (r : ℝ) * ((S₁ + S₂) ^ 2 * 2 ^ B.rank)
              = (r : ℝ) * (S₁ + S₂) ^ 2 * 2 ^ B.rank := by ring
            _ ≤ ((r : ℝ) + 1) * ((r : ℝ) * S₁ ^ 2 + S₂ ^ 2) * 2 ^ B.rank := hmul
            _ = ((r : ℝ) + 1) * (((r : ℝ) * S₁ ^ 2 + S₂ ^ 2) * 2 ^ B.rank) := by ring
            _ ≤ ((r : ℝ) + 1) * ((r : ℝ) * (s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2) * W) :=
                mul_le_mul_of_nonneg_left hcomb (by positivity)
            _ = (r : ℝ) * (((r : ℝ) + 1) * (s * (∑ q, c q ^ 2) + ∑ p, ∑ q, N p q ^ 2) * W) := by
                ring
        have hres := le_of_mul_le_mul_left hstep hr'
        push_cast
        dsimp only [W] at hres
        linarith

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
    rw [hM'_apply]
    have hg2 : g p ^ 2 ≤ 1 := by nlinarith [abs_nonneg (g p), sq_abs (g p), hg p]
    have hh2 : h q ^ 2 ≤ 1 := by nlinarith [abs_nonneg (h q), sq_abs (h q), hh q]
    have hgh : g p ^ 2 * h q ^ 2 ≤ 1 := by nlinarith [sq_nonneg (g p), sq_nonneg (h q)]
    calc (M p q * g p * h q) ^ 2 = M p q ^ 2 * (g p ^ 2 * h q ^ 2) := by ring
      _ ≤ M p q ^ 2 * 1 := mul_le_mul_of_nonneg_left hgh (sq_nonneg _)
      _ = M p q ^ 2 := mul_one _
  have hmain := sq_sum_matrix_bilinear_le_of_rank_le B M.rank M' hrank
  simp_rw [← hM'_apply]
  refine hmain.trans ?_
  have hpow : (0 : ℝ) ≤ 2 ^ Fintype.card α * 2 ^ Fintype.card β := by positivity
  have hr0 : (0 : ℝ) ≤ M.rank := Nat.cast_nonneg _
  calc (M.rank : ℝ) * (∑ p, ∑ q, M' p q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β
      = (M.rank : ℝ) * (∑ p, ∑ q, M' p q ^ 2) * (2 ^ Fintype.card α * 2 ^ Fintype.card β) := by
        ring
    _ ≤ (M.rank : ℝ) * (∑ p, ∑ q, M p q ^ 2) * (2 ^ Fintype.card α * 2 ^ Fintype.card β) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hr0) hpow
    _ = (M.rank : ℝ) * (∑ p, ∑ q, M p q ^ 2) * 2 ^ Fintype.card α * 2 ^ Fintype.card β := by
        ring

end Matrix
