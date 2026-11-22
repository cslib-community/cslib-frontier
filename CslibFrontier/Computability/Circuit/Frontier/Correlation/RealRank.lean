/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas
public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.CostLambda
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real-rank Lindsey lemma and correlation with quadratic forms

`CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle` bounds the correlation of a
Boolean target `T ⊆ Bool^ι` with a quadratic form `S = {x | BitString.quadForm Q x}` across a
coordinate cut `X ⊆ ι` by partitioning `T` and `Tᶜ` into monochromatic combinatorial rectangles:
`correlation S T ² · 2^{ρ(X)} ≤ #classes`. Covering `T` and `Tᶜ` by rectangles bounds the
*nonnegative* rank of their `{0, 1}` communication matrices across `X`.

This module strengthens that bound from nonnegative rank / rectangle covers to **ordinary matrix
rank over `ℝ`**:

* **`ℓ²` and real-rank Lindsey lemmas** (`Matrix.sq_sum_bilinear_mul_two_pow_rank_le_l2`,
  `Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le`). For any real matrix `M` and bilinear form
  `B` over `𝔽₂`, orthogonal projection onto columns reduces `M` to `rank M` orthogonal rank-one
  pieces whose squared `ℓ²` norms sum to `∑_{p, q} M_{p, q}²`, yielding
  `(∑_{p, q} M_{p, q} g(p) h(q) (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ rank M · ‖M‖_F² · 2^{|α| + |β|}`.
* **Real-rank correlation bound** (`sq_correlation_quadForm_mul_le_rank_signMatrix`,
  `sq_correlation_quadForm_mul_le_rank_charMatrix_add_one`). Specializing `M` to the `{1, -1}`
  sign communication matrix `signMatrix T X` across `X` (where `‖S_T‖_F² = 2^n`) gives
  `correlation S T ² · 2^{ρ(X)} ≤ (signMatrix T X).rank ≤ (charMatrix T X).rank + 1`.
* **`AND → XOR` separation** (`rank_signMatrix_andXorSet`, `rank_charMatrix_andXorSet`,
  `nonnegRank_charMatrix_andXorSet`). On the `4`-bit `AND → XOR` relation across `{0, 1} | {2, 3}`,
  the `{1, -1}` sign matrix has real rank `2`, the `{0, 1}` characteristic matrix has real rank `3`,
  and the `{0, 1}` nonnegative rank is `4` (while partitioning both `T` and `Tᶜ` into monochromatic
  rectangles requires `4 + 4 = 8` classes).
* **Unconditional `2.8006 n` `U₂` quadratic-form correlation bounds**
  (`eventually_abs_correlation_quadForm_le_u2_gaussian`,
  `eventually_abs_correlation_hardForm_le_u2`,
  `exists_eventually_abs_correlation_hardForm_le_of_lt_u2`,
  `exists_eventually_abs_correlation_hardForm_le_u2_28006`). Combining `u2CubicPairBound_gaussian`
  with the `3`-state `U₂` branching program bounds correlation with any high-cut-rank quadratic
  form — and in particular with `hardForm n` (whose submatrix-robust block is **chosen
  nonconstructively by `Classical.choose`**) — by `2^{-Ω(n)}` for every `U₂` circuit up to
  `2.8006 n` inner gates (`c* ≥ 28007 / 10000 > 28006 / 10000`).

## Main definitions

* `Cslib.Circuits.Frontier.charMatrix`, `Cslib.Circuits.Frontier.signMatrix`: `{0, 1}` and
  `{1, -1}` communication matrices of `T ⊆ (ι → Bool)` across a cut `X : Set ι`.
* `Cslib.Circuits.Frontier.andXorSet`, `Cslib.Circuits.Frontier.andXorCut`: `4`-bit `AND → XOR`
  witness separating `signMatrix` rank (`2`), `charMatrix` rank (`3`), and `nonnegRank` (`4`).

## Main results

* `Matrix.sq_sum_bilinear_mul_two_pow_rank_le_l2`: `ℓ²`-weighted Lindsey's lemma over `𝔽₂`.
* `Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le`: real-rank Lindsey's lemma over `𝔽₂`.
* `Cslib.Circuits.Frontier.rank_signMatrix_le_rank_charMatrix_add_one`:
  `(signMatrix T X).rank ≤ (charMatrix T X).rank + 1`.
* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_rank_signMatrix`,
  `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_rank_charMatrix_add_one`: quadratic-form
  correlation bounded by real rank across any cut `X`.
* `Cslib.Circuits.Frontier.rank_signMatrix_andXorSet`,
  `Cslib.Circuits.Frontier.rank_charMatrix_andXorSet`,
  `Cslib.Circuits.Frontier.nonnegRank_charMatrix_andXorSet`: `2 < 3 < 4` rank separation.
* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_u2_gaussian`,
  `Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le_u2`,
  `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt_u2`,
  `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_u2_28006`: unconditional
  `U₂` quadratic-form correlation bounds up to `2.8006 n` inner gates.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [FioriniMassarPokuttaTiwaryDeWolf2015]
-/

public section

namespace Matrix

open Finset

variable {α β : Type*}

/-- Subadditivity of matrix rank over a field: `rank (A + B) ≤ rank A + rank B`. -/
theorem rank_add_le_rank_add {R m n : Type*} [Field R] [Finite m] [Fintype n]
    (A B : Matrix m n R) : (A + B).rank ≤ A.rank + B.rank := by
  classical
  have := Fintype.ofFinite m
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  have hsub : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.mpr ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono := Submodule.finrank_mono hsub
  omega

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

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset

section CutMatrices

variable {ι : Type*}

/-- Split an input `x : ι → Bool` into its restriction to `X` and its restriction to `Xᶜ`. -/
def cutEquiv (X : Set ι) [DecidablePred (· ∈ X)] :
    (ι → Bool) ≃ (X → Bool) × (↥Xᶜ → Bool) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun pq i := if h : i ∈ X then pq.1 ⟨i, h⟩ else pq.2 ⟨i, h⟩
  left_inv x := funext fun i => by by_cases h : i ∈ X <;> simp [h]
  right_inv := fun ⟨p, q⟩ => Prod.ext (funext fun ⟨i, h⟩ => dite_eq_left h)
    (funext fun ⟨i, h⟩ => dite_eq_right h)

/-- Boolean communication matrix of `T ⊆ (ι → Bool)` across the coordinate cut `X : Set ι`. -/
private noncomputable def boolCutMatrix (T : Set (ι → Bool)) (X : Set ι) :
    Matrix (X → Bool) (↥Xᶜ → Bool) Bool :=
  letI := Classical.propDecidable
  Matrix.of fun p q => decide ((cutEquiv X).symm (p, q) ∈ T)

/-- The `{0, 1}` real communication matrix of `T` across `X`. -/
noncomputable def charMatrix (T : Set (ι → Bool)) (X : Set ι) :
    Matrix (X → Bool) (↥Xᶜ → Bool) ℝ :=
  Basis.boolIndicator ℝ (boolCutMatrix T X)

/-- The `{1, -1}` real sign communication matrix of `T` across `X`. -/
noncomputable def signMatrix (T : Set (ι → Bool)) (X : Set ι) :
    Matrix (X → Bool) (↥Xᶜ → Bool) ℝ :=
  Basis.signIndicator ℝ (boolCutMatrix T X)

theorem charMatrix_apply (T : Set (ι → Bool)) (X : Set ι) (p : X → Bool) (q : ↥Xᶜ → Bool) :
    charMatrix T X p q =
      letI := Classical.propDecidable
      if (cutEquiv X).symm (p, q) ∈ T then 1 else 0 := by
  classical
  simp only [charMatrix, Basis.boolIndicator_apply, boolCutMatrix, of_apply]
  by_cases h : (cutEquiv X).symm (p, q) ∈ T <;> simp [h]

theorem signMatrix_apply (T : Set (ι → Bool)) (X : Set ι) (p : X → Bool) (q : ↥Xᶜ → Bool) :
    signMatrix T X p q =
      letI := Classical.propDecidable
      if (cutEquiv X).symm (p, q) ∈ T then 1 else -1 := by
  classical
  simp only [signMatrix, Basis.signIndicator_apply, boolCutMatrix, of_apply]
  by_cases h : (cutEquiv X).symm (p, q) ∈ T <;> simp [h]

/-- Shifting from `{0, 1}` to `{1, -1}` adds at most `1` to the real matrix rank:
`signIndicator = 2 • boolIndicator - J`. -/
theorem rank_signIndicator_le_add_one {m n : Type*} [Finite m] [Fintype n]
    (M : Matrix m n Bool) :
    (Basis.signIndicator ℝ M).rank ≤ (Basis.boolIndicator ℝ M).rank + 1 := by
  have heq : Basis.signIndicator ℝ M =
      (2 : ℝ) • Basis.boolIndicator ℝ M + Matrix.vecMulVec (fun _ => -1) (fun _ => 1) := by
    ext i j
    simp only [Basis.signIndicator_apply, Matrix.add_apply, Matrix.smul_apply,
      Basis.boolIndicator_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    cases M i j <;> norm_num
  rw [heq]
  have hadd := Matrix.rank_add_le_rank_add
    ((2 : ℝ) • Basis.boolIndicator ℝ M) (Matrix.vecMulVec (fun _ => (-1 : ℝ)) (fun _ => 1))
  have hsmul : ((2 : ℝ) • Basis.boolIndicator ℝ M).rank = (Basis.boolIndicator ℝ M).rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  have hvec := Matrix.rank_vecMulVec_le (fun _ : m => (-1 : ℝ)) (fun _ : n => (1 : ℝ))
  omega

variable [Fintype ι] [DecidableEq ι]

open Classical in
/-- For every `T` and cut `X`, `(signMatrix T X).rank ≤ (charMatrix T X).rank + 1`. -/
theorem rank_signMatrix_le_rank_charMatrix_add_one (T : Set (ι → Bool)) (X : Set ι) :
    (signMatrix T X).rank ≤ (charMatrix T X).rank + 1 :=
  rank_signIndicator_le_add_one (boolCutMatrix T X)

/-- Equivalence between `Bool` and `ZMod 2` via `BitString.bitVal`. -/
private def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun := BitString.bitVal (ZMod 2)
  invFun z := z == 1
  left_inv b := by cases b <;> decide
  right_inv z := by revert z; decide

open Classical in
/-- **Correlation through real sign-matrix rank.** For any quadratic form `Q` over `𝔽₂`, target set
`T ⊆ (ι → Bool)`, and coordinate cut `X ⊆ ι`,
`correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤ (signMatrix T X).rank`.
-/
theorem sq_correlation_quadForm_mul_le_rank_signMatrix
    (Q : Matrix ι ι (ZMod 2)) (T : Set (ι → Bool)) (X : Set ι) :
    correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (signMatrix T X).rank := by
  set S := {x : ι → Bool | BitString.quadForm Q x}
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ)
  have hNn : N = 2 ^ Fintype.card ι := by simp [N, Fintype.card_bool]
  have hn : Fintype.card X + Fintype.card ↥Xᶜ = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact ncard_add_ncard_compl X
  let e := cutEquiv X
  let eX : (X → Bool) ≃ (X → ZMod 2) := Equiv.piCongrRight fun _ => boolEquivZMod2
  let eY : (↥Xᶜ → Bool) ≃ (↥Xᶜ → ZMod 2) := Equiv.piCongrRight fun _ => boolEquivZMod2
  let C := (Q + Qᵀ).submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι)
  let g : (X → ZMod 2) → ℝ := fun u =>
    (-1) ^ (u ⬝ᵥ Q.submatrix ((↑) : X → ι) ((↑) : X → ι) *ᵥ u).val
  let h : (↥Xᶜ → ZMod 2) → ℝ := fun w =>
    (-1) ^ (w ⬝ᵥ Q.submatrix ((↑) : ↥Xᶜ → ι) ((↑) : ↥Xᶜ → ι) *ᵥ w).val
  set Mz : Matrix (X → ZMod 2) (↥Xᶜ → ZMod 2) ℝ := (signMatrix T X).submatrix eX.symm eY.symm
  have hsum : correlation S T * N =
      -∑ u : X → ZMod 2, ∑ w : ↥Xᶜ → ZMod 2, Mz u w * g u * h w * (-1 : ℝ) ^ (u ⬝ᵥ C *ᵥ w).val := by
    rw [correlation_mul_card_eq_sum, ← Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (e.trans (Equiv.prodCongr eX eY)) _ _ fun x => ?_
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
    have hq := dotProduct_mulVec_self_eq_add Q X fun i => BitString.bitVal (ZMod 2) (x i)
    have hS : (if x ∈ S then (1 : ℝ) else -1) =
        -(-1 : ℝ) ^ ((fun i => BitString.bitVal (ZMod 2) (x i)) ⬝ᵥ
          Q *ᵥ fun i => BitString.bitVal (ZMod 2) (x i)).val := by
      rw [BitString.neg_one_pow_val_eq]
      simp only [S, mem_ofPred_eq]
      split_ifs <;> simp
    have hT : Mz (eX (e x).1) (eY (e x).2) = if x ∈ T then 1 else -1 := by
      simp only [Mz, submatrix_apply, Equiv.symm_apply_apply, signMatrix_apply]
      have hex : e.symm (e x) = x := e.symm_apply_apply x
      rw [Prod.mk.eta, hex]
    have hw : (if (x ∈ S ↔ x ∈ T) then (1 : ℝ) else -1) =
        (if x ∈ T then 1 else -1) * (if x ∈ S then 1 else -1) := by
      by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS, hxT]
    rw [hw, ← hT, hS, hq, ZMod.neg_one_pow_val_add, ZMod.neg_one_pow_val_add]
    have hg_eq : X.domRestrict (fun i => BitString.bitVal (ZMod 2) (x i)) = eX (e x).1 := rfl
    have hh_eq : Xᶜ.domRestrict (fun i => BitString.bitVal (ZMod 2) (x i)) = eY (e x).2 := rfl
    rw [hg_eq, hh_eq]
    dsimp only [g, h, C]
    ring
  have hL := Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le C Mz g h
    (fun _ => by simp [g]) (fun _ => by simp [h])
  have hCR : (2 : ℝ) ^ C.rank = 2 ^ (Q + Qᵀ).cutRank X := by
    rw [((Q + Qᵀ).cutRank_eq_rank X).symm]
  have hMrankR : (Mz.rank : ℝ) = (signMatrix T X).rank :=
    congrArg Nat.cast (Matrix.rank_submatrix _ eX.symm eY.symm)
  set Fsq : ℝ := ∑ u, ∑ w, Mz u w ^ 2
  have hMsq : Fsq = N := by
    have h1 : ∀ u w, Mz u w ^ 2 = 1 := by
      intro u w
      simp only [Mz, submatrix_apply, signMatrix_apply]
      split_ifs <;> norm_num
    dsimp only [Fsq]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_pi, Fintype.card_pi]
    simp only [Fintype.card_congr boolEquivZMod2.symm, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ]
    push_cast
    rw [← pow_add, hn, hNn]
  have hprod : (2 : ℝ) ^ Fintype.card X * 2 ^ Fintype.card ↥Xᶜ = N := by
    rw [hNn, ← pow_add, hn]
  have hNN : 0 < N * N := by rw [hNn]; positivity
  have hbound : correlation S T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X * (N * N) ≤
      (signMatrix T X).rank * (N * N) := by
    calc correlation S T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X * (N * N)
        = (correlation S T * N) ^ 2 * 2 ^ (Q + Qᵀ).cutRank X := by ring
      _ ≤ (Mz.rank : ℝ) * Fsq * 2 ^ Fintype.card X * 2 ^ Fintype.card ↥Xᶜ := by
          rw [hsum, neg_sq, ← hCR]
          exact hL
      _ = (signMatrix T X).rank * (N * N) := by
          rw [hMrankR, hMsq, mul_assoc ((signMatrix T X).rank * N), hprod]
          ring
  exact le_of_mul_le_mul_right hbound hNN

open Classical in
/-- **Correlation through `{0, 1}` real matrix rank.** Across any coordinate cut `X ⊆ ι`,
`correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
  (charMatrix T X).rank + 1`. -/
theorem sq_correlation_quadForm_mul_le_rank_charMatrix_add_one
    (Q : Matrix ι ι (ZMod 2)) (T : Set (ι → Bool)) (X : Set ι) :
    correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (charMatrix T X).rank + 1 :=
  (sq_correlation_quadForm_mul_le_rank_signMatrix Q T X).trans
    (by exact_mod_cast rank_signMatrix_le_rank_charMatrix_add_one T X)

end CutMatrices

/-! ### Explicit `2 < 3 < 4` separation on the `AND → XOR` relation -/

/-- The `4`-bit `AND → XOR` input set `{x : Fin 4 → Bool | (x 2 && x 0) == (x 3 ^^ x 1)}`, matching
`Basis.andXorMatrix` across the cut `andXorCut = {0, 1}` (`(x 0, x 1) = (b, d)` on `X` and
`(x 2, x 3) = (a, c)` on `Xᶜ`). -/
@[expose]
def andXorSet : Set (Fin 4 → Bool) :=
  {x | Basis.andXorMatrix (x 0, x 1) (x 2, x 3) = true}

/-- The left half `{0, 1} ⊆ Fin 4` of the `AND → XOR` cut. -/
@[expose]
def andXorCut : Set (Fin 4) :=
  {i | i.val < 2}

private def andXorLeftEquiv : (andXorCut → Bool) ≃ Bool × Bool where
  toFun p := (p ⟨0, by simp [andXorCut]⟩, p ⟨1, by simp [andXorCut]⟩)
  invFun bd i := if i.1.val = 0 then bd.1 else bd.2
  left_inv p := by
    ext ⟨i, hi⟩
    fin_cases i
    · rfl
    · rfl
    · simp [andXorCut] at hi
    · simp [andXorCut] at hi
  right_inv := fun ⟨_, _⟩ => rfl

private def andXorRightEquiv : (↥andXorCutᶜ → Bool) ≃ Bool × Bool where
  toFun q := (q ⟨2, by simp [andXorCut]⟩, q ⟨3, by simp [andXorCut]⟩)
  invFun ac i := if i.1.val = 2 then ac.1 else ac.2
  left_inv q := by
    ext ⟨i, hi⟩
    fin_cases i
    · simp [andXorCut] at hi
    · simp [andXorCut] at hi
    · rfl
    · rfl
  right_inv := fun ⟨_, _⟩ => rfl

private theorem boolCutMatrix_andXorSet :
    boolCutMatrix andXorSet andXorCut =
      Basis.andXorMatrix.submatrix andXorLeftEquiv andXorRightEquiv := by
  classical
  ext p q
  rw [Bool.eq_iff_iff]
  simp only [boolCutMatrix, of_apply, submatrix_apply]
  rw [decide_eq_true_eq]
  simp only [andXorSet, mem_ofPred_eq]
  have h0 : (cutEquiv andXorCut).symm (p, q) 0 = p ⟨0, by simp [andXorCut]⟩ :=
    dite_eq_left (by simp [andXorCut])
  have h1 : (cutEquiv andXorCut).symm (p, q) 1 = p ⟨1, by simp [andXorCut]⟩ :=
    dite_eq_left (by simp [andXorCut])
  have h2 : (cutEquiv andXorCut).symm (p, q) 2 = q ⟨2, by simp [andXorCut]⟩ :=
    dite_eq_right (by simp [andXorCut])
  have h3 : (cutEquiv andXorCut).symm (p, q) 3 = q ⟨3, by simp [andXorCut]⟩ :=
    dite_eq_right (by simp [andXorCut])
  rw [h0, h1, h2, h3]
  rfl

open Classical in
/-- Across `andXorCut`, the `{1, -1}` sign matrix of `andXorSet` has real rank `2`. -/
theorem rank_signMatrix_andXorSet : (signMatrix andXorSet andXorCut).rank = 2 := by
  have heq : signMatrix andXorSet andXorCut =
      (Basis.signIndicator ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv andXorRightEquiv := by
    ext p q
    simp only [signMatrix, Basis.signIndicator_apply, submatrix_apply, boolCutMatrix_andXorSet]
    by_cases h : Basis.andXorMatrix (andXorLeftEquiv p) (andXorRightEquiv q) = true <;> simp [h]
  rw [heq, Matrix.rank_submatrix, Basis.rank_signIndicator_andXorMatrix_real]

open Classical in
/-- Across `andXorCut`, the `{0, 1}` characteristic matrix of `andXorSet` has real rank `3`. -/
theorem rank_charMatrix_andXorSet : (charMatrix andXorSet andXorCut).rank = 3 := by
  have heq : charMatrix andXorSet andXorCut =
      (Basis.boolIndicator ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv andXorRightEquiv := by
    ext p q
    simp only [charMatrix, Basis.boolIndicator_apply, submatrix_apply, boolCutMatrix_andXorSet]
    by_cases h : Basis.andXorMatrix (andXorLeftEquiv p) (andXorRightEquiv q) = true <;> simp [h]
  rw [heq, Matrix.rank_submatrix, Basis.rank_andXorMatrix_real]

/-- Across `andXorCut`, the `{0, 1}` characteristic matrix of `andXorSet` has nonnegative rank `4`
(strictly exceeding both `(signMatrix andXorSet andXorCut).rank = 2` and
`(charMatrix andXorSet andXorCut).rank = 3`). -/
theorem nonnegRank_charMatrix_andXorSet : (charMatrix andXorSet andXorCut).nonnegRank = 4 := by
  have heq : charMatrix andXorSet andXorCut =
      (Basis.boolIndicator ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv andXorRightEquiv := by
    ext p q
    simp only [charMatrix, Basis.boolIndicator_apply, submatrix_apply, boolCutMatrix_andXorSet]
    by_cases h : Basis.andXorMatrix (andXorLeftEquiv p) (andXorRightEquiv q) = true <;> simp [h]
  have hle1 := Matrix.nonnegRank_submatrix_le (Basis.boolIndicator ℝ Basis.andXorMatrix)
    andXorLeftEquiv andXorRightEquiv
  have hinv : Basis.boolIndicator ℝ Basis.andXorMatrix =
      (charMatrix andXorSet andXorCut).submatrix andXorLeftEquiv.symm andXorRightEquiv.symm := by
    rw [heq, submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, submatrix_id_id]
  have hle2 := Matrix.nonnegRank_submatrix_le (charMatrix andXorSet andXorCut)
    andXorLeftEquiv.symm andXorRightEquiv.symm
  rw [← heq] at hle1
  rw [← hinv] at hle2
  exact le_antisymm (hle1.trans_eq Basis.nonnegRank_andXorMatrix_real)
    (Basis.nonnegRank_andXorMatrix_real ▸ hle2)

/-! ### Unconditional `2.8006 n` `U₂` quadratic-form correlation bounds -/

section U2Correlation

open Filter Asymptotics

universe v

/-- **Unconditional `U₂` quadratic-form correlation bound.** With `p = gaussianCoefficient` and
`B_pair = 271212 / 1000000`, set `δ := 2 p - B_pair`, `A := (7/8) B_pair + (1/8)(2p)`,
`L_{U₂} := 1 + (1 - δ) / A`, and `c*_{U₂} := 1 + (1/2 - δ) / A` (`≥ 2.8007`). For every
`c ≥ 1 / 2`, every `γ < (c*_{U₂} - c) / (2 L_{U₂})`, and every family `Q_n` whose polar matrix has
bisection cut rank `⌊n/2⌋ - o(n)`, eventually every `U₂` circuit with at most `c n` inner gates has
correlation at most `2^{-γ n}` with `BitString.quadForm (Q n)`. -/
theorem eventually_abs_correlation_quadForm_le_u2_gaussian {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_u2 Gaussian.gaussianCoefficient_pos (by norm_num)
    Gaussian.le_two_mul_gaussianCoefficient Gaussian.u2CubicPairBound_gaussian
    (by linarith [Gaussian.two_mul_gaussianCoefficient_le])
    (by linarith [Gaussian.two_mul_gaussianCoefficient_le]) hc hγ Q e he hQ

/-- **Exponentially small `U₂` correlation with `hardForm n`** (whose submatrix-robust block is
chosen nonconstructively by `Classical.choose`). -/
theorem eventually_abs_correlation_hardForm_le_u2 {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))))) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_u2_gaussian hc hγ hardMatrix _ isLittleO_hardDeficiency
    (Eventually.of_forall half_le_cutRank_hardMatrix_add)

/-- **Every gate-count coefficient strictly below `c*_{U₂}` (`≥ 2.8007`).** Note that `hardForm` is
chosen nonconstructively via `Classical.choose`. -/
theorem exists_eventually_abs_correlation_hardForm_le_of_lt_u2 {c : ℝ}
    (hc : c <
      1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  set c' := max c (1 / 2)
  set c_star := 1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
    ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))
  set L_u2 := 1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
    ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))
  have hL : 0 < L_u2 := by
    have := Gaussian.u2CircuitCoefficient_ge_46362
    dsimp only [L_u2]; linarith
  have hc' : c' < c_star := max_lt hc (by
    have := Gaussian.u2CorrelationThreshold_ge_28007
    dsimp only [c_star]; linarith)
  set r := (c_star - c') / (2 * L_u2)
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [eventually_abs_correlation_hardForm_le_u2.{v} (le_max_right c (1 / 2))
    (γ := r / 2) (half_lt_self hr)] with n hn σ I Acc C hU2 hsize
  exact hn σ I Acc C hU2
    (hsize.trans (mul_le_mul_of_nonneg_right (le_max_left c _) (Nat.cast_nonneg n)))

/-- **Unconditional `2.8006 n` `U₂` quadratic-form correlation bound (`28006 / 10000`).** Some fixed
`γ > 0` bounds, for all large `n`, the correlation of every `U₂` circuit with at most `2.8006 n`
inner gates with `hardForm n` (chosen nonconstructively by `Classical.choose`) by `2^{-γ n}`. -/
theorem exists_eventually_abs_correlation_hardForm_le_u2_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), I.IsU2 →
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt_u2
    (by linarith [Gaussian.u2CorrelationThreshold_ge_28007])

/-- **Unconditional `2.8006 n` De Morgan correlation bound** with `hardForm n` (nonconstructive via
`Classical.choose`). -/
theorem exists_eventually_abs_correlation_hardForm_le_deMorgan_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (Acc : Set Bool)
      (C : Circuit Boolean.DeMorgan.signature n 1),
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x}
            {x | C.eval Boolean.DeMorgan.interpretation x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventually_abs_correlation_hardForm_le_u2_28006.{0}
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc C hsize
  exact hn Boolean.DeMorgan.signature Boolean.DeMorgan.interpretation Acc C
    Boolean.DeMorgan.isU2 hsize

/-- **Unconditional `2.8006 n` Boolean correlation bound** with `hardForm n` (nonconstructive via
`Classical.choose`). -/
theorem exists_eventually_abs_correlation_hardForm_le_boolean_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (Acc : Set Bool)
      (C : Circuit Boolean.signature n 1),
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x}
            {x | C.eval Boolean.interpretation x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventually_abs_correlation_hardForm_le_u2_28006.{0}
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc C hsize
  exact hn Boolean.signature Boolean.interpretation Acc C Boolean.isU2 hsize

end U2Correlation

end Cslib.Circuits.Frontier
