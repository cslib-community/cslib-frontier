/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Averages in a state

Rigidity arguments average over questions, group elements and outcomes. Mathlib's uniform average
`𝔼 i ∈ s, f i` (`Finset.expect`) handles these averages, and the state norm `‖·‖_φ` behaves under
it like a norm:

* the triangle inequality, `‖∑ a_i‖_φ ≤ ∑ ‖a_i‖_φ` and `‖𝔼 a_i‖_φ ≤ 𝔼 ‖a_i‖_φ`
  (`Cslib.Quantum.AlgState.norm_sum_le`, `Cslib.Quantum.AlgState.norm_expect_le`);
* **Jensen**, `‖𝔼 a_i‖²_φ ≤ 𝔼 ‖a_i‖²_φ` (`Cslib.Quantum.AlgState.norm_expect_sq_le`);
* **Jensen with contractions**, `‖𝔼 u_i d_i‖²_φ ≤ 𝔼 ‖d_i‖²_φ` when every `u_i` is a contraction
  (`Cslib.Quantum.AlgState.norm_expect_mul_sq_le`). This is the core step of twirling and of the
  compression of regular representations.

## Main results

* `Cslib.Quantum.AlgState.norm_expect_sq_le`: Jensen for the state norm.
* `Cslib.Quantum.AlgState.norm_expect_mul_sq_le`: Jensen with contractions.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Quantum.AlgState

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A] (φ : AlgState A) {ι : Type*} (s : Finset ι)

/-- The triangle inequality over finite sums. -/
theorem norm_sum_le (a : ι → A) : φ.norm (∑ i ∈ s, a i) ≤ ∑ i ∈ s, φ.norm (a i) := by
  simpa [norm, map_sum] using _root_.norm_sum_le s fun i => φ.toPreGNS (a i)

/-- Squared state-norm distance through an intermediate operator. -/
theorem norm_sub_sq_le_through (a b c : A) :
    φ.norm (a - c) ^ 2 ≤ 2 * φ.norm (a - b) ^ 2 + 2 * φ.norm (b - c) ^ 2 := by
  have h := φ.norm_add_le (a - b) (b - c)
  rw [sub_add_sub_cancel] at h
  calc
    _ ≤ (φ.norm (a - b) + φ.norm (b - c)) ^ 2 :=
      pow_le_pow_left₀ (φ.norm_nonneg _) h 2
    _ ≤ _ := by nlinarith [sq_nonneg (φ.norm (a - b) - φ.norm (b - c))]

variable [Module ℚ≥0 A]

theorem norm_nnqsmul (q : ℚ≥0) (a : A) : φ.norm (q • a) = q * φ.norm a := by
  rw [← NNRat.cast_smul_eq_nnqsmul ℂ, norm_smul]
  simp

/-- The triangle inequality for averages. -/
theorem norm_expect_le (a : ι → A) : φ.norm (𝔼 i ∈ s, a i) ≤ 𝔼 i ∈ s, φ.norm (a i) :=
  le_expect_of_subadditive φ.norm_zero φ.norm_add_le fun n a => by
    rw [norm_nnqsmul, NNRat.smul_def]

/-- **Jensen** for the state norm: `‖𝔼_i a_i‖²_φ ≤ 𝔼_i ‖a_i‖²_φ`. -/
theorem norm_expect_sq_le (a : ι → A) :
    φ.norm (𝔼 i ∈ s, a i) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (a i) ^ 2 :=
  (pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_expect_le s a) 2).trans
    (s.sq_expect_le_expect_sq _)

/-- Squared distance to a fixed operator is convex under a nonempty finite average. -/
theorem norm_sub_expect_sq_le (hs : s.Nonempty) (a : A) (b : ι → A) :
    φ.norm (a - (𝔼 i ∈ s, b i)) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (a - b i) ^ 2 := by
  have h : (𝔼 i ∈ s, (a - b i)) = a - (𝔼 i ∈ s, b i) := by
    rw [expect_sub_distrib, Finset.expect_const hs]
  rw [← h]
  exact φ.norm_expect_sq_le s _

/-- Squared distance from a finite average to a fixed operator. -/
theorem norm_expect_sub_sq_le (hs : s.Nonempty) (a : ι → A) (b : A) :
    φ.norm ((𝔼 i ∈ s, a i) - b) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (a i - b) ^ 2 := by
  have h : (𝔼 i ∈ s, (a i - b)) = (𝔼 i ∈ s, a i) - b := by
    rw [expect_sub_distrib, Finset.expect_const hs]
  rw [← h]
  exact φ.norm_expect_sq_le s _

/-- If either family is first sampled on a subset of at least half the indices and compared
with the other on all indices, the two resulting distances control the distance of the full
averages. The common restricted averages supply the intermediate operators. -/
theorem norm_expect_sub_expect_sq_le_of_half [Fintype ι] [Nonempty ι]
    (hs : s.Nonempty) (hd : (1 / 2 : ℝ) ≤ s.dens) (a b : ι → A) :
    φ.norm ((𝔼 i, a i) - (𝔼 i, b i)) ^ 2 ≤
      12 * (𝔼 i ∈ s, 𝔼 j, φ.norm (a i - b j) ^ 2) +
      2 * (𝔼 j ∈ s, 𝔼 i, φ.norm (a i - b j) ^ 2) := by
  classical
  let aAll := 𝔼 i, a i
  let bAll := 𝔼 i, b i
  let aRestricted := 𝔼 i ∈ s, a i
  let bRestricted := 𝔼 j ∈ s, b j
  let dist (i j : ι) := φ.norm (a i - b j) ^ 2
  let forward := 𝔼 i ∈ s, 𝔼 j, dist i j
  let reverse := 𝔼 j ∈ s, 𝔼 i, dist i j
  have hforward : φ.norm (aRestricted - bAll) ^ 2 ≤ forward :=
    (φ.norm_expect_sub_sq_le s hs a bAll).trans <|
      expect_le_expect fun i _ => φ.norm_sub_expect_sq_le univ univ_nonempty (a i) b
  have hreverse : φ.norm (aAll - bRestricted) ^ 2 ≤ reverse :=
    (φ.norm_sub_expect_sq_le s hs aAll b).trans <|
      expect_le_expect fun j _ => φ.norm_expect_sub_sq_le univ univ_nonempty a (b j)
  have hrestricted (i : ι) : (𝔼 j ∈ s, dist i j) ≤ 2 * 𝔼 j, dist i j := by
    have hpos : 0 ≤ (𝔼 j ∈ s, dist i j) := expect_nonneg fun _ _ => sq_nonneg _
    have hmask : (s.dens : ℝ) * (𝔼 j ∈ s, dist i j) ≤ 𝔼 j, dist i j := by
      rw [← NNRat.smul_def, ← Fintype.expect_ite_mem]
      refine expect_le_expect fun j _ => ?_
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    linarith [mul_le_mul_of_nonneg_right hd hpos]
  have hmiddle : φ.norm (aRestricted - bRestricted) ^ 2 ≤ 2 * forward := by
    calc
      _ ≤ 𝔼 i ∈ s, φ.norm (a i - bRestricted) ^ 2 := φ.norm_expect_sub_sq_le s hs a bRestricted
      _ ≤ 𝔼 i ∈ s, 𝔼 j ∈ s, dist i j :=
        expect_le_expect fun i _ => φ.norm_sub_expect_sq_le s hs (a i) b
      _ ≤ 2 * forward := by
        rw [Finset.mul_expect]
        exact expect_le_expect fun i _ => hrestricted i
  have hmiddle' : φ.norm (bRestricted - aRestricted) ^ 2 ≤ 2 * forward := by
    rw [← neg_sub aRestricted bRestricted, φ.norm_neg]
    exact hmiddle
  change φ.norm (aAll - bAll) ^ 2 ≤ 12 * forward + 2 * reverse
  linarith [φ.norm_sub_sq_le_through aAll bRestricted bAll,
    φ.norm_sub_sq_le_through bRestricted aRestricted bAll]

/-- **Jensen with contractions**: `‖𝔼_i u_i d_i‖²_φ ≤ 𝔼_i ‖d_i‖²_φ` when every `u_i` is a
contraction. -/
theorem norm_expect_mul_sq_le {u d : ι → A} (hu : ∀ i ∈ s, star (u i) * u i ≤ 1) :
    φ.norm (𝔼 i ∈ s, u i * d i) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (d i) ^ 2 :=
  (φ.norm_expect_sq_le s _).trans <| expect_le_expect fun i hi =>
    pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_mul_le_of_star_mul_self_le_one (hu i hi) _) 2

end Cslib.Quantum.AlgState
