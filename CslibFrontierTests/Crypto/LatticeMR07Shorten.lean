/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.Lattice.MR07Shorten

/-!
Non-vacuous client tests for `CslibFrontier.Crypto.Computational.Lattice.MR07Shorten`:
* Dimension-0 and concrete positive-dimension `shortenRoundBound` evaluation.
* Dimension-1 (`0 × 1` `omitRowTable` edge case), skewed 2-D, and skewed 3-D rational bases with
  `maxSqNormIndex` and `ratOrthoTarget_spec`.
* Concrete 2-D one-round shortening preserving linear independence, `‖S'‖ ≤ ‖S‖`, and contracting
  `sqNormProd` by `(13 / 16) ^ 2`.
* End-to-end 2-D `shortenLoop_isSolution_givp` and `shortenGuardedIter_isSolution_givp` on `ℤ²`
  using `Cslib.Algorithms.LatticeReduction.exists_int_inner_of_mem_span`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.LatticeMR07Shorten

open Cslib.Algorithms.LatticeReduction Cslib.Crypto Cslib.Crypto.MR07Shorten Module
open scoped RealInnerProductSpace

/-- Concrete `shortenRoundBound` evaluation in dimension 0. -/
example : shortenRoundBound 0 101 = 0 := rfl

/-- Concrete `shortenRoundBound` evaluation in dimension 2 with `B = 101`. -/
example : shortenRoundBound 2 101 = 28 := by decide

/-- Dim 1 (`0 × 1` `omitRowTable` edge case): `S1 = ![![5]]` in `ℚ¹`. -/
private def S1 : Fin 1 → Fin 1 → ℚ := ![![5]]

example :
    (∀ j, j ≠ maxSqNormIndex S1 →
      ⟪toEuclidean (ratOrthoTarget S1), toEuclidean (S1 j)⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖fun j => toEuclidean (S1 j)‖ < ‖toEuclidean (ratOrthoTarget S1)‖ ∧
    ‖toEuclidean (ratOrthoTarget S1)‖ ≤ (9 / 16 : ℝ) * ‖fun j => toEuclidean (S1 j)‖ := by
  refine ratOrthoTarget_spec S1 ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : c 0 * (5 : ℝ) = 0 := by
    simpa [S1, toEuclidean] using congr_arg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hc
  fin_cases i
  change c 0 = 0
  linarith

/-- Concrete 2-D skewed lattice basis `S2 = ![![1, 0], ![10, 1]]` in `ℚ²`. -/
private def S2 : Fin 2 → Fin 2 → ℚ := ![![1, 0], ![10, 1]]

private theorem S2_linearIndependent : LinearIndependent ℝ (fun j => toEuclidean (S2 j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hc
  have h1 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hc
  simp [Fin.sum_univ_two, S2, toEuclidean] at h0 h1
  intro i
  fin_cases i
  · change c 0 = 0; linarith
  · change c 1 = 0; linarith

private theorem maxSqNormIndex_S2 : maxSqNormIndex S2 = 1 := by
  simp only [maxSqNormIndex, sqNormRat, S2, List.finRange, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

example :
    (∀ j, j ≠ maxSqNormIndex S2 →
      ⟪toEuclidean (ratOrthoTarget S2), toEuclidean (S2 j)⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖fun j => toEuclidean (S2 j)‖ < ‖toEuclidean (ratOrthoTarget S2)‖ ∧
    ‖toEuclidean (ratOrthoTarget S2)‖ ≤ (9 / 16 : ℝ) * ‖fun j => toEuclidean (S2 j)‖ :=
  ratOrthoTarget_spec S2 S2_linearIndependent

/-- Concrete 3-D skewed lattice basis `S3 = ![![1, 0, 0], ![0, 1, 0], ![7, 5, 1]]` in `ℚ³`:
exercises multi-row `(2 × 3)` `ratKernelBasis` orthogonality and rational scaling. -/
private def S3 : Fin 3 → Fin 3 → ℚ := ![![1, 0, 0], ![0, 1, 0], ![7, 5, 1]]

example : maxSqNormIndex S3 = 2 := by
  simp only [maxSqNormIndex, sqNormRat, S3, List.finRange, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

example :
    (∀ j, j ≠ maxSqNormIndex S3 →
      ⟪toEuclidean (ratOrthoTarget S3), toEuclidean (S3 j)⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖fun j => toEuclidean (S3 j)‖ < ‖toEuclidean (ratOrthoTarget S3)‖ ∧
    ‖toEuclidean (ratOrthoTarget S3)‖ ≤ (9 / 16 : ℝ) * ‖fun j => toEuclidean (S3 j)‖ := by
  refine ratOrthoTarget_spec S3 ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hc
  have h1 := congr_arg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hc
  have h2 := congr_arg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hc
  simp [Fin.sum_univ_three, S3, toEuclidean] at h0 h1 h2
  intro i
  fin_cases i
  · change c 0 = 0; linarith
  · change c 1 = 0; linarith
  · change c 2 = 0; linarith

/-- End-to-end concrete 2-D one-round shortening check on `S2`: replacing `![10, 1]` by
`u = ![0, ±5]` matching the sign of `ratOrthoTarget S2` preserves linear independence,
preserves `‖S'‖ ≤ ‖S‖`, and strictly contracts `sqNormProd` by `≤ (13/16)^2`. -/
example :
    let S := fun j => toEuclidean (S2 j)
    let i := maxSqNormIndex S2
    let t := toEuclidean (ratOrthoTarget S2)
    let u := if (0 : ℝ) ≤ t 1 then toEuclidean ![0, 5] else toEuclidean ![0, -5]
    LinearIndependent ℝ (Function.update S i u) ∧
      ‖Function.update S i u‖ ≤ ‖S‖ ∧
      sqNormProd (Function.update S i u) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd S := by
  intro S i t u
  have hli : LinearIndependent ℝ S := S2_linearIndependent
  have ⟨horth, hlo, hhi⟩ := ratOrthoTarget_spec S2 hli
  have hi_eq : ‖S i‖ = ‖S‖ := norm_maxSqNormIndex_eq_pi_norm S2
  have hS_norm_sq : ‖S‖ ^ 2 = 101 := by
    rw [← hi_eq, show i = 1 from maxSqNormIndex_S2, ← sqNormRat_cast_eq_norm_sq]
    norm_num [S2, sqNormRat, Fin.sum_univ_two]
  have hS_norm_ge : (10 : ℝ) ≤ ‖S‖ := by nlinarith [norm_nonneg S]
  have hS_norm_le : ‖S‖ ≤ (10.1 : ℝ) := by nlinarith [norm_nonneg S]
  have ht0 : t 0 = 0 := by
    have hne : (0 : Fin 2) ≠ maxSqNormIndex S2 := by rw [maxSqNormIndex_S2]; decide
    have h := horth 0 hne
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [t, S2, toEuclidean, Fin.sum_univ_two] using h
  have ht_norm_eq : ‖t‖ = |t 1| := by
    have hsq : ‖t‖ ^ 2 = (t 1) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, ht0]
      simp [Real.norm_eq_abs]
    nlinarith [norm_nonneg t, abs_nonneg (t 1), sq_abs (t 1)]
  have hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖ := by
    have h5_lo : (5 : ℝ) < |t 1| := by rw [← ht_norm_eq]; linarith
    have h5_hi : |t 1| ≤ (6 : ℝ) := by rw [← ht_norm_eq]; linarith
    have hdist_sq : ∀ c : ℚ, ‖toEuclidean ![0, c] - t‖ ^ 2 = ((c : ℝ) - t 1) ^ 2 := by
      intro c
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [toEuclidean, ht0, Real.norm_eq_abs]
    dsimp only [u]
    split_ifs with hsgn
    · have ht1 : (5 : ℝ) < t 1 ∧ t 1 ≤ 6 := by
        rw [abs_of_nonneg hsgn] at h5_lo h5_hi; exact ⟨h5_lo, h5_hi⟩
      have hsq : ‖toEuclidean ![0, 5] - t‖ ^ 2 = (5 - t 1) ^ 2 := by
        simpa using hdist_sq 5
      nlinarith [norm_nonneg (toEuclidean ![0, 5] - t)]
    · push Not at hsgn
      have ht1 : (-6 : ℝ) ≤ t 1 ∧ t 1 < -5 := by
        rw [abs_of_neg hsgn] at h5_lo h5_hi; constructor <;> linarith
      have hsq : ‖toEuclidean ![0, -5] - t‖ ^ 2 = (-5 - t 1) ^ 2 := by
        simpa using hdist_sq (-5)
      nlinarith [norm_nonneg (toEuclidean ![0, -5] - t)]
  exact ⟨shortenStep_linearIndependent hli horth hlo.le hu_dist,
    shortenStep_pi_norm_le hhi hu_dist,
    shortenStep_sqNormProd_le hi_eq hhi hu_dist⟩

private theorem fin_cast_two_cases {n : ℕ} (hn : n = 2) (j : Fin n) :
    j = Fin.cast hn.symm 0 ∨ j = Fin.cast hn.symm 1 := by
  have hjlt := j.isLt
  by_cases h : j.val = 0
  · left; exact Fin.ext (by simpa using h)
  · right; exact Fin.ext (by simp; omega)

/-- End-to-end concrete `shortenLoop_isSolution_givp` and `shortenGuardedIter_isSolution_givp`
checks on `L = ℤ² ⊂ EuclideanSpace ℝ (Fin 2)` with `φ _ = 1`, `γ = 1` and coordinatewise rounding
oracle starting from `S2 = ![![1, 0], ![10, 1]]`. -/
example :
    let e : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun j =>
      WithLp.toLp 2 (fun k => if j = k then (1 : ℝ) else 0)
    let L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℤ (Set.range e)
    ∃ (S₀ : Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2))
      (stepTarget : (Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2)) →
        Fin (finrank ℤ L) × EuclideanSpace ℝ (Fin 2))
      (oracle : ℕ → (Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2)) →
        EuclideanSpace ℝ (Fin 2) → ℝ → Option (EuclideanSpace ℝ (Fin 2)))
      (seq : ℕ → Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2)),
      let K := shortenRoundBound (finrank ℤ L) 101
      let S_out := shortenLoop L stepTarget oracle K S₀
      (GIVP.IsSolution (fun _ => (1 : ℝ)) 8 L S_out ∧ ‖S_out‖ ≤ ‖S₀‖) ∧
        (GIVP.IsSolution (fun _ => (1 : ℝ)) 8 L (seq K) ∧ ‖seq K‖ ≤ ‖seq 0‖) := by
  classical
  intro e L
  have he_li : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hc
    fin_cases i <;> simpa [e, Fin.sum_univ_two] using hi
  have hrank : finrank ℤ L = 2 := by
    let b : Basis (Fin 2) ℤ L := Basis.span (he_li.restrict_scalars' ℤ)
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let S₀ : Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2) := fun i =>
    toEuclidean (S2 (Fin.cast hrank i))
  let stepTarget : (Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2)) →
      Fin (finrank ℤ L) × EuclideanSpace ℝ (Fin 2) := fun S =>
    if h : ∃ i : Fin (finrank ℤ L), ‖S i‖ = ‖S‖ ∧
        ∃ t : EuclideanSpace ℝ (Fin 2),
          (∀ j, j ≠ i → ⟪t, S j⟫ = 0) ∧ (1 / 2 : ℝ) * ‖S‖ ≤ ‖t‖ ∧ ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖ then
      (h.choose, h.choose_spec.2.choose)
    else (Fin.cast hrank.symm 0, 0)
  have hTarget : ValidTargetOracle L stepTarget := by
    intro S hS_li _
    have hmax : ∃ i : Fin (finrank ℤ L), ‖S i‖ = ‖S‖ := by
      have hne : (Finset.univ : Finset (Fin (finrank ℤ L))).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨Fin.cast hrank.symm 0⟩
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖S j‖) hne
      refine ⟨i, le_antisymm (norm_le_pi_norm S i) ?_⟩
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      exact fun j => hi j (Finset.mem_univ j)
    obtain ⟨i, hi⟩ := hmax
    have hj_other : ∃ j : Fin (finrank ℤ L), j ≠ i := by
      let j0 : Fin (finrank ℤ L) := Fin.cast hrank.symm 0
      let j1 : Fin (finrank ℤ L) := Fin.cast hrank.symm 1
      by_cases h : i = j0
      · refine ⟨j1, fun heq => ?_⟩
        have := congr_arg Fin.val (heq.trans h)
        simp [j0, j1] at this
      · exact ⟨j0, Ne.symm h⟩
    obtain ⟨j, hji⟩ := hj_other
    let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-(S j 1), S j 0]
    have hv_orth : ⟪v, S j⟫ = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [v, dotProduct, Fin.sum_univ_two]
      ring
    have hv_norm : ‖v‖ = ‖S j‖ := by
      have hsq : ‖v‖ ^ 2 = ‖S j‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
          Fin.sum_univ_two]
        simp [v, Real.norm_eq_abs]
        ring
      nlinarith [norm_nonneg v, norm_nonneg (S j)]
    have hv_pos : 0 < ‖v‖ := by
      rw [hv_norm]; exact norm_pos_iff.mpr (hS_li.ne_zero j)
    let t : EuclideanSpace ℝ (Fin 2) := ((1 / 2 : ℝ) * ‖S‖ / ‖v‖) • v
    have ht_norm : ‖t‖ = (1 / 2 : ℝ) * ‖S‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hv_pos.ne']
    have hex : ∃ i' : Fin (finrank ℤ L), ‖S i'‖ = ‖S‖ ∧
        ∃ t' : EuclideanSpace ℝ (Fin 2),
          (∀ k, k ≠ i' → ⟪t', S k⟫ = 0) ∧ (1 / 2 : ℝ) * ‖S‖ ≤ ‖t'‖ ∧
            ‖t'‖ ≤ (9 / 16 : ℝ) * ‖S‖ := by
      refine ⟨i, hi, t, ?_, by linarith, by linarith [norm_nonneg S]⟩
      intro k hki
      have hkj : k = j := by
        apply Fin.ext
        have hklt := k.isLt; have hilt := i.isLt; have hjlt := j.isLt
        have hki' : k.val ≠ i.val := fun h => hki (Fin.ext h)
        have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
        omega
      subst hkj
      rw [inner_smul_left, hv_orth, mul_zero]
    dsimp only [stepTarget]
    simp only [hex, ↓reduceDIte]
    exact ⟨hex.choose_spec.1, hex.choose_spec.2.choose_spec⟩
  let roundVec : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun t =>
    WithLp.toLp 2 (fun k => (round (t k) : ℝ))
  let oracle : ℕ → (Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2)) →
      EuclideanSpace ℝ (Fin 2) → ℝ → Option (EuclideanSpace ℝ (Fin 2)) :=
    fun _ _ t _ => some (roundVec t)
  have hround_mem : ∀ t, roundVec t ∈ L := by
    intro t
    have heq : roundVec t = round (t 0) • e 0 + round (t 1) • e 1 := by
      ext k; fin_cases k <;> simp [roundVec, e]
    rw [heq]
    exact L.add_mem (L.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
      (L.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
  have hround_dist : ∀ t, ‖roundVec t - t‖ ≤ 1 := by
    intro t
    have hsq : ‖roundVec t - t‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      have h0 : |((round (t 0) : ℤ) : ℝ) - t 0| ≤ 1 / 2 := by
        simpa [abs_sub_comm] using abs_sub_round (t 0)
      have h1 : |((round (t 1) : ℤ) : ℝ) - t 1| ≤ 1 / 2 := by
        simpa [abs_sub_comm] using abs_sub_round (t 1)
      have h0sq : ((round (t 0) : ℝ) - t 0) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_abs ((round (t 0) : ℝ) - t 0), abs_nonneg ((round (t 0) : ℝ) - t 0)]
      have h1sq : ((round (t 1) : ℝ) - t 1) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_abs ((round (t 1) : ℝ) - t 1), abs_nonneg ((round (t 1) : ℝ) - t 1)]
      simp only [WithLp.ofLp_sub, Pi.sub_apply, roundVec, Real.norm_eq_abs, sq_abs]
      linarith
    nlinarith [norm_nonneg (roundVec t - t)]
  have he_gram : HasIntegralGram e := by
    intro i j
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    fin_cases i <;> fin_cases j <;> simp [e, dotProduct]
  have hL_gram : ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫ = z :=
    fun _ hx _ hy => exists_int_inner_of_mem_span he_gram hx hy
  have hS₀_li : LinearIndependent ℝ S₀ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hc
    have h1 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hc
    have hsum : ∀ f : Fin (finrank ℤ L) → ℝ,
        ∑ i, f i = f (Fin.cast hrank.symm 0) + f (Fin.cast hrank.symm 1) := by
      intro f
      rw [← Equiv.sum_comp (finCongr hrank.symm), Fin.sum_univ_two]
      rfl
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      WithLp.ofLp_zero, Pi.zero_apply] at h0 h1
    rw [hsum] at h0 h1
    simp [S₀, S2, toEuclidean] at h0 h1
    intro i
    rcases fin_cast_two_cases hrank i with rfl | rfl <;> linarith
  have hS₀_mem : ∀ j, S₀ j ∈ L := by
    intro j
    rcases fin_cast_two_cases hrank j with rfl | rfl
    · have : S₀ (Fin.cast hrank.symm 0) = e 0 := by
        ext k; fin_cases k <;> simp [S₀, S2, toEuclidean, e]
      rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
    · have : S₀ (Fin.cast hrank.symm 1) = (10 : ℤ) • e 0 + e 1 := by
        ext k; fin_cases k <;> simp [S₀, S2, toEuclidean, e]
      rw [this]
      exact L.add_mem (L.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.subset_span ⟨1, rfl⟩)
  have hB : ∀ j, ‖S₀ j‖ ^ 2 ≤ (101 : ℕ) := by
    intro j
    rcases fin_cast_two_cases hrank j with rfl | rfl
    · simp only [S₀, Fin.cast_cast, Fin.cast_eq_self, ← sqNormRat_cast_eq_norm_sq]
      norm_num [S2, sqNormRat, Fin.sum_univ_two]
    · simp only [S₀, Fin.cast_cast, Fin.cast_eq_self, ← sqNormRat_cast_eq_norm_sq]
      norm_num [S2, sqNormRat, Fin.sum_univ_two]
  have hround_sol : ∀ S, IncGDD.IsValidInstance (fun _ => (1 : ℝ)) 1 L S (‖S‖ / 8) →
      IncGDD.IsSolution 8 L S (stepTarget S).2 (‖S‖ / 8) (roundVec (stepTarget S).2) := by
    intro S hval
    refine ⟨hround_mem _, ?_⟩
    have hr : (1 : ℝ) < ‖S‖ / 8 := by simpa using hval.radius_gt
    linarith [hround_dist (stepTarget S).2, norm_nonneg S]
  have hres1 := shortenLoop_isSolution_givp (fun _ => (1 : ℝ)) 1 L stepTarget oracle hTarget
    hL_gram 101 S₀ hS₀_li hS₀_mem hB fun k _ hval =>
      ⟨roundVec (stepTarget (shortenLoop L stepTarget oracle k S₀)).2, rfl, hround_sol _ hval⟩
  let seq : ℕ → Fin (finrank ℤ L) → EuclideanSpace ℝ (Fin 2) :=
    Nat.rec S₀ fun _ Sk => shortenGuardedStep L Sk (stepTarget Sk).1 (roundVec (stepTarget Sk).2)
  have hres2 := shortenGuardedIter_isSolution_givp (fun _ => (1 : ℝ)) 1 L stepTarget hTarget
    hL_gram 101 seq (fun k => roundVec (stepTarget (seq k)).2) hS₀_li hS₀_mem hB
    (fun _ _ => rfl) (fun k _ hval => hround_sol (seq k) hval)
  exact ⟨S₀, stepTarget, oracle, seq, by simpa using hres1, by simpa using hres2⟩

end CslibFrontierTests.Crypto.LatticeMR07Shorten
