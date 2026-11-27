/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds
import CslibFrontier.MachineLearning.Rademacher.Dudley

/-!
# Tests for covering/packing numbers and Dudley's entropy integral

Ordinary-import `module` client (no `import all`) exercising:
1. Metric covering/packing duality (`Cslib.Metric`): exact empty/singleton values, non-trivial
   separation on `{0, 1} ⊆ ℝ` (`packingNumber = 2` for `ε < 1`), packing–covering duality
   (`internalCoveringNumber_le_packingNumber`, `packingNumber_two_mul_le_coveringNumber`,
   `internalCoveringNumber_le_coveringNumber_half`), total boundedness
   (`exists_internalCover_of_lt_top`), and translation invariance (`coveringNumber_vadd`).
2. Volumetric closed-ball covering bounds in `EuclideanSpace ℝ (Fin d)` and `ℝ` (`d = 0, 1, 2`),
   including the exact `ε = 1 / 2` bound `(1 + 2 * 1 / (1 / 2)) ^ d = 5 ^ d` matching
   `NormedSpace.exists_halfNet`, plus an explicit `0`-dimensional (`Subsingleton`) check.
3. Truncated and full `[0, R]` Dudley entropy integrals on concrete bounded and **uncountable**
   real-valued function classes (`empiricalRademacherComplexity_le_dudley_integral`,
   `empiricalRademacherComplexity_le_dudley_integral_zero`,
   `empiricalRademacherComplexity_le_dudley_of_bound`).
4. Polynomial covering integration (`empiricalRademacherComplexity_le_of_polynomial_covering`)
   at `d = 0` (exact `0` complexity) and `d > 0`, AND concrete Lipschitz parametric families on an
   uncountable domain (`ℝ` with clipped affine shifts) showing `O(L r √(d / m))` with no `log m`.
5. Boundary cases (`m = 0`, `L = 0`, `r = 0`, `Θ = ∅`) of
   `empiricalRademacherComplexity_lipschitz_ball_le`.
6. Population generalization bound (`lipschitz_ball_generalization_bound`) on `Fin 3`.
7. Bridge from VC-dimension Hamming packing to empirical `L²(P_m)` covering numbers
   (`empiricalCoveringNumber_bitClass_le_of_vcDim`) and direct derivation of an `O(√(d / m))`
   Rademacher bound via Dudley's entropy integral on `thresholdClass` (`vcDim ≤ 1`).
-/

set_option linter.privateModule false

open Cslib.Metric Cslib.MachineLearning Cslib.MachineLearning.PACLearning
open Cslib.MachineLearning.OnlineLearning.MistakeBound
open MeasureTheory Finset
open scoped BigOperators

namespace Cslib.MachineLearning.Tests

/-! ### Metric covering & packing numbers and duality -/

example : coveringNumber (∅ : Set ℝ) (1 : ℝ) = 0 ∧
    internalCoveringNumber (∅ : Set ℝ) 1 = 0 ∧
    packingNumber (∅ : Set ℝ) 1 = 0 :=
  ⟨coveringNumber_empty 1, internalCoveringNumber_empty 1, packingNumber_empty 1⟩

/-- Exact separation check on the 2-point set `{0, 1} ⊆ ℝ`: strictly `(1/2)`-separated, so
`2 ≤ packingNumber {0, 1} (1/2) ≤ coveringNumber {0, 1} (1/4)` and covered by `{0, 1}`
(`packingNumber = internalCoveringNumber = coveringNumber = 2` at small scale). -/
example : (2 : ℕ∞) ≤ packingNumber ({0, 1} : Set ℝ) (1 / 2) ∧
    internalCoveringNumber ({0, 1} : Set ℝ) (1 / 2) ≤ 2 ∧
    coveringNumber ({0, 1} : Set ℝ) (1 / 2) ≤ 2 := by
  have hpack : (2 : ℕ∞) ≤ packingNumber ({0, 1} : Set ℝ) (1 / 2) := by
    let P : Finset ℝ := {0, 1}
    have hcard : P.card = 2 := Finset.card_pair (by norm_num : (0 : ℝ) ≠ 1)
    have hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 / 2 : ℝ) < dist x y := by
      intro x hx y hy hxy
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · norm_num [Real.dist_eq]
      · norm_num [Real.dist_eq]
      · exact (hxy rfl).elim
    have h := card_le_packingNumber (s := ({0, 1} : Set ℝ)) (ε := 1 / 2)
      (P := P) (by intro x hx; simpa [P] using hx) hsep
    simpa [hcard] using h
  have hint : internalCoveringNumber ({0, 1} : Set ℝ) (1 / 2) ≤ 2 := by
    let T : Finset ℝ := {0, 1}
    have hcard : T.card = 2 := Finset.card_pair (by norm_num : (0 : ℝ) ≠ 1)
    have h := internalCoveringNumber_le_card (s := ({0, 1} : Set ℝ)) (ε := 1 / 2) (T := T)
      (by intro x hx; simpa [T] using hx)
      (by intro x hx; exact ⟨x, by simpa [T] using hx, by simp⟩)
    simpa [hcard] using h
  exact ⟨hpack, hint, (coveringNumber_le_internalCoveringNumber _ _).trans hint⟩

/-- Negative separation check: the same two-point set has `coveringNumber {0, 1} (1/2) = 1`
because the external midpoint `1/2` covers both `0` and `1` within radius `1/2` — showing
strict separation between `coveringNumber` (`1`) and `internalCoveringNumber` (`2` at `ε = 1/2`). -/
example : coveringNumber ({0, 1} : Set ℝ) (1 / 2) = 1 ∧
    (2 : ℕ∞) ≤ internalCoveringNumber ({0, 1} : Set ℝ) (1 / 2) := by
  constructor
  · refine le_antisymm ?_ (one_le_coveringNumber ⟨0, by simp⟩ _)
    refine coveringNumber_le_one_of_subset_closedBall (x₀ := (1 / 2 : ℝ)) ?_
    rintro x (rfl | rfl) <;> norm_num [Real.dist_eq]
  · refine le_internalCoveringNumber fun T hTs hT => ?_
    obtain ⟨y₀, hy₀, h0⟩ := hT 0 (by simp)
    obtain ⟨y₁, hy₁, h1⟩ := hT 1 (by simp)
    have h0eq : y₀ = 0 := by
      rcases hTs y₀ hy₀ with rfl | rfl
      · rfl
      · norm_num [Real.dist_eq] at h0
    have h1eq : y₁ = 1 := by
      rcases hTs y₁ hy₁ with rfl | rfl
      · norm_num [Real.dist_eq] at h1
      · rfl
    have hne : y₀ ≠ y₁ := by rw [h0eq, h1eq]; norm_num
    have hsub : ({y₀, y₁} : Finset ℝ) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hcard : 2 ≤ T.card := by
      have h2 : ({y₀, y₁} : Finset ℝ).card = 2 := Finset.card_pair hne
      rw [← h2]
      exact Finset.card_le_card hsub
    exact_mod_cast hcard

/-- Packing–covering chain on any pseudometric set at scale `1`: `packingNumber s 2 ≤
coveringNumber s 1 ≤ internalCoveringNumber s 1 ≤ packingNumber s 1 ≤ coveringNumber s (1/2)`. -/
example (s : Set ℝ) :
    packingNumber s 2 ≤ coveringNumber s 1 ∧
    internalCoveringNumber s 1 ≤ coveringNumber s (1 / 2) :=
  ⟨by simpa using packingNumber_two_mul_le_coveringNumber s 1,
    internalCoveringNumber_le_coveringNumber_half s zero_le_one⟩

/-- Check `internalCoveringNumber_lt_top_of_totallyBounded` and `exists_internalCover_of_lt_top` on
`Metric.closedBall (0 : ℝ) 2`. -/
example : ∃ T : Finset ℝ,
    (T.card : ℕ∞) = internalCoveringNumber (Metric.closedBall (0 : ℝ) 2) (1 / 2) ∧
    (∀ y ∈ T, y ∈ Metric.closedBall (0 : ℝ) 2) ∧
    ∀ x ∈ Metric.closedBall (0 : ℝ) 2, ∃ y ∈ T, dist x y ≤ 1 / 2 :=
  exists_internalCover_of_lt_top <|
    internalCoveringNumber_lt_top_of_totallyBounded
      (isCompact_closedBall (0 : ℝ) 2).totallyBounded (by norm_num)

/-- Volumetric closed-ball bound recovers `5 ^ d` at `R = 1, ε = 1 / 2` in
`EuclideanSpace ℝ (Fin d)`, and checks the `0`-dimensional `Subsingleton` case. -/
example (d : ℕ) :
    ((packingNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (1 / 2)).toNat : ℝ) ≤
      5 ^ d ∧
    ((coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (1 / 2)).toNat : ℝ) ≤
      6 ^ d := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin
  have h1 : (1 + 2 * (1 : ℝ) / (1 / 2)) = 5 := by norm_num
  have h2 : (3 * (1 : ℝ) / (1 / 2)) = 6 := by norm_num
  refine ⟨?_, ?_⟩
  · simpa only [hrank, h1] using
      packingNumber_closedBall_toNat_le (0 : EuclideanSpace ℝ (Fin d))
        (R := 1) (ε := 1 / 2) zero_le_one (by norm_num)
  · simpa only [hrank, h2] using
      coveringNumber_closedBall_toNat_le_three_pow (0 : EuclideanSpace ℝ (Fin d))
        (R := 1) (ε := 1 / 2) (by norm_num) (by norm_num)

example : ((packingNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 3) 0.01).toNat : ℝ) ≤
    1 := by
  have h := packingNumber_closedBall_toNat_le (0 : EuclideanSpace ℝ (Fin 0))
    (R := 3) (ε := 0.01) (by norm_num) (by norm_num)
  simpa [finrank_euclideanSpace_fin] using h

/-! ### Dudley entropy integral: truncated, improper `[0, R]`, and singleton/antitone checks -/

/-- For a singleton class `{f₀}`, `empiricalCoveringNumber = 1`, `log 1 = 0`, and the full `[0, 1]`
Dudley integral vanishes (`0`). -/
example {Z : Type*} (f₀ : Z → ℝ) (S : Fin 4 → Z) :
    empiricalRademacherComplexity ({f₀} : Set (Z → ℝ)) S ≤
      16 / Real.sqrt 4 *
        ∫ ε in (0 : ℝ)..1,
          Real.sqrt (Real.log (empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε).toNat) := by
  have hF : ∀ f ∈ ({f₀} : Set (Z → ℝ)),
      dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ 1 := by
    rintro f rfl; simp
  have hcov (ε : ℝ) (hε : 0 < ε) :
      (empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε).toNat = 1 := by
    have hlt := empiricalCoveringNumber_lt_top (f₀ := f₀) (R := 1) hF hε
    have hle : empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε ≤ 1 :=
      coveringNumber_le_one_of_subset_closedBall (x₀ := empiricalL2Vec S f₀) (by
        rintro _ ⟨f, rfl, rfl⟩; simpa using hε.le)
    have hge : 1 ≤ empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε :=
      one_le_coveringNumber (s := empiricalL2Vec S '' {f₀})
        ⟨empiricalL2Vec S f₀, f₀, rfl, rfl⟩ ε
    have heq : empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε = 1 := le_antisymm hle hge
    simp [heq]
  have hint : IntervalIntegrable
      (fun ε => Real.sqrt (Real.log (empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε).toNat))
      volume 0 1 := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr ?_
    intro ε hε
    rw [Set.uIoc_of_le zero_le_one] at hε
    simp [hcov ε hε.1]
  exact empiricalRademacherComplexity_le_dudley_integral_zero (by omega) S f₀ zero_lt_one hF hint

/-- Truncated Dudley entropy integral plus `empiricalCoveringNumber_anti` & `lt_top`. -/
example {Z : Type*} (F : Set (Z → ℝ)) (S : Fin 5 → Z)
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ 1) :
    empiricalCoveringNumber F S 1 ≤ empiricalCoveringNumber F S (1 / 2) ∧
    empiricalCoveringNumber F S (1 / 2) < ⊤ ∧
    empiricalRademacherComplexity F S ≤
      4 * (1 / 4 : ℝ) + 16 / Real.sqrt 5 *
        ∫ ε in (1 / 4 : ℝ)..1, Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat) := by
  have hdist : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S 0) ≤ 1 := fun f hf =>
    dist_empiricalL2Vec_le_of_abs_sub_le S zero_le_one fun i => by
      simpa using hF f hf (S i)
  exact ⟨empiricalCoveringNumber_anti F S (by norm_num),
    empiricalCoveringNumber_lt_top hdist (by norm_num),
    empiricalRademacherComplexity_le_dudley_integral (by omega) S 0
      (by norm_num) (by norm_num) hdist⟩

/-- `d = 0` polynomial covering bound yields `0`. -/
example {Z : Type*} (f₀ : Z → ℝ) (S : Fin 3 → Z) :
    empiricalRademacherComplexity ({f₀} : Set (Z → ℝ)) S ≤ 0 := by
  have h := empiricalRademacherComplexity_le_of_polynomial_covering
    (F := ({f₀} : Set (Z → ℝ))) (by omega) S f₀ (R := 1) (C := 1) (d := 0)
    zero_lt_one le_rfl (by rintro f rfl; simp) (fun ε hε => by
      have hle : empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε ≤ 1 :=
        coveringNumber_le_one_of_subset_closedBall (x₀ := empiricalL2Vec S f₀) (by
          rintro _ ⟨f, rfl, rfl⟩; simpa using hε.1.le)
      have hnat : (empiricalCoveringNumber ({f₀} : Set (Z → ℝ)) S ε).toNat ≤ 1 :=
        ENat.toNat_le_of_le_natCast hle
      simpa using Nat.cast_le (α := ℝ).2 hnat)
  simpa using h

/-! ### Uncountable real-valued Lipschitz parametric class (`ℝ` and `Fin 2`) -/

/-- Shifted bounded affine family on **uncountable** domain `ℝ` indexed by `θ ∈ [-2, 2] ⊆ ℝ`:
`Φ θ x = max (-1) (min 1 (x + θ))` is `1`-Lipschitz in `θ` uniformly over all `x : ℝ`. -/
private noncomputable def clippedShift (θ : ℝ) (x : ℝ) : ℝ :=
  max (-1) (min 1 (x + θ))

private theorem abs_clippedShift_sub_le (θ₁ θ₂ x : ℝ) :
    |clippedShift θ₁ x - clippedShift θ₂ x| ≤ 1 * dist θ₁ θ₂ := by
  rw [one_mul, Real.dist_eq, clippedShift, clippedShift]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have h1 := le_max_right (-1 : ℝ) (min 1 (x + θ₂))
    have h2 := le_max_left (-1 : ℝ) (min 1 (x + θ₂))
    have h := le_abs_self (θ₁ - θ₂)
    rcases max_cases (-1 : ℝ) (min 1 (x + θ₁)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]; linarith [abs_nonneg (θ₁ - θ₂)]
    · rw [heq]
      rcases min_cases (1 : ℝ) (x + θ₂) with ⟨hm2, _⟩ | ⟨hm2, _⟩
      · have : min 1 (x + θ₁) ≤ 1 := min_le_left _ _
        linarith [hm2 ▸ h1, abs_nonneg (θ₁ - θ₂)]
      · have : min 1 (x + θ₁) ≤ x + θ₁ := min_le_right _ _
        linarith [hm2 ▸ h1]
  · have h1 := le_max_right (-1 : ℝ) (min 1 (x + θ₁))
    have h2 := le_max_left (-1 : ℝ) (min 1 (x + θ₁))
    have h := neg_le_abs (θ₁ - θ₂)
    rcases max_cases (-1 : ℝ) (min 1 (x + θ₂)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]; linarith [abs_nonneg (θ₁ - θ₂)]
    · rw [heq]
      rcases min_cases (1 : ℝ) (x + θ₁) with ⟨hm1, _⟩ | ⟨hm1, _⟩
      · have : min 1 (x + θ₂) ≤ 1 := min_le_left _ _
        linarith [hm1 ▸ h1, abs_nonneg (θ₁ - θ₂)]
      · have : min 1 (x + θ₂) ≤ x + θ₂ := min_le_right _ _
        linarith [hm1 ▸ h1]

example {m : ℕ} (S : Fin m → ℝ) :
    empiricalRademacherComplexity (clippedShift '' Metric.closedBall (0 : ℝ) 2) S ≤
      32 * Real.sqrt ((1 + Real.log 3) / m) := by
  have h := empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise S (θ₀ := (0 : ℝ))
    (r := 2) (L := 1) (by norm_num) zero_le_one Set.Subset.rfl
    fun θ₁ _ θ₂ _ x => abs_clippedShift_sub_le θ₁ θ₂ x
  simpa only [Module.finrank_self, Nat.cast_one, one_mul,
    show (16 : ℝ) * 1 * 2 = 32 by norm_num] using h

/-- Boundary checks: `m = 0`, `r = 0`, `L = 0`, and `Θ = ∅`. -/
example (S : Fin 0 → ℝ) :
    empiricalRademacherComplexity (clippedShift '' Metric.closedBall (0 : ℝ) 2) S ≤ 0 := by
  simpa using empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise S (θ₀ := (0 : ℝ))
    (r := 2) (L := 1) (by norm_num) zero_le_one Set.Subset.rfl
    fun θ₁ _ θ₂ _ x => abs_clippedShift_sub_le θ₁ θ₂ x

example (S : Fin 5 → ℝ) :
    empiricalRademacherComplexity (clippedShift '' ({0} : Set ℝ)) S ≤ 0 := by
  have hΘ : ({0} : Set ℝ) ⊆ Metric.closedBall 0 0 := by rw [Metric.closedBall_zero]
  simpa using empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise S (θ₀ := (0 : ℝ))
    (r := 0) (L := 1) le_rfl zero_le_one hΘ
    fun θ₁ _ θ₂ _ x => abs_clippedShift_sub_le θ₁ θ₂ x

example (S : Fin 5 → ℝ) :
    empiricalRademacherComplexity ((fun (_θ : ℝ) (_x : ℝ) => (7 : ℝ)) ''
      Metric.closedBall (0 : ℝ) 5) S ≤ 0 := by
  have h := empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise S
    (Φ := fun (_θ : ℝ) (_x : ℝ) => (7 : ℝ)) (θ₀ := (0 : ℝ))
    (r := 5) (L := 0) (by norm_num) le_rfl Set.Subset.rfl (fun _ _ _ _ _ => by simp)
  simpa only [mul_zero, zero_mul] using h

/-- Uniform generalization bound for `clippedShift` over a finite domain `Fin 3`. -/
example (D : PMF (Fin 3)) :
    ((Probability.PMF.pi fun _ : Fin 20 => D).toOuterMeasure
      {S | ∃ θ ∈ Metric.closedBall (0 : ℝ) 1,
        (𝔼 i, clippedShift θ (S i : ℝ)) +
          32 * 1 * 1 * Real.sqrt (1 * (1 + Real.log 3) / 20) +
          (1 - (-1)) * Real.sqrt (Real.log (1 / (1 / 10 : ℝ)) / (2 * 20)) <
          ∑ z : Fin 3, (D z).toReal * clippedShift θ (z : ℝ)}).toReal ≤ 1 / 10 := by
  have hIcc : ∀ θ ∈ Metric.closedBall (0 : ℝ) 1, ∀ z : Fin 3,
      clippedShift θ (z : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro θ _ z
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have h := lipschitz_ball_generalization_bound D (m := 20) (by omega)
    (Φ := fun θ (z : Fin 3) => clippedShift θ (z : ℝ)) (θ₀ := (0 : ℝ))
    (r := 1) (L := 1) (a := -1) (b := 1) zero_le_one zero_le_one (by norm_num)
    Set.Subset.rfl hIcc (fun θ₁ _ θ₂ _ z => abs_clippedShift_sub_le θ₁ θ₂ z)
    (δ := 1 / 10) (by norm_num)
  simpa [Module.finrank_self] using h

/-! ### Empirical `L²(P_m)` covering & Dudley bound for a VC class (`thresholdClass`) -/

/-- Direct end-to-end derivation of the `O(1 / √m)` Rademacher bound (no `log m`!) for
`thresholdClass` via `empiricalCoveringNumber_bitClass_le_of_vcDim` + Dudley's polynomial entropy
integral. -/
example {m : ℕ} (hm : 0 < m) (S : Fin m → ℕ) :
    empiricalRademacherComplexity (bitClass (thresholdClass ℕ)) S ≤
      16 * Real.sqrt (4 * (1 + Real.log (Real.sqrt 8)) / m) := by
  have hbound : ∀ f ∈ bitClass (thresholdClass ℕ),
      dist (empiricalL2Vec S f) (empiricalL2Vec S 0) ≤ 1 := by
    intro f hf
    refine dist_empiricalL2Vec_le_of_abs_sub_le S zero_le_one fun i => ?_
    obtain ⟨h0, h1⟩ := mem_Icc_of_mem_bitClass hf (S i)
    simp only [Pi.zero_apply, sub_zero, abs_le]
    exact ⟨by linarith, h1⟩
  have hsh : ∀ W : Finset ℕ, SetShatters (thresholdClass ℕ) ↑W → W.card ≤ 1 := fun W hW => by
    by_contra hgt
    exact not_setShatters_thresholdClass (by omega) hW
  have h1le : (1 : ℝ) ≤ Real.sqrt 8 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  have h := empiricalRademacherComplexity_le_of_polynomial_covering hm S 0
    (R := 1) (C := Real.sqrt 8) (d := 4) zero_lt_one h1le hbound
    fun ε hε => by
      simpa only [show 4 * 1 = 4 by norm_num] using
        empiricalCoveringNumber_bitClass_le_of_vcDim hsh S hε.1 hε.2
  simpa using h

/-- Direct `norm_sq_empiricalL2Vec` and `dist_sq_empiricalL2Vec` check on `Fin 2`. -/
example :
    let S : Fin 2 → ℝ := fun i => if i = 0 then 0 else 2
    ‖empiricalL2Vec S id‖ ^ 2 = 2 ∧
      dist (empiricalL2Vec S id) (empiricalL2Vec S (fun x => x - 1)) ^ 2 = 1 := by
  intro S
  refine ⟨?_, ?_⟩
  · rw [norm_sq_empiricalL2Vec (by omega)]
    simp [S, Fin.sum_univ_two]
    norm_num
  · rw [dist_sq_empiricalL2Vec (by omega)]
    simp [S]

/-- Covering & packing monotonicity checks (`internalCoveringNumber_anti`, `packingNumber_anti`,
`packingNumber_mono`). -/
example :
    internalCoveringNumber ({0, 1} : Set ℝ) 2 ≤ internalCoveringNumber ({0, 1} : Set ℝ) 1 ∧
    packingNumber ({0, 1} : Set ℝ) 2 ≤ packingNumber ({0, 1} : Set ℝ) 1 ∧
    packingNumber ({0} : Set ℝ) 1 ≤ packingNumber ({0, 1} : Set ℝ) 1 :=
  ⟨internalCoveringNumber_anti _ (by norm_num),
    packingNumber_anti _ (by norm_num),
    packingNumber_mono (by simp) 1⟩

end Cslib.MachineLearning.Tests
