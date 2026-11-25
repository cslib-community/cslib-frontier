/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Normed.CoveringNumber
public import CslibFrontier.MachineLearning.Rademacher.Classification
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import CslibFrontier.MachineLearning.PACLearning.Packing
import CslibFrontier.Probability.BitString.Chaining
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Dudley's entropy integral for Rademacher complexity

`CslibFrontier/Probability/BitString/Chaining.lean` proves the discrete dyadic chaining sum
`Cslib.BitString.expect_ciSup_sum_mul_signVal_le_chaining`, and
`CslibFrontier/MachineLearning/Rademacher/Chaining.lean` applies it to binary VC classes. Here we
turn the dyadic chaining sum into the **continuous Dudley entropy integral**
[Dudley1967; Vershynin2018, Theorem 8.1.3; ShalevShwartzBenDavid2014, Lemma 27.4] in the
empirical `L²(P_m)` metric (`EuclideanSpace ℝ (Fin m)` scaled by `1 / √m`), avoiding the discrete
index-tuple assumption and opening chaining to continuous, real-valued function classes.

For a sample `S : Fin m → Z` (`m > 0`) and `f : Z → ℝ`, the normalized empirical embedding
`empiricalL2Vec S f` satisfies

`dist (empiricalL2Vec S f) (empiricalL2Vec S g) = √((∑ i, (f (S i) - g (S i)) ^ 2) / m)`.

Every class `F : Set (Z → ℝ)` bounded in empirical `L²(P_m)` radius `R` around some center `f₀`
has finite covering numbers `empiricalCoveringNumber F S ε` at every `ε > 0` (since bounded subsets
of `EuclideanSpace ℝ (Fin m)` are totally bounded). Because `ε ↦ √(log N(F, S, ε))` is antitone
and nonnegative on `(0, R]`, it is automatically `IntervalIntegrable` on `[α, R]` for every
`0 < α ≤ R` with no extra measurability or integrability hypothesis. Comparing the dyadic sum at
scales `R / 2 ^ n` with Riemann lower rectangles on `[R / 2 ^ (n + 2), R / 2 ^ (n + 1)]` yields:

* **Truncated Dudley entropy integral** (`empiricalRademacherComplexity_le_dudley_integral`):
  for every `0 < α ≤ R`,
  `R̂_S(F) ≤ 4 α + (16 / √m) ∫ ε in α..R, √(log N_2(F, S, ε))`.
* **Improper `[0, R]` Dudley integral** (`empiricalRademacherComplexity_le_dudley_integral_zero`):
  when `ε ↦ √(log N_2(F, S, ε))` is `IntervalIntegrable` on `0..R`, letting `α → 0⁺` gives
  `R̂_S(F) ≤ (16 / √m) ∫ ε in 0..R, √(log N_2(F, S, ε))`.
* **Polynomial metric entropy bound** (`empiricalRademacherComplexity_le_of_polynomial_covering`):
  via the exact antiderivative of `log (C / ε)` and Cauchy–Schwarz (`√(log (C / ε)) ≤ (t + log (C /
  ε) / t) / 2`), if `N_2(F, S, ε) ≤ (C / ε) ^ d` on `(0, R]` (`0 < R ≤ C`), then
  `R̂_S(F) ≤ 16 R √(d (1 + log (C / R)) / m)` (removing the `log m` factor of Massart's lemma).
* **Real-valued Lipschitz parametric classes** (`empiricalRademacherComplexity_lipschitz_ball_le`,
  `rademacherComplexity_lipschitz_ball_le`, `lipschitz_ball_generalization_bound`): combining
  Dudley's integral with the volumetric closed-ball covering bound `(1 + 2 r / ε) ^ d` of
  `CslibFrontier/Foundations/Analysis/Normed/CoveringNumber.lean` bounds any `L`-Lipschitz
  parameterization `Φ : E → Z → ℝ` on a ball of radius `r` in any finite-dimensional real normed
  space `E` of dimension `d` by `16 L r √(d (1 + log 3) / m)`.
* **VC empirical `L²(P_m)` covering bound** (`empiricalCoveringNumber_bitClass_le_of_vcDim`): links
  the Hamming-distance packing bound of
  `CslibFrontier/MachineLearning/PACLearning/Packing.lean` to `(√8 / ε) ^ (4 d)`.

## Main definitions

* `Cslib.MachineLearning.empiricalL2Vec`: empirical `L²(P_m)` embedding `f ↦ (f (S i) / √m)_i`.
* `Cslib.MachineLearning.empiricalCoveringNumber`: external covering number of `F` in `L²(P_m)`.

## Main results

* `Cslib.MachineLearning.rademacherAverage_le_dudley_integral`: centered truncated Dudley entropy
  integral for an arbitrary vector family `a : ι → Fin m → ℝ`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_dudley_integral`: truncated Dudley
  entropy integral for `empiricalRademacherComplexity F S`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_dudley_integral_zero`: full `[0, R]`
  Dudley entropy integral under `IntervalIntegrable`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_dudley_of_bound`: Dudley integral with an
  antitone upper bound `M` dominating `empiricalCoveringNumber F S`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_of_polynomial_covering`: closed-form
  `16 R √(d (1 + log (C / R)) / m)` bound under polynomial covering `(C / ε) ^ d`.
* `Cslib.MachineLearning.empiricalCoveringNumber_lipschitz_ball_le`: empirical covering bound for
  an `L`-Lipschitz parametric family on a ball of radius `r` in a finite-dimensional normed space.
* `Cslib.MachineLearning.empiricalRademacherComplexity_lipschitz_ball_le`: `O(L r √(d / m))`
  empirical Rademacher bound for `L`-Lipschitz parametric classes.
* `Cslib.MachineLearning.rademacherComplexity_lipschitz_ball_le`: population form on finite `Z`.
* `Cslib.MachineLearning.lipschitz_ball_generalization_bound`: high-probability uniform
  generalization bound for bounded `L`-Lipschitz parametric classes.
* `Cslib.MachineLearning.empiricalCoveringNumber_bitClass_le_of_vcDim`: empirical `L²(P_m)`
  covering bound `(√8 / ε) ^ (4 d)` for VC classes via `card_le_div_pow_of_le_hammingDist`.

## References

* [R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian
  processes*][Dudley1967] (locator unverified)
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.1 and Theorem 8.1.3
  (locators unverified)
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Lemma 27.4 (locator unverified)
-/

public section

open Finset MeasureTheory
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString Cslib.Metric Cslib.MachineLearning.PACLearning

/-! ### Empirical `L²(P_m)` embedding and covering numbers -/

/-- Normalized vector embedding `v ↦ (v i / √m)_i : EuclideanSpace ℝ (Fin m)`. -/
private noncomputable def vecL2 {m : ℕ} (v : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => v i / Real.sqrt m

private theorem norm_sq_vecL2 {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) :
    ‖vecL2 v‖ ^ 2 = (∑ i, v i ^ 2) / m := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecL2, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hm_pos.le,
    ← sum_div]

private theorem dist_sq_vecL2 {m : ℕ} (hm : 0 < m) (u v : Fin m → ℝ) :
    dist (vecL2 u) (vecL2 v) ^ 2 = (∑ i, (u i - v i) ^ 2) / m := by
  have hsub : vecL2 u - vecL2 v = vecL2 (fun i => u i - v i) := by
    ext i
    simp only [vecL2, PiLp.sub_apply, WithLp.ofLp_toLp, sub_div]
  rw [dist_eq_norm, hsub, norm_sq_vecL2 hm]

/-- The normalized **empirical `L²(P_m)` vector** `(f (S 0) / √m, …, f (S (m - 1)) / √m)` inside
`EuclideanSpace ℝ (Fin m)`. Its norm squared is `(∑ i, f (S i) ^ 2) / m` for `m > 0`. -/
@[expose] noncomputable def empiricalL2Vec {Z : Type*} {m : ℕ} (S : Fin m → Z) (f : Z → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => f (S i) / Real.sqrt m

theorem norm_sq_empiricalL2Vec {Z : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (f : Z → ℝ) :
    ‖empiricalL2Vec S f‖ ^ 2 = (∑ i, f (S i) ^ 2) / m :=
  norm_sq_vecL2 hm (fun i => f (S i))

theorem dist_sq_empiricalL2Vec {Z : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → Z)
    (f g : Z → ℝ) :
    dist (empiricalL2Vec S f) (empiricalL2Vec S g) ^ 2 =
      (∑ i, (f (S i) - g (S i)) ^ 2) / m :=
  dist_sq_vecL2 hm (fun i => f (S i)) (fun i => g (S i))

theorem dist_empiricalL2Vec_le_of_abs_sub_le {Z : Type*} {m : ℕ} (S : Fin m → Z)
    {f g : Z → ℝ} {B : ℝ} (hB : 0 ≤ B) (hfg : ∀ i : Fin m, |f (S i) - g (S i)| ≤ B) :
    dist (empiricalL2Vec S f) (empiricalL2Vec S g) ≤ B := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hzero : empiricalL2Vec S f = empiricalL2Vec S g := by ext i; exact i.elim0
    simpa [hzero] using hB
  refine (sq_le_sq₀ dist_nonneg hB).1 ?_
  rw [dist_sq_empiricalL2Vec hm]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [div_le_iff₀ hm_pos]
  calc ∑ i : Fin m, (f (S i) - g (S i)) ^ 2
      ≤ ∑ _i : Fin m, B ^ 2 :=
        sum_le_sum fun i _ => (sq_le_sq₀ (abs_nonneg _) hB).2 (hfg i) |> fun h => by
          simpa only [sq_abs] using h
    _ = B ^ 2 * m := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- The **empirical `L²(P_m)` covering number** `N_2(F, S, ε) : ℕ∞` of a function class
`F : Set (Z → ℝ)` on a sample `S : Fin m → Z` at scale `ε : ℝ`. -/
@[expose] noncomputable def empiricalCoveringNumber {Z : Type*} (F : Set (Z → ℝ)) {m : ℕ}
    (S : Fin m → Z) (ε : ℝ) : ℕ∞ :=
  coveringNumber (empiricalL2Vec S '' F) ε

theorem empiricalCoveringNumber_anti {Z : Type*} (F : Set (Z → ℝ)) {m : ℕ} (S : Fin m → Z)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    empiricalCoveringNumber F S ε₂ ≤ empiricalCoveringNumber F S ε₁ :=
  coveringNumber_anti _ hε

theorem empiricalCoveringNumber_lt_top {Z : Type*} {F : Set (Z → ℝ)} {m : ℕ} {S : Fin m → Z}
    {f₀ : Z → ℝ} {R : ℝ} (hF : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    empiricalCoveringNumber F S ε < ⊤ := by
  have hsub : empiricalL2Vec S '' F ⊆ Metric.closedBall (empiricalL2Vec S f₀) R := by
    rintro _ ⟨f, hf, rfl⟩
    exact Metric.mem_closedBall.2 (hF f hf)
  have htb : TotallyBounded (empiricalL2Vec S '' F) :=
    (isCompact_closedBall (empiricalL2Vec S f₀) R).totallyBounded.subset hsub
  exact coveringNumber_lt_top_of_totallyBounded htb hε

/-! ### Dyadic sum to continuous `intervalIntegral` helpers -/

private theorem antitoneOn_sqrt_log_coveringNumber {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs_tb : TotallyBounded s) (R : ℝ) :
    AntitoneOn (fun ε => Real.sqrt (Real.log (coveringNumber s ε).toNat)) (Set.Ioc 0 R) := by
  intro ε₁ hε₁ ε₂ hε₂ hle
  have hlt₁ : coveringNumber s ε₁ < ⊤ := coveringNumber_lt_top_of_totallyBounded hs_tb hε₁.1
  have hcov : coveringNumber s ε₂ ≤ coveringNumber s ε₁ := coveringNumber_anti s hle
  have hnat : (coveringNumber s ε₂).toNat ≤ (coveringNumber s ε₁).toNat :=
    ENat.toNat_le_of_le_natCast (by simpa [ENat.natCast_toNat hlt₁.ne] using hcov)
  rcases Nat.eq_zero_or_pos (coveringNumber s ε₂).toNat with h0 | hpos
  · simp only [h0, Nat.cast_zero, Real.log_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  · exact Real.sqrt_le_sqrt (Real.log_le_log (Nat.cast_pos.2 hpos) (Nat.cast_le.2 hnat))

private theorem antitoneOn_intervalIntegrable {g : ℝ → ℝ} {a b R : ℝ}
    (hanti : AntitoneOn g (Set.Ioc 0 R)) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    IntervalIntegrable g volume a b := by
  refine AntitoneOn.intervalIntegrable (hanti.mono fun x hx => ?_)
  rw [Set.uIcc_of_le hab] at hx
  exact ⟨lt_of_lt_of_le ha hx.1, hx.2.trans hb⟩

/-- Lower Riemann-sum inequality turning a dyadic sum of an antitone nonnegative function `g` on
`(0, R]` into `4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε`. -/
private theorem sum_dyadic_le_intervalIntegral {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hanti : AntitoneOn g (Set.Ioc 0 R)) (K : ℕ) :
    ∑ n ∈ range K, (R / 2 ^ n) * g (R / 2 ^ (n + 1)) ≤
      4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK_pos : 0 < R / 2 ^ (K + 2) := by positivity
    have hmid_pos : 0 < R / 2 ^ (K + 1) := by positivity
    have ha_le_b : R / 2 ^ (K + 2) ≤ R / 2 ^ (K + 1) :=
      div_le_div_of_nonneg_left hR.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    have hb_le_c : R / 2 ^ (K + 1) ≤ R / 2 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using div_le_div_of_nonneg_left hR.le (by positivity) this
    have hc_le_R : R / 2 ≤ R := by linarith
    have hint_ab : IntervalIntegrable g volume (R / 2 ^ (K + 2)) (R / 2 ^ (K + 1)) :=
      antitoneOn_intervalIntegrable hanti hK_pos ha_le_b (hb_le_c.trans hc_le_R)
    have hint_bc : IntervalIntegrable g volume (R / 2 ^ (K + 1)) (R / 2) :=
      antitoneOn_intervalIntegrable hanti hmid_pos hb_le_c hc_le_R
    have hstep : (R / 2 ^ K) * g (R / 2 ^ (K + 1)) ≤
        4 * ∫ ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g ε := by
      have hwidth : (R / 2 ^ (K + 1) - R / 2 ^ (K + 2)) * 4 = R / 2 ^ K := by
        rw [show (2 : ℝ) ^ (K + 2) = 4 * 2 ^ K by ring,
          show (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K by ring]
        field_simp
        ring
      have hmono : ∫ _ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g (R / 2 ^ (K + 1)) ≤
          ∫ ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g ε := by
        refine intervalIntegral.integral_mono_on ha_le_b intervalIntegrable_const hint_ab
          fun x hx => hanti ⟨lt_of_lt_of_le hK_pos hx.1, hx.2.trans (hb_le_c.trans hc_le_R)⟩
            ⟨hmid_pos, hb_le_c.trans hc_le_R⟩ hx.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      calc (R / 2 ^ K) * g (R / 2 ^ (K + 1))
          = 4 * ((R / 2 ^ (K + 1) - R / 2 ^ (K + 2)) * g (R / 2 ^ (K + 1))) := by
              rw [← hwidth]; ring
        _ ≤ 4 * ∫ ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g ε :=
              mul_le_mul_of_nonneg_left hmono (by norm_num)
    rw [sum_range_succ]
    calc ∑ n ∈ range K, R / 2 ^ n * g (R / 2 ^ (n + 1)) + R / 2 ^ K * g (R / 2 ^ (K + 1))
        ≤ 4 * (∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε) +
            4 * (∫ ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g ε) :=
          add_le_add ih hstep
      _ = 4 * ((∫ ε in (R / 2 ^ (K + 2))..(R / 2 ^ (K + 1)), g ε) +
            (∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε)) := by ring
      _ = 4 * ∫ ε in (R / 2 ^ (K + 2))..(R / 2), g ε := by
          rw [intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc]

/-- Pick a dyadic truncation depth `K` for `0 < α ≤ R / 2` with `α ≤ R / 2 ^ (K + 1)` and
`R / 2 ^ K < 4 * α`. -/
private theorem exists_dyadic_cutoff {α R : ℝ} (hα : 0 < α) (hαR : α ≤ R / 2) :
    ∃ K : ℕ, α ≤ R / 2 ^ (K + 1) ∧ R / 2 ^ K < 4 * α := by
  classical
  have hex : ∃ k : ℕ, R / 2 ^ (k + 2) < α := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / α) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, ?_⟩
    have hpow : (2 : ℝ) ^ k ≤ 2 ^ (k + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ (by positivity)]
    have h1 : R < α * 2 ^ k := by rwa [div_lt_iff₀ hα, mul_comm] at hk
    have h2 : α * 2 ^ k ≤ α * 2 ^ (k + 2) := mul_le_mul_of_nonneg_left hpow hα.le
    linarith
  let K := Nat.find hex
  refine ⟨K, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos K with h0 | hpos
    · simpa [h0] using hαR
    · have hmin : ¬ R / 2 ^ ((K - 1) + 2) < α :=
        Nat.find_min hex (by omega : K - 1 < K)
      rw [show K - 1 + 2 = K + 1 by omega] at hmin
      exact le_of_not_gt hmin
  · have hspec : R / 2 ^ (K + 2) < α := Nat.find_spec hex
    have hpow : R / (2 : ℝ) ^ (K + 2) = (R / 2 ^ K) / 4 := by
      rw [show (2 : ℝ) ^ (K + 2) = 2 ^ K * 4 by ring, ← div_div]
    rw [hpow] at hspec
    linarith

private theorem intervalIntegrable_sqrt_log_div {α R C : ℝ} (hα : 0 < α) (hαR : α ≤ R)
    (hC : 0 < C) :
    IntervalIntegrable (fun ε => Real.sqrt (Real.log (C / ε))) volume α R := by
  refine antitoneOn_intervalIntegrable ?_ hα hαR le_rfl
  intro x hx y hy hxy
  exact Real.sqrt_le_sqrt
    (Real.log_le_log (div_pos hC hy.1) (div_le_div_of_nonneg_left hC.le hx.1 hxy))

/-- Elementary Cauchy–Schwarz upper bound for the polynomial metric-entropy integral:
`∫ x in α..R, √(log (C / x)) ≤ R √(1 + log (C / R))` for `0 < α ≤ R ≤ C`. -/
private theorem intervalIntegral_sqrt_log_div_le {α R C : ℝ} (hα : 0 < α) (hαR : α ≤ R)
    (hRC : R ≤ C) :
    ∫ x in α..R, Real.sqrt (Real.log (C / x)) ≤ R * Real.sqrt (1 + Real.log (C / R)) := by
  have hR : 0 < R := lt_of_lt_of_le hα hαR
  have hC : 0 < C := lt_of_lt_of_le hR hRC
  have hlogR_nonneg : 0 ≤ Real.log (C / R) :=
    Real.log_nonneg ((one_le_div hR).2 hRC)
  have ht_pos : 0 < Real.sqrt (1 + Real.log (C / R)) :=
    Real.sqrt_pos.2 (by linarith)
  set t := Real.sqrt (1 + Real.log (C / R))
  have ht_sq : t ^ 2 = 1 + Real.log (C / R) := Real.sq_sqrt (by linarith)
  -- `∫ x in α..R, log (C / x) = R (log (C / R) + 1) - α (log (C / α) + 1)`.
  have hlog_eq : ∫ x in α..R, Real.log (C / x) =
      R * (Real.log (C / R) + 1) - α * (Real.log (C / α) + 1) := by
    let F : ℝ → ℝ := fun x => x * Real.log C - x * Real.log x + x
    have hF_eq (x : ℝ) (hx : 0 < x) : F x = x * (Real.log (C / x) + 1) := by
      simp only [F, Real.log_div hC.ne' hx.ne']
      ring
    have hderiv : ∀ x ∈ Set.uIcc α R, HasDerivAt F (Real.log (C / x)) x := by
      intro x hx
      rw [Set.uIcc_of_le hαR] at hx
      have hxpos : 0 < x := lt_of_lt_of_le hα hx.1
      have h1 : HasDerivAt (fun y : ℝ => y * Real.log C) (1 * Real.log C) x :=
        (hasDerivAt_id x).mul_const _
      have h2 : HasDerivAt (fun y : ℝ => y * Real.log y) (1 * Real.log x + x * x⁻¹) x :=
        (hasDerivAt_id x).mul (Real.hasDerivAt_log hxpos.ne')
      have h3 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have hcomb := (h1.sub h2).add h3
      convert hcomb using 1
      rw [Real.log_div hC.ne' hxpos.ne', mul_inv_cancel₀ hxpos.ne']
      ring
    have hcont : ContinuousOn (fun x => Real.log (C / x)) (Set.uIcc α R) := by
      rw [Set.uIcc_of_le hαR]
      refine ContinuousOn.log
        (continuousOn_const.div continuousOn_id fun y (hy : y ∈ Set.Icc α R) =>
          (lt_of_lt_of_le hα hy.1).ne')
        fun y (hy : y ∈ Set.Icc α R) => div_ne_zero hC.ne' (lt_of_lt_of_le hα hy.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable),
      hF_eq R hR, hF_eq α hα]
  have hlog_le : ∫ x in α..R, Real.log (C / x) ≤ R * (1 + Real.log (C / R)) := by
    have hlogα : 0 ≤ Real.log (C / α) :=
      Real.log_nonneg ((one_le_div hα).2 (hαR.trans hRC))
    rw [hlog_eq]
    nlinarith
  have hint_log : IntervalIntegrable (fun x => Real.log (C / x)) volume α R := by
    refine antitoneOn_intervalIntegrable ?_ hα hαR le_rfl
    intro x hx y hy hxy
    exact Real.log_le_log (div_pos hC hy.1) (div_le_div_of_nonneg_left hC.le hx.1 hxy)
  have hint_sqrt : IntervalIntegrable (fun x => Real.sqrt (Real.log (C / x))) volume α R :=
    intervalIntegrable_sqrt_log_div hα hαR hC
  have hint_rhs : IntervalIntegrable (fun x => (t + Real.log (C / x) / t) / 2) volume α R :=
    (intervalIntegrable_const.add (hint_log.div_const t)).div_const 2
  have hpt : ∀ x ∈ Set.Icc α R,
      Real.sqrt (Real.log (C / x)) ≤ (t + Real.log (C / x) / t) / 2 := by
    intro x hx
    have hlogx : 0 ≤ Real.log (C / x) :=
      Real.log_nonneg ((one_le_div (lt_of_lt_of_le hα hx.1)).2 (hx.2.trans hRC))
    have hsq := sq_nonneg (t - Real.sqrt (Real.log (C / x)))
    have h1 : 2 * t * Real.sqrt (Real.log (C / x)) ≤ t ^ 2 + Real.log (C / x) := by
      nlinarith [Real.sq_sqrt hlogx]
    have hmul : Real.sqrt (Real.log (C / x)) * 2 ≤ t + Real.log (C / x) / t := by
      refine le_of_mul_le_mul_left ?_ ht_pos
      calc t * (Real.sqrt (Real.log (C / x)) * 2)
          = 2 * t * Real.sqrt (Real.log (C / x)) := by ring
        _ ≤ t ^ 2 + Real.log (C / x) := h1
        _ = t * (t + Real.log (C / x) / t) := by
            have htne : t ≠ 0 := ht_pos.ne'
            field_simp
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 hmul
  calc ∫ x in α..R, Real.sqrt (Real.log (C / x))
      ≤ ∫ x in α..R, (t + Real.log (C / x) / t) / 2 :=
        intervalIntegral.integral_mono_on hαR hint_sqrt hint_rhs hpt
    _ = ((∫ _x in α..R, t) + (∫ x in α..R, Real.log (C / x)) / t) / 2 := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_add intervalIntegrable_const (hint_log.div_const t),
          intervalIntegral.integral_div]
    _ = ((R - α) * t + (∫ x in α..R, Real.log (C / x)) / t) / 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ (R * t + R * (1 + Real.log (C / R)) / t) / 2 := by
        gcongr
        linarith
    _ = R * t := by
        rw [← ht_sq]
        field_simp
        ring

/-! ### Dudley's continuous entropy integral -/

/-- **Truncated Dudley entropy integral for a family of vectors** [Dudley1967; Vershynin2018,
Theorem 8.1.3; ShalevShwartzBenDavid2014, Lemma 27.4] (locators unverified). For any family
`a : ι → Fin m → ℝ` (`m > 0`) lying in an empirical `L²(P_m)` ball of radius `R` around a center
`c₀ : Fin m → ℝ`, and every truncation level `α ∈ (0, R]`,

`rademacherAverage a ≤ 4 α + (16 / √m) ∫ ε in α..R, √(log N_2(range a, ε))`.

The antitone integrand is automatically `IntervalIntegrable` on `[α, R]`; no finiteness of `ι`
or integrability hypothesis is needed. -/
theorem rademacherAverage_le_dudley_integral {ι : Type*} {m : ℕ} (hm : 0 < m)
    (a : ι → Fin m → ℝ) (c₀ : Fin m → ℝ) {R α : ℝ} (hα : 0 < α) (hαR : α ≤ R)
    (ha : ∀ j, (∑ i, (a j i - c₀ i) ^ 2) / m ≤ R ^ 2) :
    rademacherAverage a ≤
      4 * α + 16 / Real.sqrt m *
        ∫ ε in α..R,
          Real.sqrt (Real.log
            (coveringNumber
              (Set.range fun j => WithLp.toLp 2 fun i => a j i / Real.sqrt m) ε).toNat) := by
  classical
  have hR : 0 < R := lt_of_lt_of_le hα hαR
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm_pos
  let A : Set (EuclideanSpace ℝ (Fin m)) := Set.range fun j => vecL2 (a j)
  let g : ℝ → ℝ := fun ε => Real.sqrt (Real.log (coveringNumber A ε).toNat)
  have hAtb : TotallyBounded A := by
    have hsub : A ⊆ Metric.closedBall (vecL2 c₀) R := by
      rintro _ ⟨j, rfl⟩
      refine Metric.mem_closedBall.2 ((sq_le_sq₀ dist_nonneg hR.le).1 ?_)
      rw [dist_sq_vecL2 hm]
      exact ha j
    exact (isCompact_closedBall (vecL2 c₀) R).totallyBounded.subset hsub
  have hg_nonneg (ε : ℝ) : 0 ≤ g ε := Real.sqrt_nonneg _
  have hg_anti : AntitoneOn g (Set.Ioc 0 R) := antitoneOn_sqrt_log_coveringNumber hAtb R
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [rademacherAverage_of_isEmpty]
    have hint_nn : 0 ≤ ∫ ε in α..R, g ε :=
      intervalIntegral.integral_nonneg hαR fun x _ => hg_nonneg x
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) hint_nn)
  -- Center `a` around `c₀`; shifting leaves both `rademacherAverage` and `coveringNumber` equal.
  let a' : ι → Fin m → ℝ := fun j i => a j i - c₀ i
  have ha'_sq (j : ι) : ∑ i, a' j i ^ 2 ≤ (R * Real.sqrt m) ^ 2 := by
    calc ∑ i, a' j i ^ 2 = (∑ i, (a j i - c₀ i) ^ 2) / m * m := by
          rw [div_mul_cancel₀ _ hm_pos.ne']
      _ ≤ R ^ 2 * m := mul_le_mul_of_nonneg_right (ha j) hm_pos.le
      _ = (R * Real.sqrt m) ^ 2 := by rw [mul_pow, Real.sq_sqrt hm_pos.le]
  have ha'_abs (j : ι) (i : Fin m) : |a' j i| ≤ R * Real.sqrt m := by
    refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs]
    calc a' j i ^ 2 ≤ ∑ k : Fin m, a' j k ^ 2 :=
          single_le_sum (fun k _ => sq_nonneg (a' j k)) (mem_univ i)
      _ ≤ (R * Real.sqrt m) ^ 2 := ha'_sq j
  have hshift : rademacherAverage a = rademacherAverage a' := by
    have heq : a = fun j i => c₀ i + 1 * (signVal false * a' j i) := by
      funext j i
      simp only [a', signVal, one_mul]
      norm_num
    calc rademacherAverage a
        = rademacherAverage (fun j i => c₀ i + 1 * (signVal false * a' j i)) := by rw [← heq]
      _ = 1 * rademacherAverage a' :=
          rademacherAverage_add_mul_signVal_mul ha'_abs c₀ (fun _ => false) zero_le_one
      _ = rademacherAverage a' := one_mul _
  let A' : Set (EuclideanSpace ℝ (Fin m)) := Set.range fun j => vecL2 (a' j)
  have hA_eq : A = (fun x => x + vecL2 c₀) '' A' := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨vecL2 (a' j), ⟨j, rfl⟩, ?_⟩
      ext i
      simp only [vecL2, a', PiLp.add_apply, WithLp.ofLp_toLp, ← add_div, sub_add_cancel]
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      ext i
      simp only [vecL2, a', PiLp.add_apply, WithLp.ofLp_toLp, ← add_div, sub_add_cancel]
  have hcov_eq (ε : ℝ) : coveringNumber A' ε = coveringNumber A ε := by
    rw [hA_eq, coveringNumber_vadd]
  have hA'_ne : A'.Nonempty := ⟨vecL2 (a' (Classical.arbitrary ι)), Classical.arbitrary ι, rfl⟩
  -- Build the finite covering sequence `T : ℕ → Finset (Fin m → ℝ)` at dyadic scales `R / 2 ^ n`.
  have hnet (n : ℕ) : ∃ C : Finset (EuclideanSpace ℝ (Fin m)),
      (C.card : ℕ∞) = coveringNumber A (R / 2 ^ n) ∧
        ∀ x ∈ A', ∃ u ∈ C, dist x u ≤ R / 2 ^ n := by
    have hlt : coveringNumber A' (R / 2 ^ n) < ⊤ := by
      rw [hcov_eq]
      exact coveringNumber_lt_top_of_totallyBounded hAtb (by positivity)
    obtain ⟨C, hcard, hcov⟩ := exists_cover_of_coveringNumber_lt_top hlt
    exact ⟨C, hcov_eq _ ▸ hcard, hcov⟩
  choose C hC_card hC_cov using hnet
  let T : ℕ → Finset (Fin m → ℝ) := fun n =>
    if n = 0 then {0}
    else (C n).image fun u i => u i * Real.sqrt m
  have hT_cov : ∀ n j, ∃ u ∈ T n,
      ∑ i, (a' j i - u i) ^ 2 ≤ (R * Real.sqrt m / 2 ^ n) ^ 2 := by
    intro n j
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, by simp [T], ?_⟩
      simpa only [Pi.zero_apply, sub_zero, pow_zero, div_one] using ha'_sq j
    · obtain ⟨u, huC, hdu⟩ := hC_cov n (vecL2 (a' j)) ⟨j, rfl⟩
      have hmem : (fun i => u i * Real.sqrt m) ∈ T n := by
        simp only [T, ite_eq_right_iff.2 fun h => (hn.ne' h).elim]
        exact mem_image_of_mem _ huC
      refine ⟨fun i => u i * Real.sqrt m, hmem, ?_⟩
      have hdist_sq : dist (vecL2 (a' j)) u ^ 2 =
          (∑ i, (a' j i - u i * Real.sqrt m) ^ 2) / m := by
        rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
        simp only [PiLp.sub_apply, vecL2, Real.norm_eq_abs, sq_abs]
        have hterm (i : Fin m) : (a' j i / Real.sqrt m - u i) ^ 2 =
            (a' j i - u i * Real.sqrt m) ^ 2 / m := by
          have : a' j i / Real.sqrt m - u i = (a' j i - u i * Real.sqrt m) / Real.sqrt m := by
            field_simp
          rw [this, div_pow, Real.sq_sqrt hm_pos.le]
        rw [sum_congr rfl fun i _ => hterm i, ← sum_div]
      have hbound : dist (vecL2 (a' j)) u ^ 2 ≤ (R / 2 ^ n) ^ 2 :=
        (sq_le_sq₀ dist_nonneg (by positivity)).2 hdu
      rw [hdist_sq, div_le_iff₀ hm_pos] at hbound
      refine hbound.trans_eq ?_
      rw [div_pow, div_pow, mul_pow, Real.sq_sqrt hm_pos.le]
      ring
  have hT_ne (n : ℕ) : (T n).Nonempty := by
    obtain ⟨u, hu, -⟩ := hT_cov n (Classical.arbitrary ι)
    exact ⟨u, hu⟩
  have hT0_card : (T 0).card = 1 := by simp [T]
  have hT_card_le (n : ℕ) : (T (n + 1)).card ≤ (coveringNumber A (R / 2 ^ (n + 1))).toNat := by
    have h1 : (T (n + 1)).card ≤ (C (n + 1)).card := by
      simp only [T, Nat.succ_ne_zero, ↓reduceIte]
      exact card_image_le
    exact h1.trans_eq (by rw [← hC_card (n + 1), ENat.toNat_natCast])
  have hTn_card_le (n : ℕ) : (T n).card ≤ (coveringNumber A (R / 2 ^ (n + 1))).toNat := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0_card]
      have hlt : coveringNumber A (R / 2 ^ 1) < ⊤ :=
        coveringNumber_lt_top_of_totallyBounded hAtb (by positivity)
      have h1 : 1 ≤ coveringNumber A (R / 2 ^ 1) := by
        rw [← hcov_eq]
        exact one_le_coveringNumber hA'_ne _
      exact_mod_cast (ENat.natCast_toNat hlt.ne).symm ▸ h1
    · have hle_scale : R / 2 ^ (n + 1) ≤ R / 2 ^ n :=
        div_le_div_of_nonneg_left hR.le (by positivity)
          (pow_le_pow_right₀ (by norm_num) (by omega))
      have hlt : coveringNumber A (R / 2 ^ (n + 1)) < ⊤ :=
        coveringNumber_lt_top_of_totallyBounded hAtb (by positivity)
      have hmono : coveringNumber A (R / 2 ^ n) ≤ coveringNumber A (R / 2 ^ (n + 1)) :=
        coveringNumber_anti A hle_scale
      have hnat : (C n).card ≤ (coveringNumber A (R / 2 ^ (n + 1))).toNat := by
        exact_mod_cast (hC_card n).symm ▸ hmono.trans_eq (ENat.natCast_toNat hlt.ne).symm
      have hsub : (T n).card ≤ (C n).card := by
        simp only [T, ite_eq_right_iff.2 fun h => (hn.ne' h).elim]
        exact card_image_le
      exact hsub.trans hnat
  -- Split between `α ≤ R / 2` (apply chaining at cutoff `K`) and `R / 2 < α ≤ R` (`K = 0`).
  rcases le_or_gt α (R / 2) with hα_half | hα_big
  · obtain ⟨K, hα_le, hK_lt⟩ := exists_dyadic_cutoff hα hα_half
    have hch := expect_ciSup_sum_mul_signVal_le_chaining a' (by positivity) ha'_sq T hT_cov K
    simp only [hT0_card, Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, zero_add,
      Fintype.card_fin] at hch
    have hrad : rademacherAverage a' ≤
        (∑ n ∈ range K, 2 * (R * Real.sqrt m) / 2 ^ n *
          Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card)) +
          R * Real.sqrt m / 2 ^ K * Real.sqrt m) / m := by
      rw [rademacherAverage_eq_expect_ciSup_sum_div]
      exact div_le_div_of_nonneg_right hch hm_pos.le
    have hsum_term (n : ℕ) :
        2 * (R * Real.sqrt m) / 2 ^ n *
            Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card)) ≤
          4 * Real.sqrt m * ((R / 2 ^ n) * g (R / 2 ^ (n + 1))) := by
      have hpos_prod : (0 : ℝ) < (T (n + 1)).card * (T n).card := by
        have h1 : 0 < (T (n + 1)).card := (hT_ne (n + 1)).card_pos
        have h2 : 0 < (T n).card := (hT_ne n).card_pos
        positivity
      set N := (coveringNumber A (R / 2 ^ (n + 1))).toNat
      have hprod_le : ((T (n + 1)).card : ℝ) * (T n).card ≤ (N : ℝ) ^ 2 := by
        rw [sq]
        exact mul_le_mul (Nat.cast_le.2 (hT_card_le n)) (Nat.cast_le.2 (hTn_card_le n))
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hlog : Real.log ((T (n + 1)).card * (T n).card) ≤ 2 * Real.log N := by
        calc Real.log ((T (n + 1)).card * (T n).card)
            ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hpos_prod hprod_le
          _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
      have hsqrt : Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card)) ≤
          2 * Real.sqrt (Real.log N) := by
        calc Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card))
            ≤ Real.sqrt (4 * Real.log N) := Real.sqrt_le_sqrt (by linarith)
          _ = 2 * Real.sqrt (Real.log N) := by
              rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]
      calc 2 * (R * Real.sqrt m) / 2 ^ n *
              Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card))
          ≤ 2 * (R * Real.sqrt m) / 2 ^ n * (2 * Real.sqrt (Real.log N)) :=
            mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = 4 * Real.sqrt m * ((R / 2 ^ n) * g (R / 2 ^ (n + 1))) := by ring
    have hsum_le : (∑ n ∈ range K, 2 * (R * Real.sqrt m) / 2 ^ n *
          Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card))) ≤
        4 * Real.sqrt m * (4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε) := by
      calc _ ≤ ∑ n ∈ range K, 4 * Real.sqrt m * ((R / 2 ^ n) * g (R / 2 ^ (n + 1))) :=
            sum_le_sum fun n _ => hsum_term n
        _ = 4 * Real.sqrt m * ∑ n ∈ range K, (R / 2 ^ n) * g (R / 2 ^ (n + 1)) := by
            rw [← mul_sum]
        _ ≤ 4 * Real.sqrt m * (4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε) :=
            mul_le_mul_of_nonneg_left (sum_dyadic_le_intervalIntegral hR hg_anti K) (by positivity)
    have hint_sub : ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε ≤ ∫ ε in α..R, g ε := by
      have hmid_le : R / 2 ^ (K + 1) ≤ R / 2 := by
        have : (2 : ℝ) ^ 1 ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        simpa using div_le_div_of_nonneg_left hR.le (by positivity) this
      have hint_low : IntervalIntegrable g volume α (R / 2 ^ (K + 1)) :=
        antitoneOn_intervalIntegrable hg_anti hα hα_le (hmid_le.trans (by linarith))
      have hint_mid : IntervalIntegrable g volume (R / 2 ^ (K + 1)) (R / 2) :=
        antitoneOn_intervalIntegrable hg_anti (by positivity) hmid_le (by linarith)
      have hint_hi : IntervalIntegrable g volume (R / 2) R :=
        antitoneOn_intervalIntegrable hg_anti (by positivity) (by linarith) le_rfl
      have h1 : 0 ≤ ∫ ε in α..(R / 2 ^ (K + 1)), g ε :=
        intervalIntegral.integral_nonneg hα_le fun x _ => hg_nonneg x
      have h2 : 0 ≤ ∫ ε in (R / 2)..R, g ε :=
        intervalIntegral.integral_nonneg (by linarith) fun x _ => hg_nonneg x
      have hsplit : ∫ ε in α..R, g ε =
          (∫ ε in α..(R / 2 ^ (K + 1)), g ε) +
            (∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε) +
              (∫ ε in (R / 2)..R, g ε) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hint_low hint_mid,
          intervalIntegral.integral_add_adjacent_intervals (hint_low.trans hint_mid) hint_hi]
      linarith
    have hsqrt_div : Real.sqrt m / (m : ℝ) = 1 / Real.sqrt m := by
      have hm_eq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm_pos.le
      rw [div_eq_div_iff hm_pos.ne' hsqrtm_pos.ne', one_mul, hm_eq]
    have hres_eq : R * Real.sqrt m / 2 ^ K * Real.sqrt m / m = R / 2 ^ K := by
      have hm_eq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm_pos.le
      calc R * Real.sqrt m / 2 ^ K * Real.sqrt m / m
          = R / 2 ^ K * (Real.sqrt m * Real.sqrt m / m) := by ring
        _ = R / 2 ^ K := by rw [hm_eq, div_self hm_pos.ne', mul_one]
    rw [hshift]
    calc rademacherAverage a'
        ≤ (∑ n ∈ range K, 2 * (R * Real.sqrt m) / 2 ^ n *
              Real.sqrt (2 * Real.log ((T (n + 1)).card * (T n).card))) / m +
            R * Real.sqrt m / 2 ^ K * Real.sqrt m / m := by
          simpa only [add_div] using hrad
      _ ≤ (4 * Real.sqrt m * (4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε)) / m +
            R / 2 ^ K := by
          rw [hres_eq]
          gcongr
      _ = R / 2 ^ K + 16 / Real.sqrt m * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε := by
          have : 4 * Real.sqrt m * (4 * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε) / m =
              16 * (Real.sqrt m / m) * ∫ ε in (R / 2 ^ (K + 1))..(R / 2), g ε := by ring
          rw [this, hsqrt_div]
          ring
      _ ≤ 4 * α + 16 / Real.sqrt m * ∫ ε in α..R, g ε := by
          exact add_le_add hK_lt.le (mul_le_mul_of_nonneg_left hint_sub (by positivity))
  · -- When `R / 2 < α ≤ R`, `K = 0` already yields `rademacherAverage a' ≤ R ≤ 4 α`.
    have hch := expect_ciSup_sum_mul_signVal_le_chaining a' (by positivity) ha'_sq T hT_cov 0
    simp only [hT0_card, Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, zero_add,
      range_zero, sum_empty, add_zero, pow_zero, div_one, Fintype.card_fin] at hch
    have hres : rademacherAverage a' ≤ R := by
      rw [rademacherAverage_eq_expect_ciSup_sum_div]
      refine (div_le_div_of_nonneg_right hch hm_pos.le).trans_eq ?_
      rw [mul_assoc, Real.mul_self_sqrt hm_pos.le, mul_div_cancel_right₀ _ hm_pos.ne']
    have hint_nn : 0 ≤ ∫ ε in α..R, g ε :=
      intervalIntegral.integral_nonneg hαR fun x _ => hg_nonneg x
    rw [hshift]
    calc rademacherAverage a'
        ≤ R := hres
      _ ≤ 4 * α := by linarith
      _ ≤ 4 * α + 16 / Real.sqrt m * (∫ ε in α..R, g ε) :=
          le_add_of_nonneg_right (mul_nonneg (by positivity) hint_nn)

/-- **Truncated Dudley entropy integral for `empiricalRademacherComplexity`** [Dudley1967;
Vershynin2018, Theorem 8.1.3] (locators unverified). For any class `F : Set (Z → ℝ)` lying within
empirical `L²(P_m)` distance `R` of a center `f₀ : Z → ℝ` on `S : Fin m → Z` (`m > 0`), and every
`α ∈ (0, R]`:

`empiricalRademacherComplexity F S ≤ 4 α + (16 / √m) ∫ ε in α..R, √(log N_2(F, S, ε))`. -/
theorem empiricalRademacherComplexity_le_dudley_integral {Z : Type*} {F : Set (Z → ℝ)}
    {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (f₀ : Z → ℝ) {R α : ℝ} (hα : 0 < α) (hαR : α ≤ R)
    (hF : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ R) :
    empiricalRademacherComplexity F S ≤
      4 * α + 16 / Real.sqrt m *
        ∫ ε in α..R, Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat) := by
  have hR : 0 ≤ R := hα.le.trans hαR
  have ha : ∀ f : F, (∑ i, ((f : Z → ℝ) (S i) - f₀ (S i)) ^ 2) / m ≤ R ^ 2 := by
    intro f
    rw [← dist_sq_empiricalL2Vec hm S f f₀]
    exact (sq_le_sq₀ dist_nonneg hR).2 (hF f f.2)
  have hrange : (Set.range fun f : F => WithLp.toLp 2 fun i => (f : Z → ℝ) (S i) / Real.sqrt m) =
      empiricalL2Vec S '' F := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
    rfl
  rw [empiricalRademacherComplexity_def]
  have h := rademacherAverage_le_dudley_integral hm
    (fun (f : F) i => (f : Z → ℝ) (S i)) (fun i => f₀ (S i)) hα hαR ha
  simpa only [hrange, empiricalCoveringNumber] using h

/-- **Full `[0, R]` Dudley entropy integral** [Dudley1967; Vershynin2018, Theorem 8.1.3]
(locators unverified): when the metric entropy integrand `ε ↦ √(log N_2(F, S, ε))` is
`IntervalIntegrable` on `0..R`, sending `α → 0⁺` removes the residual term `4 α`. -/
theorem empiricalRademacherComplexity_le_dudley_integral_zero {Z : Type*} {F : Set (Z → ℝ)}
    {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (f₀ : Z → ℝ) {R : ℝ} (hR : 0 < R)
    (hF : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ R)
    (hint : IntervalIntegrable
      (fun ε => Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat)) volume 0 R) :
    empiricalRademacherComplexity F S ≤
      16 / Real.sqrt m *
        ∫ ε in (0 : ℝ)..R, Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat) := by
  let g : ℝ → ℝ := fun ε => Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set α := min (δ / 4) R
  have hα_pos : 0 < α := lt_min (by positivity) hR
  have hαR : α ≤ R := min_le_right _ _
  have h4α : 4 * α ≤ δ := by
    have : α ≤ δ / 4 := min_le_left _ _
    linarith
  have h0α : 0 ≤ α := hα_pos.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.2 (Or.inl ⟨h0α, hαR⟩))))
    (hint.mono_set (Set.uIcc_subset_uIcc_right (Set.mem_uIcc.2 (Or.inl ⟨h0α, hαR⟩))))
  have hnonneg : 0 ≤ ∫ ε in (0 : ℝ)..α, g ε :=
    intervalIntegral.integral_nonneg h0α fun _ _ => Real.sqrt_nonneg _
  have hint_mono : ∫ ε in α..R, g ε ≤ ∫ ε in (0 : ℝ)..R, g ε := by
    change (∫ ε in (0 : ℝ)..α, g ε) + ∫ ε in α..R, g ε = ∫ ε in (0 : ℝ)..R, g ε at hsplit
    linarith
  calc empiricalRademacherComplexity F S
      ≤ 4 * α + 16 / Real.sqrt m * (∫ ε in α..R, g ε) :=
        empiricalRademacherComplexity_le_dudley_integral hm S f₀ hα_pos hαR hF
    _ ≤ δ + 16 / Real.sqrt m * (∫ ε in (0 : ℝ)..R, g ε) :=
        add_le_add h4α (mul_le_mul_of_nonneg_left hint_mono (by positivity))
    _ = 16 / Real.sqrt m * (∫ ε in (0 : ℝ)..R, g ε) + δ := add_comm _ _

/-- **Truncated Dudley entropy integral with an antitone upper bound `M` on the covering numbers**
(handles arbitrary non-negative real-valued majorants `M : ℝ → ℝ`). -/
theorem empiricalRademacherComplexity_le_dudley_of_bound {Z : Type*} {F : Set (Z → ℝ)}
    {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (f₀ : Z → ℝ) {R α : ℝ} (hα : 0 < α) (hαR : α ≤ R)
    (hF : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ R)
    {M : ℝ → ℝ} (hM_int : IntervalIntegrable (fun ε => Real.sqrt (Real.log (M ε))) volume α R)
    (hM : ∀ ε ∈ Set.Icc α R, ((empiricalCoveringNumber F S ε).toNat : ℝ) ≤ M ε) :
    empiricalRademacherComplexity F S ≤
      4 * α + 16 / Real.sqrt m * ∫ ε in α..R, Real.sqrt (Real.log (M ε)) := by
  have hsub : empiricalL2Vec S '' F ⊆ Metric.closedBall (empiricalL2Vec S f₀) R := by
    rintro _ ⟨f, hf, rfl⟩
    exact Metric.mem_closedBall.2 (hF f hf)
  have htb : TotallyBounded (empiricalL2Vec S '' F) :=
    (isCompact_closedBall (empiricalL2Vec S f₀) R).totallyBounded.subset hsub
  have hint_emp : IntervalIntegrable
      (fun ε => Real.sqrt (Real.log (empiricalCoveringNumber F S ε).toNat)) volume α R :=
    antitoneOn_intervalIntegrable (antitoneOn_sqrt_log_coveringNumber htb R) hα hαR le_rfl
  refine (empiricalRademacherComplexity_le_dudley_integral hm S f₀ hα hαR hF).trans ?_
  gcongr
  refine intervalIntegral.integral_mono_on hαR hint_emp hM_int fun ε hε => ?_
  rcases Nat.eq_zero_or_pos (empiricalCoveringNumber F S ε).toNat with h0 | hpos
  · simp only [h0, Nat.cast_zero, Real.log_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  · exact Real.sqrt_le_sqrt (Real.log_le_log (Nat.cast_pos.2 hpos) (hM ε hε))

/-! ### Polynomial covering numbers: removing the `log m` factor -/

/-- **Dudley bound for polynomial covering numbers**: if `F` lies in an empirical `L²(P_m)` ball
of radius `R` around `f₀` and satisfies `N_2(F, S, ε) ≤ (C / ε) ^ d` for all `ε ∈ (0, R]` with
`0 < R ≤ C`, then

`empiricalRademacherComplexity F S ≤ 16 * R * √(d * (1 + log (C / R)) / m)`.

Valid for every `d : ℕ` (including `d = 0`, giving `0`). No `log m` factor appears. -/
theorem empiricalRademacherComplexity_le_of_polynomial_covering {Z : Type*} {F : Set (Z → ℝ)}
    {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (f₀ : Z → ℝ) {R C : ℝ} {d : ℕ}
    (hR : 0 < R) (hRC : R ≤ C)
    (hF : ∀ f ∈ F, dist (empiricalL2Vec S f) (empiricalL2Vec S f₀) ≤ R)
    (hcov : ∀ ε ∈ Set.Ioc 0 R, ((empiricalCoveringNumber F S ε).toNat : ℝ) ≤ (C / ε) ^ d) :
    empiricalRademacherComplexity F S ≤
      16 * R * Real.sqrt (d * (1 + Real.log (C / R)) / m) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hC_pos : 0 < C := lt_of_lt_of_le hR hRC
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set α := min (δ / 4) R
  have hα_pos : 0 < α := lt_min (by positivity) hR
  have hαR : α ≤ R := min_le_right _ _
  have h4α : 4 * α ≤ δ := by
    have : α ≤ δ / 4 := min_le_left _ _
    linarith
  have hM_eq (ε : ℝ) (hε : 0 < ε) :
      Real.sqrt (Real.log ((C / ε) ^ d)) = Real.sqrt d * Real.sqrt (Real.log (C / ε)) := by
    rw [Real.log_pow, Real.sqrt_mul (Nat.cast_nonneg d)]
  have hint_sqrt : IntervalIntegrable (fun ε => Real.sqrt (Real.log (C / ε))) volume α R :=
    intervalIntegrable_sqrt_log_div hα_pos hαR hC_pos
  have hint_M : IntervalIntegrable
      (fun ε => Real.sqrt (Real.log ((C / ε) ^ d))) volume α R := by
    refine (hint_sqrt.const_mul (Real.sqrt d)).congr ?_
    intro ε hε
    rw [Set.uIoc_of_le hαR] at hε
    exact (hM_eq ε (lt_trans hα_pos hε.1)).symm
  have hdud := empiricalRademacherComplexity_le_dudley_of_bound hm S f₀ hα_pos hαR hF hint_M
    fun ε hε => hcov ε ⟨lt_of_lt_of_le hα_pos hε.1, hε.2⟩
  have hint_eval : ∫ ε in α..R, Real.sqrt (Real.log ((C / ε) ^ d)) =
      Real.sqrt d * ∫ ε in α..R, Real.sqrt (Real.log (C / ε)) := by
    have hcongr : ∫ ε in α..R, Real.sqrt (Real.log ((C / ε) ^ d)) =
        ∫ ε in α..R, Real.sqrt d * Real.sqrt (Real.log (C / ε)) :=
      intervalIntegral.integral_congr fun ε hε => by
        rw [Set.uIcc_of_le hαR] at hε
        exact hM_eq ε (lt_of_lt_of_le hα_pos hε.1)
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hbound_int := intervalIntegral_sqrt_log_div_le hα_pos hαR hRC
  have hlogR_nn : 0 ≤ 1 + Real.log (C / R) := by
    have : 0 ≤ Real.log (C / R) := Real.log_nonneg ((one_le_div hR).2 hRC)
    linarith
  have hprod_eq : 16 / Real.sqrt m * (Real.sqrt d * (R * Real.sqrt (1 + Real.log (C / R)))) =
      16 * R * Real.sqrt (d * (1 + Real.log (C / R)) / m) := by
    rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg d) hlogR_nn),
      Real.sqrt_mul (Nat.cast_nonneg d)]
    ring
  calc empiricalRademacherComplexity F S
      ≤ 4 * α + 16 / Real.sqrt m * ∫ ε in α..R, Real.sqrt (Real.log ((C / ε) ^ d)) := hdud
    _ = 4 * α + 16 / Real.sqrt m * (Real.sqrt d * ∫ ε in α..R, Real.sqrt (Real.log (C / ε))) := by
        rw [hint_eval]
    _ ≤ δ + 16 / Real.sqrt m * (Real.sqrt d * (R * Real.sqrt (1 + Real.log (C / R)))) := by
        refine add_le_add h4α ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound_int (Real.sqrt_nonneg _)) (by positivity)
    _ = 16 * R * Real.sqrt (d * (1 + Real.log (C / R)) / m) + δ := by
        rw [hprod_eq, add_comm]

/-! ### Application 1: Lipschitz parametric classes on finite-dimensional normed spaces -/

section LipschitzParametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Empirical `L²(P_m)` covering bound for an `L`-Lipschitz parametric class**: if
`Θ ⊆ closedBall θ₀ r` and `Φ : E → Z → ℝ` is `L`-Lipschitz in empirical `L²(P_m)` distance, then
`empiricalCoveringNumber (Φ '' Θ) S ε ≤ (1 + 2 L r / ε) ^ dim E` for every `ε > 0`. -/
theorem empiricalCoveringNumber_lipschitz_ball_le {Z : Type*} {m : ℕ} (S : Fin m → Z)
    {Φ : E → Z → ℝ} {θ₀ : E} {r L ε : ℝ} (hr : 0 ≤ r) (hL : 0 < L) (hε : 0 < ε)
    {Θ : Set E} (hΘ : Θ ⊆ Metric.closedBall θ₀ r)
    (hΦ : ∀ θ₁ ∈ Metric.closedBall θ₀ r, ∀ θ₂ ∈ Metric.closedBall θ₀ r,
      dist (empiricalL2Vec S (Φ θ₁)) (empiricalL2Vec S (Φ θ₂)) ≤ L * dist θ₁ θ₂) :
    ((empiricalCoveringNumber (Φ '' Θ) S ε).toNat : ℝ) ≤
      (1 + 2 * (L * r) / ε) ^ Module.finrank ℝ E := by
  have hεL : 0 < ε / L := div_pos hε hL
  have h1 : empiricalCoveringNumber (Φ '' Θ) S ε ≤
      empiricalCoveringNumber (Φ '' Metric.closedBall θ₀ r) S ε :=
    coveringNumber_mono (Set.image_mono (Set.image_mono hΘ)) ε
  have h2 : empiricalCoveringNumber (Φ '' Metric.closedBall θ₀ r) S ε ≤
      internalCoveringNumber (empiricalL2Vec S '' (Φ '' Metric.closedBall θ₀ r)) ε :=
    coveringNumber_le_internalCoveringNumber _ ε
  have h3 : internalCoveringNumber (empiricalL2Vec S '' (Φ '' Metric.closedBall θ₀ r)) ε ≤
      internalCoveringNumber (Metric.closedBall θ₀ r) (ε / L) := by
    have himg : empiricalL2Vec S '' (Φ '' Metric.closedBall θ₀ r) =
        (fun θ => empiricalL2Vec S (Φ θ)) '' Metric.closedBall θ₀ r := by
      ext y; simp [Set.mem_image]
    have hmul : L * (ε / L) = ε := mul_div_cancel₀ ε hL.ne'
    simpa only [himg, hmul] using internalCoveringNumber_image_le_of_lipschitz hL.le hΦ (ε / L)
  have hlt_ball : internalCoveringNumber (Metric.closedBall θ₀ r) (ε / L) < ⊤ :=
    lt_of_le_of_lt (internalCoveringNumber_le_packingNumber _ hεL.le)
      (packingNumber_closedBall_lt_top θ₀ hr hεL)
  have hnat : (empiricalCoveringNumber (Φ '' Θ) S ε).toNat ≤
      (internalCoveringNumber (Metric.closedBall θ₀ r) (ε / L)).toNat :=
    ENat.toNat_le_of_le_natCast <| by
      simpa [ENat.natCast_toNat hlt_ball.ne] using (h1.trans h2).trans h3
  have hvol := internalCoveringNumber_closedBall_toNat_le θ₀ hr hεL
  calc ((empiricalCoveringNumber (Φ '' Θ) S ε).toNat : ℝ)
      ≤ ((internalCoveringNumber (Metric.closedBall θ₀ r) (ε / L)).toNat : ℝ) :=
        Nat.cast_le.2 hnat
    _ ≤ (1 + 2 * r / (ε / L)) ^ Module.finrank ℝ E := hvol
    _ = (1 + 2 * (L * r) / ε) ^ Module.finrank ℝ E := by
        congr 1; field_simp

/-- **Empirical Rademacher complexity of an `L`-Lipschitz parametric class** [Vershynin2018,
Section 8.1] (locator unverified). For any finite-dimensional real normed space `E` of dimension
`d`, any parameter set `Θ ⊆ Metric.closedBall θ₀ r` (`0 ≤ r`), and any `L`-Lipschitz
parameterization `Φ : E → Z → ℝ` on `closedBall θ₀ r` (`0 ≤ L`) in the empirical `L²(P_m)` metric,

`empiricalRademacherComplexity (Φ '' Θ) S ≤ 16 L r √(d (1 + log 3) / m)`.

No `log m` factor appears; edge cases (`m = 0`, `L = 0`, `r = 0`, `Θ = ∅`, `d = 0`) are all
included. -/
theorem empiricalRademacherComplexity_lipschitz_ball_le {Z : Type*} {m : ℕ} (S : Fin m → Z)
    {Φ : E → Z → ℝ} {θ₀ : E} {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    {Θ : Set E} (hΘ : Θ ⊆ Metric.closedBall θ₀ r)
    (hΦ : ∀ θ₁ ∈ Metric.closedBall θ₀ r, ∀ θ₂ ∈ Metric.closedBall θ₀ r,
      dist (empiricalL2Vec S (Φ θ₁)) (empiricalL2Vec S (Φ θ₂)) ≤ L * dist θ₁ θ₂) :
    empiricalRademacherComplexity (Φ '' Θ) S ≤
      16 * L * r * Real.sqrt (Module.finrank ℝ E * (1 + Real.log 3) / m) := by
  have hzero_nn : 0 ≤ 16 * L * r * Real.sqrt (Module.finrank ℝ E * (1 + Real.log 3) / m) := by
    positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalRademacherComplexity_def, rademacherAverage_def, Real.iSup_const_zero]
  rcases Θ.eq_empty_or_nonempty with rfl | ⟨θ₁, hθ₁⟩
  · simpa only [Set.image_empty, empiricalRademacherComplexity_empty] using hzero_nn
  rcases eq_or_lt_of_le hL with rfl | hL_pos
  · -- `L = 0`: every `f ∈ Φ '' Θ` equals `Φ θ₁` on `S`, so empirical Rademacher complexity is `0`.
    have hconst (θ : E) (hθ : θ ∈ Θ) (i : Fin m) : Φ θ (S i) = Φ θ₁ (S i) := by
      have hd : dist (empiricalL2Vec S (Φ θ)) (empiricalL2Vec S (Φ θ₁)) = 0 :=
        le_antisymm (by simpa using hΦ θ (hΘ hθ) θ₁ (hΘ hθ₁)) dist_nonneg
      have hsq : (∑ k, (Φ θ (S k) - Φ θ₁ (S k)) ^ 2) / m = 0 := by
        rw [← dist_sq_empiricalL2Vec hm, hd, sq, zero_mul]
      have hsum : ∑ k : Fin m, (Φ θ (S k) - Φ θ₁ (S k)) ^ 2 = 0 := by
        have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
        rwa [div_eq_zero_iff, or_iff_left hm0] at hsq
      have hsqi := (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (Φ θ (S k) - Φ θ₁ (S k))).1
        hsum i (mem_univ i)
      linarith [sq_eq_zero_iff.1 hsqi]
    have huniq : rademacherAverage (fun f : ↥(Φ '' Θ) => fun i => (f : Z → ℝ) (S i)) =
        rademacherAverage (fun _ : Unit => fun i => Φ θ₁ (S i)) := by
      refine rademacherAverage_eq_of_forall_exists (B := ⨆ i : Fin m, |Φ θ₁ (S i)|) ?_ ?_ ?_ ?_
      · rintro ⟨_, θ, hθ, rfl⟩ i
        change |Φ θ (S i)| ≤ _
        rw [hconst θ hθ i]
        exact le_ciSup (f := fun k : Fin m => |Φ θ₁ (S k)|) (Set.finite_range _).bddAbove i
      · intro _ i
        exact le_ciSup (f := fun k : Fin m => |Φ θ₁ (S k)|) (Set.finite_range _).bddAbove i
      · rintro ⟨_, θ, hθ, rfl⟩
        exact ⟨(), funext fun i => hconst θ hθ i⟩
      · intro _
        exact ⟨⟨Φ θ₁, θ₁, hθ₁, rfl⟩, rfl⟩
    rw [empiricalRademacherComplexity_def, huniq, rademacherAverage_unique]
    simp
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · -- `r = 0`: `closedBall θ₀ 0 = {θ₀}`, so `Φ '' Θ` is a singleton `{Φ θ₀}`.
    have hsub : Φ '' Θ = {Φ θ₀} := by
      ext f
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨θ, hθ, rfl⟩
        have hθeq : θ = θ₀ := by
          have := hΘ hθ; rw [Metric.closedBall_zero] at this; exact this
        rw [hθeq]
      · rintro rfl
        have hθ₁eq : θ₁ = θ₀ := by
          have := hΘ hθ₁; rw [Metric.closedBall_zero] at this; exact this
        exact ⟨θ₀, hθ₁eq ▸ hθ₁, rfl⟩
    rw [hsub, empiricalRademacherComplexity_singleton]
    simp
  -- General case: `R = L * r > 0`, `C = 3 * L * r`.
  have hR_pos : 0 < L * r := mul_pos hL_pos hr_pos
  have hbound : ∀ f ∈ Φ '' Θ, dist (empiricalL2Vec S f) (empiricalL2Vec S (Φ θ₀)) ≤ L * r := by
    rintro _ ⟨θ, hθ, rfl⟩
    have hθball : θ ∈ Metric.closedBall θ₀ r := hΘ hθ
    exact (hΦ θ hθball θ₀ (Metric.mem_closedBall_self hr)).trans
      (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.1 hθball) hL_pos.le)
  have hcov : ∀ ε ∈ Set.Ioc 0 (L * r),
      ((empiricalCoveringNumber (Φ '' Θ) S ε).toNat : ℝ) ≤
        (3 * (L * r) / ε) ^ Module.finrank ℝ E := by
    intro ε hε
    refine (empiricalCoveringNumber_lipschitz_ball_le S hr hL_pos hε.1 hΘ hΦ).trans ?_
    refine pow_le_pow_left₀ (by have := hε.1; positivity) ?_ _
    have h1 : (1 : ℝ) ≤ (L * r) / ε := (one_le_div hε.1).2 hε.2
    linarith [show 3 * (L * r) / ε = (L * r) / ε + 2 * (L * r) / ε by ring]
  have hres := empiricalRademacherComplexity_le_of_polynomial_covering hm S (Φ θ₀)
    hR_pos (by linarith : L * r ≤ 3 * (L * r)) hbound hcov
  have hratio : 3 * (L * r) / (L * r) = 3 := by field_simp
  rw [hratio] at hres
  simpa only [mul_assoc] using hres

/-- Pointwise-Lipschitz corollary: if `|Φ θ₁ z - Φ θ₂ z| ≤ L * dist θ₁ θ₂` for all `z`, then the
empirical `L²(P_m)` hypothesis holds on every sample `S`. -/
theorem empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise {Z : Type*} {m : ℕ}
    (S : Fin m → Z) {Φ : E → Z → ℝ} {θ₀ : E} {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    {Θ : Set E} (hΘ : Θ ⊆ Metric.closedBall θ₀ r)
    (hΦ : ∀ θ₁ ∈ Metric.closedBall θ₀ r, ∀ θ₂ ∈ Metric.closedBall θ₀ r, ∀ z,
      |Φ θ₁ z - Φ θ₂ z| ≤ L * dist θ₁ θ₂) :
    empiricalRademacherComplexity (Φ '' Θ) S ≤
      16 * L * r * Real.sqrt (Module.finrank ℝ E * (1 + Real.log 3) / m) :=
  empiricalRademacherComplexity_lipschitz_ball_le S hr hL hΘ fun θ₁ h₁ θ₂ h₂ =>
    dist_empiricalL2Vec_le_of_abs_sub_le S (mul_nonneg hL dist_nonneg) fun i =>
      hΦ θ₁ h₁ θ₂ h₂ (S i)

/-- **Population Rademacher complexity of an `L`-Lipschitz parametric class** on a finite domain
`Z`. -/
theorem rademacherComplexity_lipschitz_ball_le {Z : Type*} [Fintype Z] (D : PMF Z) (m : ℕ)
    {Φ : E → Z → ℝ} {θ₀ : E} {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    {Θ : Set E} (hΘ : Θ ⊆ Metric.closedBall θ₀ r)
    (hΦ : ∀ θ₁ ∈ Metric.closedBall θ₀ r, ∀ θ₂ ∈ Metric.closedBall θ₀ r, ∀ z,
      |Φ θ₁ z - Φ θ₂ z| ≤ L * dist θ₁ θ₂) :
    rademacherComplexity D (Φ '' Θ) m ≤
      16 * L * r * Real.sqrt (Module.finrank ℝ E * (1 + Real.log 3) / m) :=
  rademacherComplexity_le D fun S =>
    empiricalRademacherComplexity_lipschitz_ball_le_of_pointwise S hr hL hΘ hΦ

/-- **Uniform generalization bound for a bounded `L`-Lipschitz parametric class**: on a finite
domain `Z`, with probability at least `1 - δ` over `m > 0` independent draws from `D`, every
`θ ∈ Θ ⊆ closedBall θ₀ r` satisfies

`E_D (Φ θ) ≤ Ê_S (Φ θ) + 32 L r √(d (1 + log 3) / m) + (b - a) √(log (1 / δ) / (2 m))`. -/
theorem lipschitz_ball_generalization_bound {Z : Type*} [Fintype Z] (D : PMF Z) {m : ℕ}
    (hm : 0 < m) {Φ : E → Z → ℝ} {θ₀ : E} {r L a b : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hab : a < b) {Θ : Set E} (hΘ : Θ ⊆ Metric.closedBall θ₀ r)
    (hIcc : ∀ θ ∈ Θ, ∀ z, Φ θ z ∈ Set.Icc a b)
    (hΦ : ∀ θ₁ ∈ Metric.closedBall θ₀ r, ∀ θ₂ ∈ Metric.closedBall θ₀ r, ∀ z,
      |Φ θ₁ z - Φ θ₂ z| ≤ L * dist θ₁ θ₂)
    {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ θ ∈ Θ, 𝔼 i, Φ θ (S i) +
        32 * L * r * Real.sqrt (Module.finrank ℝ E * (1 + Real.log 3) / m) +
        (b - a) * Real.sqrt (Real.log (1 / δ) / (2 * m)) <
          ∑ z, (D z).toReal * Φ θ z}).toReal ≤ δ := by
  have hF : ∀ f ∈ Φ '' Θ, ∀ z, f z ∈ Set.Icc a b := by
    rintro _ ⟨θ, hθ, rfl⟩ z; exact hIcc θ hθ z
  have hR := rademacherComplexity_lipschitz_ball_le D m hr hL hΘ hΦ
  have hgen := rademacherComplexity_generalization_bound D hm hab hF hδ
  refine (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_)).trans hgen
  rintro S ⟨θ, hθ, hlt⟩
  exact ⟨Φ θ, ⟨θ, hθ, rfl⟩, by linarith⟩

end LipschitzParametric

/-! ### Application 2: Empirical `L²(P_m)` covering numbers of binary VC classes -/

/-- **Empirical `L²(P_m)` covering bound for a binary VC class** [Vershynin2018, Theorem 8.3.18]
(locator unverified): if every set shattered by `C` has at most `d` points, then for every sample
`S : Fin m → α` and every `0 < ε ≤ 1`,

`empiricalCoveringNumber (bitClass C) S ε ≤ (√8 / ε) ^ (4 * d)`.

Directly lifts the Hamming-distance packing bound `card_le_div_pow_of_le_hammingDist`. -/
theorem empiricalCoveringNumber_bitClass_le_of_vcDim {α : Type*} {C : ConceptClass α Bool}
    {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {m : ℕ} (S : Fin m → α) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((empiricalCoveringNumber (bitClass C) S ε).toNat : ℝ) ≤
      (Real.sqrt 8 / ε) ^ (4 * d) := by
  classical
  have hone_le : (1 : ℝ) ≤ (Real.sqrt 8 / ε) ^ (4 * d) := by
    refine one_le_pow₀ ((one_le_div hε).2 ?_)
    have : (1 : ℝ) ≤ Real.sqrt 8 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hpow_eq : (Real.sqrt 8 / ε) ^ (4 * d) = (8 / ε ^ 2) ^ (2 * d) := by
    calc (Real.sqrt 8 / ε) ^ (4 * d)
        = ((Real.sqrt 8 / ε) ^ 2) ^ (2 * d) := by rw [← pow_mul]; ring_nf
      _ = (8 / ε ^ 2) ^ (2 * d) := by rw [div_pow, Real.sq_sqrt (by norm_num)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hle1 : empiricalCoveringNumber (bitClass C) S ε ≤ 1 :=
      coveringNumber_le_one_of_subset_closedBall (x₀ := 0) fun v _ => by
        have hv : v = 0 := by ext i; exact i.elim0
        simpa [hv] using hε.le
    have hnat : (empiricalCoveringNumber (bitClass C) S ε).toNat ≤ 1 :=
      ENat.toNat_le_of_le_natCast (by simpa using hle1)
    exact (Nat.cast_le.2 hnat).trans (by simpa using hone_le)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  -- Bound any strictly `ε`-separated subset `P ⊆ empiricalL2Vec S '' bitClass C` via `Packing`.
  have hpack_bound : ∀ P : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ v ∈ P, v ∈ empiricalL2Vec S '' bitClass C) →
      (∀ v ∈ P, ∀ w ∈ P, v ≠ w → ε < dist v w) →
      (P.card : ℝ) ≤ (8 / ε ^ 2) ^ (2 * d) := by
    intro P hP hsep
    have hpick : ∀ v ∈ P, ∃ c ∈ C, empiricalL2Vec S (fun x => bitVal ℝ (c x)) = v := by
      intro v hv
      obtain ⟨f, hf, hfv⟩ := hP v hv
      obtain ⟨c, hc, rfl⟩ := mem_bitClass.1 hf
      exact ⟨c, hc, hfv⟩
    let toWord : EuclideanSpace ℝ (Fin m) → (Fin m → Bool) := fun v =>
      if hv : v ∈ P then fun i => Classical.choose (hpick v hv) (S i) else fun _ => false
    have htoWord_eq (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ P) :
        toWord v = fun i => Classical.choose (hpick v hv) (S i) :=
      dite_eq_left_of_eq_true (eq_true hv)
    have hvec_eq (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ P) :
        empiricalL2Vec S (fun x => bitVal ℝ (Classical.choose (hpick v hv) x)) = v :=
      (Classical.choose_spec (hpick v hv)).2
    have hdist_ham (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ P)
        (w : EuclideanSpace ℝ (Fin m)) (hw : w ∈ P) :
        dist v w ^ 2 = (hammingDist (toWord v) (toWord w) : ℝ) / m := by
      calc dist v w ^ 2
          = dist (empiricalL2Vec S (fun x => bitVal ℝ (Classical.choose (hpick v hv) x)))
              (empiricalL2Vec S (fun x => bitVal ℝ (Classical.choose (hpick w hw) x))) ^ 2 := by
            rw [hvec_eq v hv, hvec_eq w hw]
        _ = (∑ i : Fin m, (bitVal ℝ (Classical.choose (hpick v hv) (S i)) -
              bitVal ℝ (Classical.choose (hpick w hw) (S i))) ^ 2) / m :=
            dist_sq_empiricalL2Vec hm S _ _
        _ = (∑ i : Fin m, if toWord v i ≠ toWord w i then (1 : ℝ) else 0) / m := by
            congr 1
            refine sum_congr rfl fun i _ => ?_
            rw [htoWord_eq v hv, htoWord_eq w hw]
            have hbit : ∀ b₁ b₂ : Bool,
                (bitVal ℝ b₁ - bitVal ℝ b₂) ^ 2 = if b₁ ≠ b₂ then (1 : ℝ) else 0 := by
              intro b₁ b₂; cases b₁ <;> cases b₂ <;> norm_num [bitVal]
            exact hbit _ _
        _ = (hammingDist (toWord v) (toWord w) : ℝ) / m := by
            rw [sum_boole]; rfl
    have hinj : Set.InjOn toWord (P : Set (EuclideanSpace ℝ (Fin m))) := by
      intro v hv w hw hvw
      by_contra hne
      have h0 : dist v w ^ 2 = 0 := by rw [hdist_ham v hv w hw, hvw, hammingDist_self]; simp
      have hlt : 0 < dist v w := lt_trans hε (hsep v hv w hw hne)
      have hpos : 0 < dist v w ^ 2 := sq_pos_of_pos hlt
      linarith
    let Q : Finset (Fin m → Bool) := P.image toWord
    have hQcard : Q.card = P.card := card_image_of_injOn hinj
    have hQC : ∀ u ∈ Q, u ∈ restriction C S := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
      refine mem_restriction.2 ⟨Classical.choose (hpick v hv),
        (Classical.choose_spec (hpick v hv)).1, fun i => ?_⟩
      simp [htoWord_eq v hv]
    have hQsep : ∀ u ∈ Q, ∀ u' ∈ Q, u ≠ u' → ε ^ 2 * m ≤ hammingDist u u' := by
      intro u hu u' hu' hne
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hu'
      have hvw : v ≠ w := fun h => hne (congrArg toWord h)
      have hd : ε ^ 2 < dist v w ^ 2 := by gcongr; exact hsep v hv w hw hvw
      rw [hdist_ham v hv w hw, lt_div_iff₀ hm_pos] at hd
      exact hd.le
    have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hε2_le1 : ε ^ 2 ≤ 1 := by nlinarith
    rw [← hQcard]
    exact card_le_div_pow_of_le_hammingDist hC hQC hε2_pos hε2_le1 hQsep
  have hpack_le : packingNumber (empiricalL2Vec S '' bitClass C) ε ≤
      ⌊(8 / ε ^ 2) ^ (2 * d)⌋₊ :=
    packingNumber_le_of_forall_card_le fun P hP hsep => by
      exact_mod_cast Nat.le_floor (hpack_bound P hP hsep)
  have hcov_le : empiricalCoveringNumber (bitClass C) S ε ≤
      ⌊(8 / ε ^ 2) ^ (2 * d)⌋₊ :=
    (coveringNumber_le_internalCoveringNumber _ ε).trans
      ((internalCoveringNumber_le_packingNumber _ hε.le).trans hpack_le)
  have hnat : (empiricalCoveringNumber (bitClass C) S ε).toNat ≤ ⌊(8 / ε ^ 2) ^ (2 * d)⌋₊ :=
    ENat.toNat_le_of_le_natCast hcov_le
  rw [hpow_eq]
  exact (Nat.cast_le.2 hnat).trans (Nat.floor_le (by positivity))

end Cslib.MachineLearning
