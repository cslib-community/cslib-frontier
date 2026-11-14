/-
Copyright (c) 2026 Samuel Schlesinger, Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing
import CslibFrontier.Foundations.Analysis.Calculus.Taylor
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Comparing expectations through smooth test functions

General tools for invariance principles proved by the Replacement Method
[O'Donnell, Sections 11.5 and 11.6][ODonnell2014], for test functions `ψ : ℝ → ℝ` of class
`Cᵐ` with a bounded `m`-th derivative.

* **The one-dimensional replacement step** (`abs_integral_sub_integral_le_of_moments`): if two
  laws have equal moments of orders `0, …, n` and `ψ` is `C^(n+1)` with `|ψ⁽ⁿ⁺¹⁾| ≤ C`, then
  `E ψ(a + s b)` differs between them by at most
  `C / (n + 1)! · |b| ^ (n + 1) · (E_μ |s| ^ (n + 1) + E_ν |s| ^ (n + 1))`, by Taylor's theorem.
  The invariance principle for sums uses `n = 2`, the Basic Invariance Principle `n = 3`.
* **Integrability** (`integrable_comp_of_memLp`): such a `ψ` grows at most like a polynomial of
  degree `n + 1`, so `ψ ∘ U` is integrable for `U` in `L^(n+1)`.
* **From `Cᵐ` tests to Lipschitz tests** (`abs_integral_comp_sub_le_of_lipschitzWith`): smoothing
  a `K`-Lipschitz `ψ` by the `m`-fold moving average of
  `CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing` turns a bound
  `|E[φ(X)] - E[φ(Y)]| ≤ C τᵐ` for all `Cᵐ` tests with `|φ⁽ᵐ⁾| ≤ C` into
  `|E[ψ(X)] - E[ψ(Y)]| ≤ (2m + 2ᵐ⁻¹) K τ`. This is the smoothing argument of Corollaries 11.59
  (`m = 3`) and 11.68 (`m = 4`).

The corresponding step to distribution functions is in
`CslibFrontier.Foundations.Probability.LevyDistance`.

## Main results

* `ProbabilityTheory.abs_integral_sub_integral_le_of_moments`: the one-dimensional replacement
  step, for laws with matching moments up to order `n` and a `C^(n+1)` test function.
* `ProbabilityTheory.integrable_comp_of_memLp`: `ψ ∘ U` is integrable for such a test function
  and `U` in `L^(n+1)`.
* `ProbabilityTheory.abs_integral_comp_sub_le_of_lipschitzWith`: from `Cᵐ` tests to Lipschitz
  tests.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Sections 11.5 and 11.6.
-/

public section

open MeasureTheory Finset Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### One coordinate -/

section OneCoordinate

open scoped Nat

/-- **The one-dimensional replacement step.** If the laws `μ` and `ν` have finite moments of order
`n + 1` and the same moments of orders `0, …, n`, and `ψ` is `C^(n+1)` with `|ψ⁽ⁿ⁺¹⁾| ≤ C`, then
for all `a`, `b`, `|E_μ ψ(a + s b) - E_ν ψ(a + s b)|` is at most
`C / (n + 1)! · |b| ^ (n + 1) · (E_μ |s| ^ (n + 1) + E_ν |s| ^ (n + 1))`. -/
theorem abs_integral_sub_integral_le_of_moments {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {n : ℕ} (hμ : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) μ)
    (hν : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) ν)
    (hmom : ∀ j ≤ n, ∫ s, s ^ j ∂μ = ∫ s, s ^ j ∂ν)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂μ - ∫ s, ψ (a + s * b) ∂ν| ≤
      C / (n + 1)! * |b| ^ (n + 1) * (∫ s, |s| ^ (n + 1) ∂μ + ∫ s, |s| ^ (n + 1) ∂ν) := by
  set T : ℝ → ℝ := fun s => ∑ j ∈ range (n + 1), iteratedDeriv j ψ a * (s * b) ^ j / (j ! : ℝ)
  set R : ℝ → ℝ := fun s => ψ (a + s * b) - T s
  set K : ℝ := C / (n + 1)! * |b| ^ (n + 1)
  have hR (s : ℝ) : |R s| ≤ K * |s| ^ (n + 1) := by
    calc |R s| ≤ C * |s * b| ^ (n + 1) / (n + 1)! := abs_sub_sum_iteratedDeriv_le hψ hC a (s * b)
      _ = K * |s| ^ (n + 1) := by rw [abs_mul, mul_pow]; ring
  have hψc : Continuous ψ := hψ.continuous
  have hTint {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      Integrable T m ∧ ∫ s, T s ∂m =
        ∑ j ∈ range (n + 1), iteratedDeriv j ψ a * b ^ j / j ! * ∫ s, s ^ j ∂m := by
    have hint (j : ℕ) (hj : j ∈ range (n + 1)) :
        Integrable (fun s => iteratedDeriv j ψ a * (s * b) ^ j / j !) m := by
      have := (integrable_pow_of_memLp hm (j := j) (by
        have := mem_range.1 hj; omega)).const_mul (iteratedDeriv j ψ a * b ^ j / j !)
      refine this.congr (ae_of_all _ fun s => ?_)
      simp only [mul_pow]; ring
    refine ⟨integrable_finsetSum _ hint, ?_⟩
    rw [integral_finsetSum _ hint]
    refine sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1 with s : 1; simp only [mul_pow]; ring
  have hRint {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      Integrable R m :=
    ((integrable_abs_pow_of_memLp hm le_rfl).const_mul K).mono'
      (by fun_prop : Continuous R).aestronglyMeasurable
      (ae_of_all _ fun s => by simpa using hR s)
  have hsplit {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      ∫ s, ψ (a + s * b) ∂m = ∫ s, T s ∂m + ∫ s, R s ∂m := by
    rw [← integral_add (hTint hm).1 (hRint hm)]
    congr 1 with s : 1; simp [R]
  have hRle {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id ((n + 1 : ℕ) : ℝ≥0∞) m) :
      |∫ s, R s ∂m| ≤ K * ∫ s, |s| ^ (n + 1) ∂m := by
    rw [← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans (integral_mono (hRint hm).abs
      ((integrable_abs_pow_of_memLp hm le_rfl).const_mul K) hR)
  have hT : ∫ s, T s ∂μ = ∫ s, T s ∂ν := by
    rw [(hTint hμ).2, (hTint hν).2]
    refine sum_congr rfl fun j hj => ?_
    rw [hmom j (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  rw [hsplit hμ, hsplit hν, hT, add_sub_add_left_eq_sub, mul_add]
  exact (abs_sub _ _).trans (add_le_add (hRle hμ) (hRle hν))

/-- If `ψ` is `C^(n+1)` with `|ψ⁽ⁿ⁺¹⁾| ≤ C`, then `ψ` grows at most like a polynomial of degree
`n + 1`, so `ψ ∘ U` is integrable for every `U` in `L^(n+1)` on a finite measure space. -/
theorem integrable_comp_of_memLp {ψ : ℝ → ℝ} {n : ℕ} (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {U : Ω → ℝ} (hU : MemLp U (n + 1 : ℕ) P) :
    Integrable (fun ω => ψ (U ω)) P := by
  obtain ⟨K, hK⟩ := hψ.exists_abs_le_mul_one_add_pow_of_abs_iteratedDeriv_le hC
  refine (((integrable_const 1).add (hU.integrable_norm_pow n.succ_ne_zero)).const_mul K).mono'
    (hψ.continuous.comp_aestronglyMeasurable hU.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  simpa [Real.norm_eq_abs] using hK (U ω)

end OneCoordinate

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'}

/-! ### From `Cᵐ` tests to Lipschitz tests -/

/-- If `φ(X)` is integrable and `|ψ - φ| ≤ M`, then `ψ(X)` is integrable and its expectation is
within `M` of that of `φ(X)`. -/
private theorem integrable_and_abs_integral_sub_le [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ u, |ψ u - φ u| ≤ M) (hφX : Integrable (fun ω => φ (X ω)) P) :
    Integrable (fun ω => ψ (X ω)) P ∧ |∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P| ≤ M := by
  have hb : ∀ᵐ ω ∂P, ‖ψ (X ω) - φ (X ω)‖ ≤ M := ae_of_all _ fun ω => hM (X ω)
  have hd : Integrable (fun ω => ψ (X ω) - φ (X ω)) P :=
    Integrable.of_bound ((hψ.sub hφ).comp_aestronglyMeasurable hX.aestronglyMeasurable) M hb
  have hψX : Integrable (fun ω => ψ (X ω)) P :=
    (hd.add hφX).congr (ae_of_all _ fun ω => sub_add_cancel _ _)
  refine ⟨hψX, ?_⟩
  rw [← integral_sub hψX hφX]
  simpa using norm_integral_le_of_norm_le_const hb

/-- **From `Cᵐ` tests to Lipschitz tests**: let `m ≥ 1` and suppose that for every `φ` of class
`Cᵐ` with `|φ⁽ᵐ⁾| ≤ C`, the random variables `φ(X)` and `φ(Y)` are integrable and
`|E[φ(X)] - E[φ(Y)]| ≤ C τᵐ`. Then `|E[ψ(X)] - E[ψ(Y)]| ≤ (2m + 2ᵐ⁻¹) K τ` for every
`K`-Lipschitz `ψ`. This is the smoothing argument behind [O'Donnell, Corollary 11.59][ODonnell2014]
(`m = 3`, constant `10`) and [O'Donnell, Corollary 11.68][ODonnell2014] (`m = 4`, constant
`16`). -/
theorem abs_integral_comp_sub_le_of_lipschitzWith [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : Ω → ℝ} {Y : Ω' → ℝ} {m : ℕ} (hm : m ≠ 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ (φ : ℝ → ℝ) (C : ℝ), ContDiff ℝ m φ → (∀ u, |iteratedDeriv m φ u| ≤ C) →
      Integrable (fun ω => φ (X ω)) P ∧ Integrable (fun ω => φ (Y ω)) Q ∧
        |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| ≤ C * τ ^ m)
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ) :
    |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q| ≤ (2 * m + 2 ^ (m - 1)) * K * τ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  have hid := h (fun u => u) 1 (contDiff_id.of_le le_top) fun u => by
    rcases k with _ | k <;> simp [iteratedDeriv_fun_id]
  have hX : AEMeasurable X P := hid.1.aemeasurable
  have hY : AEMeasurable Y Q := hid.2.1.aemeasurable
  have key (t : ℝ) (ht : 0 < t) : |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q| ≤
      2 * (k + 1) * K * t + 2 ^ k * K / t ^ k * τ ^ (k + 1) := by
    set φ := (movingAverage t)^[k + 1] ψ
    have hφ : ContDiff ℝ (k + 1 : ℕ) φ := contDiff_iterate_movingAverage hψ.continuous (k + 1)
    have hC (u : ℝ) : |iteratedDeriv (k + 1) φ u| ≤ 2 ^ k * K / t ^ k :=
      hψ.abs_iteratedDeriv_iterate_movingAverage_le ht (Nat.lt_succ_self k) u
    have hM (u : ℝ) : |ψ u - φ u| ≤ (k + 1 : ℕ) * K * t := by
      rw [abs_sub_comm]
      exact hψ.abs_iterate_movingAverage_sub_le ht (k + 1) u
    obtain ⟨hφX, hφY, hXY⟩ := h φ _ hφ hC
    have hX' := (integrable_and_abs_integral_sub_le hX hφ.continuous hψ.continuous hM hφX).2
    have hY' := (integrable_and_abs_integral_sub_le hY hφ.continuous hψ.continuous hM hφY).2
    calc |∫ ω, ψ (X ω) ∂P - ∫ ω, ψ (Y ω) ∂Q|
        = |(∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P) + (∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q) -
            (∫ ω, ψ (Y ω) ∂Q - ∫ ω, φ (Y ω) ∂Q)| := by congr 1; ring
      _ ≤ |∫ ω, ψ (X ω) ∂P - ∫ ω, φ (X ω) ∂P| + |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| +
            |∫ ω, ψ (Y ω) ∂Q - ∫ ω, φ (Y ω) ∂Q| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ (k + 1 : ℕ) * K * t + 2 ^ k * K / t ^ k * τ ^ (k + 1) + (k + 1 : ℕ) * K * t := by
          gcongr
      _ = 2 * (k + 1) * K * t + 2 ^ k * K / t ^ k * τ ^ (k + 1) := by push_cast; ring
  rw [Nat.add_sub_cancel]
  push_cast
  rcases hτ.eq_or_lt with rfl | hτ
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have ht : 0 < δ / (2 * (k + 1) * K + 1) := by positivity
    refine (key _ ht).trans ?_
    rw [zero_pow (by omega), mul_zero, add_zero, mul_zero, zero_add, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [K.2]
  · refine (key τ hτ).trans_eq ?_
    field_simp
    ring

end ProbabilityTheory
