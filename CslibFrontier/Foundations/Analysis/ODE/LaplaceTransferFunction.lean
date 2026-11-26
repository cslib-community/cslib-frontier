/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, with `Mathlib/Analysis/ODE/TransferFunction.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.TransferFunction
public import CslibFrontier.Foundations.Analysis.LaplaceTransform.Convolution
public import CslibFrontier.Foundations.Analysis.LaplaceTransform.Exp
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Laplace transforms of LTI responses and the transfer function

For a real LTI system `ẋ = A x + B u`, `y = C x + D u` (`LTISystem`) with response kernel
`h t = C exp (t A) B` and transfer function `H s = C (s I - A)⁻¹ B + D`
(`LTISystem.transferFunction`), this file proves the frequency-domain form of the time-domain
output formula of `CslibFrontier.Foundations.Analysis.ODE.StateSpace`. Real signals are read
over `ℂ` coordinatewise, `t ↦ fun i => (y t i : ℂ)`, and transformed with `laplace`.

## The growth hypothesis

The half-planes are explicit in the growth of the flow: the hypothesis
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0` and all entries. Every real matrix satisfies one
(`Matrix.exists_abs_exp_smul_apply_le`, with `ω` the `L∞` operator norm of `A`), and a decay
bound `‖x t‖ ≤ M exp (-α t) ‖x 0‖` on the trajectories of `ẋ = A x`, as in
`ContinuousLinearMap.IsExponentiallyStable`, gives one with `ω = -α`
(`Matrix.abs_exp_smul_apply_le_of_forall_norm_le`). No diagonalizability, minimality,
controllability or observability is assumed.

## Results

* **The resolvent** (`Matrix.laplace_exp_smul_apply_ofReal`): on `re s > ω`, `s I - A` is
  invertible (`Matrix.isUnit_smul_one_sub_map_of_abs_exp_smul_apply_le`) and the entries of the
  flow have transforms `laplace (exp (t • A) i j) s = (s I - A)⁻¹ i j`.
* **The impulse response** (`LTISystem.laplace_responseKernel`,
  `LTISystem.laplace_responseKernel_eq_transferFunction_sub`): on `re s > ω`,
  `laplace (h i j) s = (C (s I - A)⁻¹ B) i j = H s i j - D i j`.
* **The transfer-function theorem** (`LTISystem.IsSolutionOn.laplace_output`): for a solution on
  `[0, ∞)` with zero initial state and an input continuous on `[0, ∞)` whose transform converges
  at `s`, with `re s > ω`, the output `y = C x + D u` has
  `laplace y s = H s *ᵥ laplace u s`, feedthrough `D` included. It is derived from the output
  formula `y = D u + h ∗ u` (`LTISystem.IsSolutionOn.output_eq_Ici`), the convolution theorem
  `laplace_causalConvolution` and the resolvent theorem, not from an assumed identity. For an
  input of exponential order `σ` the hypothesis on `u` holds on `re s > σ`
  (`LTISystem.IsSolutionOn.laplace_output_of_norm_le`).
* **Poles and stability.** The transform of `h` is holomorphic on `re s > ω`
  (`LTISystem.differentiableOn_laplace_responseKernel`), so `H = laplace h + D` is holomorphic
  there (`LTISystem.differentiableOn_transferFunction_of_abs_exp_smul_apply_le`). A **pole** of an
  entry `H i j` is a point `z` with `meromorphicOrderAt (fun s => H s i j) z < 0` (Mathlib's
  order of a meromorphic function; `H i j` is rational, hence meromorphic). Every pole has
  `re z ≤ ω` (`LTISystem.re_le_of_meromorphicOrderAt_transferFunction_neg`); under exponential
  stability, for instance from an accepted `Cslib.LinearAlgebra.LyapunovCert`, there is `α > 0`
  with every pole in `re z ≤ -α`
  (`LTISystem.exists_pos_re_le_of_meromorphicOrderAt_neg_of_isExponentiallyStable`).

The converse fails: a pole of `(s I - A)⁻¹` can cancel in `C (s I - A)⁻¹ B`, so `H` can be
holomorphic on `re s > -1` although `A` has the eigenvalue `1` (the tests check #8322's hidden
unstable mode). The stability certificate concerns `A`, not `H`.

## References

* S. Boyd, *EE263: Introduction to Linear Dynamical Systems*, Stanford, lecture "Solution via
  Laplace transform and matrix exponential" (the resolvent, the transfer function, poles as
  eigenvalues). Locator to be checked.
-/

public section

open Set Matrix NormedSpace MeasureTheory

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {M ω : ℝ} {s : ℂ}

/-- The entries of the real flow, read over `ℂ`, are those of the flow of `A` read over `ℂ`. -/
theorem ofReal_exp_smul_apply (A : Matrix n n ℝ) (t : ℝ) (i j : n) :
    ((exp (t • A) i j : ℝ) : ℂ) = exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) i j := by
  rw [← map_algebraMap_exp_smul]
  rfl

/-- The entries of the real flow are continuous in time. -/
theorem continuous_exp_smul_apply (A : Matrix n n ℝ) (i j : n) :
    Continuous fun t : ℝ => exp (t • A) i j := by
  have hc : Continuous fun t : ℝ => exp (t • toEuclideanCLM (𝕜 := ℝ) A) :=
    (differentiable_exp_smul_const ℝ (toEuclideanCLM (𝕜 := ℝ) A)).continuous
  have e : (fun t : ℝ => exp (t • A) i j) = fun t =>
      (exp (t • toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 (Pi.single j 1))).ofLp i := by
    funext t
    rw [ofLp_exp_smul_toEuclideanCLM_apply, WithLp.ofLp_toLp, mulVec_single_one]
    rfl
  rw [e]
  exact (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp (hc.clm_apply continuous_const))

/-- **A decay bound on trajectories bounds the entries of the flow.** If every trajectory of
`ẋ = A x` on `[0, ∞)` satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖` in the Euclidean norm, then
`|exp (t • A) i j| ≤ M exp (-α t)` for `t > 0` and all entries. -/
theorem abs_exp_smul_apply_le_of_forall_norm_le {α : ℝ}
    (h : ∀ x : ℝ → EuclideanSpace ℝ n, (toEuclideanCLM (𝕜 := ℝ) A).IsTrajectoryOn x (Ici 0) →
      ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖) :
    ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (-α * t) := by
  intro t ht i j
  have hx := (isTrajectoryOn_toEuclideanCLM_iff
    (x := fun t => exp (t • A) *ᵥ Pi.single j 1)).2 (hasDerivWithinAt_exp_smul_mulVec A _)
  have h1 := h _ hx t (le_of_lt ht)
  have hn : ‖(WithLp.toLp 2 (exp ((0 : ℝ) • A) *ᵥ Pi.single j 1) : EuclideanSpace ℝ n)‖ = 1 := by
    rw [zero_smul, exp_zero, one_mulVec]
    exact (PiLp.norm_single (p := 2) (β := fun _ : n => ℝ) j (1 : ℝ)).trans (by simp)
  rw [hn, mul_one] at h1
  rw [neg_mul]
  have h2 := PiLp.norm_apply_le
    (WithLp.toLp 2 (exp (t • A) *ᵥ Pi.single j 1) : EuclideanSpace ℝ n) i
  have e : (WithLp.toLp 2 ((exp (t • A)).col j) : EuclideanSpace ℝ n).ofLp i = exp (t • A) i j :=
    rfl
  rw [mulVec_single_one] at h1 h2
  rw [e, Real.norm_eq_abs] at h2
  exact h2.trans h1

/-- **Every real matrix has an exponential growth bound** for the entries of its flow:
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, with `M = 1` and `ω` the `L∞` operator norm of
`A` read over `ℂ`. -/
theorem exists_abs_exp_smul_apply_le (A : Matrix n n ℝ) :
    ∃ M ω : ℝ, ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (ω * t) := by
  open scoped Matrix.Norms.Operator in
  refine ⟨1, ‖A.map (algebraMap ℝ ℂ)‖, fun t ht i j => ?_⟩
  have : Nonempty n := ⟨i⟩
  open scoped Matrix.Norms.Operator in
  calc |exp (t • A) i j| = ‖exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) i j‖ := by
        rw [← ofReal_exp_smul_apply, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖exp ((t : ℂ) • A.map (algebraMap ℝ ℂ))‖ := norm_apply_le_linfty_opNorm _ i j
    _ ≤ 1 * Real.exp (‖A.map (algebraMap ℝ ℂ)‖ * t) := by
        rw [one_mul]
        exact norm_exp_smul_le (le_of_lt ht)

private theorem norm_exp_smul_map_apply_le
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (ω * t)) :
    ∀ t ∈ Ioi (0 : ℝ), ∀ i j,
      ‖exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) i j‖ ≤ M * Real.exp (ω * t) := fun t ht i j => by
  rw [← ofReal_exp_smul_apply, Complex.norm_real, Real.norm_eq_abs]
  exact hA t ht i j

/-- The entries of the real flow have convergent Laplace transforms on `re s > ω` under the
growth bound `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`. -/
theorem laplaceConvergent_exp_smul_apply_ofReal
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i j : n) : LaplaceConvergent (fun t : ℝ => (exp (t • A) i j : ℂ)) s := by
  simp_rw [ofReal_exp_smul_apply]
  exact laplaceConvergent_exp_smul_apply (norm_exp_smul_map_apply_le hA) hs i j

/-- **`s I - A` is invertible on the half-plane of growth.** Under the growth bound
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, the complex matrix `s • 1 - A` is invertible for
every `s` with `ω < re s`. -/
theorem isUnit_smul_one_sub_map_of_abs_exp_smul_apply_le
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    IsUnit (s • (1 : Matrix n n ℂ) - A.map (algebraMap ℝ ℂ)) :=
  isUnit_smul_one_sub_of_norm_exp_le (norm_exp_smul_map_apply_le hA) hs

/-- **The Laplace transform of the real flow is the resolvent.** Under the growth bound
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, for every `s` with `ω < re s`,
`laplace (fun t => exp (t • A) i j) s = (s • 1 - A)⁻¹ i j` with `A` read over `ℂ`. -/
theorem laplace_exp_smul_apply_ofReal
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i j : n) : laplace (fun t : ℝ => (exp (t • A) i j : ℂ)) s =
      (s • (1 : Matrix n n ℂ) - A.map (algebraMap ℝ ℂ))⁻¹ i j := by
  simp_rw [ofReal_exp_smul_apply]
  exact laplace_exp_smul_apply (norm_exp_smul_map_apply_le hA) hs i j

end Matrix

namespace LTISystem

variable {n m p : Type*} [Fintype n] [DecidableEq n] (S : LTISystem n m p) {M ω : ℝ} {s : ℂ}

/-! ### The impulse response -/

private theorem ofReal_responseKernel_apply (t : ℝ) (i : p) (j : m) :
    ((S.responseKernel t i j : ℝ) : ℂ) = ∑ l, (∑ k, S.C.map (algebraMap ℝ ℂ) i k *
      (exp (t • S.A) k l : ℂ)) * S.B.map (algebraMap ℝ ℂ) l j := by
  rw [responseKernel_eq]
  simp [Matrix.mul_apply]

omit [DecidableEq n] in
private theorem laplaceConvergent_sandwich {P : Matrix p n ℂ} {Q : Matrix n m ℂ}
    {F : ℝ → n → n → ℂ} (hF : ∀ k l, LaplaceConvergent (fun t => F t k l) s) (i : p) (j : m) :
    LaplaceConvergent (fun t => ∑ l, (∑ k, P i k * F t k l) * Q l j) s :=
  LaplaceConvergent.sum fun l _ =>
    (LaplaceConvergent.sum fun k _ => (hF k l).const_mul (P i k)).mul_const (Q l j)

omit [DecidableEq n] in
private theorem laplace_sandwich {P : Matrix p n ℂ} {Q : Matrix n m ℂ}
    {F : ℝ → n → n → ℂ} (hF : ∀ k l, LaplaceConvergent (fun t => F t k l) s) (i : p) (j : m) :
    laplace (fun t => ∑ l, (∑ k, P i k * F t k l) * Q l j) s =
      (P * Matrix.of (fun k l => laplace (fun t => F t k l) s) * Q) i j := by
  rw [laplace_sum fun l _ =>
    (LaplaceConvergent.sum fun k _ => (hF k l).const_mul (P i k)).mul_const (Q l j)]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [laplace_mul_const, laplace_sum fun k _ => (hF k l).const_mul (P i k)]
  simp only [laplace_const_mul]

/-- The entries of the response kernel have convergent Laplace transforms on `re s > ω` under
the growth bound `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`. -/
theorem laplaceConvergent_responseKernel
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i : p) (j : m) : LaplaceConvergent (fun t => (S.responseKernel t i j : ℂ)) s := by
  simp_rw [ofReal_responseKernel_apply]
  exact laplaceConvergent_sandwich (P := S.C.map (algebraMap ℝ ℂ))
    (Q := S.B.map (algebraMap ℝ ℂ)) (laplaceConvergent_exp_smul_apply_ofReal hA hs) i j

/-- **The transform of the impulse response.** Under the growth bound
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, for every `s` with `ω < re s` the entries of the
response kernel `h t = C exp (t A) B` have transforms
`laplace (fun t => h t i j) s = (C (s I - A)⁻¹ B) i j`, with the matrices read over `ℂ`. -/
theorem laplace_responseKernel
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i : p) (j : m) : laplace (fun t => (S.responseKernel t i j : ℂ)) s =
      (S.C.map (algebraMap ℝ ℂ) * (s • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))⁻¹ *
        S.B.map (algebraMap ℝ ℂ)) i j := by
  simp_rw [ofReal_responseKernel_apply]
  rw [laplace_sandwich (P := S.C.map (algebraMap ℝ ℂ)) (Q := S.B.map (algebraMap ℝ ℂ))
    (laplaceConvergent_exp_smul_apply_ofReal hA hs) i j]
  have hR : Matrix.of (fun k l => laplace (fun t : ℝ => (exp (t • S.A) k l : ℂ)) s) =
      (s • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))⁻¹ := by
    ext k l
    exact laplace_exp_smul_apply_ofReal hA hs k l
  rw [hR]

/-- **The transform of the impulse response is `H - D`.** Under the growth bound
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, for every `s` with `ω < re s`,
`laplace (fun t => h t i j) s = H s i j - D i j`. -/
theorem laplace_responseKernel_eq_transferFunction_sub
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i : p) (j : m) : laplace (fun t => (S.responseKernel t i j : ℂ)) s =
      S.transferFunction s i j - S.D i j := by
  rw [laplace_responseKernel S hA hs]
  simp [transferFunction]

private theorem continuous_responseKernel_apply (i : p) (j : m) :
    Continuous fun t => S.responseKernel t i j := by
  simp_rw [responseKernel_eq, Matrix.mul_apply]
  exact continuous_finsetSum _ fun l _ => (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_exp_smul_apply S.A k l)).mul continuous_const

/-! ### Poles and stability -/

/-- The entries of the response kernel inherit the growth of the flow. -/
private theorem norm_ofReal_responseKernel_apply_le
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (i : p)
    (j : m) : ∀ t ∈ Ioi (0 : ℝ), ‖((S.responseKernel t i j : ℝ) : ℂ)‖ ≤
      (∑ l, ∑ k, |S.C i k| * M * |S.B l j|) * Real.exp (ω * t) := fun t ht => by
  rw [Complex.norm_real, Real.norm_eq_abs, responseKernel_eq]
  simp only [Matrix.mul_apply]
  calc |∑ l, (∑ k, S.C i k * exp (t • S.A) k l) * S.B l j|
      ≤ ∑ l, ∑ k, |S.C i k| * |exp (t • S.A) k l| * |S.B l j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [abs_mul]
        refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
          (abs_nonneg _)).trans (le_of_eq ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [abs_mul]
    _ ≤ ∑ l, ∑ k, |S.C i k| * M * |S.B l j| * Real.exp (ω * t) := by
        refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
        have := hA t ht k l
        calc |S.C i k| * |exp (t • S.A) k l| * |S.B l j| ≤
              |S.C i k| * (M * Real.exp (ω * t)) * |S.B l j| := by gcongr
          _ = |S.C i k| * M * |S.B l j| * Real.exp (ω * t) := by ring
    _ = (∑ l, ∑ k, |S.C i k| * M * |S.B l j|) * Real.exp (ω * t) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.sum_mul]

/-- **The transform of the impulse response is holomorphic on the half-plane of growth.** Under
the growth bound `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, `s ↦ laplace (h i j) s` is complex
differentiable on `re s > ω`. -/
theorem differentiableOn_laplace_responseKernel
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (i : p) (j : m) :
    DifferentiableOn ℂ (laplace fun t => (S.responseKernel t i j : ℂ)) {s | ω < s.re} :=
  differentiableOn_laplace (Complex.continuous_ofReal.comp
      (continuous_responseKernel_apply S i j)).aestronglyMeasurable
    (S.norm_ofReal_responseKernel_apply_le hA i j)

/-- **The transfer function is holomorphic on the half-plane of growth, via the Laplace
transform.** Under the growth bound `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, every entry of
`H` is complex differentiable on `re s > ω`, because `H = laplace h + D` there. -/
theorem differentiableOn_transferFunction_of_abs_exp_smul_apply_le
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (i : p) (j : m) :
    DifferentiableOn ℂ (fun s => S.transferFunction s i j) {s | ω < s.re} :=
  ((S.differentiableOn_laplace_responseKernel hA i j).add_const (S.D i j : ℂ)).congr fun s hs => by
    rw [S.laplace_responseKernel_eq_transferFunction_sub hA hs, sub_add_cancel]

/-- **Every pole of the transfer function lies in `re z ≤ ω`.** Under the growth bound
`|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`, every pole `z` of an entry of `H`, i.e. every `z`
with `meromorphicOrderAt (fun s => H s i j) z < 0`, has `re z ≤ ω`. -/
theorem re_le_of_meromorphicOrderAt_transferFunction_neg
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (i : p) (j : m)
    {z : ℂ} (hz : meromorphicOrderAt (fun s => S.transferFunction s i j) z < 0) : z.re ≤ ω := by
  by_contra h
  have hopen : IsOpen {s : ℂ | ω < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have han := (S.differentiableOn_transferFunction_of_abs_exp_smul_apply_le hA i j).analyticAt
    (hopen.mem_nhds (not_le.1 h))
  exact (not_lt.2 han.meromorphicOrderAt_nonneg) hz

/-- **Stable systems have their poles in a half-plane `re z ≤ -α` with `α > 0`.** If `ẋ = A x`
is exponentially stable in the Euclidean norm, for instance by
`Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check`, there is `α > 0` such that
every pole `z` of every entry of the transfer function (`meromorphicOrderAt (H · i j) z < 0`) has
`re z ≤ -α`. -/
theorem exists_pos_re_le_of_meromorphicOrderAt_neg_of_isExponentiallyStable
    (hA : (toEuclideanCLM (𝕜 := ℝ) S.A).IsExponentiallyStable) :
    ∃ α > 0, ∀ (i : p) (j : m) (z : ℂ),
      meromorphicOrderAt (fun s => S.transferFunction s i j) z < 0 → z.re ≤ -α :=
  let ⟨_, α, hα, h⟩ := hA
  ⟨α, hα, fun i j _ hz => S.re_le_of_meromorphicOrderAt_transferFunction_neg
    (abs_exp_smul_apply_le_of_forall_norm_le h) i j hz⟩

/-! ### The transfer-function theorem -/

variable {S} [Fintype m] [Fintype p] {u : ℝ → m → ℝ} {x : ℝ → n → ℝ}

set_option linter.unusedFintypeInType false in
/-- The complexified output is the feedthrough plus causal convolutions. -/
private theorem ofReal_output_apply (hx : S.IsSolutionOn u x (Ici 0)) (hx₀ : x 0 = 0)
    (hu : ContinuousOn u (Ici 0)) {t : ℝ} (ht : 0 ≤ t) (i : p) :
    (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ) = ∑ j, (S.D i j : ℂ) * (u t j : ℂ) +
      ∑ j, causalConvolution (ContinuousLinearMap.mul ℂ ℂ)
        (fun τ => (S.responseKernel τ i j : ℂ)) (fun τ => (u τ j : ℂ)) t := by
  rw [hx.output_eq_Ici hu ht, hx₀]
  simp only [mulVec_zero, zero_add]
  have hcont : ∀ j, ContinuousOn (fun τ => S.responseKernel (t - τ) i j * u τ j) (uIcc 0 t) :=
    fun j => (((continuous_responseKernel_apply S i j).comp
      (continuous_const.sub continuous_id)).continuousOn).mul
      (((continuous_apply j).comp_continuousOn hu).mono (by
        rw [uIcc_of_le ht]; exact Icc_subset_Ici_self))
  have hv : IntervalIntegrable (fun τ => S.responseKernel (t - τ) *ᵥ u τ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable (continuousOn_pi.2 fun i' => ?_)
    simp only [mulVec, dotProduct]
    exact continuousOn_finsetSum _ fun j _ => (((continuous_responseKernel_apply S i' j).comp
      (continuous_const.sub continuous_id)).continuousOn).mul
      (((continuous_apply j).comp_continuousOn hu).mono (by
        rw [uIcc_of_le ht]; exact Icc_subset_Ici_self))
  have hi : (∫ τ in (0 : ℝ)..t, S.responseKernel (t - τ) *ᵥ u τ) i =
      ∑ j, ∫ τ in (0 : ℝ)..t, S.responseKernel (t - τ) i j * u τ j := by
    calc (∫ τ in (0 : ℝ)..t, S.responseKernel (t - τ) *ᵥ u τ) i =
          ∫ τ in (0 : ℝ)..t, (S.responseKernel (t - τ) *ᵥ u τ) i :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : p => ℝ) i).intervalIntegral_comp_comm
          hv).symm
      _ = _ := by
        simp only [mulVec, dotProduct]
        exact intervalIntegral.integral_finsetSum fun j _ => (hcont j).intervalIntegrable
  rw [Pi.add_apply, hi, Complex.ofReal_add]
  congr 1
  · simp [mulVec, dotProduct]
  · push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [causalConvolution, ← intervalIntegral.integral_ofReal]
    push_cast
    rfl

set_option linter.unusedFintypeInType false in
/-- The complexified output on `(0, ∞)`, in functional form. -/
private theorem eqOn_output (hx : S.IsSolutionOn u x (Ici 0)) (hx₀ : x 0 = 0)
    (hu : ContinuousOn u (Ici 0)) (i : p) :
    EqOn (fun t => (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ))
      (fun t => ∑ j, (S.D i j : ℂ) * (u t j : ℂ) +
        ∑ j, causalConvolution (ContinuousLinearMap.mul ℂ ℂ)
          (fun τ => (S.responseKernel τ i j : ℂ)) (fun τ => (u τ j : ℂ)) t) (Ioi 0) :=
  fun _ ht => ofReal_output_apply hx hx₀ hu (le_of_lt ht) i

set_option linter.unusedFintypeInType false in
private theorem laplaceConvergent_output_apply (hx : S.IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) (hu : ContinuousOn u (Ici 0))
    (huL : LaplaceConvergent (fun t j => (u t j : ℂ)) s)
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re)
    (i : p) : LaplaceConvergent (fun t => (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ)) s := by
  refine LaplaceConvergent.congr ?_ (eqOn_output hx hx₀ hu i).symm
  exact (LaplaceConvergent.sum fun j _ => (huL.apply j).const_mul _).add
    (LaplaceConvergent.sum fun j _ => laplaceConvergent_causalConvolution _
      (S.laplaceConvergent_responseKernel hA hs i j) (huL.apply j))

/-- **Convergence of the transform of the output.** For a solution on `[0, ∞)` with zero
initial state, driven by an input continuous on `[0, ∞)` whose transform converges at `s`, the
transform of the output `y = C x + D u`, read over `ℂ`, converges at every such `s` with
`ω < re s`, where `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`. -/
theorem IsSolutionOn.laplaceConvergent_output (hx : S.IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) (hu : ContinuousOn u (Ici 0))
    (huL : LaplaceConvergent (fun t j => (u t j : ℂ)) s)
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    LaplaceConvergent (fun t i => (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ)) s :=
  laplaceConvergent_pi_iff.2 fun i => laplaceConvergent_output_apply hx hx₀ hu huL hA hs i

/-- **The transfer-function theorem** `laplace y s = H s *ᵥ laplace u s`. Let `x` solve the state
equation on `[0, ∞)` with zero initial state `x 0 = 0`, driven by an input `u` continuous on
`[0, ∞)`, and let `|exp (t • A) i j| ≤ M exp (ω t)` for `t > 0`. For every `s` with `ω < re s` at
which the transform of `u` converges, the output `y = C x + D u`, read over `ℂ`, has
`laplace y s = H s *ᵥ laplace u s`, where `H s = C (s I - A)⁻¹ B + D` is the transfer function,
including the feedthrough `D`. -/
theorem IsSolutionOn.laplace_output (hx : S.IsSolutionOn u x (Ici 0)) (hx₀ : x 0 = 0)
    (hu : ContinuousOn u (Ici 0)) (huL : LaplaceConvergent (fun t j => (u t j : ℂ)) s)
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    laplace (fun t i => (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ)) s =
      S.transferFunction s *ᵥ laplace (fun t j => (u t j : ℂ)) s := by
  funext i
  rw [laplace_apply (hx.laplaceConvergent_output hx₀ hu huL hA hs),
    laplace_congr (eqOn_output hx hx₀ hu i),
    laplace_add (LaplaceConvergent.sum fun j _ => (huL.apply j).const_mul _)
      (LaplaceConvergent.sum fun j _ => laplaceConvergent_causalConvolution _
        (S.laplaceConvergent_responseKernel hA hs i j) (huL.apply j)),
    laplace_sum fun j _ => (huL.apply j).const_mul _,
    laplace_sum fun j _ => laplaceConvergent_causalConvolution _
        (S.laplaceConvergent_responseKernel hA hs i j) (huL.apply j),
    ← Finset.sum_add_distrib]
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [laplace_const_mul, laplace_causalConvolution _
      (S.laplaceConvergent_responseKernel hA hs i j) (huL.apply j),
    ContinuousLinearMap.mul_apply', S.laplace_responseKernel_eq_transferFunction_sub hA hs,
    laplace_apply huL]
  ring

/-- **The transfer-function theorem for an input of exponential order.** As
`LTISystem.IsSolutionOn.laplace_output`, with the convergence of the input's transform replaced
by the bound `‖u t‖ ≤ K exp (σ t)` for `t > 0`: then `laplace y s = H s *ᵥ laplace u s` for every
`s` with `σ < re s` and `ω < re s`. -/
theorem IsSolutionOn.laplace_output_of_norm_le {K σ : ℝ} (hx : S.IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) (hu : ContinuousOn u (Ici 0))
    (huK : ∀ t ∈ Ioi (0 : ℝ), ‖u t‖ ≤ K * Real.exp (σ * t)) (hσ : σ < s.re)
    (hA : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • S.A) i j| ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    laplace (fun t i => (((S.C *ᵥ x t + S.D *ᵥ u t) i : ℝ) : ℂ)) s =
      S.transferFunction s *ᵥ laplace (fun t j => (u t j : ℂ)) s := by
  have hmeas : AEStronglyMeasurable (fun t j => (u t j : ℂ)) (volume.restrict (Ioi 0)) :=
    ContinuousOn.aestronglyMeasurable (continuousOn_pi.2 fun j =>
      Complex.continuous_ofReal.comp_continuousOn
        (((continuous_apply j).comp_continuousOn hu).mono Ioi_subset_Ici_self)) measurableSet_Ioi
  have hb : ∀ t ∈ Ioi (0 : ℝ), ‖(fun j => (u t j : ℂ))‖ ≤ K * Real.exp (σ * t) := fun t ht =>
    (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (huK t ht))).2 fun j => by
      rw [Complex.norm_real]
      exact (norm_le_pi_norm (u t) j).trans (huK t ht)
  exact hx.laplace_output hx₀ hu (laplaceConvergent_of_norm_le_exp hmeas hb hσ)
    hA hs

end LTISystem
