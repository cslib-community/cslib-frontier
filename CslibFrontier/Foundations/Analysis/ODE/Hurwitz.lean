/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/Hurwitz.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.ImpulseBounds
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hurwitz matrices and the Lyapunov characterization

A real square matrix `A` is *Hurwitz* (`Matrix.IsHurwitz`) when every complex eigenvalue of `A`,
i.e. every point of the spectrum of `A` read over `ℂ`, has negative real part; equivalently every
complex root of the characteristic polynomial does (`Matrix.isHurwitz_iff_isRoot_charpoly`). This
module proves the classical characterizations of Hurwitz matrices for the finite-dimensional real
linear system `ẋ = A x`, for every `A`, diagonalizable or not:

* **Spectrum and stability.** `A` is Hurwitz iff `ẋ = A x` is exponentially stable in the
  Euclidean norm (`Matrix.isHurwitz_iff_isExponentiallyStable`). More precisely, a decay bound
  `‖x t‖ ≤ M exp (-α t) ‖x 0‖` for all trajectories puts the spectrum in `re μ ≤ -α`
  (`Matrix.re_le_of_forall_norm_le`).
* **The Lyapunov equation.** If `A` is Hurwitz, then for every `Q` the Lyapunov equation
  `Aᵀ P + P A = -Q` has exactly one solution (`Matrix.IsHurwitz.existsUnique_lyapunov_eq`); it is
  symmetric when `Q` is (`Matrix.IsHurwitz.isHermitian_of_lyapunov_eq`) and positive definite
  when `Q` is (`Matrix.IsHurwitz.posDef_of_lyapunov_eq`); packaged as
  `Matrix.IsHurwitz.existsUnique_isHermitian_lyapunov_eq` and
  `Matrix.IsHurwitz.existsUnique_posDef_lyapunov_eq`. Conversely, `A` is Hurwitz iff every
  `Q ≻ 0` admits a solution `P ≻ 0` (`Matrix.isHurwitz_iff_forall_posDef_exists_posDef`, and
  with uniqueness `Matrix.isHurwitz_iff_forall_posDef_existsUnique_posDef`), iff some `P ≻ 0`
  has `-(Aᵀ P + P A) ≻ 0` (`Matrix.isHurwitz_iff_exists_posDef`).

When `Q = Cᵀ C`, the solution is the Gramian `∫₀^∞ exp (t Aᵀ) Q exp (t A) dt` entrywise, by
`Matrix.dotProduct_mulVec_eq_integral`.

## Proof route

*Stability gives the spectral bound.* An eigenvector `v` of `A` over `ℂ` for `μ` satisfies
`exp (t A) v = exp (t μ) v` (`Matrix.exp_smul_mulVec_eq_of_pow_mulVec_eq_zero` with `k = 1`). The
real and imaginary parts of `v` are real initial states, whose trajectories bound
`exp (t re μ) ‖v‖`, so `exp (t (re μ + α))` stays bounded.

*The spectral bound gives stability, without diagonalization.* For a generalized eigenvector `v`,
`(A - μ)ᵏ v = 0`, the exponential series terminates:
`exp (t A) v = exp (t μ) ∑_{j < k} tʲ / j! (A - μ)ʲ v`
(`Matrix.exp_smul_mulVec_eq_of_pow_mulVec_eq_zero`), which tends to `0` when `re μ < 0`. The
generalized eigenspaces span `ℂⁿ` (`Module.End.iSup_maxGenEigenspace_eq_top`), so
`exp (t A) → 0` (`Matrix.IsHurwitz.tendsto_exp_smul`). For any bounded operator on a real Banach
space, `exp (t A) → 0` is equivalent to exponential stability: once `‖exp (T A)‖ ≤ 1/2`, the
semigroup property gives the rate `log 2 / T`
(`ContinuousLinearMap.isExponentiallyStable_iff_tendsto_exp_smul`).

*The Lyapunov equation.* If `Aᵀ X + X A = 0` then `X exp (t A) = exp (-t Aᵀ) X`, so
`exp (t Aᵀ) X exp (t A) = X` for all `t`, and the left side tends to `0`: the linear map
`X ↦ Aᵀ X + X A` is injective, hence bijective in finite dimension. Along a trajectory the energy
`xᵀ P x` has derivative `-xᵀ Q x ≤ 0` and tends to `0`, so `P ⪰ 0`; and `xᵀ P x = 0` forces
`P x = 0`, hence `xᵀ Q x = -xᵀ (Aᵀ P + P A) x = 0`, so `x = 0`.

## Main definitions

* `Matrix.IsHurwitz`: every eigenvalue of the real matrix `A` over `ℂ` has negative real part.

## Main results

* `ContinuousLinearMap.isExponentiallyStable_iff_tendsto_exp_smul`
* `Matrix.exp_smul_mulVec_eq_of_pow_mulVec_eq_zero`
* `Matrix.re_le_of_forall_norm_le`
* `Matrix.isHurwitz_iff_isExponentiallyStable`
* `Matrix.IsHurwitz.existsUnique_lyapunov_eq`, `Matrix.IsHurwitz.posDef_of_lyapunov_eq`
* `Matrix.IsHurwitz.existsUnique_isHermitian_lyapunov_eq`,
  `Matrix.IsHurwitz.existsUnique_posDef_lyapunov_eq`
* `Matrix.isHurwitz_iff_forall_posDef_exists_posDef`,
  `Matrix.isHurwitz_iff_forall_posDef_existsUnique_posDef`, `Matrix.isHurwitz_iff_exists_posDef`

## References

* S. Boyd, L. El Ghaoui, E. Feron and V. Balakrishnan, *Linear Matrix Inequalities in System and
  Control Theory*, 1994, §1.2 and §2.7, for the Lyapunov characterization of stable matrices. The
  results here are the standard finite-dimensional statements, proved without diagonalization.
-/

public section

open Set Filter Topology NormedSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A : E →L[ℝ] E}

/-- **Exponential stability is decay of the flow.** For a bounded operator `A` on a real Banach
space, `ẋ = A x` is exponentially stable iff `exp (t • A) → 0` in operator norm as `t → ∞`. -/
theorem isExponentiallyStable_iff_tendsto_exp_smul :
    A.IsExponentiallyStable ↔ Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  constructor
  · rintro ⟨M, α, hα, hM⟩
    have hb : ∀ t ≥ 0, ‖exp (t • A)‖ ≤ |M| * Real.exp (-(α * t)) := fun t ht =>
      opNorm_le_bound _ (by positivity) fun y => by
        have h := hM _ (isTrajectoryOn_exp_smul_apply A y _) t ht
        simp only [zero_smul, exp_zero] at h
        exact h.trans <| mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le) (norm_nonneg y)
    have hlim : Tendsto (fun t => |M| * Real.exp (-(α * t))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hα))).const_mul |M|
    exact squeeze_zero_norm' (eventually_atTop.2 ⟨0, hb⟩) hlim
  · intro h
    let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
    obtain ⟨T, hT, hT0⟩ := ((tendsto_norm_zero.comp h).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and (eventually_gt_atTop 0) |>.exists
    simp only [Function.comp_apply] at hT
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (f := fun s : ℝ => exp (s • A))
      (exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT0.le⟩)
    have hpow : ∀ (q : ℕ) (y : E), ‖(exp (T • A) ^ q) y‖ ≤ (1 / 2) ^ q * ‖y‖ := by
      intro q y
      induction q with
      | zero => simp
      | succ q ih =>
        rw [pow_succ']
        change ‖exp (T • A) ((exp (T • A) ^ q) y)‖ ≤ _
        calc _ ≤ 1 / 2 * ((1 / 2) ^ q * ‖y‖) :=
              (le_opNorm _ _).trans (mul_le_mul hT.le ih (norm_nonneg _) (by norm_num))
          _ = _ := by ring
    refine ⟨2 * K, Real.log 2 / T, div_pos (Real.log_pos one_lt_two) hT0, fun x hx t ht => ?_⟩
    set q := ⌊t / T⌋₊
    set s := t - q * T
    have hqt : (q : ℝ) * T ≤ t := (le_div_iff₀ hT0).1 (Nat.floor_le (div_nonneg ht hT0.le))
    have htq : t < (q + 1) * T := (div_lt_iff₀ hT0).1 (Nat.lt_floor_add_one _)
    have hs : s ∈ Icc 0 T := ⟨by simp only [s]; linarith, by simp only [s]; linarith⟩
    have hsplit : exp (t • A) = exp (s • A) * exp (T • A) ^ q := by
      have : t • A = s • A + q • (T • A) := by
        rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← add_smul]
        simp only [s]
        ring_nf
      rw [this, exp_add_of_commute (((Commute.refl A).smul_left s).smul_right T |>.smul_right q),
        exp_nsmul]
    rw [hx.eqOn_exp_smul_apply_Ici ht]
    dsimp only
    rw [hsplit]
    change ‖exp (s • A) ((exp (T • A) ^ q) (x 0))‖ ≤ _
    have h2 : ((1 : ℝ) / 2) ^ q ≤ 2 * Real.exp (-(Real.log 2 / T * t)) := by
      rw [one_div, inv_pow, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
        ← Real.exp_neg, ← Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.2 ?_
      have : Real.log 2 / T * t = Real.log 2 * (t / T) := by ring
      nlinarith [Real.log_pos one_lt_two, (div_lt_iff₀ hT0).2 htq]
    calc ‖exp (s • A) ((exp (T • A) ^ q) (x 0))‖ ≤ K * ((1 / 2) ^ q * ‖x 0‖) :=
          (le_opNorm _ _).trans (mul_le_mul (hK s hs) (hpow q _) (norm_nonneg _) hK0)
      _ ≤ K * (2 * Real.exp (-(Real.log 2 / T * t)) * ‖x 0‖) := by gcongr
      _ = 2 * K * Real.exp (-(Real.log 2 / T * t)) * ‖x 0‖ := by ring

end ContinuousLinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real square matrix is **Hurwitz** when every eigenvalue over `ℂ`, i.e. every point of the
spectrum of `A` read as a complex matrix, has negative real part. Repeated and defective
eigenvalues are allowed. See `Matrix.isHurwitz_iff_isRoot_charpoly` for the characteristic
polynomial form. -/
@[expose] def IsHurwitz (A : Matrix n n ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), μ.re < 0

/-- `A` is Hurwitz iff every complex root of its characteristic polynomial has negative real
part. -/
theorem isHurwitz_iff_isRoot_charpoly {A : Matrix n n ℝ} :
    A.IsHurwitz ↔ ∀ μ : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ → μ.re < 0 := by
  simp only [IsHurwitz, mem_spectrum_iff_isRoot_charpoly, charpoly_map]

/-- **The flow on a generalized eigenvector.** If `(M - μ)ᵏ v = 0` for a complex matrix `M`, the
exponential series applied to `v` terminates:
`exp (t M) v = exp (t μ) ∑_{j < k} tʲ / j! (M - μ)ʲ v`. With `k = 1`, `exp (t M) v = exp (t μ) v`
for an eigenvector. -/
theorem exp_smul_mulVec_eq_of_pow_mulVec_eq_zero {M : Matrix n n ℂ} {μ : ℂ} {v : n → ℂ} {k : ℕ}
    (hv : ((M - μ • 1) ^ k) *ᵥ v = 0) (t : ℂ) :
    exp (t • M) *ᵥ v = Complex.exp (t * μ) •
      ∑ j ∈ Finset.range k, (t ^ j / j.factorial) • ((M - μ • 1) ^ j *ᵥ v) := by
  set N := M - μ • 1
  have hsplit : t • M = t • N + (t * μ) • (1 : Matrix n n ℂ) := by
    simp only [N, smul_sub, smul_smul, sub_add_cancel]
  have hcomm : Commute (t • N) ((t * μ) • (1 : Matrix n n ℂ)) := (Commute.one_right _).smul_right _
  have hscalar : exp ((t * μ) • (1 : Matrix n n ℂ)) = Complex.exp (t * μ) • 1 := by
    open scoped Matrix.Norms.Operator in
    have h := algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := Matrix n n ℂ) (t * μ)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
    exact Complex.exp_eq_exp_ℂ ▸ h.symm
  have hser : HasSum (fun j => ((j.factorial : ℂ)⁻¹ • (t • N) ^ j) *ᵥ v) (exp (t • N) *ᵥ v) := by
    open scoped Matrix.Norms.Operator in
    exact (exp_series_hasSum_exp' (𝕂 := ℂ) (t • N)).map (mulVec.addMonoidHomLeft v)
      (continuous_id.matrix_mulVec continuous_const)
  have hterm : ∀ j, ((j.factorial : ℂ)⁻¹ • (t • N) ^ j) *ᵥ v =
      (t ^ j / j.factorial) • (N ^ j *ᵥ v) := fun j => by
    rw [smul_pow, smul_smul, smul_mulVec, div_eq_inv_mul]
  have hfin : HasSum (fun j => ((j.factorial : ℂ)⁻¹ • (t • N) ^ j) *ᵥ v)
      (∑ j ∈ Finset.range k, (t ^ j / j.factorial) • (N ^ j *ᵥ v)) := by
    simp only [hterm]
    refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    have hNj : N ^ j = N ^ (j - k) * N ^ k := by rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hNj, ← mulVec_mulVec, hv, mulVec_zero, smul_zero]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, hscalar, mul_smul_comm, mul_one, smul_mulVec,
    hser.unique hfin]

/-- The exponential of a real matrix, read over `ℂ`, is the exponential of the complex matrix. -/
theorem map_algebraMap_exp_smul (A : Matrix n n ℝ) (t : ℝ) :
    (exp (t • A)).map (algebraMap ℝ ℂ) = exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) := by
  have h : (t • A).map (algebraMap ℝ ℂ) = (t : ℂ) • A.map (algebraMap ℝ ℂ) := by
    ext i j
    simp
  rw [← h]
  open scoped Matrix.Norms.Operator in
  exact map_exp_of_mem_ball (𝕂 := ℝ) ((algebraMap ℝ ℂ).mapMatrix)
    (continuous_id.matrix_map Complex.continuous_ofReal) (t • A)
    ((expSeries_radius_eq_top ℝ (Matrix n n ℝ)).symm ▸ edist_lt_top _ _)

/-- **Hurwitz matrices have decaying flows.** If `A` is Hurwitz, then `exp (t • A) → 0` as
`t → ∞`. Each generalized eigenvector over `ℂ` decays by
`Matrix.exp_smul_mulVec_eq_of_pow_mulVec_eq_zero`, and generalized eigenvectors span `ℂⁿ`; no
diagonalization is used. -/
theorem IsHurwitz.tendsto_exp_smul {A : Matrix n n ℝ} (hA : A.IsHurwitz) :
    Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  set Ac := A.map (algebraMap ℝ ℂ)
  let S : Submodule ℂ (n → ℂ) :=
    { carrier := {v | Tendsto (fun t : ℝ => exp ((t : ℂ) • Ac) *ᵥ v) atTop (𝓝 0)}
      add_mem' := fun {a b} ha hb => by
        simpa only [Set.mem_ofPred_eq, mulVec_add, add_zero] using ha.add hb
      zero_mem' := by simpa only [Set.mem_ofPred_eq, mulVec_zero] using tendsto_const_nhds
      smul_mem' := fun c v hv => by
        simpa only [Set.mem_ofPred_eq, mulVec_smul, smul_zero] using hv.const_smul c }
  have hgen : ∀ μ, Module.End.maxGenEigenspace (toLin' Ac) μ ≤ S := by
    intro μ v hv
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
    have hk' : ((Ac - μ • 1) ^ k) *ᵥ v = 0 := by
      have e : toLin' Ac - μ • 1 = toLin' (Ac - μ • 1) := by
        rw [map_sub, map_smul, toLin'_one, Module.End.one_eq_id]
      rwa [e, ← toLin'_pow, toLin'_apply] at hk
    by_cases hμ : μ ∈ spectrum ℂ Ac
    · have hc : 0 < -μ.re := neg_pos.2 (hA μ hμ)
      change Tendsto _ atTop _
      simp_rw [exp_smul_mulVec_eq_of_pow_mulVec_eq_zero hk', Finset.smul_sum]
      rw [← Finset.sum_const_zero (s := Finset.range k)]
      refine tendsto_finsetSum _ fun j _ => ?_
      set w := (Ac - μ • 1) ^ j *ᵥ v
      have hp : Tendsto (fun t : ℝ => t ^ j * Real.exp (μ.re * t)) atTop (𝓝 0) := by
        simpa only [mul_zero] using (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
          (tendsto_id.const_mul_atTop hc)).const_mul ((-μ.re)⁻¹ ^ j)).congr fun t => by
          dsimp only [Function.comp_apply, id]
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel_left₀ hc.ne', neg_mul, neg_neg]
      refine squeeze_zero_norm' (eventually_atTop.2 ⟨0, fun t ht => le_of_eq ?_⟩)
        (by simpa using hp.mul_const (‖w‖ / j.factorial))
      rw [norm_smul, norm_smul, Complex.norm_exp, norm_div, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg ht, Complex.norm_natCast]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring_nf
    · have hu : IsUnit (Ac - μ • 1) := by
        rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hμ
        simpa only [neg_sub] using hμ.neg
      have hv0 : v = 0 := (mulVec_injective_iff_isUnit.2 (hu.pow k)) (by rw [hk', mulVec_zero])
      exact hv0.symm ▸ S.zero_mem
  have key (v : n → ℂ) : Tendsto (fun t : ℝ => exp ((t : ℂ) • Ac) *ᵥ v) atTop (𝓝 0) :=
    (Module.End.iSup_maxGenEigenspace_eq_top (toLin' Ac) ▸ iSup_le hgen) Submodule.mem_top
  have hcol : ∀ y : n → ℝ, Tendsto (fun t : ℝ => exp (t • A) *ᵥ y) atTop (𝓝 0) := by
    intro y
    have e : ∀ t : ℝ, exp ((t : ℂ) • Ac) *ᵥ (fun i => (y i : ℂ)) =
        fun i => ((exp (t • A) *ᵥ y) i : ℂ) := by
      intro t
      rw [← map_algebraMap_exp_smul]
      ext i
      simp [mulVec, dotProduct]
    have h := key fun i => (y i : ℂ)
    simp_rw [e] at h
    have hre := ((continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)).tendsto
      0).comp h
    simp only [Function.comp_def, Complex.ofReal_re] at hre
    exact hre
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simpa [Function.comp_def, mulVec_single_one] using
    ((continuous_apply i).tendsto _).comp (hcol (Pi.single j 1))

/-- A Hurwitz matrix gives an exponentially stable system `ẋ = A x` in the Euclidean norm. -/
theorem IsHurwitz.isExponentiallyStable {A : Matrix n n ℝ} (hA : A.IsHurwitz) :
    (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable := by
  rw [ContinuousLinearMap.isExponentiallyStable_iff_tendsto_exp_smul]
  have hc : Continuous (toEuclideanCLM (n := n) (𝕜 := ℝ)) :=
    (toEuclideanCLM (n := n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  simpa [Function.comp_def, ← map_smul, ← toEuclideanCLM_exp] using
    (hc.tendsto 0).comp hA.tendsto_exp_smul

/-- **A decay rate bounds the spectrum.** If every trajectory of `ẋ = A x` on `[0, ∞)` satisfies
`‖x t‖ ≤ M exp (-α t) ‖x 0‖` in the Euclidean norm, then every eigenvalue `μ` of `A` over `ℂ`
has `re μ ≤ -α`. -/
theorem re_le_of_forall_norm_le {A : Matrix n n ℝ} {M α : ℝ}
    (h : ∀ x : ℝ → EuclideanSpace ℝ n, (toEuclideanCLM (𝕜 := ℝ) A).IsTrajectoryOn x (Ici 0) →
      ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) : μ.re ≤ -α := by
  set Ac := A.map (algebraMap ℝ ℂ)
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, ← exists_mulVec_eq_zero_iff] at hμ
  obtain ⟨v, hv0, hv⟩ := hμ
  have hv' : (Ac - μ • 1) *ᵥ v = 0 := by rw [← neg_sub, neg_mulVec, hv, neg_zero]
  have hflow : ∀ t : ℝ, (exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v = Complex.exp (t * μ) • v := by
    intro t
    rw [map_algebraMap_exp_smul,
      exp_smul_mulVec_eq_of_pow_mulVec_eq_zero (k := 1) (by rwa [pow_one])]
    simp
  set a : n → ℝ := fun i => (v i).re
  set b : n → ℝ := fun i => (v i).im
  have hn : ∀ z : n → ℝ, ‖WithLp.toLp 2 z‖ ^ 2 = z ⬝ᵥ z := fun z => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  have hb : ∀ y : n → ℝ, ∀ t ≥ 0, (exp (t • A) *ᵥ y) ⬝ᵥ (exp (t • A) *ᵥ y) ≤
      M ^ 2 * Real.exp (-(2 * α * t)) * (y ⬝ᵥ y) := by
    intro y t ht
    have hx := (isTrajectoryOn_toEuclideanCLM_iff (x := fun t => exp (t • A) *ᵥ y)).2
      (hasDerivWithinAt_exp_smul_mulVec A y)
    have h1 := h _ hx t ht
    simp only [zero_smul, exp_zero, one_mulVec] at h1
    rw [← hn, ← hn]
    calc _ ≤ (M * Real.exp (-(α * t)) * ‖WithLp.toLp 2 y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
          ring_nf
  have hsum : a ⬝ᵥ a + b ⬝ᵥ b = ∑ i, Complex.normSq (v i) := by
    simp [a, b, dotProduct, Complex.normSq_apply, Finset.sum_add_distrib]
  have hS : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    rw [hsum]
    exact (Complex.normSq_pos.2 hi).trans_le
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i))
  have hcoord : ∀ t : ℝ, ∀ i, (exp (t • A) *ᵥ a) i = (Complex.exp (t * μ) * v i).re ∧
      (exp (t • A) *ᵥ b) i = (Complex.exp (t * μ) * v i).im := by
    intro t i
    have e := congrFun (hflow t) i
    simp only [mulVec, dotProduct, map_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [← e]
    constructor <;> simp [mulVec, dotProduct, a, b, Complex.re_sum, Complex.im_sum]
  have hE : ∀ t : ℝ, (exp (t • A) *ᵥ a) ⬝ᵥ (exp (t • A) *ᵥ a) +
      (exp (t • A) *ᵥ b) ⬝ᵥ (exp (t • A) *ᵥ b) = Real.exp (2 * t * μ.re) * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    intro t
    rw [hsum, Finset.mul_sum, dotProduct, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hcoord t i).1, (hcoord t i).2, ← Complex.normSq_apply, Complex.normSq_mul,
      Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.re_ofReal_mul, sq, ← Real.exp_add]
    ring_nf
  by_contra! hlt
  set c := μ.re + α
  have hc : 0 < c := by simp only [c]; linarith
  set t := (M ^ 2 + 1) / (2 * c)
  have ht : 0 ≤ t := by positivity
  have hk : Real.exp (2 * t * μ.re) * (a ⬝ᵥ a + b ⬝ᵥ b) ≤
      M ^ 2 * Real.exp (-(2 * α * t)) * (a ⬝ᵥ a + b ⬝ᵥ b) :=
    calc _ = _ := (hE t).symm
      _ ≤ _ := add_le_add (hb a t ht) (hb b t ht)
      _ = _ := by ring
  have hk' := le_of_mul_le_mul_right hk hS
  have hexp : Real.exp (2 * t * c) ≤ M ^ 2 :=
    calc Real.exp (2 * t * c) = Real.exp (2 * t * μ.re) * Real.exp (2 * α * t) := by
          rw [← Real.exp_add]
          simp only [c]
          ring_nf
      _ ≤ M ^ 2 * Real.exp (-(2 * α * t)) * Real.exp (2 * α * t) :=
          mul_le_mul_of_nonneg_right hk' (Real.exp_pos _).le
      _ = M ^ 2 := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have h3 : 2 * t * c = M ^ 2 + 1 := by simp only [t]; field_simp
  linarith [Real.add_one_le_exp (2 * t * c)]

/-- **Exponential stability gives a Hurwitz matrix.** -/
theorem isHurwitz_of_isExponentiallyStable {A : Matrix n n ℝ}
    (hA : (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable) : A.IsHurwitz := by
  obtain ⟨M, α, hα, h⟩ := hA
  exact fun μ hμ => (re_le_of_forall_norm_le h hμ).trans_lt (neg_neg_of_pos hα)

/-- **Hurwitz iff exponentially stable.** A real square matrix `A` is Hurwitz iff `ẋ = A x` is
exponentially stable in the Euclidean norm: there are `M` and `α > 0` with
`‖x t‖ ≤ M exp (-α t) ‖x 0‖` for every trajectory on `[0, ∞)` and every `t ≥ 0`. -/
theorem isHurwitz_iff_isExponentiallyStable {A : Matrix n n ℝ} :
    A.IsHurwitz ↔ (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable :=
  ⟨IsHurwitz.isExponentiallyStable, isHurwitz_of_isExponentiallyStable⟩

/-! ### The Lyapunov equation -/

/-- **Uniqueness for the homogeneous Lyapunov equation.** If `A` is Hurwitz and
`Aᵀ X + X A = 0`, then `X = 0`: `X exp (t A) = exp (-t Aᵀ) X`, so `exp (t Aᵀ) X exp (t A) = X`
for all `t`, and the left side tends to `0`. `X` need not be symmetric. -/
theorem IsHurwitz.eq_zero_of_lyapunov_eq_zero {A X : Matrix n n ℝ} (hA : A.IsHurwitz)
    (hX : Aᵀ * X + X * A = 0) : X = 0 := by
  have hF : ∀ t : ℝ, exp (t • Aᵀ) * X * exp (t • A) = X := by
    intro t
    have hsc : SemiconjBy X (t • A) (t • -Aᵀ) := by
      rw [SemiconjBy, mul_smul_comm, smul_mul_assoc, neg_mul, eq_neg_of_add_eq_zero_right hX]
    have hsc' : X * exp (t • A) = exp (t • -Aᵀ) * X := by
      open scoped Matrix.Norms.Operator in
      exact hsc.exp_right
    rw [mul_assoc, hsc', ← mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Aᵀ).neg_right).smul_left t |>.smul_right t), smul_neg, add_neg_cancel,
      exp_zero, one_mul]
  have hE := hA.tendsto_exp_smul
  have hET : Tendsto (fun t : ℝ => exp (t • Aᵀ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, ← transpose_smul, exp_transpose] using
      (continuous_id.matrix_transpose.tendsto 0).comp hE
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun t => (hF t).symm)
    (by simpa only [zero_mul] using (hET.mul_const X).mul hE)

/-- **Existence and uniqueness for the Lyapunov equation.** If `A` is Hurwitz, then for every
real matrix `Q` the Lyapunov equation `Aᵀ P + P A = -Q` has exactly one solution `P` among all
real matrices: the linear map `P ↦ Aᵀ P + P A` is injective
(`Matrix.IsHurwitz.eq_zero_of_lyapunov_eq_zero`), hence bijective. -/
theorem IsHurwitz.existsUnique_lyapunov_eq {A : Matrix n n ℝ} (hA : A.IsHurwitz)
    (Q : Matrix n n ℝ) : ∃! P : Matrix n n ℝ, Aᵀ * P + P * A = -Q := by
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun P => Aᵀ * P + P * A
      map_add' := fun P P' => by rw [mul_add, add_mul]; abel
      map_smul' := fun c P => by
        rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_add] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun X hX => hA.eq_zero_of_lyapunov_eq_zero hX
  obtain ⟨P, hP⟩ := LinearMap.injective_iff_surjective.1 hinj (-Q)
  exact ⟨P, hP, fun P' hP' => hinj (hP'.trans hP.symm)⟩

/-- If `A` is Hurwitz and `Q` is symmetric, the solution of `Aᵀ P + P A = -Q` is symmetric: `Pᵀ`
solves the same equation. -/
theorem IsHurwitz.isHermitian_of_lyapunov_eq {A P Q : Matrix n n ℝ} (hA : A.IsHurwitz)
    (hQ : Q.IsHermitian) (hP : Aᵀ * P + P * A = -Q) : P.IsHermitian := by
  have hQ' : Qᵀ = Q := (conjTranspose_eq_transpose_of_trivial (A := Q)).symm.trans hQ
  have hPt : Aᵀ * Pᵀ + Pᵀ * A = -Q := by
    simpa only [transpose_add, transpose_mul, transpose_transpose, transpose_neg, hQ', add_comm]
      using congrArg transpose hP
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact (hA.existsUnique_lyapunov_eq Q).unique hPt hP

/-- **The Lyapunov solution is positive definite.** If `A` is Hurwitz, `Q ≻ 0` and
`Aᵀ P + P A = -Q`, then `P ≻ 0`. Along `x t = exp (t A) y` the energy `xᵀ P x` is nonincreasing
and tends to `0`, so `yᵀ P y ≥ 0`; if `yᵀ P y = 0` then `P y = 0`, so
`yᵀ Q y = -yᵀ (Aᵀ P + P A) y = 0` and `y = 0`. -/
theorem IsHurwitz.posDef_of_lyapunov_eq {A P Q : Matrix n n ℝ} (hA : A.IsHurwitz)
    (hQ : Q.PosDef) (hP : Aᵀ * P + P * A = -Q) : P.PosDef := by
  have hH := hA.isHermitian_of_lyapunov_eq hQ.isHermitian hP
  have hQy : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ Q *ᵥ y := fun y => by
    simpa using hQ.posSemidef.dotProduct_mulVec_nonneg y
  have hnonneg : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ P *ᵥ y := fun y => by
    have hle : ∀ t : ℝ, t ≥ 0 → (exp (t • A) *ᵥ y) ⬝ᵥ P *ᵥ (exp (t • A) *ᵥ y) ≤ y ⬝ᵥ P *ᵥ y :=
      fun t ht => by
        simpa using dotProduct_mulVec_le_exp_mul (P := P) (hasDerivWithinAt_exp_smul_mulVec A y)
          (K := 0) (fun z => by simpa [hP, neg_mulVec] using hQy z) ht
    have hlim : Tendsto (fun t : ℝ => (exp (t • A) *ᵥ y) ⬝ᵥ P *ᵥ (exp (t • A) *ᵥ y)) atTop
        (𝓝 0) := by
      have hc : Continuous fun z : n → ℝ => z ⬝ᵥ P *ᵥ z :=
        continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
      simpa [Function.comp_def] using (hc.tendsto 0).comp
        (tendsto_exp_smul_mulVec hA.isExponentiallyStable y)
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨0, hle⟩)
  have hpsd : P.PosSemidef := .of_dotProduct_mulVec_nonneg hH (by simpa using hnonneg)
  refine .of_dotProduct_mulVec_pos hH fun y hy => ?_
  rcases (hnonneg y).lt_or_eq with h | h
  · simpa using h
  exfalso
  have hPy : P *ᵥ y = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by simpa using h.symm)
  have hPt : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hH
  have h0 : y ⬝ᵥ (Aᵀ * P + P * A) *ᵥ y = 0 := by
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, hPy, mulVec_zero,
      dotProduct_zero, zero_add, dotProduct_mulVec, ← mulVec_transpose, hPt, hPy, zero_dotProduct]
  rw [hP, neg_mulVec, dotProduct_neg, neg_eq_zero] at h0
  exact (lt_irrefl (0 : ℝ)) (by simpa only [star_trivial, h0] using hQ.dotProduct_mulVec_pos hy)

/-- **The unique symmetric solution.** If `A` is Hurwitz and `Q` is symmetric, the Lyapunov
equation `Aᵀ P + P A = -Q` has exactly one symmetric solution. It is in fact the only solution
among all real matrices (`Matrix.IsHurwitz.existsUnique_lyapunov_eq`). -/
theorem IsHurwitz.existsUnique_isHermitian_lyapunov_eq {A Q : Matrix n n ℝ} (hA : A.IsHurwitz)
    (hQ : Q.IsHermitian) : ∃! P : Matrix n n ℝ, P.IsHermitian ∧ Aᵀ * P + P * A = -Q := by
  obtain ⟨P, hP, huniq⟩ := hA.existsUnique_lyapunov_eq Q
  exact ⟨P, ⟨hA.isHermitian_of_lyapunov_eq hQ hP, hP⟩, fun P' hP' => huniq P' hP'.2⟩

/-- **The unique positive definite solution.** If `A` is Hurwitz and `Q ≻ 0`, the Lyapunov
equation `Aᵀ P + P A = -Q` has exactly one positive definite solution, and no other solution at
all (`Matrix.IsHurwitz.existsUnique_lyapunov_eq`). -/
theorem IsHurwitz.existsUnique_posDef_lyapunov_eq {A Q : Matrix n n ℝ} (hA : A.IsHurwitz)
    (hQ : Q.PosDef) : ∃! P : Matrix n n ℝ, P.PosDef ∧ Aᵀ * P + P * A = -Q := by
  obtain ⟨P, hP, huniq⟩ := hA.existsUnique_lyapunov_eq Q
  exact ⟨P, ⟨hA.posDef_of_lyapunov_eq hQ hP, hP⟩, fun P' hP' => huniq P' hP'.2⟩

/-- **Lyapunov's theorem, with the quantifiers explicit.** A real square matrix `A` is Hurwitz iff
for every positive definite `Q` there is a positive definite `P` with `Aᵀ P + P A = -Q`. The
solution is then unique among all real matrices (`Matrix.IsHurwitz.existsUnique_lyapunov_eq`). -/
theorem isHurwitz_iff_forall_posDef_exists_posDef {A : Matrix n n ℝ} :
    A.IsHurwitz ↔ ∀ Q : Matrix n n ℝ, Q.PosDef → ∃ P : Matrix n n ℝ, P.PosDef ∧
      Aᵀ * P + P * A = -Q := by
  refine ⟨fun hA Q hQ => ?_, fun h => ?_⟩
  · obtain ⟨P, hP, -⟩ := hA.existsUnique_lyapunov_eq Q
    exact ⟨P, hA.posDef_of_lyapunov_eq hQ hP, hP⟩
  · obtain ⟨P, hP, hPQ⟩ := h 1 PosDef.one
    exact isHurwitz_of_isExponentiallyStable <|
      isExponentiallyStable_toEuclideanCLM_of_posDef hP
        (by simpa only [hPQ, neg_neg] using PosDef.one)

/-- **Lyapunov's theorem, with uniqueness.** A real square matrix `A` is Hurwitz iff for every
positive definite `Q` there is exactly one positive definite `P` with `Aᵀ P + P A = -Q`. -/
theorem isHurwitz_iff_forall_posDef_existsUnique_posDef {A : Matrix n n ℝ} :
    A.IsHurwitz ↔ ∀ Q : Matrix n n ℝ, Q.PosDef → ∃! P : Matrix n n ℝ, P.PosDef ∧
      Aᵀ * P + P * A = -Q :=
  ⟨fun hA _ hQ => hA.existsUnique_posDef_lyapunov_eq hQ, fun h =>
    isHurwitz_iff_forall_posDef_exists_posDef.2 fun Q hQ => (h Q hQ).exists⟩

/-- **Lyapunov's theorem, existential form.** A real square matrix `A` is Hurwitz iff some
positive definite `P` has `-(Aᵀ P + P A)` positive definite. -/
theorem isHurwitz_iff_exists_posDef {A : Matrix n n ℝ} :
    A.IsHurwitz ↔ ∃ P : Matrix n n ℝ, P.PosDef ∧ (-(Aᵀ * P + P * A)).PosDef := by
  refine ⟨fun hA => ?_, fun ⟨P, hP, hQ⟩ =>
    isHurwitz_of_isExponentiallyStable (isExponentiallyStable_toEuclideanCLM_of_posDef hP hQ)⟩
  obtain ⟨P, hP, hPQ⟩ := isHurwitz_iff_forall_posDef_exists_posDef.1 hA 1 PosDef.one
  exact ⟨P, hP, by rw [hPQ, neg_neg]; exact PosDef.one⟩

end Matrix
