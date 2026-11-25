/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.ChiSquare
public import CslibFrontier.Probability.MarkovChain.Mixing
public import Mathlib.Algebra.Module.LinearMap.End
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Reversible spectral gap, lazy chains, and total-variation mixing bounds

For a Markov chain `P : MarkovChain S` on a finite state space `S` and a reference distribution
`π : PMF S`, the transition operator `P.stepOp : Module.End ℝ (S → ℝ)` maps an observable `f` to
`x ↦ ∑ y, P(x, y) f(y)`. Composition of chains corresponds to composition of operators, so `stepOp`
is a monoid homomorphism (`(P ^ t).stepOp = P.stepOp ^ t`). Every eigenvalue `μ` of `P.stepOp`
satisfies `|μ| ≤ 1` (`abs_eigenvalue_le_one`, [LevinPeres2017], Lemma 12.1(i)), and when `π` is
stationary every eigenfunction with `μ ≠ 1` has `π`-expectation zero
(`IsStationary.sum_mul_eq_zero_of_stepOp_eq_smul`, Lemma 12.3).

When `P` is reversible with respect to `π`, `P.stepOp` is self-adjoint in `ℓ²(π)`
(`IsReversible.sum_mul_stepOp_comm`, `(12.1)`), and its Dirichlet form
`𝓔(f) = (1 / 2) ∑_{x, y} π(x) P(x, y) (f(x) - f(y))²` (`dirichletForm`, `(13.2)`) equals
`⟨f, f⟩_π - ⟨f, P f⟩_π` (`IsReversible.dirichletForm_eq_sub`, Lemma 13.6). On the `π`-mean-zero
functions of positive `ℓ²(π)` norm:

* `P.spectralGap π` (`γ = 1 - λ₂`, `(12.7)` and Lemma 13.7 `(13.3)`) is the infimum of
  `𝓔(f) / ⟨f, f⟩_π`;
* `P.spectralContraction π` (`λ_*`, `(12.6)` and `(12.8)`) is the supremum of
  `√(⟨P f, P f⟩_π / ⟨f, f⟩_π)`, which for reversible `P` equals the supremum of
  `|⟨f, P f⟩_π| / ⟨f, f⟩_π` (`IsReversible.spectralContraction_eq_ciSup_abs`);
* `P.absSpectralGap π` (`γ_* := 1 - λ_*`, Section 12.2) is the absolute spectral gap.

When `S` has at least two states and `π` is strictly positive, conjugating `P.stepOp` into
`EuclideanSpace ℝ S` by `D_π^{1/2}` (`Lemma 12.2`) produces non-constant eigenfunctions of
`P.stepOp` achieving `|μ| = λ_*` (`IsReversible.exists_eigenfunction_abs_eq_spectralContraction`)
and `μ = 1 - γ` (`IsReversible.exists_eigenfunction_eq_one_sub_spectralGap`), matching the
eigenvalue definitions `(12.6)` and `(12.7)`.

Passing to the lazy chain `P.lazy` (`(I + P) / 2`, Section 1.3) preserves stationarity and
reversibility, makes the transition operator positive semidefinite in `ℓ²(π)` (Exercise 12.3), and
eliminates negative eigenvalues near `-1`: `P.lazy.absSpectralGap π = P.lazy.spectralGap π =
P.spectralGap π / 2` (`IsReversible.absSpectralGap_lazy`).

Combining `ℓ²(π)` variance contraction (`(12.8)`, Exercise 12.4) with Pearson `χ²` divergence
(`Cslib.Probability.PMF.chiSquare`, Lemma 12.18) yields:

* `χ²(ν.bind (P ^ t) ‖ π) ≤ λ_*^{2t} χ²(ν ‖ π)` and
  `χ²((P ^ t) x ‖ π) ≤ λ_*^{2t} (1 - π(x)) / π(x)`;
* the pointwise transition-ratio bound
  `|P^t(x, y) / π(y) - 1| ≤ λ_*^t / √(π(x) π(y))` (`(12.13)`);
* the pointwise and worst-case total-variation bounds
  `dist ((P ^ t) x) π ≤ (1 / 2) √((1 - π(x)) / π(x)) · λ_*^t` and
  `d(t) ≤ (1 / 2) √((1 - π_min) / π_min) · λ_*^t`;
* the mixing-time upper bounds of **Theorem 12.4** (`(12.10)`):
  `t_mix(ε) ≤ ⌈γ_*⁻¹ ((1 / 2) log(1 / π_min) + log(1 / (2 ε)))⌉₊ ≤ ⌈γ_*⁻¹ log(1 / (ε π_min))⌉₊`;
* the eigenvalue and relaxation-time lower bounds of **Theorem 12.5** (`(12.14)`–`(12.15)`):
  `λ_*^t ≤ 2 d(t)` and `(γ_*⁻¹ - 1) log(1 / (2 ε)) ≤ t_mix(ε)`.

## Main definitions

* `Cslib.Probability.MarkovChain.lazy`: the lazy Markov chain `(I + P) / 2`.
* `Cslib.Probability.MarkovChain.stepOp`: the Markov transition operator as a monoid homomorphism.
* `Cslib.Probability.MarkovChain.dirichletForm`: the Dirichlet form `𝓔(f)`.
* `Cslib.Probability.MarkovChain.spectralContraction`: the `ℓ²(π)` contraction factor `λ_*`.
* `Cslib.Probability.MarkovChain.absSpectralGap`: the absolute spectral gap `γ_* = 1 - λ_*`.
* `Cslib.Probability.MarkovChain.spectralGap`: the spectral gap `γ = 1 - λ₂`.

## Main results

* `Cslib.Probability.MarkovChain.IsStationary.lazy`,
  `Cslib.Probability.MarkovChain.IsReversible.lazy`,
  `Cslib.Probability.MarkovChain.IsReversible.pow`: stationarity and reversibility under laziness
  and iteration.
* `Cslib.Probability.MarkovChain.abs_eigenvalue_le_one`,
  `Cslib.Probability.MarkovChain.IsStationary.sum_mul_eq_zero_of_stepOp_eq_smul`: Lemmas 12.1(i)
  and 12.3.
* `Cslib.Probability.MarkovChain.IsReversible.dirichletForm_eq_sub`: Lemma 13.6.
* `Cslib.Probability.MarkovChain.IsStationary.sum_mul_stepOp_pow_sub_sq_le`: variance contraction
  `(12.8)` / Exercise 12.4.
* `Cslib.Probability.MarkovChain.IsReversible.spectralContraction_eq_ciSup_abs`,
  `Cslib.Probability.MarkovChain.IsReversible.exists_eigenfunction_abs_eq_spectralContraction`,
  `Cslib.Probability.MarkovChain.IsReversible.exists_eigenfunction_eq_one_sub_spectralGap`:
  Rayleigh and eigenfunction characterizations (Lemmas 12.2 and 13.7).
* `Cslib.Probability.MarkovChain.IsReversible.spectralContraction_lazy`,
  `Cslib.Probability.MarkovChain.IsReversible.absSpectralGap_lazy`: Exercise 12.3 and Section 12.2.
* `Cslib.Probability.MarkovChain.IsReversible.chiSquare_bind_pow_le`,
  `Cslib.Probability.MarkovChain.IsReversible.chiSquare_pow_le`,
  `Cslib.Probability.MarkovChain.IsReversible.abs_toReal_div_sub_one_le`,
  `Cslib.Probability.MarkovChain.IsReversible.dist_pow_le`,
  `Cslib.Probability.MarkovChain.IsReversible.distToStationary_le_of_le_toReal`: `χ²`, `(12.13)`,
  and total-variation contraction.
* `Cslib.Probability.MarkovChain.IsReversible.mixingTime_le_of_absSpectralGap_pos`,
  `Cslib.Probability.MarkovChain.IsReversible.mixingTime_le_ceil_mul_log`: Theorem 12.4, `(12.10)`.
* `Cslib.Probability.MarkovChain.IsStationary.pow_abs_le_two_mul_distToStationary`,
  `Cslib.Probability.MarkovChain.IsReversible.spectralContraction_pow_le_two_mul_distToStationary`,
  `Cslib.Probability.MarkovChain.IsReversible.inv_absSpectralGap_sub_one_mul_log_le_mixingTime`:
  Theorem 12.5, `(12.14)`–`(12.15)`.

## References

* [LevinPeres2017], Sections 1.3, 12.1, 12.2, 12.6, Chapter 12 Exercises, and Section 13.2.1.
-/

public section

open scoped BigOperators ENNReal Cslib.Probability.PMF RealInnerProductSpace

namespace Cslib.Probability.MarkovChain

open Finset Cslib.Probability.PMF

/-! ### Reversibility of iterates and lazy chains -/

section GeneralState

variable {S : Type*}

/-- Detailed balance holds for the identity chain `1`. -/
theorem isReversible_one (π : PMF S) : (1 : MarkovChain S).IsReversible π := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  · simp [one_apply, PMF.pure_apply_of_ne _ _ hxy, PMF.pure_apply_of_ne _ _ hxy.symm]

/-- Detailed balance is preserved under `t`-step iteration (`P ^ t`). -/
theorem IsReversible.pow {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) :
    ∀ t : ℕ, (P ^ t).IsReversible π
  | 0 => isReversible_one π
  | t + 1 => fun x y => by
    rw [pow_succ_apply, pow_succ_apply', PMF.bind_apply, PMF.bind_apply,
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun z => ?_
    calc π x * ((P ^ t) x z * P z y)
        = (π x * (P ^ t) x z) * P z y := (mul_assoc _ _ _).symm
      _ = (π z * (P ^ t) z x) * P z y := by rw [hrev.pow t x z]
      _ = (π z * P z y) * (P ^ t) z x := mul_right_comm _ _ _
      _ = (π y * P y z) * (P ^ t) z x := by rw [hrev z y]
      _ = π y * (P y z * (P ^ t) z x) := mul_assoc _ _ _

/-- The **lazy version** `(I + P) / 2` of a Markov chain `P` ([LevinPeres2017], Section 1.3, p. 8):
from `x`, flip a fair coin and either take one step of `P` or remain at `x`. -/
noncomputable def lazy (P : MarkovChain S) : MarkovChain S where
  step x := (PMF.uniformOfFintype Bool).bind fun b => if b then P x else PMF.pure x

/-- Pointwise transition probabilities of `P.lazy` without `DecidableEq`. -/
theorem lazy_apply_eq (P : MarkovChain S) (x y : S) :
    P.lazy x y = 2⁻¹ * P x y + 2⁻¹ * PMF.pure x y := by
  change ((PMF.uniformOfFintype Bool).bind fun b => if b then P x else PMF.pure x) y = _
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte,
    Bool.false_eq_true]

/-- Transition probabilities of `P.lazy`: `(1 / 2) P(x, y) + (1 / 2) 1_{y = x}`. -/
theorem lazy_apply [DecidableEq S] (P : MarkovChain S) (x y : S) :
    P.lazy x y = 2⁻¹ * P x y + if y = x then 2⁻¹ else 0 := by
  rw [lazy_apply_eq, PMF.pure_apply]
  split_ifs <;> simp

@[simp]
theorem lazy_apply_self (P : MarkovChain S) (x : S) : P.lazy x x = 2⁻¹ * P x x + 2⁻¹ := by
  rw [lazy_apply_eq, PMF.pure_apply_self, mul_one]

theorem lazy_apply_of_ne (P : MarkovChain S) {x y : S} (h : x ≠ y) :
    P.lazy x y = 2⁻¹ * P x y := by
  rw [lazy_apply_eq, PMF.pure_apply_of_ne _ _ h.symm, mul_zero, add_zero]

/-- Stationarity is preserved by passing to the lazy chain. -/
theorem IsStationary.lazy {P : MarkovChain S} {π : PMF S} (h : P.IsStationary π) :
    P.lazy.IsStationary π := by
  change π.bind (fun x => (PMF.uniformOfFintype Bool).bind fun b =>
    if b then P x else PMF.pure x) = π
  rw [PMF.bind_comm]
  have hbranch : (fun b : Bool => π.bind fun x => if b then P x else PMF.pure x) =
      fun _ => π := by
    funext b
    cases b
    · exact PMF.bind_pure π
    · exact h
  rw [hbranch, PMF.bind_const]

/-- Detailed balance is preserved by passing to the lazy chain. -/
theorem IsReversible.lazy {P : MarkovChain S} {π : PMF S} (h : P.IsReversible π) :
    P.lazy.IsReversible π := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  · rw [lazy_apply_of_ne P hxy, lazy_apply_of_ne P hxy.symm, ← mul_assoc, mul_comm (π x) 2⁻¹,
      mul_assoc, h x y, ← mul_assoc, mul_comm 2⁻¹ (π y), mul_assoc]

/-- Exact `χ²` divergence of a point mass `PMF.pure x` from `π`: `(1 - π(x)) / π(x)`. -/
theorem chiSquare_pure_left [Finite S] {π : PMF S} (x : S) (hx : π x ≠ 0) :
    chiSquare (PMF.pure x) π = (1 - (π x).toReal) / (π x).toReal := by
  let := Fintype.ofFinite S
  classical
  have hsup : (PMF.pure x).support ⊆ π.support := by
    intro y hy
    rw [PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
    exact (PMF.mem_support_iff π x).mpr hx
  have hxpos : 0 < (π x).toReal := ENNReal.toReal_pos hx (π.apply_ne_top x)
  have hrest : ∑ y ∈ univ.erase x, ((PMF.pure x) y).toReal ^ 2 / (π y).toReal = 0 :=
    sum_eq_zero fun y hy => by
      rw [PMF.pure_apply_of_ne _ _ (ne_of_mem_erase hy), ENNReal.toReal_zero]
      simp
  rw [chiSquare_eq_sum_div_sub_one hsup, ← add_sum_erase _ _ (mem_univ x),
    PMF.pure_apply_self, ENNReal.toReal_one, one_pow, hrest, add_zero]
  field_simp [hxpos.ne']

end GeneralState

/-! ### Transition operator and `ℓ²(π)` geometry -/

section FiniteState

variable {S : Type*} [Fintype S]

/-- The **transition operator** `P ↦ (f ↦ (x ↦ ∑ y, P(x, y) f(y)))`, packaged as a monoid
homomorphism from `MarkovChain S` to linear endomorphisms of `S → ℝ`. -/
noncomputable def stepOp : MarkovChain S →* Module.End ℝ (S → ℝ) where
  toFun P :=
    { toFun f x := ∑ y, (P x y).toReal * f y
      map_add' f g := funext fun x => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' c f := funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun y _ => by ring }
  map_one' := LinearMap.ext fun f => funext fun x => by
    classical
    change ∑ y, ((PMF.pure x) y).toReal * f y = f x
    rw [← add_sum_erase _ _ (mem_univ x), PMF.pure_apply_self, ENNReal.toReal_one, one_mul,
      sum_eq_zero fun y hy => by
        rw [PMF.pure_apply_of_ne _ _ (ne_of_mem_erase hy), ENNReal.toReal_zero, zero_mul],
      add_zero]
  map_mul' P Q := LinearMap.ext fun f => funext fun x => sum_bind_mul (P x) Q f

theorem stepOp_apply (P : MarkovChain S) (f : S → ℝ) (x : S) :
    P.stepOp f x = ∑ y, (P x y).toReal * f y := by
  unfold stepOp
  rfl

@[simp]
theorem stepOp_const (P : MarkovChain S) (c : ℝ) : P.stepOp (fun _ => c) = fun _ => c :=
  funext fun x => by rw [stepOp_apply, ← sum_mul, sum_toReal, one_mul]

theorem stepOp_add_const (P : MarkovChain S) (f : S → ℝ) (c : ℝ) (x : S) :
    P.stepOp (fun y => f y + c) x = P.stepOp f x + c := by
  change P.stepOp (f + fun _ => c) x = _
  rw [map_add, Pi.add_apply, stepOp_const]

theorem stepOp_sub_const (P : MarkovChain S) (f : S → ℝ) (c : ℝ) (x : S) :
    P.stepOp (fun y => f y - c) x = P.stepOp f x - c := by
  change P.stepOp (f - fun _ => c) x = _
  rw [map_sub, Pi.sub_apply, stepOp_const]

/-- The lazy transition operator averages the identity and `P.stepOp`:
`P.lazy.stepOp f x = (f x + P.stepOp f x) / 2`. -/
theorem stepOp_lazy_apply (P : MarkovChain S) (f : S → ℝ) (x : S) :
    P.lazy.stepOp f x = (f x + P.stepOp f x) / 2 := by
  have h1 : (1 : MarkovChain S).stepOp f x = f x := by simp
  rw [← h1, stepOp_apply, stepOp_apply, stepOp_apply, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun y _ => ?_
  have hne1 : (2 : ℝ≥0∞)⁻¹ * P x y ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ((P x).apply_ne_top y)
  have hne2 : (2 : ℝ≥0∞)⁻¹ * PMF.pure x y ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ((PMF.pure x).apply_ne_top y)
  rw [lazy_apply_eq, ENNReal.toReal_add hne1 hne2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_apply]
  ring

/-- `ℓ^∞` contraction of `P.stepOp` ([LevinPeres2017], Exercise 12.1(a), p. 177). -/
theorem abs_stepOp_le_of_forall_abs_le (P : MarkovChain S) {f : S → ℝ} {B : ℝ}
    (hf : ∀ y, |f y| ≤ B) (x : S) : |P.stepOp f x| ≤ B := by
  calc |P.stepOp f x| = |∑ y, (P x y).toReal * f y| := by rw [stepOp_apply]
    _ ≤ ∑ y, |(P x y).toReal * f y| := abs_sum_le_sum_abs _ _
    _ = ∑ y, (P x y).toReal * |f y| :=
        sum_congr rfl fun y _ => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ B := sum_mul_le (P x) (fun y => |f y|) B hf

/-- **Every eigenvalue of a finite Markov chain has absolute value at most `1`**
([LevinPeres2017], Lemma 12.1(i), p. 161, and Exercise 12.1(a), p. 177). -/
theorem abs_eigenvalue_le_one (P : MarkovChain S) {f : S → ℝ} {μ : ℝ}
    (hf0 : f ≠ 0) (hf : P.stepOp f = μ • f) : |μ| ≤ 1 := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hf0
  have : Nonempty S := ⟨x₀⟩
  obtain ⟨x, -, hmax⟩ := univ.exists_max_image (fun y => |f y|) univ_nonempty
  have hxpos : 0 < |f x| := (abs_pos.mpr hx₀).trans_le (hmax x₀ (mem_univ x₀))
  have hstep : |P.stepOp f x| ≤ |f x| :=
    P.abs_stepOp_le_of_forall_abs_le (fun y => hmax y (mem_univ y)) x
  rw [hf, Pi.smul_apply, smul_eq_mul, abs_mul] at hstep
  exact le_of_mul_le_mul_right (by simpa using hstep) hxpos

/-- Pointwise Jensen inequality `(P f x)² ≤ P (f²) x`. -/
theorem sq_stepOp_le (P : MarkovChain S) (f : S → ℝ) (x : S) :
    P.stepOp f x ^ 2 ≤ P.stepOp (fun y => f y ^ 2) x := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset S)
    (fun y => Real.sqrt (P x y).toReal * f y) (fun y => Real.sqrt (P x y).toReal)
  have hL : (∑ y, Real.sqrt (P x y).toReal * f y * Real.sqrt (P x y).toReal) = P.stepOp f x := by
    rw [stepOp_apply]
    refine sum_congr rfl fun y _ => ?_
    calc Real.sqrt (P x y).toReal * f y * Real.sqrt (P x y).toReal
        = (Real.sqrt (P x y).toReal ^ 2) * f y := by ring
      _ = (P x y).toReal * f y := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  have hR1 : ∑ y, (Real.sqrt (P x y).toReal * f y) ^ 2 = P.stepOp (fun y => f y ^ 2) x := by
    rw [stepOp_apply]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hR2 : ∑ y, Real.sqrt (P x y).toReal ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt ENNReal.toReal_nonneg, sum_toReal]
  rw [hL, hR1, hR2, mul_one] at hcs
  exact hcs

/-- Under a stationary distribution `π`, `P.stepOp` preserves `π`-expectations. -/
theorem IsStationary.sum_mul_stepOp {P : MarkovChain S} {π : PMF S} (hπ : P.IsStationary π)
    (f : S → ℝ) : ∑ x, (π x).toReal * P.stepOp f x = ∑ x, (π x).toReal * f x :=
  (sum_bind_mul π P f).symm.trans (by rw [hπ])

/-- **Eigenfunctions with eigenvalue `μ ≠ 1` have mean zero** ([LevinPeres2017], Lemma 12.3,
pp. 162–163); no reversibility is needed. -/
theorem IsStationary.sum_mul_eq_zero_of_stepOp_eq_smul {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} {μ : ℝ} (hμ : μ ≠ 1) (hf : P.stepOp f = μ • f) :
    ∑ x, (π x).toReal * f x = 0 := by
  have h := hπ.sum_mul_stepOp f
  rw [hf] at h
  have hmul : ∑ x, (π x).toReal * (μ • f) x = μ * ∑ x, (π x).toReal * f x := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hmul] at h
  have hzero : (1 - μ) * ∑ x, (π x).toReal * f x = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hμ.symm)

/-- Under stationarity, `P.stepOp` does not increase the `ℓ²(π)` second moment. -/
theorem IsStationary.sum_mul_stepOp_sq_le {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) (f : S → ℝ) :
    ∑ x, (π x).toReal * P.stepOp f x ^ 2 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
  (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (P.sq_stepOp_le f x)
    ENNReal.toReal_nonneg).trans_eq (hπ.sum_mul_stepOp fun y => f y ^ 2)

/-- Cauchy–Schwarz inequality in `ℓ²(π)`. -/
theorem sq_sum_mul_le (π : PMF S) (f g : S → ℝ) :
    (∑ x, (π x).toReal * f x * g x) ^ 2 ≤
      (∑ x, (π x).toReal * f x ^ 2) * ∑ x, (π x).toReal * g x ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset S)
    (fun x => Real.sqrt (π x).toReal * f x) (fun x => Real.sqrt (π x).toReal * g x)
  have hL : (∑ x, (Real.sqrt (π x).toReal * f x) * (Real.sqrt (π x).toReal * g x)) =
      ∑ x, (π x).toReal * f x * g x := by
    refine sum_congr rfl fun x _ => ?_
    calc (Real.sqrt (π x).toReal * f x) * (Real.sqrt (π x).toReal * g x)
        = (Real.sqrt (π x).toReal ^ 2) * f x * g x := by ring
      _ = (π x).toReal * f x * g x := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  have hR (h : S → ℝ) : ∑ x, (Real.sqrt (π x).toReal * h x) ^ 2 =
      ∑ x, (π x).toReal * h x ^ 2 := by
    refine sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [hL, hR f, hR g] at hcs
  exact hcs

/-- Under stationarity, `|⟨f, P f⟩_π| ≤ ⟨f, f⟩_π`. -/
theorem IsStationary.abs_sum_mul_stepOp_le {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) (f : S → ℝ) :
    |∑ x, (π x).toReal * f x * P.stepOp f x| ≤ ∑ x, (π x).toReal * f x ^ 2 := by
  have hnn : 0 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  refine abs_le_of_sq_le_sq ?_ hnn
  calc (∑ x, (π x).toReal * f x * P.stepOp f x) ^ 2
      ≤ (∑ x, (π x).toReal * f x ^ 2) * ∑ x, (π x).toReal * P.stepOp f x ^ 2 :=
        sq_sum_mul_le π f (P.stepOp f)
    _ ≤ (∑ x, (π x).toReal * f x ^ 2) * ∑ x, (π x).toReal * f x ^ 2 :=
        mul_le_mul_of_nonneg_left (hπ.sum_mul_stepOp_sq_le f) hnn
    _ = (∑ x, (π x).toReal * f x ^ 2) ^ 2 := (sq _).symm

/-- **Positive semidefiniteness of lazy chains in `ℓ²(π)`** ([LevinPeres2017], Exercise 12.3,
p. 177): `0 ≤ ⟨f, P.lazy f⟩_π` for every `π`-stationary chain `P`. -/
theorem IsStationary.sum_mul_stepOp_lazy_nonneg {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) (f : S → ℝ) :
    0 ≤ ∑ x, (π x).toReal * f x * P.lazy.stepOp f x := by
  have hsplit : ∑ x, (π x).toReal * f x * P.lazy.stepOp f x =
      ((∑ x, (π x).toReal * f x ^ 2) + ∑ x, (π x).toReal * f x * P.stepOp f x) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun x _ => by rw [P.stepOp_lazy_apply]; ring
  rw [hsplit]
  linarith [neg_abs_le (∑ x, (π x).toReal * f x * P.stepOp f x), hπ.abs_sum_mul_stepOp_le f]

omit [Fintype S] in
theorem IsReversible.toReal_mul_eq {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π)
    (x y : S) : (π x).toReal * (P x y).toReal = (π y).toReal * (P y x).toReal := by
  rw [← ENNReal.toReal_mul, hrev x y, ENNReal.toReal_mul]

/-- **Self-adjointness of reversible chains in `ℓ²(π)`** ([LevinPeres2017], Section 12.1,
`(12.1)`): `⟨f, P g⟩_π = ⟨P f, g⟩_π`. -/
theorem IsReversible.sum_mul_stepOp_comm {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (f g : S → ℝ) :
    ∑ x, (π x).toReal * f x * P.stepOp g x = ∑ x, (π x).toReal * P.stepOp f x * g x := by
  simp only [stepOp_apply, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  calc (π x).toReal * f x * ((P x y).toReal * g y)
      = ((π x).toReal * (P x y).toReal) * f x * g y := by ring
    _ = ((π y).toReal * (P y x).toReal) * f x * g y := by rw [hrev.toReal_mul_eq x y]
    _ = (π y).toReal * ((P y x).toReal * f x) * g y := by ring

/-! ### Dirichlet form -/

/-- The **Dirichlet form** `𝓔(f) = (1 / 2) ∑_{x, y} π(x) P(x, y) (f(x) - f(y))²` associated to
`(P, π)` ([LevinPeres2017], Section 13.2.1, `(13.2)`, p. 181). -/
noncomputable def dirichletForm (P : MarkovChain S) (π : PMF S) (f : S → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, (π x).toReal * (P x y).toReal * (f x - f y) ^ 2

theorem dirichletForm_nonneg (P : MarkovChain S) (π : PMF S) (f : S → ℝ) :
    0 ≤ P.dirichletForm π f :=
  mul_nonneg (by positivity) <| sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (sq_nonneg _)

@[simp]
theorem dirichletForm_const (P : MarkovChain S) (π : PMF S) (c : ℝ) :
    P.dirichletForm π (fun _ => c) = 0 := by
  simp [dirichletForm]

@[simp]
theorem dirichletForm_add_const (P : MarkovChain S) (π : PMF S) (f : S → ℝ) (c : ℝ) :
    P.dirichletForm π (fun x => f x + c) = P.dirichletForm π f := by
  simp only [dirichletForm, add_sub_add_right_eq_sub]

@[simp]
theorem dirichletForm_sub_const (P : MarkovChain S) (π : PMF S) (f : S → ℝ) (c : ℝ) :
    P.dirichletForm π (fun x => f x - c) = P.dirichletForm π f := by
  simp only [dirichletForm, sub_sub_sub_cancel_right]

/-- Passing to the lazy chain halves the Dirichlet form. -/
theorem dirichletForm_lazy (P : MarkovChain S) (π : PMF S) (f : S → ℝ) :
    P.lazy.dirichletForm π f = P.dirichletForm π f / 2 := by
  unfold dirichletForm
  have hterm (x y : S) :
      (π x).toReal * (P.lazy x y).toReal * (f x - f y) ^ 2 =
        ((π x).toReal * (P x y).toReal * (f x - f y) ^ 2) / 2 := by
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · rw [lazy_apply_of_ne P hxy, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      ring
  simp_rw [hterm, ← sum_div]
  ring

/-- **Dirichlet form identity for reversible Markov chains** ([LevinPeres2017], Lemma 13.6,
pp. 181–182): `𝓔(f) = ⟨f, f⟩_π - ⟨f, P f⟩_π`. -/
theorem IsReversible.dirichletForm_eq_sub {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (f : S → ℝ) :
    P.dirichletForm π f =
      (∑ x, (π x).toReal * f x ^ 2) - ∑ x, (π x).toReal * f x * P.stepOp f x := by
  have hexp (x y : S) : (π x).toReal * (P x y).toReal * (f x - f y) ^ 2 =
      (π x).toReal * (P x y).toReal * f x ^ 2 -
        2 * ((π x).toReal * f x * ((P x y).toReal * f y)) +
        (π x).toReal * (P x y).toReal * f y ^ 2 := by ring
  have h1 : ∑ x, ∑ y, (π x).toReal * (P x y).toReal * f x ^ 2 =
      ∑ x, (π x).toReal * f x ^ 2 := by
    refine sum_congr rfl fun x _ => ?_
    simp_rw [mul_assoc, ← mul_sum, ← sum_mul, sum_toReal, one_mul]
  have h2 : ∑ x, ∑ y, (π x).toReal * (P x y).toReal * f y ^ 2 =
      ∑ y, (π y).toReal * f y ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp_rw [hrev.toReal_mul_eq _ y, mul_assoc, ← mul_sum, ← sum_mul, sum_toReal, one_mul]
  have hcross : ∑ x, ∑ y, 2 * ((π x).toReal * f x * ((P x y).toReal * f y)) =
      2 * ∑ x, (π x).toReal * f x * P.stepOp f x := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_sum, stepOp_apply, ← mul_sum]
  unfold dirichletForm
  simp_rw [hexp, sum_add_distrib, sum_sub_distrib, h1, h2, hcross]
  ring

theorem IsReversible.dirichletForm_le_two_mul {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (f : S → ℝ) :
    P.dirichletForm π f ≤ 2 * ∑ x, (π x).toReal * f x ^ 2 := by
  rw [hrev.dirichletForm_eq_sub]
  linarith [neg_abs_le (∑ x, (π x).toReal * f x * P.stepOp f x),
    hrev.isStationary.abs_sum_mul_stepOp_le f]

/-! ### Spectral contraction `λ_*`, absolute spectral gap `γ_*`, and spectral gap `γ` -/

private theorem nonempty_meanZeroPos [Nontrivial S] {π : PMF S} (hπ : ∀ x, π x ≠ 0) :
    Nonempty {f : S → ℝ // ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2} := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  have ha : 0 < (π a).toReal := ENNReal.toReal_pos (hπ a) (π.apply_ne_top a)
  have hb : 0 < (π b).toReal := ENNReal.toReal_pos (hπ b) (π.apply_ne_top b)
  let f : S → ℝ := fun x =>
    (if x = a then (π a).toReal⁻¹ else 0) - if x = b then (π b).toReal⁻¹ else 0
  refine ⟨⟨f, ?_, ?_⟩⟩
  · have hsum_a : ∑ x, (π x).toReal * (if x = a then (π a).toReal⁻¹ else 0) = 1 := by
      simp [mul_ite, ha.ne']
    have hsum_b : ∑ x, (π x).toReal * (if x = b then (π b).toReal⁻¹ else 0) = 1 := by
      simp [mul_ite, hb.ne']
    simp_rw [f, mul_sub, sum_sub_distrib, hsum_a, hsum_b, sub_self]
  · refine sum_pos' (fun x _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      ⟨a, mem_univ a, mul_pos ha (sq_pos_iff.mpr ?_)⟩
    simp [f, hab, ha.ne']

/-- The **`ℓ²(π)` spectral contraction** `λ_*` of `(P, π)` ([LevinPeres2017], `(12.6)` and
`(12.8)`): the operator norm of `P.stepOp` on the `π`-mean-zero functions of positive `ℓ²(π)`
second moment, or `0` when no such function exists. -/
noncomputable def spectralContraction (P : MarkovChain S) (π : PMF S) : ℝ :=
  ⨆ f : {f : S → ℝ // ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2},
    Real.sqrt ((∑ x, (π x).toReal * P.stepOp f.1 x ^ 2) / ∑ x, (π x).toReal * f.1 x ^ 2)

/-- The **absolute spectral gap** `γ_* := 1 - λ_*` ([LevinPeres2017], Section 12.2, p. 163). -/
noncomputable def absSpectralGap (P : MarkovChain S) (π : PMF S) : ℝ :=
  1 - P.spectralContraction π

/-- The **spectral gap** `γ = 1 - λ₂` ([LevinPeres2017], Section 12.2, `(12.7)`, and Lemma 13.7,
`(13.3)`, p. 182): the infimum of `𝓔(f) / ⟨f, f⟩_π` over the `π`-mean-zero functions of positive
`ℓ²(π)` second moment, or `0` when no such function exists. -/
noncomputable def spectralGap (P : MarkovChain S) (π : PMF S) : ℝ :=
  ⨅ f : {f : S → ℝ // ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2},
    P.dirichletForm π f.1 / ∑ x, (π x).toReal * f.1 x ^ 2

theorem spectralContraction_nonneg (P : MarkovChain S) (π : PMF S) :
    0 ≤ P.spectralContraction π :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

theorem absSpectralGap_le_one (P : MarkovChain S) (π : PMF S) : P.absSpectralGap π ≤ 1 := by
  unfold absSpectralGap
  linarith [P.spectralContraction_nonneg π]

@[simp]
theorem one_sub_absSpectralGap (P : MarkovChain S) (π : PMF S) :
    1 - P.absSpectralGap π = P.spectralContraction π := by
  unfold absSpectralGap
  ring

theorem spectralGap_nonneg (P : MarkovChain S) (π : PMF S) : 0 ≤ P.spectralGap π :=
  Real.iInf_nonneg fun f => div_nonneg (P.dirichletForm_nonneg π f.1) f.2.2.le

private theorem isEmpty_meanZeroPos_of_subsingleton [Subsingleton S] (π : PMF S) :
    IsEmpty {f : S → ℝ //
      ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2} := by
  refine ⟨fun ⟨f, hmean, hpos⟩ => ?_⟩
  obtain ⟨x₀, _⟩ := π.support_nonempty
  have huniv : (univ : Finset S) = {x₀} := by ext y; simp [Subsingleton.elim y x₀]
  rw [huniv, sum_singleton] at hmean hpos
  rcases mul_eq_zero.mp hmean with h0 | h0
  · rw [h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  · rw [h0, sq, mul_zero, mul_zero] at hpos; exact lt_irrefl 0 hpos

@[simp]
theorem spectralContraction_eq_zero_of_subsingleton [Subsingleton S] (P : MarkovChain S)
    (π : PMF S) : P.spectralContraction π = 0 := by
  have := isEmpty_meanZeroPos_of_subsingleton π
  simp [spectralContraction]

@[simp]
theorem spectralGap_eq_zero_of_subsingleton [Subsingleton S] (P : MarkovChain S) (π : PMF S) :
    P.spectralGap π = 0 := by
  have := isEmpty_meanZeroPos_of_subsingleton π
  simp [spectralGap]

private theorem IsStationary.bddAbove_spectralContraction {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) :
    BddAbove (Set.range fun f : {f : S → ℝ //
        ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2} =>
      Real.sqrt ((∑ x, (π x).toReal * P.stepOp f.1 x ^ 2) / ∑ x, (π x).toReal * f.1 x ^ 2)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨f, rfl⟩
  rw [Real.sqrt_le_one]
  exact (div_le_one f.2.2).mpr (hπ.sum_mul_stepOp_sq_le f.1)

theorem IsStationary.spectralContraction_le_one {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) : P.spectralContraction π ≤ 1 :=
  Real.iSup_le (fun f => Real.sqrt_le_one.mpr ((div_le_one f.2.2).mpr
    (hπ.sum_mul_stepOp_sq_le f.1))) zero_le_one

theorem IsStationary.absSpectralGap_nonneg {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) : 0 ≤ P.absSpectralGap π :=
  sub_nonneg.mpr hπ.spectralContraction_le_one

/-- One-step `ℓ²(π)` contraction on `π`-mean-zero functions. -/
theorem IsStationary.sum_mul_stepOp_sq_le_spectralContraction {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} (hf : ∑ x, (π x).toReal * f x = 0) :
    ∑ x, (π x).toReal * P.stepOp f x ^ 2 ≤
      P.spectralContraction π ^ 2 * ∑ x, (π x).toReal * f x ^ 2 := by
  have hnn : 0 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rcases hnn.eq_or_lt with hzero | hpos
  · have hle := hπ.sum_mul_stepOp_sq_le f
    rw [← hzero] at hle ⊢
    linarith [sum_nonneg fun x (_ : x ∈ univ) =>
      mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ (π x).toReal) (sq_nonneg (P.stepOp f x))]
  · have hsup : Real.sqrt ((∑ x, (π x).toReal * P.stepOp f x ^ 2) /
        ∑ x, (π x).toReal * f x ^ 2) ≤ P.spectralContraction π :=
      le_ciSup hπ.bddAbove_spectralContraction ⟨f, hf, hpos⟩
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsup 2
    rw [Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) hpos.le), div_le_iff₀ hpos] at hsq
    exact hsq

/-- Characterization of `P.spectralContraction π ≤ c` for `c ≥ 0`. -/
theorem IsStationary.spectralContraction_le_iff {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {c : ℝ} (hc : 0 ≤ c) :
    P.spectralContraction π ≤ c ↔
      ∀ f : S → ℝ, ∑ x, (π x).toReal * f x = 0 →
        ∑ x, (π x).toReal * P.stepOp f x ^ 2 ≤ c ^ 2 * ∑ x, (π x).toReal * f x ^ 2 := by
  refine ⟨fun hle f hf => (hπ.sum_mul_stepOp_sq_le_spectralContraction hf).trans ?_, fun h => ?_⟩
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (P.spectralContraction_nonneg π) hle 2)
      (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  · refine Real.iSup_le (fun f => ?_) hc
    rw [← Real.sqrt_sq hc]
    exact Real.sqrt_le_sqrt ((div_le_iff₀ f.2.2).mpr (h f.1 f.2.1))

/-- **`t`-step `ℓ²(π)` contraction** on `π`-mean-zero functions. -/
theorem IsStationary.sum_mul_stepOp_pow_sq_le {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} (hf : ∑ x, (π x).toReal * f x = 0) (t : ℕ) :
    ∑ x, (π x).toReal * (P ^ t).stepOp f x ^ 2 ≤
      P.spectralContraction π ^ (2 * t) * ∑ x, (π x).toReal * f x ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmean : ∑ x, (π x).toReal * (P ^ t).stepOp f x = 0 := by
      rw [(hπ.pow t).sum_mul_stepOp, hf]
    have hstep : (P ^ (t + 1)).stepOp f = P.stepOp ((P ^ t).stepOp f) := by
      rw [pow_succ', map_mul, mul_apply_eq_comp]
    rw [hstep]
    calc ∑ x, (π x).toReal * P.stepOp ((P ^ t).stepOp f) x ^ 2
        ≤ P.spectralContraction π ^ 2 * ∑ x, (π x).toReal * (P ^ t).stepOp f x ^ 2 :=
          hπ.sum_mul_stepOp_sq_le_spectralContraction hmean
      _ ≤ P.spectralContraction π ^ 2 *
          (P.spectralContraction π ^ (2 * t) * ∑ x, (π x).toReal * f x ^ 2) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = P.spectralContraction π ^ (2 * (t + 1)) * ∑ x, (π x).toReal * f x ^ 2 := by ring

/-- **`t`-step variance contraction** `Var_π(P^t f) ≤ (1 - γ_*)^{2t} Var_π(f)`
([LevinPeres2017], `(12.8)`, p. 163, and Exercise 12.4, p. 177). -/
theorem IsStationary.sum_mul_stepOp_pow_sub_sq_le {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) (f : S → ℝ) (t : ℕ) :
    ∑ x, (π x).toReal * ((P ^ t).stepOp f x - ∑ y, (π y).toReal * f y) ^ 2 ≤
      P.spectralContraction π ^ (2 * t) *
        ∑ x, (π x).toReal * (f x - ∑ y, (π y).toReal * f y) ^ 2 := by
  set m := ∑ y, (π y).toReal * f y
  have hmean : ∑ x, (π x).toReal * (f x - m) = 0 := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal, one_mul, m, sub_self]
  simpa only [stepOp_sub_const] using hπ.sum_mul_stepOp_pow_sq_le hmean t

/-- For stationary `P`, `|⟨f, P f⟩_π| ≤ λ_* ⟨f, f⟩_π` on `π`-mean-zero functions. -/
theorem IsStationary.abs_sum_mul_stepOp_le_spectralContraction {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} (hf : ∑ x, (π x).toReal * f x = 0) :
    |∑ x, (π x).toReal * f x * P.stepOp f x| ≤
      P.spectralContraction π * ∑ x, (π x).toReal * f x ^ 2 := by
  have hnn : 0 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (P.spectralContraction_nonneg π) hnn)
  calc (∑ x, (π x).toReal * f x * P.stepOp f x) ^ 2
      ≤ (∑ x, (π x).toReal * f x ^ 2) * ∑ x, (π x).toReal * P.stepOp f x ^ 2 :=
        sq_sum_mul_le π f (P.stepOp f)
    _ ≤ (∑ x, (π x).toReal * f x ^ 2) *
          (P.spectralContraction π ^ 2 * ∑ x, (π x).toReal * f x ^ 2) :=
        mul_le_mul_of_nonneg_left (hπ.sum_mul_stepOp_sq_le_spectralContraction hf) hnn
    _ = (P.spectralContraction π * ∑ x, (π x).toReal * f x ^ 2) ^ 2 := by ring

private theorem IsReversible.spectralContraction_le_of_abs_sum_mul_stepOp_le
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ f : S → ℝ, ∑ x, (π x).toReal * f x = 0 →
      |∑ x, (π x).toReal * f x * P.stepOp f x| ≤ c * ∑ x, (π x).toReal * f x ^ 2) :
    P.spectralContraction π ≤ c := by
  refine (hrev.isStationary.spectralContraction_le_iff hc).mpr fun f hf => ?_
  have hg : ∑ x, (π x).toReal * P.stepOp f x = 0 := by
    rw [hrev.isStationary.sum_mul_stepOp, hf]
  have hpol (t : ℝ) :
      4 * t * ∑ x, (π x).toReal * P.stepOp f x ^ 2 ≤
        2 * c * (t ^ 2 * ∑ x, (π x).toReal * f x ^ 2 +
          ∑ x, (π x).toReal * P.stepOp f x ^ 2) := by
    let u : S → ℝ := t • f + P.stepOp f
    let v : S → ℝ := t • f - P.stepOp f
    have hu : ∑ x, (π x).toReal * u x = 0 := by
      simp_rw [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib,
        mul_left_comm _ t, ← mul_sum, hf, hg, mul_zero, add_zero]
    have hv : ∑ x, (π x).toReal * v x = 0 := by
      simp_rw [v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, sum_sub_distrib,
        mul_left_comm _ t, ← mul_sum, hf, hg, mul_zero, sub_zero]
    have hcomm : ∑ x, (π x).toReal * f x * P.stepOp (P.stepOp f) x =
        ∑ x, (π x).toReal * P.stepOp f x ^ 2 := by
      rw [hrev.sum_mul_stepOp_comm]
      exact sum_congr rfl fun x _ => by ring
    have hdiff : 4 * t * ∑ x, (π x).toReal * P.stepOp f x ^ 2 =
        (∑ x, (π x).toReal * u x * P.stepOp u x) -
          ∑ x, (π x).toReal * v x * P.stepOp v x := by
      rw [← sum_sub_distrib, show 4 * t * ∑ x, (π x).toReal * P.stepOp f x ^ 2 =
          2 * t * ∑ x, (π x).toReal * f x * P.stepOp (P.stepOp f) x +
            2 * t * ∑ x, (π x).toReal * P.stepOp f x ^ 2 by rw [hcomm]; ring,
        mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      simp only [u, v, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    have hsum_sq : (∑ x, (π x).toReal * u x ^ 2) + ∑ x, (π x).toReal * v x ^ 2 =
        2 * (t ^ 2 * ∑ x, (π x).toReal * f x ^ 2 +
          ∑ x, (π x).toReal * P.stepOp f x ^ 2) := by
      rw [← sum_add_distrib, mul_sum, ← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      simp only [u, v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    calc 4 * t * ∑ x, (π x).toReal * P.stepOp f x ^ 2
        ≤ |∑ x, (π x).toReal * u x * P.stepOp u x| +
            |∑ x, (π x).toReal * v x * P.stepOp v x| := by
          rw [hdiff]
          linarith [le_abs_self (∑ x, (π x).toReal * u x * P.stepOp u x),
            neg_le_abs (∑ x, (π x).toReal * v x * P.stepOp v x)]
      _ ≤ c * (∑ x, (π x).toReal * u x ^ 2) + c * ∑ x, (π x).toReal * v x ^ 2 :=
          add_le_add (h u hu) (h v hv)
      _ = 2 * c * (t ^ 2 * ∑ x, (π x).toReal * f x ^ 2 +
            ∑ x, (π x).toReal * P.stepOp f x ^ 2) := by
          rw [← mul_add, hsum_sq]
          ring
  rcases hc.eq_or_lt with rfl | hpos
  · linarith [hpol 1]
  · exact le_of_mul_le_mul_left (by linarith [hpol c]) (by positivity : 0 < 2 * c)

/-- **Rayleigh characterization of `λ_*` for reversible chains**: `P.spectralContraction π ≤ c`
iff `|⟨f, P f⟩_π| ≤ c ⟨f, f⟩_π` on `π`-mean-zero functions. -/
theorem IsReversible.spectralContraction_le_iff_abs_sum_mul_stepOp_le
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) {c : ℝ} (hc : 0 ≤ c) :
    P.spectralContraction π ≤ c ↔
      ∀ f : S → ℝ, ∑ x, (π x).toReal * f x = 0 →
        |∑ x, (π x).toReal * f x * P.stepOp f x| ≤ c * ∑ x, (π x).toReal * f x ^ 2 :=
  ⟨fun hle _f hf => (hrev.isStationary.abs_sum_mul_stepOp_le_spectralContraction hf).trans
    (mul_le_mul_of_nonneg_right hle
      (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))),
    hrev.spectralContraction_le_of_abs_sum_mul_stepOp_le hc⟩

/-- **Absolute Rayleigh-quotient formula for `λ_*`** on reversible chains. -/
theorem IsReversible.spectralContraction_eq_ciSup_abs {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) :
    P.spectralContraction π =
      ⨆ f : {f : S → ℝ // ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2},
        |∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x| / ∑ x, (π x).toReal * f.1 x ^ 2 := by
  have hle (f : {f : S → ℝ //
      ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2}) :
      |∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x| / ∑ x, (π x).toReal * f.1 x ^ 2 ≤
        P.spectralContraction π :=
    (div_le_iff₀ f.2.2).mpr (hrev.isStationary.abs_sum_mul_stepOp_le_spectralContraction f.2.1)
  refine le_antisymm ?_ (Real.iSup_le hle (P.spectralContraction_nonneg π))
  refine hrev.spectralContraction_le_of_abs_sum_mul_stepOp_le
    (Real.iSup_nonneg fun f => div_nonneg (abs_nonneg _) f.2.2.le) fun f hf => ?_
  have hnn : 0 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rcases hnn.eq_or_lt with hzero | hpos
  · have habs := hrev.isStationary.abs_sum_mul_stepOp_le f
    rw [← hzero] at habs ⊢
    linarith [abs_nonneg (∑ x, (π x).toReal * f x * P.stepOp f x)]
  · rw [← div_le_iff₀ hpos]
    exact le_ciSup ⟨P.spectralContraction π, Set.forall_mem_range.mpr hle⟩ ⟨f, hf, hpos⟩

/-! ### Poincaré inequality and lazy spectral gap -/

private theorem bddBelow_spectralGap (P : MarkovChain S) (π : PMF S) :
    BddBelow (Set.range fun u : {f : S → ℝ //
        ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2} =>
      P.dirichletForm π u.1 / ∑ x, (π x).toReal * u.1 x ^ 2) :=
  ⟨0, by rintro _ ⟨u, rfl⟩; exact div_nonneg (P.dirichletForm_nonneg π u.1) u.2.2.le⟩

/-- **Poincaré inequality** (`γ Var_π(f) ≤ 𝓔(f)`, [LevinPeres2017], Lemma 13.7 and Remark 13.8,
p. 182), valid without any support or reversibility assumption. -/
theorem spectralGap_mul_le_dirichletForm (P : MarkovChain S) (π : PMF S) (f : S → ℝ) :
    P.spectralGap π * ∑ x, (π x).toReal * (f x - ∑ y, (π y).toReal * f y) ^ 2 ≤
      P.dirichletForm π f := by
  set g : S → ℝ := fun x => f x - ∑ y, (π y).toReal * f y
  have hg_mean : ∑ x, (π x).toReal * g x = 0 := by
    simp_rw [g, mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal, one_mul, sub_self]
  have hnn : 0 ≤ ∑ x, (π x).toReal * g x ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [← P.dirichletForm_sub_const π f (∑ y, (π y).toReal * f y)]
  rcases hnn.eq_or_lt with hzero | hpos
  · rw [← hzero, mul_zero]
    exact P.dirichletForm_nonneg π g
  · exact (le_div_iff₀ hpos).mp (ciInf_le (P.bddBelow_spectralGap π) ⟨g, hg_mean, hpos⟩)

/-- Variational characterization of `c ≤ P.spectralGap π` ([LevinPeres2017], Lemma 13.7,
`(13.3)`, p. 182). -/
theorem le_spectralGap_iff [Nontrivial S] {P : MarkovChain S} {π : PMF S}
    (hπ : ∀ x, π x ≠ 0) {c : ℝ} :
    c ≤ P.spectralGap π ↔
      ∀ f : S → ℝ, ∑ x, (π x).toReal * f x = 0 →
        c * ∑ x, (π x).toReal * f x ^ 2 ≤ P.dirichletForm π f := by
  have := nonempty_meanZeroPos hπ
  refine ⟨fun hle f hf => ?_, fun h => le_ciInf fun f => (le_div_iff₀ f.2.2).mpr (h f.1 f.2.1)⟩
  have hsq : 0 ≤ ∑ x, (π x).toReal * f x ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hpoinc := P.spectralGap_mul_le_dirichletForm π f
  rw [hf] at hpoinc
  simp only [sub_zero] at hpoinc
  exact (mul_le_mul_of_nonneg_right hle hsq).trans hpoinc

theorem IsReversible.spectralGap_le_two {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) : P.spectralGap π ≤ 2 := by
  by_cases hne : Nonempty {f : S → ℝ //
      ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2}
  · obtain ⟨f⟩ := hne
    exact (ciInf_le (P.bddBelow_spectralGap π) f).trans
      ((div_le_iff₀ f.2.2).mpr (hrev.dirichletForm_le_two_mul f.1))
  · have : IsEmpty {f : S → ℝ //
        ∑ x, (π x).toReal * f x = 0 ∧ 0 < ∑ x, (π x).toReal * f x ^ 2} :=
      not_nonempty_iff.mp hne
    simp [spectralGap]

/-- Passing to the lazy chain halves the spectral gap `γ`. -/
theorem spectralGap_lazy (P : MarkovChain S) (π : PMF S) :
    P.lazy.spectralGap π = P.spectralGap π / 2 := by
  unfold spectralGap
  simp_rw [dirichletForm_lazy, div_right_comm _ (2 : ℝ), div_eq_mul_inv _ (2 : ℝ),
    mul_comm _ (2 : ℝ)⁻¹]
  rw [← Real.mul_iInf_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]

/-- On a nontrivial state space with strictly positive `π`, `γ_* ≤ γ`. -/
theorem IsReversible.absSpectralGap_le_spectralGap [Nontrivial S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    P.absSpectralGap π ≤ P.spectralGap π := by
  have := nonempty_meanZeroPos hπ
  refine le_ciInf fun f => ?_
  have hle : |∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x| / ∑ x, (π x).toReal * f.1 x ^ 2 ≤
      P.spectralContraction π :=
    (div_le_iff₀ f.2.2).mpr (hrev.isStationary.abs_sum_mul_stepOp_le_spectralContraction f.2.1)
  have hdir : P.dirichletForm π f.1 / ∑ x, (π x).toReal * f.1 x ^ 2 =
      1 - (∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x) / ∑ x, (π x).toReal * f.1 x ^ 2 := by
    rw [hrev.dirichletForm_eq_sub, sub_div, div_self f.2.2.ne']
  rw [absSpectralGap, hdir]
  have habs : (∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x) / ∑ x, (π x).toReal * f.1 x ^ 2 ≤
      |∑ x, (π x).toReal * f.1 x * P.stepOp f.1 x| / ∑ x, (π x).toReal * f.1 x ^ 2 :=
    div_le_div_of_nonneg_right (le_abs_self _) f.2.2.le
  linarith

/-- For every reversible chain, `λ_*(P.lazy) ≤ 1 - γ(P) / 2`. -/
theorem IsReversible.spectralContraction_lazy_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) :
    P.lazy.spectralContraction π ≤ 1 - P.spectralGap π / 2 := by
  have hc : 0 ≤ 1 - P.spectralGap π / 2 := by linarith [hrev.spectralGap_le_two]
  rw [hrev.lazy.spectralContraction_eq_ciSup_abs]
  refine Real.iSup_le (fun f => ?_) hc
  have hpsd := hrev.isStationary.sum_mul_stepOp_lazy_nonneg f.1
  rw [abs_of_nonneg hpsd]
  have hdir : (∑ x, (π x).toReal * f.1 x * P.lazy.stepOp f.1 x) /
      ∑ x, (π x).toReal * f.1 x ^ 2 =
      1 - (P.dirichletForm π f.1 / ∑ x, (π x).toReal * f.1 x ^ 2) / 2 := by
    have hsub := hrev.lazy.dirichletForm_eq_sub f.1
    rw [dirichletForm_lazy] at hsub
    have hnum : ∑ x, (π x).toReal * f.1 x * P.lazy.stepOp f.1 x =
        (∑ x, (π x).toReal * f.1 x ^ 2) - P.dirichletForm π f.1 / 2 := by linarith
    rw [hnum, sub_div, div_self f.2.2.ne', div_right_comm]
  rw [hdir]
  have hgap : P.spectralGap π ≤ P.dirichletForm π f.1 / ∑ x, (π x).toReal * f.1 x ^ 2 :=
    ciInf_le (P.bddBelow_spectralGap π) f
  linarith

/-- **Exact lazy spectral contraction** on a nontrivial state space with strictly positive `π`:
`λ_*(P.lazy) = 1 - γ(P) / 2`. -/
theorem IsReversible.spectralContraction_lazy [Nontrivial S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    P.lazy.spectralContraction π = 1 - P.spectralGap π / 2 := by
  refine le_antisymm hrev.spectralContraction_lazy_le ?_
  have hle := hrev.lazy.absSpectralGap_le_spectralGap hπ
  rw [absSpectralGap, P.spectralGap_lazy π] at hle
  linarith

/-- **Exact lazy absolute spectral gap** ([LevinPeres2017], Section 12.2, p. 163, and
Exercise 12.3, p. 177): `γ_*(P.lazy) = γ(P.lazy) = γ(P) / 2`. -/
theorem IsReversible.absSpectralGap_lazy [Nontrivial S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    P.lazy.absSpectralGap π = P.spectralGap π / 2 := by
  rw [absSpectralGap, hrev.spectralContraction_lazy hπ]
  ring

/-! ### Eigenfunction existence via symmetric conjugation (Lemma 12.2) -/

private noncomputable def sqrtVec (π : PMF S) : EuclideanSpace ℝ S :=
  WithLp.toLp 2 fun x => Real.sqrt (π x).toReal

private noncomputable def meanZeroSubmodule (π : PMF S) : Submodule ℝ (EuclideanSpace ℝ S) :=
  (ℝ ∙ sqrtVec π)ᗮ

private theorem mem_meanZeroSubmodule_iff (π : PMF S) (u : EuclideanSpace ℝ S) :
    u ∈ meanZeroSubmodule π ↔ ∑ x, Real.sqrt (π x).toReal * u.ofLp x = 0 := by
  rw [meanZeroSubmodule, Submodule.mem_orthogonal_singleton_iff_inner_left,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  simp only [sqrtVec, WithLp.ofLp_toLp, mul_comm]

private noncomputable def symmEnd (P : MarkovChain S) (π : PMF S) :
    Module.End ℝ (EuclideanSpace ℝ S) where
  toFun u := WithLp.toLp 2 fun x =>
    Real.sqrt (π x).toReal * P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x
  map_add' u v := WithLp.ofLp_injective 2 <| funext fun x => by
    have hdiv : (fun y => (u.ofLp y + v.ofLp y) / Real.sqrt (π y).toReal) =
        (fun y => u.ofLp y / Real.sqrt (π y).toReal) +
          fun y => v.ofLp y / Real.sqrt (π y).toReal :=
      funext fun y => by simp [add_div]
    change Real.sqrt (π x).toReal * P.stepOp (fun y => (u.ofLp y + v.ofLp y) /
        Real.sqrt (π y).toReal) x =
      Real.sqrt (π x).toReal * P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x +
        Real.sqrt (π x).toReal * P.stepOp (fun y => v.ofLp y / Real.sqrt (π y).toReal) x
    rw [hdiv, map_add, Pi.add_apply, mul_add]
  map_smul' c u := WithLp.ofLp_injective 2 <| funext fun x => by
    have hdiv : (fun y => (c * u.ofLp y) / Real.sqrt (π y).toReal) =
        c • fun y => u.ofLp y / Real.sqrt (π y).toReal :=
      funext fun y => by simp [mul_div_assoc]
    change Real.sqrt (π x).toReal * P.stepOp (fun y => (c * u.ofLp y) /
        Real.sqrt (π y).toReal) x =
      c * (Real.sqrt (π x).toReal * P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x)
    rw [hdiv, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

private theorem isSymmetric_symmEnd {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    (symmEnd P π).IsSymmetric := by
  intro u v
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, star_trivial, dotProduct, dotProduct]
  have hL : ∑ x, v.ofLp x * (symmEnd P π u).ofLp x =
      ∑ x, (π x).toReal * P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x *
        (v.ofLp x / Real.sqrt (π x).toReal) := by
    refine sum_congr rfl fun x _ => ?_
    have hx : 0 < Real.sqrt (π x).toReal :=
      Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ x) (π.apply_ne_top x))
    simp only [symmEnd, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    calc v.ofLp x * (Real.sqrt (π x).toReal *
          P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x)
        = (Real.sqrt (π x).toReal ^ 2) *
            P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x *
            (v.ofLp x / Real.sqrt (π x).toReal) := by
          field_simp [hx.ne']
      _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  have hR : ∑ x, (symmEnd P π v).ofLp x * u.ofLp x =
      ∑ x, (π x).toReal * (u.ofLp x / Real.sqrt (π x).toReal) *
        P.stepOp (fun y => v.ofLp y / Real.sqrt (π y).toReal) x := by
    refine sum_congr rfl fun x _ => ?_
    have hx : 0 < Real.sqrt (π x).toReal :=
      Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ x) (π.apply_ne_top x))
    simp only [symmEnd, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    calc (Real.sqrt (π x).toReal *
          P.stepOp (fun y => v.ofLp y / Real.sqrt (π y).toReal) x) * u.ofLp x
        = (Real.sqrt (π x).toReal ^ 2) * (u.ofLp x / Real.sqrt (π x).toReal) *
            P.stepOp (fun y => v.ofLp y / Real.sqrt (π y).toReal) x := by
          field_simp [hx.ne']
      _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [hL, hR]
  exact (hrev.sum_mul_stepOp_comm _ _).symm

private theorem symmEnd_mem_meanZeroSubmodule {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) {u : EuclideanSpace ℝ S}
    (hu : u ∈ meanZeroSubmodule π) : symmEnd P π u ∈ meanZeroSubmodule π := by
  rw [mem_meanZeroSubmodule_iff] at hu ⊢
  have hmul (x : S) : Real.sqrt (π x).toReal * (symmEnd P π u).ofLp x =
      (π x).toReal * P.stepOp (fun y => u.ofLp y / Real.sqrt (π y).toReal) x := by
    simp only [symmEnd, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, ← mul_assoc,
      ← sq, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hmul' (x : S) : (π x).toReal * (u.ofLp x / Real.sqrt (π x).toReal) =
      Real.sqrt (π x).toReal * u.ofLp x := by
    have hx : 0 < Real.sqrt (π x).toReal :=
      Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ x) (π.apply_ne_top x))
    calc (π x).toReal * (u.ofLp x / Real.sqrt (π x).toReal)
        = (Real.sqrt (π x).toReal ^ 2) * (u.ofLp x / Real.sqrt (π x).toReal) := by
          rw [Real.sq_sqrt ENNReal.toReal_nonneg]
      _ = Real.sqrt (π x).toReal * u.ofLp x := by field_simp [hx.ne']
  simp_rw [hmul]
  rw [hrev.isStationary.sum_mul_stepOp]
  simpa only [hmul'] using hu

private noncomputable def meanZeroEnd {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) : Module.End ℝ (meanZeroSubmodule π) :=
  (symmEnd P π).restrict (fun _ hu => symmEnd_mem_meanZeroSubmodule hrev hπ hu)

private theorem isSymmetric_meanZeroEnd {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    (meanZeroEnd hrev hπ).IsSymmetric :=
  fun u v => isSymmetric_symmEnd hrev hπ u.1 v.1

private theorem nontrivial_meanZeroSubmodule [Nontrivial S] {π : PMF S} (hπ : ∀ x, π x ≠ 0) :
    Nontrivial (meanZeroSubmodule π) := by
  obtain ⟨f₀, hf₀_mean, hf₀_pos⟩ := nonempty_meanZeroPos hπ
  let u₀ : EuclideanSpace ℝ S := WithLp.toLp 2 fun x => Real.sqrt (π x).toReal * f₀ x
  have hu₀ : u₀ ∈ meanZeroSubmodule π := by
    rw [mem_meanZeroSubmodule_iff]
    have hpt (x : S) : Real.sqrt (π x).toReal * u₀.ofLp x = (π x).toReal * f₀ x := by
      simp only [u₀, ← mul_assoc, ← sq, Real.sq_sqrt ENNReal.toReal_nonneg]
    simpa only [hpt] using hf₀_mean
  refine ⟨⟨u₀, hu₀⟩, 0, fun h0 => hf₀_pos.ne' ?_⟩
  have hnorm : ‖u₀‖ ^ 2 = ∑ x, (π x).toReal * f₀ x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine sum_congr rfl fun x _ => ?_
    simp only [u₀, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hu0 : u₀ = 0 := congrArg Subtype.val h0
  simpa [hu0] using hnorm.symm

private noncomputable def toMeanZeroSubmodule {π : PMF S} {g : S → ℝ}
    (hg : ∑ x, (π x).toReal * g x = 0) : meanZeroSubmodule π :=
  ⟨WithLp.toLp 2 fun x => Real.sqrt (π x).toReal * g x, by
    rw [mem_meanZeroSubmodule_iff]
    have hpt (x : S) :
        Real.sqrt (π x).toReal * (WithLp.toLp 2 fun y => Real.sqrt (π y).toReal * g y).ofLp x =
          (π x).toReal * g x := by
      simp only [← mul_assoc, ← sq, Real.sq_sqrt ENNReal.toReal_nonneg]
    simpa only [hpt] using hg⟩

private theorem norm_sq_toMeanZeroSubmodule {π : PMF S} {g : S → ℝ}
    (hg : ∑ x, (π x).toReal * g x = 0) :
    ‖toMeanZeroSubmodule hg‖ ^ 2 = ∑ x, (π x).toReal * g x ^ 2 := by
  change ‖(WithLp.toLp 2 fun x => Real.sqrt (π x).toReal * g x : EuclideanSpace ℝ S)‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  refine sum_congr rfl fun x _ => ?_
  simp only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]

private theorem eigenfunction_of_eigenvectorBasis {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0)
    (i : Fin (Module.finrank ℝ (meanZeroSubmodule π))) :
    let hT := isSymmetric_meanZeroEnd hrev hπ
    let b := hT.eigenvectorBasis rfl
    let f : S → ℝ := fun x => (b i).1.ofLp x / Real.sqrt (π x).toReal
    f ≠ 0 ∧ (∑ x, (π x).toReal * f x = 0) ∧ (0 < ∑ x, (π x).toReal * f x ^ 2) ∧
      P.stepOp f = (hT.eigenvalues rfl i) • f := by
  set hT := isSymmetric_meanZeroEnd hrev hπ
  set b := hT.eigenvectorBasis rfl
  set f : S → ℝ := fun x => (b i).1.ofLp x / Real.sqrt (π x).toReal
  have hsqrt_pos (x : S) : 0 < Real.sqrt (π x).toReal :=
    Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ x) (π.apply_ne_top x))
  have hf_ne : f ≠ 0 := by
    intro hf0
    apply b.toBasis.ne_zero i
    refine Subtype.ext (WithLp.ofLp_injective 2 (funext fun x => ?_))
    have hx := congrFun hf0 x
    simp only [f, Pi.zero_apply, div_eq_zero_iff] at hx
    exact hx.resolve_right (hsqrt_pos x).ne'
  have hf_mean : ∑ x, (π x).toReal * f x = 0 := by
    have hpt (x : S) : (π x).toReal * f x = Real.sqrt (π x).toReal * (b i).1.ofLp x := by
      simp only [f]
      calc (π x).toReal * ((b i).1.ofLp x / Real.sqrt (π x).toReal)
          = (Real.sqrt (π x).toReal ^ 2) * ((b i).1.ofLp x / Real.sqrt (π x).toReal) := by
            rw [Real.sq_sqrt ENNReal.toReal_nonneg]
        _ = Real.sqrt (π x).toReal * (b i).1.ofLp x := by field_simp [(hsqrt_pos x).ne']
    simpa only [hpt] using (mem_meanZeroSubmodule_iff π (b i).1).mp (b i).2
  have hf_pos : 0 < ∑ x, (π x).toReal * f x ^ 2 := by
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hf_ne
    exact sum_pos' (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      ⟨x₀, mem_univ x₀, mul_pos (ENNReal.toReal_pos (hπ x₀) (π.apply_ne_top x₀))
        (sq_pos_iff.mpr hx₀)⟩
  have hf_eig : P.stepOp f = (hT.eigenvalues rfl i) • f := by
    have hbi := congrArg (fun w : meanZeroSubmodule π => w.1.ofLp) (hT.apply_eigenvectorBasis rfl i)
    ext x
    have hx : Real.sqrt (π x).toReal * P.stepOp f x = hT.eigenvalues rfl i * (b i).1.ofLp x :=
      congrFun hbi x
    simp only [f, Pi.smul_apply, smul_eq_mul]
    calc P.stepOp f x
        = (Real.sqrt (π x).toReal * P.stepOp f x) / Real.sqrt (π x).toReal := by
          field_simp [(hsqrt_pos x).ne']
      _ = (hT.eigenvalues rfl i * (b i).1.ofLp x) / Real.sqrt (π x).toReal := by rw [hx]
      _ = hT.eigenvalues rfl i * ((b i).1.ofLp x / Real.sqrt (π x).toReal) := mul_div_assoc _ _ _
  exact ⟨hf_ne, hf_mean, hf_pos, hf_eig⟩

/-- **Existence of a mean-zero eigenfunction achieving `|μ| = λ_*`** ([LevinPeres2017], Lemma 12.2
and `(12.6)`, pp. 161–163). -/
theorem IsReversible.exists_eigenfunction_abs_eq_spectralContraction [Nontrivial S]
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    ∃ (f : S → ℝ) (μ : ℝ),
      f ≠ 0 ∧ (∑ x, (π x).toReal * f x = 0) ∧ P.stepOp f = μ • f ∧
        |μ| = P.spectralContraction π := by
  have := nontrivial_meanZeroSubmodule hπ
  set hT := isSymmetric_meanZeroEnd hrev hπ
  set n := Module.finrank ℝ (meanZeroSubmodule π)
  have : Nonempty (Fin n) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨i, -, himax⟩ := univ.exists_max_image
    (fun j : Fin n => |hT.eigenvalues rfl j|) univ_nonempty
  obtain ⟨hf_ne, hf_mean, hf_pos, hf_eig⟩ := eigenfunction_of_eigenvectorBasis hrev hπ i
  set b := hT.eigenvectorBasis rfl
  set μ := hT.eigenvalues rfl i
  set f : S → ℝ := fun x => (b i).1.ofLp x / Real.sqrt (π x).toReal
  refine ⟨f, μ, hf_ne, hf_mean, hf_eig, le_antisymm ?_ ?_⟩
  · have habs := hrev.isStationary.abs_sum_mul_stepOp_le_spectralContraction hf_mean
    have hray : ∑ x, (π x).toReal * f x * P.stepOp f x = μ * ∑ x, (π x).toReal * f x ^ 2 := by
      rw [hf_eig, mul_sum]
      exact sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hray, abs_mul, abs_of_pos hf_pos] at habs
    exact le_of_mul_le_mul_right habs hf_pos
  · refine (hrev.isStationary.spectralContraction_le_iff (abs_nonneg μ)).mpr fun g hg => ?_
    let w := toMeanZeroSubmodule hg
    have hTw_norm : ‖meanZeroEnd hrev hπ w‖ ^ 2 = ∑ x, (π x).toReal * P.stepOp g x ^ 2 := by
      change ‖symmEnd P π w.1‖ ^ 2 = _
      rw [EuclideanSpace.real_norm_sq_eq]
      refine sum_congr rfl fun x _ => ?_
      have hdiv : (fun y => w.1.ofLp y / Real.sqrt (π y).toReal) = g :=
        funext fun y => mul_div_cancel_left₀ (g y)
          (Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ y) (π.apply_ne_top y))).ne'
      simp only [symmEnd, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hdiv, mul_pow,
        Real.sq_sqrt ENNReal.toReal_nonneg]
    rw [← hTw_norm, ← norm_sq_toMeanZeroSubmodule hg, ← b.repr.norm_map (meanZeroEnd hrev hπ w),
      ← b.repr.norm_map w, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hj := hT.eigenvectorBasis_apply_self_apply rfl w j
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hj
    change ((b.repr (meanZeroEnd hrev hπ w)).ofLp j) ^ 2 ≤ |μ| ^ 2 * ((b.repr w).ofLp j) ^ 2
    rw [hj, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (hT.eigenvalues rfl j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (himax j (mem_univ j)) 2

/-- **Existence of a mean-zero eigenfunction achieving `μ = 1 - γ`** ([LevinPeres2017], Lemma 12.2
and Lemma 13.7, pp. 161–162 and 182). -/
theorem IsReversible.exists_eigenfunction_eq_one_sub_spectralGap [Nontrivial S]
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) :
    ∃ (f : S → ℝ),
      f ≠ 0 ∧ (∑ x, (π x).toReal * f x = 0) ∧
        P.stepOp f = (1 - P.spectralGap π) • f := by
  have := nontrivial_meanZeroSubmodule hπ
  set hT := isSymmetric_meanZeroEnd hrev hπ
  let i₀ : Fin (Module.finrank ℝ (meanZeroSubmodule π)) := ⟨0, Module.finrank_pos⟩
  obtain ⟨hf_ne, hf_mean, hf_pos, hf_eig⟩ := eigenfunction_of_eigenvectorBasis hrev hπ i₀
  set b := hT.eigenvectorBasis rfl
  set μ₀ := hT.eigenvalues rfl i₀
  set f : S → ℝ := fun x => (b i₀).1.ofLp x / Real.sqrt (π x).toReal
  have hgap_eq : 1 - P.spectralGap π = μ₀ := by
    have hle_gap : P.spectralGap π ≤ 1 - μ₀ := by
      refine (ciInf_le (P.bddBelow_spectralGap π) ⟨f, hf_mean, hf_pos⟩).trans_eq ?_
      rw [hrev.dirichletForm_eq_sub, hf_eig]
      have hray : ∑ x, (π x).toReal * f x * (μ₀ • f) x = μ₀ * ∑ x, (π x).toReal * f x ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [hray, sub_div, div_self hf_pos.ne', mul_div_cancel_right₀ _ hf_pos.ne']
    have hge_gap : 1 - μ₀ ≤ P.spectralGap π := by
      have : Nonempty {g : S → ℝ //
          ∑ x, (π x).toReal * g x = 0 ∧ 0 < ∑ x, (π x).toReal * g x ^ 2} :=
        ⟨⟨f, hf_mean, hf_pos⟩⟩
      refine le_ciInf fun g => ?_
      rw [le_div_iff₀ g.2.2, hrev.dirichletForm_eq_sub]
      suffices ∑ x, (π x).toReal * g.1 x * P.stepOp g.1 x ≤
          μ₀ * ∑ x, (π x).toReal * g.1 x ^ 2 by linarith
      let w := toMeanZeroSubmodule g.2.1
      have hinner : ⟪w, meanZeroEnd hrev hπ w⟫ = ∑ x, (π x).toReal * g.1 x * P.stepOp g.1 x := by
        change ⟪w.1, symmEnd P π w.1⟫ = _
        rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
        refine sum_congr rfl fun x _ => ?_
        have hdiv : (fun y => w.1.ofLp y / Real.sqrt (π y).toReal) = g.1 :=
          funext fun y => mul_div_cancel_left₀ (g.1 y)
            (Real.sqrt_pos.mpr (ENNReal.toReal_pos (hπ y) (π.apply_ne_top y))).ne'
        simp only [symmEnd, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hdiv]
        simp only [w, toMeanZeroSubmodule]
        calc (Real.sqrt (π x).toReal * P.stepOp g.1 x) * (Real.sqrt (π x).toReal * g.1 x)
            = (Real.sqrt (π x).toReal ^ 2) * g.1 x * P.stepOp g.1 x := by ring
          _ = (π x).toReal * g.1 x * P.stepOp g.1 x := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
      rw [← hinner, ← norm_sq_toMeanZeroSubmodule g.2.1,
        ← b.repr.inner_map_map w (meanZeroEnd hrev hπ w), ← b.repr.norm_map w,
        EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
        EuclideanSpace.real_norm_sq_eq, mul_sum]
      refine sum_le_sum fun j _ => ?_
      have hj := hT.eigenvectorBasis_apply_self_apply rfl w j
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hj
      change (b.repr (meanZeroEnd hrev hπ w)).ofLp j * (b.repr w).ofLp j ≤
        μ₀ * ((b.repr w).ofLp j) ^ 2
      rw [hj, mul_assoc, ← sq]
      exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone rfl (show i₀ ≤ j from Nat.zero_le j.1)) (sq_nonneg _)
    linarith
  exact ⟨f, hf_ne, hf_mean, hgap_eq ▸ hf_eig⟩

/-! ### `χ²`, `ℓ^∞`, and total-variation mixing upper bounds (Theorem 12.4) -/

omit [Fintype S] in
private theorem support_subset_of_forall_ne_zero {π : PMF S} (hπ : ∀ x, π x ≠ 0) (ν : PMF S) :
    ν.support ⊆ π.support := fun x _ => (PMF.mem_support_iff π x).mpr (hπ x)

omit [Fintype S] in
private theorem toReal_mul_div_sub_one {π : PMF S} (hπ : ∀ x, π x ≠ 0) (z : S) (a : ℝ) :
    (π z).toReal * (a / (π z).toReal - 1) = a - (π z).toReal := by
  field_simp [(ENNReal.toReal_pos (hπ z) (π.apply_ne_top z)).ne']

private theorem sum_toReal_mul_div_sub_one {π : PMF S} (hπ : ∀ x, π x ≠ 0) (ν : PMF S) :
    ∑ z, (π z).toReal * ((ν z).toReal / (π z).toReal - 1) = 0 := by
  simp_rw [toReal_mul_div_sub_one hπ, sum_sub_distrib, sum_toReal, sub_self]

private theorem chiSquare_eq_sum_toReal_mul_sq {π : PMF S} (hπ : ∀ x, π x ≠ 0) (μ : PMF S) :
    chiSquare μ π = ∑ x, (π x).toReal * ((μ x).toReal / (π x).toReal - 1) ^ 2 := by
  rw [chiSquare_eq_sum (support_subset_of_forall_ne_zero hπ μ)]
  refine sum_congr rfl fun x _ => ?_
  field_simp [(ENNReal.toReal_pos (hπ x) (π.apply_ne_top x)).ne']

private theorem stepOp_pow_relDensity {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (ν : PMF S) (t : ℕ) (y : S) :
    (P ^ t).stepOp (fun x => (ν x).toReal / (π x).toReal - 1) y =
      ((ν.bind (P ^ t : MarkovChain S)) y).toReal / (π y).toReal - 1 := by
  rw [stepOp_sub_const, stepOp_apply, bind_apply_toReal, sum_div]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  have hx : 0 < (π x).toReal := ENNReal.toReal_pos (hπ x) (π.apply_ne_top x)
  have hy : 0 < (π y).toReal := ENNReal.toReal_pos (hπ y) (π.apply_ne_top y)
  have hbal := (hrev.pow t).toReal_mul_eq y x
  field_simp [hx.ne', hy.ne']
  calc (((P ^ t : MarkovChain S) y x).toReal) * (ν x).toReal * (π y).toReal
      = (ν x).toReal * ((π y).toReal * ((P ^ t : MarkovChain S) y x).toReal) := by ring
    _ = (ν x).toReal * ((π x).toReal * ((P ^ t : MarkovChain S) x y).toReal) := by rw [hbal]
    _ = (ν x).toReal * (π x).toReal * ((P ^ t : MarkovChain S) x y).toReal := by ring

/-- **`χ²` contraction for reversible Markov chains** ([LevinPeres2017], Section 12.6,
Lemma 12.18): `χ²(ν.bind (P ^ t) ‖ π) ≤ λ_*^{2t} χ²(ν ‖ π)`. -/
theorem IsReversible.chiSquare_bind_pow_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (ν : PMF S) (t : ℕ) :
    chiSquare (ν.bind (P ^ t : MarkovChain S)) π ≤
      P.spectralContraction π ^ (2 * t) * chiSquare ν π := by
  rw [chiSquare_eq_sum_toReal_mul_sq hπ, chiSquare_eq_sum_toReal_mul_sq hπ]
  simp_rw [← stepOp_pow_relDensity hrev hπ ν t]
  exact hrev.isStationary.sum_mul_stepOp_pow_sq_le (sum_toReal_mul_div_sub_one hπ ν) t

/-- **Pointwise `χ²` contraction**: `χ²((P ^ t) x ‖ π) ≤ λ_*^{2t} (1 - π(x)) / π(x)`. -/
theorem IsReversible.chiSquare_pow_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (x : S) (t : ℕ) :
    chiSquare ((P ^ t) x) π ≤
      P.spectralContraction π ^ (2 * t) * ((1 - (π x).toReal) / (π x).toReal) := by
  simpa only [PMF.pure_bind, chiSquare_pure_left x (hπ x)] using
    hrev.chiSquare_bind_pow_le hπ (PMF.pure x) t

/-- **Pointwise transition-ratio bound** ([LevinPeres2017], `(12.13)`, p. 164):
`|P^t(x, y) / π(y) - 1| ≤ λ_*^t / √(π(x) π(y))`. -/
theorem IsReversible.abs_toReal_div_sub_one_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ z, π z ≠ 0) (x y : S) (t : ℕ) :
    |((P ^ t) x y).toReal / (π y).toReal - 1| ≤
      P.spectralContraction π ^ t / Real.sqrt ((π x).toReal * (π y).toReal) := by
  classical
  let δ : S → S → ℝ := fun u z => ((PMF.pure u z).toReal / (π z).toReal) - 1
  have hδ_mean (u : S) : ∑ z, (π z).toReal * δ u z = 0 :=
    sum_toReal_mul_div_sub_one hπ (PMF.pure u)
  have hδ_sq (u : S) : ∑ z, (π z).toReal * δ u z ^ 2 ≤ 1 / (π u).toReal := by
    have hu : 0 < (π u).toReal := ENNReal.toReal_pos (hπ u) (π.apply_ne_top u)
    refine ((chiSquare_eq_sum_toReal_mul_sq hπ (PMF.pure u)).symm.trans
      (chiSquare_pure_left u (hπ u))).le.trans ?_
    exact div_le_div_of_nonneg_right (by linarith [ENNReal.toReal_nonneg (a := π u)]) hu.le
  have hpair : ∑ z, (π z).toReal * δ y z * (P ^ t).stepOp (δ x) z =
      ((P ^ t) x y).toReal / (π y).toReal - 1 := by
    simp only [δ, stepOp_pow_relDensity hrev hπ (PMF.pure x) t, PMF.pure_bind,
      toReal_mul_div_sub_one hπ, sub_mul, sum_sub_distrib, sum_toReal, sub_self, sub_zero]
    rw [Fintype.sum_eq_single y fun z hz => by
        rw [PMF.pure_apply_of_ne _ _ hz, ENNReal.toReal_zero, zero_mul],
      PMF.pure_apply_self, ENNReal.toReal_one, one_mul]
  have hx : 0 < (π x).toReal := ENNReal.toReal_pos (hπ x) (π.apply_ne_top x)
  have hy : 0 < (π y).toReal := ENNReal.toReal_pos (hπ y) (π.apply_ne_top y)
  have hrhs_nn : 0 ≤ P.spectralContraction π ^ t / Real.sqrt ((π x).toReal * (π y).toReal) :=
    div_nonneg (pow_nonneg (P.spectralContraction_nonneg π) t) (Real.sqrt_nonneg _)
  refine abs_le_of_sq_le_sq ?_ hrhs_nn
  rw [← hpair]
  calc (∑ z, (π z).toReal * δ y z * (P ^ t).stepOp (δ x) z) ^ 2
      ≤ (∑ z, (π z).toReal * δ y z ^ 2) * ∑ z, (π z).toReal * (P ^ t).stepOp (δ x) z ^ 2 :=
        sq_sum_mul_le π (δ y) ((P ^ t).stepOp (δ x))
    _ ≤ (1 / (π y).toReal) *
          (P.spectralContraction π ^ (2 * t) * (1 / (π x).toReal)) := by
        refine mul_le_mul (hδ_sq y) ?_
          (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
          (by positivity)
        exact (hrev.isStationary.sum_mul_stepOp_pow_sq_le (hδ_mean x) t).trans
          (mul_le_mul_of_nonneg_left (hδ_sq x) (pow_nonneg (P.spectralContraction_nonneg π) _))
    _ = (P.spectralContraction π ^ t / Real.sqrt ((π x).toReal * (π y).toReal)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (mul_nonneg hx.le hy.le), pow_mul']
        field_simp [hx.ne', hy.ne']

/-- **Total-variation contraction from an arbitrary initial distribution**:
`dist (ν.bind (P ^ t)) π ≤ (1 / 2) √(χ²(ν ‖ π)) · λ_*^t`. -/
theorem IsReversible.dist_bind_pow_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (ν : PMF S) (t : ℕ) :
    dist (ν.bind (P ^ t : MarkovChain S)) π ≤
      (1 / 2) * Real.sqrt (chiSquare ν π) * P.spectralContraction π ^ t := by
  refine (dist_le_sqrt_chiSquare_div_two
    (support_subset_of_forall_ne_zero hπ (ν.bind (P ^ t : MarkovChain S)))).trans ?_
  have hchi := hrev.chiSquare_bind_pow_le hπ ν t
  have hsqrt := Real.sqrt_le_sqrt hchi
  rw [pow_mul', Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg (P.spectralContraction_nonneg π) t)] at hsqrt
  linarith

/-- **Pointwise total-variation contraction**:
`dist ((P ^ t) x) π ≤ (1 / 2) √((1 - π(x)) / π(x)) · λ_*^t`. -/
theorem IsReversible.dist_pow_le {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (x : S) (t : ℕ) :
    dist ((P ^ t) x) π ≤
      (1 / 2) * Real.sqrt ((1 - (π x).toReal) / (π x).toReal) * P.spectralContraction π ^ t := by
  simpa only [PMF.pure_bind, chiSquare_pure_left x (hπ x)] using
    hrev.dist_bind_pow_le hπ (PMF.pure x) t

omit [Fintype S] in
private theorem forall_ne_zero_of_le_toReal {π : PMF S} {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) : ∀ x, π x ≠ 0 := by
  intro x hx0
  have := hmin x
  rw [hx0, ENNReal.toReal_zero] at this
  linarith

/-- **Worst-case total-variation contraction** `d(t) ≤ (1 / 2) √((1 - π_min) / π_min) · λ_*^t`. -/
theorem IsReversible.distToStationary_le_of_le_toReal {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) (t : ℕ) :
    P.distToStationary π t ≤
      (1 / 2) * Real.sqrt ((1 - π_min) / π_min) * P.spectralContraction π ^ t := by
  have hπ := forall_ne_zero_of_le_toReal hpos hmin
  refine P.distToStationary_le π (fun x => (hrev.dist_pow_le hπ x t).trans ?_)
    (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (pow_nonneg (P.spectralContraction_nonneg π) t))
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity))
    (pow_nonneg (P.spectralContraction_nonneg π) t)
  have hx : 0 < (π x).toReal := hpos.trans_le (hmin x)
  have h1 : (1 - (π x).toReal) / (π x).toReal = ((π x).toReal)⁻¹ - 1 := by field_simp [hx.ne']
  have h2 : (1 - π_min) / π_min = π_min⁻¹ - 1 := by field_simp [hpos.ne']
  rw [h1, h2]
  linarith [inv_anti₀ hpos (hmin x)]

/-- Exponential worst-case bound `d(t) ≤ e^{-γ_* t} / (2 √π_min)` ([LevinPeres2017], proof of
Theorem 12.4, p. 164). -/
theorem IsReversible.distToStationary_le_exp {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) (t : ℕ) :
    P.distToStationary π t ≤
      Real.exp (-(P.absSpectralGap π * t)) / (2 * Real.sqrt π_min) := by
  refine (hrev.distToStationary_le_of_le_toReal hpos hmin t).trans ?_
  have hsqrt : Real.sqrt ((1 - π_min) / π_min) ≤ 1 / Real.sqrt π_min := by
    calc Real.sqrt ((1 - π_min) / π_min)
        ≤ Real.sqrt (1 / π_min) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hpos.le)
      _ = 1 / Real.sqrt π_min := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hpow : P.spectralContraction π ^ t ≤ Real.exp (-(P.absSpectralGap π * t)) := by
    rw [← one_sub_absSpectralGap, show -(P.absSpectralGap π * t) = t * -P.absSpectralGap π by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀
      (by linarith [P.spectralContraction_nonneg π, one_sub_absSpectralGap P π])
      (by linarith [Real.add_one_le_exp (-P.absSpectralGap π)]) t
  calc (1 / 2) * Real.sqrt ((1 - π_min) / π_min) * P.spectralContraction π ^ t
      ≤ (1 / 2) * (1 / Real.sqrt π_min) * Real.exp (-(P.absSpectralGap π * t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hpow
          (pow_nonneg (P.spectralContraction_nonneg π) t) (by positivity)
    _ = Real.exp (-(P.absSpectralGap π * t)) / (2 * Real.sqrt π_min) := by
        field_simp [(Real.sqrt_pos.mpr hpos).ne']

/-- **Relaxation-time mixing bound** ([LevinPeres2017], Theorem 12.4, `(12.10)`, pp. 163–164):
`t_mix(ε) ≤ ⌈γ_*⁻¹ ((1 / 2) log(1 / π_min) + log(1 / (2 ε)))⌉₊`. -/
theorem IsReversible.mixingTime_le_of_absSpectralGap_pos {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) (hgap : 0 < P.absSpectralGap π)
    {ε : ℝ} (hε : 0 < ε) :
    P.mixingTime π ε ≤
      (⌈(P.absSpectralGap π)⁻¹ *
        ((1 / 2) * Real.log (1 / π_min) + Real.log (1 / (2 * ε)))⌉₊ : ℕ) := by
  set L := (1 / 2) * Real.log (1 / π_min) + Real.log (1 / (2 * ε)) with hL_def
  set t := ⌈(P.absSpectralGap π)⁻¹ * L⌉₊
  refine P.mixingTime_le_of_distToStationary_le ?_
  refine (hrev.distToStationary_le_exp hpos hmin t).trans ?_
  have ht : L ≤ P.absSpectralGap π * t := (inv_mul_le_iff₀ hgap).mp (Nat.le_ceil _)
  have hsqrt_pos : 0 < Real.sqrt π_min := Real.sqrt_pos.mpr hpos
  have hlog_sqrt : (1 / 2) * Real.log (1 / π_min) = Real.log (1 / Real.sqrt π_min) := by
    have hsq : (1 / Real.sqrt π_min) ^ 2 = 1 / π_min := by
      rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    rw [← hsq, Real.log_pow]
    ring
  have hexp_L : Real.exp (-L) = 2 * ε * Real.sqrt π_min := by
    rw [hL_def, hlog_sqrt, Real.exp_neg, Real.exp_add,
      Real.exp_log (div_pos one_pos hsqrt_pos), Real.exp_log (by positivity : 0 < 1 / (2 * ε))]
    field_simp [hsqrt_pos.ne', hε.ne']
  calc Real.exp (-(P.absSpectralGap π * t)) / (2 * Real.sqrt π_min)
      ≤ Real.exp (-L) / (2 * Real.sqrt π_min) :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht)) (by positivity)
    _ = ε := by
        rw [hexp_L]
        field_simp [hsqrt_pos.ne']

/-- Simplified relaxation-time mixing bound `t_mix(ε) ≤ ⌈γ_*⁻¹ log(1 / (ε π_min))⌉₊`
([LevinPeres2017], Theorem 12.4, `(12.10)`, p. 163). -/
theorem IsReversible.mixingTime_le_ceil_mul_log {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) (hgap : 0 < P.absSpectralGap π)
    {ε : ℝ} (hε : 0 < ε) :
    P.mixingTime π ε ≤ (⌈(P.absSpectralGap π)⁻¹ * Real.log (1 / (ε * π_min))⌉₊ : ℕ) := by
  refine (hrev.mixingTime_le_of_absSpectralGap_pos hpos hmin hgap hε).trans ?_
  obtain ⟨x₀, _⟩ := π.support_nonempty
  have hmin1 : π_min ≤ 1 := (hmin x₀).trans (toReal_apply_le_one π x₀)
  have hlog_pi : 0 ≤ Real.log (1 / π_min) :=
    Real.log_nonneg ((one_le_div hpos).mpr hmin1)
  have hlog_eps : Real.log (1 / (2 * ε)) ≤ Real.log (1 / ε) :=
    Real.log_le_log (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) hε]
      linarith)
  have hsum : (1 / 2) * Real.log (1 / π_min) + Real.log (1 / (2 * ε)) ≤
      Real.log (1 / (ε * π_min)) := by
    have hmul_log : Real.log (1 / (ε * π_min)) = Real.log (1 / ε) + Real.log (1 / π_min) := by
      rw [show 1 / (ε * π_min) = (1 / ε) * (1 / π_min) by ring,
        Real.log_mul (by positivity) (by positivity)]
    linarith
  exact ENat.natCast_le_natCast.mpr (Nat.ceil_mono
    (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hgap.le)))

/-! ### Eigenvalue and relaxation-time lower bounds (Theorem 12.5) -/

/-- Any nonzero `π`-mean-zero eigenfunction `P.stepOp f = μ • f` gives `|μ|^t ≤ 2 d(t)`
([LevinPeres2017], `(12.15)`, p. 164). -/
theorem pow_abs_le_two_mul_distToStationary_of_mean_zero (P : MarkovChain S) (π : PMF S)
    {f : S → ℝ} {μ : ℝ} (hf0 : f ≠ 0) (hmean : ∑ y, (π y).toReal * f y = 0)
    (hf : P.stepOp f = μ • f) (t : ℕ) :
    |μ| ^ t ≤ 2 * P.distToStationary π t := by
  have hpow : ∀ s : ℕ, (P ^ s).stepOp f = (μ ^ s) • f := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ', map_mul, mul_apply_eq_comp, ih, map_smul, hf, smul_smul, pow_succ]
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hf0
  have : Nonempty S := ⟨x₀⟩
  obtain ⟨x, -, hmax⟩ := univ.exists_max_image (fun y => |f y|) univ_nonempty
  have hxpos : 0 < |f x| := (abs_pos.mpr hx₀).trans_le (hmax x₀ (mem_univ x₀))
  have habs := abs_sum_mul_sub_le ((P ^ t) x) π f (fun y => hmax y (mem_univ y))
  rw [← stepOp_apply, hpow t, Pi.smul_apply, smul_eq_mul, hmean, sub_zero, abs_mul, abs_pow] at habs
  have hdist : 2 * |f x| * dist ((P ^ t) x) π ≤ 2 * P.distToStationary π t * |f x| := by
    have hd := P.dist_le_distToStationary π t x
    nlinarith
  exact le_of_mul_le_mul_right (habs.trans hdist) hxpos

/-- **Eigenvalue lower bound on total-variation distance** ([LevinPeres2017], Theorem 12.5,
`(12.15)`, p. 164): for a `π`-stationary chain and an eigenfunction with eigenvalue `μ ≠ 1`,
`|μ|^t ≤ 2 d(t)`. -/
theorem IsStationary.pow_abs_le_two_mul_distToStationary {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} {μ : ℝ} (hμ : μ ≠ 1) (hf0 : f ≠ 0)
    (hf : P.stepOp f = μ • f) (t : ℕ) :
    |μ| ^ t ≤ 2 * P.distToStationary π t :=
  pow_abs_le_two_mul_distToStationary_of_mean_zero P π hf0
    (hπ.sum_mul_eq_zero_of_stepOp_eq_smul hμ hf) hf t

/-- **Eigenvalue lower bound on mixing time** ([LevinPeres2017], Theorem 12.5, p. 164):
if `P` is `π`-stationary and `P.stepOp f = μ • f` (`f ≠ 0`, `|μ| < 1`), then every `t` with
`t_mix(ε) ≤ t` (`0 < ε`) satisfies `((1 - |μ|)⁻¹ - 1) log(1 / (2 ε)) ≤ t`. -/
theorem IsStationary.inv_one_sub_abs_sub_one_mul_log_le {P : MarkovChain S} {π : PMF S}
    (hπ : P.IsStationary π) {f : S → ℝ} {μ : ℝ} (hμ : |μ| < 1) (hf0 : f ≠ 0)
    (hf : P.stepOp f = μ • f) {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : P.mixingTime π ε ≤ t) :
    ((1 - |μ|)⁻¹ - 1) * Real.log (1 / (2 * ε)) ≤ t := by
  have h1μ : 0 < 1 - |μ| := sub_pos.mpr hμ
  have hcoeff_nn : 0 ≤ (1 - |μ|)⁻¹ - 1 :=
    sub_nonneg.mpr ((one_le_inv₀ h1μ).mpr (by linarith [abs_nonneg μ]))
  by_cases hε2 : 1 / 2 ≤ ε
  · have hlog_np : Real.log (1 / (2 * ε)) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
    exact (mul_nonpos_of_nonneg_of_nonpos hcoeff_nn hlog_np).trans (Nat.cast_nonneg t)
  push Not at hε2
  rcases (abs_nonneg μ).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  have hne1 : μ ≠ 1 := fun h1 => by rw [h1, abs_one] at hμ; exact lt_irrefl 1 hμ
  have hd : P.distToStationary π t ≤ ε := (hπ.mixingTime_le_iff ε t).mp ht
  have hpow : |μ| ^ t ≤ 2 * ε :=
    (hπ.pow_abs_le_two_mul_distToStationary hne1 hf0 hf t).trans (by linarith)
  have hinv_le : (2 * ε)⁻¹ ≤ |μ|⁻¹ ^ t := by
    rw [inv_pow]
    exact (inv_le_inv₀ (by positivity) (pow_pos hpos t)).mpr hpow
  have hlog1 : Real.log (1 / (2 * ε)) ≤ t * Real.log (|μ|⁻¹) := by
    rw [one_div]
    exact (Real.log_le_log (by positivity) hinv_le).trans_eq (Real.log_pow _ _)
  have hlog2 : Real.log (|μ|⁻¹) ≤ (1 - |μ|) / |μ| := by
    refine (Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)).trans_eq ?_
    field_simp [hpos.ne']
  have hlog3 : Real.log (1 / (2 * ε)) ≤ (t : ℝ) * ((1 - |μ|) / |μ|) :=
    hlog1.trans (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg t))
  rw [show (1 - |μ|)⁻¹ - 1 = |μ| / (1 - |μ|) by field_simp [h1μ.ne']; ring]
  calc (|μ| / (1 - |μ|)) * Real.log (1 / (2 * ε))
      ≤ (|μ| / (1 - |μ|)) * ((t : ℝ) * ((1 - |μ|) / |μ|)) :=
        mul_le_mul_of_nonneg_left hlog3 (div_nonneg hpos.le h1μ.le)
    _ = t := by field_simp [hpos.ne', h1μ.ne']

/-- **Reversible contraction lower bound** `λ_*^t ≤ 2 d(t)` ([LevinPeres2017], `(12.15)`, p. 164)
on a nontrivial state space with strictly positive `π`. -/
theorem IsReversible.spectralContraction_pow_le_two_mul_distToStationary [Nontrivial S]
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (t : ℕ) :
    P.spectralContraction π ^ t ≤ 2 * P.distToStationary π t := by
  obtain ⟨f, μ, hf0, hmean, hf, hμ⟩ := hrev.exists_eigenfunction_abs_eq_spectralContraction hπ
  rw [← hμ]
  exact pow_abs_le_two_mul_distToStationary_of_mean_zero P π hf0 hmean hf t

/-- When `γ_* = 0` on a nontrivial state space with strictly positive `π`, the chain never mixes
below `1 / 2`: `t_mix(ε) = ⊤` for every `ε < 1 / 2`. -/
theorem IsReversible.mixingTime_eq_top_of_absSpectralGap_eq_zero [Nontrivial S]
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0)
    (hgap : P.absSpectralGap π = 0) {ε : ℝ} (hε : ε < 1 / 2) :
    P.mixingTime π ε = ⊤ := by
  rw [P.mixingTime_eq_top_iff ε]
  intro t
  have h1 : P.spectralContraction π = 1 := by linarith [one_sub_absSpectralGap P π]
  have hd := hrev.spectralContraction_pow_le_two_mul_distToStationary hπ t
  rw [h1, one_pow] at hd
  linarith

/-- **Relaxation-time lower bound on mixing time** ([LevinPeres2017], Theorem 12.5, `(12.14)`,
p. 164): `((γ_*)⁻¹ - 1) log(1 / (2 ε)) ≤ t` whenever `t_mix(ε) ≤ t`. -/
theorem IsReversible.inv_absSpectralGap_sub_one_mul_log_le_mixingTime [Nontrivial S]
    {P : MarkovChain S} {π : PMF S} (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0)
    (hgap : 0 < P.absSpectralGap π) {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : P.mixingTime π ε ≤ t) :
    ((P.absSpectralGap π)⁻¹ - 1) * Real.log (1 / (2 * ε)) ≤ t := by
  obtain ⟨f, μ, hf0, -, hf, hμ⟩ := hrev.exists_eigenfunction_abs_eq_spectralContraction hπ
  have h1μ : 1 - |μ| = P.absSpectralGap π := by
    rw [hμ]
    unfold absSpectralGap
    rfl
  have hlt1 : |μ| < 1 := by linarith
  rw [← h1μ]
  exact hrev.isStationary.inv_one_sub_abs_sub_one_mul_log_le hlt1 hf0 hf hε ht

end FiniteState

end Cslib.Probability.MarkovChain
