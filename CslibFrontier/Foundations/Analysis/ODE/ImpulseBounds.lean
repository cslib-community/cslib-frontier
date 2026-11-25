/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/ImpulseBounds.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.LinearLyapunov
public import CslibFrontier.Foundations.Analysis.ODE.StateSpace
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy and decay bounds for LTI impulse responses

For a linear system `ẋ = A x` and a curve `x` solving it on `[0, ∞)`, and any real matrices `W`
and `C`, the quadratic energy `V t = x t ⬝ᵥ W *ᵥ x t` has derivative `x ⬝ᵥ (Aᵀ W + W A) *ᵥ x`
(`Matrix.hasDerivWithinAt_dotProduct_mulVec`), so with `R = Aᵀ W + W A + Cᵀ C` the *storage
identity* holds on every `[0, T]` (`Matrix.integral_mulVec_dotProduct_eq`):
`∫₀ᵀ ‖C x‖² = V 0 - V T + ∫₀ᵀ x ⬝ᵥ R *ᵥ x`. Two cases are classical (Boyd and Barratt, §5.6.1;
Boyd, El Ghaoui, Feron and Balakrishnan, §6.2):

* **Gramian equation.** If `R = 0`, the output energy on `[0, T]` is `V 0 - V T`; when the state
  tends to `0` the output energy on `[0, ∞)` is finite and equals `V 0`
  (`Matrix.integrableOn_Ioi_and_integral_eq`).
* **Dissipation inequality.** If `R ⪯ 0` and `W ⪰ 0`, the output energy on `[0, ∞)` is finite and
  at most `V 0` (`Matrix.integrableOn_Ioi_and_integral_le`). No stability of `A` is assumed or
  concluded: output energy says nothing about unobservable modes.

A decay inequality `Aᵀ P + P A + 2 α P ⪯ 0` gives `V t ≤ exp (-2 α t) V 0` for `V` built on `P`
(`Matrix.dotProduct_mulVec_le_exp_neg_mul`, from `le_exp_mul_sub_mul_of_hasDerivWithinAt`), and
with `lo 1 ⪯ P ⪯ hi 1`, `lo > 0`, the state bound `‖x t‖₂² ≤ (hi / lo) exp (-2 α t) ‖x 0‖₂²`
(`Matrix.dotProduct_self_le_exp_neg_mul`). With `Cᵀ C ⪯ γ P` the output of a trajectory satisfies
`‖C x t‖₂² ≤ γ hi exp (-2 α t) ‖x 0‖₂²` (`Matrix.mulVec_dotProduct_le_exp_neg_mul`).

## Impulse responses

For an `LTISystem` with response kernel `h t = C exp (t A) B`, the impulse `v δ₀` moves the state
to `B v` (`LTISystem.responseKernel_mulVec_eq`), and `h t *ᵥ v = C *ᵥ (exp (t A) *ᵥ B *ᵥ v)`.
Applying the results above to these trajectories, and summing over the columns of `h`, gives:

* the input-direction energy `∫₀^∞ ‖h t v‖₂² = (B v)ᵀ W (B v)` and the multi-input energy
  `∫₀^∞ ‖h t‖_F² = tr (Bᵀ W B)` for an exactly solved Gramian equation and a state that tends to
  `0` (`LTISystem.integrableOn_Ioi_and_integral_mulVec_eq`,
  `LTISystem.integrableOn_Ioi_and_integral_frobeniusSq_eq`), with the finite-horizon form
  `∫₀ᵀ ‖h‖_F² = tr (Bᵀ W B) - tr (X Tᵀ W X T)`, `X T = exp (T A) B`
  (`LTISystem.integral_frobeniusSq_eq`);
* the Gramian `W = ∫₀^∞ exp (t Aᵀ) Cᵀ C exp (t A) dt` entrywise, hence `W ⪰ 0`, for a symmetric
  solution and exponentially stable `A` (`Matrix.dotProduct_mulVec_eq_integral`,
  `Matrix.posSemidef_of_lyapunov_eq`); `W` may be singular;
* the upper bounds `∫₀^∞ ‖h t v‖₂² ≤ (B v)ᵀ W (B v)` and `∫₀^∞ ‖h t‖_F² ≤ tr (Bᵀ W B)` from a
  dissipation inequality (`LTISystem.integrableOn_Ioi_and_integral_mulVec_le`,
  `LTISystem.integrableOn_Ioi_and_integral_frobeniusSq_le`), without any stability assumption;
* the envelopes `‖h t v‖₂² ≤ γ β exp (-2 α t) ‖v‖₂²` and
  `‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α t)` from `Cᵀ C ⪯ γ P` and `Bᵀ P B ⪯ β 1`
  (`LTISystem.responseKernel_mulVec_sq_le`, `LTISystem.frobeniusSq_responseKernel_le`), and the
  energy tail `∫_T^∞ ‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α T) / (2 α)`
  (`LTISystem.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le`).

## Norms and normalization

Vectors are coordinate vectors `n → ℝ`. The squared Euclidean norm `‖y‖₂²` is written `y ⬝ᵥ y`, and
the squared Frobenius norm of a matrix `M` is written out as `∑ i, ∑ j, M i j ^ 2`; no matrix norm
instance is used. The impulse-response energy `∫₀^∞ ‖h t‖_F² dt` is the time-domain definition of
the squared `H₂` norm; no frequency-domain identity is used. Integrals are Lebesgue integrals over
`Set.Ioi 0`, stated together with integrability, so a divergent integral is never hidden behind
Lean's convention that a non-integrable function has integral `0`. These results concern the
response kernel `h` only; a system with direct feedthrough `D ≠ 0` has the impulse response
`D δ₀ + h`, whose energy is infinite, so a theorem about the full impulse response must also check
`D = 0`.

## References

* S. Boyd and C. Barratt, *Linear Controller Design: Limits of Performance*, 1991, §5.6.1,
  (5.35)–(5.37): the `H₂` norm as impulse-response energy, computed from the Gramian.
* S. Boyd, L. El Ghaoui, E. Feron and V. Balakrishnan, *Linear Matrix Inequalities in System and
  Control Theory*, 1994, §5.1.3 (decay rate) and §6.2 (output energy bounds).
-/

public section

open Set Filter Topology NormedSpace Matrix MeasureTheory

namespace Matrix

variable {n p : Type*} [Fintype n] [Fintype p]

omit [Fintype n] in
private theorem continuous_dotProduct_mulVec (M : Matrix n n ℝ) [Fintype n] :
    Continuous fun y : n → ℝ => y ⬝ᵥ M *ᵥ y :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- `y ⬝ᵥ (Cᵀ * C) *ᵥ y = (C *ᵥ y) ⬝ᵥ (C *ᵥ y)`. -/
private theorem dotProduct_transpose_mul_mulVec (C : Matrix p n ℝ) (y : n → ℝ) :
    y ⬝ᵥ (Cᵀ * C) *ᵥ y = C *ᵥ y ⬝ᵥ C *ᵥ y := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

variable {A W : Matrix n n ℝ} {C : Matrix p n ℝ} {x : ℝ → n → ℝ}

/-- **Storage identity.** For a solution `x` of `x' = A *ᵥ x` on `[0, ∞)`, any `W` and `C`, and
`T ≥ 0`, with `R = Aᵀ W + W A + Cᵀ C`:
`∫₀ᵀ ‖C x‖² = x 0 ⬝ᵥ W *ᵥ x 0 - x T ⬝ᵥ W *ᵥ x T + ∫₀ᵀ x ⬝ᵥ R *ᵥ x`. -/
theorem integral_mulVec_dotProduct_eq
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in 0..T, C *ᵥ x t ⬝ᵥ C *ᵥ x t = x 0 ⬝ᵥ W *ᵥ x 0 - x T ⬝ᵥ W *ᵥ x T +
      ∫ t in 0..T, x t ⬝ᵥ (Aᵀ * W + W * A + Cᵀ * C) *ᵥ x t := by
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht =>
    ((hx t ht.1).continuousWithinAt).mono Icc_subset_Ici_self
  have hint : ∀ M : Matrix n n ℝ, IntervalIntegrable (fun t => x t ⬝ᵥ M *ᵥ x t) volume 0 T :=
    fun M => ((continuous_dotProduct_mulVec M).comp_continuousOn hxc).intervalIntegrable_of_Icc hT
  have hV := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (fun t ht => ((hasDerivWithinAt_dotProduct_mulVec (P := W) hx ht.1).continuousWithinAt).mono
      Icc_subset_Ici_self)
    (fun t ht => (hasDerivWithinAt_dotProduct_mulVec (P := W) hx (le_of_lt ht.1)).hasDerivAt
      (Ici_mem_nhds ht.1)) (hint _)
  have hsplit : (fun t => x t ⬝ᵥ (Aᵀ * W + W * A + Cᵀ * C) *ᵥ x t) =
      fun t => x t ⬝ᵥ (Aᵀ * W + W * A) *ᵥ x t + x t ⬝ᵥ (Cᵀ * C) *ᵥ x t := by
    funext t
    rw [add_mulVec, dotProduct_add]
  rw [hsplit, intervalIntegral.integral_add (hint _) (hint _), hV]
  simp only [dotProduct_transpose_mul_mulVec]
  ring

omit [Fintype n] in
private theorem dotProduct_self_nonneg' (y : n → ℝ) [Fintype n] : 0 ≤ y ⬝ᵥ y := by
  simpa using dotProduct_self_star_nonneg y

/-- The output energy density `‖C x t‖²` of a solution is integrable on every `(0, T]`. -/
private theorem integrableOn_Ioc_mulVec_dotProduct
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) (T : ℝ) :
    IntegrableOn (fun t => C *ᵥ x t ⬝ᵥ C *ᵥ x t) (Ioc 0 T) := by
  have hc : ContinuousOn (fun t => C *ᵥ x t ⬝ᵥ C *ᵥ x t) (Icc 0 T) := by
    have hxc : ContinuousOn x (Icc 0 T) := fun t ht =>
      ((hx t ht.1).continuousWithinAt).mono Icc_subset_Ici_self
    simpa only [Function.comp_def, dotProduct_transpose_mul_mulVec] using
      (continuous_dotProduct_mulVec (Cᵀ * C)).comp_continuousOn hxc
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- Bounded partial integrals of a nonnegative density give integrability on `(0, ∞)`. -/
private theorem integrableOn_Ioi_of_bounded {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hloc : ∀ T, IntegrableOn g (Ioc 0 T)) {I : ℝ} (hI : ∀ᶠ T in atTop, ∫ t in 0..T, g t ≤ I) :
    IntegrableOn g (Ioi 0) :=
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I 0 hloc tendsto_id <| hI.mono fun T hT => by
    simpa only [id, Real.norm_of_nonneg (hg _)] using hT

/-- **Dissipation inequality on `[0, ∞)`.** If `Aᵀ W + W A + Cᵀ C ⪯ 0` and `W ⪰ 0` as quadratic
forms, then for every solution `x` of `x' = A *ᵥ x` on `[0, ∞)` the output energy `‖C x‖²` is
integrable on `(0, ∞)` with integral at most `x 0 ⬝ᵥ W *ᵥ x 0`. No stability of `A` is assumed. -/
theorem integrableOn_Ioi_and_integral_le
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t)
    (hR : ∀ y, y ⬝ᵥ (Aᵀ * W + W * A + Cᵀ * C) *ᵥ y ≤ 0) (hW : ∀ y, 0 ≤ y ⬝ᵥ W *ᵥ y) :
    IntegrableOn (fun t => C *ᵥ x t ⬝ᵥ C *ᵥ x t) (Ioi 0) ∧
      ∫ t in Ioi 0, C *ᵥ x t ⬝ᵥ C *ᵥ x t ≤ x 0 ⬝ᵥ W *ᵥ x 0 := by
  have hbound : ∀ T, 0 ≤ T → ∫ t in 0..T, C *ᵥ x t ⬝ᵥ C *ᵥ x t ≤ x 0 ⬝ᵥ W *ᵥ x 0 := by
    intro T hT
    rw [integral_mulVec_dotProduct_eq (W := W) hx hT]
    have := intervalIntegral.integral_nonneg_of_forall (μ := volume) hT fun t =>
      neg_nonneg.2 (hR (x t))
    rw [intervalIntegral.integral_neg] at this
    linarith [hW (x T)]
  have hint := integrableOn_Ioi_of_bounded (fun t => dotProduct_self_nonneg' _)
    (integrableOn_Ioc_mulVec_dotProduct hx) (eventually_atTop.2 ⟨0, hbound⟩)
  exact ⟨hint, le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
    (eventually_atTop.2 ⟨0, hbound⟩)⟩

/-- **Gramian equation on `[0, ∞)`.** If `Aᵀ W + W A + Cᵀ C = 0` and the solution `x` of
`x' = A *ᵥ x` tends to `0`, then the output energy `‖C x‖²` is integrable on `(0, ∞)` with
integral exactly `x 0 ⬝ᵥ W *ᵥ x 0`. Neither `W ⪰ 0` nor observability is assumed. -/
theorem integrableOn_Ioi_and_integral_eq
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t)
    (hR : Aᵀ * W + W * A + Cᵀ * C = 0) (hx₀ : Tendsto x atTop (𝓝 0)) :
    IntegrableOn (fun t => C *ᵥ x t ⬝ᵥ C *ᵥ x t) (Ioi 0) ∧
      ∫ t in Ioi 0, C *ᵥ x t ⬝ᵥ C *ᵥ x t = x 0 ⬝ᵥ W *ᵥ x 0 := by
  have hpart : ∀ T, 0 ≤ T →
      ∫ t in 0..T, C *ᵥ x t ⬝ᵥ C *ᵥ x t = x 0 ⬝ᵥ W *ᵥ x 0 - x T ⬝ᵥ W *ᵥ x T := fun T hT => by
    rw [integral_mulVec_dotProduct_eq (W := W) hx hT, hR]
    simp
  have hV : Tendsto (fun T => x T ⬝ᵥ W *ᵥ x T) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((continuous_dotProduct_mulVec W).tendsto 0).comp hx₀
  have hlim : Tendsto (fun T => ∫ t in 0..T, C *ᵥ x t ⬝ᵥ C *ᵥ x t) atTop
      (𝓝 (x 0 ⬝ᵥ W *ᵥ x 0)) := by
    refine (tendsto_congr' (eventually_atTop.2 ⟨0, fun T hT => (hpart T hT).symm⟩)).1 ?_
    simpa using hV.const_sub (x 0 ⬝ᵥ W *ᵥ x 0)
  have hint := integrableOn_Ioi_of_bounded (fun t => dotProduct_self_nonneg' _)
    (integrableOn_Ioc_mulVec_dotProduct hx) (hlim.eventually (eventually_le_nhds (lt_add_one _)))
  exact ⟨hint, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) hlim⟩

/-- **Energy decay in coordinates.** If `Aᵀ P + P A ⪯ K P` as quadratic forms, every solution of
`x' = A *ᵥ x` on `[0, ∞)` satisfies `x t ⬝ᵥ P *ᵥ x t ≤ exp (K t) (x 0 ⬝ᵥ P *ᵥ x 0)` for `t ≥ 0`. -/
theorem dotProduct_mulVec_le_exp_mul {P : Matrix n n ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) {K : ℝ}
    (hK : ∀ y, y ⬝ᵥ (Aᵀ * P + P * A) *ᵥ y ≤ K * (y ⬝ᵥ P *ᵥ y)) {t : ℝ} (ht : 0 ≤ t) :
    x t ⬝ᵥ P *ᵥ x t ≤ Real.exp (K * t) * (x 0 ⬝ᵥ P *ᵥ x 0) := by
  simpa using le_exp_mul_sub_mul_of_hasDerivWithinAt
    (fun τ hτ => hasDerivWithinAt_dotProduct_mulVec (P := P) hx hτ) (fun τ _ => hK (x τ)) ht

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] {A P : Matrix n n ℝ} {x : ℝ → n → ℝ}

/-- `N ⪯ M` as matrices gives the inequality of quadratic forms. -/
private theorem dotProduct_mulVec_le_of_posSemidef_sub {M N : Matrix n n ℝ}
    (h : (M - N).PosSemidef) (y : n → ℝ) : y ⬝ᵥ N *ᵥ y ≤ y ⬝ᵥ M *ᵥ y := by
  have := h.dotProduct_mulVec_nonneg y
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
  linarith

/-- **Certified decay rate.** If `Aᵀ P + P A + 2 α P ⪯ 0`, every solution of `x' = A *ᵥ x` on
`[0, ∞)` satisfies `V (x t) ≤ exp (-2 α t) V (x 0)` for `V y = y ⬝ᵥ P *ᵥ y` and `t ≥ 0`. -/
theorem dotProduct_mulVec_le_exp_neg_mul
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) {α : ℝ}
    (hP : (-(Aᵀ * P + P * A + (2 * α) • P)).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    x t ⬝ᵥ P *ᵥ x t ≤ Real.exp (-(2 * α) * t) * (x 0 ⬝ᵥ P *ᵥ x 0) := by
  refine dotProduct_mulVec_le_exp_mul hx (fun y => ?_) ht
  have := hP.dotProduct_mulVec_nonneg y
  simp only [star_trivial, neg_mulVec, add_mulVec, smul_mulVec, dotProduct_neg, dotProduct_add,
    dotProduct_smul, smul_eq_mul] at this ⊢
  linarith

/-- **Certified state decay.** If moreover `m 1 ⪯ P ⪯ M 1` with `m > 0`, every solution of
`x' = A *ᵥ x` on `[0, ∞)` satisfies `‖x t‖₂² ≤ (M / m) exp (-2 α t) ‖x 0‖₂²` for `t ≥ 0`, where
`‖y‖₂² = y ⬝ᵥ y`. -/
theorem dotProduct_self_le_exp_neg_mul [DecidableEq n]
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) {α m M : ℝ}
    (hP : (-(Aᵀ * P + P * A + (2 * α) • P)).PosSemidef) (hm : 0 < m)
    (hlow : (P - m • 1).PosSemidef) (hup : (M • 1 - P).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    x t ⬝ᵥ x t ≤ M / m * Real.exp (-(2 * α) * t) * (x 0 ⬝ᵥ x 0) := by
  have hl := dotProduct_mulVec_le_of_posSemidef_sub hlow (x t)
  have hu := dotProduct_mulVec_le_of_posSemidef_sub hup (x 0)
  simp only [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hl hu
  have hd := dotProduct_mulVec_le_exp_neg_mul hx hP ht
  have he := Real.exp_pos (-(2 * α) * t)
  rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀' hm]
  calc m * (x t ⬝ᵥ x t) ≤ x t ⬝ᵥ P *ᵥ x t := hl
    _ ≤ Real.exp (-(2 * α) * t) * (x 0 ⬝ᵥ P *ᵥ x 0) := hd
    _ ≤ Real.exp (-(2 * α) * t) * (M * (x 0 ⬝ᵥ x 0)) := mul_le_mul_of_nonneg_left hu he.le
    _ = M * (Real.exp (-(2 * α) * t) * (x 0 ⬝ᵥ x 0)) := by ring

/-- **Certified output decay from an initial state.** If `Aᵀ P + P A + 2 α P ⪯ 0`,
`Cᵀ C ⪯ γ P` with `γ ≥ 0` and `P ⪯ M 1`, every solution of `x' = A *ᵥ x` on `[0, ∞)` satisfies
`‖C x t‖₂² ≤ γ M exp (-2 α t) ‖x 0‖₂²` for `t ≥ 0`. The bound is normalized by the initial
state, not by the initial output, which may vanish although the state stores energy. -/
theorem mulVec_dotProduct_le_exp_neg_mul [DecidableEq n] {p : Type*} [Fintype p]
    {C : Matrix p n ℝ} (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t)
    {α γ M : ℝ} (hP : (-(Aᵀ * P + P * A + (2 * α) • P)).PosSemidef)
    (hC : (γ • P - Cᵀ * C).PosSemidef) (hγ : 0 ≤ γ) (hup : (M • 1 - P).PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) : C *ᵥ x t ⬝ᵥ C *ᵥ x t ≤ γ * M * Real.exp (-(2 * α) * t) * (x 0 ⬝ᵥ x 0) := by
  have hc := dotProduct_mulVec_le_of_posSemidef_sub hC (x t)
  have hu := dotProduct_mulVec_le_of_posSemidef_sub hup (x 0)
  rw [dotProduct_transpose_mul_mulVec, smul_mulVec, dotProduct_smul, smul_eq_mul] at hc
  simp only [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hu
  have hd := dotProduct_mulVec_le_exp_neg_mul hx hP ht
  have he := (Real.exp_pos (-(2 * α) * t)).le
  calc C *ᵥ x t ⬝ᵥ C *ᵥ x t ≤ γ * (x t ⬝ᵥ P *ᵥ x t) := hc
    _ ≤ γ * (Real.exp (-(2 * α) * t) * (M * (x 0 ⬝ᵥ x 0))) :=
      mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left hu he)) hγ
    _ = _ := by ring

/-- Every `exp (t • A) *ᵥ y` solves `x' = A *ᵥ x` on `[0, ∞)`. -/
theorem hasDerivWithinAt_exp_smul_mulVec [DecidableEq n] (A : Matrix n n ℝ) (y : n → ℝ) :
    ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun τ => exp (τ • A) *ᵥ y) (A *ᵥ (exp (t • A) *ᵥ y)) (Ici 0) t := by
  have h := ContinuousLinearMap.isTrajectoryOn_exp_smul_apply (toEuclideanCLM (𝕜 := ℝ) A)
    (WithLp.toLp 2 y) (Ici 0)
  have e : (fun t : ℝ => exp (t • toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 y)) =
      fun t => WithLp.toLp 2 (exp (t • A) *ᵥ y) := by
    funext t
    rw [← ofLp_exp_smul_toEuclideanCLM_apply, WithLp.toLp_ofLp]
  rw [e] at h
  exact isTrajectoryOn_toEuclideanCLM_iff.1 h

/-- An exponentially stable `ẋ = A x` drives every `exp (t • A) *ᵥ y` to `0`. -/
theorem tendsto_exp_smul_mulVec [DecidableEq n]
    (hA : (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable) (y : n → ℝ) :
    Tendsto (fun t : ℝ => exp (t • A) *ᵥ y) atTop (𝓝 0) := by
  obtain ⟨M, α, hα, hM⟩ := hA
  have hx := (isTrajectoryOn_toEuclideanCLM_iff (x := fun t => exp (t • A) *ᵥ y)
    (s := Ici (0 : ℝ))).2 (hasDerivWithinAt_exp_smul_mulVec A y)
  have hlim : Tendsto (fun t => M * Real.exp (-(α * t)) * ‖WithLp.toLp 2 y‖) atTop (𝓝 0) := by
    have : Tendsto (fun t => Real.exp (-(α * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hα))
    simpa using (this.const_mul M).mul_const ‖WithLp.toLp 2 y‖
  have h0 : Tendsto (fun t : ℝ => WithLp.toLp 2 (exp (t • A) *ᵥ y)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    simpa using hM _ hx t ht
  simpa [Function.comp_def] using ((PiLp.continuous_ofLp 2 _).tendsto 0).comp h0


/-- The output energy of `t ↦ exp (t • A) *ᵥ u` under the Gramian equation and stability. -/
private theorem gramian_key {W : Matrix n n ℝ} {p : Type*} [Fintype p] [DecidableEq n]
    {C : Matrix p n ℝ} (hR : Aᵀ * W + W * A + Cᵀ * C = 0)
    (hA : (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable) (u : n → ℝ) :
    IntegrableOn (fun t : ℝ => C *ᵥ (exp (t • A) *ᵥ u) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ u)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), C *ᵥ (exp (t • A) *ᵥ u) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ u) = u ⬝ᵥ W *ᵥ u := by
  have h := integrableOn_Ioi_and_integral_eq (hasDerivWithinAt_exp_smul_mulVec A u) hR
    (tendsto_exp_smul_mulVec hA u)
  simp only [zero_smul, NormedSpace.exp_zero, one_mulVec] at h
  exact h

/-- **The observability Gramian as an integral.** If `W` is symmetric, `Aᵀ W + W A + Cᵀ C = 0`
and `ẋ = A x` is exponentially stable, then for all `y`, `z`
`y ⬝ᵥ W *ᵥ z = ∫₀^∞ (C exp (t A) y) ⬝ᵥ (C exp (t A) z) dt`, the integrand being integrable. With
`y`, `z` standard basis vectors this is `W = ∫₀^∞ exp (t Aᵀ) Cᵀ C exp (t A) dt` entrywise. -/
theorem dotProduct_mulVec_eq_integral [DecidableEq n] {W : Matrix n n ℝ} {p : Type*} [Fintype p]
    {C : Matrix p n ℝ} (hW : Wᵀ = W) (hR : Aᵀ * W + W * A + Cᵀ * C = 0)
    (hA : (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable) (y z : n → ℝ) :
    IntegrableOn (fun t : ℝ => C *ᵥ (exp (t • A) *ᵥ y) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ z)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), C *ᵥ (exp (t • A) *ᵥ y) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ z) = y ⬝ᵥ W *ᵥ z := by
  have hfun : (fun t : ℝ => C *ᵥ (exp (t • A) *ᵥ y) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ z)) = fun t =>
      (C *ᵥ (exp (t • A) *ᵥ (y + z)) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ (y + z)) -
        C *ᵥ (exp (t • A) *ᵥ (y - z)) ⬝ᵥ C *ᵥ (exp (t • A) *ᵥ (y - z))) / 4 := by
    funext t
    simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
      dotProduct_sub]
    rw [dotProduct_comm (C *ᵥ (exp (t • A) *ᵥ z))]
    ring
  have h₁ := gramian_key hR hA (y + z)
  have h₂ := gramian_key hR hA (y - z)
  have hsymm : z ⬝ᵥ W *ᵥ y = y ⬝ᵥ W *ᵥ z := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hW]
  rw [hfun]
  refine ⟨(h₁.1.sub h₂.1).div_const 4, ?_⟩
  rw [integral_div, integral_sub h₁.1 h₂.1, h₁.2, h₂.2]
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, hsymm]
  ring

/-- **A Gramian solution is positive semidefinite.** If `W` is symmetric,
`Aᵀ W + W A + Cᵀ C = 0` and `ẋ = A x` is exponentially stable, then `W ⪰ 0`. `W` may be singular:
neither observability nor `W ≻ 0` is required. -/
theorem posSemidef_of_lyapunov_eq [DecidableEq n] {W : Matrix n n ℝ} {p : Type*} [Fintype p]
    {C : Matrix p n ℝ} (hW : W.IsHermitian) (hR : Aᵀ * W + W * A + Cᵀ * C = 0)
    (hA : (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable) : W.PosSemidef :=
  .of_dotProduct_mulVec_nonneg hW fun y => by
    rw [star_trivial, ← (gramian_key hR hA y).2]
    exact setIntegral_nonneg measurableSet_Ioi fun t _ => dotProduct_self_nonneg' _

end Matrix

namespace LTISystem

variable {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m] [Fintype p]
  {S : LTISystem n m p} {W P : Matrix n n ℝ}

omit [Fintype p] in
/-- `h t *ᵥ v = C *ᵥ (exp (t A) *ᵥ (B *ᵥ v))`, for every `t`. -/
private theorem responseKernel_mulVec_eq' (t : ℝ) (v : m → ℝ) :
    S.responseKernel t *ᵥ v = S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ v)) := by
  rw [responseKernel_eq, mulVec_mulVec, mulVec_mulVec]

omit [Fintype n] [DecidableEq n] [Fintype p] in
/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the columns. -/
private theorem sum_sq_eq_sum_mulVec_single [DecidableEq m] {k : Type*} [Fintype k]
    (M : Matrix k m ℝ) :
    ∑ i, ∑ j, M i j ^ 2 = ∑ j, M *ᵥ Pi.single j 1 ⬝ᵥ M *ᵥ Pi.single j 1 := by
  simp only [mulVec_single_one, dotProduct, col_apply, sq]
  exact Finset.sum_comm

omit [DecidableEq n] [Fintype p] in
/-- `vᵀ (Bᵀ W B) v = (B v)ᵀ W (B v)`. -/
private theorem dotProduct_transpose_mul_mul_mulVec (B : Matrix n m ℝ) (W : Matrix n n ℝ)
    (v : m → ℝ) : v ⬝ᵥ (Bᵀ * W * B) *ᵥ v = B *ᵥ v ⬝ᵥ W *ᵥ (B *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [DecidableEq n] [Fintype p] in
/-- `tr (Bᵀ W B) = ∑ⱼ (B eⱼ)ᵀ W (B eⱼ)`. -/
private theorem trace_eq_sum [DecidableEq m] (B : Matrix n m ℝ) (W : Matrix n n ℝ) :
    trace (Bᵀ * W * B) = ∑ j, B *ᵥ Pi.single j 1 ⬝ᵥ W *ᵥ (B *ᵥ Pi.single j 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← dotProduct_transpose_mul_mul_mulVec, diag_apply, mulVec_single_one, single_one_dotProduct,
    col_apply]

/-- The squared Frobenius norm of `h t` is the output energy density of the trajectories from the
columns of `B`. -/
private theorem frobeniusSq_eq [DecidableEq m] (t : ℝ) :
    ∑ i, ∑ j, S.responseKernel t i j ^ 2 = ∑ j, S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single j 1)) ⬝ᵥ
      S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single j 1)) := by
  simp only [sum_sq_eq_sum_mulVec_single, responseKernel_mulVec_eq']

/-! ### Exact energy from the Gramian equation -/

/-- **Finite-horizon storage identity.** If `Aᵀ W + W A + Cᵀ C = 0`, then for `T ≥ 0`
`∫₀ᵀ ‖h t‖_F² = tr (Bᵀ W B) - tr (X Tᵀ W X T)` with `X T = exp (T A) B`. No stability is
assumed. -/
theorem integral_frobeniusSq_eq (hR : S.Aᵀ * W + W * S.A + S.Cᵀ * S.C = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in 0..T, ∑ i, ∑ j, S.responseKernel t i j ^ 2 =
      trace (S.Bᵀ * W * S.B) - trace ((exp (T • S.A) * S.B)ᵀ * W * (exp (T • S.A) * S.B)) := by
  classical
  rw [intervalIntegral.integral_congr fun t _ => frobeniusSq_eq t,
    intervalIntegral.integral_finsetSum fun j _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
        (integrableOn_Ioc_mulVec_dotProduct (hasDerivWithinAt_exp_smul_mulVec S.A _) T),
    trace_eq_sum, trace_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mulVec_dotProduct_eq (W := W) (hasDerivWithinAt_exp_smul_mulVec S.A _) hT, hR]
  simp only [← mulVec_mulVec, zero_smul, NormedSpace.exp_zero, one_mulVec, zero_mulVec,
    dotProduct_zero, intervalIntegral.integral_zero, add_zero]

/-- **Exact input-direction energy.** If `Aᵀ W + W A + Cᵀ C = 0` and `ẋ = A x` is exponentially
stable, then `‖h t v‖₂²` is integrable on `(0, ∞)` and `∫₀^∞ ‖h t v‖₂² = (B v)ᵀ W (B v)`. -/
theorem integrableOn_Ioi_and_integral_mulVec_eq (hR : S.Aᵀ * W + W * S.A + S.Cᵀ * S.C = 0)
    (hA : (toEuclideanCLM (𝕜 := ℝ) S.A).IsExponentiallyStable) (v : m → ℝ) :
    IntegrableOn (fun t => S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v) (Ioi 0) ∧
      ∫ t in Ioi 0, S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v =
        S.B *ᵥ v ⬝ᵥ W *ᵥ (S.B *ᵥ v) := by
  simp only [responseKernel_mulVec_eq']
  exact gramian_key hR hA (S.B *ᵥ v)

/-- **Exact impulse-response energy.** If `Aᵀ W + W A + Cᵀ C = 0` and `ẋ = A x` is exponentially
stable, then `‖h t‖_F² = ∑ i, ∑ j, h t i j ^ 2` is integrable on `(0, ∞)` and
`∫₀^∞ ‖h t‖_F² = tr (Bᵀ W B)`. `W` need not be positive definite. -/
theorem integrableOn_Ioi_and_integral_frobeniusSq_eq
    (hR : S.Aᵀ * W + W * S.A + S.Cᵀ * S.C = 0)
    (hA : (toEuclideanCLM (𝕜 := ℝ) S.A).IsExponentiallyStable) :
    IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, S.responseKernel t i j ^ 2 = trace (S.Bᵀ * W * S.B) := by
  classical
  have h := fun j => integrableOn_Ioi_and_integral_mulVec_eq hR hA (Pi.single j (1 : ℝ))
  simp only [sum_sq_eq_sum_mulVec_single, trace_eq_sum]
  exact ⟨integrable_finsetSum _ fun j _ => (h j).1,
    (integral_finsetSum _ fun j _ => (h j).1).trans (Finset.sum_congr rfl fun j _ => (h j).2)⟩

/-! ### Upper bounds from a dissipation inequality -/

/-- **Input-direction energy bound.** If `W ⪰ 0` and `Aᵀ W + W A + Cᵀ C ⪯ 0`, then `‖h t v‖₂²`
is integrable on `(0, ∞)` and `∫₀^∞ ‖h t v‖₂² ≤ (B v)ᵀ W (B v)`. No stability of `A` is assumed,
and none follows. -/
theorem integrableOn_Ioi_and_integral_mulVec_le (hW : W.PosSemidef)
    (hR : (-(S.Aᵀ * W + W * S.A + S.Cᵀ * S.C)).PosSemidef) (v : m → ℝ) :
    IntegrableOn (fun t => S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v) (Ioi 0) ∧
      ∫ t in Ioi 0, S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤
        S.B *ᵥ v ⬝ᵥ W *ᵥ (S.B *ᵥ v) := by
  have h := integrableOn_Ioi_and_integral_le (C := S.C) (W := W)
    (hasDerivWithinAt_exp_smul_mulVec S.A (S.B *ᵥ v))
    (fun y => by
      have := hR.dotProduct_mulVec_nonneg y
      simp only [star_trivial, neg_mulVec, dotProduct_neg] at this
      linarith)
    (fun y => by simpa using hW.dotProduct_mulVec_nonneg y)
  simp only [zero_smul, NormedSpace.exp_zero, one_mulVec] at h
  simp only [responseKernel_mulVec_eq']
  exact h

/-- **Impulse-response energy bound.** If `W ⪰ 0` and `Aᵀ W + W A + Cᵀ C ⪯ 0`, then
`‖h t‖_F²` is integrable on `(0, ∞)` and `∫₀^∞ ‖h t‖_F² ≤ tr (Bᵀ W B)`. No stability of `A` is
assumed, and none follows. -/
theorem integrableOn_Ioi_and_integral_frobeniusSq_le (hW : W.PosSemidef)
    (hR : (-(S.Aᵀ * W + W * S.A + S.Cᵀ * S.C)).PosSemidef) :
    IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤ trace (S.Bᵀ * W * S.B) := by
  classical
  have h := fun j => integrableOn_Ioi_and_integral_mulVec_le hW hR (Pi.single j (1 : ℝ))
  simp only [sum_sq_eq_sum_mulVec_single, trace_eq_sum]
  exact ⟨integrable_finsetSum _ fun j _ => (h j).1,
    (integral_finsetSum _ fun j _ => (h j).1).trans_le (Finset.sum_le_sum fun j _ => (h j).2)⟩

/-! ### Decay envelopes -/

/-- The output energy density decays: `‖h t v‖₂² ≤ γ exp (-2 α t) (B v)ᵀ P (B v)`. -/
private theorem responseKernel_mulVec_sq_le_aux {α γ : ℝ}
    (hP : (-(S.Aᵀ * P + P * S.A + (2 * α) • P)).PosSemidef)
    (hC : (γ • P - S.Cᵀ * S.C).PosSemidef) (hγ : 0 ≤ γ) (v : m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤
      γ * Real.exp (-(2 * α) * t) * (S.B *ᵥ v ⬝ᵥ P *ᵥ (S.B *ᵥ v)) := by
  have hd := dotProduct_mulVec_le_exp_neg_mul (hasDerivWithinAt_exp_smul_mulVec S.A (S.B *ᵥ v))
    hP ht
  simp only [zero_smul, NormedSpace.exp_zero, one_mulVec] at hd
  have hc := dotProduct_mulVec_le_of_posSemidef_sub hC (exp (t • S.A) *ᵥ (S.B *ᵥ v))
  rw [dotProduct_transpose_mul_mulVec, smul_mulVec, dotProduct_smul, smul_eq_mul] at hc
  rw [responseKernel_mulVec_eq', mul_assoc]
  exact hc.trans (mul_le_mul_of_nonneg_left hd hγ)

/-- **Certified impulse-response envelope.** If `Aᵀ P + P A + 2 α P ⪯ 0`, `Cᵀ C ⪯ γ P` with
`γ ≥ 0`, and `Bᵀ P B ⪯ β 1`, then `‖h t v‖₂² ≤ γ β exp (-2 α t) ‖v‖₂²` for every input direction
`v` and `t ≥ 0`, where `‖y‖₂² = y ⬝ᵥ y`. -/
theorem responseKernel_mulVec_sq_le [DecidableEq m] {α γ β : ℝ}
    (hP : (-(S.Aᵀ * P + P * S.A + (2 * α) • P)).PosSemidef)
    (hC : (γ • P - S.Cᵀ * S.C).PosSemidef) (hB : (β • 1 - S.Bᵀ * P * S.B).PosSemidef)
    (hγ : 0 ≤ γ) (v : m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤
      γ * β * Real.exp (-(2 * α) * t) * (v ⬝ᵥ v) := by
  have hb := dotProduct_mulVec_le_of_posSemidef_sub hB v
  rw [dotProduct_transpose_mul_mul_mulVec, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul] at hb
  have he := mul_nonneg hγ (Real.exp_pos (-(2 * α) * t)).le
  calc _ ≤ γ * Real.exp (-(2 * α) * t) * (S.B *ᵥ v ⬝ᵥ P *ᵥ (S.B *ᵥ v)) :=
        responseKernel_mulVec_sq_le_aux hP hC hγ v ht
    _ ≤ γ * Real.exp (-(2 * α) * t) * (β * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left hb he
    _ = _ := by ring

/-- **Certified Frobenius envelope.** If `Aᵀ P + P A + 2 α P ⪯ 0` and `Cᵀ C ⪯ γ P` with `γ ≥ 0`,
then `‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α t)` for `t ≥ 0`. -/
theorem frobeniusSq_responseKernel_le {α γ : ℝ}
    (hP : (-(S.Aᵀ * P + P * S.A + (2 * α) • P)).PosSemidef)
    (hC : (γ • P - S.Cᵀ * S.C).PosSemidef) (hγ : 0 ≤ γ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤
      γ * trace (S.Bᵀ * P * S.B) * Real.exp (-(2 * α) * t) := by
  classical
  rw [sum_sq_eq_sum_mulVec_single, trace_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have := responseKernel_mulVec_sq_le_aux hP hC hγ (Pi.single j 1) ht
  linarith

/-- **Certified energy tail.** If `α > 0`, `Aᵀ P + P A + 2 α P ⪯ 0` and `Cᵀ C ⪯ γ P` with
`γ ≥ 0`, then for `T ≥ 0` the tail `‖h t‖_F²` is integrable on `(T, ∞)` and
`∫_T^∞ ‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α T) / (2 α)`. -/
theorem integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le {α γ : ℝ} (hα : 0 < α)
    (hP : (-(S.Aᵀ * P + P * S.A + (2 * α) • P)).PosSemidef)
    (hC : (γ • P - S.Cᵀ * S.C).PosSemidef) (hγ : 0 ≤ γ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T) ∧
      ∫ t in Ioi T, ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤
        γ * trace (S.Bᵀ * P * S.B) * Real.exp (-(2 * α) * T) / (2 * α) := by
  classical
  set c := γ * trace (S.Bᵀ * P * S.B)
  have hneg : -(2 * α) < 0 := by linarith
  have hg : IntegrableOn (fun t => c * Real.exp (-(2 * α) * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul c
  have henv : ∀ t ∈ Ioi T, ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤ c * Real.exp (-(2 * α) * t) :=
    fun t ht => frobeniusSq_responseKernel_le hP hC hγ (hT.trans (le_of_lt ht))
  have hcont : ContinuousOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T) := by
    refine ContinuousOn.congr (f := fun t => ∑ j, S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ
      Pi.single j 1)) ⬝ᵥ S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single j 1))) ?_
      fun t _ => frobeniusSq_eq t
    refine continuousOn_finsetSum _ fun j _ => ?_
    have hx : ContinuousOn (fun t => exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single j 1)) (Ioi T) :=
      fun t ht => ((hasDerivWithinAt_exp_smul_mulVec S.A _ t
        (hT.trans (le_of_lt ht))).continuousWithinAt).mono fun τ hτ => hT.trans (le_of_lt hτ)
    exact ((continuous_const.matrix_mulVec continuous_id).dotProduct
      (continuous_const.matrix_mulVec continuous_id)).comp_continuousOn hx
  have hf : IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T) := by
    refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact henv t ht
  refine ⟨hf, (setIntegral_mono_on hf hg measurableSet_Ioi henv).trans_eq ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hneg]
  field_simp

end LTISystem
