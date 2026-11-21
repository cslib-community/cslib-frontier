/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Closeness of families of measurements

Rigidity arguments compare *families* of measurements `A = (A^q_a)_{q,a}`, indexed by a question
`q` and an outcome `a`, in a state `φ` and under a question distribution `μ`. The source's relation
[Ji, Natarajan, Vidick, Wright and Yuen, §5.2, Definition 5.16][JNVWY2020] (arXiv:2001.04383v4,
p. 55) squares, sums over outcomes and averages over questions, for vector states, and bounds the
result by `O(δ)`:

`E_{q ∼ μ} ∑_a ‖(A^q_a - B^q_a) ψ‖² = O(δ)`.

The relation `A ≈ᶠ[μ, φ; δ] B` (`Cslib.Quantum.FamApprox`) adapts it. It fixes an exact budget in
place of `O(δ)`, bounds the *distance* rather than its square, so for `δ ≥ 0` it says
`E_{q ∼ μ} ∑_a ‖A^q_a - B^q_a‖²_φ ≤ δ²` (`Cslib.Quantum.famApprox_iff`), and it allows families of
arbitrary operators in an arbitrary state of an algebra. So the source's `A ≈_δ B` with constant
`C` is `A ≈ᶠ[μ, φ; √(C δ)] B`, as for single operators in
`CslibFrontier/Foundations/Quantum/Algebra/Approx.lean`.

The relation is the generic closeness `Cslib.Close` through the weighted linear map
`x ↦ (√μ(q) · x_{q,a})_{q,a}` into `ℓ²(Q × α)` over the GNS pre-inner-product space of `φ`
(`Cslib.Quantum.famL`).
This map may discard the questions of probability `0`, so it need not be injective; separately, its
seminorm does not distinguish operators of state norm `0`. The relation inherits the calculus of
`Cslib.Close` and composes in `calc` chains. Per-question bounds turn into family closeness
(`Cslib.Quantum.famApprox_of_forall`). For example, consistent measurements are close
(`Cslib.Quantum.Measurement.famApprox_of_agreement`).

## Main definitions

* `Cslib.Quantum.famL`: the weighted linear map of families into `ℓ²`.
* `Cslib.Quantum.FamApprox`: closeness of families, notation `A ≈ᶠ[μ, φ; δ] B`.
* `Cslib.Quantum.Measurement.effects`: the effects of a family of measurements.

## Main results

* `Cslib.Quantum.famApprox_iff`: for `δ ≥ 0`, `A ≈ᶠ[μ, φ; δ] B` iff
  `E_q ∑_a ‖A^q_a - B^q_a‖²_φ ≤ δ²`.
* `Cslib.Quantum.famApprox_of_forall`: per-question bounds give family closeness.
* `Cslib.Quantum.Measurement.famApprox_of_agreement`: consistency implies closeness, for families.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

open Finset

namespace Cslib.Quantum

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A] {Q α : Type*} [Fintype Q] [Fintype α]

/-- The weighted linear map `x ↦ (√μ(q) · x_{q,a})_{q,a}` of families into `ℓ²(Q × α)` over the
GNS pre-inner-product space of `φ`. Its norm is `√(E_{q∼μ} ∑_a ‖x_{q,a}‖²_φ)`
(`Cslib.Quantum.norm_famL_sq`). It discards the questions of probability `0`. -/
noncomputable def famL (μ : PMF Q) (φ : AlgState A) :
    (Q → α → A) →ₗ[ℂ] PiLp 2 (fun _ : Q × α => φ.toPositiveLinearMap.PreGNS) where
  toFun x := WithLp.toLp 2 fun p => (√(μ p.1).toReal : ℂ) • φ.toPreGNS (x p.1 p.2)
  map_add' x y := by ext p; simp [smul_add]
  map_smul' z x := by ext p; simp [smul_comm z]

theorem norm_famL_sq (μ : PMF Q) (φ : AlgState A) (x : Q → α → A) :
    ‖famL μ φ x‖ ^ 2 = ∑ q, (μ q).toReal * ∑ a, φ.norm (x q a) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [famL, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg]
  rfl

/-- `x` and `y` are `δ`-close as families in the state `φ` under the question distribution `μ`:
`‖famL μ φ (x - y)‖ ≤ δ`, which for `δ ≥ 0` is `E_{q∼μ} ∑_a ‖x_{q,a} - y_{q,a}‖²_φ ≤ δ²`
(`Cslib.Quantum.famApprox_iff`). A named relation, so that it elaborates under binders. -/
def FamApprox (μ : PMF Q) (φ : AlgState A) (δ : ℝ) (x y : Q → α → A) : Prop :=
  x ≈[famL μ φ | δ] y

@[inherit_doc] scoped[Cslib.Quantum] notation:50 x " ≈ᶠ[" μ ", " φ "; " δ "] " y:50 =>
  Cslib.Quantum.FamApprox μ φ δ x y

variable {μ : PMF Q} {φ : AlgState A} {x y z : Q → α → A} {δ δ' : ℝ}

theorem famApprox_iff (hδ : 0 ≤ δ) :
    x ≈ᶠ[μ, φ; δ] y ↔ ∑ q, (μ q).toReal * ∑ a, φ.norm (x q a - y q a) ^ 2 ≤ δ ^ 2 := by
  rw [FamApprox, Close, ← pow_le_pow_iff_left₀ (norm_nonneg _) hδ two_ne_zero, norm_famL_sq]
  rfl

theorem FamApprox.symm (h : x ≈ᶠ[μ, φ; δ] y) : y ≈ᶠ[μ, φ; δ] x :=
  Close.symm h

theorem FamApprox.mono (h : x ≈ᶠ[μ, φ; δ] y) (hδ : δ ≤ δ') : x ≈ᶠ[μ, φ; δ'] y :=
  Close.mono h hδ

/-- Errors add along chains of family approximations. -/
theorem FamApprox.trans (h₁ : x ≈ᶠ[μ, φ; δ] y) (h₂ : y ≈ᶠ[μ, φ; δ'] z) :
    x ≈ᶠ[μ, φ; δ + δ'] z :=
  Close.trans h₁ h₂

instance : @Trans (Q → α → A) _ _ (FamApprox μ φ δ) (FamApprox μ φ δ') (FamApprox μ φ (δ + δ')) :=
  ⟨FamApprox.trans⟩

/-- Per-question bounds `∑_a ‖x_{q,a} - y_{q,a}‖²_φ ≤ ε` give family closeness `√ε`. -/
theorem famApprox_of_forall {ε : ℝ} (h : ∀ q, ∑ a, φ.norm (x q a - y q a) ^ 2 ≤ ε) :
    x ≈ᶠ[μ, φ; √ε] y := by
  obtain ⟨q₀, -⟩ := μ.support_nonempty
  have hε : 0 ≤ ε := (sum_nonneg fun _ _ => sq_nonneg _).trans (h q₀)
  rw [famApprox_iff (Real.sqrt_nonneg _), Real.sq_sqrt hε]
  calc ∑ q, (μ q).toReal * ∑ a, φ.norm (x q a - y q a) ^ 2 ≤ ∑ q, (μ q).toReal * ε :=
        sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (h q) ENNReal.toReal_nonneg
    _ = ε := by rw [← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

namespace Measurement

/-- The effects `(A^q_a)_{q,a}` of a family of measurements. -/
def effects (M : Q → Measurement α A) : Q → α → A :=
  fun q a => (M q).effect a

variable [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] in
/-- **Consistency implies closeness**, for families: measurements agreeing with probability at
least `1 - ε` on every question are `√(2ε)`-close as families. -/
theorem famApprox_of_agreement (μ : PMF Q) (φ : AlgState A) (M R : Q → Measurement α A)
    (hc : ∀ q a, Commute ((M q).effect a) ((R q).effect a)) {ε : ℝ}
    (h : ∀ q, 1 - ε ≤ agreement φ (M q) (R q)) : effects M ≈ᶠ[μ, φ; √(2 * ε)] effects R :=
  famApprox_of_forall fun q => sum_norm_sub_sq_le_of_agreement φ (M q) (R q) (hc q) (h q)

end Measurement

end Cslib.Quantum
