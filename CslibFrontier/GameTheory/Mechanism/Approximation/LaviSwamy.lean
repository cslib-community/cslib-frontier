/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Compactness.Compact
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lavi–Swamy LP-Based Randomized Truthful-in-Expectation Mechanisms

This module formalizes the convex-decomposition and randomized VCG framework of Lavi and Swamy
([LaviSwamy2011]; [CarrVempala2002]; [NisanRoughgardenTardosVazirani2007], Chapter 12, §12.3,
locators not verified against primary PDF).

Consider `ι` agents whose linear valuations over a finite coordinate space `κ` are vectors
`vᵢ : κ → ℝ`, a fractional feasible polytope `P : Set (κ → ℝ)`, and a finite nonempty set of
integral outcomes indexed by `Ω` via `embed : Ω → κ → ℝ`. The core structural result is the
**Carr–Vempala / Lavi–Swamy Decomposition Lemma**: if an `α`-integrality-gap verifier ensures that
for every real weight vector `w : κ → ℝ` some integral outcome `ω : Ω` satisfies
`(w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω`, then `(1 / α) • x` lies in the convex hull of `{embed ω | ω : Ω}`,
and hence is realized in expectation by a distribution `μ : PMF Ω`
(`exists_convex_decomposition_of_integralityGap`, proved algebraically via Farkas' lemma
`Matrix.exists_nonneg_mulVec_eq_iff`). Under downward closure of `embed`, verifying the gap on
nonnegative weights suffices for all real weights (`integralityGap_of_nonneg_approx`).

Combining convex decomposition with a fractional VCG mechanism on `P` yields the **Lavi–Swamy
randomized mechanism**: on reported valuations `b`, it computes a fractional welfare maximizer
`x*(b) ∈ P`, decomposes `(1 / α) • x*(b)` into `μ(b) : PMF Ω`, samples `ω ∼ μ(b)`, and charges
either deterministic scaled fractional VCG payments `(1 / α) * p_VCG(b)` (`laviSwamyDet`) or
outcome-dependent payments proportional to realized value (`laviSwamyExPost`). Both achieve exact
truthfulness in expectation and expected welfare `(1 / α) * OPT_frac(b) ≥ (1 / α) * OPT_int(b)`;
the outcome-dependent variant is moreover ex-post individually rational and satisfies ex-post no
positive transfers on nonnegative valuations.

Running time (Ellipsoid separation via the integrality-gap verifier) is not formalized here; this
module captures the exact LP duality / convex-decomposition, incentive, IR/NPT, and approximation
theorems of §12.3.

## Main definitions

* `Cslib.GameTheory.Mechanism.LaviSwamy.expectedVal`: expectation of a real function under a `PMF`
  on a finite type.
* `Cslib.GameTheory.Mechanism.LaviSwamy.RandomizedLinearMechanism`: randomized outcome rule
  `outcomeDist : (ι → κ → ℝ) → PMF Ω` with outcome-dependent payments `payment b ω i`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.VerifiesIntegralityGap`: every real linear objective on `P`
  is `α`-approximated by some integral outcome in `range embed`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.IsFracWelfareMax`, `fracVcgPayment`: fractional welfare
  maximization and Clarke-pivot VCG payments on `P`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.laviSwamyDet`, `laviSwamyExPost`: the deterministic-payment
  and ex-post-IR Lavi–Swamy randomized mechanisms.

## Main results

* `Cslib.GameTheory.Mechanism.LaviSwamy.exists_convex_decomposition_of_integralityGap`:
  **Carr–Vempala / Lavi–Swamy Decomposition Lemma**: `(1 / α) • x` is a convex combination of
  `embed` (realized by a `PMF Ω`) whenever every real weight vector is `α`-approximated on `x`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.integralityGap_of_nonneg_approx`: downward-closed integral
  sets upgrade a nonnegative-weight `α`-approximation to an `α`-integrality-gap verifier for all
  real weights.
* `Cslib.GameTheory.Mechanism.LaviSwamy.laviSwamyDet_isTruthfulInExpectation`,
  `laviSwamyDet_expectedWelfare_eq`, `laviSwamyDet_approx_integral`: exact truthfulness in
  expectation and `α`-approximation for `laviSwamyDet`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.laviSwamyExPost_isTruthfulInExpectationOn`,
  `laviSwamyExPost_isExPostIROn`, `laviSwamyExPost_isExPostNPTOn`,
  `laviSwamyExPost_expectedWelfare_eq`, `laviSwamyExPost_approx_integral`: exact truthfulness in
  expectation, ex-post IR, ex-post NPT, and `α`-approximation for `laviSwamyExPost`.
* `Cslib.GameTheory.Mechanism.LaviSwamy.exists_laviSwamyExPost_of_isCompact`: unconditional
  existence of such a mechanism on any compact nonempty packing polytope `P`.

## References

* [R. D. Carr and S. Vempala, *Randomized Metarounding*][CarrVempala2002]
* [R. Lavi and C. Swamy, *Truthful and Near-Optimal Mechanism Design via Linear
  Programming*][LaviSwamy2011]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*, Chapter 12, §12.3][NisanRoughgardenTardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.Mechanism.LaviSwamy

open Finset Matrix

/-! ### Finite `PMF` Expectations -/

section ExpectedVal

variable {Ω κ : Type*} [Fintype Ω]

/-- Expectation `∑ ω, (p ω).toReal * g ω` of `g : Ω → ℝ` under a `PMF Ω` on a finite type. -/
@[expose] noncomputable def expectedVal (p : PMF Ω) (g : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, (p ω).toReal * g ω

theorem expectedVal_const (p : PMF Ω) (c : ℝ) : expectedVal p (fun _ => c) = c := by
  simp only [expectedVal, ← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

theorem expectedVal_sub (p : PMF Ω) (g₁ g₂ : Ω → ℝ) :
    expectedVal p (fun ω => g₁ ω - g₂ ω) = expectedVal p g₁ - expectedVal p g₂ := by
  simp only [expectedVal, mul_sub, Finset.sum_sub_distrib]

theorem expectedVal_mul_const (p : PMF Ω) (g : Ω → ℝ) (c : ℝ) :
    expectedVal p (fun ω => g ω * c) = expectedVal p g * c := by
  simp only [expectedVal, Finset.sum_mul, mul_assoc]

theorem expectedVal_sum {ι : Type*} [Fintype ι] (p : PMF Ω) (g : ι → Ω → ℝ) :
    expectedVal p (fun ω => ∑ i : ι, g i ω) = ∑ i : ι, expectedVal p (g i) := by
  simp only [expectedVal, Finset.mul_sum]
  exact Finset.sum_comm

/-- Expectation of a linear functional `ω ↦ v ⬝ᵥ embed ω` equals `v` dotted with the expected
vector `∑ ω, (p ω).toReal • embed ω`. -/
theorem expectedVal_dotProduct [Fintype κ] (p : PMF Ω) (embed : Ω → κ → ℝ) (v : κ → ℝ) :
    expectedVal p (fun ω => v ⬝ᵥ embed ω) =
      v ⬝ᵥ (∑ ω : Ω, (p ω).toReal • embed ω) := by
  simp only [expectedVal, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Convert a real probability vector on a finite type into a `PMF`. -/
noncomputable def pmfOfRealWeights (μ : Ω → ℝ) (hnonneg : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω : Ω, μ ω = 1) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (μ ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hnonneg ω), hsum, ENNReal.ofReal_one])

@[simp]
theorem pmfOfRealWeights_toReal (μ : Ω → ℝ) (hnonneg : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω : Ω, μ ω = 1) (ω : Ω) :
    (pmfOfRealWeights μ hnonneg hsum ω).toReal = μ ω := by
  simp only [pmfOfRealWeights, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hnonneg ω)]

end ExpectedVal

/-! ### Carr–Vempala / Lavi–Swamy Convex Decomposition Lemma -/

section Decomposition

variable {Ω κ : Type*} [Fintype Ω] [Fintype κ]

/-- A finite integral outcome set `embed : Ω → κ → ℝ` satisfies an **`α`-integrality gap** on
`P : Set (κ → ℝ)` if every real linear objective `w : κ → ℝ` on every `x ∈ P` is at most `α` times
the best integral outcome value ([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007], Chapter 12,
Definition 12.13, locator not verified against primary PDF). -/
@[expose] def VerifiesIntegralityGap (P : Set (κ → ℝ)) (embed : Ω → κ → ℝ) (α : ℝ) : Prop :=
  ∀ (w : κ → ℝ) (x : κ → ℝ), x ∈ P → ∃ ω : Ω, (w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω

/-- **Carr–Vempala / Lavi–Swamy Decomposition Lemma** ([CarrVempala2002]; [LaviSwamy2011];
[NisanRoughgardenTardosVazirani2007], Chapter 12, Lemma 12.14 and Claims 12.17–12.18, locators not
verified against primary PDF): if every real weight vector `w : κ → ℝ` admits an integral outcome
`ω : Ω` with `(w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω`, then `(1 / α) • x` is a convex combination of
`{embed ω | ω : Ω}`, realized by a probability mass function `p : PMF Ω`. -/
theorem exists_convex_decomposition_of_integralityGap (embed : Ω → κ → ℝ) {x : κ → ℝ} {α : ℝ}
    (hgap : ∀ w : κ → ℝ, ∃ ω : Ω, (w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω) :
    ∃ p : PMF Ω, ∑ ω : Ω, (p ω).toReal • embed ω = (1 / α) • x := by
  let A : Matrix (κ ⊕ Unit) Ω ℝ := Sum.elim (fun k ω => embed ω k) (fun _ _ => 1)
  let b : κ ⊕ Unit → ℝ := Sum.elim ((1 / α) • x) (fun _ => 1)
  obtain ⟨μ, hμ_nonneg, hAμ⟩ : ∃ μ : Ω → ℝ, 0 ≤ μ ∧ A *ᵥ μ = b := by
    rw [Matrix.exists_nonneg_mulVec_eq_iff]
    intro y hy
    obtain ⟨ω₀, hω₀⟩ := hgap (fun k => -y (.inl k))
    have hω₀_ge : 0 ≤ ∑ k, y (.inl k) * embed ω₀ k + y (.inr ()) := by
      simpa only [Pi.zero_apply, vecMul, dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
        Finset.sum_singleton, PUnit.default_eq_unit, A, Sum.elim_inl, Sum.elim_inr, mul_one]
        using hy ω₀
    simp only [dotProduct, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
      PUnit.default_eq_unit, b, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
      mul_one, one_div_mul_eq_div, ← mul_div_assoc, ← Finset.sum_div]
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, neg_div] at hω₀
    linarith
  have hsum : ∑ ω : Ω, μ ω = 1 := by
    simpa only [mulVec, dotProduct, A, b, Sum.elim_inr, one_mul] using congr_fun hAμ (.inr ())
  refine ⟨pmfOfRealWeights μ hμ_nonneg hsum, funext fun k => ?_⟩
  simpa only [mulVec, dotProduct, A, b, Sum.elim_inl, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, pmfOfRealWeights_toReal, mul_comm _ (μ _)] using congr_fun hAμ (.inl k)

omit [Fintype Ω] in
/-- The scaled fractional point `(1 / α) • x` lies in `convexHull ℝ (Set.range embed)` whenever
`x` satisfies the real-weight `α`-integrality-gap condition. -/
theorem scaled_mem_convexHull_of_integralityGap [Finite Ω] (embed : Ω → κ → ℝ) {x : κ → ℝ} {α : ℝ}
    (hgap : ∀ w : κ → ℝ, ∃ ω : Ω, (w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω) :
    (1 / α) • x ∈ convexHull ℝ (Set.range embed) := by
  have := Fintype.ofFinite Ω
  obtain ⟨p, hp⟩ := exists_convex_decomposition_of_integralityGap embed hgap
  simpa only [Finset.centerMass, Cslib.Probability.PMF.sum_toReal, inv_one, one_smul, hp] using
    Finset.centerMass_mem_convexHull (s := Set.range embed) (t := Finset.univ)
      (w := fun ω : Ω => (p ω).toReal)
      (fun _ _ => ENNReal.toReal_nonneg)
      ((Cslib.Probability.PMF.sum_toReal p).symm ▸ zero_lt_one)
      (fun ω _ => Set.mem_range_self ω)

omit [Fintype Ω] in
/-- **Clamping negative weights** ([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007],
Chapter 12, Claim 12.19, locator not verified against primary PDF): when `x ≥ 0` and `embed` is
closed under zeroing arbitrary subsets of coordinates, an `α`-approximation for nonnegative weights
upgrades to an `α`-integrality-gap verifier for all real weights. -/
theorem integralityGap_of_nonneg_approx [DecidableEq κ] {embed : Ω → κ → ℝ} {x : κ → ℝ} {α : ℝ}
    (hα : 0 < α) (hx : 0 ≤ x)
    (hdown : ∀ (ω : Ω) (S : Finset κ), ∃ ω' : Ω,
      ∀ k : κ, embed ω' k = if k ∈ S then embed ω k else 0)
    (hnonneg : ∀ w : κ → ℝ, 0 ≤ w → ∃ ω : Ω, (w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω) :
    ∀ w : κ → ℝ, ∃ ω : Ω, (w ⬝ᵥ x) / α ≤ w ⬝ᵥ embed ω := by
  intro w
  let wPos : κ → ℝ := fun k => max 0 (w k)
  obtain ⟨ω, hω⟩ := hnonneg wPos fun k => le_max_left 0 (w k)
  obtain ⟨ω', hω'⟩ := hdown ω (Finset.univ.filter fun k : κ => 0 ≤ w k)
  refine ⟨ω', ?_⟩
  calc (w ⬝ᵥ x) / α
    _ ≤ (wPos ⬝ᵥ x) / α := div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (le_max_right 0 (w k)) (hx k))
          hα.le
    _ ≤ wPos ⬝ᵥ embed ω := hω
    _ = w ⬝ᵥ embed ω' := Finset.sum_congr rfl fun k _ => by
          rw [hω' k]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, wPos]
          split_ifs with hk
          · rw [max_eq_right hk]
          · rw [max_eq_left (le_of_not_ge hk), zero_mul, mul_zero]

end Decomposition

/-! ### Fractional VCG and the Lavi–Swamy Randomized Mechanisms -/

section Mechanism

variable {ι Ω κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype κ]

/-- A randomized direct-revelation mechanism for agents `ι` with linear valuations `vᵢ : κ → ℝ`
over an integral outcome space `Ω`. On reported valuation profiles `b`, it outputs a distribution
`outcomeDist b : PMF Ω` and charges agent `i` the payment `payment b ω i` when outcome `ω` is
realized. -/
structure RandomizedLinearMechanism (ι Ω κ : Type*) where
  /-- The distribution over integral outcomes. -/
  outcomeDist : (ι → κ → ℝ) → PMF Ω
  /-- The payment charged to agent `i` when outcome `ω` is realized. -/
  payment : (ι → κ → ℝ) → Ω → ι → ℝ

/-- Expected quasilinear utility `E_{ω ∼ outcomeDist b}[v ⬝ᵥ embed ω - payment b ω i]` of agent
`i` with true linear valuation `v` on reported profile `b`. -/
@[expose] noncomputable def RandomizedLinearMechanism.expectedUtility
    (M : RandomizedLinearMechanism ι Ω κ) (embed : Ω → κ → ℝ) (i : ι)
    (v : κ → ℝ) (b : ι → κ → ℝ) : ℝ :=
  expectedVal (M.outcomeDist b) fun ω => v ⬝ᵥ embed ω - M.payment b ω i

/-- **Truthfulness in expectation** on a domain `D` of linear valuation profiles: truthful
reporting maximizes every agent's expected quasilinear utility. -/
@[expose] def RandomizedLinearMechanism.IsTruthfulInExpectationOn
    (M : RandomizedLinearMechanism ι Ω κ) (embed : Ω → κ → ℝ)
    (D : Set (ι → κ → ℝ)) : Prop :=
  ∀ b ∈ D, ∀ (i : ι) (v : κ → ℝ), Function.update b i v ∈ D →
    M.expectedUtility embed i v b ≤ M.expectedUtility embed i v (Function.update b i v)

/-- **Ex-post individual rationality** on a domain `D`: for every realized outcome `ω`, a truthful
agent's realized utility `bᵢ ⬝ᵥ embed ω - payment b ω i` is nonnegative. -/
@[expose] def RandomizedLinearMechanism.IsExPostIROn
    (M : RandomizedLinearMechanism ι Ω κ) (embed : Ω → κ → ℝ)
    (D : Set (ι → κ → ℝ)) : Prop :=
  ∀ b ∈ D, ∀ (i : ι) (ω : Ω), 0 ≤ b i ⬝ᵥ embed ω - M.payment b ω i

/-- **Ex-post no positive transfers (NPT)** on a domain `D`: every realized payment is
nonnegative. -/
@[expose] def RandomizedLinearMechanism.IsExPostNPTOn
    (M : RandomizedLinearMechanism ι Ω κ) (D : Set (ι → κ → ℝ)) : Prop :=
  ∀ b ∈ D, ∀ (i : ι) (ω : Ω), 0 ≤ M.payment b ω i

/-- Expected social welfare `E_{ω ∼ outcomeDist b}[∑ᵢ bᵢ ⬝ᵥ embed ω]` of the randomized
mechanism on reported profile `b`. -/
@[expose] noncomputable def RandomizedLinearMechanism.expectedWelfare
    (M : RandomizedLinearMechanism ι Ω κ) (embed : Ω → κ → ℝ) (b : ι → κ → ℝ) : ℝ :=
  expectedVal (M.outcomeDist b) fun ω => ∑ i : ι, b i ⬝ᵥ embed ω

/-- The domain of nonnegative linear valuation profiles `b i k ≥ 0`. -/
@[expose] def nonnegValProfiles : Set (ι → κ → ℝ) :=
  {b | ∀ i, 0 ≤ b i}

/-- Fractional welfare maximization over a polytope `P`: `xStar b ∈ P` maximizes
`∑ᵢ bᵢ ⬝ᵥ x` over `P`. -/
@[expose] def IsFracWelfareMax (P : Set (κ → ℝ)) (xStar : (ι → κ → ℝ) → κ → ℝ) : Prop :=
  ∀ b, xStar b ∈ P ∧ ∀ x ∈ P, (∑ i : ι, b i ⬝ᵥ x) ≤ ∑ i : ι, b i ⬝ᵥ xStar b

/-- Others' fractional welfare maximization for Clarke pivots: `othersMax i b ∈ P` maximizes
`∑_{j ≠ i} bⱼ ⬝ᵥ x` over `P` and depends only on `b_{-i}`. -/
@[expose] def IsOthersFracWelfareMax (P : Set (κ → ℝ))
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ) : Prop :=
  (∀ i b, othersMax i b ∈ P ∧
    ∀ x ∈ P, (∑ j ∈ Finset.univ.erase i, b j ⬝ᵥ x) ≤
      ∑ j ∈ Finset.univ.erase i, b j ⬝ᵥ othersMax i b) ∧
  (∀ i b v, othersMax i (Function.update b i v) = othersMax i b)

/-- The fractional VCG (Clarke-pivot) payment of agent `i` on report profile `b`. -/
@[expose] def fracVcgPayment (xStar : (ι → κ → ℝ) → κ → ℝ)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ) (b : ι → κ → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, b j ⬝ᵥ othersMax i b) -
    ∑ j ∈ Finset.univ.erase i, b j ⬝ᵥ xStar b

private theorem sum_erase_dotProduct_update (b : ι → κ → ℝ) (i : ι) (v : κ → ℝ) (x : κ → ℝ) :
    ∑ j ∈ Finset.univ.erase i, Function.update b i v j ⬝ᵥ x =
      ∑ j ∈ Finset.univ.erase i, b j ⬝ᵥ x :=
  Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem fracVcgPayment_nonneg {P : Set (κ → ℝ)} {xStar : (ι → κ → ℝ) → κ → ℝ}
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (ho : IsOthersFracWelfareMax P othersMax) (b : ι → κ → ℝ) (i : ι) :
    0 ≤ fracVcgPayment xStar othersMax b i :=
  sub_nonneg.mpr ((ho.1 i b).2 (xStar b) (hx b).1)

theorem fracVcgPayment_le_val {P : Set (κ → ℝ)} {xStar : (ι → κ → ℝ) → κ → ℝ}
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (ho : IsOthersFracWelfareMax P othersMax) {b : ι → κ → ℝ} (i : ι)
    (hnonneg : 0 ≤ b i ⬝ᵥ othersMax i b) :
    fracVcgPayment xStar othersMax b i ≤ b i ⬝ᵥ xStar b := by
  have hmax := (hx b).2 (othersMax i b) (ho.1 i b).1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hmax
  simp only [fracVcgPayment]
  linarith

private theorem fracVcg_dsic_ineq {P : Set (κ → ℝ)} {xStar : (ι → κ → ℝ) → κ → ℝ}
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (ho : IsOthersFracWelfareMax P othersMax) (b : ι → κ → ℝ) (i : ι) (v : κ → ℝ) :
    v ⬝ᵥ xStar b - fracVcgPayment xStar othersMax b i ≤
      v ⬝ᵥ xStar (Function.update b i v) -
        fracVcgPayment xStar othersMax (Function.update b i v) i := by
  have hmax := (hx (Function.update b i v)).2 (xStar b) (hx b).1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Function.update_self,
    sum_erase_dotProduct_update, sum_erase_dotProduct_update] at hmax
  simp only [fracVcgPayment, ho.2 i b v, sum_erase_dotProduct_update]
  linarith

/-- Choose a convex-decomposition distribution `μ(b) : PMF Ω` for `(1 / α) • xStar b`. -/
noncomputable def decompDist {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (hgap : VerifiesIntegralityGap P embed α) (b : ι → κ → ℝ) : PMF Ω :=
  (exists_convex_decomposition_of_integralityGap embed
    (fun w => hgap w (xStar b) (hx b).1)).choose

omit [DecidableEq ι] in
theorem decompDist_expectation {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (hgap : VerifiesIntegralityGap P embed α) (b : ι → κ → ℝ) :
    ∑ ω : Ω, (decompDist hx hgap b ω).toReal • embed ω = (1 / α) • xStar b :=
  (exists_convex_decomposition_of_integralityGap embed
    (fun w => hgap w (xStar b) (hx b).1)).choose_spec

omit [DecidableEq ι] in
theorem decompDist_expectedVal_dotProduct {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (hgap : VerifiesIntegralityGap P embed α) (b : ι → κ → ℝ) (v : κ → ℝ) :
    expectedVal (decompDist hx hgap b) (fun ω => v ⬝ᵥ embed ω) =
      (1 / α) * (v ⬝ᵥ xStar b) := by
  rw [expectedVal_dotProduct, decompDist_expectation, dotProduct_smul, smul_eq_mul]

/-- The **Lavi–Swamy randomized mechanism with deterministic scaled VCG payments**
([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Definition 12.15, locator not
verified against primary PDF): samples `ω ∼ decompDist hx hgap b` and charges deterministic payment
`(1 / α) * fracVcgPayment xStar othersMax b i`. -/
@[expose] noncomputable def laviSwamyDet {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) : RandomizedLinearMechanism ι Ω κ where
  outcomeDist := decompDist hx hgap
  payment b _ i := (1 / α) * fracVcgPayment xStar othersMax b i

/-- **Truthfulness in expectation of `laviSwamyDet`** ([LaviSwamy2011];
[NisanRoughgardenTardosVazirani2007], Chapter 12, Lemma 12.16, locator not verified against
primary PDF): holds on all real linear valuation profiles when `0 < α`. -/
theorem laviSwamyDet_isTruthfulInExpectation {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    (hα : 0 < α) {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (ho : IsOthersFracWelfareMax P othersMax)
    (hgap : VerifiesIntegralityGap P embed α) :
    (laviSwamyDet hx othersMax hgap).IsTruthfulInExpectationOn embed Set.univ := by
  intro b _ i v _
  simp only [RandomizedLinearMechanism.expectedUtility, laviSwamyDet, expectedVal_sub,
    expectedVal_const, decompDist_expectedVal_dotProduct]
  linarith [mul_le_mul_of_nonneg_left (fracVcg_dsic_ineq hx ho b i v)
    (div_nonneg zero_le_one hα.le)]

/-- **Exact expected welfare identity for `laviSwamyDet`**: expected welfare equals
`(1 / α)` times the optimal fractional welfare. -/
theorem laviSwamyDet_expectedWelfare_eq {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) (b : ι → κ → ℝ) :
    (laviSwamyDet hx othersMax hgap).expectedWelfare embed b =
      (1 / α) * (∑ i : ι, b i ⬝ᵥ xStar b) := by
  simp only [RandomizedLinearMechanism.expectedWelfare, laviSwamyDet, expectedVal_sum,
    decompDist_expectedVal_dotProduct, Finset.mul_sum]

/-- **`α`-approximation to every integral outcome for `laviSwamyDet`**: when every integral
outcome lies in `P`, expected welfare is at least `(1 / α)` times the welfare of every `ω : Ω`. -/
theorem laviSwamyDet_approx_integral {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    (hα : 0 < α) {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) (hembed : ∀ ω, embed ω ∈ P)
    (b : ι → κ → ℝ) (ω : Ω) :
    (1 / α) * (∑ i : ι, b i ⬝ᵥ embed ω) ≤
      (laviSwamyDet hx othersMax hgap).expectedWelfare embed b := by
  rw [laviSwamyDet_expectedWelfare_eq]
  exact mul_le_mul_of_nonneg_left ((hx b).2 (embed ω) (hembed ω)) (div_nonneg zero_le_one hα.le)

/-- The **Lavi–Swamy randomized mechanism with ex-post IR outcome-dependent payments**
([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Lemma 12.16, locator not
verified against primary PDF): charges `(bᵢ ⬝ᵥ embed ω) * (p_VCG(b) / (bᵢ ⬝ᵥ x*(b)))` when
`bᵢ ⬝ᵥ x*(b) > 0`, and `0` otherwise. -/
@[expose] noncomputable def laviSwamyExPost {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) : RandomizedLinearMechanism ι Ω κ where
  outcomeDist := decompDist hx hgap
  payment b ω i :=
    if 0 < b i ⬝ᵥ xStar b then
      (b i ⬝ᵥ embed ω) * (fracVcgPayment xStar othersMax b i / (b i ⬝ᵥ xStar b))
    else 0

private theorem laviSwamyExPost_expectedPayment_eq {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (ho : IsOthersFracWelfareMax P othersMax)
    (hgap : VerifiesIntegralityGap P embed α) (hP_nonneg : ∀ x ∈ P, 0 ≤ x)
    {b : ι → κ → ℝ} (hb : b ∈ nonnegValProfiles) (i : ι) :
    expectedVal (decompDist hx hgap b)
        (fun ω => (laviSwamyExPost hx othersMax hgap).payment b ω i) =
      (1 / α) * fracVcgPayment xStar othersMax b i := by
  simp only [laviSwamyExPost]
  split_ifs with hpos
  · rw [expectedVal_mul_const, decompDist_expectedVal_dotProduct]
    field_simp [hpos.ne']
  · rw [expectedVal_const]
    have hp0 : fracVcgPayment xStar othersMax b i = 0 :=
      le_antisymm ((fracVcgPayment_le_val hx ho i
        (dotProduct_nonneg_of_nonneg (hb i) (hP_nonneg _ (ho.1 i b).1))).trans (not_lt.mp hpos))
        (fracVcgPayment_nonneg hx ho b i)
    simp [hp0]

/-- **Truthfulness in expectation of `laviSwamyExPost`** on nonnegative linear valuation profiles
([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Lemma 12.16, locator not
verified against primary PDF). -/
theorem laviSwamyExPost_isTruthfulInExpectationOn {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    (hα : 0 < α) {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (ho : IsOthersFracWelfareMax P othersMax)
    (hgap : VerifiesIntegralityGap P embed α) (hP_nonneg : ∀ x ∈ P, 0 ≤ x) :
    (laviSwamyExPost hx othersMax hgap).IsTruthfulInExpectationOn embed nonnegValProfiles := by
  intro b hb i v hv
  have hout : (laviSwamyExPost hx othersMax hgap).outcomeDist = decompDist hx hgap := rfl
  simp only [RandomizedLinearMechanism.expectedUtility, expectedVal_sub, hout,
    laviSwamyExPost_expectedPayment_eq hx ho hgap hP_nonneg hb i,
    laviSwamyExPost_expectedPayment_eq hx ho hgap hP_nonneg hv i,
    decompDist_expectedVal_dotProduct]
  linarith [mul_le_mul_of_nonneg_left (fracVcg_dsic_ineq hx ho b i v)
    (div_nonneg zero_le_one hα.le)]

/-- **Ex-post individual rationality of `laviSwamyExPost`** on nonnegative valuation profiles
when integral outcomes are nonnegative (`0 ≤ embed ω`). -/
theorem laviSwamyExPost_isExPostIROn {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (ho : IsOthersFracWelfareMax P othersMax)
    (hgap : VerifiesIntegralityGap P embed α) (hP_nonneg : ∀ x ∈ P, 0 ≤ x)
    (hembed_nonneg : ∀ ω, 0 ≤ embed ω) :
    (laviSwamyExPost hx othersMax hgap).IsExPostIROn embed nonnegValProfiles := by
  intro b hb i ω
  simp only [laviSwamyExPost, sub_nonneg]
  have hval := dotProduct_nonneg_of_nonneg (hb i) (hembed_nonneg ω)
  split_ifs with hpos
  · calc (b i ⬝ᵥ embed ω) * (fracVcgPayment xStar othersMax b i / (b i ⬝ᵥ xStar b))
      _ ≤ (b i ⬝ᵥ embed ω) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hpos).mpr
            (fracVcgPayment_le_val hx ho i
              (dotProduct_nonneg_of_nonneg (hb i) (hP_nonneg _ (ho.1 i b).1)))) hval
      _ = b i ⬝ᵥ embed ω := mul_one _
  · exact hval

/-- **Ex-post no positive transfers (NPT) of `laviSwamyExPost`** on nonnegative valuation profiles
when integral outcomes are nonnegative. -/
theorem laviSwamyExPost_isExPostNPTOn {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    {othersMax : ι → (ι → κ → ℝ) → κ → ℝ} (ho : IsOthersFracWelfareMax P othersMax)
    (hgap : VerifiesIntegralityGap P embed α) (hembed_nonneg : ∀ ω, 0 ≤ embed ω) :
    (laviSwamyExPost hx othersMax hgap).IsExPostNPTOn nonnegValProfiles := by
  intro b hb i ω
  simp only [laviSwamyExPost]
  split_ifs with hpos
  · exact mul_nonneg (dotProduct_nonneg_of_nonneg (hb i) (hembed_nonneg ω))
      (div_nonneg (fracVcgPayment_nonneg hx ho b i) hpos.le)
  · exact le_rfl

/-- **Exact expected welfare identity for `laviSwamyExPost`**. -/
theorem laviSwamyExPost_expectedWelfare_eq {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) (b : ι → κ → ℝ) :
    (laviSwamyExPost hx othersMax hgap).expectedWelfare embed b =
      (1 / α) * (∑ i : ι, b i ⬝ᵥ xStar b) := by
  simp only [RandomizedLinearMechanism.expectedWelfare, laviSwamyExPost, expectedVal_sum,
    decompDist_expectedVal_dotProduct, Finset.mul_sum]

/-- **`α`-approximation to every integral outcome for `laviSwamyExPost`**. -/
theorem laviSwamyExPost_approx_integral {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    (hα : 0 < α) {xStar : (ι → κ → ℝ) → κ → ℝ} (hx : IsFracWelfareMax P xStar)
    (othersMax : ι → (ι → κ → ℝ) → κ → ℝ)
    (hgap : VerifiesIntegralityGap P embed α) (hembed : ∀ ω, embed ω ∈ P)
    (b : ι → κ → ℝ) (ω : Ω) :
    (1 / α) * (∑ i : ι, b i ⬝ᵥ embed ω) ≤
      (laviSwamyExPost hx othersMax hgap).expectedWelfare embed b := by
  rw [laviSwamyExPost_expectedWelfare_eq]
  exact mul_le_mul_of_nonneg_left ((hx b).2 (embed ω) (hembed ω)) (div_nonneg zero_le_one hα.le)

/-- **Existence of a Lavi–Swamy randomized mechanism on any compact packing polytope**
([LaviSwamy2011]; [NisanRoughgardenTardosVazirani2007], Chapter 12, §12.3, locator not verified
against primary PDF): for any compact nonempty polytope `P ⊆ {x | 0 ≤ x}` containing `range embed`
and satisfying an `α`-integrality gap, there exists a randomized mechanism that is truthful in
expectation, ex-post IR, ex-post NPT, and achieves at least `(1 / α)` of the optimal fractional
(and hence integral) social welfare on every nonnegative valuation profile. -/
theorem exists_laviSwamyExPost_of_isCompact {P : Set (κ → ℝ)} {embed : Ω → κ → ℝ} {α : ℝ}
    (hα : 0 < α) (hP_compact : IsCompact P) (hP_ne : P.Nonempty)
    (hP_nonneg : ∀ x ∈ P, 0 ≤ x) (hembed : ∀ ω, embed ω ∈ P)
    (hgap : VerifiesIntegralityGap P embed α) :
    ∃ M : RandomizedLinearMechanism ι Ω κ,
      M.IsTruthfulInExpectationOn embed nonnegValProfiles ∧
      M.IsExPostIROn embed nonnegValProfiles ∧
      M.IsExPostNPTOn nonnegValProfiles ∧
      (∀ b : ι → κ → ℝ, ∀ x ∈ P, (1 / α) * (∑ i : ι, b i ⬝ᵥ x) ≤ M.expectedWelfare embed b) ∧
      (∀ b : ι → κ → ℝ, ∀ ω : Ω,
        (1 / α) * (∑ i : ι, b i ⬝ᵥ embed ω) ≤ M.expectedWelfare embed b) := by
  have hsum_dot (s : Finset ι) (f : ι → κ → ℝ) (y : κ → ℝ) :
      (∑ i ∈ s, f i) ⬝ᵥ y = ∑ i ∈ s, f i ⬝ᵥ y := by
    simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hcont (w : κ → ℝ) : Continuous fun x : κ → ℝ => w ⬝ᵥ x :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
  have hex (w : κ → ℝ) : ∃ x ∈ P, ∀ y ∈ P, w ⬝ᵥ y ≤ w ⬝ᵥ x :=
    let ⟨x, hxP, hxmax⟩ := hP_compact.exists_isMaxOn hP_ne (hcont w).continuousOn
    ⟨x, hxP, fun _ hy => hxmax hy⟩
  choose opt hoptP hoptMax using hex
  let xStar : (ι → κ → ℝ) → κ → ℝ := fun b => opt (∑ i : ι, b i)
  let othersMax : ι → (ι → κ → ℝ) → κ → ℝ := fun i b =>
    opt (∑ j ∈ Finset.univ.erase i, b j)
  have hx : IsFracWelfareMax P xStar := fun b =>
    ⟨hoptP _, fun y hy => by simpa only [hsum_dot] using hoptMax (∑ i : ι, b i) y hy⟩
  have ho : IsOthersFracWelfareMax P othersMax :=
    ⟨fun i b => ⟨hoptP _, fun y hy => by
      simpa only [hsum_dot] using hoptMax (∑ j ∈ Finset.univ.erase i, b j) y hy⟩,
     fun i b v => congrArg opt (Finset.sum_congr rfl fun j hj =>
       Function.update_of_ne (Finset.ne_of_mem_erase hj) v b)⟩
  exact ⟨laviSwamyExPost hx othersMax hgap,
    laviSwamyExPost_isTruthfulInExpectationOn hα hx ho hgap hP_nonneg,
    laviSwamyExPost_isExPostIROn hx ho hgap hP_nonneg fun ω => hP_nonneg _ (hembed ω),
    laviSwamyExPost_isExPostNPTOn hx ho hgap fun ω => hP_nonneg _ (hembed ω),
    fun b x hxP => (laviSwamyExPost_expectedWelfare_eq hx othersMax hgap b).symm ▸
      mul_le_mul_of_nonneg_left ((hx b).2 x hxP) (div_nonneg zero_le_one hα.le),
    laviSwamyExPost_approx_integral hα hx othersMax hgap hembed⟩

end Mechanism

end Cslib.GameTheory.Mechanism.LaviSwamy
