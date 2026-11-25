/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.PredictionMarket.ScoringRules
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hanson's Logarithmic Market Scoring Rule (LMSR)

Robin Hanson's *market scoring rule* (MSR) turns any proper scoring rule `S` into a sequential
automated market maker: a trader who updates the market's reported distribution from `p₁` to `p₂`
receives net payoff `S.score p₂ ω - S.score p₁ ω` when outcome `ω` occurs
[Hanson2003; PennockSami2007, §26.4.1, pp. 663–664]. Sequential payoffs telescope across any chain
of updates, so the market maker's net loss depends only on the initial and final distributions.

For the logarithmic scoring rule scaled by liquidity parameter `b > 0`, Hanson's **Logarithmic
Market Scoring Rule (LMSR)** is equivalent to a cost-function automated market maker with cost
function

  `lmsrCost b q = b * Real.log (∑ ω, Real.exp (q ω / b))`

and instantaneous price vector given by the softmax distribution

  `lmsrPrice b q ω = Real.exp (q ω / b) / ∑ ω', Real.exp (q ω' / b)`

[Hanson2007; PennockSami2007, §26.4.1, pp. 663–664].

## Main definitions

* `Cslib.GameTheory.PredictionMarket.msrStepPayoff`: net payoff `S.score p₂ ω - S.score p₁ ω` of
  a single market scoring rule update.
* `Cslib.GameTheory.PredictionMarket.msrTotalPayoff`: cumulative payoff across `T` sequential MSR
  updates.
* `Cslib.GameTheory.PredictionMarket.lmsrCost`: Hanson's LMSR cost function
  `b * log (∑ ω, exp (q ω / b))`.
* `Cslib.GameTheory.PredictionMarket.lmsrPrice`: the instantaneous softmax price vector
  `exp (q ω / b) / ∑ ω', exp (q ω' / b)`.
* `Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff`: net payoff `(q₂ ω - q₁ ω) - (C(q₂) - C(q₁))`
  to the trader (equivalently, the market maker's net loss) when moving from `q₁` to `q₂` and
  outcome `ω` occurs.

## Main results

* `Cslib.GameTheory.PredictionMarket.msrTotalPayoff_eq_sub`: telescoping of sequential MSR payoffs.
* `Cslib.GameTheory.PredictionMarket.msrStepPayoff_expected_lt`: myopic truthfulness of a strictly
  proper market scoring rule.
* `Cslib.GameTheory.PredictionMarket.lmsrPrice_mem_openProbSimplex`: LMSR instantaneous prices
  always lie in the open probability simplex.
* `Cslib.GameTheory.PredictionMarket.hasFDerivAt_lmsrCost`,
  `Cslib.GameTheory.PredictionMarket.hasDerivAt_lmsrCost_update`: the gradient (and coordinate
  partial derivatives) of `lmsrCost b` equals the softmax price vector `lmsrPrice b q`
  [PennockSami2007, §26.4.1, pp. 663–664].
* `Cslib.GameTheory.PredictionMarket.lmsrCost_bregmanDivergence_eq`,
  `Cslib.GameTheory.PredictionMarket.convexOn_lmsrCost`: original mathematical companions proving
  the exact KL-divergence Bregman identity for `lmsrCost b` and global convexity of `lmsrCost b`
  on `ℝ^Ω`.
* `Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_eq_msrStepPayoff`,
  `Cslib.GameTheory.PredictionMarket.sum_lmsrTraderPayoff_eq_msrTotalPayoff`,
  `Cslib.GameTheory.PredictionMarket.exists_shares_lmsrTraderPayoff_eq_msrStepPayoff`: pointwise
  and sequential equivalence between LMSR cost-function trading and Hanson's logarithmic market
  scoring rule [PennockSami2007, §26.4.1, pp. 663–664].
* `Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_le`,
  `Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_seq_le`,
  `Cslib.GameTheory.PredictionMarket.exists_lmsrTraderPayoff_zero_gt`: worst-case market-maker
  loss starting from zero shares is at most `b * log |Ω|`, and this bound is tight
  [PennockSami2007, §26.4.1, pp. 663–664; Hanson2007].

## References

* [R. Hanson, *Combinatorial Information Market Design*][Hanson2003]
* [R. Hanson, *Logarithmic Market Scoring Rules for Modular Combinatorial Information
  Aggregation*][Hanson2007]
* [D. M. Pennock, R. Sami, *Computational Aspects of Prediction Markets*, Chapter 26 of
  *Algorithmic Game Theory*][PennockSami2007]
-/

public section

open Finset Matrix Set

namespace Cslib.GameTheory.PredictionMarket

section MSR

variable {Ω : Type*}

/-- Net payoff `S.score p₂ ω - S.score p₁ ω` to a trader who updates the market scoring rule from
distribution `p₁` to `p₂` when outcome `ω` realizes
[Hanson2003; PennockSami2007, §26.4.1, pp. 663–664]. -/
def msrStepPayoff (S : ScoringRule Ω) (p₁ p₂ : Ω → ℝ) (ω : Ω) : ℝ :=
  S.score p₂ ω - S.score p₁ ω

@[simp]
theorem msrStepPayoff_apply (S : ScoringRule Ω) (p₁ p₂ : Ω → ℝ) (ω : Ω) :
    msrStepPayoff S p₁ p₂ ω = S.score p₂ ω - S.score p₁ ω := by
  rfl

/-- Cumulative payoff across `T` sequential updates `reports 0 → reports 1 → … → reports T` under
market scoring rule `S`. -/
def msrTotalPayoff (S : ScoringRule Ω) (reports : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range T, msrStepPayoff S (reports t) (reports (t + 1)) ω

/-- Sequential MSR payoffs telescope: the net transfer from the market maker across any chain of
updates depends only on the initial and final distributions
[PennockSami2007, §26.4.1, pp. 663–664]. -/
theorem msrTotalPayoff_eq_sub (S : ScoringRule Ω) (reports : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) :
    msrTotalPayoff S reports T ω = S.score (reports T) ω - S.score (reports 0) ω := by
  simpa only [msrTotalPayoff, msrStepPayoff_apply] using
    sum_range_sub (fun t => S.score (reports t) ω) T

/-- Myopic truthfulness of a strictly proper market scoring rule: a trader with true belief `q ∈ P`
strictly maximizes expected net MSR payoff by updating the current report `p₁` to `q`
[Hanson2003; PennockSami2007, §26.4.1, pp. 663–664]. -/
theorem msrStepPayoff_expected_lt [Fintype Ω] {S : ScoringRule Ω} {P : Set (Ω → ℝ)}
    (hS : S.IsStrictlyProperOn P) {q p₁ p₂ : Ω → ℝ} (hq : q ∈ P) (hp₂ : p₂ ∈ P) (hne : p₂ ≠ q) :
    ∑ ω, q ω * msrStepPayoff S p₁ p₂ ω < ∑ ω, q ω * msrStepPayoff S p₁ q ω := by
  have h1 : ∀ r, ∑ ω, q ω * msrStepPayoff S p₁ r ω =
      S.expectedScore q r - S.expectedScore q p₁ := fun r => by
    simp only [msrStepPayoff_apply, mul_sub, sum_sub_distrib, ScoringRule.expectedScore_apply]
  rw [h1 p₂, h1 q]
  linarith [hS.expectedScore_lt hq hp₂ hne]

end MSR

section LMSR

variable {Ω : Type*} [Fintype Ω]

/-- Hanson's **LMSR cost function** with liquidity parameter `b`:
`C(q) = b * Real.log (∑ ω, Real.exp (q ω / b))`
[PennockSami2007, §26.4.1, pp. 663–664; Hanson2007]. -/
noncomputable def lmsrCost (b : ℝ) (q : Ω → ℝ) : ℝ :=
  b * Real.log (∑ ω, Real.exp (q ω / b))

/-- Instantaneous **LMSR price vector** (softmax probability distribution):
`p_ω(q) = Real.exp (q ω / b) / ∑ ω', Real.exp (q ω' / b)`
[PennockSami2007, §26.4.1, pp. 663–664]. -/
noncomputable def lmsrPrice (b : ℝ) (q : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (q ω / b) / ∑ ω', Real.exp (q ω' / b)

/-- Net payoff `(q₂ ω - q₁ ω) - (C(q₂) - C(q₁))` to the trader moving the LMSR state from `q₁` to
`q₂` when outcome `ω` occurs. By zero-sum accounting, this equally equals the market maker's net
loss on that transition. -/
noncomputable def lmsrTraderPayoff (b : ℝ) (q₁ q₂ : Ω → ℝ) (ω : Ω) : ℝ :=
  (q₂ ω - q₁ ω) - (lmsrCost b q₂ - lmsrCost b q₁)

@[simp]
theorem lmsrCost_apply (b : ℝ) (q : Ω → ℝ) :
    lmsrCost b q = b * Real.log (∑ ω, Real.exp (q ω / b)) := by
  rfl

@[simp]
theorem lmsrPrice_apply (b : ℝ) (q : Ω → ℝ) (ω : Ω) :
    lmsrPrice b q ω = Real.exp (q ω / b) / ∑ ω', Real.exp (q ω' / b) := by
  rfl

@[simp]
theorem lmsrTraderPayoff_apply (b : ℝ) (q₁ q₂ : Ω → ℝ) (ω : Ω) :
    lmsrTraderPayoff b q₁ q₂ ω = (q₂ ω - q₁ ω) - (lmsrCost b q₂ - lmsrCost b q₁) := by
  rfl

private theorem sum_exp_pos [Nonempty Ω] (b : ℝ) (q : Ω → ℝ) :
    0 < ∑ ω : Ω, Real.exp (q ω / b) :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- Every instantaneous LMSR price is strictly positive. -/
theorem lmsrPrice_pos [Nonempty Ω] (b : ℝ) (q : Ω → ℝ) (ω : Ω) : 0 < lmsrPrice b q ω :=
  div_pos (Real.exp_pos _) (sum_exp_pos b q)

/-- Instantaneous LMSR prices sum to `1`. -/
theorem sum_lmsrPrice [Nonempty Ω] (b : ℝ) (q : Ω → ℝ) : ∑ ω, lmsrPrice b q ω = 1 := by
  simp only [lmsrPrice_apply, ← sum_div]
  exact div_self (sum_exp_pos b q).ne'

/-- Instantaneous LMSR prices form a strictly positive probability distribution in
`openProbSimplex Ω` [PennockSami2007, §26.4.1, pp. 663–664]. -/
theorem lmsrPrice_mem_openProbSimplex [Nonempty Ω] (b : ℝ) (q : Ω → ℝ) :
    lmsrPrice b q ∈ openProbSimplex Ω :=
  ⟨isMixedStrategy_iff.2 ⟨fun ω => (lmsrPrice_pos b q ω).le, sum_lmsrPrice b q⟩, lmsrPrice_pos b q⟩

/-- At zero shares, the LMSR price is uniform over `Ω`. -/
theorem lmsrPrice_zero (b : ℝ) (ω : Ω) :
    lmsrPrice b (0 : Ω → ℝ) ω = (Fintype.card Ω : ℝ)⁻¹ := by
  simp only [lmsrPrice_apply, Pi.zero_apply, zero_div, Real.exp_zero, sum_const, card_univ,
    nsmul_eq_mul, mul_one, one_div]

/-- At zero shares, the LMSR cost equals `b * Real.log |Ω|`. -/
theorem lmsrCost_zero (b : ℝ) : lmsrCost b (0 : Ω → ℝ) = b * Real.log (Fintype.card Ω) := by
  simp only [lmsrCost_apply, Pi.zero_apply, zero_div, Real.exp_zero, sum_const, card_univ,
    nsmul_eq_mul, mul_one]

/-- Translation equivariance of `lmsrCost`: adding `c` shares of every outcome increases the cost
by exactly `c` (no-arbitrage for risk-free constant bundles). -/
theorem lmsrCost_add_const [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q : Ω → ℝ) (c : ℝ) :
    lmsrCost b (fun ω => q ω + c) = lmsrCost b q + c := by
  simp_rw [lmsrCost_apply, add_div, Real.exp_add, ← sum_mul]
  rw [Real.log_mul (sum_exp_pos b q).ne' (Real.exp_pos _).ne', Real.log_exp, mul_add,
    mul_div_cancel₀ _ hb.ne']

/-- Translation invariance of `lmsrPrice`: adding a constant share bundle leaves prices
unchanged. -/
theorem lmsrPrice_add_const {b : ℝ} (q : Ω → ℝ) (c : ℝ) :
    lmsrPrice b (fun ω => q ω + c) = lmsrPrice b q := by
  funext ω
  simp_rw [lmsrPrice_apply, add_div, Real.exp_add, ← sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_pos _).ne'

/-- Log-inversion of softmax: for any strictly positive distribution `p ∈ openProbSimplex Ω`, the
share vector `ω ↦ b * log (p ω)` induces price vector `p`. -/
theorem lmsrPrice_log_eq {b : ℝ} (hb : 0 < b) {p : Ω → ℝ} (hp : p ∈ openProbSimplex Ω) :
    lmsrPrice b (fun ω => b * Real.log (p ω)) = p := by
  funext ω
  simp only [lmsrPrice_apply]
  have hexp : ∀ i, Real.exp (b * Real.log (p i) / b) = p i := fun i => by
    rw [mul_div_cancel_left₀ _ hb.ne', Real.exp_log (hp.2 i)]
  simp only [hexp, hp.1.sum_eq_one, div_one]

/-- The log-inverted share vector `ω ↦ b * log (p ω)` has zero LMSR cost. -/
theorem lmsrCost_log_eq_zero {b : ℝ} (hb : 0 < b) {p : Ω → ℝ} (hp : p ∈ openProbSimplex Ω) :
    lmsrCost b (fun ω => b * Real.log (p ω)) = 0 := by
  simp only [lmsrCost_apply]
  have hexp : ∀ i, Real.exp (b * Real.log (p i) / b) = p i := fun i => by
    rw [mul_div_cancel_left₀ _ hb.ne', Real.exp_log (hp.2 i)]
  simp only [hexp, hp.1.sum_eq_one, Real.log_one, mul_zero]

/-! ### Instantaneous price as gradient of `lmsrCost` -/

/-- **Gradient identity for LMSR** [PennockSami2007, §26.4.1, pp. 663–664]: the Fréchet derivative
of `lmsrCost b` at `q` is `v ↦ v ⬝ᵥ lmsrPrice b q`. -/
theorem hasFDerivAt_lmsrCost [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q : Ω → ℝ) :
    HasFDerivAt (lmsrCost b) (dotCLM (lmsrPrice b q)) q := by
  have hterm (ω : Ω) : HasFDerivAt (fun x : Ω → ℝ => Real.exp (x ω / b))
      ((Real.exp (q ω / b) / b) • ContinuousLinearMap.proj (R := ℝ) ω) q := by
    have hdiv : HasFDerivAt (fun x : Ω → ℝ => x ω / b)
        (b⁻¹ • ContinuousLinearMap.proj (R := ℝ) ω) q := by
      simpa only [div_eq_inv_mul] using (hasFDerivAt_apply ω q).const_mul b⁻¹
    have hexp := (Real.hasDerivAt_exp (q ω / b)).comp_hasFDerivAt q hdiv
    rwa [smul_smul, ← div_eq_mul_inv] at hexp
  have hsum : HasFDerivAt (fun x : Ω → ℝ => ∑ ω, Real.exp (x ω / b))
      (∑ ω, (Real.exp (q ω / b) / b) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ω => ℝ) ω) q := by
    simpa only [Finset.sum_fn] using HasFDerivAt.fun_sum fun ω _ => hterm ω
  refine (((Real.hasDerivAt_log (sum_exp_pos b q).ne').comp_hasFDerivAt q hsum).const_mul
    b).congr_fderiv ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  ext v
  simp only [dotCLM_apply, dotProduct, lmsrPrice_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact sum_congr rfl fun _ _ => by field_simp [hb.ne', (sum_exp_pos b q).ne']

/-- Coordinate partial derivative of `lmsrCost b`: `∂C / ∂q_ω = lmsrPrice b q ω`
[PennockSami2007, §26.4.1, pp. 663–664]. -/
theorem hasDerivAt_lmsrCost_update [Nonempty Ω] [DecidableEq Ω] {b : ℝ} (hb : 0 < b)
    (q : Ω → ℝ) (ω : Ω) :
    HasDerivAt (fun t : ℝ => lmsrCost b (Function.update q ω t)) (lmsrPrice b q ω) (q ω) := by
  have hupd : HasDerivAt (fun t : ℝ => Function.update q ω t) (Pi.single ω (1 : ℝ)) (q ω) :=
    hasDerivAt_pi.2 fun i => by
      rcases eq_or_ne i ω with rfl | h
      · simpa only [Function.update_self, Pi.single_eq_same] using hasDerivAt_id' (q i)
      · simpa only [Function.update_of_ne h, Pi.single_eq_of_ne h] using
          hasDerivAt_const (q ω) (q i)
  simpa only [Function.update_eq_self, Function.comp_def, dotCLM_apply, single_dotProduct,
    one_mul] using
    (hasFDerivAt_lmsrCost hb (Function.update q ω (q ω))).comp_hasDerivAt (q ω) hupd

/-! ### Convexity, KL-divergence Bregman identity, and monotonicity -/

/-- Fundamental LMSR log-price identity: `q ω - C(q) = b * log (lmsrPrice b q ω)`. -/
theorem sub_lmsrCost_eq_mul_log_lmsrPrice [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q : Ω → ℝ) (ω : Ω) :
    q ω - lmsrCost b q = b * Real.log (lmsrPrice b q ω) := by
  rw [lmsrPrice_apply, Real.log_div (Real.exp_pos _).ne' (sum_exp_pos b q).ne', Real.log_exp,
    lmsrCost_apply]
  field_simp [hb.ne']

/-- Mathematical identity (original to this formalization): the Bregman divergence
`bregmanDivergence (lmsrCost b) (lmsrPrice b) q₂ q₁` equals `b` times the KL divergence (expected
log-score gap) between the induced softmax distributions `lmsrPrice b q₁` and `lmsrPrice b q₂`. -/
theorem lmsrCost_bregmanDivergence_eq [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q₁ q₂ : Ω → ℝ) :
    bregmanDivergence (lmsrCost b) (lmsrPrice b) q₂ q₁ =
      b * ((logScore Ω).expectedScore (lmsrPrice b q₁) (lmsrPrice b q₁) -
        (logScore Ω).expectedScore (lmsrPrice b q₁) (lmsrPrice b q₂)) := by
  rw [bregmanDivergence_apply]
  have hpoint (ω : Ω) : (q₂ ω - q₁ ω) - (lmsrCost b q₂ - lmsrCost b q₁) =
      b * Real.log (lmsrPrice b q₂ ω) - b * Real.log (lmsrPrice b q₁ ω) := by
    linarith [sub_lmsrCost_eq_mul_log_lmsrPrice hb q₁ ω,
      sub_lmsrCost_eq_mul_log_lmsrPrice hb q₂ ω]
  have hsum : ∑ ω, lmsrPrice b q₁ ω * ((q₂ ω - q₁ ω) - (lmsrCost b q₂ - lmsrCost b q₁)) =
      (q₂ - q₁) ⬝ᵥ lmsrPrice b q₁ - (lmsrCost b q₂ - lmsrCost b q₁) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_lmsrPrice b q₁, one_mul, dotProduct,
      Pi.sub_apply]
    congr 1
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ ω, lmsrPrice b q₁ ω * ((q₂ ω - q₁ ω) - (lmsrCost b q₂ - lmsrCost b q₁)) =
      b * ((logScore Ω).expectedScore (lmsrPrice b q₁) (lmsrPrice b q₂) -
        (logScore Ω).expectedScore (lmsrPrice b q₁) (lmsrPrice b q₁)) := by
    simp only [hpoint, ScoringRule.expectedScore_apply, logScore_score, mul_sub, sum_sub_distrib,
      mul_sum]
    congr 1 <;> exact sum_congr rfl fun _ _ => by ring
  linarith

/-- First-order subgradient inequality for `lmsrCost b`: every trade costs at least its
instantaneous price valuation `(q₂ - q₁) ⬝ᵥ lmsrPrice b q₁`. -/
theorem lmsrCost_subgradient_le [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q₁ q₂ : Ω → ℝ) :
    lmsrCost b q₁ + (q₂ - q₁) ⬝ᵥ lmsrPrice b q₁ ≤ lmsrCost b q₂ := by
  have hproper := isStrictlyProperOn_logScore.isProperOn.expectedScore_le
    (lmsrPrice_mem_openProbSimplex b q₁) (lmsrPrice_mem_openProbSimplex b q₂)
  have hbreg := lmsrCost_bregmanDivergence_eq hb q₁ q₂
  rw [bregmanDivergence_apply] at hbreg
  linarith [mul_nonneg hb.le (sub_nonneg.mpr hproper)]

/-- Global convexity of `lmsrCost b` on `ℝ^Ω` (original mathematical companion deduced from
`lmsrCost_subgradient_le` and `convexOn_of_forall_add_le`). -/
theorem convexOn_lmsrCost [Nonempty Ω] {b : ℝ} (hb : 0 < b) :
    ConvexOn ℝ (Set.univ : Set (Ω → ℝ)) (lmsrCost b) :=
  convexOn_of_forall_add_le (g := fun q : Ω → ℝ => dotCLM (lmsrPrice b q)) convex_univ
    fun q₁ _ q₂ _ => by
      simpa only [dotCLM_apply] using lmsrCost_subgradient_le hb q₁ q₂

/-- Monotonicity of `lmsrCost b`: more shares in every outcome cost at least as much. -/
theorem lmsrCost_mono [Nonempty Ω] {b : ℝ} (hb : 0 < b) {q₁ q₂ : Ω → ℝ}
    (h : ∀ ω, q₁ ω ≤ q₂ ω) : lmsrCost b q₁ ≤ lmsrCost b q₂ := by
  have hdot : 0 ≤ (q₂ - q₁) ⬝ᵥ lmsrPrice b q₁ :=
    sum_nonneg fun ω _ => mul_nonneg (sub_nonneg.mpr (h ω)) (lmsrPrice_pos b q₁ ω).le
  linarith [lmsrCost_subgradient_le hb q₁ q₂]

/-! ### Equivalence with sequential logarithmic market scoring rule -/

/-- **Single-step LMSR / MSR equivalence** [PennockSami2007, §26.4.1, pp. 663–664]: the net
payoff of moving the cost-function market maker from `q₁` to `q₂` equals the payoff of updating
Hanson's scaled logarithmic market scoring rule from `lmsrPrice b q₁` to `lmsrPrice b q₂`. -/
theorem lmsrTraderPayoff_eq_msrStepPayoff [Nonempty Ω] {b : ℝ} (hb : 0 < b)
    (q₁ q₂ : Ω → ℝ) (ω : Ω) :
    lmsrTraderPayoff b q₁ q₂ ω =
      msrStepPayoff ((logScore Ω).affine b 0) (lmsrPrice b q₁) (lmsrPrice b q₂) ω := by
  simp only [lmsrTraderPayoff_apply, msrStepPayoff_apply, ScoringRule.affine_score,
    logScore_score, Pi.zero_apply, add_zero]
  linarith [sub_lmsrCost_eq_mul_log_lmsrPrice hb q₁ ω, sub_lmsrCost_eq_mul_log_lmsrPrice hb q₂ ω]

/-- **Sequential LMSR / MSR equivalence** [PennockSami2007, §26.4.1, pp. 663–664]: across any
finite sequence of share updates `qs 0, …, qs T`, cumulative cost-function trading payoffs equal
cumulative logarithmic MSR payoffs (and telescope to `lmsrTraderPayoff b (qs 0) (qs T) ω`). -/
theorem sum_lmsrTraderPayoff_eq_msrTotalPayoff [Nonempty Ω] {b : ℝ} (hb : 0 < b)
    (qs : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ range T, lmsrTraderPayoff b (qs t) (qs (t + 1)) ω =
      msrTotalPayoff ((logScore Ω).affine b 0) (fun t => lmsrPrice b (qs t)) T ω :=
  sum_congr rfl fun t _ => lmsrTraderPayoff_eq_msrStepPayoff hb (qs t) (qs (t + 1)) ω

/-- Path independence of LMSR trading: cumulative net payoff across any sequence `qs 0, …, qs T`
depends only on the endpoints `qs 0` and `qs T`. -/
theorem sum_lmsrTraderPayoff_eq_endpoints (b : ℝ) (qs : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ range T, lmsrTraderPayoff b (qs t) (qs (t + 1)) ω =
      lmsrTraderPayoff b (qs 0) (qs T) ω := by
  have hterm : ∀ t, lmsrTraderPayoff b (qs t) (qs (t + 1)) ω =
      (qs (t + 1) ω - lmsrCost b (qs (t + 1))) - (qs t ω - lmsrCost b (qs t)) := fun t => by
    simp only [lmsrTraderPayoff_apply]; ring
  simp only [hterm, sum_range_sub (fun t => qs t ω - lmsrCost b (qs t)) T, lmsrTraderPayoff_apply]
  ring

/-- **Realizability of any sequential MSR trajectory by LMSR cost-function trading**
[PennockSami2007, §26.4.1, pp. 663–664]: every sequence of strictly positive probability reports
`ps : ℕ → Ω → ℝ` is realized by an explicit sequence of LMSR share vectors with identical prices
and identical step-by-step payoffs. -/
theorem exists_shares_lmsrTraderPayoff_eq_msrStepPayoff [Nonempty Ω] {b : ℝ} (hb : 0 < b)
    {ps : ℕ → Ω → ℝ} (hps : ∀ t, ps t ∈ openProbSimplex Ω) :
    ∃ qs : ℕ → Ω → ℝ, (∀ t, lmsrPrice b (qs t) = ps t) ∧
      ∀ t ω, lmsrTraderPayoff b (qs t) (qs (t + 1)) ω =
        msrStepPayoff ((logScore Ω).affine b 0) (ps t) (ps (t + 1)) ω := by
  refine ⟨fun t ω => b * Real.log (ps t ω), fun t => lmsrPrice_log_eq hb (hps t), fun t ω => ?_⟩
  rw [lmsrTraderPayoff_eq_msrStepPayoff hb, lmsrPrice_log_eq hb (hps t),
    lmsrPrice_log_eq hb (hps (t + 1))]

/-! ### Bounded worst-case market-maker loss and tightness -/

/-- General worst-case LMSR market-maker loss bound from an arbitrary initial state `q₀`: for every
final share vector `q` and every outcome `ω`, the market maker's net loss is at most
`-b * log (lmsrPrice b q₀ ω)`. -/
theorem lmsrTraderPayoff_le_neg_mul_log_price [Nonempty Ω] {b : ℝ} (hb : 0 < b)
    (q₀ q : Ω → ℝ) (ω : Ω) :
    lmsrTraderPayoff b q₀ q ω ≤ -(b * Real.log (lmsrPrice b q₀ ω)) := by
  rw [lmsrTraderPayoff_eq_msrStepPayoff hb]
  simp only [msrStepPayoff_apply, ScoringRule.affine_score, logScore_score, Pi.zero_apply,
    add_zero]
  have hp_le : lmsrPrice b q ω ≤ 1 := by
    have h1 := single_le_sum (fun i _ => (lmsrPrice_pos b q i).le) (mem_univ ω)
    linarith [sum_lmsrPrice b q]
  have hlog_nonpos : Real.log (lmsrPrice b q ω) ≤ 0 :=
    Real.log_nonpos (lmsrPrice_pos b q ω).le hp_le
  nlinarith

/-- **Worst-case LMSR market-maker loss bound**
[PennockSami2007, §26.4.1, pp. 663–664; Hanson2007]: starting from zero initial shares (`q₀ = 0`,
uniform initial prices), for every final share vector `q` and every outcome `ω`, the market maker
loses at most `b * Real.log |Ω|`. -/
theorem lmsrTraderPayoff_zero_le [Nonempty Ω] {b : ℝ} (hb : 0 < b) (q : Ω → ℝ) (ω : Ω) :
    lmsrTraderPayoff b 0 q ω ≤ b * Real.log (Fintype.card Ω) := by
  have h := lmsrTraderPayoff_le_neg_mul_log_price hb 0 q ω
  rw [lmsrPrice_zero, Real.log_inv] at h
  linarith

/-- Sequential form of the worst-case LMSR loss bound: starting from `qs 0 = 0`, the cumulative
market-maker loss over any number `T` of trades and any outcome `ω` is at most
`b * Real.log |Ω|` [PennockSami2007, §26.4.1, pp. 663–664]. -/
theorem lmsrTraderPayoff_zero_seq_le [Nonempty Ω] {b : ℝ} (hb : 0 < b) {qs : ℕ → Ω → ℝ}
    (h0 : qs 0 = 0) (T : ℕ) (ω : Ω) :
    ∑ t ∈ range T, lmsrTraderPayoff b (qs t) (qs (t + 1)) ω ≤ b * Real.log (Fintype.card Ω) := by
  rw [sum_lmsrTraderPayoff_eq_endpoints, h0]
  exact lmsrTraderPayoff_zero_le hb (qs T) ω

/-- **Tightness of the `b * log |Ω|` worst-case loss bound**: for every outcome `ω` and every
`ε > 0`, there exists a share vector `q` causing market-maker loss strictly exceeding
`b * Real.log |Ω| - ε`. -/
theorem exists_lmsrTraderPayoff_zero_gt [Nonempty Ω] {b : ℝ} (hb : 0 < b)
    (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Ω → ℝ, b * Real.log (Fintype.card Ω) - ε < lmsrTraderPayoff b 0 q ω := by
  classical
  have hcard_pos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  by_cases h1 : Fintype.card Ω = 1
  · refine ⟨0, ?_⟩
    simp only [lmsrTraderPayoff_apply, Pi.zero_apply, sub_self, h1, Nat.cast_one, Real.log_one,
      mul_zero, zero_sub]
    linarith
  · have hcard_gt : (1 : ℝ) < Fintype.card Ω :=
      Nat.one_lt_cast.mpr (Nat.lt_of_le_of_ne Fintype.card_pos (Ne.symm h1))
    set δ : ℝ := 1 - Real.exp (-(ε / b)) with hδ_def
    have hδ_pos : 0 < δ :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hε hb)))
    set M : ℝ := (Fintype.card Ω : ℝ) / δ with hM_def
    have hM_pos : 0 < M := div_pos hcard_pos hδ_pos
    let q : Ω → ℝ := Pi.single ω (b * Real.log M)
    refine ⟨q, ?_⟩
    rw [lmsrTraderPayoff_eq_msrStepPayoff hb]
    simp only [msrStepPayoff_apply, ScoringRule.affine_score, logScore_score, Pi.zero_apply,
      add_zero, lmsrPrice_zero, Real.log_inv]
    have hω_term : Real.exp (q ω / b) = M := by
      simp only [q, Pi.single_eq_same, mul_div_cancel_left₀ _ hb.ne', Real.exp_log hM_pos]
    have hsum_q : ∑ i : Ω, Real.exp (q i / b) = M + ((Fintype.card Ω : ℝ) - 1) := by
      rw [← Finset.add_sum_erase univ _ (mem_univ ω), hω_term,
        sum_congr rfl (g := fun _ => (1 : ℝ)) fun i hi => by
          simp [q, Pi.single_eq_of_ne (mem_erase.mp hi).1],
        sum_const, card_erase_of_mem (mem_univ ω), card_univ, nsmul_eq_mul, mul_one,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    have hprice_gt : Real.exp (-(ε / b)) < lmsrPrice b q ω := by
      rw [lmsrPrice_apply, hω_term, hsum_q, lt_div_iff₀ (by linarith), mul_add]
      have hM_eq : Real.exp (-(ε / b)) * M + δ * M = M := by rw [hδ_def]; ring
      have hM_mul : δ * M = Fintype.card Ω := mul_div_cancel₀ _ hδ_pos.ne'
      linarith [mul_lt_of_lt_one_left (sub_pos.mpr hcard_gt) (sub_pos.mp hδ_pos)]
    have hlog_gt : -(ε / b) < Real.log (lmsrPrice b q ω) := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hprice_gt
    have hcancel : b * -(ε / b) = -ε := by rw [mul_neg, mul_div_cancel₀ _ hb.ne']
    linarith [mul_lt_mul_of_pos_left hlog_gt hb]

end LMSR

end Cslib.GameTheory.PredictionMarket
