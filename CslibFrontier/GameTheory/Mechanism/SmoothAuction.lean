/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FirstPrice
public import CslibFrontier.GameTheory.Strategic.SmoothHierarchy
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smooth mechanisms and the price of anarchy of first- and second-price auctions

Syrgkanis and Tardos [SyrgkanisTardos2013] adapted Roughgarden's smoothness framework
[Roughgarden2015] from cost-minimization games to sealed-bid quasilinear mechanisms. A
single-parameter mechanism `M` is **`(λ, μ)`-smooth** with respect to feasible allocations `X`
(`Mechanism.IsSmoothMechanism`) if for every nonnegative valuation profile `v` and benchmark
`x ∈ X`, each bidder `i` has a finitely supported deviation distribution `D i` over nonnegative bids
(depending only on `v` and `x`, never on `b`) such that against every nonnegative bid profile `b`,
`λ * socialWelfare v x - μ * ∑ i, M.payment b i` is at most
`∑ i, E_{z ∼ D i}[M.utility i (v i) (update b i z)]`.

Charging revenue `∑ i, M.payment b i` on the right-hand side rather than social welfare makes two
transfers immediate:

1. **Complete-information equilibria** (`IsSmoothMechanism.welfare_ge`,
   `welfare_ge_of_isCorrelated`, `welfare_ge_of_isPureNash`): when bidding `0` guarantees
   nonnegative utility (`HasZeroBidFloor`) and total payments are nonnegative (`0 ≤ μ`), every
   coarse correlated, correlated, or pure Nash equilibrium of `M.toCostGame v` (over nonnegative
   bids `ℝ≥0`) achieves expected welfare at least `λ / max 1 μ * socialWelfare v x`, with **no**
   no-overbidding assumption.
2. **Incomplete-information Bayes–Nash equilibria** (`integral_welfare_ge_of_isBayesNash`): for
   arbitrary independent valuation priors `Measure.pi ν` on `∏ i, [0, h i]`, every Bayes–Nash
   equilibrium (`Mechanism.IsBayesNash`) achieves expected social welfare at least
   `λ / max 1 μ * E_{v ∼ ν}[socialWelfare v (x v)]`.

We instantiate this framework on the two canonical single-item auctions:

* **First-price auction (`FirstPrice.mechanism`)**: via a uniform `K`-level geometric shading grid
  `z_k = v_i * (1 - exp (-k / K))`, `FirstPrice.mechanism` is
  `(exp (-1 / K) * (1 - exp (-1)), 1)`-smooth for every `K ≥ 1`
  (`FirstPrice.isSmoothMechanism_grid`, and `(1 / 2, 1)`-smooth at midpoint `v_i / 2`). Passing
  `K → ∞` via the Archimedean property establishes the unconditional **`1 - 1 / e` price of
  anarchy** across coarse correlated, correlated, pure Nash, and arbitrary independent-prior
  Bayes–Nash equilibria (`FirstPrice.welfare_ge_one_sub_exp_neg_one`,
  `FirstPrice.integral_welfare_ge_one_sub_exp_neg_one`).
* **Vickrey second-price auction (`Vickrey.mechanism`)**: truthful deviation gives
  `u_i(v_i, b_{-i}) ≥ v_i - highestOtherBid b i` (`Vickrey.utility_truthful_ge`), yielding the
  Christodoulou–Kovács–Schapira [ChristodoulouKovacsSchapira2008] **`1 / 2` price of anarchy under
  no-overbidding** for coarse correlated and Bayes–Nash equilibria
  (`Vickrey.welfare_ge_half_of_noOverbidding`,
  `Vickrey.integral_welfare_ge_half_of_isBayesNash_noOverbidding`), paired with a checked two-bidder
  overbidding pure Nash witness (`Vickrey.exists_overbidding_isPureNash_welfare_zero`) showing why
  the no-overbidding hypothesis is indispensable in second-price auctions.

## Main definitions

* `Cslib.GameTheory.SingleParameter.socialWelfare`,
  `Cslib.GameTheory.SingleParameter.Mechanism.welfare`: social welfare `∑ i, v i * x i`.
* `Cslib.GameTheory.SingleParameter.Mechanism.toCostGame`: complete-information strategic game of a
  sealed-bid mechanism over nonnegative bids `ℝ≥0`, with `cost i b = -M.utility i (v i) b`.
* `Cslib.GameTheory.SingleParameter.Mechanism.HasZeroBidFloor`: bidding `0` yields nonnegative
  allocation and nonpositive payment.
* `Cslib.GameTheory.SingleParameter.Mechanism.IsSmoothMechanism`: Syrgkanis–Tardos `(λ, μ)`-smooth
  mechanisms.

## Main results

* `Cslib.GameTheory.SingleParameter.Mechanism.IsSmoothMechanism.welfare_ge`,
  `Cslib.GameTheory.SingleParameter.Mechanism.IsSmoothMechanism.welfare_ge_of_isCorrelated`,
  `Cslib.GameTheory.SingleParameter.Mechanism.IsSmoothMechanism.welfare_ge_of_isPureNash`:
  `λ / max 1 μ` welfare guarantee across complete-information equilibria.
* `Cslib.GameTheory.SingleParameter.Mechanism.IsSmoothMechanism.integral_welfare_ge_of_isBayesNash`:
  `λ / max 1 μ` welfare guarantee for independent-prior Bayes–Nash equilibria.
* `Cslib.GameTheory.SingleParameter.FirstPrice.isSmoothMechanism_half`,
  `Cslib.GameTheory.SingleParameter.FirstPrice.isSmoothMechanism_grid`,
  `Cslib.GameTheory.SingleParameter.FirstPrice.welfare_ge_one_sub_exp_neg_one`,
  `Cslib.GameTheory.SingleParameter.FirstPrice.integral_welfare_ge_one_sub_exp_neg_one`:
  `(1 / 2, 1)` deterministic smoothness, `(exp (-1 / K) * (1 - exp (-1)), 1)` grid smoothness, and
  unconditional `1 - 1 / e` price of anarchy of the first-price auction.
* `Cslib.GameTheory.SingleParameter.Vickrey.utility_truthful_ge`,
  `Cslib.GameTheory.SingleParameter.Vickrey.welfare_ge_half_of_noOverbidding`,
  `Cslib.GameTheory.SingleParameter.Vickrey.integral_welfare_ge_half_of_isBayesNash_noOverbidding`,
  `Cslib.GameTheory.SingleParameter.Vickrey.exists_overbidding_isPureNash_welfare_zero`:
  `1 / 2` price of anarchy of the second-price auction under no-overbidding and zero-welfare
  overbidding pure Nash witness.

## References

* [ChristodoulouKovacsSchapira2008]
* [Roughgarden2015]
* [SyrgkanisTardos2013]
-/

open MeasureTheory Finset Function
open scoped NNReal

public section

namespace Cslib.GameTheory.SingleParameter

/-- Social welfare `∑ i, v i * x i` of allocation `x` under valuation profile `v`. -/
@[expose] def socialWelfare {ι : Type*} [Fintype ι] (v x : ι → ℝ) : ℝ :=
  ∑ i, v i * x i

namespace Mechanism

variable {ι : Type*}

/-- Realized social welfare `∑ i, v i * M.allocation b i` of mechanism `M` on bid profile `b`. -/
@[expose] def welfare [Fintype ι] (M : Mechanism ι) (v b : ι → ℝ) : ℝ :=
  socialWelfare v (M.allocation b)

/-- Quasilinear accounting identity: utilities plus payments equal realized social welfare. -/
theorem sum_utility_add_sum_payment [Fintype ι] (M : Mechanism ι) (v b : ι → ℝ) :
    (∑ i, M.utility i (v i) b) + ∑ i, M.payment b i = M.welfare v b := by
  simp only [utility, welfare, socialWelfare, sum_sub_distrib]
  ring

/-- Complete-information strategic game induced by a sealed-bid mechanism `M` at valuation profile
`v`: each bidder `i` submits a nonnegative bid `b i : ℝ≥0`, and minimizing cost `-M.utility` is
equivalent to maximizing quasilinear utility. -/
@[expose] def toCostGame (M : Mechanism ι) (v : ι → ℝ) : CostGame ι (fun _ => ℝ≥0) where
  cost i b := -M.utility i (v i) (fun j => (b j : ℝ))

/-- Bidding `0` guarantees nonnegative allocation and nonpositive payment against nonnegative
opponent bids, so every equilibrium type has a zero-bid outside option of utility at least `0`. -/
@[expose] def HasZeroBidFloor [DecidableEq ι] (M : Mechanism ι) : Prop :=
  ∀ i (b : ι → ℝ), 0 ≤ b →
    0 ≤ M.allocation (update b i 0) i ∧ M.payment (update b i 0) i ≤ 0

theorem HasZeroBidFloor.utility_zero_nonneg [DecidableEq ι] {M : Mechanism ι}
    (h0 : M.HasZeroBidFloor) {i : ι} {b : ι → ℝ} (hb : 0 ≤ b) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ M.utility i v (update b i 0) := by
  obtain ⟨hx, hp⟩ := h0 i b hb
  rw [utility]
  nlinarith

/-- **Syrgkanis–Tardos `(λ, μ)`-smooth mechanism** ([SyrgkanisTardos2013]): for every nonnegative
valuation profile `v` and feasible benchmark allocation `x ∈ X`, there exist finitely supported bid
distributions `D i` (independent of `b`) such that for every nonnegative bid profile `b`,
`λ * socialWelfare v x - μ * ∑ i, M.payment b i` is at most
`∑ i, E_{z ∼ D i}[M.utility i (v i) (update b i z)]`. -/
@[expose] def IsSmoothMechanism [Fintype ι] [DecidableEq ι] (M : Mechanism ι)
    (X : Set (ι → ℝ)) (lam μ : ℝ) : Prop :=
  ∀ (v : ι → ℝ), 0 ≤ v → ∀ x ∈ X, ∃ D : ι → Convexity.StdSimplex ℝ ℝ≥0,
    ∀ (b : ι → ℝ), 0 ≤ b →
      lam * socialWelfare v x - μ * ∑ i, M.payment b i ≤
        ∑ i, (D i).weights.sum fun z w =>
          w * M.utility i (v i) (update b i (z : ℝ))

section CompleteInfo

/-- Coercing `Function.update` on `ℝ≥0` bid profiles commutes with `(↑) : ℝ≥0 → ℝ`. -/
theorem coe_update_nnreal [DecidableEq ι] (b : ι → ℝ≥0) (i : ι) (z : ℝ≥0) :
    (fun j => ((update b i z j : ℝ≥0) : ℝ)) = update (fun j => (b j : ℝ)) i (z : ℝ) :=
  funext <| apply_update (fun _ => ((↑) : ℝ≥0 → ℝ)) b i z

theorem expected_utility_ge_of_cce [DecidableEq ι] {M : Mechanism ι}
    {v : ι → ℝ} {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (M.toCostGame v).IsCoarseCorrelatedEquilibrium σ) (i : ι) (z : ℝ≥0) :
    σ.weights.sum (fun b w => w * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) ≤
      σ.weights.sum (fun b w => w * M.utility i (v i) (fun j => (b j : ℝ))) := by
  have h := hσ i z
  simp only [toCostGame, mul_neg, Finsupp.sum] at h ⊢
  rw [sum_neg_distrib, sum_neg_distrib, neg_le_neg_iff] at h
  refine le_trans ?_ h
  exact le_of_eq (sum_congr rfl fun b _ => by rw [coe_update_nnreal])

private theorem div_max_one_mul_le {lam μ W U P E : ℝ} (hsm : lam * W - μ * P ≤ U)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hwel : E = U + P) : lam / max 1 μ * W ≤ E := by
  have hm1 : 1 ≤ max 1 μ := le_max_left 1 μ
  have hm2 : μ ≤ max 1 μ := le_max_right 1 μ
  have hm_pos : 0 < max 1 μ := lt_of_lt_of_le zero_lt_one hm1
  rw [div_mul_eq_mul_div, div_le_iff₀ hm_pos]
  nlinarith

variable [Fintype ι] [DecidableEq ι] {M : Mechanism ι}

/-- **Complete-information robust price of anarchy for smooth mechanisms** ([SyrgkanisTardos2013]):
if `M` is `(λ, μ)`-smooth, satisfies `HasZeroBidFloor`, and collects nonnegative total payments on
nonnegative bids, then every coarse correlated equilibrium `σ` of `M.toCostGame v` (`0 ≤ v`)
satisfies `λ / max 1 μ * socialWelfare v x ≤ E_{b ∼ σ}[M.welfare v b]` for all `x ∈ X`. -/
theorem IsSmoothMechanism.welfare_ge {X : Set (ι → ℝ)}
    {lam μ : ℝ} (hM : M.IsSmoothMechanism X lam μ) (h0 : M.HasZeroBidFloor)
    (hpay : ∀ b : ι → ℝ, 0 ≤ b → 0 ≤ ∑ i, M.payment b i) {v : ι → ℝ} (hv : 0 ≤ v)
    {x : ι → ℝ} (hx : x ∈ X) {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (M.toCostGame v).IsCoarseCorrelatedEquilibrium σ) :
    lam / max 1 μ * socialWelfare v x ≤
      σ.weights.sum (fun b w => w * M.welfare v (fun j => (b j : ℝ))) := by
  obtain ⟨D, hD⟩ := hM v hv x hx
  have htot : ∑ b ∈ σ.weights.support, σ.weights b = 1 := σ.total
  have hir : ∀ i, 0 ≤ σ.weights.sum (fun b w => w * M.utility i (v i) (fun j => (b j : ℝ))) := by
    intro i
    refine le_trans ?_ (expected_utility_ge_of_cce hσ i 0)
    simp only [Finsupp.sum, NNReal.coe_zero]
    exact sum_nonneg fun b _ => mul_nonneg (Convexity.StdSimplex.weights_nonneg b)
      (h0.utility_zero_nonneg (fun j => (b j).coe_nonneg) (hv i))
  have hir_sum : 0 ≤ σ.weights.sum (fun b w =>
      w * ∑ i, M.utility i (v i) (fun j => (b j : ℝ))) := by
    simp only [Finsupp.sum, mul_sum]
    rw [sum_comm]
    exact sum_nonneg fun i _ => hir i
  have hpay_exp : 0 ≤ σ.weights.sum (fun b w => w * ∑ i, M.payment (fun j => (b j : ℝ)) i) := by
    simp only [Finsupp.sum]
    exact sum_nonneg fun b _ => mul_nonneg (Convexity.StdSimplex.weights_nonneg b)
      (hpay _ fun j => (b j).coe_nonneg)
  have hdev_le : ∀ i, σ.weights.sum (fun b w => w * (D i).weights.sum fun z wt =>
        wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) ≤
      σ.weights.sum (fun b w => w * M.utility i (v i) (fun j => (b j : ℝ))) := by
    intro i
    have htotD : ∑ z ∈ (D i).weights.support, (D i).weights z = 1 := (D i).total
    have hswap : σ.weights.sum (fun b w => w * (D i).weights.sum fun z wt =>
          wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) =
        (D i).weights.sum (fun z wt => wt * σ.weights.sum fun b w =>
          w * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) := by
      simp only [Finsupp.sum, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun z _ => sum_congr rfl fun b _ => by ring
    rw [hswap]
    calc (D i).weights.sum (fun z wt => wt * σ.weights.sum fun b w =>
            w * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ)))
        ≤ (D i).weights.sum (fun _ wt => wt * σ.weights.sum fun b w =>
            w * M.utility i (v i) (fun j => (b j : ℝ))) := by
          simp only [Finsupp.sum]
          exact sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (expected_utility_ge_of_cce hσ i z)
            (Convexity.StdSimplex.weights_nonneg z)
      _ = σ.weights.sum (fun b w => w * M.utility i (v i) (fun j => (b j : ℝ))) := by
          simp only [Finsupp.sum]
          rw [← sum_mul, htotD, one_mul]
  have hsm_exp : lam * socialWelfare v x -
        μ * σ.weights.sum (fun b w => w * ∑ i, M.payment (fun j => (b j : ℝ)) i) ≤
      σ.weights.sum (fun b w => w * ∑ i, M.utility i (v i) (fun j => (b j : ℝ))) := by
    have hpt : σ.weights.sum (fun b w =>
          w * (lam * socialWelfare v x - μ * ∑ i, M.payment (fun j => (b j : ℝ)) i)) ≤
        σ.weights.sum (fun b w => w * ∑ i, (D i).weights.sum fun z wt =>
          wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) := by
      simp only [Finsupp.sum]
      exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
        (hD _ fun j => (b j).coe_nonneg) (Convexity.StdSimplex.weights_nonneg b)
    have hL : σ.weights.sum (fun b w =>
          w * (lam * socialWelfare v x - μ * ∑ i, M.payment (fun j => (b j : ℝ)) i)) =
        lam * socialWelfare v x -
          μ * σ.weights.sum (fun b w => w * ∑ i, M.payment (fun j => (b j : ℝ)) i) := by
      simp only [Finsupp.sum]
      have hr : ∀ b ∈ σ.weights.support,
          σ.weights b * (lam * socialWelfare v x - μ * ∑ i, M.payment (fun j => (b j : ℝ)) i) =
            lam * socialWelfare v x * σ.weights b -
              μ * (σ.weights b * ∑ i, M.payment (fun j => (b j : ℝ)) i) := fun _ _ => by ring
      rw [sum_congr rfl hr, sum_sub_distrib, ← mul_sum, ← mul_sum, htot, mul_one]
    have hR : σ.weights.sum (fun b w => w * ∑ i, (D i).weights.sum fun z wt =>
          wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) ≤
        σ.weights.sum (fun b w => w * ∑ i, M.utility i (v i) (fun j => (b j : ℝ))) := by
      have hcommL : σ.weights.sum (fun b w => w * ∑ i, (D i).weights.sum fun z wt =>
            wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) =
          ∑ i, σ.weights.sum (fun b w => w * (D i).weights.sum fun z wt =>
            wt * M.utility i (v i) (update (fun j => (b j : ℝ)) i (z : ℝ))) := by
        simp only [Finsupp.sum, mul_sum]
        exact sum_comm
      have hcommR : σ.weights.sum (fun b w => w * ∑ i, M.utility i (v i) (fun j => (b j : ℝ))) =
          ∑ i, σ.weights.sum (fun b w => w * M.utility i (v i) (fun j => (b j : ℝ))) := by
        simp only [Finsupp.sum, mul_sum]
        exact sum_comm
      rw [hcommL, hcommR]
      exact sum_le_sum fun i _ => hdev_le i
    linarith
  have hwel : σ.weights.sum (fun b w => w * M.welfare v (fun j => (b j : ℝ))) =
      σ.weights.sum (fun b w => w * ∑ i, M.utility i (v i) (fun j => (b j : ℝ))) +
        σ.weights.sum (fun b w => w * ∑ i, M.payment (fun j => (b j : ℝ)) i) := by
    simp only [Finsupp.sum, ← M.sum_utility_add_sum_payment v, mul_add, sum_add_distrib]
  exact div_max_one_mul_le hsm_exp hir_sum hpay_exp hwel

/-- Correlated-equilibrium welfare bound for `(λ, μ)`-smooth mechanisms. -/
theorem IsSmoothMechanism.welfare_ge_of_isCorrelated {X : Set (ι → ℝ)}
    {lam μ : ℝ} (hM : M.IsSmoothMechanism X lam μ) (h0 : M.HasZeroBidFloor)
    (hpay : ∀ b : ι → ℝ, 0 ≤ b → 0 ≤ ∑ i, M.payment b i) {v : ι → ℝ} (hv : 0 ≤ v)
    {x : ι → ℝ} (hx : x ∈ X) {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (M.toCostGame v).IsCorrelatedEquilibrium σ) :
    lam / max 1 μ * socialWelfare v x ≤
      σ.weights.sum (fun b w => w * M.welfare v (fun j => (b j : ℝ))) :=
  hM.welfare_ge h0 hpay hv hx hσ.isCoarseCorrelatedEquilibrium

/-- Pure Nash welfare bound for `(λ, μ)`-smooth mechanisms. -/
theorem IsSmoothMechanism.welfare_ge_of_isPureNash {X : Set (ι → ℝ)}
    {lam μ : ℝ} (hM : M.IsSmoothMechanism X lam μ) (h0 : M.HasZeroBidFloor)
    (hpay : ∀ b : ι → ℝ, 0 ≤ b → 0 ≤ ∑ i, M.payment b i) {v : ι → ℝ} (hv : 0 ≤ v)
    {x : ι → ℝ} (hx : x ∈ X) {b : ι → ℝ≥0} (hb : (M.toCostGame v).IsPureNash b) :
    lam / max 1 μ * socialWelfare v x ≤ M.welfare v (fun j => (b j : ℝ)) := by
  have h := hM.welfare_ge h0 hpay hv hx hb.isCoarseCorrelatedEquilibrium
  simpa only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul,
    one_mul] using h

end CompleteInfo

section Bayesian

variable [Fintype ι] [DecidableEq ι] {M : Mechanism ι}

private theorem integral_utility_update_eq (M : Mechanism ι) {ν : ι → Measure ℝ} {β : ι → ℝ → ℝ}
    {i : ι} {z : ℝ}
    (ha : Integrable (fun w => M.allocation (update (fun j => β j (w j)) i z) i) (Measure.pi ν))
    (hp : Integrable (fun w => M.payment (update (fun j => β j (w j)) i z) i) (Measure.pi ν))
    (c : ℝ) :
    (∫ w, M.utility i c (update (fun j => β j (w j)) i z) ∂Measure.pi ν) =
      c * M.interimAllocation ν β i z - M.interimPayment ν β i z := by
  simp only [utility, interimAllocation, interimPayment]
  rw [integral_sub (ha.const_mul c) hp, integral_const_mul]

private noncomputable def interimSliceUtil (M : Mechanism ι) (ν : ι → Measure ℝ) (β : ι → ℝ → ℝ)
    (i : ι) (t : ℝ) : ℝ :=
  ∫ w, M.utility i (update w i t i) (fun j => β j (update w i t j)) ∂Measure.pi ν

private theorem interimSliceUtil_integrable (M : Mechanism ι) {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {β : ι → ℝ → ℝ} {i : ι}
    (hu : Integrable (fun v => M.utility i (v i) (fun j => β j (v j))) (Measure.pi ν)) :
    Integrable (M.interimSliceUtil ν β i) (ν i) :=
  ((measurePreserving_update ν i).integrable_comp_of_integrable hu).integral_prod_right

private theorem interimSliceUtil_comp_integrable (M : Mechanism ι) {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {β : ι → ℝ → ℝ} {i : ι}
    (hu : Integrable (fun v => M.utility i (v i) (fun j => β j (v j))) (Measure.pi ν)) :
    Integrable (fun v : ι → ℝ => M.interimSliceUtil ν β i (v i)) (Measure.pi ν) :=
  integrable_comp_eval (M.interimSliceUtil_integrable hu)

private theorem integral_interimSliceUtil_eq (M : Mechanism ι) {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {β : ι → ℝ → ℝ} {i : ι}
    (hu : Integrable (fun v => M.utility i (v i) (fun j => β j (v j))) (Measure.pi ν)) :
    (∫ v, M.interimSliceUtil ν β i (v i) ∂Measure.pi ν) =
      ∫ v, M.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν := by
  rw [integral_apply_eval_eq_integral_integral ν (Φ := fun _ t => M.interimSliceUtil ν β i t)
      (fun _ _ => rfl) (M.interimSliceUtil_comp_integrable hu),
    integral_const, probReal_univ, one_smul]
  exact integral_integral_update_swap ν hu i

private theorem interimSliceUtil_eq_interim (M : Mechanism ι) {ν : ι → Measure ℝ} {β : ι → ℝ → ℝ}
    {i : ι} {t : ℝ}
    (ha : Integrable (fun w => M.allocation (update (fun j => β j (w j)) i (β i t)) i)
      (Measure.pi ν))
    (hp : Integrable (fun w => M.payment (update (fun j => β j (w j)) i (β i t)) i)
      (Measure.pi ν)) :
    M.interimSliceUtil ν β i t =
      t * M.interimAllocation ν β i (β i t) - M.interimPayment ν β i (β i t) := by
  have hupd : ∀ w : ι → ℝ,
      M.utility i (update w i t i) (fun j => β j (update w i t j)) =
        M.utility i t (update (fun j => β j (w j)) i (β i t)) := by
    intro w
    rw [update_self]
    congr 1
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [update_self, update_self]
    · rw [update_of_ne hj, update_of_ne hj]
  simp only [interimSliceUtil, hupd]
  exact M.integral_utility_update_eq ha hp t

omit [DecidableEq ι] in
private theorem integral_welfare_eq_add_payment (M : Mechanism ι) {ν : ι → Measure ℝ}
    {β : ι → ℝ → ℝ}
    (hu : ∀ i, Integrable (fun v => M.utility i (v i) (fun j => β j (v j))) (Measure.pi ν))
    (hp : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi ν)) :
    (∫ v, M.welfare v (fun j => β j (v j)) ∂Measure.pi ν) =
      (∫ v, ∑ i, M.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν) +
        ∫ v, ∑ i, M.payment (fun j => β j (v j)) i ∂Measure.pi ν := by
  have hpt : (fun v => M.welfare v (fun j => β j (v j))) =
      fun v => (∑ i, M.utility i (v i) (fun j => β j (v j))) +
        ∑ i, M.payment (fun j => β j (v j)) i := by
    funext v
    exact (M.sum_utility_add_sum_payment v _).symm
  rw [hpt, integral_add (integrable_finsetSum _ fun i _ => hu i)
    (integrable_finsetSum _ fun i _ => hp i)]

/-- **Bayesian price of anarchy for smooth mechanisms** ([SyrgkanisTardos2013]): if `M` is
`(λ, μ)`-smooth, satisfies `HasZeroBidFloor`, and collects nonnegative total payments on
nonnegative bids, then for any independent probability measures `ν i` supported on `[0, h i]` and
any Bayes–Nash equilibrium `β` (`M.IsBayesNash ν h β`), every integrable benchmark allocation rule
`x : (ι → ℝ) → ι → ℝ` with `x v ∈ X` on `∏ i, [0, h i]` achieves expected equilibrium welfare at
least `λ / max 1 μ * ∫ v, socialWelfare v (x v) ∂Measure.pi ν`. -/
theorem IsSmoothMechanism.integral_welfare_ge_of_isBayesNash {X : Set (ι → ℝ)} {lam μ : ℝ}
    (hM : M.IsSmoothMechanism X lam μ) (h0 : M.HasZeroBidFloor)
    (hpay : ∀ b : ι → ℝ, 0 ≤ b → 0 ≤ ∑ i, M.payment b i)
    {ν : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (ν i)] {h : ι → ℝ}
    (hsupp : ∀ i, ∀ᵐ t ∂ν i, t ∈ Set.Icc 0 (h i))
    {β : ι → ℝ → ℝ} (hβ : M.IsBayesNash ν h β)
    (halloc_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => M.allocation (update (fun j => β j (w j)) i z) i) (Measure.pi ν))
    (hpay_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => M.payment (update (fun j => β j (w j)) i z) i) (Measure.pi ν))
    (hutil_eq : ∀ i, Integrable (fun v => M.utility i (v i) (fun j => β j (v j))) (Measure.pi ν))
    (hpay_eq : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi ν))
    {x : (ι → ℝ) → ι → ℝ} (hx_mem : ∀ v, (∀ i, v i ∈ Set.Icc 0 (h i)) → x v ∈ X)
    (hx_int : Integrable (fun v => socialWelfare v (x v)) (Measure.pi ν)) :
    lam / max 1 μ * ∫ v, socialWelfare v (x v) ∂Measure.pi ν ≤
      ∫ v, M.welfare v (fun j => β j (v j)) ∂Measure.pi ν := by
  have hbox : ∀ᵐ v ∂Measure.pi ν, ∀ i, v i ∈ Set.Icc 0 (h i) := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hsupp i)
  have hdev_int : ∀ i (z : ℝ), 0 ≤ z → ∀ c : ℝ,
      Integrable (fun w => M.utility i c (update (fun j => β j (w j)) i z)) (Measure.pi ν) :=
    fun i z hz c => ((halloc_dev i z hz).const_mul c).sub (hpay_dev i z hz)
  have hslice_eq : ∀ i {t : ℝ}, t ∈ Set.Icc 0 (h i) →
      M.interimSliceUtil ν β i t =
        t * M.interimAllocation ν β i (β i t) - M.interimPayment ν β i (β i t) :=
    fun i _ ht => M.interimSliceUtil_eq_interim (halloc_dev i _ (hβ.nonneg ht))
      (hpay_dev i _ (hβ.nonneg ht))
  have hir : ∀ i, 0 ≤ ∫ v, M.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν := by
    intro i
    rw [← M.integral_interimSliceUtil_eq (hutil_eq i)]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hbox] with v hv
    dsimp only [Pi.zero_apply]
    rw [hslice_eq i (hv i)]
    have hbn := (hβ i (v i) (hv i)).2 0 le_rfl
    have h0_eq := (M.integral_utility_update_eq (halloc_dev i 0 le_rfl)
      (hpay_dev i 0 le_rfl) (v i)).symm
    have h0_nonneg : 0 ≤ ∫ w, M.utility i (v i) (update (fun j => β j (w j)) i 0)
        ∂Measure.pi ν := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hbox] with w hw
      dsimp only [Pi.zero_apply]
      exact h0.utility_zero_nonneg (fun j => hβ.nonneg (hw j)) (hv i).1
    linarith
  have hpay_sum_int : Integrable (fun w => ∑ i, M.payment (fun j => β j (w j)) i) (Measure.pi ν) :=
    integrable_finsetSum _ fun i _ => hpay_eq i
  have hpay_nonneg : 0 ≤ ∫ w, ∑ i, M.payment (fun j => β j (w j)) i ∂Measure.pi ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hbox] with w hw
    dsimp only [Pi.zero_apply]
    exact hpay _ fun j => hβ.nonneg (hw j)
  set P := ∫ w, ∑ i, M.payment (fun j => β j (w j)) i ∂Measure.pi ν
  have hpt : ∀ᵐ v ∂Measure.pi ν,
      lam * socialWelfare v (x v) - μ * P ≤ ∑ i, M.interimSliceUtil ν β i (v i) := by
    filter_upwards [hbox] with v hv
    obtain ⟨D, hD⟩ := hM v (fun i => (hv i).1) (x v) (hx_mem v hv)
    have hL_int : Integrable
        (fun w => lam * socialWelfare v (x v) - μ * ∑ i, M.payment (fun j => β j (w j)) i)
        (Measure.pi ν) :=
      (integrable_const _).sub (hpay_sum_int.const_mul μ)
    have hR_int_i : ∀ i, Integrable (fun w => (D i).weights.sum fun z wt =>
        wt * M.utility i (v i) (update (fun j => β j (w j)) i (z : ℝ))) (Measure.pi ν) := by
      intro i
      simp only [Finsupp.sum]
      exact integrable_finsetSum _ fun z _ => (hdev_int i (z : ℝ) z.coe_nonneg (v i)).const_mul _
    have hR_int : Integrable (fun w => ∑ i, (D i).weights.sum fun z wt =>
        wt * M.utility i (v i) (update (fun j => β j (w j)) i (z : ℝ))) (Measure.pi ν) :=
      integrable_finsetSum _ fun i _ => hR_int_i i
    have hae_w : ∀ᵐ w ∂Measure.pi ν,
        lam * socialWelfare v (x v) - μ * ∑ i, M.payment (fun j => β j (w j)) i ≤
          ∑ i, (D i).weights.sum fun z wt =>
            wt * M.utility i (v i) (update (fun j => β j (w j)) i (z : ℝ)) := by
      filter_upwards [hbox] with w hw
      exact hD _ fun j => hβ.nonneg (hw j)
    have hint_le := integral_mono_ae hL_int hR_int hae_w
    have hL_eval : (∫ w, (lam * socialWelfare v (x v) -
          μ * ∑ i, M.payment (fun j => β j (w j)) i) ∂Measure.pi ν) =
        lam * socialWelfare v (x v) - μ * P := by
      rw [integral_sub (integrable_const _) (hpay_sum_int.const_mul μ), integral_const,
        probReal_univ, one_smul, integral_const_mul]
    have hR_eval : (∫ w, (∑ i, (D i).weights.sum fun z wt =>
          wt * M.utility i (v i) (update (fun j => β j (w j)) i (z : ℝ))) ∂Measure.pi ν) ≤
        ∑ i, M.interimSliceUtil ν β i (v i) := by
      rw [integral_finsetSum _ fun i _ => hR_int_i i]
      refine sum_le_sum fun i _ => ?_
      rw [hslice_eq i (hv i)]
      simp only [Finsupp.sum]
      rw [integral_finsetSum (D i).weights.support fun (z : ℝ≥0) _ =>
        (hdev_int i (z : ℝ) z.coe_nonneg (v i)).const_mul _]
      calc ∑ z ∈ (D i).weights.support,
              ∫ w, (D i).weights z * M.utility i (v i) (update (fun j => β j (w j)) i (z : ℝ))
                ∂Measure.pi ν
          = ∑ z ∈ (D i).weights.support,
              (D i).weights z * (v i * M.interimAllocation ν β i (z : ℝ) -
                M.interimPayment ν β i (z : ℝ)) := by
            refine sum_congr rfl fun z _ => ?_
            rw [integral_const_mul,
              M.integral_utility_update_eq (halloc_dev i (z : ℝ) z.coe_nonneg)
                (hpay_dev i (z : ℝ) z.coe_nonneg) (v i)]
        _ ≤ ∑ z ∈ (D i).weights.support,
              (D i).weights z * (v i * M.interimAllocation ν β i (β i (v i)) -
                M.interimPayment ν β i (β i (v i))) :=
            sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
              ((hβ i (v i) (hv i)).2 (z : ℝ) z.coe_nonneg)
              (Convexity.StdSimplex.weights_nonneg z)
        _ = v i * M.interimAllocation ν β i (β i (v i)) -
              M.interimPayment ν β i (β i (v i)) := by
            have htotD : ∑ z ∈ (D i).weights.support, (D i).weights z = 1 := (D i).total
            rw [← sum_mul, htotD, one_mul]
    linarith
  have hmain := integral_mono_ae ((hx_int.const_mul lam).sub (integrable_const (μ * P)))
    (integrable_finsetSum _ fun i _ => M.interimSliceUtil_comp_integrable (hutil_eq i)) hpt
  dsimp only [Pi.sub_apply] at hmain
  rw [integral_sub (hx_int.const_mul lam) (integrable_const (μ * P)), integral_const_mul,
    integral_const, probReal_univ, one_smul,
    integral_finsetSum _ fun i _ => M.interimSliceUtil_comp_integrable (hutil_eq i)] at hmain
  have hsum_slice : (∑ i, ∫ v, M.interimSliceUtil ν β i (v i) ∂Measure.pi ν) =
      ∫ v, ∑ i, M.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν := by
    rw [integral_finsetSum _ fun i _ => hutil_eq i]
    exact sum_congr rfl fun i _ => M.integral_interimSliceUtil_eq (hutil_eq i)
  rw [hsum_slice] at hmain
  have hir_tot : 0 ≤ ∫ v, ∑ i, M.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν := by
    rw [integral_finsetSum _ fun i _ => hutil_eq i]
    exact sum_nonneg fun i _ => hir i
  exact div_max_one_mul_le hmain hir_tot hpay_nonneg
    (M.integral_welfare_eq_add_payment hutil_eq hpay_eq)

end Bayesian

end Mechanism

private theorem vickrey_allocation_nonneg {ι : Type*} [LinearOrder ι] (b : ι → ℝ) (i : ι) :
    0 ≤ Vickrey.allocation b i := by
  rcases Vickrey.allocation_binary b i with h0 | h1
  · rw [h0]
  · rw [h1]
    exact zero_le_one

/-! ### First-price auction: `(1 - 1 / e, 1)`-smoothness and unconditional PoA -/

namespace FirstPrice

section Smoothness

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

omit [Fintype ι] in
theorem hasZeroBidFloor : (FirstPrice.mechanism (ι := ι)).HasZeroBidFloor := by
  intro i b _
  refine ⟨?_, ?_⟩
  · rw [FirstPrice.mechanism_allocation]
    exact vickrey_allocation_nonneg (update b i 0) i
  · simp only [FirstPrice.mechanism, update_self, zero_mul, le_refl]

theorem sum_payment_nonneg {b : ι → ℝ} (hb : 0 ≤ b) :
    0 ≤ ∑ i, FirstPrice.mechanism.payment b i :=
  sum_nonneg fun i _ => mul_nonneg (hb i) (vickrey_allocation_nonneg b i)

private theorem sum_mul_allocation_eq_of_wins {b f : ι → ℝ} {w : ι} (hw : Vickrey.Wins b w) :
    ∑ j, f j * Vickrey.allocation b j = f w := by
  rw [sum_eq_single w
    (fun j _ hj => by
      rcases Vickrey.allocation_binary b j with h0 | h1
      · rw [h0, mul_zero]
      · exact absurd ((Vickrey.allocation_eq_one_iff.1 h1).unique hw) hj)
    (fun h => absurd (Finset.mem_univ w) h), Vickrey.allocation_eq_one_iff.2 hw, mul_one]

theorem highestOtherBid_le_sum_payment {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    Vickrey.highestOtherBid b i ≤ ∑ j, FirstPrice.mechanism.payment b j := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨w, hw⟩ := Vickrey.exists_wins b
  rw [show (∑ j, FirstPrice.mechanism.payment b j) = b w from sum_mul_allocation_eq_of_wins hw]
  refine Vickrey.highestOtherBid_le_iff.2 ⟨hb w, fun j _ => ?_⟩
  rcases eq_or_ne j w with rfl | hjw
  · exact le_rfl
  · exact (hw j hjw).1

omit [Fintype ι] in
theorem utility_nonneg_of_le (b : ι → ℝ) (i : ι) {v z : ℝ} (hzv : z ≤ v) :
    0 ≤ FirstPrice.mechanism.utility i v (update b i z) := by
  simp only [Mechanism.utility, FirstPrice.mechanism, update_self]
  rcases Vickrey.allocation_binary (update b i z) i with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    linarith

theorem utility_eq_sub_of_highestOtherBid_lt (b : ι → ℝ) (i : ι) (v : ℝ) {z : ℝ}
    (hlt : Vickrey.highestOtherBid b i < z) :
    FirstPrice.mechanism.utility i v (update b i z) = v - z := by
  have hw := Vickrey.wins_update_of_lt hlt
  simp only [Mechanism.utility, FirstPrice.mechanism, update_self,
    Vickrey.allocation_eq_one_iff.2 hw, mul_one]

private theorem finsupp_sum_finset_nonneg {K : ℕ} (s : Finset (Fin K)) (f : Fin K → ℝ≥0)
    (c : ℝ) (hc : 0 ≤ c) (z : ℝ≥0) :
    0 ≤ (∑ k ∈ s, Finsupp.single (f k) c) z := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · linarith
    · linarith

private theorem finsupp_sum_finset_linear {K : ℕ} (s : Finset (Fin K)) (f : Fin K → ℝ≥0)
    (c : ℝ) (g : ℝ≥0 → ℝ) :
    (∑ k ∈ s, Finsupp.single (f k) c).sum (fun z w => w * g z) =
      ∑ k ∈ s, c * g (f k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
      Finsupp.sum_single_index (zero_mul _), ih]

/-- Uniform finitely supported probability distribution over `K` points `f : Fin K → ℝ≥0`
(`1 ≤ K`), handling repeated values cleanly by summing `Finsupp.single` masses. -/
private noncomputable def uniformSimplex {K : ℕ} (hK : 1 ≤ K) (f : Fin K → ℝ≥0) :
    Convexity.StdSimplex ℝ ℝ≥0 where
  weights := ∑ k : Fin K, Finsupp.single (f k) (1 / (K : ℝ))
  nonneg z := finsupp_sum_finset_nonneg univ f (1 / (K : ℝ)) (by positivity) z
  total := by
    have hK0 : (K : ℝ) ≠ 0 := by
      have : 0 < K := by omega
      positivity
    have h := finsupp_sum_finset_linear univ f (1 / (K : ℝ)) (fun _ => 1)
    simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [h]
    field_simp

private theorem uniformSimplex_sum {K : ℕ} (hK : 1 ≤ K) (f : Fin K → ℝ≥0) (g : ℝ≥0 → ℝ) :
    (uniformSimplex hK f).weights.sum (fun z w => w * g z) =
      ∑ k : Fin K, 1 / (K : ℝ) * g (f k) :=
  finsupp_sum_finset_linear univ f (1 / (K : ℝ)) g

omit [LinearOrder ι] in
theorem singleItemFeasible_cases {x : ι → ℝ}
    (hx : x ∈ Vickrey.singleItemFeasible (ι := ι)) :
    (∀ i, x i = 0) ∨ ∃ i, x i = 1 ∧ ∀ j, j ≠ i → x j = 0 := by
  classical
  by_cases hall : ∀ i, x i = 0
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨i, hi0⟩ := hall
    have hi1 : x i = 1 := (hx.1 i).resolve_left hi0
    refine Or.inr ⟨i, hi1, fun j hj => ?_⟩
    by_contra hj0
    have hj1 : x j = 1 := (hx.1 j).resolve_left hj0
    have hge2 : (2 : ℝ) ≤ ∑ k, x k := by
      have hpair : ({i, j} : Finset ι) ⊆ univ := subset_univ _
      have hsum_pair : ∑ k ∈ ({i, j} : Finset ι), x k = 2 := by
        rw [sum_pair hj.symm, hi1, hj1]
        norm_num
      have hnonneg : ∀ k ∈ univ, k ∉ ({i, j} : Finset ι) → 0 ≤ x k := fun k _ _ => by
        rcases hx.1 k with h | h <;> rw [h]
        exact zero_le_one
      linarith [sum_le_sum_of_subset_of_nonneg hpair hnonneg]
    linarith [hx.2]

private theorem isSmoothMechanism_of_winner {lam : ℝ}
    (hwin_dev : ∀ (v : ι → ℝ), 0 ≤ v → ∀ i₀ : ι, ∃ D₀ : Convexity.StdSimplex ℝ ℝ≥0,
      ∀ b : ι → ℝ, 0 ≤ b →
        lam * v i₀ - ∑ j, FirstPrice.mechanism.payment b j ≤
          D₀.weights.sum (fun z w =>
            w * FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (z : ℝ)))) :
    (FirstPrice.mechanism (ι := ι)).IsSmoothMechanism Vickrey.singleItemFeasible lam 1 := by
  classical
  intro v hv x hx
  rcases singleItemFeasible_cases hx with hall0 | ⟨i₀, hi₀, hj0⟩
  · refine ⟨fun _ => Convexity.StdSimplex.single 0, fun b hb => ?_⟩
    have hsw : socialWelfare v x = 0 := sum_eq_zero fun i _ => by rw [hall0 i, mul_zero]
    have hp := sum_payment_nonneg hb
    have hu : 0 ≤ ∑ i, (Convexity.StdSimplex.single (0 : ℝ≥0)).weights.sum fun z w =>
        w * FirstPrice.mechanism.utility i (v i) (update b i (z : ℝ)) := by
      refine sum_nonneg fun i _ => ?_
      simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul,
        NNReal.coe_zero]
      exact utility_nonneg_of_le b i (hv i)
    rw [hsw, mul_zero, one_mul]
    linarith
  · obtain ⟨D₀, hD₀⟩ := hwin_dev v hv i₀
    let D : ι → Convexity.StdSimplex ℝ ℝ≥0 :=
      fun i => if i = i₀ then D₀ else Convexity.StdSimplex.single 0
    refine ⟨D, fun b hb => ?_⟩
    have hsw : socialWelfare v x = v i₀ := by
      rw [socialWelfare, sum_eq_single i₀
        (fun j _ hj => by rw [hj0 j hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i₀) h), hi₀, mul_one]
    rw [hsw, one_mul, ← add_sum_erase _ (fun i => (D i).weights.sum fun z w =>
      w * FirstPrice.mechanism.utility i (v i) (update b i (z : ℝ))) (Finset.mem_univ i₀)]
    have hhead : (D i₀).weights.sum
        (fun z w => w * FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (z : ℝ))) =
        D₀.weights.sum
          (fun z w => w * FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (z : ℝ))) := by
      simp only [D, ↓reduceIte]
    have htail : 0 ≤ ∑ j ∈ univ.erase i₀, (D j).weights.sum
        (fun z w => w * FirstPrice.mechanism.utility j (v j) (update b j (z : ℝ))) := by
      refine sum_nonneg fun j hj => ?_
      have hjne : j ≠ i₀ := ne_of_mem_erase hj
      simp only [D, hjne, ↓reduceIte, Convexity.StdSimplex.weights_single,
        Finsupp.sum_single_index, zero_mul, one_mul, NNReal.coe_zero]
      exact utility_nonneg_of_le b j (hv j)
    linarith [hD₀ b hb]

/-- **Deterministic `(1 / 2, 1)`-smoothness of the first-price auction**: shading by `1 / 2` on the
benchmark winner gives total deviation utility at least
`1 / 2 * socialWelfare v x - ∑ i, payment b i`. -/
theorem isSmoothMechanism_half :
    (FirstPrice.mechanism (ι := ι)).IsSmoothMechanism Vickrey.singleItemFeasible (1 / 2) 1 := by
  refine isSmoothMechanism_of_winner fun v hv i₀ => ?_
  let mid : ℝ≥0 := ⟨v i₀ / 2, div_nonneg (hv i₀) zero_le_two⟩
  refine ⟨Convexity.StdSimplex.single mid, fun b hb => ?_⟩
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul]
  change 1 / 2 * v i₀ - ∑ j, FirstPrice.mechanism.payment b j ≤
    FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (v i₀ / 2))
  have hB := highestOtherBid_le_sum_payment hb i₀
  by_cases hlt : Vickrey.highestOtherBid b i₀ < v i₀ / 2
  · have hwin := utility_eq_sub_of_highestOtherBid_lt b i₀ (v i₀) hlt
    have hp := sum_payment_nonneg hb
    linarith
  · push Not at hlt
    have hu0 : 0 ≤ FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (v i₀ / 2)) :=
      utility_nonneg_of_le b i₀ (div_le_self (hv i₀) one_le_two)
    linarith

/-- **Uniform `K`-grid `(exp (-1 / K) * (1 - exp (-1)), 1)`-smoothness of the first-price auction**
(finitely supported discretization of the geometric-shading distribution of
[SyrgkanisTardos2013]). -/
theorem isSmoothMechanism_grid {K : ℕ} (hK : 1 ≤ K) :
    (FirstPrice.mechanism (ι := ι)).IsSmoothMechanism Vickrey.singleItemFeasible
      (Real.exp (-1 / (K : ℝ)) * (1 - Real.exp (-1))) 1 := by
  set q : ℝ := Real.exp (-1 / (K : ℝ))
  have hK_pos : (0 : ℝ) < K := by
    have : 0 < K := by omega
    positivity
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt1 : q < 1 := Real.exp_lt_one_iff.2 (by
    rw [neg_div]
    exact neg_neg_of_pos (div_pos zero_lt_one hK_pos))
  have hq_pow_le1 : ∀ m : ℕ, q ^ m ≤ 1 := fun m => pow_le_one₀ hq_pos.le hq_lt1.le
  have hqK : q ^ K = Real.exp (-1) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have h1q_le : 1 - q ≤ 1 / (K : ℝ) := by
    have hexp := Real.add_one_le_exp (-(1 / (K : ℝ)))
    have hneg : -(1 / (K : ℝ)) = -1 / (K : ℝ) := by ring
    rw [hneg] at hexp
    dsimp [q]
    linarith
  refine isSmoothMechanism_of_winner fun v hv i₀ => ?_
  let grid (k : Fin K) : ℝ≥0 :=
    ⟨v i₀ * (1 - q ^ (k.val + 1)),
      mul_nonneg (hv i₀) (sub_nonneg.2 (hq_pow_le1 (k.val + 1)))⟩
  refine ⟨uniformSimplex hK grid, fun b hb => ?_⟩
  rw [uniformSimplex_sum]
  have hgrid_le : ∀ k : Fin K, (grid k : ℝ) ≤ v i₀ := fun k => by
    change v i₀ * (1 - q ^ (k.val + 1)) ≤ v i₀
    have : 0 ≤ v i₀ * q ^ (k.val + 1) := mul_nonneg (hv i₀) (pow_nonneg hq_pos.le _)
    linarith
  set B := Vickrey.highestOtherBid b i₀
  have hB_nonneg : 0 ≤ B := Vickrey.highestOtherBid_nonneg b i₀
  have hB_le_pay : B ≤ ∑ j, FirstPrice.mechanism.payment b j :=
    highestOtherBid_le_sum_payment hb i₀
  by_cases hhigh : v i₀ * (1 - q ^ K) ≤ B
  · rw [hqK] at hhigh
    have hterm_nonneg : 0 ≤ ∑ k : Fin K, 1 / (K : ℝ) *
        FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (grid k : ℝ)) :=
      sum_nonneg fun k _ => mul_nonneg (by positivity)
        (utility_nonneg_of_le b i₀ (hgrid_le k))
    have hexp_lt1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have hv1e : 0 ≤ v i₀ * (1 - Real.exp (-1)) := mul_nonneg (hv i₀) (by linarith)
    have hq_scale : q * (1 - Real.exp (-1)) * v i₀ ≤ v i₀ * (1 - Real.exp (-1)) := by
      nlinarith [hq_lt1.le]
    linarith
  · push Not at hhigh
    let S_win : Finset (Fin K) := univ.filter fun k => B < (grid k : ℝ)
    have hlast_mem : (⟨K - 1, by omega⟩ : Fin K) ∈ S_win := by
      simp only [S_win, mem_filter, Finset.mem_univ, true_and, grid]
      have hkK : K - 1 + 1 = K := by omega
      rwa [hkK]
    set k₀ : Fin K := S_win.min' ⟨_, hlast_mem⟩
    have hk₀_mem : k₀ ∈ S_win := Finset.min'_mem S_win _
    have hk₀_lt : B < v i₀ * (1 - q ^ (k₀.val + 1)) := (mem_filter.1 hk₀_mem).2
    have hk₀_prev : v i₀ * (1 - q ^ k₀.val) ≤ B := by
      rcases Nat.eq_zero_or_pos k₀.val with hk0 | hkpos
      · rw [hk0, pow_zero, sub_self, mul_zero]
        exact hB_nonneg
      · let prev : Fin K := ⟨k₀.val - 1, by omega⟩
        have hprev_lt : prev < k₀ := by
          change k₀.val - 1 < k₀.val
          omega
        have hnot_mem : prev ∉ S_win := fun hm =>
          hprev_lt.not_ge (Finset.min'_le S_win prev hm)
        simp only [S_win, mem_filter, Finset.mem_univ, true_and, not_lt, grid, prev] at hnot_mem
        have hsub : k₀.val - 1 + 1 = k₀.val := by omega
        rwa [hsub] at hnot_mem
    have hwin_ge : ∀ k : Fin K, k₀.val ≤ k.val →
        v i₀ * q ^ (k.val + 1) ≤
          FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (grid k : ℝ)) := by
      intro k hk
      have hpow_le : q ^ (k.val + 1) ≤ q ^ (k₀.val + 1) :=
        pow_le_pow_of_le_one hq_pos.le hq_lt1.le (by omega)
      have hBk : B < (grid k : ℝ) := by
        change B < v i₀ * (1 - q ^ (k.val + 1))
        have := mul_le_mul_of_nonneg_left hpow_le (hv i₀)
        linarith
      rw [utility_eq_sub_of_highestOtherBid_lt b i₀ (v i₀) hBk]
      change v i₀ * q ^ (k.val + 1) ≤ v i₀ - v i₀ * (1 - q ^ (k.val + 1))
      linarith
    have hsum_filter : ∑ k ∈ univ.filter (fun k : Fin K => k₀.val ≤ k.val),
          1 / (K : ℝ) * (v i₀ * q ^ (k.val + 1)) ≤
        ∑ k : Fin K, 1 / (K : ℝ) *
          FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (grid k : ℝ)) := by
      calc ∑ k ∈ univ.filter (fun k : Fin K => k₀.val ≤ k.val),
            1 / (K : ℝ) * (v i₀ * q ^ (k.val + 1))
          ≤ ∑ k ∈ univ.filter (fun k : Fin K => k₀.val ≤ k.val),
              1 / (K : ℝ) *
                FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (grid k : ℝ)) :=
            sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (hwin_ge k (mem_filter.1 hk).2) (by positivity)
        _ ≤ ∑ k : Fin K, 1 / (K : ℝ) *
              FirstPrice.mechanism.utility i₀ (v i₀) (update b i₀ (grid k : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
              mul_nonneg (by positivity) (utility_nonneg_of_le b i₀ (hgrid_le k))
    have hico_eq : ∑ k ∈ univ.filter (fun k : Fin K => k₀.val ≤ k.val),
          1 / (K : ℝ) * (v i₀ * q ^ (k.val + 1)) =
        ∑ m ∈ Ico k₀.val K, 1 / (K : ℝ) * (v i₀ * q ^ (m + 1)) := by
      refine sum_bij (fun k _ => k.val)
        (fun k hk => mem_Ico.2 ⟨(mem_filter.1 hk).2, k.isLt⟩)
        (fun _ _ _ _ h => Fin.ext h)
        (fun m hm =>
          ⟨⟨m, (mem_Ico.1 hm).2⟩, mem_filter.2 ⟨Finset.mem_univ _, (mem_Ico.1 hm).1⟩, rfl⟩)
        (fun _ _ => rfl)
    have htele : q * v i₀ * (q ^ k₀.val - q ^ K) ≤
        ∑ m ∈ Ico k₀.val K, 1 / (K : ℝ) * (v i₀ * q ^ (m + 1)) := by
      have hterm : ∀ m ∈ Ico k₀.val K,
          q * v i₀ * (q ^ m - q ^ (m + 1)) ≤ 1 / (K : ℝ) * (v i₀ * q ^ (m + 1)) := by
        intro m _
        have hvq : 0 ≤ v i₀ * q ^ (m + 1) := mul_nonneg (hv i₀) (pow_nonneg hq_pos.le _)
        have hmul := mul_le_mul_of_nonneg_right h1q_le hvq
        linarith [show q * v i₀ * (q ^ m - q ^ (m + 1)) = (1 - q) * (v i₀ * q ^ (m + 1)) by ring]
      have hsum_sub : ∑ m ∈ Ico k₀.val K, (q ^ m - q ^ (m + 1)) = q ^ k₀.val - q ^ K := by
        have hind : ∀ n, k₀.val ≤ n →
            ∑ m ∈ Ico k₀.val n, (q ^ m - q ^ (m + 1)) = q ^ k₀.val - q ^ n := by
          intro n hn
          induction hn with
          | refl => simp
          | @step m hkm ih =>
            rw [Finset.sum_Ico_succ_top hkm, ih, pow_succ]
            ring
        exact hind K k₀.isLt.le
      calc q * v i₀ * (q ^ k₀.val - q ^ K)
          = q * v i₀ * ∑ m ∈ Ico k₀.val K, (q ^ m - q ^ (m + 1)) := by rw [hsum_sub]
        _ = ∑ m ∈ Ico k₀.val K, q * v i₀ * (q ^ m - q ^ (m + 1)) := mul_sum _ _ _
        _ ≤ ∑ m ∈ Ico k₀.val K, 1 / (K : ℝ) * (v i₀ * q ^ (m + 1)) := sum_le_sum hterm
    rw [hqK] at htele
    have hlow : q * (1 - Real.exp (-1)) * v i₀ - ∑ j, FirstPrice.mechanism.payment b j ≤
        q * v i₀ * (q ^ k₀.val - Real.exp (-1)) := by
      have h1 : v i₀ - B ≤ v i₀ * q ^ k₀.val := by linarith
      have h2 : q * (v i₀ - B - v i₀ * Real.exp (-1)) ≤
          q * (v i₀ * q ^ k₀.val - v i₀ * Real.exp (-1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hq_pos.le
      have h3 : q * B ≤ B := by nlinarith [hq_lt1.le, hB_nonneg]
      linarith
    linarith

private theorem le_of_forall_exp_neg_inv_mul_le {A W : ℝ} (hW : 0 ≤ W)
    (hK : ∀ K : ℕ, 1 ≤ K → Real.exp (-1 / (K : ℝ)) * W ≤ A) : W ≤ A := by
  by_contra hlt
  push Not at hlt
  have hW_pos : 0 < W := by
    by_contra hW0
    have hW_eq : W = 0 := le_antisymm (not_lt.1 hW0) hW
    subst hW_eq
    have h1 := hK 1 le_rfl
    rw [mul_zero] at h1
    linarith
  obtain ⟨K, hK_gt⟩ := exists_nat_gt (W / (W - A))
  have hK1 : 1 ≤ K := by
    by_contra hK0
    have hKz : K = 0 := by omega
    subst hKz
    have hpos : 0 < W / (W - A) := div_pos hW_pos (by linarith)
    simp only [Nat.cast_zero] at hK_gt
    linarith
  have hK_pos : (0 : ℝ) < K := by positivity
  have hexp_ge : 1 - 1 / (K : ℝ) ≤ Real.exp (-1 / (K : ℝ)) := by
    have hexp := Real.add_one_le_exp (-(1 / (K : ℝ)))
    have hneg : -(1 / (K : ℝ)) = -1 / (K : ℝ) := by ring
    rw [hneg] at hexp
    linarith
  have hstep1 : (1 - 1 / (K : ℝ)) * W ≤ A :=
    (mul_le_mul_of_nonneg_right hexp_ge hW).trans (hK K hK1)
  have hstep2 : W - A ≤ W / (K : ℝ) := by
    linarith [show (1 - 1 / (K : ℝ)) * W = W - W / (K : ℝ) by ring]
  have hstep3 : (W - A) * (K : ℝ) ≤ W := (le_div_iff₀ hK_pos).1 hstep2
  have hstep4 : W < (K : ℝ) * (W - A) := (div_lt_iff₀ (by linarith)).1 hK_gt
  linarith

omit [LinearOrder ι] in
private theorem socialWelfare_nonneg_of_singleItemFeasible {v x : ι → ℝ} (hv : 0 ≤ v)
    (hx : x ∈ Vickrey.singleItemFeasible (ι := ι)) : 0 ≤ socialWelfare v x := by
  refine sum_nonneg fun i _ => mul_nonneg (hv i) ?_
  rcases hx.1 i with h0 | h1
  · rw [h0]
  · rw [h1]
    exact zero_le_one

/-- **Unconditional `1 - 1 / e` robust price of anarchy of the first-price auction**
([SyrgkanisTardos2013]): for every nonnegative valuation profile `v`, every feasible single-item
allocation `x ∈ singleItemFeasible`, and every coarse correlated equilibrium `σ` of
`mechanism.toCostGame v` (without any no-overbidding assumption),
`(1 - exp (-1)) * socialWelfare v x ≤ E_{b ∼ σ}[mechanism.welfare v b]`. -/
theorem welfare_ge_one_sub_exp_neg_one {v : ι → ℝ} (hv : 0 ≤ v)
    {x : ι → ℝ} (hx : x ∈ Vickrey.singleItemFeasible) {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (FirstPrice.mechanism.toCostGame v).IsCoarseCorrelatedEquilibrium σ) :
    (1 - Real.exp (-1)) * socialWelfare v x ≤
      σ.weights.sum (fun b w => w * FirstPrice.mechanism.welfare v (fun j => (b j : ℝ))) := by
  classical
  have hexp_lt1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hW_nonneg : 0 ≤ (1 - Real.exp (-1)) * socialWelfare v x :=
    mul_nonneg (by linarith) (socialWelfare_nonneg_of_singleItemFeasible hv hx)
  refine le_of_forall_exp_neg_inv_mul_le hW_nonneg fun K hK => ?_
  have hgrid := (isSmoothMechanism_grid (ι := ι) hK).welfare_ge
    hasZeroBidFloor (fun _ hb => sum_payment_nonneg hb) hv hx hσ
  rw [max_self, div_one, mul_assoc] at hgrid
  exact hgrid

/-- **Unconditional `1 - 1 / e` Bayesian price of anarchy of the first-price auction**
([SyrgkanisTardos2013]): for arbitrary independent valuation distributions `ν i` on `[0, h i]` and
any Bayes–Nash equilibrium `β` of `FirstPrice.mechanism`, expected equilibrium welfare is at least
`1 - exp (-1)` times the expected welfare of any integrable benchmark rule `x` valued in
`singleItemFeasible`. -/
theorem integral_welfare_ge_one_sub_exp_neg_one
    {ν : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (ν i)] {h : ι → ℝ}
    (hsupp : ∀ i, ∀ᵐ t ∂ν i, t ∈ Set.Icc 0 (h i))
    {β : ι → ℝ → ℝ} (hβ : FirstPrice.mechanism.IsBayesNash ν h β)
    (halloc_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => FirstPrice.mechanism.allocation (update (fun j => β j (w j)) i z) i)
        (Measure.pi ν))
    (hpay_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => FirstPrice.mechanism.payment (update (fun j => β j (w j)) i z) i)
        (Measure.pi ν))
    (hutil_eq : ∀ i,
      Integrable (fun v => FirstPrice.mechanism.utility i (v i) (fun j => β j (v j)))
        (Measure.pi ν))
    (hpay_eq : ∀ i,
      Integrable (fun v => FirstPrice.mechanism.payment (fun j => β j (v j)) i) (Measure.pi ν))
    {x : (ι → ℝ) → ι → ℝ}
    (hx_mem : ∀ v, (∀ i, v i ∈ Set.Icc 0 (h i)) → x v ∈ Vickrey.singleItemFeasible)
    (hx_int : Integrable (fun v => socialWelfare v (x v)) (Measure.pi ν)) :
    (1 - Real.exp (-1)) * ∫ v, socialWelfare v (x v) ∂Measure.pi ν ≤
      ∫ v, FirstPrice.mechanism.welfare v (fun j => β j (v j)) ∂Measure.pi ν := by
  classical
  have hexp_lt1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hbox : ∀ᵐ v ∂Measure.pi ν, ∀ i, v i ∈ Set.Icc 0 (h i) := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hsupp i)
  have hint_nonneg : 0 ≤ ∫ v, socialWelfare v (x v) ∂Measure.pi ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hbox] with v hv
    dsimp only [Pi.zero_apply]
    exact socialWelfare_nonneg_of_singleItemFeasible (fun i => (hv i).1) (hx_mem v hv)
  have hW_nonneg : 0 ≤ (1 - Real.exp (-1)) * ∫ v, socialWelfare v (x v) ∂Measure.pi ν :=
    mul_nonneg (by linarith) hint_nonneg
  refine le_of_forall_exp_neg_inv_mul_le hW_nonneg fun K hK => ?_
  have hgrid := (isSmoothMechanism_grid (ι := ι) hK).integral_welfare_ge_of_isBayesNash
    hasZeroBidFloor (fun _ hb => sum_payment_nonneg hb) hsupp hβ halloc_dev hpay_dev
    hutil_eq hpay_eq hx_mem hx_int
  rw [max_self, div_one, mul_assoc] at hgrid
  exact hgrid

end Smoothness

end FirstPrice

/-! ### Second-price (Vickrey) auction: `1 / 2` PoA under no-overbidding and necessity witness -/

namespace Vickrey

section Smoothness

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- **Truthful deviation lower bound in the second-price auction**: for every bidder `i`, valuation
`v`, and bid profile `b`, bidding `v` guarantees utility at least `v - highestOtherBid b i`. -/
theorem utility_truthful_ge (b : ι → ℝ) (i : ι) (v : ℝ) :
    v - highestOtherBid b i ≤ Vickrey.mechanism.utility i v (update b i v) := by
  by_cases hwin : Wins (update b i v) i
  · simp only [Mechanism.utility, Vickrey.mechanism, allocation_eq_one_iff.2 hwin, mul_one,
      highestOtherBid_update, le_refl]
  · have hob : v ≤ highestOtherBid b i := by
      by_contra hlt
      exact hwin (wins_update_of_lt (lt_of_not_ge hlt))
    simp only [Mechanism.utility, Vickrey.mechanism, allocation_eq_zero_iff.2 hwin, mul_zero,
      sub_self]
    linarith

private theorem highestOtherBid_le_welfare_of_noOverbidding {v b : ι → ℝ} (hv : 0 ≤ v)
    (hnob : ∀ j, b j ≤ v j) (i : ι) :
    highestOtherBid b i ≤ Vickrey.mechanism.welfare v b := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨w, hw⟩ := exists_wins b
  rw [show Vickrey.mechanism.welfare v b = v w from FirstPrice.sum_mul_allocation_eq_of_wins hw]
  refine highestOtherBid_le_iff.2 ⟨hv w, fun j _ => ?_⟩
  rcases eq_or_ne j w with rfl | hjw
  · exact hnob j
  · exact (hw j hjw).1.trans (hnob w)

private theorem sum_payment_nonneg_vickrey (b : ι → ℝ) :
    0 ≤ ∑ i, Vickrey.mechanism.payment b i :=
  sum_nonneg fun i _ => mul_nonneg (highestOtherBid_nonneg b i) (vickrey_allocation_nonneg b i)

/-- **`1 / 2` robust price of anarchy of the second-price auction under no-overbidding**
([ChristodoulouKovacsSchapira2008]): for every coarse correlated equilibrium `σ` of
`Vickrey.mechanism.toCostGame v` (`0 ≤ v`) supported on bid profiles satisfying `b j ≤ v j`,
`1 / 2 * socialWelfare v x ≤ E_{b ∼ σ}[mechanism.welfare v b]` for all `x ∈ singleItemFeasible`. -/
theorem welfare_ge_half_of_noOverbidding {v : ι → ℝ} (hv : 0 ≤ v) {x : ι → ℝ}
    (hx : x ∈ singleItemFeasible) {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (Vickrey.mechanism.toCostGame v).IsCoarseCorrelatedEquilibrium σ)
    (hnob : ∀ b ∈ σ.weights.support, ∀ j, (b j : ℝ) ≤ v j) :
    1 / 2 * socialWelfare v x ≤
      σ.weights.sum (fun b w => w * Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) := by
  classical
  rcases FirstPrice.singleItemFeasible_cases hx with hall0 | ⟨i₀, hi₀, hj0⟩
  · have hsw : socialWelfare v x = 0 := sum_eq_zero fun i _ => by rw [hall0 i, mul_zero]
    rw [hsw, mul_zero]
    simp only [Finsupp.sum]
    refine sum_nonneg fun b _ => mul_nonneg (Convexity.StdSimplex.weights_nonneg b) ?_
    exact sum_nonneg fun i _ => mul_nonneg (hv i) (vickrey_allocation_nonneg _ i)
  · have hsw : socialWelfare v x = v i₀ := by
      rw [socialWelfare, sum_eq_single i₀
        (fun j _ hj => by rw [hj0 j hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i₀) h), hi₀, mul_one]
    have htot : ∑ b ∈ σ.weights.support, σ.weights b = 1 := σ.total
    have hcce_i₀ : σ.weights.sum (fun b w =>
          w * Vickrey.mechanism.utility i₀ (v i₀)
            (update (fun j => (b j : ℝ)) i₀ (v i₀))) ≤
        σ.weights.sum (fun b w =>
          w * Vickrey.mechanism.utility i₀ (v i₀) (fun j => (b j : ℝ))) :=
      Mechanism.expected_utility_ge_of_cce hσ i₀ ⟨v i₀, hv i₀⟩
    have hlow : v i₀ -
          σ.weights.sum (fun b w => w * Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) ≤
        σ.weights.sum (fun b w =>
          w * Vickrey.mechanism.utility i₀ (v i₀) (fun j => (b j : ℝ))) := by
      have hpt : σ.weights.sum (fun b w =>
            w * (v i₀ - Vickrey.mechanism.welfare v (fun j => (b j : ℝ)))) ≤
          σ.weights.sum (fun b w =>
            w * Vickrey.mechanism.utility i₀ (v i₀)
              (update (fun j => (b j : ℝ)) i₀ (v i₀))) := by
        simp only [Finsupp.sum]
        refine sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_
          (Convexity.StdSimplex.weights_nonneg b)
        have h1 := utility_truthful_ge (fun j => (b j : ℝ)) i₀ (v i₀)
        have h2 := highestOtherBid_le_welfare_of_noOverbidding hv (hnob b hb) i₀
        linarith
      have hL : σ.weights.sum (fun b w =>
            w * (v i₀ - Vickrey.mechanism.welfare v (fun j => (b j : ℝ)))) =
          v i₀ -
            σ.weights.sum (fun b w => w * Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) := by
        simp only [Finsupp.sum]
        have hr : ∀ b ∈ σ.weights.support,
            σ.weights b * (v i₀ - Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) =
              v i₀ * σ.weights b -
                σ.weights b * Vickrey.mechanism.welfare v (fun j => (b j : ℝ)) :=
          fun _ _ => by ring
        rw [sum_congr rfl hr, sum_sub_distrib, ← mul_sum, htot, mul_one]
      linarith
    have hir_other : ∀ j, j ≠ i₀ →
        0 ≤ σ.weights.sum (fun b w =>
          w * Vickrey.mechanism.utility j (v j) (fun k => (b k : ℝ))) := by
      intro j _
      refine le_trans ?_ (Mechanism.expected_utility_ge_of_cce hσ j 0)
      simp only [Finsupp.sum, NNReal.coe_zero]
      refine sum_nonneg fun b _ => mul_nonneg (Convexity.StdSimplex.weights_nonneg b) ?_
      rw [Mechanism.utility, mechanism_isNormalized j _ (fun k => (b k).coe_nonneg), sub_zero]
      exact mul_nonneg (hv j) (vickrey_allocation_nonneg _ j)
    have hu_le_wel : σ.weights.sum (fun b w =>
          w * Vickrey.mechanism.utility i₀ (v i₀) (fun j => (b j : ℝ))) ≤
        σ.weights.sum (fun b w => w * Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) := by
      have hwel_eq : σ.weights.sum (fun b w =>
            w * Vickrey.mechanism.welfare v (fun j => (b j : ℝ))) =
          (∑ j, σ.weights.sum fun b w =>
            w * Vickrey.mechanism.utility j (v j) (fun k => (b k : ℝ))) +
            σ.weights.sum fun b w => w * ∑ j, Vickrey.mechanism.payment (fun k => (b k : ℝ)) j := by
        simp only [Finsupp.sum, ← Vickrey.mechanism.sum_utility_add_sum_payment v, mul_add,
          sum_add_distrib, mul_sum]
        rw [sum_comm]
      rw [hwel_eq, ← add_sum_erase _ _ (Finset.mem_univ i₀)]
      have hrest : 0 ≤ ∑ j ∈ univ.erase i₀, σ.weights.sum fun b w =>
          w * Vickrey.mechanism.utility j (v j) (fun k => (b k : ℝ)) :=
        sum_nonneg fun j hj => hir_other j (ne_of_mem_erase hj)
      have hpay0 : 0 ≤ σ.weights.sum fun b w =>
          w * ∑ j, Vickrey.mechanism.payment (fun k => (b k : ℝ)) j := by
        simp only [Finsupp.sum]
        exact sum_nonneg fun b _ => mul_nonneg (Convexity.StdSimplex.weights_nonneg b)
          (sum_payment_nonneg_vickrey _)
      linarith
    rw [hsw]
    linarith

/-- **`1 / 2` Bayesian price of anarchy of the second-price auction under no-overbidding**
([ChristodoulouKovacsSchapira2008]): for independent valuation priors `ν i` on `[0, h i]` and any
Bayes–Nash equilibrium `β` satisfying `β i t ≤ t` on `[0, h i]`, expected equilibrium welfare is at
least `1 / 2` of any integrable `singleItemFeasible` benchmark. -/
theorem integral_welfare_ge_half_of_isBayesNash_noOverbidding
    {ν : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (ν i)] {h : ι → ℝ}
    (hsupp : ∀ i, ∀ᵐ t ∂ν i, t ∈ Set.Icc 0 (h i))
    {β : ι → ℝ → ℝ} (hβ : Vickrey.mechanism.IsBayesNash ν h β)
    (hnob : ∀ i, ∀ t ∈ Set.Icc 0 (h i), β i t ≤ t)
    (halloc_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => Vickrey.mechanism.allocation (update (fun j => β j (w j)) i z) i)
        (Measure.pi ν))
    (hpay_dev : ∀ i (z : ℝ), 0 ≤ z →
      Integrable (fun w => Vickrey.mechanism.payment (update (fun j => β j (w j)) i z) i)
        (Measure.pi ν))
    (hutil_eq : ∀ i,
      Integrable (fun v => Vickrey.mechanism.utility i (v i) (fun j => β j (v j)))
        (Measure.pi ν))
    (hpay_eq : ∀ i,
      Integrable (fun v => Vickrey.mechanism.payment (fun j => β j (v j)) i) (Measure.pi ν))
    {x : (ι → ℝ) → ι → ℝ}
    (hx_mem : ∀ v, (∀ i, v i ∈ Set.Icc 0 (h i)) → x v ∈ singleItemFeasible)
    (hx_int : Integrable (fun v => socialWelfare v (x v)) (Measure.pi ν)) :
    1 / 2 * ∫ v, socialWelfare v (x v) ∂Measure.pi ν ≤
      ∫ v, Vickrey.mechanism.welfare v (fun j => β j (v j)) ∂Measure.pi ν := by
  classical
  have hbox : ∀ᵐ v ∂Measure.pi ν, ∀ i, v i ∈ Set.Icc 0 (h i) := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hsupp i)
  have hwel_int :
      Integrable (fun w => Vickrey.mechanism.welfare w (fun j => β j (w j)))
        (Measure.pi ν) := by
    have hpt_w : (fun w => Vickrey.mechanism.welfare w (fun j => β j (w j))) =
        fun w => (∑ i, Vickrey.mechanism.utility i (w i) (fun j => β j (w j))) +
          ∑ i, Vickrey.mechanism.payment (fun j => β j (w j)) i := by
      funext w
      exact (Vickrey.mechanism.sum_utility_add_sum_payment w _).symm
    rw [hpt_w]
    exact (integrable_finsetSum _ fun i _ => hutil_eq i).add
      (integrable_finsetSum _ fun i _ => hpay_eq i)
  set W_eq := ∫ w, Vickrey.mechanism.welfare w (fun j => β j (w j)) ∂Measure.pi ν
  have hdev_int : ∀ i (z : ℝ), 0 ≤ z → ∀ c : ℝ,
      Integrable (fun w => Vickrey.mechanism.utility i c (update (fun j => β j (w j)) i z))
        (Measure.pi ν) :=
    fun i z hz c => ((halloc_dev i z hz).const_mul c).sub (hpay_dev i z hz)
  have hslice_eq : ∀ i {t : ℝ}, t ∈ Set.Icc 0 (h i) →
      Vickrey.mechanism.interimSliceUtil ν β i t =
        t * Vickrey.mechanism.interimAllocation ν β i (β i t) -
          Vickrey.mechanism.interimPayment ν β i (β i t) :=
    fun i _ ht => Vickrey.mechanism.interimSliceUtil_eq_interim (halloc_dev i _ (hβ.nonneg ht))
      (hpay_dev i _ (hβ.nonneg ht))
  have hslice_nonneg : ∀ i {t : ℝ}, t ∈ Set.Icc 0 (h i) →
      0 ≤ Vickrey.mechanism.interimSliceUtil ν β i t := by
    intro i t ht
    rw [hslice_eq i ht]
    have hbn := (hβ i t ht).2 0 le_rfl
    have h0_eq := (Vickrey.mechanism.integral_utility_update_eq (halloc_dev i 0 le_rfl)
      (hpay_dev i 0 le_rfl) t).symm
    have h0_nonneg : 0 ≤ ∫ w, Vickrey.mechanism.utility i t (update (fun j => β j (w j)) i 0)
        ∂Measure.pi ν := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hbox] with w hw
      dsimp only [Pi.zero_apply]
      rw [Mechanism.utility, mechanism_isNormalized i _ (fun j => hβ.nonneg (hw j)), sub_zero]
      exact mul_nonneg ht.1 (vickrey_allocation_nonneg _ i)
    linarith
  have hpt : ∀ᵐ v ∂Measure.pi ν,
      socialWelfare v (x v) - W_eq ≤ ∑ i, Vickrey.mechanism.interimSliceUtil ν β i (v i) := by
    filter_upwards [hbox] with v hv
    rcases FirstPrice.singleItemFeasible_cases (hx_mem v hv) with hall0 | ⟨i₀, hi₀, hj0⟩
    · have hsw : socialWelfare v (x v) = 0 := sum_eq_zero fun i _ => by rw [hall0 i, mul_zero]
      have hsum_nonneg : 0 ≤ ∑ i, Vickrey.mechanism.interimSliceUtil ν β i (v i) :=
        sum_nonneg fun i _ => hslice_nonneg i (hv i)
      have hwel_nonneg : 0 ≤ W_eq := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [hbox] with w hw
        dsimp only [Pi.zero_apply]
        exact sum_nonneg fun i _ => mul_nonneg (hw i).1 (vickrey_allocation_nonneg _ i)
      linarith
    · have hsw : socialWelfare v (x v) = v i₀ := by
        rw [socialWelfare, sum_eq_single i₀
          (fun j _ hj => by rw [hj0 j hj, mul_zero])
          (fun h => absurd (Finset.mem_univ i₀) h), hi₀, mul_one]
      have hae_w : ∀ᵐ w ∂Measure.pi ν,
          v i₀ - Vickrey.mechanism.welfare w (fun j => β j (w j)) ≤
            Vickrey.mechanism.utility i₀ (v i₀) (update (fun j => β j (w j)) i₀ (v i₀)) := by
        filter_upwards [hbox] with w hw
        have h1 := utility_truthful_ge (fun j => β j (w j)) i₀ (v i₀)
        have h2 := highestOtherBid_le_welfare_of_noOverbidding (fun j => (hw j).1)
          (fun j => hnob j (w j) (hw j)) i₀
        linarith
      have hint_w := integral_mono_ae ((integrable_const (v i₀)).sub hwel_int)
        (hdev_int i₀ (v i₀) (hv i₀).1 (v i₀)) hae_w
      dsimp only [Pi.sub_apply] at hint_w
      rw [integral_sub (integrable_const _) hwel_int, integral_const, probReal_univ, one_smul,
        Vickrey.mechanism.integral_utility_update_eq (halloc_dev i₀ (v i₀) (hv i₀).1)
          (hpay_dev i₀ (v i₀) (hv i₀).1) (v i₀)] at hint_w
      have hbn := (hβ i₀ (v i₀) (hv i₀)).2 (v i₀) (hv i₀).1
      have hi₀_le : Vickrey.mechanism.interimSliceUtil ν β i₀ (v i₀) ≤
          ∑ i, Vickrey.mechanism.interimSliceUtil ν β i (v i) := by
        rw [← add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : 0 ≤ ∑ j ∈ univ.erase i₀, Vickrey.mechanism.interimSliceUtil ν β j (v j) :=
          sum_nonneg fun j _ => hslice_nonneg j (hv j)
        linarith
      have hslice_i₀ := hslice_eq i₀ (hv i₀)
      linarith
  have hmain := integral_mono_ae (hx_int.sub (integrable_const W_eq))
    (integrable_finsetSum _ fun i _ =>
      Vickrey.mechanism.interimSliceUtil_comp_integrable (hutil_eq i)) hpt
  dsimp only [Pi.sub_apply] at hmain
  rw [integral_sub hx_int (integrable_const W_eq), integral_const, probReal_univ, one_smul,
    integral_finsetSum _ fun i _ =>
      Vickrey.mechanism.interimSliceUtil_comp_integrable (hutil_eq i)] at hmain
  have hsum_slice : (∑ i, ∫ v, Vickrey.mechanism.interimSliceUtil ν β i (v i) ∂Measure.pi ν) =
      ∫ v, ∑ i, Vickrey.mechanism.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν := by
    rw [integral_finsetSum _ fun i _ => hutil_eq i]
    exact sum_congr rfl fun i _ => Vickrey.mechanism.integral_interimSliceUtil_eq (hutil_eq i)
  rw [hsum_slice] at hmain
  have hpay_nonneg :
      0 ≤ ∫ w, ∑ i, Vickrey.mechanism.payment (fun j => β j (w j)) i ∂Measure.pi ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hbox] with w _
    dsimp only [Pi.zero_apply]
    exact sum_payment_nonneg_vickrey _
  have hwel_decomp : W_eq =
      (∫ v, ∑ i, Vickrey.mechanism.utility i (v i) (fun j => β j (v j)) ∂Measure.pi ν) +
        ∫ w, ∑ i, Vickrey.mechanism.payment (fun j => β j (w j)) i ∂Measure.pi ν :=
    Vickrey.mechanism.integral_welfare_eq_add_payment hutil_eq hpay_eq
  linarith

/-- **Necessity of no-overbidding in the second-price auction**: with two bidders of valuations
`v 0 = 0` and `v 1 = 1`, the overbidding profile `b 0 = 2`, `b 1 = 0` is a pure Nash equilibrium of
`Vickrey.mechanism.toCostGame v` whose realized social welfare is `0` while optimal single-item
welfare is `1`. -/
theorem exists_overbidding_isPureNash_welfare_zero :
    ∃ (v : Fin 2 → ℝ) (b : Fin 2 → ℝ≥0) (x : Fin 2 → ℝ),
      0 ≤ v ∧ x ∈ singleItemFeasible ∧ socialWelfare v x = 1 ∧
        (Vickrey.mechanism.toCostGame v).IsPureNash b ∧
        Vickrey.mechanism.welfare v (fun j => (b j : ℝ)) = 0 := by
  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  let b : Fin 2 → ℝ≥0 := fun i => if i = 0 then 2 else 0
  let x : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  have hw0 : Wins (fun j : Fin 2 => (b j : ℝ)) 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simp [b]
  have hlose : allocation (fun j : Fin 2 => (b j : ℝ)) 1 = 0 := by
    rcases allocation_binary (fun j : Fin 2 => (b j : ℝ)) 1 with h0 | h1
    · exact h0
    · exact absurd ((allocation_eq_one_iff.1 h1).unique hw0) (by decide)
  refine ⟨v, b, x, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v]
  · refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [x]
    · simp [Fin.sum_univ_two, x]
  · simp [socialWelfare, Fin.sum_univ_two, v, x]
  · intro i z
    fin_cases i
    · have hob0 : highestOtherBid (fun j : Fin 2 => (b j : ℝ)) 0 = 0 := by
        refine le_antisymm ?_ (highestOtherBid_nonneg _ _)
        refine highestOtherBid_le_iff.2 ⟨le_rfl, fun j hj => ?_⟩
        fin_cases j
        · exact absurd rfl hj
        · simp [b]
      dsimp [Mechanism.toCostGame]
      rw [Mechanism.coe_update_nnreal b 0 z]
      simp only [Mechanism.utility, Vickrey.mechanism, v, Fin.isValue, ↓reduceIte,
        zero_mul, zero_sub, neg_neg, highestOtherBid_update, hob0]
      exact le_rfl
    · have hob1 : highestOtherBid (fun j : Fin 2 => (b j : ℝ)) 1 = 2 := by
        refine le_antisymm ?_ ?_
        · refine highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩
          fin_cases j
          · simp [b]
          · exact absurd rfl hj
        · have hle := le_highestOtherBid (b := fun j : Fin 2 => (b j : ℝ))
            (i := 1) (j := 0) (by decide)
          simpa [b] using hle
      dsimp [Mechanism.toCostGame]
      rw [Mechanism.coe_update_nnreal b 1 z]
      simp only [Mechanism.utility, Vickrey.mechanism, hlose, mul_zero, sub_self, neg_zero,
        v, Fin.isValue, one_ne_zero, ↓reduceIte, one_mul, highestOtherBid_update, hob1]
      rcases allocation_binary (update (fun j : Fin 2 => (b j : ℝ)) 1 (z : ℝ)) 1 with h0 | h1
      · rw [h0]
        norm_num
      · rw [h1]
        norm_num
  · rw [show Vickrey.mechanism.welfare v (fun j => (b j : ℝ)) = v 0 from
      FirstPrice.sum_mul_allocation_eq_of_wins hw0]
    rfl

end Smoothness

end Vickrey

end Cslib.GameTheory.SingleParameter
