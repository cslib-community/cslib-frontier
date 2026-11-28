/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.ResourceAllocation.NetworkUtilityMax
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests and concrete witnesses for NRTV §22.1 Network Utility Maximization and Wireless Max-Weight

Exercises `CslibFrontier.GameTheory.ResourceAllocation.NetworkUtilityMax` as an ordinary `module`
client without exposing internals:

1. **Multi-link wireline network (`R = Fin 2`, `L = Fin 2`, `route 0 = {0, 1}`, `route 1 = {1}`,
   `c = ![2, 4]`)**: non-diagonal full-row-rank routing matrix with strictly concave admissible
   piecewise quadratic-logarithmic utilities, witnessing KKT optimality (`IsKKT`), social
   optimality (`IsSocialOptimum`), price-taking decentralization (Eq. (22.7)), uniqueness of rates
   and Lagrange multipliers, weighted proportional fairness and myopic bid alignment
   (`w = ![4, 2]`, Eqs. (22.8)–(22.12), (22.15)), fixed-bid convergence (`tendsto_of_fixedBids`),
   and an explicit non-stationary dual congestion-control trajectory
   `p(t) = ![1 + e⁻ᵗ, 1 + 2 e⁻ᵗ]`, `x(t) = ![2 - e⁻ᵗ, 2 - e⁻ᵗ]` satisfying `IsDualPriceTrajectory`,
   Lyapunov monotonicity, and global convergence to `(x*, p*)`.
2. **Boundary `x_r = 0` KKT witness**: single-link 2-route network with linear utilities `2 x` and
   `x` where `x* = ![1, 0]`, `p* = ![2]` satisfies `IsKKT` with strict inequality
   `U'_1(0) = 1 < 2 = q*_1`, verifying boundary KKT handling.
3. **Interfering 2-link wireless network (`WirelessNetworkModel (Fin 2) (Fin 2) (Fin 2)`)**:
   mutually interfering links with schedules `M₀ = {0}`, `M₁ = {1}` and capacities `c = ![2, 4]`,
   witnessing the Max-Weight corner-point identity (Eq. (22.20)), joint rate-and-schedule KKT
   optimality at time-sharing `f* = ![1 / 2, 1 / 2]`, and an explicit non-stationary Max-Weight
   trajectory `p(t) = ![3 + e⁻ᵗ, 3 / 2 + (1 / 2) e⁻ᵗ]`, `x(t) = ![1 - e⁻ᵗ, 2 - (1 / 2) e⁻ᵗ]`
   satisfying `IsWirelessDualTrajectory`, Lyapunov drift/stability, and global convergence.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.NetworkUtilityMax

open Cslib.GameTheory Filter Set
open scoped Topology

/-! ### Smooth strictly concave admissible utility family -/

/-- Smooth strictly concave utility equal to `a x - (b / 2) x^2` on `[0, x₀]` and extended by
`(a x₀ - (b / 2) x₀^2) + (a - b x₀) x₀ log(x / x₀)` for `x > x₀`, with continuous strictly
decreasing positive derivative on `[0, ∞)` whenever `0 < b`, `0 < x₀`, and `0 < a - b x₀`. -/
private noncomputable def quadLog (a b x₀ x : ℝ) : ℝ :=
  if x ≤ x₀ then a * x - (b / 2) * x ^ 2
  else (a * x₀ - (b / 2) * x₀ ^ 2) + (a - b * x₀) * x₀ * Real.log (x / x₀)

private noncomputable def quadLogDeriv (a b x₀ x : ℝ) : ℝ :=
  if x ≤ x₀ then a - b * x else (a - b * x₀) * x₀ / x

private theorem hasDerivAt_quadLog {a b x₀ x : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (quadLog a b x₀) (quadLogDeriv a b x₀ x) x := by
  let leftFn : ℝ → ℝ := fun z => a * z - (b / 2) * z ^ 2
  let rightFn : ℝ → ℝ := fun z =>
    (a * x₀ - (b / 2) * x₀ ^ 2) + (a - b * x₀) * x₀ * Real.log (z / x₀)
  have hL : ∀ z, HasDerivAt leftFn (a - b * z) z := fun z => by
    have h1 := (hasDerivAt_id' z).const_mul a
    have h2 := ((hasDerivAt_id' z).pow 2).const_mul (b / 2)
    convert h1.sub h2 using 1
    ring
  have hR : ∀ z, 0 < z → HasDerivAt rightFn ((a - b * x₀) * x₀ / z) z := fun z hz => by
    have hdiv : HasDerivAt (fun w : ℝ => w / x₀) (1 / x₀) z := (hasDerivAt_id' z).div_const x₀
    have hlog : HasDerivAt (fun w : ℝ => Real.log (w / x₀)) ((1 / x₀) / (z / x₀)) z :=
      hdiv.log (div_pos hz hx₀).ne'
    have hmul := (hlog.const_mul ((a - b * x₀) * x₀)).const_add (a * x₀ - (b / 2) * x₀ ^ 2)
    convert hmul using 1
    field_simp [hz.ne', hx₀.ne']
  rcases lt_trichotomy x x₀ with hlt | hEq | hgt
  · have hEq' : quadLog a b x₀ =ᶠ[𝓝 x] leftFn := by
      filter_upwards [Iio_mem_nhds hlt] with z hz
      simp only [quadLog, leftFn, (mem_Iio.mp hz).le, ↓reduceIte]
    simpa only [quadLogDeriv, hlt.le, ↓reduceIte] using (hL x).congr_of_eventuallyEq hEq'
  · subst hEq
    have hleft_w : HasDerivWithinAt (quadLog a b x) (a - b * x) (Iic x) x := by
      have hEq' : EqOn (quadLog a b x) leftFn (Iic x) := fun z hz => by
        simp only [quadLog, leftFn, mem_Iic.mp hz, ↓reduceIte]
      exact ((hL x).hasDerivWithinAt (s := Iic x)).congr hEq' (hEq' le_rfl)
    have hright_w : HasDerivWithinAt (quadLog a b x) (a - b * x) (Ici x) x := by
      have hEq' : EqOn (quadLog a b x) rightFn (Ici x) := fun z hz => by
        rcases eq_or_lt_of_le (mem_Ici.mp hz) with rfl | hzgt
        · simp [quadLog, rightFn, div_self hx₀.ne']
        · simp [quadLog, rightFn, not_le.mpr hzgt]
      have hRx₀ : HasDerivAt rightFn (a - b * x) x := by
        simpa only [mul_div_cancel_right₀ _ hx₀.ne'] using hR x hx₀
      exact (hRx₀.hasDerivWithinAt (s := Ici x)).congr hEq' (hEq' le_rfl)
    have hunion : HasDerivWithinAt (quadLog a b x) (a - b * x) Set.univ x := by
      simpa only [Iic_union_Ici] using hleft_w.union hright_w
    simpa only [quadLogDeriv, le_rfl, ↓reduceIte] using hasDerivWithinAt_univ.mp hunion
  · have hEq' : quadLog a b x₀ =ᶠ[𝓝 x] rightFn := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      simp only [quadLog, rightFn, not_le.mpr (mem_Ioi.mp hz), ↓reduceIte]
    simpa only [quadLogDeriv, not_le.mpr hgt, ↓reduceIte] using
      (hR x (hx₀.trans hgt)).congr_of_eventuallyEq hEq'

private theorem derivWithin_quadLog {a b x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : 0 ≤ x) :
    derivWithin (quadLog a b x₀) (Ici 0) x = quadLogDeriv a b x₀ x :=
  (hasDerivAt_quadLog hx₀).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 x hx)

private theorem quadLog_admissible_and_strictConcave {a b x₀ : ℝ}
    (hb : 0 < b) (hx₀ : 0 < x₀) (hpos : 0 < a - b * x₀) :
    IsAdmissibleUtility (quadLog a b x₀) ∧ StrictConcaveOn ℝ (Ici 0) (quadLog a b x₀) := by
  have hdiff : DifferentiableOn ℝ (quadLog a b x₀) (Ici 0) :=
    fun _ _ => (hasDerivAt_quadLog hx₀).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn (quadLog a b x₀) (Ici 0) := hdiff.continuousOn
  have hderiv_pos : ∀ x ∈ interior (Ici (0 : ℝ)), 0 < deriv (quadLog a b x₀) x := by
    intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_quadLog hx₀).deriv]
    dsimp only [quadLogDeriv]
    split_ifs with hle
    · nlinarith
    · exact div_pos (mul_pos hpos hx₀) hx
  have hderiv_anti : StrictAntiOn (deriv (quadLog a b x₀)) (interior (Ici (0 : ℝ))) := by
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [(hasDerivAt_quadLog hx₀).deriv, (hasDerivAt_quadLog hx₀).deriv]
    dsimp only [quadLogDeriv]
    split_ifs with hyle hxle hxle
    · nlinarith
    · linarith [not_le.mp hxle]
    · have h1 : a - b * x₀ ≤ a - b * x := by nlinarith
      have h2 : (a - b * x₀) * x₀ / y < a - b * x₀ := by
        rw [div_lt_iff₀ hy]
        nlinarith [not_le.mp hyle]
      linarith
    · exact div_lt_div_of_pos_left (mul_pos hpos hx₀) hx hxy
  have hstrict : StrictConcaveOn ℝ (Ici 0) (quadLog a b x₀) :=
    hderiv_anti.strictConcaveOn_of_deriv (convex_Ici 0) hcont
  have hmono : StrictMonoOn (quadLog a b x₀) (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv_pos
  exact ⟨⟨hstrict.concaveOn, hmono, hdiff⟩, hstrict⟩

/-! ### 1. Multi-link wireline network witness (Eqs. (22.1)–(22.15)) -/

section WirelineNetwork

/-- Two-link, two-route wireline network with routing matrix `R = [[1, 0], [1, 1]]`,
capacities `c = ![2, 4]`, and smooth strictly concave utilities `quadLog 8 3 2` and
`quadLog 5 2 2`. -/
private noncomputable def wirelineNet : NetworkUtilityModel (Fin 2) (Fin 2) where
  route := fun r => if r = 0 then {0, 1} else {1}
  capacity := ![2, 4]
  utility := fun r => if r = 0 then quadLog 8 3 2 else quadLog 5 2 2

private theorem wirelineNet_injective_routePrice :
    Function.Injective wirelineNet.routePrice := by
  intro p₁ p₂ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [NetworkUtilityModel.routePrice, wirelineNet, ↓reduceIte, one_ne_zero,
    Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), Finset.sum_singleton] at h0 h1
  funext l
  rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
  · linarith
  · exact h1

private theorem wirelineNet_admissible_and_strict :
    (∀ r, IsAdmissibleUtility (wirelineNet.utility r)) ∧
      (∀ r, StrictConcaveOn ℝ (Ici 0) (wirelineNet.utility r)) := by
  have h0 := quadLog_admissible_and_strictConcave (a := 8) (b := 3) (x₀ := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 := quadLog_admissible_and_strictConcave (a := 5) (b := 2) (x₀ := 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨fun r => ?_, fun r => ?_⟩ <;>
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;>
    simp [wirelineNet, h0, h1]

private theorem wirelineNet_linkLoad_zero (x : Fin 2 → ℝ) :
    wirelineNet.linkLoad x 0 = x 0 := by
  have hflt : Finset.univ.filter (fun r : Fin 2 => (0 : Fin 2) ∈ wirelineNet.route r) = {0} := by
    decide
  simp [NetworkUtilityModel.linkLoad, hflt]

private theorem wirelineNet_linkLoad_one (x : Fin 2 → ℝ) :
    wirelineNet.linkLoad x 1 = x 0 + x 1 := by
  have hflt : Finset.univ.filter (fun r : Fin 2 => (1 : Fin 2) ∈ wirelineNet.route r) = {0, 1} := by
    decide
  simp [NetworkUtilityModel.linkLoad, hflt, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]

private theorem wirelineNet_routePrice_zero (p : Fin 2 → ℝ) :
    wirelineNet.routePrice p 0 = p 0 + p 1 := by
  simp [NetworkUtilityModel.routePrice, wirelineNet, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]

private theorem wirelineNet_routePrice_one (p : Fin 2 → ℝ) :
    wirelineNet.routePrice p 1 = p 1 := by
  simp [NetworkUtilityModel.routePrice, wirelineNet]

/-- KKT optimality, price-taking decentralization (Eq. (22.7)), uniqueness of optimal rates and
link prices, weighted proportional fairness alignment (`w = ![4, 2]`, Eqs. (22.8)–(22.12)),
myopic bid optimality, and fixed-bid dual convergence on `wirelineNet`. -/
example :
    let xStar : Fin 2 → ℝ := ![2, 2]
    let pStar : Fin 2 → ℝ := ![1, 1]
    let w : Fin 2 → ℝ := ![4, 2]
    wirelineNet.IsKKT xStar pStar ∧
    wirelineNet.IsSocialOptimum xStar ∧
    (∀ y, wirelineNet.IsSocialOptimum y → y = xStar) ∧
    (∀ p', wirelineNet.IsKKT xStar p' → p' = pStar) ∧
    wirelineNet.IsWeightedPropFair w xStar ∧
    wirelineNet.IsWeightedPropFairKKT w xStar pStar ∧
    (∀ t : ℝ, 0 ≤ t →
      wirelineNet.utility 0 (t / 2) - t ≤ wirelineNet.utility 0 (4 / 2) - 4) ∧
    (∀ x p, wirelineNet.IsDualPriceTrajectory x p →
      (∀ t ∈ Ici (0 : ℝ), ∀ r, 0 < wirelineNet.routePrice (p t) r) →
      (∀ t ∈ Ici (0 : ℝ), ∀ r, x t r = w r / wirelineNet.routePrice (p t) r) →
      Tendsto x atTop (𝓝 xStar) ∧ Tendsto p atTop (𝓝 pStar)) := by
  intro xStar pStar w
  obtain ⟨hU, hstrict⟩ := wirelineNet_admissible_and_strict
  have hderiv : ∀ r : Fin 2, derivWithin (wirelineNet.utility r) (Ici 0) (xStar r) =
      wirelineNet.routePrice pStar r := by
    intro r
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · rw [wirelineNet_routePrice_zero]
      change derivWithin (quadLog 8 3 2) (Ici 0) 2 = 1 + 1
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
    · rw [wirelineNet_routePrice_one]
      change derivWithin (quadLog 5 2 2) (Ici 0) 2 = 1
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
  have hkkt : wirelineNet.IsKKT xStar pStar := by
    refine ⟨⟨fun r => by rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [xStar],
      fun l => ?_⟩,
      fun l => by rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [pStar],
      fun l => ?_, fun r => (hderiv r).le, fun r _ => hderiv r⟩
    · rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · rw [wirelineNet_linkLoad_zero]; simp [xStar, wirelineNet]
      · rw [wirelineNet_linkLoad_one]; simp [xStar, wirelineNet]; norm_num
    · rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · rw [wirelineNet_linkLoad_zero]; simp [xStar, wirelineNet]
      · rw [wirelineNet_linkLoad_one]; simp [xStar, wirelineNet]; norm_num
  have hopt : wirelineNet.IsSocialOptimum xStar :=
    hkkt.isSocialOptimum (fun r => (hU r).concaveOn) (fun r => (hU r).differentiableOn)
  have hxpos : ∀ r : Fin 2, 0 < xStar r := fun r => by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [xStar]
  have hmyopic := hkkt.isWeightedPropFairKKT_of_myopicBids hxpos fun r =>
    (hU r).derivWithin_pos (hxpos r).le
  have hw_eq : (fun r => xStar r * derivWithin (wirelineNet.utility r) (Ici 0) (xStar r)) = w := by
    funext r
    rw [hderiv r]
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · rw [wirelineNet_routePrice_zero]; simp [xStar, pStar, w]; norm_num
    · rw [wirelineNet_routePrice_one]; simp [xStar, pStar, w]
  rw [hw_eq] at hmyopic
  have hbid0 : ∀ t : ℝ, 0 ≤ t →
      wirelineNet.utility 0 (t / 2) - t ≤ wirelineNet.utility 0 (4 / 2) - 4 :=
    (myopicBid_isMax_iff_derivWithin_eq (hU 0).concaveOn (hU 0).differentiableOn
      (by norm_num) (by norm_num)).mpr (by
        have h42 : (4 : ℝ) / 2 = xStar 0 := by simp [xStar]; norm_num
        rw [h42, hderiv 0, wirelineNet_routePrice_zero]
        simp [pStar]; norm_num)
  have hroute : ∀ r : Fin 2, (wirelineNet.route r).Nonempty := fun r => by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [wirelineNet]
  have hcap : ∀ l : Fin 2, 0 < wirelineNet.capacity l := fun l => by
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [wirelineNet]
  have hfixed : ∀ x p, wirelineNet.IsDualPriceTrajectory x p →
      (∀ t ∈ Ici (0 : ℝ), ∀ r, 0 < wirelineNet.routePrice (p t) r) →
      (∀ t ∈ Ici (0 : ℝ), ∀ r, x t r = w r / wirelineNet.routePrice (p t) r) →
      Tendsto x atTop (𝓝 xStar) ∧ Tendsto p atTop (𝓝 pStar) := fun x p htraj hqpos hctrl => by
    obtain ⟨_, hxlim, hplim⟩ :=
      htraj.tendsto_of_fixedBids hroute hcap hmyopic.1 hmyopic.2.1 hqpos hctrl
    exact ⟨hxlim, hplim wirelineNet_injective_routePrice⟩
  exact ⟨hkkt, hopt,
    fun y hy => hy.eq_of_strictConcaveOn hopt hstrict,
    fun p' hp' => hp'.price_eq_of_injective_routePrice hkkt hxpos wirelineNet_injective_routePrice,
    hmyopic.2.2, hmyopic.2.1, hbid0, hfixed⟩

/-- Explicit non-stationary dual congestion-control trajectory on `wirelineNet`:
`p(t) = ![1 + e⁻ᵗ, 1 + 2 e⁻ᵗ]`, `x(t) = ![2 - e⁻ᵗ, 2 - e⁻ᵗ]` satisfies `IsDualPriceTrajectory`,
Eq. (22.15), Lyapunov monotonicity, and global convergence `(x(t), q(t), p(t)) → (x*, q*, p*)`. -/
example :
    let xStar : Fin 2 → ℝ := ![2, 2]
    let pStar : Fin 2 → ℝ := ![1, 1]
    let p : ℝ → Fin 2 → ℝ := fun t => ![1 + Real.exp (-t), 1 + 2 * Real.exp (-t)]
    let x : ℝ → Fin 2 → ℝ := fun t => ![2 - Real.exp (-t), 2 - Real.exp (-t)]
    wirelineNet.IsDualPriceTrajectory x p ∧
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) ∧
    Tendsto x atTop (𝓝 xStar) ∧
    Tendsto (fun t => wirelineNet.routePrice (p t)) atTop (𝓝 (wirelineNet.routePrice pStar)) ∧
    Tendsto p atTop (𝓝 pStar) := by
  intro xStar pStar p x
  obtain ⟨hU, hstrict⟩ := wirelineNet_admissible_and_strict
  have hroute : ∀ r : Fin 2, (wirelineNet.route r).Nonempty := fun r => by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [wirelineNet]
  have hcap : ∀ l : Fin 2, 0 ≤ wirelineNet.capacity l := fun l => by
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [wirelineNet]
  have hderiv_star : ∀ r : Fin 2, derivWithin (wirelineNet.utility r) (Ici 0) (xStar r) =
      wirelineNet.routePrice pStar r := fun r => by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · rw [wirelineNet_routePrice_zero]
      change derivWithin (quadLog 8 3 2) (Ici 0) 2 = 1 + 1
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
    · rw [wirelineNet_routePrice_one]
      change derivWithin (quadLog 5 2 2) (Ici 0) 2 = 1
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
  have hkkt : wirelineNet.IsKKT xStar pStar := by
    refine ⟨⟨fun r => by rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [xStar],
      fun l => ?_⟩,
      fun l => by rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [pStar],
      fun l => ?_, fun r => (hderiv_star r).le, fun r _ => hderiv_star r⟩
    · rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · rw [wirelineNet_linkLoad_zero]; simp [xStar, wirelineNet]
      · rw [wirelineNet_linkLoad_one]; simp [xStar, wirelineNet]; norm_num
    · rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · rw [wirelineNet_linkLoad_zero]; simp [xStar, wirelineNet]
      · rw [wirelineNet_linkLoad_one]; simp [xStar, wirelineNet]; norm_num
  have hexp_le : ∀ t ∈ Ici (0 : ℝ), Real.exp (-t) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mem_Ici.mp ht))
  have hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r : Fin 2, 0 ≤ x t r := fun t ht r => by
    have h1 := hexp_le t ht
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;>
      change 0 ≤ 2 - Real.exp (-t) <;> linarith
  have hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r : Fin 2,
      derivWithin (wirelineNet.utility r) (Ici 0) (x t r) = wirelineNet.routePrice (p t) r := by
    intro t ht r
    have hle : 2 - Real.exp (-t) ≤ 2 := by linarith [Real.exp_pos (-t)]
    have hnn : 0 ≤ 2 - Real.exp (-t) := by linarith [hexp_le t ht]
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · rw [wirelineNet_routePrice_zero]
      change derivWithin (quadLog 8 3 2) (Ici 0) (2 - Real.exp (-t)) =
        (1 + Real.exp (-t)) + (1 + 2 * Real.exp (-t))
      rw [derivWithin_quadLog (by norm_num) hnn]
      simp only [quadLogDeriv, hle, ↓reduceIte]
      ring
    · rw [wirelineNet_routePrice_one]
      change derivWithin (quadLog 5 2 2) (Ici 0) (2 - Real.exp (-t)) = 1 + 2 * Real.exp (-t)
      rw [derivWithin_quadLog (by norm_num) hnn]
      simp only [quadLogDeriv, hle, ↓reduceIte]
      ring
  have htraj : wirelineNet.IsDualPriceTrajectory x p := by
    intro t ht
    have he : 0 < Real.exp (-t) := Real.exp_pos (-t)
    refine ⟨fun l => by
        rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
        · change 0 ≤ 1 + Real.exp (-t); linarith
        · change 0 ≤ 1 + 2 * Real.exp (-t); linarith,
      fun l => ?_⟩
    have hd_exp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa only [mul_neg_one] using (hasDerivAt_neg t).exp
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
    · have hp_pos : ¬ (p t 0 ≤ 0) := by change ¬ (1 + Real.exp (-t) ≤ 0); linarith
      have hdrift : projDrift (wirelineNet.linkLoad (x t) 0 - wirelineNet.capacity 0) (p t 0) =
          -Real.exp (-t) := by
        simp only [projDrift, hp_pos, ↓reduceIte, wirelineNet_linkLoad_zero]
        change (2 - Real.exp (-t)) - 2 = -Real.exp (-t)
        ring
      rw [hdrift]
      have hfun : (fun s => p s 0) = fun s => 1 + Real.exp (-s) := by ext s; rfl
      rw [hfun]
      exact (hd_exp.const_add 1).hasDerivWithinAt
    · have hp_pos : ¬ (p t 1 ≤ 0) := by change ¬ (1 + 2 * Real.exp (-t) ≤ 0); linarith
      have hdrift : projDrift (wirelineNet.linkLoad (x t) 1 - wirelineNet.capacity 1) (p t 1) =
          -(2 * Real.exp (-t)) := by
        simp only [projDrift, hp_pos, ↓reduceIte, wirelineNet_linkLoad_one]
        change (2 - Real.exp (-t)) + (2 - Real.exp (-t)) - 4 = -(2 * Real.exp (-t))
        ring
      rw [hdrift]
      have hfun : (fun s => p s 1) = fun s => 1 + 2 * Real.exp (-s) := by ext s; rfl
      rw [hfun]
      simpa only [mul_neg] using ((hd_exp.const_mul 2).const_add 1).hasDerivWithinAt
  have hanti := htraj.antitoneOn_lyapunov_of_myopic hU hkkt hderiv_star hx0 hctrl
  obtain ⟨hxlim, hqlim, hplim⟩ :=
    htraj.tendsto_of_myopic hroute hcap hU hstrict hkkt hderiv_star hx0 hctrl
  exact ⟨htraj, hanti, hxlim, hqlim, hplim wirelineNet_injective_routePrice⟩

end WirelineNetwork

/-! ### 2. Boundary `x_r = 0` KKT witness -/

section BoundaryZeroRate

/-- Single-link 2-route network with linear utilities `U₀(x) = 2 x` and `U₁(x) = x`, where the
unique optimal allocation `x* = ![1, 0]` has `x* 1 = 0` and strict inequality
`U'₁(0) = 1 < 2 = q*₁`, witnessing boundary KKT handling. -/
example :
    let M : NetworkUtilityModel (Fin 2) (Fin 1) :=
      { route := fun _ => {0}
        capacity := fun _ => 1
        utility := fun r x => if r = 0 then 2 * x else x }
    M.IsKKT ![1, 0] ![2] ∧ M.IsSocialOptimum ![1, 0] ∧
      derivWithin (M.utility 1) (Ici 0) ((![1, 0] : Fin 2 → ℝ) 1) < M.routePrice ![2] 1 := by
  intro M
  have hflt : Finset.univ.filter (fun r : Fin 2 => (0 : Fin 1) ∈ M.route r) = {0, 1} := by decide
  have hload : M.linkLoad ![1, 0] 0 = 1 := by
    rw [NetworkUtilityModel.linkLoad, hflt, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
    norm_num
  have hq : ∀ r : Fin 2, M.routePrice ![2] r = 2 := fun _ => by
    simp [NetworkUtilityModel.routePrice, M]
  have hd0 : ∀ x ≥ 0, derivWithin (M.utility 0) (Ici 0) x = 2 := fun x hx => by
    have hfun : M.utility 0 = fun z => 2 * z := by ext z; simp [M]
    rw [hfun]
    simpa only [mul_one] using
      ((hasDerivAt_id' x).const_mul (2 : ℝ)).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 x hx)
  have hd1 : ∀ x ≥ 0, derivWithin (M.utility 1) (Ici 0) x = 1 := fun x hx => by
    have hfun : M.utility 1 = fun z => z := by ext z; simp [M]
    rw [hfun]
    exact (hasDerivAt_id' x).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 x hx)
  have hkkt : M.IsKKT ![1, 0] ![2] := by
    refine ⟨⟨fun r => by rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> norm_num,
      fun l => ?_⟩,
      fun l => by rw [Subsingleton.elim l 0]; norm_num, fun l => ?_, fun r => ?_, fun r hr => ?_⟩
    · rw [Subsingleton.elim l 0, hload]
    · rw [Subsingleton.elim l 0, hload]; change (2 : ℝ) * (1 - 1) = 0; ring
    · rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
      · rw [hq 0]; change derivWithin (M.utility 0) (Ici 0) 1 ≤ 2; rw [hd0 1 zero_le_one]
      · rw [hq 1]; change derivWithin (M.utility 1) (Ici 0) 0 ≤ 2; rw [hd1 0 le_rfl]; norm_num
    · rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
      · rw [hq 0]; change derivWithin (M.utility 0) (Ici 0) 1 = 2; exact hd0 1 zero_le_one
      · simp at hr
  have hU : ∀ r : Fin 2, IsAdmissibleUtility (M.utility r) := fun r => by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · simpa only [M, ↓reduceIte] using
        KellyGame.isAdmissibleUtility_linear (by norm_num : (0 : ℝ) < 2)
    · have hfun : M.utility 1 = fun x => 1 * x := by ext x; simp [M]
      rw [hfun]
      exact KellyGame.isAdmissibleUtility_linear zero_lt_one
  refine ⟨hkkt, hkkt.isSocialOptimum (fun r => (hU r).concaveOn) (fun r => (hU r).differentiableOn),
    ?_⟩
  rw [hq 1]
  change derivWithin (M.utility 1) (Ici 0) 0 < 2
  rw [hd1 0 le_rfl]
  norm_num

end BoundaryZeroRate

/-! ### 3. Interfering 2-link wireless network witness (Eqs. (22.16)–(22.21)) -/

section WirelessNetwork

/-- Two mutually interfering wireless links (`M₀ = {0}`, `M₁ = {1}`) with capacities `c = ![2, 4]`,
single-link routes, and smooth strictly concave utilities `quadLog 4 1 1` and
`quadLog (7 / 2) 1 2`. -/
private noncomputable def wirelessNet : WirelessNetworkModel (Fin 2) (Fin 2) (Fin 2) where
  route := fun r => {r}
  capacity := ![2, 4]
  utility := fun r => if r = 0 then quadLog 4 1 1 else quadLog (7 / 2) 1 2
  schedule := fun s => {s}

private theorem wirelessNet_admissible_and_strict :
    (∀ r, IsAdmissibleUtility (wirelessNet.utility r)) ∧
      (∀ r, StrictConcaveOn ℝ (Ici 0) (wirelessNet.utility r)) := by
  have h0 := quadLog_admissible_and_strictConcave (a := 4) (b := 1) (x₀ := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 := quadLog_admissible_and_strictConcave (a := 7 / 2) (b := 1) (x₀ := 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨fun r => ?_, fun r => ?_⟩ <;>
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;>
    simp [wirelessNet, h0, h1]

/-- Max-Weight corner-point identity (Eq. (22.20)) at asymmetric prices `p = ![4, 1]`: pure
schedule `s* = 0` achieves exact maximum weight `8` over all schedule distributions. -/
example :
    let p : Fin 2 → ℝ := ![4, 1]
    Finset.univ.sup' Finset.univ_nonempty (wirelessNet.scheduleWeight p) = 8 ∧
    IsScheduleDist (Pi.single (0 : Fin 2) (1 : ℝ)) ∧
    ∑ l, p l * wirelessNet.scheduledCapacity (Pi.single (0 : Fin 2) (1 : ℝ)) l = 8 ∧
    ∀ f, IsScheduleDist f → ∑ l, p l * wirelessNet.scheduledCapacity f l ≤ 8 := by
  intro p
  have hsup : Finset.univ.sup' Finset.univ_nonempty (wirelessNet.scheduleWeight p) = 8 := by
    have h0 : wirelessNet.scheduleWeight p 0 = 8 := by
      simp [WirelessNetworkModel.scheduleWeight, wirelessNet, p]; norm_num
    have h1 : wirelessNet.scheduleWeight p 1 = 4 := by
      simp [WirelessNetworkModel.scheduleWeight, wirelessNet, p]
    refine le_antisymm ?_ ?_
    · rw [Finset.sup'_le_iff]
      intro s _
      rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;> linarith
    · exact h0 ▸ Finset.le_sup' (wirelessNet.scheduleWeight p) (Finset.mem_univ 0)
  have hdist : IsScheduleDist (Pi.single (0 : Fin 2) (1 : ℝ)) :=
    ⟨fun s => by rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;> simp, by simp⟩
  have heq : ∑ l, p l * wirelessNet.scheduledCapacity (Pi.single (0 : Fin 2) (1 : ℝ)) l = 8 := by
    rw [wirelessNet.sum_price_mul_scheduledCapacity_eq, Fin.sum_univ_two]
    simp [WirelessNetworkModel.scheduleWeight, wirelessNet, p]
    norm_num
  have hle : ∀ f, IsScheduleDist f → ∑ l, p l * wirelessNet.scheduledCapacity f l ≤ 8 :=
    fun f hf => hsup ▸ wirelessNet.sum_price_mul_scheduledCapacity_le_maxWeight
      (fun l => by rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [p])
      (fun l => by rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [wirelessNet]) hf
  exact ⟨hsup, hdist, heq, hle⟩

/-- Wireless KKT optimality (`IsWirelessKKT`, `IsWirelessOptimum`) at `x* = ![1, 2]`,
`f* = ![1 / 2, 1 / 2]`, `p* = ![3, 3 / 2]`, and explicit non-stationary Max-Weight dual trajectory
`p(t) = ![3 + e⁻ᵗ, 3 / 2 + (1 / 2) e⁻ᵗ]`, `x(t) = ![1 - e⁻ᵗ, 2 - (1 / 2) e⁻ᵗ]` witnessing
Lyapunov drift, stability, and global convergence (Eqs. (22.15)–(22.21)). -/
example :
    let xStar : Fin 2 → ℝ := ![1, 2]
    let fStar : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    let pStar : Fin 2 → ℝ := ![3, 3 / 2]
    let p : ℝ → Fin 2 → ℝ := fun t => ![3 + Real.exp (-t), 3 / 2 + (1 / 2) * Real.exp (-t)]
    let x : ℝ → Fin 2 → ℝ := fun t => ![1 - Real.exp (-t), 2 - (1 / 2) * Real.exp (-t)]
    let f : ℝ → Fin 2 → ℝ := fun _ => fStar
    wirelessNet.IsWirelessKKT xStar fStar pStar ∧
    wirelessNet.IsWirelessOptimum xStar fStar ∧
    wirelessNet.IsWirelessDualTrajectory x f p ∧
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) ∧
    Tendsto x atTop (𝓝 xStar) ∧
    Tendsto p atTop (𝓝 pStar) := by
  intro xStar fStar pStar p x f
  obtain ⟨hU, hstrict⟩ := wirelessNet_admissible_and_strict
  have hroute : ∀ r : Fin 2, (wirelessNet.route r).Nonempty := fun r => by simp [wirelessNet]
  have hcap : ∀ l : Fin 2, 0 ≤ wirelessNet.capacity l := fun l => by
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp [wirelessNet]
  have hload : ∀ (y : Fin 2 → ℝ) (l : Fin 2), wirelessNet.linkLoad y l = y l := fun y l => by
    have hflt : Finset.univ.filter (fun r : Fin 2 => l ∈ wirelessNet.route r) = {l} := by
      ext r; simp [wirelessNet, eq_comm]
    simp [NetworkUtilityModel.linkLoad, hflt]
  have hsched : ∀ (g : Fin 2 → ℝ) (l : Fin 2),
      wirelessNet.scheduledCapacity g l = g l * wirelessNet.capacity l := fun g l => by
    have hflt : Finset.univ.filter (fun s : Fin 2 => l ∈ wirelessNet.schedule s) = {l} := by
      ext s; simp [wirelessNet, eq_comm]
    simp [WirelessNetworkModel.scheduledCapacity, hflt]
  have hq : ∀ (q : Fin 2 → ℝ) (r : Fin 2), wirelessNet.routePrice q r = q r := fun q r => by
    simp [NetworkUtilityModel.routePrice, wirelessNet]
  have hfStar_dist : IsScheduleDist fStar :=
    ⟨fun s => by rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;> simp [fStar],
      by simp [Fin.sum_univ_two, fStar]; norm_num⟩
  have hsched_max_tie : ∀ (q : Fin 2 → ℝ) (W : ℝ), 0 ≤ W →
      (∀ s : Fin 2, wirelessNet.scheduleWeight q s = W) →
      ∀ f', IsScheduleDist f' →
        ∑ l, q l * wirelessNet.scheduledCapacity f' l ≤
          ∑ l, q l * wirelessNet.scheduledCapacity fStar l := by
    intro q W hW htie f' hf'
    rw [wirelessNet.sum_price_mul_scheduledCapacity_eq q f',
      wirelessNet.sum_price_mul_scheduledCapacity_eq q fStar]
    simp_rw [htie, ← Finset.sum_mul]
    have hsumStar : ∑ s : Fin 2, fStar s = 1 := by simp [Fin.sum_univ_two, fStar]; norm_num
    rw [hsumStar, one_mul]
    exact mul_le_mul_of_nonneg_right hf'.2 hW |> fun h => by linarith
  have hderiv_star : ∀ r : Fin 2,
      derivWithin (wirelessNet.utility r) (Ici 0) (xStar r) = wirelessNet.routePrice pStar r := by
    intro r
    rw [hq]
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · change derivWithin (quadLog 4 1 1) (Ici 0) 1 = 3
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
    · change derivWithin (quadLog (7 / 2) 1 2) (Ici 0) 2 = 3 / 2
      rw [derivWithin_quadLog (by norm_num) (by norm_num)]
      simp [quadLogDeriv]; norm_num
  have hkkt : wirelessNet.IsWirelessKKT xStar fStar pStar := by
    refine ⟨⟨fun r => by rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl <;> simp [xStar],
      hfStar_dist, fun l => ?_⟩,
      fun l => by
        rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
        · simp [pStar]
        · simp [pStar]; norm_num,
      fun l => ?_, fun r => (hderiv_star r).le, fun r _ => hderiv_star r,
      hsched_max_tie pStar 6 (by norm_num) fun s => ?_⟩
    · rw [hload, hsched]
      rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · simp [xStar, fStar, wirelessNet]
      · simp [xStar, fStar, wirelessNet]; norm_num
    · rw [hload, hsched]
      rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
      · simp [xStar, fStar, wirelessNet]
      · simp [xStar, fStar, wirelessNet]; norm_num
    · rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;>
        (simp [WirelessNetworkModel.scheduleWeight, wirelessNet, pStar]; norm_num)
  have hopt : wirelessNet.IsWirelessOptimum xStar fStar :=
    hkkt.isWirelessOptimum (fun r => (hU r).concaveOn) (fun r => (hU r).differentiableOn)
  have hexp_le : ∀ t ∈ Ici (0 : ℝ), Real.exp (-t) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mem_Ici.mp ht))
  have hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r : Fin 2, 0 ≤ x t r := fun t ht r => by
    have h1 := hexp_le t ht
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · change 0 ≤ 1 - Real.exp (-t); linarith
    · change 0 ≤ 2 - (1 / 2) * Real.exp (-t); linarith
  have hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r : Fin 2,
      derivWithin (wirelessNet.utility r) (Ici 0) (x t r) = wirelessNet.routePrice (p t) r := by
    intro t ht r
    rw [hq]
    have h1 := hexp_le t ht
    have he := Real.exp_pos (-t)
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
    · change derivWithin (quadLog 4 1 1) (Ici 0) (1 - Real.exp (-t)) = 3 + Real.exp (-t)
      rw [derivWithin_quadLog (by norm_num) (by linarith)]
      simp only [quadLogDeriv, show 1 - Real.exp (-t) ≤ 1 by linarith, ↓reduceIte]
      ring
    · change derivWithin (quadLog (7 / 2) 1 2) (Ici 0) (2 - (1 / 2) * Real.exp (-t)) =
        3 / 2 + (1 / 2) * Real.exp (-t)
      rw [derivWithin_quadLog (by norm_num) (by linarith)]
      simp only [quadLogDeriv, show 2 - (1 / 2) * Real.exp (-t) ≤ 2 by linarith, ↓reduceIte]
      ring
  have htraj : wirelessNet.IsWirelessDualTrajectory x f p := by
    intro t ht
    have he := Real.exp_pos (-t)
    refine ⟨fun l => by
        rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
        · change 0 ≤ 3 + Real.exp (-t); linarith
        · change 0 ≤ 3 / 2 + (1 / 2) * Real.exp (-t); linarith,
      fun l => ?_⟩
    have hd_exp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa only [mul_neg_one] using (hasDerivAt_neg t).exp
    rw [hload, hsched]
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
    · have hp_pos : ¬ (p t 0 ≤ 0) := by change ¬ (3 + Real.exp (-t) ≤ 0); linarith
      have hdrift : projDrift (x t 0 - f t 0 * wirelessNet.capacity 0) (p t 0) =
          -Real.exp (-t) := by
        simp only [projDrift, hp_pos, ↓reduceIte]
        change (1 - Real.exp (-t)) - (1 / 2) * 2 = -Real.exp (-t)
        ring
      rw [hdrift]
      have hfun : (fun s => p s 0) = fun s => 3 + Real.exp (-s) := by ext s; rfl
      rw [hfun]
      exact (hd_exp.const_add 3).hasDerivWithinAt
    · have hp_pos : ¬ (p t 1 ≤ 0) := by
        change ¬ (3 / 2 + (1 / 2) * Real.exp (-t) ≤ 0); linarith
      have hdrift : projDrift (x t 1 - f t 1 * wirelessNet.capacity 1) (p t 1) =
          -(1 / 2 * Real.exp (-t)) := by
        simp only [projDrift, hp_pos, ↓reduceIte]
        change (2 - (1 / 2) * Real.exp (-t)) - (1 / 2) * 4 = -(1 / 2 * Real.exp (-t))
        ring
      rw [hdrift]
      have hfun : (fun s => p s 1) = fun s => 3 / 2 + (1 / 2) * Real.exp (-s) := by ext s; rfl
      rw [hfun]
      simpa only [mul_neg] using
        ((hd_exp.const_mul (1 / 2 : ℝ)).const_add (3 / 2 : ℝ)).hasDerivWithinAt
  have hf_max : ∀ t ∈ Ici (0 : ℝ), ∀ f', IsScheduleDist f' →
      ∑ l, p t l * wirelessNet.scheduledCapacity f' l ≤
        ∑ l, p t l * wirelessNet.scheduledCapacity (f t) l := fun t _ =>
    hsched_max_tie (p t) (6 + 2 * Real.exp (-t)) (by linarith [Real.exp_pos (-t)]) fun s => by
      rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;>
        simp [WirelessNetworkModel.scheduleWeight, wirelessNet, p] <;> ring
  have hanti := htraj.antitoneOn_lyapunov_of_myopic hU hkkt hderiv_star
    (fun _ _ => hfStar_dist) hf_max hx0 hctrl
  obtain ⟨hxlim, _, hplim⟩ := htraj.tendsto_of_myopic hroute hcap hU hstrict hkkt hderiv_star
    (fun _ _ => hfStar_dist) hf_max hx0 hctrl
  have hinj : Function.Injective wirelessNet.routePrice := fun q₁ q₂ h => funext fun l => by
    simpa only [hq] using congrFun h l
  exact ⟨hkkt, hopt, htraj, hanti, hxlim, hplim hinj⟩

end WirelessNetwork

end CslibFrontierTests.GameTheory.NetworkUtilityMax
