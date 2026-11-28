/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Multi-link network utility maximization, dual congestion control, and wireless Max-Weight

This module formalizes Section 22.1 of Ozdaglar and Srikant ([OzdaglarSrikant2007], pp. 572–578;
building on [Kelly1997]): competitive pricing and decentralized dual congestion control in
multi-link communication networks, together with the wireless Max-Weight scheduling extension.

1. **Multi-link Network Utility Maximization (`NUM`, Eqs. (22.1)–(22.7), pp. 572–575):**
   A finite network `NetworkUtilityModel R L` consists of sources/routes `R`, links `L`, route
   incidence `route : R → Finset L`, link capacities `capacity : L → ℝ`, and utility functions
   `utility : R → ℝ → ℝ`. The aggregate rate on link `l` is `linkLoad x l = ∑_{r : l ∈ r} x_r`,
   and the route price of source `r` under link prices `p` is `routePrice p r = ∑_{l ∈ r} p_l`,
   satisfying the adjoint identity `qᵀ x = pᵀ y` (`sum_routePrice_mul_eq_sum_price_mul_linkLoad`).
   For concave utilities differentiable on `[0, ∞)` (such as `IsAdmissibleUtility`), the KKT
   conditions `IsKKT` (`U'_r(x̂_r) ≤ q̂_r` with equality at `x̂_r > 0`, matching Eq. (22.2) on
   interior rates, plus Eqs. (22.3)–(22.5)) are both necessary (via Farkas' lemma) and sufficient
   for social optimality (`isSocialOptimum_iff_exists_isKKT`), decentralize the optimum via
   price-taking net-utility maximization (`IsKKT.priceTaking_optimal`, Eq. (22.7)), yield a unique
   optimal rate vector under strict concavity (`IsSocialOptimum.eq_of_strictConcaveOn`), and yield
   unique Lagrange multipliers at positive rates when the routing matrix has full row rank
   (`Function.Injective M.routePrice`, `IsKKT.price_eq_of_injective_routePrice`).

2. **Weighted Proportionally Fair Allocation (Eqs. (22.8)–(22.12), pp. 574, 576; [Vazirani2007],
   §5.13, p. 125):**
   For positive bids `w : R → ℝ`, positive capacities, and nonempty routes, the weighted
   proportionally fair allocation `IsWeightedPropFair` (`∑_r w_r (y_r - x*_r) / x*_r ≤ 0` for all
   feasible `y`) exists uniquely (`existsUnique_isWeightedPropFair`), coincides with maximizing
   `∑_r w_r log x_r` over positive feasible rates (`isWeightedPropFair_iff_max_log`, Eq. (22.8)),
   and is characterized by the KKT system `IsWeightedPropFairKKT` (`w_r / x*_r = q*_r`,
   Eqs. (22.9)–(22.12)). Setting `w_r = x̂_r U'_r(x̂_r)` aligns the proportionally fair optimum with
   the social optimum (`IsKKT.isWeightedPropFairKKT_of_myopicBids`), and facing route price
   `q_r > 0`, a myopic price-taker maximizing `U_r(w_r / q_r) - w_r` selects `w_r` satisfying
   `U'_r(w_r / q_r) = q_r` (`myopicBid_isMax_iff_derivWithin_eq`, Eq. (22.15)).

3. **Dual Congestion Control Lyapunov Stability and Global Convergence (Eqs. (22.13)–(22.15),
   pp. 575–576):**
   Under the projected link-price dynamics `ṗ_l = (y_l - c_l)^+_{p_l}` (`IsDualPriceTrajectory`,
   Eq. (22.13)), the quadratic Lyapunov function `lyapunov pStar p = (1 / 2) ∑_l (p_l - p*_l)^2`
   satisfies `dV/dt ≤ ∑_r (q_r(t) - q*_r) (x_r(t) - x*_r)` (`hasDerivWithinAt_lyapunov_le`). Both
   under fixed bids `x_r = w_r / q_r` (Eq. (22.14)) and under myopic rate control `U'_r(x_r) = q_r`
   (Eq. (22.15)) for strictly concave admissible utilities, `lyapunov pStar ∘ p` is nonincreasing
   on `[0, ∞)` and the trajectory converges globally: `q(t) → q*`, `x(t) → x*`, and under full row
   rank `p(t) → p*` (`tendsto_of_fixedBids`, `tendsto_of_myopic`).

4. **Wireless Network Utility Maximization and Max-Weight Scheduling (Eqs. (22.16)–(22.21),
   pp. 577–578):**
   Extending `NetworkUtilityModel` with a finite family of interference-free link schedules
   `schedule : S → Finset L` (`WirelessNetworkModel`), the scheduling dual subproblem (Eq. (22.20))
   attains its exact maximum at a maximum-weighted-price corner schedule
   (`sum_price_mul_scheduledCapacity_le_maxWeight`, `exists_maxWeight_corner`). The wireless KKT
   conditions (`IsWirelessKKT`) are necessary and sufficient for joint rate-and-schedule optimality
   (`IsWirelessKKT.isWirelessOptimum`, `IsWirelessOptimum.exists_isWirelessKKT`). Under the
   wireless projected price update `ṗ_l = (y_l - ∑_{s : l ∈ M_s} f_s c_l)^+_{p_l}` with a
   Max-Weight schedule at every instant (Eq. (22.21)), `lyapunov pStar ∘ p` obeys the same drift
   bound (`IsWirelessDualTrajectory.hasDerivWithinAt_lyapunov_le`), is nonincreasing, and converges
   globally under myopic rate control (`IsWirelessDualTrajectory.tendsto_of_myopic`).

## Main definitions

* `Cslib.GameTheory.NetworkUtilityModel`: multi-link network model (`route`, `capacity`, `utility`)
  with `linkLoad`, `routePrice`, `IsFeasible`, `welfare`, `IsSocialOptimum`, and `IsKKT`.
* `Cslib.GameTheory.NetworkUtilityModel.IsWeightedPropFair`, `IsWeightedPropFairKKT`: weighted
  proportional fairness and its KKT conditions (Eqs. (22.8)–(22.12)).
* `Cslib.GameTheory.projDrift`, `lyapunov`, `NetworkUtilityModel.IsDualPriceTrajectory`: projected
  excess-demand price dynamics (Eq. (22.13)) and quadratic Lyapunov function.
* `Cslib.GameTheory.IsScheduleDist`, `Cslib.GameTheory.WirelessNetworkModel`: wireless network
  extension with `schedule`, `scheduledCapacity`, `scheduleWeight`, `IsWirelessFeasible`,
  `IsWirelessOptimum`, `IsWirelessKKT`, and `IsWirelessDualTrajectory`.

## Main results

* `Cslib.GameTheory.NetworkUtilityModel.sum_routePrice_mul_eq_sum_price_mul_linkLoad`: adjoint
  routing identity `qᵀ x = pᵀ y` ([OzdaglarSrikant2007], §22.1, p. 575).
* `Cslib.GameTheory.NetworkUtilityModel.IsKKT.priceTaking_optimal`, `IsKKT.isSocialOptimum`,
  `IsSocialOptimum.exists_isKKT`, `isSocialOptimum_iff_exists_isKKT`, `exists_isKKT`,
  `IsSocialOptimum.eq_of_strictConcaveOn`, `IsKKT.price_eq_of_injective_routePrice`: KKT
  characterization, existence, uniqueness, and shadow-price decentralization
  ([OzdaglarSrikant2007], §22.1, Eqs. (22.1)–(22.7)).
* `Cslib.GameTheory.NetworkUtilityModel.isWeightedPropFair_iff_max_log`,
  `isWeightedPropFair_iff_exists_kkt`, `existsUnique_isWeightedPropFair`,
  `IsKKT.isWeightedPropFairKKT_of_myopicBids`, `myopicBid_isMax_iff_derivWithin_eq`: weighted
  proportional fairness and myopic bid alignment ([OzdaglarSrikant2007], §22.1,
  Eqs. (22.8)–(22.12), (22.15); [Vazirani2007], §5.13).
* `Cslib.GameTheory.NetworkUtilityModel.IsDualPriceTrajectory.hasDerivWithinAt_lyapunov_le`,
  `antitoneOn_lyapunov_of_fixedBids`, `tendsto_of_fixedBids`, `antitoneOn_lyapunov_of_myopic`,
  `tendsto_of_myopic`: dual congestion control Lyapunov stability and global convergence
  ([OzdaglarSrikant2007], §22.1, Eqs. (22.13)–(22.15)).
* `Cslib.GameTheory.WirelessNetworkModel.sum_price_mul_scheduledCapacity_le_maxWeight`,
  `exists_maxWeight_corner`, `IsWirelessKKT.isWirelessOptimum`,
  `IsWirelessOptimum.exists_isWirelessKKT`, `exists_isWirelessKKT`,
  `IsWirelessDualTrajectory.hasDerivWithinAt_lyapunov_le`,
  `IsWirelessDualTrajectory.antitoneOn_lyapunov_of_myopic`,
  `IsWirelessDualTrajectory.tendsto_of_myopic`: wireless Max-Weight dual decomposition, KKT
  optimality, Lyapunov stability, and global convergence ([OzdaglarSrikant2007], §22.1,
  Eqs. (22.16)–(22.21)).

## References

* [Kelly1997]
* [OzdaglarSrikant2007]
* [Vazirani2007]
-/

public section

open Filter Matrix Set
open scoped Topology

namespace Cslib.GameTheory

/-! ### Private analysis helpers (first-order optimality, concavity, Barbalat) -/

private theorem hasDerivWithinAt_nonpos_of_eventually_le {φ : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt φ d (Ici 0) 0) (hmax : ∀ᶠ t in 𝓝[≥] (0 : ℝ), φ t ≤ φ 0) :
    d ≤ 0 := by
  have hlim : Tendsto (slope φ 0) (𝓝[>] 0) (𝓝 d) := by
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp (hd.mono Ioi_subset_Ici_self)
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using h1
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope φ 0 t ≤ 0 := by
    filter_upwards [hmax.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self),
      self_mem_nhdsWithin] with t ht hpos
    rw [slope_def_field, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (mem_Ioi.mp hpos).le
  exact le_of_tendsto hlim hle

private theorem antitoneOn_Ici_of_hasDerivWithinAt_nonpos {V V' : ℝ → ℝ}
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt V (V' t) (Ici 0) t)
    (hnonpos : ∀ t ∈ Ici (0 : ℝ), V' t ≤ 0) :
    AntitoneOn V (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousWithinAt) ?_ ?_
  · intro t ht
    rw [interior_Ici] at ht
    have hda := (hd t (mem_Ioi.mp ht).le).hasDerivAt (Ici_mem_nhds ht)
    exact hda.differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [((hd t (mem_Ioi.mp ht).le).hasDerivAt (Ici_mem_nhds ht)).deriv]
    exact hnonpos t (mem_Ioi.mp ht).le

private theorem strictAntiOn_derivWithin_of_strictConcaveOn {u : ℝ → ℝ}
    (hstrict : StrictConcaveOn ℝ (Ici 0) u) (hdiff : DifferentiableOn ℝ u (Ici 0)) :
    StrictAntiOn (derivWithin u (Ici 0)) (Ici 0) := by
  intro x hx y hy hxy
  have hdx : HasDerivWithinAt u (derivWithin u (Ici 0) x) (Ici 0) x := (hdiff x hx).hasDerivWithinAt
  have hdy : HasDerivWithinAt u (derivWithin u (Ici 0) y) (Ici 0) y := (hdiff y hy).hasDerivWithinAt
  have h1 := hstrict.neg.add_lt_of_hasFDerivWithinAt hx hy hxy.ne' hdx.neg.hasFDerivWithinAt
  have h2 := hstrict.neg.add_lt_of_hasFDerivWithinAt hy hx hxy.ne hdy.neg.hasFDerivWithinAt
  simp only [Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h1 h2
  nlinarith

private theorem continuousWithinAt_derivWithin_of_admissible {u : ℝ → ℝ}
    (hu : IsAdmissibleUtility u) {x₀ : ℝ} (hx₀ : 0 ≤ x₀) :
    ContinuousWithinAt (derivWithin u (Ici 0)) (Ici 0) x₀ := by
  set g : ℝ → ℝ := derivWithin u (Ici 0)
  have hanti : AntitoneOn g (Ici 0) := hu.derivWithin_antitoneOn
  have hd_pos : ∀ z > 0, HasDerivAt u (g z) z := fun z hz =>
    (hu.hasDerivWithinAt hz.le).hasDerivAt (Ici_mem_nhds hz)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- Right control: find `cR > x₀` with `g x₀ - ε < g cR`.
  have hR_lim : Tendsto (slope u x₀) (𝓝[>] x₀) (𝓝 (g x₀)) := by
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp
      ((hu.hasDerivWithinAt hx₀).mono (Ioi_subset_Ici hx₀))
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using h1
  have hR_ev : ∀ᶠ y in 𝓝[>] x₀, g x₀ - ε < slope u x₀ y :=
    hR_lim.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨yR, hyR_lt, hyR_gt⟩ := (hR_ev.and self_mem_nhdsWithin).exists
  have hR_cont : ContinuousOn u (Icc x₀ yR) :=
    hu.continuousOn.mono fun z hz => hx₀.trans hz.1
  have hR_deriv : ∀ z ∈ Ioo x₀ yR, HasDerivAt u (g z) z := fun z hz =>
    hd_pos z (lt_of_le_of_lt hx₀ hz.1)
  obtain ⟨cR, hcR, hcR_eq⟩ := exists_hasDerivAt_eq_slope u g hyR_gt hR_cont hR_deriv
  have hgR : g x₀ - ε < g cR := by
    rw [hcR_eq]
    simpa only [slope_def_field] using hyR_lt
  rcases eq_or_lt_of_le hx₀ with rfl | hx₀_pos
  · refine ⟨cR, hcR.1, fun x hx hdist => ?_⟩
    have hx0 : 0 ≤ x := mem_Ici.mp hx
    rw [Real.dist_eq] at hdist ⊢
    have hxc : x < cR := by
      rw [sub_zero, abs_of_nonneg hx0] at hdist
      exact hdist
    have hle : g x ≤ g 0 := hanti le_rfl hx0 hx0
    have hge : g cR ≤ g x := hanti hx0 (mem_Ici.mpr hcR.1.le) hxc.le
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  · -- Left control when `x₀ > 0`: find `cL ∈ (0, x₀)` with `g cL < g x₀ + ε`.
    have hL_lim : Tendsto (slope u x₀) (𝓝[<] x₀) (𝓝 (g x₀)) := by
      have h1 := hasDerivWithinAt_iff_tendsto_slope.mp
        ((hd_pos x₀ hx₀_pos).hasDerivWithinAt (s := Iio x₀))
      simpa only [Set.sdiff_singleton_eq_self (notMem_Iio.mpr le_rfl)] using h1
    have hL_ev : ∀ᶠ y in 𝓝[<] x₀, slope u x₀ y < g x₀ + ε :=
      hL_lim.eventually (Iio_mem_nhds (by linarith))
    have hL_pos : ∀ᶠ y in 𝓝[<] x₀, 0 < y :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hx₀_pos)
    obtain ⟨yL, ⟨hyL_lt, hyL_pos⟩, hyL_gt⟩ := ((hL_ev.and hL_pos).and self_mem_nhdsWithin).exists
    have hL_cont : ContinuousOn u (Icc yL x₀) :=
      hu.continuousOn.mono fun z hz => hyL_pos.le.trans hz.1
    have hL_deriv : ∀ z ∈ Ioo yL x₀, HasDerivAt u (g z) z := fun z hz =>
      hd_pos z (hyL_pos.trans hz.1)
    obtain ⟨cL, hcL, hcL_eq⟩ := exists_hasDerivAt_eq_slope u g hyL_gt hL_cont hL_deriv
    have hgL : g cL < g x₀ + ε := by
      rw [hcL_eq]
      have hslope : (u x₀ - u yL) / (x₀ - yL) = slope u x₀ yL := by
        rw [slope_def_field]
        have hne : x₀ - yL ≠ 0 := sub_ne_zero.mpr hyL_gt.ne'
        have hne' : yL - x₀ ≠ 0 := sub_ne_zero.mpr hyL_gt.ne
        field_simp [hne, hne']
        ring
      rwa [hslope]
    refine ⟨min (cR - x₀) (x₀ - cL), lt_min (sub_pos.mpr hcR.1) (sub_pos.mpr hcL.2),
      fun x hx hdist => ?_⟩
    have hx0 : 0 ≤ x := mem_Ici.mp hx
    rw [Real.dist_eq, abs_lt] at hdist ⊢
    have hlt_R : x < cR := by linarith [min_le_left (cR - x₀) (x₀ - cL)]
    have hgt_L : cL < x := by linarith [min_le_right (cR - x₀) (x₀ - cL)]
    have h1 : g cR ≤ g x := hanti hx0 (hx₀.trans hcR.1.le) hlt_R.le
    have h2 : g x ≤ g cL := hanti (hyL_pos.trans hcL.1).le hx0 hgt_L.le
    exact ⟨by linarith, by linarith⟩

/-- Uniform continuity of the inverse of any strictly antitone function on a bounded interval
`[0, X]`: small changes in `f a` force small changes in `a`. -/
private theorem uniform_modulus_of_strictAntiOn {f : ℝ → ℝ} (hf : StrictAntiOn f (Ici 0))
    {X : ℝ} (hX : 0 ≤ X) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ a ∈ Icc 0 X, ∀ b ∈ Icc 0 X, |f a - f b| < η → |a - b| < ε := by
  rcases eq_or_lt_of_le hX with rfl | hX_pos
  · refine ⟨1, zero_lt_one, fun a ha b hb _ => ?_⟩
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    have hb0 : b = 0 := le_antisymm hb.2 hb.1
    simp [ha0, hb0, hε]
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 * X / ε)
    have hN_pos : 0 < N := by
      by_contra h0
      have hN0 : N = 0 := by omega
      rw [hN0, Nat.cast_zero] at hN
      have : 0 < 2 * X / ε := by positivity
      linarith
    have hstep : 2 * X / (N : ℝ) < ε := by
      have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      rw [div_lt_iff₀ hNr]
      have h1 := (div_lt_iff₀ hε).mp hN
      linarith
    let grid : ℕ → ℝ := fun k => (k : ℝ) * X / (N : ℝ)
    have hgrid_nonneg : ∀ k : ℕ, 0 ≤ grid k := fun k => by dsimp only [grid]; positivity
    have hgrid_lt : ∀ k : ℕ, grid k < grid (k + 1) := fun k => by
      dsimp only [grid]
      have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      rw [div_lt_div_iff_of_pos_right hNr]
      push_cast
      nlinarith
    have huniv : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN_pos⟩, Finset.mem_univ _⟩
    let η : ℝ := Finset.univ.inf' huniv fun k : Fin N => f (grid k.val) - f (grid (k.val + 1))
    have hη_pos : 0 < η := by
      rw [Finset.lt_inf'_iff]
      intro k _
      exact sub_pos.mpr (hf (hgrid_nonneg k.val) (hgrid_nonneg (k.val + 1)) (hgrid_lt k.val))
    have hordered : ∀ a ∈ Icc 0 X, ∀ b ∈ Icc 0 X, a ≤ b → ε ≤ b - a → η ≤ |f a - f b| := by
      intro a ha b hb _ hba
      have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      let k : ℕ := Nat.floor (a * (N : ℝ) / X) + 1
      have ha_lt : a < grid k := by
        have hk : a * (N : ℝ) / X < (k : ℝ) := by
          dsimp only [k]; push_cast; exact Nat.lt_floor_add_one _
        dsimp only [grid]
        have h1 := (div_lt_iff₀ hX_pos).mp hk
        rw [lt_div_iff₀ hNr]
        linarith
      have hgk1_lt : grid (k + 1) < b := by
        have hk : (Nat.floor (a * (N : ℝ) / X) : ℝ) ≤ a * (N : ℝ) / X :=
          Nat.floor_le (div_nonneg (mul_nonneg ha.1 hNr.le) hX_pos.le)
        have hcalc : grid (k + 1) ≤ a + 2 * X / (N : ℝ) := by
          dsimp only [grid, k]
          push_cast
          have h1 : ((Nat.floor (a * (N : ℝ) / X) : ℝ) + 1 + 1) * X / (N : ℝ) ≤
              (a * (N : ℝ) / X + 2) * X / (N : ℝ) := by
            apply div_le_div_of_nonneg_right _ hNr.le
            nlinarith
          have h2 : (a * (N : ℝ) / X + 2) * X / (N : ℝ) = a + 2 * X / (N : ℝ) := by
            field_simp [hX_pos.ne', hNr.ne']
          linarith
        linarith
      have hk_lt_N : k < N := by
        have hlt : grid (k + 1) < grid N := by
          have hgn : grid N = X := by
            dsimp only [grid]; field_simp [hNr.ne']
          linarith [hb.2]
        dsimp only [grid] at hlt
        have h1 : ((k + 1 : ℕ) : ℝ) * X < (N : ℝ) * X := (div_lt_div_iff_of_pos_right hNr).mp hlt
        have h2 : ((k + 1 : ℕ) : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_right h1 hX_pos.le
        have h3 : k + 1 < N := Nat.cast_lt.mp h2
        omega
      have hη_le : η ≤ f (grid k) - f (grid (k + 1)) :=
        Finset.inf'_le (f := fun j : Fin N => f (grid j.val) - f (grid (j.val + 1)))
          (Finset.mem_univ ⟨k, hk_lt_N⟩)
      have hf1 : f (grid k) < f a := hf ha.1 (hgrid_nonneg k) ha_lt
      have hf2 : f b < f (grid (k + 1)) := hf (hgrid_nonneg (k + 1)) hb.1 hgk1_lt
      have hdiff : f (grid k) - f (grid (k + 1)) < f a - f b := by linarith
      exact hη_le.trans (hdiff.le.trans (le_abs_self _))
    refine ⟨η, hη_pos, fun a ha b hb hlt => ?_⟩
    by_contra hge
    push Not at hge
    rcases le_total a b with hab | hba
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)] at hge
      linarith [hordered a ha b hb hab hge]
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)] at hge
      rw [abs_sub_comm] at hlt
      linarith [hordered b hb a ha hba hge]

/-- Elementary MVT-based Barbalat lemma: if `V ≥ 0` on `[0, ∞)` has derivative `V' t ≤ -φ t`
with `φ ≥ 0` uniformly continuous on `[0, ∞)`, then `φ t → 0` as `t → ∞`. -/
private theorem tendsto_zero_of_hasDerivWithinAt_le_neg {V V' φ : ℝ → ℝ}
    (hV0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ V t)
    (hVderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt V (V' t) (Ici 0) t)
    (hφ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ φ t)
    (hdecay : ∀ t ∈ Ici (0 : ℝ), V' t ≤ -φ t)
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |s - t| ≤ δ → |φ s - φ t| ≤ ε) :
    Tendsto φ atTop (𝓝 0) := by
  have hanti : AntitoneOn V (Ici 0) :=
    antitoneOn_Ici_of_hasDerivWithinAt_nonpos hVderiv fun t ht => by
      linarith [hdecay t ht, hφ0 t ht]
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hnot
  push Not at hnot
  obtain ⟨δ, hδ, hδ_uc⟩ := huc (ε / 2) (half_pos hε)
  have hdrop : ∀ u : ℝ, 0 ≤ u → ε ≤ φ u → V (u + δ) ≤ V u - (ε / 2) * δ := by
    intro u hu hφu
    have hcont : ContinuousOn V (Icc u (u + δ)) :=
      fun s hs => (hVderiv s (hu.trans hs.1)).continuousWithinAt.mono fun z hz => hu.trans hz.1
    have hder : ∀ s ∈ Ioo u (u + δ), HasDerivAt V (V' s) s := fun s hs =>
      (hVderiv s (hu.trans hs.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt hu hs.1))
    obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope V V' (by linarith : u < u + δ) hcont hder
    have hc0 : 0 ≤ c := hu.trans hc.1.le
    have hdiff : |c - u| ≤ δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le)]
      linarith [hc.2]
    have hφc : ε / 2 ≤ φ c := by
      have h1 := hδ_uc c hc0 u hu hdiff
      rw [abs_le] at h1
      linarith
    have hVc : V' c ≤ -(ε / 2) := by linarith [hdecay c hc0]
    have hslope : (V (u + δ) - V u) / δ ≤ -(ε / 2) := by
      have hden : u + δ - u = δ := by ring
      rw [hden] at hc_eq
      linarith
    have hmul := (div_le_iff₀ hδ).mp hslope
    linarith
  have hstep_exists : ∀ T : ℝ, 0 ≤ T → ∃ t ≥ T, ε ≤ φ t := by
    intro T hT
    obtain ⟨t, htT, hdist⟩ := hnot T
    refine ⟨t, htT, ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hφ0 t (hT.trans htT))] at hdist
    exact hdist
  have hseq : ∀ n : ℕ, ∃ t : ℝ, 0 ≤ t ∧ V (t + δ) ≤ V 0 - ((n + 1 : ℕ) : ℝ) * ((ε / 2) * δ) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨t₀, ht₀, hφ₀⟩ := hstep_exists 0 le_rfl
      refine ⟨t₀, ht₀, ?_⟩
      have h1 := hdrop t₀ ht₀ hφ₀
      have h2 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht₀) ht₀
      have hcast : ((0 + 1 : ℕ) : ℝ) * ((ε / 2) * δ) = (ε / 2) * δ := by norm_num
      linarith
    | succ n ih =>
      obtain ⟨tn, htn0, hVn⟩ := ih
      obtain ⟨t', ht', hφ'⟩ := hstep_exists (tn + δ) (by linarith)
      have ht'0 : 0 ≤ t' := by linarith
      refine ⟨t', ht'0, ?_⟩
      have h1 := hdrop t' ht'0 hφ'
      have h2 := hanti (mem_Ici.mpr (by linarith : 0 ≤ tn + δ)) (mem_Ici.mpr ht'0) ht'
      have hcast : ((n + 1 + 1 : ℕ) : ℝ) * ((ε / 2) * δ) =
          ((n + 1 : ℕ) : ℝ) * ((ε / 2) * δ) + (ε / 2) * δ := by push_cast; ring
      linarith
  have hstep_pos : 0 < (ε / 2) * δ := mul_pos (half_pos hε) hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (V 0 / ((ε / 2) * δ))
  obtain ⟨tN, htN0, hVN⟩ := hseq N
  have hVN_nonneg : 0 ≤ V (tN + δ) := hV0 (tN + δ) (mem_Ici.mpr (by linarith))
  have hN_mul : V 0 < (N : ℝ) * ((ε / 2) * δ) := (div_lt_iff₀ hstep_pos).mp hN
  have hcast : ((N + 1 : ℕ) : ℝ) * ((ε / 2) * δ) =
      (N : ℝ) * ((ε / 2) * δ) + (ε / 2) * δ := by push_cast; ring
  linarith

private theorem hasDerivWithinAt_comp_add_mul {u : ℝ → ℝ} {x d : ℝ}
    (hu : HasDerivWithinAt u (derivWithin u (Ici 0) x) (Ici 0) x)
    (hmaps : ∀ᶠ t in 𝓝[≥] (0 : ℝ), x + t * d ∈ Ici (0 : ℝ)) :
    HasDerivWithinAt (fun t => u (x + t * d))
      (derivWithin u (Ici 0) x * d) (Ici 0) 0 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hmaps
  have hlin : HasDerivWithinAt (fun t : ℝ => x + t * d) d (Icc 0 (δ / 2)) 0 := by
    simpa only [one_mul] using
      (((hasDerivAt_id' (0 : ℝ)).mul_const d).const_add x).hasDerivWithinAt (s := Icc 0 (δ / 2))
  have hu0 : HasDerivWithinAt u (derivWithin u (Ici 0) x) (Ici 0) (x + 0 * d) := by
    simpa only [zero_mul, add_zero] using hu
  have hmaps' : MapsTo (fun t : ℝ => x + t * d) (Icc 0 (δ / 2)) (Ici 0) := fun t ht => by
    apply hsub
    refine ⟨?_, ht.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  exact (hu0.comp 0 hlin hmaps').mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (half_pos hδ))

private theorem eventually_add_mul_nonneg_nhdsGE {a b : ℝ} (ha : 0 ≤ a) (hb : a = 0 → 0 ≤ b) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ a + t * b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← ha0, zero_add]
    exact mul_nonneg (mem_Ici.mp ht) (hb ha0.symm)
  · have hcont : ContinuousAt (fun t : ℝ => a + t * b) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a + t * b :=
      hcont.eventually (show Ioi (0 : ℝ) ∈ 𝓝 (a + 0 * b) by
        simpa only [zero_mul, add_zero] using Ioi_mem_nhds hapos)
    exact (hmem.filter_mono nhdsWithin_le_nhds).mono fun _ ht => ht.le

private theorem eventually_add_mul_le_nhdsGE {a b c : ℝ} (hac : a ≤ c) (hb : a = c → b ≤ 0) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), a + t * b ≤ c := by
  have h := eventually_add_mul_nonneg_nhdsGE (a := c - a) (b := -b) (sub_nonneg.mpr hac)
    fun h0 => neg_nonneg.mpr (hb (by linarith))
  exact h.mono fun t ht => by linarith

/-! ### Shared dual-dynamics definitions (`projDrift`, `lyapunov`, myopic bid optimality) -/

/-- **Myopic price-taking bid optimality** ([OzdaglarSrikant2007], §22.1, Eq. (22.15), p. 576):
facing route price `q > 0` with a concave differentiable utility `u` on `[0, ∞)`, a positive bid
`w > 0` maximizes instantaneous net utility `t ↦ u (t / q) - t` over `t ≥ 0` if and only if
`u'(w / q) = q` (equivalently `w = (w / q) * u'(w / q)`). -/
theorem myopicBid_isMax_iff_derivWithin_eq {u : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Ici 0) u) (hdiff : DifferentiableOn ℝ u (Ici 0))
    {q w : ℝ} (hq : 0 < q) (hw : 0 < w) :
    (∀ t : ℝ, 0 ≤ t → u (t / q) - t ≤ u (w / q) - w) ↔
      derivWithin u (Ici 0) (w / q) = q := by
  have hwq : 0 < w / q := div_pos hw hq
  constructor
  · intro hmax
    have hloc : IsLocalMax (fun t => u (t / q) - t) w := by
      filter_upwards [Ioi_mem_nhds hw] with t ht
      exact hmax t (mem_Ioi.mp ht).le
    have hdu : HasDerivAt u (derivWithin u (Ici 0) (w / q)) (w / q) :=
      (hdiff (w / q) hwq.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds hwq)
    have hd : HasDerivAt (fun t => u (t / q) - t)
        (derivWithin u (Ici 0) (w / q) * (1 / q) - 1) w := by
      have hdiv : HasDerivAt (fun t : ℝ => t / q) (1 / q) w := (hasDerivAt_id' w).div_const q
      exact (hdu.comp w hdiv).sub (hasDerivAt_id' w)
    have hzero := hloc.hasDerivAt_eq_zero hd
    field_simp [hq.ne'] at hzero
    linarith
  · intro heq t ht
    have htan := hconc.le_add_mul_of_hasDerivWithinAt hwq.le (div_nonneg ht hq.le)
      (hdiff (w / q) hwq.le).hasDerivWithinAt
    rw [heq] at htan
    have hmul : q * (t / q - w / q) = t - w := by field_simp [hq.ne']
    linarith

/-- Projected price drift `(a)^+_b = max a 0` when `b ≤ 0` and `a` when `b > 0`
([OzdaglarSrikant2007], §22.1, Eq. (22.13), p. 575). -/
@[expose] noncomputable def projDrift (a b : ℝ) : ℝ :=
  if b ≤ 0 then max a 0 else a

/-- Quadratic Lyapunov function `V(p) = (1 / 2) ∑_l (p_l - p*_l)^2`
([OzdaglarSrikant2007], §22.1, p. 575). -/
@[expose] noncomputable def lyapunov {L : Type*} [Fintype L] (pStar p : L → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (p l - pStar l) ^ 2

theorem lyapunov_nonneg {L : Type*} [Fintype L] (pStar p : L → ℝ) :
    0 ≤ lyapunov pStar p :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem lyapunov_eq_zero_iff {L : Type*} [Fintype L] {pStar p : L → ℝ} :
    lyapunov pStar p = 0 ↔ p = pStar := by
  constructor
  · intro h
    have hsum : ∑ l, (p l - pStar l) ^ 2 = 0 := by
      unfold lyapunov at h; linarith
    funext l
    have hl := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (p i - pStar i)).mp
      hsum l (Finset.mem_univ l)
    linarith [sq_eq_zero_iff.mp hl]
  · rintro rfl
    simp [lyapunov]

private theorem mul_projDrift_le {a p pStar : ℝ} (hp : 0 ≤ p) (hpStar : 0 ≤ pStar) :
    (p - pStar) * projDrift a p ≤ (p - pStar) * a := by
  unfold projDrift
  split_ifs with hp0
  · have hpeq : p = 0 := le_antisymm hp0 hp
    rw [hpeq, zero_sub]
    rcases le_total a 0 with ha | ha
    · rw [max_eq_right ha, mul_zero]
      nlinarith
    · rw [max_eq_left ha]
  · exact le_rfl

private theorem le_projDrift (a b : ℝ) : a ≤ projDrift a b := by
  unfold projDrift
  split_ifs
  · exact le_max_left a 0
  · exact le_rfl

private theorem abs_projDrift_le (a b : ℝ) : |projDrift a b| ≤ |a| := by
  unfold projDrift
  split_ifs
  · rcases le_total a 0 with ha | ha
    · rw [max_eq_right ha, abs_zero]; exact abs_nonneg a
    · rw [max_eq_left ha]
  · exact le_rfl

private theorem hasDerivWithinAt_lyapunov {L : Type*} [Fintype L] {p : ℝ → L → ℝ}
    {p' : L → ℝ} {pStar : L → ℝ} {t : ℝ}
    (hp : ∀ l, HasDerivWithinAt (fun s => p s l) (p' l) (Ici 0) t) :
    HasDerivWithinAt (fun s => lyapunov pStar (p s))
      (∑ l, (p t l - pStar l) * p' l) (Ici 0) t := by
  have hsq : ∀ l, HasDerivWithinAt (fun s => (p s l - pStar l) ^ 2)
      (2 * (p t l - pStar l) * p' l) (Ici 0) t := fun l => by
    have h1 := ((hp l).sub_const (pStar l)).mul ((hp l).sub_const (pStar l))
    have hfun : (fun s => (p s l - pStar l) ^ 2) =
        fun s => (p s l - pStar l) * (p s l - pStar l) := by ext s; ring
    rw [hfun]
    convert h1 using 1
    ring
  have hsum : HasDerivWithinAt (fun s => (1 / 2 : ℝ) * ∑ l, (p s l - pStar l) ^ 2)
      ((1 / 2 : ℝ) * ∑ l, 2 * (p t l - pStar l) * p' l) (Ici 0) t :=
    (HasDerivWithinAt.fun_sum fun l (_ : l ∈ Finset.univ) => hsq l).const_mul (1 / 2 : ℝ)
  unfold lyapunov
  convert hsum using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

private theorem antitoneOn_lyapunov_of_drift_nonpos {L : Type*} [Fintype L]
    {p : ℝ → L → ℝ} {pStar : L → ℝ}
    (hdrift : ∀ t ∈ Ici (0 : ℝ),
      ∃ D, HasDerivWithinAt (fun s => lyapunov pStar (p s)) D (Ici 0) t ∧ D ≤ 0) :
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) := by
  classical
  let D : ℝ → ℝ := fun t => if h : t ∈ Ici (0 : ℝ) then (hdrift t h).choose else 0
  refine antitoneOn_Ici_of_hasDerivWithinAt_nonpos (V' := D)
    (fun t ht => ?_) (fun t ht => ?_)
  · simp only [D, ht, ↓reduceDIte]
    exact (hdrift t ht).choose_spec.1
  · simp only [D, ht, ↓reduceDIte]
    exact (hdrift t ht).choose_spec.2

/-! ### Part 1: Multi-link Network Utility Maximization (`NUM`, Eqs. (22.1)–(22.7)) -/

/-- A multi-link network utility maximization (NUM) instance with sources/routes `R`, links `L`,
route incidence `route : R → Finset L`, link capacities `capacity : L → ℝ`, and source utilities
`utility : R → ℝ → ℝ` ([OzdaglarSrikant2007], §22.1, pp. 572–573; [Kelly1997]). -/
structure NetworkUtilityModel (R L : Type*) where
  /-- Set of links traversed by source `r`. -/
  route : R → Finset L
  /-- Available bandwidth capacity `c_l` of link `l`. -/
  capacity : L → ℝ
  /-- Utility function `U_r` of source `r` on `[0, ∞)`. -/
  utility : R → ℝ → ℝ

namespace NetworkUtilityModel

variable {R L : Type*} (M : NetworkUtilityModel R L)

/-- Aggregate arrival rate `y_l = ∑_{r : l ∈ r} x_r` on link `l`. -/
@[expose] def linkLoad [Fintype R] [DecidableEq L] (x : R → ℝ) (l : L) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => l ∈ M.route r), x r

/-- Aggregate price `q_r = ∑_{l ∈ r} p_l` along route `r` ([OzdaglarSrikant2007], Eq. (22.6)). -/
@[expose] def routePrice (p : L → ℝ) (r : R) : ℝ :=
  ∑ l ∈ M.route r, p l

/-- Feasibility of a rate vector `x : R → ℝ`: `x ≥ 0` and `R x ≤ c`
([OzdaglarSrikant2007], Eqs. (22.1), (22.4)–(22.5)). -/
@[expose] def IsFeasible [Fintype R] [DecidableEq L] (x : R → ℝ) : Prop :=
  (∀ r, 0 ≤ x r) ∧ ∀ l, M.linkLoad x l ≤ M.capacity l

/-- Aggregate social welfare `∑_r U_r(x_r)` of a rate vector `x`. -/
@[expose] def welfare [Fintype R] (x : R → ℝ) : ℝ :=
  ∑ r, M.utility r (x r)

/-- A feasible rate vector `x` is socially optimal if it maximizes aggregate utility over all
feasible rate vectors ([OzdaglarSrikant2007], Eq. (22.1), p. 573). -/
@[expose] def IsSocialOptimum [Fintype R] [DecidableEq L] (x : R → ℝ) : Prop :=
  M.IsFeasible x ∧ ∀ y, M.IsFeasible y → M.welfare y ≤ M.welfare x

/-- Karush–Kuhn–Tucker (KKT) optimality conditions for multi-link network utility maximization
([OzdaglarSrikant2007], §22.1, Eqs. (22.2)–(22.5), p. 573). For general utilities on `[0, ∞)` with
finite right derivative at `0`, stationarity at `x r = 0` is `U'_r(0) ≤ q_r`, reducing to Eq. (22.2)
`U'_r(x r) = q_r` at all strictly positive rates `0 < x r`. -/
structure IsKKT [Fintype R] [DecidableEq L] (x : R → ℝ) (p : L → ℝ) : Prop where
  /-- Primal feasibility: `x ≥ 0` and `R x ≤ c` (Eqs. (22.4)–(22.5)). -/
  feasible : M.IsFeasible x
  /-- Dual nonnegativity: `p ≥ 0` (Eq. (22.5)). -/
  price_nonneg : ∀ l, 0 ≤ p l
  /-- Complementary slackness: `p_l (y_l - c_l) = 0` for every link `l` (Eq. (22.3)). -/
  comp_slack : ∀ l, p l * (M.linkLoad x l - M.capacity l) = 0
  /-- Stationarity inequality: `U'_r(x_r) ≤ q_r` for every source `r`. -/
  deriv_le : ∀ r, derivWithin (M.utility r) (Ici 0) (x r) ≤ M.routePrice p r
  /-- Interior stationarity equality: `U'_r(x_r) = q_r` whenever `0 < x_r` (Eq. (22.2)). -/
  deriv_eq_of_pos : ∀ r, 0 < x r → derivWithin (M.utility r) (Ici 0) (x r) = M.routePrice p r

/-- Adjoint routing identity `qᵀ x = pᵀ R x = pᵀ y` ([OzdaglarSrikant2007], §22.1, p. 575). -/
theorem sum_routePrice_mul_eq_sum_price_mul_linkLoad [Fintype R] [Fintype L] [DecidableEq L]
    (p : L → ℝ) (x : R → ℝ) :
    ∑ r, M.routePrice p r * x r = ∑ l, p l * M.linkLoad x l := by
  classical
  calc ∑ r, M.routePrice p r * x r
      = ∑ r, ∑ l ∈ M.route r, p l * x r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [routePrice, Finset.sum_mul]
    _ = ∑ r, ∑ l : L, if l ∈ M.route r then p l * x r else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_filter]
          congr 1
          ext l
          simp
    _ = ∑ l : L, ∑ r : R, if l ∈ M.route r then p l * x r else 0 := Finset.sum_comm
    _ = ∑ l : L, ∑ r ∈ Finset.univ.filter (fun r => l ∈ M.route r), p l * x r := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_filter]
    _ = ∑ l, p l * M.linkLoad x l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [linkLoad, Finset.mul_sum]

private theorem linkLoad_add [Fintype R] [DecidableEq L] (x y : R → ℝ) (l : L) :
    M.linkLoad (fun r => x r + y r) l = M.linkLoad x l + M.linkLoad y l := by
  simp only [linkLoad, Finset.sum_add_distrib]

private theorem linkLoad_smul [Fintype R] [DecidableEq L] (c : ℝ) (x : R → ℝ) (l : L) :
    M.linkLoad (fun r => c * x r) l = c * M.linkLoad x l := by
  simp only [linkLoad, Finset.mul_sum]

private theorem linkLoad_sub [Fintype R] [DecidableEq L] (x y : R → ℝ) (l : L) :
    M.linkLoad (fun r => x r - y r) l = M.linkLoad x l - M.linkLoad y l := by
  simp only [linkLoad, Finset.sum_sub_distrib]

private theorem routePrice_sub (p q : L → ℝ) (r : R) :
    M.routePrice (fun l => p l - q l) r = M.routePrice p r - M.routePrice q r := by
  simp only [routePrice, Finset.sum_sub_distrib]

private theorem routePrice_add (p q : L → ℝ) (r : R) :
    M.routePrice (fun l => p l + q l) r = M.routePrice p r + M.routePrice q r := by
  simp only [routePrice, Finset.sum_add_distrib]

private theorem routePrice_smul (c : ℝ) (p : L → ℝ) (r : R) :
    M.routePrice (fun l => c * p l) r = c * M.routePrice p r := by
  simp only [routePrice, Finset.mul_sum]

/-- **First Welfare Theorem for multi-link shadow pricing** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.1), (22.3)–(22.7), pp. 573–574): if `(x, p)` is feasible with nonnegative link prices
satisfying complementary slackness and each source `r` solves its price-taking problem
`max_{t ≥ 0} (U_r(t) - q_r t)` at `x_r`, then `x` maximizes aggregate social welfare (without
assuming concavity or differentiability). -/
theorem isSocialOptimum_of_priceTaking [Fintype R] [Finite L] [DecidableEq L]
    {x : R → ℝ} {p : L → ℝ} (hx : M.IsFeasible x) (hp : ∀ l, 0 ≤ p l)
    (hcs : ∀ l, p l * (M.linkLoad x l - M.capacity l) = 0)
    (hpt : ∀ r (t : ℝ), 0 ≤ t →
      M.utility r t - M.routePrice p r * t ≤ M.utility r (x r) - M.routePrice p r * x r) :
    M.IsSocialOptimum x := by
  let : Fintype L := Fintype.ofFinite L
  refine ⟨hx, fun y hy => ?_⟩
  have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hpt r (y r) (hy.1 r)
  simp only [Finset.sum_sub_distrib] at hsum
  rw [M.sum_routePrice_mul_eq_sum_price_mul_linkLoad p y,
    M.sum_routePrice_mul_eq_sum_price_mul_linkLoad p x] at hsum
  have hcap : ∑ l, p l * M.linkLoad y l ≤ ∑ l, p l * M.linkLoad x l := by
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 : p l * M.linkLoad y l ≤ p l * M.capacity l :=
      mul_le_mul_of_nonneg_left (hy.2 l) (hp l)
    have h2 : p l * M.linkLoad x l = p l * M.capacity l := by linarith [hcs l]
    linarith
  change ∑ r, M.utility r (y r) ≤ ∑ r, M.utility r (x r)
  linarith

/-- **Price-taking decentralization** ([OzdaglarSrikant2007], §22.1, Eqs. (22.6)–(22.7),
pp. 573–574): at any KKT pair `(x, p)` for concave utilities differentiable on `[0, ∞)`, each
source `r` maximizes its price-taking net utility `U_r(t) - q_r t` over `t ≥ 0` at `t = x_r`. -/
theorem IsKKT.priceTaking_optimal [Fintype R] [DecidableEq L] {M : NetworkUtilityModel R L}
    {x : R → ℝ} {p : L → ℝ} (hkkt : M.IsKKT x p)
    (hconc : ∀ r, ConcaveOn ℝ (Ici 0) (M.utility r))
    (hdiff : ∀ r, DifferentiableOn ℝ (M.utility r) (Ici 0))
    (r : R) {t : ℝ} (ht : 0 ≤ t) :
    M.utility r t - M.routePrice p r * t ≤ M.utility r (x r) - M.routePrice p r * x r := by
  have htan := (hconc r).le_add_mul_of_hasDerivWithinAt (hkkt.feasible.1 r) ht
    ((hdiff r (x r) (hkkt.feasible.1 r)).hasDerivWithinAt)
  have hprod : (derivWithin (M.utility r) (Ici 0) (x r) - M.routePrice p r) * (t - x r) ≤ 0 := by
    rcases eq_or_lt_of_le (hkkt.feasible.1 r) with hx0 | hxpos
    · rw [← hx0, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hx0 ▸ hkkt.deriv_le r)) ht
    · rw [hkkt.deriv_eq_of_pos r hxpos, sub_self, zero_mul]
  linarith

/-- **KKT sufficiency** ([OzdaglarSrikant2007], §22.1, Eqs. (22.1)–(22.5), p. 573): every KKT pair
`(x, p)` for concave differentiable utilities is socially optimal. -/
theorem IsKKT.isSocialOptimum [Fintype R] [Finite L] [DecidableEq L] {M : NetworkUtilityModel R L}
    {x : R → ℝ} {p : L → ℝ} (hkkt : M.IsKKT x p)
    (hconc : ∀ r, ConcaveOn ℝ (Ici 0) (M.utility r))
    (hdiff : ∀ r, DifferentiableOn ℝ (M.utility r) (Ici 0)) :
    M.IsSocialOptimum x :=
  M.isSocialOptimum_of_priceTaking hkkt.feasible hkkt.price_nonneg hkkt.comp_slack
    fun r _ ht => hkkt.priceTaking_optimal hconc hdiff r ht

/-- Core Farkas' lemma step for polyhedral KKT multipliers on `{x ≥ 0 | R x ≤ c}`: if every
feasible first-order direction `d` has nonpositive directional derivative `∑_r g_r d_r ≤ 0`, then
nonnegative link prices `p` exist satisfying complementary slackness and `g_r ≤ q_r` (with equality
whenever `x_r > 0`). -/
private theorem exists_prices_of_no_improving_dir [Fintype R] [Finite L] [DecidableEq L]
    {x g : R → ℝ}
    (hno : ∀ d : R → ℝ,
      (∀ r, x r = 0 → 0 ≤ d r) →
      (∀ l, M.linkLoad x l = M.capacity l → M.linkLoad d l ≤ 0) →
      ∑ r, g r * d r ≤ 0) :
    ∃ p : L → ℝ, (∀ l, 0 ≤ p l) ∧
      (∀ l, p l * (M.linkLoad x l - M.capacity l) = 0) ∧
      (∀ r, g r ≤ M.routePrice p r) ∧
      (∀ r, 0 < x r → g r = M.routePrice p r) := by
  classical
  let : Fintype L := Fintype.ofFinite L
  let A : Matrix R (L ⊕ R) ℝ := Matrix.of fun r j =>
    match j with
    | Sum.inl l => if l ∈ M.route r ∧ M.linkLoad x l = M.capacity l then 1 else 0
    | Sum.inr r' => if r' = r ∧ x r = 0 then -1 else 0
  have hfarkas : ∀ y : R → ℝ, 0 ≤ y ᵥ* A → 0 ≤ y ⬝ᵥ g := by
    intro y hy
    have hd_nonneg : ∀ r, x r = 0 → 0 ≤ -y r := by
      intro r hr0
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inr r) := hy (Sum.inr r)
      have hcalc : (y ᵥ* A) (Sum.inr r) = -y r := by
        simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply]
        rw [Finset.sum_eq_single r]
        · simp [hr0]
        · intro r' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ r) h
      rw [hcalc] at h1
      exact h1
    have hd_cap : ∀ l, M.linkLoad x l = M.capacity l → M.linkLoad (fun r => -y r) l ≤ 0 := by
      intro l hl
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inl l) := hy (Sum.inl l)
      have hcalc : (y ᵥ* A) (Sum.inl l) = M.linkLoad y l := by
        simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, hl, and_true]
        rw [linkLoad, Finset.sum_filter]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hmem : l ∈ M.route r <;> simp [hmem]
      rw [hcalc] at h1
      have hneg : M.linkLoad (fun r => -y r) l = -M.linkLoad y l := by
        simp only [linkLoad, Finset.sum_neg_distrib]
      linarith
    have hdir := hno (fun r => -y r) hd_nonneg hd_cap
    have hdot : y ⬝ᵥ g = -(∑ r, g r * (-y r)) := by
      simp only [dotProduct, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    linarith
  obtain ⟨u, hu0, hAu⟩ := (Matrix.exists_nonneg_mulVec_eq_iff A g).mpr hfarkas
  let p : L → ℝ := fun l => if M.linkLoad x l = M.capacity l then u (Sum.inl l) else 0
  have hp0 : ∀ l, 0 ≤ p l := fun l => by
    dsimp only [p]; split_ifs
    · exact hu0 (Sum.inl l)
    · exact le_rfl
  have hcs : ∀ l, p l * (M.linkLoad x l - M.capacity l) = 0 := fun l => by
    dsimp only [p]; split_ifs with hl
    · rw [hl, sub_self, mul_zero]
    · rw [zero_mul]
  have hrow : ∀ r, M.routePrice p r - (if x r = 0 then u (Sum.inr r) else 0) = g r := by
    intro r
    have h1 := congrFun hAu r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply] at h1
    have hL : (∑ l : L, (if l ∈ M.route r ∧ M.linkLoad x l = M.capacity l then (1 : ℝ) else 0) *
        u (Sum.inl l)) = M.routePrice p r := by
      have hfilt : M.routePrice p r = ∑ l : L, if l ∈ M.route r then p l else 0 := by
        rw [routePrice, ← Finset.sum_filter (s := Finset.univ) (p := fun l => l ∈ M.route r)
          (f := p)]
        congr 1
        ext l
        simp
      rw [hfilt]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [p]
      by_cases h1l : l ∈ M.route r <;> by_cases h2l : M.linkLoad x l = M.capacity l <;>
        simp [h1l, h2l]
    have hR : (∑ r' : R, (if r' = r ∧ x r = 0 then (-1 : ℝ) else 0) * u (Sum.inr r')) =
        -(if x r = 0 then u (Sum.inr r) else 0) := by
      rw [Finset.sum_eq_single r]
      · by_cases hr0 : x r = 0 <;> simp [hr0]
      · intro r' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ r) h
    rw [hL, hR] at h1
    linarith
  refine ⟨p, hp0, hcs, fun r => ?_, fun r hr => ?_⟩
  · have h1 := hrow r
    by_cases hr0 : x r = 0
    · simp only [hr0, ↓reduceIte] at h1
      have hu_r : 0 ≤ u (Sum.inr r) := hu0 (Sum.inr r)
      linarith
    · simp only [hr0, ↓reduceIte, sub_zero] at h1
      exact h1.ge
  · have h1 := hrow r
    simp only [hr.ne', ↓reduceIte, sub_zero] at h1
    exact h1.symm

private theorem eventually_isFeasible_add_mul [Fintype R] [Finite L] [DecidableEq L]
    {x d : R → ℝ} (hx : M.IsFeasible x) (hd_r : ∀ r, x r = 0 → 0 ≤ d r)
    (hd_l : ∀ l, M.linkLoad x l = M.capacity l → M.linkLoad d l ≤ 0) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), M.IsFeasible (fun r => x r + t * d r) := by
  have h1 : ∀ r : R, ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ x r + t * d r :=
    fun r => eventually_add_mul_nonneg_nhdsGE (hx.1 r) (hd_r r)
  have h2 : ∀ l : L, ∀ᶠ t in 𝓝[≥] (0 : ℝ),
      M.linkLoad (fun r => x r + t * d r) l ≤ M.capacity l := fun l =>
    (eventually_add_mul_le_nhdsGE (hx.2 l) (hd_l l)).mono fun t ht => by
      rwa [M.linkLoad_add, M.linkLoad_smul]
  filter_upwards [eventually_all.mpr h1, eventually_all.mpr h2] with t ht1 ht2
  exact ⟨ht1, ht2⟩

/-- **KKT necessity** ([OzdaglarSrikant2007], §22.1, Eqs. (22.2)–(22.5), p. 573): every socially
optimal rate vector `x` for utilities differentiable on `[0, ∞)` admits nonnegative link Lagrange
multipliers `p` satisfying `M.IsKKT x p`. -/
theorem IsSocialOptimum.exists_isKKT [Fintype R] [Finite L] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x : R → ℝ} (hopt : M.IsSocialOptimum x)
    (hdiff : ∀ r, DifferentiableOn ℝ (M.utility r) (Ici 0)) :
    ∃ p : L → ℝ, M.IsKKT x p := by
  have hno : ∀ d : R → ℝ,
      (∀ r, x r = 0 → 0 ≤ d r) →
      (∀ l, M.linkLoad x l = M.capacity l → M.linkLoad d l ≤ 0) →
      ∑ r, derivWithin (M.utility r) (Ici 0) (x r) * d r ≤ 0 := by
    intro d hd_r hd_l
    have hfeas_ev := M.eventually_isFeasible_add_mul hopt.1 hd_r hd_l
    have hmax_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        M.welfare (fun r => x r + t * d r) ≤ M.welfare (fun r => x r + 0 * d r) :=
      hfeas_ev.mono fun t ht => by simpa only [zero_mul, add_zero] using hopt.2 _ ht
    have hderiv_r : ∀ r : R, HasDerivWithinAt (fun t => M.utility r (x r + t * d r))
        (derivWithin (M.utility r) (Ici 0) (x r) * d r) (Ici 0) 0 := fun r =>
      hasDerivWithinAt_comp_add_mul ((hdiff r (x r) (hopt.1.1 r)).hasDerivWithinAt)
        (hfeas_ev.mono fun t ht => ht.1 r)
    have hderiv_sum : HasDerivWithinAt (fun t => M.welfare (fun r => x r + t * d r))
        (∑ r, derivWithin (M.utility r) (Ici 0) (x r) * d r) (Ici 0) 0 :=
      HasDerivWithinAt.fun_sum fun r _ => hderiv_r r
    exact hasDerivWithinAt_nonpos_of_eventually_le hderiv_sum hmax_ev
  obtain ⟨p, hp0, hcs, hle, heq⟩ := M.exists_prices_of_no_improving_dir hno
  exact ⟨p, hopt.1, hp0, hcs, hle, heq⟩

/-- **KKT characterization of multi-link NUM** ([OzdaglarSrikant2007], §22.1, Eqs. (22.1)–(22.5),
p. 573): for concave utilities differentiable on `[0, ∞)`, a rate vector `x` is socially optimal
if and only if it admits nonnegative link Lagrange multipliers `p` satisfying `M.IsKKT x p`. -/
theorem isSocialOptimum_iff_exists_isKKT [Fintype R] [Finite L] [DecidableEq L]
    (hconc : ∀ r, ConcaveOn ℝ (Ici 0) (M.utility r))
    (hdiff : ∀ r, DifferentiableOn ℝ (M.utility r) (Ici 0)) {x : R → ℝ} :
    M.IsSocialOptimum x ↔ ∃ p : L → ℝ, M.IsKKT x p :=
  ⟨fun hopt => hopt.exists_isKKT hdiff, fun ⟨_, hkkt⟩ => hkkt.isSocialOptimum hconc hdiff⟩

private theorem isCompact_isFeasible [Fintype R] [DecidableEq L]
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 ≤ M.capacity l) :
    IsCompact {x : R → ℝ | M.IsFeasible x} := by
  have hbound : ∀ x, M.IsFeasible x → ∀ r, x r ≤ ∑ l ∈ M.route r, M.capacity l := by
    intro x hx r
    obtain ⟨l, hl⟩ := hroute r
    have h1 : x r ≤ M.linkLoad x l :=
      Finset.single_le_sum (f := x) (fun r' _ => hx.1 r')
        (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hl⟩)
    have h2 : M.capacity l ≤ ∑ l' ∈ M.route r, M.capacity l' :=
      Finset.single_le_sum (fun l' _ => hcap l') hl
    exact (h1.trans (hx.2 l)).trans h2
  refine (isCompact_univ_pi fun r : R => isCompact_Icc (a := (0 : ℝ))
    (b := ∑ l ∈ M.route r, M.capacity l)).of_isClosed_subset ?_
    (fun x hx r _ => ⟨hx.1 r, hbound x hx r⟩)
  have h1 : IsClosed {x : R → ℝ | ∀ r, 0 ≤ x r} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
  have h2 : IsClosed {x : R → ℝ | ∀ l, M.linkLoad x l ≤ M.capacity l} := by
    simpa only [Set.ofPred_forall, linkLoad] using isClosed_iInter fun l =>
      isClosed_le (continuous_finsetSum _ fun r _ => continuous_apply r) continuous_const
  exact h1.inter h2

/-- Existence of a socially optimal rate allocation when every source uses at least one link, link
capacities are nonnegative, and utilities are continuous on `[0, ∞)`. -/
theorem exists_isSocialOptimum [Fintype R] [DecidableEq L]
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 ≤ M.capacity l)
    (hcont : ∀ r, ContinuousOn (M.utility r) (Ici 0)) :
    ∃ x, M.IsSocialOptimum x := by
  have hne : ({x : R → ℝ | M.IsFeasible x}).Nonempty :=
    ⟨0, fun _ => le_rfl, fun l => by simp [linkLoad, hcap l]⟩
  have hcont_w : ContinuousOn M.welfare {x : R → ℝ | M.IsFeasible x} :=
    continuousOn_finsetSum _ fun r _ =>
      (hcont r).comp (continuous_apply r).continuousOn fun x hx => hx.1 r
  obtain ⟨x, hx, hmax⟩ := (M.isCompact_isFeasible hroute hcap).exists_isMaxOn hne hcont_w
  exact ⟨x, hx, fun y hy => hmax hy⟩

/-- Existence of a KKT optimal primal-dual pair `(x, p)` solving multi-link NUM
([OzdaglarSrikant2007], §22.1, Eqs. (22.1)–(22.5), p. 573). -/
theorem exists_isKKT [Fintype R] [Finite L] [DecidableEq L]
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 ≤ M.capacity l)
    (hdiff : ∀ r, DifferentiableOn ℝ (M.utility r) (Ici 0)) :
    ∃ x p, M.IsKKT x p ∧ M.IsSocialOptimum x := by
  obtain ⟨x, hopt⟩ := M.exists_isSocialOptimum hroute hcap fun r => (hdiff r).continuousOn
  obtain ⟨p, hkkt⟩ := hopt.exists_isKKT hdiff
  exact ⟨x, p, hkkt, hopt⟩

/-- **Uniqueness of the socially optimal rate vector** ([OzdaglarSrikant2007], §22.1, p. 573):
when every utility function is strictly concave on `[0, ∞)`, any two social optima coincide. -/
theorem IsSocialOptimum.eq_of_strictConcaveOn [Fintype R] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x₁ x₂ : R → ℝ}
    (h₁ : M.IsSocialOptimum x₁) (h₂ : M.IsSocialOptimum x₂)
    (hstrict : ∀ r, StrictConcaveOn ℝ (Ici 0) (M.utility r)) :
    x₁ = x₂ := by
  by_contra hne
  obtain ⟨r₀, hr₀⟩ : ∃ r, x₁ r ≠ x₂ r := Function.ne_iff.mp hne
  let m : R → ℝ := fun r => (1 / 2 : ℝ) * x₁ r + (1 / 2 : ℝ) * x₂ r
  have hm : M.IsFeasible m := by
    refine ⟨fun r => by dsimp only [m]; linarith [h₁.1.1 r, h₂.1.1 r], fun l => ?_⟩
    have hload : M.linkLoad m l =
        (1 / 2 : ℝ) * M.linkLoad x₁ l + (1 / 2 : ℝ) * M.linkLoad x₂ l := by
      simp only [m, M.linkLoad_add, M.linkLoad_smul]
    linarith [h₁.1.2 l, h₂.1.2 l]
  have hle : ∀ r, (1 / 2 : ℝ) * M.utility r (x₁ r) + (1 / 2 : ℝ) * M.utility r (x₂ r) ≤
      M.utility r (m r) := fun r =>
    (hstrict r).concaveOn.2 (h₁.1.1 r) (h₂.1.1 r) (by norm_num) (by norm_num) (by norm_num)
  have hlt : (1 / 2 : ℝ) * M.utility r₀ (x₁ r₀) + (1 / 2 : ℝ) * M.utility r₀ (x₂ r₀) <
      M.utility r₀ (m r₀) :=
    (hstrict r₀).2 (h₁.1.1 r₀) (h₂.1.1 r₀) hr₀ (by norm_num) (by norm_num) (by norm_num)
  have hsum := Finset.sum_lt_sum (fun r _ => hle r) ⟨r₀, Finset.mem_univ r₀, hlt⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hopt1 := h₁.2 m hm
  have hopt2 := h₂.2 m hm
  change ∑ r, M.utility r (m r) ≤ ∑ r, M.utility r (x₁ r) at hopt1
  change ∑ r, M.utility r (m r) ≤ ∑ r, M.utility r (x₂ r) at hopt2
  linarith

/-- **Uniqueness of link Lagrange multipliers** ([OzdaglarSrikant2007], §22.1, p. 575): when the
routing matrix has full row rank (`Function.Injective M.routePrice`), any two KKT multiplier
vectors at a strictly positive optimal rate vector `x > 0` are equal. -/
theorem IsKKT.price_eq_of_injective_routePrice [Fintype R] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x : R → ℝ} {p₁ p₂ : L → ℝ}
    (h₁ : M.IsKKT x p₁) (h₂ : M.IsKKT x p₂) (hx : ∀ r, 0 < x r)
    (hinj : Function.Injective M.routePrice) :
    p₁ = p₂ :=
  hinj <| funext fun r =>
    (h₁.deriv_eq_of_pos r (hx r)).symm.trans (h₂.deriv_eq_of_pos r (hx r))

/-! ### Part 2: Weighted Proportional Fairness and Myopic Bid Alignment (Eqs. (22.8)–(22.12)) -/

/-- A strictly positive feasible rate vector `x` is **weighted proportionally fair** for positive
bids `w` if `∑_r w_r (y_r - x_r) / x_r ≤ 0` for every feasible rate vector `y`
([OzdaglarSrikant2007], §22.1, p. 574; [Vazirani2007], §5.13, p. 125; [Kelly1997]). -/
@[expose] def IsWeightedPropFair [Fintype R] [DecidableEq L] (w x : R → ℝ) : Prop :=
  M.IsFeasible x ∧ (∀ r, 0 < x r) ∧
    ∀ y, M.IsFeasible y → ∑ r, w r * (y r - x r) / x r ≤ 0

/-- KKT conditions for the weighted proportionally fair optimization problem `max ∑_r w_r log x_r`
([OzdaglarSrikant2007], §22.1, Eqs. (22.9)–(22.12), p. 574). -/
structure IsWeightedPropFairKKT [Fintype R] [DecidableEq L]
    (w x : R → ℝ) (p : L → ℝ) : Prop where
  /-- Primal feasibility (Eqs. (22.11)–(22.12)). -/
  feasible : M.IsFeasible x
  /-- Strict positivity of equilibrium rates `x* > 0` (so `w_r / x*_r` is finite). -/
  rate_pos : ∀ r, 0 < x r
  /-- Dual nonnegativity: `p* ≥ 0` (Eq. (22.12)). -/
  price_nonneg : ∀ l, 0 ≤ p l
  /-- Complementary slackness: `p*_l (y*_l - c_l) = 0` for every link `l` (Eq. (22.10)). -/
  comp_slack : ∀ l, p l * (M.linkLoad x l - M.capacity l) = 0
  /-- Rate-price equation `w_r / x*_r = ∑_{l ∈ r} p*_l` (Eq. (22.9)). -/
  rate_eq : ∀ r, w r / x r = M.routePrice p r

/-- Uniqueness of the weighted proportionally fair allocation for positive bids `w > 0`. -/
theorem IsWeightedPropFair.eq_of_isWeightedPropFair [Fintype R] [DecidableEq L]
    {M : NetworkUtilityModel R L} {w x₁ x₂ : R → ℝ} (hw : ∀ r, 0 < w r)
    (h₁ : M.IsWeightedPropFair w x₁) (h₂ : M.IsWeightedPropFair w x₂) :
    x₁ = x₂ := by
  have hsum_le : ∑ r, w r * (x₂ r - x₁ r) ^ 2 / (x₁ r * x₂ r) ≤ 0 := by
    have heq : ∀ r, w r * (x₂ r - x₁ r) ^ 2 / (x₁ r * x₂ r) =
        w r * (x₂ r - x₁ r) / x₁ r + w r * (x₁ r - x₂ r) / x₂ r := fun r => by
      have h1 : x₁ r ≠ 0 := (h₁.2.1 r).ne'
      have h2 : x₂ r ≠ 0 := (h₂.2.1 r).ne'
      field_simp [h1, h2]
      ring
    simp_rw [heq, Finset.sum_add_distrib]
    linarith [h₁.2.2 x₂ h₂.1, h₂.2.2 x₁ h₁.1]
  have hterm_nonneg : ∀ r ∈ (Finset.univ : Finset R),
      0 ≤ w r * (x₂ r - x₁ r) ^ 2 / (x₁ r * x₂ r) := fun r _ =>
    div_nonneg (mul_nonneg (hw r).le (sq_nonneg _)) (mul_nonneg (h₁.2.1 r).le (h₂.2.1 r).le)
  have hsum_zero : ∑ r, w r * (x₂ r - x₁ r) ^ 2 / (x₁ r * x₂ r) = 0 :=
    le_antisymm hsum_le (Finset.sum_nonneg hterm_nonneg)
  funext r
  have hr := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_zero r (Finset.mem_univ r)
  have hden : 0 < x₁ r * x₂ r := mul_pos (h₁.2.1 r) (h₂.2.1 r)
  have hnum : w r * (x₂ r - x₁ r) ^ 2 = 0 := (div_eq_zero_iff.mp hr).resolve_right hden.ne'
  have hsq : (x₂ r - x₁ r) ^ 2 = 0 := (mul_eq_zero.mp hnum).resolve_left (hw r).ne'
  linarith [sq_eq_zero_iff.mp hsq]

/-- Equivalence between weighted proportional fairness (`∑_r w_r (y_r - x_r) / x_r ≤ 0`) and
maximizing `∑_r w_r log x_r` over positive feasible rate vectors ([OzdaglarSrikant2007], §22.1,
Eq. (22.8), p. 574; [Vazirani2007], §5.13, p. 125). -/
theorem isWeightedPropFair_iff_max_log [Fintype R] [DecidableEq L]
    {w x : R → ℝ} (hw : ∀ r, 0 < w r) :
    M.IsWeightedPropFair w x ↔
      M.IsFeasible x ∧ (∀ r, 0 < x r) ∧
        ∀ y, M.IsFeasible y → (∀ r, 0 < y r) →
          ∑ r, w r * Real.log (y r) ≤ ∑ r, w r * Real.log (x r) := by
  constructor
  · rintro ⟨hx, hxpos, hpf⟩
    refine ⟨hx, hxpos, fun y hy hypos => ?_⟩
    have hlog : ∀ r, w r * Real.log (y r) ≤
        w r * Real.log (x r) + w r * (y r - x r) / x r := fun r => by
      have h1 := Real.log_le_sub_one_of_pos (div_pos (hypos r) (hxpos r))
      rw [Real.log_div (hypos r).ne' (hxpos r).ne'] at h1
      have h2 : y r / x r - 1 = (y r - x r) / x r := by field_simp [(hxpos r).ne']
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 (hw r).le
      linarith [show w r * ((y r - x r) / x r) = w r * (y r - x r) / x r by ring]
    have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hlog r
    rw [Finset.sum_add_distrib] at hsum
    linarith [hpf y hy]
  · rintro ⟨hx, hxpos, hmax⟩
    refine ⟨hx, hxpos, fun y hy => ?_⟩
    let φ : ℝ → ℝ := fun t => ∑ r, w r * Real.log ((1 - t) * x r + t * y r)
    have hderiv_r : ∀ r : R, HasDerivWithinAt
        (fun t => w r * Real.log ((1 - t) * x r + t * y r))
        (w r * (y r - x r) / x r) (Ici 0) 0 := fun r => by
      have haff : HasDerivAt (fun t : ℝ => (1 - t) * x r + t * y r) (y r - x r) 0 := by
        have h1 : (fun t : ℝ => (1 - t) * x r + t * y r) = fun t => x r + t * (y r - x r) := by
          ext t; ring
        rw [h1]
        simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (y r - x r)).const_add (x r)
      have hval : (1 - (0 : ℝ)) * x r + 0 * y r = x r := by ring
      have hlog : HasDerivAt Real.log (x r)⁻¹ ((1 - (0 : ℝ)) * x r + 0 * y r) := by
        rw [hval]
        exact Real.hasDerivAt_log (hxpos r).ne'
      have hcomp := (hlog.comp (0 : ℝ) haff).const_mul (w r)
      have hder_eq : w r * ((x r)⁻¹ * (y r - x r)) = w r * (y r - x r) / x r := by
        field_simp [(hxpos r).ne']
      rw [← hder_eq]
      exact hcomp.hasDerivWithinAt
    have hderiv : HasDerivWithinAt φ (∑ r, w r * (y r - x r) / x r) (Ici 0) 0 :=
      HasDerivWithinAt.fun_sum fun r _ => hderiv_r r
    have hle_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ), φ t ≤ φ 0 := by
      filter_upwards [Ico_mem_nhdsGE (zero_lt_one : (0 : ℝ) < 1)] with t ht
      let z : R → ℝ := fun r => (1 - t) * x r + t * y r
      have hz_pos : ∀ r, 0 < z r := fun r => by
        dsimp only [z]
        have h1 : 0 < (1 - t) * x r := mul_pos (sub_pos.mpr ht.2) (hxpos r)
        have h2 : 0 ≤ t * y r := mul_nonneg ht.1 (hy.1 r)
        linarith
      have hz_feas : M.IsFeasible z := by
        refine ⟨fun r => (hz_pos r).le, fun l => ?_⟩
        have hload : M.linkLoad z l = (1 - t) * M.linkLoad x l + t * M.linkLoad y l := by
          simp only [z, M.linkLoad_add, M.linkLoad_smul]
        rw [hload]
        nlinarith [ht.1, ht.2, hx.2 l, hy.2 l]
      simpa only [φ, sub_zero, one_mul, zero_mul, add_zero] using hmax z hz_feas hz_pos
    exact hasDerivWithinAt_nonpos_of_eventually_le hderiv hle_ev

/-- **KKT characterization of weighted proportional fairness** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.8)–(22.12), p. 574): `x` is weighted proportionally fair for bids `w` if and only if there
exist link prices `p` satisfying Eqs. (22.9)–(22.12). -/
theorem isWeightedPropFair_iff_exists_kkt [Fintype R] [Finite L] [DecidableEq L]
    {w x : R → ℝ} :
    M.IsWeightedPropFair w x ↔ ∃ p : L → ℝ, M.IsWeightedPropFairKKT w x p := by
  let : Fintype L := Fintype.ofFinite L
  constructor
  · intro hpf
    have hno : ∀ d : R → ℝ,
        (∀ r, x r = 0 → 0 ≤ d r) →
        (∀ l, M.linkLoad x l = M.capacity l → M.linkLoad d l ≤ 0) →
        ∑ r, (w r / x r) * d r ≤ 0 := by
      intro d hd_r hd_l
      have hfeas_ev := M.eventually_isFeasible_add_mul hpf.1 hd_r hd_l
      obtain ⟨t, ht_feas, ht_pos⟩ :=
        ((hfeas_ev.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)).and
          self_mem_nhdsWithin).exists
      have hpf_t := hpf.2.2 (fun r => x r + t * d r) ht_feas
      have hfactor : ∑ r, w r * (x r + t * d r - x r) / x r =
          t * ∑ r, (w r / x r) * d r := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [hfactor] at hpf_t
      exact nonpos_of_mul_nonpos_right hpf_t (mem_Ioi.mp ht_pos)
    obtain ⟨p, hp0, hcs, _, heq⟩ := M.exists_prices_of_no_improving_dir hno
    exact ⟨p, hpf.1, hpf.2.1, hp0, hcs, fun r => heq r (hpf.2.1 r)⟩
  · rintro ⟨p, hkkt⟩
    refine ⟨hkkt.feasible, hkkt.rate_pos, fun y hy => ?_⟩
    have heq : ∑ r, w r * (y r - x r) / x r = ∑ r, M.routePrice p r * (y r - x r) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← hkkt.rate_eq r]
      ring
    rw [heq]
    have hdiff : ∑ r, M.routePrice p r * (y r - x r) =
        ∑ l, p l * (M.linkLoad y l - M.linkLoad x l) := by
      simpa only [M.linkLoad_sub] using
        M.sum_routePrice_mul_eq_sum_price_mul_linkLoad p (fun r => y r - x r)
    rw [hdiff]
    refine Finset.sum_nonpos fun l _ => ?_
    have h1 : p l * M.linkLoad y l ≤ p l * M.capacity l :=
      mul_le_mul_of_nonneg_left (hy.2 l) (hkkt.price_nonneg l)
    have h2 : p l * M.linkLoad x l = p l * M.capacity l := by linarith [hkkt.comp_slack l]
    linarith

/-- **Existence and uniqueness of weighted proportionally fair allocation** ([OzdaglarSrikant2007],
§22.1, Eqs. (22.8)–(22.12), p. 574): for positive bids `w`, positive link capacities, and nonempty
routes, there is a unique weighted proportionally fair rate vector `x*`, together with link
Lagrange multipliers `p*` satisfying Eqs. (22.9)–(22.12). -/
theorem existsUnique_isWeightedPropFair [Fintype R] [Finite L] [DecidableEq L]
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 < M.capacity l)
    {w : R → ℝ} (hw : ∀ r, 0 < w r) :
    (∃! x, M.IsWeightedPropFair w x) ∧
      ∃ x p, M.IsWeightedPropFair w x ∧ M.IsWeightedPropFairKKT w x p := by
  classical
  let : Fintype L := Fintype.ofFinite L
  have hex : ∃ x, M.IsWeightedPropFair w x := by
    by_cases hR : Nonempty R
    · have : Nonempty R := hR
      obtain ⟨r₀⟩ := hR
      obtain ⟨l₀, _⟩ := hroute r₀
      have hL : (Finset.univ : Finset L).Nonempty := ⟨l₀, Finset.mem_univ l₀⟩
      have hRne : (Finset.univ : Finset R).Nonempty := ⟨r₀, Finset.mem_univ r₀⟩
      let cMin : ℝ := Finset.univ.inf' hL M.capacity
      let cMax : ℝ := Finset.univ.sup' hL M.capacity
      have hcMin_pos : 0 < cMin := (Finset.lt_inf'_iff hL).mpr fun l _ => hcap l
      have hcMax_pos : 0 < cMax :=
        lt_of_lt_of_le (hcap l₀) (Finset.le_sup' M.capacity (Finset.mem_univ l₀))
      have hcard_pos : (0 : ℝ) < (Fintype.card R : ℝ) :=
        Nat.cast_pos.mpr Fintype.card_pos
      let x₀ : R → ℝ := fun _ => cMin / (Fintype.card R : ℝ)
      have hx₀_pos : ∀ r, 0 < x₀ r := fun _ => div_pos hcMin_pos hcard_pos
      have hx₀_feas : M.IsFeasible x₀ := by
        refine ⟨fun r => (hx₀_pos r).le, fun l => ?_⟩
        have h1 : M.linkLoad x₀ l ≤ ∑ _r : R, cMin / (Fintype.card R : ℝ) := by
          rw [linkLoad]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => (div_pos hcMin_pos hcard_pos).le
        have h2 : ∑ _r : R, cMin / (Fintype.card R : ℝ) = cMin := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_div_cancel₀ _ hcard_pos.ne']
        exact (h1.trans h2.le).trans (Finset.inf'_le M.capacity (Finset.mem_univ l))
      have hfeas_le_cMax : ∀ x, M.IsFeasible x → ∀ r, x r ≤ cMax := fun x hx r => by
        obtain ⟨l, hl⟩ := hroute r
        have h1 : x r ≤ M.linkLoad x l :=
          Finset.single_le_sum (f := x) (fun r' _ => hx.1 r')
            (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hl⟩)
        exact (h1.trans (hx.2 l)).trans (Finset.le_sup' M.capacity (Finset.mem_univ l))
      let wMin : ℝ := Finset.univ.inf' hRne w
      have hwMin_pos : 0 < wMin := (Finset.lt_inf'_iff hRne).mpr fun r _ => hw r
      let B : ℝ := ∑ r, w r * (|Real.log cMax| + |Real.log (x₀ r)|) + 1
      have hB_pos : 0 < B := by
        have hsum0 : 0 ≤ ∑ r, w r * (|Real.log cMax| + |Real.log (x₀ r)|) :=
          Finset.sum_nonneg fun r _ => mul_nonneg (hw r).le (by positivity)
        linarith
      let ε : ℝ := min (cMin / (Fintype.card R : ℝ)) (Real.exp (-(B / wMin)))
      have hε_pos : 0 < ε := lt_min (div_pos hcMin_pos hcard_pos) (Real.exp_pos _)
      have hε_le_x₀ : ∀ r, ε ≤ x₀ r := fun _ => min_le_left _ _
      have hlog_ε : Real.log ε ≤ -(B / wMin) := by
        calc Real.log ε ≤ Real.log (Real.exp (-(B / wMin))) :=
              Real.log_le_log hε_pos (min_le_right _ _)
          _ = -(B / wMin) := Real.log_exp _
      let K : Set (R → ℝ) := {x | M.IsFeasible x ∧ ∀ r, ε ≤ x r}
      have hK_compact : IsCompact K := by
        have hclosed : IsClosed {x : R → ℝ | ∀ r, ε ≤ x r} := by
          simpa only [Set.ofPred_forall] using
            isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
        exact (M.isCompact_isFeasible hroute fun l => (hcap l).le).inter_right hclosed
      have hK_ne : K.Nonempty := ⟨x₀, hx₀_feas, hε_le_x₀⟩
      have hcont_log : ContinuousOn (fun x : R → ℝ => ∑ r, w r * Real.log (x r)) K :=
        continuousOn_finsetSum _ fun r _ => continuousOn_const.mul <|
          Real.continuousOn_log.comp (continuous_apply r).continuousOn
            fun x hx => ne_of_gt (lt_of_lt_of_le hε_pos (hx.2 r))
      obtain ⟨xStar, hxStar_K, hxStar_max⟩ := hK_compact.exists_isMaxOn hK_ne hcont_log
      refine ⟨xStar, (M.isWeightedPropFair_iff_max_log hw).mpr
        ⟨hxStar_K.1, fun r => lt_of_lt_of_le hε_pos (hxStar_K.2 r), fun y hy hypos => ?_⟩⟩
      by_cases hyK : ∀ r, ε ≤ y r
      · exact hxStar_max ⟨hy, hyK⟩
      · push Not at hyK
        obtain ⟨r₁, hr₁⟩ := hyK
        have hlt_x₀ : ∑ r, w r * Real.log (y r) < ∑ r, w r * Real.log (x₀ r) := by
          have h1 : w r₁ * Real.log (y r₁) ≤ -B := by
            have hly : Real.log (y r₁) ≤ -(B / wMin) :=
              (Real.log_le_log (hypos r₁) hr₁.le).trans hlog_ε
            have hneg_w : w r₁ * (-(B / wMin)) ≤ wMin * (-(B / wMin)) := by
              have hwm : wMin ≤ w r₁ := Finset.inf'_le w (Finset.mem_univ r₁)
              have hdiv : 0 ≤ B / wMin := div_nonneg hB_pos.le hwMin_pos.le
              nlinarith
            have hcancel : wMin * (-(B / wMin)) = -B := by
              field_simp [hwMin_pos.ne']
            exact (mul_le_mul_of_nonneg_left hly (hw r₁).le).trans (hneg_w.trans hcancel.le)
          have h2 : ∑ r ∈ Finset.univ.erase r₁, w r * Real.log (y r) ≤
              ∑ r, w r * |Real.log cMax| := by
            calc ∑ r ∈ Finset.univ.erase r₁, w r * Real.log (y r)
                ≤ ∑ r ∈ Finset.univ.erase r₁, w r * |Real.log cMax| := by
                  refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hw r).le
                  exact (Real.log_le_log (hypos r) (hfeas_le_cMax y hy r)).trans (le_abs_self _)
              _ ≤ ∑ r, w r * |Real.log cMax| :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                    fun r _ _ => mul_nonneg (hw r).le (abs_nonneg _)
          have h3 : -(∑ r, w r * |Real.log (x₀ r)|) ≤ ∑ r, w r * Real.log (x₀ r) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_le_sum fun r _ => ?_
            have := neg_abs_le (Real.log (x₀ r))
            nlinarith [hw r]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₁)]
          have hB_exp : B = ∑ r, w r * |Real.log cMax| + ∑ r, w r * |Real.log (x₀ r)| + 1 := by
            simp only [B, mul_add, Finset.sum_add_distrib]
          linarith
        exact hlt_x₀.le.trans (hxStar_max ⟨hx₀_feas, hε_le_x₀⟩)
    · have : IsEmpty R := not_nonempty_iff.mp hR
      refine ⟨isEmptyElim, ⟨fun r => isEmptyElim r, fun l => by
        simp only [linkLoad, Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
        exact (hcap l).le⟩, fun r => isEmptyElim r, fun _ _ => by simp⟩
  obtain ⟨x, hx⟩ := hex
  obtain ⟨p, hkkt⟩ := M.isWeightedPropFair_iff_exists_kkt.mp hx
  exact ⟨⟨x, hx, fun y hy => hy.eq_of_isWeightedPropFair hw hx⟩, ⟨x, p, hx, hkkt⟩⟩

/-- **Alignment of social optimality with weighted proportional fairness** ([OzdaglarSrikant2007],
§22.1, p. 574): if `(x̂, p̂)` satisfies KKT for general utilities with `x̂ > 0` and positive
marginal utilities, setting `w_r = x̂_r U'_r(x̂_r)` makes `(x̂, p̂)` satisfy Eqs. (22.9)–(22.12)
and makes `x̂` the unique weighted proportionally fair allocation for `w`. -/
theorem IsKKT.isWeightedPropFairKKT_of_myopicBids [Fintype R] [Finite L] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x : R → ℝ} {p : L → ℝ}
    (hkkt : M.IsKKT x p) (hx : ∀ r, 0 < x r)
    (hderiv_pos : ∀ r, 0 < derivWithin (M.utility r) (Ici 0) (x r)) :
    let w : R → ℝ := fun r => x r * derivWithin (M.utility r) (Ici 0) (x r)
    (∀ r, 0 < w r) ∧ M.IsWeightedPropFairKKT w x p ∧ M.IsWeightedPropFair w x := by
  intro w
  have hw : ∀ r, 0 < w r := fun r => mul_pos (hx r) (hderiv_pos r)
  have hwpf_kkt : M.IsWeightedPropFairKKT w x p :=
    ⟨hkkt.feasible, hx, hkkt.price_nonneg, hkkt.comp_slack, fun r => by
      dsimp only [w]
      rw [mul_div_cancel_left₀ _ (hx r).ne']
      exact hkkt.deriv_eq_of_pos r (hx r)⟩
  exact ⟨hw, hwpf_kkt, M.isWeightedPropFair_iff_exists_kkt.mpr ⟨p, hwpf_kkt⟩⟩

/-! ### Part 3: Dual Congestion Control Lyapunov Stability and Convergence (Eqs. (22.13)–(22.15)) -/

/-- Shared route-price lower barrier for any projected excess-demand trajectory with time-varying
service rate `svc t l ≤ M.capacity l` (covering both wireline and wireless models). -/
private theorem routePrice_ge_of_barrier [Fintype R] [DecidableEq L]
    {x : ℝ → R → ℝ} {svc : ℝ → L → ℝ} {p : ℝ → L → ℝ}
    (hroute : ∀ r, (M.route r).Nonempty)
    (hp : ∀ t ∈ Ici (0 : ℝ), (∀ l, 0 ≤ p t l) ∧
      ∀ l, HasDerivWithinAt (fun s => p s l)
        (projDrift (M.linkLoad (x t) l - svc t l) (p t l)) (Ici 0) t)
    (hsvc : ∀ t ∈ Ici (0 : ℝ), ∀ l, svc t l ≤ M.capacity l)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    {r : R} {qMin : ℝ} (hq0 : qMin ≤ M.routePrice (p 0) r)
    (hbarrier : ∀ s ∈ Ici (0 : ℝ), M.routePrice (p s) r < qMin →
      ∀ l ∈ M.route r, M.capacity l < x s r) :
    ∀ t ∈ Ici (0 : ℝ), qMin ≤ M.routePrice (p t) r := by
  intro t ht
  by_contra hlt
  push Not at hlt
  let g : ℝ → ℝ := fun s => M.routePrice (p s) r
  let g' : ℝ → ℝ := fun s =>
    ∑ l ∈ M.route r, projDrift (M.linkLoad (x s) l - svc s l) (p s l)
  have hg_deriv : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' s) (Ici 0) s := fun s hs =>
    HasDerivWithinAt.fun_sum fun l _ => (hp s hs).2 l
  have hg_cont : ContinuousOn g (Icc 0 t) :=
    fun s hs => (hg_deriv s hs.1).continuousWithinAt.mono fun _ hz => hz.1
  let S : Set ℝ := {s ∈ Icc 0 t | qMin ≤ g s}
  have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, ht⟩, hq0⟩
  have hS_bdd : BddAbove S := ⟨t, fun _ hs => hs.1.2⟩
  have hS_closed : IsClosed S :=
    hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  let s₀ : ℝ := sSup S
  have hs₀_mem : s₀ ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  have hs₀_lt : s₀ < t := lt_of_le_of_ne hs₀_mem.1.2 fun heq => by
    have : qMin ≤ g t := heq ▸ hs₀_mem.2
    linarith
  have hcont_sub : ContinuousOn g (Icc s₀ t) :=
    hg_cont.mono (Icc_subset_Icc_left hs₀_mem.1.1)
  have hder_sub : ∀ s ∈ Ioo s₀ t, HasDerivAt g (g' s) s := fun s hs =>
    (hg_deriv s (hs₀_mem.1.1.trans hs.1.le)).hasDerivAt
      (Ici_mem_nhds (lt_of_le_of_lt hs₀_mem.1.1 hs.1))
  obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' hs₀_lt hcont_sub hder_sub
  have hc_lt_qMin : g c < qMin := by
    by_contra hge
    push Not at hge
    have hcS : c ∈ S := ⟨⟨hs₀_mem.1.1.trans hc.1.le, hc.2.le⟩, hge⟩
    linarith [le_csSup hS_bdd hcS, hc.1]
  have hc0 : 0 ≤ c := hs₀_mem.1.1.trans hc.1.le
  have hpos_g' : 0 < g' c := by
    dsimp only [g']
    refine Finset.sum_pos (fun l hl => ?_) (hroute r)
    have hcap_lt : M.capacity l < x c r := hbarrier c hc0 hc_lt_qMin l hl
    have hload_ge : x c r ≤ M.linkLoad (x c) l :=
      Finset.single_le_sum (f := x c) (fun r' _ => hx0 c hc0 r')
        (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hl⟩)
    have hexcess : 0 < M.linkLoad (x c) l - svc c l := by linarith [hsvc c hc0 l]
    exact hexcess.trans_le (le_projDrift _ _)
  have hneg_slope : (g t - g s₀) / (t - s₀) < 0 :=
    div_neg_of_neg_of_pos (by linarith [hs₀_mem.2]) (sub_pos.mpr hs₀_lt)
  linarith

/-- Shared Lipschitz bound for `t ↦ M.routePrice (p t) r` when rates and service rates are
uniformly bounded on `[0, ∞)`. -/
private theorem lipschitz_routePrice_of_bounded [Fintype R] [Finite L] [DecidableEq L]
    {x : ℝ → R → ℝ} {svc : ℝ → L → ℝ} {p : ℝ → L → ℝ}
    (hp : ∀ t ∈ Ici (0 : ℝ), (∀ l, 0 ≤ p t l) ∧
      ∀ l, HasDerivWithinAt (fun s => p s l)
        (projDrift (M.linkLoad (x t) l - svc t l) (p t l)) (Ici 0) t)
    {X : R → ℝ} (hx : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r ∧ x t r ≤ X r)
    (hsvc : ∀ t ∈ Ici (0 : ℝ), ∀ l, 0 ≤ svc t l ∧ svc t l ≤ M.capacity l) :
    ∃ K ≥ 0, ∀ r, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |M.routePrice (p s) r - M.routePrice (p t) r| ≤ K * |s - t| := by
  let : Fintype L := Fintype.ofFinite L
  let B : ℝ := (∑ r : R, max (X r) 0) + ∑ l : L, max (M.capacity l) 0
  have hB0 : 0 ≤ B := add_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)
    (Finset.sum_nonneg fun _ _ => le_max_right _ _)
  have hlink_lip : ∀ l, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |p s l - p t l| ≤ B * |s - t| := by
    intro l s hs t ht
    have hordered : ∀ a ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ), a ≤ b →
        |p b l - p a l| ≤ B * (b - a) := by
      intro a ha b hb hab
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have hcont : ContinuousOn (fun u => p u l) (Icc a b) :=
          fun u hu => ((hp u (ha.trans hu.1)).2 l).continuousWithinAt.mono fun _ hz => ha.trans hz.1
        have hder : ∀ u ∈ Ioo a b, HasDerivAt (fun z => p z l)
            (projDrift (M.linkLoad (x u) l - svc u l) (p u l)) u := fun u hu =>
          ((hp u (ha.trans hu.1.le)).2 l).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt ha hu.1))
        obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hder
        have hc0 : 0 ≤ c := ha.trans hc.1.le
        have hload_nn : 0 ≤ M.linkLoad (x c) l := Finset.sum_nonneg fun r _ => (hx c hc0 r).1
        have hload_le : M.linkLoad (x c) l ≤ ∑ r : R, max (X r) 0 := by
          calc M.linkLoad (x c) l
              ≤ ∑ r ∈ Finset.univ.filter (fun r => l ∈ M.route r), max (X r) 0 :=
                Finset.sum_le_sum fun r _ => (hx c hc0 r).2.trans (le_max_left _ _)
            _ ≤ ∑ r : R, max (X r) 0 :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  fun _ _ _ => le_max_right _ _
        have hsvc_le : svc c l ≤ ∑ l' : L, max (M.capacity l') 0 :=
          (hsvc c hc0 l).2.trans ((le_max_left _ _).trans
            (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ l)))
        have habs_le : |M.linkLoad (x c) l - svc c l| ≤ B := by
          rw [abs_le]
          exact ⟨by linarith [(hsvc c hc0 l).1], by linarith [(hsvc c hc0 l).1]⟩
        have hdrift : |projDrift (M.linkLoad (x c) l - svc c l) (p c l)| ≤ B :=
          (abs_projDrift_le _ _).trans habs_le
        rw [hc_eq, abs_div, abs_of_pos (sub_pos.mpr hlt)] at hdrift
        exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hdrift
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hordered s hs t ht hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hordered t ht s hs hts
  refine ⟨(Fintype.card L : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB0, fun r s hs t ht => ?_⟩
  rw [← M.routePrice_sub, routePrice]
  calc |∑ l ∈ M.route r, (p s l - p t l)|
      ≤ ∑ l ∈ M.route r, |p s l - p t l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ M.route r, B * |s - t| := Finset.sum_le_sum fun l _ => hlink_lip l s hs t ht
    _ = ((M.route r).card : ℝ) * (B * |s - t|) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card L : ℝ) * (B * |s - t|) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB0 (abs_nonneg _))
        exact_mod_cast Finset.card_le_univ (M.route r)
    _ = (Fintype.card L : ℝ) * B * |s - t| := by ring

/-- When `M.routePrice` is injective (full row rank of `R`), convergence of route prices
`M.routePrice (p t) → M.routePrice pStar` implies convergence of link prices `p t → pStar`. -/
private theorem tendsto_price_of_tendsto_routePrice [Finite R]
    {p : ℝ → L → ℝ} {pStar : L → ℝ} (hinj : Function.Injective M.routePrice)
    (hq : Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar))) :
    Tendsto p atTop (𝓝 pStar) := by
  let f : (L → ℝ) →ₗ[ℝ] (R → ℝ) :=
    { toFun := M.routePrice
      map_add' := fun a b => funext fun r => M.routePrice_add a b r
      map_smul' := fun c a => funext fun r => M.routePrice_smul c a r }
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hker
  have hg_cont : Continuous g := g.continuous_of_finiteDimensional
  have hleft : ∀ q : L → ℝ, g (M.routePrice q) = q := fun q => by
    have := LinearMap.congr_fun hg q
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, f, LinearMap.coe_mk, AddHom.coe_mk]
      using this
  have hlim : Tendsto (fun t => g (M.routePrice (p t))) atTop (𝓝 (g (M.routePrice pStar))) :=
    hg_cont.continuousAt.tendsto.comp hq
  simpa only [hleft] using hlim

/-- Shared global convergence engine for myopic rate control `U'_r(x_r(t)) = q_r(t)` under any
projected price trajectory satisfying the Lyapunov drift bound (used for both wireline
Eqs. (22.13)+(22.15) and wireless Max-Weight Eqs. (22.15)+(22.21)). -/
private theorem tendsto_of_myopic_drift [Fintype R] [Fintype L] [DecidableEq L]
    {x : ℝ → R → ℝ} {svc : ℝ → L → ℝ} {p : ℝ → L → ℝ} {xStar : R → ℝ} {pStar : L → ℝ}
    (hroute : ∀ r, (M.route r).Nonempty)
    (hcap : ∀ l, 0 ≤ M.capacity l)
    (hU : ∀ r, IsAdmissibleUtility (M.utility r))
    (hstrict : ∀ r, StrictConcaveOn ℝ (Ici 0) (M.utility r))
    (hxStar0 : ∀ r, 0 ≤ xStar r)
    (hxStar_eq : ∀ r, derivWithin (M.utility r) (Ici 0) (xStar r) = M.routePrice pStar r)
    (hp : ∀ t ∈ Ici (0 : ℝ), (∀ l, 0 ≤ p t l) ∧
      ∀ l, HasDerivWithinAt (fun s => p s l)
        (projDrift (M.linkLoad (x t) l - svc t l) (p t l)) (Ici 0) t)
    (hsvc : ∀ t ∈ Ici (0 : ℝ), ∀ l, 0 ≤ svc t l ∧ svc t l ≤ M.capacity l)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      derivWithin (M.utility r) (Ici 0) (x t r) = M.routePrice (p t) r)
    (hdrift : ∀ t ∈ Ici (0 : ℝ),
      ∃ D, HasDerivWithinAt (fun s => lyapunov pStar (p s)) D (Ici 0) t ∧
        D ≤ ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) * (x t r - xStar r)) :
    Tendsto x atTop (𝓝 xStar) ∧
      Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar)) ∧
      (Function.Injective M.routePrice → Tendsto p atTop (𝓝 pStar)) := by
  have hanti : ∀ r, StrictAntiOn (derivWithin (M.utility r) (Ici 0)) (Ici 0) :=
    fun r => strictAntiOn_derivWithin_of_strictConcaveOn (hstrict r) (hU r).differentiableOn
  -- Step 1: automatic uniform upper bound `X r` on `x t r` via the route-price barrier.
  let X : R → ℝ := fun r => max (x 0 r) ((∑ l ∈ M.route r, M.capacity l) + 1)
  have hX_nonneg : ∀ r, 0 ≤ X r := fun r =>
    le_trans (hx0 0 le_rfl r) (le_max_left _ _)
  have hx_le_X : ∀ t ∈ Ici (0 : ℝ), ∀ r, x t r ≤ X r := by
    intro t ht r
    have hq0 : derivWithin (M.utility r) (Ici 0) (X r) ≤ M.routePrice (p 0) r := by
      rw [← hctrl 0 le_rfl r]
      exact (hU r).derivWithin_antitoneOn (hx0 0 le_rfl r) (hX_nonneg r) (le_max_left _ _)
    have hq_ge : derivWithin (M.utility r) (Ici 0) (X r) ≤ M.routePrice (p t) r := by
      refine M.routePrice_ge_of_barrier hroute hp (fun s hs l => (hsvc s hs l).2) hx0 hq0 ?_ t ht
      intro s hs hlt l hl
      rw [← hctrl s hs r] at hlt
      have hX_lt : X r < x s r := by
        by_contra hle
        push Not at hle
        have := (hU r).derivWithin_antitoneOn (hx0 s hs r) (hX_nonneg r) hle
        linarith
      have hcap_le : M.capacity l ≤ ∑ l' ∈ M.route r, M.capacity l' :=
        Finset.single_le_sum (fun l' _ => hcap l') hl
      have hcap_lt_X : M.capacity l < X r :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      exact hcap_lt_X.trans hX_lt
    rw [← hctrl t ht r] at hq_ge
    by_contra hgt
    push Not at hgt
    have := hanti r (hX_nonneg r) (hx0 t ht r) hgt
    linarith
  -- Step 2: Lipschitz route prices `q_r` and uniformly continuous rates `x_r`.
  obtain ⟨K, hK0, hq_lip⟩ := M.lipschitz_routePrice_of_bounded hp
    (fun t ht r => ⟨hx0 t ht r, hx_le_X t ht r⟩) hsvc
  have hx_uc : ∀ r, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |s - t| ≤ δ → |x s r - x t r| ≤ ε := by
    intro r ε hε
    obtain ⟨η, hη, hmod⟩ := uniform_modulus_of_strictAntiOn (hanti r) (hX_nonneg r) hε
    refine ⟨η / (2 * (K + 1)), by positivity, fun s hs t ht hst => ?_⟩
    have hq_lt : |derivWithin (M.utility r) (Ici 0) (x s r) -
        derivWithin (M.utility r) (Ici 0) (x t r)| < η := by
      rw [hctrl s hs r, hctrl t ht r]
      have h1 := hq_lip r s hs t ht
      have h2 : K * |s - t| ≤ K * (η / (2 * (K + 1))) :=
        mul_le_mul_of_nonneg_left hst hK0
      have h3 : K * (η / (2 * (K + 1))) < η := by
        have hpos : 0 < 2 * (K + 1) := by linarith
        rw [mul_div_assoc', div_lt_iff₀ hpos]
        nlinarith
      exact h1.trans_lt (h2.trans_lt h3)
    exact (hmod (x s r) ⟨hx0 s hs r, hx_le_X s hs r⟩
      (x t r) ⟨hx0 t ht r, hx_le_X t ht r⟩ hq_lt).le
  -- Step 3: apply Barbalat to `φ(t) = ∑_r (q_r(t) - q*_r) (x*_r - x_r(t)) ≥ 0`.
  let φ : ℝ → ℝ := fun t =>
    ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r)
  have hterm_nn : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      0 ≤ (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r) := by
    intro t ht r
    rw [← hctrl t ht r, ← hxStar_eq r]
    rcases le_total (x t r) (xStar r) with hle | hge
    · exact mul_nonneg (sub_nonneg.mpr ((hU r).derivWithin_antitoneOn (hx0 t ht r) (hxStar0 r) hle))
        (sub_nonneg.mpr hle)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((hU r).derivWithin_antitoneOn (hxStar0 r) (hx0 t ht r) hge))
        (sub_nonpos.mpr hge)
  have hφ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ φ t :=
    fun t ht => Finset.sum_nonneg fun r _ => hterm_nn t ht r
  have hVderiv_all : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => lyapunov pStar (p s))
      (∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - svc t l) (p t l)) (Ici 0) t :=
    fun t ht => hasDerivWithinAt_lyapunov (hp t ht).2
  have hVdecay : ∀ t ∈ Ici (0 : ℝ),
      (∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - svc t l) (p t l)) ≤ -φ t := by
    intro t ht
    obtain ⟨D, hD_der, hD_le⟩ := hdrift t ht
    have hDeq : D = ∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - svc t l) (p t l) :=
      (hD_der.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm.trans
        ((hVderiv_all t ht).derivWithin (uniqueDiffOn_Ici 0 t ht))
    rw [← hDeq]
    have hneg : -φ t = ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) * (x t r - xStar r) := by
      simp only [φ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    linarith
  have hφ_uc : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |s - t| ≤ δ → |φ s - φ t| ≤ ε := by
    intro ε hε
    by_cases hR : Nonempty R
    · have : Nonempty R := hR
      have hcard : (0 : ℝ) < (Fintype.card R : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
      have hterm_uc : ∀ r : R, ∃ δ > 0, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ), |s - t| ≤ δ →
          |(M.routePrice (p s) r - M.routePrice pStar r) * (xStar r - x s r) -
            (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r)| ≤
            ε / (Fintype.card R : ℝ) := by
        intro r
        let Mq : ℝ := max (|derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r|)
          (|derivWithin (M.utility r) (Ici 0) (X r) - M.routePrice pStar r|) + 1
        let Mx : ℝ := max (xStar r) (X r) + 1
        have hMq : 0 < Mq := by
          dsimp only [Mq]
          have h0 : 0 ≤ |derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r| := abs_nonneg _
          have h1 := le_max_left (|derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r|)
            (|derivWithin (M.utility r) (Ici 0) (X r) - M.routePrice pStar r|)
          linarith
        have hMx : 0 < Mx := by
          dsimp only [Mx]
          linarith [hxStar0 r, le_max_left (xStar r) (X r)]
        have hq_bdd : ∀ u ∈ Ici (0 : ℝ), |M.routePrice (p u) r - M.routePrice pStar r| ≤ Mq := by
          intro u hu
          rw [← hctrl u hu r]
          have h1 := (hU r).derivWithin_antitoneOn (le_rfl : (0 : ℝ) ≤ 0) (hx0 u hu r) (hx0 u hu r)
          have h2 := (hU r).derivWithin_antitoneOn (hx0 u hu r) (hX_nonneg r) (hx_le_X u hu r)
          rw [abs_le]
          constructor
          · have := neg_abs_le (derivWithin (M.utility r) (Ici 0) (X r) - M.routePrice pStar r)
            have := le_max_right (|derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r|)
              (|derivWithin (M.utility r) (Ici 0) (X r) - M.routePrice pStar r|)
            linarith
          · have := le_abs_self (derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r)
            have := le_max_left (|derivWithin (M.utility r) (Ici 0) 0 - M.routePrice pStar r|)
              (|derivWithin (M.utility r) (Ici 0) (X r) - M.routePrice pStar r|)
            linarith
        have hx_bdd : ∀ u ∈ Ici (0 : ℝ), |xStar r - x u r| ≤ Mx := by
          intro u hu
          rw [abs_le]
          constructor
          · linarith [hxStar0 r, hx_le_X u hu r, le_max_right (xStar r) (X r)]
          · linarith [hx0 u hu r, le_max_left (xStar r) (X r)]
        let εr : ℝ := ε / (2 * (Fintype.card R : ℝ))
        have hεr : 0 < εr := by positivity
        obtain ⟨δx, hδx, hδx_uc⟩ := hx_uc r (εr / Mq) (div_pos hεr hMq)
        let δq : ℝ := εr / ((K + 1) * Mx)
        have hδq : 0 < δq := by positivity
        refine ⟨min δx δq, lt_min hδx hδq, fun s hs t ht hst => ?_⟩
        have h1 : |M.routePrice (p s) r - M.routePrice (p t) r| * |xStar r - x t r| ≤ εr := by
          have ha := hq_lip r s hs t ht
          have hb := hx_bdd t ht
          have hstq : |s - t| ≤ δq := hst.trans (min_le_right _ _)
          have hmul : K * |s - t| * Mx ≤ (K + 1) * δq * Mx := by
            have hK1 : K * |s - t| ≤ (K + 1) * δq := by nlinarith [abs_nonneg (s - t)]
            exact mul_le_mul_of_nonneg_right hK1 hMx.le
          have hcancel : (K + 1) * δq * Mx = εr := by
            dsimp only [δq]
            have hK1 : (K + 1 : ℝ) ≠ 0 := by linarith
            field_simp [hK1, hMx.ne']
          exact (mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hK0 (abs_nonneg _))).trans
            (hmul.trans hcancel.le)
        have h2 : |M.routePrice (p s) r - M.routePrice pStar r| * |x s r - x t r| ≤ εr := by
          have ha := hq_bdd s hs
          have hb := hδx_uc s hs t ht (hst.trans (min_le_left _ _))
          have hcancel : Mq * (εr / Mq) = εr := mul_div_cancel₀ _ hMq.ne'
          exact (mul_le_mul ha hb (abs_nonneg _) hMq.le).trans hcancel.le
        have hsplit : (M.routePrice (p s) r - M.routePrice pStar r) * (xStar r - x s r) -
            (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r) =
            (M.routePrice (p s) r - M.routePrice (p t) r) * (xStar r - x t r) -
            (M.routePrice (p s) r - M.routePrice pStar r) * (x s r - x t r) := by ring
        rw [hsplit]
        have htri := abs_sub ((M.routePrice (p s) r - M.routePrice (p t) r) * (xStar r - x t r))
          ((M.routePrice (p s) r - M.routePrice pStar r) * (x s r - x t r))
        rw [abs_mul, abs_mul] at htri
        have hε2 : εr + εr = ε / (Fintype.card R : ℝ) := by dsimp only [εr]; ring
        linarith
      choose δr hδr_pos hδr_uc using hterm_uc
      obtain ⟨r₀⟩ := hR
      have huniv : (Finset.univ : Finset R).Nonempty := ⟨r₀, Finset.mem_univ r₀⟩
      refine ⟨Finset.univ.inf' huniv δr, (Finset.lt_inf'_iff huniv).mpr fun r _ => hδr_pos r,
        fun s hs t ht hst => ?_⟩
      dsimp only [φ]
      rw [← Finset.sum_sub_distrib]
      calc |∑ r, ((M.routePrice (p s) r - M.routePrice pStar r) * (xStar r - x s r) -
              (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r))|
          ≤ ∑ r, |(M.routePrice (p s) r - M.routePrice pStar r) * (xStar r - x s r) -
              (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r : R, ε / (Fintype.card R : ℝ) :=
            Finset.sum_le_sum fun r _ => hδr_uc r s hs t ht
              (hst.trans (Finset.inf'_le δr (Finset.mem_univ r)))
        _ = ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne']
    · have : IsEmpty R := not_nonempty_iff.mp hR
      refine ⟨1, zero_lt_one, fun _ _ _ _ _ => ?_⟩
      simp [φ, hε.le]
  have hφ_lim : Tendsto φ atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivWithinAt_le_neg (fun t _ => lyapunov_nonneg pStar (p t))
      hVderiv_all hφ0 hVdecay hφ_uc
  -- Step 4: deduce `x t → xStar`, `routePrice (p t) → routePrice pStar`, and `p t → pStar`.
  have hx_lim : Tendsto x atTop (𝓝 xStar) := by
    rw [tendsto_pi_nhds]
    intro r
    have hterm_lim : Tendsto
        (fun t => (M.routePrice (p t) r - M.routePrice pStar r) * (xStar r - x t r))
        atTop (𝓝 0) :=
      squeeze_zero' (eventually_atTop.mpr ⟨0, fun t ht => hterm_nn t ht r⟩)
        (eventually_atTop.mpr ⟨0, fun t ht =>
          Finset.single_le_sum (f := fun r' =>
            (M.routePrice (p t) r' - M.routePrice pStar r') * (xStar r' - x t r'))
            (fun r' _ => hterm_nn t ht r') (Finset.mem_univ r)⟩)
        hφ_lim
    rw [Metric.tendsto_atTop] at hterm_lim ⊢
    intro ε hε
    set g := derivWithin (M.utility r) (Ici 0)
    have hxStar_add : 0 ≤ xStar r + ε := by linarith [hxStar0 r]
    have hgapR : 0 < (g (xStar r) - g (xStar r + ε)) * ε :=
      mul_pos (sub_pos.mpr (hanti r (hxStar0 r) hxStar_add (by linarith))) hε
    let η : ℝ := if h : ε ≤ xStar r then
        min ((g (xStar r) - g (xStar r + ε)) * ε) ((g (xStar r - ε) - g (xStar r)) * ε)
      else (g (xStar r) - g (xStar r + ε)) * ε
    have hη_pos : 0 < η := by
      dsimp only [η]
      split_ifs with h
      · exact lt_min hgapR (mul_pos
          (sub_pos.mpr (hanti r (sub_nonneg.mpr h) (hxStar0 r) (by linarith))) hε)
      · exact hgapR
    obtain ⟨T, hT⟩ := hterm_lim η hη_pos
    refine ⟨max T 0, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right T 0).trans ht
    have hsmall := hT t ((le_max_left T 0).trans ht)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hterm_nn t ht0 r),
      ← hctrl t ht0 r, ← hxStar_eq r] at hsmall
    change (g (x t r) - g (xStar r)) * (xStar r - x t r) < η at hsmall
    rw [Real.dist_eq, abs_lt]
    constructor
    · by_contra hle
      push Not at hle
      have hε_le : ε ≤ xStar r := by linarith [hx0 t ht0 r]
      have hg_ge : g (xStar r - ε) ≤ g (x t r) :=
        (hU r).derivWithin_antitoneOn (hx0 t ht0 r) (sub_nonneg.mpr hε_le) (by linarith)
      have hprod : (g (xStar r - ε) - g (xStar r)) * ε ≤
          (g (x t r) - g (xStar r)) * (xStar r - x t r) := by
        nlinarith [sub_pos.mpr (hanti r (sub_nonneg.mpr hε_le) (hxStar0 r) (by linarith))]
      have hη_le : η ≤ (g (xStar r - ε) - g (xStar r)) * ε := by
        simp only [η, hε_le, ↓reduceDIte, min_le_right]
      linarith
    · by_contra hge
      push Not at hge
      have hg_le : g (x t r) ≤ g (xStar r + ε) :=
        (hU r).derivWithin_antitoneOn hxStar_add (hx0 t ht0 r) (by linarith)
      have hprod : (g (xStar r) - g (xStar r + ε)) * ε ≤
          (g (x t r) - g (xStar r)) * (xStar r - x t r) := by
        nlinarith [sub_pos.mpr (hanti r (hxStar0 r) hxStar_add (by linarith))]
      have hη_le : η ≤ (g (xStar r) - g (xStar r + ε)) * ε := by
        dsimp only [η]; split_ifs
        · exact min_le_left _ _
        · exact le_rfl
      linarith
  have hq_lim : Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar)) := by
    rw [tendsto_pi_nhds]
    intro r
    have hxr : Tendsto (fun t => x t r) atTop (𝓝[Ici 0] (xStar r)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(tendsto_pi_nhds.mp hx_lim r), eventually_atTop.mpr ⟨0, fun t ht => hx0 t ht r⟩⟩
    have hcomp := (continuousWithinAt_derivWithin_of_admissible (hU r) (hxStar0 r)).tendsto.comp hxr
    rw [hxStar_eq r] at hcomp
    exact hcomp.congr' (eventually_atTop.mpr ⟨0, fun t ht => hctrl t ht r⟩)
  exact ⟨hx_lim, hq_lim, fun hinj => M.tendsto_price_of_tendsto_routePrice hinj hq_lim⟩

/-- A dual congestion-control price trajectory `p : ℝ → L → ℝ` driven by source rates
`x : ℝ → R → ℝ` on `[0, ∞)`: prices stay nonnegative and evolve according to the projected
excess-demand ODE `ṗ_l(t) = (y_l(t) - c_l)^+_{p_l(t)}` ([OzdaglarSrikant2007], §22.1,
Eq. (22.13), p. 575). -/
@[expose] def IsDualPriceTrajectory [Fintype R] [DecidableEq L]
    (x : ℝ → R → ℝ) (p : ℝ → L → ℝ) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), (∀ l, 0 ≤ p t l) ∧
    ∀ l, HasDerivWithinAt (fun s => p s l)
      (projDrift (M.linkLoad (x t) l - M.capacity l) (p t l)) (Ici 0) t

/-- **Dual congestion-control Lyapunov drift inequality** ([OzdaglarSrikant2007], §22.1,
pp. 575–576, steps (a)–(b)): along any dual price trajectory `p`, the derivative of
`lyapunov pStar (p t)` is bounded above by `∑_r (q_r(t) - q*_r) (x_r(t) - x*_r)`. -/
theorem IsDualPriceTrajectory.hasDerivWithinAt_lyapunov_le [Fintype R] [Fintype L] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x : ℝ → R → ℝ} {p : ℝ → L → ℝ}
    (htraj : M.IsDualPriceTrajectory x p) {xStar : R → ℝ} {pStar : L → ℝ}
    (hxStar : M.IsFeasible xStar) (hpStar : ∀ l, 0 ≤ pStar l)
    (hcs : ∀ l, pStar l * (M.linkLoad xStar l - M.capacity l) = 0)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    ∃ D, HasDerivWithinAt (fun s => lyapunov pStar (p s)) D (Ici 0) t ∧
      D ≤ ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) * (x t r - xStar r) := by
  refine ⟨∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - M.capacity l) (p t l),
    hasDerivWithinAt_lyapunov (htraj t ht).2, ?_⟩
  calc ∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - M.capacity l) (p t l)
      ≤ ∑ l, (p t l - pStar l) * (M.linkLoad (x t) l - M.capacity l) :=
        Finset.sum_le_sum fun l _ => mul_projDrift_le ((htraj t ht).1 l) (hpStar l)
    _ ≤ ∑ l, (p t l - pStar l) * (M.linkLoad (x t) l - M.linkLoad xStar l) := by
        refine Finset.sum_le_sum fun l _ => ?_
        have h1 : p t l * (M.linkLoad xStar l - M.capacity l) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ((htraj t ht).1 l) (sub_nonpos.mpr (hxStar.2 l))
        have h2 := hcs l
        linarith
    _ = ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) * (x t r - xStar r) := by
        simpa only [M.routePrice_sub, M.linkLoad_sub] using
          (M.sum_routePrice_mul_eq_sum_price_mul_linkLoad
            (fun l => p t l - pStar l) (fun r => x t r - xStar r)).symm

private theorem myopic_rate_drift_nonpos [Fintype R]
    (hU : ∀ r, IsAdmissibleUtility (M.utility r))
    {x xStar : R → ℝ} {p pStar : L → ℝ}
    (hx : ∀ r, 0 ≤ x r) (hxStar : ∀ r, 0 ≤ xStar r)
    (hctrl : ∀ r, derivWithin (M.utility r) (Ici 0) (x r) = M.routePrice p r)
    (hctrlStar : ∀ r, derivWithin (M.utility r) (Ici 0) (xStar r) = M.routePrice pStar r) :
    ∑ r, (M.routePrice p r - M.routePrice pStar r) * (x r - xStar r) ≤ 0 := by
  refine Finset.sum_nonpos fun r _ => ?_
  rw [← hctrl r, ← hctrlStar r]
  rcases le_total (x r) (xStar r) with hle | hge
  · exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr ((hU r).derivWithin_antitoneOn (hx r) (hxStar r) hle))
      (sub_nonpos.mpr hle)
  · exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ((hU r).derivWithin_antitoneOn (hxStar r) (hx r) hge))
      (sub_nonneg.mpr hge)

/-- **Lyapunov stability for fixed-bid dual congestion control** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.13)–(22.14), pp. 575–576): under `x_r(t) = w_r / q_r(t)`, `lyapunov pStar ∘ p` is
nonincreasing on `[0, ∞)`. -/
theorem IsDualPriceTrajectory.antitoneOn_lyapunov_of_fixedBids [Fintype R] [Fintype L]
    [DecidableEq L] {M : NetworkUtilityModel R L} {w : R → ℝ} {x : ℝ → R → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {pStar : L → ℝ}
    (hw : ∀ r, 0 < w r) (hkkt : M.IsWeightedPropFairKKT w xStar pStar)
    (htraj : M.IsDualPriceTrajectory x p)
    (hqpos : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 < M.routePrice (p t) r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r, x t r = w r / M.routePrice (p t) r) :
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) := by
  refine antitoneOn_lyapunov_of_drift_nonpos fun t ht => ?_
  obtain ⟨D, hD_der, hD_le⟩ :=
    htraj.hasDerivWithinAt_lyapunov_le hkkt.feasible hkkt.price_nonneg hkkt.comp_slack ht
  refine ⟨D, hD_der, hD_le.trans (Finset.sum_nonpos fun r _ => ?_)⟩
  have hqStar : 0 < M.routePrice pStar r := by
    rw [← hkkt.rate_eq r]; exact div_pos (hw r) (hkkt.rate_pos r)
  have hxStar_eq : xStar r = w r / M.routePrice pStar r := by
    rw [← hkkt.rate_eq r, div_div_cancel₀ (hw r).ne']
  rw [hctrl t ht r, hxStar_eq]
  have hid : (M.routePrice (p t) r - M.routePrice pStar r) *
      (w r / M.routePrice (p t) r - w r / M.routePrice pStar r) =
      -((M.routePrice (p t) r - M.routePrice pStar r) ^ 2 *
        (w r / (M.routePrice (p t) r * M.routePrice pStar r))) := by
    field_simp [(hqpos t ht r).ne', hqStar.ne']
    ring
  rw [hid]
  exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _)
    (div_nonneg (hw r).le (mul_nonneg (hqpos t ht r).le hqStar.le)))

/-- **Global asymptotic convergence of fixed-bid dual congestion control** ([OzdaglarSrikant2007],
§22.1, Eqs. (22.13)–(22.14), pp. 575–576): along any trajectory of `ṗ_l = (y_l - c_l)^+_{p_l}`
with `x_r = w_r / q_r`, route prices converge to `q*`, rates converge to the unique weighted
proportionally fair allocation `x*`, and under full row rank (`Function.Injective M.routePrice`)
link prices converge to `p*`. -/
theorem IsDualPriceTrajectory.tendsto_of_fixedBids [Fintype R] [Finite L] [DecidableEq L]
    {M : NetworkUtilityModel R L} {w : R → ℝ} {x : ℝ → R → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {pStar : L → ℝ}
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 < M.capacity l)
    (hw : ∀ r, 0 < w r) (hkkt : M.IsWeightedPropFairKKT w xStar pStar)
    (htraj : M.IsDualPriceTrajectory x p)
    (hqpos : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 < M.routePrice (p t) r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r, x t r = w r / M.routePrice (p t) r) :
    Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar)) ∧
      Tendsto x atTop (𝓝 xStar) ∧
      (Function.Injective M.routePrice → Tendsto p atTop (𝓝 pStar)) := by
  let : Fintype L := Fintype.ofFinite L
  have hqStar_pos : ∀ r, 0 < M.routePrice pStar r := fun r => by
    rw [← hkkt.rate_eq r]; exact div_pos (hw r) (hkkt.rate_pos r)
  have hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r := fun t ht r => by
    rw [hctrl t ht r]; exact div_nonneg (hw r).le (hqpos t ht r).le
  -- Step 1: automatic positive lower bound on `q_r(t)` and hence upper bound on `x_r(t)`.
  let qMin : R → ℝ := fun r =>
    min (M.routePrice (p 0) r) (Finset.inf' (M.route r) (hroute r) fun l => w r / M.capacity l)
  have hqMin_pos : ∀ r, 0 < qMin r := fun r =>
    lt_min (hqpos 0 le_rfl r)
      ((Finset.lt_inf'_iff (hroute r)).mpr fun l _ => div_pos (hw r) (hcap l))
  have hq_ge : ∀ t ∈ Ici (0 : ℝ), ∀ r, qMin r ≤ M.routePrice (p t) r := by
    intro t ht r
    refine M.routePrice_ge_of_barrier hroute htraj
      (fun _ _ _ => le_rfl) hx0 (min_le_left _ _) ?_ t ht
    intro s hs hlt l hl
    have hlt_l : M.routePrice (p s) r < w r / M.capacity l :=
      hlt.trans_le ((min_le_right _ _).trans
        (Finset.inf'_le (f := fun l' => w r / M.capacity l') hl))
    rw [hctrl s hs r]
    exact (lt_div_iff₀ (hqpos s hs r)).mpr ((lt_div_iff₀ (hcap l)).mp hlt_l |> fun h => by linarith)
  have hx_le : ∀ t ∈ Ici (0 : ℝ), ∀ r, x t r ≤ w r / qMin r := fun t ht r => by
    rw [hctrl t ht r]
    exact div_le_div_of_nonneg_left (hw r).le (hqMin_pos r) (hq_ge t ht r)
  -- Step 2: uniform upper bound on `p t l` and `q_r(t)` from Lyapunov stability.
  have hanti := htraj.antitoneOn_lyapunov_of_fixedBids hw hkkt hqpos hctrl
  have hp_le : ∀ t ∈ Ici (0 : ℝ), ∀ l, p t l ≤ pStar l + Real.sqrt (2 * lyapunov pStar (p 0)) := by
    intro t ht l
    have hVle : lyapunov pStar (p t) ≤ lyapunov pStar (p 0) := hanti (mem_Ici.mpr le_rfl) ht ht
    have hsq : (p t l - pStar l) ^ 2 ≤ 2 * lyapunov pStar (p 0) := by
      have h1 : (p t l - pStar l) ^ 2 ≤ ∑ l', (p t l' - pStar l') ^ 2 :=
        Finset.single_le_sum (f := fun l' => (p t l' - pStar l') ^ 2)
          (fun l' _ => sq_nonneg _) (Finset.mem_univ l)
      unfold lyapunov at hVle ⊢
      linarith
    have habs : |p t l - pStar l| ≤ Real.sqrt (2 * lyapunov pStar (p 0)) :=
      (Real.sqrt_sq_eq_abs _).symm ▸ Real.sqrt_le_sqrt hsq
    linarith [(abs_le.mp habs).2]
  let Qmax : R → ℝ := fun r =>
    ∑ l ∈ M.route r, (pStar l + Real.sqrt (2 * lyapunov pStar (p 0)))
  have hq_le : ∀ t ∈ Ici (0 : ℝ), ∀ r, M.routePrice (p t) r ≤ Qmax r := fun t ht r =>
    Finset.sum_le_sum fun l _ => hp_le t ht l
  have hQmax_pos : ∀ r, 0 < Qmax r := fun r => lt_of_lt_of_le (hqpos 0 le_rfl r) (hq_le 0 le_rfl r)
  -- Step 3: Lipschitz bound on `q_r` and Barbalat on `φ(t) = ∑_r c_r (q_r(t) - q*_r)^2`.
  obtain ⟨K, hK0, hq_lip⟩ := M.lipschitz_routePrice_of_bounded htraj
    (fun t ht r => ⟨hx0 t ht r, hx_le t ht r⟩) (fun _ _ l => ⟨(hcap l).le, le_rfl⟩)
  let c : R → ℝ := fun r => w r / (Qmax r * M.routePrice pStar r)
  have hc_pos : ∀ r, 0 < c r := fun r => div_pos (hw r) (mul_pos (hQmax_pos r) (hqStar_pos r))
  let φ : ℝ → ℝ := fun t => ∑ r, c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2
  have hφ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ φ t := fun t _ =>
    Finset.sum_nonneg fun r _ => mul_nonneg (hc_pos r).le (sq_nonneg _)
  have hVderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => lyapunov pStar (p s))
      (∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - M.capacity l) (p t l)) (Ici 0) t :=
    fun t ht => hasDerivWithinAt_lyapunov (htraj t ht).2
  have hVdecay : ∀ t ∈ Ici (0 : ℝ),
      (∑ l, (p t l - pStar l) * projDrift (M.linkLoad (x t) l - M.capacity l) (p t l)) ≤ -φ t := by
    intro t ht
    obtain ⟨D, hD_der, hD_le⟩ :=
      htraj.hasDerivWithinAt_lyapunov_le hkkt.feasible hkkt.price_nonneg hkkt.comp_slack ht
    have hDeq : D = ∑ l, (p t l - pStar l) *
        projDrift (M.linkLoad (x t) l - M.capacity l) (p t l) :=
      (hD_der.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm.trans
        ((hVderiv t ht).derivWithin (uniqueDiffOn_Ici 0 t ht))
    rw [← hDeq]
    have hsum_le : ∑ r, (M.routePrice (p t) r - M.routePrice pStar r) *
        (x t r - xStar r) ≤ -φ t := by
      rw [show -φ t = ∑ r, -(c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2) by
        simp only [φ, Finset.sum_neg_distrib]]
      refine Finset.sum_le_sum fun r _ => ?_
      have hxStar_eq : xStar r = w r / M.routePrice pStar r := by
        rw [← hkkt.rate_eq r, div_div_cancel₀ (hw r).ne']
      rw [hctrl t ht r, hxStar_eq]
      have hid : (M.routePrice (p t) r - M.routePrice pStar r) *
          (w r / M.routePrice (p t) r - w r / M.routePrice pStar r) =
          -(w r / (M.routePrice (p t) r * M.routePrice pStar r) *
            (M.routePrice (p t) r - M.routePrice pStar r) ^ 2) := by
        field_simp [(hqpos t ht r).ne', (hqStar_pos r).ne']
        ring
      rw [hid]
      have hcoef : c r ≤ w r / (M.routePrice (p t) r * M.routePrice pStar r) :=
        div_le_div_of_nonneg_left (hw r).le (mul_pos (hqpos t ht r) (hqStar_pos r))
          (mul_le_mul_of_nonneg_right (hq_le t ht r) (hqStar_pos r).le)
      nlinarith [sq_nonneg (M.routePrice (p t) r - M.routePrice pStar r)]
    exact hD_le.trans hsum_le
  have hφ_uc : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      |s - t| ≤ δ → |φ s - φ t| ≤ ε := by
    intro ε hε
    let Lφ : ℝ := ∑ r, c r * (2 * (Qmax r + M.routePrice pStar r) * K)
    have hLφ0 : 0 ≤ Lφ := Finset.sum_nonneg fun r _ =>
      mul_nonneg (hc_pos r).le (mul_nonneg (by linarith [hQmax_pos r, hqStar_pos r]) hK0)
    refine ⟨ε / (Lφ + 1), by positivity, fun s hs t ht hst => ?_⟩
    have hlip : |φ s - φ t| ≤ Lφ * |s - t| := by
      dsimp only [φ, Lφ]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      calc |∑ r, (c r * (M.routePrice (p s) r - M.routePrice pStar r) ^ 2 -
              c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2)|
          ≤ ∑ r, |c r * (M.routePrice (p s) r - M.routePrice pStar r) ^ 2 -
              c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r, c r * (2 * (Qmax r + M.routePrice pStar r) * K) * |s - t| := by
            refine Finset.sum_le_sum fun r _ => ?_
            have hfac : c r * (M.routePrice (p s) r - M.routePrice pStar r) ^ 2 -
                c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2 =
                c r * ((M.routePrice (p s) r - M.routePrice pStar r) +
                  (M.routePrice (p t) r - M.routePrice pStar r)) *
                (M.routePrice (p s) r - M.routePrice (p t) r) := by ring
            rw [hfac, abs_mul, abs_mul, abs_of_pos (hc_pos r)]
            have hsum_bdd : |(M.routePrice (p s) r - M.routePrice pStar r) +
                (M.routePrice (p t) r - M.routePrice pStar r)| ≤
                2 * (Qmax r + M.routePrice pStar r) := by
              rw [abs_le]
              constructor <;> linarith [hqpos s hs r, hqpos t ht r, hq_le s hs r, hq_le t ht r,
                hqStar_pos r]
            have hdiff_bdd := hq_lip r s hs t ht
            calc c r * |(M.routePrice (p s) r - M.routePrice pStar r) +
                    (M.routePrice (p t) r - M.routePrice pStar r)| *
                    |M.routePrice (p s) r - M.routePrice (p t) r|
                ≤ c r * (2 * (Qmax r + M.routePrice pStar r)) * (K * |s - t|) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hsum_bdd (hc_pos r).le)
                    hdiff_bdd (abs_nonneg _)
                    (mul_nonneg (hc_pos r).le (by linarith [hQmax_pos r, hqStar_pos r]))
              _ = c r * (2 * (Qmax r + M.routePrice pStar r) * K) * |s - t| := by ring
    have hbound : Lφ * |s - t| ≤ ε := by
      have h1 : Lφ * |s - t| ≤ (Lφ + 1) * (ε / (Lφ + 1)) := by nlinarith [abs_nonneg (s - t)]
      have hcancel : (Lφ + 1) * (ε / (Lφ + 1)) = ε := mul_div_cancel₀ _ (by linarith)
      linarith
    exact hlip.trans hbound
  have hφ_lim : Tendsto φ atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivWithinAt_le_neg (fun t _ => lyapunov_nonneg pStar (p t))
      hVderiv hφ0 hVdecay hφ_uc
  have hq_lim : Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar)) := by
    rw [tendsto_pi_nhds]
    intro r
    have hsq_lim : Tendsto (fun t => c r * (M.routePrice (p t) r - M.routePrice pStar r) ^ 2)
        atTop (𝓝 0) :=
      squeeze_zero (fun t => mul_nonneg (hc_pos r).le (sq_nonneg _))
        (fun t => Finset.single_le_sum
          (f := fun r' => c r' * (M.routePrice (p t) r' - M.routePrice pStar r') ^ 2)
          (fun r' _ => mul_nonneg (hc_pos r').le (sq_nonneg _))
          (Finset.mem_univ r))
        hφ_lim
    rw [Metric.tendsto_atTop] at hsq_lim ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := hsq_lim (c r * ε ^ 2) (mul_pos (hc_pos r) (sq_pos_of_pos hε))
    refine ⟨T, fun t ht => ?_⟩
    have h1 := hT t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hc_pos r).le (sq_nonneg _))] at h1
    have h2 : (M.routePrice (p t) r - M.routePrice pStar r) ^ 2 < ε ^ 2 :=
      lt_of_mul_lt_mul_left h1 (hc_pos r).le
    rw [Real.dist_eq]
    nlinarith [sq_abs (M.routePrice (p t) r - M.routePrice pStar r),
      abs_nonneg (M.routePrice (p t) r - M.routePrice pStar r)]
  have hx_lim : Tendsto x atTop (𝓝 xStar) := by
    rw [tendsto_pi_nhds]
    intro r
    have hlim : Tendsto (fun t => w r / M.routePrice (p t) r) atTop
        (𝓝 (w r / M.routePrice pStar r)) :=
      tendsto_const_nhds.div (tendsto_pi_nhds.mp hq_lim r) (hqStar_pos r).ne'
    have hxStar_eq : w r / M.routePrice pStar r = xStar r := by
      rw [← hkkt.rate_eq r, div_div_cancel₀ (hw r).ne']
    rw [hxStar_eq] at hlim
    exact hlim.congr' (eventually_atTop.mpr ⟨0, fun t ht => (hctrl t ht r).symm⟩)
  exact ⟨hq_lim, hx_lim, fun hinj => M.tendsto_price_of_tendsto_routePrice hinj hq_lim⟩

/-- **Lyapunov stability for myopic dual congestion control** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.13), (22.15), pp. 575–576): under `U'_r(x_r(t)) = q_r(t)` with concave differentiable
utilities, `lyapunov pStar ∘ p` is nonincreasing on `[0, ∞)`. -/
theorem IsDualPriceTrajectory.antitoneOn_lyapunov_of_myopic [Fintype R] [Fintype L]
    [DecidableEq L] {M : NetworkUtilityModel R L} {x : ℝ → R → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {pStar : L → ℝ}
    (hU : ∀ r, IsAdmissibleUtility (M.utility r))
    (hkkt : M.IsKKT xStar pStar)
    (hxStar_eq : ∀ r, derivWithin (M.utility r) (Ici 0) (xStar r) = M.routePrice pStar r)
    (htraj : M.IsDualPriceTrajectory x p)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      derivWithin (M.utility r) (Ici 0) (x t r) = M.routePrice (p t) r) :
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) :=
  antitoneOn_lyapunov_of_drift_nonpos fun t ht => by
    obtain ⟨D, hD_der, hD_le⟩ :=
      htraj.hasDerivWithinAt_lyapunov_le hkkt.feasible hkkt.price_nonneg hkkt.comp_slack ht
    exact ⟨D, hD_der, hD_le.trans
      (M.myopic_rate_drift_nonpos hU (hx0 t ht) hkkt.feasible.1 (hctrl t ht) hxStar_eq)⟩

/-- **Global asymptotic convergence of myopic dual congestion control** ([OzdaglarSrikant2007],
§22.1, Eqs. (22.13), (22.15), pp. 575–576): for strictly concave admissible utilities, any
trajectory of `ṗ_l = (y_l - c_l)^+_{p_l}` with `U'_r(x_r) = q_r` converges globally: `x(t) → x*`,
`q(t) → q*`, and under full row rank (`Function.Injective M.routePrice`) `p(t) → p*`. -/
theorem IsDualPriceTrajectory.tendsto_of_myopic [Fintype R] [Finite L] [DecidableEq L]
    {M : NetworkUtilityModel R L} {x : ℝ → R → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {pStar : L → ℝ}
    (hroute : ∀ r, (M.route r).Nonempty) (hcap : ∀ l, 0 ≤ M.capacity l)
    (hU : ∀ r, IsAdmissibleUtility (M.utility r))
    (hstrict : ∀ r, StrictConcaveOn ℝ (Ici 0) (M.utility r))
    (hkkt : M.IsKKT xStar pStar)
    (hxStar_eq : ∀ r, derivWithin (M.utility r) (Ici 0) (xStar r) = M.routePrice pStar r)
    (htraj : M.IsDualPriceTrajectory x p)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      derivWithin (M.utility r) (Ici 0) (x t r) = M.routePrice (p t) r) :
    Tendsto x atTop (𝓝 xStar) ∧
      Tendsto (fun t => M.routePrice (p t)) atTop (𝓝 (M.routePrice pStar)) ∧
      (Function.Injective M.routePrice → Tendsto p atTop (𝓝 pStar)) := by
  let : Fintype L := Fintype.ofFinite L
  exact M.tendsto_of_myopic_drift hroute hcap hU hstrict hkkt.feasible.1 hxStar_eq htraj
    (fun _ _ l => ⟨hcap l, le_rfl⟩) hx0 hctrl
    fun _ ht =>
      htraj.hasDerivWithinAt_lyapunov_le hkkt.feasible hkkt.price_nonneg hkkt.comp_slack ht

end NetworkUtilityModel

/-! ### Part 4: Wireless NUM and Max-Weight Scheduling (Eqs. (22.16)–(22.21)) -/

/-- A valid schedule time-sharing distribution on a finite schedule set `S`: `f ≥ 0` and
`∑_s f_s ≤ 1` ([OzdaglarSrikant2007], Eqs. (22.17)–(22.18), p. 577). -/
@[expose] def IsScheduleDist {S : Type*} [Fintype S] (f : S → ℝ) : Prop :=
  (∀ s, 0 ≤ f s) ∧ ∑ s, f s ≤ 1

/-- A wireless network utility maximization model with routes `R`, links `L`, and interference-free
schedules `S` ([OzdaglarSrikant2007], §22.1, pp. 577–578). Schedule `s : S` simultaneously activates
the links in `schedule s`, serving `capacity l` packets per unit time on each `l ∈ schedule s`. -/
structure WirelessNetworkModel (R L S : Type*) extends NetworkUtilityModel R L where
  /-- Subset of links `M_s` activated simultaneously under schedule `s`. -/
  schedule : S → Finset L

namespace WirelessNetworkModel

variable {R L S : Type*} (W : WirelessNetworkModel R L S)

/-- Effective service rate `∑_{s : l ∈ M_s} f_s c_l` of link `l` under schedule time-sharing
fractions `f : S → ℝ` ([OzdaglarSrikant2007], Eq. (22.16), p. 577). -/
@[expose] def scheduledCapacity [Fintype S] [DecidableEq L] (f : S → ℝ) (l : L) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => l ∈ W.schedule s), f s * W.capacity l

/-- Weighted price `∑_{l ∈ M_s} p_l c_l` of schedule `s` under link prices `p`
([OzdaglarSrikant2007], §22.1, p. 578). -/
@[expose] def scheduleWeight (p : L → ℝ) (s : S) : ℝ :=
  ∑ l ∈ W.schedule s, p l * W.capacity l

/-- Primal feasibility of `(x, f)` for wireless network utility maximization
([OzdaglarSrikant2007], Eqs. (22.16)–(22.18), p. 577). -/
@[expose] def IsWirelessFeasible [Fintype R] [Fintype S] [DecidableEq L]
    (x : R → ℝ) (f : S → ℝ) : Prop :=
  (∀ r, 0 ≤ x r) ∧ IsScheduleDist f ∧ ∀ l, W.linkLoad x l ≤ W.scheduledCapacity f l

/-- Joint rate-and-schedule social optimality for wireless NUM
([OzdaglarSrikant2007], §22.1, pp. 577–578). -/
@[expose] def IsWirelessOptimum [Fintype R] [Fintype S] [DecidableEq L]
    (x : R → ℝ) (f : S → ℝ) : Prop :=
  W.IsWirelessFeasible x f ∧ ∀ x' f', W.IsWirelessFeasible x' f' → W.welfare x' ≤ W.welfare x

/-- Wireless KKT optimality conditions for joint rate control and scheduling
([OzdaglarSrikant2007], §22.1, Eqs. (22.16)–(22.20), pp. 577–578). -/
structure IsWirelessKKT [Fintype R] [Fintype L] [Fintype S] [DecidableEq L]
    (x : R → ℝ) (f : S → ℝ) (p : L → ℝ) : Prop where
  /-- Primal feasibility (Eqs. (22.16)–(22.18)). -/
  feasible : W.IsWirelessFeasible x f
  /-- Dual nonnegativity of link congestion prices. -/
  price_nonneg : ∀ l, 0 ≤ p l
  /-- Complementary slackness between link prices and scheduled capacity slack. -/
  comp_slack : ∀ l, p l * (W.linkLoad x l - W.scheduledCapacity f l) = 0
  /-- Rate-control stationarity: `U'_r(x_r) ≤ q_r`. -/
  deriv_le : ∀ r, derivWithin (W.utility r) (Ici 0) (x r) ≤ W.routePrice p r
  /-- Interior rate-control equality: `U'_r(x_r) = q_r` whenever `0 < x_r`. -/
  deriv_eq_of_pos : ∀ r, 0 < x r → derivWithin (W.utility r) (Ici 0) (x r) = W.routePrice p r
  /-- Scheduling dual optimality: `f` maximizes `∑_l p_l ∑_{s : l ∈ M_s} f_s c_l` over all
  schedule distributions (Eq. (22.20)). -/
  schedule_opt : ∀ f', IsScheduleDist f' →
    ∑ l, p l * W.scheduledCapacity f' l ≤ ∑ l, p l * W.scheduledCapacity f l

/-- Wireless dual-congestion-control and scheduling price trajectory on `[0, ∞)`:
`ṗ_l(t) = (y_l(t) - ∑_{s : l ∈ M_s} f_s(t) c_l)^+_{p_l(t)}`
([OzdaglarSrikant2007], §22.1, Eq. (22.21), p. 578). -/
@[expose] def IsWirelessDualTrajectory [Fintype R] [Fintype S] [DecidableEq L]
    (x : ℝ → R → ℝ) (f : ℝ → S → ℝ) (p : ℝ → L → ℝ) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), (∀ l, 0 ≤ p t l) ∧
    ∀ l, HasDerivWithinAt (fun s => p s l)
      (projDrift (W.linkLoad (x t) l - W.scheduledCapacity (f t) l) (p t l)) (Ici 0) t

/-- Sum-interchange identity for the wireless scheduling dual subproblem
([OzdaglarSrikant2007], §22.1, p. 578, first equality):
`∑_l p_l ∑_{s : l ∈ M_s} f_s c_l = ∑_s f_s ∑_{l ∈ M_s} p_l c_l`. -/
theorem sum_price_mul_scheduledCapacity_eq [Fintype L] [Fintype S] [DecidableEq L]
    (p : L → ℝ) (f : S → ℝ) :
    ∑ l, p l * W.scheduledCapacity f l = ∑ s, f s * W.scheduleWeight p s := by
  classical
  calc ∑ l, p l * W.scheduledCapacity f l
      = ∑ l, ∑ s ∈ Finset.univ.filter (fun s => l ∈ W.schedule s), p l * (f s * W.capacity l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [scheduledCapacity, Finset.mul_sum]
    _ = ∑ l : L, ∑ s : S, if l ∈ W.schedule s then p l * (f s * W.capacity l) else 0 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_filter]
    _ = ∑ s : S, ∑ l : L, if l ∈ W.schedule s then f s * (p l * W.capacity l) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun l _ => ?_
          split_ifs <;> ring
    _ = ∑ s : S, ∑ l ∈ W.schedule s, f s * (p l * W.capacity l) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_filter]
          congr 1
          ext l
          simp
    _ = ∑ s, f s * W.scheduleWeight p s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [scheduleWeight, Finset.mul_sum]

private theorem scheduledCapacity_nonneg [Fintype S] [DecidableEq L]
    (hcap : ∀ l, 0 ≤ W.capacity l) {f : S → ℝ} (hf : IsScheduleDist f) (l : L) :
    0 ≤ W.scheduledCapacity f l :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hf.1 s) (hcap l)

private theorem scheduledCapacity_le_capacity [Fintype S] [DecidableEq L]
    (hcap : ∀ l, 0 ≤ W.capacity l) {f : S → ℝ} (hf : IsScheduleDist f) (l : L) :
    W.scheduledCapacity f l ≤ W.capacity l := by
  calc W.scheduledCapacity f l
      = (∑ s ∈ Finset.univ.filter (fun s => l ∈ W.schedule s), f s) * W.capacity l := by
          rw [scheduledCapacity, Finset.sum_mul]
    _ ≤ (∑ s : S, f s) * W.capacity l :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => hf.1 s)
            (hcap l)
    _ ≤ 1 * W.capacity l := mul_le_mul_of_nonneg_right hf.2 (hcap l)
    _ = W.capacity l := one_mul _

/-- **Max-Weight upper bound** ([OzdaglarSrikant2007], §22.1, p. 578, Eq. (22.20)): for
nonnegative link prices and capacities, every schedule distribution `f` has weighted service rate
at most the maximum-weighted-price schedule `max_s ∑_{l ∈ M_s} p_l c_l`. -/
theorem sum_price_mul_scheduledCapacity_le_maxWeight [Fintype L] [Fintype S] [DecidableEq L]
    [Nonempty S] {p : L → ℝ} (hp : ∀ l, 0 ≤ p l) (hcap : ∀ l, 0 ≤ W.capacity l)
    {f : S → ℝ} (hf : IsScheduleDist f) :
    ∑ l, p l * W.scheduledCapacity f l ≤
      Finset.univ.sup' Finset.univ_nonempty (W.scheduleWeight p) := by
  set M := Finset.univ.sup' Finset.univ_nonempty (W.scheduleWeight p)
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hM0 : 0 ≤ M :=
    (Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (hcap l)).trans
      (Finset.le_sup' (W.scheduleWeight p) (Finset.mem_univ s₀))
  calc ∑ l, p l * W.scheduledCapacity f l
      = ∑ s, f s * W.scheduleWeight p s := W.sum_price_mul_scheduledCapacity_eq p f
    _ ≤ ∑ s, f s * M := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (Finset.le_sup' (W.scheduleWeight p) (Finset.mem_univ s)) (hf.1 s)
    _ = (∑ s, f s) * M := (Finset.sum_mul ..).symm
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hf.2 hM0
    _ = M := one_mul M

/-- **Max-Weight corner-point attainment** ([OzdaglarSrikant2007], §22.1, p. 578, Eq. (22.20)):
there exists a pure schedule `s*` whose corner distribution `Pi.single s* 1` attains the exact
maximum `max_s ∑_{l ∈ M_s} p_l c_l` over all schedule distributions `IsScheduleDist`. -/
theorem exists_maxWeight_corner [Fintype L] [Fintype S] [DecidableEq L] [DecidableEq S]
    [Nonempty S] {p : L → ℝ} (hp : ∀ l, 0 ≤ p l) (hcap : ∀ l, 0 ≤ W.capacity l) :
    ∃ sStar : S, IsScheduleDist (Pi.single sStar 1) ∧
      ∑ l, p l * W.scheduledCapacity (Pi.single sStar 1) l =
        Finset.univ.sup' Finset.univ_nonempty (W.scheduleWeight p) ∧
      ∀ f, IsScheduleDist f →
        ∑ l, p l * W.scheduledCapacity f l ≤
          ∑ l, p l * W.scheduledCapacity (Pi.single sStar 1) l := by
  obtain ⟨sStar, _, hsStar⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (W.scheduleWeight p)
  have hdist : IsScheduleDist (Pi.single sStar (1 : ℝ)) := by
    refine ⟨fun s => ?_, ?_⟩
    · rcases eq_or_ne s sStar with rfl | hne
      · simp
      · simp [Pi.single_eq_of_ne hne]
    · simp
  have heq : ∑ l, p l * W.scheduledCapacity (Pi.single sStar 1) l =
      Finset.univ.sup' Finset.univ_nonempty (W.scheduleWeight p) := by
    rw [W.sum_price_mul_scheduledCapacity_eq, Finset.sum_eq_single sStar]
    · simpa only [Pi.single_eq_same, one_mul] using hsStar.symm
    · intro s _ hne; simp [Pi.single_eq_of_ne hne]
    · intro h; exact absurd (Finset.mem_univ sStar) h
  refine ⟨sStar, hdist, heq, fun f hf => ?_⟩
  rw [heq]
  exact W.sum_price_mul_scheduledCapacity_le_maxWeight hp hcap hf

/-- **Wireless KKT sufficiency and dual decomposition** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.16)–(22.20), pp. 577–578): every wireless KKT triple `(x, f, p)` for concave
differentiable utilities maximizes aggregate utility over all wireless-feasible `(x', f')`. -/
theorem IsWirelessKKT.isWirelessOptimum [Fintype R] [Fintype L] [Fintype S] [DecidableEq L]
    {W : WirelessNetworkModel R L S} {x : R → ℝ} {f : S → ℝ} {p : L → ℝ}
    (hkkt : W.IsWirelessKKT x f p)
    (hconc : ∀ r, ConcaveOn ℝ (Ici 0) (W.utility r))
    (hdiff : ∀ r, DifferentiableOn ℝ (W.utility r) (Ici 0)) :
    W.IsWirelessOptimum x f := by
  refine ⟨hkkt.feasible, fun x' f' hfeas' => ?_⟩
  have hpt : ∀ r, W.utility r (x' r) - W.routePrice p r * x' r ≤
      W.utility r (x r) - W.routePrice p r * x r := fun r => by
    have htan := (hconc r).le_add_mul_of_hasDerivWithinAt (hkkt.feasible.1 r) (hfeas'.1 r)
      ((hdiff r (x r) (hkkt.feasible.1 r)).hasDerivWithinAt)
    have hprod : (derivWithin (W.utility r) (Ici 0) (x r) - W.routePrice p r) *
        (x' r - x r) ≤ 0 := by
      rcases eq_or_lt_of_le (hkkt.feasible.1 r) with hx0 | hxpos
      · rw [← hx0, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hx0 ▸ hkkt.deriv_le r)) (hfeas'.1 r)
      · rw [hkkt.deriv_eq_of_pos r hxpos, sub_self, zero_mul]
    linarith
  have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hpt r
  simp only [Finset.sum_sub_distrib] at hsum
  rw [W.toNetworkUtilityModel.sum_routePrice_mul_eq_sum_price_mul_linkLoad p x',
    W.toNetworkUtilityModel.sum_routePrice_mul_eq_sum_price_mul_linkLoad p x] at hsum
  have hcap : ∑ l, p l * W.linkLoad x' l ≤ ∑ l, p l * W.linkLoad x l := by
    calc ∑ l, p l * W.linkLoad x' l
        ≤ ∑ l, p l * W.scheduledCapacity f' l :=
          Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hfeas'.2.2 l) (hkkt.price_nonneg l)
      _ ≤ ∑ l, p l * W.scheduledCapacity f l := hkkt.schedule_opt f' hfeas'.2.1
      _ = ∑ l, p l * W.linkLoad x l :=
          Finset.sum_congr rfl fun l _ => by linarith [hkkt.comp_slack l]
  change ∑ r, W.utility r (x' r) ≤ ∑ r, W.utility r (x r)
  linarith

/-- **Wireless KKT necessity via Farkas' lemma** ([OzdaglarSrikant2007], §22.1,
Eqs. (22.16)–(22.20), pp. 577–578): every wireless optimum `(x, f)` for utilities differentiable on
`[0, ∞)` admits nonnegative link prices `p` satisfying `W.IsWirelessKKT x f p`. -/
theorem IsWirelessOptimum.exists_isWirelessKKT [Fintype R] [Fintype L] [Fintype S] [DecidableEq L]
    {W : WirelessNetworkModel R L S} {x : R → ℝ} {f : S → ℝ}
    (hopt : W.IsWirelessOptimum x f)
    (hdiff : ∀ r, DifferentiableOn ℝ (W.utility r) (Ici 0)) :
    ∃ p : L → ℝ, W.IsWirelessKKT x f p := by
  classical
  let g : R → ℝ := fun r => derivWithin (W.utility r) (Ici 0) (x r)
  have hsched_add : ∀ a b : S → ℝ, ∀ l,
      W.scheduledCapacity (fun s => a s + b s) l =
        W.scheduledCapacity a l + W.scheduledCapacity b l := fun a b l => by
    simp only [scheduledCapacity, add_mul, Finset.sum_add_distrib]
  have hsched_smul : ∀ c : ℝ, ∀ a : S → ℝ, ∀ l,
      W.scheduledCapacity (fun s => c * a s) l = c * W.scheduledCapacity a l := fun c a l => by
    simp only [scheduledCapacity, mul_assoc, Finset.mul_sum]
  have hno : ∀ (dx : R → ℝ) (df : S → ℝ),
      (∀ r, x r = 0 → 0 ≤ dx r) →
      (∀ s, f s = 0 → 0 ≤ df s) →
      (∑ s, f s = 1 → ∑ s, df s ≤ 0) →
      (∀ l, W.linkLoad x l = W.scheduledCapacity f l →
        W.linkLoad dx l ≤ W.scheduledCapacity df l) →
      ∑ r, g r * dx r ≤ 0 := by
    intro dx df hdx hdf hsum_f hcap_l
    have hfeas_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        W.IsWirelessFeasible (fun r => x r + t * dx r) (fun s => f s + t * df s) := by
      have h1 : ∀ r : R, ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ x r + t * dx r :=
        fun r => eventually_add_mul_nonneg_nhdsGE (hopt.1.1 r) (hdx r)
      have h2 : ∀ s : S, ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ f s + t * df s :=
        fun s => eventually_add_mul_nonneg_nhdsGE (hopt.1.2.1.1 s) (hdf s)
      have h3 : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ∑ s, (f s + t * df s) ≤ 1 :=
        (eventually_add_mul_le_nhdsGE hopt.1.2.1.2 hsum_f).mono fun t ht => by
          rwa [Finset.sum_add_distrib, ← Finset.mul_sum]
      have h4 : ∀ l : L, ∀ᶠ t in 𝓝[≥] (0 : ℝ),
          W.linkLoad (fun r => x r + t * dx r) l ≤
            W.scheduledCapacity (fun s => f s + t * df s) l := fun l =>
        (eventually_add_mul_le_nhdsGE (a := W.linkLoad x l - W.scheduledCapacity f l)
          (b := W.linkLoad dx l - W.scheduledCapacity df l) (c := 0)
          (sub_nonpos.mpr (hopt.1.2.2 l))
          (fun h0 => sub_nonpos.mpr (hcap_l l (sub_eq_zero.mp h0)))).mono fun t ht => by
            rw [W.toNetworkUtilityModel.linkLoad_add, W.toNetworkUtilityModel.linkLoad_smul,
              hsched_add, hsched_smul]
            linarith
      filter_upwards [eventually_all.mpr h1, eventually_all.mpr h2, h3, eventually_all.mpr h4]
        with t ht1 ht2 ht3 ht4
      exact ⟨ht1, ⟨ht2, ht3⟩, ht4⟩
    have hmax_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        W.welfare (fun r => x r + t * dx r) ≤ W.welfare (fun r => x r + 0 * dx r) :=
      hfeas_ev.mono fun t ht => by simpa only [zero_mul, add_zero] using hopt.2 _ _ ht
    have hderiv_r : ∀ r : R, HasDerivWithinAt (fun t => W.utility r (x r + t * dx r))
        (g r * dx r) (Ici 0) 0 := fun r =>
      hasDerivWithinAt_comp_add_mul ((hdiff r (x r) (hopt.1.1 r)).hasDerivWithinAt)
        (hfeas_ev.mono fun t ht => ht.1 r)
    exact hasDerivWithinAt_nonpos_of_eventually_le
      (HasDerivWithinAt.fun_sum fun r _ => hderiv_r r) hmax_ev
  -- Encode KKT multipliers `(p : L → ℝ, lam : Unit → ℝ, sx : R → ℝ, sf : S → ℝ) ≥ 0` via Farkas.
  let A : Matrix (R ⊕ S) (L ⊕ Unit ⊕ R ⊕ S) ℝ := Matrix.of fun i j =>
    match i, j with
    | Sum.inl r, Sum.inl l =>
        if l ∈ W.route r ∧ W.linkLoad x l = W.scheduledCapacity f l then 1 else 0
    | Sum.inl _, Sum.inr (Sum.inl ()) => 0
    | Sum.inl r, Sum.inr (Sum.inr (Sum.inl r')) => if r' = r ∧ x r = 0 then -1 else 0
    | Sum.inl _, Sum.inr (Sum.inr (Sum.inr _)) => 0
    | Sum.inr s, Sum.inl l =>
        if l ∈ W.schedule s ∧ W.linkLoad x l = W.scheduledCapacity f l then -W.capacity l else 0
    | Sum.inr _, Sum.inr (Sum.inl ()) => if ∑ s', f s' = 1 then 1 else 0
    | Sum.inr _, Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr s, Sum.inr (Sum.inr (Sum.inr s')) => if s' = s ∧ f s = 0 then -1 else 0
  let b : R ⊕ S → ℝ := Sum.elim g 0
  have hfarkas : ∀ y : R ⊕ S → ℝ, 0 ≤ y ᵥ* A → 0 ≤ y ⬝ᵥ b := by
    intro y hy
    let dx : R → ℝ := fun r => -y (Sum.inl r)
    let df : S → ℝ := fun s => -y (Sum.inr s)
    have hdx : ∀ r, x r = 0 → 0 ≤ dx r := fun r hr0 => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inr (Sum.inr (Sum.inl r))) := hy _
      have hcalc : (y ᵥ* A) (Sum.inr (Sum.inr (Sum.inl r))) = dx r := by
        simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply,
          mul_zero, Finset.sum_const_zero, add_zero, dx]
        rw [Finset.sum_eq_single r]
        · simp [hr0]
        · intro r' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ r) h
      rwa [hcalc] at h1
    have hdf : ∀ s, f s = 0 → 0 ≤ df s := fun s hs0 => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inr (Sum.inr (Sum.inr s))) := hy _
      have hcalc : (y ᵥ* A) (Sum.inr (Sum.inr (Sum.inr s))) = df s := by
        simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply,
          mul_zero, Finset.sum_const_zero, zero_add, df]
        rw [Finset.sum_eq_single s]
        · simp [hs0]
        · intro s' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ s) h
      rwa [hcalc] at h1
    have hsum_f : ∑ s, f s = 1 → ∑ s, df s ≤ 0 := fun hfeq => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inr (Sum.inl ())) := hy _
      have hcalc : (y ᵥ* A) (Sum.inr (Sum.inl ())) = -(∑ s, df s) := by
        simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply,
          mul_zero, Finset.sum_const_zero, zero_add, hfeq, ↓reduceIte, mul_one, df,
          Finset.sum_neg_distrib, neg_neg]
      rw [hcalc] at h1
      linarith
    have hcap_l : ∀ l, W.linkLoad x l = W.scheduledCapacity f l →
        W.linkLoad dx l ≤ W.scheduledCapacity df l := fun l hleq => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inl l) := hy _
      have hcalc : (y ᵥ* A) (Sum.inl l) = W.scheduledCapacity df l - W.linkLoad dx l := by
        simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply,
          hleq, and_true]
        have hL : (∑ r : R, y (Sum.inl r) * if l ∈ W.route r then (1 : ℝ) else 0) =
            -W.linkLoad dx l := by
          rw [NetworkUtilityModel.linkLoad, Finset.sum_filter, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          dsimp only [dx]
          by_cases hmem : l ∈ W.route r <;> simp [hmem]
        have hS : (∑ s : S, y (Sum.inr s) * if l ∈ W.schedule s then -W.capacity l else 0) =
            W.scheduledCapacity df l := by
          rw [scheduledCapacity, Finset.sum_filter]
          refine Finset.sum_congr rfl fun s _ => ?_
          dsimp only [df]
          by_cases hmem : l ∈ W.schedule s <;> simp [hmem]
        rw [hL, hS]
        ring
      rw [hcalc] at h1
      linarith
    have hdir := hno dx df hdx hdf hsum_f hcap_l
    have hdot : y ⬝ᵥ b = -(∑ r, g r * dx r) := by
      simp only [dotProduct, Fintype.sum_sum_type, b, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, ← Finset.sum_neg_distrib, dx]
      refine Finset.sum_congr rfl fun r _ => by ring
    linarith
  obtain ⟨u, hu0, hAu⟩ := (Matrix.exists_nonneg_mulVec_eq_iff A b).mpr hfarkas
  let p : L → ℝ := fun l =>
    if W.linkLoad x l = W.scheduledCapacity f l then u (Sum.inl l) else 0
  let lam : ℝ := if ∑ s, f s = 1 then u (Sum.inr (Sum.inl ())) else 0
  have hp0 : ∀ l, 0 ≤ p l := fun l => by
    dsimp only [p]; split_ifs
    · exact hu0 (Sum.inl l)
    · exact le_rfl
  have hlam0 : 0 ≤ lam := by
    dsimp only [lam]; split_ifs
    · exact hu0 (Sum.inr (Sum.inl ()))
    · exact le_rfl
  have hcs : ∀ l, p l * (W.linkLoad x l - W.scheduledCapacity f l) = 0 := fun l => by
    dsimp only [p]; split_ifs with hl
    · rw [hl, sub_self, mul_zero]
    · rw [zero_mul]
  have hcs_lam : lam * (∑ s, f s - 1) = 0 := by
    dsimp only [lam]; split_ifs with hf1
    · rw [hf1, sub_self, mul_zero]
    · rw [zero_mul]
  have hrow_r : ∀ r, W.routePrice p r - (if x r = 0 then u (Sum.inr (Sum.inr (Sum.inl r))) else 0) =
      g r := by
    intro r
    have h1 := congrFun hAu (Sum.inl r)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply, b,
      Sum.elim_inl, zero_mul, Finset.sum_const_zero, add_zero] at h1
    have hL : (∑ l : L, (if l ∈ W.route r ∧ W.linkLoad x l = W.scheduledCapacity f l
        then (1 : ℝ) else 0) * u (Sum.inl l)) = W.routePrice p r := by
      have hfilt : W.routePrice p r = ∑ l : L, if l ∈ W.route r then p l else 0 := by
        rw [NetworkUtilityModel.routePrice,
          ← Finset.sum_filter (s := Finset.univ) (p := fun l => l ∈ W.route r) (f := p)]
        congr 1; ext l; simp
      rw [hfilt]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [p]
      by_cases h1l : l ∈ W.route r <;> by_cases h2l : W.linkLoad x l = W.scheduledCapacity f l <;>
        simp [h1l, h2l]
    have hR : (∑ r' : R, (if r' = r ∧ x r = 0 then (-1 : ℝ) else 0) *
        u (Sum.inr (Sum.inr (Sum.inl r')))) =
        -(if x r = 0 then u (Sum.inr (Sum.inr (Sum.inl r))) else 0) := by
      rw [Finset.sum_eq_single r]
      · by_cases hr0 : x r = 0 <;> simp [hr0]
      · intro r' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ r) h
    rw [hL, hR] at h1
    linarith
  have hrow_s : ∀ s, lam - W.scheduleWeight p s -
      (if f s = 0 then u (Sum.inr (Sum.inr (Sum.inr s))) else 0) = 0 := by
    intro s
    have h1 := congrFun hAu (Sum.inr s)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique, A,
      Matrix.of_apply, b, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      zero_add] at h1
    have hL : (∑ l : L, (if l ∈ W.schedule s ∧ W.linkLoad x l = W.scheduledCapacity f l
        then -W.capacity l else 0) * u (Sum.inl l)) = -W.scheduleWeight p s := by
      have hfilt : -W.scheduleWeight p s =
          ∑ l : L, if l ∈ W.schedule s then -(p l * W.capacity l) else 0 := by
        rw [scheduleWeight, ← Finset.sum_neg_distrib, ← Finset.sum_filter]
        congr 1; ext l; simp
      rw [hfilt]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [p]
      by_cases h1l : l ∈ W.schedule s <;>
        by_cases h2l : W.linkLoad x l = W.scheduledCapacity f l <;>
        simp [h1l, h2l, mul_comm]
    have hU : (if ∑ s', f s' = 1 then (1 : ℝ) else 0) * u (Sum.inr (Sum.inl ())) = lam := by
      dsimp only [lam]; split_ifs <;> simp
    have hS : (∑ s' : S, (if s' = s ∧ f s = 0 then (-1 : ℝ) else 0) *
        u (Sum.inr (Sum.inr (Sum.inr s')))) =
        -(if f s = 0 then u (Sum.inr (Sum.inr (Sum.inr s))) else 0) := by
      rw [Finset.sum_eq_single s]
      · by_cases hs0 : f s = 0 <;> simp [hs0]
      · intro s' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [hL, hU, hS] at h1
    linarith
  have hsched_opt : ∀ f', IsScheduleDist f' →
      ∑ l, p l * W.scheduledCapacity f' l ≤ ∑ l, p l * W.scheduledCapacity f l := by
    intro f' hf'
    rw [W.sum_price_mul_scheduledCapacity_eq p f', W.sum_price_mul_scheduledCapacity_eq p f]
    have hle_lam : ∀ s, W.scheduleWeight p s ≤ lam := fun s => by
      have h1 := hrow_s s
      by_cases hs0 : f s = 0
      · simp only [hs0, ↓reduceIte] at h1
        have hu_s : 0 ≤ u (Sum.inr (Sum.inr (Sum.inr s))) := hu0 _
        linarith
      · simp only [hs0, ↓reduceIte, sub_zero] at h1
        linarith
    have heq_lam : ∀ s, f s * W.scheduleWeight p s = f s * lam := fun s => by
      rcases eq_or_lt_of_le (hopt.1.2.1.1 s) with hs0 | hspos
      · rw [← hs0, zero_mul, zero_mul]
      · have h1 := hrow_s s
        simp only [hspos.ne', ↓reduceIte, sub_zero] at h1
        rw [show W.scheduleWeight p s = lam by linarith]
    calc ∑ s, f' s * W.scheduleWeight p s
        ≤ ∑ s, f' s * lam :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hle_lam s) (hf'.1 s)
      _ = (∑ s, f' s) * lam := (Finset.sum_mul ..).symm
      _ ≤ 1 * lam := mul_le_mul_of_nonneg_right hf'.2 hlam0
      _ = (∑ s, f s) * lam := by linarith [hcs_lam]
      _ = ∑ s, f s * lam := Finset.sum_mul ..
      _ = ∑ s, f s * W.scheduleWeight p s := Finset.sum_congr rfl fun s _ => (heq_lam s).symm
  refine ⟨p, hopt.1, hp0, hcs, fun r => ?_, fun r hr => ?_, hsched_opt⟩
  · have h1 := hrow_r r
    by_cases hr0 : x r = 0
    · simp only [hr0, ↓reduceIte] at h1
      have hu_r : 0 ≤ u (Sum.inr (Sum.inr (Sum.inl r))) := hu0 _
      change g r ≤ W.routePrice p r
      linarith
    · simp only [hr0, ↓reduceIte, sub_zero] at h1
      exact h1.ge
  · have h1 := hrow_r r
    simp only [hr.ne', ↓reduceIte, sub_zero] at h1
    exact h1.symm

/-- Existence of a wireless KKT primal-dual optimal triple `(x, f, p)` when every route is
nonempty, capacities are nonnegative, and utilities are differentiable on `[0, ∞)`
([OzdaglarSrikant2007], §22.1, Eqs. (22.16)–(22.20), pp. 577–578). -/
theorem exists_isWirelessKKT [Fintype R] [Fintype L] [Fintype S] [DecidableEq L]
    (hroute : ∀ r, (W.route r).Nonempty) (hcap : ∀ l, 0 ≤ W.capacity l)
    (hdiff : ∀ r, DifferentiableOn ℝ (W.utility r) (Ici 0)) :
    ∃ x f p, W.IsWirelessKKT x f p ∧ W.IsWirelessOptimum x f := by
  let K : Set ((R → ℝ) × (S → ℝ)) := {z | W.IsWirelessFeasible z.1 z.2}
  have hK_compact : IsCompact K := by
    have hbox : IsCompact ((Set.pi Set.univ fun r : R =>
        Icc (0 : ℝ) (∑ l ∈ W.route r, W.capacity l)) ×ˢ
        (Set.pi Set.univ fun _ : S => Icc (0 : ℝ) 1)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
    refine hbox.of_isClosed_subset ?_ ?_
    · have hcont_fst : ∀ r : R, Continuous fun z : (R → ℝ) × (S → ℝ) => z.1 r := fun r =>
        (continuous_apply r).comp continuous_fst
      have hcont_snd : ∀ s : S, Continuous fun z : (R → ℝ) × (S → ℝ) => z.2 s := fun s =>
        (continuous_apply s).comp continuous_snd
      have h1 : IsClosed {z : (R → ℝ) × (S → ℝ) | ∀ r, 0 ≤ z.1 r} := by
        simpa only [Set.ofPred_forall] using isClosed_iInter fun r =>
          isClosed_le continuous_const (hcont_fst r)
      have h2 : IsClosed {z : (R → ℝ) × (S → ℝ) | ∀ s, 0 ≤ z.2 s} := by
        simpa only [Set.ofPred_forall] using isClosed_iInter fun s =>
          isClosed_le continuous_const (hcont_snd s)
      have h3 : IsClosed {z : (R → ℝ) × (S → ℝ) | ∑ s, z.2 s ≤ 1} :=
        isClosed_le (continuous_finsetSum _ fun s _ => hcont_snd s) continuous_const
      have hcont_mul : ∀ s l, Continuous fun z : (R → ℝ) × (S → ℝ) => z.2 s * W.capacity l :=
        fun s l => (hcont_snd s).mul continuous_const
      have h4 : IsClosed {z : (R → ℝ) × (S → ℝ) |
          ∀ l, W.linkLoad z.1 l ≤ W.scheduledCapacity z.2 l} := by
        simpa only [Set.ofPred_forall, NetworkUtilityModel.linkLoad, scheduledCapacity] using
          isClosed_iInter fun l => isClosed_le
            (continuous_finsetSum _ fun r _ => hcont_fst r)
            (continuous_finsetSum _ fun s _ => hcont_mul s l)
      have hKeq : K = {z : (R → ℝ) × (S → ℝ) | ∀ r, 0 ≤ z.1 r} ∩
          (({z : (R → ℝ) × (S → ℝ) | ∀ s, 0 ≤ z.2 s} ∩ {z : (R → ℝ) × (S → ℝ) | ∑ s, z.2 s ≤ 1}) ∩
            {z : (R → ℝ) × (S → ℝ) | ∀ l, W.linkLoad z.1 l ≤ W.scheduledCapacity z.2 l}) := by
        ext ⟨x, f⟩
        simp only [K, IsWirelessFeasible, IsScheduleDist, mem_inter_iff, mem_ofPred_eq,
          and_assoc]
      rw [hKeq]
      exact h1.inter ((h2.inter h3).inter h4)
    · rintro ⟨x, f⟩ ⟨hx0, hf, hcap_l⟩
      refine ⟨fun r _ => ⟨hx0 r, ?_⟩, fun s _ => ⟨hf.1 s, ?_⟩⟩
      · obtain ⟨l, hl⟩ := hroute r
        have h1 : x r ≤ W.linkLoad x l :=
          Finset.single_le_sum (f := x) (fun r' _ => hx0 r')
            (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hl⟩)
        have h2 : W.capacity l ≤ ∑ l' ∈ W.route r, W.capacity l' :=
          Finset.single_le_sum (fun l' _ => hcap l') hl
        exact ((h1.trans (hcap_l l)).trans (W.scheduledCapacity_le_capacity hcap hf l)).trans h2
      · exact (Finset.single_le_sum (fun s' _ => hf.1 s') (Finset.mem_univ s)).trans hf.2
  have hK_ne : K.Nonempty := ⟨(0, 0), fun _ => le_rfl, ⟨fun _ => le_rfl, by simp⟩, fun l => by
    simp [NetworkUtilityModel.linkLoad, scheduledCapacity]⟩
  have hcont : ContinuousOn (fun z : (R → ℝ) × (S → ℝ) => W.welfare z.1) K :=
    continuousOn_finsetSum _ fun r _ =>
      (hdiff r).continuousOn.comp
        ((continuous_apply r).comp
          (continuous_fst : Continuous fun z : (R → ℝ) × (S → ℝ) => z.1)).continuousOn
        fun z hz => hz.1 r
  obtain ⟨⟨x, f⟩, hxf_mem, hxf_max⟩ := hK_compact.exists_isMaxOn hK_ne hcont
  have hopt : W.IsWirelessOptimum x f :=
    ⟨hxf_mem, fun x' f' h' => hxf_max (show (x', f') ∈ K from h')⟩
  obtain ⟨p, hkkt⟩ := hopt.exists_isWirelessKKT hdiff
  exact ⟨x, f, p, hkkt, hopt⟩

/-- **Wireless Max-Weight Lyapunov drift inequality** ([OzdaglarSrikant2007], §22.1, Eq. (22.21),
p. 578): along any wireless dual trajectory where `f t` is a maximum-weighted-price schedule
distribution at `p t`, the derivative of `lyapunov pStar (p t)` satisfies
`dV/dt ≤ ∑_r (q_r(t) - q*_r) (x_r(t) - x*_r)`. -/
theorem IsWirelessDualTrajectory.hasDerivWithinAt_lyapunov_le [Fintype R] [Fintype L] [Fintype S]
    [DecidableEq L] {W : WirelessNetworkModel R L S}
    {x : ℝ → R → ℝ} {f : ℝ → S → ℝ} {p : ℝ → L → ℝ}
    (htraj : W.IsWirelessDualTrajectory x f p)
    {xStar : R → ℝ} {fStar : S → ℝ} {pStar : L → ℝ}
    (hkkt : W.IsWirelessKKT xStar fStar pStar)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ))
    (hft_dist : IsScheduleDist (f t))
    (hft_max : ∀ f', IsScheduleDist f' →
      ∑ l, p t l * W.scheduledCapacity f' l ≤ ∑ l, p t l * W.scheduledCapacity (f t) l) :
    ∃ D, HasDerivWithinAt (fun s => lyapunov pStar (p s)) D (Ici 0) t ∧
      D ≤ ∑ r, (W.routePrice (p t) r - W.routePrice pStar r) * (x t r - xStar r) := by
  refine ⟨∑ l, (p t l - pStar l) *
      projDrift (W.linkLoad (x t) l - W.scheduledCapacity (f t) l) (p t l),
    hasDerivWithinAt_lyapunov (htraj t ht).2, ?_⟩
  have hsched_term : ∑ l, (p t l - pStar l) *
      (W.scheduledCapacity fStar l - W.scheduledCapacity (f t) l) ≤ 0 := by
    have hsplit : ∑ l, (p t l - pStar l) *
        (W.scheduledCapacity fStar l - W.scheduledCapacity (f t) l) =
        (∑ l, p t l * W.scheduledCapacity fStar l - ∑ l, p t l * W.scheduledCapacity (f t) l) +
        (∑ l, pStar l * W.scheduledCapacity (f t) l -
          ∑ l, pStar l * W.scheduledCapacity fStar l) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hsplit]
    linarith [hft_max fStar hkkt.feasible.2.1, hkkt.schedule_opt (f t) hft_dist]
  have hcs_term : ∑ l, (p t l - pStar l) *
      (W.linkLoad xStar l - W.scheduledCapacity fStar l) ≤ 0 := by
    refine Finset.sum_nonpos fun l _ => ?_
    have h1 : p t l * (W.linkLoad xStar l - W.scheduledCapacity fStar l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ((htraj t ht).1 l) (sub_nonpos.mpr (hkkt.feasible.2.2 l))
    linarith [hkkt.comp_slack l]
  calc ∑ l, (p t l - pStar l) *
          projDrift (W.linkLoad (x t) l - W.scheduledCapacity (f t) l) (p t l)
      ≤ ∑ l, (p t l - pStar l) * (W.linkLoad (x t) l - W.scheduledCapacity (f t) l) :=
        Finset.sum_le_sum fun l _ => mul_projDrift_le ((htraj t ht).1 l) (hkkt.price_nonneg l)
    _ = (∑ l, (p t l - pStar l) * (W.linkLoad (x t) l - W.linkLoad xStar l)) +
        (∑ l, (p t l - pStar l) * (W.linkLoad xStar l - W.scheduledCapacity fStar l)) +
        (∑ l, (p t l - pStar l) * (W.scheduledCapacity fStar l - W.scheduledCapacity (f t) l)) := by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ ∑ l, (p t l - pStar l) * (W.linkLoad (x t) l - W.linkLoad xStar l) := by linarith
    _ = ∑ r, (W.routePrice (p t) r - W.routePrice pStar r) * (x t r - xStar r) := by
        simpa only [W.toNetworkUtilityModel.routePrice_sub,
          W.toNetworkUtilityModel.linkLoad_sub] using
          (W.toNetworkUtilityModel.sum_routePrice_mul_eq_sum_price_mul_linkLoad
            (fun l => p t l - pStar l) (fun r => x t r - xStar r)).symm

/-- **Lyapunov stability of wireless Max-Weight dual congestion control** ([OzdaglarSrikant2007],
§22.1, Eqs. (22.15), (22.21), p. 578): `lyapunov pStar ∘ p` is nonincreasing on `[0, ∞)`. -/
theorem IsWirelessDualTrajectory.antitoneOn_lyapunov_of_myopic [Fintype R] [Fintype L] [Fintype S]
    [DecidableEq L] {W : WirelessNetworkModel R L S}
    {x : ℝ → R → ℝ} {f : ℝ → S → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {fStar : S → ℝ} {pStar : L → ℝ}
    (hU : ∀ r, IsAdmissibleUtility (W.utility r))
    (hkkt : W.IsWirelessKKT xStar fStar pStar)
    (hxStar_eq : ∀ r, derivWithin (W.utility r) (Ici 0) (xStar r) = W.routePrice pStar r)
    (htraj : W.IsWirelessDualTrajectory x f p)
    (hf_dist : ∀ t ∈ Ici (0 : ℝ), IsScheduleDist (f t))
    (hf_max : ∀ t ∈ Ici (0 : ℝ), ∀ f', IsScheduleDist f' →
      ∑ l, p t l * W.scheduledCapacity f' l ≤ ∑ l, p t l * W.scheduledCapacity (f t) l)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      derivWithin (W.utility r) (Ici 0) (x t r) = W.routePrice (p t) r) :
    AntitoneOn (fun t => lyapunov pStar (p t)) (Ici 0) :=
  antitoneOn_lyapunov_of_drift_nonpos fun t ht => by
    obtain ⟨D, hD_der, hD_le⟩ :=
      htraj.hasDerivWithinAt_lyapunov_le hkkt ht (hf_dist t ht) (hf_max t ht)
    exact ⟨D, hD_der, hD_le.trans
      (W.toNetworkUtilityModel.myopic_rate_drift_nonpos hU (hx0 t ht) hkkt.feasible.1
        (hctrl t ht) hxStar_eq)⟩

/-- **Global asymptotic convergence of wireless Max-Weight dual congestion control**
([OzdaglarSrikant2007], §22.1, Eqs. (22.15), (22.21), p. 578): for strictly concave admissible
utilities, any wireless Max-Weight trajectory converges globally: `x(t) → x*`, `q(t) → q*`, and
under full row rank (`Function.Injective W.routePrice`) `p(t) → p*`. -/
theorem IsWirelessDualTrajectory.tendsto_of_myopic [Fintype R] [Fintype L] [Fintype S]
    [DecidableEq L] {W : WirelessNetworkModel R L S}
    {x : ℝ → R → ℝ} {f : ℝ → S → ℝ} {p : ℝ → L → ℝ}
    {xStar : R → ℝ} {fStar : S → ℝ} {pStar : L → ℝ}
    (hroute : ∀ r, (W.route r).Nonempty) (hcap : ∀ l, 0 ≤ W.capacity l)
    (hU : ∀ r, IsAdmissibleUtility (W.utility r))
    (hstrict : ∀ r, StrictConcaveOn ℝ (Ici 0) (W.utility r))
    (hkkt : W.IsWirelessKKT xStar fStar pStar)
    (hxStar_eq : ∀ r, derivWithin (W.utility r) (Ici 0) (xStar r) = W.routePrice pStar r)
    (htraj : W.IsWirelessDualTrajectory x f p)
    (hf_dist : ∀ t ∈ Ici (0 : ℝ), IsScheduleDist (f t))
    (hf_max : ∀ t ∈ Ici (0 : ℝ), ∀ f', IsScheduleDist f' →
      ∑ l, p t l * W.scheduledCapacity f' l ≤ ∑ l, p t l * W.scheduledCapacity (f t) l)
    (hx0 : ∀ t ∈ Ici (0 : ℝ), ∀ r, 0 ≤ x t r)
    (hctrl : ∀ t ∈ Ici (0 : ℝ), ∀ r,
      derivWithin (W.utility r) (Ici 0) (x t r) = W.routePrice (p t) r) :
    Tendsto x atTop (𝓝 xStar) ∧
      Tendsto (fun t => W.routePrice (p t)) atTop (𝓝 (W.routePrice pStar)) ∧
      (Function.Injective W.routePrice → Tendsto p atTop (𝓝 pStar)) :=
  W.toNetworkUtilityModel.tendsto_of_myopic_drift hroute hcap hU hstrict hkkt.feasible.1 hxStar_eq
    htraj (fun t ht l => ⟨W.scheduledCapacity_nonneg hcap (hf_dist t ht) l,
      W.scheduledCapacity_le_capacity hcap (hf_dist t ht) l⟩) hx0 hctrl
    fun _ ht => htraj.hasDerivWithinAt_lyapunov_le hkkt ht (hf_dist _ ht) (hf_max _ ht)

end WirelessNetworkModel

end Cslib.GameTheory
