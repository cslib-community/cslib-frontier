/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Monotone.Basic
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Kelly's proportional allocation mechanism and the `3/4` efficiency theorem

A single infinitely divisible resource of capacity `C > 0` is shared among a finite set `ι` of
users with utility functions `U_i : [0, ∞) → ℝ` ([Johari2007], §21.2; [Kelly1997];
[JohariTsitsiklis2004]). Under **Kelly's proportional allocation mechanism**, each user `i` submits
a nonnegative bid `w_i ≥ 0`, the market-clearing price is `p = (∑_j w_j) / C`, and user `i`
receives allocation `d_i = C · w_i / (∑_j w_j)` (with `d_i = 0` when `∑_j w_j = 0`) and quasilinear
payoff `U_i(d_i) - w_i`.

When users are **price-taking**, a competitive equilibrium `(w, μ)` always exists for admissible
concave strictly increasing utilities (`IsAdmissibleUtility`) and maximizes aggregate social
welfare `∑_i U_i(d_i)` over feasible allocations `SYSTEM` ([Johari2007], Theorem 21.1;
[Kelly1997]). When users are **price-anticipating** and `|ι| ≥ 2`, the resulting strategic game
admits a unique Nash equilibrium `w`, whose allocation `d` uniquely solves the strictly concave
potential problem `GAME` maximizing `∑_i Û_i(d_i)` where
`Û_i(d_i) = (1 - d_i / C) U_i(d_i) + (1 / C) ∫_0^{d_i} U_i(z) dz` ([Johari2007], Theorem 21.2;
[JohariTsitsiklis2004]) and satisfies the corresponding variational inequality ([Johari2007],
Corollary 21.3).

The headline efficiency theorem of Johari and Tsitsiklis ([JohariTsitsiklis2004]; [Johari2007],
Theorem 21.4) shows that if each admissible utility satisfies `U_i(0) ≥ 0`, then every Nash
equilibrium achieves at least `3/4` of the maximum feasible aggregate utility (efficiency loss at
most `1/4`, i.e., price of anarchy at most `4/3`). Moreover, this constant `3/4` is tight: an
explicit family of `(n + 1)`-user linear-utility instances has unique Nash equilibrium achieving
exact welfare `3/4 + 1 / (4 (2 n - 1))` against optimal welfare `1`, approaching `3/4` arbitrarily
closely as `n → ∞`.

`IsAdmissibleUtility` requires concavity, strict monotonicity, and differentiability within
`[0, ∞)` (i.e., differentiability on `(0, ∞)` with a finite right derivative at `0`). This matches
Assumption 1 of [Johari2007], §21.2, without needing an explicit continuity assumption on the
derivative (which is automatic for differentiable concave functions on `(0, ∞)`).

`KellyGame.IsNashEquilibrium` maximizes quasilinear payoffs directly over nonnegative real bids
on `ι → ℝ` rather than wrapping `CostGame ι (fun _ => {t : ℝ // 0 ≤ t})`
(`CslibFrontier.GameTheory.Strategic.Basic`), keeping unilateral deviations and single-variable
convex calculus over `ℝ` subtype-free.

## Main definitions

* `Cslib.GameTheory.IsAdmissibleUtility`: concave, strictly increasing utilities differentiable on
  `[0, ∞)` (Assumption 1 of [Johari2007], §21.2).
* `Cslib.GameTheory.KellyGame`: a single-resource divisible allocation instance with fields
  `capacity` and `utility`.
* `Cslib.GameTheory.KellyGame.IsFeasibleAllocation`, `welfare`, `IsSocialOptimum`: the `SYSTEM`
  problem.
* `Cslib.GameTheory.KellyGame.price`, `allocation`, `payoff`: Kelly's proportional allocation rule.
* `Cslib.GameTheory.KellyGame.IsCompetitiveEquilibrium`: price-taking competitive equilibrium.
* `Cslib.GameTheory.KellyGame.IsNashEquilibrium`: price-anticipating Nash equilibrium.
* `Cslib.GameTheory.KellyGame.modifiedUtility`, `modifiedWelfare`, `IsGameOptimum`: the `GAME`
  optimization problem.
* `Cslib.GameTheory.KellyGame.kellyTightGame`: explicit `(n + 1)`-user linear tightness instances.

## Main results

* `Cslib.GameTheory.KellyGame.IsCompetitiveEquilibrium.isSocialOptimum`: every competitive
  equilibrium maximizes aggregate welfare (First Welfare Theorem).
* `Cslib.GameTheory.KellyGame.exists_isCompetitiveEquilibrium`: existence of a price-taking
  competitive equilibrium solving `SYSTEM` ([Johari2007], Theorem 21.1; [Kelly1997]), and
  `existsUnique_isCompetitiveEquilibrium_of_strictConcaveOn` for uniqueness under strict concavity.
* `Cslib.GameTheory.KellyGame.isNashEquilibrium_iff_kkt`: first-order KKT characterization of
  price-anticipating Nash equilibria.
* `Cslib.GameTheory.KellyGame.existsUnique_isNashEquilibrium`: existence and uniqueness of the
  price-anticipating Nash equilibrium and equivalence with the unique maximizer of `GAME`
  ([Johari2007], Theorem 21.2; [JohariTsitsiklis2004]).
* `Cslib.GameTheory.KellyGame.IsNashEquilibrium.variational_inequality`: variational inequality
  characterizing the Nash allocation ([Johari2007], Corollary 21.3).
* `Cslib.GameTheory.KellyGame.IsNashEquilibrium.three_fourths_welfare_le`: the Johari–Tsitsiklis
  `3/4` worst-case efficiency guarantee ([JohariTsitsiklis2004]; [Johari2007], Theorem 21.4).
* `Cslib.GameTheory.KellyGame.exists_nash_welfare_lt_three_fourths_add`: tightness of `3/4` to
  within every `ε > 0` on linear utilities ([JohariTsitsiklis2004]; [Johari2007], Theorem 21.4).

## References

* [Johari2007]
* [JohariTsitsiklis2004]
* [Kelly1997]
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Cslib.GameTheory

/-! ### Admissible utility functions -/

/-- An admissible utility function for the divisible single-resource allocation model: concave,
strictly increasing, and differentiable within `[0, ∞)` (equivalently differentiable on `(0, ∞)`
with a finite right derivative at `0`). This formalizes Assumption 1 of [Johari2007], §21.2. -/
structure IsAdmissibleUtility (u : ℝ → ℝ) : Prop where
  /-- Concavity on `[0, ∞)`. -/
  concaveOn : ConcaveOn ℝ (Ici 0) u
  /-- Strict monotonicity on `[0, ∞)`. -/
  strictMonoOn : StrictMonoOn u (Ici 0)
  /-- Differentiability within `[0, ∞)` (including a finite right derivative at `0`). -/
  differentiableOn : DifferentiableOn ℝ u (Ici 0)

/-! ### First-order local-maximum helper -/

private theorem hasDerivWithinAt_nonpos_of_isMaxOn_Icc {φ : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hd : HasDerivWithinAt φ d (Ici 0) 0) (hmax : ∀ t ∈ Icc 0 δ, φ t ≤ φ 0) : d ≤ 0 := by
  have hlim : Tendsto (slope φ 0) (𝓝[>] 0) (𝓝 d) := by
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp (hd.mono Ioi_subset_Ici_self)
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using h1
  have hle : ∀ᶠ t in 𝓝[>] 0, slope φ 0 t ≤ 0 := by
    filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
    rw [slope_def_field, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax t ⟨ht.1.le, ht.2⟩)) ht.1.le
  exact le_of_tendsto hlim hle

namespace IsAdmissibleUtility

theorem continuousOn {u : ℝ → ℝ} (hu : IsAdmissibleUtility u) : ContinuousOn u (Ici 0) :=
  hu.differentiableOn.continuousOn

theorem hasDerivWithinAt {u : ℝ → ℝ} (hu : IsAdmissibleUtility u) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt u (derivWithin u (Ici 0) x) (Ici 0) x :=
  (hu.differentiableOn x hx).hasDerivWithinAt

/-- First-order concavity inequality on `[0, ∞)`: `u y ≤ u x + u'(x) (y - x)`. -/
theorem le_add_derivWithin {u : ℝ → ℝ} (hu : IsAdmissibleUtility u) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    u y ≤ u x + derivWithin u (Ici 0) x * (y - x) :=
  hu.concaveOn.le_add_mul_of_hasDerivWithinAt hx hy (hu.hasDerivWithinAt hx)

/-- The marginal utility `u'` is nonincreasing on `[0, ∞)`. -/
theorem derivWithin_antitoneOn {u : ℝ → ℝ} (hu : IsAdmissibleUtility u) :
    AntitoneOn (derivWithin u (Ici 0)) (Ici 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have h1 := hu.le_add_derivWithin hx hy
    have h2 := hu.le_add_derivWithin hy hx
    nlinarith

/-- Every concave, strictly increasing, differentiable function on `[0, ∞)` has strictly positive
marginal utility everywhere on `[0, ∞)`. -/
theorem derivWithin_pos {u : ℝ → ℝ} (hu : IsAdmissibleUtility u) {x : ℝ} (hx : 0 ≤ x) :
    0 < derivWithin u (Ici 0) x := by
  have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
  linarith [hu.strictMonoOn hx hx1 (by linarith), hu.le_add_derivWithin hx hx1]

end IsAdmissibleUtility

/-! ### Kelly resource allocation model -/

/-- A single-resource divisible allocation problem with user type `ι`, total capacity `capacity`,
and utility functions `utility i : ℝ → ℝ` on `[0, ∞)` ([Johari2007], §21.2). -/
structure KellyGame (ι : Type*) where
  /-- Total divisible capacity `C` of the resource. -/
  capacity : ℝ
  /-- Utility function `U_i` of user `i` on `[0, ∞)`. -/
  utility : ι → ℝ → ℝ

namespace KellyGame

variable {ι : Type*} (G : KellyGame ι)

/-- An allocation vector `d : ι → ℝ` is feasible for `SYSTEM` if it is nonnegative and its sum
does not exceed the resource capacity `G.capacity`. -/
@[expose] def IsFeasibleAllocation [Fintype ι] (d : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ ∑ i, d i ≤ G.capacity

/-- Aggregate social welfare `∑_i U_i(d_i)` of an allocation `d`. -/
@[expose] def welfare [Fintype ι] (d : ι → ℝ) : ℝ :=
  ∑ i, G.utility i (d i)

/-- A feasible allocation `d` solves `SYSTEM` if it maximizes aggregate welfare over all feasible
allocations ([Johari2007], §21.2). -/
@[expose] def IsSocialOptimum [Fintype ι] (d : ι → ℝ) : Prop :=
  G.IsFeasibleAllocation d ∧ ∀ x, G.IsFeasibleAllocation x → G.welfare x ≤ G.welfare d

/-- The market-clearing price `p(w) = (∑_j w_j) / C` induced by bid vector `w`. -/
@[expose] noncomputable def price [Fintype ι] (w : ι → ℝ) : ℝ :=
  (∑ j, w j) / G.capacity

/-- Kelly's proportional allocation rule: user `i` receives `C · w_i / (∑_j w_j)`, which equals `0`
when `∑_j w_j = 0` ([Johari2007], §21.2; [Kelly1997]). -/
@[expose] noncomputable def allocation [Fintype ι] (w : ι → ℝ) (i : ι) : ℝ :=
  G.capacity * w i / ∑ j, w j

/-- Quasilinear payoff `U_i(d_i(w)) - w_i` of user `i` in the price-anticipating Kelly game. -/
@[expose] noncomputable def payoff [Fintype ι] (w : ι → ℝ) (i : ι) : ℝ :=
  G.utility i (G.allocation w i) - w i

/-- A **price-taking competitive equilibrium** `(w, μ)` consists of nonnegative bids `w` and a
positive market-clearing price `μ = (∑_j w_j) / C` such that each user `i` maximizes
`U_i(t / μ) - t` over `t ≥ 0` at `t = w_i` ([Johari2007], §21.2, Theorem 21.1). -/
@[expose] def IsCompetitiveEquilibrium [Fintype ι] (w : ι → ℝ) (μ : ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ 0 < μ ∧ μ = G.price w ∧
    ∀ i (t : ℝ), 0 ≤ t → G.utility i (t / μ) - t ≤ G.utility i (w i / μ) - w i

/-- A **price-anticipating Nash equilibrium** `w` is a nonnegative bid profile from which no user
can strictly improve its payoff by unilaterally changing its bid to any `t ≥ 0` ([Johari2007],
§21.2, Theorem 21.2). -/
@[expose] def IsNashEquilibrium [Fintype ι] [DecidableEq ι] (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ i (t : ℝ), 0 ≤ t → G.payoff (Function.update w i t) i ≤ G.payoff w i

/-- The modified utility `Û_i(x) = (1 - x / C) U_i(x) + (1 / C) ∫_0^x U_i(z) dz` defining the
potential optimization problem `GAME` ([Johari2007], §21.2, Theorem 21.2). -/
@[expose] noncomputable def modifiedUtility (i : ι) (x : ℝ) : ℝ :=
  (1 - x / G.capacity) * G.utility i x + (1 / G.capacity) * ∫ z in (0 : ℝ)..x, G.utility i z

/-- Aggregate modified welfare `∑_i Û_i(d_i)` (the objective of `GAME`). -/
@[expose] noncomputable def modifiedWelfare [Fintype ι] (d : ι → ℝ) : ℝ :=
  ∑ i, G.modifiedUtility i (d i)

/-- A feasible allocation `d` solves `GAME` if it maximizes aggregate modified welfare over all
feasible allocations ([Johari2007], §21.2, Theorem 21.2). -/
@[expose] def IsGameOptimum [Fintype ι] (d : ι → ℝ) : Prop :=
  G.IsFeasibleAllocation d ∧
    ∀ x, G.IsFeasibleAllocation x → G.modifiedWelfare x ≤ G.modifiedWelfare d

/-! ### Basic properties of proportional allocation -/

section Basic

variable [Fintype ι]

theorem allocation_eq_zero_of_sum_eq_zero {w : ι → ℝ} (hw : ∑ j, w j = 0) (i : ι) :
    G.allocation w i = 0 := by
  simp [allocation, hw]

theorem allocation_eq_div_price {w : ι → ℝ} (hC : G.capacity ≠ 0) (i : ι) :
    G.allocation w i = w i / G.price w := by
  simp only [allocation, price]
  by_cases hW : ∑ j, w j = 0
  · simp [hW]
  · field_simp

theorem allocation_nonneg {w : ι → ℝ} (hC : 0 ≤ G.capacity) (hw : ∀ j, 0 ≤ w j) (i : ι) :
    0 ≤ G.allocation w i := by
  unfold allocation
  have hW : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => hw j
  exact div_nonneg (mul_nonneg hC (hw i)) hW

theorem sum_allocation_eq_capacity {w : ι → ℝ} (hW : ∑ j, w j ≠ 0) :
    ∑ i, G.allocation w i = G.capacity := by
  simp only [allocation]
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_cancel_right₀ _ hW]

theorem isFeasibleAllocation_allocation {w : ι → ℝ} (hC : 0 ≤ G.capacity) (hw : ∀ j, 0 ≤ w j) :
    G.IsFeasibleAllocation (G.allocation w) := by
  refine ⟨G.allocation_nonneg hC hw, ?_⟩
  by_cases hW : ∑ j, w j = 0
  · simp [allocation_eq_zero_of_sum_eq_zero, hW, hC]
  · rw [G.sum_allocation_eq_capacity hW]

theorem allocation_le_capacity {w : ι → ℝ} (hC : 0 ≤ G.capacity) (hw : ∀ j, 0 ≤ w j) (i : ι) :
    G.allocation w i ≤ G.capacity := by
  have hf := G.isFeasibleAllocation_allocation hC hw
  exact (Finset.single_le_sum (fun j _ => hf.1 j) (Finset.mem_univ i)).trans hf.2

theorem isFeasibleAllocation_le_capacity {d : ι → ℝ} (hd : G.IsFeasibleAllocation d) (i : ι) :
    d i ≤ G.capacity :=
  (Finset.single_le_sum (fun j _ => hd.1 j) (Finset.mem_univ i)).trans hd.2

end Basic

/-! ### Simplex optimization and shared KKT characterization -/

section SimplexKKT

variable [Fintype ι]

/-- The feasible allocation simplex `{d | G.IsFeasibleAllocation d}` is compact. -/
theorem isCompact_isFeasibleAllocation {G : KellyGame ι} :
    IsCompact {d : ι → ℝ | G.IsFeasibleAllocation d} := by
  refine (isCompact_univ_pi fun _ : ι => isCompact_Icc).of_isClosed_subset
    (?_) (fun d hd i _ => ⟨hd.1 i, G.isFeasibleAllocation_le_capacity hd i⟩)
  refine (?_ : IsClosed {d : ι → ℝ | ∀ i, 0 ≤ d i}).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  simpa only [Set.ofPred_forall] using
    isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

private theorem nonempty_feasibleAllocation {G : KellyGame ι} (hC : 0 ≤ G.capacity) :
    ({d : ι → ℝ | G.IsFeasibleAllocation d}).Nonempty :=
  ⟨0, fun _ => le_rfl, by simp [hC]⟩

private theorem exists_simplex_maximizer {G : KellyGame ι} (hC : 0 ≤ G.capacity)
    {f : ι → ℝ → ℝ} (hcont : ∀ i, ContinuousOn (f i) (Icc 0 G.capacity)) :
    ∃ d, G.IsFeasibleAllocation d ∧
      ∀ x, G.IsFeasibleAllocation x → ∑ i, f i (x i) ≤ ∑ i, f i (d i) := by
  obtain ⟨d, hd, hmax⟩ := isCompact_isFeasibleAllocation.exists_isMaxOn
    (nonempty_feasibleAllocation hC) <| continuousOn_finsetSum _ fun i _ =>
      (hcont i).comp (continuous_apply i).continuousOn fun d hd =>
        ⟨hd.1 i, G.isFeasibleAllocation_le_capacity hd i⟩
  exact ⟨d, hd, fun x hx => hmax hx⟩

private theorem sum_comp_update_eq [DecidableEq ι] (g : ι → ℝ → ℝ) (d : ι → ℝ)
    (i₀ : ι) (v : ℝ) :
    ∑ i, g i (Function.update d i₀ v i) = ∑ i, g i (d i) - g i₀ (d i₀) + g i₀ v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase _ (fun i => g i (d i)) (Finset.mem_univ i₀), Function.update_self,
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
  ring

private theorem exists_pos_of_sum_pos {d : ι → ℝ} (h : 0 < ∑ i, d i) :
    ∃ i, 0 < d i := by
  by_contra hall
  push Not at hall
  linarith [Finset.sum_nonpos (s := Finset.univ) fun i _ => hall i]

private theorem simplex_maximizer_sum_eq_capacity [Nonempty ι] {G : KellyGame ι}
    {f : ι → ℝ → ℝ} (hmono : ∀ i, StrictMonoOn (f i) (Icc 0 G.capacity))
    {d : ι → ℝ} (hd : G.IsFeasibleAllocation d)
    (hmax : ∀ x, G.IsFeasibleAllocation x → ∑ i, f i (x i) ≤ ∑ i, f i (d i)) :
    ∑ i, d i = G.capacity := by
  classical
  refine le_antisymm hd.2 (not_lt.mp fun hlt => ?_)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set δ := G.capacity - ∑ i, d i
  set x := Function.update d i₀ (d i₀ + δ)
  have hx_feas : G.IsFeasibleAllocation x := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = i₀
      · subst hi; simp only [x, Function.update_self]; linarith [hd.1 i]
      · simp only [x, Function.update_of_ne hi]; exact hd.1 i
    · have := sum_comp_update_eq (fun _ t => t) d i₀ (d i₀ + δ)
      linarith
  have hdi₀ : d i₀ ∈ Icc 0 G.capacity := ⟨hd.1 i₀, G.isFeasibleAllocation_le_capacity hd i₀⟩
  have hxi₀ : d i₀ + δ ∈ Icc 0 G.capacity :=
    ⟨by linarith [hd.1 i₀],
      by linarith [Finset.add_sum_erase Finset.univ d (Finset.mem_univ i₀),
        Finset.sum_nonneg (s := Finset.univ.erase i₀) fun j _ => hd.1 j]⟩
  have hle := hmax x hx_feas
  rw [sum_comp_update_eq f d i₀ (d i₀ + δ)] at hle
  linarith [hmono i₀ hdi₀ hxi₀ (by linarith : d i₀ < d i₀ + δ)]

/-- Pairwise first-order optimality condition on the simplex: at a social optimum `d`, if user `i`
receives positive allocation `d i > 0`, shifting infinitesimal capacity from `i` to `j` cannot
improve welfare, so `dj' ≤ di'`. -/
theorem IsSocialOptimum.swap_deriv_le {G : KellyGame ι} {d : ι → ℝ} (hd : G.IsSocialOptimum d)
    {i j : ι} (hij : i ≠ j) (hdi : 0 < d i) {di' dj' : ℝ}
    (hderiv_i : HasDerivWithinAt (G.utility i) di' (Icc 0 G.capacity) (d i))
    (hderiv_j : HasDerivWithinAt (G.utility j) dj' (Icc 0 G.capacity) (d j)) :
    dj' ≤ di' := by
  classical
  set φ : ℝ → ℝ := fun t => G.utility i (d i - t) + G.utility j (d j + t)
  have hsum_ij : d i + d j ≤ G.capacity := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset ι))
      fun k _ _ => hd.1.1 k
    rw [Finset.sum_pair hij] at hle
    exact hle.trans hd.1.2
  have hφ_i : HasDerivWithinAt (fun t => G.utility i (d i - t)) (-di') (Icc 0 (d i)) 0 := by
    have hfi : HasDerivWithinAt (G.utility i) di' (Icc 0 G.capacity) (d i - 0) := by
      simpa only [sub_zero] using hderiv_i
    simpa only [Function.comp_def, mul_neg_one] using
      hfi.comp 0 (((hasDerivAt_id' (0 : ℝ)).const_sub (d i)).hasDerivWithinAt (s := Icc 0 (d i)))
        fun t ht => ⟨sub_nonneg.mpr ht.2,
          by linarith [ht.1, G.isFeasibleAllocation_le_capacity hd.1 i]⟩
  have hφ_j : HasDerivWithinAt (fun t => G.utility j (d j + t)) dj' (Icc 0 (d i)) 0 := by
    have hfj : HasDerivWithinAt (G.utility j) dj' (Icc 0 G.capacity) (d j + 0) := by
      simpa only [add_zero] using hderiv_j
    simpa only [Function.comp_def, mul_one] using
      hfj.comp 0 (((hasDerivAt_id' (0 : ℝ)).const_add (d j)).hasDerivWithinAt (s := Icc 0 (d i)))
        fun t ht => ⟨add_nonneg (hd.1.1 j) ht.1, by linarith [ht.2, hsum_ij]⟩
  have hφ_deriv : HasDerivWithinAt φ (-di' + dj') (Ici 0) 0 :=
    (hφ_i.add hφ_j).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hdi)
  have hφ_max : ∀ t ∈ Icc 0 (d i), φ t ≤ φ 0 := by
    intro t ht
    set d₁ := Function.update d i (d i - t)
    set x := Function.update d₁ j (d j + t)
    have hd₁j : d₁ j = d j := Function.update_of_ne hij.symm _ _
    have hx_feas : G.IsFeasibleAllocation x := by
      refine ⟨fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hkj
        · simp only [x, Function.update_self]
          linarith [hd.1.1 k, ht.1]
        · rcases eq_or_ne k i with rfl | hki
          · simp only [x, d₁, Function.update_of_ne hkj, Function.update_self]
            linarith [ht.2]
          · simp only [x, d₁, Function.update_of_ne hkj, Function.update_of_ne hki]
            exact hd.1.1 k
      · have h1 := sum_comp_update_eq (fun _ z => z) d₁ j (d j + t)
        rw [hd₁j, sum_comp_update_eq (fun _ z => z) d i (d i - t)] at h1
        linarith [hd.1.2]
    have hle := hd.2 x hx_feas
    have h1 := sum_comp_update_eq G.utility d₁ j (d j + t)
    rw [hd₁j, sum_comp_update_eq G.utility d i (d i - t)] at h1
    simp only [welfare, φ, sub_zero, add_zero] at hle ⊢
    linarith
  linarith [hasDerivWithinAt_nonpos_of_isMaxOn_Icc hdi hφ_deriv hφ_max]

private theorem simplex_kkt_of_maximizer {G : KellyGame ι} (hC : 0 < G.capacity)
    {f f' : ι → ℝ → ℝ}
    (hd_deriv : ∀ i, ∀ x ∈ Icc 0 G.capacity, HasDerivWithinAt (f i) (f' i x) (Icc 0 G.capacity) x)
    {d : ι → ℝ} (hd : G.IsFeasibleAllocation d) (hsum : ∑ i, d i = G.capacity)
    (hmax : ∀ x, G.IsFeasibleAllocation x → ∑ i, f i (x i) ≤ ∑ i, f i (d i)) :
    ∃ μ, (∀ i, f' i (d i) ≤ μ) ∧ (∀ i, 0 < d i → f' i (d i) = μ) := by
  have hopt : (⟨G.capacity, f⟩ : KellyGame ι).IsSocialOptimum d := ⟨hd, hmax⟩
  have hswap : ∀ i j, 0 < d i → f' j (d j) ≤ f' i (d i) := fun i j hdi => by
    by_cases hij : i = j
    · subst hij; exact le_rfl
    · exact hopt.swap_deriv_le hij hdi
        (hd_deriv i (d i) ⟨hd.1 i, G.isFeasibleAllocation_le_capacity hd i⟩)
        (hd_deriv j (d j) ⟨hd.1 j, G.isFeasibleAllocation_le_capacity hd j⟩)
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos (hsum.symm ▸ hC)
  exact ⟨f' i₀ (d i₀), fun j => hswap i₀ j hi₀,
    fun j hj => le_antisymm (hswap i₀ j hi₀) (hswap j i₀ hj)⟩

private theorem simplex_variational_of_kkt {G : KellyGame ι}
    {f' : ι → ℝ → ℝ} {d : ι → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (hsum : ∑ i, d i = G.capacity)
    (hle : ∀ i, f' i (d i) ≤ μ) (heq : ∀ i, 0 < d i → f' i (d i) = μ)
    (hd0 : ∀ i, 0 ≤ d i) {x : ι → ℝ} (hx : G.IsFeasibleAllocation x) :
    ∑ i, f' i (d i) * (x i - d i) ≤ 0 := by
  calc ∑ i, f' i (d i) * (x i - d i)
      ≤ ∑ i, μ * (x i - d i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases eq_or_lt_of_le (hd0 i) with h0 | hpos
        · rw [← h0, sub_zero]
          exact mul_le_mul_of_nonneg_right (h0 ▸ hle i) (hx.1 i)
        · rw [heq i hpos]
    _ = μ * (∑ i, x i - ∑ i, d i) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ (by linarith [hx.2])

private theorem simplex_maximizer_of_kkt {G : KellyGame ι}
    {f f' : ι → ℝ → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Icc 0 G.capacity) (f i))
    (hd_deriv : ∀ i, ∀ x ∈ Icc 0 G.capacity, HasDerivWithinAt (f i) (f' i x) (Icc 0 G.capacity) x)
    {d : ι → ℝ} (hd : G.IsFeasibleAllocation d) (hsum : ∑ i, d i = G.capacity)
    {μ : ℝ} (hμ : 0 ≤ μ) (hle : ∀ i, f' i (d i) ≤ μ) (heq : ∀ i, 0 < d i → f' i (d i) = μ)
    {x : ι → ℝ} (hx : G.IsFeasibleAllocation x) :
    ∑ i, f i (x i) ≤ ∑ i, f i (d i) := by
  have htan : ∑ i, f i (x i) ≤ ∑ i, (f i (d i) + f' i (d i) * (x i - d i)) :=
    Finset.sum_le_sum fun i _ =>
      (hconc i).le_add_mul_of_hasDerivWithinAt
        ⟨hd.1 i, G.isFeasibleAllocation_le_capacity hd i⟩
        ⟨hx.1 i, G.isFeasibleAllocation_le_capacity hx i⟩
        (hd_deriv i (d i) ⟨hd.1 i, G.isFeasibleAllocation_le_capacity hd i⟩)
  rw [Finset.sum_add_distrib] at htan
  linarith [simplex_variational_of_kkt hμ hsum hle heq hd.1 hx]

private theorem simplex_maximizer_unique_of_strictConcaveOn {G : KellyGame ι}
    {f : ι → ℝ → ℝ} (hstrict : ∀ i, StrictConcaveOn ℝ (Icc 0 G.capacity) (f i))
    {d₁ d₂ : ι → ℝ} (hd₁ : G.IsFeasibleAllocation d₁) (hd₂ : G.IsFeasibleAllocation d₂)
    (hmax₁ : ∀ x, G.IsFeasibleAllocation x → ∑ i, f i (x i) ≤ ∑ i, f i (d₁ i))
    (hmax₂ : ∀ x, G.IsFeasibleAllocation x → ∑ i, f i (x i) ≤ ∑ i, f i (d₂ i)) :
    d₁ = d₂ := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, d₁ k ≠ d₂ k := Function.ne_iff.mp hne
  set m : ι → ℝ := fun i => (1 / 2 : ℝ) * d₁ i + (1 / 2 : ℝ) * d₂ i
  have hm_feas : G.IsFeasibleAllocation m := by
    refine ⟨fun i => by dsimp only [m]; linarith [hd₁.1 i, hd₂.1 i], ?_⟩
    simp only [m, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith [hd₁.2, hd₂.2]
  have hle_i : ∀ i, (1 / 2 : ℝ) * f i (d₁ i) + (1 / 2 : ℝ) * f i (d₂ i) ≤ f i (m i) := fun i =>
    (hstrict i).concaveOn.2
      ⟨hd₁.1 i, G.isFeasibleAllocation_le_capacity hd₁ i⟩
      ⟨hd₂.1 i, G.isFeasibleAllocation_le_capacity hd₂ i⟩
      (by norm_num) (by norm_num) (by norm_num)
  have hlt_k : (1 / 2 : ℝ) * f k (d₁ k) + (1 / 2 : ℝ) * f k (d₂ k) < f k (m k) :=
    (hstrict k).2
      ⟨hd₁.1 k, G.isFeasibleAllocation_le_capacity hd₁ k⟩
      ⟨hd₂.1 k, G.isFeasibleAllocation_le_capacity hd₂ k⟩
      hk (by norm_num) (by norm_num) (by norm_num)
  have hsum_lt :
      ∑ i, ((1 / 2 : ℝ) * f i (d₁ i) + (1 / 2 : ℝ) * f i (d₂ i)) < ∑ i, f i (m i) :=
    Finset.sum_lt_sum (fun i _ => hle_i i) ⟨k, Finset.mem_univ k, hlt_k⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_lt
  linarith [hmax₁ m hm_feas, hmax₂ m hm_feas]

end SimplexKKT

/-! ### Price-taking competitive equilibrium (Theorem 21.1) -/

section CompetitiveEquilibrium

variable [Fintype ι]

/-- **First Welfare Theorem for Kelly's mechanism** ([Johari2007], §21.2, Theorem 21.1;
[Kelly1997]): every price-taking competitive equilibrium `(w, μ)` induces a socially optimal
allocation `G.allocation w` (without assuming concavity or differentiability). -/
theorem IsCompetitiveEquilibrium.isSocialOptimum {G : KellyGame ι} (hC : 0 < G.capacity)
    {w : ι → ℝ} {μ : ℝ} (hce : G.IsCompetitiveEquilibrium w μ) :
    G.IsSocialOptimum (G.allocation w) := by
  obtain ⟨hw, hμ, hprice, hopt⟩ := hce
  have hsum_w : ∑ j, w j = μ * G.capacity := by
    rw [hprice, price, div_mul_cancel₀ _ hC.ne']
  have halloc : ∀ i, G.allocation w i = w i / μ := fun i => by
    rw [G.allocation_eq_div_price hC.ne', ← hprice]
  refine ⟨G.isFeasibleAllocation_allocation hC.le hw, fun x hx => ?_⟩
  have hsum_ineq := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => by
    simpa only [mul_div_cancel_left₀ _ hμ.ne', ← halloc i] using
      hopt i (μ * x i) (mul_nonneg hμ.le (hx.1 i))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum_ineq
  have hcap : μ * ∑ i, x i ≤ ∑ i, w i := hsum_w ▸ mul_le_mul_of_nonneg_left hx.2 hμ.le
  change ∑ i, G.utility i (x i) ≤ ∑ i, G.utility i (G.allocation w i)
  linarith

/-- First-order KKT characterization of `SYSTEM` optima for admissible utilities. -/
theorem isSocialOptimum_iff_kkt [Nonempty ι] {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) {d : ι → ℝ} :
    G.IsSocialOptimum d ↔
      G.IsFeasibleAllocation d ∧ ∑ i, d i = G.capacity ∧
        ∃ μ, 0 < μ ∧
          (∀ i, derivWithin (G.utility i) (Ici 0) (d i) ≤ μ) ∧
          (∀ i, 0 < d i → derivWithin (G.utility i) (Ici 0) (d i) = μ) := by
  have hderiv_Icc : ∀ i, ∀ x ∈ Icc 0 G.capacity,
      HasDerivWithinAt (G.utility i) (derivWithin (G.utility i) (Ici 0) x)
        (Icc 0 G.capacity) x := fun i x hx =>
    ((hU i).hasDerivWithinAt hx.1).mono fun _ hz => hz.1
  constructor
  · rintro ⟨hd, hmax⟩
    have hsum := simplex_maximizer_sum_eq_capacity
      (fun i => (hU i).strictMonoOn.mono fun _ hz => hz.1) hd hmax
    obtain ⟨μ, hle, heq⟩ := simplex_kkt_of_maximizer hC hderiv_Icc hd hsum hmax
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hμ : 0 < μ := lt_of_lt_of_le ((hU i₀).derivWithin_pos (hd.1 i₀)) (hle i₀)
    exact ⟨hd, hsum, μ, hμ, hle, heq⟩
  · rintro ⟨hd, hsum, μ, hμ, hle, heq⟩
    refine ⟨hd, fun x hx => simplex_maximizer_of_kkt
      (fun i => (hU i).concaveOn.subset (fun _ hz => hz.1) (convex_Icc 0 G.capacity))
      hderiv_Icc hd hsum hμ.le hle heq hx⟩

/-- Every social optimum for strictly increasing utilities exhausts the resource capacity. -/
theorem IsSocialOptimum.sum_eq_capacity [Nonempty ι] {G : KellyGame ι}
    (hmono : ∀ i, StrictMonoOn (G.utility i) (Icc 0 G.capacity))
    {d : ι → ℝ} (hd : G.IsSocialOptimum d) :
    ∑ i, d i = G.capacity :=
  simplex_maximizer_sum_eq_capacity hmono hd.1 hd.2

/-- Existence of a socially optimal allocation for `SYSTEM` with positive capacity and continuous
utilities on `[0, C]`. -/
theorem exists_isSocialOptimum {G : KellyGame ι} (hC : 0 ≤ G.capacity)
    (hcont : ∀ i, ContinuousOn (G.utility i) (Icc 0 G.capacity)) :
    ∃ d, G.IsSocialOptimum d :=
  exists_simplex_maximizer hC hcont

/-- Existence and uniqueness of the socially optimal allocation for `SYSTEM` with strictly concave
continuous utilities on `[0, C]`. -/
theorem existsUnique_isSocialOptimum_of_strictConcaveOn {G : KellyGame ι} (hC : 0 ≤ G.capacity)
    (hcont : ∀ i, ContinuousOn (G.utility i) (Icc 0 G.capacity))
    (hstrict : ∀ i, StrictConcaveOn ℝ (Icc 0 G.capacity) (G.utility i)) :
    ∃! d, G.IsSocialOptimum d := by
  obtain ⟨d, hd⟩ := exists_isSocialOptimum hC hcont
  exact ⟨d, hd, fun d' hd' =>
    simplex_maximizer_unique_of_strictConcaveOn hstrict hd'.1 hd.1 hd'.2 hd.2⟩

/-- **Existence of Kelly competitive equilibrium** ([Johari2007], §21.2, Theorem 21.1;
[Kelly1997]): for `Nonempty ι`, positive capacity `G.capacity`, and admissible utilities, there
exists a competitive equilibrium `(w, μ)`, and its allocation `G.allocation w` solves `SYSTEM`. -/
theorem exists_isCompetitiveEquilibrium [Nonempty ι] {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) :
    ∃ w μ, G.IsCompetitiveEquilibrium w μ ∧ G.IsSocialOptimum (G.allocation w) := by
  obtain ⟨d, hd, hmax⟩ := exists_simplex_maximizer hC.le fun i =>
    (hU i).continuousOn.mono fun _ hz => hz.1
  obtain ⟨_, hsum, μ, hμ, hle, heq⟩ := (isSocialOptimum_iff_kkt hC hU).mp ⟨hd, hmax⟩
  set w : ι → ℝ := fun i => μ * d i
  have hw : ∀ i, 0 ≤ w i := fun i => mul_nonneg hμ.le (hd.1 i)
  have hprice : μ = G.price w := by
    simp only [price, w, ← Finset.mul_sum, hsum, mul_div_cancel_right₀ _ hC.ne']
  have hce : G.IsCompetitiveEquilibrium w μ := by
    refine ⟨hw, hμ, hprice, fun i t ht => ?_⟩
    rw [show w i / μ = d i from mul_div_cancel_left₀ (d i) hμ.ne']
    have htan := (hU i).le_add_derivWithin (hd.1 i) (div_nonneg ht hμ.le)
    have hprod : (derivWithin (G.utility i) (Ici 0) (d i) - μ) * (t / μ - d i) ≤ 0 := by
      rcases eq_or_lt_of_le (hd.1 i) with h0 | hpos
      · rw [← h0, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (h0 ▸ hle i)) (div_nonneg ht hμ.le)
      · rw [heq i hpos, sub_self, zero_mul]
    nlinarith [mul_div_cancel₀ t hμ.ne', show w i = μ * d i from rfl]
  exact ⟨w, μ, hce, hce.isSocialOptimum hC⟩

/-- When utilities are also strictly concave on `[0, ∞)`, the competitive equilibrium `(w, μ)` is
unique. -/
theorem existsUnique_isCompetitiveEquilibrium_of_strictConcaveOn [Nonempty ι] {G : KellyGame ι}
    (hC : 0 < G.capacity) (hU : ∀ i, IsAdmissibleUtility (G.utility i))
    (hstrict : ∀ i, StrictConcaveOn ℝ (Ici 0) (G.utility i)) :
    ∃! p : (ι → ℝ) × ℝ, G.IsCompetitiveEquilibrium p.1 p.2 := by
  obtain ⟨w, μ, hce, _⟩ := exists_isCompetitiveEquilibrium hC hU
  refine ⟨(w, μ), hce, ?_⟩
  rintro ⟨w', μ'⟩ hce'
  have hopt := hce.isSocialOptimum hC
  have hopt' := hce'.isSocialOptimum hC
  have hd_eq : G.allocation w' = G.allocation w :=
    simplex_maximizer_unique_of_strictConcaveOn
      (fun i => (hstrict i).subset (fun _ hz => hz.1) (convex_Icc 0 G.capacity))
      hopt'.1 hopt.1 hopt'.2 hopt.2
  have hprice_eq : μ' = μ := by
    have hsum_d : ∑ i, G.allocation w i = G.capacity :=
      G.sum_allocation_eq_capacity fun h0 =>
        hce.2.1.ne' (by rw [hce.2.2.1]; simp only [price, h0, zero_div])
    obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos (hsum_d.symm ▸ hC)
    have hderiv_eq : ∀ (wb : ι → ℝ) (mb : ℝ), G.IsCompetitiveEquilibrium wb mb →
        0 < G.allocation wb i₀ → derivWithin (G.utility i₀) (Ici 0) (G.allocation wb i₀) = mb := by
      intro wb mb hceb hpos
      have halloc_i : G.allocation wb i₀ = wb i₀ / mb := by
        rw [G.allocation_eq_div_price hC.ne', ← hceb.2.2.1]
      have hwi_pos : 0 < wb i₀ := (div_pos_iff_of_pos_right hceb.2.1).mp (halloc_i ▸ hpos)
      have hmax : IsLocalMax (fun t => G.utility i₀ (t / mb) - t) (wb i₀) := by
        filter_upwards [Ioi_mem_nhds hwi_pos] with t ht
        exact hceb.2.2.2 i₀ t ht.le
      have hda := ((hU i₀).hasDerivWithinAt (div_nonneg hwi_pos.le hceb.2.1.le)).hasDerivAt
        (Ici_mem_nhds (div_pos hwi_pos hceb.2.1))
      have hzero := hmax.hasDerivAt_eq_zero
        ((hda.comp (wb i₀) ((hasDerivAt_id' (wb i₀)).div_const mb)).sub (hasDerivAt_id' (wb i₀)))
      rw [halloc_i]
      have hmbne : mb ≠ 0 := hceb.2.1.ne'
      field_simp at hzero; linarith
    have h1 := hderiv_eq w μ hce hi₀
    have h2 := hderiv_eq w' μ' hce' (hd_eq.symm ▸ hi₀)
    rw [hd_eq] at h2; linarith
  ext i
  · have hi := congrFun hd_eq i
    rw [G.allocation_eq_div_price hC.ne', G.allocation_eq_div_price hC.ne',
      ← hce.2.2.1, ← hce'.2.2.1, hprice_eq] at hi
    exact (div_left_inj₀ hce.2.1.ne').mp hi
  · exact hprice_eq

end CompetitiveEquilibrium

/-! ### Properties of the modified utility `Û_i` -/

section ModifiedUtility

private theorem hasDerivWithinAt_integral_of_continuousOn {u : ℝ → ℝ} {C x : ℝ}
    (hu : ContinuousOn u (Ici 0)) (hx : x ∈ Icc 0 C) :
    HasDerivWithinAt (fun t => ∫ z in (0 : ℝ)..t, u z) (u x) (Icc 0 C) x := by
  have hint : IntervalIntegrable u volume 0 x :=
    (hu.mono (by rw [uIcc_of_le hx.1]; exact fun _ hz => hz.1)).intervalIntegrable
  rcases eq_or_lt_of_le hx.1 with hx0 | hx_pos
  · subst hx0
    have hmeas : StronglyMeasurableAtFilter u (𝓝[>] (0 : ℝ)) :=
      (hu.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici 0).filter_mono
        (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have hcont : ContinuousWithinAt u (Ioi 0) 0 := (hu 0 le_rfl).mono Ioi_subset_Ici_self
    exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
      hint hmeas hcont).mono fun _ hz => hz.1
  · have hmeas : StronglyMeasurableAtFilter u (𝓝 x) :=
      nhdsWithin_eq_nhds.mpr (Ici_mem_nhds hx_pos) ▸
        hu.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici x
    have hcont : ContinuousAt u x := hu.continuousAt (Ici_mem_nhds hx_pos)
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).hasDerivWithinAt

/-- Derivative of `modifiedUtility G i` on `[0, C]`: `Û_i'(x) = (1 - x / C) U_i'(x)`. -/
theorem hasDerivWithinAt_modifiedUtility {G : KellyGame ι} {i : ι}
    (hu : IsAdmissibleUtility (G.utility i)) {x : ℝ} (hx : x ∈ Icc 0 G.capacity) :
    HasDerivWithinAt (G.modifiedUtility i)
      ((1 - x / G.capacity) * derivWithin (G.utility i) (Ici 0) x) (Icc 0 G.capacity) x := by
  have h1 : HasDerivWithinAt (fun t : ℝ => 1 - t / G.capacity) (-(1 / G.capacity))
      (Icc 0 G.capacity) x :=
    (((hasDerivAt_id' x).div_const G.capacity).const_sub (1 : ℝ)).hasDerivWithinAt
  have h2 : HasDerivWithinAt (G.utility i) (derivWithin (G.utility i) (Ici 0) x)
      (Icc 0 G.capacity) x :=
    (hu.hasDerivWithinAt hx.1).mono fun _ hz => hz.1
  have h3 := hasDerivWithinAt_integral_of_continuousOn hu.continuousOn hx
  have hsum : HasDerivWithinAt (G.modifiedUtility i) _ (Icc 0 G.capacity) x :=
    ((h1.mul h2).add (h3.const_mul (1 / G.capacity))).congr (fun _ _ => rfl) rfl
  convert hsum using 1
  ring

/-- Each modified utility `Û_i` is strictly concave on `[0, C]` whenever `U_i` is concave and
strictly increasing (even when `U_i` is linear). -/
theorem modifiedUtility_strictConcaveOn {G : KellyGame ι} (hC : 0 < G.capacity) {i : ι}
    (hu : IsAdmissibleUtility (G.utility i)) :
    StrictConcaveOn ℝ (Icc 0 G.capacity) (G.modifiedUtility i) := by
  have hcont : ContinuousOn (G.modifiedUtility i) (Icc 0 G.capacity) :=
    fun x hx => (hasDerivWithinAt_modifiedUtility hu hx).continuousWithinAt
  have hderiv_Ioo : ∀ x ∈ Ioo 0 G.capacity,
      deriv (G.modifiedUtility i) x =
        (1 - x / G.capacity) * derivWithin (G.utility i) (Ici 0) x := fun x hx =>
    ((hasDerivWithinAt_modifiedUtility hu (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).deriv
  have hanti : StrictAntiOn (deriv (G.modifiedUtility i)) (interior (Icc 0 G.capacity)) := by
    rw [interior_Icc]
    intro x hx y hy hxy
    rw [hderiv_Ioo x hx, hderiv_Ioo y hy]
    have hux : 0 < derivWithin (G.utility i) (Ici 0) x := hu.derivWithin_pos hx.1.le
    have huy : derivWithin (G.utility i) (Ici 0) y ≤ derivWithin (G.utility i) (Ici 0) x :=
      hu.derivWithin_antitoneOn hx.1.le hy.1.le hxy.le
    have h1y : 0 < 1 - y / G.capacity := by
      rw [sub_pos, div_lt_one hC]; exact hy.2
    have h1lt : 1 - y / G.capacity < 1 - x / G.capacity := by
      have : x / G.capacity < y / G.capacity := div_lt_div_of_pos_right hxy hC
      linarith
    calc (1 - y / G.capacity) * derivWithin (G.utility i) (Ici 0) y
        ≤ (1 - y / G.capacity) * derivWithin (G.utility i) (Ici 0) x :=
          mul_le_mul_of_nonneg_left huy h1y.le
      _ < (1 - x / G.capacity) * derivWithin (G.utility i) (Ici 0) x :=
          mul_lt_mul_of_pos_right h1lt hux
  exact hanti.strictConcaveOn_of_deriv (convex_Icc 0 G.capacity) hcont

theorem modifiedUtility_strictMonoOn {G : KellyGame ι} (hC : 0 < G.capacity) {i : ι}
    (hu : IsAdmissibleUtility (G.utility i)) :
    StrictMonoOn (G.modifiedUtility i) (Icc 0 G.capacity) := by
  have hcont : ContinuousOn (G.modifiedUtility i) (Icc 0 G.capacity) :=
    fun x hx => (hasDerivWithinAt_modifiedUtility hu hx).continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 G.capacity) hcont fun x hx => ?_
  rw [interior_Icc] at hx
  rw [((hasDerivWithinAt_modifiedUtility hu (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)).deriv]
  exact mul_pos (by rw [sub_pos, div_lt_one hC]; exact hx.2) (hu.derivWithin_pos hx.1.le)

end ModifiedUtility

/-! ### Price-anticipating Nash equilibrium, `GAME`, and variational inequality -/

section NashEquilibrium

variable [Fintype ι] [DecidableEq ι]

/-- At any Nash equilibrium with strictly increasing utilities and positive capacity, the sum of
all *other* users' bids is strictly positive for every user `i` (so at least two users bid
strictly positively; in particular, no Nash equilibrium exists with a single user). -/
theorem IsNashEquilibrium.sum_erase_pos {G : KellyGame ι} (hC : 0 < G.capacity)
    (hmono : ∀ i, StrictMonoOn (G.utility i) (Ici 0)) {w : ι → ℝ} (hne : G.IsNashEquilibrium w)
    (i : ι) : 0 < ∑ j ∈ Finset.univ.erase i, w j := by
  obtain ⟨hw, hbr⟩ := hne
  refine lt_of_le_of_ne (Finset.sum_nonneg fun j _ => hw j) (Ne.symm fun hzero => ?_)
  have hsum_w : ∑ j, w j = w i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hzero, add_zero]
  have hupd_alloc : ∀ t : ℝ, 0 < t → G.allocation (Function.update w i t) i = G.capacity :=
    fun t ht => by
      have hsum : ∑ j, Function.update w i t j = t := by
        rw [sum_comp_update_eq (fun _ z => z), hsum_w]; ring
      simp only [allocation, Function.update_self, hsum, mul_div_cancel_right₀ _ ht.ne']
  rcases eq_or_lt_of_le (hw i) with hwi0 | hwi_pos
  · have hsum0 : ∑ j, w j = 0 := hsum_w.trans hwi0.symm
    have hult := hmono i le_rfl hC.le hC
    set t := (G.utility i G.capacity - G.utility i 0) / 2
    have ht : 0 < t := half_pos (sub_pos.mpr hult)
    have hle := hbr i t ht.le
    simp only [payoff, Function.update_self, hupd_alloc t ht,
      G.allocation_eq_zero_of_sum_eq_zero hsum0, ← hwi0, sub_zero] at hle
    dsimp only [t] at hle; linarith
  · have halloc_wi : G.allocation w i = G.capacity := by
      simp only [allocation, hsum_w, mul_div_cancel_right₀ _ hwi_pos.ne']
    have hle := hbr i (w i / 2) (half_pos hwi_pos).le
    simp only [payoff, Function.update_self, hupd_alloc _ (half_pos hwi_pos), halloc_wi] at hle
    linarith

theorem IsNashEquilibrium.price_pos [Nonempty ι] {G : KellyGame ι} (hC : 0 < G.capacity)
    (hmono : ∀ i, StrictMonoOn (G.utility i) (Ici 0)) {w : ι → ℝ} (hne : G.IsNashEquilibrium w) :
    0 < G.price w := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h1 := hne.sum_erase_pos hC hmono i₀
  have hsum : 0 < ∑ j, w j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    linarith [hne.1 i₀]
  exact div_pos hsum hC

/-- At any Nash equilibrium with strictly increasing utilities, total equilibrium allocation equals
the resource capacity. -/
theorem IsNashEquilibrium.sum_allocation_eq_capacity [Nonempty ι] {G : KellyGame ι}
    (hC : 0 < G.capacity) (hmono : ∀ i, StrictMonoOn (G.utility i) (Ici 0)) {w : ι → ℝ}
    (hne : G.IsNashEquilibrium w) : ∑ i, G.allocation w i = G.capacity :=
  G.sum_allocation_eq_capacity fun h0 =>
    (hne.price_pos hC hmono).ne' (by simp only [price, h0, zero_div])

theorem IsNashEquilibrium.allocation_lt_capacity {G : KellyGame ι} (hC : 0 < G.capacity)
    (hmono : ∀ i, StrictMonoOn (G.utility i) (Ici 0)) {w : ι → ℝ} (hne : G.IsNashEquilibrium w)
    (i : ι) : G.allocation w i < G.capacity := by
  have herase := hne.sum_erase_pos hC hmono i
  have hsum : ∑ j, w j = w i + ∑ j ∈ Finset.univ.erase i, w j :=
    (Finset.add_sum_erase Finset.univ w (Finset.mem_univ i)).symm
  have hW : 0 < ∑ j, w j := by linarith [hne.1 i]
  simp only [allocation]
  rw [div_lt_iff₀ hW]
  nlinarith

/-- Concavity of a user's single-variable allocation response `t ↦ C · t / (t + s)` on `[0, ∞)`
when other users' aggregate bid `s` is strictly positive. -/
private theorem concaveOn_propAlloc {C s : ℝ} (hC : 0 < C) (hs : 0 < s) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun t => C * t / (t + s)) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hxs : 0 < x + s := by linarith
  have hys : 0 < y + s := by linarith
  have habs : 0 < a * x + b * y + s := by nlinarith
  simp only [smul_eq_mul]
  have hdiff :
      C * (a * x + b * y) / (a * x + b * y + s) -
        (a * (C * x / (x + s)) + b * (C * y / (y + s))) =
      C * s * a * b * (x - y) ^ 2 / ((a * x + b * y + s) * (x + s) * (y + s)) := by
    field_simp
    rw [show a = 1 - b by linarith]; ring
  have : 0 ≤ C * s * a * b * (x - y) ^ 2 / ((a * x + b * y + s) * (x + s) * (y + s)) := by
    positivity
  linarith

private theorem concaveOn_userPayoff {C s : ℝ} {u : ℝ → ℝ} (hC : 0 < C) (hs : 0 < s)
    (hu : IsAdmissibleUtility u) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun t => u (C * t / (t + s)) - t) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : 0 ≤ x := mem_Ici.mp hx
  have hy0 : 0 ≤ y := mem_Ici.mp hy
  have hfx : 0 ≤ C * x / (x + s) := div_nonneg (mul_nonneg hC.le hx0) (by linarith)
  have hfy : 0 ≤ C * y / (y + s) := div_nonneg (mul_nonneg hC.le hy0) (by linarith)
  have haxby : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  have hmono := hu.strictMonoOn.monotoneOn
    (add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hfy))
    (div_nonneg (mul_nonneg hC.le haxby) (by simp only [smul_eq_mul]; linarith))
    ((concaveOn_propAlloc hC hs).2 hx hy ha hb hab)
  have hconc := hu.concaveOn.2 hfx hfy ha hb hab
  simp only [smul_eq_mul] at hmono hconc ⊢
  linarith

private theorem hasDerivWithinAt_userPayoff {C s t : ℝ} {u : ℝ → ℝ} (hC : 0 < C) (hs : 0 < s)
    (ht : 0 ≤ t) (hu : IsAdmissibleUtility u) :
    HasDerivWithinAt (fun x => u (C * x / (x + s)) - x)
      (derivWithin u (Ici 0) (C * t / (t + s)) * (C * s / (t + s) ^ 2) - 1) (Ici 0) t := by
  have hfrac : HasDerivWithinAt (fun x : ℝ => C * x / (x + s)) (C * s / (t + s) ^ 2) (Ici 0) t := by
    have hq := ((((hasDerivAt_id' t).const_mul C).div ((hasDerivAt_id' t).add_const s)
      (by linarith)).hasDerivWithinAt (s := Ici 0))
    have hsimp : (C * 1 * (t + s) - C * t * 1) / (t + s) ^ 2 = C * s / (t + s) ^ 2 := by ring
    rwa [hsimp] at hq
  have hmaps : MapsTo (fun x : ℝ => C * x / (x + s)) (Ici 0) (Ici 0) := fun x hx =>
    div_nonneg (mul_nonneg hC.le hx) (by linarith [mem_Ici.mp hx])
  exact ((hu.hasDerivWithinAt (hmaps ht)).comp t hfrac hmaps).sub
    (hasDerivAt_id' t).hasDerivWithinAt

/-- **First-order KKT characterization of price-anticipating Nash equilibria** ([Johari2007],
§21.2): a nonnegative bid profile `w` is a Nash equilibrium iff every user faces a positive sum
of competing bids and the modified marginal utility `U_i'(d_i) (1 - d_i / C)` is at most the
clearing price `μ = G.price w`, with equality whenever `d_i > 0`. -/
theorem isNashEquilibrium_iff_kkt {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) {w : ι → ℝ} :
    G.IsNashEquilibrium w ↔
      (∀ i, 0 ≤ w i) ∧ (∀ i, 0 < ∑ j ∈ Finset.univ.erase i, w j) ∧
        (∀ i, derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
            (1 - G.allocation w i / G.capacity) ≤ G.price w) ∧
        (∀ i, 0 < G.allocation w i →
          derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
            (1 - G.allocation w i / G.capacity) = G.price w) := by
  have hpayoff_eq : ∀ (i : ι) (t : ℝ),
      G.payoff (Function.update w i t) i =
        G.utility i (G.capacity * t / (t + ∑ j ∈ Finset.univ.erase i, w j)) - t := fun i t => by
    have hsum : ∑ j, Function.update w i t j = t + ∑ j ∈ Finset.univ.erase i, w j := by
      have := Finset.add_sum_erase Finset.univ w (Finset.mem_univ i)
      rw [sum_comp_update_eq (fun _ z => z)]; linarith
    simp only [payoff, allocation, Function.update_self, hsum]
  have hpayoff_self : ∀ i : ι, G.payoff w i =
      G.utility i (G.capacity * w i / (w i + ∑ j ∈ Finset.univ.erase i, w j)) - w i := fun i => by
    simpa only [Function.update_eq_self] using hpayoff_eq i (w i)
  have hfactor : ∀ (i : ι), 0 ≤ w i → 0 < ∑ j ∈ Finset.univ.erase i, w j →
      let s := ∑ j ∈ Finset.univ.erase i, w j
      0 < G.price w ∧ G.capacity * w i / (w i + s) = G.allocation w i ∧
        G.capacity * s / (w i + s) ^ 2 = (1 - G.allocation w i / G.capacity) / G.price w := by
    intro i hwi hs s
    have hW : w i + s = ∑ j, w j := Finset.add_sum_erase Finset.univ w (Finset.mem_univ i)
    have hWpos : 0 < ∑ j, w j := by linarith
    refine ⟨div_pos hWpos hC, by simp only [allocation, hW], ?_⟩
    have hs_eq : s = ∑ j, w j - w i := by linarith
    simp only [allocation, price]
    rw [hW, hs_eq]
    field_simp
  constructor
  · intro hne
    have herase : ∀ i, 0 < ∑ j ∈ Finset.univ.erase i, w j :=
      fun i => hne.sum_erase_pos hC (fun j => (hU j).strictMonoOn) i
    refine ⟨hne.1, herase, ?_, ?_⟩
    · intro i
      set s := ∑ j ∈ Finset.univ.erase i, w j
      obtain ⟨hμpos, halloc_eq, hfac⟩ := hfactor i (hne.1 i) (herase i)
      have hd := hasDerivWithinAt_userPayoff hC (herase i) (hne.1 i) (hU i)
      rw [halloc_eq, hfac] at hd
      have hφ_deriv : HasDerivWithinAt
          (fun δ => G.utility i (G.capacity * (w i + δ) / ((w i + δ) + s)) - (w i + δ))
          (derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
            ((1 - G.allocation w i / G.capacity) / G.price w) - 1) (Ici 0) 0 := by
        have hd' : HasDerivWithinAt (fun x => G.utility i (G.capacity * x / (x + s)) - x)
            (derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
              ((1 - G.allocation w i / G.capacity) / G.price w) - 1) (Ici 0) (w i + 0) := by
          simpa only [add_zero] using hd
        simpa only [Function.comp_def, mul_one] using
          hd'.comp 0 ((hasDerivAt_id' (0 : ℝ)).const_add (w i)).hasDerivWithinAt fun δ hδ =>
            add_nonneg (hne.1 i) hδ
      have hφ_max : ∀ δ ∈ Icc (0 : ℝ) 1,
          G.utility i (G.capacity * (w i + δ) / ((w i + δ) + s)) - (w i + δ) ≤
          G.utility i (G.capacity * (w i + 0) / ((w i + 0) + s)) - (w i + 0) := fun δ hδ => by
        simpa only [add_zero, hpayoff_eq, hpayoff_self] using
          hne.2 i (w i + δ) (by linarith [hne.1 i, hδ.1])
      have hle0 := hasDerivWithinAt_nonpos_of_isMaxOn_Icc zero_lt_one hφ_deriv hφ_max
      exact (div_le_one hμpos).mp (by simpa only [mul_div_assoc] using sub_nonpos.mp hle0)
    · intro i hdi
      set s := ∑ j ∈ Finset.univ.erase i, w j
      obtain ⟨hμpos, halloc_eq, hfac⟩ := hfactor i (hne.1 i) (herase i)
      have hWpos : 0 < ∑ j, w j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; linarith [hne.1 i, herase i]
      have hwi_pos : 0 < w i :=
        (mul_pos_iff_of_pos_left hC).mp ((div_pos_iff_of_pos_right hWpos).mp hdi)
      have hd := (hasDerivWithinAt_userPayoff hC (herase i) (hne.1 i) (hU i)).hasDerivAt
        (Ici_mem_nhds hwi_pos)
      rw [halloc_eq, hfac] at hd
      have hmax : IsLocalMax (fun x => G.utility i (G.capacity * x / (x + s)) - x) (w i) := by
        filter_upwards [Ioi_mem_nhds hwi_pos] with t ht
        simpa only [hpayoff_eq, hpayoff_self] using hne.2 i t ht.le
      have hzero := hmax.hasDerivAt_eq_zero hd
      rwa [← mul_div_assoc, sub_eq_zero, div_eq_one_iff_eq hμpos.ne'] at hzero
  · rintro ⟨hw, herase, hle, heq⟩
    refine ⟨hw, fun i t ht => ?_⟩
    set s := ∑ j ∈ Finset.univ.erase i, w j
    obtain ⟨hμpos, halloc_eq, hfac⟩ := hfactor i (hw i) (herase i)
    have hd := hasDerivWithinAt_userPayoff hC (herase i) (hw i) (hU i)
    rw [halloc_eq, hfac] at hd
    have htan := (concaveOn_userPayoff hC (herase i) (hU i)).le_add_mul_of_hasDerivWithinAt
      (hw i) ht hd
    have hterm :
        (derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
          ((1 - G.allocation w i / G.capacity) / G.price w) - 1) * (t - w i) ≤ 0 := by
      rcases eq_or_lt_of_le (hw i) with hwi0 | hwi_pos
      · rw [← hwi0, sub_zero]
        refine mul_nonpos_of_nonpos_of_nonneg ?_ ht
        rw [sub_nonpos, ← mul_div_assoc, div_le_one hμpos]
        exact hle i
      · have hWpos : 0 < ∑ j, w j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; linarith [herase i]
        have hdi : 0 < G.allocation w i := div_pos (mul_pos hC hwi_pos) hWpos
        rw [← mul_div_assoc, heq i hdi, div_self hμpos.ne', sub_self, zero_mul]
    rw [hpayoff_eq, hpayoff_self]
    linarith

/-- **Existence and uniqueness of the price-anticipating Nash equilibrium and equivalence with
`GAME`** ([Johari2007], §21.2, Theorem 21.2; [JohariTsitsiklis2004]): for `2 ≤ Fintype.card ι`,
positive capacity, and admissible utilities, the Kelly game has a unique Nash equilibrium `w`, and
its allocation `G.allocation w` is the unique maximizer of `GAME`. -/
theorem existsUnique_isNashEquilibrium {G : KellyGame ι} (hcard : 2 ≤ Fintype.card ι)
    (hC : 0 < G.capacity) (hU : ∀ i, IsAdmissibleUtility (G.utility i)) :
    (∃! w, G.IsNashEquilibrium w) ∧
      (∃! d, G.IsGameOptimum d) ∧
      ∀ w, G.IsNashEquilibrium w → G.IsGameOptimum (G.allocation w) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hstrict : ∀ i, StrictConcaveOn ℝ (Icc 0 G.capacity) (G.modifiedUtility i) :=
    fun i => modifiedUtility_strictConcaveOn hC (hU i)
  have hderiv : ∀ i, ∀ x ∈ Icc 0 G.capacity,
      HasDerivWithinAt (G.modifiedUtility i)
        ((1 - x / G.capacity) * derivWithin (G.utility i) (Ici 0) x) (Icc 0 G.capacity) x :=
    fun i _ hx => hasDerivWithinAt_modifiedUtility (hU i) hx
  obtain ⟨dStar, hdStar, hmaxStar⟩ := exists_simplex_maximizer hC.le fun i x hx =>
    (hderiv i x hx).continuousWithinAt
  have hgameUnique : ∀ d, G.IsGameOptimum d → d = dStar := fun d hd =>
    simplex_maximizer_unique_of_strictConcaveOn hstrict hd.1 hdStar hd.2 hmaxStar
  have hsumStar : ∑ i, dStar i = G.capacity :=
    simplex_maximizer_sum_eq_capacity (fun i => modifiedUtility_strictMonoOn hC (hU i))
      hdStar hmaxStar
  obtain ⟨μStar, hleStar, heqStar⟩ := simplex_kkt_of_maximizer hC hderiv hdStar hsumStar hmaxStar
  have hltCStar : ∀ i, dStar i < G.capacity := fun i =>
    lt_of_le_of_ne (G.isFeasibleAllocation_le_capacity hdStar i) fun heqC => by
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]; omega :
        0 < (Finset.univ.erase i).card)
      have hrest : ∑ k ∈ Finset.univ.erase i, dStar k = 0 := by
        linarith [Finset.add_sum_erase Finset.univ dStar (Finset.mem_univ i)]
      have hdj0 : dStar j = 0 := le_antisymm
        ((Finset.single_le_sum (fun k _ => hdStar.1 k) hj).trans hrest.le) (hdStar.1 j)
      have hμ0 : μStar = 0 := by
        simpa only [heqC, div_self hC.ne', sub_self, zero_mul, eq_comm] using
          heqStar i (by linarith)
      have hj_le := hleStar j
      rw [hdj0, zero_div, sub_zero, one_mul, hμ0] at hj_le
      linarith [(hU j).derivWithin_pos le_rfl]
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos (hsumStar.symm ▸ hC)
  have hμStar_pos : 0 < μStar := by
    rw [← heqStar i₀ hi₀]
    exact mul_pos (by rw [sub_pos, div_lt_one hC]; exact hltCStar i₀)
      ((hU i₀).derivWithin_pos (hdStar.1 i₀))
  set wStar : ι → ℝ := fun i => μStar * dStar i
  have hpriceStar : G.price wStar = μStar := by
    simp only [price, wStar, ← Finset.mul_sum, hsumStar, mul_div_cancel_right₀ _ hC.ne']
  have hallocStar : G.allocation wStar = dStar := funext fun i => by
    rw [G.allocation_eq_div_price hC.ne', hpriceStar]
    exact mul_div_cancel_left₀ (dStar i) hμStar_pos.ne'
  have hneStar : G.IsNashEquilibrium wStar := by
    rw [isNashEquilibrium_iff_kkt hC hU]
    refine ⟨fun i => mul_nonneg hμStar_pos.le (hdStar.1 i), fun i => ?_,
      fun i => by
        rw [hallocStar, hpriceStar, mul_comm]
        exact hleStar i,
      fun i hdi => by
        rw [hallocStar, hpriceStar, mul_comm]
        exact heqStar i (hallocStar ▸ hdi)⟩
    have hsum_e : ∑ j ∈ Finset.univ.erase i, dStar j = G.capacity - dStar i := by
      linarith [Finset.add_sum_erase Finset.univ dStar (Finset.mem_univ i)]
    simp only [wStar, ← Finset.mul_sum, hsum_e]
    exact mul_pos hμStar_pos (sub_pos.mpr (hltCStar i))
  have hne_to_game : ∀ w, G.IsNashEquilibrium w → G.IsGameOptimum (G.allocation w) := by
    intro w hne
    obtain ⟨hw, _, hle, heq⟩ := (isNashEquilibrium_iff_kkt hC hU).mp hne
    have hfeas := G.isFeasibleAllocation_allocation hC.le hw
    refine ⟨hfeas, fun x hx => simplex_maximizer_of_kkt
      (fun i => (hstrict i).concaveOn) hderiv hfeas
      (hne.sum_allocation_eq_capacity hC fun j => (hU j).strictMonoOn)
      (hne.price_pos hC fun j => (hU j).strictMonoOn).le
      (fun i => by rw [mul_comm]; exact hle i)
      (fun i hdi => by rw [mul_comm]; exact heq i hdi) hx⟩
  have hne_unique : ∀ w, G.IsNashEquilibrium w → w = wStar := by
    intro w hne
    have hd_eq : G.allocation w = dStar := hgameUnique _ (hne_to_game w hne)
    obtain ⟨_, _, _, heq⟩ := (isNashEquilibrium_iff_kkt hC hU).mp hne
    have hprice_eq : G.price w = μStar := by
      have h1 := heq i₀ (hd_eq.symm ▸ hi₀)
      rw [hd_eq, mul_comm] at h1; linarith [heqStar i₀ hi₀]
    funext i
    have hi := congrFun hd_eq i
    rw [G.allocation_eq_div_price hC.ne', hprice_eq] at hi
    calc w i = μStar * (w i / μStar) := (mul_div_cancel₀ (w i) hμStar_pos.ne').symm
      _ = μStar * dStar i := by rw [hi]
  exact ⟨⟨wStar, hneStar, hne_unique⟩, ⟨dStar, ⟨hdStar, hmaxStar⟩, hgameUnique⟩, hne_to_game⟩

/-- **Variational inequality for Kelly Nash equilibria** ([Johari2007], §21.2, Corollary 21.3):
at any Nash equilibrium `w` with allocation `d = G.allocation w`,
`∑_i U_i'(d_i) (1 - d_i / C) (x_i - d_i) ≤ 0` for every feasible allocation `x`. -/
theorem IsNashEquilibrium.variational_inequality {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) {w : ι → ℝ} (hne : G.IsNashEquilibrium w)
    {x : ι → ℝ} (hx : G.IsFeasibleAllocation x) :
    ∑ i, derivWithin (G.utility i) (Ici 0) (G.allocation w i) *
        (1 - G.allocation w i / G.capacity) * (x i - G.allocation w i) ≤ 0 := by
  rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
  · simp
  · obtain ⟨hw, _, hle, heq⟩ := (isNashEquilibrium_iff_kkt hC hU).mp hne
    have hμpos : 0 < G.price w := hne.price_pos hC fun j => (hU j).strictMonoOn
    exact simplex_variational_of_kkt
      (f' := fun i t => derivWithin (G.utility i) (Ici 0) t * (1 - t / G.capacity))
      hμpos.le (hne.sum_allocation_eq_capacity hC fun j => (hU j).strictMonoOn)
      hle heq (G.allocation_nonneg hC.le hw) hx

end NashEquilibrium

/-! ### Johari–Tsitsiklis `3/4` worst-case efficiency theorem (Theorem 21.4) -/

section Efficiency

variable [Fintype ι]

/-- Linear core of the Johari–Tsitsiklis `3/4` bound: under the Nash first-order conditions for
nonnegative slopes `α_i`, `3/4 · ∑_i α_i x_i ≤ ∑_i α_i d_i`. -/
private theorem linear_three_fourths_bound [Nonempty ι] {C μ : ℝ} (hC : 0 < C)
    {α d x : ι → ℝ} (hα : ∀ i, 0 ≤ α i) (hd0 : ∀ i, 0 ≤ d i) (hsum_d : ∑ i, d i = C)
    (hle : ∀ i, α i * (1 - d i / C) ≤ μ) (heq : ∀ i, 0 < d i → α i * (1 - d i / C) = μ)
    (hx0 : ∀ i, 0 ≤ x i) (hsum_x : ∑ i, x i ≤ C) :
    3 / 4 * ∑ i, α i * x i ≤ ∑ i, α i * d i := by
  classical
  obtain ⟨k, -, hkmax⟩ := Finset.exists_max_image Finset.univ α Finset.univ_nonempty
  have hopt_ub : ∑ i, α i * x i ≤ α k * C :=
    calc ∑ i, α i * x i
        ≤ ∑ i, α k * x i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hkmax i (Finset.mem_univ i)) (hx0 i)
      _ = α k * ∑ i, x i := (Finset.mul_sum ..).symm
      _ ≤ α k * C := mul_le_mul_of_nonneg_left hsum_x (hα k)
  have hterm_ge : ∀ i, μ * d i ≤ α i * d i := fun i => by
    rcases eq_or_lt_of_le (hd0 i) with h0 | hpos
    · rw [← h0, mul_zero, mul_zero]
    · have := heq i hpos
      have : 0 ≤ α i * (d i / C) := mul_nonneg (hα i) (div_nonneg (hd0 i) hC.le)
      exact mul_le_mul_of_nonneg_right (by nlinarith) (hd0 i)
  have herase : C - d k = ∑ i ∈ Finset.univ.erase k, d i := by
    linarith [Finset.add_sum_erase Finset.univ d (Finset.mem_univ k)]
  have hrest_ge : μ * (C - d k) ≤ ∑ i ∈ Finset.univ.erase k, α i * d i :=
    calc μ * (C - d k)
        = ∑ i ∈ Finset.univ.erase k, μ * d i := by rw [herase, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.univ.erase k, α i * d i := Finset.sum_le_sum fun i _ => hterm_ge i
  set z := d k / C
  have hdk_eq : d k = C * z := by simp only [z]; field_simp
  have h1z : 0 ≤ 1 - z := sub_nonneg.mpr <| (div_le_one hC).mpr <|
    hsum_d ▸ Finset.single_le_sum (fun i _ => hd0 i) (Finset.mem_univ k)
  have hrest_z : α k * C * (1 - z) ^ 2 ≤ μ * (C - d k) := by
    have hC1z : C - d k = C * (1 - z) := by rw [hdk_eq]; ring
    rw [hC1z]
    have := mul_le_mul_of_nonneg_right (hle k) (mul_nonneg hC.le h1z)
    nlinarith
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => α i * d i) (Finset.mem_univ k)
  have hquad : 3 / 4 ≤ z + (1 - z) ^ 2 := by nlinarith [sq_nonneg (z - 1 / 2)]
  calc 3 / 4 * ∑ i, α i * x i
      ≤ 3 / 4 * (α k * C) := by linarith
    _ ≤ (z + (1 - z) ^ 2) * (α k * C) := mul_le_mul_of_nonneg_right hquad (mul_nonneg (hα k) hC.le)
    _ = α k * (C * z) + α k * C * (1 - z) ^ 2 := by ring
    _ ≤ ∑ i, α i * d i := by rw [← hdk_eq]; linarith

/-- **Johari–Tsitsiklis `3/4` worst-case efficiency theorem** ([JohariTsitsiklis2004];
[Johari2007], §21.2, Theorem 21.4): for positive capacity and admissible utilities with
`U_i(0) ≥ 0`, every price-anticipating Nash equilibrium `w` of Kelly's proportional allocation
mechanism achieves at least `3/4` of the aggregate welfare of any feasible allocation `x`. -/
theorem IsNashEquilibrium.three_fourths_welfare_le [DecidableEq ι] {G : KellyGame ι}
    (hC : 0 < G.capacity) (hU : ∀ i, IsAdmissibleUtility (G.utility i))
    (hU0 : ∀ i, 0 ≤ G.utility i 0) {w : ι → ℝ} (hne : G.IsNashEquilibrium w)
    {x : ι → ℝ} (hx : G.IsFeasibleAllocation x) :
    3 / 4 * G.welfare x ≤ G.welfare (G.allocation w) := by
  rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
  · simp [welfare]
  · obtain ⟨hw, _, hle, heq⟩ := (isNashEquilibrium_iff_kkt hC hU).mp hne
    set d := G.allocation w
    set α : ι → ℝ := fun i => derivWithin (G.utility i) (Ici 0) (d i)
    have hd0 : ∀ i, 0 ≤ d i := G.allocation_nonneg hC.le hw
    have hlin := linear_three_fourths_bound hC (fun i => ((hU i).derivWithin_pos (hd0 i)).le)
      hd0 (hne.sum_allocation_eq_capacity hC fun j => (hU j).strictMonoOn)
      hle heq hx.1 hx.2
    have hconc_x : ∀ i, G.utility i (x i) ≤ G.utility i (d i) + α i * (x i - d i) :=
      fun i => (hU i).le_add_derivWithin (hd0 i) (hx.1 i)
    have hconc_0 : ∀ i, 0 ≤ G.utility i (d i) - α i * d i := fun i => by
      have h0 := (hU i).le_add_derivWithin (hd0 i) le_rfl
      linarith [hU0 i]
    have hsum_x : G.welfare x ≤ G.welfare d + ∑ i, α i * x i - ∑ i, α i * d i := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hconc_x i
      simp only [welfare, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h ⊢
      linarith
    have hsum_0 : 0 ≤ G.welfare d - ∑ i, α i * d i := by
      have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hconc_0 i
      simpa only [welfare, Finset.sum_sub_distrib] using h
    linarith

end Efficiency

/-! ### Explicit tightness family approaching `3/4` -/

section Tightness

/-- The `(n + 1)`-user linear-utility Kelly game of capacity `1` with `U_0(x) = x` and
`U_i(x) = (n / (2 n - 1)) · x` for `i ≠ 0`. For `n ≥ 2`, its unique Nash equilibrium has welfare
`3/4 + 1 / (4 (2 n - 1))` against optimal welfare `1`. -/
@[expose] noncomputable def kellyTightGame (n : ℕ) : KellyGame (Fin (n + 1)) where
  capacity := 1
  utility := fun i x => if i = 0 then x else ((n : ℝ) / (2 * (n : ℝ) - 1)) * x

/-- The explicit Nash equilibrium bid vector for `kellyTightGame n`: `w_0 = 1/4` and
`w_i = 1 / (4 n)` for `i ≠ 0`. -/
@[expose] noncomputable def kellyTightBid (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then 1 / 4 else 1 / (4 * (n : ℝ))

/-- Every positive-slope linear utility `x ↦ a * x` (`0 < a`) satisfies `IsAdmissibleUtility`. -/
theorem isAdmissibleUtility_linear {a : ℝ} (ha : 0 < a) :
    IsAdmissibleUtility (fun x => a * x) where
  concaveOn := ⟨convex_Ici 0, fun x _ y _ p q _ _ _ => by simp only [smul_eq_mul]; linarith⟩
  strictMonoOn := fun _ _ _ _ hxy => mul_lt_mul_of_pos_left hxy ha
  differentiableOn := (differentiable_id.const_mul a).differentiableOn

/-- Right-sided derivative on `[0, ∞)` of a linear function `t ↦ a * t` at `0 ≤ x`. -/
theorem derivWithin_linear {a x : ℝ} (hx : 0 ≤ x) :
    derivWithin (fun t : ℝ => a * t) (Ici 0) x = a := by
  have hd : HasDerivWithinAt (fun t : ℝ => a * t) a (Ici 0) x := by
    simpa only [mul_one] using ((hasDerivAt_id' x).const_mul a).hasDerivWithinAt
  exact hd.derivWithin (uniqueDiffOn_Ici 0 x hx)

/-- Exact equilibrium and efficiency analysis of `kellyTightGame n` for `n ≥ 2`: admissible linear
utilities, unique Nash equilibrium `kellyTightBid n`, optimal welfare `1`, and Nash welfare
`3/4 + 1 / (4 (2 n - 1))`. -/
theorem kellyTightGame_spec {n : ℕ} (hn : 2 ≤ n) :
    (∀ i, IsAdmissibleUtility ((kellyTightGame n).utility i)) ∧
    (∀ i, (kellyTightGame n).utility i 0 = 0) ∧
    (kellyTightGame n).IsNashEquilibrium (kellyTightBid n) ∧
    (kellyTightGame n).IsSocialOptimum (Pi.single (M := fun _ => ℝ) (0 : Fin (n + 1)) 1) ∧
    (kellyTightGame n).welfare (Pi.single (M := fun _ => ℝ) (0 : Fin (n + 1)) 1) = 1 ∧
    (kellyTightGame n).welfare ((kellyTightGame n).allocation (kellyTightBid n)) =
      3 / 4 + 1 / (4 * (2 * (n : ℝ) - 1)) := by
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hslope_pos : 0 < (n : ℝ) / (2 * (n : ℝ) - 1) := div_pos (by linarith) h2n1_pos
  have hslope_le : (n : ℝ) / (2 * (n : ℝ) - 1) ≤ 1 := (div_le_one h2n1_pos).mpr (by linarith)
  have hu_eq : ∀ i, (kellyTightGame n).utility i =
      fun t => (if i = 0 then 1 else (n : ℝ) / (2 * (n : ℝ) - 1)) * t := fun i =>
    funext fun _ => by
      unfold kellyTightGame
      dsimp only
      split_ifs <;> ring
  have hU : ∀ i, IsAdmissibleUtility ((kellyTightGame n).utility i) := fun i => by
    rw [hu_eq i]
    exact isAdmissibleUtility_linear (by split_ifs <;> positivity)
  have hU0 : ∀ i, (kellyTightGame n).utility i 0 = 0 := fun i => by
    unfold kellyTightGame; dsimp only; split_ifs <;> simp
  have hcard_erase : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]; omega
  have hsum_bid : ∑ j : Fin (n + 1), kellyTightBid n j = 1 / 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    have hrest : ∑ j ∈ Finset.univ.erase (0 : Fin (n + 1)), kellyTightBid n j =
        ∑ _j ∈ Finset.univ.erase (0 : Fin (n + 1)), (1 / (4 * (n : ℝ))) :=
      Finset.sum_congr rfl fun j hj => by simp [kellyTightBid, Finset.ne_of_mem_erase hj]
    rw [hrest, Finset.sum_const, hcard_erase, nsmul_eq_mul]
    simp only [kellyTightBid, ↓reduceIte]
    field_simp; ring
  have hprice : (kellyTightGame n).price (kellyTightBid n) = 1 / 2 := by
    simp only [KellyGame.price, kellyTightGame, hsum_bid, div_one]
  have halloc0 : (kellyTightGame n).allocation (kellyTightBid n) 0 = 1 / 2 := by
    rw [KellyGame.allocation, hsum_bid]
    simp only [kellyTightGame, kellyTightBid, ↓reduceIte]; norm_num
  have halloc_ne : ∀ i : Fin (n + 1), i ≠ 0 →
      (kellyTightGame n).allocation (kellyTightBid n) i = 1 / (2 * (n : ℝ)) := fun i hi => by
    rw [KellyGame.allocation, hsum_bid]
    simp only [kellyTightGame, kellyTightBid, hi, ↓reduceIte]
    field_simp; ring
  have hne : (kellyTightGame n).IsNashEquilibrium (kellyTightBid n) := by
    rw [isNashEquilibrium_iff_kkt (by simp [kellyTightGame] : 0 < (kellyTightGame n).capacity) hU]
    have herase : ∀ i, 0 < ∑ j ∈ Finset.univ.erase i, kellyTightBid n j := fun i => by
      have h := Finset.add_sum_erase Finset.univ (kellyTightBid n) (Finset.mem_univ i)
      rw [hsum_bid] at h
      have hlt : kellyTightBid n i < 1 / 2 := by
        unfold kellyTightBid
        split_ifs
        · norm_num
        · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hfoc : ∀ i, derivWithin ((kellyTightGame n).utility i) (Ici 0)
        ((kellyTightGame n).allocation (kellyTightBid n) i) *
        (1 - (kellyTightGame n).allocation (kellyTightBid n) i / (kellyTightGame n).capacity) =
        (kellyTightGame n).price (kellyTightBid n) := fun i => by
      rw [hprice, hu_eq i]
      by_cases hi : i = 0
      · subst hi
        rw [halloc0, derivWithin_linear (by norm_num)]
        simp only [kellyTightGame, ↓reduceIte, div_one]
        norm_num
      · rw [halloc_ne i hi, derivWithin_linear (by positivity)]
        dsimp only [kellyTightGame]
        simp only [hi, ↓reduceIte, div_one]
        have hn0 : (n : ℝ) ≠ 0 := by linarith
        rw [div_mul_eq_mul_div, div_eq_iff h2n1_pos.ne']
        field_simp [hn0]
    have hw_nn : ∀ i, 0 ≤ kellyTightBid n i := fun i => by
      unfold kellyTightBid
      split_ifs <;> positivity
    exact ⟨hw_nn, herase, fun i => (hfoc i).le, fun i _ => hfoc i⟩
  set opt : Fin (n + 1) → ℝ := Pi.single (0 : Fin (n + 1)) 1
  have hopt_welfare : (kellyTightGame n).welfare opt = 1 := by
    rw [KellyGame.welfare, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.sum_eq_zero fun i hi => by
        simp only [opt, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi), hU0 i]]
    simp [kellyTightGame, opt]
  have hopt : (kellyTightGame n).IsSocialOptimum opt := by
    refine ⟨⟨fun i => by by_cases hi : i = 0 <;> simp [opt, hi],
      by simp [kellyTightGame, opt]⟩, fun x hx => ?_⟩
    rw [hopt_welfare]
    calc (kellyTightGame n).welfare x
        ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => by
          unfold kellyTightGame
          dsimp only
          split_ifs
          · exact le_rfl
          · exact mul_le_of_le_one_left (hx.1 i) hslope_le
      _ ≤ 1 := hx.2
  have hne_welfare :
      (kellyTightGame n).welfare ((kellyTightGame n).allocation (kellyTightBid n)) =
        3 / 4 + 1 / (4 * (2 * (n : ℝ) - 1)) := by
    rw [KellyGame.welfare, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    have hrest : ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
        (kellyTightGame n).utility i ((kellyTightGame n).allocation (kellyTightBid n) i) =
        ∑ _i ∈ Finset.univ.erase (0 : Fin (n + 1)),
          ((n : ℝ) / (2 * (n : ℝ) - 1) * (1 / (2 * (n : ℝ)))) :=
      Finset.sum_congr rfl fun i hi => by
        have hne0 := Finset.ne_of_mem_erase hi
        rw [halloc_ne i hne0]
        simp [kellyTightGame, hne0]
    rw [hrest, Finset.sum_const, hcard_erase, nsmul_eq_mul, halloc0]
    simp only [kellyTightGame, ↓reduceIte]
    have hne1 : (2 * (n : ℝ) - 1) ≠ 0 := h2n1_pos.ne'
    field_simp [hne1]; ring
  exact ⟨hU, hU0, hne, hopt, hopt_welfare, hne_welfare⟩

/-- **Tightness of the `3/4` efficiency bound** ([JohariTsitsiklis2004]; [Johari2007], §21.2,
Theorem 21.4): for every `ε > 0`, there exists a finite linear-utility Kelly game whose unique
Nash equilibrium achieves strictly less than `(3/4 + ε)` times the optimal social welfare. -/
theorem exists_nash_welfare_lt_three_fourths_add {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (G : KellyGame (Fin (n + 1))) (w x : Fin (n + 1) → ℝ),
      0 < G.capacity ∧
      (∀ i, IsAdmissibleUtility (G.utility i)) ∧
      (∀ i, 0 ≤ G.utility i 0) ∧
      G.IsNashEquilibrium w ∧
      G.IsSocialOptimum x ∧
      0 < G.welfare x ∧
      G.welfare (G.allocation w) < (3 / 4 + ε) * G.welfare x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (8 * ε) + 1)
  set n := max N 2
  have hn2 : 2 ≤ n := le_max_right N 2
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left N 2
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  obtain ⟨hU, hU0, hne, hopt, hopt_w, hne_w⟩ := kellyTightGame_spec hn2
  refine ⟨n, kellyTightGame n, kellyTightBid n, Pi.single (M := fun _ => ℝ) 0 1,
    by simp [kellyTightGame], hU, fun i => (hU0 i).ge, hne, hopt, by linarith, ?_⟩
  rw [hopt_w, hne_w, mul_one]
  have hgap : 1 / (4 * (2 * (n : ℝ) - 1)) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 / (8 * ε) < (n : ℝ) - 1 := by linarith
    have h2 : 1 < ((n : ℝ) - 1) * (8 * ε) := (div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * ε)).mp h1
    nlinarith
  linarith

end Tightness

end KellyGame

end Cslib.GameTheory
