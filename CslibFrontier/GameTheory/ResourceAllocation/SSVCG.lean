/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.Filter.AtTopBot.Defs
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Scalar Strategy VCG (SSVCG) mechanisms for divisible resource allocation

When a resource manager moves beyond a single market-clearing price while keeping one-dimensional
bids `θ_i > 0`, a **Scalar Strategy VCG (SSVCG)** mechanism fixes a single-parameter family
`{U(·; θ)}_{θ > 0}` of strictly concave admissible surrogate utility functions whose marginal
utilities cover `(0, ∞)` at every allocation `d ≥ 0` ([Johari2007], §21.4, Assumption 2). Given
declared parameters `θ : ι → ℝ` (`θ_i > 0`), the mechanism chooses the unique feasible allocation
`d(θ)` maximizing `∑_i U(d_i; θ_i)` and charges each user `i` the Clarke-pivot Groves payment
`t_i(θ) = h_i(θ_{-i}) - ∑_{j ≠ i} U(d_j(θ); θ_j)`.

This module formalizes §21.4 of [Johari2007]:

* **Lemma 21.11** (`SSVCGMechanism.isNashEquilibrium_iff`): `θ` is a Nash equilibrium iff for
  every user `i`, `d(θ)` maximizes `U_i(x_i) + ∑_{j ≠ i} U(x_j; θ_j)` over feasible allocations.
* **Corollary 21.12** (`SSVCGMechanism.exists_efficient_isNashEquilibrium`): every SSVCG mechanism
  admits a socially optimal Nash equilibrium (price of stability `1`).
* **Example 21.13** (`exists_bluff_isNashEquilibrium`): with finite marginal utility at `0`,
  inefficient "bluff" Nash equilibria exist (demonstrated explicitly on two identical users with
  `U(x) = log (1 + x)` and surrogate family `U(x; θ) = θ log (1 + x)`).
* **Proposition 21.14** (`SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope`):
  when every user's marginal utility diverges to `+∞` as `x → 0⁺` (`HasInfiniteInitialSlope`),
  *every* Nash equilibrium of an SSVCG mechanism is socially optimal (price of anarchy `1`).

`SSVCGMechanism` and its `clarkePivot`, `payment`, and `IsNashEquilibrium` operate directly on
positive scalar bids `θ : ι → ℝ` and `sSup` over the continuous feasible simplex rather than
wrapping `Cslib.GameTheory.Mechanism` (`CslibFrontier.GameTheory.Mechanism.VCG`, whose `vcg` assumes
`[Fintype Ω]` and collects full functional bids `ι → Ω → ℝ`) or `CostGame`
(`CslibFrontier.GameTheory.Strategic.Basic`), keeping scalar surrogate deviations subtype-free.

## Main definitions

* `Cslib.GameTheory.IsSSVCGSurrogateFamily`: admissible single-parameter surrogate family
  (Assumption 2 of [Johari2007], §21.4).
* `Cslib.GameTheory.HasInfiniteInitialSlope`: concave, continuous, strictly increasing utilities
  with `U'(x) → +∞` as `x → 0⁺`.
* `Cslib.GameTheory.SSVCGMechanism`: scalar-strategy VCG mechanism `(capacity, surrogate)` with
  `allocation`, `clarkePivot`, `payment`, `payoff`, and `IsNashEquilibrium`.

## Main results

* `Cslib.GameTheory.SSVCGMechanism.isNashEquilibrium_iff` ([Johari2007], §21.4, Lemma 21.11).
* `Cslib.GameTheory.SSVCGMechanism.exists_efficient_isNashEquilibrium` ([Johari2007], §21.4,
  Corollary 21.12).
* `Cslib.GameTheory.exists_bluff_isNashEquilibrium` ([Johari2007], §21.4, Example 21.13).
* `Cslib.GameTheory.SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope`
  ([Johari2007], §21.4, Proposition 21.14).

## References

* [Johari2007]
-/

public section

open Filter Set
open scoped Topology

namespace Cslib.GameTheory

/-! ### Assumptions for SSVCG mechanisms -/

/-- An admissible single-parameter surrogate utility family `{U(·; θ)}_{θ > 0}` for Scalar
Strategy VCG: for every `θ > 0`, `surrogate θ` is admissible (`IsAdmissibleUtility`) and strictly
concave on `[0, ∞)`, and at every allocation `d ≥ 0` the marginal utility covers `(0, ∞)` as
`θ > 0` varies (Assumption 2 of [Johari2007], §21.4). -/
structure IsSSVCGSurrogateFamily (surrogate : ℝ → ℝ → ℝ) : Prop where
  /-- Each surrogate utility `U(·; θ)` (`θ > 0`) satisfies Assumption 1. -/
  admissible : ∀ θ, 0 < θ → IsAdmissibleUtility (surrogate θ)
  /-- Each surrogate utility `U(·; θ)` (`θ > 0`) is strictly concave on `[0, ∞)`. -/
  strictConcaveOn : ∀ θ, 0 < θ → StrictConcaveOn ℝ (Ici 0) (surrogate θ)
  /-- Surjectivity of positive marginal utilities at every nonnegative allocation. -/
  surjective_derivWithin : ∀ γ, 0 < γ → ∀ d, 0 ≤ d →
    ∃ θ, 0 < θ ∧ derivWithin (surrogate θ) (Ici 0) d = γ

/-- A concave, continuous, strictly increasing utility on `[0, ∞)` that is differentiable on
`(0, ∞)` with infinite marginal utility at `0` (`U'(x) → +∞` as `x → 0⁺`), as assumed in
[Johari2007], §21.4, Proposition 21.14. -/
structure HasInfiniteInitialSlope (u : ℝ → ℝ) : Prop where
  /-- Concavity on `[0, ∞)`. -/
  concaveOn : ConcaveOn ℝ (Ici 0) u
  /-- Continuity on `[0, ∞)`. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- Strict monotonicity on `[0, ∞)`. -/
  strictMonoOn : StrictMonoOn u (Ici 0)
  /-- Differentiability on `(0, ∞)`. -/
  differentiableOn : DifferentiableOn ℝ u (Ioi 0)
  /-- Marginal utility diverges to `+∞` as the allocation approaches `0` from above. -/
  tendsto_deriv_atTop : Tendsto (deriv u) (𝓝[>] 0) atTop

private theorem HasInfiniteInitialSlope.hasDerivAt {u : ℝ → ℝ} (hu : HasInfiniteInitialSlope u)
    {x : ℝ} (hx : 0 < x) : HasDerivAt u (deriv u x) x :=
  ((hu.differentiableOn x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt

private theorem HasInfiniteInitialSlope.le_add_deriv {u : ℝ → ℝ} (hu : HasInfiniteInitialSlope u)
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    u y ≤ u x + deriv u x * (y - x) :=
  hu.concaveOn.le_add_mul_of_hasDerivWithinAt hx.le hy (hu.hasDerivAt hx).hasDerivWithinAt

private theorem HasInfiniteInitialSlope.deriv_pos {u : ℝ → ℝ} (hu : HasInfiniteInitialSlope u)
    {x : ℝ} (hx : 0 < x) : 0 < deriv u x := by
  have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
  have hlt : u x < u (x + 1) := hu.strictMonoOn hx.le hx1 (by linarith)
  have hle := hu.le_add_deriv hx hx1
  linarith

/-! ### SSVCG mechanism definition -/

/-- A **Scalar Strategy VCG (SSVCG)** mechanism for allocating a single divisible resource of
capacity `capacity` via a single-parameter surrogate utility family `surrogate`
([Johari2007], §21.4). -/
structure SSVCGMechanism (ι : Type*) where
  /-- Total divisible capacity `C` of the resource. -/
  capacity : ℝ
  /-- Single-parameter surrogate utility family `surrogate θ : ℝ → ℝ`. -/
  surrogate : ℝ → ℝ → ℝ

namespace SSVCGMechanism

variable {ι : Type*} (M : SSVCGMechanism ι)

/-- The surrogate `KellyGame` formed from the declared parameter profile `θ : ι → ℝ`. -/
@[expose] def reportedGame (θ : ι → ℝ) : KellyGame ι where
  capacity := M.capacity
  utility := fun i => M.surrogate (θ i)

/-- The allocation rule `d(θ)` choosing a maximizer of reported surrogate welfare `∑_i U(d_i; θ_i)`
over feasible allocations (unique under `IsSSVCGSurrogateFamily`). -/
@[expose] noncomputable def allocation [Fintype ι] (θ : ι → ℝ) : ι → ℝ :=
  open scoped Classical in
  if h : ∃ d, (M.reportedGame θ).IsSocialOptimum d then Classical.choose h else 0

/-- The Clarke pivot `h_i(θ_{-i}) = sup_{x feasible} ∑_{j ≠ i} U(x_j; θ_j)`, independent of
user `i`'s own declaration `θ_i`. -/
@[expose] noncomputable def clarkePivot [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (i : ι) : ℝ :=
  sSup ((fun x : ι → ℝ => ∑ j ∈ Finset.univ.erase i, M.surrogate (θ j) (x j)) ''
    {x | (M.reportedGame θ).IsFeasibleAllocation x})

/-- The Groves/VCG payment `t_i(θ) = h_i(θ_{-i}) - ∑_{j ≠ i} U(d_j(θ); θ_j)` charged to user `i`
([Johari2007], §21.4). -/
@[expose] noncomputable def payment [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (i : ι) : ℝ :=
  M.clarkePivot θ i - ∑ j ∈ Finset.univ.erase i, M.surrogate (θ j) (M.allocation θ j)

/-- Quasilinear payoff `U_i(d_i(θ)) - t_i(θ)` of user `i` under true utilities `U`. -/
@[expose] noncomputable def payoff [Fintype ι] [DecidableEq ι]
    (U : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) : ℝ :=
  U i (M.allocation θ i) - M.payment θ i

/-- A positive parameter profile `θ` (`∀ i, 0 < θ i`) is a **Nash equilibrium** of the SSVCG
mechanism under true utilities `U` if no user can strictly increase its payoff by changing its
scalar strategy to any `t > 0` ([Johari2007], §21.4). -/
@[expose] def IsNashEquilibrium [Fintype ι] [DecidableEq ι]
    (U : ι → ℝ → ℝ) (θ : ι → ℝ) : Prop :=
  (∀ i, 0 < θ i) ∧ ∀ i (t : ℝ), 0 < t → M.payoff U (Function.update θ i t) i ≤ M.payoff U θ i

section Basic

variable [Fintype ι]

theorem allocation_isSocialOptimum {M : SSVCGMechanism ι} (hC : 0 ≤ M.capacity)
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i) :
    (M.reportedGame θ).IsSocialOptimum (M.allocation θ) := by
  have hex : ∃ d, (M.reportedGame θ).IsSocialOptimum d :=
    KellyGame.exists_isSocialOptimum hC fun i =>
      (hfam.admissible (θ i) (hθ i)).continuousOn.mono Icc_subset_Ici_self
  unfold allocation
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem allocation_eq_of_isSocialOptimum {M : SSVCGMechanism ι} (hC : 0 ≤ M.capacity)
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i)
    {d : ι → ℝ} (hd : (M.reportedGame θ).IsSocialOptimum d) :
    M.allocation θ = d := by
  obtain ⟨d₀, _, huniq⟩ := KellyGame.existsUnique_isSocialOptimum_of_strictConcaveOn
    (G := M.reportedGame θ) hC
    (fun i => (hfam.admissible (θ i) (hθ i)).continuousOn.mono Icc_subset_Ici_self)
    (fun i => (hfam.strictConcaveOn (θ i) (hθ i)).subset Icc_subset_Ici_self
      (convex_Icc 0 M.capacity))
  rw [huniq (M.allocation θ) (allocation_isSocialOptimum hC hfam hθ), huniq d hd]

theorem clarkePivot_update_self [DecidableEq ι] (θ : ι → ℝ) (i : ι) (t : ℝ) :
    M.clarkePivot (Function.update θ i t) i = M.clarkePivot θ i := by
  unfold clarkePivot
  congr 1
  ext y
  simp only [mem_image, Set.mem_ofPred_eq, KellyGame.IsFeasibleAllocation, reportedGame]
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> refine ⟨x, hx, ?_⟩
  · exact Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · exact Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Clarke-pivot SSVCG payments are always nonnegative for admissible surrogate families. -/
theorem payment_nonneg [DecidableEq ι] {M : SSVCGMechanism ι} (hC : 0 ≤ M.capacity)
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i) (i : ι) :
    0 ≤ M.payment θ i := by
  unfold payment clarkePivot
  rw [sub_nonneg]
  have hfeas := (allocation_isSocialOptimum hC hfam hθ).1
  have hcont : ContinuousOn
      (fun x : ι → ℝ => ∑ j ∈ Finset.univ.erase i, M.surrogate (θ j) (x j))
      {x | (M.reportedGame θ).IsFeasibleAllocation x} := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    have hj_cont : ContinuousOn (M.surrogate (θ j)) (Icc 0 M.capacity) :=
      (hfam.admissible (θ j) (hθ j)).continuousOn.mono Icc_subset_Ici_self
    exact hj_cont.comp (continuous_apply j).continuousOn fun x hx =>
      ⟨hx.1 j, (M.reportedGame θ).isFeasibleAllocation_le_capacity hx j⟩
  exact le_csSup (KellyGame.isCompact_isFeasibleAllocation.image_of_continuousOn hcont).bddAbove
    ⟨M.allocation θ, hfeas, rfl⟩

end Basic

/-! ### Lemma 21.11, Corollary 21.12, and Proposition 21.14 -/

section Characterization

variable [Fintype ι] [DecidableEq ι]

/-- The user-`i` hybrid game replacing user `i`'s surrogate utility with its true utility `U i`. -/
@[expose] def hybridGame (M : SSVCGMechanism ι) (U : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) :
    KellyGame ι where
  capacity := M.capacity
  utility := Function.update (fun j => M.surrogate (θ j)) i (U i)

private theorem hybridGame_welfare_eq (M : SSVCGMechanism ι) (U : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι)
    (x : ι → ℝ) :
    (M.hybridGame U θ i).welfare x =
      U i (x i) + ∑ j ∈ Finset.univ.erase i, M.surrogate (θ j) (x j) := by
  unfold KellyGame.welfare hybridGame
  dsimp only
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem payoff_eq_hybridWelfare_sub_pivot (M : SSVCGMechanism ι) (U : ι → ℝ → ℝ)
    (θ : ι → ℝ) (i : ι) :
    M.payoff U θ i = (M.hybridGame U θ i).welfare (M.allocation θ) - M.clarkePivot θ i := by
  rw [payoff, payment, hybridGame_welfare_eq]
  ring

omit [Fintype ι] in
private theorem hybridGame_strictMonoOn {M : SSVCGMechanism ι}
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    {θ : ι → ℝ} (hθ : ∀ j, 0 < θ j) {i : ι} (hUi : StrictMonoOn (U i) (Ici 0)) :
    ∀ j, StrictMonoOn ((M.hybridGame U θ i).utility j) (Icc 0 M.capacity) := fun j => by
  unfold hybridGame; dsimp only
  by_cases hji : j = i
  · subst hji; rw [Function.update_self]; exact hUi.mono Icc_subset_Ici_self
  · rw [Function.update_of_ne hji]
    exact (hfam.admissible (θ j) (hθ j)).strictMonoOn.mono Icc_subset_Ici_self

private theorem hybridGame_isSocialOptimum_of_reported_update {M : SSVCGMechanism ι}
    (hC : 0 ≤ M.capacity) (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    {θ : ι → ℝ} (hθ : ∀ j, 0 < θ j) (hne : M.IsNashEquilibrium U θ) {i : ι} {t : ℝ}
    (ht : 0 < t) (hθ' : ∀ j, 0 < Function.update θ i t j) {xStar : ι → ℝ}
    (hxStar : (M.hybridGame U θ i).IsSocialOptimum xStar)
    (hrep_opt : (M.reportedGame (Function.update θ i t)).IsSocialOptimum xStar) :
    (M.hybridGame U θ i).IsSocialOptimum (M.allocation θ) := by
  set θ' := Function.update θ i t
  have halloc_eq : M.allocation θ' = xStar :=
    allocation_eq_of_isSocialOptimum hC hfam hθ' hrep_opt
  have hbr := hne.2 i t ht
  rw [payoff_eq_hybridWelfare_sub_pivot, payoff_eq_hybridWelfare_sub_pivot,
    M.clarkePivot_update_self θ i t] at hbr
  have hw_eq : (M.hybridGame U θ' i).welfare (M.allocation θ') =
      (M.hybridGame U θ i).welfare xStar := by
    rw [halloc_eq, hybridGame_welfare_eq, hybridGame_welfare_eq]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      simp only [θ', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hw_eq] at hbr
  refine ⟨(allocation_isSocialOptimum hC hfam hθ).1, fun x hx => ?_⟩
  linarith [hxStar.2 x hx]

/-- **Nash equilibrium characterization for SSVCG** ([Johari2007], §21.4, Lemma 21.11):
for an admissible surrogate family and admissible true utilities, a positive parameter profile
`θ` is a Nash equilibrium iff for every user `i`, `d(θ)` maximizes
`U_i(x_i) + ∑_{j ≠ i} U(x_j; θ_j)` over feasible allocations. -/
theorem isNashEquilibrium_iff {M : SSVCGMechanism ι} (hC : 0 < M.capacity)
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    (hU : ∀ i, IsAdmissibleUtility (U i)) {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i) :
    M.IsNashEquilibrium U θ ↔
      ∀ i, (M.hybridGame U θ i).IsSocialOptimum (M.allocation θ) := by
  constructor
  · intro hne i
    have : Nonempty ι := ⟨i⟩
    have hhybrid_adm : ∀ j, IsAdmissibleUtility ((M.hybridGame U θ i).utility j) := fun j => by
      unfold hybridGame; dsimp only
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hU j
      · rw [Function.update_of_ne hji]; exact hfam.admissible (θ j) (hθ j)
    obtain ⟨xStar, hxStar⟩ := KellyGame.exists_isSocialOptimum hC.le fun j =>
      (hhybrid_adm j).continuousOn.mono Icc_subset_Ici_self
    obtain ⟨hx_feas, hx_sum, μ, hμ, hle, heq⟩ :=
      (KellyGame.isSocialOptimum_iff_kkt hC hhybrid_adm).mp hxStar
    have hγ : 0 < derivWithin (U i) (Ici 0) (xStar i) := (hU i).derivWithin_pos (hx_feas.1 i)
    obtain ⟨t, ht_pos, ht_deriv⟩ := hfam.surjective_derivWithin _ hγ (xStar i) (hx_feas.1 i)
    set θ' := Function.update θ i t
    have hθ' : ∀ j, 0 < θ' j := fun j => by
      by_cases hji : j = i
      · subst hji; simpa only [θ', Function.update_self] using ht_pos
      · simpa only [θ', Function.update_of_ne hji] using hθ j
    have hrep_adm : ∀ j, IsAdmissibleUtility ((M.reportedGame θ').utility j) :=
      fun j => hfam.admissible (θ' j) (hθ' j)
    have hrep_opt : (M.reportedGame θ').IsSocialOptimum xStar := by
      rw [KellyGame.isSocialOptimum_iff_kkt hC hrep_adm]
      refine ⟨hx_feas, hx_sum, μ, hμ, fun j => ?_, fun j hj => ?_⟩
      · by_cases hji : j = i
        · subst hji
          have h1 := hle j
          simp only [reportedGame, θ', Function.update_self, ht_deriv]
          simpa only [hybridGame, Function.update_self] using h1
        · have h1 := hle j
          simp only [reportedGame, θ', Function.update_of_ne hji]
          simpa only [hybridGame, Function.update_of_ne hji] using h1
      · by_cases hji : j = i
        · subst hji
          have h1 := heq j hj
          simp only [reportedGame, θ', Function.update_self, ht_deriv]
          simpa only [hybridGame, Function.update_self] using h1
        · have h1 := heq j hj
          simp only [reportedGame, θ', Function.update_of_ne hji]
          simpa only [hybridGame, Function.update_of_ne hji] using h1
    exact hybridGame_isSocialOptimum_of_reported_update hC.le hfam hθ hne ht_pos hθ' hxStar hrep_opt
  · intro hopt
    refine ⟨hθ, fun i t ht => ?_⟩
    set θ' := Function.update θ i t
    have hθ' : ∀ j, 0 < θ' j := fun j => by
      by_cases hji : j = i
      · subst hji; simpa only [θ', Function.update_self] using ht
      · simpa only [θ', Function.update_of_ne hji] using hθ j
    have hfeas' : (M.hybridGame U θ i).IsFeasibleAllocation (M.allocation θ') :=
      (allocation_isSocialOptimum hC.le hfam hθ').1
    rw [payoff_eq_hybridWelfare_sub_pivot, payoff_eq_hybridWelfare_sub_pivot,
      M.clarkePivot_update_self θ i t]
    have hw_eq : (M.hybridGame U θ' i).welfare (M.allocation θ') =
        (M.hybridGame U θ i).welfare (M.allocation θ') := by
      rw [hybridGame_welfare_eq, hybridGame_welfare_eq]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by
        simp only [θ', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hw_eq]
    linarith [(hopt i).2 (M.allocation θ') hfeas']

/-- **Existence of a fully efficient SSVCG Nash equilibrium (`PoS = 1`)** ([Johari2007], §21.4,
Corollary 21.12): for any admissible utilities and positive capacity, an SSVCG mechanism admits a
Nash equilibrium whose allocation solves `SYSTEM`. -/
theorem exists_efficient_isNashEquilibrium [Nonempty ι] {M : SSVCGMechanism ι}
    (hC : 0 < M.capacity) (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    (hU : ∀ i, IsAdmissibleUtility (U i)) :
    ∃ θ, M.IsNashEquilibrium U θ ∧
      (⟨M.capacity, U⟩ : KellyGame ι).IsSocialOptimum (M.allocation θ) := by
  set G : KellyGame ι := ⟨M.capacity, U⟩
  obtain ⟨dS, hdS⟩ := KellyGame.exists_isSocialOptimum (G := G) hC.le fun i =>
    (hU i).continuousOn.mono Icc_subset_Ici_self
  obtain ⟨hdS_feas, hdS_sum, μ, hμ, hle, heq⟩ :=
    (KellyGame.isSocialOptimum_iff_kkt (G := G) hC hU).mp hdS
  have hchoose : ∀ i, ∃ t, 0 < t ∧
      derivWithin (M.surrogate t) (Ici 0) (dS i) = derivWithin (U i) (Ici 0) (dS i) :=
    fun i => hfam.surjective_derivWithin _ ((hU i).derivWithin_pos (hdS_feas.1 i)) (dS i)
      (hdS_feas.1 i)
  choose θ hθ hθ_deriv using hchoose
  have hrep_opt : (M.reportedGame θ).IsSocialOptimum dS := by
    rw [KellyGame.isSocialOptimum_iff_kkt hC (fun i => hfam.admissible (θ i) (hθ i))]
    refine ⟨hdS_feas, hdS_sum, μ, hμ, fun i => ?_, fun i hi => ?_⟩
    · simp only [reportedGame, hθ_deriv i]; exact hle i
    · simp only [reportedGame, hθ_deriv i]; exact heq i hi
  have halloc_eq : M.allocation θ = dS :=
    allocation_eq_of_isSocialOptimum hC.le hfam hθ hrep_opt
  have hne : M.IsNashEquilibrium U θ := by
    rw [isNashEquilibrium_iff hC hfam hU hθ]
    intro i
    rw [halloc_eq]
    have hhybrid_adm : ∀ j, IsAdmissibleUtility ((M.hybridGame U θ i).utility j) := fun j => by
      unfold hybridGame; dsimp only
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hU j
      · rw [Function.update_of_ne hji]; exact hfam.admissible (θ j) (hθ j)
    rw [KellyGame.isSocialOptimum_iff_kkt hC hhybrid_adm]
    refine ⟨hdS_feas, hdS_sum, μ, hμ, fun j => ?_, fun j hj => ?_⟩
    · unfold hybridGame; dsimp only
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hle j
      · rw [Function.update_of_ne hji, hθ_deriv j]; exact hle j
    · unfold hybridGame; dsimp only
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact heq j hj
      · rw [Function.update_of_ne hji, hθ_deriv j]; exact heq j hj
  exact ⟨θ, hne, halloc_eq ▸ hdS⟩

private theorem hybrid_opt_pos_of_infiniteSlope {M : SSVCGMechanism ι} (hC : 0 < M.capacity)
    (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    {θ : ι → ℝ} (hθ : ∀ j, 0 < θ j) {i : ι} (hUi : HasInfiniteInitialSlope (U i))
    {x : ι → ℝ} (hx : (M.hybridGame U θ i).IsSocialOptimum x) :
    0 < x i := by
  have : Nonempty ι := ⟨i⟩
  have hsum : ∑ j, x j = M.capacity :=
    hx.sum_eq_capacity (hybridGame_strictMonoOn hfam hθ hUi.strictMonoOn)
  refine lt_of_le_of_ne (hx.1.1 i) (Ne.symm fun hxi0 => ?_)
  have hex_k : ∃ k, k ≠ i ∧ 0 < x k := by
    by_contra hall
    push Not at hall
    have hle0 : ∑ j, x j ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      by_cases hji : j = i
      · subst hji; linarith
      · exact hall j hji
    linarith
  obtain ⟨k, hki, hxk⟩ := hex_k
  set g := M.surrogate (θ k)
  have hg : IsAdmissibleUtility g := hfam.admissible (θ k) (hθ k)
  set bound := derivWithin g (Ici 0) 0
  have hev_slope : ∀ᶠ t in 𝓝[>] (0 : ℝ), bound < deriv (U i) t :=
    hUi.tendsto_deriv_atTop.eventually (eventually_gt_atTop bound)
  have hev_Ioc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 (x k) :=
    Filter.eventually_iff.mpr (Ioc_mem_nhdsGT hxk)
  obtain ⟨t, ⟨ht0, htxk⟩, hslope⟩ := (hev_Ioc.and hev_slope).exists
  set y := Function.update (Function.update x k (x k - t)) i t
  have hyi : y i = t := by simp only [y, Function.update_self]
  have hyk : y k = x k - t := by
    simp only [y, Function.update_of_ne hki, Function.update_self]
  have hy_other : ∀ j, j ≠ k → j ≠ i → y j = x j := fun j hjk hji => by
    simp only [y, Function.update_of_ne hji, Function.update_of_ne hjk]
  have hy_feas : (M.hybridGame U θ i).IsFeasibleAllocation y := by
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji; rw [hyi]; exact ht0.le
      · by_cases hjk : j = k
        · subst hjk; rw [hyk]; linarith
        · rw [hy_other j hjk hji]; exact hx.1.1 j
    · have hsum_y : ∑ j, y j = ∑ j, x j := by
        rw [← Finset.add_sum_erase _ y (Finset.mem_univ i),
          ← Finset.add_sum_erase _ x (Finset.mem_univ i)]
        have hk_mem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
        rw [← Finset.add_sum_erase _ y hk_mem, ← Finset.add_sum_erase _ x hk_mem]
        have hrest : ∑ j ∈ (Finset.univ.erase i).erase k, y j =
            ∑ j ∈ (Finset.univ.erase i).erase k, x j :=
          Finset.sum_congr rfl fun j hj =>
            hy_other j (Finset.ne_of_mem_erase hj)
              (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
        rw [hrest, hyi, hyk, hxi0]
        ring
      linarith [hx.1.2]
  have hle := hx.2 y hy_feas
  rw [hybridGame_welfare_eq, hybridGame_welfare_eq] at hle
  have hk_mem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
  rw [← Finset.add_sum_erase _ (fun j => M.surrogate (θ j) (y j)) hk_mem,
    ← Finset.add_sum_erase _ (fun j => M.surrogate (θ j) (x j)) hk_mem] at hle
  have hrest : ∑ j ∈ (Finset.univ.erase i).erase k, M.surrogate (θ j) (y j) =
      ∑ j ∈ (Finset.univ.erase i).erase k, M.surrogate (θ j) (x j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [hy_other j (Finset.ne_of_mem_erase hj)
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))]
  rw [hrest, hyi, hyk, hxi0] at hle
  have hU_lb : deriv (U i) t * t ≤ U i t - U i 0 := by
    have hconc := hUi.le_add_deriv ht0 le_rfl
    linarith
  have hg_ub : g (x k) - g (x k - t) ≤ bound * t := by
    have hconc := hg.le_add_derivWithin (by linarith : 0 ≤ x k - t) hxk.le
    have hanti := hg.derivWithin_antitoneOn le_rfl (by linarith : 0 ≤ x k - t) (by linarith)
    have hmul : derivWithin g (Ici 0) (x k - t) * t ≤ bound * t :=
      mul_le_mul_of_nonneg_right hanti ht0.le
    linarith
  have hdiff : U i t - U i 0 ≤ g (x k) - g (x k - t) := by linarith
  have hcontr : deriv (U i) t * t ≤ bound * t := hU_lb.trans (hdiff.trans hg_ub)
  nlinarith

/-- **Full efficiency (`PoA = 1`) of SSVCG under infinite initial marginal utility**
([Johari2007], §21.4, Proposition 21.14): if capacity is positive and every user's concave strictly
increasing utility satisfies `U_i'(x) → +∞` as `x → 0⁺`, then *every* Nash equilibrium `θ` of an
SSVCG mechanism induces a socially optimal allocation `M.allocation θ`. -/
theorem isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope {M : SSVCGMechanism ι}
    (hC : 0 < M.capacity) (hfam : IsSSVCGSurrogateFamily M.surrogate) {U : ι → ℝ → ℝ}
    (hU : ∀ i, HasInfiniteInitialSlope (U i)) {θ : ι → ℝ} (hne : M.IsNashEquilibrium U θ) :
    (⟨M.capacity, U⟩ : KellyGame ι).IsSocialOptimum (M.allocation θ) := by
  have hθ : ∀ i, 0 < θ i := hne.1
  set d := M.allocation θ
  have hd_rep : (M.reportedGame θ).IsSocialOptimum d := allocation_isSocialOptimum hC.le hfam hθ
  by_cases hEmpty : IsEmpty ι
  · exact ⟨hd_rep.1, fun x _ => by simp [KellyGame.welfare]⟩
  have : Nonempty ι := not_isEmpty_iff.mp hEmpty
  by_cases hcard : 2 ≤ Fintype.card ι
  · have hhybrid_opt : ∀ i, (M.hybridGame U θ i).IsSocialOptimum d := by
      intro i
      have hcont_h : ∀ j, ContinuousOn ((M.hybridGame U θ i).utility j) (Icc 0 M.capacity) := by
        intro j
        unfold hybridGame; dsimp only
        by_cases hji : j = i
        · subst hji; rw [Function.update_self]; exact (hU j).continuousOn.mono Icc_subset_Ici_self
        · rw [Function.update_of_ne hji]
          exact (hfam.admissible (θ j) (hθ j)).continuousOn.mono Icc_subset_Ici_self
      obtain ⟨xStar, hxStar⟩ := KellyGame.exists_isSocialOptimum hC.le hcont_h
      have hx_pos : 0 < xStar i := hybrid_opt_pos_of_infiniteSlope hC hfam hθ (hU i) hxStar
      have hx_sum : ∑ j, xStar j = M.capacity :=
        hxStar.sum_eq_capacity (hybridGame_strictMonoOn hfam hθ (hU i).strictMonoOn)
      have hγ : 0 < deriv (U i) (xStar i) := (hU i).deriv_pos hx_pos
      obtain ⟨t, ht_pos, ht_deriv⟩ := hfam.surjective_derivWithin _ hγ (xStar i) hx_pos.le
      set θ' := Function.update θ i t
      have hθ' : ∀ j, 0 < θ' j := fun j => by
        by_cases hji : j = i
        · subst hji; simpa only [θ', Function.update_self] using ht_pos
        · simpa only [θ', Function.update_of_ne hji] using hθ j
      have hdi_deriv : HasDerivWithinAt ((M.hybridGame U θ i).utility i) (deriv (U i) (xStar i))
          (Icc 0 M.capacity) (xStar i) := by
        simpa only [hybridGame, Function.update_self] using
          ((hU i).hasDerivAt hx_pos).hasDerivWithinAt
      have hdj_deriv : ∀ {j}, j ≠ i →
          HasDerivWithinAt ((M.hybridGame U θ i).utility j)
            (derivWithin (M.surrogate (θ j)) (Ici 0) (xStar j))
            (Icc 0 M.capacity) (xStar j) := fun {j} hji => by
        simp only [hybridGame, Function.update_of_ne hji]
        exact ((hfam.admissible (θ j) (hθ j)).hasDerivWithinAt (hxStar.1.1 j)).mono
          Icc_subset_Ici_self
      have hrep_opt : (M.reportedGame θ').IsSocialOptimum xStar := by
        rw [KellyGame.isSocialOptimum_iff_kkt hC fun j => hfam.admissible (θ' j) (hθ' j)]
        refine ⟨hxStar.1, hx_sum, deriv (U i) (xStar i), hγ, fun j => ?_, fun j hj => ?_⟩
        · by_cases hji : j = i
          · subst hji; simp only [reportedGame, θ', Function.update_self, ht_deriv]; exact le_rfl
          · simp only [reportedGame, θ', Function.update_of_ne hji]
            exact hxStar.swap_deriv_le (Ne.symm hji) hx_pos hdi_deriv (hdj_deriv hji)
        · by_cases hji : j = i
          · subst hji; simp only [reportedGame, θ', Function.update_self, ht_deriv]
          · simp only [reportedGame, θ', Function.update_of_ne hji]
            exact le_antisymm
              (hxStar.swap_deriv_le (Ne.symm hji) hx_pos hdi_deriv (hdj_deriv hji))
              (hxStar.swap_deriv_le hji hj (hdj_deriv hji) hdi_deriv)
      exact hybridGame_isSocialOptimum_of_reported_update hC.le hfam hθ hne ht_pos hθ' hxStar
        hrep_opt
    have hd_pos : ∀ i, 0 < d i :=
      fun i => hybrid_opt_pos_of_infiniteSlope hC hfam hθ (hU i) (hhybrid_opt i)
    obtain ⟨hd_feas, hd_sum, μ, hμ, _, hrep_eq⟩ :=
      (KellyGame.isSocialOptimum_iff_kkt hC fun i => hfam.admissible (θ i) (hθ i)).mp hd_rep
    have htrue_eq : ∀ i, deriv (U i) (d i) = μ := by
      intro i
      have hother : ∃ k, k ≠ i := by
        have hcard_e : 0 < (Finset.univ.erase i).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]; omega
        obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard_e
        exact ⟨k, Finset.ne_of_mem_erase hk⟩
      obtain ⟨k, hki⟩ := hother
      have hdi_deriv : HasDerivWithinAt ((M.hybridGame U θ i).utility i) (deriv (U i) (d i))
          (Icc 0 M.capacity) (d i) := by
        simpa only [hybridGame, Function.update_self] using
          ((hU i).hasDerivAt (hd_pos i)).hasDerivWithinAt
      have hdk_deriv : HasDerivWithinAt ((M.hybridGame U θ i).utility k)
          (derivWithin (M.surrogate (θ k)) (Ici 0) (d k)) (Icc 0 M.capacity) (d k) := by
        simp only [hybridGame, Function.update_of_ne hki]
        exact ((hfam.admissible (θ k) (hθ k)).hasDerivWithinAt (hd_pos k).le).mono
          Icc_subset_Ici_self
      have heq_ik : deriv (U i) (d i) = derivWithin (M.surrogate (θ k)) (Ici 0) (d k) :=
        le_antisymm
          ((hhybrid_opt i).swap_deriv_le hki (hd_pos k) hdk_deriv hdi_deriv)
          ((hhybrid_opt i).swap_deriv_le (Ne.symm hki) (hd_pos i) hdi_deriv hdk_deriv)
      rw [heq_ik]
      exact hrep_eq k (hd_pos k)
    refine ⟨hd_feas, fun x hx => ?_⟩
    have htan : ∑ i, U i (x i) ≤ ∑ i, (U i (d i) + deriv (U i) (d i) * (x i - d i)) :=
      Finset.sum_le_sum fun i _ => (hU i).le_add_deriv (hd_pos i) (hx.1 i)
    have hlin : ∑ i, deriv (U i) (d i) * (x i - d i) ≤ 0 := by
      have h1 : ∑ i, deriv (U i) (d i) * (x i - d i) = ∑ i, μ * (x i - d i) :=
        Finset.sum_congr rfl fun i _ => by rw [htrue_eq i]
      rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [reportedGame] at hd_sum
      exact mul_nonpos_of_nonneg_of_nonpos hμ.le (by linarith [hx.2, hd_sum])
    rw [Finset.sum_add_distrib] at htan
    change ∑ i, U i (x i) ≤ ∑ i, U i (d i)
    linarith
  · have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have huniv : (Finset.univ : Finset ι) = {i₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ i₀, fun j _ => hsub.elim j i₀⟩
    have hmono_rep : ∀ j, StrictMonoOn ((M.reportedGame θ).utility j) (Icc 0 M.capacity) :=
      fun j => (hfam.admissible (θ j) (hθ j)).strictMonoOn.mono Icc_subset_Ici_self
    have hd_sum : d i₀ = M.capacity := by
      simpa only [huniv, Finset.sum_singleton, reportedGame] using
        hd_rep.sum_eq_capacity hmono_rep
    refine ⟨hd_rep.1, fun x hx => ?_⟩
    have hx_le : x i₀ ≤ d i₀ := by
      have hxs : ∑ i, x i ≤ M.capacity := hx.2
      simp only [huniv, Finset.sum_singleton] at hxs
      linarith
    simp only [KellyGame.welfare, huniv, Finset.sum_singleton]
    exact (hU i₀).strictMonoOn.monotoneOn (hx.1 i₀) (hd_rep.1.1 i₀) hx_le

end Characterization

end SSVCGMechanism

/-! ### Example 21.13: Inefficient bluff equilibrium in SSVCG -/

section BluffExample

private theorem hasDerivAt_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
  have hpos : (1 : ℝ) + x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id' x).const_add 1
  have h2 := (Real.hasDerivAt_log hpos).comp x h1
  simpa only [Function.comp_def, mul_one, one_div] using h2

/-- `U(x) = log (1 + x)` is strictly concave and admissible on `[0, ∞)`, with derivative
`1 / (1 + x)`. -/
theorem isAdmissibleUtility_log_one_add :
    IsAdmissibleUtility (fun x => Real.log (1 + x)) ∧
    StrictConcaveOn ℝ (Ici 0) (fun x => Real.log (1 + x)) ∧
    ∀ x, 0 ≤ x → derivWithin (fun t => Real.log (1 + t)) (Ici 0) x = 1 / (1 + x) := by
  have hderiv : ∀ x, 0 ≤ x → derivWithin (fun t => Real.log (1 + t)) (Ici 0) x = 1 / (1 + x) :=
    fun x hx => (hasDerivAt_log_one_add hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 x hx)
  have hdiff : DifferentiableOn ℝ (fun x => Real.log (1 + x)) (Ici 0) :=
    fun x hx => (hasDerivAt_log_one_add hx).differentiableAt.differentiableWithinAt
  have hstrict : StrictConcaveOn ℝ (Ici 0) (fun x => Real.log (1 + x)) := by
    have hanti : StrictAntiOn (deriv fun x => Real.log (1 + x)) (interior (Ici (0 : ℝ))) := by
      rw [interior_Ici]
      intro x hx y hy hxy
      rw [(hasDerivAt_log_one_add hx.le).deriv, (hasDerivAt_log_one_add hy.le).deriv]
      exact one_div_lt_one_div_of_lt (by linarith [mem_Ioi.mp hx]) (by linarith)
    exact hanti.strictConcaveOn_of_deriv (convex_Ici 0) hdiff.continuousOn
  have hmono : StrictMonoOn (fun x => Real.log (1 + x)) (Ici 0) := fun x hx y hy hxy =>
    Real.log_lt_log (by linarith [mem_Ici.mp hx]) (by linarith)
  exact ⟨⟨hstrict.concaveOn, hmono, hdiff⟩, hstrict, hderiv⟩

/-- The logarithmic single-parameter family `U(x; θ) = θ · log (1 + x)` satisfies Assumption 2
(`IsSSVCGSurrogateFamily`). -/
theorem isSSVCGSurrogateFamily_mul_log_one_add :
    IsSSVCGSurrogateFamily (fun θ x => θ * Real.log (1 + x)) := by
  obtain ⟨hadm, hstrict, _⟩ := isAdmissibleUtility_log_one_add
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_, fun γ hγ d hd => ?_⟩
  · refine ⟨hadm.concaveOn.smul hθ.le, fun x hx y hy hxy =>
      mul_lt_mul_of_pos_left (hadm.strictMonoOn hx hy hxy) hθ,
      hadm.differentiableOn.const_mul θ⟩
  · refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have h := hstrict.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    nlinarith
  · refine ⟨γ * (1 + d), mul_pos hγ (by linarith), ?_⟩
    have h1 : HasDerivWithinAt (fun x => (γ * (1 + d)) * Real.log (1 + x))
        ((γ * (1 + d)) * (1 / (1 + d))) (Ici 0) d :=
      ((hasDerivAt_log_one_add hd).const_mul (γ * (1 + d))).hasDerivWithinAt
    rw [h1.derivWithin (uniqueDiffOn_Ici 0 d hd)]
    have h1d : (1 : ℝ) + d ≠ 0 := by linarith
    field_simp

/-- **Bluff equilibrium in SSVCG** ([Johari2007], §21.4, Example 21.13): with two identical users
having finite-initial-slope utility `U(x) = log (1 + x)` and capacity `1`, the logarithmic SSVCG
mechanism admits an inefficient Nash equilibrium `θ = ![3, 1/4]` allocating the entire capacity to
user `0` (welfare `log 2 < 2 log (3/2)`). -/
theorem exists_bluff_isNashEquilibrium :
    let M : SSVCGMechanism (Fin 2) := ⟨1, fun θ x => θ * Real.log (1 + x)⟩
    let U : Fin 2 → ℝ → ℝ := fun _ x => Real.log (1 + x)
    let θ : Fin 2 → ℝ := ![3, 1 / 4]
    M.IsNashEquilibrium U θ ∧
      M.allocation θ = ![1, 0] ∧
      (⟨1, U⟩ : KellyGame (Fin 2)).welfare (M.allocation θ) <
        (⟨1, U⟩ : KellyGame (Fin 2)).welfare ![1 / 2, 1 / 2] := by
  intro M U θ
  have hfam := isSSVCGSurrogateFamily_mul_log_one_add
  obtain ⟨hadm, _, hderiv⟩ := isAdmissibleUtility_log_one_add
  have hθ : ∀ i, 0 < θ i := fun i => by fin_cases i <;> norm_num [θ]
  have hd_feas : (M.reportedGame θ).IsFeasibleAllocation ![1, 0] :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [M, SSVCGMechanism.reportedGame]⟩
  have hderiv_scaled : ∀ c x, 0 ≤ x →
      derivWithin (fun t => c * Real.log (1 + t)) (Ici 0) x = c / (1 + x) := fun c x hx => by
    have h1 : HasDerivWithinAt (fun t => c * Real.log (1 + t)) (c * (1 / (1 + x))) (Ici 0) x :=
      ((hasDerivAt_log_one_add hx).const_mul c).hasDerivWithinAt
    rw [h1.derivWithin (uniqueDiffOn_Ici 0 x hx)]
    ring
  have hrep_opt : (M.reportedGame θ).IsSocialOptimum ![1, 0] := by
    rw [KellyGame.isSocialOptimum_iff_kkt (by simp [M, SSVCGMechanism.reportedGame])
      fun i => hfam.admissible (θ i) (hθ i)]
    refine ⟨hd_feas, by simp [M, SSVCGMechanism.reportedGame], 3 / 2, by norm_num, ?_, ?_⟩
    · intro i; fin_cases i
      · change derivWithin (fun t => (3 : ℝ) * Real.log (1 + t)) (Ici 0) 1 ≤ 3 / 2
        rw [hderiv_scaled 3 1 zero_le_one]; norm_num
      · change derivWithin (fun t => (1 / 4 : ℝ) * Real.log (1 + t)) (Ici 0) 0 ≤ 3 / 2
        rw [hderiv_scaled (1 / 4) 0 le_rfl]; norm_num
    · intro i hi; fin_cases i
      · change derivWithin (fun t => (3 : ℝ) * Real.log (1 + t)) (Ici 0) 1 = 3 / 2
        rw [hderiv_scaled 3 1 zero_le_one]; norm_num
      · change (0 : ℝ) < 0 at hi; exact absurd hi (lt_irrefl 0)
  have halloc : M.allocation θ = ![1, 0] :=
    SSVCGMechanism.allocation_eq_of_isSocialOptimum (by simp [M]) hfam hθ hrep_opt
  have hne : M.IsNashEquilibrium U θ := by
    rw [SSVCGMechanism.isNashEquilibrium_iff (by simp [M]) hfam (fun _ => hadm) hθ]
    intro i
    rw [halloc]
    have hhybrid_adm : ∀ j, IsAdmissibleUtility ((M.hybridGame U θ i).utility j) := fun j => by
      unfold SSVCGMechanism.hybridGame; dsimp only
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hadm
      · rw [Function.update_of_ne hji]; exact hfam.admissible (θ j) (hθ j)
    rw [KellyGame.isSocialOptimum_iff_kkt (by simp [M, SSVCGMechanism.hybridGame]) hhybrid_adm]
    fin_cases i
    · refine ⟨hd_feas, by simp [M, SSVCGMechanism.hybridGame], 1 / 2, by norm_num, ?_, ?_⟩
      · intro j; fin_cases j
        · change derivWithin (fun t => Real.log (1 + t)) (Ici 0) 1 ≤ 1 / 2
          rw [hderiv 1 zero_le_one]; norm_num
        · change derivWithin (fun t => (1 / 4 : ℝ) * Real.log (1 + t)) (Ici 0) 0 ≤ 1 / 2
          rw [hderiv_scaled (1 / 4) 0 le_rfl]; norm_num
      · intro j hj; fin_cases j
        · change derivWithin (fun t => Real.log (1 + t)) (Ici 0) 1 = 1 / 2
          rw [hderiv 1 zero_le_one]; norm_num
        · change (0 : ℝ) < 0 at hj; exact absurd hj (lt_irrefl 0)
    · refine ⟨hd_feas, by simp [M, SSVCGMechanism.hybridGame], 3 / 2, by norm_num, ?_, ?_⟩
      · intro j; fin_cases j
        · change derivWithin (fun t => (3 : ℝ) * Real.log (1 + t)) (Ici 0) 1 ≤ 3 / 2
          rw [hderiv_scaled 3 1 zero_le_one]; norm_num
        · change derivWithin (fun t => Real.log (1 + t)) (Ici 0) 0 ≤ 3 / 2
          rw [hderiv 0 le_rfl]; norm_num
      · intro j hj; fin_cases j
        · change derivWithin (fun t => (3 : ℝ) * Real.log (1 + t)) (Ici 0) 1 = 3 / 2
          rw [hderiv_scaled 3 1 zero_le_one]; norm_num
        · change (0 : ℝ) < 0 at hj; exact absurd hj (lt_irrefl 0)
  refine ⟨hne, halloc, ?_⟩
  rw [halloc]
  simp only [KellyGame.welfare, U, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Real.log_one]
  have h1 : Real.log (1 + 1 / 2) + Real.log (1 + 1 / 2) = Real.log (9 / 4) := by
    have hsq : Real.log ((3 / 2 : ℝ) ^ (2 : ℕ)) = 2 * Real.log (3 / 2) := by
      simpa only [Nat.cast_ofNat] using Real.log_pow (3 / 2 : ℝ) 2
    have hnum : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    have h94 : (3 / 2 : ℝ) ^ (2 : ℕ) = 9 / 4 := by norm_num
    rw [hnum, ← h94, hsq]
    ring
  rw [h1]
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h2]
  exact Real.log_lt_log (by norm_num) (by norm_num)

end BluffExample

end Cslib.GameTheory
