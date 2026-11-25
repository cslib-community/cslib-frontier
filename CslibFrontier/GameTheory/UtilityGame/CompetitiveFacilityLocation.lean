/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.UtilityGame.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Vetta's competitive facility location game

In the **competitive facility location game** ([Vetta2002]; [TardosWexler2007],
Section 19.4.1, pp. 502–503), `k` service providers `i : ι` choose facility locations `s i : S i`
to serve a finite set of clients `j : J`. Each client `j` has reservation value `value j` (`π_j`)
for service, and serving `j` from provider `i`'s location `a : S i` incurs connection cost
`serviceCost j i a` (`c_{j, s_i}`).

Under second-cheapest pricing ([TardosWexler2007], p. 503), a provider `i` serving client `j`
charges the lowest connection cost available from any competing provider `i' ≠ i`, capped at `j`'s
reservation value `value j` (`secondPrice`), earning profit
`max 0 (secondPrice j s i - serviceCost j i (s i))` from `j`. Social welfare (`socialWelfare`) sums
the realized client-plus-provider surplus `max_{x ∈ T} max(0, π_j - c_j(x))` across all clients `j`.
When `serviceCost j i a ≤ value j` (Section 19.4.1's without-loss-of-generality normalization) and
at least two providers are present, `secondPrice` equals `min_{i' ≠ i} c_{j, s_{i'}}`
(`secondPrice_eq_inf'`) and `socialWelfare` equals `∑ j, (π_j - min_i c_{j, s_i})`
(`socialWelfare_eq_sum_sub_inf'`).

We prove all numbered facility-location results and facility-cost extensions of Section 19.4:

1. **Monotone basic utility game ([TardosWexler2007], Theorem 19.18, p. 505):** `toUtilityGame` is a
   basic utility game (`isBasic_toUtilityGame`, hence `isValid_toUtilityGame`) with monotone social
   welfare (`monotone_socialWelfare`) and `socialWelfare ∅ = 0`.
2. **Potential game and price of stability `1` ([TardosWexler2007], Theorem 19.16 and
   Corollary 19.17, pp. 503–504):** `-socialWelfare ∘ profileSet` is an exact potential of
   `toCostGame` (`isExactPotential`), so finite instances have pure Nash equilibria
   (`exists_isPureNash`), every welfare-maximizing profile is stable
   (`isPureNash_of_forall_socialWelfare_le`, giving `PoS = 1`), and better/best-response dynamics
   always converge (`hasFIP`, `exists_reflTransGen_isPureNash`), though suboptimal equilibria exist
   (`exists_competitiveFacilityLocation_poa_eq_two` attains `PoA = 2` on `2` providers and `2`
   clients).
3. **Price of anarchy `2` and `O(n log(1 / ε))` random best-response convergence:** immediate for
   pure Nash, mixed Nash, and coarse correlated equilibria
   (`socialWelfare_le_two_mul_of_isPureNash`, `socialWelfare_le_two_mul_expected_of_isMixedNash`)
   and random best-response trajectories (`mul_socialWelfare_le_expectedWalkValue`) by instantiating
   `Basic.lean`.
4. **Facility opening costs ([TardosWexler2007], Section 19.5.3, p. 511 and Exercise 19.17,
   p. 515):** subtracting installation costs `openingCost i a` (`withOpeningCost`) preserves
   `IsBasic` (hence exact potential and pure-equilibrium existence) while breaking monotonicity;
   every pure Nash equilibrium `s` still satisfies `V_f(o) ≤ 2 * V_f(s) + ∑ i, f(i, s i)`
   (`netWelfare_le_two_mul_add_openingCost_of_isPureNash`, Exercise 19.17(b)), whereas no constant
   multiplicative price-of-anarchy bound holds (`exists_withOpeningCost_poa_gt`, Exercise 19.17(a)).

## Main definitions

* `Cslib.GameTheory.UtilityGame.CompetitiveFacilityLocation`: competitive facility location game
  data (`value`, `serviceCost`).
* `CompetitiveFacilityLocation.secondPrice`, `CompetitiveFacilityLocation.clientProfit`,
  `CompetitiveFacilityLocation.profit`, `CompetitiveFacilityLocation.clientSurplus`,
  `CompetitiveFacilityLocation.socialWelfare`: second-cheapest pricing, provider profits, and set
  social welfare.
* `CompetitiveFacilityLocation.toUtilityGame`, `CompetitiveFacilityLocation.toCostGame`:
  embeddings as a `UtilityGame` and `CostGame`.
* `CompetitiveFacilityLocation.withOpeningCost`: facility-opening-cost extension
  ([TardosWexler2007], Exercise 19.17).

## Main results

* `CompetitiveFacilityLocation.secondPrice_eq_inf'`,
  `CompetitiveFacilityLocation.socialWelfare_eq_sum_sub_inf'`: exact agreement with Section 19.4.1's
  `min_{i' ≠ i} c_{j, s_{i'}}` and `∑ j, (π_j - min_i c_{j, s_i})` formulas when `c ≤ π`.
* `CompetitiveFacilityLocation.isBasic_toUtilityGame`,
  `CompetitiveFacilityLocation.monotone_socialWelfare` ([TardosWexler2007], Theorem 19.18):
  competitive facility location is a monotone basic utility game.
* `CompetitiveFacilityLocation.isExactPotential` ([TardosWexler2007], Theorem 19.16): social welfare
  is an exact potential.
* `CompetitiveFacilityLocation.exists_isPureNash`,
  `CompetitiveFacilityLocation.isPureNash_of_forall_socialWelfare_le`,
  `CompetitiveFacilityLocation.hasFIP`,
  `CompetitiveFacilityLocation.exists_reflTransGen_isPureNash` ([TardosWexler2007],
  Corollary 19.17): pure-equilibrium existence, `PoS = 1`, and convergence of improvement dynamics.
* `CompetitiveFacilityLocation.socialWelfare_le_two_mul_of_isPureNash`,
  `CompetitiveFacilityLocation.exists_competitiveFacilityLocation_poa_eq_two`: tight pure `PoA = 2`
  (and mixed/coarse-correlated extensions).
* `CompetitiveFacilityLocation.isBasic_withOpeningCost`,
  `CompetitiveFacilityLocation.netWelfare_le_two_mul_add_openingCost_of_isPureNash`,
  `CompetitiveFacilityLocation.exists_withOpeningCost_poa_gt` ([TardosWexler2007], Exercise 19.17):
  facility opening costs preserve `IsBasic`, satisfy `V_f(o) ≤ 2 * V_f(s) + F`, and admit unbounded
  price of anarchy.

## References

* [TardosWexler2007]
* [Vetta2002]
-/

public section

namespace Cslib.GameTheory.UtilityGame

open Cslib.Algorithms.Lean
open Finset Function

/-! ## Submodularity and min-max duality for `Finset.fold max` -/

private theorem monotone_fold_max {α : Type*} (b : ℝ) (g : α → ℝ) :
    Monotone fun T : Finset α => T.fold max b g := by
  intro A B hAB
  rw [Finset.fold_max_le]
  exact ⟨(Finset.le_fold_max b).2 (Or.inl le_rfl),
    fun x hx => (Finset.le_fold_max (g x)).2 (Or.inr ⟨x, hAB hx, le_rfl⟩)⟩

private theorem fold_max_union {α : Type*} [DecidableEq α] (b : ℝ) (g : α → ℝ) (A B : Finset α) :
    (A ∪ B).fold max b g = max (A.fold max b g) (B.fold max b g) := by
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨le_max_of_le_left ((Finset.le_fold_max b).2 (Or.inl le_rfl)), fun x hx => ?_⟩
    rcases Finset.mem_union.mp hx with hA | hB
    · exact le_max_of_le_left ((Finset.le_fold_max (g x)).2 (Or.inr ⟨x, hA, le_rfl⟩))
    · exact le_max_of_le_right ((Finset.le_fold_max (g x)).2 (Or.inr ⟨x, hB, le_rfl⟩))
  · exact max_le (monotone_fold_max b g Finset.subset_union_left)
      (monotone_fold_max b g Finset.subset_union_right)

private theorem isSubmodular_fold_max {α : Type*} [DecidableEq α] (b : ℝ) (g : α → ℝ) :
    Submodular.IsSubmodular fun T : Finset α => T.fold max b g := by
  intro A B
  have hU := fold_max_union b g A B
  have hI : (A ∩ B).fold max b g ≤ min (A.fold max b g) (B.fold max b g) :=
    le_min (monotone_fold_max b g Finset.inter_subset_left)
      (monotone_fold_max b g Finset.inter_subset_right)
  have hsum := max_add_min (A.fold max b g) (B.fold max b g)
  linarith

private theorem fold_max_sub_eq_sub_fold_min {α : Type*} (v : ℝ) (c : α → ℝ) (u : Finset α) :
    u.fold max 0 (fun x => v - c x) = v - u.fold min v c := by
  induction u using Finset.cons_induction with
  | empty =>
      simp only [Finset.fold_empty, sub_self]
  | cons x u' hx ih =>
      rw [Finset.fold_cons hx, Finset.fold_cons hx, ih]
      rcases le_total (c x) (u'.fold min v c) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
      · rw [min_eq_right h, max_eq_right (by linarith)]

/-! ## Competitive facility location model -/

/-- A **competitive facility location game** ([Vetta2002]; [TardosWexler2007],
Section 19.4.1, pp. 502–503): service providers `i : ι` choose facility locations in `S i` to serve
clients `j : J` with reservation values `value j` (`π_j`) and connection costs
`serviceCost j i a` (`c_{j, s_i}`). -/
structure CompetitiveFacilityLocation (ι : Type*) (S : ι → Type*) (J : Type*) where
  /-- Reservation value `π_j` of client `j` for receiving service. -/
  value : J → ℝ
  /-- Connection cost `c_{j, s_i}` for provider `i` at location `a : S i` to serve client `j`. -/
  serviceCost : J → ∀ i, S i → ℝ

namespace CompetitiveFacilityLocation

section Model

variable {ι : Type*} {S : ι → Type*} {J : Type*}
  (G : CompetitiveFacilityLocation ι S J)

/-- Second-cheapest connection price `p_{ij}(s)` available to client `j` outside provider `i`,
capped at client `j`'s reservation value `value j` ([TardosWexler2007], Section 19.4.1, p. 503). -/
def secondPrice [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι) : ℝ :=
  (Finset.univ.erase i).fold min (G.value j) fun i' => G.serviceCost j i' (s i')

theorem secondPrice_def [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι) :
    G.secondPrice j s i =
      (Finset.univ.erase i).fold min (G.value j) fun i' => G.serviceCost j i' (s i') := by
  rfl

@[simp]
theorem secondPrice_update_self [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι)
    (a : S i) :
    G.secondPrice j (Function.update s i a) i = G.secondPrice j s i := by
  unfold secondPrice
  refine Finset.fold_congr fun i' hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

private theorem fold_min_eq_inf' {α : Type*} {s : Finset α} (hne : s.Nonempty) (b : ℝ)
    (g : α → ℝ) (hle : ∀ x ∈ s, g x ≤ b) : s.fold min b g = s.inf' hne g := by
  let ⟨x₀, hx₀⟩ := hne
  exact le_antisymm
    (Finset.le_inf' hne _ fun x hx => (Finset.fold_min_le (g x)).2 (.inr ⟨x, hx, le_rfl⟩))
    ((Finset.le_fold_min _).2 ⟨(Finset.inf'_le _ hx₀).trans (hle x₀ hx₀),
      fun _ hx => Finset.inf'_le _ hx⟩)

/-- Under Section 19.4.1's normalization `serviceCost j i' a ≤ value j` and at least one competing
provider `i' ≠ i`, `secondPrice j s i` is literally `min_{i' ≠ i} c_{j, s_{i'}}`
([TardosWexler2007], p. 503). -/
theorem secondPrice_eq_inf' [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι)
    (hne : (Finset.univ.erase i).Nonempty)
    (hle : ∀ i' (a : S i'), G.serviceCost j i' a ≤ G.value j) :
    G.secondPrice j s i =
      (Finset.univ.erase i).inf' hne fun i' => G.serviceCost j i' (s i') :=
  fold_min_eq_inf' hne _ _ fun i' _ => hle i' (s i')

/-- Profit earned by provider `i` from client `j` at profile `s`: `max 0 (p_{ij}(s) - c_{j, s_i})`.
If `i` is the unique lowest-cost provider (with `c_{j, s_i} < p_{ij}(s)`), `i` serves `j` at price
`p_{ij}(s)`; if tied (`c_{j, s_i} = p_{ij}(s)`) or undercut (`c_{j, s_i} > p_{ij}(s)`), `i` earns
zero regardless of tie-breaking. -/
def clientProfit [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι) : ℝ :=
  max 0 (G.secondPrice j s i - G.serviceCost j i (s i))

theorem clientProfit_def [Fintype ι] [DecidableEq ι] (j : J) (s : ∀ i, S i) (i : ι) :
    G.clientProfit j s i = max 0 (G.secondPrice j s i - G.serviceCost j i (s i)) := by
  rfl

/-- Total profit `α_i(s)` of provider `i` across all clients `j : J`. -/
def profit [Fintype ι] [DecidableEq ι] [Fintype J] (i : ι) (s : ∀ k, S k) : ℝ :=
  ∑ j : J, G.clientProfit j s i

theorem profit_def [Fintype ι] [DecidableEq ι] [Fintype J] (i : ι) (s : ∀ k, S k) :
    G.profit i s = ∑ j : J, G.clientProfit j s i := by
  rfl

/-- Social surplus generated for client `j` by a finite set `T` of opened `(provider, location)`
pairs: `max(0, max_{x ∈ T} (π_j - c_j(x)))`. -/
def clientSurplus (j : J) (T : Finset (Σ i, S i)) : ℝ :=
  T.fold max 0 fun x => G.value j - G.serviceCost j x.1 x.2

theorem clientSurplus_def (j : J) (T : Finset (Σ i, S i)) :
    G.clientSurplus j T = T.fold max 0 fun x => G.value j - G.serviceCost j x.1 x.2 := by
  rfl

@[simp]
theorem clientSurplus_empty (j : J) : G.clientSurplus j ∅ = 0 := by
  simp only [clientSurplus, Finset.fold_empty]

@[simp]
theorem clientSurplus_singleton (j : J) (x : Σ i, S i) :
    G.clientSurplus j {x} = max 0 (G.value j - G.serviceCost j x.1 x.2) := by
  rw [clientSurplus, Finset.fold_singleton, max_comm]

/-- Social welfare `V(T)` of a finite set `T` of opened `(provider, location)` pairs
([TardosWexler2007], Section 19.4.3, p. 505). -/
def socialWelfare [Fintype J] (T : Finset (Σ i, S i)) : ℝ :=
  ∑ j : J, G.clientSurplus j T

theorem socialWelfare_def [Fintype J] (T : Finset (Σ i, S i)) :
    G.socialWelfare T = ∑ j : J, G.clientSurplus j T := by
  rfl

@[simp]
theorem socialWelfare_empty [Fintype J] : G.socialWelfare ∅ = 0 := by
  simp only [socialWelfare, clientSurplus_empty, Finset.sum_const_zero]

/-- Under Section 19.4.1's normalization `serviceCost j i a ≤ value j` and `[Nonempty ι]`, the
social welfare of profile `s` equals `∑ j, (π_j - min_i c_{j, s_i})` ([TardosWexler2007], p. 505).
-/
theorem socialWelfare_eq_sum_sub_inf' [Fintype ι] [Nonempty ι] [Fintype J] (s : ∀ i, S i)
    (hle : ∀ j i (a : S i), G.serviceCost j i a ≤ G.value j) :
    G.socialWelfare (profileSet s) =
      ∑ j : J,
        (G.value j - Finset.univ.inf' Finset.univ_nonempty fun i => G.serviceCost j i (s i)) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [clientSurplus, fold_profileSet, fold_max_sub_eq_sub_fold_min,
    fold_min_eq_inf' Finset.univ_nonempty _ _ fun i _ => hle j i (s i)]

/-- Embedding of the competitive facility location game as a `UtilityGame` ([TardosWexler2007],
Section 19.4.3, p. 505). -/
def toUtilityGame [Fintype ι] [DecidableEq ι] [Fintype J] : UtilityGame ι S where
  socialValue := G.socialWelfare
  utility := G.profit

@[simp]
theorem toUtilityGame_socialValue [Fintype ι] [DecidableEq ι] [Fintype J]
    (T : Finset (Σ i, S i)) :
    G.toUtilityGame.socialValue T = G.socialWelfare T := by
  rfl

@[simp]
theorem toUtilityGame_profileValue [Fintype ι] [DecidableEq ι] [Fintype J] (s : ∀ i, S i) :
    G.toUtilityGame.profileValue s = G.socialWelfare (profileSet s) := by
  rw [profileValue_def, toUtilityGame_socialValue]

@[simp]
theorem toUtilityGame_utility [Fintype ι] [DecidableEq ι] [Fintype J] (i : ι) (s : ∀ k, S k) :
    G.toUtilityGame.utility i s = G.profit i s := by
  rfl

/-- Strategic game in cost-minimization form (`cost = -profit`) associated to `G`. -/
def toCostGame [Fintype ι] [DecidableEq ι] [Fintype J] : CostGame ι S :=
  G.toUtilityGame.toCostGame

theorem toCostGame_eq [Fintype ι] [DecidableEq ι] [Fintype J] :
    G.toCostGame = G.toUtilityGame.toCostGame := by
  rfl

@[simp]
theorem toCostGame_cost [Fintype ι] [DecidableEq ι] [Fintype J] (i : ι) (s : ∀ k, S k) :
    G.toCostGame.cost i s = -G.profit i s := by
  rw [toCostGame_eq, UtilityGame.toCostGame_cost, toUtilityGame_utility]

end Model

/-! ## Theorems 19.16, 19.17, 19.18, 19.19, and 19.20 for competitive facility location -/

section MainResults

variable {ι : Type*} {S : ι → Type*} {J : Type*}
  (G : CompetitiveFacilityLocation ι S J)

/-- Client-by-client exact marginal contribution identity: provider `i`'s profit from client `j`
equals `j`'s surplus loss when `i` drops out ([TardosWexler2007], proof of Theorem 19.16, p. 504).
-/
private theorem clientProfit_eq_clientSurplus_sub [Fintype ι] [DecidableEq ι] (j : J)
    (s : ∀ i, S i) (i : ι) :
    G.clientProfit j s i =
      G.clientSurplus j (profileSet s) - G.clientSurplus j (profileWithout s i) := by
  unfold clientProfit secondPrice clientSurplus
  rw [fold_profileSet, fold_profileWithout, fold_max_sub_eq_sub_fold_min,
    fold_max_sub_eq_sub_fold_min]
  dsimp only
  have hfold : (Finset.univ.fold min (G.value j) fun i' => G.serviceCost j i' (s i')) =
      min (G.serviceCost j i (s i))
        ((Finset.univ.erase i).fold min (G.value j) fun i' => G.serviceCost j i' (s i')) := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
    exact Finset.fold_insert (Finset.notMem_erase i Finset.univ)
  rw [hfold]
  let m := (Finset.univ.erase i).fold min (G.value j) fun i' => G.serviceCost j i' (s i')
  change max 0 (m - G.serviceCost j i (s i)) =
    (G.value j - min (G.serviceCost j i (s i)) m) - (G.value j - m)
  rcases le_total (G.serviceCost j i (s i)) m with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-- Client-by-client budget bound: across all providers `i`, total profit extracted from client `j`
never exceeds `j`'s social surplus (at most one lowest-cost provider earns positive profit). -/
private theorem sum_clientProfit_le_clientSurplus [Fintype ι] [DecidableEq ι] (j : J)
    (s : ∀ i, S i) :
    ∑ i : ι, G.clientProfit j s i ≤ G.clientSurplus j (profileSet s) := by
  by_cases hne : Nonempty ι
  · obtain ⟨i₀, _, hi₀⟩ :=
      Finset.exists_min_image Finset.univ (fun i => G.serviceCost j i (s i)) Finset.univ_nonempty
    have hzero : ∀ i ∈ Finset.univ.erase i₀, G.clientProfit j s i = 0 := by
      intro i hi
      have hne_i : i₀ ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hi).symm, Finset.mem_univ i₀⟩
      have hsec_le : G.secondPrice j s i ≤ G.serviceCost j i₀ (s i₀) :=
        (Finset.fold_min_le (G.serviceCost j i₀ (s i₀))).2 (Or.inr ⟨i₀, hne_i, le_rfl⟩)
      have hmin_le : G.serviceCost j i₀ (s i₀) ≤ G.serviceCost j i (s i) :=
        hi₀ i (Finset.mem_univ i)
      rw [clientProfit_def, max_eq_left (by linarith)]
    rw [← Finset.add_sum_erase Finset.univ (fun i => G.clientProfit j s i) (Finset.mem_univ i₀),
      Finset.sum_eq_zero hzero, add_zero, clientProfit_eq_clientSurplus_sub]
    have hnonneg : 0 ≤ G.clientSurplus j (profileWithout s i₀) := by
      unfold clientSurplus
      exact (Finset.le_fold_max 0).2 (Or.inl le_rfl)
    linarith
  · have hEmpty : IsEmpty ι := not_nonempty_iff.mp hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    unfold clientSurplus
    exact (Finset.le_fold_max 0).2 (Or.inl le_rfl)

/-- Social welfare in the competitive facility location game is monotone ([TardosWexler2007],
Theorem 19.18, p. 505). -/
theorem monotone_socialWelfare [Fintype J] : Monotone G.socialWelfare := by
  intro A B hAB
  exact Finset.sum_le_sum fun j _ => monotone_fold_max 0 _ hAB

/-- Monotonicity of `G.toUtilityGame.socialValue` for module-isolated callers of `UtilityGame`
theorems. -/
theorem monotone_toUtilityGame_socialValue [Fintype ι] [DecidableEq ι] [Fintype J] :
    Monotone G.toUtilityGame.socialValue := by
  intro A B hAB
  simpa only [toUtilityGame_socialValue] using G.monotone_socialWelfare hAB

/-- **Theorem 19.18** ([TardosWexler2007], p. 505; [Vetta2002]): the competitive
facility location game is a basic (and monotone, by `monotone_socialWelfare`) utility game. -/
theorem isBasic_toUtilityGame [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [Fintype J] :
    G.toUtilityGame.IsBasic where
  isSubmodular :=
    Submodular.isSubmodular_sum Finset.univ fun j _ => isSubmodular_fold_max 0 _
  sum_utility_le s := by
    simp only [toUtilityGame_utility, profit_def, toUtilityGame_profileValue, socialWelfare]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => G.sum_clientProfit_le_clientSurplus j s
  utility_eq_marginal i s := by
    simp only [toUtilityGame_utility, profit_def, toUtilityGame_profileValue,
      toUtilityGame_socialValue, socialWelfare, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => G.clientProfit_eq_clientSurplus_sub j s i

/-- The competitive facility location game satisfies Vetta's valid utility game conditions. -/
theorem isValid_toUtilityGame [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [Fintype J] :
    G.toUtilityGame.IsValid :=
  G.isBasic_toUtilityGame.isValid

/-- Payoff-form unilateral deviation identity ([TardosWexler2007], proof of Theorem 19.16, p. 504):
when provider `i` changes location to `a`, the change in `i`'s profit equals the change in social
welfare `V`. -/
theorem profit_sub_profit_eq [Fintype ι] [DecidableEq ι] [Fintype J] (s : ∀ i, S i) (i : ι)
    (a : S i) :
    G.profit i (Function.update s i a) - G.profit i s =
      G.socialWelfare (profileSet (Function.update s i a)) - G.socialWelfare (profileSet s) := by
  simpa only [toUtilityGame_utility, toUtilityGame_profileValue] using
    IsBasic.utility_sub_utility_eq (G := G.toUtilityGame) (fun k s' => by
      simp only [toUtilityGame_utility, profit_def, toUtilityGame_profileValue,
        toUtilityGame_socialValue, socialWelfare, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => G.clientProfit_eq_clientSurplus_sub j s' k) s i a

/-- **Theorem 19.16** ([TardosWexler2007], p. 503): the competitive facility location game is an
exact potential game with social welfare `V(s)` as potential (`-V(s)` for `toCostGame`). -/
theorem isExactPotential [Fintype ι] [DecidableEq ι] [Fintype J] :
    G.toCostGame.IsExactPotential (fun s => -G.socialWelfare (profileSet s)) := by
  intro s i a
  simp only [toCostGame_cost]
  have h := G.profit_sub_profit_eq s i a
  linarith

/-- **Corollary 19.17 (existence)** ([TardosWexler2007], p. 504): every finite nonempty competitive
facility location game admits a pure Nash equilibrium. -/
theorem exists_isPureNash [Fintype ι] [DecidableEq ι] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    [Fintype J] :
    ∃ s, G.toCostGame.IsPureNash s :=
  G.isExactPotential.isGeneralizedOrdinalPotential.exists_isPureNash

/-- **Corollary 19.17 (efficiency stability)** ([TardosWexler2007], p. 504): every socially
efficient outcome of the competitive facility location game is a pure Nash equilibrium. -/
theorem isPureNash_of_forall_socialWelfare_le [Fintype ι] [DecidableEq ι] [Fintype J]
    {s : ∀ i, S i}
    (hs : ∀ s', G.socialWelfare (profileSet s') ≤ G.socialWelfare (profileSet s)) :
    G.toCostGame.IsPureNash s :=
  G.isExactPotential.isGeneralizedOrdinalPotential.isPureNash_of_forall_le fun s' =>
    neg_le_neg (hs s')

/-- **Corollary 19.17 (price of stability `1`)** ([TardosWexler2007], p. 504): every finite
nonempty competitive facility location game has a pure Nash equilibrium maximizing social welfare.
-/
theorem exists_isPureNash_forall_socialWelfare_le [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] [Fintype J] :
    ∃ s, G.toCostGame.IsPureNash s ∧
      ∀ s', G.socialWelfare (profileSet s') ≤ G.socialWelfare (profileSet s) := by
  obtain ⟨s, hs⟩ := Finite.exists_max fun s' => G.socialWelfare (profileSet s')
  exact ⟨s, G.isPureNash_of_forall_socialWelfare_le hs, hs⟩

/-- **Corollary 19.17 (finite improvement property)** ([TardosWexler2007], p. 504): every finite
competitive facility location game has the finite improvement property (all better-response and
best-response improvement sequences terminate). -/
theorem hasFIP [Fintype ι] [DecidableEq ι] [∀ i, Finite (S i)] [Fintype J] :
    G.toCostGame.HasFIP :=
  G.isExactPotential.isGeneralizedOrdinalPotential.hasFIP

/-- **Corollary 19.17 (convergence of improvement dynamics)** ([TardosWexler2007], p. 504): from
any starting profile `s₀`, better-response dynamics reach a pure Nash equilibrium. -/
theorem exists_reflTransGen_isPureNash [Fintype ι] [DecidableEq ι] [∀ i, Finite (S i)]
    [Fintype J] (s₀ : ∀ i, S i) :
    ∃ t, Relation.ReflTransGen (flip G.toCostGame.Improves) s₀ t ∧ G.toCostGame.IsPureNash t :=
  G.hasFIP.exists_reflTransGen_isPureNash s₀

/-- **Price of Anarchy `≤ 2` for Competitive Facility Location** ([TardosWexler2007],
Theorems 19.18–19.19, p. 505; [Vetta2002]): every pure Nash equilibrium `s` achieves
at least half the social welfare of any profile `o`. -/
theorem socialWelfare_le_two_mul_of_isPureNash [Fintype ι] [DecidableEq ι] [Fintype J]
    {s : ∀ i, S i} (hs : G.toCostGame.IsPureNash s) (o : ∀ i, S i) :
    G.socialWelfare (profileSet o) ≤ 2 * G.socialWelfare (profileSet s) := by
  classical
  simpa only [toUtilityGame_profileValue] using
    G.isValid_toUtilityGame.profileValue_le_two_mul_of_isPureNash G.monotone_socialWelfare hs o

/-- **Mixed Nash Price of Anarchy `≤ 2` for Competitive Facility Location** ([Vetta2002];
[TardosWexler2007], Section 19.5.3, p. 511): every mixed Nash equilibrium `p` achieves expected
social welfare at least half of any pure profile `o`. -/
theorem socialWelfare_le_two_mul_expected_of_isMixedNash [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (S i)] [Fintype J] {p : ∀ i, S i → ℝ} (hp : G.toCostGame.IsMixedNash p)
    (o : ∀ i, S i) :
    G.socialWelfare (profileSet o) ≤
      2 * ∑ s, productWeight p s * G.socialWelfare (profileSet s) := by
  classical
  simpa only [toUtilityGame_profileValue] using
    G.isValid_toUtilityGame.profileValue_le_two_mul_expected_of_isMixedNash
      G.monotone_socialWelfare hp o

/-- **Random Best-Response Convergence for Competitive Facility Location** ([TardosWexler2007],
Theorems 19.18 and 19.20, pp. 505–506): after `t ≥ (n / 2) * log (1 / ε)` random best-response
steps from any profile `s₀`, expected social welfare is at least `(1 / 2 - ε)` times optimal. -/
theorem mul_socialWelfare_le_expectedWalkValue [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype J] {br : ∀ i, (∀ k, S k) → S i} (hbr : G.toUtilityGame.IsBestResponse br)
    {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : (Fintype.card ι : ℝ) / 2 * Real.log (1 / ε) ≤ t)
    (s₀ o : ∀ i, S i) :
    (1 / 2 - ε) * G.socialWelfare (profileSet o) ≤ G.toUtilityGame.expectedWalkValue br s₀ t := by
  classical
  simpa only [toUtilityGame_profileValue] using
    G.isBasic_toUtilityGame.mul_profileValue_le_expectedWalkValue G.monotone_socialWelfare
      (by simp only [toUtilityGame_socialValue, socialWelfare_empty, le_rfl]) hbr hε ht s₀ o

end MainResults

/-! ## Tightness `PoA = 2` on 2 providers and 2 clients -/

/-- Two-provider, two-client competitive facility location instance attaining exact `PoA = 2` (and
witnessing Corollary 19.17's claim that pure equilibria need not be socially optimal). -/
private def twoByTwoTight : CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) (Fin 2) where
  value _ := 1
  serviceCost j i b :=
    if j = 0 then
      if (i = 0 && !b) || (i = 1 && b) then 0 else 1
    else
      if i = 0 && b then 0 else 1

private theorem socialWelfare_twoByTwoTight (b₀ b₁ : Bool) :
    twoByTwoTight.socialWelfare (profileSet ![b₀, b₁]) =
      (if !b₀ || b₁ then 1 else 0) + (if b₀ then 1 else 0) := by
  unfold socialWelfare clientSurplus
  rw [Fin.sum_univ_two, fold_profileSet, fold_profileSet]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [huniv, Finset.fold_insert (by simp only [mem_singleton, h01, not_false_eq_true]),
    Finset.fold_singleton,
    Finset.fold_insert (by simp only [mem_singleton, h01, not_false_eq_true]),
    Finset.fold_singleton]
  cases b₀ <;> cases b₁ <;> norm_num [twoByTwoTight]

private theorem neg_le_neg_of_fin_two_bool_update (f : (Fin 2 → Bool) → ℝ)
    (h10 : f ![true, false] ≤ f ![false, false])
    (h01 : f ![false, true] ≤ f ![false, false])
    (i : Fin 2) (b : Bool) :
    -f ![false, false] ≤ -f (Function.update ![false, false] i b) := by
  rw [neg_le_neg_iff]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> cases b
  · convert le_rfl using 2; ext k; fin_cases k <;> rfl
  · convert h10 using 2; ext k; fin_cases k <;> rfl
  · convert le_rfl using 2; ext k; fin_cases k <;> rfl
  · convert h01 using 2; ext k; fin_cases k <;> rfl

/-- Exact tightness of `PoA ≤ 2` for competitive facility location: there is a 2-provider, 2-client
instance satisfying `0 ≤ c ≤ π` with a pure Nash equilibrium `s` of welfare `1` and an optimal
profile `o` of welfare `2 = 2 * V(s)`. -/
theorem exists_competitiveFacilityLocation_poa_eq_two :
    ∃ (G : CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) (Fin 2))
      (s o : Fin 2 → Bool),
      (∀ j i b, 0 ≤ G.serviceCost j i b ∧ G.serviceCost j i b ≤ G.value j) ∧
      G.toCostGame.IsPureNash s ∧
      0 < G.socialWelfare (profileSet s) ∧
      G.socialWelfare (profileSet o) = 2 * G.socialWelfare (profileSet s) := by
  refine ⟨twoByTwoTight, ![false, false], ![true, true],
    fun j i b => by fin_cases j <;> fin_cases i <;> cases b <;> norm_num [twoByTwoTight],
    twoByTwoTight.isExactPotential.isGeneralizedOrdinalPotential.isPureNash_of_forall_update_le
      (neg_le_neg_of_fin_two_bool_update (fun s => twoByTwoTight.socialWelfare (profileSet s))
        (by rw [socialWelfare_twoByTwoTight, socialWelfare_twoByTwoTight]; norm_num)
        (by rw [socialWelfare_twoByTwoTight, socialWelfare_twoByTwoTight]; norm_num)),
    by rw [socialWelfare_twoByTwoTight]; norm_num,
    by rw [socialWelfare_twoByTwoTight, socialWelfare_twoByTwoTight]; norm_num⟩

/-! ## Facility opening costs (Section 19.5.3 and Exercise 19.17) -/

section OpeningCosts

variable {ι : Type*} {S : ι → Type*} {J : Type*}
  (G : CompetitiveFacilityLocation ι S J)

/-- Competitive facility location with facility installation costs `openingCost i a` (`f(s_i)`) paid
by any provider `i` locating at `a` ([TardosWexler2007], Section 19.5.3, p. 511 and Exercise 19.17,
p. 515). -/
def withOpeningCost [Fintype ι] [DecidableEq ι] [Fintype J]
    (openingCost : ∀ i, S i → ℝ) : UtilityGame ι S where
  socialValue T := G.socialWelfare T - ∑ x ∈ T, openingCost x.1 x.2
  utility i s := G.profit i s - openingCost i (s i)

@[simp]
theorem withOpeningCost_socialValue [Fintype ι] [DecidableEq ι] [Fintype J]
    (openingCost : ∀ i, S i → ℝ) (T : Finset (Σ i, S i)) :
    (G.withOpeningCost openingCost).socialValue T =
      G.socialWelfare T - ∑ x ∈ T, openingCost x.1 x.2 := by
  rfl

@[simp]
theorem withOpeningCost_profileValue [Fintype ι] [DecidableEq ι] [Fintype J]
    (openingCost : ∀ i, S i → ℝ) (s : ∀ i, S i) :
    (G.withOpeningCost openingCost).profileValue s =
      G.socialWelfare (profileSet s) - ∑ i, openingCost i (s i) := by
  simp only [profileValue_def, withOpeningCost_socialValue, sum_profileSet]

@[simp]
theorem withOpeningCost_utility [Fintype ι] [DecidableEq ι] [Fintype J]
    (openingCost : ∀ i, S i → ℝ) (i : ι) (s : ∀ k, S k) :
    (G.withOpeningCost openingCost).utility i s = G.profit i s - openingCost i (s i) := by
  rfl

/-- Adding facility opening costs preserves `IsBasic` (hence `IsValid`, exact potential `-V_f`, and
pure-equilibrium existence), losing only monotonicity of `socialValue`. -/
theorem isBasic_withOpeningCost [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [Fintype J]
    (openingCost : ∀ i, S i → ℝ) :
    (G.withOpeningCost openingCost).IsBasic where
  isSubmodular := by
    convert G.isBasic_toUtilityGame.isSubmodular.add
      (Submodular.isSubmodular_modularSum fun x : Σ i, S i => -openingCost x.1 x.2) using 1
    ext T
    simp [Submodular.modularSum, Finset.sum_neg_distrib, sub_eq_add_neg]
  sum_utility_le s := by
    have h := G.isBasic_toUtilityGame.sum_utility_le s
    simp only [toUtilityGame_utility, toUtilityGame_profileValue] at h
    simp only [withOpeningCost_utility, withOpeningCost_profileValue, Finset.sum_sub_distrib]
    linarith
  utility_eq_marginal i s := by
    have h := G.isBasic_toUtilityGame.utility_eq_marginal i s
    simp only [toUtilityGame_utility, toUtilityGame_profileValue, toUtilityGame_socialValue] at h
    simp only [withOpeningCost_utility, withOpeningCost_profileValue, withOpeningCost_socialValue,
      sum_profileWithout]
    linarith [Finset.add_sum_erase Finset.univ (fun k => openingCost k (s k)) (Finset.mem_univ i)]

/-- **Exercise 19.17(b)** ([TardosWexler2007], p. 515): at any pure Nash equilibrium `s` of the
facility location game with opening costs `f`, the net social welfare of any profile `o` is at most
`2 * V_f(s) + F`, where `F = ∑ i, f(i, s i)` is the total facility opening cost paid at `s`. -/
theorem netWelfare_le_two_mul_add_openingCost_of_isPureNash [Fintype ι] [DecidableEq ι]
    [Fintype J] (openingCost : ∀ i, S i → ℝ) {s : ∀ i, S i}
    (hs : (G.withOpeningCost openingCost).toCostGame.IsPureNash s) (o : ∀ i, S i) :
    (G.withOpeningCost openingCost).profileValue o ≤
      2 * (G.withOpeningCost openingCost).profileValue s + ∑ i, openingCost i (s i) := by
  classical
  rw [isPureNash_toCostGame_iff] at hs
  have hdev :=
    G.isValid_toUtilityGame.profileValue_sub_le_sum_deviation G.monotone_socialWelfare s o
  simp only [toUtilityGame_profileValue, toUtilityGame_utility] at hdev
  have hbud := G.isValid_toUtilityGame.sum_utility_le s
  simp only [toUtilityGame_profileValue, toUtilityGame_utility] at hbud
  have hne : ∑ i, (G.profit i (Function.update s i (o i)) - openingCost i (o i)) ≤
      ∑ i, (G.profit i s - openingCost i (s i)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hs i (o i)
    simpa only [withOpeningCost_utility, Function.update_self] using hi
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hne
  simp only [withOpeningCost_profileValue]
  linarith

/-- Parametrized 2-provider, 1-client instance with opening costs witnessing unbounded price of
anarchy ([TardosWexler2007], Section 19.5.3, p. 511 and Exercise 19.17(a), p. 515). -/
private def openingCostTrapGame (M : ℝ) :
    CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) Unit where
  value _ := M
  serviceCost _ i b := if (i = 0 && !b) || (i = 1 && b) then 0 else M

private def openingCostTrapFee (M : ℝ) (i : Fin 2) (b : Bool) : ℝ :=
  if i = 0 && !b then M - 1 else 0

private theorem openingCostTrap_profileValue {M : ℝ} (hM : 1 ≤ M) (b₀ b₁ : Bool) :
    ((openingCostTrapGame M).withOpeningCost (openingCostTrapFee M)).profileValue ![b₀, b₁] =
      (if !b₀ || b₁ then M else 0) - (if !b₀ then M - 1 else 0) := by
  rw [withOpeningCost_profileValue, Fin.sum_univ_two]
  unfold socialWelfare clientSurplus
  rw [Fintype.sum_unique, fold_profileSet]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [huniv, Finset.fold_insert (by simp only [mem_singleton, h01, not_false_eq_true]),
    Finset.fold_singleton]
  cases b₀ <;> cases b₁ <;> norm_num [openingCostTrapGame, openingCostTrapFee]
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith)]; ring
  · linarith

/-- **Exercise 19.17(a)** ([TardosWexler2007], p. 515): when facilities have nonnegative opening
costs, no constant price-of-anarchy bound holds — for every `C : ℝ`, there is a 2-provider,
1-client competitive facility location instance (with `0 ≤ c ≤ π` and `0 ≤ f`) admitting a pure Nash
equilibrium `s` of positive net social welfare and a profile `o` with `C * V_f(s) < V_f(o)`. -/
theorem exists_withOpeningCost_poa_gt (C : ℝ) :
    ∃ (G : CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) Unit)
      (f : Fin 2 → Bool → ℝ) (s o : Fin 2 → Bool),
      (∀ j i b, 0 ≤ G.serviceCost j i b ∧ G.serviceCost j i b ≤ G.value j) ∧
      (∀ i b, 0 ≤ f i b) ∧
      (G.withOpeningCost f).toCostGame.IsPureNash s ∧
      0 < (G.withOpeningCost f).profileValue s ∧
      C * (G.withOpeningCost f).profileValue s < (G.withOpeningCost f).profileValue o := by
  let M := max 2 (C + 1)
  have hM1 : 1 ≤ M := le_trans (by norm_num) (le_max_left 2 (C + 1))
  have hMC : C < M := lt_of_lt_of_le (by linarith) (le_max_right 2 (C + 1))
  refine ⟨openingCostTrapGame M, openingCostTrapFee M, ![false, false], ![true, true],
    fun _ _ _ => by dsimp only [openingCostTrapGame]; split_ifs <;> constructor <;> linarith,
    fun _ _ => by dsimp only [openingCostTrapFee]; split_ifs <;> linarith, ?_,
    by rw [openingCostTrap_profileValue hM1]; norm_num,
    by rw [openingCostTrap_profileValue hM1, openingCostTrap_profileValue hM1]; norm_num; linarith⟩
  have hpot :=
    ((openingCostTrapGame M).isBasic_withOpeningCost (openingCostTrapFee M)).isExactPotential
  exact hpot.isGeneralizedOrdinalPotential.isPureNash_of_forall_update_le
    (neg_le_neg_of_fin_two_bool_update
      ((openingCostTrapGame M).withOpeningCost (openingCostTrapFee M)).profileValue
      (by
        rw [openingCostTrap_profileValue hM1, openingCostTrap_profileValue hM1]
        norm_num)
      (by
        rw [openingCostTrap_profileValue hM1, openingCostTrap_profileValue hM1]
        norm_num))

end OpeningCosts

end CompetitiveFacilityLocation

end Cslib.GameTheory.UtilityGame
