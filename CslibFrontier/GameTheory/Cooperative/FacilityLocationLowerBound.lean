/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Cooperative.FacilityLocationCostSharing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tight `1 / 3` lower bound for cross-monotonic facility location cost sharing

This module formalizes **Section 15.5** of [JainMahdian2007] (pp. 400–402; Immorlica, Mahdian, and
Mirrokni 2005): the **`1 / 3` budget-balance factor of `FLCostShare` (Theorem 15.21) is tight** for
every cross-monotonic cost-sharing scheme on metric facility location games.

1. **`flTightInstance m k` (**Lemma 15.22**, Figure 15.5a, pp. 400–401):** a metric instance
   with `m` facilities of opening cost `3`, `m` primary agents `a₁, …, aₘ` (`inl i` connected at
   distance `1` only to `fᵢ`), and `k` shared agents `a'₁, …, a'ₖ` (`inr r` connected at distance
   `1` to every `fᵢ`). We prove:
   * `flTightInstance_isMetric`: exact shortest-path metric (`{1, 2, 3}` bipartite distance).
   * `flTightInstance_cost_univ`: optimal coalition cost is **`3 * m + k + 1`** (`1 ≤ m`).
   * `flTightInstance_flCostShareScheme_sum`: for `1 ≤ m` and `1 ≤ k`, `FLCostShare` assigns
     every agent cost share `1 + 3 / (k + 1)`, recovering total `(m + k) * (1 + 3 / (k + 1))`
     (ratio tending to `1 / 3` as `k → ∞` and `m / k → ∞`).

2. **`flHardInstance k m` (**Theorem 15.23**, Figure 15.5b, pp. 401–402):** `k` groups
   `A₁, …, Aₖ` of `m` agents each (`Fin k × Fin m`), and `m^k` facilities `f_b` indexed by cross-
   sections `b : Fin k → Fin m`, each of opening cost `3`, with connection cost `1` to `(i, b i)`
   and `3` otherwise. By an elementary double-counting proof over `(i, b) : Fin k × (Fin k → Fin m)`
   (replacing probabilistic averaging with `Finset.sum`), we prove:
   * `flHardInstance_isMetric`: metric instance via `{1, 2, 3}` bipartite shortest-path distance.
   * Exact slice cost `c(Aᵢ ∪ T_{i,b}) = 3 * m + k` for every `(i, b)`.
   * `flHardInstance_budgetBalance_le`: for **every** cross-monotonic `γ`-budget-balanced scheme
     `ξ` (even without assuming nonnegativity),
     `γ * (3 * m + k) ≤ m * ((k + 3) / k) + (k + 2)` (matching inequality `(15.6)`, p. 402).
   * `not_exists_crossMonotone_isBudgetBalanced`: for every **`γ > 1 / 3`**, there
     exist finite `k, m ≥ 1` such that **no** cross-monotonic `γ`-budget-balanced cost-sharing
     scheme exists on `flHardInstance k m`.

## Source verification note

In [JainMahdian2007], p. 401 (proof of Theorem 15.23), the randomly sampled subset `T` contains
`k - 1` agents (`{a_j : j ≠ i}`), whereas Lemma 15.22 uses `k` shared agents `a'₁, …, a'ₖ`.
Hence `flTightInstance m k` has optimal cost `3 * m + k + 1`, while each sample slice
`S(i, b) = Aᵢ ∪ T(i, b)` in Theorem 15.23 has optimal cost `3 * m + k` (`= 3 * m + (k - 1) + 1`).
Both formulas yield `3 * m + o(m)` with exact inequality `(15.6)` unchanged (`c(T) ≤ k + 2`).

## Main definitions

* `Cslib.GameTheory.FacilityLocationInstance.flTightInstance`: `m + k`-agent bipartite metric
  instance of Lemma 15.22 ([JainMahdian2007], Figure 15.5a).
* `Cslib.GameTheory.FacilityLocationInstance.flHardInstance`: `k × m`-agent metric instance of
  Theorem 15.23 ([JainMahdian2007], Figure 15.5b).

## Main results

* `Cslib.GameTheory.FacilityLocationInstance.flTightInstance_cost_univ`: **Lemma 15.22**.
* `Cslib.GameTheory.FacilityLocationInstance.flTightInstance_flCostShareScheme_sum`: tightness
  of `FLCostShare` on `flTightInstance`.
* `Cslib.GameTheory.FacilityLocationInstance.flHardInstance_budgetBalance_le`: exact finite
  double-counting bound, **inequality `(15.6)`** ([JainMahdian2007], p. 402).
* `Cslib.GameTheory.FacilityLocationInstance.not_exists_crossMonotone_isBudgetBalanced`:
  **Theorem 15.23** ([JainMahdian2007], pp. 401–402).

## References

* [JainMahdian2007]
-/

public section

namespace Cslib.GameTheory

namespace FacilityLocationInstance

/-! ### Shared `{1, 2, 3}` bipartite shortest-path pseudometric -/

/-- Any facility location instance whose connection costs are `1` on a bipartite adjacency relation
`adj : F → A → Prop` and `3` elsewhere is metric (shortest-path `{1, 2, 3}` metric on `A ⊕ F`). -/
private theorem isMetric_of_bipartite {A F : Type*} (I : FacilityLocationInstance A F)
    (adj : F → A → Prop)
    (hconn : ∀ i j, I.connCost i j = open scoped Classical in if adj i j then 1 else 3) :
    I.IsMetric := by
  classical
  let d : A ⊕ F → A ⊕ F → ℝ
    | .inl a₁, .inl a₂ => if a₁ = a₂ then 0 else 2
    | .inr f₁, .inr f₂ => if f₁ = f₂ then 0 else 2
    | .inl a, .inr f => if adj f a then 1 else 3
    | .inr f, .inl a => if adj f a then 1 else 3
  refine ⟨{
    dist := d
    dist_self := fun x => by cases x <;> simp [d]
    dist_comm := fun x y => by cases x <;> cases y <;> simp only [d, eq_comm]
    dist_triangle := fun x y z => by
      cases x <;> cases y <;> cases z <;> dsimp only [d] <;> split_ifs <;>
        first | (norm_num; done) | (subst_vars; contradiction)
  }, hconn⟩

private theorem sum_ite_one_three {m : ℕ} (S : Finset (Fin m)) :
    ∑ j : Fin m, (if j ∈ S then (1 : ℝ) else 3) = 3 * (m : ℝ) - 2 * (S.card : ℝ) := by
  have hrew : ∀ j : Fin m, (if j ∈ S then (1 : ℝ) else 3) =
      3 - (if j ∈ S then (2 : ℝ) else 0) := fun j => by split_ifs <;> norm_num
  simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ### Lemma 15.22: the `FLCostShare` tightness instance -/

/-- **Lemma 15.22 instance** ([JainMahdian2007], Figure 15.5a, pp. 400–401): `m` facilities of
opening cost `3`, `m` primary agents `inl j` (`j : Fin m`, unit distance only to `f_j`), and `k`
shared agents `inr r` (`r : Fin k`, unit distance to every facility). -/
@[expose] def flTightInstance (m k : ℕ) :
    FacilityLocationInstance (Fin m ⊕ Fin k) (Fin m) where
  openCost _ := 3
  connCost i
    | .inl j => if i = j then 1 else 3
    | .inr _ => 1
  openCost_nonneg _ := by norm_num
  connCost_nonneg i j := by
    cases j with
    | inl j => dsimp only; split_ifs <;> norm_num
    | inr _ => norm_num

theorem flTightInstance_isMetric (m k : ℕ) : (flTightInstance m k).IsMetric := by
  refine isMetric_of_bipartite (flTightInstance m k)
    (fun i a => match a with | .inl j => i = j | .inr _ => True) fun i a => ?_
  classical
  cases a with
  | inl j => dsimp only [flTightInstance]; by_cases h : i = j <;> simp [h]
  | inr r => simp [flTightInstance]

private theorem flTightInstance_planCost {m k : ℕ} (F' : Finset (Fin m)) (hF' : F'.Nonempty) :
    (flTightInstance m k).planCost Finset.univ F' hF' =
      3 * (m : ℝ) + (k : ℝ) + (F'.card : ℝ) := by
  have hconn_l (j : Fin m) : F'.inf' hF' (fun i => (flTightInstance m k).connCost i (.inl j)) =
      if j ∈ F' then 1 else 3 := by
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun i hi => ?_)
    · obtain ⟨i₀, hi₀⟩ := hF'
      split_ifs with hj
      · exact (Finset.inf'_le _ hj).trans (by simp [flTightInstance])
      · have hne : i₀ ≠ j := fun h => hj (h ▸ hi₀)
        exact (Finset.inf'_le _ hi₀).trans (by simp [flTightInstance, hne])
    · dsimp only [flTightInstance]
      split_ifs <;> first | (subst_vars; contradiction) | norm_num
  have hconn_r (r : Fin k) :
      F'.inf' hF' (fun i => (flTightInstance m k).connCost i (.inr r)) = 1 := by
    simp [flTightInstance]
  rw [planCost_eq, Fintype.sum_sum_type]
  simp_rw [hconn_l, hconn_r, sum_ite_one_three]
  simp only [flTightInstance, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

/-- **Lemma 15.22** ([JainMahdian2007], pp. 400–401): for every `m ≥ 1` and `k ≥ 0`, the exact
optimal cost of `flTightInstance m k` is `3 * m + k + 1` (achieved by opening a single
facility). -/
theorem flTightInstance_cost_univ (m k : ℕ) [NeZero m] :
    (flTightInstance m k).toCostSharingGame.cost Finset.univ =
      3 * (m : ℝ) + (k : ℝ) + 1 := by
  have hU : (Finset.univ : Finset (Fin m ⊕ Fin k)).Nonempty := ⟨.inl 0, Finset.mem_univ _⟩
  refine le_antisymm ?_ ?_
  · simpa [flTightInstance_planCost] using
      (flTightInstance m k).toCostSharingGame_cost_le_planCost Finset.univ {0}
        (Finset.singleton_nonempty 0)
  · refine (flTightInstance m k).le_toCostSharingGame_cost_of_nonempty hU fun F' hF' => ?_
    rw [flTightInstance_planCost F' hF']
    exact_mod_cast Nat.add_le_add_left hF'.card_pos (3 * m + k)

/-- On `flTightInstance m k` (`m ≥ 1, k ≥ 1`), every facility `i` opens in `FLCostShare` at the
same time `1 + 3 / (k + 1)`, so every agent pays `1 + 3 / (k + 1)` and total recovered cost is
`(m + k) * (1 + 3 / (k + 1))` (ratio `(1 / 3) + o(1)` against `3 * m + k + 1`). -/
theorem flTightInstance_flCostShareScheme_sum (m k : ℕ) [NeZero m] (hk : 1 ≤ k) :
    ∑ j : Fin m ⊕ Fin k, (flTightInstance m k).flCostShareScheme.share Finset.univ j =
      ((m : ℝ) + (k : ℝ)) * (1 + 3 / ((k : ℝ) + 1)) := by
  set t : ℝ := 1 + 3 / ((k : ℝ) + 1)
  have hk_ge : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have ht_gt : 1 < t := by dsimp only [t]; linarith [div_pos (by norm_num : (0 : ℝ) < 3) hk1_pos]
  have hdiv : 3 / ((k : ℝ) + 1) ≤ 2 := (div_le_iff₀ hk1_pos).2 (by linarith)
  have ht_le3 : t ≤ 3 := by dsimp only [t]; linarith
  have hopen_eq (i : Fin m) : (flTightInstance m k).openTime i Finset.univ = t := by
    refine ((flTightInstance m k).eq_openTime_of_sum_max_eq
      ⟨.inl 0, Finset.mem_univ _⟩ (by norm_num [flTightInstance]) ?_).symm
    rw [Fintype.sum_sum_type]
    have hl : ∑ j : Fin m, max 0 (t - (flTightInstance m k).connCost i (.inl j)) = t - 1 := by
      rw [Fintype.sum_eq_single i fun j hj => by simp [flTightInstance, Ne.symm hj]; linarith]
      simp [flTightInstance, ht_gt.le]
    have hr : ∑ r : Fin k, max 0 (t - (flTightInstance m k).connCost i (.inr r)) =
        (k : ℝ) * (t - 1) := by
      simp [flTightInstance, ht_gt.le]; ring
    rw [hl, hr]
    change (t - 1) + (k : ℝ) * (t - 1) = 3
    dsimp only [t]
    field_simp [hk1_pos.ne']
    ring
  have hshare (j : Fin m ⊕ Fin k) :
      (flTightInstance m k).flCostShareScheme.share Finset.univ j = t := by
    rw [(flTightInstance m k).flCostShareScheme_share_of_mem (Finset.mem_univ j)]
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun i _ => (hopen_eq i) ▸ le_max_left _ _)
    refine (Finset.inf'_le _ (Finset.mem_univ (j.elim id fun _ => 0))).trans ?_
    rw [hopen_eq]
    cases j <;> simp [flTightInstance, ht_gt.le]
  simp_rw [hshare, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add]

/-! ### Theorem 15.23: tight `1 / 3` upper bound for ALL cross-monotonic schemes -/

/-- **Theorem 15.23 metric instance** ([JainMahdian2007], Figure 15.5b, pp. 401–402): `k` groups
`A₁, …, Aₖ` of `m` agents each (`Fin k × Fin m`), and `m^k` facilities `f_b` indexed by
cross-sections `b : Fin k → Fin m`, each of opening cost `3`, with connection cost `1` to
`(i, b i)` and `3` otherwise. -/
@[expose] def flHardInstance (k m : ℕ) :
    FacilityLocationInstance (Fin k × Fin m) (Fin k → Fin m) where
  openCost _ := 3
  connCost b a := if b a.1 = a.2 then 1 else 3
  openCost_nonneg _ := by norm_num
  connCost_nonneg _ _ := by split_ifs <;> norm_num

theorem flHardInstance_isMetric (k m : ℕ) : (flHardInstance k m).IsMetric := by
  refine isMetric_of_bipartite (flHardInstance k m) (fun b a => b a.1 = a.2) fun _ _ => ?_
  dsimp only [flHardInstance]
  split_ifs <;> rfl

/-- Full cross-section `B(b) = {(j, b j) | j : Fin k}` of `flHardInstance k m`. -/
private def diagCoalition {k m : ℕ} (b : Fin k → Fin m) : Finset (Fin k × Fin m) :=
  Finset.univ.image fun j : Fin k => (j, b j)

/-- Partial cross-section `T(i, b) = {(j, b j) | j ≠ i}` (size `k - 1`). -/
private def punctureCoalition {k m : ℕ} (i : Fin k) (b : Fin k → Fin m) :
    Finset (Fin k × Fin m) :=
  (Finset.univ.erase i).image fun j : Fin k => (j, b j)

/-- Row coalition `Aᵢ = {(i, x) | x : Fin m}` (size `m`). -/
private def rowCoalition {k m : ℕ} (i : Fin k) : Finset (Fin k × Fin m) :=
  Finset.univ.image fun x : Fin m => (i, x)

/-- Sample slice `S(i, b) = Aᵢ ∪ T(i, b)` of size `m + k - 1` ([JainMahdian2007], p. 401). -/
private def sliceCoalition {k m : ℕ} (i : Fin k) (b : Fin k → Fin m) :
    Finset (Fin k × Fin m) :=
  rowCoalition i ∪ punctureCoalition i b

private theorem row_puncture_disjoint {k m : ℕ} (i : Fin k) (b : Fin k → Fin m) :
    Disjoint (rowCoalition i) (punctureCoalition i b) := by
  rw [Finset.disjoint_left]
  intro a hrow hpunc
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hrow
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.1 hpunc
  exact (Finset.ne_of_mem_erase hj) (congrArg Prod.fst heq)

private theorem diagCoalition_update_eq {k m : ℕ} (i : Fin k) (b : Fin k → Fin m) (x : Fin m) :
    diagCoalition (Function.update b i x) = insert (i, x) (punctureCoalition i b) := by
  ext ⟨j, y⟩
  simp only [diagCoalition, punctureCoalition, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨r, rfl, hby⟩
    by_cases h : r = i
    · subst h; left; exact ⟨rfl, by simpa [Function.update_self] using hby.symm⟩
    · right; exact ⟨r, ⟨h, trivial⟩, rfl, by simpa [Function.update_of_ne h] using hby⟩
  · rintro (⟨rfl, rfl⟩ | ⟨r, ⟨hne, _⟩, rfl, rfl⟩)
    · exact ⟨j, rfl, by simp⟩
    · exact ⟨r, rfl, by simp [Function.update_of_ne hne]⟩

private theorem diagCoalition_update_subset_slice {k m : ℕ} (i : Fin k) (b : Fin k → Fin m)
    (x : Fin m) :
    diagCoalition (Function.update b i x) ⊆ sliceCoalition i b := by
  rw [diagCoalition_update_eq]
  exact Finset.insert_subset
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    Finset.subset_union_right

private theorem card_punctureCoalition {k m : ℕ} [NeZero k] (i : Fin k) (b : Fin k → Fin m) :
    ((punctureCoalition i b).card : ℝ) = k - 1 := by
  rw [punctureCoalition, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub NeZero.one_le, Nat.cast_one]

/-- A coalition inside the cross-section of `b` is served by `f_b` alone at cost `3 + |S|`. -/
private theorem cost_le_of_subset_diag {k m : ℕ} [NeZero m] (b : Fin k → Fin m)
    {S : Finset (Fin k × Fin m)} (hS : S ⊆ diagCoalition b) :
    (flHardInstance k m).toCostSharingGame.cost S ≤ 3 + S.card := by
  refine ((flHardInstance k m).toCostSharingGame_cost_le_planCost S {b}
    (Finset.singleton_nonempty b)).trans_eq ?_
  rw [planCost_eq, Finset.sum_singleton, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine congrArg (3 + ·) (Finset.sum_congr rfl fun a ha => ?_)
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 (hS ha)
  simp [flHardInstance]

private theorem diagCoalition_cost_le {k m : ℕ} [NeZero m] (b : Fin k → Fin m) :
    (flHardInstance k m).toCostSharingGame.cost (diagCoalition b) ≤ (k : ℝ) + 3 := by
  refine (cost_le_of_subset_diag b subset_rfl).trans_eq ?_
  rw [diagCoalition, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h,
    Finset.card_univ, Fintype.card_fin, add_comm]

private theorem punctureCoalition_cost_le {k m : ℕ} [NeZero k] [NeZero m]
    (i : Fin k) (b : Fin k → Fin m) :
    (flHardInstance k m).toCostSharingGame.cost (punctureCoalition i b) ≤ (k : ℝ) + 2 :=
  (cost_le_of_subset_diag (S := punctureCoalition i b) b
    (Finset.image_subset_image (Finset.erase_subset i _))).trans
    (by rw [card_punctureCoalition]; linarith)

/-- Lower and upper optimal cost of each sample slice `S(i, b) = Aᵢ ∪ T(i, b)` in
`flHardInstance k m`: exact optimal cost **`3 * m + k`** (`= 3 * m + (k - 1) + 1`). -/
private theorem sliceCoalition_cost {k m : ℕ} [NeZero k] [NeZero m]
    (i : Fin k) (b : Fin k → Fin m) :
    (flHardInstance k m).toCostSharingGame.cost (sliceCoalition i b) = 3 * (m : ℝ) + (k : ℝ) := by
  have hS_ne : (sliceCoalition i b).Nonempty :=
    ⟨(i, 0), Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩
  refine le_antisymm ?_ ?_
  · refine ((flHardInstance k m).toCostSharingGame_cost_le_planCost
      (sliceCoalition i b) {b} (Finset.singleton_nonempty b)).trans ?_
    rw [planCost_eq, Finset.sum_singleton, sliceCoalition,
      Finset.sum_union (row_puncture_disjoint i b)]
    have hrow : ∑ a ∈ rowCoalition i, ({b} : Finset (Fin k → Fin m)).inf'
        (Finset.singleton_nonempty b) (fun c => (flHardInstance k m).connCost c a) =
        3 * (m : ℝ) - 2 := by
      rw [rowCoalition, Finset.sum_image (fun x₁ _ x₂ _ h => congrArg Prod.snd h)]
      simpa [flHardInstance, eq_comm] using sum_ite_one_three (m := m) {b i}
    have hpunc : ∑ a ∈ punctureCoalition i b, ({b} : Finset (Fin k → Fin m)).inf'
        (Finset.singleton_nonempty b) (fun c => (flHardInstance k m).connCost c a) =
        (k : ℝ) - 1 := by
      rw [punctureCoalition, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
      simp [flHardInstance, Nat.cast_sub NeZero.one_le]
    rw [hrow, hpunc]
    dsimp only [flHardInstance]
    linarith
  · refine (flHardInstance k m).le_toCostSharingGame_cost_of_nonempty hS_ne fun F' hF' => ?_
    rw [planCost_eq, sliceCoalition, Finset.sum_union (row_puncture_disjoint i b)]
    have hopen : ∑ c ∈ F', (flHardInstance k m).openCost c = 3 * (F'.card : ℝ) := by
      simp [flHardInstance, mul_comm]
    let matched : Finset (Fin m) := F'.image fun c => c i
    have hrow_ge : 3 * (m : ℝ) - 2 * (matched.card : ℝ) ≤
        ∑ a ∈ rowCoalition i, F'.inf' hF' (fun c => (flHardInstance k m).connCost c a) := by
      rw [rowCoalition, Finset.sum_image (fun x₁ _ x₂ _ h => congrArg Prod.snd h),
        ← sum_ite_one_three matched]
      refine Finset.sum_le_sum fun x _ => ?_
      refine Finset.le_inf' _ _ fun c hc => ?_
      by_cases hcx : c i = x
      · rw [← hcx, ite_eq_left (Finset.mem_image_of_mem _ hc)]
        simp [flHardInstance]
      · simp only [flHardInstance, hcx, ↓reduceIte]
        split_ifs <;> norm_num
    have hpunc_ge : (k : ℝ) - 1 ≤
        ∑ a ∈ punctureCoalition i b, F'.inf' hF' (fun c => (flHardInstance k m).connCost c a) := by
      have hterm : ∀ a ∈ punctureCoalition i b, (1 : ℝ) ≤
          F'.inf' hF' (fun c => (flHardInstance k m).connCost c a) := fun a _ =>
        Finset.le_inf' _ _ fun c _ => by
          dsimp only [flHardInstance]; split_ifs <;> norm_num
      calc
        (k : ℝ) - 1 = ∑ _a ∈ punctureCoalition i b, (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_punctureCoalition]
        _ ≤ _ := Finset.sum_le_sum hterm
    have hF_ge1 : (1 : ℝ) ≤ (F'.card : ℝ) := Nat.one_le_cast.2 hF'.card_pos
    have hm_le : (matched.card : ℝ) ≤ (F'.card : ℝ) := Nat.cast_le.2 Finset.card_image_le
    linarith

/-- Self-inverse bijection `(b, x) ↦ (Function.update b i x, b i)` on `(Fin k → Fin m) × Fin m`. -/
private def swapCoordEquiv {k m : ℕ} (i : Fin k) :
    (Fin k → Fin m) × Fin m ≃ (Fin k → Fin m) × Fin m where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun q := (Function.update q.1 i q.2, q.1 i)
  left_inv _ := by simp [Function.update_idem]
  right_inv _ := by simp [Function.update_idem]

/-- **Exact finite double-counting inequality `(15.6)`** ([JainMahdian2007], p. 402): for every
`k ≥ 1`, `m ≥ 1`, and every cross-monotonic `γ`-budget-balanced cost-sharing scheme `ξ` on
`flHardInstance k m` (without assuming nonnegativity),
`γ * (3 * m + k) ≤ m * ((k + 3) / k) + (k + 2)`. -/
theorem flHardInstance_budgetBalance_le {k m : ℕ} [NeZero k] [NeZero m]
    {ξ : CostSharingScheme (Fin k × Fin m)} {γ : ℝ}
    (hcm : ξ.IsCrossMonotone)
    (hbb : ξ.IsBudgetBalanced (flHardInstance k m).toCostSharingGame γ) :
    γ * (3 * (m : ℝ) + (k : ℝ)) ≤
      (m : ℝ) * (((k : ℝ) + 3) / (k : ℝ)) + ((k : ℝ) + 2) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hpi_card : (Fintype.card (Fin k → Fin m) : ℝ) = (m : ℝ) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  have hmk_pos : (0 : ℝ) < (m : ℝ) ^ k := pow_pos hm_pos k
  -- Pointwise upper bound on `∑ a ∈ sliceCoalition i b, ξ.share (sliceCoalition i b) a`.
  have hslice_le (i : Fin k) (b : Fin k → Fin m) :
      ∑ a ∈ sliceCoalition i b, ξ.share (sliceCoalition i b) a ≤
        (∑ x : Fin m, ξ.share (diagCoalition (Function.update b i x)) (i, x)) +
          ((k : ℝ) + 2) := by
    have hsplit : ∑ a ∈ sliceCoalition i b, ξ.share (sliceCoalition i b) a =
        (∑ a ∈ rowCoalition i, ξ.share (sliceCoalition i b) a) +
          ∑ a ∈ punctureCoalition i b, ξ.share (sliceCoalition i b) a :=
      Finset.sum_union (f := ξ.share (sliceCoalition i b)) (row_puncture_disjoint i b)
    have h1 : ∑ a ∈ rowCoalition i, ξ.share (sliceCoalition i b) a ≤
        ∑ x : Fin m, ξ.share (diagCoalition (Function.update b i x)) (i, x) := by
      rw [rowCoalition, Finset.sum_image (fun x₁ _ x₂ _ h => congrArg Prod.snd h)]
      refine Finset.sum_le_sum fun x _ => hcm (diagCoalition_update_subset_slice i b x) ?_
      rw [diagCoalition_update_eq]
      exact Finset.mem_insert_self _ _
    have h2 : ∑ a ∈ punctureCoalition i b, ξ.share (sliceCoalition i b) a ≤ (k : ℝ) + 2 := by
      calc
        ∑ a ∈ punctureCoalition i b, ξ.share (sliceCoalition i b) a
            ≤ ∑ a ∈ punctureCoalition i b, ξ.share (punctureCoalition i b) a :=
              Finset.sum_le_sum fun a ha => hcm Finset.subset_union_right ha
        _ ≤ (flHardInstance k m).toCostSharingGame.cost (punctureCoalition i b) :=
              (hbb (punctureCoalition i b)).2
        _ ≤ (k : ℝ) + 2 := punctureCoalition_cost_le i b
    linarith
  -- Double sum of first term via the bijection `swapCoordEquiv`.
  have hfirst_sum :
      ∑ i : Fin k, ∑ b : Fin k → Fin m,
        ∑ x : Fin m, ξ.share (diagCoalition (Function.update b i x)) (i, x) =
      (m : ℝ) * ∑ c : Fin k → Fin m, ∑ i : Fin k, ξ.share (diagCoalition c) (i, c i) := by
    have hper_i (i : Fin k) :
        ∑ b : Fin k → Fin m, ∑ x : Fin m, ξ.share (diagCoalition (Function.update b i x)) (i, x) =
          (m : ℝ) * ∑ c : Fin k → Fin m, ξ.share (diagCoalition c) (i, c i) := by
      rw [← Fintype.sum_prod_type']
      have hterm (p : (Fin k → Fin m) × Fin m) :
          ξ.share (diagCoalition (Function.update p.1 i p.2)) (i, p.2) =
            ξ.share (diagCoalition (swapCoordEquiv i p).1) (i, (swapCoordEquiv i p).1 i) := by
        simp only [swapCoordEquiv, Equiv.coe_fn_mk, Function.update_self]
      simp_rw [hterm]
      rw [Equiv.sum_comp (swapCoordEquiv i)
        (fun q : (Fin k → Fin m) × Fin m => ξ.share (diagCoalition q.1) (i, q.1 i)),
        Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
    simp_rw [hper_i, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  -- Bound `∑ i, ξ.share (diagCoalition c) (i, c i) ≤ k + 3` for each cross-section `c`.
  have hdiag_le : ∀ c : Fin k → Fin m,
      ∑ i : Fin k, ξ.share (diagCoalition c) (i, c i) ≤ (k : ℝ) + 3 := fun c =>
    calc _ = ∑ a ∈ diagCoalition c, ξ.share (diagCoalition c) a := by
          rw [diagCoalition, Finset.sum_image fun _ _ _ _ h => congrArg Prod.fst h]
      _ ≤ _ := (hbb (diagCoalition c)).2.trans (diagCoalition_cost_le c)
  have hlhs_ge :
      (k : ℝ) * (m : ℝ) ^ k * (γ * (3 * (m : ℝ) + (k : ℝ))) ≤
        ∑ i : Fin k, ∑ b : Fin k → Fin m,
          ∑ a ∈ sliceCoalition i b, ξ.share (sliceCoalition i b) a := by
    calc _ = ∑ _i : Fin k, ∑ _b : Fin k → Fin m, (γ * (3 * (m : ℝ) + (k : ℝ))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hpi_card]
          ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => by
          rw [← sliceCoalition_cost i b]; exact (hbb (sliceCoalition i b)).1
  have hrhs_le :
      ∑ i : Fin k, ∑ b : Fin k → Fin m,
        ∑ a ∈ sliceCoalition i b, ξ.share (sliceCoalition i b) a ≤
      (m : ℝ) * (m : ℝ) ^ k * ((k : ℝ) + 3) + (k : ℝ) * (m : ℝ) ^ k * ((k : ℝ) + 2) := by
    have hsum := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := Finset.univ) fun c _ => hdiag_le c) hm_pos.le
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hslice_le i b).trans ?_
    simp only [Finset.sum_add_distrib, hfirst_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hpi_card] at hsum ⊢
    linarith
  refine le_of_mul_le_mul_left ((hlhs_ge.trans hrhs_le).trans_eq ?_) (mul_pos hk_pos hmk_pos)
  field_simp [hk_pos.ne']

/-- **Theorem 15.23** ([JainMahdian2007], Section 15.5, pp. 401–402; Immorlica–Mahdian–Mirrokni
2005): any cross-monotonic cost-sharing scheme for metric facility location is at most
**`(1 / 3)`-budget-balanced**. For every `γ > 1 / 3`, there exist finite positive `k, m : ℕ` such
that `flHardInstance k m` admits **no** cross-monotonic `γ`-budget-balanced cost-sharing scheme. -/
theorem not_exists_crossMonotone_isBudgetBalanced {γ : ℝ} (hγ : 1 / 3 < γ) :
    ∃ (k m : ℕ) (_ : NeZero k) (_ : NeZero m),
      (flHardInstance k m).IsMetric ∧
      ¬ ∃ ξ : CostSharingScheme (Fin k × Fin m),
          ξ.IsCrossMonotone ∧ ξ.IsBudgetBalanced (flHardInstance k m).toCostSharingGame γ := by
  have hε : 0 < 3 * γ - 1 := by linarith
  obtain ⟨k0, hk0⟩ := exists_nat_gt (6 / (3 * γ - 1))
  let k : ℕ := max k0 1
  have hk_cast : 6 / (3 * γ - 1) < (k : ℝ) :=
    lt_of_lt_of_le hk0 (by exact_mod_cast le_max_left k0 1)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hcoeff : (3 : ℝ) < (3 * γ - 1) * (k : ℝ) - 3 := by
    have h6 : 6 < (3 * γ - 1) * (k : ℝ) := (div_lt_iff₀ hε).1 hk_cast |>.trans_eq (mul_comm _ _)
    linarith
  let m : ℕ := k * (k + 2) + 1
  have : NeZero k := ⟨by omega⟩
  have : NeZero m := ⟨by omega⟩
  refine ⟨k, m, inferInstance, inferInstance, flHardInstance_isMetric k m, fun ⟨ξ, hcm, hbb⟩ => ?_⟩
  have hmul : γ * (3 * (m : ℝ) + (k : ℝ)) * (k : ℝ) ≤
      (m : ℝ) * ((k : ℝ) + 3) + (k : ℝ) * ((k : ℝ) + 2) :=
    (mul_le_mul_of_nonneg_right (flHardInstance_budgetBalance_le hcm hbb) hk_pos.le).trans_eq
      (by field_simp [hk_pos.ne'])
  have hm_ge : (k : ℝ) * ((k : ℝ) + 2) < (m : ℝ) := by exact_mod_cast Nat.lt_succ_self _
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  nlinarith [mul_lt_mul_of_pos_right hcoeff hm_pos, sq_nonneg (k : ℝ)]

end FacilityLocationInstance

end Cslib.GameTheory
