/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Cooperative.MoulinCostSharing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cross-monotonic cost sharing for metric facility location (`FLCostShare`)

This module formalizes the **Pál–Tardos `1 / 3`-budget-balanced cross-monotonic cost-sharing
scheme** `FLCostShare` for cooperative metric facility location games ([JainMahdian2007],
Section 15.4.2, Figure 15.4, and **Theorem 15.21**, pp. 397–400).

## Closed-form characterization of ghost cost shares

In `FLCostShare` (Figure 15.4, p. 399), every agent `j ∈ T` continuously grows a *ghost* cost
share `α'ⱼ(t) = t` at uniform rate `1`, even after `j`'s real cost share `αⱼ` freezes. Consequently,
each facility `i : F` becomes tight independently of agent freezing at time `t = openTime I i T`
satisfying

`∑ j ∈ T, max 0 (t - I.connCost i j) = I.openCost i`

(`sum_max_sub_openTime_eq_openCost`). For nonempty `T`, `openTime I i T` admits the closed-form
minimum over nonempty subsets `S ⊆ T`:

`openTime I i T = min_{∅ ≠ S ⊆ T} (I.openCost i + ∑ j ∈ S, I.connCost i j) / |S|`.

When `0 < I.openCost i`, this time is **unique** (`eq_openTime_of_sum_max_eq`). When
`I.openCost i = 0`, `openTime I i T = min_{j ∈ T} I.connCost i j`, which gives the exact same
freeze values `max (openTime I i T) (I.connCost i j) = I.connCost i j` as opening `i` at time `0`.
Agent `j ∈ T` freezes at the first time `t` when some facility `i` is open (`openTime I i T ≤ t`)
and within distance `I.connCost i j ≤ t`:

`(flCostShareScheme I).share T j = min_{i : F} max (I.openTime i T) (I.connCost i j)`.

## Main definitions

* `Cslib.GameTheory.FacilityLocationInstance.openTime`: facility opening time in `FLCostShare`
  ([JainMahdian2007], Figure 15.4, p. 399).
* `Cslib.GameTheory.FacilityLocationInstance.flCostShareScheme`: ghost primal-dual cost-sharing
  scheme `FLCostShare` as a `CostSharingScheme A`.

## Main results

* `Cslib.GameTheory.FacilityLocationInstance.sum_max_sub_openTime_eq_openCost`: ghost tightness
  equation `∑ j ∈ T, max 0 (openTime I i T - I.connCost i j) = I.openCost i`.
* `Cslib.GameTheory.FacilityLocationInstance.eq_openTime_of_sum_max_eq`: uniqueness of `openTime`
  whenever `0 < I.openCost i`.
* `Cslib.GameTheory.FacilityLocationInstance.flCostShareScheme_isNonneg`: nonnegativity of
  `FLCostShare`.
* `Cslib.GameTheory.FacilityLocationInstance.flCostShareScheme_isCrossMonotone`: cross-monotonicity
  of `FLCostShare` ([JainMahdian2007], Section 15.4.2, p. 398).
* `Cslib.GameTheory.FacilityLocationInstance.flCostShareScheme_sum_le_cost`: competitiveness
  `∑ j ∈ T, share T j ≤ c(T)` (holds for *arbitrary*, not necessarily metric, instances).
* `Cslib.GameTheory.FacilityLocationInstance.flCostShareScheme_isBudgetBalanced`: **Theorem 15.21**
  ([JainMahdian2007], pp. 398–400): `FLCostShare` is **`(1 / 3)`-budget-balanced** on every metric
  facility location instance (hence yields a `(1 / 3)`-budget-balanced group-strategyproof
  `moulinMechanism` via `CostSharingScheme.moulinMechanism_isGroupStrategyproof`, and a
  `(1 / 3)`-core allocation via `CostSharingScheme.inApproxCore_univ`).

## Source verification note

In [JainMahdian2007], p. 400 (proof of Theorem 15.21), the prose writes "`t_{i₁} = αⱼ` (i.e., the
facility whose opening has caused the cost share of `j` to freeze)". Formally, `j` can freeze
either when facility `i₁` opens (`t_{i₁} = αⱼ`, `d_{i₁, j} ≤ αⱼ`) or when `αⱼ` hits `d_{i₁, j}`
for an already-open facility `i₁` (`d_{i₁, j} = αⱼ`, `t_{i₁} ≤ αⱼ`). In both cases
`max (t_{i₁}) (d_{i₁, j}) = αⱼ`, giving `t_{i₁} ≤ αⱼ` and `d_{i₁, j} ≤ αⱼ`, so the triangle
inequality `d(i, i₂) ≤ d(i, j) + d(i₁, j) + 2 t_{i₁} ≤ tᵢ + 3 αⱼ` holds verbatim.

## References

* [JainMahdian2007]
-/

public section

namespace Cslib.GameTheory

namespace FacilityLocationInstance

section OpeningTime

variable {A F : Type*}

/-- Facility opening time `tᵢ(T)` in `FLCostShare` ([JainMahdian2007], Figure 15.4, p. 399): for
nonempty coalition `T`, the minimum over nonempty `S ⊆ T` of
`(openCost i + ∑ j ∈ S, connCost i j) / |S|`, and `0` for `T = ∅`. -/
noncomputable def openTime (I : FacilityLocationInstance A F) (i : F) (T : Finset A) : ℝ :=
  open scoped Classical in
  if hT : T.Nonempty then
    (T.powerset.filter Finset.Nonempty).inf'
      ⟨T, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.Subset.rfl, hT⟩⟩
      (fun S => (I.openCost i + ∑ j ∈ S, I.connCost i j) / (S.card : ℝ))
  else 0

theorem openTime_le_ratio (I : FacilityLocationInstance A F) (i : F) {T S : Finset A}
    (hS : S.Nonempty) (hST : S ⊆ T) :
    I.openTime i T ≤ (I.openCost i + ∑ j ∈ S, I.connCost i j) / (S.card : ℝ) := by
  have hT : T.Nonempty := hS.mono hST
  dsimp only [openTime]
  split_ifs
  · exact Finset.inf'_le
      (fun U => (I.openCost i + ∑ j ∈ U, I.connCost i j) / (U.card : ℝ))
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hST, hS⟩)

theorem openTime_nonneg (I : FacilityLocationInstance A F) (i : F) (T : Finset A) :
    0 ≤ I.openTime i T := by
  dsimp only [openTime]
  split_ifs
  · refine Finset.le_inf' _ _ fun S _ => div_nonneg ?_ (Nat.cast_nonneg _)
    exact add_nonneg (I.openCost_nonneg i) (Finset.sum_nonneg fun j _ => I.connCost_nonneg i j)
  · exact le_rfl

private theorem exists_subset_eq_openTime (I : FacilityLocationInstance A F) (i : F)
    {T : Finset A} (hT : T.Nonempty) :
    ∃ S : Finset A, S ⊆ T ∧ S.Nonempty ∧
      I.openTime i T = (I.openCost i + ∑ j ∈ S, I.connCost i j) / (S.card : ℝ) := by
  classical
  dsimp only [openTime]
  split_ifs
  obtain ⟨S, hSmem, heq⟩ := Finset.exists_mem_eq_inf'
    (⟨T, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.Subset.rfl, hT⟩⟩ :
      (T.powerset.filter Finset.Nonempty).Nonempty)
    (fun U => (I.openCost i + ∑ j ∈ U, I.connCost i j) / (U.card : ℝ))
  refine ⟨S, Finset.mem_powerset.1 (Finset.mem_filter.1 hSmem).1,
    (Finset.mem_filter.1 hSmem).2, heq⟩

/-- Increasing the active coalition can only hasten (decrease) a facility's opening time. -/
theorem openTime_antitone (I : FacilityLocationInstance A F) (i : F) {S T : Finset A}
    (hS : S.Nonempty) (hST : S ⊆ T) :
    I.openTime i T ≤ I.openTime i S := by
  obtain ⟨S', hS'sub, hS'ne, heq⟩ := I.exists_subset_eq_openTime i hS
  rw [heq]
  exact I.openTime_le_ratio i hS'ne (hS'sub.trans hST)

/-- **Ghost tightness equation** for `FLCostShare` ([JainMahdian2007], Figure 15.4, p. 399): for
every nonempty coalition `T` and facility `i`, `∑ j ∈ T, max 0 (tᵢ(T) - dᵢⱼ) = fᵢ`. -/
theorem sum_max_sub_openTime_eq_openCost (I : FacilityLocationInstance A F) (i : F)
    {T : Finset A} (hT : T.Nonempty) :
    ∑ j ∈ T, max 0 (I.openTime i T - I.connCost i j) = I.openCost i := by
  classical
  set t := I.openTime i T
  refine le_antisymm ?_ ?_
  · set P : Finset A := T.filter fun j => I.connCost i j < t
    have hPsub : P ⊆ T := Finset.filter_subset _ T
    have hzero : ∀ j ∈ T, j ∉ P → max 0 (t - I.connCost i j) = 0 := fun j hj hjP =>
      max_eq_left (sub_nonpos.2 (by simpa [P, Finset.mem_filter, hj] using hjP))
    rw [← Finset.sum_subset hPsub hzero]
    by_cases hP : P.Nonempty
    · have hcard_pos : (0 : ℝ) < P.card := mod_cast hP.card_pos
      have hmul := (le_div_iff₀ hcard_pos).1 (I.openTime_le_ratio i hP hPsub)
      rw [Finset.sum_congr rfl fun j hj =>
          max_eq_right (sub_nonneg.2 (Finset.mem_filter.1 hj).2.le),
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hP, Finset.sum_empty]
      exact I.openCost_nonneg i
  · obtain ⟨S, hST, hSne, heq⟩ := I.exists_subset_eq_openTime i hT
    have hcard_pos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
    have hmul : (S.card : ℝ) * t = I.openCost i + ∑ j ∈ S, I.connCost i j := by
      have ht : t = (I.openCost i + ∑ j ∈ S, I.connCost i j) / (S.card : ℝ) := heq
      field_simp [hcard_pos.ne'] at ht
      linarith
    calc
      I.openCost i = (S.card : ℝ) * t - ∑ j ∈ S, I.connCost i j := by linarith
      _ = ∑ j ∈ S, (t - I.connCost i j) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ S, max 0 (t - I.connCost i j) :=
            Finset.sum_le_sum fun j _ => le_max_right _ _
      _ ≤ ∑ j ∈ T, max 0 (t - I.connCost i j) :=
            Finset.sum_le_sum_of_subset_of_nonneg hST fun j _ _ => le_max_left _ _

/-- For strictly positive opening cost `0 < I.openCost i`, `I.openTime i T` is the **unique** time
`t` solving `∑ j ∈ T, max 0 (t - I.connCost i j) = I.openCost i`. -/
theorem eq_openTime_of_sum_max_eq (I : FacilityLocationInstance A F) {i : F} {T : Finset A}
    (hT : T.Nonempty) (hf : 0 < I.openCost i) {t : ℝ}
    (ht : ∑ j ∈ T, max 0 (t - I.connCost i j) = I.openCost i) :
    t = I.openTime i T := by
  have hstrict : ∀ {x y : ℝ}, x < y → 0 < ∑ j ∈ T, max 0 (x - I.connCost i j) →
      ∑ j ∈ T, max 0 (x - I.connCost i j) < ∑ j ∈ T, max 0 (y - I.connCost i j) := by
    intro x y hxy hxpos
    obtain ⟨j₀, hj₀T, hj₀pos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
      (g := fun j => max 0 (x - I.connCost i j)) (by rwa [Finset.sum_const_zero])
    refine Finset.sum_lt_sum (fun j _ => max_le_max_left 0 (sub_le_sub_right hxy.le _))
      ⟨j₀, hj₀T, ?_⟩
    rw [max_eq_right (lt_max_iff.1 hj₀pos |>.resolve_left (lt_irrefl 0)).le]
    exact (sub_lt_sub_right hxy _).trans_le (le_max_right _ _)
  have hgoal := I.sum_max_sub_openTime_eq_openCost i hT
  rcases lt_trichotomy t (I.openTime i T) with hlt | heq | hgt
  · exact absurd (hstrict hlt (ht.symm ▸ hf)) (by linarith)
  · exact heq
  · exact absurd (hstrict hgt (hgoal.symm ▸ hf)) (by linarith)

/-- When `I.openCost i = 0`, `openTime I i T ≤ connCost i j` for every `j ∈ T`. -/
theorem openTime_le_connCost_of_zero (I : FacilityLocationInstance A F) {i : F} {T : Finset A}
    (hf : I.openCost i = 0) {j : A} (hj : j ∈ T) :
    I.openTime i T ≤ I.connCost i j := by
  have h := I.openTime_le_ratio i (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.2 hj)
  simpa [hf] using h

end OpeningTime

section Scheme

variable {A F : Type*} [Fintype F] [Nonempty F]

/-- The **Pál–Tardos `FLCostShare` cost-sharing scheme** ([JainMahdian2007], Figure 15.4, p. 399):
for a coalition `T` and agent `j ∈ T`,
`share T j = min_{i : F} max (openTime I i T) (connCost i j)`. -/
noncomputable def flCostShareScheme (I : FacilityLocationInstance A F) : CostSharingScheme A where
  share T j :=
    open scoped Classical in
    if j ∈ T then
      Finset.univ.inf' Finset.univ_nonempty fun i : F => max (I.openTime i T) (I.connCost i j)
    else 0
  share_eq_zero_of_not_mem _ _ hj := by
    classical
    exact ite_eq_right hj

theorem flCostShareScheme_share_of_mem (I : FacilityLocationInstance A F) {T : Finset A}
    {j : A} (hj : j ∈ T) :
    I.flCostShareScheme.share T j =
      Finset.univ.inf' Finset.univ_nonempty fun i : F => max (I.openTime i T) (I.connCost i j) := by
  classical
  exact ite_eq_left hj

/-- Every `FLCostShare` cost share is nonnegative. -/
theorem flCostShareScheme_isNonneg (I : FacilityLocationInstance A F) :
    I.flCostShareScheme.IsNonneg := by
  intro T j
  by_cases hj : j ∈ T
  · rw [I.flCostShareScheme_share_of_mem hj]
    exact Finset.le_inf' _ _ fun i _ => le_trans (I.connCost_nonneg i j) (le_max_right _ _)
  · rw [I.flCostShareScheme.share_eq_zero_of_not_mem hj]

/-- **Cross-monotonicity of `FLCostShare`** ([JainMahdian2007], Section 15.4.2, p. 398): growing the
coalition `S ⊆ T` decreases every facility's opening time `openTime I i T ≤ openTime I i S`, hence
decreases every agent's cost share `share T j ≤ share S j`. -/
theorem flCostShareScheme_isCrossMonotone (I : FacilityLocationInstance A F) :
    I.flCostShareScheme.IsCrossMonotone := by
  intro S T hST j hjS
  have hjT : j ∈ T := hST hjS
  rw [I.flCostShareScheme_share_of_mem hjT, I.flCostShareScheme_share_of_mem hjS]
  refine Finset.le_inf' _ _ fun i _ => ?_
  calc
    Finset.univ.inf' Finset.univ_nonempty (fun k => max (I.openTime k T) (I.connCost k j))
        ≤ max (I.openTime i T) (I.connCost i j) := Finset.inf'_le _ (Finset.mem_univ i)
    _ ≤ max (I.openTime i S) (I.connCost i j) :=
        max_le_max_right _ (I.openTime_antitone i ⟨j, hjS⟩ hST)

/-- Upper budget-balance bound (competitiveness) for `FLCostShare`: on **every** (even non-metric)
facility location instance `I`, `∑ j ∈ T, share T j ≤ I.toCostSharingGame.cost T`. -/
theorem flCostShareScheme_sum_le_cost (I : FacilityLocationInstance A F) (T : Finset A) :
    ∑ j ∈ T, I.flCostShareScheme.share T j ≤ I.toCostSharingGame.cost T := by
  classical
  by_cases hT : T.Nonempty
  · refine I.le_toCostSharingGame_cost_of_nonempty hT fun F' hF' => ?_
    choose φ hφ_mem hφ_eq using fun j : A =>
      Finset.exists_mem_eq_inf' hF' (fun i : F => I.connCost i j)
    have hfiber : ∀ i ∈ F',
        ∑ j ∈ T.filter (fun j => φ j = i), I.flCostShareScheme.share T j ≤
          I.openCost i + ∑ j ∈ T.filter (fun j => φ j = i), I.connCost i j := by
      intro i _
      have hterm : ∀ j ∈ T.filter (fun j => φ j = i), I.flCostShareScheme.share T j ≤
          I.connCost i j + max 0 (I.openTime i T - I.connCost i j) := fun j hj => by
        rw [I.flCostShareScheme_share_of_mem (Finset.mem_filter.1 hj).1]
        exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (max_le
          (by linarith [le_max_right 0 (I.openTime i T - I.connCost i j)])
          (by linarith [le_max_left 0 (I.openTime i T - I.connCost i j)]))
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_add_distrib, ← I.sum_max_sub_openTime_eq_openCost i hT]
      linarith [Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun j => φ j = i) T)
        fun j _ _ => le_max_left (0 : ℝ) (I.openTime i T - I.connCost i j)]
    have hsplit_conn : ∑ j ∈ T, F'.inf' hF' (fun i => I.connCost i j) =
        ∑ i ∈ F', ∑ j ∈ T.filter (fun j => φ j = i), I.connCost i j := by
      rw [← Finset.sum_fiberwise_of_maps_to (fun j _ => hφ_mem j)
        (fun j => F'.inf' hF' (fun i => I.connCost i j))]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [hφ_eq j, (Finset.mem_filter.1 hj).2]
    rw [← Finset.sum_fiberwise_of_maps_to (fun j _ => hφ_mem j)
      (fun j => I.flCostShareScheme.share T j), planCost_eq, hsplit_conn, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hfiber
  · simp [Finset.not_nonempty_iff_eq_empty.1 hT, I.toCostSharingGame.cost_empty]

/-! ### Greedy facility-pruning postprocessing and proof of Theorem 15.21 -/

/-- Greedy independent dominating subset of `rem` ordered by nondecreasing `t`: repeatedly select
a remaining facility `i₀` minimizing `t`, then discard all `i` with `dF i₀ i ≤ 2 * t i`. -/
private theorem exists_greedy_cover {F : Type*} (rem : Finset F) (t : F → ℝ) (dF : F → F → ℝ)
    (ht_nn : ∀ i, 0 ≤ t i) (hd_sym : ∀ a b, dF a b = dF b a) (hd_self : ∀ a, dF a a = 0) :
    ∃ F' : Finset F, F' ⊆ rem ∧
      (∀ a ∈ F', ∀ b ∈ F', a ≠ b → 2 * max (t a) (t b) < dF a b) ∧
      (∀ i ∈ rem, ∃ i' ∈ F', t i' ≤ t i ∧ dF i' i ≤ 2 * t i) := by
  classical
  induction rem using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i₀, hi₀, hi₀_min⟩ := Finset.exists_min_image S t hS
      let S' : Finset F := S.filter fun i => 2 * t i < dF i₀ i
      have hi₀_nmem : i₀ ∉ S' := by
        simp only [S', Finset.mem_filter, not_and, not_lt]
        intro _
        rw [hd_self i₀]
        linarith [ht_nn i₀]
      obtain ⟨F', hF'sub, hind, hdom⟩ := ih S' (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.filter_subset _ S, fun h => hi₀_nmem (h ▸ hi₀)⟩)
      refine ⟨insert i₀ F',
        Finset.insert_subset hi₀ (hF'sub.trans (Finset.filter_subset _ S)), ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha' <;>
          rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact absurd rfl hab
        · have hb'S' := hF'sub hb'
          rw [max_eq_right (hi₀_min b (Finset.mem_filter.1 hb'S').1)]
          exact (Finset.mem_filter.1 hb'S').2
        · have ha'S' := hF'sub ha'
          rw [max_eq_left (hi₀_min a (Finset.mem_filter.1 ha'S').1), hd_sym a b]
          exact (Finset.mem_filter.1 ha'S').2
        · exact hind a ha' b hb' hab
      · intro i hi
        by_cases hclose : dF i₀ i ≤ 2 * t i
        · exact ⟨i₀, Finset.mem_insert_self _ _, hi₀_min i hi, hclose⟩
        · obtain ⟨i', hi', ht_le, hd_le⟩ :=
            hdom i (Finset.mem_filter.2 ⟨hi, lt_of_not_ge hclose⟩)
          exact ⟨i', Finset.mem_insert_of_mem hi', ht_le, hd_le⟩
    · exact ⟨∅, Finset.empty_subset _, fun _ h => absurd h (Finset.notMem_empty _),
        fun i hi => absurd ⟨i, hi⟩ hS⟩

/-- Some facility witnesses an agent's `FLCostShare` share: its opening time and its connection
cost are both at most the share. -/
private theorem exists_le_share (I : FacilityLocationInstance A F) {T : Finset A} {j : A}
    (hj : j ∈ T) : ∃ i, I.openTime i T ≤ I.flCostShareScheme.share T j ∧
      I.connCost i j ≤ I.flCostShareScheme.share T j := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun k : F => max (I.openTime k T) (I.connCost k j))
  rw [I.flCostShareScheme_share_of_mem hj, h]
  exact ⟨i, le_max_left _ _, le_max_right _ _⟩

/-- Lower bound (cost recovery ≥ `1 / 3`) in **Theorem 15.21** ([JainMahdian2007], pp. 398–400):
for every metric facility location instance `I`, `c(T) ≤ 3 * ∑ j ∈ T, share T j`. -/
private theorem flCostShareScheme_cost_le_three_mul_sum (I : FacilityLocationInstance A F)
    (hmet : I.IsMetric) (T : Finset A) :
    I.toCostSharingGame.cost T ≤ 3 * ∑ j ∈ T, I.flCostShareScheme.share T j := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨m, hm⟩ := hmet
    let _ : PseudoMetricSpace (A ⊕ F) := m
    let t : F → ℝ := fun i => I.openTime i T
    let dF : F → F → ℝ := fun a b => dist (Sum.inr a : A ⊕ F) (Sum.inr b)
    have hdist_eq : ∀ i j, I.connCost i j = dist (Sum.inr i : A ⊕ F) (Sum.inl j) := hm
    obtain ⟨F', _, hind, hdom_univ⟩ := exists_greedy_cover (Finset.univ : Finset F) t dF
      (fun i => I.openTime_nonneg i T)
      (fun a b => dist_comm _ _)
      (fun a => dist_self _)
    have hdom : ∀ i : F, ∃ i' ∈ F', t i' ≤ t i ∧ dF i' i ≤ 2 * t i := fun i =>
      hdom_univ i (Finset.mem_univ i)
    obtain ⟨i₀⟩ := ‹Nonempty F›
    obtain ⟨i₀', hi₀', _, _⟩ := hdom i₀
    have hF' : F'.Nonempty := ⟨i₀', hi₀'⟩
    let ball : F → Finset A := fun i => T.filter fun j => I.connCost i j ≤ t i
    have hdisj : Set.PairwiseDisjoint (F' : Set F) ball := by
      intro a ha b hb hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j hja hjb
      have da : dist (Sum.inr a : A ⊕ F) (Sum.inl j) ≤ t a :=
        hdist_eq a j ▸ (Finset.mem_filter.1 hja).2
      have db : dist (Sum.inr b : A ⊕ F) (Sum.inl j) ≤ t b :=
        hdist_eq b j ▸ (Finset.mem_filter.1 hjb).2
      have htri := dist_comm (Sum.inl j : A ⊕ F) (Sum.inr b) ▸
        dist_triangle (Sum.inr a : A ⊕ F) (Sum.inl j) (Sum.inr b)
      linarith [hind a ha b hb hab, le_max_left (t a) (t b), le_max_right (t a) (t b)]
    -- Every agent `j ∈ ball i` (`i ∈ F'`) satisfies `t i ≤ 3 * share T j`.
    have hball_share : ∀ i ∈ F', ∀ j ∈ ball i, t i ≤ 3 * I.flCostShareScheme.share T j := by
      intro i hiF j hjball
      have hjT : j ∈ T := (Finset.mem_filter.1 hjball).1
      have hdij : I.connCost i j ≤ t i := (Finset.mem_filter.1 hjball).2
      set α := I.flCostShareScheme.share T j
      obtain ⟨i₁, hti₁, hdi₁⟩ : ∃ i₁, t i₁ ≤ α ∧ I.connCost i₁ j ≤ α := I.exists_le_share hjT
      have hα_nn : 0 ≤ α := I.flCostShareScheme_isNonneg T j
      obtain ⟨i₂, hi₂F, hti₂_le, hd_i₂i₁⟩ := hdom i₁
      by_cases heq : i₂ = i
      · subst heq; linarith
      · by_contra hlt
        have hα_lt : 3 * α < t i := lt_of_not_ge hlt
        have htri1 : dF i i₂ ≤
            dist (Sum.inr i : A ⊕ F) (Sum.inl j) + dist (Sum.inl j : A ⊕ F) (Sum.inr i₂) :=
          dist_triangle _ _ _
        have htri2 : dist (Sum.inl j : A ⊕ F) (Sum.inr i₂) ≤
            dist (Sum.inl j : A ⊕ F) (Sum.inr i₁) + dist (Sum.inr i₁ : A ⊕ F) (Sum.inr i₂) :=
          dist_triangle _ _ _
        rw [← hdist_eq i j] at htri1
        rw [dist_comm (Sum.inl j : A ⊕ F) (Sum.inr i₁), ← hdist_eq i₁ j,
          dist_comm (Sum.inr i₁ : A ⊕ F) (Sum.inr i₂)] at htri2
        change dF i₂ i₁ ≤ 2 * t i₁ at hd_i₂i₁
        have hfar := hind i hiF i₂ hi₂F (Ne.symm heq)
        rw [max_eq_left (by linarith : t i₂ ≤ t i)] at hfar
        linarith
    -- For each `i ∈ F'`, `openCost i + ∑ j ∈ ball i, connCost i j ≤ 3 * ∑ j ∈ ball i, share T j`.
    have hfac_bound : ∀ i ∈ F',
        I.openCost i + ∑ j ∈ ball i, I.connCost i j ≤
          3 * ∑ j ∈ ball i, I.flCostShareScheme.share T j := by
      intro i hiF
      have hzero : ∀ j ∈ T, j ∉ ball i → max 0 (t i - I.connCost i j) = 0 := fun j hj hjb =>
        max_eq_left (sub_nonpos.2 (le_of_lt (by simpa [ball, Finset.mem_filter, hj] using hjb)))
      have hopen : I.openCost i = ∑ j ∈ ball i, (t i - I.connCost i j) := by
        rw [← I.sum_max_sub_openTime_eq_openCost i hT,
          ← Finset.sum_subset (Finset.filter_subset _ T) hzero]
        exact Finset.sum_congr rfl fun j hj =>
          max_eq_right (sub_nonneg.2 (Finset.mem_filter.1 hj).2)
      rw [hopen, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => by linarith [hball_share i hiF j hj]
    -- For every agent `j ∈ T`, its nearest facility in `F'` has distance ≤ `3 * share T j`.
    have hrest_bound : ∀ j ∈ T,
        F'.inf' hF' (fun i => I.connCost i j) ≤ 3 * I.flCostShareScheme.share T j := by
      intro j hjT
      obtain ⟨i₁, hti₁, hdi₁⟩ : ∃ i₁, t i₁ ≤ I.flCostShareScheme.share T j ∧
          I.connCost i₁ j ≤ I.flCostShareScheme.share T j := I.exists_le_share hjT
      obtain ⟨i', hi'F, _, hd_i'i₁⟩ := hdom i₁
      have htri : dist (Sum.inr i' : A ⊕ F) (Sum.inl j) ≤
          dist (Sum.inr i' : A ⊕ F) (Sum.inr i₁) + dist (Sum.inr i₁ : A ⊕ F) (Sum.inl j) :=
        dist_triangle _ _ _
      rw [← hdist_eq i' j, ← hdist_eq i₁ j] at htri
      exact (Finset.inf'_le (fun i => I.connCost i j) hi'F).trans (by
        change dF i' i₁ ≤ 2 * t i₁ at hd_i'i₁; linarith)
    let U : Finset A := F'.biUnion ball
    have hUT : U ⊆ T := Finset.biUnion_subset.2 fun _ _ => Finset.filter_subset _ T
    have hconn_split :
        ∑ j ∈ T, F'.inf' hF' (fun i => I.connCost i j) =
          (∑ j ∈ U, F'.inf' hF' (fun i => I.connCost i j)) +
            ∑ j ∈ T \ U, F'.inf' hF' (fun i => I.connCost i j) :=
      (Finset.sum_sdiff hUT).symm.trans (add_comm _ _)
    have hU_le : ∑ j ∈ U, F'.inf' hF' (fun i => I.connCost i j) ≤
        ∑ i ∈ F', ∑ j ∈ ball i, I.connCost i j := by
      rw [Finset.sum_biUnion hdisj]
      exact Finset.sum_le_sum fun i hi =>
        Finset.sum_le_sum fun j _ => Finset.inf'_le (fun k => I.connCost k j) hi
    have hshare_split :
        ∑ j ∈ T, I.flCostShareScheme.share T j =
          (∑ i ∈ F', ∑ j ∈ ball i, I.flCostShareScheme.share T j) +
            ∑ j ∈ T \ U, I.flCostShareScheme.share T j := by
      rw [← Finset.sum_biUnion hdisj, add_comm, Finset.sum_sdiff hUT]
    refine (I.toCostSharingGame_cost_le_planCost T F' hF').trans ?_
    rw [planCost_eq, hconn_split, hshare_split]
    have hsum_F' : (∑ i ∈ F', I.openCost i) + ∑ i ∈ F', ∑ j ∈ ball i, I.connCost i j ≤
        3 * ∑ i ∈ F', ∑ j ∈ ball i, I.flCostShareScheme.share T j := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum hfac_bound
    have hsum_rem : ∑ j ∈ T \ U, F'.inf' hF' (fun i => I.connCost i j) ≤
        3 * ∑ j ∈ T \ U, I.flCostShareScheme.share T j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => hrest_bound j (Finset.mem_sdiff.1 hj).1
    linarith
  · simp [Finset.not_nonempty_iff_eq_empty.1 hT, I.toCostSharingGame.cost_empty]

/-- **Theorem 15.21** ([JainMahdian2007], Section 15.4.2, p. 398; Pál–Tardos 2003): on every
metric facility location instance `I`, the ghost primal-dual scheme `I.flCostShareScheme` is
**`(1 / 3)`-budget-balanced** for `I.toCostSharingGame`. Together with
`flCostShareScheme_isCrossMonotone` and `flCostShareScheme_isNonneg`, passing it to
`CostSharingScheme.moulinMechanism` yields a `(1 / 3)`-budget-balanced, group-strategyproof
mechanism with no positive transfers, voluntary participation, and consumer sovereignty. -/
theorem flCostShareScheme_isBudgetBalanced (I : FacilityLocationInstance A F)
    (hmet : I.IsMetric) :
    I.flCostShareScheme.IsBudgetBalanced I.toCostSharingGame (1 / 3) := fun T =>
  ⟨by linarith [I.flCostShareScheme_cost_le_three_mul_sum hmet T],
    I.flCostShareScheme_sum_le_cost T⟩

end Scheme

end FacilityLocationInstance

end Cslib.GameTheory
