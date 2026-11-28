/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Tree
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Convex
import CslibFrontier.Foundations.Data.Fintype.UpdateInduction
import Mathlib.Tactic.Linarith

/-!
# Strategyproof facility location on tree metric graphs

This module formalizes the tree characterization theorem of [SchummerVohra2002] (Theorem 1,
p. 15 of the January 2001 author preprint): on a finite tree metric graph `MetricGraph W`
(`W.graph.IsTree`), a deterministic facility-location mechanism is strategyproof and surjective
if and only if it is the evaluation map of an extended median voter scheme (`TreeEMVS`).

`TreeEMVS` adapts the source's definition. The source builds an extended median voter scheme from
a consistent family of generalized median voter schemes on leaf-to-leaf paths (Section 3,
pp. 9–15); `TreeEMVS` instead records, at every point and in every direction, which coalitions
win. The `TreeEMVS` docstring describes the correspondence.

The module also proves that every such mechanism is strongly group strategyproof. This
strengthening is not stated in the source, whose Theorem 1 concerns individual strategyproofness.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.TreeEMVS`: an extended median voter scheme on a tree metric
  graph, specified by monotone branch-winning coalition families `win y q : Finset ι → Prop`
  satisfying branch invariance, nesting, duality, disjoint-branch exclusivity, and interior
  openness.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.IsEquilibrium`: equilibrium condition asserting that
  at `y`, no branch contains a winning coalition of reported agent locations.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.eval`: the unique equilibrium outcome of a `TreeEMVS`.

## Main results

* `Cslib.GameTheory.FacilityLocation.TreeEMVS.existsUnique_equilibrium`: every `TreeEMVS` admits a
  unique equilibrium outcome for every profile.
* `Cslib.GameTheory.FacilityLocation.TreeEMVS.eval_isGroupStrategyProof`: every `TreeEMVS`
  evaluates to a strongly group-strategyproof mechanism.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_treeEMVS`:
  Schummer–Vohra's characterization on trees: deterministic onto strategyproof mechanisms on
  `MetricGraph W` coincide with `TreeEMVS.eval`.
* `Cslib.GameTheory.FacilityLocation.isGroupStrategyProof_of_isStrategyProof_of_surjective_tree`:
  every deterministic onto strategyproof mechanism on a tree metric graph is strongly group
  strategyproof.

## References

* [SchummerVohra2002] J. Schummer and R. V. Vohra, "Strategy-proof Location on a Network",
  Journal of Economic Theory 104(2) (2002), 405–428.
-/

public section

open SimpleGraph SimpleGraph.MetricGraph

namespace Cslib.GameTheory.FacilityLocation

section Helpers

private lemma exists_pos_le_dist_finset {ι G : Type*} [PseudoMetricSpace G] (S : Finset ι)
    (x : ι → G) (y : G) (hpos : ∀ i ∈ S, 0 < dist y (x i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ dist y (x i) := by
  by_cases hne : S.Nonempty
  · obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => dist y (x i)) hne
    exact ⟨dist y (x i), hpos i hi, hmin⟩
  · exact ⟨1, zero_lt_one, fun i hi => absurd ⟨i, hi⟩ hne⟩

private lemma sp_dist_le {ι G : Type*} [DecidableEq ι] [PseudoMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {f : (ι → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (z : ι → G) (i : ι) (w : G) :
    dist (f z) (z i) ≤ dist (f (Function.update z i w)) (z i) := by
  simpa only [_root_.dist_comm] using (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp z i w

private lemma sp_update_dist_le {ι G : Type*} [DecidableEq ι] [PseudoMetricSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {f : (ι → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (z : ι → G) (i : ι) (w : G) :
    dist (f (Function.update z i w)) w ≤ dist (f z) w := by
  have h := sp_dist_le hf_sp (Function.update z i w) i (z i)
  simpa only [Function.update_idem, Function.update_eq_self, Function.update_self] using h

private lemma sp_update_self_outcome {ι G : Type*} [DecidableEq ι] [MetricSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {f : (ι → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (z : ι → G) (i : ι) :
    f (Function.update z i (f z)) = f z := by
  have h := sp_update_dist_le hf_sp z i (f z)
  rw [_root_.dist_self] at h
  exact dist_eq_zero.mp (le_antisymm h dist_nonneg)

private lemma vertex_mem_subtree_removeBranch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {S : Finset V} {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w) :
    (vertex c : MetricGraph W) ∈ subtree W (removeBranch W S c w) :=
  vertex_mem_subtree W ((mem_removeBranch_iff hT hadj).mpr ⟨hc, .refl c⟩)

private lemma mem_subtree_removeBranch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {S : Finset V} (hS : IsSubtreeVertexSet W S) {c w : V}
    (hc : c ∈ S) (hadj : W.graph.Adj c w) {u : MetricGraph W} :
    u ∈ subtree W (removeBranch W S c w) ↔
      u ∈ subtree W S ∧ u ∉ branch (vertex c : MetricGraph W) (vertex w) := by
  rw [subtree_removeBranch hT hS hc hadj]
  rfl

private lemma mem_subtree_removeBranch_of_disjoint {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) {S : Finset V} (hS : IsSubtreeVertexSet W S) {c w₁ w₂ : V}
    (hc : c ∈ S) (hadj₁ : W.graph.Adj c w₁) (hadj₂ : W.graph.Adj c w₂) (hne : w₁ ≠ w₂)
    {u : MetricGraph W} (huS : u ∈ subtree W S)
    (huB : u ∈ branch (vertex c : MetricGraph W) (vertex w₁)) :
    u ∈ subtree W (removeBranch W S c w₂) :=
  (mem_subtree_removeBranch hT hS hc hadj₂).mpr
    ⟨huS, fun h => Set.disjoint_left.mp
      (disjoint_branch_vertex_of_adj hT hadj₁ hadj₂ hne) huB h⟩

private lemma card_filter_update_branch_erase {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (P : α → Prop) [DecidablePred P] (z : ι → α) {j : ι} {w : α}
    (hj : P (z j)) (hw : ¬ P w) :
    (Finset.univ.filter fun i => P (Function.update z j w i)).card =
      (Finset.univ.filter fun i => P (z i)).card - 1 := by
  have hsub : Finset.univ.filter (fun i => P (Function.update z j w i)) =
      (Finset.univ.filter fun i => P (z i)).erase j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hi : i = j
    · subst hi; simp [hw]
    · simp [hi]
  rw [hsub, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)]

private lemma isClosed_insert_branch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) (y q : MetricGraph W) :
    IsClosed (insert y (branch y q)) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro w₀ hw₀
  have hw₀_ne : w₀ ≠ y := fun h => hw₀ (Or.inl h)
  have hw₀_nb : w₀ ∉ branch y q := fun h => hw₀ (Or.inr h)
  refine ⟨dist y w₀, dist_pos.mpr hw₀_ne.symm, fun w hw_lt => ?_⟩
  rw [Metric.mem_ball] at hw_lt
  rintro (rfl | hw_mem)
  · exact lt_irrefl _ hw_lt
  · rw [← branch_eq_of_mem hT hw_mem] at hw₀_nb
    simp only [branch, Set.mem_ofPred_eq, Classical.not_not, mem_interval_iff] at hw₀_nb
    linarith [dist_nonneg (x := w) (y := y), dist_comm w w₀]

private lemma isConvex_insert_branch {V : Type*} [Finite V] {W : WeightedGraph V}
    (hT : W.graph.IsTree) (y q : MetricGraph W) :
    IsConvex (insert y (branch y q)) := by
  intro a b ha hb z hz
  by_cases hzy : z = y
  · exact Or.inl hzy
  · refine Or.inr ?_
    rcases ha with ha_eq | ha_b <;> rcases hb with hb_eq | hb_b
    · rw [ha_eq, hb_eq, interval_eq_singleton_self] at hz; exact absurd hz hzy
    · rw [ha_eq] at hz; exact mem_branch_of_mem_interval hT hb_b hz hzy
    · rw [hb_eq] at hz; exact mem_branch_of_mem_interval hT ha_b (interval_comm a y ▸ hz) hzy
    · by_contra hz_nb
      have hne : branch y q ≠ branch y z := fun heq => hz_nb (heq ▸ mem_branch_self hzy)
      have hdisj := branch_disjoint_of_ne hT hne
      have hcv : z ∈ (branch y z)ᶜ := isConvex_compl_branch hT y z
        (Set.disjoint_left.mp hdisj ha_b) (Set.disjoint_left.mp hdisj hb_b) hz
      exact hcv (mem_branch_self hzy)

end Helpers

section TreeEMVS

/-- An **extended median voter scheme** (`TreeEMVS`) on a finite tree metric graph `MetricGraph W`
for agents `ι`, represented by a monotone family of winning coalitions `win y q` for each
direction `branch y q` (`q ≠ y`) satisfying branch invariance, nesting, pairwise duality,
disjoint-branch exclusivity, and interior openness.

This adapts the definition of [SchummerVohra2002] (January 2001 author preprint, Section 3,
pp. 9–15), which uses a consistent family of generalized median voter schemes, one on each path
`[x, z]` between leaves. Such a scheme has a point `α_S` on `[x, z]` for each coalition `S`, and
its outcome is the point at distance `max_S min (min_{i ∈ S} d(p_i, x), d(α_S, x))` from `x`.
The outcome thus lies strictly beyond a point `y` towards `z` exactly when some coalition `S`
with `α_S` strictly beyond `y` has all its reports strictly beyond `y`. Reading `win y z S` as
"`α_S` lies strictly beyond `y` towards `z`":

* the equilibrium `IsEquilibrium`, where no branch at `y` holds a winning coalition of reports,
  is the source's outcome, its unique critical point;
* `duality` relates the parameters read from the two ends of a path, where complementary
  coalitions exchange roles;
* `branch_eq` and `nesting` express the source's consistency condition between overlapping paths
  (p. 12), and `exclusive` rules out complementary coalitions pulling into different branches;
* `open_interior` reflects the strict inequality in "strictly beyond".

This correspondence is explanatory. The library does not prove an equivalence with the
path-based definition; `isStrategyProof_and_surjective_iff_exists_treeEMVS` characterizes
strategyproof onto rules directly in terms of `TreeEMVS`. -/
structure TreeEMVS {V : Type*} (W : WeightedGraph V) [Finite V]
    (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι] where
  /-- Winning coalition predicate `win y q S` for direction `branch y q`. -/
  win : MetricGraph W → MetricGraph W → Finset ι → Prop
  /-- Winning coalitions depend only on the branch `branch y q`. -/
  branch_eq : ∀ {y q₁ q₂ : MetricGraph W},
    q₁ ≠ y → q₂ ≠ y → branch y q₁ = branch y q₂ → win y q₁ = win y q₂
  /-- The empty coalition never wins in any direction. -/
  empty_false : ∀ {y q : MetricGraph W}, q ≠ y → ¬ win y q ∅
  /-- The grand coalition always wins in every direction. -/
  univ_true : ∀ {y q : MetricGraph W}, q ≠ y → win y q Finset.univ
  /-- Winning coalitions are upward closed under subset inclusion. -/
  mono : ∀ {y q : MetricGraph W} {S T : Finset ι},
    q ≠ y → S ⊆ T → win y q S → win y q T
  /-- Winning in a smaller branch implies winning in any containing branch. -/
  nesting : ∀ {y₁ q₁ y₂ q₂ : MetricGraph W} {S : Finset ι},
    q₁ ≠ y₁ → q₂ ≠ y₂ → branch y₂ q₂ ⊆ branch y₁ q₁ → win y₂ q₂ S → win y₁ q₁ S
  /-- Duality between opposite directions along the geodesic `interval y₁ y₂`. -/
  duality : ∀ {y₁ y₂ : MetricGraph W} {S : Finset ι},
    y₁ ≠ y₂ → ¬ win y₁ y₂ S → win y₂ y₁ Sᶜ
  /-- Complementary coalitions cannot simultaneously win along distinct branches at `y`. -/
  exclusive : ∀ {y q₁ q₂ : MetricGraph W} {S : Finset ι},
    q₁ ≠ y → q₂ ≠ y → branch y q₁ ≠ branch y q₂ → ¬ (win y q₁ S ∧ win y q₂ Sᶜ)
  /-- Openness: a winning coalition at `(y, q)` remains winning at some strictly interior point
  on `interval y q`. -/
  open_interior : ∀ {y q : MetricGraph W} {S : Finset ι},
    q ≠ y → win y q S → ∃ p ∈ interval y q, p ≠ y ∧ p ≠ q ∧ win p q S

namespace TreeEMVS

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- `y` is an equilibrium of `E` at profile `x` if no branch at `y` contains a winning
coalition of reported locations. -/
@[expose] def IsEquilibrium (E : TreeEMVS W ι) (x : ι → MetricGraph W)
    (y : MetricGraph W) : Prop :=
  ∀ q : MetricGraph W, q ≠ y →
    ∀ S : Finset ι, (∀ i, i ∈ S ↔ x i ∈ branch y q) → ¬ E.win y q S

open Classical in
private noncomputable def branchCoal (x : ι → MetricGraph W) (y q : MetricGraph W) : Finset ι :=
  Finset.univ.filter fun i => x i ∈ branch y q

omit [Nonempty ι] [DecidableEq ι] in
private lemma mem_branchCoal (x : ι → MetricGraph W) (y q : MetricGraph W) (i : ι) :
    i ∈ branchCoal x y q ↔ x i ∈ branch y q := by
  simp [branchCoal]

private lemma win_opposite_of_not_win (E : TreeEMVS W ι) (x : ι → MetricGraph W)
    {y₁ y₂ : MetricGraph W} (hne : y₁ ≠ y₂) (hnot : ¬ E.win y₁ y₂ (branchCoal x y₁ y₂)) :
    E.win y₂ y₁ (branchCoal x y₂ y₁) :=
  E.mono hne (fun i hi => (mem_branchCoal x y₂ y₁ i).mpr
    (branch_symm hne ((mem_branchCoal x y₁ y₂ i).not.mp (Finset.mem_compl.mp hi))))
    (E.duality hne hnot)

private lemma win_branchCoal_congr (E : TreeEMVS W ι) (x : ι → MetricGraph W)
    {y q₁ q₂ : MetricGraph W} (hq1 : q₁ ≠ y) (hq2 : q₂ ≠ y)
    (hbr : branch y q₁ = branch y q₂) (hw : E.win y q₁ (branchCoal x y q₁)) :
    E.win y q₂ (branchCoal x y q₂) := by
  have hS : branchCoal x y q₁ = branchCoal x y q₂ := Finset.ext fun i => by
    simp only [mem_branchCoal, hbr]
  rwa [← hS, ← E.branch_eq hq1 hq2 hbr]

private lemma branch_eq_of_win_branchCoal (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) {y q₁ q₂ : MetricGraph W} (hq1 : q₁ ≠ y) (hq2 : q₂ ≠ y)
    (hw1 : E.win y q₁ (branchCoal x y q₁)) (hw2 : E.win y q₂ (branchCoal x y q₂)) :
    branch y q₁ = branch y q₂ := by
  by_contra hne
  have hdisj := branch_disjoint_of_ne hT hne
  have hsub : branchCoal x y q₂ ⊆ (branchCoal x y q₁)ᶜ := fun i hi => by
    rw [mem_branchCoal] at hi
    rw [Finset.mem_compl, mem_branchCoal]
    exact Set.disjoint_right.mp hdisj hi
  exact E.exclusive hq1 hq2 hne ⟨hw1, E.mono hq2 hsub hw2⟩

private lemma equilibrium_unique (E : TreeEMVS W ι) {x : ι → MetricGraph W}
    {y₁ y₂ : MetricGraph W} (h₁ : E.IsEquilibrium x y₁) (h₂ : E.IsEquilibrium x y₂) :
    y₁ = y₂ := by
  by_contra hne
  exact h₂ y₁ hne _ (mem_branchCoal x y₂ y₁)
    (E.win_opposite_of_not_win x hne (h₁ y₂ (Ne.symm hne) _ (mem_branchCoal x y₁ y₂)))

/-- Stepping a tiny distance along the stem of a winning direction `(y, q)` produces a point `p`
whose backward branch toward `y` cannot win. -/
private lemma exists_not_win_toward (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) {y q : MetricGraph W} (hq : q ≠ y)
    (hwin : E.win y q (branchCoal x y q)) :
    ∃ p, p ≠ y ∧ ¬ E.win p y (branchCoal x p y) := by
  obtain ⟨v₀, hv₀_mem, hv₀_pos, _, hstem_sub, r₀, hr₀_pos, _, _⟩ := exists_stem_segment hT hq
  have hv₀_ne : v₀ ≠ y := fun h => by simp [h] at hv₀_pos
  have hbr_eq : branch y v₀ = branch y q := branch_eq_of_mem hT hv₀_mem
  have hwin_v0 : E.win y v₀ (branchCoal x y q) :=
    (E.branch_eq hv₀_ne hq hbr_eq).symm ▸ hwin
  obtain ⟨p₀, hp₀_mem, hp₀_ne_y, hp₀_ne_v, hp₀_win⟩ := E.open_interior hv₀_ne hwin_v0
  obtain ⟨δ, hδ_pos, hδ_le⟩ := exists_pos_le_dist_finset (branchCoal x y q) x y fun i hi =>
    dist_pos.mpr fun heq => notMem_branch_self y q (heq ▸ (mem_branchCoal x y q i).mp hi)
  let r : ℝ := min (min r₀ δ) (dist y p₀) / 2
  have hr_pos : 0 < r := by have := dist_pos.mpr hp₀_ne_y.symm; positivity
  have hr_le_p0 : r ≤ dist y p₀ / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hr_lt_p0 : r < dist y p₀ := by linarith [dist_pos.mpr hp₀_ne_y.symm]
  obtain ⟨p, hp_mem_p0, hp_dist, _⟩ :=
    exists_mem_interval_dist_eq y p₀ ⟨hr_pos.le, hr_lt_p0.le⟩
  have hp_ne_y : p ≠ y := fun h => by rw [h, _root_.dist_self] at hp_dist; linarith
  have hp_mem_v0 : p ∈ interval y v₀ :=
    interval_subset_of_mem hT (left_mem_interval y v₀) hp₀_mem hp_mem_p0
  have hp_ne_v0 : p ≠ v₀ := fun h => by
    have := mem_interval_iff.mp hp₀_mem
    linarith [h ▸ hp_dist, dist_nonneg (x := p₀) (y := v₀)]
  have hp0_in_pv0 : p₀ ∈ interval p v₀ := by
    rw [mem_interval_iff]
    linarith [mem_interval_iff.mp hp₀_mem, mem_interval_iff.mp hp_mem_p0,
      mem_interval_iff.mp hp_mem_v0]
  have hp_win_v0 : E.win p v₀ (branchCoal x y q) := E.nesting hp_ne_v0.symm hp₀_ne_v.symm
    (fun _ hz => branch_subset_branch_of_mem_interval hp0_in_pv0 hz) hp₀_win
  have hp_in_b : p ∈ branch y q :=
    hbr_eq ▸ mem_branch_of_mem_interval hT (mem_branch_self hv₀_ne) hp_mem_v0 hp_ne_y
  have hS_p_y : branchCoal x p y = (branchCoal x y q)ᶜ := by
    ext i
    rw [Finset.mem_compl, mem_branchCoal, mem_branchCoal]
    refine ⟨fun hi_py hi_yq => hi_py (hstem_sub (x i) hi_yq p hp_mem_v0 ?_), fun hi_not => ?_⟩
    · have : r ≤ min r₀ δ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith [hδ_le i ((mem_branchCoal x y q i).mpr hi_yq), min_le_right r₀ δ]
    · exact branch_symm hp_ne_y.symm (branch_eq_of_mem hT hp_in_b ▸ hi_not)
  have hbr_ne : branch p v₀ ≠ branch p y := fun h =>
    (h ▸ mem_branch_self hp_ne_v0.symm) hp_mem_v0
  exact ⟨p, hp_ne_y, fun hw =>
    E.exclusive hp_ne_v0.symm hp_ne_y.symm hbr_ne ⟨hp_win_v0, hS_p_y ▸ hw⟩⟩

private lemma exists_equilibrium [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : ∃ y, E.IsEquilibrium x y := by
  by_contra hnone
  have hwin_ex : ∀ y : MetricGraph W, ∃ q, q ≠ y ∧ E.win y q (branchCoal x y q) := fun y => by
    by_contra hy
    push Not at hy
    refine hnone ⟨y, fun q hqy S' hS' hwin => hy q hqy ?_⟩
    have hEq : S' = branchCoal x y q :=
      Finset.ext fun i => (hS' i).trans (mem_branchCoal x y q i).symm
    exact hEq ▸ hwin
  let qy (y : MetricGraph W) : MetricGraph W := (hwin_ex y).choose
  have hqy_ne (y : MetricGraph W) : qy y ≠ y := (hwin_ex y).choose_spec.1
  have hqy_win (y : MetricGraph W) : E.win y (qy y) (branchCoal x y (qy y)) :=
    (hwin_ex y).choose_spec.2
  let M (y : MetricGraph W) : Set (MetricGraph W) := insert y (branch y (qy y))
  have hpair : ∀ y₁ y₂, (M y₁ ∩ M y₂).Nonempty := fun y₁ y₂ => by
    by_cases h12 : y₁ = y₂
    · exact ⟨y₁, Or.inl rfl, h12 ▸ Or.inl rfl⟩
    · by_cases hb1 : branch y₁ (qy y₁) = branch y₁ y₂
      · exact ⟨y₂, Or.inr (hb1 ▸ mem_branch_self (Ne.symm h12)), Or.inl rfl⟩
      · have hnot : ¬ E.win y₁ y₂ (branchCoal x y₁ y₂) := fun hw =>
          hb1 (E.branch_eq_of_win_branchCoal hT x (hqy_ne y₁) (Ne.symm h12) (hqy_win y₁) hw)
        have hb2 := E.branch_eq_of_win_branchCoal hT x (hqy_ne y₂) h12 (hqy_win y₂)
          (E.win_opposite_of_not_win x h12 hnot)
        exact ⟨y₁, Or.inl rfl, Or.inr (hb2 ▸ mem_branch_self h12)⟩
  have hne_inter : (⋂ y, M y).Nonempty := by
    by_contra hemp
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subfamily_closed M
      (fun y => isClosed_insert_branch hT y (qy y))
      (by simp [Set.not_nonempty_iff_eq_empty.mp hemp])
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · exact Set.disjoint_left.mp hF (Set.mem_univ (vertex (Classical.arbitrary V))) (by simp)
    · obtain ⟨z, hz⟩ := helly_theorem hT hFne
        (fun y _ => isConvex_insert_branch hT y (qy y)) fun y₁ _ y₂ _ => hpair y₁ y₂
      exact Set.disjoint_left.mp hF (Set.mem_univ z) hz
  obtain ⟨yStar, hyStar⟩ := hne_inter
  obtain ⟨p, hp_ne, hp_not⟩ :=
    E.exists_not_win_toward hT x (hqy_ne yStar) (hqy_win yStar)
  rcases Set.mem_iInter.mp hyStar p with rfl | hy_br
  · exact hp_ne rfl
  · exact hp_not (E.win_branchCoal_congr x (hqy_ne p) hp_ne.symm
      (branch_eq_of_mem hT hy_br).symm (hqy_win p))

/-- Every `TreeEMVS` admits a unique equilibrium for every agent profile. -/
theorem existsUnique_equilibrium [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : ∃! y, E.IsEquilibrium x y := by
  obtain ⟨y, hy⟩ := E.exists_equilibrium hT x
  exact ⟨y, hy, fun y' hy' => E.equilibrium_unique hy' hy⟩

/-- Evaluates a `TreeEMVS` on profile `x` by returning its unique equilibrium location. -/
noncomputable def eval [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) : MetricGraph W :=
  (E.existsUnique_equilibrium hT x).choose

theorem eval_eq_iff [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (x : ι → MetricGraph W) (y : MetricGraph W) :
    E.eval hT x = y ↔ E.IsEquilibrium x y := by
  have hspec := (E.existsUnique_equilibrium hT x).choose_spec
  exact ⟨fun h => h ▸ hspec.1, fun hy => (hspec.2 y hy).symm⟩

theorem eval_const [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι)
    (y : MetricGraph W) : E.eval hT (fun _ => y) = y := by
  rw [E.eval_eq_iff hT]
  intro q hq S hS
  have hS_emp : S = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi => notMem_branch_self y q ((hS i).mp hi)
  exact hS_emp ▸ E.empty_false hq

theorem eval_surjective [Nonempty V] (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    Function.Surjective (E.eval hT) :=
  fun y => ⟨fun _ => y, E.eval_const hT y⟩

/-- Every `TreeEMVS` evaluates to a strongly group-strategyproof mechanism. -/
theorem eval_isGroupStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    (Mechanism.deterministic (E.eval hT)).IsGroupStrategyProof := by
  rw [Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, i₀, _, hlt⟩
  let y := E.eval hT x
  let y' := E.eval hT (A.piecewise z x)
  have hne : y ≠ y' := fun heq => hlt.ne (by simp [y, y', heq])
  have hA_sub : ∀ i ∈ A, x i ∈ branch y y' := fun i hi => by
    by_contra hnot
    simp only [branch, Set.mem_ofPred_eq, Classical.not_not, mem_interval_iff] at hnot
    linarith [hle i hi, dist_pos.mpr hne, dist_comm y y', dist_comm (x i) y, dist_comm (x i) y']
  have hnot : ¬ E.win y y' (branchCoal x y y') :=
    ((E.eval_eq_iff hT x y).mp rfl) y' hne.symm _ (mem_branchCoal x y y')
  have hsub : (branchCoal x y y')ᶜ ⊆ branchCoal (A.piecewise z x) y' y := fun i hi => by
    rw [Finset.mem_compl, mem_branchCoal] at hi
    rw [mem_branchCoal, Finset.piecewise_eq_of_notMem _ _ _ fun hA => hi (hA_sub i hA)]
    exact branch_symm hne hi
  exact ((E.eval_eq_iff hT _ y').mp rfl) y hne _ (mem_branchCoal _ y' y)
    (E.mono hne hsub (E.duality hne hnot))

theorem eval_isStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (E : TreeEMVS W ι) :
    (Mechanism.deterministic (E.eval hT)).IsStrategyProof :=
  (E.eval_isGroupStrategyProof hT).isStrategyProof

end TreeEMVS

end TreeEMVS

section Range

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Finite ι] [DecidableEq ι]

private lemma pareto_branch [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    (x : ι → MetricGraph W) {q : MetricGraph W} (hq : q ≠ f x) :
    ¬ ∀ i, x i ∈ branch (f x) q := by
  let _ := Fintype.ofFinite ι
  intro hall
  let y := f x
  obtain ⟨v₀, hv₀_mem, _, _, hstem_sub, r₀, hr₀_pos, hr₀_le, hball⟩ := exists_stem_segment hT hq
  obtain ⟨dmin, hdmin_pos, hdmin_le⟩ :=
    exists_pos_le_dist_finset Finset.univ x y fun i _ =>
      dist_pos.mpr fun h => notMem_branch_self y q (by simpa only [← h] using hall i)
  let r : ℝ := min r₀ (dmin / 3)
  have hr_pos : 0 < r := lt_min hr₀_pos (by positivity)
  have hr_le_r0 : r ≤ r₀ := min_le_left _ _
  obtain ⟨p, hp_mem, hp_dist, _⟩ :=
    exists_mem_interval_dist_eq y v₀ ⟨hr_pos.le, hr_le_r0.trans hr₀_le⟩
  have hp_ne_y : p ≠ y := fun h => by rw [h, _root_.dist_self] at hp_dist; linarith
  have hfp : f (fun _ => p) = y := by
    refine Function.update_induction (P := fun z => f z = y) (y := fun _ => p) rfl ?_
    intro z _ hfz i₀ hi₀_eq _
    let z' := Function.update z i₀ p
    have hle_p : dist p (f z') ≤ dist y p := by
      simpa only [_root_.dist_comm, hfz] using sp_update_dist_le hf_sp z i₀ p
    have hball_z' := hball p hp_mem (hp_dist.symm ▸ hr_pos) (hp_dist.symm ▸ hr_le_r0) (f z') hle_p
    have hfz_le_xi : dist y (f z') ≤ dist y (x i₀) := by
      have : r ≤ dmin / 3 := min_le_right _ _
      linarith [hball_z'.2, hdmin_le i₀ (Finset.mem_univ i₀)]
    have hfzp_mem := hstem_sub (x i₀) (hall i₀) (f z') hball_z'.1 hfz_le_xi
    have hfz_sp := sp_dist_le hf_sp z i₀ p
    rw [hfz, hi₀_eq] at hfz_sp
    have hd0 : dist y (f z') = 0 := by
      linarith [mem_interval_iff.mp hfzp_mem, _root_.dist_comm (x i₀) y,
        _root_.dist_comm (x i₀) (f z'), _root_.dist_comm y (f z'),
        _root_.dist_comm (f z') (x i₀), dist_nonneg (x := y) (y := f z')]
    exact (dist_eq_zero.mp hd0).symm
  exact hp_ne_y ((unanimous_of_surjective_isStrategyProof hf_sp hf_onto p).symm.trans hfp)

private lemma range_of_convex
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {K : Set (MetricGraph W)} (hK : IsConvex K) (hKc : IsClosed K) (hKn : K.Nonempty)
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ K) : f x ∈ K := by
  by_contra hnot
  let p := gate K (f x)
  have hp_ne : p ≠ f x := fun h => hnot (h ▸ hK.gate_mem hT hKc hKn (f x))
  refine pareto_branch hT hf_sp hf_onto x hp_ne fun i hmem => ?_
  have hm := mem_interval_iff.mp (hK.gate_mem_interval hT hKc (f x) (hx i))
  have hd : dist p (f x) = 0 := by
    linarith [mem_interval_iff.mp hmem, dist_comm p (x i), dist_comm p (f x), dist_comm (f x) (x i)]
  exact hp_ne (dist_eq_zero.mp hd)

private lemma range_subtree
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : IsSubtreeVertexSet W S)
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ subtree W S) : f x ∈ subtree W S :=
  range_of_convex hT hf_sp hf_onto (isConvex_subtree hT S) (isClosed_subtree W S)
    (subtree_nonempty hS.nonempty) hx

omit [Finite ι] in
private lemma exists_moulinScheme_interval [Fintype ι] [Nonempty ι]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) (a b : MetricGraph W) :
    ∃ (φ : Set.Icc (0 : ℝ) (dist a b) → MetricGraph W) (E : MoulinScheme ι 0 (dist a b)),
      Isometry φ ∧
      φ ⟨0, le_rfl, dist_nonneg⟩ = a ∧
      φ ⟨dist a b, dist_nonneg, le_rfl⟩ = b ∧
      Set.range φ = interval a b ∧
      ∀ x : ι → Set.Icc (0 : ℝ) (dist a b), f (fun i => φ (x i)) = φ (E.eval x) := by
  obtain ⟨φ, hφ, hφ0, hφd, hrange⟩ := exists_isometry_interval hT a b
  have hrange_f : ∀ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ :=
    fun x hx => hrange.symm ▸ range_of_convex hT hf_sp hf_onto (isConvex_interval hT a b)
      (isClosed_interval a b) ⟨a, left_mem_interval a b⟩ fun i => hrange ▸ hx i
  have honto_f : ∀ y ∈ Set.range φ, ∃ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range φ) ∧ f x = y :=
    fun y hy => ⟨fun _ => y, fun _ => hy, unanimous_of_surjective_isStrategyProof hf_sp hf_onto y⟩
  obtain ⟨E, hE⟩ := moulinScheme_of_isometry dist_nonneg φ hφ hf_sp hrange_f honto_f
  exact ⟨φ, E, hφ, hφ0, hφd, hrange, hE⟩

end Range

section Characterization

variable {V : Type*} [Finite V] {W : WeightedGraph V}
variable {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]

private def BranchInvOn (W : WeightedGraph V) (f : (ι → MetricGraph W) → MetricGraph W)
    (S : Finset V) : Prop :=
  ∀ ⦃y q : MetricGraph W⦄, y ∈ subtree W S → q ∈ subtree W S → q ≠ y →
    ∀ ⦃x₁ x₂ : ι → MetricGraph W⦄,
      (∀ i, x₁ i ∈ subtree W S) → (∀ i, x₂ i ∈ subtree W S) →
      (∀ i, x₁ i ∈ branch y q ↔ x₂ i ∈ branch y q) →
      (f x₁ ∈ branch y q ↔ f x₂ ∈ branch y q)

private lemma real_not_between_iff {y q w : ℝ} (hne : q ≠ y) :
    |q - y| + |y - w| ≠ |q - w| ↔ if y < q then y < w else w < y := by
  have helper : ∀ a b c : ℝ, a < b → (|b - a| + |a - c| ≠ |b - c| ↔ a < c) := fun a b c hab => by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      rw [abs_of_pos (sub_pos.mpr hab), abs_of_nonneg (sub_nonneg.mpr hc),
        abs_of_pos (by linarith)] at h
      exact h (by ring)
    · intro hac heq
      rw [abs_of_pos (sub_pos.mpr hab), abs_of_neg (sub_neg.mpr hac)] at heq
      rcases abs_cases (b - c) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> linarith
  split_ifs with hyq
  · exact helper y q w hyq
  · have h := helper (-y) (-q) (-w) (neg_lt_neg (lt_of_le_of_ne (not_lt.mp hyq) hne))
    simpa only [neg_sub_neg, abs_sub_comm, neg_lt_neg_iff] using h

private lemma branchInvOn_of_interval
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} {a b : V} (hsub : subtree W S = interval (vertex a) (vertex b)) :
    BranchInvOn W f S := by
  let _ := Fintype.ofFinite ι
  obtain ⟨φ, E, hφ, _, _, hrange, hE⟩ :=
    exists_moulinScheme_interval hT hf_sp hf_onto (vertex a) (vertex b)
  have hcoord : ∀ {u}, u ∈ subtree W S → ∃ t, φ t = u := fun hu =>
    Set.mem_range.mp (by rw [hrange, ← hsub]; exact hu)
  have hbr : ∀ {y₀ q₀ w₀ : Set.Icc (0 : ℝ) (dist (vertex a : MetricGraph W) (vertex b))},
      q₀ ≠ y₀ → (φ w₀ ∈ branch (φ y₀) (φ q₀) ↔
        if (y₀ : ℝ) < q₀ then (y₀ : ℝ) < w₀ else (w₀ : ℝ) < y₀) := by
    intro y₀ q₀ w₀ hne
    simpa only [branch, Set.mem_ofPred_eq, mem_interval_iff, hφ.dist_eq, Subtype.dist_eq,
      Real.dist_eq] using real_not_between_iff (fun h => hne (Subtype.ext h))
  intro y q hy hq hqy x₁ x₂ hx₁ hx₂ hiff
  obtain ⟨y₀, rfl⟩ := hcoord hy
  obtain ⟨q₀, rfl⟩ := hcoord hq
  have hq0_ne : q₀ ≠ y₀ := fun h => hqy (h ▸ rfl)
  let c₁ i := (hcoord (hx₁ i)).choose
  let c₂ i := (hcoord (hx₂ i)).choose
  have hc₁ i : φ (c₁ i) = x₁ i := (hcoord (hx₁ i)).choose_spec
  have hc₂ i : φ (c₂ i) = x₂ i := (hcoord (hx₂ i)).choose_spec
  have heq_p (i) : (if (y₀ : ℝ) < q₀ then (y₀ : ℝ) < c₁ i else (c₁ i : ℝ) < y₀) ↔
      (if (y₀ : ℝ) < q₀ then (y₀ : ℝ) < c₂ i else (c₂ i : ℝ) < y₀) := by
    rw [← hbr hq0_ne, ← hbr hq0_ne, hc₁ i, hc₂ i]; exact hiff i
  have h1 : x₁ = fun i => φ (c₁ i) := funext fun i => (hc₁ i).symm
  have h2 : x₂ = fun i => φ (c₂ i) := funext fun i => (hc₂ i).symm
  rw [h1, h2, hE c₁, hE c₂, hbr hq0_ne, hbr hq0_ne]
  split_ifs with hyq
  · have hS_eq : (Finset.univ.filter fun i => (c₁ i : ℝ) ≤ y₀) =
        Finset.univ.filter fun i => (c₂ i : ℝ) ≤ y₀ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← not_lt]
      exact not_congr (by simpa only [hyq, ↓reduceIte] using heq_p i)
    rw [E.lt_eval_iff c₁ y₀, E.lt_eval_iff c₂ y₀, hS_eq]
  · have hS_eq : (Finset.univ.filter fun i => (c₁ i : ℝ) < y₀) =
        Finset.univ.filter fun i => (c₂ i : ℝ) < y₀ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hyq, ↓reduceIte] using heq_p i
    rw [E.eval_lt_iff c₁ y₀, E.eval_lt_iff c₂ y₀, hS_eq]

omit [Nonempty ι] in
private lemma proj_interval_of_branchInvOn
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : IsSubtreeVertexSet W S) (hinv : BranchInvOn W f S)
    {a b : MetricGraph W} (ha : a ∈ subtree W S) (hb : b ∈ subtree W S)
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ subtree W S) :
    treeMedian hT a b (f x) = f (fun i => treeMedian hT a b (x i)) := by
  by_contra hne
  let p₁ := treeMedian hT a b (f x)
  let p₂ := f (fun i => treeMedian hT a b (x i))
  have hp₁_ab : p₁ ∈ interval a b := treeMedian_mem_xy hT a b (f x)
  have hπx_S : ∀ i, treeMedian hT a b (x i) ∈ subtree W S := fun i =>
    isConvex_subtree hT S ha hb (treeMedian_mem_xy hT a b (x i))
  have hp₂_ab : p₂ ∈ interval a b := range_of_convex hT hf_sp hf_onto (isConvex_interval hT a b)
    (isClosed_interval a b) ⟨a, left_mem_interval a b⟩ fun i => treeMedian_mem_xy hT a b (x i)
  have hmed_iff : ∀ u, u ∈ branch p₁ p₂ ↔ treeMedian hT a b u ∈ branch p₁ p₂ := fun u =>
    mem_branch_iff_of_mem_interval (treeMedian_mem_interval_of_mem hT hp₁_ab u)
      (treeMedian_mem_interval_of_mem hT hp₂_ab u)
  have hres := hinv (isConvex_subtree hT S ha hb hp₁_ab)
    (range_subtree hT hf_sp hf_onto hS hπx_S) (Ne.symm hne) hx hπx_S fun i => hmed_iff (x i)
  rw [hmed_iff (f x)] at hres
  exact notMem_branch_self p₁ p₂ (hres.mpr (mem_branch_self (Ne.symm hne)))

omit [Finite ι] [Nonempty ι] in
/-- Shifting an agent from `branch (vertex c) (vertex w₁)` to `vertex c` cannot push an interior
outcome `f z ∈ subtree W (removeBranch W S c w₁)` out of `subtree W (removeBranch W S c w₁)`. -/
private lemma update_vertex_mem_removeBranch
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {S : Finset V} (hS : IsSubtreeVertexSet W S)
    {c w₁ : V} (hc : c ∈ S) (hadj₁ : W.graph.Adj c w₁)
    {z : ι → MetricGraph W} {j : ι}
    (hj_C1 : z j ∈ branch (vertex c : MetricGraph W) (vertex w₁))
    (hy_nC1 : f z ∉ branch (vertex c : MetricGraph W) (vertex w₁))
    (hy'_S : f (Function.update z j (vertex c)) ∈ subtree W S) :
    f (Function.update z j (vertex c)) ∈ subtree W (removeBranch W S c w₁) := by
  rw [subtree_removeBranch hT hS hc hadj₁]
  refine ⟨hy'_S, fun hy'_C1 => ?_⟩
  let y := f z; let y' := f (Function.update z j (vertex c))
  have hbr_zj : branch (vertex c) (z j) = branch (vertex c) (vertex w₁) :=
    branch_eq_of_mem hT hj_C1
  have hc_int_y : (vertex c : MetricGraph W) ∈ interval (z j) y := by
    have := hy_nC1; rwa [← hbr_zj, branch, Set.mem_ofPred_eq, Classical.not_not] at this
  let b := treeMedian hT (vertex c) (z j) y'
  have hb_ne : b ≠ vertex c := fun heq => by
    have hc_int : (vertex c : MetricGraph W) ∈ interval (z j) y' := by
      have h := treeMedian_mem_yz hT (vertex c) (z j) y'
      change b ∈ interval (z j) y' at h; rwa [heq] at h
    have hdisj := branch_disjoint_of_mem_interval hT hc_int
    rw [hbr_zj, branch_eq_of_mem hT hy'_C1] at hdisj
    exact Set.disjoint_left.mp hdisj hj_C1 hj_C1
  have hb_pos : 0 < dist (vertex c : MetricGraph W) b := dist_pos.mpr hb_ne.symm
  have hsp_j : dist y (z j) ≤ dist y' (z j) := sp_dist_le hf_sp z j (vertex c)
  have hsp_c : dist y' (vertex c) ≤ dist y (vertex c) := sp_update_dist_le hf_sp z j (vertex c)
  have := mem_interval_iff.mp (treeMedian_mem_xy hT (vertex c) (z j) y')
  have := mem_interval_iff.mp (interval_comm y' (vertex c) ▸
    treeMedian_mem_zx hT (vertex c) (z j) y')
  have := mem_interval_iff.mp (treeMedian_mem_yz hT (vertex c) (z j) y')
  have := mem_interval_iff.mp hc_int_y
  linarith [_root_.dist_comm (z j) b, _root_.dist_comm b (vertex c),
    _root_.dist_comm (vertex c) (z j), _root_.dist_comm y (z j),
    _root_.dist_comm y' (z j), _root_.dist_comm y' (vertex c), _root_.dist_comm y (vertex c)]

/-- Contradiction step of `proj_removeBranch_of_branchInvOn` when `f z` lies inside the reduced
subtree `subtree W (removeBranch W S c w₁)`. -/
private lemma proj_removeBranch_step_in
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : IsSubtreeVertexSet W S)
    {c w₁ : V} (hc : c ∈ S) (hadj₁ : W.graph.Adj c w₁)
    (hinv₁ : BranchInvOn W f (removeBranch W S c w₁))
    {z : ι → MetricGraph W} {j : ι}
    (hj_C1 : z j ∈ branch (vertex c : MetricGraph W) (vertex w₁))
    (hy_sub : f z ∈ subtree W (removeBranch W S c w₁))
    (hih_z' : gate (subtree W (removeBranch W S c w₁)) (f (Function.update z j (vertex c))) =
      f (fun i => gate (subtree W (removeBranch W S c w₁)) (Function.update z j (vertex c) i)))
    (hih_zy : gate (subtree W (removeBranch W S c w₁)) (f (Function.update z j (f z))) =
      f (fun i => gate (subtree W (removeBranch W S c w₁)) (Function.update z j (f z) i)))
    (hy'_S : f (Function.update z j (vertex c)) ∈ subtree W S)
    (hne_res : gate (subtree W (removeBranch W S c w₁)) (f z) ≠
      gate (subtree W (removeBranch W S c w₁)) (f (Function.update z j (vertex c)))) :
    False := by
  let _ := Fintype.ofFinite ι
  let S₁ := removeBranch W S c w₁
  let π₁ := gate (subtree W S₁)
  let y := f z; let z' := Function.update z j (vertex c); let y' := f z'
  let z_y := Function.update z j y
  have hS₁ := hS.removeBranch hT hc hadj₁
  have hc₁ : (vertex c : MetricGraph W) ∈ subtree W S₁ :=
    vertex_mem_subtree_removeBranch hT hc hadj₁
  have hy_nC1 : y ∉ branch (vertex c) (vertex w₁) :=
    ((mem_subtree_removeBranch hT hS hc hadj₁).mp hy_sub).2
  have hy'_sub : y' ∈ subtree W S₁ :=
    update_vertex_mem_removeBranch hT hf_sp hS hc hadj₁ hj_C1 hy_nC1 hy'_S
  have hy_π : π₁ y = y := gate_eq_self hy_sub
  have hy'_π : π₁ y' = y' := gate_eq_self hy'_sub
  replace hne_res : y ≠ y' := fun h => hne_res (hy_π.trans (h.trans hy'_π.symm))
  have hc_int_y : (vertex c : MetricGraph W) ∈ interval (z j) y := by
    have := hy_nC1
    rwa [← branch_eq_of_mem hT hj_C1, branch, Set.mem_ofPred_eq, Classical.not_not] at this
  have hd_eq : dist (vertex c : MetricGraph W) y = dist (vertex c : MetricGraph W) y' := by
    linarith [sp_dist_le hf_sp z j (vertex c), sp_update_dist_le hf_sp z j (vertex c),
      mem_interval_iff.mp hc_int_y, dist_triangle (z j) (vertex c) y',
      _root_.dist_comm y (z j), _root_.dist_comm y' (z j),
      _root_.dist_comm y (vertex c), _root_.dist_comm y' (vertex c),
      _root_.dist_comm (z j) (vertex c)]
  have hih_zy' : y = f (fun i => π₁ (z_y i)) := by
    have hzy_eq : f z_y = y := sp_update_self_outcome hf_sp z j
    exact hy_π.symm.trans (hzy_eq ▸ hih_zy)
  have hih_z'' : y' = f (fun i => π₁ (z' i)) := hy'_π.symm.trans hih_z'
  have hm_ne_y' : treeMedian hT (vertex c) y' y ≠ y' := fun h => by
    have hmem : y' ∈ interval (vertex c) y := by
      have hm := interval_comm y (vertex c) ▸ treeMedian_mem_zx hT (vertex c) y' y
      rwa [h] at hm
    exact hne_res (dist_eq_zero.mp (by linarith [mem_interval_iff.mp hmem])).symm
  obtain ⟨φ, E_P, hφ, hφ0, hφd, hrange, hE_P⟩ :=
    exists_moulinScheme_interval hT hf_sp hf_onto (vertex c) y'
  obtain ⟨m₀, hm₀_eq⟩ := Set.mem_range.mp (hrange.symm ▸ treeMedian_mem_xy hT (vertex c) y' y)
  have hmed_base (i) := Set.mem_range.mp
    (hrange.symm ▸ treeMedian_mem_xy hT (vertex c) y' (π₁ (z' i)))
  let b_base : ι → Set.Icc (0 : ℝ) (dist (vertex c : MetricGraph W) y') :=
    fun i => (hmed_base i).choose
  let c₀ : Set.Icc (0 : ℝ) (dist (vertex c : MetricGraph W) y') := ⟨0, le_rfl, dist_nonneg⟩
  have hπ_S (u : ι → MetricGraph W) (i) : π₁ (u i) ∈ subtree W S₁ :=
    gate_subtree_mem hT hS₁.nonempty (u i)
  have hproj_z' := proj_interval_of_branchInvOn hT hf_sp hf_onto hS₁ hinv₁ hc₁ hy'_sub (hπ_S z')
  have hproj_zy := proj_interval_of_branchInvOn hT hf_sp hf_onto hS₁ hinv₁ hc₁ hy'_sub (hπ_S z_y)
  have hφ_z' : (fun i => φ (Function.update b_base j c₀ i)) =
      fun i => treeMedian hT (vertex c) y' (π₁ (z' i)) := funext fun i => by
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self, c₀, hφ0, z', π₁, gate_eq_self hc₁]
      exact eq_treeMedian_of_mem hT (left_mem_interval _ _) (right_mem_interval _ _)
        (left_mem_interval _ _)
    · simp only [Function.update_of_ne hi, b_base, (hmed_base i).choose_spec]
  have hφ_zy : (fun i => φ (Function.update b_base j m₀ i)) =
      fun i => treeMedian hT (vertex c) y' (π₁ (z_y i)) := funext fun i => by
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self, hm₀_eq, z_y, hy_π]
    · rw [Function.update_of_ne hi]
      exact ((hmed_base i).choose_spec).trans (by simp only [z_y, z', Function.update_of_ne hi])
  have h0_eq : E_P.eval (Function.update b_base j c₀) =
      ⟨dist (vertex c : MetricGraph W) y', dist_nonneg, le_rfl⟩ := hφ.injective <| by
    rw [← hE_P, hφ_z', ← hproj_z', ← hih_z'', hφd]
    exact (eq_treeMedian_of_mem hT (right_mem_interval _ _) (left_mem_interval _ _)
      (left_mem_interval _ _)).symm
  have hm_eq : E_P.eval (Function.update b_base j m₀) = m₀ := hφ.injective <| by
    rw [← hE_P, hφ_zy, ← hproj_zy, ← hih_zy', hm₀_eq]
  have hmono : (E_P.eval (Function.update b_base j c₀) : ℝ) ≤
      E_P.eval (Function.update b_base j m₀) := E_P.eval_mono fun i => by
    by_cases hi : i = j
    · subst hi; simp only [Function.update_self, c₀]; exact m₀.2.1
    · simp only [Function.update_of_ne hi, le_rfl]
  rw [h0_eq, hm_eq] at hmono
  exact hm_ne_y' (hm₀_eq.symm.trans (by
    rw [show m₀ = ⟨dist (vertex c : MetricGraph W) y', dist_nonneg, le_rfl⟩ from
      Subtype.ext (le_antisymm m₀.2.2 hmono), hφd]))

omit [Finite ι] [Nonempty ι] in
open Classical in
/-- Pushing-loop lemma for the exterior case (`f z ∈ branch (vertex c) (vertex w₁)`) of
`proj_removeBranch_of_branchInvOn`: inductively moves agents sitting in `subtree W S₁ \ C₂` to
`y = f u`, preserving the outcome and staying inside `subtree W S₃`. -/
private lemma proj_removeBranch_push_loop
    [Fintype ι] [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : IsSubtreeVertexSet W S)
    {c w₁ w₂ w₃ : V} (hc : c ∈ S) (hw₂ : w₂ ∈ S)
    (hadj₁ : W.graph.Adj c w₁) (hadj₂ : W.graph.Adj c w₂) (hadj₃ : W.graph.Adj c w₃)
    (hw₁₂ : w₁ ≠ w₂) (hw₁₃ : w₁ ≠ w₃) (hw₂₃ : w₂ ≠ w₃)
    (hinv₁ : BranchInvOn W f (removeBranch W S c w₁))
    (hinv₃ : BranchInvOn W f (removeBranch W S c w₃))
    {m : ℕ} {y : MetricGraph W} (hy_S : y ∈ subtree W S)
    (hy_C1 : y ∈ branch (vertex c : MetricGraph W) (vertex w₁))
    (ih : ∀ u : ι → MetricGraph W, (∀ i, u i ∈ subtree W S) →
      (Finset.univ.filter fun i =>
        u i ∈ branch (vertex c : MetricGraph W) (vertex w₁)).card < m →
      gate (subtree W (removeBranch W S c w₁)) (f u) =
        f (fun i => gate (subtree W (removeBranch W S c w₁)) (u i))) :
    ∀ (k : ℕ) (Y : Finset ι) (u : ι → MetricGraph W),
      (∀ i ∈ Y, u i = y) → (∀ i, u i ∈ subtree W S) → f u = y →
      (Finset.univ.filter fun i =>
        (if i ∈ Y then vertex c else u i) ∈
          branch (vertex c : MetricGraph W) (vertex w₁)).card < m →
      f (fun i => gate (subtree W (removeBranch W S c w₁))
        (if i ∈ Y then vertex c else u i)) ∈
        branch (vertex c : MetricGraph W) (vertex w₂) →
      (Finset.univ.filter fun i => i ∉ Y ∧
        u i ∈ subtree W (removeBranch W S c w₁) \
          branch (vertex c : MetricGraph W) (vertex w₂)).card = k →
      False := by
  classical
  let S₁ := removeBranch W S c w₁
  let S₃ := removeBranch W S c w₃
  let π₁ := gate (subtree W S₁)
  let C₁ := branch (vertex c : MetricGraph W) (vertex w₁)
  let C₂ := branch (vertex c : MetricGraph W) (vertex w₂)
  have hS₁ := hS.removeBranch hT hc hadj₁
  have hc_S₁ := vertex_mem_subtree_removeBranch hT hc hadj₁
  have hc_S₃ := vertex_mem_subtree_removeBranch hT hc hadj₃
  have hw₂_ne : (vertex w₂ : MetricGraph W) ≠ vertex c :=
    fun h => hadj₂.ne (vertex_injective (W := W) h.symm)
  have hw₂_S₁ : (vertex w₂ : MetricGraph W) ∈ subtree W S₁ :=
    mem_subtree_removeBranch_of_disjoint hT hS hc hadj₂ hadj₁ hw₁₂.symm
      (vertex_mem_subtree W hw₂) (mem_branch_self hw₂_ne)
  have hw₂_S₃ : (vertex w₂ : MetricGraph W) ∈ subtree W S₃ :=
    mem_subtree_removeBranch_of_disjoint hT hS hc hadj₂ hadj₃ hw₂₃
      (vertex_mem_subtree W hw₂) (mem_branch_self hw₂_ne)
  intro k
  induction k with
  | zero =>
    intro Y u hYu hu_S hfu huv_card hπuv_C2 hk0
    let u_v := fun i => if i ∈ Y then (vertex c : MetricGraph W) else u i
    have huv_S : ∀ i, u_v i ∈ subtree W S := fun i => by
      dsimp only [u_v]; split_ifs
      · exact vertex_mem_subtree W hc
      · exact hu_S i
    have hπ_eq := ih u_v huv_S huv_card
    have hfuv_nC1 : f u_v ∉ C₁ := fun hmem =>
      notMem_branch_self (vertex c) (vertex w₂)
        (by rw [← hπ_eq, gate_subtree_removeBranch hT hS hc hadj₁ hmem] at hπuv_C2; exact hπuv_C2)
    have hfuv_C2 : f u_v ∈ C₂ := by
      rwa [← hπ_eq, gate_eq_self ((mem_subtree_removeBranch hT hS hc hadj₁).mpr
        ⟨range_subtree hT hf_sp hf_onto hS huv_S, hfuv_nC1⟩)] at hπuv_C2
    have hemp := Finset.card_eq_zero.mp hk0
    have hu_S3 : ∀ i, u i ∈ subtree W S₃ := fun i => by
      by_cases hiC1 : u i ∈ C₁
      · exact mem_subtree_removeBranch_of_disjoint hT hS hc hadj₁ hadj₃ hw₁₃ (hu_S i) hiC1
      · have hiY : i ∉ Y := fun h => hiC1 (hYu i h ▸ hy_C1)
        have hi_S₁ : u i ∈ subtree W S₁ :=
          (mem_subtree_removeBranch hT hS hc hadj₁).mpr ⟨hu_S i, hiC1⟩
        have hi_C2 : u i ∈ C₂ := by
          by_contra hi_nC2
          exact Finset.notMem_empty i (hemp ▸ Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, hiY, hi_S₁, hi_nC2⟩)
        exact mem_subtree_removeBranch_of_disjoint hT hS hc hadj₂ hadj₃ hw₂₃ (hu_S i) hi_C2
    have huv_S3 : ∀ i, u_v i ∈ subtree W S₃ := fun i => by
      dsimp only [u_v]; split_ifs
      · exact hc_S₃
      · exact hu_S3 i
    have hy_nC2 : y ∉ C₂ := Set.disjoint_left.mp
      (disjoint_branch_vertex_of_adj hT hadj₁ hadj₂ hw₁₂) hy_C1
    have heq_C2 := hinv₃ hc_S₃ hw₂_S₃ hw₂_ne hu_S3 huv_S3 fun i => by
      dsimp only [u_v]; split_ifs with hiY
      · rw [hYu i hiY]; simp [C₂, hy_nC2]
      · rfl
    exact hy_nC2 (hfu ▸ heq_C2.mpr hfuv_C2)
  | succ k ihk =>
    intro Y u hYu hu_S hfu huv_card hπuv_C2 hk_succ
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by rw [hk_succ]; exact Nat.succ_pos k)
    obtain ⟨hi₀_nY, hi₀_S1, hi₀_nC2⟩ := (Finset.mem_filter.mp hi₀).2
    let Y' := insert i₀ Y
    let u' := Function.update u i₀ y
    let u_v := fun i => if i ∈ Y then (vertex c : MetricGraph W) else u i
    let u'_v := fun i => if i ∈ Y' then (vertex c : MetricGraph W) else u' i
    have hu'_v_eq : u'_v = Function.update u_v i₀ (vertex c) := funext fun i => by
      by_cases hi : i = i₀
      · subst hi; simp [u'_v, Y']
      · simp [u'_v, u_v, u', Y', hi]
    have hi₀_nC1 : u i₀ ∉ C₁ := ((mem_subtree_removeBranch hT hS hc hadj₁).mp hi₀_S1).2
    have hcard' : (Finset.univ.filter fun i => u'_v i ∈ C₁).card < m := by
      suffices h : (Finset.univ.filter fun i => u'_v i ∈ C₁) =
          Finset.univ.filter fun i => u_v i ∈ C₁ from h ▸ huv_card
      ext i; rw [hu'_v_eq]; by_cases hi : i = i₀
      · subst hi; simp [u_v, hi₀_nY, hi₀_nC1, C₁]
      · simp [hi]
    have hπu'v_C2 : f (fun i => π₁ (u'_v i)) ∈ C₂ := (hinv₁ hc_S₁ hw₂_S₁ hw₂_ne
      (fun i => gate_subtree_mem hT hS₁.nonempty (u_v i))
      (fun i => gate_subtree_mem hT hS₁.nonempty (u'_v i)) fun i => by
        by_cases hi : i = i₀
        · subst hi; rw [hu'_v_eq, Function.update_self]
          have : u_v i = u i := ite_eq_right_iff.mpr fun h => absurd h hi₀_nY
          rw [this, gate_eq_self hc_S₁, gate_eq_self hi₀_S1]
          simp [hi₀_nC2]
        · simp [hu'_v_eq, hi]).mp hπuv_C2
    have hsub_opp : (Finset.univ.filter fun i => i ∉ Y' ∧ u' i ∈ subtree W S₁ \ C₂) =
        (Finset.univ.filter fun i => i ∉ Y ∧ u i ∈ subtree W S₁ \ C₂).erase i₀ := by
      ext i; by_cases hi : i = i₀
      · subst hi; simp [Y']
      · simp [Y', u', hi]
    refine ihk Y' u' (fun i hi => by
      rcases Finset.mem_insert.mp hi with rfl | hiY
      · simp [u']
      · have hne : i ≠ i₀ := fun h => hi₀_nY (h ▸ hiY)
        simp only [u', Function.update_of_ne hne, hYu i hiY])
      (fun i => by by_cases hi : i = i₀ <;> simp [u', hi, hy_S, hu_S])
      (by change f (Function.update u i₀ y) = y; rw [← hfu, sp_update_self_outcome hf_sp])
      hcard' hπu'v_C2
      (by rw [hsub_opp, Finset.card_erase_of_mem hi₀, hk_succ]; simp)

private lemma proj_removeBranch_of_branchInvOn
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {S : Finset V} (hS : IsSubtreeVertexSet W S)
    {c w₁ : V} (hc : c ∈ S) (hw₁ : w₁ ∈ S) (hadj₁ : W.graph.Adj c w₁)
    (hdeg3 : ∃ T : Finset V, 3 ≤ T.card ∧ ∀ u ∈ T, u ∈ S ∧ W.graph.Adj c u)
    (hinv_rem : ∀ w ∈ S, W.graph.Adj c w → BranchInvOn W f (removeBranch W S c w))
    {x : ι → MetricGraph W} (hx : ∀ i, x i ∈ subtree W S) :
    let π₁ := gate (subtree W (removeBranch W S c w₁))
    π₁ (f x) = f (fun i => π₁ (x i)) := by
  classical
  let _ := Fintype.ofFinite ι
  let S₁ := removeBranch W S c w₁
  let π₁ := gate (subtree W S₁)
  let C₁ := branch (vertex c : MetricGraph W) (vertex w₁)
  have hS₁ := hS.removeBranch hT hc hadj₁
  have hc₁ : (vertex c : MetricGraph W) ∈ subtree W S₁ :=
    vertex_mem_subtree_removeBranch hT hc hadj₁
  suffices h : ∀ (m : ℕ) (z : ι → MetricGraph W), (∀ i, z i ∈ subtree W S) →
      (Finset.univ.filter fun i => z i ∈ C₁).card = m →
      π₁ (f z) = f (fun i => π₁ (z i)) from h _ x hx rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro z hz hcard
    rcases m.eq_zero_or_pos with rfl | hm_pos
    · have hz₁ : ∀ i, z i ∈ subtree W S₁ := fun i =>
        (mem_subtree_removeBranch hT hS hc hadj₁).mpr ⟨hz i, fun hmem =>
          Finset.notMem_empty i ((Finset.card_eq_zero.mp hcard) ▸
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩)⟩
      have hπz : (fun i => π₁ (z i)) = z := funext fun i => gate_eq_self (hz₁ i)
      rw [hπz]
      exact gate_eq_self (range_subtree hT hf_sp hf_onto hS₁ hz₁)
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hcard ▸ hm_pos)
      have hj_C1 : z j ∈ C₁ := (Finset.mem_filter.mp hj).2
      let z' := Function.update z j (vertex c)
      have hz'_S : ∀ i, z' i ∈ subtree W S := fun i => by
        by_cases hi : i = j <;> simp [z', hi, vertex_mem_subtree W hc, hz]
      have hcard' : (Finset.univ.filter fun i => z' i ∈ C₁).card = m - 1 := by
        simpa only [hcard] using card_filter_update_branch_erase (· ∈ C₁) z hj_C1
          (notMem_branch_self _ _)
      have hπ_upd : (fun i => π₁ (z' i)) = fun i => π₁ (z i) := funext fun i => by
        by_cases hi : i = j
        · subst hi; simp only [z', Function.update_self, π₁]
          rw [gate_eq_self hc₁, gate_subtree_removeBranch hT hS hc hadj₁ hj_C1]
        · simp [z', hi]
      have hih' : π₁ (f z') = f (fun i => π₁ (z i)) :=
        hπ_upd ▸ ih (m - 1) (Nat.sub_lt hm_pos zero_lt_one) z' hz'_S hcard'
      by_contra hne_res
      rw [← hih'] at hne_res
      have hy_S : f z ∈ subtree W S := range_subtree hT hf_sp hf_onto hS hz
      let z_y := Function.update z j (f z)
      have hz_y_S : ∀ i, z_y i ∈ subtree W S := fun i => by
        by_cases hi : i = j <;> simp [z_y, hi, hy_S, hz]
      by_cases hy_sub : f z ∈ subtree W S₁
      · have hcard_y : (Finset.univ.filter fun i => z_y i ∈ C₁).card = m - 1 := by
          simpa only [hcard] using card_filter_update_branch_erase (· ∈ C₁) z hj_C1
            ((mem_subtree_removeBranch hT hS hc hadj₁).mp hy_sub).2
        exact proj_removeBranch_step_in hT hf_sp hf_onto hS hc hadj₁ (hinv_rem w₁ hw₁ hadj₁)
          hj_C1 hy_sub (hπ_upd.symm ▸ hih')
          (ih (m - 1) (Nat.sub_lt hm_pos zero_lt_one) z_y hz_y_S hcard_y)
          (range_subtree hT hf_sp hf_onto hS hz'_S) hne_res
      · have hy_C1 : f z ∈ C₁ := by
          rw [subtree_removeBranch hT hS hc hadj₁] at hy_sub; simpa [C₁, hy_S] using hy_sub
        have hπ_y : π₁ (f z) = vertex c := gate_subtree_removeBranch hT hS hc hadj₁ hy_C1
        rw [hπ_y] at hne_res
        have hy'_S1 := (mem_subtree_removeBranch hT hS hc hadj₁).mp
          (gate_subtree_mem hT hS₁.nonempty (f z'))
        obtain ⟨w₂, hw₂, hadj₂, hπy'_br⟩ :=
          exists_adj_mem_branch_of_mem_subtree hT hS hc hy'_S1.1 (Ne.symm hne_res)
        have hw₁₂ : w₁ ≠ w₂ := fun h => hy'_S1.2 (h ▸ hπy'_br)
        obtain ⟨T, hT3, hT_mem⟩ := hdeg3
        obtain ⟨w₃, hw₃⟩ : ((T.erase w₁).erase w₂).Nonempty := Finset.card_pos.mp (by
          have := Finset.pred_card_le_card_erase (s := T) (a := w₁)
          have := Finset.pred_card_le_card_erase (s := T.erase w₁) (a := w₂)
          omega)
        obtain ⟨hw₃_ne2, hw₃_ne1, hw₃_T⟩ : w₃ ≠ w₂ ∧ w₃ ≠ w₁ ∧ w₃ ∈ T := by
          simpa only [Finset.mem_erase] using hw₃
        obtain ⟨hw₃, hadj₃⟩ := hT_mem w₃ hw₃_T
        have hif_eq : ∀ i, (if i ∈ ({j} : Finset ι) then vertex c else z_y i) = z' i := fun i => by
          by_cases hi : i = j <;> simp [z', z_y, hi]
        refine proj_removeBranch_push_loop hT hf_sp hf_onto hS hc hw₂ hadj₁ hadj₂ hadj₃
          hw₁₂ hw₃_ne1.symm hw₃_ne2.symm (hinv_rem w₁ hw₁ hadj₁) (hinv_rem w₃ hw₃ hadj₃)
          hy_S hy_C1 (fun u hu hlt => ih _ hlt u hu rfl) _ {j} z_y
          (fun i hi => by rw [Finset.mem_singleton.mp hi]; simp [z_y]) hz_y_S
          (sp_update_self_outcome hf_sp z j) ?_ ?_ rfl
        · simpa only [hif_eq, C₁, hcard'] using Nat.sub_lt hm_pos zero_lt_one
        · simp only [hif_eq]
          change f (fun i => π₁ (z' i)) ∈ _
          rw [hπ_upd, ← hih']
          exact hπy'_br

private lemma branchInvOn_all
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    (S : Finset V) (hS : IsSubtreeVertexSet W S) :
    BranchInvOn W f S := by
  classical
  induction S using (_root_.measure Finset.card).wf.induction with
  | h S ih =>
    by_cases hdeg : ∀ v ∈ S, (S.filter fun u => W.graph.Adj v u).card ≤ 2
    · obtain ⟨a, _, b, _, hsub⟩ := hS.exists_subtree_eq_interval hT fun v hv T hTm =>
        (Finset.card_le_card fun u hu => Finset.mem_filter.mpr (hTm u hu)).trans (hdeg v hv)
      exact branchInvOn_of_interval hT hf_sp hf_onto hsub
    · push Not at hdeg
      obtain ⟨c, hc, hdeg3⟩ := hdeg
      let nb := S.filter fun w => W.graph.Adj c w
      have hdeg3' : ∃ T : Finset V, 3 ≤ T.card ∧ ∀ u ∈ T, u ∈ S ∧ W.graph.Adj c u :=
        ⟨nb, hdeg3, fun u hu => Finset.mem_filter.mp hu⟩
      have hinv_rem : ∀ w ∈ S, W.graph.Adj c w → BranchInvOn W f (removeBranch W S c w) :=
        fun w hw hadj => ih _ (card_removeBranch_lt hT hw hadj) (hS.removeBranch hT hc hadj)
      intro y q hy hq hqy x₁ x₂ hx₁ hx₂ hiff
      have hnb_ex : ∃ w ∈ nb, y ∉ branch (vertex c) (vertex w) ∧
          q ∉ branch (vertex c) (vertex w) := by
        by_contra hnot; push Not at hnot
        have hcard_le (z : MetricGraph W) :
            (nb.filter fun w => z ∈ branch (vertex c) (vertex w)).card ≤ 1 :=
          Finset.card_le_one.mpr fun w₁ hw₁ w₂ hw₂ => by
            by_contra hne
            have h1 := Finset.mem_filter.mp hw₁; have h2 := Finset.mem_filter.mp hw₂
            exact Set.disjoint_left.mp (disjoint_branch_vertex_of_adj hT
              (Finset.mem_filter.mp h1.1).2 (Finset.mem_filter.mp h2.1).2 hne) h1.2 h2.2
        have hsub : nb ⊆ (nb.filter fun w => y ∈ branch (vertex c) (vertex w)) ∪
            (nb.filter fun w => q ∈ branch (vertex c) (vertex w)) := fun w hw => by
          by_cases hyw : y ∈ branch (vertex c) (vertex w)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hyw⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hnot w hw hyw⟩)
        linarith [(Finset.card_le_card hsub).trans (Finset.card_union_le _ _),
          hcard_le y, hcard_le q]
      obtain ⟨w, hw_nb, hy_not, hq_not⟩ := hnb_ex
      obtain ⟨hw, hadj⟩ := Finset.mem_filter.mp hw_nb
      let Sw := removeBranch W S c w
      let π := gate (subtree W Sw)
      have hSw := hS.removeBranch hT hc hadj
      have hy_Sw : y ∈ subtree W Sw := (mem_subtree_removeBranch hT hS hc hadj).mpr ⟨hy, hy_not⟩
      have hq_Sw : q ∈ subtree W Sw := (mem_subtree_removeBranch hT hS hc hadj).mpr ⟨hq, hq_not⟩
      have hproj (x : ι → MetricGraph W) (hx : ∀ i, x i ∈ subtree W S) :
          π (f x) = f (fun i => π (x i)) :=
        proj_removeBranch_of_branchInvOn hT hf_sp hf_onto hS hc hw hadj hdeg3' hinv_rem hx
      rw [mem_branch_gate_subtree_iff hT hy_Sw hq_Sw (f x₁),
        mem_branch_gate_subtree_iff hT hy_Sw hq_Sw (f x₂)]
      change π (f x₁) ∈ branch y q ↔ π (f x₂) ∈ branch y q
      rw [hproj x₁ hx₁, hproj x₂ hx₂]
      exact hinv_rem w hw hadj hy_Sw hq_Sw hqy
        (fun i => gate_subtree_mem hT hSw.nonempty (x₁ i))
        (fun i => gate_subtree_mem hT hSw.nonempty (x₂ i))
        fun i => by
          rw [← mem_branch_gate_subtree_iff hT hy_Sw hq_Sw (x₁ i),
            ← mem_branch_gate_subtree_iff hT hy_Sw hq_Sw (x₂ i)]
          exact hiff i

private lemma two_val_win_mono
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f)
    {y q : MetricGraph W} (hq : q ≠ y) {S T : Finset ι} (hST : S ⊆ T)
    (hwinS : f (fun i => if i ∈ S then q else y) ∈ branch y q) :
    f (fun i => if i ∈ T then q else y) ∈ branch y q := by
  let _ := Fintype.ofFinite ι
  obtain ⟨φ, E_I, hφ, hφ0, hφd, hrange, hE_I⟩ :=
    exists_moulinScheme_interval hT hf_sp hf_onto y q
  let d := dist y q
  let c (A : Finset ι) : ι → Set.Icc (0 : ℝ) d :=
    fun i => if i ∈ A then ⟨d, dist_nonneg, le_rfl⟩ else ⟨0, le_rfl, dist_nonneg⟩
  have hmap (A : Finset ι) : (fun i => φ (c A i)) = fun i => if i ∈ A then q else y :=
    funext fun i => by dsimp only [c]; split_ifs <;> assumption
  have hf_eq (A : Finset ι) : f (fun i => if i ∈ A then q else y) = φ (E_I.eval (c A)) := by
    rw [← hmap A, hE_I]
  have hmono : (E_I.eval (c S) : ℝ) ≤ E_I.eval (c T) := E_I.eval_mono fun i => by
    dsimp only [c]; split_ifs with h1 h2
    exacts [le_rfl, absurd (hST h1) h2, dist_nonneg, le_rfl]
  have hpos1 : (0 : ℝ) < E_I.eval (c S) := lt_of_le_of_ne (E_I.eval (c S)).2.1 fun h0 => by
    have hfx : f (fun i => if i ∈ S then q else y) = y := by
      rw [hf_eq S, show E_I.eval (c S) = ⟨0, le_rfl, dist_nonneg⟩ from Subtype.ext h0.symm, hφ0]
    rw [hfx] at hwinS
    exact notMem_branch_self y q hwinS
  have hf₂_ne : f (fun i => if i ∈ T then q else y) ≠ y := fun heq => by
    have : (E_I.eval (c T) : ℝ) = 0 := congrArg Subtype.val <| hφ.injective <|
      (hf_eq T).symm.trans (heq.trans hφ0.symm)
    linarith
  exact mem_branch_of_mem_interval hT (mem_branch_self hq)
    (hrange ▸ hf_eq T ▸ ⟨E_I.eval (c T), rfl⟩) hf₂_ne

private lemma exists_mid_branch_mem
    (hT : W.graph.IsTree) {y q z : MetricGraph W} (hz_int : z ∈ interval y q)
    (hz_br : z ∈ branch y q) :
    ∃ p ∈ interval y q, p ≠ y ∧ p ≠ q ∧ y ∉ branch p q ∧ z ∈ branch p q := by
  have hz_ne : z ≠ y := fun h => notMem_branch_self y q (h ▸ hz_br)
  have hdz_pos : 0 < dist y z := dist_pos.mpr hz_ne.symm
  obtain ⟨p, hp_z, hp_dist, _⟩ :=
    exists_mem_interval_dist_eq y z ⟨(half_pos hdz_pos).le, half_le_self hdz_pos.le⟩
  have hp_q : p ∈ interval y q := interval_subset_of_mem hT (left_mem_interval y q) hz_int hp_z
  have hp_ne_y : p ≠ y := fun h => by rw [h, _root_.dist_self] at hp_dist; linarith
  have hp_ne_q : p ≠ q := fun h => by
    have h1 := mem_interval_iff.mp hz_int
    linarith [h ▸ hp_dist, dist_nonneg (x := z) (y := q)]
  have hfz_br : z ∈ branch p q := fun hmem => by
    have hd : dist p z = 0 := by
      linarith [mem_interval_iff.mp hmem, mem_interval_iff.mp hp_q, mem_interval_iff.mp hp_z,
        mem_interval_iff.mp hz_int, _root_.dist_comm q p, _root_.dist_comm q z,
        _root_.dist_comm p z]
    linarith [(dist_eq_zero.mp hd).symm ▸ hp_dist]
  exact ⟨p, hp_q, hp_ne_y, hp_ne_q,
    by simpa only [branch, Set.mem_ofPred_eq, Classical.not_not] using interval_comm y q ▸ hp_q,
    hfz_br⟩

omit [Finite ι] in
/-- Schummer–Vohra characterization on tree metric graphs ([SchummerVohra2002], Theorem 1, with
`TreeEMVS` in place of the source's path-based definition): a deterministic mechanism on a finite
tree metric graph is strategyproof and surjective if and only if it is the evaluation map of a
`TreeEMVS`. -/
theorem isStrategyProof_and_surjective_iff_exists_treeEMVS [Fintype ι]
    [Nonempty V] [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (f : (ι → MetricGraph W) → MetricGraph W) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f) ↔
      ∃ E : TreeEMVS W ι, f = E.eval hT := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  refine ⟨?_, fun ⟨E, hE⟩ => hE ▸ ⟨E.eval_isStrategyProof hT, E.eval_surjective hT⟩⟩
  rintro ⟨hf_sp, hf_onto⟩
  have hf_unan : ∀ y, f (fun _ => y) = y := unanimous_of_surjective_isStrategyProof hf_sp hf_onto
  have hinv_univ := branchInvOn_all hT hf_sp hf_onto Finset.univ (isSubtreeVertexSet_univ W)
  have hmem_u (z : MetricGraph W) : z ∈ subtree W Finset.univ := subtree_univ hT ▸ Set.mem_univ z
  let win (y q : MetricGraph W) (S : Finset ι) : Prop :=
    f (fun i => if i ∈ S then q else y) ∈ branch y q
  have hwin_eq {y q : MetricGraph W} (hq : q ≠ y) {S : Finset ι} {x : ι → MetricGraph W}
      (hS : ∀ i, x i ∈ branch y q ↔ i ∈ S) : f x ∈ branch y q ↔ win y q S :=
    hinv_univ (hmem_u y) (hmem_u q) hq (fun i => hmem_u (x i)) (fun _ => hmem_u _) fun i => by
      rw [hS i]; by_cases hi : i ∈ S <;> simp [hi, mem_branch_self hq]
  let E : TreeEMVS W ι :=
    { win := win
      branch_eq := fun {y q₁ q₂} hq1 hq2 hbr => by
        ext S
        have hx i : (if i ∈ S then q₁ else y) ∈ branch y q₂ ↔ i ∈ S := by
          rw [← hbr]; by_cases hi : i ∈ S <;> simp [hi, mem_branch_self hq1]
        simpa only [win, hbr] using hwin_eq hq2 hx
      empty_false := fun _ => by simp [win, hf_unan]
      univ_true := fun hq => by simp [win, hf_unan, mem_branch_self hq]
      mono := fun hq hST hw => two_val_win_mono hT hf_sp hf_onto hq hST hw
      nesting := fun {y₁ q₁ y₂ q₂ S} hq1 hq2 hsub hw => by
        let x : ι → MetricGraph W := fun i => if i ∈ S then q₂ else y₁
        have hy1 : y₁ ∉ branch y₂ q₂ := fun h => notMem_branch_self y₁ q₁ (hsub h)
        have hx2 i : x i ∈ branch y₂ q₂ ↔ i ∈ S := by
          by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self hq2, hy1]
        have hx1 i : x i ∈ branch y₁ q₁ ↔ i ∈ S := by
          by_cases hi : i ∈ S <;> simp [x, hi, hsub (mem_branch_self hq2)]
        exact (hwin_eq hq1 hx1).mp (hsub ((hwin_eq hq2 hx2).mpr hw))
      duality := fun {y₁ y₂ S} h12 hnot => by
        let x : ι → MetricGraph W := fun i => if i ∈ S then y₂ else y₁
        have hfx_n : f x ∉ branch y₁ y₂ := fun h =>
          hnot ((hwin_eq h12.symm fun i => by
            by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self h12.symm]).mp h)
        exact (hwin_eq h12 fun i => by
          by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self h12]).mp (branch_symm h12 hfx_n)
      exclusive := fun {y q₁ q₂ S} hq1 hq2 hbr ⟨hw1, hw2⟩ => by
        have hdisj := branch_disjoint_of_ne hT hbr
        let x : ι → MetricGraph W := fun i => if i ∈ S then q₁ else q₂
        have hx1 : ∀ i, x i ∈ branch y q₁ ↔ i ∈ S := fun i => by
          by_cases hi : i ∈ S <;>
            simp [x, hi, mem_branch_self hq1, Set.disjoint_right.mp hdisj (mem_branch_self hq2)]
        have hx2 : ∀ i, x i ∈ branch y q₂ ↔ i ∈ Sᶜ := fun i => by
          by_cases hi : i ∈ S <;>
            simp [x, hi, Set.disjoint_left.mp hdisj (mem_branch_self hq1), mem_branch_self hq2]
        exact Set.disjoint_left.mp hdisj
          ((hwin_eq hq1 hx1).mpr hw1) ((hwin_eq hq2 hx2).mpr hw2)
      open_interior := fun {y q S} _ hw => by
        let x : ι → MetricGraph W := fun i => if i ∈ S then q else y
        have hz_int : f x ∈ interval y q := range_of_convex hT hf_sp hf_onto
          (isConvex_interval hT y q) (isClosed_interval y q) ⟨y, left_mem_interval y q⟩
          fun i => by by_cases hi : i ∈ S <;> simp [x, hi]
        obtain ⟨p, hp_q, hp_y, hp_ne_q, hy_nb, hz_br⟩ := exists_mid_branch_mem hT hz_int hw
        refine ⟨p, hp_q, hp_y, hp_ne_q, (hwin_eq hp_ne_q.symm fun i => ?_).mp hz_br⟩
        by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self hp_ne_q.symm, hy_nb] }
  refine ⟨E, funext fun x => ((E.eval_eq_iff hT x (f x)).mpr ?_).symm⟩
  intro q hq S hS hw
  exact notMem_branch_self (f x) q ((hwin_eq hq fun i => (hS i).symm).mpr hw)

/-- Every deterministic, surjective, strategyproof facility-location mechanism on a finite tree
metric graph is strongly group strategyproof. This strengthens Theorem 1 of [SchummerVohra2002],
which states only individual strategyproofness; the strengthening is not stated in the source. -/
theorem isGroupStrategyProof_of_isStrategyProof_of_surjective_tree
    [Nonempty V] [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    (Mechanism.deterministic f).IsGroupStrategyProof := by
  let _ := Fintype.ofFinite ι
  obtain ⟨E, rfl⟩ :=
    (isStrategyProof_and_surjective_iff_exists_treeEMVS hT f).mp ⟨hf_sp, hf_onto⟩
  exact E.eval_isGroupStrategyProof hT

end Characterization

end Cslib.GameTheory.FacilityLocation
