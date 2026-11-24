/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.Algorithms.Lean.Submodular.Greedy
public import CslibFrontier.GameTheory.Network.InfluenceModels
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Influence Submodularity and Greedy Influence Maximization

This module formalizes Section 24.4 of [Kleinberg2007] (pp. 622–627), establishing the
local-to-global submodularity theorems for network influence functions and their `(1 - 1/e)` greedy
approximation corollaries:

1. **Independent Cascade Submodularity via Live-Edge Graphs** ([KempeKleinbergTardos2003];
   [Kleinberg2007], Theorem 24.5, pp. 625–626): flipping all edge coins upfront decomposes
   `IndependentCascadeModel.influence` into a convex combination of directed reachability coverage
   sizes `|liveReachable H S|` (`IndependentCascadeModel.influence_eq_sum_liveGraphWeight`), each
   of which is monotone and submodular (`IndependentCascadeModel.isSubmodular_influence`).
2. **Mossel–Roch General Threshold Submodularity** ([MosselRoch2007]; [Kleinberg2007],
   Theorem 24.6, p. 626): whenever every local threshold function `M.thresholdFn v` is submodular,
   the global expectation `S ↦ ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V` is monotone and
   submodular for every monotone submodular objective `φ : Finset V → ℝ`
   (`GeneralThresholdModel.isSubmodular_integral_thresholdFinal`), and in particular `M.influence`
   is submodular (`GeneralThresholdModel.isSubmodular_influence`). Specializations yield
   submodularity for `LinearThresholdModel` and for `T`-step nonprogressive threshold processes via
   `timeLayeredDigraph` (`GeneralThresholdModel.isSubmodular_nonprogStepInfluence`).
3. **Diminishing-Returns Cascade Submodularity** ([KempeKleinbergTardos2003];
   [KempeKleinbergTardos2005]; [Kleinberg2007], Theorem 24.4, pp. 624, 626): under
   `CascadeModel.HasDiminishingReturns`, every translated threshold function
   `C.toGeneralThresholdModel.thresholdFn v` is submodular
   (`CascadeModel.isSubmodular_toGeneralThresholdModel_thresholdFn`), so `C.influence` is
   submodular (`CascadeModel.isSubmodular_influence_of_diminishingReturns`).
4. **Greedy `(1 - 1/e)` Influence Maximization** ([NemhauserWolseyFisher1978];
   [KempeKleinbergTardos2003]; [Kleinberg2007], Theorem 24.3 and Section 24.4, pp. 623–626):
   combining monotone submodularity with `one_sub_exp_neg_one_mul_le_submodularGreedy` gives the
   `(1 - Real.exp (-1))` cardinality-constrained greedy guarantee across all three models.

## Main definitions

* `Cslib.GameTheory.Network.liveReachableFrom`, `Cslib.GameTheory.Network.liveReachable`:
  vertices reachable from a seed or seed set in a realized live-edge digraph `H : Digraph V`.
* `Cslib.GameTheory.Network.liveGraphWeight`: product Bernoulli weight of a live-edge digraph `H`
  under `IC : IndependentCascadeModel G`.
* `Cslib.GameTheory.Network.IndependentCascadeModel.influence`: expected final active-set size in
  the Independent Cascade Model.

## Main results

* `Cslib.GameTheory.Network.IndependentCascadeModel.influence_eq_sum_liveGraphWeight`: live-edge
  graph decomposition of Independent Cascade influence ([Kleinberg2007], Section 24.4, pp. 625–626).
* `Cslib.GameTheory.Network.IndependentCascadeModel.isSubmodular_influence`:
  **Theorem 24.5** of [Kleinberg2007] ([KempeKleinbergTardos2003]).
* `Cslib.GameTheory.Network.GeneralThresholdModel.isSubmodular_integral_thresholdFinal`,
  `Cslib.GameTheory.Network.GeneralThresholdModel.isSubmodular_influence`:
  **Theorem 24.6** of [Kleinberg2007] ([MosselRoch2007]).
* `Cslib.GameTheory.Network.CascadeModel.isSubmodular_influence_of_diminishingReturns`:
  **Theorem 24.4** of [Kleinberg2007] ([KempeKleinbergTardos2003]; [KempeKleinbergTardos2005]).
* `Cslib.GameTheory.Network.GeneralThresholdModel.one_sub_exp_neg_one_mul_le_greedy_influence`,
  `Cslib.GameTheory.Network.CascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence`,
  `Cslib.GameTheory.Network.IndependentCascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence`:
  `(1 - 1/e)` greedy influence maximization guarantees.

## References

* [KempeKleinbergTardos2003]
* [KempeKleinbergTardos2005]
* [Kleinberg2007]
* [MosselRoch2007]
* [NemhauserWolseyFisher1978]
-/

public section

open Cslib.Algorithms.Lean.Submodular MeasureTheory Set

namespace Cslib.GameTheory.Network

/-! ## Theorem 24.5: Independent Cascade Live-Edge Decomposition and Submodularity -/

section LiveEdge

/-- Vertices reachable from `s : V` along directed paths in a realized live-edge graph
`H : Digraph V` ([Kleinberg2007], Section 24.4, pp. 625–626). -/
noncomputable def liveReachableFrom {V : Type*} [Fintype V] (H : Digraph V) (s : V) : Finset V :=
  open scoped Classical in
  Finset.univ.filter (Relation.ReflTransGen H.Adj s ·)

@[simp]
theorem mem_liveReachableFrom {V : Type*} [Fintype V] {H : Digraph V} {s v : V} :
    v ∈ liveReachableFrom H s ↔ Relation.ReflTransGen H.Adj s v := by
  unfold liveReachableFrom
  simp

/-- Vertices reachable from at least one seed in `S` along directed paths in `H : Digraph V`
([Kleinberg2007], Section 24.4, p. 625). -/
noncomputable def liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V)
    (S : Finset V) : Finset V :=
  S.biUnion (liveReachableFrom H)

@[simp]
theorem mem_liveReachable {V : Type*} [DecidableEq V] [Fintype V] {H : Digraph V}
    {S : Finset V} {v : V} :
    v ∈ liveReachable H S ↔ ∃ s ∈ S, Relation.ReflTransGen H.Adj s v := by
  simp [liveReachable]

@[simp]
theorem liveReachable_empty {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V) :
    liveReachable H ∅ = ∅ := by
  simp [liveReachable]

theorem subset_liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V)
    (S : Finset V) : S ⊆ liveReachable H S :=
  fun s hs => mem_liveReachable.mpr ⟨s, hs, Relation.ReflTransGen.refl⟩

theorem monotone_liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V) :
    Monotone (liveReachable H) :=
  fun _ _ hAB _ hv =>
    let ⟨s, hs, hp⟩ := mem_liveReachable.mp hv
    mem_liveReachable.mpr ⟨s, hAB hs, hp⟩

/-- Realized live-edge graph probability
`∏_{(u, v)} p_{uv}^{[H.Adj u v]} (1 - p_{uv})^{[¬ H.Adj u v]}` under independent edge coin flips
([Kleinberg2007], Section 24.4, p. 625). -/
noncomputable def liveGraphWeight {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) (H : Digraph V) : ℝ :=
  open scoped Classical in
  ∏ e : V × V, if H.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2

theorem liveGraphWeight_nonneg {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) (H : Digraph V) :
    0 ≤ liveGraphWeight IC H := by
  classical
  refine Finset.prod_nonneg fun e _ => ?_
  split_ifs
  · exact IC.edgeProb_nonneg e.1 e.2
  · exact sub_nonneg.mpr (IC.edgeProb_le_one e.1 e.2)

private theorem liveGraphWeight_eq_zero_of_not_le {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) {H : Digraph V} (hnot : ¬ H ≤ G) :
    liveGraphWeight IC H = 0 := by
  classical
  have hex : ∃ e : V × V, H.Adj e.1 e.2 ∧ ¬ G.Adj e.1 e.2 := by
    by_contra hall
    push Not at hall
    exact hnot fun u v huv => hall (u, v) huv
  rcases hex with ⟨e, heH, heG⟩
  unfold liveGraphWeight
  refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
  simp [heH, IC.edgeProb_eq_zero_of_not_adj e.1 e.2 heG]

/-- Sum of independent Bernoulli product weights over subsets `E ⊆ U` containing `inSet` and
disjoint from `outSet`. -/
private theorem sum_powerset_bernWeight {α : Type*} [DecidableEq α] (p : α → ℝ)
    (U inSet outSet : Finset α) (hin : inSet ⊆ U) (hout : outSet ⊆ U)
    (hdisj : Disjoint inSet outSet) :
    (∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E outSet,
        ∏ a ∈ U, (if a ∈ E then p a else 1 - p a)) =
      (∏ a ∈ inSet, p a) * (∏ a ∈ outSet, (1 - p a)) := by
  induction U using Finset.induction generalizing inSet outSet with
  | empty =>
    rw [Finset.subset_empty.mp hin, Finset.subset_empty.mp hout]
    simp
  | insert a U haU ih =>
    have hsplit_sum :
        ∀ f : Finset α → ℝ,
          ∑ E ∈ (insert a U).powerset, f E =
            (∑ E ∈ U.powerset, f E) + ∑ E ∈ U.powerset, f (insert a E) := by
      intro f
      have hdisj_pow : Disjoint U.powerset (U.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro E h1 h2
        rcases Finset.mem_image.mp h2 with ⟨F, _, rfl⟩
        exact haU (Finset.mem_powerset.mp h1 (Finset.mem_insert_self a F))
      rw [Finset.powerset_insert, Finset.sum_union hdisj_pow, Finset.sum_image]
      intro E₁ hE₁ E₂ hE₂ heq
      have ha₁ : a ∉ E₁ := fun h => haU (Finset.mem_powerset.mp hE₁ h)
      have ha₂ : a ∉ E₂ := fun h => haU (Finset.mem_powerset.mp hE₂ h)
      simpa only [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using
        congrArg (fun S => S.erase a) heq
    rw [Finset.sum_filter, hsplit_sum]
    have hprod_no : ∀ {E : Finset α}, E ∈ U.powerset →
        (∏ x ∈ insert a U, if x ∈ E then p x else 1 - p x) =
          (1 - p a) * ∏ x ∈ U, if x ∈ E then p x else 1 - p x := by
      intro E hE
      have haE : a ∉ E := fun h => haU (Finset.mem_powerset.mp hE h)
      rw [Finset.prod_insert haU]
      simp [haE]
    have hprod_yes : ∀ {E : Finset α}, E ∈ U.powerset →
        (∏ x ∈ insert a U, if x ∈ insert a E then p x else 1 - p x) =
          p a * ∏ x ∈ U, if x ∈ E then p x else 1 - p x := by
      intro E hE
      rw [Finset.prod_insert haU]
      simp only [Finset.mem_insert_self, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun x hxU => ?_
      have hxa : x ≠ a := fun h => haU (h ▸ hxU)
      simp [hxa]
    by_cases hain : a ∈ inSet
    · have haout : a ∉ outSet := Finset.disjoint_left.mp hdisj hain
      have hin' : inSet.erase a ⊆ U :=
        fun x hx => (Finset.mem_insert.mp (hin (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
      have hout' : outSet ⊆ U :=
        fun x hx => (Finset.mem_insert.mp (hout hx)).resolve_left fun hxa => haout (hxa ▸ hx)
      have hdisj' : Disjoint (inSet.erase a) outSet :=
        hdisj.mono_left (Finset.erase_subset a inSet)
      have hno_zero : (∑ E ∈ U.powerset,
          if inSet ⊆ E ∧ Disjoint E outSet then
            ∏ x ∈ insert a U, (if x ∈ E then p x else 1 - p x) else 0) = 0 := by
        refine Finset.sum_eq_zero fun E hE => ?_
        have haE : a ∉ E := fun h => haU (Finset.mem_powerset.mp hE h)
        have hnot : ¬ (inSet ⊆ E ∧ Disjoint E outSet) := fun h => haE (h.1 hain)
        simp [hnot]
      have hyes : (∑ E ∈ U.powerset,
          if inSet ⊆ insert a E ∧ Disjoint (insert a E) outSet then
            ∏ x ∈ insert a U, (if x ∈ insert a E then p x else 1 - p x) else 0) =
          p a * ∑ E ∈ U.powerset with inSet.erase a ⊆ E ∧ Disjoint E outSet,
            ∏ x ∈ U, (if x ∈ E then p x else 1 - p x) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun E hE => ?_
        have hcond : (inSet ⊆ insert a E ∧ Disjoint (insert a E) outSet) ↔
            (inSet.erase a ⊆ E ∧ Disjoint E outSet) := by
          rw [Finset.disjoint_insert_left]
          refine and_congr ?_ ⟨fun h => h.2, fun h => ⟨haout, h⟩⟩
          exact ⟨fun h x hx => (Finset.mem_insert.mp (h (Finset.mem_of_mem_erase hx))).resolve_left
              (Finset.ne_of_mem_erase hx),
            fun h x hx => by
              rcases eq_or_ne x a with rfl | hxa
              · exact Finset.mem_insert_self x E
              · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨hxa, hx⟩))⟩
        split_ifs with h1 h2 h2
        · exact hprod_yes hE
        · exact absurd (hcond.mp h1) h2
        · exact absurd (hcond.mpr h2) h1
        · simp
      rw [hno_zero, zero_add, hyes, ih (inSet.erase a) outSet hin' hout' hdisj', ← mul_assoc,
        Finset.mul_prod_erase inSet p hain]
    · by_cases haout : a ∈ outSet
      · have hin' : inSet ⊆ U :=
          fun x hx => (Finset.mem_insert.mp (hin hx)).resolve_left fun hxa => hain (hxa ▸ hx)
        have hout' : outSet.erase a ⊆ U :=
          fun x hx => (Finset.mem_insert.mp (hout (Finset.mem_of_mem_erase hx))).resolve_left
            (Finset.ne_of_mem_erase hx)
        have hdisj' : Disjoint inSet (outSet.erase a) :=
          hdisj.mono_right (Finset.erase_subset a outSet)
        have hyes_zero : (∑ E ∈ U.powerset,
            if inSet ⊆ insert a E ∧ Disjoint (insert a E) outSet then
              ∏ x ∈ insert a U, (if x ∈ insert a E then p x else 1 - p x) else 0) = 0 := by
          refine Finset.sum_eq_zero fun E _ => ?_
          split_ifs with h
          · exact absurd haout (Finset.disjoint_insert_left.mp h.2).1
          · rfl
        have hno : (∑ E ∈ U.powerset,
            if inSet ⊆ E ∧ Disjoint E outSet then
              ∏ x ∈ insert a U, (if x ∈ E then p x else 1 - p x) else 0) =
            (1 - p a) * ∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E (outSet.erase a),
              ∏ x ∈ U, (if x ∈ E then p x else 1 - p x) := by
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun E hE => ?_
          have haE : a ∉ E := fun h => haU (Finset.mem_powerset.mp hE h)
          have hcond : Disjoint E outSet ↔ Disjoint E (outSet.erase a) := by
            refine ⟨fun h => h.mono_right (Finset.erase_subset a outSet), fun h => ?_⟩
            rw [Finset.disjoint_left] at h ⊢
            intro x hxE hxout
            rcases eq_or_ne x a with rfl | hxa
            · exact haE hxE
            · exact h hxE (Finset.mem_erase.mpr ⟨hxa, hxout⟩)
          split_ifs with h1 h2 h2
          · exact hprod_no hE
          · exact absurd ⟨h1.1, hcond.mp h1.2⟩ h2
          · exact absurd ⟨h2.1, hcond.mpr h2.2⟩ h1
          · simp
        rw [hyes_zero, add_zero, hno, ih inSet (outSet.erase a) hin' hout' hdisj',
          mul_left_comm, Finset.mul_prod_erase outSet (fun x => 1 - p x) haout]
      · have hin' : inSet ⊆ U :=
          fun x hx => (Finset.mem_insert.mp (hin hx)).resolve_left fun hxa => hain (hxa ▸ hx)
        have hout' : outSet ⊆ U :=
          fun x hx => (Finset.mem_insert.mp (hout hx)).resolve_left fun hxa => haout (hxa ▸ hx)
        have hcomb :
            (∑ E ∈ U.powerset,
              if inSet ⊆ E ∧ Disjoint E outSet then
                ∏ x ∈ insert a U, (if x ∈ E then p x else 1 - p x) else 0) +
            (∑ E ∈ U.powerset,
              if inSet ⊆ insert a E ∧ Disjoint (insert a E) outSet then
                ∏ x ∈ insert a U, (if x ∈ insert a E then p x else 1 - p x) else 0) =
            ∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E outSet,
              ∏ x ∈ U, (if x ∈ E then p x else 1 - p x) := by
          rw [← Finset.sum_add_distrib, Finset.sum_filter]
          refine Finset.sum_congr rfl fun E hE => ?_
          have hcond : (inSet ⊆ insert a E ∧ Disjoint (insert a E) outSet) ↔
              (inSet ⊆ E ∧ Disjoint E outSet) := by
            rw [Finset.disjoint_insert_left]
            refine and_congr ?_ ⟨fun h => h.2, fun h => ⟨haout, h⟩⟩
            exact ⟨fun h x hx => (Finset.mem_insert.mp (h hx)).resolve_left
                fun hxa => hain (hxa ▸ hx),
              fun h => h.trans (Finset.subset_insert a E)⟩
          split_ifs with h1 h2 h2
          · rw [hprod_no hE, hprod_yes hE]
            ring
          · exact absurd (hcond.mpr h1) h2
          · exact absurd (hcond.mp h2) h1
          · simp
        rw [hcomb, ih inSet outSet hin' hout' hdisj]

/-- Equivalence between `Digraph V` and edge sets `Finset (V × V)`. -/
private noncomputable def digraphEquivEdgeFinset (V : Type*) [DecidableEq V] [Fintype V] :
    Digraph V ≃ Finset (V × V) where
  toFun H := open scoped Classical in Finset.univ.filter fun e : V × V => H.Adj e.1 e.2
  invFun E := ⟨fun u v => (u, v) ∈ E⟩
  left_inv H := by
    ext u v
    simp
  right_inv E := by
    ext ⟨u, v⟩
    simp

/-- Modifying incoming edges into a vertex `v ∈ B` already in the seed set `B` leaves
`liveReachable · B` unchanged. -/
private theorem liveReachable_congr_inEdges {V : Type*} [DecidableEq V] [Fintype V]
    {H₁ H₂ : Digraph V} {v : V} {B : Finset V} (hv : v ∈ B)
    (hother : ∀ x y, y ≠ v → (H₁.Adj x y ↔ H₂.Adj x y)) :
    liveReachable H₁ B = liveReachable H₂ B := by
  have dir : ∀ {G₁ G₂ : Digraph V}, (∀ x y, y ≠ v → G₁.Adj x y → G₂.Adj x y) →
      liveReachable G₁ B ⊆ liveReachable G₂ B := by
    intro G₁ G₂ hG z hz
    rcases mem_liveReachable.mp hz with ⟨s, hsB, hp⟩
    clear hz
    induction hp with
    | refl => exact subset_liveReachable G₂ B hsB
    | @tail a b _ hab ih =>
      rcases mem_liveReachable.mp ih with ⟨s', hs'B, hp'⟩
      rcases eq_or_ne b v with rfl | hbv
      · exact subset_liveReachable G₂ B hv
      · exact mem_liveReachable.mpr ⟨s', hs'B, hp'.tail (hG a b hbv hab)⟩
  exact Finset.Subset.antisymm
    (dir fun x y hy => (hother x y hy).mp)
    (dir fun x y hy => (hother x y hy).mpr)

namespace IndependentCascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (IC : IndependentCascadeModel G)

/-- Expected number of active vertices at the end of the Independent Cascade process starting from
seed set `S` ([Kleinberg2007], Section 24.4, p. 623). -/
noncomputable def influence (S : Finset V) : ℝ :=
  IC.toCascadeModel.influence S

@[simp]
theorem toCascadeModel_influence (S : Finset V) :
    IC.toCascadeModel.influence S = IC.influence S := by
  rfl

private theorem survivalProb_toCascadeModel (w : V) (X : Finset V) :
    IC.toCascadeModel.survivalProb w X = ∏ u ∈ X, (1 - IC.edgeProb u w) := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    rw [IC.toCascadeModel.survivalProb_insert w hu, ih, Finset.prod_insert hu, mul_comm,
      IC.toCascadeModel_prob]

private theorem survivalProd_mul_cascadeProbFrom_eq_sum_liveGraphWeight
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)}
    (hvalid : CascadeModel.ValidNextEdge G nextEdge)
    (active : Finset V) (tried : V → Finset V)
    (hinv : ∀ w ∉ active, tried w ⊆ active ∩ inNeighbors G w) (A : Finset V) :
    open scoped Classical in
    (∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w)) *
        IC.toCascadeModel.cascadeProbFrom nextEdge active tried A =
      ∑ H : Digraph V with
          (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = A,
        liveGraphWeight IC H := by
  classical
  have step_live : ∀ n, Fintype.card V * Fintype.card V - ∑ w : V, (tried w).card = n →
      (∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w)) *
          IC.toCascadeModel.cascadeProbFrom nextEdge active tried A =
        ∑ H : Digraph V with
            (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = A,
          liveGraphWeight IC H := by
    intro n
    induction n using Nat.strong_induction_on generalizing active tried with
    | _ n ih =>
      intro hn
      by_cases hne : (CascadeModel.untriedEdges G active tried).Nonempty
      · obtain ⟨⟨u, v⟩, huv_mem, hnext⟩ := (hvalid active tried).1 hne
        rcases CascadeModel.mem_untriedEdges.mp huv_mem with ⟨hu_act, hv_inact, hadj, hu_untried⟩
        dsimp only at hu_act hv_inact hadj hu_untried
        let tried' := Function.update tried v (insert u (tried v))
        have hcard_lt : ∑ w : V, (tried w).card < ∑ w : V, (tried' w).card := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
            ← Finset.add_sum_erase _ (fun w => (tried' w).card) (Finset.mem_univ v)]
          dsimp only [tried']
          rw [Function.update_self, Finset.card_insert_of_notMem hu_untried]
          have hrest : ∑ w ∈ Finset.univ.erase v, (tried w).card =
              ∑ w ∈ Finset.univ.erase v, (Function.update tried v (insert u (tried v)) w).card :=
            Finset.sum_congr rfl fun w hw => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
          rw [hrest]
          omega
        have hbound : ∑ w : V, (tried w).card < Fintype.card V * Fintype.card V := by
          have hb' : ∑ w : V, (tried' w).card ≤ Fintype.card V * Fintype.card V :=
            (Finset.sum_le_sum fun w _ => Finset.card_le_univ _).trans (by simp)
          omega
        have hm_lt : Fintype.card V * Fintype.card V - ∑ w : V, (tried' w).card < n := by omega
        have hinv_succ : ∀ w ∉ insert v active, tried' w ⊆ insert v active ∩ inNeighbors G w := by
          intro w hw
          have hw_ne : w ≠ v := fun h => hw (Finset.mem_insert.mpr (Or.inl h))
          have hw_inact : w ∉ active := fun h => hw (Finset.mem_insert_of_mem h)
          dsimp only [tried']
          rw [Function.update_of_ne hw_ne]
          exact (hinv w hw_inact).trans
            (Finset.inter_subset_inter_right (Finset.subset_insert v active))
        have hinv_fail : ∀ w ∉ active, tried' w ⊆ active ∩ inNeighbors G w := by
          intro w hw
          dsimp only [tried']
          rcases eq_or_ne w v with rfl | hwv
          · rw [Function.update_self]
            exact Finset.insert_subset (Finset.mem_inter.mpr ⟨hu_act, mem_inNeighbors.mpr hadj⟩)
              (hinv w hw)
          · rw [Function.update_of_ne hwv]
            exact hinv w hw
        have ih_succ := ih _ hm_lt (insert v active) tried' hinv_succ rfl
        have ih_fail := ih _ hm_lt active tried' hinv_fail rfl
        rw [IC.toCascadeModel.cascadeProbFrom_eq]
        simp only [hnext, huv_mem, ↓reduceIte]
        have hv_compl : v ∈ activeᶜ := Finset.mem_compl.mpr hv_inact
        have hcompl_erase : activeᶜ.erase v = (insert v active)ᶜ := by
          ext w
          simp
        have hprod_split : ∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w) =
            IC.toCascadeModel.survivalProb v (tried v) *
              ∏ w ∈ (insert v active)ᶜ, IC.toCascadeModel.survivalProb w (tried' w) := by
          rw [← Finset.mul_prod_erase _ _ hv_compl, hcompl_erase]
          congr 1
          refine Finset.prod_congr rfl fun w hw => ?_
          have hw_ne : w ≠ v :=
            fun h => (Finset.mem_compl.mp hw) (h ▸ Finset.mem_insert_self v active)
          dsimp only [tried']
          rw [Function.update_of_ne hw_ne]
        have hprod_fail : (∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w)) *
            (1 - IC.toCascadeModel.prob v u (tried v)) =
            ∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried' w) := by
          rw [hprod_split, mul_right_comm, ← IC.toCascadeModel.survivalProb_insert v hu_untried,
            ← hcompl_erase, ← Finset.mul_prod_erase activeᶜ
              (fun w => IC.toCascadeModel.survivalProb w (tried' w)) hv_compl]
          dsimp only [tried']
          rw [Function.update_self]
        have halg :
            (∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w)) *
              (IC.toCascadeModel.prob v u (tried v) *
                IC.toCascadeModel.cascadeProbFrom nextEdge (insert v active) tried' A +
                (1 - IC.toCascadeModel.prob v u (tried v)) *
                IC.toCascadeModel.cascadeProbFrom nextEdge active tried' A) =
            IC.edgeProb u v * IC.toCascadeModel.survivalProb v (tried v) *
              (∑ H : Digraph V with
                  (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                    liveReachable H (insert v active) = A,
                liveGraphWeight IC H) +
              (∑ H : Digraph V with
                  (∀ w ∉ active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧ liveReachable H active = A,
                liveGraphWeight IC H) := by
          rw [← ih_succ, ← ih_fail, ← hprod_fail, hprod_split, IC.toCascadeModel_prob]
          ring
        change (∏ w ∈ activeᶜ, IC.toCascadeModel.survivalProb w (tried w)) *
            (IC.toCascadeModel.prob v u (tried v) *
              IC.toCascadeModel.cascadeProbFrom nextEdge (insert v active) tried' A +
              (1 - IC.toCascadeModel.prob v u (tried v)) *
              IC.toCascadeModel.cascadeProbFrom nextEdge active tried' A) = _
        rw [halg]
        -- Split RHS filter on `H.Adj u v` vs `¬ H.Adj u v`.
        let S_all := Finset.univ.filter fun H : Digraph V =>
          (∀ w ∉ active, ∀ x ∈ tried w, ¬ H.Adj x w) ∧ liveReachable H active = A
        have hpart : ∑ H ∈ S_all, liveGraphWeight IC H =
            (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) +
              (∑ H ∈ S_all with ¬ H.Adj u v, liveGraphWeight IC H) :=
          (Finset.sum_filter_add_sum_filter_not S_all (fun H : Digraph V => H.Adj u v) _).symm
        change _ = ∑ H ∈ S_all, liveGraphWeight IC H
        rw [hpart]
        congr 1
        · -- `H.Adj u v` branch: factor out incoming edges to `v`.
          let Base := Finset.univ.filter fun H₀ : Digraph V =>
            (∀ x, ¬ H₀.Adj x v) ∧
              (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H₀.Adj x w) ∧
              liveReachable H₀ (insert v active) = A
          let mkH : Digraph V → Finset V → Digraph V := fun H₀ X =>
            ⟨fun x y => if y = v then x ∈ X else H₀.Adj x y⟩
          have hweight_mkH : ∀ H₀ ∈ Base, ∀ X : Finset V,
              liveGraphWeight IC (mkH H₀ X) =
                (∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
                (∏ x : V, if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v) := by
            intro H₀ _ X
            unfold liveGraphWeight
            rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : V × V => e.2 ≠ v)]
            congr 1
            · refine Finset.prod_congr rfl fun e he => ?_
              have hne_v : e.2 ≠ v := (Finset.mem_filter.mp he).2
              simp [mkH, hne_v]
            · have hbij : (∏ e ∈ Finset.univ.filter (fun e : V × V => ¬ e.2 ≠ v),
                  if (mkH H₀ X).Adj e.1 e.2 then IC.edgeProb e.1 e.2
                  else 1 - IC.edgeProb e.1 e.2) =
                  ∏ x : V, if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v := by
                refine Finset.prod_bij (fun e _ => e.1) ?_ ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hx
                  have hy₁ : y₁ = v := not_not.mp (Finset.mem_filter.mp h₁).2
                  have hy₂ : y₂ = v := not_not.mp (Finset.mem_filter.mp h₂).2
                  subst hx hy₁ hy₂
                  rfl
                · intro x _
                  exact ⟨(x, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_not.mpr rfl⟩, rfl⟩
                · intro ⟨x, y⟩ hy
                  have hyv : y = v := not_not.mp (Finset.mem_filter.mp hy).2
                  subst hyv
                  simp [mkH]
              convert hbij
          have hsum_succ :
              (∑ H : Digraph V with
                  (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                    liveReachable H (insert v active) = A,
                liveGraphWeight IC H) =
              ∑ H₀ ∈ Base,
                ∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
            have hprod_bij :
                (∑ H : Digraph V with
                    (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                      liveReachable H (insert v active) = A,
                  liveGraphWeight IC H) =
                ∑ p ∈ Base ×ˢ (Finset.univ : Finset (Finset V)),
                  liveGraphWeight IC (mkH p.1 p.2) := by
              refine Finset.sum_bij
                (fun H _ => (⟨fun x y => y ≠ v ∧ H.Adj x y⟩,
                  Finset.univ.filter fun x => H.Adj x v)) ?_ ?_ ?_ ?_
              · intro H hH
                rcases (Finset.mem_filter.mp hH).2 with ⟨hno, hreach⟩
                let H₀ : Digraph V := ⟨fun x y => y ≠ v ∧ H.Adj x y⟩
                have hreach₀ : liveReachable H₀ (insert v active) = A := by
                  rw [← hreach]
                  exact liveReachable_congr_inEdges (Finset.mem_insert_self v active)
                    fun x y hy => by simp [H₀, hy]
                refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  fun x => by simp, fun w hw x hx h => hno w hw x hx h.2, hreach₀⟩,
                  Finset.mem_univ _⟩
              · intro H₁ _ H₂ _ heq
                rcases Prod.mk.inj heq with ⟨h₀, hX⟩
                ext x y
                rcases eq_or_ne y v with rfl | hyv
                · simpa using congrArg (x ∈ ·) hX
                · have h := congrFun (congrFun (congrArg Digraph.Adj h₀) x) y
                  simpa [hyv] using h
              · rintro ⟨H₀, X⟩ hp
                rcases Finset.mem_product.mp hp with ⟨hBase, _⟩
                dsimp only at hBase
                rcases (Finset.mem_filter.mp hBase).2 with ⟨hnov, hno, hreach₀⟩
                have hreach : liveReachable (mkH H₀ X) (insert v active) = A := by
                  rw [← hreach₀]
                  exact liveReachable_congr_inEdges (Finset.mem_insert_self v active)
                    fun x y hy => by simp [mkH, hy]
                refine ⟨mkH H₀ X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hreach⟩, ?_⟩
                · intro w hw x hx
                  have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self v active)
                  simpa [mkH, hwv] using hno w hw x hx
                · refine Prod.ext ?_ ?_
                  · ext x y
                    rcases eq_or_ne y v with rfl | hyv
                    · simp only [mkH, ↓reduceIte, ne_eq, not_true_eq_false, false_and, false_iff]
                      exact hnov x
                    · simp [mkH, hyv]
                  · ext x
                    simp [mkH]
              · intro H _
                congr 1
                ext x y
                rcases eq_or_ne y v with rfl | hyv <;> simp [mkH, *]
            rw [hprod_bij, Finset.sum_product]
            refine Finset.sum_congr rfl fun H₀ hH₀ => ?_
            have hrow : (∑ X : Finset V, liveGraphWeight IC (mkH H₀ X)) =
                (∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
                ∑ X ∈ (Finset.univ : Finset V).powerset with (∅ : Finset V) ⊆ X ∧
                    Disjoint X (∅ : Finset V),
                  ∏ x ∈ (Finset.univ : Finset V),
                    (if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v) := by
              rw [Finset.mul_sum]
              have hpuniv : (Finset.univ : Finset V).powerset.filter
                  (fun X => (∅ : Finset V) ⊆ X ∧ Disjoint X (∅ : Finset V)) = Finset.univ := by
                ext X
                simp
              rw [hpuniv]
              exact Finset.sum_congr rfl fun X _ => hweight_mkH H₀ hH₀ X
            rw [hrow, sum_powerset_bernWeight _ _ _ _ (Finset.empty_subset _)
              (Finset.empty_subset _) (Finset.disjoint_empty_left _)]
            simp
          have hsum_act :
              (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) =
              IC.edgeProb u v * IC.toCascadeModel.survivalProb v (tried v) *
              ∑ H₀ ∈ Base,
                ∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
            let XValid := (Finset.univ : Finset V).powerset.filter
              fun X => ({u} : Finset V) ⊆ X ∧ Disjoint X (tried v)
            have hreach_ins : ∀ H : Digraph V, H.Adj u v →
                liveReachable H active = liveReachable H (insert v active) := by
              intro H huvH
              refine Finset.Subset.antisymm
                (monotone_liveReachable H (Finset.subset_insert v active)) ?_
              intro z hz
              rcases mem_liveReachable.mp hz with ⟨s, hs, hp⟩
              rcases Finset.mem_insert.mp hs with rfl | hs_act
              · exact mem_liveReachable.mpr
                  ⟨u, hu_act, (Relation.ReflTransGen.single huvH).trans hp⟩
              · exact mem_liveReachable.mpr ⟨s, hs_act, hp⟩
            have hprod_bij :
                (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) =
                ∑ p ∈ Base ×ˢ XValid, liveGraphWeight IC (mkH p.1 p.2) := by
              refine Finset.sum_bij
                (fun H _ => (⟨fun x y => y ≠ v ∧ H.Adj x y⟩,
                  Finset.univ.filter fun x => H.Adj x v)) ?_ ?_ ?_ ?_
              · intro H hH
                rcases Finset.mem_filter.mp hH with ⟨hS, huvH⟩
                rcases (Finset.mem_filter.mp hS).2 with ⟨hno, hreach⟩
                let H₀ : Digraph V := ⟨fun x y => y ≠ v ∧ H.Adj x y⟩
                have hreach₀ : liveReachable H₀ (insert v active) = A := by
                  rw [← hreach, hreach_ins H huvH]
                  exact liveReachable_congr_inEdges (Finset.mem_insert_self v active)
                    fun x y hy => by simp [H₀, hy]
                refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  fun x => by simp, ?_, hreach₀⟩, ?_⟩
                · intro w hw x hx h
                  have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v active)
                  have hwin : w ∉ active := fun ha => hw (Finset.mem_insert_of_mem ha)
                  dsimp only [tried'] at hx
                  rw [Function.update_of_ne hwv] at hx
                  exact hno w hwin x hx h.2
                · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
                    Finset.singleton_subset_iff.mpr (by simp [huvH]), ?_⟩
                  rw [Finset.disjoint_left]
                  intro x hx hxt
                  exact hno v hv_inact x hxt (Finset.mem_filter.mp hx).2
              · intro H₁ _ H₂ _ heq
                rcases Prod.mk.inj heq with ⟨h₀, hX⟩
                ext x y
                rcases eq_or_ne y v with rfl | hyv
                · simpa using congrArg (x ∈ ·) hX
                · have h := congrFun (congrFun (congrArg Digraph.Adj h₀) x) y
                  simpa [hyv] using h
              · rintro ⟨H₀, X⟩ hp
                rcases Finset.mem_product.mp hp with ⟨hBase, hXV⟩
                dsimp only at hBase hXV
                rcases (Finset.mem_filter.mp hBase).2 with ⟨hnov, hno, hreach₀⟩
                rcases (Finset.mem_filter.mp hXV).2 with ⟨huX, hdisjX⟩
                have huv_mk : (mkH H₀ X).Adj u v := by
                  simpa [mkH] using Finset.singleton_subset_iff.mp huX
                have hreach_mk : liveReachable (mkH H₀ X) active = A := by
                  rw [hreach_ins (mkH H₀ X) huv_mk, ← hreach₀]
                  exact (liveReachable_congr_inEdges (Finset.mem_insert_self v active)
                    fun x y hy => by simp [mkH, hy]).symm
                refine ⟨mkH H₀ X, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, ?_, hreach_mk⟩, huv_mk⟩, ?_⟩
                · intro w hw x hx
                  rcases eq_or_ne w v with rfl | hwv
                  · simp only [mkH, ↓reduceIte]
                    exact fun hxX => Finset.disjoint_left.mp hdisjX hxX hx
                  · have hw' : w ∉ insert v active := by simp [hwv, hw]
                    have hx' : x ∈ tried' w := by
                      dsimp only [tried']
                      rwa [Function.update_of_ne hwv]
                    simpa [mkH, hwv] using hno w hw' x hx'
                · refine Prod.ext ?_ ?_
                  · ext x y
                    rcases eq_or_ne y v with rfl | hyv
                    · simp only [mkH, ↓reduceIte, ne_eq, not_true_eq_false, false_and, false_iff]
                      exact hnov x
                    · simp [mkH, hyv]
                  · ext x
                    simp [mkH]
              · intro H _
                congr 1
                ext x y
                rcases eq_or_ne y v with rfl | hyv <;> simp [mkH, *]
            rw [hprod_bij, Finset.sum_product, Finset.mul_sum]
            refine Finset.sum_congr rfl fun H₀ hH₀ => ?_
            have hrow : (∑ X ∈ XValid, liveGraphWeight IC (mkH H₀ X)) =
                (∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
                ∑ X ∈ XValid,
                  ∏ x ∈ (Finset.univ : Finset V),
                    (if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun X _ => hweight_mkH H₀ hH₀ X
            have hdisj_ut : Disjoint ({u} : Finset V) (tried v) :=
              Finset.disjoint_singleton_left.mpr hu_untried
            have hbern := sum_powerset_bernWeight (fun x => IC.edgeProb x v) Finset.univ
              {u} (tried v) (Finset.subset_univ _) (Finset.subset_univ _) hdisj_ut
            rw [hrow, hbern, Finset.prod_singleton, ← IC.survivalProb_toCascadeModel v (tried v)]
            ring
          rw [hsum_succ, hsum_act]
        · -- `¬ H.Adj u v` branch: identical filter to `tried'`.
          symm
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext H
          simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hno, hreach⟩, hnotuv⟩
            refine ⟨fun w hw x hx => ?_, hreach⟩
            dsimp only [tried'] at hx
            rcases eq_or_ne w v with rfl | hwv
            · rw [Function.update_self] at hx
              rcases Finset.mem_insert.mp hx with rfl | hxt
              · exact hnotuv
              · exact hno w hv_inact x hxt
            · rw [Function.update_of_ne hwv] at hx
              exact hno w hw x hx
          · rintro ⟨hno', hreach⟩
            refine ⟨⟨fun w hw x hx => ?_, hreach⟩, ?_⟩
            · rcases eq_or_ne w v with rfl | hwv
              · exact hno' w hv_inact x (by simp [tried', Finset.mem_insert_of_mem hx])
              · exact hno' w hw x (by simp [tried', Function.update_of_ne hwv, hx])
            · exact hno' v hv_inact u (by simp [tried'])
      · -- Base case: `untriedEdges G active tried = ∅`.
        have hemp : CascadeModel.untriedEdges G active tried = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hne
        have hnext : nextEdge active tried = none := (hvalid active tried).2 hemp
        rw [IC.toCascadeModel.cascadeProbFrom_eq]
        simp only [hnext]
        have htr_eq : ∀ w ∉ active, tried w = active ∩ inNeighbors G w := by
          intro w hw
          refine Finset.Subset.antisymm (hinv w hw) fun u hu => ?_
          rcases Finset.mem_inter.mp hu with ⟨hu_act, hadj⟩
          rw [mem_inNeighbors] at hadj
          by_contra hu_not
          have hmem : (u, w) ∈ CascadeModel.untriedEdges G active tried :=
            CascadeModel.mem_untriedEdges.mpr ⟨hu_act, hw, hadj, hu_not⟩
          rw [hemp] at hmem
          exact Finset.notMem_empty _ hmem
        have hreach_closed : ∀ H : Digraph V, H ≤ G →
            (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) →
            liveReachable H active = active := by
          intro H hHG hno
          refine Finset.Subset.antisymm (fun z hz => ?_) (subset_liveReachable H active)
          rcases mem_liveReachable.mp hz with ⟨s, hs, hp⟩
          clear hz
          induction hp with
          | refl => exact hs
          | @tail x y _ hxy ih_p =>
            by_contra hy_not
            have hGxy : G.Adj x y := hHG hxy
            have hx_tr : x ∈ tried y := by
              rw [htr_eq y hy_not]
              exact Finset.mem_inter.mpr ⟨ih_p, mem_inNeighbors.mpr hGxy⟩
            exact hno y hy_not x hx_tr hxy
        by_cases hA : active = A
        · subst hA
          simp only [↓reduceIte, mul_one]
          have hsum_drop_reach :
              (∑ H : Digraph V with
                  (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = active,
                liveGraphWeight IC H) =
              ∑ H : Digraph V with (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w),
                liveGraphWeight IC H := by
            refine Finset.sum_subset (fun H hH => ?_) fun H hH hnot => ?_
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
              exact hH.1
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH hnot
              by_cases hHG : H ≤ G
              · exact absurd ⟨hH, hreach_closed H hHG hH⟩ hnot
              · exact liveGraphWeight_eq_zero_of_not_le IC hHG
          rw [hsum_drop_reach]
          let outEdges : Finset (V × V) :=
            Finset.univ.filter fun e : V × V => e.2 ∉ active ∧ e.1 ∈ tried e.2
          have hbij :
              (∑ H : Digraph V with (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w),
                liveGraphWeight IC H) =
              ∑ E ∈ (Finset.univ : Finset (V × V)).powerset with
                  (∅ : Finset (V × V)) ⊆ E ∧ Disjoint E outEdges,
                ∏ e ∈ (Finset.univ : Finset (V × V)),
                  (if e ∈ E then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) := by
            refine Finset.sum_bij (fun H _ => digraphEquivEdgeFinset V H) ?_ ?_ ?_ ?_
            · intro H hH
              have hno := (Finset.mem_filter.mp hH).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
                Finset.empty_subset _, ?_⟩
              rw [Finset.disjoint_left]
              intro ⟨x, y⟩ hxE hxo
              rcases (Finset.mem_filter.mp hxo).2 with ⟨hy, hxt⟩
              have hadjH : H.Adj x y := by
                simpa [digraphEquivEdgeFinset] using hxE
              exact hno y hy x hxt hadjH
            · intro H₁ _ H₂ _ heq
              exact (digraphEquivEdgeFinset V).injective heq
            · intro E hE
              rcases (Finset.mem_filter.mp hE).2 with ⟨_, hdisjE⟩
              let H := (digraphEquivEdgeFinset V).symm E
              refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
                (digraphEquivEdgeFinset V).apply_symm_apply E⟩
              intro w hw u hu hadjH
              have hmemE : (u, w) ∈ E := hadjH
              have hmemOut : (u, w) ∈ outEdges :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hu⟩
              exact Finset.disjoint_left.mp hdisjE hmemE hmemOut
            · intro H _
              unfold liveGraphWeight
              refine Finset.prod_congr rfl fun ⟨x, y⟩ _ => ?_
              simp [digraphEquivEdgeFinset]
          rw [hbij, sum_powerset_bernWeight _ _ _ _ (Finset.empty_subset _)
            (Finset.subset_univ _) (Finset.disjoint_empty_left _), Finset.prod_empty, one_mul]
          -- Identify `∏ e ∈ outEdges, (1 - IC.edgeProb e.1 e.2)` with `∏ w ∈ activeᶜ, ...`.
          have hout_eq : outEdges =
              activeᶜ.biUnion fun w =>
                (tried w).map ⟨fun x => (x, w), fun _ _ h => congrArg Prod.fst h⟩ := by
            ext ⟨u, w⟩
            rw [Finset.mem_filter, Finset.mem_biUnion]
            simp only [Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_map]
            constructor
            · rintro ⟨hw, hu⟩
              exact ⟨w, hw, u, hu, rfl⟩
            · rintro ⟨w', hw', u', hu', hpair⟩
              change (u', w') = (u, w) at hpair
              cases hpair
              exact ⟨hw', hu'⟩
          rw [hout_eq, Finset.prod_biUnion]
          · refine Finset.prod_congr rfl fun w _ => ?_
            rw [IC.survivalProb_toCascadeModel w (tried w), Finset.prod_map]
            rfl
          · intro w₁ _ w₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro ⟨x, y⟩ h₁ h₂
            rw [Finset.mem_map] at h₁ h₂
            rcases h₁ with ⟨u₁, _, hp₁⟩
            rcases h₂ with ⟨u₂, _, hp₂⟩
            change (u₁, w₁) = (x, y) at hp₁
            change (u₂, w₂) = (x, y) at hp₂
            cases hp₁
            cases hp₂
            exact hne rfl
        · simp only [hA, ↓reduceIte, mul_zero]
          symm
          refine Finset.sum_eq_zero fun H hH => ?_
          rcases (Finset.mem_filter.mp hH).2 with ⟨hno, hreach⟩
          by_cases hHG : H ≤ G
          · exact absurd ((hreach_closed H hHG hno).symm.trans hreach) hA
          · exact liveGraphWeight_eq_zero_of_not_le IC hHG
  exact step_live _ rfl

/-- **Live-Edge Distribution Equivalence** ([KempeKleinbergTardos2003]; [Kleinberg2007],
Section 24.4, pp. 625–626): under any valid attempt schedule `nextEdge`, the Independent Cascade
probability of terminating at active set `A` equals the total weight of realized live-edge graphs
`H` in which `liveReachable H S = A`. -/
theorem activeSetProb_eq_sum_liveGraphWeight
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)}
    (hvalid : CascadeModel.ValidNextEdge G nextEdge) (S A : Finset V) :
    open scoped Classical in
    IC.toCascadeModel.activeSetProb nextEdge S A =
      ∑ H : Digraph V with liveReachable H S = A, liveGraphWeight IC H := by
  classical
  have key := IC.survivalProd_mul_cascadeProbFrom_eq_sum_liveGraphWeight hvalid S (fun _ => ∅)
    (fun _ _ => Finset.empty_subset _) A
  have hprod1 : (∏ w ∈ Sᶜ, IC.toCascadeModel.survivalProb w ∅) = 1 :=
    Finset.prod_eq_one fun w _ => IC.toCascadeModel.survivalProb_empty w
  rw [hprod1, one_mul] at key
  rw [IC.toCascadeModel.activeSetProb_def, key]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext H
  simp

/-- **Live-Edge Expectation Formula** ([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.4,
p. 625): expected influence in the Independent Cascade Model equals the weighted sum of reachable
set sizes `|liveReachable H S|` across all realized live-edge graphs `H : Digraph V`. -/
theorem influence_eq_sum_liveGraphWeight (S : Finset V) :
    IC.influence S = ∑ H : Digraph V, liveGraphWeight IC H * ((liveReachable H S).card : ℝ) := by
  classical
  rw [influence, IC.toCascadeModel.influence_def]
  simp_rw [IC.activeSetProb_eq_sum_liveGraphWeight CascadeModel.validNextEdge_defaultNextEdge,
    Finset.sum_mul]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨A₁, H₁⟩ h₁ ⟨A₂, H₂⟩ h₂ hH
    dsimp only at hH
    subst hH
    have hA₁ : liveReachable H₁ S = A₁ := (Finset.mem_filter.mp (Finset.mem_sigma.mp h₁).2).2
    have hA₂ : liveReachable H₁ S = A₂ := (Finset.mem_filter.mp (Finset.mem_sigma.mp h₂).2).2
    exact Sigma.ext (hA₁.symm.trans hA₂) HEq.rfl
  · intro H _
    exact ⟨⟨liveReachable H S, H⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩,
      rfl⟩
  · rintro ⟨A, H⟩ h
    have hA : liveReachable H S = A := (Finset.mem_filter.mp (Finset.mem_sigma.mp h).2).2
    rw [hA]

@[simp]
theorem influence_empty : IC.influence ∅ = 0 := by
  simp [IC.influence_eq_sum_liveGraphWeight]

theorem monotone_influence : Monotone IC.influence := by
  intro A B hAB
  simp only [IC.influence_eq_sum_liveGraphWeight]
  refine Finset.sum_le_sum fun H _ => ?_
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_card (monotone_liveReachable H hAB)))
    (liveGraphWeight_nonneg IC H)

/-- **Kempe–Kleinberg–Tardos Independent Cascade Submodularity Theorem**
([KempeKleinbergTardos2003]; [Kleinberg2007], Theorem 24.5, pp. 625–626): for every instance of
the Independent Cascade Model, the expected influence function `IC.influence` is submodular. -/
theorem isSubmodular_influence : IsSubmodular IC.influence := by
  have hcov : ∀ H : Digraph V,
      (fun S : Finset V => liveGraphWeight IC H * ((liveReachable H S).card : ℝ)) =
        weightedCoverage (liveReachableFrom H) (fun _ => liveGraphWeight IC H) := by
    intro H
    ext S
    simp [weightedCoverage, liveReachable, mul_comm]
  have heq : IC.influence =
      fun S => ∑ H : Digraph V,
        weightedCoverage (liveReachableFrom H) (fun _ => liveGraphWeight IC H) S := by
    ext S
    rw [IC.influence_eq_sum_liveGraphWeight]
    exact Finset.sum_congr rfl fun H _ => congrFun (hcov H) S
  rw [heq]
  exact isSubmodular_sum Finset.univ fun H _ =>
    isSubmodular_weightedCoverage (liveReachableFrom H) fun _ => liveGraphWeight_nonneg IC H

end IndependentCascadeModel

end LiveEdge

/-! ## Theorem 24.6: Mossel–Roch General Threshold Submodularity -/

section MosselRoch

/-- Order-reversing involution on `Ioo c 1` fixing all points outside `Ioo c 1`. -/
private noncomputable def reflectUnit (c z : ℝ) : ℝ :=
  if z ∈ Ioo c 1 then 1 + c - z else z

private theorem reflectUnit_involutive (c : ℝ) : Function.Involutive (reflectUnit c) := by
  intro z
  unfold reflectUnit
  by_cases hz : z ∈ Ioo c 1
  · have hz' : 1 + c - z ∈ Ioo c 1 := by
      rcases hz with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    simp only [hz, ↓reduceIte, hz']
    ring
  · simp [hz]

private theorem measurable_reflectUnit (c : ℝ) : Measurable (reflectUnit c) :=
  Measurable.ite measurableSet_Ioo (measurable_const.sub measurable_id) measurable_id

private theorem measurePreserving_reflectUnit {c : ℝ} (hc0 : 0 ≤ c) :
    MeasurePreserving (reflectUnit c) unitMeasure unitMeasure where
  measurable := measurable_reflectUnit c
  map_eq := by
    ext s hs
    rw [Measure.map_apply (measurable_reflectUnit c) hs]
    let J := Ioo c 1
    have hJ_sub : J ⊆ Icc 0 1 := fun z hz => ⟨hc0.trans hz.1.le, hz.2.le⟩
    have hpre_split : reflectUnit c ⁻¹' s =
        ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ∩ J) ∪ (s \ J) := by
      ext z
      simp only [mem_preimage, reflectUnit, J, mem_union, mem_inter_iff, mem_sdiff]
      by_cases hz : z ∈ Ioo c 1
      · have hz' : (1 + c) - z ∈ Ioo c 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
        simp [hz, hz']
      · simp [hz]
    have hpre_inJ : (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ⊆ J := by
      intro z hz
      rcases hz.2 with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    have hpre_inter : (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ∩ J =
        (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) :=
      inter_eq_left.mpr hpre_inJ
    rw [hpre_split, hpre_inter]
    have hdisj1 : Disjoint ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) (s \ J) :=
      Disjoint.mono_left hpre_inJ disjoint_sdiff_right
    have hm_sJ : MeasurableSet (s ∩ J) := hs.inter measurableSet_Ioo
    have hm_diff : MeasurableSet (s \ J) := hs.diff measurableSet_Ioo
    have hm_pre : MeasurableSet ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) :=
      hm_sJ.preimage (measurable_const.sub measurable_id)
    rw [measure_union hdisj1 hm_diff]
    have hvol_eq : unitMeasure ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) = unitMeasure (s ∩ J) := by
      rw [unitMeasure_def, Measure.restrict_apply hm_pre, Measure.restrict_apply hm_sJ,
        inter_eq_left.mpr (hpre_inJ.trans hJ_sub),
        inter_eq_left.mpr (inter_subset_right.trans hJ_sub)]
      exact (volume.measurePreserving_sub_left (1 + c)).measure_preimage hm_sJ.nullMeasurableSet
    have hdisj2 : Disjoint (s ∩ J) (s \ J) :=
      Disjoint.mono_left inter_subset_right disjoint_sdiff_right
    rw [hvol_eq, ← measure_union hdisj2 hm_diff, inter_union_sdiff]

private theorem ae_lt_one_thresholdMeasure (V : Type*) [Fintype V] :
    ∀ᵐ θ ∂thresholdMeasure V, ∀ v : V, θ v < 1 := by
  have hae_unit : ∀ᵐ z ∂unitMeasure, z < 1 := by
    rw [ae_iff]
    have hmeas : MeasurableSet {z : ℝ | ¬ z < 1} := by
      simp_rw [not_lt]
      exact measurableSet_Ici
    have hsub : {z : ℝ | ¬ z < 1} ∩ Icc (0 : ℝ) 1 = {1} := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, not_lt, mem_Icc, mem_singleton_iff]
      exact ⟨fun ⟨h1, _, h2⟩ => le_antisymm h2 h1, fun h => ⟨h.ge, h ▸ zero_le_one, h.le⟩⟩
    rw [unitMeasure_def, Measure.restrict_apply hmeas, hsub, Real.volume_singleton]
  rw [thresholdMeasure_def, ae_all_iff]
  intro v
  have hp := MeasureTheory.measurePreserving_eval (fun _ : V => unitMeasure) v
  exact hp.quasiMeasurePreserving.ae hae_unit

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

/-- Coordinatewise threshold reflection outside `K`: preserves `U v` for `v ∈ K` and reflects
`U v ∈ (g_v(K), 1)` to `1 + g_v(K) - U v` for `v ∉ K`. -/
private noncomputable def reflectMap (K : Finset V) (U : V → ℝ) : V → ℝ :=
  fun v => if v ∈ K then U v else reflectUnit (M.thresholdFn v K) (U v)

private theorem reflectMap_involutive (K : Finset V) :
    Function.Involutive (M.reflectMap K) := by
  intro U
  ext v
  unfold reflectMap
  by_cases hv : v ∈ K
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    exact reflectUnit_involutive (M.thresholdFn v K) (U v)

private theorem measurePreserving_reflectMap (K : Finset V) :
    MeasurePreserving (M.reflectMap K) (thresholdMeasure V) (thresholdMeasure V) := by
  rw [thresholdMeasure_def V]
  exact measurePreserving_pi (fun _ : V => unitMeasure) (fun _ : V => unitMeasure)
    (f := fun v z => if v ∈ K then z else reflectUnit (M.thresholdFn v K) z) fun v => by
    by_cases hv : v ∈ K
    · simp only [hv, ↓reduceIte]
      exact MeasurePreserving.id unitMeasure
    · simp only [hv, ↓reduceIte]
      exact measurePreserving_reflectUnit (M.thresholdFn_nonneg v K)

/-- Conditional reflection coupling from seed `X` to superset `Y`: runs `X` under `U` to obtain
`K = M.thresholdFinal U X`, reflects surviving thresholds on `Kᶜ`, and continues from `K ∪ Y`. -/
private noncomputable def reflectCouple (X Y : Finset V) (U : V → ℝ) : Finset V :=
  let K := M.thresholdFinal U X
  M.thresholdFinal (M.reflectMap K U) (K ∪ Y)

/-- **Reflection Marginal-Law Identity** ([MosselRoch2007]): whenever `X ⊆ Y`, `M.reflectCouple X Y`
has the exact same expectation under `thresholdMeasure V` as `U ↦ M.thresholdFinal U Y`. -/
private theorem integral_reflectCouple {X Y : Finset V} (hXY : X ⊆ Y) (φ : Finset V → ℝ) :
    (∫ U, φ (M.reflectCouple X Y U) ∂thresholdMeasure V) =
      ∫ U, φ (M.thresholdFinal U Y) ∂thresholdMeasure V := by
  let E : Finset V → Set (V → ℝ) := fun K =>
    {U : V → ℝ | M.thresholdFinal U X = K ∧ ∀ v : V, U v < 1}
  have hmE : ∀ K : Finset V, MeasurableSet (E K) := by
    intro K
    have heqE : E K = {U | M.thresholdFinal U X = K} ∩
        ⋂ v : V, (fun U : V → ℝ => U v) ⁻¹' Iio 1 := by
      ext U
      simp [E]
    rw [heqE]
    exact (M.measurableSet_thresholdFinal_eq X K).inter
      (MeasurableSet.iInter fun v => measurableSet_Iio.preimage (measurable_pi_apply v))
  have hmem_reflect : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K ↔ M.reflectMap K U ∈ E K := by
    suffices dir : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K → M.reflectMap K U ∈ E K from
      fun K U => ⟨dir K U, fun h => M.reflectMap_involutive K U ▸ dir K _ h⟩
    intro K U ⟨hfin, hlt1⟩
    rw [M.thresholdFinal_eq_iff_piecewise] at hfin
    rcases hfin with ⟨hpiece, hsurv⟩
    have hpiece_eq : K.piecewise (M.reflectMap K U) (fun _ => (2 : ℝ)) =
        K.piecewise U (fun _ => (2 : ℝ)) := by
      ext v
      by_cases hv : v ∈ K
      · simp [reflectMap, hv]
      · simp [Finset.piecewise_eq_of_notMem _ _ _ hv]
    refine ⟨(M.thresholdFinal_eq_iff_piecewise _ X K).mpr ⟨hpiece_eq ▸ hpiece, fun v hvK => ?_⟩,
      fun v => ?_⟩
    · have hmem : U v ∈ Ioo (M.thresholdFn v K) 1 := ⟨hsurv v hvK, hlt1 v⟩
      simp only [reflectMap, hvK, ↓reduceIte, reflectUnit, hmem]
      linarith [hmem.2]
    · by_cases hvK : v ∈ K
      · simp [reflectMap, hvK, hlt1 v]
      · have hmem : U v ∈ Ioo (M.thresholdFn v K) 1 := ⟨hsurv v hvK, hlt1 v⟩
        simp only [reflectMap, hvK, ↓reduceIte, reflectUnit, hmem]
        linarith [hmem.1]
  have hsum_lhs : ∀ᵐ U ∂thresholdMeasure V,
      φ (M.reflectCouple X Y U) =
        ∑ K : Finset V, (E K).indicator (fun U' => φ (M.reflectCouple X Y U')) U := by
    filter_upwards [ae_lt_one_thresholdMeasure V] with U hlt1
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · have hmem : U ∈ E (M.thresholdFinal U X) := ⟨rfl, hlt1⟩
      rw [indicator_of_mem hmem]
    · intro K _ hne
      have hnot : U ∉ E K := fun h => hne h.1.symm
      rw [indicator_of_notMem hnot]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  have hsum_rhs : ∀ᵐ U ∂thresholdMeasure V,
      φ (M.thresholdFinal U Y) =
        ∑ K : Finset V, (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) U := by
    filter_upwards [ae_lt_one_thresholdMeasure V] with U hlt1
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · have hmem : U ∈ E (M.thresholdFinal U X) := ⟨rfl, hlt1⟩
      rw [indicator_of_mem hmem]
    · intro K _ hne
      have hnot : U ∉ E K := fun h => hne h.1.symm
      rw [indicator_of_notMem hnot]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  have hint_piece_rhs : ∀ K : Finset V,
      Integrable ((E K).indicator fun U => φ (M.thresholdFinal U Y)) (thresholdMeasure V) :=
    fun K => (M.integrable_of_finset Y φ).indicator (hmE K)
  have hterm_eq : ∀ (K : Finset V) (U : V → ℝ),
      (E K).indicator (fun U' => φ (M.reflectCouple X Y U')) U =
        (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) := by
    intro K U
    by_cases hU : U ∈ E K
    · have hRU : M.reflectMap K U ∈ E K := (hmem_reflect K U).mp hU
      rw [indicator_of_mem hU, indicator_of_mem hRU]
      dsimp only [reflectCouple]
      rw [hU.1]
      have hYK : K ∪ Y = M.thresholdFinal (M.reflectMap K U) X ∪ Y := by rw [hRU.1]
      rw [hYK, M.thresholdFinal_union_eq, Finset.union_eq_right.mpr hXY]
    · have hRU : M.reflectMap K U ∉ E K := mt (hmem_reflect K U).mpr hU
      rw [indicator_of_notMem hU, indicator_of_notMem hRU]
  have hint_piece_lhs : ∀ K : Finset V,
      Integrable ((E K).indicator fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) := by
    intro K
    have hfn : ((E K).indicator fun U => φ (M.reflectCouple X Y U)) =
        fun U => (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) :=
      funext (hterm_eq K)
    rw [hfn]
    exact (M.measurePreserving_reflectMap K).integrable_comp_of_integrable (hint_piece_rhs K)
  rw [integral_congr_ae hsum_lhs, integral_congr_ae hsum_rhs,
    integral_finsetSum _ (fun K _ => hint_piece_lhs K),
    integral_finsetSum _ (fun K _ => hint_piece_rhs K)]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hfn : ((E K).indicator fun U => φ (M.reflectCouple X Y U)) =
      fun U => (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) :=
    funext (hterm_eq K)
  rw [hfn]
  have hp := M.measurePreserving_reflectMap K
  conv_rhs => rw [← hp.map_eq]
  rw [integral_map hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact (hint_piece_rhs K).aestronglyMeasurable)]

private theorem integrable_reflectCouple (X Y : Finset V) (φ : Finset V → ℝ) :
    Integrable (fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) := by
  have heq : (fun U : V → ℝ => φ (M.reflectCouple X Y U)) =
      fun U => ∑ K : Finset V, ∑ L : Finset V,
        ({U' : V → ℝ | M.thresholdFinal U' X = K} ∩
          {U' : V → ℝ | M.thresholdFinal (M.reflectMap K U') (K ∪ Y) = L}).indicator
          (fun _ => φ L) U := by
    ext U
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · rw [Finset.sum_eq_single (M.reflectCouple X Y U)]
      · simp [reflectCouple]
      · intro L _ hne
        have hnot : U ∉ {U' : V → ℝ | M.thresholdFinal U' X = M.thresholdFinal U X} ∩
            {U' : V → ℝ |
              M.thresholdFinal (M.reflectMap (M.thresholdFinal U X) U')
                (M.thresholdFinal U X ∪ Y) = L} :=
          fun h => hne h.2.symm
        exact indicator_of_notMem hnot _
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · intro K _ hne
      refine Finset.sum_eq_zero fun L _ => ?_
      have hnot : U ∉ {U' : V → ℝ | M.thresholdFinal U' X = K} ∩
          {U' : V → ℝ | M.thresholdFinal (M.reflectMap K U') (K ∪ Y) = L} :=
        fun h => hne h.1.symm
      exact indicator_of_notMem hnot _
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [heq]
  refine integrable_finsetSum _ fun K _ => integrable_finsetSum _ fun L _ => ?_
  refine (integrable_const (φ L)).indicator ((M.measurableSet_thresholdFinal_eq X K).inter ?_)
  exact (M.measurableSet_thresholdFinal_eq (K ∪ Y) L).preimage
    (M.measurePreserving_reflectMap K).measurable

/-- Monotonicity of general threshold expectations for any monotone objective `φ`. -/
theorem monotone_integral_thresholdFinal {φ : Finset V → ℝ} (hmono : Monotone φ) :
    Monotone (fun S : Finset V => ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) := by
  intro A B hAB
  exact integral_mono (M.integrable_of_finset A φ) (M.integrable_of_finset B φ) fun θ =>
    hmono (M.thresholdFinal_mono_seed θ hAB)

/-- **Mossel–Roch Functional Submodularity Theorem** ([MosselRoch2007]; generalizing
[Kleinberg2007], Theorem 24.6, p. 626): if every local threshold function `M.thresholdFn v` is
submodular, then for every monotone submodular objective `φ : Finset V → ℝ`, the expected value
`S ↦ ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V` is submodular. -/
theorem isSubmodular_integral_thresholdFinal
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v))
    {φ : Finset V → ℝ} (hφ_mono : Monotone φ) (hφ_sub : IsSubmodular φ) :
    IsSubmodular (fun S : Finset V => ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) := by
  intro A B
  dsimp only
  rw [← M.integral_reflectCouple (Finset.subset_union_left (s₁ := A) (s₂ := B)) φ,
    ← M.integral_reflectCouple (Finset.inter_subset_right (s₁ := A) (s₂ := B)) φ]
  have hintD := M.integrable_reflectCouple A (A ∪ B) φ
  have hintB := M.integrable_reflectCouple (A ∩ B) B φ
  rw [← integral_add hintD (M.integrable_of_finset (A ∩ B) φ),
    ← integral_add (M.integrable_of_finset A φ) hintB]
  refine integral_mono_ae (hintD.add (M.integrable_of_finset (A ∩ B) φ))
    ((M.integrable_of_finset A φ).add hintB) ?_
  filter_upwards [ae_lt_one_thresholdMeasure V] with U hlt1
  set Cstar := M.thresholdFinal U (A ∩ B)
  set Astar := M.thresholdFinal U A
  set Bstar := M.reflectCouple (A ∩ B) B U
  set Dstar := M.reflectCouple A (A ∪ B) U
  have hCA : Cstar ⊆ Astar := M.thresholdFinal_mono_seed U Finset.inter_subset_left
  have hCB : Cstar ⊆ Bstar :=
    Finset.subset_union_left.trans (M.subset_thresholdFinal (M.reflectMap Cstar U) (Cstar ∪ B))
  have hC_inter : Cstar ⊆ Astar ∩ Bstar := Finset.subset_inter hCA hCB
  -- Show `Dstar ⊆ Astar ∪ Bstar` via the least post-fixed point property of `thresholdFinal`.
  have hD_union : Dstar ⊆ Astar ∪ Bstar := by
    have hD_eq : Dstar = M.thresholdFinal (M.reflectMap Astar U) (Astar ∪ B) := by
      have hunion : Astar ∪ (A ∪ B) = Astar ∪ B := by
        have hAsub : A ⊆ Astar := M.subset_thresholdFinal U A
        ext v
        simp only [Finset.mem_union]
        exact ⟨fun h => h.elim Or.inl fun h' => h'.elim (fun hvA => Or.inl (hAsub hvA)) Or.inr,
          fun h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩
      change M.thresholdFinal (M.reflectMap Astar U) (Astar ∪ (A ∪ B)) = _
      rw [hunion]
    rw [hD_eq]
    have hB_sub : B ⊆ Bstar :=
      Finset.subset_union_right.trans (M.subset_thresholdFinal (M.reflectMap Cstar U) (Cstar ∪ B))
    refine M.thresholdFinal_subset_of_lt (Finset.union_subset_union_right hB_sub) fun v hvAB => ?_
    have hvA : v ∉ Astar := fun h => hvAB (Finset.mem_union_left _ h)
    have hvB : v ∉ Bstar := fun h => hvAB (Finset.mem_union_right _ h)
    have hvC : v ∉ Cstar := fun h => hvA (hCA h)
    have hA_lt : M.thresholdFn v Astar < U v := M.thresholdFn_lt_of_notMem_thresholdFinal hvA
    have hC_lt : M.thresholdFn v Cstar < U v := M.thresholdFn_lt_of_notMem_thresholdFinal hvC
    have hB_lt : M.thresholdFn v Bstar < M.reflectMap Cstar U v :=
      M.thresholdFn_lt_of_notMem_thresholdFinal hvB
    have hRA : M.reflectMap Astar U v = 1 + M.thresholdFn v Astar - U v := by
      have hmem : U v ∈ Ioo (M.thresholdFn v Astar) 1 := ⟨hA_lt, hlt1 v⟩
      simp [reflectMap, hvA, reflectUnit, hmem]
    have hRC : M.reflectMap Cstar U v = 1 + M.thresholdFn v Cstar - U v := by
      have hmem : U v ∈ Ioo (M.thresholdFn v Cstar) 1 := ⟨hC_lt, hlt1 v⟩
      simp [reflectMap, hvC, reflectUnit, hmem]
    have hsub_v := hlocal v Astar Bstar
    have hC_le_inter : M.thresholdFn v Cstar ≤ M.thresholdFn v (Astar ∩ Bstar) :=
      M.monotone v hC_inter
    rw [hRA]
    rw [hRC] at hB_lt
    linarith
  calc φ Dstar + φ Cstar
      ≤ φ (Astar ∪ Bstar) + φ (Astar ∩ Bstar) :=
        add_le_add (hφ_mono hD_union) (hφ_mono hC_inter)
    _ ≤ φ Astar + φ Bstar := hφ_sub Astar Bstar

/-- **Mossel–Roch General Threshold Submodularity Theorem** ([MosselRoch2007]; [Kleinberg2007],
Theorem 24.6, p. 626): for any instance of the General Threshold Model in which all local threshold
functions `M.thresholdFn v` are submodular, the global expected influence function `M.influence` is
submodular. -/
theorem isSubmodular_influence (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) :
    IsSubmodular M.influence := by
  have heq : M.influence = fun S => ∫ θ, ((M.thresholdFinal θ S).card : ℝ) ∂thresholdMeasure V :=
    funext M.influence_def
  rw [heq]
  have hcard_mono : Monotone (fun X : Finset V => (X.card : ℝ)) :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card h)
  have hcard_sub : IsSubmodular (fun X : Finset V => (X.card : ℝ)) := by
    intro A B
    dsimp only
    exact_mod_cast (Finset.card_union_add_card_inter A B).le
  exact M.isSubmodular_integral_thresholdFinal hlocal hcard_mono hcard_sub

/-- Lifting a locally submodular `GeneralThresholdModel` to `timeLayeredDigraph G T` preserves
submodularity of all local threshold functions. -/
theorem isSubmodular_toTimeLayered_thresholdFn
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) (T : ℕ)
    (vt : V × Fin (T + 1)) :
    IsSubmodular ((M.toTimeLayered T).thresholdFn vt) := by
  intro A B
  simp only [M.toTimeLayered_thresholdFn]
  split_ifs with h0
  · simp
  · set prev : Fin (T + 1) := ⟨(vt.2 : ℕ) - 1, by omega⟩
    let slice : Finset (V × Fin (T + 1)) → Finset V :=
      fun X => Finset.univ.filter fun u => (u, prev) ∈ X
    have hU : slice (A ∪ B) = slice A ∪ slice B := by
      ext u
      simp [slice]
    have hI : slice (A ∩ B) = slice A ∩ slice B := by
      ext u
      simp [slice]
    change M.thresholdFn vt.1 (slice (A ∪ B)) + M.thresholdFn vt.1 (slice (A ∩ B)) ≤
      M.thresholdFn vt.1 (slice A) + M.thresholdFn vt.1 (slice B)
    rw [hU, hI]
    exact hlocal vt.1 (slice A) (slice B)

/-- Monotonicity of expected step-`t` active count in the `T`-step nonprogressive threshold
process ([Kleinberg2007], Section 24.3, p. 622). -/
theorem monotone_nonprogStepInfluence (T : ℕ) (t : Fin (T + 1)) :
    Monotone (M.nonprogStepInfluence T t) := by
  intro A B hAB
  rw [M.nonprogStepInfluence_eq_toTimeLayered, M.nonprogStepInfluence_eq_toTimeLayered]
  have hφ_mono : Monotone (fun X : Finset (V × Fin (T + 1)) =>
      ((X.filter (·.2 = t)).card : ℝ)) :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h))
  exact (M.toTimeLayered T).monotone_integral_thresholdFinal hφ_mono
    (by
      intro x hx
      rcases mem_seedLayer0.mp hx with ⟨h0, hxA⟩
      exact mem_seedLayer0.mpr ⟨h0, hAB hxA⟩)

/-- Submodularity of expected step-`t` active count in the `T`-step nonprogressive threshold
process via `timeLayeredDigraph G T` and Theorem 24.6 ([KempeKleinbergTardos2003];
[MosselRoch2007]; [Kleinberg2007], Sections 24.3–24.4, pp. 622, 626). -/
theorem isSubmodular_nonprogStepInfluence
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) (T : ℕ) (t : Fin (T + 1)) :
    IsSubmodular (M.nonprogStepInfluence T t) := by
  intro A B
  simp only [M.nonprogStepInfluence_eq_toTimeLayered, seedLayer0_union, seedLayer0_inter]
  let φ : Finset (V × Fin (T + 1)) → ℝ := fun X => ((X.filter (·.2 = t)).card : ℝ)
  have hφ_mono : Monotone φ :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h))
  have hφ_sub : IsSubmodular φ := by
    intro X Y
    dsimp only [φ]
    have hfU : (X ∪ Y).filter (·.2 = t) = X.filter (·.2 = t) ∪ Y.filter (·.2 = t) :=
      Finset.filter_union _ _ _
    have hfI : (X ∩ Y).filter (·.2 = t) = X.filter (·.2 = t) ∩ Y.filter (·.2 = t) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      tauto
    rw [hfU, hfI]
    exact_mod_cast (Finset.card_union_add_card_inter _ _).le
  exact (M.toTimeLayered T).isSubmodular_integral_thresholdFinal
    (M.isSubmodular_toTimeLayered_thresholdFn hlocal T) hφ_mono hφ_sub
    (seedLayer0 T A) (seedLayer0 T B)

end GeneralThresholdModel

/-! ### Linear Threshold Model Specialization -/

namespace LinearThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (L : LinearThresholdModel G)

/-- Every local threshold function of a `LinearThresholdModel` is modular, hence submodular
([Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (v : V) :
    IsSubmodular (L.toGeneralThresholdModel.thresholdFn v) := by
  have heq : L.toGeneralThresholdModel.thresholdFn v = modularSum (fun u => L.weight u v) := by
    ext X
    simp [modularSum]
  rw [heq]
  exact isSubmodular_modularSum _

/-- Expected influence in any `LinearThresholdModel` is submodular
([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_influence : IsSubmodular L.toGeneralThresholdModel.influence :=
  L.toGeneralThresholdModel.isSubmodular_influence
    L.isSubmodular_toGeneralThresholdModel_thresholdFn

end LinearThresholdModel

end MosselRoch

/-! ## Theorem 24.4: Diminishing-Returns Cascade Submodularity -/

namespace CascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (C : CascadeModel G)

@[simp]
theorem influence_empty : C.influence ∅ = 0 := by
  rw [C.influence_eq_toGeneralThresholdModel, C.toGeneralThresholdModel.influence_empty]

theorem monotone_influence : Monotone C.influence := by
  intro A B hAB
  rw [C.influence_eq_toGeneralThresholdModel, C.influence_eq_toGeneralThresholdModel]
  exact C.toGeneralThresholdModel.monotone_influence hAB

/-- If a `CascadeModel` has diminishing-returns incremental probabilities (`HasDiminishingReturns`),
every local threshold function of `C.toGeneralThresholdModel` is submodular
([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (hdim : C.HasDiminishingReturns)
    (v : V) : IsSubmodular (C.toGeneralThresholdModel.thresholdFn v) := by
  rw [isSubmodular_iff_marginalGain_le]
  intro X Y u hXY huY
  have huX : u ∉ X := fun h => huY (hXY h)
  have hgain : ∀ {Z : Finset V}, u ∉ Z →
      marginalGain (C.toGeneralThresholdModel.thresholdFn v) Z u =
        C.survivalProb v Z * C.prob v u Z := by
    intro Z huZ
    simp only [marginalGain, toGeneralThresholdModel_thresholdFn, C.survivalProb_insert v huZ]
    ring
  rw [hgain huY, hgain huX]
  exact mul_le_mul (C.survivalProb_anti v hXY) (hdim v u hXY huY)
    (C.prob_nonneg v u Y) (C.survivalProb_nonneg v X)

/-- **Kempe–Kleinberg–Tardos Diminishing-Returns Cascade Submodularity Theorem**
([KempeKleinbergTardos2003]; [KempeKleinbergTardos2005]; [Kleinberg2007], Theorem 24.4,
pp. 624, 626): for any instance of the Cascade Model whose incremental functions satisfy
`HasDiminishingReturns`, the resulting expected influence function `C.influence` is submodular. -/
theorem isSubmodular_influence_of_diminishingReturns (hdim : C.HasDiminishingReturns) :
    IsSubmodular C.influence := by
  have heq : C.influence = C.toGeneralThresholdModel.influence :=
    funext C.influence_eq_toGeneralThresholdModel
  rw [heq]
  exact C.toGeneralThresholdModel.isSubmodular_influence
    (C.isSubmodular_toGeneralThresholdModel_thresholdFn hdim)

end CascadeModel

/-! ## Greedy `(1 - 1/e)` Influence Maximization Guarantees (Theorem 24.3 + Theorems 24.4–24.6) -/

section GreedyGuarantees

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]

/-- **`(1 - 1/e)` Greedy Influence Maximization for Locally Submodular Threshold Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [MosselRoch2007]; [Kleinberg2007],
Theorems 24.3 and 24.6, pp. 623–626): `k`-step `submodularGreedy` achieves at least
`(1 - Real.exp (-1)) * M.influence OPT` against every `OPT ⊆ xs.toFinset` with `OPT.card ≤ k`. -/
theorem GeneralThresholdModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (M : GeneralThresholdModel G) (hlocal : ∀ v, IsSubmodular (M.thresholdFn v))
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * M.influence OPT ≤
      M.influence (submodularGreedy M.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy (M.isSubmodular_influence hlocal)
    M.monotone_influence M.influence_empty.ge xs k hOPT_sub hOPT_card

/-- **`(1 - 1/e)` Greedy Influence Maximization for Diminishing-Returns Cascade Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [KempeKleinbergTardos2005];
[Kleinberg2007], Theorems 24.3 and 24.4, pp. 623–626). -/
theorem CascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (C : CascadeModel G) (hdim : C.HasDiminishingReturns)
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * C.influence OPT ≤
      C.influence (submodularGreedy C.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy
    (C.isSubmodular_influence_of_diminishingReturns hdim)
    C.monotone_influence C.influence_empty.ge xs k hOPT_sub hOPT_card

/-- **`(1 - 1/e)` Greedy Influence Maximization for Independent Cascade Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [Kleinberg2007], Theorems 24.3 and 24.5,
pp. 623–626). -/
theorem IndependentCascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (IC : IndependentCascadeModel G)
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * IC.influence OPT ≤
      IC.influence (submodularGreedy IC.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy IC.isSubmodular_influence
    IC.monotone_influence IC.influence_empty.ge xs k hOPT_sub hOPT_card

end GreedyGuarantees

end Cslib.GameTheory.Network
