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
  simp [liveReachableFrom]

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
  exacts [IC.edgeProb_nonneg e.1 e.2, sub_nonneg.mpr (IC.edgeProb_le_one e.1 e.2)]

private theorem liveGraphWeight_eq_zero_of_not_le {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) {H : Digraph V} (hnot : ¬ H ≤ G) :
    liveGraphWeight IC H = 0 := by
  classical
  unfold liveGraphWeight
  by_contra hne
  exact hnot fun u v huv => by
    by_contra hno
    exact hne (Finset.prod_eq_zero (Finset.mem_univ (u, v))
      (by simp [huv, IC.edgeProb_eq_zero_of_not_adj u v hno]))

/-- Sum of independent Bernoulli product weights over subsets `E ⊆ U` containing `inSet` and
disjoint from `outSet`. -/
private theorem sum_powerset_bernWeight {α : Type*} [DecidableEq α] (p : α → ℝ)
    (U inSet outSet : Finset α) (hin : inSet ⊆ U) (hout : outSet ⊆ U)
    (hdisj : Disjoint inSet outSet) :
    (∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E outSet,
        ∏ a ∈ U, (if a ∈ E then p a else 1 - p a)) =
      (∏ a ∈ inSet, p a) * (∏ a ∈ outSet, (1 - p a)) := by
  let f (a : α) : ℝ := if a ∈ outSet then 0 else p a
  let g (a : α) : ℝ := if a ∈ inSet then 0 else 1 - p a
  have hlhs : ∏ a ∈ U, (f a + g a) = (∏ a ∈ inSet, p a) * (∏ a ∈ outSet, (1 - p a)) := by
    have hfree : ∏ a ∈ U \ (inSet ∪ outSet), (f a + g a) = 1 := Finset.prod_eq_one fun a ha => by
      rcases Finset.notMem_union.mp (Finset.mem_sdiff.mp ha).2 with ⟨h1, h2⟩
      simp only [f, g, h1, h2, ↓reduceIte]; ring
    rw [← Finset.prod_sdiff (Finset.union_subset hin hout), hfree, one_mul, Finset.prod_union hdisj]
    congr 1
    · exact Finset.prod_congr rfl fun a ha => by
        simp [f, g, ha, Finset.disjoint_left.mp hdisj ha]
    · exact Finset.prod_congr rfl fun a ha => by
        simp [f, g, ha, Finset.disjoint_right.mp hdisj ha]
  rw [← hlhs, Finset.prod_add,
    ← Finset.sum_subset (Finset.filter_subset (fun E => inSet ⊆ E ∧ Disjoint E outSet) U.powerset)]
  · refine Finset.sum_congr rfl fun E hE => ?_
    rcases Finset.mem_filter.mp hE with ⟨hEU, hinE, hEout⟩
    rw [← Finset.prod_sdiff (Finset.mem_powerset.mp hEU), mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun a ha => by simp [f, ha, Finset.disjoint_left.mp hEout ha]
    · exact Finset.prod_congr rfl fun a ha => by
        rcases Finset.mem_sdiff.mp ha with ⟨_, haE⟩
        simp [g, haE, mt (@hinE a) haE]
  · intro E hEU hnot
    rw [Finset.mem_filter] at hnot
    by_cases h1 : inSet ⊆ E
    · obtain ⟨a, haE, haout⟩ := Finset.not_disjoint_iff.mp fun h => hnot ⟨hEU, h1, h⟩
      exact mul_eq_zero_of_left (Finset.prod_eq_zero haE (by simp [f, haout])) _
    · obtain ⟨a, hain, haE⟩ := Finset.not_subset.mp h1
      exact mul_eq_zero_of_right _
        (Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hin hain, haE⟩) (by simp [g, hain]))

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
@[expose] noncomputable def influence (S : Finset V) : ℝ :=
  IC.toCascadeModel.influence S

private theorem survivalProb_toCascadeModel (w : V) (X : Finset V) :
    IC.toCascadeModel.survivalProb w X = ∏ u ∈ X, (1 - IC.edgeProb u w) := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    rw [IC.toCascadeModel.survivalProb_insert w hu, ih, Finset.prod_insert hu, mul_comm,
      IC.toCascadeModel_prob]

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
  let toE := digraphEquivEdgeFinset V
  -- Independence on a subset `F` of potential edges: when `P` depends only on `Fᶜ` and
  -- `inE, outE ⊆ F` are disjoint, the Bernoulli weight factors into `inE`/`outE` times `Fᶜ`.
  have hfactor : ∀ (F inE outE : Finset (V × V)) (P : Digraph V → Prop) [DecidablePred P],
      inE ⊆ F → outE ⊆ F → Disjoint inE outE →
      (∀ H₁ H₂ : Digraph V, (∀ e ∉ F, H₁.Adj e.1 e.2 ↔ H₂.Adj e.1 e.2) → (P H₁ ↔ P H₂)) →
      (∑ H : Digraph V with P H ∧ (∀ e ∈ inE, H.Adj e.1 e.2) ∧ (∀ e ∈ outE, ¬ H.Adj e.1 e.2),
        liveGraphWeight IC H) =
      ((∏ e ∈ inE, IC.edgeProb e.1 e.2) * (∏ e ∈ outE, (1 - IC.edgeProb e.1 e.2))) *
        ∑ E₀ ∈ (Finset.univ \ F).powerset with P (toE.symm E₀),
          ∏ e ∈ Finset.univ \ F,
            if e ∈ E₀ then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
    intro F inE outE P _ hin hout hdisj hP
    let R := (Finset.univ \ F).powerset.filter fun E₀ => P (toE.symm E₀)
    let FV := F.powerset.filter fun E₁ => inE ⊆ E₁ ∧ Disjoint E₁ outE
    have hbij : (∑ H : Digraph V with P H ∧ (∀ e ∈ inE, H.Adj e.1 e.2) ∧
          (∀ e ∈ outE, ¬ H.Adj e.1 e.2), liveGraphWeight IC H) =
        ∑ q ∈ R ×ˢ FV,
          (∏ e ∈ Finset.univ \ F,
            if e ∈ q.1 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
          (∏ e ∈ F, if e ∈ q.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) := by
      refine Finset.sum_bij' (fun H _ => (toE H \ F, toE H ∩ F))
        (fun q _ => toE.symm (q.1 ∪ q.2)) ?_ ?_ ?_ ?_ ?_
      · intro H hH
        rcases (Finset.mem_filter.mp hH).2 with ⟨hPH, hHin, hHout⟩
        refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl),
            (hP H _ fun e he => by simp [toE, digraphEquivEdgeFinset, he]).mp hPH⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
            Finset.subset_inter
              (fun e he => by simpa [toE, digraphEquivEdgeFinset] using hHin e he) hin,
            Finset.disjoint_left.mpr fun e he heo => hHout e heo
              (by simpa [toE, digraphEquivEdgeFinset] using (Finset.mem_inter.mp he).1)⟩⟩
      · rintro ⟨E₀, E₁⟩ hq
        rcases Finset.mem_product.mp hq with ⟨hR, hFV⟩
        rcases Finset.mem_filter.mp hR with ⟨hE₀_sub, hPE₀⟩
        rcases Finset.mem_filter.mp hFV with ⟨hE₁_sub, hinE₁, hdisjE₁⟩
        have hE₀F := Finset.mem_powerset.mp hE₀_sub
        have hE₁F := Finset.mem_powerset.mp hE₁_sub
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hP _ _ fun e he => by simp [toE, digraphEquivEdgeFinset, mt (@hE₁F e) he]).mpr hPE₀,
          fun e he => Finset.mem_union.mpr (Or.inr (hinE₁ he)),
          fun e he => by
            have he₀ : e ∉ E₀ := fun h => (Finset.mem_sdiff.mp (hE₀F h)).2 (hout he)
            have he₁ : e ∉ E₁ := fun h => Finset.disjoint_left.mp hdisjE₁ h he
            simp [toE, digraphEquivEdgeFinset, he₀, he₁]⟩
      · intro H _
        rw [Finset.sdiff_union_inter, toE.symm_apply_apply]
      · rintro ⟨E₀, E₁⟩ hq
        rcases Finset.mem_product.mp hq with ⟨hR, hFV⟩
        have hE₀F := Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1
        have hE₁F := Finset.mem_powerset.mp (Finset.mem_filter.mp hFV).1
        rw [toE.apply_symm_apply]
        refine Prod.ext (Finset.ext fun e => ?_) (Finset.ext fun e => ?_) <;>
          simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
        · exact ⟨fun ⟨h, heF⟩ => h.resolve_right fun h1 => heF (hE₁F h1),
            fun h => ⟨Or.inl h, (Finset.mem_sdiff.mp (hE₀F h)).2⟩⟩
        · exact ⟨fun ⟨h, heF⟩ => h.resolve_left fun h0 => (Finset.mem_sdiff.mp (hE₀F h0)).2 heF,
            fun h => ⟨Or.inr h, hE₁F h⟩⟩
      · intro H _
        unfold liveGraphWeight
        rw [← Finset.prod_sdiff (Finset.subset_univ F)]
        congr 1
        · exact Finset.prod_congr rfl fun e he => by
            simp [toE, digraphEquivEdgeFinset, (Finset.mem_sdiff.mp he).2]
        · exact Finset.prod_congr rfl fun e he => by simp [toE, digraphEquivEdgeFinset, he]
    rw [hbij, Finset.sum_product, mul_comm,
      ← sum_powerset_bernWeight (fun e => IC.edgeProb e.1 e.2) F inE outE hin hout hdisj,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => ?_
    dsimp only
    rw [Finset.mul_sum]
  have h0 := IC.toCascadeModel.activeSetProb_eq_of_step hvalid S A
    (fun active tried =>
      ∑ H : Digraph V with
          (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = A,
        liveGraphWeight IC H)
    (fun active tried htr_eq => by
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
          by_contra hy_act
          exact hno y hy_act x
            (htr_eq y hy_act ▸ Finset.mem_inter.mpr ⟨ih_p, mem_inNeighbors.mpr (hHG hxy)⟩) hxy
      by_cases hA : active = A
      · subst hA
        simp only [↓reduceIte]
        let outEdges : Finset (V × V) := activeᶜ.biUnion fun w =>
          (tried w).map ⟨fun x => (x, w), fun _ _ h => congrArg Prod.fst h⟩
        have hdrop : (∑ H : Digraph V with
              (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = active,
            liveGraphWeight IC H) =
            ∑ H : Digraph V with True ∧ (∀ e ∈ (∅ : Finset (V × V)), H.Adj e.1 e.2) ∧
              (∀ e ∈ outEdges, ¬ H.Adj e.1 e.2), liveGraphWeight IC H := by
          have hmem_out {H : Digraph V} :
              (∀ e ∈ outEdges, ¬ H.Adj e.1 e.2) ↔ ∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w := by
            simp only [outEdges, Finset.mem_biUnion, Finset.mem_compl, Finset.mem_map]
            exact ⟨fun h w hw u hu => h (u, w) ⟨w, hw, u, hu, rfl⟩,
              fun h _ ⟨_, hw', _, hu', heq⟩ => heq ▸ h _ hw' _ hu'⟩
          refine Finset.sum_subset (fun H hH => ?_) fun H hH hnot => ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty, IsEmpty.forall_iff,
              implies_true, true_and, hmem_out] at hH ⊢
            exact hH.1
          · simp only [Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty, IsEmpty.forall_iff,
              implies_true, true_and, hmem_out] at hH hnot
            exact if hHG : H ≤ G then absurd ⟨hH, hreach_closed H hHG hH⟩ hnot
              else liveGraphWeight_eq_zero_of_not_le IC hHG
        rw [hdrop, hfactor Finset.univ ∅ outEdges (fun _ => True) (Finset.empty_subset _)
          (Finset.subset_univ _) (Finset.disjoint_empty_left _) (fun _ _ _ => Iff.rfl),
          Finset.sdiff_self, Finset.powerset_empty,
          Finset.filter_true_of_mem (fun _ _ => trivial)]
        simp only [Finset.sum_singleton, Finset.prod_empty, one_mul, mul_one]
        rw [Finset.prod_biUnion]
        · exact Finset.prod_congr rfl fun w _ =>
            (Finset.prod_map _ _ _).trans (IC.survivalProb_toCascadeModel w (tried w)).symm
        · intro w₁ _ w₂ _ hne
          refine Finset.disjoint_left.mpr fun ⟨x, y⟩ h₁ h₂ => hne ?_
          rcases Finset.mem_map.mp h₁ with ⟨_, _, ⟨⟩⟩
          rcases Finset.mem_map.mp h₂ with ⟨_, _, ⟨⟩⟩
          rfl
      · simp only [hA, ↓reduceIte]
        refine Finset.sum_eq_zero fun H hH => ?_
        rcases (Finset.mem_filter.mp hH).2 with ⟨hno, hreach⟩
        exact if hHG : H ≤ G then absurd ((hreach_closed H hHG hno).symm.trans hreach) hA
          else liveGraphWeight_eq_zero_of_not_le IC hHG)
    (fun active tried _ u v hu_act hv_inact _ hu_untried => by
      let tried' := Function.update tried v (insert u (tried v))
      let S_all := Finset.univ.filter fun H : Digraph V =>
        (∀ w ∉ active, ∀ x ∈ tried w, ¬ H.Adj x w) ∧ liveReachable H active = A
      change ∑ H ∈ S_all, liveGraphWeight IC H =
        IC.toCascadeModel.prob v u (tried v) * IC.toCascadeModel.survivalProb v (tried v) *
          (∑ H : Digraph V with
              (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                liveReachable H (insert v active) = A,
            liveGraphWeight IC H) +
          (∑ H : Digraph V with
              (∀ w ∉ active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧ liveReachable H active = A,
            liveGraphWeight IC H)
      rw [← Finset.sum_filter_add_sum_filter_not S_all (fun H : Digraph V => H.Adj u v),
        IC.toCascadeModel_prob]
      congr 1
      · -- `H.Adj u v` branch: factor out incoming edges to `v`.
        let F : Finset (V × V) := Finset.univ.filter fun e => e.2 = v
        let P (H : Digraph V) : Prop :=
          (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
            liveReachable H (insert v active) = A
        let outV : Finset (V × V) :=
          (tried v).map ⟨fun x => (x, v), fun _ _ h => congrArg Prod.fst h⟩
        have hP : ∀ H₁ H₂ : Digraph V,
            (∀ e ∉ F, H₁.Adj e.1 e.2 ↔ H₂.Adj e.1 e.2) → (P H₁ ↔ P H₂) := by
          intro H₁ H₂ heq
          have heq' : ∀ x y, y ≠ v → (H₁.Adj x y ↔ H₂.Adj x y) := fun x y hy =>
            heq (x, y) (by simp [F, hy])
          have hr := liveReachable_congr_inEdges (Finset.mem_insert_self v active) heq'
          exact and_congr (forall_congr' fun w => imp_congr_right fun hw =>
            forall₂_congr fun x _ => not_congr
              (heq' x w fun h => hw (Finset.mem_insert.mpr (Or.inl h))))
            (by rw [hr])
        have hreach_ins (H : Digraph V) (huvH : H.Adj u v) :
            liveReachable H active = liveReachable H (insert v active) :=
          Finset.Subset.antisymm (monotone_liveReachable H (Finset.subset_insert v active))
            fun z hz => by
              rcases mem_liveReachable.mp hz with ⟨s, hs, hp⟩
              rcases Finset.mem_insert.mp hs with rfl | hs_act
              exacts [mem_liveReachable.mpr
                  ⟨u, hu_act, (Relation.ReflTransGen.single huvH).trans hp⟩,
                mem_liveReachable.mpr ⟨s, hs_act, hp⟩]
        have hlhs_eq : (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) =
            ∑ H : Digraph V with P H ∧ (∀ e ∈ ({(u, v)} : Finset (V × V)), H.Adj e.1 e.2) ∧
              (∀ e ∈ outV, ¬ H.Adj e.1 e.2), liveGraphWeight IC H := by
          refine Finset.sum_congr (Finset.ext fun H => ?_) fun _ _ => rfl
          simp only [S_all, P, outV, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, forall_eq, Finset.mem_map]
          constructor
          · rintro ⟨⟨hno, hr⟩, huvH⟩
            refine ⟨⟨fun w hw x hx => ?_, (hreach_ins H huvH).symm.trans hr⟩, huvH, ?_⟩
            · rcases not_or.mp (mt Finset.mem_insert.mpr hw) with ⟨hwv, hwa⟩
              exact hno w hwa x (by simpa only [tried', Function.update_of_ne hwv] using hx)
            · rintro ⟨x, y⟩ ⟨_, hx', ⟨⟩⟩
              exact hno v hv_inact x hx'
          · rintro ⟨⟨hno, hr⟩, huvH, hout⟩
            refine ⟨⟨fun w hw x hx => ?_, (hreach_ins H huvH).trans hr⟩, huvH⟩
            rcases eq_or_ne w v with rfl | hwv
            · exact hout (x, w) ⟨x, hx, rfl⟩
            · exact hno w (fun h => (Finset.mem_insert.mp h).elim hwv hw) x
                (by simpa only [tried', Function.update_of_ne hwv] using hx)
        have hrhs_eq : (∑ H : Digraph V with P H, liveGraphWeight IC H) =
            ∑ E₀ ∈ (Finset.univ \ F).powerset with P (toE.symm E₀),
              ∏ e ∈ Finset.univ \ F,
                if e ∈ E₀ then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
          simpa only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
            Finset.prod_empty, one_mul] using hfactor F ∅ ∅ P (Finset.empty_subset _)
              (Finset.empty_subset _) (Finset.disjoint_empty_left _) hP
        rw [hlhs_eq, hfactor F {(u, v)} outV P
          (Finset.singleton_subset_iff.mpr (by simp [F]))
          (Finset.forall_mem_map.mpr fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
          (Finset.disjoint_singleton_left.mpr fun h => by
            rcases Finset.mem_map.mp h with ⟨_, hx, ⟨⟩⟩
            exact hu_untried hx)
          hP, ← hrhs_eq, Finset.prod_singleton, IC.survivalProb_toCascadeModel v (tried v),
          Finset.prod_map]
        rfl
      · -- `¬ H.Adj u v` branch: identical filter to `tried'`.
        refine Finset.sum_congr (Finset.ext fun H => ?_) fun _ _ => rfl
        simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨hno, hr⟩, hnuv⟩ => ⟨fun w hw x hx => by
            rcases eq_or_ne w v with rfl | hwv
            · rcases Finset.mem_insert.mp (by simpa [tried'] using hx) with rfl | hxt
              exacts [hnuv, hno w hv_inact x hxt]
            · exact hno w hw x (by simpa [tried', Function.update_of_ne hwv] using hx), hr⟩,
          fun ⟨hno', hr⟩ => ⟨⟨fun w hw x hx => by
            rcases eq_or_ne w v with rfl | hwv
            · exact hno' w hv_inact x (by simp [tried', hx])
            · exact hno' w hw x (by simp [tried', Function.update_of_ne hwv, hx]), hr⟩,
            hno' v hv_inact u (by simp [tried'])⟩⟩)
  rw [h0]
  exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl

/-- **Live-Edge Expectation Formula** ([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.4,
p. 625): expected influence in the Independent Cascade Model equals the weighted sum of reachable
set sizes `|liveReachable H S|` across all realized live-edge graphs `H : Digraph V`. -/
theorem influence_eq_sum_liveGraphWeight (S : Finset V) :
    IC.influence S = ∑ H : Digraph V, liveGraphWeight IC H * ((liveReachable H S).card : ℝ) := by
  classical
  rw [influence, IC.toCascadeModel.influence_def]
  simp_rw [IC.activeSetProb_eq_sum_liveGraphWeight CascadeModel.validNextEdge_defaultNextEdge,
    Finset.sum_mul]
  exact (Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun H hH => by
    rw [(Finset.mem_filter.mp hH).2]).trans
    (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _)

@[simp]
theorem influence_empty : IC.influence ∅ = 0 :=
  IC.toCascadeModel.influence_empty

theorem monotone_influence : Monotone IC.influence :=
  IC.toCascadeModel.monotone_influence

/-- **Kempe–Kleinberg–Tardos Independent Cascade Submodularity Theorem**
([KempeKleinbergTardos2003]; [Kleinberg2007], Theorem 24.5, pp. 625–626): for every instance of
the Independent Cascade Model, the expected influence function `IC.influence` is submodular. -/
theorem isSubmodular_influence : IsSubmodular IC.influence := by
  have heq : IC.influence = fun S => ∑ H : Digraph V,
      weightedCoverage (liveReachableFrom H) (fun _ => liveGraphWeight IC H) S :=
    funext fun S => (IC.influence_eq_sum_liveGraphWeight S).trans
      (Finset.sum_congr rfl fun H _ => by simp [weightedCoverage, liveReachable, mul_comm])
  exact heq ▸ isSubmodular_sum Finset.univ fun H _ =>
    isSubmodular_weightedCoverage (liveReachableFrom H) fun _ => liveGraphWeight_nonneg IC H

end IndependentCascadeModel

end LiveEdge

/-! ## Theorem 24.6: Mossel–Roch General Threshold Submodularity -/

section MosselRoch

/-- Order-reversing involution on `Ioo c 1` fixing all points outside `Ioo c 1`. -/
private noncomputable def reflectUnit (c z : ℝ) : ℝ :=
  if z ∈ Ioo c 1 then 1 + c - z else z

private theorem sub_mem_Ioo {c z : ℝ} (hz : z ∈ Ioo c 1) : 1 + c - z ∈ Ioo c 1 :=
  ⟨by linarith [hz.2],
    by linarith [hz.1]⟩

private theorem sub_mem_Ioo_iff {c z : ℝ} : 1 + c - z ∈ Ioo c 1 ↔ z ∈ Ioo c 1 :=
  ⟨fun h => sub_sub_cancel (1 + c) z ▸ sub_mem_Ioo h, sub_mem_Ioo⟩

private theorem reflectUnit_involutive (c : ℝ) : Function.Involutive (reflectUnit c) := by
  intro z
  unfold reflectUnit
  by_cases hz : z ∈ Ioo c 1
  · simp only [hz, ↓reduceIte, sub_mem_Ioo_iff]; ring
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
    have hpre_inJ : (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ⊆ J :=
      fun _ ⟨_, hz⟩ => sub_mem_Ioo_iff.mp hz
    have hpre : reflectUnit c ⁻¹' s = (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ∪ (s \ J) := by
      ext z
      simp only [mem_preimage, reflectUnit, J, mem_union, mem_inter_iff, mem_sdiff, sub_mem_Ioo_iff]
      by_cases hz : z ∈ Ioo c 1 <;> simp [hz]
    rw [hpre]
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

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

/-- Coordinatewise threshold reflection outside `K`: preserves `U v` for `v ∈ K` and reflects
`U v ∈ (g_v(K), 1)` to `1 + g_v(K) - U v` for `v ∉ K`. -/
private noncomputable def reflectMap (K : Finset V) (U : V → ℝ) : V → ℝ :=
  fun v => if v ∈ K then U v else reflectUnit (M.thresholdFn v K) (U v)

private theorem reflectMap_of_notMem {K : Finset V} {U : V → ℝ} {v : V} (hv : v ∉ K)
    (h1 : M.thresholdFn v K < U v) (h2 : U v < 1) :
    M.reflectMap K U v = 1 + M.thresholdFn v K - U v := by
  have hmem : U v ∈ Ioo (M.thresholdFn v K) 1 := ⟨h1, h2⟩
  simp [reflectMap, hv, reflectUnit, hmem]

private theorem reflectMap_involutive (K : Finset V) :
    Function.Involutive (M.reflectMap K) := by
  intro U
  ext v
  by_cases hv : v ∈ K <;> simp [reflectMap, hv, reflectUnit_involutive (M.thresholdFn v K) (U v)]

private theorem measurePreserving_reflectMap (K : Finset V) :
    MeasurePreserving (M.reflectMap K) (thresholdMeasure V) (thresholdMeasure V) := by
  rw [thresholdMeasure_def V]
  refine measurePreserving_pi (fun _ : V => unitMeasure) (fun _ : V => unitMeasure)
    (f := fun v z => if v ∈ K then z else reflectUnit (M.thresholdFn v K) z) fun v => ?_
  split_ifs
  exacts [MeasurePreserving.id unitMeasure,
    measurePreserving_reflectUnit (M.thresholdFn_nonneg v K)]

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
  have hmE : ∀ K : Finset V, MeasurableSet (E K) := fun K => by
    have heqE : E K = {U | M.thresholdFinal U X = K} ∩ ⋂ v : V, (· v) ⁻¹' Iio 1 :=
      Set.ext fun _ => by simp [E]
    exact heqE ▸ (M.measurableSet_thresholdFinal_eq X K).inter
      (MeasurableSet.iInter fun v => measurableSet_Iio.preimage (measurable_pi_apply v))
  have hmem_reflect : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K ↔ M.reflectMap K U ∈ E K := by
    suffices dir : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K → M.reflectMap K U ∈ E K from
      fun K U => ⟨dir K U, fun h => M.reflectMap_involutive K U ▸ dir K _ h⟩
    intro K U ⟨hfin, hlt1⟩
    rw [M.thresholdFinal_eq_iff_piecewise] at hfin
    rcases hfin with ⟨hpiece, hsurv⟩
    have hpiece_eq : K.piecewise (M.reflectMap K U) (fun _ => (2 : ℝ)) =
        K.piecewise U (fun _ => (2 : ℝ)) :=
      funext fun v => by by_cases hv : v ∈ K <;> simp [reflectMap, hv]
    refine ⟨(M.thresholdFinal_eq_iff_piecewise _ X K).mpr ⟨hpiece_eq ▸ hpiece, fun v hvK => ?_⟩,
      fun v => ?_⟩
    · rw [M.reflectMap_of_notMem hvK (hsurv v hvK) (hlt1 v)]
      linarith [hlt1 v]
    · by_cases hvK : v ∈ K
      · simp [reflectMap, hvK, hlt1 v]
      · rw [M.reflectMap_of_notMem hvK (hsurv v hvK) (hlt1 v)]
        linarith [hsurv v hvK]
  have hsum_ae : ∀ ψ : (V → ℝ) → ℝ, ∀ᵐ U ∂thresholdMeasure V,
      ψ U = ∑ K : Finset V, (E K).indicator ψ U := by
    intro ψ
    filter_upwards [ae_mem_Ioo_thresholdMeasure V] with U hU
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · exact (indicator_of_mem (⟨rfl, fun v => (hU v).2⟩ : U ∈ E _) _).symm
    · exact fun K _ hne => indicator_of_notMem (fun (h : U ∈ E K) => hne h.1.symm) _
    · exact fun habs => absurd (Finset.mem_univ _) habs
  have hsum_lhs := hsum_ae fun U' => φ (M.reflectCouple X Y U')
  have hsum_rhs := hsum_ae fun U' => φ (M.thresholdFinal U' Y)
  have hint_piece_rhs : ∀ K : Finset V,
      Integrable ((E K).indicator fun U => φ (M.thresholdFinal U Y)) (thresholdMeasure V) :=
    fun K => (M.integrable_of_finset Y φ).indicator (hmE K)
  have hfn : ∀ K : Finset V, ((E K).indicator fun U => φ (M.reflectCouple X Y U)) =
      fun U => (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) :=
    fun K => funext fun U => by
      by_cases hU : U ∈ E K
      · have hRU : M.reflectMap K U ∈ E K := (hmem_reflect K U).mp hU
        rw [indicator_of_mem hU, indicator_of_mem hRU]
        simp only [reflectCouple, hU.1, congrArg (· ∪ Y) hRU.1.symm, M.thresholdFinal_union_eq,
          Finset.union_eq_right.mpr hXY]
      · rw [indicator_of_notMem hU, indicator_of_notMem (mt (hmem_reflect K U).mpr hU)]
  have hint_piece_lhs (K : Finset V) :
      Integrable ((E K).indicator fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) :=
    hfn K ▸ (M.measurePreserving_reflectMap K).integrable_comp_of_integrable (hint_piece_rhs K)
  rw [integral_congr_ae hsum_lhs, integral_congr_ae hsum_rhs,
    integral_finsetSum _ (fun K _ => hint_piece_lhs K),
    integral_finsetSum _ (fun K _ => hint_piece_rhs K)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hfn K]
  have hp := M.measurePreserving_reflectMap K
  conv_rhs => rw [← hp.map_eq]
  rw [integral_map hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact (hint_piece_rhs K).aestronglyMeasurable)]

private theorem integrable_reflectCouple (X Y : Finset V) (φ : Finset V → ℝ) :
    Integrable (fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) := by
  have heq : (fun U => φ (M.reflectCouple X Y U)) = fun U => ∑ K : Finset V,
      {U' | M.thresholdFinal U' X = K}.indicator
        (fun U' => φ (M.thresholdFinal (M.reflectMap K U') (K ∪ Y))) U := by
    ext U
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · simp [reflectCouple]
    · exact fun K _ hne => indicator_of_notMem (fun (h : M.thresholdFinal U X = K) => hne h.symm) _
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [heq]
  exact integrable_finsetSum _ fun K _ =>
    ((M.measurePreserving_reflectMap K).integrable_comp_of_integrable
      (M.integrable_of_finset (K ∪ Y) φ)).indicator (M.measurableSet_thresholdFinal_eq X K)

/-- Monotonicity of general threshold expectations for any monotone objective `φ`. -/
theorem monotone_integral_thresholdFinal {φ : Finset V → ℝ} (hmono : Monotone φ) :
    Monotone (fun S : Finset V => ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) :=
  fun A B hAB => integral_mono (M.integrable_of_finset A φ) (M.integrable_of_finset B φ) fun θ =>
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
  filter_upwards [ae_mem_Ioo_thresholdMeasure V] with U hU
  have hlt1 : ∀ v : V, U v < 1 := fun v => (hU v).2
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
    change M.thresholdFinal (M.reflectMap Astar U) (Astar ∪ (A ∪ B)) ⊆ _
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr (M.subset_thresholdFinal U A)]
    have hB_sub : B ⊆ Bstar :=
      Finset.subset_union_right.trans (M.subset_thresholdFinal (M.reflectMap Cstar U) (Cstar ∪ B))
    refine M.thresholdFinal_subset_of_lt (Finset.union_subset_union_right hB_sub) fun v hvAB => ?_
    have hvA : v ∉ Astar := fun h => hvAB (Finset.mem_union_left _ h)
    have hvB : v ∉ Bstar := fun h => hvAB (Finset.mem_union_right _ h)
    have hvC : v ∉ Cstar := fun h => hvA (hCA h)
    have hB_lt : M.thresholdFn v Bstar < M.reflectMap Cstar U v :=
      M.thresholdFn_lt_of_notMem_thresholdFinal hvB
    rw [M.reflectMap_of_notMem hvC (M.thresholdFn_lt_of_notMem_thresholdFinal hvC) (hlt1 v)]
      at hB_lt
    rw [M.reflectMap_of_notMem hvA (M.thresholdFn_lt_of_notMem_thresholdFinal hvA) (hlt1 v)]
    linarith [hlocal v Astar Bstar, M.monotone v hC_inter]
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
  rw [funext M.influence_def]
  exact M.isSubmodular_integral_thresholdFinal hlocal
    (fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card h)) fun A B => by
      simpa only [← Nat.cast_add, Nat.cast_le] using (Finset.card_union_add_card_inter A B).le

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
    have hU : slice (A ∪ B) = slice A ∪ slice B := Finset.ext fun _ => by simp [slice]
    have hI : slice (A ∩ B) = slice A ∩ slice B := Finset.ext fun _ => by simp [slice]
    simpa only [← hU, ← hI, slice] using hlocal vt.1 (slice A) (slice B)

/-- Monotonicity of expected step-`t` active count in the `T`-step nonprogressive threshold
process ([Kleinberg2007], Section 24.3, p. 622). -/
theorem monotone_nonprogStepInfluence (T : ℕ) (t : Fin (T + 1)) :
    Monotone (M.nonprogStepInfluence T t) := by
  intro A B hAB
  simp only [M.nonprogStepInfluence_eq_toTimeLayered]
  exact (M.toTimeLayered T).monotone_integral_thresholdFinal
    (fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h)))
    fun _ hx => mem_seedLayer0.mpr ⟨(mem_seedLayer0.mp hx).1, hAB (mem_seedLayer0.mp hx).2⟩

/-- Submodularity of expected step-`t` active count in the `T`-step nonprogressive threshold
process via `timeLayeredDigraph G T` and Theorem 24.6 ([KempeKleinbergTardos2003];
[MosselRoch2007]; [Kleinberg2007], Sections 24.3–24.4, pp. 622, 626). -/
theorem isSubmodular_nonprogStepInfluence
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) (T : ℕ) (t : Fin (T + 1)) :
    IsSubmodular (M.nonprogStepInfluence T t) := by
  intro A B
  simp only [M.nonprogStepInfluence_eq_toTimeLayered, seedLayer0_union, seedLayer0_inter]
  let φ : Finset (V × Fin (T + 1)) → ℝ := fun X => ((X.filter (·.2 = t)).card : ℝ)
  have hφ_sub : IsSubmodular φ := fun X Y => by
    dsimp only [φ]
    rw [Finset.filter_union, Finset.filter_inter_distrib]
    exact_mod_cast (Finset.card_union_add_card_inter _ _).le
  exact (M.toTimeLayered T).isSubmodular_integral_thresholdFinal
    (M.isSubmodular_toTimeLayered_thresholdFn hlocal T)
    (fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h)))
    hφ_sub (seedLayer0 T A) (seedLayer0 T B)

end GeneralThresholdModel

/-! ### Linear Threshold Model Specialization -/

namespace LinearThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (L : LinearThresholdModel G)

/-- Every local threshold function of a `LinearThresholdModel` is modular, hence submodular
([Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (v : V) :
    IsSubmodular (L.toGeneralThresholdModel.thresholdFn v) := by
  have heq : L.toGeneralThresholdModel.thresholdFn v = modularSum (fun u => L.weight u v) :=
    funext fun _ => by simp [modularSum]
  exact heq ▸ isSubmodular_modularSum _

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

/-- If a `CascadeModel` has diminishing-returns incremental probabilities (`HasDiminishingReturns`),
every local threshold function of `C.toGeneralThresholdModel` is submodular
([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (hdim : C.HasDiminishingReturns)
    (v : V) : IsSubmodular (C.toGeneralThresholdModel.thresholdFn v) := by
  rw [isSubmodular_iff_marginalGain_le]
  intro X Y u hXY huY
  have huX : u ∉ X := fun h => huY (hXY h)
  have hgain {Z : Finset V} (huZ : u ∉ Z) :
      marginalGain (C.toGeneralThresholdModel.thresholdFn v) Z u =
        C.survivalProb v Z * C.prob v u Z := by
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
  rw [funext C.influence_eq_toGeneralThresholdModel]
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
