/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CSP
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Nice

/-!
# Primal graphs of constraint satisfaction problems and nice-tree DP invariants

For a constraint satisfaction problem `F : CSP Rel V`, the **primal graph** `CSP.primalGraph F`
places an edge between distinct variables that appear together in the scope of some constraint of
`F`. Every constraint scope is therefore a clique of `CSP.primalGraph F`, so every constraint
scope is covered by some bag of any `RootedTreeDecomposition` or `NiceTreeDecomposition` of
`CSP.primalGraph F` (and likewise for `CSP.activePrimalGraph F` on `F.vars.toFinset`, which
remains finite even when `V` is infinite).

Over any valid `SimpleGraph.NiceTree V` covering all constraint scopes of `F`, we define the exact
partial-assignment count `CSP.subtreeSatCount` and recursive dynamic-programming specification
`CSP.specDPCount` / `CSP.specDPDecide`, proving the leaf, introduce, forget, and join recurrences
and the root identity `CSP.specDPCount = F.modelCount sem`.

## Main definitions

* `Cslib.Logic.PL.CSP.primalGraph`: primal graph on `V`.
* `Cslib.Logic.PL.CSP.activePrimalGraph`: induced primal graph on `F.vars.toFinset`.
* `Cslib.Logic.PL.CSP.subtreeSatCount`: count of satisfying partial extensions of a bag assignment.
* `Cslib.Logic.PL.CSP.specDPCount`, `Cslib.Logic.PL.CSP.specDPDecide`: nice-tree DP
  specifications.

## Main results

* `Cslib.Logic.PL.CSP.isClique_scope_of_mem`,
  `Cslib.Logic.PL.CSP.exists_coversFinset_scope_of_mem`: constraint scopes form cliques and lie in
  some bag.
* `Cslib.Logic.PL.CSP.subtreeSatCount_leaf`, `Cslib.Logic.PL.CSP.subtreeSatCount_introduce`,
  `Cslib.Logic.PL.CSP.subtreeSatCount_forget`, `Cslib.Logic.PL.CSP.subtreeSatCount_join`: exact
  DP recurrences.
* `Cslib.Logic.PL.CSP.specDPCount_eq_modelCount`,
  `Cslib.Logic.PL.CSP.specDPDecide_eq_true_iff_satisfiable`: correctness of the DP specification.
-/

public section

namespace Cslib.Logic.PL

namespace CSP

open SimpleGraph

section PrimalGraph

variable {Rel : Type*} {V : Type*}

/-- The primal graph of `F`: distinct variables sharing a constraint scope are adjacent. -/
@[expose] def primalGraph (F : CSP Rel V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ c ∈ F, u ∈ c.scope ∧ v ∈ c.scope
  symm := ⟨fun _ _ ⟨hne, c, hc, hu, hv⟩ => ⟨hne.symm, c, hc, hv, hu⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

theorem primalGraph_adj {F : CSP Rel V} {u v : V} :
    F.primalGraph.Adj u v ↔ u ≠ v ∧ ∃ c ∈ F, u ∈ c.scope ∧ v ∈ c.scope :=
  Iff.rfl

instance instDecidableRelPrimalGraphAdj [DecidableEq V] (F : CSP Rel V) :
    DecidableRel F.primalGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ∃ c ∈ F, u ∈ c.scope ∧ v ∈ c.scope))

/-- The scope of every constraint of `F` forms a clique in `F.primalGraph`. -/
theorem isClique_scope_of_mem [DecidableEq V] (F : CSP Rel V) {c : Constraint Rel V}
    (hc : c ∈ F) : F.primalGraph.IsClique (c.scope.toFinset : Set V) := fun _ hu _ hv huv =>
  ⟨huv, c, hc, List.mem_toFinset.1 hu, List.mem_toFinset.1 hv⟩

/-- Every constraint scope of `F` lies in some bag of any nice tree decomposition of
`F.primalGraph`. -/
theorem exists_coversFinset_scope_of_mem [DecidableEq V] {F : CSP Rel V}
    (N : F.primalGraph.NiceTreeDecomposition) {c : Constraint Rel V} (hc : c ∈ F) :
    N.tree.CoversFinset c.scope.toFinset :=
  N.exists_coversFinset_of_isClique (F.isClique_scope_of_mem hc)

/-- Every constraint scope of `F` lies in some bag of any rooted tree decomposition of
`F.primalGraph`. -/
theorem exists_bag_subset_scope_of_mem [DecidableEq V] {F : CSP Rel V} {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) {c : Constraint Rel V} (hc : c ∈ F) :
    ∃ i, c.scope.toFinset ⊆ R.bag i :=
  R.exists_subset_bag_of_isClique (F.isClique_scope_of_mem hc)

/-- The primal graph induced on the active variables `F.vars.toFinset`. -/
@[expose] def activePrimalGraph [DecidableEq V] (F : CSP Rel V) :
    SimpleGraph {v : V // v ∈ F.vars.toFinset} :=
  F.primalGraph.induce (F.vars.toFinset : Set V)

instance instDecidableRelActivePrimalGraphAdj [DecidableEq V] (F : CSP Rel V) :
    DecidableRel F.activePrimalGraph.Adj := fun u v =>
  F.instDecidableRelPrimalGraphAdj u.val v.val

theorem mem_vars_finset_of_mem [DecidableEq V] {F : CSP Rel V} {c : Constraint Rel V}
    (hc : c ∈ F) {v : V} (hv : v ∈ c.scope) : v ∈ F.vars.toFinset :=
  List.mem_toFinset.2 (List.mem_flatMap.2 ⟨c, hc, hv⟩)

/-- Lift a nice tree decomposition of `F.activePrimalGraph` into `NiceTree V` preserving validity,
empty root bag, width, size, and constraint-scope coverage. -/
@[expose] def liftActiveNiceTree [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) : NiceTree V :=
  N.tree.map Subtype.val

theorem liftActiveNiceTree_localValid [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) : (liftActiveNiceTree N).LocalValid :=
  NiceTree.localValid_map Subtype.val_injective N.localValid

theorem liftActiveNiceTree_bag [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) : (liftActiveNiceTree N).bag = ∅ := by
  rw [liftActiveNiceTree, NiceTree.bag_map Subtype.val_injective, N.bag_root, Finset.image_empty]

theorem liftActiveNiceTree_subtreeVerts [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) :
    (liftActiveNiceTree N).subtreeVerts = F.vars.toFinset := by
  rw [liftActiveNiceTree, NiceTree.subtreeVerts_map]
  ext v
  simp only [Finset.mem_image, Subtype.exists]
  constructor
  · rintro ⟨u, hu, _, rfl⟩
    exact hu
  · intro hv
    exact ⟨v, hv, N.exists_mem_bag ⟨v, hv⟩, rfl⟩

theorem liftActiveNiceTree_coversFinset [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) {c : Constraint Rel V} (hc : c ∈ F) :
    (liftActiveNiceTree N).CoversFinset c.scope.toFinset := by
  let K : Finset {v : V // v ∈ F.vars.toFinset} :=
    c.scope.toFinset.subtype fun v => v ∈ F.vars.toFinset
  have hK : F.activePrimalGraph.IsClique (K : Set {v : V // v ∈ F.vars.toFinset}) := by
    rintro ⟨u, hu⟩ huK ⟨w, hw⟩ hwK huw
    simp only [Finset.mem_coe, Finset.mem_subtype, List.mem_toFinset, K] at huK hwK
    have hne : u ≠ w := fun h => huw (Subtype.ext h)
    exact F.isClique_scope_of_mem hc (List.mem_toFinset.2 huK) (List.mem_toFinset.2 hwK) hne
  have hcov :=
    NiceTree.coversFinset_map Subtype.val_injective (N.exists_coversFinset_of_isClique hK)
  have hImg : K.image Subtype.val = c.scope.toFinset := by
    ext v
    simp only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, K, List.mem_toFinset]
    constructor
    · rintro ⟨w, _, hwc, rfl⟩
      exact hwc
    · intro hv
      exact ⟨v, List.mem_flatMap.2 ⟨c, hc, hv⟩, hv, rfl⟩
  rwa [hImg] at hcov

theorem liftActiveNiceTree_width [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) : (liftActiveNiceTree N).width = N.width :=
  NiceTree.width_map Subtype.val_injective N.tree

theorem liftActiveNiceTree_size [DecidableEq V] {F : CSP Rel V}
    (N : F.activePrimalGraph.NiceTreeDecomposition) : (liftActiveNiceTree N).size = N.size :=
  NiceTree.size_map Subtype.val N.tree

end PrimalGraph

/-! ### Exact subtree counting and DP recurrences -/

section TreeDP

variable {Rel V D : Type*} [DecidableEq V]

private def extendSubtree (S U : Finset V) (σ : ↑(S ∩ U) → D) (α : V → D) : V → D :=
  fun v => if hv : v ∈ S ∩ U then σ ⟨v, hv⟩ else α v

/-- Finite set of partial assignments on `S ∩ U` agreeing with `α` on `B` and satisfying every
constraint of `F` whose scope lies inside `S`. -/
noncomputable def subtreeSatSet [Finite D] (sem : Rel → List D → Bool)
    (F : CSP Rel V) (U S B : Finset V) (α : V → D) : Finset (↑(S ∩ U) → D) := by
  classical
  letI := Fintype.ofFinite (↑(S ∩ U) → D)
  exact Finset.univ.filter fun σ =>
    (∀ v : ↑(S ∩ U), v.val ∈ B → σ v = α v.val) ∧
      ∀ c ∈ F, c.scope.toFinset ⊆ S → c.eval sem (extendSubtree S U σ α) = true

/-- Number of satisfying partial extensions of `α` on `S ∩ U`. -/
noncomputable def subtreeSatCount [Finite D] (sem : Rel → List D → Bool)
    (F : CSP Rel V) (U S B : Finset V) (α : V → D) : ℕ :=
  (subtreeSatSet sem F U S B α).card

private theorem mem_subtreeSatSet [Finite D] {sem : Rel → List D → Bool} {F : CSP Rel V}
    {U S B : Finset V} {α : V → D} {σ : ↑(S ∩ U) → D} :
    σ ∈ subtreeSatSet sem F U S B α ↔
      (∀ v : ↑(S ∩ U), v.val ∈ B → σ v = α v.val) ∧
        ∀ c ∈ F, c.scope.toFinset ⊆ S → c.eval sem (extendSubtree S U σ α) = true := by
  classical
  unfold subtreeSatSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem extendSubtree_eval_congr {sem : Rel → List D → Bool} {F : CSP Rel V}
    {U S₁ S₂ : Finset V} (hU : F.vars.toFinset ⊆ U) {c : Constraint Rel V} (hc : c ∈ F)
    (hc1 : c.scope.toFinset ⊆ S₁) (hc2 : c.scope.toFinset ⊆ S₂)
    {σ₁ : ↑(S₁ ∩ U) → D} {σ₂ : ↑(S₂ ∩ U) → D} {α₁ α₂ : V → D}
    (hagree : ∀ v (hv1 : v ∈ S₁ ∩ U) (hv2 : v ∈ S₂ ∩ U), v ∈ c.scope → σ₁ ⟨v, hv1⟩ = σ₂ ⟨v, hv2⟩) :
    c.eval sem (extendSubtree S₁ U σ₁ α₁) = c.eval sem (extendSubtree S₂ U σ₂ α₂) := by
  refine Constraint.eval_congr fun v hv => ?_
  have hvU : v ∈ U := hU (F.mem_vars_finset_of_mem hc hv)
  have hv1 : v ∈ S₁ ∩ U := Finset.mem_inter.2 ⟨hc1 (List.mem_toFinset.2 hv), hvU⟩
  have hv2 : v ∈ S₂ ∩ U := Finset.mem_inter.2 ⟨hc2 (List.mem_toFinset.2 hv), hvU⟩
  simp only [extendSubtree, hv1, hv2, ↓reduceDIte]
  exact hagree v hv1 hv2 hv

private theorem extendSubtree_eval_bag {sem : Rel → List D → Bool} {F : CSP Rel V}
    {U S B : Finset V} (hU : F.vars.toFinset ⊆ U) {c : Constraint Rel V} (hc : c ∈ F)
    (hcS : c.scope.toFinset ⊆ S) (hcB : c.scope.toFinset ⊆ B)
    {σ : ↑(S ∩ U) → D} {α : V → D} (hσB : ∀ v : ↑(S ∩ U), v.val ∈ B → σ v = α v.val) :
    c.eval sem (extendSubtree S U σ α) = c.eval sem α := by
  refine Constraint.eval_congr fun v hv => ?_
  have hvU : v ∈ U := hU (F.mem_vars_finset_of_mem hc hv)
  have hvS : v ∈ S ∩ U := Finset.mem_inter.2 ⟨hcS (List.mem_toFinset.2 hv), hvU⟩
  simp only [extendSubtree, hvS, ↓reduceDIte]
  exact hσB ⟨v, hvS⟩ (hcB (List.mem_toFinset.2 hv))

/-- Satisfaction of the constraints inside `S` does not depend on the values outside `S ∩ U`. -/
private theorem forall_eval_extendSubtree_iff {sem : Rel → List D → Bool} {F : CSP Rel V}
    {U S : Finset V} (hU : F.vars.toFinset ⊆ U) {σ : ↑(S ∩ U) → D} {α β : V → D} :
    (∀ c ∈ F, c.scope.toFinset ⊆ S → c.eval sem (extendSubtree S U σ α) = true) ↔
      ∀ c ∈ F, c.scope.toFinset ⊆ S → c.eval sem (extendSubtree S U σ β) = true :=
  forall₂_congr fun _ hc => forall_congr' fun hcS => by
    rw [extendSubtree_eval_congr hU hc hcS hcS (α₂ := β) fun _ _ _ _ => rfl]

private theorem mem_of_disjoint_sdiff {A B C : Finset V} (h : Disjoint (A \ B) C) {v : V}
    (hA : v ∈ A) (hC : v ∈ C) : v ∈ B :=
  by_contra fun hB => Finset.disjoint_left.1 h (Finset.mem_sdiff.2 ⟨hA, hB⟩) hC

theorem subtreeSatCount_congr [Finite D] (sem : Rel → List D → Bool) {F : CSP Rel V}
    {U S B : Finset V} (hU : F.vars.toFinset ⊆ U) {α β : V → D}
    (h : ∀ v ∈ B ∩ U, α v = β v) :
    subtreeSatCount sem F U S B α = subtreeSatCount sem F U S B β := by
  unfold subtreeSatCount
  congr 1
  ext σ
  rw [mem_subtreeSatSet, mem_subtreeSatSet, forall_eval_extendSubtree_iff hU (α := α) (β := β)]
  refine and_congr_left' (forall_congr' fun v => imp_congr_right fun hvB => ?_)
  rw [h v.val (Finset.mem_inter.2 ⟨hvB, (Finset.mem_inter.1 v.property).2⟩)]

theorem subtreeSatCount_empty_eq_modelCountOn [Fintype D] [Inhabited D]
    (sem : Rel → List D → Bool) {F : CSP Rel V}
    {U S : Finset V} (hU : F.vars.toFinset ⊆ U) (hF : ∀ c ∈ F, c.scope.toFinset ⊆ S) (α : V → D) :
    subtreeSatCount sem F U S ∅ α = CSP.modelCountOn sem F (S ∩ U) := by
  unfold subtreeSatCount modelCountOn
  congr 1
  ext σ
  simp only [mem_subtreeSatSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, false_implies, implies_true, true_and, CSP.eval, List.all_eq_true]
  have hEq : ∀ c ∈ F, c.eval sem (extendSubtree S U σ α) =
      c.eval sem (fun v => if h : v ∈ S ∩ U then σ ⟨v, h⟩ else default) := fun c hc =>
    Constraint.eval_congr fun v hv => by
      have hvSU : v ∈ S ∩ U := Finset.mem_inter.2
        ⟨hF c hc (List.mem_toFinset.2 hv), hU (F.mem_vars_finset_of_mem hc hv)⟩
      simp only [extendSubtree, hvSU, ↓reduceDIte]
  exact ⟨fun h c hc => (hEq c hc).symm.trans (h c hc (hF c hc)),
    fun h c hc _ => (hEq c hc).trans (h c hc)⟩

theorem subtreeSatCount_root_eq_modelCount [Fintype D] [Inhabited D]
    (sem : Rel → List D → Bool) {F : CSP Rel V}
    {S : Finset V} (hS : F.vars.toFinset ⊆ S) (α : V → D) :
    subtreeSatCount sem F F.vars.toFinset S ∅ α = CSP.modelCount sem F := by
  have hF : ∀ c ∈ F, c.scope.toFinset ⊆ S := fun c hc =>
    Finset.Subset.trans (fun v hv => F.mem_vars_finset_of_mem hc (List.mem_toFinset.1 hv)) hS
  rw [subtreeSatCount_empty_eq_modelCountOn sem Finset.Subset.rfl hF α,
    Finset.inter_eq_right.2 hS, modelCount]

theorem subtreeSatCount_leaf [Finite D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : CSP Rel V) (U : Finset V) (α : V → D) :
    subtreeSatCount sem F U ∅ ∅ α =
      if ∀ c ∈ F, c.scope = [] → c.eval sem (fun _ => default) = true then 1 else 0 := by
  let σ₀ : ↑((∅ : Finset V) ∩ U) → D := fun x =>
    absurd (Finset.mem_inter.1 x.property).1 (Finset.notMem_empty _)
  have huniq : ∀ σ : ↑((∅ : Finset V) ∩ U) → D, σ = σ₀ := fun σ =>
    funext fun x => absurd (Finset.mem_inter.1 x.property).1 (Finset.notMem_empty _)
  have hmem : ∀ σ, σ ∈ subtreeSatSet sem F U ∅ ∅ α ↔
      ∀ c ∈ F, c.scope = [] → c.eval sem (fun _ => default) = true := fun σ => by
    simp only [mem_subtreeSatSet, Finset.notMem_empty, false_implies, implies_true, true_and,
      Finset.subset_empty, List.toFinset_eq_empty_iff]
    exact forall₂_congr fun c _ => forall_congr' fun hnil => by
      rw [Constraint.eval_congr (fun v hv => by simp [hnil] at hv)]
  unfold subtreeSatCount
  split_ifs with hc
  · exact Finset.card_eq_one.2
      ⟨σ₀, Finset.eq_singleton_iff_unique_mem.2 ⟨(hmem σ₀).2 hc, fun σ _ => huniq σ⟩⟩
  · exact Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun σ hσ => hc ((hmem σ).1 hσ))

theorem subtreeSatCount_introduce [Finite D] (sem : Rel → List D → Bool) {F : CSP Rel V}
    {U S B : Finset V} {v : V} (hvS : v ∉ S) (hBS : B ⊆ S) (hU : F.vars.toFinset ⊆ U)
    (hcov : ∀ c ∈ F, c.scope.toFinset ⊆ insert v S →
      c.scope.toFinset ⊆ S ∨ c.scope.toFinset ⊆ insert v B)
    (α : V → D) :
    subtreeSatCount sem F U (insert v S) (insert v B) α =
      if ∀ c ∈ F, c.scope.toFinset ⊆ insert v B → v ∈ c.scope → c.eval sem α = true then
        subtreeSatCount sem F U S B α
      else 0 := by
  classical
  by_cases hAll : ∀ c ∈ F, c.scope.toFinset ⊆ insert v B → v ∈ c.scope → c.eval sem α = true
  · rw [ite_eq_left hAll]
    unfold subtreeSatCount
    refine Finset.card_bij
      (fun σ _ => fun x => σ ⟨x.val, by
        have := Finset.mem_inter.1 x.property
        exact Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem this.1, this.2⟩⟩)
      ?_ ?_ ?_
    · intro σ hσ
      rw [mem_subtreeSatSet] at hσ ⊢
      refine ⟨fun x hxB => hσ.1 _ (Finset.mem_insert_of_mem hxB), fun c hc hcS => ?_⟩
      have hcIS := hcS.trans (Finset.subset_insert v S)
      exact (extendSubtree_eval_congr hU hc hcS hcIS fun _ _ _ _ => rfl).trans (hσ.2 c hc hcIS)
    · intro σ₁ hσ₁ σ₂ hσ₂ hEq
      rw [mem_subtreeSatSet] at hσ₁ hσ₂
      ext x
      have hx := Finset.mem_inter.1 x.property
      rcases Finset.mem_insert.1 hx.1 with hxv | hxS
      · have hxB : x.val ∈ insert v B := Finset.mem_insert.2 (Or.inl hxv)
        rw [hσ₁.1 x hxB, hσ₂.1 x hxB]
      · exact congrFun hEq ⟨x.val, Finset.mem_inter.2 ⟨hxS, hx.2⟩⟩
    · intro τ hτ
      rw [mem_subtreeSatSet] at hτ
      have hσB : ∀ x : ↑(insert v S ∩ U), x.val ∈ insert v B →
          (if hx : x.val ∈ S ∩ U then τ ⟨x.val, hx⟩ else α x.val) = α x.val := fun x hxB => by
        split_ifs with hxS
        · have hxv : x.val ≠ v := fun h => hvS (h ▸ (Finset.mem_inter.1 hxS).1)
          exact hτ.1 _ ((Finset.mem_insert.1 hxB).resolve_left hxv)
        · rfl
      refine ⟨fun x => if hx : x.val ∈ S ∩ U then τ ⟨x.val, hx⟩ else α x.val, ?_, ?_⟩
      · refine mem_subtreeSatSet.2 ⟨hσB, fun c hc hcIS => ?_⟩
        by_cases hvc : v ∈ c.scope
        · have hcIB := (hcov c hc hcIS).resolve_left fun h => hvS (h (List.mem_toFinset.2 hvc))
          rw [extendSubtree_eval_bag hU hc hcIS hcIB hσB]
          exact hAll c hc hcIB hvc
        · have hcS := (Finset.subset_insert_iff_of_notMem (mt List.mem_toFinset.1 hvc)).1 hcIS
          rw [extendSubtree_eval_congr hU hc hcIS hcS
            (σ₂ := τ) (α₂ := α) (fun w _ hwS _ => dite_eq_left hwS)]
          exact hτ.2 c hc hcS
      · ext x
        simp [x.property]
  · rw [ite_eq_right hAll]
    push Not at hAll
    obtain ⟨c, hc, hcIB, -, hcEval⟩ := hAll
    have hcIS := hcIB.trans (Finset.insert_subset_insert v hBS)
    unfold subtreeSatCount
    refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun σ hσ => hcEval ?_)
    rw [mem_subtreeSatSet] at hσ
    exact (extendSubtree_eval_bag hU hc hcIS hcIB hσ.1).symm.trans (hσ.2 c hc hcIS)

theorem subtreeSatCount_forget [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    {F : CSP Rel V} {U S B : Finset V}
    {v : V} (hvB : v ∈ B) (hBS : B ⊆ S) (hU : F.vars.toFinset ⊆ U) (α : V → D) :
    subtreeSatCount sem F U S (B.erase v) α =
      if v ∈ U then ∑ d : D, subtreeSatCount sem F U S B (Function.update α v d)
      else subtreeSatCount sem F U S B (Function.update α v default) := by
  classical
  by_cases hvU : v ∈ U
  · rw [ite_eq_left hvU]
    have hvSU : v ∈ S ∩ U := Finset.mem_inter.2 ⟨hBS hvB, hvU⟩
    have hPart : subtreeSatSet sem F U S (B.erase v) α =
        Finset.univ.biUnion fun d : D => subtreeSatSet sem F U S B (Function.update α v d) := by
      ext σ
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_subtreeSatSet]
      constructor
      · rintro ⟨hσB, hσF⟩
        refine ⟨σ ⟨v, hvSU⟩, fun x hxB => ?_, (forall_eval_extendSubtree_iff hU).1 hσF⟩
        by_cases hxv : x.val = v
        · have hx_eq : x = ⟨v, hvSU⟩ := Subtype.ext hxv
          simp [hx_eq]
        · rw [Function.update_of_ne hxv]
          exact hσB x (Finset.mem_erase.2 ⟨hxv, hxB⟩)
      · rintro ⟨d, hσB, hσF⟩
        refine ⟨fun x hxE => ?_, (forall_eval_extendSubtree_iff hU).1 hσF⟩
        rw [hσB x (Finset.mem_erase.1 hxE).2, Function.update_of_ne (Finset.mem_erase.1 hxE).1]
    have hDisj : ((Finset.univ : Finset D) : Set D).PairwiseDisjoint
        (fun d => subtreeSatSet sem F U S B (Function.update α v d)) := by
      intro d₁ _ d₂ _ hne s hs₁ hs₂ σ hσ
      have h1 := (mem_subtreeSatSet.1 (hs₁ hσ)).1 ⟨v, hvSU⟩ hvB
      have h2 := (mem_subtreeSatSet.1 (hs₂ hσ)).1 ⟨v, hvSU⟩ hvB
      simp only [Function.update_self] at h1 h2
      exact absurd (h1.symm.trans h2) hne
    unfold subtreeSatCount
    rw [hPart, Finset.card_biUnion hDisj]
  · rw [ite_eq_right hvU]
    unfold subtreeSatCount
    congr 1
    ext σ
    rw [mem_subtreeSatSet, mem_subtreeSatSet,
      forall_eval_extendSubtree_iff hU (α := α) (β := Function.update α v default)]
    refine and_congr_left' (forall_congr' fun x => ?_)
    have hxv : x.val ≠ v := fun h => hvU (h ▸ (Finset.mem_inter.1 x.property).2)
    rw [Function.update_of_ne hxv, Finset.mem_erase, and_iff_right hxv]

theorem subtreeSatCount_join [Finite D] (sem : Rel → List D → Bool) {F : CSP Rel V}
    {U S_L S_R B : Finset V} (hdisj : Disjoint (S_L \ B) S_R) (hBLS : B ⊆ S_L)
    (hU : F.vars.toFinset ⊆ U)
    (hcov : ∀ c ∈ F, c.scope.toFinset ⊆ S_L ∪ S_R → c.scope.toFinset ⊆ S_L ∨ c.scope.toFinset ⊆ S_R)
    (α : V → D) :
    subtreeSatCount sem F U (S_L ∪ S_R) B α =
      subtreeSatCount sem F U S_L B α * subtreeSatCount sem F U S_R B α := by
  classical
  unfold subtreeSatCount
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun σ _ =>
      (fun x => σ ⟨x.val, Finset.mem_inter.2
          ⟨Finset.mem_union_left _ (Finset.mem_inter.1 x.property).1,
            (Finset.mem_inter.1 x.property).2⟩⟩,
       fun x => σ ⟨x.val, Finset.mem_inter.2
          ⟨Finset.mem_union_right _ (Finset.mem_inter.1 x.property).1,
            (Finset.mem_inter.1 x.property).2⟩⟩))
    ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_product, mem_subtreeSatSet] at hσ ⊢
    refine ⟨⟨fun x hxB => hσ.1 _ hxB, fun c hc hcL => ?_⟩,
      ⟨fun x hxB => hσ.1 _ hxB, fun c hc hcR => ?_⟩⟩
    · have hcU := hcL.trans (Finset.subset_union_left (s₂ := S_R))
      exact (extendSubtree_eval_congr hU hc hcL hcU fun _ _ _ _ => rfl).trans (hσ.2 c hc hcU)
    · have hcU := hcR.trans (Finset.subset_union_right (s₁ := S_L))
      exact (extendSubtree_eval_congr hU hc hcR hcU fun _ _ _ _ => rfl).trans (hσ.2 c hc hcU)
  · intro σ₁ _ σ₂ _ hEq
    have hL := congrArg Prod.fst hEq
    have hR := congrArg Prod.snd hEq
    ext x
    have hx := Finset.mem_inter.1 x.property
    rcases Finset.mem_union.1 hx.1 with hxL | hxR
    · exact congrFun hL ⟨x.val, Finset.mem_inter.2 ⟨hxL, hx.2⟩⟩
    · exact congrFun hR ⟨x.val, Finset.mem_inter.2 ⟨hxR, hx.2⟩⟩
  · rintro ⟨σL, σR⟩ hpair
    simp only [Finset.mem_product, mem_subtreeSatSet] at hpair
    rcases hpair with ⟨⟨hLB, hLF⟩, ⟨hRB, hRF⟩⟩
    let σ : ↑((S_L ∪ S_R) ∩ U) → D := fun x =>
      if hxL : x.val ∈ S_L then
        σL ⟨x.val, Finset.mem_inter.2 ⟨hxL, (Finset.mem_inter.1 x.property).2⟩⟩
      else σR ⟨x.val, Finset.mem_inter.2
        ⟨(Finset.mem_union.1 (Finset.mem_inter.1 x.property).1).resolve_left hxL,
          (Finset.mem_inter.1 x.property).2⟩⟩
    have hσL : ∀ w (hwL : w ∈ S_L ∩ U) (hw : w ∈ (S_L ∪ S_R) ∩ U),
        σ ⟨w, hw⟩ = σL ⟨w, hwL⟩ := fun w hwL hw => by
      dsimp [σ]
      rw [dite_eq_left (Finset.mem_inter.1 hwL).1]
    have hσR : ∀ w (hwR : w ∈ S_R ∩ U) (hw : w ∈ (S_L ∪ S_R) ∩ U),
        σ ⟨w, hw⟩ = σR ⟨w, hwR⟩ := fun w hwR hw => by
      dsimp [σ]
      split_ifs with hwL
      · have hwB := mem_of_disjoint_sdiff hdisj hwL (Finset.mem_inter.1 hwR).1
        rw [hLB _ hwB, hRB _ hwB]
      · rfl
    refine ⟨σ, ?_, ?_⟩
    · simp only [mem_subtreeSatSet]
      refine ⟨fun x hxB => ?_, fun c hc hcU => ?_⟩
      · exact (hσL x.val (Finset.mem_inter.2
          ⟨hBLS hxB, (Finset.mem_inter.1 x.property).2⟩) x.property).trans
          (hLB _ hxB)
      · rcases hcov c hc hcU with hcL | hcR
        · rw [extendSubtree_eval_congr hU hc hcU hcL (fun w hw hwL _ => hσL w hwL hw)]
          exact hLF c hc hcL
        · rw [extendSubtree_eval_congr hU hc hcU hcR (fun w hw hwR _ => hσR w hwR hw)]
          exact hRF c hc hcR
    · ext x
      · exact hσL x.val x.property _
      · exact hσR x.val x.property _

section FintypeDomain

variable [Fintype D] [Inhabited D]

/-- Nice-tree dynamic programming specification returning the exact number of satisfying partial
extensions on `T.subtreeVerts ∩ U` extending `α` on `T.bag`. -/
@[expose] noncomputable def specDPCount (sem : Rel → List D → Bool) (F : CSP Rel V)
    (U : Finset V) : NiceTree V → (V → D) → ℕ
  | .leaf, _ =>
    if ∀ c ∈ F, c.scope = [] → c.eval sem (fun _ => default) = true then 1 else 0
  | .introduce v child, α =>
    if ∀ c ∈ F, c.scope.toFinset ⊆ insert v child.bag → v ∈ c.scope → c.eval sem α = true then
      specDPCount sem F U child α
    else 0
  | .forget v child, α =>
    if v ∈ U then ∑ d : D, specDPCount sem F U child (Function.update α v d)
    else specDPCount sem F U child (Function.update α v default)
  | .join left right, α =>
    specDPCount sem F U left α * specDPCount sem F U right α

/-- Nice-tree dynamic programming specification for satisfiability. -/
@[expose] noncomputable def specDPDecide (sem : Rel → List D → Bool) (F : CSP Rel V)
    (U : Finset V) : NiceTree V → (V → D) → Bool
  | .leaf, _ =>
    F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => default)
  | .introduce v child, α =>
    (F.all fun c =>
      !(decide (c.scope.toFinset ⊆ insert v child.bag) && decide (v ∈ c.scope)) || c.eval sem α) &&
      specDPDecide sem F U child α
  | .forget v child, α =>
    if v ∈ U then decide (∃ d : D, specDPDecide sem F U child (Function.update α v d) = true)
    else specDPDecide sem F U child (Function.update α v default)
  | .join left right, α =>
    specDPDecide sem F U left α && specDPDecide sem F U right α

theorem specDPCount_eq_subtreeSatCount (sem : Rel → List D → Bool) {F : CSP Rel V}
    {U : Finset V} (hU : F.vars.toFinset ⊆ U) :
    ∀ {T : NiceTree V}, T.LocalValid →
      (∀ c ∈ F, c.scope.toFinset ⊆ T.subtreeVerts → T.CoversFinset c.scope.toFinset) →
      ∀ α, specDPCount sem F U T α = subtreeSatCount sem F U T.subtreeVerts T.bag α
  | .leaf, _, _, α => by
    simp only [specDPCount, NiceTree.subtreeVerts, NiceTree.bag]
    exact (subtreeSatCount_leaf sem F U α).symm
  | .introduce v child, hval, hcov, α => by
    have hcov_child : ∀ c ∈ F, c.scope.toFinset ⊆ child.subtreeVerts →
        child.CoversFinset c.scope.toFinset := fun c hc hcSub =>
      (hcov c hc (hcSub.trans (Finset.subset_insert _ _))).elim (fun hbag =>
        NiceTree.coversFinset_of_subset_bag
          ((Finset.subset_insert_iff_of_notMem fun hv => hval.1 (hcSub hv)).1 hbag)) id
    have hcov_step : ∀ c ∈ F, c.scope.toFinset ⊆ insert v child.subtreeVerts →
        c.scope.toFinset ⊆ child.subtreeVerts ∨ c.scope.toFinset ⊆ insert v child.bag :=
      fun c hc hcSub => ((hcov c hc hcSub).imp_right
        NiceTree.coversFinset_subset_subtreeVerts).symm
    simp only [specDPCount, NiceTree.subtreeVerts, NiceTree.bag]
    rw [subtreeSatCount_introduce sem hval.1 child.bag_subset_subtreeVerts hU hcov_step α,
      specDPCount_eq_subtreeSatCount sem hU hval.2 hcov_child α]
  | .forget v child, hval, hcov, α => by
    have hcov_child : ∀ c ∈ F, c.scope.toFinset ⊆ child.subtreeVerts →
        child.CoversFinset c.scope.toFinset := fun c hc hcSub =>
      (hcov c hc hcSub).elim
        (fun hbag => NiceTree.coversFinset_of_subset_bag (hbag.trans (Finset.erase_subset v _))) id
    simp only [specDPCount, NiceTree.subtreeVerts, NiceTree.bag,
      specDPCount_eq_subtreeSatCount sem hU hval.2 hcov_child]
    rw [subtreeSatCount_forget sem hval.1 child.bag_subset_subtreeVerts hU α]
  | .join left right, hval, hcov, α => by
    obtain ⟨hbag, hdisj, hcL, hcR⟩ := hval
    have hcov_L : ∀ c ∈ F, c.scope.toFinset ⊆ left.subtreeVerts →
        left.CoversFinset c.scope.toFinset := fun c hc hcSub => by
      rcases hcov c hc (hcSub.trans Finset.subset_union_left) with hB | hL | hR
      · exact NiceTree.coversFinset_of_subset_bag hB
      · exact hL
      · exact NiceTree.coversFinset_of_subset_bag fun v hv =>
          mem_of_disjoint_sdiff hdisj (hcSub hv) (NiceTree.coversFinset_subset_subtreeVerts hR hv)
    have hcov_R : ∀ c ∈ F, c.scope.toFinset ⊆ right.subtreeVerts →
        right.CoversFinset c.scope.toFinset := fun c hc hcSub => by
      rcases hcov c hc (hcSub.trans Finset.subset_union_right) with hB | hL | hR
      · exact NiceTree.coversFinset_of_subset_bag (hbag ▸ hB)
      · exact NiceTree.coversFinset_of_subset_bag fun v hv =>
          mem_of_disjoint_sdiff (NiceTree.disjoint_join_right hbag hdisj) (hcSub hv)
            (NiceTree.coversFinset_subset_subtreeVerts hL hv)
      · exact hR
    have hcov_step : ∀ c ∈ F, c.scope.toFinset ⊆ left.subtreeVerts ∪ right.subtreeVerts →
        c.scope.toFinset ⊆ left.subtreeVerts ∨ c.scope.toFinset ⊆ right.subtreeVerts :=
        fun c hc hcSub => by
      rcases hcov c hc hcSub with hB | hL | hR
      · exact Or.inl (hB.trans left.bag_subset_subtreeVerts)
      · exact Or.inl (NiceTree.coversFinset_subset_subtreeVerts hL)
      · exact Or.inr (NiceTree.coversFinset_subset_subtreeVerts hR)
    simp only [specDPCount, NiceTree.subtreeVerts, NiceTree.bag]
    rw [subtreeSatCount_join sem hdisj left.bag_subset_subtreeVerts hU hcov_step α,
      specDPCount_eq_subtreeSatCount sem hU hcL hcov_L α,
      specDPCount_eq_subtreeSatCount sem hU hcR hcov_R α, hbag]

theorem specDPCount_pos_iff_specDPDecide (sem : Rel → List D → Bool) (F : CSP Rel V)
    (U : Finset V) (T : NiceTree V) (α : V → D) :
    0 < specDPCount sem F U T α ↔ specDPDecide sem F U T α = true := by
  classical
  induction T generalizing α with
  | leaf =>
    simp only [specDPCount, specDPDecide, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    split_ifs with h
    · exact iff_of_true Nat.zero_lt_one fun c hc => imp_iff_not_or.1 (h c hc)
    · exact iff_of_false (lt_irrefl 0) fun h' => h fun c hc => imp_iff_not_or.2 (h' c hc)
  | introduce v child ih =>
    simp only [specDPCount, specDPDecide, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not]
    split_ifs with h
    · rw [ih α, iff_and_self]
      exact fun _ c hc => by have := h c hc; tauto
    · exact iff_of_false (lt_irrefl 0) fun ⟨hF, _⟩ => h fun c hc => by have := hF c hc; tauto
  | forget v child ih =>
    simp only [specDPCount, specDPDecide]
    split_ifs
    · rw [Nat.pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff, not_forall]
      simp only [Finset.mem_univ, forall_true_left, ← Nat.pos_iff_ne_zero, ih, decide_eq_true_eq]
    · exact ih (Function.update α v default)
  | join left right ihL ihR =>
    simp only [specDPCount, specDPDecide, Bool.and_eq_true]
    rw [Nat.pos_iff_ne_zero, Nat.mul_ne_zero_iff, ← Nat.pos_iff_ne_zero,
      ← Nat.pos_iff_ne_zero, ihL, ihR]

theorem specDPCount_eq_modelCount (sem : Rel → List D → Bool) {F : CSP Rel V}
    {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset)
    (α : V → D) :
    specDPCount sem F F.vars.toFinset T α = CSP.modelCount sem F := by
  rw [specDPCount_eq_subtreeSatCount sem Finset.Subset.rfl hval (fun c hc _ => hcov c hc) α,
    hbag, subtreeSatCount_root_eq_modelCount sem hsub α]

theorem specDPDecide_eq_true_iff_satisfiable (sem : Rel → List D → Bool) {F : CSP Rel V}
    {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset)
    (α : V → D) :
    specDPDecide sem F F.vars.toFinset T α = true ↔ CSP.Satisfiable sem F := by
  rw [← specDPCount_pos_iff_specDPDecide, specDPCount_eq_modelCount sem hval hbag hsub hcov α,
    CSP.modelCount_pos_iff]

theorem specDPCount_primalGraph_eq_modelCount (sem : Rel → List D → Bool)
    {F : CSP Rel V} (N : F.primalGraph.NiceTreeDecomposition) (α : V → D) :
    specDPCount sem F F.vars.toFinset N.tree α = CSP.modelCount sem F :=
  specDPCount_eq_modelCount sem N.localValid N.bag_root
    (fun v _ => N.exists_mem_bag v) (fun _ hc => F.exists_coversFinset_scope_of_mem N hc) α

theorem specDPCount_activePrimalGraph_eq_modelCount (sem : Rel → List D → Bool)
    {F : CSP Rel V} (N : F.activePrimalGraph.NiceTreeDecomposition) (α : V → D) :
    specDPCount sem F F.vars.toFinset (liftActiveNiceTree N) α = CSP.modelCount sem F :=
  specDPCount_eq_modelCount sem (liftActiveNiceTree_localValid N) (liftActiveNiceTree_bag N)
    (by rw [liftActiveNiceTree_subtreeVerts])
    (fun _ hc => liftActiveNiceTree_coversFinset N hc) α

end FintypeDomain

end TreeDP

end CSP

end Cslib.Logic.PL
