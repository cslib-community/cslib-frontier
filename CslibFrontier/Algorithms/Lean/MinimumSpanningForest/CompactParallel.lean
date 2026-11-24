/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict

/-!
# Compacting parallel edges before a decision-tree lookup

A multigraph induced on a bounded vertex set can have arbitrarily many parallel labels.
Discarding loops and all but the lightest edge for each endpoint pair preserves the minimum
spanning forest. With injective weights the remaining edge count is at most the square of the
number of vertices, as required for a bounded topology catalogue.
-/

public section

namespace Cslib.Multigraph

open Finset

variable {E V W : Type*} [LinearOrder W] {ends : E → Sym2 V} {w : E → W} {S : Finset E}

/-- Remove loops and retain the minimum-weight label on each parallel class. -/
noncomputable def compactParallel (ends : E → Sym2 V) (w : E → W) (S : Finset E) : Finset E := by
  classical
  exact S.filter fun e => ¬ (ends e).IsDiag ∧ ∀ f ∈ S, ends f = ends e → w e ≤ w f

private theorem mem_compactParallel {e : E} :
    e ∈ compactParallel ends w S ↔
      e ∈ S ∧ ¬ (ends e).IsDiag ∧ ∀ f ∈ S, ends f = ends e → w e ≤ w f := by
  classical exact mem_filter

/-- Parallel-edge compaction selects labels present in the input. -/
theorem compactParallel_subset : compactParallel ends w S ⊆ S :=
  fun _ he => (mem_compactParallel.1 he).1

/-- Every original MSF label survives compaction. A strictly lighter parallel edge supplies
a bypass consisting of just one edge. -/
theorem msf_compactParallel (ends : E → Sym2 V) (w : E → W) (S : Finset E) :
    msf ends w (compactParallel ends w S) = msf ends w S := by
  apply msf_eq_of_subset w _ (fun _ he => (mem_compactParallel.1 he).1)
  intro e he
  refine mem_compactParallel.2 ⟨msf_subset w he, fun hd => notMem_msf_of_isDiag w hd he, ?_⟩
  intro f hf same
  apply le_of_not_gt
  intro lt
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  exact ((mem_msf_iff w hab).1 he).2 (Joins.of_mem ⟨hf, lt⟩ (same.trans hab))

/-- Compaction puts at most one label in each unordered endpoint class. -/
theorem injOn_compactParallel (hw : Function.Injective w) :
    Set.InjOn ends (compactParallel ends w S : Set E) := by
  intro e he f hf same
  obtain ⟨heS, _, leastE⟩ := mem_compactParallel.1 he
  obtain ⟨hfS, _, leastF⟩ := mem_compactParallel.1 hf
  exact hw ((leastE f hfS same.symm).antisymm (leastF e heS same))

/-- A component on `X` vertices fits the `|X|²` edge cutoff even when the input has arbitrary
parallel edges. -/
theorem card_compactParallel_le (hw : Function.Injective w) {X : Finset V}
    (hX : ∀ e ∈ S, ∀ x ∈ ends e, x ∈ X) :
    (compactParallel ends w S).card ≤ X.card ^ 2 := by
  classical
  let U := compactParallel ends w S
  let ofPair : V × V → Sym2 V := fun z => s(z.1, z.2)
  have maps : U.image ends ⊆ (X.product X).image ofPair := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.1 ht
    obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
      Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
    have hf := (mem_compactParallel.1 he).1
    exact mem_image.2 ⟨(a, b), mem_product.2 ⟨hX e hf _ (by simp [hab]),
      hX e hf _ (by simp [hab])⟩, hab.symm⟩
  calc
    U.card = (U.image ends).card := (card_image_of_injOn (injOn_compactParallel hw)).symm
    _ ≤ ((X.product X).image ofPair).card := card_le_card maps
    _ ≤ (X.product X).card := card_image_le
    _ = X.card ^ 2 := by simp [sq]

/-- The compact vertex numbering also fits the supplied component vertex set. -/
theorem vertices_compactParallel_subset {E V : Type} [LinearOrder V] {ends : E → Sym2 V}
    {w : E → W} {S : Finset E} {X : Finset V} (hX : ∀ e ∈ S, ∀ x ∈ ends e, x ∈ X) :
    OptimalTree.vertices ends (compactParallel ends w S) ⊆ X := by
  intro x hx
  obtain ⟨e, he, hx⟩ := mem_biUnion.1 hx
  exact hX e (mem_compactParallel.1 he).1 x (Sym2.mem_toFinset.1 hx)

end Cslib.Multigraph
