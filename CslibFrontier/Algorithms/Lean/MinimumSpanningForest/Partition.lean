/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RobustContraction
import all CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest

/-!
# Corrupted components in the Pettie–Ramachandran partition

Each completed Prim search supplies its vertex set and final edge keys. We compute its marked
boundary edges, remove their labels from the residual problem, and contract its internal edges.
The algorithm retains all marked labels at their original weights. Along a valid sequence, the
minimum spanning forest of the union of these labels, the internal minimum spanning forests,
and the terminal residual minimum spanning forest equals the original minimum spanning forest.

## References

* [Seth Pettie and Vijaya Ramachandran, *An optimal minimum spanning tree algorithm*]
  [PettieRamachandran2002], §3.2, Lemma 3.3(e).
-/

public section

namespace Cslib.Multigraph

open Finset

variable {V E W : Type*} [LinearOrder W]

/-- A component as it stands at the end of its Prim search in the current quotient graph. -/
structure PartitionPart (V E W : Type*) where
  /-- The reached vertices, including the starting vertex. -/
  vertices : Set V
  /-- Final keys of the current search, with each extracted key frozen at extraction. -/
  key : E → W

namespace PartitionPart

variable (p : PartitionPart V E W) (ends : E → Sym2 V) (w : E → W) (S : Finset E)

/-- Exactly the edges on the final boundary whose keys have changed. -/
noncomputable def marks : Finset E := by
  classical
  exact S.filter fun e => e ∈ (toGraph ends).edgeCut p.vertices ∧ p.key e ≠ w e

theorem mem_marks {e : E} :
    e ∈ p.marks ends w S ↔ e ∈ S ∧ e ∈ (toGraph ends).edgeCut p.vertices ∧ p.key e ≠ w e := by
  classical exact mem_filter

/-- Endpoint map after contracting this component. Labels still denote their original edges. -/
noncomputable def nextEnds : E → Sym2 V :=
  Sym2.map (contract ends (internalEdges ends S p.vertices)) ∘ ends

/-- Active edges after removing the internal and marked edges of the current component. -/
noncomputable def remaining [DecidableEq E] : Finset E :=
  (S \ internalEdges ends S p.vertices) \ p.marks ends w S

theorem remaining_subset [DecidableEq E] : p.remaining ends w S ⊆ S :=
  fun _ he => (mem_sdiff.1 (mem_sdiff.1 he).1).1

theorem marks_subset_sdiff [DecidableEq E] :
    p.marks ends w S ⊆ S \ internalEdges ends S p.vertices := by
  intro e he
  obtain ⟨heS, cut, _⟩ := (p.mem_marks ends w S).1 he
  obtain ⟨a, b, hab, _, hb⟩ := Graph.mem_edgeCut_iff.1 cut
  refine mem_sdiff.2 ⟨heS, fun h => hb ((mem_internalEdges.1 h).2 b ?_)⟩
  change ends e = s(a, b) at hab
  simp [hab]

private theorem clean {e a b} (he : e ∈ S) (hm : e ∉ p.marks ends w S) (ha : a ∈ p.vertices)
    (hb : b ∉ p.vertices) (hab : ends e = s(a, b)) : p.key e = w e := by
  by_contra h
  exact hm ((p.mem_marks ends w S).2 ⟨he, Graph.mem_edgeCut_iff.2 ⟨a, b, hab, ha, hb⟩, h⟩)

end PartitionPart

namespace PrimPartition

variable [DecidableEq E]

/-- Each search starts in the quotient left by its predecessors and raises keys only above
the input weights. The empty list leaves the remaining graph for the dense-case algorithm. -/
inductive Valid (w : E → W) : (E → Sym2 V) → Finset E → List (PartitionPart V E W) → Prop where
  | nil {ends S} : Valid w ends S []
  | cons {ends S p ps} (prim : PrimPrefix ends S p.key p.vertices)
      (raised : ∀ e ∈ S, w e ≤ p.key e)
      (tail : Valid w (p.nextEnds ends S) (p.remaining ends w S) ps) :
      Valid w ends S (p :: ps)

/-- The partition retains original edge labels throughout all contractions. -/
structure Result (E : Type*) where
  /-- Edge sets passed to the small-graph subroutine. -/
  pieces : List (Finset E)
  /-- Original-weight labels rescued from each corrupted boundary. -/
  marked : Finset E
  /-- Internal forests together with the forest of the terminal residual graph. -/
  forests : Finset E
  /-- Active labels left in the terminal quotient. -/
  residual : Finset E

/-- Fold the completed components in search order. This specifies the edge sets consumed by
the small-graph and dense-case solvers. -/
noncomputable def collect (w : E → W) (ends : E → Sym2 V) (S : Finset E) :
    List (PartitionPart V E W) → Result E
  | [] => ⟨[], ∅, msf ends w S, S⟩
  | p :: ps =>
    let I := internalEdges ends S p.vertices
    let r := collect w (p.nextEnds ends S) (p.remaining ends w S) ps
    ⟨I :: r.pieces, p.marks ends w S ∪ r.marked, msf ends w I ∪ r.forests, r.residual⟩

variable {w : E → W} {ends : E → Sym2 V} {S : Finset E} {ps : List (PartitionPart V E W)}

theorem marked_subset : (collect w ends S ps).marked ⊆ S := by
  induction ps generalizing ends S with
  | nil => simp [collect]
  | cons p ps ih =>
    exact union_subset (fun _ he => ((p.mem_marks ends w S).1 he).1)
      (ih.trans (p.remaining_subset ends w S))

theorem forests_subset : (collect w ends S ps).forests ⊆ S := by
  induction ps generalizing ends S with
  | nil => exact msf_subset w
  | cons p ps ih =>
    exact union_subset (fun _ he => (mem_internalEdges.1 (msf_subset w he)).1)
      (ih.trans (p.remaining_subset ends w S))

/-- The internal edge sets, marked labels, and terminal residual partition the input edge
labels. A label marked at one stage cannot be marked again at a later stage. -/
theorem card_partition :
    ((collect w ends S ps).pieces.map Finset.card).sum + (collect w ends S ps).marked.card +
      (collect w ends S ps).residual.card = S.card := by
  induction ps generalizing ends S with
  | nil => simp [collect]
  | cons p ps ih =>
    let I := internalEdges ends S p.vertices
    let M := p.marks ends w S
    let r := collect w (p.nextEnds ends S) (p.remaining ends w S) ps
    have hI : I ⊆ S := fun _ he => (mem_internalEdges.1 he).1
    have hM : M ⊆ S \ I := p.marks_subset_sdiff ends w S
    have hd : Disjoint M r.marked :=
      Finset.disjoint_left.2 fun _ hm hr => (mem_sdiff.1 (marked_subset hr)).2 hm
    have h₁ := card_sdiff_add_card_eq_card hI
    have h₂ := card_sdiff_add_card_eq_card hM
    have h₃ := ih (ends := p.nextEnds ends S) (S := p.remaining ends w S)
    change (r.pieces.map Finset.card).sum + r.marked.card + r.residual.card =
      ((S \ I) \ M).card at h₃
    change ((I :: r.pieces).map Finset.card).sum + (M ∪ r.marked).card + r.residual.card = S.card
    rw [card_union_of_disjoint hd, List.map_cons, List.sum_cons]
    omega

/-- **Lemma 3.3(e).** The chosen internal and residual forest edges and all marked labels
suffice to recover the minimum spanning forest, for an arbitrary number of contractions. -/
theorem Valid.msf_subset (run : Valid w ends S ps) (hw : Function.Injective w) :
    msf ends w S ⊆ (collect w ends S ps).forests ∪ (collect w ends S ps).marked := by
  induction run with
  | nil => simp [collect]
  | @cons ends S p ps prim raised tail ih =>
    have h := prim.msf_subset_robust hw raised
      (fun f hf hm a ha b hb hab => p.clean ends w S hf hm ha hb hab)
    intro e he
    rcases mem_union.1 (h he) with hF | hM
    · rcases mem_union.1 hF with hI | hQ
      · exact mem_union_left _ (mem_union_left _ hI)
      · rcases mem_union.1 (ih hQ) with hL | hR
        · exact mem_union_left _ (mem_union_right _ hL)
        · exact mem_union_right _ (mem_union_right _ hR)
    · exact mem_union_right _ (mem_union_left _ hM)

theorem Valid.msf_eq (run : Valid w ends S ps) (hw : Function.Injective w) :
    msf ends w ((collect w ends S ps).forests ∪ (collect w ends S ps).marked) = msf ends w S :=
  msf_eq_of_subset w (run.msf_subset hw) (union_subset forests_subset marked_subset)

omit [DecidableEq E] in
private theorem acyclic_insert {F : Set E} {g : E} (hF : IsAcyclic ends F)
    (fresh : ∀ a b, ends g = s(a, b) → ¬Joins ends F a b) : IsAcyclic ends (insert g F) := by
  intro e he u v huv hj
  rcases he with rfl | he
  · apply fresh u v huv
    exact Joins.mono (S := (insert e F : Set E) \ {e}) (fun f hf => hf.1.resolve_left hf.2) hj
  · have path : Joins ends (insert g (F \ {e})) u v := hj.mono fun f hf => by
      rcases hf.1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hf.2⟩
    rcases joins_insert_iff.1 path with h | ⟨x, y, hxy, hux, hyv⟩
    · exact hF e he u v huv h
    · exact fresh x y hxy (((hux.mono Set.sdiff_subset).symm.trans (Joins.of_mem he huv)).trans
        (hyv.mono Set.sdiff_subset).symm)

/-- If a forest lies in the contracted edges and a second forest is acyclic after contraction,
their original edge labels together form a forest before contraction. -/
private theorem acyclic_union_contracted {I F H : Finset E} (hF : IsAcyclic ends F)
    (hFI : F ⊆ I) (hH : IsAcyclic (Sym2.map (contract ends (I : Set E)) ∘ ends) H) :
    IsAcyclic ends ((F ∪ H : Finset E) : Set E) := by
  let q := contract ends (I : Set E)
  induction H using Finset.induction_on with
  | empty => simpa using hF
  | @insert e H he ih =>
    have tail : IsAcyclic (Sym2.map q ∘ ends) (H : Set E) := by
      intro f hf a b hab path
      exact hH f (mem_insert_of_mem hf) a b hab
        (Joins.mono (S := (H : Set E) \ {f}) (fun g hg => ⟨mem_insert_of_mem hg.1, hg.2⟩) path)
    rw [Finset.union_insert, Finset.coe_insert]
    refine acyclic_insert (ih tail) ?_
    intro a b hab path
    have mapped : Joins (Sym2.map q ∘ ends) (H : Set E) (q a) (q b) := by
      apply (joins_map_iff (ends := ends) (C := (I : Set E))
        (fun _ _ => contract_eq_contract_iff)).2
      apply path.mono
      intro f hf
      exact (mem_union.1 hf).elim (fun h => Or.inr (hFI h)) Or.inl
    apply hH e (mem_insert_self ..) (q a) (q b) (by simp [q, hab])
    exact mapped.mono fun f hf => ⟨mem_insert_of_mem hf, fun h => he (h ▸ hf)⟩

/-- The forest edges assembled across all contracted graphs remain acyclic in the input graph.
This holds for every list of components, even without the Prim growth property. -/
theorem isAcyclic_forests (hw : Function.Injective w) :
    IsAcyclic ends ((collect w ends S ps).forests : Set E) := by
  induction ps generalizing ends S with
  | nil => exact isAcyclic_msf w hw
  | cons p ps ih =>
    exact acyclic_union_contracted (isAcyclic_msf w hw) (msf_subset w)
      (ih (ends := p.nextEnds ends S) (S := p.remaining ends w S))

/-- On an input supported on `X`, at most `|X| - 1` forest edges and one candidate per
marked label survive the reduction. -/
theorem card_candidates_le (hw : Function.Injective w) {X : Finset V}
    (hX : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) :
    ((collect w ends S ps).forests ∪ (collect w ends S ps).marked).card ≤
      X.card - 1 + (collect w ends S ps).marked.card :=
  (card_union_le _ _).trans (Nat.add_le_add_right
    ((isAcyclic_forests hw).card_le (fun e he => hX e (forests_subset he))) _)

end PrimPartition
end Cslib.Multigraph
