/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Assembly.Reorient
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Replacement

/-!
# Boundary reference directions for graph components

Reorient a replacement graph on shared edges and retain its private reference directions. The
resulting graph component realizes the correspondingly reoriented constraint vertex.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.Replacement.realizesReorient`: a local graph
  implementation with arbitrary boundary polarities.
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph.Replacement

open scoped BigOperators

/-- A boundary reorientation preserves the source-port identity and all private port pairs. -/
theorem portMultiset_reorient_boundary {S T E I : Type*} [Fintype S] [Fintype T] [Fintype I]
    (G : ConstraintGraph S E) (H : ConstraintGraph T (E ⊕ I)) (weight : I → ℕ)
    (h : H.portMultiset = Multiset.map (WeightedPort.map Sum.inl) G.portMultiset +
      ∑ i, ({⟨⟨Sum.inr i, false⟩, weight i⟩} + {⟨⟨Sum.inr i, true⟩, weight i⟩}))
    (mask : E → Bool) :
    (H.reorient (Sum.elim mask (fun _ => false))).portMultiset =
      Multiset.map (WeightedPort.map Sum.inl) (G.reorient mask).portMultiset +
        ∑ i, ({⟨⟨Sum.inr i, false⟩, weight i⟩} + {⟨⟨Sum.inr i, true⟩, weight i⟩}) := by
  have hshared : Multiset.map (WeightedPort.reorient (Sum.elim mask (fun _ : I => false)))
      (Multiset.map (WeightedPort.map Sum.inl) G.portMultiset) =
      Multiset.map (WeightedPort.map Sum.inl)
        (Multiset.map (WeightedPort.reorient mask) G.portMultiset) := by
    change Multiset.map _ (Multiset.map _ G.portMultiset) =
      Multiset.map _ (Multiset.map _ G.portMultiset)
    simp only [Multiset.map_map]
    rfl
  have hprivate : Multiset.map (WeightedPort.reorient (Sum.elim mask (fun _ : I => false)))
      (∑ i, ({⟨⟨Sum.inr i, false⟩, weight i⟩} + {⟨⟨Sum.inr i, true⟩, weight i⟩})) =
      ∑ i, ({⟨⟨Sum.inr i, false⟩, weight i⟩} + {⟨⟨Sum.inr i, true⟩, weight i⟩}) := by
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [WeightedPort.reorient, Port.reorient]
  rw [ConstraintGraph.portMultiset_reorient, h, Multiset.map_add, hshared, hprivate,
    ConstraintGraph.portMultiset_reorient]

variable {V E I : Type*} [DecidableEq I]

private theorem boundary_step (H : ConstraintGraph V (E ⊕ I)) (mask s : E → Bool)
    (x y : I → Bool) :
    (component (H.reorient (Sum.elim mask (fun _ => false)))).Step s x y ↔
      (component H).Step (mask + s) x y := by
  simp only [Component.Step, component, ConstraintGraph.legal_reorient_boundary]

variable [DecidableEq E]

/-- Reorienting only the shared edges transports a local graph implementation. -/
@[expose] def realizesReorient (H : ConstraintGraph V (E ⊕ I)) {v : Vertex E}
    (R : Realizes (component H) v) (mask : E → Bool) :
    Realizes (component (H.reorient (Sum.elim mask (fun _ => false)))) (v.reorient mask) where
  canon := (R.reorient mask).canon
  sound hs := (R.reorient mask).sound ((H.legal_reorient_boundary mask _ _).1 hs)
  legal_canon hs := (H.legal_reorient_boundary mask _ _).2 ((R.reorient mask).legal_canon hs)
  move {s} e hs ht := by
    obtain ⟨u, hp, hu, hq⟩ := (R.reorient mask).move e hs ht
    exact ⟨u, Relation.ReflTransGen.mono
        (fun x y h => (boundary_step H mask s x y).2 h) _ _ hp,
      (H.legal_reorient_boundary mask _ _).2 hu,
      Relation.ReflTransGen.mono
        (fun x y h => (boundary_step H mask (reverse s e) x y).2 h) _ _ hq⟩

end Cslib.Complexity.NCL.ConstraintGraph.Replacement
