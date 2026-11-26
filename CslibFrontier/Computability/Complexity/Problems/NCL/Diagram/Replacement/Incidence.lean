/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Basic

/-!
# Incidences of open graph replacements

Replacing a cell keeps its boundary ports and adds one pair of opposite, equally weighted ports
for every private wire. Summing this identity over cells proves well-formedness for arbitrary
shared-edge assemblies.

## Main results

* `Cslib.Complexity.NCL.Diagram.Replacement.portMultiset`: exact replacement incidences.

## References

* [E. D. Demaine and R. A. Hearn, *Constraint Logic: A Uniform Framework for Modeling
  Computation as Games*][DemaineHearn2008]
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.Diagram.Replacement

variable {a b : List Color} {g : Prim a b} {H : Diagram Prim a b} {E : Type*}
variable (S : OpenSim Prim.interp Prim.interp (gen g) H)
variable (p : (gen g : Diagram Prim a b).Edge → E)

private def boundaryWeight : (gen g : Diagram Prim a b).Edge → ℕ :=
  Sum.elim (fun i => (a.get i).weight) (fun j => (b.get j).weight)

private def boundaryDirection : (gen g : Diagram Prim a b).Edge → Bool :=
  Sum.elim (fun _ => true) (fun _ => false)

private theorem weight_ι (hH : H.checkGens Prim.interp.checkPorts = true)
    (i : (gen g : Diagram Prim a b).Edge) :
    H.edgeWeight (S.ι i) = boundaryWeight i := by
  rcases i with i | j
  · exact congrArg H.edgeWeight (S.ι_top i)
  · exact (congrArg H.edgeWeight (S.ι_bottom j)).trans (edgeWeight_bottom Prim.interp H hH j)

private theorem label_top (i : Fin a.length) : label S p (.inl i) = .inl (p (.inl i)) :=
  (congrArg (label S p) (S.ι_top i).symm).trans (label_ι S p (.inl i))

private theorem label_bottom (i : Fin b.length) :
    label S p (H.bottom i) = .inl (p (.inr i)) :=
  (congrArg (label S p) (S.ι_bottom i).symm).trans (label_ι S p (.inr i))

private theorem boundary_ports :
    Multiset.map (WeightedPort.map
        (fun x : Fin a.length ⊕ Fin b.length => (Sum.inl (p x) : E ⊕ Inner S)))
        (↑(genVertex a b 0).ports) =
      ∑ i : (gen g : Diagram Prim a b).Edge,
        {⟨⟨Sum.inl (p i), boundaryDirection i⟩, boundaryWeight i⟩} := by
  rw [ports_genVertex, ← Multiset.coe_mapAddMonoidHom, map_add, map_sum, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_singleton, WeightedPort.map, Port.map]
  rw [Fintype.sum_sum_type]
  rfl

private theorem two_ports (i : (gen g : Diagram Prim a b).Edge) :
    ({⟨⟨Sum.inl (p i), false⟩, boundaryWeight i⟩} +
      {⟨⟨Sum.inl (p i), true⟩, boundaryWeight i⟩} : Multiset (WeightedPort (E ⊕ Inner S))) =
    {⟨⟨Sum.inl (p i), boundaryDirection i⟩, boundaryWeight i⟩} +
      {⟨⟨Sum.inl (p i), !(boundaryDirection i)⟩, boundaryWeight i⟩} := by
  rcases i with i | i
  · exact add_comm _ _
  · rfl

/-- A replacement has its declared boundary ports and exactly one pair per private wire. -/
theorem portMultiset_boundary [Fintype (Inner S)]
    (hH : H.checkGens Prim.interp.checkPorts = true) :
    (graph S p).portMultiset =
      Multiset.map (WeightedPort.map (fun x : Fin a.length ⊕ Fin b.length => Sum.inl (p x)))
        (↑(genVertex a b 0).ports) +
      ∑ e : Inner S, ({⟨⟨Sum.inr e, false⟩, H.edgeWeight e⟩} +
        {⟨⟨Sum.inr e, true⟩, H.edgeWeight e⟩}) := by
  let A : Multiset (WeightedPort (E ⊕ Inner S)) :=
    ∑ i : (gen g : Diagram Prim a b).Edge,
      {⟨⟨Sum.inl (p i), boundaryDirection i⟩, boundaryWeight i⟩}
  let B : Multiset (WeightedPort (E ⊕ Inner S)) :=
    ∑ i : (gen g : Diagram Prim a b).Edge,
      {⟨⟨Sum.inl (p i), !(boundaryDirection i)⟩, boundaryWeight i⟩}
  let P : Multiset (WeightedPort (E ⊕ Inner S)) :=
    ∑ e : Inner S, ({⟨⟨Sum.inr e, false⟩, H.edgeWeight e⟩} +
      {⟨⟨Sum.inr e, true⟩, H.edgeWeight e⟩})
  have hbal := congrArg (Multiset.map (WeightedPort.map (label S p)))
    (portMultiset_add_boundary Prim.interp H hH)
  simp only [← Multiset.coe_mapAddMonoidHom, map_add, map_sum] at hbal
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_singleton,
    WeightedPort.map, Port.map] at hbal
  rw [← ConstraintGraph.portMultiset_map, sum_edges S] at hbal
  simp only [label_top, label_bottom, label_ι, label_private, weight_ι S hH, two_ports S p,
    Finset.sum_add_distrib] at hbal
  have hbal' : (graph S p).portMultiset + B = (A + B) + P := by
    dsimp only [A, B, P, boundaryDirection, boundaryWeight] at hbal ⊢
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Bool.not_true, Bool.not_false, add_assoc, graph, Finset.sum_add_distrib] at hbal ⊢
    exact hbal
  exact (add_right_cancel (b := B) (c := A + P) (hbal'.trans (by ac_rfl))).trans
    (congrArg (· + P) (boundary_ports S p).symm)

/-- A replacement retains its source ports and adds exactly the private-wire port pairs. -/
theorem portMultiset [Fintype (Inner S)] (hg : Prim.interp.checkPorts g = true)
    (hH : H.checkGens Prim.interp.checkPorts = true) :
    (graph S p).portMultiset =
      Multiset.map (WeightedPort.map (fun x : Fin a.length ⊕ Fin b.length => Sum.inl (p x)))
        (↑(g.flatMap Vertex.ports)) +
      ∑ e : Inner S, ({⟨⟨Sum.inr e, false⟩, H.edgeWeight e⟩} +
        {⟨⟨Sum.inr e, true⟩, H.edgeWeight e⟩}) := by
  erw [Multiset.coe_eq_coe.mpr (of_decide_eq_true hg)]
  exact portMultiset_boundary S p hH

end Cslib.Complexity.NCL.Diagram.Replacement
