/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Logic.Equiv.Basic

/-!
# Changing reference directions

A mask reverses the reference direction of selected edges, both at ports and in configurations.
This supports cups and caps in drawings: their two descending segments can represent opposite
reference directions of the original edge.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.reorient`: change the port direction bits.
* `Cslib.Complexity.NCL.ConstraintGraph.reorientSimulation`: the induced simulation.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.legal_reorient`: translate configurations by the mask.
* `Cslib.Complexity.NCL.ConstraintGraph.WellFormed.reorient`: preserve edge incidences.
-/

public section

namespace Cslib.Complexity.NCL

variable {V E : Type*}

/-- Change the reference direction at one port. -/
@[expose]
def Port.reorient (mask : E → Bool) (p : Port E) : Port E := ⟨p.edge, mask p.edge ^^ p.dir⟩

/-- A port reads the configuration with the same reference directions. -/
theorem Port.in_reorient (mask : E → Bool) (p : Port E) (s : E → Bool) :
    (p.reorient mask).In s ↔ p.In (mask + s) := by
  change s p.edge = (mask p.edge ^^ p.dir) ↔ (mask p.edge ^^ s p.edge) = p.dir
  have h : s p.edge = (mask p.edge ^^ p.dir) ↔
      (mask p.edge ^^ s p.edge) = (mask p.edge ^^ (mask p.edge ^^ p.dir)) :=
    Bool.xor_right_inj.symm
  simpa only [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor] using h

/-- Change a weighted port's reference direction, retaining its edge and weight. -/
@[expose] def WeightedPort.reorient (mask : E → Bool) (p : WeightedPort E) : WeightedPort E :=
  ⟨p.port.reorient mask, p.weight⟩

/-- Change port directions while preserving weights and required in-flow. -/
@[expose] def Vertex.reorient (mask : E → Bool) (v : Vertex E) : Vertex E :=
  ⟨v.ports.map (WeightedPort.reorient mask), v.minInflow⟩

/-- Satisfaction commutes with the change of reference directions. -/
theorem Vertex.sat_reorient (mask : E → Bool) (v : Vertex E) (s : E → Bool) :
    (v.reorient mask).Sat s ↔ v.Sat (mask + s) := by
  simp only [Vertex.Sat, Vertex.reorient, Vertex.inflow, List.map_map,
    Function.comp_def, WeightedPort.reorient, Port.in_reorient]

/-- Change the reference directions of the edges selected by a mask. -/
@[expose]
def ConstraintGraph.reorient (G : ConstraintGraph V E) (mask : E → Bool) : ConstraintGraph V E :=
  fun v => (G v).reorient mask

/-- A legal reoriented configuration translates to a legal original configuration. -/
theorem ConstraintGraph.legal_reorient (G : ConstraintGraph V E) (mask s : E → Bool) :
    (G.reorient mask).Legal s ↔ G.Legal (mask + s) :=
  forall_congr' (fun v => Vertex.sat_reorient mask (G v) s)

/-- Reversing an edge commutes with a fixed change of reference directions. -/
theorem reverse_add_left [DecidableEq E] (mask s : E → Bool) (e : E) :
    reverse (mask + s) e = mask + reverse s e := by
  funext f
  by_cases h : f = e
  · subst f
    simp only [reverse_self, Pi.add_apply, Bool.add_eq_xor, Bool.xor_not]
  · simp only [reverse_of_ne _ h, Pi.add_apply]

/-- Translating by the mask preserves and reflects single-edge moves. -/
theorem ConstraintGraph.step_reorient [DecidableEq E]
    (G : ConstraintGraph V E) (mask s t : E → Bool) :
    (G.reorient mask).Step (mask + s) (mask + t) ↔ G.Step s t := by
  simp only [ConstraintGraph.Step, ConstraintGraph.legal_reorient, Cslib.BitString.add_cancel_left]
  constructor
  · rintro ⟨hs, ht, e, he⟩
    rw [reverse_add_left] at he
    exact ⟨hs, ht, e, add_left_cancel he⟩
  · rintro ⟨hs, ht, e, rfl⟩
    exact ⟨hs, ht, e, (reverse_add_left mask s e).symm⟩

/-- Translating configurations by the mask gives an exact simulation. -/
@[expose] def ConstraintGraph.reorientSimulation [DecidableEq E]
    (G : ConstraintGraph V E) (mask : E → Bool) :
    ConstraintGraph.Simulation G (G.reorient mask) where
  toSimulation := NCL.Simulation.ofEquiv
    (Function.Involutive.toPerm (mask + ·) (Cslib.BitString.add_cancel_left mask))
    (ConstraintGraph.step_reorient G mask)
  legal_abs hs := (ConstraintGraph.legal_reorient G mask _).1 hs
  legal_enc := by
    intro s hs
    change (G.reorient mask).Legal (mask + s)
    rw [ConstraintGraph.legal_reorient, Cslib.BitString.add_cancel_left]
    exact hs

/-- The AND/OR check only depends on weights and required in-flow. -/
theorem Vertex.checkAndOr_reorient (mask : E → Bool) (v : Vertex E) :
    (v.reorient mask).checkAndOr = v.checkAndOr := by
  simp only [Vertex.checkAndOr, Vertex.reorient, List.map_map, Function.comp_def,
    WeightedPort.reorient]

/-- Changing reference directions preserves distinct port edges. -/
theorem Vertex.checkLoopFree_reorient [DecidableEq E] (mask : E → Bool) (v : Vertex E) :
    (v.reorient mask).checkLoopFree = v.checkLoopFree := by
  simp only [Vertex.checkLoopFree, Vertex.reorient, List.map_map, Function.comp_def,
    WeightedPort.reorient, Port.reorient]

/-- Changing reference directions preserves AND/OR vertices. -/
theorem ConstraintGraph.IsAndOr.reorient (G : ConstraintGraph V E) (mask : E → Bool)
    (hG : G.IsAndOr) : (G.reorient mask).IsAndOr := by
  intro v
  exact (Vertex.checkAndOr_eq_true_iff _).1
    ((Vertex.checkAndOr_reorient mask (G v)).trans ((Vertex.checkAndOr_eq_true_iff _).2 (hG v)))

/-- Changing reference directions preserves absence of self-loops. -/
theorem ConstraintGraph.LoopFree.reorient (G : ConstraintGraph V E)
    (mask : E → Bool) (hG : G.LoopFree) : (G.reorient mask).LoopFree := by
  classical
  intro v
  exact (Vertex.checkLoopFree_eq_true_iff _).1
    ((Vertex.checkLoopFree_reorient mask (G v)).trans
      ((Vertex.checkLoopFree_eq_true_iff _).2 (hG v)))

/-- Collecting all weighted ports commutes with a change of reference directions. -/
theorem ConstraintGraph.portMultiset_reorient [Fintype V]
    (G : ConstraintGraph V E) (mask : E → Bool) :
    (G.reorient mask).portMultiset = Multiset.map (WeightedPort.reorient mask) G.portMultiset := by
  rw [← Multiset.coe_mapAddMonoidHom, ConstraintGraph.portMultiset,
    ConstraintGraph.portMultiset, map_sum]
  rfl

/-- The two ports of each edge retain equal weights and opposite directions. -/
theorem ConstraintGraph.WellFormed.reorient [Fintype V] [Fintype E]
    (G : ConstraintGraph V E) (mask : E → Bool) (hG : G.WellFormed) :
    (G.reorient mask).WellFormed := by
  obtain ⟨weight, hw⟩ := hG
  refine ⟨weight, ?_⟩
  rw [ConstraintGraph.portMultiset_reorient, hw, ← Multiset.coe_mapAddMonoidHom, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  cases hm : mask e
  · simp [WeightedPort.reorient, Port.reorient, hm]
  · simpa [WeightedPort.reorient, Port.reorient, hm] using
      (Multiset.cons_swap (⟨⟨e, true⟩, weight e⟩ : WeightedPort E) ⟨⟨e, false⟩, weight e⟩ 0)

end Cslib.Complexity.NCL
