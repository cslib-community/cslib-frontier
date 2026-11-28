/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Step
public import CslibFrontier.Algorithms.Reachability.Savitch
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite configuration reachability by Savitch's algorithm

An `m`-edge graph has `2^m` Boolean orientations. Every reachable orientation is reachable
within that many moves, so Savitch's recursion at width and depth `m` decides NCL reachability.

## Main results

* `Cslib.Complexity.NCL.AndOrGraph.reach_eq_true_iff`: the generic bit-string procedure
  decides finite NCL configuration reachability.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph

/-- Savitch's midpoint recursion at depth equal to the edge count decides configuration
reachability. -/
theorem reach_eq_true_iff (g : AndOrGraph) (hb : g.Bounded)
    (s t : List Bool) (hs : s.length = g.edgeCount) (ht : t.length = g.edgeCount) :
    Cslib.Reachability.reach g.checkStep g.edgeCount g.edgeCount s t = true ↔
      g.graph.Reachable (g.config s) (g.config t) := by
  rw [Cslib.Reachability.reach_iff hs ht]
  constructor
  · intro h
    exact Relation.ReflTransGen.lift g.config (fun a b hab =>
      ((checkStep_eq_true_iff g hb a b).1 hab.2.2).2.2) _ _ h.reflTransGen
  · intro h
    have hc : Nat.card (Fin g.edgeCount → Bool) ≤ 2 ^ g.edgeCount + 1 := by
      simp [Nat.card_eq_fintype_card]
    have hw := (Relation.reflTransGen_iff_relatesWithinSteps hc).1 h
    have hh := hw.map
      (r' := fun a b => a.length = g.edgeCount ∧ b.length = g.edgeCount ∧ g.checkStep a b = true)
      (fun q : Fin g.edgeCount → Bool => List.ofFn q) (fun a b hab => by
      refine ⟨List.length_ofFn, List.length_ofFn, ?_⟩
      apply (checkStep_eq_true_iff g hb _ _).2
      refine ⟨List.length_ofFn, List.length_ofFn, ?_⟩
      simpa only [config_ofFn] using hab)
    simpa only [ofFn_config g s hs, ofFn_config g t ht] using hh

end Cslib.Complexity.NCL.AndOrGraph
