/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.DP
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Exact independent set

`EXACT INDSET` asks whether the largest independent set of a graph has exactly `k` vertices
([Arora and Barak, Section 5.1][AroraBarak07]). A graph has independence number `k` exactly when
it has an independent set of `k` vertices and none of `k + 1`, so `EXACT INDSET` is the difference
of `IndependentSet` and its preimage under `⟨G, k⟩ ↦ ⟨G, k + 1⟩`, two `NP` languages. Hence it lies
in `DP` ([Arora and Barak, Exercise 5 §8(a)][AroraBarak07]).

## Main definitions

* `Cslib.Complexity.ExactIndependentSet`: the instances `⟨G, k⟩` with `α(G) = k`
  (`Cslib.Complexity.mem_ExactIndependentSet` unfolds membership).

## Main results

* `Cslib.Complexity.mem_ExactIndependentSet_iff`: an independent set of `k` vertices and none of
  `k + 1`.
* `Cslib.Complexity.ExactIndependentSet_mem_DP`: `EXACT INDSET ∈ DP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft of January 2007,
  Section 5.1 and Exercise 5 §8][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Exact independent set** ([Arora and Barak, Section 5.1][AroraBarak07]): the instances
`⟨G, k⟩` whose largest independent set of declared vertices has exactly `k` vertices. -/
def ExactIndependentSet : Set IndependentSetInstance :=
  {x | x.graph.indepNum = x.m}

theorem mem_ExactIndependentSet {x : IndependentSetInstance} :
    x ∈ ExactIndependentSet ↔ x.graph.indepNum = x.m :=
  Iff.rfl

/-- `⟨G, k⟩` is in `EXACT INDSET` iff `G` has an independent set of `k` vertices and none of
`k + 1`. -/
theorem mem_ExactIndependentSet_iff {x : IndependentSetInstance} :
    x ∈ ExactIndependentSet ↔
      x ∈ IndependentSet ∧ (⟨x.graph, x.m + 1⟩ : IndependentSetInstance) ∉ IndependentSet := by
  rw [mem_ExactIndependentSet, ← Graph.le_indepNum_iff, ← Graph.le_indepNum_iff]
  omega

/-- **`EXACT INDSET ∈ DP`** ([Arora and Barak, Exercise 5 §8(a), draft of January 2007,
p. 5.10][AroraBarak07]): it is the difference of `IndependentSet` and the preimage of
`IndependentSet` under the polynomial-time map `⟨G, k⟩ ↦ ⟨G, k + 1⟩`. -/
theorem ExactIndependentSet_mem_DP : ExactIndependentSet ∈ DP encIndependentSetInstance := by
  have hid : ComputableInPolyTime (fun x : IndependentSetInstance => x)
      encIndependentSetInstance encIndependentSetInstance := .id'
  have hgraph : ComputableInPolyTime IndependentSetInstance.graph
      encIndependentSetInstance encGraph := encIndependentSetInstance_graph_polyTime hid
  have hm : ComputableInPolyTime IndependentSetInstance.m
      encIndependentSetInstance encNat := encIndependentSetInstance_m_polyTime hid
  have hsucc : ComputableInPolyTime (fun x : IndependentSetInstance => x.m + 1)
      encIndependentSetInstance encNat := .binary_add' hm (.const 1)
  have hmap : ComputableInPolyTime
      (fun x : IndependentSetInstance => (⟨x.graph, x.m + 1⟩ : IndependentSetInstance))
      encIndependentSetInstance encIndependentSetInstance :=
    encIndependentSetInstance_mk_polyTime hgraph hsucc
  have hred : PolyTimeReducible encIndependentSetInstance encIndependentSetInstance
      ((fun x : IndependentSetInstance => (⟨x.graph, x.m + 1⟩ : IndependentSetInstance)) ⁻¹'
        IndependentSet) IndependentSet := ⟨_, hmap, fun _ => Iff.rfl⟩
  exact mem_DP_iff_diff.2 ⟨IndependentSet, IndependentSet.mem_NP, _,
    hred.mem_NP IndependentSet.mem_NP, Set.ext fun _ => mem_ExactIndependentSet_iff⟩

end Cslib.Complexity
