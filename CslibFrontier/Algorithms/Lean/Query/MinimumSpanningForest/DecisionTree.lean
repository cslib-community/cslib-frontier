/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp

/-!
# MSF Decision Trees and Optimality Structural Lemmas

Umbrella module re-exporting a step toward Theorem 5.8 of [PettieRamachandran2002] (#8624): the
minimum spanning forest comparison decision-tree upper/lower framework (§4.1, p. 23 and §5.1,
pp. 25–26) built over `Cslib.Multigraph.msf`:

* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic`: binary comparison
  decision trees `MSFTree`/`MSFDT`, `optDepth`, bitmask encodings `endsOfMask`, complete padded
  trees `MSFDT.padTo`, and compilation from `FreeM (LEQuery (Fin e))`.
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical`:
  isomorphism invariance (`optDepth_reindex`), embedding monotonicity (`optDepth_le_of_inj`,
  `optDepth_le_of_submask`), `optDepthMN` (`T*(m, n)`) and exact-`m` equivalence
  (`optDepthMN_eq_exact`), Proposition 5.1 (`le_two_mul_optDepthMN`), and Proposition 5.2
  monotonicity bounds.
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp`: Property 5.3
  cut-vertex sufficiency (`msfDecomposes_of_card_inter_le_one`), Lemma 5.5 additivity
  (`optDepth_edgeUnionList_eq_sum`), Corollary 5.6 (`sum_optDepth_le_optDepthMN`), and
  Corollary 5.7 doubling (`two_mul_optDepthMN_le`).

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/
