/-
Copyright (c) 2026 Shriya Thakur, Hugo Akitaya, Freddy Stock,
Adriano Corbelino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Akitaya, Shriya Thakur, Freddy Stock, Adriano Corbelino
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Problems.HittingSet

/-! # NP-completeness of Hitting Set -/

register_result "garey-johnson-hitting-set" where
  title := "Hitting Set is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := GareyJohnson1979, theorem := "Problem SP8 (HITTING SET)",
      locator := "printed p. 222" }
  ]
  theorems := [Cslib.Complexity.HittingSet_npComplete]
  scope := "Instances pair a SetSystem (a ground list and a list of subsets, with binary \
    labels) with a binary bound k under encHittingSet; a yes-instance has at most k distinct \
    ground elements meeting every listed subset. Any k is allowed, subsets may contain labels \
    outside the ground list, and repeated ground entries count once; for 1 ≤ k ≤ |S| and \
    subsets of the ground list this is SP8. Native NP and native polynomial-time Karp \
    reductions; hardness reduces VertexCover, the transformation the source cites. The remark \
    that the problem remains NP-complete with subsets of at most two elements is not stated \
    separately, although the reduction produces only such instances."
