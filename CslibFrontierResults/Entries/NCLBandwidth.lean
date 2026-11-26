/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.BoundedReduction
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Hardness

/-!
# Collected results: fixed-H word and bounded-bandwidth NCL reconfiguration
-/

register_result "wrochna-fixed-h-word-pspace-hard" where
  title := "Wrochna: fixed-H word reconfiguration is PSPACE-hard"
  topic := "space complexity"
  sources := [
    { paper := Wrochna2014, theorem := "Theorem 3 (PSPACE-hardness direction)",
      locator := "arXiv:1405.0847v1, §3, p. 5; symmetric rewriting in §2, Lemma 2" }
  ]
  theorems := [
    Cslib.Complexity.NCL.HWord.exists_language_pspaceHard
  ]
  scope := "There is one fixed finite directed graph on a nonempty alphabet for which \
    reconfiguration of equal-length words is PSPACE-hard under deterministic multitape \
    polynomial-time many-one reductions. Adjacent letters must form a directed edge, and a \
    move changes one position while preserving legality, including the first and last positions. \
    The input encoding encInstance contains two framed lists of unary finite-alphabet ranks. \
    Outside-fleet agent source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7948#pullrequestreview-6028755848"

register_result "ncl-bounded-bandwidth-planar-and-or-pspace-complete" where
  title := "van der Zanden: bounded-bandwidth planar AND/OR reachability is PSPACE-complete"
  topic := "space complexity"
  sources := [
    { paper := VanDerZanden2015, theorem := "Theorem 6",
      locator := "IPEC 2015, §3, pp. 286–289; bandwidth in §2.1, Definition 4" }
  ]
  theorems := [
    Cslib.Complexity.NCL.exists_BandwidthPlanarAndOrNCL_pspaceComplete
  ]
  scope := "For some fixed natural bandwidth bound, configuration-to-configuration reachability \
    on planar AND/OR multigraphs is PSPACE-complete under deterministic multitape \
    polynomial-time many-one reductions. The general encAndOrNCL encoding uses binary edge \
    numbers and two orientation-bit lists. Membership includes polygonal-embedding planarity \
    and existence of a vertex order with bounded absolute edge spans. Inputs admit loops and \
    parallel edges; the reduction emits loop-free graphs. A single move reverses one edge \
    between legal configurations. The bandwidth bound depends only on the fixed alphabet \
    of the source word problem. Outside-fleet agent source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7948#pullrequestreview-6028755848"
