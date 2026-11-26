/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Completeness

/-! # Collected results: directed symmetric self-closing door reachability -/

register_result "directed-symmetric-self-closing-door-pspace" where
  title := "Directed symmetric self-closing door reachability is PSPACE-complete"
  topic := "space complexity"
  sources := [
    { paper := AniBosboomDemaineEtAl2021,
      theorem := "Corollary 2.4 (directed symmetric case)",
      locator := "Section 2.2, p. 3:5 (PDF p. 5); model in Section 1, p. 3:3, \
        and Section 2.1, p. 3:4" }
  ]
  theorems := [
    Cslib.Complexity.SelfClosingDoor.Reachability_pspaceHard,
    Cslib.Complexity.SelfClosingDoor.Reachability_pspaceComplete
  ]
  scope := "Single-player target-location reachability in arbitrary finite networks of \
    directed symmetric self-closing doors with prescribed initial bits and unrestricted final \
    door bits. Location labels encode freely connected wiring components, allowing identified \
    endpoints, loops and parallel doors; no planarity restriction. Explicit framed door lists \
    and binary location labels, uniform multitape polynomial-time many-one reductions. \
    Completeness combines the directed symmetric hardness case with a Savitch space upper bound. \
    Source check: https://github.com/cslib-community/cslib-frontier/pull/8343#issuecomment-7138309266"
