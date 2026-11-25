/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.MaxFlow.RelabelToFront

register_result "goldberg-tarjan-relabel-to-front" where
  title := "Goldberg–Tarjan relabel-to-front push–relabel scheduler and O(|V|³) operation, \
    discharge, and current-arc advance count bounds"
  topic := "algorithms"
  sources := [
    { paper := GoldbergTarjan1988, theorem := unverified, locator := unverified },
    { paper := CLRS2009, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront.discharge_spec,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFrontWith_correct,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFrontWith_bounds,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFrontWith_totalSteps_le,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFront_correct,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFrontDense_correct,
    Cslib.Algorithms.Lean.MaxFlow.relabelToFrontExact_correct
  ]
  scope := "Pure Lean formalization on integral networks N : Network V over finite vertex types \
    [Fintype V] [DecidableEq V] (CslibFrontier.Algorithms.Lean.MaxFlow.Basic) with N.s ≠ N.t, \
    candidate neighbor lists adj : V → List V satisfying IsAdjacency N adj (covering every \
    non-loop pair u ≠ v with 0 < N.cap u v + N.cap v u), and a duplicate-free enumeration vs of \
    V \\ {N.s, N.t}. Proves that discharge preserves CurrentArcInv, executes a valid run of \
    generic PushRelabel operations with at most one nonsaturating push, and drains its target \
    vertex, and that relabelToFrontWith maintains topological admissibility order TopoOrder \
    (RTFInv) and terminates in a maximum flow and minimum gap cut of equal value with at most \
    (|V| - 2) * ((|V| - 2) * (2 * |V| - 1) + 1) ≤ 2 |V|³ discharge calls, ≤ 2 |V|² relabels, \
    ≤ 2 |V| |E| saturating pushes, ≤ 4 |V|³ nonsaturating pushes and total push/relabel \
    operations, ≤ 2 |V| ∑_{v ≠ s, t} |adj v| current-arc pointer advances, and ≤ 8 |V|³ \
    combined discharges + ops.length + advances when every adj v is duplicate-free (with \
    executable Fin n endpoints relabelToFront, relabelToFrontDense, and relabelToFrontExact \
    achieving ≤ 4 n |E| advances). Counts push/relabel operations, discharge calls, and \
    current-arc advances only; Preflow.relabelHeight scans Finset.univ and Function.update / \
    list concatenation are uncharged pure operations, so a certified Word-RAM O(|V|³) running \
    time (#3373) remains open. Primary-PDF theorem numbers and page locators in \
    [GoldbergTarjan1988] and [CLRS2009] were not verified against local PDFs on disk."
