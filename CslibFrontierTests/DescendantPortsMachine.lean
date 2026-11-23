/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantPorts

/-! # One native port verifier on genuine root endpoints -/

public section

namespace Turing.MultiTapeATM.DescendantPorts.Tests

open MultiTapeTM MultiTapeTM.DescendantPorts QuantifiedWord SeededChildCounts
open Cslib.Circuits.Frontier NativeChild

-- A one-interval stationary schedule with one Boolean copy has these two half-edges.
private def graph : DescribedNetwork Unit :=
  ⟨2, [([0], ()), ([1], ()), ([0, 1], ())]⟩

private theorem root_represents :
    (RootEndpointQuery.endpointQuery 0 1 [false, false]).Represents graph.edgeEnds := by
  refine ⟨by decide, ?_⟩
  intro e p
  change RootEndpointQuery.query 0 ⟨[false, false], 1, e⟩ = some p ↔
    e < graph.edgeEnds.length ∧ graph.edgeEnds.getD e (0, 0) = p
  rw [show graph.edgeEnds = [(0, 2), (1, 2)] by decide]
  by_cases he : e < 2
  · have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with rfl | rfl
    · rw [show RootEndpointQuery.query 0 ⟨[false, false], 1, 0⟩ = some (0, 2) by decide]
      simp
    · rw [show RootEndpointQuery.query 0 ⟨[false, false], 1, 1⟩ = some (1, 2) by decide]
      simp
  · have hn := RootEndpointQuery.query_eq_none_of_edgeCount_le 0
      ⟨[false, false], 1, e⟩ (by
        simpa [RootEndpointQuery.edgeCount, RootEndpointQuery.intervals] using Nat.le_of_not_gt he)
    rw [hn]
    simp [he]

/-- Both candidates use the same machine and constants. The accepted request includes the
genuine incident edge; the rejected request omits it. The endpoint continuation is the native
root lookup, rather than an independently supplied predicate or a vacuous empty graph. -/
theorem exists_shared_machine :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C d : ℕ),
      ∀ (host : List Bool) (complete : Bool),
        let ports := if complete then [0] else []
        let a : Input := ⟨[false, false], ⟨1, [], ⟨2, 3, 0, ports⟩⟩⟩
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * (a.raw.length + shortSize a ^ d + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ complete = true) := by
  obtain ⟨U, src, Q, hQ, atm, C, d, hrun⟩ := exists_evaluator 0
  refine ⟨U, src, Q, hQ, atm, C, d, ?_⟩
  intro host complete ports a start time
  have hs := hrun host a
  have hv := plays_program_network graph (r := 2) (by decide) (by decide)
    (RootEndpointQuery.endpointQuery 0 1 [false, false]) root_represents 0 ports
  refine ⟨hs.1, hs.2.trans (hv.trans ?_)⟩
  cases complete <;> simp [graph, ports]

end Turing.MultiTapeATM.DescendantPorts.Tests
