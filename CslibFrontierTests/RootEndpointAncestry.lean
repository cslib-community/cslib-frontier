/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAncestry
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildCounts

open Turing Turing.MultiTapeTM Turing.MultiTapePTM Cslib.Circuits.Frontier NativeChild
open EndpointQuery

-- Both sides of the same parent edge produce distinct child edges carrying the same keys.
example : ChildNumbering.childEdgeList [1, 1] 1 [(0, 1)] [3] = [(0, 5), (1, 5)] := by decide

-- At the next split only packet endpoints survive. Their order and new packet offsets differ.
example : ChildNumbering.childEdgeList [0, 0, 0, 0, 0, 1] 1
    (ChildNumbering.childEdgeList [1, 1] 1 [(0, 1)] [3]) [0, 2] = [(0, 1), (0, 3)] := by decide

-- A genuine grandchild has no endpoint witness at its first index past the end.
example {k q copies : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (x : List Bool) (b σ : ℕ)
    (code : BlockLetter k State b → Fin copies → Bool) (l m : Labels) (p : ℕ × ℕ) :
    let root := RootEndpointQuery.endpointQuery k copies
      (ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)))
    let child := root.child (l.split root)
    let grand := child.child (m.split child)
    let es := m.edges (l.edges (RootPortGraph.ends (q := q) M x b σ code))
    ¬ grand.accepts es.length p := by
  intro root child grand es
  have h : grand.Represents es := RootEndpointQuery.represents_descendant M x b σ code [l, m]
  rw [h.2]
  simp

-- A negative summand at a real edge can be certified with the same single parent endpoint.
example {q : EndpointQuery} {es} (hq : q.Represents es) {i : ℕ} (hi : i < q.size)
    (f : ℕ × ℕ → Bool) : MultiTapeATM.SeededChildCounts.atEndpoint q i f = false ↔
      ∃ p, q.accepts i p ∧ f p = false :=
  MultiTapeATM.SeededChildCounts.atEndpoint_eq_iff hq hi f false
