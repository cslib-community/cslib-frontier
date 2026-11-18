/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.MaxCSP
public import CslibFrontier.Computability.Complexity.Classes.PCP.Promise
import CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT
import CslibFrontier.Computability.PCP.Encoded.Constraints
import CslibFrontier.Computability.PCP.Encoded.Verifier.Reduction
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime

/-!
# Upper bounds for gap problems of 2CSP

The instances are executable constraint graphs (`Cslib.PCP.Encoded.Graph`) whose edges carry the
complete tables of binary constraints over a finite alphabet. This module gives two upper bounds
that contrast with the hardness of `Cslib.Complexity.GapTwoCSP` over `128` symbols
(`Cslib.Complexity.GapTwoCSP_npHard`).

* **Boolean labels.** Writing a Boolean constraint graph as a formula
  (`Cslib.PCP.Encoded.Graph.toCNF`, with one bit per label) gives clauses of width two. So
  satisfiability of Boolean constraint graphs reduces to `Cslib.Complexity.TwoSAT`, which is in
  `P`. Hence every promise problem whose yes-instances are satisfiable and whose no-instances are
  unsatisfiable is in `PromiseP`. With every positive threshold, this covers the gap problem with
  Boolean labels.
* **Constant gap.** For a fixed finite alphabet and a constant gap, the edge-sampling verifier of
  `Cslib.PCP.Encoded.Graph.mem_PromisePCP_of_gapReduction` reads the labels of both endpoints of
  random edges. It places the gap problem in the promise class `PCP(log n, 1)`.

The source is [Goldreich, draft r5][Goldreich2007DraftR5], Definition 9.18 (printed p. 432) and
Exercises 9.24 and 9.25 (printed p. 452). Its `gapCSP^Σ_τ`, for `τ : ℕ → (0, 1]`, has instances
`(G, Φ)`. `G = (V, E)` is a graph, possibly with parallel edges and loops, and `Φ` assigns each
edge a constraint `Σ² → {0, 1}`. The yes-instances satisfy `vlt(G, Φ) = 0`. The no-instances
satisfy `vlt(G, Φ) ≥ τ(|E|)`, where `vlt` is the least proportion of violated constraints over all
assignments `V → Σ`. Here, an instance is a `Graph (Σ → Σ → Bool)`. `vlt` is
`(g.toGraph id).unsatVal`. For a well-formed graph (`g.WellFormed`) over a nonempty alphabet, this
equals the minimum over labellings of the declared vertices
(`Cslib.PCP.Encoded.Graph.unsatVal_toFiniteGraph`). Exercise 9.24 also admits malformed graphs, so
there `unsatVal` is only used through its definition. Edges are counted with multiplicity.
`GapTwoCSP Σ (1 - c)` is `gapCSP^Σ_c` for a constant `c`. Its value is `1 - vlt`, and its
soundness `1 - c`.

## Main results

* `Cslib.Complexity.mem_PromiseP_of_satisfiable_bool`: Exercise 9.24, for every threshold at
  once.
* `Cslib.Complexity.GapTwoCSP_restrict_mem_PromisePCP`: Exercise 9.25.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r5][Goldreich2007DraftR5]
-/

public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Cslib.Logic.PL Turing.MultiTapeTM

/-- **Gap 2CSP with Boolean labels is in `PromiseP`** ([Goldreich, draft r5][Goldreich2007DraftR5],
Exercise 9.24, printed p. 452). Let a promise problem on Boolean constraint graphs have only
satisfiable yes-instances and only unsatisfiable no-instances. Then it is solvable in polynomial
time, by the reduction to 2SAT through `Cslib.PCP.Encoded.Graph.toCNF`.

For every `τ : ℕ → (0, 1]`, Goldreich's `gapCSP^{0,1}_τ` is such a problem. Its yes-instances
have `vlt = 0`. Its no-instances have `vlt ≥ τ(|E|) > 0`, so they are unsatisfiable. The
instantiation is checked in the test module `CslibFrontierTests.GapTwoCSPUpperBounds`. Instances
need not be well-formed: the vertices are all natural numbers, and the declared vertex count is
ignored. -/
theorem mem_PromiseP_of_satisfiable_bool {Q : PromiseProblem (Graph (Bool → Bool → Bool))}
    (hyes : ∀ g ∈ Q.yes, (g.toGraph id).Satisfiable)
    (hno : ∀ g ∈ Q.no, ¬ (g.toGraph id).Satisfiable) :
    Q ∈ PromiseP (Graph.encoding encConstraintTable) := by
  let e : Bool ≃ (Fin 1 → Bool) := (Equiv.funUnique (Fin 1) Bool).symm
  let pairs := (Finset.univ : Finset (Bool × Bool)).toList
  have hpairs : ∀ p, p ∈ pairs := fun p => Finset.mem_toList.2 (Finset.mem_univ p)
  have hmem (g : Graph (Bool → Bool → Bool)) :
      Graph.toCNF e pairs g ∈ TwoSAT ↔ (g.toGraph id).Satisfiable := by
    rw [mem_TwoSAT, Graph.satisfiable_toCNF_iff e pairs hpairs,
      and_iff_right fun c hc => (Graph.length_of_mem_toCNF e pairs hc).le]
  have hred : PromiseProblem.PolyTimeReducible (Graph.encoding encConstraintTable) encCNF Q
      (.ofSet TwoSAT) :=
    ⟨Graph.toCNF e pairs, Graph.isPolyTime_toCNF e pairs,
      fun g hg => (hmem g).2 (hyes g hg), fun g hg => mt (hmem g).1 (hno g hg)⟩
  exact hred.mem_PromiseP (ofSet_mem_PromiseP.2 TwoSAT.mem_P)

/-- **Gap 2CSP with a constant gap is in the promise class `PCP(log n, 1)`** ([Goldreich, draft
r5][Goldreich2007DraftR5], Exercise 9.25, printed p. 452). Fix a finite nonempty alphabet `α` and a
constant `c > 0`. Consider the well-formed constraint graphs: the satisfiable ones as
yes-instances, and those in which every labelling violates at least the proportion `c` of the edges
as no-instances. This is Goldreich's `gapCSP^α_c`, and a polynomial-time verifier with logarithmic
randomness and constantly many queries decides it.

Restricting to well-formed graphs (`Cslib.PCP.Encoded.Graph.WellFormed`, every endpoint a declared
vertex) is the source's `G = (V, E)`. The verifier is the one of the guideline. Each round draws
an index from a power-of-two range of fair bits; an index below the number of edges selects that
edge, and the remaining padding indices accept (with three edges, one of the four indices is
padding). It then reads the two endpoint labels, each a one-hot block of width `|α|` in a proof
with one block per vertex, so a round makes `2 |α|` queries. On a no-instance a round rejects
with probability at least `c / 2`, and a constant number of rounds, depending on `c`, brings the
soundness error to one half. Nonemptiness of `α` is implicit in the source, whose `vlt` is a
minimum over the assignments `V → α`. -/
theorem GapTwoCSP_restrict_mem_PromisePCP {α : Type} [Fintype α] [Nonempty α] {c : ℝ}
    (hc : 0 < c) :
    (GapTwoCSP α (1 - c)).restrict {g | g.WellFormed} ∈
      PromisePCP (fun n => Nat.log 2 n + 1) (fun _ => 1) (Graph.encoding encConstraintTable) := by
  let encode : α → Fin (Fintype.card α) → Bool := fun a i => decide (Fintype.equivFin α a = i)
  have hinj : Function.Injective encode := fun a b h => by
    simpa [encode, eq_comm] using congrFun h (Fintype.equivFin α a)
  exact Graph.mem_PromisePCP_of_gapReduction (graph := id) (eval := id) (Fintype.card α) encode
    (Function.invFun encode) (Function.leftInverse_invFun hinj) .id'
    (Graph.isPolyTime_constraintTableEval ((⟨encode, hinj⟩ : α ↪ _).trans (encPi encBool)))
    (fun _ hg => hg.2) (fun _ hg => mem_yes_GapTwoCSP.1 hg.1) hc
    (fun _ hg => by simpa using (mem_no_GapTwoCSP (by linarith)).1 hg.1)

end Cslib.Complexity
