/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Chosen
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Dimacs
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! # Maximum clique as a pseudo-Boolean optimization problem, end to end

CakePB's encoding of maximum clique [Gocht, McCreesh, Myreen, Nordström, Oertel and
Tan][GochtMcCreeshMyreenNordstromOertelTan2024] (`cliqueScript.sml`, CakeML commit `14856fcf`,
`examples/pseudo_bool/graph_encoding/`), with its correctness theorem, and the end-to-end
theorems that turn a VeriPB proof accepted by the verified checker into bounds on the cliques of
the graph.

**The encoding** (`Cslib.Logic.PL.VeriPB.Graph.encodeClique`, CakePB's `encode` and
`clique_obj`) of a graph `G` on `Fin n` has the variable `v` for the vertex `v`, which is `x(v + 1)`
in OPB text, and the constraint `~x + ~y ≥ 1` for each pair of vertices `x < y` that are not
adjacent, in the order of CakePB's (`x` first, then `y`). It minimizes the number of vertices not
chosen, `∑ᵥ ~xᵥ`, written here as `∑ᵥ -xᵥ + n`, the objectives of the checker being linear forms
over variables (`Cslib.Logic.PL.VeriPB.Objective`).

**Correctness** (CakePB's `encode_correct`). An assignment `σ` chooses the vertices
`Cslib.Logic.PL.VeriPB.chosen n σ`. It satisfies the constraints exactly when the vertices it
chooses form a clique (`Cslib.Logic.PL.VeriPB.Graph.forall_holds_cliqueConstraints_iff`), every set
of vertices is chosen by some assignment (`Cslib.Logic.PL.VeriPB.exists_chosen_eq`), and the
objective is `n` minus the number of vertices chosen
(`Cslib.Logic.PL.VeriPB.Graph.eval_cliqueObjective`). So the solutions are exactly the cliques, and
the objective value of a clique `s` is `n - |s|`.

**End to end.** The encoding is printed as OPB text (`Cslib.Logic.PL.VeriPB.Text.printOPB`), and
the proof is checked against that text by `Cslib.Logic.PL.VeriPB.Text.checkOPBOutput`, as the
VeriPB tool would check it against the same file. The round trip of the printer
(`Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB_printOPB`) carries the conclusion back to the
encoding built in Lean. A `BOUNDS lb : q ub` conclusion is turned into bounds `(l, u)` on clique
sizes as CakePB's `conv_concl` does (`Cslib.Logic.PL.VeriPB.Graph.convConcl`): `u = n - lb` and
`l = n - ub`, with `INF` and the impossible negative bounds handled as in CakePB.
* `Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkCliqueGraph` (CakePB's
  `full_encode_sem_concl`): if `Cslib.Logic.PL.VeriPB.Graph.checkCliqueGraph G pbp = some (l, u)`,
  every clique of `G` has at most `u` vertices and some clique has at least `l`;
  `Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkCliqueGraph` (`full_encode_sem_concl_check`):
  equal bounds `k` give `G.cliqueNum = k`.
* `Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkClique`: the checker
  `Cslib.Logic.PL.VeriPB.Graph.checkClique` takes a DIMACS graph and a proof as text, and if it
  returns `(l, u)`, the text parses to a graph (`Cslib.Logic.PL.VeriPB.Graph.parseDIMACSGraph`)
  whose cliques have at most `u` vertices, one of them at least `l`;
  `Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkClique`: equal bounds `k` give clique number
  `k`. This is the pure functional specification behind the paper's Figure 5, CakePB's
  `clique_sem` in `cliqueProgScript.sml`, not Figure 5 itself: Figure 5 (`main_semantics`) is a
  theorem about the compiled x64 machine code, its file and command-line I/O and its output, which
  nothing here covers.

The trusted base is the DIMACS graph reader, the definitions of `SimpleGraph`, `IsClique` and
`cliqueNum`, and the Lean kernel for a check run by `decide +kernel`, or Lean's compiler for a
compiled run. The encoding, the OPB printer and reader, the proof reader and the checker are
verified. CakePB's own end-to-end theorem also covers its compiled machine code.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Graph.encodeClique`: the encoding.
* `Cslib.Logic.PL.VeriPB.Graph.convConcl`: bounds on clique sizes from a `BOUNDS` conclusion.
* `Cslib.Logic.PL.VeriPB.Graph.checkCliqueGraph`, `Cslib.Logic.PL.VeriPB.Graph.checkClique`: the
  checkers, for a graph built in Lean and for a DIMACS graph.

## Main results

* `Cslib.Logic.PL.VeriPB.Graph.forall_holds_cliqueConstraints_iff`,
  `Cslib.Logic.PL.VeriPB.exists_chosen_eq`,
  `Cslib.Logic.PL.VeriPB.Graph.eval_cliqueObjective`: correctness of the encoding.
* `Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkCliqueGraph`,
  `Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkCliqueGraph`,
  `Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkClique`,
  `Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkClique`: the end-to-end theorems.

## References

* [S. Gocht, C. McCreesh, M. O. Myreen, J. Nordström, A. Oertel, Y. K. Tan, *End-to-End
  Verification for Subgraph Solving*][GochtMcCreeshMyreenNordstromOertelTan2024]
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB.Graph

open PBConstr Text

variable {n : ℕ}

/-! ### The encoding -/

/-- The constraints of the encoding: `~x + ~y ≥ 1` for each pair `x < y` of vertices that are not
adjacent, ordered by `x` and then `y` (CakePB's `mk_constraint`). -/
def cliqueConstraints (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List PBConstr :=
  (List.finRange n).flatMap fun x =>
    ((List.finRange n).filter fun y => decide (x < y ∧ ¬ G.Adj x y)).map fun y =>
      ⟨[(1, (x.val, false)), (1, (y.val, false))], 1⟩

/-- The objective of the encoding: the number `∑ᵥ ~xᵥ = ∑ᵥ -xᵥ + n` of vertices not chosen. -/
def cliqueObjective (n : ℕ) : Objective := ⟨(List.finRange n).map fun v => (v.val, -1), n⟩

/-- **The maximum clique encoding** of a graph on `Fin n`: the constraints
`Cslib.Logic.PL.VeriPB.Graph.cliqueConstraints`, minimizing the number of vertices not chosen. -/
def encodeClique (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Instance :=
  ⟨cliqueConstraints G, some (cliqueObjective n), none⟩

/-! ### Correctness -/

/-- The constraint `~x + ~y ≥ 1` of the non-edge `x`, `y`. -/
private abbrev nonEdge (x y : Fin n) : PBConstr := ⟨[(1, (x.val, false)), (1, (y.val, false))], 1⟩

private theorem holds_nonEdge_iff {x y : Fin n} {σ : ℕ → Bool} :
    (nonEdge x y).Holds σ ↔ ¬ (σ x.val = true ∧ σ y.val = true) := by
  simp only [Holds, lhs, termVal, Literal.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  cases σ x.val <;> cases σ y.val <;> decide

private theorem mem_cliqueConstraints {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {c : PBConstr} :
    c ∈ cliqueConstraints G ↔ ∃ x y : Fin n, x < y ∧ ¬ G.Adj x y ∧ c = nonEdge x y := by
  simp only [cliqueConstraints, List.mem_flatMap, List.mem_finRange, List.mem_map,
    List.mem_filter, decide_eq_true_eq, true_and, and_assoc, @eq_comm PBConstr _ c]

/-- **The solutions of the encoding are the cliques**: an assignment satisfies the constraints of
the encoding exactly when the vertices it chooses form a clique. -/
theorem forall_holds_cliqueConstraints_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : ℕ → Bool) :
    (∀ c ∈ cliqueConstraints G, c.Holds σ) ↔ G.IsClique (chosen n σ : Set (Fin n)) := by
  have hmem : ∀ v : Fin n, v ∈ (chosen n σ : Set (Fin n)) ↔ σ v.val = true := by simp
  constructor
  · intro h x hx y hy hne
    rw [hmem] at hx hy
    by_contra hadj
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact holds_nonEdge_iff.1 (h _ (mem_cliqueConstraints.2 ⟨x, y, hlt, hadj, rfl⟩)) ⟨hx, hy⟩
    · exact holds_nonEdge_iff.1 (h _ (mem_cliqueConstraints.2
        ⟨y, x, hlt, fun h' => hadj h'.symm, rfl⟩)) ⟨hy, hx⟩
  · intro h c hc
    obtain ⟨x, y, hxy, hadj, rfl⟩ := mem_cliqueConstraints.1 hc
    exact holds_nonEdge_iff.2 fun ⟨hx, hy⟩ =>
      hadj (h ((hmem x).2 hx) ((hmem y).2 hy) hxy.ne)

/-- **The objective value** of an assignment is `n` minus the number of vertices it chooses. -/
theorem eval_cliqueObjective (σ : ℕ → Bool) :
    (cliqueObjective n).eval σ = n - (chosen n σ).card := by
  have hcard : ((chosen n σ).card : ℤ) = ∑ v : Fin n, ((σ v.val).toNat : ℤ) := by
    rw [chosen, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    cases σ v.val <;> rfl
  rw [hcard]
  simp only [Objective.eval, cliqueObjective, linVal, List.map_map, Function.comp_def, neg_one_mul]
  rw [← Fin.sum_univ_def, Finset.sum_neg_distrib]
  ring

/-! ### End to end -/

/-- **Bounds on clique sizes from a conclusion**, as CakePB's `conv_concl`: `BOUNDS lb : q ub`
gives the bounds `(l, u)` with `u = n - lb` (`0` for `lb = INF`; `n` for `lb ≤ 0`) and
`l = n - |ub|` (`0` for `ub = INF`). Other conclusions give nothing. -/
def convConcl (n : ℕ) : Conclusion → Option (ℕ × ℕ)
  | .bounds lb _ ub _ =>
    some ((ub.map fun u => n - u.natAbs).getD 0, (lb.map fun l => n - l.toNat).getD 0)
  | _ => none

/-- **The clique checker for a graph built in Lean**: check the proof `pbp` against the printed
OPB text of the encoding of `G`, and read the bounds on clique sizes off its conclusion. -/
def checkCliqueGraph (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (pbp : String) :
    Option (ℕ × ℕ) :=
  ((checkOPBOutput (printOPB (encodeClique G)) pbp).map (·.1)).bind (convConcl n)

/-- **The clique checker for a DIMACS graph**: read the graph, then check the proof `pbp` against
its encoding (`Cslib.Logic.PL.VeriPB.Graph.checkCliqueGraph`). -/
def checkClique (graph pbp : String) : Option (ℕ × ℕ) :=
  (parseDIMACSGraph graph).bind fun g => checkCliqueGraph g.graph pbp

/-- **Clique bounds from an accepted proof** (CakePB's `full_encode_sem_concl`): if the checker
accepts a proof against the encoding of `G` with bounds `(l, u)`, then every clique of `G` has at
most `u` vertices and some clique has at least `l`. -/
theorem clique_bounds_of_checkCliqueGraph {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {pbp : String} {l u : ℕ} (h : checkCliqueGraph G pbp = some (l, u)) :
    (∀ s : Finset (Fin n), G.IsClique (s : Set (Fin n)) → s.card ≤ u) ∧
      ∃ s : Finset (Fin n), G.IsClique (s : Set (Fin n)) ∧ l ≤ s.card := by
  obtain ⟨concl, hc, hconv⟩ := Option.bind_eq_some_iff.1 h
  cases concl with
  | bounds lb q ub asg =>
    obtain ⟨f, hf, hlb, hub⟩ := bounds_of_checkOPB_printOPB (stdNames_covers _) hc
    cases hf
    simp only [convConcl, Option.some.injEq, Prod.mk.injEq] at hconv
    obtain ⟨rfl, rfl⟩ := hconv
    have hcard : ∀ σ, (chosen n σ).card ≤ n := fun σ =>
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    constructor
    · intro s hs
      obtain ⟨σ, rfl⟩ := exists_chosen_eq s
      obtain ⟨l', rfl, hle⟩ := hlb σ ((forall_holds_cliqueConstraints_iff G σ).2 hs)
      rw [eval_cliqueObjective] at hle
      have := hcard σ
      simp only [Option.map_some, Option.getD_some]; omega
    · cases ub with
      | none => exact ⟨∅, by simp, by simp⟩
      | some u' =>
        obtain ⟨σ, hσ, hle⟩ := hub u' rfl
        refine ⟨chosen n σ, (forall_holds_cliqueConstraints_iff G σ).1 hσ, ?_⟩
        rw [eval_cliqueObjective] at hle
        have := hcard σ
        simp only [Option.map_some, Option.getD_some]; omega
  | _ => simp [convConcl] at hconv

/-- **The clique number from an accepted proof** (CakePB's `full_encode_sem_concl_check`): if the
checker accepts a proof against the encoding of `G` with equal bounds `(k, k)`, then the clique
number of `G` is `k`. -/
theorem cliqueNum_eq_of_checkCliqueGraph {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {pbp : String} {k : ℕ} (h : checkCliqueGraph G pbp = some (k, k)) : G.cliqueNum = k := by
  obtain ⟨hub, s, hs, hle⟩ := clique_bounds_of_checkCliqueGraph h
  obtain ⟨t, ht⟩ := G.exists_isNClique_cliqueNum
  exact le_antisymm (ht.card_eq ▸ hub t ht.isClique) (hle.trans hs.card_le_cliqueNum)

/-- **Clique bounds for a DIMACS graph**, the pure functional specification step behind Figure 5
of the paper (CakePB's `clique_sem`), not Figure 5 itself, which is about compiled machine code
and its I/O: if the checker returns the bounds `(l, u)` for the DIMACS text `graph` and the proof
`pbp`, then the text parses to a graph `g` every clique of which has at most `u` vertices, and
some clique of which has at least `l`. -/
theorem clique_bounds_of_checkClique {graph pbp : String} {l u : ℕ}
    (h : checkClique graph pbp = some (l, u)) :
    ∃ g, parseDIMACSGraph graph = some g ∧
      (∀ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) → s.card ≤ u) ∧
      ∃ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) ∧ l ≤ s.card := by
  obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨g, hg, clique_bounds_of_checkCliqueGraph h⟩

/-- **The clique number of a DIMACS graph** (CakePB's `clique_sem` with equal bounds): if the
checker returns the bounds `(k, k)` for the DIMACS text `graph` and the proof `pbp`, then the text
parses to a graph of clique number `k`. -/
theorem cliqueNum_eq_of_checkClique {graph pbp : String} {k : ℕ}
    (h : checkClique graph pbp = some (k, k)) :
    ∃ g, parseDIMACSGraph graph = some g ∧ g.graph.cliqueNum = k := by
  obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨g, hg, cliqueNum_eq_of_checkCliqueGraph h⟩

end Cslib.Logic.PL.VeriPB.Graph
