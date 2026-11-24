/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
import CslibFrontier.Logics.Propositional.CNF.Dimacs
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! # Reading LAD graphs

The LAD graph format of the subgraph isomorphism benchmarks, as read by the subgraph isomorphism
front end of CakePB [Gocht, McCreesh, Myreen, Nordström, Oertel and
Tan][GochtMcCreeshMyreenNordstromOertelTan2024] (`parse_lad` and `check_good_graph` in
`graph_basicScript.sml`, CakeML commit `14856fcf`, `examples/pseudo_bool/graph_encoding/`): a
first line holding the number of vertices `n`, then one line per vertex `u = 0, 1, …`, holding
the number `d` of neighbours of `u` followed by the `d` neighbours. The vertices are numbered from
`0`.

`Cslib.Logic.PL.VeriPB.Graph.parseLAD` accepts a text exactly when CakePB does, except for loops,
and on an accepted loop-free text it gives the same adjacency relation as CakePB. The neighbour
lists themselves may differ: CakePB stores each list as a set (`list_to_num_set` in
`parse_lad_edges`) and its encoder reads the neighbours sorted, while the reader here keeps each
list as written, a repeated neighbour included (`"2\n2 1 1\n1 0\n"` gives `[[1, 1], [0]]`). As
in CakePB:
* the words of a line are separated by spaces, tabs and carriage returns, and are decimal numerals
  (leading zeros allowed);
* a line holding no word is rejected, but the text may end with a newline;
* the count `d` must be the number of neighbours that follow, and a neighbour may be repeated;
* there may be fewer than `n` vertex lines, a vertex without one having no neighbours, but not
  more;
* every neighbour is below `n`, and the lists are symmetric: `v` is listed for `u` exactly when `u`
  is listed for `v` (CakePB's `check_good_graph`, its "undirectedness check").

CakePB also accepts a loop, a vertex listed among its own neighbours, which a subgraph
isomorphism must then map to a loop. A simple graph has no loops, so the reader rejects them.

With these checks the simple graph `Cslib.Logic.PL.VeriPB.Graph.LADGraph.graph` of a graph read
has exactly the edges listed (`Cslib.Logic.PL.VeriPB.Graph.adj_iff_of_parseLAD`): nothing is
symmetrized or dropped. The words of a line are read by the DIMACS CNF reader's
`Cslib.Logic.PL.Dimacs.words`, its lines split by the OPB lexer's
`Cslib.Logic.PL.VeriPB.Text.splitChars`, and its numbers by `Nat.ofDecimal?`.

The reader is defined on lists of characters by structural recursion, so the kernel evaluates it.
It is trusted to read a file as intended: no theorem relates the text to the lists read. Its
helpers are private, and a client that evaluates it in the kernel imports this module with
`import all`.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Graph.LADGraph`, `Cslib.Logic.PL.VeriPB.Graph.LADGraph.graph`: a graph
  read from LAD, and its simple graph.
* `Cslib.Logic.PL.VeriPB.Graph.parseLAD`: the reader.

## Main statements

* `Cslib.Logic.PL.VeriPB.Graph.adj_iff_of_parseLAD`: the simple graph of a graph read has exactly
  the edges listed.
-/

public section

namespace Cslib.Logic.PL.VeriPB.Graph

open Cslib.Logic.PL.Dimacs

/-- **A graph read from LAD**: its number of vertices `n`, the vertices being `Fin n`, and the
neighbour lists of the vertices `0, 1, …` in the order of the file, a vertex beyond the end of the
list having no neighbours. -/
structure LADGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The neighbour lists. -/
  nbrs : List (List (Fin n))
  deriving DecidableEq, Repr

namespace LADGraph

/-- **The simple graph of a LAD graph**: `u` and `v` are adjacent when `u ≠ v` and `v` is listed
for `u` or `u` for `v`. -/
@[expose] def graph (g : LADGraph) : SimpleGraph (Fin g.n) :=
  SimpleGraph.fromRel fun u v => v ∈ g.nbrs.getD u.val []

instance (g : LADGraph) : DecidableRel g.graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun u v => v ∈ g.nbrs.getD u.val []).Adj)

@[simp] theorem graph_adj {g : LADGraph} {u v : Fin g.n} :
    g.graph.Adj u v ↔ u ≠ v ∧ (v ∈ g.nbrs.getD u.val [] ∨ u ∈ g.nbrs.getD v.val []) :=
  SimpleGraph.fromRel_adj _ u v

end LADGraph

/-- A vertex: a numeral below `n`. -/
private def vertex? (n : ℕ) (w : List Char) : Option (Fin n) :=
  (Nat.ofDecimal? w).bind fun v => if h : v < n then some ⟨v, h⟩ else none

/-- A vertex line `d v₁ … v_d`, as words: its neighbours. -/
private def vertexLine? (n : ℕ) : List (List Char) → Option (List (Fin n))
  | [] => none
  | d :: ws =>
    (Nat.ofDecimal? d).bind fun d => if ws.length = d then ws.mapM (vertex? n) else none

/-- The neighbour lists are at most `n`, loop-free and symmetric. -/
private def isGood (n : ℕ) (ls : List (List (Fin n))) : Bool :=
  decide (ls.length ≤ n) && (List.finRange n).all fun u =>
    (ls.getD u.val []).all fun v => u != v && (ls.getD v.val []).contains u

/-- The lines of a text, without the empty piece after a final newline. -/
private def ladLines (s : String) : List (List Char) :=
  let ls := Text.splitChars (· == '\n') s.toList
  if ls.getLast? = some [] then ls.dropLast else ls

/-- **Reading a LAD graph**: the number of vertices `n` alone on the first line, then the vertex
lines `d v₁ … v_d` of the vertices `0, 1, …`, at most `n` of them, with every `vᵢ < n`. Fails on a
malformed or empty line, on a loop and on neighbour lists that are not symmetric. -/
def parseLAD (s : String) : Option LADGraph :=
  match (ladLines s).map (words · []) with
  | [h] :: ls =>
    (Nat.ofDecimal? h).bind fun n =>
      (ls.mapM (vertexLine? n)).bind fun nb => if isGood n nb then some ⟨n, nb⟩ else none
  | _ => none

private theorem of_isGood {n : ℕ} {ls : List (List (Fin n))} (h : isGood n ls = true)
    {u v : Fin n} (hv : v ∈ ls.getD u.val []) : u ≠ v ∧ u ∈ ls.getD v.val [] := by
  simp only [isGood, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  exact h.2 u v hv

/-- **The graph read has exactly the edges listed**: in the simple graph of a graph read from LAD,
`u` and `v` are adjacent exactly when `v` is listed for `u` (CakePB's `check_good_graph`). -/
theorem adj_iff_of_parseLAD {s : String} {g : LADGraph} (h : parseLAD s = some g)
    (u v : Fin g.n) : g.graph.Adj u v ↔ v ∈ g.nbrs.getD u.val [] := by
  unfold parseLAD at h
  split at h
  · obtain ⟨n, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨nb, -, h⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at h with hg
    cases h
    rw [LADGraph.graph_adj]
    constructor
    · rintro ⟨-, hv | hu⟩
      · exact hv
      · exact (of_isGood hg hu).2
    · intro hv
      exact ⟨(of_isGood hg hv).1, .inl hv⟩
  · cases h

end Cslib.Logic.PL.VeriPB.Graph
