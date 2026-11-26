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

/-! # Reading DIMACS graphs

The DIMACS graph format of the Second DIMACS Implementation Challenge, as read by the graph front
ends of CakePB [Gocht, McCreesh, Myreen, Nordström, Oertel and
Tan][GochtMcCreeshMyreenNordstromOertelTan2024] (`parse_dimacs` in `graph_basicScript.sml`,
CakeML commit `14856fcf`, `examples/pseudo_bool/graph_encoding/`): a header `p edge n m` (or
`p col n m`) giving the number of vertices `n`, then one line `e u v` per edge, with
`1 ≤ u, v ≤ n`. Lines whose first word starts with `c` are comments, and empty lines are skipped.

`Cslib.Logic.PL.VeriPB.Graph.parseDIMACSGraph` reads the vertex `u` of the file as the vertex
`u - 1` of `Fin n`, as CakePB numbers it from `0`. It fails on a missing or malformed header and on
any other line that is not an edge line with both ends in `1, …, n`: that is CakePB's
well-formedness check (`parse_dimacs_edge`). The edges are read as elements of `Fin n × Fin n`, so
that a parsed graph is well formed by its type: CakePB's `parse_dimacs_good_graph` (the graph is
undirected and mentions only vertices below `n`) holds by construction, and the graph
`Cslib.Logic.PL.VeriPB.Graph.DimacsGraph.graph` is a `SimpleGraph (Fin n)` with decidable
adjacency. As in CakePB, an edge may be listed in either direction or both, repeated edges are
allowed, and the edge count `m` of the header is not checked. A loop `e u u` is accepted and
dropped, since a simple graph has none; it changes no clique.

The reader accepts some files that `parse_dimacs` rejects, and reads them as CakePB reads the same
file once the difference is removed:
* blank lines are skipped, where CakePB keeps them and fails on them;
* a line whose first word starts with `c` is a comment, where CakePB requires the word `c` itself
  (`nocomment_line`);
* the numbers may contain the digit separator `_` of `Cslib.Logic.PL.Dimacs.natOfChars?`, where
  CakePB reads them with `fromNatString`.

The words and numbers of a line are
read by the DIMACS CNF reader's `Cslib.Logic.PL.Dimacs.words` and
`Cslib.Logic.PL.Dimacs.natOfChars?`, and its lines split by the OPB lexer's
`Cslib.Logic.PL.VeriPB.Text.splitChars`.

The reader is defined on lists of characters by structural recursion, so the kernel evaluates it.
It is trusted to read a file as intended: no theorem relates the text to the graph read. Its
helpers are private, and a client that evaluates it in the kernel imports this module with
`import all`.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Graph.DimacsGraph`, `Cslib.Logic.PL.VeriPB.Graph.DimacsGraph.graph`: a
  graph read from DIMACS, and its simple graph.
* `Cslib.Logic.PL.VeriPB.Graph.parseDIMACSGraph`: the reader.
-/

public section

namespace Cslib.Logic.PL.VeriPB.Graph

open Cslib.Logic.PL.Dimacs

/-- **A graph read from DIMACS**: its number of vertices `n`, the vertices being `Fin n`, and its
edges in the order of the file, each as the pair of its ends. -/
structure DimacsGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges. -/
  edges : List (Fin n × Fin n)
  deriving DecidableEq, Repr

namespace DimacsGraph

/-- **The simple graph of a DIMACS graph**: `u` and `v` are adjacent when `u ≠ v` and the edge
`(u, v)` or `(v, u)` is listed. -/
@[expose] def graph (g : DimacsGraph) : SimpleGraph (Fin g.n) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ g.edges

instance (g : DimacsGraph) : DecidableRel g.graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun u v => (u, v) ∈ g.edges).Adj)

@[simp] theorem graph_adj {g : DimacsGraph} {u v : Fin g.n} :
    g.graph.Adj u v ↔ u ≠ v ∧ ((u, v) ∈ g.edges ∨ (v, u) ∈ g.edges) :=
  SimpleGraph.fromRel_adj _ u v

end DimacsGraph

/-- A vertex `u` of the file, `1 ≤ u ≤ n`, as the vertex `u - 1`. -/
private def vertex? (n : ℕ) (w : List Char) : Option (Fin n) :=
  (natOfChars? w).bind fun u => if h : 0 < u ∧ u ≤ n then some ⟨u - 1, by omega⟩ else none

/-- An edge line `e u v`, as words, with both ends among the `n` vertices. -/
private def edge? (n : ℕ) : List (List Char) → Option (Fin n × Fin n)
  | [['e'], u, v] => (vertex? n u).bind fun u => (vertex? n v).map fun v => (u, v)
  | _ => none

/-- The header `p edge n m` or `p col n m`, as words: the numbers `n` and `m`. -/
private def header? : List (List Char) → Option (ℕ × ℕ)
  | [['p'], lab, v, e] =>
    if lab = ['e', 'd', 'g', 'e'] ∨ lab = ['c', 'o', 'l'] then
      (natOfChars? v).bind fun v => (natOfChars? e).map fun e => (v, e)
    else none
  | _ => none

/-- The edge lines, as words, each with both ends among the `n` vertices. -/
private def edges? (n : ℕ) : List (List (List Char)) → Option (List (Fin n × Fin n))
  | [] => some []
  | l :: ls => (edge? n l).bind fun e => (edges? n ls).map (e :: ·)

/-- A line, as words, is read: it is not empty and its first word does not start with `c`. -/
private def isRead : List (List Char) → Bool
  | [] => false
  | w :: _ => w.head? != some 'c'

/-- **Reading a DIMACS graph**: the header `p edge n m` or `p col n m` as the first line that is
neither empty nor a comment, then the edge lines `e u v` with `1 ≤ u, v ≤ n`, the vertex `u` read
as `u - 1`. Fails on a missing or malformed header and on any other line. -/
def parseDIMACSGraph (s : String) : Option DimacsGraph :=
  match ((Text.splitChars (· == '\n') s.toList).map (words · [])).filter isRead with
  | [] => none
  | h :: ls => (header? h).bind fun (n, _) => (edges? n ls).map fun es => ⟨n, es⟩

end Cslib.Logic.PL.VeriPB.Graph
