/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Instruction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildPorts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Pairwise
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import Mathlib.Data.List.GetD

/-!
# Checking an ordered port list through endpoint access

A proposed port list is fixed before a universal edge challenge. One pair of endpoints is then
guessed for that edge, and a universal selector checks either the exact endpoint query or the
equivalence between incidence and membership in the proposed list. The structural guard requires
an in-range vertex and strictly increasing, in-range ports, including when there are no edges.

This original game needs no prefix-rank queries and makes at most one endpoint request on a
branch. `plays_program` characterizes it for any represented endpoint relation;
`plays_program_network` identifies its accepted candidate with a rows-first network's actual
ordered ports. The raw assignment and the network's complete vertex and edge lists are absent
from the executable query.

The native endpoint continuation and assignment-bit checks are composed separately in the
compressed entry construction tracked by #4728.
-/

public section

namespace Turing.MultiTapeTM.DescendantPorts

open Cslib Cslib.BitString Cslib.Circuits.Frontier
open MultiTapeATM QuantifiedWord SeededChildCounts NativeChild

/-- A candidate ordered port list in a graph with binary edge and vertex counts. -/
structure Query where
  /-- Exact number of graph edges, in binary. -/
  edges : ℕ
  /-- Exact number of graph vertices, in binary. -/
  vertices : ℕ
  /-- Selected vertex number, in binary. -/
  vertex : ℕ
  /-- Proposed ports in their required increasing order, with binary edge numbers. -/
  ports : List ℕ
  deriving DecidableEq

/-- Binary graph counts and vertex key followed by the framed list of binary port numbers. -/
enc_structure encQuery : Query where
  edges : encNat, vertices : encNat, vertex : encNat, ports : (encList encNat)

/-- The selected vertex exists, and the proposed port numbers are increasing and in range. -/
@[expose] def guard (q : Query) : Bool :=
  decide (q.vertex < q.vertices) && decide (q.ports.Pairwise (· < ·)) &&
    q.ports.all (fun e => decide (e < q.edges))

private theorem guard_iff (q : Query) : guard q = true ↔
    q.vertex < q.vertices ∧ q.ports.Pairwise (· < ·) ∧ ∀ e ∈ q.ports, e < q.edges := by
  simp [guard, List.all_eq_true, and_assoc]

/-- Universal edge, two shared existential endpoints, then a universal check selector. -/
@[expose] def flags (q : Query) : List Bool :=
  List.replicate q.edges.size true ++
    (List.replicate q.vertices.size false ++ (List.replicate q.vertices.size false ++ [true]))

/-- A common endpoint guess is checked either against the graph or against port membership. -/
@[expose] def dispatch (q : Query) (e row column : ℕ) (endpoint : Bool) : Joined.Instruction :=
  if guard q then
    if e < q.edges then
      if endpoint then .inr (e, (row, column))
      else .inl (decide (q.vertex = row ∨ q.vertex = column) == decide (e ∈ q.ports))
    else .inl true
  else .inl false

/-- Parse one completed quantified word into a local verdict or its only endpoint request. -/
@[expose] def program (x : Query × List Bool) : Joined.Instruction :=
  let q := x.1
  let rest := x.2.drop q.edges.size
  let tail := rest.drop q.vertices.size
  dispatch q (ofBits (x.2.take q.edges.size))
    (ofBits (rest.take q.vertices.size)) (ofBits (tail.take q.vertices.size))
    ((tail.drop q.vertices.size).headD false)

private theorem program_fields (q : Query) (e : Fin (2 ^ q.edges.size))
    (row column : Fin (2 ^ q.vertices.size)) (bit : Bool) :
    program (q, lowBits q.edges.size e.val ++ (lowBits q.vertices.size row.val ++
      (lowBits q.vertices.size column.val ++ [bit]))) =
        dispatch q e.val row.val column.val bit := by
  simp [program, length_lowBits, ofBits_lowBits e.isLt, ofBits_lowBits row.isLt,
    ofBits_lowBits column.isLt]

private theorem plays_fields (q : Query) (endpoint : EndpointQuery) :
    plays (fun xs => Joined.holds endpoint (program (q, xs))) [] (flags q) ↔
      ∀ e : Fin (2 ^ q.edges.size), ∃ row : Fin (2 ^ q.vertices.size),
        ∃ column : Fin (2 ^ q.vertices.size),
          ∀ bit, Joined.holds endpoint (dispatch q e.val row.val column.val bit) := by
  rw [flags, plays_forall_field]
  apply forall_congr'
  intro e
  rw [plays_exists_field]
  apply exists_congr
  intro row
  rw [plays_exists_field]
  apply exists_congr
  intro column
  simp only [plays, ↓reduceIte, List.nil_append, List.append_assoc, program_fields]

/-- The word verifies the exact increasing incidence list, including the structural guard for
an edgeless graph. Endpoint coordinates are bounded by the supplied exact vertex count. -/
theorem plays_program (q : Query) (endpoint : EndpointQuery) (edges : List (ℕ × ℕ))
    (hendpoint : endpoint.Represents edges) (hedges : q.edges = edges.length)
    (hvertices : ∀ p ∈ edges, p.1 < q.vertices ∧ p.2 < q.vertices) :
    plays (fun xs => Joined.holds endpoint (program (q, xs))) [] (flags q) ↔
      q.vertex < q.vertices ∧ q.ports = (List.range q.edges).filter (fun e =>
        (edges.getD e (0, 0)).1 = q.vertex ∨ (edges.getD e (0, 0)).2 = q.vertex) := by
  rw [plays_fields]
  constructor
  · intro h
    obtain ⟨row, column, hzero⟩ := h 0
    have hg : guard q = true := by
      by_contra hguard
      have hfalse := hzero false
      simp [dispatch, hguard, Joined.holds] at hfalse
    obtain ⟨hv, hs, hb⟩ := (guard_iff q).mp hg
    refine ⟨hv, hs.eq_of_mem_iff (List.pairwise_lt_range.filter _) fun e => ?_⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    by_cases he : e < q.edges
    · obtain ⟨row, column, hp⟩ := h ⟨e, he.trans (Nat.lt_size_self q.edges)⟩
      have hend := hp true
      have hlocal := hp false
      simp only [dispatch, hg, ↓reduceIte, he, Bool.false_eq_true, Joined.holds] at hend hlocal
      obtain ⟨_, hpair⟩ := (hendpoint.2 _ _).mp hend
      rw [hpair]
      have hi : (q.vertex = row.val ∨ q.vertex = column.val) ↔ e ∈ q.ports := by
        simpa only [beq_iff_eq, decide_eq_decide] using hlocal
      simpa only [he, true_and, eq_comm] using hi.symm
    · exact ⟨fun hm => (he (hb e hm)).elim, fun hm => (he hm.1).elim⟩
  · rintro ⟨hv, hports⟩
    have hg : guard q = true := (guard_iff q).mpr ⟨hv, by
      rw [hports]
      exact List.pairwise_lt_range.filter _, fun e he => by
        rw [hports] at he
        exact List.mem_range.mp (List.mem_filter.mp he).1⟩
    intro e
    by_cases he : e.val < q.edges
    · have he' : e.val < edges.length := by omega
      have hpair := hvertices (edges.getD e.val (0, 0)) (by
        rw [List.getD_eq_getElem _ _ he']
        exact List.getElem_mem _)
      let row : Fin (2 ^ q.vertices.size) :=
        ⟨(edges.getD e.val (0, 0)).1, hpair.1.trans (Nat.lt_size_self q.vertices)⟩
      let column : Fin (2 ^ q.vertices.size) :=
        ⟨(edges.getD e.val (0, 0)).2, hpair.2.trans (Nat.lt_size_self q.vertices)⟩
      refine ⟨row, column, fun bit => ?_⟩
      cases bit with
      | false =>
        simp only [dispatch, hg, he, Bool.false_eq_true, ↓reduceIte, Joined.holds]
        rw [beq_iff_eq, decide_eq_decide, hports]
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, he, true_and, row, column]
        exact or_congr eq_comm eq_comm
      | true =>
        simp only [dispatch, hg, he, ↓reduceIte, Joined.holds]
        exact (hendpoint.2 _ _).mpr ⟨he', rfl⟩
    · exact ⟨0, 0, fun bit => by simp [dispatch, hg, he, Joined.holds]⟩

/-- On a rows-first network with increasing stored ports, the accepted candidate is exactly
the selected vertex's port list. An invalid vertex never has an accepted candidate. -/
theorem plays_program_network {T : Type} (D : DescribedNetwork T) {r : ℕ}
    (hD : D.IsRowsFirstBipartite r)
    (hports : ∀ v ∈ D.vertices, v.1.Pairwise (· < ·))
    (endpoint : EndpointQuery) (hendpoint : endpoint.Represents D.edgeEnds)
    (vertex : ℕ) (ports : List ℕ) :
    let q : Query := ⟨D.numEdges, D.vertices.length, vertex, ports⟩
    plays (fun xs => Joined.holds endpoint (program (q, xs))) [] (flags q) ↔
      ∃ hv : vertex < D.vertices.length, ports = D.vertices[vertex].1 := by
  intro q
  rw [plays_program q endpoint D.edgeEnds hendpoint]
  · constructor
    · rintro ⟨hv, hp⟩
      exact ⟨hv, hp.trans (DescribedNetwork.ports_eq_filter_edgeEnds hD ⟨vertex, hv⟩
        (hports _ (List.getElem_mem _))).symm⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨hv, DescribedNetwork.ports_eq_filter_edgeEnds hD ⟨vertex, hv⟩
        (hports _ (List.getElem_mem _))⟩
  · simp [q, DescribedNetwork.edgeEnds]
  · intro p hp
    rw [DescribedNetwork.edgeEnds_eq hD] at hp
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨(D.srcFin hD e).isLt, (D.tgtFin hD e).isLt⟩

open ComputableInPolyTime

private theorem guard_polyTime : ComputableInPolyTime guard encQuery encBool := by
  have hv := encQuery_vertex_deg.computableInPolyTime
  have hV := encQuery_vertices_deg.computableInPolyTime
  have hp := encQuery_ports_deg.computableInPolyTime
  have he := encQuery_edges_deg.computableInPolyTime
  have hs := (ComputableInPolyTime.pairwise encNat (· < ·) binary_lt).comp hp
  have hb := allWithEncoding (binary_lt' (snd encQuery encNat)
    (he.comp (fst encQuery encNat))) id' hp
  exact bool_and' (bool_and' (binary_lt' hv hV) hs) hb

/-- All flags are prepared from the binary graph sizes before any endpoint is guessed. -/
theorem flags_polyTime : ComputableInPolyTime flags encQuery encBits := by
  have he := binary_size.comp encQuery_edges_deg.computableInPolyTime
  have hv := binary_size.comp encQuery_vertices_deg.computableInPolyTime
  exact ((bitsReplicate true).comp he).bitsAppend
    (((bitsReplicate false).comp hv).bitsAppend
      (((bitsReplicate false).comp hv).bitsAppend (const [true])))

/-- The terminal parser is polynomial only in the short query and its choice word; neither a
raw schedule nor the global edge assignment is an argument to this deterministic program. -/
theorem program_polyTime : ComputableInPolyTime program (encPair encQuery encBits)
    Joined.encInstruction := by
  have hq := fst encQuery encBits
  have hx := snd encQuery encBits
  have he := binary_size.comp (encQuery_edges_deg.computableInPolyTime.comp hq)
  have hv := binary_size.comp (encQuery_vertices_deg.computableInPolyTime.comp hq)
  have hrest := bitsDropWithInput hx he
  have htail := bitsDropWithInput hrest hv
  have hedge := bitsToNat.comp (bitsTakeWithInput hx he)
  have hrow := bitsToNat.comp (bitsTakeWithInput hrest hv)
  have hcolumn := bitsToNat.comp (bitsTakeWithInput htail hv)
  have hbit :=
    (ListEncoding.headD (enc₁ := encBool) (enc := encBits) false).computableInPolyTime.comp
      (bitsDropWithInput htail hv)
  have hvertex := encQuery_vertex_deg.computableInPolyTime.comp hq
  have hmem := decide_mem (encQuery_ports_deg.computableInPolyTime.comp hq) hedge
  have hinc := decide_or (decide_eq' hvertex hrow) (decide_eq' hvertex hcolumn)
  have heq := hinc.beq hmem
  have hanswer := hrow.prod hcolumn
  have hquery := (ComputableInPolyTime.sumInr encBool (encPair encNat (encPair encNat encNat))).comp
    (hedge.prod hanswer)
  have hlocal :=
    (ComputableInPolyTime.sumInl encBool (encPair encNat (encPair encNat encNat))).comp heq
  exact ite (guard_polyTime.comp hq)
    (ite_decide (binary_lt' hedge (encQuery_edges_deg.computableInPolyTime.comp hq))
      (ite hbit hquery hlocal) (const (Sum.inl true : Joined.Instruction)))
    (const (Sum.inl false : Joined.Instruction))

end Turing.MultiTapeTM.DescendantPorts
