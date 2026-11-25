/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEdges
import CslibFrontier.Foundations.Geometry.Polygonal.Concatenate
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
import Mathlib.Tactic.FinCases

/-!
# Contracting an embedded recognition subdivision

Concatenating each three-piece chain gives an embedding of the original listed graph.
The route supports are exactly the unions of their indexed pieces, and the outgoing
germs at the original vertices agree. The only possible closure within a chain is its
original loop. This is original geometry.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal

private abbrev Edge (G : Graph) := Fin G.edges.length

private abbrev pieceEdge (I : FixedRotationInput) (i : Edge I.graph) (k : Fin 3) :
    Edge (subdivisionGraph I) := (⟨i, k⟩ : SubdivisionEdgeIndex I).edge

private theorem piece_vertex {I : FixedRotationInput} (i : Edge I.graph) (k : Fin 3) (b : Bool) :
    Dart.vertex (pieceEdge I i k, b) = if b then
      (⟨i, k⟩ : SubdivisionEdgeIndex I).endpoints.2
    else (⟨i, k⟩ : SubdivisionEdgeIndex I).endpoints.1 := by
  have h := (Dart.edge_eq_vertices (pieceEdge I i k)).symm.trans
    (subdivision_edge_endpoints I (pieceEdge I i k))
  simp only [subdivisionEdgeIndex_edge] at h
  cases b
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

private theorem piece_vertex_cases {I : FixedRotationInput} (i : Edge I.graph) (k : Fin 3)
    (b : Bool) :
    (k = 0 ∧ b = false ∧ Dart.vertex (pieceEdge I i k, b) = Dart.vertex (i, false)) ∨
    (k = 2 ∧ b = true ∧ Dart.vertex (pieceEdge I i k, b) = Dart.vertex (i, true)) ∨
    ∃ c : Bool, Dart.vertex (pieceEdge I i k, b) =
      I.graph.vertices.length + 2 * i.val + c.toNat := by
  have hv := Dart.edge_eq_vertices i
  fin_cases k <;> cases b <;> simp [piece_vertex, SubdivisionEdgeIndex.endpoints, hv]

private theorem piece_ne {I : FixedRotationInput} {i j : Edge I.graph} {k l : Fin 3}
    (h : i ≠ j ∨ k ≠ l) : pieceEdge I i k ≠ pieceEdge I j l := by
  intro he
  have hidx := congrArg (subdivisionEdgeIndex I) he
  simp only [subdivisionEdgeIndex_edge] at hidx
  exact h.elim (fun hn => hn (congrArg SubdivisionEdgeIndex.original hidx))
    (fun hn => hn (congrArg SubdivisionEdgeIndex.piece hidx))

private theorem piece_endpoints {I : FixedRotationInput}
    (F : PolygonalDrawing (subdivisionGraph I)) (i : Edge I.graph) :
    (F.route (pieceEdge I i 0)).start = F.vertex (Dart.vertex (i, false)) ∧
    (F.route (pieceEdge I i 0)).finish = (F.route (pieceEdge I i 1)).start ∧
    ((F.route (pieceEdge I i 0)).concat (F.route (pieceEdge I i 1))).finish =
      (F.route (pieceEdge I i 2)).start ∧
    (F.route (pieceEdge I i 2)).finish = F.vertex (Dart.vertex (i, true)) := by
  have hpq :
      (F.route (pieceEdge I i 0)).endpoint true = (F.route (pieceEdge I i 1)).endpoint false := by
    simp [F.endpoint_eq, piece_vertex, SubdivisionEdgeIndex.endpoints]
  change (F.route (pieceEdge I i 0)).endpoint false = _ ∧
    (F.route (pieceEdge I i 0)).endpoint true = (F.route (pieceEdge I i 1)).endpoint false ∧
    ((F.route (pieceEdge I i 0)).concat (F.route (pieceEdge I i 1))).endpoint true =
      (F.route (pieceEdge I i 2)).endpoint false ∧
    (F.route (pieceEdge I i 2)).endpoint true = _
  rw [Route.endpoint_concat _ _ hpq true]
  simp [F.endpoint_eq, piece_vertex, SubdivisionEdgeIndex.endpoints, Dart.edge_eq_vertices i]

private theorem piece_open {I : FixedRotationInput} (hI : Valid I)
    {F : PolygonalDrawing (subdivisionGraph I)} (hF : F.IsEmbedding)
    (i : Edge I.graph) (k : Fin 3) :
    (F.route (pieceEdge I i k)).start ≠ (F.route (pieceEdge I i k)).finish := by
  change (F.route (pieceEdge I i k)).endpoint false ≠ (F.route (pieceEdge I i k)).endpoint true
  rw [F.endpoint_eq, F.endpoint_eq]
  obtain ⟨hm, hn⟩ := subdivision_endpoint_spec hI (pieceEdge I i k)
  exact hF.vertex_ne (((referenceOrder_enumerates hI).2 _).mp (hm false))
    (((referenceOrder_enumerates hI).2 _).mp (hm true)) hn

private theorem same_occurrence_end_contact {I : FixedRotationInput} (hI : Valid I)
    (i : Edge I.graph) (k l : Fin 3) (hkl : k < l) (b c : Bool)
    (h : Dart.vertex (pieceEdge I i k, b) = Dart.vertex (pieceEdge I i l, c)) :
    (k = 0 ∧ l = 1 ∧ b = true ∧ c = false) ∨
    (k = 1 ∧ l = 2 ∧ b = true ∧ c = false) ∨
    (k = 0 ∧ l = 2 ∧ b = false ∧ c = true) := by
  obtain ⟨hl, hr⟩ := hI.edge_endpoints_lt (List.getElem_mem i.isLt)
  fin_cases k <;> fin_cases l <;> cases b <;> cases c <;>
    simp [piece_vertex, SubdivisionEdgeIndex.endpoints, Fin.lt_def] at hkl h ⊢ <;> omega

private theorem route_pair_contact {I : FixedRotationInput}
    {F : PolygonalDrawing (subdivisionGraph I)} (hF : F.IsEmbedding)
    (i : Edge I.graph) (k l : Fin 3) (hkl : k ≠ l)
    (a : Fin (F.route (pieceEdge I i k)).segments)
    (b : Fin (F.route (pieceEdge I i l)).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (h : (F.route (pieceEdge I i k)).eval a s = (F.route (pieceEdge I i l)).eval b t) :
    ∃ c d, (F.route (pieceEdge I i k)).AtEnd a s c ∧ (F.route (pieceEdge I i l)).AtEnd b t d ∧
      Dart.vertex (pieceEdge I i k, c) = Dart.vertex (pieceEdge I i l, d) :=
  hF.edge_contacts _ _ (piece_ne (Or.inr hkl)) a b s t hs ht h

private def joinedRoute {I : FixedRotationInput} (F : PolygonalDrawing (subdivisionGraph I))
    (i : Edge I.graph) : Route :=
  ((F.route (pieceEdge I i 0)).concat (F.route (pieceEdge I i 1))).concat
    (F.route (pieceEdge I i 2))

private theorem end_position_of_shift {a j m n : ℕ} {s : ℝ}
    (hindex : a = m + j) (hend : (j : ℝ) + s = n) :
    (a : ℝ) + s = ((m + n : ℕ) : ℝ) := by
  simp only [hindex, Nat.cast_add, add_assoc, hend]

private theorem joined_simple {I : FixedRotationInput} (hI : Valid I)
    {F : PolygonalDrawing (subdivisionGraph I)} (hF : F.IsEmbedding)
    (i : Edge I.graph) : (joinedRoute F i).IsSimple := by
  let p := F.route (pieceEdge I i 0)
  let q := F.route (pieceEdge I i 1)
  let r := F.route (pieceEdge I i 2)
  obtain ⟨hs, hpq, hjoin, ht⟩ := piece_endpoints F i
  have hprefix : (p.concat q).IsSimple := by
    apply (hF.simple (pieceEdge I i 0)).concat (hF.simple (pieceEdge I i 1))
      (piece_open hI hF i 0) (piece_open hI hF i 1) hpq
    intro a b s t hs' ht' he
    obtain ⟨c, d, hc, hd, hcd⟩ := route_pair_contact hF i 0 1 (by decide) a b hs' ht' he
    have hh : c = true ∧ d = false := by
      simpa using same_occurrence_end_contact hI i 0 1 (by decide) c d hcd
    exact Or.inl ⟨hh.1 ▸ hc, hh.2 ▸ hd⟩
  have hstart : (p.concat q).start = p.start := Route.endpoint_concat p q hpq false
  have hend : (p.concat q).finish = q.finish := Route.endpoint_concat p q hpq true
  have hopen : (p.concat q).start ≠ (p.concat q).finish := by
    rw [hstart, hend, hs]
    change F.vertex (Dart.vertex (i, false)) ≠ (F.route (pieceEdge I i 1)).endpoint true
    rw [F.endpoint_eq]
    have hm (k : Fin 3) (b : Bool) : Dart.vertex (pieceEdge I i k, b) ∈
        (subdivisionGraph I).vertices :=
      ((referenceOrder_enumerates hI).2 _).mp ((subdivision_endpoint_spec hI _).1 b)
    have hsrc : Dart.vertex (pieceEdge I i 0, false) = Dart.vertex (i, false) := by
      simp [piece_vertex, SubdivisionEdgeIndex.endpoints, Dart.edge_eq_vertices i]
    rw [← hsrc]
    apply hF.vertex_ne (hm 0 false) (hm 1 true)
    intro he
    simpa using same_occurrence_end_contact hI i 0 1 (by decide) false true he
  change ((p.concat q).concat r).IsSimple
  apply hprefix.concat (hF.simple (pieceEdge I i 2)) hopen (piece_open hI hF i 2)
    hjoin
  intro a b s t hs' ht' he
  rcases Route.concat_eval_cases p q hpq a with ⟨j, hj, hval⟩ | ⟨j, hj, hval⟩ <;>
    specialize hval s
  · obtain ⟨c, d, hc, hd, hcd⟩ :=
      route_pair_contact hF i 0 2 (by decide) j b hs' ht' (hval.symm.trans he)
    have hh : c = false ∧ d = true := by
      simpa using same_occurrence_end_contact hI i 0 2 (by decide) c d hcd
    refine .inr ⟨?_, hh.2 ▸ hd⟩
    have ha : p.AtEnd j s false := hh.1 ▸ hc
    change (a.val : ℝ) + s = 0
    rw [hj]
    exact ha
  · obtain ⟨c, d, hc, hd, hcd⟩ :=
      route_pair_contact hF i 1 2 (by decide) j b hs' ht' (hval.symm.trans he)
    have hh : c = true ∧ d = false := by
      simpa using same_occurrence_end_contact hI i 1 2 (by decide) c d hcd
    refine .inl ⟨?_, hh.2 ▸ hd⟩
    have ha : q.AtEnd j s true := hh.1 ▸ hc
    change (a.val : ℝ) + s = ((p.concat q).segments : ℝ)
    exact (end_position_of_shift hj ha).trans
      (congrArg (fun n : ℕ => (n : ℝ)) (Route.segments_concat p q).symm)

private def shift {I : FixedRotationInput} (F : PolygonalDrawing (subdivisionGraph I))
    (i : Edge I.graph) (k : Fin 3) : ℕ :=
  (![0, (F.route (pieceEdge I i 0)).segments,
    (F.route (pieceEdge I i 0)).segments + (F.route (pieceEdge I i 1)).segments] : Fin 3 → ℕ) k

private theorem joined_trace {I : FixedRotationInput}
    (F : PolygonalDrawing (subdivisionGraph I)) (i : Edge I.graph)
    (a : Fin (joinedRoute F i).segments) (s : ℝ) :
    ∃ (k : Fin 3) (j : Fin (F.route (pieceEdge I i k)).segments), a.val = shift F i k + j.val ∧
      (joinedRoute F i).eval a s = (F.route (pieceEdge I i k)).eval j s := by
  let p := F.route (pieceEdge I i 0)
  let q := F.route (pieceEdge I i 1)
  let r := F.route (pieceEdge I i 2)
  obtain ⟨_, hpq, hj, _⟩ := piece_endpoints F i
  rcases Route.concat_eval_cases (p.concat q) r hj a with ⟨b, hb, hv⟩ | ⟨b, hb, hv⟩ <;>
    specialize hv s
  · rcases Route.concat_eval_cases p q hpq b with ⟨j, hidx, hval⟩ | ⟨j, hidx, hval⟩ <;>
      specialize hval s
    · exact ⟨0, j, by simpa [shift] using hb.trans hidx, hv.trans hval⟩
    · exact ⟨1, j, by simpa [shift, p] using hb.trans hidx, hv.trans hval⟩
  · exact ⟨2, b, by simpa [shift, Route.segments_concat, p, q] using hb, hv⟩

private theorem joined_segments {I : FixedRotationInput}
    (F : PolygonalDrawing (subdivisionGraph I)) (i : Edge I.graph) :
    (joinedRoute F i).segments = shift F i 2 + (F.route (pieceEdge I i 2)).segments := by
  simp [joinedRoute, shift, Route.segments_concat]

private theorem joined_support {I : FixedRotationInput}
    (F : PolygonalDrawing (subdivisionGraph I)) (i : Edge I.graph) :
    (joinedRoute F i).support = ⋃ k : Fin 3, (F.route (pieceEdge I i k)).support := by
  let p := F.route (pieceEdge I i 0)
  let q := F.route (pieceEdge I i 1)
  let r := F.route (pieceEdge I i 2)
  obtain ⟨_, hpq, hj, _⟩ := piece_endpoints F i
  change ((p.concat q).concat r).support = _
  rw [Route.support_concat _ _ hj, Route.support_concat _ _ hpq]
  ext x
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ((h | h) | h) <;> exact ⟨_, h⟩
  · rintro ⟨k, hk⟩
    fin_cases k
    exacts [.inl (.inl hk), .inl (.inr hk), .inr hk]

/-- Undo the indexed twice subdivision of an actual embedding. Original vertex points and
outgoing germs are retained, and each original route has exactly its three-piece support.
Loops and parallel occurrences use their own indexed pieces. -/
theorem exists_contracted_subdivision_embedding {I : FixedRotationInput} (hI : Valid I)
    {F : PolygonalDrawing (subdivisionGraph I)} (hF : F.IsEmbedding) :
    ∃ D : PolygonalDrawing I.graph, D.IsEmbedding ∧ D.vertex = F.vertex ∧
      (∀ i, (D.route i).support = ⋃ k : Fin 3,
        (F.route (⟨i, k⟩ : SubdivisionEdgeIndex I).edge).support) ∧
      ∀ d : Dart I.graph, D.germ d = F.germ (subdivisionDart I d) := by
  let D : PolygonalDrawing I.graph := {
    vertex := F.vertex
    route := joinedRoute F
    endpoint_eq := by
      intro i b
      obtain ⟨hs, hpq, hjoin, ht⟩ := piece_endpoints F i
      change (((F.route (pieceEdge I i 0)).concat (F.route (pieceEdge I i 1))).concat
        (F.route (pieceEdge I i 2))).endpoint b = _
      rw [Route.endpoint_concat _ _ hjoin]
      cases b
      · exact (Route.endpoint_concat _ _ hpq false).trans hs
      · exact ht
  }
  have hnames : I.graph.vertices = List.range I.graph.vertices.length := hI.1
  have hbound (v : ℕ) (hv : v ∈ I.graph.vertices) : v < I.graph.vertices.length :=
    List.mem_range.mp (hnames ▸ hv)
  have hsub (v : ℕ) (hv : v ∈ I.graph.vertices) : v ∈ (subdivisionGraph I).vertices := by
    have hlt := hbound v hv
    simp only [subdivisionGraph, subdivisionSize, List.mem_range]
    omega
  have hevertex (d : Dart I.graph) : d.vertex ∈ I.graph.vertices :=
    RotationSystem.vertex_mem (fun v hv => hnames ▸ List.mem_range.mpr (hI.2.1 v hv)) d
  have hvertex : ∀ i (a : Fin (D.route i).segments) (s : ℝ), s ∈ Set.Icc 0 1 →
      ∀ v ∈ I.graph.vertices, (D.route i).eval a s = D.vertex v →
      ∃ b, (D.route i).AtEnd a s b ∧ Dart.vertex (i, b) = v := by
    intro i a s hs v hv he
    obtain ⟨k, j, hj, hval⟩ := joined_trace F i a s
    obtain ⟨b, hb, hname⟩ := hF.vertex_contacts _ j s hs v (hsub v hv) (hval.symm.trans he)
    rcases piece_vertex_cases i k b with ⟨rfl, rfl, hend⟩ | ⟨rfl, rfl, hend⟩ | ⟨c, hnew⟩
    · refine ⟨false, ?_, hend.symm.trans hname⟩
      change (a.val : ℝ) + s = 0
      rw [show a.val = j.val by simpa [shift] using hj]
      exact hb
    · refine ⟨true, ?_, hend.symm.trans hname⟩
      change (a.val : ℝ) + s = (joinedRoute F i).segments
      exact (end_position_of_shift hj hb).trans
        (congrArg (fun n : ℕ => (n : ℝ)) (joined_segments F i).symm)
    · have hlt := hbound v hv
      omega
  have hshared {i j : Edge I.graph} (hne : i ≠ j) (k l : Fin 3) (b c : Bool)
      (he : Dart.vertex (pieceEdge I i k, b) = Dart.vertex (pieceEdge I j l, c)) :
      Dart.vertex (pieceEdge I i k, b) ∈ I.graph.vertices := by
    rcases piece_vertex_cases i k b with ⟨_, _, hb⟩ | ⟨_, _, hb⟩ | ⟨d, hb⟩
    · exact hb.symm ▸ hevertex (i, false)
    · exact hb.symm ▸ hevertex (i, true)
    · rcases piece_vertex_cases j l c with ⟨_, _, hc⟩ | ⟨_, _, hc⟩ | ⟨a, hc⟩
      · exact (he.trans hc).symm ▸ hevertex (j, false)
      · exact (he.trans hc).symm ▸ hevertex (j, true)
      · rw [hb, hc] at he
        exact (hne (Fin.ext (by cases d <;> cases a <;> simp at he <;> omega))).elim
  refine ⟨D, ⟨?_, joined_simple hI hF, hvertex, ?_⟩, rfl, joined_support F, ?_⟩
  · exact fun u hu v hv he => hF.vertices_injective (hsub u hu) (hsub v hv) he
  · intro i j hne a b s t hs ht he
    obtain ⟨k, a', _, ha⟩ := joined_trace F i a s
    obtain ⟨l, b', _, hb⟩ := joined_trace F j b t
    obtain ⟨c, d, hc, _, hcd⟩ := hF.edge_contacts _ _ (piece_ne (Or.inl hne))
      a' b' s t hs ht (ha.symm.trans (he.trans hb))
    let v := Dart.vertex (pieceEdge I i k, c)
    have hv := hshared hne k l c d hcd
    have hx : (D.route i).eval a s = D.vertex v :=
      ha.trans (((F.route (pieceEdge I i k)).at_eq_endpoint a' hs c hc).trans (F.endpoint_eq _ c))
    obtain ⟨u, hu, huv⟩ := hvertex i a s hs v hv hx
    obtain ⟨w, hw, hwv⟩ := hvertex j b t ht v hv (he.symm.trans hx)
    exact ⟨u, w, hu, hw, huv.trans hwv.symm⟩
  · rintro ⟨i, b⟩
    obtain ⟨_, hpq, hjoin, _⟩ := piece_endpoints F i
    cases b
    · exact (Route.germ_concat _ _ hjoin false).trans (Route.germ_concat _ _ hpq false)
    · exact Route.germ_concat _ _ hjoin true

end Cslib.Complexity.Graph.RotationRecognition
