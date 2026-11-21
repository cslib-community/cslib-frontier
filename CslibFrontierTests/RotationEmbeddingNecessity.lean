/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.EmbeddingNecessity
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexTransport
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Ordinary positioned-embedding clients with actual rational contacts and arbitrary
segment parameters. The horizontal-piece example uses the internally selected axis. -/

public section

namespace CslibFrontierTests.RotationEmbeddingNecessity

open Cslib Polygonal Cslib.Complexity Graph RotationRecognition

private def input : FixedRotationInput := ⟨⟨[0, 1], [(0, 1)]⟩, [none, none]⟩

private theorem input_valid : Valid input := (validate_eq_true_iff input).mp (by decide)

private theorem input_order : referenceOrder input = [0, 1, 2, 3] := by decide +kernel

private def P (n : ℕ) : ℂ := parabolaPoint n
private def W (flat : Bool) : ℂ := if flat then ⟨4, 1⟩ else ⟨4, 0⟩

private def route (flat : Bool) (e : Fin (subdivisionGraph input).edges.length) : Route :=
  if e.val = 0 then Route.line (P 0) (P 2)
    else if e.val = 1 then Route.line (P 2) (P 3)
    else (Route.line (P 3) (W flat)).append (P 1)

private def drawing (flat : Bool) : PolygonalDrawing (subdivisionGraph input) where
  vertex := P
  route := route flat
  endpoint_eq := by
    intro e b
    fin_cases e <;> cases b <;> rfl

private theorem last_simple (flat : Bool) :
    ((Route.line (P 3) (W flat)).append (P 1)).IsSimple := by
  apply (Route.isSimple_line (by cases flat <;> norm_num [P, W, parabolaPoint])).append
  · cases flat <;> norm_num [W, P, parabolaPoint]
  · intro i s t hs ht heq
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change AffineMap.lineMap (P 3) (W flat) s =
      AffineMap.lineMap (W flat) (P 1) t at heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    have hs1 : s = 1 := by
      cases flat <;> norm_num [P, W, parabolaPoint, AffineMap.lineMap_apply_module'] at hre him <;>
        linarith
    have ht0 : t = 0 := by
      cases flat <;> norm_num [P, W, parabolaPoint, AffineMap.lineMap_apply_module'] at hre him <;>
        linarith
    left
    exact ⟨by simp [Route.AtEnd, Route.position, hs1, Route.segments, Route.line], ht0⟩

private theorem drawing_simple (flat : Bool) (e : Fin (subdivisionGraph input).edges.length) :
    ((drawing flat).route e).IsSimple := by
  fin_cases e
  · change (Route.line (P 0) (P 2)).IsSimple
    exact Route.isSimple_line (by norm_num [P, parabolaPoint])
  · change (Route.line (P 2) (P 3)).IsSimple
    exact Route.isSimple_line (by norm_num [P, parabolaPoint])
  · exact last_simple flat

private theorem drawing_vertex_contacts (flat : Bool)
    (e : Fin (subdivisionGraph input).edges.length)
    (i : Fin ((drawing flat).route e).segments) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (v : ℕ) (hv : v ∈ (subdivisionGraph input).vertices)
    (heq : ((drawing flat).route e).eval i t = (drawing flat).vertex v) :
    ∃ b, ((drawing flat).route e).AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  rcases ht with ⟨ht0, ht1⟩
  have hvlt : v < 4 := by simpa [subdivisionGraph, subdivisionSize, input] using hv
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases flat <;> fin_cases e
  all_goals dsimp only [drawing, route] at i hre him ⊢
  all_goals dsimp [Route.segments, Route.line, Route.append] at i hre him ⊢
  all_goals fin_cases i <;> interval_cases v
  all_goals dsimp [Route.eval, Route.append, Route.line, Fin.lastCases,
    Fin.reverseInduction, Fin.reverseInduction.go] at hre him ⊢
  all_goals
    norm_num [drawing, route, P, W, parabolaPoint, Route.eval, Route.append, Route.line,
      AffineMap.lineMap_apply_module', Route.AtEnd, Route.position, Route.segments,
      Dart.vertex, Graph.edgeEndpoint, subdivisionGraph, subdivide, input, Bool.exists_bool]
      at *
  all_goals linarith

private theorem drawing_edge_contacts (flat : Bool)
    (e f : Fin (subdivisionGraph input).edges.length) (hef : e ≠ f)
    (i : Fin ((drawing flat).route e).segments) (j : Fin ((drawing flat).route f).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((drawing flat).route e).eval i s = ((drawing flat).route f).eval j t) :
    ∃ a b, ((drawing flat).route e).AtEnd i s a ∧
      ((drawing flat).route f).AtEnd j t b ∧ Dart.vertex (e, a) = Dart.vertex (f, b) := by
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases flat <;> fin_cases e <;> fin_cases f <;> try contradiction
  all_goals
    dsimp only [drawing, route] at i j hre him ⊢
    dsimp [Route.segments, Route.line, Route.append] at i j hre him ⊢
    fin_cases i <;> fin_cases j
    all_goals dsimp [Route.eval, Route.append, Route.line, Fin.lastCases,
      Fin.reverseInduction, Fin.reverseInduction.go] at hre him ⊢
    all_goals norm_num [drawing, route, P, W, parabolaPoint, Route.eval, Route.append, Route.line,
        AffineMap.lineMap_apply_module', Route.AtEnd, Route.position, Route.segments,
        Dart.vertex, Graph.edgeEndpoint, subdivisionGraph, subdivide, input, Bool.exists_bool]
        at hre him ⊢
  all_goals first
    | constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    | linarith [hs.1, hs.2, ht.1, ht.2]

private theorem drawing_embedding (flat : Bool) : (drawing flat).IsEmbedding where
  vertices_injective := by
    intro a _ b _ h
    have hre := congrArg Complex.re h
    change (a : ℝ) = (b : ℝ) at hre
    exact_mod_cast hre
  simple := drawing_simple flat
  vertex_contacts := drawing_vertex_contacts flat
  edge_contacts := drawing_edge_contacts flat

private theorem drawing_vertices (flat : Bool) (v : ℕ)
    (hv : v ∈ (subdivisionGraph input).vertices) :
    (drawing flat).vertex v = (referenceDrawing input).vertex v := by
  have hvlt : v < 4 := by simpa [subdivisionGraph, subdivisionSize, input] using hv
  simp only [referenceDrawing, referencePoint, input_order]
  interval_cases v <;> norm_num [drawing, P, List.idxOf_cons]

private theorem drawing_frozen (flat : Bool)
    (e : Fin (subdivisionGraph input).edges.length)
    (he : ((subdivide input)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true) :
    (drawing flat).route e = (referenceDrawing input).route e := by
  fin_cases e <;> norm_num [subdivide, input] at he

-- The original first/last reference pair has a nonzero row; the concrete drawing is planar.
example : query input = true :=
  query_eq_true_of_positioned_frozen_embedding input_valid (drawing false)
    (drawing_embedding false) (drawing_vertices false) (drawing_frozen false)

-- This variant has a horizontal last world-coordinate piece. The axis is chosen internally.
example : query input = true :=
  query_eq_true_of_positioned_frozen_embedding input_valid (drawing true)
    (drawing_embedding true) (drawing_vertices true) (drawing_frozen true)

-- The same nonzero-row fixture works from an embedding away from the reference position.
example : ∃ D : PolygonalDrawing (subdivisionGraph input), D.IsEmbedding ∧
    D.vertex 0 ≠ (referenceDrawing input).vertex 0 ∧ query input = true := by
  have hq : ∀ w ∈ (subdivisionGraph input).vertices, w ≠ 0 →
      (-1 : ℂ) ≠ (drawing false).vertex w := by
    intro w _ _ he
    have hre : (-1 : ℝ) = (w : ℝ) := congrArg Complex.re he
    have hw : 0 ≤ (w : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨D, hD, hV, _, _, _, _⟩ :=
    (drawing_embedding false).exists_single_vertex_transport (by decide) 0 (by decide) _ hq
  have hzero : D.vertex 0 = (-1 : ℂ) := by
    simpa only [ite_true] using hV 0 (by decide)
  refine ⟨D, hD, ?_, query_eq_true_of_unfrozen_embedding input_valid (by decide) D hD⟩
  rw [hzero, ← drawing_vertices false 0 (by decide)]
  intro he
  have hre := congrArg Complex.re he
  norm_num [drawing, P, parabolaPoint] at hre

example : ¬MoveEquations (frame input) (fun _ _ => false) := by
  intro h
  have hrow := h ((((3, 1), false) : Segment), 2) (by decide)
    ((((0, 2), false) : Segment), 0) (by decide) (by decide) (by decide)
  change (false : Bool) = true at hrow
  cases hrow



-- Actual original crossing, before replacing the final route by the two-piece arc.
example : (⟨3 / 2, 3⟩ : ℂ) ∈
      openSegment ℝ (((referenceDrawing input).route ⟨0, by decide⟩).start)
        (((referenceDrawing input).route ⟨0, by decide⟩).finish) ∩
      openSegment ℝ (((referenceDrawing input).route ⟨2, by decide⟩).start)
        (((referenceDrawing input).route ⟨2, by decide⟩).finish) := by
  change (⟨3 / 2, 3⟩ : ℂ) ∈
    openSegment ℝ ((referenceDrawing input).vertex 0) ((referenceDrawing input).vertex 2) ∩
      openSegment ℝ ((referenceDrawing input).vertex 3) ((referenceDrawing input).vertex 1)
  rw [← drawing_vertices false 0 (by decide), ← drawing_vertices false 2 (by decide),
    ← drawing_vertices false 3 (by decide), ← drawing_vertices false 1 (by decide)]
  constructor <;> rw [openSegment_eq_image_lineMap]
  all_goals
    refine ⟨3 / 4, by norm_num, ?_⟩
    apply Complex.ext <;>
      norm_num [drawing, P, referenceDrawing, referencePoint, input_order, input, List.idxOf_cons,
        Dart.vertex, Graph.edgeEndpoint, subdivisionGraph, subdivide, parabolaPoint,
        AffineMap.lineMap_apply_module', Complex.real_smul]

-- Reference drawings that need no detours: a fixed loop with an isolate; a path with
-- just one fixed end; a reversed listed occurrence; and two parallel loop records.
-- Their actual reference-positioned embeddings, rather than an unrelated digon, are proved here.
private def smallInput (k : Fin 4) : FixedRotationInput :=
  if k = 0 then ⟨⟨[0, 1], [(0, 0)]⟩, [some [0, 1], some []]⟩
  else if k = 1 then ⟨⟨[0, 1], [(0, 1)]⟩, [some [0], none]⟩
  else if k = 2 then ⟨⟨[0, 1], [(1, 0)]⟩, [none, some [0]]⟩
  else ⟨⟨[0, 1], [(0, 0), (0, 0)]⟩, [some [0, 1, 2, 3], some []]⟩

private theorem small_valid (k : Fin 4) : Valid (smallInput k) := by
  fin_cases k <;> exact (validate_eq_true_iff _).mp (by decide)

private theorem small_embedding_012 (k : Fin 3) :
    (referenceDrawing (smallInput k.castSucc)).IsEmbedding where
  vertices_injective := referenceDrawing_vertices_injective (small_valid k.castSucc)
  simple := referenceDrawing_simple (small_valid k.castSucc)
  vertex_contacts := referenceDrawing_vertex_contacts (small_valid k.castSucc)
  edge_contacts := by
    intro e f hef i j s t hs ht heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    fin_cases k <;> fin_cases e <;> fin_cases f <;> try contradiction
    all_goals change Fin 1 at i j
    all_goals fin_cases i; fin_cases j
    all_goals dsimp [referenceDrawing, referencePoint, referenceOrder, centerBlocks,
      smallInput, Route.line, Route.eval, Dart.vertex, Graph.edgeEndpoint,
      subdivisionGraph, subdivide] at hre him ⊢
    all_goals norm_num [referenceDrawing, referencePoint, referenceOrder, centerBlocks,
          smallInput, List.range_succ, List.range_zero, List.any_cons, List.any_nil,
          Route.line, Route.eval, parabolaPoint,
          AffineMap.lineMap_apply_module', Complex.real_smul, Route.AtEnd, Route.position,
          Route.segments, Dart.vertex, Graph.edgeEndpoint, subdivisionGraph, subdivide,
          Bool.exists_bool] at hre him ⊢
    all_goals first
      | constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      | linarith [hs.1, hs.2, ht.1, ht.2]


private theorem small_contacts_3_lt
    (e f : Fin (subdivisionGraph (smallInput 3)).edges.length) (hlt : e.val < f.val)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (_ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing (smallInput 3)).route e).eval 0 s =
      ((referenceDrawing (smallInput 3)).route f).eval 0 t) :
    ∃ a b, ((referenceDrawing (smallInput 3)).route e).AtEnd 0 s a ∧
      ((referenceDrawing (smallInput 3)).route f).AtEnd 0 t b ∧
      Dart.vertex (e, a) = Dart.vertex (f, b) := by
  have hroute (g : Fin (subdivisionGraph (smallInput 3)).edges.length) :
      (referenceDrawing (smallInput 3)).route g =
        if g.val = 0 then Route.line (P 0) (P 4)
        else if g.val = 1 then Route.line (P 4) (P 3)
        else if g.val = 2 then Route.line (P 3) (P 0)
        else if g.val = 3 then Route.line (P 0) (P 2)
        else if g.val = 4 then Route.line (P 2) (P 1)
        else Route.line (P 1) (P 0) := by
    fin_cases g <;> rfl
  rw [hroute e, hroute f] at heq ⊢
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases e <;> fin_cases f <;> norm_num at hlt
  all_goals dsimp [Route.line, Route.eval, Dart.vertex, Graph.edgeEndpoint,
    subdivisionGraph, subdivide, smallInput] at hre him ⊢
  all_goals norm_num [P, parabolaPoint, AffineMap.lineMap_apply_module', Complex.real_smul,
    Route.AtEnd, Route.position, Route.segments, Route.line, Bool.exists_bool] at hre him ⊢
  all_goals first
    | constructor <;> linarith [hs.1, hs.2]
    | linarith [hs.1, hs.2]

private theorem small_embedding_3 :
    (referenceDrawing (smallInput 3)).IsEmbedding where
  vertices_injective := referenceDrawing_vertices_injective (small_valid 3)
  simple := referenceDrawing_simple (small_valid 3)
  vertex_contacts := referenceDrawing_vertex_contacts (small_valid 3)
  edge_contacts := by
    intro e f hef i j s t hs ht heq
    have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst i j
    by_cases hlt : e.val < f.val
    · exact small_contacts_3_lt e f hlt s t hs ht heq
    · have hgt : f.val < e.val := by
        have hne : e.val ≠ f.val := fun h => hef (Fin.ext h)
        omega
      obtain ⟨a, b, ha, hb, hab⟩ := small_contacts_3_lt f e hgt t s ht hs heq.symm
      exact ⟨b, a, hb, ha, hab.symm⟩


private theorem small_embedding (k : Fin 4) :
    (referenceDrawing (smallInput k)).IsEmbedding := by
  fin_cases k
  · exact small_embedding_012 0
  · exact small_embedding_012 1
  · exact small_embedding_012 2
  · exact small_embedding_3

example (k : Fin 4) : query (smallInput k) = true :=
  query_eq_true_of_positioned_frozen_embedding (small_valid k) _ (small_embedding k)
    (fun _ _ => rfl) (fun _ _ => rfl)

-- Both frozen ends of the original loop and its declared isolated point survive.
example : ((subdivide (smallInput 0))[0]).frozen = true ∧
    ((subdivide (smallInput 0))[2]).frozen = true ∧
    1 ∈ (subdivisionGraph (smallInput 0)).vertices ∧
    (∀ e ∈ (subdivisionGraph (smallInput 0)).edges, e.1 ≠ 1 ∧ e.2 ≠ 1) := by
  decide

-- Empty edge data still have two positioned isolates; no fictitious route is needed.
private def emptyInput : FixedRotationInput := ⟨⟨[0, 1], []⟩, [some [], none]⟩

private theorem empty_valid : Valid emptyInput := (validate_eq_true_iff _).mp (by decide)

private theorem empty_embedding : (referenceDrawing emptyInput).IsEmbedding where
  vertices_injective := referenceDrawing_vertices_injective empty_valid
  simple := referenceDrawing_simple empty_valid
  vertex_contacts := referenceDrawing_vertex_contacts empty_valid
  edge_contacts := by intro e; exact Fin.elim0 e

example : query emptyInput = true :=
  query_eq_true_of_unfrozen_embedding empty_valid (by decide) _ empty_embedding

-- The original star is supplied before any edges are subdivided or vertices positioned.
private def freeStar : FixedRotationInput :=
  ⟨Graph.RotationSystem.starGraph 3, [none, none, none, none]⟩

example : query freeStar = true := by
  have hI : Valid freeStar := (validate_eq_true_iff freeStar).mp (by decide)
  exact query_eq_true_of_unfrozen_original_embedding hI (by decide) _
    (PolygonalDrawing.star_isEmbedding 3)

-- The shared append-support property includes degenerate and already closed routes.
example : ((Route.line (0 : ℂ) 0).append 0).support = {0} := by
  rw [Route.support_append, Route.support_line, Route.finish_line]
  simp only [segment_same, Set.union_self]

-- Mixed drawings may share a whole piece. Individual simplicity does not provide the
-- reciprocal closed-node exclusions of the straight observation law.
example : (Route.line (P 0) (P 2)).IsSimple ∧
    (P 0) ∈ (Route.line (P 0) (P 2)).support := by
  refine ⟨Route.isSimple_line (by norm_num [P, parabolaPoint]), ?_⟩
  rw [Route.support_line]
  exact left_mem_segment ℝ _ _

-- Three edge supports may meet at their declared star center in a genuine embedding.
-- Hence no-three-away-from-vertices cannot be strengthened to no-three everywhere.
theorem declared_star_has_three_supports :
    (PolygonalDrawing.star 3).IsEmbedding ∧
    (∀ e : Fin (Graph.RotationSystem.starGraph 3).edges.length,
      (0 : ℂ) ∈ ((PolygonalDrawing.star 3).route e).support) := by
  refine ⟨PolygonalDrawing.star_isEmbedding 3, ?_⟩
  intro e
  change (0 : ℂ) ∈ (Route.line _ 0).support
  rw [Route.support_line]
  exact right_mem_segment ℝ _ _

end CslibFrontierTests.RotationEmbeddingNecessity
