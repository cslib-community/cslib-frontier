/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEdges
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import CslibFrontier.Foundations.Geometry.Polygonal.Trisection
import Mathlib.Tactic.FinCases

/-!
# Subdividing an embedded listed graph

Each original edge is cut near its two ends. Its three pieces give the actual routes
of the indexed recognition subdivision, including for loops and parallel edges.
Membership in a piece transfers to an original route parameter, which distinguishes
shared cut points from other contacts. This is original finite geometry.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal

private abbrev Edge (G : Graph) := Fin G.edges.length

private noncomputable abbrev cut : ℝ := 1 / 3

private theorem cut_pos : 0 < cut := by norm_num [cut]

private theorem cut_small : cut + cut < 1 := by norm_num [cut]

private theorem cut_mem : cut ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨cut_pos, by linarith [cut_small, cut_pos]⟩

private def fresh (I : FixedRotationInput) (i : Edge I.graph) (b : Bool) : ℕ :=
  I.graph.vertices.length + 2 * i.val + b.toNat

private def boundary (k : Fin 3) (b : Bool) : Fin 4 :=
  if b then k.succ else k.castSucc

private def originalBoundary (b : Bool) : Fin 4 := if b then 3 else 0

private def cutBoundary (b : Bool) : Fin 4 := if b then 2 else 1

private def node (I : FixedRotationInput) (i : Edge I.graph) : Fin 4 → ℕ :=
  ![Dart.vertex (i, false), fresh I i false, fresh I i true, Dart.vertex (i, true)]

private theorem endpoint_lt {I : FixedRotationInput} (hI : Valid I)
    (i : Edge I.graph) (b : Bool) : Dart.vertex (i, b) < I.graph.vertices.length := by
  have h : I.graph.edges[i].1 < I.graph.vertices.length ∧
      I.graph.edges[i].2 < I.graph.vertices.length :=
    hI.edge_endpoints_lt (List.getElem_mem i.isLt)
  rw [Dart.edge_eq_vertices i] at h
  cases b
  · exact h.1
  · exact h.2

private theorem old_mem {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.vertices.length) : v ∈ I.graph.vertices :=
  hI.1 ▸ List.mem_range.mpr hv

private theorem name_cases {I : FixedRotationInput} {v : ℕ}
    (hv : v ∈ (subdivisionGraph I).vertices) :
    v < I.graph.vertices.length ∨ ∃ (i : Edge I.graph) (b : Bool), v = fresh I i b := by
  change v ∈ List.range (subdivisionSize I) at hv
  have hsize := List.mem_range.mp hv
  unfold subdivisionSize at hsize
  by_cases hb : v < I.graph.vertices.length
  · exact Or.inl hb
  · let d := v - I.graph.vertices.length
    let i : Edge I.graph := ⟨d / 2, by dsimp [d]; omega⟩
    by_cases hpar : d % 2 = 0
    · exact Or.inr ⟨i, false, by dsimp [fresh, i, d] at *; omega⟩
    · exact Or.inr ⟨i, true, by dsimp [fresh, i, d] at *; omega⟩

private noncomputable def cutPoint {I : FixedRotationInput}
    (D : PolygonalDrawing I.graph) (i : Edge I.graph) (b : Bool) : ℂ :=
  (D.route i).eval ((D.route i).endSegment b) (Route.endTime b cut)

private noncomputable def place {I : FixedRotationInput} (D : PolygonalDrawing I.graph)
    (v : ℕ) : ℂ :=
  if v < I.graph.vertices.length then D.vertex v
  else
    let d := v - I.graph.vertices.length
    if h : d / 2 < I.graph.edges.length then
      cutPoint D ⟨d / 2, h⟩ (decide (d % 2 = 1))
    else D.vertex v

private theorem place_old {I : FixedRotationInput} (D : PolygonalDrawing I.graph)
    {v : ℕ} (hv : v < I.graph.vertices.length) : place D v = D.vertex v := by
  simp [place, hv]

private theorem place_fresh {I : FixedRotationInput} (D : PolygonalDrawing I.graph)
    (i : Edge I.graph) (b : Bool) : place D (fresh I i b) = cutPoint D i b := by
  have hq : (fresh I i b - I.graph.vertices.length) / 2 = i.val := by
    cases b <;> simp only [fresh, Bool.toNat_false, Bool.toNat_true] <;> omega
  have hr : (fresh I i b - I.graph.vertices.length) % 2 = b.toNat := by
    cases b <;> simp only [fresh, Bool.toNat_false, Bool.toNat_true] <;> omega
  have hv : ¬fresh I i b < I.graph.vertices.length := by unfold fresh; omega
  unfold place
  rw [ite_eq_right hv]
  dsimp only
  split
  · rename_i h
    have hi : (⟨(fresh I i b - I.graph.vertices.length) / 2, h⟩ : Edge I.graph) = i :=
      Fin.ext hq
    rw [hi, hr]
    cases b <;> rfl
  · rename_i h
    exact (h (hq ▸ i.isLt)).elim

private theorem dart_node {I : FixedRotationInput} (e : Edge (subdivisionGraph I)) (b : Bool) :
    Dart.vertex (e, b) = node I (subdivisionEdgeIndex I e).original
      (boundary (subdivisionEdgeIndex I e).piece b) := by
  generalize hd : subdivisionEdgeIndex I e = d
  obtain ⟨i, k⟩ := d
  have hpair := subdivision_edge_endpoints I e
  rw [hd, Dart.edge_eq_vertices e] at hpair
  have hleft := congrArg Prod.fst (Dart.edge_eq_vertices i)
  have hright := congrArg Prod.snd (Dart.edge_eq_vertices i)
  fin_cases k <;> cases b
  all_goals simp only [SubdivisionEdgeIndex.endpoints, Fin.getElem_fin, List.getElem_cons_zero,
    List.getElem_cons_succ] at hpair
  · exact (congrArg Prod.fst hpair).trans hleft
  · exact congrArg Prod.snd hpair
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair
  · exact congrArg Prod.fst hpair
  · exact (congrArg Prod.snd hpair).trans hright

private theorem piece_endpoint {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing I.graph) (i : Edge I.graph) (k : Fin 3) (b : Bool) :
    ((D.route i).trisect cut cut k).endpoint b = place D (node I i (boundary k b)) := by
  have placed (a : Fin 4) :
      (D.route i).trisectionPoints cut cut a = place D (node I i a) := by
    have hold (b : Bool) :
        (D.route i).endpoint b = place D (Dart.vertex (i, b)) := by
      rw [D.endpoint_eq, place_old D (endpoint_lt hI i b)]
    fin_cases a
    · exact hold false
    · exact (place_fresh D i false).symm
    · exact (place_fresh D i true).symm
    · exact hold true
  rw [Route.endpoint_trisect]
  exact placed (boundary k b)

private noncomputable def drawing {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing I.graph) : PolygonalDrawing (subdivisionGraph I) where
  vertex := place D
  route := fun e =>
    let d := subdivisionEdgeIndex I e
    (D.route d.original).trisect cut cut d.piece
  endpoint_eq := by
    intro e b
    rw [dart_node]
    let d := subdivisionEdgeIndex I e
    exact piece_endpoint hI D d.original d.piece b

-- The two levels of parameter data stay separate: a sample is on the original
-- route, and a trace certifies how a parameter on a new piece maps to that sample.
private structure Sample (p : Route) where
  index : Fin p.segments
  time : ℝ
  inside : time ∈ Set.Icc 0 1

private noncomputable def Sample.value {p : Route} (x : Sample p) : ℂ :=
  p.eval x.index x.time

private def Sample.position {p : Route} (x : Sample p) : ℝ :=
  p.position x.index x.time

private abbrev Sample.atEnd {p : Route} (x : Sample p) (b : Bool) :=
  p.AtEnd x.index x.time b

private noncomputable def cutSample (p : Route) (b : Bool) : Sample p :=
  ⟨p.endSegment b, Route.endTime b cut, Route.endTime_mem b ⟨cut_mem.1.le, cut_mem.2.le⟩⟩

private theorem cutSample_not_end (p : Route) (b c : Bool) :
    ¬(cutSample p b).atEnd c :=
  p.not_atEnd_near_end b c cut_mem

private theorem cutSample_position (p : Route) (b : Bool) :
    (cutSample p b).position = p.trisectionBounds cut cut (cutBoundary b) := by
  change p.position (p.endSegment b) (Route.endTime b cut) = _
  rw [p.position_near_end]
  cases b <;> rfl

private theorem original_node (I : FixedRotationInput) (i : Edge I.graph) (b : Bool) :
    node I i (originalBoundary b) = Dart.vertex (i, b) := by
  cases b <;> rfl

private theorem cut_node (I : FixedRotationInput) (i : Edge I.graph) (b : Bool) :
    node I i (cutBoundary b) = fresh I i b := by
  cases b <;> rfl

-- Contact on the original drawing either has one position on one route, or
-- consists of two original ends bearing the same vertex name.
private theorem sample_contact {I : FixedRotationInput} {D : PolygonalDrawing I.graph}
    (hI : Valid I) (hD : D.IsEmbedding) {i j : Edge I.graph}
    (x : Sample (D.route i)) (y : Sample (D.route j)) (he : x.value = y.value) :
    (i = j ∧ x.position = y.position) ∨
      ∃ b c, x.atEnd b ∧ y.atEnd c ∧ Dart.vertex (i, b) = Dart.vertex (j, c) := by
  have names {b c : Bool} (hx : x.atEnd b) (hy : y.atEnd c) :
      Dart.vertex (i, b) = Dart.vertex (j, c) := by
    have hx' := ((D.route i).at_eq_endpoint x.index x.inside b hx).trans (D.endpoint_eq i b)
    have hy' := ((D.route j).at_eq_endpoint y.index y.inside c hy).trans (D.endpoint_eq j c)
    exact hD.vertices_injective (old_mem hI (endpoint_lt hI i b))
      (old_mem hI (endpoint_lt hI j c)) (hx'.symm.trans (he.trans hy'))
  by_cases hij : i = j
  · subst j
    rcases hD.simple i x.index y.index x.time y.time x.inside y.inside he with
      h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨false, true, hx, hy, names hx hy⟩
    · exact Or.inr ⟨true, false, hx, hy, names hx hy⟩
  · exact Or.inr (hD.edge_contacts i j hij x.index y.index x.time y.time x.inside y.inside he)

private structure Trace (p : Route) (k : Fin 3)
    (i : Fin (p.trisect cut cut k).segments) (u : ℝ) where
  source : Sample p
  value_eq : source.value = (p.trisect cut cut k).eval i u
  interval : source.position ∈
    Set.Icc (p.trisectionBounds cut cut k.castSucc) (p.trisectionBounds cut cut k.succ)
  atLower : source.position = p.trisectionBounds cut cut k.castSucc →
    (p.trisect cut cut k).AtEnd i u false
  atUpper : source.position = p.trisectionBounds cut cut k.succ →
    (p.trisect cut cut k).AtEnd i u true

private theorem trace_exists (p : Route) (k : Fin 3)
    (i : Fin (p.trisect cut cut k).segments) (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    Nonempty (Trace p k i u) := by
  obtain ⟨j, r, hr, he, hp, hl, hh⟩ :=
    p.exists_trisect_eval cut_pos cut_pos cut_small k i u hu
  exact ⟨⟨⟨j, r, hr⟩, he, hp, hl.mp, hh.mp⟩⟩

private theorem Trace.at_boundary {p : Route} {k : Fin 3}
    {i : Fin (p.trisect cut cut k).segments} {u : ℝ}
    (L : Trace p k i u) (a : Fin 4) (he : L.source.position = p.trisectionBounds cut cut a) :
    ∃ b, (p.trisect cut cut k).AtEnd i u b ∧ boundary k b = a := by
  have hm := p.strictMono_trisectionBounds cut_pos cut_pos cut_small
  obtain ⟨hl, hu⟩ := L.interval
  rw [he] at hl hu
  have hlo := hm.le_iff_le.mp hl
  have hhi := hm.le_iff_le.mp hu
  change k.val ≤ a.val at hlo
  change a.val ≤ k.val + 1 at hhi
  rcases (show a.val = k.val ∨ a.val = k.val + 1 by omega) with hv | hv
  · have hb : a = k.castSucc := Fin.ext hv
    subst a
    exact ⟨false, L.atLower he, rfl⟩
  · have hb : a = k.succ := Fin.ext hv
    subst a
    exact ⟨true, L.atUpper he, rfl⟩

private theorem Trace.at_original_end {p : Route} {k : Fin 3}
    {i : Fin (p.trisect cut cut k).segments} {u : ℝ}
    (L : Trace p k i u) (b : Bool) (hb : L.source.atEnd b) :
    ∃ c, (p.trisect cut cut k).AtEnd i u c ∧ boundary k c = originalBoundary b :=
  L.at_boundary (originalBoundary b) (by cases b <;> exact hb)

private theorem interval_contact (p : Route) {k l : Fin 3} (hne : k ≠ l) {w : ℝ}
    (hk : w ∈ Set.Icc (p.trisectionBounds cut cut k.castSucc) (p.trisectionBounds cut cut k.succ))
    (hl : w ∈ Set.Icc (p.trisectionBounds cut cut l.castSucc) (p.trisectionBounds cut cut l.succ)) :
    ∃ a, w = p.trisectionBounds cut cut a := by
  have hm := (p.strictMono_trisectionBounds cut_pos cut_pos cut_small).monotone
  have ordered {a b : Fin 3} (hab : a < b)
      (hx : w ≤ p.trisectionBounds cut cut a.succ)
      (hy : p.trisectionBounds cut cut b.castSucc ≤ w) :
      w = p.trisectionBounds cut cut a.succ :=
    le_antisymm hx ((hm (show a.succ ≤ b.castSucc from hab)).trans hy)
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact ⟨k.succ, ordered hkl hk.2 hl.1⟩
  · exact ⟨l.succ, ordered hlk hl.2 hk.1⟩

private theorem fresh_ne_old {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding) {v : ℕ}
    (hv : v < I.graph.vertices.length) (i : Edge I.graph) (b : Bool) :
    place D (fresh I i b) ≠ place D v := by
  rw [place_fresh, place_old D hv]
  intro he
  let x := cutSample (D.route i) b
  obtain ⟨c, hc, _⟩ :=
    hD.vertex_contacts i x.index x.time x.inside v (old_mem hI hv) he
  exact cutSample_not_end _ b c hc

private theorem place_injective {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding) :
    Set.InjOn (place D) {v | v ∈ (subdivisionGraph I).vertices} := by
  intro u hu v hv he
  rcases name_cases hu with hu' | ⟨i, b, rfl⟩ <;>
    rcases name_cases hv with hv' | ⟨j, c, rfl⟩
  · rw [place_old D hu', place_old D hv'] at he
    exact hD.vertices_injective (old_mem hI hu') (old_mem hI hv') he
  · exact (fresh_ne_old hI hD hu' j c he.symm).elim
  · exact (fresh_ne_old hI hD hv' i b he).elim
  · rw [place_fresh, place_fresh] at he
    rcases sample_contact hI hD (cutSample (D.route i) b) (cutSample (D.route j) c) he with
      ⟨hij, hp⟩ | ⟨a, _, ha, _, _⟩
    · subst j
      rw [cutSample_position, cutSample_position] at hp
      have hk := (D.route i).strictMono_trisectionBounds cut_pos cut_pos cut_small
      have hb := hk.injective hp
      rw [← cut_node I i b, ← cut_node I i c, hb]
    · exact (cutSample_not_end _ b a ha).elim

private theorem vertex_contacts {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding)
    (e : Edge (subdivisionGraph I)) (i : Fin ((drawing hI D).route e).segments)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) (v : ℕ) (hv : v ∈ (subdivisionGraph I).vertices)
    (he : ((drawing hI D).route e).eval i t = (drawing hI D).vertex v) :
    ∃ b, ((drawing hI D).route e).AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  let d := subdivisionEdgeIndex I e
  obtain ⟨L⟩ := trace_exists (D.route d.original) d.piece i t ht
  have hv' : L.source.value = place D v := L.value_eq.trans he
  rcases name_cases hv with hold | ⟨j, b, rfl⟩
  · rw [place_old D hold] at hv'
    obtain ⟨b, hb, hn⟩ := hD.vertex_contacts d.original L.source.index L.source.time
      L.source.inside v (old_mem hI hold) hv'
    obtain ⟨c, hc, hcut⟩ := L.at_original_end b hb
    refine ⟨c, hc, ?_⟩
    rw [dart_node, hcut, original_node]
    exact hn
  · rw [place_fresh] at hv'
    rcases sample_contact hI hD L.source (cutSample (D.route j) b) hv' with
      ⟨hij, hp⟩ | ⟨_, c, _, hc, _⟩
    · subst j
      obtain ⟨c, hc, hp'⟩ := L.at_boundary (cutBoundary b) (hp.trans (cutSample_position _ b))
      exact ⟨c, hc, by rw [dart_node, hp', cut_node]⟩
    · exact (cutSample_not_end _ b c hc).elim

private theorem edge_contacts {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding)
    (e f : Edge (subdivisionGraph I)) (hef : e ≠ f)
    (i : Fin ((drawing hI D).route e).segments) (j : Fin ((drawing hI D).route f).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : ((drawing hI D).route e).eval i s = ((drawing hI D).route f).eval j t) :
    ∃ b c, ((drawing hI D).route e).AtEnd i s b ∧ ((drawing hI D).route f).AtEnd j t c ∧
      Dart.vertex (e, b) = Dart.vertex (f, c) := by
  let a := subdivisionEdgeIndex I e
  let b := subdivisionEdgeIndex I f
  obtain ⟨L⟩ := trace_exists (D.route a.original) a.piece i s hs
  obtain ⟨M⟩ := trace_exists (D.route b.original) b.piece j t ht
  have heq := L.value_eq.trans (he.trans M.value_eq.symm)
  rcases sample_contact hI hD L.source M.source heq with ⟨hi, hp⟩ | ⟨b, c, hb, hc, hn⟩
  · have hpiece : a.piece ≠ b.piece := by
      intro h
      apply hef
      apply Fin.ext
      have he' : e.val = 3 * a.original.val + a.piece.val := subdivisionEdgeIndex_val I e
      have hf' : f.val = 3 * b.original.val + b.piece.val := subdivisionEdgeIndex_val I f
      exact he'.trans (by rw [hi, h, ← hf'])
    have hfint : L.source.position ∈ Set.Icc
        ((D.route a.original).trisectionBounds cut cut b.piece.castSucc)
        ((D.route a.original).trisectionBounds cut cut b.piece.succ) := by
      rw [hp, hi]
      exact M.interval
    obtain ⟨k, hk⟩ := interval_contact (D.route a.original) hpiece L.interval hfint
    have hM : M.source.position = (D.route b.original).trisectionBounds cut cut k := by
      calc
        _ = L.source.position := hp.symm
        _ = (D.route a.original).trisectionBounds cut cut k := hk
        _ = _ := by rw [hi]
    obtain ⟨b, hb, hbe⟩ := L.at_boundary k hk
    obtain ⟨c, hc, hcf⟩ := M.at_boundary k hM
    exact ⟨b, c, hb, hc, by rw [dart_node e, dart_node f, hbe, hcf, hi]⟩
  · obtain ⟨b', hb', hbe⟩ := L.at_original_end b hb
    obtain ⟨c', hc', hcf⟩ := M.at_original_end c hc
    refine ⟨b', c', hb', hc', ?_⟩
    rw [dart_node e, dart_node f, hbe, hcf, original_node, original_node]
    exact hn

private theorem drawing_germ {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing I.graph) (d : Dart I.graph) :
    (drawing hI D).germ (subdivisionDart I d) = cut • D.germ d := by
  rcases d with ⟨i, b⟩
  change ((D.route (subdivisionEdgeIndex I (subdivisionDart I (i, b)).1).original).trisect
    cut cut (subdivisionEdgeIndex I (subdivisionDart I (i, b)).1).piece).germ b =
      cut • (D.route i).germ b
  rw [subdivisionEdgeIndex_subdivisionDart]
  let p := D.route i
  have hcut (c : Bool) :
      (p.cutEnds cut cut).endpoint c = p.endpoint c + cut • p.germ c := by
    rw [p.endpoint_cutEnds, p.eval_near_end, ite_self]
  cases b
  · change (Route.line p.start (p.cutEnds cut cut).start).germ false = _
    rw [Route.germ_line]
    change (p.cutEnds cut cut).endpoint false - p.endpoint false = _
    rw [hcut, add_sub_cancel_left]
  · change (Route.line (p.cutEnds cut cut).finish p.finish).germ true = _
    rw [Route.germ_line]
    change (p.cutEnds cut cut).endpoint true - p.endpoint true = _
    rw [hcut, add_sub_cancel_left]

/-- An embedding of the original listed graph yields an embedding of its recognition
subdivision, with the original declared vertex positions retained. Two interior points
are chosen on each indexed route, and the three resulting pieces are used in order.
The outgoing directions at the selected first and last darts are preserved. -/
theorem exists_subdivision_embedding {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing I.graph) (hD : D.IsEmbedding) :
    ∃ E : PolygonalDrawing (subdivisionGraph I), E.IsEmbedding ∧
      (∀ v ∈ I.graph.vertices, E.vertex v = D.vertex v) ∧
        ∀ d : Dart I.graph, E.direction (subdivisionDart I d) = D.direction d := by
  refine ⟨drawing hI D, ⟨place_injective hI hD, ?_, vertex_contacts hI hD, edge_contacts hI hD⟩,
    ?_, ?_⟩
  · intro e
    exact (hD.simple (subdivisionEdgeIndex I e).original).trisect cut_pos cut_pos cut_small _
  · intro v hv
    apply place_old D
    rw [hI.1] at hv
    exact List.mem_range.mp hv
  · intro d
    simp only [PolygonalDrawing.direction, drawing_germ, Complex.real_smul,
      Complex.arg_real_mul _ cut_pos]

end Cslib.Complexity.Graph.RotationRecognition
