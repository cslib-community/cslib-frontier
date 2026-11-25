/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Even crossing parity of polygonal drawings

`EvenCrossings` records even indexed open-segment crossing parity on independent edges and
on distinct edge occurrences incident with a marked vertex of a polygonal drawing.
The subdrawing module proves that restricting routes preserves this condition.
Concatenating a directed dart sequence retains the original indexed crossing parities
additively and preserves the two outer germs.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Cslib.Polygonal

/-- Independent edge pairs and pairs incident with a marked vertex have even indexed
open-segment crossing parity. Edges and their incidences are distinguished by list position. -/
@[expose] def EvenCrossings {G : Graph} (D : PolygonalDrawing G) (marked : ℕ → Prop) : Prop :=
  ∀ e f : Fin G.edges.length, e ≠ f →
    ((∀ b c : Bool, Dart.vertex (e, b) ≠ Dart.vertex (f, c)) ∨
      ∃ b c : Bool, Dart.vertex (e, b) = Dart.vertex (f, c) ∧ marked (Dart.vertex (e, b))) →
    (D.route e).intersectionParity (D.route f) = false

private theorem orientedRoute_spec {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    let p := if d.2 then (D.route d.1).reverse else D.route d.1
    p.start = D.vertex d.vertex ∧ p.finish = D.vertex d.reverse.vertex ∧
      p.germ false = D.germ d ∧ p.germ true = D.germ d.reverse ∧
      p.support = (D.route d.1).support ∧
      ∀ e, p.intersectionParity (D.route e) = (D.route d.1).intersectionParity (D.route e) := by
  rcases d with ⟨i, tag⟩
  cases tag
  · exact ⟨D.endpoint_eq i false, D.endpoint_eq i true, rfl, rfl, rfl, fun _ => rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, Route.support_reverse _, fun e => ?_⟩
    · change (D.route i).reverse.endpoint false = _
      rw [Route.endpoint_reverse]
      exact D.endpoint_eq i true
    · change (D.route i).reverse.endpoint true = _
      rw [Route.endpoint_reverse]
      exact D.endpoint_eq i false
    · exact Route.germ_reverse _ false
    · exact Route.germ_reverse _ true
    · exact Route.intersectionParity_reverse_left _ _

/-- Orient each edge route along its given dart and concatenate the routes in sequence.
The geometry agrees with traversal when consecutive darts have matching vertices. -/
@[expose] def dartSequenceRoute {G : Graph} (D : PolygonalDrawing G) {n : ℕ}
    (path : Fin (n + 1) → Dart G) : Route :=
  let piece i := if (path i).2 then (D.route (path i).1).reverse else D.route (path i).1
  Fin.foldr n (fun i q => (piece i.castSucc).concat q) (piece (Fin.last n))

/-- The route of a consecutive dart sequence has its original outer endpoints and germs.
Its support is the union of the traversed edge supports, and its crossing parity against
any edge sums with multiplicity along the sequence. The route may have self-intersections. -/
theorem dartSequenceRoute_spec {G : Graph} (D : PolygonalDrawing G) {n : ℕ}
    (path : Fin (n + 1) → Dart G)
    (hstep : ∀ i : Fin n, (path i.castSucc).reverse.vertex = (path i.succ).vertex) :
    let p := D.dartSequenceRoute path
    p.start = D.vertex (path 0).vertex ∧
      p.finish = D.vertex (path (Fin.last n)).reverse.vertex ∧
      p.germ false = D.germ (path 0) ∧ p.germ true = D.germ (path (Fin.last n)).reverse ∧
      p.support = ⋃ i, (D.route (path i).1).support ∧
      ∀ e, p.intersectionParity (D.route e) =
        ∑ i, (D.route (path i).1).intersectionParity (D.route e) := by
  dsimp only
  induction n with
  | zero =>
    rw [dartSequenceRoute, Fin.foldr_zero, show Fin.last 0 = 0 from rfl]
    obtain ⟨hstart, hfinish, hfirst, hlast, hsupport, hparity⟩ :=
      orientedRoute_spec D (path 0)
    refine ⟨hstart, hfinish, hfirst, hlast, ?_, fun e => ?_⟩
    · rw [hsupport]
      ext z
      simp only [Set.mem_iUnion]
      refine ⟨fun hz => ⟨0, hz⟩, ?_⟩
      rintro ⟨i, hi⟩
      rwa [Fin.fin_one_eq_zero i] at hi
    · rw [Fin.sum_univ_one]
      exact hparity e
  | succ n ih =>
    let tail (i : Fin (n + 1)) := path i.succ
    let d := path 0
    let p := if d.2 then (D.route d.1).reverse else D.route d.1
    let q := D.dartSequenceRoute tail
    obtain ⟨hpStart, hpFinish, hpFirst, _, hpSupport, hpParity⟩ := orientedRoute_spec D d
    obtain ⟨hqStart, hqFinish, _, hqLast, hqSupport, hqParity⟩ := ih tail (fun i => by
      simpa only [tail, Fin.castSucc_succ] using hstep i.succ)
    have hjoin : p.finish = q.start := by
      change p.finish = _ at hpFinish
      change q.start = _ at hqStart
      rw [hpFinish, hqStart]
      exact congrArg D.vertex (hstep 0)
    have hroute : D.dartSequenceRoute path = p.concat q := by
      simp only [dartSequenceRoute, Fin.foldr_succ, Fin.castSucc_zero, Fin.castSucc_succ,
        Fin.succ_last, Nat.succ_eq_add_one, p, q, d, tail]
      rfl
    rw [hroute]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Route.endpoint_concat p q hjoin false).trans hpStart
    · exact (Route.endpoint_concat p q hjoin true).trans hqFinish
    · exact (Route.germ_concat p q hjoin false).trans hpFirst
    · exact (Route.germ_concat p q hjoin true).trans hqLast
    · rw [Route.support_concat p q hjoin, hpSupport, hqSupport]
      ext z
      simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_succ, d, tail]
    · intro e
      rw [Route.intersectionParity_concat_left p q _ hjoin, hpParity, hqParity]
      exact (Fin.sum_univ_succ (fun i => (D.route (path i).1).intersectionParity (D.route e))).symm

end Cslib.Complexity.Graph.PolygonalDrawing
