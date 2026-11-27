/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary actual reference patch assembly clients)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferencePatchAssembly
import CslibFrontierTests.RotationReferenceStar
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
The raw all-free loop fixture has three actual indexed reference routes meeting at a
strict-interior point outside EVERY declared vertex image. A global no-triple conclusion
therefore requires an actual change of drawing. The assertions use the actual source coordinates.
Finite append-word clients exercise the existing constructor's actual indices and all-real
parameters; no new concatenation representation is used.
-/

public section

namespace Cslib.Tests.RotationReferencePatchAssembly

open Cslib.Polygonal Cslib.Polygonal.Route
open Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

/-- Five all-free original loops, with unused original vertex names retained. -/
@[expose] def tripleInput : FixedRotationInput :=
  ⟨⟨List.range 10, [(0, 0), (6, 6), (1, 1), (2, 2), (8, 8)]⟩, List.replicate 10 none⟩

private theorem triple_valid : Valid tripleInput :=
  (validate_eq_true_iff tripleInput).mp (by decide +kernel)

private theorem triple_order : referenceOrder tripleInput = List.range 20 := by
  decide +kernel

private def first : Fin (subdivisionGraph tripleInput).edges.length := ⟨0, by decide +kernel⟩
private def second : Fin (subdivisionGraph tripleInput).edges.length := ⟨3, by decide +kernel⟩
private def third : Fin (subdivisionGraph tripleInput).edges.length := ⟨12, by decide +kernel⟩

private def fourth : Fin (subdivisionGraph tripleInput).edges.length := ⟨6, by decide +kernel⟩

private theorem selected_endpoints (k : Fin 4) :
    let e := (![first, second, third, fourth] :
      Fin 4 → Fin (subdivisionGraph tripleInput).edges.length) k
    let a : ℕ := (![0, 6, 8, 1] : Fin 4 → ℕ) k
    let b : ℕ := (![10, 12, 18, 14] : Fin 4 → ℕ) k
    ((referenceDrawing tripleInput).route e).start = parabolaPoint a ∧
      ((referenceDrawing tripleInput).route e).finish = parabolaPoint b := by
  -- Establish actual endpoint membership before reading ranks; no idxOf default is used.
  let e := (![first, second, third, fourth] :
      Fin 4 → Fin (subdivisionGraph tripleInput).edges.length) k
  have hmem := (subdivision_endpoint_spec triple_valid e).1
  have hrank (tag : Bool) :
      (referenceOrder tripleInput).idxOf (Dart.vertex (e, tag)) = Dart.vertex (e, tag) := by
    have hv : Dart.vertex (e, tag) < 20 := by
      simpa only [triple_order, List.mem_range] using hmem tag
    rw [triple_order]
    have hi := List.get_idxOf (l := List.range 20) List.nodup_range
      ⟨Dart.vertex (e, tag), by simpa only [List.length_range] using hv⟩
    simpa only [List.get_eq_getElem, List.getElem_range, Fin.val_mk] using hi
  constructor
  · change parabolaPoint ((referenceOrder tripleInput).idxOf (Dart.vertex (e, false)) : ℝ) = _
    rw [hrank false]
    fin_cases k <;> rfl
  · change parabolaPoint ((referenceOrder tripleInput).idxOf (Dart.vertex (e, true)) : ℝ) = _
    rw [hrank true]
    fin_cases k <;> rfl

private theorem selected_open (k : Fin 3) :
    let e := (![first, second, third] : Fin 3 → Fin (subdivisionGraph tripleInput).edges.length) k
    (⟨9, 90⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route e).start
      ((referenceDrawing tripleInput).route e).finish := by
  have he := selected_endpoints k.castSucc
  fin_cases k <;>
    norm_num only [Fin.castSucc_mk, Matrix.cons_val_zero', Matrix.cons_val_succ'] at he ⊢ <;>
    rw [he.1, he.2] <;>
    apply (mem_openChord_iff (by norm_num) _).mpr <;> norm_num

private theorem another_open :
    (⟨14 / 5, 28⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route first).start
      ((referenceDrawing tripleInput).route first).finish ∧
    (⟨14 / 5, 28⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route fourth).start
      ((referenceDrawing tripleInput).route fourth).finish := by
  have hfirst := selected_endpoints 0
  have hfourth := selected_endpoints 3
  norm_num at hfirst hfourth
  constructor
  · rw [hfirst.1, hfirst.2]
    exact (mem_openChord_iff (by norm_num) _).mpr (by norm_num)
  · rw [hfourth.1, hfourth.2]
    exact (mem_openChord_iff (by norm_num) _).mpr (by norm_num)

/-- The original reference drawing has a genuine nonvertex triple, even with valid input. -/
theorem source_has_nonvertex_triple : Valid tripleInput ∧
    ∃ e f g : Fin (subdivisionGraph tripleInput).edges.length,
      e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
      (⟨9, 90⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route e).start
        ((referenceDrawing tripleInput).route e).finish ∧
      (⟨9, 90⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route f).start
        ((referenceDrawing tripleInput).route f).finish ∧
      (⟨9, 90⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing tripleInput).route g).start
        ((referenceDrawing tripleInput).route g).finish ∧
      ∀ v ∈ (subdivisionGraph tripleInput).vertices,
        (⟨9, 90⟩ : ℂ) ≠ (referenceDrawing tripleInput).vertex v := by
  refine ⟨triple_valid, first, second, third, by decide +kernel, by decide +kernel,
    by decide +kernel, selected_open 0, selected_open 1, selected_open 2, ?_⟩
  intro v hv heq
  have hvertex : (referenceDrawing tripleInput).vertex v =
      parabolaPoint ((referenceOrder tripleInput).idxOf v : ℝ) := rfl
  rw [hvertex] at heq
  have hx := congrArg Complex.re heq
  have hy := congrArg Complex.im heq
  change (9 : ℝ) = ((referenceOrder tripleInput).idxOf v : ℝ) at hx
  change (90 : ℝ) = ((referenceOrder tripleInput).idxOf v : ℝ) ^ 2 at hy
  rw [← hx] at hy
  norm_num at hy

-- Exact segment count includes the original line and each appended actual node.
example (p : Route) (a b c : ℂ) :
    ([a, b, c].foldl Route.append p).segments = p.segments + 3 :=
  segments_foldl_append p [a, b, c]

-- The new final-segment specification applies even outside the closed unit interval.
example (p : Route) (a b : ℂ) (i : Fin ([a, b].foldl Route.append p).segments) :
    (∃ j : Fin p.segments, i.val = j.val ∧
      ([a, b].foldl Route.append p).eval i 3 = p.eval j 3) ∨
    (∃ q : Fin 2, i.val = p.segments + q.val ∧
      ([a, b].foldl Route.append p).eval i 3 =
        AffineMap.lineMap ((p.finish :: [a, b])[q.castSucc]) (([a, b] : List ℂ)[q]) (3 : ℝ)) := by
  rcases foldl_append_eval_cases p [a, b] i 3 with ⟨j, hj, he, _⟩ | ⟨q, hq, he, _⟩
  · exact Or.inl ⟨j, hj, he⟩
  · exact Or.inr ⟨q, hq, he⟩


-- The supplied global drawing has an actual patched free route, not the old one-segment
-- witness. Its full center list includes the genuine triple point proved above.
example : ∃ D' : PolygonalDrawing (subdivisionGraph tripleInput),
    D'.vertex = (referenceDrawing tripleInput).vertex ∧
    7 ≤ (D'.route first).segments ∧
    (∀ e, (D'.route e).IsSimple) ∧
    (∀ e b, ∃ c : ℝ, 0 < c ∧
      (D'.route e).germ b = c • ((referenceDrawing tripleInput).route e).germ b) := by
  classical
  obtain ⟨A⟩ :=
      exists_reference_patch_assembly triple_valid
  have hsupport : (⟨9, 90⟩ : ℂ) ∈ ((referenceDrawing tripleInput).route first).support := by
    change (⟨9, 90⟩ : ℂ) ∈
      (Route.line ((referenceDrawing tripleInput).route first).start
        ((referenceDrawing tripleInput).route first).finish).support
    rw [support_line]
    exact openSegment_subset_segment ℝ _ _ (selected_open 0)
  have hsupport' : (⟨14 / 5, 28⟩ : ℂ) ∈ ((referenceDrawing tripleInput).route first).support := by
    change (⟨14 / 5, 28⟩ : ℂ) ∈
      (Route.line ((referenceDrawing tripleInput).route first).start
        ((referenceDrawing tripleInput).route first).finish).support
    rw [support_line]
    exact openSegment_subset_segment ℝ _ _ another_open.1
  let z : ReferencePatchAssembly.EdgeCenter tripleInput first :=
    ⟨(⟨9, 90⟩ : ℂ), ⟨first, second, by decide +kernel,
      selected_open 0, selected_open 1⟩, hsupport⟩
  let w : ReferencePatchAssembly.EdgeCenter tripleInput first :=
    ⟨(⟨14 / 5, 28⟩ : ℂ), ⟨first, fourth, by decide +kernel,
      another_open.1, another_open.2⟩, hsupport'⟩
  have hzmem := A.centers_complete first z
  have hwmem := A.centers_complete first w
  have hzw : z ≠ w := by
    intro heq
    have hx := congrArg (fun u => u.val.re) heq
    norm_num [z, w] at hx
  have hcard : 2 ≤ (A.centers first).length := by
    have hsubset : ({z, w} : Finset _) ⊆ (A.centers first).toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact List.mem_toFinset.mpr hzmem
      · rcases Finset.mem_singleton.mp hx with rfl
        exact List.mem_toFinset.mpr hwmem
    have hh := Finset.card_le_card hsubset
    rw [Finset.card_pair hzw] at hh
    exact hh.trans (List.toFinset_card_le (A.centers first))
  have hsegments := A.segments_eq first (by decide +kernel)
  exact ⟨A.drawing, A.vertex_eq, by omega, A.simple, A.germs⟩

-- The public prescribed-star fixture includes both loop ends, parallel occurrences,
-- decreasing source orientations and a fixed isolate. Frozen routes remain literally
-- original even when other routes receive patches; declared star contacts are permitted.
example :
    let I := RotationReferenceStar.input
    ∃ D' : PolygonalDrawing (subdivisionGraph I),
      D'.vertex = (referenceDrawing I).vertex ∧ (∀ e, (D'.route e).IsSimple) ∧
      (∀ e : Fin (subdivisionGraph I).edges.length,
        ((subdivide I)[e.val]'(by
          simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
          D'.route e = (referenceDrawing I).route e) ∧
      D'.vertex 2 = (referenceDrawing I).vertex 2 ∧
      (∀ (i : Fin (D'.route ⟨0, by decide⟩).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
        (D'.route ⟨0, by decide⟩).eval i t ≠ D'.vertex 2) := by
  let I := RotationReferenceStar.input
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide +kernel)
  obtain ⟨A⟩ :=
      exists_reference_patch_assembly hI
  refine ⟨A.drawing, A.vertex_eq, A.simple, ?_, congrFun A.vertex_eq 2, ?_⟩
  · intro e he
    change (subdivide I)[e.val].frozen = true at he
    have hh := A.route_eq e
    dsimp only at hh
    rw [ite_eq_left he] at hh
    exact hh
  · intro i t ht heq
    obtain ⟨b, _, hb⟩ := A.vertex_contacts ⟨0, by decide⟩ i t ht 2 (by decide +kernel) heq
    cases b <;> norm_num [I, RotationReferenceStar.input, Dart.vertex,
      Cslib.Complexity.Graph.edgeEndpoint,
      subdivisionGraph, subdivide] at hb

-- When the actual crossing set is empty, every selected complete list is empty and
-- the supplied assembly retains each literal original route, even for free members.
example {I : FixedRotationInput} (hI : Valid I)
    (hno : ∀ z : ℂ, ¬∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish) :
    ∃ D' : PolygonalDrawing (subdivisionGraph I),
      D'.vertex = (referenceDrawing I).vertex ∧
      (∀ e, D'.route e = (referenceDrawing I).route e) := by
  obtain ⟨A⟩ :=
      exists_reference_patch_assembly hI
  have hnil (e : Fin (subdivisionGraph I).edges.length) : A.centers e = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z _
    exact hno z.val z.property.1
  refine ⟨A.drawing, A.vertex_eq, ?_⟩
  intro e
  simpa only [hnil, ite_self] using A.route_eq e

-- In the empty-edge case the internally selected lists and drawing still exist; all
-- isolated declared vertices are retained. There is no zero-segment Route convention.
example :
    let I : FixedRotationInput := ⟨⟨[0, 1], []⟩, [none, some []]⟩
    ∃ D' : PolygonalDrawing (subdivisionGraph I),
      D'.vertex = (referenceDrawing I).vertex ∧
      (∀ e, D'.route e = (referenceDrawing I).route e) := by
  let I : FixedRotationInput := ⟨⟨[0, 1], []⟩, [none, some []]⟩
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide +kernel)
  obtain ⟨A⟩ :=
      exists_reference_patch_assembly hI
  refine ⟨A.drawing, A.vertex_eq, ?_⟩
  intro e
  exact Fin.elim0 e

end Cslib.Tests.RotationReferencePatchAssembly
