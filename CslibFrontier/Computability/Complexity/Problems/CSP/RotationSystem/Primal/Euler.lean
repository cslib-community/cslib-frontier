/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Components
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Sum

/-!
# Componentwise Euler preservation for CSP polygons

Counts refer to the actual listed graphs and every face orbit, including singleton orbits.
The target predicate is the existing componentwise `NumericalGenusZero`, with no change of
model and no geometric, native-computation or recognition claim.

## Main results

* `Cslib.Complexity.CSP.polygon_component_vertex_count`: exact variable/constraint split.
* `Cslib.Complexity.CSP.polygon_component_edge_count`: preserves indexed edge counts.
* `Cslib.Complexity.CSP.polygon_component_face_card`: complete component face counts.
* `Cslib.Complexity.CSP.numericalGenusZero_polygon_iff`: componentwise Euler equivalence.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph.RotationCertificate Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

private theorem idxOf_var_lt_numVars (o : F.Occurrence) :
    F.distinctVars.idxOf o.var < F.numVars :=
  CSP.length_distinctVars (F := F) ▸
    List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)

/-- Componentwise polygon face count for any black/white face decomposition matching the
constraint indices of forward darts and the incidence faces of backward darts. -/
theorem polygon_component_face_card_of_equiv {α : Type*}
    (r : Graph.RotationSystem (incidenceGraph F)) (root : ℕ) (hr : root < F.numVars)
    (e : (polygonRotation r).Face ≃ α ⊕ r.Face) (idx : α → Fin F.length)
    (hblack : ∀ o : F.Occurrence,
      ∃ a, e (Quotient.mk _ (polygonDart o false)) = .inl a ∧ idx a = o.1)
    (hwhite : ∀ o : F.Occurrence,
      e (Quotient.mk _ (polygonDart ((argumentPermutation F).symm o) true)) =
        .inr (Quotient.mk _ (incidenceDart o false))) :
    Nat.card {f : (polygonRotation r).Face // ∃ d : Graph.Dart (polygonGraph F),
      SameComponent (polygonGraph F) root d.vertex ∧ Quotient.mk _ d = f} =
    Nat.card {a : α // SameComponent (incidenceGraph F) root (F.numVars + (idx a).val)} +
      Nat.card {f : r.Face // ∃ d : Graph.Dart (incidenceGraph F),
        SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f} := by
  let Q : α ⊕ r.Face → Prop := Sum.elim
    (fun a => SameComponent (incidenceGraph F) root (F.numVars + (idx a).val))
    (fun f => ∃ d : Graph.Dart (incidenceGraph F),
      SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f)
  have hmem (f : (polygonRotation r).Face) :
      (∃ d : Graph.Dart (polygonGraph F), SameComponent (polygonGraph F) root d.vertex ∧
        Quotient.mk _ d = f) ↔ Q (e f) := by
    induction f using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨edge, b⟩
      obtain ⟨o, ho⟩ := exists_polygonDart (F := F) (edge, b)
      cases b
      · obtain ⟨a, ha, hidx⟩ := hblack o
        rw [← ho, ha, componentFace_mk_iff _ polygon_endpoints_declared, vertex_polygonDart]
        simp only [Bool.false_eq_true, ↓reduceIte,
          sameComponent_polygon_iff hr (idxOf_var_lt_numVars o), Q, Sum.elim]
        have hc := Graph.RotationSystem.sameComponent_reverse
          (incidenceVertices_declared F) (incidenceDart o false)
        change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at hc
        simp only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte, ← hidx] at hc
        exact ⟨(·.trans hc), (·.trans hc.symm)⟩
      · have hw := Equiv.symm_apply_apply (argumentPermutation F) o ▸
          hwhite (argumentPermutation F o)
        rw [← ho, hw, componentFace_mk_iff _ polygon_endpoints_declared]
        dsimp only [Q, Sum.elim]
        rw [componentFace_mk_iff _ (incidenceVertices_declared F),
          vertex_polygonDart, vertex_incidenceDart]
        exact sameComponent_polygon_iff hr (idxOf_var_lt_numVars (argumentSuccessor o))
  have : Finite α := Finite.of_injective (e.symm ∘ Sum.inl)
    (e.symm.injective.comp Sum.inl_injective)
  calc
    _ = Nat.card {s // Q s} := Nat.card_congr (e.subtypeEquiv hmem)
    _ = Nat.card {a : α // Q (.inl a)} + Nat.card {f : r.Face // Q (.inr f)} := by
      rw [Nat.card_congr (Equiv.subtypeSum (p := Q)), Nat.card_sum]
    _ = _ := rfl

/-- In a component rooted at a dense variable, polygon faces are exactly its constraint
positions together with its original incidence faces. All face orbits are counted. -/
theorem polygon_component_face_card (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) (root : ℕ) (hr : root < F.numVars) :
    Nat.card {f : (polygonRotation r).Face // ∃ d : Graph.Dart (polygonGraph F),
      SameComponent (polygonGraph F) root d.vertex ∧ Quotient.mk _ d = f} =
    Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} +
      Nat.card {f : r.Face // ∃ d : Graph.Dart (incidenceGraph F),
        SameComponent (incidenceGraph F) root d.vertex ∧ Quotient.mk _ d = f} :=
  polygon_component_face_card_of_equiv r root hr (polygonFaceEquiv r hOrder hPos) id
    (fun o => ⟨o.1, polygonFaceEquiv_black r hOrder hPos o, rfl⟩)
    (polygonFaceEquiv_white r hOrder hPos)

open Classical in
/-- The incidence component has the polygon's variable vertices plus its indexed positive
constraint vertices. Vertex names are counted once, while constraint positions stay distinct. -/
theorem polygon_component_vertex_count (root : ℕ) (hr : root < F.numVars) :
    (incidenceGraph F).distinctVertices.countP
      (fun v => decide (SameComponent (incidenceGraph F) root v)) =
    (polygonGraph F).distinctVertices.countP
      (fun v => decide (SameComponent (polygonGraph F) root v)) +
      Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} := by
  classical
  rw [Graph.countP_vertices_range _ _ (incidenceGraph_vertices F),
    Graph.countP_vertices_range _ F.numVars rfl,
    ← Nat.card_congr (finSumFinEquiv.subtypeEquivOfSubtype
      (p := fun v : Fin (F.numVars + F.length) => SameComponent (incidenceGraph F) root v.val)),
    Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  exact congrArg (· + _) (Nat.card_congr
    (Equiv.subtypeEquivRight fun v => (sameComponent_polygon_iff hr v.isLt).symm))

open Classical in
/-- The component edge counts agree exactly: both lists retain one edge position per
occurrence, and its first endpoint is the same dense variable. -/
theorem polygon_component_edge_count (root : ℕ) (hr : root < F.numVars) :
    (polygonGraph F).edges.countP
      (fun e => decide (SameComponent (polygonGraph F) root e.1)) =
    (incidenceGraph F).edges.countP
      (fun e => decide (SameComponent (incidenceGraph F) root e.1)) := by
  classical
  rw [incidenceGraph_edges]
  change (F.occurrences.map _).countP _ = _
  rw [List.countP_map, List.countP_map]
  refine List.countP_congr fun record hrecord => ?_
  obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hrecord
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact sameComponent_polygon_iff hr (idxOf_var_lt_numVars o)

open Classical in
private abbrev ComponentEuler {G : Graph} (s : Graph.RotationSystem G) (root : ℕ) : Prop :=
  G.distinctVertices.countP (fun v => decide (SameComponent G root v)) +
    ((List.finRange (2 * G.edges.length)).countP fun i =>
      decide (SameComponent G root ((Graph.Dart.indexEquiv G).symm i).vertex ∧
        s.IsFaceRepresentative ((Graph.Dart.indexEquiv G).symm i))) =
    G.edges.countP (fun e => decide (SameComponent G root e.1)) + 2

private theorem component_euler_iff (r : Graph.RotationSystem (incidenceGraph F))
    {root : ℕ} (hr : root < F.numVars)
    (hF : Nat.card (ComponentFace (polygonRotation r) root) =
      Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} +
        Nat.card (ComponentFace r root)) :
    ComponentEuler (polygonRotation r) root ↔ ComponentEuler r root := by
  classical
  dsimp only [ComponentEuler]
  rw [count_faceRepresentatives_eq_card_componentFace _ polygon_endpoints_declared,
    count_faceRepresentatives_eq_card_componentFace _ (incidenceVertices_declared F)]
  have hV := polygon_component_vertex_count root hr
  have hE := polygon_component_edge_count root hr
  omega

/-- Backward numerical Euler transport from componentwise face counts on dense variables. -/
theorem numericalGenusZero_polygon_of_face_card
    (r : Graph.RotationSystem (incidenceGraph F))
    (hF : ∀ root < F.numVars,
      Nat.card (ComponentFace (polygonRotation r) root) =
        Nat.card {i : Fin F.length // SameComponent (incidenceGraph F) root (F.numVars + i.val)} +
          Nat.card (ComponentFace r root))
    (hgenus : r.NumericalGenusZero) : (polygonRotation r).NumericalGenusZero := by
  classical
  intro root hr
  have hdense : root < F.numVars := List.mem_range.mp hr
  obtain ⟨o, ho⟩ := exists_occurrence_dense root hdense
  rw [ite_eq_left ⟨polygonDart o false, (vertex_polygonDart o false).trans ho⟩]
  have hi := hgenus root (by rw [incidenceGraph_vertices, List.mem_range]; omega)
  rw [ite_eq_left ⟨incidenceDart o false, (vertex_incidenceDart o false).trans ho⟩] at hi
  exact (component_euler_iff r hdense (hF root hdense)).mpr hi

/-- Replacing every positive ordered incidence star by its actual occurrence-indexed polygon
preserves the existing componentwise numerical genus-zero predicate in both directions.
This includes disconnected and empty instances. It asserts no geometric realization. -/
theorem numericalGenusZero_polygon_iff (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) :
    (polygonRotation r).NumericalGenusZero ↔ r.NumericalGenusZero := by
  classical
  refine ⟨fun hP root hr => ?_,
    numericalGenusZero_polygon_of_face_card r (polygon_component_face_card r hOrder hPos)⟩
  have ⟨o, hdart, hc⟩ : ∃ o : F.Occurrence,
      (∃ d : Graph.Dart (incidenceGraph F), d.vertex = root) ∧
        SameComponent (incidenceGraph F) root (F.distinctVars.idxOf o.var) := by
    by_cases hv : root < F.numVars
    · obtain ⟨o, ho⟩ := exists_occurrence_dense root hv
      refine ⟨o, ⟨incidenceDart o false, (vertex_incidenceDart o false).trans ho⟩, ?_⟩
      rw [← ho]
      exact .refl (by simpa [vertex_incidenceDart] using
        Graph.RotationSystem.vertex_mem (incidenceVertices_declared F) (incidenceDart o false))
    · rw [incidenceGraph_vertices, List.mem_range] at hr
      let o : F.Occurrence := ⟨⟨root - F.numVars, by omega⟩, ⟨0, hPos _⟩⟩
      have ho : (incidenceDart o true).vertex = root := by simp [vertex_incidenceDart, o]; omega
      have hrev := Graph.RotationSystem.sameComponent_reverse
        (incidenceVertices_declared F) (incidenceDart o false)
      change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at hrev
      exact ⟨o, ⟨incidenceDart o true, ho⟩, by simpa [vertex_incidenceDart, ho] using hrev.symm⟩
  rw [ite_eq_left hdart]
  have hp := hP (F.distinctVars.idxOf o.var) (List.mem_range.mpr (idxOf_var_lt_numVars o))
  rw [ite_eq_left ⟨polygonDart o false, vertex_polygonDart o false⟩] at hp
  have hi := (component_euler_iff r (idxOf_var_lt_numVars o)
    (polygon_component_face_card r hOrder hPos _ (idxOf_var_lt_numVars o))).mp hp
  have hrel (v : ℕ) : SameComponent (incidenceGraph F) root v ↔
      SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var) v :=
    ⟨hc.symm.trans, hc.trans⟩
  simpa only [hrel] using hi

end Cslib.Complexity.CSP
