/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (closed passages through prescribed darts)

import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.ComponentOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.CutVertex

/-! A positive-length path and an empty path both close through their specified indexed darts. -/
set_option linter.privateModule false

namespace CslibFrontierTests.ClosedPassagesCutVertex

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev triangle : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

private abbrev a : Dart triangle := (0, false)
private abbrev b : Dart triangle := (2, true)

private theorem a_other : a.reverse.vertex ≠ 0 := by decide
private theorem b_other : b.reverse.vertex ≠ 0 := by decide

private theorem bridge : (triangle.toSimpleGraph.induce {w | w ≠ 0}).Reachable
    ⟨a.reverse.vertex, a_other⟩ ⟨b.reverse.vertex, b_other⟩ :=
  SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))

example : ∃ (x : Fin 3 → Bool) (P : ClosedPassages triangle x) (i : Fin P.count),
    P.dart i false = a ∧ P.dart i true = b ∧ x 0 = true ∧ x 2 = true ∧
      (∀ j, (P.dart j false).vertex = 0 → j = i) ∧
      (triangle.toSimpleGraph.induce {w | w ≠ 0}).Reachable
        ⟨a.reverse.vertex, a_other⟩ ⟨b.reverse.vertex, b_other⟩ := by
  obtain ⟨x, P, i, ha, hb, hunique, hreach⟩ :=
    ClosedPassages.exists_through_darts_of_reachable a b rfl rfl (by decide) a_other b_other bridge
  have hx₀ : x 0 = true := by simpa only [ha] using P.supported i false
  have hx₂ : x 2 = true := by simpa only [hb] using P.supported i true
  exact ⟨x, P, i, ha, hb, hx₀, hx₂, hunique, hreach b.reverse hx₂ b_other⟩

private abbrev parallel : Graph := ⟨[0, 1], [(0, 1), (0, 1)]⟩

private abbrev c : Dart parallel := (0, false)
private abbrev d : Dart parallel := (1, false)

private theorem c_other : c.reverse.vertex ≠ 0 := by decide
private theorem d_other : d.reverse.vertex ≠ 0 := by decide

example : ∃ (x : Fin 2 → Bool) (P : ClosedPassages parallel x) (i : Fin P.count),
    P.dart i false = c ∧ P.dart i true = d := by
  have here : (parallel.toSimpleGraph.induce {w | w ≠ 0}).Reachable
      ⟨c.reverse.vertex, c_other⟩ ⟨d.reverse.vertex, d_other⟩ := .rfl
  obtain ⟨x, P, i, hc, hd, _, _⟩ :=
    ClosedPassages.exists_through_darts_of_reachable c d rfl rfl (by decide) c_other d_other here
  exact ⟨x, P, i, hc, hd⟩

private abbrev withDetour : Graph :=
  ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 0), (1, 3), (3, 2)]⟩

private abbrev region : Set ℕ := {v | v = 1 ∨ v = 2}

-- The permitted route from 1 to 2 excludes both edges of the detour through 3.
example : ∃ (x : Fin 5 → Bool) (P : ClosedPassages withDetour x) (i : Fin P.count),
    P.dart i false = (0, false) ∧ P.dart i true = (2, true) ∧ x 3 = false ∧ x 4 = false := by
  have hpath : (withDetour.toSimpleGraph.induce region).Reachable
      ⟨1, Or.inl rfl⟩ ⟨2, Or.inr rfl⟩ :=
    SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))
  obtain ⟨x, P, i, ha, hb, _, hs⟩ :=
    ClosedPassages.exists_through_darts_of_induced_reachable
      (G := withDetour) (S := region) (v := 0) (by decide)
      (0, false) (2, true) rfl rfl (by decide) (Or.inl rfl) (Or.inr rfl) hpath
  have hout (d : Dart withDetour) (hd : d.vertex = 3) : x d.1 = false := by
    by_contra h
    obtain ⟨hm, _⟩ := hs d (Bool.eq_true_of_not_eq_false h) (by rw [hd]; decide)
    exact (by decide : 3 ∉ region) (hd ▸ hm)
  exact ⟨x, P, i, ha, hb, hout (3, true) rfl, hout (4, false) rfl⟩

private abbrev threeArms : Graph :=
  ⟨[0, 1, 2, 3, 4], [(0, 2), (0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 1)]⟩

private abbrev awayZero : Set ℕ := {n | n ≠ 0}
private abbrev one : awayZero := ⟨1, by decide⟩
private abbrev awayPair : Set awayZero := {n | n ≠ one}
private abbrev two : awayPair := ⟨⟨2, by decide⟩, by decide⟩
private abbrev arms := (threeArms.toSimpleGraph.induce awayZero).induce awayPair
private abbrev arm := arms.connectedComponentMk two

private theorem arms_bot : arms = ⊥ := by
  ext x y
  have hx0 : x.val.val ≠ 0 := x.val.property
  have hy0 : y.val.val ≠ 0 := y.val.property
  have hx1 : x.val.val ≠ 1 := fun h => x.property (Subtype.ext h)
  have hy1 : y.val.val ≠ 1 := fun h => y.property (Subtype.ext h)
  change threeArms.toSimpleGraph.Adj x.val.val y.val.val ↔ False
  rw [Graph.toSimpleGraph_adj]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  tauto

private theorem mem_arm {n : ℕ} :
    n ∈ Subtype.val '' (Subtype.val '' arm.supp) ↔ n = 2 := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h : arms.Reachable x two :=
      SimpleGraph.ConnectedComponent.exact ((arm.mem_supp_iff x).mp hx)
    rw [arms_bot, SimpleGraph.reachable_bot] at h
    exact congrArg (fun w : awayPair => w.val.val) h
  · rintro rfl
    exact ⟨two.val, ⟨two, rfl, rfl⟩, rfl⟩

-- The outside darts enter two different components, numbered 3 and 4.
example {D : PolygonalDrawing threeArms} {r : RotationSystem threeArms}
    (hr : D.Realizes r) (hreg : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {v | v ∈ threeArms.vertices})
    (heven : ∀ (e f : Fin threeArms.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := threeArms) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = 0) → (D.route e).intersectionParity (D.route f) = false) :
    ¬r.Alternates (0, false) (1, false) (3, false) (5, false) := by
  apply ClosedPassages.not_alternates_of_component_after_deleting_pair (G := threeArms)
    (a := (0, false)) (b := (1, false)) (c := (3, false)) (d := (5, false))
    hr hreg hsimple hvertices (by decide) heven one arm rfl (mem_arm.mpr rfl) (mem_arm.mpr rfl)
    (fun h => (by decide : (3 : ℕ) ≠ 2) (mem_arm.mp h))
    (fun h => (by decide : (4 : ℕ) ≠ 2) (mem_arm.mp h)) (by decide) (by decide)
  · exact SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))
  · exact SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))

private abbrev twoTriangles : Graph :=
  ⟨[0, 1, 2, 3, 4], [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]⟩

open Classical in
open scoped BigOperators in
-- The induced paths use edges (1, 2) and (3, 4). Only the four spokes contribute.
example {D : PolygonalDrawing twoTriangles} {r : RotationSystem twoTriangles}
    (hr : D.Realizes r) (hreg : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {v | v ∈ twoTriangles.vertices})
    (heven : D.EvenCrossings (fun _ => False)) :
    decide (r.Alternates (0, false) (2, true) (3, false) (5, true)) =
      ∑ f ∈ ({3, 5} : Finset (Fin 6)), ∑ e ∈ ({0, 2} : Finset (Fin 6)),
        (D.route e).intersectionParity (D.route f) := by
  let left : Set ℕ := {v | v = 1 ∨ v = 2}
  let right : Set ℕ := {v | v = 3 ∨ v = 4}
  have hdisj : Disjoint left right := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    change v = 1 ∨ v = 2 at hv
    change v = 3 ∨ v = 4 at hw
    omega
  have hl : 0 ∉ left := (by decide : ¬ (0 = (1 : ℕ) ∨ 0 = 2))
  have hr' : 0 ∉ right := (by decide : ¬ (0 = (3 : ℕ) ∨ 0 = 4))
  apply ClosedPassages.decide_alternates_eq_sum_crossings_of_disjoint_induced_paths
    (v := 0) (S := left) (T := right) hr hreg hsimple hvertices (by decide) heven
    hl hr' hdisj rfl rfl rfl rfl (by decide) (by decide)
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  · exact SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))
  · exact SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))

end CslibFrontierTests.ClosedPassagesCutVertex
