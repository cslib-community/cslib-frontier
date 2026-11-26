/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
import Mathlib.Logic.Equiv.Set

/-!
# Closed passages through prescribed darts at a vertex

A path avoiding a vertex can be closed through two specified darts at that vertex. This
keeps the original edge indices, also when the path is empty and the two darts come from
parallel edges. The construction works for any induced vertex set omitting the common vertex.
It is used to compare components in [issue #3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `Cslib.Complexity.Graph.ClosedPassages.exists_through_darts_of_induced_reachable` constructs the
  passages and identifies the unique visit outside the induced set.
* `Cslib.Complexity.Graph.ClosedPassages.exists_through_darts_of_reachable` specializes to
  deleting a single vertex.
-/

public section

namespace Cslib.Complexity.Graph.ClosedPassages

/-- Two distinct darts at a vertex outside `S` can be closed along a path in the graph
induced on `S`. The passages visit the common vertex exactly once; each remaining supported
endpoint lies in the path's component of the induced graph. -/
theorem exists_through_darts_of_induced_reachable {G : Graph} {S : Set ℕ} {v : ℕ}
    (hv : v ∉ S) (a b : Dart G) (ha : a.vertex = v) (hb : b.vertex = v) (hab : a ≠ b)
    (ha' : a.reverse.vertex ∈ S) (hb' : b.reverse.vertex ∈ S)
    (h : (G.toSimpleGraph.induce S).Reachable ⟨a.reverse.vertex, ha'⟩ ⟨b.reverse.vertex, hb'⟩) :
    ∃ (x : Fin G.edges.length → Bool) (P : ClosedPassages G x) (i : Fin P.count),
      P.dart i false = a ∧ P.dart i true = b ∧
      (∀ j, (P.dart j false).vertex = v → j = i) ∧
      ∀ (e : Dart G), x e.1 = true → e.vertex ≠ v →
        ∃ he : e.vertex ∈ S, (G.toSimpleGraph.induce S).Reachable
          ⟨a.reverse.vertex, ha'⟩ ⟨e.vertex, he⟩ := by
  classical
  obtain ⟨n, circuit, site, hfirst, hfinal, hstart, hfinish, hindex, _, hsiteReach⟩ :=
    Dart.exists_path_of_induced_reachable a b (ha.symm ▸ hv) (hb.symm ▸ hv) hab ha' hb' h
  let index (i : Fin (n + 1)) := (circuit i).1
  have hnext (i : Fin (n + 1)) :
      (circuit i).reverse.vertex = (circuit (finRotate _ i)).vertex :=
    Fin.lastCases (by rw [hfinal, finRotate_last, hfirst, ha, hb])
      (fun j => by
        rw [show finRotate (n + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt,
          hfinish, Fin.lastCases_castSucc, hstart]
        rfl) i
  let x (e : Fin G.edges.length) := decide (e ∈ Set.range index)
  let edges : Fin (n + 1) ≃ {e // x e = true} :=
    (Equiv.ofInjective index hindex).trans (Equiv.subtypeEquivRight fun _ =>
      decide_eq_true_iff.symm)
  let tag (i : Fin (n + 1)) := (circuit i).2
  have hclosed (i : Fin (n + 1)) :
      Dart.vertex (G := G) ((edges i).val, !tag i) =
        Dart.vertex ((edges (finRotate _ i)).val, tag (finRotate _ i)) := hnext i
  let P := ofCyclicEdges edges tag hclosed
  have hout (i : Fin (n + 1)) : P.dart i false = circuit i :=
    ofCyclicEdges_dart_false edges tag hclosed i
  have hin : P.dart (0 : Fin (n + 1)) true = (circuit ((finRotate (n + 1)).symm 0)).reverse :=
    ofCyclicEdges_dart_true edges tag hclosed 0
  have hlast : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate _).injective (by rw [Equiv.apply_symm_apply, finRotate_last])
  refine ⟨x, P, (0 : Fin (n + 1)), (hout 0).trans hfirst,
    by rw [hin, hlast, hfinal], ?_, ?_⟩
  · intro (j : Fin (n + 1)) hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · rfl
    · rw [hout, hstart] at hj
      exact (hv (hj ▸ (hsiteReach i).choose)).elim
  · have hreach {z : ℕ} (hz : z ≠ v) (j : Fin (n + 1)) (hj : (circuit j).vertex = z) :
        ∃ hz' : z ∈ S, (G.toSimpleGraph.induce S).Reachable ⟨a.reverse.vertex, ha'⟩ ⟨z, hz'⟩ := by
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · exact (hz (hj.symm.trans ((congrArg Dart.vertex hfirst).trans ha))).elim
      · rw [hstart] at hj
        exact hj ▸ hsiteReach i
    intro e he hz
    obtain ⟨j, hj⟩ : e.1 ∈ Set.range index := of_decide_eq_true he
    rcases Dart.eq_or_eq_reverse_of_edge_eq hj.symm with hforward | hreverse
    · exact hreach hz j (congrArg Dart.vertex hforward).symm
    · exact hreach hz (finRotate _ j) ((hnext j).symm.trans
        (congrArg Dart.vertex hreverse).symm)

/-- Distinct nonloop darts at `v` whose opposite vertices are connected outside `v` occur
together in a closed passage system. There is exactly one visit to `v`, and all other
supported endpoints lie in the component of the connecting path in the vertex-deleted graph. -/
theorem exists_through_darts_of_reachable {G : Graph} {v : ℕ} (a b : Dart G)
    (ha : a.vertex = v) (hb : b.vertex = v) (hab : a ≠ b)
    (ha' : a.reverse.vertex ≠ v) (hb' : b.reverse.vertex ≠ v)
    (h : (G.toSimpleGraph.induce {w | w ≠ v}).Reachable
      ⟨a.reverse.vertex, ha'⟩ ⟨b.reverse.vertex, hb'⟩) :
    ∃ (x : Fin G.edges.length → Bool) (P : ClosedPassages G x) (i : Fin P.count),
      P.dart i false = a ∧ P.dart i true = b ∧
      (∀ j, (P.dart j false).vertex = v → j = i) ∧
      ∀ (e : Dart G), x e.1 = true → ∀ he : e.vertex ≠ v,
        (G.toSimpleGraph.induce {w | w ≠ v}).Reachable
          ⟨a.reverse.vertex, ha'⟩ ⟨e.vertex, he⟩ := by
  obtain ⟨x, P, i, hPa, hPb, huniq, hsupport⟩ :=
    exists_through_darts_of_induced_reachable (S := {w | w ≠ v}) (fun h => h rfl)
      a b ha hb hab ha' hb' h
  exact ⟨x, P, i, hPa, hPb, huniq, fun e he hv => (hsupport e he hv).choose_spec⟩

end Cslib.Complexity.Graph.ClosedPassages
