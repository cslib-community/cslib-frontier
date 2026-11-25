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

private theorem eq_or_eq_reverse {G : Graph} {d e : Dart G} (h : d.1 = e.1) :
    d = e ∨ d = e.reverse := by
  rcases d with ⟨i, b⟩
  rcases e with ⟨j, c⟩
  change i = j at h
  subst j
  cases b <;> cases c <;> simp [Dart.reverse]

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
  obtain ⟨p, hp⟩ := h.exists_isPath
  obtain ⟨d, hinj, hd⟩ := Dart.exists_darts_of_induced_trail p hp.isTrail
  have hab' : a.1 ≠ b.1 := by
    intro he
    rcases eq_or_eq_reverse he with he | he
    · exact hab he
    · exact hv ((he ▸ ha) ▸ hb')
  have avoid (e : Dart G) (he : e.vertex = v) (i : Fin p.length) : e.1 ≠ (d i).1 := by
    intro hi
    rcases eq_or_eq_reverse hi with hi | hi
    · exact hv (((hd i).1.symm.trans (hi ▸ he)) ▸ (p.getVert i).property)
    · exact hv (((hd i).2.symm.trans (hi ▸ he)) ▸ (p.getVert (i.val + 1)).property)
  let tail : Fin (p.length + 1) → Dart G := Fin.snoc d b.reverse
  let circuit : Fin (p.length + 2) → Dart G := Fin.cons a tail
  let index (i : Fin (p.length + 2)) := (circuit i).1
  have hindex : Function.Injective index := by
    change Function.Injective (Prod.fst ∘ Fin.cons a (Fin.snoc d b.reverse))
    rw [Fin.comp_cons, Fin.comp_snoc]
    apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        rw [Fin.snoc_last] at hi
        exact hab' hi.symm
      · intro hi
        rw [Fin.snoc_castSucc] at hi
        exact avoid a ha j hi.symm
    · apply Fin.snoc_injective_of_injective hinj
      rintro ⟨i, hi⟩
      exact avoid b hb i hi.symm
  have hstart (i : Fin (p.length + 1)) : (tail i).vertex = (p.getVert i).val := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [tail, Fin.snoc_last, Fin.val_last, p.getVert_length]
    · simpa only [tail, Fin.snoc_castSucc, Fin.val_castSucc] using (hd j).1
  have hnext (i : Fin (p.length + 2)) :
      (circuit i).reverse.vertex = (circuit (finRotate _ i)).vertex := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [circuit, tail, Fin.cons_last, Fin.snoc_last, Dart.reverse_reverse,
        finRotate_last, Fin.cons_zero] using hb.trans ha.symm
    · have hrot : finRotate _ j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [hrot]
      have hsucc : (circuit j.succ).vertex = (p.getVert j).val := by
        simpa only [circuit, Fin.cons_succ] using hstart j
      rw [hsucc]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [circuit, Fin.castSucc_zero, Fin.cons_zero, Fin.val_zero, p.getVert_zero]
      · rw [show k.succ.castSucc = k.castSucc.succ from Fin.ext rfl]
        simpa only [circuit, tail, Fin.cons_succ, Fin.snoc_castSucc, Fin.val_succ] using (hd k).2
  let x (e : Fin G.edges.length) := decide (e ∈ Set.range index)
  let edges : Fin (p.length + 2) ≃ {e // x e = true} :=
    (Equiv.ofInjective index hindex).trans (Equiv.subtypeEquivRight fun _ =>
      decide_eq_true_iff.symm)
  let tag (i : Fin (p.length + 2)) := (circuit i).2
  have hclosed (i : Fin (p.length + 2)) :
      (Dart.vertex (G := G) ((edges i).val, !tag i)) =
        Dart.vertex ((edges (finRotate _ i)).val, tag (finRotate _ i)) := hnext i
  let P := ofCyclicEdges edges tag hclosed
  have hout (i : Fin (p.length + 2)) : P.dart i false = circuit i :=
    ofCyclicEdges_dart_false edges tag hclosed i
  have hin (i : Fin (p.length + 2)) :
      P.dart i true = (circuit ((finRotate _).symm i)).reverse :=
    ofCyclicEdges_dart_true edges tag hclosed i
  have hlast : (finRotate (p.length + 2)).symm 0 = Fin.last (p.length + 1) := by
    apply (finRotate _).injective
    rw [Equiv.apply_symm_apply, finRotate_last]
  refine ⟨x, P, (0 : Fin (p.length + 2)), ?_, ?_, ?_, ?_⟩
  · simpa only [circuit, Fin.cons_zero] using hout 0
  · simpa only [hlast, circuit, Fin.cons_last, tail, Fin.snoc_last, Dart.reverse_reverse]
      using hin 0
  · intro j hj
    change Fin (p.length + 2) at j
    have hvertex := (congrArg Dart.vertex (hout j)).symm.trans hj
    clear hj
    revert hvertex
    refine Fin.cases (fun _ => rfl) (fun i hj => ?_) j
    have he : (p.getVert i).val = v := by
      simpa only [circuit, Fin.cons_succ, hstart] using hj
    exact (hv (he ▸ (p.getVert i).property)).elim
  · have hreach {z : ℕ} (hz : z ≠ v) (j : Fin (p.length + 2)) :
        (circuit j).vertex = z → ∃ hz' : z ∈ S, (G.toSimpleGraph.induce S).Reachable
          ⟨a.reverse.vertex, ha'⟩ ⟨z, hz'⟩ := by
      refine Fin.cases ?_ (fun i => ?_) j
      · intro hj
        exact (hz (hj.symm.trans ha)).elim
      · intro hj
        have he : (p.getVert i).val = z := by
          simpa only [circuit, Fin.cons_succ, hstart] using hj
        have hzS : z ∈ S := he ▸ (p.getVert i).property
        have heq : p.getVert i = ⟨z, hzS⟩ := Subtype.ext he
        refine ⟨hzS, ?_⟩
        rw [← heq]
        exact p.reachable_of_mem_support p.start_mem_support (p.getVert_mem_support i)
    intro e he hz
    obtain ⟨j, hj⟩ : e.1 ∈ Set.range index := of_decide_eq_true he
    rcases eq_or_eq_reverse hj.symm with hforward | hreverse
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
