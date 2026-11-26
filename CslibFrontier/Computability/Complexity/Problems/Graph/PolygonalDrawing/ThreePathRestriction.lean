/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.ThreePathOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Subdrawing
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation

/-!
# Three-path order in an ambient drawing

Selecting the indexed edges of three internally disjoint paths gives degree two at the
internal vertices and degree three at the two ends. The restricted drawing retains the
geometric germs, so comparing the three paths there compares their literal cyclic order in
the original drawing, which can have additional edges at any of those vertices.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Cslib.Polygonal

private theorem rotate_ne_self {G : Graph} (r : RotationSystem G) {a b : Dart G}
    (hv : a.vertex = b.vertex) (hne : a ≠ b) : r.rotate a ≠ a :=
  fun h => hne (((r.sameCycle_iff a b).mpr hv).eq_of_left h)

private theorem inverse_rotate_eq_of_two {G : Graph} (r : RotationSystem G) {a b : Dart G}
    (hv : a.vertex = b.vertex) (hne : a ≠ b)
    (hall : ∀ d : Dart G, d.vertex = a.vertex → d = a ∨ d = b) :
    r.rotate.symm a = b := by
  have h := r.vertex_rotate (r.rotate.symm a)
  rw [r.rotate.apply_symm_apply] at h
  refine (hall _ h.symm).resolve_left fun he => rotate_ne_self r hv hne ?_
  exact (congrArg r.rotate he).symm.trans (r.rotate.apply_symm_apply a)

private theorem inverse_rotate_eq_iff_interval {G : Graph} (r : RotationSystem G)
    {a b c : Dart G} (hab : a.vertex = b.vertex) (hac : a.vertex = c.vertex)
    (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (hall : ∀ d : Dart G, d.vertex = a.vertex → d = a ∨ d = b ∨ d = c) :
    r.rotate.symm a = c ↔ b ∈ r.rotationInterval a c := by
  classical
  have noFixedA := rotate_ne_self r hab hab'
  have rotA := (hall (r.rotate a) (r.vertex_rotate a)).resolve_left noFixedA
  have comparison : r.rotate.symm a = c ↔ r.rotate a = b := by
    rw [Equiv.symm_apply_eq]
    refine ⟨fun h => rotA.resolve_right fun he => ?_, fun h => ?_⟩
    · rcases hall (r.rotate b) ((r.vertex_rotate b).trans hab.symm) with hba | hbb | hbc
      · exact hbc' (r.rotate.injective (hba.trans h))
      · exact rotate_ne_self r hab.symm hab'.symm hbb
      · exact hab' (r.rotate.injective (he.trans hbc.symm))
    · rcases hall (r.rotate c) ((r.vertex_rotate c).trans hac.symm) with hc | hc | hc
      · exact hc.symm
      · exact (hac' (r.rotate.injective (h.trans hc.symm))).elim
      · exact (rotate_ne_self r hac.symm hac'.symm hc).elim
  rw [comparison]
  refine ⟨fun he => Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (r.rotationDistance_pos_of_ne a c hac hac'.symm),
      by simpa only [zero_add, pow_one] using he⟩, fun hm => rotA.resolve_right fun hc => ?_⟩
  have hdist := (r.mem_rotationInterval_iff_lt_distance a b c hab hac hab' hbc' hac').mp hm
  rw [← hc, r.rotationDistance_rotate_of_ne a a rfl noFixedA, r.rotationDistance_self] at hdist
  exact (not_lt_of_ge (r.rotationDistance_pos_of_ne a b hab hab'.symm) hdist).elim

/-- Three nonempty indexed paths between distinct vertices have opposite strict cyclic
orders at their two ends if all crossings between different paths are even. Their interiors
are enumerated by `site`, which has no repetitions even across paths and avoids both ends.
Other edges of the drawing may be incident at any of these vertices. -/
theorem HasRegularContacts.opposite_three_path_orders {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (hR : D.Realizes r) (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.vertices)
    {u v : ℕ} (huv : u ≠ v) {length : Fin 3 → ℕ}
    (path : ∀ k, Fin (length k + 1) → Dart G) (site : ∀ k, Fin (length k) → ℕ)
    (hstart : ∀ k i, (path k i).vertex = Fin.cases u (site k) i)
    (hfinish : ∀ k i, (path k i).reverse.vertex = Fin.lastCases v (site k) i)
    (hsite : Function.Injective fun i : (k : Fin 3) × Fin (length k) => site i.1 i.2)
    (havoid : ∀ k i, site k i ≠ u ∧ site k i ≠ v)
    (hedges : Function.Injective fun i : (k : Fin 3) × Fin (length k + 1) => (path i.1 i.2).1)
    (heven : ∀ (a b : Fin 3), a ≠ b → ∀ i j,
      (D.route (path a i).1).intersectionParity (D.route (path b j).1) = false) :
    path 1 0 ∈ r.rotationInterval (path 0 0) (path 2 0) ↔
      (path 1 (Fin.last (length 1))).reverse ∉
        r.rotationInterval (path 0 (Fin.last (length 0))).reverse
          (path 2 (Fin.last (length 2))).reverse := by
  classical
  let I := (k : Fin 3) × Fin (length k + 1)
  let coords := Fintype.equivFin I
  let edge (i : I) := (path i.1 i.2).1
  let H : Graph := ⟨G.vertices, List.ofFn fun j => G.edges[edge (coords.symm j)]⟩
  let index : Fin H.edges.length ≃ I :=
    (finCongr (List.length_ofFn (f := fun j => G.edges[edge (coords.symm j)]))).trans coords.symm
  let edges : Fin H.edges.length ↪ Fin G.edges.length :=
    ⟨fun j => edge (index j), hedges.comp index.injective⟩
  have edgeEq (j : Fin H.edges.length) : H.edges[j] = G.edges[edges j] := List.getElem_ofFn ..
  have hEnds (j : Fin H.edges.length) (b : Bool) :
      Dart.vertex (G := G) (edges j, b) = Dart.vertex (G := H) (j, b) := by
    have he := (Dart.edge_eq_vertices (G := G) (edges j)).symm.trans
      ((edgeEq j).symm.trans (Dart.edge_eq_vertices (G := H) j))
    cases b
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  let lift : Dart H ↪ Dart G := ⟨fun d => (edges d.1, d.2), fun _ _ h =>
    Prod.ext (edges.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2⟩
  have liftVertex (d : Dart H) : (lift d).vertex = d.vertex := hEnds d.1 d.2
  let arm (k : Fin 3) (i : Fin (length k + 1)) : Dart H :=
    (index.symm ⟨k, i⟩, (path k i).2)
  have liftArm (k : Fin 3) (i : Fin (length k + 1)) : lift (arm k i) = path k i :=
    Prod.ext (congrArg edge (index.apply_symm_apply ⟨k, i⟩)) rfl
  have liftReverse (d : Dart H) : lift d.reverse = (lift d).reverse := rfl
  have startVertex (k : Fin 3) (i : Fin (length k + 1)) :
      (arm k i).vertex = Fin.cases u (site k) i := by
    rw [← liftVertex, liftArm, hstart]
  have finishVertex (k : Fin 3) (i : Fin (length k + 1)) :
      (arm k i).reverse.vertex = Fin.lastCases v (site k) i := by
    rw [← liftVertex, liftReverse, liftArm, hfinish]
  have allDarts (d : Dart H) : ∃ k i, d = arm k i ∨ d = (arm k i).reverse :=
    ⟨(index d.1).1, (index d.1).2, (Bool.eq_or_eq_not d.2 (path (index d.1).1 (index d.1).2).2).imp
      (Prod.ext (index.symm_apply_apply d.1).symm)
      (Prod.ext (index.symm_apply_apply d.1).symm)⟩
  have hH : ∀ w ∈ H.incidenceVertices, w ∈ H.vertices := fun w hw => by
    obtain ⟨e, he, hwe⟩ := List.mem_flatMap.mp hw
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
    exact hG w (List.mem_flatMap.mpr ⟨e, List.mem_iff_get.mpr ⟨edges j, (edgeEq j).symm.trans hj⟩,
      hwe⟩)
  let A := D.subdrawing edges id hEnds
  have hA : A.HasRegularContacts :=
    hD.subdrawing edges id hEnds hH (fun _ h => h) (fun _ _ _ _ h => h)
  have dirEq (d : Dart H) : A.direction d = D.direction (lift d) := rfl
  have dirInj (a b : Dart H) (hab : a.vertex = b.vertex)
      (he : A.direction a = A.direction b) : a = b :=
    lift.injective (hR.directions_injective (lift a) (lift b)
      (by simpa only [liftVertex] using hab) he)
  let s := A.rotationOfDirections dirInj
  have hS : A.Realizes s := A.realizes_rotationOfDirections (fun d => hR.nonzero (lift d)) dirInj
  have startAt (k : Fin 3) : (arm k 0).vertex = u := startVertex k 0
  have finishAt (k : Fin 3) : (arm k (Fin.last (length k))).reverse.vertex = v := by
    rw [finishVertex, Fin.lastCases_last]
  have armsNe {a b : Fin 3} (hab : a ≠ b) (i : Fin (length a + 1)) (j : Fin (length b + 1)) :
      (arm a i).1 ≠ (arm b j).1 := fun he =>
    hab (congrArg Sigma.fst (index.symm.injective he))
  have classifyDart (d : Dart H) :
      (∃ k, d = arm k 0 ∧ d.vertex = u) ∨
      (∃ k, d = (arm k (Fin.last (length k))).reverse ∧ d.vertex = v) ∨
      ∃ k j, (d = arm k j.succ ∨ d = (arm k j.castSucc).reverse) ∧ d.vertex = site k j := by
    obtain ⟨k, i, rfl | rfl⟩ := allDarts d
    · exact Fin.cases (Or.inl ⟨k, rfl, startAt k⟩)
        (fun j => Or.inr (Or.inr ⟨k, j, Or.inl rfl, startVertex k j.succ⟩)) i
    · exact Fin.lastCases (Or.inr (Or.inl ⟨k, rfl, finishAt k⟩))
        (fun j => Or.inr (Or.inr ⟨k, j, Or.inr rfl,
          by rw [finishVertex, Fin.lastCases_castSucc]⟩)) i
  let start : Fin 3 ≃ {d : Dart H // d.vertex = u} :=
    Equiv.ofBijective (fun k => ⟨arm k 0, startAt k⟩)
      ⟨fun _ _ he => by_contra fun hab => armsNe hab 0 0 (congrArg (·.val.1) he), fun d => by
        rcases classifyDart d.val with ⟨k, hk, _⟩ | ⟨_, _, hv⟩ | ⟨k, j, _, hs⟩
        · exact ⟨k, Subtype.ext hk.symm⟩
        · exact absurd (d.property.symm.trans hv) huv
        · exact absurd (hs.symm.trans d.property) (havoid k j).1⟩
  let finish : Fin 3 ≃ {d : Dart H // d.vertex = v} :=
    Equiv.ofBijective (fun k => ⟨(arm k (Fin.last (length k))).reverse, finishAt k⟩)
      ⟨fun _ _ he => by_contra fun hab => armsNe hab _ _ (congrArg (·.val.1) he), fun d => by
        rcases classifyDart d.val with ⟨_, _, hu⟩ | ⟨k, hk, _⟩ | ⟨k, j, _, hs⟩
        · exact absurd (hu.symm.trans d.property) huv
        · exact ⟨k, Subtype.ext hk.symm⟩
        · exact absurd (hs.symm.trans d.property) (havoid k j).2⟩
  have step (k : Fin 3) (j : Fin (length k)) :
      s.rotate.symm (arm k j.castSucc).reverse = arm k j.succ := by
    have ha : (arm k j.castSucc).reverse.vertex = site k j := by
      rw [finishVertex, Fin.lastCases_castSucc]
    refine inverse_rotate_eq_of_two s (ha.trans (startVertex k j.succ).symm)
      (fun h => Nat.succ_ne_self _
        (congrArg (fun i : I => i.2.val) (index.symm.injective (congrArg Prod.fst h))).symm)
      fun d hd => ?_
    rcases classifyDart d with ⟨_, _, hu⟩ | ⟨_, _, hv⟩ | ⟨a, l, hdl, hs⟩
    · exact absurd (ha.symm.trans (hd.symm.trans hu)) (havoid k j).1
    · exact absurd (ha.symm.trans (hd.symm.trans hv)) (havoid k j).2
    · cases @hsite ⟨a, l⟩ ⟨k, j⟩ (hs.symm.trans (hd.trans ha))
      exact hdl.symm
  have even (a b : Fin 3) (hab : a ≠ b) (i : Fin (length a + 1)) (j : Fin (length b + 1)) :
      (A.route (arm a i).1).intersectionParity (A.route (arm b j).1) = false := by
    change (D.route (lift (arm a i)).1).intersectionParity (D.route (lift (arm b j)).1) = false
    simpa only [liftArm] using heven a b hab i j
  have compare := hA.inverse_rotate_iff_not_inverse_rotate_of_three_paths
    (fun e => hsimple (edges e)) hS hH arm start finish (fun _ => rfl) (fun _ => rfl)
    step index.symm.injective even
  have interval {w : ℕ} (ports : Fin 3 ≃ {d : Dart H // d.vertex = w}) :
      s.rotate.symm (ports 0).val = (ports 2).val ↔
        lift (ports 1).val ∈ r.rotationInterval (lift (ports 0).val) (lift (ports 2).val) := by
    let a := (ports 0).val
    let b := (ports 1).val
    let c := (ports 2).val
    have hab := (ports 0).property.trans (ports 1).property.symm
    have hbc := (ports 1).property.trans (ports 2).property.symm
    have ne {i j : Fin 3} (h : i ≠ j) : (ports i).val ≠ (ports j).val :=
      fun he => h (ports.injective (Subtype.ext he))
    have nab : a ≠ b := ne (by decide)
    have nbc : b ≠ c := ne (by decide)
    have nac : a ≠ c := ne (by decide)
    have hall (d : Dart H) (hd : d.vertex = a.vertex) : d = a ∨ d = b ∨ d = c := by
      obtain ⟨i, hi⟩ := ports.surjective ⟨d, hd.trans (ports 0).property⟩
      have h : d = (ports i).val := congrArg Subtype.val hi.symm
      fin_cases i <;> simp [h, a, b, c]
    have hlab : (lift a).vertex = (lift b).vertex := by simpa only [liftVertex] using hab
    have hlbc : (lift b).vertex = (lift c).vertex := by simpa only [liftVertex] using hbc
    have large := hR.clockwise (lift a) (lift b) (lift c) hlab hlbc
      (lift.injective.ne nab) (lift.injective.ne nbc) (lift.injective.ne nac)
    exact (inverse_rotate_eq_iff_interval s hab (hab.trans hbc) nab nac nbc hall).trans
      ((hS.clockwise a b c hab hbc nab nbc nac).symm.trans large)
  simp only [← liftArm, ← liftReverse]
  exact (interval start).symm.trans (compare.trans (interval finish).not)

end Cslib.Complexity.Graph.PolygonalDrawing
