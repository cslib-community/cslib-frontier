/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Polygonal
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.CutVertex
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity
import Mathlib.Data.Finset.Max

/-!
# Order of incident components from crossing parity

A closed passage through a vertex rules out alternation with a second passage whose
other vertices are disjoint from the first. This yields a consecutive component at a cut vertex
and rules out interleaving one component of a separating pair with its complement.

## Main results

* `exists_consecutive_component_darts` finds a consecutive class in one vertex's port order.
* `not_alternates_of_component_after_deleting_pair` forbids interleaving with the complement
  of a chosen component, even if the two outside darts enter different components.
* `exists_separating_component_rank_interval` identifies the first and last darts of that
  component when the cycle is cut at an outside dart.
-/

public section

namespace Cslib.Complexity.Graph.ClosedPassages

open Cslib.Polygonal

private theorem regular_edge_endpoints_ne {G : Graph} {D : PolygonalDrawing G}
    (hreg : D.HasRegularContacts) (e : Fin G.edges.length) :
    Dart.vertex (G := G) (e, false) ≠ Dart.vertex (G := G) (e, true) := fun he => by
  have hend : (D.route e).point 0 = (D.route e).point (Fin.last (D.route e).segments) := by
    change (D.route e).endpoint false = (D.route e).endpoint true
    rw [D.endpoint_eq, D.endpoint_eq, he]
  exact Nat.succ_ne_zero _ (congrArg Fin.val (hreg.points_injective e hend)).symm

private theorem regular_dart_endpoints_ne {G : Graph} {D : PolygonalDrawing G}
    (hreg : D.HasRegularContacts) (d : Dart G) : d.reverse.vertex ≠ d.vertex := by
  rcases d with ⟨e, _ | _⟩
  exacts [(regular_edge_endpoints_ne hreg e).symm, regular_edge_endpoints_ne hreg e]

private theorem not_alternates_of_passages_meeting_at {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    {x y : Fin G.edges.length → Bool} (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (i : Fin P.count) (j : Fin Q.count)
    (hPi : ∀ k, (P.dart k false).vertex = v → k = i)
    (hQj : ∀ l, (Q.dart l false).vertex = v → l = j)
    (hmeet : ∀ e f : Dart G, x e.1 = true → y f.1 = true → e.vertex = f.vertex → e.vertex = v) :
    ¬r.Alternates (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true) := by
  have hdisjoint (e : Fin G.edges.length) (he : x e = true) (hf : y e = true) : False := by
    exact regular_edge_endpoints_ne hreg e ((hmeet (e, false) (e, false) he hf rfl).trans
      (hmeet (e, true) (e, true) he hf rfl).symm)
  exact P.not_alternates_of_unique_shared_passages Q hR hreg hsimple hvertices hdeclared
    hdisjoint (fun e f he hf => heven e f (fun h => hdisjoint e he (h ▸ hf))
      (fun s t => hmeet (e, s) (f, t) he hf)) i j (by
        intro k l hkl
        have hk := hmeet _ _ (P.supported k false) (Q.supported l false) hkl
        exact ⟨hPi k hk, hQj l (hkl.symm.trans hk)⟩)

/-- Two pairs of darts at `v` cannot alternate if their opposite ends can be joined
in disjoint induced vertex sets avoiding `v`. Every pair of distinct edges that meets
only at `v` or has no common endpoint must cross evenly. -/
theorem not_alternates_of_disjoint_induced_paths {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ} {a b c d : Dart G}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    {S T : Set ℕ} (hvS : v ∉ S) (hvT : v ∉ T) (hST : Disjoint S T)
    (ha : a.vertex = v) (ha' : a.reverse.vertex ∈ S) (hb' : b.reverse.vertex ∈ S)
    (hc' : c.reverse.vertex ∈ T) (hd' : d.reverse.vertex ∈ T)
    (hreach₁ : (G.toSimpleGraph.induce S).Reachable
      ⟨a.reverse.vertex, ha'⟩ ⟨b.reverse.vertex, hb'⟩)
    (hreach₂ : (G.toSimpleGraph.induce T).Reachable
      ⟨c.reverse.vertex, hc'⟩ ⟨d.reverse.vertex, hd'⟩) : ¬r.Alternates a b c d := by
  intro halt
  have ⟨hab, hcd, _, _, _, _, hvab, hvcd, hvac, _⟩ := halt
  have hc := hvac.symm.trans ha
  obtain ⟨x, P, i, hPa, hPb, hPi, hPx⟩ :=
    exists_through_darts_of_induced_reachable hvS a b ha (hvab.symm.trans ha) hab ha' hb' hreach₁
  obtain ⟨y, Q, j, hQc, hQd, hQj, hQy⟩ :=
    exists_through_darts_of_induced_reachable hvT c d hc (hvcd.symm.trans hc) hcd hc' hd' hreach₂
  refine not_alternates_of_passages_meeting_at hR hreg hsimple hvertices hdeclared heven
    P Q i j hPi hQj (fun e f he hf hef => by_contra fun hn =>
      Set.disjoint_left.mp hST (hPx e he hn).1 (hef.symm ▸ (hQy f hf (hef ▸ hn)).1)) ?_
  rwa [hPa, hPb, hQc, hQd]

/-- At `v`, darts into one component after deleting `u` and `v` cannot alternate
with two darts outside that component if both of their opposite ends can reach `u` in
the graph with only `v` deleted. The two outside ends may lie in different components
after deleting both vertices. This supplies the local non-alternation in Claim B of
[FulekKynclPalvolgyi2017], §3. -/
theorem not_alternates_of_component_after_deleting_pair {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ} {a b c d : Dart G}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    (u : {w : ℕ // w ≠ v})
    (C : ((G.toSimpleGraph.induce {w | w ≠ v}).induce {w | w ≠ u}).ConnectedComponent)
    (ha : a.vertex = v)
    (haS : a.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp))
    (hbS : b.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp))
    (hcS : c.reverse.vertex ∉ Subtype.val '' (Subtype.val '' C.supp))
    (hdS : d.reverse.vertex ∉ Subtype.val '' (Subtype.val '' C.supp))
    (hc : c.reverse.vertex ≠ v) (hd : d.reverse.vertex ≠ v)
    (hcu : (G.toSimpleGraph.induce {w | w ≠ v}).Reachable ⟨c.reverse.vertex, hc⟩ u)
    (hdu : (G.toSimpleGraph.induce {w | w ≠ v}).Reachable ⟨d.reverse.vertex, hd⟩ u) :
    ¬r.Alternates a b c d := by
  let K := G.toSimpleGraph.induce {w | w ≠ v}
  let W := Subtype.val '' C.supp
  let S : Set ℕ := Subtype.val '' W
  let T : Set ℕ := Subtype.val '' Wᶜ
  have hST : Disjoint S T := Set.disjoint_left.mpr fun _ ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩ =>
    hy (Subtype.ext (hzx.trans hzy.symm) ▸ hx)
  let projection : (K.induce {w | w ≠ u}) →g G.toSimpleGraph := ⟨fun w => w.val.val, fun h => h⟩
  let outside : K.induce Wᶜ →g G.toSimpleGraph.induce T :=
    ⟨fun x => ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩, fun h => h⟩
  have transport (U : Set ℕ) (hU : U = projection '' C.supp) (h₁ : a.reverse.vertex ∈ U)
      (h₂ : b.reverse.vertex ∈ U) :
      (G.toSimpleGraph.induce U).Reachable ⟨a.reverse.vertex, h₁⟩ ⟨b.reverse.vertex, h₂⟩ := by
    subst U
    exact C.reachable_induce_image projection h₁ h₂
  have hP := transport S (Set.image_image _ _ _) haS hbS
  have hcW : (⟨c.reverse.vertex, hc⟩ : {w : ℕ // w ≠ v}) ∉ W :=
    fun h => hcS ⟨⟨c.reverse.vertex, hc⟩, h, rfl⟩
  have hdW : (⟨d.reverse.vertex, hd⟩ : {w : ℕ // w ≠ v}) ∉ W :=
    fun h => hdS ⟨⟨d.reverse.vertex, hd⟩, h, rfl⟩
  exact not_alternates_of_disjoint_induced_paths hR hreg hsimple hvertices hdeclared heven
    (S := S) (T := T) (fun ⟨x, _, hx⟩ => x.property hx) (fun ⟨x, _, hx⟩ => x.property hx) hST ha
    haS hbS ⟨_, hcW, rfl⟩ ⟨_, hdW, rfl⟩ hP (((hcu.avoiding_component_after_delete C hcW).trans
      (hdu.avoiding_component_after_delete C hdW).symm).map outside)

/-- Darts into one separating component form a single interval starting from any outside
cut dart. The outside darts must reach the other separator after deleting the current
vertex. The interval endpoints are actual darts, including when the component has
only one incident dart. -/
theorem exists_separating_component_rank_interval {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    (u : {w : ℕ // w ≠ v})
    (C : ((G.toSimpleGraph.induce {w | w ≠ v}).induce {w | w ≠ u}).ConnectedComponent)
    (o w : Dart G) (ho : o.vertex = v) (hw : w.vertex = v)
    (hoC : o.reverse.vertex ∉ Subtype.val '' (Subtype.val '' C.supp))
    (hwC : w.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp))
    (hreach : ∀ d : Dart G, d.vertex = v →
      d.reverse.vertex ∉ Subtype.val '' (Subtype.val '' C.supp) →
      ∀ hd : d.reverse.vertex ≠ v,
        (G.toSimpleGraph.induce {w | w ≠ v}).Reachable ⟨d.reverse.vertex, hd⟩ u) :
    ∃ a b : Dart G, a.vertex = v ∧ b.vertex = v ∧
      a.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp) ∧
      b.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp) ∧
      ∀ d : Dart G, d.vertex = v →
        (d.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp) ↔
          r.rotationDistance o a ≤ r.rotationDistance o d ∧
            r.rotationDistance o d ≤ r.rotationDistance o b) := by
  classical
  let enters (d : Dart G) : Prop :=
    d.reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp)
  let S := Finset.univ.filter fun d : Dart G => d.vertex = v ∧ enters d
  let rank := r.rotationDistance o
  have hmem (d : Dart G) : d ∈ S ↔ d.vertex = v ∧ enters d := by simp [S]
  have hS : S.Nonempty := ⟨w, (hmem w).mpr ⟨hw, hwC⟩⟩
  obtain ⟨a, has, hmin⟩ := S.exists_min_image rank hS
  obtain ⟨b, hbs, hmax⟩ := S.exists_max_image rank hS
  obtain ⟨ha, haC⟩ := (hmem a).mp has
  obtain ⟨hb, hbC⟩ := (hmem b).mp hbs
  refine ⟨a, b, ha, hb, haC, hbC, fun d hd => ⟨fun hc => ?_, ?_⟩⟩
  · exact ⟨hmin d ((hmem d).mpr ⟨hd, hc⟩), hmax d ((hmem d).mpr ⟨hd, hc⟩)⟩
  · rintro ⟨hl, hr⟩
    -- An outside dart strictly between the extrema would alternate with the cut dart.
    by_contra hdC
    have hoa := ho.trans ha.symm
    have hob := ho.trans hb.symm
    have hod := ho.trans hd.symm
    have had : a ≠ d := fun he => hdC (he ▸ haC)
    have hbd : b ≠ d := fun he => hdC (he ▸ hbC)
    have hlt : rank a < rank d :=
      lt_of_le_of_ne hl (fun he => had ((r.rotationDistance_eq_iff_eq o a d hoa hod).mp he))
    have hgt : rank d < rank b :=
      lt_of_le_of_ne hr (fun he => hbd ((r.rotationDistance_eq_iff_eq o d b hod hob).mp he).symm)
    have hao : a ≠ o := fun he => hoC (he ▸ haC)
    have hbo : b ≠ o := fun he => hoC (he ▸ hbC)
    have hod' : o ≠ d := fun he => by
      have hzero : rank o = 0 := r.rotationDistance_self o
      rw [← he, hzero] at hlt
      exact Nat.not_lt_zero _ hlt
    have haInside := (r.mem_rotationInterval_iff_lt_distance o a d hoa hod
      hao.symm had hod').mpr hlt
    have hbOutside : b ∉ r.rotationInterval o d :=
      fun he => (not_lt_of_ge hgt.le)
        ((r.mem_rotationInterval_iff_lt_distance o b d hob hod hbo.symm hbd hod').mp he)
    have ho' : o.reverse.vertex ≠ v := ho ▸ regular_dart_endpoints_ne hreg o
    have hd' : d.reverse.vertex ≠ v := hd ▸ regular_dart_endpoints_ne hreg d
    apply not_alternates_of_component_after_deleting_pair hR hreg hsimple hvertices
      hdeclared heven u C ha haC hbC hoC hdC ho' hd'
      (hreach o ho hoC ho') (hreach d hd hdC hd')
    exact ⟨fun he => (ne_of_lt (hlt.trans hgt)) (congrArg rank he), hod', hao, had, hbo, hbd,
      ha.trans hb.symm, hod, hoa.symm, iff_of_true haInside hbOutside⟩

/-- At a vertex `v`, a pair of darts into one component of the vertex-deleted graph cannot
alternate with a pair into another component. Crossings are assumed even for distinct edges
that share no endpoint other than `v`, as in an independently even drawing at an even vertex. -/
theorem not_alternates_of_distinct_components_away {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ} {a b c d : Dart G}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    (ha : a.vertex = v) (ha' : a.reverse.vertex ≠ v) (hb' : b.reverse.vertex ≠ v)
    (hc' : c.reverse.vertex ≠ v) (hd' : d.reverse.vertex ≠ v)
    (hreach₁ : (G.toSimpleGraph.induce {w | w ≠ v}).Reachable
      ⟨a.reverse.vertex, ha'⟩ ⟨b.reverse.vertex, hb'⟩)
    (hreach₂ : (G.toSimpleGraph.induce {w | w ≠ v}).Reachable
      ⟨c.reverse.vertex, hc'⟩ ⟨d.reverse.vertex, hd'⟩)
    (hsep : ¬ (G.toSimpleGraph.induce {w | w ≠ v}).Reachable
      ⟨a.reverse.vertex, ha'⟩ ⟨c.reverse.vertex, hc'⟩) : ¬ r.Alternates a b c d := by
  intro halt
  have ⟨hab, hcd, _, _, _, _, hvab, hvcd, hvac, _⟩ := halt
  have hc := hvac.symm.trans ha
  obtain ⟨x, P, i, hPa, hPb, hPi, hPx⟩ :=
    exists_through_darts_of_reachable a b ha (hvab.symm.trans ha) hab ha' hb' hreach₁
  obtain ⟨y, Q, j, hQc, hQd, hQj, hQy⟩ :=
    exists_through_darts_of_reachable c d hc (hvcd.symm.trans hc) hcd hc' hd' hreach₂
  refine not_alternates_of_passages_meeting_at hR hreg hsimple hvertices hdeclared heven
    P Q i j hPi hQj (fun e f he hf hef => by_contra fun hn => ?_) (by rwa [hPa, hPb, hQc, hQd])
  have hq := hQy f hf (hef ▸ hn)
  rw [← (Subtype.ext hef : (⟨e.vertex, hn⟩ : {w : ℕ // w ≠ v}) = ⟨f.vertex, hef ▸ hn⟩)] at hq
  exact hsep ((hPx e he hn).trans hq.symm)

/-- At a vertex incident with an edge, one component of the vertex-deleted graph occupies
an interval of the literal clockwise port ranks. Crossings must be even between distinct
edges that share no endpoint other than the vertex. -/
theorem exists_consecutive_component_darts {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {v : ℕ}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {w | w ∈ G.vertices})
    (hdeclared : ∀ e : Dart G, e.vertex ∈ G.vertices)
    (heven : ∀ (e f : Fin G.edges.length), e ≠ f →
      (∀ i j : Bool, Dart.vertex (G := G) (e, i) = Dart.vertex (f, j) →
        Dart.vertex (e, i) = v) → (D.route e).intersectionParity (D.route f) = false)
    (hv : ∃ d : Dart G, d.vertex = v) :
    ∃ a b : Dart G, a.vertex = v ∧ b.vertex = v ∧ ∃ ha : a.reverse.vertex ≠ v,
      ∀ d : Dart G, d.vertex = v → ∀ hd : d.reverse.vertex ≠ v,
        ((G.toSimpleGraph.induce {w | w ≠ v}).Reachable
          ⟨a.reverse.vertex, ha⟩ ⟨d.reverse.vertex, hd⟩ ↔
          r.portRank a ≤ r.portRank d ∧ r.portRank d ≤ r.portRank b) := by
  classical
  let K := G.toSimpleGraph.induce {w | w ≠ v}
  let color (d : Dart G) : Option K.ConnectedComponent :=
    if h : d.reverse.vertex ≠ v then some (K.connectedComponentMk ⟨d.reverse.vertex, h⟩)
    else none
  have avoid (d : Dart G) (hd : d.vertex = v) : d.reverse.vertex ≠ v := by
    rw [← hd]
    exact regular_dart_endpoints_ne hreg d
  have same (d e : Dart G) (hd : d.reverse.vertex ≠ v) (he : e.reverse.vertex ≠ v) :
      color d = color e ↔ K.Reachable ⟨d.reverse.vertex, hd⟩ ⟨e.reverse.vertex, he⟩ := by
    simp only [color, dite_eq_left hd, dite_eq_left he, Option.some.injEq]
    exact ⟨SimpleGraph.ConnectedComponent.exact, SimpleGraph.ConnectedComponent.sound⟩
  obtain ⟨a, b, ha, hb, _, hinterval⟩ :=
    r.exists_consecutive_class_of_no_alternates color hv (by
      intro a b c d ha hab hcd hac halt
      have hports := halt
      obtain ⟨_, _, _, _, _, _, hvab, hvcd, hvac, _⟩ := hports
      have hc := hvac.symm.trans ha
      have ha' := avoid a ha
      have hb' := avoid b (hvab.symm.trans ha)
      have hc' := avoid c hc
      have hd' := avoid d (hvcd.symm.trans hc)
      exact not_alternates_of_distinct_components_away hR hreg hsimple hvertices hdeclared heven
        ha ha' hb' hc' hd' ((same a b ha' hb').mp hab) ((same c d hc' hd').mp hcd)
        (fun h => hac ((same a c ha' hc').mpr h)) halt)
  refine ⟨a, b, ha, hb, avoid a ha, fun d hd hd' => ?_⟩
  rw [← same a d (avoid a ha) hd', eq_comm]
  exact hinterval d hd

end Cslib.Complexity.Graph.ClosedPassages
