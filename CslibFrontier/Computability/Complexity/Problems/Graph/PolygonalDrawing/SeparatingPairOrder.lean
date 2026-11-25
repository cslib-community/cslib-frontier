/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.IntersectionParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.ThreePathRestriction
import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity

/-!
# Three choices through a separating pair

The prescribed darts into three disjoint vertex sets determine opposite cyclic orders
at two marked ends. The connecting paths are extracted inside the sets. A direct edge
between the two ends can take the place of any such path.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- Three choices through a separating pair occur in opposite orders at its two marked
ends. Each choice is either a direct indexed edge or a pair of prescribed darts admitting
a connecting path in its own induced vertex set. These sets avoid the two ends and are
pairwise disjoint, as for distinct components after deleting the two ends. This is the
triple comparison used for the component orders in [FulekKynclPalvolgyi2017], §3, Claim B. -/
theorem HasRegularContacts.opposite_orders_of_induced_reachable {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {marked : ℕ → Prop}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple) (hR : D.Realizes r)
    (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.vertices) (heven : D.EvenCrossings marked)
    {u v : ℕ} (huv : u ≠ v) (hu : marked u) (hv : marked v)
    (a b : Fin 3 → Dart G) (ha : ∀ k, (a k).vertex = u) (hb : ∀ k, (b k).vertex = v)
    (haInj : Function.Injective fun k => (a k).1)
    (S : Fin 3 → Set ℕ) (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (havoid : ∀ k, u ∉ S k ∧ v ∉ S k)
    (hpath : ∀ k, b k = (a k).reverse ∨
      ∃ (ha' : (a k).reverse.vertex ∈ S k) (hb' : (b k).reverse.vertex ∈ S k),
        (G.toSimpleGraph.induce (S k)).Reachable
          ⟨(a k).reverse.vertex, ha'⟩ ⟨(b k).reverse.vertex, hb'⟩) :
    a 1 ∈ r.rotationInterval (a 0) (a 2) ↔ b 1 ∉ r.rotationInterval (b 0) (b 2) := by
  classical
  have chooseArm (k : Fin 3) : ∃ n : ℕ, ∃ (path : Fin (n + 1) → Dart G) (site : Fin n → ℕ),
      path 0 = a k ∧ (path (Fin.last n)).reverse = b k ∧
      (∀ i, (path i).vertex = Fin.cases u site i) ∧
      (∀ i, (path i).reverse.vertex = Fin.lastCases v site i) ∧
      Function.Injective (fun i => (path i).1) ∧
      Function.Injective site ∧ ∀ i, site i ∈ S k := by
    rcases hpath k with hDirect | ⟨ha', hb', hr⟩
    · have zero (i : Fin (0 + 1)) : i = 0 := by
        apply Fin.ext
        have := i.isLt
        omega
      refine ⟨0, fun _ => a k, Fin.elim0, rfl, hDirect.symm, ?_, ?_,
        fun i j _ => (zero i).trans (zero j).symm, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      · intro i
        have he : i = 0 := zero i
        subst i
        exact ha k
      · intro i
        have he : i = Fin.last 0 := zero i
        subst i
        rw [Fin.lastCases_last, ← hDirect]
        exact hb k
    · have haOutside : (a k).vertex ∉ S k := ha k ▸ (havoid k).1
      have hbOutside : (b k).vertex ∉ S k := hb k ▸ (havoid k).2
      have hab : a k ≠ b k := fun h => huv ((ha k).symm.trans
        ((congrArg Dart.vertex h).trans (hb k)))
      obtain ⟨n, path, site, hfirst, hlast, hs, ht, hi, hj, hre⟩ :=
        Dart.exists_path_of_induced_reachable (a k) (b k) haOutside hbOutside hab ha' hb' hr
      refine ⟨n, path, site, hfirst, hlast, ?_, ?_, hi, hj, fun i => (hre i).choose⟩
      · simpa only [ha k] using hs
      · simpa only [hb k] using ht
  choose length path site first last start finish injectiveEdges injectiveSite siteMem
    using chooseArm
  have outside (k : Fin 3) (i : Fin (length k)) : site k i ≠ u ∧ site k i ≠ v :=
    ⟨fun h => (havoid k).1 (h ▸ siteMem k i), fun h => (havoid k).2 (h ▸ siteMem k i)⟩
  have contained (k : Fin 3) (i : Fin (length k + 1)) (tag : Bool) :
      let w := Dart.vertex (G := G) ((path k i).1, tag)
      w = u ∨ w = v ∨ w ∈ S k := by
    let d : Dart G := ((path k i).1, tag)
    change d.vertex = u ∨ d.vertex = v ∨ d.vertex ∈ S k
    rcases Dart.eq_or_eq_reverse_of_edge_eq (d := d) (e := path k i) rfl with hd | hd
    · rw [hd, start]
      exact Fin.cases (Or.inl rfl) (fun j => Or.inr (Or.inr (siteMem k j))) i
    · rw [hd, finish]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.lastCases_last]
        exact Or.inr (Or.inl rfl)
      · rw [Fin.lastCases_castSucc]
        exact Or.inr (Or.inr (siteMem k j))
  have sharedFirst {k l : Fin 3} (hkl : k ≠ l) (i : Fin (length k + 1))
      (j : Fin (length l + 1)) (he : (path k i).1 = (path l j).1) : i = 0 := by
    revert he
    refine Fin.cases (fun _ => rfl) (fun t he => ?_) i
    have hs : (path k t.succ).vertex = site k t := start k t.succ
    have hm := contained l j (path k t.succ).2
    change Dart.vertex (G := G) ((path l j).1, (path k t.succ).2) = u ∨
      Dart.vertex (G := G) ((path l j).1, (path k t.succ).2) = v ∨
      Dart.vertex (G := G) ((path l j).1, (path k t.succ).2) ∈ S l at hm
    rw [← he] at hm
    change (path k t.succ).vertex = u ∨ (path k t.succ).vertex = v ∨
      (path k t.succ).vertex ∈ S l at hm
    rw [hs] at hm
    rcases hm with hm | hm | hm
    · exact ((outside k t).1 hm).elim
    · exact ((outside k t).2 hm).elim
    · exact (Set.disjoint_left.mp (hdisjoint hkl) (siteMem k t) hm).elim
  have edgeNe {k l : Fin 3} (hkl : k ≠ l) (i : Fin (length k + 1)) (j : Fin (length l + 1)) :
      (path k i).1 ≠ (path l j).1 := by
    intro he
    have hi := sharedFirst hkl i j he
    have hj := sharedFirst hkl.symm j i he.symm
    rw [hi, hj, first, first] at he
    exact hkl (haInj he)
  have allEdges : Function.Injective (fun p : (k : Fin 3) × Fin (length k + 1) =>
      (path p.1 p.2).1) := by
    rintro ⟨k, i⟩ ⟨l, j⟩ he
    change (path k i).1 = (path l j).1 at he
    by_cases hkl : k = l
    · subst l
      obtain rfl := injectiveEdges k he
      rfl
    · exact (edgeNe hkl i j he).elim
  have allSites : Function.Injective (fun p : (k : Fin 3) × Fin (length k) =>
      site p.1 p.2) := by
    rintro ⟨k, i⟩ ⟨l, j⟩ he
    change site k i = site l j at he
    by_cases hkl : k = l
    · subst l
      obtain rfl := injectiveSite k he
      rfl
    · exact (Set.disjoint_left.mp (hdisjoint hkl) (siteMem k i) (he.symm ▸ siteMem l j)).elim
  have even (k l : Fin 3) (hkl : k ≠ l) (i : Fin (length k + 1)) (j : Fin (length l + 1)) :
      (D.route (path k i).1).intersectionParity (D.route (path l j).1) = false := by
    apply heven _ _ (edgeNe hkl i j)
    by_cases hIndependent : ∀ t s : Bool,
        Dart.vertex (G := G) ((path k i).1, t) ≠ Dart.vertex (G := G) ((path l j).1, s)
    · exact Or.inl hIndependent
    · push Not at hIndependent
      obtain ⟨t, s, he⟩ := hIndependent
      refine Or.inr ⟨t, s, he, ?_⟩
      rcases contained k i t with h | h | h
      · exact h ▸ hu
      · exact h ▸ hv
      · rcases contained l j s with h' | h' | h'
        · exact (he.trans h') ▸ hu
        · exact (he.trans h') ▸ hv
        · exact (Set.disjoint_left.mp (hdisjoint hkl) h (he.symm ▸ h')).elim
  simpa only [first, last] using
    hD.opposite_three_path_orders hsimple hR hG huv path site start finish allSites outside
      allEdges even

end Cslib.Complexity.Graph.PolygonalDrawing
