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
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.VecNotation

/-!
# Three choices through a separating pair

The prescribed darts into three disjoint vertex sets determine opposite cyclic orders
at two marked ends. The connecting paths are extracted inside the sets. A direct edge
between the two ends can take the place of any such path.
`HasRegularContacts.rotationDistance_lt_iff_of_separating_components` gives reversed rank
comparisons for an arbitrary family of component and direct-edge representatives.
Sorting a finite list of the other choices at either end therefore gives opposite lists
when both ranks are measured from the same reference choice.
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

/-- From a common reference choice, the ranks of different separating components are reversed
at the two marked vertices. A choice is either a component of the graph with the two vertices
deleted, represented by darts entering it at both ends, or one indexed direct edge. The result
applies to any representatives of the stated choices. -/
theorem HasRegularContacts.rotationDistance_lt_iff_of_separating_components {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {marked : ℕ → Prop}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple) (hR : D.Realizes r)
    (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.vertices) (heven : D.EvenCrossings marked)
    {u : ℕ} (v : {w : ℕ // w ≠ u}) (hu : marked u) (hv : marked v.val)
    {ι : Type*} (a b : ι → Dart G) (ha : ∀ k, (a k).vertex = u)
    (hb : ∀ k, (b k).vertex = v.val) (haInj : Function.Injective fun k => (a k).1)
    (component : ι → Option
      ((G.toSimpleGraph.induce {w | w ≠ u}).induce {w | w ≠ v}).ConnectedComponent)
    (hcomponents : ∀ ⦃i j C⦄, component i = some C → component j = some C → i = j)
    (hports : ∀ k, match component k with
      | none => b k = (a k).reverse
      | some C => (a k).reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp) ∧
          (b k).reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp))
    {o i j : ι} (hoi : o ≠ i) (hoj : o ≠ j) :
    r.rotationDistance (a o) (a i) < r.rotationDistance (a o) (a j) ↔
      r.rotationDistance (b o) (b j) < r.rotationDistance (b o) (b i) := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  let K := (G.toSimpleGraph.induce {w | w ≠ u}).induce {w | w ≠ v}
  let projection : K →g G.toSimpleGraph := ⟨fun w => w.val.val, fun h => h⟩
  let S (k : ι) : Set ℕ := (component k).elim ∅ (fun C => projection '' C.supp)
  have avoid (k : ι) : u ∉ S k ∧ v.val ∉ S k := by
    cases hc : component k with
    | none => simp [S, hc]
    | some C =>
      simp only [S, hc, Option.elim_some]
      exact ⟨fun ⟨w, _, he⟩ => w.val.property he, fun ⟨w, _, he⟩ => w.property (Subtype.ext he)⟩
  have disjoint : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro x y hxy
    cases hc : component x with
    | none => simp [S, hc]
    | some C =>
      cases he : component y with
      | none => simp [S, he]
      | some E =>
        have hCE : C ≠ E := fun h => hxy (hcomponents hc (h.symm ▸ he))
        have hCE' := SimpleGraph.pairwise_disjoint_supp_connectedComponent K hCE
        simp only [S, hc, he, Option.elim_some, Set.disjoint_left]
        rintro w ⟨p, hp, rfl⟩ ⟨q, hq, hw⟩
        have hpq : q = p := Subtype.ext (Subtype.ext hw)
        exact Set.disjoint_left.mp hCE' hp (hpq ▸ hq)
  have paths (k : ι) : b k = (a k).reverse ∨
      ∃ (ha' : (a k).reverse.vertex ∈ S k) (hb' : (b k).reverse.vertex ∈ S k),
        (G.toSimpleGraph.induce (S k)).Reachable
          ⟨(a k).reverse.vertex, ha'⟩ ⟨(b k).reverse.vertex, hb'⟩ := by
    have hp := hports k
    cases hc : component k with
    | none =>
      rw [hc] at hp
      exact Or.inl hp
    | some C =>
      rw [hc] at hp
      have hs : S k = projection '' C.supp := by simp only [S, hc, Option.elim_some]
      have hmem : (a k).reverse.vertex ∈ projection '' C.supp ∧
          (b k).reverse.vertex ∈ projection '' C.supp := by
        change (a k).reverse.vertex ∈ (fun w => w.val.val) '' C.supp ∧
          (b k).reverse.vertex ∈ (fun w => w.val.val) '' C.supp
        simpa only [Set.image_image] using hp
      right
      rw [hs]
      exact ⟨hmem.1, hmem.2, C.reachable_induce_image projection hmem.1 hmem.2⟩
  have aNe {x y : ι} (hxy : x ≠ y) : a x ≠ a y :=
    fun he => hxy (haInj (congrArg Prod.fst he))
  have bNe {x y : ι} (hxy : x ≠ y) : b x ≠ b y := by
    intro he
    have shared := congrArg (fun d : Dart G => d.reverse.vertex) he
    rcases paths x with hx | ⟨_, hx, _⟩ <;> rcases paths y with hy | ⟨_, hy, _⟩
    · have hrev := congrArg Dart.reverse (hx.symm.trans (he.trans hy))
      exact aNe hxy (by simpa only [Dart.reverse_reverse] using hrev)
    · rw [hx, Dart.reverse_reverse, ha] at shared
      exact (avoid y).1 (shared.symm ▸ hy)
    · rw [hy, Dart.reverse_reverse, ha] at shared
      exact (avoid x).1 (shared ▸ hx)
    · exact Set.disjoint_left.mp (disjoint hxy) hx (shared.symm ▸ hy)
  let triple : Fin 3 → ι := ![o, i, j]
  have htriple : Function.Injective triple := by
    intro x y he
    fin_cases x <;> fin_cases y <;> dsimp [triple] at he
    all_goals first | rfl | exact absurd he ‹_› | exact absurd he.symm ‹_›
  have compare :
      a i ∈ r.rotationInterval (a o) (a j) ↔ b i ∉ r.rotationInterval (b o) (b j) :=
    hD.opposite_orders_of_induced_reachable hsimple hR hG heven (Ne.symm v.property) hu hv
      (a ∘ triple) (b ∘ triple) (fun k => ha (triple k)) (fun k => hb (triple k))
      (haInj.comp htriple) (S ∘ triple) (fun _ _ h => disjoint (htriple.ne h))
      (fun k => avoid (triple k)) (fun k => paths (triple k))
  rw [r.mem_rotationInterval_iff_lt_distance _ _ _ ((ha o).trans (ha i).symm)
      ((ha o).trans (ha j).symm) (aNe hoi) (aNe hij) (aNe hoj),
    r.mem_rotationInterval_iff_lt_distance _ _ _ ((hb o).trans (hb i).symm)
      ((hb o).trans (hb j).symm) (bNe hoi) (bNe hij) (bNe hoj)] at compare
  have rankNe : r.rotationDistance (b o) (b i) ≠ r.rotationDistance (b o) (b j) :=
    fun he => bNe hij ((r.rotationDistance_eq_iff_eq _ _ _ ((hb o).trans (hb i).symm)
      ((hb o).trans (hb j).symm)).mp he)
  exact compare.trans (by omega)

/-- Sorting separating pieces from a common reference piece at the two marked ends
gives opposite lists. Each piece is represented at both ends by actual incident darts,
and the reference piece is omitted from the list being sorted. Direct indexed edges
participate in the same order as pieces with an interior component. -/
theorem HasRegularContacts.mergeSort_eq_reverse_of_separating_components {G : Graph}
    {D : PolygonalDrawing G} {r : RotationSystem G} {marked : ℕ → Prop}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple) (hR : D.Realizes r)
    (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.vertices) (heven : D.EvenCrossings marked)
    {u : ℕ} (v : {w : ℕ // w ≠ u}) (hu : marked u) (hv : marked v.val)
    {ι : Type*} (a b : ι → Dart G) (ha : ∀ k, (a k).vertex = u)
    (hb : ∀ k, (b k).vertex = v.val) (haInj : Function.Injective fun k => (a k).1)
    (component : ι → Option
      ((G.toSimpleGraph.induce {w | w ≠ u}).induce {w | w ≠ v}).ConnectedComponent)
    (hcomponents : ∀ ⦃i j C⦄, component i = some C → component j = some C → i = j)
    (hports : ∀ k, match component k with
      | none => b k = (a k).reverse
      | some C => (a k).reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp) ∧
          (b k).reverse.vertex ∈ Subtype.val '' (Subtype.val '' C.supp))
    (o : ι) (pieces : List ι) (ho : o ∉ pieces) :
    let fromA (k : ι) := r.rotationDistance (a o) (a k)
    let fromB (k : ι) := r.rotationDistance (b o) (b k)
    pieces.mergeSort (fun i j => decide (fromB i ≤ fromB j)) =
      (pieces.mergeSort (fun i j => decide (fromA i ≤ fromA j))).reverse := by
  dsimp only
  let fromA (k : ι) := r.rotationDistance (a o) (a k)
  let fromB (k : ι) := r.rotationDistance (b o) (b k)
  let order (rank : ι → ℕ) := pieces.mergeSort (fun i j => decide (rank i ≤ rank j))
  have hperm (rank : ι → ℕ) : (order rank).Perm pieces := List.mergeSort_perm _ _
  have sorted (rank : ι → ℕ) : (order rank).Pairwise (fun i j => rank i ≤ rank j) := by
    have hs := List.pairwise_mergeSort (le := fun i j => decide (rank i ≤ rank j))
      (fun i j k hij hjk => by
        simp only [decide_eq_true_eq] at hij hjk ⊢
        exact hij.trans hjk)
      (fun i j => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) pieces
    exact hs.imp (fun he => of_decide_eq_true he)
  have reverseLE {i j : ι} (hi : i ∈ pieces) (hj : j ∈ pieces) :
      fromA i ≤ fromA j ↔ fromB j ≤ fromB i := by
    have hne {k : ι} (hk : k ∈ pieces) : o ≠ k := fun he => ho (he.symm ▸ hk)
    simpa only [fromA, fromB, not_lt] using
      not_congr (hD.rotationDistance_lt_iff_of_separating_components hsimple hR hG heven
        v hu hv a b ha hb haInj component hcomponents hports (hne hj) (hne hi))
  have revPerm : (order fromA).reverse.Perm pieces :=
    (List.reverse_perm _).trans (hperm fromA)
  have revSorted : (order fromA).reverse.Pairwise (fun i j => fromB i ≤ fromB j) := by
    rw [List.pairwise_reverse]
    exact (sorted fromA).imp_of_mem fun hi hj he =>
      (reverseLE ((hperm fromA).mem_iff.mp hi) ((hperm fromA).mem_iff.mp hj)).mp he
  change order fromB = (order fromA).reverse
  refine ((hperm fromB).trans revPerm.symm).eq_of_pairwise ?_ (sorted fromB) revSorted
  intro i j hi hj hij hji
  have hi' := (hperm fromB).mem_iff.mp hi
  have hj' := revPerm.mem_iff.mp hj
  have hEq := le_antisymm ((reverseLE hi' hj').mpr hji) ((reverseLE hj' hi').mpr hij)
  exact haInj (congrArg Prod.fst
    ((r.rotationDistance_eq_iff_eq _ _ _ ((ha o).trans (ha i).symm)
      ((ha o).trans (ha j).symm)).mp hEq))

end Cslib.Complexity.Graph.PolygonalDrawing
