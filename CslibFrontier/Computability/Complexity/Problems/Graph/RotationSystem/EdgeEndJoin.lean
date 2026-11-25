/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus
import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate

/-!
# Joining both ends of two edges

The two endpoint pairs of nonloop marker edges in different components can be identified
by vertex-corner swaps. The first swap joins their components and makes the two opposite
marker darts cofacial. The second identification then preserves numerical genus zero.
Deleting the duplicate marker then yields the actual glued rotation. Its successor is
described in the original dart coordinates by the two swaps and one possible skip.
The two rooted cyclic words at the retained marker also use the original dart coordinates.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.CycleSurgery

private theorem faceNext_reverse_vertex {G : Graph} (r : RotationSystem G) (d : Dart G) :
    (r.faceNext d.reverse).vertex = d.vertex := by
  change (r.rotate.symm d.reverse.reverse).vertex = d.vertex
  rw [Dart.reverse_reverse, ← r.vertex_rotate (r.rotate.symm d), r.rotate.apply_symm_apply]

private theorem mergeDartEquiv_reverse_vertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (a b : Dart G)
    (hb : b.vertex ≠ b.reverse.vertex) (hsep : ¬SameComponent G a.vertex b.vertex) :
    let h := r.faceNext a.reverse
    let k := r.faceNext b.reverse
    let e := mergeDartEquiv h k
    (e a.reverse).vertex = a.reverse.vertex ∧ (e b.reverse).vertex = b.reverse.vertex := by
  let h := r.faceNext a.reverse
  let k := r.faceNext b.reverse
  have unchanged (d : Dart G) (hd : d.vertex ≠ b.vertex) :
      (mergeDartEquiv h k d).vertex = d.vertex := by
    rw [vertex_mergeDartEquiv, faceNext_reverse_vertex r b, Function.update_of_ne hd]
    rfl
  exact ⟨unchanged a.reverse (fun he => hsep (he ▸ sameComponent_reverse hG a)),
    unchanged b.reverse hb.symm⟩

private theorem sameCycle_after_join_swap {α : Type} [Finite α] [DecidableEq α]
    (f : Equiv.Perm α) {x y : α} (hne : x ≠ y) (hsep : ¬f.SameCycle x y) :
    (Equiv.swap x y * f).SameCycle x y := by
  let g := Equiv.swap x y * f
  by_contra hn
  have joined := (card_orbits_swap_mul f x y hne).2 hsep
  have undo := (card_orbits_swap_mul g x y hne).2 hn
  have he : Equiv.swap x y * g = f := by simp [g, ← mul_assoc]
  change Nat.card (Quotient (Perm.SameCycle.setoid g)) + 1 =
    Nat.card (Quotient (Perm.SameCycle.setoid f)) at joined
  rw [he] at undo
  omega

/-- Identify corresponding ends of two nonloop marker edges in different components. The
first join swaps the clockwise successors immediately preceding the forward marker darts.
Their reverse darts then lie on one face, allowing the second join at those darts. Both
indexed markers remain in the result with corresponding endpoints identified, and the
constructed rotation has numerical genus zero. -/
theorem numericalGenusZero_mergeEdgeEnds {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (a b : Dart G) (ha : a.vertex ≠ a.reverse.vertex) (hb : b.vertex ≠ b.reverse.vertex)
    (hsep : ¬SameComponent G a.vertex b.vertex) :
    let h := r.faceNext a.reverse
    let k := r.faceNext b.reverse
    let e := mergeDartEquiv h k
    let a' := e a.reverse
    let b' := e b.reverse
    ∃ (h₁ : h.vertex ≠ k.vertex) (h₂ : a'.vertex ≠ b'.vertex),
      let f := e.trans (mergeDartEquiv a' b')
      ((r.mergeVertices h k h₁).mergeVertices a' b' h₂).NumericalGenusZero ∧
        (f a).vertex = (f b).vertex ∧ (f a.reverse).vertex = (f b.reverse).vertex ∧
        (f a).vertex ≠ (f a.reverse).vertex := by
  classical
  dsimp only
  let h := r.faceNext a.reverse
  let k := r.faceNext b.reverse
  let e := mergeDartEquiv h k
  let a' := e a.reverse
  let b' := e b.reverse
  have hh : h.vertex = a.vertex := faceNext_reverse_vertex r a
  have hk : k.vertex = b.vertex := faceNext_reverse_vertex r b
  have hnot : ¬SameComponent G h.vertex k.vertex := by
    rwa [hh, hk]
  have h₁ : h.vertex ≠ k.vertex := by
    intro he
    apply hnot
    rw [← he]
    exact .refl (vertex_mem hG h)
  have differentFaces : ¬r.faceNext.SameCycle h k :=
    fun he => hnot (r.sameComponent_of_sameFace hG he)
  have farNe : a.reverse.vertex ≠ b.reverse.vertex := by
    intro he
    exact hsep ((sameComponent_reverse hG a).trans
      (he.symm ▸ (sameComponent_reverse hG b).symm))
  obtain ⟨av, bv⟩ := mergeDartEquiv_reverse_vertices r hG a b hb hsep
  have h₂ : a'.vertex ≠ b'.vertex := by rwa [av, bv]
  let s := r.mergeVertices h k h₁
  let g := Equiv.swap h k * r.faceNext
  have hg : g.SameCycle h k :=
    sameCycle_after_join_swap r.faceNext (fun he => h₁ (congrArg Dart.vertex he)) differentFaces
  have semiconj : Function.Semiconj e g s.faceNext :=
    fun d => (r.faceNext_mergeVertices h k h₁ d).symm
  have fa : s.faceNext a' = e k := by
    rw [← semiconj a.reverse]
    change e (Equiv.swap h k h) = e k
    rw [Equiv.swap_apply_left]
  have fb : s.faceNext b' = e h := by
    rw [← semiconj b.reverse]
    change e (Equiv.swap h k k) = e h
    rw [Equiv.swap_apply_right]
  have cofacial : s.faceNext.SameCycle a' b' := by
    apply Equiv.Perm.sameCycle_apply_right.mp
    apply Equiv.Perm.sameCycle_apply_left.mp
    rw [fa, fb]
    exact (hg.map_of_semiconj semiconj).symm
  have genus : s.NumericalGenusZero :=
    r.numericalGenusZero_mergeVertices_of_not_sameComponent hG hr h k h₁ hnot
  have endpoint (d : Dart (mergeGraph h k)) : (mergeDartEquiv a' b' d).vertex =
      Function.update id b'.vertex a'.vertex d.vertex := vertex_mergeDartEquiv a' b' d
  refine ⟨h₁, h₂, s.numericalGenusZero_mergeVertices (mergeGraph_endpoints_declared h k hG)
    genus a' b' h₂ cofacial, ?_, ?_, ?_⟩
  · have he : (e a).vertex = (e b).vertex := by
      change (mergeDartEquiv h k a).vertex = (mergeDartEquiv h k b).vertex
      rw [vertex_mergeDartEquiv, vertex_mergeDartEquiv, ← hh, ← hk, Function.update_self,
        Function.update_of_ne h₁]
      rfl
    change (mergeDartEquiv a' b' (e a)).vertex = (mergeDartEquiv a' b' (e b)).vertex
    rw [endpoint (e a), endpoint (e b), he]
  · change (mergeDartEquiv a' b' a').vertex = (mergeDartEquiv a' b' b').vertex
    rw [endpoint a', endpoint b', Function.update_self, Function.update_of_ne h₂]
    rfl
  · have frontA : (e a).vertex = a.vertex := by
      change (mergeDartEquiv h k a).vertex = a.vertex
      rw [vertex_mergeDartEquiv, Function.update_of_ne]
      · rfl
      · exact fun he => h₁ (hh.trans he)
    have otherB : a.vertex ≠ b'.vertex := by
      rw [bv]
      exact fun he => hsep (he.symm ▸ (sameComponent_reverse hG b).symm)
    change (mergeDartEquiv a' b' (e a)).vertex ≠ (mergeDartEquiv a' b' a').vertex
    rw [endpoint (e a), endpoint a', frontA, Function.update_of_ne otherB,
      Function.update_of_ne h₂, av]
    exact ha

private theorem lifted_rotationWord_eq {G H : Graph} (s : RotationSystem H)
    (lift : Dart H ↪ Dart G) (root : Dart H) (tail : List ℕ)
    (hn : ((lift root).index :: tail).Nodup)
    (hstep : ∀ d, d.vertex = root.vertex →
      ((lift root).index :: tail).formPerm (lift d).index = (lift (s.rotate d)).index) :
    (List.range (Function.minimalPeriod s.rotate root)).map
      (fun n => (lift (s.rotate^[n] root)).index) = (lift root).index :: tail := by
  let word := (lift root).index :: tail
  have hpow (n : ℕ) :
      (word.formPerm ^ n) (lift root).index = (lift (s.rotate^[n] root)).index := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, ih, Function.iterate_succ_apply']
      apply hstep
      rw [Perm.iterate_eq_pow]
      exact (s.sameCycle_iff _ _).mp ((Perm.SameCycle.refl s.rotate root).pow_left (n := n))
  have hi : Function.Injective (fun d => (lift d).index) := fun _ _ h =>
    lift.injective ((Dart.indexEquiv G).injective (Fin.ext h))
  have hrecur (n : ℕ) : s.rotate^[n] root = root ↔ word.length ∣ n := by
    rw [← hi.eq_iff, ← hpow n, List.formPerm_pow_apply_head _ _ hn]
    have hpos : 0 < word.length := Nat.zero_lt_succ _
    have hm := Nat.mod_lt n hpos
    change word[n % word.length] = word[0] ↔ _
    rw [hn.getElem_inj_iff, Nat.dvd_iff_mod_eq_zero]
  have hlen : Function.minimalPeriod s.rotate root = word.length :=
    Nat.dvd_antisymm
      (Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ((hrecur word.length).mpr dvd_rfl))
      ((hrecur _).mp Function.iterate_minimalPeriod)
  change _ = word
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hlen]
  · intro n hn₁ hn₂
    simp only [List.getElem_map, List.getElem_range, ← hpow n]
    rw [List.formPerm_pow_apply_head _ _ hn]
    simp only [word, Nat.mod_eq_of_lt hn₂]

open Classical in
/-- Glue two nonloop marker edges from different components, retaining `a` and deleting `b`.
The graph identifies the two pairs of endpoint names and keeps the original edge list with
only the selected occurrence removed. In the original dart coordinates, the successor
swaps at the two predecessors of the forward markers and at the two reverse markers;
when the result points to a deleted end, it continues through that end. Every surviving
dart has a unique preimage in the glued rotation. The rooted words at the retained marker
list the two old tails in forward order at its first end and reversed block order at its
other end, with the direction of each tail preserved. -/
theorem exists_numericalGenusZero_glueMarkerEdges {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (a b : Dart G) (ha : a.vertex ≠ a.reverse.vertex) (hb : b.vertex ≠ b.reverse.vertex)
    (hsep : ¬SameComponent G a.vertex b.vertex) :
    let names := Function.update id b.reverse.vertex a.reverse.vertex ∘
      Function.update id b.vertex a.vertex
    let splice := r.rotate * swap (r.faceNext a.reverse) (r.faceNext b.reverse) *
      swap a.reverse b.reverse
    let word (d : Dart G) := cycleWord (ofRotation r) d.index
    ∃ (H : Graph) (s : RotationSystem H) (lift : Dart H ↪ Dart G),
      H.vertices = (G.relabel names).vertices ∧
      H.edges = (G.relabel names).edges.eraseIdx b.1.val ∧ s.NumericalGenusZero ∧
      (∀ d, d.vertex = names (lift d).vertex ∧ (lift d).2 = d.2 ∧
        (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1) ∧
      (∀ d, d ∈ Set.range lift ↔ d.1 ≠ b.1) ∧
      (∀ x y, s.rotate x = y ↔ splice (lift x) = lift y ∨
        ∃ tag, splice (lift x) = (b.1, tag) ∧ splice (b.1, tag) = lift y) ∧
      ∃ u, lift u = a ∧ lift u.reverse = a.reverse ∧
        ((List.range (Function.minimalPeriod s.rotate u)).map
          (fun i => (lift (s.rotate^[i] u)).index)) =
          a.index :: ((word a).tail ++ (word b).tail) ∧
        ((List.range (Function.minimalPeriod s.rotate u.reverse)).map
          (fun i => (lift (s.rotate^[i] u.reverse)).index)) =
          a.reverse.index :: ((word b.reverse).tail ++ (word a.reverse).tail) := by
  dsimp only
  let h := r.faceNext a.reverse
  let k := r.faceNext b.reverse
  let e := mergeDartEquiv h k
  let a' := e a.reverse
  let b' := e b.reverse
  let f := e.trans (mergeDartEquiv a' b')
  let names := Function.update id b.reverse.vertex a.reverse.vertex ∘
    Function.update id b.vertex a.vertex
  let splice := r.rotate * swap h k * swap a.reverse b.reverse
  obtain ⟨h₁, h₂, hgenus, hfront, hback, hnonloop⟩ :=
    r.numericalGenusZero_mergeEdgeEnds hG hr a b ha hb hsep
  let t := (r.mergeVertices h k h₁).mergeVertices a' b' h₂
  have hh : h.vertex = a.vertex := faceNext_reverse_vertex r a
  have hk : k.vertex = b.vertex := faceNext_reverse_vertex r b
  obtain ⟨av, bv⟩ := mergeDartEquiv_reverse_vertices r hG a b hb hsep
  have hgraph : mergeGraph a' b' = G.relabel names := by
    change (G.relabel _).relabel _ = _
    rw [show Function.update id k.vertex h.vertex = Function.update id b.vertex a.vertex from
      by rw [hh, hk], show Function.update id b'.vertex a'.vertex =
        Function.update id b.reverse.vertex a.reverse.vertex from by rw [av, bv]]
    apply Graph.ext
    · simp only [Graph.relabel, List.map_map, names]
    · simp only [Graph.relabel, List.map_map, names]
      apply List.map_congr_left
      rintro ⟨u, v⟩ -
      rfl
  have hcoords (d : Dart G) : (f d).vertex = names d.vertex := by
    change (mergeDartEquiv a' b' (e d)).vertex = _
    rw [vertex_mergeDartEquiv a' b' (e d), vertex_mergeDartEquiv h k d, av, bv, hh, hk]
    rfl
  have hswap (d : Dart G) :
      swap a' b' (e d) = e (swap a.reverse b.reverse d) :=
    (e.injective.map_swap a.reverse b.reverse d).symm
  have hrotate (d : Dart G) : t.rotate (f d) = f (splice d) := by
    change ((r.mergeVertices h k h₁).mergeVertices a' b' h₂).rotate
      (mergeDartEquiv a' b' (e d)) = mergeDartEquiv a' b' (e (splice d))
    rw [rotate_mergeVertices, permCongr_apply, symm_apply_apply, Perm.mul_apply, hswap,
      rotate_mergeVertices, permCongr_apply, symm_apply_apply]
    rfl
  have hb' : (f b).vertex ≠ (f b.reverse).vertex := by
    change (f a).vertex = (f b).vertex at hfront
    change (f a.reverse).vertex = (f b.reverse).vertex at hback
    rwa [← hfront, ← hback]
  have htag (tag : Bool) : f (b.1, tag) = ((f b).1, tag) := by cases tag <;> rfl
  have hnb : Dart.vertex (G := mergeGraph a' b') ((f b).1, false) ≠
      Dart.vertex ((f b).1, true) := by
    rw [← htag false, ← htag true]
    rcases b with ⟨i, tag⟩
    cases tag
    · exact hb'
    · exact hb'.symm
  obtain ⟨H, s, e', hV, hEdges, hz, he', hstep⟩ := t.exists_numericalGenusZero_deleteNonloopEdge
    (mergeGraph_endpoints_declared a' b' (mergeGraph_endpoints_declared h k hG))
    hgenus (f b).1 hnb
  let lift := e'.trans f.symm.toEmbedding
  have hval (d : Dart G) : (f d).1.val = d.1.val := rfl
  have hbit (d : Dart G) : (f d).2 = d.2 := rfl
  have hLift (d : Dart H) : f (lift d) = e' d := f.apply_symm_apply _
  have hIndex (d : Dart H) :
      (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1 := by
    have he := (he' d).2.2
    rw [← hLift, hval, hval] at he
    exact he
  have hEdges' : H.edges = (G.relabel names).edges.eraseIdx b.1.val := by
    have hbval := hval b
    rwa [hbval, hgraph] at hEdges
  have hSize : H.edges.length + 1 = G.edges.length := by
    have hbnd := b.1.isLt
    rw [hEdges', List.length_eraseIdx_of_lt (by simpa only [Graph.relabel, List.length_map]
      using b.1.isLt)]
    simp only [Graph.relabel, List.length_map]
    omega
  let castIndex := finCongr hSize.symm
  let removed := castIndex b.1
  have hskipIndex (d : Dart H) : castIndex (lift d).1 = removed.succAbove d.1 := by
    apply Fin.ext
    change (lift d).1.val = (removed.succAbove d.1).val
    rw [hIndex]
    by_cases hd : d.1.val < b.1.val
    · rw [ite_eq_left hd, Fin.succAbove_of_castSucc_lt _ _
        (show d.1.castSucc < removed from hd), Fin.val_castSucc]
    · rw [ite_eq_right hd, Fin.succAbove_of_le_castSucc _ _
        (show removed ≤ d.1.castSucc from Nat.le_of_not_gt hd), Fin.val_succ]
  have coords (d : Dart H) : d.vertex = names (lift d).vertex ∧ (lift d).2 = d.2 ∧
      (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1 := by
    have hc := he' d
    rw [← hLift d, hcoords, hbit] at hc
    exact ⟨hc.1.symm, hc.2.1, hIndex d⟩
  have hrange (d : Dart G) : d ∈ Set.range lift ↔ d.1 ≠ b.1 := by
    have hsurvivor : castIndex d.1 ∈ Set.range removed.succAbove ↔ d.1 ≠ b.1 := by
      rw [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact not_congr castIndex.injective.eq_iff
    rw [← hsurvivor]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (hskipIndex x).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨(j, d.2), Prod.ext (castIndex.injective ((hskipIndex (j, d.2)).trans hj)) ?_⟩
      simpa only [← hLift, hbit] using (he' (j, d.2)).2.1
  have hstep (x y : Dart H) : s.rotate x = y ↔ splice (lift x) = lift y ∨
      ∃ tag, splice (lift x) = (b.1, tag) ∧ splice (b.1, tag) = lift y := by
    have heq (d c : Dart G) : t.rotate (f d) = f c ↔ splice d = c := by
      rw [hrotate, f.injective.eq_iff]
    simpa only [← hLift, ← htag, heq] using hstep x y
  -- Each swap acts only at one of the two pairs of endpoint fibers.
  have differentEnds {x y : Dart G} (hx : SameComponent G a.vertex x.vertex)
      (hy : SameComponent G b.vertex y.vertex) : x.vertex ≠ y.vertex :=
    fun he => hsep (hx.trans (he.symm ▸ hy.symm))
  have ca := SameComponent.refl (vertex_mem hG a)
  have cb := SameComponent.refl (vertex_mem hG b)
  have car := sameComponent_reverse hG a
  have cbr := sameComponent_reverse hG b
  have hab := differentEnds ca cb
  have hab' := differentEnds ca cbr
  have ha'b := differentEnds car cb
  have ha'b' := differentEnds car cbr
  let front (d : Dart G) := d.vertex = a.vertex ∨ d.vertex = b.vertex
  let back (d : Dart G) := d.vertex = a.reverse.vertex ∨ d.vertex = b.reverse.vertex
  have disjoint (d : Dart G) (hf : front d) (hb' : back d) : False := by
    rcases hf with he | he <;> rcases hb' with hr' | hr'
    · exact ha (he.symm.trans hr')
    · exact hab' (he.symm.trans hr')
    · exact ha'b (hr'.symm.trans he)
    · exact hb (he.symm.trans hr')
  have nameFront (d : Dart G) : names d.vertex = a.vertex ↔ front d := by
    by_cases hf : d.vertex = b.vertex
    · simp [names, front, hf, hab']
    by_cases hb' : d.vertex = b.reverse.vertex
    · simp [names, front, hb', hb.symm, ha.symm, hab'.symm]
    · simp [names, front, hf, hb']
  have nameBack (d : Dart G) : names d.vertex = a.reverse.vertex ↔ back d := by
    by_cases hf : d.vertex = b.vertex
    · simp [names, back, hf, hab', ha, ha'b.symm, hb]
    by_cases hb' : d.vertex = b.reverse.vertex
    · simp [names, back, hb', hb.symm]
    · simp [names, back, hf, hb']
  have hprev (d : Dart G) : r.faceNext d.reverse = r.rotate.symm d := by
    change r.rotate.symm d.reverse.reverse = _
    rw [Dart.reverse_reverse]
  let before := r.rotate * swap (r.rotate.symm a) (r.rotate.symm b)
  let after := r.rotate * swap a.reverse b.reverse
  have hswapMem (p : Dart G → Prop) (d x y : Dart G)
      (hx : p x) (hy : p y) (hd : p d) : p (swap x y d) :=
    (Equiv.predicate_swap p x y (iff_of_true hx hy) d).mpr hd
  have hbefore (d : Dart G) (hd : front d) : splice d = before d := by
    have hda : d ≠ a.reverse := fun he => disjoint d hd (Or.inl (congrArg Dart.vertex he))
    have hdb : d ≠ b.reverse := fun he => disjoint d hd (Or.inr (congrArg Dart.vertex he))
    change (r.rotate * swap h k) (swap a.reverse b.reverse d) = _
    rw [swap_apply_of_ne_of_ne hda hdb]
    simp only [h, k, hprev, before]
  have hafter (d : Dart G) (hd : back d) : splice d = after d := by
    let e := swap a.reverse b.reverse d
    have he : back e := hswapMem back d a.reverse b.reverse (Or.inl rfl) (Or.inr rfl) hd
    have heh : e ≠ h := fun he' => disjoint e (Or.inl ((congrArg Dart.vertex he').trans hh)) he
    have hek : e ≠ k := fun he' => disjoint e (Or.inr ((congrArg Dart.vertex he').trans hk)) he
    change r.rotate (swap h k e) = r.rotate e
    rw [swap_apply_of_ne_of_ne heh hek]
  have prevVertex (d : Dart G) : (r.rotate.symm d).vertex = d.vertex :=
    (congrArg Dart.vertex (hprev d).symm).trans (faceNext_reverse_vertex r d)
  have beforeMem (d : Dart G) (hd : front d) : front (before d) := by
    change front (r.rotate (swap (r.rotate.symm a) (r.rotate.symm b) d))
    simpa only [front, r.vertex_rotate] using
      hswapMem front d (r.rotate.symm a) (r.rotate.symm b)
        (Or.inl (prevVertex a)) (Or.inr (prevVertex b)) hd
  have afterMem (d : Dart G) (hd : back d) : back (after d) := by
    change back (r.rotate (swap a.reverse b.reverse d))
    simpa only [back, r.vertex_rotate] using
      hswapMem back d a.reverse b.reverse (Or.inl rfl) (Or.inr rfl) hd
  -- The deleted edge has just one end in each pair of fibers.
  have skipAt (p : Dart G → Prop) (f : Perm (Dart G)) (cut : Dart G)
      (hcut : cut.1 = b.1) (hc : p cut) (hc' : ¬p cut.reverse)
      (hagree : ∀ d, p d → splice d = f d) (hmem : ∀ d, p d → p (f d))
      (x y : Dart H) (hx : p (lift x)) :
      s.rotate x = y ↔ f (lift x) = lift y ∨ f (lift x) = cut ∧ f cut = lift y := by
    rw [hstep, hagree _ hx]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨tag, he, ht⟩
      have he' : p (b.1, tag) := he ▸ hmem _ hx
      have ht' : (b.1, tag) = cut :=
        (Dart.eq_or_eq_reverse_of_edge_eq (d := (b.1, tag)) (e := cut) hcut.symm).resolve_right
          (fun hrev => hc' (by rw [← hrev]; exact he'))
      refine ⟨he.trans ht', ?_⟩
      rw [← hagree cut hc, ← ht']
      exact ht
    · rintro ⟨he, ht⟩
      have he' : (b.1, cut.2) = cut := Prod.ext hcut.symm rfl
      refine ⟨cut.2, he.trans he'.symm, ?_⟩
      rw [he', hagree cut hc]
      exact ht
  have survivor_ne (d : Dart H) (cut : Dart G) (hcut : cut.1 = b.1) : lift d ≠ cut :=
    fun he => (hrange (lift d)).mp ⟨d, rfl⟩ ((congrArg Prod.fst he).trans hcut)
  have ret : a.1 ≠ b.1 := by
    intro he
    have hs := Dart.eq_or_eq_reverse_of_edge_eq he
    exact hs.elim (fun he => hab (congrArg Dart.vertex he))
      (fun he => hab' (congrArg Dart.vertex he))
  obtain ⟨u, hu⟩ := (hrange a).mpr ret
  let v := u.reverse
  have hv : lift v = a.reverse := by
    rw [← hu]
    apply Prod.ext
    · apply Fin.ext
      exact (coords v).2.2.trans (coords u).2.2.symm
    · change (lift v).2 = !(lift u).2
      rw [(coords v).2.1, (coords u).2.1]
      rfl
  have uVertex : u.vertex = a.vertex :=
    (coords u).1.trans ((nameFront _).mpr (Or.inl (congrArg Dart.vertex hu)))
  have vVertex : v.vertex = a.reverse.vertex :=
    (coords v).1.trans ((nameBack _).mpr (Or.inl (congrArg Dart.vertex hv)))
  let word (d : Dart G) := cycleWord (ofRotation r) d.index
  have hc : verifyRotation G (ofRotation r) = true := verifyRotation_ofRotation r hG
  have nodupHeads (x y : Dart G) (hxy : x.vertex ≠ y.vertex) :
      (x.index :: ((word x).tail ++ (word y).tail)).Nodup ∧
      (x.index :: ((word y).tail ++ (word x).tail)).Nodup := by
    have hn : (word x ++ (word y).tail).Nodup := List.nodup_append'.mpr
      ⟨nodup_cycleWord hc x, (nodup_cycleWord hc y).sublist (List.tail_sublist _),
        List.disjoint_left.mpr fun _ hx hy =>
          List.disjoint_left.mp (disjoint_cycleWord hc x y hxy) hx (List.mem_of_mem_tail hy)⟩
    change (x.index :: ((word x).tail ++ (word y).tail)).Nodup at hn
    exact ⟨hn, (List.Perm.cons _ List.perm_append_comm).nodup_iff.mp hn⟩
  refine ⟨H, s, lift, hV.trans (congrArg Graph.vertices hgraph), hEdges', hz, coords, hrange,
    hstep, u, hu, hv, ?_, ?_⟩
  · refine (lifted_rotationWord_eq s lift u ((word a).tail ++ (word b).tail) ?_ ?_).trans ?_
    · simpa only [hu] using (nodupHeads a b hab).1
    · intro d hd
      have hfd : front (lift d) := (nameFront _).mp ((coords d).1.symm.trans (hd.trans uVertex))
      have hs := skipAt front before b rfl (Or.inr rfl)
        (fun hb' => disjoint b.reverse hb' (Or.inr rfl)) hbefore beforeMem d (s.rotate d) hfd
      rw [hu]
      exact (formPerm_cycleWord_join_skip_iff r hG a b (lift d) (lift (s.rotate d)) hab hfd
        (survivor_ne d b rfl) (survivor_ne (s.rotate d) b rfl)).1.mpr (hs.mp rfl)
    · rw [hu]
  · refine (lifted_rotationWord_eq s lift v
      ((word b.reverse).tail ++ (word a.reverse).tail) ?_ ?_).trans ?_
    · simpa only [hv] using (nodupHeads a.reverse b.reverse ha'b').2
    · intro d hd
      have hbd : back (lift d) := (nameBack _).mp ((coords d).1.symm.trans (hd.trans vVertex))
      have hs := skipAt back after b.reverse rfl (Or.inr rfl)
        (fun hb' => disjoint b (Or.inr rfl) (by simpa only [Dart.reverse_reverse] using hb'))
        hafter afterMem d (s.rotate d) hbd
      rw [hv]
      exact (formPerm_cycleWord_join_skip_iff r hG a.reverse b.reverse (lift d)
        (lift (s.rotate d)) ha'b' hbd (survivor_ne d b.reverse rfl)
        (survivor_ne (s.rotate d) b.reverse rfl)).2.mpr (hs.mp rfl)
    · rw [hv]

end Cslib.Complexity.Graph.RotationSystem
