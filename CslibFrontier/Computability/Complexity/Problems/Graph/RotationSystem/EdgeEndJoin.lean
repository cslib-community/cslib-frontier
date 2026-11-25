/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus
import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery

/-!
# Joining both ends of two edges

The two endpoint pairs of nonloop marker edges in different components can be identified
by vertex-corner swaps. The first swap joins their components and makes the two opposite
marker darts cofacial. The second identification then preserves numerical genus zero.
Deleting the duplicate marker then yields the actual glued rotation. Its successor is
described in the original dart coordinates by the two swaps and one possible skip.
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

open Classical in
/-- Glue two nonloop marker edges from different components, retaining `a` and deleting `b`.
The graph identifies the two pairs of endpoint names and keeps the original edge list with
only the selected occurrence removed. In the original dart coordinates, the successor
swaps at the two predecessors of the forward markers and at the two reverse markers;
when the result points to a deleted end, it continues through that end. Every surviving
dart has a unique preimage in the glued rotation. -/
theorem exists_numericalGenusZero_glueMarkerEdges {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (a b : Dart G) (ha : a.vertex ≠ a.reverse.vertex) (hb : b.vertex ≠ b.reverse.vertex)
    (hsep : ¬SameComponent G a.vertex b.vertex) :
    let names := Function.update id b.reverse.vertex a.reverse.vertex ∘
      Function.update id b.vertex a.vertex
    let splice := r.rotate * swap (r.faceNext a.reverse) (r.faceNext b.reverse) *
      swap a.reverse b.reverse
    ∃ (H : Graph) (s : RotationSystem H) (lift : Dart H ↪ Dart G),
      H.vertices = (G.relabel names).vertices ∧
      H.edges = (G.relabel names).edges.eraseIdx b.1.val ∧ s.NumericalGenusZero ∧
      (∀ d, d.vertex = names (lift d).vertex ∧ (lift d).2 = d.2 ∧
        (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1) ∧
      (∀ d, d ∈ Set.range lift ↔ d.1 ≠ b.1) ∧
      ∀ x y, s.rotate x = y ↔ splice (lift x) = lift y ∨
        ∃ tag, splice (lift x) = (b.1, tag) ∧ splice (b.1, tag) = lift y := by
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
  refine ⟨H, s, lift, hV.trans (congrArg Graph.vertices hgraph), hEdges', hz, ?_, ?_, ?_⟩
  · intro d
    have hc := he' d
    rw [← hLift d, hcoords, hbit] at hc
    exact ⟨hc.1.symm, hc.2.1, hIndex d⟩
  · intro d
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
  · intro x y
    have heq (d c : Dart G) : t.rotate (f d) = f c ↔ splice d = c := by
      rw [hrotate, f.injective.eq_iff]
    simpa only [← hLift, ← htag, heq] using hstep x y

end Cslib.Complexity.Graph.RotationSystem
