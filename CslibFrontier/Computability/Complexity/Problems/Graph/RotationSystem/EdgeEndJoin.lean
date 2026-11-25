/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus
import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery

/-!
# Joining both ends of two edges

The two endpoint pairs of nonloop marker edges in different components can be identified
by vertex-corner swaps. The first swap joins their components and makes the two opposite
marker darts cofacial. The second identification then preserves numerical genus zero.
This supplies the two-end identification for gluing along a separator edge.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.CycleSurgery

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
  have near (d : Dart G) : (r.faceNext d.reverse).vertex = d.vertex := by
    change (r.rotate.symm d.reverse.reverse).vertex = d.vertex
    rw [Dart.reverse_reverse, ← r.vertex_rotate (r.rotate.symm d), r.rotate.apply_symm_apply]
  have hh : h.vertex = a.vertex := near a
  have hk : k.vertex = b.vertex := near b
  have hnot : ¬SameComponent G h.vertex k.vertex := by
    rwa [hh, hk]
  have h₁ : h.vertex ≠ k.vertex := by
    intro he
    apply hnot
    rw [← he]
    exact .refl (vertex_mem hG h)
  have differentFaces : ¬r.faceNext.SameCycle h k :=
    fun he => hnot (r.sameComponent_of_sameFace hG he)
  have farA : a.reverse.vertex ≠ k.vertex := by
    intro he
    exact hsep ((he.trans hk) ▸ sameComponent_reverse hG a)
  have farB : b.reverse.vertex ≠ k.vertex := hk.symm ▸ hb.symm
  have farNe : a.reverse.vertex ≠ b.reverse.vertex := by
    intro he
    exact hsep ((sameComponent_reverse hG a).trans
      (he.symm ▸ (sameComponent_reverse hG b).symm))
  have av : a'.vertex = a.reverse.vertex := by
    change (mergeDartEquiv h k a.reverse).vertex = a.reverse.vertex
    rw [vertex_mergeDartEquiv, Function.update_of_ne farA]
    rfl
  have bv : b'.vertex = b.reverse.vertex := by
    change (mergeDartEquiv h k b.reverse).vertex = b.reverse.vertex
    rw [vertex_mergeDartEquiv, Function.update_of_ne farB]
    rfl
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

end Cslib.Complexity.Graph.RotationSystem
