/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
public import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import CslibFrontier.Foundations.GroupTheory.Perm.Doubled
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rotations from enumerated vertex fibers

An enumeration of each vertex's actual dart fiber determines its cyclic successor. Empty
fibers require no chosen dart, and both ends of a loop remain separate. The directed intervals
of this rotation are the cyclic order of the enumeration indices. This constructor is used to
recover the rotation of a polygonal embedding from its clockwise germ directions.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph}

private def fiberNext
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v})) (d : Dart G) : Dart G :=
  ((rank d.vertex).symm (finRotate _ (rank d.vertex ⟨d, rfl⟩))).val

private theorem fiberNext_at
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v}))
    (v : ℕ) (d : {d : Dart G // d.vertex = v}) :
    fiberNext rank d.val = ((rank v).symm (finRotate _ (rank v d))).val := by
  rcases d with ⟨d, rfl⟩
  rfl

private theorem vertex_fiberNext
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v})) (d : Dart G) :
    (fiberNext rank d).vertex = d.vertex :=
  ((rank d.vertex).symm (finRotate _ (rank d.vertex ⟨d, rfl⟩))).property

private theorem fiberNext_bijective
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v})) :
    Function.Bijective (fiberNext rank) := by
  constructor
  · intro a b h
    have hv : b.vertex = a.vertex :=
      (vertex_fiberNext rank b).symm.trans
        ((congrArg Dart.vertex h).symm.trans (vertex_fiberNext rank a))
    let a' : {d : Dart G // d.vertex = a.vertex} := ⟨a, rfl⟩
    let b' : {d : Dart G // d.vertex = a.vertex} := ⟨b, hv⟩
    have hh : ((rank a.vertex).symm (finRotate _ (rank a.vertex a'))).val =
        ((rank a.vertex).symm (finRotate _ (rank a.vertex b'))).val := by
      rw [← fiberNext_at rank a.vertex a', ← fiberNext_at rank a.vertex b']
      exact h
    exact congrArg Subtype.val ((rank a.vertex).injective
      ((finRotate _).injective ((rank a.vertex).symm.injective (Subtype.ext hh))))
  · intro b
    let a := (rank b.vertex).symm ((finRotate _).symm (rank b.vertex ⟨b, rfl⟩))
    refine ⟨a.val, ?_⟩
    rw [fiberNext_at rank b.vertex a]
    simp only [a, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Turn each enumeration of a vertex's full dart fiber into one cyclic rotation. -/
noncomputable def ofFiberEquiv
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v})) : RotationSystem G where
  rotate := Equiv.ofBijective (fiberNext rank) (fiberNext_bijective rank)
  sameCycle_iff a b := by
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      have hv (k : ℕ) : ((Equiv.ofBijective (fiberNext rank)
          (fiberNext_bijective rank) ^ k) a).vertex = a.vertex := by
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact (vertex_fiberNext rank _).trans ih
      have hvertex := hv n
      rw [hn] at hvertex
      exact hvertex.symm
    · intro hab
      let f : Fin (Fintype.card {d : Dart G // d.vertex = a.vertex}) → Dart G :=
        fun i => ((rank a.vertex).symm i).val
      have hs : Function.Semiconj f (finRotate _)
          (Equiv.ofBijective (fiberNext rank) (fiberNext_bijective rank)) := by
        intro i
        change ((rank a.vertex).symm (finRotate _ i)).val =
          fiberNext rank ((rank a.vertex).symm i).val
        rw [fiberNext_at rank a.vertex ((rank a.vertex).symm i)]
        simp only [Equiv.apply_symm_apply]
      have h := (Equiv.Perm.sameCycle_finRotate
        (rank a.vertex ⟨a, rfl⟩) (rank a.vertex ⟨b, hab.symm⟩)).map_of_semiconj hs
      simpa only [f, Equiv.symm_apply_apply] using h

/-- The successor follows the supplied fiber enumeration, including its wraparound. -/
theorem rotate_ofFiberEquiv
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v}))
    (v : ℕ) (d : {d : Dart G // d.vertex = v}) :
    (ofFiberEquiv rank).rotate d.val =
      ((rank v).symm (finRotate _ (rank v d))).val :=
  fiberNext_at rank v d

private theorem pow_ofFiberEquiv
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v}))
    (v : ℕ) (i : Fin (Fintype.card {d : Dart G // d.vertex = v})) (k : ℕ) :
    ((ofFiberEquiv rank).rotate ^ k) ((rank v).symm i).val =
      ((rank v).symm ((finRotate _ ^ k) i)).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, rotate_ofFiberEquiv,
      Equiv.apply_symm_apply, pow_succ', Equiv.Perm.mul_apply]

private theorem distance_ofFiberEquiv_zero
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v}))
    (v : ℕ) (hpos : 0 < Fintype.card {d : Dart G // d.vertex = v})
    (d : {d : Dart G // d.vertex = v}) :
    (ofFiberEquiv rank).rotationDistance ((rank v).symm ⟨0, hpos⟩).val d.val =
      (rank v d).val := by
  have hp (k : Fin (Fintype.card {d : Dart G // d.vertex = v})) :
      (finRotate _ ^ k.val) (⟨0, hpos⟩ : Fin (Fintype.card {d : Dart G // d.vertex = v})) = k := by
    rw [← (finRotate _).iterate_eq_pow, ← finCycle_eq_finRotate_iterate]
    simp only [finCycle_apply]
    apply Fin.ext
    change (0 + k.val) % Fintype.card {d : Dart G // d.vertex = v} = k.val
    simp only [zero_add, Nat.mod_eq_of_lt k.isLt]
  apply rotationDistance_eq
    (h := ((rank v).symm ⟨0, hpos⟩).property.trans d.property.symm)
  · rw [pow_ofFiberEquiv, hp, Equiv.symm_apply_apply]
  · intro k hk heq
    have heq' : ((rank v).symm ⟨k, hk.trans (rank v d).isLt⟩).val = d.val := by
      rw [pow_ofFiberEquiv, hp ⟨k, hk.trans (rank v d).isLt⟩] at heq
      exact heq
    have heq'' : (rank v).symm ⟨k, hk.trans (rank v d).isLt⟩ =
        (rank v).symm (rank v d) := by
      apply Subtype.ext
      simpa only [Equiv.symm_apply_apply] using heq'
    have hv := congrArg Fin.val ((rank v).symm.injective heq'')
    exact (Nat.ne_of_lt hk) hv

/-- Literal directed intervals agree with cyclic comparison of the supplied fiber ranks. -/
theorem mem_rotationInterval_ofFiberEquiv_iff
    (rank : ∀ v, {d : Dart G // d.vertex = v} ≃
      Fin (Fintype.card {d : Dart G // d.vertex = v}))
    (v : ℕ) (a b c : {d : Dart G // d.vertex = v})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b.val ∈ (ofFiberEquiv rank).rotationInterval a.val c.val ↔
      (rank v a < rank v b ∧ rank v b < rank v c) ∨
      (rank v b < rank v c ∧ rank v c < rank v a) ∨
      (rank v c < rank v a ∧ rank v a < rank v b) := by
  have hpos : 0 < Fintype.card {d : Dart G // d.vertex = v} :=
    Fintype.card_pos_iff.mpr ⟨a⟩
  let o := ((rank v).symm ⟨0, hpos⟩).val
  rw [(ofFiberEquiv rank).mem_rotationInterval_iff_ranks o a.val b.val c.val
    (((rank v).symm ⟨0, hpos⟩).property.trans a.property.symm)
    (((rank v).symm ⟨0, hpos⟩).property.trans b.property.symm)
    (((rank v).symm ⟨0, hpos⟩).property.trans c.property.symm)
    (fun h => hab (Subtype.ext h)) (fun h => hbc (Subtype.ext h))
    (fun h => hac (Subtype.ext h)),
    distance_ofFiberEquiv_zero rank v hpos a,
    distance_ofFiberEquiv_zero rank v hpos b,
    distance_ofFiberEquiv_zero rank v hpos c]
  rfl

end Cslib.Complexity.Graph.RotationSystem
