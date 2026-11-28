/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ConnectedEuler
public import CslibFrontier.Foundations.GroupTheory.Perm.Doubled
public import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD

/-!
# Unbounded-arity ordered incidence stars

The center has the prescribed forward cyclic order, with no degree bound. Leaves keep
singleton vertex rotations. The face permutation is a doubled inverse center cycle, so a
positive star has precisely one full dart face. A zero-arity star is the declared center
point and retains the existing conventional-face rule.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

/-- One distinct leaf per argument and one constraint center, including the arity-zero point. -/
@[expose] def starGraph (n : ℕ) : Graph :=
  ⟨List.range (n + 1), (List.finRange n).map fun i => (i.val, n)⟩

/-- Argument/end coordinates on the actual listed star. -/
@[expose] def starDartEquiv (n : ℕ) : Fin n × Bool ≃ Dart (starGraph n) :=
  Equiv.prodCongr (finCongr (by simp [starGraph])) (Equiv.refl Bool)

/-- The leaves use their own argument indices and the center has name `n`. -/
@[simp] theorem vertex_starDartEquiv {n : ℕ} (i : Fin n) (b : Bool) :
    (starDartEquiv n (i, b)).vertex = if b then n else i.val := by
  change (if b then (((List.finRange n).map fun i => (i.val, n)).getD i.val (0, 0)).2
    else (((List.finRange n).map fun i => (i.val, n)).getD i.val (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Center successor is forward argument rotation; each leaf successor is its own dart. -/
@[expose] def starRotor (n : ℕ) : Perm (Fin n × Bool) where
  toFun d := (if d.2 then finRotate n d.1 else d.1, d.2)
  invFun d := (if d.2 then (finRotate n).symm d.1 else d.1, d.2)
  left_inv := by
    rintro ⟨i, b⟩
    cases b
    · rfl
    · exact Prod.ext ((finRotate n).symm_apply_apply i) rfl
  right_inv := by
    rintro ⟨i, b⟩
    cases b
    · rfl
    · exact Prod.ext ((finRotate n).apply_symm_apply i) rfl

private theorem sameCycle_starRotor {n : ℕ} (i j : Fin n) (b c : Bool) :
    (starRotor n).SameCycle (i, b) (j, c) ↔ b = c ∧ (b = false → i = j) := by
  refine ⟨fun h => ⟨Perm.sameCycle_one.mp (h.map_of_semiconj (u := Prod.snd) (g := 1) fun _ => rfl),
    fun hf => congrArg Prod.fst (h.eq_of_left (by rw [hf]; rfl))⟩, ?_⟩
  rintro ⟨rfl, h⟩
  cases b
  · exact h rfl ▸ .rfl
  · exact (Perm.sameCycle_finRotate i j).map_of_semiconj (u := (·, true)) fun _ => rfl

/-- Actual indexed star rotation, with one vertex cycle per endpoint fiber. -/
@[expose] def starRotation (n : ℕ) : RotationSystem (starGraph n) where
  rotate := (starDartEquiv n).permCongr (starRotor n)
  sameCycle_iff d e := by
    obtain ⟨⟨i, b⟩, rfl⟩ := (starDartEquiv n).surjective d
    obtain ⟨⟨j, c⟩, rfl⟩ := (starDartEquiv n).surjective e
    rw [Perm.sameCycle_equiv_iff (starDartEquiv n) (starRotor n) _ (by intro a; simp),
      sameCycle_starRotor, vertex_starDartEquiv, vertex_starDartEquiv]
    cases b <;> cases c <;>
      simp [Fin.ext_iff, Nat.ne_of_lt i.isLt, (Nat.ne_of_lt j.isLt).symm]

/-- Reversal changes only the endpoint bit of an actual star occurrence. -/
@[simp] theorem reverse_starDartEquiv {n : ℕ} (i : Fin n) (b : Bool) :
    (starDartEquiv n (i, b)).reverse = starDartEquiv n (i, !b) := rfl

/-- The literal face step: turn back at the center, and then return along a leaf. -/
theorem faceNext_starDartEquiv {n : ℕ} (i : Fin n) (b : Bool) :
    (starRotation n).faceNext (starDartEquiv n (i, b)) =
      starDartEquiv n (if b then i else (finRotate n).symm i, !b) := by
  apply (starRotation n).rotate.injective
  change (starRotation n).rotate ((starRotation n).rotate.symm
    (starDartEquiv n (i, b)).reverse) = _
  rw [Equiv.apply_symm_apply, reverse_starDartEquiv]
  cases b
  · change starDartEquiv n (i, true) =
      starDartEquiv n (finRotate n ((finRotate n).symm i), true)
    rw [Equiv.apply_symm_apply]
  · rfl

private def starFaceEquiv (n : ℕ) : Fin n × Bool ≃ Dart (starGraph n) :=
  ({ toFun := fun d => (d.1, !d.2)
     invFun := fun d => (d.1, !d.2)
     left_inv := by rintro ⟨i, b⟩; cases b <;> rfl
     right_inv := by rintro ⟨i, b⟩; cases b <;> rfl } :
    Fin n × Bool ≃ Fin n × Bool).trans (starDartEquiv n)

private theorem starFace_semiconj (n : ℕ) :
    Function.Semiconj (starFaceEquiv n) (Perm.doubled (finRotate n).symm)
      (starRotation n).faceNext := by
  rintro ⟨i, b⟩
  cases b <;> simp [starFaceEquiv, Perm.doubled, faceNext_starDartEquiv]

/-- The full star face is one orbit, including the unary two-dart boundary walk. -/
theorem sameFace_starRotation {n : ℕ} (d e : Dart (starGraph n)) :
    (starRotation n).faceNext.SameCycle d e := by
  obtain ⟨⟨i, b⟩, rfl⟩ := (starFaceEquiv n).surjective d
  obtain ⟨⟨j, c⟩, rfl⟩ := (starFaceEquiv n).surjective e
  apply Perm.SameCycle.map_of_semiconj (starFace_semiconj n)
  exact (Perm.sameCycle_doubled _ _ _).mpr (Perm.sameCycle_finRotate i j).inv

/-- A positive star has one actual dart face; the zero star has no dart face. -/
theorem card_faces_starRotation {n : ℕ} (hn : 0 < n) :
    Nat.card (starRotation n).Face = 1 :=
  Nat.card_eq_one_iff_unique.mpr
    ⟨⟨Quotient.ind₂ fun d e => Quotient.sound (sameFace_starRotation d e)⟩,
      ⟨Quotient.mk _ (starDartEquiv n (⟨0, hn⟩, false))⟩⟩

/-- Every indexed endpoint is declared, without a bound on the arity. -/
theorem starGraph_endpoints_declared (n : ℕ) :
    ∀ v ∈ (starGraph n).incidenceVertices, v ∈ (starGraph n).vertices := by
  intro v hv
  obtain ⟨_, he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  rcases List.mem_cons.mp hv with rfl | hv
  · simpa only [starGraph, List.mem_range] using Nat.lt_succ_of_lt i.isLt
  · simp [List.mem_singleton.mp hv, starGraph]

/-- All declared star vertices lie in its center's component. -/
theorem starGraph_connected (n : ℕ) : ∀ u ∈ (starGraph n).vertices,
    ∀ v ∈ (starGraph n).vertices, Graph.RotationCertificate.SameComponent (starGraph n) u v := by
  have connect (u : ℕ) (hu : u ∈ (starGraph n).vertices) :
      Graph.RotationCertificate.SameComponent (starGraph n) u n := by
    rcases eq_or_ne u n with rfl | he
    · exact .refl (by simp [starGraph])
    · have hi : u < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (by simpa [starGraph] using hu)) he
      simpa using sameComponent_reverse (starGraph_endpoints_declared n)
        (starDartEquiv n (⟨u, hi⟩, false))
  exact fun u hu v hv => (connect u hu).trans (connect v hv).symm

/-- Ordered stars of every arity have componentwise numerical genus zero. The nullary
center is a point component; positive stars use the complete doubled face orbit. -/
theorem numericalGenusZero_starRotation (n : ℕ) : (starRotation n).NumericalGenusZero := by
  cases n with
  | zero =>
    rintro root hr
    obtain rfl : root = 0 := by simpa [starGraph] using hr
    simp [starGraph, Dart]
  | succ n =>
    rw [numericalGenusZero_iff_connected_euler (starRotation (n + 1))
      (starGraph_endpoints_declared _) (starGraph_connected _) (starDartEquiv (n + 1) (0, false)),
      card_faces_starRotation (Nat.succ_pos n)]
    simp [starGraph, List.toFinset_card_of_nodup List.nodup_range, Nat.add_assoc]

end Cslib.Complexity.Graph.RotationSystem
