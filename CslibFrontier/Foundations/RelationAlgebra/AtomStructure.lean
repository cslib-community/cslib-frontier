/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.RelationAlgebra.AtomStructure

/-!
# Renaming the atoms of an atom structure

Additions to `Cslib.Foundations.RelationAlgebra.AtomStructure`: an atom structure can be carried
along a bijection of its atoms, and the complex algebra does not change up to isomorphism.

## Main definitions

* `Cslib.RelationAlgebra.AtomStructure.map`: the atom structure with its atoms renamed along a
  bijection.
* `Cslib.RelationAlgebra.ComplexAlgebra.mapEquiv`: the isomorphism from the complex algebra of an
  atom structure to that of the renamed one.
-/

public section

namespace Cslib.RelationAlgebra

variable {α β : Type*}

/-- The atom structure obtained by renaming the atoms along a bijection. -/
@[expose, simps]
def AtomStructure.map (A : AtomStructure α) (e : α ≃ β) : AtomStructure β where
  conv b := e (A.conv (e.symm b))
  id := e.symm ⁻¹' A.id
  cycles := {(r, s, t) | (e.symm r, e.symm s, e.symm t) ∈ A.cycles}

instance AtomStructure.instLawfulAtomStructureMap (A : AtomStructure α) [LawfulAtomStructure A]
    (e : α ≃ β) : LawfulAtomStructure (A.map e) where
  assoc h₁ h₂ :=
    let ⟨q, hq₁, hq₂⟩ := A.assoc h₁ h₂
    ⟨e q, by simpa using hq₁, by simpa using hq₂⟩
  id_cycle_right hs h := e.symm.injective (A.id_cycle_right hs h)
  exists_id_cycle_right r :=
    let ⟨s, hs, h⟩ := A.exists_id_cycle_right (e.symm r)
    ⟨e s, by simpa using hs, by simpa using h⟩
  cycle_left h := by simpa using A.cycle_left h

@[simp]
theorem AtomStructure.map_map_symm (A : AtomStructure α) (e : α ≃ β) :
    (A.map e).map e.symm = A := by
  obtain ⟨conv, id, cycles⟩ := A
  simp only [AtomStructure.map, AtomStructure.mk.injEq]
  exact ⟨funext fun a => by simp, Set.ext fun a => by simp, Set.ext fun a => by simp⟩

/-- Renaming the atoms of an atom structure gives an isomorphic complex algebra. -/
def ComplexAlgebra.mapEquiv (A : AtomStructure α) [LawfulAtomStructure A] (e : α ≃ β) :
    RelationAlgebraEquiv (ComplexAlgebra A) (ComplexAlgebra (A.map e)) where
  toFun x := ⟨e.symm ⁻¹' x.carrier⟩
  invFun y := ⟨e ⁻¹' y.carrier⟩
  left_inv x := by
    ext a
    change e.symm (e a) ∈ x.carrier ↔ a ∈ x
    rw [e.symm_apply_apply, ComplexAlgebra.mem_carrier]
  right_inv y := by
    ext b
    change e (e.symm b) ∈ y.carrier ↔ b ∈ y
    rw [e.apply_symm_apply, ComplexAlgebra.mem_carrier]
  map_rel_iff' {x y} := by
    refine ⟨fun h a ha => ?_, fun h a ha => h ha⟩
    have : e.symm (e a) ∈ y.carrier :=
      h (a := e a) (show e.symm (e a) ∈ x.carrier by rwa [e.symm_apply_apply])
    rwa [e.symm_apply_apply] at this
  map_mul' x y := by
    ext c
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      exact ⟨e r, show e.symm (e r) ∈ x.carrier by rwa [e.symm_apply_apply],
        e s, show e.symm (e s) ∈ y.carrier by rwa [e.symm_apply_apply], by simpa using h⟩
    · rintro ⟨r, hr, s, hs, h⟩
      exact ⟨e.symm r, hr, e.symm s, hs, h⟩
  map_star' x := by
    ext c
    change e.symm c ∈ star x ↔ c ∈ star (_ : ComplexAlgebra (A.map e))
    simp only [ComplexAlgebra.mem_star]
    change _ ↔ e.symm (e (A.conv (e.symm c))) ∈ x
    rw [e.symm_apply_apply]

end Cslib.RelationAlgebra
