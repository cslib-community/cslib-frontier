/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.Game
public import Cslib.Foundations.RelationAlgebra.Group
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Defs

/-! # The representation game: checked instances

An atom structure on which ∃ loses, two on which she wins (one by Theorem 1 from a representation,
one by an explicit strategy), and the shapes in which the reduction from tilings applies the
results. -/

@[expose] public section

namespace Cslib.Tests.RelationAlgebraGame

open Cslib.RelationAlgebra

/-- The atom structure with one atom, which is not an identity atom, and every triple a cycle. -/
def noIdentity : AtomStructure Unit where
  conv a := a
  id := ∅
  cycles := Set.univ

/-- ∃ cannot answer the opening move on `noIdentity`: the loops of a network need an identity
atom. -/
theorem not_hasWinningStrategy_noIdentity : ¬noIdentity.HasWinningStrategy := fun h =>
  have := h.lawful
  let ⟨_, hs, _⟩ := noIdentity.exists_id_cycle_right ()
  hs

/-- ∃ has a winning strategy on the group of order two, by Theorem 1 and the Cayley
representation. -/
theorem hasWinningStrategy_ofGroup_zmod :
    (AtomStructure.ofGroup (Multiplicative (ZMod 2))).HasWinningStrategy :=
  (representable_complexAlgebra_iff _).mp (ComplexAlgebra.representable_ofGroup _)

/-- The network with one node over the trivial group. -/
def point : AtomicNetwork (AtomStructure.ofGroup Unit) (Fin 1) where
  label _ _ := ()
  label_mem_id := by simp
  conv_label _ _ := rfl
  label_mem_cycles _ _ _ := rfl

/-- ∃ has a winning strategy on the trivial group, by an explicit strategy: she plays the network
with one node, in which every move of ∀ already has a witness. -/
theorem hasWinningStrategy_ofGroup_unit : (AtomStructure.ofGroup Unit).HasWinningStrategy :=
  .of_forall_exists_comap_castSucc (fun n => {_N | n = 1}) (fun _ => ⟨1, point, rfl, 0, 0, rfl⟩)
    fun _ _ _ i _ _ _ _ h => (h i rfl rfl).elim

/-- Theorem 1 for the instances of the undecidability theorem: atom structures on `Fin n`. -/
example {n : ℕ} (A : AtomStructure (Fin n)) [LawfulAtomStructure A] :
    Representable (ComplexAlgebra A) ↔ A.HasWinningStrategy :=
  representable_complexAlgebra_iff A

/-- A winning strategy on a finite atom structure gives a representable relation algebra, with no
law of the structure assumed. -/
example {α : Type} [Finite α] (F : AtomStructure α) (h : F.HasWinningStrategy) :
    have := h.lawful
    Representable (ComplexAlgebra F) :=
  have := h.lawful
  h.representable

/-- A representation in any universes gives a saturated network realizing each atom. -/
example {α : Type} [Finite α] {A : AtomStructure α} [LawfulAtomStructure A] {ι : Type 1}
    {β : ι → Type 2}
    (r : Representation (ComplexAlgebra A) ι β) (a : α) :
    ∃ (D : Type) (N : AtomicNetwork A D), N.Saturated ∧ ∃ m n, N m n = a :=
  r.hasWinningStrategy.exists_saturated a

end Cslib.Tests.RelationAlgebraGame
