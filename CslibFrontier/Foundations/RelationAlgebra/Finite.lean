/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.Game
import Mathlib.Data.Fintype.Order

/-!
# Representability of finite relation algebras

Two consequences of Theorem 1 of [HirschHodkinson2001], that a finite relation algebra is
representable if and only if ∃ has a winning strategy in the game on its atoms. The game does not
mention universes, whereas `Representable` asks for a representation whose index and base types
lie in the universe of the algebra.

## Main results

* `Cslib.RelationAlgebra.Representation.representable`: a finite relation algebra with a
  representation whose index and base types lie in any universes is representable.
* `Cslib.RelationAlgebraEquiv.representable_iff`: isomorphic finite relation algebras, in any
  universes, are both representable or both not.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

universe u v w

namespace Cslib

open RelationAlgebra

namespace RelationAlgebra

/-- A finite relation algebra that has a representation, with index and base types in any
universes, is representable. For finite algebras this is the `representable_univ` wanted
upstream. -/
theorem Representation.representable {α : Type u} [RelationAlgebra α] [Finite α] {ι : Type v}
    {β : ι → Type w} (r : Representation α ι β) : Representable α := by
  cases nonempty_fintype α
  let : CompleteAtomicRelationAlgebra α :=
    { ‹RelationAlgebra α›, Fintype.toCompleteAtomicBooleanAlgebra α with }
  have e : RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) := complexAlgebraEquiv
  exact (representable_iff_hasWinningStrategy α).mpr (Representation.hasWinningStrategy
    ⟨r.hom.comp e.symm.toHom, r.injective.comp (EquivLike.injective e.symm)⟩)

end RelationAlgebra

/-- Isomorphic finite relation algebras are both representable or both not, whatever their
universes. -/
theorem RelationAlgebraEquiv.representable_iff {α : Type u} {β : Type v} [RelationAlgebra α]
    [RelationAlgebra β] [Finite α] (e : RelationAlgebraEquiv α β) :
    Representable α ↔ Representable β := by
  have : Finite β := .of_equiv α e
  exact ⟨fun ⟨_, _, ⟨r⟩⟩ => Representation.representable
      ⟨r.hom.comp e.symm.toHom, r.injective.comp (EquivLike.injective e.symm)⟩,
    fun ⟨_, _, ⟨r⟩⟩ => Representation.representable
      ⟨r.hom.comp e.toHom, r.injective.comp (EquivLike.injective e)⟩⟩

end Cslib
