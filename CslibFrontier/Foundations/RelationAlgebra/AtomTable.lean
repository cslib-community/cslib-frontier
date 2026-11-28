/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.AtomStructure
public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.Computability.Primrec.List
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite relation algebras as tables of atoms

A finite relation algebra is the complex algebra of its atom structure, which is given by finitely
much data: the number of atoms, the converse of each, which of them lie below the identity, and
the triples `(a, b, c)` with `c ≤ a;b`. An `AtomTable` records these as numbers and lists of
numbers, so that finite relation algebras become the instances of decision problems in the sense
of Mathlib's `ComputablePred` and many-one reducibility.

A table need not describe an atom structure: the lists may be malformed. `AtomTable.Presents`
relates a table to the atom structure it describes, of which there is at most one, and that
structure need not satisfy the laws (`LawfulAtomStructure`), associativity among them.

## Main definitions

* `Cslib.RelationAlgebra.AtomTable`: tables, coded as tuples `(size, conv, id, cycles)`.
* `Cslib.RelationAlgebra.AtomTable.Presents`: a table presents an atom structure on `Fin size`.
* `Cslib.RelationAlgebra.AtomTable.IsRepresentable`: a table presents a lawful atom structure
  whose complex algebra is representable.

## Main results

* `Cslib.RelationAlgebra.AtomTable.Presents.unique`: a table presents at most one atom structure.
* `Cslib.RelationAlgebra.AtomTable.exists_presents_equiv`: every finite relation algebra is
  isomorphic to the complex algebra of an atom structure presented by a table.
-/

public section

universe u

namespace Cslib.RelationAlgebra

/-- A finite atom table with atoms `0, …, size - 1`. -/
structure AtomTable where
  /-- The number of atoms. -/
  size : ℕ
  /-- `conv[a]` is the converse of the atom `a`. -/
  conv : List ℕ
  /-- The identity atoms. -/
  id : List ℕ
  /-- The consistent triples: `(a, b, c)` says `c ≤ a;b`. -/
  cycles : List (ℕ × ℕ × ℕ)

namespace AtomTable

/-- A table is coded as the tuple `(size, conv, id, cycles)`. -/
@[expose] def equivProd : AtomTable ≃ ℕ × List ℕ × List ℕ × List (ℕ × ℕ × ℕ) where
  toFun t := (t.size, t.conv, t.id, t.cycles)
  invFun := fun (size, conv, id, cycles) => ⟨size, conv, id, cycles⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable AtomTable := Primcodable.ofEquiv _ equivProd

/-- The table `t` presents the atom structure `A` on `Fin t.size`. -/
structure Presents (t : AtomTable) (A : AtomStructure (Fin t.size)) : Prop where
  /-- The converse of each atom is the entry of the list `conv` at its position. -/
  conv (a : Fin t.size) : t.conv[a.val]? = some (A.conv a).val
  /-- The identity atoms are those listed in `id`. -/
  id (a : Fin t.size) : a ∈ A.id ↔ a.val ∈ t.id
  /-- The cycles are the triples listed in `cycles`. -/
  cycles (a b c : Fin t.size) : (a, b, c) ∈ A.cycles ↔ (a.val, b.val, c.val) ∈ t.cycles

/-- A table presents at most one atom structure. -/
theorem Presents.unique {t : AtomTable} {A B : AtomStructure (Fin t.size)} (hA : t.Presents A)
    (hB : t.Presents B) : A = B := by
  have hconv : A.conv = B.conv := funext fun a =>
    Fin.ext (Option.some.inj ((hA.conv a).symm.trans (hB.conv a)))
  have hid : A.id = B.id := Set.ext fun a => (hA.id a).trans (hB.id a).symm
  have hcycles : A.cycles = B.cycles := Set.ext fun ⟨a, b, c⟩ =>
    (hA.cycles a b c).trans (hB.cycles a b c).symm
  cases A
  cases B
  congr

/-- The table presents a lawful atom structure whose complex algebra is representable. This is
the representation problem for finite relation algebras as a predicate on tables; a table that
presents no atom structure, or one violating the laws, is a no-instance. -/
@[expose] def IsRepresentable (t : AtomTable) : Prop :=
  ∃ A : AtomStructure (Fin t.size), t.Presents A ∧
    ∃ _ : LawfulAtomStructure A, Representable (ComplexAlgebra A)

/-- Every finite relation algebra is isomorphic to the complex algebra of an atom structure that
some table presents. Isomorphic relation algebras are both representable or both not
(`Cslib.RelationAlgebraEquiv.representable_iff`; for finite ones in different universes, by
`Cslib.RelationAlgebra.Representation.representable`), so tables cover the representation problem
for finite relation algebras. -/
theorem exists_presents_equiv (α : Type u) [RelationAlgebra α] [Finite α] :
    ∃ (t : AtomTable) (A : AtomStructure (Fin t.size)), t.Presents A ∧
      ∃ _ : LawfulAtomStructure A, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra A)) := by
  cases nonempty_fintype α
  let : CompleteAtomicRelationAlgebra α :=
    { ‹RelationAlgebra α›, Fintype.toCompleteAtomicBooleanAlgebra α with }
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {a : α // IsAtom a}
  let A := (atomStructure α).map e
  refine ⟨⟨n, List.ofFn fun a => (A.conv a).val, A.id.toFinite.toFinset.toList.map Fin.val,
    A.cycles.toFinite.toFinset.toList.map fun c => (c.1.val, c.2.1.val, c.2.2.val)⟩, A,
    ⟨fun a => by simp, fun a => ?_, fun a b c => ?_⟩, inferInstance,
    ⟨complexAlgebraEquiv.trans (ComplexAlgebra.mapEquiv _ e)⟩⟩
  · simpa using ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, h⟩ => Fin.ext h ▸ hb⟩
  · simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Prod.exists,
      Prod.mk.injEq, Fin.val_inj]
    exact ⟨fun h => ⟨a, b, c, h, rfl, rfl, rfl⟩, by rintro ⟨_, _, _, h, rfl, rfl, rfl⟩; exact h⟩

end AtomTable

end Cslib.RelationAlgebra
