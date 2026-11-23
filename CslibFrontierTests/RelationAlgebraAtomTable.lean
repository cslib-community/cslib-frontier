/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.AtomTable
public import CslibFrontier.Foundations.RelationAlgebra.Finite
public import Cslib.Foundations.RelationAlgebra.Group
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs

/-! # Atom tables: checked instances

A table that presents an atom structure with a representable complex algebra, a table that
presents a relation algebra with no representation, and a table that presents nothing. -/

@[expose] public section

namespace Cslib.Tests.RelationAlgebraAtomTable

open Cslib.RelationAlgebra

/-! ### A yes-instance: the group of order two -/

/-- The table of the group of order two: the identity `0` and one other atom `1`, with
`1;1 = 0`. -/
def cyclicTwo : AtomTable := ⟨2, [0, 1], [0], [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]⟩

/-- The atom structure of the group of order two, with its atoms numbered. -/
def cyclicTwoStructure : AtomStructure (Fin 2) :=
  (AtomStructure.ofGroup (Multiplicative (ZMod 2))).map Multiplicative.toAdd

instance : LawfulAtomStructure cyclicTwoStructure :=
  AtomStructure.instLawfulAtomStructureMap _ _

theorem presents_cyclicTwo : cyclicTwo.Presents cyclicTwoStructure where
  conv := by decide
  id := by
    change ∀ a : Fin 2, Multiplicative.ofAdd (a : ZMod 2) = 1 ↔ a.val ∈ [0]
    decide
  cycles := by
    change ∀ a b c : Fin 2, Multiplicative.ofAdd (a : ZMod 2) * Multiplicative.ofAdd b =
      Multiplicative.ofAdd c ↔ (a.val, b.val, c.val) ∈ cyclicTwo.cycles
    decide

/-- The table of the group of order two satisfies the predicate of the representation problem, by
the Cayley representation. -/
theorem isRepresentable_cyclicTwo : cyclicTwo.IsRepresentable := by
  change ∃ A : AtomStructure (Fin 2), cyclicTwo.Presents A ∧
    ∃ _ : LawfulAtomStructure A, Representable (ComplexAlgebra A)
  have h : Representable (ComplexAlgebra
      ((AtomStructure.ofGroup (Multiplicative (ZMod 2))).map Multiplicative.toAdd)) :=
    (ComplexAlgebra.mapEquiv _ _).representable_iff.mp (ComplexAlgebra.representable_ofGroup _)
  exact ⟨cyclicTwoStructure, presents_cyclicTwo, inferInstance, h⟩

/-! ### A no-instance that presents a relation algebra

The integral relation algebra `14₃₇` with four atoms: the identity `0`, an atom `1` with converse
`2`, and a symmetric atom `3`. It is listed as not representable in
[BodirskyJahnKnauerKonecnyWinkler2026], Table 9 and Theorem 4.2, where the proof is cited to
Maddux, *Relation Algebras* (2006) (that book was not read; locator not verified). The same source
states that four is the least number of atoms of a relation algebra with no representation. The
proof here does not rely on the source: it is by Theorem 1 of [HirschHodkinson2001], and ∀ wins
the game in three rounds. -/

/-- The table of `14₃₇`. Writing `r`, `r˘`, `a` for the atoms `1`, `2`, `3`, the cycles other than
those with the identity are the Peircean transforms of `r ≤ r;r`, `r ≤ a;r`, `r ≤ r;a` and
`a ≤ r;a`. -/
def fourAtoms : AtomTable := ⟨4, [0, 2, 1, 3], [0],
  [(0, 0, 0), (0, 1, 1), (0, 2, 2), (0, 3, 3), (1, 0, 1), (1, 1, 1), (1, 2, 0), (1, 2, 1),
    (1, 2, 2), (1, 2, 3), (1, 3, 1), (1, 3, 3), (2, 0, 2), (2, 1, 0), (2, 1, 1), (2, 1, 2),
    (2, 1, 3), (2, 2, 2), (2, 3, 2), (2, 3, 3), (3, 0, 3), (3, 1, 1), (3, 1, 3), (3, 2, 2),
    (3, 2, 3), (3, 3, 0), (3, 3, 1), (3, 3, 2)]⟩

/-- The atom structure of `14₃₇`. -/
def fourAtomsStructure : AtomStructure (Fin 4) where
  conv := ![0, 2, 1, 3]
  id := {a | a.val ∈ fourAtoms.id}
  cycles := {(a, b, c) | (a.val, b.val, c.val) ∈ fourAtoms.cycles}

-- The instances deciding the laws nest five bounded quantifiers.
set_option synthInstance.maxSize 1024 in
/-- The table of `14₃₇` satisfies the laws, associativity among them. -/
instance : LawfulAtomStructure fourAtomsStructure where
  assoc {r q p s t} :=
    (by decide : ∀ r q p s t : Fin 4, (r.val, q.val, p.val) ∈ fourAtoms.cycles →
      (s.val, t.val, q.val) ∈ fourAtoms.cycles → ∃ q' : Fin 4,
        (q'.val, t.val, p.val) ∈ fourAtoms.cycles ∧ (r.val, s.val, q'.val) ∈ fourAtoms.cycles)
      r q p s t
  id_cycle_right {s r p} :=
    (by decide : ∀ s r p : Fin 4, s.val ∈ fourAtoms.id →
      (r.val, s.val, p.val) ∈ fourAtoms.cycles → p = r) s r p
  exists_id_cycle_right :=
    (by decide : ∀ r : Fin 4, ∃ s : Fin 4, s.val ∈ fourAtoms.id ∧
      (r.val, s.val, r.val) ∈ fourAtoms.cycles)
  cycle_left {r s t} :=
    (by decide : ∀ r s t : Fin 4, (r.val, s.val, t.val) ∈ fourAtoms.cycles →
      ((![0, 2, 1, 3] r : Fin 4).val, t.val, s.val) ∈ fourAtoms.cycles) r s t

theorem presents_fourAtoms : fourAtoms.Presents fourAtomsStructure where
  conv := by decide
  id _ := .rfl
  cycles _ _ _ := .rfl

/-- The table of `14₃₇` presents a relation algebra but fails the predicate of the representation
problem. In a saturated network with an edge `m → n` labelled `r`, take `p₂` with
`m → p₂ → n` labelled `r`, `a`, then `p₃` with `m → p₃ → n` labelled `a`, `a`, then `p₄` with
`m → p₄ → p₂` labelled `a`, `a`. No labels of the edges `p₂ p₃`, `n p₄`, `p₃ p₄` make all the
triangles on these five nodes cycles. -/
theorem not_isRepresentable_fourAtoms : ¬fourAtoms.IsRepresentable := by
  change ¬∃ A : AtomStructure (Fin 4), fourAtoms.Presents A ∧
    ∃ _ : LawfulAtomStructure A, Representable (ComplexAlgebra A)
  rintro ⟨A, hA, _, hrep⟩
  obtain rfl := hA.unique presents_fourAtoms
  obtain ⟨D, N, hN, m, n, hmn⟩ :=
    ((representable_complexAlgebra_iff _).mp hrep).exists_saturated (1 : Fin 4)
  have mem (x y z : Fin 4) (h : (x.val, y.val, z.val) ∈ fourAtoms.cycles) :
      (x, y, z) ∈ fourAtomsStructure.cycles := h
  obtain ⟨p₂, h₁, h₂⟩ := hN (m := m) (n := n) (by rw [hmn]; exact mem 1 3 1 (by decide))
  obtain ⟨p₃, h₃, h₄⟩ := hN (m := m) (n := n) (by rw [hmn]; exact mem 3 3 1 (by decide))
  obtain ⟨p₄, h₅, h₆⟩ := hN (m := m) (n := p₂) (by rw [h₁]; exact mem 3 3 1 (by decide))
  have key : ∀ x y z : Fin 4, ¬(((1 : Fin 4).val, y.val, (3 : Fin 4).val) ∈ fourAtoms.cycles ∧
      ((1 : Fin 4).val, x.val, (3 : Fin 4).val) ∈ fourAtoms.cycles ∧
      ((3 : Fin 4).val, x.val, (3 : Fin 4).val) ∈ fourAtoms.cycles ∧
      ((3 : Fin 4).val, (3 : Fin 4).val, y.val) ∈ fourAtoms.cycles ∧
      ((3 : Fin 4).val, z.val, y.val) ∈ fourAtoms.cycles ∧
      ((3 : Fin 4).val, z.val, (3 : Fin 4).val) ∈ fourAtoms.cycles ∧
      (x.val, z.val, (3 : Fin 4).val) ∈ fourAtoms.cycles) := by
    set_option synthInstance.maxSize 1024 in decide
  have hn₂ : N n p₂ = (3 : Fin 4) := by rw [← N.conv_label, h₂]; rfl
  have hn₃ : N n p₃ = (3 : Fin 4) := by rw [← N.conv_label, h₄]; rfl
  have h₂₄ : N p₂ p₄ = (3 : Fin 4) := by rw [← N.conv_label, h₆]; rfl
  have t₁ := N.label_mem_cycles m n p₄
  have t₂ := N.label_mem_cycles m p₂ p₃
  have t₃ := N.label_mem_cycles n p₂ p₃
  have t₄ := N.label_mem_cycles n p₂ p₄
  have t₅ := N.label_mem_cycles n p₃ p₄
  have t₆ := N.label_mem_cycles m p₃ p₄
  have t₇ := N.label_mem_cycles p₂ p₃ p₄
  rw [hmn, h₅] at t₁
  rw [h₁, h₃] at t₂
  rw [hn₂, hn₃] at t₃
  rw [hn₂, h₂₄] at t₄
  rw [hn₃] at t₅
  rw [h₃, h₅] at t₆
  rw [h₂₄] at t₇
  exact key _ _ _ ⟨t₁, t₂, t₃, t₄, t₅, t₆, t₇⟩

/-! ### A table that presents nothing -/

/-- A table whose converse list is too short presents no atom structure, so it is a no-instance
of the representation problem. -/
example : ¬(⟨1, [], [0], [(0, 0, 0)]⟩ : AtomTable).IsRepresentable := fun ⟨_, h, _⟩ =>
  nomatch h.conv (0 : Fin 1)

end Cslib.Tests.RelationAlgebraAtomTable
