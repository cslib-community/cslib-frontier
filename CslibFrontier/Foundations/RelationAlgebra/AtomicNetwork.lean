/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Cslib.Foundations.RelationAlgebra.Representation
import Mathlib.Data.Set.Finite.Basic

/-!
# Atomic networks

An atomic network labels every ordered pair of nodes with an atom so that the labels behave like
the atoms holding between the points of a representation: identity atoms label exactly the loops,
reversing an edge takes the converse, and every triangle is a cycle
[HirschHodkinson2001], Section 2.1. Networks need only the converse, the identity atoms and the
cycles, so they are defined over any `AtomStructure`, without assuming its laws
(`LawfulAtomStructure`).

A network is *saturated* when every way of placing an edge label below a product of two atoms is
witnessed by a third node. A saturated network over an atom structure defines a homomorphism from
the complex algebra to the algebra of all relations on its nodes, sending an element to the set of
edges whose labels lie in it ([HirschHodkinson1997], Lemma 4(1), (b) implies (a)). Over finitely
many atoms every homomorphism from the complex algebra to the relations on a type arises in this
way, because every pair of points then lies in the image of exactly one atom, as in the proof of
[HirschHodkinson1997], Lemma 6.

## Main definitions

* `Cslib.RelationAlgebra.AtomicNetwork`: the atomic networks over an atom structure on a type of
  nodes.
* `Cslib.RelationAlgebra.AtomicNetwork.comap`: the subnetwork induced along an embedding.
* `Cslib.RelationAlgebra.AtomicNetwork.Saturated`: every consistent triangle on an edge is
  witnessed.
* `Cslib.RelationAlgebra.AtomicNetwork.Saturated.hom`: the homomorphism of a saturated network.

## Main results

* `Cslib.RelationAlgebraHom.exists_saturated`: over finitely many atoms, a homomorphism from a
  complex algebra to the relations on a type is the homomorphism of a saturated network.

## References

* [R. Hirsch, I. Hodkinson, *Step by step — building representations in algebraic
  logic*][HirschHodkinson1997]
* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra

variable {α D D' : Type*}

/-- An atomic network over the atom structure `F` with nodes `D`: a labelling of the ordered pairs
of nodes by atoms in which the identity atoms label exactly the loops, the reverse of an edge
carries the converse atom, and every triangle is a cycle [HirschHodkinson2001], Section 2.1. The
source's networks are these with `D` finite; they are *strict*, in that only loops have identity
labels. -/
structure AtomicNetwork (F : AtomStructure α) (D : Type*) where
  /-- The atom labelling the edge from the first node to the second. -/
  label : D → D → α
  /-- The source's `h(d, e) ≤ 1' ↔ d = e`. -/
  label_mem_id {d e : D} : label d e ∈ F.id ↔ d = e
  /-- The source's `h(e, d) = h(d, e)˘`. -/
  conv_label (d e : D) : F.conv (label d e) = label e d
  /-- The source's `h(d, f) ≤ h(d, e);h(e, f)`. -/
  label_mem_cycles (d e f : D) : (label d e, label e f, label d f) ∈ F.cycles

namespace AtomicNetwork

variable {F : AtomStructure α}

instance : CoeFun (AtomicNetwork F D) fun _ => D → D → α := ⟨label⟩

@[ext]
theorem ext {N M : AtomicNetwork F D} (h : ∀ d e, N d e = M d e) : N = M := by
  cases N
  cases M
  congr
  exact funext₂ h

/-- The network induced on `D'` by an embedding of `D'` into the nodes of `N`. The subnetworks of
`N` are its images under the inclusions of subsets of nodes. -/
@[expose, simps]
def comap (N : AtomicNetwork F D) (f : D' ↪ D) : AtomicNetwork F D' where
  label d e := N (f d) (f e)
  label_mem_id := N.label_mem_id.trans f.injective.eq_iff
  conv_label _ _ := N.conv_label _ _
  label_mem_cycles _ _ _ := N.label_mem_cycles _ _ _

/-- A network is saturated when, for every edge `(m, n)` and atoms `a`, `b` whose product lies
above its label, some node `p` has `N m p = a` and `N p n = b`. This is condition (b) of
[HirschHodkinson1997], Lemma 4(1), which notes that Maddux calls such a network a *complete
labelling*; the name "saturated" is ours. -/
@[expose]
def Saturated (N : AtomicNetwork F D) : Prop :=
  ∀ ⦃m n a b⦄, (a, b, N m n) ∈ F.cycles → ∃ p, N m p = a ∧ N p n = b

/-- Saturation is preserved by renaming the nodes. -/
theorem Saturated.comap {N : AtomicNetwork F D} (h : N.Saturated) (e : D' ≃ D) :
    (N.comap e.toEmbedding).Saturated := fun m n _ _ hab =>
  let ⟨p, hp⟩ := h (m := e m) (n := e n) hab
  ⟨e.symm p, by simpa using hp⟩

variable {A : AtomStructure α} [LawfulAtomStructure A] {N : AtomicNetwork A D}

/-- The homomorphism from a complex algebra to the relations on the nodes of a saturated network:
an element is sent to the set of edges whose labels belong to it. -/
def Saturated.hom (h : N.Saturated) : RelationAlgebraHom (ComplexAlgebra A) (SetRel D D) where
  toFun x := {e | N e.1 e.2 ∈ x}
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_one' := by
    ext ⟨m, n⟩
    exact N.label_mem_id
  map_mul' x y := by
    ext ⟨m, n⟩
    constructor
    · rintro ⟨r, hr, s, hs, hrs⟩
      obtain ⟨p, rfl, rfl⟩ := h hrs
      exact ⟨p, hr, hs⟩
    · rintro ⟨p, hp, hq⟩
      exact ⟨_, hp, _, hq, N.label_mem_cycles m p n⟩
  map_star' x := by
    ext ⟨m, n⟩
    exact (ComplexAlgebra.mem_star.trans (by rw [← N.conv_label m n]) :
      N m n ∈ star x ↔ N n m ∈ x)

@[simp]
theorem Saturated.mem_hom (h : N.Saturated) {x : ComplexAlgebra A} {m n : D} :
    (m, n) ∈ h.hom x ↔ N m n ∈ x := .rfl

end AtomicNetwork

end Cslib.RelationAlgebra

namespace Cslib.RelationAlgebraHom

open RelationAlgebra

variable {α X : Type*} {A : AtomStructure α} [LawfulAtomStructure A]

/-- Over finitely many atoms, every homomorphism from a complex algebra to the algebra of all
relations on a type is the homomorphism of a saturated network on that type: each pair of points
lies in the image of exactly one atom, which labels it. -/
theorem exists_saturated [Finite α] (f : RelationAlgebraHom (ComplexAlgebra A) (SetRel X X)) :
    ∃ N : AtomicNetwork A X, N.Saturated ∧ ∀ x m n, (m, n) ∈ f x ↔ N m n ∈ x := by
  have atom (m n : X) : ∃ a, (m, n) ∈ f ⟨{a}⟩ := by
    have key (s : Set α) : (m, n) ∈ f ⟨s⟩ → ∃ a, (m, n) ∈ f ⟨{a}⟩ := by
      induction s, s.toFinite using Set.Finite.induction_on with
      | empty => exact fun h => ((map_bot f).le h).elim
      | @insert a s _ _ ih =>
        intro h
        rw [show (⟨insert a s⟩ : ComplexAlgebra A) = ⟨{a}⟩ ⊔ ⟨s⟩ from rfl, map_sup] at h
        exact h.elim (fun h => ⟨a, h⟩) ih
    exact key Set.univ ((map_top f).ge trivial)
  choose label hlabel using atom
  have mem (x : ComplexAlgebra A) (m n : X) : (m, n) ∈ f x ↔ label m n ∈ x := by
    refine ⟨fun h => by_contra fun hx => ?_, fun h => ?_⟩
    · have : (m, n) ∈ f (⟨{label m n}⟩ ⊓ x) := by
        rw [map_inf]
        exact ⟨hlabel m n, h⟩
      rw [show ⟨{label m n}⟩ ⊓ x = ⊥ from ComplexAlgebra.ext fun a =>
        ⟨fun ⟨ha, hax⟩ => hx (ha ▸ hax), False.elim⟩, map_bot] at this
      exact this
    · exact OrderHomClass.mono f (show (⟨{label m n}⟩ : ComplexAlgebra A) ≤ x from
        fun a ha => ha ▸ h) (hlabel m n)
  have mul (m n : X) (a b : α) :
      (a, b, label m n) ∈ A.cycles ↔ ∃ p, label m p = a ∧ label p n = b := by
    have := mem (⟨{a}⟩ * ⟨{b}⟩) m n
    rw [map_mul] at this
    refine Iff.trans ⟨fun h => ⟨a, rfl, b, rfl, h⟩, ?_⟩ (this.symm.trans ?_)
    · rintro ⟨_, rfl, _, rfl, h⟩
      exact h
    · exact exists_congr fun p => and_congr (mem _ m p) (mem _ p n)
  refine ⟨⟨label, fun {d e} => ?_, fun d e => ?_, fun d e g => ?_⟩, fun m n a b => (mul m n a b).mp,
    mem⟩
  · rw [← SetRel.mem_one, ← map_one f]
    exact (mem 1 d e).symm
  · have := (mem (star ⟨{label e d}⟩) d e).mp (by rw [map_star]; exact hlabel e d)
    exact ComplexAlgebra.mem_star.mp this
  · exact (mul d g _ _).mpr ⟨e, rfl, rfl⟩

end Cslib.RelationAlgebraHom
