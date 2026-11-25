/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Replacement
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Incidence
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# Open diagrams on shared graph edges

An injective map names a cell's boundary ports by edges of the ambient graph. Its implementation
uses the same names at the boundary and gives its private wires fresh names.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Replacement.Inner`: private implementation wires.
* `Cslib.Complexity.NCL.Diagram.Replacement.graph`: the implementation on ambient edge names.

## Main results

* `Cslib.Complexity.NCL.Diagram.Replacement.label_injective`: boundary identifications do not
  identify two wires of one implementation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.Diagram.Replacement

open scoped BigOperators

variable {a b : List Color} {g : Prim a b} {H : Diagram Prim a b}
variable {E : Type*} (S : OpenSim Prim.interp Prim.interp (gen g) H)

/-- Wires outside the source cell's boundary. -/
abbrev Inner := {e : H.Edge // e ∉ Set.range S.ι}

/-- Find the boundary occurrence of an implementation wire by scanning its finite port list. -/
@[expose] def boundaryIndex (e : H.Edge) : Option (gen g : Diagram Prim a b).Edge :=
  (boundaryList a b).find? (fun x => decide (S.ι x = e))

/-- Give boundary wires ambient names and private wires their own names. -/
@[expose] def label (p : (gen g : Diagram Prim a b).Edge → E) (e : H.Edge) : E ⊕ Inner S :=
  match h : boundaryIndex S e with
  | some x => .inl (p x)
  | none => .inr ⟨e, by
      rintro ⟨x, rfl⟩
      have hx : x ∈ boundaryList a b := by
        rcases x with i | i <;> simp [boundaryList]
      have hn := List.find?_eq_none.1 h x hx
      simp only [decide_true] at hn
      contradiction⟩

/-- The local implementation on ambient boundary names and its fresh private wires. -/
@[expose] def graph (p : (gen g : Diagram Prim a b).Edge → E) :
    ConstraintGraph (H.Vtx Prim.interp) (E ⊕ Inner S) :=
  (H.graph Prim.interp).map (label S p)

/-- Read an implementation on fixed ambient boundary and private directions. -/
@[expose] def orient (p : (gen g : Diagram Prim a b).Edge → E)
    (s : E → Bool) (x : Inner S → Bool) : H.Edge → Bool :=
  Sum.elim s x ∘ label S p

/-- Restrict an implementation orientation to its private wires. -/
@[expose] def restrict (t : H.Edge → Bool) : Inner S → Bool := t ∘ Subtype.val

/-- Agreement with the shared boundary. -/
@[expose]
def Agrees (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool) (t : H.Edge → Bool) : Prop :=
  ∀ x, t (S.ι x) = s (p x)

end Cslib.Complexity.NCL.Diagram.Replacement

end

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.Diagram.Replacement

open scoped BigOperators

variable {a b : List Color} {g : Prim a b} {H : Diagram Prim a b}
variable {E : Type*} (S : OpenSim Prim.interp Prim.interp (gen g) H)

/-- Source wires remain boundary wires of the implementation. -/
theorem boundary_ι (x : (gen g : Diagram Prim a b).Edge) : H.IsBoundary (S.ι x) := by
  rcases x with i | i
  exacts [.inl ⟨i, S.ι_top i⟩, .inr ⟨i, S.ι_bottom i⟩]

/-- An internal implementation wire has a fresh private name. -/
theorem label_private (p : (gen g : Diagram Prim a b).Edge → E) (e : Inner S) :
    label S p e = .inr e := by
  have hn : boundaryIndex S e = none :=
    List.find?_eq_none.2 fun x _ hx => e.property ⟨x, of_decide_eq_true hx⟩
  unfold label
  split
  · rename_i x hx
    cases hx.symm.trans hn
  · rfl

/-- Boundary wire names agree with the supplied ambient naming. -/
theorem label_ι (p : (gen g : Diagram Prim a b).Edge → E) (x : (gen g : Diagram Prim a b).Edge) :
    label S p (S.ι x) = .inl (p x) := by
  have hx : x ∈ boundaryList a b := by rcases x with i | i <;> simp [boundaryList]
  unfold label boundaryIndex
  split
  · rename_i y hy
    have hy' := List.find?_some hy
    exact congrArg (Sum.inl ∘ p) (S.ι_injective (of_decide_eq_true hy'))
  · rename_i hn
    exact (List.find?_eq_none.1 hn x hx (by simp)).elim

private theorem label_range (p : (gen g : Diagram Prim a b).Edge → E) {e : H.Edge}
    (he : e ∈ Set.range S.ι) : label S p e = .inl (p (Classical.choose he)) := by
  exact (congrArg (label S p) (Classical.choose_spec he).symm).trans (label_ι S p _)

/-- An injective ambient naming preserves distinct implementation wires. -/
theorem label_injective {p : (gen g : Diagram Prim a b).Edge → E} (hp : Function.Injective p) :
    Function.Injective (label S p) := by
  classical
  intro x y h
  by_cases hx : x ∈ Set.range S.ι <;> by_cases hy : y ∈ Set.range S.ι
  · rw [label_range S p hx, label_range S p hy] at h
    exact (Classical.choose_spec hx).symm.trans
      ((congrArg S.ι (hp (Sum.inl_injective h))).trans (Classical.choose_spec hy))
  · rw [label_range S p hx, label_private S p ⟨y, hy⟩] at h
    cases h
  · rw [label_private S p ⟨x, hx⟩, label_range S p hy] at h
    cases h
  · rw [label_private S p ⟨x, hx⟩, label_private S p ⟨y, hy⟩] at h
    exact congrArg Subtype.val (Sum.inr_injective h)

/-- Reading a boundary wire ignores the private orientation. -/
theorem orient_ι (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool)
    (x : Inner S → Bool) (i : (gen g : Diagram Prim a b).Edge) :
    orient S p s x (S.ι i) = s (p i) := by
  simp only [orient, Function.comp_apply, label_ι, Sum.elim_inl]

/-- Reading a private wire ignores the boundary orientation. -/
theorem orient_private (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool)
    (x : Inner S → Bool) (e : Inner S) : orient S p s x e = x e := by
  simp only [orient, Function.comp_apply, label_private, Sum.elim_inr]

/-- A boundary-compatible implementation is reconstructed from its private restriction. -/
theorem orient_restrict (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool)
    {t : H.Edge → Bool} (ht : Agrees S p s t) : orient S p s (restrict S t) = t := by
  classical
  funext e
  by_cases he : e ∈ Set.range S.ι
  · obtain ⟨x, rfl⟩ := he
    exact (orient_ι S p s _ x).trans (ht x).symm
  · exact orient_private S p s _ ⟨e, he⟩

/-- Inner paths preserve the supplied ambient boundary. -/
theorem agrees_of_innerReach (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool)
    {t u : H.Edge → Bool} (ht : Agrees S p s t) (hu : InnerReach Prim.interp H t u) :
    Agrees S p s u :=
  fun x => (InnerReach.boundary hu (boundary_ι S x)).trans (ht x)

/-- The local graph and diagram impose the same constraints on the shared/private split. -/
theorem legal_iff (p : (gen g : Diagram Prim a b).Edge → E) (s : E → Bool)
    (x : Inner S → Bool) :
    (graph S p).Legal (Sum.elim s x) ↔ (H.graph Prim.interp).Legal (orient S p s x) :=
  ConstraintGraph.legal_map (H.graph Prim.interp) (label S p) (Sum.elim s x)

/-- The private wires of a finite diagram form a finite type. -/
instance : Fintype (Inner S) := inferInstanceAs (Fintype {e : H.Edge // e ∉ Set.range S.ι})

/-- Every implementation wire is either a source boundary wire or a fresh private wire. -/
private def edgeEquiv : (gen g : Diagram Prim a b).Edge ⊕ Inner S ≃ H.Edge where
  toFun := Sum.elim S.ι Subtype.val
  invFun := label S _root_.id
  left_inv x := by
    rcases x with i | i
    · exact label_ι S _root_.id i
    · exact label_private S _root_.id i
  right_inv e := by
    classical
    by_cases he : e ∈ Set.range S.ι
    · obtain ⟨i, rfl⟩ := he
      rw [label_ι]
      rfl
    · exact congrArg (Sum.elim S.ι Subtype.val) (label_private S _root_.id ⟨e, he⟩)

/-- A sum over implementation wires splits into its boundary and private parts. -/
theorem sum_edges [Fintype (Inner S)] {M : Type*} [AddCommMonoid M] (f : H.Edge → M) :
    ∑ e, f e = (∑ i : (gen g : Diagram Prim a b).Edge, f (S.ι i)) +
      ∑ e : Inner S, f e :=
  ((edgeEquiv S).sum_comp f).symm.trans (Fintype.sum_sum_type _)

/-- Private wires are precisely the created wires that do not reach the lower boundary. -/
theorem card_inner : Fintype.card (Inner S) + b.length = H.innerCount := by
  have h := sum_edges S fun _ => (1 : ℕ)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, mul_one,
    (Fintype.card_congr H.numEquiv).trans (Fintype.card_fin _)] at h
  have hb : Fintype.card (gen g : Diagram Prim a b).Edge = a.length + b.length := by
    change Fintype.card (Fin a.length ⊕ Fin b.length) = _
    simp
  omega

end Cslib.Complexity.NCL.Diagram.Replacement
