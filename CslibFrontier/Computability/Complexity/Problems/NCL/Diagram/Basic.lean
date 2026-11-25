/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
public import Mathlib.Data.Fintype.Sum
public import CslibFrontier.Foundations.Data.List.Equiv
import Mathlib.Data.Sum.Basic
import Mathlib.Data.List.OfFn

/-!
# Plane diagrams of constraint graphs

A diagram draws a graph from top to bottom: wires run downwards, each generator is a box with
some wires entering from above and some leaving below, and diagrams are stacked (`comp`) and
placed side by side (`tensor`). The only explicit wire crossing is `swap`. The predicate
`Cslib.Complexity.NCL.Diagram.Planar` excludes these crossings; it gives a plane drawing of the
interpreted graph only when the generators admit compatible plane drawings. Wires carry colors
(`Cslib.Complexity.NCL.Color`): the type of a diagram lists the colors of the wires on its top
and bottom boundary. The interpretation must separately respect these colors as port weights.

The constraint graph of a diagram (`Cslib.Complexity.NCL.Diagram.graph`) is defined by recursion
on its syntax, so the names of its edges and vertices are positions in the diagram rather than
numbers:

* the edges (`Cslib.Complexity.NCL.Diagram.Edge`) are the wires of the top boundary and the wires
  created below some generator (`Cslib.Complexity.NCL.Diagram.Inner`);
* the wires of the bottom boundary are given by `Cslib.Complexity.NCL.Diagram.bottom`; stacking
  identifies the bottom wires of the upper diagram with the top wires of the lower one;
* every generator `g` becomes the vertices that an interpretation
  (`Cslib.Complexity.NCL.Diagram.Interp`) gives it, on its own wires; usually a single vertex
  whose ports have the weights of the colors of its wires
  (`Cslib.Complexity.NCL.Diagram.Interp.threshold`).

Orientations follow the drawing: the bit of an edge is `true` when it points downwards. So a wire
points into the generator below it when its bit is `true`, and into the generator above it when
its bit is `false`.

## Main definitions

* `Cslib.Complexity.NCL.Color`: red and blue wires, of weights one and two.
* `Cslib.Complexity.NCL.Diagram`: diagrams over a family `Γ` of generators.
* `Cslib.Complexity.NCL.Diagram.Edge`, `Cslib.Complexity.NCL.Diagram.Vtx`,
  `Cslib.Complexity.NCL.Diagram.bottom`, `Cslib.Complexity.NCL.Diagram.graph`: the constraint
  graph of a diagram.
* `Cslib.Complexity.NCL.Diagram.Planar`: the diagram has no crossing.

## Main results

* `Cslib.Complexity.NCL.Diagram.bottom_comp`, `Cslib.Complexity.NCL.Diagram.bottom_tensor_left`,
  `Cslib.Complexity.NCL.Diagram.bottom_tensor_right`: the bottom wires of stacks and
  juxtapositions.
* `Cslib.Complexity.NCL.Diagram.bottom_injective`: distinct bottom wires are distinct edges.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

/-- The color of a wire: red edges have weight one, blue edges weight two
[HearnDemaine2005, Section 2.2]. -/
inductive Color
  | red
  | blue
  deriving @[expose] DecidableEq, Repr

/-- The weight of an edge of the given color. -/
@[expose] def Color.weight : Color → ℕ
  | .red => 1
  | .blue => 2

/-- A diagram over the generators `Γ`, from the wires `a` on top to the wires `b` below. -/
inductive Diagram (Γ : List Color → List Color → Type) : List Color → List Color → Type
  /-- One generator, with the wires `a` entering from above and the wires `b` leaving below. -/
  | gen {a b : List Color} (g : Γ a b) : Diagram Γ a b
  /-- Wires running straight down. -/
  | id (a : List Color) : Diagram Γ a a
  /-- Two wires crossing. -/
  | swap (x y : Color) : Diagram Γ [x, y] [y, x]
  /-- The first diagram above the second. -/
  | comp {a b c : List Color} : Diagram Γ a b → Diagram Γ b c → Diagram Γ a c
  /-- The first diagram to the left of the second. -/
  | tensor {a b c d : List Color} : Diagram Γ a b → Diagram Γ c d → Diagram Γ (a ++ c) (b ++ d)

namespace Diagram

variable {Γ : List Color → List Color → Type} {a b c d : List Color}

/-- The wires created inside a diagram: those leaving a generator below. -/
@[expose] def Inner : {a b : List Color} → Diagram Γ a b → Type
  | _, b, gen _ => Fin b.length
  | _, _, id _ => Empty
  | _, _, swap .. => Empty
  | _, _, comp D₁ D₂ => D₁.Inner ⊕ D₂.Inner
  | _, _, tensor D₁ D₂ => D₁.Inner ⊕ D₂.Inner

/-- The edges of a diagram: the wires of the top boundary, and those created inside. -/
abbrev Edge (D : Diagram Γ a b) : Type := Fin a.length ⊕ D.Inner

/-- The meaning of the generators: each generator is a list of vertices on its own wires, those
above (`.inl i`) and those below (`.inr j`). -/
structure Interp (Γ : List Color → List Color → Type) where
  /-- The vertices of a generator. -/
  verts : {a b : List Color} → Γ a b → List (Vertex (Fin a.length ⊕ Fin b.length))

variable (I : Interp Γ)

/-- The vertices of a diagram: those of its generators. -/
@[expose] def Vtx : {a b : List Color} → Diagram Γ a b → Type
  | _, _, gen g => Fin (I.verts g).length
  | _, _, id _ => Empty
  | _, _, swap .. => Empty
  | _, _, comp D₁ D₂ => D₁.Vtx ⊕ D₂.Vtx
  | _, _, tensor D₁ D₂ => D₁.Vtx ⊕ D₂.Vtx

variable {I}

/-- The edges of the upper part of a stack, as edges of the stack. -/
@[expose] def compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) : D₁.Edge → (comp D₁ D₂).Edge :=
  Sum.map _root_.id Sum.inl

/-- The edges of the left part of a juxtaposition, as edges of the juxtaposition. -/
@[expose]
def tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) : D₁.Edge → (tensor D₁ D₂).Edge :=
  Sum.map ((List.appendIndexEquiv a c) ∘ Sum.inl) Sum.inl

/-- The edges of the right part of a juxtaposition, as edges of the juxtaposition. -/
@[expose]
def tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) : D₂.Edge → (tensor D₁ D₂).Edge :=
  Sum.map ((List.appendIndexEquiv a c) ∘ Sum.inr) Sum.inr

/-- The edge of each wire of the bottom boundary. -/
@[expose] def bottom : {a b : List Color} → (D : Diagram Γ a b) → Fin b.length → D.Edge
  | _, _, gen _, j => .inr j
  | _, _, id _, j => .inl j
  | _, _, swap .., j => .inl j.rev
  | _, _, comp D₁ D₂, j =>
    match bottom D₂ j with
    | .inl i => compLeft D₁ D₂ (bottom D₁ i)
    | .inr e => .inr (Sum.inr e)
  | _, _, tensor D₁ D₂, j =>
    ((List.appendIndexEquiv _ _).symm j).elim (fun j => tensorLeft D₁ D₂ (bottom D₁ j))
      (fun j => tensorRight D₁ D₂ (bottom D₂ j))

/-- The edges of the lower part of a stack, as edges of the stack: its top wires are the bottom
wires of the upper part. -/
@[expose] def compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) : D₂.Edge → (comp D₁ D₂).Edge
  | .inl i => compLeft D₁ D₂ (D₁.bottom i)
  | .inr e => .inr (Sum.inr e)

/-- The vertex of a generator with the wires `a` above and `b` below: the wires above point in
when they point down, the wires below when they point up. -/
@[expose] def genVertex (a b : List Color) (need : ℕ) : Vertex (Fin a.length ⊕ Fin b.length) :=
  ⟨(List.finRange a.length).map (fun i => ⟨⟨.inl i, true⟩, (a.get i).weight⟩) ++
    (List.finRange b.length).map (fun j => ⟨⟨.inr j, false⟩, (b.get j).weight⟩), need⟩

/-- Each generator `g` is one vertex, with minimum in-flow `need g`. -/
@[expose] def Interp.threshold (need : ∀ {a b : List Color}, Γ a b → ℕ) : Interp Γ :=
  ⟨fun {a b} g => [genVertex a b (need g)]⟩

variable (I) in
/-- The constraint graph of a diagram. -/
@[expose]
def graph : {a b : List Color} → (D : Diagram Γ a b) → ConstraintGraph (D.Vtx I) D.Edge
  | _, _, gen g => fun i => (I.verts g).get i
  | _, _, id _ => Empty.elim
  | _, _, swap .. => Empty.elim
  | _, _, comp D₁ D₂ => Sum.elim (fun v => ((graph D₁) v).map (compLeft D₁ D₂))
      (fun v => ((graph D₂) v).map (compRight D₁ D₂))
  | _, _, tensor D₁ D₂ => Sum.elim (fun v => ((graph D₁) v).map (tensorLeft D₁ D₂))
      (fun v => ((graph D₂) v).map (tensorRight D₁ D₂))

/-- The diagram contains no `swap`. Geometric planarity additionally requires compatible plane
drawings of the interpreted generators; an arbitrary `Interp` need not supply them. -/
@[expose] def Planar : {a b : List Color} → Diagram Γ a b → Prop
  | _, _, gen _ => True
  | _, _, id _ => True
  | _, _, swap .. => False
  | _, _, comp D₁ D₂ => D₁.Planar ∧ D₂.Planar
  | _, _, tensor D₁ D₂ => D₁.Planar ∧ D₂.Planar

/-! ### The edges of stacks and juxtapositions -/

section Edges

variable (D₁ : Diagram Γ a b)

theorem bottom_comp (D₂ : Diagram Γ b c) (j : Fin c.length) :
    (comp D₁ D₂).bottom j = compRight D₁ D₂ (D₂.bottom j) := by
  cases h : D₂.bottom j <;> simp [bottom, compRight, h]

theorem bottom_tensor_left (D₂ : Diagram Γ c d) (j : Fin b.length) :
    (tensor D₁ D₂).bottom (List.appendIndexEquiv b d (.inl j)) =
      tensorLeft D₁ D₂ (D₁.bottom j) := by
  simp [bottom]

theorem bottom_tensor_right (D₂ : Diagram Γ c d) (j : Fin d.length) :
    (tensor D₁ D₂).bottom ((List.appendIndexEquiv b d) (.inr j)) =
      tensorRight D₁ D₂ (D₂.bottom j) := by
  simp [bottom]

theorem compLeft_injective (D₂ : Diagram Γ b c) : Function.Injective (compLeft D₁ D₂) :=
  Function.injective_id.sumMap Sum.inl_injective

theorem compLeft_ne_inr_inr (D₂ : Diagram Γ b c) (x : D₁.Edge) (e : D₂.Inner) :
    compLeft D₁ D₂ x ≠ .inr (Sum.inr e) := by
  rcases x with _ | _ <;> rintro ⟨⟩

theorem compRight_injective (D₂ : Diagram Γ b c) (h₁ : Function.Injective D₁.bottom) :
    Function.Injective (compRight D₁ D₂) := by
  rintro (i | e) (i' | e') h <;> simp only [compRight] at h
  · rw [h₁ (compLeft_injective D₁ D₂ h)]
  · exact absurd h (compLeft_ne_inr_inr D₁ D₂ _ _)
  · exact absurd h.symm (compLeft_ne_inr_inr D₁ D₂ _ _)
  · exact congrArg Sum.inr (Sum.inr_injective (Sum.inr_injective h))

theorem tensorLeft_injective (D₂ : Diagram Γ c d) : Function.Injective (tensorLeft D₁ D₂) :=
  ((List.appendIndexEquiv a c).injective.comp Sum.inl_injective).sumMap Sum.inl_injective

theorem tensorRight_injective (D₂ : Diagram Γ c d) : Function.Injective (tensorRight D₁ D₂) :=
  ((List.appendIndexEquiv a c).injective.comp Sum.inr_injective).sumMap Sum.inr_injective

theorem tensorLeft_ne_tensorRight (D₂ : Diagram Γ c d) (x : D₁.Edge) (y : D₂.Edge) :
    tensorLeft D₁ D₂ x ≠ tensorRight D₁ D₂ y := by
  rcases x with i | _ <;> rcases y with i' | _
  · intro h
    exact Sum.inl_ne_inr ((List.appendIndexEquiv a c).injective (Sum.inl.inj h))
  all_goals rintro ⟨⟩

/-- The diagram `D` with the wires `l` running down on its left and `r` on its right: one layer of
a drawing. -/
@[expose] def pad (l : List Color) (D : Diagram Γ a b) (r : List Color) :
    Diagram Γ (l ++ (a ++ r)) (l ++ (b ++ r)) :=
  (id l).tensor (D.tensor (id r))

/-- The edges of `D` as edges of the padded layer. -/
@[expose]
def padIn (l : List Color) (D : Diagram Γ a b) (r : List Color) : D.Edge → (pad l D r).Edge :=
  tensorRight (id l) (D.tensor (id r)) ∘ tensorLeft D (id r)

/-- The wire `x` crosses the wires `l` from left to right; the wires `r` run down on the right. -/
@[expose] def moveRight (x : Color) : (l r : List Color) → Diagram Γ (x :: (l ++ r)) (l ++ (x :: r))
  | [], r => id (x :: r)
  | y :: l, r => ((swap x y).tensor (id (l ++ r))).comp ((id [y]).tensor (moveRight x l r))

/-- The wire `x` crosses the wires `l` from right to left; the wires `r` run down on the right. -/
@[expose] def moveLeft : (l : List Color) → (x : Color) → (r : List Color) →
    Diagram Γ (l ++ (x :: r)) (x :: (l ++ r))
  | [], x, r => id (x :: r)
  | y :: l, x, r => ((id [y]).tensor (moveLeft l x r)).comp ((swap y x).tensor (id (l ++ r)))

end Edges

/-! ### Configurations of stacks and juxtapositions -/

section Legal

/-- A configuration of a stack is one of each part. -/
theorem legal_comp_iff (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (s : (comp D₁ D₂).Edge → Bool) :
    ((comp D₁ D₂).graph I).Legal s ↔
      (D₁.graph I).Legal (s ∘ compLeft D₁ D₂) ∧ (D₂.graph I).Legal (s ∘ compRight D₁ D₂) :=
  ConstraintGraph.legal_sumElim_map _ _ _ _ s

/-- A configuration of a juxtaposition is one of each part. -/
theorem legal_tensor_iff (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (tensor D₁ D₂).Edge → Bool) :
    ((tensor D₁ D₂).graph I).Legal s ↔
      (D₁.graph I).Legal (s ∘ tensorLeft D₁ D₂) ∧
        (D₂.graph I).Legal (s ∘ tensorRight D₁ D₂) :=
  ConstraintGraph.legal_sumElim_map _ _ _ _ s

/-- Wires alone impose no constraint. -/
theorem legal_id (a : List Color) (s : (id a : Diagram Γ a a).Edge → Bool) :
    ((id a : Diagram Γ a a).graph I).Legal s :=
  fun v => v.elim

/-- Crossing wires impose no constraint. -/
theorem legal_swap (x y : Color) (s : (swap x y : Diagram Γ _ _).Edge → Bool) :
    ((swap x y : Diagram Γ _ _).graph I).Legal s :=
  fun v => v.elim

end Legal

/-- **Distinct wires of the bottom boundary are distinct edges.** -/
theorem bottom_injective : {a b : List Color} → (D : Diagram Γ a b) → Function.Injective D.bottom
  | _, _, gen _ => Sum.inr_injective
  | _, _, id _ => Sum.inl_injective
  | _, _, swap .. => fun _ _ h => Fin.rev_injective (Sum.inl_injective h)
  | _, _, comp D₁ D₂ => fun j j' h => by
    simp only [bottom_comp] at h
    exact bottom_injective D₂ (compRight_injective D₁ D₂ (bottom_injective D₁) h)
  | _, _, tensor D₁ D₂ => fun j j' h => by
    obtain ⟨j, rfl⟩ := (List.appendIndexEquiv _ _).surjective j
    obtain ⟨j', rfl⟩ := (List.appendIndexEquiv _ _).surjective j'
    rcases j with j | j <;> rcases j' with j' | j' <;>
      simp only [bottom_tensor_left, bottom_tensor_right] at h
    · rw [bottom_injective D₁ (tensorLeft_injective D₁ D₂ h)]
    · exact absurd h (tensorLeft_ne_tensorRight D₁ D₂ _ _)
    · exact absurd h.symm (tensorLeft_ne_tensorRight D₁ D₂ _ _)
    · rw [bottom_injective D₂ (tensorRight_injective D₁ D₂ h)]

/-! ### Instances -/

instance instDecidableEqInner : {a b : List Color} → (D : Diagram Γ a b) → DecidableEq D.Inner
  | _, _, gen _ => inferInstanceAs (DecidableEq (Fin _))
  | _, _, id _ => inferInstanceAs (DecidableEq Empty)
  | _, _, swap .. => inferInstanceAs (DecidableEq Empty)
  | _, _, comp D₁ D₂ =>
    letI := instDecidableEqInner D₁
    letI := instDecidableEqInner D₂
    inferInstanceAs (DecidableEq (D₁.Inner ⊕ D₂.Inner))
  | _, _, tensor D₁ D₂ =>
    letI := instDecidableEqInner D₁
    letI := instDecidableEqInner D₂
    inferInstanceAs (DecidableEq (D₁.Inner ⊕ D₂.Inner))

instance instFintypeInner : {a b : List Color} → (D : Diagram Γ a b) → Fintype D.Inner
  | _, _, gen _ => inferInstanceAs (Fintype (Fin _))
  | _, _, id _ => inferInstanceAs (Fintype Empty)
  | _, _, swap .. => inferInstanceAs (Fintype Empty)
  | _, _, comp D₁ D₂ =>
    letI := instFintypeInner D₁
    letI := instFintypeInner D₂
    inferInstanceAs (Fintype (D₁.Inner ⊕ D₂.Inner))
  | _, _, tensor D₁ D₂ =>
    letI := instFintypeInner D₁
    letI := instFintypeInner D₂
    inferInstanceAs (Fintype (D₁.Inner ⊕ D₂.Inner))

instance instFintypeVtx : {a b : List Color} → (D : Diagram Γ a b) → Fintype (D.Vtx I)
  | _, _, gen _ => inferInstanceAs (Fintype (Fin _))
  | _, _, id _ => inferInstanceAs (Fintype Empty)
  | _, _, swap .. => inferInstanceAs (Fintype Empty)
  | _, _, comp D₁ D₂ =>
    letI := instFintypeVtx D₁
    letI := instFintypeVtx D₂
    inferInstanceAs (Fintype (D₁.Vtx I ⊕ D₂.Vtx I))
  | _, _, tensor D₁ D₂ =>
    letI := instFintypeVtx D₁
    letI := instFintypeVtx D₂
    inferInstanceAs (Fintype (D₁.Vtx I ⊕ D₂.Vtx I))

instance instDecidablePlanar : {a b : List Color} → (D : Diagram Γ a b) → Decidable D.Planar
  | _, _, gen _ => inferInstanceAs (Decidable True)
  | _, _, id _ => inferInstanceAs (Decidable True)
  | _, _, swap .. => inferInstanceAs (Decidable False)
  | _, _, comp D₁ D₂ =>
    letI := instDecidablePlanar D₁
    letI := instDecidablePlanar D₂
    inferInstanceAs (Decidable (D₁.Planar ∧ D₂.Planar))
  | _, _, tensor D₁ D₂ =>
    letI := instDecidablePlanar D₁
    letI := instDecidablePlanar D₂
    inferInstanceAs (Decidable (D₁.Planar ∧ D₂.Planar))

end Diagram

end Cslib.Complexity.NCL
