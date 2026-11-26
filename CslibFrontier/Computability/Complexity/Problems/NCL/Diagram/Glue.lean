/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Run

/-!
# Configurations of stacks and juxtapositions

A configuration of a stack or of a juxtaposition of diagrams is a configuration of each part, the
two agreeing on the wires they share (`Cslib.Complexity.NCL.Diagram.glueComp`,
`Cslib.Complexity.NCL.Diagram.glueTensor`). Reversing an edge of one part is reversing it in the
whole, and moves of one part that keep its boundary (`Cslib.Complexity.NCL.Diagram.InnerReach`)
are moves of the whole that keep its boundary. These are the bookkeeping lemmas behind
substitution (`Cslib.Complexity.NCL.Diagram.OpenSim`).

## Main definitions

* `Cslib.Complexity.NCL.Diagram.IsBoundary`, `Cslib.Complexity.NCL.Diagram.InnerReach`: the
  boundary of a diagram, and reachability by moves that keep it.
* `Cslib.Complexity.NCL.Diagram.glueComp`, `Cslib.Complexity.NCL.Diagram.glueTensor`: the
  configuration of a stack or a juxtaposition, part by part.

## Main results

* `Cslib.Complexity.NCL.Diagram.innerReach_glueComp_left`,
  `Cslib.Complexity.NCL.Diagram.innerReach_glueComp_right`,
  `Cslib.Complexity.NCL.Diagram.innerReach_glueTensor_left`,
  `Cslib.Complexity.NCL.Diagram.innerReach_glueTensor_right`: moves inside a part are moves
  inside the whole.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

open ConstraintGraph Relation

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color} {Label : Type*}

/-! ### The boundary and the moves inside -/

/-- The edge is a wire of the top or of the bottom boundary. -/
@[expose] def IsBoundary (D : Diagram Γ a b) (y : D.Edge) : Prop :=
  (∃ i, y = .inl i) ∨ ∃ j, y = D.bottom j

variable (I) in
/-- A move of the diagram that reverses an edge off the boundary. -/
@[expose]
def InnerStep (D : Diagram Γ a b) (t t' : D.Edge → Bool) : Prop :=
  (D.graph I).StepOn (fun e => ¬D.IsBoundary e) t t'

variable (I) in
/-- Reachability by moves that keep the boundary. -/
abbrev InnerReach (D : Diagram Γ a b) : (D.Edge → Bool) → (D.Edge → Bool) → Prop :=
  ReflTransGen (InnerStep I D)

/-! ### Gluing configurations of the parts -/

/-- The configuration of a stack with the given configurations of its parts. They must agree on
the shared wires (`Cslib.Complexity.NCL.Diagram.glueComp_compRight`). -/
@[expose] def glueComp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) : (comp D₁ D₂).Edge → Label
  | .inl i => t₁ (.inl i)
  | .inr (.inl e) => t₁ (.inr e)
  | .inr (.inr e) => t₂ (.inr e)

theorem glueComp_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) (x : D₁.Edge) : glueComp D₁ D₂ t₁ t₂ (compLeft D₁ D₂ x) = t₁ x := by
  rcases x with i | e <;> rfl

theorem glueComp_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) (h : ∀ j, t₂ (.inl j) = t₁ (D₁.bottom j)) (x : D₂.Edge) :
    glueComp D₁ D₂ t₁ t₂ (compRight D₁ D₂ x) = t₂ x := by
  rcases x with j | e
  · exact (glueComp_compLeft D₁ D₂ t₁ t₂ _).trans (h j).symm
  · rfl

theorem glueComp_eta (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t : (comp D₁ D₂).Edge → Label) :
    glueComp D₁ D₂ (t ∘ compLeft D₁ D₂) (t ∘ compRight D₁ D₂) = t := by
  funext x
  rcases x with i | e | e <;> rfl

theorem glueComp_congr_right (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Label)
    {t₂ t₂' : D₂.Edge → Label} (h : ∀ e, t₂ (.inr e) = t₂' (.inr e)) :
    glueComp D₁ D₂ t₁ t₂ = glueComp D₁ D₂ t₁ t₂' := by
  funext x
  rcases x with i | e | e <;> first | rfl | exact h e

theorem legal_glueComp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {t₁ : D₁.Edge → Bool}
    {t₂ : D₂.Edge → Bool} (h₁ : (D₁.graph I).Legal t₁) (h₂ : (D₂.graph I).Legal t₂)
    (h : ∀ j, t₂ (.inl j) = t₁ (D₁.bottom j)) :
    ((comp D₁ D₂).graph I).Legal (glueComp D₁ D₂ t₁ t₂) :=
  (legal_comp_iff _ _ _).2
    ⟨(funext (glueComp_compLeft D₁ D₂ t₁ t₂)).symm ▸ h₁,
     (funext (glueComp_compRight D₁ D₂ t₁ t₂ h)).symm ▸ h₂⟩

/-- Configurations of a stack agree when they agree on the upper part and inside the lower one. -/
private theorem comp_ext {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {t t' : (comp D₁ D₂).Edge → Bool}
    (h₁ : ∀ x, t (compLeft D₁ D₂ x) = t' (compLeft D₁ D₂ x))
    (h₂ : ∀ e, t (.inr (.inr e)) = t' (.inr (.inr e))) : t = t' := by
  funext x
  rcases x with i | e | e
  exacts [h₁ (.inl i), h₁ (.inr e), h₂ e]

theorem glueComp_reverse_left (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Bool)
    (t₂ : D₂.Edge → Bool) (y : D₁.Edge) :
    glueComp D₁ D₂ (reverse t₁ y) t₂ = reverse (glueComp D₁ D₂ t₁ t₂) (compLeft D₁ D₂ y) := by
  refine comp_ext (fun x => ?_) (fun e => ?_)
  · rw [glueComp_compLeft, reverse_apply_of_injective (compLeft_injective D₁ D₂)]
    exact congrArg (reverse · y x) (funext fun z => (glueComp_compLeft D₁ D₂ t₁ t₂ z).symm)
  · exact (reverse_of_ne (glueComp D₁ D₂ t₁ t₂) (compLeft_ne_inr_inr D₁ D₂ y e).symm).symm

theorem glueComp_reverse_right (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (t₁ : D₁.Edge → Bool)
    (t₂ : D₂.Edge → Bool) (e : D₂.Inner) :
    glueComp D₁ D₂ t₁ (reverse t₂ (.inr e)) =
      reverse (glueComp D₁ D₂ t₁ t₂) (.inr (.inr e)) := by
  refine comp_ext (fun x => ?_) (fun e' => ?_)
  · rw [glueComp_compLeft, reverse_of_ne _ (compLeft_ne_inr_inr D₁ D₂ x e), glueComp_compLeft]
  · obtain rfl | h := eq_or_ne e' e
    · simp [glueComp]
    · dsimp only [glueComp]
      rw [reverse_of_ne _ (Sum.inr_injective.ne h)]
      exact (reverse_of_ne (glueComp D₁ D₂ t₁ t₂)
        (fun hc => h (Sum.inr_injective (Sum.inr_injective hc)))).symm

/-! ### Moves inside the parts of a stack -/

/-- The parts of a stack share exactly the wires between them. -/
theorem compLeft_eq_compRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {y : D₁.Edge}
    {z : D₂.Edge} (h : compLeft D₁ D₂ y = compRight D₁ D₂ z) :
    ∃ j, z = .inl j ∧ y = D₁.bottom j := by
  rcases z with j | e
  · exact ⟨j, rfl, compLeft_injective D₁ D₂ h⟩
  · exact absurd h (compLeft_ne_inr_inr D₁ D₂ y e)

private theorem not_isBoundary_compLeft {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {y : D₁.Edge}
    (hy : ¬D₁.IsBoundary y) : ¬(comp D₁ D₂).IsBoundary (compLeft D₁ D₂ y) := by
  rintro (⟨i, h⟩ | ⟨j, h⟩)
  · exact hy (Or.inl ⟨i, compLeft_injective D₁ D₂ h⟩)
  · rw [bottom_comp] at h
    obtain ⟨k, -, rfl⟩ := compLeft_eq_compRight h
    exact hy (Or.inr ⟨k, rfl⟩)

private theorem not_isBoundary_compRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {z : D₂.Edge}
    (hz : ¬D₂.IsBoundary z) : ¬(comp D₁ D₂).IsBoundary (compRight D₁ D₂ z) := by
  rcases z with j | e
  · exact absurd (Or.inl ⟨j, rfl⟩) hz
  rintro (⟨i, h⟩ | ⟨j, h⟩)
  · injection h
  · rw [bottom_comp] at h
    exact hz (Or.inr ⟨j, compRight_injective D₁ D₂ (bottom_injective D₁) h⟩)

private theorem InnerStep.boundary {D : Diagram Γ a b} {t t' : D.Edge → Bool}
    (h : InnerStep I D t t')
    {y : D.Edge} (hy : D.IsBoundary y) : t' y = t y :=
  (ConstraintGraph.StepOn.apply_eq h (not_not_intro hy)).symm

theorem InnerReach.boundary {D : Diagram Γ a b} {t t' : D.Edge → Bool} (h : InnerReach I D t t')
    {y : D.Edge} (hy : D.IsBoundary y) : t' y = t y := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (hs.boundary hy).trans ih

theorem InnerReach.legal {D : Diagram Γ a b} {t t' : D.Edge → Bool} (h : InnerReach I D t t')
    (ht : (D.graph I).Legal t) : (D.graph I).Legal t' := by
  induction h with
  | refl => exact ht
  | tail _ hs _ => exact hs.2.1

/-- Moves inside the upper part of a stack are moves inside the stack. -/
theorem innerReach_glueComp_left {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    {t₁ t₁' : D₁.Edge → Bool} {t₂ : D₂.Edge → Bool} (h : InnerReach I D₁ t₁ t₁')
    (h₂ : (D₂.graph I).Legal t₂) (hag : ∀ j, t₂ (.inl j) = t₁ (D₁.bottom j)) :
    InnerReach I (comp D₁ D₂) (glueComp D₁ D₂ t₁ t₂) (glueComp D₁ D₂ t₁' t₂) := by
  induction h with
  | refl => exact .refl
  | @tail u u' hr hs ih =>
    have hu (j) : t₂ (.inl j) = u (D₁.bottom j) :=
      (hag j).trans (InnerReach.boundary hr (Or.inr ⟨j, rfl⟩)).symm
    have hu' (j) := (hu j).trans (hs.boundary (Or.inr ⟨j, rfl⟩)).symm
    obtain ⟨hl, hl', y, hy, rfl⟩ := hs
    exact ih.tail ⟨legal_glueComp hl h₂ hu, legal_glueComp hl' h₂ hu', compLeft D₁ D₂ y,
      not_isBoundary_compLeft hy, glueComp_reverse_left ..⟩

/-- Moves inside the lower part of a stack are moves inside the stack. -/
theorem innerReach_glueComp_right {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    {t₁ : D₁.Edge → Bool} {t₂ t₂' : D₂.Edge → Bool} (h : InnerReach I D₂ t₂ t₂')
    (h₁ : (D₁.graph I).Legal t₁) (hag : ∀ j, t₂ (.inl j) = t₁ (D₁.bottom j)) :
    InnerReach I (comp D₁ D₂) (glueComp D₁ D₂ t₁ t₂) (glueComp D₁ D₂ t₁ t₂') := by
  induction h with
  | refl => exact .refl
  | @tail u u' hr hs ih =>
    have hu (j) : u (.inl j) = t₁ (D₁.bottom j) :=
      (InnerReach.boundary hr (Or.inl ⟨j, rfl⟩)).trans (hag j)
    have hu' (j) := (hs.boundary (Or.inl ⟨j, rfl⟩)).trans (hu j)
    obtain ⟨hl, hl', z, hz, rfl⟩ := hs
    rcases z with j | e
    · exact absurd (Or.inl ⟨j, rfl⟩) hz
    exact ih.tail ⟨legal_glueComp h₁ hl hu, legal_glueComp h₁ hl' hu', compRight D₁ D₂ (.inr e),
      not_isBoundary_compRight hz, glueComp_reverse_right ..⟩

private theorem comp_cases {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} (x : (comp D₁ D₂).Edge) :
    (∃ y, x = compLeft D₁ D₂ y) ∨ ∃ e, x = .inr (.inr e) := by
  rcases x with i | e | e
  · exact Or.inl ⟨.inl i, rfl⟩
  · exact Or.inl ⟨.inr e, rfl⟩
  · exact Or.inr ⟨e, rfl⟩

theorem comp_cases_compRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (x : (comp D₁ D₂).Edge) : (∃ y, x = compLeft D₁ D₂ y) ∨ ∃ z, x = compRight D₁ D₂ z := by
  rcases comp_cases x with ⟨y, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨.inr e, rfl⟩

theorem reverse_compLeft_comp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (comp D₁ D₂).Edge → Bool) (y : D₁.Edge) :
    reverse s (compLeft D₁ D₂ y) ∘ compLeft D₁ D₂ = reverse (s ∘ compLeft D₁ D₂) y :=
  reverse_comp_of_injective (compLeft_injective D₁ D₂) s y

theorem reverse_compRight_comp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (comp D₁ D₂).Edge → Bool) (z : D₂.Edge) :
    reverse s (compRight D₁ D₂ z) ∘ compRight D₁ D₂ = reverse (s ∘ compRight D₁ D₂) z :=
  reverse_comp_of_injective (compRight_injective D₁ D₂ (bottom_injective D₁)) s z

/-- Reversing an edge of one part of a stack, not shared with the other part, leaves the other
part alone. -/
theorem reverse_compLeft_comp_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (comp D₁ D₂).Edge → Bool) {y : D₁.Edge} (hy : ∀ j, y ≠ D₁.bottom j) :
    reverse s (compLeft D₁ D₂ y) ∘ compRight D₁ D₂ = s ∘ compRight D₁ D₂ :=
  reverse_comp_of_not_mem_range s fun z h => by
    obtain ⟨j, -, rfl⟩ := compLeft_eq_compRight h.symm
    exact hy j rfl

theorem reverse_inr_comp_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (comp D₁ D₂).Edge → Bool) (e : D₂.Inner) :
    reverse s (.inr (.inr e)) ∘ compLeft D₁ D₂ = s ∘ compLeft D₁ D₂ :=
  reverse_comp_of_not_mem_range s fun y => compLeft_ne_inr_inr D₁ D₂ y e

/-! ### Juxtaposition -/

/-- The configuration of a juxtaposition with the given configurations of its parts. -/
@[expose] def glueTensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) : (tensor D₁ D₂).Edge → Label
  | .inl i =>
    ((List.appendIndexEquiv a c).symm i).elim (fun i => t₁ (.inl i)) (fun i => t₂ (.inl i))
  | .inr (.inl e) => t₁ (.inr e)
  | .inr (.inr e) => t₂ (.inr e)

theorem glueTensor_tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) (x : D₁.Edge) :
    glueTensor D₁ D₂ t₁ t₂ (tensorLeft D₁ D₂ x) = t₁ x := by
  rcases x with i | e
  · simp [glueTensor, tensorLeft, Sum.map]
  · rfl

theorem glueTensor_tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) (t₁ : D₁.Edge → Label)
    (t₂ : D₂.Edge → Label) (x : D₂.Edge) :
    glueTensor D₁ D₂ t₁ t₂ (tensorRight D₁ D₂ x) = t₂ x := by
  rcases x with i | e
  · simp [glueTensor, tensorRight, Sum.map]
  · rfl

theorem tensor_cases {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} (x : (tensor D₁ D₂).Edge) :
    (∃ y, x = tensorLeft D₁ D₂ y) ∨ ∃ z, x = tensorRight D₁ D₂ z := by
  rcases x with i | e | e
  · obtain ⟨i, rfl⟩ := (List.appendIndexEquiv a c).surjective i
    rcases i with i | i
    · exact Or.inl ⟨.inl i, rfl⟩
    · exact Or.inr ⟨.inl i, rfl⟩
  · exact Or.inl ⟨.inr e, rfl⟩
  · exact Or.inr ⟨.inr e, rfl⟩

/-- Configurations of a juxtaposition agree when they agree on both parts. -/
private theorem tensor_ext {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {t t' : (tensor D₁ D₂).Edge → Label}
    (h₁ : ∀ x, t (tensorLeft D₁ D₂ x) = t' (tensorLeft D₁ D₂ x))
    (h₂ : ∀ x, t (tensorRight D₁ D₂ x) = t' (tensorRight D₁ D₂ x)) : t = t' := by
  funext x
  rcases tensor_cases x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact h₁ y
  · exact h₂ z

theorem legal_glueTensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {t₁ : D₁.Edge → Bool}
    {t₂ : D₂.Edge → Bool} (h₁ : (D₁.graph I).Legal t₁) (h₂ : (D₂.graph I).Legal t₂) :
    ((tensor D₁ D₂).graph I).Legal (glueTensor D₁ D₂ t₁ t₂) := by
  rw [legal_tensor_iff, Function.comp_def, Function.comp_def,
    funext (glueTensor_tensorLeft D₁ D₂ t₁ t₂), funext (glueTensor_tensorRight D₁ D₂ t₁ t₂)]
  exact ⟨h₁, h₂⟩

theorem glueTensor_reverse_left (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (t₁ : D₁.Edge → Bool) (t₂ : D₂.Edge → Bool) (y : D₁.Edge) :
    glueTensor D₁ D₂ (reverse t₁ y) t₂ =
      reverse (glueTensor D₁ D₂ t₁ t₂) (tensorLeft D₁ D₂ y) := by
  refine tensor_ext (fun x => ?_) (fun x => ?_)
  · rw [glueTensor_tensorLeft, reverse_apply_of_injective (tensorLeft_injective D₁ D₂)]
    exact congrArg (reverse · y x) (funext fun z => (glueTensor_tensorLeft D₁ D₂ t₁ t₂ z).symm)
  · rw [glueTensor_tensorRight, reverse_of_ne _ (tensorLeft_ne_tensorRight D₁ D₂ y x).symm,
      glueTensor_tensorRight]

theorem glueTensor_reverse_right (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (t₁ : D₁.Edge → Bool) (t₂ : D₂.Edge → Bool) (z : D₂.Edge) :
    glueTensor D₁ D₂ t₁ (reverse t₂ z) =
      reverse (glueTensor D₁ D₂ t₁ t₂) (tensorRight D₁ D₂ z) := by
  refine tensor_ext (fun x => ?_) (fun x => ?_)
  · rw [glueTensor_tensorLeft, reverse_of_ne _ (tensorLeft_ne_tensorRight D₁ D₂ x z),
      glueTensor_tensorLeft]
  · rw [glueTensor_tensorRight, reverse_apply_of_injective (tensorRight_injective D₁ D₂)]
    exact congrArg (reverse · z x) (funext fun w => (glueTensor_tensorRight D₁ D₂ t₁ t₂ w).symm)

theorem glueTensor_eta (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (t : (tensor D₁ D₂).Edge → Label) :
    glueTensor D₁ D₂ (t ∘ tensorLeft D₁ D₂) (t ∘ tensorRight D₁ D₂) = t :=
  tensor_ext (fun _ => glueTensor_tensorLeft ..) (fun _ => glueTensor_tensorRight ..)

private theorem not_isBoundary_tensorLeft {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {y : D₁.Edge}
    (hy : ¬D₁.IsBoundary y) : ¬(tensor D₁ D₂).IsBoundary (tensorLeft D₁ D₂ y) := by
  rcases y with i | e
  · exact absurd (Or.inl ⟨i, rfl⟩) hy
  rintro (⟨i, h⟩ | ⟨j, h⟩)
  · injection h
  · rcases (List.appendIndexEquiv b d).surjective j with ⟨j | j, rfl⟩
    · rw [bottom_tensor_left] at h
      exact hy (Or.inr ⟨j, tensorLeft_injective D₁ D₂ h⟩)
    · rw [bottom_tensor_right] at h
      exact tensorLeft_ne_tensorRight D₁ D₂ _ _ h

private theorem not_isBoundary_tensorRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {z : D₂.Edge}
    (hz : ¬D₂.IsBoundary z) : ¬(tensor D₁ D₂).IsBoundary (tensorRight D₁ D₂ z) := by
  rcases z with i | e
  · exact absurd (Or.inl ⟨i, rfl⟩) hz
  rintro (⟨i, h⟩ | ⟨j, h⟩)
  · injection h
  · rcases (List.appendIndexEquiv b d).surjective j with ⟨j | j, rfl⟩
    · rw [bottom_tensor_left] at h
      exact tensorLeft_ne_tensorRight D₁ D₂ _ _ h.symm
    · rw [bottom_tensor_right] at h
      exact hz (Or.inr ⟨j, tensorRight_injective D₁ D₂ h⟩)

/-- Moves inside the left part of a juxtaposition are moves inside the juxtaposition. -/
theorem innerReach_glueTensor_left {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {t₁ t₁' : D₁.Edge → Bool} {t₂ : D₂.Edge → Bool} (h : InnerReach I D₁ t₁ t₁')
    (h₂ : (D₂.graph I).Legal t₂) :
    InnerReach I (tensor D₁ D₂) (glueTensor D₁ D₂ t₁ t₂) (glueTensor D₁ D₂ t₁' t₂) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hl, hl', y, hy, rfl⟩ := hs
    exact ih.tail ⟨legal_glueTensor hl h₂, legal_glueTensor hl' h₂, tensorLeft D₁ D₂ y,
      not_isBoundary_tensorLeft hy, glueTensor_reverse_left ..⟩

/-- Moves inside the right part of a juxtaposition are moves inside the juxtaposition. -/
theorem innerReach_glueTensor_right {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {t₁ : D₁.Edge → Bool} {t₂ t₂' : D₂.Edge → Bool} (h : InnerReach I D₂ t₂ t₂')
    (h₁ : (D₁.graph I).Legal t₁) :
    InnerReach I (tensor D₁ D₂) (glueTensor D₁ D₂ t₁ t₂) (glueTensor D₁ D₂ t₁ t₂') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hl, hl', z, hz, rfl⟩ := hs
    exact ih.tail ⟨legal_glueTensor h₁ hl, legal_glueTensor h₁ hl', tensorRight D₁ D₂ z,
      not_isBoundary_tensorRight hz, glueTensor_reverse_right ..⟩

theorem reverse_tensorLeft_comp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (tensor D₁ D₂).Edge → Bool) (y : D₁.Edge) :
    reverse s (tensorLeft D₁ D₂ y) ∘ tensorLeft D₁ D₂ = reverse (s ∘ tensorLeft D₁ D₂) y :=
  reverse_comp_of_injective (tensorLeft_injective D₁ D₂) s y

theorem reverse_tensorRight_comp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (tensor D₁ D₂).Edge → Bool) (z : D₂.Edge) :
    reverse s (tensorRight D₁ D₂ z) ∘ tensorRight D₁ D₂ = reverse (s ∘ tensorRight D₁ D₂) z :=
  reverse_comp_of_injective (tensorRight_injective D₁ D₂) s z

theorem reverse_tensorLeft_comp_tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (tensor D₁ D₂).Edge → Bool) (y : D₁.Edge) :
    reverse s (tensorLeft D₁ D₂ y) ∘ tensorRight D₁ D₂ = s ∘ tensorRight D₁ D₂ :=
  reverse_comp_of_not_mem_range s fun z => (tensorLeft_ne_tensorRight D₁ D₂ y z).symm

theorem reverse_tensorRight_comp_tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (tensor D₁ D₂).Edge → Bool) (z : D₂.Edge) :
    reverse s (tensorRight D₁ D₂ z) ∘ tensorLeft D₁ D₂ = s ∘ tensorLeft D₁ D₂ :=
  reverse_comp_of_not_mem_range s fun y => tensorLeft_ne_tensorRight D₁ D₂ y z

end Cslib.Complexity.NCL.Diagram
