/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Basic

/-!
# Occurrences of a diagram in another

An occurrence of a diagram `H` in a diagram `D` (`Cslib.Complexity.NCL.Diagram.Occurrence`) is
a path down the syntax of `D` to a copy of `H`. It embeds the edges of `H` among those of `D`
(`Cslib.Complexity.NCL.Diagram.Occurrence.emb`), and every legal configuration of `D` restricts to
a legal configuration of `H`. So a static property of a gadget, proved once, holds wherever the
gadget is used, and so does a property of its moves.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Occurrence`, `Cslib.Complexity.NCL.Diagram.Occurrence.emb`.
* `Cslib.Complexity.NCL.Diagram.Occurrence.trans`: an occurrence inside an occurrence.

## Main results

* `Cslib.Complexity.NCL.Diagram.Occurrence.legal`: legality restricts to an occurrence.
* `Cslib.Complexity.NCL.Diagram.Occurrence.reverse_comp`: reversing an edge of an occurrence
  commutes with the restriction.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {c d : List Color}
  {H : Diagram Γ c d}

/-- An occurrence of the diagram `H` in a diagram: a path down its syntax to a copy of `H`. -/
inductive Occurrence (H : Diagram Γ c d) : {a b : List Color} → Diagram Γ a b → Type
  /-- `H` itself. -/
  | refl : Occurrence H H
  /-- An occurrence in the upper part of a stack. -/
  | compLeft {a b e : List Color} {D₁ : Diagram Γ a b} (D₂ : Diagram Γ b e) :
      Occurrence H D₁ → Occurrence H (D₁.comp D₂)
  /-- An occurrence in the lower part of a stack. -/
  | compRight {a b e : List Color} (D₁ : Diagram Γ a b) {D₂ : Diagram Γ b e} :
      Occurrence H D₂ → Occurrence H (D₁.comp D₂)
  /-- An occurrence in the left part of a juxtaposition. -/
  | tensorLeft {a b e f : List Color} {D₁ : Diagram Γ a b} (D₂ : Diagram Γ e f) :
      Occurrence H D₁ → Occurrence H (D₁.tensor D₂)
  /-- An occurrence in the right part of a juxtaposition. -/
  | tensorRight {a b e f : List Color} (D₁ : Diagram Γ a b) {D₂ : Diagram Γ e f} :
      Occurrence H D₂ → Occurrence H (D₁.tensor D₂)

namespace Occurrence

/-- The edges of the occurrence, as edges of the diagram. -/
@[expose] def emb : {a b : List Color} → {D : Diagram Γ a b} → Occurrence H D → H.Edge → D.Edge
  | _, _, _, refl => _root_.id
  | _, _, _, compLeft D₂ o => Diagram.compLeft _ D₂ ∘ o.emb
  | _, _, _, compRight D₁ o => Diagram.compRight D₁ _ ∘ o.emb
  | _, _, _, tensorLeft D₂ o => Diagram.tensorLeft _ D₂ ∘ o.emb
  | _, _, _, tensorRight D₁ o => Diagram.tensorRight D₁ _ ∘ o.emb

theorem emb_injective : {a b : List Color} → {D : Diagram Γ a b} → (o : Occurrence H D) →
    Function.Injective o.emb
  | _, _, _, refl => Function.injective_id
  | _, _, _, compLeft D₂ o => (Diagram.compLeft_injective _ D₂).comp o.emb_injective
  | _, _, _, compRight D₁ o =>
    (Diagram.compRight_injective D₁ _ (bottom_injective D₁)).comp o.emb_injective
  | _, _, _, tensorLeft D₂ o => (Diagram.tensorLeft_injective _ D₂).comp o.emb_injective
  | _, _, _, tensorRight D₁ o => (Diagram.tensorRight_injective D₁ _).comp o.emb_injective

/-- **Legality restricts to an occurrence.** -/
theorem legal : {a b : List Color} → {D : Diagram Γ a b} → (o : Occurrence H D) →
    {t : D.Edge → Bool} → (D.graph I).Legal t → (H.graph I).Legal (t ∘ o.emb)
  | _, _, _, refl, _, ht => ht
  | _, _, _, compLeft D₂ o, t, ht => o.legal ((legal_comp_iff _ D₂ t).1 ht).1
  | _, _, _, compRight D₁ o, t, ht => o.legal ((legal_comp_iff D₁ _ t).1 ht).2
  | _, _, _, tensorLeft D₂ o, t, ht => o.legal ((legal_tensor_iff _ D₂ t).1 ht).1
  | _, _, _, tensorRight D₁ o, t, ht => o.legal ((legal_tensor_iff D₁ _ t).1 ht).2

/-- **Reversing an edge of an occurrence commutes with the restriction.** -/
theorem reverse_comp {a b : List Color} {D : Diagram Γ a b} (o : Occurrence H D)
    (t : D.Edge → Bool) (y : H.Edge) : reverse t (o.emb y) ∘ o.emb = reverse (t ∘ o.emb) y :=
  reverse_comp_of_injective o.emb_injective t y

/-- **A move of the diagram reversing an edge of an occurrence is a move of the occurrence.** -/
theorem legal_reverse {a b : List Color} {D : Diagram Γ a b} (o : Occurrence H D)
    {t : D.Edge → Bool} {y : H.Edge} (ht : (D.graph I).Legal (reverse t (o.emb y))) :
    (H.graph I).Legal (reverse (t ∘ o.emb) y) :=
  o.reverse_comp t y ▸ o.legal ht

/-- If reversing a local edge is illegal, a move of the containing diagram leaves it unchanged. -/
theorem apply_eq_of_not_legal_reverse {a b : List Color} {D : Diagram Γ a b}
    (o : Occurrence H D) {s t : D.Edge → Bool} {x : H.Edge}
    (h : (D.graph I).Step s t) (hx : ¬(H.graph I).Legal (reverse (s ∘ o.emb) x)) :
    s (o.emb x) = t (o.emb x) := by
  obtain ⟨_, ht, e, rfl⟩ := h
  by_cases he : e = o.emb x
  · subst e
    exact (hx (o.legal_reverse ht)).elim
  · exact (reverse_of_ne s (Ne.symm he)).symm

/-- The occurrence of a layer's diagram in the padded layer. -/
@[expose] def pad {a b : List Color} {D : Diagram Γ a b} (l r : List Color) (o : Occurrence H D) :
    Occurrence H (Diagram.pad l D r) :=
  .tensorRight _ (.tensorLeft _ o)

/-- An occurrence of `K` in an occurrence of `H`. -/
@[expose] def trans {e f : List Color} {K : Diagram Γ e f} :
    {a b : List Color} → {D : Diagram Γ a b} → Occurrence H D → Occurrence K H → Occurrence K D
  | _, _, _, refl, o' => o'
  | _, _, _, compLeft D₂ o, o' => .compLeft D₂ (o.trans o')
  | _, _, _, compRight D₁ o, o' => .compRight D₁ (o.trans o')
  | _, _, _, tensorLeft D₂ o, o' => .tensorLeft D₂ (o.trans o')
  | _, _, _, tensorRight D₁ o, o' => .tensorRight D₁ (o.trans o')

theorem emb_trans {e f : List Color} {K : Diagram Γ e f} :
    {a b : List Color} → {D : Diagram Γ a b} → (o : Occurrence H D) → (o' : Occurrence K H) →
      (o.trans o').emb = o.emb ∘ o'.emb
  | _, _, _, refl, _ => rfl
  | _, _, _, compLeft _ o, o' => congrArg (_ ∘ ·) (o.emb_trans o')
  | _, _, _, compRight _ o, o' => congrArg (_ ∘ ·) (o.emb_trans o')
  | _, _, _, tensorLeft _ o, o' => congrArg (_ ∘ ·) (o.emb_trans o')
  | _, _, _, tensorRight _ o, o' => congrArg (_ ∘ ·) (o.emb_trans o')

end Occurrence

end Cslib.Complexity.NCL.Diagram
