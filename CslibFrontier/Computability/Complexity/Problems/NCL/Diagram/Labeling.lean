/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Contract

/-!
# Wire labels through diagrams

A labeling records the identity of every wire and the labels read at both boundaries. Stacking
and juxtaposition reuse the gluing operations for orientations, with an arbitrary label type.
These labelings track the original incidences through the swaps of a canonical graph drawing.

## Main definitions

* `Diagram.Labeling`: wire labels with specified boundary lists.
* `Diagram.Labeling.comp`, `Diagram.Labeling.tensor`: gluing compatible labelings.
* `Diagram.Labeling.moveLeft`: labels are preserved when a wire crosses a bundle.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {Label : Type*} {a b c d : List Color}

/-- Labels on every wire, with prescribed readings at the two boundaries. -/
structure Labeling (D : Diagram Γ a b) (x y : List Label) where
  /-- The identity carried by each wire. -/
  label : D.Edge → Label
  /-- The labels read above the diagram. -/
  top_eq : D.topList label = x
  /-- The labels read below the diagram. -/
  bot_eq : D.botList label = y

namespace Labeling

variable {x y z : List Label}

private theorem agrees {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) (j : Fin b.length) :
    t.label (.inl j) = s.label (D₁.bottom j) :=
  congrFun (List.ofFn_inj.1 (t.top_eq.trans s.bot_eq.symm)) j

/-- Stack labelings with the same labels on their shared boundary. -/
@[expose] def comp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) : Labeling (D₁.comp D₂) x z where
  label := glueComp D₁ D₂ s.label t.label
  top_eq := (congrArg (D₁.topList ·) (funext fun e => glueComp_compLeft _ _ _ _ e)).trans s.top_eq
  bot_eq := by
    exact (botList_compRight D₁ D₂ _).symm.trans
      ((congrArg (D₂.botList ·) (funext (glueComp_compRight _ _ _ _ (agrees s t)))).trans t.bot_eq)

@[simp] theorem comp_label_left {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) :
    (s.comp t).label ∘ compLeft D₁ D₂ = s.label :=
  funext fun e => glueComp_compLeft _ _ _ _ e

@[simp] theorem comp_label_right {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) :
    (s.comp t).label ∘ compRight D₁ D₂ = t.label :=
  funext fun e => glueComp_compRight _ _ _ _ (agrees s t) e

/-- Pulling an orientation back along the labels of a stack checks both parts. -/
theorem legal_comp (I : Interp Γ) {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) (u : Label → Bool) :
    ((D₁.comp D₂).graph I).Legal (u ∘ (s.comp t).label) ↔
      (D₁.graph I).Legal (u ∘ s.label) ∧ (D₂.graph I).Legal (u ∘ t.label) := by
  rw [legal_comp_iff]
  simp only [Function.comp_assoc, comp_label_left, comp_label_right]

/-- Juxtapose labelings and concatenate their boundary lists. -/
@[expose] def tensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {x₁ y₁ x₂ y₂ : List Label}
    (s : Labeling D₁ x₁ y₁) (t : Labeling D₂ x₂ y₂) :
    Labeling (D₁.tensor D₂) (x₁ ++ x₂) (y₁ ++ y₂) where
  label := glueTensor D₁ D₂ s.label t.label
  top_eq := by
    rw [topList_tensor]
    exact congrArg₂ (· ++ ·)
      ((congrArg (D₁.topList ·) (funext fun e => glueTensor_tensorLeft _ _ _ _ e)).trans s.top_eq)
      ((congrArg (D₂.topList ·) (funext fun e => glueTensor_tensorRight _ _ _ _ e)).trans t.top_eq)
  bot_eq := by
    rw [botList_tensor]
    exact congrArg₂ (· ++ ·)
      ((congrArg (D₁.botList ·) (funext fun e => glueTensor_tensorLeft _ _ _ _ e)).trans s.bot_eq)
      ((congrArg (D₂.botList ·) (funext fun e => glueTensor_tensorRight _ _ _ _ e)).trans t.bot_eq)

@[simp] theorem tensor_label_left {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x₁ y₁ x₂ y₂ : List Label} (s : Labeling D₁ x₁ y₁) (t : Labeling D₂ x₂ y₂) :
    (s.tensor t).label ∘ tensorLeft D₁ D₂ = s.label :=
  funext fun e => glueTensor_tensorLeft _ _ _ _ e

@[simp] theorem tensor_label_right {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x₁ y₁ x₂ y₂ : List Label} (s : Labeling D₁ x₁ y₁) (t : Labeling D₂ x₂ y₂) :
    (s.tensor t).label ∘ tensorRight D₁ D₂ = t.label :=
  funext fun e => glueTensor_tensorRight _ _ _ _ e

/-- Pulling an orientation back along juxtaposed labels checks both parts. -/
theorem legal_tensor (I : Interp Γ) {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x₁ y₁ x₂ y₂ : List Label} (s : Labeling D₁ x₁ y₁) (t : Labeling D₂ x₂ y₂)
    (u : Label → Bool) :
    ((D₁.tensor D₂).graph I).Legal (u ∘ (s.tensor t).label) ↔
      (D₁.graph I).Legal (u ∘ s.label) ∧ (D₂.graph I).Legal (u ∘ t.label) := by
  rw [legal_tensor_iff]
  simp only [Function.comp_assoc, tensor_label_left, tensor_label_right]

/-- If every edge reaches the lower boundary, distinct and exhaustive bottom labels identify
all diagram edges bijectively. -/
theorem bijective_of_bottom {D : Diagram Γ a b} {x y : List Label} (L : Labeling D x y)
    (hb : Function.Surjective D.bottom) (hn : y.Nodup) (hm : ∀ tag, tag ∈ y) :
    Function.Bijective L.label := by
  have hbot : List.ofFn (L.label ∘ D.bottom) = y := L.bot_eq
  have hinj : Function.Injective (L.label ∘ D.bottom) := List.nodup_ofFn.1 (hbot.symm ▸ hn)
  refine ⟨fun e f hef => ?_, fun tag => ?_⟩
  · obtain ⟨i, rfl⟩ := hb e
    obtain ⟨j, rfl⟩ := hb f
    exact congrArg D.bottom (hinj hef)
  · obtain ⟨i, hi⟩ := List.mem_ofFn.1 (hbot.symm ▸ hm tag)
    exact ⟨D.bottom i, hi⟩

/-- Straight wires preserve their labels. -/
@[expose] def id (a : List Color) (x : List Label) (h : x.length = a.length) :
    Labeling (Diagram.id (Γ := Γ) a) x x where
  label := Sum.elim (fun i => x.get (i.cast h.symm)) Empty.elim
  top_eq := by
    change List.ofFn (fun i : Fin a.length => x.get (i.cast h.symm)) = x
    rw [List.ofFn_congr h.symm]
    simp
  bot_eq := by
    change List.ofFn (fun i : Fin a.length => x.get (i.cast h.symm)) = x
    rw [List.ofFn_congr h.symm]
    simp

/-- Crossing two wires exchanges their boundary positions. -/
@[expose] def swap (a b : Color) (x y : Label) :
    Labeling (Diagram.swap (Γ := Γ) a b) [x, y] [y, x] where
  label := Sum.elim (fun i => if i.val = 0 then x else y) Empty.elim
  top_eq := rfl
  bot_eq := rfl

/-- Route one labeled wire to the left across a labeled bundle. -/
@[expose] def moveLeft (x : Color) (tag : Label) (r : List Color) (rs : List Label)
    (hrs : rs.length = r.length) : (l : List Color) → (ls : List Label) →
    ls.length = l.length →
    Labeling (Diagram.moveLeft (Γ := Γ) l x r) (ls ++ tag :: rs) (tag :: (ls ++ rs))
  | [], [], _ => .id _ _ (by simp [hrs])
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | y :: l, b :: ls, h =>
    ((Labeling.id [y] [b] rfl).tensor
      (moveLeft x tag r rs hrs l ls (Nat.succ_injective h))).comp
        ((swap y x b tag).tensor (Labeling.id (l ++ r) (ls ++ rs)
          (by simp [Nat.succ_injective h, hrs])))

end Labeling

end Cslib.Complexity.NCL.Diagram
