/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Labeling
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Measure

/-!
# The labels of actual wire crossings

Read each swap's two incoming labels, in the same structural order as its diagram. Stacking
and juxtaposition restrict the labeling along the existing edge embeddings.

## Main results

* `Diagram.length_crossingPairs`: one recorded pair for each actual swap.
* `Diagram.crossingPairs_map`: changing the labels maps both coordinates of every pair.
-/

public section

namespace Cslib.Complexity.NCL.Diagram
variable {Γ : List Color → List Color → Type} {Label Label' : Type*}

/-- The ordered input-label pair at every swap of a diagram. -/
@[expose] def crossingPairs : {a b : List Color} → (D : Diagram Γ a b) →
    (D.Edge → Label) → List (Label × Label)
  | _, _, .gen _, _ => []
  | _, _, .id _, _ => []
  | _, _, .swap _ _, label => [(label (.inl 0), label (.inl 1))]
  | _, _, .comp D₁ D₂, label =>
      crossingPairs D₁ (label ∘ compLeft D₁ D₂) ++
        crossingPairs D₂ (label ∘ compRight D₁ D₂)
  | _, _, .tensor D₁ D₂, label =>
      crossingPairs D₁ (label ∘ tensorLeft D₁ D₂) ++
        crossingPairs D₂ (label ∘ tensorRight D₁ D₂)

/-- Every actual swap contributes exactly one label pair. -/
theorem length_crossingPairs {a b : List Color} (D : Diagram Γ a b) (label : D.Edge → Label) :
    (D.crossingPairs label).length = D.swapCount := by
  induction D with
  | gen | id | swap => rfl
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [crossingPairs, List.length_append, ih₁, ih₂, swapCount]

/-- Relabeling a diagram applies the same function to both wires at every crossing. -/
theorem crossingPairs_map {a b : List Color} (D : Diagram Γ a b) (label : D.Edge → Label)
    (f : Label → Label') :
    D.crossingPairs (f ∘ label) = (D.crossingPairs label).map (Prod.map f f) := by
  induction D with
  | gen | id | swap => rfl
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [crossingPairs, Function.comp_assoc, ih₁, ih₂, List.map_append]

namespace Labeling
variable {a b c d : List Color} {x y z x' y' : List Label}

/-- Stacking labeled diagrams concatenates their actual crossing events. -/
theorem crossingPairs_comp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Labeling D₁ x y) (t : Labeling D₂ y z) :
    (D₁.comp D₂).crossingPairs (s.comp t).label =
      D₁.crossingPairs s.label ++ D₂.crossingPairs t.label := by
  rw [crossingPairs, comp_label_left, comp_label_right]

/-- Juxtaposing labeled diagrams concatenates their actual crossing events. -/
theorem crossingPairs_tensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    (s : Labeling D₁ x y) (t : Labeling D₂ x' y') :
    (D₁.tensor D₂).crossingPairs (s.tensor t).label =
      D₁.crossingPairs s.label ++ D₂.crossingPairs t.label := by
  rw [crossingPairs, tensor_label_left, tensor_label_right]

/-- Moving one wire left crosses the preceding wires in reverse order. -/
theorem crossingPairs_moveLeft (x : Color) (tag : Label) (r : List Color) (rs : List Label)
    (hrs : rs.length = r.length) :
    ∀ (l : List Color) (ls : List Label) (hls : ls.length = l.length),
    (Diagram.moveLeft (Γ := Γ) l x r).crossingPairs
      (Labeling.moveLeft x tag r rs hrs l ls hls).label = ls.reverse.map (·, tag)
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | y :: l, b :: ls, h => by
      simp only [Diagram.moveLeft, Labeling.moveLeft]
      rw [crossingPairs_comp, crossingPairs_tensor, crossingPairs_tensor]
      simp only [crossingPairs, Labeling.swap, List.nil_append, List.append_nil,
        crossingPairs_moveLeft x tag r rs hrs l ls (Nat.succ_injective h), List.reverse_cons,
        List.map_append, List.map_cons, List.map_nil]
      rfl

end Labeling

end Cslib.Complexity.NCL.Diagram

