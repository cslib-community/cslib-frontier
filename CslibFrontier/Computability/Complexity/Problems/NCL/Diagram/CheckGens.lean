/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Substitution
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree

/-!
# Compositional checks of diagram generators

Check a property of each generator without enumerating graph configurations. Checks compose
with substitution. Checking the AND/OR shape of each local vertex proves that the whole
interpreted graph consists of AND/OR vertices, since all edge renamings preserve vertex kind.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.checkGens`: a Boolean check of every generator.

## Main results

* `Cslib.Complexity.NCL.Diagram.checkGens_subst`: generator checks commute with substitution.
* `Cslib.Complexity.NCL.Diagram.isAndOr_of_checkGens`: successful local shape checks imply
  `ConstraintGraph.IsAndOr` for the whole graph.
* `Cslib.Complexity.NCL.Diagram.loopFree_of_checkGens`: distinct local port edges remain
  distinct after composition.

## References

* AND/OR constraint graphs are defined in [Hearn and Demaine][HearnDemaine2005, Section 2.2].
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ Γ' : List Color → List Color → Type} {a b : List Color}

/-- Check every generator of a diagram. Routing wires require no check. -/
@[expose] def checkGens (test : ∀ {a b : List Color}, Γ a b → Bool) :
    {a b : List Color} → Diagram Γ a b → Bool
  | _, _, .gen g => test g
  | _, _, .id _ => true
  | _, _, .swap .. => true
  | _, _, .comp D₁ D₂ => D₁.checkGens test && D₂.checkGens test
  | _, _, .tensor D₁ D₂ => D₁.checkGens test && D₂.checkGens test

/-- Checks of substituted generators compose with the original diagram's check. -/
theorem checkGens_subst (test : ∀ {a b : List Color}, Γ' a b → Bool)
    (H : ∀ {a b : List Color}, Γ a b → Diagram Γ' a b) (D : Diagram Γ a b) :
    (D.subst H).checkGens test = D.checkGens (fun g => (H g).checkGens test) := by
  induction D with
  | gen _ | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => simp only [subst, checkGens, ih₁, ih₂]

/-- Two local checks can be combined in one diagram traversal. -/
theorem checkGens_and (test₁ test₂ : ∀ {a b : List Color}, Γ a b → Bool)
    (D : Diagram Γ a b) : D.checkGens (fun g => test₁ g && test₂ g) =
      (D.checkGens test₁ && D.checkGens test₂) := by
  induction D with
  | gen _ | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp [checkGens, ih₁, ih₂, Bool.and_assoc, Bool.and_left_comm]

/-- Moving a wire across a bundle introduces no generators. -/
theorem checkGens_moveLeft (test : ∀ {a b : List Color}, Γ a b → Bool)
    (l : List Color) (c : Color) (r : List Color) :
    (moveLeft l c r : Diagram Γ _ _).checkGens test = true := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [moveLeft, checkGens, ih, Bool.true_and]

/-- Checked local AND/OR vertex shapes imply the graph-level property. -/
theorem isAndOr_of_checkGens (I : Interp Γ) (D : Diagram Γ a b)
    (h : D.checkGens (fun g => (I.verts g).all Vertex.checkAndOr) = true) :
    (D.graph I).IsAndOr := by
  induction D with
  | gen g =>
    intro i
    exact (Vertex.checkAndOr_eq_true_iff _).1 ((List.all_eq_true.1 h) _ (List.get_mem _ i))
  | id _ | swap _ _ => exact fun v => v.elim
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [checkGens, Bool.and_eq_true] at h
    rintro (v | v)
    · exact (ih₁ h.1 v).map _
    · exact (ih₂ h.2 v).map _

/-- Checked local incidence lists imply loop-freedom of the whole graph. -/
theorem loopFree_of_checkGens (I : Interp Γ) (D : Diagram Γ a b)
    (h : D.checkGens (fun g => (I.verts g).all Vertex.checkLoopFree) = true) :
    (D.graph I).LoopFree := by
  induction D with
  | gen g =>
    intro i
    exact (Vertex.checkLoopFree_eq_true_iff _).1 ((List.all_eq_true.1 h) _ (List.get_mem _ i))
  | id _ | swap _ _ => exact fun v => v.elim
  | comp D₁ D₂ ih₁ ih₂ =>
    simp only [checkGens, Bool.and_eq_true] at h
    rintro (v | v)
    · exact ((ih₁ h.1).map (compLeft_injective D₁ D₂)) v
    · exact ((ih₂ h.2).map (compRight_injective D₁ D₂ (bottom_injective D₁))) v
  | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [checkGens, Bool.and_eq_true] at h
    rintro (v | v)
    · exact ((ih₁ h.1).map (tensorLeft_injective D₁ D₂)) v
    · exact ((ih₂ h.2).map (tensorRight_injective D₁ D₂)) v

end Cslib.Complexity.NCL.Diagram
