/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Bundle
public import Mathlib.Data.Fintype.Inv

/-!
# Closing a labeled incidence drawing

Source cells, a wire permutation, and sink cells form a closed diagram. If the source boundary
lists every incidence label exactly once, those labels are a bijective naming of the resulting
diagram edges. Legality is the conjunction of the source and sink constraints.

## Main definitions

* `Planar.Embedding.Drawing`: a closed diagram with a bijective edge labeling and listed
  constraints.
* `Planar.Embedding.Drawing.close`: close source and sink bundles through a labeled wiring.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

variable {Label : Type*}

/-- A closed diagram with a bijective incidence naming and an exact constraint list. -/
structure Drawing (diagram : Diagram Cell [] []) (specs : List (Vertex Label)) where
  /-- Every diagram edge carries exactly one incidence label. -/
  edgeEquiv : diagram.Edge ≃ Label
  /-- The diagram has exactly the listed constraints on its labeled edges. -/
  legal_iff (u : Label → Bool) : (diagram.graph Cell.interp).Legal (u ∘ edgeEquiv) ↔
    ∀ v ∈ specs, v.Sat u

namespace Drawing

/-- The closed incidence diagram underlying a source/wiring/sink assembly. -/
@[expose] def closeDiagram {a b : List Color} {xs ys : List Label}
    {sourceSpecs sinkSpecs : List (Vertex Label)}
    (S : Sources a xs sourceSpecs) (W : Wiring Cell a b xs ys) (T : Sinks b ys sinkSpecs) :
    Diagram Cell [] [] := S.diagram.comp (W.diagram.comp T.diagram)

/-- Connect source and sink bundles through the specified wire permutation. -/
@[expose] def close [DecidableEq Label] {a b : List Color} {xs ys : List Label}
    {sourceSpecs sinkSpecs : List (Vertex Label)}
    (S : Sources a xs sourceSpecs) (W : Wiring Cell a b xs ys) (T : Sinks b ys sinkSpecs)
    (hn : xs.Nodup) (hm : ∀ tag, tag ∈ xs) :
    Drawing (closeDiagram S W T) (sourceSpecs ++ sinkSpecs) := by
  let lower := W.diagram.comp T.diagram
  let D := closeDiagram S W T
  let L : Labeling D [] [] := S.labeling.comp (W.labeling.comp T.labeling)
  let ι : S.diagram.Edge → D.Edge := compLeft S.diagram lower
  have hlow : IsEmpty lower.Inner := by
    let := W.no_inner
    let := T.no_inner
    change IsEmpty (W.diagram.Inner ⊕ T.diagram.Inner)
    infer_instance
  have hι : Function.Bijective ι := by
    refine ⟨compLeft_injective _ _, fun e => ?_⟩
    rcases e with i | e | e
    · exact ⟨.inl i, rfl⟩
    · exact ⟨.inr e, rfl⟩
    · exact (hlow.false e).elim
  have hS := S.labeling.bijective_of_bottom S.bottom_surjective hn hm
  have hleft : L.label ∘ ι = S.labeling.label := Labeling.comp_label_left ..
  have hlabel : Function.Bijective L.label := by
    constructor
    · intro e f hef
      obtain ⟨s, rfl⟩ := hι.2 e
      obtain ⟨t, rfl⟩ := hι.2 f
      exact congrArg ι (hS.1 ((congrFun hleft s).symm.trans (hef.trans (congrFun hleft t))))
    · intro tag
      obtain ⟨e, he⟩ := hS.2 tag
      exact ⟨ι e, (congrFun hleft e).trans he⟩
  refine ⟨{ toFun := L.label
            invFun := Fintype.bijInv hlabel
            left_inv := Fintype.leftInverse_bijInv hlabel
            right_inv := Fintype.rightInverse_bijInv hlabel }, fun u => ?_⟩
  change (D.graph Cell.interp).Legal (u ∘ L.label) ↔ _
  have hw : (W.diagram.graph Cell.interp).Legal (u ∘ W.labeling.label) := W.legal _ _
  have ht : (lower.graph Cell.interp).Legal (u ∘ (W.labeling.comp T.labeling).label) ↔
      ∀ v ∈ sinkSpecs, v.Sat u := by
    have h := (Labeling.legal_comp Cell.interp W.labeling T.labeling u).trans
      (and_congr Iff.rfl (T.legal_iff u))
    simpa only [hw, true_and] using h
  exact ((Labeling.legal_comp Cell.interp S.labeling (W.labeling.comp T.labeling) u).trans
    (and_congr (S.legal_iff u) ht)).trans (by simp only [List.forall_mem_append])

end Drawing

end Cslib.Complexity.NCL.Planar.Embedding
