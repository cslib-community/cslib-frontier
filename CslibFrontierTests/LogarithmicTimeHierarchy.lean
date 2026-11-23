/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.LogarithmicTimeHierarchy

namespace CslibFrontierTests.LogarithmicTimeHierarchy

open FirstOrder FirstOrder.Language
open Cslib.Complexity
open Cslib.Logic.FO.Ordered
open Cslib.Logic.WordMSO

/-- The formula reads the letter at the canonically named position one. -/
example : {w : List Bool | w[1]? = some true} ∈ LH (Function.Embedding.refl _) := by
  let L := wordLanguage Bool
  let inc : L →ᴸ language L := LHom.sumInl
  refine ⟨Relations.formula₁ (inc.onRelation (wordLanguage.letterSymb true)) (one L), ?_⟩
  intro w hw
  change 2 ≤ w.length at hw
  let : L.Structure (Fin w.length) := wordStructure w
  let : Fact (2 ≤ w.length) := ⟨hw⟩
  change w[1]? = some true ↔ @Sentence.Realize (language L) (Fin w.length) _ _
  unfold Sentence.Realize
  rw [Formula.realize_rel₁, inc.map_onRelation,
    List.getElem?_eq_getElem (show 1 < w.length from hw)]
  change some w[1] = some true ↔
    @Structure.RelMap _ _ (wordStructure w) 1 (wordLanguage.letterSymb true)
      ![(one L).realize default]
  have hOne : (one L).realize (default : Empty → Fin w.length) = ⟨1, hw⟩ :=
    Fin.ext (realize_one_val _)
  simp only [hOne, wordStructure.relMap_letterSymb, Matrix.cons_val_zero, Option.some.injEq]
  rfl

end CslibFrontierTests.LogarithmicTimeHierarchy
