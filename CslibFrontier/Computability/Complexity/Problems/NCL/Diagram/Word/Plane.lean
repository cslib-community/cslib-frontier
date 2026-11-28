/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Standard
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing

/-!
# Checking plane words

A checked plane layer contains one standard AND/OR vertex and occupies adjacent wires.
The word checker applies this local check to every layer. A planar diagram built from these
cells emits a checked plane word.

## Main definitions

* `Cslib.Complexity.NCL.Slice.checkPlane`, `Cslib.Complexity.NCL.Word.checkPlane`: layer checks.

## Main results

* `Cslib.Complexity.NCL.Diagram.checkPlane_toWord`: checked diagram cells give a checked word.
-/

public section

namespace Cslib.Complexity.NCL

/-- Check for one standard vertex on the adjacent input and output wires. -/
@[expose] def Slice.checkPlane : Slice → Bool
  | .gen _ _ _ vs => (vs.length == 1) && Prim.checkStandard vs
  | .swap _ => false

/-- Check that every layer is a standard single-vertex layer. -/
@[expose] def Word.checkPlane (w : Word) : Bool := w.all Slice.checkPlane

namespace Diagram

variable {a b : List Color}

/-- A planar diagram of standard single-vertex cells emits a checked plane word. -/
theorem checkPlane_toWord (D : Diagram Prim a b) (k : ℕ) (hP : D.Planar)
    (hD : D.checkGens (fun g => (g.length == 1) && Prim.checkStandard g) = true) :
    (D.toWord Prim.interp k).checkPlane = true := by
  induction D generalizing k with
  | gen g =>
    simpa only [toWord, Word.checkPlane, List.all_cons, List.all_nil, Bool.and_true,
      Slice.checkPlane, checkGens, Prim.interp] using hD
  | id _ => rfl
  | swap _ _ => exact hP.elim
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [Planar] at hP
    simp only [checkGens, Bool.and_eq_true] at hD
    simp only [toWord, Word.checkPlane, List.all_append, Bool.and_eq_true]
    exact ⟨ih₁ _ hP.1 hD.1, ih₂ _ hP.2 hD.2⟩

end Diagram
end Cslib.Complexity.NCL
