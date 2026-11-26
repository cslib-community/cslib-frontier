/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Planarize
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Measure

/-!
# Origins of planarized wiring vertices

In a generator-free drawing, every vertex introduced by planarization belongs to one syntactic
crossing. `crossingOrigin` numbers these crossings in syntax order, with the left or upper part
before the right or lower part. This local origin is useful when relating a planar layout to
parameters of the original drawing.

## Main definitions

* `Planar.crossingOrigin`: the crossing responsible for a vertex of a planarized wiring.
-/

public section

namespace Cslib.Complexity.NCL.Planar

open Diagram

variable {Γ : List Color → List Color → Type}

/-- Every vertex of a planarized generator-free drawing comes from one syntactic crossing. -/
@[expose] def crossingOrigin (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) :
    ∀ {a b : List Color} (D : Diagram Γ a b), D.checkGens (fun _ => false) = true →
      (planarizeAlong H D).Vtx Prim.interp → Fin (swapCount D)
  | _, _, .gen _, h => by cases h
  | _, _, .id _, _ => fun v => v.elim
  | _, _, .swap .., _ => fun _ => (0 : Fin 1)
  | _, _, .comp D₁ D₂, h | _, _, .tensor D₁ D₂, h =>
    show ((planarizeAlong H D₁).Vtx Prim.interp ⊕ (planarizeAlong H D₂).Vtx Prim.interp) →
        Fin (swapCount D₁ + swapCount D₂) from
      Sum.elim
        (fun v => (crossingOrigin H D₁ (Bool.and_eq_true_iff.1 h).1 v).castAdd (swapCount D₂))
        (fun v => Fin.natAdd (swapCount D₁)
          (crossingOrigin H D₂ (Bool.and_eq_true_iff.1 h).2 v))

end Cslib.Complexity.NCL.Planar
