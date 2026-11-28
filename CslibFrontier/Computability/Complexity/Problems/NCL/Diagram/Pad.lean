/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Substitution

/-!
# Open simulations beside unchanged wires

## Main definitions

* `Cslib.Complexity.NCL.Diagram.OpenSim.pad`: extend an open simulation by identical wires
  on its two sides.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ Γ' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
  {a b : List Color} {D : Diagram Γ a b} {D' : Diagram Γ' a b}

/-- An open implementation remains valid beside unchanged wires on either side. -/
@[expose] def OpenSim.pad (l r : List Color) (S : OpenSim I I' D D') :
    OpenSim I I' (pad l D r) (pad l D' r) :=
  (OpenSim.idWires l).tensor (S.tensor (OpenSim.idWires r))

end Cslib.Complexity.NCL.Diagram
