/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation

/-!
# Transporting closed diagram configurations

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Realization.mapClosed`: encode a closed realization through a
  constraint-graph simulation.
-/

public section

namespace Cslib.Complexity.NCL.Diagram.Realization

/-- Encode a legal closed-diagram configuration through a constraint-graph simulation. -/
@[expose] def mapClosed {Γ Γ' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
    {D : Diagram Γ [] []} {D' : Diagram Γ' [] []} [DecidableEq D.Edge] [DecidableEq D'.Edge]
    (R : Realization I D [] []) (S : ConstraintGraph.Simulation (D.graph I) (D'.graph I')) :
    Realization I' D' [] [] where
  orient := S.enc R.orient
  legal := S.legal_enc R.legal
  top_eq := rfl
  bot_eq := rfl

end Cslib.Complexity.NCL.Diagram.Realization
