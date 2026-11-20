/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSAT
public import CslibFrontier.Computability.Complexity.Problems.PlanarPositiveOneInThreeSAT
public import CslibFrontier.Computability.PolyTime.CSP.OneHotOrder
public import CslibFrontier.Computability.PolyTime.Graph.OrthogonalRotation

/-!
# The executed ThreeSAT-to-rotation-OneHot3 compiler

The existing total positive exact-three compiler emits an actual integer orthogonal drawing
on every raw source input. The program reads its clockwise successor table, exchanges the
last two arguments where necessary, and conjugates that table by the same occurrence map.
No source embedding generator, target rotation, or geometric rank is supplied as a parameter.

This module proves native runtime, exact target width, and the satisfiability equivalence
including malformed ordinary ThreeSAT inputs. The separate hardness module combines these
facts with acceptance of the emitted table by the full target genus/order checker.

The program is an original composition of the actual compiler in
`CslibFrontier/Computability/Complexity/Problems/PlanarPositiveOneInThreeSAT.lean`
with the native orthogonal scan and ternary occurrence transport.

## Main definitions

* `compileThreeSAT`: the actual output constraints and supplied binary rotation table.

## Main results

* `computableInPolyTime_compileThreeSAT`: native runtime on every raw source formula.
* `satisfiable_compileThreeSAT_iff`: exact equivalence with the guarded ThreeSAT language.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph Turing.MultiTapeTM

/-- Execute the actual source drawing compiler, integer clockwise scan, scope alignment,
and binary successor-table conjugation. Every raw formula has a concrete output record. -/
@[expose] def compileThreeSAT (φ : CNF ℕ) : RotationInstance Unit :=
  let drawn := toDrawnPlanarPositiveOneInExactThreeSATThree φ
  let F := ofCNF drawn.formula
  let c := OrthogonalDrawing.rotationCertificate (incidenceGraph F) drawn.drawing
  ⟨orderedConstraints F c, orderedCertificate F c⟩

/-- Both output fields are computed natively in polynomial time. In particular, the
runtime proof includes the actual drawing generator and the literal binary table. -/
theorem computableInPolyTime_compileThreeSAT :
    ComputableInPolyTime compileThreeSAT encCNF (encRotationInstance encUnit) := by
  unfold compileThreeSAT
  have hd := computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree
  have hf := computableInPolyTime_ofCNF.comp
    (encDrawnPlanarPositiveOneInExactThreeSATThree_formula_polyTime hd)
  have hg := (computableInPolyTime_incidenceGraph encUnit encNat).comp hf
  have hc := OrthogonalDrawing.computableInPolyTime_rotationCertificate.comp
    (hg.prod (encDrawnPlanarPositiveOneInExactThreeSATThree_drawing_polyTime hd))
  have hi := hf.prod hc
  have hp := encRotationInstance_mk_polyTime encUnit
    (computableInPolyTime_orderedConstraints.comp hi)
    (computableInPolyTime_orderedCertificate.comp hi)
  simpa only [Function.comp_def] using hp

/-- Every raw source formula produces scopes of exactly the fixed OneHot3 arity. -/
theorem wellFormed_compileThreeSAT (φ : CNF ℕ) :
    (compileThreeSAT φ).constraints.WellFormed arity := by
  apply wellFormed_orderedConstraints
  exact wellFormed_ofCNF _ fun row hrow =>
    (exactClauses_toPlanarPositiveOneInExactThreeSATThree φ row hrow).1

/-- Satisfiability of the actual output body agrees with the original ordinary ThreeSAT
language, including its source syntax rejection, on every raw formula. -/
theorem satisfiable_compileThreeSAT_iff (φ : CNF ℕ) :
    (compileThreeSAT φ).constraints.Satisfiable sem ↔ φ ∈ ThreeSAT := by
  change (orderedConstraints _ _).Satisfiable sem ↔ _
  rw [satisfiable_orderedConstraints_iff]
  exact (satisfiable_ofCNF_iff _ (positive_toPlanarPositiveOneInExactThreeSATThree φ)).trans
    (oneSatisfiable_toPlanarPositiveOneInExactThreeSATThree_iff φ)

end Cslib.Complexity.CSP.OneHot3
