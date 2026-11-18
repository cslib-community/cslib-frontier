/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Compiler
import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.OrderAcceptance
import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.RotationCorrectness

/-!
# Native hardness of supplied ordered OneHot3 rotation certificates

The actual total ThreeSAT drawing compiler supplies every source drawing internally.
The executed cardinal table is genus zero, and the ternary scope permutation transports
it to the original ordered CSP checker. Thus all raw ThreeSAT inputs have an accepting
syntax/geometry output whose satisfiability is exactly the original guarded language.

This native reduction is an original composition of the existing actual drawing compiler
and the internally verified clockwise table. It is a reduction from raw ThreeSAT formulas;
it does not assert a reduction from arbitrary raw supplied-drawing records.

## Main results

* `verifyRotationCertificate_compileThreeSAT`: full checker acceptance on every raw input.
* `polyTimeReducible_ThreeSAT`: the actual native reduction to the guarded target language.
* `npHard`: native NP-hardness of supplied ordered OneHot3 rotation certificates.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph Turing.MultiTapeTM

/-- The actual output passes the full ordered certificate checker on every raw source
formula. The source drawing, the native table, target genus and argument order are all
constructed internally. -/
theorem verifyRotationCertificate_compileThreeSAT (φ : CNF ℕ) :
    verifyRotationCertificate (compileThreeSAT φ).constraints (compileThreeSAT φ).rotation =
      true := by
  let ψ := toPlanarPositiveOneInExactThreeSATThree φ
  let F := ofCNF ψ
  let drawing := (toDrawnPlanarPositiveOneInExactThreeSATThree φ).drawing
  let c := OrthogonalDrawing.rotationCertificate (incidenceGraph F) drawing
  have hp : OneSAT.positiveCheck ψ = true := positive_toPlanarPositiveOneInExactThreeSATThree φ
  have hw : F.WellFormed arity := wellFormed_ofCNF ψ fun row hrow =>
    (exactClauses_toPlanarPositiveOneInExactThreeSATThree φ row hrow).1
  have hd : IsPlanarOrthogonalDrawing (incidenceGraph F) drawing := by
    rw [incidenceGraph_ofCNF ψ hp]
    exact isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ
  exact verifyRotationCertificate_orderedCertificate F c hw
    (OrthogonalDrawing.verifyGenusZero_rotationCertificate hd)

/-- The executed output's membership in the canonical ordered-certificate language agrees
with the original ThreeSAT language, including every malformed source formula. -/
theorem mem_compileThreeSAT_iff (φ : CNF ℕ) :
    compileThreeSAT φ ∈ RotationCSPSAT arity sem ↔ φ ∈ ThreeSAT := by
  change _ ∧ _ ∧ _ ↔ _
  rw [and_iff_right (wellFormed_compileThreeSAT φ),
    and_iff_right (verifyRotationCertificate_compileThreeSAT φ)]
  exact satisfiable_compileThreeSAT_iff φ

/-- Native polynomial-time reduction from ordinary ThreeSAT to the canonical supplied
ordered-certificate problem for OneHot3. No geometric or hardness provider is a premise. -/
theorem polyTimeReducible_ThreeSAT :
    PolyTimeReducible encCNF (encRotationInstance encUnit) ThreeSAT
      (RotationCSPSAT arity sem) :=
  ⟨compileThreeSAT, computableInPolyTime_compileThreeSAT,
    fun φ => (mem_compileThreeSAT_iff φ).symm⟩

/-- Supplied full ordered rotation-certificate OneHot3 is native NP-hard. Only this base
construction uses ternary source scopes; target substitution has arbitrary original arities. -/
theorem npHard : NPHard (encRotationInstance encUnit) (RotationCSPSAT arity sem) :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT

end Cslib.Complexity.CSP.OneHot3
