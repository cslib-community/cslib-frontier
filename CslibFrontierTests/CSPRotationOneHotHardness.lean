/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Hardness

/-!
The actual compiler accepts the empty satisfiable formula. A satisfiable raw clause with
four arguments is outside ThreeSAT: its compiled certificate still passes the full checker,
while its compiled CSP is rejected by the target language. The variable name stays binary.
-/

public section

namespace CslibFrontierTests.CSPRotationOneHotHardness

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Cslib.Complexity.CSP.OneHot3

/-- A raw positive clause with one repeated large name and four actual argument positions. -/
def wide : CNF ℕ := [[(2 ^ 250, true), (2 ^ 250, true), (2 ^ 250, true), (2 ^ 250, true)]]

example : compileThreeSAT [] ∈ RotationCSPSAT arity sem := by
  apply (mem_compileThreeSAT_iff []).mpr
  exact ⟨by simp, ⟨fun _ => false, rfl⟩⟩

example : wide.Satisfiable ∧ verifyRotationCertificate (compileThreeSAT wide).constraints
      (compileThreeSAT wide).rotation = true ∧
    compileThreeSAT wide ∉ RotationCSPSAT arity sem := by
  refine ⟨⟨fun _ => true, rfl⟩, verifyRotationCertificate_compileThreeSAT wide, ?_⟩
  rw [mem_compileThreeSAT_iff]
  simp [ThreeSAT, wide]

end CslibFrontierTests.CSPRotationOneHotHardness
