/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.OneHotOrder
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.OrderAcceptance

/-! Scope alignment executes a genuine conjugation: a reverse-ordered clause star becomes
accepted in the new scope order, while every variable-end tag remains fixed. -/

public section

namespace CslibFrontierTests.CSPOneHotOrder

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Cslib.Complexity.Graph
open OneHot3

/-- A ternary clause with three separate original variable names. -/
def source : CSP Unit ℕ := [⟨(), [7, 9, 11]⟩]

/-- An actual reverse-ordered rotation at the constraint, with singleton variable fibers. -/
def reverseTable : RotationCertificate := ⟨[0, 5, 2, 1, 4, 3]⟩

example : orderedConstraints source reverseTable = [⟨(), [7, 11, 9]⟩] := by decide +kernel

example : (orderedCertificate source reverseTable).successor = [0, 3, 2, 5, 4, 1] := by
  decide +kernel

example : RotationCertificate.verifyGenusZero (incidenceGraph source) reverseTable = true := by
  decide +kernel

example : verifyRotationCertificate source reverseTable = false := by decide +kernel

example : verifyRotationCertificate (orderedConstraints source reverseTable)
    (orderedCertificate source reverseTable) = true := by decide +kernel

-- The general acceptance proof consumes only the source width and source numerical check.
example : verifyRotationCertificate (orderedConstraints source reverseTable)
    (orderedCertificate source reverseTable) = true := by
  apply verifyRotationCertificate_orderedCertificate
  · simp [source, Cslib.Logic.PL.CSP.WellFormed, arity]
  · decide +kernel

-- A short raw table uses its fixed fallback; evaluation still retains the original assignment.
example : (orderedConstraints [⟨(), []⟩, ⟨(), [7, 7, 7]⟩] ⟨[]⟩).eval sem
    (fun v => v == 7) = false := by decide +kernel

-- Unbounded binary lookup data do not become iteration counts in either native certificate.
example : dartReindex reverseTable (dartReindex reverseTable (2 ^ 250 + 17)) =
    2 ^ 250 + 17 := dartReindex_involutive reverseTable _

end CslibFrontierTests.CSPOneHotOrder
