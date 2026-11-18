/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryAppendAcceptance

/-!
The executed append is checked with both nonempty probes, either one empty, and both empty.
The right body has two separate original components. They survive even when its probe is
empty. A three-port probe also distinguishes the original directed order from its reflection.
-/

public section

namespace CslibFrontierTests.CSPBoundaryAppendAcceptance

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Cslib.Complexity.Graph
open OrderedBoundary

/-- The left body has one unary occurrence at label zero. -/
def left : CSP Unit ℕ := [⟨(), [0]⟩]

/-- The right body has two separate unary components at labels one and two. -/
def right : CSP Unit ℕ := [⟨(), [1]⟩, ⟨(), [2]⟩]

/-- The left atom with an empty structural probe. -/
def leftClosed : Witness left [] := ⟨⟨[0, 1]⟩, by decide +kernel⟩

/-- Both right components with an empty structural probe. -/
def rightClosed : Witness right [] := ⟨⟨[0, 1, 2, 3]⟩, by decide +kernel⟩

/-- The left atom with its single actual boundary marker. -/
def leftMarked : Witness left [0] := ⟨⟨[2, 1, 0, 3]⟩, by decide +kernel⟩

/-- Both right atoms joined by the reversed two-port structural probe. -/
def rightMarked : Witness right [1, 2] :=
  ⟨⟨[6, 1, 4, 3, 2, 7, 0, 5]⟩, by decide +kernel⟩

/-- Executed append with both probes empty, retaining all three body components. -/
def closedJoin : Witness (left ++ right) [] :=
  leftClosed.appendComputed rightClosed
    (by simp [left, right, CSP.vars]) (by decide +kernel)

/-- Executed append retaining a left marker and both closed right components. -/
def leftJoin : Witness (left ++ right) [0] :=
  leftMarked.appendComputed rightClosed
    (by simp [left, right, CSP.vars, List.disjoint_left]) (by decide +kernel)

/-- Executed append with an empty left probe and both right markers. -/
def rightJoin : Witness (left ++ right) [1, 2] :=
  leftClosed.appendComputed rightMarked
    (by simp [left, right, CSP.vars]) (by decide +kernel)

example : closedJoin.certificate.successor = [0, 1, 2, 3, 4, 5] := by
  decide +kernel

example : verify (left ++ right) [] closedJoin.certificate = true := by
  exact closedJoin.accepted

example : leftJoin.certificate.successor = [6, 1, 2, 3, 4, 5, 0, 7] ∧
    verify (left ++ right) [0] leftJoin.certificate = true := by
  exact ⟨by decide +kernel, leftJoin.accepted⟩

example : verify (left ++ right) [1, 2] rightJoin.certificate = true := by
  exact rightJoin.accepted

/-- Executed three-port append retaining the original directed boundary order. -/
def markedJoin : Witness (left ++ right) [0, 1, 2] :=
  leftMarked.appendComputed rightMarked
    (by simp [left, right, CSP.vars, List.disjoint_left]) (by decide +kernel)

example : verify (left ++ right) [0, 1, 2] markedJoin.certificate = true ∧
    verify (left ++ right) [2, 1, 0] markedJoin.certificate = false := by
  exact ⟨markedJoin.accepted, by decide +kernel⟩

end CslibFrontierTests.CSPBoundaryAppendAcceptance
