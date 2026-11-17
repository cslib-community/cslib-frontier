/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal

/-!
# Local orthogonal incidence drawings

`LocalIncidence` names the clause index, variable index and route.
`LocalGeometry` records finite vertex, incidence and exterior-access data without clause semantics.
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Orthogonal

/-- An incidence records its clause index, variable index, and clause-to-variable route. -/
abbrev LocalIncidence := ℕ × ℕ × Route

namespace LocalIncidence

/-- The local index of the incident clause. -/
abbrev clauseIndex (e : LocalIncidence) : ℕ := e.1

/-- The local index of the incident variable. -/
abbrev variableIndex (e : LocalIncidence) : ℕ := e.2.1

/-- The route from the clause position to the variable position. -/
abbrev route (e : LocalIncidence) : Route := e.2.2

end LocalIncidence

/-- Finite local replacement data. Variables and clauses have separate zero-based indices.
`terminalVariables`, `boundaryPorts`, and `accessRoutes` have corresponding orders. -/
structure LocalGeometry where
  /-- Common square side length; the elementary templates use 180. -/
  size : ℕ := 180
  /-- Positions in variable-index order. -/
  variablePositions : List Point
  /-- Positions in clause-index order. -/
  clausePositions : List Point
  /-- Routes with their incident clause and variable indices. -/
  incidenceRoutes : List LocalIncidence
  /-- Variables exposed to the exterior. -/
  terminalVariables : List ℕ
  /-- Exterior endpoints of the access routes. -/
  boundaryPorts : List Point
  /-- Boundary-to-terminal routes. -/
  accessRoutes : List Route

namespace LocalGeometry

/-- Indexed variable position; valid incidence indices are certified separately. -/
def variablePosition (g : LocalGeometry) (v : ℕ) : Point :=
  g.variablePositions.getD v (0, 0)

/-- Indexed clause position; valid incidence indices are certified separately. -/
def clausePosition (g : LocalGeometry) (i : ℕ) : Point :=
  g.clausePositions.getD i (0, 0)

/-- Permitted contacts of two incidence routes: their shared graph endpoints. -/
def commonEndpoints (g : LocalGeometry) (e f : LocalIncidence) : List Point :=
  (if e.clauseIndex = f.clauseIndex then [g.clausePosition e.clauseIndex] else []) ++
    (if e.variableIndex = f.variableIndex then [g.variablePosition e.variableIndex] else [])

end LocalGeometry

end Cslib.Complexity.SAT
