/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.GeometryData
public import CslibFrontier.Foundations.Geometry.Orthogonal.Separation
public import CslibFrontier.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Pi

/-!
# Local incidence drawing certificates

`LocalGeometry.Check` certifies finite endpoints, simplicity, contacts and access isolation.
`LocalGeometry.RowCheck` and `LocalGeometry.check_of_rows` allow independent row certificates.
The continuous consequences apply to both ordinary CNF and exact-one gadget drawings.
These arithmetic and continuous certificates are original and assert no clause semantics.
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Orthogonal

namespace LocalGeometry

/-- Common listed endpoints of two segments are the permitted self-contacts. -/
def segmentEndpoints (a b : Point × Point) : List Point :=
  ([a.1, a.2].filter fun p => p = b.1 ∨ p = b.2)

/-- A decidable finite simplicity certificate for an individual polygonal route. -/
def SimpleCheck (r : Route) : Prop :=
  r.Nodup ∧ ∀ a ∈ r.consecutivePairs, ∀ b ∈ r.consecutivePairs, a ≠ b →
    segmentContactCheck (segmentEndpoints a b) a.1 a.2 b.1 b.2 = true

instance (r : Route) : Decidable (SimpleCheck r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The finite certificate refers to graph endpoints, complete routes, and all exterior
accesses. The core lies strictly inside the square cell of side `g.size`. -/
def Check (g : LocalGeometry) : Prop :=
  (g.variablePositions ++ g.clausePositions).Nodup ∧
  (g.incidenceRoutes.map fun e => (e.clauseIndex, e.variableIndex)).Nodup ∧
  g.accessRoutes.length = g.terminalVariables.length ∧
  g.accessRoutes.length = g.boundaryPorts.length ∧
  (∀ e ∈ g.incidenceRoutes,
    e.clauseIndex < g.clausePositions.length ∧ e.variableIndex < g.variablePositions.length ∧
      e.route.head? = some (g.clausePosition e.clauseIndex) ∧
      e.route.getLast? = some (g.variablePosition e.variableIndex) ∧
      IsOrthogonal e.route ∧ SimpleCheck e.route ∧
      ∀ p ∈ e.route, 20 ≤ p.1 ∧ p.1 ≤ (g.size : ℤ) - 20 ∧
        20 ≤ p.2 ∧ p.2 ≤ (g.size : ℤ) - 20) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ f ∈ g.incidenceRoutes, e ≠ f →
    routeContactCheck (g.commonEndpoints e f) e.route f.route = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ v : Fin g.variablePositions.length, v.val ≠ e.variableIndex →
    routeContactCheck [] e.route [g.variablePosition v] = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ i : Fin g.clausePositions.length, i.val ≠ e.clauseIndex →
    routeContactCheck [] e.route [g.clausePosition i] = true) ∧
  (∀ i : Fin g.accessRoutes.length,
    let r := g.accessRoutes.getD i []
    let v := g.terminalVariables.getD i 0
    v < g.variablePositions.length ∧
      r.head? = some (g.boundaryPorts.getD i (0, 0)) ∧
      r.getLast? = some (g.variablePosition v) ∧
      IsOrthogonal r ∧ SimpleCheck r ∧
      (∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ g.size ∧ 0 ≤ p.2 ∧ p.2 ≤ g.size) ∧
      (∀ p ∈ r.tail, 0 < p.1 ∧ p.1 < g.size ∧ 0 < p.2 ∧ p.2 < g.size) ∧
      (∀ e ∈ g.incidenceRoutes,
        routeContactCheck (if e.variableIndex = v then [g.variablePosition v] else [])
          r e.route = true) ∧
      (∀ j : Fin g.accessRoutes.length, i ≠ j →
        routeContactCheck [] r (g.accessRoutes.getD j []) = true) ∧
      (∀ w : Fin g.variablePositions.length, w.val ≠ v →
        routeContactCheck [] r [g.variablePosition w] = true) ∧
      ∀ p ∈ g.clausePositions, routeContactCheck [] r [p] = true)

/-- The checks belonging to one incidence row. Keeping these separate permits one
kernel certificate per route rather than reducing the whole drawing at once. -/
def RowCheck (g : LocalGeometry) (e : LocalIncidence) : Prop :=
  (e.clauseIndex < g.clausePositions.length ∧ e.variableIndex < g.variablePositions.length ∧
      e.route.head? = some (g.clausePosition e.clauseIndex) ∧
      e.route.getLast? = some (g.variablePosition e.variableIndex) ∧
      IsOrthogonal e.route ∧ SimpleCheck e.route ∧
      ∀ p ∈ e.route, 20 ≤ p.1 ∧ p.1 ≤ (g.size : ℤ) - 20 ∧
        20 ≤ p.2 ∧ p.2 ≤ (g.size : ℤ) - 20) ∧
  (∀ f ∈ g.incidenceRoutes, e ≠ f →
    routeContactCheck (g.commonEndpoints e f) e.route f.route = true) ∧
  (∀ v : Fin g.variablePositions.length, v.val ≠ e.variableIndex →
    routeContactCheck [] e.route [g.variablePosition v] = true) ∧
  (∀ i : Fin g.clausePositions.length, i.val ≠ e.clauseIndex →
    routeContactCheck [] e.route [g.clausePosition i] = true)

instance (g : LocalGeometry) (e : LocalIncidence) : Decidable (RowCheck g e) := by
  unfold RowCheck
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- Assemble the unchanged complete check from independently certified incidence rows.
Access isolation remains a separate obligation, including every nonincident vertex. -/
theorem check_of_rows {g : LocalGeometry}
    (vertices : (g.variablePositions ++ g.clausePositions).Nodup)
    (incidences : (g.incidenceRoutes.map fun e => (e.clauseIndex, e.variableIndex)).Nodup)
    (terminals : g.accessRoutes.length = g.terminalVariables.length)
    (ports : g.accessRoutes.length = g.boundaryPorts.length)
    (rows : ∀ e ∈ g.incidenceRoutes, RowCheck g e)
    (accesses : ∀ i : Fin g.accessRoutes.length,
    let r := g.accessRoutes.getD i []
    let v := g.terminalVariables.getD i 0
    v < g.variablePositions.length ∧
      r.head? = some (g.boundaryPorts.getD i (0, 0)) ∧
      r.getLast? = some (g.variablePosition v) ∧
      IsOrthogonal r ∧ SimpleCheck r ∧
      (∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ g.size ∧ 0 ≤ p.2 ∧ p.2 ≤ g.size) ∧
      (∀ p ∈ r.tail, 0 < p.1 ∧ p.1 < g.size ∧ 0 < p.2 ∧ p.2 < g.size) ∧
      (∀ e ∈ g.incidenceRoutes,
        routeContactCheck (if e.variableIndex = v then [g.variablePosition v] else [])
          r e.route = true) ∧
      (∀ j : Fin g.accessRoutes.length, i ≠ j →
        routeContactCheck [] r (g.accessRoutes.getD j []) = true) ∧
      (∀ w : Fin g.variablePositions.length, w.val ≠ v →
        routeContactCheck [] r [g.variablePosition w] = true) ∧
      ∀ p ∈ g.clausePositions, routeContactCheck [] r [p] = true) : Check g :=
  ⟨vertices, incidences, terminals, ports, (fun e he => (rows e he).1),
    (fun e he => (rows e he).2.1), (fun e he => (rows e he).2.2.1),
    (fun e he => (rows e he).2.2.2), accesses⟩

instance (g : LocalGeometry) : Decidable (Check g) := by
  unfold Check
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- The finite simplicity certificate controls full real segment intersections. -/
theorem isSimple_of_check {r : Route} (h : SimpleCheck r) : IsSimple r := by
  refine ⟨h.1, ?_⟩
  intro a ha b hb hne p hp hq
  obtain ⟨q, hq, hpq⟩ := segmentContactCheck_sound (h.2 a ha b hb hne) hp hq
  have hq' := List.mem_filter.mp hq
  have hqa : q = a.1 ∨ q = a.2 := by simpa using hq'.1
  have hqb : q = b.1 ∨ q = b.2 := by simpa using hq'.2
  exact ⟨hqa.elim (fun h => Or.inl (h ▸ hpq)) (fun h => Or.inr (h ▸ hpq)),
    hqb.elim (fun h => Or.inl (h ▸ hpq)) (fun h => Or.inr (h ▸ hpq))⟩

/-- Every checked incidence has its prescribed clause and variable endpoints. -/
theorem incidence_endpoints {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) :
    e.clauseIndex < g.clausePositions.length ∧ e.variableIndex < g.variablePositions.length ∧
      e.route.head? = some (g.clausePosition e.clauseIndex) ∧
      e.route.getLast? = some (g.variablePosition e.variableIndex) := by
  have he' := h.2.2.2.2.1 e he
  exact ⟨he'.1, he'.2.1, he'.2.2.1, he'.2.2.2.1⟩

/-- Every checked incidence is properly orthogonal. -/
theorem incidence_orthogonal {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsOrthogonal e.route :=
  (h.2.2.2.2.1 e he).2.2.2.2.1

/-- Every checked incidence is simple over its full continuous support. -/
theorem incidence_isSimple {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsSimple e.route :=
  isSimple_of_check (h.2.2.2.2.1 e he).2.2.2.2.2.1

/-- Checked incidence routes can meet only at a shared clause or variable vertex. -/
theorem routes_contact {g : LocalGeometry} (h : Check g)
    {e f : LocalIncidence} (he : e ∈ g.incidenceRoutes) (hf : f ∈ g.incidenceRoutes)
    (hne : e ≠ f) {p : ℝ × ℝ} (hp : p ∈ support e.route) (hq : p ∈ support f.route) :
    ∃ q ∈ g.commonEndpoints e f, p = realPoint q :=
  routeContactCheck_sound (h.2.2.2.2.2.1 e he f hf hne) hp hq

/-- Checked incidences avoid every nonincident variable vertex. -/
theorem variable_not_mem_support {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {v : Fin g.variablePositions.length} (hv : v.val ≠ e.variableIndex) :
    realPoint (g.variablePosition v) ∉ support e.route :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.2.2.1 e he v hv)

/-- Checked incidences avoid every nonincident clause vertex. -/
theorem clause_not_mem_support {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {i : Fin g.clausePositions.length} (hi : i.val ≠ e.clauseIndex) :
    realPoint (g.clausePosition i) ∉ support e.route :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.2.2.2.1 e he i hi)

/-- Exterior access routes are simple over their full continuous support. -/
theorem access_isSimple {g : LocalGeometry} (h : Check g) (i : Fin g.accessRoutes.length) :
    IsSimple (g.accessRoutes.getD i []) :=
  isSimple_of_check (h.2.2.2.2.2.2.2.2 i).2.2.2.2.1

/-- Distinct checked accesses have disjoint full real supports. -/
theorem access_disjoint {g : LocalGeometry} (h : Check g)
    {i j : Fin g.accessRoutes.length} (hne : i ≠ j) :
    Disjoint (support (g.accessRoutes.getD i [])) (support (g.accessRoutes.getD j [])) :=
  disjoint_support_of_routeContactCheck
    ((h.2.2.2.2.2.2.2.2 i).2.2.2.2.2.2.2.2.1 j hne)

/-- A checked access meets the core only at its corresponding terminal. -/
theorem access_contact {g : LocalGeometry} (h : Check g)
    {i : Fin g.accessRoutes.length} {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support (g.accessRoutes.getD i []))
    (hq : p ∈ support e.route) :
    e.variableIndex = g.terminalVariables.getD i 0 ∧
      p = realPoint (g.variablePosition (g.terminalVariables.getD i 0)) :=
  routeContactCheck_ite_sound ((h.2.2.2.2.2.2.2.2 i).2.2.2.2.2.2.2.1 e he) hp hq

end LocalGeometry

end Cslib.Complexity.SAT
