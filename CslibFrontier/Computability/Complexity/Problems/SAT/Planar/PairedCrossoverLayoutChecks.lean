/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.PairedCrossoverLayoutData
public import CslibFrontier.Foundations.Geometry.Orthogonal.Separation
import CslibFrontier.Foundations.Data.List.TakeQuantifiers
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip

/-!
# Finite certificates for the paired-port orthogonal crossover

Finite arithmetic certificates control the full real support of every route. The core has
57 variable vertices, 78 clause vertices and 162 incidences. Eight mutually disjoint access routes
connect the signal terminals to the boundary of `[0,240]²`; only the associated terminal may meet
an access route. An external clause uses this access and the terminal's remaining occurrence.

## Main definitions

* `Cslib.Logic.PL.CNF.PairedCrossover.clausePosition`: indexed positions of clause vertices.
* `Cslib.Logic.PL.CNF.PairedCrossover.commonEndpoints`: permitted contacts of incidence routes.

## Main results

* `Cslib.Logic.PL.CNF.PairedCrossover.incidenceRoutes_cover`: exact ordinary CNF literal incidences.
* `Cslib.Logic.PL.CNF.PairedCrossover.routes_contact_check`: finite permitted-contact certificate.
* `Cslib.Logic.PL.CNF.PairedCrossover.access_contact_check`: finite access isolation certificate.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The paired modification and its finite orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedCrossover

open Orthogonal

/-- The clause position at an index. All indices in `incidenceRoutes` are certified in range. -/
def clausePosition (i : ℕ) : Point := clausePositions.getD i (0, 0)

/-- Every variable, including both lanes on each side. -/
def variableList : List Variable :=
  [.center] ++ (List.finRange 4).flatMap (fun s =>
    (List.finRange 2).map (Variable.port s)) ++
    Crossover.internalList.flatMap fun v => List.ofFn fun i : Fin 6 => Variable.copy v i

/-- Every variable is included in the finite drawing vertex list. -/
theorem mem_variableList : ∀ v, v ∈ variableList := by decide +kernel

/-- The exact literal-incidence list of the ordinary CNF formula. -/
theorem incidenceRoutes_cover :
    incidenceRoutes.map (fun e => (e.1, e.2.1)) =
      formula.zipIdx.flatMap (fun ci => ci.1.map fun l => (ci.2, l.1)) := by
  decide +kernel

/-- The fixed formula and drawing have 78 clauses and 162 incidences. -/
theorem drawing_sizes : clausePositions.length = 78 ∧ incidenceRoutes.length = 162 := by
  decide +kernel

/-- Variable vertices have distinct positions. -/
theorem variablePosition_injective : Function.Injective variablePosition := by
  have h : (variableList.map variablePosition).Nodup := by decide +kernel
  exact fun v w => List.inj_on_of_nodup_map h (mem_variableList v) (mem_variableList w)

/-- Clause vertices are pairwise distinct. -/
theorem clausePositions_nodup : clausePositions.Nodup := by decide +kernel

/-- No clause vertex is a variable vertex. -/
theorem variablePosition_not_mem_clauses :
    ∀ v, variablePosition v ∉ clausePositions := by decide +kernel

/-- The only allowed contacts between two distinct incidence routes are shared graph endpoints. -/
def commonEndpoints (e f : ℕ × Variable × Route) : List Point :=
  (if e.1 = f.1 then [clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [variablePosition e.2.1] else [])

private def LocalSpec (e : ℕ × Variable × Route) : Prop :=
  (e.1 < 78 ∧ e.2.2.head? = some (clausePosition e.1) ∧
    e.2.2.getLast? = some (variablePosition e.2.1)) ∧
  IsOrthogonal e.2.2 ∧
  (∀ p ∈ e.2.2, 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220) ∧
  e.2.2.Nodup ∧
  ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
    segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true

private instance (e : ℕ × Variable × Route) : Decidable (LocalSpec e) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def rowCheck (e : ℕ × Variable × Route) : Bool :=
  decide (LocalSpec e) &&
  ((incidenceRoutes.all fun f => e == f ||
      routeContactCheck (commonEndpoints e f) e.2.2 f.2.2) &&
   ((variableList.all fun v => v == e.2.1 ||
      routeContactCheck [] e.2.2 [variablePosition v]) &&
    ((List.finRange 78).all fun i => i.val == e.1 ||
      routeContactCheck [] e.2.2 [clausePosition i])))

private theorem row_checked (e : ℕ × Variable × Route) (he : e ∈ incidenceRoutes) :
    rowCheck e = true := by
  suffices checked : incidenceRoutes.all rowCheck = true from List.all_eq_true.mp checked e he
  -- Six rows per kernel reduction bound the peak memory of each certificate.
  iterate 26 (refine List.all_eq_true_of_take_drop 6 (by decide +kernel) ?_)
  decide +kernel

private theorem local_checked (e : ℕ × Variable × Route) (he : e ∈ incidenceRoutes) :
    LocalSpec e := by
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every route starts at its clause and ends at its variable, with a valid clause index. -/
theorem incidence_endpoints : ∀ e ∈ incidenceRoutes,
    e.1 < 78 ∧ e.2.2.head? = some (clausePosition e.1) ∧
      e.2.2.getLast? = some (variablePosition e.2.1) :=
  fun e he => (local_checked e he).1

/-- All incidence routes have proper axis-aligned segments. -/
theorem incidence_orthogonal :
    ∀ e ∈ incidenceRoutes, IsOrthogonal e.2.2 :=
  fun e he => (local_checked e he).2.1

/-- All listed core points are inside the smaller rectangle `[20,220]²`. -/
theorem core_bounds : ∀ e ∈ incidenceRoutes, ∀ p ∈ e.2.2,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 :=
  fun e he => (local_checked e he).2.2.1

/-- Exactly 407 proper segments and 2192 units of total Manhattan wire length. -/
theorem route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum = 407 ∧
      (incidenceRoutes.map fun e => wireLength e.2.2).sum = 2192 := by decide +kernel

/-- Every incidence route lists each bend only once. -/
theorem incidence_points_nodup : ∀ e ∈ incidenceRoutes, e.2.2.Nodup :=
  fun e he => (local_checked e he).2.2.2.1

/-- Finite simplicity certificate: distinct segments are disjoint except at a shared next bend. -/
theorem incidence_simple_check : ∀ e ∈ incidenceRoutes,
    ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
      segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true :=
  fun e he => (local_checked e he).2.2.2.2

/-- Exhaustive finite contact certificate for the fixed route table. -/
theorem routes_contact_check : ∀ e ∈ incidenceRoutes, ∀ f ∈ incidenceRoutes,
    e ≠ f → routeContactCheck (commonEndpoints e f) e.2.2 f.2.2 = true := by
  intro e he f hf hne
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hf' := List.all_eq_true.mp h.2.1 f hf
  simpa only [Bool.or_eq_true, beq_iff_eq, hne, false_or] using hf'

/-- No route visits a nonincident variable vertex. -/
theorem variable_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ v,
    v ≠ e.2.1 → routeContactCheck [] e.2.2 [variablePosition v] = true := by
  intro e he v hv
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hv' := List.all_eq_true.mp h.2.2.1 v (mem_variableList v)
  simpa only [Bool.or_eq_true, beq_iff_eq, hv, false_or] using hv'

/-- No route visits a nonincident clause vertex. -/
theorem clause_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ i : Fin 78,
    i.val ≠ e.1 → routeContactCheck [] e.2.2 [clausePosition i] = true := by
  intro e he i hi
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hi' := List.all_eq_true.mp h.2.2.2 i (List.mem_finRange i)
  simpa only [Bool.or_eq_true, beq_iff_eq, hi, false_or] using hi'

/-- All eight access routes have their prescribed endpoints and proper orthogonal segments. -/
theorem access_endpoints : ∀ s l, IsOrthogonal (accessRoute s l) ∧
    (accessRoute s l).head? = some (boundaryPort s l) ∧
      (accessRoute s l).getLast? = some (variablePosition (terminal s l)) := by decide +kernel

/-- The eight access routes are mutually disjoint. -/
theorem access_disjoint_check : ∀ p q : PairedPorts.Port, p ≠ q →
    routeContactCheck [] (accessRoute p.1 p.2) (accessRoute q.1 q.2) = true :=
  PairedPorts.access_disjoint_check

/-- Access to a port can meet an incidence route only at that port. -/
theorem access_contact_check : ∀ s l, ∀ e ∈ incidenceRoutes,
    routeContactCheck (if e.2.1 = terminal s l then [variablePosition (terminal s l)] else [])
      (accessRoute s l) e.2.2 = true := by decide +kernel

end Cslib.Logic.PL.CNF.PairedCrossover
