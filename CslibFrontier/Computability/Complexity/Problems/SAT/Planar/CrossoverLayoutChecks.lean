/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.CrossoverLayoutData
public import CslibFrontier.Foundations.Geometry.Orthogonal.Separation
import CslibFrontier.Foundations.Data.List.TakeQuantifiers
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip

/-!
# Finite certificates for the fixed orthogonal crossover

Finite arithmetic certificates control the full real support of every route. The core has
53 variable vertices, 74 clause vertices and 154 incidences. Four mutually disjoint access routes
connect the signal terminals to the boundary of `[0,240]²`; only the associated terminal may meet
an access route. An external clause uses this access and the terminal's remaining occurrence.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.clausePosition`: indexed positions of clause vertices.
* `Cslib.Logic.PL.CNF.Crossover.commonEndpoints`: permitted contacts of incidence routes.

## Main results

* `Cslib.Logic.PL.CNF.Crossover.incidenceRoutes_cover`: exact ordinary CNF literal incidences.
* `Cslib.Logic.PL.CNF.Crossover.routes_contact_check`: finite permitted-contact certificate.
* `Cslib.Logic.PL.CNF.Crossover.access_contact_check`: finite access isolation certificate.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The finite orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

open Orthogonal

/-- The clause position at an index. All indices in `incidenceRoutes` are certified in range. -/
def clausePosition (i : ℕ) : Point := clausePositions.getD i (0, 0)

/-- All variable names, with each local six-copy block listed in order. -/
def splitVariables : List SplitVariable :=
  [.aLeft, .aRight, .bTop, .bBottom, .center] ++
    internalList.flatMap fun v => List.ofFn fun i : Fin 6 => SplitVariable.copy v i

/-- Every variable name is included in the explicit finite vertex list. -/
theorem mem_splitVariables (v : SplitVariable) : v ∈ splitVariables := by
  cases v with
  | aLeft | aRight | bTop | bBottom | center => decide
  | copy v i =>
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨v, mem_internalList v, List.mem_ofFn.mpr ⟨i, rfl⟩⟩

/-- The exact literal-incidence list of the ordinary CNF formula. -/
theorem incidenceRoutes_cover :
    incidenceRoutes.map (fun e => (e.1, e.2.1)) =
      splitFormula.zipIdx.flatMap (fun ci => ci.1.map fun l => (ci.2, l.1)) := by
  decide +kernel

/-- The fixed formula and drawing have 74 clauses and 154 incidences. -/
theorem drawing_sizes : clausePositions.length = 74 ∧ incidenceRoutes.length = 154 := by
  decide +kernel

/-- Variable vertices have distinct positions. -/
theorem variablePosition_injective : Function.Injective variablePosition := by
  have h : (splitVariables.map variablePosition).Nodup := by decide +kernel
  exact fun v w => List.inj_on_of_nodup_map h (mem_splitVariables v) (mem_splitVariables w)

/-- Clause vertices are pairwise distinct. -/
theorem clausePositions_nodup : clausePositions.Nodup := by decide +kernel

/-- No clause vertex is a variable vertex. -/
theorem variablePosition_not_mem_clauses :
    ∀ v, variablePosition v ∉ clausePositions := by decide +kernel

/-- The only allowed contacts between two distinct incidence routes are shared graph endpoints. -/
def commonEndpoints (e f : ℕ × SplitVariable × Route) : List Point :=
  (if e.1 = f.1 then [clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [variablePosition e.2.1] else [])

private def LocalSpec (e : ℕ × SplitVariable × Route) : Prop :=
  (e.1 < 74 ∧ e.2.2.head? = some (clausePosition e.1) ∧
    e.2.2.getLast? = some (variablePosition e.2.1)) ∧
  IsOrthogonal e.2.2 ∧
  (∀ p ∈ e.2.2, 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220) ∧
  e.2.2.Nodup ∧
  ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
    segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true

private instance (e : ℕ × SplitVariable × Route) : Decidable (LocalSpec e) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def rowCheck (e : ℕ × SplitVariable × Route) : Bool :=
  decide (LocalSpec e) &&
  ((incidenceRoutes.all fun f => e == f ||
      routeContactCheck (commonEndpoints e f) e.2.2 f.2.2) &&
   ((splitVariables.all fun v => v == e.2.1 ||
      routeContactCheck [] e.2.2 [variablePosition v]) &&
    ((List.finRange 74).all fun i => i.val == e.1 ||
      routeContactCheck [] e.2.2 [clausePosition i])))

private theorem row_checked (e : ℕ × SplitVariable × Route) (he : e ∈ incidenceRoutes) :
    rowCheck e = true := by
  suffices checked : incidenceRoutes.all rowCheck = true from List.all_eq_true.mp checked e he
  -- Six rows per kernel reduction bound the peak memory of each certificate.
  iterate 25 (refine List.all_eq_true_of_take_drop 6 (by decide +kernel) ?_)
  decide +kernel

private theorem local_checked (e : ℕ × SplitVariable × Route) (he : e ∈ incidenceRoutes) :
    LocalSpec e := by
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every route starts at its clause and ends at its variable, with a valid clause index. -/
theorem incidence_endpoints : ∀ e ∈ incidenceRoutes,
    e.1 < 74 ∧ e.2.2.head? = some (clausePosition e.1) ∧
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

/-- Exactly 410 proper segments and 2116 units of total Manhattan wire length. -/
theorem route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum = 410 ∧
      (incidenceRoutes.map fun e => wireLength e.2.2).sum = 2116 := by decide +kernel

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
  have hv' := List.all_eq_true.mp h.2.2.1 v (mem_splitVariables v)
  simpa only [Bool.or_eq_true, beq_iff_eq, hv, false_or] using hv'

/-- No route visits a nonincident clause vertex. -/
theorem clause_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ i : Fin 74,
    i.val ≠ e.1 → routeContactCheck [] e.2.2 [clausePosition i] = true := by
  intro e he i hi
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hi' := List.all_eq_true.mp h.2.2.2 i (List.mem_finRange i)
  simpa only [Bool.or_eq_true, beq_iff_eq, hi, false_or] using hi'

/-- Four orthogonal access routes, each with its prescribed endpoints. -/
theorem access_endpoints : ∀ i, IsOrthogonal (accessRoute i) ∧
    (accessRoute i).head? = some (boundaryPort i) ∧
      (accessRoute i).getLast? = some (variablePosition (splitTerminal i)) := by decide +kernel

/-- The four access routes are mutually disjoint. -/
theorem access_disjoint_check : ∀ i j, i ≠ j →
    routeContactCheck [] (accessRoute i) (accessRoute j) = true := by decide +kernel

/-- Access to a terminal can meet an incidence route only at that terminal. -/
theorem access_contact_check : ∀ i, ∀ e ∈ incidenceRoutes,
    routeContactCheck (if e.2.1 = splitTerminal i then [variablePosition (splitTerminal i)] else [])
      (accessRoute i) e.2.2 = true := by decide +kernel

end Cslib.Logic.PL.CNF.Crossover
