/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Constraint graphs from explicit weighted endpoints

Assign every edge one endpoint of each direction, a common weight, and a demand at each vertex.
An explicit edge enumeration then generates the port-list representation.

## Main definitions

* `EndpointGraph`: the endpoint, weight and demand data.
* `EndpointGraph.graph`: enumerate the incident ports at each vertex.

## Main results

* `EndpointGraph.wellFormed`: enumerating every edge exactly once gives consistent incidences.
-/

public section

namespace Cslib.Complexity.NCL

/-- A weighted graph specified by the two endpoints of every edge and the vertex demands. -/
structure EndpointGraph (V E : Type*) where
  /-- The vertex at the endpoint entered by a given orientation bit. -/
  endpoint : E → Bool → V
  /-- The common weight at the two endpoints. -/
  weight : E → ℕ
  /-- The minimum incoming weight at a vertex. -/
  demand : V → ℕ

namespace EndpointGraph

variable {V E : Type*} [DecidableEq V] (D : EndpointGraph V E)

/-- Port-list semantics generated from an explicit edge enumeration. -/
@[expose] def graph (es : List E) : ConstraintGraph V E := fun v =>
  { ports := es.flatMap fun e =>
      (if D.endpoint e false = v then [⟨⟨e, false⟩, D.weight e⟩] else []) ++
        (if D.endpoint e true = v then [⟨⟨e, true⟩, D.weight e⟩] else [])
    minInflow := D.demand v }

/-- A generated port belongs to its selected endpoint and has the edge's declared weight. -/
theorem mem_ports (es : List E) (v : V) (p : Port E) (w : ℕ) :
    ⟨p, w⟩ ∈ (D.graph es v).ports ↔
      p.edge ∈ es ∧ w = D.weight p.edge ∧ D.endpoint p.edge p.dir = v := by
  rcases p with ⟨e, b⟩
  cases b <;> simp [graph, List.mem_flatMap, WeightedPort.mk.injEq, Port.mk.injEq, and_comm]

/-- Incoming weight is the sum of edge weights whose selected endpoints equal the vertex. -/
theorem inflow (es : List E) (v : V) (s : E → Bool) :
    (D.graph es v).inflow s =
      (es.map fun e => if D.endpoint e (s e) = v then D.weight e else 0).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [graph, Vertex.inflow, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    cases hs : s e <;> by_cases hfalse : D.endpoint e false = v <;>
      by_cases htrue : D.endpoint e true = v <;>
      simp_all [Port.In]

private theorem portMultiset_eq [Fintype V] (es : List E) :
    (D.graph es).portMultiset =
      (es.map fun e => ({⟨⟨e, false⟩, D.weight e⟩} +
        {⟨⟨e, true⟩, D.weight e⟩} : Multiset (WeightedPort E))).sum := by
  induction es with
  | nil => simp [ConstraintGraph.portMultiset, graph]
  | cons e es ih =>
    simp only [ConstraintGraph.portMultiset, graph, List.flatMap_cons, List.map_cons,
      List.sum_cons, ← Multiset.coe_add, Finset.sum_add_distrib]
    change _ + _ + (D.graph es).portMultiset = _
    rw [ih]
    simp [apply_ite, eq_comm]

/-- A complete nonrepeating edge enumeration produces a well-formed constraint graph. -/
theorem wellFormed [Fintype V] [Fintype E]
    (es : List E) (hn : es.Nodup) (hc : ∀ e, e ∈ es) : (D.graph es).WellFormed := by
  classical
  refine ⟨D.weight, ?_⟩
  rw [portMultiset_eq, ← List.sum_toFinset _ hn]
  have he : es.toFinset = Finset.univ := Finset.ext fun e => by simp [hc e]
  rw [he]

/-- Distinct endpoints and a nonrepeating enumeration exclude repeated edges at a vertex. -/
theorem loopFree (es : List E) (hn : es.Nodup)
    (he : ∀ e, D.endpoint e false ≠ D.endpoint e true) : (D.graph es).LoopFree := by
  intro v
  have hp : ((D.graph es v).ports.map fun p => p.port.edge) =
      es.filter (fun e => decide (D.endpoint e false = v ∨ D.endpoint e true = v)) := by
    clear hn
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [graph, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih]
      by_cases hfalse : D.endpoint e false = v <;>
        by_cases htrue : D.endpoint e true = v
      · exact (he e (hfalse.trans htrue.symm)).elim
      · simp [hfalse, htrue]
      · simp [hfalse, htrue]
      · simp [hfalse, htrue]
  rw [hp]
  exact hn.filter _

end EndpointGraph
end Cslib.Complexity.NCL
