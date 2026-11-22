/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Nondeterministic constraint logic

An orientation gives each edge one bit. A weighted port contributes to its vertex's inflow when
the bit agrees with the port's direction. A legal move flips one edge and preserves every
vertex's minimum inflow. AND vertices have incident weights 1, 1, 2 and OR vertices have weights
2, 2, 2. Both require inflow at least two.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.Legal`, `Cslib.Complexity.NCL.ConstraintGraph.Step`,
  `Cslib.Complexity.NCL.ConstraintGraph.Reachable` and
  `Cslib.Complexity.NCL.ConstraintGraph.CanReverse`.

## Main results

* `Cslib.Complexity.NCL.Vertex.sat_and` and `Cslib.Complexity.NCL.Vertex.sat_or` express the
  weighted constraints as Boolean conditions on the three ports.

## References

* [Hearn and Demaine][HearnDemaine2005, Sections 2.1 and 2.2]
-/

public section

namespace Cslib.Complexity.NCL

variable {V E E' : Type*}

/-- An edge seen from one of its endpoints: the edge points into this endpoint when its
orientation bit equals `dir`. -/
structure Port (E : Type*) where
  /-- The edge. -/
  edge : E
  /-- The orientation bit with which the edge points into this endpoint. -/
  dir : Bool
  deriving @[expose] DecidableEq

namespace Port

/-- The edge points into this endpoint. -/
@[expose] def In (p : Port E) (s : E → Bool) : Prop := s p.edge = p.dir

instance (p : Port E) (s : E → Bool) : Decidable (p.In s) :=
  inferInstanceAs (Decidable (s p.edge = p.dir))

/-- Rename the edge of a port. -/
@[expose] def map (f : E → E') (p : Port E) : Port E' := ⟨f p.edge, p.dir⟩

end Port

/-- A port together with the edge weight it contributes to inflow when directed inward. -/
structure WeightedPort (E : Type*) where
  /-- The incident edge and the direction in which it points into the vertex. -/
  port : Port E
  /-- The edge weight. -/
  weight : ℕ
  deriving @[expose] DecidableEq

/-- Rename the edge of a weighted port, preserving its direction and weight. -/
@[expose] def WeightedPort.map (f : E → E') (p : WeightedPort E) : WeightedPort E' :=
  ⟨p.port.map f, p.weight⟩

/-- Injective edge renaming is injective on weighted ports. -/
theorem WeightedPort.map_injective {f : E → E'} (hf : Function.Injective f) :
    Function.Injective (WeightedPort.map f) := by
  rintro ⟨⟨e, d⟩, w⟩ ⟨⟨e', d'⟩, w'⟩ h
  simp only [WeightedPort.map, Port.map, WeightedPort.mk.injEq, Port.mk.injEq] at h
  obtain ⟨⟨hedge, rfl⟩, rfl⟩ := h
  rw [hf hedge]

/-- A vertex of a constraint graph [HearnDemaine2005, Section 2.1]: its incident edges, as ports
with weights, and its minimum in-flow. -/
structure Vertex (E : Type*) where
  /-- The incident edges, as ports, each with its weight. -/
  ports : List (WeightedPort E)
  /-- The minimum in-flow. -/
  minInflow : ℕ

namespace Vertex

/-- The total weight of the incident edges that point in. -/
@[expose] def inflow (v : Vertex E) (s : E → Bool) : ℕ :=
  (v.ports.map fun p => if p.port.In s then p.weight else 0).sum

/-- The in-flow constraint of the vertex holds. -/
@[expose] def Sat (v : Vertex E) (s : E → Bool) : Prop := v.minInflow ≤ v.inflow s

instance (v : Vertex E) (s : E → Bool) : Decidable (v.Sat s) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Rename the edges of a vertex. -/
@[expose] def map (f : E → E') (v : Vertex E) : Vertex E' :=
  ⟨v.ports.map (WeightedPort.map f), v.minInflow⟩

@[simp] theorem sat_map (f : E → E') (v : Vertex E) (s : E' → Bool) :
    (v.map f).Sat s ↔ v.Sat (s ∘ f) := by
  simp only [Sat, map, inflow, List.map_map]
  rfl

/-- An AND vertex [HearnDemaine2005, Section 2.2]: red edges `a`, `b` of weight one, a blue
edge `c` of weight two, and minimum in-flow two. -/
@[expose] def and (a b c : Port E) : Vertex E := ⟨[⟨a, 1⟩, ⟨b, 1⟩, ⟨c, 2⟩], 2⟩

/-- An OR vertex [HearnDemaine2005, Section 2.2]: three blue edges of weight two, and minimum
in-flow two. -/
@[expose] def or (a b c : Port E) : Vertex E := ⟨[⟨a, 2⟩, ⟨b, 2⟩, ⟨c, 2⟩], 2⟩

/-- The blue edge of an AND vertex may point out exactly when both red edges point in. -/
@[simp] theorem sat_and (a b c : Port E) (s : E → Bool) :
    (and a b c).Sat s ↔ c.In s ∨ a.In s ∧ b.In s := by
  by_cases ha : a.In s <;> by_cases hb : b.In s <;> by_cases hc : c.In s <;>
    simp [Sat, inflow, and, ha, hb, hc]

/-- An edge of an OR vertex may point out exactly when another one points in. -/
@[simp] theorem sat_or (a b c : Port E) (s : E → Bool) :
    (or a b c).Sat s ↔ a.In s ∨ b.In s ∨ c.In s := by
  by_cases ha : a.In s <;> by_cases hb : b.In s <;> by_cases hc : c.In s <;>
    simp [Sat, inflow, or, ha, hb, hc]

/-- Vertices with the same minimum in-flow whose ports are the same up to order have the same
constraint. -/
theorem sat_iff_of_perm {v w : Vertex E} (hp : v.ports.Perm w.ports)
    (hm : v.minInflow = w.minInflow) (s : E → Bool) : v.Sat s ↔ w.Sat s := by
  rw [Sat, Sat, inflow, inflow, hm, (hp.map _).sum_nat]

/-- The vertex is an AND vertex, up to the order of its ports. -/
@[expose] def IsAnd (v : Vertex E) : Prop :=
  ∃ a b c, v.minInflow = 2 ∧ v.ports.Perm (and a b c).ports

/-- The vertex is an OR vertex, up to the order of its ports. -/
@[expose] def IsOr (v : Vertex E) : Prop :=
  ∃ a b c, v.minInflow = 2 ∧ v.ports.Perm (or a b c).ports

/-- The vertex is an AND or an OR vertex, up to the order of its ports. A diagram lists the ports
of a vertex in drawing order, so its AND and OR vertices are such vertices
[HearnDemaine2005, Section 2.2]. -/
@[expose] def IsAndOr (v : Vertex E) : Prop := v.IsAnd ∨ v.IsOr

end Vertex

/-- Reverse the edge `e`. -/
@[expose]
def reverse [DecidableEq E] (s : E → Bool) (e : E) : E → Bool := Function.update s e (!s e)

section Reverse

variable [DecidableEq E]

@[simp] theorem reverse_self (s : E → Bool) (e : E) : reverse s e e = !s e := by
  simp [reverse]

theorem reverse_of_ne (s : E → Bool) {e f : E} (h : f ≠ e) : reverse s e f = s f := by
  simp [reverse, h]

end Reverse

/-- A constraint graph [HearnDemaine2005, Section 2.1]: every vertex in `V` with its incident
edges among `E`. -/
abbrev ConstraintGraph (V E : Type*) := V → Vertex E

namespace ConstraintGraph

variable (G : ConstraintGraph V E)

/-- A configuration: an orientation satisfying every in-flow constraint. -/
@[expose] def Legal (s : E → Bool) : Prop := ∀ v, (G v).Sat s

instance [Fintype V] (s : E → Bool) : Decidable (G.Legal s) :=
  inferInstanceAs (Decidable (∀ v, (G v).Sat s))

/-- A move: the reversal of one edge between two configurations. -/
@[expose]
def Step [DecidableEq E] (s t : E → Bool) : Prop := G.Legal s ∧ G.Legal t ∧ ∃ e, t = reverse s e

/-- Reflexive-transitive closure of legal moves on orientations. The empty sequence relates
each orientation to itself. The decision problems require legality of the initial orientation. -/
abbrev Reachable [DecidableEq E] : (E → Bool) → (E → Bool) → Prop := Relation.ReflTransGen G.Step

/-- From the configuration `s`, the edge `e` can eventually be reversed: the
configuration-to-edge question of [HearnDemaine2005, Section 2.1]. -/
@[expose]
def CanReverse [DecidableEq E] (s : E → Bool) (e : E) : Prop := ∃ t, G.Reachable s t ∧ t e ≠ s e

/-- Every vertex is an AND or an OR vertex. -/
@[expose] def IsAndOr : Prop := ∀ v, (G v).IsAndOr

/-- Rename the edges of a constraint graph. -/
@[expose] def map (f : E → E') : ConstraintGraph V E' := fun v => (G v).map f

variable {G} [DecidableEq E]

theorem Step.legal_left {s t : E → Bool} (h : G.Step s t) : G.Legal s := h.1

theorem Step.legal_right {s t : E → Bool} (h : G.Step s t) : G.Legal t := h.2.1

end ConstraintGraph

end Cslib.Complexity.NCL
