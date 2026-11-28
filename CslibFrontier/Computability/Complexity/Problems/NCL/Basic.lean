/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs
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

* `Cslib.Complexity.NCL.ConstraintGraph.Reachable.symm`: reachability is symmetric.
* `Cslib.Complexity.NCL.Vertex.sat_and` and `Cslib.Complexity.NCL.Vertex.sat_or` express the
  weighted constraints as Boolean conditions on the three ports.

## References

* [Hearn and Demaine][HearnDemaine2005, Sections 2.1 and 2.2]
-/

public section

namespace Cslib.Complexity.NCL

variable {V V' E E' : Type*}

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

@[simp] theorem in_map (f : E → E') (p : Port E) (s : E' → Bool) :
    (p.map f).In s ↔ p.In (s ∘ f) :=
  Iff.rfl

@[simp] theorem map_map {E'' : Type*} (f : E → E') (g : E' → E'') (p : Port E) :
    (p.map f).map g = p.map (g ∘ f) :=
  rfl

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
  deriving @[expose] DecidableEq

namespace Vertex

/-- The total weight of the incident edges that point in. -/
@[expose] def inflow (v : Vertex E) (s : E → Bool) : ℕ :=
  (v.ports.map fun p => if p.port.In s then p.weight else 0).sum

/-- The in-flow constraint of the vertex holds. -/
@[expose] def Sat (v : Vertex E) (s : E → Bool) : Prop := v.minInflow ≤ v.inflow s

instance (v : Vertex E) (s : E → Bool) : Decidable (v.Sat s) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **Monotonicity**: pointing more edges in keeps the in-flow constraint. -/
theorem Sat.mono {v : Vertex E} {s t : E → Bool} (h : ∀ p ∈ v.ports, p.port.In s → p.port.In t)
    (hs : v.Sat s) : v.Sat t := by
  refine hs.trans (List.sum_le_sum fun p hp => ?_)
  by_cases hin : p.port.In s
  · simp [hin, h p hp hin]
  · simp [hin]

/-- Rename the edges of a vertex. -/
@[expose] def map (f : E → E') (v : Vertex E) : Vertex E' :=
  ⟨v.ports.map (WeightedPort.map f), v.minInflow⟩

/-- Injective edge renamings induce injective vertex renamings. -/
theorem map_injective {f : E → E'} (hf : Function.Injective f) :
    Function.Injective (Vertex.map f) := by
  rintro ⟨ps, n⟩ ⟨ps', n'⟩ h
  obtain ⟨hps, hn⟩ := Vertex.mk.inj h
  exact congrArg₂ Vertex.mk (List.map_injective_iff.mpr (WeightedPort.map_injective hf) hps) hn

@[simp] theorem map_map {E'' : Type*} (f : E → E') (g : E' → E'') (v : Vertex E) :
    (v.map f).map g = v.map (g ∘ f) := by
  simp only [map, List.map_map]
  rfl

/-- Two renamings whose composite is `h` compose to the renaming by `h`. -/
theorem map_comp_map {E'' : Type*} {f : E → E'} {g : E' → E''} {h : E → E''}
    (hgf : ∀ x, g (f x) = h x) : Vertex.map g ∘ Vertex.map f = Vertex.map h := by
  funext v
  rw [Function.comp_apply, map_map]
  exact congrArg (map · v) (funext hgf)

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

/-- An unconstrained endpoint. Listing its port keeps the incidence of a boundary wire explicit
even though the endpoint requires no in-flow. -/
@[expose] def loose (p : Port E) (weight : ℕ) : Vertex E := ⟨[⟨p, weight⟩], 0⟩

@[simp] theorem sat_loose (p : Port E) (weight : ℕ) (s : E → Bool) : (loose p weight).Sat s :=
  Nat.zero_le _

/-- A clause as a vertex: at least one of the ports points in. Assumptions such as "if `e` points
one way, then `f` points the other" are clauses, so refutations can use them like vertices. -/
@[expose] def clause (ps : List (Port E)) : Vertex E := ⟨ps.map (fun p => ⟨p, 1⟩), 1⟩

theorem sat_clause {ps : List (Port E)} {s : E → Bool} {p : Port E} (hp : p ∈ ps)
    (h : p.In s) : (clause ps).Sat s := by
  refine le_trans ?_ (List.le_sum_of_mem (List.mem_map.2
    ⟨⟨p, 1⟩, List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩))
  simp [clause, h]

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

@[simp] theorem reverse_reverse (s : E → Bool) (e : E) : reverse (reverse s e) e = s := by
  funext f
  by_cases h : f = e
  · subst h
    simp
  · simp [reverse_of_ne _ h]

/-- Reversing the image of an edge under an injection, seen through the injection. -/
theorem reverse_apply_of_injective [DecidableEq E'] {f : E → E'} (hf : Function.Injective f)
    (t : E' → Bool) (y x : E) : reverse t (f y) (f x) = reverse (t ∘ f) y x :=
  Function.update_apply_of_injective t hf y (!t (f y)) x

/-- Reversing an edge in the image of an injection commutes with restriction. -/
theorem reverse_comp_of_injective [DecidableEq E'] {f : E → E'} (hf : Function.Injective f)
    (t : E' → Bool) (y : E) : reverse t (f y) ∘ f = reverse (t ∘ f) y :=
  Function.update_comp_eq_of_injective t hf y (!t (f y))

/-- Reversing an edge commutes with renaming the edges. -/
theorem reverse_comp_equiv [DecidableEq E'] (σ : E ≃ E') (s : E' → Bool) (e : E') :
    reverse s e ∘ σ = reverse (s ∘ σ) (σ.symm e) := by
  simpa only [Equiv.apply_symm_apply] using reverse_comp_of_injective σ.injective s (σ.symm e)

end Reverse

/-- Reversing an edge outside the image of a map leaves the restriction unchanged. -/
theorem reverse_comp_of_not_mem_range [DecidableEq E'] {f : E → E'} (t : E' → Bool) {y : E'}
    (hy : ∀ x, f x ≠ y) : reverse t y ∘ f = t ∘ f :=
  Function.update_comp_eq_of_forall_ne t (!t y) hy

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

@[simp] theorem legal_map (f : E → E') (s : E' → Bool) : (G.map f).Legal s ↔ G.Legal (s ∘ f) :=
  forall_congr' fun v => Vertex.sat_map f (G v) s

/-- The configurations of two graphs placed side by side, with their edges renamed into a common
type, are those of each graph. -/
theorem legal_sumElim_map {V₁ V₂ E₁ E₂ : Type*} (G₁ : ConstraintGraph V₁ E₁)
    (G₂ : ConstraintGraph V₂ E₂) (f₁ : E₁ → E) (f₂ : E₂ → E) (s : E → Bool) :
    ConstraintGraph.Legal (Sum.elim (fun v => (G₁ v).map f₁) (fun v => (G₂ v).map f₂)) s ↔
      G₁.Legal (s ∘ f₁) ∧ G₂.Legal (s ∘ f₂) := by
  simp only [Legal, Sum.forall, Sum.elim_inl, Sum.elim_inr, Vertex.sat_map]

/-- Reindexing the vertices along a surjection keeps the configurations. -/
theorem legal_comp {τ : V' → V} (hτ : Function.Surjective τ) (s : E → Bool) :
    ConstraintGraph.Legal (G ∘ τ) s ↔ G.Legal s :=
  (hτ.forall (p := fun v => (G v).Sat s)).symm

variable {G} [DecidableEq E]

theorem Step.legal_left {s t : E → Bool} (h : G.Step s t) : G.Legal s := h.1

theorem Step.legal_right {s t : E → Bool} (h : G.Step s t) : G.Legal t := h.2.1

/-- A path from a legal configuration ends at a legal configuration, including an empty path. -/
theorem Reachable.legal {s t : E → Bool} (h : G.Reachable s t) (hs : G.Legal s) :
    G.Legal t := by
  cases h with
  | refl => exact hs
  | tail _ hst => exact hst.legal_right

/-- Every move can be undone. -/
theorem Step.symm {s t : E → Bool} (h : G.Step s t) : G.Step t s := by
  obtain ⟨hs, ht, e, rfl⟩ := h
  exact ⟨ht, hs, e, (reverse_reverse s e).symm⟩

/-- **Reversibility**: reachability is symmetric. -/
theorem Reachable.symm {s t : E → Bool} (h : G.Reachable s t) : G.Reachable t s := by
  let : Std.Symm G.Step := ⟨fun _ _ h => h.symm⟩
  exact Std.Symm.symm _ _ h

end ConstraintGraph

end Cslib.Complexity.NCL
