/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Assembly.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import Mathlib.Data.Fintype.Sigma

/-!
# Replacing vertices in an arbitrary constraint graph

A replacement shares the original edge names and has its own private edges. Taking the disjoint
union of the private edges produces an ordinary constraint graph. The assembly theorem schedules
the preparations and cleanups on both ends of a shared edge.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.Replacement.component`: a local graph as a component.
* `Cslib.Complexity.NCL.ConstraintGraph.Replacement.graph`: the substituted graph.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.Replacement.simulation`: global graph substitution.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph.Replacement

open Relation
open scoped BigOperators

universe u v w z
variable {V : Type u} {E : Type v} {I : V → Type w} {W : V → Type z}
variable [∀ v, DecidableEq (I v)]

/-- An open graph with global boundary names on the left and private names on the right. -/
@[expose] def component {J : Type w} {U : Type z} (H : ConstraintGraph U (E ⊕ J)) [DecidableEq J] :
    Component E where
  State := J → Bool
  Legal s x := H.Legal (Sum.elim s x)
  InnerStep _ x y := ∃ e, y = reverse x e

/-- Replace every old vertex by a local graph, retaining the old boundary edges. -/
@[expose] def graph (H : (v : V) → ConstraintGraph (W v) (E ⊕ I v)) :
    ConstraintGraph (Σ v, W v) (E ⊕ Σ v, I v) :=
  fun ⟨v, w⟩ => (H v w).map (Sum.map id (Sigma.mk v))

/-- The product of the local replacement components. -/
@[expose] def model (H : (v : V) → ConstraintGraph (W v) (E ⊕ I v)) : Assembly.Model V E :=
  ⟨fun v => component (H v)⟩

/-- Assemble the shared boundary and all private orientations. -/
@[expose] def pack (H : (v : V) → ConstraintGraph (W v) (E ⊕ I v))
    (x : (model H).State) : E ⊕ (Σ v, I v) → Bool :=
  Sum.elim x.boundary (fun ⟨v, e⟩ => x.inner v e)

/-- Read a graph orientation as its shared boundary and local private orientations. -/
@[expose] def unpack (H : (v : V) → ConstraintGraph (W v) (E ⊕ I v))
    (s : E ⊕ (Σ v, I v) → Bool) : (model H).State :=
  ⟨fun e => s (.inl e), fun v e => s (.inr ⟨v, e⟩)⟩

end Cslib.Complexity.NCL.ConstraintGraph.Replacement

end

public section

namespace Cslib.Complexity.NCL.ConstraintGraph.Replacement

open Relation
open scoped BigOperators

universe u v w z
variable {V : Type u} {E : Type v} {I : V → Type w} {W : V → Type z}
variable (H : (v : V) → ConstraintGraph (W v) (E ⊕ I v))

/-- Replacing vertices by AND/OR graphs gives an AND/OR graph. -/
theorem isAndOr (h : ∀ v, (H v).IsAndOr) : (graph H).IsAndOr :=
  fun ⟨v, w⟩ => (h v w).map _

/-- Private edge labels are disjoint, so loop-free replacements give a loop-free whole graph. -/
theorem loopFree (h : ∀ v, (H v).LoopFree) : (graph H).LoopFree := by
  intro ⟨v, w⟩
  exact ((h v).map (Function.injective_id.sumMap sigma_mk_injective)) w

/-- The ports of a replacement graph are the disjoint union of its renamed local ports. -/
theorem portMultiset_graph [Fintype V] [∀ v, Fintype (W v)] :
    (graph H).portMultiset =
      ∑ v, Multiset.map (WeightedPort.map (Sum.map id (Sigma.mk v))) (H v).portMultiset := by
  rw [ConstraintGraph.portMultiset, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  change ((H v).map (Sum.map id (Sigma.mk v))).portMultiset = _
  exact ConstraintGraph.portMultiset_map _ _

variable [∀ v, DecidableEq (I v)]

/-- Global legality is the conjunction of the local replacement constraints. -/
theorem legal_iff (s : E ⊕ (Σ v, I v) → Bool) :
    (graph H).Legal s ↔ (model H).Legal (unpack H s) := by
  simp only [graph, ConstraintGraph.Legal, Vertex.sat_map, Assembly.Model.Legal,
    model, component, unpack]
  have heq (v : V) : s ∘ Sum.map id (Sigma.mk v) =
      Sum.elim (fun e => s (.inl e)) (fun e => s (.inr ⟨v, e⟩)) := by
    funext e
    cases e <;> rfl
  constructor
  · intro h v w
    simpa only [heq] using h ⟨v, w⟩
  · intro h ⟨v, w⟩
    simpa only [heq] using h v w

private theorem unpack_pack (x : (model H).State) : unpack H (pack H x) = x := by
  cases x
  rfl

private theorem legal_pack (x : (model H).State) :
    (graph H).Legal (pack H x) ↔ (model H).Legal x := by
  rw [legal_iff, unpack_pack]

variable [DecidableEq E] [DecidableEq V]

private theorem pack_flip (s : E → Bool) (x : (v : V) → I v → Bool) (e : E) :
    pack H ⟨reverse s e, x⟩ = reverse (pack H ⟨s, x⟩) (.inl e) := by
  funext y
  rcases y with f | ⟨v, f⟩ <;> simp [pack, reverse, Function.update]

private theorem pack_inner (s : E → Bool) (x : (v : V) → I v → Bool)
    (v : V) (e : I v) :
    pack H ⟨s, Function.update x v (reverse (x v) e)⟩ =
      reverse (pack H ⟨s, x⟩) (.inr ⟨v, e⟩) := by
  funext y
  rcases y with f | ⟨w, f⟩
  · simp [pack, reverse, Function.update]
  · by_cases hw : w = v
    · subst w
      simp [pack, reverse, Function.update]
    · have hne : (⟨w, f⟩ : Σ v, I v) ≠ ⟨v, e⟩ :=
        fun h => hw (congrArg Sigma.fst h)
      simp [pack, reverse, Function.update, hw, hne]

private theorem step_pack {x y : (model H).State} (h : (model H).Step x y) :
    (graph H).Step (pack H x) (pack H y) := by
  obtain ⟨hx, hy⟩ := Assembly.Model.Step.legal _ h
  refine ⟨(legal_pack H x).2 hx, (legal_pack H y).2 hy, ?_⟩
  cases h with
  | flip s x e _ _ => exact ⟨.inl e, pack_flip H s x e⟩
  | inner s x v y _ hm =>
    obtain ⟨e, rfl⟩ := hm.2.2
    exact ⟨.inr ⟨v, e⟩, pack_inner H s x v e⟩

/-- Certified vertex replacements compose into a simulation of ordinary constraint graphs. -/
def simulation [Fintype V] (G : ConstraintGraph V E)
    (real : ∀ v, Realizes (component (H v)) (G v)) :
    ConstraintGraph.Simulation G (graph H) where
  abs s e := s (.inl e)
  enc s := pack H ((model H).canon G real s)
  abs_enc _ := rfl
  legal_abs hs v := (real v).sound ((legal_iff H _).1 hs v)
  legal_enc hs := (legal_pack H _).2 (fun v => (real v).legal_canon (hs v))
  step_abs {s t} h := by
    obtain ⟨hs, ht, e, rfl⟩ := h
    have hsrc : G.Legal (fun e => s (.inl e)) := fun v =>
      (real v).sound ((legal_iff H s).1 hs v)
    have htgt : G.Legal (fun f => reverse s e (.inl f)) := fun v =>
      (real v).sound ((legal_iff H _).1 ht v)
    cases e with
    | inl e =>
      exact .single ⟨hsrc, htgt, e, by funext f; simp [reverse, Function.update]⟩
    | inr e =>
      have heq : (fun f => reverse s (.inr e) (.inl f)) = (fun f => s (.inl f)) := by
        funext f
        exact reverse_of_ne s (by simp)
      rw [heq]
  step_enc {s t} h := by
    have hp := ((model H).simulation G real).step_enc h
    exact ReflTransGen.lift' (pack H) (fun _ _ hm => .single (step_pack H hm.2)) _ _ hp

/-- Every source edge is retained as a shared edge of the replacement graph. -/
theorem simulation_abs [Fintype V] (G : ConstraintGraph V E)
    (real : ∀ v, Realizes (component (H v)) (G v))
    (s : E ⊕ (Σ v, I v) → Bool) (e : E) :
    (simulation H G real).abs s e = s (.inl e) := by rfl

/-- Canonical private directions are computed by their owner's local realization. -/
theorem simulation_enc_private [Fintype V] (G : ConstraintGraph V E)
    (real : ∀ v, Realizes (component (H v)) (G v))
    (s : E → Bool) (v : V) (e : I v) :
    (simulation H G real).enc s (.inr ⟨v, e⟩) = (real v).canon s e := by rfl

end Cslib.Complexity.NCL.ConstraintGraph.Replacement
