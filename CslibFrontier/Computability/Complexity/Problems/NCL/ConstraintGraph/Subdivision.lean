/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.List.Nodup

/-!
# Subdividing constraint-graph edges

Each old edge is replaced by a chain of segments, with a degree-two vertex between consecutive
segments. Both incident weights and the minimum inflow at a joint are the old edge weight.
For positive weights, legality says that the segment directions decrease along the chain.
Reading the first segment gives a legal old orientation; repeating an old direction gives a
canonical extension. A legal old reversal lifts by reversing the segments in order.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.graph`: the subdivided graph.
* `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.simulation`: reachability under subdivision.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.loopFree`,
  `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.wellFormed_of_portMultiset`: incidence.
* `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.card_segment`,
  `Cslib.Complexity.NCL.ConstraintGraph.Subdivision.card_vertex`: exact size formulas.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph.Subdivision

variable {V E : Type*}

/-- The segments of each old edge, in order from its false endpoint to its true endpoint. -/
abbrev Segment (n : E → ℕ) := Σ e, Fin (n e + 1)
/-- The inserted degree-two vertices, one between consecutive segments. -/
abbrev Joint (n : E → ℕ) := Σ e, Fin (n e)

/-- The segment incident to the old false endpoint. -/
@[expose] def first (n : E → ℕ) (e : E) : Segment n := ⟨e, 0⟩
/-- The segment incident to the old true endpoint. -/
@[expose] def last (n : E → ℕ) (e : E) : Segment n := ⟨e, Fin.last (n e)⟩

private def port (n : E → ℕ) (p : Port E) : Port (Segment n) :=
  ⟨if p.dir then last n p.edge else first n p.edge, p.dir⟩

private def vertex (n : E → ℕ) (v : Vertex E) : Vertex (Segment n) :=
  ⟨v.ports.map (fun p => ⟨port n p.port, p.weight⟩), v.minInflow⟩

private def wire {n : E → ℕ} (w : ℕ) (a b : Segment n) : Vertex (Segment n) :=
  ⟨[⟨⟨a, true⟩, w⟩, ⟨⟨b, false⟩, w⟩], w⟩

/-- Insert `n e` vertices with equal incident weight and minimum inflow `w e` on each edge. -/
@[expose]
def graph (G : ConstraintGraph V E) (n w : E → ℕ) : ConstraintGraph (V ⊕ Joint n) (Segment n)
  | .inl v => ⟨(G v).ports.map (fun p =>
      ⟨⟨if p.port.dir then last n p.port.edge else first n p.port.edge, p.port.dir⟩, p.weight⟩),
      (G v).minInflow⟩
  | .inr ⟨e, j⟩ =>
      ⟨[⟨⟨⟨e, j.castSucc⟩, true⟩, w e⟩, ⟨⟨⟨e, j.succ⟩, false⟩, w e⟩], w e⟩

/-- Extend an old orientation by giving every segment its old edge direction. -/
@[expose] def enc (n : E → ℕ) (s : E → Bool) : Segment n → Bool := fun i => s i.1

/-- Read the direction of the first segment of each old edge. -/
@[expose] def abs (n : E → ℕ) (s : Segment n → Bool) : E → Bool := fun e => s (first n e)

private theorem port_in_enc (n : E → ℕ) (s : E → Bool) (p : Port E) :
    (port n p).In (enc n s) ↔ p.In s := by
  rcases p with ⟨e, d⟩
  cases d <;> rfl

private theorem sat_vertex_enc (n : E → ℕ) (v : Vertex E) (s : E → Bool) :
    (vertex n v).Sat (enc n s) ↔ v.Sat s := by
  simp only [vertex, Vertex.Sat, Vertex.inflow, List.map_map, Function.comp_def, port_in_enc]

private theorem sat_wire_iff {n : E → ℕ} (w : ℕ) (hw : 0 < w)
    (a b : Segment n) (s : Segment n → Bool) :
    (wire w a b).Sat s ↔ s b ≤ s a := by
  change w ≤ (if s a = true then w else 0) + ((if s b = false then w else 0) + 0) ↔ _
  cases ha : s a <;> cases hb : s b <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
      Nat.add_zero, Nat.zero_add]
  all_goals first
    | exact ⟨fun _ => by decide +kernel, fun _ => by omega⟩
    | exact ⟨fun h => False.elim (by omega), fun h => False.elim (by simpa using h rfl)⟩

private theorem legal_enc (G : ConstraintGraph V E) (n w : E → ℕ) {s : E → Bool}
    (hs : G.Legal s) : (graph G n w).Legal (enc n s) := by
  intro v
  cases v with
  | inl v => exact (sat_vertex_enc n (G v) s).2 (hs v)
  | inr j =>
    rcases j with ⟨e, j⟩
    change (wire (w e) _ _).Sat (enc n s)
    cases h : s e <;> simp [wire, Vertex.Sat, Vertex.inflow, Port.In, enc, h]

private theorem adjacent_le (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    {s : Segment n → Bool} (hs : (graph G n w).Legal s) (e : E) (j : Fin (n e)) :
    s ⟨e, j.succ⟩ ≤ s ⟨e, j.castSucc⟩ :=
  (sat_wire_iff (w e) (hw e) _ _ s).1 (hs (.inr ⟨e, j⟩))

private theorem segment_le_first (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    {s : Segment n → Bool} (hs : (graph G n w).Legal s) (e : E) (j : Fin (n e + 1)) :
    s ⟨e, j⟩ ≤ s (first n e) := by
  rcases j with ⟨j, hj⟩
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    exact (adjacent_le G n w hw hs e ⟨j, by omega⟩).trans (ih (by omega))

private theorem legal_abs (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    {s : Segment n → Bool} (hs : (graph G n w).Legal s) : G.Legal (abs n s) := by
  intro v
  apply (sat_vertex_enc n (G v) (abs n s)).1
  apply Vertex.Sat.mono (s := s) _ (hs (.inl v))
  intro p hp hin
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases q with ⟨⟨e, d⟩, wt⟩
  cases d with
  | false => exact hin
  | true =>
    have hle := segment_le_first G n w hw hs e (Fin.last (n e))
    change s (last n e) ≤ s (first n e) at hle
    change s (last n e) = true at hin
    change s (first n e) = true
    rw [hin] at hle
    exact Bool.eq_true_of_true_le hle

private theorem abs_enc (n : E → ℕ) (s : E → Bool) : abs n (enc n s) = s := rfl

private theorem first_injective (n : E → ℕ) : Function.Injective (first n) :=
  fun _ _ h => congrArg Sigma.fst h

private theorem port_edge_fst (n : E → ℕ) (p : Port E) : (port n p).edge.1 = p.edge := by
  rcases p with ⟨e, d⟩
  cases d <;> rfl

/-- Subdivision preserves the condition that no vertex repeats an edge. -/
theorem loopFree (G : ConstraintGraph V E) (n w : E → ℕ) (hl : G.LoopFree) :
    (graph G n w).LoopFree := by
  intro v
  cases v with
  | inl v =>
    apply List.Nodup.of_map Sigma.fst
    change ((vertex n (G v)).ports.map (fun p => p.port.edge)).map Sigma.fst |>.Nodup
    simpa only [vertex, List.map_map, Function.comp_def, port_edge_fst] using hl v
  | inr j =>
    rcases j with ⟨e, j⟩
    have hne : (⟨e, j.castSucc⟩ : Segment n) ≠ ⟨e, j.succ⟩ := by
      intro h
      have hv := congrArg (fun i : Segment n => i.2.val) h
      change j.val = j.val + 1 at hv
      omega
    change ([⟨e, j.castSucc⟩, ⟨e, j.succ⟩] : List (Segment n)).Nodup
    simp [hne]

private def portMap (n : E → ℕ) :
    Multiset (WeightedPort E) →+ Multiset (WeightedPort (Segment n)) :=
  Multiset.mapAddMonoidHom (fun p => ⟨port n p.port, p.weight⟩)

private theorem source_ports [Fintype V] (G : ConstraintGraph V E) (n : E → ℕ) :
    (∑ v, (↑(vertex n (G v)).ports : Multiset (WeightedPort (Segment n)))) =
      portMap n G.portMultiset := by
  rw [ConstraintGraph.portMultiset, map_sum]
  rfl

private theorem graph_ports [Fintype V] [Fintype E] (G : ConstraintGraph V E) (n w : E → ℕ) :
    (graph G n w).portMultiset = portMap n G.portMultiset +
      ∑ e, ∑ j : Fin (n e),
        ({⟨⟨⟨e, j.castSucc⟩, true⟩, w e⟩} +
          {⟨⟨⟨e, j.succ⟩, false⟩, w e⟩} : Multiset (WeightedPort (Segment n))) := by
  rw [ConstraintGraph.portMultiset, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·)
  · exact source_ports G n
  · rw [Fintype.sum_sigma]
    rfl

private theorem chain_ports (n w : E → ℕ) (e : E) :
    ({⟨⟨first n e, false⟩, w e⟩} + {⟨⟨last n e, true⟩, w e⟩} :
      Multiset (WeightedPort (Segment n))) +
        ∑ j : Fin (n e), ({⟨⟨⟨e, j.castSucc⟩, true⟩, w e⟩} + {⟨⟨⟨e, j.succ⟩, false⟩, w e⟩}) =
      ∑ j : Fin (n e + 1), ({⟨⟨⟨e, j⟩, false⟩, w e⟩} + {⟨⟨⟨e, j⟩, true⟩, w e⟩}) := by
  simp only [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun j : Fin (n e + 1) =>
    ({⟨⟨⟨e, j⟩, false⟩, w e⟩} : Multiset (WeightedPort (Segment n))))]
  rw [Fin.sum_univ_castSucc (fun j : Fin (n e + 1) =>
    ({⟨⟨⟨e, j⟩, true⟩, w e⟩} : Multiset (WeightedPort (Segment n))))]
  unfold first last
  ac_rfl

/-- Consistent edge weights and opposite endpoints are preserved by subdivision. -/
theorem wellFormed_of_portMultiset [Fintype V] [Fintype E]
    (G : ConstraintGraph V E) (n w : E → ℕ)
    (hG : G.portMultiset = ∑ e,
      ({⟨⟨e, false⟩, w e⟩} + {⟨⟨e, true⟩, w e⟩} : Multiset (WeightedPort E))) :
    (graph G n w).WellFormed := by
  refine ⟨fun i => w i.1, ?_⟩
  rw [graph_ports, hG, map_sum]
  change (∑ e, ({⟨⟨first n e, false⟩, w e⟩} + {⟨⟨last n e, true⟩, w e⟩} :
      Multiset (WeightedPort (Segment n)))) +
      ∑ e, ∑ j : Fin (n e), ({⟨⟨⟨e, j.castSucc⟩, true⟩, w e⟩} +
        {⟨⟨⟨e, j.succ⟩, false⟩, w e⟩} : Multiset (WeightedPort (Segment n))) = _
  rw [← Finset.sum_add_distrib, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  exact chain_ports n w e

/-- The subdivision contains one more segment than joint on each old edge. -/
theorem card_segment [Fintype E] (n : E → ℕ) :
    Fintype.card (Segment n) = ∑ e, (n e + 1) := by simp [Segment, Fintype.card_sigma]

/-- The new vertices are the old vertices together with the inserted joints. -/
theorem card_vertex [Fintype V] [Fintype E] (n : E → ℕ) :
    Fintype.card (V ⊕ Joint n) = Fintype.card V + ∑ e, n e := by
  simp [Joint, Fintype.card_sigma]

variable [DecidableEq E]

private theorem step_abs (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    {s t : Segment n → Bool} (h : (graph G n w).Step s t) :
    Relation.ReflGen G.Step (abs n s) (abs n t) := by
  obtain ⟨hs, ht, ⟨⟨e, j⟩, rfl⟩⟩ := h
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    apply Relation.ReflGen.single
    refine ⟨legal_abs G n w hw hs, legal_abs G n w hw ht, e, ?_⟩
    exact reverse_comp_of_injective (first_injective n) s e
  · have heq : abs n (reverse s ⟨e, j⟩) = abs n s :=
      reverse_comp_of_not_mem_range s
        (fun f h => hj (congrArg (fun i : Segment n => i.2.val) h).symm)
    rw [heq]

private def ramp (n : E → ℕ) (s : E → Bool) (e : E) (k : ℕ) : Segment n → Bool :=
  fun i => if i.1 = e then decide (i.2.val < k) else s i.1

private theorem ramp_port_of_ne (n : E → ℕ) (s : E → Bool) (e : E) (k : ℕ) (p : Port E)
    (he : p.edge ≠ e) : (port n p).In (ramp n s e k) ↔ p.In s := by
  rcases p with ⟨f, d⟩
  cases d <;> simp [port, ramp, first, last, Port.In, he]

private theorem ramp_adjacent (n : E → ℕ) (s : E → Bool) (e : E) (k : ℕ)
    (f : E) (j : Fin (n f)) :
    ramp n s e k ⟨f, j.succ⟩ ≤ ramp n s e k ⟨f, j.castSucc⟩ := by
  by_cases hf : f = e
  · simp only [ramp, hf, ite_true]
    intro h
    have hlt : j.val + 1 < k := of_decide_eq_true h
    change decide (j.val < k) = true
    exact decide_eq_true (by omega)
  · simp only [ramp, hf, ite_false]
    exact Bool.le_refl _

private theorem sat_ramp (v : Vertex E) (n : E → ℕ)
    (hl : (v.ports.map (fun p => p.port.edge)).Nodup) (s : E → Bool) (e : E) (he : s e = false)
    (hs : v.Sat s) (ht : v.Sat (reverse s e)) (k : ℕ) :
    (vertex n v).Sat (ramp n s e k) := by
  classical
  by_cases hneg : ∃ q ∈ v.ports, q.port.edge = e ∧ q.port.dir = false
  · apply Vertex.Sat.mono (s := enc n (reverse s e)) _
      ((sat_vertex_enc n v _).2 ht)
    intro p hp hin
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hin' := (port_in_enc n (reverse s e) q.port).1 hin
    by_cases hqe : q.port.edge = e
    · obtain ⟨q₀, hq₀, hqe₀, hdir⟩ := hneg
      have hqeq := List.inj_on_of_nodup_map hl hq hq₀ (hqe.trans hqe₀.symm)
      rw [hqeq] at hin'
      change reverse s e q₀.port.edge = q₀.port.dir at hin'
      rw [hqe₀, hdir, reverse_self, he] at hin'
      cases hin'
    · apply (ramp_port_of_ne n s e k q.port hqe).2
      change s q.port.edge = q.port.dir
      change reverse s e q.port.edge = q.port.dir at hin'
      rwa [reverse_of_ne s hqe] at hin'
  · apply Vertex.Sat.mono (s := enc n s) _ ((sat_vertex_enc n v s).2 hs)
    intro p hp hin
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hin' := (port_in_enc n s q.port).1 hin
    have hqe : q.port.edge ≠ e := by
      intro hqe
      apply hneg
      refine ⟨q, hq, hqe, ?_⟩
      change s q.port.edge = q.port.dir at hin'
      rw [← hin', hqe, he]
    exact (ramp_port_of_ne n s e k q.port hqe).2 hin'

private theorem legal_ramp (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    (hl : G.LoopFree) (s : E → Bool) (e : E) (he : s e = false)
    (hs : G.Legal s) (ht : G.Legal (reverse s e)) (k : ℕ) :
    (graph G n w).Legal (ramp n s e k) := by
  intro v
  cases v with
  | inr j =>
    rcases j with ⟨f, j⟩
    exact (sat_wire_iff (w f) (hw f) _ _ _).2 (ramp_adjacent n s e k f j)
  | inl v => exact sat_ramp (G v) n (hl v) s e he (hs v) (ht v) k

private theorem ramp_zero (n : E → ℕ) (s : E → Bool) (e : E) (he : s e = false) :
    ramp n s e 0 = enc n s := by
  funext ⟨f, j⟩
  by_cases hf : f = e
  · subst f
    simp [ramp, enc, he]
  · simp [ramp, enc, hf]

private theorem ramp_end (n : E → ℕ) (s : E → Bool) (e : E) (he : s e = false) :
    ramp n s e (n e + 1) = enc n (reverse s e) := by
  funext ⟨f, j⟩
  by_cases hf : f = e
  · subst f
    simp [ramp, enc, reverse_self, he, j.isLt]
  · simp [ramp, enc, hf, reverse_of_ne _ hf]

private theorem ramp_succ (n : E → ℕ) (s : E → Bool) (e : E) (k : ℕ)
    (hk : k < n e + 1) :
    ramp n s e (k + 1) = reverse (ramp n s e k) ⟨e, ⟨k, hk⟩⟩ := by
  funext ⟨f, j⟩
  by_cases hf : f = e
  · subst f
    by_cases hj : j.val = k
    · have hj' : j = ⟨k, hk⟩ := Fin.ext hj
      subst j
      simp [ramp, reverse_self]
    · have hne : (⟨e, j⟩ : Segment n) ≠ ⟨e, ⟨k, hk⟩⟩ := by
        intro h
        exact hj (congrArg (fun i : Segment n => i.2.val) h)
      rw [reverse_of_ne _ hne]
      simp only [ramp, ite_true, eq_self]
      have hiff : j.val < k + 1 ↔ j.val < k := by omega
      simp only [hiff]
  · have hne : (⟨f, j⟩ : Segment n) ≠ ⟨e, ⟨k, hk⟩⟩ := by
      intro h
      exact hf (congrArg Sigma.fst h)
    rw [reverse_of_ne _ hne]
    simp [ramp, hf]

private theorem reachable_ramp (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    (hl : G.LoopFree) (s : E → Bool) (e : E) (he : s e = false)
    (hs : G.Legal s) (ht : G.Legal (reverse s e)) :
    (graph G n w).Reachable (enc n s) (enc n (reverse s e)) := by
  have hr (k : ℕ) (hk : k ≤ n e + 1) :
      (graph G n w).Reachable (ramp n s e 0) (ramp n s e k) := by
    induction k with
    | zero => exact .refl
    | succ k ih =>
      exact (ih (by omega)).tail
        ⟨legal_ramp G n w hw hl s e he hs ht k,
          legal_ramp G n w hw hl s e he hs ht (k + 1), ⟨e, ⟨k, by omega⟩⟩,
          ramp_succ n s e k (by omega)⟩
  rw [← ramp_zero n s e he, ← ramp_end n s e he]
  exact hr (n e + 1) le_rfl

private theorem step_enc (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    (hl : G.LoopFree) {s t : E → Bool} (h : G.Step s t) :
    (graph G n w).Reachable (enc n s) (enc n t) := by
  obtain ⟨hs, ht, e, rfl⟩ := h
  cases he : s e
  · exact reachable_ramp G n w hw hl s e he hs ht
  · have hfalse : reverse s e e = false := by simp [he]
    have hsource : G.Legal (reverse (reverse s e) e) := by simpa only [reverse_reverse] using hs
    have hr := reachable_ramp G n w hw hl (reverse s e) e hfalse ht hsource
    simpa only [reverse_reverse] using hr.symm

/-- Inserting arbitrarily many positive-weight W vertices on each edge preserves reachability. -/
@[expose] def simulation (G : ConstraintGraph V E) (n w : E → ℕ) (hw : ∀ e, 0 < w e)
    (hl : G.LoopFree) : ConstraintGraph.Simulation G (graph G n w) where
  abs := abs n
  enc := enc n
  abs_enc := by exact abs_enc n
  legal_enc := by exact legal_enc G n w
  legal_abs := by exact legal_abs G n w hw
  step_abs := by exact step_abs G n w hw
  step_enc := by exact step_enc G n w hw hl

/-- Abstraction reads the first segment. -/
@[simp] theorem simulation_abs (G : ConstraintGraph V E) (n w : E → ℕ)
    (hw : ∀ e, 0 < w e) (hl : G.LoopFree) (s : Segment n → Bool) :
    (simulation G n w hw hl).abs s = abs n s := by rfl

/-- Encoding repeats each old edge direction. -/
@[simp] theorem simulation_enc (G : ConstraintGraph V E) (n w : E → ℕ)
    (hw : ∀ e, 0 < w e) (hl : G.LoopFree) (s : E → Bool) :
    (simulation G n w hw hl).enc s = enc n s := by rfl

end Cslib.Complexity.NCL.ConstraintGraph.Subdivision
