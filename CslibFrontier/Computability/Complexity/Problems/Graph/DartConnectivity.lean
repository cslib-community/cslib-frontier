/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Dart invariants and existing graph components

Adjacency and trails in induced simple graphs lift to oriented occurrences in the edge list.
`exists_path_of_induced_reachable` joins prescribed end darts through an induced path.
Vertex and edge-reversal invariants are constant on existing declared-vertex components.
Point components have no darts.
-/

public section

namespace Cslib.Complexity.Graph

namespace Dart

/-- A simple-graph adjacency is witnessed by an oriented listed edge occurrence. -/
theorem exists_of_adj {G : Graph} {u v : ℕ} (h : G.toSimpleGraph.Adj u v) :
    ∃ d : Dart G, d.vertex = u ∧ d.reverse.vertex = v := by
  obtain ⟨-, h | h⟩ := toSimpleGraph_adj.mp h
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    change G.edges[i.val] = (u, v) at hi
    exact ⟨(i, false), by simp [vertex, reverse, edgeEndpoint, hi]⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    change G.edges[i.val] = (v, u) at hi
    exact ⟨(i, true), by simp [vertex, reverse, edgeEndpoint, hi]⟩

/-- Either orientation of a dart gives the same unordered pair of listed endpoints. -/
theorem sym2_vertex_reverse {G : Graph} (d : Dart G) :
    (s(d.vertex, d.reverse.vertex) : Sym2 ℕ) = s(G.edges[d.1].1, G.edges[d.1].2) := by
  rcases d with ⟨i, _ | _⟩
  · exact edge_eq_vertices i ▸ rfl
  · exact edge_eq_vertices i ▸ Sym2.eq_swap

/-- Each step of a trail in an induced simple graph lifts to an oriented listed edge.
The chosen occurrences have distinct indices, and preserve the order of the trail's vertices. -/
theorem exists_darts_of_induced_trail {G : Graph} {S : Set ℕ} {u v : S}
    (p : (G.toSimpleGraph.induce S).Walk u v) (hp : p.IsTrail) :
    ∃ d : Fin p.length → Dart G, Function.Injective (fun i => (d i).1) ∧
      ∀ i, (d i).vertex = (p.getVert i).val ∧
        (d i).reverse.vertex = (p.getVert (i.val + 1)).val := by
  classical
  have hlift (i : Fin p.length) : ∃ d : Dart G,
      d.vertex = (p.getVert i).val ∧ d.reverse.vertex = (p.getVert (i.val + 1)).val :=
    exists_of_adj (p.adj_getVert_succ i.isLt)
  choose d hd using hlift
  refine ⟨d, fun i j hij => Fin.ext ((hp.edges_nodup.getElem_inj_iff
    (hi := p.length_edges.symm ▸ i.isLt) (hj := p.length_edges.symm ▸ j.isLt)).mp ?_), hd⟩
  apply Sym2.map.injective (f := Subtype.val) Subtype.val_injective
  have hdi := hd i
  have hdj := hd j
  simp only [SimpleGraph.Walk.getElem_edges, Sym2.map_mk, ← hdi.1, ← hdi.2, ← hdj.1, ← hdj.2,
    sym2_vertex_reverse, (hij : (d i).1 = (d j).1)]

/-- The two darts on one edge occurrence agree or are reverses. -/
theorem eq_or_eq_reverse_of_edge_eq {G : Graph} {d e : Dart G} (h : d.1 = e.1) :
    d = e ∨ d = e.reverse := by
  rcases d with ⟨i, b⟩
  rcases e with ⟨j, c⟩
  cases h
  exact (Bool.eq_or_eq_not b c).imp (Prod.ext rfl) (Prod.ext rfl)

/-- Join two prescribed outgoing darts at vertices outside `S` using a path in the graph
induced on `S`. The first dart is traversed forward and the last backward. The listed edges
are distinct, the intervening sites are distinct, and every site is in the reachable
component of the first inner endpoint. The two outer vertices may agree. -/
theorem exists_path_of_induced_reachable {G : Graph} {S : Set ℕ} (a b : Dart G)
    (ha : a.vertex ∉ S) (hb : b.vertex ∉ S) (hab : a ≠ b)
    (ha' : a.reverse.vertex ∈ S) (hb' : b.reverse.vertex ∈ S)
    (h : (G.toSimpleGraph.induce S).Reachable ⟨a.reverse.vertex, ha'⟩ ⟨b.reverse.vertex, hb'⟩) :
    ∃ (n : ℕ) (path : Fin (n + 1) → Dart G) (site : Fin n → ℕ),
      path 0 = a ∧ (path (Fin.last n)).reverse = b ∧
      (∀ i, (path i).vertex = Fin.cases a.vertex site i) ∧
      (∀ i, (path i).reverse.vertex = Fin.lastCases b.vertex site i) ∧
      Function.Injective (fun i => (path i).1) ∧ Function.Injective site ∧
      ∀ i, ∃ hi : site i ∈ S, (G.toSimpleGraph.induce S).Reachable
        ⟨a.reverse.vertex, ha'⟩ ⟨site i, hi⟩ := by
  classical
  obtain ⟨p, hp⟩ := h.exists_isPath
  obtain ⟨d, hdInj, hd⟩ := exists_darts_of_induced_trail p hp.isTrail
  have hab' : a.1 ≠ b.1 := fun he =>
    (eq_or_eq_reverse_of_edge_eq he).elim hab fun he => ha (he.symm ▸ hb')
  have avoid (e : Dart G) (he : e.vertex ∉ S) (i : Fin p.length) : e.1 ≠ (d i).1 := fun hi =>
    (eq_or_eq_reverse_of_edge_eq hi).elim
      (fun hi => he (hi.symm ▸ (hd i).1.symm ▸ (p.getVert i).property))
      fun hi => he (hi.symm ▸ (hd i).2.symm ▸ (p.getVert (i.val + 1)).property)
  let tail : Fin (p.length + 1) → Dart G := Fin.snoc d b.reverse
  let path : Fin (p.length + 2) → Dart G := Fin.cons a tail
  let site (i : Fin (p.length + 1)) := (p.getVert i).val
  refine ⟨p.length + 1, path, site, rfl,
    by simp only [path, tail, Fin.cons_last, Fin.snoc_last, reverse_reverse], ?_, ?_, ?_,
    fun i j he => Fin.ext (hp.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) (Subtype.ext he)),
    fun i => ⟨(p.getVert i).property,
      p.reachable_of_mem_support p.start_mem_support (p.getVert_mem_support i)⟩⟩
  · refine Fin.cases rfl fun j => ?_
    change (tail j).vertex = site j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [tail, Fin.snoc_last, site, Fin.val_last, p.getVert_length]
    · simpa only [tail, Fin.snoc_castSucc, site, Fin.val_castSucc] using (hd k).1
  · refine Fin.lastCases
      (by simp only [path, tail, Fin.cons_last, Fin.snoc_last, reverse_reverse, Fin.lastCases_last])
      fun j => ?_
    rw [Fin.lastCases_castSucc]
    refine Fin.cases
      (by simp only [path, Fin.castSucc_zero, Fin.cons_zero, site, Fin.val_zero, p.getVert_zero])
      (fun k => ?_) j
    rw [show k.succ.castSucc = k.castSucc.succ from Fin.ext rfl]
    simpa only [path, tail, Fin.cons_succ, Fin.snoc_castSucc, site, Fin.val_succ] using (hd k).2
  · change Function.Injective (Prod.fst ∘ Fin.cons a (Fin.snoc d b.reverse))
    rw [Fin.comp_cons, Fin.comp_snoc]
    refine Fin.cons_injective_of_injective ?_
      (Fin.snoc_injective_of_injective hdInj fun ⟨i, hi⟩ => avoid b hb i hi.symm)
    rintro ⟨i, hi⟩
    revert hi
    exact Fin.lastCases (fun hi => hab' (by simpa [reverse] using hi.symm))
      (fun j hi => avoid a ha j (by simpa using hi.symm)) i

/-- Vertex invariance and reversal invariance imply constancy on existing edge components.
Only finite listed edge witnesses are used; the ambient natural-number universe need not be
finite. The component hypothesis already includes endpoint declarations. -/
theorem eq_of_sameComponent {G : Graph} {β : Sort*} (f : Dart G → β)
    (hv : ∀ d e, d.vertex = e.vertex → f d = f e)
    (ha : ∀ d, f d = f d.reverse) {d e : Dart G}
    (h : RotationCertificate.SameComponent G d.vertex e.vertex) : f d = f e := by
  obtain ⟨_, _, ⟨p⟩⟩ := h
  have hw {u v : {v // v ∈ G.vertices}} (p : G.induced.Walk u v) :
      ∀ d e : Dart G, d.vertex = u.val → e.vertex = v.val → f d = f e := by
    induction p with
    | nil => exact fun d e hd he => hv d e (hd.trans he.symm)
    | @cons u v w hadj p ih =>
      intro d e hd he
      obtain ⟨a, hau, hav⟩ := exists_of_adj hadj
      exact (hv d a (hd.trans hau.symm)).trans ((ha a).trans (ih a.reverse e hav he))
  exact hw p d e rfl rfl

/-- Every vertex in an edge component has an incident dart. This does not invent a dart for
a declared isolated point. -/
theorem exists_of_sameComponent {G : Graph} (d : Dart G) (v : ℕ)
    (h : RotationCertificate.SameComponent G d.vertex v) : ∃ e : Dart G, e.vertex = v := by
  by_cases hv : d.vertex = v
  · exact ⟨d, hv⟩
  obtain ⟨_, _, hc⟩ := h
  obtain ⟨_, hw⟩ := hc.nonempty_neighborSet_right fun he => hv (congrArg Subtype.val he)
  obtain ⟨e, he, -⟩ := exists_of_adj hw
  exact ⟨e, he⟩

end Dart

end Cslib.Complexity.Graph
