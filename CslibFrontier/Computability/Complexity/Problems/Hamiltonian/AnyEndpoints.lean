/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Directed
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Undirected
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.IsChain

/-!
# Hamiltonian paths between unspecified endpoints

`DirHamPathAny` is the set of directed graphs that have a Hamiltonian path, with no endpoints
given: the language dHAMPATH of [Arora and Barak, draft, Theorem 2.18][AroraBarak07], whose
instances are graphs alone. `DirHamPath` instead fixes the start and the end vertex.

**Empty-graph convention.** A Hamiltonian path is a *nonempty* list of the declared vertices, so a
graph without declared vertices is not in `DirHamPathAny`
(`DirHamPathAny.notMem_of_vertices_eq_nil`). Equivalently, `G ∈ DirHamPathAny` exactly when `G`
has a Hamiltonian path between some vertices `s` and `t` (`mem_DirHamPathAny_iff`). The reduction
below produces graphs with at least two vertices, so it does not depend on this convention.

**The reduction** `DirHamPath.toAny` shifts every vertex label by two and adds a source `0` with
the single arc `0 → s + 2` and a sink `1` with the single arc `t + 2 → 1`. No arc enters `0` and
no arc leaves `1`, so a Hamiltonian path of the new graph starts at `0`, ends at `1`, and in
between is a shifted Hamiltonian path of the old graph from `s` to `t`
(`DirHamPath.toAny_mem_iff`). Shifting rather than picking fresh labels keeps the reduction a
simple list map, and also handles arcs of the old graph with undeclared endpoints.

**The undirected problem.** `HamPathAny` is the set of graphs with an undirected Hamiltonian path
(Mathlib's `SimpleGraph.Walk.IsHamiltonian`, as in `HamPath`) between some declared vertices: the
language HAMPATH of [Arora and Barak, draft, Exercise 2.17][AroraBarak07]. A graph without declared
vertices is not a member (`HamPathAny.notMem_of_vertices_eq_nil`); a graph with one declared vertex
is (`HamPathAny.mem_of_vertices_eq_singleton`). Read as an undirected graph, `DirHamPath.toAny x`
attaches a pendant vertex `0` to `s + 2` and a pendant vertex `1` to `t + 2`. A pendant vertex of a
Hamiltonian path is one of its ends, so after reversing the path if needed it runs from `0` to `1`,
and in between is a shifted Hamiltonian path from `s` to `t`
(`DirHamPath.toAny_mem_HamPathAny_iff`). The same polynomial-time construction therefore reduces
`HamPath` to `HamPathAny`.

## Main definitions

* `Cslib.Complexity.DirHamPathAny`: graphs with a Hamiltonian path.
* `Cslib.Complexity.DirHamPath.toAny`: the reduction from `DirHamPath`.
* `Cslib.Complexity.DirHamPathAny.verifier`: its verifier.
* `Cslib.Complexity.HamPathAny`: undirected graphs with a Hamiltonian path.
* `Cslib.Complexity.HamPathAny.verifier`: its verifier.

## Main results

* `Cslib.Complexity.mem_DirHamPathAny_iff`: some endpoints exist.
* `Cslib.Complexity.DirHamPath.toAny_mem_iff`,
  `Cslib.Complexity.DirHamPath.computableInPolyTime_toAny`,
  `Cslib.Complexity.polyTimeReducible_DirHamPath_DirHamPathAny`: the reduction.
* `Cslib.Complexity.DirHamPathAny.mem_NP`, `Cslib.Complexity.DirHamPathAny_npHard`,
  `Cslib.Complexity.DirHamPathAny_npComplete`: `DirHamPathAny` is `NP`-complete.
* `Cslib.Complexity.mem_HamPathAny_iff`: undirected Hamiltonian paths as nonempty lists.
* `Cslib.Complexity.DirHamPath.toAny_mem_HamPathAny_iff`,
  `Cslib.Complexity.polyTimeReducible_HamPath_HamPathAny`: the undirected reduction.
* `Cslib.Complexity.HamPathAny.mem_NP`, `Cslib.Complexity.HamPathAny_npHard`,
  `Cslib.Complexity.HamPathAny_npComplete`: `HamPathAny` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime


/-! ### Verifiers for paths between unspecified endpoints

The verifiers for `DirHamPathAny` and `HamPathAny` differ only in their edge test. -/

/-- The verifier that decodes an ordering of the declared vertices and checks that it is nonempty
and that consecutive vertices pass the edge test `r` checks membership in the set of graphs with
such an ordering. -/
private theorem isVerifier_anyVerifier {r : Graph → ℕ → ℕ → Bool} {R : Graph → ℕ → ℕ → Prop}
    (hr : ∀ G u v, r G u v = true ↔ R G u v) :
    IsVerifier encGraph (Polynomial.X ^ 2)
      (Graph.verifyOrdering (fun G => G.vertices) fun G p =>
        decide (p ≠ []) && Graph.chainBool (r G) p)
      {G | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.vertices) ∧ p ≠ [] ∧ p.IsChain (R G)} :=
  Graph.isVerifier_verifyOrdering (P := fun G p => p ≠ [] ∧ p.IsChain (R G))
    Graph.length_vertices_le_encGraph fun G p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Graph.chainBool_eq_true_iff (hr G)]

/-- The verifier of `isVerifier_anyVerifier` is polynomial-time for a polynomial-time edge test. -/
private theorem computableInPolyTime_anyVerifier {r : Graph → ℕ → ℕ → Bool}
    (hr : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ => r q.1.1 q.1.2 q.2)
      (encPair (encPair encGraph encNat) encNat) encBool) :
    ComputableInPolyTime
      (Graph.verifyOrdering (fun G => G.vertices) fun G p =>
        decide (p ≠ []) && Graph.chainBool (r G) p)
      (encPair encGraph encBits) encBool := by
  have hproj : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by
    fun_prop
  refine Graph.computableInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (bool_and' ?_ (Graph.computableInPolyTime_chainBool (hr.comp hproj) (snd _ _)))
  simpa only [Function.comp_def, _root_.decide_not] using
    bool_not.comp ((snd _ _).decide_eq' (const []))

/-! ### Directed Hamiltonian paths between unspecified endpoints -/

/-- The directed graphs with a Hamiltonian path between some vertices: a nonempty list of every
declared vertex exactly once whose consecutive vertices are joined by arcs
[Arora and Barak, draft, Theorem 2.18][AroraBarak07]. Graphs without declared vertices are not
members. -/
def DirHamPathAny : Set Graph :=
  {G | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.vertices) ∧ p ≠ [] ∧
    p.IsChain fun u v => (u, v) ∈ G.edges}

/-- A graph is in `DirHamPathAny` exactly when it has a Hamiltonian path between some vertices. -/
theorem mem_DirHamPathAny_iff {G : Graph} :
    G ∈ DirHamPathAny ↔ ∃ s t p, G.IsDirHamPath s t p := by
  constructor
  · rintro ⟨p, hnd, hcov, hne, hch⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨a, _, _, hnd, hcov, rfl, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hch⟩
  · rintro ⟨s, t, p, hnd, hcov, hs, -, hch⟩
    exact ⟨p, hnd, hcov, by rintro rfl; simp at hs, hch⟩

namespace DirHamPathAny

/-- **Empty-graph convention**: a graph without declared vertices has no Hamiltonian path. -/
theorem notMem_of_vertices_eq_nil {G : Graph} (h : G.vertices = []) : G ∉ DirHamPathAny := by
  rintro ⟨p, -, hcov, hne, -⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil p hne
  simpa [h] using (hcov v).1 hv


/-- The verifier for `DirHamPathAny`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it is nonempty, lists every declared vertex exactly
once, and that consecutive vertices are joined by arcs. -/
def verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.vertices) fun G p =>
    decide (p ≠ []) && Graph.chainBool G.arcBool p

/-- `DirHamPathAny.verifier` verifies `DirHamPathAny` with certificates of length `n ^ 2` for
graphs of encoded length `n`. -/
theorem isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier DirHamPathAny :=
  isVerifier_anyVerifier (R := fun G u v => (u, v) ∈ G.edges) Graph.arcBool_eq_true_iff

/-- The `DirHamPathAny` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encGraph encBits) encBool :=
  computableInPolyTime_anyVerifier Graph.computableInPolyTime_arcBool

/-- `DirHamPathAny` belongs to `NP`. -/
theorem mem_NP : DirHamPathAny ∈ NP encGraph :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

end DirHamPathAny

/-! ### The reduction from `DirHamPath` -/

/-- An element of a chain other than its first has a predecessor related to it. -/
private theorem exists_rel_of_mem_tail {R : ℕ → ℕ → Prop} :
    ∀ {p : List ℕ}, p.IsChain R → ∀ {x}, x ∈ p.tail → ∃ y, R y x
  | [], _, _, hx => by simp at hx
  | [_], _, _, hx => by simp at hx
  | a :: b :: l, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨a, h.1⟩
    · exact exists_rel_of_mem_tail h.2 hx

/-- An element of a chain that has no predecessor related to it is the first element. -/
private theorem head?_eq_of_forall_not_rel {R : ℕ → ℕ → Prop} {p : List ℕ} (hch : p.IsChain R)
    {x : ℕ} (hx : x ∈ p) (hin : ∀ y, ¬R y x) : p.head? = some x := by
  cases p with
  | nil => simp at hx
  | cons a r =>
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · obtain ⟨y, hy⟩ := exists_rel_of_mem_tail hch hx
      exact absurd hy (hin y)

/-- An element of a chain that has no successor related to it is the last element. -/
private theorem getLast?_eq_of_forall_not_rel {R : ℕ → ℕ → Prop} {p : List ℕ}
    (hch : p.IsChain R) {x : ℕ} (hx : x ∈ p) (hout : ∀ y, ¬R x y) : p.getLast? = some x := by
  rw [← List.head?_reverse]
  exact head?_eq_of_forall_not_rel (List.isChain_reverse.mpr hch) (List.mem_reverse.mpr hx) hout

namespace DirHamPath

/-- The reduction from `DirHamPath` to `DirHamPathAny`: shift every vertex by two, and add a source
`0` with an arc to `s + 2` and a sink `1` with an arc from `t + 2`. -/
def toAny (x : PathInstance) : Graph :=
  ⟨0 :: 1 :: x.graph.vertices.map (· + 2),
    (0, x.source + 2) :: (x.target + 2, 1) :: x.graph.edges.map fun e => (e.1 + 2, e.2 + 2)⟩

private theorem mem_toAny_vertices {x : PathInstance} {v : ℕ} :
    v ∈ (toAny x).vertices ↔ v = 0 ∨ v = 1 ∨ ∃ w ∈ x.graph.vertices, w + 2 = v := by
  simp [toAny]

private theorem mem_toAny_edges {x : PathInstance} {u v : ℕ} :
    (u, v) ∈ (toAny x).edges ↔ (u = 0 ∧ v = x.source + 2) ∨ (u = x.target + 2 ∧ v = 1) ∨
      ∃ a b, (a, b) ∈ x.graph.edges ∧ a + 2 = u ∧ b + 2 = v := by
  simp [toAny]

/-- An arc of `toAny x` between shifted vertices is a shifted arc of `x.graph`. -/
private theorem shifted_edge {x : PathInstance} {a b : ℕ}
    (h : (a + 2, b + 2) ∈ (toAny x).edges) : (a, b) ∈ x.graph.edges := by
  rw [mem_toAny_edges] at h
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨a', b', h, ha, hb⟩
  · omega
  · omega
  · obtain rfl : a' = a := by omega
    obtain rfl : b' = b := by omega
    exact h

private theorem shift_injective : Function.Injective (· + 2 : ℕ → ℕ) :=
  fun _ _ h => by simpa using h

/-- **Shifting paths.** Let `R'` be a relation on the vertices of `toAny x` that relates shifted
vertices `a + 2`, `b + 2` exactly when `R` relates `a`, `b`, relates `0` only to `x.source + 2`
and only `x.target + 2` to `1`, and does not relate `0` to `1`. Then the `R'`-paths of `toAny x`
from `0` to `1` through every declared vertex are, after removing their ends and shifting back,
the `R`-paths of `x.graph` from `x.source` to `x.target` through every declared vertex. Both
reductions apply this, with the arcs (`DirHamPath.toAny_mem_iff`) and with the undirected
adjacency (`DirHamPath.toAny_mem_HamPathAny_iff`) of `toAny x`. -/
private theorem exists_toAny_path_iff {x : PathInstance} {R R' : ℕ → ℕ → Prop}
    (h01 : ¬R' 0 1) (hs : ∀ a, R' 0 (a + 2) ↔ a = x.source)
    (ht : ∀ b, R' (b + 2) 1 ↔ b = x.target) (hR : ∀ a b, R' (a + 2) (b + 2) ↔ R a b) :
    (∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ (toAny x).vertices) ∧ p.head? = some 0 ∧
        p.getLast? = some 1 ∧ p.IsChain R') ↔
      ∃ q : List ℕ, q.Nodup ∧ (∀ v, v ∈ q ↔ v ∈ x.graph.vertices) ∧ q.head? = some x.source ∧
        q.getLast? = some x.target ∧ q.IsChain R := by
  constructor
  · rintro ⟨p, hnd, hcov, h0, h1, hch⟩
    obtain ⟨r, rfl⟩ : ∃ r, p = 0 :: r := by
      cases p with
      | nil => simp at h0
      | cons a r => simp only [List.head?_cons, Option.some.injEq] at h0; exact ⟨r, by rw [h0]⟩
    have hr : r ≠ [] := by rintro rfl; simp at h1
    obtain ⟨m, rfl⟩ : ∃ m, r = m ++ [1] := by
      refine ⟨r.dropLast, ?_⟩
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hr] at h1
      simp only [Option.getD_some, Option.some.injEq] at h1
      conv_lhs => rw [← List.dropLast_append_getLast hr, h1]
    -- the vertices in between are shifted
    have hnd' := hnd
    rw [List.nodup_cons, List.mem_append, not_or, List.nodup_append] at hnd'
    have hm2 : ∀ v ∈ m, 2 ≤ v := fun v hv => by
      have hv0 : v ≠ 0 := by rintro rfl; exact hnd'.1.1 hv
      have hv1 : v ≠ 1 := by rintro rfl; exact hnd'.2.2.2 1 hv 1 (by simp) rfl
      omega
    obtain ⟨q, rfl⟩ : ∃ q, m = q.map (· + 2) :=
      ⟨m.map (· - 2), by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id m]
        exact List.map_congr_left fun v hv => by
          change v = v - 2 + 2
          have := hm2 v hv
          omega⟩
    have hq : q ≠ [] := by
      rintro rfl
      simp only [List.map_nil, List.nil_append, List.isChain_cons_cons] at hch
      exact h01 hch.1
    rw [← List.singleton_append, ← List.append_assoc, List.isChain_append, List.isChain_append]
      at hch
    obtain ⟨⟨-, hmid, hfirst⟩, -, hlast⟩ := hch
    refine ⟨q, (List.nodup_map_iff shift_injective).mp hnd'.2.1, fun v => ?_, ?_, ?_, ?_⟩
    · have := hcov (v + 2)
      simp only [List.mem_cons, List.mem_append, List.mem_map,
        mem_toAny_vertices, shift_injective.eq_iff, exists_eq_right] at this
      simpa [show v + 2 ≠ 0 by omega, show v + 2 ≠ 1 by omega, shift_injective.eq_iff] using this
    · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hq
      rw [List.head?_cons, (hs a).1 (hfirst 0 (by simp) (a + 2) (by simp))]
    · rw [List.getLast?_eq_some_getLast hq]
      refine congrArg some ((ht _).1 (hlast _ ?_ 1 (by simp)))
      rw [Option.mem_def, List.getLast?_append_of_ne_nil _ (by simpa using hq),
        List.getLast?_map, List.getLast?_eq_some_getLast hq]
      rfl
    · rw [List.isChain_map] at hmid
      exact hmid.imp fun a b h => (hR a b).1 h
  · rintro ⟨q, hnd, hcov, hq0, hq1, hch⟩
    have hq : q ≠ [] := by rintro rfl; simp at hq0
    refine ⟨0 :: (q.map (· + 2) ++ [1]), ?_, fun v => ?_, rfl, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr
        ⟨(List.nodup_map_iff shift_injective).mpr hnd, List.nodup_singleton _, ?_⟩⟩
      · rw [List.mem_append, List.mem_singleton, List.mem_map]
        rintro (⟨_, _, h⟩ | h) <;> omega
      · intro a ha b hb
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_singleton] at hb
        omega
    · rw [mem_toAny_vertices]
      simp only [List.mem_cons, List.mem_append, List.mem_map, hcov, List.not_mem_nil, or_false]
      exact or_congr_right or_comm
    · rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rfl
    · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hq
      simp only [List.head?_cons, Option.some.injEq] at hq0
      subst hq0
      rw [← List.singleton_append, ← List.append_assoc, List.isChain_append, List.isChain_append]
      refine ⟨⟨List.isChain_singleton _, ?_, ?_⟩, List.isChain_singleton _, ?_⟩
      · rw [List.isChain_map]
        exact hch.imp fun u v h => (hR u v).2 h
      · intro u hu v hv
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hu
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        rw [← hu, ← hv]
        exact (hs _).2 rfl
      · intro u hu v hv
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_map, hq1] at hu
        simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
        rw [← hu, ← hv]
        exact (ht _).2 rfl

/-- **Correctness of `DirHamPath.toAny`.** -/
theorem toAny_mem_iff (x : PathInstance) : toAny x ∈ DirHamPathAny ↔ x ∈ DirHamPath := by
  have hpath := exists_toAny_path_iff (x := x) (R := fun u v => (u, v) ∈ x.graph.edges)
    (R' := fun u v => (u, v) ∈ (toAny x).edges) (by simp [mem_toAny_edges])
    (fun a => by
      rw [mem_toAny_edges]
      refine ⟨?_, fun h => Or.inl ⟨rfl, by rw [h]⟩⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨_, _, -, h, -⟩) <;> omega)
    (fun b => by
      rw [mem_toAny_edges]
      refine ⟨?_, fun h => Or.inr (Or.inl ⟨by rw [h], rfl⟩)⟩
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨_, _, -, -, h⟩) <;> omega)
    (fun a b => ⟨shifted_edge, fun h => mem_toAny_edges.2 (Or.inr (Or.inr ⟨a, b, h, rfl, rfl⟩))⟩)
  constructor
  · rintro ⟨p, hnd, hcov, -, hch⟩
    -- no arc enters `0` and no arc leaves `1`, so the path runs from `0` to `1`
    exact hpath.1 ⟨p, hnd, hcov,
      head?_eq_of_forall_not_rel hch ((hcov 0).2 (by simp [toAny]))
        fun _ h => by rw [mem_toAny_edges] at h; omega,
      getLast?_eq_of_forall_not_rel hch ((hcov 1).2 (by simp [toAny]))
        fun _ h => by rw [mem_toAny_edges] at h; omega, hch⟩
  · intro hx
    obtain ⟨p, hnd, hcov, h0, -, hch⟩ := hpath.2 hx
    exact ⟨p, hnd, hcov, by rintro rfl; simp at h0, hch⟩

/-- The reduction `DirHamPath.toAny` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toAny :
    ComputableInPolyTime toAny encPathInstance encGraph := by
  have hadd : ComputableInPolyTime (· + 2 : ℕ → ℕ) encNat encNat :=
    binary_add' .id' (const 2)
  unfold toAny
  fun_prop

end DirHamPath

/-- `DirHamPath` reduces to `DirHamPathAny` in polynomial time via `DirHamPath.toAny`. -/
theorem polyTimeReducible_DirHamPath_DirHamPathAny :
    PolyTimeReducible encPathInstance encGraph DirHamPath DirHamPathAny :=
  ⟨DirHamPath.toAny, DirHamPath.computableInPolyTime_toAny,
    fun x => (DirHamPath.toAny_mem_iff x).symm⟩

/-- `DirHamPathAny` is `NP`-hard. -/
theorem DirHamPathAny_npHard : NPHard encGraph DirHamPathAny :=
  DirHamPath_npHard.trans polyTimeReducible_DirHamPath_DirHamPathAny

/-- **Directed Hamiltonian path, without given endpoints, is `NP`-complete**
[Arora and Barak, draft, Theorem 2.18][AroraBarak07]. -/
theorem DirHamPathAny_npComplete : NPComplete encGraph DirHamPathAny :=
  ⟨DirHamPathAny.mem_NP, DirHamPathAny_npHard⟩

/-! ### Undirected Hamiltonian paths between unspecified endpoints -/

/-- The undirected graphs with a Hamiltonian path between some declared vertices: the language
HAMPATH of [Arora and Barak, draft, Exercise 2.17][AroraBarak07], whose instances are graphs alone.
The path is a Hamiltonian walk (Mathlib's `SimpleGraph.Walk.IsHamiltonian`) of the graph induced
on the declared vertices, as in `HamPath`. **Empty-graph convention:** the endpoints must be
declared vertices, so a graph without declared vertices is not a member
(`HamPathAny.notMem_of_vertices_eq_nil`), while a graph with exactly one distinct declared vertex
is a member, through the walk of length zero. -/
def HamPathAny : Set Graph := {G | ∃ s t, (⟨G, s, t⟩ : PathInstance) ∈ HamPath}

/-- Undirected Hamiltonian paths between unspecified endpoints as lists of vertices: a nonempty
list of every declared vertex exactly once whose consecutive vertices are adjacent. -/
theorem mem_HamPathAny_iff {G : Graph} :
    G ∈ HamPathAny ↔ ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.vertices) ∧ p ≠ [] ∧
      p.IsChain G.toSimpleGraph.Adj := by
  simp only [HamPathAny, Set.mem_ofPred_eq, mem_HamPath_iff]
  constructor
  · rintro ⟨s, t, p, hnd, hcov, hs, -, hch⟩
    exact ⟨p, hnd, hcov, by rintro rfl; simp at hs, hch⟩
  · rintro ⟨p, hnd, hcov, hne, hch⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨a, _, _, hnd, hcov, rfl, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hch⟩

namespace HamPathAny

/-- **Empty-graph convention**: a graph without declared vertices has no Hamiltonian path. -/
theorem notMem_of_vertices_eq_nil {G : Graph} (h : G.vertices = []) : G ∉ HamPathAny := by
  rintro ⟨s, t, hs, -⟩
  simp [h] at hs

/-- A graph with a single declared vertex has a Hamiltonian path, of length zero. -/
theorem mem_of_vertices_eq_singleton {G : Graph} {v : ℕ} (h : G.vertices = [v]) :
    G ∈ HamPathAny :=
  mem_HamPathAny_iff.2 ⟨[v], List.nodup_singleton v, fun w => by simp [h], List.cons_ne_nil _ _,
    List.isChain_singleton v⟩

/-- The verifier for `HamPathAny`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it is nonempty, lists every declared vertex exactly
once, and that consecutive vertices are adjacent. -/
def verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.vertices) fun G p =>
    decide (p ≠ []) && Graph.chainBool G.adjBool p

/-- `HamPathAny.verifier` verifies `HamPathAny` with certificates of length `n ^ 2` for graphs of
encoded length `n`. -/
theorem isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier HamPathAny := fun G => by
  rw [mem_HamPathAny_iff]
  exact isVerifier_anyVerifier (R := fun G => G.toSimpleGraph.Adj) Graph.adjBool_eq_true_iff G

/-- The `HamPathAny` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encGraph encBits) encBool :=
  computableInPolyTime_anyVerifier Graph.computableInPolyTime_adjBool

/-- `HamPathAny` belongs to `NP`. -/
theorem mem_NP : HamPathAny ∈ NP encGraph :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

end HamPathAny

/-! ### The reduction from `HamPath`

The construction `DirHamPath.toAny` also reduces `HamPath` to `HamPathAny`: read as an undirected
graph, it attaches a pendant vertex `0` to `s + 2` and a pendant vertex `1` to `t + 2`. -/

namespace DirHamPath

private theorem adj_toAny_iff {x : PathInstance} {u v : ℕ} :
    (toAny x).toSimpleGraph.Adj u v ↔ (u = 0 ∧ v = x.source + 2) ∨ (v = 0 ∧ u = x.source + 2) ∨
      (u = 1 ∧ v = x.target + 2) ∨ (v = 1 ∧ u = x.target + 2) ∨
      ∃ a b, x.graph.toSimpleGraph.Adj a b ∧ a + 2 = u ∧ b + 2 = v := by
  simp only [Graph.toSimpleGraph_adj, toAny, List.mem_cons, Prod.mk.injEq, List.mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hne, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, h, rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, h, rfl, rfl⟩)⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, ⟨by omega, Or.inl h⟩, rfl, rfl⟩)))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, a, ⟨by omega, Or.inr h⟩, rfl, rfl⟩)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, ⟨hne, h⟩, rfl, rfl⟩)
    · exact ⟨by omega, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨by omega, Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rcases h with h | h
      · exact ⟨by omega, Or.inl (Or.inr (Or.inr ⟨a, b, h, rfl, rfl⟩))⟩
      · exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨b, a, h, rfl, rfl⟩))⟩

/-- The pendant vertex `0` of `toAny x` is adjacent only to `x.source + 2`. -/
private theorem eq_of_adj_toAny_zero {x : PathInstance} {y : ℕ}
    (h : (toAny x).toSimpleGraph.Adj 0 y) : y = x.source + 2 := by
  rw [adj_toAny_iff] at h
  rcases h with h | h | h | h | ⟨_, _, -, h, -⟩ <;> omega

/-- The pendant vertex `1` of `toAny x` is adjacent only to `x.target + 2`. -/
private theorem eq_of_adj_toAny_one {x : PathInstance} {y : ℕ}
    (h : (toAny x).toSimpleGraph.Adj 1 y) : y = x.target + 2 := by
  rw [adj_toAny_iff] at h
  rcases h with h | h | h | h | ⟨_, _, -, h, -⟩ <;> omega

/-- **Correctness of `DirHamPath.toAny` for undirected paths:** the graph `toAny x`, with a pendant
vertex attached to each of `s + 2` and `t + 2`, has a Hamiltonian path exactly when `x.graph` has
one from `s` to `t`. -/
theorem toAny_mem_HamPathAny_iff (x : PathInstance) : toAny x ∈ HamPathAny ↔ x ∈ HamPath := by
  have hpath := exists_toAny_path_iff (x := x) (R := x.graph.toSimpleGraph.Adj)
    (R' := (toAny x).toSimpleGraph.Adj) (fun h => by have := eq_of_adj_toAny_zero h; omega)
    (fun a => ⟨fun h => by have := eq_of_adj_toAny_zero h; omega,
      fun h => adj_toAny_iff.2 (Or.inl ⟨rfl, by rw [h]⟩)⟩)
    (fun b => ⟨fun h => by have := eq_of_adj_toAny_one h.symm; omega,
      fun h => adj_toAny_iff.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [h]⟩))))⟩)
    (fun a b => ⟨fun h => by
      rw [adj_toAny_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨a', b', h, ha, hb⟩
      · omega
      · omega
      · omega
      · omega
      · obtain rfl : a' = a := by omega
        obtain rfl : b' = b := by omega
        exact h,
      fun h => adj_toAny_iff.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, h, rfl, rfl⟩))))⟩)
  rw [mem_HamPathAny_iff, mem_HamPath_iff, ← hpath]
  constructor
  · rintro ⟨p, hnd, hcov, -, hch⟩
    -- the pendant vertices `0` and `1` are the ends; reverse the path if it ends at `0`
    have h0 := hch.head?_eq_or_getLast?_eq_of_rel_eq hnd ((hcov 0).2 (by simp [toAny]))
      fun _ h => h.elim eq_of_adj_toAny_zero fun h => eq_of_adj_toAny_zero h.symm
    have h1 := hch.head?_eq_or_getLast?_eq_of_rel_eq hnd ((hcov 1).2 (by simp [toAny]))
      fun _ h => h.elim eq_of_adj_toAny_one fun h => eq_of_adj_toAny_one h.symm
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · simp [h0] at h1
    · exact ⟨p, hnd, hcov, h0, h1, hch⟩
    · refine ⟨p.reverse, List.nodup_reverse.2 hnd, fun v => by simp [hcov], ?_, ?_,
        List.isChain_reverse.2 (hch.imp fun _ _ h => h.symm)⟩
      · rwa [List.head?_reverse]
      · rwa [List.getLast?_reverse]
    · simp [h0] at h1
  · rintro ⟨p, hnd, hcov, h0, -, hch⟩
    exact ⟨p, hnd, hcov, by rintro rfl; simp at h0, hch⟩

end DirHamPath

/-- `HamPath` reduces to `HamPathAny` in polynomial time via `DirHamPath.toAny`, which attaches a
pendant vertex to each endpoint. -/
theorem polyTimeReducible_HamPath_HamPathAny :
    PolyTimeReducible encPathInstance encGraph HamPath HamPathAny :=
  ⟨DirHamPath.toAny, DirHamPath.computableInPolyTime_toAny,
    fun x => (DirHamPath.toAny_mem_HamPathAny_iff x).symm⟩

/-- `HamPathAny` is `NP`-hard. -/
theorem HamPathAny_npHard : NPHard encGraph HamPathAny :=
  HamPath_npHard.trans polyTimeReducible_HamPath_HamPathAny

/-- **Undirected Hamiltonian path, without given endpoints, is `NP`-complete**
[Arora and Barak, draft, Exercise 2.17][AroraBarak07]. -/
theorem HamPathAny_npComplete : NPComplete encGraph HamPathAny :=
  ⟨HamPathAny.mem_NP, HamPathAny_npHard⟩

end Cslib.Complexity
