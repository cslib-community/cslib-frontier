/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest

/-!
# The state of a call of the certificate procedure

The certificate procedure of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.1,
Algorithm 1, pp. 12–14) maintains, within one call, a set `P` of *portals*, a *spoke* `σ(v)` for
some vertices `v` (an edge from `v` to the portal `π(v)`), and a forest `F`.
`Cslib.Query.Certificate.State` records these together with the instance itself: its vertex set
and its ends map. Following the program's shared design, every instance of the recursion has the
root's edge type `E` and vertex type `V`; a child instance differs only in its vertex set and its
ends map (a projected edge `e` gets the ends `s(π u, π v)`).

The portal `π(v)` is not stored: it is the end of the spoke `σ(v)` other than `v`
(`Cslib.Query.Certificate.State.proj`), and `v` itself when `v` has no spoke.

`Cslib.Query.Certificate.State.Invariant` collects the properties of the state that the batch
procedure (§3.2) preserves and that the correctness argument of §3.3 uses:

* the forest is an acyclic set of admissible edges on the instance's vertices (Claim 3.5, p. 17),
  so it has at most `n - 1` edges (`Cslib.Query.Certificate.State.Invariant.card_forest_le`);
* portals are vertices of the instance;
* a spoke of `v` is an edge with ends `v` and `π v`, and `π v` is a portal;
* every spoke is *supported* by the forest: its ends are joined by forest edges no heavier than
  it. This is the property "whenever a spoke `s` is declared, going forward, it will always be the
  case that `F≤w(s)` connects its endpoints" of §3.3 (p. 17), used in Claim 3.6 and Lemma 3.7.
  It survives every later forest update `F ← MSF(G[F ∪ T])`, by Fact 2.5
  (`Cslib.Multigraph.supported_msf_iff`).

## Main definitions

* `Cslib.Query.Certificate.otherEnd`: the end of an unordered pair other than a given vertex.
* `Cslib.Query.Certificate.State`: the state of a call; `State.init` is its initial value
  (Algorithm 1, lines 3–4).
* `Cslib.Query.Certificate.State.proj`: the portal `π(v)` at the far end of the spoke of `v`.
* `Cslib.Query.Certificate.State.Invariant`: the invariant described above.

## Main results

* `Cslib.Query.Certificate.State.invariant_init`: the initial state satisfies the invariant.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.1–3.3, pp. 12–18.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type} [DecidableEq V]

/-- The end of `z` other than `v`: `x` when `z = s(v, x)`, and `v` itself when `v ∉ z`. -/
def otherEnd (v : V) (z : Sym2 V) : V :=
  if h : v ∈ z then Sym2.Mem.other' h else v

theorem mk_otherEnd {v : V} {z : Sym2 V} (h : v ∈ z) : s(v, otherEnd v z) = z := by
  simp [otherEnd, h]

@[simp] theorem otherEnd_mk (v x : V) : otherEnd v s(v, x) = x :=
  Sym2.congr_right.1 (mk_otherEnd (Sym2.mem_mk_left v x))

theorem otherEnd_mem {v : V} {z : Sym2 V} (h : v ∈ z) : otherEnd v z ∈ z := by
  have := Sym2.mem_mk_right v (otherEnd v z)
  rwa [mk_otherEnd h] at this

/-- The state of one call of the certificate procedure ([KhannaPuttermanSong2026], §3.1,
Algorithm 1, p. 14). -/
structure State (V E : Type) where
  /-- The vertex set `X` of the instance. -/
  vertices : Finset V
  /-- The ends of the edges in the instance; a child instance has projected ends. -/
  ends : E → Sym2 V
  /-- The portals `P`. -/
  portals : Finset V
  /-- The spoke `σ(v)` of each vertex, if any: an edge from `v` to the portal `π(v)`. -/
  spoke : V → Option E
  /-- The forest `F`. -/
  forest : Finset E

namespace State

/-- The initial state on the vertices `X` with ends `ends`: no portals, no spokes and an empty
forest (Algorithm 1, lines 3–4). -/
@[expose, simps]
def init (X : Finset V) (ends : E → Sym2 V) : State V E :=
  ⟨X, ends, ∅, fun _ => none, ∅⟩

/-- The portal `π(v)`: the end of the spoke of `v` other than `v`, and `v` itself when `v` has no
spoke. -/
def proj (st : State V E) (v : V) : V :=
  match st.spoke v with
  | some s => otherEnd v (st.ends s)
  | none => v

theorem proj_of_spoke_eq_some {st : State V E} {v : V} {s : E} (h : st.spoke v = some s) :
    st.proj v = otherEnd v (st.ends s) := by
  simp [proj, h]

/-- A vertex without a spoke is its own portal. -/
theorem proj_of_spoke_eq_none {st : State V E} {v : V} (h : st.spoke v = none) : st.proj v = v := by
  simp [proj, h]

variable [LinearOrder W]

/-- The invariant of the certificate procedure's state, for weights `w` and admissibility `adm`
(see the module documentation). -/
structure Invariant (st : State V E) (w : E → W) (adm : E → Prop) : Prop where
  /-- Forest edges have their ends among the vertices of the instance. -/
  forest_ends : ∀ f ∈ st.forest, ∀ v ∈ st.ends f, v ∈ st.vertices
  /-- The forest is acyclic. -/
  forest_acyclic : IsAcyclic st.ends st.forest
  /-- Forest edges are admissible (Claim 3.5, p. 17). -/
  forest_adm : ∀ f ∈ st.forest, adm f
  /-- Portals are vertices of the instance. -/
  portals_subset : st.portals ⊆ st.vertices
  /-- Only vertices of the instance have spokes. -/
  mem_vertices_of_spoke : ∀ v s, st.spoke v = some s → v ∈ st.vertices
  /-- The spoke of `v` is incident to `v`. -/
  mem_ends_spoke : ∀ v s, st.spoke v = some s → v ∈ st.ends s
  /-- The far end of a spoke is a portal. -/
  proj_mem_portals : ∀ v s, st.spoke v = some s → st.proj v ∈ st.portals
  /-- Every spoke is supported by the forest. -/
  spoke_supported : ∀ v s, st.spoke v = some s → Supported st.ends w st.forest s

/-- The initial state satisfies the invariant. -/
theorem invariant_init (X : Finset V) (ends : E → Sym2 V) (w : E → W) (adm : E → Prop) :
    (init X ends).Invariant w adm where
  forest_ends := by simp [init]
  forest_acyclic := by simpa [init] using isAcyclic_empty
  forest_adm := by simp [init]
  portals_subset := by simp [init]
  mem_vertices_of_spoke := by simp [init]
  mem_ends_spoke := by simp [init]
  proj_mem_portals := by simp [init]
  spoke_supported := by simp [init]

namespace Invariant

variable {st : State V E} {w : E → W} {adm : E → Prop}

/-- A spoke of `v` has the ends `v` and `π v`. -/
theorem ends_spoke (h : st.Invariant w adm) {v : V} {s : E} (hs : st.spoke v = some s) :
    st.ends s = s(v, st.proj v) := by
  rw [proj_of_spoke_eq_some hs, mk_otherEnd (h.mem_ends_spoke v s hs)]

/-- The forest has at most `n - 1` edges. -/
theorem card_forest_le (h : st.Invariant w adm) : #st.forest ≤ #st.vertices - 1 :=
  h.forest_acyclic.card_le h.forest_ends

end Invariant

end State

end Cslib.Query.Certificate
