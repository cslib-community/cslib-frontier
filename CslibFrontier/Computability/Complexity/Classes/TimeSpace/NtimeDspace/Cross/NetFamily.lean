/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.EdgeNetBasic
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Closed

/-!
# Logspace access to network families (Definition 2.1)

A family of networks has *logspace access at size `s`* (Definition 2.1) if, with constants uniform
across the family,

* (a) every network `G` of the family has a description of length `s^{O(1)}`, at most `O(s)`
  edges, `s^{O(1)}` vertices, maximum degree `O(log s)` and vertex functions with values in
  `{0, …, s^{O(1)}}`;
* (b) given read-only access to the description of `G`, one can compute in space `O(log s)` and
  time `s^{O(1)}` its vertex and edge names, its incidences and port orders, and the value of any
  vertex function at any argument.

`LogspaceNetFamily` formalizes this. A family is a membership predicate `Mem w s` ("`w` describes a
network of the family at size `s`") together with the network `net w s` described by `w`, an
`EdgeNet ℤ (Fin (V w s))`: vertices are the names `0, …, V - 1`, edges the names `0, …, M - 1`, each
edge has two distinct ends (parallel edges allowed, no loops), every vertex has its ordered list of
ports, and the vertex functions are integer valued and do not depend on any modulus. The value
`Z(G)` is `(net w s).value : ℤ`; reduced modulo `p` it is the value of `(net w s).mapEval` over
`ZMod p` (`EdgeNet.value_mapEval`).

The machine model for (b) is the verified counter language `ProgLang.Prog`: the description `w` is
its read-only input (`Prog.input`), and each accessor is a closed program on the size `s` and its
arguments. "Space `O(log s)` and time `s^{O(1)}`" is the condition that on arguments in range every
value arising in the evaluation is at most `(s + 2)^C` (`Prog.Bounded`): the compiled counter
machine then keeps `O(1)` registers of `O(log s)` bits, and its loops run at most `(s + 2)^C`
times at a fixed nesting depth. Concretely, the accessors are

* `edgesP`, `vertsP` on `[s]`: the numbers `M` of edges and `V` of vertices;
* `endUP`, `endWP` on `[i, s]`: the two ends of edge `i < M`;
* `degP` on `[v, s]`: the degree of vertex `v < V`, and `portP` on `[v, j, s]`: its `j`-th port;
* `funP` on `[v, A, s]`: the value `f_v(x)` at the argument `x` whose bit on port `j` is bit `j` of
  `A < 2^{deg v}`.

This module holds only the definition (and `EdgeNet.mapEval`), with light imports, so that the
earlier route (NetAccess, which adds the block-network instances of `NetTerm`) and
the current one
(`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cube/NetInst.lean`) can both
import it.

## Main definitions

* `LogspaceNetFamily`: network families with logspace access (Definition 2.1).
* `EdgeNet.mapEval`: the network with vertex functions mapped (to `ZMod p`).

## Main results

* `EdgeNet.value_mapEval`: mapping the vertex functions by a ring map maps the value.

## References

* The paper (`separating-ntime-from-space.tex`), §2, Definition 2.1 (`def:access`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open ProgLang SumProduct

/-! ### Mapping the vertex functions -/

namespace EdgeNet

variable {R S V : Type}

/-- The network with the same graph and the vertex functions composed with `f`. -/
def mapEval (f : R → S) (G : EdgeNet R V) : EdgeNet S V where
  M := G.M
  u := G.u
  w := G.w
  huw := G.huw
  ports := G.ports
  hports := G.hports
  eval v x := f (G.eval v x)

@[simp] theorem mapEval_M (f : R → S) (G : EdgeNet R V) : (G.mapEval f).M = G.M := rfl
@[simp] theorem mapEval_ports (f : R → S) (G : EdgeNet R V) : (G.mapEval f).ports = G.ports := rfl
@[simp] theorem mapEval_u (f : R → S) (G : EdgeNet R V) : (G.mapEval f).u = G.u := rfl
@[simp] theorem mapEval_w (f : R → S) (G : EdgeNet R V) : (G.mapEval f).w = G.w := rfl
@[simp] theorem mapEval_eval (f : R → S) (G : EdgeNet R V) (v : V) (x : List Bool) :
    (G.mapEval f).eval v x = f (G.eval v x) := rfl

/-- **Mapping the vertex functions by a ring map maps the value.** -/
theorem value_mapEval [CommRing R] [CommRing S] [Fintype V] (f : R →+* S) (G : EdgeNet R V) :
    (G.mapEval f).value = f G.value := by
  simp only [value, map_sum, map_prod]
  rfl

end EdgeNet

/-! ### Definition 2.1 -/

/-- **A family of networks with logspace access at size `s`** (Definition 2.1).

`Mem w s` says that `w` describes a network of the family at size `s`; that network is `net w s`,
with `V w s` vertices and integer vertex functions. All conditions are imposed on members only,
with the one constant `C` of the family:

* (a) `length_le`, `edges_le`, `verts_le`, `deg_le`, `eval_mem`: description length `≤ (s+2)^C`,
  at most `C (s+1)` edges, at most `(s+2)^C` vertices, degree at most `C (log₂ s + 1)`, and
  vertex function values in `{0, …, (s+2)^C}` (at arguments of the right length);
  `ports_nodup`: the port list of a vertex lists each edge at it once (it is "the ordered list of
  edges at `v`").
* (b) the closed programs `edgesP`, `vertsP`, `endUP`, `endWP`, `degP`, `portP`, `funP`, reading
  the description as their input, compute the numbers of edges and vertices, the ends of an edge,
  the degree and the ports of a vertex, and the value of a vertex function; on arguments in range,
  every value arising in their evaluation is at most `(s+2)^C`. -/
structure LogspaceNetFamily where
  /-- `w` describes a network of the family at size `s`. -/
  Mem : List Bool → ℕ → Prop
  /-- The number of vertices of the network described by `w` at size `s`. -/
  V : List Bool → ℕ → ℕ
  /-- The network described by `w` at size `s`, with integer vertex functions. -/
  net : (w : List Bool) → (s : ℕ) → EdgeNet ℤ (Fin (V w s))
  /-- The constant of the family. -/
  C : ℕ
  /-- (a) The description has length `s^{O(1)}`. -/
  length_le : ∀ w s, Mem w s → w.length ≤ (s + 2) ^ C
  /-- (a) The network has `O(s)` edges. -/
  edges_le : ∀ w s, Mem w s → (net w s).M ≤ C * (s + 1)
  /-- (a) The network has `s^{O(1)}` vertices. -/
  verts_le : ∀ w s, Mem w s → V w s ≤ (s + 2) ^ C
  /-- (a) The network has maximum degree `O(log s)`. -/
  deg_le : ∀ w s, Mem w s → ∀ v, ((net w s).ports v).length ≤ C * (Nat.log 2 s + 1)
  /-- (a) The vertex functions take values in `{0, …, s^{O(1)}}`. -/
  eval_mem : ∀ w s, Mem w s → ∀ v (x : List Bool), x.length = ((net w s).ports v).length →
    0 ≤ (net w s).eval v x ∧ (net w s).eval v x ≤ (s + 2) ^ C
  /-- The ports of a vertex are the edges at it, each listed once. -/
  ports_nodup : ∀ w s, Mem w s → ∀ v, ((net w s).ports v).Nodup
  /-- (b) The number of edges, on `[s]`. -/
  edgesP : Prog
  /-- (b) The number of vertices, on `[s]`. -/
  vertsP : Prog
  /-- (b) The first end of an edge, on `[i, s]`. -/
  endUP : Prog
  /-- (b) The second end of an edge, on `[i, s]`. -/
  endWP : Prog
  /-- (b) The degree of a vertex, on `[v, s]`. -/
  degP : Prog
  /-- (b) The `j`-th port of a vertex, on `[v, j, s]`. -/
  portP : Prog
  /-- (b) The vertex function of `v` at the bits of `A` on its ports, on `[v, A, s]`. -/
  funP : Prog
  edgesP_closed : Prog'.closed 1 edgesP = true
  vertsP_closed : Prog'.closed 1 vertsP = true
  endUP_closed : Prog'.closed 2 endUP = true
  endWP_closed : Prog'.closed 2 endWP = true
  degP_closed : Prog'.closed 2 degP = true
  portP_closed : Prog'.closed 3 portP = true
  funP_closed : Prog'.closed 3 funP = true
  /-- (b) `edgesP` computes the number of edges in space `O(log s)`. -/
  edgesP_spec : ∀ w s, Mem w s →
    edgesP.eval w [s] = (net w s).M ∧ edgesP.Bounded w ((s + 2) ^ C) [s]
  /-- (b) `vertsP` computes the number of vertices in space `O(log s)`. -/
  vertsP_spec : ∀ w s, Mem w s →
    vertsP.eval w [s] = V w s ∧ vertsP.Bounded w ((s + 2) ^ C) [s]
  /-- (b) `endUP` computes the first end of every edge in space `O(log s)`. -/
  endUP_spec : ∀ w s, Mem w s → ∀ i (hi : i < (net w s).M),
    endUP.eval w [i, s] = ((net w s).u ⟨i, hi⟩ : ℕ) ∧ endUP.Bounded w ((s + 2) ^ C) [i, s]
  /-- (b) `endWP` computes the second end of every edge in space `O(log s)`. -/
  endWP_spec : ∀ w s, Mem w s → ∀ i (hi : i < (net w s).M),
    endWP.eval w [i, s] = ((net w s).w ⟨i, hi⟩ : ℕ) ∧ endWP.Bounded w ((s + 2) ^ C) [i, s]
  /-- (b) `degP` computes the degree of every vertex in space `O(log s)`. -/
  degP_spec : ∀ w s, Mem w s → ∀ v (hv : v < V w s),
    degP.eval w [v, s] = ((net w s).ports ⟨v, hv⟩).length ∧ degP.Bounded w ((s + 2) ^ C) [v, s]
  /-- (b) `portP` computes the port order of every vertex in space `O(log s)`. -/
  portP_spec : ∀ w s, Mem w s → ∀ v (hv : v < V w s) j (hj : j < ((net w s).ports ⟨v, hv⟩).length),
    portP.eval w [v, j, s] = (((net w s).ports ⟨v, hv⟩).get ⟨j, hj⟩ : ℕ) ∧
      portP.Bounded w ((s + 2) ^ C) [v, j, s]
  /-- (b) `funP` computes every vertex function at every argument in space `O(log s)`. -/
  funP_spec : ∀ w s, Mem w s → ∀ v (hv : v < V w s) A, A < 2 ^ ((net w s).ports ⟨v, hv⟩).length →
    (funP.eval w [v, A, s] : ℤ) = (net w s).eval ⟨v, hv⟩
        (List.ofFn fun j : Fin ((net w s).ports ⟨v, hv⟩).length => A.testBit j) ∧
      funP.Bounded w ((s + 2) ^ C) [v, A, s]

end Cslib.Complexity.NtimeDspace.Cross
