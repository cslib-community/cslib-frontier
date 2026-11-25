/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Network
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# Kirchhoff `1`-symbol additive-component frontier deduplication

In a constraint network over a finite abelian group `A`, two dual mechanisms compress the frontier
message across a vertex cut `P`:

1. **`COPY` fan-out components.** A connected `COPY` component `T` forces every edge in `E(T)` to
   carry a single shared value in `A`. Whenever `k = |E(T) ∩ δ(P)| ≥ 1` edges of `T` cross the cut
   `δ(P)`, recording `1` value in `A` determines all `k` cut wires, saving `k - 1` symbols.
2. **Kirchhoff additive (`+` / `XOR`) components.** Dual to `COPY`, let `(K, E(K))` be a connected
   subgraph of additive vertices over `A`, where each vertex `v ∈ K` constrains the signed net flow
   `netFlow G E(K) α v` of its incident internal edges in `E(K)` to equal an external demand
   determined by inputs read at `v` and incident wires outside `E(K)`. By Kirchhoff's divergence
   identity (`Multigraph.sum_netFlow_eq_cutFlow`), the sum of internal net flows on `K ∩ P` equals
   the single boundary flow sum `cutFlow G E(K) P α ∈ A` across `E(K) ∩ δ(P)`, while on `K \ P` it
   equals `- cutFlow G E(K) P α`. Because the signed incidence operator of a connected multigraph
   over `A` has cokernel `A` (`Multigraph.exists_netFlow_eq_iff` — even when `(K, E(K))` has cycles
   and parallel edges), two runs `(x, α)` and `(y, β)` agreeing on non-additive cut wires splice
   across `P` by re-solving `E(K)` internally **if and only if** the single group element
   `cutFlow G E(K) P · ∈ A` matches (`KirchhoffDecomposition.exists_splice_on_component_iff`). When
   `k = |E(K) ∩ δ(P)| ≥ 1` edges of `K` cross `δ(P)`, `1` symbol in `A` replaces all `k` cut wire
   values, saving `k - 1` symbols.

When `(K, E(K))` is a simple forest (`Multigraph.IsForest`: loopless, no parallel edges, and
acyclic, as holds automatically in circuit DAGs where each `+` gate has fan-out routed through
`COPY` junctions), every edge of `E(K)` is a bridge of `(K, E(K))` whose wire value equals the sum
of demands on one side (`Multigraph.eqOn_of_netFlow_eq_of_isForest`). Thus internal additive wire
witnesses are unique, preserving unambiguity of the resulting read-once branching program
(`KirchhoffDecomposition.unambiguous_branchingProgram`).

Finally, because `COPY` vertices and additive vertices are disjoint, any `COPY` edge set touching
`V_copy` is edge-disjoint from any internal additive edge set on `V_add`
(`Multigraph.disjoint_of_subset_touching_of_endpoints`). Both savings therefore apply
simultaneously with zero overlap (`KirchhoffDecomposition.card_cutSymbol_eq`,
`KirchhoffDecomposition.ncard_state_le`, `KirchhoffDecomposition.logb_ncard_state_le`), reducing the
cut alphabet exponent at `P` to

`|δ(P)| - ∑_i (|E_copy i ∩ δ(P)| - 1) - ∑_j (|E_add j ∩ δ(P)| - 1)`

and wiring directly into `ReadOnceNBP` (`KirchhoffDecomposition.branchingProgram`) and `Sweep`
(`KirchhoffDecomposition.sweep`).

The simultaneous `COPY` + Kirchhoff `1`-symbol frontier compression (`KirchhoffDecomposition`,
`kirchhoff_splice`, `branchingProgram`, and `unambiguous_branchingProgram`) is original to this
library.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.edgeContribution`,
  `Cslib.Circuits.Frontier.Multigraph.netFlow`,
  `Cslib.Circuits.Frontier.Multigraph.cutFlow`: signed incidence and boundary cut flow over an
  `AddCommGroup A`.
* `Cslib.Circuits.Frontier.Multigraph.subgraph`,
  `Cslib.Circuits.Frontier.Multigraph.IsForest`: sub-multigraph on `(K, F)` and simple forests.
* `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition`: simultaneous `COPY` and connected additive
  component decomposition of a `Network A ι V E`.
* `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.cutMessage`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.compressedWidth`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.branchingProgram`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.sweep`: compressed frontier messages,
  compressed cut width, exact `ReadOnceNBP`, and `Sweep`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.sum_netFlow_eq_cutFlow`: Kirchhoff's divergence identity.
* `Cslib.Circuits.Frontier.Multigraph.exists_netFlow_eq_iff`: `coker = A` solvability on any
  connected multigraph component (including cyclic multigraphs).
* `Cslib.Circuits.Frontier.Multigraph.eqOn_of_netFlow_eq_of_isForest`: unique wire witnesses on
  acyclic simple forests.
* `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.exists_splice_on_component_iff`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.kirchhoff_splice`: exact `1`-symbol additive
  splicing iff and global simultaneous `COPY` + additive splicing.
* `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.ncard_state_le`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.logb_ncard_state_le`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.accepted_branchingProgram`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.unambiguous_branchingProgram`,
  `Cslib.Circuits.Frontier.Dual.KirchhoffDecomposition.size_branchingProgram_le`: compressed
  state/logarithmic bounds and exact/unambiguous `ReadOnceNBP` size bounds.
-/

public section

namespace Cslib.Circuits.Frontier

open Set

namespace Multigraph

variable {V E A : Type*} [AddCommGroup A] (G : Multigraph V E)

/-! ### Signed incidence and Kirchhoff's divergence identity -/

open Classical in
/-- Signed contribution of an edge `e` under wire assignment `α : E → A` at vertex `v`:
`+ α e` if `v` is the source, `- α e` if `v` is the target, and `0` if `e` is a self-loop at `v`
or not incident to `v`. -/
@[expose]
noncomputable def edgeContribution (α : E → A) (e : E) (v : V) : A :=
  (if G.src e = v then α e else 0) - (if G.tgt e = v then α e else 0)

open Classical in
/-- Net signed outflow of `α : E → A` on the edge subset `F : Set E` at vertex `v`. -/
@[expose]
noncomputable def netFlow [Finite E] (F : Set E) (α : E → A) (v : V) : A :=
  ∑ e ∈ (toFinite F).toFinset, G.edgeContribution α e v

open Classical in
/-- Net signed flow of `α : E → A` on `F : Set E` leaving `P : Set V` across `G.edgeCut P`: each
edge `e ∈ F ∩ G.edgeCut P` contributes `+ α e` when `G.src e ∈ P` and `- α e` when `G.src e ∉ P`. -/
@[expose]
noncomputable def cutFlow [Finite E] (F : Set E) (P : Set V) (α : E → A) : A :=
  ∑ e ∈ (toFinite (F ∩ G.edgeCut P)).toFinset, if G.src e ∈ P then α e else -α e

variable {G}

theorem netFlow_eq_sum [Fintype E] (F : Set E) [DecidablePred (· ∈ F)] (α : E → A) (v : V) :
    G.netFlow F α v = ∑ e ∈ Finset.univ.filter (· ∈ F), G.edgeContribution α e v := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e; simp

theorem netFlow_univ [Fintype E] (α : E → A) (v : V) :
    G.netFlow univ α v = ∑ e : E, G.edgeContribution α e v := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e; simp

theorem cutFlow_eq_sum [Fintype E] (F : Set E) (P : Set V) [DecidablePred (· ∈ F)]
    [DecidablePred (· ∈ P)] (α : E → A) :
    G.cutFlow F P α =
      ∑ e ∈ Finset.univ.filter (fun e => e ∈ F ∧ ¬(G.src e ∈ P ↔ G.tgt e ∈ P)),
        if G.src e ∈ P then α e else -α e := by
  classical
  refine Finset.sum_congr ?_ fun e _ => ?_
  · ext e; simp [mem_edgeCut]
  · by_cases hs : G.src e ∈ P <;> simp [hs]

theorem edgeContribution_of_notMem_incidenceSet {α : E → A} {e : E} {v : V}
    (he : e ∉ G.incidenceSet v) : G.edgeContribution α e v = 0 := by
  have hs : G.src e ≠ v := fun h => he (Or.inl h)
  have ht : G.tgt e ≠ v := fun h => he (Or.inr h)
  simp [edgeContribution, hs, ht]

theorem edgeContribution_congr {α β : E → A} {e : E} {v : V} (h : α e = β e) :
    G.edgeContribution α e v = G.edgeContribution β e v := by
  simp only [edgeContribution, h]

theorem edgeContribution_sub (α β : E → A) (e : E) (v : V) :
    G.edgeContribution (α - β) e v = G.edgeContribution α e v - G.edgeContribution β e v := by
  classical
  simp only [edgeContribution, Pi.sub_apply]
  by_cases hs : G.src e = v <;> by_cases ht : G.tgt e = v <;>
    simp only [hs, ht, ↓reduceIte] <;> abel

/-- `netFlow` at `v` depends only on the values of `α` on `F ∩ G.incidenceSet v`. -/
theorem netFlow_congr [Finite E] {F : Set E} {α β : E → A} {v : V}
    (h : ∀ e ∈ F, e ∈ G.incidenceSet v → α e = β e) :
    G.netFlow F α v = G.netFlow F β v := by
  refine Finset.sum_congr rfl fun e he => ?_
  have heF : e ∈ F := (toFinite F).mem_toFinset.mp he
  by_cases hinc : e ∈ G.incidenceSet v
  · exact G.edgeContribution_congr (h e heF hinc)
  · rw [G.edgeContribution_of_notMem_incidenceSet hinc,
      G.edgeContribution_of_notMem_incidenceSet hinc]

theorem netFlow_sub [Finite E] (F : Set E) (α β : E → A) (v : V) :
    G.netFlow F (α - β) v = G.netFlow F α v - G.netFlow F β v := by
  simp only [netFlow, edgeContribution_sub, Finset.sum_sub_distrib]

@[simp]
theorem netFlow_zero [Finite E] (F : Set E) (v : V) :
    G.netFlow F (0 : E → A) v = 0 := by
  simp [netFlow, edgeContribution]

@[simp]
theorem cutFlow_empty_right [Finite E] (F : Set E) (α : E → A) :
    G.cutFlow F ∅ α = 0 := by
  simp [cutFlow]

@[simp]
theorem cutFlow_univ_right [Finite E] (F : Set E) (α : E → A) :
    G.cutFlow F univ α = 0 := by
  simp [cutFlow]

theorem cutFlow_eq_zero_of_disjoint [Finite E] {F : Set E} {P : Set V} (α : E → A)
    (h : F ∩ G.edgeCut P = ∅) : G.cutFlow F P α = 0 := by
  simp [cutFlow, h]

theorem cutFlow_congr [Finite E] {F : Set E} {P : Set V} {α β : E → A}
    (h : EqOn α β (F ∩ G.edgeCut P)) : G.cutFlow F P α = G.cutFlow F P β := by
  classical
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e ∈ F ∩ G.edgeCut P := (toFinite _).mem_toFinset.mp he
  rw [h he']

/-- Reversing the side of a cut negates `cutFlow`. -/
theorem cutFlow_compl [Finite E] (F : Set E) (P : Set V) (α : E → A) :
    G.cutFlow F Pᶜ α = -G.cutFlow F P α := by
  classical
  have hcut : G.edgeCut Pᶜ = G.edgeCut P := by
    ext e; simp only [mem_edgeCut, mem_compl_iff]; tauto
  have hfin : (toFinite (F ∩ G.edgeCut Pᶜ)).toFinset = (toFinite (F ∩ G.edgeCut P)).toFinset := by
    ext e; simp [hcut]
  rw [cutFlow, cutFlow, hfin, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hs : G.src e ∈ P <;> simp [hs]

open Classical in
private theorem sum_edgeContribution_eq [Finite V] (S : Set V) (α : E → A) (e : E) :
    ∑ v ∈ (toFinite S).toFinset, G.edgeContribution α e v =
      if e ∈ G.edgeCut S then (if G.src e ∈ S then α e else -α e) else 0 := by
  simp only [edgeContribution, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    (toFinite S).mem_toFinset]
  by_cases hs : G.src e ∈ S <;> by_cases ht : G.tgt e ∈ S
  · have hc : e ∉ G.edgeCut S := by simp [mem_edgeCut, hs, ht]
    simp [hs, ht, hc]
  · have hc : e ∈ G.edgeCut S := by simp [mem_edgeCut, hs, ht]
    simp [hs, ht, hc]
  · have hc : e ∈ G.edgeCut S := by simp [mem_edgeCut, hs, ht]
    simp [hs, ht, hc]
  · have hc : e ∉ G.edgeCut S := by simp [mem_edgeCut, hs, ht]
    simp [hs, ht, hc]

variable (G) in
/-- **Kirchhoff's divergence identity.** Summing the net signed outflow of `F` over any vertex set
`S` telescopes internal edges and leaves the signed boundary flow of `F` across `G.edgeCut S`. -/
theorem sum_netFlow_eq_cutFlow [Finite V] [Finite E] (F : Set E) (S : Set V) (α : E → A) :
    ∑ v ∈ (toFinite S).toFinset, G.netFlow F α v = G.cutFlow F S α := by
  classical
  dsimp only [netFlow]
  rw [Finset.sum_comm]
  simp_rw [G.sum_edgeContribution_eq S α]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e
  simp

/-- Stepwise boundary flow update when inserting one new vertex `v ∉ P`. -/
theorem cutFlow_insert [Finite V] [Finite E] (F : Set E) {P : Set V} {v : V} (hv : v ∉ P)
    (α : E → A) :
    G.cutFlow F (insert v P) α = G.cutFlow F P α + G.netFlow F α v := by
  classical
  rw [← G.sum_netFlow_eq_cutFlow F (insert v P) α, ← G.sum_netFlow_eq_cutFlow F P α]
  have hfin : (toFinite (insert v P)).toFinset = insert v (toFinite P).toFinset := by
    ext u; simp
  have hv' : v ∉ (toFinite P).toFinset := by simpa using hv
  rw [hfin, Finset.sum_insert hv', add_comm]

/-- When every edge of `F` has both endpoints in `K`, the net flows of `F` on `K` sum to `0`. -/
theorem sum_netFlow_eq_zero_of_endpoints [Finite V] [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) (α : E → A) :
    ∑ v ∈ (toFinite K).toFinset, G.netFlow F α v = 0 := by
  rw [G.sum_netFlow_eq_cutFlow F K α]
  refine G.cutFlow_eq_zero_of_disjoint α (eq_empty_iff_forall_notMem.mpr fun e ⟨heF, heC⟩ => ?_)
  exact heC (iff_of_true (hF heF).1 (hF heF).2)

/-- When `F` has all endpoints in `K`, summing `netFlow F α` over `K ∩ P` gives `cutFlow F P α`. -/
theorem sum_netFlow_inter_eq_cutFlow [Finite V] [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) (P : Set V) (α : E → A) :
    ∑ v ∈ (toFinite (K ∩ P)).toFinset, G.netFlow F α v = G.cutFlow F P α := by
  classical
  rw [G.sum_netFlow_eq_cutFlow F (K ∩ P) α, cutFlow, cutFlow]
  have hset : F ∩ G.edgeCut (K ∩ P) = F ∩ G.edgeCut P := by
    ext e
    simp only [mem_inter_iff, mem_edgeCut, mem_inter_iff]
    refine and_congr_right fun heF => not_congr ?_
    have hk := hF heF
    tauto
  have hfin : (toFinite (F ∩ G.edgeCut (K ∩ P))).toFinset =
      (toFinite (F ∩ G.edgeCut P)).toFinset := by ext e; simp [hset]
  rw [hfin]
  refine Finset.sum_congr rfl fun e he => ?_
  have heF : e ∈ F := ((toFinite _).mem_toFinset.mp he).1
  simp [(hF heF).1]

/-- When `F` has all endpoints in `K`, summing `netFlow F α` over `K \ P` gives
`- cutFlow F P α`. -/
theorem sum_netFlow_diff_eq_neg_cutFlow [Finite V] [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) (P : Set V) (α : E → A) :
    ∑ v ∈ (toFinite (K \ P)).toFinset, G.netFlow F α v = -G.cutFlow F P α := by
  have hfin : (toFinite (K \ P)).toFinset = (toFinite (K ∩ Pᶜ)).toFinset := by
    ext v; simp [Set.sdiff_eq]
  rw [hfin, G.sum_netFlow_inter_eq_cutFlow hF Pᶜ α, G.cutFlow_compl]

/-! ### Sub-multigraphs, connected `coker = A` solvability, and forest uniqueness -/

variable (G) in
/-- The sub-multigraph on vertex set `K` and edge set `F` when `F` has both endpoints in `K`. -/
@[expose]
def subgraph (K : Set V) (F : Set E) (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) :
    Multigraph K F where
  src e := ⟨G.src e.1, (hF e.2).1⟩
  tgt e := ⟨G.tgt e.1, (hF e.2).2⟩

variable (G) in
/-- A sub-multigraph `(K, F)` is a *simple forest* when it has no self-loops, no parallel edges,
and its underlying simple graph is acyclic. -/
structure IsForest (K : Set V) (F : Set E)
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) : Prop where
  /-- No edge in `F` is a self-loop. -/
  loopless : (G.subgraph K F hF).Loopless
  /-- Distinct edges in `F` have distinct unordered endpoint pairs. -/
  ends_injOn : InjOn G.ends F
  /-- The underlying simple graph on `K` has no cycles. -/
  isAcyclic : (G.subgraph K F hF).toSimpleGraph.IsAcyclic

/-- Edge-disjointness of two edge families whose endpoints lie in disjoint vertex sets: it suffices
that every edge of `E₁` has at least one endpoint in `U` and every edge of `E₂` has both endpoints
in `W`. -/
theorem disjoint_of_subset_touching_of_endpoints {U W : Set V} (hUW : Disjoint U W)
    {E₁ E₂ : Set E} (h₁ : E₁ ⊆ G.touching U)
    (h₂ : ∀ ⦃e⦄, e ∈ E₂ → G.src e ∈ W ∧ G.tgt e ∈ W) : Disjoint E₁ E₂ := by
  rw [disjoint_left]
  intro e he₁ he₂
  rcases h₁ he₁ with hs | ht
  · exact disjoint_left.mp hUW hs (h₂ he₂).1
  · exact disjoint_left.mp hUW ht (h₂ he₂).2

open Classical in
private theorem netFlow_update_edge [Finite E] {F : Set E} {e : E} (he : e ∈ F) (α : E → A)
    (δ : A) (v : V) :
    G.netFlow F (Function.update α e (α e + δ)) v =
      G.netFlow F α v + ((if G.src e = v then δ else 0) - (if G.tgt e = v then δ else 0)) := by
  have hmem : e ∈ (toFinite F).toFinset := (toFinite F).mem_toFinset.mpr he
  dsimp only [netFlow]
  rw [← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase (toFinite F).toFinset (fun f => G.edgeContribution α f v) hmem]
  have hrest : ∑ f ∈ ((toFinite F).toFinset).erase e,
      G.edgeContribution (Function.update α e (α e + δ)) f v =
      ∑ f ∈ ((toFinite F).toFinset).erase e, G.edgeContribution α f v := by
    refine Finset.sum_congr rfl fun f hf => G.edgeContribution_congr ?_
    exact Function.update_of_ne (Finset.ne_of_mem_erase hf) _ _
  rw [hrest]
  simp only [edgeContribution, Function.update_self]
  by_cases hs : G.src e = v <;> by_cases ht : G.tgt e = v <;>
    simp only [hs, ht, ↓reduceIte] <;> abel

open Classical in
private theorem exists_netFlow_shift_adj [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) {u w : K}
    (hadj : (G.subgraph K F hF).toSimpleGraph.Adj u w) (α : E → A) (δ : A) :
    ∃ α' : E → A, EqOn α' α Fᶜ ∧ ∀ z : V,
      G.netFlow F α' z = G.netFlow F α z + (if z = u.1 then δ else 0) -
        (if z = w.1 then δ else 0) := by
  obtain ⟨hne, ⟨e, heF⟩, hends⟩ := toSimpleGraph_adj.mp hadj
  have hval : u.1 ≠ w.1 := Subtype.coe_ne_coe.mpr hne
  have hpair : s(G.src e, G.tgt e) = s(u.1, w.1) := by
    simpa [ends, subgraph, Sym2.map_mk] using congrArg (Sym2.map Subtype.val) hends
  rcases Sym2.eq_iff.mp hpair with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · refine ⟨Function.update α e (α e + δ),
      fun f hf => Function.update_of_ne (fun hfe : f = e => hf (hfe.symm ▸ heF)) _ _, fun z => ?_⟩
    rw [G.netFlow_update_edge heF α δ z, hs, ht]
    by_cases hzu : z = u.1 <;> by_cases hzw : z = w.1 <;>
      simp only [hzu, hzw, hval, hval.symm, eq_comm, ↓reduceIte] <;> abel
  · refine ⟨Function.update α e (α e + -δ),
      fun f hf => Function.update_of_ne (fun hfe : f = e => hf (hfe.symm ▸ heF)) _ _, fun z => ?_⟩
    rw [G.netFlow_update_edge heF α (-δ) z, hs, ht]
    by_cases hzu : z = u.1 <;> by_cases hzw : z = w.1 <;>
      simp only [hzu, hzw, hval, hval.symm, eq_comm, ↓reduceIte] <;> abel

open Classical in
private theorem exists_netFlow_shift_walk [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K) {u r : K}
    (p : (G.subgraph K F hF).toSimpleGraph.Walk u r) (α : E → A) (δ : A) :
    ∃ α' : E → A, EqOn α' α Fᶜ ∧ ∀ z : V,
      G.netFlow F α' z = G.netFlow F α z + (if z = u.1 then δ else 0) -
        (if z = r.1 then δ else 0) := by
  induction p generalizing α with
  | nil =>
    exact ⟨α, eqOn_refl α Fᶜ, fun z => by abel⟩
  | @cons u w r hadj p ih =>
    obtain ⟨α₁, hα₁, hflow₁⟩ := G.exists_netFlow_shift_adj hF hadj α δ
    obtain ⟨α₂, hα₂, hflow₂⟩ := ih α₁
    refine ⟨α₂, hα₂.trans hα₁, fun z => ?_⟩
    rw [hflow₂ z, hflow₁ z]
    abel

/-- **Connected additive solvability (`coker = A`).** On any finite connected sub-multigraph
`(K, F)` (possibly containing cycles, parallel edges, and self-loops), an internal wire assignment
`w : E → A` agreeing with `α₀` outside `F` achieves `netFlow F w v = b v` for all `v ∈ K` **if and
only if** the demands on `K` sum to `0`. -/
theorem exists_netFlow_eq_iff [Finite V] [Finite E] {K : Set V} {F : Set E}
    (hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K)
    (hconn : (G.subgraph K F hF).toSimpleGraph.Connected) (α₀ : E → A) (b : V → A) :
    (∃ w : E → A, EqOn w α₀ Fᶜ ∧ ∀ v ∈ K, G.netFlow F w v = b v) ↔
      ∑ v ∈ (toFinite K).toFinset, b v = 0 := by
  classical
  let _ := Fintype.ofFinite K
  constructor
  · rintro ⟨w, -, hw⟩
    rw [← G.sum_netFlow_eq_zero_of_endpoints hF w]
    exact Finset.sum_congr rfl fun v hv => (hw v ((toFinite K).mem_toFinset.mp hv)).symm
  · intro hsum
    obtain ⟨r⟩ := hconn.nonempty
    let base : E → A := Fᶜ.piecewise α₀ 0
    have hbase_compl : EqOn base α₀ Fᶜ := piecewise_eqOn Fᶜ α₀ 0
    have hbase_flow (z : V) : G.netFlow F base z = 0 :=
      (G.netFlow_congr fun e heF _ => piecewise_eq_of_notMem Fᶜ α₀ 0 (not_notMem.mpr heF)).trans
        (G.netFlow_zero F z)
    -- Push each demand `b u` (`u ∈ K \ {r}`) along a walk in `(K, F)` to the root `r`.
    let S : Finset K := Finset.univ.erase r
    have hpush : ∀ T : Finset K, T ⊆ S → ∃ w : E → A, EqOn w α₀ Fᶜ ∧
        ∀ u : K, u ≠ r → G.netFlow F w u.1 = if u ∈ T then b u.1 else 0 := by
      intro T hTS
      induction T using Finset.induction_on with
      | empty =>
        refine ⟨base, hbase_compl, fun u _ => ?_⟩
        simp [hbase_flow]
      | @insert u₀ T hu₀ ih =>
        obtain ⟨w₀, hw₀_compl, hw₀_flow⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hTS)
        have hu₀_ne : u₀ ≠ r := Finset.ne_of_mem_erase (hTS (Finset.mem_insert_self u₀ T))
        obtain ⟨p⟩ := hconn.preconnected u₀ r
        obtain ⟨w₁, hw₁_compl, hw₁_flow⟩ := G.exists_netFlow_shift_walk hF p w₀ (b u₀.1)
        refine ⟨w₁, hw₁_compl.trans hw₀_compl, fun u hur => ?_⟩
        have hur_val : u.1 ≠ r.1 := Subtype.coe_ne_coe.mpr hur
        rw [hw₁_flow u.1, hw₀_flow u hur, ite_eq_right hur_val, sub_zero]
        rcases eq_or_ne u u₀ with rfl | hu
        · simp [hu₀]
        · simp [hu, Subtype.coe_ne_coe.mpr hu]
    obtain ⟨w, hw_compl, hw_nonroot⟩ := hpush S Finset.Subset.rfl
    refine ⟨w, hw_compl, fun v hvK => ?_⟩
    by_cases hvr : (⟨v, hvK⟩ : K) = r
    · obtain rfl : v = r.1 := congrArg Subtype.val hvr
      have hK_erase : ∀ z ∈ ((toFinite K).toFinset).erase r.1, G.netFlow F w z = b z := by
        intro z hz
        have hz_ne : z ≠ r.1 := Finset.ne_of_mem_erase hz
        have hzK : z ∈ K := (toFinite K).mem_toFinset.mp (Finset.mem_of_mem_erase hz)
        have hsub_ne : (⟨z, hzK⟩ : K) ≠ r := fun h => hz_ne (congrArg Subtype.val h)
        have hmemS : (⟨z, hzK⟩ : K) ∈ S := Finset.mem_erase.mpr ⟨hsub_ne, Finset.mem_univ _⟩
        simpa [hmemS] using hw_nonroot ⟨z, hzK⟩ hsub_ne
      have hr_mem : r.1 ∈ (toFinite K).toFinset := (toFinite K).mem_toFinset.mpr r.2
      have h0 := G.sum_netFlow_eq_zero_of_endpoints hF w
      rw [← Finset.add_sum_erase _ _ hr_mem] at h0 hsum
      rw [Finset.sum_congr rfl hK_erase] at h0
      exact add_right_cancel (h0.trans hsum.symm)
    · have hmemS : (⟨v, hvK⟩ : K) ∈ S := Finset.mem_erase.mpr ⟨hvr, Finset.mem_univ _⟩
      simpa [hmemS] using hw_nonroot ⟨v, hvK⟩ hvr

/-- **Acyclic witness uniqueness.** On any simple forest `(K, F)` (not necessarily connected),
every edge `e ∈ F` is a bridge whose wire value is uniquely determined by the net flows of `F` on
`K`: any two assignments `w₁, w₂` with the same `netFlow F · v` for all `v ∈ K` agree on `F`. -/
theorem eqOn_of_netFlow_eq_of_isForest [Finite V] [Finite E] {K : Set V} {F : Set E}
    {hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K} (hfor : G.IsForest K F hF)
    {w₁ w₂ : E → A} (hflow : ∀ v ∈ K, G.netFlow F w₁ v = G.netFlow F w₂ v) :
    EqOn w₁ w₂ F := by
  classical
  intro e heF
  set H := G.subgraph K F hF
  let e' : F := ⟨e, heF⟩
  let u : K := H.src e'
  let v : K := H.tgt e'
  have huv_ne : u ≠ v := hfor.loopless e'
  have hadj : H.toSimpleGraph.Adj u v := toSimpleGraph_adj.mpr ⟨huv_ne, e', rfl⟩
  have hbridge : ¬(H.toSimpleGraph.deleteEdges {s(u, v)}).Reachable u v :=
    SimpleGraph.isBridge_iff.mp
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hfor.isAcyclic hadj)
  set H' := H.toSimpleGraph.deleteEdges {s(u, v)}
  let C : Set V := Subtype.val '' {z : K | H'.Reachable u z}
  have hCK : C ⊆ K := Subtype.coe_image_subset K _
  have huC : G.src e ∈ C := ⟨u, SimpleGraph.Reachable.refl u, rfl⟩
  have hvC : G.tgt e ∉ C := by
    rintro ⟨z, hrz, hzv⟩
    have hzv' : z = v := Subtype.ext hzv
    exact hbridge (hzv' ▸ hrz)
  have hcut_eq : F ∩ G.edgeCut C = {e} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr ⟨heF, fun h => hvC (h.mp huC)⟩)
    intro f hf
    obtain ⟨hfF, hfC⟩ := hf
    rw [mem_singleton_iff]
    by_contra hfe
    let f' : F := ⟨f, hfF⟩
    have hf_ne : H.src f' ≠ H.tgt f' := hfor.loopless f'
    have hf_adj : H.toSimpleGraph.Adj (H.src f') (H.tgt f') :=
      toSimpleGraph_adj.mpr ⟨hf_ne, f', rfl⟩
    have hends_ne : s(H.src f', H.tgt f') ≠ s(u, v) := by
      intro hends_eq
      have hGends : G.ends f = G.ends e := by
        change s(G.src f, G.tgt f) = s(G.src e, G.tgt e)
        simpa [H, subgraph, Sym2.map_mk, f', e', u, v] using
          congrArg (Sym2.map Subtype.val) hends_eq
      exact hfe (hfor.ends_injOn hfF heF hGends)
    have hf_del : H'.Adj (H.src f') (H.tgt f') :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hf_adj, Set.notMem_singleton_iff.mpr hends_ne⟩
    have hsrcC : G.src f ∈ C ↔ H'.Reachable u (H.src f') :=
      Subtype.val_injective.mem_set_image (a := H.src f')
    have htgtC : G.tgt f ∈ C ↔ H'.Reachable u (H.tgt f') :=
      Subtype.val_injective.mem_set_image (a := H.tgt f')
    have hiff : G.src f ∈ C ↔ G.tgt f ∈ C := by
      rw [hsrcC, htgtC]
      exact ⟨fun hr => hr.trans hf_del.reachable, fun hr => hr.trans hf_del.symm.reachable⟩
    exact hfC hiff
  have hval (w : E → A) : ∑ z ∈ (toFinite C).toFinset, G.netFlow F w z = w e := by
    rw [G.sum_netFlow_eq_cutFlow F C w, cutFlow]
    have hfin : (toFinite (F ∩ G.edgeCut C)).toFinset = {e} := by ext f; simp [hcut_eq]
    rw [hfin, Finset.sum_singleton, ite_eq_left huC]
  rw [← hval w₁, ← hval w₂]
  exact Finset.sum_congr rfl fun z hz => hflow z (hCK ((toFinite C).mem_toFinset.mp hz))

/-- Global uniqueness of `w` when `(K, F)` is a simple forest and `w₁, w₂` agree outside `F`. -/
theorem eq_of_netFlow_eq_of_isForest [Finite V] [Finite E] {K : Set V} {F : Set E}
    {hF : ∀ ⦃e⦄, e ∈ F → G.src e ∈ K ∧ G.tgt e ∈ K} (hfor : G.IsForest K F hF)
    {w₁ w₂ : E → A} (hcompl : EqOn w₁ w₂ Fᶜ)
    (hflow : ∀ v ∈ K, G.netFlow F w₁ v = G.netFlow F w₂ v) :
    w₁ = w₂ := by
  funext e
  by_cases he : e ∈ F
  · exact G.eqOn_of_netFlow_eq_of_isForest hfor hflow he
  · exact hcompl he

end Multigraph

/-! ### Simultaneous `COPY` + Kirchhoff additive decomposition of a `Network` -/

namespace Dual

/-- A *Kirchhoff decomposition* of a constraint network `N` over an abelian group `A`, bundling
pairwise disjoint `COPY` edge classes (`copyEdges`) and pairwise vertex-disjoint connected additive
subgraphs (`addVerts`, `addEdges`) that are mutually edge-disjoint. -/
structure KirchhoffDecomposition {A ι V E : Type*} [AddCommGroup A] [Finite E]
    (N : Network A ι V E) (ιC ιK : Type*) where
  /-- Edge classes whose wires carry a common `COPY` value in every satisfying assignment. -/
  copyEdges : ιC → Set E
  /-- Distinct `COPY` classes are edge-disjoint. -/
  copyEdges_pairwiseDisjoint : Pairwise fun i₁ i₂ => Disjoint (copyEdges i₁) (copyEdges i₂)
  /-- Every satisfying assignment is constant on each `COPY` edge class. -/
  copy_const : ∀ ⦃x α⦄, N.Satisfies x α → ∀ i, ∀ ⦃e₁⦄, e₁ ∈ copyEdges i →
    ∀ ⦃e₂⦄, e₂ ∈ copyEdges i → α e₁ = α e₂
  /-- Vertex sets of the connected additive (`+` / `XOR`) components. -/
  addVerts : ιK → Set V
  /-- Distinct additive components are vertex-disjoint. -/
  addVerts_pairwiseDisjoint : Pairwise fun j₁ j₂ => Disjoint (addVerts j₁) (addVerts j₂)
  /-- Internal edge sets of the additive components. -/
  addEdges : ιK → Set E
  /-- Every internal edge of additive component `j` has both endpoints in `addVerts j`. -/
  addEdges_endpoints : ∀ j, ∀ ⦃e⦄, e ∈ addEdges j → N.src e ∈ addVerts j ∧ N.tgt e ∈ addVerts j
  /-- Each `COPY` edge class is disjoint from each internal additive edge set. -/
  disjoint_copy_add : ∀ i j, Disjoint (copyEdges i) (addEdges j)
  /-- Each additive component `(addVerts j, addEdges j)` is connected. -/
  add_connected : ∀ j,
    (N.subgraph (addVerts j) (addEdges j) (addEdges_endpoints j)).toSimpleGraph.Connected
  /-- External demand at an additive vertex `v`, read off inputs at `v` and external incident
  wires. -/
  demand : V → (ι → A) → (E → A) → A
  /-- At `v ∈ addVerts j`, `demand v` depends only on inputs read at `v` and incident edges outside
  `addEdges j`. -/
  demand_congr : ∀ j, ∀ v ∈ addVerts j, ∀ x x' α α',
    (∀ i, N.site i = some v → x i = x' i) →
    (∀ e ∈ N.incidenceSet v, e ∉ addEdges j → α e = α' e) →
    demand v x α = demand v x' α'
  /-- At `v ∈ addVerts j`, the local network constraint is
  `netFlow (addEdges j) α v = demand v x α`. -/
  constraint_add_iff : ∀ j, ∀ v ∈ addVerts j, ∀ x α,
    N.Constraint v x α ↔ N.netFlow (addEdges j) α v = demand v x α

namespace KirchhoffDecomposition

variable {A ι V E ιC ιK : Type*} [AddCommGroup A] [Finite E] {N : Network A ι V E}
  (D : KirchhoffDecomposition N ιC ιK)

/-- Distinct additive components have disjoint internal edge sets. -/
theorem addEdges_pairwiseDisjoint :
    Pairwise fun j₁ j₂ => Disjoint (D.addEdges j₁) (D.addEdges j₂) := by
  intro j₁ j₂ hne
  exact N.disjoint_of_subset_touching_of_endpoints (D.addVerts_pairwiseDisjoint hne)
    (fun _ he => Or.inl (D.addEdges_endpoints j₁ he).1) (D.addEdges_endpoints j₂)

/-- Union of all `COPY` edge classes. -/
@[expose]
def allCopyEdges : Set E :=
  ⋃ i, D.copyEdges i

/-- Union of all internal additive edge sets. -/
@[expose]
def allAddEdges : Set E :=
  ⋃ j, D.addEdges j

/-- Cut edges across `P` belonging to neither a `COPY` class nor an additive component. -/
@[expose]
def rawCut (P : Set V) : Set E :=
  N.edgeCut P \ (D.allCopyEdges ∪ D.allAddEdges)

/-- Indices of `COPY` classes that cross `N.edgeCut P`. -/
@[expose]
def activeCopy (P : Set V) : Set ιC :=
  {i | (D.copyEdges i ∩ N.edgeCut P).Nonempty}

/-- Indices of additive components whose internal edges cross `N.edgeCut P`. -/
@[expose]
def activeAdd (P : Set V) : Set ιK :=
  {j | (D.addEdges j ∩ N.edgeCut P).Nonempty}

/-- Disjoint sum of active `COPY` symbols, active Kirchhoff flow symbols, and raw cut edges at
`P`. -/
abbrev CutSymbol (P : Set V) :=
  ↥(D.activeCopy P) ⊕ ↥(D.activeAdd P) ⊕ ↥(D.rawCut P)

open Classical in
/-- Compressed frontier message of an edge assignment `α : E → A` across cut `P`: `1` symbol in `A`
per active `COPY` component, `1` Kirchhoff flow sum in `A` per active additive component, and raw
wire values on the remaining cut edges. -/
noncomputable def cutMessage (P : Set V) (α : E → A) : D.CutSymbol P → A
  | .inl ⟨_, hi⟩ => α hi.some
  | .inr (.inl ⟨j, _⟩) => N.cutFlow (D.addEdges j) P α
  | .inr (.inr ⟨e, _⟩) => α e

/-- Uniform layer-independent state type for `ReadOnceNBP` and `Sweep`. -/
@[nolint unusedArguments]
abbrev State (_D : KirchhoffDecomposition N ιC ιK) :=
  (ιC → Option A) × (ιK → Option A) × (E → Option A)

/-- Canonical empty state at layers with empty frontier (`t = 0` and `t ≥ |V|`). -/
@[nolint unusedArguments]
def emptyState (_D : KirchhoffDecomposition N ιC ιK) : _D.State :=
  (fun _ => none, fun _ => none, fun _ => none)

open Classical in
/-- Uniform layer state encoding `D.cutMessage P α`. -/
noncomputable def state (P : Set V) (α : E → A) : D.State :=
  (fun i => if h : (D.copyEdges i ∩ N.edgeCut P).Nonempty then some (α h.some) else none,
    fun j => if (D.addEdges j ∩ N.edgeCut P).Nonempty then some (N.cutFlow (D.addEdges j) P α)
      else none,
    fun e => if e ∈ D.rawCut P then some (α e) else none)

/-- Compressed cut width (number of `A`-symbols) across `P`. -/
@[expose]
noncomputable def compressedWidth [Finite ιC] [Finite ιK] (P : Set V) : ℕ :=
  (N.edgeCut P).ncard -
    ∑ i ∈ (toFinite (univ : Set ιC)).toFinset, ((D.copyEdges i ∩ N.edgeCut P).ncard - 1) -
    ∑ j ∈ (toFinite (univ : Set ιK)).toFinset, ((D.addEdges j ∩ N.edgeCut P).ncard - 1)

@[simp]
theorem state_of_edgeCut_eq_empty {P : Set V} (hP : N.edgeCut P = ∅) (α : E → A) :
    D.state P α = D.emptyState := by
  ext x <;> simp [state, emptyState, rawCut, hP]

/-- Two assignments have the same uniform `state P` iff they have the same `cutMessage P`. -/
theorem state_eq_iff {P : Set V} {α β : E → A} :
    D.state P α = D.state P β ↔ D.cutMessage P α = D.cutMessage P β := by
  classical
  constructor
  · intro h
    have hC := congrArg Prod.fst h
    have hK := congrArg (Prod.fst ∘ Prod.snd) h
    have hR := congrArg (Prod.snd ∘ Prod.snd) h
    funext s
    rcases s with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨e, he⟩
    · have hi' : (D.copyEdges i ∩ N.edgeCut P).Nonempty := hi
      simpa [cutMessage, state, hi'] using congrFun hC i
    · have hj' : (D.addEdges j ∩ N.edgeCut P).Nonempty := hj
      simpa [cutMessage, state, hj'] using congrFun hK j
    · have he' : e ∈ D.rawCut P := he
      simpa [cutMessage, state, he'] using congrFun hR e
  · intro h
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) (funext fun e => ?_))
    · dsimp only [state]
      split_ifs with hi
      · exact congrArg some (congrFun h (.inl ⟨i, hi⟩))
      · rfl
    · dsimp only [state]
      split_ifs with hj
      · exact congrArg some (congrFun h (.inr (.inl ⟨j, hj⟩)))
      · rfl
    · dsimp only [state]
      split_ifs with he
      · exact congrArg some (congrFun h (.inr (.inr ⟨e, he⟩)))
      · rfl

/-- Matching `cutMessage P` implies matching `cutFlow (D.addEdges j) P` for every `j : ιK`
(active components match by the recorded symbol; inactive components have `0 = 0`). -/
theorem cutFlow_eq_of_state_eq {P : Set V} {α β : E → A} (h : D.state P α = D.state P β)
    (j : ιK) : N.cutFlow (D.addEdges j) P α = N.cutFlow (D.addEdges j) P β := by
  by_cases hj : (D.addEdges j ∩ N.edgeCut P).Nonempty
  · exact congrFun (D.state_eq_iff.mp h) (.inr (.inl ⟨j, hj⟩))
  · rw [not_nonempty_iff_eq_empty] at hj
    rw [N.cutFlow_eq_zero_of_disjoint α hj, N.cutFlow_eq_zero_of_disjoint β hj]

/-- For satisfying assignments, matching `state P` forces equality on all non-additive cut edges. -/
theorem eqOn_nonAdd_cut_of_state_eq {P : Set V} {x y : ι → A} {α β : E → A}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β) (h : D.state P α = D.state P β) :
    EqOn α β (N.edgeCut P \ D.allAddEdges) := by
  have hmsg := D.state_eq_iff.mp h
  rintro e ⟨heC, henotA⟩
  by_cases heCopy : e ∈ D.allCopyEdges
  · obtain ⟨i, hei⟩ := mem_iUnion.mp heCopy
    have hne : (D.copyEdges i ∩ N.edgeCut P).Nonempty := ⟨e, hei, heC⟩
    have hrep : α hne.some = β hne.some := congrFun hmsg (.inl ⟨i, hne⟩)
    rw [D.copy_const hx i hei hne.some_mem.1, hrep, D.copy_const hy i hne.some_mem.1 hei]
  · have heRaw : e ∈ D.rawCut P := ⟨heC, fun hu => hu.elim heCopy henotA⟩
    exact congrFun hmsg (.inr (.inr ⟨e, heRaw⟩))

/-! ### Exact `1`-symbol Kirchhoff splicing iff and global network splicing -/

private theorem not_mem_addEdges_of_notMem_addVerts {j : ιK} {v : V} (hv : v ∉ D.addVerts j)
    {e : E} (he : e ∈ N.incidenceSet v) : e ∉ D.addEdges j := by
  intro hej
  rcases he with rfl | rfl
  · exact hv (D.addEdges_endpoints j hej).1
  · exact hv (D.addEdges_endpoints j hej).2

private theorem not_mem_allAddEdges_of_mem_addVerts {j : ιK} {v : V} (hv : v ∈ D.addVerts j)
    {e : E} (he : e ∈ N.incidenceSet v) (henot : e ∉ D.addEdges j) : e ∉ D.allAddEdges := by
  intro hall
  obtain ⟨j', hej'⟩ := mem_iUnion.mp hall
  by_cases hjj' : j = j'
  · exact henot (hjj' ▸ hej')
  · have hv' : v ∉ D.addVerts j' := disjoint_left.mp (D.addVerts_pairwiseDisjoint hjj') hv
    exact D.not_mem_addEdges_of_notMem_addVerts hv' he hej'

private theorem not_mem_allAddEdges_of_mem_copyEdges {i : ιC} {e : E} (he : e ∈ D.copyEdges i) :
    e ∉ D.allAddEdges := fun hall =>
  (mem_iUnion.mp hall).elim fun j hej => disjoint_left.mp (D.disjoint_copy_add i j) he hej

open Classical in
/-- At an additive vertex in `P`, a splice of `(x, α)` and `(y, β)` has the demand of `(x, α)`. -/
private theorem demand_splice_in {P : Set V} {x z : ι → A} {α β γ : E → A}
    (hx : N.Satisfies x α) (hzx : EqOn z x (N.readIn P))
    (hγ : EqOn γ ((N.touching P).piecewise α β) D.allAddEdgesᶜ) {j : ιK} {v : V}
    (hvK : v ∈ D.addVerts j) (hvP : v ∈ P) :
    D.demand v z γ = N.netFlow (D.addEdges j) α v := by
  rw [(D.constraint_add_iff j v hvK x α).mp (hx v)]
  refine D.demand_congr j v hvK z x γ α (fun i hi => hzx ⟨v, hvP, hi⟩) fun e he henot => ?_
  rw [hγ (D.not_mem_allAddEdges_of_mem_addVerts hvK he henot)]
  exact piecewise_eq_of_mem _ _ _
    (he.imp (fun h : N.src e = v => h ▸ hvP) (fun h : N.tgt e = v => h ▸ hvP))

open Classical in
/-- At an additive vertex outside `P`, a splice of `(x, α)` and `(y, β)` has the demand of
`(y, β)`. -/
private theorem demand_splice_out {P : Set V} {y z : ι → A} {α β γ : E → A}
    (hy : N.Satisfies y β) (hzy : EqOn z y (N.readIn P)ᶜ)
    (hcut : EqOn α β (N.edgeCut P \ D.allAddEdges))
    (hγ : EqOn γ ((N.touching P).piecewise α β) D.allAddEdgesᶜ) {j : ιK} {v : V}
    (hvK : v ∈ D.addVerts j) (hvP : v ∉ P) :
    D.demand v z γ = N.netFlow (D.addEdges j) β v := by
  rw [(D.constraint_add_iff j v hvK y β).mp (hy v)]
  refine D.demand_congr j v hvK z y γ β (fun i hi => hzy fun ⟨u, huP, hiu⟩ =>
    hvP (Option.some_injective _ (hiu.symm.trans hi) ▸ huP)) fun e he henot => ?_
  have henotAll : e ∉ D.allAddEdges := D.not_mem_allAddEdges_of_mem_addVerts hvK he henot
  rw [hγ henotAll]
  by_cases ht : e ∈ N.touching P
  · rw [piecewise_eq_of_mem _ _ _ ht]
    refine hcut ⟨?_, henotAll⟩
    rcases he with h | h <;> rcases ht with h' | h' <;> simp_all [Multigraph.mem_edgeCut]
  · exact piecewise_eq_of_notMem _ _ _ ht

open Classical in
/-- **Exact `1`-symbol Kirchhoff splicing iff on a single additive component `j`** (even with
cycles and parallel edges). Given valid runs `(x, α)` and `(y, β)` agreeing on non-additive cut
edges across `P`, splicing external wires via `(N.touching P).piecewise α β` admits an internal
wire assignment on `D.addEdges j` satisfying every vertex in `D.addVerts j` **if and only if** the
single group element `N.cutFlow (D.addEdges j) P · ∈ A` agrees between `α` and `β`. -/
theorem exists_splice_on_component_iff [Finite V] {P : Set V} {x y z : ι → A} {α β : E → A}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β)
    (hcut : EqOn α β (N.edgeCut P \ D.allAddEdges))
    (hzx : EqOn z x (N.readIn P)) (hzy : EqOn z y (N.readIn P)ᶜ) (j : ιK) :
    (∃ w : E → A, EqOn w ((N.touching P).piecewise α β) (D.addEdges j)ᶜ ∧
      ∀ v ∈ D.addVerts j, N.Constraint v z w) ↔
      N.cutFlow (D.addEdges j) P α = N.cutFlow (D.addEdges j) P β := by
  let γ₀ := (N.touching P).piecewise α β
  -- External demand of `(z, γ₀)` on `D.addVerts j ∩ P` agrees with `(x, α)`, and on
  -- `D.addVerts j \ P` agrees with `(y, β)`.
  have hdem_in {v : V} (hvK : v ∈ D.addVerts j) (hvP : v ∈ P) :
      D.demand v z γ₀ = N.netFlow (D.addEdges j) α v :=
    D.demand_splice_in hx hzx (fun _ _ => rfl) hvK hvP
  have hdem_out {v : V} (hvK : v ∈ D.addVerts j) (hvP : v ∉ P) :
      D.demand v z γ₀ = N.netFlow (D.addEdges j) β v :=
    D.demand_splice_out hy hzy hcut (fun _ _ => rfl) hvK hvP
  -- Rewrite local satisfaction on `D.addVerts j` as `netFlow = demand v z γ₀`.
  have hcon_iff (w : E → A) (hw : EqOn w γ₀ (D.addEdges j)ᶜ) :
      (∀ v ∈ D.addVerts j, N.Constraint v z w) ↔
        ∀ v ∈ D.addVerts j, N.netFlow (D.addEdges j) w v = D.demand v z γ₀ := by
    refine forall₂_congr fun v hvK => (D.constraint_add_iff j v hvK z w).trans ?_
    rw [D.demand_congr j v hvK z z w γ₀ (fun _ _ => rfl) fun e _ henot => hw henot]
  have heq_ex : (∃ w : E → A, EqOn w γ₀ (D.addEdges j)ᶜ ∧
      ∀ v ∈ D.addVerts j, N.Constraint v z w) ↔
      ∃ w : E → A, EqOn w γ₀ (D.addEdges j)ᶜ ∧
        ∀ v ∈ D.addVerts j, N.netFlow (D.addEdges j) w v = D.demand v z γ₀ :=
    exists_congr fun w => and_congr_right (hcon_iff w)
  change (∃ w : E → A, EqOn w γ₀ (D.addEdges j)ᶜ ∧ ∀ v ∈ D.addVerts j, N.Constraint v z w) ↔ _
  rw [heq_ex, N.exists_netFlow_eq_iff (D.addEdges_endpoints j) (D.add_connected j) γ₀
    (fun v => D.demand v z γ₀)]
  -- Split `D.addVerts j` into `D.addVerts j ∩ P` and `D.addVerts j \ P`.
  have hpart : (toFinite (D.addVerts j)).toFinset =
      (toFinite (D.addVerts j ∩ P)).toFinset ∪ (toFinite (D.addVerts j \ P)).toFinset := by
    ext v
    simp only [Finset.mem_union, (toFinite _).mem_toFinset, mem_inter_iff, mem_sdiff]
    tauto
  have hdisj : Disjoint (toFinite (D.addVerts j ∩ P)).toFinset
      (toFinite (D.addVerts j \ P)).toFinset := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact ((toFinite _).mem_toFinset.mp hv₂).2 ((toFinite _).mem_toFinset.mp hv₁).2
  rw [hpart, Finset.sum_union hdisj]
  have hsum_in : ∑ v ∈ (toFinite (D.addVerts j ∩ P)).toFinset, D.demand v z γ₀ =
      N.cutFlow (D.addEdges j) P α := by
    rw [← N.sum_netFlow_inter_eq_cutFlow (D.addEdges_endpoints j) P α]
    exact Finset.sum_congr rfl fun v hv =>
      hdem_in ((toFinite _).mem_toFinset.mp hv).1 ((toFinite _).mem_toFinset.mp hv).2
  have hsum_out : ∑ v ∈ (toFinite (D.addVerts j \ P)).toFinset, D.demand v z γ₀ =
      -N.cutFlow (D.addEdges j) P β := by
    rw [← N.sum_netFlow_diff_eq_neg_cutFlow (D.addEdges_endpoints j) P β]
    exact Finset.sum_congr rfl fun v hv =>
      hdem_out ((toFinite _).mem_toFinset.mp hv).1 ((toFinite _).mem_toFinset.mp hv).2
  rw [hsum_in, hsum_out, ← sub_eq_add_neg, sub_eq_zero]

/-- **Simultaneous `COPY` + Kirchhoff global splicing theorem.** If satisfying runs `(x, α)` and
`(y, β)` have the same compressed state `D.state P` across cut `P`, then splicing `x` on
`N.readIn P` with `y` on `(N.readIn P)ᶜ` produces a globally satisfying assignment `γ` that
preserves all earlier frontier states `D.state Q` (`Q ⊆ P`) from `α` and agrees with
`(N.touching P).piecewise α β` outside `D.allAddEdges`. -/
theorem kirchhoff_splice [Finite V] {P : Set V} {x y z : ι → A} {α β : E → A}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β) (hstate : D.state P α = D.state P β)
    (hzx : EqOn z x (N.readIn P)) (hzy : EqOn z y (N.readIn P)ᶜ) :
    ∃ γ : E → A, N.Satisfies z γ ∧
      (letI := Classical.dec
       EqOn γ ((N.touching P).piecewise α β) D.allAddEdgesᶜ) ∧
      (∀ j, ∀ v ∈ D.addVerts j ∩ P,
        N.netFlow (D.addEdges j) γ v = N.netFlow (D.addEdges j) α v) ∧
      (∀ j, ∀ v ∈ D.addVerts j \ P,
        N.netFlow (D.addEdges j) γ v = N.netFlow (D.addEdges j) β v) := by
  classical
  have hcut := D.eqOn_nonAdd_cut_of_state_eq hx hy hstate
  set γ₀ := (N.touching P).piecewise α β
  have hex (j : ιK) : ∃ w : E → A, EqOn w γ₀ (D.addEdges j)ᶜ ∧
      ∀ v ∈ D.addVerts j, N.Constraint v z w :=
    (D.exists_splice_on_component_iff hx hy hcut hzx hzy j).mpr (D.cutFlow_eq_of_state_eq hstate j)
  choose ws hws_compl hws_con using hex
  let γ : E → A := fun e => if h : ∃ j, e ∈ D.addEdges j then ws h.choose e else γ₀ e
  have hγ_on (j : ιK) : EqOn γ (ws j) (D.addEdges j) := by
    intro e hej
    have hex_e : ∃ j', e ∈ D.addEdges j' := ⟨j, hej⟩
    have heq_j : hex_e.choose = j := by_contra fun hne =>
      disjoint_left.mp (D.addEdges_pairwiseDisjoint hne) hex_e.choose_spec hej
    simp only [γ, hex_e, ↓reduceDIte, heq_j]
  have hγ_off : EqOn γ γ₀ D.allAddEdgesᶜ := by
    intro e henot
    have hno : ¬∃ j, e ∈ D.addEdges j := fun ⟨j, hej⟩ => henot (mem_iUnion.mpr ⟨j, hej⟩)
    simp only [γ, hno, ↓reduceDIte]
  have hγ_inc_add {j : ιK} {v : V} (hvK : v ∈ D.addVerts j) :
      ∀ e ∈ N.incidenceSet v, γ e = ws j e := by
    intro e he
    by_cases hej : e ∈ D.addEdges j
    · exact hγ_on j hej
    · have henotAll : e ∉ D.allAddEdges := D.not_mem_allAddEdges_of_mem_addVerts hvK he hej
      rw [hγ_off henotAll, hws_compl j hej]
  have hsat : N.Satisfies z γ := by
    intro v
    by_cases hvAdd : ∃ j, v ∈ D.addVerts j
    · obtain ⟨j, hvK⟩ := hvAdd
      exact N.constraint_congr v z z (ws j) γ (fun _ _ => rfl)
        (fun e he => (hγ_inc_add hvK e he).symm) (hws_con j v hvK)
    · -- Non-additive vertex: no incident edge lies in `D.allAddEdges`.
      have hinc_off : ∀ e ∈ N.incidenceSet v, γ e = γ₀ e := by
        intro e he
        refine hγ_off fun hall => ?_
        obtain ⟨j, hej⟩ := mem_iUnion.mp hall
        exact D.not_mem_addEdges_of_notMem_addVerts (fun hvj => hvAdd ⟨j, hvj⟩) he hej
      by_cases hvP : v ∈ P
      · refine N.constraint_congr v x z α γ (fun i hi => (hzx ⟨v, hvP, hi⟩).symm)
          (fun e he => ?_) (hx v)
        rw [hinc_off e he]
        dsimp only [γ₀]
        have ht : e ∈ N.touching P :=
          he.imp (fun h : N.src e = v => h ▸ hvP) (fun h : N.tgt e = v => h ▸ hvP)
        exact (piecewise_eq_of_mem _ _ _ ht).symm
      · refine N.constraint_congr v y z β γ (fun i hi => (hzy fun ⟨u, huP, hiu⟩ =>
          hvP (Option.some_injective _ (hiu.symm.trans hi) ▸ huP)).symm)
          (fun e he => ?_) (hy v)
        rw [hinc_off e he]
        dsimp only [γ₀]
        by_cases ht : e ∈ N.touching P
        · rw [piecewise_eq_of_mem _ _ _ ht]
          refine (hcut ⟨?_, fun hall => ?_⟩).symm
          · rcases he with h | h <;> rcases ht with h' | h' <;> simp_all [Multigraph.mem_edgeCut]
          · obtain ⟨j, hej⟩ := mem_iUnion.mp hall
            exact D.not_mem_addEdges_of_notMem_addVerts (fun hvj => hvAdd ⟨j, hvj⟩) he hej
        · exact (piecewise_eq_of_notMem _ _ _ ht).symm
  refine ⟨γ, hsat, hγ_off, fun j v ⟨hvK, hvP⟩ => ?_, fun j v ⟨hvK, hvP⟩ => ?_⟩
  · rw [(D.constraint_add_iff j v hvK z γ).mp (hsat v), D.demand_splice_in hx hzx hγ_off hvK hvP]
  · rw [(D.constraint_add_iff j v hvK z γ).mp (hsat v),
      D.demand_splice_out hy hzy hcut hγ_off hvK hvP]

/-- **Global witness uniqueness under acyclic additive forests.** When every additive component is
a simple forest and non-additive edges are uniquely determined by the input, every input `x` has at
most one satisfying wire assignment globally on `E`. -/
theorem satisfies_unique_of_isForest [Finite V]
    (hfor : ∀ j, N.IsForest (D.addVerts j) (D.addEdges j) (D.addEdges_endpoints j))
    (hnonAdd : ∀ x α₁ α₂, N.Satisfies x α₁ → N.Satisfies x α₂ → EqOn α₁ α₂ D.allAddEdgesᶜ)
    (x : ι → A) {α₁ α₂ : E → A} (h₁ : N.Satisfies x α₁) (h₂ : N.Satisfies x α₂) :
    α₁ = α₂ := by
  have hoff := hnonAdd x α₁ α₂ h₁ h₂
  funext e
  by_cases hall : e ∈ D.allAddEdges
  · obtain ⟨j, hej⟩ := mem_iUnion.mp hall
    refine N.eqOn_of_netFlow_eq_of_isForest (hfor j) (fun v hvK => ?_) hej
    rw [(D.constraint_add_iff j v hvK x α₁).mp (h₁ v),
      (D.constraint_add_iff j v hvK x α₂).mp (h₂ v)]
    exact D.demand_congr j v hvK x x α₁ α₂ (fun _ _ => rfl) fun f hf hfnot =>
      hoff (D.not_mem_allAddEdges_of_mem_addVerts hvK hf hfnot)
  · exact hoff hall

/-! ### Simultaneous zero-overlap cut cardinality and logarithmic bounds -/

private theorem ncard_active_add_excess {κ E' : Type*} [Finite κ] [Finite E'] (S : κ → Set E')
    (hdisj : Pairwise fun k₁ k₂ => Disjoint (S k₁) (S k₂)) :
    {k : κ | (S k).Nonempty}.ncard +
      ∑ k ∈ (toFinite (univ : Set κ)).toFinset, ((S k).ncard - 1) =
      (⋃ k, S k).ncard := by
  classical
  let _ := Fintype.ofFinite κ
  let _ := Fintype.ofFinite E'
  have hu : (toFinite (univ : Set κ)).toFinset = Finset.univ := by ext; simp
  have hact : {k : κ | (S k).Nonempty}.ncard =
      ∑ k ∈ Finset.univ, if (S k).Nonempty then 1 else 0 := by
    have : {k : κ | (S k).Nonempty} = ↑(Finset.univ.filter fun k => (S k).Nonempty) := by
      ext k; simp
    rw [this, ncard_coe_finset, Finset.card_filter]
  rw [hu, hact, ← Finset.sum_add_distrib]
  have hterm : ∀ k : κ, (if (S k).Nonempty then 1 else 0) + ((S k).ncard - 1) = (S k).ncard := by
    intro k
    by_cases hk : (S k).Nonempty
    · have hpos : 1 ≤ (S k).ncard := (ncard_pos (toFinite _)).mpr hk
      rw [ite_eq_left hk]; omega
    · rw [not_nonempty_iff_eq_empty] at hk
      simp [hk]
  simp_rw [hterm]
  have hbi : (⋃ k, S k) = ↑(Finset.univ.biUnion fun k => (toFinite (S k)).toFinset) := by
    ext e; simp
  rw [hbi, ncard_coe_finset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ncard_coe_finset, (toFinite (S k)).coe_toFinset]
  · intro k₁ _ k₂ _ hne
    change Disjoint (toFinite (S k₁)).toFinset (toFinite (S k₂)).toFinset
    rw [← Finset.disjoint_coe, (toFinite _).coe_toFinset, (toFinite _).coe_toFinset]
    exact hdisj hne

/-- Exact natural-number partition identity across any cut `P`: the compressed symbol count plus
the `COPY` excess and the Kirchhoff additive excess equals `(N.edgeCut P).ncard`. -/
theorem card_cutSymbol_add_excess [Finite ιC] [Finite ιK] (P : Set V) :
    Nat.card (D.CutSymbol P) +
      ∑ i ∈ (toFinite (univ : Set ιC)).toFinset, ((D.copyEdges i ∩ N.edgeCut P).ncard - 1) +
      ∑ j ∈ (toFinite (univ : Set ιK)).toFinset, ((D.addEdges j ∩ N.edgeCut P).ncard - 1) =
      (N.edgeCut P).ncard := by
  have hcopy := ncard_active_add_excess (fun i => D.copyEdges i ∩ N.edgeCut P) fun i₁ i₂ hne =>
    (D.copyEdges_pairwiseDisjoint hne).mono inter_subset_left inter_subset_left
  have hadd := ncard_active_add_excess (fun j => D.addEdges j ∩ N.edgeCut P) fun j₁ j₂ hne =>
    (D.addEdges_pairwiseDisjoint hne).mono inter_subset_left inter_subset_left
  have hsym : Nat.card (D.CutSymbol P) =
      (D.activeCopy P).ncard + (D.activeAdd P).ncard + (D.rawCut P).ncard := by
    rw [Nat.card_sum, Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq, add_assoc]
  set UC := ⋃ i, D.copyEdges i ∩ N.edgeCut P
  set UA := ⋃ j, D.addEdges j ∩ N.edgeCut P
  have hdisj_CA : Disjoint UC UA := by
    rw [disjoint_left]
    intro e heC heA
    obtain ⟨i, hei, -⟩ := mem_iUnion.mp heC
    obtain ⟨j, hej, -⟩ := mem_iUnion.mp heA
    exact disjoint_left.mp (D.disjoint_copy_add i j) hei hej
  have hdisj_raw : Disjoint (UC ∪ UA) (D.rawCut P) := by
    rw [disjoint_left]
    rintro e (heC | heA) ⟨-, hnot⟩
    · obtain ⟨i, hei, -⟩ := mem_iUnion.mp heC
      exact hnot (Or.inl (mem_iUnion.mpr ⟨i, hei⟩))
    · obtain ⟨j, hej, -⟩ := mem_iUnion.mp heA
      exact hnot (Or.inr (mem_iUnion.mpr ⟨j, hej⟩))
  have hunion : (UC ∪ UA) ∪ D.rawCut P = N.edgeCut P := by
    ext e
    simp only [UC, UA, rawCut, allCopyEdges, allAddEdges, mem_union, mem_iUnion, mem_inter_iff,
      mem_sdiff]
    constructor
    · rintro ((⟨_, _, heP⟩ | ⟨_, _, heP⟩) | ⟨heP, -⟩) <;> exact heP
    · intro heP
      by_cases hCA : (∃ i, e ∈ D.copyEdges i) ∨ ∃ j, e ∈ D.addEdges j
      · rcases hCA with ⟨i, hi⟩ | ⟨j, hj⟩
        · exact Or.inl (Or.inl ⟨i, hi, heP⟩)
        · exact Or.inl (Or.inr ⟨j, hj, heP⟩)
      · exact Or.inr ⟨heP, hCA⟩
  have htot : (N.edgeCut P).ncard = UC.ncard + UA.ncard + (D.rawCut P).ncard := by
    rw [← hunion, ncard_union_eq hdisj_raw (toFinite _) (toFinite _),
      ncard_union_eq hdisj_CA (toFinite _) (toFinite _)]
  rw [hsym, htot]
  dsimp only [activeCopy, activeAdd] at hsym ⊢
  omega

/-- The number of compressed cut symbols at `P` equals `D.compressedWidth P`. -/
theorem card_cutSymbol_eq [Finite ιC] [Finite ιK] (P : Set V) :
    Nat.card (D.CutSymbol P) = D.compressedWidth P := by
  have h := D.card_cutSymbol_add_excess P
  unfold compressedWidth
  omega

/-- **Simultaneous `COPY` + Kirchhoff state count bound.** Across any cut `P`, the number of
distinct compressed states `D.state P α` realized by any set `W` of edge assignments is at most
`|A| ^ D.compressedWidth P`. -/
theorem ncard_state_le [Finite A] [Finite ιC] [Finite ιK] (P : Set V) (W : Set (E → A)) :
    (D.state P '' W).ncard ≤ Nat.card A ^ D.compressedWidth P := by
  calc (D.state P '' W).ncard
      ≤ (D.cutMessage P '' W).ncard :=
        ncard_image_le_ncard_image_of_factorsThrough (toFinite W) fun _ _ _ _ h =>
          D.state_eq_iff.mpr h
    _ ≤ (univ : Set (D.CutSymbol P → A)).ncard :=
        ncard_le_ncard (subset_univ _) finite_univ
    _ = Nat.card A ^ D.compressedWidth P := by
        rw [ncard_univ, Nat.card_fun, D.card_cutSymbol_eq]

/-- **Logarithmic frontier message bound (`log_{|A|}`).** For `1 < |A|`, the base-`|A|` logarithm
of the number of compressed frontier states across `P` is at most
`|δ(P)| - ∑_i (|E_copy i ∩ δ(P)| - 1) - ∑_j (|E_add j ∩ δ(P)| - 1)`. -/
theorem logb_ncard_state_le [Finite A] [Finite ιC] [Finite ιK] (hA : 1 < Nat.card A)
    (P : Set V) (W : Set (E → A)) :
    Real.logb (Nat.card A) ((D.state P '' W).ncard : ℝ) ≤
      ((N.edgeCut P).ncard : ℝ) -
        ∑ i ∈ (toFinite (univ : Set ιC)).toFinset,
          (((D.copyEdges i ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) -
        ∑ j ∈ (toFinite (univ : Set ιK)).toFinset,
          (((D.addEdges j ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) := by
  have hb : (1 : ℝ) < Nat.card A := by exact_mod_cast hA
  have hcard := D.ncard_state_le P W
  have hsum : ((D.compressedWidth P : ℕ) : ℝ) =
      ((N.edgeCut P).ncard : ℝ) -
        ∑ i ∈ (toFinite (univ : Set ιC)).toFinset,
          (((D.copyEdges i ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) -
        ∑ j ∈ (toFinite (univ : Set ιK)).toFinset,
          (((D.addEdges j ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) := by
    have hex := D.card_cutSymbol_add_excess P
    rw [D.card_cutSymbol_eq] at hex
    have hexR : ((D.compressedWidth P : ℕ) : ℝ) +
        ∑ i ∈ (toFinite (univ : Set ιC)).toFinset,
          (((D.copyEdges i ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) +
        ∑ j ∈ (toFinite (univ : Set ιK)).toFinset,
          (((D.addEdges j ∩ N.edgeCut P).ncard - 1 : ℕ) : ℝ) = ((N.edgeCut P).ncard : ℝ) := by
      exact_mod_cast hex
    linarith
  rw [← hsum]
  rcases Nat.eq_zero_or_pos (D.state P '' W).ncard with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    positivity
  · calc Real.logb (Nat.card A) ((D.state P '' W).ncard : ℝ)
        ≤ Real.logb (Nat.card A) (((Nat.card A ^ D.compressedWidth P : ℕ) : ℝ)) :=
          Real.logb_le_logb_of_le hb (by exact_mod_cast hpos) (by exact_mod_cast hcard)
      _ = (D.compressedWidth P : ℝ) := by
          rw [Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one]

/-! ### Exact `ReadOnceNBP` and `Sweep` integration along a `Layout` -/

section Layout

variable (π : Layout V)

/-- **Kirchhoff-compressed read-once branching program along layout `π`.** Layer `t` stores only
`D.state (π.initial t) α` (`1` symbol per active `COPY` class, `1` Kirchhoff flow sum per active
additive component, and raw values on ungrouped cut edges). -/
noncomputable def branchingProgram : ReadOnceNBP ι A D.State where
  length := Nat.card V + 1
  revealed := N.revealedBy π
  revealed_zero := by simp [Network.revealedBy]
  revealed_length := by simp [Network.revealedBy]
  revealed_mono := N.revealedBy_mono π
  start := D.emptyState
  accept := D.emptyState
  Edge t m a m' := ∃ (x : ι → A) (α : E → A),
    N.Satisfies x α ∧
    m = D.state (π.initial t) α ∧
    m' = D.state (π.initial (t + 1)) α ∧
    (N.revealedBy π (t + 1) \ N.revealedBy π t).domRestrict x = a

private theorem isAcceptingPath_state {x : ι → A} {α : E → A} (hα : N.Satisfies x α) :
    (D.branchingProgram π).IsAcceptingPath x fun t => D.state (π.initial t) α where
  start := D.state_of_edgeCut_eq_empty (by simp) α
  accept := D.state_of_edgeCut_eq_empty (by
    change N.edgeCut (π.initial (Nat.card V + 1)) = ∅
    rw [π.initial_of_card_le (Nat.le_succ _), Multigraph.edgeCut_univ]) α
  edge _ _ := ⟨x, α, hα, rfl, rfl, rfl⟩

/-- When `γ` is produced by `kirchhoff_splice` across `P`, it preserves `D.state Q` from `α` on
every subset `Q ⊆ P`, and when `P' = insert v P` (`v ∉ P`) and `D.state P α = D.state P β`, it
preserves `D.state (insert v P)` from `β`. -/
private theorem state_subset_of_splice [Finite V] {P Q : Set V} (hQP : Q ⊆ P) {α β γ : E → A}
    (hoff : letI := Classical.dec; EqOn γ ((N.touching P).piecewise α β) D.allAddEdgesᶜ)
    (hflow_in : ∀ j, ∀ u ∈ D.addVerts j ∩ P,
      N.netFlow (D.addEdges j) γ u = N.netFlow (D.addEdges j) α u) :
    D.state Q γ = D.state Q α := by
  classical
  have htouchQ {e : E} (heQ : e ∈ N.edgeCut Q) : e ∈ N.touching P :=
    N.touching_mono hQP (N.edgeCut_subset_touching Q heQ)
  rw [D.state_eq_iff]
  funext s
  rcases s with ⟨i, hi⟩ | ⟨j, _⟩ | ⟨e, he⟩
  · dsimp only [cutMessage]
    have hmem : hi.some ∈ D.copyEdges i ∩ N.edgeCut Q := hi.some_mem
    rw [hoff (D.not_mem_allAddEdges_of_mem_copyEdges hmem.1),
      piecewise_eq_of_mem _ _ _ (htouchQ hmem.2)]
  · dsimp only [cutMessage]
    rw [← N.sum_netFlow_inter_eq_cutFlow (D.addEdges_endpoints j) Q γ,
      ← N.sum_netFlow_inter_eq_cutFlow (D.addEdges_endpoints j) Q α]
    exact Finset.sum_congr rfl fun u hu => by
      have hu' : u ∈ D.addVerts j ∩ Q := (toFinite _).mem_toFinset.mp hu
      exact hflow_in j u ⟨hu'.1, hQP hu'.2⟩
  · dsimp only [cutMessage]
    have henotA : e ∉ D.allAddEdges := fun ha => he.2 (Or.inr ha)
    rw [hoff henotA, piecewise_eq_of_mem _ _ _ (htouchQ he.1)]

private theorem state_insert_of_splice [Finite V] {P : Set V} {v : V} (hv : v ∉ P)
    {x y : ι → A} {α β γ : E → A} (hx : N.Satisfies x α) (hy : N.Satisfies y β)
    (hstate : D.state P α = D.state P β)
    (hoff : letI := Classical.dec; EqOn γ ((N.touching P).piecewise α β) D.allAddEdgesᶜ)
    (hflow_in : ∀ j, ∀ u ∈ D.addVerts j ∩ P,
      N.netFlow (D.addEdges j) γ u = N.netFlow (D.addEdges j) α u)
    (hflow_out : ∀ j, ∀ u ∈ D.addVerts j \ P,
      N.netFlow (D.addEdges j) γ u = N.netFlow (D.addEdges j) β u) :
    D.state (insert v P) γ = D.state (insert v P) β := by
  classical
  have hcut := D.eqOn_nonAdd_cut_of_state_eq hx hy hstate
  have nonAdd_eq {e : E} (heC : e ∈ N.edgeCut (insert v P)) (henotA : e ∉ D.allAddEdges) :
      γ e = β e := by
    rw [hoff henotA]
    by_cases ht : e ∈ N.touching P
    · rw [piecewise_eq_of_mem _ _ _ ht]
      refine hcut ⟨?_, henotA⟩
      -- If both endpoints lay in `P`, both would lie in `insert v P`.
      rcases ht with h | h <;> intro hi
      · exact heC (iff_of_true (mem_insert_of_mem v h) (mem_insert_of_mem v (hi.mp h)))
      · exact heC (iff_of_true (mem_insert_of_mem v (hi.mpr h)) (mem_insert_of_mem v h))
    · exact piecewise_eq_of_notMem _ _ _ ht
  rw [D.state_eq_iff]
  funext s
  rcases s with ⟨i, hi⟩ | ⟨j, _⟩ | ⟨e, he⟩
  · dsimp only [cutMessage]
    have hmem : hi.some ∈ D.copyEdges i ∩ N.edgeCut (insert v P) := hi.some_mem
    exact nonAdd_eq hmem.2 (D.not_mem_allAddEdges_of_mem_copyEdges hmem.1)
  · dsimp only [cutMessage]
    rw [N.cutFlow_insert (D.addEdges j) hv γ, N.cutFlow_insert (D.addEdges j) hv β]
    have hP : N.cutFlow (D.addEdges j) P γ = N.cutFlow (D.addEdges j) P β := by
      rw [← D.cutFlow_eq_of_state_eq hstate j,
        ← N.sum_netFlow_inter_eq_cutFlow (D.addEdges_endpoints j) P γ,
        ← N.sum_netFlow_inter_eq_cutFlow (D.addEdges_endpoints j) P α]
      exact Finset.sum_congr rfl fun u hu => hflow_in j u ((toFinite _).mem_toFinset.mp hu)
    have hv_flow : N.netFlow (D.addEdges j) γ v = N.netFlow (D.addEdges j) β v := by
      by_cases hvK : v ∈ D.addVerts j
      · exact hflow_out j v ⟨hvK, hv⟩
      · have h0 (w : E → A) : N.netFlow (D.addEdges j) w v = 0 :=
          (N.netFlow_congr fun e hej heinc =>
            (D.not_mem_addEdges_of_notMem_addVerts hvK heinc hej).elim).trans (N.netFlow_zero _ v)
        rw [h0 γ, h0 β]
    rw [hP, hv_flow]
  · exact nonAdd_eq he.1 (fun ha => he.2 (Or.inr ha))

/-- **Gluing for Kirchhoff-compressed branching programs.** Every accepting path of
`D.branchingProgram π` on `x` is realized as `t ↦ D.state (π.initial t) α` for a global satisfying
assignment `α` of `N` on `x` (without requiring acyclicity!). -/
private theorem exists_satisfies_of_isAcceptingPath [Finite V] {x : ι → A} {γ : ℕ → D.State}
    (hγ : (D.branchingProgram π).IsAcceptingPath x γ) :
    ∃ α : E → A, N.Satisfies x α ∧ ∀ t ≤ Nat.card V + 1, γ t = D.state (π.initial t) α := by
  classical
  -- Induct up to `t = Nat.card V`, splicing step witnesses along `π.initial t`.
  have hind : ∀ t ≤ Nat.card V, ∃ (y : ι → A) (β : E → A),
      N.Satisfies y β ∧ EqOn y x (N.readIn (π.initial t)) ∧
      ∀ s ≤ t, γ s = D.state (π.initial s) β := by
    intro t ht
    induction t with
    | zero =>
      obtain ⟨x₀, α₀, hα₀, _, _, _⟩ := hγ.edge 0 (Nat.succ_pos _)
      refine ⟨x₀, α₀, hα₀, by simp, fun s hs => ?_⟩
      obtain rfl : s = 0 := Nat.le_zero.mp hs
      have hst : γ 0 = D.emptyState := hγ.start
      rw [hst, D.state_of_edgeCut_eq_empty (by simp)]
    | succ t ih =>
      have ht_lt : t < Nat.card V := Nat.lt_of_succ_le ht
      obtain ⟨y_t, β_t, hy_t, hyx, hγβ⟩ := ih ht_lt.le
      obtain ⟨x_t, α_t, hx_t, hm_t, hm_succ, hdom⟩ := hγ.edge t (Nat.lt_succ_of_lt ht_lt)
      set P := π.initial t
      set z : ι → A := (N.readIn P).piecewise y_t x_t
      have hstate : D.state P β_t = D.state P α_t := (hγβ t le_rfl).symm.trans hm_t
      obtain ⟨γ_sp, hsat_sp, hoff_sp, hfin_sp, hfout_sp⟩ :=
        D.kirchhoff_splice hy_t hx_t hstate (piecewise_eqOn _ _ _) (piecewise_eqOn_compl _ _ _)
      refine ⟨z, γ_sp, hsat_sp, ?_, fun s hs => ?_⟩
      · intro i hi
        dsimp only [z]
        by_cases hiP : i ∈ N.readIn P
        · exact (piecewise_eq_of_mem _ _ _ hiP).trans (hyx hiP)
        · rw [piecewise_eq_of_notMem _ _ _ hiP]
          have hnew : i ∈ N.revealedBy π (t + 1) \ N.revealedBy π t := by
            simp only [Network.revealedBy, ht, ht_lt.le, ↓reduceIte, mem_sdiff]
            exact ⟨hi, hiP⟩
          exact congrFun hdom ⟨i, hnew⟩
      · rcases hs.lt_or_eq with hst | rfl
        · have hsle : s ≤ t := Nat.lt_succ_iff.mp hst
          have hsub : π.initial s ⊆ P := fun u hu => lt_of_lt_of_le hu hsle
          rw [hγβ s hsle, ← D.state_subset_of_splice hsub hoff_sp hfin_sp]
        · have hv_notMem : π.symm ⟨t, ht_lt⟩ ∉ P := by
            simp [P, Layout.mem_initial]
          rw [hm_succ, π.initial_succ ht_lt,
            ← D.state_insert_of_splice hv_notMem hy_t hx_t hstate hoff_sp hfin_sp hfout_sp]
  obtain ⟨y, β, hyβ, hyx, hγβ⟩ := hind (Nat.card V) le_rfl
  rw [π.initial_of_card_le le_rfl] at hyx
  have hxβ : N.Satisfies x β := fun v =>
    N.constraint_congr v y x β β (fun i hi => hyx ⟨v, mem_univ v, hi⟩) (fun _ _ => rfl) (hyβ v)
  refine ⟨β, hxβ, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht_lt | rfl
  · exact hγβ t (Nat.lt_succ_iff.mp ht_lt)
  · have hacc : γ (Nat.card V + 1) = D.emptyState := hγ.accept
    rw [hacc,
      D.state_of_edgeCut_eq_empty (by rw [π.initial_of_card_le (Nat.le_succ _),
        Multigraph.edgeCut_univ])]

/-- **Exactness of `D.branchingProgram π`.** The Kirchhoff-compressed read-once branching program
accepts `N.accepted` (even when additive components contain cycles!). -/
theorem accepted_branchingProgram [Finite V] :
    (D.branchingProgram π).accepted = N.accepted := by
  ext x
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨α, hα, -⟩ := D.exists_satisfies_of_isAcceptingPath π hγ
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    exact ⟨_, D.isAcceptingPath_state π hα⟩

/-- **Kirchhoff-compressed sweep of `N.accepted` along layout `π`.** -/
noncomputable def sweep [Finite V] : Sweep N.accepted D.State :=
  D.accepted_branchingProgram π ▸ (D.branchingProgram π).sweep

/-- **Unambiguity of `D.branchingProgram π` under acyclic additive forests.** When every additive
component is a simple forest and non-additive edges are uniquely determined by `x`, the compressed
branching program is `Unambiguous`. -/
theorem unambiguous_branchingProgram [Finite V]
    (hfor : ∀ j, N.IsForest (D.addVerts j) (D.addEdges j) (D.addEdges_endpoints j))
    (hnonAdd : ∀ x α₁ α₂, N.Satisfies x α₁ → N.Satisfies x α₂ → EqOn α₁ α₂ D.allAddEdgesᶜ) :
    (D.branchingProgram π).Unambiguous := by
  intro x γ δ hγ hδ t ht
  obtain ⟨α, hα, hγα⟩ := D.exists_satisfies_of_isAcceptingPath π hγ
  obtain ⟨β, hβ, hδβ⟩ := D.exists_satisfies_of_isAcceptingPath π hδ
  rw [hγα t ht, hδβ t ht, D.satisfies_unique_of_isForest hfor hnonAdd x hα hβ]

/-- At layer `t ≤ |V|`, the states visited by `D.branchingProgram π` on `N.accepted` number at most
`|A| ^ D.compressedWidth (π.initial t)`. -/
private theorem ncard_image_path_le [Finite V] [Finite A] [Finite ιC] [Finite ιK] {t : ℕ}
    (ht : t ≤ Nat.card V) :
    ((fun x => (D.branchingProgram π).path x t) '' N.accepted).ncard ≤
      Nat.card A ^ D.compressedWidth (π.initial t) := by
  have hsub : (fun x => (D.branchingProgram π).path x t) '' N.accepted ⊆
      D.state (π.initial t) '' (univ : Set (E → A)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← D.accepted_branchingProgram π] at hx
    obtain ⟨α, -, hα⟩ := D.exists_satisfies_of_isAcceptingPath π
      ((D.branchingProgram π).isAcceptingPath_path hx)
    exact ⟨α, mem_univ α, (hα t (Nat.le_succ_of_le ht)).symm⟩
  exact (ncard_le_ncard hsub (toFinite _)).trans (D.ncard_state_le (π.initial t) univ)

/-- **Step-`t` edge count of `D.branchingProgram π`.** Because `D.state (π.initial (t + 1)) α` is
uniquely determined by `D.cutMessage (π.initial t) α` and the incident wire values of `α` at the
vertex processed at step `t`, step `t < |V|` has at most
`|A| ^ (D.compressedWidth (π.initial t) + |incidenceSet v_t| + |readAt v_t|)` edges. -/
private theorem ncard_edges_le [Finite V] [Finite ι] [Finite A] [Finite ιC] [Finite ιK] {t : ℕ}
    (ht : t < Nat.card V) :
    ((D.branchingProgram π).edges t).ncard ≤
      Nat.card A ^ (D.compressedWidth (π.initial t) +
        (N.incidenceSet (π.symm ⟨t, ht⟩)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
  classical
  set P := π.initial t
  set v := π.symm ⟨t, ht⟩
  have hvP : v ∉ P := by simp [P, v, Layout.mem_initial]
  let f : (D.branchingProgram π).edges t →
      (D.CutSymbol P → A) × (↥(N.incidenceSet v) → A) × (↥(N.readAt v) → A) := fun e =>
    let h := e.2
    let x := h.choose
    let α := h.choose_spec.choose
    (D.cutMessage P α, (N.incidenceSet v).domRestrict α, (N.readAt v).domRestrict x)
  have hinj : Function.Injective f := by
    intro e₁ e₂ hfeq
    have h₁ := e₁.2.choose_spec.choose_spec
    have h₂ := e₂.2.choose_spec.choose_spec
    set x₁ := e₁.2.choose
    set α₁ := e₁.2.choose_spec.choose
    set x₂ := e₂.2.choose
    set α₂ := e₂.2.choose_spec.choose
    have hinc' : EqOn α₁ α₂ (N.incidenceSet v) :=
      domRestrict_eq_domRestrict_iff.mp (congrArg (Prod.fst ∘ Prod.snd) hfeq)
    have hread' : EqOn x₁ x₂ (N.readAt v) :=
      domRestrict_eq_domRestrict_iff.mp (congrArg (Prod.snd ∘ Prod.snd) hfeq)
    have hstP : D.state P α₁ = D.state P α₂ := D.state_eq_iff.mpr (congrArg Prod.fst hfeq)
    have hm_eq : e₁.1.1 = e₂.1.1 := h₁.2.1.trans (hstP.trans h₂.2.1.symm)
    have ha_eq : e₁.1.2.1 = e₂.1.2.1 := by
      rw [← h₁.2.2.2, ← h₂.2.2.2]
      exact domRestrict_eq_domRestrict_iff.mpr (hread'.mono (N.revealedBy_succ_diff_subset π ht))
    -- `m'` at `π.initial (t + 1) = insert v P` is uniquely determined by `hstP` and `hinc'`.
    have hm'_eq : e₁.1.2.2 = e₂.1.2.2 := by
      rw [h₁.2.2.1, h₂.2.2.1, π.initial_succ ht, D.state_eq_iff]
      funext s
      have hnonAdd {e : E} (heC : e ∈ N.edgeCut (insert v P)) (henotA : e ∉ D.allAddEdges) :
          α₁ e = α₂ e := by
        by_cases hev : e ∈ N.incidenceSet v
        · exact hinc' hev
        · exact D.eqOn_nonAdd_cut_of_state_eq h₁.1 h₂.1 hstP
            ⟨(N.edgeCut_insert_subset v P heC).resolve_right hev, henotA⟩
      rcases s with ⟨i, hi⟩ | ⟨j, _⟩ | ⟨e, he⟩
      · dsimp only [cutMessage]
        exact hnonAdd hi.some_mem.2 (D.not_mem_allAddEdges_of_mem_copyEdges hi.some_mem.1)
      · dsimp only [cutMessage]
        rw [N.cutFlow_insert (D.addEdges j) hvP α₁, N.cutFlow_insert (D.addEdges j) hvP α₂,
          D.cutFlow_eq_of_state_eq hstP j, N.netFlow_congr fun e _ hev => hinc' hev]
      · exact hnonAdd he.1 (fun ha => he.2 (Or.inr ha))
    exact Subtype.ext (Prod.ext hm_eq (Prod.ext ha_eq hm'_eq))
  calc ((D.branchingProgram π).edges t).ncard
      = Nat.card ((D.branchingProgram π).edges t) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card ((D.CutSymbol P → A) × (↥(N.incidenceSet v) → A) × (↥(N.readAt v) → A)) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card A ^ (D.compressedWidth P + (N.incidenceSet v).ncard + (N.readAt v).ncard) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fun,
          D.card_cutSymbol_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← pow_add, ← pow_add,
          add_assoc]

/-- At the final step `t = |V|`, both frontiers are empty and edges are determined by unread
inputs. -/
private theorem ncard_edges_last_le [Finite ι] [Finite A] :
    ((D.branchingProgram π).edges (Nat.card V)).ncard ≤ Nat.card A ^ N.readᶜ.ncard := by
  classical
  have hempty (s : ℕ) (hs : Nat.card V ≤ s) (α : E → A) :
      D.state (π.initial s) α = D.emptyState :=
    D.state_of_edgeCut_eq_empty (by rw [π.initial_of_card_le hs, Multigraph.edgeCut_univ]) α
  have hnewly : (D.branchingProgram π).newly (Nat.card V) = N.readᶜ := by
    simp [ReadOnceNBP.newly, branchingProgram, Network.revealedBy, Network.read,
      π.initial_of_card_le le_rfl, compl_eq_univ_sdiff]
  let f : (D.branchingProgram π).edges (Nat.card V) →
      ((D.branchingProgram π).newly (Nat.card V) → A) := fun e => e.1.2.1
  have hinj : Function.Injective f := by
    intro e₁ e₂ h
    obtain ⟨x₁, α₁, -, hm₁, hm₁', _⟩ := e₁.2
    obtain ⟨x₂, α₂, -, hm₂, hm₂', _⟩ := e₂.2
    have h₁_eq : e₁.1.1 = e₂.1.1 :=
      (hm₁.trans (hempty _ le_rfl α₁)).trans (hm₂.trans (hempty _ le_rfl α₂)).symm
    have h₂_eq : e₁.1.2.2 = e₂.1.2.2 :=
      (hm₁'.trans (hempty _ (Nat.le_succ _) α₁)).trans
        (hm₂'.trans (hempty _ (Nat.le_succ _) α₂)).symm
    exact Subtype.ext (Prod.ext h₁_eq (Prod.ext h h₂_eq))
  calc ((D.branchingProgram π).edges (Nat.card V)).ncard
      = Nat.card ((D.branchingProgram π).edges (Nat.card V)) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card ((D.branchingProgram π).newly (Nat.card V) → A) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card A ^ N.readᶜ.ncard := by
        rw [Nat.card_fun, Nat.card_coe_set_eq, hnewly]

/-- **Total size of the Kirchhoff-compressed `ReadOnceNBP`.** If every frontier `π.initial t` has
compressed width `D.compressedWidth (π.initial t) ≤ w`, maximum degree at most `d`, and at most `m`
inputs read per vertex, then
`(D.branchingProgram π).size ≤ |V| · |A| ^ (w + d + m) + |A| ^ |readᶜ|`. -/
theorem size_branchingProgram_le [Finite V] [Finite ι] [Finite A] [Finite ιC] [Finite ιK]
    {w d m : ℕ} (hw : ∀ t < Nat.card V, D.compressedWidth (π.initial t) ≤ w)
    (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    (D.branchingProgram π).size ≤
      Nat.card V * Nat.card A ^ (w + d + m) + Nat.card A ^ N.readᶜ.ncard := by
  have hA : 1 ≤ Nat.card A := Nat.card_pos
  rw [ReadOnceNBP.size, show (D.branchingProgram π).length = Nat.card V + 1 from rfl,
    Finset.sum_range_succ]
  refine add_le_add ?_ (D.ncard_edges_last_le π)
  calc ∑ t ∈ Finset.range (Nat.card V), ((D.branchingProgram π).edges t).ncard
      ≤ ∑ _t ∈ Finset.range (Nat.card V), Nat.card A ^ (w + d + m) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have ht' : t < Nat.card V := Finset.mem_range.mp ht
        refine (D.ncard_edges_le π ht').trans (Nat.pow_le_pow_right hA ?_)
        have := hw t ht'
        have := hd (π.symm ⟨t, ht'⟩)
        have := hm (π.symm ⟨t, ht'⟩)
        omega
    _ = Nat.card V * Nat.card A ^ (w + d + m) := by simp

/-- **Rectangle-free frontier counting bound with simultaneous `COPY` + Kirchhoff compression.** -/
theorem ncard_accepted_le [Finite V] [Finite ι] [Finite A] [Finite ιC] [Finite ιK] {K : ℕ}
    (hfree : RectangleFree N.accepted K) {w d m : ℕ}
    (hw : ∀ t < Nat.card V, D.compressedWidth (π.initial t) ≤ w)
    (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    N.accepted.ncard ≤
      (K - 1) ^ 2 * (Nat.card V * Nat.card A ^ (w + d + m) + Nat.card A ^ N.readᶜ.ncard) := by
  have h := (D.branchingProgram π).ncard_accepted_le (Nat.succ_pos _) (K := K)
    (by rwa [D.accepted_branchingProgram π])
  rw [D.accepted_branchingProgram π] at h
  exact h.trans (Nat.mul_le_mul_left _ (D.size_branchingProgram_le π hw hd hm))

/-- **Rectangle-bias peeling bound with simultaneous `COPY` + Kirchhoff compression** (under
acyclic additive forests). -/
theorem abs_signedCount_accepted_le [Finite V] [Finite ι] [Finite A] [Finite ιC] [Finite ιK]
    (hfor : ∀ j, N.IsForest (D.addVerts j) (D.addEdges j) (D.addEdges_endpoints j))
    (hnonAdd : ∀ x α₁ α₂, N.Satisfies x α₁ → N.Satisfies x α₂ → EqOn α₁ α₂ D.allAddEdgesᶜ)
    {S : Set (ι → A)} {K : ℕ} {b : ℝ} (hb : 0 ≤ b) (hS : RectangleBias S K b)
    {w d m : ℕ} (hw : ∀ t < Nat.card V, D.compressedWidth (π.initial t) ≤ w)
    (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    |signedCount S N.accepted| ≤ 2 * b * N.accepted.ncard +
      ((K - 1) ^ 2 * (Nat.card V * Nat.card A ^ (w + d + m) + Nat.card A ^ N.readᶜ.ncard) : ℕ) := by
  have h := (D.branchingProgram π).abs_signedCount_accepted_le
    (D.unambiguous_branchingProgram π hfor hnonAdd) (Nat.succ_pos _) hb hS
  rw [D.accepted_branchingProgram π] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact_mod_cast Nat.mul_le_mul_left _ (D.size_branchingProgram_le π hw hd hm)

end Layout

end KirchhoffDecomposition

end Dual

end Cslib.Circuits.Frontier
