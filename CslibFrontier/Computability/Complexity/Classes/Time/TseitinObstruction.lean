/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import CslibFrontier.Logics.Propositional.Tseitin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Tseitin local-extension obstruction and shared-ancestor segregator failure

This module formalizes two explicit counterexamples/obstructions to naive sublinear-communication
and segregator protocols:

1. **Exact characterization of the Tseitin local-extension protocol (Hint 2).**
   For a connected finite simple graph `G = (V, E)` with odd total charge `∑ v, χ v = true`, the
   global system `∀ v, (⊕_{e ∋ v} y e) = χ v` is unsatisfiable. Nevertheless, for any fixed edge
   subset `S ⊆ E` and query budget `q`, the `∃ α : S → Bool, ∀ Q (|Q| ≤ q), ∃ β : E \ S → Bool`
   local-extension protocol accepts if and only if `G.deleteEdges S` retains a connected
   component of cardinality strictly greater than `q`
   (`Cslib.Complexity.tseitinLocalExtension_iff_exists_large_component`).
   On `h`-edge-expanders with `2 * |S| < h * |V|`, such a giant component of size at least
   `|V| - |S| / h` always exists (`Cslib.Complexity.exists_large_component_of_edgeExpander`),
   refuting sublinear-query local extension protocols. Meanwhile, global parity checks
   (`Cslib.Complexity.tseitinSatisfiable_iff_sum_eq_false`, proved by reducing to
   `Cslib.Logic.PL.Tseitin`) resolve Tseitin consistency directly.

2. **Shared-ancestor cheating and boundary separation in local-cone segregator protocols.**
   When two check cones `cone q₁, cone q₂` share an unpinned ancestor `z ∉ J`, an existential
   prover responding per challenge `q` can supply incompatible local assignments for `z` even
   though no single global assignment satisfies all cones
   (`Cslib.Complexity.segregator_shared_ancestor_unsound`).
   Conversely, whenever `J` separates every shared vertex across cones (`IsSeparator J`), local
   acceptance implies global satisfiability (`Cslib.Complexity.localCone_sound_of_separator`).

## Main definitions

* `Cslib.Complexity.tseitinVertexSum`: XOR parity of incident edge bits at vertex `v`.
* `Cslib.Complexity.TseitinSatisfies`, `Cslib.Complexity.TseitinSatisfiable`: local and global
  Tseitin satisfaction on finite graphs.
* `Cslib.Complexity.cutEdges`: edges crossing a vertex cut `U`.
* `Cslib.Complexity.IsEdgeExpander`: combinatorial `h`-edge expansion.
* `Cslib.Complexity.LocalConeProtocol`, `Cslib.Complexity.LocalConeProtocol.IsSeparator`,
  `Cslib.Complexity.LocalConeProtocol.Accepts`: general finite-cone local checking protocol and
  separator predicate.

## Main results

* `Cslib.Complexity.not_tseitinSatisfiable_of_sum_eq_true`: global inconsistency from odd parity.
* `Cslib.Complexity.tseitinSatisfiable_iff_sum_eq_false`: global parity characterization on
  connected finite graphs.
* `Cslib.Complexity.tseitinLocalExtension_iff_exists_large_component`: exact characterization of
  the local-extension protocol.
* `Cslib.Complexity.exists_large_component_of_edgeExpander`: giant component in expanders after
  sublinear edge deletion.
* `Cslib.Complexity.localCone_sound_of_separator`: any separator boundary `J` restores soundness
  of local-cone checking.
* `Cslib.Complexity.segregator_shared_ancestor_unsound`: explicit 3-vertex fork DAG showing
  unsoundness when `J = ∅` and restoration of soundness when shared ancestor `2 ∈ J`.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
-/

public section

namespace Cslib.Complexity

open Finset

/-! ### Tseitin systems on finite simple graphs -/

section Tseitin

variable {V : Type} [Fintype V] [DecidableEq V]

/-- XOR parity of edges incident to `v` in `G` under assignment `y : Sym2 V → Bool`. -/
@[expose] def tseitinVertexSum (G : SimpleGraph V) [DecidableRel G.Adj] (y : Sym2 V → Bool)
    (v : V) : Bool :=
  ∑ e ∈ G.edgeFinset, if v ∈ e then y e else 0

/-- Agreement with `G.neighborFinset`: summing over `G.edgeFinset` filtered by `v ∈ e` equals
summing over `G.neighborFinset v`. -/
theorem tseitinVertexSum_eq_sum_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Sym2 V → Bool) (v : V) :
    tseitinVertexSum G y v = ∑ w ∈ G.neighborFinset v, y s(v, w) := by
  classical
  unfold tseitinVertexSum
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun e he => Sym2.Mem.other (Finset.mem_filter.1 he).2) ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet]
    rw [Sym2.other_spec he.2]
    exact he.1
  · intro e₁ he₁ e₂ he₂ h
    rw [Finset.mem_filter] at he₁ he₂
    calc e₁ = s(v, Sym2.Mem.other he₁.2) := (Sym2.other_spec he₁.2).symm
      _ = s(v, Sym2.Mem.other he₂.2) := by rw [h]
      _ = e₂ := Sym2.other_spec he₂.2
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hw_mem : s(v, w) ∈ G.edgeFinset.filter (v ∈ ·) :=
      Finset.mem_filter.2 ⟨(SimpleGraph.mem_edgeFinset).2 hw, by simp⟩
    refine ⟨s(v, w), hw_mem, ?_⟩
    have hspec : s(v, Sym2.Mem.other (Finset.mem_filter.1 hw_mem).2) = s(v, w) :=
      Sym2.other_spec (Finset.mem_filter.1 hw_mem).2
    rcases Sym2.eq_iff.mp hspec with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (G.ne_of_adj hw)
  · intro e he
    rw [Sym2.other_spec (Finset.mem_filter.1 he).2]

/-- The edge boundary `∂_G(U)`: edges of `G` with exactly one endpoint in `U`. -/
@[expose] def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => (U.filter (· ∈ e)).card = 1

theorem mem_cutEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {e : Sym2 V} :
    e ∈ cutEdges G U ↔
      e ∈ G.edgeFinset ∧ ∃ u w : V, e = s(u, w) ∧ u ∈ U ∧ w ∉ U := by
  classical
  simp only [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨he, hcard⟩
    refine ⟨he, ?_⟩
    induction e using Sym2.ind with
    | h u w =>
      have hne : u ≠ w := G.ne_of_adj he
      by_cases hu : u ∈ U <;> by_cases hw : w ∈ U
      · exfalso
        have heq : U.filter (· ∈ s(u, w)) = {u, w} := by
          ext z
          simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨by rcases h with rfl | rfl <;> assumption, h⟩⟩
        rw [heq, Finset.card_pair hne] at hcard
        omega
      · exact ⟨u, w, rfl, hu, hw⟩
      · exact ⟨w, u, Sym2.eq_swap, hw, hu⟩
      · exfalso
        have heq : U.filter (· ∈ s(u, w)) = ∅ := by
          ext z
          simp only [Finset.mem_filter, Sym2.mem_iff, Finset.notMem_empty, iff_false, not_and,
            not_or]
          intro hz
          exact ⟨fun hzu => hu (hzu ▸ hz), fun hzw => hw (hzw ▸ hz)⟩
        rw [heq, Finset.card_empty] at hcard
        omega
  · rintro ⟨he, u, w, rfl, hu, hw⟩
    refine ⟨he, ?_⟩
    have heq : U.filter (· ∈ s(u, w)) = {u} := by
      ext z
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
      refine ⟨fun ⟨hz, h⟩ => h.resolve_right fun h' => hw (h' ▸ hz), ?_⟩
      rintro rfl
      exact ⟨hu, Or.inl rfl⟩
    rw [heq, Finset.card_singleton]

omit [Fintype V] in
private theorem sum_filter_mem_sym2 {U : Finset V} {e : Sym2 V} (hnd : ¬ e.IsDiag) (b : Bool) :
    (∑ v ∈ U, if v ∈ e then b else (0 : Bool)) =
      if (U.filter (· ∈ e)).card = 1 then b else 0 := by
  induction e using Sym2.ind with
  | h u w =>
    have hne : u ≠ w := hnd
    have hpair : (∑ v ∈ U, if v ∈ s(u, w) then b else (0 : Bool)) =
        (if u ∈ U then b else 0) + (if w ∈ U then b else 0) := by
      by_cases hu : u ∈ U <;> by_cases hw : w ∈ U
      · rw [← Finset.add_sum_erase U _ hu]
        have hwu : w ∈ U.erase u := Finset.mem_erase.2 ⟨hne.symm, hw⟩
        have h2 : (∑ v ∈ U.erase u, if v ∈ s(u, w) then b else (0 : Bool)) = b := by
          rw [← Finset.add_sum_erase (U.erase u) _ hwu]
          have hrest : (∑ v ∈ (U.erase u).erase w, if v ∈ s(u, w) then b else (0 : Bool)) = 0 := by
            refine Finset.sum_eq_zero fun z hz => ?_
            rw [Finset.mem_erase, Finset.mem_erase] at hz
            have hnotin : z ∉ s(u, w) := by simp [Sym2.mem_iff, hz.1, hz.2.1]
            exact ite_eq_right hnotin
          rw [hrest, add_zero]
          exact ite_eq_left (Sym2.mem_mk_right u w)
        rw [h2]
        simp only [Sym2.mem_mk_left u w, hu, hw, ↓reduceIte]
      · rw [← Finset.add_sum_erase U _ hu]
        have hrest : (∑ v ∈ U.erase u, if v ∈ s(u, w) then b else (0 : Bool)) = 0 := by
          refine Finset.sum_eq_zero fun z hz => ?_
          rw [Finset.mem_erase] at hz
          have hzw : z ≠ w := fun h => hw (h ▸ hz.2)
          have hnotin : z ∉ s(u, w) := by simp [Sym2.mem_iff, hz.1, hzw]
          exact ite_eq_right hnotin
        rw [hrest, add_zero]
        simp only [Sym2.mem_mk_left u w, hu, hw, ↓reduceIte, add_zero]
      · rw [← Finset.add_sum_erase U _ hw]
        have hrest : (∑ v ∈ U.erase w, if v ∈ s(u, w) then b else (0 : Bool)) = 0 := by
          refine Finset.sum_eq_zero fun z hz => ?_
          rw [Finset.mem_erase] at hz
          have hzu : z ≠ u := fun h => hu (h ▸ hz.2)
          have hnotin : z ∉ s(u, w) := by simp [Sym2.mem_iff, hz.1, hzu]
          exact ite_eq_right hnotin
        rw [hrest, add_zero]
        simp only [Sym2.mem_mk_right u w, hu, hw, ↓reduceIte, zero_add]
      · have hrest : (∑ v ∈ U, if v ∈ s(u, w) then b else (0 : Bool)) = 0 := by
          refine Finset.sum_eq_zero fun z hz => ?_
          have hzu : z ≠ u := fun h => hu (h ▸ hz)
          have hzw : z ≠ w := fun h => hw (h ▸ hz)
          have hnotin : z ∉ s(u, w) := by simp [Sym2.mem_iff, hzu, hzw]
          exact ite_eq_right hnotin
        rw [hrest]
        simp only [hu, hw, ↓reduceIte, add_zero]
    rw [hpair]
    by_cases hu : u ∈ U <;> by_cases hw : w ∈ U
    · have heq : U.filter (· ∈ s(u, w)) = {u, w} := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨by rcases h with rfl | rfl <;> assumption, h⟩⟩
      rw [heq, Finset.card_pair hne]
      simp [hu, hw, BooleanRing.add_self]
    · have heq : U.filter (· ∈ s(u, w)) = {u} := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        refine ⟨fun ⟨hz, h⟩ => h.resolve_right fun h' => hw (h' ▸ hz), ?_⟩
        rintro rfl
        exact ⟨hu, Or.inl rfl⟩
      rw [heq, Finset.card_singleton]
      simp [hu, hw]
    · have heq : U.filter (· ∈ s(u, w)) = {w} := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        refine ⟨fun ⟨hz, h⟩ => h.resolve_left fun h' => hu (h' ▸ hz), ?_⟩
        rintro rfl
        exact ⟨hw, Or.inr rfl⟩
      rw [heq, Finset.card_singleton]
      simp [hu, hw]
    · have heq : U.filter (· ∈ s(u, w)) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.notMem_empty, iff_false, not_and,
          not_or]
        intro hz
        exact ⟨fun hzu => hu (hzu ▸ hz), fun hzw => hw (hzw ▸ hz)⟩
      rw [heq, Finset.card_empty]
      simp [hu, hw]

/-- **Cut-sum identity for Tseitin systems**: summing the vertex constraints over `U` leaves
precisely the XOR parity of edges crossing `∂_G(U)`. -/
theorem sum_tseitinVertexSum_eq_sum_cutEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : Sym2 V → Bool) (U : Finset V) :
    (∑ v ∈ U, tseitinVertexSum G y v) = ∑ e ∈ cutEdges G U, y e := by
  unfold tseitinVertexSum cutEdges
  rw [Finset.sum_comm]
  calc
    ∑ e ∈ G.edgeFinset, ∑ v ∈ U, (if v ∈ e then y e else (0 : Bool))
      = ∑ e ∈ G.edgeFinset, if (U.filter (· ∈ e)).card = 1 then y e else 0 := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [SimpleGraph.mem_edgeFinset] at he
        exact sum_filter_mem_sym2 (G.not_isDiag_of_mem_edgeSet he) (y e)
    _ = ∑ e ∈ G.edgeFinset.filter fun e => (U.filter (· ∈ e)).card = 1, y e := by
        rw [Finset.sum_filter]

/-- Total parity over all vertices vanishes for every edge assignment. -/
theorem sum_univ_tseitinVertexSum (G : SimpleGraph V) [DecidableRel G.Adj] (y : Sym2 V → Bool) :
    (∑ v : V, tseitinVertexSum G y v) = false := by
  rw [sum_tseitinVertexSum_eq_sum_cutEdges]
  have hempty : cutEdges G Finset.univ = ∅ := by
    ext e
    simp only [mem_cutEdges_iff, Finset.mem_univ, not_true_eq_false, and_false,
      exists_false, Finset.notMem_empty]
  rw [hempty, Finset.sum_empty, Bool.zero_eq_false]

/-- An edge assignment `y` satisfies the Tseitin vertex equations of `(G, χ)` on vertex subset
`Q`. -/
@[expose] def TseitinSatisfies (G : SimpleGraph V) [DecidableRel G.Adj] (χ : V → Bool)
    (y : Sym2 V → Bool) (Q : Finset V) : Prop :=
  ∀ v ∈ Q, tseitinVertexSum G y v = χ v

/-- Global satisfiability of the Tseitin system `(G, χ)`. -/
@[expose] def TseitinSatisfiable (G : SimpleGraph V) [DecidableRel G.Adj] (χ : V → Bool) : Prop :=
  ∃ y : Sym2 V → Bool, TseitinSatisfies G χ y Finset.univ

/-- **Global inconsistency**: whenever `∑ v, χ v = true`, no edge assignment satisfies all vertex
equations of `(G, χ)`. -/
theorem not_tseitinSatisfiable_of_sum_eq_true (G : SimpleGraph V) [DecidableRel G.Adj]
    (χ : V → Bool) (hodd : (∑ v : V, χ v) = true) : ¬ TseitinSatisfiable G χ := by
  rintro ⟨y, hy⟩
  have hsum : (∑ v : V, tseitinVertexSum G y v) = ∑ v : V, χ v :=
    Finset.sum_congr rfl fun v _ => hy v (Finset.mem_univ v)
  rw [sum_univ_tseitinVertexSum, hodd] at hsum
  exact Bool.false_ne_true hsum

/-! ### Connected-graph satisfiability via `Cslib.Logic.PL.Tseitin` -/

section ConnectedSat

open Cslib.Logic.PL

private def endsOfSimple {V : Type} (G : SimpleGraph V) : G.edgeSet → Sym2 V := Subtype.val

private theorem toSimpleGraph_endsOfSimple {V : Type} (G : SimpleGraph V) :
    Cslib.Multigraph.toSimpleGraph (endsOfSimple G) = G := by
  ext u v
  rw [Cslib.Multigraph.toSimpleGraph_adj]
  refine ⟨fun ⟨_, e, he⟩ => ?_, fun hadj => ⟨G.ne_of_adj hadj, ⟨s(u, v), hadj⟩, rfl⟩⟩
  have h2 := e.2
  rw [endsOfSimple] at he
  rw [he] at h2
  exact h2

private theorem tseitinVertexSum_eq_parityOn {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (y : Sym2 V → Bool) (v : V) :
    tseitinVertexSum G y v =
      Cslib.parityOn (Cslib.Multigraph.incidence (endsOfSimple G) v) (fun e => y e.1) := by
  classical
  rw [Cslib.parityOn_eq_sum]
  unfold tseitinVertexSum
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun e he => ⟨e, (SimpleGraph.mem_edgeFinset.1 (Finset.mem_filter.1 he).1)⟩)
    ?_ (fun _ _ _ _ h => congrArg Subtype.val h) ?_ (fun _ _ => rfl)
  · intro e he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    exact Cslib.Multigraph.mem_incidence.2 ⟨he.2, G.not_isDiag_of_mem_edgeSet he.1⟩
  · intro e he
    rw [Cslib.Multigraph.mem_incidence] at he
    exact ⟨e.1, Finset.mem_filter.2 ⟨SimpleGraph.mem_edgeFinset.2 e.2, he.1⟩, Subtype.eta _ _⟩

/-- **Connected-graph parity characterization**: for a connected finite simple graph `G`,
a Tseitin system `(G, χ)` is globally satisfiable if and only if `∑ v, χ v = false`. -/
theorem tseitinSatisfiable_iff_sum_eq_false (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (χ : V → Bool) :
    TseitinSatisfiable G χ ↔ (∑ v : V, χ v) = false := by
  classical
  constructor
  · intro hsat
    by_contra hodd
    exact not_tseitinSatisfiable_of_sum_eq_true G χ (Bool.eq_true_of_not_eq_false hodd) hsat
  · intro heven
    have hG : (Cslib.Multigraph.toSimpleGraph (endsOfSimple G)).Connected := by
      rwa [toSimpleGraph_endsOfSimple G]
    have hχ : Cslib.parityOn Finset.univ χ = false := by
      rwa [Cslib.parityOn_eq_sum]
    obtain ⟨u⟩ := hconn.nonempty
    obtain ⟨σ, hσ⟩ := Tseitin.exists_forall_parityOn_incidence_eq hG χ u
    refine ⟨fun e => if h : e ∈ G.edgeSet then σ ⟨e, h⟩ else false, fun v _ => ?_⟩
    rw [tseitinVertexSum_eq_parityOn G]
    have hσv := hσ v
    rw [hχ, Bool.false_and, Bool.false_xor] at hσv
    convert hσv using 2
    ext ⟨e, he⟩
    simp [he]

/-- On a connected finite simple graph `G`, any proper subset `Q ≠ univ` of Tseitin vertex
equations can be satisfied regardless of `∑ v, χ v`. -/
theorem tseitinSatisfies_of_ne_univ (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (χ : V → Bool) {Q : Finset V} (hQ : Q ≠ Finset.univ) :
    ∃ y : Sym2 V → Bool, TseitinSatisfies G χ y Q := by
  classical
  have hG : (Cslib.Multigraph.toSimpleGraph (endsOfSimple G)).Connected := by
    rwa [toSimpleGraph_endsOfSimple G]
  obtain ⟨σ, hσ⟩ := Tseitin.exists_forall_mem_parityOn_incidence_eq hG χ hQ
  refine ⟨fun e => if h : e ∈ G.edgeSet then σ ⟨e, h⟩ else false, fun v hv => ?_⟩
  rw [tseitinVertexSum_eq_parityOn G]
  convert hσ v hv using 2
  ext ⟨e, he⟩
  simp [he]

end ConnectedSat

/-! ### Exact graph characterization of Hint 2's local-extension protocol -/

omit [DecidableEq V] in
open Classical in
private theorem mem_supp_toFinset_iff {G : SimpleGraph V} (S : Finset (Sym2 V))
    (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) (v : V) :
    v ∈ C.supp.toFinset ↔ (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk v = C := by
  rw [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]

open Classical in
private theorem cutEdges_supp_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) :
    cutEdges G C.supp.toFinset ⊆ S := by
  intro e he
  rw [mem_cutEdges_iff] at he
  rcases he with ⟨heG, u, w, rfl, hu, hw⟩
  by_contra heS
  have hadj : (G.deleteEdges (S : Set (Sym2 V))).Adj u w :=
    SimpleGraph.deleteEdges_adj.2 ⟨SimpleGraph.mem_edgeFinset.mp heG, heS⟩
  have hsame : (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk u =
      (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk w :=
    SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
  rw [mem_supp_toFinset_iff] at hu hw
  exact hw (hsame ▸ hu)

open Classical in
private theorem sum_component_cutEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (α : Sym2 V → Bool)
    [Fintype (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent] :
    (∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
      ∑ e ∈ cutEdges G C.supp.toFinset, α e) = false := by
  have hsub' (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) :
      (∑ e ∈ cutEdges G C.supp.toFinset, α e) =
      ∑ e ∈ S.filter (· ∈ cutEdges G C.supp.toFinset), α e := by
    congr 1
    ext e
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨cutEdges_supp_subset S C h, h⟩, fun h => h.2⟩
  simp_rw [hsub', Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  by_cases heG : e ∈ G.edgeFinset
  · induction e using Sym2.ind with
    | h u w =>
      let Cu := (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk u
      let Cw := (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk w
      by_cases hC : Cu = Cw
      · refine Finset.sum_eq_zero fun C _ => ?_
        split_ifs with hc
        · exfalso
          rw [mem_cutEdges_iff] at hc
          rcases hc with ⟨_, a, b, heq, ha, hb⟩
          rw [mem_supp_toFinset_iff] at ha hb
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hb (hC.symm.trans ha)
          · exact hb (hC.trans ha)
        · rfl
      · have hCu : s(u, w) ∈ cutEdges G Cu.supp.toFinset :=
          mem_cutEdges_iff.mpr ⟨heG, u, w, rfl,
            (mem_supp_toFinset_iff S Cu u).2 rfl,
            fun hh => hC ((mem_supp_toFinset_iff S Cu w).1 hh).symm⟩
        have hCw : s(u, w) ∈ cutEdges G Cw.supp.toFinset :=
          mem_cutEdges_iff.mpr ⟨heG, w, u, Sym2.eq_swap,
            (mem_supp_toFinset_iff S Cw w).2 rfl,
            fun hh => hC ((mem_supp_toFinset_iff S Cw u).1 hh)⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ Cu),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hC, Finset.mem_univ Cw⟩)]
        have hrest : (∑ C ∈ (Finset.univ.erase Cu).erase Cw,
            if s(u, w) ∈ cutEdges G C.supp.toFinset then α s(u, w) else (0 : Bool)) = 0 := by
          refine Finset.sum_eq_zero fun C hCmem => ?_
          rw [Finset.mem_erase, Finset.mem_erase] at hCmem
          split_ifs with hc
          · exfalso
            rw [mem_cutEdges_iff] at hc
            rcases hc with ⟨_, a, b, heq, ha, _⟩
            rw [mem_supp_toFinset_iff] at ha
            rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hCmem.2.1 ha.symm
            · exact hCmem.1 ha.symm
          · rfl
        simp only [hCu, hCw, ↓reduceIte, hrest, add_zero, BooleanRing.add_self]
  · refine Finset.sum_eq_zero fun C _ => ?_
    split_ifs with hc
    · exact absurd (mem_cutEdges_iff.mp hc).1 heG
    · rfl

/-- **Exact characterization of Hint 2's local-extension protocol.**
On a connected graph `G = (V, E)` with odd total Tseitin charge `∑ v, χ v = true`, for any edge
cut `S` and query budget `q`, an existential commitment `α : S → Bool` can be extended to satisfy
every subset `Q` of at most `q` vertices if and only if `G.deleteEdges S` has a connected
component with strictly more than `q` vertices. -/
theorem tseitinLocalExtension_iff_exists_large_component
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (χ : V → Bool)
    (hodd : (∑ v : V, χ v) = true) (S : Finset (Sym2 V)) (q : ℕ) :
    (∃ α : Sym2 V → Bool, ∀ Q : Finset V, Q.card ≤ q →
      ∃ β : Sym2 V → Bool,
        TseitinSatisfies G χ (fun e => if e ∈ S then α e else β e) Q) ↔
    ∃ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent, q < C.supp.ncard := by
  classical
  let instFin : Fintype (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent := Fintype.ofFinite _
  constructor
  · rintro ⟨α, hα⟩
    by_contra hsmall
    push Not at hsmall
    have hdiscrep : (∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        ((∑ v ∈ C.supp.toFinset, χ v) + ∑ e ∈ cutEdges G C.supp.toFinset, α e)) = true := by
      rw [Finset.sum_add_distrib, sum_component_cutEdges, ← Bool.zero_eq_false, add_zero]
      have hpart : (∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
          ∑ v ∈ C.supp.toFinset, χ v) = ∑ v : V, χ v := by
        have hfilt (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) :
            C.supp.toFinset = Finset.univ.filter
              (fun v => (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk v = C) := by
          ext v; simp
        simp_rw [hfilt]
        convert @Finset.sum_fiberwise _ _ _ _ (Classical.decEq _) instFin Finset.univ
          (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk χ
      rw [hpart, hodd]
    have hex_bad : ∃ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        (∑ v ∈ C.supp.toFinset, χ v) + ∑ e ∈ cutEdges G C.supp.toFinset, α e = true := by
      by_contra hall
      push Not at hall
      have hz : (∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
          ((∑ v ∈ C.supp.toFinset, χ v) + ∑ e ∈ cutEdges G C.supp.toFinset, α e)) = false := by
        rw [← Bool.zero_eq_false]
        exact Finset.sum_eq_zero fun C _ => by simpa [Bool.zero_eq_false] using hall C
      rw [hz] at hdiscrep
      exact Bool.false_ne_true hdiscrep
    obtain ⟨C, hC⟩ := hex_bad
    have hcardC : C.supp.toFinset.card ≤ q := by
      rw [← Set.ncard_eq_toFinset_card' C.supp]
      exact hsmall C
    obtain ⟨β, hβ⟩ := hα C.supp.toFinset hcardC
    let y := fun e => if e ∈ S then α e else β e
    have hsum1 : (∑ v ∈ C.supp.toFinset, tseitinVertexSum G y v) =
        ∑ v ∈ C.supp.toFinset, χ v :=
      Finset.sum_congr rfl fun v hv => hβ v hv
    rw [sum_tseitinVertexSum_eq_sum_cutEdges] at hsum1
    have hsum2 : (∑ e ∈ cutEdges G C.supp.toFinset, y e) =
        ∑ e ∈ cutEdges G C.supp.toFinset, α e := by
      refine Finset.sum_congr rfl fun e he => ?_
      simp [y, cutEdges_supp_subset S C he]
    rw [hsum2] at hsum1
    rw [← hsum1, BooleanRing.add_self] at hC
    exact Bool.false_ne_true hC
  · rintro ⟨C₀, hC₀⟩
    rw [Set.ncard_eq_toFinset_card' C₀.supp] at hC₀
    let delG := G.deleteEdges (S : Set (Sym2 V))
    let Gq : SimpleGraph delG.ConnectedComponent :=
      { Adj C₁ C₂ := C₁ ≠ C₂ ∧ ∃ e ∈ G.edgeFinset ∩ S, ∃ u w : V,
          e = s(u, w) ∧ delG.connectedComponentMk u = C₁ ∧ delG.connectedComponentMk w = C₂
        symm := ⟨fun _ _ h => by
          rcases h with ⟨hne, e, he, u, w, heq, hu, hw⟩
          exact ⟨hne.symm, e, he, w, u, heq.trans Sym2.eq_swap, hw, hu⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    have hGq_conn : Gq.Connected := by
      have : Nonempty V := hconn.nonempty
      have : Nonempty delG.ConnectedComponent :=
        ⟨delG.connectedComponentMk (Classical.arbitrary V)⟩
      refine SimpleGraph.Connected.mk fun C₁ C₂ => ?_
      obtain ⟨v₁, hv₁⟩ := Quot.exists_rep C₁
      obtain ⟨v₂, hv₂⟩ := Quot.exists_rep C₂
      obtain ⟨p⟩ := hconn v₁ v₂
      have hwalk : ∀ {a b : V} (pw : G.Walk a b),
          Gq.Reachable (delG.connectedComponentMk a) (delG.connectedComponentMk b) := by
        intro a b pw
        induction pw with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons x y z hadj q ih =>
          by_cases hsame : delG.connectedComponentMk x = delG.connectedComponentMk y
          · rw [hsame]
            exact ih
          · have hS : s(x, y) ∈ S := by
              by_contra hnot
              exact hsame (SimpleGraph.ConnectedComponent.eq.mpr
                (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.2 ⟨hadj, hnot⟩)))
            have hadjq : Gq.Adj (delG.connectedComponentMk x) (delG.connectedComponentMk y) :=
              ⟨hsame, s(x, y), Finset.mem_inter.2 ⟨(SimpleGraph.mem_edgeFinset).2 hadj, hS⟩,
                x, y, rfl, rfl, rfl⟩
            exact (SimpleGraph.Adj.reachable hadjq).trans ih
      change Gq.Reachable C₁ C₂
      rw [← hv₁, ← hv₂]
      exact hwalk p
    let Crosses (qC : Sym2 delG.ConnectedComponent) (e : Sym2 V) : Prop :=
      e ∈ G.edgeFinset ∩ S ∧ ∃ u w : V, e = s(u, w) ∧
        s(delG.connectedComponentMk u, delG.connectedComponentMk w) = qC
    have hex_cross (qC : Sym2 delG.ConnectedComponent)
        (hqC : qC ∈ Gq.edgeFinset) : ∃ e : Sym2 V, Crosses qC e := by
      rw [SimpleGraph.mem_edgeFinset] at hqC
      induction qC using Sym2.ind with
      | h C₁ C₂ =>
        rcases hqC with ⟨_, e, he, u, w, heq, hu, hw⟩
        exact ⟨e, he, u, w, heq, by rw [hu, hw]⟩
    have : Nonempty V := hconn.nonempty
    let repEdge (qC : Sym2 delG.ConnectedComponent) : Sym2 V :=
      if h : qC ∈ Gq.edgeFinset then Classical.choose (hex_cross qC h)
      else s(Classical.arbitrary V, Classical.arbitrary V)
    have hrep_spec {qC} (hqC : qC ∈ Gq.edgeFinset) : Crosses qC (repEdge qC) := by
      dsimp only [repEdge]
      simp only [hqC, ↓reduceDIte]
      exact Classical.choose_spec (hex_cross qC hqC)
    have hrep_inj : Set.InjOn repEdge Gq.edgeFinset := by
      intro q₁ hq₁ q₂ hq₂ heq
      obtain ⟨_, u₁, w₁, h1, hq1⟩ := hrep_spec hq₁
      obtain ⟨_, u₂, w₂, h2, hq2⟩ := hrep_spec hq₂
      have hsame := h1.symm.trans (heq.trans h2)
      rcases Sym2.eq_iff.mp hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hq1.symm.trans hq2
      · exact hq1.symm.trans (Sym2.eq_swap.trans hq2)
    let χ_q (C : delG.ConnectedComponent) : Bool :=
      if C = C₀ then ∑ C' ∈ Finset.univ.erase C₀, ∑ v ∈ C'.supp.toFinset, χ v
      else ∑ v ∈ C.supp.toFinset, χ v
    have hχ_q_even : (∑ C : delG.ConnectedComponent, χ_q C) = false := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C₀)]
      have hrest : (∑ C ∈ Finset.univ.erase C₀, χ_q C) =
          ∑ C ∈ Finset.univ.erase C₀, ∑ v ∈ C.supp.toFinset, χ v := by
        refine Finset.sum_congr rfl fun C hC => ?_
        simp [χ_q, (Finset.mem_erase.1 hC).1]
      simp only [χ_q, ↓reduceIte, hrest, BooleanRing.add_self, Bool.zero_eq_false]
    obtain ⟨yq, hyq⟩ := (tseitinSatisfiable_iff_sum_eq_false Gq hGq_conn χ_q).mpr hχ_q_even
    let α (e : Sym2 V) : Bool :=
      if h : ∃ qC ∈ Gq.edgeFinset, repEdge qC = e then yq h.choose else false
    have hα_rep {qC} (hqC : qC ∈ Gq.edgeFinset) : α (repEdge qC) = yq qC := by
      have hex : ∃ qC' ∈ Gq.edgeFinset, repEdge qC' = repEdge qC := ⟨qC, hqC, rfl⟩
      simp only [α, hex, ↓reduceDIte]
      have hspec := Classical.choose_spec hex
      have hsame : hex.choose = qC := hrep_inj hspec.1 hqC hspec.2
      rw [hsame]
    have hα_boundary (C : delG.ConnectedComponent) :
        (∑ e ∈ cutEdges G C.supp.toFinset, α e) = tseitinVertexSum Gq yq C := by
      unfold tseitinVertexSum
      let Qedges := Gq.edgeFinset.filter (C ∈ ·)
      have hsub_img : Qedges.image repEdge ⊆ cutEdges G C.supp.toFinset := by
        intro e he
        rw [Finset.mem_image] at he
        rcases he with ⟨qC, hqC, rfl⟩
        rw [Finset.mem_filter] at hqC
        obtain ⟨heS, u, w, huw, hmk⟩ := hrep_spec hqC.1
        have heG : repEdge qC ∈ G.edgeFinset := (Finset.mem_inter.1 heS).1
        have hnd : ¬ qC.IsDiag := Gq.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hqC.1)
        induction qC using Sym2.ind with
        | h C₁ C₂ =>
          have hCne : C₁ ≠ C₂ := hnd
          have hCmem : C = C₁ ∨ C = C₂ := by simpa [Sym2.mem_iff] using hqC.2
          rcases Sym2.eq_iff.mp hmk with ⟨hu1, hw2⟩ | ⟨hu2, hw1⟩
          · rcases hCmem with hC1 | hC2
            · exact mem_cutEdges_iff.mpr ⟨heG, u, w, huw,
                (mem_supp_toFinset_iff S C u).2 (hu1.trans hC1.symm),
                fun hh => hCne
                  (hC1.symm.trans (((mem_supp_toFinset_iff S C w).1 hh).symm.trans hw2))⟩
            · exact mem_cutEdges_iff.mpr ⟨heG, w, u, huw.trans Sym2.eq_swap,
                (mem_supp_toFinset_iff S C w).2 (hw2.trans hC2.symm),
                fun hh => hCne (hu1.symm.trans (((mem_supp_toFinset_iff S C u).1 hh).trans hC2))⟩
          · rcases hCmem with hC1 | hC2
            · exact mem_cutEdges_iff.mpr ⟨heG, w, u, huw.trans Sym2.eq_swap,
                (mem_supp_toFinset_iff S C w).2 (hw1.trans hC1.symm),
                fun hh => hCne
                  (hC1.symm.trans (((mem_supp_toFinset_iff S C u).1 hh).symm.trans hu2))⟩
            · exact mem_cutEdges_iff.mpr ⟨heG, u, w, huw,
                (mem_supp_toFinset_iff S C u).2 (hu2.trans hC2.symm),
                fun hh => hCne
                  (hw1.symm.trans (((mem_supp_toFinset_iff S C w).1 hh).trans hC2))⟩
      rw [← Finset.sum_subset hsub_img fun e he hnot => ?_]
      · rw [Finset.sum_image fun q₁ hq₁ q₂ hq₂ h =>
          hrep_inj (Finset.mem_filter.1 hq₁).1 (Finset.mem_filter.1 hq₂).1 h]
        rw [← Finset.sum_filter]
        refine Finset.sum_congr rfl fun qC hqC => hα_rep (Finset.mem_filter.1 hqC).1
      · by_cases hex : ∃ qC ∈ Gq.edgeFinset, repEdge qC = e
        · exfalso
          apply hnot
          refine Finset.mem_image.2 ⟨hex.choose,
            Finset.mem_filter.2 ⟨(Classical.choose_spec hex).1, ?_⟩,
            (Classical.choose_spec hex).2⟩
          obtain ⟨_, u, w, huw, hmk⟩ := hrep_spec (Classical.choose_spec hex).1
          rw [(Classical.choose_spec hex).2] at huw
          rw [mem_cutEdges_iff] at he
          rcases he with ⟨_, a, b, hab, ha, _⟩
          rw [mem_supp_toFinset_iff] at ha
          have hpair : s(a, b) = s(u, w) := hab.symm.trans huw
          rw [show hex.choose = s(delG.connectedComponentMk u,
            delG.connectedComponentMk w) from hmk.symm]
          rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ha ▸ Sym2.mem_mk_left _ _
          · exact ha ▸ Sym2.mem_mk_right _ _
        · simp only [α, hex, ↓reduceDIte]
          rfl
    have hcomp_sum_cut (C : delG.ConnectedComponent) :
        (∑ v ∈ C.supp.toFinset, ∑ e ∈ G.edgeFinset ∩ S, if v ∈ e then α e else (0 : Bool)) =
        ∑ e ∈ cutEdges G C.supp.toFinset, α e := by
      rw [Finset.sum_comm]
      have heq1 : (∑ e ∈ G.edgeFinset ∩ S, ∑ v ∈ C.supp.toFinset,
            if v ∈ e then α e else (0 : Bool)) =
          ∑ e ∈ (G.edgeFinset ∩ S).filter (fun e =>
            (C.supp.toFinset.filter (· ∈ e)).card = 1), α e := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e he => ?_
        exact sum_filter_mem_sym2 (G.not_isDiag_of_mem_edgeSet
          (SimpleGraph.mem_edgeFinset.mp (Finset.mem_inter.1 he).1)) (α e)
      rw [heq1]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨⟨heG, _⟩, hc⟩
        exact Finset.mem_filter.2 ⟨heG, hc⟩
      · intro hc
        have hsub := cutEdges_supp_subset S C hc
        rw [cutEdges, Finset.mem_filter] at hc
        exact ⟨⟨hc.1, hsub⟩, hc.2⟩
    refine ⟨α, fun Q hQ => ?_⟩
    have hnot_sub : ¬ C₀.supp.toFinset ⊆ Q := fun h =>
      Nat.not_lt.mpr ((Finset.card_le_card h).trans hQ) hC₀
    obtain ⟨u₀, hu₀C, hu₀Q⟩ := Finset.not_subset.mp hnot_sub
    have hmk_u₀ : delG.connectedComponentMk u₀ = C₀ := (mem_supp_toFinset_iff S C₀ u₀).1 hu₀C
    let compSub (C : delG.ConnectedComponent) := {v : V // delG.connectedComponentMk v = C}
    let GC (C : delG.ConnectedComponent) : SimpleGraph (compSub C) :=
      delG.induce {v : V | delG.connectedComponentMk v = C}
    have hGC_conn (C : delG.ConnectedComponent) : (GC C).Connected := by
      have : Nonempty (compSub C) :=
        let ⟨v, hv⟩ := Quot.exists_rep C
        ⟨⟨v, hv⟩⟩
      refine SimpleGraph.Connected.mk fun a b => ?_
      have hreach : delG.Reachable a.1 b.1 :=
        SimpleGraph.ConnectedComponent.eq.mp (a.2.trans b.2.symm)
      obtain ⟨p⟩ := hreach
      have hp_stay : ∀ {x y : V} (pw : delG.Walk x y),
          (hx : delG.connectedComponentMk x = C) →
          (hy : delG.connectedComponentMk y = C) →
          (GC C).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
        intro x y pw hx hy
        induction pw with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons x y z hadj q ih =>
          have hxy : delG.connectedComponentMk x = delG.connectedComponentMk y :=
            SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
          have hyC : delG.connectedComponentMk y = C := hxy.symm.trans hx
          exact SimpleGraph.Reachable.trans
            (SimpleGraph.Adj.reachable (show (GC C).Adj ⟨x, hx⟩ ⟨y, hyC⟩ from hadj))
            (ih hyC hy)
      exact hp_stay p a.2 b.2
    let χBase (v : V) : Bool := χ v + ∑ e ∈ G.edgeFinset ∩ S, if v ∈ e then α e else (0 : Bool)
    have hβ_exists (C : delG.ConnectedComponent) :
        ∃ βC : Sym2 (compSub C) → Bool,
          TseitinSatisfies (GC C) (fun v => χBase v.1) βC
            (if h : C = C₀ then Finset.univ.erase ⟨u₀, h ▸ hmk_u₀⟩ else Finset.univ) := by
      by_cases hC : C = C₀
      · subst C
        simp only [↓reduceDIte]
        exact tseitinSatisfies_of_ne_univ (GC C₀) (hGC_conn C₀) (fun v => χBase v.1)
          (by
            intro heq
            have hu : (⟨u₀, hmk_u₀⟩ : compSub C₀) ∈ Finset.univ.erase ⟨u₀, hmk_u₀⟩ := by
              rw [heq]; exact Finset.mem_univ _
            exact (Finset.mem_erase.1 hu).1 rfl)
      · simp only [hC, ↓reduceDIte]
        refine (tseitinSatisfiable_iff_sum_eq_false (GC C) (hGC_conn C) fun v => χBase v.1).2 ?_
        have hmap_base : (∑ v : compSub C, χBase v.1) = ∑ v ∈ C.supp.toFinset, χBase v := by
          refine Finset.sum_bij (fun v _ => v.1) ?_
            (fun _ _ _ _ h => Subtype.ext h) ?_ (fun _ _ => rfl)
          · intro v _; exact (mem_supp_toFinset_iff S C v.1).2 v.2
          · intro v hv; exact ⟨⟨v, (mem_supp_toFinset_iff S C v).1 hv⟩, Finset.mem_univ _, rfl⟩
        rw [hmap_base]
        have hsum_split : (∑ v ∈ C.supp.toFinset, χBase v) =
            (∑ v ∈ C.supp.toFinset, χ v) +
              ∑ v ∈ C.supp.toFinset, ∑ e ∈ G.edgeFinset ∩ S, if v ∈ e then α e else (0 : Bool) :=
          Finset.sum_add_distrib
        rw [hsum_split, hcomp_sum_cut C, hα_boundary C, hyq C (Finset.mem_univ C)]
        simp [χ_q, hC, BooleanRing.add_self, Bool.zero_eq_false]
    choose βC hβC using hβ_exists
    let rawβ (a b : V) : Bool :=
      if h : delG.connectedComponentMk a = delG.connectedComponentMk b then
        βC (delG.connectedComponentMk a) s(⟨a, rfl⟩, ⟨b, h.symm⟩)
      else false
    have hrawβ_symm : ∀ a b : V, rawβ a b = rawβ b a := by
      intro a b
      have hsymm_eq : ∀ {C₁ C₂ : delG.ConnectedComponent}
          (h₁ : C₁ = C₂) (ha : delG.connectedComponentMk a = C₁)
          (hb : delG.connectedComponentMk b = C₂),
          βC C₁ s(⟨a, ha⟩, ⟨b, hb.trans h₁.symm⟩) = βC C₂ s(⟨b, hb⟩, ⟨a, ha.trans h₁⟩) := by
        intro C₁ C₂ h₁ ha hb
        subst h₁
        exact congrArg (βC C₁) Sym2.eq_swap
      dsimp only [rawβ]
      by_cases h₁ : delG.connectedComponentMk a = delG.connectedComponentMk b
      · have h₂ := h₁.symm
        rw [dite_eq_left h₁, dite_eq_left h₂]
        exact hsymm_eq h₁ rfl rfl
      · have h₂ : delG.connectedComponentMk b ≠ delG.connectedComponentMk a := fun hh => h₁ hh.symm
        rw [dite_eq_right h₁, dite_eq_right h₂]
    let β : Sym2 V → Bool := Sym2.lift ⟨rawβ, hrawβ_symm⟩
    refine ⟨β, fun v hvQ => ?_⟩
    let C := delG.connectedComponentMk v
    let y := fun e => if e ∈ S then α e else β e
    have hpart_edges : tseitinVertexSum G y v =
        (∑ e ∈ G.edgeFinset.filter (· ∈ S), if v ∈ e then α e else (0 : Bool)) +
          ∑ e ∈ G.edgeFinset.filter (· ∉ S), if v ∈ e then β e else (0 : Bool) := by
      unfold tseitinVertexSum
      exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset (· ∈ S)
        (fun e => if v ∈ e then y e else (0 : Bool))).symm.trans (by
        congr 1
        · refine Finset.sum_congr rfl fun e he => ?_
          simp [y, (Finset.mem_filter.1 he).2]
        · refine Finset.sum_congr rfl fun e he => ?_
          simp [y, (Finset.mem_filter.1 he).2])
    have hlocal_match : (∑ e ∈ G.edgeFinset.filter (· ∉ S), if v ∈ e then β e else (0 : Bool)) =
        tseitinVertexSum (GC C) (βC C) ⟨v, rfl⟩ := by
      rw [tseitinVertexSum_eq_sum_neighborFinset]
      have hsum_G_diff : (∑ e ∈ G.edgeFinset.filter (· ∉ S), if v ∈ e then β e else (0 : Bool)) =
          ∑ w ∈ delG.neighborFinset v, β s(v, w) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun e he => Sym2.Mem.other (Finset.mem_filter.1 he).2) ?_ ?_ ?_ ?_
        · intro e he
          rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
          rw [SimpleGraph.mem_neighborFinset]
          have hmem : s(v, Sym2.Mem.other he.2) ∈ G.edgeSet := by
            rw [Sym2.other_spec he.2]
            exact he.1.1
          rw [SimpleGraph.mem_edgeSet] at hmem
          refine SimpleGraph.deleteEdges_adj.2 ⟨hmem, ?_⟩
          rw [Sym2.other_spec he.2]
          exact he.1.2
        · intro e₁ he₁ e₂ he₂ h
          rw [Finset.mem_filter] at he₁ he₂
          calc e₁ = s(v, Sym2.Mem.other he₁.2) := (Sym2.other_spec he₁.2).symm
            _ = s(v, Sym2.Mem.other he₂.2) := by rw [h]
            _ = e₂ := Sym2.other_spec he₂.2
        · intro w hw
          rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hw
          have hmem : s(v, w) ∈ (G.edgeFinset.filter (· ∉ S)).filter (v ∈ ·) :=
            Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨(SimpleGraph.mem_edgeFinset).2 hw.1, hw.2⟩,
              by simp⟩
          refine ⟨s(v, w), hmem, ?_⟩
          have hspec : s(v, Sym2.Mem.other (Finset.mem_filter.1 hmem).2) = s(v, w) :=
            Sym2.other_spec (Finset.mem_filter.1 hmem).2
          rcases Sym2.eq_iff.mp hspec with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h (G.ne_of_adj hw.1)
        · intro e he
          rw [Sym2.other_spec (Finset.mem_filter.1 he).2]
      rw [hsum_G_diff]
      refine Finset.sum_bij
        (fun w hw => ⟨w, (SimpleGraph.ConnectedComponent.eq.mpr
          (by rw [SimpleGraph.mem_neighborFinset] at hw; exact hw.reachable)).symm⟩)
        ?_ (fun _ _ _ _ h => Subtype.ext_iff.mp h) ?_ ?_
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw ⊢
        exact hw
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        exact ⟨w.1, by rw [SimpleGraph.mem_neighborFinset]; exact hw, Subtype.eta _ _⟩
      · intro w hw
        have hmkw : delG.connectedComponentMk v = delG.connectedComponentMk w :=
          SimpleGraph.ConnectedComponent.eq.mpr
            (by rw [SimpleGraph.mem_neighborFinset] at hw; exact hw.reachable)
        dsimp only [β]
        rw [Sym2.lift_mk]
        simp only [rawβ, hmkw, ↓reduceDIte]
        rfl
    have hvu₀ : v ≠ u₀ := fun h => hu₀Q (h ▸ hvQ)
    have hloc_eval : tseitinVertexSum (GC C) (βC C) ⟨v, rfl⟩ = χBase v := by
      by_cases hC : C = C₀
      · have hsat := hβC C ⟨v, rfl⟩
        simp only [hC, ↓reduceDIte] at hsat
        exact hsat (Finset.mem_erase.2 ⟨fun h => hvu₀ (congrArg Subtype.val h), Finset.mem_univ _⟩)
      · have hsat := hβC C ⟨v, rfl⟩
        simp only [hC, ↓reduceDIte] at hsat
        exact hsat (Finset.mem_univ _)
    have hpart_edges' : (∑ e ∈ G.edgeFinset ∩ S, if v ∈ e then α e else (0 : Bool)) =
        ∑ e ∈ G.edgeFinset.filter (· ∈ S), if v ∈ e then α e else (0 : Bool) := by
      rw [← Finset.filter_mem_eq_inter]
    rw [hpart_edges, ← hpart_edges', hlocal_match, hloc_eval]
    dsimp only [χBase]
    rw [add_comm (χ v) _, ← add_assoc, BooleanRing.add_self, zero_add]

/-! ### Giant component in expanders after sublinear edge deletion -/

/-- A graph `G` has edge expansion `h` if every vertex subset `U` with `2 * |U| ≤ |V|` has
at least `h * |U|` edges in `∂_G(U)`. -/
@[expose] def IsEdgeExpander (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℕ) : Prop :=
  ∀ U : Finset V, 2 * U.card ≤ Fintype.card V → h * U.card ≤ (cutEdges G U).card

/-- **Expander giant-component bound**: in an `h`-edge-expander (`h > 0`), deleting a set `S`
with `2 * |S| < h * |V|` leaves a connected component of `G.deleteEdges S` of size at least
`|V| - |S| / h`. -/
theorem exists_large_component_of_edgeExpander (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hh : 0 < h) (hexp : IsEdgeExpander G h) (S : Finset (Sym2 V))
    (hS : 2 * S.card < h * Fintype.card V) :
    ∃ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
      Fintype.card V - S.card / h ≤ C.supp.ncard := by
  classical
  have : Fintype (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent := Fintype.ofFinite _
  have hex_half : ∃ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
      Fintype.card V < 2 * C.supp.toFinset.card := by
    by_contra hall
    push Not at hall
    have hle_sum : ∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        h * C.supp.toFinset.card ≤
        ∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
          (cutEdges G C.supp.toFinset).card :=
      Finset.sum_le_sum fun C _ => hexp C.supp.toFinset (hall C)
    have hcard_sum : ∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        C.supp.toFinset.card = Fintype.card V := by
      have := Finset.sum_card_fiberwise_eq_card_filter
        (s := Finset.univ) (t := Finset.univ)
        (g := (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk)
      have hfilt (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) :
          C.supp.toFinset = Finset.univ.filter
            (fun v => (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk v = C) := by
        ext v; simp
      simp_rw [hfilt]
      simpa using this
    have hlhs : ∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        h * C.supp.toFinset.card = h * Fintype.card V := by
      rw [← Finset.mul_sum, hcard_sum]
    have hrhs : (∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
        (cutEdges G C.supp.toFinset).card) ≤ 2 * S.card := by
      have hcard_eq (C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent) :
          (cutEdges G C.supp.toFinset).card =
          ∑ e ∈ S, if e ∈ cutEdges G C.supp.toFinset then 1 else 0 := by
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext e
        rw [Finset.mem_filter]
        exact ⟨fun h => ⟨cutEdges_supp_subset S C h, h⟩, fun h => h.2⟩
      simp_rw [hcard_eq]
      rw [Finset.sum_comm]
      calc ∑ e ∈ S, ∑ C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent,
              (if e ∈ cutEdges G C.supp.toFinset then 1 else 0)
          ≤ ∑ _e ∈ S, 2 := by
            refine Finset.sum_le_sum fun e _ => ?_
            rw [Finset.sum_boole, Nat.cast_id]
            by_cases heG : e ∈ G.edgeFinset
            · induction e using Sym2.ind with
              | h u w =>
                let Cu := (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk u
                let Cw := (G.deleteEdges (S : Set (Sym2 V))).connectedComponentMk w
                have hsub : Finset.univ.filter
                    (fun C => s(u, w) ∈ cutEdges G C.supp.toFinset) ⊆ {Cu, Cw} := by
                  intro C hC
                  rw [Finset.mem_filter, mem_cutEdges_iff] at hC
                  rcases hC.2 with ⟨_, a, b, heq, ha, _⟩
                  rw [mem_supp_toFinset_iff] at ha
                  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Finset.mem_insert.2 (Or.inl ha.symm)
                  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 ha.symm))
                exact (Finset.card_le_card hsub).trans Finset.card_le_two
            · have heq : Finset.univ.filter
                  (fun C : (G.deleteEdges (S : Set (Sym2 V))).ConnectedComponent =>
                    e ∈ cutEdges G C.supp.toFinset) = ∅ := by
                ext C
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                  iff_false]
                intro hc
                exact heG (mem_cutEdges_iff.mp hc).1
              rw [heq, Finset.card_empty]
              omega
        _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    omega
  obtain ⟨C, hC⟩ := hex_half
  refine ⟨C, ?_⟩
  rw [Set.ncard_eq_toFinset_card' C.supp]
  let U := Finset.univ \ C.supp.toFinset
  have hU_card : U.card + C.supp.toFinset.card = Fintype.card V :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hU_half : 2 * U.card ≤ Fintype.card V := by omega
  have hcut_eq : cutEdges G U = cutEdges G C.supp.toFinset := by
    ext e
    simp only [mem_cutEdges_iff, U, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, u, w, heq, hu, hw⟩
      exact ⟨he, w, u, heq.trans Sym2.eq_swap, not_not.mp hw, hu⟩
    · rintro ⟨he, u, w, heq, hu, hw⟩
      exact ⟨he, w, u, heq.trans Sym2.eq_swap, hw, not_not.mpr hu⟩
  have hexpU : h * U.card ≤ (cutEdges G U).card := hexp U hU_half
  have hcutS : (cutEdges G U).card ≤ S.card := by
    rw [hcut_eq]
    exact Finset.card_le_card (cutEdges_supp_subset S C)
  have hU_div : U.card ≤ S.card / h :=
    (Nat.le_div_iff_mul_le hh).mpr (by rw [Nat.mul_comm]; exact hexpU.trans hcutS)
  omega

end Tseitin

/-! ### Shared-ancestor cheating and boundary separation in local-cone segregator protocols -/

section SegregatorCounterexample

/-- A finite local-cone checking protocol over global vertex assignments `V → σ` and challenge
set `Q`, where each constraint `ValidAt q` depends only on the vertices inside `cone q`. -/
structure LocalConeProtocol (σ V Q : Type*) [Fintype V] [DecidableEq V] where
  /-- Dependency cone for each universal challenge `q`. -/
  cone : Q → Finset V
  /-- Local validity check for challenge `q`. -/
  ValidAt : Q → (V → σ) → Prop
  /-- `ValidAt q` depends solely on coordinates inside `cone q`. -/
  valid_local : ∀ q y₁ y₂, (∀ v ∈ cone q, y₁ v = y₂ v) → (ValidAt q y₁ ↔ ValidAt q y₂)

/-- A vertex commitment set `J` is a **cone separator** when no uncommitted vertex `v ∉ J` lies
in two distinct cones. -/
@[expose] def LocalConeProtocol.IsSeparator {σ V Q : Type*} [Fintype V] [DecidableEq V]
    (P : LocalConeProtocol σ V Q) (J : Finset V) : Prop :=
  ∀ v ∉ J, ∀ q₁ q₂, v ∈ P.cone q₁ → v ∈ P.cone q₂ → q₁ = q₂

/-- The 2-block local-cone extension protocol parameterized by committed boundary `J`: existentially
fix `assignJ` on `J`, then for every challenge `q`, existentially extend `assignJ` inside
`cone q` to satisfy `ValidAt q`. -/
@[expose] def LocalConeProtocol.Accepts {σ V Q : Type*} [Fintype V] [DecidableEq V]
    (P : LocalConeProtocol σ V Q) (J : Finset V) : Prop :=
  ∃ assignJ : {v // v ∈ J} → σ, ∀ q : Q, ∃ y : V → σ,
    (∀ v (hv : v ∈ J ∩ P.cone q), y v = assignJ ⟨v, (Finset.mem_inter.1 hv).1⟩) ∧ P.ValidAt q y

/-- **Boundary-separator soundness**: whenever `J` separates all shared vertices between cones,
local acceptance implies a single global assignment satisfying all constraints simultaneously. -/
theorem localCone_sound_of_separator {σ V Q : Type*} [Fintype V] [DecidableEq V]
    [Nonempty σ] (P : LocalConeProtocol σ V Q) {J : Finset V}
    (hsep : P.IsSeparator J) (hacc : P.Accepts J) :
    ∃ y : V → σ, ∀ q : Q, P.ValidAt q y := by
  classical
  obtain ⟨assignJ, hExt⟩ := hacc
  choose ext hext using hExt
  let y (v : V) : σ :=
    if hv : v ∈ J then assignJ ⟨v, hv⟩
    else if hq : ∃ q, v ∈ P.cone q then ext hq.choose v
    else Classical.arbitrary σ
  refine ⟨y, fun q => ?_⟩
  refine (P.valid_local q y (ext q) fun v hv => ?_).2 (hext q).2
  dsimp only [y]
  by_cases hvJ : v ∈ J
  · rw [dite_eq_left hvJ]
    exact ((hext q).1 v (Finset.mem_inter.2 ⟨hvJ, hv⟩)).symm
  · rw [dite_eq_right hvJ]
    have hqex : ∃ q', v ∈ P.cone q' := ⟨q, hv⟩
    rw [dite_eq_left hqex]
    have heq : hqex.choose = q := hsep v hvJ hqex.choose q hqex.choose_spec hv
    rw [heq]

/-- Explicit 3-vertex fork DAG `{0, 1, 2}` where ancestor `2` is shared by leaf cones
`cone 0 = {0, 2}` (checking `y 0 = true ∧ y 0 = y 2`) and `cone 1 = {1, 2}`
(checking `y 1 = true ∧ y 1 = !(y 2)`). -/
@[expose] def forkConeProtocol : LocalConeProtocol Bool (Fin 3) (Fin 2) where
  cone q := if q = 0 then {0, 2} else {1, 2}
  ValidAt q y := if q = 0 then (y 0 = true ∧ y 0 = y 2) else (y 1 = true ∧ y 1 = !(y 2))
  valid_local q y₁ y₂ hagree := by
    fin_cases q
    · simp only [Fin.isValue]
      have h0 := hagree 0 (by simp)
      have h2 := hagree 2 (by simp)
      simp [h0, h2]
    · simp only [Fin.isValue]
      have h1 := hagree 1 (by simp)
      have h2 := hagree 2 (by simp)
      simp [h1, h2]

/-- **Shared-ancestor counterexample for segregator protocols**:
1. The 3-vertex fork DAG has NO global satisfying assignment;
2. Leaving the shared ancestor `2` outside the commitment (`J = ∅`) allows local extensions to
   cheatingly accept;
3. Pinning `{2} ⊆ J` satisfies `IsSeparator {2}` and restores soundness (`¬ Accepts {2}`). -/
theorem segregator_shared_ancestor_unsound :
    (¬ ∃ y : Fin 3 → Bool, ∀ q : Fin 2, forkConeProtocol.ValidAt q y) ∧
    forkConeProtocol.Accepts ∅ ∧
    (forkConeProtocol.IsSeparator {2} ∧ ¬ forkConeProtocol.Accepts {2}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have h0 := hy 0
    have h1 := hy 1
    dsimp only [forkConeProtocol] at h0 h1
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] at h0 h1
    rw [h0.1] at h0
    rw [h1.1] at h1
    cases h : y 2 <;> simp [h] at h0 h1
  · refine ⟨fun ⟨_, h⟩ => False.elim (by simp at h), fun q => ?_⟩
    fin_cases q
    · exact ⟨fun _ => true, fun _ hv => by simp at hv, by simp [forkConeProtocol]⟩
    · exact ⟨fun v => if v = 1 then true else false, fun _ hv => by simp at hv,
        by simp [forkConeProtocol]⟩
  · intro v hv q₁ q₂ h1 h2
    fin_cases v <;> fin_cases q₁ <;> fin_cases q₂ <;> simp_all [forkConeProtocol]
  · intro hacc
    obtain ⟨y, hy⟩ := localCone_sound_of_separator forkConeProtocol
      (fun v hv q₁ q₂ h1 h2 => by
        fin_cases v <;> fin_cases q₁ <;> fin_cases q₂ <;> simp_all [forkConeProtocol]) hacc
    have h0 : y 0 = true ∧ y 0 = y 2 := by simpa [forkConeProtocol] using hy 0
    have h1 : y 1 = true ∧ y 1 = !(y 2) := by simpa [forkConeProtocol] using hy 1
    cases h2 : y 2 <;> simp_all

end SegregatorCounterexample

end Cslib.Complexity
