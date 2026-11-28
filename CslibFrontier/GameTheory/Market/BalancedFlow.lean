/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.EisenbergGale
public import CslibFrontier.Algorithms.Lean.MaxFlow.RealFlow
public import Cslib.Algorithms.Lean.Query.FreeM
import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equality networks, tight sets, balanced flows, and rational equilibria in linear Fisher markets

This module formalizes the combinatorial network-flow infrastructure of the Devanur–Papadimitriou–
Saberi–Vazirani (DPSV) algorithm for linear Fisher markets ([Vazirani2007], Chapter 5):

* **Equality subgraph and money-flow network `N(p)`** ([Vazirani2007], Section 5.3, pp. 108–109):
  `IsEqualityEdge`, `FlowVertex`, `equalityNetwork` (instantiating
  `Cslib.Algorithms.Lean.MaxFlow.RealFlow` with a finite non-binding big-`M` capacity on equality
  arcs), and **Lemma 5.2** (`exists_isEquilibrium_iff_minCut`, `isEquilibrium_of_isMaxRealFlow`).
* **Tight sets and the Invariant** ([Vazirani2007], Section 5.6, p. 111; Section 5.8, p. 115):
  `buyerNeighborhood`, `goodValue`, `budgetSum`, `SatisfiesInvariant`, `IsTightSet`,
  **Lemma 5.3** (`satisfiesInvariant_iff`), submodular closure of tight sets under union and
  intersection (`isTightSet_union_and_inter`), and the unique maximal tight set `maximalTightSet`.
* **Balanced flows** ([Vazirani2007], Section 5.7, pp. 111–113): `surplus`, `surplusSqNorm`,
  `IsBalancedFlow`, existence (`exists_isBalancedFlow`), max-flow property
  (`IsBalancedFlow.isMaxEqualityFlow`), **Lemma 5.4** (`surplus_eq_of_isBalancedFlow`: uniqueness
  of the balanced surplus vector), and **Theorem 5.5** (`isBalancedFlow_iff_satisfiesPropertyOne`:
  characterization via Property 1 in the residual graph `R(f) - {s, t}`).
* **Divide-and-conquer balanced-flow algorithm** ([Vazirani2007], Section 5.7.1, pp. 113–115):
  `MaxFlowQuery`, `IsValidMaxFlowOracle`, `canonicalMaxFlowOracle`, `balancedFlowProgram` in
  `Cslib.FreeM`, and **Lemmas 5.6–5.7 / Theorem 5.8** (`balancedFlowProgram_spec`: outputs a
  balanced max-flow in at most `Fintype.card G` max-flow oracle calls via batched level execution).
* **Finding tight sets** ([Vazirani2007], Section 5.9, pp. 117–118): `scaledSubnetwork`,
  `minTightRatio`, `tightSetAtMinRatio`, **Lemma 5.9**
  (`minCut_scaledSubnetwork_of_le_minTightRatio`, `not_minCut_and_subset_of_minTightRatio_lt`),
  **Lemma 5.10** (`ssubset_of_minCut_at_avgRatio`), and **Lemma 5.11** (`findTightSetProgram`,
  `findTightSetProgram_spec`: finds `(x*, S*)` in at most `A.card` max-flow oracle calls).
* **Rationality and polynomial bit-length bounds** ([Vazirani2007], Section 5.10, Lemma 5.12,
  pp. 118–119; Section 5.2, Theorem 5.1 part 4, pp. 107–108): **Lemma 5.12**
  (`exists_rat_price_of_isTightSet`: prices in any tight set `S` are rational with denominator at
  most `S.card * U ^ (S.card - 1) ≤ n * U ^ n`) and **Theorem 5.1 part 4**
  (`exists_rational_equilibrium_of_nat` for integer inputs and `exists_rational_equilibrium_of_rat`
  for general rational inputs: existence of rational equilibrium prices and allocations with
  explicit polynomial-bit numerator and denominator bounds).

The full DPSV phase loop, potential drop analysis, and polynomial-time termination theorem
([Vazirani2007], Sections 5.8 and 5.10, `Theorem 5.22`) remain open under `#7789`.

## References

* [Vazirani2007]
-/

public section

namespace Cslib.GameTheory.Market.LinearFisherMarket

open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut
open Cslib (FreeM)

universe u

/-! ### Bipartite flow-network vertices and generic `RealFlow` bridge -/

/-- Vertices of the bipartite money-flow network `N(p)` ([Vazirani2007], Section 5.3.1, p. 108):
source `source`, goods `good g`, buyers `buyer i`, and sink `sink`. -/
inductive FlowVertex (I G : Type*) where
  | source
  | good (g : G)
  | buyer (i : I)
  | sink
  deriving DecidableEq

private def flowVertexEquiv (I G : Type*) : FlowVertex I G ≃ (Unit ⊕ G) ⊕ (I ⊕ Unit) where
  toFun
    | .source => .inl (.inl ())
    | .good g => .inl (.inr g)
    | .buyer i => .inr (.inl i)
    | .sink => .inr (.inr ())
  invFun
    | .inl (.inl ()) => .source
    | .inl (.inr g) => .good g
    | .inr (.inl i) => .buyer i
    | .inr (.inr ()) => .sink
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with (⟨⟩ | g) | (i | ⟨⟩) <;> rfl

instance instFintypeFlowVertex {I G : Type*} [Fintype I] [Fintype G] :
    Fintype (FlowVertex I G) :=
  Fintype.ofEquiv ((Unit ⊕ G) ⊕ (I ⊕ Unit))
    { toFun
        | .inl (.inl ()) => .source
        | .inl (.inr g) => .good g
        | .inr (.inl i) => .buyer i
        | .inr (.inr ()) => .sink
      invFun
        | .source => .inl (.inl ())
        | .good g => .inl (.inr g)
        | .buyer i => .inr (.inl i)
        | .sink => .inr (.inr ())
      left_inv v := by rcases v with (⟨⟩ | g) | (i | ⟨⟩) <;> rfl
      right_inv v := by cases v <;> rfl }

/-- Summing a function over `FlowVertex I G` splits into `source`, goods, buyers, and `sink`. -/
private theorem sum_flowVertex {I G M : Type*} [Fintype I] [Fintype G] [AddCommMonoid M]
    (h : FlowVertex I G → M) :
    ∑ v : FlowVertex I G, h v =
      h .source + (∑ g : G, h (.good g)) + ((∑ i : I, h (.buyer i)) + h .sink) := by
  rw [← (flowVertexEquiv I G).symm.sum_comp]
  simp [flowVertexEquiv, Fintype.sum_sum_type]

section BipartiteNetwork

variable {I G : Type*}

/-- Non-binding finite surrogate for `+∞` on bipartite arcs of a subnetwork with good capacities `a`
on `A` and buyer capacities `b` on `B`. -/
private def bigM (A : Finset G) (B : Finset I) (a : G → ℝ) (b : I → ℝ) : ℝ :=
  (∑ g ∈ A, a g) + (∑ i ∈ B, b i) + 1

/-- Capacity matrix on `FlowVertex I G` for a bipartite subnetwork on active goods `A ⊆ G`, active
buyers `B ⊆ I`, source-to-good capacities `a`, buyer-to-sink capacities `b`, and bipartite edge
relation `E : G → I → Prop`. -/
private noncomputable def bipCap (A : Finset G) (B : Finset I)
    (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) :
    FlowVertex I G → FlowVertex I G → ℝ :=
  open scoped Classical in fun u v =>
    match u, v with
    | .source, .good g => if g ∈ A then a g else 0
    | .good g, .buyer i => if g ∈ A ∧ i ∈ B ∧ E g i then bigM A B a b else 0
    | .buyer i, .sink => if i ∈ B then b i else 0
    | _, _ => 0

private theorem bipCap_nonneg {A : Finset G} {B : Finset I} {a : G → ℝ} {b : I → ℝ}
    {E : G → I → Prop} (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i)
    (u v : FlowVertex I G) : 0 ≤ bipCap A B a b E u v := by
  have hM : 0 ≤ bigM A B a b := by
    unfold bigM
    linarith [Finset.sum_nonneg ha, Finset.sum_nonneg hb]
  cases u <;> cases v <;> simp only [bipCap] <;> try exact le_rfl
  · split_ifs with h
    · exact ha _ h
    · exact le_rfl
  · split_ifs with h
    · exact hM
    · exact le_rfl
  · split_ifs with h
    · exact hb _ h
    · exact le_rfl

/-- Active goods placed on the source side of cut `X`. -/
private def cutGoods [DecidableEq I] [DecidableEq G] (A : Finset G)
    (X : Finset (FlowVertex I G)) : Finset G :=
  A.filter fun g => .good g ∈ X

/-- Active buyers placed on the source side of cut `X`. -/
private def cutBuyers [DecidableEq I] [DecidableEq G] (B : Finset I)
    (X : Finset (FlowVertex I G)) : Finset I :=
  B.filter fun i => .buyer i ∈ X

/-- Build the `s`–`t` cut `{.source} ∪ A₁ ∪ B₁`. -/
private def mkCut [DecidableEq I] [DecidableEq G] (A₁ : Finset G) (B₁ : Finset I) :
    Finset (FlowVertex I G) :=
  insert .source (A₁.image .good ∪ B₁.image .buyer)

private theorem source_mem_mkCut [DecidableEq I] [DecidableEq G] (A₁ : Finset G) (B₁ : Finset I) :
    FlowVertex.source ∈ mkCut A₁ B₁ :=
  Finset.mem_insert_self _ _

private theorem sink_notMem_mkCut [DecidableEq I] [DecidableEq G] (A₁ : Finset G) (B₁ : Finset I) :
    FlowVertex.sink ∉ mkCut A₁ B₁ := by
  simp [mkCut]

private theorem good_mem_mkCut_iff [DecidableEq I] [DecidableEq G] (A₁ : Finset G) (B₁ : Finset I)
    (g : G) : FlowVertex.good g ∈ mkCut A₁ B₁ ↔ g ∈ A₁ := by
  simp [mkCut]

private theorem buyer_mem_mkCut_iff [DecidableEq I] [DecidableEq G] (A₁ : Finset G) (B₁ : Finset I)
    (i : I) : FlowVertex.buyer i ∈ mkCut A₁ B₁ ↔ i ∈ B₁ := by
  simp [mkCut]

/-- Bipartite neighborhood `Γ_B(S)` of `S` inside `B` under edge relation `E`. -/
private noncomputable def bipNbr (B : Finset I) (E : G → I → Prop) (S : Finset G) : Finset I :=
  open scoped Classical in B.filter fun i => ∃ g ∈ S, E g i

private theorem mem_bipNbr {B : Finset I} {E : G → I → Prop} {S : Finset G} {i : I} :
    i ∈ bipNbr B E S ↔ i ∈ B ∧ ∃ g ∈ S, E g i := by
  classical
  simp [bipNbr]

private theorem bipNbr_empty (B : Finset I) (E : G → I → Prop) : bipNbr B E ∅ = ∅ := by
  ext i; simp [mem_bipNbr]

private theorem bipNbr_union [DecidableEq I] [DecidableEq G] (B : Finset I) (E : G → I → Prop)
    (S₁ S₂ : Finset G) :
    bipNbr B E (S₁ ∪ S₂) = bipNbr B E S₁ ∪ bipNbr B E S₂ := by
  ext i
  simp only [mem_bipNbr, Finset.mem_union]
  constructor
  · rintro ⟨hiB, g, hg | hg, hE⟩
    · exact Or.inl ⟨hiB, g, hg, hE⟩
    · exact Or.inr ⟨hiB, g, hg, hE⟩
  · rintro (⟨hiB, g, hg, hE⟩ | ⟨hiB, g, hg, hE⟩)
    · exact ⟨hiB, g, Or.inl hg, hE⟩
    · exact ⟨hiB, g, Or.inr hg, hE⟩

private theorem bipNbr_inter_subset [DecidableEq I] [DecidableEq G] (B : Finset I)
    (E : G → I → Prop) (S₁ S₂ : Finset G) :
    bipNbr B E (S₁ ∩ S₂) ⊆ bipNbr B E S₁ ∩ bipNbr B E S₂ := by
  intro i hi
  rw [Finset.mem_inter, mem_bipNbr, mem_bipNbr]
  rw [mem_bipNbr] at hi
  obtain ⟨hiB, g, hg, hE⟩ := hi
  rw [Finset.mem_inter] at hg
  exact ⟨⟨hiB, g, hg.1, hE⟩, ⟨hiB, g, hg.2, hE⟩⟩

variable [Fintype I] [Fintype G]

/-- Exact formula for `cutWeight (bipCap A B a b E) X` for any `s`–`t` cut `X`. -/
private theorem cutWeight_bipCap [DecidableEq I] [DecidableEq G] {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop} {X : Finset (FlowVertex I G)}
    (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X) :
    cutWeight (bipCap A B a b E) X =
      (∑ g ∈ A \ cutGoods A X, a g) +
      (∑ g ∈ cutGoods A X, ∑ i ∈ B \ cutBuyers B X,
        open scoped Classical in if E g i then bigM A B a b else 0) +
      (∑ i ∈ cutBuyers B X, b i) := by
  classical
  have key : cutWeight (bipCap A B a b E) X =
      ∑ u : FlowVertex I G, ∑ v : FlowVertex I G,
        if u ∈ X ∧ v ∉ X then bipCap A B a b E u v else 0 := by
    unfold cutWeight
    calc
      ∑ u ∈ X, ∑ v ∈ Finset.univ \ X, bipCap A B a b E u v
        = ∑ u ∈ X, ∑ v : FlowVertex I G, if v ∉ X then bipCap A B a b E u v else 0 := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      _ = ∑ u : FlowVertex I G,
            if u ∈ X then ∑ v : FlowVertex I G,
              (if v ∉ X then bipCap A B a b E u v else 0) else 0 := by
            rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : u ∈ X
            · simp [hu]
            · simp [hu]
  rw [key, sum_flowVertex]
  have hsrc : ∑ v : FlowVertex I G,
      (if FlowVertex.source ∈ X ∧ v ∉ X then bipCap A B a b E .source v else 0) =
      ∑ g ∈ A \ cutGoods A X, a g := by
    rw [sum_flowVertex]
    simp only [bipCap, hs, true_and, ite_self, Finset.sum_const_zero, zero_add, add_zero]
    symm
    rw [← Finset.univ_inter (A \ cutGoods A X), ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Finset.mem_sdiff, cutGoods, Finset.mem_filter, not_and]
    by_cases hgA : g ∈ A <;> by_cases hgX : FlowVertex.good g ∈ X <;> simp [hgA, hgX]
  have hgoods : ∑ g : G, ∑ v : FlowVertex I G,
      (if FlowVertex.good g ∈ X ∧ v ∉ X then bipCap A B a b E (.good g) v else 0) =
      ∑ g ∈ cutGoods A X, ∑ i ∈ B \ cutBuyers B X,
        if E g i then bigM A B a b else 0 := by
    have hinner (g : G) : ∑ v : FlowVertex I G,
        (if FlowVertex.good g ∈ X ∧ v ∉ X then bipCap A B a b E (.good g) v else 0) =
        if g ∈ cutGoods A X then
          ∑ i ∈ B \ cutBuyers B X, if E g i then bigM A B a b else 0
        else 0 := by
      rw [sum_flowVertex]
      simp only [bipCap, ite_self, Finset.sum_const_zero, zero_add, add_zero]
      by_cases hg : g ∈ cutGoods A X
      · have hgA : g ∈ A := (Finset.mem_filter.1 hg).1
        have hgX : FlowVertex.good g ∈ X := (Finset.mem_filter.1 hg).2
        simp only [hg, ↓reduceIte, hgA, hgX, true_and]
        symm
        rw [← Finset.univ_inter (B \ cutBuyers B X), ← Finset.sum_ite_mem]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mem_sdiff, cutBuyers, Finset.mem_filter, not_and]
        by_cases hiB : i ∈ B <;> by_cases hiX : FlowVertex.buyer i ∈ X <;>
          by_cases hE : E g i <;> simp [hiB, hiX, hE]
      · simp only [hg, ↓reduceIte]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [cutGoods, Finset.mem_filter, not_and] at hg
        by_cases hgA : g ∈ A
        · simp [hg hgA]
        · simp [hgA]
    simp_rw [hinner, Finset.sum_ite_mem, Finset.univ_inter]
  have hbuyers : ∑ i : I, ∑ v : FlowVertex I G,
      (if FlowVertex.buyer i ∈ X ∧ v ∉ X then bipCap A B a b E (.buyer i) v else 0) =
      ∑ i ∈ cutBuyers B X, b i := by
    have hinner (i : I) : ∑ v : FlowVertex I G,
        (if FlowVertex.buyer i ∈ X ∧ v ∉ X then bipCap A B a b E (.buyer i) v else 0) =
        if i ∈ cutBuyers B X then b i else 0 := by
      rw [sum_flowVertex]
      simp only [bipCap, ht, not_false_eq_true, and_true, ite_self, Finset.sum_const_zero,
        zero_add, add_zero, cutBuyers, Finset.mem_filter]
      by_cases hiB : i ∈ B <;> by_cases hiX : FlowVertex.buyer i ∈ X <;> simp [hiB, hiX]
    simp_rw [hinner, Finset.sum_ite_mem, Finset.univ_inter]
  have hsink : ∑ v : FlowVertex I G,
      (if FlowVertex.sink ∈ X ∧ v ∉ X then bipCap A B a b E .sink v else 0) = 0 := by
    simp [ht]
  rw [hsrc, hgoods, hbuyers, hsink, add_zero]

private theorem cutWeight_bipCap_source [DecidableEq I] [DecidableEq G] (A : Finset G)
    (B : Finset I) (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) :
    cutWeight (bipCap A B a b E) ({.source} : Finset (FlowVertex I G)) = ∑ g ∈ A, a g := by
  rw [cutWeight_bipCap (Finset.mem_singleton_self _) (by simp)]
  have hg : cutGoods A ({.source} : Finset (FlowVertex I G)) = ∅ := by ext g; simp [cutGoods]
  have hb : cutBuyers B ({.source} : Finset (FlowVertex I G)) = ∅ := by ext i; simp [cutBuyers]
  simp [hg, hb]

private theorem cutWeight_bipCap_sink [DecidableEq I] [DecidableEq G] (A : Finset G) (B : Finset I)
    (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) :
    cutWeight (bipCap A B a b E) (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
      ∑ i ∈ B, b i := by
  rw [cutWeight_bipCap (by simp) (by simp)]
  have hg : cutGoods A (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) = A := by
    ext g; simp [cutGoods]
  have hb : cutBuyers B (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) = B := by
    ext i; simp [cutBuyers]
  simp [hg, hb]

private theorem cutWeight_bipCap_of_no_cross [DecidableEq I] [DecidableEq G]
    {A : Finset G} {B : Finset I} {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    {X : Finset (FlowVertex I G)} (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X)
    (hnc : ∀ g ∈ cutGoods A X, ∀ i ∈ B \ cutBuyers B X, ¬ E g i) :
    cutWeight (bipCap A B a b E) X =
      (∑ g ∈ A \ cutGoods A X, a g) + ∑ i ∈ cutBuyers B X, b i := by
  classical
  rw [cutWeight_bipCap hs ht]
  have hmid : (∑ g ∈ cutGoods A X, ∑ i ∈ B \ cutBuyers B X,
      if E g i then bigM A B a b else 0) = 0 :=
    Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun i hi => by simp [hnc g hg i hi]
  rw [hmid, add_zero]

/-- Any `s`–`t` cut `X` crossing an active bipartite arc `(g₀, i₀)` has weight strictly greater
than `∑ g ∈ A, a g` (since it pays the non-binding arc capacity `bigM A B a b`). -/
private theorem sum_lt_cutWeight_bipCap_of_cross [DecidableEq I] [DecidableEq G]
    {A : Finset G} {B : Finset I} {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i)
    {X : Finset (FlowVertex I G)} (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X)
    {g₀ : G} (hg₀ : g₀ ∈ cutGoods A X) {i₀ : I} (hi₀ : i₀ ∈ B \ cutBuyers B X) (hE : E g₀ i₀) :
    ∑ g ∈ A, a g < cutWeight (bipCap A B a b E) X := by
  classical
  have hM_nn : 0 ≤ bigM A B a b := by
    unfold bigM
    linarith [Finset.sum_nonneg ha, Finset.sum_nonneg hb]
  have hterm_nn (g : G) (i : I) : 0 ≤ if E g i then bigM A B a b else 0 := by
    split_ifs <;> linarith
  have hmid : bigM A B a b ≤ ∑ g ∈ cutGoods A X, ∑ i ∈ B \ cutBuyers B X,
      if E g i then bigM A B a b else 0 := by
    calc
      bigM A B a b = if E g₀ i₀ then bigM A B a b else 0 := by simp [hE]
      _ ≤ ∑ i ∈ B \ cutBuyers B X, if E g₀ i then bigM A B a b else 0 :=
          Finset.single_le_sum (f := fun i => if E g₀ i then bigM A B a b else 0)
            (fun i _ => hterm_nn g₀ i) hi₀
      _ ≤ ∑ g ∈ cutGoods A X, ∑ i ∈ B \ cutBuyers B X, if E g i then bigM A B a b else 0 :=
          Finset.single_le_sum
            (f := fun g => ∑ i ∈ B \ cutBuyers B X, if E g i then bigM A B a b else 0)
            (fun g _ => Finset.sum_nonneg fun i _ => hterm_nn g i) hg₀
  rw [cutWeight_bipCap hs ht]
  have h1 : 0 ≤ ∑ g ∈ A \ cutGoods A X, a g :=
    Finset.sum_nonneg fun g hg => ha g (Finset.mem_sdiff.1 hg).1
  have h2 : 0 ≤ ∑ i ∈ cutBuyers B X, b i :=
    Finset.sum_nonneg fun i hi => hb i (Finset.mem_filter.1 hi).1
  have hb_nn : 0 ≤ ∑ i ∈ B, b i := Finset.sum_nonneg hb
  have hbig : ∑ g ∈ A, a g < bigM A B a b := by unfold bigM; linarith
  linarith

/-- Any `s`–`t` cut crossing an active bipartite arc `(g, i)` has weight strictly exceeding both
`∑ g ∈ A, a g` and `∑ i ∈ B, b i`, hence cannot be a minimum `s`–`t` cut. -/
private theorem no_cross_of_minCut [DecidableEq I] [DecidableEq G] {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i)
    {X : Finset (FlowVertex I G)} (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X)
    (hmin : cutWeight (bipCap A B a b E) X =
      minRealCutBetween (bipCap A B a b E) .source .sink) :
    ∀ g ∈ cutGoods A X, ∀ i ∈ B \ cutBuyers B X, ¬ E g i := by
  intro g₀ hg₀ i₀ hi₀ hE
  have hlt := sum_lt_cutWeight_bipCap_of_cross ha hb hs ht hg₀ hi₀ hE
  have hle_src : cutWeight (bipCap A B a b E) X ≤ ∑ g ∈ A, a g := by
    rw [hmin, ← cutWeight_bipCap_source A B a b E]
    exact minRealCutBetween_le_cutWeight _ (Finset.mem_singleton_self _) (by simp)
  linarith

/-- **Generic Lemma 5.3 on any bipartite subnetwork**: `{.source}` is a min-cut in
`bipCap A B a b E` if and only if every `S ⊆ A` satisfies `∑ g ∈ S, a g ≤ ∑ i ∈ bipNbr B E S, b i`.
-/
private theorem source_minCut_bipCap_iff [DecidableEq I] [DecidableEq G]
    {A : Finset G} {B : Finset I} {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i) :
    cutWeight (bipCap A B a b E) ({.source} : Finset (FlowVertex I G)) =
        minRealCutBetween (bipCap A B a b E) .source .sink ↔
      ∀ S ⊆ A, ∑ g ∈ S, a g ≤ ∑ i ∈ bipNbr B E S, b i := by
  constructor
  · intro hmin S hSA
    set X := mkCut S (bipNbr B E S)
    have hX_le : cutWeight (bipCap A B a b E) ({.source} : Finset (FlowVertex I G)) ≤
        cutWeight (bipCap A B a b E) X := by
      rw [hmin]
      exact minRealCutBetween_le_cutWeight _ (source_mem_mkCut _ _) (sink_notMem_mkCut _ _)
    have hcutG : cutGoods A X = S := by
      ext g
      simp only [cutGoods, Finset.mem_filter, X, good_mem_mkCut_iff, and_iff_right_iff_imp]
      exact fun hg => hSA hg
    have hcutB : cutBuyers B X = bipNbr B E S := by
      ext i
      simp only [cutBuyers, Finset.mem_filter, X, buyer_mem_mkCut_iff, mem_bipNbr]
      tauto
    have hnc : ∀ g ∈ cutGoods A X, ∀ i ∈ B \ cutBuyers B X, ¬ E g i := by
      intro g hg i hi hE
      rw [hcutG] at hg
      rw [Finset.mem_sdiff, hcutB, mem_bipNbr] at hi
      exact hi.2 ⟨hi.1, g, hg, hE⟩
    rw [cutWeight_bipCap_source, cutWeight_bipCap_of_no_cross (source_mem_mkCut _ _)
      (sink_notMem_mkCut _ _) hnc, hcutG, hcutB] at hX_le
    have hsplit : ∑ g ∈ A, a g = (∑ g ∈ S, a g) + ∑ g ∈ A \ S, a g := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hSA]
    linarith
  · intro hinv
    refine le_antisymm ?_ (minRealCutBetween_le_cutWeight _ (Finset.mem_singleton_self _) (by simp))
    rw [le_minRealCutBetween_iff _ (by simp)]
    intro X hs ht
    by_cases hcross : ∃ g ∈ cutGoods A X, ∃ i ∈ B \ cutBuyers B X, E g i
    · obtain ⟨g₀, hg₀, i₀, hi₀, hE⟩ := hcross
      rw [cutWeight_bipCap_source]
      exact (sum_lt_cutWeight_bipCap_of_cross ha hb hs ht hg₀ hi₀ hE).le
    · push Not at hcross
      rw [cutWeight_bipCap_source, cutWeight_bipCap_of_no_cross hs ht hcross]
      have hsub : bipNbr B E (cutGoods A X) ⊆ cutBuyers B X := by
        intro i hi
        rw [mem_bipNbr] at hi
        obtain ⟨hiB, g, hg, hE⟩ := hi
        by_contra hnot
        exact hcross g hg i (Finset.mem_sdiff.2 ⟨hiB, hnot⟩) hE
      have hsubA : cutGoods A X ⊆ A := Finset.filter_subset _ _
      have h1 := hinv (cutGoods A X) hsubA
      have h2 : ∑ i ∈ bipNbr B E (cutGoods A X), b i ≤ ∑ i ∈ cutBuyers B X, b i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hb i (Finset.mem_filter.1 hi).1
      have hsplit : ∑ g ∈ A, a g = (∑ g ∈ cutGoods A X, a g) + ∑ g ∈ A \ cutGoods A X, a g := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsubA]
      linarith

/-- Bipartite money flow feasibility predicate on a subnetwork `(A, B, a, b, E)`. -/
private def IsBipFlow (A : Finset G) (B : Finset I)
    (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) (f : G → I → ℝ) : Prop :=
  (∀ g i, 0 ≤ f g i) ∧
  (∀ g i, 0 < f g i → g ∈ A ∧ i ∈ B ∧ E g i) ∧
  (∀ g ∈ A, ∑ i ∈ B, f g i ≤ a g) ∧
  (∀ i ∈ B, ∑ g ∈ A, f g i ≤ b i)

/-- Extract the bipartite money flow `g i ↦ F (.good g, .buyer i)` from a `RealFlow` `F`. -/
@[expose] def ofRealFlow (F : FlowVertex I G × FlowVertex I G → ℝ) (g : G) (i : I) : ℝ :=
  F (.good g, .buyer i)

/-- Lift a bipartite money flow `f : G → I → ℝ` to a flow on `FlowVertex I G`. -/
private def toRealFlow (f : G → I → ℝ) : FlowVertex I G × FlowVertex I G → ℝ
  | (.source, .good g) => ∑ i : I, f g i
  | (.good g, .buyer i) => f g i
  | (.buyer i, .sink) => ∑ g : G, f g i
  | _ => 0

private theorem isFeasibleRealFlow_toRealFlow {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop} {f : G → I → ℝ}
    (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i)
    (hf : IsBipFlow A B a b E f) :
    IsFeasibleRealFlow (bipCap A B a b E) .source .sink (toRealFlow f) := by
  classical
  have hf0 : ∀ g i, ¬ (g ∈ A ∧ i ∈ B ∧ E g i) → f g i = 0 := fun g i h =>
    le_antisymm (not_lt.1 fun hpos => h (hf.2.1 g i hpos)) (hf.1 g i)
  have hsumG (g : G) : ∑ i : I, f g i = if g ∈ A then ∑ i ∈ B, f g i else 0 := by
    split_ifs with hgA
    · symm
      refine Finset.sum_subset (Finset.subset_univ B) fun i _ hiB => hf0 g i fun h => hiB h.2.1
    · exact Finset.sum_eq_zero fun i _ => hf0 g i fun h => hgA h.1
  have hsumB (i : I) : ∑ g : G, f g i = if i ∈ B then ∑ g ∈ A, f g i else 0 := by
    split_ifs with hiB
    · symm
      refine Finset.sum_subset (Finset.subset_univ A) fun g _ hgA => hf0 g i fun h => hgA h.1
    · exact Finset.sum_eq_zero fun g _ => hf0 g i fun h => hiB h.2.1
  refine ⟨fun u v => ?_, fun u v => ?_, fun v hvs hvt => ?_⟩
  · cases u <;> cases v <;> simp only [toRealFlow] <;> try exact le_rfl
    · exact Finset.sum_nonneg fun i _ => hf.1 _ i
    · exact hf.1 _ _
    · exact Finset.sum_nonneg fun g _ => hf.1 g _
  · cases u <;> cases v <;> simp only [toRealFlow, bipCap] <;> try exact le_rfl
    · rename_i g
      rw [hsumG]; split_ifs with hgA
      · exact hf.2.2.1 g hgA
      · exact le_rfl
    · rename_i g i
      split_ifs with h
      · have hle : f g i ≤ ∑ i' ∈ B, f g i' :=
          Finset.single_le_sum (fun i' _ => hf.1 g i') h.2.1
        have hle2 : ∑ i' ∈ B, f g i' ≤ a g := hf.2.2.1 g h.1
        have hle3 : a g ≤ ∑ g' ∈ A, a g' := Finset.single_le_sum ha h.1
        have hb_nn : 0 ≤ ∑ i' ∈ B, b i' := Finset.sum_nonneg hb
        unfold bigM
        linarith
      · exact (hf0 g i h).le
    · rename_i i
      rw [hsumB]; split_ifs with hiB
      · exact hf.2.2.2 i hiB
      · exact le_rfl
  · cases v with
    | source => exact absurd rfl hvs
    | sink => exact absurd rfl hvt
    | good g =>
      rw [sum_flowVertex, sum_flowVertex]
      simp [toRealFlow]
    | buyer i =>
      rw [sum_flowVertex, sum_flowVertex]
      simp [toRealFlow]

private theorem realNetOut_toRealFlow (f : G → I → ℝ) :
    realNetOut (toRealFlow f) .source = ∑ g : G, ∑ i : I, f g i := by
  rw [realNetOut, sum_flowVertex, sum_flowVertex]
  simp [toRealFlow]

private theorem isBipFlow_ofRealFlow {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow (bipCap A B a b E) .source .sink F) :
    IsBipFlow A B a b E (ofRealFlow F) ∧
      (∀ g, F (.source, .good g) = ∑ i : I, ofRealFlow F g i) ∧
      (∀ i, F (.buyer i, .sink) = ∑ g : G, ofRealFlow F g i) ∧
      realNetOut F .source = ∑ g ∈ A, ∑ i ∈ B, ofRealFlow F g i := by
  classical
  have hzero {u v : FlowVertex I G} (hW : bipCap A B a b E u v = 0) : F (u, v) = 0 :=
    le_antisymm (hW ▸ hF.2.1 u v) (hF.1 u v)
  have hsupp : ∀ g i, 0 < ofRealFlow F g i → g ∈ A ∧ i ∈ B ∧ E g i := by
    intro g i hpos
    by_contra h
    have hz : bipCap A B a b E (.good g) (.buyer i) = 0 := by simp [bipCap, h]
    have h0 := hzero hz
    dsimp only [ofRealFlow] at hpos
    linarith
  have hfg0 : ∀ g i, ¬ (g ∈ A ∧ i ∈ B ∧ E g i) → ofRealFlow F g i = 0 := fun g i h =>
    le_antisymm (not_lt.1 fun hpos => h (hsupp g i hpos)) (hF.1 _ _)
  have hsrc_eq (g : G) : F (.source, .good g) = ∑ i : I, ofRealFlow F g i := by
    have hcons := hF.2.2 (.good g) (by simp) (by simp)
    rw [sum_flowVertex, sum_flowVertex] at hcons
    have h1 : ∑ g' : G, F (.good g', .good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h2 : ∑ i : I, F (.buyer i, .good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h3 : F (.sink, .good g) = 0 := hzero (by simp [bipCap])
    have h4 : F (.good g, .source) = 0 := hzero (by simp [bipCap])
    have h5 : ∑ g' : G, F (.good g, .good g') = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h6 : F (.good g, .sink) = 0 := hzero (by simp [bipCap])
    simp only [h1, h2, h3, h4, h5, h6, add_zero, zero_add] at hcons
    exact hcons
  have hsink_eq (i : I) : F (.buyer i, .sink) = ∑ g : G, ofRealFlow F g i := by
    have hcons := hF.2.2 (.buyer i) (by simp) (by simp)
    rw [sum_flowVertex, sum_flowVertex] at hcons
    have h1 : F (.source, .buyer i) = 0 := hzero (by simp [bipCap])
    have h2 : ∑ i' : I, F (.buyer i', .buyer i) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h3 : F (.sink, .buyer i) = 0 := hzero (by simp [bipCap])
    have h4 : F (.buyer i, .source) = 0 := hzero (by simp [bipCap])
    have h5 : ∑ g : G, F (.buyer i, .good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h6 : ∑ i' : I, F (.buyer i, .buyer i') = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    simp only [h1, h2, h3, h4, h5, h6, add_zero, zero_add] at hcons
    exact hcons.symm
  have hval : realNetOut F .source = ∑ g ∈ A, ∑ i ∈ B, ofRealFlow F g i := by
    rw [realNetOut, sum_flowVertex, sum_flowVertex]
    have h1 : F (.source, .source) = 0 := hzero (by simp [bipCap])
    have h2 : ∑ i : I, F (.source, .buyer i) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h3 : F (.source, .sink) = 0 := hzero (by simp [bipCap])
    have h4 : ∑ g : G, F (.good g, .source) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h5 : ∑ i : I, F (.buyer i, .source) = 0 :=
      Finset.sum_eq_zero fun _ _ => hzero (by simp [bipCap])
    have h6 : F (.sink, .source) = 0 := hzero (by simp [bipCap])
    simp only [h1, h2, h3, h4, h5, h6, add_zero, zero_add, sub_zero, hsrc_eq]
    symm
    calc
      ∑ g ∈ A, ∑ i ∈ B, ofRealFlow F g i
        = ∑ g ∈ A, ∑ i : I, ofRealFlow F g i :=
            Finset.sum_congr rfl fun g _ =>
              Finset.sum_subset (Finset.subset_univ B) fun i _ hiB =>
                hfg0 g i fun h => hiB h.2.1
      _ = ∑ g : G, ∑ i : I, ofRealFlow F g i :=
            Finset.sum_subset (Finset.subset_univ A) fun g _ hgA =>
              Finset.sum_eq_zero fun i _ => hfg0 g i fun h => hgA h.1
  refine ⟨⟨fun g i => hF.1 _ _, hsupp, fun g hgA => ?_, fun i hiB => ?_⟩, hsrc_eq, hsink_eq, hval⟩
  · calc
      ∑ i ∈ B, ofRealFlow F g i ≤ ∑ i : I, ofRealFlow F g i :=
        Finset.sum_le_univ_sum_of_nonneg fun i => hF.1 _ _
      _ = F (.source, .good g) := (hsrc_eq g).symm
      _ ≤ bipCap A B a b E .source (.good g) := hF.2.1 _ _
      _ = a g := by simp [bipCap, hgA]
  · calc
      ∑ g ∈ A, ofRealFlow F g i ≤ ∑ g : G, ofRealFlow F g i :=
        Finset.sum_le_univ_sum_of_nonneg fun g => hF.1 _ _
      _ = F (.buyer i, .sink) := (hsink_eq i).symm
      _ ≤ bipCap A B a b E (.buyer i) .sink := hF.2.1 _ _
      _ = b i := by simp [bipCap, hiB]

end BipartiteNetwork

/-! ### Section 5.3: Equality subgraph, network `N(p)`, and Lemma 5.2 -/

section EqualityNetwork

variable {I G : Type*}

/-- An **equality edge** between buyer `i` and good `g` at prices `p` ([Vazirani2007],
Section 5.3, p. 108): good `g` maximizes buyer `i`'s bang-per-buck `M.bangPerBuck p i g =
M.utility i g / p g`. -/
@[expose] def IsEqualityEdge (M : LinearFisherMarket I G) (p : G → ℝ) (i : I) (g : G) : Prop :=
  ∀ g' : G, M.bangPerBuck p i g' ≤ M.bangPerBuck p i g

theorem isEqualityEdge_smul {M : LinearFisherMarket I G} {p : G → ℝ} {c : ℝ} (hc : 0 < c)
    (i : I) (g : G) :
    M.IsEqualityEdge (c • p) i g ↔ M.IsEqualityEdge p i g := by
  have hdiv (g' : G) : M.bangPerBuck (c • p) i g' = c⁻¹ * M.bangPerBuck p i g' := by
    simp only [bangPerBuck_eq, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_div_div_swap, div_eq_inv_mul]
  simp only [IsEqualityEdge, hdiv, mul_le_mul_iff_right₀ (inv_pos.2 hc)]

/-- Under `hbuyer : ∃ g, 0 < M.utility i g` and positive prices `hp`, every equality edge incident
to buyer `i` has strictly positive marginal utility. -/
theorem utility_pos_of_isEqualityEdge {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) {i : I} (hbuyer : ∃ g, 0 < M.utility i g) {g : G}
    (he : M.IsEqualityEdge p i g) : 0 < M.utility i g := by
  obtain ⟨g₀, hg₀⟩ := hbuyer
  have hle : M.utility i g₀ / p g₀ ≤ M.utility i g / p g := by
    simpa only [bangPerBuck_eq] using he g₀
  have hpos : 0 < M.utility i g / p g := (div_pos hg₀ (hp g₀)).trans_le hle
  exact (div_pos_iff_of_pos_right (hp g)).1 hpos

variable [Fintype I] [Fintype G]

/-- The bipartite **money-flow network `N(p)`** ([Vazirani2007], Section 5.3.1, p. 108), with
capacity `p g * M.supply g` on `(.source, .good g)`, capacity `M.budget i` on `(.buyer i, .sink)`,
and a non-binding finite capacity `∑ g, p g * M.supply g + ∑ i, M.budget i + 1` on equality arcs
`(.good g, .buyer i)`. For `unitSupply` (`M.supply g = 1`), source arcs have capacity `p g`. -/
noncomputable def equalityNetwork (M : LinearFisherMarket I G) (p : G → ℝ) :
    FlowVertex I G → FlowVertex I G → ℝ :=
  bipCap Finset.univ Finset.univ (fun g => p g * M.supply g) M.budget
    (fun g i => M.IsEqualityEdge p i g)

/-- Feasible bipartite money flow `f : G → I → ℝ` in `N(p)`: nonnegative, supported on equality
edges, sending at most `p g * M.supply g` out of each good `g`, and sending at most `M.budget i`
into each buyer `i`. -/
@[expose] def IsEqualityFlow (M : LinearFisherMarket I G) (p : G → ℝ) (f : G → I → ℝ) : Prop :=
  (∀ g i, 0 ≤ f g i) ∧
  (∀ g i, 0 < f g i → M.IsEqualityEdge p i g) ∧
  (∀ g, ∑ i : I, f g i ≤ p g * M.supply g) ∧
  (∀ i, ∑ g : G, f g i ≤ M.budget i)

private theorem isEqualityFlow_iff_isBipFlow (M : LinearFisherMarket I G) (p : G → ℝ)
    (f : G → I → ℝ) :
    M.IsEqualityFlow p f ↔
      IsBipFlow Finset.univ Finset.univ (fun g => p g * M.supply g) M.budget
        (fun g i => M.IsEqualityEdge p i g) f := by
  simp [IsEqualityFlow, IsBipFlow]

/-- Total money value `∑ g, ∑ i, f g i` routed by a bipartite money flow `f`. -/
@[expose] def flowValue (f : G → I → ℝ) : ℝ :=
  ∑ g : G, ∑ i : I, f g i

/-- Allocation `x i g = f g i / p g` induced by a bipartite money flow `f` in `N(p)`
([Vazirani2007], Section 5.3.1, p. 109). -/
@[expose] noncomputable def moneyFlowToAlloc (f : G → I → ℝ) (p : G → ℝ) (i : I) (g : G) : ℝ :=
  f g i / p g

/-- A bipartite equality flow `f` is a **maximum equality flow** in `N(p)` if it is feasible and
maximizes `flowValue` over all feasible equality flows. -/
@[expose] def IsMaxEqualityFlow (M : LinearFisherMarket I G) (p : G → ℝ)
    (f : G → I → ℝ) : Prop :=
  M.IsEqualityFlow p f ∧ ∀ f', M.IsEqualityFlow p f' → flowValue f' ≤ flowValue f

theorem equalityNetwork_nonneg {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (u v : FlowVertex I G) : 0 ≤ M.equalityNetwork p u v :=
  bipCap_nonneg (fun g _ => mul_nonneg (hp g) (M.supply_nonneg g))
    (fun i _ => M.budget_nonneg i) u v

theorem cutWeight_equalityNetwork_source [DecidableEq I] [DecidableEq G]
    (M : LinearFisherMarket I G) (p : G → ℝ) :
    cutWeight (M.equalityNetwork p) ({.source} : Finset (FlowVertex I G)) =
      ∑ g : G, p g * M.supply g :=
  cutWeight_bipCap_source _ _ _ _ _

theorem cutWeight_equalityNetwork_sink [DecidableEq I] [DecidableEq G]
    (M : LinearFisherMarket I G) (p : G → ℝ) :
    cutWeight (M.equalityNetwork p) (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
      ∑ i : I, M.budget i :=
  cutWeight_bipCap_sink _ _ _ _ _

/-- **Lemma 5.2 (allocation recovery)** ([Vazirani2007], Section 5.3.1, p. 109): if both cuts
`({.source}, A ∪ B ∪ {.sink})` and `({.source} ∪ A ∪ B, {.sink})` are min-cuts in `N(p)` at
positive prices `p`, then the allocation `moneyFlowToAlloc (ofRealFlow F) p` induced by **any**
maximum flow `F` in `N(p)` is a market equilibrium allocation. -/
theorem isEquilibrium_of_isMaxRealFlow [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hgood : ∀ g, ∃ i, 0 < M.utility i g)
    (hsrc : cutWeight (M.equalityNetwork p) ({.source} : Finset (FlowVertex I G)) =
      minRealCutBetween (M.equalityNetwork p) .source .sink)
    (hsink : cutWeight (M.equalityNetwork p) (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
      minRealCutBetween (M.equalityNetwork p) .source .sink)
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow (M.equalityNetwork p) .source .sink F)
    (hFmax : IsMaxRealFlow (M.equalityNetwork p) .source .sink (realNetOut F .source)) :
    M.IsEquilibrium (moneyFlowToAlloc (ofRealFlow F) p) p := by
  have hW_nn := M.equalityNetwork_nonneg fun g => (hp g).le
  have hval_eq : realNetOut F .source = minRealCutBetween (M.equalityNetwork p) .source .sink :=
    IsGreatest.unique hFmax (isMaxRealFlow_minRealCutBetween hW_nn (by simp))
  obtain ⟨hf_bip, -, -, hval_sum⟩ := isBipFlow_ofRealFlow hF
  set f := ofRealFlow F
  have hf : M.IsEqualityFlow p f := (isEqualityFlow_iff_isBipFlow M p f).2 hf_bip
  have hsum_goods : ∑ g : G, ∑ i : I, f g i = ∑ g : G, p g * M.supply g := by
    rw [← hval_sum, hval_eq, ← hsrc, cutWeight_equalityNetwork_source]
  have hsum_buyers : ∑ i : I, ∑ g : G, f g i = ∑ i : I, M.budget i := by
    rw [Finset.sum_comm, ← hval_sum, hval_eq, ← hsink, cutWeight_equalityNetwork_sink]
  have hgood_sat : ∀ g : G, ∑ i : I, f g i = p g * M.supply g := by
    intro g
    have hdiff : ∑ g' : G, (p g' * M.supply g' - ∑ i : I, f g' i) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_goods, sub_self]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun g' _ =>
      sub_nonneg.2 (hf.2.2.1 g')).1 hdiff g (Finset.mem_univ g)
    linarith
  have hbuyer_sat : ∀ i : I, ∑ g : G, f g i = M.budget i := by
    intro i
    have hdiff : ∑ i' : I, (M.budget i' - ∑ g : G, f g i') = 0 := by
      rw [Finset.sum_sub_distrib, hsum_buyers, sub_self]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i' _ =>
      sub_nonneg.2 (hf.2.2.2 i')).1 hdiff i (Finset.mem_univ i)
    linarith
  rw [isEquilibrium_iff_bangPerBuck hbuyer hgood]
  refine ⟨hp, fun i g => div_nonneg (hf.1 g i) (hp g).le, fun g => ?_, fun i => ?_,
    fun i g hpos => ?_⟩
  · simp only [moneyFlowToAlloc, ← Finset.sum_div, hgood_sat g]
    exact mul_div_cancel_left₀ (M.supply g) (hp g).ne'
  · simp only [expenditure_eq_sum, moneyFlowToAlloc]
    calc
      ∑ g : G, p g * (f g i / p g) = ∑ g : G, f g i :=
        Finset.sum_congr rfl fun g _ => mul_div_cancel₀ (f g i) (hp g).ne'
      _ = M.budget i := hbuyer_sat i
  · exact hf.2.1 g i ((div_pos_iff_of_pos_right (hp g)).1 hpos)

/-- **Lemma 5.2 (equilibrium price test)** ([Vazirani2007], Section 5.3.1, p. 109): positive prices
`p` are equilibrium prices of a linear Fisher market (where every buyer desires some good and every
good is desired by some buyer) if and only if both `({.source}, A ∪ B ∪ {.sink})` and
`({.source} ∪ A ∪ B, {.sink})` are minimum `s`–`t` cuts in `N(p)`. -/
theorem exists_isEquilibrium_iff_minCut [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hgood : ∀ g, ∃ i, 0 < M.utility i g) :
    (∃ x : I → G → ℝ, M.IsEquilibrium x p) ↔
      cutWeight (M.equalityNetwork p) ({.source} : Finset (FlowVertex I G)) =
        minRealCutBetween (M.equalityNetwork p) .source .sink ∧
      cutWeight (M.equalityNetwork p) (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
        minRealCutBetween (M.equalityNetwork p) .source .sink := by
  have hW_nn := M.equalityNetwork_nonneg fun g => (hp g).le
  constructor
  · rintro ⟨x, heq⟩
    obtain ⟨-, hx_nn, hclear, hexp, hmax⟩ := (isEquilibrium_iff_bangPerBuck hbuyer hgood).1 heq
    let f : G → I → ℝ := fun g i => p g * x i g
    have hf : M.IsEqualityFlow p f := by
      refine ⟨fun g i => mul_nonneg (hp g).le (hx_nn i g), fun g i hpos => ?_, fun g => ?_,
        fun i => ?_⟩
      · exact hmax i g (pos_of_mul_pos_right hpos (hp g).le)
      · simp only [f, ← Finset.mul_sum, hclear g, le_rfl]
      · simp only [f, ← expenditure_eq_sum, hexp i, le_rfl]
    have hF : IsFeasibleRealFlow (M.equalityNetwork p) .source .sink (toRealFlow f) :=
      isFeasibleRealFlow_toRealFlow (fun g _ => mul_nonneg (hp g).le (M.supply_nonneg g))
        (fun i _ => M.budget_nonneg i) ((isEqualityFlow_iff_isBipFlow M p f).1 hf)
    have hval_src : realNetOut (toRealFlow f) .source =
        cutWeight (M.equalityNetwork p) ({.source} : Finset (FlowVertex I G)) := by
      rw [realNetOut_toRealFlow, cutWeight_equalityNetwork_source]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [f, ← Finset.mul_sum, hclear g]
    have hval_sink : realNetOut (toRealFlow f) .source =
        cutWeight (M.equalityNetwork p) (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) := by
      rw [realNetOut_toRealFlow, Finset.sum_comm, cutWeight_equalityNetwork_sink]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [f, ← expenditure_eq_sum, hexp i]
    have hle_min : realNetOut (toRealFlow f) .source ≤
        minRealCutBetween (M.equalityNetwork p) .source .sink :=
      (isMaxRealFlow_minRealCutBetween hW_nn (by simp)).2 ⟨toRealFlow f, hF, rfl⟩
    exact ⟨le_antisymm (hval_src ▸ hle_min)
        (minRealCutBetween_le_cutWeight _ (Finset.mem_singleton_self _) (by simp)),
      le_antisymm (hval_sink ▸ hle_min)
        (minRealCutBetween_le_cutWeight _ (by simp) (by simp))⟩
  · rintro ⟨hsrc, hsink⟩
    obtain ⟨F, hF, hFmax⟩ := exists_isMaxRealFlow hW_nn .source .sink
    exact ⟨moneyFlowToAlloc (ofRealFlow F) p,
      isEquilibrium_of_isMaxRealFlow hp hbuyer hgood hsrc hsink hF hFmax⟩

end EqualityNetwork

/-! ### Section 5.6: Tight sets, the Invariant, Lemma 5.3, and the maximal tight set -/

section TightSets

variable {I G : Type*} [Fintype I]

/-- Equality-subgraph neighborhood `Γ(S)` of a set of goods `S ⊆ G`: buyers having an equality edge
to at least one good in `S` ([Vazirani2007], Section 5.6, p. 111). -/
noncomputable def buyerNeighborhood (M : LinearFisherMarket I G) (p : G → ℝ)
    (S : Finset G) : Finset I :=
  bipNbr Finset.univ (fun g i => M.IsEqualityEdge p i g) S

theorem mem_buyerNeighborhood {M : LinearFisherMarket I G} {p : G → ℝ} {S : Finset G} {i : I} :
    i ∈ M.buyerNeighborhood p S ↔ ∃ g ∈ S, M.IsEqualityEdge p i g := by
  simp [buyerNeighborhood, mem_bipNbr]

/-- Total money value `∑ g ∈ S, p g * M.supply g` of the goods in `S` (`∑ g ∈ S, p g` for unit
supply; [Vazirani2007], Section 5.6, p. 111). -/
@[expose] def goodValue (M : LinearFisherMarket I G) (p : G → ℝ) (S : Finset G) : ℝ :=
  ∑ g ∈ S, p g * M.supply g

/-- Total money budget `∑ i ∈ T, M.budget i` of buyers in `T` ([Vazirani2007], Section 5.6,
p. 111). -/
@[expose] def budgetSum (M : LinearFisherMarket I G) (T : Finset I) : ℝ :=
  ∑ i ∈ T, M.budget i

/-- A subset of goods `S` is a **tight set** at prices `p` if its total value equals the total
budget of its equality-subgraph neighborhood `Γ(S)` ([Vazirani2007], Section 5.6, p. 111). -/
@[expose] def IsTightSet (M : LinearFisherMarket I G) (p : G → ℝ) (S : Finset G) : Prop :=
  M.goodValue p S = M.budgetSum (M.buyerNeighborhood p S)

variable [Fintype G]

/-- **The Invariant** ([Vazirani2007], Section 5.6, p. 111): prices `p` satisfy the Invariant when
the source cut `({.source}, A ∪ B ∪ {.sink})` is a minimum `s`–`t` cut in `N(p)`. -/
@[expose] def SatisfiesInvariant [DecidableEq I] [DecidableEq G] (M : LinearFisherMarket I G)
    (p : G → ℝ) : Prop :=
  cutWeight (M.equalityNetwork p) ({.source} : Finset (FlowVertex I G)) =
    minRealCutBetween (M.equalityNetwork p) .source .sink

/-- **Lemma 5.3** ([Vazirani2007], Section 5.6, p. 111): for nonnegative prices `p`, `N(p)`
satisfies the Invariant if and only if `M.goodValue p S ≤ M.budgetSum (M.buyerNeighborhood p S)`
for every subset `S` of goods. -/
theorem satisfiesInvariant_iff [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) :
    M.SatisfiesInvariant p ↔
      ∀ S : Finset G, M.goodValue p S ≤ M.budgetSum (M.buyerNeighborhood p S) := by
  simpa only [SatisfiesInvariant, equalityNetwork, goodValue, budgetSum, buyerNeighborhood,
    Finset.subset_univ, forall_true_left] using
    source_minCut_bipCap_iff (A := Finset.univ) (B := Finset.univ)
      (a := fun g => p g * M.supply g) (b := M.budget) (E := fun g i => M.IsEqualityEdge p i g)
      (fun g _ => mul_nonneg (hp g) (M.supply_nonneg g)) (fun i _ => M.budget_nonneg i)

omit [Fintype G] in
/-- Submodularity of `S ↦ M.budgetSum (M.buyerNeighborhood p S)`. -/
private theorem budgetSum_buyerNeighborhood_union_add_inter_le [DecidableEq G]
    (M : LinearFisherMarket I G) (p : G → ℝ) (S₁ S₂ : Finset G) :
    M.budgetSum (M.buyerNeighborhood p (S₁ ∪ S₂)) +
        M.budgetSum (M.buyerNeighborhood p (S₁ ∩ S₂)) ≤
      M.budgetSum (M.buyerNeighborhood p S₁) + M.budgetSum (M.buyerNeighborhood p S₂) := by
  classical
  have hunion : M.buyerNeighborhood p (S₁ ∪ S₂) =
      M.buyerNeighborhood p S₁ ∪ M.buyerNeighborhood p S₂ :=
    bipNbr_union _ _ S₁ S₂
  have hinter : M.budgetSum (M.buyerNeighborhood p (S₁ ∩ S₂)) ≤
      M.budgetSum (M.buyerNeighborhood p S₁ ∩ M.buyerNeighborhood p S₂) :=
    Finset.sum_le_sum_of_subset_of_nonneg (bipNbr_inter_subset _ _ S₁ S₂)
      fun i _ _ => M.budget_nonneg i
  have hmod : M.budgetSum (M.buyerNeighborhood p S₁ ∪ M.buyerNeighborhood p S₂) +
      M.budgetSum (M.buyerNeighborhood p S₁ ∩ M.buyerNeighborhood p S₂) =
      M.budgetSum (M.buyerNeighborhood p S₁) + M.budgetSum (M.buyerNeighborhood p S₂) :=
    Finset.sum_union_inter
  rw [hunion]
  linarith

/-- Under the Invariant, tight sets are closed under union and intersection
([Vazirani2007], Section 5.8, p. 115). -/
theorem isTightSet_union_and_inter [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hinv : M.SatisfiesInvariant p) {S₁ S₂ : Finset G}
    (h₁ : M.IsTightSet p S₁) (h₂ : M.IsTightSet p S₂) :
    M.IsTightSet p (S₁ ∪ S₂) ∧ M.IsTightSet p (S₁ ∩ S₂) := by
  have hall := (satisfiesInvariant_iff hp).1 hinv
  have hval : M.goodValue p (S₁ ∪ S₂) + M.goodValue p (S₁ ∩ S₂) =
      M.goodValue p S₁ + M.goodValue p S₂ :=
    Finset.sum_union_inter
  have hnbr_sub := budgetSum_buyerNeighborhood_union_add_inter_le M p S₁ S₂
  have hle_u := hall (S₁ ∪ S₂)
  have hle_i := hall (S₁ ∩ S₂)
  unfold IsTightSet at h₁ h₂ ⊢
  exact ⟨by linarith, by linarith⟩

/-- The union of all tight sets at prices `p` ([Vazirani2007], Section 5.8, p. 115). Under
`SatisfiesInvariant M p`, this is the unique maximal tight set. -/
noncomputable def maximalTightSet [DecidableEq G] (M : LinearFisherMarket I G)
    (p : G → ℝ) : Finset G :=
  open scoped Classical in (Finset.univ.filter fun S : Finset G => M.IsTightSet p S).biUnion id

theorem isTightSet_maximalTightSet [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hinv : M.SatisfiesInvariant p) :
    M.IsTightSet p (M.maximalTightSet p) := by
  classical
  have hbi : ∀ (F : Finset (Finset G)), (∀ S ∈ F, M.IsTightSet p S) →
      M.IsTightSet p (F.biUnion id) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      simp [IsTightSet, goodValue, budgetSum, buyerNeighborhood, bipNbr_empty]
    | @insert S F hSF ih =>
      intro hF
      rw [Finset.biUnion_insert]
      exact (isTightSet_union_and_inter hp hinv
        (hF S (Finset.mem_insert_self S F))
        (ih fun T hT => hF T (Finset.mem_insert_of_mem hT))).1
  exact hbi _ fun S hS => (Finset.mem_filter.1 hS).2

theorem subset_maximalTightSet [DecidableEq G] {M : LinearFisherMarket I G} {p : G → ℝ}
    {S : Finset G} (hS : M.IsTightSet p S) : S ⊆ M.maximalTightSet p := by
  classical
  intro g hg
  exact Finset.mem_biUnion.2 ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩, hg⟩

end TightSets

/-! ### Section 5.7: Balanced flows, Lemma 5.4, and Theorem 5.5 -/

section BalancedFlows

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Buyer `i`'s surplus money `M.budget i - ∑ g, f g i` under a bipartite money flow `f`
([Vazirani2007], Section 5.7, pp. 111–112). -/
@[expose] def surplus (M : LinearFisherMarket I G) (f : G → I → ℝ) (i : I) : ℝ :=
  M.budget i - ∑ g : G, f g i

/-- Squared `ℓ₂` norm `∑ i, (M.surplus f i) ^ 2` of the surplus vector ([Vazirani2007],
Section 5.5, p. 110; Section 5.7, p. 112). Minimizing `surplusSqNorm` is equivalent to minimizing
the `ℓ₂` norm `√(surplusSqNorm)`. -/
@[expose] def surplusSqNorm (M : LinearFisherMarket I G) (f : G → I → ℝ) : ℝ :=
  ∑ i : I, (M.surplus f i) ^ 2

/-- A **balanced flow** in `N(p)` ([Vazirani2007], Section 5.7, p. 112): a feasible equality money
flow minimizing `surplusSqNorm M f` (equivalently, the `ℓ₂` norm of the surplus vector) over all
feasible equality flows. -/
@[expose] def IsBalancedFlow (M : LinearFisherMarket I G) (p : G → ℝ) (f : G → I → ℝ) : Prop :=
  M.IsEqualityFlow p f ∧ ∀ f', M.IsEqualityFlow p f' → M.surplusSqNorm f ≤ M.surplusSqNorm f'

/-- Minimizing `surplusSqNorm` is equivalent to minimizing the Euclidean `ℓ₂` norm
`Real.sqrt (surplusSqNorm)`. -/
theorem isBalancedFlow_iff_sqrt {M : LinearFisherMarket I G} {p : G → ℝ} {f : G → I → ℝ} :
    M.IsBalancedFlow p f ↔
      M.IsEqualityFlow p f ∧
        ∀ f', M.IsEqualityFlow p f' →
          Real.sqrt (M.surplusSqNorm f) ≤ Real.sqrt (M.surplusSqNorm f') := by
  have hnn (h : G → I → ℝ) : 0 ≤ M.surplusSqNorm h :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  refine and_congr_right fun _ => forall_congr' fun f' => imp_congr_right fun _ => ?_
  exact ⟨fun h => Real.sqrt_le_sqrt h, fun h => by
    have := mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rwa [Real.mul_self_sqrt (hnn f), Real.mul_self_sqrt (hnn f')] at this⟩

/-- **Existence of a balanced flow**: for nonnegative prices `p`, `N(p)` always admits a balanced
flow (compactness of the feasible polytope and continuity of `surplusSqNorm`). -/
theorem exists_isBalancedFlow {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) :
    ∃ f : G → I → ℝ, M.IsBalancedFlow p f := by
  let K : Set (G → I → ℝ) := {f | M.IsEqualityFlow p f}
  have h0 : (0 : G → I → ℝ) ∈ K :=
    ⟨fun _ _ => le_rfl, fun _ _ h => (lt_irrefl (0 : ℝ) h).elim,
      fun g => by simp [mul_nonneg (hp g) (M.supply_nonneg g)],
      fun i => by simp [M.budget_nonneg i]⟩
  have hK_eq : K =
      (⋂ g, ⋂ i, {f : G → I → ℝ | 0 ≤ f g i}) ∩
      (⋂ g, ⋂ i, {f : G → I → ℝ | ¬ M.IsEqualityEdge p i g → f g i = 0}) ∩
      (⋂ g, {f : G → I → ℝ | ∑ i : I, f g i ≤ p g * M.supply g}) ∩
      (⋂ i, {f : G → I → ℝ | ∑ g : G, f g i ≤ M.budget i}) := by
    ext f
    simp only [K, IsEqualityFlow, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hnn, hsupp, hg, hi⟩
      exact ⟨⟨⟨hnn, fun g i hne => le_antisymm (not_lt.1 fun hpos => hne (hsupp g i hpos))
        (hnn g i)⟩, hg⟩, hi⟩
    · rintro ⟨⟨⟨hnn, hzero⟩, hg⟩, hi⟩
      exact ⟨hnn, fun g i hpos => by_contra fun hne => (hpos.ne' (hzero g i hne)), hg, hi⟩
  have hK_closed : IsClosed K := by
    rw [hK_eq]
    refine (((isClosed_iInter fun g => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_iInter fun g => isClosed_iInter fun i => ?_)).inter
      (isClosed_iInter fun g => isClosed_le (by fun_prop) continuous_const)).inter
      (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const)
    by_cases hE : M.IsEqualityEdge p i g
    · simp [hE]
    · simp only [hE, not_false_eq_true, true_implies]
      exact isClosed_eq (by fun_prop) continuous_const
  have hK_compact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun i =>
      isCompact_Icc (a := (0 : ℝ)) (b := M.budget i)).of_isClosed_subset hK_closed
      fun f hf g _ i _ => ⟨hf.1 g i,
        (Finset.single_le_sum (fun g' _ => hf.1 g' i) (Finset.mem_univ g)).trans (hf.2.2.2 i)⟩
  have hcont : ContinuousOn M.surplusSqNorm K := by
    have : Continuous M.surplusSqNorm := by
      unfold surplusSqNorm surplus
      fun_prop
    exact this.continuousOn
  obtain ⟨f, hfK, hfmin⟩ := hK_compact.exists_isMinOn ⟨0, h0⟩ hcont
  exact ⟨f, hfK, fun f' hf' => isMinOn_iff.1 hfmin f' hf'⟩

/-- **Lemma 5.4** ([Vazirani2007], Section 5.7, p. 112): all balanced flows in `N(p)` have the exact
same buyer surplus vector. Note that [Vazirani2007], p. 112 prints "strictly concave" for the
strictly convex objective `surplusSqNorm`. -/
theorem surplus_eq_of_isBalancedFlow {M : LinearFisherMarket I G} {p : G → ℝ}
    {f₁ f₂ : G → I → ℝ} (h₁ : M.IsBalancedFlow p f₁) (h₂ : M.IsBalancedFlow p f₂) :
    M.surplus f₁ = M.surplus f₂ := by
  let fmid : G → I → ℝ := fun g i => (f₁ g i + f₂ g i) / 2
  have hfmid : M.IsEqualityFlow p fmid := by
    refine ⟨fun g i => by dsimp only [fmid]; linarith [h₁.1.1 g i, h₂.1.1 g i], fun g i hpos => ?_,
      fun g => ?_, fun i => ?_⟩
    · rcases (h₁.1.1 g i).eq_or_lt with h0 | hlt
      · exact h₂.1.2.1 g i (by dsimp only [fmid] at hpos; linarith)
      · exact h₁.1.2.1 g i hlt
    · simp only [fmid, ← Finset.sum_div, Finset.sum_add_distrib]
      linarith [h₁.1.2.2.1 g, h₂.1.2.2.1 g]
    · simp only [fmid, ← Finset.sum_div, Finset.sum_add_distrib]
      linarith [h₁.1.2.2.2 i, h₂.1.2.2.2 i]
  have hsurp_mid (i : I) : M.surplus fmid i = (M.surplus f₁ i + M.surplus f₂ i) / 2 := by
    simp only [surplus, fmid, ← Finset.sum_div, Finset.sum_add_distrib]
    ring
  have hpara : ∑ i : I, (M.surplus f₁ i - M.surplus f₂ i) ^ 2 =
      2 * M.surplusSqNorm f₁ + 2 * M.surplusSqNorm f₂ - 4 * M.surplusSqNorm fmid := by
    simp only [surplusSqNorm, hsurp_mid, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle1 : M.surplusSqNorm f₁ ≤ M.surplusSqNorm fmid := h₁.2 fmid hfmid
  have hle2 : M.surplusSqNorm f₂ ≤ M.surplusSqNorm fmid := h₂.2 fmid hfmid
  have hsum0 : ∑ i : I, (M.surplus f₁ i - M.surplus f₂ i) ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  ext i
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 hsum0 i
    (Finset.mem_univ i)
  linarith [sq_eq_zero_iff.1 hi0]

/-- **Residual reachability in `R(f) - {s, t}`** ([Vazirani2007], Section 5.7, p. 112): buyer `i`
is reachable from buyer `j` along alternating backward flow edges `(b, g)` (`f g b > 0`) and
forward equality edges `(g, b')` (`M.IsEqualityEdge p b' g`). -/
@[expose] def ResidualReachable (M : LinearFisherMarket I G) (p : G → ℝ)
    (f : G → I → ℝ) (j i : I) : Prop :=
  Relation.ReflTransGen (fun u v => ∃ g : G, 0 < f g u ∧ M.IsEqualityEdge p v g) j i

/-- **Property 1 of balanced flows** ([Vazirani2007], Section 5.7, p. 112): whenever buyer `j` has
strictly smaller surplus than buyer `i`, there is no path from `j` to `i` in `R(f) - {s, t}`. -/
@[expose] def SatisfiesPropertyOne (M : LinearFisherMarket I G) (p : G → ℝ)
    (f : G → I → ℝ) : Prop :=
  ∀ j i : I, M.surplus f j < M.surplus f i → ¬ M.ResidualReachable p f j i

private theorem filter_length_le_one_of_nodup {α : Type*} [DecidableEq α] {L : List α}
    (hnd : L.Nodup) (x : α) : (L.filter fun a => a = x).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    by_cases hax : a = x
    · subst hax
      simp only [decide_true, ↓reduceIte, List.length_cons]
      have hnil : tl.filter (fun b => decide (b = a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        simp only [decide_eq_true_eq]
        exact fun hba => hnd.1 (hba ▸ hb)
      rw [hnil]
      simp
    · simp only [hax, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2

/-- Generic augmentation along a simple buyer residual chain `b₀ → … → bₖ` in `R(f) - {s, t}`:
transfers `ε > 0` units of spending from `b₀` to `bₖ` while preserving every good's outflow and
every intermediate buyer's spending. -/
private theorem exists_shift_along_resChain {E : G → I → Prop} {a : G → ℝ} {b : I → ℝ}
    {f : G → I → ℝ} (hf : IsBipFlow Finset.univ Finset.univ a b E f)
    {j i : I} (hreach : Relation.ReflTransGen (fun u v => ∃ g : G, 0 < f g u ∧ E g v) j i)
    (hsurp : b j - ∑ g, f g j < b i - ∑ g, f g i) :
    ∃ f' : G → I → ℝ, IsBipFlow Finset.univ Finset.univ a b E f' ∧
      (∑ b' : I, (b b' - ∑ g, f' g b') ^ 2) < ∑ b' : I, (b b' - ∑ g, f g b') ^ 2 := by
  classical
  obtain ⟨path, hnodup, hhead, hlast, harcs⟩ := exists_nodup_list_of_reflTransGen hreach
  have hne_ji : j ≠ i := fun h => lt_irrefl _ (h ▸ hsurp)
  let w : I × I → G := fun e =>
    if h : ∃ g : G, 0 < f g e.1 ∧ E g e.2 then h.choose else
      (show Nonempty G from by
        have hne_arcs := pathArcs_ne_nil_of_head?_ne_getLast? hne_ji hhead hlast
        rcases hpa : pathArcs path with _ | ⟨e₀, _⟩
        · exact absurd hpa hne_arcs
        · obtain ⟨g₀, -, -⟩ := harcs e₀ (by rw [hpa]; exact List.mem_cons_self)
          exact ⟨g₀⟩).some
  have hw_spec : ∀ e ∈ pathArcs path, 0 < f (w e) e.1 ∧ E (w e) e.2 := by
    intro e he
    have hex : ∃ g : G, 0 < f g e.1 ∧ E g e.2 := harcs e he
    simp only [w, hex, ↓reduceDIte]
    exact hex.choose_spec
  let d : G → I → ℝ := fun g x =>
    ((pathArcs path).map fun e =>
      if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0).sum
  have hd_good (g : G) : ∑ x : I, d g x = 0 := by
    have hswap : ∀ L : List (I × I),
        ∑ x : I, (L.map fun e =>
          if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0).sum
        = 0 := by
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, add_zero]
        split_ifs
        · simp [Finset.sum_sub_distrib]
        · simp
    exact hswap (pathArcs path)
  have hd_buyer (x : I) : ∑ g : G, d g x =
      (if x = i then (1 : ℝ) else 0) - (if x = j then 1 else 0) := by
    have hsum_g : ∀ L : List (I × I),
        ∑ g : G, (L.map fun e =>
          if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0).sum
        = (L.map fun e =>
          (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0)).sum := by
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
        congr 1
        rw [Finset.sum_eq_single (w e) (fun g _ hg => by simp [hg.symm]) (by simp)]
        simp
    rw [hsum_g]
    have htele : ∀ (L : List I) (a₀ b₀ : I), L.head? = some a₀ → L.getLast? = some b₀ →
        ((pathArcs L).map fun e =>
          (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0)).sum =
        (if x = b₀ then (1 : ℝ) else 0) - (if x = a₀ then 1 else 0) := by
      intro L
      induction L with
      | nil => intro _ _ h; simp at h
      | cons u rest ih =>
        intro a₀ b₀ hh hl
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        cases rest with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          simp [pathArcs_singleton]
        | cons v tl =>
          have hl' : (v :: tl).getLast? = some b₀ := by simpa using hl
          rw [pathArcs_cons_cons, List.map_cons, List.sum_cons, ih v b₀ rfl hl']
          ring
    exact htele path j i hhead hlast
  have hcard_fst (x : I) : ((pathArcs path).filter fun e => e.1 = x).length ≤ 1 := by
    have hnodup_fst : ((pathArcs path).map Prod.fst).Nodup :=
      hnodup.sublist (map_fst_pathArcs_sublist path)
    have hlen : ((pathArcs path).filter fun e => e.1 = x).length =
        (((pathArcs path).map Prod.fst).filter fun a => a = x).length := by
      rw [List.filter_map, List.length_map]
      rfl
    rw [hlen]
    exact filter_length_le_one_of_nodup hnodup_fst x
  have hd_pos_edge : ∀ g x, 0 < d g x → E g x := by
    intro g x hpos
    by_contra hnotE
    have hle : d g x ≤ 0 := by
      have hterm : ∀ e ∈ pathArcs path,
          (if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0)
            ≤ 0 := by
        intro e he
        by_cases hwg : w e = g
        · by_cases hx2 : x = e.2
          · exfalso; exact hnotE (hwg ▸ hx2 ▸ (hw_spec e he).2)
          · split_ifs <;> linarith
        · simp [hwg]
      have hlist : ∀ L : List (I × I), (∀ e ∈ L,
          (if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0)
            ≤ 0) →
          (L.map fun e =>
            if w e = g then
              (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0)
            else 0).sum ≤ 0 := by
        intro L
        induction L with
        | nil => intro _; simp
        | cons e es ih =>
          intro h
          simp only [List.map_cons, List.sum_cons]
          linarith [h e List.mem_cons_self, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]
      exact hlist _ hterm
    linarith
  have hd_neg_lower : ∀ g x, d g x < 0 → -1 ≤ d g x ∧ 0 < f g x := by
    intro g x hneg
    have hex : ∃ e ∈ pathArcs path, w e = g ∧ e.1 = x := by
      by_contra hall
      push Not at hall
      have hge : 0 ≤ d g x := by
        have hlist : ∀ L : List (I × I), (∀ e ∈ L, w e = g → e.1 ≠ x) →
            0 ≤ (L.map fun e =>
              if w e = g then (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0)
              else 0).sum := by
          intro L
          induction L with
          | nil => intro _; simp
          | cons e es ih =>
            intro h
            simp only [List.map_cons, List.sum_cons]
            have h0 : 0 ≤ if w e = g then
                (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0 := by
              by_cases hwg : w e = g
              · have hne1 : x ≠ e.1 := (h e List.mem_cons_self hwg).symm
                simp only [hwg, hne1, ↓reduceIte, sub_zero]
                split_ifs <;> linarith
              · simp [hwg]
            linarith [ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]
        exact hlist _ hall
      linarith
    obtain ⟨e₀, he₀, hwg₀, hfst₀⟩ := hex
    refine ⟨?_, hwg₀ ▸ hfst₀ ▸ (hw_spec e₀ he₀).1⟩
    have hlb : ∀ L : List (I × I),
        -((L.filter fun e => e.1 = x).length : ℝ) ≤
        (L.map fun e =>
          if w e = g then
            (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0)
          else 0).sum := by
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        by_cases h1 : e.1 = x
        · simp only [h1, decide_true, ↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
          have hterm : (-1 : ℝ) ≤ if w e = g then
              (if x = e.2 then (1 : ℝ) else 0) - 1 else 0 := by
            split_ifs <;> linarith
          linarith
        · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hterm : (0 : ℝ) ≤ if w e = g then
              (if x = e.2 then (1 : ℝ) else 0) - (if x = e.1 then 1 else 0) else 0 := by
            have hne1 : x ≠ e.1 := fun h => h1 h.symm
            simp only [hne1, ↓reduceIte, sub_zero]
            split_ifs <;> linarith
          linarith
    have hcard_r : (((pathArcs path).filter fun e => e.1 = x).length : ℝ) ≤ 1 := by
      exact_mod_cast hcard_fst x
    linarith [hlb (pathArcs path)]
  let negPairs : Finset (G × I) := Finset.univ.filter fun p => d p.1 p.2 < 0
  have hneg_pos : ∀ p ∈ negPairs, 0 < f p.1 p.2 := fun p hp =>
    (hd_neg_lower p.1 p.2 (Finset.mem_filter.1 hp).2).2
  set γj : ℝ := b j - ∑ g, f g j
  set γi : ℝ := b i - ∑ g, f g i
  set gap : ℝ := (γi - γj) / 2
  have hgap_pos : 0 < gap := half_pos (sub_pos.2 hsurp)
  let ε : ℝ := if h : negPairs.Nonempty then
    min gap (negPairs.inf' h fun p => f p.1 p.2) else gap
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    split_ifs with h
    · refine lt_min hgap_pos ?_
      rw [Finset.lt_inf'_iff]
      exact hneg_pos
    · exact hgap_pos
  have hε_le_gap : ε ≤ gap := by
    dsimp only [ε]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  have hε_le_f : ∀ g x, d g x < 0 → ε ≤ f g x := by
    intro g x hneg
    have hmem : (g, x) ∈ negPairs := Finset.mem_filter.2 ⟨Finset.mem_univ _, hneg⟩
    have hne : negPairs.Nonempty := ⟨(g, x), hmem⟩
    dsimp only [ε]
    rw [dite_eq_left hne]
    exact (min_le_right _ _).trans (Finset.inf'_le (fun p : G × I => f p.1 p.2) hmem)
  let f' : G → I → ℝ := fun g x => f g x + ε * d g x
  have hf'_nn : ∀ g x, 0 ≤ f' g x := by
    intro g x
    dsimp only [f']
    by_cases hneg : d g x < 0
    · have hlb := (hd_neg_lower g x hneg).1
      have hle := hε_le_f g x hneg
      nlinarith
    · push Not at hneg
      linarith [hf.1 g x, mul_nonneg hε_pos.le hneg]
  have hf'_supp : ∀ g x, 0 < f' g x → g ∈ Finset.univ ∧ x ∈ Finset.univ ∧ E g x := by
    intro g x hpos
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    dsimp only [f'] at hpos
    by_cases hfg : 0 < f g x
    · exact (hf.2.1 g x hfg).2.2
    · have hfg0 : f g x = 0 := le_antisymm (not_lt.1 hfg) (hf.1 g x)
      rw [hfg0, zero_add] at hpos
      exact hd_pos_edge g x (pos_of_mul_pos_right hpos hε_pos.le)
  have hf'_good : ∀ g ∈ (Finset.univ : Finset G), ∑ x ∈ Finset.univ, f' g x ≤ a g := by
    intro g _
    simp only [f', Finset.sum_add_distrib, ← Finset.mul_sum, hd_good g, mul_zero, add_zero]
    exact hf.2.2.1 g (Finset.mem_univ g)
  have hf'_sum (x : I) : ∑ g : G, f' g x =
      (∑ g : G, f g x) + ε * ((if x = i then 1 else 0) - (if x = j then 1 else 0)) := by
    simp only [f', Finset.sum_add_distrib, ← Finset.mul_sum, hd_buyer x]
  have hf'_buyer : ∀ x ∈ (Finset.univ : Finset I), ∑ g ∈ Finset.univ, f' g x ≤ b x := by
    intro x _
    rw [hf'_sum x]
    by_cases hxi : x = i
    · subst hxi
      simp only [↓reduceIte, hne_ji.symm, sub_zero, mul_one]
      have hgj_nn : 0 ≤ γj := sub_nonneg.2 (hf.2.2.2 j (Finset.mem_univ j))
      dsimp only [γj, γi, gap] at hgj_nn hε_le_gap
      linarith
    · by_cases hxj : x = j
      · subst hxj
        simp only [hne_ji, ↓reduceIte, zero_sub, mul_neg, mul_one]
        linarith [hf.2.2.2 x (Finset.mem_univ x), hε_pos]
      · simp only [hxi, hxj, ↓reduceIte, sub_self, mul_zero, add_zero]
        exact hf.2.2.2 x (Finset.mem_univ x)
  refine ⟨f', ⟨hf'_nn, hf'_supp, hf'_good, hf'_buyer⟩, ?_⟩
  have hdiff : (∑ x : I, (b x - ∑ g, f' g x) ^ 2) - ∑ x : I, (b x - ∑ g, f g x) ^ 2 =
      ((γj + ε) ^ 2 - γj ^ 2) + ((γi - ε) ^ 2 - γi ^ 2) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add j i hne_ji]
    · simp only [hf'_sum, ↓reduceIte, hne_ji, hne_ji.symm, zero_sub, sub_zero, mul_neg, mul_one,
        γj, γi]
      ring
    · intro x hx
      simp only [hf'_sum, hx.1, hx.2, ↓reduceIte, sub_self, mul_zero, add_zero, sub_self]
  have hlt_diff : ((γj + ε) ^ 2 - γj ^ 2) + ((γi - ε) ^ 2 - γi ^ 2) < 0 := by
    have hsurp' : γj < γi := hsurp
    dsimp only [gap] at hε_le_gap
    nlinarith
  linarith

/-- Every balanced flow in `N(p)` is a maximum flow in `N(p)` ([Vazirani2007], Section 5.7,
p. 112). -/
theorem IsBalancedFlow.isMaxEqualityFlow {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) {f : G → I → ℝ} (hbal : M.IsBalancedFlow p f) :
    M.IsMaxEqualityFlow p f := by
  classical
  refine ⟨hbal.1, fun f' hf' => ?_⟩
  by_contra hlt
  push Not at hlt
  have hha : ∀ g ∈ (Finset.univ : Finset G), 0 ≤ p g * M.supply g :=
    fun g _ => mul_nonneg (hp g) (M.supply_nonneg g)
  have hhb : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ M.budget i := fun i _ => M.budget_nonneg i
  let W := M.equalityNetwork p
  let F := toRealFlow f
  have hF : IsFeasibleRealFlow W .source .sink F :=
    isFeasibleRealFlow_toRealFlow hha hhb ((isEqualityFlow_iff_isBipFlow M p f).1 hbal.1)
  have hreach_sink : Relation.ReflTransGen (Residual W F) .source .sink := by
    by_contra hno
    let X : Finset (FlowVertex I G) :=
      Finset.univ.filter (Relation.ReflTransGen (Residual W F) .source)
    have hsX : FlowVertex.source ∈ X := Finset.mem_filter.2 ⟨Finset.mem_univ _, .refl⟩
    have htX : FlowVertex.sink ∉ X := fun h => hno (Finset.mem_filter.1 h).2
    have hsat : ∀ u ∈ X, ∀ v ∈ Finset.univ \ X, F (u, v) = W u v ∧ F (v, u) = 0 := by
      intro u hu v hv
      have hnr : ¬ Residual W F u v := fun h =>
        (Finset.mem_sdiff.1 hv).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (Finset.mem_filter.1 hu).2.tail h⟩)
      simp only [Residual, not_or, not_lt] at hnr
      exact ⟨le_antisymm (hF.2.1 u v) hnr.1, le_antisymm hnr.2 (hF.1 v u)⟩
    have hvalX : realNetOut F .source = cutWeight W X := by
      rw [hF.realNetOut_eq_sub hsX htX,
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => (hsat u hu v hv).1,
        Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => (hsat u hu v hv).2,
        sub_zero, ← cutWeight]
    have hF' : IsFeasibleRealFlow W .source .sink (toRealFlow f') :=
      isFeasibleRealFlow_toRealFlow hha hhb ((isEqualityFlow_iff_isBipFlow M p f').1 hf')
    have hle := hF'.realNetOut_le_cutWeight hsX htX
    rw [realNetOut_toRealFlow, ← hvalX, realNetOut_toRealFlow] at hle
    exact (not_le_of_gt hlt) hle
  obtain ⟨path, hnodup, hhead, hlast, harcs⟩ := exists_nodup_list_of_reflTransGen hreach_sink
  have hsink_in : ∀ u, Residual W F u .sink →
      ∃ i, u = .buyer i ∧ F (.buyer i, .sink) < M.budget i := by
    intro u hu
    cases u with
    | buyer i =>
      rcases hu with hfwd | hbwd
      · exact ⟨i, rfl, by simpa [F, W, equalityNetwork, toRealFlow, bipCap] using hfwd⟩
      · simp [F, toRealFlow] at hbwd
    | source => rcases hu with h | h <;> simp [F, W, equalityNetwork, toRealFlow, bipCap] at h
    | good g => rcases hu with h | h <;> simp [F, W, equalityNetwork, toRealFlow, bipCap] at h
    | sink => rcases hu with h | h <;> simp [F, W, equalityNetwork, toRealFlow, bipCap] at h
  let d : FlowVertex I G × FlowVertex I G → ℝ := fun e =>
    if e ∈ pathArcs path ∧ F e < W e.1 e.2 then 1
    else if (e.2, e.1) ∈ pathArcs path ∧ ¬ (F (e.2, e.1) < W e.2 e.1) then -1
    else 0
  have hd_antisym (u v : FlowVertex I G) : d (u, v) - d (v, u) =
      (if (u, v) ∈ pathArcs path then (1 : ℝ) else 0) -
        (if (v, u) ∈ pathArcs path then 1 else 0) := by
    by_cases huv : (u, v) ∈ pathArcs path
    · have hvu : (v, u) ∉ pathArcs path := not_swap_mem_pathArcs hnodup huv
      by_cases hfwd : F (u, v) < W u v
      · simp [d, huv, hvu, hfwd]
      · simp [d, huv, hvu, hfwd, not_lt.1 hfwd]
    · by_cases hvu : (v, u) ∈ pathArcs path
      · by_cases hfwd : F (v, u) < W v u
        · simp [d, huv, hvu, hfwd]
        · simp [d, huv, hvu, hfwd]
      · simp [d, huv, hvu]
  have hd_net (v : FlowVertex I G) : realNetOut d v =
      (if v = .source then (1 : ℝ) else 0) - (if v = .sink then 1 else 0) := by
    rw [realNetOut, ← Finset.sum_sub_distrib]
    simp_rw [hd_antisym]
    have hZ := sum_pathArcs_sign hnodup hhead hlast v
    have hR : (∑ w : FlowVertex I G,
        ((if (v, w) ∈ pathArcs path then (1 : ℝ) else 0) -
          (if (w, v) ∈ pathArcs path then 1 else 0))) =
        ((∑ w : FlowVertex I G,
          ((if (v, w) ∈ pathArcs path then (1 : ℤ) else 0) -
            (if (w, v) ∈ pathArcs path then 1 else 0)) : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs <;> simp
    rw [hR, hZ]
    by_cases hs : v = .source
    · subst hs; simp
    · by_cases ht : v = .sink
      · subst ht; simp
      · have hs' : FlowVertex.source ≠ v := Ne.symm hs
        have ht' : FlowVertex.sink ≠ v := Ne.symm ht
        simp [hs, ht, hs', ht']
  let margin : FlowVertex I G × FlowVertex I G → ℝ := fun e =>
    if F e < W e.1 e.2 then W e.1 e.2 - F e else F (e.2, e.1)
  have hmargin_pos : ∀ e ∈ pathArcs path, 0 < margin e := by
    intro e he
    dsimp only [margin]
    split_ifs with hfwd
    · exact sub_pos.2 hfwd
    · exact (harcs e he).resolve_left hfwd
  have harcs_ne : (pathArcs path).toFinset.Nonempty := by
    have hne := pathArcs_ne_nil_of_head?_ne_getLast? (by simp : FlowVertex.source ≠ .sink)
      hhead hlast
    rcases hpa : pathArcs path with _ | ⟨e₀, _⟩
    · exact absurd hpa hne
    · exact ⟨e₀, List.mem_toFinset.2 List.mem_cons_self⟩
  set ε : ℝ := (pathArcs path).toFinset.inf' harcs_ne margin
  have hε_pos : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro e he
    exact hmargin_pos e (List.mem_toFinset.1 he)
  have hε_le : ∀ e ∈ pathArcs path, ε ≤ margin e := fun e he =>
    Finset.inf'_le margin (List.mem_toFinset.2 he)
  let F' : FlowVertex I G × FlowVertex I G → ℝ := F + ε • d
  have hF'_feas : IsFeasibleRealFlow W .source .sink F' := by
    refine ⟨fun u v => ?_, fun u v => ?_, fun v hvs hvt => ?_⟩
    · simp only [F', Pi.add_apply, Pi.smul_apply, smul_eq_mul, d]
      split_ifs with h1 h2
      · linarith [hF.1 u v, hε_pos]
      · have hm : ε ≤ F (u, v) := by
          have := hε_le (v, u) h2.1
          simpa [margin, h2.2] using this
        linarith
      · linarith [hF.1 u v]
    · simp only [F', Pi.add_apply, Pi.smul_apply, smul_eq_mul, d]
      split_ifs with h1 h2
      · have hm : ε ≤ W u v - F (u, v) := by
          have := hε_le (u, v) h1.1
          simpa [margin, h1.2] using this
        linarith
      · linarith [hF.2.1 u v, hε_pos]
      · linarith [hF.2.1 u v]
    · rw [eq_comm, ← sub_eq_zero, ← realNetOut]
      simp [F', realNetOut_add, realNetOut_smul, hd_net, hF.realNetOut_eq_zero hvs hvt, hvs, hvt]
  obtain ⟨u₀, hu₀_mem⟩ := exists_mem_pathArcs_snd_eq (List.mem_of_getLast? hlast)
    (by rw [hhead]; simp)
  obtain ⟨i₀, rfl, hi₀_lt⟩ := hsink_in u₀ (harcs (u₀, .sink) hu₀_mem)
  have hno_sink_fst : ∀ v, (FlowVertex.sink, v) ∉ pathArcs path := by
    intro v hv
    have haux : ∀ L : List (FlowVertex I G), L.Nodup → L.getLast? = some .sink →
        (FlowVertex.sink, v) ∉ pathArcs L := by
      intro L
      induction L with
      | nil => intro _ _ h; simp [pathArcs] at h
      | cons a rest ih =>
        intro hnd hl hmem
        cases rest with
        | nil => simp [pathArcs] at hmem
        | cons b tl =>
          rw [pathArcs_cons_cons, List.mem_cons] at hmem
          rw [List.nodup_cons] at hnd
          have hl' : (b :: tl).getLast? = some .sink := by simpa using hl
          rcases hmem with hhead_eq | htl
          · injection hhead_eq with ha _
            subst ha
            exact hnd.1 (List.mem_of_getLast? hl')
          · exact ih hnd.2 hl' htl
    exact haux path hnodup hlast hv
  have huniq_sink_in : ∀ i : I, (.buyer i, FlowVertex.sink) ∈ pathArcs path → i = i₀ := by
    intro i hi
    have haux : ∀ L : List (FlowVertex I G), L.Nodup →
        ∀ a b, (a, FlowVertex.sink) ∈ pathArcs L → (b, FlowVertex.sink) ∈ pathArcs L → a = b := by
      intro L
      induction L with
      | nil => intro _ _ _ h; simp [pathArcs] at h
      | cons x rest ih =>
        intro hnd a b ha hb
        cases rest with
        | nil => simp [pathArcs] at ha
        | cons y tl =>
          rw [pathArcs_cons_cons, List.mem_cons] at ha hb
          rw [List.nodup_cons] at hnd
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · injection ha with h1 _; injection hb with h2 _; exact h1.trans h2.symm
          · injection ha with _ hy; subst hy
            exfalso
            cases tl with
            | nil => simp [pathArcs] at hb
            | cons z zs =>
              rw [pathArcs_cons_cons, List.mem_cons] at hb
              rcases hb with hb | hb
              · injection hb with _ hz
                exact (List.nodup_cons.1 hnd.2).1 (hz ▸ List.mem_cons_self)
              · exact (List.nodup_cons.1 hnd.2).1 (snd_mem_of_mem_pathArcs hb)
          · injection hb with _ hy; subst hy
            exfalso
            cases tl with
            | nil => simp [pathArcs] at ha
            | cons z zs =>
              rw [pathArcs_cons_cons, List.mem_cons] at ha
              rcases ha with ha | ha
              · injection ha with _ hz
                exact (List.nodup_cons.1 hnd.2).1 (hz ▸ List.mem_cons_self)
              · exact (List.nodup_cons.1 hnd.2).1 (snd_mem_of_mem_pathArcs ha)
          · exact ih hnd.2 a b ha hb
    have heq := haux path hnodup (.buyer i) (.buyer i₀) hi hu₀_mem
    injection heq
  obtain ⟨hf2_bip, -, hsink2, -⟩ := isBipFlow_ofRealFlow hF'_feas
  set f₂ := ofRealFlow F'
  have hf2 : M.IsEqualityFlow p f₂ := (isEqualityFlow_iff_isBipFlow M p f₂).2 hf2_bip
  have hsurp2 : ∀ i : I, M.surplus f₂ i = M.surplus f i - if i = i₀ then ε else 0 := by
    intro i
    have hsi : ∑ g : G, f₂ g i = F' (.buyer i, .sink) := (hsink2 i).symm
    have hFi : F (.buyer i, .sink) = ∑ g : G, f g i := rfl
    simp only [surplus, hsi, F', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFi]
    by_cases hi : i = i₀
    · subst hi
      have hfwd : F (.buyer i, .sink) < W (.buyer i) .sink := by
        simpa [W, equalityNetwork, bipCap] using hi₀_lt
      simp only [d, hu₀_mem, hfwd, and_self, ↓reduceIte, mul_one]
      ring
    · have hnot : (FlowVertex.buyer i, FlowVertex.sink) ∉ pathArcs path :=
        fun h => hi (huniq_sink_in i h)
      simp only [d, hnot, false_and, hno_sink_fst, ↓reduceIte, mul_zero, add_zero, hi, sub_zero]
  have hε_le_surp : ε ≤ M.surplus f i₀ := by
    have hfwd : F (.buyer i₀, .sink) < W (.buyer i₀) .sink := by
      simpa [W, equalityNetwork, bipCap] using hi₀_lt
    have hm := hε_le (.buyer i₀, .sink) hu₀_mem
    simp only [margin, hfwd, ↓reduceIte] at hm
    simpa [W, equalityNetwork, bipCap, F, toRealFlow, surplus] using hm
  have hsq_lt : M.surplusSqNorm f₂ < M.surplusSqNorm f := by
    have hdiff : M.surplusSqNorm f₂ - M.surplusSqNorm f =
        (M.surplus f i₀ - ε) ^ 2 - (M.surplus f i₀) ^ 2 := by
      simp only [surplusSqNorm, ← Finset.sum_sub_distrib, hsurp2]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
      simp
    have hpos_surp : 0 < M.surplus f i₀ := sub_pos.2 (by simpa [F, toRealFlow] using hi₀_lt)
    nlinarith
  exact not_lt_of_ge (hbal.2 f₂ hf2) hsq_lt

/-- **Abel summation lemma** for majorization: if `γ, γ' : I → ℝ` with `0 ≤ γ i`, and every strict
upper-tail set `{i | c ≤ γ i}` (`0 < c`) satisfies `∑_{c ≤ γ i} γ i ≤ ∑_{c ≤ γ i} γ' i`, then
`∑ i, γ i * (γ' i - γ i) ≥ 0`, hence `∑ i, (γ i) ^ 2 ≤ ∑ i, (γ' i) ^ 2`. -/
private theorem sum_sq_le_of_upper_tail_le {γ γ' : I → ℝ} (hγ_nn : ∀ i, 0 ≤ γ i)
    (htail : ∀ c : ℝ, 0 < c →
      ∑ i ∈ Finset.univ.filter (fun i => c ≤ γ i), γ i ≤
        ∑ i ∈ Finset.univ.filter (fun i => c ≤ γ i), γ' i) :
    ∑ i : I, (γ i) ^ 2 ≤ ∑ i : I, (γ' i) ^ 2 := by
  classical
  let posVals : Finset ℝ := (Finset.univ.image γ).filter (0 < ·)
  let vs : List ℝ := posVals.sort (· ≤ ·)
  have hvs_sorted : vs.Pairwise (· < ·) := by
    have hle : vs.Pairwise (· ≤ ·) := Finset.pairwise_sort posVals (· ≤ ·)
    have hnd : vs.Nodup := Finset.sort_nodup posVals (· ≤ ·)
    refine List.pairwise_iff_getElem.2 fun a b ha hb hab => ?_
    exact lt_of_le_of_ne (List.pairwise_iff_getElem.1 hle a b ha hb hab)
      fun heq => hab.ne (congrArg Fin.val
        ((List.nodup_iff_injective_getElem.1 hnd) (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) heq))
  have hvs_pos : ∀ v ∈ vs, 0 < v := fun v hv =>
    (Finset.mem_filter.1 ((Finset.mem_sort (· ≤ ·)).1 hv)).2
  have hrep : ∀ (L : List ℝ) (base : ℝ), 0 ≤ base → L.Pairwise (· < ·) →
      (∀ v ∈ L, base < v) → ∀ x : ℝ, (x = base ∨ x ∈ L) →
      x - base =
        (List.zipWith (fun prev cur => (cur - prev) * if cur ≤ x then (1 : ℝ) else 0)
          (base :: L) L).sum := by
    intro L
    induction L with
    | nil =>
      intro base _ _ _ x hx
      rcases hx with rfl | h
      · simp
      · simp at h
    | cons v tl ih =>
      intro base hbase hpair hgt x hx
      rw [List.pairwise_cons] at hpair
      have hbv : base < v := hgt v List.mem_cons_self
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rcases hx with hxb | hx
      · have hzero : ∀ (M : List ℝ) (p : ℝ), (∀ u ∈ M, base < u) →
            (List.zipWith (fun prev cur => (cur - prev) * if cur ≤ base then (1 : ℝ) else 0)
              (p :: M) M).sum = 0 := by
          intro M
          induction M with
          | nil => intro _ _; simp
          | cons u us ihM =>
            intro p hu
            simp only [List.zipWith_cons_cons, List.sum_cons]
            rw [ite_eq_right_iff.2 fun hle => absurd hle (not_le.2 (hu u List.mem_cons_self)),
              mul_zero, zero_add]
            exact ihM u fun u' hu' => hu u' (List.mem_cons_of_mem _ hu')
        rw [hxb, ite_eq_right_iff.2 fun hle => absurd hle (not_le.2 hbv), mul_zero, zero_add,
          hzero tl v fun u hu => hgt u (List.mem_cons_of_mem _ hu), sub_self]
      · rcases List.mem_cons.1 hx with hxv | htl
        · rw [hxv, ite_eq_left_iff.2 fun h => absurd le_rfl h, mul_one]
          have hrest := ih v (by linarith) hpair.2 hpair.1 v (Or.inl rfl)
          linarith
        · have hvx : v < x := hpair.1 x htl
          rw [ite_eq_left_iff.2 fun h => absurd hvx.le h, mul_one]
          have hrest := ih v (by linarith) hpair.2 hpair.1 x (Or.inr htl)
          linarith
  have hinner_nonneg : 0 ≤ ∑ i : I, γ i * (γ' i - γ i) := by
    have hterm (i : I) : γ i =
        (List.zipWith (fun prev cur => (cur - prev) * if cur ≤ γ i then (1 : ℝ) else 0)
          (0 :: vs) vs).sum := by
      have hx : γ i = 0 ∨ γ i ∈ vs := by
        rcases (hγ_nn i).eq_or_lt with h0 | hpos
        · exact Or.inl h0.symm
        · exact Or.inr ((Finset.mem_sort (· ≤ ·)).2
            (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem γ (Finset.mem_univ i), hpos⟩))
      simpa using hrep vs 0 le_rfl hvs_sorted hvs_pos (γ i) hx
    have hsum_zip : ∀ (A B : List ℝ),
        (∀ p ∈ List.zip A B, p.1 ≤ p.2 ∧ 0 < p.2) →
        0 ≤ ∑ i : I,
          (List.zipWith (fun prev cur => (cur - prev) * if cur ≤ γ i then (1 : ℝ) else 0)
            A B).sum * (γ' i - γ i) := by
      intro A
      induction A with
      | nil => intro B _; simp
      | cons a as ih =>
        intro B hAB
        cases B with
        | nil => simp
        | cons b bs =>
          simp only [List.zipWith_cons_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
          have hab := hAB (a, b) (by simp)
          have hhead : 0 ≤ ∑ i : I,
              ((b - a) * if b ≤ γ i then (1 : ℝ) else 0) * (γ' i - γ i) := by
            have hfac : ∑ i : I,
                ((b - a) * if b ≤ γ i then (1 : ℝ) else 0) * (γ' i - γ i) =
                (b - a) * ∑ i ∈ Finset.univ.filter (fun i => b ≤ γ i), (γ' i - γ i) := by
              rw [Finset.sum_filter, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs <;> ring
            rw [hfac]
            refine mul_nonneg (sub_nonneg.2 hab.1) ?_
            rw [Finset.sum_sub_distrib, sub_nonneg]
            exact htail b hab.2
          have htail' := ih bs fun p hp => hAB p (by simp [hp])
          linarith
    have hzip_ok : ∀ p ∈ List.zip (0 :: vs) vs, p.1 ≤ p.2 ∧ 0 < p.2 := by
      have haux : ∀ (L : List ℝ) (base : ℝ), 0 ≤ base → L.Pairwise (· < ·) →
          (∀ v ∈ L, base < v) → ∀ p ∈ List.zip (base :: L) L, p.1 ≤ p.2 ∧ 0 < p.2 := by
        intro L
        induction L with
        | nil => intro _ _ _ _ p hp; simp at hp
        | cons v tl ih =>
          intro base hbase hpair hgt p hp
          rw [List.pairwise_cons] at hpair
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨(hgt v List.mem_cons_self).le, by linarith [hgt v List.mem_cons_self]⟩
          · exact ih v (by linarith [hgt v List.mem_cons_self]) hpair.2 hpair.1 p hp
      exact haux vs 0 le_rfl hvs_sorted hvs_pos
    simpa only [← hterm] using hsum_zip (0 :: vs) vs hzip_ok
  have hsq : (∑ i : I, (γ' i) ^ 2) - ∑ i : I, (γ i) ^ 2 =
      2 * (∑ i : I, γ i * (γ' i - γ i)) + ∑ i : I, (γ' i - γ i) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq_nn : 0 ≤ ∑ i : I, (γ' i - γ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- **Theorem 5.5** ([Vazirani2007], Section 5.7, pp. 112–113): a maximum equality money flow `f` in
`N(p)` is balanced if and only if it satisfies Property 1 (`M.SatisfiesPropertyOne p f`). -/
theorem isBalancedFlow_iff_satisfiesPropertyOne {M : LinearFisherMarket I G} {p : G → ℝ}
    {f : G → I → ℝ} (hfmax : M.IsMaxEqualityFlow p f) :
    M.IsBalancedFlow p f ↔ M.SatisfiesPropertyOne p f := by
  classical
  constructor
  · intro hbal j i hsurp hreach
    obtain ⟨f', hf', hlt⟩ := exists_shift_along_resChain
      ((isEqualityFlow_iff_isBipFlow M p f).1 hbal.1) hreach hsurp
    have hle := hbal.2 f' ((isEqualityFlow_iff_isBipFlow M p f').2 hf')
    exact not_lt_of_ge hle hlt
  · intro hprop
    refine ⟨hfmax.1, fun f' hf' => ?_⟩
    refine sum_sq_le_of_upper_tail_le (fun i => sub_nonneg.2 (hfmax.1.2.2.2 i)) fun c hc => ?_
    let U : Finset I := Finset.univ.filter fun i => c ≤ M.surplus f i
    let G' : Finset G := Finset.univ.filter fun g => ∃ i ∈ U, M.IsEqualityEdge p i g
    have hno_leak : ∀ g ∈ G', ∀ j ∉ U, f g j = 0 := by
      intro g hg j hj
      obtain ⟨i, hiU, hE⟩ := (Finset.mem_filter.1 hg).2
      refine le_antisymm (not_lt.1 fun hpos => ?_) (hfmax.1.1 g j)
      have hj_lt : M.surplus f j < M.surplus f i := by
        have h1 : M.surplus f j < c :=
          not_le.1 fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        have h2 : c ≤ M.surplus f i := (Finset.mem_filter.1 hiU).2
        linarith
      exact hprop j i hj_lt (Relation.ReflTransGen.single ⟨g, hpos, hE⟩)
    have hsat : ∀ g ∈ G', ∑ b : I, f g b = p g * M.supply g := by
      intro g hg
      refine le_antisymm (hfmax.1.2.2.1 g) (not_lt.1 fun hslack => ?_)
      obtain ⟨i, hiU, hE⟩ := (Finset.mem_filter.1 hg).2
      have hsi_pos : 0 < M.surplus f i := hc.trans_le (Finset.mem_filter.1 hiU).2
      set δ : ℝ := min (p g * M.supply g - ∑ b : I, f g b) (M.surplus f i)
      have hδ_pos : 0 < δ := lt_min (sub_pos.2 hslack) hsi_pos
      let f'' : G → I → ℝ := fun g₁ i₁ => f g₁ i₁ + if g₁ = g ∧ i₁ = i then δ else 0
      have hf'' : M.IsEqualityFlow p f'' := by
        refine ⟨fun g₁ i₁ => by
            dsimp only [f'']; split_ifs <;> linarith [hfmax.1.1 g₁ i₁, hδ_pos],
          fun g₁ i₁ hpos => ?_, fun g₁ => ?_, fun i₁ => ?_⟩
        · dsimp only [f''] at hpos
          split_ifs at hpos with hgi
          · rcases hgi with ⟨rfl, rfl⟩; exact hE
          · exact hfmax.1.2.1 g₁ i₁ (by linarith)
        · by_cases hgg : g₁ = g
          · subst hgg
            simp only [f'', true_and, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
            have hle := min_le_left (p g₁ * M.supply g₁ - ∑ b : I, f g₁ b) (M.surplus f i)
            dsimp only [δ]
            linarith
          · simp only [f'', hgg, false_and, ↓reduceIte, add_zero]
            exact hfmax.1.2.2.1 g₁
        · by_cases hii : i₁ = i
          · subst hii
            simp only [f'', and_true, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
            have hle : δ ≤ M.surplus f i₁ :=
              min_le_right (p g * M.supply g - ∑ b : I, f g b) (M.surplus f i₁)
            unfold surplus at hle
            linarith
          · simp only [f'', hii, and_false, ↓reduceIte, add_zero]
            exact hfmax.1.2.2.2 i₁
      have hval_inc : flowValue f'' = flowValue f + δ := by
        simp only [flowValue, f'', Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single g (fun g₁ _ hg₁ => by simp [hg₁]) (by simp)]
        simp
      linarith [hfmax.2 f'' hf'']
    have hspent_le : ∑ i ∈ U, ∑ g : G, f' g i ≤ ∑ i ∈ U, ∑ g : G, f g i := by
      calc
        ∑ i ∈ U, ∑ g : G, f' g i
          = ∑ i ∈ U, ∑ g ∈ G', f' g i := by
              refine Finset.sum_congr rfl fun i hiU => ?_
              symm
              refine Finset.sum_subset (Finset.subset_univ G') fun g _ hgG' => ?_
              refine le_antisymm (not_lt.1 fun hpos => hgG' ?_) (hf'.1 g i)
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hiU, hf'.2.1 g i hpos⟩
        _ = ∑ g ∈ G', ∑ i ∈ U, f' g i := Finset.sum_comm
        _ ≤ ∑ g ∈ G', ∑ i : I, f' g i :=
              Finset.sum_le_sum fun g _ => Finset.sum_le_univ_sum_of_nonneg fun i => hf'.1 g i
        _ ≤ ∑ g ∈ G', p g * M.supply g := Finset.sum_le_sum fun g _ => hf'.2.2.1 g
        _ = ∑ g ∈ G', ∑ i : I, f g i := Finset.sum_congr rfl fun g hg => (hsat g hg).symm
        _ = ∑ g ∈ G', ∑ i ∈ U, f g i := by
              refine Finset.sum_congr rfl fun g hg => ?_
              symm
              exact Finset.sum_subset (Finset.subset_univ U) fun j _ hjU => hno_leak g hg j hjU
        _ = ∑ i ∈ U, ∑ g ∈ G', f g i := Finset.sum_comm
        _ ≤ ∑ i ∈ U, ∑ g : G, f g i :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_univ_sum_of_nonneg fun g => hfmax.1.1 g i
    change ∑ i ∈ U, M.surplus f i ≤ ∑ i ∈ U, M.surplus f' i
    simp only [surplus, Finset.sum_sub_distrib]
    linarith

end BalancedFlows

/-! ### Section 5.7.1: Divide-and-conquer balanced-flow algorithm (`Theorem 5.8`) -/

section MaxFlowOracle

/-- Oracle query signature for single maximum-flow computations on bipartite networks over
`FlowVertex I G`. Used with `Cslib.FreeM` to count exact max-flow oracle calls in
**Theorem 5.8** ([Vazirani2007], Section 5.7.1, p. 115) and **Lemma 5.11** ([Vazirani2007],
Section 5.9, p. 118). -/
inductive MaxFlowQuery (I G : Type u) : Type u → Type u where
  /-- Query a maximum `source`–`sink` flow on capacity matrix `W`. -/
  | maxFlow (W : FlowVertex I G → FlowVertex I G → ℝ) :
      MaxFlowQuery I G (FlowVertex I G × FlowVertex I G → ℝ)

/-- Validity predicate for a `MaxFlowQuery` oracle: on every nonnegative capacity matrix `W`,
`oracle (.maxFlow W)` returns a feasible maximum `source`–`sink` flow. -/
@[expose] def IsValidMaxFlowOracle {I G : Type u} [Fintype I] [Fintype G]
    (oracle : {ι : Type u} → MaxFlowQuery I G ι → ι) : Prop :=
  ∀ W : FlowVertex I G → FlowVertex I G → ℝ, (∀ u v, 0 ≤ W u v) →
    IsFeasibleRealFlow W .source .sink (oracle (.maxFlow W)) ∧
      IsMaxRealFlow W .source .sink (realNetOut (oracle (.maxFlow W)) .source)

/-- Canonical valid `MaxFlowQuery` oracle backed by `exists_isMaxRealFlow`. -/
noncomputable def canonicalMaxFlowOracle {I G : Type u} [Fintype I] [Fintype G] :
    {ι : Type u} → MaxFlowQuery I G ι → ι
  | _, .maxFlow W =>
    open scoped Classical in
    if h : ∀ u v, 0 ≤ W u v then (exists_isMaxRealFlow h .source .sink).choose else 0

theorem isValidMaxFlowOracle_canonical {I G : Type u} [Fintype I] [Fintype G] :
    IsValidMaxFlowOracle (canonicalMaxFlowOracle (I := I) (G := G)) := by
  intro W hW
  change IsFeasibleRealFlow W .source .sink
      (open scoped Classical in
        if h : ∀ u v, 0 ≤ W u v then (exists_isMaxRealFlow h .source .sink).choose else 0) ∧
    IsMaxRealFlow W .source .sink (realNetOut
      (open scoped Classical in
        if h : ∀ u v, 0 ≤ W u v then (exists_isMaxRealFlow h .source .sink).choose else 0)
      .source)
  have hd : (open scoped Classical in
      if h : ∀ u v, 0 ≤ W u v then (exists_isMaxRealFlow h .source .sink).choose else 0) =
      (exists_isMaxRealFlow hW .source .sink).choose := by
    split_ifs
    rfl
  rw [hd]
  exact (exists_isMaxRealFlow hW .source .sink).choose_spec

section ResidualCuts

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Outgoing residual arcs of a feasible flow `F` on `bipCap A B a b E` from `.good g` go only to
`.source` or to `.buyer i` along an active bipartite edge `g ∈ A ∧ i ∈ B ∧ E g i`. -/
private theorem residual_bipCap_good_cases {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow (bipCap A B a b E) .source .sink F)
    {g : G} {w : FlowVertex I G} (hres : Residual (bipCap A B a b E) F (.good g) w) :
    w = .source ∨ ∃ i, w = .buyer i ∧ g ∈ A ∧ i ∈ B ∧ E g i := by
  have hzero {u v : FlowVertex I G} (hW : bipCap A B a b E u v = 0) : F (u, v) = 0 :=
    le_antisymm (hW ▸ hF.2.1 u v) (hF.1 u v)
  cases w with
  | source => exact Or.inl rfl
  | sink =>
    rcases hres with h1 | h2
    · simp [bipCap] at h1; linarith [hF.1 (.good g) .sink]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E .sink (.good g) = 0)]
  | good g' =>
    rcases hres with h1 | h2
    · simp [bipCap] at h1; linarith [hF.1 (.good g) (.good g')]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E (.good g') (.good g) = 0)]
  | buyer i =>
    refine Or.inr ⟨i, rfl, ?_⟩
    rcases hres with h1 | h2
    · by_contra hnot
      have h0 : bipCap A B a b E (.good g) (.buyer i) = 0 := by simp [bipCap, hnot]
      linarith [hF.1 (.good g) (.buyer i)]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E (.buyer i) (.good g) = 0)]

/-- Outgoing residual arcs of a feasible flow `F` on `bipCap A B a b E` from `.buyer i` go only
forward to `.sink` (with `i ∈ B` and `F (.buyer i, .sink) < b i`) or backward to `.good g`
(with `0 < ofRealFlow F g i`). -/
private theorem residual_bipCap_buyer_cases {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow (bipCap A B a b E) .source .sink F)
    {i : I} {w : FlowVertex I G} (hres : Residual (bipCap A B a b E) F (.buyer i) w) :
    (w = .sink ∧ i ∈ B ∧ F (.buyer i, .sink) < b i) ∨
      ∃ g, w = .good g ∧ 0 < ofRealFlow F g i := by
  have hzero {u v : FlowVertex I G} (hW : bipCap A B a b E u v = 0) : F (u, v) = 0 :=
    le_antisymm (hW ▸ hF.2.1 u v) (hF.1 u v)
  cases w with
  | source =>
    rcases hres with h1 | h2
    · simp [bipCap] at h1; linarith [hF.1 (.buyer i) .source]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E .source (.buyer i) = 0)]
  | buyer i' =>
    rcases hres with h1 | h2
    · simp [bipCap] at h1; linarith [hF.1 (.buyer i) (.buyer i')]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E (.buyer i') (.buyer i) = 0)]
  | sink =>
    refine Or.inl ⟨rfl, ?_⟩
    rcases hres with h1 | h2
    · by_cases hiB : i ∈ B
      · exact ⟨hiB, by simpa [bipCap, hiB] using h1⟩
      · simp [bipCap, hiB] at h1; linarith [hF.1 (.buyer i) .sink]
    · linarith [hzero (by simp [bipCap] : bipCap A B a b E .sink (.buyer i) = 0)]
  | good g =>
    refine Or.inr ⟨g, rfl, ?_⟩
    rcases hres with h1 | h2
    · simp [bipCap] at h1; linarith [hF.1 (.buyer i) (.good g)]
    · exact h2

omit [Fintype I] [Fintype G] in
/-- Every active bipartite edge `(g, i)` has positive forward residual capacity in
`bipCap A B a b E` for any feasible flow `F` (because `bigM A B a b` strictly exceeds `a g`). -/
private theorem residual_bipCap_good_buyer_of_edge {A : Finset G} {B : Finset I}
    {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g ∈ A, 0 ≤ a g) (hb : ∀ i ∈ B, 0 ≤ b i)
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hf : IsBipFlow A B a b E (ofRealFlow F))
    {g : G} (hg : g ∈ A) {i : I} (hi : i ∈ B) (hE : E g i) :
    Residual (bipCap A B a b E) F (.good g) (.buyer i) := by
  left
  simp only [bipCap, hg, hi, hE, and_self, ↓reduceIte]
  have hle1 : ofRealFlow F g i ≤ ∑ i' ∈ B, ofRealFlow F g i' :=
    Finset.single_le_sum (fun i' _ => hf.1 g i') hi
  have hle2 : ∑ i' ∈ B, ofRealFlow F g i' ≤ a g := hf.2.2.1 g hg
  have hle3 : a g ≤ ∑ g' ∈ A, a g' := Finset.single_le_sum ha hg
  have hbn : 0 ≤ ∑ i' ∈ B, b i' := Finset.sum_nonneg hb
  change F (.good g, .buyer i) ≤ _ at hle1
  unfold bigM
  linarith

/-- The **unique maximal `s`–`t` minimum cut** induced by a maximum flow `F` on `W`: all vertices
that cannot reach `.sink` in the residual graph of `F` ([Vazirani2007], Section 5.7.1, p. 113). -/
private noncomputable def maxMinCut (W : FlowVertex I G → FlowVertex I G → ℝ)
    (F : FlowVertex I G × FlowVertex I G → ℝ) : Finset (FlowVertex I G) :=
  open scoped Classical in
  Finset.univ.filter fun v => ¬ Relation.ReflTransGen (Residual W F) v .sink

private theorem mem_maxMinCut {W : FlowVertex I G → FlowVertex I G → ℝ}
    {F : FlowVertex I G × FlowVertex I G → ℝ} {v : FlowVertex I G} :
    v ∈ maxMinCut W F ↔ ¬ Relation.ReflTransGen (Residual W F) v .sink := by
  classical
  simp [maxMinCut]

private theorem source_mem_maxMinCut {W : FlowVertex I G → FlowVertex I G → ℝ}
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow W .source .sink F)
    (hFmax : IsMaxRealFlow W .source .sink (realNetOut F .source)) :
    FlowVertex.source ∈ maxMinCut W F :=
  mem_maxMinCut.2 (not_resReachable_of_isMaxRealFlow hF hFmax (by simp))

private theorem sink_notMem_maxMinCut (W : FlowVertex I G → FlowVertex I G → ℝ)
    (F : FlowVertex I G × FlowVertex I G → ℝ) :
    FlowVertex.sink ∉ maxMinCut W F := by
  rw [mem_maxMinCut]
  exact fun h => h .refl

private theorem sat_of_maxMinCut {W : FlowVertex I G → FlowVertex I G → ℝ}
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow W .source .sink F) {u v : FlowVertex I G}
    (hu : u ∈ maxMinCut W F) (hv : v ∉ maxMinCut W F) :
    F (u, v) = W u v ∧ F (v, u) = 0 := by
  rw [mem_maxMinCut] at hu hv
  push Not at hv
  have hnr : ¬ Residual W F u v := fun h => hu (Relation.ReflTransGen.head h hv)
  simp only [Residual, not_or, not_lt] at hnr
  exact ⟨le_antisymm (hF.2.1 u v) hnr.1, le_antisymm hnr.2 (hF.1 v u)⟩

private theorem cutWeight_maxMinCut [DecidableEq I] [DecidableEq G]
    {W : FlowVertex I G → FlowVertex I G → ℝ} (hW : ∀ u v, 0 ≤ W u v)
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow W .source .sink F)
    (hFmax : IsMaxRealFlow W .source .sink (realNetOut F .source)) :
    cutWeight W (maxMinCut W F) = minRealCutBetween W .source .sink := by
  have hs := source_mem_maxMinCut hF hFmax
  have ht := sink_notMem_maxMinCut W F
  have hval : realNetOut F .source = cutWeight W (maxMinCut W F) := by
    rw [hF.realNetOut_eq_sub hs ht,
      Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv =>
        (sat_of_maxMinCut hF hu (Finset.mem_sdiff.1 hv).2).1,
      Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv =>
        (sat_of_maxMinCut hF hu (Finset.mem_sdiff.1 hv).2).2,
      sub_zero, ← cutWeight]
  rw [← hval]
  exact IsGreatest.unique hFmax (isMaxRealFlow_minRealCutBetween hW (by simp))

private theorem subset_maxMinCut_of_minCut [DecidableEq I] [DecidableEq G]
    {W : FlowVertex I G → FlowVertex I G → ℝ} (hW : ∀ u v, 0 ≤ W u v)
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow W .source .sink F)
    (hFmax : IsMaxRealFlow W .source .sink (realNetOut F .source))
    {X : Finset (FlowVertex I G)} (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X)
    (hX : cutWeight W X = minRealCutBetween W .source .sink) :
    X ⊆ maxMinCut W F := by
  have hval_eq : realNetOut F .source = cutWeight W X := by
    rw [hX]
    exact IsGreatest.unique hFmax (isMaxRealFlow_minRealCutBetween hW (by simp))
  have hno_cross : ∀ u ∈ X, ∀ v ∉ X, ¬ Residual W F u v := by
    intro u hu v hv hres
    have hv_sd : v ∈ Finset.univ \ X := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hv⟩
    have hdiff_zero :
        (∑ x ∈ X, ∑ y ∈ Finset.univ \ X, (W x y - F (x, y))) +
        (∑ x ∈ X, ∑ y ∈ Finset.univ \ X, F (y, x)) = 0 := by
      have hsub := hF.realNetOut_eq_sub hs ht
      rw [hval_eq, cutWeight] at hsub
      simp only [Finset.sum_sub_distrib]
      linarith
    have hnn1 : 0 ≤ ∑ x ∈ X, ∑ y ∈ Finset.univ \ X, (W x y - F (x, y)) :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sub_nonneg.2 (hF.2.1 x y)
    have hnn2 : 0 ≤ ∑ x ∈ X, ∑ y ∈ Finset.univ \ X, F (y, x) :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hF.1 y x
    have hz1 : ∑ x ∈ X, ∑ y ∈ Finset.univ \ X, (W x y - F (x, y)) = 0 := by linarith
    have hz2 : ∑ x ∈ X, ∑ y ∈ Finset.univ \ X, F (y, x) = 0 := by linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sub_nonneg.2 (hF.2.1 u y)).1
      ((Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
        Finset.sum_nonneg fun y _ => sub_nonneg.2 (hF.2.1 x y)).1 hz1 u hu) v hv_sd
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hF.1 y u).1
      ((Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
        Finset.sum_nonneg fun y _ => hF.1 y x).1 hz2 u hu) v hv_sd
    rcases hres with hlt | hpos <;> linarith
  intro u hu
  rw [mem_maxMinCut]
  intro hreach
  have hnot : ∀ w, Relation.ReflTransGen (Residual W F) w .sink → w ∉ X := by
    intro w hw
    induction hw using Relation.ReflTransGen.head_induction_on with
    | refl => exact ht
    | @head a b hab _ ih =>
      intro ha
      exact hno_cross a ha b ih hab
  exact hnot u hreach hu

end ResidualCuts

end MaxFlowOracle

section DivideAndConquerBalancedFlow

variable {I G : Type u}

/-- Existence of the uniform buyer-capacity shift `X ≥ 0` making `∑ i ∈ B, max 0 (b i - X) = t`
([Vazirani2007], Section 5.7.1, p. 113). -/
private theorem exists_uniformShift {B : Finset I} {b : I → ℝ} {t : ℝ}
    (hb : ∀ i ∈ B, 0 ≤ b i) (ht0 : 0 ≤ t) (htB : t ≤ ∑ i ∈ B, b i) :
    ∃ X : ℝ, 0 ≤ X ∧ ∑ i ∈ B, max 0 (b i - X) = t := by
  let φ : ℝ → ℝ := fun x => ∑ i ∈ B, max 0 (b i - x)
  set M : ℝ := ∑ i ∈ B, b i
  have hM : 0 ≤ M := Finset.sum_nonneg hb
  have hφ_cont : ContinuousOn φ (Set.Icc 0 M) := by
    have : Continuous φ := by
      dsimp only [φ]
      fun_prop
    exact this.continuousOn
  have hφ0 : φ 0 = M := by
    dsimp only [φ, M]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [max_eq_right (hb i hi)]
  have hφM : φ M = 0 := by
    dsimp only [φ]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hle : b i ≤ M := Finset.single_le_sum hb hi
    exact max_eq_left (sub_nonpos.2 hle)
  have hmem : t ∈ Set.Icc (φ M) (φ 0) := by rw [hφM, hφ0]; exact ⟨ht0, htB⟩
  obtain ⟨X, hX_mem, hX_eq⟩ := intermediate_value_Icc' hM hφ_cont hmem
  exact ⟨X, hX_mem.1, hX_eq⟩

/-- The uniform capacity shift `X ≥ 0` reducing buyer capacities on `B` so total buyer capacity
matches `t`. -/
private noncomputable def uniformShift (B : Finset I) (b : I → ℝ) (t : ℝ) : ℝ :=
  open scoped Classical in
  if h : ∃ X : ℝ, 0 ≤ X ∧ ∑ i ∈ B, max 0 (b i - X) = t then h.choose else 0

private theorem uniformShift_spec {B : Finset I} {b : I → ℝ} {t : ℝ}
    (hb : ∀ i ∈ B, 0 ≤ b i) (ht0 : 0 ≤ t) (htB : t ≤ ∑ i ∈ B, b i) :
    0 ≤ uniformShift B b t ∧ ∑ i ∈ B, max 0 (b i - uniformShift B b t) = t := by
  classical
  have hex := exists_uniformShift hb ht0 htB
  simp only [uniformShift, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- One active bipartite subnetwork `(goods, buyers)` in the divide-and-conquer recursion of
[Vazirani2007], Section 5.7.1, pp. 113–115. -/
private structure BipPiece (I G : Type u) where
  goods : Finset G
  buyers : Finset I

/-- Validity invariant of a bipartite piece `P`: nonempty goods, every buyer in `P.buyers` has an
incident edge from `P.goods`, and `P` satisfies the Invariant (`Lemma 5.3`). -/
private def ValidPiece (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) (P : BipPiece I G) : Prop :=
  P.goods.Nonempty ∧
  (∀ i ∈ P.buyers, ∃ g ∈ P.goods, E g i) ∧
  (∀ S ⊆ P.goods, ∑ g ∈ S, a g ≤ ∑ i ∈ bipNbr P.buyers E S, b i)

/-- Reduced buyer capacity vector `b'(i) = max(0, b(i) - X)` for piece `P`. -/
private noncomputable def reducedCap (a : G → ℝ) (b : I → ℝ) (P : BipPiece I G) (i : I) : ℝ :=
  max 0 (b i - uniformShift P.buyers b (∑ g ∈ P.goods, a g))

/-- Combined goods of a piece list. -/
private def batchGoods [DecidableEq G] (ps : List (BipPiece I G)) : Finset G :=
  ps.foldr (fun P acc => P.goods ∪ acc) ∅

/-- Combined buyers of a piece list. -/
private def batchBuyers [DecidableEq I] (ps : List (BipPiece I G)) : Finset I :=
  ps.foldr (fun P acc => P.buyers ∪ acc) ∅

private theorem mem_batchGoods [DecidableEq G] {ps : List (BipPiece I G)} {g : G} :
    g ∈ batchGoods ps ↔ ∃ P ∈ ps, g ∈ P.goods := by
  induction ps with
  | nil => simp [batchGoods]
  | cons P tl ih =>
    rw [batchGoods, List.foldr_cons, Finset.mem_union]
    change g ∈ P.goods ∨ g ∈ batchGoods tl ↔ _
    rw [ih]
    simp

private theorem mem_batchBuyers [DecidableEq I] {ps : List (BipPiece I G)} {i : I} :
    i ∈ batchBuyers ps ↔ ∃ P ∈ ps, i ∈ P.buyers := by
  induction ps with
  | nil => simp [batchBuyers]
  | cons P tl ih =>
    rw [batchBuyers, List.foldr_cons, Finset.mem_union]
    change i ∈ P.buyers ∨ i ∈ batchBuyers tl ↔ _
    rw [ih]
    simp

/-- Disjoint-union reduced buyer capacity across a list of pairwise disjoint pieces. -/
private noncomputable def batchReducedCap [DecidableEq I] (a : G → ℝ) (b : I → ℝ)
    (ps : List (BipPiece I G)) (i : I) : ℝ :=
  match ps.find? (fun P => decide (i ∈ P.buyers)) with
  | some P => reducedCap a b P i
  | none => 0

private theorem batchReducedCap_nonneg [DecidableEq I] (a : G → ℝ) (b : I → ℝ)
    (ps : List (BipPiece I G)) (i : I) : 0 ≤ batchReducedCap a b ps i := by
  unfold batchReducedCap
  cases ps.find? (fun P => decide (i ∈ P.buyers)) with
  | none => exact le_rfl
  | some P => exact le_max_left _ _

/-- Pairwise vertex disjointness of a list of bipartite pieces. -/
private def PairwiseDisjointPieces (ps : List (BipPiece I G)) : Prop :=
  ps.Pairwise fun P Q => Disjoint P.goods Q.goods ∧ Disjoint P.buyers Q.buyers

private theorem PairwiseDisjointPieces.disjoint_of_ne {ps : List (BipPiece I G)}
    (hdisj : PairwiseDisjointPieces ps) {P Q : BipPiece I G}
    (hP : P ∈ ps) (hQ : Q ∈ ps) (hne : P ≠ Q) :
    Disjoint P.goods Q.goods ∧ Disjoint P.buyers Q.buyers := by
  induction ps with
  | nil => simp at hP
  | cons R tl ih =>
    rw [PairwiseDisjointPieces, List.pairwise_cons] at hdisj
    rcases List.mem_cons.1 hP with rfl | hPtl <;> rcases List.mem_cons.1 hQ with rfl | hQtl
    · exact absurd rfl hne
    · exact hdisj.1 Q hQtl
    · exact ⟨(hdisj.1 P hPtl).1.symm, (hdisj.1 P hPtl).2.symm⟩
    · exact ih hdisj.2 hPtl hQtl

private theorem batchReducedCap_eq_of_mem [DecidableEq I] {a : G → ℝ} {b : I → ℝ}
    {ps : List (BipPiece I G)} (hdisj : PairwiseDisjointPieces ps) {P : BipPiece I G}
    (hP : P ∈ ps) {i : I} (hi : i ∈ P.buyers) :
    batchReducedCap a b ps i = reducedCap a b P i := by
  unfold batchReducedCap
  induction ps with
  | nil => simp at hP
  | cons Q tl ih =>
    rw [PairwiseDisjointPieces, List.pairwise_cons] at hdisj
    rw [List.find?_cons]
    rcases List.mem_cons.1 hP with rfl | htl
    · simp [hi]
    · have hnot : i ∉ Q.buyers :=
        Finset.disjoint_right.1 (hdisj.1 P htl).2 hi
      simp only [hnot, decide_false]
      exact ih hdisj.2 htl

/-- Disjoint-union edge relation across `ps`: only intra-piece edges. -/
private def batchEdge (E : G → I → Prop) (ps : List (BipPiece I G)) (g : G) (i : I) : Prop :=
  ∃ P ∈ ps, g ∈ P.goods ∧ i ∈ P.buyers ∧ E g i

/-- Single combined reduced capacity matrix `N'_level` on `FlowVertex I G` for all disjoint pieces
at one level of the divide-and-conquer tree ([Vazirani2007], Section 5.7.1, Theorem 5.8, p. 115). -/
private noncomputable def batchCap [DecidableEq I] [DecidableEq G] (a : G → ℝ) (b : I → ℝ)
    (E : G → I → Prop) (ps : List (BipPiece I G)) : FlowVertex I G → FlowVertex I G → ℝ :=
  bipCap (batchGoods ps) (batchBuyers ps) a (batchReducedCap a b ps) (batchEdge E ps)

private theorem batchCap_nonneg [DecidableEq I] [DecidableEq G] {a : G → ℝ} {b : I → ℝ}
    {E : G → I → Prop} {ps : List (BipPiece I G)} (ha : ∀ g, 0 ≤ a g) (u v : FlowVertex I G) :
    0 ≤ batchCap a b E ps u v :=
  bipCap_nonneg (fun g _ => ha g) (fun i _ => batchReducedCap_nonneg a b ps i) u v

private theorem batchEdge_iff_of_mem_goods {E : G → I → Prop} {ps : List (BipPiece I G)}
    (hdisj : PairwiseDisjointPieces ps) {P : BipPiece I G} (hP : P ∈ ps)
    {g : G} (hg : g ∈ P.goods) (i : I) :
    batchEdge E ps g i ↔ i ∈ P.buyers ∧ E g i := by
  constructor
  · rintro ⟨Q, hQ, hgQ, hiQ, hE⟩
    have hPQ : Q = P := by
      by_contra hne
      exact Finset.disjoint_left.1 (hdisj.disjoint_of_ne hQ hP hne).1 hgQ hg
    subst hPQ
    exact ⟨hiQ, hE⟩
  · rintro ⟨hiP, hE⟩
    exact ⟨P, hP, hg, hiP, hE⟩

private theorem batchEdge_iff_of_mem_buyers {E : G → I → Prop} {ps : List (BipPiece I G)}
    (hdisj : PairwiseDisjointPieces ps) {P : BipPiece I G} (hP : P ∈ ps)
    (g : G) {i : I} (hi : i ∈ P.buyers) :
    batchEdge E ps g i ↔ g ∈ P.goods ∧ E g i := by
  constructor
  · rintro ⟨Q, hQ, hgQ, hiQ, hE⟩
    have hPQ : Q = P := by
      by_contra hne
      exact Finset.disjoint_left.1 (hdisj.disjoint_of_ne hQ hP hne).2 hiQ hi
    subst hPQ
    exact ⟨hgQ, hE⟩
  · rintro ⟨hgP, hE⟩
    exact ⟨P, hP, hgP, hi, hE⟩

variable [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- Restricting a max-flow `F` of `batchCap a b E ps` to any piece `P ∈ ps` yields a max-flow
`F_P` of the individual piece network `bipCap P.goods P.buyers a (reducedCap a b P) E`, AND the
maximal `s`–`t` min-cut `maxMinCut` restricts identically on `P.goods` and `P.buyers`. -/
private theorem batch_restrict {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g, 0 ≤ a g) {ps : List (BipPiece I G)} (hdisj : PairwiseDisjointPieces ps)
    {F : FlowVertex I G × FlowVertex I G → ℝ}
    (hF : IsFeasibleRealFlow (batchCap a b E ps) .source .sink F)
    (hFmax : IsMaxRealFlow (batchCap a b E ps) .source .sink (realNetOut F .source))
    {P : BipPiece I G} (hP : P ∈ ps) :
    let fP : G → I → ℝ := fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0
    let WP := bipCap P.goods P.buyers a (reducedCap a b P) E
    IsFeasibleRealFlow WP .source .sink (toRealFlow fP) ∧
      IsMaxRealFlow WP .source .sink (realNetOut (toRealFlow fP) .source) ∧
      cutGoods P.goods (maxMinCut (batchCap a b E ps) F) =
        cutGoods P.goods (maxMinCut WP (toRealFlow fP)) ∧
      cutBuyers P.buyers (maxMinCut (batchCap a b E ps) F) =
        cutBuyers P.buyers (maxMinCut WP (toRealFlow fP)) := by
  classical
  intro fP WP
  obtain ⟨hfAll, hFsrc, hFsink, hFval⟩ := isBipFlow_ofRealFlow hF
  have hfP_bip : IsBipFlow P.goods P.buyers a (reducedCap a b P) E fP := by
    refine ⟨fun g i => by dsimp only [fP]; split_ifs <;> linarith [hfAll.1 g i],
      fun g i hpos => ?_, fun g hgP => ?_, fun i hiP => ?_⟩
    · dsimp only [fP] at hpos
      split_ifs at hpos with hgi
      · have hEall := (hfAll.2.1 g i hpos).2.2
        exact ⟨hgi.1, hgi.2, ((batchEdge_iff_of_mem_goods hdisj hP hgi.1 i).1 hEall).2⟩
      · exact (lt_irrefl (0 : ℝ) hpos).elim
    · have hle : ∑ i ∈ P.buyers, fP g i ≤ ∑ i ∈ batchBuyers ps, ofRealFlow F g i := by
        calc
          ∑ i ∈ P.buyers, fP g i = ∑ i ∈ P.buyers, ofRealFlow F g i :=
            Finset.sum_congr rfl fun i hiP => by simp [fP, hgP, hiP]
          _ ≤ ∑ i ∈ batchBuyers ps, ofRealFlow F g i :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun i hi => mem_batchBuyers.2 ⟨P, hP, hi⟩) fun i _ _ => hfAll.1 g i
      exact hle.trans (hfAll.2.2.1 g (mem_batchGoods.2 ⟨P, hP, hgP⟩))
    · have hle : ∑ g ∈ P.goods, fP g i ≤ ∑ g ∈ batchGoods ps, ofRealFlow F g i := by
        calc
          ∑ g ∈ P.goods, fP g i = ∑ g ∈ P.goods, ofRealFlow F g i :=
            Finset.sum_congr rfl fun g hgP => by simp [fP, hgP, hiP]
          _ ≤ ∑ g ∈ batchGoods ps, ofRealFlow F g i :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun g hg => mem_batchGoods.2 ⟨P, hP, hg⟩) fun g _ _ => hfAll.1 g i
      have hcap := hfAll.2.2.2 i (mem_batchBuyers.2 ⟨P, hP, hiP⟩)
      rw [batchReducedCap_eq_of_mem hdisj hP hiP] at hcap
      exact hle.trans hcap
  have hFP_feas : IsFeasibleRealFlow WP .source .sink (toRealFlow fP) :=
    isFeasibleRealFlow_toRealFlow (fun g _ => ha g) (fun i _ => le_max_left _ _) hfP_bip
  have hFP_max : IsMaxRealFlow WP .source .sink (realNetOut (toRealFlow fP) .source) := by
    refine ⟨⟨toRealFlow fP, hFP_feas, rfl⟩, ?_⟩
    rintro _ ⟨GP, hGP, rfl⟩
    obtain ⟨hgP, -, -, hGPval⟩ := isBipFlow_ofRealFlow hGP
    let falt : G → I → ℝ := fun g i =>
      if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow GP g i else ofRealFlow F g i
    have hfalt_bip : IsBipFlow (batchGoods ps) (batchBuyers ps) a (batchReducedCap a b ps)
        (batchEdge E ps) falt := by
      refine ⟨fun g i => by
        dsimp only [falt]; split_ifs <;> first | exact hgP.1 g i | exact hfAll.1 g i,
        fun g i hpos => ?_, fun g hgA => ?_, fun i hiB => ?_⟩
      · dsimp only [falt] at hpos
        split_ifs at hpos with hgi
        · have hE := (hgP.2.1 g i hpos).2.2
          exact ⟨mem_batchGoods.2 ⟨P, hP, hgi.1⟩, mem_batchBuyers.2 ⟨P, hP, hgi.2⟩,
            ⟨P, hP, hgi.1, hgi.2, hE⟩⟩
        · exact hfAll.2.1 g i hpos
      · by_cases hgP' : g ∈ P.goods
        · have hsum : ∑ i ∈ batchBuyers ps, falt g i = ∑ i ∈ P.buyers, ofRealFlow GP g i := by
            have h1 : ∑ i ∈ batchBuyers ps, falt g i = ∑ i ∈ P.buyers, falt g i := by
              symm
              refine Finset.sum_subset (fun i hi => mem_batchBuyers.2 ⟨P, hP, hi⟩) fun i _ hiP => ?_
              simp only [falt, hgP', hiP, and_false, ↓reduceIte]
              refine le_antisymm (not_lt.1 fun hpos => hiP ?_) (hfAll.1 g i)
              exact ((batchEdge_iff_of_mem_goods hdisj hP hgP' i).1 (hfAll.2.1 g i hpos).2.2).1
            rw [h1]
            exact Finset.sum_congr rfl fun i hi => by simp [falt, hgP', hi]
          rw [hsum]
          exact hgP.2.2.1 g hgP'
        · have hsum : ∑ i ∈ batchBuyers ps, falt g i = ∑ i ∈ batchBuyers ps, ofRealFlow F g i :=
            Finset.sum_congr rfl fun i _ => by simp [falt, hgP']
          rw [hsum]
          exact hfAll.2.2.1 g hgA
      · by_cases hiP' : i ∈ P.buyers
        · have hsum : ∑ g ∈ batchGoods ps, falt g i = ∑ g ∈ P.goods, ofRealFlow GP g i := by
            have h1 : ∑ g ∈ batchGoods ps, falt g i = ∑ g ∈ P.goods, falt g i := by
              symm
              refine Finset.sum_subset (fun g hg => mem_batchGoods.2 ⟨P, hP, hg⟩) fun g _ hgP => ?_
              simp only [falt, hgP, false_and, ↓reduceIte]
              refine le_antisymm (not_lt.1 fun hpos => hgP ?_) (hfAll.1 g i)
              exact ((batchEdge_iff_of_mem_buyers hdisj hP g hiP').1 (hfAll.2.1 g i hpos).2.2).1
            rw [h1]
            exact Finset.sum_congr rfl fun g hg => by simp [falt, hg, hiP']
          rw [hsum, batchReducedCap_eq_of_mem hdisj hP hiP']
          exact hgP.2.2.2 i hiP'
        · have hsum : ∑ g ∈ batchGoods ps, falt g i = ∑ g ∈ batchGoods ps, ofRealFlow F g i :=
            Finset.sum_congr rfl fun g _ => by simp [falt, hiP']
          rw [hsum]
          exact hfAll.2.2.2 i hiB
    have hFalt_le : realNetOut (toRealFlow falt) .source ≤ realNetOut F .source :=
      hFmax.2 ⟨toRealFlow falt,
        isFeasibleRealFlow_toRealFlow (fun g _ => ha g) (fun i _ => batchReducedCap_nonneg a b ps i)
          hfalt_bip, rfl⟩
    have hdiff : realNetOut (toRealFlow falt) .source - realNetOut F .source =
        realNetOut GP .source - realNetOut (toRealFlow fP) .source := by
      have hF_all : realNetOut F .source = ∑ g : G, ∑ i : I, ofRealFlow F g i := by
        rw [hFval]
        calc
          ∑ g ∈ batchGoods ps, ∑ i ∈ batchBuyers ps, ofRealFlow F g i
            = ∑ g ∈ batchGoods ps, ∑ i : I, ofRealFlow F g i :=
                Finset.sum_congr rfl fun g _ => Finset.sum_subset (Finset.subset_univ _)
                  fun i _ hi =>
                    le_antisymm (not_lt.1 fun h => hi (hfAll.2.1 g i h).2.1) (hfAll.1 g i)
          _ = ∑ g : G, ∑ i : I, ofRealFlow F g i :=
                Finset.sum_subset (Finset.subset_univ _) fun g _ hg =>
                  Finset.sum_eq_zero fun i _ =>
                    le_antisymm (not_lt.1 fun h => hg (hfAll.2.1 g i h).1) (hfAll.1 g i)
      have hGP_all : realNetOut GP .source = ∑ g : G, ∑ i : I,
          if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow GP g i else 0 := by
        rw [hGPval]
        calc
          ∑ g ∈ P.goods, ∑ i ∈ P.buyers, ofRealFlow GP g i
            = ∑ g ∈ P.goods, ∑ i : I,
                if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow GP g i else 0 :=
                Finset.sum_congr rfl fun g hg => by
                  rw [← Finset.univ_inter P.buyers, ← Finset.sum_ite_mem]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  by_cases hi : i ∈ P.buyers <;> simp [hg, hi]
          _ = ∑ g : G, ∑ i : I,
                if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow GP g i else 0 := by
                rw [← Finset.univ_inter P.goods, ← Finset.sum_ite_mem]
                refine Finset.sum_congr rfl fun g _ => ?_
                by_cases hg : g ∈ P.goods <;> simp [hg]
      rw [realNetOut_toRealFlow, realNetOut_toRealFlow, hF_all, hGP_all,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hgi : g ∈ P.goods ∧ i ∈ P.buyers <;> simp [falt, fP, hgi]
    linarith
  -- Show residual reachability to `.sink` agrees on all vertices of `P`!
  let inP : FlowVertex I G → Prop
    | .good g => g ∈ P.goods
    | .buyer i => i ∈ P.buyers
    | _ => False
  have hFP_src (g : G) (hg : g ∈ P.goods) :
      toRealFlow fP (.source, .good g) = F (.source, .good g) := by
    rw [toRealFlow, hFsrc g]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ P.buyers
    · simp [fP, hg, hi]
    · simp only [fP, hg, hi, and_false, ↓reduceIte]
      symm
      refine le_antisymm (not_lt.1 fun hpos => hi ?_) (hfAll.1 g i)
      exact ((batchEdge_iff_of_mem_goods hdisj hP hg i).1 (hfAll.2.1 g i hpos).2.2).1
  have hFP_sink (i : I) (hi : i ∈ P.buyers) :
      toRealFlow fP (.buyer i, .sink) = F (.buyer i, .sink) := by
    rw [toRealFlow, hFsink i]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g ∈ P.goods
    · simp [fP, hg, hi]
    · simp only [fP, hg, hi, false_and, ↓reduceIte]
      symm
      refine le_antisymm (not_lt.1 fun hpos => hg ?_) (hfAll.1 g i)
      exact ((batchEdge_iff_of_mem_buyers hdisj hP g hi).1 (hfAll.2.1 g i hpos).2.2).1
  have hreach_iff : ∀ v : FlowVertex I G, inP v →
      (Relation.ReflTransGen (Residual (batchCap a b E ps) F) v .sink ↔
        Relation.ReflTransGen (Residual WP (toRealFlow fP)) v .sink) := by
    have hdir1 : ∀ v, Relation.ReflTransGen (Residual (batchCap a b E ps) F) v .sink →
        inP v → Relation.ReflTransGen (Residual WP (toRealFlow fP)) v .sink := by
      intro v hv
      induction hv using Relation.ReflTransGen.head_induction_on with
      | refl => intro h; exact False.elim h
      | @head u w huw hws ih =>
        intro huP
        cases u with
        | source | sink => exact False.elim huP
        | good g =>
          have hgP : g ∈ P.goods := huP
          rcases residual_bipCap_good_cases hF huw with rfl | ⟨i, rfl, -, -, hEall⟩
          · exact absurd hws (not_resReachable_of_isMaxRealFlow hF hFmax (by simp))
          · have hE := (batchEdge_iff_of_mem_goods hdisj hP hgP i).1 hEall
            exact Relation.ReflTransGen.head
              (residual_bipCap_good_buyer_of_edge (fun g' _ => ha g') (fun _ _ => le_max_left _ _)
                hfP_bip hgP hE.1 hE.2)
              (ih hE.1)
        | buyer i =>
          have hiP : i ∈ P.buyers := huP
          rcases residual_bipCap_buyer_cases hF huw with ⟨rfl, -, hlt⟩ | ⟨g, rfl, hpos⟩
          · rw [batchReducedCap_eq_of_mem hdisj hP hiP, ← hFP_sink i hiP] at hlt
            exact Relation.ReflTransGen.single (Or.inl (by simpa [WP, bipCap, hiP] using hlt))
          · have hgP : g ∈ P.goods :=
              ((batchEdge_iff_of_mem_buyers hdisj hP g hiP).1 (hfAll.2.1 g i hpos).2.2).1
            exact Relation.ReflTransGen.head
              (Or.inr (by simpa [toRealFlow, fP, hgP, hiP, ofRealFlow] using hpos))
              (ih hgP)
    have hdir2 : ∀ v, Relation.ReflTransGen (Residual WP (toRealFlow fP)) v .sink →
        inP v → Relation.ReflTransGen (Residual (batchCap a b E ps) F) v .sink := by
      intro v hv
      induction hv using Relation.ReflTransGen.head_induction_on with
      | refl => intro h; exact False.elim h
      | @head u w huw hws ih =>
        intro huP
        cases u with
        | source | sink => exact False.elim huP
        | good g =>
          have hgP : g ∈ P.goods := huP
          rcases residual_bipCap_good_cases hFP_feas huw with rfl | ⟨i, rfl, -, hiP, hE⟩
          · exact absurd hws (not_resReachable_of_isMaxRealFlow hFP_feas hFP_max (by simp))
          · exact Relation.ReflTransGen.head
              (residual_bipCap_good_buyer_of_edge (fun g' _ => ha g')
                (fun i' _ => batchReducedCap_nonneg a b ps i') hfAll
                (mem_batchGoods.2 ⟨P, hP, hgP⟩) (mem_batchBuyers.2 ⟨P, hP, hiP⟩)
                ⟨P, hP, hgP, hiP, hE⟩)
              (ih hiP)
        | buyer i =>
          have hiP : i ∈ P.buyers := huP
          rcases residual_bipCap_buyer_cases hFP_feas huw with ⟨rfl, -, hlt⟩ | ⟨g, rfl, hpos⟩
          · rw [hFP_sink i hiP] at hlt
            refine Relation.ReflTransGen.single (Or.inl ?_)
            have hcap : batchCap a b E ps (.buyer i) .sink = reducedCap a b P i := by
              simp [batchCap, bipCap, mem_batchBuyers.2 ⟨P, hP, hiP⟩,
                batchReducedCap_eq_of_mem hdisj hP hiP]
            linarith
          · have hpos' : 0 < fP g i := by simpa [ofRealFlow, toRealFlow] using hpos
            have hgP : g ∈ P.goods := (hfP_bip.2.1 g i hpos').1
            exact Relation.ReflTransGen.head
              (Or.inr (by simpa [fP, hgP, hiP, ofRealFlow] using hpos'))
              (ih hgP)
    exact fun v hv => ⟨fun h => hdir1 v h hv, fun h => hdir2 v h hv⟩
  refine ⟨hFP_feas, hFP_max, ?_, ?_⟩
  · ext g
    simp only [cutGoods, Finset.mem_filter, mem_maxMinCut]
    exact and_congr_right fun hg => not_congr (hreach_iff (.good g) hg)
  · ext i
    simp only [cutBuyers, Finset.mem_filter, mem_maxMinCut]
    exact and_congr_right fun hi => not_congr (hreach_iff (.buyer i) hi)

/-- A bipartite flow `f` satisfies the piece-level balancedness specification on `P = (A, B)`:
it is feasible on `P`, saturates all goods in `A`, and satisfies Property 1 on `(A, B)`. -/
private def IsPieceBalanced (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop)
    (P : BipPiece I G) (f : G → I → ℝ) : Prop :=
  IsBipFlow P.goods P.buyers a b E f ∧
  (∀ g ∈ P.goods, ∑ i ∈ P.buyers, f g i = a g) ∧
  ∀ j ∈ P.buyers, ∀ i ∈ P.buyers,
    b j - ∑ g ∈ P.goods, f g j < b i - ∑ g ∈ P.goods, f g i →
    ¬ Relation.ReflTransGen (fun u v => ∃ g ∈ P.goods, 0 < f g u ∧ E g v) j i

/-- **Single-piece Case 1 lemma** ([Vazirani2007], Section 5.7.1, Lemmas 5.6–5.7, pp. 113–114):
when the maximal min-cut of `N'` puts all of `P` on the source side (`A₂ = ∅ ∧ B₂ = ∅`), `f'`
itself is a piece-balanced max-flow on `P`. -/
private theorem isPieceBalanced_case1 {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g, 0 ≤ a g) (hb : ∀ i, 0 ≤ b i)
    {P : BipPiece I G} (hP : ValidPiece a b E P)
    {F' : FlowVertex I G × FlowVertex I G → ℝ}
    (hF' : IsFeasibleRealFlow (bipCap P.goods P.buyers a (reducedCap a b P) E) .source .sink F')
    (hF'max : IsMaxRealFlow (bipCap P.goods P.buyers a (reducedCap a b P) E) .source .sink
      (realNetOut F' .source))
    (hA : cutGoods P.goods (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E) F') =
      P.goods)
    (hB : cutBuyers P.buyers (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E) F') =
      P.buyers) :
    IsPieceBalanced a b E P (ofRealFlow F') := by
  classical
  set W' := bipCap P.goods P.buyers a (reducedCap a b P) E
  set X := uniformShift P.buyers b (∑ g ∈ P.goods, a g)
  have hInvA : ∑ g ∈ P.goods, a g ≤ ∑ i ∈ P.buyers, b i :=
    (hP.2.2 P.goods Finset.Subset.rfl).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hb i)
  have hX := uniformShift_spec (fun i _ => hb i) (Finset.sum_nonneg fun g _ => ha g) hInvA
  have hW'_nn : ∀ u v, 0 ≤ W' u v := bipCap_nonneg (fun g _ => ha g) (fun i _ => le_max_left _ _)
  obtain ⟨hf'_bip, -, -, hF'val⟩ := isBipFlow_ofRealFlow hF'
  have hval_eq : ∑ g ∈ P.goods, ∑ i ∈ P.buyers, ofRealFlow F' g i = ∑ g ∈ P.goods, a g := by
    have hmc := cutWeight_maxMinCut hW'_nn hF' hF'max
    have hs := source_mem_maxMinCut hF' hF'max
    have ht := sink_notMem_maxMinCut W' F'
    have hnc := no_cross_of_minCut (A := P.goods) (B := P.buyers) (a := a)
      (b := reducedCap a b P) (E := E) (fun g _ => ha g) (fun i _ => le_max_left _ _) hs ht hmc
    have hcw := cutWeight_bipCap_of_no_cross (A := P.goods) (B := P.buyers) (a := a)
      (b := reducedCap a b P) (E := E) hs ht hnc
    rw [hA, hB, Finset.sdiff_self, Finset.sum_empty, zero_add] at hcw
    have hsum_red : ∑ i ∈ P.buyers, reducedCap a b P i = ∑ g ∈ P.goods, a g := hX.2
    rw [← hF'val, IsGreatest.unique hF'max (isMaxRealFlow_minRealCutBetween hW'_nn (by simp)),
      ← hmc, hcw, hsum_red]
  have hsatG : ∀ g ∈ P.goods, ∑ i ∈ P.buyers, ofRealFlow F' g i = a g := by
    intro g hg
    have hdiff : ∑ g' ∈ P.goods, (a g' - ∑ i ∈ P.buyers, ofRealFlow F' g' i) = 0 := by
      rw [Finset.sum_sub_distrib, hval_eq, sub_self]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun g' hg' =>
      sub_nonneg.2 (hf'_bip.2.2.1 g' hg')).1 hdiff g hg
    linarith
  have hsatB : ∀ i ∈ P.buyers, ∑ g ∈ P.goods, ofRealFlow F' g i = reducedCap a b P i := by
    intro i hi
    have hsum_i : ∑ i' ∈ P.buyers, ∑ g ∈ P.goods, ofRealFlow F' g i' =
        ∑ i' ∈ P.buyers, reducedCap a b P i' := by
      rw [Finset.sum_comm, hval_eq]
      exact hX.2.symm
    have hdiff :
        ∑ i' ∈ P.buyers, (reducedCap a b P i' - ∑ g ∈ P.goods, ofRealFlow F' g i') = 0 := by
      rw [Finset.sum_sub_distrib, hsum_i, sub_self]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i' hi' =>
      sub_nonneg.2 (hf'_bip.2.2.2 i' hi')).1 hdiff i hi
    linarith
  have hf_bip : IsBipFlow P.goods P.buyers a b E (ofRealFlow F') :=
    ⟨hf'_bip.1, hf'_bip.2.1, hf'_bip.2.2.1, fun i hi =>
      (hf'_bip.2.2.2 i hi).trans (max_le (hb i) (by linarith [hX.1]))⟩
  refine ⟨hf_bip, hsatG, fun j hj i hi hsurp hreach => ?_⟩
  have hsurp_eq (k : I) (hk : k ∈ P.buyers) :
      b k - ∑ g ∈ P.goods, ofRealFlow F' g k = min (b k) X := by
    rw [hsatB k hk, reducedCap]
    rcases le_total (b k) X with hle | hle
    · rw [max_eq_left (sub_nonpos.2 hle), sub_zero, min_eq_left hle]
    · rw [max_eq_right (sub_nonneg.2 hle), min_eq_right hle]; ring
  rw [hsurp_eq j hj, hsurp_eq i hi] at hsurp
  have hbj_lt : b j < X := by
    have hlt : min (b j) X < X := lt_of_lt_of_le hsurp (min_le_right _ _)
    by_contra hge; push Not at hge
    rw [min_eq_right hge] at hlt
    exact lt_irrefl _ hlt
  have hfj_zero : ∀ g ∈ P.goods, ofRealFlow F' g j = 0 := by
    intro g hg
    have hsum0 : ∑ g' ∈ P.goods, ofRealFlow F' g' j = 0 := by
      rw [hsatB j hj, reducedCap, max_eq_left (sub_nonpos.2 hbj_lt.le)]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun g' _ => hf'_bip.1 g' j).1 hsum0 g hg
  cases hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact lt_irrefl _ hsurp
  | @head u v huv _ _ =>
    obtain ⟨g, hgP, hpos, -⟩ := huv
    linarith [hfj_zero g hgP]

/-- **Single-piece Case 2 structural split & Lemmas 5.6–5.7** ([Vazirani2007], Section 5.7.1,
pp. 113–115): when the maximal min-cut `(S, T)` of `N'` has `T ≠ {.sink}` (`A₂.Nonempty ∨
B₂.Nonempty`), both sub-pieces `P₁ = (A₁, B₁ ∩ Γ(A₁))` and `P₂ = (A₂, B₂)` are valid, strictly
smaller in goods, and vertex-disjoint; combining any piece-balanced flows `f₁` on `P₁` and `f₂` on
`P₂` produces a piece-balanced max-flow `f = f₁ + f₂` on `P`. -/
private theorem case2_split_and_combine {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g, 0 ≤ a g) (hb : ∀ i, 0 ≤ b i)
    {P : BipPiece I G} (hP : ValidPiece a b E P)
    {F' : FlowVertex I G × FlowVertex I G → ℝ}
    (hF' : IsFeasibleRealFlow (bipCap P.goods P.buyers a (reducedCap a b P) E) .source .sink F')
    (hF'max : IsMaxRealFlow (bipCap P.goods P.buyers a (reducedCap a b P) E) .source .sink
      (realNetOut F' .source))
    (hcase2 : ¬ (cutGoods P.goods
        (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E) F') = P.goods ∧
      cutBuyers P.buyers
        (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E) F') = P.buyers)) :
    let S := maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E) F'
    let A₁ := cutGoods P.goods S
    let B₁ := cutBuyers P.buyers S
    let A₂ := P.goods \ A₁
    let B₂ := P.buyers \ B₁
    let P₁ : BipPiece I G := ⟨A₁, B₁ ∩ bipNbr P.buyers E A₁⟩
    let P₂ : BipPiece I G := ⟨A₂, B₂⟩
    ValidPiece a b E P₁ ∧ ValidPiece a b E P₂ ∧
      A₁.card < P.goods.card ∧ A₂.card < P.goods.card ∧
      Disjoint P₁.goods P₂.goods ∧ Disjoint P₁.buyers P₂.buyers ∧
      ∀ f₁ f₂ : G → I → ℝ, IsPieceBalanced a b E P₁ f₁ → IsPieceBalanced a b E P₂ f₂ →
        IsPieceBalanced a b E P (fun g i => f₁ g i + f₂ g i) := by
  classical
  intro S A₁ B₁ A₂ B₂ P₁ P₂
  set W' := bipCap P.goods P.buyers a (reducedCap a b P) E
  set X := uniformShift P.buyers b (∑ g ∈ P.goods, a g)
  have hInvA : ∑ g ∈ P.goods, a g ≤ ∑ i ∈ P.buyers, b i :=
    (hP.2.2 P.goods Finset.Subset.rfl).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hb i)
  have hX := uniformShift_spec (fun i _ => hb i) (Finset.sum_nonneg fun g _ => ha g) hInvA
  have hW'_nn : ∀ u v, 0 ≤ W' u v := bipCap_nonneg (fun g _ => ha g) (fun i _ => le_max_left _ _)
  have hsS : FlowVertex.source ∈ S := source_mem_maxMinCut hF' hF'max
  have htS : FlowVertex.sink ∉ S := sink_notMem_maxMinCut W' F'
  have hmc : cutWeight W' S = minRealCutBetween W' .source .sink :=
    cutWeight_maxMinCut hW'_nn hF' hF'max
  have hnc : ∀ g ∈ A₁, ∀ i ∈ B₂, ¬ E g i :=
    no_cross_of_minCut (fun g _ => ha g) (fun i _ => le_max_left _ _) hsS htS hmc
  have hA₁_sub : A₁ ⊆ P.goods := Finset.filter_subset _ _
  have hB₁_sub : B₁ ⊆ P.buyers := Finset.filter_subset _ _
  obtain ⟨hf'_bip, hF'src, hF'sink, -⟩ := isBipFlow_ofRealFlow hF'
  -- Key saturation properties of `F'` across `(S, univ \ S)`:
  -- 1. Every `g ∈ A₂` has `(.source, .good g)` saturated in `F'`.
  have hF'_sat_A₂ : ∀ g ∈ A₂, F' (.source, .good g) = a g := by
    intro g hg
    have hgP : g ∈ P.goods := (Finset.mem_sdiff.1 hg).1
    have hgNotS : FlowVertex.good g ∉ S := fun h =>
      (Finset.mem_sdiff.1 hg).2 (Finset.mem_filter.2 ⟨hgP, h⟩)
    simpa [W', bipCap, hgP] using (sat_of_maxMinCut hF' hsS hgNotS).1
  -- 2. Every `i ∈ B₁` has `(.buyer i, .sink)` saturated in `F'`.
  have hF'_sat_B₁ : ∀ i ∈ B₁, F' (.buyer i, .sink) = reducedCap a b P i := by
    intro i hi
    have hiP : i ∈ P.buyers := (Finset.mem_filter.1 hi).1
    have hiS : FlowVertex.buyer i ∈ S := (Finset.mem_filter.1 hi).2
    simpa [W', bipCap, hiP] using (sat_of_maxMinCut hF' hiS htS).1
  -- 3. No flow of `F'` goes from `A₂` to `B₁` (otherwise backward residual edge puts `B₁` in `T`).
  have hF'_zero_A₂_B₁ : ∀ g ∈ A₂, ∀ i ∈ B₁, ofRealFlow F' g i = 0 := by
    intro g hg i hi
    have hgP : g ∈ P.goods := (Finset.mem_sdiff.1 hg).1
    have hgNotS : FlowVertex.good g ∉ S := fun h =>
      (Finset.mem_sdiff.1 hg).2 (Finset.mem_filter.2 ⟨hgP, h⟩)
    have hiS : FlowVertex.buyer i ∈ S := (Finset.mem_filter.1 hi).2
    exact (sat_of_maxMinCut hF' hiS hgNotS).2
  -- 4. Every `i ∈ B₂` has `0 < reducedCap a b P i` (hence `X < b i` and `b'(i) = b i - X`).
  have hB₂_red_pos : ∀ i ∈ B₂, 0 < reducedCap a b P i := by
    intro i hi
    have hiP : i ∈ P.buyers := (Finset.mem_sdiff.1 hi).1
    have hiNotS : FlowVertex.buyer i ∉ S := fun h =>
      (Finset.mem_sdiff.1 hi).2 (Finset.mem_filter.2 ⟨hiP, h⟩)
    rw [mem_maxMinCut, not_not] at hiNotS
    refine lt_of_le_of_ne (le_max_left _ _) fun h0 => ?_
    have hred0 : reducedCap a b P i = 0 := h0.symm
    cases hiNotS using Relation.ReflTransGen.head_induction_on with
    | @head u w huw _ _ =>
      rcases residual_bipCap_buyer_cases hF' huw with ⟨rfl, -, hlt⟩ | ⟨g, rfl, hpos⟩
      · linarith [hF'.1 (.buyer i) .sink, hred0]
      · have hle1 : ofRealFlow F' g i ≤ ∑ g' ∈ P.goods, ofRealFlow F' g' i :=
          Finset.single_le_sum (fun g' _ => hf'_bip.1 g' i) (hf'_bip.2.1 g i hpos).1
        have hle2 : ∑ g' ∈ P.goods, ofRealFlow F' g' i ≤ reducedCap a b P i :=
          hf'_bip.2.2.2 i hiP
        linarith
  -- 5. `A₂.Nonempty` and `A₁.Nonempty`!
  have hA₂_ne : A₂.Nonempty := by
    by_contra hA₂_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hA₂_empty
    have hA₁_eq : A₁ = P.goods := by
      ext g
      refine ⟨fun hg => hA₁_sub hg, fun hg => ?_⟩
      by_contra hnot
      have : g ∈ A₂ := Finset.mem_sdiff.2 ⟨hg, hnot⟩
      rw [hA₂_empty] at this
      exact Finset.notMem_empty g this
    have hB₂_ne : B₂.Nonempty := by
      by_contra hB₂_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hB₂_empty
      have hB₁_eq : B₁ = P.buyers := by
        ext i
        refine ⟨fun hi => hB₁_sub hi, fun hi => ?_⟩
        by_contra hnot
        have : i ∈ B₂ := Finset.mem_sdiff.2 ⟨hi, hnot⟩
        rw [hB₂_empty] at this
        exact Finset.notMem_empty i this
      exact hcase2 ⟨hA₁_eq, hB₁_eq⟩
    obtain ⟨i, hiB₂⟩ := hB₂_ne
    obtain ⟨g, hgP, hE⟩ := hP.2.1 i (Finset.mem_sdiff.1 hiB₂).1
    exact hnc g (hA₁_eq ▸ hgP) i hiB₂ hE
  have hA₁_ne : A₁.Nonempty := by
    by_contra hA₁_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hA₁_empty
    have hA₂_eq : A₂ = P.goods := by simp [A₂, hA₁_empty]
    have hcwS : cutWeight W' S = (∑ g ∈ P.goods, a g) + ∑ i ∈ B₁, reducedCap a b P i := by
      rw [cutWeight_bipCap_of_no_cross hsS htS hnc]
      change (∑ g ∈ A₂, a g) + ∑ i ∈ B₁, reducedCap a b P i = _
      rw [hA₂_eq]
    have hcwSink : cutWeight W' (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
        ∑ g ∈ P.goods, a g := by
      rw [cutWeight_bipCap_sink]
      exact hX.2
    have hle_sink : cutWeight W' S ≤ cutWeight W' (Finset.univ \ {.sink}) := by
      rw [hmc]
      exact minRealCutBetween_le_cutWeight _ (by simp) (by simp)
    have hB₁_nn : 0 ≤ ∑ i ∈ B₁, reducedCap a b P i :=
      Finset.sum_nonneg fun i _ => le_max_left _ _
    have hsink_min : cutWeight W' (Finset.univ \ ({.sink} : Finset (FlowVertex I G))) =
        minRealCutBetween W' .source .sink := by
      rw [← hmc]; linarith
    have hsub := subset_maxMinCut_of_minCut hW'_nn hF' hF'max (by simp) (by simp) hsink_min
    obtain ⟨g, hgA₂⟩ := hA₂_ne
    have hgIn : FlowVertex.good g ∈ S := hsub (by simp)
    have : g ∈ A₁ := Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hgA₂).1, hgIn⟩
    rw [hA₁_empty] at this
    exact Finset.notMem_empty g this
  -- 6. ValidPiece for `P₁` and `P₂`!
  have hP₁_valid : ValidPiece a b E P₁ := by
    refine ⟨hA₁_ne, fun i hi => ?_, fun T hT => ?_⟩
    · have hiNbr := (Finset.mem_inter.1 hi).2
      exact (mem_bipNbr.1 hiNbr).2
    · have hnbr_eq : bipNbr P₁.buyers E T = bipNbr P.buyers E T := by
        ext i
        simp only [P₁, mem_bipNbr, Finset.mem_inter]
        constructor
        · rintro ⟨⟨hiB₁, _⟩, g, hgT, hE⟩
          exact ⟨hB₁_sub hiB₁, g, hgT, hE⟩
        · rintro ⟨hiP, g, hgT, hE⟩
          have hiB₁ : i ∈ B₁ := by
            by_contra hnot
            exact hnc g (hT hgT) i (Finset.mem_sdiff.2 ⟨hiP, hnot⟩) hE
          exact ⟨⟨hiB₁, ⟨hiP, g, hT hgT, hE⟩⟩, g, hgT, hE⟩
      rw [hnbr_eq]
      exact hP.2.2 T (hT.trans hA₁_sub)
  have hP₂_valid : ValidPiece a b E P₂ := by
    refine ⟨hA₂_ne, fun i hi => ?_, fun T hT => ?_⟩
    · obtain ⟨g, hgP, hE⟩ := hP.2.1 i (Finset.mem_sdiff.1 hi).1
      refine ⟨g, Finset.mem_sdiff.2 ⟨hgP, fun hgA₁ => hnc g hgA₁ i hi hE⟩, hE⟩
    · -- Restriction of `F'` to `T ⊆ A₂` routes all `a g` from `T` into `bipNbr B₂ E T`!
      have hsum_sat : ∑ g ∈ T, a g = ∑ g ∈ T, ∑ i ∈ bipNbr B₂ E T, ofRealFlow F' g i := by
        refine Finset.sum_congr rfl fun g hgT => ?_
        have hgA₂ : g ∈ A₂ := hT hgT
        have hgP : g ∈ P.goods := (Finset.mem_sdiff.1 hgA₂).1
        rw [← hF'_sat_A₂ g hgA₂, hF'src g]
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun i _ hiNbr => ?_
        refine le_antisymm (not_lt.1 fun hpos => hiNbr ?_) (hf'_bip.1 g i)
        have hsupp := hf'_bip.2.1 g i hpos
        have hiB₂ : i ∈ B₂ := Finset.mem_sdiff.2 ⟨hsupp.2.1, fun hiB₁ =>
          hpos.ne' (hF'_zero_A₂_B₁ g hgA₂ i hiB₁)⟩
        exact mem_bipNbr.2 ⟨hiB₂, g, hgT, hsupp.2.2⟩
      rw [hsum_sat, Finset.sum_comm]
      calc
        ∑ i ∈ bipNbr B₂ E T, ∑ g ∈ T, ofRealFlow F' g i
          ≤ ∑ i ∈ bipNbr B₂ E T, ∑ g ∈ P.goods, ofRealFlow F' g i :=
              Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum_of_subset_of_nonneg (hT.trans Finset.sdiff_subset)
                  fun g _ _ => hf'_bip.1 g i
        _ ≤ ∑ i ∈ bipNbr B₂ E T, reducedCap a b P i :=
              Finset.sum_le_sum fun i hi =>
                hf'_bip.2.2.2 i (Finset.mem_sdiff.1 (mem_bipNbr.1 hi).1).1
        _ ≤ ∑ i ∈ bipNbr B₂ E T, b i :=
              Finset.sum_le_sum fun i hi => max_le (hb i) (by linarith [hX.1])
  -- 7. Strict cardinality drops and disjointness:
  have hdisjA : Disjoint A₁ A₂ := Finset.disjoint_sdiff
  have hunionA : A₁ ∪ A₂ = P.goods := Finset.union_sdiff_of_subset hA₁_sub
  have hcard_sum : A₁.card + A₂.card = P.goods.card := by
    rw [← Finset.card_union_of_disjoint hdisjA, hunionA]
  have hA₁_lt : A₁.card < P.goods.card := by
    have := Finset.card_pos.2 hA₂_ne; omega
  have hA₂_lt : A₂.card < P.goods.card := by
    have := Finset.card_pos.2 hA₁_ne; omega
  have hdisjB : Disjoint P₁.buyers P₂.buyers :=
    Finset.disjoint_sdiff.mono_left Finset.inter_subset_left
  refine ⟨hP₁_valid, hP₂_valid, hA₁_lt, hA₂_lt, hdisjA, hdisjB, ?_⟩
  -- 8. Combine any piece-balanced flows `f₁` on `P₁` and `f₂` on `P₂`!
  intro f₁ f₂ hf₁ hf₂
  let f : G → I → ℝ := fun g i => f₁ g i + f₂ g i
  have hf₁_zero : ∀ g i, ¬ (g ∈ P₁.goods ∧ i ∈ P₁.buyers) → f₁ g i = 0 := fun g i h =>
    le_antisymm (not_lt.1 fun hpos => h ⟨(hf₁.1.2.1 g i hpos).1, (hf₁.1.2.1 g i hpos).2.1⟩)
      (hf₁.1.1 g i)
  have hf₂_zero : ∀ g i, ¬ (g ∈ P₂.goods ∧ i ∈ P₂.buyers) → f₂ g i = 0 := fun g i h =>
    le_antisymm (not_lt.1 fun hpos => h ⟨(hf₂.1.2.1 g i hpos).1, (hf₂.1.2.1 g i hpos).2.1⟩)
      (hf₂.1.1 g i)
  have hf_on_A₁ (g : G) (hg : g ∈ A₁) : ∑ i ∈ P.buyers, f g i = a g := by
    have h2 : ∑ i ∈ P.buyers, f₂ g i = 0 := Finset.sum_eq_zero fun i _ =>
      hf₂_zero g i fun h => Finset.disjoint_left.1 hdisjA hg h.1
    have h1 : ∑ i ∈ P.buyers, f₁ g i = ∑ i ∈ P₁.buyers, f₁ g i := by
      symm
      refine Finset.sum_subset (Finset.inter_subset_left.trans hB₁_sub) fun i _ hi =>
        hf₁_zero g i fun h => hi h.2
    simp only [f, Finset.sum_add_distrib, h2, add_zero, h1]
    exact hf₁.2.1 g hg
  have hf_on_A₂ (g : G) (hg : g ∈ A₂) : ∑ i ∈ P.buyers, f g i = a g := by
    have h1 : ∑ i ∈ P.buyers, f₁ g i = 0 := Finset.sum_eq_zero fun i _ =>
      hf₁_zero g i fun h => Finset.disjoint_right.1 hdisjA hg h.1
    have h2 : ∑ i ∈ P.buyers, f₂ g i = ∑ i ∈ B₂, f₂ g i := by
      symm
      refine Finset.sum_subset Finset.sdiff_subset fun i _ hi =>
        hf₂_zero g i fun h => hi h.2
    simp only [f, Finset.sum_add_distrib, h1, zero_add, h2]
    exact hf₂.2.1 g hg
  have hf_satG : ∀ g ∈ P.goods, ∑ i ∈ P.buyers, f g i = a g := fun g hg => by
    rw [← hunionA, Finset.mem_union] at hg
    rcases hg with hg | hg
    exacts [hf_on_A₁ g hg, hf_on_A₂ g hg]
  have hf_spent_B₁' (i : I) (hi : i ∈ P₁.buyers) :
      ∑ g ∈ P.goods, f g i = ∑ g ∈ A₁, f₁ g i := by
    have h2 : ∑ g ∈ P.goods, f₂ g i = 0 := Finset.sum_eq_zero fun g _ =>
      hf₂_zero g i fun h => Finset.disjoint_left.1 hdisjB hi h.2
    have h1 : ∑ g ∈ P.goods, f₁ g i = ∑ g ∈ A₁, f₁ g i := by
      symm
      refine Finset.sum_subset hA₁_sub fun g _ hg => hf₁_zero g i fun h => hg h.1
    simp only [f, Finset.sum_add_distrib, h2, add_zero, h1]
  have hf_spent_B₁_iso (i : I) (hi : i ∈ B₁) (hnot : i ∉ P₁.buyers) :
      ∑ g ∈ P.goods, f g i = 0 := by
    refine Finset.sum_eq_zero fun g _ => ?_
    have h1 : f₁ g i = 0 := hf₁_zero g i fun h => hnot h.2
    have h2 : f₂ g i = 0 := hf₂_zero g i fun h => (Finset.mem_sdiff.1 h.2).2 hi
    simp [f, h1, h2]
  have hf_spent_B₂ (i : I) (hi : i ∈ B₂) :
      ∑ g ∈ P.goods, f g i = ∑ g ∈ A₂, f₂ g i := by
    have h1 : ∑ g ∈ P.goods, f₁ g i = 0 := Finset.sum_eq_zero fun g _ =>
      hf₁_zero g i fun h => Finset.disjoint_right.1 hdisjB hi h.2
    have h2 : ∑ g ∈ P.goods, f₂ g i = ∑ g ∈ A₂, f₂ g i := by
      symm
      refine Finset.sum_subset Finset.sdiff_subset fun g _ hg => hf₂_zero g i fun h => hg h.1
    simp only [f, Finset.sum_add_distrib, h1, zero_add, h2]
  have hf_bip : IsBipFlow P.goods P.buyers a b E f := by
    refine ⟨fun g i => add_nonneg (hf₁.1.1 g i) (hf₂.1.1 g i), fun g i hpos => ?_,
      fun g hg => (hf_satG g hg).le, fun i hi => ?_⟩
    · rcases (hf₁.1.1 g i).eq_or_lt with h0 | h1
      · have h2 : 0 < f₂ g i := by dsimp only [f] at hpos; linarith
        have hs := hf₂.1.2.1 g i h2
        exact ⟨(Finset.mem_sdiff.1 hs.1).1, (Finset.mem_sdiff.1 hs.2.1).1, hs.2.2⟩
      · have hs := hf₁.1.2.1 g i h1
        exact ⟨hA₁_sub hs.1, hB₁_sub (Finset.mem_inter.1 hs.2.1).1, hs.2.2⟩
    · by_cases hiB₁ : i ∈ B₁
      · by_cases hiP₁ : i ∈ P₁.buyers
        · rw [hf_spent_B₁' i hiP₁]; exact hf₁.1.2.2.2 i hiP₁
        · rw [hf_spent_B₁_iso i hiB₁ hiP₁]; exact hb i
      · have hiB₂ : i ∈ B₂ := Finset.mem_sdiff.2 ⟨hi, hiB₁⟩
        rw [hf_spent_B₂ i hiB₂]; exact hf₂.1.2.2.2 i hiB₂
  -- Key surplus separation of Lemma 5.7:
  -- Every `i ∈ B₁` has surplus `≤ X`; every `j ∈ B₂` has surplus `> X`!
  have hsurp_B₁_le : ∀ i ∈ B₁, b i - ∑ g ∈ P.goods, f g i ≤ X := by
    intro i₀ hi₀
    by_cases hi₀P₁ : i₀ ∈ P₁.buyers
    · -- Let `H ⊆ P₁.buyers` be buyers in `P₁.buyers` with maximum surplus under `f₁`.
      have hP₁B_ne : P₁.buyers.Nonempty := ⟨i₀, hi₀P₁⟩
      set M₁ : ℝ := P₁.buyers.sup' hP₁B_ne fun i => b i - ∑ g ∈ A₁, f₁ g i
      have hle_M₁ : b i₀ - ∑ g ∈ P.goods, f g i₀ ≤ M₁ := by
        rw [hf_spent_B₁' i₀ hi₀P₁]
        exact Finset.le_sup' (fun i => b i - ∑ g ∈ A₁, f₁ g i) hi₀P₁
      suffices hM₁_le : M₁ ≤ X from hle_M₁.trans hM₁_le
      let H : Finset I := P₁.buyers.filter fun i => b i - ∑ g ∈ A₁, f₁ g i = M₁
      have hH_ne : H.Nonempty := by
        obtain ⟨im, him, him_eq⟩ := Finset.exists_mem_eq_sup' hP₁B_ne
          (fun i => b i - ∑ g ∈ A₁, f₁ g i)
        exact ⟨im, Finset.mem_filter.2 ⟨him, him_eq.symm⟩⟩
      let J : Finset G := A₁.filter fun g => ∃ i ∈ H, E g i
      -- Every `g ∈ J` sends all its `f₁`-flow into `H` (by Property 1 of `f₁`).
      have hf₁_J_to_H : ∀ g ∈ J, ∀ j ∈ P₁.buyers, j ∉ H → f₁ g j = 0 := by
        intro g hgJ j hjP₁ hjH
        obtain ⟨i, hiH, hE⟩ := (Finset.mem_filter.1 hgJ).2
        refine le_antisymm (not_lt.1 fun hpos => ?_) (hf₁.1.1 g j)
        have hj_lt : b j - ∑ g' ∈ A₁, f₁ g' j < b i - ∑ g' ∈ A₁, f₁ g' i := by
          have hle := Finset.le_sup' (f := fun k => b k - ∑ g' ∈ A₁, f₁ g' k) hjP₁
          have hne : b j - ∑ g' ∈ A₁, f₁ g' j ≠ M₁ := fun heq =>
            hjH (Finset.mem_filter.2 ⟨hjP₁, heq⟩)
          rw [(Finset.mem_filter.1 hiH).2]
          exact lt_of_le_of_ne hle hne
        exact hf₁.2.2 j hjP₁ i (Finset.mem_filter.1 hiH).1 hj_lt
          (Relation.ReflTransGen.single ⟨g, (Finset.mem_filter.1 hgJ).1, hpos, hE⟩)
      -- Total `f₁`-spending of `H` equals `∑ g ∈ J, a g`.
      have hH_spent : ∑ i ∈ H, ∑ g ∈ A₁, f₁ g i = ∑ g ∈ J, a g := by
        calc
          ∑ i ∈ H, ∑ g ∈ A₁, f₁ g i
            = ∑ i ∈ H, ∑ g ∈ J, f₁ g i := by
                refine Finset.sum_congr rfl fun i hiH => ?_
                symm
                refine Finset.sum_subset (Finset.filter_subset _ _) fun g hgA₁ hgJ => ?_
                refine le_antisymm (not_lt.1 fun hpos => hgJ ?_) (hf₁.1.1 g i)
                exact Finset.mem_filter.2 ⟨hgA₁, i, hiH, (hf₁.1.2.1 g i hpos).2.2⟩
          _ = ∑ g ∈ J, ∑ i ∈ H, f₁ g i := Finset.sum_comm
          _ = ∑ g ∈ J, ∑ i ∈ P₁.buyers, f₁ g i := by
                refine Finset.sum_congr rfl fun g hgJ => ?_
                exact Finset.sum_subset (Finset.filter_subset _ _) fun j hjP₁ hjH =>
                  hf₁_J_to_H g hgJ j hjP₁ hjH
          _ = ∑ g ∈ J, a g :=
                Finset.sum_congr rfl fun g hgJ => hf₁.2.1 g (Finset.mem_filter.1 hgJ).1
      -- In `F'`, every `i ∈ H ⊆ B₁` is saturated (`F'(i, t) = reducedCap i`), and all flow
      -- entering `H` in `F'` comes from `J` (none from `A₂` by `hF'_zero_A₂_B₁`, none from
      -- `A₁ \ J` since no equality edge).
      have hred_H_le : ∑ i ∈ H, reducedCap a b P i ≤ ∑ g ∈ J, a g := by
        calc
          ∑ i ∈ H, reducedCap a b P i
            = ∑ i ∈ H, ∑ g ∈ P.goods, ofRealFlow F' g i := by
                refine Finset.sum_congr rfl fun i hiH => ?_
                have hiB₁ : i ∈ B₁ := (Finset.mem_inter.1 (Finset.mem_filter.1 hiH).1).1
                rw [← hF'_sat_B₁ i hiB₁, hF'sink i]
                symm
                exact Finset.sum_subset (Finset.subset_univ _) fun g _ hgP =>
                  le_antisymm (not_lt.1 fun hpos => hgP (hf'_bip.2.1 g i hpos).1) (hf'_bip.1 g i)
          _ = ∑ i ∈ H, ∑ g ∈ J, ofRealFlow F' g i := by
                refine Finset.sum_congr rfl fun i hiH => ?_
                have hiB₁ : i ∈ B₁ := (Finset.mem_inter.1 (Finset.mem_filter.1 hiH).1).1
                symm
                refine Finset.sum_subset ((Finset.filter_subset _ _).trans hA₁_sub)
                  fun g hgP hgJ => ?_
                refine le_antisymm (not_lt.1 fun hpos => hgJ ?_) (hf'_bip.1 g i)
                have hgA₁ : g ∈ A₁ := by
                  by_contra hnot
                  exact hpos.ne' (hF'_zero_A₂_B₁ g (Finset.mem_sdiff.2 ⟨hgP, hnot⟩) i hiB₁)
                exact Finset.mem_filter.2 ⟨hgA₁, i, hiH, (hf'_bip.2.1 g i hpos).2.2⟩
          _ = ∑ g ∈ J, ∑ i ∈ H, ofRealFlow F' g i := Finset.sum_comm
          _ ≤ ∑ g ∈ J, ∑ i ∈ P.buyers, ofRealFlow F' g i :=
                Finset.sum_le_sum fun g _ =>
                  Finset.sum_le_sum_of_subset_of_nonneg
                    ((Finset.filter_subset _ _).trans (Finset.inter_subset_left.trans hB₁_sub))
                    fun i _ _ => hf'_bip.1 g i
          _ ≤ ∑ g ∈ J, a g :=
                Finset.sum_le_sum fun g hgJ =>
                  hf'_bip.2.2.1 g (hA₁_sub (Finset.mem_filter.1 hgJ).1)
      -- Now sum `b i - ∑ g ∈ A₁, f₁ g i = M₁` over `i ∈ H`!
      have hH_sum : (H.card : ℝ) * M₁ ≤ (H.card : ℝ) * X := by
        have h1 : (H.card : ℝ) * M₁ = (∑ i ∈ H, b i) - ∑ g ∈ J, a g := by
          rw [← hH_spent, ← Finset.sum_sub_distrib,
            Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2,
            Finset.sum_const, nsmul_eq_mul]
        have h2 : ∑ i ∈ H, b i ≤ (∑ i ∈ H, reducedCap a b P i) + (H.card : ℝ) * X := by
          have : ∑ i ∈ H, b i ≤ ∑ i ∈ H, (reducedCap a b P i + X) :=
            Finset.sum_le_sum fun i _ => by
              unfold reducedCap; linarith [le_max_right (0 : ℝ) (b i - X)]
          simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using this
        linarith
      have hH_pos : (0 : ℝ) < (H.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hH_ne
      exact le_of_mul_le_mul_left hH_sum hH_pos
    · -- Isolated buyer `i₀ ∈ B₁ \ P₁.buyers`: no edge from `A₁`, no flow from `A₂` in `F'`, so
      -- `reducedCap i₀ = F'(i₀, t) = 0`, hence `b i₀ ≤ X`!
      rw [hf_spent_B₁_iso i₀ hi₀ hi₀P₁, sub_zero]
      have hF'i₀_zero : F' (.buyer i₀, .sink) = 0 := by
        rw [hF'sink i₀]
        refine Finset.sum_eq_zero fun g _ => ?_
        refine le_antisymm (not_lt.1 fun hpos => ?_) (hf'_bip.1 g i₀)
        have hsupp := hf'_bip.2.1 g i₀ hpos
        by_cases hgA₁ : g ∈ A₁
        · exact hi₀P₁ (Finset.mem_inter.2 ⟨hi₀, mem_bipNbr.2 ⟨hsupp.2.1, g, hgA₁, hsupp.2.2⟩⟩)
        · exact hpos.ne' (hF'_zero_A₂_B₁ g (Finset.mem_sdiff.2 ⟨hsupp.1, hgA₁⟩) i₀ hi₀)
      have hred0 : reducedCap a b P i₀ = 0 := (hF'_sat_B₁ i₀ hi₀).symm.trans hF'i₀_zero
      have hle : b i₀ - X ≤ 0 := by
        have := le_max_right (0 : ℝ) (b i₀ - X)
        unfold reducedCap at hred0
        linarith
      linarith
  have hsurp_B₂_gt : ∀ j ∈ B₂, X < b j - ∑ g ∈ P.goods, f g j := by
    intro j₀ hj₀
    have hB₂_ne : B₂.Nonempty := ⟨j₀, hj₀⟩
    set m₂ : ℝ := B₂.inf' hB₂_ne fun j => b j - ∑ g ∈ A₂, f₂ g j
    have hm₂_le : m₂ ≤ b j₀ - ∑ g ∈ P.goods, f g j₀ := by
      rw [hf_spent_B₂ j₀ hj₀]
      exact Finset.inf'_le (fun j => b j - ∑ g ∈ A₂, f₂ g j) hj₀
    suffices hX_lt : X < m₂ from hX_lt.trans_le hm₂_le
    let L : Finset I := B₂.filter fun j => b j - ∑ g ∈ A₂, f₂ g j = m₂
    have hL_ne : L.Nonempty := by
      obtain ⟨jm, hjm, hjm_eq⟩ := Finset.exists_mem_eq_inf' hB₂_ne
        (fun j => b j - ∑ g ∈ A₂, f₂ g j)
      exact ⟨jm, Finset.mem_filter.2 ⟨hjm, hjm_eq.symm⟩⟩
    let K : Finset G := A₂.filter fun g => ∃ j ∈ L, 0 < f₂ g j
    -- Every `g ∈ K` has NO edge to `B₂ \ L` (by Property 1 of `f₂`).
    have hK_no_edge : ∀ g ∈ K, ∀ j ∈ B₂, j ∉ L → ¬ E g j := by
      intro g hgK j hjB₂ hjL hE
      obtain ⟨i, hiL, hpos⟩ := (Finset.mem_filter.1 hgK).2
      have hi_lt : b i - ∑ g' ∈ A₂, f₂ g' i < b j - ∑ g' ∈ A₂, f₂ g' j := by
        have hle : m₂ ≤ b j - ∑ g' ∈ A₂, f₂ g' j :=
          Finset.inf'_le (fun k => b k - ∑ g' ∈ A₂, f₂ g' k) hjB₂
        have hne : m₂ ≠ b j - ∑ g' ∈ A₂, f₂ g' j := fun heq =>
          hjL (Finset.mem_filter.2 ⟨hjB₂, heq.symm⟩)
        rw [(Finset.mem_filter.1 hiL).2]
        exact lt_of_le_of_ne hle hne
      exact hf₂.2.2 i (Finset.mem_filter.1 hiL).1 j hjB₂ hi_lt
        (Relation.ReflTransGen.single ⟨g, (Finset.mem_filter.1 hgK).1, hpos, hE⟩)
    -- Total `f₂`-spending of `L` equals `∑ g ∈ K, a g`.
    have hL_spent : ∑ j ∈ L, ∑ g ∈ A₂, f₂ g j = ∑ g ∈ K, a g := by
      calc
        ∑ j ∈ L, ∑ g ∈ A₂, f₂ g j
          = ∑ j ∈ L, ∑ g ∈ K, f₂ g j := by
              refine Finset.sum_congr rfl fun j hjL => ?_
              symm
              refine Finset.sum_subset (Finset.filter_subset _ _) fun g hgA₂ hgK => ?_
              exact le_antisymm (not_lt.1 fun hpos => hgK
                (Finset.mem_filter.2 ⟨hgA₂, j, hjL, hpos⟩)) (hf₂.1.1 g j)
        _ = ∑ g ∈ K, ∑ j ∈ L, f₂ g j := Finset.sum_comm
        _ = ∑ g ∈ K, ∑ j ∈ B₂, f₂ g j := by
              refine Finset.sum_congr rfl fun g hgK => ?_
              exact Finset.sum_subset (Finset.filter_subset _ _) fun j hjB₂ hjL =>
                le_antisymm (not_lt.1 fun hpos =>
                  hK_no_edge g hgK j hjB₂ hjL (hf₂.1.2.1 g j hpos).2.2) (hf₂.1.1 g j)
        _ = ∑ g ∈ K, a g := Finset.sum_congr rfl fun g hgK => hf₂.2.1 g (Finset.mem_filter.1 hgK).1
    -- In `F'`, every `g ∈ K ⊆ A₂` is saturated and sends all its flow into `L` (since no flow to
    -- `B₁` and no edge to `B₂ \ L`). Moreover `∑ g ∈ K, a g < ∑ j ∈ L, reducedCap a b P j` strictly
    -- (else no vertex in `K ∪ L` could reach `.sink` in `Residual W' F'`, contradicting `L ⊆ B₂`).
    have hK_F' : ∑ g ∈ K, a g = ∑ g ∈ K, ∑ j ∈ L, ofRealFlow F' g j := by
      refine Finset.sum_congr rfl fun g hgK => ?_
      have hgA₂ : g ∈ A₂ := (Finset.mem_filter.1 hgK).1
      rw [← hF'_sat_A₂ g hgA₂, hF'src g]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hjL => ?_
      refine le_antisymm (not_lt.1 fun hpos => ?_) (hf'_bip.1 g j)
      have hsupp := hf'_bip.2.1 g j hpos
      by_cases hjB₁ : j ∈ B₁
      · exact hpos.ne' (hF'_zero_A₂_B₁ g hgA₂ j hjB₁)
      · exact hK_no_edge g hgK j (Finset.mem_sdiff.2 ⟨hsupp.2.1, hjB₁⟩) hjL hsupp.2.2
    have hK_le_L : ∑ g ∈ K, a g ≤ ∑ j ∈ L, reducedCap a b P j := by
      rw [hK_F', Finset.sum_comm]
      calc
        ∑ j ∈ L, ∑ g ∈ K, ofRealFlow F' g j
          ≤ ∑ j ∈ L, ∑ g ∈ P.goods, ofRealFlow F' g j :=
              Finset.sum_le_sum fun j _ =>
                Finset.sum_le_sum_of_subset_of_nonneg
                  ((Finset.filter_subset _ _).trans Finset.sdiff_subset) fun g _ _ => hf'_bip.1 g j
        _ ≤ ∑ j ∈ L, reducedCap a b P j :=
              Finset.sum_le_sum fun j hjL =>
                hf'_bip.2.2.2 j (Finset.mem_sdiff.1 (Finset.mem_filter.1 hjL).1).1
    have hK_lt_L : ∑ g ∈ K, a g < ∑ j ∈ L, reducedCap a b P j := by
      refine lt_of_le_of_ne hK_le_L fun heq => ?_
      -- If equality holds, then (a) every `j ∈ L` is saturated in `F'`, and (b) every `g ∉ K` sends
      -- `0` flow to `L` in `F'`. Then `K ∪ L` has NO residual edge to `(univ \ S) \ (K ∪ L)`.
      have hKL_eq : ∑ j ∈ L, ∑ g ∈ K, ofRealFlow F' g j = ∑ j ∈ L, reducedCap a b P j := by
        rw [Finset.sum_comm, ← hK_F', heq]
      have hL_sat_F' : ∀ j ∈ L, F' (.buyer j, .sink) = reducedCap a b P j := by
        intro j hjL
        have hjP : j ∈ P.buyers := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hjL).1).1
        have hle1 : ∑ g ∈ K, ofRealFlow F' g j ≤ ∑ g ∈ P.goods, ofRealFlow F' g j :=
          Finset.sum_le_sum_of_subset_of_nonneg
            ((Finset.filter_subset _ _).trans Finset.sdiff_subset) fun g _ _ => hf'_bip.1 g j
        have hle2 : ∑ g ∈ P.goods, ofRealFlow F' g j ≤ reducedCap a b P j := hf'_bip.2.2.2 j hjP
        have hdiff : ∑ j' ∈ L, (reducedCap a b P j' - ∑ g ∈ K, ofRealFlow F' g j') = 0 := by
          rw [Finset.sum_sub_distrib, hKL_eq, sub_self]
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j' hj' => by
          have hj'P : j' ∈ P.buyers := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hj').1).1
          have h1 : ∑ g ∈ K, ofRealFlow F' g j' ≤ ∑ g ∈ P.goods, ofRealFlow F' g j' :=
            Finset.sum_le_sum_of_subset_of_nonneg
              ((Finset.filter_subset _ _).trans Finset.sdiff_subset) fun g _ _ => hf'_bip.1 g j'
          linarith [hf'_bip.2.2.2 j' hj'P]).1 hdiff j hjL
        have hF'j : F' (.buyer j, .sink) = ∑ g ∈ P.goods, ofRealFlow F' g j := by
          rw [hF'sink j]
          symm
          exact Finset.sum_subset (Finset.subset_univ _) fun g _ hgP =>
            le_antisymm (not_lt.1 fun hpos => hgP (hf'_bip.2.1 g j hpos).1) (hf'_bip.1 g j)
        linarith
      have hnotK_to_L : ∀ g ∉ K, ∀ j ∈ L, ofRealFlow F' g j = 0 := by
        intro g hgK j hjL
        by_cases hgP : g ∈ P.goods
        · have hdiff : ∑ j' ∈ L, (∑ g' ∈ P.goods \ K, ofRealFlow F' g' j') = 0 := by
            have hsplit : ∀ j' ∈ L, ∑ g' ∈ P.goods, ofRealFlow F' g' j' =
                (∑ g' ∈ K, ofRealFlow F' g' j') + ∑ g' ∈ P.goods \ K, ofRealFlow F' g' j' :=
              fun j' _ => by
                rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
                  ((Finset.filter_subset _ _).trans Finset.sdiff_subset)]
            have hsum_P : ∑ j' ∈ L, ∑ g' ∈ P.goods, ofRealFlow F' g' j' =
                ∑ j' ∈ L, reducedCap a b P j' := by
              refine Finset.sum_congr rfl fun j' hj' => ?_
              rw [← hL_sat_F' j' hj', hF'sink j']
              exact Finset.sum_subset (Finset.subset_univ _) fun g' _ hg' =>
                le_antisymm (not_lt.1 fun hpos => hg' (hf'_bip.2.1 g' j' hpos).1) (hf'_bip.1 g' j')
            have := Finset.sum_congr rfl hsplit
            rw [hsum_P, Finset.sum_add_distrib, hKL_eq] at this
            linarith
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j' _ =>
            Finset.sum_nonneg fun g' _ => hf'_bip.1 g' j').1 hdiff j hjL
          exact (Finset.sum_eq_zero_iff_of_nonneg fun g' _ => hf'_bip.1 g' j).1 h0 g
            (Finset.mem_sdiff.2 ⟨hgP, hgK⟩)
        · exact le_antisymm (not_lt.1 fun hpos => hgP (hf'_bip.2.1 g j hpos).1) (hf'_bip.1 g j)
      -- Prove no vertex in `K` or `L` can reach `.sink` in `Residual W' F'`.
      let inKL : FlowVertex I G → Prop
        | .good g => g ∈ K
        | .buyer j => j ∈ L
        | _ => False
      have hno_sink : ∀ v, Relation.ReflTransGen (Residual W' F') v .sink → ¬ inKL v := by
        intro v hv
        induction hv using Relation.ReflTransGen.head_induction_on with
        | refl => exact id
        | @head u w huw hws ih =>
          intro huKL
          cases u with
          | source | sink => exact huKL
          | good g =>
            have hgK : g ∈ K := huKL
            rcases residual_bipCap_good_cases hF' huw with rfl | ⟨j, rfl, -, hjP, hEj⟩
            · exact absurd hws (not_resReachable_of_isMaxRealFlow hF' hF'max (by simp))
            · by_cases hjL : j ∈ L
              · exact ih hjL
              · by_cases hjB₁ : j ∈ B₁
                · exact (mem_maxMinCut.1 (Finset.mem_filter.1 hjB₁).2) hws
                · exact hK_no_edge g hgK j (Finset.mem_sdiff.2 ⟨hjP, hjB₁⟩) hjL hEj
          | buyer j =>
            have hjL : j ∈ L := huKL
            rcases residual_bipCap_buyer_cases hF' huw with ⟨rfl, -, hlt⟩ | ⟨g, rfl, hpos⟩
            · linarith [hL_sat_F' j hjL]
            · by_cases hgK : g ∈ K
              · exact ih hgK
              · linarith [hnotK_to_L g hgK j hjL]
      obtain ⟨j₁, hj₁L⟩ := hL_ne
      have hj₁B₂ : j₁ ∈ B₂ := (Finset.mem_filter.1 hj₁L).1
      have hj₁NotS : FlowVertex.buyer j₁ ∉ S := fun h =>
        (Finset.mem_sdiff.1 hj₁B₂).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj₁B₂).1, h⟩)
      exact hno_sink (.buyer j₁) (by rwa [mem_maxMinCut, not_not] at hj₁NotS) hj₁L
    -- Now sum `b j - ∑ g ∈ A₂, f₂ g j = m₂` over `j ∈ L` using `b j = reducedCap a b P j + X`!
    have hL_sum : (L.card : ℝ) * X < (L.card : ℝ) * m₂ := by
      have h1 : (L.card : ℝ) * m₂ = (∑ j ∈ L, b j) - ∑ g ∈ K, a g := by
        rw [← hL_spent, ← Finset.sum_sub_distrib,
          Finset.sum_congr rfl fun j hj => (Finset.mem_filter.1 hj).2,
          Finset.sum_const, nsmul_eq_mul]
      have h2 : ∑ j ∈ L, b j = (∑ j ∈ L, reducedCap a b P j) + (L.card : ℝ) * X := by
        have : ∑ j ∈ L, b j = ∑ j ∈ L, (reducedCap a b P j + X) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hpos := hB₂_red_pos j (Finset.mem_filter.1 hj).1
          unfold reducedCap at hpos ⊢
          have hgt : 0 < b j - X := by
            by_contra hle; push Not at hle; rw [max_eq_left hle] at hpos; exact lt_irrefl _ hpos
          rw [max_eq_right hgt.le]; ring
        simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using this
      linarith
    have hL_pos : (0 : ℝ) < (L.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hL_ne
    exact lt_of_mul_lt_mul_left hL_sum hL_pos.le
  -- Finally, establish Property 1 on `P` for `f = f₁ + f₂`!
  refine ⟨hf_bip, hf_satG, fun j hj i hi hsurp hreach => ?_⟩
  -- Observe: no step in `R_P(f) - {s, t}` can go from `B₁` to `B₂` (no flow from `A₂` to `B₁`, and
  -- no equality edge from `A₁` to `B₂`).
  have hno_B₁_to_B₂ : ∀ u ∈ B₁, ∀ v ∈ B₂, ¬ ∃ g ∈ P.goods, 0 < f g u ∧ E g v := by
    rintro u huB₁ v hvB₂ ⟨g, hgP, hpos, hE⟩
    by_cases hgA₁ : g ∈ A₁
    · exact hnc g hgA₁ v hvB₂ hE
    · have hgA₂ : g ∈ A₂ := Finset.mem_sdiff.2 ⟨hgP, hgA₁⟩
      have h1 : f₁ g u = 0 := hf₁_zero g u fun h => Finset.disjoint_left.1 hdisjA h.1 hgA₂
      have h2 : f₂ g u = 0 := hf₂_zero g u fun h => (Finset.mem_sdiff.1 h.2).2 huB₁
      dsimp only [f] at hpos; linarith
  -- Case split on `j, i ∈ B₁` vs `B₂`:
  by_cases hjB₁ : j ∈ B₁
  · -- Any buyer reachable from `j ∈ B₁` MUST stay in `B₁`!
    have hstay_B₁ : ∀ u v, Relation.ReflTransGen
        (fun x y => ∃ g ∈ P.goods, 0 < f g x ∧ E g y) u v → u ∈ B₁ → v ∈ P.buyers → v ∈ B₁ := by
      intro u v huv
      induction huv with
      | refl => intro hu _; exact hu
      | @tail a c _ hac ih =>
        intro hu hcP
        obtain ⟨g, hgP, hpos, hE⟩ := hac
        have haP : a ∈ P.buyers := (hf_bip.2.1 g a hpos).2.1
        have haB₁ : a ∈ B₁ := ih hu haP
        by_contra hcNotB₁
        exact hno_B₁_to_B₂ a haB₁ c (Finset.mem_sdiff.2 ⟨hcP, hcNotB₁⟩) ⟨g, hgP, hpos, hE⟩
    have hiB₁ : i ∈ B₁ := hstay_B₁ j i hreach hjB₁ hi
    -- Since `j` reaches `i` and `j ≠ i`, the first step has `f g j > 0`, forcing `j ∈ P₁.buyers`,
    -- and every edge along the path stays inside `P₁`!
    have hne_ji : j ≠ i := fun h => lt_irrefl _ (h ▸ hsurp)
    -- Every step from `u ∈ B₁` with `0 < f g u` forces `g ∈ A₁` and `u ∈ P₁.buyers`, and if `E g v`
    -- with `v ∈ B₁`, then `v ∈ P₁.buyers`!
    have hstep_P₁ : ∀ u v, u ∈ B₁ → (∃ g ∈ P.goods, 0 < f g u ∧ E g v) →
        v ∈ B₁ → u ∈ P₁.buyers ∧ v ∈ P₁.buyers ∧ ∃ g ∈ A₁, 0 < f₁ g u ∧ E g v := by
      rintro u v huB₁ ⟨g, hgP, hpos, hE⟩ hvB₁
      have h2 : f₂ g u = 0 := hf₂_zero g u fun h => (Finset.mem_sdiff.1 h.2).2 huB₁
      have h1_pos : 0 < f₁ g u := by dsimp only [f] at hpos; linarith
      have hs := hf₁.1.2.1 g u h1_pos
      exact ⟨hs.2.1, Finset.mem_inter.2 ⟨hvB₁, mem_bipNbr.2 ⟨hB₁_sub hvB₁, g, hs.1, hE⟩⟩,
        g, hs.1, h1_pos, hE⟩
    have hlift : ∀ u v, Relation.ReflTransGen (fun x y => ∃ g ∈ P.goods, 0 < f g x ∧ E g y) u v →
        u ∈ B₁ → v ∈ B₁ → u ≠ v →
        u ∈ P₁.buyers ∧ v ∈ P₁.buyers ∧
          Relation.ReflTransGen (fun x y => ∃ g ∈ A₁, 0 < f₁ g x ∧ E g y) u v := by
      intro u v huv
      induction huv using Relation.ReflTransGen.head_induction_on with
      | refl => intro _ _ hne; exact absurd rfl hne
      | @head a c hac hcv ih =>
        intro haB₁ hvB₁ hav
        have hcP : c ∈ P.buyers := by
          rcases hac with ⟨g, hgP, hpos, hE⟩
          rcases Relation.ReflTransGen.cases_head hcv with rfl | ⟨_, hcc', _⟩
          · exact hB₁_sub hvB₁
          · obtain ⟨g', _, hpos', _⟩ := hcc'
            exact (hf_bip.2.1 g' c hpos').2.1
        have hcB₁ : c ∈ B₁ := by
          by_contra hcNotB₁
          exact hno_B₁_to_B₂ a haB₁ c (Finset.mem_sdiff.2 ⟨hcP, hcNotB₁⟩) hac
        obtain ⟨haP₁, hcP₁, hstep⟩ := hstep_P₁ a c haB₁ hac hcB₁
        by_cases hcv_eq : c = v
        · subst hcv_eq
          exact ⟨haP₁, hcP₁, Relation.ReflTransGen.single hstep⟩
        · obtain ⟨_, hvP₁, hrest⟩ := ih hcB₁ hvB₁ hcv_eq
          exact ⟨haP₁, hvP₁, Relation.ReflTransGen.head hstep hrest⟩
    obtain ⟨hjP₁, hiP₁, hreach₁⟩ := hlift j i hreach hjB₁ hiB₁ hne_ji
    rw [hf_spent_B₁' j hjP₁, hf_spent_B₁' i hiP₁] at hsurp
    exact hf₁.2.2 j hjP₁ i hiP₁ hsurp hreach₁
  · have hjB₂ : j ∈ B₂ := Finset.mem_sdiff.2 ⟨hj, hjB₁⟩
    by_cases hiB₁ : i ∈ B₁
    · -- `j ∈ B₂` has surplus `> X`, while `i ∈ B₁` has surplus `≤ X`, contradicting `hsurp`!
      linarith [hsurp_B₁_le i hiB₁, hsurp_B₂_gt j hjB₂]
    · have hiB₂ : i ∈ B₂ := Finset.mem_sdiff.2 ⟨hi, hiB₁⟩
      -- Path from `j ∈ B₂` to `i ∈ B₂` can never visit `B₁` (since `B₁` cannot return to `B₂`),
      -- so every step stays in `B₂` and uses `f₂` on `A₂`!
      have hlift₂ : ∀ u v, Relation.ReflTransGen (fun x y => ∃ g ∈ P.goods, 0 < f g x ∧ E g y) u v →
          u ∈ B₂ → v ∈ B₂ →
          Relation.ReflTransGen (fun x y => ∃ g ∈ A₂, 0 < f₂ g x ∧ E g y) u v := by
        intro u v huv
        induction huv using Relation.ReflTransGen.head_induction_on with
        | refl => intro _ _; exact .refl
        | @head a c hac hcv ih =>
          intro haB₂ hvB₂
          have hcB₂ : c ∈ B₂ := by
            by_contra hcNotB₂
            have hcP : c ∈ P.buyers := by
              rcases Relation.ReflTransGen.cases_head hcv with rfl | ⟨_, hcc', _⟩
              · exact (Finset.mem_sdiff.1 hvB₂).1
              · obtain ⟨g', _, hpos', _⟩ := hcc'
                exact (hf_bip.2.1 g' c hpos').2.1
            have hcB₁ : c ∈ B₁ := by
              by_contra hcNotB₁; exact hcNotB₂ (Finset.mem_sdiff.2 ⟨hcP, hcNotB₁⟩)
            -- From `c ∈ B₁`, `hcv` stays in `B₁`, contradicting `v ∈ B₂`!
            have hstay : ∀ x y, Relation.ReflTransGen
                (fun p q => ∃ g ∈ P.goods, 0 < f g p ∧ E g q) x y →
                x ∈ B₁ → y ∈ P.buyers → y ∈ B₁ := by
              intro x y hxy
              induction hxy with
              | refl => intro hx _; exact hx
              | @tail p q _ hpq ihs =>
                intro hx hqP
                obtain ⟨g', hg'P, hpos', hE'⟩ := hpq
                have hpB₁ := ihs hx (hf_bip.2.1 g' p hpos').2.1
                by_contra hqNotB₁
                exact hno_B₁_to_B₂ p hpB₁ q (Finset.mem_sdiff.2 ⟨hqP, hqNotB₁⟩)
                  ⟨g', hg'P, hpos', hE'⟩
            exact (Finset.mem_sdiff.1 hvB₂).2 (hstay c v hcv hcB₁ (Finset.mem_sdiff.1 hvB₂).1)
          obtain ⟨g, hgP, hpos, hE⟩ := hac
          have h1 : f₁ g a = 0 := hf₁_zero g a fun h => Finset.disjoint_right.1 hdisjB haB₂ h.2
          have h2_pos : 0 < f₂ g a := by dsimp only [f] at hpos; linarith
          have hgA₂ : g ∈ A₂ := (hf₂.1.2.1 g a h2_pos).1
          exact Relation.ReflTransGen.head ⟨g, hgA₂, h2_pos, hE⟩ (ih hcB₂ hvB₂)
      rw [hf_spent_B₂ j hjB₂, hf_spent_B₂ i hiB₂] at hsurp
      exact hf₂.2.2 j hjB₂ i hiB₂ hsurp (hlift₂ j i hreach hjB₂ hiB₂)

/-- Level-by-level divide-and-conquer balanced-flow loop in `FreeM (MaxFlowQuery I G)`
([Vazirani2007], Section 5.7.1, pp. 113–115): each recursion level issues **one** combined
max-flow query on the disjoint union `batchCap a b E ps` of all active pieces. -/
private noncomputable def balancedFlowLoop (a : G → ℝ) (b : I → ℝ) (E : G → I → Prop) :
    ℕ → List (BipPiece I G) → FreeM (MaxFlowQuery I G) (G → I → ℝ)
  | 0, _ => pure 0
  | _, [] => pure 0
  | k + 1, ps => do
      let W := batchCap a b E ps
      let F ← FreeM.lift (.maxFlow W)
      let S := maxMinCut W F
      let nextPs : List (BipPiece I G) := ps.flatMap fun P =>
        let A₁ := cutGoods P.goods S
        let B₁ := cutBuyers P.buyers S
        if A₁ = P.goods ∧ B₁ = P.buyers then []
        else [⟨A₁, B₁ ∩ bipNbr P.buyers E A₁⟩, ⟨P.goods \ A₁, P.buyers \ B₁⟩]
      let fNext ← balancedFlowLoop a b E k nextPs
      pure fun g i =>
        fNext g i +
          open scoped Classical in
          if ∃ P ∈ ps, cutGoods P.goods S = P.goods ∧ cutBuyers P.buyers S = P.buyers ∧
              g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0

/-- **Divide-and-conquer balanced-flow program** ([Vazirani2007], Section 5.7.1, pp. 113–115):
runs `balancedFlowLoop` for at most `Fintype.card G` max-flow oracle queries on `N(p)`. -/
noncomputable def balancedFlowProgram (M : LinearFisherMarket I G) (p : G → ℝ) :
    FreeM (MaxFlowQuery I G) (G → I → ℝ) :=
  if (Finset.univ : Finset G).Nonempty then
    balancedFlowLoop (fun g => p g * M.supply g) M.budget (fun g i => M.IsEqualityEdge p i g)
      (Fintype.card G) [⟨Finset.univ, M.buyerNeighborhood p Finset.univ⟩]
  else pure 0

/-- Inductive specification of `balancedFlowLoop`: when `ps` is a pairwise vertex-disjoint list of
valid pieces with `P.goods.card ≤ k` for all `P ∈ ps`, `balancedFlowLoop` uses at most `k`
max-flow queries and outputs a flow supported on `ps` whose restriction to each `P ∈ ps` is
piece-balanced. -/
private theorem balancedFlowLoop_spec {a : G → ℝ} {b : I → ℝ} {E : G → I → Prop}
    (ha : ∀ g, 0 ≤ a g) (hb : ∀ i, 0 ≤ b i)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    ∀ (k : ℕ) (ps : List (BipPiece I G)),
      PairwiseDisjointPieces ps →
      (∀ P ∈ ps, ValidPiece a b E P ∧ P.goods.card ≤ k) →
      let f := (balancedFlowLoop a b E k ps).eval oracle
      (balancedFlowLoop a b E k ps).countQueries oracle ≤ k ∧
      (∀ g i, 0 ≤ f g i) ∧
      (∀ g i, 0 < f g i → ∃ P ∈ ps, g ∈ P.goods ∧ i ∈ P.buyers) ∧
      ∀ P ∈ ps, IsPieceBalanced a b E P
        (fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then f g i else 0) := by
  classical
  intro k
  induction k with
  | zero =>
    intro ps _ hvalid
    have hnil : ps = [] := by
      cases ps with
      | nil => rfl
      | cons P _ =>
        have h1 := (hvalid P List.mem_cons_self).1.1
        have h2 := (hvalid P List.mem_cons_self).2
        have := Finset.card_pos.2 h1
        omega
    subst hnil
    simp [balancedFlowLoop]
  | succ k ih =>
    intro ps hdisj hvalid
    cases ps with
    | nil => simp [balancedFlowLoop]
    | cons P₀ tl =>
      let ps' := P₀ :: tl
      set W := batchCap a b E ps'
      set F := oracle (.maxFlow W)
      have hF_spec := horacle W (batchCap_nonneg ha)
      have hF : IsFeasibleRealFlow W .source .sink F := hF_spec.1
      have hFmax : IsMaxRealFlow W .source .sink (realNetOut F .source) := hF_spec.2
      set S := maxMinCut W F
      let nextStep : BipPiece I G → List (BipPiece I G) := fun P =>
        let A₁ := cutGoods P.goods S
        let B₁ := cutBuyers P.buyers S
        if A₁ = P.goods ∧ B₁ = P.buyers then []
        else [⟨A₁, B₁ ∩ bipNbr P.buyers E A₁⟩, ⟨P.goods \ A₁, P.buyers \ B₁⟩]
      let nextPs := ps'.flatMap nextStep
      -- Verify `PairwiseDisjointPieces nextPs` and `∀ Q ∈ nextPs, ValidPiece Q ∧ Q.goods.card ≤ k`.
      have hnext_sub : ∀ P ∈ ps', ∀ Q ∈ nextStep P, Q.goods ⊆ P.goods ∧ Q.buyers ⊆ P.buyers := by
        intro P _ Q hQ
        dsimp only [nextStep] at hQ
        split_ifs at hQ with hc
        · simp at hQ
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl
          · exact ⟨Finset.filter_subset _ _,
              Finset.inter_subset_left.trans (Finset.filter_subset _ _)⟩
          · exact ⟨Finset.sdiff_subset, Finset.sdiff_subset⟩
      have hnext_valid : ∀ Q ∈ nextPs, ValidPiece a b E Q ∧ Q.goods.card ≤ k := by
        intro Q hQ
        obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
        obtain ⟨hFP_feas, hFP_max, hcutG, hcutB⟩ := batch_restrict ha hdisj hF hFmax hP
        dsimp only [nextStep] at hQP
        split_ifs at hQP with hc
        · simp at hQP
        · have hc' : ¬ (cutGoods P.goods
              (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E)
                (toRealFlow fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0))
              = P.goods ∧
            cutBuyers P.buyers
              (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E)
                (toRealFlow fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0))
              = P.buyers) := by
            rwa [← hcutG, ← hcutB]
          obtain ⟨hP₁_v, hP₂_v, hlt₁, hlt₂, -, -, -⟩ :=
            case2_split_and_combine ha hb (hvalid P hP).1 hFP_feas hFP_max hc'
          simp only [← hcutG, ← hcutB] at hP₁_v hP₂_v hlt₁ hlt₂
          have hcardP := (hvalid P hP).2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hQP
          rcases hQP with rfl | rfl
          · exact ⟨hP₁_v, by dsimp only [S, W, ps'] at hlt₁ ⊢; omega⟩
          · exact ⟨hP₂_v, by dsimp only [S, W, ps'] at hlt₂ ⊢; omega⟩
      have hnext_disj : PairwiseDisjointPieces nextPs := by
        have hflat : ∀ (L : List (BipPiece I G)), PairwiseDisjointPieces L →
            (∀ P ∈ L, PairwiseDisjointPieces (nextStep P)) →
            (∀ P ∈ L, ∀ Q ∈ nextStep P, Q.goods ⊆ P.goods ∧ Q.buyers ⊆ P.buyers) →
            PairwiseDisjointPieces (L.flatMap nextStep) := by
          intro L
          induction L with
          | nil => intro _ _ _; simp [PairwiseDisjointPieces]
          | cons P rest ihL =>
            intro hLd hstep hsub
            rw [PairwiseDisjointPieces, List.pairwise_cons] at hLd
            rw [List.flatMap_cons, PairwiseDisjointPieces, List.pairwise_append]
            refine ⟨hstep P List.mem_cons_self,
              ihL hLd.2 (fun R hR => hstep R (List.mem_cons_of_mem _ hR))
                (fun R hR => hsub R (List.mem_cons_of_mem _ hR)), ?_⟩
            intro Q₁ hQ₁ Q₂ hQ₂
            obtain ⟨R, hR, hQ₂R⟩ := List.mem_flatMap.1 hQ₂
            have hsub1 := hsub P List.mem_cons_self Q₁ hQ₁
            have hsub2 := hsub R (List.mem_cons_of_mem _ hR) Q₂ hQ₂R
            have hPR := hLd.1 R hR
            exact ⟨hPR.1.mono hsub1.1 hsub2.1, hPR.2.mono hsub1.2 hsub2.2⟩
        refine hflat ps' hdisj (fun P hP => ?_) hnext_sub
        dsimp only [nextStep]
        split_ifs with hc
        · simp [PairwiseDisjointPieces]
        · refine List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h => by simp at h) .nil)
          intro Q hQ
          rw [List.mem_singleton.1 hQ]
          exact ⟨Finset.disjoint_sdiff, Finset.disjoint_sdiff.mono_left Finset.inter_subset_left⟩
      obtain ⟨hih_q, hih_nn, hih_supp, hih_bal⟩ := ih nextPs hnext_disj hnext_valid
      set fNext := (balancedFlowLoop a b E k nextPs).eval oracle
      let fDone : G → I → ℝ := fun g i =>
        if ∃ P ∈ ps', cutGoods P.goods S = P.goods ∧ cutBuyers P.buyers S = P.buyers ∧
            g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0
      have hcount_eq : (balancedFlowLoop a b E (k + 1) ps').countQueries oracle =
          1 + (balancedFlowLoop a b E k nextPs).countQueries oracle := by
        change (FreeM.lift (.maxFlow W) >>= fun F' => _).countQueries oracle = _
        rw [FreeM.countQueries_liftBind]
        dsimp only
        rw [FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
      have heval_eq : (balancedFlowLoop a b E (k + 1) ps').eval oracle =
          fun g i => fNext g i + fDone g i := by
        change (FreeM.lift (.maxFlow W) >>= fun F' => _).eval oracle = _
        rw [FreeM.eval_liftBind]
        dsimp only
        rw [FreeM.eval_bind, FreeM.eval_pure]
      rw [hcount_eq, heval_eq]
      have hfDone_nn : ∀ g i, 0 ≤ fDone g i := fun g i => by
        dsimp only [fDone]; split_ifs <;> first | exact hF.1 _ _ | exact le_rfl
      refine ⟨by omega, fun g i => add_nonneg (hih_nn g i) (hfDone_nn g i), fun g i hpos => ?_,
        fun P hP => ?_⟩
      · rcases (hih_nn g i).eq_or_lt with h0 | h1
        · have h2 : 0 < fDone g i := by linarith
          dsimp only [fDone] at h2
          split_ifs at h2 with hex
          · obtain ⟨P, hP, -, -, hgP, hiP⟩ := hex
            exact ⟨P, hP, hgP, hiP⟩
          · exact (lt_irrefl (0 : ℝ) h2).elim
        · obtain ⟨Q, hQ, hgQ, hiQ⟩ := hih_supp g i h1
          obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
          have hsub := hnext_sub P hP Q hQP
          exact ⟨P, hP, hsub.1 hgQ, hsub.2 hiQ⟩
      · obtain ⟨hFP_feas, hFP_max, hcutG, hcutB⟩ := batch_restrict ha hdisj hF hFmax hP
        by_cases hc : cutGoods P.goods S = P.goods ∧ cutBuyers P.buyers S = P.buyers
        · -- Case 1: `P` finished at this level; `fNext` is 0 on `P` and `fDone` matches `F`.
          have hrest_eq : (fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then fNext g i + fDone g i
              else 0) = ofRealFlow (toRealFlow fun g i =>
                if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0) := by
            ext g i
            by_cases hgi : g ∈ P.goods ∧ i ∈ P.buyers
            · have hfNext0 : fNext g i = 0 := by
                refine le_antisymm (not_lt.1 fun hpos => ?_) (hih_nn g i)
                obtain ⟨Q, hQ, hgQ, _⟩ := hih_supp g i hpos
                obtain ⟨R, hR, hQR⟩ := List.mem_flatMap.1 hQ
                have hsub := hnext_sub R hR Q hQR
                by_cases hRP : R = P
                · subst hRP; simp [nextStep, hc] at hQR
                · exact Finset.disjoint_left.1 (hdisj.disjoint_of_ne hR hP hRP).1 (hsub.1 hgQ) hgi.1
              have hfDone_eq : fDone g i = ofRealFlow F g i := by
                dsimp only [fDone]
                exact ite_eq_left_iff.2 fun h => absurd ⟨P, hP, hc.1, hc.2, hgi.1, hgi.2⟩ h
              simp [hgi, hfNext0, hfDone_eq, ofRealFlow, toRealFlow]
            · simp [hgi, ofRealFlow, toRealFlow]
          rw [hrest_eq]
          exact isPieceBalanced_case1 ha hb (hvalid P hP).1 hFP_feas hFP_max
            (hcutG.symm.trans hc.1) (hcutB.symm.trans hc.2)
        · -- Case 2: `P` split into `P₁` and `P₂` in `nextPs`; `fDone` is 0 on `P`.
          have hc' : ¬ (cutGoods P.goods
              (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E)
                (toRealFlow fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0))
              = P.goods ∧
            cutBuyers P.buyers
              (maxMinCut (bipCap P.goods P.buyers a (reducedCap a b P) E)
                (toRealFlow fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then ofRealFlow F g i else 0))
              = P.buyers) := by
            rwa [← hcutG, ← hcutB]
          obtain ⟨-, -, -, -, -, -, hcomb⟩ :=
            case2_split_and_combine ha hb (hvalid P hP).1 hFP_feas hFP_max hc'
          rw [← hcutG, ← hcutB] at hcomb
          let P₁ : BipPiece I G := ⟨cutGoods P.goods S,
            cutBuyers P.buyers S ∩ bipNbr P.buyers E (cutGoods P.goods S)⟩
          let P₂ : BipPiece I G := ⟨P.goods \ cutGoods P.goods S, P.buyers \ cutBuyers P.buyers S⟩
          have hP₁_mem : P₁ ∈ nextPs := List.mem_flatMap.2 ⟨P, hP, by simp [nextStep, hc, P₁]⟩
          have hP₂_mem : P₂ ∈ nextPs := List.mem_flatMap.2 ⟨P, hP, by simp [nextStep, hc, P₂]⟩
          have hf₁ := hih_bal P₁ hP₁_mem
          have hf₂ := hih_bal P₂ hP₂_mem
          have hcomb_eq : (fun g i => if g ∈ P.goods ∧ i ∈ P.buyers then fNext g i + fDone g i
              else 0) = fun g i =>
                (if g ∈ P₁.goods ∧ i ∈ P₁.buyers then fNext g i else 0) +
                (if g ∈ P₂.goods ∧ i ∈ P₂.buyers then fNext g i else 0) := by
            ext g i
            by_cases hgi : g ∈ P.goods ∧ i ∈ P.buyers
            · have hfDone0 : fDone g i = 0 := by
                dsimp only [fDone]
                refine ite_eq_right_iff.2 fun hex => ?_
                obtain ⟨R, hR, hRc1, hRc2, hgR, _⟩ := hex
                by_cases hRP : R = P
                · subst hRP; exact absurd ⟨hRc1, hRc2⟩ hc
                · exact absurd hgR
                    (Finset.disjoint_right.1 (hdisj.disjoint_of_ne hR hP hRP).1 hgi.1)
              rw [ite_eq_left_iff.2 fun h => absurd hgi h, hfDone0, add_zero]
              by_cases h1 : g ∈ P₁.goods ∧ i ∈ P₁.buyers
              · have h2 : ¬ (g ∈ P₂.goods ∧ i ∈ P₂.buyers) := fun h =>
                  (Finset.mem_sdiff.1 h.1).2 h1.1
                simp [h1, h2]
              · by_cases h2 : g ∈ P₂.goods ∧ i ∈ P₂.buyers
                · simp [h1, h2]
                · simp only [h1, h2, ↓reduceIte, add_zero]
                  -- Neither in `P₁` nor in `P₂`, so `fNext g i = 0`!
                  refine le_antisymm (not_lt.1 fun hpos => ?_) (hih_nn g i)
                  obtain ⟨Q, hQ, hgQ, hiQ⟩ := hih_supp g i hpos
                  obtain ⟨R, hR, hQR⟩ := List.mem_flatMap.1 hQ
                  have hsub := hnext_sub R hR Q hQR
                  have hRP : R = P := by
                    by_contra hne
                    exact Finset.disjoint_left.1 (hdisj.disjoint_of_ne hR hP hne).1
                      (hsub.1 hgQ) hgi.1
                  subst hRP
                  dsimp only [nextStep] at hQR
                  rw [ite_eq_right_iff.2 fun h => absurd h hc] at hQR
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQR
                  rcases hQR with rfl | rfl
                  · exact h1 ⟨hgQ, hiQ⟩
                  · exact h2 ⟨hgQ, hiQ⟩
            · have h1 : ¬ (g ∈ P₁.goods ∧ i ∈ P₁.buyers) := fun h =>
                hgi ⟨Finset.filter_subset _ _ h.1,
                  (Finset.inter_subset_left.trans (Finset.filter_subset _ _)) h.2⟩
              have h2 : ¬ (g ∈ P₂.goods ∧ i ∈ P₂.buyers) := fun h =>
                hgi ⟨Finset.sdiff_subset h.1, Finset.sdiff_subset h.2⟩
              simp [hgi, h1, h2]
          rw [hcomb_eq]
          exact hcomb _ _ hf₁ hf₂

/-- **Theorem 5.8 (together with Lemmas 5.6 and 5.7)** ([Vazirani2007], Section 5.7.1,
pp. 113–115): when `N(p)` satisfies the Invariant (`M.SatisfiesInvariant p`) at nonnegative prices
`p`, the divide-and-conquer program `M.balancedFlowProgram p` evaluated with any valid max-flow
oracle outputs a balanced maximum flow in `N(p)` while making at most `Fintype.card G` max-flow
oracle calls. -/
theorem balancedFlowProgram_spec {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hinv : M.SatisfiesInvariant p)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    let f := (M.balancedFlowProgram p).eval oracle
    M.IsMaxEqualityFlow p f ∧
      M.IsBalancedFlow p f ∧
      (M.balancedFlowProgram p).countQueries oracle ≤ Fintype.card G := by
  classical
  dsimp only [balancedFlowProgram]
  split_ifs with hG
  · let P₀ : BipPiece I G := ⟨Finset.univ, M.buyerNeighborhood p Finset.univ⟩
    have hP₀_valid : ValidPiece (fun g => p g * M.supply g) M.budget
        (fun g i => M.IsEqualityEdge p i g) P₀ := by
      refine ⟨hG, fun i hi => ?_, fun S _ => ?_⟩
      · obtain ⟨g, -, hE⟩ := mem_buyerNeighborhood.1 hi
        exact ⟨g, Finset.mem_univ g, hE⟩
      · have hnbr : bipNbr (M.buyerNeighborhood p Finset.univ)
            (fun g i => M.IsEqualityEdge p i g) S = M.buyerNeighborhood p S := by
          ext i
          simp only [mem_bipNbr, mem_buyerNeighborhood, Finset.mem_univ, true_and]
          exact ⟨fun ⟨_, g, hgS, hE⟩ => ⟨g, hgS, hE⟩,
            fun ⟨g, hgS, hE⟩ => ⟨⟨g, hE⟩, g, hgS, hE⟩⟩
        rw [hnbr]
        exact (satisfiesInvariant_iff hp).1 hinv S
    have hdisj : PairwiseDisjointPieces [P₀] := by simp [PairwiseDisjointPieces]
    obtain ⟨hq, hf_nn, hf_supp, hbal_all⟩ := balancedFlowLoop_spec
      (fun g => mul_nonneg (hp g) (M.supply_nonneg g)) M.budget_nonneg horacle
      (Fintype.card G) [P₀] hdisj (fun P hP => by
        rw [List.mem_singleton.1 hP]; exact ⟨hP₀_valid, by simp [P₀]⟩)
    set f := (balancedFlowLoop (fun g => p g * M.supply g) M.budget
      (fun g i => M.IsEqualityEdge p i g) (Fintype.card G) [P₀]).eval oracle
    have hf_eq : (fun g i => if g ∈ P₀.goods ∧ i ∈ P₀.buyers then f g i else 0) = f := by
      ext g i
      by_cases hi : i ∈ P₀.buyers
      · simp [P₀, hi]
      · simp only [P₀, Finset.mem_univ, hi, and_false, ↓reduceIte]
        symm
        refine le_antisymm (not_lt.1 fun hpos => ?_) (hf_nn g i)
        obtain ⟨Q, hQ, -, hiQ⟩ := hf_supp g i hpos
        rw [List.mem_singleton.1 hQ] at hiQ
        exact hi hiQ
    have hPB : IsPieceBalanced (fun g => p g * M.supply g) M.budget
        (fun g i => M.IsEqualityEdge p i g) P₀ f := by
      rw [← hf_eq]
      exact hbal_all P₀ List.mem_cons_self
    have hf_feas : M.IsEqualityFlow p f := by
      refine ⟨hPB.1.1, fun g i hpos => (hPB.1.2.1 g i hpos).2.2, fun g => ?_, fun i => ?_⟩
      · calc
          ∑ i : I, f g i = ∑ i ∈ P₀.buyers, f g i := by
            symm
            exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
              le_antisymm (not_lt.1 fun hpos => hi (hPB.1.2.1 g i hpos).2.1) (hPB.1.1 g i)
          _ ≤ p g * M.supply g := (hPB.2.1 g (Finset.mem_univ g)).le
      · by_cases hi : i ∈ P₀.buyers
        · exact hPB.1.2.2.2 i hi
        · have h0 : ∑ g : G, f g i = 0 := Finset.sum_eq_zero fun g _ =>
            le_antisymm (not_lt.1 fun hpos => hi (hPB.1.2.1 g i hpos).2.1) (hPB.1.1 g i)
          rw [h0]; exact M.budget_nonneg i
    -- Lemma 5.6: `f` saturates every good `g`, hence is a max-flow in `N(p)`!
    have hf_max : M.IsMaxEqualityFlow p f := by
      refine ⟨hf_feas, fun f' hf' => ?_⟩
      calc
        flowValue f' ≤ ∑ g : G, p g * M.supply g :=
          Finset.sum_le_sum fun g _ => hf'.2.2.1 g
        _ = ∑ g : G, ∑ i ∈ P₀.buyers, f g i :=
          Finset.sum_congr rfl fun g _ => (hPB.2.1 g (Finset.mem_univ g)).symm
        _ = flowValue f := Finset.sum_congr rfl fun g _ =>
          (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
            le_antisymm (not_lt.1 fun hpos => hi (hPB.1.2.1 g i hpos).2.1) (hPB.1.1 g i))
    have hf_prop1 : M.SatisfiesPropertyOne p f := by
      intro j i hsurp hreach
      have hne_ji : j ≠ i := fun h => lt_irrefl _ (h ▸ hsurp)
      have hj_in : j ∈ P₀.buyers := by
        rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨_, huv, _⟩
        · exact absurd rfl hne_ji
        · obtain ⟨g, hpos, _⟩ := huv
          exact (hPB.1.2.1 g j hpos).2.1
      have hi_in : i ∈ P₀.buyers := by
        cases hreach with
        | refl => exact absurd rfl hne_ji
        | @tail _ _ _ hlast =>
          obtain ⟨g, _, hE⟩ := hlast
          exact mem_buyerNeighborhood.2 ⟨g, Finset.mem_univ g, hE⟩
      have hreach_P₀ : Relation.ReflTransGen
          (fun u v => ∃ g ∈ P₀.goods, 0 < f g u ∧ M.IsEqualityEdge p v g) j i := by
        have hlift : ∀ a b,
            Relation.ReflTransGen (fun u v => ∃ g, 0 < f g u ∧ M.IsEqualityEdge p v g) a b →
            Relation.ReflTransGen
              (fun u v => ∃ g ∈ P₀.goods, 0 < f g u ∧ M.IsEqualityEdge p v g) a b := by
          intro a b hab
          induction hab with
          | refl => exact .refl
          | @tail _ _ _ hbc ih =>
            obtain ⟨g, hpos, hE⟩ := hbc
            exact ih.tail ⟨g, Finset.mem_univ g, hpos, hE⟩
        exact hlift j i hreach
      exact hPB.2.2 j hj_in i hi_in hsurp hreach_P₀
    exact ⟨hf_max, (isBalancedFlow_iff_satisfiesPropertyOne hf_max).2 hf_prop1, hq⟩
  · -- Empty goods type: `f = 0` is trivially balanced in `0` queries.
    have hG_empty : IsEmpty G := ⟨fun g => hG ⟨g, Finset.mem_univ g⟩⟩
    have hf0 : M.IsEqualityFlow p 0 :=
      ⟨fun _ _ => le_rfl, fun _ _ h => (lt_irrefl (0 : ℝ) h).elim,
        fun g => isEmptyElim g, fun i => by simp [M.budget_nonneg i]⟩
    have hmax0 : M.IsMaxEqualityFlow p 0 :=
      ⟨hf0, fun f' _ => by simp [flowValue]⟩
    have hbal0 : M.IsBalancedFlow p 0 :=
      ⟨hf0, fun f' _ => by simp [surplusSqNorm, surplus]⟩
    exact ⟨hmax0, hbal0, by simp⟩

end DivideAndConquerBalancedFlow

/-! ### Section 5.9: Finding tight sets (`Lemmas 5.9–5.11`) -/

section FindingTightSets

variable {I G : Type u}

/-- Scaled bipartite equality subnetwork `N(x · p)` restricted to active goods `A` and their
equality neighborhood `M.buyerNeighborhood p A` ([Vazirani2007], Section 5.9, pp. 117–118). When
`0 < x`, `A = Finset.univ`, and `M.buyerNeighborhood p Finset.univ = Finset.univ`, this coincides
with `M.equalityNetwork (x • p)`. -/
noncomputable def scaledSubnetwork [Fintype I] (M : LinearFisherMarket I G) (p : G → ℝ)
    (A : Finset G) (x : ℝ) : FlowVertex I G → FlowVertex I G → ℝ :=
  bipCap A (M.buyerNeighborhood p A) (fun g => x * (p g * M.supply g)) M.budget
    (fun g i => M.IsEqualityEdge p i g)

theorem scaledSubnetwork_nonneg [Fintype I] {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} {x : ℝ} (hx : 0 ≤ x) (hp : ∀ g ∈ A, 0 ≤ p g) (u v : FlowVertex I G) :
    0 ≤ M.scaledSubnetwork p A x u v :=
  bipCap_nonneg (fun g hg => mul_nonneg hx (mul_nonneg (hp g hg) (M.supply_nonneg g)))
    (fun i _ => M.budget_nonneg i) u v

theorem cutWeight_scaledSubnetwork_source [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
    (M : LinearFisherMarket I G) (p : G → ℝ) (A : Finset G) (x : ℝ) :
    cutWeight (M.scaledSubnetwork p A x) ({.source} : Finset (FlowVertex I G)) =
      x * M.goodValue p A := by
  rw [scaledSubnetwork, cutWeight_bipCap_source, goodValue, Finset.mul_sum]

theorem scaledSubnetwork_univ_eq_equalityNetwork [Fintype I] [Fintype G]
    {M : LinearFisherMarket I G} {p : G → ℝ} {x : ℝ} (hx : 0 < x)
    (hcover : M.buyerNeighborhood p Finset.univ = Finset.univ) :
    M.scaledSubnetwork p Finset.univ x = M.equalityNetwork (x • p) := by
  classical
  ext u v
  have hcap_eq : (fun g => x * (p g * M.supply g)) = fun g => (x • p) g * M.supply g := by
    ext g; simp [smul_eq_mul, mul_assoc]
  have hE_eq : (fun g i => M.IsEqualityEdge p i g) = fun g i => M.IsEqualityEdge (x • p) i g := by
    ext g i; exact (isEqualityEdge_smul hx i g).symm
  simp only [scaledSubnetwork, equalityNetwork, hcover, hcap_eq, hE_eq]

private theorem nonempty_powerset_filter {A : Finset G} (hA : A.Nonempty) :
    (A.powerset.filter Finset.Nonempty).Nonempty :=
  ⟨A, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.Subset.rfl, hA⟩⟩

/-- Minimum ratio `x* = min_{∅ ≠ S ⊆ A} m(Γ(S)) / p(S)` at which a nonempty subset of `A` goes
tight under uniform price scaling ([Vazirani2007], Section 5.9, p. 117). -/
noncomputable def minTightRatio [Fintype I] (M : LinearFisherMarket I G) (p : G → ℝ)
    (A : Finset G) (hA : A.Nonempty) : ℝ :=
  (A.powerset.filter Finset.Nonempty).inf' (nonempty_powerset_filter hA)
    fun S => M.budgetSum (M.buyerNeighborhood p S) / M.goodValue p S

/-- Unique maximal subset `S* ⊆ A` going tight at scale `x* = M.minTightRatio p A hA`
([Vazirani2007], Section 5.9, p. 117). -/
noncomputable def tightSetAtMinRatio [Fintype I] [DecidableEq G] (M : LinearFisherMarket I G)
    (p : G → ℝ) (A : Finset G) (hA : A.Nonempty) : Finset G :=
  open scoped Classical in
  (A.powerset.filter fun S =>
    M.minTightRatio p A hA * M.goodValue p S = M.budgetSum (M.buyerNeighborhood p S)).biUnion id

private theorem goodValue_pos_of_nonempty {M : LinearFisherMarket I G} {p : G → ℝ}
    {A S : Finset G} (hp : ∀ g ∈ A, 0 < p g * M.supply g) (hSA : S ⊆ A) (hS : S.Nonempty) :
    0 < M.goodValue p S := by
  obtain ⟨g₀, hg₀⟩ := hS
  exact (hp g₀ (hSA hg₀)).trans_le
    (Finset.single_le_sum (fun g hg => (hp g (hSA hg)).le) hg₀)

theorem minTightRatio_nonneg [Fintype I] {M : LinearFisherMarket I G} {p : G → ℝ} {A : Finset G}
    (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g) :
    0 ≤ M.minTightRatio p A hA := by
  unfold minTightRatio
  rw [Finset.le_inf'_iff]
  intro S hS
  obtain ⟨hSA, hSne⟩ := Finset.mem_filter.1 hS
  exact div_nonneg (Finset.sum_nonneg fun i _ => M.budget_nonneg i)
    (goodValue_pos_of_nonempty hp (Finset.mem_powerset.1 hSA) hSne).le

theorem minTightRatio_mul_goodValue_le [Fintype I] {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g)
    {S : Finset G} (hSA : S ⊆ A) :
    M.minTightRatio p A hA * M.goodValue p S ≤ M.budgetSum (M.buyerNeighborhood p S) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp [goodValue, budgetSum, buyerNeighborhood, bipNbr_empty]
  · have hmem : S ∈ A.powerset.filter Finset.Nonempty :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSA, hSne⟩
    have hle : M.minTightRatio p A hA ≤
        M.budgetSum (M.buyerNeighborhood p S) / M.goodValue p S :=
      Finset.inf'_le _ hmem
    exact (le_div_iff₀ (goodValue_pos_of_nonempty hp hSA hSne)).1 hle

theorem tightSetAtMinRatio_spec [Fintype I] [DecidableEq G] {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g) :
    let xStar := M.minTightRatio p A hA
    let SStar := M.tightSetAtMinRatio p A hA
    SStar ⊆ A ∧ SStar.Nonempty ∧
      xStar * M.goodValue p SStar = M.budgetSum (M.buyerNeighborhood p SStar) ∧
      ∀ S ⊆ A, xStar * M.goodValue p S = M.budgetSum (M.buyerNeighborhood p S) → S ⊆ SStar := by
  classical
  intro xStar SStar
  have hsubA : SStar ⊆ A := by
    intro g hg
    obtain ⟨S, hS, hgS⟩ := Finset.mem_biUnion.1 hg
    exact Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1 hgS
  have hmax_sub : ∀ S ⊆ A,
      xStar * M.goodValue p S = M.budgetSum (M.buyerNeighborhood p S) → S ⊆ SStar := by
    intro S hSA htight g hg
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSA, htight⟩, hg⟩
  have hne : SStar.Nonempty := by
    obtain ⟨S₀, hS₀_mem, hS₀_eq⟩ := Finset.exists_mem_eq_inf' (nonempty_powerset_filter hA)
      (fun S => M.budgetSum (M.buyerNeighborhood p S) / M.goodValue p S)
    obtain ⟨hS₀A, hS₀ne⟩ := Finset.mem_filter.1 hS₀_mem
    have hS₀A' : S₀ ⊆ A := Finset.mem_powerset.1 hS₀A
    have htight : xStar * M.goodValue p S₀ = M.budgetSum (M.buyerNeighborhood p S₀) := by
      have hpos := goodValue_pos_of_nonempty hp hS₀A' hS₀ne
      exact (eq_div_iff hpos.ne').1 hS₀_eq
    exact hS₀ne.mono (hmax_sub S₀ hS₀A' htight)
  have hunion_tight : ∀ S₁ S₂ : Finset G, S₁ ⊆ A → S₂ ⊆ A →
      xStar * M.goodValue p S₁ = M.budgetSum (M.buyerNeighborhood p S₁) →
      xStar * M.goodValue p S₂ = M.budgetSum (M.buyerNeighborhood p S₂) →
      xStar * M.goodValue p (S₁ ∪ S₂) = M.budgetSum (M.buyerNeighborhood p (S₁ ∪ S₂)) := by
    intro S₁ S₂ h₁A h₂A h₁ h₂
    have hval : M.goodValue p (S₁ ∪ S₂) + M.goodValue p (S₁ ∩ S₂) =
        M.goodValue p S₁ + M.goodValue p S₂ := Finset.sum_union_inter
    have hnbr_sub := budgetSum_buyerNeighborhood_union_add_inter_le M p S₁ S₂
    have hle_u := minTightRatio_mul_goodValue_le hA hp (Finset.union_subset h₁A h₂A)
    have hle_i := minTightRatio_mul_goodValue_le hA hp
      ((Finset.inter_subset_left (s₁ := S₁) (s₂ := S₂)).trans h₁A)
    have hvalx : xStar * M.goodValue p (S₁ ∪ S₂) + xStar * M.goodValue p (S₁ ∩ S₂) =
        xStar * M.goodValue p S₁ + xStar * M.goodValue p S₂ := by
      rw [← mul_add, ← mul_add, hval]
    change xStar * M.goodValue p (S₁ ∪ S₂) ≤ _ at hle_u
    change xStar * M.goodValue p (S₁ ∩ S₂) ≤ _ at hle_i
    linarith
  have htight_SStar : xStar * M.goodValue p SStar = M.budgetSum (M.buyerNeighborhood p SStar) := by
    have hbi : ∀ (F : Finset (Finset G)),
        (∀ S ∈ F, S ⊆ A ∧ xStar * M.goodValue p S = M.budgetSum (M.buyerNeighborhood p S)) →
        F.biUnion id ⊆ A ∧
          xStar * M.goodValue p (F.biUnion id) =
            M.budgetSum (M.buyerNeighborhood p (F.biUnion id)) := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        intro _
        simp [goodValue, budgetSum, buyerNeighborhood, bipNbr_empty]
      | @insert S F _ ih =>
        intro hF
        have hS := hF S (Finset.mem_insert_self S F)
        have hrest := ih fun T hT => hF T (Finset.mem_insert_of_mem hT)
        rw [Finset.biUnion_insert]
        exact ⟨Finset.union_subset hS.1 hrest.1, hunion_tight S _ hS.1 hrest.1 hS.2 hrest.2⟩
    exact (hbi _ fun S hS =>
      ⟨Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1, (Finset.mem_filter.1 hS).2⟩).2
  exact ⟨hsubA, hne, htight_SStar, hmax_sub⟩

private theorem bipNbr_sub_eq_buyerNeighborhood [Fintype I] {M : LinearFisherMarket I G}
    {p : G → ℝ} {A S : Finset G} (hSA : S ⊆ A) :
    bipNbr (M.buyerNeighborhood p A) (fun g i => M.IsEqualityEdge p i g) S =
      M.buyerNeighborhood p S := by
  ext i
  simp only [mem_bipNbr, mem_buyerNeighborhood]
  exact ⟨fun ⟨_, g, hgS, hE⟩ => ⟨g, hgS, hE⟩,
    fun ⟨g, hgS, hE⟩ => ⟨⟨g, hSA hgS, hE⟩, g, hgS, hE⟩⟩

variable [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- **Lemma 5.9 (part 1)** ([Vazirani2007], Section 5.9, p. 117): if `0 ≤ x ≤ x*`, then the source
cut `({.source}, A ∪ Γ(A) ∪ {.sink})` is a minimum `s`–`t` cut in `N(x · p)`. -/
theorem minCut_scaledSubnetwork_of_le_minTightRatio {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ M.minTightRatio p A hA) :
    cutWeight (M.scaledSubnetwork p A x) ({.source} : Finset (FlowVertex I G)) =
      minRealCutBetween (M.scaledSubnetwork p A x) .source .sink := by
  rw [scaledSubnetwork, source_minCut_bipCap_iff
    (fun g hg => mul_nonneg hx0 (hp g hg).le) (fun i _ => M.budget_nonneg i)]
  intro S hSA
  rw [← Finset.mul_sum, bipNbr_sub_eq_buyerNeighborhood hSA]
  have hgv_nn : 0 ≤ M.goodValue p S :=
    Finset.sum_nonneg fun g hg => (hp g (hSA hg)).le
  exact (mul_le_mul_of_nonneg_right hx hgv_nn).trans (minTightRatio_mul_goodValue_le hA hp hSA)

/-- **Lemma 5.9 (part 2)** ([Vazirani2007], Section 5.9, pp. 117–118): if `x > x*`, then
`({.source}, A ∪ Γ(A) ∪ {.sink})` is **not** a minimum `s`–`t` cut in `N(x · p)`, and for **every**
minimum `s`–`t` cut `X` in `N(x · p)`, the maximal tight set `S*` is contained in the goods on the
source side of `X` (`S* ⊆ A.filter (fun g => .good g ∈ X)`). -/
theorem not_minCut_and_subset_of_minTightRatio_lt {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g)
    {x : ℝ} (hx : M.minTightRatio p A hA < x) :
    cutWeight (M.scaledSubnetwork p A x) ({.source} : Finset (FlowVertex I G)) ≠
        minRealCutBetween (M.scaledSubnetwork p A x) .source .sink ∧
      ∀ X : Finset (FlowVertex I G), FlowVertex.source ∈ X → FlowVertex.sink ∉ X →
        cutWeight (M.scaledSubnetwork p A x) X =
          minRealCutBetween (M.scaledSubnetwork p A x) .source .sink →
        M.tightSetAtMinRatio p A hA ⊆ A.filter fun g => .good g ∈ X := by
  classical
  have hx0 : 0 ≤ x := (minTightRatio_nonneg hA hp).trans hx.le
  obtain ⟨hSStar_sub, hSStar_ne, hSStar_tight, -⟩ := tightSetAtMinRatio_spec hA hp
  set xStar := M.minTightRatio p A hA
  set SStar := M.tightSetAtMinRatio p A hA
  constructor
  · intro hmin
    have hall := (source_minCut_bipCap_iff (A := A) (B := M.buyerNeighborhood p A)
      (a := fun g => x * (p g * M.supply g)) (b := M.budget)
      (E := fun g i => M.IsEqualityEdge p i g)
      (fun g hg => mul_nonneg hx0 (hp g hg).le) (fun i _ => M.budget_nonneg i)).1 hmin
    have hle := hall SStar hSStar_sub
    rw [← Finset.mul_sum, bipNbr_sub_eq_buyerNeighborhood hSStar_sub] at hle
    change x * M.goodValue p SStar ≤ M.budgetSum (M.buyerNeighborhood p SStar) at hle
    have hgv_pos : 0 < M.goodValue p SStar := goodValue_pos_of_nonempty hp hSStar_sub hSStar_ne
    have hlt : xStar * M.goodValue p SStar < x * M.goodValue p SStar :=
      mul_lt_mul_of_pos_right hx hgv_pos
    linarith [hSStar_tight]
  · intro X hs ht hXmin
    set B := M.buyerNeighborhood p A
    set A₁ := cutGoods A X
    set B₁ := cutBuyers B X
    set A₂ := A \ A₁
    set B₂ := B \ B₁
    have hnc := no_cross_of_minCut (fun g hg => mul_nonneg hx0 (hp g hg).le)
      (fun i _ => M.budget_nonneg i) hs ht hXmin
    set S₂ := SStar ∩ A₂
    set S₁ := SStar ∩ A₁
    suffices hS₂_empty : S₂ = ∅ by
      intro g hg
      have hgA : g ∈ A := hSStar_sub hg
      by_contra hgNot
      have : g ∈ S₂ := Finset.mem_inter.2 ⟨hg, Finset.mem_sdiff.2 ⟨hgA, hgNot⟩⟩
      rw [hS₂_empty] at this
      exact Finset.notMem_empty g this
    by_contra hS₂_ne_empty
    have hS₂_ne : S₂.Nonempty := Finset.nonempty_iff_ne_empty.2 hS₂_ne_empty
    have hS₁_sub : S₁ ⊆ A := Finset.inter_subset_left.trans hSStar_sub
    have hS₂_sub : S₂ ⊆ A := Finset.inter_subset_left.trans hSStar_sub
    -- Move `S₂` and `Γ(S₂) ∩ B₂` to the source side of `X`:
    let Y := mkCut (A₁ ∪ S₂) (B₁ ∪ (M.buyerNeighborhood p S₂ ∩ B₂))
    have hcutG_Y : cutGoods A Y = A₁ ∪ S₂ := by
      ext g
      simp only [cutGoods, Finset.mem_filter, Y, good_mem_mkCut_iff, and_iff_right_iff_imp]
      intro hg
      rcases Finset.mem_union.1 hg with hg | hg
      exacts [Finset.filter_subset _ _ hg, hS₂_sub hg]
    have hcutB_Y : cutBuyers B Y = B₁ ∪ (M.buyerNeighborhood p S₂ ∩ B₂) := by
      ext i
      simp only [cutBuyers, Finset.mem_filter, Y, buyer_mem_mkCut_iff, and_iff_right_iff_imp]
      intro hi
      rcases Finset.mem_union.1 hi with hi | hi
      exacts [Finset.filter_subset _ _ hi, Finset.sdiff_subset (Finset.mem_inter.1 hi).2]
    have hnc_Y : ∀ g ∈ cutGoods A Y, ∀ i ∈ B \ cutBuyers B Y, ¬ M.IsEqualityEdge p i g := by
      intro g hg i hi hE
      rw [hcutG_Y, Finset.mem_union] at hg
      rw [Finset.mem_sdiff, hcutB_Y, Finset.mem_union, not_or] at hi
      rcases hg with hgA₁ | hgS₂
      · exact hnc g hgA₁ i (Finset.mem_sdiff.2 ⟨hi.1, hi.2.1⟩) hE
      · exact hi.2.2 (Finset.mem_inter.2
          ⟨mem_buyerNeighborhood.2 ⟨g, hgS₂, hE⟩, Finset.mem_sdiff.2 ⟨hi.1, hi.2.1⟩⟩)
    have hX_le_Y : cutWeight (M.scaledSubnetwork p A x) X ≤
        cutWeight (M.scaledSubnetwork p A x) Y := by
      rw [hXmin]
      exact minRealCutBetween_le_cutWeight _ (source_mem_mkCut _ _) (sink_notMem_mkCut _ _)
    rw [scaledSubnetwork, cutWeight_bipCap_of_no_cross hs ht hnc,
      cutWeight_bipCap_of_no_cross (source_mem_mkCut _ _) (sink_notMem_mkCut _ _) hnc_Y,
      hcutG_Y, hcutB_Y] at hX_le_Y
    -- Simplify `cutWeight Y - cutWeight X`:
    have hS₂_sub_A₂ : S₂ ⊆ A₂ := Finset.inter_subset_right
    have hA_split : A \ A₁ = (A \ (A₁ ∪ S₂)) ∪ S₂ := by
      ext g
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
      constructor
      · intro ⟨hgA, hgA₁⟩
        by_cases hgS₂ : g ∈ S₂
        · exact Or.inr hgS₂
        · exact Or.inl ⟨hgA, hgA₁, hgS₂⟩
      · rintro (⟨hgA, hgA₁, _⟩ | hgS₂)
        · exact ⟨hgA, hgA₁⟩
        · exact Finset.mem_sdiff.1 (hS₂_sub_A₂ hgS₂)
    have hA_disj : Disjoint (A \ (A₁ ∪ S₂)) S₂ := by
      rw [Finset.disjoint_left]
      intro g hg hgS₂
      exact (Finset.mem_sdiff.1 hg).2 (Finset.mem_union.2 (Or.inr hgS₂))
    have hB_disj : Disjoint B₁ (M.buyerNeighborhood p S₂ ∩ B₂) :=
      Finset.disjoint_sdiff.mono_right Finset.inter_subset_right
    have hsumG_eq : ∑ g ∈ A \ A₁, x * (p g * M.supply g) =
        (∑ g ∈ A \ (A₁ ∪ S₂), x * (p g * M.supply g)) + x * M.goodValue p S₂ := by
      rw [hA_split, Finset.sum_union hA_disj, goodValue, Finset.mul_sum]
    have hsumB_eq : ∑ i ∈ B₁ ∪ (M.buyerNeighborhood p S₂ ∩ B₂), M.budget i =
        (∑ i ∈ B₁, M.budget i) + M.budgetSum (M.buyerNeighborhood p S₂ ∩ B₂) :=
      Finset.sum_union hB_disj
    have hS₂_bound : x * M.goodValue p S₂ ≤ M.budgetSum (M.buyerNeighborhood p S₂ ∩ B₂) := by
      linarith
    -- Now compare against `SStar = S₁ ⊔ S₂`:
    have hS₁_nbr_B₁ : M.buyerNeighborhood p S₁ ⊆ B₁ := by
      intro i hi
      obtain ⟨g, hgS₁, hE⟩ := mem_buyerNeighborhood.1 hi
      have hgA₁ : g ∈ A₁ := (Finset.mem_inter.1 hgS₁).2
      have hiB : i ∈ B := mem_buyerNeighborhood.2 ⟨g, hS₁_sub hgS₁, hE⟩
      by_contra hnot
      exact hnc g hgA₁ i (Finset.mem_sdiff.2 ⟨hiB, hnot⟩) hE
    have hdisj_nbr : Disjoint (M.buyerNeighborhood p S₂ ∩ B₂) (M.buyerNeighborhood p S₁) :=
      (Finset.disjoint_sdiff.symm).mono Finset.inter_subset_right hS₁_nbr_B₁
    have hunion_sub : (M.buyerNeighborhood p S₂ ∩ B₂) ∪ M.buyerNeighborhood p S₁ ⊆
        M.buyerNeighborhood p SStar := by
      refine Finset.union_subset ?_ ?_
      · exact Finset.inter_subset_left.trans (fun i hi => by
          obtain ⟨g, hg, hE⟩ := mem_buyerNeighborhood.1 hi
          exact mem_buyerNeighborhood.2 ⟨g, Finset.inter_subset_left hg, hE⟩)
      · exact fun i hi => by
          obtain ⟨g, hg, hE⟩ := mem_buyerNeighborhood.1 hi
          exact mem_buyerNeighborhood.2 ⟨g, Finset.inter_subset_left hg, hE⟩
    have hbudget_split : M.budgetSum (M.buyerNeighborhood p S₂ ∩ B₂) +
        M.budgetSum (M.buyerNeighborhood p S₁) ≤ M.budgetSum (M.buyerNeighborhood p SStar) := by
      unfold budgetSum
      rw [← Finset.sum_union hdisj_nbr]
      exact Finset.sum_le_sum_of_subset_of_nonneg hunion_sub fun i _ _ => M.budget_nonneg i
    have hSStar_split : M.goodValue p SStar = M.goodValue p S₁ + M.goodValue p S₂ := by
      have hu : S₁ ∪ S₂ = SStar := by
        ext g
        simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, A₂, Finset.mem_sdiff]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hg
          by_cases hgA₁ : g ∈ A₁
          · exact Or.inl ⟨hg, hgA₁⟩
          · exact Or.inr ⟨hg, hSStar_sub hg, hgA₁⟩
      have hd : Disjoint S₁ S₂ := Finset.disjoint_sdiff.mono Finset.inter_subset_right
        Finset.inter_subset_right
      rw [← hu, goodValue, Finset.sum_union hd]
      rfl
    have hS₂_lt : xStar * M.goodValue p S₂ < x * M.goodValue p S₂ :=
      mul_lt_mul_of_pos_right hx (goodValue_pos_of_nonempty hp hS₂_sub hS₂_ne)
    have hS₁_le := minTightRatio_mul_goodValue_le hA hp hS₁_sub
    have hSStar_eq : xStar * M.goodValue p S₁ + xStar * M.goodValue p S₂ =
        M.budgetSum (M.buyerNeighborhood p SStar) := by
      rw [← mul_add, ← hSStar_split]; exact hSStar_tight
    linarith

/-- **Lemma 5.10** ([Vazirani2007], Section 5.9, p. 118): at `x = m(Γ(A)) / p(A) > x*`, for any
minimum `s`–`t` cut `X` in `N(x · p)`, the source-side goods `A₁ = A.filter (fun g => .good g ∈ X)`
form a **proper** subset of `A` (`A₁ ⊂ A`). -/
theorem ssubset_of_minCut_at_avgRatio {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g)
    (hx : M.minTightRatio p A hA < M.budgetSum (M.buyerNeighborhood p A) / M.goodValue p A)
    {X : Finset (FlowVertex I G)} (hs : FlowVertex.source ∈ X) (ht : FlowVertex.sink ∉ X)
    (hXmin : cutWeight (M.scaledSubnetwork p A
        (M.budgetSum (M.buyerNeighborhood p A) / M.goodValue p A)) X =
      minRealCutBetween (M.scaledSubnetwork p A
        (M.budgetSum (M.buyerNeighborhood p A) / M.goodValue p A)) .source .sink) :
    A.filter (fun g => .good g ∈ X) ⊂ A := by
  set x := M.budgetSum (M.buyerNeighborhood p A) / M.goodValue p A
  have hx0 : 0 ≤ x := (minTightRatio_nonneg hA hp).trans hx.le
  refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun hEq => ?_⟩
  have hnc := no_cross_of_minCut (fun g hg => mul_nonneg hx0 (hp g hg).le)
    (fun i _ => M.budget_nonneg i) hs ht hXmin
  have hB₁_eq : cutBuyers (M.buyerNeighborhood p A) X = M.buyerNeighborhood p A := by
    ext i
    refine ⟨fun hi => Finset.filter_subset _ _ hi, fun hi => ?_⟩
    obtain ⟨g, hgA, hE⟩ := mem_buyerNeighborhood.1 hi
    by_contra hnot
    exact hnc g (by change g ∈ A.filter _; rw [hEq]; exact hgA) i
      (Finset.mem_sdiff.2 ⟨hi, hnot⟩) hE
  have hcwX : cutWeight (M.scaledSubnetwork p A x) X = M.budgetSum (M.buyerNeighborhood p A) := by
    rw [scaledSubnetwork, cutWeight_bipCap_of_no_cross hs ht hnc, hB₁_eq]
    change (∑ g ∈ A \ A.filter (fun g => .good g ∈ X), _) +
      M.budgetSum (M.buyerNeighborhood p A) = _
    rw [hEq, Finset.sdiff_self, Finset.sum_empty, zero_add]
  have hgv_pos := goodValue_pos_of_nonempty hp Finset.Subset.rfl hA
  have hcwSrc : cutWeight (M.scaledSubnetwork p A x) ({.source} : Finset (FlowVertex I G)) =
      M.budgetSum (M.buyerNeighborhood p A) := by
    rw [cutWeight_scaledSubnetwork_source]
    exact div_mul_cancel₀ _ hgv_pos.ne'
  exact (not_minCut_and_subset_of_minTightRatio_lt hA hp hx).1 (by rw [hcwSrc, ← hcwX, hXmin])

/-- Recursive tight-set search loop in `FreeM (MaxFlowQuery I G)` ([Vazirani2007], Section 5.9,
Lemma 5.11, p. 118). -/
private noncomputable def findTightSetLoop (M : LinearFisherMarket I G) (p : G → ℝ) :
    ℕ → Finset G → FreeM (MaxFlowQuery I G) (ℝ × Finset G)
  | 0, A => pure (0, A)
  | k + 1, A => do
      let x := M.budgetSum (M.buyerNeighborhood p A) / M.goodValue p A
      let W := M.scaledSubnetwork p A x
      let F ← FreeM.lift (.maxFlow W)
      if realNetOut F .source = x * M.goodValue p A then
        pure (x, A)
      else
        findTightSetLoop M p k (cutGoods A (maxMinCut W F))

/-- **Tight-set search program** ([Vazirani2007], Section 5.9, Lemma 5.11, p. 118): finds the
minimum tight ratio `x*` and maximal tight set `S*` on `(A, Γ(A))` using at most `A.card` max-flow
oracle calls. -/
noncomputable def findTightSetProgram (M : LinearFisherMarket I G) (p : G → ℝ)
    (A : Finset G) : FreeM (MaxFlowQuery I G) (ℝ × Finset G) :=
  findTightSetLoop M p A.card A

/-- **Lemma 5.11** ([Vazirani2007], Section 5.9, p. 118): for any nonempty `A : Finset G` with
positive good values `∀ g ∈ A, 0 < p g * M.supply g` and any valid max-flow oracle `oracle`,
`M.findTightSetProgram p A` computes `(M.minTightRatio p A hA, M.tightSetAtMinRatio p A hA)` using
at most `A.card` (hence at most `Fintype.card G`) max-flow oracle calls. -/
theorem findTightSetProgram_spec {M : LinearFisherMarket I G} {p : G → ℝ}
    {A : Finset G} (hA : A.Nonempty) (hp : ∀ g ∈ A, 0 < p g * M.supply g)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    (M.findTightSetProgram p A).eval oracle =
        (M.minTightRatio p A hA, M.tightSetAtMinRatio p A hA) ∧
      (M.findTightSetProgram p A).countQueries oracle ≤ A.card := by
  classical
  have hloop : ∀ (k : ℕ) (B : Finset G) (hB : B.Nonempty),
      (∀ g ∈ B, 0 < p g * M.supply g) → B.card ≤ k →
      (findTightSetLoop M p k B).eval oracle =
          (M.minTightRatio p B hB, M.tightSetAtMinRatio p B hB) ∧
        (findTightSetLoop M p k B).countQueries oracle ≤ k := by
    intro k
    induction k with
    | zero =>
      intro B hB _ hcard
      have := Finset.card_pos.2 hB
      omega
    | succ k ih =>
      intro B hB hpB hcard
      set x := M.budgetSum (M.buyerNeighborhood p B) / M.goodValue p B
      have hx_ge : M.minTightRatio p B hB ≤ x :=
        Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.Subset.rfl, hB⟩)
      have hx0 : 0 ≤ x := (minTightRatio_nonneg hB hpB).trans hx_ge
      set W := M.scaledSubnetwork p B x
      have hW_nn : ∀ u v, 0 ≤ W u v :=
        bipCap_nonneg (fun g hg => mul_nonneg hx0 (hpB g hg).le) (fun i _ => M.budget_nonneg i)
      set F := oracle (.maxFlow W)
      have hF_spec := horacle W hW_nn
      have hF_val : realNetOut F .source = minRealCutBetween W .source .sink :=
        IsGreatest.unique hF_spec.2 (isMaxRealFlow_minRealCutBetween hW_nn (by simp))
      have hsrc_cw : cutWeight W ({.source} : Finset (FlowVertex I G)) = x * M.goodValue p B :=
        cutWeight_scaledSubnetwork_source M p B x
      by_cases hmin : realNetOut F .source = x * M.goodValue p B
      · have hsrc_min : cutWeight W ({.source} : Finset (FlowVertex I G)) =
            minRealCutBetween W .source .sink := by rw [hsrc_cw, ← hmin, hF_val]
        have hx_le : x ≤ M.minTightRatio p B hB := by
          by_contra hlt
          push Not at hlt
          exact (not_minCut_and_subset_of_minTightRatio_lt hB hpB hlt).1 hsrc_min
        have hx_eq : x = M.minTightRatio p B hB := le_antisymm hx_le hx_ge
        obtain ⟨hS_sub, -, -, hS_max⟩ := tightSetAtMinRatio_spec hB hpB
        have hB_tight : M.minTightRatio p B hB * M.goodValue p B =
            M.budgetSum (M.buyerNeighborhood p B) := by
          rw [← hx_eq]
          exact div_mul_cancel₀ _ (goodValue_pos_of_nonempty hpB Finset.Subset.rfl hB).ne'
        have hS_eq : M.tightSetAtMinRatio p B hB = B :=
          Finset.Subset.antisymm hS_sub (hS_max B Finset.Subset.rfl hB_tight)
        have heval_done : (findTightSetLoop M p (k + 1) B).eval oracle = (x, B) := by
          change (FreeM.lift (.maxFlow W) >>= fun F' => _).eval oracle = _
          rw [FreeM.eval_liftBind]
          dsimp only [x, W, F]
          rw [ite_eq_left_iff.2 fun h => absurd hmin h]
          rfl
        have hq_done : (findTightSetLoop M p (k + 1) B).countQueries oracle = 1 := by
          change (FreeM.lift (.maxFlow W) >>= fun F' => _).countQueries oracle = _
          rw [FreeM.countQueries_liftBind]
          dsimp only [x, W, F]
          rw [ite_eq_left_iff.2 fun h => absurd hmin h]
          rfl
        rw [heval_done, hq_done, hx_eq, hS_eq]
        exact ⟨rfl, by omega⟩
      · have hx_gt : M.minTightRatio p B hB < x := by
          refine lt_of_le_of_ne hx_ge fun heq => hmin ?_
          rw [hF_val, ← hsrc_cw]
          exact (minCut_scaledSubnetwork_of_le_minTightRatio hB hpB hx0 heq.ge).symm
        set S := maxMinCut W F
        set A₁ := cutGoods B S
        have hS_min : cutWeight W S = minRealCutBetween W .source .sink :=
          cutWeight_maxMinCut hW_nn hF_spec.1 hF_spec.2
        have hSStar_sub_A₁ : M.tightSetAtMinRatio p B hB ⊆ A₁ :=
          (not_minCut_and_subset_of_minTightRatio_lt hB hpB hx_gt).2 S
            (source_mem_maxMinCut hF_spec.1 hF_spec.2) (sink_notMem_maxMinCut W F) hS_min
        have hA₁_ssub : A₁ ⊂ B :=
          ssubset_of_minCut_at_avgRatio hB hpB hx_gt
            (source_mem_maxMinCut hF_spec.1 hF_spec.2) (sink_notMem_maxMinCut W F) hS_min
        obtain ⟨-, hSStar_ne, hSStar_tight, hSStar_max⟩ := tightSetAtMinRatio_spec hB hpB
        have hA₁_ne : A₁.Nonempty := hSStar_ne.mono hSStar_sub_A₁
        have hpA₁ : ∀ g ∈ A₁, 0 < p g * M.supply g := fun g hg => hpB g (hA₁_ssub.1 hg)
        have hcardA₁ : A₁.card ≤ k := by
          have := Finset.card_lt_card hA₁_ssub; omega
        have hxStar_eq : M.minTightRatio p A₁ hA₁_ne = M.minTightRatio p B hB := by
          apply le_antisymm
          · have hmem : M.tightSetAtMinRatio p B hB ∈ A₁.powerset.filter Finset.Nonempty :=
              Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSStar_sub_A₁, hSStar_ne⟩
            have hle := Finset.inf'_le (f := fun T => M.budgetSum (M.buyerNeighborhood p T) /
              M.goodValue p T) hmem
            have hgv_pos := goodValue_pos_of_nonempty hpA₁ hSStar_sub_A₁ hSStar_ne
            rwa [← hSStar_tight, mul_div_cancel_right₀ _ hgv_pos.ne'] at hle
          · unfold minTightRatio
            rw [Finset.le_inf'_iff]
            intro T hT
            obtain ⟨hTA₁, hTne⟩ := Finset.mem_filter.1 hT
            exact Finset.inf'_le _ (Finset.mem_filter.2
              ⟨Finset.mem_powerset.2 ((Finset.mem_powerset.1 hTA₁).trans hA₁_ssub.1), hTne⟩)
        have hSStar_eq : M.tightSetAtMinRatio p A₁ hA₁_ne = M.tightSetAtMinRatio p B hB := by
          obtain ⟨h1_sub, -, h1_tight, h1_max⟩ := tightSetAtMinRatio_spec hA₁_ne hpA₁
          apply Finset.Subset.antisymm
          · exact hSStar_max _ (h1_sub.trans hA₁_ssub.1) (hxStar_eq ▸ h1_tight)
          · exact h1_max _ hSStar_sub_A₁ (hxStar_eq.symm ▸ hSStar_tight)
        obtain ⟨hih_eval, hih_q⟩ := ih A₁ hA₁_ne hpA₁ hcardA₁
        have heval_step : (findTightSetLoop M p (k + 1) B).eval oracle =
            (findTightSetLoop M p k A₁).eval oracle := by
          change (FreeM.lift (.maxFlow W) >>= fun F' => _).eval oracle = _
          rw [FreeM.eval_liftBind]
          dsimp only [x, W, F, A₁, S]
          rw [ite_eq_right_iff.2 fun h => absurd h hmin]
        have hq_step : (findTightSetLoop M p (k + 1) B).countQueries oracle =
            1 + (findTightSetLoop M p k A₁).countQueries oracle := by
          change (FreeM.lift (.maxFlow W) >>= fun F' => _).countQueries oracle = _
          rw [FreeM.countQueries_liftBind]
          dsimp only [x, W, F, A₁, S]
          rw [ite_eq_right_iff.2 fun h => absurd h hmin]
        rw [heval_step, hq_step, hih_eval, hxStar_eq, hSStar_eq]
        exact ⟨rfl, by omega⟩
  exact hloop A.card A hA hp le_rfl

end FindingTightSets

/-! ### Section 5.10 (Lemma 5.12) & Section 5.2 (Theorem 5.1 part 4): Rationality -/

section Rationality

variable {I G : Type*}

/-- Express a nonnegative rational `q : ℚ` as `(q.num.natAbs : ℚ) / (q.den : ℚ)`. -/
private theorem rat_eq_natAbs_div_den {q : ℚ} (hq : 0 ≤ q) :
    q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
  have hnum : ((q.num.natAbs : ℤ) : ℚ) = (q.num : ℚ) :=
    congrArg Int.cast (Int.natAbs_of_nonneg (Rat.num_nonneg.2 hq))
  rw [Int.cast_natCast] at hnum
  exact (Rat.num_div_den q).symm.trans (congrArg (· / (q.den : ℚ)) hnum.symm)

/-- Denominator and numerator bounds for a nonnegative rational written as `(a : ℚ) / (b : ℚ)` with
`a, b : ℕ` and `0 < b`. -/
private theorem rat_div_nat_bounds {a b : ℕ} (hb : 0 < b) :
    let q : ℚ := (a : ℚ) / (b : ℚ)
    q.den ≤ b ∧ q.num.natAbs ≤ a := by
  intro q
  have hd0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hcross_q : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) :=
    (div_eq_div_iff hd0 hb0).1 (Rat.num_div_den q)
  have hcross_z : q.num * (b : ℤ) = (a : ℤ) * (q.den : ℤ) := by exact_mod_cast hcross_q
  have hcross_n : q.num.natAbs * b = a * q.den := by
    have habs := congrArg Int.natAbs hcross_z
    simpa [Int.natAbs_mul] using habs
  have hdvd : q.den ∣ b := by
    have hdvd_mul : q.den ∣ q.num.natAbs * b := ⟨a, by linarith⟩
    exact q.reduced.symm.dvd_of_dvd_mul_left hdvd_mul
  have hden_le : q.den ≤ b := Nat.le_of_dvd hb hdvd
  have hnum_le : q.num.natAbs ≤ a := by
    have : q.num.natAbs * b ≤ a * b := hcross_n.le.trans (Nat.mul_le_mul_left a hden_le)
    exact Nat.le_of_mul_le_mul_right this hb
  exact ⟨hden_le, hnum_le⟩

/-- A reflexive–transitive chain starting inside `P` and ending outside `P` crosses the boundary of
`P` in a single step. -/
private theorem reflTransGen_boundary {α : Type*} {R : α → α → Prop} {P : α → Prop} {x y : α}
    (hxy : Relation.ReflTransGen R x y) (hx : P x) (hy : ¬ P y) :
    ∃ u v, P u ∧ ¬ P v ∧ R u v := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hx hy
  | @head a b hab _ ih =>
    by_cases hb : P b
    · exact ih hb
    · exact ⟨a, b, hx, hb, hab⟩

variable [Fintype I] [Fintype G]

/-- Connected-component spanning-tree rationality ([Vazirani2007], Section 5.10, Lemma 5.12,
pp. 118–119): in a unit-supply linear Fisher market with integer utilities `u ≤ U` and integer
budgets `e`, at any positive price vector `p` satisfying the Invariant, the connected component `C`
of any good `g₀` in a tight set `S` is itself tight and admits a common positive integer
denominator `c ≤ C.card * U ^ (C.card - 1)` and positive integer weights `N g ≤ U ^ (C.card - 1)`
summing to `c` such that `c * p g = N g * M_C` for every `g ∈ C`. -/
private theorem tightSet_component_rat [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hinv : M.SatisfiesInvariant p)
    {S : Finset G} (hStight : M.IsTightSet p S) {g₀ : G} (hg₀ : g₀ ∈ S) :
    let adj : G → G → Prop := fun g₁ g₂ =>
      g₁ ∈ S ∧ g₂ ∈ S ∧ ∃ i : I, M.IsEqualityEdge p i g₁ ∧ M.IsEqualityEdge p i g₂
    let C : Finset G := open scoped Classical in S.filter fun g => Relation.ReflTransGen adj g₀ g
    let M_C : ℕ := ∑ i ∈ M.buyerNeighborhood p C, e i
    ∃ (c : ℕ) (N : G → ℕ),
      0 < c ∧ c ≤ C.card * U ^ (C.card - 1) ∧ c = ∑ g ∈ C, N g ∧
      1 ≤ U ∧ 0 < M_C ∧ M.IsTightSet p C ∧
      ∀ g ∈ C, 0 < N g ∧ N g ≤ U ^ (C.card - 1) ∧ (c : ℝ) * p g = ((N g * M_C : ℕ) : ℝ) := by
  classical
  intro adj C M_C
  have hC_sub : C ⊆ S := Finset.filter_subset _ _
  have hg₀C : g₀ ∈ C := Finset.mem_filter.2 ⟨hg₀, .refl⟩
  have hC_pos : 1 ≤ C.card := Finset.one_le_card.2 ⟨g₀, hg₀C⟩
  -- 1. `C` and `S \ C` have disjoint equality neighborhoods, so `C` is itself tight!
  have hdisj_nbr : Disjoint (M.buyerNeighborhood p C) (M.buyerNeighborhood p (S \ C)) := by
    rw [Finset.disjoint_left]
    intro i hiC hiSC
    obtain ⟨g₁, hg₁C, hE₁⟩ := mem_buyerNeighborhood.1 hiC
    obtain ⟨g₂, hg₂SC, hE₂⟩ := mem_buyerNeighborhood.1 hiSC
    obtain ⟨hg₁S, hreach₁⟩ := Finset.mem_filter.1 hg₁C
    obtain ⟨hg₂S, hg₂NotC⟩ := Finset.mem_sdiff.1 hg₂SC
    have hadj : adj g₁ g₂ := ⟨hg₁S, hg₂S, i, hE₁, hE₂⟩
    exact hg₂NotC (Finset.mem_filter.2 ⟨hg₂S, hreach₁.tail hadj⟩)
  have hC_tight : M.IsTightSet p C := by
    have hall := (satisfiesInvariant_iff fun g => (hp g).le).1 hinv
    have hleC := hall C
    have hleSC := hall (S \ C)
    have hS_split : C ∪ (S \ C) = S := Finset.union_sdiff_of_subset hC_sub
    have hval_add : M.goodValue p S = M.goodValue p C + M.goodValue p (S \ C) := by
      have h : M.goodValue p (C ∪ (S \ C)) = M.goodValue p C + M.goodValue p (S \ C) :=
        Finset.sum_union Finset.disjoint_sdiff
      rwa [hS_split] at h
    have hnbr_union : M.buyerNeighborhood p S =
        M.buyerNeighborhood p C ∪ M.buyerNeighborhood p (S \ C) := by
      have h : M.buyerNeighborhood p (C ∪ (S \ C)) =
          M.buyerNeighborhood p C ∪ M.buyerNeighborhood p (S \ C) :=
        bipNbr_union _ _ C (S \ C)
      rwa [hS_split] at h
    have hbud_add : M.budgetSum (M.buyerNeighborhood p S) =
        M.budgetSum (M.buyerNeighborhood p C) + M.budgetSum (M.buyerNeighborhood p (S \ C)) := by
      rw [hnbr_union, budgetSum, Finset.sum_union hdisj_nbr]
      rfl
    unfold IsTightSet at hStight ⊢
    linarith
  have hgvC_eq : M.goodValue p C = ∑ g ∈ C, p g := by
    simp only [goodValue, hsup, mul_one]
  have hbudC_eq : M.budgetSum (M.buyerNeighborhood p C) = (M_C : ℝ) := by
    simp only [budgetSum, M_C, he, Nat.cast_sum]
  have hsumC_eq : ∑ g ∈ C, p g = (M_C : ℝ) := by
    rw [← hgvC_eq, ← hbudC_eq]
    exact hC_tight
  have hMC_pos_real : (0 : ℝ) < (M_C : ℝ) := by
    rw [← hsumC_eq]
    exact (hp g₀).trans_le (Finset.single_le_sum (fun g _ => (hp g).le) hg₀C)
  have hMC_pos : 0 < M_C := by exact_mod_cast hMC_pos_real
  have hU_ge1 : 1 ≤ U := by
    have hnbr_ne : (M.buyerNeighborhood p C).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have : M_C = 0 := by simp [M_C, hempty]
      omega
    obtain ⟨i₀, _⟩ := hnbr_ne
    obtain ⟨g₁, hg₁⟩ := hbuyer i₀
    rw [hu i₀ g₁] at hg₁
    have hpos : 0 < u i₀ g₁ := by exact_mod_cast hg₁
    exact hpos.trans_le (hU i₀ g₁)
  -- 2. Spanning-tree induction on `k` (`1 ≤ k ≤ C.card`) expressing `p g / p g₀` as `N g / D`.
  have htree : ∀ k, 1 ≤ k → k ≤ C.card →
      ∃ (T : Finset G) (D : ℕ) (N : G → ℕ),
        T ⊆ C ∧ g₀ ∈ T ∧ T.card = k ∧
        0 < D ∧ D ≤ U ^ (k - 1) ∧
        ∀ g ∈ T, 0 < N g ∧ N g ≤ U ^ (k - 1) ∧ (D : ℝ) * p g = (N g : ℝ) * p g₀ := by
    intro k hk1 hkC
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hk0 | hkgt
      · have hk_zero : k = 0 := by omega
        subst hk_zero
        refine ⟨{g₀}, 1, fun _ => 1, Finset.singleton_subset_iff.2 hg₀C,
          Finset.mem_singleton_self g₀, Finset.card_singleton g₀,
          Nat.one_pos, by simp, fun g hg => ?_⟩
        rw [Finset.mem_singleton.1 hg]
        exact ⟨Nat.one_pos, by simp, by simp⟩
      · have hk1' : 1 ≤ k := by omega
        obtain ⟨T, D, N, hTC, hg₀T, hTcard, hDpos, hDle, hTspec⟩ := ih hk1' (by omega)
        have hCT_ne : (C \ T).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h0
          have hCT : C ⊆ T := Finset.sdiff_eq_empty_iff_subset.1 h0
          have : C.card ≤ T.card := Finset.card_le_card hCT
          omega
        obtain ⟨g_out, hg_out⟩ := hCT_ne
        obtain ⟨hg_outC, hg_outNotT⟩ := Finset.mem_sdiff.1 hg_out
        have hreach_out : Relation.ReflTransGen adj g₀ g_out := (Finset.mem_filter.1 hg_outC).2
        obtain ⟨g_in, g_new, hg_inT, hg_newNotT, hadj⟩ :=
          reflTransGen_boundary (P := fun g => g ∈ T) hreach_out hg₀T hg_outNotT
        have hg_newC : g_new ∈ C := by
          have hg_inC : g_in ∈ C := hTC hg_inT
          exact Finset.mem_filter.2 ⟨hadj.2.1, (Finset.mem_filter.1 hg_inC).2.tail hadj⟩
        obtain ⟨-, -, i, hE_in, hE_new⟩ := hadj
        set a := u i g_in
        set b := u i g_new
        have ha_pos_r : (0 : ℝ) < (a : ℝ) := by
          rw [← hu i g_in]
          exact utility_pos_of_isEqualityEdge hp (hbuyer i) hE_in
        have hb_pos_r : (0 : ℝ) < (b : ℝ) := by
          rw [← hu i g_new]
          exact utility_pos_of_isEqualityEdge hp (hbuyer i) hE_new
        have ha_pos : 0 < a := by exact_mod_cast ha_pos_r
        have hb_pos : 0 < b := by exact_mod_cast hb_pos_r
        have ha_le : a ≤ U := hU i g_in
        have hb_le : b ≤ U := hU i g_new
        have hratio : (a : ℝ) * p g_new = (b : ℝ) * p g_in := by
          have hle1 : M.bangPerBuck p i g_new ≤ M.bangPerBuck p i g_in := hE_in g_new
          have hle2 : M.bangPerBuck p i g_in ≤ M.bangPerBuck p i g_new := hE_new g_in
          have heq : M.utility i g_in / p g_in = M.utility i g_new / p g_new := by
            simpa only [bangPerBuck_eq] using le_antisymm hle2 hle1
          rw [hu i g_in, hu i g_new, div_eq_div_iff (hp g_in).ne' (hp g_new).ne'] at heq
          exact heq
        have hpow_step : U * U ^ (k - 1) = U ^ ((k + 1) - 1) := by
          have hexp : (k + 1) - 1 = (k - 1) + 1 := by omega
          rw [hexp, pow_succ']
        let T' := insert g_new T
        let D' := a * D
        let N' : G → ℕ := fun g => if g = g_new then b * N g_in else a * N g
        refine ⟨T', D', N', Finset.insert_subset hg_newC hTC,
          Finset.mem_insert_of_mem hg₀T, by rw [Finset.card_insert_of_notMem hg_newNotT, hTcard],
          Nat.mul_pos ha_pos hDpos,
          (Nat.mul_le_mul ha_le hDle).trans hpow_step.le, fun g hg => ?_⟩
        rcases Finset.mem_insert.1 hg with hg_eq | hgT
        · obtain ⟨hNin_pos, hNin_le, hNin_eq⟩ := hTspec g_in hg_inT
          refine ⟨by simp [N', hg_eq, Nat.mul_pos hb_pos hNin_pos],
            by simpa [N', hg_eq] using (Nat.mul_le_mul hb_le hNin_le).trans hpow_step.le, ?_⟩
          simp only [D', N', hg_eq, ↓reduceIte, Nat.cast_mul]
          calc
            (a : ℝ) * (D : ℝ) * p g_new = (D : ℝ) * ((a : ℝ) * p g_new) := by ring
            _ = (D : ℝ) * ((b : ℝ) * p g_in) := by rw [hratio]
            _ = (b : ℝ) * ((D : ℝ) * p g_in) := by ring
            _ = (b : ℝ) * ((N g_in : ℝ) * p g₀) := by rw [hNin_eq]
            _ = (b : ℝ) * (N g_in : ℝ) * p g₀ := by ring
        · have hne : g ≠ g_new := fun h => hg_newNotT (h ▸ hgT)
          obtain ⟨hNg_pos, hNg_le, hNg_eq⟩ := hTspec g hgT
          refine ⟨by simp [N', hne, Nat.mul_pos ha_pos hNg_pos],
            by simpa [N', hne] using (Nat.mul_le_mul ha_le hNg_le).trans hpow_step.le, ?_⟩
          simp only [D', N', hne, ↓reduceIte, Nat.cast_mul]
          calc
            (a : ℝ) * (D : ℝ) * p g = (a : ℝ) * ((D : ℝ) * p g) := by ring
            _ = (a : ℝ) * ((N g : ℝ) * p g₀) := by rw [hNg_eq]
            _ = (a : ℝ) * (N g : ℝ) * p g₀ := by ring
  obtain ⟨T, D, N, hTC, -, hTcard, hDpos, -, hTspec⟩ := htree C.card hC_pos le_rfl
  have hT_eq : T = C := Finset.eq_of_subset_of_card_le hTC hTcard.ge
  subst hT_eq
  -- 3. Sum over `C` to express `p g = (N g * M_C) / c` where `c = ∑ g ∈ C, N g`.
  let c : ℕ := ∑ g ∈ C, N g
  have hc_pos : 0 < c :=
    (hTspec g₀ hg₀C).1.trans_le (Finset.single_le_sum (fun g _ => Nat.zero_le (N g)) hg₀C)
  have hc_le : c ≤ C.card * U ^ (C.card - 1) := by
    calc
      ∑ g ∈ C, N g ≤ ∑ _g ∈ C, U ^ (C.card - 1) :=
        Finset.sum_le_sum fun g hg => (hTspec g hg).2.1
      _ = C.card * U ^ (C.card - 1) := by simp
  have hsum_rel : (D : ℝ) * (M_C : ℝ) = (c : ℝ) * p g₀ := by
    calc
      (D : ℝ) * (M_C : ℝ) = (D : ℝ) * ∑ g ∈ C, p g := by rw [hsumC_eq]
      _ = ∑ g ∈ C, (D : ℝ) * p g := Finset.mul_sum C p (D : ℝ)
      _ = ∑ g ∈ C, (N g : ℝ) * p g₀ := Finset.sum_congr rfl fun g hg => (hTspec g hg).2.2
      _ = (∑ g ∈ C, (N g : ℝ)) * p g₀ := (Finset.sum_mul C (fun g => (N g : ℝ)) (p g₀)).symm
      _ = (c : ℝ) * p g₀ := by simp [c]
  have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hDpos.ne'
  refine ⟨c, N, hc_pos, hc_le, rfl, hU_ge1, hMC_pos, hC_tight, fun g hg => ?_⟩
  obtain ⟨hNg_pos, hNg_le, hNg_eq⟩ := hTspec g hg
  refine ⟨hNg_pos, hNg_le, ?_⟩
  apply mul_left_cancel₀ hD_ne
  calc
    (D : ℝ) * ((c : ℝ) * p g) = (c : ℝ) * ((D : ℝ) * p g) := by ring
    _ = (c : ℝ) * ((N g : ℝ) * p g₀) := by rw [hNg_eq]
    _ = (N g : ℝ) * ((c : ℝ) * p g₀) := by ring
    _ = (N g : ℝ) * ((D : ℝ) * (M_C : ℝ)) := by rw [hsum_rel]
    _ = (D : ℝ) * ((N g * M_C : ℕ) : ℝ) := by push_cast; ring

/-- **Lemma 5.12** ([Vazirani2007], Section 5.10, pp. 118–119): in a unit-supply linear Fisher
market with integer utilities `u i g ≤ U` and integer budgets `e i`, at any positive price vector
`p` satisfying the Invariant, every good `g` in a tight set `S` has a rational price `q : ℚ` with
denominator at most `S.card * U ^ (S.card - 1)` (hence at most
`Fintype.card G * U ^ Fintype.card G`, matching `Δ = n U ^ n` in [Vazirani2007], p. 118). -/
theorem exists_rat_price_of_isTightSet [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hinv : M.SatisfiesInvariant p)
    {S : Finset G} (hStight : M.IsTightSet p S) {g : G} (hg : g ∈ S) :
    ∃ q : ℚ, (q : ℝ) = p g ∧
      q.den ≤ S.card * U ^ (S.card - 1) ∧
      q.den ≤ Fintype.card G * U ^ Fintype.card G := by
  classical
  obtain ⟨c, N, hc_pos, hc_le, -, hU_ge1, -, -, hC_spec⟩ :=
    tightSet_component_rat hsup hu hU he hbuyer hp hinv hStight hg
  let adj : G → G → Prop := fun g₁ g₂ =>
    g₁ ∈ S ∧ g₂ ∈ S ∧ ∃ i : I, M.IsEqualityEdge p i g₁ ∧ M.IsEqualityEdge p i g₂
  let C : Finset G := S.filter fun g' => Relation.ReflTransGen adj g g'
  let M_C : ℕ := ∑ i ∈ M.buyerNeighborhood p C, e i
  have hgC : g ∈ C := Finset.mem_filter.2 ⟨hg, .refl⟩
  obtain ⟨-, -, hpg_eq⟩ := hC_spec g hgC
  change c ≤ C.card * U ^ (C.card - 1) at hc_le
  let q : ℚ := ((N g * M_C : ℕ) : ℚ) / (c : ℚ)
  have hq_real : (q : ℝ) = p g := by
    have hc0 : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc_pos.ne'
    simp only [q, Rat.cast_div, Rat.cast_natCast]
    exact (div_eq_iff hc0).2 (by linarith [hpg_eq])
  have hden_le_c : q.den ≤ c := (rat_div_nat_bounds hc_pos).1
  have hC_card_le_S : C.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hS_card_le_n : S.card ≤ Fintype.card G := Finset.card_le_univ S
  have hc_le_S : c ≤ S.card * U ^ (S.card - 1) :=
    hc_le.trans (Nat.mul_le_mul hC_card_le_S (Nat.pow_le_pow_right hU_ge1 (by omega)))
  have hc_le_n : S.card * U ^ (S.card - 1) ≤ Fintype.card G * U ^ Fintype.card G :=
    Nat.mul_le_mul hS_card_le_n (Nat.pow_le_pow_right hU_ge1 (by omega))
  exact ⟨q, hq_real, hden_le_c.trans hc_le_S, (hden_le_c.trans hc_le_S).trans hc_le_n⟩

/-- Given a tight connected component `C` of goods with common integer denominator `c` and scaled
integer supplies `N g * M_C` satisfying `∑ g ∈ C, N g = c` and `c * p g = N g * M_C`, the integral
max-flow min-cut theorem (`Network.exists_maxFlow_eq_minCut`) yields an integral money flow
`F : G → I → ℕ` supported on equality edges in `C × Γ(C)` that saturates every good `g ∈ C` to
`N g * M_C` and every buyer `i ∈ Γ(C)` to `c * e i`. -/
private theorem exists_int_component_flow [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G}
    (hsup : ∀ g, M.supply g = 1)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hinv : M.SatisfiesInvariant p)
    {C : Finset G} (hC_tight : M.IsTightSet p C)
    {c : ℕ} {N : G → ℕ} (hc_sum : c = ∑ g ∈ C, N g)
    (hpg : ∀ g ∈ C, (c : ℝ) * p g = ((N g * (∑ i ∈ M.buyerNeighborhood p C, e i) : ℕ) : ℝ)) :
    let B := M.buyerNeighborhood p C
    let M_C := ∑ i ∈ B, e i
    ∃ F : G → I → ℕ,
      (∀ g i, 0 < F g i → g ∈ C ∧ i ∈ B ∧ M.IsEqualityEdge p i g) ∧
      (∀ g ∈ C, ∑ i ∈ B, F g i = N g * M_C) ∧
      (∀ i ∈ B, ∑ g ∈ C, F g i = c * e i) := by
  classical
  intro B M_C
  let bigM_nat : ℕ := c * M_C + 1
  let Nint : Network (FlowVertex I G) := {
    s := .source
    t := .sink
    cap := fun u v =>
      match u, v with
      | .source, .good g => if g ∈ C then N g * M_C else 0
      | .good g, .buyer i => if g ∈ C ∧ i ∈ B ∧ M.IsEqualityEdge p i g then bigM_nat else 0
      | .buyer i, .sink => if i ∈ B then c * e i else 0
      | _, _ => 0
  }
  have hsum_src : ∑ g ∈ C, N g * M_C = c * M_C := by
    rw [← Finset.sum_mul, hc_sum]
  have hsum_sink : ∑ i ∈ B, c * e i = c * M_C := by
    rw [← Finset.mul_sum]
  have hcap_src_cut : Nint.cutCapacity ({.source} : Finset (FlowVertex I G)) = c * M_C := by
    rw [Network.cutCapacity, Finset.sum_singleton]
    have hsplit : ∑ v ∈ Finset.univ \ ({.source} : Finset (FlowVertex I G)), Nint.cap .source v =
        ∑ v : FlowVertex I G, Nint.cap .source v := by
      refine Finset.sum_subset (Finset.sdiff_subset) fun v _ hv => ?_
      rw [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at hv
      have hvs : v = .source := hv (Finset.mem_univ v)
      subst hvs
      rfl
    rw [hsplit, sum_flowVertex]
    simp only [Nint, zero_add, add_zero, Finset.sum_const_zero, Finset.sum_ite_mem,
      Finset.univ_inter]
    exact hsum_src
  -- Every `s`–`t` cut of `Nint` has capacity at least `c * M_C`.
  have hcut_ge : ∀ X : Finset (FlowVertex I G), Nint.IsCut X → c * M_C ≤ Nint.cutCapacity X := by
    intro X ⟨hsX, htNotX⟩
    by_cases hcross : ∃ g ∈ C, ∃ i ∈ B,
        M.IsEqualityEdge p i g ∧ FlowVertex.good g ∈ X ∧ FlowVertex.buyer i ∉ X
    · obtain ⟨g, hgC, i, hiB, hE, hgX, hiNotX⟩ := hcross
      have hiSdiff : FlowVertex.buyer i ∈ Finset.univ \ X :=
        Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hiNotX⟩
      have hle1 : Nint.cap (.good g) (.buyer i) ≤
          ∑ v ∈ Finset.univ \ X, Nint.cap (.good g) v :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hiSdiff
      have hle2 : ∑ v ∈ Finset.univ \ X, Nint.cap (.good g) v ≤ Nint.cutCapacity X :=
        Finset.single_le_sum (f := fun u => ∑ v ∈ Finset.univ \ X, Nint.cap u v)
          (fun _ _ => Nat.zero_le _) hgX
      have hcap_eq : Nint.cap (.good g) (.buyer i) = c * M_C + 1 := by
        simp [Nint, hgC, hiB, hE, bigM_nat]
      omega
    · push Not at hcross
      let C₁ := C.filter fun g => FlowVertex.good g ∈ X
      let C₂ := C \ C₁
      let B₁ := B.filter fun i => FlowVertex.buyer i ∈ X
      have hsrc_term : ∑ g ∈ C₂, N g * M_C ≤ ∑ v ∈ Finset.univ \ X, Nint.cap .source v := by
        have hinj : ∀ g₁ ∈ C₂, ∀ g₂ ∈ C₂,
            (FlowVertex.good g₁ : FlowVertex I G) = .good g₂ → g₁ = g₂ :=
          fun _ _ _ _ h => by cases h; rfl
        have hsub : C₂.image (FlowVertex.good (I := I)) ⊆ Finset.univ \ X := by
          intro v hv
          obtain ⟨g, hgC₂, rfl⟩ := Finset.mem_image.1 hv
          obtain ⟨hgC, hgNotC₁⟩ := Finset.mem_sdiff.1 hgC₂
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h =>
            hgNotC₁ (Finset.mem_filter.2 ⟨hgC, h⟩)⟩
        calc
          ∑ g ∈ C₂, N g * M_C = ∑ g ∈ C₂, Nint.cap .source (.good g) :=
            Finset.sum_congr rfl fun g hg => by simp [Nint, (Finset.mem_sdiff.1 hg).1]
          _ = ∑ v ∈ C₂.image (FlowVertex.good (I := I)), Nint.cap .source v :=
            (Finset.sum_image fun a ha b hb h => hinj a ha b hb h).symm
          _ ≤ ∑ v ∈ Finset.univ \ X, Nint.cap .source v :=
            Finset.sum_le_sum_of_subset hsub
      have hsink_term : ∑ i ∈ B₁, c * e i ≤
          ∑ u ∈ B₁.image (FlowVertex.buyer (G := G)), ∑ v ∈ Finset.univ \ X, Nint.cap u v := by
        rw [Finset.sum_image fun _ _ _ _ h => by cases h; rfl]
        refine Finset.sum_le_sum fun i hi => ?_
        have hiB : i ∈ B := (Finset.mem_filter.1 hi).1
        have htSdiff : FlowVertex.sink ∈ Finset.univ \ X :=
          Finset.mem_sdiff.2 ⟨Finset.mem_univ _, htNotX⟩
        have hle := Finset.single_le_sum (f := fun v => Nint.cap (.buyer i) v)
          (fun _ _ => Nat.zero_le _) htSdiff
        simpa [Nint, hiB] using hle
      have hsub_X : insert FlowVertex.source (B₁.image (FlowVertex.buyer (G := G))) ⊆ X := by
        refine Finset.insert_subset hsX ?_
        intro v hv
        obtain ⟨i, hiB₁, rfl⟩ := Finset.mem_image.1 hv
        exact (Finset.mem_filter.1 hiB₁).2
      have hsrc_notMem : FlowVertex.source ∉ B₁.image (FlowVertex.buyer (G := G)) := by
        simp
      have hcut_lb : (∑ g ∈ C₂, N g * M_C) + (∑ i ∈ B₁, c * e i) ≤ Nint.cutCapacity X := by
        calc
          (∑ g ∈ C₂, N g * M_C) + (∑ i ∈ B₁, c * e i)
            ≤ (∑ v ∈ Finset.univ \ X, Nint.cap .source v) +
                ∑ u ∈ B₁.image (FlowVertex.buyer (G := G)), ∑ v ∈ Finset.univ \ X, Nint.cap u v :=
                Nat.add_le_add hsrc_term hsink_term
          _ = ∑ u ∈ insert FlowVertex.source (B₁.image (FlowVertex.buyer (G := G))),
                ∑ v ∈ Finset.univ \ X, Nint.cap u v := by
                rw [Finset.sum_insert hsrc_notMem]
          _ ≤ Nint.cutCapacity X := Finset.sum_le_sum_of_subset hsub_X
      -- Cast to `ℝ` and use `SatisfiesInvariant` on `C₁`.
      have hnbr_sub : M.buyerNeighborhood p C₁ ⊆ B₁ := by
        intro i hi
        obtain ⟨g, hgC₁, hE⟩ := mem_buyerNeighborhood.1 hi
        obtain ⟨hgC, hgX⟩ := Finset.mem_filter.1 hgC₁
        have hiB : i ∈ B := mem_buyerNeighborhood.2 ⟨g, hgC, hE⟩
        exact Finset.mem_filter.2 ⟨hiB, hcross g hgC i hiB hE hgX⟩
      have hinvC₁ : M.goodValue p C₁ ≤ M.budgetSum (M.buyerNeighborhood p C₁) :=
        (satisfiesInvariant_iff fun g => (hp g).le).1 hinv C₁
      have hreal_ge : ((c * M_C : ℕ) : ℝ) ≤
          (((∑ g ∈ C₂, N g * M_C) + (∑ i ∈ B₁, c * e i) : ℕ) : ℝ) := by
        have h1 : ((∑ g ∈ C₂, N g * M_C : ℕ) : ℝ) = (c : ℝ) * ∑ g ∈ C₂, p g := by
          rw [Nat.cast_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun g hg => (hpg g (Finset.sdiff_subset hg)).symm
        have h2 : (c : ℝ) * ∑ g ∈ C₁, p g ≤ ((∑ i ∈ B₁, c * e i : ℕ) : ℝ) := by
          have hgv1 : M.goodValue p C₁ = ∑ g ∈ C₁, p g := by simp [goodValue, hsup]
          have hbud_le : M.budgetSum (M.buyerNeighborhood p C₁) ≤ M.budgetSum B₁ :=
            Finset.sum_le_sum_of_subset_of_nonneg hnbr_sub fun i _ _ => M.budget_nonneg i
          have hbudB₁ : M.budgetSum B₁ = ∑ i ∈ B₁, (e i : ℝ) := by simp [budgetSum, he]
          have hcast : ((∑ i ∈ B₁, c * e i : ℕ) : ℝ) = (c : ℝ) * ∑ i ∈ B₁, (e i : ℝ) := by
            rw [Nat.cast_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => Nat.cast_mul c (e i)
          rw [hcast, ← hbudB₁]
          exact mul_le_mul_of_nonneg_left (hgv1 ▸ hinvC₁.trans hbud_le) (Nat.cast_nonneg c)
        have hC_sum : (∑ g ∈ C₁, p g) + (∑ g ∈ C₂, p g) = (M_C : ℝ) := by
          rw [← Finset.sum_union Finset.disjoint_sdiff,
            Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
          have hgvC : M.goodValue p C = ∑ g ∈ C, p g := by simp [goodValue, hsup]
          have hbudC : M.budgetSum B = (M_C : ℝ) := by simp [budgetSum, M_C, he, Nat.cast_sum]
          rw [← hgvC, ← hbudC]
          exact hC_tight
        rw [Nat.cast_add, h1]
        have hmul_eq : ((c * M_C : ℕ) : ℝ) = (c : ℝ) * ∑ g ∈ C₁, p g + (c : ℝ) * ∑ g ∈ C₂, p g := by
          rw [Nat.cast_mul, ← hC_sum, mul_add]
        linarith
      exact (Nat.cast_le (α := ℝ)).1 hreal_ge |>.trans hcut_lb
  -- Obtain an integral maximum flow saturating `c * M_C`.
  obtain ⟨f, Xmin, -, hXmin, hfval⟩ :=
    Nint.exists_maxFlow_eq_minCut (by simp [Nint])
  have hXmin_cap : Nint.cutCapacity Xmin = c * M_C :=
    le_antisymm ((hXmin.2 {.source} ⟨by simp [Nint], by simp [Nint]⟩).trans hcap_src_cut.le)
      (hcut_ge Xmin hXmin.1)
  have hf_zero {u v : FlowVertex I G} (h0 : Nint.cap u v = 0) : f u v = 0 :=
    Nat.eq_zero_of_le_zero (h0 ▸ f.le_cap u v)
  let F : G → I → ℕ := fun g i => f (.good g) (.buyer i)
  have hF_supp : ∀ g i, 0 < F g i → g ∈ C ∧ i ∈ B ∧ M.IsEqualityEdge p i g := by
    intro g i hpos
    by_contra hnot
    have h0 : f (.good g) (.buyer i) = 0 := hf_zero (by simp [Nint, hnot])
    dsimp only [F] at hpos
    omega
  have hF_src (g : G) : f .source (.good g) = ∑ i ∈ B, F g i := by
    have hcons := f.conserve (.good g) (by simp [Nint]) (by simp [Nint])
    rw [sum_flowVertex, sum_flowVertex] at hcons
    have h1 : ∑ g' : G, f (.good g') (.good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    have h2 : ∑ i : I, f (.buyer i) (.good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    have h3 : f .sink (.good g) = 0 := hf_zero (by simp [Nint])
    have h4 : f (.good g) .source = 0 := hf_zero (by simp [Nint])
    have h5 : ∑ g' : G, f (.good g) (.good g') = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    have h6 : f (.good g) .sink = 0 := hf_zero (by simp [Nint])
    simp only [h1, h2, h3, h4, h5, h6, add_zero, zero_add] at hcons
    rw [hcons]
    symm
    exact Finset.sum_subset (Finset.subset_univ B) fun i _ hiB =>
      Nat.eq_zero_of_not_pos fun hpos => hiB (hF_supp g i hpos).2.1
  have hF_sink (i : I) : f (.buyer i) .sink = ∑ g ∈ C, F g i := by
    have hcons := f.conserve (.buyer i) (by simp [Nint]) (by simp [Nint])
    rw [sum_flowVertex, sum_flowVertex] at hcons
    have h1 : f .source (.buyer i) = 0 := hf_zero (by simp [Nint])
    have h2 : ∑ i' : I, f (.buyer i') (.buyer i) = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    have h3 : f .sink (.buyer i) = 0 := hf_zero (by simp [Nint])
    have h4 : f (.buyer i) .source = 0 := hf_zero (by simp [Nint])
    have h5 : ∑ g : G, f (.buyer i) (.good g) = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    have h6 : ∑ i' : I, f (.buyer i) (.buyer i') = 0 :=
      Finset.sum_eq_zero fun _ _ => hf_zero (by simp [Nint])
    simp only [h1, h2, h3, h4, h5, h6, add_zero, zero_add] at hcons
    rw [← hcons]
    symm
    exact Finset.sum_subset (Finset.subset_univ C) fun g _ hgC =>
      Nat.eq_zero_of_not_pos fun hpos => hgC (hF_supp g i hpos).1
  have hf_val_nat : ∑ g ∈ C, f .source (.good g) = c * M_C := by
    have hval_z : f.value = ∑ g ∈ C, (f .source (.good g) : ℤ) := by
      rw [Network.Flow.value, Network.Flow.netOut, sum_flowVertex, sum_flowVertex]
      have h1 : f .source .source = 0 := hf_zero (by simp [Nint])
      have h2 : ∑ i : I, (f .source (.buyer i) : ℤ) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have h0 : f .source (.buyer i) = 0 := hf_zero (by simp [Nint])
          simp [h0]
      have h3 : f .source .sink = 0 := hf_zero (by simp [Nint])
      have h4 : ∑ g : G, (f (.good g) .source : ℤ) = 0 :=
        Finset.sum_eq_zero fun g _ => by
          have h0 : f (.good g) .source = 0 := hf_zero (by simp [Nint])
          simp [h0]
      have h5 : ∑ i : I, (f (.buyer i) .source : ℤ) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have h0 : f (.buyer i) .source = 0 := hf_zero (by simp [Nint])
          simp [h0]
      have h6 : f .sink .source = 0 := hf_zero (by simp [Nint])
      simp only [Nint, h1, h2, h3, h4, h5, h6, Nat.cast_zero, add_zero, zero_add, sub_zero]
      symm
      exact Finset.sum_subset (Finset.subset_univ C) fun g _ hgC => by
        have h0 : f .source (.good g) = 0 := hf_zero (by simp [Nint, hgC])
        simp [h0]
    have hz : ((∑ g ∈ C, f .source (.good g) : ℕ) : ℤ) = ((c * M_C : ℕ) : ℤ) := by
      rw [Nat.cast_sum, ← hval_z, hfval, hXmin_cap]
    exact_mod_cast hz
  have hsatG : ∀ g ∈ C, ∑ i ∈ B, F g i = N g * M_C := by
    have hall := (Finset.sum_eq_sum_iff_of_le fun g hg => by
      simpa [Nint, hg] using f.le_cap .source (.good g)).1 (hf_val_nat.trans hsum_src.symm)
    intro g hg
    rw [← hF_src g]
    exact hall g hg
  have hsatB : ∀ i ∈ B, ∑ g ∈ C, F g i = c * e i := by
    have hsumB : ∑ i ∈ B, f (.buyer i) .sink = ∑ i ∈ B, c * e i := by
      calc
        ∑ i ∈ B, f (.buyer i) .sink = ∑ i ∈ B, ∑ g ∈ C, F g i :=
          Finset.sum_congr rfl fun i _ => hF_sink i
        _ = ∑ g ∈ C, ∑ i ∈ B, F g i := Finset.sum_comm
        _ = ∑ g ∈ C, N g * M_C := Finset.sum_congr rfl hsatG
        _ = c * M_C := hsum_src
        _ = ∑ i ∈ B, c * e i := hsum_sink.symm
    have hall := (Finset.sum_eq_sum_iff_of_le fun i hi => by
      simpa [Nint, hi] using f.le_cap (.buyer i) .sink).1 hsumB
    intro i hi
    rw [← hF_sink i]
    exact hall i hi
  exact ⟨F, hF_supp, hsatG, hsatB⟩

/-- **Theorem 5.1, part 4 (integer inputs)** ([Vazirani2007], Section 5.2, p. 107; Section 5.10,
Lemma 5.12, pp. 118–119): every non-degenerate unit-supply linear Fisher market with integer
utilities `u i g ≤ U` and integer budgets `e i` (total budget `E = ∑ i, e i`) admits a rational
equilibrium `(xQ, pQ)` with explicit polynomial-bit bounds:
* `(pQ g).den ≤ n * U ^ n` and `(pQ g).num.natAbs ≤ E * U ^ n`,
* `(xQ i g).den ≤ E * U ^ n` and `(xQ i g).num.natAbs ≤ E * U ^ n`,
where `n = Fintype.card G`. -/
theorem exists_rational_equilibrium_of_nat {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ)) :
    let n := Fintype.card G
    let E := ∑ i : I, e i
    ∃ (xQ : I → G → ℚ) (pQ : G → ℚ),
      M.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) ∧
      (∀ g, (pQ g).den ≤ n * U ^ n ∧ (pQ g).num.natAbs ≤ E * U ^ n) ∧
      (∀ i g, (xQ i g).den ≤ E * U ^ n ∧ (xQ i g).num.natAbs ≤ E * U ^ n) := by
  classical
  intro n E
  by_cases hG : Nonempty G
  · obtain ⟨x, p, heq⟩ := hnd.exists_isEquilibrium
    have hbb := (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).1 heq
    obtain ⟨hp, hx_nn, hclear, hexp, hmax_bb⟩ := hbb
    have hmc := (exists_isEquilibrium_iff_minCut hp hnd.buyer_nonsatiated hnd.good_desired).1
      ⟨x, heq⟩
    have hinv : M.SatisfiesInvariant p := hmc.1
    -- Every buyer spends positive budget, hence has an equality edge to some good.
    have hbuyer_edge : ∀ i : I, ∃ g : G, M.IsEqualityEdge p i g := by
      intro i
      have hexp_pos : ∑ _g : G, (0 : ℝ) < ∑ g : G, p g * x i g := by
        rw [Finset.sum_const_zero, ← expenditure_eq_sum, hexp i]
        exact hnd.budget_pos i
      obtain ⟨g, -, hg_pos⟩ := Finset.exists_lt_of_sum_lt hexp_pos
      have hx_pos : 0 < x i g := by
        by_contra hle
        push Not at hle
        have hx0 : x i g = 0 := le_antisymm hle (hx_nn i g)
        rw [hx0, mul_zero] at hg_pos
        exact lt_irrefl _ hg_pos
      exact ⟨g, hmax_bb i g hx_pos⟩
    have hnbr_univ : M.buyerNeighborhood p Finset.univ = Finset.univ := by
      ext i
      simp only [mem_buyerNeighborhood, Finset.mem_univ, true_and, iff_true]
      exact hbuyer_edge i
    have hsum_p_eq : ∑ g : G, p g = ∑ i : I, M.budget i := by
      calc
        ∑ g : G, p g = ∑ g : G, p g * M.supply g := by simp [hsup]
        _ = ∑ g : G, p g * ∑ i : I, x i g := Finset.sum_congr rfl fun g _ => by rw [hclear g]
        _ = ∑ g : G, ∑ i : I, p g * x i g := Finset.sum_congr rfl fun g _ => Finset.mul_sum _ _ _
        _ = ∑ i : I, ∑ g : G, p g * x i g := Finset.sum_comm
        _ = ∑ i : I, M.budget i := Finset.sum_congr rfl fun i _ => by
            rw [← expenditure_eq_sum, hexp i]
    have huniv_tight : M.IsTightSet p Finset.univ := by
      rw [IsTightSet, hnbr_univ, goodValue, budgetSum]
      simpa [hsup] using hsum_p_eq
    -- Connected components of goods in the equality graph.
    let adj : G → G → Prop := fun g₁ g₂ =>
      g₁ ∈ (Finset.univ : Finset G) ∧ g₂ ∈ (Finset.univ : Finset G) ∧
        ∃ i : I, M.IsEqualityEdge p i g₁ ∧ M.IsEqualityEdge p i g₂
    have hadj_symm : ∀ g₁ g₂, adj g₁ g₂ → adj g₂ g₁ := by
      rintro g₁ g₂ ⟨h1, h2, i, hE1, hE2⟩
      exact ⟨h2, h1, i, hE2, hE1⟩
    have hrt_symm : ∀ g₁ g₂, Relation.ReflTransGen adj g₁ g₂ → Relation.ReflTransGen adj g₂ g₁ := by
      intro g₁ g₂ h
      induction h with
      | refl => exact .refl
      | @tail b c _ hbc ih => exact Relation.ReflTransGen.head (hadj_symm b c hbc) ih
    let comp : G → Finset G := fun g₀ =>
      Finset.univ.filter fun g => Relation.ReflTransGen adj g₀ g
    have hmem_comp_self (g : G) : g ∈ comp g := Finset.mem_filter.2 ⟨Finset.mem_univ g, .refl⟩
    have hcomp_eq {g₁ g₂ : G} (h : g₂ ∈ comp g₁) : comp g₂ = comp g₁ := by
      have h12 : Relation.ReflTransGen adj g₁ g₂ := (Finset.mem_filter.1 h).2
      ext g
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h2g => h12.trans h2g, fun h1g => (hrt_symm g₁ g₂ h12).trans h1g⟩
    -- Package rational price & integral flow data per component `C` (depends only on `C`).
    let CompData (C : Finset G) : Prop :=
      ∃ (c : ℕ) (N : G → ℕ) (F : G → I → ℕ),
        let B := M.buyerNeighborhood p C
        let M_C := ∑ i ∈ B, e i
        0 < c ∧ c ≤ C.card * U ^ (C.card - 1) ∧ 1 ≤ U ∧ 0 < M_C ∧
        (∀ g ∈ C, 0 < N g ∧ N g ≤ U ^ (C.card - 1) ∧ (c : ℝ) * p g = ((N g * M_C : ℕ) : ℝ)) ∧
        (∀ g i, 0 < F g i → g ∈ C ∧ i ∈ B ∧ M.IsEqualityEdge p i g) ∧
        (∀ g ∈ C, ∑ i ∈ B, F g i = N g * M_C) ∧
        (∀ i ∈ B, ∑ g ∈ C, F g i = c * e i)
    have hCompData : ∀ C : Finset G, (∃ g₀, C = comp g₀) → CompData C := by
      rintro C ⟨g₀, rfl⟩
      obtain ⟨c, N, hc_pos, hc_le, hc_sum, hU_ge1, hMC_pos, hC_tight, hC_spec⟩ :=
        tightSet_component_rat hsup hu hU he hnd.buyer_nonsatiated hp hinv huniv_tight
          (Finset.mem_univ g₀)
      obtain ⟨F, hF_supp, hF_satG, hF_satB⟩ :=
        exists_int_component_flow hsup he hp hinv hC_tight hc_sum fun g hg => (hC_spec g hg).2.2
      exact ⟨c, N, F, hc_pos, hc_le, hU_ge1, hMC_pos, hC_spec, hF_supp, hF_satG, hF_satB⟩
    let cOf (C : Finset G) : ℕ :=
      if h : ∃ g₀, C = comp g₀ then (hCompData C h).choose else 1
    let NOf (C : Finset G) : G → ℕ :=
      if h : ∃ g₀, C = comp g₀ then (hCompData C h).choose_spec.choose else fun _ => 1
    let FOf (C : Finset G) : G → I → ℕ :=
      if h : ∃ g₀, C = comp g₀ then (hCompData C h).choose_spec.choose_spec.choose else fun _ _ => 0
    have hcomp_spec (g₀ : G) :
        let C := comp g₀
        let B := M.buyerNeighborhood p C
        let M_C := ∑ i ∈ B, e i
        0 < cOf C ∧ cOf C ≤ C.card * U ^ (C.card - 1) ∧ 1 ≤ U ∧ 0 < M_C ∧
        (∀ g ∈ C, 0 < NOf C g ∧ NOf C g ≤ U ^ (C.card - 1) ∧
          (cOf C : ℝ) * p g = ((NOf C g * M_C : ℕ) : ℝ)) ∧
        (∀ g i, 0 < FOf C g i → g ∈ C ∧ i ∈ B ∧ M.IsEqualityEdge p i g) ∧
        (∀ g ∈ C, ∑ i ∈ B, FOf C g i = NOf C g * M_C) ∧
        (∀ i ∈ B, ∑ g ∈ C, FOf C g i = cOf C * e i) := by
      have hex : ∃ g', comp g₀ = comp g' := ⟨g₀, rfl⟩
      simpa only [cOf, NOf, FOf, hex, ↓reduceDIte] using
        (hCompData (comp g₀) hex).choose_spec.choose_spec.choose_spec
    let MOf (C : Finset G) : ℕ := ∑ i ∈ M.buyerNeighborhood p C, e i
    let pQ : G → ℚ := fun g =>
      ((NOf (comp g) g * MOf (comp g) : ℕ) : ℚ) / (cOf (comp g) : ℚ)
    let xQ : I → G → ℚ := fun i g =>
      (FOf (comp g) g i : ℚ) / ((NOf (comp g) g * MOf (comp g) : ℕ) : ℚ)
    have hpQ_eq (g : G) : (pQ g : ℝ) = p g := by
      obtain ⟨hc_pos, -, -, -, hNspec, -, -, -⟩ := hcomp_spec g
      obtain ⟨-, -, hpg⟩ := hNspec g (hmem_comp_self g)
      have hc0 : (cOf (comp g) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc_pos.ne'
      simp only [pQ, MOf, Rat.cast_div, Rat.cast_natCast]
      exact (div_eq_iff hc0).2 (by linarith [hpg])
    have hxQ_nn (i : I) (g : G) : 0 ≤ (xQ i g : ℝ) := by
      simp only [xQ, Rat.cast_div, Rat.cast_natCast]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hxQ_clear (g : G) : ∑ i : I, (xQ i g : ℝ) = M.supply g := by
      obtain ⟨-, -, -, hMC_pos, hNspec, hFsupp, hFsatG, -⟩ := hcomp_spec g
      obtain ⟨hNg_pos, -, -⟩ := hNspec g (hmem_comp_self g)
      have hden_pos : 0 < NOf (comp g) g * MOf (comp g) := Nat.mul_pos hNg_pos hMC_pos
      have hden_ne : ((NOf (comp g) g * MOf (comp g) : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.2 hden_pos.ne'
      have hsum_F : ∑ i : I, (FOf (comp g) g i : ℝ) =
          ((NOf (comp g) g * MOf (comp g) : ℕ) : ℝ) := by
        have hsub : ∑ i : I, (FOf (comp g) g i : ℝ) =
            ∑ i ∈ M.buyerNeighborhood p (comp g), (FOf (comp g) g i : ℝ) := by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun i _ hiB => ?_
          have h0 : FOf (comp g) g i = 0 :=
            Nat.eq_zero_of_not_pos fun hpos => hiB (hFsupp g i hpos).2.1
          simp [h0]
        rw [hsub, ← Nat.cast_sum, hFsatG g (hmem_comp_self g)]
      simp only [xQ, Rat.cast_div, Rat.cast_natCast]
      rw [← Finset.sum_div, hsum_F, div_self hden_ne, hsup g]
    have hxQ_exp (i : I) :
        expenditure (fun g => (pQ g : ℝ)) (fun g => (xQ i g : ℝ)) = M.budget i := by
      obtain ⟨g_i, hE_i⟩ := hbuyer_edge i
      set C_i := comp g_i
      have hi_in_B : i ∈ M.buyerNeighborhood p C_i :=
        mem_buyerNeighborhood.2 ⟨g_i, hmem_comp_self g_i, hE_i⟩
      obtain ⟨hc_pos, -, -, -, -, -, -, hFsatB⟩ := hcomp_spec g_i
      have hzero_out : ∀ g : G, g ∉ C_i → (xQ i g : ℝ) = 0 := by
        intro g hgNot
        have hF0 : FOf (comp g) g i = 0 := by
          refine Nat.eq_zero_of_not_pos fun hpos => hgNot ?_
          obtain ⟨-, hiBg, hEg⟩ := (hcomp_spec g).2.2.2.2.2.1 g i hpos
          have hadj : adj g_i g := ⟨Finset.mem_univ _, Finset.mem_univ _, i, hE_i, hEg⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_univ g, Relation.ReflTransGen.single hadj⟩
        simp [xQ, hF0]
      have hterm_in : ∀ g ∈ C_i, (pQ g : ℝ) * (xQ i g : ℝ) = (FOf C_i g i : ℝ) / (cOf C_i : ℝ) := by
        intro g hg
        have hcg : comp g = C_i := hcomp_eq hg
        obtain ⟨-, -, -, hMC_pos, hNspec, -, -, -⟩ := hcomp_spec g_i
        obtain ⟨hNg_pos, -, -⟩ := hNspec g hg
        have hden_ne : ((NOf C_i g * MOf C_i : ℕ) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.2 (Nat.mul_pos hNg_pos hMC_pos).ne'
        simp only [pQ, xQ, hcg, Rat.cast_div, Rat.cast_natCast]
        rw [div_mul_div_comm, mul_comm ((NOf C_i g * MOf C_i : ℕ) : ℝ),
          mul_div_mul_right _ _ hden_ne]
      have hc0 : (cOf C_i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc_pos.ne'
      calc
        expenditure (fun g => (pQ g : ℝ)) (fun g => (xQ i g : ℝ))
          = ∑ g : G, (pQ g : ℝ) * (xQ i g : ℝ) := expenditure_eq_sum _ _
        _ = ∑ g ∈ C_i, (pQ g : ℝ) * (xQ i g : ℝ) := by
            symm
            exact Finset.sum_subset (Finset.subset_univ C_i) fun g _ hg => by
              rw [hzero_out g hg, mul_zero]
        _ = ∑ g ∈ C_i, (FOf C_i g i : ℝ) / (cOf C_i : ℝ) := Finset.sum_congr rfl hterm_in
        _ = (∑ g ∈ C_i, (FOf C_i g i : ℝ)) / (cOf C_i : ℝ) := (Finset.sum_div _ _ _).symm
        _ = ((cOf C_i * e i : ℕ) : ℝ) / (cOf C_i : ℝ) := by
            rw [← Nat.cast_sum, hFsatB i hi_in_B]
        _ = (e i : ℝ) := by rw [Nat.cast_mul, mul_div_cancel_left₀ _ hc0]
        _ = M.budget i := (he i).symm
    have hxQ_bb (i : I) (g : G) (hpos : 0 < (xQ i g : ℝ)) :
        ∀ g', M.bangPerBuck (fun g => (pQ g : ℝ)) i g' ≤
          M.bangPerBuck (fun g => (pQ g : ℝ)) i g := by
      have hFpos : 0 < FOf (comp g) g i := by
        by_contra h0
        have hF0 : FOf (comp g) g i = 0 := Nat.eq_zero_of_not_pos h0
        simp [xQ, hF0] at hpos
      have hE : M.IsEqualityEdge p i g := ((hcomp_spec g).2.2.2.2.2.1 g i hFpos).2.2
      have hpeq : (fun g' => (pQ g' : ℝ)) = p := funext hpQ_eq
      rw [hpeq]
      exact hE
    have hEqQ : M.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) :=
      (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).2
        ⟨fun g => (hpQ_eq g).symm ▸ hp g, hxQ_nn, hxQ_clear, hxQ_exp, hxQ_bb⟩
    -- Check denominator and numerator bounds for `pQ` and `xQ`.
    have hpQ_bounds (g : G) : (pQ g).den ≤ n * U ^ n ∧ (pQ g).num.natAbs ≤ E * U ^ n := by
      obtain ⟨hc_pos, hc_le, hU_ge1, -, hNspec, -, -, -⟩ := hcomp_spec g
      obtain ⟨-, hNg_le, -⟩ := hNspec g (hmem_comp_self g)
      obtain ⟨hden_c, hnum_NM⟩ := rat_div_nat_bounds (a := NOf (comp g) g * MOf (comp g)) hc_pos
      have hC_le_n : (comp g).card ≤ n := Finset.card_le_univ _
      have hpow_le : U ^ ((comp g).card - 1) ≤ U ^ n :=
        Nat.pow_le_pow_right hU_ge1 (by omega)
      have hMC_le_E : MOf (comp g) ≤ E :=
        Finset.sum_le_univ_sum_of_nonneg fun i => Nat.zero_le (e i)
      refine ⟨hden_c.trans (hc_le.trans (Nat.mul_le_mul hC_le_n hpow_le)),
        hnum_NM.trans ?_⟩
      calc
        NOf (comp g) g * MOf (comp g) ≤ U ^ n * E :=
          Nat.mul_le_mul (hNg_le.trans hpow_le) hMC_le_E
        _ = E * U ^ n := Nat.mul_comm _ _
    have hxQ_bounds (i : I) (g : G) :
        (xQ i g).den ≤ E * U ^ n ∧ (xQ i g).num.natAbs ≤ E * U ^ n := by
      obtain ⟨-, -, hU_ge1, hMC_pos, hNspec, hFsupp, hFsatG, -⟩ := hcomp_spec g
      obtain ⟨hNg_pos, hNg_le, -⟩ := hNspec g (hmem_comp_self g)
      have hden_pos : 0 < NOf (comp g) g * MOf (comp g) := Nat.mul_pos hNg_pos hMC_pos
      obtain ⟨hden_le, hnum_le⟩ := rat_div_nat_bounds (a := FOf (comp g) g i) hden_pos
      have hF_le : FOf (comp g) g i ≤ NOf (comp g) g * MOf (comp g) := by
        by_cases hiB : i ∈ M.buyerNeighborhood p (comp g)
        · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (FOf (comp g) g j)) hiB).trans
            (hFsatG g (hmem_comp_self g)).le
        · have h0 : FOf (comp g) g i = 0 :=
            Nat.eq_zero_of_not_pos fun hpos => hiB (hFsupp g i hpos).2.1
          omega
      have hC_le_n : (comp g).card ≤ n := Finset.card_le_univ _
      have hpow_le : U ^ ((comp g).card - 1) ≤ U ^ n :=
        Nat.pow_le_pow_right hU_ge1 (by omega)
      have hMC_le_E : MOf (comp g) ≤ E :=
        Finset.sum_le_univ_sum_of_nonneg fun j => Nat.zero_le (e j)
      have hNM_le : NOf (comp g) g * MOf (comp g) ≤ E * U ^ n := by
        calc
          NOf (comp g) g * MOf (comp g) ≤ U ^ n * E :=
            Nat.mul_le_mul (hNg_le.trans hpow_le) hMC_le_E
          _ = E * U ^ n := Nat.mul_comm _ _
      exact ⟨hden_le.trans hNM_le, hnum_le.trans (hF_le.trans hNM_le)⟩
    exact ⟨xQ, pQ, hEqQ, hpQ_bounds, hxQ_bounds⟩
  · -- Empty goods type: `I` is also empty by `buyer_nonsatiated`, so `(0, 0)` is trivially an eq.
    have : IsEmpty G := not_nonempty_iff.1 hG
    have : IsEmpty I := ⟨fun i => let ⟨g, _⟩ := hnd.buyer_nonsatiated i; isEmptyElim g⟩
    refine ⟨0, 0, ?_, fun g => isEmptyElim g, fun i => isEmptyElim i⟩
    exact (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).2
      ⟨fun g => isEmptyElim g, fun i => isEmptyElim i, fun g => isEmptyElim g,
        fun i => isEmptyElim i, fun i => isEmptyElim i⟩

/-- **Theorem 5.1, part 4 (general rational inputs)** ([Vazirani2007], Section 5.2, pp. 107–108;
Section 5.10, Lemma 5.12, pp. 118–119): every non-degenerate unit-supply linear Fisher market with
rational utilities `uQ i g` and rational budgets `eQ i` whose numerators are bounded by `B_num` and
denominators by `B_den` admits a rational equilibrium `(xQ, pQ)` whose numerators and denominators
satisfy explicit polynomial-bit bounds in `m = Fintype.card I`, `n = Fintype.card G`, `B_num`, and
`B_den`. -/
theorem exists_rational_equilibrium_of_rat {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1)
    {uQ : I → G → ℚ} (hu : ∀ i g, M.utility i g = (uQ i g : ℝ))
    {eQ : I → ℚ} (he : ∀ i, M.budget i = (eQ i : ℝ))
    {B_num B_den : ℕ}
    (hnum_u : ∀ i g, (uQ i g).num.natAbs ≤ B_num)
    (hden_u : ∀ i g, (uQ i g).den ≤ B_den)
    (hnum_e : ∀ i, (eQ i).num.natAbs ≤ B_num)
    (hden_e : ∀ i, (eQ i).den ≤ B_den) :
    let m := Fintype.card I
    let n := Fintype.card G
    let U := B_num * B_den ^ n
    let E := m * B_num * B_den ^ m
    ∃ (xQ : I → G → ℚ) (pQ : G → ℚ),
      M.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) ∧
      (∀ g, (pQ g).den ≤ n * U ^ n * B_den ^ m ∧ (pQ g).num.natAbs ≤ E * U ^ n) ∧
      (∀ i g, (xQ i g).den ≤ E * U ^ n ∧ (xQ i g).num.natAbs ≤ E * U ^ n) := by
  classical
  intro m n U E
  by_cases hG : Nonempty G
  · -- Clear denominators per buyer for utilities and globally for budgets.
    let L_u : I → ℕ := fun i => ∏ g : G, (uQ i g).den
    let L_e : ℕ := ∏ i : I, (eQ i).den
    have hLu_pos (i : I) : 0 < L_u i :=
      Finset.prod_pos fun g _ => Nat.pos_of_ne_zero (uQ i g).den_nz
    have hLe_pos : 0 < L_e :=
      Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (eQ i).den_nz
    have hLu_le (i : I) : L_u i ≤ B_den ^ n := by
      calc
        ∏ g : G, (uQ i g).den ≤ ∏ _g : G, B_den := Finset.prod_le_prod fun g _ => hden_u i g
        _ = B_den ^ n := by simp [n]
    have hLe_le : L_e ≤ B_den ^ m := by
      calc
        ∏ i : I, (eQ i).den ≤ ∏ _i : I, B_den := Finset.prod_le_prod fun i _ => hden_e i
        _ = B_den ^ m := by simp [m]
    let uN : I → G → ℕ := fun i g => (uQ i g).num.natAbs * (L_u i / (uQ i g).den)
    let eN : I → ℕ := fun i => (eQ i).num.natAbs * (L_e / (eQ i).den)
    have huN_eq (i : I) (g : G) : (uN i g : ℝ) = (L_u i : ℝ) * M.utility i g := by
      have hnn_q : 0 ≤ uQ i g := by
        have : (0 : ℝ) ≤ (uQ i g : ℝ) := hu i g ▸ M.utility_nonneg i g
        exact_mod_cast this
      have hdvd : (uQ i g).den ∣ L_u i :=
        Finset.dvd_prod_of_mem (fun g' => (uQ i g').den) (Finset.mem_univ g)
      have hden_ne : ((uQ i g).den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (uQ i g).den_nz
      rw [hu i g]
      have hrat : (uQ i g : ℝ) = ((uQ i g).num.natAbs : ℝ) / ((uQ i g).den : ℝ) := by
        simpa [Rat.cast_div, Rat.cast_natCast] using
          congrArg (Rat.cast (K := ℝ)) (rat_eq_natAbs_div_den hnn_q)
      rw [hrat, mul_div_assoc', eq_div_iff hden_ne]
      have hnat : uN i g * (uQ i g).den = L_u i * (uQ i g).num.natAbs := by
        dsimp only [uN]
        rw [mul_assoc, Nat.div_mul_cancel hdvd, mul_comm]
      exact_mod_cast hnat
    have heN_eq (i : I) : (eN i : ℝ) = (L_e : ℝ) * M.budget i := by
      have hnn_q : 0 ≤ eQ i := by
        have : (0 : ℝ) ≤ (eQ i : ℝ) := he i ▸ M.budget_nonneg i
        exact_mod_cast this
      have hdvd : (eQ i).den ∣ L_e :=
        Finset.dvd_prod_of_mem (fun j => (eQ j).den) (Finset.mem_univ i)
      have hden_ne : ((eQ i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (eQ i).den_nz
      rw [he i]
      have hrat : (eQ i : ℝ) = ((eQ i).num.natAbs : ℝ) / ((eQ i).den : ℝ) := by
        simpa [Rat.cast_div, Rat.cast_natCast] using
          congrArg (Rat.cast (K := ℝ)) (rat_eq_natAbs_div_den hnn_q)
      rw [hrat, mul_div_assoc', eq_div_iff hden_ne]
      have hnat : eN i * (eQ i).den = L_e * (eQ i).num.natAbs := by
        dsimp only [eN]
        rw [mul_assoc, Nat.div_mul_cancel hdvd, mul_comm]
      exact_mod_cast hnat
    have huN_le (i : I) (g : G) : uN i g ≤ U :=
      Nat.mul_le_mul (hnum_u i g) ((Nat.div_le_self _ _).trans (hLu_le i))
    have heN_sum_le : ∑ i : I, eN i ≤ E := by
      calc
        ∑ i : I, eN i ≤ ∑ _i : I, (B_num * B_den ^ m) := Finset.sum_le_sum fun i _ =>
          Nat.mul_le_mul (hnum_e i) ((Nat.div_le_self _ _).trans hLe_le)
        _ = m * (B_num * B_den ^ m) := by simp [m]
        _ = E := by simp [E, mul_assoc]
    -- Build the scaled integer unit-supply market `M_int`.
    let M_int : LinearFisherMarket I G :=
      unitSupply (fun i => (eN i : ℝ)) (fun i g => (uN i g : ℝ))
        (fun i => Nat.cast_nonneg _) (fun i g => Nat.cast_nonneg _)
    have hnd_int : M_int.IsNonDegenerate := {
      budget_pos := fun i => by
        simp only [M_int, unitSupply_budget, heN_eq]
        exact mul_pos (Nat.cast_pos.2 hLe_pos) (hnd.budget_pos i)
      supply_pos := fun g => by simp [M_int]
      buyer_nonsatiated := fun i => by
        obtain ⟨g, hg⟩ := hnd.buyer_nonsatiated i
        refine ⟨g, ?_⟩
        simp only [M_int, unitSupply_utility, huN_eq]
        exact mul_pos (Nat.cast_pos.2 (hLu_pos i)) hg
      good_desired := fun g => by
        obtain ⟨i, hi⟩ := hnd.good_desired g
        refine ⟨i, ?_⟩
        simp only [M_int, unitSupply_utility, huN_eq]
        exact mul_pos (Nat.cast_pos.2 (hLu_pos i)) hi
    }
    obtain ⟨xQ, pIntQ, hEq_int, hpInt_bounds, hxQ_bounds⟩ :=
      exists_rational_equilibrium_of_nat (M := M_int) hnd_int (fun g => by simp [M_int])
        (u := uN) (fun _ _ => by simp [M_int]) huN_le (e := eN) (fun _ => by simp [M_int])
    obtain ⟨hpInt_pos, hxQ_nn, hxQ_clear, hxQ_exp_int, hxQ_bb_int⟩ :=
      (isEquilibrium_iff_bangPerBuck hnd_int.buyer_nonsatiated hnd_int.good_desired).1 hEq_int
    let pQ : G → ℚ := fun g => pIntQ g / (L_e : ℚ)
    have hLe_pos_r : (0 : ℝ) < (L_e : ℝ) := Nat.cast_pos.2 hLe_pos
    have hEqM : M.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) := by
      refine (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).2
        ⟨fun g => ?_, hxQ_nn, fun g => by rw [hxQ_clear g, unitSupply_supply, hsup g],
          fun i => ?_, fun i g hpos g' => ?_⟩
      · simp only [pQ, Rat.cast_div, Rat.cast_natCast]
        exact div_pos (hpInt_pos g) hLe_pos_r
      · have hexp_i := hxQ_exp_int i
        rw [expenditure_eq_sum] at hexp_i
        simp only [M_int, unitSupply_budget, heN_eq] at hexp_i
        have hsum : expenditure (fun g => (pQ g : ℝ)) (fun g => (xQ i g : ℝ)) =
            (∑ g : G, (pIntQ g : ℝ) * (xQ i g : ℝ)) / (L_e : ℝ) := by
          rw [expenditure_eq_sum]
          simp only [pQ, Rat.cast_div, Rat.cast_natCast, div_mul_eq_mul_div, Finset.sum_div]
        rw [hsum, hexp_i, mul_div_cancel_left₀ _ hLe_pos_r.ne']
      · have hbb := hxQ_bb_int i g hpos g'
        have hscale (g₀ : G) :
            M_int.bangPerBuck (fun g₁ => (pIntQ g₁ : ℝ)) i g₀ =
              ((L_u i : ℝ) / (L_e : ℝ)) * M.bangPerBuck (fun g₁ => (pQ g₁ : ℝ)) i g₀ := by
          simp only [bangPerBuck_eq, M_int, unitSupply_utility, huN_eq, pQ, Rat.cast_div,
            Rat.cast_natCast]
          field_simp [hLe_pos_r.ne', (hpInt_pos g₀).ne']
        rw [hscale g', hscale g] at hbb
        exact le_of_mul_le_mul_left hbb (div_pos (Nat.cast_pos.2 (hLu_pos i)) hLe_pos_r)
    have hpQ_bounds (g : G) :
        (pQ g).den ≤ n * U ^ n * B_den ^ m ∧ (pQ g).num.natAbs ≤ E * U ^ n := by
      have hpInt_nn_q : 0 ≤ pIntQ g := by
        have : (0 : ℝ) ≤ (pIntQ g : ℝ) := (hpInt_pos g).le
        exact_mod_cast this
      have hpQ_frac : pQ g = ((pIntQ g).num.natAbs : ℚ) / (((pIntQ g).den * L_e : ℕ) : ℚ) :=
        (congrArg (· / (L_e : ℚ)) (rat_eq_natAbs_div_den hpInt_nn_q)).trans
          (by rw [div_div, Nat.cast_mul])
      have hden_pos : 0 < (pIntQ g).den * L_e :=
        Nat.mul_pos (Nat.pos_of_ne_zero (pIntQ g).den_nz) hLe_pos
      obtain ⟨hden_le, hnum_le⟩ := rat_div_nat_bounds (a := (pIntQ g).num.natAbs) hden_pos
      rw [← hpQ_frac] at hden_le hnum_le
      obtain ⟨hpi_den, hpi_num⟩ := hpInt_bounds g
      exact ⟨hden_le.trans (Nat.mul_le_mul hpi_den hLe_le),
        hnum_le.trans (hpi_num.trans (Nat.mul_le_mul_right _ heN_sum_le))⟩
    have hxQ_bounds' (i : I) (g : G) :
        (xQ i g).den ≤ E * U ^ n ∧ (xQ i g).num.natAbs ≤ E * U ^ n := by
      obtain ⟨hd, hn⟩ := hxQ_bounds i g
      exact ⟨hd.trans (Nat.mul_le_mul_right _ heN_sum_le),
        hn.trans (Nat.mul_le_mul_right _ heN_sum_le)⟩
    exact ⟨xQ, pQ, hEqM, hpQ_bounds, hxQ_bounds'⟩
  · have : IsEmpty G := not_nonempty_iff.1 hG
    have : IsEmpty I := ⟨fun i => let ⟨g, _⟩ := hnd.buyer_nonsatiated i; isEmptyElim g⟩
    refine ⟨0, 0, ?_, fun g => isEmptyElim g, fun i => isEmptyElim i⟩
    exact (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).2
      ⟨fun g => isEmptyElim g, fun i => isEmptyElim i, fun g => isEmptyElim g,
        fun i => isEmptyElim i, fun i => isEmptyElim i⟩

end Rationality

end Cslib.GameTheory.Market.LinearFisherMarket
