/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
public import CslibFrontier.Algorithms.Lean.MaxFlow.RealFlow
public import Mathlib.Basic.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Transitive Trust Graphs and Sybilproof Reputation Mechanisms

Formalizes transitive trust graphs, contraction-based Sybil strategies, symmetric impossibility
theorems, and the value- and rank-sybilproofness properties of capacity-constrained maximum-flow
and shortest-path (`Pathrank`) reputation mechanisms from Section 27.5 (Definitions 27.2–27.4 and
27.6, Theorems 27.5 and 27.7–27.9, Figure 27.2, and Exercise 27.8, pp. 689–693, 697) of Eric
Friedman, Paul Resnick, and Rahul Sami, *"Manipulation-Resistant Reputation Systems"*, Chapter 27
of *Algorithmic Game Theory* [FriedmanResnickSami2007], following Alice Cheng and Eric Friedman,
*"Sybilproof Reputation Mechanisms"* [ChengFriedman2005].

## Model and source mapping

* **Trust graphs (`TrustGraph V`, `relabel`, `contract`):** directed loop-free nonnegative real
  trust matrices `weight : V → V → ℝ` (`0` for absent edges). Functorial vertex contraction
  `G.contract π` sums weights across distinct `π`-fibers and zeroes induced self-loops, satisfying
  `contract_contract : (G.contract f).contract g = G.contract (g ∘ f)` unconditionally.
* **Sybil strategies (`SybilStrategy G v`, Definition 27.2, p. 691; [ChengFriedman2005,
  Definition 2, p. 129]):** an extended trust graph `S.graph` on finite vertex type `S.Vertex`
  together with a collapse map `S.collapse : S.Vertex → V` whose fiber over `v` is a nonempty
  Sybil cluster `S.sybils`, whose restriction outside `S.sybils` is bijective with
  `{w : V // w ≠ v}` via `S.honestEmbed`, and whose contraction `S.graph.contract S.collapse`
  equals `G` (preserving honest-to-honest weights and additive incoming/outgoing trust sums while
  permitting arbitrary internal fake edges among `S.sybils`).
* **Global symmetric reputation functions (`GlobalRepFn`):**
  * **Theorem 27.7 (`GlobalRepFn.not_isKRankSybilproof_of_isSymmetric`, pp. 691–692;
    [ChengFriedman2005, Theorem 2, p. 130]):** for every `1 ≤ K`, no nontrivial isomorphism-
    invariant reputation function is `K`-rank-sybilproof (`|U'| ≤ K + 1`), proved by step-by-step
    `1`-Sybil splitting along `G ⊔ G.contract (clamp k)` (`1 ≤ k ≤ |V|`).
  * **Theorem 27.5 (`GlobalRepFn.not_isRankSybilproof_of_isSymmetric`, p. 691;
    [ChengFriedman2005, Theorem 1, p. 130]):** immediate `K = 1` corollary.
  * **Section 27.5.1 (`GlobalRepFn.not_isRankStrategyproof_of_isSymmetric`, p. 690):** no
    nontrivial symmetric reputation function is rank-strategyproof against unilateral changes to a
    vertex's outgoing ratings.
* **Seeded reputation functions (`SeededRepFn`), Max-Flow (`maxFlowRep`), and Pathrank
  (`pathrankRep`):**
  * **Theorem 27.8 (`isValueSybilproof_maxFlowRep`, `not_isRankSybilproof_maxFlowRep`, p. 692;
    Figure 27.2 & Exercise 27.8):** `maxFlowRep G s v = minRealCutBetween G.weight s v` (certified
    equal to maximum `s`–`v` flow for `s ≠ v` by `isMaxRealFlow_maxFlowRep` via
    `isMaxRealFlow_minRealCutBetween`) is value-sybilproof via cut pullback
    `cutWeight_pullback_eq_contract`, but fails rank-sybilproofness (even with `1` extra Sybil and
    unmoved incoming links) on Figure 27.2 (`maxFlowCounterexampleGraph`,
    `maxFlowCounterexampleSybil`).
  * **Theorem 27.9 and Section 27.5.1 (`isValueSybilproof_pathrankRep`,
    `isRankSybilproof_pathrankRep`, `isRankStrategyproof_pathrankRep`, `isMonotonic_pathrankRep`,
    pp. 690, 692; [ChengFriedman2005, Theorem 5, p. 131]):** `pathrankRep G s v =
    ((1 + pathrankDist G s v)⁻¹).toReal`, where `pathrankDist` is shortest-walk length under
    inverse-trust edge lengths `(ENNReal.ofReal (G.weight x y))⁻¹`, is value-sybilproof,
    rank-sybilproof, rank-strategyproof, and monotonic.

## Main definitions

* `Cslib.GameTheory.Reputation.TrustGraph`, `TrustGraph.empty`, `TrustGraph.relabel`,
  `TrustGraph.contract`, `TrustGraph.disjointUnion`
* `Cslib.GameTheory.Reputation.SybilStrategy`, `SybilStrategy.sybils`, `SybilStrategy.honest`
* `Cslib.GameTheory.Reputation.GlobalRepFn`, `GlobalRepFn.IsSymmetric`, `GlobalRepFn.IsNontrivial`,
  `GlobalRepFn.IsValueSybilproof`, `GlobalRepFn.IsRankSybilproof`, `GlobalRepFn.IsKRankSybilproof`,
  `GlobalRepFn.IsRankStrategyproof`
* `Cslib.GameTheory.Reputation.SeededRepFn`, `SeededRepFn.IsValueSybilproof`,
  `SeededRepFn.IsRankSybilproof`, `SeededRepFn.IsRankStrategyproof`, `SeededRepFn.IsMonotonic`
* `Cslib.GameTheory.Reputation.maxFlowRep`, `maxFlowCounterexampleGraph`,
  `maxFlowCounterexampleSybil`, `walkInvTrustLen`, `pathrankDist`, `pathrankRep`

## Main results

* `Cslib.GameTheory.Reputation.TrustGraph.contract_contract` and `cutWeight_pullback_eq_contract`:
  functorial contraction and exact cut-weight pullback.
* `Cslib.GameTheory.Reputation.GlobalRepFn.not_isKRankSybilproof_of_isSymmetric` and
  `not_isRankSybilproof_of_isSymmetric`: Theorems 27.7 and 27.5.
* `Cslib.GameTheory.Reputation.GlobalRepFn.not_isRankStrategyproof_of_isSymmetric`: §27.5.1
  impossibility.
* `Cslib.GameTheory.Reputation.isValueSybilproof_maxFlowRep` and `not_isRankSybilproof_maxFlowRep`:
  Theorem 27.8 and Figure 27.2 / Exercise 27.8.
* `Cslib.GameTheory.Reputation.isValueSybilproof_pathrankRep`, `isRankSybilproof_pathrankRep`,
  `isRankStrategyproof_pathrankRep`, and `isMonotonic_pathrankRep`: Theorem 27.9 and §27.5.1
  possibility.

## References

* [E. Friedman, P. Resnick, and R. Sami, *Manipulation-Resistant Reputation
  Systems*][FriedmanResnickSami2007]
* [A. Cheng and E. Friedman, *Sybilproof Reputation Mechanisms*][ChengFriedman2005]
-/

public section

open Finset
open scoped ENNReal

namespace Cslib.GameTheory.Reputation

open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut

/-! ### Trust graphs and functorial contraction -/

/-- Loop-free directed trust graph with nonnegative real edge weights
[FriedmanResnickSami2007, §27.5, p. 689; ChengFriedman2005, §3, p. 129]. -/
@[ext]
structure TrustGraph (V : Type*) where
  /-- Nonnegative trust weight `weight u v` assigned by `u` to `v` (`0` when absent). -/
  weight : V → V → ℝ
  /-- All trust weights are nonnegative. -/
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  /-- Self-loops carry zero weight (`weight v v = 0`). -/
  weight_diag : ∀ v, weight v v = 0

namespace TrustGraph

/-- Empty trust graph with zero trust on all pairs. -/
@[expose] def empty (V : Type*) : TrustGraph V where
  weight _ _ := 0
  weight_nonneg _ _ := le_rfl
  weight_diag _ := rfl

@[simp]
theorem empty_weight (V : Type*) (u v : V) : (empty V).weight u v = 0 :=
  rfl

/-- Transport a trust graph along a bijection `e : V ≃ V'`. -/
def relabel {V V' : Type*} (e : V ≃ V') (G : TrustGraph V) : TrustGraph V' where
  weight u' v' := G.weight (e.symm u') (e.symm v')
  weight_nonneg _ _ := G.weight_nonneg _ _
  weight_diag _ := G.weight_diag _

@[simp]
theorem relabel_weight {V V' : Type*} (e : V ≃ V') (G : TrustGraph V) (u' v' : V') :
    (G.relabel e).weight u' v' = G.weight (e.symm u') (e.symm v') := by
  rfl

/-- Disjoint union `G₁ ⊔ G₂` of two trust graphs on `V₁ ⊕ V₂`, with zero cross-component edges. -/
def disjointUnion {V₁ V₂ : Type*} (G₁ : TrustGraph V₁) (G₂ : TrustGraph V₂) :
    TrustGraph (V₁ ⊕ V₂) where
  weight
    | Sum.inl u₁, Sum.inl v₁ => G₁.weight u₁ v₁
    | Sum.inr u₂, Sum.inr v₂ => G₂.weight u₂ v₂
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
  weight_nonneg x y := by
    cases x <;> cases y
    · exact G₁.weight_nonneg _ _
    · exact le_rfl
    · exact le_rfl
    · exact G₂.weight_nonneg _ _
  weight_diag x := by
    cases x
    · exact G₁.weight_diag _
    · exact G₂.weight_diag _

/-- Contract a finite trust graph `G'` along `π : V' → V`, summing weights across distinct
`π`-fibers and deleting induced self-loops [FriedmanResnickSami2007, Definition 27.2, p. 691;
ChengFriedman2005, Definition 2, p. 129]. -/
def contract {V' V : Type*} [Fintype V'] [DecidableEq V] (π : V' → V) (G' : TrustGraph V') :
    TrustGraph V where
  weight u v :=
    if u = v then 0
    else ∑ x ∈ univ.filter (fun x => π x = u), ∑ y ∈ univ.filter (fun y => π y = v), G'.weight x y
  weight_nonneg u v := by
    split_ifs
    · exact le_rfl
    · exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => G'.weight_nonneg _ _
  weight_diag v := by simp

@[simp]
theorem contract_weight_of_ne {V' V : Type*} [Fintype V'] [DecidableEq V] (π : V' → V)
    (G' : TrustGraph V') {u v : V} (huv : u ≠ v) :
    (G'.contract π).weight u v =
      ∑ x ∈ univ.filter (fun x => π x = u), ∑ y ∈ univ.filter (fun y => π y = v), G'.weight x y :=
  ite_eq_right huv

@[simp]
theorem contract_id {V : Type*} [Fintype V] [DecidableEq V] (G : TrustGraph V) :
    G.contract id = G := by
  ext u v
  by_cases huv : u = v
  · subst huv; simp [contract, G.weight_diag]
  · rw [contract_weight_of_ne id G huv]
    simp [Finset.filter_eq']

private theorem sum_filter_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (p : X → Y) (z₀ : Z) (q : Y → Z) (H : X → ℝ) :
    ∑ y ∈ univ.filter (fun y => q y = z₀), ∑ x ∈ univ.filter (fun x => p x = y), H x =
      ∑ x ∈ univ.filter (fun x => q (p x) = z₀), H x := by
  refine (sum_congr rfl fun y hy => sum_congr ?_ fun _ _ => rfl).trans
    (sum_fiberwise_of_maps_to (s := univ.filter fun x : X => q (p x) = z₀)
      (t := univ.filter fun y : Y => q y = z₀) (g := p)
      (fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩) H)
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ (mem_filter.mp hy).2, h⟩, fun h => h.2⟩

/-- Functoriality of trust-graph contraction: contracting along `f` and then `g` equals contracting
along `g ∘ f`. -/
theorem contract_contract {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq C]
    (f : A → B) (g : B → C) (G : TrustGraph A) :
    (G.contract f).contract g = G.contract (g ∘ f) := by
  ext c₁ c₂
  by_cases hc : c₁ = c₂
  · subst hc
    rw [((G.contract f).contract g).weight_diag, (G.contract (g ∘ f)).weight_diag]
  · rw [contract_weight_of_ne g (G.contract f) hc, contract_weight_of_ne (g ∘ f) G hc]
    calc ∑ b₁ ∈ univ.filter (fun b => g b = c₁),
          ∑ b₂ ∈ univ.filter (fun b => g b = c₂), (G.contract f).weight b₁ b₂
        = ∑ b₁ ∈ univ.filter (fun b => g b = c₁),
            ∑ b₂ ∈ univ.filter (fun b => g b = c₂),
              ∑ a₁ ∈ univ.filter (fun a => f a = b₁),
                ∑ a₂ ∈ univ.filter (fun a => f a = b₂), G.weight a₁ a₂ :=
          sum_congr rfl fun b₁ hb₁ => sum_congr rfl fun b₂ hb₂ =>
            contract_weight_of_ne f G fun h =>
              hc ((mem_filter.mp hb₁).2.symm.trans (h ▸ (mem_filter.mp hb₂).2))
      _ = ∑ b₁ ∈ univ.filter (fun b => g b = c₁),
            ∑ a₁ ∈ univ.filter (fun a => f a = b₁),
              ∑ b₂ ∈ univ.filter (fun b => g b = c₂),
                ∑ a₂ ∈ univ.filter (fun a => f a = b₂), G.weight a₁ a₂ :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ b₁ ∈ univ.filter (fun b => g b = c₁),
            ∑ a₁ ∈ univ.filter (fun a => f a = b₁),
              ∑ a₂ ∈ univ.filter (fun a => g (f a) = c₂), G.weight a₁ a₂ :=
          sum_congr rfl fun _ _ => sum_congr rfl fun a₁ _ =>
            sum_filter_comp f c₂ g (fun a₂ => G.weight a₁ a₂)
      _ = ∑ a₁ ∈ univ.filter (fun a => g (f a) = c₁),
            ∑ a₂ ∈ univ.filter (fun a => g (f a) = c₂), G.weight a₁ a₂ :=
          sum_filter_comp f c₁ g fun a₁ =>
            ∑ a₂ ∈ univ.filter (fun a => g (f a) = c₂), G.weight a₁ a₂

/-- Pulling a vertex cut `X ⊆ V` back along `π : V' → V` preserves `cutWeight` identically against
`G'.contract π`. -/
theorem cutWeight_pullback_eq_contract {V' V : Type*} [Fintype V'] [DecidableEq V'] [Fintype V]
    [DecidableEq V] (π : V' → V) (G' : TrustGraph V') (X : Finset V) :
    cutWeight G'.weight (univ.filter fun x' => π x' ∈ X) = cutWeight (G'.contract π).weight X := by
  have hfib : ∀ (S : Finset V) (f : V' → ℝ),
      ∑ x' ∈ univ.filter (fun x' => π x' ∈ S), f x' =
        ∑ u ∈ S, ∑ x' ∈ univ.filter (fun x' => π x' = u), f x' := fun S f => by
    rw [← sum_fiberwise_of_maps_to (t := S) (g := π) (fun _ hx => (mem_filter.mp hx).2) f]
    refine sum_congr rfl fun u hu => sum_congr ?_ fun _ _ => rfl
    ext x'
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩
  have hcompl : univ \ univ.filter (fun x' => π x' ∈ X) =
      univ.filter (fun y' => π y' ∈ univ \ X) := Finset.ext fun _ => by simp
  rw [cutWeight, cutWeight, hcompl, hfib X]
  refine sum_congr rfl fun u hu => ?_
  simp_rw [hfib (univ \ X)]
  rw [sum_comm]
  exact sum_congr rfl fun v hv =>
    (contract_weight_of_ne π G' fun h => (mem_sdiff.mp hv).2 (by rwa [← h])).symm

end TrustGraph

/-! ### Contraction-based Sybil strategies (Definition 27.2) -/

/-- **Sybil strategy** `(G', U')` for user `v` in trust graph `G`
([FriedmanResnickSami2007, Definition 27.2, p. 691; ChengFriedman2005, Definition 2, p. 129]):
an extended finite trust graph `graph` on `Vertex` with collapse map `collapse : Vertex → V` whose
fiber over `v` is nonempty, whose non-`v` vertices correspond bijectively to honest users `w ≠ v`,
and whose contraction `graph.contract collapse` recovers `G`. -/
structure SybilStrategy {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (v : V) where
  /-- Extended vertex type after creating Sybil identities. -/
  Vertex : Type
  /-- Finiteness of the extended vertex set. -/
  instFintype : Fintype Vertex
  /-- Decidable equality on the extended vertex set. -/
  instDecidableEq : DecidableEq Vertex
  /-- Modified trust graph on `Vertex`. -/
  graph : TrustGraph Vertex
  /-- Contraction map collapsing all Sybils onto `v` and keeping honest users distinct. -/
  collapse : Vertex → V
  /-- User `v` has at least one Sybil representative (`v ∈ U'`). -/
  exists_collapse_eq : ∃ u : Vertex, collapse u = v
  /-- Embedding of honest users `w ≠ v` into `Vertex`. -/
  honestEmbed : {w : V // w ≠ v} → Vertex
  /-- `collapse` is left-inverse to `honestEmbed`. -/
  collapse_honestEmbed : ∀ w : {w : V // w ≠ v}, collapse (honestEmbed w) = w.1
  /-- Every non-Sybil vertex (`collapse x ≠ v`) is the image of its honest user. -/
  honestEmbed_collapse : ∀ (x : Vertex) (hx : collapse x ≠ v), honestEmbed ⟨collapse x, hx⟩ = x
  /-- Collapsing the Sybil cluster onto `v` yields `G`. -/
  contract_eq : graph.contract collapse = G

attribute [instance] SybilStrategy.instFintype SybilStrategy.instDecidableEq

namespace SybilStrategy

variable {V : Type} [Fintype V] [DecidableEq V] {G : TrustGraph V} {v : V}
  (S : SybilStrategy G v)

/-- The Sybil subset `U' ⊆ S.Vertex` of identities collapsing onto `v`. -/
def sybils : Finset S.Vertex :=
  univ.filter fun x => S.collapse x = v

@[simp]
theorem mem_sybils {x : S.Vertex} : x ∈ S.sybils ↔ S.collapse x = v := by
  simp [sybils]

theorem sybils_nonempty : S.sybils.Nonempty := by
  obtain ⟨u, hu⟩ := S.exists_collapse_eq
  exact ⟨u, S.mem_sybils.mpr hu⟩

/-- Image of an honest user `w ≠ v` in `S.Vertex`. -/
def honest (w : V) (hw : w ≠ v) : S.Vertex :=
  S.honestEmbed ⟨w, hw⟩

@[simp]
theorem collapse_honest (w : V) (hw : w ≠ v) : S.collapse (S.honest w hw) = w :=
  S.collapse_honestEmbed ⟨w, hw⟩

theorem honest_notMem_sybils (w : V) (hw : w ≠ v) : S.honest w hw ∉ S.sybils := by
  rw [S.mem_sybils, S.collapse_honest]
  exact hw

theorem fiber_honest {w : V} (hw : w ≠ v) :
    univ.filter (fun x : S.Vertex => S.collapse x = w) = {S.honest w hw} := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  refine ⟨fun hx => ?_, fun h => h ▸ S.collapse_honest w hw⟩
  simp only [honest]
  convert (S.honestEmbed_collapse x (hx ▸ hw)).symm using 2
  exact Subtype.ext hx.symm

theorem weight_honest_honest {w₁ w₂ : V} (hw₁ : w₁ ≠ v) (hw₂ : w₂ ≠ v) :
    S.graph.weight (S.honest w₁ hw₁) (S.honest w₂ hw₂) = G.weight w₁ w₂ := by
  by_cases h12 : w₁ = w₂
  · subst h12
    rw [S.graph.weight_diag, G.weight_diag]
  · conv_rhs => rw [← S.contract_eq]
    rw [TrustGraph.contract_weight_of_ne _ _ h12, S.fiber_honest hw₁, S.fiber_honest hw₂]
    simp

theorem sum_weight_honest_sybils {w : V} (hw : w ≠ v) :
    ∑ u ∈ S.sybils, S.graph.weight (S.honest w hw) u = G.weight w v := by
  conv_rhs => rw [← S.contract_eq]
  rw [TrustGraph.contract_weight_of_ne _ _ hw, S.fiber_honest hw]
  simp [sybils]

theorem sum_weight_sybils_honest {w : V} (hw : w ≠ v) :
    ∑ u ∈ S.sybils, S.graph.weight u (S.honest w hw) = G.weight v w := by
  conv_rhs => rw [← S.contract_eq]
  rw [TrustGraph.contract_weight_of_ne _ _ hw.symm, S.fiber_honest hw]
  simp [sybils]

end SybilStrategy

/-! ### Global reputation functions and symmetric impossibility (Theorems 27.5 & 27.7, §27.5.1) -/

/-- Global cardinal reputation aggregation mechanism `F : TrustGraph V → V → ℝ`
[FriedmanResnickSami2007, §27.5, p. 689; ChengFriedman2005, Definition 1, p. 129]. -/
abbrev GlobalRepFn : Type 1 :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], TrustGraph V → V → ℝ

namespace GlobalRepFn

/-- Isomorphism invariance (symmetry) of a global reputation function
[FriedmanResnickSami2007, §27.5, p. 690; ChengFriedman2005, Definition 6, p. 130]. -/
@[expose] def IsSymmetric (F : GlobalRepFn) : Prop :=
  ∀ {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (G : TrustGraph V) (e : V ≃ V') (x : V), F (G.relabel e) (e x) = F G x

/-- Nontriviality: on at least one finite trust graph, `F` distinguishes two vertices
[FriedmanResnickSami2007, §27.5, p. 689; ChengFriedman2005, §4.1, p. 130]. -/
@[expose] def IsNontrivial (F : GlobalRepFn) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : TrustGraph V) (v w : V), F G v < F G w

/-- **Value-sybilproofness** ([FriedmanResnickSami2007, Definition 27.3, p. 691;
ChengFriedman2005, Definition 5, p. 130]): no Sybil identity achieves strictly higher value than
`v`'s honest score. -/
@[expose] def IsValueSybilproof (F : GlobalRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (v : V) (S : SybilStrategy G v),
    ∀ u ∈ S.sybils, F S.graph u ≤ F G v

/-- **Rank-sybilproofness** ([FriedmanResnickSami2007, Definition 27.4, p. 691;
ChengFriedman2005, Definition 3, p. 129]): no Sybil identity overtakes or ties an honest user `w`
who strictly outranked `v`. -/
@[expose] def IsRankSybilproof (F : GlobalRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (v : V) (S : SybilStrategy G v),
    ∀ u ∈ S.sybils, ∀ (w : V) (hw : w ≠ v),
      F G v < F G w → F S.graph u < F S.graph (S.honest w hw)

/-- **`K`-rank-sybilproofness** ([FriedmanResnickSami2007, Definition 27.6, p. 691]):
rank-sybilproofness against Sybil strategies creating at most `K` additional identities
(`|U'| ≤ K + 1`). -/
@[expose] def IsKRankSybilproof (K : ℕ) (F : GlobalRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (v : V) (S : SybilStrategy G v),
    S.sybils.card ≤ K + 1 →
      ∀ u ∈ S.sybils, ∀ (w : V) (hw : w ≠ v),
        F G v < F G w → F S.graph u < F S.graph (S.honest w hw)

/-- **Rank-strategyproofness** ([FriedmanResnickSami2007, §27.5.1, p. 690]): no user `v` can
improve her weak-order ranking relative to another user `w` (turning `<` into `≥` or `≤` into `>`)
by unilaterally altering her outgoing trust ratings. -/
@[expose] def IsRankStrategyproof (F : GlobalRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G G' : TrustGraph V) (v : V),
    (∀ x, x ≠ v → ∀ y, G'.weight x y = G.weight x y) →
      ∀ w : V, (F G v < F G w → F G' v < F G' w) ∧ (F G v ≤ F G w → F G' v ≤ F G' w)

theorem IsRankSybilproof.isKRankSybilproof {F : GlobalRepFn} (h : F.IsRankSybilproof) (K : ℕ) :
    F.IsKRankSybilproof K :=
  fun G v S _ u hu w hw hlt => h G v S u hu w hw hlt

theorem IsKRankSybilproof.mono {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) {F : GlobalRepFn}
    (h : F.IsKRankSybilproof K₂) : F.IsKRankSybilproof K₁ :=
  fun G v S hcard => h G v S (hcard.trans (Nat.add_le_add_right hK 1))

private def clampFin {n k : ℕ} (hk : 1 ≤ k) (i : Fin n) : Fin k :=
  ⟨min i.1 (k - 1), by omega⟩

private def stepFin {k : ℕ} (hk : 1 ≤ k) (i : Fin (k + 1)) : Fin k :=
  ⟨min i.1 (k - 1), by omega⟩

private theorem stepFin_comp_clampFin {n k : ℕ} (hk : 1 ≤ k) :
    stepFin hk ∘ clampFin (Nat.le_add_left 1 k) = clampFin (n := n) hk := by
  ext i
  simp only [Function.comp_apply, stepFin, clampFin, Nat.add_sub_cancel, min_assoc]
  simp

/-- **Theorem 27.7** ([FriedmanResnickSami2007, pp. 691–692];
[ChengFriedman2005, Theorem 2, p. 130]): for every `1 ≤ K`, there is no nontrivial symmetric
`K`-rank-sybilproof reputation function. -/
theorem not_isKRankSybilproof_of_isSymmetric {K : ℕ} (hK : 1 ≤ K) {F : GlobalRepFn}
    (hSym : F.IsSymmetric) (hNontriv : F.IsNontrivial) : ¬ F.IsKRankSybilproof K := by
  intro hSPK
  have hSP1 : F.IsKRankSybilproof 1 := hSPK.mono hK
  obtain ⟨V₀, instFin, instDec, G₀, v₀, w₀, hlt₀⟩ := hNontriv
  let _ := instFin
  let _ := instDec
  let n := Fintype.card V₀
  have hn2 : 2 ≤ n := Fintype.one_lt_card_iff.mpr ⟨v₀, w₀, fun h => hlt₀.ne (h ▸ rfl)⟩
  let eBase : V₀ ≃ Fin n := Fintype.equivFin V₀
  let lastIdx : Fin n := ⟨n - 1, by omega⟩
  let e : V₀ ≃ Fin n := eBase.trans (Equiv.swap (eBase w₀) lastIdx)
  let G : TrustGraph (Fin n) := G₀.relabel e
  let v : Fin n := e v₀
  have hew₀ : e w₀ = lastIdx := by simp [e]
  have hv_lt : F G v < F G lastIdx := by
    linarith [hSym G₀ e v₀, hew₀ ▸ hSym G₀ e w₀]
  have hvw : v ≠ lastIdx := fun h => hv_lt.ne (h ▸ rfl)
  let H : ∀ k : ℕ, 1 ≤ k → TrustGraph (Fin k) := fun k hk => G.contract (clampFin hk)
  -- Step 0: G → G ⊔ H 1 adds a single isolated Sybil `Sum.inr 0` for `v`.
  have hstep1 : F (G.disjointUnion (H 1 le_rfl)) (Sum.inr ⟨0, Nat.zero_lt_one⟩) <
      F (G.disjointUnion (H 1 le_rfl)) (Sum.inl lastIdx) := by
    let S₀ : SybilStrategy G v :=
      { Vertex := Fin n ⊕ Fin 1
        instFintype := inferInstance
        instDecidableEq := inferInstance
        graph := G.disjointUnion (H 1 le_rfl)
        collapse := Sum.elim id (fun _ => v)
        exists_collapse_eq := ⟨Sum.inr 0, rfl⟩
        honestEmbed := fun w => Sum.inl w.1
        collapse_honestEmbed := fun _ => rfl
        honestEmbed_collapse := fun x hx => by
          cases x with | inl _ => rfl | inr _ => exact absurd rfl hx
        contract_eq := by
          ext a b
          by_cases hab : a = b
          · subst hab; rw [TrustGraph.weight_diag, G.weight_diag]
          · have hflt : ∀ u : Fin n,
                univ.filter (fun x : Fin n ⊕ Fin 1 => Sum.elim id (fun _ => v) x = u) =
                  if u = v then {Sum.inl v, Sum.inr 0} else {Sum.inl u} := fun u => by
              ext (_ | z)
              · by_cases h : u = v <;> simp [h]
              · by_cases h : u = v <;> simp [h, Subsingleton.elim z 0, eq_comm]
            rw [TrustGraph.contract_weight_of_ne _ _ hab, hflt a, hflt b]
            rcases eq_or_ne a v with rfl | hav <;> rcases eq_or_ne b v with rfl | hbv
            · exact absurd rfl hab
            all_goals simp [*, TrustGraph.disjointUnion] }
    have hcard : S₀.sybils.card ≤ 2 :=
      (card_le_card (t := {Sum.inl v, Sum.inr 0}) fun
        | .inl _, hx => by simpa [S₀] using S₀.mem_sybils.mp hx
        | .inr z, _ => by simp [Subsingleton.elim z 0]).trans (card_insert_le _ _)
    exact hSP1 G v S₀ hcard (Sum.inr 0) (by simp [S₀, SybilStrategy.sybils]) lastIdx hvw.symm hv_lt
  -- Inductive step: `Sum.inr ⟨k - 1, _⟩` stays strictly below `Sum.inl lastIdx` (`1 ≤ k ≤ n`).
  have hind : ∀ (k : ℕ) (hk1 : 1 ≤ k), k ≤ n →
      F (G.disjointUnion (H k hk1)) (Sum.inr ⟨k - 1, by omega⟩) <
        F (G.disjointUnion (H k hk1)) (Sum.inl lastIdx) := by
    intro k
    induction k with
    | zero => intro hk1; omega
    | succ m ih =>
      intro _ hmn
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · exact hstep1
      · have hm_ge1 : 1 ≤ m := hm_pos
        have hprev := ih hm_ge1 (by omega)
        let target : Fin n ⊕ Fin m := Sum.inr ⟨m - 1, by omega⟩
        let πStep : Fin n ⊕ Fin (m + 1) → Fin n ⊕ Fin m :=
          Sum.map id (stepFin hm_ge1)
        let Sk : SybilStrategy (G.disjointUnion (H m hm_ge1)) target :=
          { Vertex := Fin n ⊕ Fin (m + 1)
            instFintype := inferInstance
            instDecidableEq := inferInstance
            graph := G.disjointUnion (H (m + 1) (by omega))
            collapse := πStep
            exists_collapse_eq := ⟨Sum.inr ⟨m, by omega⟩, by simp [πStep, target, stepFin]⟩
            honestEmbed := fun w => Sum.map id (Fin.castLE (by omega)) w.1
            collapse_honestEmbed := fun ⟨w, hw⟩ => by
              rcases w with i | j
              · rfl
              · have hne : j.1 ≠ m - 1 := fun hv => hw (congrArg Sum.inr (Fin.ext hv))
                simp [πStep, stepFin, Nat.min_eq_left (by omega : j.1 ≤ m - 1)]
            honestEmbed_collapse := fun x hx => by
              rcases x with i | j
              · rfl
              · simp only [πStep, Sum.map_inr, stepFin, target, ne_eq, Sum.inr.injEq,
                  Fin.ext_iff] at hx
                simp [πStep, stepFin, Nat.min_eq_left (by omega : j.1 ≤ m - 1)]
            contract_eq := by
              have hcomp : (H (m + 1) (by omega)).contract (stepFin hm_ge1) = H m hm_ge1 := by
                simp only [H, TrustGraph.contract_contract, stepFin_comp_clampFin]
              ext a b
              by_cases hab : a = b
              · subst hab; rw [TrustGraph.weight_diag, (G.disjointUnion (H m hm_ge1)).weight_diag]
              · rw [TrustGraph.contract_weight_of_ne _ _ hab]
                rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂
                · simp [sum_filter, Fintype.sum_sum_type, πStep, TrustGraph.disjointUnion]
                · simp [sum_filter, Fintype.sum_sum_type, πStep, TrustGraph.disjointUnion]
                · simp [sum_filter, Fintype.sum_sum_type, πStep, TrustGraph.disjointUnion]
                · have hab' : a₂ ≠ b₂ := fun h => hab (by simp [h])
                  dsimp only [TrustGraph.disjointUnion]
                  rw [← hcomp, TrustGraph.contract_weight_of_ne (stepFin hm_ge1) _ hab']
                  simp [sum_filter, Fintype.sum_sum_type, πStep] }
        have hcard : Sk.sybils.card ≤ 2 :=
          (card_le_card (t := {Sum.inr ⟨m - 1, by omega⟩, Sum.inr ⟨m, by omega⟩}) fun
            | .inl _, hx => absurd (Sk.mem_sybils.mp hx) (by simp [Sk, πStep, target])
            | .inr j, hx => by
              have hjm := Sk.mem_sybils.mp hx
              simp only [Sk, πStep, Sum.map_inr, stepFin, target, Sum.inr.injEq, Fin.ext_iff] at hjm
              simp only [mem_insert, mem_singleton, Sum.inr.injEq, Fin.ext_iff]
              omega).trans (card_insert_le _ _)
        simpa [Sk, SybilStrategy.honest] using hSP1 (G.disjointUnion (H m hm_ge1)) target Sk hcard
          (Sum.inr ⟨m, by omega⟩) (by simp [Sk, SybilStrategy.sybils, πStep, target, stepFin])
          (Sum.inl lastIdx) (by simp [target]) hprev
  have hfinal := hind n (by omega) le_rfl
  have hHn : H n (by omega) = G := by
    simp [H, (funext fun i => Fin.ext (Nat.min_eq_left (by omega)) :
      clampFin (n := n) (k := n) (by omega) = id)]
  rw [hHn] at hfinal
  have hrelabel : (G.disjointUnion G).relabel (Equiv.sumComm _ _) = G.disjointUnion G := by
    ext (_ | _) (_ | _) <;> rfl
  exact hfinal.ne
    (by simpa [hrelabel] using hSym (G.disjointUnion G) (Equiv.sumComm _ _) (Sum.inl lastIdx))

/-- **Theorem 27.5** ([FriedmanResnickSami2007, p. 691];
[ChengFriedman2005, Theorem 1, p. 130]): there is no nontrivial symmetric rank-sybilproof
reputation function. -/
theorem not_isRankSybilproof_of_isSymmetric {F : GlobalRepFn} (hSym : F.IsSymmetric)
    (hNontriv : F.IsNontrivial) : ¬ F.IsRankSybilproof :=
  fun h => not_isKRankSybilproof_of_isSymmetric le_rfl hSym hNontriv (h.isKRankSybilproof 1)

/-- **Section 27.5.1 impossibility** ([FriedmanResnickSami2007, p. 690]): there is no nontrivial
symmetric rank-strategyproof reputation function. -/
theorem not_isRankStrategyproof_of_isSymmetric {F : GlobalRepFn} (hSym : F.IsSymmetric)
    (hNontriv : F.IsNontrivial) : ¬ F.IsRankStrategyproof := by
  intro hRSP
  obtain ⟨V₀, instFin, instDec, G₀, v₀, w₀, hlt₀⟩ := hNontriv
  let _ := instFin
  let _ := instDec
  let n := Fintype.card V₀
  let e : V₀ ≃ Fin n := Fintype.equivFin V₀
  let G : TrustGraph (Fin n) := G₀.relabel e
  have hlt : F G (e v₀) < F G (e w₀) := by rwa [hSym G₀ e v₀, hSym G₀ e w₀]
  -- Prefix graphs `G_pref k` turn on outgoing edges of vertices `< k` one vertex at a time.
  let G_pref : ℕ → TrustGraph (Fin n) := fun k =>
    { weight := fun u v => if u.1 < k then G.weight u v else 0
      weight_nonneg := fun u v => by
        split_ifs
        exacts [G.weight_nonneg u v, le_rfl]
      weight_diag := fun v => by
        split_ifs
        exacts [G.weight_diag v, rfl] }
  have hconst : ∀ k ≤ n, ∀ x y : Fin n, F (G_pref k) x = F (G_pref k) y := by
    intro k
    induction k with
    | zero =>
      intro _ x y
      have hrel : (G_pref 0).relabel (Equiv.swap x y) = G_pref 0 :=
        TrustGraph.ext (funext₂ fun _ _ => rfl)
      simpa [hrel] using (hSym (G_pref 0) (Equiv.swap x y) x).symm
    | succ k ih =>
      intro hkn x y
      have ihk := ih (Nat.le_of_succ_le hkn)
      let uk : Fin n := ⟨k, hkn⟩
      have hout : ∀ a : Fin n, a ≠ uk → ∀ b : Fin n,
          (G_pref (k + 1)).weight a b = (G_pref k).weight a b := fun a ha _ => by
        have hak : a.1 < k + 1 ↔ a.1 < k := ⟨fun h => Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h)
          fun hv => ha (Fin.ext hv), Nat.lt_succ_of_lt⟩
        simp [G_pref, hak]
      have heq_uk : ∀ z : Fin n, F (G_pref (k + 1)) uk = F (G_pref (k + 1)) z := fun z =>
        le_antisymm ((hRSP (G_pref k) (G_pref (k + 1)) uk hout z).2 (ihk uk z).le) <|
          not_lt.mp fun hlt_z => ((hRSP (G_pref (k + 1)) (G_pref k) uk
            (fun a ha b => (hout a ha b).symm) z).1 hlt_z).ne (ihk uk z)
      exact (heq_uk x).symm.trans (heq_uk y)
  have hGn : G_pref n = G := TrustGraph.ext (funext₂ fun u _ => ite_eq_left u.2)
  exact hlt.ne (hGn ▸ hconst n le_rfl (e v₀) (e w₀))

end GlobalRepFn

/-! ### Seeded reputation functions, Max-Flow (Theorem 27.8), and Pathrank (Theorem 27.9) -/

/-- Seeded (rooted) cardinal reputation mechanism `F : TrustGraph V → (seed : V) → V → ℝ`
[FriedmanResnickSami2007, §27.5, p. 690; ChengFriedman2005, §4.2, p. 130]. -/
abbrev SeededRepFn : Type 1 :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], TrustGraph V → V → V → ℝ

namespace SeededRepFn

/-- **Value-sybilproofness** for a seeded reputation function ([FriedmanResnickSami2007,
Definition 27.3 & Theorem 27.8, pp. 691–692; ChengFriedman2005, Definition 5, p. 130]):
no non-seed attacker `v ≠ s` can create a Sybil identity `u ∈ S.sybils` whose score from the
seed exceeds `v`'s honest score. -/
@[expose] def IsValueSybilproof (F : SeededRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (s v : V) (hsv : v ≠ s)
    (S : SybilStrategy G v), ∀ u ∈ S.sybils,
      F S.graph (S.honest s hsv.symm) u ≤ F G s v

/-- **Rank-sybilproofness** for a seeded reputation function ([FriedmanResnickSami2007,
Definition 27.4 & Theorem 27.9, pp. 691–692; ChengFriedman2005, Definition 3, p. 129]):
no non-seed attacker `v ≠ s` can create a Sybil identity `u ∈ S.sybils` that ties or overtakes
any honest user `w ≠ v` who strictly outranked `v`. -/
@[expose] def IsRankSybilproof (F : SeededRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V) (s v : V) (hsv : v ≠ s)
    (S : SybilStrategy G v), ∀ u ∈ S.sybils, ∀ (w : V) (hw : w ≠ v),
      F G s v < F G s w →
        F S.graph (S.honest s hsv.symm) u < F S.graph (S.honest s hsv.symm) (S.honest w hw)

/-- **Rank-strategyproofness** for a seeded reputation function ([FriedmanResnickSami2007, §27.5.1,
p. 690]): no non-seed user `v ≠ s` can boost her weak-order ranking relative to any `w` by
changing her outgoing trust ratings. -/
@[expose] def IsRankStrategyproof (F : SeededRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G G' : TrustGraph V) (s v : V), v ≠ s →
    (∀ x, x ≠ v → ∀ y, G'.weight x y = G.weight x y) →
      ∀ w : V, (F G s v < F G s w → F G' s v < F G' s w) ∧ (F G s v ≤ F G s w → F G' s v ≤ F G' s w)

/-- **Monotonicity** of a seeded reputation function ([FriedmanResnickSami2007, §27.5, p. 690]):
increasing the trust weight on an incoming edge `(u, v)` (`u ≠ v`) never reduces `v`'s rank
relative to any node `w`. -/
@[expose] def IsMonotonic (F : SeededRepFn) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G G' : TrustGraph V) (s u v : V), u ≠ v →
    G.weight u v ≤ G'.weight u v →
    (∀ x y, (x, y) ≠ (u, v) → G'.weight x y = G.weight x y) →
      ∀ w : V, (F G s w < F G s v → F G' s w < F G' s v) ∧ (F G s w ≤ F G s v → F G' s w ≤ F G' s v)

end SeededRepFn

/-! #### Maximum-flow reputation (`maxFlowRep`, Theorem 27.8 & Figure 27.2) -/

/-- **Maximum-flow reputation** from trusted seed `s` to `v` ([FriedmanResnickSami2007, §27.5,
pp. 690, 692]): defined as `minRealCutBetween G.weight s v`, which equals the greatest value of a
feasible real `s`–`v` flow whenever `s ≠ v` (`isMaxRealFlow_maxFlowRep`). -/
noncomputable def maxFlowRep {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V)
    (s v : V) : ℝ :=
  minRealCutBetween G.weight s v

/-- For every non-seed vertex `v ≠ s`, `maxFlowRep G s v` is the maximum value of a feasible real
`s`–`v` flow in `G` (via `isMaxRealFlow_minRealCutBetween`). -/
theorem isMaxRealFlow_maxFlowRep {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V)
    {s v : V} (hsv : s ≠ v) : IsMaxRealFlow G.weight s v (maxFlowRep G s v) :=
  isMaxRealFlow_minRealCutBetween G.weight_nonneg hsv

/-- **Theorem 27.8** ([FriedmanResnickSami2007, p. 692]; [ChengFriedman2005, Theorem 4, p. 131]):
the maximum-flow reputation mechanism is **value-sybilproof**. -/
theorem isValueSybilproof_maxFlowRep : SeededRepFn.IsValueSybilproof maxFlowRep := by
  intro V _ _ G s v hsv S u hu
  obtain ⟨X, hsX, hvX, hXeq⟩ := exists_cutWeight_eq_minRealCutBetween G.weight hsv.symm
  let X' : Finset S.Vertex := univ.filter fun x' => S.collapse x' ∈ X
  have hsX' : S.honest s hsv.symm ∈ X' :=
    mem_filter.mpr ⟨mem_univ _, (S.collapse_honest s hsv.symm).symm ▸ hsX⟩
  have huX' : u ∉ X' := fun h => hvX ((S.mem_sybils.mp hu) ▸ (mem_filter.mp h).2)
  calc maxFlowRep S.graph (S.honest s hsv.symm) u
      ≤ cutWeight S.graph.weight X' := minRealCutBetween_le_cutWeight S.graph.weight hsX' huX'
    _ = cutWeight (S.graph.contract S.collapse).weight X :=
        TrustGraph.cutWeight_pullback_eq_contract S.collapse S.graph X
    _ = cutWeight G.weight X := by rw [S.contract_eq]
    _ = maxFlowRep G s v := hXeq

/-- Honest 3-vertex trust graph of **Figure 27.2** ([FriedmanResnickSami2007, p. 692]) on `Fin 3`
(`0 = s`, `1 = a`, `2 = b`): edges `s → a` of capacity `1`, `a → b` of capacity `7 / 10`, and
`s → b` of capacity `1 / 2`. -/
@[expose] noncomputable def maxFlowCounterexampleGraph : TrustGraph (Fin 3) where
  weight
    | 0, 1 => 1
    | 1, 2 => 7 / 10
    | 0, 2 => 1 / 2
    | _, _ => 0
  weight_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  weight_diag i := by fin_cases i <;> rfl

/-- Post-attack 4-vertex trust graph of **Figure 27.2** ([FriedmanResnickSami2007, p. 692]) on
`Fin 4` (`0 = s`, `1 = a`, `2 = b`, `3 = a'`): `a` retains incoming edge `s → a` (`1`) while Sybil
`a'` takes outgoing edge `a' → b` (`7 / 10`), severing the `s → a → b` flow path. -/
private noncomputable def maxFlowCounterexampleSybilGraph : TrustGraph (Fin 4) where
  weight
    | 0, 1 => 1
    | 3, 2 => 7 / 10
    | 0, 2 => 1 / 2
    | _, _ => 0
  weight_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  weight_diag i := by fin_cases i <;> rfl

/-- Explicit `1`-Sybil strategy for `a = 1` in **Figure 27.2** ([FriedmanResnickSami2007, p. 692;
Exercise 27.8, p. 697]), which also leaves all incoming trust edges to `a` unmoved. -/
noncomputable def maxFlowCounterexampleSybil : SybilStrategy maxFlowCounterexampleGraph 1 where
  Vertex := Fin 4
  instFintype := inferInstance
  instDecidableEq := inferInstance
  graph := maxFlowCounterexampleSybilGraph
  collapse
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 1
  exists_collapse_eq := ⟨1, rfl⟩
  honestEmbed w := if w.1 = 0 then 0 else 2
  collapse_honestEmbed := by
    rintro ⟨w, hw⟩
    fin_cases w
    · rfl
    · exact absurd rfl hw
    · rfl
  honestEmbed_collapse x hx := by
    fin_cases x
    · rfl
    · exact absurd rfl hx
    · rfl
    · exact absurd rfl hx
  contract_eq := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [TrustGraph.contract, sum_filter, Fin.sum_univ_four,
        maxFlowCounterexampleSybilGraph, maxFlowCounterexampleGraph] <;>
      norm_num

private theorem weight_le_cutWeight {V : Type*} [Fintype V] [DecidableEq V] (G : TrustGraph V)
    {X : Finset V} {u v : V} (hu : u ∈ X) (hv : v ∉ X) :
    G.weight u v ≤ cutWeight G.weight X := by
  rw [cutWeight]
  have h1 : G.weight u v ≤ ∑ w ∈ univ \ X, G.weight u w :=
    single_le_sum (fun w _ => G.weight_nonneg u w) (mem_sdiff.mpr ⟨mem_univ v, hv⟩)
  exact h1.trans (single_le_sum (fun x _ => sum_nonneg fun w _ => G.weight_nonneg x w) hu)

private theorem maxFlowRep_eq_of_cut {V : Type} [Fintype V] [DecidableEq V] (G : TrustGraph V)
    {s t : V} (hst : s ≠ t) {X₀ : Finset V} (hs₀ : s ∈ X₀) (ht₀ : t ∉ X₀) {c : ℝ}
    (hc : cutWeight G.weight X₀ = c)
    (hlow : ∀ X, s ∈ X → t ∉ X → c ≤ cutWeight G.weight X) :
    maxFlowRep G s t = c :=
  le_antisymm ((minRealCutBetween_le_cutWeight G.weight hs₀ ht₀).trans_eq hc)
    ((le_minRealCutBetween_iff G.weight hst c).mpr hlow)

private theorem maxFlowRep_maxFlowCounterexampleGraph :
    maxFlowRep maxFlowCounterexampleGraph 0 1 = 1 ∧
      maxFlowRep maxFlowCounterexampleGraph 0 2 = 6 / 5 := by
  refine ⟨?_, ?_⟩
  · refine maxFlowRep_eq_of_cut _ (by decide) (X₀ := {0, 2}) (by decide) (by decide) ?_
      fun _ hs ht => ?_
    · simp [cutWeight, Fin.sum_univ_three, maxFlowCounterexampleGraph]
    · simpa [maxFlowCounterexampleGraph] using
        weight_le_cutWeight maxFlowCounterexampleGraph hs ht
  · have hc01 : cutWeight maxFlowCounterexampleGraph.weight {0, 1} = 6 / 5 := by
      simp [cutWeight, Fin.sum_univ_three, maxFlowCounterexampleGraph]
      norm_num
    refine maxFlowRep_eq_of_cut _ (by decide) (X₀ := {0, 1}) (by decide) (by decide) hc01
      fun X hs ht => ?_
    have hX : X = if (1 : Fin 3) ∈ X then {0, 1} else {0} := by
      ext z
      fin_cases z <;> by_cases h1 : (1 : Fin 3) ∈ X <;> simp [hs, h1, ht]
    rw [hX]
    split_ifs
    · exact hc01.ge
    · simp [cutWeight, Fin.sum_univ_three, maxFlowCounterexampleGraph]
      norm_num

private theorem maxFlowRep_maxFlowCounterexampleSybilGraph :
    maxFlowRep maxFlowCounterexampleSybilGraph 0 1 = 1 ∧
      maxFlowRep maxFlowCounterexampleSybilGraph 0 2 = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · refine maxFlowRep_eq_of_cut _ (by decide) (X₀ := {0, 2, 3}) (by decide) (by decide) ?_
      fun _ hs ht => ?_
    · simp [cutWeight, Fin.sum_univ_four, maxFlowCounterexampleSybilGraph]
    · simpa [maxFlowCounterexampleSybilGraph] using
        weight_le_cutWeight maxFlowCounterexampleSybilGraph hs ht
  · refine maxFlowRep_eq_of_cut _ (by decide) (X₀ := {0, 1}) (by decide) (by decide) ?_
      fun _ hs ht => ?_
    · simp [cutWeight, Fin.sum_univ_four, maxFlowCounterexampleSybilGraph]
    · simpa [maxFlowCounterexampleSybilGraph] using
        weight_le_cutWeight maxFlowCounterexampleSybilGraph hs ht

/-- **Failure of rank-sybilproofness for Max-Flow** ([FriedmanResnickSami2007, p. 692, Figure 27.2;
Exercise 27.8, p. 697]): `maxFlowRep` is **not** rank-sybilproof (even against a single extra Sybil
with unmoved incoming links). -/
theorem not_isRankSybilproof_maxFlowRep : ¬ SeededRepFn.IsRankSybilproof maxFlowRep :=
    fun hRSP => by
  have hhon := maxFlowRep_maxFlowCounterexampleGraph
  have hsyb := maxFlowRep_maxFlowCounterexampleSybilGraph
  have hres := hRSP maxFlowCounterexampleGraph 0 1 (by decide) maxFlowCounterexampleSybil
    (1 : Fin 4) (maxFlowCounterexampleSybil.mem_sybils.mpr rfl) 2 (by decide) (by linarith)
  change maxFlowRep maxFlowCounterexampleSybilGraph 0 1 <
    maxFlowRep maxFlowCounterexampleSybilGraph 0 2 at hres
  linarith

/-! #### Pathrank reputation (`pathrankDist`, `pathrankRep`, Theorem 27.9 & §27.5.1) -/

/-- Inverse-trust edge length `(ENNReal.ofReal (G.weight u v))⁻¹ : ℝ≥0∞` (`⊤` when `weight u v = 0`)
[FriedmanResnickSami2007, §27.5, p. 690]. -/
@[expose] noncomputable def invTrustLen {V : Type*} (G : TrustGraph V) (u v : V) : ℝ≥0∞ :=
  (ENNReal.ofReal (G.weight u v))⁻¹

/-- Total inverse-trust length of a walk represented by vertex sequence `p : List V`
[FriedmanResnickSami2007, §27.5, p. 690]. -/
noncomputable def walkInvTrustLen {V : Type*} (G : TrustGraph V) (p : List V) : ℝ≥0∞ :=
  ((pathArcs p).map fun e => invTrustLen G e.1 e.2).sum

@[simp]
theorem walkInvTrustLen_nil {V : Type*} (G : TrustGraph V) : walkInvTrustLen G [] = 0 := by
  simp [walkInvTrustLen]

@[simp]
theorem walkInvTrustLen_singleton {V : Type*} (G : TrustGraph V) (x : V) :
    walkInvTrustLen G [x] = 0 := by
  simp [walkInvTrustLen]

@[simp]
theorem walkInvTrustLen_cons_cons {V : Type*} (G : TrustGraph V) (u v : V) (rest : List V) :
    walkInvTrustLen G (u :: v :: rest) = invTrustLen G u v + walkInvTrustLen G (v :: rest) := by
  simp [walkInvTrustLen]

/-- Shortest inverse-trust walk distance from `s` to `v` in `ℝ≥0∞` (`0` at `v = s`, `⊤` if
unreachable) [FriedmanResnickSami2007, §27.5, p. 690]. -/
@[expose] noncomputable def pathrankDist {V : Type*} (G : TrustGraph V) (s v : V) : ℝ≥0∞ :=
  ⨅ (p : List V) (_ : p.head? = some s ∧ p.getLast? = some v), walkInvTrustLen G p

/-- **Pathrank reputation** `((1 + pathrankDist G s v)⁻¹).toReal ∈ [0, 1]` from trusted seed `s` to
`v` (`1` at `v = s`, `0` when `v` is unreachable, and strictly antitone in shortest inverse-trust
distance `pathrankDist G s v`) [FriedmanResnickSami2007, §27.5, pp. 690, 692;
ChengFriedman2005, §4.2, Theorem 5, p. 131]. -/
@[expose] noncomputable def pathrankRep {V : Type*} (G : TrustGraph V) (s v : V) : ℝ :=
  ((1 + pathrankDist G s v)⁻¹).toReal

@[simp]
theorem pathrankDist_self {V : Type*} (G : TrustGraph V) (s : V) : pathrankDist G s s = 0 := by
  refine le_antisymm ?_ zero_le
  exact iInf₂_le [s] ⟨rfl, rfl⟩ |>.trans_eq (walkInvTrustLen_singleton G s)

@[simp]
theorem pathrankRep_self {V : Type*} (G : TrustGraph V) (s : V) : pathrankRep G s s = 1 := by
  simp [pathrankRep]

private theorem inv_one_add_strictAnti : StrictAnti fun d : ℝ≥0∞ => ((1 + d)⁻¹).toReal := by
  intro d₁ d₂ hlt
  have h1top : (1 + d₁)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le le_self_add).ne'
  by_cases hd2 : d₂ = ⊤
  · subst hd2
    have hinv_pos : (0 : ℝ≥0∞) < (1 + d₁)⁻¹ :=
      ENNReal.inv_pos.mpr (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hlt.ne_top⟩)
    simpa using ENNReal.toReal_pos hinv_pos.ne' h1top
  · exact (ENNReal.toReal_lt_toReal
      (ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le le_self_add).ne') h1top).mpr
      (ENNReal.inv_lt_inv.mpr (ENNReal.add_lt_add_left ENNReal.one_ne_top hlt))

theorem pathrankRep_lt_iff {V W : Type*} (G₁ : TrustGraph V) (G₂ : TrustGraph W)
    (s₁ v₁ : V) (s₂ v₂ : W) :
    pathrankRep G₁ s₁ v₁ < pathrankRep G₂ s₂ v₂ ↔
      pathrankDist G₂ s₂ v₂ < pathrankDist G₁ s₁ v₁ :=
  inv_one_add_strictAnti.lt_iff_gt

theorem pathrankRep_le_iff {V W : Type*} (G₁ : TrustGraph V) (G₂ : TrustGraph W)
    (s₁ v₁ : V) (s₂ v₂ : W) :
    pathrankRep G₁ s₁ v₁ ≤ pathrankRep G₂ s₂ v₂ ↔
      pathrankDist G₂ s₂ v₂ ≤ pathrankDist G₁ s₁ v₁ :=
  inv_one_add_strictAnti.le_iff_ge

private theorem pathrankDist_le_invTrustLen_add {V : Type*} (G : TrustGraph V) (x y z : V) :
    pathrankDist G x z ≤ invTrustLen G x y + pathrankDist G y z := by
  unfold pathrankDist
  rw [ENNReal.add_iInf]
  refine le_iInf fun q => ?_
  by_cases hq : q.head? = some y ∧ q.getLast? = some z
  · rw [iInf_pos hq]
    rcases q with _ | ⟨y', rest⟩
    · simp at hq
    · rcases hq with ⟨hy_eq, hlast⟩
      cases Option.some.inj hy_eq
      exact (iInf₂_le (x :: y :: rest) ⟨rfl, by simpa using hlast⟩).trans_eq
        (walkInvTrustLen_cons_cons G x y rest)
  · rw [iInf_neg hq, add_top]
    exact le_top

private theorem invTrustLen_anti {V₁ V₂ : Type*} {G₁ : TrustGraph V₁} {G₂ : TrustGraph V₂}
    {u₁ v₁ : V₁} {u₂ v₂ : V₂} (hle : G₁.weight u₁ v₁ ≤ G₂.weight u₂ v₂) :
    invTrustLen G₂ u₂ v₂ ≤ invTrustLen G₁ u₁ v₁ :=
  ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hle)

private noncomputable def minEdgeStep {V : Type*} [Fintype V] (G : TrustGraph V) : ℝ≥0∞ :=
  (ENNReal.ofReal ((∑ x : V, ∑ y : V, G.weight x y) + 1))⁻¹

private theorem minEdgeStep_pos {V : Type*} [Fintype V] (G : TrustGraph V) :
    0 < minEdgeStep G :=
  ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

private theorem minEdgeStep_le_invTrustLen {V : Type*} [Fintype V] (G : TrustGraph V) (x y : V) :
    minEdgeStep G ≤ invTrustLen G x y := by
  rw [minEdgeStep, invTrustLen, ENNReal.inv_le_inv]
  apply ENNReal.ofReal_le_ofReal
  have h1 : G.weight x y ≤ ∑ y' : V, G.weight x y' :=
    single_le_sum (fun y' _ => G.weight_nonneg x y') (mem_univ y)
  have h2 : ∑ y' : V, G.weight x y' ≤ ∑ x' : V, ∑ y' : V, G.weight x' y' :=
    single_le_sum (fun x' _ => sum_nonneg fun y' _ => G.weight_nonneg x' y') (mem_univ x)
  linarith

private theorem pathrankDist_le_of_walk {V : Type*} (G : TrustGraph V) {s v : V} {p : List V}
    (hp : p.head? = some s ∧ p.getLast? = some v) :
    pathrankDist G s v ≤ walkInvTrustLen G p := by
  rw [pathrankDist]
  exact iInf₂_le p hp

private theorem le_pathrankDist_iff {V : Type*} (G : TrustGraph V) {s v : V} {d : ℝ≥0∞} :
    d ≤ pathrankDist G s v ↔
      ∀ p : List V, (p.head? = some s ∧ p.getLast? = some v) → d ≤ walkInvTrustLen G p := by
  rw [pathrankDist]
  exact le_iInf₂_iff

private theorem exists_walk_lt_of_pathrankDist_lt {V : Type*} (G : TrustGraph V) {s v : V}
    {b : ℝ≥0∞} (hlt : pathrankDist G s v < b) :
    ∃ p : List V, (p.head? = some s ∧ p.getLast? = some v) ∧ walkInvTrustLen G p < b := by
  by_contra! hge
  exact hlt.not_ge ((le_pathrankDist_iff G).mpr hge)

private theorem pathrankDist_add_minEdgeStep_le_of_mem {V : Type*} [Fintype V] (G : TrustGraph V)
    {v w : V} (hvw : v ≠ w) :
    ∀ (p : List V) (x : V), p.head? = some x → p.getLast? = some w → v ∈ p →
      pathrankDist G x v + minEdgeStep G ≤ walkInvTrustLen G p
  | [], _, hh, _, _ => by simp at hh
  | [z], _, _, hl, hv => absurd ((List.mem_singleton.mp hv).trans (Option.some.inj hl)) hvw
  | z :: y :: rest', x, hh, hl, hv => by
      cases Option.some.inj hh
      rw [walkInvTrustLen_cons_cons]
      by_cases hzv : z = v
      · subst hzv
        rw [pathrankDist_self, zero_add]
        exact (minEdgeStep_le_invTrustLen G z y).trans le_self_add
      · calc pathrankDist G z v + minEdgeStep G
            ≤ (invTrustLen G z y + pathrankDist G y v) + minEdgeStep G :=
              add_le_add (pathrankDist_le_invTrustLen_add G z y v) le_rfl
          _ = invTrustLen G z y + (pathrankDist G y v + minEdgeStep G) := add_assoc _ _ _
          _ ≤ invTrustLen G z y + walkInvTrustLen G (y :: rest') := add_le_add le_rfl <|
              pathrankDist_add_minEdgeStep_le_of_mem G hvw (y :: rest') y rfl hl
                ((List.mem_cons.mp hv).resolve_left (Ne.symm hzv))

private theorem pathrankDist_le_walk_sybil {V : Type} [Fintype V] [DecidableEq V]
    {G : TrustGraph V} {v : V} (S : SybilStrategy G v) {u : S.Vertex} (hu : u ∈ S.sybils) :
    ∀ (p : List S.Vertex) (x : V) (hx : x ≠ v),
      p.head? = some (S.honest x hx) → p.getLast? = some u →
        pathrankDist G x v ≤ walkInvTrustLen S.graph p
  | [], _, _, hh, _ => by simp at hh
  | [z], x, hx, hh, hl =>
      absurd ((Option.some.inj hh).symm.trans (Option.some.inj hl) ▸ hu)
        (S.honest_notMem_sybils x hx)
  | z :: y :: rest', x, hx, hh, hl => by
      rw [walkInvTrustLen_cons_cons, Option.some.inj hh]
      by_cases hy : y ∈ S.sybils
      · have hle_w : S.graph.weight (S.honest x hx) y ≤ G.weight x v := by
          rw [← S.sum_weight_honest_sybils hx]
          exact single_le_sum (fun u' _ => S.graph.weight_nonneg _ u') hy
        exact ((pathrankDist_le_of_walk G (p := [x, v]) ⟨rfl, rfl⟩).trans_eq
          (by simp [walkInvTrustLen])).trans ((invTrustLen_anti hle_w).trans le_self_add)
      · have hyv : S.collapse y ≠ v := mt S.mem_sybils.mpr hy
        have hy_eq : y = S.honest (S.collapse y) hyv := (S.honestEmbed_collapse y hyv).symm
        calc pathrankDist G x v
            ≤ invTrustLen G x (S.collapse y) + pathrankDist G (S.collapse y) v :=
              pathrankDist_le_invTrustLen_add G x _ v
          _ = invTrustLen S.graph (S.honest x hx) y + pathrankDist G (S.collapse y) v := by
              rw [hy_eq]
              simp [invTrustLen, S.weight_honest_honest hx hyv]
          _ ≤ invTrustLen S.graph (S.honest x hx) y + walkInvTrustLen S.graph (y :: rest') :=
              add_le_add le_rfl
                (pathrankDist_le_walk_sybil S hu (y :: rest') _ hyv (congrArg some hy_eq) hl)

private theorem liftWalk_sybil {V : Type} [Fintype V] [DecidableEq V] {G : TrustGraph V} {v : V}
    (S : SybilStrategy G v) :
    ∀ (p : List V) (x w : V) (hx : x ≠ v) (hw : w ≠ v),
      p.head? = some x → p.getLast? = some w → v ∉ p →
        pathrankDist S.graph (S.honest x hx) (S.honest w hw) ≤ walkInvTrustLen G p
  | [], _, _, _, _, hh, _, _ => by simp at hh
  | [z], x, w, hx, hw, hh, hl, _ => by simp [← Option.some.inj hh, ← Option.some.inj hl]
  | z :: y :: rest', x, w, hx, hw, hh, hl, hnot => by
      cases Option.some.inj hh
      have hyv : y ≠ v := fun h => hnot (List.mem_cons_of_mem z (h ▸ List.mem_cons_self))
      rw [walkInvTrustLen_cons_cons]
      calc pathrankDist S.graph (S.honest z hx) (S.honest w hw)
          ≤ invTrustLen S.graph (S.honest z hx) (S.honest y hyv) +
              pathrankDist S.graph (S.honest y hyv) (S.honest w hw) :=
            pathrankDist_le_invTrustLen_add S.graph _ _ _
        _ = invTrustLen G z y + pathrankDist S.graph (S.honest y hyv) (S.honest w hw) := by
            simp [invTrustLen, S.weight_honest_honest hx hyv]
        _ ≤ invTrustLen G z y + walkInvTrustLen G (y :: rest') :=
            add_le_add le_rfl (liftWalk_sybil S (y :: rest') y w hyv hw rfl hl
              fun hm => hnot (List.mem_cons_of_mem z hm))

/-- **Theorem 27.9 (value-sybilproofness)** ([FriedmanResnickSami2007, p. 692];
[ChengFriedman2005, Theorem 4, p. 131]): `pathrankRep` is **value-sybilproof**. -/
theorem isValueSybilproof_pathrankRep :
    SeededRepFn.IsValueSybilproof fun G => pathrankRep G := by
  intro V _ _ G s v hsv S u hu
  rw [pathrankRep_le_iff, le_pathrankDist_iff]
  exact fun p hp => pathrankDist_le_walk_sybil S hu p s hsv.symm hp.1 hp.2

/-- **Theorem 27.9 (rank-sybilproofness)** ([FriedmanResnickSami2007, p. 692];
[ChengFriedman2005, Theorem 5, p. 131]): `pathrankRep` is **rank-sybilproof**. -/
theorem isRankSybilproof_pathrankRep :
    SeededRepFn.IsRankSybilproof fun G => pathrankRep G := by
  intro V _ _ G s v hsv S u hu w hw hlt
  rw [pathrankRep_lt_iff] at hlt ⊢
  obtain ⟨p, hp_valid, hp⟩ := exists_walk_lt_of_pathrankDist_lt G hlt
  have hv_not_mem : v ∉ p := by
    intro hmem
    have hle := pathrankDist_add_minEdgeStep_le_of_mem G hw.symm p s hp_valid.1 hp_valid.2 hmem
    exact hp.not_ge (le_self_add.trans hle)
  have hlift := liftWalk_sybil S p s w hsv.symm hw hp_valid.1 hp_valid.2 hv_not_mem
  have hval : pathrankDist G s v ≤ pathrankDist S.graph (S.honest s hsv.symm) u :=
    (pathrankRep_le_iff S.graph G (S.honest s hsv.symm) u s v).mp
      (isValueSybilproof_pathrankRep G s v hsv S u hu)
  exact (hlift.trans_lt hp).trans_le hval

private theorem pathrankDist_le_of_out_congr {V : Type*} {G G' : TrustGraph V}
    {v : V} (hout : ∀ x, x ≠ v → ∀ y, G'.weight x y = G.weight x y) :
    ∀ (p : List V) (x : V), p.head? = some x → p.getLast? = some v →
      pathrankDist G x v ≤ walkInvTrustLen G' p
  | [], _, hh, _ => by simp at hh
  | [z], x, hh, hl => by simp [← Option.some.inj hh, ← Option.some.inj hl]
  | z :: y :: rest', x, hh, hl => by
      cases Option.some.inj hh
      by_cases hzv : z = v
      · subst hzv
        simp
      · rw [walkInvTrustLen_cons_cons]
        calc pathrankDist G z v
            ≤ invTrustLen G z y + pathrankDist G y v := pathrankDist_le_invTrustLen_add G z y v
          _ = invTrustLen G' z y + pathrankDist G y v := by simp [invTrustLen, hout z hzv y]
          _ ≤ invTrustLen G' z y + walkInvTrustLen G' (y :: rest') :=
              add_le_add le_rfl (pathrankDist_le_of_out_congr hout (y :: rest') y rfl hl)

private theorem pathrankDist_eq_of_out_congr {V : Type*} {G G' : TrustGraph V}
    {s v : V} (hout : ∀ x, x ≠ v → ∀ y, G'.weight x y = G.weight x y) :
    pathrankDist G' s v = pathrankDist G s v :=
  le_antisymm
    ((le_pathrankDist_iff G).mpr fun p hp =>
      pathrankDist_le_of_out_congr (fun x hx y => (hout x hx y).symm) p s hp.1 hp.2)
    ((le_pathrankDist_iff G').mpr fun p hp =>
      pathrankDist_le_of_out_congr hout p s hp.1 hp.2)

private theorem walkInvTrustLen_congr_of_notMem {V : Type*} {G G' : TrustGraph V} {v : V}
    (hcongr : ∀ x y, x ≠ v → y ≠ v → G'.weight x y = G.weight x y) :
    ∀ (p : List V), v ∉ p → walkInvTrustLen G' p = walkInvTrustLen G p
  | [], _ | [_], _ => rfl
  | z :: y :: rest', hnot => by
      have hzv : z ≠ v := fun h => hnot (h ▸ List.mem_cons_self)
      have hyv : y ≠ v := fun h => hnot (List.mem_cons_of_mem z (h ▸ List.mem_cons_self))
      rw [walkInvTrustLen_cons_cons, walkInvTrustLen_cons_cons,
        walkInvTrustLen_congr_of_notMem hcongr (y :: rest') fun hm =>
          hnot (List.mem_cons_of_mem z hm)]
      simp [invTrustLen, hcongr z y hzv hyv]

/-- **Section 27.5.1 (rank-strategyproofness of Pathrank)**
([FriedmanResnickSami2007, §27.5.1, p. 690]): `pathrankRep` is **rank-strategyproof**. -/
theorem isRankStrategyproof_pathrankRep :
    SeededRepFn.IsRankStrategyproof fun G => pathrankRep G := by
  intro V _ _ G G' s v _ hout w
  have heq_v : pathrankDist G' s v = pathrankDist G s v := pathrankDist_eq_of_out_congr hout
  have hw_congr := walkInvTrustLen_congr_of_notMem (G := G) (G' := G') (v := v)
    fun x y hxv _ => hout x hxv y
  have hstrict : pathrankDist G s w < pathrankDist G s v →
      pathrankDist G' s w < pathrankDist G' s v := fun hlt => by
    obtain ⟨p, hp_valid, hp⟩ := exists_walk_lt_of_pathrankDist_lt G hlt
    have hv_not : v ∉ p := fun hmem => hp.not_ge (le_self_add.trans
      (pathrankDist_add_minEdgeStep_le_of_mem G (fun h => hlt.ne (by rw [h])) p s
        hp_valid.1 hp_valid.2 hmem))
    exact ((pathrankDist_le_of_walk G' hp_valid).trans_eq (hw_congr p hv_not)
      |>.trans_lt hp).trans_eq heq_v.symm
  refine ⟨fun hlt => (pathrankRep_lt_iff ..).mpr (hstrict ((pathrankRep_lt_iff ..).mp hlt)),
    fun hle => ?_⟩
  rw [pathrankRep_le_iff] at hle ⊢
  rcases eq_or_lt_of_le hle with hd_eq | hd_lt
  · by_cases hwv : w = v
    · subst hwv; exact le_rfl
    · by_cases htop : pathrankDist G s v = ⊤
      · simp [heq_v, htop]
      · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        let δ : ℝ≥0∞ := min (ε : ℝ≥0∞) (minEdgeStep G)
        have hδ_pos : 0 < δ := lt_min (ENNReal.coe_pos.mpr hε) (minEdgeStep_pos G)
        have hlt_δ : pathrankDist G s w < pathrankDist G s v + δ :=
          hd_eq.trans_lt (ENNReal.lt_add_right htop hδ_pos.ne')
        obtain ⟨p, hp_valid, hp⟩ := exists_walk_lt_of_pathrankDist_lt G hlt_δ
        have hv_not : v ∉ p := fun hmem =>
          (hp.trans_le (add_le_add le_rfl (min_le_right _ _))).not_ge
            (pathrankDist_add_minEdgeStep_le_of_mem G (Ne.symm hwv) p s
              hp_valid.1 hp_valid.2 hmem)
        calc pathrankDist G' s w
            ≤ walkInvTrustLen G' p := pathrankDist_le_of_walk G' hp_valid
          _ = walkInvTrustLen G p := hw_congr p hv_not
          _ ≤ pathrankDist G s v + δ := hp.le
          _ ≤ pathrankDist G' s v + ε := heq_v ▸ add_le_add le_rfl (min_le_left _ _)
  · exact (hstrict hd_lt).le

private theorem walkInvTrustLen_anti_pointwise {V : Type*} {G G' : TrustGraph V}
    (hle : ∀ x y, G.weight x y ≤ G'.weight x y) :
    ∀ p : List V, walkInvTrustLen G' p ≤ walkInvTrustLen G p
  | [] | [_] => le_rfl
  | z :: y :: rest' => by
      simp only [walkInvTrustLen_cons_cons]
      exact add_le_add (invTrustLen_anti (hle z y))
        (walkInvTrustLen_anti_pointwise hle (y :: rest'))

/-- **Section 27.5 (monotonicity of Pathrank)** ([FriedmanResnickSami2007, §27.5, pp. 690, 692]):
`pathrankRep` is **monotonic** in incoming edge trust weights. -/
theorem isMonotonic_pathrankRep : SeededRepFn.IsMonotonic fun G => pathrankRep G := by
  intro V _ _ G G' s u v _ huv hother w
  have hle_all : ∀ x y, G.weight x y ≤ G'.weight x y := fun x y => by
    by_cases hxy : (x, y) = (u, v)
    · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩; exact huv
    · exact (hother x y hxy).ge
  have hdv : pathrankDist G' s v ≤ pathrankDist G s v :=
    (le_pathrankDist_iff G).mpr fun p hp =>
      (pathrankDist_le_of_walk G' hp).trans (walkInvTrustLen_anti_pointwise hle_all p)
  have hmin_w : ∀ hwv : w ≠ v,
      min (pathrankDist G s w) (pathrankDist G' s v + minEdgeStep G') ≤ pathrankDist G' s w :=
    fun hwv => (le_pathrankDist_iff G').mpr fun p hp => by
      by_cases hmem : v ∈ p
      · exact (min_le_right _ _).trans
          (pathrankDist_add_minEdgeStep_le_of_mem G' hwv.symm p s hp.1 hp.2 hmem)
      · exact (min_le_left _ _).trans ((pathrankDist_le_of_walk G hp).trans_eq
          (walkInvTrustLen_congr_of_notMem
            (fun x y _ hyv => hother x y fun h => hyv (Prod.mk.inj h).2) p hmem).symm)
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · rw [pathrankRep_lt_iff] at hlt ⊢
    exact (lt_min (hdv.trans_lt hlt)
      (ENNReal.lt_add_right (hdv.trans_lt hlt).ne_top (minEdgeStep_pos G').ne')).trans_le
      (hmin_w fun h => hlt.ne (h ▸ rfl))
  · rw [pathrankRep_le_iff] at hle ⊢
    by_cases hwv : w = v
    · subst hwv; exact le_rfl
    · exact (le_min (hdv.trans hle) le_self_add).trans (hmin_w hwv)

end Cslib.GameTheory.Reputation
