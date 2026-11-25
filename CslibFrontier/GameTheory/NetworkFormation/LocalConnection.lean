/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The local connection game

In the **local connection game** (the unilateral network creation game of Fabrikant, Luthra,
Maneva, Papadimitriou and Shenker [FabrikantLuthraManevaPapadimitriouShenker2003];
[TardosWexler2007], Section 19.2, pp. 489–494), the players are the vertices of a finite set `V`,
and a strategy `s u : LinkSet V u` of player `u` is a set of incident undirected edges (`neighbors`
with `u ∉ neighbors`) that `u` builds and pays `α ≥ 0` each to maintain. Together the strategies
form the undirected simple graph `formedGraph s : SimpleGraph V` in which `v` and `w` are adjacent
whenever `w ∈ s v` or `v ∈ s w`.

Player `u` minimizes the sum of her edge-construction cost and shortest-path distances to all
vertices in `formedGraph s`. Disconnected pairs incur infinite distance cost ([TardosWexler2007],
Section 19.2.1, p. 490): we value individual and social costs in `ℝ≥0∞` using `SimpleGraph.edist`
(`playerECost`, `socialECost`, `networkECost`) so that unreachable pairs contribute `⊤` rather than
Mathlib's `0` convention on `SimpleGraph.dist`, and connect connected profiles to real-valued costs
(`playerCost`, `socialCost`, `networkCost`). Every ordered pair `(u, v)` with `u ≠ v` contributes
`dist(u, v)` once to `u` and once to `v` ([TardosWexler2007], Section 19.2.1, p. 490), placing the
social-optimality transition between cliques and stars at `α = 2` and the unilateral stability
transition at `α = 1`.

In Theorem 19.5 ([TardosWexler2007], p. 492), writing `dist(u, v) ≥ 2k` bounds `k ≤ √α` from the
`k²` distance savings along the second half of a shortest `u`–`v` path; for odd diameter
`d = 2k + 1`, the exact savings `0 + 2 + ⋯ + 2k = k(k + 1) = (d² - 1)/4` yield the sharp bound
`d ≤ √(4α + 1) ≤ 2√α + 1` of [FabrikantLuthraManevaPapadimitriouShenker2003] (attained
with equality on `P₄` at `α = 2`, where `d = 3 > 2√2`).

## Main definitions

* `Cslib.GameTheory.LocalConnection.LinkSet`, `Cslib.GameTheory.LocalConnection.Profile`: a
  player's loopless incident link set and a pure strategy profile `∀ u : V, LinkSet V u`.
* `Cslib.GameTheory.LocalConnection.formedGraph`: the undirected `SimpleGraph V` formed by a
  strategy profile.
* `Cslib.GameTheory.LocalConnection.NoDoubleEdges`: no undirected edge is paid for by both
  endpoints.
* `Cslib.GameTheory.LocalConnection.playerECost`, `Cslib.GameTheory.LocalConnection.socialECost`,
  `Cslib.GameTheory.LocalConnection.networkECost`: `ℝ≥0∞`-valued individual, profile-social, and
  graph-social costs (infinite when disconnected).
* `Cslib.GameTheory.LocalConnection.playerCost`, `Cslib.GameTheory.LocalConnection.socialCost`,
  `Cslib.GameTheory.LocalConnection.networkCost`: real-valued costs on connected networks.
* `Cslib.GameTheory.LocalConnection.IsPureNash`, `Cslib.GameTheory.LocalConnection.IsStableNetwork`,
  `Cslib.GameTheory.LocalConnection.IsSocialOptimum`,
  `Cslib.GameTheory.LocalConnection.IsOptimalNetwork`: Nash stability and social optimality for
  strategy profiles and networks.
* `Cslib.GameTheory.LocalConnection.orientProfile`,
  `Cslib.GameTheory.LocalConnection.starCenterProfile`,
  `Cslib.GameTheory.LocalConnection.starLeafProfile`,
  `Cslib.GameTheory.LocalConnection.completeProfile`: single-sponsor edge orientations and
  canonical star/complete profiles.

## Main results

* `Cslib.GameTheory.LocalConnection.IsPureNash.connected`,
  `Cslib.GameTheory.LocalConnection.IsPureNash.noDoubleEdges`,
  `Cslib.GameTheory.LocalConnection.IsPureNash.socialECost_eq_networkECost`: every pure Nash
  equilibrium on a nonempty vertex set forms a connected graph, has no double-bought edges when
  `α > 0`, and has profile social cost equal to `networkECost` when `α ≥ 0`.
* `Cslib.GameTheory.LocalConnection.isOptimalNetwork_starGraph`,
  `Cslib.GameTheory.LocalConnection.isOptimalNetwork_top`,
  `Cslib.GameTheory.LocalConnection.NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_starGraph`,
  `Cslib.GameTheory.LocalConnection.NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_top`
  ([TardosWexler2007], Lemma 19.1): stars are socially optimal for `α ≥ 2`, and the complete graph
  is socially optimal for `0 ≤ α ≤ 2`.
* `Cslib.GameTheory.LocalConnection.NoDoubleEdges.isPureNash_of_formedGraph_eq_starGraph`,
  `Cslib.GameTheory.LocalConnection.isStableNetwork_starGraph`,
  `Cslib.GameTheory.LocalConnection.NoDoubleEdges.isPureNash_of_formedGraph_eq_top`,
  `Cslib.GameTheory.LocalConnection.isStableNetwork_top`,
  `Cslib.GameTheory.LocalConnection.isStableNetwork_top_iff`
  ([TardosWexler2007], Lemma 19.2): stars are pure Nash equilibria for `α ≥ 1`, and the complete
  graph is a pure Nash equilibrium for `0 ≤ α ≤ 1` (and iff `α ≤ 1` when `|V| ≥ 3`).
* `Cslib.GameTheory.LocalConnection.exists_isPureNash_isSocialOptimum_of_le_one`,
  `Cslib.GameTheory.LocalConnection.exists_isPureNash_isSocialOptimum_of_two_le`,
  `Cslib.GameTheory.LocalConnection.exists_isPureNash_socialECost_le_four_thirds`,
  `Cslib.GameTheory.LocalConnection.socialCost_starCenterProfile_lt_four_thirds_mul`,
  `Cslib.GameTheory.LocalConnection.networkCost_one_starGraph_div_top`
  ([TardosWexler2007], Theorem 19.3): the price of stability is `1` for `0 ≤ α ≤ 1` and `α ≥ 2`,
  and at most `4/3` (strictly `< 4/3` for `|V| ≥ 2`) for `1 ≤ α ≤ 2`, with star-to-clique ratio
  `(4n² - 6n + 2)/(3n² - 3n) = 4/3 - 2/(3n)` at `α = 1`.
* `Cslib.GameTheory.LocalConnection.IsPureNash.socialECost_le_three_mul_diam_mul`,
  `Cslib.GameTheory.LocalConnection.IsPureNash.socialCost_le_three_mul_diam_mul`
  ([TardosWexler2007], Lemma 19.4): a pure Nash equilibrium of diameter `d` has social cost at
  most `3d` times optimal.
* `Cslib.GameTheory.LocalConnection.IsPureNash.diam_le_sqrt_four_mul_add_one`,
  `Cslib.GameTheory.LocalConnection.IsPureNash.diam_le_two_mul_sqrt_add_one`,
  `Cslib.GameTheory.LocalConnection.IsPureNash.socialECost_le_six_mul_sqrt_add_three_mul`
  ([FabrikantLuthraManevaPapadimitriouShenker2003]; [TardosWexler2007], Theorem 19.5):
  any pure Nash equilibrium has diameter at most `√(4α + 1) ≤ 2√α + 1` and social cost at most
  `6√α + 3` times optimal (`O(√α)`).
* `Cslib.GameTheory.LocalConnection.IsPureNash.diam_le_four_mul_div_sqrt_card_add_nine`,
  `IsPureNash.socialECost_le_twelve_mul_div_sqrt_card_add_twenty_seven_mul`
  ([AlbersEiltsEvenDarMansourRoditty2006]; [TardosWexler2007], Theorem 19.6): any pure Nash
  equilibrium on `n` players has diameter at most `4α / √n + 9` and social cost at most
  `(12α / √n + 27)` times optimal (`O(1 + α / √n)`).

## References

* [AlbersEiltsEvenDarMansourRoditty2006]
* [FabrikantLuthraManevaPapadimitriouShenker2003]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory.LocalConnection

open Finset SimpleGraph
open scoped BigOperators ENNReal

/-! ### Link strategies, profiles, and formed graphs -/

/-- A pure strategy for player `u` in the local connection game on vertex set `V`: a finite set
`neighbors` of other vertices to which `u` builds undirected incident links, excluding self-loops
([TardosWexler2007], Section 19.2.1, p. 490). -/
@[ext]
structure LinkSet (V : Type*) (u : V) where
  /-- The target vertices of the undirected edges paid for by player `u`. -/
  neighbors : Finset V
  /-- Players cannot build self-loops. -/
  notMem_self : u ∉ neighbors
  deriving DecidableEq

namespace LinkSet

variable {V : Type*} {u v : V}

instance : Membership V (LinkSet V u) :=
  ⟨fun a w => w ∈ a.neighbors⟩

@[simp]
theorem mem_iff {a : LinkSet V u} {w : V} : w ∈ a ↔ w ∈ a.neighbors :=
  Iff.rfl

instance [DecidableEq V] (a : LinkSet V u) : DecidablePred (· ∈ a) :=
  fun w => inferInstanceAs (Decidable (w ∈ a.neighbors))

theorem ne_of_mem {a : LinkSet V u} (h : v ∈ a) : v ≠ u :=
  fun hvu => a.notMem_self (hvu ▸ h)

instance : EmptyCollection (LinkSet V u) :=
  ⟨⟨∅, notMem_empty u⟩⟩

@[simp]
theorem neighbors_empty : (∅ : LinkSet V u).neighbors = ∅ :=
  rfl

theorem notMem_empty (w : V) : w ∉ (∅ : LinkSet V u) :=
  Finset.notMem_empty w

/-- Build a `LinkSet V u` from an arbitrary `s : Finset V` by erasing `u`. -/
def ofFinset [DecidableEq V] (u : V) (s : Finset V) : LinkSet V u where
  neighbors := s.erase u
  notMem_self := notMem_erase u s

@[simp]
theorem neighbors_ofFinset [DecidableEq V] (u : V) (s : Finset V) :
    (ofFinset u s).neighbors = s.erase u := by
  unfold ofFinset; rfl

theorem mem_ofFinset [DecidableEq V] {s : Finset V} {w : V} :
    w ∈ ofFinset u s ↔ w ≠ u ∧ w ∈ s := by
  rw [mem_iff, neighbors_ofFinset, mem_erase]

/-- The strategy in which player `u` builds links to every other vertex in `V`. -/
def univ [Fintype V] [DecidableEq V] (u : V) : LinkSet V u :=
  ofFinset u Finset.univ

@[simp]
theorem neighbors_univ [Fintype V] [DecidableEq V] (u : V) :
    (univ u).neighbors = Finset.univ.erase u := by
  unfold univ; exact neighbors_ofFinset u Finset.univ

theorem mem_univ [Fintype V] [DecidableEq V] {w : V} :
    w ∈ univ u ↔ w ≠ u := by
  rw [mem_iff, neighbors_univ, mem_erase]
  simp only [Finset.mem_univ, and_true]

/-- Remove vertex `w` from player `u`'s link set. -/
def erase [DecidableEq V] (a : LinkSet V u) (w : V) : LinkSet V u where
  neighbors := a.neighbors.erase w
  notMem_self := fun h => a.notMem_self (mem_of_mem_erase h)

@[simp]
theorem neighbors_erase [DecidableEq V] (a : LinkSet V u) (w : V) :
    (a.erase w).neighbors = a.neighbors.erase w := by
  unfold erase; rfl

theorem mem_erase_iff [DecidableEq V] {a : LinkSet V u} {w x : V} :
    x ∈ a.erase w ↔ x ≠ w ∧ x ∈ a := by
  rw [mem_iff, neighbors_erase, Finset.mem_erase, mem_iff]

instance [Fintype V] [DecidableEq V] (u : V) : Fintype (LinkSet V u) :=
  Fintype.ofEquiv { s : Finset V // u ∉ s }
    { toFun := fun s => ⟨s.1, s.2⟩
      invFun := fun a => ⟨a.neighbors, a.notMem_self⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

end LinkSet

/-- A pure strategy profile assigning a `LinkSet V u` to each player `u : V`. -/
abbrev Profile (V : Type*) := ∀ u : V, LinkSet V u

/-- The undirected simple graph formed by strategy profile `s`: an edge connects `v` and `w`
whenever `v` builds a link to `w` or `w` builds a link to `v` ([TardosWexler2007], Section 19.2.1,
p. 490). -/
def formedGraph {V : Type*} (s : Profile V) : SimpleGraph V where
  Adj v w := w ∈ s v ∨ v ∈ s w
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => h.elim (s v).notMem_self (s v).notMem_self⟩

@[simp]
theorem formedGraph_adj {V : Type*} {s : Profile V} {v w : V} :
    (formedGraph s).Adj v w ↔ w ∈ s v ∨ v ∈ s w := by
  unfold formedGraph; rfl

instance {V : Type*} [DecidableEq V] (s : Profile V) : DecidableRel (formedGraph s).Adj :=
  fun v w => decidable_of_iff' (w ∈ s v ∨ v ∈ s w) formedGraph_adj

@[simp]
theorem formedGraph_empty {V : Type*} : formedGraph (fun _ : V => (∅ : LinkSet V _)) = ⊥ := by
  ext v w
  simp only [formedGraph_adj, LinkSet.notMem_empty, or_self, bot_adj]

/-- A profile has **no double-bought edges** if no pair of players both pay for the undirected edge
between them. -/
@[expose] def NoDoubleEdges {V : Type*} (s : Profile V) : Prop :=
  ∀ ⦃u v : V⦄, v ∈ s u → u ∉ s v

/-! ### Individual, profile-social, and network-social costs -/

theorem ncard_edgeSet_eq_card_edgeFinset {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

private theorem two_mul_choose_two : ∀ n : ℕ, 2 * (n.choose 2 : ℝ) = (n : ℝ) * (n - 1 : ℕ)
  | 0 => by norm_num
  | 1 => by norm_num
  | m + 2 => by
    have ih := two_mul_choose_two (m + 1)
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    simp only [Nat.add_sub_cancel] at ih ⊢
    push_cast at ih ⊢
    linarith

section Costs

variable {V : Type*} [Fintype V]

/-- Player `u`'s extended cost under edge price `α` and strategy profile `s` in `ℝ≥0∞`:
`ENNReal.ofReal α * #(s u).neighbors + ∑ v, (formedGraph s).edist u v`. Unreachable pairs have
`edist = ⊤`, giving disconnected players cost `⊤` ([TardosWexler2007], Section 19.2.1, p. 490). -/
noncomputable def playerECost (α : ℝ) (s : Profile V) (u : V) : ℝ≥0∞ :=
  ENNReal.ofReal α * ((s u).neighbors.card : ℝ≥0∞) +
    ∑ v : V, ((formedGraph s).edist u v : ℝ≥0∞)

/-- The extended social cost `∑ u, playerECost α s u` of strategy profile `s`. -/
noncomputable def socialECost (α : ℝ) (s : Profile V) : ℝ≥0∞ :=
  ∑ u : V, playerECost α s u

/-- The extended social cost `SC(G) = α |E| + ∑_{u, v} edist_G(u, v)` of a network `G`
([TardosWexler2007], Section 19.2.1, p. 490). -/
noncomputable def networkECost (α : ℝ) (G : SimpleGraph V) : ℝ≥0∞ :=
  ENNReal.ofReal α * (G.edgeSet.ncard : ℝ≥0∞) + ∑ u : V, ∑ v : V, (G.edist u v : ℝ≥0∞)

/-- Player `u`'s real-valued cost `α * #(s u).neighbors + ∑ v, (formedGraph s).dist u v`, which
agrees with `playerECost` when `formedGraph s` is connected and `0 ≤ α`. -/
noncomputable def playerCost (α : ℝ) (s : Profile V) (u : V) : ℝ :=
  α * ((s u).neighbors.card : ℝ) + ∑ v : V, ((formedGraph s).dist u v : ℝ)

/-- Real-valued social cost `∑ u, playerCost α s u` of a profile `s`. -/
noncomputable def socialCost (α : ℝ) (s : Profile V) : ℝ :=
  ∑ u : V, playerCost α s u

/-- Real-valued social cost `α * |E| + ∑_{u, v} dist_G(u, v)` of a network `G`. -/
noncomputable def networkCost (α : ℝ) (G : SimpleGraph V) : ℝ :=
  α * (G.edgeSet.ncard : ℝ) + ∑ u : V, ∑ v : V, (G.dist u v : ℝ)

@[simp]
theorem playerECost_def (α : ℝ) (s : Profile V) (u : V) :
    playerECost α s u =
      ENNReal.ofReal α * ((s u).neighbors.card : ℝ≥0∞) +
        ∑ v : V, ((formedGraph s).edist u v : ℝ≥0∞) := by
  unfold playerECost; rfl

@[simp]
theorem socialECost_def (α : ℝ) (s : Profile V) :
    socialECost α s = ∑ u : V, playerECost α s u := by
  unfold socialECost; rfl

@[simp]
theorem networkECost_def (α : ℝ) (G : SimpleGraph V) :
    networkECost α G =
      ENNReal.ofReal α * (G.edgeSet.ncard : ℝ≥0∞) + ∑ u : V, ∑ v : V, (G.edist u v : ℝ≥0∞) := by
  unfold networkECost; rfl

@[simp]
theorem playerCost_def (α : ℝ) (s : Profile V) (u : V) :
    playerCost α s u =
      α * ((s u).neighbors.card : ℝ) + ∑ v : V, ((formedGraph s).dist u v : ℝ) := by
  unfold playerCost; rfl

@[simp]
theorem socialCost_def (α : ℝ) (s : Profile V) :
    socialCost α s = ∑ u : V, playerCost α s u := by
  unfold socialCost; rfl

@[simp]
theorem networkCost_def (α : ℝ) (G : SimpleGraph V) :
    networkCost α G = α * (G.edgeSet.ncard : ℝ) + ∑ u : V, ∑ v : V, (G.dist u v : ℝ) := by
  unfold networkCost; rfl

/-- Player `u` has infinite extended cost if and only if some vertex is unreachable from `u`. -/
theorem playerECost_eq_top_iff {α : ℝ} {s : Profile V} {u : V} :
    playerECost α s u = ⊤ ↔ ∃ v : V, ¬ (formedGraph s).Reachable u v := by
  have hfin : ENNReal.ofReal α * ((s u).neighbors.card : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  simp only [playerECost_def, ENNReal.add_eq_top, hfin, false_or, ENNReal.sum_eq_top, mem_univ,
    true_and, ENat.toENNReal_eq_top]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, fun hr => edist_ne_top_iff_reachable.mpr hr hv⟩,
    fun ⟨v, hv⟩ => ⟨v, edist_eq_top_of_not_reachable hv⟩⟩

theorem playerECost_ne_top_iff {α : ℝ} {s : Profile V} {u : V} :
    playerECost α s u ≠ ⊤ ↔ ∀ v : V, (formedGraph s).Reachable u v := by
  rw [ne_eq, playerECost_eq_top_iff, not_exists_not]

/-- On a nonempty vertex set, `socialECost α s = ⊤` if and only if `formedGraph s` is
disconnected. -/
theorem socialECost_eq_top_iff [Nonempty V] {α : ℝ} {s : Profile V} :
    socialECost α s = ⊤ ↔ ¬ (formedGraph s).Connected := by
  rw [socialECost_def, ENNReal.sum_eq_top, SimpleGraph.connected_iff]
  simp only [mem_univ, true_and, playerECost_eq_top_iff, ‹Nonempty V›, and_true, Preconnected,
    not_forall]

theorem networkECost_eq_top_iff [Nonempty V] {α : ℝ} {G : SimpleGraph V} :
    networkECost α G = ⊤ ↔ ¬ G.Connected := by
  have hfin : ENNReal.ofReal α * (G.edgeSet.ncard : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  rw [SimpleGraph.connected_iff]
  simp only [networkECost_def, ENNReal.add_eq_top, hfin, false_or, ENNReal.sum_eq_top, mem_univ,
    true_and, ENat.toENNReal_eq_top, ‹Nonempty V›, and_true, Preconnected, not_forall]
  exact ⟨fun ⟨u, v, huv⟩ => ⟨u, v, fun hr => edist_ne_top_iff_reachable.mpr hr huv⟩,
    fun ⟨u, v, huv⟩ => ⟨u, v, edist_eq_top_of_not_reachable huv⟩⟩

theorem playerCost_nonneg {α : ℝ} (hα : 0 ≤ α) (s : Profile V) (u : V) :
    0 ≤ playerCost α s u := by
  rw [playerCost_def]; positivity

theorem socialCost_nonneg {α : ℝ} (hα : 0 ≤ α) (s : Profile V) :
    0 ≤ socialCost α s :=
  sum_nonneg fun u _ => playerCost_nonneg hα s u

theorem networkCost_nonneg {α : ℝ} (hα : 0 ≤ α) (G : SimpleGraph V) :
    0 ≤ networkCost α G := by
  rw [networkCost_def]; positivity

/-- When every vertex is reachable from `u` and `0 ≤ α`, `playerECost` equals `ENNReal.ofReal` of
`playerCost`. -/
theorem playerECost_eq_ofReal_of_forall_reachable {α : ℝ} (hα : 0 ≤ α) {s : Profile V} {u : V}
    (hr : ∀ v, (formedGraph s).Reachable u v) :
    playerECost α s u = ENNReal.ofReal (playerCost α s u) := by
  have hsum : (∑ v : V, ((formedGraph s).edist u v : ℝ≥0∞)) =
      ENNReal.ofReal (∑ v : V, ((formedGraph s).dist u v : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
    refine sum_congr rfl fun v _ => ?_
    rw [← (hr v).coe_dist_eq_edist, ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  rw [playerECost_def, playerCost_def, ENNReal.ofReal_add (by positivity)
    (sum_nonneg fun _ _ => Nat.cast_nonneg _),
    ENNReal.ofReal_mul hα, ENNReal.ofReal_natCast, hsum]

theorem playerECost_eq_ofReal_of_connected {α : ℝ} (hα : 0 ≤ α) {s : Profile V}
    (hc : (formedGraph s).Connected) (u : V) :
    playerECost α s u = ENNReal.ofReal (playerCost α s u) :=
  playerECost_eq_ofReal_of_forall_reachable hα (hc u)

theorem socialECost_eq_ofReal_of_connected {α : ℝ} (hα : 0 ≤ α) {s : Profile V}
    (hc : (formedGraph s).Connected) :
    socialECost α s = ENNReal.ofReal (socialCost α s) := by
  rw [socialECost_def, socialCost_def,
    ENNReal.ofReal_sum_of_nonneg fun u _ => playerCost_nonneg hα s u]
  exact sum_congr rfl fun u _ => playerECost_eq_ofReal_of_connected hα hc u

theorem networkECost_eq_ofReal_of_preconnected {α : ℝ} (hα : 0 ≤ α) {G : SimpleGraph V}
    (hc : G.Preconnected) :
    networkECost α G = ENNReal.ofReal (networkCost α G) := by
  have hsum : (∑ u : V, ∑ v : V, (G.edist u v : ℝ≥0∞)) =
      ENNReal.ofReal (∑ u : V, ∑ v : V, (G.dist u v : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sum_nonneg fun _ _ => Nat.cast_nonneg _]
    refine sum_congr rfl fun u _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Nat.cast_nonneg _]
    refine sum_congr rfl fun v _ => ?_
    rw [← (hc u v).coe_dist_eq_edist, ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  rw [networkECost_def, networkCost_def, ENNReal.ofReal_add (by positivity)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => Nat.cast_nonneg _),
    ENNReal.ofReal_mul hα, ENNReal.ofReal_natCast, hsum]

theorem networkECost_eq_ofReal_of_connected {α : ℝ} (hα : 0 ≤ α) {G : SimpleGraph V}
    (hc : G.Connected) :
    networkECost α G = ENNReal.ofReal (networkCost α G) :=
  networkECost_eq_ofReal_of_preconnected hα hc.preconnected

theorem socialECost_eq_add_sum_edist (α : ℝ) (s : Profile V) :
    socialECost α s =
      ENNReal.ofReal α * ((∑ u : V, (s u).neighbors.card : ℕ) : ℝ≥0∞) +
        ∑ u : V, ∑ v : V, ((formedGraph s).edist u v : ℝ≥0∞) := by
  simp only [socialECost_def, playerECost_def, sum_add_distrib, ← mul_sum, Nat.cast_sum]

theorem socialCost_eq_add_sum_dist (α : ℝ) (s : Profile V) :
    socialCost α s =
      α * ((∑ u : V, (s u).neighbors.card : ℕ) : ℝ) +
        ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) := by
  simp only [socialCost_def, playerCost_def, sum_add_distrib, ← mul_sum, Nat.cast_sum]

/-! ### Edge counting and single-sponsor orientations -/

/-- Every undirected edge of `formedGraph s` is sponsored by at least one endpoint, so
`(formedGraph s).edgeSet.ncard ≤ ∑ u, #(s u).neighbors`. -/
theorem ncard_edgeSet_formedGraph_le (s : Profile V) :
    (formedGraph s).edgeSet.ncard ≤ ∑ u : V, (s u).neighbors.card := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, ← card_sigma univ (fun u => (s u).neighbors)]
  have hsub : (formedGraph s).edgeFinset ⊆
      (univ.sigma fun u => (s u).neighbors).image (fun p => s(p.1, p.2)) := by
    intro e he
    rcases e with ⟨u, v⟩
    rw [mem_edgeFinset, mem_edgeSet, formedGraph_adj] at he
    rw [mem_image]
    exact he.elim
      (fun hv => ⟨⟨u, v⟩, mem_sigma.mpr ⟨mem_univ u, hv⟩, rfl⟩)
      (fun hu => ⟨⟨v, u⟩, mem_sigma.mpr ⟨mem_univ v, hu⟩, Sym2.eq_swap⟩)
  exact (card_le_card hsub).trans card_image_le

/-- Under `NoDoubleEdges s`, each edge of `formedGraph s` has a unique sponsor, so
`∑ u, #(s u).neighbors = (formedGraph s).edgeSet.ncard`. -/
theorem NoDoubleEdges.sum_card_neighbors_eq {s : Profile V} (h : NoDoubleEdges s) :
    (∑ u : V, (s u).neighbors.card) = (formedGraph s).edgeSet.ncard := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, ← card_sigma univ (fun u => (s u).neighbors)]
  refine Finset.card_bij (fun p _ => s(p.1, p.2))
    (fun p hp => mem_edgeFinset.mpr (formedGraph_adj.mpr (Or.inl (mem_sigma.mp hp).2)))
    (fun ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ heq => ?_) (fun e he => ?_)
  · rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact False.elim (h (mem_sigma.mp hp₁).2 (mem_sigma.mp hp₂).2)
  · rcases e with ⟨u, v⟩
    rw [mem_edgeFinset, mem_edgeSet, formedGraph_adj] at he
    exact he.elim
      (fun hv => ⟨⟨u, v⟩, mem_sigma.mpr ⟨mem_univ u, hv⟩, rfl⟩)
      (fun hu => ⟨⟨v, u⟩, mem_sigma.mpr ⟨mem_univ v, hu⟩, Sym2.eq_swap⟩)

theorem networkECost_formedGraph_le (α : ℝ) (s : Profile V) :
    networkECost α (formedGraph s) ≤ socialECost α s := by
  rw [socialECost_eq_add_sum_edist, networkECost_def]
  gcongr
  exact ncard_edgeSet_formedGraph_le s

theorem NoDoubleEdges.socialECost_eq_networkECost {s : Profile V} (h : NoDoubleEdges s) (α : ℝ) :
    socialECost α s = networkECost α (formedGraph s) := by
  rw [socialECost_eq_add_sum_edist, networkECost_def, h.sum_card_neighbors_eq]

theorem NoDoubleEdges.socialCost_eq_networkCost {s : Profile V} (h : NoDoubleEdges s) (α : ℝ) :
    socialCost α s = networkCost α (formedGraph s) := by
  rw [socialCost_eq_add_sum_dist, networkCost_def, h.sum_card_neighbors_eq]

/-- Canonical single-sponsor profile forming an arbitrary simple graph `G : SimpleGraph V`,
assigning each undirected edge to its smaller endpoint under `Fintype.equivFin V`. -/
noncomputable def orientProfile [DecidableEq V] (G : SimpleGraph V) : Profile V :=
  letI := Classical.decRel G.Adj
  let e := Fintype.equivFin V
  fun u => LinkSet.ofFinset u (univ.filter fun v => G.Adj u v ∧ e u < e v)

@[simp]
theorem formedGraph_orientProfile [DecidableEq V] (G : SimpleGraph V) :
    formedGraph (orientProfile G) = G := by
  ext u v
  simp only [formedGraph_adj, orientProfile, LinkSet.mem_ofFinset, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨_, hadj, _⟩ | ⟨_, hadj, _⟩)
    · exact hadj
    · exact hadj.symm
  · intro hadj
    have hne : u ≠ v := hadj.ne
    rcases lt_trichotomy (Fintype.equivFin V u) (Fintype.equivFin V v) with hlt | heq | hgt
    · exact Or.inl ⟨hne.symm, hadj, hlt⟩
    · exact False.elim (hne ((Fintype.equivFin V).injective heq))
    · exact Or.inr ⟨hne, hadj.symm, hgt⟩

theorem noDoubleEdges_orientProfile [DecidableEq V] (G : SimpleGraph V) :
    NoDoubleEdges (orientProfile G) := by
  intro u v hv hu
  simp only [orientProfile, LinkSet.mem_ofFinset, mem_filter, mem_univ, true_and] at hv hu
  exact lt_asymm hv.2.2 hu.2.2

theorem socialECost_orientProfile [DecidableEq V] (α : ℝ) (G : SimpleGraph V) :
    socialECost α (orientProfile G) = networkECost α G := by
  rw [(noDoubleEdges_orientProfile G).socialECost_eq_networkECost, formedGraph_orientProfile]

theorem socialCost_orientProfile [DecidableEq V] (α : ℝ) (G : SimpleGraph V) :
    socialCost α (orientProfile G) = networkCost α G := by
  rw [(noDoubleEdges_orientProfile G).socialCost_eq_networkCost, formedGraph_orientProfile]

/-! ### Closed-form network costs and Lemma 19.1 (network level) -/

/-- A network `G` is **optimal** (or socially efficient) for edge cost `α` if it minimizes
`networkECost α` over all simple graphs on `V` ([TardosWexler2007], Section 19.2.2, p. 490). -/
@[expose] def IsOptimalNetwork (α : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ G' : SimpleGraph V, networkECost α G ≤ networkECost α G'

/-- A strategy profile `s` is **socially optimal** for edge cost `α` if it minimizes `socialECost α`
over all profiles. -/
@[expose] def IsSocialOptimum (α : ℝ) (s : Profile V) : Prop :=
  ∀ s' : Profile V, socialECost α s ≤ socialECost α s'

theorem isOptimalNetwork_iff_forall_profile {α : ℝ} {G : SimpleGraph V} :
    IsOptimalNetwork α G ↔ ∀ s' : Profile V, networkECost α G ≤ socialECost α s' := by
  classical
  refine ⟨fun h s' => (h (formedGraph s')).trans (networkECost_formedGraph_le α s'),
    fun h G' => ?_⟩
  simpa only [socialECost_orientProfile] using h (orientProfile G')

theorem NoDoubleEdges.isSocialOptimum_iff_isOptimalNetwork {α : ℝ} {s : Profile V}
    (hnd : NoDoubleEdges s) :
    IsSocialOptimum α s ↔ IsOptimalNetwork α (formedGraph s) := by
  rw [IsSocialOptimum, isOptimalNetwork_iff_forall_profile]
  simp only [hnd.socialECost_eq_networkECost]

private theorem sum_dist_starGraph_center (r : V) :
    (∑ v : V, (starGraph r).dist r v) = Fintype.card V - 1 := by
  classical
  rw [← sum_erase_add _ _ (mem_univ r)]
  simp only [SimpleGraph.dist_self, add_zero]
  have h1 : ∀ v ∈ univ.erase r, (starGraph r).dist r v = 1 := fun v hv =>
    dist_eq_one_iff_adj.mpr (starGraph_adj_center_iff.mpr (mem_erase.mp hv).1.symm)
  rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ r), card_univ, smul_eq_mul,
    mul_one]

private theorem sum_dist_starGraph_of_ne {r u : V} (hur : u ≠ r) :
    (∑ v : V, (starGraph r).dist u v) = 1 + 2 * (Fintype.card V - 2) := by
  classical
  rw [← sum_erase_add _ _ (mem_univ u)]
  simp only [SimpleGraph.dist_self, add_zero]
  have hrmem : r ∈ univ.erase u := mem_erase.mpr ⟨hur.symm, mem_univ r⟩
  rw [← sum_erase_add _ _ hrmem]
  have hur_adj : (starGraph r).dist u r = 1 :=
    dist_eq_one_iff_adj.mpr (starGraph_center_adj' hur.symm)
  have h2 : ∀ v ∈ (univ.erase u).erase r, (starGraph r).dist u v = 2 := by
    intro v hv
    obtain ⟨hvr, hvu⟩ := mem_erase.mp hv
    obtain ⟨hvu, _⟩ := mem_erase.mp hvu
    have hed : (starGraph r).edist u v = 2 := by
      rw [edist_eq_two_iff]
      refine ⟨hvu.symm, ?_, ⟨r, ?_⟩⟩
      · simp only [starGraph_adj, hur, hvr, or_self, and_false, not_false_eq_true]
      · rw [mem_commonNeighbors]
        exact ⟨starGraph_center_adj' hur.symm, starGraph_center_adj' hvr.symm⟩
    rw [SimpleGraph.dist, hed]
    rfl
  rw [sum_congr rfl h2, hur_adj, sum_const, card_erase_of_mem hrmem,
    card_erase_of_mem (mem_univ u), card_univ, smul_eq_mul]
  omega

private theorem sum_dist_top_vertex (u : V) :
    (∑ v : V, ((⊤ : SimpleGraph V).dist u v : ℝ)) = (Fintype.card V - 1 : ℕ) := by
  classical
  rw [← sum_erase_add _ _ (mem_univ u)]
  simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
  have h1 : ∀ v ∈ univ.erase u, ((⊤ : SimpleGraph V).dist u v : ℝ) = 1 := fun v hv => by
    rw [dist_top_of_ne (mem_erase.mp hv).1.symm, Nat.cast_one]
  rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ u), card_univ, nsmul_eq_mul,
    mul_one]

/-- Closed-form real social cost of `starGraph r` on `n = Fintype.card V` vertices:
`α(n - 1) + 2(n - 1)²`. -/
theorem networkCost_starGraph (α : ℝ) (r : V) :
    networkCost α (starGraph r) =
      α * (Fintype.card V - 1 : ℕ) + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 := by
  classical
  have hedge : (starGraph r).edgeSet.ncard = Fintype.card V - 1 := by
    have htree := (isTree_starGraph r).card_edgeFinset
    rw [ncard_edgeSet_eq_card_edgeFinset]
    omega
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  have hsum : (∑ u : V, ∑ v : V, (starGraph r).dist u v) = 2 * (Fintype.card V - 1) ^ 2 := by
    rw [← sum_erase_add _ _ (mem_univ r), sum_dist_starGraph_center r]
    have hleaf : ∀ u ∈ univ.erase r,
        (∑ v : V, (starGraph r).dist u v) = 1 + 2 * (Fintype.card V - 2) :=
      fun u hu => sum_dist_starGraph_of_ne (mem_erase.mp hu).1
    rw [sum_congr rfl hleaf, sum_const, card_erase_of_mem (mem_univ r), card_univ, smul_eq_mul]
    rcases eq_or_lt_of_le hcard with h1 | h2
    · rw [← h1]; norm_num
    · set m := Fintype.card V - 2
      have hm : Fintype.card V = m + 2 := by omega
      have hm1 : m + 2 - 1 = m + 1 := rfl
      rw [hm, hm1]
      ring
  rw [networkCost_def, hedge]
  have hcast : (∑ u : V, ∑ v : V, ((starGraph r).dist u v : ℝ)) =
      ((∑ u : V, ∑ v : V, (starGraph r).dist u v : ℕ) : ℝ) := by
    push_cast; rfl
  rw [hcast, hsum]
  push_cast
  ring

/-- Closed-form real social cost of the complete graph `⊤` on `n = Fintype.card V` vertices:
`α · n.choose 2 + n(n - 1)`. -/
theorem networkCost_top (α : ℝ) :
    networkCost α (⊤ : SimpleGraph V) =
      α * ((Fintype.card V).choose 2 : ℝ) +
        (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
  classical
  have hedge : (⊤ : SimpleGraph V).edgeSet.ncard = (Fintype.card V).choose 2 := by
    rw [ncard_edgeSet_eq_card_edgeFinset, card_edgeFinset_top_eq_card_choose_two]
  simp only [networkCost_def, hedge, sum_dist_top_vertex, sum_const, card_univ, nsmul_eq_mul]

/-- In any preconnected graph `G` on `n` vertices with `m` edges, non-adjacent distinct pairs have
distance at least `2`, giving `2n(n - 1) ≤ (∑_{u, v} dist_G(u, v)) + 2m`
([TardosWexler2007], Proof of Lemma 19.1, p. 490). -/
theorem two_mul_card_mul_le_sum_dist_add_two_mul_edges {G : SimpleGraph V} (hc : G.Preconnected) :
    2 * (Fintype.card V * (Fintype.card V - 1)) ≤
      (∑ u : V, ∑ v : V, G.dist u v) + 2 * G.edgeSet.ncard := by
  classical
  have hadj_sum : 2 * G.edgeSet.ncard =
      ∑ u : V, ∑ v : V, if G.Adj u v then 1 else 0 := by
    rw [ncard_edgeSet_eq_card_edgeFinset, ← G.sum_degrees_eq_twice_card_edges]
    refine sum_congr rfl fun u _ => ?_
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
  have hoff_sum : 2 * (Fintype.card V * (Fintype.card V - 1)) =
      ∑ u : V, ∑ v : V, if u ≠ v then 2 else 0 := by
    have inner : ∀ u : V, (∑ v : V, if u ≠ v then 2 else 0) = 2 * (Fintype.card V - 1) := by
      intro u
      rw [← sum_erase_add _ _ (mem_univ u)]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
      have h1 : ∀ v ∈ univ.erase u, (if u ≠ v then 2 else 0) = 2 := fun v hv => by
        simp only [ne_eq, (mem_erase.mp hv).1.symm, not_false_eq_true, ↓reduceIte]
      rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ u), card_univ, smul_eq_mul,
        mul_comm]
    simp only [inner, sum_const, card_univ, smul_eq_mul]
    ring
  rw [hoff_sum, hadj_sum, ← sum_add_distrib]
  refine sum_le_sum fun u _ => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun v _ => ?_
  by_cases huv : u = v
  · subst huv; simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_le]
  · simp only [ne_eq, huv, not_false_eq_true, ↓reduceIte]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ↓reduceIte, dist_eq_one_iff_adj.mpr hadj, le_refl]
    · simp only [hadj, ↓reduceIte, add_zero]
      exact (hc u v).one_lt_dist_of_ne_of_not_adj huv hadj

/-- Lower bound `(α - 2)m + 2n(n - 1) ≤ SC(G)` for every preconnected graph `G`
([TardosWexler2007], Proof of Lemma 19.1, p. 490). -/
theorem le_networkCost_of_preconnected {α : ℝ} {G : SimpleGraph V} (hc : G.Preconnected) :
    (α - 2) * (G.edgeSet.ncard : ℝ) +
      2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ≤ networkCost α G := by
  have hnat : ((2 * (Fintype.card V * (Fintype.card V - 1)) : ℕ) : ℝ) ≤
      (((∑ u : V, ∑ v : V, G.dist u v) + 2 * G.edgeSet.ncard : ℕ) : ℝ) :=
    Nat.cast_le.mpr (two_mul_card_mul_le_sum_dist_add_two_mul_edges hc)
  push_cast at hnat
  rw [networkCost_def]
  linarith

private theorem card_sub_one_le_ncard_edgeSet {G : SimpleGraph V} (hc : G.Connected) :
    ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (G.edgeSet.ncard : ℝ) := by
  have h1 := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h1
  exact_mod_cast (show Fintype.card V - 1 ≤ G.edgeSet.ncard by omega)

/-- **Optimal network for `α ≥ 2`** ([TardosWexler2007], Lemma 19.1, p. 490): for `α ≥ 2`, any star
`starGraph r` minimizes `networkECost α` over all networks. -/
theorem isOptimalNetwork_starGraph {α : ℝ} (hα : 2 ≤ α) (r : V) :
    IsOptimalNetwork α (starGraph r) := by
  have : Nonempty V := ⟨r⟩
  have hα₀ : 0 ≤ α := by linarith
  intro G'
  by_cases hc : G'.Connected
  · rw [networkECost_eq_ofReal_of_connected hα₀ (connected_starGraph r),
      networkECost_eq_ofReal_of_connected hα₀ hc,
      ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg hα₀ G')]
    have hm_real := card_sub_one_le_ncard_edgeSet hc
    have hlow := le_networkCost_of_preconnected (α := α) hc.preconnected
    have hmul : (α - 2) * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (α - 2) * (G'.edgeSet.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hm_real (by linarith)
    have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
    have hident : α * ((Fintype.card V - 1 : ℕ) : ℝ) + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 =
        (α - 2) * ((Fintype.card V - 1 : ℕ) : ℝ) +
          2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
      have hcast : (Fintype.card V : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel hcard).symm
      rw [hcast]; ring
    rw [networkCost_starGraph, hident]
    linarith
  · rw [networkECost_eq_top_iff.mpr hc]
    exact le_top

/-- **Optimal network for `0 ≤ α ≤ 2`** ([TardosWexler2007], Lemma 19.1, p. 490): for `0 ≤ α ≤ 2`,
the complete graph `⊤` minimizes `networkECost α` over all networks. -/
theorem isOptimalNetwork_top {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 2) :
    IsOptimalNetwork α (⊤ : SimpleGraph V) := by
  classical
  intro G'
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    rw [networkECost_def, Set.eq_empty_of_isEmpty (⊤ : SimpleGraph V).edgeSet, Set.ncard_empty]
    simp only [Nat.cast_zero, mul_zero, univ_eq_empty, sum_empty, add_zero, zero_le]
  · by_cases hc : G'.Connected
    · have htop_pre : (⊤ : SimpleGraph V).Preconnected := fun u v =>
        if huv : u = v then huv ▸ Reachable.rfl else Adj.reachable (by simp [huv])
      rw [networkECost_eq_ofReal_of_preconnected hα₀ htop_pre,
        networkECost_eq_ofReal_of_connected hα₀ hc,
        ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg hα₀ G')]
      have hm : G'.edgeSet.ncard ≤ (Fintype.card V).choose 2 := by
        rw [ncard_edgeSet_eq_card_edgeFinset]
        exact G'.card_edgeFinset_le_card_choose_two
      have hm_real : (G'.edgeSet.ncard : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by
        exact_mod_cast hm
      have hchoose := two_mul_choose_two (Fintype.card V)
      have hlow := le_networkCost_of_preconnected (α := α) hc.preconnected
      have hmul : (2 - α) * (G'.edgeSet.ncard : ℝ) ≤
          (2 - α) * ((Fintype.card V).choose 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hm_real (by linarith)
      rw [networkCost_top]
      linarith
    · rw [networkECost_eq_top_iff.mpr hc]
      exact le_top

/-- **Social optimality of star profiles for `α ≥ 2`** ([TardosWexler2007], Lemma 19.1, p. 490). -/
theorem NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_starGraph {α : ℝ} (hα : 2 ≤ α) (r : V)
    {s : Profile V} (hG : formedGraph s = starGraph r) (hnd : NoDoubleEdges s) :
    IsSocialOptimum α s := by
  rw [hnd.isSocialOptimum_iff_isOptimalNetwork, hG]
  exact isOptimalNetwork_starGraph hα r

/-- **Social optimality of complete-graph profiles for `0 ≤ α ≤ 2`** ([TardosWexler2007],
Lemma 19.1, p. 490). -/
theorem NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_top {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 2)
    {s : Profile V} (hG : formedGraph s = ⊤) (hnd : NoDoubleEdges s) :
    IsSocialOptimum α s := by
  rw [hnd.isSocialOptimum_iff_isOptimalNetwork, hG]
  exact isOptimalNetwork_top hα₀ hα

/-- Lower bound `α(n - 1) + n(n - 1) ≤ SC(G')` for every connected network `G'` when `0 ≤ α`
([TardosWexler2007], Proof of Lemma 19.4, p. 492). -/
theorem edge_add_dist_le_networkCost_of_connected {α : ℝ} (hα₀ : 0 ≤ α) {G' : SimpleGraph V}
    (hc : G'.Connected) :
    α * (Fintype.card V - 1 : ℕ) +
      (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ≤ networkCost α G' := by
  classical
  have hm_real := card_sub_one_le_ncard_edgeSet hc
  have hdist : Fintype.card V * (Fintype.card V - 1) ≤ ∑ u : V, ∑ v : V, G'.dist u v := by
    have hu : ∀ u : V, Fintype.card V - 1 ≤ ∑ v : V, G'.dist u v := by
      intro u
      rw [← sum_erase_add _ _ (mem_univ u)]
      simp only [SimpleGraph.dist_self, add_zero]
      calc Fintype.card V - 1
          = ∑ _v ∈ univ.erase u, 1 := by
            simp only [sum_const, card_erase_of_mem (mem_univ u), card_univ, smul_eq_mul, mul_one]
        _ ≤ ∑ v ∈ univ.erase u, G'.dist u v :=
          sum_le_sum fun v hv => (hc u v).pos_dist_of_ne (mem_erase.mp hv).1.symm
    calc Fintype.card V * (Fintype.card V - 1)
        = ∑ _u : V, (Fintype.card V - 1) := by simp only [sum_const, card_univ, smul_eq_mul]
      _ ≤ ∑ u : V, ∑ v : V, G'.dist u v := sum_le_sum fun u _ => hu u
  have hdist_real : (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ≤
      ∑ u : V, ∑ v : V, (G'.dist u v : ℝ) := by exact_mod_cast hdist
  have hmul : α * (Fintype.card V - 1 : ℕ) ≤ α * (G'.edgeSet.ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hm_real hα₀
  rw [networkCost_def]
  linarith

/-- Exact star-to-clique ratio `(4n² - 6n + 2) / (3n² - 3n)` at the threshold `α = 1`
([TardosWexler2007], Proof of Theorem 19.3, p. 491). -/
theorem networkCost_one_starGraph_div_top (hV : 2 ≤ Fintype.card V) (r : V) :
    networkCost 1 (starGraph r) / networkCost 1 (⊤ : SimpleGraph V) =
      (4 * (Fintype.card V : ℝ) ^ 2 - 6 * (Fintype.card V : ℝ) + 2) /
        (3 * (Fintype.card V : ℝ) ^ 2 - 3 * (Fintype.card V : ℝ)) := by
  have hchoose := two_mul_choose_two (Fintype.card V)
  have hn_sub : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]
  have hn_pos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hn1_pos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
    linarith
  have hstar : networkCost 1 (starGraph r) =
      (2 * (Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 1) := by
    rw [networkCost_starGraph, hn_sub]; ring
  have htop : networkCost 1 (⊤ : SimpleGraph V) =
      3 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
    rw [networkCost_top, ← hn_sub] at *
    linarith
  have hden1 : 3 * (Fintype.card V : ℝ) ^ 2 - 3 * (Fintype.card V : ℝ) ≠ 0 := by
    have : 3 * (Fintype.card V : ℝ) ^ 2 - 3 * (Fintype.card V : ℝ) =
        3 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by ring
    rw [this]; positivity
  rw [hstar, htop]
  field_simp [hn_pos.ne', hn1_pos.ne', hden1]
  ring

end Costs

/-! ### Solution concepts, canonical profiles, and Nash equilibria -/

section PureNash

private theorem dist_getVert_of_shortest {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) {m : ℕ} (hm : m ≤ p.length) :
    G.dist u (p.getVert m) = m ∧ G.dist (p.getVert m) v = p.length - m := by
  have h1 : G.dist u (p.getVert m) ≤ m := by
    have h := dist_le (p.take m)
    rwa [Walk.take_length, Nat.min_eq_left hm] at h
  have h2 : G.dist (p.getVert m) v ≤ p.length - m := by
    have h := dist_le (p.drop m)
    rwa [Walk.drop_length] at h
  have htri : G.dist u v ≤ G.dist u (p.getVert m) + G.dist (p.getVert m) v := hc.dist_triangle
  omega

private theorem exists_adj_step_mem {V : Type*} {H : SimpleGraph V} {S : Finset V} {a b : V}
    (q : H.Walk a b) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ u' v' : V, u' ∉ S ∧ v' ∈ S ∧ H.Adj u' v' := by
  induction q with
  | nil => exact False.elim (ha hb)
  | @cons x y _ hadj _ ih =>
    by_cases hy : y ∈ S
    · exact ⟨x, y, ha, hy, hadj⟩
    · exact ih hy hb

private theorem getVert_one_and_dist_deleteEdges_of_lt {V : Type*} {G : SimpleGraph V}
    {u w : V} (p : G.Walk u w) (hp : p.length = G.dist u w)
    {v : V} (huv : u ≠ v) (hlt : G.dist u w < (G.deleteEdges {s(u, v)}).dist u w) :
    p.getVert 1 = v ∧ (G.deleteEdges {s(u, v)}).dist v w ≤ G.dist u w - 1 := by
  have he_mem : s(u, v) ∈ p.edges := by
    by_contra hnot
    have hle : (G.deleteEdges {s(u, v)}).dist u w ≤ p.length := by
      have h := dist_le (p.toDeleteEdges {s(u, v)} (fun e he => by
        rw [Set.mem_singleton_iff]; rintro rfl; exact hnot he))
      rwa [Walk.length_transfer] at h
    omega
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  cases p with
  | nil => simp only [Walk.edges_nil, List.not_mem_nil] at he_mem
  | @cons _ x _ hadj p_tail =>
    obtain ⟨_, hu_not_tail⟩ := (Walk.cons_isPath_iff hadj p_tail).mp hpath
    have hnot_tail : s(u, v) ∉ p_tail.edges := fun hmem =>
      hu_not_tail (p_tail.fst_mem_support_of_mem_edges hmem)
    simp only [Walk.edges_cons, List.mem_cons] at he_mem
    have heq_sym : s(u, v) = s(u, x) := he_mem.resolve_right hnot_tail
    have hxv : x = v := by
      rw [Sym2.eq_iff] at heq_sym
      rcases heq_sym with ⟨_, hvx⟩ | ⟨_, hvu⟩
      · exact hvx.symm
      · exact False.elim (huv hvu.symm)
    subst hxv
    refine ⟨by simp only [Walk.getVert_cons_succ, Walk.getVert_zero], ?_⟩
    have hq : (G.deleteEdges {s(u, x)}).dist x w ≤ p_tail.length := by
      have h := dist_le (p_tail.toDeleteEdges {s(u, x)} (fun e he => by
        rw [Set.mem_singleton_iff]; rintro rfl; exact hnot_tail he))
      rwa [Walk.length_transfer] at h
    simp only [Walk.length_cons] at hp
    omega

private theorem sum_range_shortcut_savings :
    ∀ (k d : ℕ), 2 * k ≤ d → (∑ j ∈ range k, (d - 1 - 2 * j)) = k * (d - k)
  | 0, _, _ => by simp only [range_zero, sum_empty, zero_mul]
  | k + 1, d, hkd => by
    rw [sum_range_succ, sum_range_shortcut_savings k d (by omega)]
    have h1 : 2 * k + 1 ≤ d := by omega
    have h2 : 2 * k ≤ d - 1 := by omega
    have h3 : 1 ≤ d := by omega
    have h4 : k ≤ d := by omega
    have h5 : k + 1 ≤ d := by omega
    zify [h1, h2, h3, h4, h5]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A strategy profile `s` is a **pure Nash equilibrium** for edge cost `α` if no player `u` can
strictly lower `playerECost α` by a unilateral deviation ([TardosWexler2007], Section 19.2.1,
p. 490). -/
@[expose] def IsPureNash (α : ℝ) (s : Profile V) : Prop :=
  ∀ (u : V) (a : LinkSet V u), playerECost α s u ≤ playerECost α (Function.update s u a) u

/-- A network `G` is **stable** for edge cost `α` if it is formed by some pure Nash equilibrium
strategy profile ([TardosWexler2007], Section 19.2.1, p. 490). -/
@[expose] def IsStableNetwork (α : ℝ) (G : SimpleGraph V) : Prop :=
  ∃ s : Profile V, formedGraph s = G ∧ IsPureNash α s

/-- Center-sponsored star profile at `r : V`: player `r` builds links to every `v ≠ r`, while all
leaf players build nothing ([TardosWexler2007], Proof of Lemma 19.2, p. 491). -/
def starCenterProfile (r : V) : Profile V :=
  fun u => if u = r then LinkSet.univ u else ∅

/-- Leaf-sponsored star profile at `r : V`: each leaf `u ≠ r` builds a single link to `r`, while
center `r` builds nothing. -/
def starLeafProfile (r : V) : Profile V :=
  fun u => if u = r then ∅ else LinkSet.ofFinset u {r}

/-- Single-sponsor strategy profile forming the complete graph `⊤ : SimpleGraph V`. -/
noncomputable def completeProfile : Profile V :=
  orientProfile (⊤ : SimpleGraph V)

@[simp]
theorem formedGraph_starCenterProfile (r : V) :
    formedGraph (starCenterProfile r) = starGraph r := by
  ext u v
  simp only [formedGraph_adj, starCenterProfile, starGraph_adj]
  by_cases hur : u = r <;> by_cases hvr : v = r
  · subst hur hvr; simp
  · subst hur; simp [hvr, Ne.symm hvr]
  · subst hvr; simp [hur]
  · simp [hur, hvr]

theorem noDoubleEdges_starCenterProfile (r : V) :
    NoDoubleEdges (starCenterProfile r) := by
  intro u v hv hu
  simp only [starCenterProfile] at hv hu
  split_ifs at hv with hur
  · subst hur
    have hvu : v ≠ u := LinkSet.ne_of_mem hv
    simp only [hvu, ↓reduceIte, LinkSet.notMem_empty] at hu
  · exact LinkSet.notMem_empty v hv

omit [Fintype V] in
@[simp]
theorem formedGraph_starLeafProfile (r : V) :
    formedGraph (starLeafProfile r) = starGraph r := by
  ext u v
  simp only [formedGraph_adj, starLeafProfile, starGraph_adj]
  by_cases hur : u = r <;> by_cases hvr : v = r
  · subst hur hvr; simp
  · subst hur; simp [hvr, Ne.symm hvr]
  · subst hvr; simp [hur]
  · simp [hur, hvr]

omit [Fintype V] in
theorem noDoubleEdges_starLeafProfile (r : V) :
    NoDoubleEdges (starLeafProfile r) := by
  intro u v hv hu
  simp only [starLeafProfile] at hv hu
  split_ifs at hv with hur
  · exact LinkSet.notMem_empty v hv
  · simp only [LinkSet.mem_ofFinset, mem_singleton] at hv
    rcases hv with ⟨_, rfl⟩
    simp only [↓reduceIte, LinkSet.notMem_empty] at hu

@[simp]
theorem formedGraph_completeProfile :
    formedGraph (completeProfile : Profile V) = ⊤ :=
  formedGraph_orientProfile ⊤

theorem noDoubleEdges_completeProfile :
    NoDoubleEdges (completeProfile : Profile V) :=
  noDoubleEdges_orientProfile ⊤

theorem isSocialOptimum_starCenterProfile {α : ℝ} (hα : 2 ≤ α) (r : V) :
    IsSocialOptimum α (starCenterProfile r) :=
  (noDoubleEdges_starCenterProfile r).isSocialOptimum_of_formedGraph_eq_starGraph hα r
    (formedGraph_starCenterProfile r)

theorem isSocialOptimum_completeProfile {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 2) :
    IsSocialOptimum α (completeProfile : Profile V) :=
  noDoubleEdges_completeProfile.isSocialOptimum_of_formedGraph_eq_top hα₀ hα
    formedGraph_completeProfile

/-! ### Structural properties of pure Nash equilibria -/

/-- Unilaterally buying links to all other vertices makes `u` universal and hence guarantees finite
cost for player `u`, regardless of other players' strategies. -/
theorem playerECost_update_univ_ne_top (α : ℝ) (s : Profile V) (u : V) :
    playerECost α (Function.update s u (LinkSet.univ u)) u ≠ ⊤ := by
  rw [playerECost_ne_top_iff]
  intro v
  by_cases hvu : v = u
  · subst hvu; exact Reachable.rfl
  · refine Adj.reachable ?_
    rw [formedGraph_adj]
    left
    rw [Function.update_self, LinkSet.mem_univ]
    exact hvu

theorem IsPureNash.playerECost_ne_top {α : ℝ} {s : Profile V} (hs : IsPureNash α s) (u : V) :
    playerECost α s u ≠ ⊤ :=
  ne_top_of_le_ne_top (playerECost_update_univ_ne_top α s u) (hs u (LinkSet.univ u))

theorem IsPureNash.preconnected {α : ℝ} {s : Profile V} (hs : IsPureNash α s) :
    (formedGraph s).Preconnected :=
  fun u v => (playerECost_ne_top_iff.mp (hs.playerECost_ne_top u)) v

/-- Every pure Nash equilibrium on a nonempty vertex set forms a connected network
([TardosWexler2007], Section 19.2.1, p. 490). -/
theorem IsPureNash.connected [Nonempty V] {α : ℝ} {s : Profile V} (hs : IsPureNash α s) :
    (formedGraph s).Connected :=
  ⟨hs.preconnected⟩

theorem IsPureNash.socialECost_ne_top {α : ℝ} {s : Profile V} (hs : IsPureNash α s) :
    socialECost α s ≠ ⊤ := by
  rw [socialECost_def, ne_eq, ENNReal.sum_eq_top]
  push Not
  exact fun u _ => hs.playerECost_ne_top u

omit [Fintype V] in
private theorem formedGraph_update_erase_eq_deleteEdges {s : Profile V} (hnd : NoDoubleEdges s)
    {u v : V} (hv : v ∈ s u) :
    formedGraph (Function.update s u ((s u).erase v)) =
      (formedGraph s).deleteEdges {s(u, v)} := by
  have huv_not : u ∉ s v := hnd hv
  have hvu : v ≠ u := LinkSet.ne_of_mem hv
  ext x y
  simp only [formedGraph_adj, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  by_cases hxu : x = u
  · subst hxu
    by_cases hyx : y = x
    · subst hyx
      simp [Function.update_self, (s y).notMem_self]
    · rw [Function.update_self, Function.update_of_ne hyx, LinkSet.mem_erase_iff]
      by_cases hyv : y = v
      · subst hyv; simp [huv_not]
      · simp [hyv, hyx]
  · by_cases hyu : y = u
    · subst hyu
      rw [Function.update_of_ne hxu, Function.update_self, LinkSet.mem_erase_iff]
      by_cases hxv : x = v
      · subst hxv; simp [huv_not]
      · simp [hxv, hxu]
    · rw [Function.update_of_ne hxu, Function.update_of_ne hyu]
      simp [hxu, hyu]

/-- For `α > 0`, at most one endpoint pays for each undirected edge in any pure Nash equilibrium
([TardosWexler2007], Section 19.2.1, p. 490). -/
theorem IsPureNash.noDoubleEdges {α : ℝ} (hα : 0 < α) {s : Profile V} (hs : IsPureNash α s) :
    NoDoubleEdges s := by
  intro u v hv hu
  let s' := Function.update s u ((s u).erase v)
  have hG : formedGraph s' = formedGraph s := by
    ext x y
    simp only [formedGraph_adj, s']
    by_cases hxu : x = u
    · subst hxu
      by_cases hyx : y = x
      · subst hyx; simp [Function.update_self, (s y).notMem_self]
      · rw [Function.update_self, Function.update_of_ne hyx, LinkSet.mem_erase_iff]
        by_cases hyv : y = v
        · subst hyv; simp [hu]
        · simp [hyv]
    · by_cases hyu : y = u
      · subst hyu
        rw [Function.update_of_ne hxu, Function.update_self, LinkSet.mem_erase_iff]
        by_cases hxv : x = v
        · subst hxv; simp [hu]
        · simp [hxv]
      · rw [Function.update_of_ne hxu, Function.update_of_ne hyu]
  have hle := hs u ((s u).erase v)
  have hpc := playerECost_eq_ofReal_of_forall_reachable hα.le (hs.preconnected u)
  have hpc' : playerECost α s' u = ENNReal.ofReal (playerCost α s' u) :=
    playerECost_eq_ofReal_of_forall_reachable hα.le fun w => by
      rw [hG]; exact hs.preconnected u w
  rw [hpc, hpc', ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg hα.le s' u)] at hle
  have hcard : ((s' u).neighbors.card : ℝ) = ((s u).neighbors.card : ℝ) - 1 := by
    simp only [s', Function.update_self, LinkSet.neighbors_erase, card_erase_of_mem hv]
    rw [Nat.cast_sub (card_pos.mpr ⟨v, hv⟩), Nat.cast_one]
  have hdist : (∑ w : V, ((formedGraph s').dist u w : ℝ)) =
      ∑ w : V, ((formedGraph s).dist u w : ℝ) := by rw [hG]
  rw [playerCost_def, playerCost_def, hcard, hdist] at hle
  linarith

theorem IsPureNash.socialECost_eq_networkECost {α : ℝ} (hα : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) :
    socialECost α s = networkECost α (formedGraph s) := by
  rcases eq_or_lt_of_le hα with rfl | hpos
  · simp only [socialECost_eq_add_sum_edist, networkECost_def, ENNReal.ofReal_zero, zero_mul]
  · exact (hs.noDoubleEdges hpos).socialECost_eq_networkECost α

theorem IsPureNash.socialCost_eq_networkCost {α : ℝ} (hα : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) :
    socialCost α s = networkCost α (formedGraph s) := by
  rcases eq_or_lt_of_le hα with rfl | hpos
  · simp only [socialCost_eq_add_sum_dist, networkCost_def, zero_mul]
  · exact (hs.noDoubleEdges hpos).socialCost_eq_networkCost α

/-- Real-valued equilibrium inequality for deviations `a` that preserve reachability from `u`. -/
theorem IsPureNash.playerCost_le {α : ℝ} (hα : 0 ≤ α) {s : Profile V} (hs : IsPureNash α s)
    {u : V} {a : LinkSet V u}
    (hr : ∀ v, (formedGraph (Function.update s u a)).Reachable u v) :
    playerCost α s u ≤ playerCost α (Function.update s u a) u := by
  have hle := hs u a
  rw [playerECost_eq_ofReal_of_forall_reachable hα (hs.preconnected u),
    playerECost_eq_ofReal_of_forall_reachable hα hr,
    ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg hα _ u)] at hle
  exact hle

/-! ### Lemma 19.2: Star and complete-graph Nash equilibria -/

/-- **Star Nash equilibrium for `α ≥ 1`** ([TardosWexler2007], Lemma 19.2, p. 491): for `α ≥ 1`,
every single-sponsor profile forming `starGraph r` (including both center-sponsored and
leaf-sponsored stars) is a pure Nash equilibrium. -/
theorem NoDoubleEdges.isPureNash_of_formedGraph_eq_starGraph {α : ℝ} (hα : 1 ≤ α) (r : V)
    {s : Profile V} (hG : formedGraph s = starGraph r) (hnd : NoDoubleEdges s) :
    IsPureNash α s := by
  have hα₀ : 0 ≤ α := by linarith
  intro u a
  let s' := Function.update s u a
  by_cases htop : playerECost α s' u = ⊤
  · rw [htop]; exact le_top
  · have hr' : ∀ v, (formedGraph s').Reachable u v := playerECost_ne_top_iff.mp htop
    have hc_s : (formedGraph s).Connected := hG ▸ connected_starGraph r
    rw [playerECost_eq_ofReal_of_connected hα₀ hc_s u,
      playerECost_eq_ofReal_of_forall_reachable hα₀ hr',
      ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg hα₀ s' u)]
    have hleaf_no_leaf : ∀ x y : V, x ≠ r → y ≠ r → y ∉ s x := by
      intro x y hxr hyr hyx
      have hadj : (starGraph r).Adj x y := hG ▸ formedGraph_adj.mpr (Or.inl hyx)
      rw [starGraph_adj] at hadj
      exact hadj.2.elim hxr hyr
    by_cases hur : u = r
    · subst hur
      have hsub : (s u).neighbors ⊆ a.neighbors := by
        intro v hv
        have hvu : v ≠ u := LinkSet.ne_of_mem hv
        have huv_not : u ∉ s v := hnd hv
        obtain ⟨q_vu⟩ := (hr' v).symm
        cases q_vu with
        | nil => exact False.elim (hvu rfl)
        | @cons _ w _ hadj_vw _ =>
          rw [formedGraph_adj] at hadj_vw
          by_cases hwu : w = u
          · subst hwu
            simp only [s', Function.update_of_ne hvu, Function.update_self] at hadj_vw
            exact hadj_vw.resolve_left huv_not
          · simp only [s', Function.update_of_ne hvu, Function.update_of_ne hwu] at hadj_vw
            exact False.elim
              (hadj_vw.elim (hleaf_no_leaf v w hvu hwu) (hleaf_no_leaf w v hwu hvu))
      have hcard_le : ((s u).neighbors.card : ℝ) ≤ ((s' u).neighbors.card : ℝ) := by
        simp only [s', Function.update_self]
        exact_mod_cast card_le_card hsub
      have hdist_le : (∑ v : V, ((formedGraph s).dist u v : ℝ)) ≤
          ∑ v : V, ((formedGraph s').dist u v : ℝ) := by
        refine sum_le_sum fun v _ => ?_
        rw [hG]
        by_cases hvu : v = u
        · subst hvu; simp only [SimpleGraph.dist_self, le_refl]
        · have h1 : (starGraph u).dist u v = 1 :=
            dist_eq_one_iff_adj.mpr (starGraph_adj_center_iff.mpr (Ne.symm hvu))
          rw [h1]
          exact_mod_cast (hr' v).pos_dist_of_ne (Ne.symm hvu)
      rw [playerCost_def, playerCost_def]
      nlinarith
    · have hsu_sub : (s u).neighbors ⊆ {r} := fun v hv =>
        mem_singleton.mpr (by by_contra hvr; exact hleaf_no_leaf u v hur hvr hv)
      have hdist_s : (∑ v : V, ((formedGraph s).dist u v : ℝ)) =
          1 + 2 * ((Fintype.card V - 2 : ℕ) : ℝ) := by
        rw [hG]; exact_mod_cast sum_dist_starGraph_of_ne hur
      have hrmem : r ∈ univ.erase u := mem_erase.mpr ⟨Ne.symm hur, mem_univ r⟩
      let leaves := (univ.erase u).erase r
      have hcard_leaves : #leaves = Fintype.card V - 2 := by
        rw [card_erase_of_mem hrmem, card_erase_of_mem (mem_univ u), card_univ]
        omega
      have hsplit : ∀ f : V → ℝ, (∑ v : V, f v) = f u + f r + ∑ v ∈ leaves, f v := fun f => by
        rw [← sum_erase_add _ _ (mem_univ u), ← sum_erase_add _ _ hrmem]; ring
      by_cases hadj_ur : (formedGraph s').Adj u r
      · have hcard_rel : (s u).neighbors.card + #(a.neighbors.erase r) ≤ a.neighbors.card := by
          by_cases hru : r ∈ s u
          · have hsu_eq : (s u).neighbors = {r} :=
              Subset.antisymm hsu_sub (singleton_subset_iff.mpr hru)
            have hra : r ∈ a.neighbors := by
              rw [formedGraph_adj] at hadj_ur
              simp only [s', Function.update_self,
                Function.update_of_ne (Ne.symm hur)] at hadj_ur
              exact hadj_ur.resolve_right (hnd hru)
            rw [hsu_eq, card_singleton, add_comm, card_erase_add_one hra]
          · have hsu_eq : (s u).neighbors = ∅ := eq_empty_iff_forall_notMem.mpr fun v hv =>
              hru ((mem_singleton.mp (hsu_sub hv)) ▸ hv)
            rw [hsu_eq, card_empty, zero_add]
            exact card_erase_le
        have ha_sub : a.neighbors.erase r ⊆ leaves := fun v hv =>
          mem_erase.mpr ⟨(mem_erase.mp hv).1,
            mem_erase.mpr ⟨LinkSet.ne_of_mem (mem_erase.mp hv).2, mem_univ v⟩⟩
        have hleaf_dist : (2 * #leaves - #(a.neighbors.erase r) : ℕ) ≤
            ∑ v ∈ leaves, (formedGraph s').dist u v := by
          have hpart : leaves = (a.neighbors.erase r) ∪ (leaves \ a.neighbors.erase r) :=
            (union_sdiff_of_subset ha_sub).symm
          have h1 : #(a.neighbors.erase r) ≤
              ∑ v ∈ a.neighbors.erase r, (formedGraph s').dist u v := by
            calc #(a.neighbors.erase r)
                = ∑ _v ∈ a.neighbors.erase r, 1 := by simp only [sum_const, smul_eq_mul, mul_one]
              _ ≤ ∑ v ∈ a.neighbors.erase r, (formedGraph s').dist u v :=
                sum_le_sum fun v hv =>
                  (hr' v).pos_dist_of_ne (LinkSet.ne_of_mem (mem_of_mem_erase hv)).symm
          have h2 : 2 * #(leaves \ a.neighbors.erase r) ≤
              ∑ v ∈ leaves \ a.neighbors.erase r, (formedGraph s').dist u v := by
            calc 2 * #(leaves \ a.neighbors.erase r)
                = ∑ _v ∈ leaves \ a.neighbors.erase r, 2 := by
                  simp only [sum_const, smul_eq_mul, mul_comm 2]
              _ ≤ ∑ v ∈ leaves \ a.neighbors.erase r, (formedGraph s').dist u v := by
                refine sum_le_sum fun v hv => ?_
                obtain ⟨hvl, hvna⟩ := mem_sdiff.mp hv
                obtain ⟨hvr, hvu⟩ := mem_erase.mp hvl
                obtain ⟨hvu, _⟩ := mem_erase.mp hvu
                have hnadj : ¬ (formedGraph s').Adj u v := by
                  rw [formedGraph_adj]
                  simp only [s', Function.update_self, Function.update_of_ne hvu]
                  exact fun h => h.elim (fun hva => hvna (mem_erase.mpr ⟨hvr, hva⟩))
                    (hleaf_no_leaf v u hvr hur)
                exact (hr' v).one_lt_dist_of_ne_of_not_adj hvu.symm hnadj
          have hsum_split : (∑ v ∈ leaves, (formedGraph s').dist u v) =
              (∑ v ∈ a.neighbors.erase r, (formedGraph s').dist u v) +
                ∑ v ∈ leaves \ a.neighbors.erase r, (formedGraph s').dist u v := by
            conv_lhs => rw [hpart]
            exact sum_union disjoint_sdiff_self_right
          have hcs : #(leaves \ a.neighbors.erase r) = #leaves - #(a.neighbors.erase r) := by
            rw [card_sdiff, inter_eq_left.mpr ha_sub]
          have := card_le_card ha_sub
          omega
        have hdist_s' : 1 + 2 * ((Fintype.card V - 2 : ℕ) : ℝ) - (#(a.neighbors.erase r) : ℝ) ≤
            ∑ v : V, ((formedGraph s').dist u v : ℝ) := by
          rw [hsplit]
          have hu0 : ((formedGraph s').dist u u : ℝ) = 0 := by
            simp only [SimpleGraph.dist_self, Nat.cast_zero]
          have hr1 : ((formedGraph s').dist u r : ℝ) = 1 := by
            rw [dist_eq_one_iff_adj.mpr hadj_ur, Nat.cast_one]
          have hl_real : ((2 * #leaves - #(a.neighbors.erase r) : ℕ) : ℝ) ≤
              ∑ v ∈ leaves, ((formedGraph s').dist u v : ℝ) := by exact_mod_cast hleaf_dist
          have hle_c : #(a.neighbors.erase r) ≤ 2 * #leaves :=
            (card_le_card ha_sub).trans (by omega)
          rw [Nat.cast_sub hle_c, Nat.cast_mul, Nat.cast_ofNat, hcard_leaves] at hl_real
          linarith
        have hcard_rel_real : ((s u).neighbors.card : ℝ) + (#(a.neighbors.erase r) : ℝ) ≤
            ((s' u).neighbors.card : ℝ) := by
          simp only [s', Function.update_self]; exact_mod_cast hcard_rel
        rw [playerCost_def, playerCost_def, hdist_s]
        nlinarith
      · have hra_not : r ∉ a.neighbors := fun hra => hadj_ur <| by
          rw [formedGraph_adj]; left
          simp only [s', Function.update_self, LinkSet.mem_iff]
          exact hra
        have hur_not : u ∉ s r := fun hur_s => hadj_ur <| by
          rw [formedGraph_adj]; right
          simp only [s', Function.update_of_ne (Ne.symm hur)]
          exact hur_s
        have hru : r ∈ s u :=
          (formedGraph_adj.mp (hG ▸ starGraph_center_adj' (Ne.symm hur))).resolve_right hur_not
        have hsu_card : (s u).neighbors.card = 1 := by
          rw [Subset.antisymm hsu_sub (singleton_subset_iff.mpr hru), card_singleton]
        have ha_nonempty : a.neighbors.Nonempty := by
          rw [nonempty_iff_ne_empty]
          intro hempty
          obtain ⟨q⟩ := hr' r
          cases q with
          | nil => exact hur rfl
          | @cons _ w _ hadj_uw _ =>
            have hwu : w ≠ u := hadj_uw.ne.symm
            rw [formedGraph_adj] at hadj_uw
            simp only [s', Function.update_self, Function.update_of_ne hwu] at hadj_uw
            rcases hadj_uw with hwa | huw_s
            · rw [LinkSet.mem_iff, hempty] at hwa; exact notMem_empty w hwa
            · by_cases hwr : w = r
              · subst hwr; exact hur_not huw_s
              · exact hleaf_no_leaf w u hwr hur huw_s
        have ha_pos : 1 ≤ a.neighbors.card := card_pos.mpr ha_nonempty
        have ha_sub : a.neighbors ⊆ leaves := fun v hv =>
          mem_erase.mpr ⟨fun hvr => hra_not (hvr ▸ hv),
            mem_erase.mpr ⟨LinkSet.ne_of_mem hv, mem_univ v⟩⟩
        have ha_le : a.neighbors.card ≤ Fintype.card V - 2 := hcard_leaves ▸ card_le_card ha_sub
        have hleaf_dist : a.neighbors.card + 3 * (#leaves - a.neighbors.card) ≤
            ∑ v ∈ leaves, (formedGraph s').dist u v := by
          have hpart : leaves = a.neighbors ∪ (leaves \ a.neighbors) :=
            (union_sdiff_of_subset ha_sub).symm
          have h1 : a.neighbors.card ≤ ∑ v ∈ a.neighbors, (formedGraph s').dist u v := by
            calc a.neighbors.card
                = ∑ _v ∈ a.neighbors, 1 := by simp only [sum_const, smul_eq_mul, mul_one]
              _ ≤ ∑ v ∈ a.neighbors, (formedGraph s').dist u v :=
                sum_le_sum fun v hv => (hr' v).pos_dist_of_ne (LinkSet.ne_of_mem hv).symm
          have h2 : 3 * #(leaves \ a.neighbors) ≤
              ∑ v ∈ leaves \ a.neighbors, (formedGraph s').dist u v := by
            calc 3 * #(leaves \ a.neighbors)
                = ∑ _v ∈ leaves \ a.neighbors, 3 := by
                  simp only [sum_const, smul_eq_mul, mul_comm 3]
              _ ≤ ∑ v ∈ leaves \ a.neighbors, (formedGraph s').dist u v := by
                refine sum_le_sum fun v hv => ?_
                obtain ⟨hvl, hvna⟩ := mem_sdiff.mp hv
                obtain ⟨hvr, hvu⟩ := mem_erase.mp hvl
                obtain ⟨hvu, _⟩ := mem_erase.mp hvu
                have hnadj : ¬ (formedGraph s').Adj u v := by
                  rw [formedGraph_adj]
                  simp only [s', Function.update_self, Function.update_of_ne hvu]
                  exact fun h => h.elim hvna (hleaf_no_leaf v u hvr hur)
                have hcn : (formedGraph s').commonNeighbors u v = ∅ := by
                  rw [Set.eq_empty_iff_forall_notMem]
                  intro z hz
                  rw [mem_commonNeighbors] at hz
                  obtain ⟨huz, hvz⟩ := hz
                  have hzu : z ≠ u := huz.ne.symm
                  by_cases hzr : z = r
                  · subst hzr; exact hadj_ur huz
                  · rw [formedGraph_adj] at hvz
                    simp only [s', Function.update_of_ne hvu, Function.update_of_ne hzu] at hvz
                    exact hvz.elim (hleaf_no_leaf v z hvr hzr) (hleaf_no_leaf z v hzr hvr)
                have hed3 : 2 < (formedGraph s').edist u v :=
                  two_lt_edist_iff.mpr ⟨hvu.symm, hnadj, hcn⟩
                rw [← (hr' v).coe_dist_eq_edist] at hed3
                have hlt : 2 < (formedGraph s').dist u v := by exact_mod_cast hed3
                omega
          have hsum_split : (∑ v ∈ leaves, (formedGraph s').dist u v) =
              (∑ v ∈ a.neighbors, (formedGraph s').dist u v) +
                ∑ v ∈ leaves \ a.neighbors, (formedGraph s').dist u v := by
            conv_lhs => rw [hpart]
            exact sum_union disjoint_sdiff_self_right
          rw [card_sdiff, inter_eq_left.mpr ha_sub] at h2
          omega
        have hur_dist2 : 2 ≤ (formedGraph s').dist u r :=
          (hr' r).one_lt_dist_of_ne_of_not_adj hur hadj_ur
        have hdist_s' : 2 + (a.neighbors.card : ℝ) +
            3 * (((Fintype.card V - 2 : ℕ) : ℝ) - (a.neighbors.card : ℝ)) ≤
            ∑ v : V, ((formedGraph s').dist u v : ℝ) := by
          rw [hsplit]
          have hu0 : ((formedGraph s').dist u u : ℝ) = 0 := by
            simp only [SimpleGraph.dist_self, Nat.cast_zero]
          have hr2 : (2 : ℝ) ≤ ((formedGraph s').dist u r : ℝ) := by exact_mod_cast hur_dist2
          have hl_real : ((a.neighbors.card + 3 * (#leaves - a.neighbors.card) : ℕ) : ℝ) ≤
              ∑ v ∈ leaves, ((formedGraph s').dist u v : ℝ) := by exact_mod_cast hleaf_dist
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_sub (card_le_card ha_sub), hcard_leaves] at hl_real
          linarith
        have ha_pos_real : (1 : ℝ) ≤ (a.neighbors.card : ℝ) := by exact_mod_cast ha_pos
        have ha_le_real : (a.neighbors.card : ℝ) ≤ ((Fintype.card V - 2 : ℕ) : ℝ) := by
          exact_mod_cast ha_le
        rw [playerCost_def, playerCost_def, hsu_card, Nat.cast_one, hdist_s]
        simp only [s', Function.update_self]
        nlinarith

theorem isPureNash_starCenterProfile {α : ℝ} (hα : 1 ≤ α) (r : V) :
    IsPureNash α (starCenterProfile r) :=
  (noDoubleEdges_starCenterProfile r).isPureNash_of_formedGraph_eq_starGraph hα r
    (formedGraph_starCenterProfile r)

theorem isPureNash_starLeafProfile {α : ℝ} (hα : 1 ≤ α) (r : V) :
    IsPureNash α (starLeafProfile r) :=
  (noDoubleEdges_starLeafProfile r).isPureNash_of_formedGraph_eq_starGraph hα r
    (formedGraph_starLeafProfile r)

/-- **Any star is a stable network for `α ≥ 1`** ([TardosWexler2007], Lemma 19.2, p. 491). -/
theorem isStableNetwork_starGraph {α : ℝ} (hα : 1 ≤ α) (r : V) :
    IsStableNetwork α (starGraph r) :=
  ⟨starCenterProfile r, formedGraph_starCenterProfile r, isPureNash_starCenterProfile hα r⟩

/-- **Complete-graph Nash equilibrium for `0 ≤ α ≤ 1`** ([TardosWexler2007], Lemma 19.2, p. 491):
for `0 ≤ α ≤ 1`, every single-sponsor profile forming `⊤` is a pure Nash equilibrium. -/
theorem NoDoubleEdges.isPureNash_of_formedGraph_eq_top {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1)
    {s : Profile V} (hG : formedGraph s = ⊤) (hnd : NoDoubleEdges s) :
    IsPureNash α s := by
  intro u a
  let s' := Function.update s u a
  by_cases htop : playerECost α s' u = ⊤
  · rw [htop]; exact le_top
  · have hr' : ∀ v, (formedGraph s').Reachable u v := playerECost_ne_top_iff.mp htop
    have hr_s : ∀ v, (formedGraph s).Reachable u v := fun v => by
      rw [hG]
      exact if huv : u = v then huv ▸ Reachable.rfl else Adj.reachable (by simp [huv])
    rw [playerECost_eq_ofReal_of_forall_reachable hα₀ hr_s,
      playerECost_eq_ofReal_of_forall_reachable hα₀ hr',
      ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg hα₀ s' u)]
    let dropped := (s u).neighbors \ a.neighbors
    let kept := (univ.erase u) \ dropped
    have hdrop_sub : dropped ⊆ univ.erase u := fun v hv =>
      mem_erase.mpr ⟨LinkSet.ne_of_mem (mem_sdiff.mp hv).1, mem_univ v⟩
    have hpart : univ.erase u = dropped ∪ kept := (union_sdiff_of_subset hdrop_sub).symm
    have hdist_s : (∑ v : V, ((formedGraph s).dist u v : ℝ)) = (Fintype.card V - 1 : ℕ) := by
      rw [hG, sum_dist_top_vertex]
    have hdist_s' : (Fintype.card V - 1 : ℕ) + #dropped ≤
        ∑ v : V, (formedGraph s').dist u v := by
      rw [← sum_erase_add _ _ (mem_univ u)]
      simp only [SimpleGraph.dist_self, add_zero]
      conv_rhs => rw [hpart]
      rw [sum_union disjoint_sdiff_self_right]
      have hd2 : 2 * #dropped ≤ ∑ v ∈ dropped, (formedGraph s').dist u v := by
        calc 2 * #dropped
            = ∑ _v ∈ dropped, 2 := by simp only [sum_const, smul_eq_mul, mul_comm 2]
          _ ≤ ∑ v ∈ dropped, (formedGraph s').dist u v := by
            refine sum_le_sum fun v hv => ?_
            obtain ⟨hv_su, hv_na⟩ := mem_sdiff.mp hv
            have hvu : v ≠ u := LinkSet.ne_of_mem hv_su
            have hnadj : ¬ (formedGraph s').Adj u v := by
              rw [formedGraph_adj]
              simp only [s', Function.update_self, Function.update_of_ne hvu]
              exact fun h => h.elim hv_na (hnd hv_su)
            exact (hr' v).one_lt_dist_of_ne_of_not_adj hvu.symm hnadj
      have hk1 : #kept ≤ ∑ v ∈ kept, (formedGraph s').dist u v := by
        calc #kept
            = ∑ _v ∈ kept, 1 := by simp only [sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ v ∈ kept, (formedGraph s').dist u v :=
            sum_le_sum fun v hv =>
              (hr' v).pos_dist_of_ne (mem_erase.mp (mem_sdiff.mp hv).1).1.symm
      have hcard_kept : #kept = Fintype.card V - 1 - #dropped := by
        simp only [kept, card_sdiff, inter_eq_left.mpr hdrop_sub,
          card_erase_of_mem (mem_univ u), card_univ]
      have hle_d : #dropped ≤ Fintype.card V - 1 := by
        simpa only [card_erase_of_mem (mem_univ u), card_univ] using card_le_card hdrop_sub
      omega
    have hcard_a : (s u).neighbors.card ≤ a.neighbors.card + #dropped := by
      have hsub : (s u).neighbors ⊆ a.neighbors ∪ dropped := fun v hv =>
        if hva : v ∈ a.neighbors then mem_union_left _ hva
        else mem_union_right _ (mem_sdiff.mpr ⟨hv, hva⟩)
      exact (card_le_card hsub).trans (card_union_le _ _)
    have hdist_s'_real : ((Fintype.card V - 1 : ℕ) : ℝ) + (#dropped : ℝ) ≤
        ∑ v : V, ((formedGraph s').dist u v : ℝ) := by exact_mod_cast hdist_s'
    have hcard_a_real : ((s u).neighbors.card : ℝ) ≤
        (a.neighbors.card : ℝ) + (#dropped : ℝ) := by exact_mod_cast hcard_a
    have hdrop_nonneg : (0 : ℝ) ≤ (#dropped : ℝ) := Nat.cast_nonneg _
    rw [playerCost_def, playerCost_def, hdist_s]
    simp only [s', Function.update_self]
    nlinarith

theorem isPureNash_completeProfile {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1) :
    IsPureNash α (completeProfile : Profile V) :=
  noDoubleEdges_completeProfile.isPureNash_of_formedGraph_eq_top hα₀ hα
    formedGraph_completeProfile

/-- **The complete graph is a stable network for `0 ≤ α ≤ 1`** ([TardosWexler2007], Lemma 19.2,
p. 491). -/
theorem isStableNetwork_top {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1) :
    IsStableNetwork α (⊤ : SimpleGraph V) :=
  ⟨completeProfile, formedGraph_completeProfile, isPureNash_completeProfile hα₀ hα⟩

/-- On `|V| ≥ 3` vertices with `0 ≤ α`, the complete graph `⊤` is stable if and only if `α ≤ 1`
(for `|V| = 2`, `⊤ = starGraph 0` is stable for all `α ≥ 0`). -/
theorem isStableNetwork_top_iff {α : ℝ} (hα₀ : 0 ≤ α) (hV : 3 ≤ Fintype.card V) :
    IsStableNetwork α (⊤ : SimpleGraph V) ↔ α ≤ 1 := by
  refine ⟨fun ⟨s, hG, hs⟩ => ?_, isStableNetwork_top hα₀⟩
  by_contra! hgt
  have hpos : 0 < α := by linarith
  let e := (Fintype.equivFin V).symm
  have h01 : e ⟨0, by omega⟩ ≠ e ⟨1, by omega⟩ := fun h => by
    have := e.injective h; simp at this
  have hadj01 : (formedGraph s).Adj (e ⟨0, by omega⟩) (e ⟨1, by omega⟩) := by
    rw [hG]; simp [h01]
  obtain ⟨u, v, hv⟩ : ∃ u v : V, v ∈ s u :=
    (formedGraph_adj.mp hadj01).elim (fun h1 => ⟨_, _, h1⟩) (fun h2 => ⟨_, _, h2⟩)
  have hvu : v ≠ u := LinkSet.ne_of_mem hv
  obtain ⟨w, hwu, hwv⟩ : ∃ w : V, w ≠ u ∧ w ≠ v := by
    have hcard_uv : #((univ.erase u).erase v) = Fintype.card V - 2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨hvu, mem_univ v⟩), card_erase_of_mem (mem_univ u),
        card_univ]
      omega
    obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < #((univ.erase u).erase v))
    exact ⟨w, (mem_erase.mp (mem_erase.mp hw).2).1, (mem_erase.mp hw).1⟩
  let s' := Function.update s u ((s u).erase v)
  have hadj_z : ∀ z : V, z ≠ u → z ≠ v → (formedGraph s').Adj u z := by
    intro z hzu hzv
    have hadj_uz : (formedGraph s).Adj u z := by rw [hG]; simp [hzu.symm]
    rw [formedGraph_adj] at hadj_uz ⊢
    simp only [s', Function.update_self, Function.update_of_ne hzu, LinkSet.mem_erase_iff]
    exact hadj_uz.elim (fun h => Or.inl ⟨hzv, h⟩) Or.inr
  have hadj_wv : (formedGraph s').Adj w v := by
    have hadj_s : (formedGraph s).Adj w v := by rw [hG]; simp [hwv]
    rw [formedGraph_adj] at hadj_s ⊢
    simpa only [s', Function.update_of_ne hwu, Function.update_of_ne hvu] using hadj_s
  have hr' : ∀ z : V, (formedGraph s').Reachable u z := fun z =>
    if hzu : z = u then hzu ▸ Reachable.rfl
    else if hzv : z = v then hzv ▸ (hadj_z w hwu hwv).reachable.trans hadj_wv.reachable
    else (hadj_z z hzu hzv).reachable
  have hle := hs.playerCost_le hα₀ hr'
  have hcard : ((s' u).neighbors.card : ℝ) = ((s u).neighbors.card : ℝ) - 1 := by
    simp only [s', Function.update_self, LinkSet.neighbors_erase, card_erase_of_mem hv]
    rw [Nat.cast_sub (card_pos.mpr ⟨v, hv⟩), Nat.cast_one]
  have hdist_s : (∑ z : V, ((formedGraph s).dist u z : ℝ)) = (Fintype.card V - 1 : ℕ) := by
    rw [hG, sum_dist_top_vertex]
  have hdist_uv : (formedGraph s').dist u v ≤ 2 := by
    have h := dist_le (Walk.cons (hadj_z w hwu hwv) (Walk.cons hadj_wv Walk.nil))
    simpa only [Walk.length_cons, Walk.length_nil] using h
  have hdist_s' : (∑ z : V, ((formedGraph s').dist u z : ℝ)) ≤
      ((Fintype.card V - 1 : ℕ) : ℝ) + 1 := by
    rw [← sum_erase_add _ _ (mem_univ u)]
    simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
    have hvmem : v ∈ univ.erase u := mem_erase.mpr ⟨hvu, mem_univ v⟩
    rw [← sum_erase_add _ _ hvmem]
    have h1 : ∀ z ∈ (univ.erase u).erase v, ((formedGraph s').dist u z : ℝ) = 1 := by
      intro z hz
      obtain ⟨hzv, hzu⟩ := mem_erase.mp hz
      rw [dist_eq_one_iff_adj.mpr (hadj_z z (mem_erase.mp hzu).1 hzv), Nat.cast_one]
    rw [sum_congr rfl h1, sum_const, card_erase_of_mem hvmem, card_erase_of_mem (mem_univ u),
      card_univ, nsmul_eq_mul, mul_one]
    have h2 : ((formedGraph s').dist u v : ℝ) ≤ 2 := by exact_mod_cast hdist_uv
    have hsub : ((Fintype.card V - 1 - 1 : ℕ) : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V - 1), Nat.cast_one]
    linarith
  rw [playerCost_def, playerCost_def, hcard, hdist_s] at hle
  linarith

/-! ### Theorem 19.3: Price of stability -/

/-- **Price of stability `1` for `0 ≤ α ≤ 1`** ([TardosWexler2007], Theorem 19.3, p. 491): there
exists a pure Nash equilibrium that is also socially optimal. -/
theorem exists_isPureNash_isSocialOptimum_of_le_one {α : ℝ} (hα₀ : 0 ≤ α) (hα : α ≤ 1) :
    ∃ s : Profile V, IsPureNash α s ∧ IsSocialOptimum α s :=
  ⟨completeProfile, isPureNash_completeProfile hα₀ hα,
    isSocialOptimum_completeProfile hα₀ (by linarith)⟩

/-- **Price of stability `1` for `α ≥ 2`** ([TardosWexler2007], Theorem 19.3, p. 491): there exists
a pure Nash equilibrium that is also socially optimal. -/
theorem exists_isPureNash_isSocialOptimum_of_two_le {α : ℝ} (hα : 2 ≤ α) :
    ∃ s : Profile V, IsPureNash α s ∧ IsSocialOptimum α s := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    refine ⟨isEmptyElim, fun u => isEmptyElim u, fun _ => ?_⟩
    simp only [socialECost_def, univ_eq_empty, sum_empty, le_refl]
  · obtain ⟨r⟩ := hNE
    exact ⟨starCenterProfile r, isPureNash_starCenterProfile (by linarith) r,
      isSocialOptimum_starCenterProfile hα r⟩

/-- For `1 ≤ α ≤ 2` and `|V| ≥ 2`, `starCenterProfile r` is a pure Nash equilibrium with social
cost strictly less than `4 / 3` times any connected profile's real social cost
([TardosWexler2007], Proof of Theorem 19.3, p. 491). -/
theorem socialCost_starCenterProfile_lt_four_thirds_mul {α : ℝ} (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hV : 2 ≤ Fintype.card V) (r : V) {s' : Profile V} (hc : (formedGraph s').Connected) :
    socialCost α (starCenterProfile r) < (4 / 3) * socialCost α s' := by
  have hα₀ : 0 ≤ α := by linarith
  have hstar_cost : socialCost α (starCenterProfile r) =
      α * (Fintype.card V - 1 : ℕ) + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 := by
    rw [(noDoubleEdges_starCenterProfile r).socialCost_eq_networkCost,
      formedGraph_starCenterProfile, networkCost_starGraph]
  have hopt : networkCost α (⊤ : SimpleGraph V) ≤ socialCost α s' := by
    have hle := (isOptimalNetwork_iff_forall_profile.mp (isOptimalNetwork_top hα₀ hα₂)) s'
    have htop_pre : (⊤ : SimpleGraph V).Preconnected := fun u v =>
      if huv : u = v then huv ▸ Reachable.rfl else Adj.reachable (by simp [huv])
    rw [networkECost_eq_ofReal_of_preconnected hα₀ htop_pre,
      socialECost_eq_ofReal_of_connected hα₀ hc,
      ENNReal.ofReal_le_ofReal_iff (socialCost_nonneg hα₀ s')] at hle
    exact hle
  have hchoose := two_mul_choose_two (Fintype.card V)
  have htop_cost : networkCost α (⊤ : SimpleGraph V) =
      (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) * (α + 2) / 2 := by
    rw [networkCost_top]
    nlinarith
  have hn_eq : (Fintype.card V : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ Fintype.card V)).symm
  have hm1_nat : (1 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ Fintype.card V - 1)
  have hstrict : α * ((Fintype.card V - 1 : ℕ) : ℝ) + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 <
      (4 / 3) * ((Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) * (α + 2) / 2) := by
    let m : ℝ := ((Fintype.card V - 1 : ℕ) : ℝ)
    have hm1 : 1 ≤ m := hm1_nat
    rw [hn_eq]
    have hgap : 0 < ((2 * m - 1) * (α - 1) + 3) * m := by nlinarith
    change α * m + 2 * m ^ 2 < (4 / 3) * ((m + 1) * m * (α + 2) / 2)
    linarith
  rw [hstar_cost]
  linarith

/-- **Price of stability at most `4 / 3`** ([TardosWexler2007], Theorem 19.3, p. 491): for every
`0 ≤ α`, there exists a pure Nash equilibrium of social cost at most `4 / 3` times that of any
strategy profile. -/
theorem exists_isPureNash_socialECost_le_four_thirds {α : ℝ} (hα₀ : 0 ≤ α) :
    ∃ s : Profile V, IsPureNash α s ∧
      ∀ s' : Profile V, socialECost α s ≤ ENNReal.ofReal (4 / 3) * socialECost α s' := by
  have h1le43 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 / 3) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  by_cases h1 : α ≤ 1
  · obtain ⟨s, hne, hopt⟩ := exists_isPureNash_isSocialOptimum_of_le_one (V := V) hα₀ h1
    refine ⟨s, hne, fun s' => ?_⟩
    calc socialECost α s ≤ 1 * socialECost α s' := by simpa only [one_mul] using hopt s'
      _ ≤ ENNReal.ofReal (4 / 3) * socialECost α s' := by gcongr
  · by_cases h2 : 2 ≤ α
    · obtain ⟨s, hne, hopt⟩ := exists_isPureNash_isSocialOptimum_of_two_le (V := V) h2
      refine ⟨s, hne, fun s' => ?_⟩
      calc socialECost α s ≤ 1 * socialECost α s' := by simpa only [one_mul] using hopt s'
        _ ≤ ENNReal.ofReal (4 / 3) * socialECost α s' := by gcongr
    · push Not at h1 h2
      rcases isEmpty_or_nonempty V with hE | hNE
      · have := hE
        refine ⟨isEmptyElim, fun u => isEmptyElim u, fun _ => ?_⟩
        simp only [socialECost_def, univ_eq_empty, sum_empty, zero_le]
      · have : Nonempty V := hNE
        obtain ⟨r⟩ := hNE
        refine ⟨starCenterProfile r, isPureNash_starCenterProfile h1.le r, fun s' => ?_⟩
        by_cases hc : (formedGraph s').Connected
        · have hc_star : (formedGraph (starCenterProfile r)).Connected :=
            formedGraph_starCenterProfile r ▸ connected_starGraph r
          rw [socialECost_eq_ofReal_of_connected hα₀ hc_star,
            socialECost_eq_ofReal_of_connected hα₀ hc, ← ENNReal.ofReal_mul (by norm_num)]
          by_cases hV : 2 ≤ Fintype.card V
          · exact ENNReal.ofReal_le_ofReal
              (socialCost_starCenterProfile_lt_four_thirds_mul h1.le h2.le hV r hc).le
          · have hcard1 : Fintype.card V = 1 := by
              have := Fintype.card_pos (α := V); omega
            have h0 : socialCost α (starCenterProfile r) = 0 := by
              rw [(noDoubleEdges_starCenterProfile r).socialCost_eq_networkCost,
                formedGraph_starCenterProfile, networkCost_starGraph, hcard1]
              norm_num
            rw [h0]
            exact ENNReal.ofReal_le_ofReal
              (mul_nonneg (by norm_num) (socialCost_nonneg hα₀ s'))
        · rw [socialECost_eq_top_iff.mpr hc, ENNReal.mul_top]
          · exact le_top
          · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            norm_num

/-! ### Lemma 19.4: Social cost of a diameter-`d` Nash equilibrium -/

/-- Non-bridge edges paid for by player `u` in a pure Nash equilibrium `s` (`0 ≤ α`) cost at most
`2 * d * (n - 1)`, via the disjoint critical shortest-path sets `W v` ([TardosWexler2007], Proof of
Lemma 19.4, p. 492). -/
private theorem mul_nonBridge_neighbors_le {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) (u : V) :
    α * ((open scoped Classical in
        #({ v ∈ (s u).neighbors | ¬ (formedGraph s).IsBridge s(u, v) })) : ℝ) ≤
      (2 * (formedGraph s).diam : ℝ) * (Fintype.card V - 1 : ℕ) := by
  classical
  rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
  · simp only [zero_mul]; positivity
  · have : Nonempty V := ⟨u⟩
    let G := formedGraph s
    have hc : G.Connected := hs.connected
    have hnd : NoDoubleEdges s := hs.noDoubleEdges hα_pos
    have hediam : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hc
    let d := G.diam
    let NB := { v ∈ (s u).neighbors | ¬ G.IsBridge s(u, v) }
    let W : V → Finset V := fun v =>
      univ.filter fun w => G.dist u w < (G.deleteEdges {s(u, v)}).dist u w
    have hW_sub : ∀ v, W v ⊆ univ.erase u := by
      intro v w hw
      rw [mem_filter] at hw
      refine mem_erase.mpr ⟨?_, mem_univ w⟩
      rintro rfl
      rw [SimpleGraph.dist_self, SimpleGraph.dist_self] at hw
      exact lt_irrefl 0 hw.2
    have hW_disj : (NB : Set V).PairwiseDisjoint W := by
      intro v₁ hv₁ v₂ hv₂ hv12
      rw [Function.onFun, Finset.disjoint_left]
      intro w hw₁ hw₂
      rw [mem_filter] at hw₁ hw₂
      obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u w
      have huv₁ : u ≠ v₁ := (LinkSet.ne_of_mem (mem_filter.mp (mem_coe.mp hv₁)).1).symm
      have huv₂ : u ≠ v₂ := (LinkSet.ne_of_mem (mem_filter.mp (mem_coe.mp hv₂)).1).symm
      have hv1_eq := (getVert_one_and_dist_deleteEdges_of_lt p hp huv₁ hw₁.2).1
      have hv2_eq := (getVert_one_and_dist_deleteEdges_of_lt p hp huv₂ hw₂.2).1
      exact hv12 (hv1_eq.symm.trans hv2_eq)
    have hbound_v : ∀ v ∈ NB, α ≤ (2 * d : ℝ) * (#(W v) : ℝ) := by
      intro v hv_nb
      obtain ⟨hv_s, hnot_br⟩ := mem_filter.mp hv_nb
      have huv : u ≠ v := (LinkSet.ne_of_mem hv_s).symm
      have : Nontrivial V := ⟨⟨u, v, huv⟩⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (diam_ne_zero_of_ediam_ne_top hediam)
      let Gv := G.deleteEdges {s(u, v)}
      have hGv_conn : Gv.Connected := hc.preconnected.connected_deleteEdges_of_not_isBridge hnot_br
      have hGv_eq : formedGraph (Function.update s u ((s u).erase v)) = Gv :=
        formedGraph_update_erase_eq_deleteEdges hnd hv_s
      have hu_not_W : u ∉ W v := fun h => (mem_erase.mp (hW_sub v h)).1 rfl
      have hv_in_W : v ∈ W v := by
        rw [mem_filter]
        refine ⟨mem_univ v, ?_⟩
        have hd1 : G.dist u v = 1 := dist_eq_one_iff_adj.mpr (formedGraph_adj.mpr (Or.inl hv_s))
        have hnadj_v : ¬ Gv.Adj u v := by
          simp only [Gv, deleteEdges_adj, Set.mem_singleton_iff, not_true_eq_false, and_false,
            not_false_eq_true]
        rw [hd1]
        exact (hGv_conn u v).one_lt_dist_of_ne_of_not_adj huv hnadj_v
      obtain ⟨q_uv⟩ := hGv_conn u v
      obtain ⟨u', v', hu'_not, hv'_in, hadj_uv'⟩ := exists_adj_step_mem q_uv hu_not_W hv_in_W
      have hdu' : Gv.dist u u' ≤ d := by
        have hle_not : ¬ G.dist u u' < Gv.dist u u' := fun h =>
          hu'_not (mem_filter.mpr ⟨mem_univ u', h⟩)
        have hle_G : G.dist u u' ≤ d := dist_le_diam hediam
        omega
      have hdv' : Gv.dist v v' ≤ d - 1 := by
        obtain ⟨p_uv', hp_uv'⟩ := hc.exists_walk_length_eq_dist u v'
        have hlt_v' : G.dist u v' < Gv.dist u v' := (mem_filter.mp hv'_in).2
        have htail : Gv.dist v v' ≤ G.dist u v' - 1 :=
          (getVert_one_and_dist_deleteEdges_of_lt p_uv' hp_uv' huv hlt_v').2
        have hle_G : G.dist u v' ≤ d := dist_le_diam hediam
        omega
      have hGv_uv : Gv.dist u v ≤ 2 * d := by
        have htri1 : Gv.dist u v' ≤ Gv.dist u u' + Gv.dist u' v' := hGv_conn.dist_triangle
        have htri2 : Gv.dist u v ≤ Gv.dist u v' + Gv.dist v' v := hGv_conn.dist_triangle
        have hadj1 : Gv.dist u' v' = 1 := dist_eq_one_iff_adj.mpr hadj_uv'
        rw [dist_comm (u := v')] at htri2
        omega
      have hGv_w : ∀ w : V, Gv.dist u w ≤ G.dist u w + (if w ∈ W v then 2 * d else 0) := by
        intro w
        by_cases hw : w ∈ W v
        · simp only [hw, ↓reduceIte]
          obtain ⟨p_uw, hp_uw⟩ := hc.exists_walk_length_eq_dist u w
          have hlt_w : G.dist u w < Gv.dist u w := (mem_filter.mp hw).2
          have htail : Gv.dist v w ≤ G.dist u w - 1 :=
            (getVert_one_and_dist_deleteEdges_of_lt p_uw hp_uw huv hlt_w).2
          have htri : Gv.dist u w ≤ Gv.dist u v + Gv.dist v w := hGv_conn.dist_triangle
          omega
        · simp only [hw, ↓reduceIte, add_zero]
          have hnot_lt : ¬ G.dist u w < Gv.dist u w := fun h =>
            hw (mem_filter.mpr ⟨mem_univ w, h⟩)
          have hanti : G.dist u w ≤ Gv.dist u w := (hGv_conn u w).dist_anti (deleteEdges_le _)
          omega
      have hsum_Gv : (∑ w : V, Gv.dist u w) ≤ (∑ w : V, G.dist u w) + 2 * d * #(W v) := by
        calc (∑ w : V, Gv.dist u w)
            ≤ ∑ w : V, (G.dist u w + if w ∈ W v then 2 * d else 0) :=
              sum_le_sum fun w _ => hGv_w w
          _ = (∑ w : V, G.dist u w) + ∑ w : V, (if w ∈ W v then 2 * d else 0) := sum_add_distrib
          _ = (∑ w : V, G.dist u w) + 2 * d * #(W v) := by
            simp only [sum_ite_mem, univ_inter, sum_const, smul_eq_mul]
            ring
      have hr_s' : ∀ w, (formedGraph (Function.update s u ((s u).erase v))).Reachable u w := by
        rw [hGv_eq]; exact hGv_conn u
      have hne_le := hs.playerCost_le hα₀ hr_s'
      have hcard_erase : (((Function.update s u ((s u).erase v) u).neighbors.card : ℝ)) =
          ((s u).neighbors.card : ℝ) - 1 := by
        simp only [Function.update_self, LinkSet.neighbors_erase, card_erase_of_mem hv_s]
        rw [Nat.cast_sub (card_pos.mpr ⟨v, hv_s⟩), Nat.cast_one]
      have hsum_real :
          (∑ w : V, ((formedGraph (Function.update s u ((s u).erase v))).dist u w : ℝ)) ≤
            (∑ w : V, (G.dist u w : ℝ)) + (2 * d : ℝ) * (#(W v) : ℝ) := by
        rw [hGv_eq]; exact_mod_cast hsum_Gv
      rw [playerCost_def, playerCost_def, hcard_erase] at hne_le
      linarith
    have hsum_W : (∑ v ∈ NB, #(W v)) ≤ Fintype.card V - 1 := by
      rw [← card_biUnion hW_disj]
      have hbi_sub : NB.biUnion W ⊆ univ.erase u := biUnion_subset.mpr fun v _ => hW_sub v
      simpa only [card_erase_of_mem (mem_univ u), card_univ] using card_le_card hbi_sub
    have hsum_W_real : (∑ v ∈ NB, (#(W v) : ℝ)) ≤ (Fintype.card V - 1 : ℕ) := by
      exact_mod_cast hsum_W
    have hNB_eq : (open scoped Classical in
        #({ v ∈ (s u).neighbors | ¬ (formedGraph s).IsBridge s(u, v) })) = #NB := by
      congr
    rw [hNB_eq]
    calc α * (#NB : ℝ)
        = ∑ _v ∈ NB, α := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ v ∈ NB, (2 * d : ℝ) * (#(W v) : ℝ) := sum_le_sum hbound_v
      _ = (2 * d : ℝ) * ∑ v ∈ NB, (#(W v) : ℝ) := (mul_sum _ _ _).symm
      _ ≤ (2 * d : ℝ) * (Fintype.card V - 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hsum_W_real (by positivity)

/-- **Real-valued social-cost bound in terms of equilibrium diameter** ([TardosWexler2007],
Lemma 19.4, p. 491): if a pure Nash equilibrium `s` (`0 ≤ α`) forms a network of diameter `d`, its
social cost is at most `3d` times the social cost of any connected profile `s'`. -/
theorem IsPureNash.socialCost_le_three_mul_diam_mul {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) {s' : Profile V} (hc' : (formedGraph s').Connected) :
    socialCost α s ≤ (3 * (formedGraph s).diam : ℝ) * socialCost α s' := by
  classical
  have : Nonempty V := hc'.nonempty
  let G := formedGraph s
  have hc : G.Connected := hs.connected
  have hediam : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hc
  by_cases hnt : Nontrivial V
  · have hd_pos : 1 ≤ G.diam := Nat.pos_of_ne_zero (diam_ne_zero_of_ediam_ne_top hediam)
    have hdist_le : (∑ u : V, ∑ v : V, (G.dist u v : ℝ)) ≤
        (G.diam : ℝ) * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
      have hu : ∀ u : V, (∑ v : V, G.dist u v) ≤ G.diam * (Fintype.card V - 1) := by
        intro u
        rw [← sum_erase_add _ _ (mem_univ u)]
        simp only [SimpleGraph.dist_self, add_zero]
        calc (∑ v ∈ univ.erase u, G.dist u v)
            ≤ ∑ _v ∈ univ.erase u, G.diam := sum_le_sum fun v _ => dist_le_diam hediam
          _ = G.diam * (Fintype.card V - 1) := by
            simp only [sum_const, card_erase_of_mem (mem_univ u), card_univ, smul_eq_mul,
              mul_comm G.diam]
      have htot : (∑ u : V, ∑ v : V, G.dist u v) ≤
          Fintype.card V * (G.diam * (Fintype.card V - 1)) := by
        calc (∑ u : V, ∑ v : V, G.dist u v)
            ≤ ∑ _u : V, (G.diam * (Fintype.card V - 1)) := sum_le_sum fun u _ => hu u
          _ = Fintype.card V * (G.diam * (Fintype.card V - 1)) := by
            simp only [sum_const, card_univ, smul_eq_mul]
      have htot_real : (∑ u : V, ∑ v : V, (G.dist u v : ℝ)) ≤
          (Fintype.card V : ℝ) * ((G.diam : ℝ) * (Fintype.card V - 1 : ℕ)) := by
        exact_mod_cast htot
      linarith
    have hedge_cost : α * (G.edgeSet.ncard : ℝ) ≤
        α * (Fintype.card V - 1 : ℕ) +
          (2 * G.diam : ℝ) * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
      rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
      · simp only [zero_mul, zero_add]; positivity
      · have hnd : NoDoubleEdges s := hs.noDoubleEdges hα_pos
        rw [← hnd.sum_card_neighbors_eq, Nat.cast_sum, mul_sum]
        have hsplit_u : ∀ u : V, (s u).neighbors.card =
            #{ v ∈ (s u).neighbors | G.IsBridge s(u, v) } +
              #{ v ∈ (s u).neighbors | ¬ G.IsBridge s(u, v) } :=
          fun u => (card_filter_add_card_filter_not _).symm
        simp only [hsplit_u, Nat.cast_add, mul_add, sum_add_distrib]
        have hbr_sum : (∑ u : V, #{ v ∈ (s u).neighbors | G.IsBridge s(u, v) }) ≤
            Fintype.card V - 1 := by
          obtain ⟨T, hTG, hT⟩ := hc.exists_isTree_le
          let brPairs : Finset (Σ _ : V, V) :=
            univ.sigma fun u => { v ∈ (s u).neighbors | G.IsBridge s(u, v) }
          have hcard_br : #brPairs =
              ∑ u : V, #{ v ∈ (s u).neighbors | G.IsBridge s(u, v) } :=
            card_sigma univ _
          rw [← hcard_br]
          have hinj : ∀ p₁ ∈ brPairs, ∀ p₂ ∈ brPairs,
              s(p₁.1, p₁.2) = s(p₂.1, p₂.2) → p₁ = p₂ := by
            rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ heq
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact False.elim (hnd (mem_filter.mp (mem_sigma.mp hp₁).2).1
                (mem_filter.mp (mem_sigma.mp hp₂).2).1)
          have himg_sub : brPairs.image (fun p => s(p.1, p.2)) ⊆ T.edgeFinset := by
            intro e he
            rw [mem_image] at he
            obtain ⟨⟨u, v⟩, hp, rfl⟩ := he
            obtain ⟨_, hbr⟩ := mem_filter.mp (mem_sigma.mp hp).2
            rw [mem_edgeFinset]
            by_contra heT
            have hle_del : T ≤ G.deleteEdges {s(u, v)} := fun a b hab => by
              rw [deleteEdges_adj, Set.mem_singleton_iff]
              exact ⟨hTG hab, fun heq => heT (heq ▸ hab)⟩
            exact isBridge_iff.mp hbr ((hT.connected u v).mono hle_del)
          have hTcard := hT.card_edgeFinset
          have hle_img : #brPairs ≤ #T.edgeFinset := by
            rw [← card_image_of_injOn hinj]
            exact card_le_card himg_sub
          omega
        have hbr_real : (∑ u : V, α * (#({ v ∈ (s u).neighbors | G.IsBridge s(u, v) }) : ℝ)) ≤
            α * (Fintype.card V - 1 : ℕ) := by
          rw [← mul_sum, ← Nat.cast_sum]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbr_sum) hα₀
        have hnb_u : ∀ u : V,
            α * (#({ v ∈ (s u).neighbors | ¬ G.IsBridge s(u, v) }) : ℝ) ≤
              (2 * G.diam : ℝ) * (Fintype.card V - 1 : ℕ) := by
          intro u
          convert mul_nonBridge_neighbors_le hα₀ hs u using 3
        have hnb_real : (∑ u : V, α * (#({ v ∈ (s u).neighbors | ¬ G.IsBridge s(u, v) }) : ℝ)) ≤
            (2 * G.diam : ℝ) * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
          calc (∑ u : V, α * (#({ v ∈ (s u).neighbors | ¬ G.IsBridge s(u, v) }) : ℝ))
              ≤ ∑ _u : V, (2 * G.diam : ℝ) * (Fintype.card V - 1 : ℕ) :=
                sum_le_sum fun u _ => hnb_u u
            _ = (2 * G.diam : ℝ) * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
                simp only [sum_const, card_univ, nsmul_eq_mul]; ring
        linarith
    have hlow_s' : α * (Fintype.card V - 1 : ℕ) +
        (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ≤ socialCost α s' := by
      have hnet : networkCost α (formedGraph s') ≤ socialCost α s' := by
        have hle := networkECost_formedGraph_le α s'
        rw [networkECost_eq_ofReal_of_connected hα₀ hc',
          socialECost_eq_ofReal_of_connected hα₀ hc',
          ENNReal.ofReal_le_ofReal_iff (socialCost_nonneg hα₀ s')] at hle
        exact hle
      exact (edge_add_dist_le_networkCost_of_connected hα₀ hc').trans hnet
    have hd1 : (1 : ℝ) ≤ (G.diam : ℝ) := by exact_mod_cast hd_pos
    rw [hs.socialCost_eq_networkCost hα₀, networkCost_def]
    have hα_term : α * ((Fintype.card V - 1 : ℕ) : ℝ) ≤
        (3 * (G.diam : ℝ)) * (α * ((Fintype.card V - 1 : ℕ) : ℝ)) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    have hdist_term : (3 * (G.diam : ℝ)) * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) =
        (2 * (G.diam : ℝ) + (G.diam : ℝ)) * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) := by
      ring
    have hmul_low := mul_le_mul_of_nonneg_left hlow_s' (by positivity : 0 ≤ 3 * (G.diam : ℝ))
    linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have hsc0 : socialCost α s = 0 := by
      rw [hs.socialCost_eq_networkCost hα₀, networkCost_def]
      have he0 : G.edgeSet = ∅ := by
        ext ⟨a, b⟩
        simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]
        rw [Subsingleton.elim a b]
        exact G.loopless.irrefl b
      have hd0 : (∑ u : V, ∑ v : V, (G.dist u v : ℝ)) = 0 :=
        sum_eq_zero fun u _ => sum_eq_zero fun v _ => by
          rw [Subsingleton.elim u v, SimpleGraph.dist_self, Nat.cast_zero]
      rw [he0, Set.ncard_empty, Nat.cast_zero, mul_zero, hd0, add_zero]
    rw [hsc0, diam_eq_zero.mpr (Or.inr hnt), Nat.cast_zero, mul_zero, zero_mul]

/-- **Extended social-cost bound in terms of equilibrium diameter** ([TardosWexler2007],
Lemma 19.4, p. 491): for every `0 ≤ α`, pure Nash equilibrium `s`, and profile `s'`,
`socialECost α s ≤ 3 * (formedGraph s).diam * socialECost α s'`. -/
theorem IsPureNash.socialECost_le_three_mul_diam_mul {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤ ((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞) * socialECost α s' := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    simp only [socialECost_def, univ_eq_empty, sum_empty, mul_zero, le_refl]
  · by_cases hnt : Nontrivial V
    · by_cases hc' : (formedGraph s').Connected
      · rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
          socialECost_eq_ofReal_of_connected hα₀ hc']
        have hcast : (((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞)) =
            ENNReal.ofReal (3 * ((formedGraph s).diam : ℝ)) := by
          rw [← ENNReal.ofReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
        rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hs.socialCost_le_three_mul_diam_mul hα₀ hc')
      · have hediam : (formedGraph s).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hs.connected
        have hd_ne : (formedGraph s).diam ≠ 0 := diam_ne_zero_of_ediam_ne_top hediam
        rw [socialECost_eq_top_iff.mpr hc', ENNReal.mul_top]
        · exact le_top
        · exact Nat.cast_ne_zero.mpr (by omega)
    · rw [not_nontrivial_iff_subsingleton] at hnt
      have h0 : socialECost α s = 0 := by
        rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
          hs.socialCost_eq_networkCost hα₀, networkCost_def]
        have he0 : (formedGraph s).edgeSet = ∅ := by
          ext ⟨a, b⟩
          simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]
          rw [Subsingleton.elim a b]
          exact (formedGraph s).loopless.irrefl b
        have hd0 : (∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ)) = 0 :=
          sum_eq_zero fun u _ => sum_eq_zero fun v _ => by
            rw [Subsingleton.elim u v, SimpleGraph.dist_self, Nat.cast_zero]
        rw [he0, Set.ncard_empty, Nat.cast_zero, mul_zero, hd0, add_zero, ENNReal.ofReal_zero]
      rw [h0]
      exact zero_le

/-! ### Theorem 19.5 and Theorem 19.6: Equilibrium diameter and Price of Anarchy -/

/-- Deviation profile in which player `x` adds an undirected link to `y`. -/
private def addLink (s : Profile V) (x y : V) : Profile V :=
  Function.update s x (LinkSet.ofFinset x (insert y (s x).neighbors))

omit [Fintype V] in
private theorem formedGraph_le_addLink (s : Profile V) (x y : V) :
    formedGraph s ≤ formedGraph (addLink s x y) := by
  intro a b hab
  have hab_ne : a ≠ b := hab.ne
  rw [formedGraph_adj] at hab ⊢
  simp only [addLink]
  by_cases hax : a = x
  · subst hax
    rw [Function.update_self, Function.update_of_ne hab_ne.symm]
    exact hab.elim
      (fun h => Or.inl (LinkSet.mem_ofFinset.mpr ⟨hab_ne.symm, mem_insert_of_mem h⟩)) Or.inr
  · by_cases hbx : b = x
    · subst hbx
      rw [Function.update_of_ne hax, Function.update_self]
      exact hab.elim Or.inl
        (fun h => Or.inr (LinkSet.mem_ofFinset.mpr ⟨hax, mem_insert_of_mem h⟩))
    · rw [Function.update_of_ne hax, Function.update_of_ne hbx]
      exact hab

omit [Fintype V] in
private theorem adj_addLink {s : Profile V} {x y : V} (hxy : x ≠ y) :
    (formedGraph (addLink s x y)).Adj x y := by
  rw [formedGraph_adj]
  left
  rw [addLink, Function.update_self, LinkSet.mem_ofFinset]
  exact ⟨hxy.symm, mem_insert_self y _⟩

/-- At any pure Nash equilibrium `s` (`0 ≤ α`), adding a single link `(x, y)` saves at most `α` in
total distance from `x` over any subset `S : Finset V` of targets. -/
private theorem sum_dist_sub_addLink_le {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) (x y : V) (S : Finset V) :
    ((∑ w ∈ S, ((formedGraph s).dist x w - (formedGraph (addLink s x y)).dist x w) : ℕ) : ℝ) ≤
      α := by
  have : Nonempty V := ⟨x⟩
  let G := formedGraph s
  let s' := addLink s x y
  let G' := formedGraph s'
  have hc : G.Connected := hs.connected
  have hle_G : G ≤ G' := formedGraph_le_addLink s x y
  have hc' : G'.Connected := hc.mono hle_G
  have hanti : ∀ w : V, G'.dist x w ≤ G.dist x w := fun w => (hc x w).dist_anti hle_G
  have hsub_all : (∑ w ∈ S, (G.dist x w - G'.dist x w)) ≤
      ∑ w : V, (G.dist x w - G'.dist x w) :=
    sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  have hsum_eq : (∑ w : V, (G.dist x w - G'.dist x w)) + ∑ w : V, G'.dist x w =
      ∑ w : V, G.dist x w := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun w _ => Nat.sub_add_cancel (hanti w)
  have hcard_le : ((s' x).neighbors.card : ℝ) ≤ ((s x).neighbors.card : ℝ) + 1 := by
    simp only [s', addLink, Function.update_self, LinkSet.neighbors_ofFinset]
    have h1 : #((insert y (s x).neighbors).erase x) ≤ #(insert y (s x).neighbors) := card_erase_le
    have h2 : #(insert y (s x).neighbors) ≤ (s x).neighbors.card + 1 := card_insert_le _ _
    exact_mod_cast h1.trans h2
  have hne : playerCost α s x ≤ playerCost α s' x := hs.playerCost_le hα₀ (hc' x)
  have hsum_eq_real : ((∑ w : V, (G.dist x w - G'.dist x w) : ℕ) : ℝ) +
      ∑ w : V, (G'.dist x w : ℝ) = ∑ w : V, (G.dist x w : ℝ) := by
    exact_mod_cast hsum_eq
  have hsub_real : ((∑ w ∈ S, (G.dist x w - G'.dist x w) : ℕ) : ℝ) ≤
      ((∑ w : V, (G.dist x w - G'.dist x w) : ℕ) : ℝ) := by
    exact_mod_cast hsub_all
  have hmul_card : α * ((s' x).neighbors.card : ℝ) ≤ α * ((s x).neighbors.card : ℝ) + α := by
    nlinarith
  rw [playerCost_def, playerCost_def] at hne
  linarith

private theorem exists_diam_pair_of_ne_zero {α : ℝ} {s : Profile V} (hs : IsPureNash α s)
    (hd_ne : (formedGraph s).diam ≠ 0) :
    (formedGraph s).Connected ∧
      ∃ u v : V, u ≠ v ∧ (formedGraph s).dist u v = (formedGraph s).diam := by
  have : Nontrivial V := (formedGraph s).nontrivial_of_diam_ne_zero hd_ne
  obtain ⟨u, v, huv_dist⟩ := (formedGraph s).exists_dist_eq_diam
  have huv : u ≠ v := fun h => by
    subst h
    rw [SimpleGraph.dist_self] at huv_dist
    exact hd_ne huv_dist.symm
  exact ⟨hs.connected, u, v, huv, huv_dist⟩

/-- **Sharp diameter bound `√(4α + 1)` at Nash equilibrium**
([FabrikantLuthraManevaPapadimitriouShenker2003]; [TardosWexler2007], Theorem 19.5,
p. 492): every pure Nash equilibrium for `0 ≤ α` has diameter at most `√(4α + 1)`. -/
theorem IsPureNash.diam_le_sqrt_four_mul_add_one {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) :
    ((formedGraph s).diam : ℝ) ≤ Real.sqrt (4 * α + 1) := by
  let G := formedGraph s
  let d := G.diam
  by_cases hd1 : d ≤ 1
  · calc (d : ℝ) ≤ 1 := by exact_mod_cast hd1
      _ = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (4 * α + 1) := Real.sqrt_le_sqrt (by linarith)
  · obtain ⟨hc, u, v, huv, huv_dist⟩ := exists_diam_pair_of_ne_zero hs (by change d ≠ 0; omega)
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
    have hp_d : p.length = d := hp.trans huv_dist
    let k := d / 2
    let target : ℕ → V := fun j => p.getVert (d - j)
    have hinj_on : ∀ i ∈ range k, ∀ j ∈ range k, target i = target j → i = j := by
      intro i hi j hj h_eq
      rw [mem_range] at hi hj
      have hd₁ := (dist_getVert_of_shortest hc p hp (m := d - i) (by omega)).1
      have hd₂ := (dist_getVert_of_shortest hc p hp (m := d - j) (by omega)).1
      change G.dist u (target i) = d - i at hd₁
      change G.dist u (target j) = d - j at hd₂
      rw [h_eq] at hd₁
      omega
    let G' := formedGraph (addLink s u v)
    have hle_G : G ≤ G' := formedGraph_le_addLink s u v
    have hc' : G'.Connected := hc.mono hle_G
    have hadj_uv : G'.Adj u v := adj_addLink huv
    have hsave_j : ∀ j ∈ range k,
        d - 1 - 2 * j ≤ G.dist u (target j) - G'.dist u (target j) := by
      intro j hj
      rw [mem_range] at hj
      obtain ⟨hdu, hdv⟩ := dist_getVert_of_shortest hc p hp (m := d - j) (by omega)
      have hG'_vw : G'.dist v (target j) ≤ j := by
        calc G'.dist v (target j)
            ≤ G.dist v (target j) := (hc v (target j)).dist_anti hle_G
          _ = G.dist (target j) v := dist_comm
          _ = p.length - (d - j) := hdv
          _ = j := by omega
      have hG'_uw : G'.dist u (target j) ≤ 1 + j := by
        calc G'.dist u (target j)
            ≤ G'.dist u v + G'.dist v (target j) := hc'.dist_triangle
          _ = 1 + G'.dist v (target j) := by rw [dist_eq_one_iff_adj.mpr hadj_uv]
          _ ≤ 1 + j := by omega
      change d - 1 - 2 * j ≤ G.dist u (p.getVert (d - j)) - G'.dist u (target j)
      rw [hdu]
      omega
    let S := (range k).image target
    have hsum_save : k * (d - k) ≤ ∑ w ∈ S, (G.dist u w - G'.dist u w) := by
      rw [sum_image hinj_on, ← sum_range_shortcut_savings k d (by omega)]
      exact sum_le_sum hsave_j
    have hsave_le_α : ((k * (d - k) : ℕ) : ℝ) ≤ α :=
      (Nat.cast_le.mpr hsum_save).trans (sum_dist_sub_addLink_le hα₀ hs u v S)
    have hd_sq_nat : d ^ 2 ≤ 4 * (k * (d - k)) + 1 := by
      rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
      · have hd0 : d = 2 * k := by omega
        have hdk0 : d - k = k := by omega
        rw [hdk0, hd0]; nlinarith
      · have hd1' : d = 2 * k + 1 := by omega
        have hdk1 : d - k = k + 1 := by omega
        rw [hdk1, hd1']; nlinarith
    have hd_sq : (d : ℝ) ^ 2 ≤ 4 * α + 1 := by
      have hcast : ((d ^ 2 : ℕ) : ℝ) ≤ ((4 * (k * (d - k)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hd_sq_nat
      push_cast at hcast hsave_le_α
      linarith
    rw [← Real.sqrt_sq (Nat.cast_nonneg d)]
    exact Real.sqrt_le_sqrt hd_sq

/-- **Diameter bound `2√α + 1` at Nash equilibrium**
([FabrikantLuthraManevaPapadimitriouShenker2003]; [TardosWexler2007], Theorem 19.5,
p. 492). -/
theorem IsPureNash.diam_le_two_mul_sqrt_add_one {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) :
    ((formedGraph s).diam : ℝ) ≤ 2 * Real.sqrt α + 1 := by
  calc ((formedGraph s).diam : ℝ)
      ≤ Real.sqrt (4 * α + 1) := hs.diam_le_sqrt_four_mul_add_one hα₀
    _ ≤ Real.sqrt ((2 * Real.sqrt α + 1) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα₀
      have hnn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
      nlinarith
    _ = 2 * Real.sqrt α + 1 := Real.sqrt_sq (by positivity)

/-- **`O(√α)` Price of Anarchy** ([FabrikantLuthraManevaPapadimitriouShenker2003];
[TardosWexler2007], Theorem 19.5, p. 492): for every `0 ≤ α`, pure Nash equilibrium `s`, and
profile `s'`, `socialECost α s ≤ (6√α + 3) * socialECost α s'`. -/
theorem IsPureNash.socialECost_le_six_mul_sqrt_add_three_mul {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤ ENNReal.ofReal (6 * Real.sqrt α + 3) * socialECost α s' := by
  have hd := hs.diam_le_two_mul_sqrt_add_one hα₀
  have h3d : (((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal (6 * Real.sqrt α + 3) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith
  calc socialECost α s
      ≤ ((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞) * socialECost α s' :=
        hs.socialECost_le_three_mul_diam_mul hα₀ s'
    _ ≤ ENNReal.ofReal (6 * Real.sqrt α + 3) * socialECost α s' := by gcongr

/-! ### Theorem 19.6: Diameter `≤ 4α / √n + 9` and `O(1 + α / √n)` Price of Anarchy -/

/-- **Diameter bound `4α / √n + 9` at Nash equilibrium**
([AlbersEiltsEvenDarMansourRoditty2006]; [TardosWexler2007], Theorem 19.6, pp. 493–494): every pure
Nash equilibrium for `0 ≤ α` on `n = Fintype.card V` players has diameter at most `4α / √n + 9`. -/
theorem IsPureNash.diam_le_four_mul_div_sqrt_card_add_nine {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) :
    ((formedGraph s).diam : ℝ) ≤ 4 * α / Real.sqrt (Fintype.card V) + 9 := by
  let G := formedGraph s
  let d := G.diam
  by_cases hd9 : d ≤ 9
  · have hd_real : (d : ℝ) ≤ 9 := by exact_mod_cast hd9
    have hdiv_nn : 0 ≤ 4 * α / Real.sqrt (Fintype.card V) := by positivity
    linarith
  · obtain ⟨hc, u, v, huv, huv_dist⟩ := exists_diam_pair_of_ne_zero hs (by change d ≠ 0; omega)
    have : Nonempty V := hc.nonempty
    let d' := (d - 1) / 4
    have hd'2 : 2 ≤ d' := by omega
    let B : Finset V := univ.filter fun w => G.dist u w ≤ d'
    have hu_in_B : u ∈ B :=
      mem_filter.mpr ⟨mem_univ u, by simp only [SimpleGraph.dist_self, zero_le]⟩
    have hB_pos : 1 ≤ #B := card_pos.mpr ⟨u, hu_in_B⟩
    let G_vu := formedGraph (addLink s v u)
    have hle_vu : G ≤ G_vu := formedGraph_le_addLink s v u
    have hc_vu : G_vu.Connected := hc.mono hle_vu
    have hadj_vu : G_vu.Adj v u := adj_addLink huv.symm
    have hsave_B : ∀ w ∈ B, d - 2 * d' - 1 ≤ G.dist v w - G_vu.dist v w := by
      intro w hw
      have hduw : G.dist u w ≤ d' := (mem_filter.mp hw).2
      have htri_G : G.dist v u ≤ G.dist v w + G.dist u w := by
        rw [dist_comm (u := u)]; exact hc.dist_triangle
      have hdvw_G : d - d' ≤ G.dist v w := by
        rw [SimpleGraph.dist_comm] at huv_dist
        change G.dist v u = d at huv_dist
        omega
      have hdvw_vu : G_vu.dist v w ≤ 1 + d' := by
        calc G_vu.dist v w
            ≤ G_vu.dist v u + G_vu.dist u w := hc_vu.dist_triangle
          _ = 1 + G_vu.dist u w := by rw [dist_eq_one_iff_adj.mpr hadj_vu]
          _ ≤ 1 + G.dist u w := Nat.add_le_add_left ((hc u w).dist_anti hle_vu) 1
          _ ≤ 1 + d' := by omega
      omega
    have hsum_B : #B * (d - 2 * d' - 1) ≤ ∑ w ∈ B, (G.dist v w - G_vu.dist v w) := by
      calc #B * (d - 2 * d' - 1)
          = ∑ _w ∈ B, (d - 2 * d' - 1) := by simp only [sum_const, smul_eq_mul]
        _ ≤ ∑ w ∈ B, (G.dist v w - G_vu.dist v w) := sum_le_sum hsave_B
    have hB_α_nat : ((#B * (d - 2 * d' - 1) : ℕ) : ℝ) ≤ α :=
      (Nat.cast_le.mpr hsum_B).trans (sum_dist_sub_addLink_le hα₀ hs v u B)
    have hd_sub_B : ((d : ℝ) - 1) * (#B : ℝ) ≤ 2 * α := by
      have hnat_ineq : (d - 1) ≤ 2 * (d - 2 * d' - 1) := by omega
      have hreal_ineq : ((d : ℝ) - 1) ≤ 2 * ((d - 2 * d' - 1 : ℕ) : ℝ) := by
        have hc1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
        rw [← hc1]; exact_mod_cast hnat_ineq
      have hB_nn : (0 : ℝ) ≤ (#B : ℝ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hreal_ineq hB_nn
      push_cast at hB_α_nat
      linarith
    let p_of : ∀ t : V, G.Walk u t := fun t => (hc.exists_walk_length_eq_dist u t).choose
    have hp_len : ∀ t : V, (p_of t).length = G.dist u t :=
      fun t => (hc.exists_walk_length_eq_dist u t).choose_spec
    let exitVert : V → V := fun t => (p_of t).getVert d'
    have hexit_prop : ∀ t ∈ Bᶜ,
        exitVert t ∈ B ∧ u ≠ exitVert t ∧ G.dist (exitVert t) t ≤ G.dist u t - d' := by
      intro t ht
      simp only [B, mem_compl, mem_filter, mem_univ, true_and, not_le] at ht
      have hm : d' ≤ (p_of t).length := by rw [hp_len t]; omega
      obtain ⟨hdu, hdt⟩ := dist_getVert_of_shortest hc (p_of t) (hp_len t) hm
      refine ⟨mem_filter.mpr ⟨mem_univ _, hdu.le⟩, ?_, ?_⟩
      · intro hueq
        change G.dist u (exitVert t) = d' at hdu
        rw [← hueq, SimpleGraph.dist_self] at hdu
        omega
      · rw [hp_len t] at hdt; exact hdt.le
    have hfiber_le : ∀ w ∈ B,
        ((d' - 1 : ℕ) : ℝ) * (#(Bᶜ.filter fun t => exitVert t = w) : ℝ) ≤ α := by
      intro w _
      let Aw := Bᶜ.filter fun t => exitVert t = w
      change ((d' - 1 : ℕ) : ℝ) * (#Aw : ℝ) ≤ α
      by_cases hAw : Aw = ∅
      · rw [hAw, card_empty, Nat.cast_zero, mul_zero]; exact hα₀
      · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hAw
        obtain ⟨ht₀_compl, htw₀⟩ := mem_filter.mp ht₀
        have huw : u ≠ w := htw₀ ▸ (hexit_prop t₀ ht₀_compl).2.1
        let G_uw := formedGraph (addLink s u w)
        have hle_uw : G ≤ G_uw := formedGraph_le_addLink s u w
        have hc_uw : G_uw.Connected := hc.mono hle_uw
        have hadj_uw : G_uw.Adj u w := adj_addLink huw
        have hsave_Aw : ∀ t ∈ Aw, d' - 1 ≤ G.dist u t - G_uw.dist u t := by
          intro t ht
          obtain ⟨ht_compl, htw⟩ := mem_filter.mp ht
          have hgt : d' < G.dist u t := by
            have htc := ht_compl
            simp only [B, mem_compl, mem_filter, mem_univ, true_and, not_le] at htc
            exact htc
          have hwt : G.dist w t ≤ G.dist u t - d' := htw ▸ (hexit_prop t ht_compl).2.2
          have hduw_t : G_uw.dist u t ≤ 1 + (G.dist u t - d') := by
            calc G_uw.dist u t
                ≤ G_uw.dist u w + G_uw.dist w t := hc_uw.dist_triangle
              _ = 1 + G_uw.dist w t := by rw [dist_eq_one_iff_adj.mpr hadj_uw]
              _ ≤ 1 + G.dist w t := Nat.add_le_add_left ((hc w t).dist_anti hle_uw) 1
              _ ≤ 1 + (G.dist u t - d') := by omega
          omega
        have hsum_Aw : #Aw * (d' - 1) ≤ ∑ t ∈ Aw, (G.dist u t - G_uw.dist u t) := by
          calc #Aw * (d' - 1)
              = ∑ _t ∈ Aw, (d' - 1) := by simp only [sum_const, smul_eq_mul]
            _ ≤ ∑ t ∈ Aw, (G.dist u t - G_uw.dist u t) := sum_le_sum hsave_Aw
        have hAw_α : ((#Aw * (d' - 1) : ℕ) : ℝ) ≤ α :=
          (Nat.cast_le.mpr hsum_Aw).trans (sum_dist_sub_addLink_le hα₀ hs u w Aw)
        push_cast at hAw_α
        linarith
    have hsum_fibers : (∑ w ∈ B, #(Bᶜ.filter fun t => exitVert t = w)) = #Bᶜ :=
      (card_eq_sum_card_fiberwise fun t ht => (hexit_prop t ht).1).symm
    have hcompl_ineq : ((d' - 1 : ℕ) : ℝ) * (#Bᶜ : ℝ) ≤ α * (#B : ℝ) := by
      calc ((d' - 1 : ℕ) : ℝ) * (#Bᶜ : ℝ)
          = ((d' - 1 : ℕ) : ℝ) * ∑ w ∈ B, (#(Bᶜ.filter fun t => exitVert t = w) : ℝ) := by
            rw [← hsum_fibers, Nat.cast_sum]
        _ = ∑ w ∈ B, ((d' - 1 : ℕ) : ℝ) * (#(Bᶜ.filter fun t => exitVert t = w) : ℝ) :=
            mul_sum _ _ _
        _ ≤ ∑ _w ∈ B, α := sum_le_sum hfiber_le
        _ = α * (#B : ℝ) := by simp only [sum_const, nsmul_eq_mul]; ring
    have hcard_split : (#B : ℝ) + (#Bᶜ : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast card_add_card_compl B
    have hd'_sub1_pos : (1 : ℝ) ≤ ((d' - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d' - 1)
    have hB_pos_real : (1 : ℝ) ≤ (#B : ℝ) := by exact_mod_cast hB_pos
    have h4_le_d : 4 * ((d' - 1 : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
      have : 4 * (d' - 1) ≤ d - 1 := by omega
      have hc1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      rw [← hc1]; exact_mod_cast this
    have hd'_lt_α : ((d' - 1 : ℕ) : ℝ) ≤ α := by nlinarith
    have hn_le_2αB : ((d' - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ≤ 2 * α * (#B : ℝ) := by
      nlinarith
    have hsq_ineq : (Fintype.card V : ℝ) * ((d' - 1 : ℕ) : ℝ) ^ 2 ≤ α ^ 2 := by
      have hstep1 : ((d : ℝ) - 1) * (((d' - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ)) ≤
          ((d : ℝ) - 1) * (2 * α * (#B : ℝ)) :=
        mul_le_mul_of_nonneg_left hn_le_2αB (by linarith)
      have hstep2 : 4 * ((d' - 1 : ℕ) : ℝ) * (((d' - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ)) ≤
          ((d : ℝ) - 1) * (((d' - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ)) :=
        mul_le_mul_of_nonneg_right h4_le_d (by positivity)
      nlinarith
    have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
    have hsqrt_pos : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr hn_pos
    have hd'1_le : ((d' - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card V) ≤ α := by
      have h1 : (((d' - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card V)) ^ 2 ≤ α ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn_pos.le]; linarith
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ((d' - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card V)),
        ← Real.sqrt_sq hα₀]
      exact Real.sqrt_le_sqrt h1
    have hd'1_div : ((d' - 1 : ℕ) : ℝ) ≤ α / Real.sqrt (Fintype.card V) :=
      (le_div_iff₀ hsqrt_pos).mpr hd'1_le
    have hd_le_4d' : (d : ℝ) ≤ 4 * ((d' - 1 : ℕ) : ℝ) + 8 := by
      have hdiv : d ≤ 4 * (d' - 1) + 8 := by omega
      have hcast : (d : ℝ) ≤ ((4 * (d' - 1) + 8 : ℕ) : ℝ) := by exact_mod_cast hdiv
      push_cast at hcast; linarith
    change (d : ℝ) ≤ 4 * α / Real.sqrt (Fintype.card V) + 9
    rw [mul_div_assoc]
    linarith

/-- **`O(1 + α / √n)` Price of Anarchy** ([AlbersEiltsEvenDarMansourRoditty2006];
[TardosWexler2007], Theorem 19.6, pp. 493–494): every pure Nash equilibrium `s` for `0 ≤ α` on
`n = Fintype.card V` players has `socialECost α s ≤ (12α / √n + 27) * socialECost α s'`. -/
theorem IsPureNash.socialECost_le_twelve_mul_div_sqrt_card_add_twenty_seven_mul {α : ℝ}
    (hα₀ : 0 ≤ α) {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤
      ENNReal.ofReal (12 * α / Real.sqrt (Fintype.card V) + 27) * socialECost α s' := by
  have hd := hs.diam_le_four_mul_div_sqrt_card_add_nine hα₀
  have h3d : (((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (12 * α / Real.sqrt (Fintype.card V) + 27) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    have h3 : 12 * α / Real.sqrt (Fintype.card V) + 27 =
        3 * (4 * α / Real.sqrt (Fintype.card V) + 9) := by ring
    rw [h3]
    linarith
  calc socialECost α s
      ≤ ((3 * (formedGraph s).diam : ℕ) : ℝ≥0∞) * socialECost α s' :=
        hs.socialECost_le_three_mul_diam_mul hα₀ s'
    _ ≤ ENNReal.ofReal (12 * α / Real.sqrt (Fintype.card V) + 27) * socialECost α s' := by gcongr

end PureNash

end Cslib.GameTheory.LocalConnection
