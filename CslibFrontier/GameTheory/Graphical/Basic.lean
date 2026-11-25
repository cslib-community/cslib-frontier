/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Strategic.Correlated
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graphical games

A *graphical game* ([Kearns2007], Definition 7.1, p. 162) on a set of players `ι` with strategy
sets `S : ι → Type*` consists of an undirected interaction graph `G : SimpleGraph ι` together with
a local payoff table `localPayoff i : (∀ j : ClosedNeighborhood G i, S j.1) → ℝ` for each player
`i`. Player `i`'s payoff at a global action profile `s : ∀ k, S k` depends only on the actions of
`i` and its neighbors in `G` (`payoff_congr`). Kearns states Definition 7.1 for binary actions
`{0, 1}` while noting (§7.2, p. 161) that all basic notions extend directly to general finite
action sets; this module works over arbitrary `S : ι → Type*`.

Negating payoffs embeds any graphical game into `Cslib.GameTheory.CostGame` (`toCostGame`), just as
`BimatrixGame.toCostGame` embeds two-player payoff games. Conversely, a normal-form `CostGame`
arises from a graphical game on `G` if and only if each player's cost is invariant under changes
outside its closed neighborhood (`CostGame.isGraphicalOn_iff_exists_graphicalGame`); in particular,
every normal-form game is represented by a graphical game on the complete graph `⊤`
(`ofCostGameComplete`, [Kearns2007], §7.2 Remarks, p. 162).

On finite player and action sets, the domain of `localPayoff` has `tableEntries M` entries, equal
to `∑ i, ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j)` (`tableEntries_eq_sum_prod`)
and bounded by `Fintype.card ι * m ^ (d + 1)` when `Fintype.card (S i) ≤ m` and
`M.graph.degree i ≤ d` (`tableEntries_le_card_mul_pow`), compared with
`CostGame.normalFormEntries ι (fun _ => α) = Fintype.card ι * (Fintype.card α) ^ Fintype.card ι`
for normal form (`tableEntries_lt_normalFormEntries` when `M.graph ≠ ⊤` and
`2 ≤ Fintype.card (S i)`).

Under independent mixed strategies `p : ∀ i, S i → ℝ`, marginalizing out players outside the
neighborhood reduces `expectedPayoff` and `deviationPayoff` to sums over `ClosedNeighborhood` and
`neighborSet` (`expectedPayoff_eq_localSum`, `deviationPayoff_eq_localDeviationPayoff`).
Consequently, whether a mixed strategy `x : S i → ℝ` is an `ε`-best response for player `i` depends
only on the mixed strategies of `M.graph.neighborSet i` (`IsApproxBestResponse`,
`isApproxNash_iff_local`). For general joint distributions ([Kearns2007], §7.4.1,
Definitions 7.7–7.8 and Lemmas 7.9–7.10, pp. 170–171), local neighborhood equivalence
`LocalNeighborhoodEquiv` strictly refines expected payoff equivalence `ExpectedPayoffEquiv` and
preserves correlated equilibria.

## Main definitions

* `Cslib.GameTheory.ClosedNeighborhood`: the subtype `{j : ι // j = i ∨ G.Adj i j}` representing
  Kearns's closed neighborhood `N_G(i)`.
* `Cslib.GameTheory.GraphicalGame`: a graphical game `(G, M)` with local payoff tables over
  `ClosedNeighborhood`.
* `Cslib.GameTheory.GraphicalGame.payoff`: player `i`'s payoff at a global action profile.
* `Cslib.GameTheory.GraphicalGame.toCostGame`: normal-form `CostGame` with negated payoffs.
* `Cslib.GameTheory.CostGame.IsGraphicalOn`: locality condition characterizing normal-form cost
  games representable on `G`.
* `Cslib.GameTheory.GraphicalGame.ofCostGameComplete`: representation of any `CostGame` as a
  graphical game on the complete graph `⊤`.
* `Cslib.GameTheory.GraphicalGame.tableEntries`, `Cslib.GameTheory.CostGame.normalFormEntries`:
  exact scalar entry counts of the graphical and normal-form payoff tables.
* `Cslib.GameTheory.GraphicalGame.expectedPayoff`, `Cslib.GameTheory.GraphicalGame.deviationPayoff`,
  `Cslib.GameTheory.GraphicalGame.localDeviationPayoff`: global and neighborhood-local expected
  payoffs under mixed strategy profiles.
* `Cslib.GameTheory.GraphicalGame.IsApproxNash`,
  `Cslib.GameTheory.GraphicalGame.IsApproxBestResponse`,
  `Cslib.GameTheory.GraphicalGame.IsBestResponse`: global `ε`-Nash equilibrium ([Kearns2007], §7.2,
  p. 162) and purely local `ε`-best-response / exact best-response predicates.
* `Cslib.GameTheory.GraphicalGame.ExpectedPayoffEquiv`,
  `Cslib.GameTheory.LocalNeighborhoodEquiv`: expected payoff equivalence and local neighborhood
  equivalence of joint distributions ([Kearns2007], Definitions 7.7–7.8, pp. 170–171).

## Main results

* `Cslib.GameTheory.GraphicalGame.payoff_congr`: local neighborhood payoff invariance.
* `Cslib.GameTheory.CostGame.isGraphicalOn_iff_exists_graphicalGame`: exact characterization of
  normal-form games induced by graphical games on `G`.
* `Cslib.GameTheory.GraphicalGame.toCostGame_ofCostGameComplete`: complete-graph universality.
* `Cslib.GameTheory.GraphicalGame.tableEntries_eq_sum_prod`,
  `Cslib.GameTheory.GraphicalGame.tableEntries_le_card_mul_pow`,
  `Cslib.GameTheory.GraphicalGame.tableEntries_lt_normalFormEntries`: succinct parameter-count
  identities and strict advantage over normal form when `G ≠ ⊤`.
* `Cslib.GameTheory.GraphicalGame.expectedPayoff_eq_localSum`,
  `Cslib.GameTheory.GraphicalGame.deviationPayoff_eq_localDeviationPayoff`: local marginalization of
  expected payoffs under product distributions.
* `Cslib.GameTheory.GraphicalGame.isApproxNash_zero_iff`,
  `Cslib.GameTheory.GraphicalGame.isApproxNash_iff_mixed`,
  `Cslib.GameTheory.GraphicalGame.isApproxNash_iff_local`,
  `Cslib.GameTheory.GraphicalGame.isMixedNash_toCostGame_iff_local`: equivalence between global
  equilibrium, mixed unilateral deviations, and local neighbor best responses.
* `Cslib.GameTheory.LocalNeighborhoodEquiv.expectedPayoffEquiv`,
  `Cslib.GameTheory.exists_graphicalGame_not_expectedPayoffEquiv`,
  `Cslib.GameTheory.LocalNeighborhoodEquiv.isCorrelatedEquilibrium_iff`: [Kearns2007], Lemmas 7.9
  and 7.10 (p. 171).

## References

* [M. Kearns, *Graphical Games*, Chapter 7 of *Algorithmic Game Theory*][Kearns2007]
-/

public section

namespace Cslib.GameTheory

open Finset Function

/-- The closed neighborhood `N_G(i) = {i} ∪ Γ_G(i)` of vertex `i` in `G` ([Kearns2007], §7.2,
p. 162), as a subtype. -/
abbrev ClosedNeighborhood {ι : Type*} (G : SimpleGraph ι) (i : ι) : Type _ :=
  {j : ι // j = i ∨ G.Adj i j}

/-- A **graphical game** ([Kearns2007], Definition 7.1, p. 162) over player type `ι` and strategy
sets `S : ι → Type*`: an undirected graph `graph` together with a local payoff function
`localPayoff i` for each player `i` depending only on actions in `ClosedNeighborhood graph i`. -/
structure GraphicalGame (ι : Type*) (S : ι → Type*) where
  /-- The undirected interaction graph `G` over the players. -/
  graph : SimpleGraph ι
  /-- Local payoff table `M_i(a^i)` for player `i` on closed-neighborhood action profiles. -/
  localPayoff : ∀ i : ι, (∀ j : ClosedNeighborhood graph i, S j.1) → ℝ

namespace CostGame

variable {ι : Type*} {S : ι → Type*}

/-- A normal-form cost game `C` is **graphical on `G`** if each player's cost depends only on the
actions of its closed neighborhood in `G`. -/
@[expose] def IsGraphicalOn (G : SimpleGraph ι) (C : CostGame ι S) : Prop :=
  ∀ i (s₁ s₂ : ∀ k, S k), (∀ j, (j = i ∨ G.Adj i j) → s₁ j = s₂ j) → C.cost i s₁ = C.cost i s₂

/-- Number of scalar payoff entries in the normal-form table `ι → (∀ i, S i) → ℝ`. -/
def normalFormEntries (ι : Type*) (S : ι → Type*) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (S i)] : ℕ :=
  Fintype.card (ι × (∀ i, S i))

theorem normalFormEntries_eq (ι : Type*) (S : ι → Type*) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (S i)] :
    normalFormEntries ι S = Fintype.card ι * ∏ i : ι, Fintype.card (S i) := by
  rw [normalFormEntries, Fintype.card_prod, Fintype.card_pi]

theorem normalFormEntries_const (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α] :
    normalFormEntries ι (fun _ => α) = Fintype.card ι * (Fintype.card α) ^ Fintype.card ι := by
  rw [normalFormEntries_eq, prod_const, card_univ]

end CostGame

namespace GraphicalGame

section Basic

variable {ι : Type*} {S : ι → Type*} (M : GraphicalGame ι S)

/-- Restrict a global pure action profile `s` to player `i`'s closed neighborhood `N_G(i)`
(`a^i` in [Kearns2007], §7.2, p. 162). -/
def restrictNeighborhood (i : ι) (s : ∀ k, S k) : ∀ j : ClosedNeighborhood M.graph i, S j.1 :=
  fun j => s j.1

@[simp] theorem restrictNeighborhood_apply (i : ι) (s : ∀ k, S k)
    (j : ClosedNeighborhood M.graph i) :
    M.restrictNeighborhood i s j = s j.1 := by
  rw [restrictNeighborhood]

/-- Player `i`'s payoff at a global action profile `s`, evaluated from `M.localPayoff i`. -/
def payoff (i : ι) (s : ∀ k, S k) : ℝ :=
  M.localPayoff i (M.restrictNeighborhood i s)

@[simp] theorem payoff_eq_localPayoff (i : ι) (s : ∀ k, S k) :
    M.payoff i s = M.localPayoff i (fun j => s j.1) := by
  unfold payoff restrictNeighborhood
  rfl

/-- **Local neighborhood payoff invariance** ([Kearns2007], Definition 7.1, p. 162): player `i`'s
payoff depends only on the actions of `i` and its neighbors in `M.graph`. -/
theorem payoff_congr {i : ι} {s₁ s₂ : ∀ k, S k}
    (h : ∀ j, (j = i ∨ M.graph.Adj i j) → s₁ j = s₂ j) :
    M.payoff i s₁ = M.payoff i s₂ := by
  simp only [payoff_eq_localPayoff]
  congr 1
  ext j
  exact h j.1 j.2

/-- Changing the action of a non-neighbor `k` (`k ≠ i` and `¬ M.graph.Adj i k`) leaves player `i`'s
payoff unchanged. -/
theorem payoff_update_of_not_adj [DecidableEq ι] {i k : ι} (hne : k ≠ i)
    (hnadj : ¬ M.graph.Adj i k) (s : ∀ j, S j) (a : S k) :
    M.payoff i (update s k a) = M.payoff i s :=
  M.payoff_congr fun j hj => update_of_ne (by rintro rfl; exact hj.elim hne hnadj) a s

/-- The normal-form cost-minimization game induced by a graphical game, with costs equal to negated
payoffs (`cost i s = - M.payoff i s`, matching `BimatrixGame.toCostGame`). -/
def toCostGame : CostGame ι S where
  cost i s := -M.payoff i s

@[simp] theorem toCostGame_cost (i : ι) (s : ∀ k, S k) :
    M.toCostGame.cost i s = -M.payoff i s := by
  rw [toCostGame]

theorem toCostGame_isGraphicalOn : M.toCostGame.IsGraphicalOn M.graph :=
  fun i _ _ h => by
    rw [toCostGame_cost, toCostGame_cost]
    exact congrArg Neg.neg (M.payoff_congr h)

/-- Represent any normal-form `CostGame` as a graphical game on the complete graph `⊤`
([Kearns2007], §7.2 Remarks, p. 162). -/
def ofCostGameComplete (C : CostGame ι S) : GraphicalGame ι S where
  graph := ⊤
  localPayoff i u := -C.cost i fun k => u ⟨k, by
    by_cases h : k = i
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.top_adj i k).2 (Ne.symm h))⟩

@[simp] theorem graph_ofCostGameComplete (C : CostGame ι S) :
    (ofCostGameComplete C).graph = ⊤ := by
  rw [ofCostGameComplete]

@[simp] theorem toCostGame_ofCostGameComplete (C : CostGame ι S) :
    (ofCostGameComplete C).toCostGame = C := by
  cases C with
  | mk cost =>
    refine congrArg CostGame.mk (funext fun i => funext fun s => ?_)
    simp [ofCostGameComplete, payoff, restrictNeighborhood]

end Basic

/-- **Normal-form locality characterization**: a `CostGame` with nonempty strategy sets is induced
by a graphical game with interaction graph `G` if and only if it satisfies
`CostGame.IsGraphicalOn G`. -/
theorem _root_.Cslib.GameTheory.CostGame.isGraphicalOn_iff_exists_graphicalGame
    {ι : Type*} {S : ι → Type*} [∀ k, Nonempty (S k)] {G : SimpleGraph ι} {C : CostGame ι S} :
    C.IsGraphicalOn G ↔ ∃ M : GraphicalGame ι S, M.graph = G ∧ M.toCostGame = C := by
  classical
  refine ⟨fun hC => ?_, ?_⟩
  · refine ⟨{
      graph := G
      localPayoff := fun i u =>
        -C.cost i fun k => if hk : k = i ∨ G.Adj i k then u ⟨k, hk⟩ else Classical.arbitrary (S k)
    }, rfl, ?_⟩
    cases C with
    | mk cost =>
      refine congrArg CostGame.mk (funext fun i => funext fun s => ?_)
      simp only [payoff_eq_localPayoff, neg_neg]
      exact hC i _ s fun j hj => by simp [hj]
  · rintro ⟨M, rfl, rfl⟩
    exact M.toCostGame_isGraphicalOn

section RepresentationSize

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]

/-- Total number of scalar entries across all local payoff tables `M.localPayoff`
([Kearns2007], §7.2 Remarks, p. 162). -/
def tableEntries (M : GraphicalGame ι S) [DecidableRel M.graph.Adj] : ℕ :=
  Fintype.card (Σ i : ι, ∀ j : ClosedNeighborhood M.graph i, S j.1)

/-- `ClosedNeighborhood M.graph i` is canonically equivalent to the finite set
`insert i (M.graph.neighborFinset i)`. -/
private def closedNeighborhoodEquiv (M : GraphicalGame ι S) [DecidableRel M.graph.Adj] (i : ι) :
    ClosedNeighborhood M.graph i ≃ {j : ι // j ∈ insert i (M.graph.neighborFinset i)} where
  toFun j := ⟨j.1, Finset.mem_insert.2 (j.2.imp id (M.graph.mem_neighborFinset i j.1).2)⟩
  invFun j := ⟨j.1, (Finset.mem_insert.1 j.2).imp id (M.graph.mem_neighborFinset i j.1).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact parameter count of a graphical game: `∑ i, ∏ j ∈ N_G(i), |S j|`. -/
theorem tableEntries_eq_sum_prod (M : GraphicalGame ι S) [DecidableRel M.graph.Adj] :
    M.tableEntries = ∑ i : ι, ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j) := by
  rw [tableEntries, Fintype.card_sigma]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.card_pi, ← Finset.prod_coe_sort (insert i (M.graph.neighborFinset i))]
  exact Fintype.prod_equiv (M.closedNeighborhoodEquiv i) _ _ fun _ => rfl

/-- **Succinct representation bound** ([Kearns2007], §7.2 Remarks, p. 162): if every player has at
most `m` pure strategies and degree at most `d` in `M.graph`, then `M` stores at most
`|ι| * m ^ (d + 1)` scalar payoff entries (exponential only in `d + 1`, linear in `|ι|`). -/
theorem tableEntries_le_card_mul_pow (M : GraphicalGame ι S) [DecidableRel M.graph.Adj]
    {m d : ℕ} (hm : ∀ i, Fintype.card (S i) ≤ m) (hd : ∀ i, M.graph.degree i ≤ d) :
    M.tableEntries ≤ Fintype.card ι * m ^ (d + 1) := by
  rw [M.tableEntries_eq_sum_prod]
  have hterm : ∀ i ∈ (univ : Finset ι),
      ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j) ≤ m ^ (d + 1) := by
    intro i _
    have hcard : (insert i (M.graph.neighborFinset i)).card ≤ d + 1 := by
      rw [Finset.card_insert_of_notMem (M.graph.notMem_neighborFinset_self i),
        M.graph.card_neighborFinset_eq_degree]
      exact Nat.add_le_add_right (hd i) 1
    rcases m.eq_zero_or_pos with rfl | hm_pos
    · have hi : Fintype.card (S i) = 0 := Nat.eq_zero_of_le_zero (hm i)
      rw [Finset.prod_eq_zero (Finset.mem_insert_self i _) hi]
      exact Nat.zero_le _
    · calc ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j)
          ≤ ∏ _j ∈ insert i (M.graph.neighborFinset i), m :=
            Finset.prod_le_prod fun j _ => hm j
        _ = m ^ (insert i (M.graph.neighborFinset i)).card := by
            rw [Finset.prod_const]
        _ ≤ m ^ (d + 1) := Nat.pow_le_pow_right hm_pos hcard
  calc ∑ i : ι, ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j)
      ≤ ∑ _i : ι, m ^ (d + 1) := Finset.sum_le_sum hterm
    _ = Fintype.card ι * m ^ (d + 1) := by rw [Finset.sum_const, card_univ, smul_eq_mul]

/-- On the complete graph `⊤`, `tableEntries` equals `CostGame.normalFormEntries`. -/
theorem tableEntries_of_graph_eq_top (M : GraphicalGame ι S) [DecidableRel M.graph.Adj]
    (htop : M.graph = ⊤) :
    M.tableEntries = CostGame.normalFormEntries ι S := by
  rw [M.tableEntries_eq_sum_prod, CostGame.normalFormEntries_eq]
  have hins : ∀ i : ι, insert i (M.graph.neighborFinset i) = univ := fun i => by
    ext j
    simp only [Finset.mem_insert, M.graph.mem_neighborFinset, htop, SimpleGraph.top_adj,
      Finset.mem_univ, iff_true]
    exact eq_or_ne j i |>.imp id Ne.symm
  simp only [hins, Finset.sum_const, card_univ, smul_eq_mul]

/-- Whenever `M.graph ≠ ⊤` and every player has at least `2` actions, the graphical game stores
strictly fewer entries than the normal-form representation ([Kearns2007], §7.2 Remarks, p. 162). -/
theorem tableEntries_lt_normalFormEntries (M : GraphicalGame ι S) [DecidableRel M.graph.Adj]
    (hntop : M.graph ≠ ⊤) (hcard : ∀ i, 2 ≤ Fintype.card (S i)) :
    M.tableEntries < CostGame.normalFormEntries ι S := by
  rw [M.tableEntries_eq_sum_prod, CostGame.normalFormEntries_eq]
  obtain ⟨i₀, k₀, hne, hnadj⟩ : ∃ i k : ι, i ≠ k ∧ ¬ M.graph.Adj i k := by
    by_contra hall
    push Not at hall
    apply hntop
    ext i k
    simpa only [SimpleGraph.top_adj] using ⟨M.graph.ne_of_adj, hall i k⟩
  have hk_not : k₀ ∉ insert i₀ (M.graph.neighborFinset i₀) := by
    simp [M.graph.mem_neighborFinset, hne.symm, hnadj]
  have hpos : 0 < ∏ j ∈ insert i₀ (M.graph.neighborFinset i₀), Fintype.card (S j) :=
    Finset.prod_pos fun j _ => by have := hcard j; omega
  have hlt : ∏ j ∈ insert i₀ (M.graph.neighborFinset i₀), Fintype.card (S j) <
      ∏ j : ι, Fintype.card (S j) :=
    calc ∏ j ∈ insert i₀ (M.graph.neighborFinset i₀), Fintype.card (S j)
        < ∏ j ∈ insert k₀ (insert i₀ (M.graph.neighborFinset i₀)), Fintype.card (S j) := by
          rw [Finset.prod_insert hk_not]
          exact lt_mul_of_one_lt_left hpos (by have := hcard k₀; omega)
      _ ≤ ∏ j : ι, Fintype.card (S j) :=
          Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) fun j _ _ => by
            have := hcard j
            omega
  have hle : ∀ i ∈ (univ : Finset ι),
      ∏ j ∈ insert i (M.graph.neighborFinset i), Fintype.card (S j) ≤
        ∏ j : ι, Fintype.card (S j) := fun i _ =>
    Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) fun j _ _ => by
      have := hcard j
      omega
  simpa only [Finset.sum_const, card_univ, smul_eq_mul] using
    Finset.sum_lt_sum hle ⟨i₀, mem_univ i₀, hlt⟩

end RepresentationSize

section MixedExpectation

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  (M : GraphicalGame ι S)

/-- Marginalization of a product distribution over coordinates outside `{j : ι // P j}`: if `f`
depends only on `{j // P j}` and every coordinate outside `P` has total weight `1`, then
`∑ s, productWeight p s * f (restrict s)` reduces to the product sum on `{j // P j}`. -/
theorem sum_productWeight_mul_restrict (P : ι → Prop) [DecidablePred P]
    {p : ∀ i, S i → ℝ} (hp : ∀ j, ¬ P j → ∑ a, p j a = 1)
    (f : (∀ j : {j : ι // P j}, S j.1) → ℝ) :
    ∑ s : (∀ i, S i), productWeight p s * f (fun j => s j.1) =
      ∑ u : (∀ j : {j : ι // P j}, S j.1), (∏ j : {j : ι // P j}, p j.1 (u j)) * f u := by
  let e := (Equiv.piEquivPiSubtypeProd P S).symm
  have hprod (u : ∀ j : {j // P j}, S j.1) (v : ∀ j : {j // ¬ P j}, S j.1) :
      productWeight p (e (u, v)) =
        (∏ j : {j // P j}, p j.1 (u j)) * (∏ j : {j // ¬ P j}, p j.1 (v j)) := by
    rw [productWeight_def,
      ← Finset.prod_filter_mul_prod_filter_not univ P (fun j => p j (e (u, v) j)),
      Finset.prod_subtype (univ.filter P) (p := P) (fun _ => mem_filter_univ _)
        (fun j => p j (e (u, v) j)),
      Finset.prod_subtype (univ.filter fun j => ¬ P j) (p := fun j => ¬ P j)
        (fun _ => mem_filter_univ _) (fun j => p j (e (u, v) j))]
    exact congrArg₂ (· * ·)
      (prod_congr rfl fun j _ => by simp [e, Equiv.piEquivPiSubtypeProd, j.2])
      (prod_congr rfl fun j _ => by simp [e, Equiv.piEquivPiSubtypeProd, j.2])
  have hrest : ∑ v : (∀ j : {j // ¬ P j}, S j.1), ∏ j : {j // ¬ P j}, p j.1 (v j) = 1 := by
    rw [← Fintype.prod_sum (fun j : {j // ¬ P j} => p j.1)]
    exact prod_eq_one fun j _ => hp j.1 j.2
  rw [← Fintype.sum_equiv e _ (fun s => productWeight p s * f (fun j => s j.1)) fun _ => rfl,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  have hu (v : ∀ j : {j // ¬ P j}, S j.1) :
      productWeight p (e (u, v)) * f (fun j => e (u, v) j.1) =
        ((∏ j : {j // P j}, p j.1 (u j)) * f u) * ∏ j : {j // ¬ P j}, p j.1 (v j) := by
    have hrestrict : (fun j : {j // P j} => e (u, v) j.1) = u := by
      ext j
      simp [e, Equiv.piEquivPiSubtypeProd, j.2]
    rw [hprod u v, hrestrict]
    ring
  simp only [hu, ← Finset.mul_sum, hrest, mul_one]

/-- Expected payoff `M_i(p) = E_{s ∼ p}[M.payoff i s]` of player `i` under independent mixed
strategies `p` ([Kearns2007], §7.2, p. 162). -/
def expectedPayoff (p : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ s, productWeight p s * M.payoff i s

theorem expectedPayoff_def (p : ∀ i, S i → ℝ) (i : ι) :
    M.expectedPayoff p i = ∑ s, productWeight p s * M.payoff i s := by
  rw [expectedPayoff]

@[simp] theorem toCostGame_expectedCost (p : ∀ i, S i → ℝ) (i : ι) :
    M.toCostGame.expectedCost p i = -M.expectedPayoff p i := by
  simp only [CostGame.expectedCost_def, expectedPayoff_def, toCostGame_cost, mul_neg,
    sum_neg_distrib]

/-- Expected payoff of player `i` when `i` plays pure strategy `a` and all other players draw
independently from `p`. -/
def deviationPayoff (p : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  ∑ s, productWeight p s * M.payoff i (update s i a)

theorem deviationPayoff_def (p : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    M.deviationPayoff p i a = ∑ s, productWeight p s * M.payoff i (update s i a) := by
  rw [deviationPayoff]

@[simp] theorem toCostGame_deviationCost (p : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    M.toCostGame.deviationCost p i a = -M.deviationPayoff p i a := by
  simp only [CostGame.deviationCost_def, deviationPayoff_def, toCostGame_cost, mul_neg,
    sum_neg_distrib]

theorem sum_mul_deviationPayoff_eq_expectedPayoff (p : ∀ i, S i → ℝ) {i : ι}
    (hp : ∑ a, p i a = 1) :
    ∑ a, p i a * M.deviationPayoff p i a = M.expectedPayoff p i := by
  have h := M.toCostGame.sum_mul_deviationCost_eq_expectedCost p hp
  simp only [toCostGame_deviationCost, toCostGame_expectedCost, mul_neg, sum_neg_distrib] at h
  linarith

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- Player `i`'s payoff when `i` plays pure action `a` and its neighbors `j ∈ M.graph.neighborSet i`
play `u j`. -/
def localNeighborPayoff (i : ι) (a : S i) (u : ∀ j : M.graph.neighborSet i, S j.1) : ℝ :=
  M.localPayoff i fun j =>
    if h : j.1 = i then cast (congrArg S h.symm) a else u ⟨j.1, j.2.resolve_left h⟩

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem localNeighborPayoff_def (i : ι) (a : S i) (u : ∀ j : M.graph.neighborSet i, S j.1) :
    M.localNeighborPayoff i a u =
      M.localPayoff i fun j =>
        if h : j.1 = i then cast (congrArg S h.symm) a else u ⟨j.1, j.2.resolve_left h⟩ := by
  rw [localNeighborPayoff]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem payoff_update_eq_localNeighborPayoff (i : ι) (a : S i) (s : ∀ k, S k) :
    M.payoff i (update s i a) = M.localNeighborPayoff i a (fun j => s j.1) := by
  rw [payoff_eq_localPayoff, localNeighborPayoff]
  congr 1
  ext ⟨j, hj⟩
  rcases eq_or_ne j i with rfl | hji <;> simp [*]

/-- Purely local expected payoff of player `i` playing pure action `a` when its neighbors in
`M.graph` use mixed strategies `nbr`. -/
noncomputable def localDeviationPayoff (i : ι) (a : S i)
    (nbr : ∀ j : M.graph.neighborSet i, S j.1 → ℝ) : ℝ := by
  classical
  exact ∑ u : (∀ j : M.graph.neighborSet i, S j.1),
    (∏ j : M.graph.neighborSet i, nbr j (u j)) * M.localNeighborPayoff i a u

theorem localDeviationPayoff_def [DecidableRel M.graph.Adj] (i : ι) (a : S i)
    (nbr : ∀ j : M.graph.neighborSet i, S j.1 → ℝ) :
    M.localDeviationPayoff i a nbr =
      ∑ u : (∀ j : M.graph.neighborSet i, S j.1),
        (∏ j : M.graph.neighborSet i, nbr j (u j)) * M.localNeighborPayoff i a u := by
  unfold localDeviationPayoff
  convert rfl

/-- **Local factorization of `expectedPayoff`**: when players outside `ClosedNeighborhood M.graph i`
use probability vectors summing to `1`, `M.expectedPayoff p i` sums only over closed-neighborhood
profiles. -/
theorem expectedPayoff_eq_localSum [DecidableRel M.graph.Adj] {p : ∀ k, S k → ℝ} {i : ι}
    (hp : ∀ k, ¬ (k = i ∨ M.graph.Adj i k) → ∑ a, p k a = 1) :
    M.expectedPayoff p i =
      ∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1),
        (∏ j : ClosedNeighborhood M.graph i, p j.1 (u j)) * M.localPayoff i u := by
  rw [expectedPayoff_def]
  exact sum_productWeight_mul_restrict (fun k => k = i ∨ M.graph.Adj i k) hp (M.localPayoff i)

/-- **Local factorization of `deviationPayoff`**: when every non-neighbor of `i` uses a vector
summing to `1`, `M.deviationPayoff p i a` equals `M.localDeviationPayoff i a` evaluated only on
`M.graph.neighborSet i` (independent of both `p i` and all non-neighbors). -/
theorem deviationPayoff_eq_localDeviationPayoff {p : ∀ k, S k → ℝ} {i : ι}
    (hp : ∀ k, ¬ M.graph.Adj i k → ∑ a, p k a = 1) (a : S i) :
    M.deviationPayoff p i a = M.localDeviationPayoff i a (fun j => p j.1) := by
  classical
  rw [deviationPayoff_def, localDeviationPayoff_def]
  simp only [payoff_update_eq_localNeighborPayoff]
  exact sum_productWeight_mul_restrict (fun k => M.graph.Adj i k) hp (M.localNeighborPayoff i a)

/-- Two mixed strategy profiles agreeing on `M.graph.neighborSet i` give player `i` identical
deviation payoffs for every pure action `a`. -/
theorem deviationPayoff_congr_neighbors {p q : ∀ k, S k → ℝ} {i : ι}
    (hp : ∀ k, ¬ M.graph.Adj i k → ∑ a, p k a = 1)
    (hq : ∀ k, ¬ M.graph.Adj i k → ∑ a, q k a = 1)
    (h_eq : ∀ j, M.graph.Adj i j → p j = q j) (a : S i) :
    M.deviationPayoff p i a = M.deviationPayoff q i a := by
  rw [M.deviationPayoff_eq_localDeviationPayoff hp a,
    M.deviationPayoff_eq_localDeviationPayoff hq a]
  congr 1
  ext j b
  exact congrFun (h_eq j.1 j.2) b

/-- Two mixed strategy profiles agreeing on `ClosedNeighborhood M.graph i` give player `i` the same
expected payoff ([Kearns2007], §7.2 & Definition 7.8 / Lemma 7.9 product case). -/
theorem expectedPayoff_congr_closedNeighborhood {p q : ∀ k, S k → ℝ} {i : ι}
    (hp : ∀ k, ∑ a, p k a = 1) (hq : ∀ k, ∑ a, q k a = 1)
    (h_eq : ∀ j, (j = i ∨ M.graph.Adj i j) → p j = q j) :
    M.expectedPayoff p i = M.expectedPayoff q i := by
  rw [← M.sum_mul_deviationPayoff_eq_expectedPayoff p (hp i),
    ← M.sum_mul_deviationPayoff_eq_expectedPayoff q (hq i), h_eq i (Or.inl rfl)]
  refine sum_congr rfl fun a _ => ?_
  rw [M.deviationPayoff_congr_neighbors (fun k _ => hp k) (fun k _ => hq k)
    (fun j hj => h_eq j (Or.inr hj)) a]

/-! ### Exact and `ε`-approximate Nash equilibria -/

/-- An additive **`ε`-approximate Nash equilibrium** of a graphical game ([Kearns2007], §7.2,
p. 162): every player uses a mixed strategy and no player can gain more than `ε` by a unilateral
pure deviation. -/
@[expose] def IsApproxNash (ε : ℝ) (p : ∀ i, S i → ℝ) : Prop :=
  (∀ i, IsMixedStrategy (p i)) ∧ ∀ i (a : S i), M.deviationPayoff p i a ≤ M.expectedPayoff p i + ε

/-- At `ε = 0`, `IsApproxNash` coincides with `M.toCostGame.IsMixedNash`. -/
theorem isApproxNash_zero_iff {p : ∀ i, S i → ℝ} :
    M.IsApproxNash 0 p ↔ M.toCostGame.IsMixedNash p := by
  refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun a => ?_
  simp only [toCostGame_expectedCost, toCostGame_deviationCost, add_zero]
  constructor <;> intro h <;> linarith

theorem IsApproxNash.mono {ε₁ ε₂ : ℝ} {p : ∀ i, S i → ℝ} (h : M.IsApproxNash ε₁ p)
    (hle : ε₁ ≤ ε₂) : M.IsApproxNash ε₂ p :=
  ⟨h.1, fun i a => by linarith [h.2 i a]⟩

/-- Equivalence between pure-deviation and mixed-deviation `ε`-Nash equilibrium ([Kearns2007],
§7.2, p. 162: `∀ i, ∀ p'_i, M_i(p) + ε ≥ M_i(p[i : p'_i])`). -/
theorem isApproxNash_iff_mixed {ε : ℝ} {p : ∀ i, S i → ℝ} :
    M.IsApproxNash ε p ↔ (∀ i, IsMixedStrategy (p i)) ∧
      ∀ i (x : S i → ℝ), IsMixedStrategy x →
        M.expectedPayoff (update p i x) i ≤ M.expectedPayoff p i + ε := by
  refine and_congr_right fun hp => forall_congr' fun i => ?_
  have hexp (x : S i → ℝ) (hx : IsMixedStrategy x) :
      M.expectedPayoff (update p i x) i = ∑ b, x b * M.deviationPayoff p i b := by
    have hupd (k : ι) (_ : ¬ M.graph.Adj i k) : ∑ a, update p i x k a = 1 := by
      rcases eq_or_ne k i with rfl | hki
      · simp [hx.sum_eq_one]
      · simp [hki, (hp k).sum_eq_one]
    rw [← M.sum_mul_deviationPayoff_eq_expectedPayoff (update p i x) (by simp [hx.sum_eq_one])]
    refine sum_congr rfl fun b _ => ?_
    rw [update_self, M.deviationPayoff_congr_neighbors hupd (fun k _ => (hp k).sum_eq_one)
      (fun j hj => update_of_ne (M.graph.ne_of_adj hj).symm x p) b]
  refine ⟨fun hi x hx => ?_, fun hi a => ?_⟩
  · rw [hexp x hx]
    calc ∑ b, x b * M.deviationPayoff p i b
        ≤ ∑ b, x b * (M.expectedPayoff p i + ε) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hi b) (hx.nonneg b)
      _ = M.expectedPayoff p i + ε := by rw [← sum_mul, hx.sum_eq_one, one_mul]
  · classical
    simpa only [hexp _ (isMixedStrategy_single a), Pi.single_apply, ite_mul, one_mul, zero_mul,
      sum_ite_eq', mem_univ, ↓reduceIte] using hi (Pi.single a 1) (isMixedStrategy_single a)

/-- Purely local `ε`-best-response predicate for player `i` against neighbor mixed strategies `nbr`
([Kearns2007], §7.2–7.3, pp. 162, 165). -/
@[expose] noncomputable def IsApproxBestResponse (ε : ℝ) (i : ι) (x : S i → ℝ)
    (nbr : ∀ j : M.graph.neighborSet i, S j.1 → ℝ) : Prop :=
  IsMixedStrategy x ∧
    ∀ a : S i, M.localDeviationPayoff i a nbr ≤
      (∑ b : S i, x b * M.localDeviationPayoff i b nbr) + ε

/-- Purely local exact best-response predicate (`ε = 0`). -/
@[expose] noncomputable def IsBestResponse (i : ι) (x : S i → ℝ)
    (nbr : ∀ j : M.graph.neighborSet i, S j.1 → ℝ) : Prop :=
  M.IsApproxBestResponse 0 i x nbr

theorem isApproxBestResponse_zero_iff {i : ι} {x : S i → ℝ}
    {nbr : ∀ j : M.graph.neighborSet i, S j.1 → ℝ} :
    M.IsApproxBestResponse 0 i x nbr ↔ M.IsBestResponse i x nbr := Iff.rfl

/-- **Locality of `IsApproxNash`**: `p` is an `ε`-Nash equilibrium of `M` if and only if each
`p i` is locally an `ε`-best response to `(fun j : M.graph.neighborSet i => p j.1)`. -/
theorem isApproxNash_iff_local {ε : ℝ} {p : ∀ i, S i → ℝ} :
    M.IsApproxNash ε p ↔ ∀ i, M.IsApproxBestResponse ε i (p i) (fun j => p j.1) := by
  refine ⟨fun ⟨hp, hbr⟩ i => ⟨hp i, fun a => ?_⟩,
    fun h => ⟨fun i => (h i).1, fun i a => ?_⟩⟩
  · simp_rw [← M.deviationPayoff_eq_localDeviationPayoff (fun k _ => (hp k).sum_eq_one),
      M.sum_mul_deviationPayoff_eq_expectedPayoff p (hp i).sum_eq_one]
    exact hbr i a
  · rw [← M.sum_mul_deviationPayoff_eq_expectedPayoff p ((h i).1).sum_eq_one]
    simp_rw [M.deviationPayoff_eq_localDeviationPayoff (fun k _ => ((h k).1).sum_eq_one)]
    exact (h i).2 a

/-- **Locality of exact Nash equilibrium**: `p` is a mixed Nash equilibrium of `M.toCostGame` if
and only if each `p i` is locally an exact best response to its neighbors in `M.graph`. -/
theorem isMixedNash_toCostGame_iff_local {p : ∀ i, S i → ℝ} :
    M.toCostGame.IsMixedNash p ↔ ∀ i, M.IsBestResponse i (p i) (fun j => p j.1) := by
  rw [← M.isApproxNash_zero_iff, M.isApproxNash_iff_local]
  rfl

end MixedExpectation

/-- **Expected payoff equivalence** `σ ≡_EP τ` ([Kearns2007], Definition 7.7, p. 170): two
finitely supported joint action distributions give every player the same expected payoff in `M`. -/
@[expose] def ExpectedPayoffEquiv {ι : Type*} {S : ι → Type*} (M : GraphicalGame ι S)
    (σ τ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
    τ.weights.sum (fun s w => w * M.payoff i s)

end GraphicalGame

section CorrelatedEquivalence

variable {ι : Type*} {S : ι → Type*}

/-- Marginal probability assigned by a finitely supported joint distribution `σ` to the
closed-neighborhood setting `u` of player `i` in `G` ([Kearns2007], Definition 7.8, p. 171). -/
noncomputable def neighborhoodMarginal (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (u : ∀ j : ClosedNeighborhood G i, S j.1) : ℝ := by
  classical
  exact σ.weights.sum fun s w => if (fun j : ClosedNeighborhood G i => s j.1) = u then w else 0

theorem neighborhoodMarginal_def (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [DecidableEq (∀ j : ClosedNeighborhood G i, S j.1)]
    (u : ∀ j : ClosedNeighborhood G i, S j.1) :
    neighborhoodMarginal G σ i u =
      σ.weights.sum fun s w => if (fun j : ClosedNeighborhood G i => s j.1) = u then w else 0 := by
  unfold neighborhoodMarginal
  convert rfl

/-- **Local neighborhood equivalence** `σ ≡_LN τ` with respect to `G` ([Kearns2007],
Definition 7.8, p. 171): `σ` and `τ` induce identical marginal distributions on every closed
neighborhood `ClosedNeighborhood G i`. -/
@[expose] def LocalNeighborhoodEquiv (G : SimpleGraph ι)
    (σ τ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1),
    neighborhoodMarginal G σ i u = neighborhoodMarginal G τ i u

private theorem sum_mul_local_eq_of_localNeighborhoodEquiv {G : SimpleGraph ι}
    {σ τ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : LocalNeighborhoodEquiv G σ τ) (i : ι)
    (f : (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) :
    σ.weights.sum (fun s w => w * f (fun j => s j.1)) =
      τ.weights.sum (fun s w => w * f (fun j => s j.1)) := by
  classical
  let U : Finset (∀ j : ClosedNeighborhood G i, S j.1) :=
    (σ.weights.support ∪ τ.weights.support).image fun s j => s j.1
  have hdecomp : ∀ ρ : Convexity.StdSimplex ℝ (∀ i, S i),
      (∀ s ∈ ρ.weights.support, (fun j : ClosedNeighborhood G i => s j.1) ∈ U) →
        ρ.weights.sum (fun s w => w * f (fun j => s j.1)) =
          ∑ u ∈ U, neighborhoodMarginal G ρ i u * f u := by
    intro ρ hU
    simp only [neighborhoodMarginal_def, Finsupp.sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun s hs => ?_
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq U (fun j : ClosedNeighborhood G i => s j.1) (fun u => ρ.weights s * f u),
      ite_eq_left_iff.2 fun hnot => absurd (hU s hs) hnot]
  rw [hdecomp σ (fun s hs => mem_image_of_mem _ (mem_union_left _ hs)),
    hdecomp τ (fun s hs => mem_image_of_mem _ (mem_union_right _ hs))]
  exact sum_congr rfl fun u _ => by rw [h i u]

/-- **Local neighborhood equivalence implies expected payoff equivalence** ([Kearns2007],
Lemma 7.9, first part, p. 171): if `σ ≡_LN τ` with respect to `M.graph`, then `σ ≡_EP τ` in `M`. -/
theorem LocalNeighborhoodEquiv.expectedPayoffEquiv {M : GraphicalGame ι S}
    {σ τ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : LocalNeighborhoodEquiv M.graph σ τ) :
    M.ExpectedPayoffEquiv σ τ :=
  fun i => sum_mul_local_eq_of_localNeighborhoodEquiv h i (M.localPayoff i)

/-- **Strictness of local neighborhood equivalence** ([Kearns2007], Lemma 7.9, second part,
p. 171): if `¬ LocalNeighborhoodEquiv G σ τ`, there exists a graphical game on `G` with `{0, 1}`
payoffs under which `σ` and `τ` are not expected-payoff equivalent. -/
theorem exists_graphicalGame_not_expectedPayoffEquiv {G : SimpleGraph ι}
    {σ τ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : ¬ LocalNeighborhoodEquiv G σ τ) :
    ∃ M : GraphicalGame ι S, M.graph = G ∧ ¬ M.ExpectedPayoffEquiv σ τ := by
  classical
  unfold LocalNeighborhoodEquiv at h
  push Not at h
  obtain ⟨i₀, u₀, hne⟩ := h
  refine ⟨{
    graph := G
    localPayoff := fun i u =>
      if hi : i = i₀ then
        if (hi ▸ u : ∀ j : ClosedNeighborhood G i₀, S j.1) = u₀ then 1 else 0
      else 0
  }, rfl, fun hep => hne ?_⟩
  have hval (ρ : Convexity.StdSimplex ℝ (∀ i, S i)) :
      ρ.weights.sum (fun s w =>
        w * (if (fun j : ClosedNeighborhood G i₀ => s j.1) = u₀ then (1 : ℝ) else 0)) =
        neighborhoodMarginal G ρ i₀ u₀ := by
    rw [neighborhoodMarginal_def]
    exact Finsupp.sum_congr fun _ _ => by split_ifs <;> ring
  simpa only [GraphicalGame.payoff_eq_localPayoff, ↓reduceDIte, hval] using hep i₀

/-- **Local neighborhood equivalence preserves approximate correlated equilibria** ([Kearns2007],
Lemma 7.10, p. 171, generalized to additive slack `ε`). -/
theorem LocalNeighborhoodEquiv.isApproxCorrelatedEquilibrium_iff [DecidableEq ι]
    {M : GraphicalGame ι S} {σ τ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h : LocalNeighborhoodEquiv M.graph σ τ) {ε : ι → ℝ} :
    M.toCostGame.IsApproxCorrelatedEquilibrium ε σ ↔
      M.toCostGame.IsApproxCorrelatedEquilibrium ε τ := by
  refine forall_congr' fun i => forall_congr' fun δ => ?_
  have h1 : σ.weights.sum (fun s w => w * M.toCostGame.cost i s) =
      τ.weights.sum (fun s w => w * M.toCostGame.cost i s) :=
    sum_mul_local_eq_of_localNeighborhoodEquiv h i fun u => -M.localPayoff i u
  let fδ : (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ := fun u =>
    -M.localPayoff i fun j =>
      if hj : j.1 = i then cast (congrArg S hj.symm) (δ (u ⟨i, Or.inl rfl⟩)) else u j
  have hcost_upd (s : ∀ k, S k) :
      M.toCostGame.cost i (update s i (δ (s i))) = fδ (fun j => s j.1) := by
    simp only [GraphicalGame.toCostGame_cost, GraphicalGame.payoff_eq_localPayoff, fδ, neg_inj]
    congr 1
    ext ⟨j, hj⟩
    rcases eq_or_ne j i with rfl | hji <;> simp [*]
  have h2 : σ.weights.sum (fun s w => w * M.toCostGame.cost i (update s i (δ (s i)))) =
      τ.weights.sum (fun s w => w * M.toCostGame.cost i (update s i (δ (s i)))) := by
    simp only [hcost_upd]
    exact sum_mul_local_eq_of_localNeighborhoodEquiv h i fδ
  rw [h1, h2]

/-- **Local neighborhood equivalence preserves correlated equilibria** ([Kearns2007], Lemma 7.10,
p. 171). -/
theorem LocalNeighborhoodEquiv.isCorrelatedEquilibrium_iff [DecidableEq ι]
    {M : GraphicalGame ι S} {σ τ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h : LocalNeighborhoodEquiv M.graph σ τ) :
    M.toCostGame.IsCorrelatedEquilibrium σ ↔ M.toCostGame.IsCorrelatedEquilibrium τ := by
  rw [← CostGame.isApproxCorrelatedEquilibrium_zero_iff,
    ← CostGame.isApproxCorrelatedEquilibrium_zero_iff]
  exact h.isApproxCorrelatedEquilibrium_iff

end CorrelatedEquivalence

end Cslib.GameTheory
