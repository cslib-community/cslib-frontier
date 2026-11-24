/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Star
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.EdgeSide
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Network creation games (Fabrikant–Luthra–Maneva–Papadimitriou–Shenker)

In the **network creation game** (also called the **local connection game**) of Fabrikant, Luthra,
Maneva, Papadimitriou, and Shenker (PODC 2003), as presented in [TardosWexler2007], Section 19.2
(locator not re-verified against primary PDF), the players are the vertices of a finite type `V`
and there is a uniform per-edge creation cost `α > 0`. Each player `u : V` chooses a set
`s u : Finset V` of incident edges to purchase, paying `α · |s u|`. Together the purchased edges
form the undirected graph `formedGraph s : SimpleGraph V` in which distinct vertices `u` and `v`
are adjacent whenever `v ∈ s u` or `u ∈ s v`.

Player `u` pays `α · |s u| + ∑ v, dist(u, v)` in `WithTop ℝ`: if every vertex is reachable from
`u` in `formedGraph s`, this is the finite real cost `connectedPlayerCost`; if some vertex is
unreachable from `u`, player `u`'s distance penalty—and hence `playerCost`—is `⊤` (`∞`). Thus
connectivity is enforced natively by the `WithTop ℝ` cost model rather than assumed as an external
restriction or approximated by a finite stand-in penalty.

## Main definitions

* `Cslib.GameTheory.NetworkCreationGame`: a network creation game with edge cost `alpha > 0`.
* `Cslib.GameTheory.NetworkCreationGame.formedGraph`: the undirected `SimpleGraph V` formed by a
  strategy profile `s : V → Finset V`.
* `Cslib.GameTheory.NetworkCreationGame.playerCost` and `socialCost`: `WithTop ℝ`-valued player
  and social costs (`⊤` iff disconnected).
* `Cslib.GameTheory.NetworkCreationGame.connectedPlayerCost`, `connectedSocialCost`, and
  `graphSocialCost`: real-valued costs on connected profiles and graphs.
* `Cslib.GameTheory.NetworkCreationGame.IsPureNash`: pure Nash equilibrium in `WithTop ℝ`.
* `Cslib.GameTheory.NetworkCreationGame.completeSocialCost`, `starSocialCost`, and
  `optSocialCost`: closed-form social cost of `K_n`, `S_n`, and their minimum `OPT`.
* `Cslib.GameTheory.NetworkCreationGame.completeProfile`, `centerStarProfile`, and
  `leafStarProfile`: canonical equilibrium orientations of `K_n` and `S_n`.

## Main results

* `IsPureNash.connected` and `IsPureNash.connectedSocialCost_eq_graphSocialCost`: every pure Nash
  equilibrium forms a connected graph without self-loops or doubly purchased edges.
* `optSocialCost_le_graphSocialCost`, `graphSocialCost_eq_completeSocialCost_iff`,
  `graphSocialCost_eq_starSocialCost_iff`, `graphSocialCost_eq_optSocialCost_iff_of_alpha_eq_two`,
  `coe_optSocialCost_le_socialCost`, and `exists_socialCost_eq_optSocialCost`
  ([TardosWexler2007], Lemma 19.1 and Exercises 19.1–19.2; locator not re-verified against primary
  PDF): `K_n` minimizes social cost for `α ≤ 2` (uniquely for `α < 2`), stars `S_n` minimize
  social cost for `α ≥ 2` (uniquely for `α > 2`), and connected graphs of diameter at most `2`
  minimize social cost at `α = 2`.
* `isPureNash_completeProfile`, `isPureNash_centerStarProfile`, `isPureNash_leafStarProfile`,
  `exists_isPureNash_socialCost_eq_optSocialCost`, and `exists_isPureNash_socialCost_le_four_thirds`
  ([TardosWexler2007], Lemma 19.2 and Theorem 19.3; locator not re-verified against primary PDF):
  `K_n` is a pure Nash equilibrium for `α ≤ 1`, both star sponsorships are pure Nash equilibria
  for `α ≥ 1`, giving `PoS = 1` outside `(1, 2)` and `PoS ≤ 4 / 3` everywhere (strict `< 4 / 3`
  when `|V| ≥ 2` and `1 ≤ α ≤ 2`).
* `IsPureNash.formedGraph_eq_top_of_alpha_lt_one` and `IsPureNash.socialCost_eq_opt_of_alpha_lt_one`
  ([TardosWexler2007], Exercise 19.3; locator not re-verified against primary PDF): for `α < 1`,
  `K_n` is the unique pure Nash equilibrium, so `PoA = 1`.
* `IsPureNash.socialCost_le_four_thirds_of_alpha_lt_two`: for `α < 2`, every pure Nash equilibrium
  has diameter at most `2` and social cost at most `(4 / 3) · OPT` (`PoA ≤ 4 / 3` on `1 ≤ α < 2`).
* `IsPureNash.socialCost_le_five_of_isTree` (Fabrikant et al. 2003, Theorem 2; locator not
  re-verified against primary PDF): every tree Nash equilibrium has social cost at most `5 · OPT`.
* `IsPureNash.socialCost_le_of_dist_le`, `IsPureNash.dist_le_two_mul_sqrt_add_one`, and
  `IsPureNash.socialCost_le_six_mul_sqrt_add_two` ([TardosWexler2007], Lemma 19.4 and Theorem 19.5;
  locator not re-verified against primary PDF): any pure Nash equilibrium of diameter `d ≥ 1` has
  social cost at most `(3 d - 1) · OPT`, every pure Nash equilibrium has diameter at most
  `2 √α + 1`, and hence `PoA ≤ 6 √α + 2 = O(√α)`.

## References

* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory

/-- A **network creation game** (Fabrikant–Luthra–Maneva–Papadimitriou–Shenker 2003;
[TardosWexler2007], Section 19.2, locator not re-verified against primary PDF) parameterized by
the positive cost `alpha > 0` of purchasing an incident undirected edge. -/
structure NetworkCreationGame where
  /-- Cost paid by a player for each edge it purchases. -/
  alpha : ℝ
  /-- Purchasing an edge has strictly positive cost. -/
  alpha_pos : 0 < alpha

namespace NetworkCreationGame

section Definitions

variable {V : Type*}

/-- The undirected graph formed by a strategy profile `s : V → Finset V`: an edge joins distinct
vertices `u` and `v` iff `v ∈ s u` or `u ∈ s v`. -/
@[expose] def formedGraph (s : V → Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => v ∈ s u

instance [DecidableEq V] (s : V → Finset V) : DecidableRel (formedGraph s).Adj :=
  inferInstanceAs (DecidableRel fun u v => u ≠ v ∧ (v ∈ s u ∨ u ∈ s v))

@[simp]
theorem formedGraph_adj {s : V → Finset V} {u v : V} :
    (formedGraph s).Adj u v ↔ u ≠ v ∧ (v ∈ s u ∨ u ∈ s v) := by
  simp [formedGraph, SimpleGraph.fromRel_adj]

variable [Fintype V] (G : NetworkCreationGame)

/-- The finite real cost `α · |s u| + ∑ v, dist(u, v)` of player `u` when all vertices are
reachable from `u` in `formedGraph s`. -/
@[expose] noncomputable def connectedPlayerCost (s : V → Finset V) (u : V) : ℝ :=
  G.alpha * ((s u).card : ℝ) + ∑ v : V, ((formedGraph s).dist u v : ℝ)

/-- Player `u`'s cost in `WithTop ℝ`: `connectedPlayerCost` when every vertex is reachable from
`u` in `formedGraph s`, and `⊤` (`∞`) when some vertex is unreachable from `u`. -/
noncomputable def playerCost (s : V → Finset V) (u : V) : WithTop ℝ :=
  open Classical in
  if ∀ v, (formedGraph s).Reachable u v then ↑(G.connectedPlayerCost s u) else ⊤

/-- Sum of `connectedPlayerCost` across all players. Agrees with `socialCost` on connected
profiles. -/
@[expose] noncomputable def connectedSocialCost (s : V → Finset V) : ℝ :=
  ∑ u : V, G.connectedPlayerCost s u

/-- Social cost `∑ u, playerCost s u` in `WithTop ℝ` (`⊤` whenever the formed graph is
disconnected). -/
@[expose] noncomputable def socialCost (s : V → Finset V) : WithTop ℝ :=
  ∑ u : V, G.playerCost s u

/-- Intrinsic social cost of an undirected graph `H` when each edge is purchased once:
`α · |E(H)| + ∑ u, ∑ v, dist_H(u, v)`. -/
@[expose] noncomputable def graphSocialCost (H : SimpleGraph V) [DecidableRel H.Adj] : ℝ :=
  G.alpha * (H.edgeFinset.card : ℝ) + ∑ u : V, ∑ v : V, (H.dist u v : ℝ)

private theorem graphSocialCost_congr {H₁ H₂ : SimpleGraph V} [inst₁ : DecidableRel H₁.Adj]
    [inst₂ : DecidableRel H₂.Adj] (h : H₁ = H₂) :
    G.graphSocialCost H₁ = G.graphSocialCost H₂ := by
  subst h
  rw [Subsingleton.elim inst₁ inst₂]

/-- A profile `s` is a **pure Nash equilibrium** if no player can strictly reduce its `WithTop ℝ`
cost by unilaterally changing its purchased neighbor set. -/
@[expose] def IsPureNash [DecidableEq V] (s : V → Finset V) : Prop :=
  ∀ u (t : Finset V), G.playerCost s u ≤ G.playerCost (Function.update s u t) u

/-- Closed-form social cost `(α / 2 + 1) · n · (n - 1)` of the complete graph on `V`. -/
@[expose] noncomputable def completeSocialCost (V : Type*) [Fintype V] : ℝ :=
  (G.alpha / 2 + 1) * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ)

/-- Closed-form social cost `(n - 1) · (α + 2 (n - 1))` of any star graph on `V`. -/
@[expose] noncomputable def starSocialCost (V : Type*) [Fintype V] : ℝ :=
  ((Fintype.card V - 1 : ℕ) : ℝ) * (G.alpha + 2 * ((Fintype.card V - 1 : ℕ) : ℝ))

/-- Optimal social cost `min (completeSocialCost V) (starSocialCost V)` on `V`. -/
@[expose] noncomputable def optSocialCost (V : Type*) [Fintype V] : ℝ :=
  min (G.completeSocialCost V) (G.starSocialCost V)

/-- Complete-graph strategy profile under a linear order: each player `u` buys `{v | u < v}`. -/
@[expose] def completeProfile [LinearOrder V] : V → Finset V :=
  fun u => Finset.univ.filter (u < ·)

/-- Center-sponsored star profile: the center `c` buys edges to all `v ≠ c`; leaves buy nothing. -/
@[expose] def centerStarProfile [DecidableEq V] (c : V) : V → Finset V :=
  fun u => if u = c then Finset.univ.erase c else ∅

/-- Leaf-sponsored star profile: each leaf `u ≠ c` buys `{c}`; the center `c` buys nothing. -/
@[expose] def leafStarProfile [DecidableEq V] (c : V) : V → Finset V :=
  fun u => if u = c then ∅ else {c}

end Definitions

section BasicCosts

variable {V : Type*} [Fintype V] (G : NetworkCreationGame)

theorem playerCost_of_forall_reachable {s : V → Finset V} {u : V}
    (h : ∀ v, (formedGraph s).Reachable u v) :
    G.playerCost s u = ↑(G.connectedPlayerCost s u) := by
  simp [playerCost, h]

theorem playerCost_of_connected {s : V → Finset V} (h : (formedGraph s).Connected) (u : V) :
    G.playerCost s u = ↑(G.connectedPlayerCost s u) :=
  G.playerCost_of_forall_reachable (fun v => h u v)

theorem playerCost_eq_top_iff {s : V → Finset V} {u : V} :
    G.playerCost s u = ⊤ ↔ ∃ v, ¬ (formedGraph s).Reachable u v := by
  classical
  simp only [playerCost, ite_eq_right_iff, WithTop.coe_ne_top, imp_false, not_forall]

theorem playerCost_ne_top_iff {s : V → Finset V} {u : V} :
    G.playerCost s u ≠ ⊤ ↔ ∀ v, (formedGraph s).Reachable u v := by
  rw [ne_eq, playerCost_eq_top_iff, not_exists_not]

theorem socialCost_of_preconnected {s : V → Finset V} (h : (formedGraph s).Preconnected) :
    G.socialCost s = ↑(G.connectedSocialCost s) := by
  unfold socialCost connectedSocialCost
  rw [WithTop.coe_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact G.playerCost_of_forall_reachable (fun v => h u v)

theorem socialCost_of_connected {s : V → Finset V} (h : (formedGraph s).Connected) :
    G.socialCost s = ↑(G.connectedSocialCost s) :=
  G.socialCost_of_preconnected h.preconnected

theorem socialCost_eq_top_of_not_connected [Nonempty V] {s : V → Finset V}
    (h : ¬ (formedGraph s).Connected) : G.socialCost s = ⊤ := by
  have hpre : ¬ (formedGraph s).Preconnected := fun hp => h ⟨hp⟩
  unfold SimpleGraph.Preconnected at hpre
  push Not at hpre
  obtain ⟨u, v, huv⟩ := hpre
  rw [socialCost, WithTop.sum_eq_top]
  exact ⟨u, Finset.mem_univ u, G.playerCost_eq_top_iff.mpr ⟨v, huv⟩⟩

theorem connectedSocialCost_eq {s : V → Finset V} :
    G.connectedSocialCost s =
      G.alpha * (∑ u : V, ((s u).card : ℝ)) +
        ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) := by
  simp only [connectedSocialCost, connectedPlayerCost, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Every edge of `formedGraph s` is purchased by at least one endpoint, so `graphSocialCost`
never exceeds `connectedSocialCost`. -/
theorem graphSocialCost_formedGraph_le [DecidableEq V] (s : V → Finset V) :
    G.graphSocialCost (formedGraph s) ≤ G.connectedSocialCost s := by
  rw [graphSocialCost, connectedSocialCost_eq]
  have hcard : (formedGraph s).edgeFinset.card ≤ ∑ u : V, (s u).card := by
    have hsub : (formedGraph s).edgeFinset ⊆
        Finset.univ.biUnion fun u => (s u).image fun v => s(u, v) := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, formedGraph_adj] at he
        rw [Finset.mem_biUnion]
        rcases he.2 with hv | hu
        · exact ⟨u, Finset.mem_univ u, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
        · exact ⟨v, Finset.mem_univ v, Finset.mem_image.mpr ⟨u, hu, Sym2.eq_swap⟩⟩
    calc (formedGraph s).edgeFinset.card
      _ ≤ (Finset.univ.biUnion fun u => (s u).image fun v => s(u, v)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u : V, ((s u).image fun v => s(u, v)).card := Finset.card_biUnion_le
      _ ≤ ∑ u : V, (s u).card := Finset.sum_le_sum fun u _ => Finset.card_image_le
  have hcardR : ((formedGraph s).edgeFinset.card : ℝ) ≤ ∑ u : V, ((s u).card : ℝ) := by
    exact_mod_cast hcard
  nlinarith [G.alpha_pos]

/-- When a profile has no self-loops (`u ∉ s u`) and no doubly purchased edges
(`v ∈ s u → u ∉ s v`), each edge of `formedGraph s` is purchased by a unique player. -/
theorem sum_card_eq_card_edgeFinset [DecidableEq V] {s : V → Finset V}
    (hirr : ∀ u, u ∉ s u) (hasym : ∀ u v, v ∈ s u → u ∉ s v) :
    ∑ u : V, (s u).card = (formedGraph s).edgeFinset.card := by
  rw [← Finset.card_sigma (s := Finset.univ)]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    rw [Finset.mem_sigma] at hp
    have hne : u ≠ v := fun h => hirr u (h ▸ hp.2)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, formedGraph_adj]
    exact ⟨hne, Or.inl hp.2⟩
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ heq
    rw [Finset.mem_sigma] at hp₁ hp₂
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hp₂.2 (hasym u₁ v₁ hp₁.2)
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, formedGraph_adj] at he
      rcases he.2 with hv | hu
      · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ u, hv⟩, rfl⟩
      · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ v, hu⟩, Sym2.eq_swap⟩

theorem connectedSocialCost_eq_graphSocialCost_of_clean [DecidableEq V] {s : V → Finset V}
    (hirr : ∀ u, u ∉ s u) (hasym : ∀ u v, v ∈ s u → u ∉ s v) :
    G.connectedSocialCost s = G.graphSocialCost (formedGraph s) := by
  rw [connectedSocialCost_eq, graphSocialCost, ← sum_card_eq_card_edgeFinset hirr hasym,
    Nat.cast_sum]

end BasicCosts

section PureNashStructure

variable {V : Type*} [Fintype V] [DecidableEq V] {G : NetworkCreationGame} {s : V → Finset V}

/-- At any pure Nash equilibrium, every vertex is reachable from every player `u`: otherwise `u`
could buy edges to all `v ≠ u` and drop its cost from `⊤` to a finite real number. -/
theorem IsPureNash.forall_reachable (hs : G.IsPureNash s) (u : V) (v : V) :
    (formedGraph s).Reachable u v := by
  have hreach_dev : ∀ w, (formedGraph (Function.update s u (Finset.univ.erase u))).Reachable u w :=
    fun w => by
      by_cases hwu : u = w
      · subst hwu
        exact SimpleGraph.Reachable.refl u
      · refine SimpleGraph.Adj.reachable ?_
        rw [formedGraph_adj]
        exact ⟨hwu, Or.inl (by simp [Ne.symm hwu])⟩
  have hlt : G.playerCost (Function.update s u (Finset.univ.erase u)) u < ⊤ := by
    rw [G.playerCost_of_forall_reachable hreach_dev]
    exact WithTop.coe_lt_top _
  have hne : G.playerCost s u ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hs u _) hlt)
  exact (G.playerCost_ne_top_iff.mp hne) v

/-- Every pure Nash equilibrium on a nonempty vertex set forms a connected graph. -/
theorem IsPureNash.connected [Nonempty V] (hs : G.IsPureNash s) : (formedGraph s).Connected :=
  ⟨fun u v => hs.forall_reachable u v⟩

/-- Unpacking a pure Nash equilibrium inequality onto `connectedPlayerCost` for any deviation that
leaves all vertices reachable from the deviating player. -/
theorem IsPureNash.connectedPlayerCost_le (hs : G.IsPureNash s) (u : V) (t : Finset V)
    (hreach : ∀ v, (formedGraph (Function.update s u t)).Reachable u v) :
    G.connectedPlayerCost s u ≤ G.connectedPlayerCost (Function.update s u t) u := by
  have h := hs u t
  rw [G.playerCost_of_forall_reachable (hs.forall_reachable u),
    G.playerCost_of_forall_reachable hreach, WithTop.coe_le_coe] at h
  exact h

private theorem IsPureNash.false_of_formedGraph_erase_eq (hs : G.IsPureNash s) {u w : V}
    (hw : w ∈ s u) (hfg : formedGraph (Function.update s u ((s u).erase w)) = formedGraph s) :
    False := by
  let s' := Function.update s u ((s u).erase w)
  have hle := hs.connectedPlayerCost_le u ((s u).erase w) (fun v => hfg ▸ hs.forall_reachable u v)
  simp only [connectedPlayerCost, Function.update_self] at hle
  have hdist : ∑ v : V, ((formedGraph s').dist u v : ℝ) =
      ∑ v : V, ((formedGraph s).dist u v : ℝ) := by
    rw [hfg]
  have hcard : (((s u).erase w).card : ℝ) + 1 = ((s u).card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hw
  dsimp only [s'] at hdist
  nlinarith [G.alpha_pos]

/-- No player buys a self-loop at a pure Nash equilibrium (`α > 0`). -/
theorem IsPureNash.notMem_self (hs : G.IsPureNash s) (u : V) : u ∉ s u := by
  intro hu
  refine hs.false_of_formedGraph_erase_eq hu ?_
  ext a b
  simp only [formedGraph_adj]
  by_cases hau : a = u
  · subst hau
    by_cases hba : a = b <;> simp [hba, Ne.symm]
  · by_cases hbu : b = u
    · subst hbu
      simp [hau]
    · simp [hau, hbu]

/-- No edge is purchased by both of its endpoints at a pure Nash equilibrium (`α > 0`). -/
theorem IsPureNash.notMem_symm (hs : G.IsPureNash s) {u v : V} (huv : v ∈ s u) : u ∉ s v := by
  intro hvu
  refine hs.false_of_formedGraph_erase_eq huv ?_
  ext a b
  simp only [formedGraph_adj]
  refine and_congr_right fun hab => ?_
  by_cases hau : a = u
  · subst hau
    rw [Function.update_self, Function.update_of_ne hab.symm, Finset.mem_erase]
    by_cases hbv : b = v <;> [subst hbv; skip] <;> simp [*]
  · rw [Function.update_of_ne hau]
    by_cases hbu : b = u
    · subst hbu
      rw [Function.update_self, Finset.mem_erase]
      by_cases hav : a = v <;> [subst hav; skip] <;> simp [*]
    · rw [Function.update_of_ne hbu]

theorem IsPureNash.connectedSocialCost_eq_graphSocialCost (hs : G.IsPureNash s) :
    G.connectedSocialCost s = G.graphSocialCost (formedGraph s) :=
  G.connectedSocialCost_eq_graphSocialCost_of_clean hs.notMem_self fun _ _ => hs.notMem_symm

theorem IsPureNash.socialCost_eq_coe (hs : G.IsPureNash s) :
    G.socialCost s = ↑(G.connectedSocialCost s) :=
  G.socialCost_of_preconnected fun u v => hs.forall_reachable u v

omit [Fintype V] in
private theorem formedGraph_le_update_insert (s : V → Finset V) (u w : V) :
    formedGraph s ≤ formedGraph (Function.update s u (insert w (s u))) := by
  intro a b hab
  rw [formedGraph_adj] at hab ⊢
  refine ⟨hab.1, ?_⟩
  rcases hab.2 with hb | ha
  · left; by_cases hau : a = u <;> [subst hau; skip] <;> simp [*]
  · right; by_cases hbu : b = u <;> [subst hbu; skip] <;> simp [*]

/-- **Unilateral edge-addition bound**: at a pure Nash equilibrium `s`, if player `u` considers
adding a single vertex `w` to `s u`, the total distance reduction from `u` across any subset
`S : Finset V` of vertices is at most `α`. -/
theorem IsPureNash.sum_dist_sub_le_alpha (hs : G.IsPureNash s) (u w : V) (S : Finset V) :
    ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) -
      ((formedGraph (Function.update s u (insert w (s u)))).dist u x : ℝ)) ≤ G.alpha := by
  let s' := Function.update s u (insert w (s u))
  have hmono : formedGraph s ≤ formedGraph s' := formedGraph_le_update_insert s u w
  have hreach' : ∀ x, (formedGraph s').Reachable u x :=
    fun x => (hs.forall_reachable u x).mono hmono
  have hdist_le : ∀ x, (formedGraph s').dist u x ≤ (formedGraph s).dist u x := fun x => by
    have he := SimpleGraph.edist_anti hmono (u := u) (v := x)
    rw [← (hreach' x).coe_dist_eq_edist, ← (hs.forall_reachable u x).coe_dist_eq_edist] at he
    exact_mod_cast he
  have hnonneg : ∀ x : V, 0 ≤ ((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ) :=
    fun x => sub_nonneg.mpr (by exact_mod_cast hdist_le x)
  have hsub : ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ)) ≤
      (∑ x : V, ((formedGraph s).dist u x : ℝ)) - ∑ x : V, ((formedGraph s').dist u x : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_univ_sum_of_nonneg hnonneg
  have hne_cost := hs.connectedPlayerCost_le u (insert w (s u)) hreach'
  simp only [connectedPlayerCost, Function.update_self] at hne_cost
  have hcard : ((insert w (s u)).card : ℝ) ≤ ((s u).card : ℝ) + 1 := by
    exact_mod_cast Finset.card_insert_le w (s u)
  dsimp only [s'] at hsub
  nlinarith [G.alpha_pos]

end PureNashStructure

section SocialOptimum

variable {V : Type*} [Fintype V] (G : NetworkCreationGame)

/-- Exact difference between `completeSocialCost` and `starSocialCost`:
`completeSocialCost - starSocialCost = (α - 2) (n - 1) (n - 2) / 2`. -/
theorem completeSocialCost_sub_starSocialCost :
    G.completeSocialCost V - G.starSocialCost V =
      (G.alpha - 2) * ((Fintype.card V - 1 : ℕ) : ℝ) * ((Fintype.card V - 2 : ℕ) : ℝ) / 2 := by
  unfold completeSocialCost starSocialCost
  rcases h : Fintype.card V with _ | _ | k
  · simp
  · simp
  · push_cast
    ring

theorem optSocialCost_eq_completeSocialCost (hα : G.alpha ≤ 2) :
    G.optSocialCost V = G.completeSocialCost V := by
  rw [optSocialCost, min_eq_left_iff, ← sub_nonpos, completeSocialCost_sub_starSocialCost]
  have hprod : 0 ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * ((Fintype.card V - 2 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith

theorem optSocialCost_eq_starSocialCost (hα : 2 ≤ G.alpha) :
    G.optSocialCost V = G.starSocialCost V := by
  rw [optSocialCost, min_eq_right_iff, ← sub_nonneg, completeSocialCost_sub_starSocialCost]
  have hprod : 0 ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * ((Fintype.card V - 2 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith

theorem optSocialCost_nonneg (V : Type*) [Fintype V] : 0 ≤ G.optSocialCost V := by
  rw [optSocialCost, completeSocialCost, starSocialCost, le_min_iff]
  have hα : 0 < G.alpha := G.alpha_pos
  exact ⟨by positivity, by positivity⟩

/-- Useful lower bound `α (n - 1) + n (n - 1) ≤ OPT` valid whenever `|V| ≥ 2`. -/
theorem alpha_add_card_mul_le_optSocialCost (hn : 2 ≤ Fintype.card V) :
    (G.alpha + (Fintype.card V : ℝ)) * ((Fintype.card V - 1 : ℕ) : ℝ) ≤ G.optSocialCost V := by
  rw [optSocialCost, le_min_iff]
  have hα : 0 < G.alpha := G.alpha_pos
  have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hn1_nn : (0 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  constructor
  · unfold completeSocialCost
    exact mul_le_mul_of_nonneg_right (by nlinarith) hn1_nn
  · unfold starSocialCost
    rw [mul_comm ((Fintype.card V - 1 : ℕ) : ℝ)]
    refine mul_le_mul_of_nonneg_right ?_ hn1_nn
    rw [hn1]
    linarith

omit [Fintype V] in
private noncomputable def diamLowerTerm [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (u v : V) : ℝ :=
  (if u = v then 0 else 2) - if H.Adj u v then 1 else 0

omit [Fintype V] in
private theorem diamLowerTerm_le_dist [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : H.Connected) (u v : V) : diamLowerTerm H u v ≤ (H.dist u v : ℝ) := by
  unfold diamLowerTerm
  by_cases huv : u = v
  · subst huv; simp
  · by_cases hadj : H.Adj u v
    · simp only [huv, ↓reduceIte, hadj, SimpleGraph.dist_eq_one_iff_adj.mpr hadj, Nat.cast_one]
      norm_num
    · simp only [huv, ↓reduceIte, hadj, sub_zero]
      exact_mod_cast hH.one_lt_dist_of_ne_of_not_adj huv hadj

private theorem sum_sum_diamLowerTerm [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ u : V, ∑ v : V, diamLowerTerm H u v) =
      2 * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) -
        2 * (H.edgeFinset.card : ℝ) := by
  unfold diamLowerTerm
  simp only [Finset.sum_sub_distrib]
  have hne2 : (∑ u : V, ∑ v : V, if u = v then (0 : ℝ) else 2) =
      2 * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
    have hinner : ∀ u : V, (∑ v : V, if u = v then (0 : ℝ) else 2) =
        2 * ((Fintype.card V - 1 : ℕ) : ℝ) := fun u => by
      have hcard : (Finset.univ.filter fun v : V => u ≠ v).card = Fintype.card V - 1 := by
        have heq : (Finset.univ.filter fun v : V => u ≠ v) = Finset.univ.erase u := by
          ext v; simp [eq_comm]
        rw [heq, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      calc (∑ v : V, if u = v then (0 : ℝ) else 2)
        _ = ∑ v : V, if u ≠ v then (2 : ℝ) else 0 :=
            Finset.sum_congr rfl fun v _ => by split_ifs <;> simp_all
        _ = ∑ _v ∈ Finset.univ.filter (fun v : V => u ≠ v), (2 : ℝ) := by rw [← Finset.sum_filter]
        _ = 2 * ((Fintype.card V - 1 : ℕ) : ℝ) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hadj1 : (∑ u : V, ∑ v : V, if H.Adj u v then (1 : ℝ) else 0) =
      2 * (H.edgeFinset.card : ℝ) := by
    have hinner : ∀ u : V, (∑ v : V, if H.Adj u v then (1 : ℝ) else 0) = (H.degree u : ℝ) :=
      fun u => by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        have heq : (Finset.univ.filter fun v => H.Adj u v) = H.neighborFinset u := by ext v; simp
        rw [heq, H.card_neighborFinset_eq_degree]
    simp only [hinner]
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  rw [hne2, hadj1]

/-- **Master social-cost lower bound** on any connected graph `H`: every distinct non-adjacent pair
has distance at least `2`, so
`2 n (n - 1) + (α - 2) |E(H)| ≤ graphSocialCost H`. -/
theorem graphSocialCost_ge_of_connected {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : H.Connected) :
    2 * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) +
      (G.alpha - 2) * (H.edgeFinset.card : ℝ) ≤ G.graphSocialCost H := by
  classical
  have hsum : ∑ u : V, ∑ v : V, diamLowerTerm H u v ≤ ∑ u : V, ∑ v : V, (H.dist u v : ℝ) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => diamLowerTerm_le_dist hH u v
  rw [sum_sum_diamLowerTerm] at hsum
  unfold graphSocialCost
  linarith

/-- Equality holds in `graphSocialCost_ge_of_connected` iff `H` has diameter at most `2`. -/
theorem graphSocialCost_eq_iff_diam_le_two {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : H.Connected) :
    G.graphSocialCost H =
      2 * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) +
        (G.alpha - 2) * (H.edgeFinset.card : ℝ) ↔
      ∀ u v : V, H.dist u v ≤ 2 := by
  classical
  have heq_iff : G.graphSocialCost H =
      2 * (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) +
        (G.alpha - 2) * (H.edgeFinset.card : ℝ) ↔
      ∑ u : V, ∑ v : V, diamLowerTerm H u v = ∑ u : V, ∑ v : V, (H.dist u v : ℝ) := by
    unfold graphSocialCost
    rw [sum_sum_diamLowerTerm]
    constructor <;> intro h <;> linarith
  rw [heq_iff, Finset.sum_eq_sum_iff_of_le
    fun u _ => Finset.sum_le_sum fun v _ => diamLowerTerm_le_dist hH u v]
  simp only [Finset.mem_univ, forall_true_left]
  refine ⟨fun h u v => ?_, fun h u => Finset.sum_congr rfl fun v _ => ?_⟩
  · have huv := Finset.sum_eq_sum_iff_of_le (fun w _ => diamLowerTerm_le_dist hH u w)
      |>.mp (h u) v (Finset.mem_univ v)
    unfold diamLowerTerm at huv
    by_cases heq : u = v
    · subst heq; simp
    · by_cases hadj : H.Adj u v
      · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]; omega
      · simp only [heq, ↓reduceIte, hadj, sub_zero] at huv
        exact_mod_cast huv.symm.le
  · apply le_antisymm (diamLowerTerm_le_dist hH u v)
    unfold diamLowerTerm
    by_cases heq : u = v
    · subst heq; simp
    · by_cases hadj : H.Adj u v
      · simp only [heq, ↓reduceIte, hadj, SimpleGraph.dist_eq_one_iff_adj.mpr hadj, Nat.cast_one]
        norm_num
      · simp only [heq, ↓reduceIte, hadj, sub_zero]
        exact_mod_cast h u v

private theorem twice_card_edgeFinset_le (H : SimpleGraph V) [DecidableRel H.Adj] :
    2 * H.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  rw [← H.sum_degrees_eq_twice_card_edges]
  calc ∑ v : V, H.degree v
    _ ≤ ∑ _v : V, (Fintype.card V - 1) :=
        Finset.sum_le_sum fun v _ => Nat.le_sub_one_of_lt (H.degree_lt_card_verts v)
    _ = Fintype.card V * (Fintype.card V - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

private theorem twice_card_edgeFinset_top [DecidableEq V] :
    2 * (⊤ : SimpleGraph V).edgeFinset.card = Fintype.card V * (Fintype.card V - 1) := by
  rw [← (⊤ : SimpleGraph V).sum_degrees_eq_twice_card_edges]
  have hdeg : ∀ v : V, (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := fun v => by
    rw [← (⊤ : SimpleGraph V).card_neighborFinset_eq_degree]
    have heq : (⊤ : SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
      ext w
      simp [eq_comm]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul]

private theorem card_vert_sub_one_le_edgeFinset (H : SimpleGraph V) [Fintype H.edgeSet]
    (hH : H.Connected) : Fintype.card V - 1 ≤ H.edgeFinset.card := by
  have h := hH.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h
  omega

theorem graphSocialCost_top [DecidableEq V] :
    G.graphSocialCost (⊤ : SimpleGraph V) = G.completeSocialCost V := by
  by_cases hV : Nonempty V
  · have hconn : (⊤ : SimpleGraph V).Connected := SimpleGraph.connected_top
    have hdiam : ∀ u v : V, (⊤ : SimpleGraph V).dist u v ≤ 2 := fun u v => by
      by_cases huv : u = v
      · subst huv; simp
      · have hadj : (⊤ : SimpleGraph V).Adj u v := by simpa using huv
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
        omega
    have heq := (G.graphSocialCost_eq_iff_diam_le_two hconn).mpr hdiam
    have hm : 2 * ((⊤ : SimpleGraph V).edgeFinset.card : ℝ) =
        (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast twice_card_edgeFinset_top (V := V)
    have hm' : ((⊤ : SimpleGraph V).edgeFinset.card : ℝ) =
        (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) / 2 := by
      linarith
    rw [heq, hm']
    unfold completeSocialCost
    ring
  · rw [not_nonempty_iff] at hV
    have hm : (⊤ : SimpleGraph V).edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e
      exact Sym2.ind (fun u => hV.elim u) e
    rw [graphSocialCost, hm, Nat.cast_zero, mul_zero, zero_add, completeSocialCost,
      Fintype.card_eq_zero]
    simp

omit [Fintype V] in
private theorem starGraph_dist_le_two (c u v : V) : (SimpleGraph.starGraph c).dist u v ≤ 2 := by
  have h1 : (SimpleGraph.starGraph c).dist u c ≤ 1 := by
    by_cases hu : u = c
    · subst hu; simp
    · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (SimpleGraph.starGraph_center_adj' (Ne.symm hu))]
  have h2 : (SimpleGraph.starGraph c).dist c v ≤ 1 := by
    by_cases hv : c = v
    · subst hv; simp
    · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (SimpleGraph.starGraph_center_adj hv)]
  exact ((SimpleGraph.connected_starGraph c).dist_triangle (v := c)).trans (by omega)

theorem graphSocialCost_starGraph [DecidableEq V] (c : V) :
    G.graphSocialCost (SimpleGraph.starGraph c) = G.starSocialCost V := by
  have hT : (SimpleGraph.starGraph c).IsTree := SimpleGraph.isTree_starGraph c
  have heq := (G.graphSocialCost_eq_iff_diam_le_two hT.connected).mpr (starGraph_dist_le_two c)
  have hm_nat : (SimpleGraph.starGraph c).edgeFinset.card = Fintype.card V - 1 := by
    have hc := hT.card_edgeFinset
    omega
  have hm : ((SimpleGraph.starGraph c).edgeFinset.card : ℝ) =
      ((Fintype.card V - 1 : ℕ) : ℝ) := by
    rw [hm_nat]
  have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
    have : Nonempty V := ⟨c⟩
    have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
    exact_mod_cast Nat.sub_add_cancel hpos
  rw [heq, hm]
  unfold starSocialCost
  nlinarith

/-- **Optimal social cost lower bound** ([TardosWexler2007], Lemma 19.1, locator not re-verified
against primary PDF): every connected graph `H` on `V` has `optSocialCost V ≤ graphSocialCost H`. -/
theorem optSocialCost_le_graphSocialCost {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : H.Connected) : G.optSocialCost V ≤ G.graphSocialCost H := by
  have hge := G.graphSocialCost_ge_of_connected hH
  rcases le_total G.alpha 2 with hα | hα
  · rw [G.optSocialCost_eq_completeSocialCost hα]
    have hm : 2 * (H.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast twice_card_edgeFinset_le H
    unfold completeSocialCost
    nlinarith
  · rw [G.optSocialCost_eq_starSocialCost hα]
    have hm : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
      exact_mod_cast card_vert_sub_one_le_edgeFinset H hH
    have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
      have := hH.nonempty
      exact_mod_cast Nat.sub_add_cancel Fintype.card_pos
    unfold starSocialCost
    nlinarith

/-- **Strict uniqueness of `K_n` for `α < 2`** ([TardosWexler2007], Exercise 19.1, locator not
re-verified against primary PDF): when `α < 2`, a connected graph achieves `completeSocialCost`
iff it is the complete graph `⊤`. -/
theorem graphSocialCost_eq_completeSocialCost_iff (hα : G.alpha < 2)
    {H : SimpleGraph V} [DecidableRel H.Adj] (hH : H.Connected) :
    G.graphSocialCost H = G.completeSocialCost V ↔ H = ⊤ := by
  classical
  refine ⟨fun heq => ?_, fun htop => (G.graphSocialCost_congr htop).trans G.graphSocialCost_top⟩
  have hge := G.graphSocialCost_ge_of_connected hH
  have hm_le : 2 * H.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) :=
    twice_card_edgeFinset_le H
  have hm_leR : 2 * (H.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
    exact_mod_cast hm_le
  have hm_eqR : 2 * (H.edgeFinset.card : ℝ) =
      (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
    unfold completeSocialCost at heq
    nlinarith
  have hm_eq : H.edgeFinset.card = (⊤ : SimpleGraph V).edgeFinset.card := by
    have h1 : 2 * H.edgeFinset.card = Fintype.card V * (Fintype.card V - 1) := by
      exact_mod_cast hm_eqR
    have h2 := twice_card_edgeFinset_top (V := V)
    omega
  have hsub : H.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hedf : H.edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hm_eq.ge
  ext u v
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset, hedf,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

omit [Fintype V] in
/-- Every finite tree of diameter at most `2` is a star graph `SimpleGraph.starGraph c`. -/
private theorem exists_eq_starGraph_of_isTree_of_diam_le_two [Finite V] {H : SimpleGraph V}
    (hT : H.IsTree) (hdiam : ∀ u v : V, H.dist u v ≤ 2) :
    ∃ c : V, H = SimpleGraph.starGraph c := by
  have := Fintype.ofFinite V
  classical
  have := hT.connected.nonempty
  by_cases hsub : Subsingleton V
  · refine ⟨Classical.arbitrary V, ?_⟩
    ext u v
    have huv : u = v := Subsingleton.elim u v
    subst huv
    simp
  · rw [not_subsingleton_iff_nontrivial] at hsub
    obtain ⟨l, hl⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨c, hlc, hc_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl
    refine ⟨c, SimpleGraph.eq_starGraph_of_isUniversal_of_cliqueFree_three ?_
      hT.isAcyclic.cliqueFree_three⟩
    intro v hvc
    by_cases hvl : v = l
    · subst hvl; exact hlc.symm
    · have hnot_lv : ¬ H.Adj l v := fun h => hvc.symm (hc_uniq v h)
      have hge2 : 2 ≤ H.dist l v :=
        hT.connected.one_lt_dist_of_ne_of_not_adj (Ne.symm hvl) hnot_lv
      have hd2 : H.dist l v = 2 := le_antisymm (hdiam l v) hge2
      have hed2 : H.edist l v = 2 := by
        rw [← (hT.connected l v).coe_dist_eq_edist, hd2]
        rfl
      obtain ⟨_, -, ⟨x, hx⟩⟩ := SimpleGraph.edist_eq_two_iff.mp hed2
      rw [SimpleGraph.mem_commonNeighbors] at hx
      have hxc : x = c := hc_uniq x hx.1
      subst hxc
      exact hx.2.symm

/-- **Strict uniqueness of star graphs for `α > 2`** ([TardosWexler2007], Exercise 19.1, locator
not re-verified against primary PDF): when `α > 2`, a connected graph achieves `starSocialCost`
iff it is `SimpleGraph.starGraph c` for some center `c : V`. -/
theorem graphSocialCost_eq_starSocialCost_iff (hα : 2 < G.alpha)
    {H : SimpleGraph V} [DecidableRel H.Adj] (hH : H.Connected) :
    G.graphSocialCost H = G.starSocialCost V ↔ ∃ c : V, H = SimpleGraph.starGraph c := by
  classical
  refine ⟨fun heq => ?_, ?_⟩
  · have := hH.nonempty
    have hge := G.graphSocialCost_ge_of_connected hH
    have hm_ge : Fintype.card V - 1 ≤ H.edgeFinset.card := card_vert_sub_one_le_edgeFinset H hH
    have hm_geR : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
      exact_mod_cast hm_ge
    have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel Fintype.card_pos
    have hm_eqR : (H.edgeFinset.card : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
      unfold starSocialCost at heq
      nlinarith
    have hm_eq : H.edgeFinset.card + 1 = Fintype.card V := by
      have h1 : H.edgeFinset.card = Fintype.card V - 1 := by exact_mod_cast hm_eqR
      have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
      omega
    have hT : H.IsTree := by
      rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      exact ⟨hH, hm_eq⟩
    have hdiam : ∀ u v : V, H.dist u v ≤ 2 := by
      refine (G.graphSocialCost_eq_iff_diam_le_two hH).mp ?_
      rw [heq, hm_eqR]
      unfold starSocialCost
      nlinarith
    exact exists_eq_starGraph_of_isTree_of_diam_le_two hT hdiam
  · rintro ⟨c, hHc⟩
    exact (G.graphSocialCost_congr hHc).trans (G.graphSocialCost_starGraph c)

/-- **Characterization of optimal graphs at `α = 2`** ([TardosWexler2007], Exercise 19.2, locator
not re-verified against primary PDF): at `α = 2`, a connected graph achieves `optSocialCost` iff
it has diameter at most `2`. -/
theorem graphSocialCost_eq_optSocialCost_iff_of_alpha_eq_two (hα : G.alpha = 2)
    {H : SimpleGraph V} [DecidableRel H.Adj] (hH : H.Connected) :
    G.graphSocialCost H = G.optSocialCost V ↔ ∀ u v : V, H.dist u v ≤ 2 := by
  rw [G.optSocialCost_eq_completeSocialCost hα.le, ← G.graphSocialCost_eq_iff_diam_le_two hH]
  unfold completeSocialCost
  rw [hα]
  constructor <;> intro h <;> linarith

/-- **Global optimality of `optSocialCost` over all strategy profiles** (connected or
disconnected): `↑(optSocialCost V) ≤ socialCost s` for every `s : V → Finset V`. -/
theorem coe_optSocialCost_le_socialCost (s : V → Finset V) :
    (G.optSocialCost V : WithTop ℝ) ≤ G.socialCost s := by
  classical
  by_cases hV : Nonempty V
  · by_cases hconn : (formedGraph s).Connected
    · rw [G.socialCost_of_connected hconn, WithTop.coe_le_coe]
      exact (G.optSocialCost_le_graphSocialCost hconn).trans (G.graphSocialCost_formedGraph_le s)
    · rw [G.socialCost_eq_top_of_not_connected hconn]
      exact le_top
  · rw [not_nonempty_iff] at hV
    simp [optSocialCost, completeSocialCost, starSocialCost, socialCost, Fintype.card_eq_zero]

end SocialOptimum

section CanonicalProfilesAndPoS

variable {V : Type*} [Fintype V] (G : NetworkCreationGame)

theorem formedGraph_completeProfile [LinearOrder V] :
    formedGraph (completeProfile (V := V)) = ⊤ := by
  ext u v
  simp only [formedGraph_adj, completeProfile, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.top_adj]
  exact and_iff_left_of_imp fun h => lt_or_gt_of_ne h

theorem connectedSocialCost_completeProfile [LinearOrder V] :
    G.connectedSocialCost (completeProfile (V := V)) = G.completeSocialCost V := by
  rw [G.connectedSocialCost_eq_graphSocialCost_of_clean
    (fun u => by simp [completeProfile])
    (fun u v huv => by
      simp only [completeProfile, Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
      exact lt_asymm huv)]
  exact (G.graphSocialCost_congr formedGraph_completeProfile).trans G.graphSocialCost_top

theorem socialCost_completeProfile [LinearOrder V] :
    G.socialCost (completeProfile (V := V)) = ↑(G.completeSocialCost V) := by
  have hpre : (formedGraph (completeProfile (V := V))).Preconnected := by
    rw [formedGraph_completeProfile]
    exact fun u v => by
      by_cases h : u = v
      · subst h; exact SimpleGraph.Reachable.refl u
      · exact SimpleGraph.Adj.reachable (by simpa using h)
  rw [G.socialCost_of_preconnected hpre, G.connectedSocialCost_completeProfile]

theorem formedGraph_centerStarProfile [DecidableEq V] (c : V) :
    formedGraph (centerStarProfile c) = SimpleGraph.starGraph c := by
  ext u v
  simp only [formedGraph_adj, centerStarProfile, SimpleGraph.starGraph_adj]
  refine and_congr_right fun huv => ?_
  by_cases huc : u = c
  · subst u
    simp [Ne.symm huv]
  · by_cases hvc : v = c
    · subst v
      simp [huc]
    · simp [huc, hvc]

theorem connectedSocialCost_centerStarProfile [DecidableEq V] (c : V) :
    G.connectedSocialCost (centerStarProfile c) = G.starSocialCost V := by
  rw [G.connectedSocialCost_eq_graphSocialCost_of_clean
    (fun u => by by_cases h : u = c <;> simp [centerStarProfile, h])
    (fun u v huv => by
      by_cases huc : u = c
      · subst u
        have hvc : v ≠ c := by simpa [centerStarProfile] using huv
        simp [centerStarProfile, hvc]
      · simp [centerStarProfile, huc] at huv)]
  exact (G.graphSocialCost_congr (formedGraph_centerStarProfile c)).trans
    (G.graphSocialCost_starGraph c)

theorem socialCost_centerStarProfile [DecidableEq V] (c : V) :
    G.socialCost (centerStarProfile c) = ↑(G.starSocialCost V) := by
  have hconn : (formedGraph (centerStarProfile c)).Connected := by
    rw [formedGraph_centerStarProfile]
    exact SimpleGraph.connected_starGraph c
  rw [G.socialCost_of_connected hconn, G.connectedSocialCost_centerStarProfile]

omit [Fintype V] in
theorem formedGraph_leafStarProfile [DecidableEq V] (c : V) :
    formedGraph (leafStarProfile c) = SimpleGraph.starGraph c := by
  ext u v
  simp only [formedGraph_adj, leafStarProfile, SimpleGraph.starGraph_adj]
  refine and_congr_right fun huv => ?_
  by_cases huc : u = c
  · subst u
    simp [Ne.symm huv]
  · by_cases hvc : v = c
    · subst v
      simp [huc]
    · simp [huc, hvc]

theorem connectedSocialCost_leafStarProfile [DecidableEq V] (c : V) :
    G.connectedSocialCost (leafStarProfile c) = G.starSocialCost V := by
  rw [G.connectedSocialCost_eq_graphSocialCost_of_clean
    (fun u => by by_cases h : u = c <;> simp [leafStarProfile, h])
    (fun u v huv => by
      by_cases huc : u = c
      · simp [leafStarProfile, huc] at huv
      · have hvc : v = c := by simpa [leafStarProfile, huc] using huv
        subst v
        simp [leafStarProfile])]
  exact (G.graphSocialCost_congr (formedGraph_leafStarProfile c)).trans
    (G.graphSocialCost_starGraph c)

theorem socialCost_leafStarProfile [DecidableEq V] (c : V) :
    G.socialCost (leafStarProfile c) = ↑(G.starSocialCost V) := by
  have hconn : (formedGraph (leafStarProfile c)).Connected := by
    rw [formedGraph_leafStarProfile]
    exact SimpleGraph.connected_starGraph c
  rw [G.socialCost_of_connected hconn, G.connectedSocialCost_leafStarProfile]

/-- `optSocialCost V` is attained by an explicit strategy profile on `V`. -/
theorem exists_socialCost_eq_optSocialCost :
    ∃ s : V → Finset V, G.socialCost s = ↑(G.optSocialCost V) := by
  classical
  by_cases hV : Nonempty V
  · rcases le_total G.alpha 2 with hα | hα
    · let e := Fintype.equivFin V
      let lo : LinearOrder V := LinearOrder.lift' e e.injective
      refine ⟨@completeProfile V _ lo, ?_⟩
      rw [G.optSocialCost_eq_completeSocialCost hα]
      exact @socialCost_completeProfile V _ G lo
    · obtain ⟨c⟩ := hV
      refine ⟨centerStarProfile c, ?_⟩
      rw [G.socialCost_centerStarProfile c, G.optSocialCost_eq_starSocialCost hα]
  · rw [not_nonempty_iff] at hV
    refine ⟨fun x => hV.elim x, ?_⟩
    simp [optSocialCost, completeSocialCost, starSocialCost, socialCost, Fintype.card_eq_zero]

/-- **Complete graph pure Nash equilibrium (`α ≤ 1`)** ([TardosWexler2007], Lemma 19.2, locator not
re-verified against primary PDF): for `α ≤ 1`, `completeProfile` is a pure Nash equilibrium. -/
theorem isPureNash_completeProfile [LinearOrder V] (hα : G.alpha ≤ 1) :
    G.IsPureNash (completeProfile (V := V)) := by
  intro u t
  let s := completeProfile (V := V)
  let s' := Function.update s u t
  have hreach_s : ∀ v, (formedGraph s).Reachable u v := fun v => by
    rw [formedGraph_completeProfile]
    by_cases h : u = v
    · subst h; exact SimpleGraph.Reachable.refl u
    · exact SimpleGraph.Adj.reachable (by simpa using h)
  rw [G.playerCost_of_forall_reachable hreach_s]
  by_cases hreach' : ∀ v, (formedGraph s').Reachable u v
  · rw [G.playerCost_of_forall_reachable hreach', WithTop.coe_le_coe]
    unfold connectedPlayerCost
    have hdist_s : ∑ v : V, ((formedGraph s).dist u v : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
      rw [formedGraph_completeProfile]
      have hpt : ∀ v : V, ((⊤ : SimpleGraph V).dist u v : ℝ) = if v = u then 0 else 1 := fun v => by
        by_cases hv : v = u
        · subst hv; simp
        · have hadj : (⊤ : SimpleGraph V).Adj u v := by simpa using Ne.symm hv
          simp [hv, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
      simp only [hpt]
      have heq : (∑ v : V, if v = u then (0 : ℝ) else 1) =
          ∑ _v ∈ Finset.univ.erase u, (1 : ℝ) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
        simp only [↓reduceIte, add_zero]
        refine Finset.sum_congr rfl fun v hv => ?_
        have hne : v ≠ u := Finset.ne_of_mem_erase hv
        simp [hne]
      rw [heq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
        nsmul_eq_mul, mul_one]
    have hpt_s' : ∀ v : V,
        (if v = u then (0 : ℝ) else 1) + (if v ∈ s u \ t then 1 else 0) ≤
          ((formedGraph s').dist u v : ℝ) := fun v => by
      by_cases hvu : v = u
      · subst hvu
        simp [s, completeProfile]
      · by_cases hdrop : v ∈ s u \ t
        · simp only [hvu, ↓reduceIte, hdrop]
          rw [Finset.mem_sdiff] at hdrop
          have huv_lt : u < v := by simpa [s, completeProfile] using hdrop.1
          have hnadj : ¬ (formedGraph s').Adj u v := by
            rw [formedGraph_adj]
            rintro ⟨-, hvt | huv'⟩
            · dsimp only [s'] at hvt
              rw [Function.update_self] at hvt
              exact hdrop.2 hvt
            · dsimp only [s'] at huv'
              rw [Function.update_of_ne hvu] at huv'
              simp only [s, completeProfile, Finset.mem_filter, Finset.mem_univ, true_and] at huv'
              exact lt_asymm huv_lt huv'
          have h2 := (hreach' v).one_lt_dist_of_ne_of_not_adj (Ne.symm hvu) hnadj
          exact_mod_cast (by omega : 2 ≤ (formedGraph s').dist u v)
        · simp only [hvu, ↓reduceIte, hdrop, add_zero]
          exact_mod_cast (hreach' v).pos_dist_of_ne (Ne.symm hvu)
    have hsum_s' : ((Fintype.card V - 1 : ℕ) : ℝ) + ((s u \ t).card : ℝ) ≤
        ∑ v : V, ((formedGraph s').dist u v : ℝ) := by
      have h1 := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt_s' v
      rw [Finset.sum_add_distrib] at h1
      have ha : (∑ v : V, if v = u then (0 : ℝ) else 1) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
        simp only [↓reduceIte, add_zero]
        have : (∑ v ∈ Finset.univ.erase u, if v = u then (0 : ℝ) else 1) =
            ∑ _v ∈ Finset.univ.erase u, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv => by
            have hne : v ≠ u := Finset.ne_of_mem_erase hv
            simp [hne]
        rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
          Finset.card_univ, nsmul_eq_mul, mul_one]
      have hb : (∑ v : V, if v ∈ s u \ t then (1 : ℝ) else 0) = ((s u \ t).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      linarith
    have hcards : (s u).card ≤ t.card + (s u \ t).card := by
      calc (s u).card
        _ = (s u ∩ t).card + (s u \ t).card := (Finset.card_inter_add_card_sdiff (s u) t).symm
        _ ≤ t.card + (s u \ t).card :=
            Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_right) _
    have hcardsR : ((s u).card : ℝ) ≤ (t.card : ℝ) + ((s u \ t).card : ℝ) := by
      exact_mod_cast hcards
    have hdrop_nonneg : (0 : ℝ) ≤ ((s u \ t).card : ℝ) := Nat.cast_nonneg _
    have hs'_self : s' u = t := Function.update_self u t s
    rw [hdist_s, hs'_self]
    nlinarith [G.alpha_pos]
  · rw [G.playerCost_eq_top_iff.mpr (not_forall.mp hreach')]
    exact le_top

omit [Fintype V] in
private lemma star_center_dist_le [DecidableEq V] {s : V → Finset V} {u : V} {t : Finset V}
    (hs : formedGraph s = SimpleGraph.starGraph u)
    (hreach' : ∀ v, (formedGraph (Function.update s u t)).Reachable u v) (v : V) :
    ((formedGraph s).dist u v : ℝ) ≤ ((formedGraph (Function.update s u t)).dist u v : ℝ) := by
  by_cases hvu : u = v
  · subst v; simp
  · have hd1 : (formedGraph s).dist u v = 1 := by
      rw [hs]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr (SimpleGraph.starGraph_center_adj hvu)
    rw [hd1]
    exact_mod_cast (hreach' v).pos_dist_of_ne hvu

omit [Fintype V] in
private lemma star_leaf_dist_sub_le_ite [DecidableEq V] {s : V → Finset V} {c u v : V}
    {t : Finset V} (hs : formedGraph s = SimpleGraph.starGraph c) (hvu : u ≠ v) (hns : u ∉ s v)
    (hr : (formedGraph (Function.update s u t)).Reachable u v) :
    ((formedGraph s).dist u v : ℝ) - ((formedGraph (Function.update s u t)).dist u v : ℝ) ≤
      if v ∈ t then 1 else 0 := by
  have hd2 : ((formedGraph s).dist u v : ℝ) ≤ 2 := by
    rw [hs]
    exact_mod_cast starGraph_dist_le_two c u v
  by_cases hvt : v ∈ t
  · simp only [hvt, ↓reduceIte]
    have hd1' : (1 : ℝ) ≤ ((formedGraph (Function.update s u t)).dist u v : ℝ) := by
      exact_mod_cast hr.pos_dist_of_ne hvu
    linarith
  · simp only [hvt, ↓reduceIte]
    have hnadj : ¬ (formedGraph (Function.update s u t)).Adj u v := by
      rw [formedGraph_adj]
      rintro ⟨-, hv1 | hu1⟩
      · rw [Function.update_self] at hv1
        exact hvt hv1
      · rw [Function.update_of_ne (Ne.symm hvu)] at hu1
        exact hns hu1
    have hd2' : (2 : ℝ) ≤ ((formedGraph (Function.update s u t)).dist u v : ℝ) := by
      exact_mod_cast hr.one_lt_dist_of_ne_of_not_adj hvu hnadj
    linarith

/-- **Center-sponsored star pure Nash equilibrium (`α ≥ 1`)** ([TardosWexler2007], Lemma 19.2,
locator not re-verified against primary PDF). -/
theorem isPureNash_centerStarProfile [DecidableEq V] (c : V) (hα : 1 ≤ G.alpha) :
    G.IsPureNash (centerStarProfile c) := by
  intro u t
  let s := centerStarProfile c
  let s' := Function.update s u t
  have hconn_s : (formedGraph s).Connected := by
    rw [formedGraph_centerStarProfile]
    exact SimpleGraph.connected_starGraph c
  rw [G.playerCost_of_connected hconn_s]
  by_cases hreach' : ∀ v, (formedGraph s').Reachable u v
  · rw [G.playerCost_of_forall_reachable hreach', WithTop.coe_le_coe]
    unfold connectedPlayerCost
    have hs'_self : s' u = t := Function.update_self u t s
    rw [hs'_self]
    by_cases huc : u = c
    · subst huc
      have hsub : Finset.univ.erase u ⊆ t := by
        intro v hv
        have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
        by_contra hvt
        have hiso : ∀ w, ¬ (formedGraph s').Adj w v := by
          intro w hadj
          rw [formedGraph_adj] at hadj
          rcases hadj.2 with hw | hv'
          · by_cases hwu : w = u
            · subst hwu
              dsimp only [s'] at hw
              rw [Function.update_self] at hw
              exact hvt hw
            · dsimp only [s'] at hw
              rw [Function.update_of_ne hwu] at hw
              simp [s, centerStarProfile, hwu] at hw
          · dsimp only [s'] at hv'
            rw [Function.update_of_ne hvu] at hv'
            simp [s, centerStarProfile, hvu] at hv'
        obtain ⟨p⟩ := (hreach' v).symm
        cases p with
        | nil => exact hvu rfl
        | @cons _ w _ hadj _ => exact hiso w hadj.symm
      have hcard : ((s u).card : ℝ) ≤ (t.card : ℝ) := by
        have hsu : s u = Finset.univ.erase u := by simp [s, centerStarProfile]
        rw [hsu]
        exact_mod_cast Finset.card_le_card hsub
      have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
        star_center_dist_le (formedGraph_centerStarProfile u) hreach' v
      nlinarith [G.alpha_pos]
    · have hsu : s u = ∅ := by simp [s, centerStarProfile, huc]
      rw [hsu, Finset.card_empty, Nat.cast_zero, mul_zero, zero_add]
      have hpt : ∀ v : V,
          ((formedGraph s).dist u v : ℝ) - ((formedGraph s').dist u v : ℝ) ≤
            if v ∈ t then 1 else 0 := fun v => by
        by_cases hvu : u = v
        · subst v
          by_cases hut : u ∈ t <;> simp [hut]
        · by_cases hvc : v = c
          · subst v
            have hd1 : (formedGraph s).dist u c = 1 := by
              rw [formedGraph_centerStarProfile]
              exact SimpleGraph.dist_eq_one_iff_adj.mpr
                (SimpleGraph.starGraph_center_adj' (Ne.symm huc))
            have hd1' : 1 ≤ (formedGraph s').dist u c := (hreach' c).pos_dist_of_ne huc
            have hd1R : (1 : ℝ) ≤ ((formedGraph s').dist u c : ℝ) := by exact_mod_cast hd1'
            rw [hd1, Nat.cast_one]
            by_cases hct : c ∈ t <;> simp only [hct, ↓reduceIte] <;> linarith
          · exact star_leaf_dist_sub_le_ite (formedGraph_centerStarProfile c) hvu
              (by simp [s, centerStarProfile, hvc]) (hreach' v)
      have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt v
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
      have ht_nonneg : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
      nlinarith
  · rw [G.playerCost_eq_top_iff.mpr (not_forall.mp hreach')]
    exact le_top

/-- **Leaf-sponsored star pure Nash equilibrium (`α ≥ 1`)** ([TardosWexler2007], Lemma 19.2,
locator not re-verified against primary PDF). -/
theorem isPureNash_leafStarProfile [DecidableEq V] (c : V) (hα : 1 ≤ G.alpha) :
    G.IsPureNash (leafStarProfile c) := by
  intro u t
  let s := leafStarProfile c
  let s' := Function.update s u t
  have hconn_s : (formedGraph s).Connected := by
    rw [formedGraph_leafStarProfile]
    exact SimpleGraph.connected_starGraph c
  rw [G.playerCost_of_connected hconn_s]
  by_cases hreach' : ∀ v, (formedGraph s').Reachable u v
  · rw [G.playerCost_of_forall_reachable hreach', WithTop.coe_le_coe]
    unfold connectedPlayerCost
    have hs'_self : s' u = t := Function.update_self u t s
    rw [hs'_self]
    by_cases huc : u = c
    · subst huc
      have hsu : s u = ∅ := by simp [s, leafStarProfile]
      rw [hsu, Finset.card_empty, Nat.cast_zero, mul_zero, zero_add]
      have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
        star_center_dist_le (formedGraph_leafStarProfile u) hreach' v
      have ht_nonneg : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
      nlinarith [G.alpha_pos]
    · have hsu : (s u).card = 1 := by simp [s, leafStarProfile, huc]
      rw [hsu, Nat.cast_one, mul_one]
      have ht_pos : 1 ≤ t.card := by
        obtain ⟨p⟩ := hreach' c
        cases p with
        | nil => exact absurd rfl huc
        | @cons _ w _ hadj _ =>
          rw [formedGraph_adj] at hadj
          rcases hadj.2 with hwt | huw
          · dsimp only [s'] at hwt
            rw [Function.update_self] at hwt
            exact Finset.card_pos.mpr ⟨w, hwt⟩
          · dsimp only [s'] at huw
            rw [Function.update_of_ne hadj.1.symm] at huw
            exfalso
            by_cases hwc : w = c
            · simp [s, leafStarProfile, hwc] at huw
            · have : u = c := by simpa [s, leafStarProfile, hwc] using huw
              exact huc this
      have ht_ge1 : (1 : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast ht_pos
      have hpt_other : ∀ v : V, u ≠ v → v ≠ c →
          ((formedGraph s).dist u v : ℝ) - ((formedGraph s').dist u v : ℝ) ≤
            if v ∈ t then 1 else 0 := fun v hvu hvc =>
        star_leaf_dist_sub_le_ite (formedGraph_leafStarProfile c) hvu
          (by simp [s, leafStarProfile, hvc, huc]) (hreach' v)
      by_cases hct : c ∈ t
      · have hpt : ∀ v : V,
            ((formedGraph s).dist u v : ℝ) - ((formedGraph s').dist u v : ℝ) ≤
              if v ∈ t.erase c then 1 else 0 := fun v => by
          by_cases hvu : u = v
          · subst v
            by_cases hm : u ∈ t.erase c <;> simp [hm]
          · by_cases hvc : v = c
            · subst v
              simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
              have hd1 : (formedGraph s).dist u c = 1 := by
                rw [formedGraph_leafStarProfile]
                exact SimpleGraph.dist_eq_one_iff_adj.mpr
                  (SimpleGraph.starGraph_center_adj' (Ne.symm huc))
              have hd1' : (1 : ℝ) ≤ ((formedGraph s').dist u c : ℝ) := by
                exact_mod_cast (hreach' c).pos_dist_of_ne huc
              rw [hd1, Nat.cast_one]
              linarith
            · have hmem_iff : v ∈ t.erase c ↔ v ∈ t := by simp [Finset.mem_erase, hvc]
              simpa only [hmem_iff] using hpt_other v hvu hvc
        have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt v
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
        have herase : ((t.erase c).card : ℝ) + 1 = (t.card : ℝ) := by
          exact_mod_cast Finset.card_erase_add_one hct
        nlinarith
      · have hpt : ∀ v : V,
            ((formedGraph s).dist u v : ℝ) - ((formedGraph s').dist u v : ℝ) ≤
              (if v ∈ t then 1 else 0) - (if v = c then 1 else 0) := fun v => by
          by_cases hvu : u = v
          · subst v
            simp only [huc, ↓reduceIte, sub_zero]
            by_cases hut : u ∈ t <;> simp [hut]
          · by_cases hvc : v = c
            · subst v
              simp only [hct, ↓reduceIte, zero_sub]
              have hd1 : (formedGraph s).dist u c = 1 := by
                rw [formedGraph_leafStarProfile]
                exact SimpleGraph.dist_eq_one_iff_adj.mpr
                  (SimpleGraph.starGraph_center_adj' (Ne.symm huc))
              have hnadj : ¬ (formedGraph s').Adj u c := by
                rw [formedGraph_adj]
                rintro ⟨-, hc1 | hu1⟩
                · dsimp only [s'] at hc1
                  rw [Function.update_self] at hc1
                  exact hct hc1
                · dsimp only [s'] at hu1
                  rw [Function.update_of_ne (Ne.symm huc)] at hu1
                  simp [s, leafStarProfile] at hu1
              have hd2' : (2 : ℝ) ≤ ((formedGraph s').dist u c : ℝ) := by
                exact_mod_cast (hreach' c).one_lt_dist_of_ne_of_not_adj huc hnadj
              rw [hd1, Nat.cast_one]
              linarith
            · simp only [hvc, ↓reduceIte, sub_zero]
              exact hpt_other v hvu hvc
        have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt v
        simp only [Finset.sum_sub_distrib] at hsum
        have ha : (∑ v : V, if v ∈ t then (1 : ℝ) else 0) = (t.card : ℝ) := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul, mul_one]
        have hb : (∑ v : V, if v = c then (1 : ℝ) else 0) = 1 := by simp
        rw [ha, hb] at hsum
        nlinarith
  · rw [G.playerCost_eq_top_iff.mpr (not_forall.mp hreach')]
    exact le_top

/-- For all `1 ≤ α`, `starSocialCost V ≤ (4 / 3) * optSocialCost V`. -/
theorem starSocialCost_le_four_thirds_optSocialCost (hα : 1 ≤ G.alpha) :
    G.starSocialCost V ≤ 4 / 3 * G.optSocialCost V := by
  rcases le_total G.alpha 2 with hα2 | hα2
  · rw [G.optSocialCost_eq_completeSocialCost hα2]
    rcases le_or_gt (Fintype.card V) 1 with hn | hn
    · have hn1 : Fintype.card V - 1 = 0 := by omega
      simp [starSocialCost, completeSocialCost, hn1]
    · have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      have hn1_nn : (0 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hn1_eq : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      unfold starSocialCost completeSocialCost
      have hlin : G.alpha + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) ≤
          4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ)) := by
        rw [hn1_eq]
        nlinarith
      calc ((Fintype.card V - 1 : ℕ) : ℝ) * (G.alpha + 2 * ((Fintype.card V - 1 : ℕ) : ℝ))
        _ ≤ ((Fintype.card V - 1 : ℕ) : ℝ) *
            (4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ))) :=
            mul_le_mul_of_nonneg_left hlin hn1_nn
        _ = 4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ) *
            ((Fintype.card V - 1 : ℕ) : ℝ)) := by ring
  · rw [G.optSocialCost_eq_starSocialCost hα2]
    have hnn := G.optSocialCost_nonneg V
    rw [G.optSocialCost_eq_starSocialCost hα2] at hnn
    linarith

/-- Strict `< 4 / 3` Price-of-Stability bound on `1 ≤ α ≤ 2` when `|V| ≥ 2`
([TardosWexler2007], Theorem 19.3, locator not re-verified against primary PDF). -/
theorem starSocialCost_lt_four_thirds_optSocialCost [Nontrivial V] (hα1 : 1 ≤ G.alpha)
    (hα2 : G.alpha ≤ 2) : G.starSocialCost V < 4 / 3 * G.optSocialCost V := by
  rw [G.optSocialCost_eq_completeSocialCost hα2]
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < ((Fintype.card V - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card V - 1)
  have hn1_eq : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold starSocialCost completeSocialCost
  have hlin : G.alpha + 2 * ((Fintype.card V - 1 : ℕ) : ℝ) <
      4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ)) := by
    rw [hn1_eq]
    nlinarith
  calc ((Fintype.card V - 1 : ℕ) : ℝ) * (G.alpha + 2 * ((Fintype.card V - 1 : ℕ) : ℝ))
    _ < ((Fintype.card V - 1 : ℕ) : ℝ) *
        (4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ))) :=
        mul_lt_mul_of_pos_left hlin hn1_pos
    _ = 4 / 3 * ((G.alpha / 2 + 1) * (Fintype.card V : ℝ) *
        ((Fintype.card V - 1 : ℕ) : ℝ)) := by ring

/-- **Price of Stability = 1** outside `(1, 2)` ([TardosWexler2007], Theorem 19.3, locator not
re-verified against primary PDF). -/
theorem exists_isPureNash_socialCost_eq_optSocialCost [DecidableEq V]
    (hα : G.alpha ≤ 1 ∨ 2 ≤ G.alpha) :
    ∃ s : V → Finset V, G.IsPureNash s ∧ G.connectedSocialCost s = G.optSocialCost V := by
  rcases hα with h1 | h2
  · let e := Fintype.equivFin V
    let lo : LinearOrder V := LinearOrder.lift' e e.injective
    have hs : G.IsPureNash (@completeProfile V _ lo) := by
      convert @isPureNash_completeProfile V _ G lo h1
    refine ⟨@completeProfile V _ lo, hs, ?_⟩
    rw [G.optSocialCost_eq_completeSocialCost (h1.trans (by norm_num))]
    exact @connectedSocialCost_completeProfile V _ G lo
  · by_cases hV : Nonempty V
    · obtain ⟨c⟩ := hV
      exact ⟨centerStarProfile c, G.isPureNash_centerStarProfile c (by linarith),
        (G.connectedSocialCost_centerStarProfile c).trans
          (G.optSocialCost_eq_starSocialCost h2).symm⟩
    · rw [not_nonempty_iff] at hV
      refine ⟨fun x => hV.elim x, fun x => hV.elim x, ?_⟩
      simp [connectedSocialCost, optSocialCost, completeSocialCost, starSocialCost,
        Fintype.card_eq_zero]

/-- **Price of Stability ≤ 4 / 3** for all `α > 0` ([TardosWexler2007], Theorem 19.3, locator not
re-verified against primary PDF). -/
theorem exists_isPureNash_socialCost_le_four_thirds [DecidableEq V] :
    ∃ s : V → Finset V, G.IsPureNash s ∧
      G.connectedSocialCost s ≤ 4 / 3 * G.optSocialCost V := by
  rcases le_or_gt G.alpha 1 with hα | hα
  · obtain ⟨s, hs, heq⟩ := G.exists_isPureNash_socialCost_eq_optSocialCost (V := V) (Or.inl hα)
    refine ⟨s, hs, ?_⟩
    have hnn := G.optSocialCost_nonneg V
    linarith
  · by_cases hV : Nonempty V
    · obtain ⟨c⟩ := hV
      exact ⟨centerStarProfile c, G.isPureNash_centerStarProfile c hα.le,
        (G.connectedSocialCost_centerStarProfile c).trans_le
          (G.starSocialCost_le_four_thirds_optSocialCost hα.le)⟩
    · rw [not_nonempty_iff] at hV
      refine ⟨fun x => hV.elim x, fun x => hV.elim x, ?_⟩
      simp [connectedSocialCost, optSocialCost, completeSocialCost, starSocialCost,
        Fintype.card_eq_zero]

end CanonicalProfilesAndPoS

section PriceOfAnarchySmallAlpha

variable {V : Type*} [Fintype V] [DecidableEq V] {G : NetworkCreationGame} {s : V → Finset V}

/-- At any pure Nash equilibrium, distinct vertices `u ≠ v` satisfy `dist u v ≤ α + 1`: otherwise
`u` could buy `{u, v}` to reduce `dist u v` to `1` and strictly lower its cost. -/
theorem IsPureNash.dist_le_alpha_add_one (hs : G.IsPureNash s) (u v : V) :
    ((formedGraph s).dist u v : ℝ) ≤ G.alpha + 1 := by
  by_cases huv : u = v
  · subst huv
    simp only [SimpleGraph.dist_self, Nat.cast_zero]
    linarith [G.alpha_pos]
  · have h := hs.sum_dist_sub_le_alpha u v {v}
    rw [Finset.sum_singleton] at h
    have hadj' : (formedGraph (Function.update s u (insert v (s u)))).Adj u v := by
      rw [formedGraph_adj]
      exact ⟨huv, Or.inl (by simp)⟩
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj', Nat.cast_one] at h
    linarith

/-- **Uniqueness of `K_n` for `α < 1`** ([TardosWexler2007], Exercise 19.3, locator not re-verified
against primary PDF): when `α < 1`, every pure Nash equilibrium forms the complete graph `⊤`. -/
theorem IsPureNash.formedGraph_eq_top_of_alpha_lt_one (hs : G.IsPureNash s) (hα : G.alpha < 1) :
    formedGraph s = ⊤ := by
  ext u v
  simp only [SimpleGraph.top_adj]
  refine ⟨fun h => h.ne, fun huv => ?_⟩
  have hd : ((formedGraph s).dist u v : ℝ) < 2 := by
    linarith [hs.dist_le_alpha_add_one u v]
  have hd_nat : (formedGraph s).dist u v < 2 := by exact_mod_cast hd
  have hd_pos : 0 < (formedGraph s).dist u v := (hs.forall_reachable u v).pos_dist_of_ne huv
  exact SimpleGraph.dist_eq_one_iff_adj.mp (by omega)

/-- **`PoA = 1` for `α < 1`** ([TardosWexler2007], Exercise 19.3, locator not re-verified against
primary PDF): every pure Nash equilibrium achieves the optimal social cost when `α < 1`. -/
theorem IsPureNash.socialCost_eq_opt_of_alpha_lt_one (hs : G.IsPureNash s) (hα : G.alpha < 1) :
    G.connectedSocialCost s = G.optSocialCost V := by
  rw [hs.connectedSocialCost_eq_graphSocialCost,
    G.optSocialCost_eq_completeSocialCost (by linarith)]
  exact (G.graphSocialCost_congr (hs.formedGraph_eq_top_of_alpha_lt_one hα)).trans
    G.graphSocialCost_top

/-- When `α < 2`, every pure Nash equilibrium has diameter at most `2`. -/
theorem IsPureNash.dist_le_two_of_alpha_lt_two (hs : G.IsPureNash s) (hα : G.alpha < 2)
    (u v : V) : (formedGraph s).dist u v ≤ 2 := by
  have hd : ((formedGraph s).dist u v : ℝ) < 3 := by
    linarith [hs.dist_le_alpha_add_one u v]
  have hd_nat : (formedGraph s).dist u v < 3 := by exact_mod_cast hd
  omega

/-- **`PoA ≤ 4 / 3` for `α < 2`** (in particular on `1 ≤ α < 2`): every pure Nash equilibrium has
diameter at most `2`, hence social cost at most `starSocialCost ≤ (4 / 3) · OPT`. -/
theorem IsPureNash.socialCost_le_four_thirds_of_alpha_lt_two (hs : G.IsPureNash s)
    (hα : G.alpha < 2) : G.connectedSocialCost s ≤ 4 / 3 * G.optSocialCost V := by
  rcases lt_or_ge G.alpha 1 with hα1 | hα1
  · rw [hs.socialCost_eq_opt_of_alpha_lt_one hα1]
    have hnn := G.optSocialCost_nonneg V
    linarith
  · by_cases hV : Nonempty V
    · have hconn := hs.connected
      have heq := (G.graphSocialCost_eq_iff_diam_le_two hconn).mpr
        (hs.dist_le_two_of_alpha_lt_two hα)
      have hm : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((formedGraph s).edgeFinset.card : ℝ) := by
        exact_mod_cast card_vert_sub_one_le_edgeFinset (formedGraph s) hconn
      have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel Fintype.card_pos
      have hle_star : G.connectedSocialCost s ≤ G.starSocialCost V := by
        rw [hs.connectedSocialCost_eq_graphSocialCost, heq]
        unfold starSocialCost
        nlinarith
      exact hle_star.trans (G.starSocialCost_le_four_thirds_optSocialCost hα1)
    · rw [not_nonempty_iff] at hV
      simp [connectedSocialCost, optSocialCost, completeSocialCost, starSocialCost,
        Fintype.card_eq_zero]

end PriceOfAnarchySmallAlpha

section TreeEquilibria

variable {V : Type*} [Fintype V]

/-- In a tree `T`, if `u ∈ edgeSide T a b` and `v ∉ edgeSide T a b`, every walk from `u` to `v`
crosses `s(a, b)` and `T.dist u v = T.dist u b + T.dist b v`. -/
private theorem dist_eq_add_of_edgeSide {T : SimpleGraph V} (hT : T.IsTree) {a b u v : V}
    (hu : u ∈ SimpleGraph.edgeSide T a b) (hv : v ∉ SimpleGraph.edgeSide T a b) :
    T.dist u v = T.dist u b + T.dist b v := by
  classical
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist u v
  have he : s(a, b) ∈ p.edges := by
    by_contra hnot
    have hr : (T.deleteEdges {s(a, b)}).Reachable u v :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hnot⟩
    exact hv (SimpleGraph.mem_edgeSide.mpr ((SimpleGraph.mem_edgeSide.mp hu).trans hr))
  have hb : b ∈ p.support := p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)
  have hlen : (p.takeUntil b hb).length + (p.dropUntil b hb).length = T.dist u v := by
    rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec p hb, hp]
  have h1 : T.dist u b ≤ (p.takeUntil b hb).length := T.dist_le _
  have h2 : T.dist b v ≤ (p.dropUntil b hb).length := T.dist_le _
  have htri : T.dist u v ≤ T.dist u b + T.dist b v := hT.connected.dist_triangle
  omega

/-- **Centroid of a finite tree**: a vertex `c` minimizing `∑ x, T.dist c x` satisfies
`2 · |edgeSide T w c| ≤ |V|` for every neighbor `w` of `c`. -/
private theorem exists_tree_centroid {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ c : V, ∀ w : V, T.Adj c w → 2 * (SimpleGraph.edgeSide T w c).card ≤ Fintype.card V := by
  classical
  have := hT.connected.nonempty
  obtain ⟨c, hc⟩ := Finite.exists_min fun u : V => ∑ x : V, (T.dist u x : ℤ)
  refine ⟨c, fun w hcw => ?_⟩
  let S := SimpleGraph.edgeSide T w c
  have hpt : ∀ x : V, (T.dist w x : ℤ) - (T.dist c x : ℤ) = if x ∈ S then -1 else 1 := fun x => by
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte]
      have hcx : x ∉ SimpleGraph.edgeSide T c w :=
        (SimpleGraph.mem_edgeSide_swap hT hcw x).mp hx
      have hd := dist_eq_add_of_edgeSide hT (SimpleGraph.mem_edgeSide_self c w) hcx
      have hcw1 : T.dist c w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcw
      omega
    · simp only [hx, ↓reduceIte]
      have hd := dist_eq_add_of_edgeSide hT (SimpleGraph.mem_edgeSide_self w c) hx
      have hwc1 : T.dist w c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcw.symm
      omega
  have hmin : (0 : ℤ) ≤ (∑ x : V, (T.dist w x : ℤ)) - ∑ x : V, (T.dist c x : ℤ) :=
    sub_nonneg.mpr (hc w)
  rw [← Finset.sum_sub_distrib] at hmin
  simp only [hpt] at hmin
  have hsum : (∑ x : V, if x ∈ S then (-1 : ℤ) else 1) =
      (Fintype.card V : ℤ) - 2 * (S.card : ℤ) := by
    have heq : ∀ x : V, (if x ∈ S then (-1 : ℤ) else 1) = 1 - if x ∈ S then 2 else 0 := fun x => by
      split_ifs <;> rfl
    simp only [heq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  rw [hsum] at hmin
  change 2 * S.card ≤ Fintype.card V
  omega

/-- **Tree equilibria Price of Anarchy ≤ 5** (Fabrikant–Luthra–Maneva–Papadimitriou–Shenker 2003,
Theorem 2; locator not re-verified against primary PDF): if `s` is a pure Nash equilibrium whose
formed graph is a tree, then `connectedSocialCost s ≤ 5 * optSocialCost V`. -/
theorem IsPureNash.socialCost_le_five_of_isTree [DecidableEq V] {G : NetworkCreationGame}
    {s : V → Finset V} (hs : G.IsPureNash s) (hT : (formedGraph s).IsTree) :
    G.connectedSocialCost s ≤ 5 * G.optSocialCost V := by
  rcases lt_or_ge G.alpha 2 with hα2 | hα2
  · have h43 := hs.socialCost_le_four_thirds_of_alpha_lt_two hα2
    have hnn := G.optSocialCost_nonneg V
    linarith
  · rcases le_or_gt (Fintype.card V) 1 with hn | hn
    · have hn1 : Fintype.card V - 1 = 0 := by omega
      have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn
      rw [hs.connectedSocialCost_eq_graphSocialCost, G.optSocialCost_eq_starSocialCost hα2]
      have hm : (formedGraph s).edgeFinset.card = 0 := by
        have hc := hT.card_edgeFinset
        omega
      have hd : ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) = 0 :=
        Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
          rw [Subsingleton.elim u v, SimpleGraph.dist_self, Nat.cast_zero]
      simp [graphSocialCost, starSocialCost, hm, hd, hn1]
    · obtain ⟨c, hc⟩ := exists_tree_centroid hT
      have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast (by omega : 0 < Fintype.card V)
      have hdist_c : ∀ u : V, u ≠ c →
          ((formedGraph s).dist u c : ℝ) ≤ 1 + 2 * G.alpha / (Fintype.card V : ℝ) := by
        intro u huc
        obtain ⟨q, hq_path, _⟩ := hT.connected.exists_path_of_dist c u
        cases q with
        | nil => exact absurd rfl huc.symm
        | @cons _ w _ hcw q' =>
          have hd_mem : (⟨(c, w), hcw⟩ : (formedGraph s).Dart) ∈
              (SimpleGraph.Walk.cons hcw q').darts := by simp
          have hside := SimpleGraph.mem_edgeSide_of_mem_darts hT.isAcyclic hq_path hd_mem
          have hu_side : u ∈ SimpleGraph.edgeSide (formedGraph s) w c :=
            (SimpleGraph.mem_edgeSide_swap hT hcw u).mpr hside.2
          let S := SimpleGraph.edgeSide (formedGraph s) c w
          have hS_card : (Fintype.card V : ℝ) ≤ 2 * (S.card : ℝ) := by
            have hcompl : S = (SimpleGraph.edgeSide (formedGraph s) w c)ᶜ :=
              SimpleGraph.edgeSide_swap hT hcw.symm
            have hadd : S.card + (SimpleGraph.edgeSide (formedGraph s) w c).card =
                Fintype.card V := by
              rw [hcompl, Finset.card_compl_add_card]
            have hcw_le := hc w hcw
            exact_mod_cast (by omega : Fintype.card V ≤ 2 * S.card)
          let s' := Function.update s u (insert c (s u))
          have hadj_uc : (formedGraph s').Adj u c := by
            rw [formedGraph_adj]
            exact ⟨huc, Or.inl (by simp [s'])⟩
          have hmono : formedGraph s ≤ formedGraph s' := formedGraph_le_update_insert s u c
          have hreach' : ∀ x, (formedGraph s').Reachable u x :=
            fun x => (hT.connected u x).mono hmono
          have hpt : ∀ x ∈ S,
              (((formedGraph s).dist u c : ℝ) - 1) ≤
                ((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ) := by
            intro x hx
            have hx_not : x ∉ SimpleGraph.edgeSide (formedGraph s) w c :=
              (SimpleGraph.mem_edgeSide_swap hT hcw.symm x).mp hx
            have hux_eq : (formedGraph s).dist u x =
                (formedGraph s).dist u c + (formedGraph s).dist c x :=
              dist_eq_add_of_edgeSide hT hu_side hx_not
            have hcx_le : (formedGraph s').dist c x ≤ (formedGraph s).dist c x := by
              have he := SimpleGraph.edist_anti hmono (u := c) (v := x)
              rw [← ((hreach' c).symm.trans (hreach' x)).coe_dist_eq_edist,
                ← (hT.connected c x).coe_dist_eq_edist] at he
              exact_mod_cast he
            have hux'_le : (formedGraph s').dist u x ≤ 1 + (formedGraph s).dist c x := by
              have htri := (hreach' c).dist_triangle_left x
              have huc1 : (formedGraph s').dist u c = 1 :=
                SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uc
              omega
            have hux_eqR : ((formedGraph s).dist u x : ℝ) =
                ((formedGraph s).dist u c : ℝ) + ((formedGraph s).dist c x : ℝ) := by
              exact_mod_cast hux_eq
            have hux'_leR : ((formedGraph s').dist u x : ℝ) ≤
                1 + ((formedGraph s).dist c x : ℝ) := by
              exact_mod_cast hux'_le
            linarith
          have hsum_ge : (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤
              ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ)) := by
            calc (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1)
              _ = ∑ _x ∈ S, (((formedGraph s).dist u c : ℝ) - 1) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ)) :=
                  Finset.sum_le_sum hpt
          have hsum_le := hs.sum_dist_sub_le_alpha u c S
          have hmul : (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤ G.alpha :=
            hsum_ge.trans hsum_le
          rcases le_or_gt (((formedGraph s).dist u c : ℝ) - 1) 0 with hnonpos | hpos
          · have hdiv_nn : 0 ≤ 2 * G.alpha / (Fintype.card V : ℝ) := by
              have := G.alpha_pos
              positivity
            linarith
          · have hn_mul : (Fintype.card V : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤
                2 * G.alpha := by
              nlinarith
            have hdiv : ((formedGraph s).dist u c : ℝ) - 1 ≤
                2 * G.alpha / (Fintype.card V : ℝ) :=
              (le_div_iff₀ hn_pos).mpr (by linarith)
            linarith
      have hsum_uc : ∑ u : V, ((formedGraph s).dist u c : ℝ) ≤
          ((Fintype.card V - 1 : ℕ) : ℝ) * (1 + 2 * G.alpha / (Fintype.card V : ℝ)) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
        simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
        calc ∑ u ∈ Finset.univ.erase c, ((formedGraph s).dist u c : ℝ)
          _ ≤ ∑ _u ∈ Finset.univ.erase c, (1 + 2 * G.alpha / (Fintype.card V : ℝ)) :=
              Finset.sum_le_sum fun u hu => hdist_c u (Finset.ne_of_mem_erase hu)
          _ = ((Fintype.card V - 1 : ℕ) : ℝ) * (1 + 2 * G.alpha / (Fintype.card V : ℝ)) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c),
                Finset.card_univ, nsmul_eq_mul]
      have hpair_sum : ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) ≤
          2 * ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ u : V, ((formedGraph s).dist u c : ℝ) := by
        have hinner : ∀ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) ≤
            ((Fintype.card V - 1 : ℕ) : ℝ) * ((formedGraph s).dist u c : ℝ) +
              ∑ v ∈ Finset.univ.erase u, ((formedGraph s).dist v c : ℝ) := fun u => by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
          simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
          calc ∑ v ∈ Finset.univ.erase u, ((formedGraph s).dist u v : ℝ)
            _ ≤ ∑ v ∈ Finset.univ.erase u,
                (((formedGraph s).dist u c : ℝ) + ((formedGraph s).dist v c : ℝ)) :=
                Finset.sum_le_sum fun v _ => by
                  have htri := hT.connected.dist_triangle (u := u) (v := c) (w := v)
                  rw [SimpleGraph.dist_comm (u := c) (v := v)] at htri
                  exact_mod_cast htri
            _ = ((Fintype.card V - 1 : ℕ) : ℝ) * ((formedGraph s).dist u c : ℝ) +
                ∑ v ∈ Finset.univ.erase u, ((formedGraph s).dist v c : ℝ) := by
                rw [Finset.sum_add_distrib, Finset.sum_const,
                  Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, nsmul_eq_mul]
        have h1 := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hinner u
        rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
        have h2 : (∑ u : V, ∑ v ∈ Finset.univ.erase u, ((formedGraph s).dist v c : ℝ)) =
            ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ v : V, ((formedGraph s).dist v c : ℝ) := by
          have hex : ∀ u : V, (∑ v ∈ Finset.univ.erase u, ((formedGraph s).dist v c : ℝ)) =
              ∑ v : V, if v = u then 0 else ((formedGraph s).dist v c : ℝ) := fun u => by
            rw [← Finset.sum_erase_add (s := Finset.univ) (a := u)
              (f := fun v => if v = u then 0 else ((formedGraph s).dist v c : ℝ))
              (Finset.mem_univ u)]
            simp only [↓reduceIte, add_zero]
            refine Finset.sum_congr rfl fun v hv => ?_
            have hne : v ≠ u := Finset.ne_of_mem_erase hv
            simp [hne]
          simp only [hex]
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
          simp only [↓reduceIte, add_zero]
          have hc_eq : (∑ u ∈ Finset.univ.erase v,
              if v = u then 0 else ((formedGraph s).dist v c : ℝ)) =
              ∑ _u ∈ Finset.univ.erase v, ((formedGraph s).dist v c : ℝ) :=
            Finset.sum_congr rfl fun u hu => by
              have hne : v ≠ u := (Finset.ne_of_mem_erase hu).symm
              simp [hne]
          rw [hc_eq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
            Finset.card_univ, nsmul_eq_mul]
        linarith
      have hm : ((formedGraph s).edgeFinset.card : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
        have hc_edge := hT.card_edgeFinset
        have : (formedGraph s).edgeFinset.card = Fintype.card V - 1 := by omega
        rw [this]
      have hn1_le : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Nat.sub_le (Fintype.card V) 1
      have hdiv_le : ((Fintype.card V - 1 : ℕ) : ℝ) * (2 * G.alpha / (Fintype.card V : ℝ)) ≤
          2 * G.alpha := by
        rw [mul_div_assoc', div_le_iff₀ hn_pos]
        have hα_pos := G.alpha_pos
        nlinarith
      rw [hs.connectedSocialCost_eq_graphSocialCost, G.optSocialCost_eq_starSocialCost hα2,
        graphSocialCost, hm]
      unfold starSocialCost
      have hn1_nn : (0 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hα_pos := G.alpha_pos
      have hsum_uc2 : ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ u : V, ((formedGraph s).dist u c : ℝ) ≤
          ((Fintype.card V - 1 : ℕ) : ℝ) *
            (((Fintype.card V - 1 : ℕ) : ℝ) + 2 * G.alpha) := by
        refine mul_le_mul_of_nonneg_left ?_ hn1_nn
        linarith
      nlinarith

end TreeEquilibria

section DiameterAndSqrtBound

variable {V : Type*} [Fintype V] [DecidableEq V] {G : NetworkCreationGame} {s : V → Finset V}

omit [Fintype V] [DecidableEq V] in
/-- Along a shortest walk `p` of length `d = H.dist u v`, vertex `p.getVert j` (`j ≤ d`) is at
exact distance `j` from `u` and `d - j` from `v`. -/
private theorem dist_getVert_of_length_eq_dist {H : SimpleGraph V} (hH : H.Connected) {u v : V}
    {p : H.Walk u v} (hp : p.length = H.dist u v) {j : ℕ} (hj : j ≤ p.length) :
    H.dist u (p.getVert j) = j ∧ H.dist (p.getVert j) v = p.length - j := by
  have h1 : H.dist u (p.getVert j) ≤ j := by
    refine (H.dist_le (p.take j)).trans ?_
    rw [SimpleGraph.Walk.take_length]
    exact Nat.min_le_left _ _
  have h2 : H.dist (p.getVert j) v ≤ p.length - j := by
    refine (H.dist_le (p.drop j)).trans ?_
    rw [SimpleGraph.Walk.drop_length]
  have htri : H.dist u v ≤ H.dist u (p.getVert j) + H.dist (p.getVert j) v :=
    hH.dist_triangle
  omega

/-- **Diameter bound `O(√α)` at any pure Nash equilibrium** ([TardosWexler2007], Theorem 19.5,
locator not re-verified against primary PDF): for all vertices `u, v : V`,
`dist(u, v) ≤ 2 √α + 1`. -/
theorem IsPureNash.dist_le_two_mul_sqrt_add_one (hs : G.IsPureNash s) (u v : V) :
    ((formedGraph s).dist u v : ℝ) ≤ 2 * Real.sqrt G.alpha + 1 := by
  let H := formedGraph s
  let d := H.dist u v
  rcases le_or_gt d 1 with hd1 | hd1
  · have hdR : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
    have hsq_nn : 0 ≤ Real.sqrt G.alpha := Real.sqrt_nonneg G.alpha
    linarith
  · have hV : Nonempty V := ⟨u⟩
    have hconn : H.Connected := hs.connected
    have huv : u ≠ v := fun h => by
      subst h
      simp [d, H] at hd1
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
    let k := d / 2
    let f : ℕ → V := fun i => p.getVert (d - i)
    let S : Finset V := (Finset.range k).image f
    have hinj : Set.InjOn f (Finset.range k) := by
      intro i₁ hi₁ i₂ hi₂ heq
      rw [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
      have hj₁ : d - i₁ ≤ p.length := by omega
      have hj₂ : d - i₂ ≤ p.length := by omega
      have hd₁ := (dist_getVert_of_length_eq_dist hconn hp hj₁).1
      have hd₂ := (dist_getVert_of_length_eq_dist hconn hp hj₂).1
      change H.dist u (f i₁) = d - i₁ at hd₁
      change H.dist u (f i₂) = d - i₂ at hd₂
      rw [heq] at hd₁
      omega
    let s' := Function.update s u (insert v (s u))
    have hmono : H ≤ formedGraph s' := formedGraph_le_update_insert s u v
    have hadj_uv : (formedGraph s').Adj u v := by
      rw [formedGraph_adj]
      exact ⟨huv, Or.inl (by simp [s'])⟩
    have hconn' : (formedGraph s').Connected := hconn.mono hmono
    have hpt : ∀ i ∈ Finset.range k,
        ((d : ℝ) - 1 - 2 * (i : ℝ)) ≤
          (H.dist u (f i) : ℝ) - ((formedGraph s').dist u (f i) : ℝ) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hj : d - i ≤ p.length := by omega
      obtain ⟨hdu, hdv⟩ := dist_getVert_of_length_eq_dist hconn hp hj
      have hdv_eq : p.length - (d - i) = i := by omega
      rw [hdv_eq] at hdv
      have hdv' : (formedGraph s').dist v (f i) ≤ i := by
        have he := SimpleGraph.edist_anti hmono (u := v) (v := f i)
        rw [← (hconn' v (f i)).coe_dist_eq_edist, ← (hconn v (f i)).coe_dist_eq_edist] at he
        have hdv_comm : H.dist v (f i) = i := by
          rw [SimpleGraph.dist_comm (u := v) (v := f i)]
          exact hdv
        rw [hdv_comm] at he
        exact_mod_cast he
      have hdu' : (formedGraph s').dist u (f i) ≤ 1 + i := by
        have htri := hconn'.dist_triangle (u := u) (v := v) (w := f i)
        have huv1 : (formedGraph s').dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv
        omega
      have hduR : (H.dist u (f i) : ℝ) = (d : ℝ) - (i : ℝ) := by
        rw [hdu, Nat.cast_sub (by omega)]
      have hdu'R : ((formedGraph s').dist u (f i) : ℝ) ≤ 1 + (i : ℝ) := by exact_mod_cast hdu'
      linarith
    have hsum_S : ∑ i ∈ Finset.range k, ((d : ℝ) - 1 - 2 * (i : ℝ)) ≤ G.alpha := by
      let g : V → ℝ := fun x => (H.dist u x : ℝ) - ((formedGraph s').dist u x : ℝ)
      calc ∑ i ∈ Finset.range k, ((d : ℝ) - 1 - 2 * (i : ℝ))
        _ ≤ ∑ i ∈ Finset.range k, g (f i) := Finset.sum_le_sum hpt
        _ = ∑ x ∈ S, g x := (Finset.sum_image hinj).symm
        _ ≤ G.alpha := hs.sum_dist_sub_le_alpha u v S
    have harith : ∑ i ∈ Finset.range k, ((d : ℝ) - 1 - 2 * (i : ℝ)) =
        (k : ℝ) * ((d : ℝ) - (k : ℝ)) := by
      have htwo : ∀ m : ℕ, ∑ i ∈ Finset.range m, (2 * (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, htwo]
      ring
    rw [harith] at hsum_S
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hsq_le : ((d : ℝ) - 1) ^ 2 ≤ 4 * G.alpha := by
      have h1 : ((d : ℝ) - 1) ^ 2 ≤ 4 * ((k : ℝ) * ((d : ℝ) - (k : ℝ))) := by
        rcases Nat.mod_two_eq_zero_or_one d with hr | hr
        · have hd_eq : (d : ℝ) = 2 * (k : ℝ) := by
            exact_mod_cast (by omega : d = 2 * k)
          rw [hd_eq]
          nlinarith
        · have hd_eq : (d : ℝ) = 2 * (k : ℝ) + 1 := by
            exact_mod_cast (by omega : d = 2 * k + 1)
          rw [hd_eq]
          nlinarith
      linarith
    have h4sq : (2 * Real.sqrt G.alpha) ^ 2 = 4 * G.alpha := by
      rw [mul_pow, Real.sq_sqrt G.alpha_pos.le]
      ring
    have hd_sub : (d : ℝ) - 1 ≤ 2 * Real.sqrt G.alpha := by
      have hnn : 0 ≤ 2 * Real.sqrt G.alpha := by
        have := Real.sqrt_nonneg G.alpha
        linarith
      nlinarith [sq_nonneg ((d : ℝ) - 1 - 2 * Real.sqrt G.alpha)]
    linarith

/-- **Diameter-`d` pure Nash equilibrium social-cost bound** ([TardosWexler2007], Lemma 19.4,
locator not re-verified against primary PDF): if `s` is a pure Nash equilibrium and every pair of
vertices has distance at most `d` (`1 ≤ d`), then `connectedSocialCost s ≤ (3 d - 1) · OPT`. -/
theorem IsPureNash.socialCost_le_of_dist_le (hs : G.IsPureNash s) {d : ℝ} (hd1 : 1 ≤ d)
    (hd : ∀ u v : V, ((formedGraph s).dist u v : ℝ) ≤ d) :
    G.connectedSocialCost s ≤ (3 * d - 1) * G.optSocialCost V := by
  rcases le_or_gt (Fintype.card V) 1 with hn | hn
  · have hn1 : Fintype.card V - 1 = 0 := by omega
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn
    rw [hs.connectedSocialCost_eq_graphSocialCost]
    have hm : (formedGraph s).edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he.ne (Subsingleton.elim u v)
    have hdist0 : ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) = 0 :=
      Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
        rw [Subsingleton.elim u v, SimpleGraph.dist_self, Nat.cast_zero]
    simp [graphSocialCost, optSocialCost, completeSocialCost, starSocialCost, hm, hdist0, hn1]
  · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have v₀ : V := Classical.arbitrary V
    let H := formedGraph s
    have hconn : H.Connected := hs.connected
    have hex_par : ∀ w : V, w ≠ v₀ →
        ∃ p : V, H.Adj p w ∧ H.dist v₀ p + 1 = H.dist v₀ w := by
      intro w hw
      have hpos : 0 < H.dist v₀ w := hconn.pos_dist_of_ne (Ne.symm hw)
      have hed : H.edist v₀ w = ((H.dist v₀ w - 1 : ℕ) : ℕ∞) + 1 := by
        rw [← (hconn v₀ w).coe_dist_eq_edist]
        exact_mod_cast (by omega : H.dist v₀ w = (H.dist v₀ w - 1) + 1)
      obtain ⟨p, hpw, hp_ed⟩ := SimpleGraph.exists_adj_edist_eq_of_edist_eq_add_one hed
      rw [← (hconn v₀ p).coe_dist_eq_edist] at hp_ed
      have hp_d : H.dist v₀ p = H.dist v₀ w - 1 := Nat.cast_injective hp_ed
      exact ⟨p, hpw, by omega⟩
    let par : V → V := fun w =>
      if hw : w ≠ v₀ then (hex_par w hw).choose else v₀
    let H₀ : SimpleGraph V := SimpleGraph.parentGraph par
    have hH₀_le : H₀ ≤ H := by
      intro x y hxy
      rw [SimpleGraph.parentGraph_adj] at hxy
      rcases hxy.2 with hp | hp
      · by_cases hx : x ≠ v₀
        · have hspec := (hex_par x hx).choose_spec.1
          have hpx : (hex_par x hx).choose = y := by simpa [par, hx] using hp
          rw [hpx] at hspec
          exact hspec.symm
        · push Not at hx
          subst x
          simp only [par, ne_eq, not_true_eq_false, ↓reduceDIte] at hp
          exact absurd hp hxy.1
      · by_cases hy : y ≠ v₀
        · have hspec := (hex_par y hy).choose_spec.1
          have hpy : (hex_par y hy).choose = x := by simpa [par, hy] using hp
          rw [hpy] at hspec
          exact hspec
        · push Not at hy
          subst y
          simp only [par, ne_eq, not_true_eq_false, ↓reduceDIte] at hp
          exact absurd hp.symm hxy.1
    have hH₀_dist_root : ∀ k : ℕ, ∀ x : V, H.dist v₀ x = k →
        H₀.Reachable v₀ x ∧ H₀.dist v₀ x ≤ k := by
      intro k
      induction k with
      | zero =>
        intro x hx
        have hxv : v₀ = x := hconn.dist_eq_zero_iff.mp hx
        subst x
        exact ⟨SimpleGraph.Reachable.refl v₀, by simp⟩
      | succ k ih =>
        intro x hx
        have hxv : x ≠ v₀ := fun h => by subst x; simp at hx
        have hspec := (hex_par x hxv).choose_spec
        have hpar_eq : par x = (hex_par x hxv).choose := by simp [par, hxv]
        obtain ⟨hr_p, hd_p⟩ := ih (par x) (by rw [hpar_eq]; omega)
        have hadj₀ : H₀.Adj (par x) x := by
          rw [SimpleGraph.parentGraph_adj]
          exact ⟨by rw [hpar_eq]; exact hspec.1.ne, Or.inr rfl⟩
        refine ⟨hr_p.trans hadj₀.reachable, ?_⟩
        have htri := hr_p.dist_triangle_left x
        have h1 : H₀.dist (par x) x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj₀
        omega
    have hH₀_conn : H₀.Connected :=
      ⟨fun x y => (hH₀_dist_root _ x rfl).1.symm.trans (hH₀_dist_root _ y rfl).1⟩
    have hH₀_diam : ∀ x y : V, (H₀.dist x y : ℝ) ≤ 2 * d := fun x y => by
      have htri := hH₀_conn.dist_triangle (u := x) (v := v₀) (w := y)
      rw [SimpleGraph.dist_comm (u := x) (v := v₀)] at htri
      have hx_le : (H₀.dist v₀ x : ℝ) ≤ d :=
        (Nat.cast_le.mpr (hH₀_dist_root _ x rfl).2).trans (hd v₀ x)
      have hy_le : (H₀.dist v₀ y : ℝ) ≤ d :=
        (Nat.cast_le.mpr (hH₀_dist_root _ y rfl).2).trans (hd v₀ y)
      have htriR : (H₀.dist x y : ℝ) ≤ (H₀.dist v₀ x : ℝ) + (H₀.dist v₀ y : ℝ) := by
        exact_mod_cast htri
      linarith
    classical
    have hH₀_edges : H₀.edgeFinset.card ≤ Fintype.card V - 1 := by
      have hsub : H₀.edgeFinset ⊆ (Finset.univ.erase v₀).image fun x => s(x, par x) := by
        intro e he
        induction e using Sym2.ind with
        | h x y =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.parentGraph_adj]
            at he
          rw [Finset.mem_image]
          rcases he.2 with hp | hp
          · have hx : x ≠ v₀ := fun h => by
              subst h
              simp only [par, ne_eq, not_true_eq_false, ↓reduceDIte] at hp
              exact he.1 hp
            exact ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩, by rw [hp]⟩
          · have hy : y ≠ v₀ := fun h => by
              subst h
              simp only [par, ne_eq, not_true_eq_false, ↓reduceDIte] at hp
              exact he.1 hp.symm
            exact ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, by rw [hp, Sym2.eq_swap]⟩
      calc H₀.edgeFinset.card
        _ ≤ ((Finset.univ.erase v₀).image fun x => s(x, par x)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.erase v₀).card := Finset.card_image_le
        _ = Fintype.card V - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
    let keep : V → Finset V := fun u => (s u).filter fun w => H₀.Adj u w
    have hdev_bound : ∀ u : V,
        G.alpha * (((s u).card : ℝ) - ((keep u).card : ℝ)) ≤
          (2 * d - 1) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
      intro u
      let s' := Function.update s u (keep u)
      have hle_s' : H₀ ≤ formedGraph s' := by
        intro a b hab
        have habH : H.Adj a b := hH₀_le hab
        rw [formedGraph_adj] at habH ⊢
        refine ⟨habH.1, ?_⟩
        rcases habH.2 with hb | ha
        · left
          by_cases hau : a = u
          · subst hau
            simp [s', keep, hb, hab]
          · simp [s', hau, hb]
        · right
          by_cases hbu : b = u
          · subst hbu
            simp [s', keep, ha, hab.symm]
          · simp [s', hbu, ha]
      have hconn' : (formedGraph s').Connected := hH₀_conn.mono hle_s'
      have hne_u := hs.connectedPlayerCost_le u (keep u) (fun x => hconn' u x)
      simp only [connectedPlayerCost, Function.update_self] at hne_u
      have hdist_diff : ∑ x : V, (((formedGraph s').dist u x : ℝ) - (H.dist u x : ℝ)) ≤
          (2 * d - 1) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
        simp only [SimpleGraph.dist_self, Nat.cast_zero, sub_self, add_zero]
        calc ∑ x ∈ Finset.univ.erase u, (((formedGraph s').dist u x : ℝ) - (H.dist u x : ℝ))
          _ ≤ ∑ _x ∈ Finset.univ.erase u, (2 * d - 1) :=
              Finset.sum_le_sum fun x hx => by
                have hxu : u ≠ x := (Finset.ne_of_mem_erase hx).symm
                have h1 : (1 : ℝ) ≤ (H.dist u x : ℝ) := by
                  exact_mod_cast hconn.pos_dist_of_ne hxu
                have h2 : ((formedGraph s').dist u x : ℝ) ≤ 2 * d := by
                  have he := SimpleGraph.edist_anti hle_s' (u := u) (v := x)
                  rw [← (hconn' u x).coe_dist_eq_edist, ← (hH₀_conn u x).coe_dist_eq_edist] at he
                  have hle0 : ((formedGraph s').dist u x : ℝ) ≤ (H₀.dist u x : ℝ) := by
                    exact_mod_cast he
                  exact hle0.trans (hH₀_diam u x)
                linarith
          _ = (2 * d - 1) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
                Finset.card_univ, nsmul_eq_mul, mul_comm]
      rw [Finset.sum_sub_distrib] at hdist_diff
      dsimp only [s', H] at hdist_diff
      linarith
    have hsum_keep : ∑ u : V, (keep u).card ≤ Fintype.card V - 1 := by
      rw [← Finset.card_sigma (s := Finset.univ)]
      refine (Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_).trans hH₀_edges
      · rintro ⟨u, w⟩ hp
        rw [Finset.mem_coe, Finset.mem_sigma] at hp
        have hadj : H₀.Adj u w := (Finset.mem_filter.mp hp.2).2
        exact SimpleGraph.mem_edgeFinset.mpr hadj
      · rintro ⟨u₁, w₁⟩ hp₁ ⟨u₂, w₂⟩ hp₂ heq
        rw [Finset.mem_coe, Finset.mem_sigma] at hp₁ hp₂
        have hw₁ : w₁ ∈ s u₁ := (Finset.mem_filter.mp hp₁.2).1
        have hw₂ : w₂ ∈ s u₂ := (Finset.mem_filter.mp hp₂.2).1
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd hw₂ (hs.notMem_symm hw₁)
    have hsum_dev := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hdev_bound u
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsum_dev
    have hkeepR : ∑ u : V, ((keep u).card : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast hsum_keep
    have hdist_total : ∑ u : V, ∑ v : V, (H.dist u v : ℝ) ≤
        d * ((Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ)) := by
      have hinner : ∀ u : V, ∑ v : V, (H.dist u v : ℝ) ≤
          d * ((Fintype.card V - 1 : ℕ) : ℝ) := fun u => by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
        simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
        calc ∑ v ∈ Finset.univ.erase u, (H.dist u v : ℝ)
          _ ≤ ∑ _v ∈ Finset.univ.erase u, d := Finset.sum_le_sum fun v _ => hd u v
          _ = d * ((Fintype.card V - 1 : ℕ) : ℝ) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
                Finset.card_univ, nsmul_eq_mul, mul_comm]
      calc ∑ u : V, ∑ v : V, (H.dist u v : ℝ)
        _ ≤ ∑ _u : V, d * ((Fintype.card V - 1 : ℕ) : ℝ) := Finset.sum_le_sum fun u _ => hinner u
        _ = d * ((Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    have hopt := G.alpha_add_card_mul_le_optSocialCost (by omega : 2 ≤ Fintype.card V)
    rw [G.connectedSocialCost_eq]
    have hα_pos := G.alpha_pos
    have h3d : 0 ≤ 3 * d - 1 := by linarith
    have hopt_mul : (3 * d - 1) *
        ((G.alpha + (Fintype.card V : ℝ)) * ((Fintype.card V - 1 : ℕ) : ℝ)) ≤
        (3 * d - 1) * G.optSocialCost V :=
      mul_le_mul_of_nonneg_left hopt h3d
    have hα_term : G.alpha * ((Fintype.card V - 1 : ℕ) : ℝ) ≤
        (3 * d - 1) * (G.alpha * ((Fintype.card V - 1 : ℕ) : ℝ)) := by
      have hprod_nn : 0 ≤ G.alpha * ((Fintype.card V - 1 : ℕ) : ℝ) :=
        mul_nonneg G.alpha_pos.le (Nat.cast_nonneg _)
      nlinarith
    have hsum_dev' : G.alpha * ∑ u : V, ((s u).card : ℝ) ≤
        G.alpha * ((Fintype.card V - 1 : ℕ) : ℝ) +
          (2 * d - 1) * ((Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ)) := by
      nlinarith
    dsimp only [H] at hdist_total
    linarith

/-- **`PoA = O(√α)` for general pure Nash equilibria** ([TardosWexler2007], Theorem 19.5, locator
not re-verified against primary PDF): every pure Nash equilibrium `s` satisfies
`connectedSocialCost s ≤ (6 √α + 2) · OPT`. -/
theorem IsPureNash.socialCost_le_six_mul_sqrt_add_two (hs : G.IsPureNash s) :
    G.connectedSocialCost s ≤ (6 * Real.sqrt G.alpha + 2) * G.optSocialCost V := by
  have hd1 : 1 ≤ 2 * Real.sqrt G.alpha + 1 := by
    have := Real.sqrt_nonneg G.alpha
    linarith
  have h := hs.socialCost_le_of_dist_le hd1 hs.dist_le_two_mul_sqrt_add_one
  have heq : 3 * (2 * Real.sqrt G.alpha + 1) - 1 = 6 * Real.sqrt G.alpha + 2 := by ring
  rwa [heq] at h

end DiameterAndSqrtBound

end NetworkCreationGame

end Cslib.GameTheory
