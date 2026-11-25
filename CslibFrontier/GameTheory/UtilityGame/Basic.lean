/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.GameTheory.Strategic.Correlated
public import CslibFrontier.GameTheory.Strategic.Potential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vetta's utility games, the price of anarchy `2`, and random best-response dynamics

In a **utility game** ([Vetta2002]; [TardosWexler2007], Section 19.4.3, p. 504), each
player `i : ι` selects a strategy `s i : S i` from a player-indexed ground set `Σ i, S i` (modeling
the disjoint union `A = ⊔ i, A_i` of player strategy sets), a social welfare function
`socialValue : Finset (Σ i, S i) → ℝ` evaluates any finite subset of player-tagged choices, and each
player receives payoff `utility i s : ℝ`. A `UtilityGame` is **valid** (`IsValid`, called a
"utility game" in [TardosWexler2007], Section 19.4.3) when:

1. `socialValue` is submodular (`Cslib.Algorithms.Lean.Submodular.IsSubmodular`);
2. the players' payoffs do not exceed the social welfare (`∑ i, utility i s ≤ profileValue s`);
3. each player's payoff is at least its marginal contribution to social welfare
   (`profileValue s - socialValue (profileWithout s i) ≤ utility i s`).

It is **basic** (`IsBasic`) when condition (3) holds with equality. Monotonicity reuses Mathlib's
`Monotone` directly on `G.socialValue`. Embedding payoffs into `Cslib.GameTheory.CostGame` via
`cost = -utility` (`toCostGame`) lets utility games reuse `IsPureNash`, `IsMixedNash`,
`IsCorrelatedEquilibrium`, `IsCoarseCorrelatedEquilibrium`, `IsExactPotential`, and `HasFIP`
directly.

Every basic utility game has `-profileValue` as an exact potential of `toCostGame`
(`IsBasic.isExactPotential`), so finite basic utility games always admit pure Nash equilibria,
every welfare-maximizing profile is a pure Nash equilibrium (`PoS = 1`), and better-response
dynamics terminate (`IsBasic.hasFIP`).

For **monotone** valid utility games, diminishing marginal returns imply the payoff-smoothness
bound `profileValue o - profileValue s ≤ ∑ i, utility i (update s i (o i))`
(`IsValid.profileValue_sub_le_sum_deviation`), yielding Vetta's price-of-anarchy bound of `2`
for pure Nash equilibria ([TardosWexler2007], Theorem 19.19) and mixed Nash equilibria
([Vetta2002]; [TardosWexler2007], Section 19.5.3, p. 511), together with an original extension to
coarse correlated equilibria (hence correlated equilibria).

For **monotone basic** utility games, one uniformly random best-response step increases expected
welfare by at least `(profileValue o - 2 * profileValue s) / n`, so `O(n log(1 / ε))` random
best-response moves reach expected social welfare at least `(1 / 2 - ε)` times optimal without
assuming convergence to equilibrium ([MirrokniVetta2004]; [GoemansMirrokniVetta2005];
[TardosWexler2007], Theorem 19.20).

Finally, Section 19.4's closed-neighborhood wealth-sharing graph location game
([TardosWexler2007], Exercise 19.16, p. 515) instantiates `IsValid` as a non-basic monotone utility
game whose pure-equilibrium price of anarchy attains `2 - 1 / k`, approaching `2` arbitrarily
closely.

## Main definitions

* `Cslib.GameTheory.UtilityGame`: a strategic game equipped with a set-level `socialValue` on
  `Finset (Σ i, S i)` and player payoffs `utility`.
* `Cslib.GameTheory.UtilityGame.profileSet`, `Cslib.GameTheory.UtilityGame.profileWithout`,
  `Cslib.GameTheory.UtilityGame.profileValue`, `Cslib.GameTheory.UtilityGame.toCostGame`: profile
  embeddings into `Finset (Σ i, S i)` and bridge to `CostGame` (`cost = -utility`).
* `Cslib.GameTheory.UtilityGame.IsValid`, `Cslib.GameTheory.UtilityGame.IsBasic`: Vetta's three
  utility-game conditions and the exact-marginal-contribution refinement.
* `Cslib.GameTheory.UtilityGame.IsBestResponse`, `Cslib.GameTheory.UtilityGame.bestResponseWalk`,
  `Cslib.GameTheory.UtilityGame.expectedWalkValue`: best-response selectors and the `t`-step
  uniformly random player best-response trajectory.
* `Cslib.GameTheory.UtilityGame.neighborhoodGame`: the closed-neighborhood wealth-sharing graph
  location game ([TardosWexler2007], Exercise 19.16).

## Main results

* `Cslib.GameTheory.UtilityGame.IsBasic.isExactPotential`: every basic utility game has
  `-profileValue` as an exact potential of `toCostGame` (implying `HasFIP`, pure-equilibrium
  existence, and stability of socially optimal profiles).
* `Cslib.GameTheory.UtilityGame.IsValid.profileValue_sub_le_sum_deviation`: monotone valid utility
  games satisfy `profileValue o - profileValue s ≤ ∑ i, utility i (update s i (o i))`.
* `Cslib.GameTheory.UtilityGame.IsValid.profileValue_le_two_mul_of_isPureNash`
  ([TardosWexler2007], Theorem 19.19; [Vetta2002]): every pure Nash equilibrium of a monotone valid
  utility game achieves at least half the social welfare of any profile (`PoA ≤ 2`).
* `Cslib.GameTheory.UtilityGame.IsValid.profileValue_le_two_mul_expected_of_isMixedNash`
  ([Vetta2002]; [TardosWexler2007], Section 19.5.3): `PoA ≤ 2` extends to mixed Nash equilibria.
* `IsValid.profileValue_le_two_mul_expected_of_isCoarseCorrelatedEquilibrium` (original):
  expected-welfare `PoA ≤ 2` extension to coarse correlated (hence correlated) equilibria.
* `Cslib.GameTheory.UtilityGame.IsBasic.mul_profileValue_le_expectedWalkValue`
  ([MirrokniVetta2004]; [GoemansMirrokniVetta2005]; [TardosWexler2007], Theorem 19.20): after
  `t ≥ (n / 2) * log (1 / ε)` random best-response steps in a monotone basic utility game with
  `0 ≤ socialValue ∅`, expected social welfare is at least `(1 / 2 - ε) * profileValue o`.
* `Cslib.GameTheory.UtilityGame.isValid_neighborhoodGame`,
  `Cslib.GameTheory.UtilityGame.exists_neighborhoodGame_isPureNash_mul_lt`
  ([TardosWexler2007], Exercise 19.16): the closed-neighborhood wealth-sharing game is a monotone
  valid utility game whose price of anarchy comes arbitrarily close to `2`.

## References

* [GoemansMirrokniVetta2005]
* [MirrokniVetta2004]
* [TardosWexler2007]
* [Vetta2002]
-/

public section

namespace Cslib.GameTheory

open Cslib.Algorithms.Lean
open Finset Function

/-- A **utility game** ([Vetta2002]; [TardosWexler2007], Section 19.4.3, p. 504): each
player `i : ι` chooses a strategy `s i : S i`, `socialValue` evaluates finite subsets of the
disjoint union `Σ i, S i` of player strategy sets, and `utility i s` is player `i`'s payoff at
the profile `s`. -/
structure UtilityGame (ι : Type*) (S : ι → Type*) where
  /-- Social welfare `V(T)` of a finite set `T` of player-tagged choices. -/
  socialValue : Finset (Σ i, S i) → ℝ
  /-- Payoff `α_i(s)` of player `i` at strategy profile `s`. -/
  utility : ι → (∀ i, S i) → ℝ

namespace UtilityGame

section Profiles

variable {ι : Type*} {S : ι → Type*}

/-- Embedding `i ↦ ⟨i, s i⟩` of players into the disjoint union `Σ i, S i`. -/
private def profileEmbedding (s : ∀ i, S i) : ι ↪ Σ i, S i :=
  ⟨fun i => ⟨i, s i⟩, fun _ _ h => (Sigma.mk.inj h).1⟩

/-- The finite set `{⟨i, s i⟩ | i : ι}` of player-tagged choices in profile `s`. -/
def profileSet [Fintype ι] (s : ∀ i, S i) : Finset (Σ i, S i) :=
  Finset.univ.map (profileEmbedding s)

@[simp]
theorem mem_profileSet [Fintype ι] {s : ∀ i, S i} {x : Σ i, S i} :
    x ∈ profileSet s ↔ s x.1 = x.2 := by
  rcases x with ⟨i, a⟩
  simp only [profileSet, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    change (⟨j, s j⟩ : Σ k, S k) = ⟨i, a⟩ at hj
    cases hj
    rfl
  · rintro rfl
    exact ⟨i, rfl⟩

@[simp]
theorem sum_profileSet [Fintype ι] {β : Type*} [AddCommMonoid β] (s : ∀ i, S i)
    (f : (Σ i, S i) → β) :
    ∑ x ∈ profileSet s, f x = ∑ i, f ⟨i, s i⟩ := by
  rw [profileSet]
  exact Finset.sum_map Finset.univ (profileEmbedding s) f

@[simp]
theorem fold_profileSet [Fintype ι] {β : Type*} (op : β → β → β) [Std.Associative op]
    [Std.Commutative op] (b : β) (f : (Σ i, S i) → β) (s : ∀ i, S i) :
    (profileSet s).fold op b f = Finset.univ.fold op b (fun i => f ⟨i, s i⟩) := by
  rw [profileSet, Finset.fold_map]
  rfl

/-- The set `s - s_i` of choices made by all players other than `i` in profile `s`. -/
def profileWithout [Fintype ι] [DecidableEq ι] (s : ∀ i, S i) (i : ι) : Finset (Σ j, S j) :=
  (Finset.univ.erase i).map (profileEmbedding s)

@[simp]
theorem mem_profileWithout [Fintype ι] [DecidableEq ι] {s : ∀ i, S i} {i : ι} {x : Σ j, S j} :
    x ∈ profileWithout s i ↔ x.1 ≠ i ∧ s x.1 = x.2 := by
  rcases x with ⟨j, a⟩
  simp only [profileWithout, mem_map, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨j', hne, hj⟩
    change (⟨j', s j'⟩ : Σ k, S k) = ⟨j, a⟩ at hj
    cases hj
    exact ⟨hne, rfl⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨j, hne, rfl⟩

@[simp]
theorem sum_profileWithout [Fintype ι] [DecidableEq ι] {β : Type*} [AddCommMonoid β]
    (s : ∀ i, S i) (i : ι) (f : (Σ j, S j) → β) :
    ∑ x ∈ profileWithout s i, f x = ∑ j ∈ Finset.univ.erase i, f ⟨j, s j⟩ := by
  rw [profileWithout]
  exact Finset.sum_map (Finset.univ.erase i) (profileEmbedding s) f

@[simp]
theorem fold_profileWithout [Fintype ι] [DecidableEq ι] {β : Type*} (op : β → β → β)
    [Std.Associative op] [Std.Commutative op] (b : β) (f : (Σ j, S j) → β)
    (s : ∀ i, S i) (i : ι) :
    (profileWithout s i).fold op b f =
      (Finset.univ.erase i).fold op b (fun j => f ⟨j, s j⟩) := by
  rw [profileWithout, Finset.fold_map]
  rfl

@[simp]
theorem profileWithout_update [Fintype ι] [DecidableEq ι] (s : ∀ j, S j) (i : ι) (a : S i) :
    profileWithout (Function.update s i a) i = profileWithout s i := by
  ext ⟨j, b⟩
  simp only [mem_profileWithout]
  exact and_congr_right fun hne => by rw [Function.update_of_ne hne]

theorem profileWithout_subset_profileSet [Fintype ι] [DecidableEq ι] (s : ∀ j, S j) (i : ι) :
    profileWithout s i ⊆ profileSet s := by
  intro x hx
  rw [mem_profileWithout] at hx
  exact mem_profileSet.mpr hx.2

theorem profileWithout_eq_erase [Fintype ι] [DecidableEq ι] [∀ j, DecidableEq (S j)]
    (s : ∀ j, S j) (i : ι) :
    profileWithout s i = (profileSet s).erase ⟨i, s i⟩ := by
  ext ⟨j, b⟩
  simp only [mem_profileWithout, mem_erase, mem_profileSet]
  constructor
  · rintro ⟨hne, rfl⟩
    exact ⟨fun h => hne (Sigma.mk.inj h).1, rfl⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨fun h => hne (by subst h; rfl), rfl⟩

theorem insert_profileWithout [Fintype ι] [DecidableEq ι] [∀ j, DecidableEq (S j)]
    (s : ∀ j, S j) (i : ι) (a : S i) :
    insert ⟨i, a⟩ (profileWithout s i) = profileSet (Function.update s i a) := by
  ext ⟨j, b⟩
  simp only [mem_insert, mem_profileWithout, mem_profileSet, Sigma.mk.inj_iff]
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self, true_and, ne_eq, not_true_eq_false, false_and, or_false,
      heq_eq_eq]
    exact eq_comm
  · simp only [Function.update_of_ne hji, hji, false_and, ne_eq, not_false_eq_true, true_and,
      false_or]

@[simp]
theorem insert_self_profileWithout [Fintype ι] [DecidableEq ι] [∀ j, DecidableEq (S j)]
    (s : ∀ j, S j) (i : ι) :
    insert ⟨i, s i⟩ (profileWithout s i) = profileSet s := by
  simpa only [Function.update_eq_self] using insert_profileWithout s i (s i)

/-- Social welfare `V(s)` of a strategy profile `s`. -/
def profileValue [Fintype ι] (G : UtilityGame ι S) (s : ∀ i, S i) : ℝ :=
  G.socialValue (profileSet s)

theorem profileValue_def [Fintype ι] (G : UtilityGame ι S) (s : ∀ i, S i) :
    G.profileValue s = G.socialValue (profileSet s) := by
  rfl

/-- Strategic game in cost-minimization form associated to `G`, with `cost i s = -G.utility i s`. -/
def toCostGame (G : UtilityGame ι S) : CostGame ι S where
  cost i s := -G.utility i s

@[simp]
theorem toCostGame_cost (G : UtilityGame ι S) (i : ι) (s : ∀ j, S j) :
    G.toCostGame.cost i s = -G.utility i s := by
  rfl

@[simp]
theorem toCostGame_socialCost [Fintype ι] (G : UtilityGame ι S) (s : ∀ j, S j) :
    G.toCostGame.socialCost s = -∑ i, G.utility i s := by
  simp only [CostGame.socialCost, toCostGame_cost, Finset.sum_neg_distrib]

theorem isPureNash_toCostGame_iff [DecidableEq ι] (G : UtilityGame ι S) {s : ∀ i, S i} :
    G.toCostGame.IsPureNash s ↔
      ∀ i (a : S i), G.utility i (Function.update s i a) ≤ G.utility i s := by
  simp only [CostGame.IsPureNash, toCostGame_cost, neg_le_neg_iff]

end Profiles

/-! ## Vetta's utility game conditions and potential structure -/

section Conditions

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)]

/-- Vetta's **valid utility game** conditions ([Vetta2002]; [TardosWexler2007],
Section 19.4.3, properties (i)–(iii), p. 504):
1. `socialValue` is submodular on `Finset (Σ i, S i)`;
2. total player payoffs never exceed social welfare;
3. each player's payoff is at least its marginal contribution to social welfare. -/
structure IsValid (G : UtilityGame ι S) : Prop where
  /-- Property (i): diminishing marginal returns of `socialValue`. -/
  isSubmodular : Submodular.IsSubmodular G.socialValue
  /-- Property (ii): `∑ i, α_i(s) ≤ V(s)`. -/
  sum_utility_le : ∀ s, ∑ i, G.utility i s ≤ G.profileValue s
  /-- Property (iii): `V(s) - V(s - s_i) ≤ α_i(s)`. -/
  marginal_le_utility : ∀ i s,
    G.profileValue s - G.socialValue (profileWithout s i) ≤ G.utility i s

/-- A **basic utility game** ([TardosWexler2007], Section 19.4.3, p. 504) satisfies properties
(i) and (ii) and achieves equality in property (iii): each player's payoff equals its exact
marginal contribution `V(s) - V(s - s_i)` to social welfare. -/
structure IsBasic (G : UtilityGame ι S) : Prop where
  /-- Property (i): diminishing marginal returns of `socialValue`. -/
  isSubmodular : Submodular.IsSubmodular G.socialValue
  /-- Property (ii): `∑ i, α_i(s) ≤ V(s)`. -/
  sum_utility_le : ∀ s, ∑ i, G.utility i s ≤ G.profileValue s
  /-- Equality in property (iii): `α_i(s) = V(s) - V(s - s_i)`. -/
  utility_eq_marginal : ∀ i s,
    G.utility i s = G.profileValue s - G.socialValue (profileWithout s i)

/-- Every basic utility game is a valid utility game. -/
theorem IsBasic.isValid {G : UtilityGame ι S} (hG : G.IsBasic) : G.IsValid where
  isSubmodular := hG.isSubmodular
  sum_utility_le := hG.sum_utility_le
  marginal_le_utility i s := (hG.utility_eq_marginal i s).symm.le

omit [∀ i, DecidableEq (S i)] in
/-- In a basic utility game, any unilateral deviation changes the deviator's payoff by the exact
change in `profileValue`. -/
theorem IsBasic.utility_sub_utility_eq {G : UtilityGame ι S}
    (hmarg : ∀ i s, G.utility i s = G.profileValue s - G.socialValue (profileWithout s i))
    (s : ∀ i, S i) (i : ι) (a : S i) :
    G.utility i (Function.update s i a) - G.utility i s =
      G.profileValue (Function.update s i a) - G.profileValue s := by
  rw [hmarg i (Function.update s i a), hmarg i s, profileWithout_update]
  ring

/-- Every basic utility game is an exact potential game with potential `-profileValue` on
`toCostGame` ([TardosWexler2007], Section 19.4.4, p. 505). -/
theorem IsBasic.isExactPotential {G : UtilityGame ι S} (hG : G.IsBasic) :
    G.toCostGame.IsExactPotential (fun s => -G.profileValue s) := by
  intro s i a
  simp only [toCostGame_cost]
  have h := IsBasic.utility_sub_utility_eq hG.utility_eq_marginal s i a
  linarith

/-- Every finite basic utility game has the finite improvement property: better-response dynamics
always terminate at a pure Nash equilibrium. -/
theorem IsBasic.hasFIP {G : UtilityGame ι S} [∀ i, Finite (S i)] (hG : G.IsBasic) :
    G.toCostGame.HasFIP :=
  hG.isExactPotential.isGeneralizedOrdinalPotential.hasFIP

/-- Every nonempty finite basic utility game admits a pure Nash equilibrium. -/
theorem IsBasic.exists_isPureNash {G : UtilityGame ι S} [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    (hG : G.IsBasic) :
    ∃ s, G.toCostGame.IsPureNash s :=
  hG.isExactPotential.isGeneralizedOrdinalPotential.exists_isPureNash

/-- In a basic utility game, every socially efficient profile is a pure Nash equilibrium
([TardosWexler2007], Section 19.4.4, p. 505). -/
theorem IsBasic.isPureNash_of_forall_profileValue_le {G : UtilityGame ι S} (hG : G.IsBasic)
    {s : ∀ i, S i} (hs : ∀ s', G.profileValue s' ≤ G.profileValue s) :
    G.toCostGame.IsPureNash s :=
  hG.isExactPotential.isGeneralizedOrdinalPotential.isPureNash_of_forall_le fun s' =>
    neg_le_neg (hs s')

/-- Every nonempty finite basic utility game admits a socially optimal pure Nash equilibrium
(the price of stability is `1`). -/
theorem IsBasic.exists_isPureNash_forall_profileValue_le {G : UtilityGame ι S}
    [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] (hG : G.IsBasic) :
    ∃ s, G.toCostGame.IsPureNash s ∧ ∀ s', G.profileValue s' ≤ G.profileValue s := by
  obtain ⟨s, hs⟩ := Finite.exists_max G.profileValue
  exact ⟨s, hG.isPureNash_of_forall_profileValue_le hs, hs⟩

/-! ## Price of anarchy `2` for monotone valid utility games -/

/-- **Payoff-smoothness of monotone valid utility games**: for any two profiles `s` and `o`,
`V(o) - V(s) ≤ ∑ i, α_i(update s i (o i))` ([Vetta2002]; [TardosWexler2007], proof of
Theorem 19.19, p. 505). -/
theorem IsValid.profileValue_sub_le_sum_deviation {G : UtilityGame ι S} (hG : G.IsValid)
    (hmono : Monotone G.socialValue) (s o : ∀ i, S i) :
    G.profileValue o - G.profileValue s ≤ ∑ i, G.utility i (Function.update s i (o i)) := by
  have hsub :=
    hG.isSubmodular.sub_le_sum_marginalGain_full_of_monotone hmono (profileSet s) (profileSet o)
  rw [sum_profileSet] at hsub
  refine hsub.trans (Finset.sum_le_sum fun i _ => ?_)
  have hdim := hG.isSubmodular.marginalGain_le_of_monotone hmono ⟨i, o i⟩
    (profileWithout_subset_profileSet s i)
  refine hdim.trans ?_
  dsimp only [Submodular.marginalGain]
  rw [insert_profileWithout]
  have hmarg := hG.marginal_le_utility i (Function.update s i (o i))
  rwa [profileValue_def, profileWithout_update] at hmarg

/-- **Price of Anarchy for Monotone Utility Games** ([TardosWexler2007], Theorem 19.19, p. 505;
[Vetta2002]): in every monotone valid utility game, the social welfare of any pure
Nash equilibrium `s` is at least half the social welfare of any profile `o`
(`profileValue o ≤ 2 * profileValue s`). -/
theorem IsValid.profileValue_le_two_mul_of_isPureNash {G : UtilityGame ι S} (hG : G.IsValid)
    (hmono : Monotone G.socialValue) {s : ∀ i, S i} (hs : G.toCostGame.IsPureNash s)
    (o : ∀ i, S i) :
    G.profileValue o ≤ 2 * G.profileValue s := by
  rw [isPureNash_toCostGame_iff] at hs
  have hdev := hG.profileValue_sub_le_sum_deviation hmono s o
  have hne : ∑ i, G.utility i (Function.update s i (o i)) ≤ ∑ i, G.utility i s :=
    Finset.sum_le_sum fun i _ => hs i (o i)
  have hbud := hG.sum_utility_le s
  linarith

/-- **Coarse Correlated Price of Anarchy for Monotone Utility Games** (original extension): for
every coarse correlated equilibrium `σ` of `G.toCostGame` (hence also every correlated equilibrium
via `CostGame.IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium`), expected social welfare under
`σ` is at least half the social welfare of any profile `o`. -/
theorem IsValid.profileValue_le_two_mul_expected_of_isCoarseCorrelatedEquilibrium
    {G : UtilityGame ι S} (hG : G.IsValid) (hmono : Monotone G.socialValue)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (hσ : G.toCostGame.IsCoarseCorrelatedEquilibrium σ)
    (o : ∀ i, S i) :
    G.profileValue o ≤ 2 * σ.weights.sum (fun s w => w * G.profileValue s) := by
  simp only [CostGame.IsCoarseCorrelatedEquilibrium, toCostGame_cost, Finsupp.sum] at hσ ⊢
  have htot : ∑ s ∈ σ.weights.support, σ.weights s = 1 := σ.total
  have h1 : G.profileValue o - ∑ s ∈ σ.weights.support, σ.weights s * G.profileValue s
      ≤ ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.utility i (Function.update s i (o i)) := by
    have hconst : G.profileValue o = ∑ s ∈ σ.weights.support, σ.weights s * G.profileValue o := by
      rw [← Finset.sum_mul, htot, one_mul]
    rw [hconst, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (hG.profileValue_sub_le_sum_deviation hmono s o)
      (Convexity.StdSimplex.weights_nonneg s)
  have h2 : ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.utility i (Function.update s i (o i))
      ≤ ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.utility i s := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := σ.weights.support)]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hσ i (o i)
    simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hi
    exact hi
  have h3 : ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.utility i s
      ≤ ∑ s ∈ σ.weights.support, σ.weights s * G.profileValue s :=
    Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hG.sum_utility_le s) (Convexity.StdSimplex.weights_nonneg s)
  linarith

/-- **Mixed Nash Price of Anarchy for Monotone Utility Games** ([Vetta2002];
[TardosWexler2007], Section 19.5.3, p. 511): for every mixed Nash equilibrium `p` of `G.toCostGame`,
expected social welfare `∑ s, productWeight p s * profileValue s` is at least half the social
welfare of any pure profile `o`. -/
theorem IsValid.profileValue_le_two_mul_expected_of_isMixedNash {G : UtilityGame ι S}
    [∀ i, Fintype (S i)] (hG : G.IsValid) (hmono : Monotone G.socialValue)
    {p : ∀ i, S i → ℝ} (hp : G.toCostGame.IsMixedNash p) (o : ∀ i, S i) :
    G.profileValue o ≤ 2 * ∑ s, productWeight p s * G.profileValue s := by
  have h := hG.profileValue_le_two_mul_expected_of_isCoarseCorrelatedEquilibrium hmono
    hp.isCoarseCorrelatedEquilibrium o
  rwa [productDist_sum] at h

end Conditions

/-! ## Transient welfare bounds for random best-response dynamics (Theorem 19.20) -/

section RandomBestResponse

variable {ι : Type*} {S : ι → Type*}

/-- `br` is a **best-response selector** for `G`: for every player `i` and profile `s`, switching
`i` to `br i s` achieves at least the payoff of any unilateral deviation `a : S i`. -/
@[expose] def IsBestResponse [DecidableEq ι] (G : UtilityGame ι S)
    (br : ∀ i, (∀ j, S j) → S i) : Prop :=
  ∀ i s (a : S i), G.utility i (Function.update s i a) ≤ G.utility i (Function.update s i (br i s))

/-- Every utility game with nonempty finite strategy sets admits a best-response selector. -/
theorem exists_isBestResponse [DecidableEq ι] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    (G : UtilityGame ι S) :
    ∃ br : ∀ i, (∀ j, S j) → S i, G.IsBestResponse br := by
  have h : ∀ i (s : ∀ j, S j), ∃ b : S i, ∀ a : S i,
      G.utility i (Function.update s i a) ≤ G.utility i (Function.update s i b) :=
    fun i s => Finite.exists_max fun a => G.utility i (Function.update s i a)
  choose br hbr using h
  exact ⟨br, hbr⟩

/-- Trajectory of `t` best-response moves starting at `s` driven by the player sequence
`seq : Fin t → ι`. -/
def bestResponseWalk [DecidableEq ι] (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i) :
    ∀ t : ℕ, (Fin t → ι) → ∀ i, S i
  | 0, _ => s
  | t + 1, seq =>
      bestResponseWalk br (Function.update s (seq 0) (br (seq 0) s)) t (Fin.tail seq)

@[simp]
theorem bestResponseWalk_zero [DecidableEq ι] (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i)
    (seq : Fin 0 → ι) :
    bestResponseWalk br s 0 seq = s := by
  rfl

@[simp]
theorem bestResponseWalk_succ [DecidableEq ι] (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i)
    (t : ℕ) (seq : Fin (t + 1) → ι) :
    bestResponseWalk br s (t + 1) seq =
      bestResponseWalk br (Function.update s (seq 0) (br (seq 0) s)) t (Fin.tail seq) := by
  rfl

/-- Expected social welfare after `t` uniformly random player best-response steps starting from `s`
([TardosWexler2007], Section 19.4.5, p. 506). -/
noncomputable def expectedWalkValue [Fintype ι] [DecidableEq ι] (G : UtilityGame ι S)
    (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i) (t : ℕ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ ^ t * ∑ seq : Fin t → ι, G.profileValue (bestResponseWalk br s t seq)

@[simp]
theorem expectedWalkValue_zero [Fintype ι] [DecidableEq ι] (G : UtilityGame ι S)
    (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i) :
    G.expectedWalkValue br s 0 = G.profileValue s := by
  simp only [expectedWalkValue, pow_zero, one_mul, Fintype.sum_unique, bestResponseWalk_zero]

theorem expectedWalkValue_succ [Fintype ι] [DecidableEq ι] (G : UtilityGame ι S)
    (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i) (t : ℕ) :
    G.expectedWalkValue br s (t + 1) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, G.expectedWalkValue br (Function.update s i (br i s)) t := by
  have hsum : (∑ seq : Fin (t + 1) → ι, G.profileValue (bestResponseWalk br s (t + 1) seq)) =
      ∑ i : ι, ∑ seq' : Fin t → ι,
        G.profileValue (bestResponseWalk br (Function.update s i (br i s)) t seq') := by
    trans ∑ p : ι × (Fin t → ι),
        G.profileValue (bestResponseWalk br (Function.update s p.1 (br p.1 s)) t p.2)
    · refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (t + 1) => ι).symm _ _ fun seq => ?_
      rw [bestResponseWalk_succ]
      rfl
    · exact Fintype.sum_prod_type _
  rw [expectedWalkValue, hsum, pow_succ', mul_assoc, Finset.mul_sum]
  simp only [expectedWalkValue]

theorem expectedWalkValue_one [Fintype ι] [DecidableEq ι] (G : UtilityGame ι S)
    (br : ∀ i, (∀ j, S j) → S i) (s : ∀ i, S i) :
    G.expectedWalkValue br s 1 =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, G.profileValue (Function.update s i (br i s)) := by
  simp only [expectedWalkValue_succ, expectedWalkValue_zero]

private theorem expectedWalkValue_nonneg [Fintype ι] [DecidableEq ι] {G : UtilityGame ι S}
    (h0 : 0 ≤ G.socialValue ∅) (hmono : Monotone G.socialValue) (br : ∀ i, (∀ j, S j) → S i)
    (s : ∀ i, S i) (t : ℕ) :
    0 ≤ G.expectedWalkValue br s t := by
  unfold expectedWalkValue
  refine mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _) (Finset.sum_nonneg ?_)
  intro seq _
  exact Submodular.nonneg_of_empty_nonneg_of_monotone h0 hmono _

section BasicWalk

variable [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)]

private theorem profileValue_le_bestResponseWalk {G : UtilityGame ι S} (hG : G.IsBasic)
    {br : ∀ i, (∀ j, S j) → S i} (hbr : G.IsBestResponse br) :
    ∀ (t : ℕ) (s : ∀ i, S i) (seq : Fin t → ι),
      G.profileValue s ≤ G.profileValue (bestResponseWalk br s t seq)
  | 0, s, _ => le_rfl
  | t + 1, s, seq => by
      have hstep : G.profileValue s ≤
          G.profileValue (Function.update s (seq 0) (br (seq 0) s)) := by
        have h1 : G.utility (seq 0) (Function.update s (seq 0) (s (seq 0))) ≤
            G.utility (seq 0) (Function.update s (seq 0) (br (seq 0) s)) :=
          hbr (seq 0) s (s (seq 0))
        rw [Function.update_eq_self] at h1
        have h2 := IsBasic.utility_sub_utility_eq hG.utility_eq_marginal s (seq 0) (br (seq 0) s)
        linarith
      exact hstep.trans
        (profileValue_le_bestResponseWalk hG hbr t
          (Function.update s (seq 0) (br (seq 0) s)) (Fin.tail seq))

/-- **One-step expected welfare increase** ([TardosWexler2007], proof of Theorem 19.20, p. 506):
in a monotone basic utility game with `n ≥ 1` players, one uniformly random best-response move from
`s` increases expected social welfare by at least `(profileValue o - 2 * profileValue s) / n`. -/
theorem IsBasic.profileValue_le_expected_step_gain {G : UtilityGame ι S} [Nonempty ι]
    (hG : G.IsBasic) (hmono : Monotone G.socialValue) {br : ∀ i, (∀ j, S j) → S i}
    (hbr : G.IsBestResponse br) (s o : ∀ i, S i) :
    (G.profileValue o - 2 * G.profileValue s) / Fintype.card ι ≤
      G.expectedWalkValue br s 1 - G.profileValue s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : G.profileValue o - 2 * G.profileValue s ≤
      ∑ i : ι, (G.profileValue (Function.update s i (br i s)) - G.profileValue s) := by
    have hdev := hG.isValid.profileValue_sub_le_sum_deviation hmono s o
    have hbud := hG.sum_utility_le s
    have hβ : ∑ i : ι, G.utility i (Function.update s i (o i)) ≤
        ∑ i : ι, G.utility i s +
          ∑ i : ι, (G.profileValue (Function.update s i (br i s)) - G.profileValue s) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hbi := hbr i s (o i)
      have heq := IsBasic.utility_sub_utility_eq hG.utility_eq_marginal s i (br i s)
      linarith
    linarith
  rw [expectedWalkValue_one, div_le_iff₀ hn]
  have hmul : ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, G.profileValue (Function.update s i (br i s)) - G.profileValue s) *
        (Fintype.card ι : ℝ) =
      ∑ i : ι, (G.profileValue (Function.update s i (br i s)) - G.profileValue s) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  linarith

omit [DecidableEq ι] in
private theorem one_sub_two_div_card_nonneg (hn2 : 2 ≤ Fintype.card ι) :
    0 ≤ 1 - 2 / (Fintype.card ι : ℝ) := by
  have hn_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr (by omega)
  have hn_real : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn2
  rw [sub_nonneg, div_le_one hn_pos]
  exact hn_real

/-- **Multi-step geometric contraction** ([TardosWexler2007], proof of Theorem 19.20, p. 506):
when `n = Fintype.card ι ≥ 2`, the expected welfare gap `V(o) - 2 * E[V(S_t)]` shrinks by at least
a `(1 - 2 / n)` factor at every random best-response step. -/
theorem IsBasic.profileValue_sub_two_mul_expectedWalkValue_le {G : UtilityGame ι S}
    (hG : G.IsBasic) (hmono : Monotone G.socialValue) {br : ∀ i, (∀ j, S j) → S i}
    (hbr : G.IsBestResponse br) (hn2 : 2 ≤ Fintype.card ι) (s₀ o : ∀ i, S i) (t : ℕ) :
    G.profileValue o - 2 * G.expectedWalkValue br s₀ t ≤
      (1 - 2 / (Fintype.card ι : ℝ)) ^ t * (G.profileValue o - 2 * G.profileValue s₀) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hn_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hfactor_nonneg : 0 ≤ 1 - 2 / (Fintype.card ι : ℝ) := one_sub_two_div_card_nonneg hn2
  induction t generalizing s₀ with
  | zero =>
      simp only [expectedWalkValue_zero, pow_zero, one_mul, le_rfl]
  | succ t ih =>
      rw [expectedWalkValue_succ]
      have hcard : ∑ _i : ι, G.profileValue o = (Fintype.card ι : ℝ) * G.profileValue o := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hrewrite : G.profileValue o -
          2 * ((Fintype.card ι : ℝ)⁻¹ *
            ∑ i : ι, G.expectedWalkValue br (Function.update s₀ i (br i s₀)) t) =
          (Fintype.card ι : ℝ)⁻¹ *
            ∑ i : ι, (G.profileValue o -
              2 * G.expectedWalkValue br (Function.update s₀ i (br i s₀)) t) := by
        rw [Finset.sum_sub_distrib, hcard, ← Finset.mul_sum]
        field_simp
      rw [hrewrite]
      have hsum_ih : ∑ i : ι, (G.profileValue o -
            2 * G.expectedWalkValue br (Function.update s₀ i (br i s₀)) t) ≤
          ∑ i : ι, (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
            (G.profileValue o - 2 * G.profileValue (Function.update s₀ i (br i s₀))) :=
        Finset.sum_le_sum fun i _ => ih (Function.update s₀ i (br i s₀))
      have hpull : (Fintype.card ι : ℝ)⁻¹ *
            ∑ i : ι, (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
              (G.profileValue o - 2 * G.profileValue (Function.update s₀ i (br i s₀))) =
          (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
            (G.profileValue o - 2 * G.expectedWalkValue br s₀ 1) := by
        rw [← Finset.mul_sum, expectedWalkValue_one, Finset.sum_sub_distrib, hcard,
          ← Finset.mul_sum]
        field_simp
      have hone : G.profileValue o - 2 * G.expectedWalkValue br s₀ 1 ≤
          (1 - 2 / (Fintype.card ι : ℝ)) * (G.profileValue o - 2 * G.profileValue s₀) := by
        have hstep := hG.profileValue_le_expected_step_gain hmono hbr s₀ o
        have halg : (1 - 2 / (Fintype.card ι : ℝ)) * (G.profileValue o - 2 * G.profileValue s₀) =
            (G.profileValue o - 2 * G.profileValue s₀) -
              2 * ((G.profileValue o - 2 * G.profileValue s₀) / Fintype.card ι) := by
          field_simp
        linarith
      calc
        (Fintype.card ι : ℝ)⁻¹ *
            ∑ i : ι, (G.profileValue o -
              2 * G.expectedWalkValue br (Function.update s₀ i (br i s₀)) t)
          ≤ (Fintype.card ι : ℝ)⁻¹ *
              ∑ i : ι, (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
                (G.profileValue o - 2 * G.profileValue (Function.update s₀ i (br i s₀))) :=
            mul_le_mul_of_nonneg_left hsum_ih (inv_nonneg.mpr hn_pos.le)
        _ = (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
              (G.profileValue o - 2 * G.expectedWalkValue br s₀ 1) := hpull
        _ ≤ (1 - 2 / (Fintype.card ι : ℝ)) ^ t *
              ((1 - 2 / (Fintype.card ι : ℝ)) * (G.profileValue o - 2 * G.profileValue s₀)) :=
            mul_le_mul_of_nonneg_left hone (pow_nonneg hfactor_nonneg t)
        _ = (1 - 2 / (Fintype.card ι : ℝ)) ^ (t + 1) *
              (G.profileValue o - 2 * G.profileValue s₀) := by
            rw [pow_succ, mul_assoc]

/-- **Random Best-Response Convergence Bound** ([MirrokniVetta2004]; [GoemansMirrokniVetta2005];
[TardosWexler2007], Theorem 19.20, p. 506): in a monotone basic utility game with `n ≥ 1` players
and `0 ≤ socialValue ∅`, starting from any profile `s₀`, for every `ε > 0` and every horizon
`t : ℕ` with `(n / 2) * log (1 / ε) ≤ t`, the expected social welfare after `t` uniformly random
best-response moves is at least `(1 / 2 - ε)` times the social welfare of any profile `o`. -/
theorem IsBasic.mul_profileValue_le_expectedWalkValue {G : UtilityGame ι S} [Nonempty ι]
    (hG : G.IsBasic) (hmono : Monotone G.socialValue) (h0 : 0 ≤ G.socialValue ∅)
    {br : ∀ i, (∀ j, S j) → S i} (hbr : G.IsBestResponse br) {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : (Fintype.card ι : ℝ) / 2 * Real.log (1 / ε) ≤ t) (s₀ o : ∀ i, S i) :
    (1 / 2 - ε) * G.profileValue o ≤ G.expectedWalkValue br s₀ t := by
  have hVo : 0 ≤ G.profileValue o :=
    Submodular.nonneg_of_empty_nonneg_of_monotone h0 hmono (profileSet o)
  have hVs0 : 0 ≤ G.profileValue s₀ :=
    Submodular.nonneg_of_empty_nonneg_of_monotone h0 hmono (profileSet s₀)
  by_cases hε_half : 1 / 2 ≤ ε
  · have hneg : (1 / 2 - ε) * G.profileValue o ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hVo
    exact hneg.trans (expectedWalkValue_nonneg h0 hmono br s₀ t)
  · push Not at hε_half
    rcases Nat.lt_or_ge (Fintype.card ι) 2 with hn1 | hn2
    · have hcard1 : Fintype.card ι = 1 := by
        have hpos := Fintype.card_pos (α := ι)
        omega
      have hlog_pos : 0 < Real.log (1 / ε) := by
        apply Real.log_pos
        rw [one_lt_div hε]
        linarith
      have ht_pos : 0 < t := by
        by_contra ht0
        have ht_zero : t = 0 := by omega
        subst ht_zero
        rw [hcard1, Nat.cast_one, Nat.cast_zero] at ht
        linarith
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_pos.ne'
      obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard1
      have ho_eq : o = Function.update s₀ i₀ (o i₀) := by
        ext j
        rw [hi₀ j, Function.update_self]
      have hstep_opt : G.profileValue o ≤ G.profileValue (Function.update s₀ i₀ (br i₀ s₀)) := by
        rw [ho_eq]
        have h1 := hbr i₀ s₀ (o i₀)
        have h2 := IsBasic.utility_sub_utility_eq hG.utility_eq_marginal s₀ i₀ (o i₀)
        have h3 := IsBasic.utility_sub_utility_eq hG.utility_eq_marginal s₀ i₀ (br i₀ s₀)
        linarith
      have hall : ∀ seq : Fin (t' + 1) → ι,
          G.profileValue o ≤ G.profileValue (bestResponseWalk br s₀ (t' + 1) seq) := by
        intro seq
        rw [bestResponseWalk_succ, hi₀ (seq 0)]
        exact hstep_opt.trans
          (profileValue_le_bestResponseWalk hG hbr t'
            (Function.update s₀ i₀ (br i₀ s₀)) (Fin.tail seq))
      have hexp : G.profileValue o ≤ G.expectedWalkValue br s₀ (t' + 1) := by
        rw [expectedWalkValue, hcard1, Nat.cast_one, inv_one, one_pow, one_mul]
        have hsum : ∑ _seq : Fin (t' + 1) → ι, G.profileValue o ≤
            ∑ seq : Fin (t' + 1) → ι, G.profileValue (bestResponseWalk br s₀ (t' + 1) seq) :=
          Finset.sum_le_sum fun seq _ => hall seq
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, hcard1,
          Finset.prod_const_one, one_smul] using hsum
      have hhalf : (1 / 2 - ε) * G.profileValue o ≤ G.profileValue o :=
        mul_le_of_le_one_left hVo (by linarith)
      exact hhalf.trans hexp
    · have hn_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr (by omega)
      have hfactor_nonneg : 0 ≤ 1 - 2 / (Fintype.card ι : ℝ) := one_sub_two_div_card_nonneg hn2
      have hdecay := hG.profileValue_sub_two_mul_expectedWalkValue_le hmono hbr hn2 s₀ o t
      have hinit : G.profileValue o - 2 * G.profileValue s₀ ≤ G.profileValue o := by linarith
      have hpow_exp : (1 - 2 / (Fintype.card ι : ℝ)) ^ t ≤ ε := by
        have hexp1 : 1 - 2 / (Fintype.card ι : ℝ) ≤ Real.exp (-(2 / (Fintype.card ι : ℝ))) :=
          Real.one_sub_le_exp_neg (2 / (Fintype.card ι : ℝ))
        have hexp_pow : (1 - 2 / (Fintype.card ι : ℝ)) ^ t ≤
            Real.exp ((t : ℝ) * (-(2 / (Fintype.card ι : ℝ)))) := by
          calc
            (1 - 2 / (Fintype.card ι : ℝ)) ^ t
              ≤ Real.exp (-(2 / (Fintype.card ι : ℝ))) ^ t :=
                pow_le_pow_left₀ hfactor_nonneg hexp1 t
            _ = Real.exp ((t : ℝ) * (-(2 / (Fintype.card ι : ℝ)))) :=
                (Real.exp_nat_mul _ t).symm
        have hexponent : (t : ℝ) * (-(2 / (Fintype.card ι : ℝ))) ≤ Real.log ε := by
          have hlog_inv : Real.log (1 / ε) = -Real.log ε := by
            rw [one_div, Real.log_inv]
          have ht' : (Fintype.card ι : ℝ) * Real.log (1 / ε) ≤ 2 * (t : ℝ) := by linarith
          have hdiv : Real.log (1 / ε) ≤ 2 * (t : ℝ) / (Fintype.card ι : ℝ) := by
            rwa [le_div_iff₀ hn_pos, mul_comm]
          have hrew : (t : ℝ) * (-(2 / (Fintype.card ι : ℝ))) =
              -(2 * (t : ℝ) / (Fintype.card ι : ℝ)) := by ring
          linarith
        exact hexp_pow.trans ((Real.exp_le_exp.mpr hexponent).trans_eq (Real.exp_log hε))
      have hbound : G.profileValue o - 2 * G.expectedWalkValue br s₀ t ≤ ε * G.profileValue o := by
        calc
          G.profileValue o - 2 * G.expectedWalkValue br s₀ t
            ≤ (1 - 2 / (Fintype.card ι : ℝ)) ^ t * (G.profileValue o - 2 * G.profileValue s₀) :=
              hdecay
          _ ≤ (1 - 2 / (Fintype.card ι : ℝ)) ^ t * G.profileValue o :=
              mul_le_mul_of_nonneg_left hinit (pow_nonneg hfactor_nonneg t)
          _ ≤ ε * G.profileValue o :=
              mul_le_mul_of_nonneg_right hpow_exp hVo
      nlinarith

end BasicWalk

end RandomBestResponse

/-! ## Closed-neighborhood wealth-sharing location game (Exercise 19.16) -/

section NeighborhoodGame

/-- Closed neighborhood `N[v] = {v} ∪ N(v)` of vertex `v` in an undirected simple graph `H`. -/
def closedNeighborhood {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (v : V) : Finset V :=
  insert v (H.neighborFinset v)

@[simp]
theorem mem_closedNeighborhood {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {u v : V} :
    u ∈ closedNeighborhood H v ↔ u = v ∨ H.Adj v u := by
  simp only [closedNeighborhood, mem_insert, SimpleGraph.mem_neighborFinset]

theorem mem_closedNeighborhood_comm {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {u v : V} :
    u ∈ closedNeighborhood H v ↔ v ∈ closedNeighborhood H u := by
  simp only [mem_closedNeighborhood, H.adj_comm, eq_comm]

/-- **Closed-neighborhood wealth-sharing location game** ([TardosWexler2007], Exercise 19.16,
p. 515): `k` players choose vertices of `H`; each vertex `v` splits one unit of wealth equally
among all players located in `N[v]` (lost if none), and social welfare counts the vertices with at
least one player in `N[v]`. -/
noncomputable def neighborhoodGame (ι : Type*) {V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : UtilityGame ι (fun _ => V) where
  socialValue :=
    Submodular.weightedCoverage (fun x : Σ _ : ι, V => closedNeighborhood H x.2) fun _ => (1 : ℝ)
  utility i s :=
    ∑ v ∈ closedNeighborhood H (s i),
      (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card

@[simp]
theorem neighborhoodGame_socialValue_apply (ι : Type*) {V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Σ _ : ι, V)) :
    (neighborhoodGame ι H).socialValue T =
      ∑ _v ∈ T.biUnion (fun x => closedNeighborhood H x.2), (1 : ℝ) := by
  rfl

@[simp]
theorem neighborhoodGame_utility_apply {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (i : ι) (s : ι → V) :
    (neighborhoodGame ι H).utility i s =
      ∑ v ∈ closedNeighborhood H (s i),
        (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card := by
  rfl

/-- Social welfare in the closed-neighborhood location game is monotone ([TardosWexler2007],
Exercise 19.16(b)). -/
theorem monotone_neighborhoodGame_socialValue (ι : Type*) {V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    Monotone (neighborhoodGame ι H).socialValue :=
  Submodular.monotone_weightedCoverage _ fun _ => zero_le_one

private theorem biUnion_profileSet_closedNeighborhood {ι V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (s : ι → V) :
    (profileSet (S := fun _ => V) s).biUnion (fun x => closedNeighborhood H x.2) =
      Finset.univ.filter fun v : V =>
        (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).Nonempty := by
  ext v
  simp only [mem_biUnion, mem_profileSet, mem_filter, mem_univ, true_and, Finset.Nonempty]
  constructor
  · rintro ⟨⟨j, u⟩, hju, hv⟩
    dsimp only at hju hv
    subst hju
    exact ⟨j, (mem_closedNeighborhood_comm H).mp hv⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨j, s j⟩, rfl, (mem_closedNeighborhood_comm H).mp hj⟩

/-- **Exercise 19.16(b)** ([TardosWexler2007], p. 515): for every undirected graph `H`, the
closed-neighborhood wealth-sharing location game is a valid utility game. -/
theorem isValid_neighborhoodGame (ι : Type*) {V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    (neighborhoodGame ι H).IsValid where
  isSubmodular := Submodular.isSubmodular_weightedCoverage _ fun _ => zero_le_one
  sum_utility_le s := by
    have hcov : (neighborhoodGame ι H).profileValue s =
        ∑ v ∈ Finset.univ.filter (fun v : V =>
          (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).Nonempty), (1 : ℝ) := by
      change ∑ v ∈ (profileSet (S := fun _ => V) s).biUnion (fun x => closedNeighborhood H x.2),
        (1 : ℝ) = _
      rw [biUnion_profileSet_closedNeighborhood]
    rw [hcov]
    have hswap : ∑ i : ι, (neighborhoodGame ι H).utility i s =
        ∑ v : V, ∑ i ∈ Finset.univ.filter (fun j : ι => s j ∈ closedNeighborhood H v),
          (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card := by
      simp only [neighborhoodGame_utility_apply]
      trans ∑ i : ι, ∑ v : V,
          if v ∈ closedNeighborhood H (s i) then
            (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card
          else 0
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext v
        simp only [mem_filter, mem_univ, true_and]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_closedNeighborhood_comm]
    rw [hswap]
    refine le_of_eq ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with hne
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℝ) < (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card :=
        Nat.cast_pos.mpr hne.card_pos
      exact mul_one_div_cancel hpos.ne'
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
  marginal_le_utility i s := by
    let covAll := (profileSet (S := fun _ => V) s).biUnion (fun x => closedNeighborhood H x.2)
    let covOther :=
      (profileWithout (S := fun _ => V) s i).biUnion (fun x => closedNeighborhood H x.2)
    have hsub : covOther ⊆ covAll := by
      intro v hv
      rcases mem_biUnion.mp hv with ⟨x, hx, hvx⟩
      exact mem_biUnion.mpr ⟨x, profileWithout_subset_profileSet (S := fun _ => V) s i hx, hvx⟩
    have hdiff : (neighborhoodGame ι H).profileValue s -
          (neighborhoodGame ι H).socialValue (profileWithout (S := fun _ => V) s i) =
        ∑ v ∈ covAll \ covOther, (1 : ℝ) := by
      change (∑ v ∈ covAll, (1 : ℝ)) - (∑ v ∈ covOther, (1 : ℝ)) = _
      rw [← Finset.sum_sdiff hsub]
      ring
    rw [hdiff, neighborhoodGame_utility_apply]
    have hexcl_sub : covAll \ covOther ⊆ closedNeighborhood H (s i) := by
      intro v hv
      rcases mem_sdiff.mp hv with ⟨hvA, hvO⟩
      rcases mem_biUnion.mp hvA with ⟨⟨j, u⟩, hju, hv_nhd⟩
      have hsu : s j = u := mem_profileSet.mp hju
      subst hsu
      by_cases hji : j = i
      · subst hji
        exact hv_nhd
      · exfalso
        exact hvO (mem_biUnion.mpr ⟨⟨j, s j⟩, mem_profileWithout.mpr ⟨hji, rfl⟩, hv_nhd⟩)
    calc
      ∑ v ∈ covAll \ covOther, (1 : ℝ)
        ≤ ∑ v ∈ covAll \ covOther,
            (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hv_nhd : v ∈ closedNeighborhood H (s i) := hexcl_sub hv
          have hvO : v ∉ covOther := (mem_sdiff.mp hv).2
          have hfilt_eq :
              (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v) = {i} := by
            ext j
            simp only [mem_filter, mem_univ, true_and, mem_singleton]
            refine ⟨fun hj => ?_, fun hji => ?_⟩
            · by_contra hji
              exact hvO (mem_biUnion.mpr ⟨⟨j, s j⟩, mem_profileWithout.mpr ⟨hji, rfl⟩,
                (mem_closedNeighborhood_comm H).mp hj⟩)
            · subst hji
              exact (mem_closedNeighborhood_comm H).mp hv_nhd
          rw [hfilt_eq, card_singleton, Nat.cast_one, div_one]
      _ ≤ ∑ v ∈ closedNeighborhood H (s i),
            (1 : ℝ) / (Finset.univ.filter fun j : ι => s j ∈ closedNeighborhood H v).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hexcl_sub fun _ _ _ => by positivity

/-- Graph of one `(k + 2)`-vertex star together with `k + 1` isolated vertices, witnessing
asymptotic `PoA = 2` tightness in [TardosWexler2007], Exercise 19.16(a). -/
private def starPlusIsolates (k : ℕ) : SimpleGraph (Fin (k + 2) ⊕ Fin (k + 1)) where
  Adj x y :=
    (x = Sum.inl 0 ∧ ∃ r : Fin (k + 2), r ≠ 0 ∧ y = Sum.inl r) ∨
      (y = Sum.inl 0 ∧ ∃ r : Fin (k + 2), r ≠ 0 ∧ x = Sum.inl r)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨rfl, r, hr, h'⟩ | ⟨rfl, r, hr, h'⟩ <;> exact hr (Sum.inl.inj h').symm⟩

private instance (k : ℕ) : DecidableRel (starPlusIsolates k).Adj := by
  intro x y
  unfold starPlusIsolates
  infer_instance

private theorem closedNeighborhood_starPlusIsolates_center (k : ℕ) :
    closedNeighborhood (starPlusIsolates k) (Sum.inl 0) =
      Finset.univ.map Function.Embedding.inl := by
  ext v
  rw [mem_closedNeighborhood, mem_map]
  dsimp only [starPlusIsolates]
  rcases v with r | j
  · constructor
    · intro _
      exact ⟨r, mem_univ r, rfl⟩
    · intro _
      by_cases hr : r = 0
      · exact Or.inl (congrArg Sum.inl hr)
      · exact Or.inr (Or.inl ⟨rfl, r, hr, rfl⟩)
  · constructor
    · rintro (h | ⟨_, r, _, h⟩ | ⟨h, _⟩) <;> cases h
    · rintro ⟨r, _, h⟩
      cases h

private theorem closedNeighborhood_starPlusIsolates_inr (k : ℕ) (j : Fin (k + 1)) :
    closedNeighborhood (starPlusIsolates k) (Sum.inr j) = {Sum.inr j} := by
  ext v
  rw [mem_closedNeighborhood, mem_singleton]
  dsimp only [starPlusIsolates]
  rcases v with r | j'
  · constructor
    · rintro (h | ⟨h, _⟩ | ⟨_, _, _, h⟩) <;> cases h
    · intro h
      cases h
  · constructor
    · rintro (h | ⟨h, _⟩ | ⟨_, _, _, h⟩)
      · exact h
      · cases h
      · cases h
    · intro h
      exact Or.inl h

private theorem closedNeighborhood_starPlusIsolates_inl_subset (k : ℕ) (r : Fin (k + 2)) :
    closedNeighborhood (starPlusIsolates k) (Sum.inl r) ⊆
      Finset.univ.map Function.Embedding.inl := by
  intro v hv
  rw [mem_closedNeighborhood] at hv
  simp only [mem_map, mem_univ, Function.Embedding.inl_apply, true_and]
  rcases hv with rfl | hadj
  · exact ⟨r, rfl⟩
  · rcases hadj with ⟨_, r', _, rfl⟩ | ⟨rfl, _⟩
    · exact ⟨r', rfl⟩
    · exact ⟨0, rfl⟩

private theorem center_mem_closedNeighborhood_inl (k : ℕ) (r : Fin (k + 2)) :
    (Sum.inl 0 : Fin (k + 2) ⊕ Fin (k + 1)) ∈
      closedNeighborhood (starPlusIsolates k) (Sum.inl r) := by
  rw [mem_closedNeighborhood]
  by_cases hr : r = 0
  · exact Or.inl (congrArg Sum.inl hr.symm)
  · exact Or.inr (Or.inr ⟨rfl, r, hr, rfl⟩)

/-- **Exercise 19.16(a)** ([TardosWexler2007], p. 515): the price of anarchy of the
closed-neighborhood wealth-sharing location game can be arbitrarily close to `2` (for every
`ε > 0`, there is a finite simple graph `H` and nonempty player set `ι` admitting a pure Nash
equilibrium `s` with positive social welfare and an alternative profile `o` satisfying
`(2 - ε) * profileValue s < profileValue o`). -/
theorem exists_neighborhoodGame_isPureNash_mul_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (H : SimpleGraph (Fin (k + 2) ⊕ Fin (k + 1))) (_ : DecidableRel H.Adj)
      (s o : Fin (k + 2) → Fin (k + 2) ⊕ Fin (k + 1)),
      (neighborhoodGame (Fin (k + 2)) H).toCostGame.IsPureNash s ∧
      0 < (neighborhoodGame (Fin (k + 2)) H).profileValue s ∧
      (2 - ε) * (neighborhoodGame (Fin (k + 2)) H).profileValue s <
        (neighborhoodGame (Fin (k + 2)) H).profileValue o := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  let s : Fin (k + 2) → Fin (k + 2) ⊕ Fin (k + 1) := fun _ => Sum.inl 0
  let o : Fin (k + 2) → Fin (k + 2) ⊕ Fin (k + 1) := fun i =>
    if hi : i.val = 0 then Sum.inl 0 else Sum.inr ⟨i.val - 1, by omega⟩
  have hs_val : (neighborhoodGame (Fin (k + 2)) (starPlusIsolates k)).profileValue s =
      (k + 2 : ℝ) := by
    change ∑ _v ∈ (profileSet (S := fun _ => Fin (k + 2) ⊕ Fin (k + 1)) s).biUnion
      (fun x => closedNeighborhood (starPlusIsolates k) x.2), (1 : ℝ) = _
    have hbi : (profileSet (S := fun _ => Fin (k + 2) ⊕ Fin (k + 1)) s).biUnion
        (fun x => closedNeighborhood (starPlusIsolates k) x.2) =
          Finset.univ.map Function.Embedding.inl := by
      ext v
      simp only [mem_biUnion, mem_profileSet, s]
      constructor
      · rintro ⟨⟨_, u⟩, hu, hv⟩
        dsimp only at hu hv
        subst hu
        rwa [closedNeighborhood_starPlusIsolates_center] at hv
      · intro hv
        exact ⟨⟨0, Sum.inl 0⟩, rfl, by rwa [closedNeighborhood_starPlusIsolates_center]⟩
    rw [hbi, Finset.sum_const, card_map, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  refine ⟨k, starPlusIsolates k, inferInstance, s, o, ?_, ?_, ?_⟩
  · rw [isPureNash_toCostGame_iff]
    intro i a
    have hm_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
    have hs_util : (neighborhoodGame (Fin (k + 2)) (starPlusIsolates k)).utility i s = 1 := by
      rw [neighborhoodGame_utility_apply]
      change ∑ v ∈ closedNeighborhood (starPlusIsolates k) (Sum.inl 0),
        (1 : ℝ) / (Finset.univ.filter fun _ : Fin (k + 2) =>
          (Sum.inl 0 : Fin (k + 2) ⊕ Fin (k + 1)) ∈
            closedNeighborhood (starPlusIsolates k) v).card = 1
      rw [closedNeighborhood_starPlusIsolates_center]
      have hcongr : ∀ v ∈ (Finset.univ.map Function.Embedding.inl :
            Finset (Fin (k + 2) ⊕ Fin (k + 1))),
          (1 : ℝ) / (Finset.univ.filter fun _ : Fin (k + 2) =>
            (Sum.inl 0 : Fin (k + 2) ⊕ Fin (k + 1)) ∈
              closedNeighborhood (starPlusIsolates k) v).card =
            (1 : ℝ) / (k + 2 : ℕ) := by
        intro v hv
        rcases mem_map.mp hv with ⟨r, _, rfl⟩
        rw [Function.Embedding.inl_apply]
        have hfilt : (Finset.univ.filter fun _ : Fin (k + 2) =>
            (Sum.inl 0 : Fin (k + 2) ⊕ Fin (k + 1)) ∈
              closedNeighborhood (starPlusIsolates k) (Sum.inl r)) = Finset.univ := by
          ext _
          simp only [mem_filter, mem_univ, true_and, iff_true]
          exact center_mem_closedNeighborhood_inl k r
        rw [hfilt, card_univ, Fintype.card_fin]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, card_map, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      exact mul_one_div_cancel hm_pos.ne'
    rw [hs_util]
    rcases a with r | j
    · rw [neighborhoodGame_utility_apply, Function.update_self]
      have hsub := closedNeighborhood_starPlusIsolates_inl_subset k r
      have hterm_le : ∀ v ∈ closedNeighborhood (starPlusIsolates k) (Sum.inl r),
          (1 : ℝ) / (Finset.univ.filter fun j' : Fin (k + 2) =>
            Function.update s i (Sum.inl r) j' ∈
              closedNeighborhood (starPlusIsolates k) v).card ≤
            (1 : ℝ) / (k + 2 : ℕ) := by
        intro v hv
        rcases mem_map.mp (hsub hv) with ⟨r', _, rfl⟩
        rw [Function.Embedding.inl_apply] at hv ⊢
        have hfilt : (Finset.univ.filter fun j' : Fin (k + 2) =>
            Function.update s i (Sum.inl r) j' ∈
              closedNeighborhood (starPlusIsolates k) (Sum.inl r')) = Finset.univ := by
          ext j'
          simp only [mem_filter, mem_univ, true_and, iff_true]
          by_cases hji : j' = i
          · subst hji
            rw [Function.update_self]
            exact (mem_closedNeighborhood_comm (starPlusIsolates k)).mp hv
          · rw [Function.update_of_ne hji]
            exact center_mem_closedNeighborhood_inl k r'
        rw [hfilt, card_univ, Fintype.card_fin]
      calc
        ∑ v ∈ closedNeighborhood (starPlusIsolates k) (Sum.inl r),
            (1 : ℝ) / (Finset.univ.filter fun j' : Fin (k + 2) =>
              Function.update s i (Sum.inl r) j' ∈
                closedNeighborhood (starPlusIsolates k) v).card
          ≤ ∑ _v ∈ closedNeighborhood (starPlusIsolates k) (Sum.inl r),
              (1 : ℝ) / (k + 2 : ℕ) := Finset.sum_le_sum hterm_le
        _ ≤ ∑ _v ∈ (Finset.univ.map Function.Embedding.inl :
              Finset (Fin (k + 2) ⊕ Fin (k + 1))), (1 : ℝ) / (k + 2 : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 1 := by
            rw [Finset.sum_const, card_map, card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_one_div_cancel hm_pos.ne'
    · rw [neighborhoodGame_utility_apply, Function.update_self,
        closedNeighborhood_starPlusIsolates_inr, sum_singleton,
        closedNeighborhood_starPlusIsolates_inr]
      have hfilt : (Finset.univ.filter fun j' : Fin (k + 2) =>
          Function.update s i (Sum.inr j) j' ∈ ({Sum.inr j} : Finset _)) = {i} := by
        ext j'
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        by_cases hji : j' = i
        · subst hji
          simp only [Function.update_self]
        · simp only [Function.update_of_ne hji, s, reduceCtorEq, hji]
      rw [hfilt, card_singleton, Nat.cast_one, div_one]
  · rw [hs_val]
    positivity
  · have ho_val : (neighborhoodGame (Fin (k + 2)) (starPlusIsolates k)).profileValue o =
        (2 * k + 3 : ℝ) := by
      change ∑ _v ∈ (profileSet (S := fun _ => Fin (k + 2) ⊕ Fin (k + 1)) o).biUnion
        (fun x => closedNeighborhood (starPlusIsolates k) x.2), (1 : ℝ) = _
      have hbi : (profileSet (S := fun _ => Fin (k + 2) ⊕ Fin (k + 1)) o).biUnion
          (fun x => closedNeighborhood (starPlusIsolates k) x.2) = Finset.univ := by
        ext v
        simp only [mem_biUnion, mem_profileSet, mem_univ, iff_true]
        rcases v with r | j
        · refine ⟨⟨0, o 0⟩, rfl, ?_⟩
          have ho0 : o 0 = Sum.inl 0 := by simp only [o, Fin.val_zero, ↓reduceDIte]
          rw [ho0, closedNeighborhood_starPlusIsolates_center]
          exact mem_map.mpr ⟨r, mem_univ r, rfl⟩
        · let idx : Fin (k + 2) := ⟨j.val + 1, by omega⟩
          refine ⟨⟨idx, o idx⟩, rfl, ?_⟩
          have hoidx : o idx = Sum.inr j := by
            simp only [o, idx, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
          rw [hoidx, closedNeighborhood_starPlusIsolates_inr]
          exact mem_singleton_self _
      rw [hbi, Finset.sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [hs_val, ho_val]
    have hk_eps : 1 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
    nlinarith

end NeighborhoodGame

end UtilityGame

end Cslib.GameTheory
