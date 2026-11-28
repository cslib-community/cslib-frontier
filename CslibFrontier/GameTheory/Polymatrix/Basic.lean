/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.CostGame
public import CslibFrontier.GameTheory.Strategic.PotentialCharacterization
public import CslibFrontier.GameTheory.Strategic.Stability
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polymatrix games and pairwise potential characterizations

In a **polymatrix game** ([Janovskaja1968]; [Howson1972]), players `i : ι` interact pairwise: for
each ordered pair of distinct players `i ≠ j`, a cost matrix `edgeCost i j : S i → S j → ℝ` gives
the pairwise cost incurred by `i` against `j`, and player `i`'s total cost at profile `s` is
`∑ j ∈ univ.erase i, edgeCost i j (s i) (s j)` (`PolymatrixGame.toCostGame`). Two-player
`BimatrixGame`s are the `Bool`-indexed special case (`PolymatrixGame.ofBimatrixGame`).

Under independent mixed strategies `p`, expectations factor into pairwise bilinear forms
(`deviationCost_toCostGame`, `expectedCost_toCostGame`), characterizing mixed Nash equilibria of
polymatrix games purely through pairwise matrix-vector inequalities (`isMixedNash_toCostGame_iff`,
[Janovskaja1968]; [Howson1972]).

When pairwise interaction matrices are symmetric (`PolymatrixGame.IsSymmetric`:
`edgeCost i j a b = edgeCost j i b a` for `i ≠ j`), half the social cost
`edgePotential P s = (1 / 2) * ∑ i, ∑ j ∈ univ.erase i, edgeCost i j (s i) (s j)` is an exact
potential (`IsSymmetric.isExactPotential_edgePotential`). Consequently every finite symmetric
polymatrix game has the finite improvement property and—by the potential function method
([TardosWexler2007], Theorem 19.13)—has **price of stability `1`**, admitting a pure Nash
equilibrium that globally minimizes social cost (`IsSymmetric.exists_isPureNash_socialCost_le`).

More generally, applying Monderer and Shapley's four-cycle curl-zero criterion
(`CostGame.exists_isExactPotential_iff_fourCycleZero`, [MondererShapley1996], Corollary 2.9,
p. 131), a polymatrix game with nonempty strategy sets admits an exact potential if and only if
every pair `i ≠ j` satisfies cross-difference symmetry (`PolymatrixGame.IsPairwisePotential`),
if and only if every skew-symmetric edge difference `edgeCost i j a b - edgeCost j i b a` separates
additively as `u i j a + v i j b` (`PolymatrixGame.IsSeparableSkew`). Under baseline zero
normalization at a reference profile `z`, exact potentiality is equivalent to `IsSymmetric`
(`isSymmetric_iff_exists_isExactPotential_of_zero_at_base`).

## Main definitions

* `Cslib.GameTheory.PolymatrixGame`: multiplayer game specified by pairwise cost matrices
  `edgeCost i j : S i → S j → ℝ` ([Janovskaja1968]; [Howson1972]).
* `Cslib.GameTheory.PolymatrixGame.toCostGame`: induced `CostGame ι S`.
* `Cslib.GameTheory.PolymatrixGame.ofBimatrixGame`: embedding of a two-player `BimatrixGame`.
* `Cslib.GameTheory.PolymatrixGame.IsSymmetric`, `Cslib.GameTheory.PolymatrixGame.edgePotential`:
  pairwise symmetric (coordination) polymatrix games and their quadratic edge potential.
* `Cslib.GameTheory.PolymatrixGame.skewEdge`,
  `Cslib.GameTheory.PolymatrixGame.IsPairwisePotential`,
  `Cslib.GameTheory.PolymatrixGame.IsSeparableSkew`: skew-symmetric edge part, pairwise cross-
  difference vanishing, and additive row-plus-column separability of skew edges.

## Main results

* `Cslib.GameTheory.PolymatrixGame.deviationCost_toCostGame`,
  `Cslib.GameTheory.PolymatrixGame.expectedCost_toCostGame`,
  `Cslib.GameTheory.PolymatrixGame.isMixedNash_toCostGame_iff`: pairwise bilinear mixed-cost
  decomposition and mixed Nash equilibrium characterization ([Janovskaja1968]; [Howson1972]).
* `Cslib.GameTheory.PolymatrixGame.IsSymmetric.isExactPotential_edgePotential`,
  `Cslib.GameTheory.PolymatrixGame.IsSymmetric.exists_isPureNash_socialCost_le`: exact edge
  potential and **price of stability `1`** for symmetric polymatrix games.
* `Cslib.GameTheory.PolymatrixGame.exists_isExactPotential_toCostGame_iff_isPairwisePotential`,
  `Cslib.GameTheory.PolymatrixGame.exists_isExactPotential_toCostGame_iff_isSeparableSkew`,
  `Cslib.GameTheory.PolymatrixGame.isSymmetric_iff_exists_isExactPotential_of_zero_at_base`:
  exact-potential characterizations of polymatrix games via [MondererShapley1996], Corollary 2.9.

## References

* [E. B. Janovskaja, *Equilibrium Points in Polymatrix Games*][Janovskaja1968]
* [J. T. Howson, Jr., *Equilibria of Polymatrix Games*][Howson1972]
* [D. Monderer and L. S. Shapley, *Potential Games*][MondererShapley1996]
* [É. Tardos and T. Wexler,
  *Network Formation Games and the Potential Function Method*][TardosWexler2007]
-/

public section

namespace Cslib.GameTheory

open Finset Function

/-- A **polymatrix game** on player set `ι` with strategy sets `S : ι → Type*`
([Janovskaja1968]; [Howson1972]): for each ordered pair `(i, j)` of distinct players, `edgeCost i j`
is the pairwise cost matrix paid by player `i` when interacting with player `j`. Diagonal entries
`edgeCost i i` are ignored by `toCostGame`. -/
structure PolymatrixGame (ι : Type*) (S : ι → Type*) where
  /-- Pairwise interaction cost `edgeCost i j a b` paid by player `i` playing `a` against `j`
  playing `b`. -/
  edgeCost : ∀ i j, S i → S j → ℝ

namespace PolymatrixGame

section Basic

variable {ι : Type*} {S : ι → Type*}

/-- The normal-form `CostGame` induced by a polymatrix game: player `i` pays the sum of its
pairwise interaction costs over all other players `j ≠ i`. -/
@[expose] def toCostGame [Fintype ι] [DecidableEq ι] (P : PolymatrixGame ι S) : CostGame ι S where
  cost i s := ∑ j ∈ univ.erase i, P.edgeCost i j (s i) (s j)

@[simp]
theorem toCostGame_cost [Fintype ι] [DecidableEq ι] (P : PolymatrixGame ι S) (i : ι)
    (s : ∀ k, S k) :
    P.toCostGame.cost i s = ∑ j ∈ univ.erase i, P.edgeCost i j (s i) (s j) :=
  rfl

/-- Embeds a two-player `BimatrixGame M N` (in payoff form) as a `Bool`-indexed `PolymatrixGame`
(in cost form). -/
@[expose] def ofBimatrixGame {M : Type*} {N : Type*} (G : BimatrixGame M N) :
    PolymatrixGame Bool (BimatrixGame.PureStrategy M N) where
  edgeCost
    | false, true => fun a b => -G.A a.down b.down
    | true, false => fun a b => -G.B b.down a.down
    | false, false => fun _ _ => 0
    | true, true => fun _ _ => 0

/-- The cost game of `ofBimatrixGame G` agrees identically with `BimatrixGame.toCostGame G`. -/
@[simp]
theorem toCostGame_ofBimatrixGame {M : Type*} {N : Type*} (G : BimatrixGame M N) :
    (ofBimatrixGame G).toCostGame = G.toCostGame := by
  unfold toCostGame BimatrixGame.toCostGame
  congr
  funext b s
  cases b <;> simp [ofBimatrixGame]

end Basic

/-! ### Bilinear mixed-strategy expectations and mixed Nash characterization -/

section Mixed

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]

/-- In a polymatrix game, player `i`'s unilateral expected cost `deviationCost` against a product
of probability vectors `p` decomposes into the sum of pairwise matrix-vector products over `j ≠ i`
([Janovskaja1968]; [Howson1972]). -/
theorem deviationCost_toCostGame (P : PolymatrixGame ι S) {p : ∀ i, S i → ℝ}
    (hp : ∀ k, ∑ c, p k c = 1) (i : ι) (a : S i) :
    P.toCostGame.deviationCost p i a =
      ∑ j ∈ univ.erase i, ∑ b : S j, p j b * P.edgeCost i j a b := by
  rw [CostGame.deviationCost_def]
  simp only [toCostGame_cost, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  simp only [update_self, update_of_ne (ne_of_mem_erase hj)]
  exact sum_productWeight_mul_apply (fun k _ => hp k) (fun b => P.edgeCost i j a b)

/-- Player `i`'s expected cost in `P.toCostGame` is the sum of pairwise bilinear forms
`∑_{j ≠ i} p_iᵀ A_{ij} p_j`. -/
theorem expectedCost_toCostGame (P : PolymatrixGame ι S) {p : ∀ i, S i → ℝ}
    (hp : ∀ k, ∑ c, p k c = 1) (i : ι) :
    P.toCostGame.expectedCost p i =
      ∑ j ∈ univ.erase i, ∑ a : S i, ∑ b : S j, p i a * (p j b * P.edgeCost i j a b) := by
  rw [← P.toCostGame.sum_mul_deviationCost_eq_expectedCost p (hp i)]
  simp only [P.deviationCost_toCostGame hp, mul_sum]
  exact sum_comm

/-- Pairwise bilinear characterization of mixed Nash equilibria in a polymatrix game
([Janovskaja1968]; [Howson1972]). -/
theorem isMixedNash_toCostGame_iff (P : PolymatrixGame ι S) {p : ∀ i, S i → ℝ} :
    P.toCostGame.IsMixedNash p ↔
      (∀ i, IsMixedStrategy (p i)) ∧
        ∀ i (a' : S i),
          ∑ j ∈ univ.erase i, ∑ a : S i, ∑ b : S j, p i a * (p j b * P.edgeCost i j a b) ≤
            ∑ j ∈ univ.erase i, ∑ b : S j, p j b * P.edgeCost i j a' b := by
  refine and_congr_right fun hmix => forall₂_congr fun i a' => ?_
  have hp1 : ∀ k, ∑ c, p k c = 1 := fun k => (hmix k).sum_eq_one
  rw [P.expectedCost_toCostGame hp1 i, P.deviationCost_toCostGame hp1 i a']

end Mixed

/-! ### Symmetric polymatrix games, exact edge potential, and price of stability -/

section SymmetricAndPotential

variable {ι : Type*} {S : ι → Type*}

/-- A polymatrix game is **pairwise symmetric** (a pairwise coordination / undirected edge game) if
`edgeCost i j a b = edgeCost j i b a` for all `i ≠ j`. -/
@[expose] def IsSymmetric (P : PolymatrixGame ι S) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ (a : S i) (b : S j), P.edgeCost i j a b = P.edgeCost j i b a

/-- Skew-symmetric part `edgeCost i j a b - edgeCost j i b a` of a directed polymatrix interaction
pair `(i, j)`. -/
@[expose] def skewEdge (P : PolymatrixGame ι S) (i j : ι) (a : S i) (b : S j) : ℝ :=
  P.edgeCost i j a b - P.edgeCost j i b a

/-- Pairwise cross-difference vanishing: for each pair `i ≠ j`, the `2 × 2` cross-difference of
`skewEdge P i j` vanishes on every strategy rectangle `(xᵢ, yᵢ) × (xⱼ, yⱼ)`. -/
@[expose] def IsPairwisePotential (P : PolymatrixGame ι S) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ (xᵢ yᵢ : S i) (xⱼ yⱼ : S j),
    (P.skewEdge i j yᵢ xⱼ - P.skewEdge i j xᵢ xⱼ) +
      (P.skewEdge i j xᵢ yⱼ - P.skewEdge i j yᵢ yⱼ) = 0

/-- `P` has **separable skew-symmetry** if for every `i ≠ j`, `edgeCost i j a b - edgeCost j i b a`
splits additively into a self-action term `u i j a` and a dummy opponent-action term `v i j b`. -/
@[expose] def IsSeparableSkew (P : PolymatrixGame ι S) : Prop :=
  ∃ (u : ∀ i, ι → S i → ℝ) (v : ι → ∀ j, S j → ℝ),
    ∀ ⦃i j : ι⦄, i ≠ j → ∀ (a : S i) (b : S j), P.skewEdge i j a b = u i j a + v i j b

private theorem IsSeparableSkew.isPairwisePotential {P : PolymatrixGame ι S}
    (h : P.IsSeparableSkew) : P.IsPairwisePotential := by
  obtain ⟨u, v, huv⟩ := h
  intro i j hij xᵢ yᵢ xⱼ yⱼ
  rw [huv hij yᵢ xⱼ, huv hij xᵢ xⱼ, huv hij xᵢ yⱼ, huv hij yᵢ yⱼ]
  ring

/-- With nonempty strategy sets, pairwise cross-difference vanishing is equivalent to additive
row-plus-column separability of `skewEdge`. -/
theorem isPairwisePotential_iff_isSeparableSkew [∀ k, Nonempty (S k)] {P : PolymatrixGame ι S} :
    P.IsPairwisePotential ↔ P.IsSeparableSkew := by
  refine ⟨fun h => ?_, IsSeparableSkew.isPairwisePotential⟩
  let z : ∀ k, S k := fun k => Classical.arbitrary (S k)
  exact ⟨fun i j a => P.skewEdge i j a (z j) - P.skewEdge i j (z i) (z j),
    fun i j b => P.skewEdge i j (z i) b, fun i j hij a b => by linarith [h hij (z i) a (z j) b]⟩

variable [Fintype ι] [DecidableEq ι]

/-- **Quadratic edge potential** `(1 / 2) * ∑ i, ∑ j ≠ i, edgeCost i j (s i) (s j)` of a symmetric
polymatrix game (half the social cost, counting each undirected pair `{i, j}` once). -/
noncomputable def edgePotential (P : PolymatrixGame ι S) (s : ∀ i, S i) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j ∈ univ.erase i, P.edgeCost i j (s i) (s j)

theorem edgePotential_def (P : PolymatrixGame ι S) (s : ∀ i, S i) :
    P.edgePotential s = (1 / 2 : ℝ) * ∑ i, ∑ j ∈ univ.erase i, P.edgeCost i j (s i) (s j) := by
  rw [edgePotential]

/-- The social cost of a polymatrix game is twice `edgePotential`. -/
theorem socialCost_eq_two_mul_edgePotential (P : PolymatrixGame ι S) (s : ∀ i, S i) :
    P.toCostGame.socialCost s = 2 * P.edgePotential s := by
  rw [CostGame.socialCost, edgePotential_def]
  simp only [toCostGame_cost]
  ring

/-- **Symmetric polymatrix games are exact potential games**: when `P.IsSymmetric`,
`P.edgePotential` is an exact potential for `P.toCostGame`. -/
theorem IsSymmetric.isExactPotential_edgePotential {P : PolymatrixGame ι S} (h : P.IsSymmetric) :
    P.toCostGame.IsExactPotential P.edgePotential := by
  intro s i a
  rw [edgePotential_def, edgePotential_def]
  have splitTotal : ∀ x : ∀ k, S k,
      (∑ k, ∑ j ∈ univ.erase k, P.edgeCost k j (x k) (x j)) =
        (∑ j ∈ univ.erase i, P.edgeCost i j (x i) (x j)) +
          ∑ k ∈ univ.erase i,
            (P.edgeCost k i (x k) (x i) +
              ∑ j ∈ (univ.erase k).erase i, P.edgeCost k j (x k) (x j)) := by
    intro x
    rw [← add_sum_erase univ _ (mem_univ i)]
    congr 1
    exact sum_congr rfl fun k hk =>
      (add_sum_erase (univ.erase k) _ (mem_erase.2 ⟨(ne_of_mem_erase hk).symm, mem_univ i⟩)).symm
  rw [splitTotal (update s i a), splitTotal s]
  have h_self : ∑ j ∈ univ.erase i, P.edgeCost i j (update s i a i) (update s i a j) =
      ∑ j ∈ univ.erase i, P.edgeCost i j a (s j) :=
    sum_congr rfl fun j hj => by rw [update_self, update_of_ne (ne_of_mem_erase hj)]
  have h_other : ∑ k ∈ univ.erase i,
        (P.edgeCost k i (update s i a k) (update s i a i) +
          ∑ j ∈ (univ.erase k).erase i, P.edgeCost k j (update s i a k) (update s i a j)) -
      ∑ k ∈ univ.erase i,
        (P.edgeCost k i (s k) (s i) +
          ∑ j ∈ (univ.erase k).erase i, P.edgeCost k j (s k) (s j)) =
      ∑ k ∈ univ.erase i, (P.edgeCost i k a (s k) - P.edgeCost i k (s i) (s k)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := ne_of_mem_erase hk
    have hrest : ∑ j ∈ (univ.erase k).erase i,
          P.edgeCost k j (update s i a k) (update s i a j) =
        ∑ j ∈ (univ.erase k).erase i, P.edgeCost k j (s k) (s j) :=
      sum_congr rfl fun j hj => by
        rw [update_of_ne hki, update_of_ne (ne_of_mem_erase hj)]
    rw [hrest, update_of_ne hki, update_self, h hki, h hki]
    ring
  rw [sum_sub_distrib] at h_other
  rw [toCostGame_cost, toCostGame_cost, h_self]
  linarith

/-- Every finite symmetric polymatrix game has the finite improvement property. -/
theorem IsSymmetric.hasFIP [∀ i, Finite (S i)] {P : PolymatrixGame ι S} (h : P.IsSymmetric) :
    P.toCostGame.HasFIP :=
  h.isExactPotential_edgePotential.isGeneralizedOrdinalPotential.hasFIP

/-- **Price of stability `1` for symmetric polymatrix games** (via [TardosWexler2007],
Theorem 19.13): every finite symmetric polymatrix game with nonempty strategy sets admits a pure
Nash equilibrium that globally minimizes `socialCost`. -/
theorem IsSymmetric.exists_isPureNash_socialCost_le [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    {P : PolymatrixGame ι S} (h : P.IsSymmetric) :
    ∃ s, P.toCostGame.IsPureNash s ∧
      ∀ s', P.toCostGame.socialCost s ≤ P.toCostGame.socialCost s' := by
  have : Finite (∀ i, S i) := Pi.finite
  obtain ⟨s, hs_nash, hs_opt⟩ :=
    h.isExactPotential_edgePotential.isGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le
      (A := 2) (B := 1 / 2) (by norm_num)
      (fun x => le_of_eq (P.socialCost_eq_two_mul_edgePotential x))
      (fun x => le_of_eq (by linarith [P.socialCost_eq_two_mul_edgePotential x]))
  exact ⟨s, hs_nash, fun s' => by linarith [hs_opt s']⟩

private theorem rect_player_diff (P : PolymatrixGame ι S) {u v : ι} (huv : u ≠ v)
    (s : ∀ k, S k) (a b : S u) (c d : S v) :
    (P.toCostGame.cost u (update (update s u b) v c) -
        P.toCostGame.cost u (update (update s u a) v c)) +
      (P.toCostGame.cost u (update (update s u a) v d) -
        P.toCostGame.cost u (update (update s u b) v d)) =
      (P.edgeCost u v b c - P.edgeCost u v a c) +
        (P.edgeCost u v a d - P.edgeCost u v b d) := by
  have hterm : ∀ (x : S u) (y : S v),
      P.toCostGame.cost u (update (update s u x) v y) =
        P.edgeCost u v x y + ∑ k ∈ (univ.erase u).erase v, P.edgeCost u k x (s k) := by
    intro x y
    rw [toCostGame_cost, ← add_sum_erase (univ.erase u) _ (mem_erase.2 ⟨huv.symm, mem_univ v⟩),
      update_of_ne huv, update_self, update_self]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [update_of_ne (ne_of_mem_erase hk),
      update_of_ne (ne_of_mem_erase (mem_of_mem_erase hk))]
  rw [hterm b c, hterm a c, hterm a d, hterm b d]
  ring

/-- In a polymatrix game, Monderer and Shapley's four-cycle sum on players `i ≠ j` collapses to the
`2 × 2` cross-difference of `skewEdge P i j` (all third-player edges `k ∉ {i, j}` cancel). -/
theorem fourCycle_toCostGame_eq (P : PolymatrixGame ι S) {i j : ι} (hij : i ≠ j)
    (s : ∀ k, S k) (xᵢ yᵢ : S i) (xⱼ yⱼ : S j) :
    let A := update (update s i xᵢ) j xⱼ
    let B := update (update s i yᵢ) j xⱼ
    let C := update (update s i yᵢ) j yⱼ
    let D := update (update s i xᵢ) j yⱼ
    (P.toCostGame.cost i B - P.toCostGame.cost i A) +
        (P.toCostGame.cost j C - P.toCostGame.cost j B) +
        (P.toCostGame.cost i D - P.toCostGame.cost i C) +
        (P.toCostGame.cost j A - P.toCostGame.cost j D) =
      (P.skewEdge i j yᵢ xⱼ - P.skewEdge i j xᵢ xⱼ) +
        (P.skewEdge i j xᵢ yⱼ - P.skewEdge i j yᵢ yⱼ) := by
  dsimp only
  have hi_sum := P.rect_player_diff hij s xᵢ yᵢ xⱼ yⱼ
  have hj_sum := P.rect_player_diff hij.symm s xⱼ yⱼ yᵢ xᵢ
  rw [update_comm hij.symm yⱼ xᵢ s, update_comm hij.symm xⱼ xᵢ s,
    update_comm hij.symm xⱼ yᵢ s, update_comm hij.symm yⱼ yᵢ s] at hj_sum
  simp only [skewEdge]
  linarith

/-- **Exact-potential characterization of polymatrix games** (via [MondererShapley1996],
Corollary 2.9, p. 131): a polymatrix game with nonempty strategy sets admits an exact potential if
and only if every pair of distinct players satisfies cross-difference vanishing
(`IsPairwisePotential`). -/
theorem exists_isExactPotential_toCostGame_iff_isPairwisePotential [∀ k, Nonempty (S k)]
    {P : PolymatrixGame ι S} :
    (∃ Φ, P.toCostGame.IsExactPotential Φ) ↔ P.IsPairwisePotential := by
  rw [CostGame.exists_isExactPotential_iff_fourCycleZero]
  refine ⟨fun h i j hij xᵢ yᵢ xⱼ yⱼ => ?_, fun h i j hij s xᵢ yᵢ xⱼ yⱼ => ?_⟩
  · let s : ∀ k, S k := fun k => Classical.arbitrary (S k)
    simpa only [P.fourCycle_toCostGame_eq hij s xᵢ yᵢ xⱼ yⱼ] using h hij s xᵢ yᵢ xⱼ yⱼ
  · simpa only [P.fourCycle_toCostGame_eq hij s xᵢ yᵢ xⱼ yⱼ] using h hij xᵢ yᵢ xⱼ yⱼ

/-- **Separable skew-symmetry characterization of exact-potential polymatrix games**: a polymatrix
game with nonempty strategy sets admits an exact potential if and only if each skew-symmetric edge
difference `edgeCost i j a b - edgeCost j i b a` (`i ≠ j`) separates as `u i j a + v i j b`. -/
theorem exists_isExactPotential_toCostGame_iff_isSeparableSkew [∀ k, Nonempty (S k)]
    {P : PolymatrixGame ι S} :
    (∃ Φ, P.toCostGame.IsExactPotential Φ) ↔ P.IsSeparableSkew :=
  P.exists_isExactPotential_toCostGame_iff_isPairwisePotential.trans
    P.isPairwisePotential_iff_isSeparableSkew

/-- Under baseline zero normalization at a reference profile `z` (`edgeCost i j (z i) b = 0` and
`edgeCost i j a (z j) = 0` for all `i ≠ j`), a polymatrix game admits an exact potential if and only
if it is pairwise symmetric (`P.IsSymmetric`). -/
theorem isSymmetric_iff_exists_isExactPotential_of_zero_at_base {P : PolymatrixGame ι S}
    (z : ∀ k, S k)
    (hzero : ∀ ⦃i j : ι⦄, i ≠ j →
      (∀ b : S j, P.edgeCost i j (z i) b = 0) ∧ (∀ a : S i, P.edgeCost i j a (z j) = 0)) :
    P.IsSymmetric ↔ ∃ Φ, P.toCostGame.IsExactPotential Φ := by
  have : ∀ k, Nonempty (S k) := fun k => ⟨z k⟩
  refine ⟨fun h => ⟨P.edgePotential, h.isExactPotential_edgePotential⟩, fun h i j hij a b => ?_⟩
  have hrect :=
    (P.exists_isExactPotential_toCostGame_iff_isPairwisePotential.1 h) hij (z i) a (z j) b
  simp only [skewEdge, (hzero hij).1, (hzero hij).2, (hzero hij.symm).1, (hzero hij.symm).2,
    sub_self] at hrect
  linarith

end SymmetricAndPotential

end PolymatrixGame

end Cslib.GameTheory
