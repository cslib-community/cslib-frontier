/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Cooperative.Core
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Analysis.Brouwer.KKMS
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Real

/-!
# Nontransferable-utility cooperative games and Scarf's theorem

This module formalizes **nontransferable-utility (NTU) cooperative games**, **NTU cost-sharing
games**, and **Scarf's theorem** ([Scarf1967]; [Shapley1973]):
every balanced NTU game satisfying closedness, comprehensiveness, nonemptiness, and
individual-rational boundedness has a nonempty core.

An NTU value game (`NTUGame A`) assigns to each coalition `S : Finset A` a cylinder set
`feasible S : Set (A → ℝ)` of achievable utility vectors. An allocation `x : A → ℝ` lies in the
core (`NTUGame.InCore`) if `x ∈ G.feasible univ` and no nonempty coalition `S` has a vector
`y ∈ G.feasible S` strictly improving all of `S`'s payoffs (`∀ i ∈ S, x i < y i`), equivalently
`x ∉ interior (G.feasible S)` (`NTUGame.inCore_iff_notMem_interior`).

Following Shapley ([Shapley1973]), Scarf's theorem (`NTUGame.nonemptyCore_of_isBalanced`) is
proved by applying the KKMS theorem (`Cslib.Brouwer.exists_balanced_inter_of_kkmCover`) to the
closed simplex cover `F S = {q | payoff q ∈ G.feasible S}` induced by maximizing the diagonal
shift `t` along rays from `q ↦ v - M • q`. Dual cost-sharing NTU games (`NTUCostSharingGame A`)
correspond to `NTUGame A` via negation (`NTUCostSharingGame.toNTUGame`), yielding the cost-sharing
form of Scarf's theorem (`NTUCostSharingGame.nonemptyCore_of_isBalanced`), and transferable-utility
games ([JainMahdian2007], Section 15.2) embed directly (`CooperativeGame.toNTUGame`,
`CostSharingGame.toNTUCostSharingGame`) so that Scarf's theorem recovers the sufficiency half of
the Bondareva–Shapley theorem.

## Main definitions

* `Cslib.GameTheory.NTUGame`: utility-side nontransferable-utility cooperative game with closed,
  comprehensive, nonempty, cylindrical coalition sets.
* `Cslib.GameTheory.NTUGame.InCore`, `Cslib.GameTheory.NTUGame.NonemptyCore`: NTU core.
* `Cslib.GameTheory.NTUGame.IsBalanced`: balancedness of an NTU game with respect to
  `IsBalancedWeights`.
* `Cslib.GameTheory.NTUGame.individualValue`, `Cslib.GameTheory.NTUGame.IsBounded`: individual
  reservation payoffs and boundedness of individually rational coalitional payoffs.
* `Cslib.GameTheory.NTUCostSharingGame`, `Cslib.GameTheory.NTUCostSharingGame.InCore`,
  `Cslib.GameTheory.NTUCostSharingGame.NonemptyCore`,
  `Cslib.GameTheory.NTUCostSharingGame.IsBalanced`,
  `Cslib.GameTheory.NTUCostSharingGame.IsBounded`: dual cost-sharing NTU games.
* `Cslib.GameTheory.CooperativeGame.toNTUGame`,
  `Cslib.GameTheory.CostSharingGame.toNTUCostSharingGame`: embeddings of TU games into NTU games.

## Main results

* `Cslib.GameTheory.NTUGame.inCore_iff_notMem_interior`: blocking by strict coalitional
  improvement coincides with membership in `interior (G.feasible S)`.
* `Cslib.GameTheory.NTUGame.nonemptyCore_of_isBalanced`: **Scarf's theorem** ([Scarf1967],
  [Shapley1973]) — every balanced bounded NTU game has a nonempty core.
* `Cslib.GameTheory.NTUCostSharingGame.nonemptyCore_of_isBalanced`: cost-sharing form of **Scarf's
  theorem** ([Scarf1967]; [Shapley1973]).
* `Cslib.GameTheory.CooperativeGame.inCore_toNTUGame_iff`,
  `Cslib.GameTheory.CooperativeGame.toNTUGame_isBalanced_iff`,
  `Cslib.GameTheory.CostSharingGame.inCore_toNTUCostSharingGame_iff`,
  `Cslib.GameTheory.CostSharingGame.toNTUCostSharingGame_isBalanced_iff`: exact TU-to-NTU core and
  balancedness equivalences.

## References

* [JainMahdian2007]
* [Scarf1967]
* [Shapley1973]
-/

public section

namespace Cslib.GameTheory

open Finset Set

/-! ## Utility-side NTU cooperative games -/

/-- A **nontransferable-utility (NTU) cooperative game** on player type `A` assigns to each
coalition `S : Finset A` a set `feasible S : Set (A → ℝ)` of payoff vectors achievable by `S`.
For every nonempty coalition `S`, `feasible S` depends only on coordinates in `S` (`isCylinder`),
is closed (`isClosed`), comprehensive downwards (`isComprehensive`), and nonempty (`nonempty`)
([Scarf1967]; [Shapley1973]). -/
@[ext]
structure NTUGame (A : Type*) where
  /-- Payoff vectors achievable by coalition `S`. -/
  feasible : Finset A → Set (A → ℝ)
  /-- Membership in `feasible S` depends only on the payoffs of players in `S`. -/
  isCylinder : ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃x y : A → ℝ⦄,
    (∀ i ∈ S, x i = y i) → x ∈ feasible S → y ∈ feasible S
  /-- `feasible S` is closed in `A → ℝ` for every nonempty `S`. -/
  isClosed : ∀ ⦃S : Finset A⦄, S.Nonempty → IsClosed (feasible S)
  /-- Free disposal: any vector coordinatewise at most an achievable vector on `S` is achievable. -/
  isComprehensive : ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃x y : A → ℝ⦄,
    x ∈ feasible S → (∀ i ∈ S, y i ≤ x i) → y ∈ feasible S
  /-- Every nonempty coalition can achieve at least one payoff vector. -/
  nonempty : ∀ ⦃S : Finset A⦄, S.Nonempty → (feasible S).Nonempty

namespace NTUGame

section CoreAndBalance

variable {A : Type*}

/-- An allocation `x : A → ℝ` lies in the **core** of an NTU game `G` if `x ∈ G.feasible univ`
and no nonempty coalition `S` can strictly improve every member's payoff via a vector
`y ∈ G.feasible S`. -/
@[expose] def InCore [Fintype A] (G : NTUGame A) (x : A → ℝ) : Prop :=
  x ∈ G.feasible Finset.univ ∧
    ∀ S : Finset A, S.Nonempty → ¬ ∃ y ∈ G.feasible S, ∀ i ∈ S, x i < y i

/-- `G` has a **nonempty core** if some allocation belongs to `G.InCore`. -/
@[expose] def NonemptyCore [Fintype A] (G : NTUGame A) : Prop :=
  ∃ x : A → ℝ, G.InCore x

/-- Under `isCylinder` and `isComprehensive`, a payoff vector lies in `interior (G.feasible S)` iff
coalition `S` has a feasible vector strictly dominating `x` on `S`. -/
theorem mem_interior_iff_exists_lt [Finite A] (G : NTUGame A) {S : Finset A} (hS : S.Nonempty)
    (x : A → ℝ) :
    x ∈ interior (G.feasible S) ↔ ∃ y ∈ G.feasible S, ∀ i ∈ S, x i < y i := by
  classical
  have := Fintype.ofFinite A
  refine ⟨fun hx => ?_, fun ⟨y, hy, hlt⟩ => ?_⟩
  · obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    refine ⟨fun i => x i + ε / 2, interior_subset (hball ?_),
      fun _ _ => lt_add_of_pos_right _ (half_pos hεpos)⟩
    simp [Metric.mem_ball, dist_pi_lt_iff hεpos, Real.dist_eq, abs_of_pos (half_pos hεpos),
      half_lt_self hεpos]
  · let δ : ℝ := S.inf' hS fun i => y i - x i
    have hδ_pos : 0 < δ := (Finset.lt_inf'_iff hS).2 fun i hi => sub_pos.2 (hlt i hi)
    refine mem_interior.2 ⟨Metric.ball x δ, fun z hz => ?_, Metric.isOpen_ball,
      Metric.mem_ball_self hδ_pos⟩
    rw [Metric.mem_ball, dist_pi_lt_iff hδ_pos] at hz
    exact G.isComprehensive hS hy fun i hi => by
      linarith [(abs_lt.1 (Real.dist_eq (z i) (x i) ▸ hz i)).2,
        Finset.inf'_le (fun j => y j - x j) hi]

/-- Core characterization in terms of interiors: `x ∈ G.InCore` iff `x ∈ G.feasible univ` and
`x ∉ interior (G.feasible S)` for every nonempty coalition `S` ([Scarf1967]). -/
theorem inCore_iff_notMem_interior [Fintype A] (G : NTUGame A) (x : A → ℝ) :
    G.InCore x ↔
      x ∈ G.feasible Finset.univ ∧ ∀ S : Finset A, S.Nonempty → x ∉ interior (G.feasible S) :=
  and_congr Iff.rfl (forall₂_congr fun _ hS => (G.mem_interior_iff_exists_lt hS x).not.symm)

/-- An NTU game `G` is **balanced** if whenever a collection of nonempty coalitions weighted by a
balanced weight vector `w` (`IsBalancedWeights w`) all accept `x`, `x` is also feasible for the
grand coalition `univ`. -/
@[expose] def IsBalanced [Fintype A] [DecidableEq A] (G : NTUGame A) : Prop :=
  ∀ w : Finset A → ℝ, IsBalancedWeights w → ∀ x : A → ℝ,
    (∀ S : Finset A, S.Nonempty → 0 < w S → x ∈ G.feasible S) → x ∈ G.feasible Finset.univ

/-- The maximum standalone payoff `individualValue i` achievable by singleton `{i}` (meaningful
whenever `{x i | x ∈ G.feasible {i}}` is bounded above). -/
noncomputable def individualValue (G : NTUGame A) (i : A) : ℝ :=
  sSup ((fun x : A → ℝ => x i) '' G.feasible {i})

/-- Under singleton upper-boundedness, `{i}` achieves `x` iff `x i ≤ G.individualValue i`. -/
theorem mem_feasible_singleton_iff (G : NTUGame A) (i : A)
    (hbdd : BddAbove ((fun x : A → ℝ => x i) '' G.feasible {i})) (x : A → ℝ) :
    x ∈ G.feasible {i} ↔ x i ≤ G.individualValue i := by
  refine ⟨fun hx => le_csSup hbdd ⟨x, hx, rfl⟩, fun hx => ?_⟩
  let T : Set ℝ := (fun y : A → ℝ => y i) '' G.feasible {i}
  have hT_eq : T = {t : ℝ | Function.const A t ∈ G.feasible {i}} := Set.ext fun t =>
    ⟨fun ⟨y, hy, hyt⟩ => hyt ▸ G.isCylinder (singleton_nonempty i)
      (fun j hj => by rw [mem_singleton.1 hj]; rfl) hy,
     fun ht => ⟨Function.const A t, ht, rfl⟩⟩
  have hsup : G.individualValue i ∈ T :=
    IsClosed.csSup_mem (hT_eq ▸ (G.isClosed (singleton_nonempty i)).preimage
      (continuous_pi fun _ => continuous_id)) ((G.nonempty (singleton_nonempty i)).image _) hbdd
  exact G.isComprehensive (singleton_nonempty i) (hT_eq ▸ hsup) fun j hj => by
    rwa [mem_singleton.1 hj]

/-- Every core allocation gives each player at least `G.individualValue i`. -/
theorem InCore.individualValue_le [Fintype A] {G : NTUGame A} {x : A → ℝ} (hx : G.InCore x)
    (i : A) (hbdd : BddAbove ((fun y : A → ℝ => y i) '' G.feasible {i})) :
    G.individualValue i ≤ x i := by
  by_contra hlt
  exact hx.2 {i} (Finset.singleton_nonempty i) ⟨fun _ => G.individualValue i,
    (G.mem_feasible_singleton_iff i hbdd _).2 le_rfl,
    fun j hj => by simpa only [Finset.mem_singleton.1 hj] using not_le.1 hlt⟩

/-- Boundedness axiom for Scarf's theorem: each singleton's payoff is bounded above, and the
individually rational coalitional payoffs `{x ∈ G.feasible S | ∀ i ∈ S, individualValue i ≤ x i}`
are uniformly bounded above. -/
@[expose] def IsBounded (G : NTUGame A) : Prop :=
  (∀ i : A, BddAbove ((fun x : A → ℝ => x i) '' G.feasible {i})) ∧
    ∃ B : ℝ, ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃x : A → ℝ⦄,
      x ∈ G.feasible S → (∀ i ∈ S, G.individualValue i ≤ x i) → ∀ i ∈ S, x i ≤ B

end CoreAndBalance

section ScarfProof

open Cslib.Brouwer

private theorem scarf_payoff_lemma {A : Type*} [Fintype A] [Nonempty A] (G : NTUGame A)
    (v : A → ℝ) (hv : ∀ i, ∀ x : A → ℝ, x ∈ G.feasible {i} ↔ x i ≤ v i)
    (B : ℝ) (hB : ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃x : A → ℝ⦄,
      x ∈ G.feasible S → (∀ i ∈ S, v i ≤ x i) → ∀ i ∈ S, x i ≤ B) :
    ∃ M : ℝ, 0 < M ∧
      let base : (A → ℝ) → A → ℝ := fun q i => v i - M * q i
      let TSet : (A → ℝ) → Set ℝ := fun q =>
        {t : ℝ | ∃ S : Finset A, S.Nonempty ∧ (fun i => base q i + t) ∈ G.feasible S}
      (∀ q : A → ℝ, BddAbove (TSet q)) ∧
      (∀ q : A → ℝ, sSup (TSet q) ∈ TSet q) ∧
      Continuous (fun q => sSup (TSet q)) ∧
      (∀ q : A → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) → ∀ i, v i ≤ base q i + sSup (TSet q)) ∧
      (∀ q : A → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
        ∀ S : Finset A, S.Nonempty → (fun i => base q i + sSup (TSet q)) ∈ G.feasible S →
          ∀ j ∈ S, 0 < q j) := by
  classical
  let vmin : ℝ := Finset.univ.inf' Finset.univ_nonempty v
  have hvmin (i : A) : vmin ≤ v i := Finset.inf'_le v (Finset.mem_univ i)
  let M : ℝ := (Fintype.card A : ℝ) * max 1 (B - vmin + 1)
  have hcardA : (0 : ℝ) < Fintype.card A := Nat.cast_pos.2 Fintype.card_pos
  have hM_pos : 0 < M := mul_pos hcardA (lt_max_of_lt_left zero_lt_one)
  let base : (A → ℝ) → A → ℝ := fun q i => v i - M * q i
  let TSet : (A → ℝ) → Set ℝ := fun q =>
    {t : ℝ | ∃ S : Finset A, S.Nonempty ∧ (fun i => base q i + t) ∈ G.feasible S}
  have hsing_mem (q : A → ℝ) (i : A) : M * q i ∈ TSet q :=
    ⟨{i}, Finset.singleton_nonempty i, (hv i _).2 (by dsimp only [base]; linarith)⟩
  have hT_closed (q : A → ℝ) : IsClosed (TSet q) := by
    have hUnion : TSet q = ⋃ S : {S : Finset A // S.Nonempty},
        {t : ℝ | (fun i => base q i + t) ∈ G.feasible S.1} := Set.ext fun _ => by simp [TSet]
    exact hUnion ▸ isClosed_iUnion_of_finite fun S =>
      (G.isClosed S.2).preimage (continuous_pi fun _ => continuous_const.add continuous_id)
  have hT_bdd (q : A → ℝ) : BddAbove (TSet q) := by
    let qmax : ℝ := Finset.univ.sup' Finset.univ_nonempty q
    have hqmax (i : A) : M * q i ≤ M * qmax :=
      mul_le_mul_of_nonneg_left (Finset.le_sup' q (Finset.mem_univ i)) hM_pos.le
    refine ⟨max (M * qmax) (B - vmin + M * qmax), fun t ht => ?_⟩
    rcases le_or_gt t (M * qmax) with hle | hgt
    · exact hle.trans (le_max_left _ _)
    · obtain ⟨S, ⟨i₀, hi₀⟩, hS⟩ := ht
      have hiB := hB ⟨i₀, hi₀⟩ hS (fun i _ => by dsimp only [base]; linarith [hqmax i]) i₀ hi₀
      dsimp only [base] at hiB
      exact le_max_of_le_right (by linarith [hqmax i₀, hvmin i₀])
  have hsSup_mem (q : A → ℝ) : sSup (TSet q) ∈ TSet q :=
    (hT_closed q).csSup_mem ⟨_, hsing_mem q (Classical.arbitrary A)⟩ (hT_bdd q)
  have ht_lip (q₁ q₂ : A → ℝ) : |sSup (TSet q₁) - sSup (TSet q₂)| ≤ M * dist q₁ q₂ := by
    have hstep (p q : A → ℝ) : sSup (TSet q) - M * dist p q ≤ sSup (TSet p) := by
      obtain ⟨S, hSne, hS⟩ := hsSup_mem q
      refine le_csSup (hT_bdd p) ⟨S, hSne, G.isComprehensive hSne hS fun i _ => ?_⟩
      dsimp only [base]
      nlinarith [(abs_le.1 (Real.dist_eq (p i) (q i) ▸ dist_le_pi_dist p q i)).1]
    exact abs_le.2 ⟨by linarith [hstep q₁ q₂],
      by linarith [dist_comm q₂ q₁ ▸ hstep q₂ q₁]⟩
  have hcont : Continuous (fun q => sSup (TSet q)) :=
    Metric.continuous_iff.2 fun q ε hε => ⟨ε / M, div_pos hε hM_pos, fun q' hq' =>
      (Real.dist_eq _ _).trans_lt ((ht_lip q' q).trans_lt ((lt_div_iff₀' hM_pos).1 hq'))⟩
  have hv_le (q : A → ℝ) (_ : ∀ i, 0 ≤ q i) (_ : ∑ i, q i = 1) (i : A) :
      v i ≤ base q i + sSup (TSet q) := by
    linarith [le_csSup (hT_bdd q) (hsing_mem q i)]
  have hpos_of_mem (q : A → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
      (S : Finset A) (hSne : S.Nonempty) (hS : (fun i => base q i + sSup (TSet q)) ∈ G.feasible S)
      (j : A) (hjS : j ∈ S) : 0 < q j := by
    by_contra hj0
    obtain ⟨imax, -, himax⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
    have hsum_le : 1 ≤ (Fintype.card A : ℝ) * q imax := by
      simpa [hq1, nsmul_eq_mul] using
        Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => himax i (Finset.mem_univ i)
    have hdiv_le : max 1 (B - vmin + 1) ≤ sSup (TSet q) :=
      (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hsum_le).trans <|
        ((mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm).trans_le
          (le_csSup (hT_bdd q) (hsing_mem q imax))
    have hj_bound := hB hSne hS (fun i _ => hv_le q hq0 hq1 i) j hjS
    simp only [base, le_antisymm (not_lt.1 hj0) (hq0 j), mul_zero, sub_zero] at hj_bound
    linarith [hvmin j, le_max_right (1 : ℝ) (B - vmin + 1)]
  exact ⟨M, hM_pos, hT_bdd, hsSup_mem, hcont, hv_le, hpos_of_mem⟩

/-- **Scarf's theorem** ([Scarf1967]; [Shapley1973]): every balanced, bounded, closed,
comprehensive NTU cooperative game on a finite nonempty player set has a nonempty core. -/
theorem nonemptyCore_of_isBalanced {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (G : NTUGame A) (hbdd : G.IsBounded) (hbal : G.IsBalanced) : G.NonemptyCore := by
  classical
  obtain ⟨hsing, B, hB⟩ := hbdd
  obtain ⟨M, _, hT_bdd, hsSup_mem, hcont, _, hpos_of_mem⟩ :=
    scarf_payoff_lemma G G.individualValue
      (fun i x => G.mem_feasible_singleton_iff i (hsing i) x) B hB
  let base : (A → ℝ) → A → ℝ := fun q i => G.individualValue i - M * q i
  let TSet : (A → ℝ) → Set ℝ := fun q =>
    {t : ℝ | ∃ S : Finset A, S.Nonempty ∧ (fun i => base q i + t) ∈ G.feasible S}
  let payoff : (A → ℝ) → A → ℝ := fun q i => base q i + sSup (TSet q)
  obtain ⟨q, -, w, hw0, _, hw_bal, hqF⟩ :=
    exists_balanced_inter_of_kkmCover (fun S => {q | payoff q ∈ G.feasible S})
      (fun S hS => (G.isClosed hS).preimage <| continuous_pi fun i =>
        (continuous_const.sub (continuous_const.mul (continuous_apply i))).add hcont)
      fun T _ q hq0 hq1 hqout => by
        obtain ⟨S, hSne, hS⟩ := hsSup_mem q
        exact ⟨S, fun j hj => by_contra fun hjT =>
          (hpos_of_mem q hq0 hq1 S hSne hS j hj).ne' (hqout j hjT), hSne, hS⟩
  refine ⟨payoff q, hbal w ⟨hw0, hw_bal⟩ (payoff q) fun S _ hwS => hqF S hwS,
    fun S hSne ⟨y, hyS, hlt⟩ => ?_⟩
  have hε_pos : 0 < S.inf' hSne fun i => y i - payoff q i :=
    (Finset.lt_inf'_iff hSne).2 fun i hi => sub_pos.2 (hlt i hi)
  linarith [le_csSup (hT_bdd q) (a := sSup (TSet q) + S.inf' hSne fun i => y i - payoff q i)
    ⟨S, hSne, G.isComprehensive hSne hyS fun i hi => by
      dsimp only [payoff]
      linarith [Finset.inf'_le (fun j => y j - payoff q j) hi]⟩]

end ScarfProof

end NTUGame

/-! ## Dual cost-sharing NTU games -/

/-- A **nontransferable-utility (NTU) cost-sharing game** on agent type `A` assigns to each
coalition `S : Finset A` a set `feasible S : Set (A → ℝ)` of cost allocations that coalition `S`
can cover, satisfying cylinder dependence, closedness, upward comprehensiveness (higher cost vectors
are also coverable), and nonemptiness ([Scarf1967]; [Shapley1973]). -/
@[ext]
structure NTUCostSharingGame (A : Type*) where
  /-- Cost-allocation vectors coverable by coalition `S`. -/
  feasible : Finset A → Set (A → ℝ)
  /-- Membership in `feasible S` depends only on costs assigned to agents in `S`. -/
  isCylinder : ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃α β : A → ℝ⦄,
    (∀ i ∈ S, α i = β i) → α ∈ feasible S → β ∈ feasible S
  /-- `feasible S` is closed in `A → ℝ` for every nonempty `S`. -/
  isClosed : ∀ ⦃S : Finset A⦄, S.Nonempty → IsClosed (feasible S)
  /-- Upward comprehensiveness: if `S` can cover `α` and `α ≤ β` on `S`, `S` can cover `β`. -/
  isComprehensive : ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃α β : A → ℝ⦄,
    α ∈ feasible S → (∀ i ∈ S, α i ≤ β i) → β ∈ feasible S
  /-- Every nonempty coalition can cover at least one cost allocation. -/
  nonempty : ∀ ⦃S : Finset A⦄, S.Nonempty → (feasible S).Nonempty

namespace NTUCostSharingGame

variable {A : Type*}

/-- An allocation `α : A → ℝ` lies in the **core** of an NTU cost-sharing game `C` if
`α ∈ C.feasible univ` and no nonempty coalition `S` has an allocation `β ∈ C.feasible S` strictly
cheaper for every member of `S` (`∀ i ∈ S, β i < α i`). -/
@[expose] def InCore [Fintype A] (C : NTUCostSharingGame A) (α : A → ℝ) : Prop :=
  α ∈ C.feasible Finset.univ ∧
    ∀ S : Finset A, S.Nonempty → ¬ ∃ β ∈ C.feasible S, ∀ i ∈ S, β i < α i

/-- `C` has a **nonempty core** if some allocation belongs to `C.InCore`. -/
@[expose] def NonemptyCore [Fintype A] (C : NTUCostSharingGame A) : Prop :=
  ∃ α : A → ℝ, C.InCore α

/-- An NTU cost-sharing game `C` is **balanced** if whenever every nonempty coalition `S` with
positive balanced weight `w S > 0` covers `α`, the grand coalition `univ` also covers `α`. -/
@[expose] def IsBalanced [Fintype A] [DecidableEq A] (C : NTUCostSharingGame A) : Prop :=
  ∀ w : Finset A → ℝ, IsBalancedWeights w → ∀ α : A → ℝ,
    (∀ S : Finset A, S.Nonempty → 0 < w S → α ∈ C.feasible S) → α ∈ C.feasible Finset.univ

/-- The minimum standalone cost `individualCost i` coverable by singleton `{i}`. -/
noncomputable def individualCost (C : NTUCostSharingGame A) (i : A) : ℝ :=
  sInf ((fun α : A → ℝ => α i) '' C.feasible {i})

/-- Boundedness axiom for an NTU cost-sharing game: each singleton cost is bounded below, and the
coalitional cost allocations bounded above by `individualCost` on `S` are uniformly bounded
below. -/
@[expose] def IsBounded (C : NTUCostSharingGame A) : Prop :=
  (∀ i : A, BddBelow ((fun α : A → ℝ => α i) '' C.feasible {i})) ∧
    ∃ B : ℝ, ∀ ⦃S : Finset A⦄, S.Nonempty → ∀ ⦃α : A → ℝ⦄,
      α ∈ C.feasible S → (∀ i ∈ S, α i ≤ C.individualCost i) → ∀ i ∈ S, B ≤ α i

/-- Negating cost vectors turns an NTU cost-sharing game into a utility-side `NTUGame`. -/
def toNTUGame (C : NTUCostSharingGame A) : NTUGame A where
  feasible S := {x : A → ℝ | -x ∈ C.feasible S}
  isCylinder _ hS _ _ hxy hx := C.isCylinder hS (fun i hi => by simp [hxy i hi]) hx
  isClosed _ hS := (C.isClosed hS).preimage continuous_neg
  isComprehensive _ hS _ _ hx hle :=
    C.isComprehensive hS hx fun i hi => neg_le_neg (hle i hi)
  nonempty _ hS := by
    obtain ⟨α, hα⟩ := C.nonempty hS
    exact ⟨-α, by simpa only [Set.mem_ofPred_eq, neg_neg] using hα⟩

@[simp]
theorem mem_toNTUGame_feasible (C : NTUCostSharingGame A) (S : Finset A) (x : A → ℝ) :
    x ∈ C.toNTUGame.feasible S ↔ -x ∈ C.feasible S :=
  Iff.rfl

@[simp]
theorem inCore_toNTUGame_iff [Fintype A] (C : NTUCostSharingGame A) (α : A → ℝ) :
    C.toNTUGame.InCore (-α) ↔ C.InCore α := by
  simp only [NTUGame.InCore, InCore, mem_toNTUGame_feasible, neg_neg]
  exact and_congr Iff.rfl (forall₂_congr fun _ _ =>
    ⟨fun h ⟨β, hβS, hlt⟩ => h ⟨-β, by simpa using hβS, fun i hi => neg_lt_neg (hlt i hi)⟩,
     fun h ⟨y, hyS, hlt⟩ => h ⟨-y, hyS, fun i hi => neg_lt.1 (hlt i hi)⟩⟩)

theorem nonemptyCore_toNTUGame_iff [Fintype A] (C : NTUCostSharingGame A) :
    C.toNTUGame.NonemptyCore ↔ C.NonemptyCore :=
  ⟨fun ⟨x, hx⟩ => ⟨-x, (C.inCore_toNTUGame_iff (-x)).1 (by simpa only [neg_neg] using hx)⟩,
   fun ⟨α, hα⟩ => ⟨-α, (C.inCore_toNTUGame_iff α).2 hα⟩⟩

theorem isBalanced_toNTUGame_iff [Fintype A] [DecidableEq A] (C : NTUCostSharingGame A) :
    C.toNTUGame.IsBalanced ↔ C.IsBalanced :=
  ⟨fun hbal w hw α hα => by
     simpa only [mem_toNTUGame_feasible, neg_neg] using hbal w hw (-α) fun S hS hwS => by
       simpa only [mem_toNTUGame_feasible, neg_neg] using hα S hS hwS,
   fun hbal w hw x hx => hbal w hw (-x) hx⟩

section

open scoped Pointwise

private theorem image_neg_singleton_eq (C : NTUCostSharingGame A) (i : A) :
    ((fun x : A → ℝ => x i) '' C.toNTUGame.feasible {i}) =
      -((fun α : A → ℝ => α i) '' C.feasible {i}) := by
  ext t
  simp only [Set.mem_image, mem_toNTUGame_feasible, Set.mem_neg]
  exact ⟨fun ⟨x, hx, hxt⟩ => ⟨-x, hx, by simp [← hxt]⟩,
    fun ⟨α, hα, hαt⟩ => ⟨-α, by simpa only [neg_neg] using hα, by simp [hαt]⟩⟩

theorem individualValue_toNTUGame (C : NTUCostSharingGame A) (i : A) :
    C.toNTUGame.individualValue i = -C.individualCost i := by
  rw [NTUGame.individualValue, individualCost, C.image_neg_singleton_eq i, Real.sSup_neg]

theorem isBounded_toNTUGame_iff (C : NTUCostSharingGame A) :
    C.toNTUGame.IsBounded ↔ C.IsBounded := by
  refine and_congr (forall_congr' fun i => ?_)
    ⟨fun ⟨B, hB⟩ => ⟨-B, fun S hS α hα hir i hi => neg_le.1 ?_⟩,
      fun ⟨B, hB⟩ => ⟨-B, fun S hS x hx hir i hi => le_neg.1 ?_⟩⟩
  · rw [C.image_neg_singleton_eq i]
    exact ⟨fun ⟨b, hb⟩ => ⟨-b, fun _ ht => neg_le.1 (hb (Set.neg_mem_neg.2 ht))⟩,
      fun ⟨b, hb⟩ => ⟨-b, fun _ ht => le_neg.1 (hb (Set.mem_neg.1 ht))⟩⟩
  · exact hB hS (x := -α) (by simpa only [mem_toNTUGame_feasible, neg_neg] using hα)
      (fun j hj => by rw [C.individualValue_toNTUGame j]; exact neg_le_neg (hir j hj)) i hi
  · exact hB hS hx (fun j hj => neg_le.1 (C.individualValue_toNTUGame j ▸ hir j hj)) i hi

private theorem bddAbove_toNTUGame_singleton (C : NTUCostSharingGame A) (i : A)
    (hbdd : BddBelow ((fun α : A → ℝ => α i) '' C.feasible {i})) :
    BddAbove ((fun x : A → ℝ => x i) '' C.toNTUGame.feasible {i}) :=
  let ⟨b, hb⟩ := hbdd
  C.image_neg_singleton_eq i ▸ ⟨-b, fun _ ht => le_neg.1 (hb (Set.mem_neg.1 ht))⟩

/-- Under singleton lower-boundedness, `{i}` covers `α` iff `C.individualCost i ≤ α i`. -/
theorem mem_feasible_singleton_iff (C : NTUCostSharingGame A) (i : A)
    (hbdd : BddBelow ((fun α : A → ℝ => α i) '' C.feasible {i})) (α : A → ℝ) :
    α ∈ C.feasible {i} ↔ C.individualCost i ≤ α i := by
  simpa [mem_toNTUGame_feasible, Pi.neg_apply, C.individualValue_toNTUGame i] using
    C.toNTUGame.mem_feasible_singleton_iff i (C.bddAbove_toNTUGame_singleton i hbdd) (-α)

/-- Every core cost allocation charges each player at most `C.individualCost i`. -/
theorem InCore.le_individualCost [Fintype A] {C : NTUCostSharingGame A} {α : A → ℝ}
    (hα : C.InCore α) (i : A)
    (hbdd : BddBelow ((fun β : A → ℝ => β i) '' C.feasible {i})) :
    α i ≤ C.individualCost i := by
  simpa [Pi.neg_apply, C.individualValue_toNTUGame i] using
    ((C.inCore_toNTUGame_iff α).2 hα).individualValue_le i
      (C.bddAbove_toNTUGame_singleton i hbdd)

end

/-- **Scarf's theorem for NTU cost-sharing games** ([Scarf1967]; [Shapley1973]): every balanced,
bounded, closed, comprehensive NTU cost-sharing game on a finite nonempty agent set has a nonempty
core. -/
theorem nonemptyCore_of_isBalanced [Fintype A] [DecidableEq A] [Nonempty A]
    (C : NTUCostSharingGame A) (hbdd : C.IsBounded) (hbal : C.IsBalanced) : C.NonemptyCore :=
  C.nonemptyCore_toNTUGame_iff.1 <|
    C.toNTUGame.nonemptyCore_of_isBalanced (C.isBounded_toNTUGame_iff.2 hbdd)
      (C.isBalanced_toNTUGame_iff.2 hbal)

end NTUCostSharingGame

/-! ## Transferable-utility specializations and Bondareva–Shapley connection -/

namespace CooperativeGame

variable {A : Type*}

/-- Every TU cooperative value game induces a closed, comprehensive, cylindrical NTU game with
`feasible S = {x | ∑ i ∈ S, x i ≤ G.val S}`. -/
def toNTUGame (G : CooperativeGame A) : NTUGame A where
  feasible S := {x : A → ℝ | ∑ i ∈ S, x i ≤ G.val S}
  isCylinder _ _ _ _ hxy hx := by
    simpa only [Set.mem_ofPred_eq, ← Finset.sum_congr rfl hxy] using hx
  isClosed S _ :=
    isClosed_le (continuous_finsetSum S fun i _ => continuous_apply i) continuous_const
  isComprehensive _ _ _ _ hx hle :=
    (Finset.sum_le_sum fun i hi => hle i hi).trans hx
  nonempty S hS := by
    classical
    obtain ⟨i₀, hi₀⟩ := hS
    refine ⟨fun i => if i = i₀ then G.val S else 0, ?_⟩
    change ∑ i ∈ S, (if i = i₀ then G.val S else 0) ≤ G.val S
    simp [hi₀]

@[simp]
theorem mem_toNTUGame_feasible (G : CooperativeGame A) (S : Finset A) (x : A → ℝ) :
    x ∈ G.toNTUGame.feasible S ↔ ∑ i ∈ S, x i ≤ G.val S :=
  Iff.rfl

@[simp]
theorem inCore_toNTUGame_iff [Fintype A] (G : CooperativeGame A) (x : A → ℝ) :
    G.toNTUGame.InCore x ↔ G.InCore x := by
  classical
  refine ⟨fun ⟨hxU, hno⟩ => ?_, fun ⟨hbal, hS⟩ => ?_⟩
  · have hge (S : Finset A) : G.val S ≤ ∑ i ∈ S, x i := by
      rcases S.eq_empty_or_nonempty with rfl | hS
      · simp
      · by_contra hlt
        have hcard : (0 : ℝ) < S.card := Nat.cast_pos.2 (Finset.card_pos.2 hS)
        refine hno S hS ⟨fun i => x i + (G.val S - ∑ j ∈ S, x j) / S.card, ?_,
          fun _ _ => lt_add_of_pos_right _ (div_pos (sub_pos.2 (not_le.1 hlt)) hcard)⟩
        rw [mem_toNTUGame_feasible, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          mul_div_cancel₀ _ hcard.ne']
        linarith
    exact ⟨le_antisymm hxU (hge Finset.univ), hge⟩
  · exact ⟨hbal.le, fun S hSne ⟨y, hyS, hlt⟩ =>
      not_lt_of_ge (hyS.trans (hS S)) (sum_lt_sum_of_nonempty hSne hlt)⟩

theorem nonemptyCore_toNTUGame_iff [Fintype A] (G : CooperativeGame A) :
    G.toNTUGame.NonemptyCore ↔ G.NonemptyCore :=
  exists_congr (G.inCore_toNTUGame_iff)

theorem individualValue_toNTUGame (G : CooperativeGame A) (i : A) :
    G.toNTUGame.individualValue i = G.val {i} := by
  have himg : ((fun x : A → ℝ => x i) '' G.toNTUGame.feasible {i}) = Set.Iic (G.val {i}) :=
    Set.ext fun t => ⟨fun ⟨x, hx, hxt⟩ => hxt ▸ by simpa using hx,
      fun ht => ⟨fun _ => t, by simpa using ht, rfl⟩⟩
  rw [NTUGame.individualValue, himg, csSup_Iic]

theorem toNTUGame_isBounded [Finite A] [Nonempty A] (G : CooperativeGame A) :
    G.toNTUGame.IsBounded := by
  classical
  have := Fintype.ofFinite A
  refine ⟨fun i => ⟨G.val {i}, fun _ ⟨x, hx, hxt⟩ => hxt ▸ by simpa using hx⟩, ?_⟩
  let f : Finset A → ℝ := fun S => G.val S - ∑ j ∈ S, G.val {j}
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty f
  refine ⟨(Finset.univ.sup' Finset.univ_nonempty fun i : A => G.val {i}) + max M 0,
    fun S _ x hx hir i hi => ?_⟩
  have hsub := Finset.single_le_sum
    (fun j hj => sub_nonneg.2 (G.individualValue_toNTUGame j ▸ hir j hj)) hi
  rw [Finset.sum_sub_distrib] at hsub
  linarith [Finset.le_sup' f (Finset.mem_univ S), (mem_toNTUGame_feasible G S x).1 hx,
    Finset.le_sup' (fun k : A => G.val {k}) (Finset.mem_univ i), le_max_left M 0]

theorem toNTUGame_isBalanced_iff [Fintype A] [DecidableEq A] [Nonempty A] (G : CooperativeGame A) :
    G.toNTUGame.IsBalanced ↔
      ∀ w : Finset A → ℝ, IsBalancedWeights w →
        ∑ S : Finset A, w S * G.val S ≤ G.val Finset.univ := by
  refine ⟨fun hbal => G.nonemptyCore_iff_balanced.1 <| G.nonemptyCore_toNTUGame_iff.1 <|
    G.toNTUGame.nonemptyCore_of_isBalanced G.toNTUGame_isBounded hbal, fun hbal w hw x hx => ?_⟩
  rw [mem_toNTUGame_feasible, ← hw.sum_mul_sum_eq x]
  refine (Finset.sum_le_sum fun S _ => ?_).trans (hbal w hw)
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · rcases (hw.1 S).lt_or_eq with hwpos | hw0
    exacts [mul_le_mul_of_nonneg_left (hx S hS hwpos) (hw.1 S), by simp [← hw0]]

end CooperativeGame

namespace CostSharingGame

variable {A : Type*}

/-- Every TU cost-sharing game induces a closed, upward-comprehensive, cylindrical NTU
cost-sharing game with `feasible S = {α | G.cost S ≤ ∑ i ∈ S, α i}`. -/
def toNTUCostSharingGame (G : CostSharingGame A) : NTUCostSharingGame A where
  feasible S := {α : A → ℝ | G.cost S ≤ ∑ i ∈ S, α i}
  isCylinder _ _ _ _ hxy hx := by
    simpa only [Set.mem_ofPred_eq, ← Finset.sum_congr rfl hxy] using hx
  isClosed S _ :=
    isClosed_le continuous_const (continuous_finsetSum S fun i _ => continuous_apply i)
  isComprehensive _ _ _ _ hx hle :=
    hx.trans (Finset.sum_le_sum fun i hi => hle i hi)
  nonempty S hS := by
    classical
    obtain ⟨i₀, hi₀⟩ := hS
    refine ⟨fun i => if i = i₀ then G.cost S else 0, ?_⟩
    change G.cost S ≤ ∑ i ∈ S, (if i = i₀ then G.cost S else 0)
    simp [hi₀]

@[simp]
theorem mem_toNTUCostSharingGame_feasible (G : CostSharingGame A) (S : Finset A) (α : A → ℝ) :
    α ∈ G.toNTUCostSharingGame.feasible S ↔ G.cost S ≤ ∑ i ∈ S, α i :=
  Iff.rfl

theorem toNTUCostSharingGame_toNTUGame (G : CostSharingGame A) :
    G.toNTUCostSharingGame.toNTUGame = G.toCooperativeGame.toNTUGame := by
  ext S x
  simp only [NTUCostSharingGame.mem_toNTUGame_feasible, mem_toNTUCostSharingGame_feasible,
    CooperativeGame.mem_toNTUGame_feasible, toCooperativeGame_val, Pi.neg_apply,
    Finset.sum_neg_distrib, le_neg]

@[simp]
theorem inCore_toNTUCostSharingGame_iff [Fintype A] (G : CostSharingGame A) (α : A → ℝ) :
    G.toNTUCostSharingGame.InCore α ↔ G.InCore α := by
  rw [← G.toNTUCostSharingGame.inCore_toNTUGame_iff α, G.toNTUCostSharingGame_toNTUGame,
    G.toCooperativeGame.inCore_toNTUGame_iff (-α), inCore_toCooperativeGame_iff]

theorem nonemptyCore_toNTUCostSharingGame_iff [Fintype A] (G : CostSharingGame A) :
    G.toNTUCostSharingGame.NonemptyCore ↔ G.NonemptyCore :=
  exists_congr (G.inCore_toNTUCostSharingGame_iff)

theorem toNTUCostSharingGame_isBounded [Finite A] [Nonempty A] (G : CostSharingGame A) :
    G.toNTUCostSharingGame.IsBounded := by
  have := Fintype.ofFinite A
  simpa only [← G.toNTUCostSharingGame.isBounded_toNTUGame_iff, G.toNTUCostSharingGame_toNTUGame]
    using G.toCooperativeGame.toNTUGame_isBounded

theorem toNTUCostSharingGame_isBalanced_iff [Fintype A] [DecidableEq A] [Nonempty A]
    (G : CostSharingGame A) :
    G.toNTUCostSharingGame.IsBalanced ↔
      ∀ w : Finset A → ℝ, IsBalancedWeights w →
        G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S := by
  simp only [← G.toNTUCostSharingGame.isBalanced_toNTUGame_iff, G.toNTUCostSharingGame_toNTUGame,
    G.toCooperativeGame.toNTUGame_isBalanced_iff, toCooperativeGame_val, mul_neg,
    Finset.sum_neg_distrib, neg_le_neg_iff]

end CostSharingGame

end Cslib.GameTheory

