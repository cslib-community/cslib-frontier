/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.GameTheory.Cooperative.Basic
public import CslibFrontier.GameTheory.Mechanism.SingleParameter
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Logic.Relation
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cross-monotonic cost-sharing schemes, Moulin's mechanism, and submodular games

This module formalizes group-strategyproof cost-sharing mechanisms and primal-dual water-filling on
submodular cost-sharing games ([JainMahdian2007], Sections 15.3 and 15.4.1; Moulin 1999; Dutta and
Ray 1989):

1. **Cost-sharing schemes and cross-monotonicity** (`CostSharingScheme`, `IsBudgetBalanced`,
   `IsCrossMonotone`, [JainMahdian2007], Definitions 15.12 and 15.13) and **Proposition 15.14**
   (`CostSharingScheme.inApproxCore_univ`, `CostSharingScheme.inCore_univ`): every `γ`-budget-
   balanced cross-monotonic scheme induces an allocation in the `γ`-core on the grand coalition.
2. **Moulin's mechanism `moulinMechanism`** (Figure 15.2) and **Proposition 15.15**: synchronous
   iterative pruning `S_{k+1} = {i ∈ S_k | ξ(S_k, i) ≤ b_i}` reaches the unique largest willing
   coalition `S*` (`IsGreatest {S | ∀ i ∈ S, ξ(S, i) ≤ b_i}`); as a derived order-independence
   result (`moulinServiced_eq_of_validPruning`), any finite path of valid partial deletions
   terminating at a willing coalition reaches the same `S*`.
3. **Theorem 15.16 (Moulin 1999)**: if `ξ` is cross-monotone and `γ`-budget-balanced (with
   nonnegative shares for No Positive Transfers), `moulinMechanism ξ` is **group-strategyproof**
   (`moulinMechanism_isGroupStrategyproof`), `γ`-budget-balanced, and satisfies Voluntary
   Participation and Consumer Sovereignty.
4. **Submodular cost-sharing games and `SubmodularCostShare`** ([JainMahdian2007], Definition 15.17,
   Lemma 15.18, Corollary 15.19, Figure 15.3, and **Theorem 15.20**): tight-set uncrossing, the
   unique maximal tight set `maximalTightSet`, and the primal-dual water-filling scheme
   `submodularCostShareScheme`, proved `1`-budget-balanced, nonnegative, and cross-monotone (hence
   yielding a `1`-budget-balanced group-strategyproof Moulin mechanism).

## Main definitions

* `Cslib.GameTheory.CostSharingScheme`: cost-sharing scheme `ξ : Finset A → A → ℝ` with `0` outside
  the serviced coalition ([JainMahdian2007], Definition 15.12).
* `Cslib.GameTheory.CostSharingScheme.IsBudgetBalanced`,
  `Cslib.GameTheory.CostSharingScheme.IsCrossMonotone`,
  `Cslib.GameTheory.CostSharingScheme.IsNonneg`: budget balance and cross-monotonicity
  ([JainMahdian2007], Definitions 15.12 and 15.13).
* `Cslib.GameTheory.CostSharingMechanism`: binary-service cost-sharing mechanism `(serviced,
  payment)`, bridged to `Cslib.GameTheory.SingleParameter.Mechanism` via
  `CostSharingMechanism.toSingleParameterMechanism`.
* `Cslib.GameTheory.CostSharingMechanism.NoPositiveTransfers`,
  `Cslib.GameTheory.CostSharingMechanism.VoluntaryParticipation`,
  `Cslib.GameTheory.CostSharingMechanism.ConsumerSovereignty`,
  `Cslib.GameTheory.CostSharingMechanism.IsBudgetBalanced`,
  `Cslib.GameTheory.CostSharingMechanism.IsGroupStrategyproof`: mechanism axioms of
  [JainMahdian2007], Section 15.3.
* `Cslib.GameTheory.CostSharingScheme.moulinStep`,
  `Cslib.GameTheory.CostSharingScheme.moulinServiced`,
  `Cslib.GameTheory.CostSharingScheme.ValidPruningStep`,
  `Cslib.GameTheory.CostSharingScheme.moulinMechanism`: Moulin's iterative-pruning mechanism
  ([JainMahdian2007], Figure 15.2).
* `Cslib.GameTheory.CostSharingGame.IsSubmodular`,
  `Cslib.GameTheory.CostSharingGame.IsTight`,
  `Cslib.GameTheory.CostSharingGame.maximalTightSet`,
  `Cslib.GameTheory.CostSharingGame.submodularCostShareScheme`: submodular games and the Dutta–Ray /
  Jain–Vazirani primal-dual algorithm `SubmodularCostShare` ([JainMahdian2007], Section 15.4.1,
  Figure 15.3).

## Main results

* `Cslib.GameTheory.CostSharingScheme.inApproxCore_univ`,
  `Cslib.GameTheory.CostSharingScheme.inCore_univ`: **Proposition 15.14** of [JainMahdian2007].
* `Cslib.GameTheory.CostSharingScheme.isGreatest_isWilling_moulinServiced`,
  `Cslib.GameTheory.CostSharingScheme.moulinServiced_eq_of_validPruning`: **Proposition 15.15** of
  [JainMahdian2007] and derived order-independence of valid pruning paths.
* `Cslib.GameTheory.CostSharingScheme.moulinMechanism_isGroupStrategyproof`,
  `Cslib.GameTheory.CostSharingScheme.moulinMechanism_isBudgetBalanced`,
  `Cslib.GameTheory.CostSharingScheme.moulinMechanism_voluntaryParticipation`,
  `Cslib.GameTheory.CostSharingScheme.moulinMechanism_consumerSovereignty`,
  `Cslib.GameTheory.CostSharingScheme.moulinMechanism_noPositiveTransfers`: **Theorem 15.16** of
  [JainMahdian2007] (Moulin 1999).
* `Cslib.GameTheory.CostSharingGame.IsTight.union`,
  `Cslib.GameTheory.CostSharingGame.IsTight.inter`,
  `Cslib.GameTheory.CostSharingGame.isGreatest_maximalTightSet`: **Lemma 15.18** (with derived
  intersection companion `IsTight.inter`) and **Corollary 15.19** of [JainMahdian2007].
* `Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isCrossMonotone`,
  `Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isBudgetBalanced`,
  `Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isNonneg`: **Theorem 15.20** of
  [JainMahdian2007].

## References

* [JainMahdian2007]
-/

public section

namespace Cslib.GameTheory

/-! ## Cost-sharing schemes and cross-monotonicity -/

/-- A **cost-sharing scheme** ([JainMahdian2007], Definition 15.12) assigns to each finite serviced
coalition `S : Finset A` a cost-share vector `share S : A → ℝ` charging `0` to agents outside `S`.
-/
@[ext]
structure CostSharingScheme (A : Type*) where
  /-- Cost share `share S i` charged to agent `i` when `S` is the serviced coalition. -/
  share : Finset A → A → ℝ
  /-- Agents outside `S` pay `0`. -/
  share_eq_zero_of_not_mem : ∀ ⦃S : Finset A⦄ ⦃i : A⦄, i ∉ S → share S i = 0

namespace CostSharingScheme

variable {A : Type*}

/-- Every cost share is nonnegative. -/
@[expose] def IsNonneg (ξ : CostSharingScheme A) : Prop :=
  ∀ (S : Finset A) (i : A), 0 ≤ ξ.share S i

/-- A cost-sharing scheme `ξ` is **`γ`-budget-balanced** with respect to `G` ([JainMahdian2007],
Definition 15.12) if `γ * G.cost S ≤ ∑ i ∈ S, ξ.share S i ≤ G.cost S` for every coalition `S`. -/
@[expose] def IsBudgetBalanced (ξ : CostSharingScheme A) (G : CostSharingGame A) (γ : ℝ) : Prop :=
  ∀ S : Finset A, γ * G.cost S ≤ ∑ i ∈ S, ξ.share S i ∧ ∑ i ∈ S, ξ.share S i ≤ G.cost S

@[simp]
theorem isBudgetBalanced_one_iff (ξ : CostSharingScheme A) (G : CostSharingGame A) :
    ξ.IsBudgetBalanced G 1 ↔ ∀ S : Finset A, ∑ i ∈ S, ξ.share S i = G.cost S := by
  simp only [IsBudgetBalanced, one_mul]
  exact ⟨fun h S => le_antisymm (h S).2 (h S).1, fun h S => ⟨(h S).ge, (h S).le⟩⟩

/-- A cost-sharing scheme `ξ` is **cross-monotone** ([JainMahdian2007], Definition 15.13) if no
member's cost share increases as the serviced coalition grows:
`S ⊆ T → i ∈ S → ξ.share T i ≤ ξ.share S i`. -/
@[expose] def IsCrossMonotone (ξ : CostSharingScheme A) : Prop :=
  ∀ ⦃S T : Finset A⦄, S ⊆ T → ∀ ⦃i : A⦄, i ∈ S → ξ.share T i ≤ ξ.share S i

/-- Equivalence with the union formulation `ξ(i, S ∪ T) ≤ ξ(i, S)` of [JainMahdian2007],
Definition 15.13. -/
theorem isCrossMonotone_iff_union [DecidableEq A] (ξ : CostSharingScheme A) :
    ξ.IsCrossMonotone ↔ ∀ (S T : Finset A), ∀ i ∈ S, ξ.share (S ∪ T) i ≤ ξ.share S i := by
  refine ⟨fun h S T i hi => h Finset.subset_union_left hi, fun h S T hST i hi => ?_⟩
  have hU : S ∪ T = T := Finset.union_eq_right.2 hST
  exact hU ▸ h S T i hi

/-- **Proposition 15.14** ([JainMahdian2007], p. 393): if `ξ` is `γ`-budget-balanced for `G` and
cross-monotone, then `ξ.share Finset.univ` lies in the `γ`-core of `G`. -/
theorem inApproxCore_univ [Fintype A] {ξ : CostSharingScheme A} {G : CostSharingGame A} {γ : ℝ}
    (hbb : ξ.IsBudgetBalanced G γ) (hcm : ξ.IsCrossMonotone) :
    G.InApproxCore γ (ξ.share Finset.univ) := by
  refine ⟨hbb Finset.univ, fun S => ?_⟩
  calc
    ∑ i ∈ S, ξ.share Finset.univ i ≤ ∑ i ∈ S, ξ.share S i :=
      Finset.sum_le_sum fun i hi => hcm (Finset.subset_univ S) hi
    _ ≤ G.cost S := (hbb S).2

/-- Exact-budget-balance specialization of **Proposition 15.14** (`γ = 1`). -/
theorem inCore_univ [Fintype A] {ξ : CostSharingScheme A} {G : CostSharingGame A}
    (hbb : ξ.IsBudgetBalanced G 1) (hcm : ξ.IsCrossMonotone) :
    G.InCore (ξ.share Finset.univ) :=
  (G.inApproxCore_one_iff _).1 (ξ.inApproxCore_univ hbb hcm)

end CostSharingScheme

/-! ## Binary cost-sharing mechanisms and Moulin's mechanism -/

/-- A sealed-bid **cost-sharing mechanism** ([JainMahdian2007], Section 15.3, p. 392) elicits a bid
profile `b : A → ℝ` and selects a serviced coalition `serviced b : Finset A` together with payments
`payment b : A → ℝ`. -/
structure CostSharingMechanism (A : Type*) where
  /-- Set of agents receiving the service under bid profile `b`. -/
  serviced : (A → ℝ) → Finset A
  /-- Payment charged to each agent under bid profile `b`. -/
  payment : (A → ℝ) → A → ℝ

namespace CostSharingMechanism

variable {A : Type*}

/-- Embed a binary cost-sharing mechanism into `Cslib.GameTheory.SingleParameter.Mechanism` with
indicator allocation `1` on `serviced b` and `0` outside. -/
def toSingleParameterMechanism [DecidableEq A] (M : CostSharingMechanism A) :
    SingleParameter.Mechanism A where
  allocation b i := if i ∈ M.serviced b then 1 else 0
  payment := M.payment

@[simp]
theorem toSingleParameterMechanism_allocation [DecidableEq A] (M : CostSharingMechanism A)
    (b : A → ℝ) (i : A) :
    M.toSingleParameterMechanism.allocation b i = if i ∈ M.serviced b then 1 else 0 := by
  rfl

@[simp]
theorem toSingleParameterMechanism_payment [DecidableEq A] (M : CostSharingMechanism A)
    (b : A → ℝ) :
    M.toSingleParameterMechanism.payment b = M.payment b := by
  rfl

/-- Quasilinear utility `u_i q_i - p_i` of agent `i` with true value `u i` under bid profile `b`
([JainMahdian2007], Section 15.3, p. 391). -/
def utility [DecidableEq A] (M : CostSharingMechanism A) (u b : A → ℝ) (i : A) : ℝ :=
  (if i ∈ M.serviced b then u i else 0) - M.payment b i

theorem utility_eq [DecidableEq A] (M : CostSharingMechanism A) (u b : A → ℝ) (i : A) :
    M.utility u b i = (if i ∈ M.serviced b then u i else 0) - M.payment b i := by
  rfl

@[simp]
theorem toSingleParameterMechanism_utility [DecidableEq A] (M : CostSharingMechanism A)
    (u b : A → ℝ) (i : A) :
    M.toSingleParameterMechanism.utility i (u i) b = M.utility u b i := by
  simp only [SingleParameter.Mechanism.utility, toSingleParameterMechanism, utility, mul_ite,
    mul_one, mul_zero]

/-- **No Positive Transfers (NPT)** ([JainMahdian2007], p. 392): payments are always nonnegative. -/
@[expose] def NoPositiveTransfers (M : CostSharingMechanism A) : Prop :=
  ∀ (b : A → ℝ) (i : A), 0 ≤ M.payment b i

/-- **Voluntary Participation (VP)** ([JainMahdian2007], p. 392): unserviced agents pay `0`, and
serviced agents pay at most their bid. -/
@[expose] def VoluntaryParticipation (M : CostSharingMechanism A) : Prop :=
  (∀ (b : A → ℝ) (i : A), i ∉ M.serviced b → M.payment b i = 0) ∧
    ∀ (b : A → ℝ) (i : A), i ∈ M.serviced b → M.payment b i ≤ b i

/-- Voluntary Participation implies truthful individual rationality `0 ≤ M.utility u u i`. -/
theorem VoluntaryParticipation.utility_truthful_nonneg [DecidableEq A]
    {M : CostSharingMechanism A} (hvp : M.VoluntaryParticipation) (u : A → ℝ) (i : A) :
    0 ≤ M.utility u u i := by
  simp only [utility]
  by_cases hi : i ∈ M.serviced u
  · simp only [hi, ↓reduceIte, sub_nonneg]
    exact hvp.2 u i hi
  · simp only [hi, ↓reduceIte, hvp.1 u i hi, sub_self, le_rfl]

/-- **Consumer Sovereignty (CS)** ([JainMahdian2007], p. 392): every agent `i` has a bid `bStar`
guaranteeing service regardless of the other agents' bids. -/
@[expose] def ConsumerSovereignty [DecidableEq A] (M : CostSharingMechanism A) : Prop :=
  ∀ i : A, ∃ bStar : ℝ, ∀ b : A → ℝ, i ∈ M.serviced (Function.update b i bStar)

/-- **`γ`-Budget Balance** of a cost-sharing mechanism ([JainMahdian2007], p. 392): the total
payment collected from `serviced b` lies between `γ * G.cost (serviced b)` and
`G.cost (serviced b)`. -/
@[expose] def IsBudgetBalanced (M : CostSharingMechanism A) (G : CostSharingGame A) (γ : ℝ) :
    Prop :=
  ∀ b : A → ℝ,
    γ * G.cost (M.serviced b) ≤ ∑ i ∈ M.serviced b, M.payment b i ∧
      ∑ i ∈ M.serviced b, M.payment b i ≤ G.cost (M.serviced b)

/-- **Group-Strategyproofness (GSP)** ([JainMahdian2007], Section 15.3, p. 392): for every
coalition `C`, true valuation profile `u`, and joint misreport `C.piecewise z u`, if every member
of `C` is weakly better off (`utility u u i ≤ utility u (C.piecewise z u) i`), then every member
of `C` receives the exact same utility (`utility u (C.piecewise z u) i = utility u u i`). -/
@[expose] def IsGroupStrategyproof [DecidableEq A] (M : CostSharingMechanism A) : Prop :=
  ∀ (u z : A → ℝ) (C : Finset A),
    (∀ i ∈ C, M.utility u u i ≤ M.utility u (C.piecewise z u) i) →
      ∀ i ∈ C, M.utility u (C.piecewise z u) i = M.utility u u i

/-- Equivalent Pareto-deviation formulation of `IsGroupStrategyproof`: no coalition `C` can
misreport so that every member is weakly happier and at least one member is strictly happier
([JainMahdian2007], p. 392; cf. `Cslib.GameTheory.CostGame.IsStrongNash`). -/
theorem isGroupStrategyproof_iff_not_beneficial [DecidableEq A] (M : CostSharingMechanism A) :
    M.IsGroupStrategyproof ↔
      ∀ (u z : A → ℝ) (C : Finset A),
        ¬ ((∀ i ∈ C, M.utility u u i ≤ M.utility u (C.piecewise z u) i) ∧
          ∃ i ∈ C, M.utility u u i < M.utility u (C.piecewise z u) i) := by
  refine ⟨fun h u z C ⟨hle, i, hi, hlt⟩ => hlt.ne' (h u z C hle i hi), fun h u z C hle i hi => ?_⟩
  refine le_antisymm ?_ (hle i hi)
  by_contra hlt
  exact h u z C ⟨hle, i, hi, lt_of_not_ge hlt⟩

/-- Group-strategyproofness implies unilateral dominant-strategy truthfulness (`IsDSIC` on
`toSingleParameterMechanism`, and in fact over all real profiles). -/
theorem IsGroupStrategyproof.isDSIC [DecidableEq A] {M : CostSharingMechanism A}
    (hgsp : M.IsGroupStrategyproof) : M.toSingleParameterMechanism.IsDSIC := by
  intro i b v _ _
  let u : A → ℝ := Function.update b i v
  have hb : b = ({i} : Finset A).piecewise b u := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [Finset.piecewise]
    · simp [Finset.piecewise, u, hj]
  have hvi : v = u i := (Function.update_self i v b).symm
  change M.toSingleParameterMechanism.utility i v b ≤ M.toSingleParameterMechanism.utility i v u
  rw [hvi, toSingleParameterMechanism_utility, toSingleParameterMechanism_utility]
  by_contra hlt
  have hgt : M.utility u u i < M.utility u b i := lt_of_not_ge hlt
  rw [hb] at hgt
  have heq := hgsp u b {i} (fun j hj => by
    rw [Finset.mem_singleton.1 hj]
    exact hgt.le) i (Finset.mem_singleton_self i)
  exact hgt.ne' heq

end CostSharingMechanism

namespace CostSharingScheme

section Moulin

variable {A : Type*}

/-- Coalition `S` is **willing** at bid profile `b` if every member `i ∈ S` bids at least its cost
share `ξ.share S i` ([JainMahdian2007], Proposition 15.15). -/
@[expose] def IsWilling (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) : Prop :=
  ∀ i ∈ S, ξ.share S i ≤ b i

theorem isWilling_empty (ξ : CostSharingScheme A) (b : A → ℝ) : ξ.IsWilling b ∅ := by
  simp [IsWilling]

/-- If `ξ` is cross-monotone, willing coalitions are closed under binary union ([JainMahdian2007],
proof of Proposition 15.15, p. 393). -/
theorem IsWilling.union [DecidableEq A] {ξ : CostSharingScheme A} (hcm : ξ.IsCrossMonotone)
    {b : A → ℝ} {S₁ S₂ : Finset A} (h₁ : ξ.IsWilling b S₁) (h₂ : ξ.IsWilling b S₂) :
    ξ.IsWilling b (S₁ ∪ S₂) := by
  intro i hi
  rcases Finset.mem_union.1 hi with hi₁ | hi₂
  · exact (hcm Finset.subset_union_left hi₁).trans (h₁ i hi₁)
  · exact (hcm Finset.subset_union_right hi₂).trans (h₂ i hi₂)

/-- One synchronous pruning step `S ↦ {i ∈ S | ξ(i, S) ≤ b_i}` of Moulin's mechanism
([JainMahdian2007], Figure 15.2). -/
noncomputable def moulinStep (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) :
    Finset A :=
  S.filter (fun i => ξ.share S i ≤ b i)

@[simp]
theorem mem_moulinStep (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) (i : A) :
    i ∈ ξ.moulinStep b S ↔ i ∈ S ∧ ξ.share S i ≤ b i :=
  Finset.mem_filter

theorem moulinStep_subset (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) :
    ξ.moulinStep b S ⊆ S :=
  Finset.filter_subset _ S

theorem moulinStep_eq_self_iff (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) :
    ξ.moulinStep b S = S ↔ ξ.IsWilling b S := by
  simp only [moulinStep, Finset.filter_eq_self, IsWilling]

private theorem iterate_shrinking_fixed {f : Finset A → Finset A} (hf : ∀ S, f S ⊆ S) :
    ∀ (k : ℕ) (S : Finset A), S.card ≤ k → f (f^[k] S) = f^[k] S
  | 0, S, hcard => by
    have hS : S = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hcard)
    subst hS
    simp only [Function.iterate_zero, id_eq]
    exact Finset.subset_empty.1 (hf ∅)
  | k + 1, S, hcard => by
    by_cases heq : f S = S
    · have hiter : ∀ m, f^[m] S = S := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih, heq]
      rw [hiter (k + 1), heq]
    · have hssub : f S ⊂ S := ssubset_of_subset_of_ne (hf S) heq
      have hlt : (f S).card < S.card := Finset.card_lt_card hssub
      rw [Function.iterate_succ_apply]
      exact iterate_shrinking_fixed hf k (f S) (Nat.le_of_lt_succ (hlt.trans_le hcard))

/-- Serviced coalition returned by Moulin's mechanism `M_ξ` ([JainMahdian2007], Figure 15.2):
iteratively prune `{i ∈ S | ξ(i, S) ≤ b_i}` from `Finset.univ` until convergence (at most
`Fintype.card A` rounds). -/
noncomputable def moulinServiced [Fintype A] (ξ : CostSharingScheme A) (b : A → ℝ) :
    Finset A :=
  (ξ.moulinStep b)^[Fintype.card A] Finset.univ

theorem moulinStep_moulinServiced [Fintype A] (ξ : CostSharingScheme A) (b : A → ℝ) :
    ξ.moulinStep b (ξ.moulinServiced b) = ξ.moulinServiced b :=
  iterate_shrinking_fixed (ξ.moulinStep_subset b) (Fintype.card A) Finset.univ
    (by rw [Finset.card_univ])

theorem isWilling_moulinServiced [Fintype A] (ξ : CostSharingScheme A) (b : A → ℝ) :
    ξ.IsWilling b (ξ.moulinServiced b) :=
  (ξ.moulinStep_eq_self_iff b _).1 (ξ.moulinStep_moulinServiced b)

/-- A valid asynchronous/partial pruning step removes any subset of agents currently unwilling to
pay their share at `S`: `{i ∈ S | ξ(i, S) ≤ b_i} ⊆ S' ⊆ S`. -/
@[expose] def ValidPruningStep (ξ : CostSharingScheme A) (b : A → ℝ) (S S' : Finset A) : Prop :=
  ξ.moulinStep b S ⊆ S' ∧ S' ⊆ S

theorem validPruningStep_moulinStep (ξ : CostSharingScheme A) (b : A → ℝ) (S : Finset A) :
    ξ.ValidPruningStep b S (ξ.moulinStep b S) :=
  ⟨Finset.Subset.refl _, ξ.moulinStep_subset b S⟩

private theorem subset_of_isWilling_of_validPruning {ξ : CostSharingScheme A}
    (hcm : ξ.IsCrossMonotone) {b : A → ℝ} {W S S' : Finset A}
    (hW : ξ.IsWilling b W) (hWS : W ⊆ S) (hstep : ξ.ValidPruningStep b S S') :
    W ⊆ S' := by
  intro i hiW
  refine hstep.1 (Finset.mem_filter.2 ⟨hWS hiW, ?_⟩)
  exact (hcm hWS hiW).trans (hW i hiW)

private theorem subset_of_isWilling_reflTransGen {ξ : CostSharingScheme A}
    (hcm : ξ.IsCrossMonotone) {b : A → ℝ} {W S₀ Q : Finset A}
    (hW : ξ.IsWilling b W) (hWS₀ : W ⊆ S₀)
    (hpath : Relation.ReflTransGen (ξ.ValidPruningStep b) S₀ Q) :
    W ⊆ Q := by
  induction hpath with
  | refl => exact hWS₀
  | tail _ hstep ih => exact subset_of_isWilling_of_validPruning hcm hW ih hstep

/-- **Proposition 15.15** ([JainMahdian2007], p. 393): if `ξ` is cross-monotone, `moulinServiced ξ
b` is the unique largest coalition `S` satisfying `∀ i ∈ S, ξ.share S i ≤ b i`. -/
theorem isGreatest_isWilling_moulinServiced [Fintype A] {ξ : CostSharingScheme A}
    (hcm : ξ.IsCrossMonotone) (b : A → ℝ) :
    IsGreatest {S : Finset A | ξ.IsWilling b S} (ξ.moulinServiced b) := by
  refine ⟨ξ.isWilling_moulinServiced b, fun S hS => ?_⟩
  have hiter : ∀ k : ℕ, Relation.ReflTransGen (ξ.ValidPruningStep b) Finset.univ
      ((ξ.moulinStep b)^[k] Finset.univ) := by
    intro k
    induction k with
    | zero => exact .refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail (ξ.validPruningStep_moulinStep b _)
  exact subset_of_isWilling_reflTransGen hcm hS (Finset.subset_univ S) (hiter (Fintype.card A))

/-- Derived order-independence result for iterative pruning (extending [JainMahdian2007],
Proposition 15.15 and Figure 15.2, p. 393, which analyze synchronous rounds): for a cross-monotone
scheme `ξ`, any finite path of valid partial deletions (`ValidPruningStep`) from `Finset.univ` that
terminates at a willing coalition `Q` reaches `ξ.moulinServiced b`. -/
theorem moulinServiced_eq_of_validPruning [Fintype A] {ξ : CostSharingScheme A}
    (hcm : ξ.IsCrossMonotone) {b : A → ℝ} {Q : Finset A}
    (hpath : Relation.ReflTransGen (ξ.ValidPruningStep b) Finset.univ Q)
    (hQ : ξ.IsWilling b Q) :
    Q = ξ.moulinServiced b :=
  le_antisymm
    ((ξ.isGreatest_isWilling_moulinServiced hcm b).2 hQ)
    (subset_of_isWilling_reflTransGen hcm (ξ.isWilling_moulinServiced b)
      (Finset.subset_univ _) hpath)

theorem moulinServiced_mono [Fintype A] {ξ : CostSharingScheme A} (hcm : ξ.IsCrossMonotone)
    {b₁ b₂ : A → ℝ} (hb : b₁ ≤ b₂) :
    ξ.moulinServiced b₁ ⊆ ξ.moulinServiced b₂ :=
  (ξ.isGreatest_isWilling_moulinServiced hcm b₂).2 fun i hi =>
    (ξ.isWilling_moulinServiced b₁ i hi).trans (hb i)

/-- **Moulin's cost-sharing mechanism `M_ξ`** ([JainMahdian2007], Figure 15.2, p. 393): service
`moulinServiced ξ b` and charge each agent `ξ.share (moulinServiced ξ b) i`. -/
noncomputable def moulinMechanism [Fintype A] (ξ : CostSharingScheme A) :
    CostSharingMechanism A where
  serviced := ξ.moulinServiced
  payment b i := ξ.share (ξ.moulinServiced b) i

@[simp]
theorem moulinMechanism_serviced [Fintype A] (ξ : CostSharingScheme A) (b : A → ℝ) :
    ξ.moulinMechanism.serviced b = ξ.moulinServiced b := by
  rfl

@[simp]
theorem moulinMechanism_payment [Fintype A] (ξ : CostSharingScheme A) (b : A → ℝ) (i : A) :
    ξ.moulinMechanism.payment b i = ξ.share (ξ.moulinServiced b) i := by
  rfl

private theorem moulinMechanism_utility_of_mem [Fintype A] [DecidableEq A]
    (ξ : CostSharingScheme A) {u b : A → ℝ} {j : A} (hj : j ∈ ξ.moulinServiced b) :
    ξ.moulinMechanism.utility u b j = u j - ξ.share (ξ.moulinServiced b) j := by
  simp only [CostSharingMechanism.utility, moulinMechanism, hj, ↓reduceIte]

private theorem moulinMechanism_utility_of_notMem [Fintype A] [DecidableEq A]
    (ξ : CostSharingScheme A) {u b : A → ℝ} {j : A} (hj : j ∉ ξ.moulinServiced b) :
    ξ.moulinMechanism.utility u b j = 0 := by
  simp only [CostSharingMechanism.utility, moulinMechanism, hj, ↓reduceIte,
    ξ.share_eq_zero_of_not_mem hj, sub_self]

theorem moulinMechanism_voluntaryParticipation [Fintype A] (ξ : CostSharingScheme A) :
    ξ.moulinMechanism.VoluntaryParticipation :=
  ⟨fun _ _ hi => ξ.share_eq_zero_of_not_mem hi,
   fun b i hi => ξ.isWilling_moulinServiced b i hi⟩

theorem moulinMechanism_noPositiveTransfers [Fintype A] {ξ : CostSharingScheme A}
    (hnn : ξ.IsNonneg) : ξ.moulinMechanism.NoPositiveTransfers :=
  fun b i => hnn (ξ.moulinServiced b) i

theorem moulinMechanism_consumerSovereignty [Fintype A] [DecidableEq A]
    (ξ : CostSharingScheme A) : ξ.moulinMechanism.ConsumerSovereignty := by
  intro i
  let bStar : ℝ := (Finset.univ : Finset (Finset A)).sup' Finset.univ_nonempty
    (fun S => ξ.share S i)
  refine ⟨bStar, fun b => ?_⟩
  have hmem : ∀ k : ℕ,
      i ∈ (ξ.moulinStep (Function.update b i bStar))^[k] Finset.univ := by
    intro k
    induction k with
    | zero => exact Finset.mem_univ i
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine Finset.mem_filter.2 ⟨ih, ?_⟩
      rw [Function.update_self]
      exact Finset.le_sup' (fun S : Finset A => ξ.share S i) (Finset.mem_univ _)
  exact hmem (Fintype.card A)

/-- **Theorem 15.16 (budget-balance half)** ([JainMahdian2007], p. 394): if `ξ` is
`γ`-budget-balanced for `G`, then `ξ.moulinMechanism` is `γ`-budget-balanced for `G`. -/
theorem moulinMechanism_isBudgetBalanced [Fintype A] {ξ : CostSharingScheme A}
    {G : CostSharingGame A} {γ : ℝ} (hbb : ξ.IsBudgetBalanced G γ) :
    ξ.moulinMechanism.IsBudgetBalanced G γ :=
  fun b => hbb (ξ.moulinServiced b)

/-- **Theorem 15.16 (Moulin 1999 — group-strategyproofness)** ([JainMahdian2007], p. 394): if `ξ`
is cross-monotone, then `ξ.moulinMechanism` is group-strategyproof. -/
theorem moulinMechanism_isGroupStrategyproof [Fintype A] [DecidableEq A]
    {ξ : CostSharingScheme A} (hcm : ξ.IsCrossMonotone) :
    ξ.moulinMechanism.IsGroupStrategyproof := by
  intro u z C hle
  let b' := C.piecewise z u
  have hvp := ξ.moulinMechanism_voluntaryParticipation
  -- Lower all overbids simultaneously via `b'' j = min (b' j) (u j)`.
  let b'' : A → ℝ := fun j => min (b' j) (u j)
  have hQ'_willing_b'' : ξ.IsWilling b'' (ξ.moulinServiced b') := by
    intro j hj
    refine le_min (ξ.isWilling_moulinServiced b' j hj) ?_
    by_cases hjC : j ∈ C
    · have h0 : 0 ≤ ξ.moulinMechanism.utility u u j := hvp.utility_truthful_nonneg u j
      have hben : 0 ≤ ξ.moulinMechanism.utility u b' j := h0.trans (hle j hjC)
      rw [ξ.moulinMechanism_utility_of_mem hj] at hben
      linarith
    · have hb'j : b' j = u j := by simp [b', hjC]
      exact hb'j ▸ ξ.isWilling_moulinServiced b' j hj
  -- Since `b'' ≤ u`, `moulinServiced b'` is willing under `u`, hence `⊆ moulinServiced u`.
  have hQ'_willing_u : ξ.IsWilling u (ξ.moulinServiced b') :=
    fun j hj => (hQ'_willing_b'' j hj).trans (min_le_right _ _)
  have hQ'_sub_Q : ξ.moulinServiced b' ⊆ ξ.moulinServiced u :=
    (ξ.isGreatest_isWilling_moulinServiced hcm u).2 hQ'_willing_u
  -- Every member of `C` is at most as happy under `b'` as under truthful `u`.
  intro i hiC
  refine le_antisymm ?_ (hle i hiC)
  by_cases hiQ' : i ∈ ξ.moulinServiced b'
  · have hiQ : i ∈ ξ.moulinServiced u := hQ'_sub_Q hiQ'
    have hshare : ξ.share (ξ.moulinServiced u) i ≤ ξ.share (ξ.moulinServiced b') i :=
      hcm hQ'_sub_Q hiQ'
    rw [ξ.moulinMechanism_utility_of_mem hiQ', ξ.moulinMechanism_utility_of_mem hiQ]
    linarith
  · rw [ξ.moulinMechanism_utility_of_notMem hiQ']
    exact hvp.utility_truthful_nonneg u i

end Moulin

end CostSharingScheme

/-! ## Submodular cost-sharing games and `SubmodularCostShare` (§15.4.1) -/

namespace CostSharingGame

section Submodular

variable {A : Type*} [DecidableEq A]

/-- A cost-sharing game `(A, c)` is **submodular** ([JainMahdian2007], Definition 15.17) if
`c(S ∪ T) + c(S ∩ T) ≤ c(S) + c(T)` for all `S, T`, reusing
`Cslib.Algorithms.Lean.Submodular.IsSubmodular`. -/
abbrev IsSubmodular (G : CostSharingGame A) : Prop :=
  Cslib.Algorithms.Lean.Submodular.IsSubmodular G.cost

/-- Every submodular cost-sharing game is disjointly subadditive (`c(∅) = 0`). -/
theorem IsSubmodular.isSubadditive {G : CostSharingGame A} (hsub : G.IsSubmodular) :
    G.IsSubadditive := by
  intro S₁ S₂ hdisj
  have h := hsub S₁ S₂
  rwa [Finset.disjoint_iff_inter_eq_empty.1 hdisj, G.cost_empty, add_zero] at h

/-- A coalition `S` is **tight** with respect to `α` ([JainMahdian2007], Section 15.4.1, p. 396)
if `∑ j ∈ S, α j = G.cost S`. -/
@[expose] def IsTight (G : CostSharingGame A) (α : A → ℝ) (S : Finset A) : Prop :=
  ∑ j ∈ S, α j = G.cost S

omit [DecidableEq A] in
@[simp]
theorem isTight_empty (G : CostSharingGame A) (α : A → ℝ) : G.IsTight α ∅ := by
  simp [IsTight]

/-- Uncrossing step for **Lemma 15.18** ([JainMahdian2007], p. 396) and its derived intersection
companion: in a submodular game, if `α` is core-feasible on `T` and `S₁, S₂ ⊆ T` are tight, then
both `S₁ ∪ S₂` and `S₁ ∩ S₂` are tight. -/
private theorem isTight_union_and_inter {G : CostSharingGame A} {T S₁ S₂ : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α)
    (hS₁ : S₁ ⊆ T) (hS₂ : S₂ ⊆ T)
    (ht₁ : G.IsTight α S₁) (ht₂ : G.IsTight α S₂) :
    G.IsTight α (S₁ ∪ S₂) ∧ G.IsTight α (S₁ ∩ S₂) := by
  have hU_le : ∑ j ∈ S₁ ∪ S₂, α j ≤ G.cost (S₁ ∪ S₂) := hfeas (Finset.union_subset hS₁ hS₂)
  have hI_le : ∑ j ∈ S₁ ∩ S₂, α j ≤ G.cost (S₁ ∩ S₂) :=
    hfeas (Finset.inter_subset_left.trans hS₁)
  have hsum : (∑ j ∈ S₁ ∪ S₂, α j) + ∑ j ∈ S₁ ∩ S₂, α j =
      (∑ j ∈ S₁, α j) + ∑ j ∈ S₂, α j := Finset.sum_union_inter
  have hmod : G.cost (S₁ ∪ S₂) + G.cost (S₁ ∩ S₂) ≤ G.cost S₁ + G.cost S₂ := hsub S₁ S₂
  simp only [IsTight] at ht₁ ht₂ ⊢
  exact ⟨by linarith, by linarith⟩

/-- **Lemma 15.18** ([JainMahdian2007], p. 396): in a submodular game, if `α` is core-feasible on
`T` and `S₁, S₂ ⊆ T` are tight, then `S₁ ∪ S₂` is also tight. -/
theorem IsTight.union {G : CostSharingGame A} {T S₁ S₂ : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α)
    (hS₁ : S₁ ⊆ T) (hS₂ : S₂ ⊆ T)
    (ht₁ : G.IsTight α S₁) (ht₂ : G.IsTight α S₂) :
    G.IsTight α (S₁ ∪ S₂) :=
  (isTight_union_and_inter hsub hfeas hS₁ hS₂ ht₁ ht₂).1

/-- Derived companion to **Lemma 15.18** ([JainMahdian2007], p. 396): under the same hypotheses,
`S₁ ∩ S₂` is also tight. -/
theorem IsTight.inter {G : CostSharingGame A} {T S₁ S₂ : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α)
    (hS₁ : S₁ ⊆ T) (hS₂ : S₂ ⊆ T)
    (ht₁ : G.IsTight α S₁) (ht₂ : G.IsTight α S₂) :
    G.IsTight α (S₁ ∩ S₂) :=
  (isTight_union_and_inter hsub hfeas hS₁ hS₂ ht₁ ht₂).2

/-- Union of all tight subsets of `T` ([JainMahdian2007], Corollary 15.19). -/
noncomputable def maximalTightSet (G : CostSharingGame A) (T : Finset A) (α : A → ℝ) :
    Finset A :=
  haveI : DecidablePred (G.IsTight α) := Classical.decPred _
  (T.powerset.filter (G.IsTight α)).biUnion id

theorem maximalTightSet_subset (G : CostSharingGame A) (T : Finset A) (α : A → ℝ) :
    G.maximalTightSet T α ⊆ T := by
  classical
  simp only [maximalTightSet]
  refine Finset.biUnion_subset.2 fun S hS => ?_
  exact Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1

/-- **Corollary 15.19** ([JainMahdian2007], p. 396): for a submodular game and core-feasible `α` on
`T`, `maximalTightSet G T α` is itself tight and contains every tight subset of `T`. -/
theorem isGreatest_maximalTightSet {G : CostSharingGame A} {T : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α) :
    IsGreatest {S : Finset A | S ⊆ T ∧ G.IsTight α S} (G.maximalTightSet T α) := by
  classical
  let P := T.powerset.filter (G.IsTight α)
  have hbiUnion : ∀ Q : Finset (Finset A), Q ⊆ P →
      Q.biUnion id ⊆ T ∧ G.IsTight α (Q.biUnion id) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Finset.empty_subset T, G.isTight_empty α⟩
    | insert S Q hSQ ih =>
      intro hQP
      have hS_mem : S ∈ P := hQP (Finset.mem_insert_self S Q)
      have hS_sub : S ⊆ T := Finset.mem_powerset.1 (Finset.mem_filter.1 hS_mem).1
      have hS_tight : G.IsTight α S := (Finset.mem_filter.1 hS_mem).2
      obtain ⟨hQ_sub, hQ_tight⟩ := ih ((Finset.subset_insert S Q).trans hQP)
      rw [Finset.biUnion_insert, id_eq]
      exact ⟨Finset.union_subset hS_sub hQ_sub,
        hS_tight.union hsub hfeas hS_sub hQ_sub hQ_tight⟩
  have hmain : P.biUnion id = G.maximalTightSet T α := by
    simp only [P, maximalTightSet]
  refine ⟨hmain ▸ hbiUnion P (Finset.Subset.refl P), fun S ⟨hST, hSt⟩ => ?_⟩
  rw [← hmain]
  exact Finset.subset_biUnion_of_mem id (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hST, hSt⟩)

theorem isTight_maximalTightSet {G : CostSharingGame A} {T : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α) :
    G.IsTight α (G.maximalTightSet T α) :=
  (G.isGreatest_maximalTightSet hsub hfeas).1.2

theorem subset_maximalTightSet_of_isTight {G : CostSharingGame A} {T S : Finset A} {α : A → ℝ}
    (hsub : G.IsSubmodular) (hfeas : G.IsCoreFeasibleOn T α)
    (hST : S ⊆ T) (ht : G.IsTight α S) :
    S ⊆ G.maximalTightSet T α :=
  (G.isGreatest_maximalTightSet hsub hfeas).2 ⟨hST, ht⟩

private theorem nonempty_attach_activeSubsets {T F : Finset A} (hne : (T \ F).Nonempty) :
    ((T.powerset.filter (fun S => (S \ F).Nonempty)).attach).Nonempty := by
  have hmem : T ∈ T.powerset.filter (fun S => (S \ F).Nonempty) :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.Subset.refl T), hne⟩
  exact ⟨⟨T, hmem⟩, Finset.mem_attach _ _⟩

/-- Minimum rate increment `δ` until a subset `S ⊆ T` with `(S \ F).Nonempty` goes tight when
increasing `α` uniformly on `T \ F`. -/
private noncomputable def nextFreezeDelta (G : CostSharingGame A) (T F : Finset A)
    (hne : (T \ F).Nonempty) (α : A → ℝ) : ℝ :=
  ((T.powerset.filter (fun S => (S \ F).Nonempty)).attach).inf'
    (nonempty_attach_activeSubsets hne)
    (fun x => (G.cost x.1 - ∑ j ∈ x.1, α j) / ((x.1 \ F).card : ℝ))

private theorem nextFreezeDelta_le (G : CostSharingGame A) {T F S : Finset A}
    (hne : (T \ F).Nonempty) (α : A → ℝ) (hST : S ⊆ T) (hSF : (S \ F).Nonempty) :
    G.nextFreezeDelta T F hne α ≤ (G.cost S - ∑ j ∈ S, α j) / ((S \ F).card : ℝ) := by
  have hmem : S ∈ T.powerset.filter (fun S => (S \ F).Nonempty) :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hST, hSF⟩
  exact Finset.inf'_le
    (fun x : {S // S ∈ T.powerset.filter (fun S => (S \ F).Nonempty)} =>
      (G.cost x.1 - ∑ j ∈ x.1, α j) / ((x.1 \ F).card : ℝ))
    (Finset.mem_attach _ ⟨S, hmem⟩)

private theorem mul_nextFreezeDelta_le (G : CostSharingGame A) {T F S : Finset A}
    (hne : (T \ F).Nonempty) (α : A → ℝ) (hST : S ⊆ T) (hSF : (S \ F).Nonempty) :
    ((S \ F).card : ℝ) * G.nextFreezeDelta T F hne α ≤ G.cost S - ∑ j ∈ S, α j := by
  have hcard_pos : (0 : ℝ) < (S \ F).card := by exact_mod_cast Finset.card_pos.2 hSF
  have hle := G.nextFreezeDelta_le hne α hST hSF
  have hmul := (le_div_iff₀ hcard_pos).1 hle
  linarith

/-- Fuel-bounded primal-dual water-filling loop for `SubmodularCostShare` ([JainMahdian2007],
Figure 15.3). Since `maximalTightSet` grows strictly at each step, `T.card` iterations suffice. -/
private noncomputable def submodularCostShareLoop (G : CostSharingGame A) (T : Finset A) :
    ℕ → (A → ℝ) → A → ℝ
  | 0, α => α
  | fuel + 1, α =>
    let F := G.maximalTightSet T α
    if hne : (T \ F).Nonempty then
      let δ := G.nextFreezeDelta T F hne α
      submodularCostShareLoop G T fuel (fun j => if j ∈ T \ F then α j + δ else α j)
    else α

private theorem submodularCostShareLoop_of_notMem (G : CostSharingGame A) (T : Finset A) :
    ∀ (fuel : ℕ) (α : A → ℝ) (j : A), j ∉ T →
      G.submodularCostShareLoop T fuel α j = α j
  | 0, _, _, _ => rfl
  | fuel + 1, α, j, hj => by
    dsimp only [submodularCostShareLoop]
    split_ifs with hne
    · rw [submodularCostShareLoop_of_notMem G T fuel _ j hj]
      have hj' : j ∉ T \ G.maximalTightSet T α := fun h => hj (Finset.mem_sdiff.1 h).1
      simp only [hj', ↓reduceIte]
    · rfl

/-- **Algorithm `SubmodularCostShare`** ([JainMahdian2007], Figure 15.3, pp. 396–397; Dutta and
Ray 1989; Jain and Vazirani 2002): starting from `α = 0`, raise all unfrozen shares `j ∈ T \ F` at
the same unit rate until a new coalition goes tight, freeze the new maximal tight set, and repeat
until `F = T`. -/
private noncomputable def submodularCostShare (G : CostSharingGame A) (T : Finset A) : A → ℝ :=
  G.submodularCostShareLoop T T.card (fun _ => 0)

private structure WaterFillingState (G : CostSharingGame A) (T : Finset A) (α : A → ℝ)
    (t₀ : ℝ) : Prop where
  t₀_nonneg : 0 ≤ t₀
  feasible : G.IsCoreFeasibleOn T α
  zero_outside : ∀ j ∉ T, α j = 0
  nonneg : ∀ j, 0 ≤ α j
  eq_t₀_unfrozen : ∀ j ∈ T \ G.maximalTightSet T α, α j = t₀
  le_t₀_frozen : ∀ j ∈ G.maximalTightSet T α, α j ≤ t₀
  history : ∀ t : ℝ, 0 ≤ t → t < t₀ →
    G.IsCoreFeasibleOn T (fun j => min (α j) t) ∧
      T.filter (fun j => α j ≤ t) = G.maximalTightSet T (fun j => min (α j) t)

private theorem sum_shift_on_sdiff {T F S : Finset A} (hST : S ⊆ T) (α : A → ℝ) (δ : ℝ) :
    (∑ j ∈ S, if j ∈ T \ F then α j + δ else α j) =
      (∑ j ∈ S, α j) + ((S \ F).card : ℝ) * δ := by
  have hcongr : (∑ j ∈ S, if j ∈ T \ F then α j + δ else α j) =
      ∑ j ∈ S, (α j + if j ∈ S \ F then δ else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmem : (j ∈ T \ F) ↔ (j ∈ S \ F) := by
      simp only [Finset.mem_sdiff, hj, hST hj, true_and]
    by_cases h : j ∈ S \ F
    · simp only [hmem.2 h, h, ↓reduceIte]
    · simp only [mt hmem.1 h, h, ↓reduceIte, add_zero]
  rw [hcongr, Finset.sum_add_distrib, ← Finset.sum_filter]
  have hfilt : S.filter (fun j => j ∈ S \ F) = S \ F := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, and_self_left]
  rw [hfilt, Finset.sum_const, nsmul_eq_mul]

private theorem waterFilling_step_history {G : CostSharingGame A} {T : Finset A} {α : A → ℝ}
    {t₀ : ℝ} (hsub : G.IsSubmodular) (st : WaterFillingState G T α t₀)
    (hne : (T \ G.maximalTightSet T α).Nonempty)
    {t : ℝ} (ht0 : 0 ≤ t)
    (htt : t < t₀ + G.nextFreezeDelta T (G.maximalTightSet T α) hne α) :
    let F := G.maximalTightSet T α
    let δ := G.nextFreezeDelta T F hne α
    let α' : A → ℝ := fun j => if j ∈ T \ F then α j + δ else α j
    G.IsCoreFeasibleOn T (fun j => min (α' j) t) ∧
      T.filter (fun j => α' j ≤ t) = G.maximalTightSet T (fun j => min (α' j) t) := by
  intro F δ α'
  have hF_sub_T : F ⊆ T := G.maximalTightSet_subset T α
  have htt' : t ≤ t₀ + δ := htt.le
  rcases lt_or_ge t t₀ with htt₀ | ht₀t
  · -- Earlier times `t < t₀`: truncation at `t` agrees identically with `α`.
    have hmin_eq : (fun j => min (α' j) t) = (fun j => min (α j) t) := by
      ext j
      by_cases hjTF : j ∈ T \ F
      · have hαj : α j = t₀ := st.eq_t₀_unfrozen j hjTF
        simp only [α', hjTF, ↓reduceIte, hαj, min_eq_right htt₀.le, min_eq_right htt']
      · simp only [α', hjTF, ↓reduceIte]
    have hfilt_eq : T.filter (fun j => α' j ≤ t) = T.filter (fun j => α j ≤ t) := by
      ext j
      simp only [Finset.mem_filter]
      refine and_congr_right fun hjT => ?_
      by_cases hjF : j ∈ F
      · have hjTF : j ∉ T \ F := fun h => (Finset.mem_sdiff.1 h).2 hjF
        simp only [α', hjTF, ↓reduceIte]
      · have hjTF : j ∈ T \ F := Finset.mem_sdiff.2 ⟨hjT, hjF⟩
        simp only [α', hjTF, ↓reduceIte, st.eq_t₀_unfrozen j hjTF]
        exact ⟨fun h => absurd h (not_le.2 htt), fun h => absurd h (not_le.2 htt₀)⟩
    rw [hmin_eq, hfilt_eq]
    exact st.history t ht0 htt₀
  · -- Current interval `t₀ ≤ t < t₀ + δ`: `min (α' ·) t` shifts `T \ F` by `t - t₀ < δ`.
    have hmin_shift : ∀ j ∈ T,
        min (α' j) t = if j ∈ T \ F then α j + (t - t₀) else α j := by
      intro j hjT
      by_cases hjF : j ∈ F
      · have hjTF : j ∉ T \ F := fun h => (Finset.mem_sdiff.1 h).2 hjF
        have hle : α j ≤ t := (st.le_t₀_frozen j hjF).trans ht₀t
        simp only [α', hjTF, ↓reduceIte, min_eq_left hle]
      · have hjTF : j ∈ T \ F := Finset.mem_sdiff.2 ⟨hjT, hjF⟩
        have hαj : α j = t₀ := st.eq_t₀_unfrozen j hjTF
        simp only [α', hjTF, ↓reduceIte, hαj, min_eq_right htt']
        ring
    have hsum_t : ∀ ⦃S : Finset A⦄, S ⊆ T →
        (∑ j ∈ S, min (α' j) t) = (∑ j ∈ S, α j) + ((S \ F).card : ℝ) * (t - t₀) := by
      intro S hST
      calc
        (∑ j ∈ S, min (α' j) t) =
            ∑ j ∈ S, if j ∈ T \ F then α j + (t - t₀) else α j :=
          Finset.sum_congr rfl fun j hj => hmin_shift j (hST hj)
        _ = (∑ j ∈ S, α j) + ((S \ F).card : ℝ) * (t - t₀) :=
          sum_shift_on_sdiff hST α (t - t₀)
    have hfeas_t : G.IsCoreFeasibleOn T (fun j => min (α' j) t) := by
      intro S hST
      rw [hsum_t hST]
      by_cases hSF : (S \ F).Nonempty
      · have hmul := G.mul_nextFreezeDelta_le hne α hST hSF
        have hcard_pos : (0 : ℝ) < (S \ F).card := by exact_mod_cast Finset.card_pos.2 hSF
        have hlt_mul : ((S \ F).card : ℝ) * (t - t₀) < ((S \ F).card : ℝ) * δ :=
          mul_lt_mul_of_pos_left (by linarith) hcard_pos
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.1 hSF, Finset.card_empty, Nat.cast_zero, zero_mul,
          add_zero]
        exact st.feasible hST
    have hfilt_F : T.filter (fun j => α' j ≤ t) = F := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hjT, hle⟩
        by_contra hjF
        have hjTF : j ∈ T \ F := Finset.mem_sdiff.2 ⟨hjT, hjF⟩
        simp only [α', hjTF, ↓reduceIte, st.eq_t₀_unfrozen j hjTF] at hle
        linarith
      · intro hjF
        have hjT : j ∈ T := hF_sub_T hjF
        have hjTF : j ∉ T \ F := fun h => (Finset.mem_sdiff.1 h).2 hjF
        refine ⟨hjT, ?_⟩
        simp only [α', hjTF, ↓reduceIte]
        exact (st.le_t₀_frozen j hjF).trans ht₀t
    have htight_sub : ∀ S ⊆ T, G.IsTight (fun k => min (α' k) t) S → S ⊆ F := by
      intro S hST hSt
      by_contra hnot
      have hSF : (S \ F).Nonempty := Finset.nonempty_iff_ne_empty.2
        (mt Finset.sdiff_eq_empty_iff_subset.1 hnot)
      have hmul := G.mul_nextFreezeDelta_le hne α hST hSF
      have hcard_pos : (0 : ℝ) < (S \ F).card := by exact_mod_cast Finset.card_pos.2 hSF
      have hlt_mul : ((S \ F).card : ℝ) * (t - t₀) < ((S \ F).card : ℝ) * δ :=
        mul_lt_mul_of_pos_left (by linarith) hcard_pos
      have heq : (∑ k ∈ S, min (α' k) t) = G.cost S := hSt
      rw [hsum_t hST] at heq
      linarith
    have hmax_F : G.maximalTightSet T (fun j => min (α' j) t) = F := by
      refine le_antisymm ?_ ?_
      · exact htight_sub _ (G.maximalTightSet_subset T _)
          (G.isTight_maximalTightSet hsub hfeas_t)
      · refine G.subset_maximalTightSet_of_isTight hsub hfeas_t hF_sub_T ?_
        rw [IsTight, hsum_t hF_sub_T, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
          Nat.cast_zero, zero_mul, add_zero]
        exact G.isTight_maximalTightSet hsub st.feasible
    exact ⟨hfeas_t, hfilt_F.trans hmax_F.symm⟩

private theorem waterFilling_step {G : CostSharingGame A} {T : Finset A} {α : A → ℝ} {t₀ : ℝ}
    (hsub : G.IsSubmodular) (st : WaterFillingState G T α t₀)
    (hne : (T \ G.maximalTightSet T α).Nonempty) :
    let F := G.maximalTightSet T α
    let δ := G.nextFreezeDelta T F hne α
    let α' : A → ℝ := fun j => if j ∈ T \ F then α j + δ else α j
    0 < δ ∧ F ⊂ G.maximalTightSet T α' ∧ WaterFillingState G T α' (t₀ + δ) := by
  intro F δ α'
  obtain ⟨⟨SStar, hSStar_mem⟩, _, hδ_eq⟩ :=
    Finset.exists_mem_eq_inf' (nonempty_attach_activeSubsets hne)
      (fun x : {S // S ∈ T.powerset.filter (fun S => (S \ F).Nonempty)} =>
        (G.cost x.1 - ∑ j ∈ x.1, α j) / ((x.1 \ F).card : ℝ))
  have hδ_val : δ = (G.cost SStar - ∑ j ∈ SStar, α j) / ((SStar \ F).card : ℝ) := hδ_eq
  have hSStar_T : SStar ⊆ T := Finset.mem_powerset.1 (Finset.mem_filter.1 hSStar_mem).1
  have hSStar_SF : (SStar \ F).Nonempty := (Finset.mem_filter.1 hSStar_mem).2
  have hδ_pos : 0 < δ := by
    have hle : ∑ j ∈ SStar, α j ≤ G.cost SStar := st.feasible hSStar_T
    have hne_cost : ∑ j ∈ SStar, α j ≠ G.cost SStar := by
      intro heq
      have hsubF : SStar ⊆ F := G.subset_maximalTightSet_of_isTight hsub st.feasible hSStar_T heq
      obtain ⟨x, hx⟩ := hSStar_SF
      exact (Finset.mem_sdiff.1 hx).2 (hsubF (Finset.mem_sdiff.1 hx).1)
    have hlt_cost : 0 < G.cost SStar - ∑ j ∈ SStar, α j := sub_pos.2 (lt_of_le_of_ne hle hne_cost)
    have hcard_pos : (0 : ℝ) < (SStar \ F).card := by exact_mod_cast Finset.card_pos.2 hSStar_SF
    rw [hδ_val]
    exact div_pos hlt_cost hcard_pos
  have hfeas' : G.IsCoreFeasibleOn T α' := by
    intro S hST
    dsimp only [α']
    rw [sum_shift_on_sdiff hST α δ]
    by_cases hSF : (S \ F).Nonempty
    · have hmul := G.mul_nextFreezeDelta_le hne α hST hSF
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hSF, Finset.card_empty, Nat.cast_zero, zero_mul,
        add_zero]
      exact st.feasible hST
  set F' := G.maximalTightSet T α'
  have hF_sub_T : F ⊆ T := G.maximalTightSet_subset T α
  have hF_tight' : G.IsTight α' F := by
    rw [IsTight]
    dsimp only [α']
    rw [sum_shift_on_sdiff hF_sub_T α δ, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
      Nat.cast_zero, zero_mul, add_zero]
    exact G.isTight_maximalTightSet hsub st.feasible
  have hF_sub_F' : F ⊆ F' :=
    G.subset_maximalTightSet_of_isTight hsub hfeas' hF_sub_T hF_tight'
  have hSStar_tight' : G.IsTight α' SStar := by
    rw [IsTight]
    dsimp only [α']
    rw [sum_shift_on_sdiff hSStar_T α δ, hδ_val]
    have hcard_ne : ((SStar \ F).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 hSStar_SF).ne'
    field_simp
    ring
  have hSStar_sub_F' : SStar ⊆ F' :=
    G.subset_maximalTightSet_of_isTight hsub hfeas' hSStar_T hSStar_tight'
  have hF_ssub_F' : F ⊂ F' := by
    refine ssubset_of_subset_not_subset hF_sub_F' fun hF'_sub_F => ?_
    obtain ⟨x, hx⟩ := hSStar_SF
    exact (Finset.mem_sdiff.1 hx).2 (hF'_sub_F (hSStar_sub_F' (Finset.mem_sdiff.1 hx).1))
  refine ⟨hδ_pos, hF_ssub_F',
    { t₀_nonneg := by linarith [st.t₀_nonneg]
      feasible := hfeas'
      zero_outside := fun j hj => by
        have hjTF : j ∉ T \ F := fun h => hj (Finset.mem_sdiff.1 h).1
        simp only [α', hjTF, ↓reduceIte, st.zero_outside j hj]
      nonneg := fun j => by
        simp only [α']
        split_ifs
        · linarith [st.nonneg j]
        · exact st.nonneg j
      eq_t₀_unfrozen := fun j hj => by
        have hjTF : j ∈ T \ F :=
          Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hj).1,
            fun hjF => (Finset.mem_sdiff.1 hj).2 (hF_sub_F' hjF)⟩
        simp only [α', hjTF, ↓reduceIte, st.eq_t₀_unfrozen j hjTF]
      le_t₀_frozen := fun j hjF' => by
        have hjT : j ∈ T := G.maximalTightSet_subset T α' hjF'
        by_cases hjF : j ∈ F
        · have hnot : j ∉ T \ F := fun h => (Finset.mem_sdiff.1 h).2 hjF
          simp only [α', hnot, ↓reduceIte]
          linarith [st.le_t₀_frozen j hjF]
        · have hjTF : j ∈ T \ F := Finset.mem_sdiff.2 ⟨hjT, hjF⟩
          simp only [α', hjTF, ↓reduceIte, st.eq_t₀_unfrozen j hjTF, le_rfl]
      history := fun _ ht0 htt => waterFilling_step_history hsub st hne ht0 htt }⟩

private theorem waterFilling_loop_spec {G : CostSharingGame A} {T : Finset A}
    (hsub : G.IsSubmodular) :
    ∀ (fuel : ℕ) {α : A → ℝ} {t₀ : ℝ},
      WaterFillingState G T α t₀ →
      T.card - (G.maximalTightSet T α).card ≤ fuel →
      let αf := G.submodularCostShareLoop T fuel α
      ∃ tf : ℝ, WaterFillingState G T αf tf ∧ G.maximalTightSet T αf = T
  | 0, α, t₀, st, hfuel => by
    have hsubF : G.maximalTightSet T α ⊆ T := G.maximalTightSet_subset T α
    have hcard_ge : T.card ≤ (G.maximalTightSet T α).card := by omega
    have hFT : G.maximalTightSet T α = T :=
      Finset.eq_of_subset_of_card_le hsubF hcard_ge
    exact ⟨t₀, st, hFT⟩
  | fuel + 1, α, t₀, st, hfuel => by
    dsimp only [submodularCostShareLoop]
    by_cases hne : (T \ G.maximalTightSet T α).Nonempty
    · simp only [hne, ↓reduceDIte]
      let α' : A → ℝ := fun j =>
        if j ∈ T \ G.maximalTightSet T α then
          α j + G.nextFreezeDelta T (G.maximalTightSet T α) hne α
        else α j
      obtain ⟨_, hssub, st'⟩ := waterFilling_step hsub st hne
      have hcard_lt : (G.maximalTightSet T α).card < (G.maximalTightSet T α').card :=
        Finset.card_lt_card hssub
      have hfuel' : T.card - (G.maximalTightSet T α').card ≤ fuel := by omega
      exact waterFilling_loop_spec hsub fuel st' hfuel'
    · simp only [hne, ↓reduceDIte]
      have hT_sub_F : T ⊆ G.maximalTightSet T α :=
        Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hne)
      have hFT : G.maximalTightSet T α = T :=
        le_antisymm (G.maximalTightSet_subset T α) hT_sub_F
      exact ⟨t₀, st, hFT⟩

private theorem submodularCostShare_waterFilling {G : CostSharingGame A}
    (hsub : G.IsSubmodular) (hnn : G.IsNonneg) (T : Finset A) :
    let α := G.submodularCostShare T
    G.IsCoreFeasibleOn T α ∧ G.IsTight α T ∧ (∀ j ∉ T, α j = 0) ∧ (∀ j, 0 ≤ α j) ∧
      ∀ t : ℝ, 0 ≤ t →
        G.IsCoreFeasibleOn T (fun j => min (α j) t) ∧
          T.filter (fun j => α j ≤ t) = G.maximalTightSet T (fun j => min (α j) t) := by
  have st₀ : WaterFillingState G T (fun _ => 0) 0 :=
    { t₀_nonneg := le_rfl
      feasible := fun S _ => by simp only [Finset.sum_const_zero]; exact hnn S
      zero_outside := fun _ _ => rfl
      nonneg := fun _ => le_rfl
      eq_t₀_unfrozen := fun _ _ => rfl
      le_t₀_frozen := fun _ _ => le_rfl
      history := fun t ht0 htt => absurd htt (not_lt.2 ht0) }
  obtain ⟨tf, stf, hFT⟩ :=
    waterFilling_loop_spec hsub T.card st₀ (Nat.sub_le T.card _)
  change WaterFillingState G T (G.submodularCostShare T) tf at stf
  change G.maximalTightSet T (G.submodularCostShare T) = T at hFT
  set α := G.submodularCostShare T
  have htightT : G.IsTight α T := hFT ▸ G.isTight_maximalTightSet hsub stf.feasible
  refine ⟨stf.feasible, htightT, stf.zero_outside, stf.nonneg, fun t ht0 => ?_⟩
  rcases lt_or_ge t tf with httf | htft
  · exact stf.history t ht0 httf
  · have hmin_eq : (fun j => min (α j) t) = α := by
      ext j
      by_cases hjT : j ∈ T
      · have hjF : j ∈ G.maximalTightSet T α := hFT.symm ▸ hjT
        exact min_eq_left ((stf.le_t₀_frozen j hjF).trans htft)
      · rw [stf.zero_outside j hjT, min_eq_left ht0]
    have hfilt_T : T.filter (fun j => α j ≤ t) = T := by
      refine Finset.filter_true_of_mem fun j hjT => ?_
      have hjF : j ∈ G.maximalTightSet T α := hFT.symm ▸ hjT
      exact (stf.le_t₀_frozen j hjF).trans htft
    rw [hmin_eq, hfilt_T, hFT]
    exact ⟨stf.feasible, rfl⟩

/-- The cost-sharing scheme defined by `SubmodularCostShare` ([JainMahdian2007], Figure 15.3,
pp. 396–397; Dutta and Ray 1989; Jain and Vazirani 2002): starting from `α = 0`, raise all unfrozen
shares `j ∈ T \ F` at the same unit rate until a new coalition goes tight, freeze the new maximal
tight set, and repeat until `F = T`. -/
noncomputable def submodularCostShareScheme (G : CostSharingGame A) : CostSharingScheme A where
  share := G.submodularCostShare
  share_eq_zero_of_not_mem {T i} hi :=
    G.submodularCostShareLoop_of_notMem T T.card (fun _ => 0) i hi

theorem submodularCostShareScheme_isNonneg {G : CostSharingGame A}
    (hsub : G.IsSubmodular) (hnn : G.IsNonneg) :
    G.submodularCostShareScheme.IsNonneg := fun T i =>
  (G.submodularCostShare_waterFilling hsub hnn T).2.2.2.1 i

/-- `SubmodularCostShare` is `1`-budget-balanced (`∑ i ∈ T, ξ(T, i) = G.cost T` for all `T`,
[JainMahdian2007], p. 396). -/
theorem submodularCostShareScheme_isBudgetBalanced {G : CostSharingGame A}
    (hsub : G.IsSubmodular) (hnn : G.IsNonneg) :
    G.submodularCostShareScheme.IsBudgetBalanced G 1 := by
  rw [CostSharingScheme.isBudgetBalanced_one_iff]
  intro T
  exact (G.submodularCostShare_waterFilling hsub hnn T).2.1

/-- **Theorem 15.20** ([JainMahdian2007], pp. 396–397; Dutta and Ray 1989; Jain and Vazirani 2002):
for any nonnegative submodular cost-sharing game `G`, the cost-sharing scheme defined by
`SubmodularCostShare` is **cross-monotone**. -/
theorem submodularCostShareScheme_isCrossMonotone {G : CostSharingGame A}
    (hsub : G.IsSubmodular) (hnn : G.IsNonneg) :
    G.submodularCostShareScheme.IsCrossMonotone := by
  intro T₁ T₂ hT₁₂ i hiT₁
  change G.submodularCostShare T₂ i ≤ G.submodularCostShare T₁ i
  set α₁ := G.submodularCostShare T₁
  set α₂ := G.submodularCostShare T₂
  obtain ⟨_, _, _, hnn₁, hhist₁⟩ := G.submodularCostShare_waterFilling hsub hnn T₁
  obtain ⟨_, _, _, _, hhist₂⟩ := G.submodularCostShare_waterFilling hsub hnn T₂
  -- Compare both runs at time `t = α₁ i ≥ 0` (`F₁ ⊆ F₂`, following pp. 396–397).
  set t := α₁ i
  have ht0 : 0 ≤ t := hnn₁ i
  obtain ⟨hfeas₁, hF₁_eq⟩ := hhist₁ t ht0
  obtain ⟨hfeas₂, hF₂_eq⟩ := hhist₂ t ht0
  set α₁t : A → ℝ := fun j => min (α₁ j) t
  set α₂t : A → ℝ := fun j => min (α₂ j) t
  set F₁ := T₁.filter (fun j => α₁ j ≤ t)
  set F₂ := T₂.filter (fun j => α₂ j ≤ t)
  have hF₁_tight : G.IsTight α₁t F₁ :=
    hF₁_eq.symm ▸ G.isTight_maximalTightSet hsub hfeas₁
  have hF₂_tight : G.IsTight α₂t F₂ :=
    hF₂_eq.symm ▸ G.isTight_maximalTightSet hsub hfeas₂
  have hF₁_sub_T₁ : F₁ ⊆ T₁ := Finset.filter_subset _ T₁
  have hF₂_sub_T₂ : F₂ ⊆ T₂ := Finset.filter_subset _ T₂
  have hinter_le : ∑ j ∈ F₁ ∩ F₂, α₁t j ≤ G.cost (F₁ ∩ F₂) :=
    hfeas₁ (Finset.inter_subset_left.trans hF₁_sub_T₁)
  -- Every `j ∈ F₁ \ F₂` lies in `T₂` and is unfrozen at time `t` in the `T₂`-run, so `α₂t j = t`.
  have hsdiff_le : ∑ j ∈ F₁ \ F₂, α₁t j ≤ ∑ j ∈ F₁ \ F₂, α₂t j := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjF₁ : j ∈ F₁ := (Finset.mem_sdiff.1 hj).1
    have hjF₂ : j ∉ F₂ := (Finset.mem_sdiff.1 hj).2
    have hjT₂ : j ∈ T₂ := hT₁₂ (hF₁_sub_T₁ hjF₁)
    have hgt : t < α₂ j := by
      by_contra hle
      exact hjF₂ (Finset.mem_filter.2 ⟨hjT₂, not_lt.1 hle⟩)
    have hα₂tj : α₂t j = t := min_eq_right hgt.le
    rw [hα₂tj]
    exact min_le_right (α₁ j) t
  -- Submodularity uncrosses `F₁` and `F₂` to show `F₁ ∪ F₂` is tight for `α₂t`.
  have hU_sub_T₂ : F₁ ∪ F₂ ⊆ T₂ := Finset.union_subset (hF₁_sub_T₁.trans hT₁₂) hF₂_sub_T₂
  have hU_tight : G.IsTight α₂t (F₁ ∪ F₂) := by
    have hU_le : ∑ j ∈ F₁ ∪ F₂, α₂t j ≤ G.cost (F₁ ∪ F₂) := hfeas₂ hU_sub_T₂
    have hmod : G.cost (F₁ ∪ F₂) + G.cost (F₁ ∩ F₂) ≤ G.cost F₁ + G.cost F₂ := hsub F₁ F₂
    have hsplit₁ : ∑ j ∈ F₁, α₁t j = (∑ j ∈ F₁ \ F₂, α₁t j) + ∑ j ∈ F₁ ∩ F₂, α₁t j := by
      have hunion₁ : (F₁ \ F₂) ∪ (F₁ ∩ F₂) = F₁ := Finset.sdiff_union_inter F₁ F₂
      have hdisj₁ : Disjoint (F₁ \ F₂) (F₁ ∩ F₂) := Finset.disjoint_sdiff_inter F₁ F₂
      conv_lhs => rw [← hunion₁]
      exact Finset.sum_union hdisj₁
    have hsplit₂ : ∑ j ∈ F₁ ∪ F₂, α₂t j = (∑ j ∈ F₁ \ F₂, α₂t j) + ∑ j ∈ F₂, α₂t j := by
      have hdisj : Disjoint (F₁ \ F₂) F₂ := Finset.sdiff_disjoint
      have hunion : (F₁ \ F₂) ∪ F₂ = F₁ ∪ F₂ := Finset.sdiff_union_self_eq_union
      rw [← hunion, Finset.sum_union hdisj]
    rw [IsTight] at hF₁_tight hF₂_tight ⊢
    linarith
  have hU_sub_F₂ : F₁ ∪ F₂ ⊆ F₂ := by
    have h := G.subset_maximalTightSet_of_isTight hsub hfeas₂ hU_sub_T₂ hU_tight
    rwa [← hF₂_eq] at h
  have hiF₁ : i ∈ F₁ := Finset.mem_filter.2 ⟨hiT₁, le_rfl⟩
  have hiF₂ : i ∈ F₂ := hU_sub_F₂ (Finset.subset_union_left hiF₁)
  exact (Finset.mem_filter.1 hiF₂).2

end Submodular

end CostSharingGame

end Cslib.GameTheory
