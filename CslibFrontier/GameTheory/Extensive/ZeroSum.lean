/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Extensive.PerfectInfoEmbedding
public import CslibFrontier.GameTheory.Extensive.SequenceFormLP
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zero-sum extensive-form games, sparse sequence form, minimax duality, and subgame perfection

This module develops two-player zero-sum extensive-form game theory in sequence, behavioral,
mixed, and perfect-information form ([vonStengel1996], [vonStengel2007], Chapter 3):

* **Sparse sequence-form payoff matrices** (`seqPayoffMat_apply`,
  `seqPayoffMat_eq_sum_filter_terminal`, `card_support_seqPayoffMat_le_card_terminal`,
  `dotProduct_seqPayoffMat_mulVec_eq_sum_support`, `ExtensiveTree.HasNoChance`): the sequence-form
  payoff matrix `T.seqPayoffMat p` has at most `Fintype.card (Terminal T)` nonzero entries—linear
  in the number of game-tree leaves rather than quadratic in exponential normal-form pure-strategy
  sets—and in chance-free trees (`HasNoChance`) each leaf maps injectively (`leafSeqPair_injective`)
  to a matrix entry holding the bare leaf payoff (`seqPayoffMat_leafSeqPair`).
* **Realization-plan minimax equivalence** (`seq_minimax_duality`, `seq_iSup_iInf_eq_iInf_iSup`,
  `isSeqNash_iff_saddlePoint`, `isSeqNash_iff_maximin_minimax`, `IsSeqNash.interchange`,
  `IsSeqNash.payoff_eq`): under perfect recall for both players and `ExtensiveTree.IsZeroSum`,
  `⨆ x, ⨅ y, x ⬝ᵥ (A *ᵥ y) = ⨅ y, ⨆ x, x ⬝ᵥ (A *ᵥ y)` over the sequence-form polytopes
  `{x | seqMat T i *ᵥ x = seqRhs T i, 0 ≤ x}`, sequence-form Nash equilibria coincide with saddle
  points and maximin/minimax pairs, satisfy equilibrium interchangeability, and determine a unique
  game value.
* **Behavioral and mixed minimax equivalences** (`behavior_iSup_iInf_eq_iInf_iSup`,
  `behavior_minimax_eq_seq_minimax`, `isBehaviorNash_iff_saddlePoint`,
  `isBehaviorNash_iff_maximin_minimax`, `isBehaviorNash_of_saddle`, `mixed_iSup_iInf_eq_iInf_iSup`,
  `mixed_minimax_eq_behavior_minimax`): `max_x min_y = min_y max_x` agrees numerically across
  realization plans, behavioral strategies, and mixed strategies, with an explicit saddle-point
  certificate helper (`isBehaviorNash_of_saddle`) for concrete finite extensive games.
* **Perfect-information zero-sum games and subgame-perfect equilibria**
  (`PerfectInfoTree.IsZeroSum`, `PerfectInfoTree.IsBehaviorSPE`, `isPureSPE_iff_isBehaviorSPE`,
  `backwardInduction_isBehaviorSPE`, `backwardInduction_snd_eq_seq_minimax`,
  `isBehaviorNash_evalBehavior_eq_backwardInduction`,
  `isBehaviorSPE_evalBehavior_eq_backwardInduction`): every zero-sum `PerfectInfoTree Bool` embeds
  via `T.toExtensiveTree` with minimax value equal to `(T.backwardInduction).2 false`, and every
  behavioral/sequence-form/mixed Nash equilibrium—even in trees with continuation ties or non-SPE
  off-path threats—attains the unique backward-induction payoff `(T.backwardInduction).2`.

## References

* [B. von Stengel, *Efficient Computation of Behavior Strategies*][vonStengel1996], §3.
* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Chapter 3, §§3.7–3.10 and Theorem 3.13.
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset Matrix

universe u v

section Helpers

private theorem bool_profile_eq {α : Bool → Type*} (β : ∀ i : Bool, α i) :
    (fun | false => β false | true => β true) = β := by
  funext i
  cases i <;> rfl

private theorem update_false_eq {α : Bool → Type*} (β : ∀ i : Bool, α i) (x : α false) :
    Function.update β false x = fun | false => x | true => β true := by
  funext i
  cases i
  · simp
  · rw [Function.update_of_ne Bool.false_ne_true.symm]

private theorem update_true_eq {α : Bool → Type*} (β : ∀ i : Bool, α i) (y : α true) :
    Function.update β true y = fun | false => β false | true => y := by
  funext i
  cases i
  · rw [Function.update_of_ne Bool.false_ne_true]
  · simp

private theorem dotProduct_neg_transpose_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ) :
    (-(Aᵀ *ᵥ x)) ⬝ᵥ y = -(x ⬝ᵥ (A *ᵥ y)) := by
  rw [neg_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

private theorem eval_isLeast_of_neg_isGreatest {α : Type*} (S : Set α) (f : α → ℝ) {u : ℝ}
    (hmax : IsGreatest ((fun y => -f y) '' S) u) :
    IsLeast (f '' S) (-u) := by
  obtain ⟨y₀, hy₀, hy₀_eq⟩ := hmax.1
  refine ⟨⟨y₀, hy₀, by linarith⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hle : -f y ≤ u := hmax.2 ⟨y, hy, rfl⟩
  linarith

end Helpers

section SparsePayoffMatrix

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

/-- The pair `(z.seq false, z.seq true)` of sequence-form indices realized at terminal leaf `z`.
-/
@[expose] def ExtensiveTree.leafSeqPair (T : ExtensiveTree Bool H Act) (z : Terminal T) :
    SeqVar T false × SeqVar T true :=
  (⟨z.seq false, z, List.prefix_rfl⟩, ⟨z.seq true, z, List.prefix_rfl⟩)

theorem ExtensiveTree.leafSeqPair_eq_iff (T : ExtensiveTree Bool H Act) (z : Terminal T)
    (σ₀ : SeqVar T false) (σ₁ : SeqVar T true) :
    T.leafSeqPair z = (σ₀, σ₁) ↔ z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 := by
  simp only [ExtensiveTree.leafSeqPair, Prod.mk.injEq, Subtype.ext_iff]

open Classical in
/-- Exact entry formula for `T.seqPayoffMat p` ([vonStengel1996], §3; [vonStengel2007], §3.10):
entry `(σ₀, σ₁)` sums `z.chanceWeight * z.payoff p` over terminal leaves realizing sequence pair
`(σ₀, σ₁)`. -/
theorem seqPayoffMat_apply [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool) (σ₀ : SeqVar T false) (σ₁ : SeqVar T true) :
    T.seqPayoffMat p σ₀ σ₁ =
      ∑ z : Terminal T,
        if z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 then z.chanceWeight * z.payoff p else 0 := by
  classical
  let r₀ : Seq H Act false → ℝ := fun σ => if σ = σ₀.1 then 1 else 0
  let r₁ : Seq H Act true → ℝ := fun τ => if τ = σ₁.1 then 1 else 0
  have hb := seqPayoffMat_bilinear T p r₀ r₁
  have hr0 : (fun σ : SeqVar T false => r₀ σ.1) = Pi.single σ₀ (1 : ℝ) := by
    ext σ
    by_cases h : σ = σ₀
    · subst h; simp [r₀]
    · have hne : σ.1 ≠ σ₀.1 := fun heq => h (Subtype.ext heq)
      simp [r₀, h, hne]
  have hr1 : (fun τ : SeqVar T true => r₁ τ.1) = Pi.single σ₁ (1 : ℝ) := by
    ext τ
    by_cases h : τ = σ₁
    · subst h; simp [r₁]
    · have hne : τ.1 ≠ σ₁.1 := fun heq => h (Subtype.ext heq)
      simp [r₁, h, hne]
  rw [hr0, hr1] at hb
  have hlhs : (Pi.single σ₀ (1 : ℝ)) ⬝ᵥ (T.seqPayoffMat p *ᵥ Pi.single σ₁ (1 : ℝ)) =
      T.seqPayoffMat p σ₀ σ₁ := by
    rw [dotProduct, sum_eq_single σ₀]
    · simp only [Pi.single_eq_same, one_mul, Matrix.mulVec, dotProduct]
      rw [sum_eq_single σ₁]
      · simp
      · intro τ _ hne
        simp [hne]
      · intro hmem
        exact absurd (mem_univ σ₁) hmem
    · intro σ _ hne
      simp [hne]
    · intro hmem
      exact absurd (mem_univ σ₀) hmem
  rw [hlhs] at hb
  rw [hb]
  refine sum_congr rfl fun z _ => ?_
  by_cases h0 : z.seq false = σ₀.1 <;> by_cases h1 : z.seq true = σ₁.1 <;>
    simp [r₀, r₁, h0, h1]

open Classical in
/-- Express entry `(σ₀, σ₁)` of `T.seqPayoffMat p` as the sum over the leaf bucket
`{z : Terminal T | T.leafSeqPair z = (σ₀, σ₁)}`. -/
theorem seqPayoffMat_eq_sum_filter_terminal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool) (σ₀ : SeqVar T false) (σ₁ : SeqVar T true) :
    T.seqPayoffMat p σ₀ σ₁ =
      ∑ z ∈ univ.filter (fun z : Terminal T => T.leafSeqPair z = (σ₀, σ₁)),
        z.chanceWeight * z.payoff p := by
  rw [seqPayoffMat_apply, Finset.sum_filter]
  refine sum_congr rfl fun z _ => ?_
  simp only [T.leafSeqPair_eq_iff]

/-- Every entry `(σ₀, σ₁)` not realized by any terminal leaf of `T` is zero in
`T.seqPayoffMat p`. -/
theorem seqPayoffMat_apply_eq_zero_of_ne_leafSeqPair [∀ i h, Fintype (Act i h)]
    {T : ExtensiveTree Bool H Act} (p : Bool) {σ₀ : SeqVar T false} {σ₁ : SeqVar T true}
    (hnone : ∀ z : Terminal T, T.leafSeqPair z ≠ (σ₀, σ₁)) :
    T.seqPayoffMat p σ₀ σ₁ = 0 := by
  classical
  rw [seqPayoffMat_eq_sum_filter_terminal]
  exact sum_eq_zero fun z hz => absurd (mem_filter.1 hz).2 (hnone z)

open Classical in
/-- Every nonzero entry of `T.seqPayoffMat p` belongs to the image of `T.leafSeqPair`. -/
theorem filter_seqPayoffMat_ne_zero_subset_image [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool) :
    univ.filter (fun e : SeqVar T false × SeqVar T true => T.seqPayoffMat p e.1 e.2 ≠ 0) ⊆
      univ.image T.leafSeqPair := by
  intro ⟨σ₀, σ₁⟩ he
  simp only [mem_filter, mem_univ, true_and, ne_eq] at he
  rw [mem_image]
  by_contra hnone
  push Not at hnone
  exact he (seqPayoffMat_apply_eq_zero_of_ne_leafSeqPair p fun z => hnone z (mem_univ z))

open Classical in
/-- **Sparse payoff matrix size bound** ([vonStengel1996], §3; [vonStengel2007], §3.10):
the sequence-form payoff matrix `T.seqPayoffMat p` has at most `Fintype.card (Terminal T)` nonzero
entries—linear in the number of leaves of the extensive game tree. -/
theorem card_support_seqPayoffMat_le_card_terminal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool) :
    (univ.filter (fun e : SeqVar T false × SeqVar T true =>
        T.seqPayoffMat p e.1 e.2 ≠ 0)).card ≤
      Fintype.card (Terminal T) :=
  (card_le_card (filter_seqPayoffMat_ne_zero_subset_image T p)).trans
    (card_image_le.trans (by rw [card_univ]))

open Classical in
/-- Sparse bilinear evaluation of `x ⬝ᵥ (T.seqPayoffMat p *ᵥ y)` restricted strictly to the
nonzero entries of `T.seqPayoffMat p`. -/
theorem dotProduct_seqPayoffMat_mulVec_eq_sum_support [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    x ⬝ᵥ (T.seqPayoffMat p *ᵥ y) =
      ∑ e ∈ univ.filter (fun e : SeqVar T false × SeqVar T true =>
          T.seqPayoffMat p e.1 e.2 ≠ 0),
        x e.1 * T.seqPayoffMat p e.1 e.2 * y e.2 := by
  rw [Finset.sum_filter]
  have hprod : x ⬝ᵥ (T.seqPayoffMat p *ᵥ y) =
      ∑ e : SeqVar T false × SeqVar T true, x e.1 * T.seqPayoffMat p e.1 e.2 * y e.2 := by
    rw [dotProduct]
    simp only [Matrix.mulVec, dotProduct, mul_sum, ← mul_assoc, Fintype.sum_prod_type]
  rw [hprod]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with hne
  · rfl
  · push Not at hne
    simp [hne]

open Classical in
/-- Leaf-indexed evaluation of `x ⬝ᵥ (T.seqPayoffMat p *ᵥ y)` for arbitrary vectors `x, y`. -/
theorem dotProduct_seqPayoffMat_mulVec_eq_sum_terminal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    x ⬝ᵥ (T.seqPayoffMat p *ᵥ y) =
      ∑ z : Terminal T,
        (z.chanceWeight * x (T.leafSeqPair z).1 * y (T.leafSeqPair z).2) * z.payoff p := by
  let r₀ : Seq H Act false → ℝ := fun σ => if h : ∃ z : Terminal T, σ <+: z.seq false then
    x ⟨σ, h⟩ else 0
  let r₁ : Seq H Act true → ℝ := fun τ => if h : ∃ z : Terminal T, τ <+: z.seq true then
    y ⟨τ, h⟩ else 0
  have hb := seqPayoffMat_bilinear T p r₀ r₁
  have hr0 : (fun σ : SeqVar T false => r₀ σ.1) = x := by
    ext σ
    simp [r₀, σ.2]
  have hr1 : (fun τ : SeqVar T true => r₁ τ.1) = y := by
    ext τ
    simp [r₁, τ.2]
  rw [hr0, hr1] at hb
  rw [hb]
  refine sum_congr rfl fun z _ => ?_
  have hz0 : r₀ (z.seq false) = x (T.leafSeqPair z).1 := by
    have hex : ∃ w : Terminal T, z.seq false <+: w.seq false := ⟨z, List.prefix_rfl⟩
    simp [r₀, hex, ExtensiveTree.leafSeqPair]
  have hz1 : r₁ (z.seq true) = y (T.leafSeqPair z).2 := by
    have hex : ∃ w : Terminal T, z.seq true <+: w.seq true := ⟨z, List.prefix_rfl⟩
    simp [r₁, hex, ExtensiveTree.leafSeqPair]
  rw [hz0, hz1]

/-- An extensive-form game tree has no chance nodes (`HasNoChance`). -/
@[expose] def ExtensiveTree.HasNoChance {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type} :
    ExtensiveTree ι H Act → Prop
  | .leaf _ => True
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _ => False
  | .decision _ _ next => ∀ a, HasNoChance (next a)

theorem ExtensiveTree.HasNoChance.chanceWeight_eq_one {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : ExtensiveTree ι H Act}, T.HasNoChance → ∀ z : Terminal T, z.chanceWeight = 1
  | .leaf _, _, .leaf => rfl
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, hnc, .chance _ _ => False.elim hnc
  | .decision _ _ _, hnc, .decision a sub =>
      (hnc a).chanceWeight_eq_one sub

private theorem eq_of_hasNoChance_seq_eq {T : ExtensiveTree Bool H Act} (hnc : T.HasNoChance) :
    ∀ {z₁ z₂ : Terminal T},
      z₁.seq false = z₂.seq false → z₁.seq true = z₂.seq true → z₁ = z₂ := by
  induction T with
  | leaf _ =>
    intro z₁ z₂ _ _
    cases z₁
    cases z₂
    rfl
  | chance _ _ _ =>
    exact False.elim hnc
  | decision p _ _ ih =>
    intro z₁ z₂ h0 h1
    cases z₁ with
    | decision a₁ sub₁ =>
      cases z₂ with
      | decision a₂ sub₂ =>
        cases p with
        | false =>
          simp only [Terminal.seq_decision_self,
            Terminal.seq_decision_ne Bool.false_ne_true] at h0 h1
          obtain ⟨hhead, htail⟩ := List.cons.inj h0
          have ha : a₁ = a₂ := eq_of_heq (Sigma.mk.inj_iff.1 hhead).2
          subst ha
          exact congrArg (Terminal.decision a₁) (ih a₁ (hnc a₁) htail h1)
        | true =>
          simp only [Terminal.seq_decision_self,
            Terminal.seq_decision_ne Bool.false_ne_true.symm] at h0 h1
          obtain ⟨hhead, htail⟩ := List.cons.inj h1
          have ha : a₁ = a₂ := eq_of_heq (Sigma.mk.inj_iff.1 hhead).2
          subst ha
          exact congrArg (Terminal.decision a₁) (ih a₁ (hnc a₁) h0 htail)

/-- In a chance-free two-player extensive game tree, distinct terminal leaves realize distinct
player-sequence pairs `T.leafSeqPair z` ([vonStengel1996], §3; [vonStengel2007], §3.10). -/
theorem ExtensiveTree.HasNoChance.leafSeqPair_injective
    {T : ExtensiveTree Bool H Act} (hnc : T.HasNoChance) :
    Function.Injective T.leafSeqPair := fun _ _ heq =>
  let ⟨h0, h1⟩ := (ExtensiveTree.leafSeqPair_eq_iff _ _ _ _).1 heq
  eq_of_hasNoChance_seq_eq hnc h0 h1

/-- In a chance-free two-player extensive game, the sequence-form payoff matrix entry at terminal
leaf `z`'s sequence pair `(z.seq false, z.seq true)` equals the bare leaf payoff `z.payoff p`
([vonStengel1996], §3; [vonStengel2007], §3.10). -/
theorem ExtensiveTree.HasNoChance.seqPayoffMat_leafSeqPair [∀ i h, Fintype (Act i h)]
    {T : ExtensiveTree Bool H Act} (hnc : T.HasNoChance) (p : Bool) (z : Terminal T) :
    T.seqPayoffMat p (T.leafSeqPair z).1 (T.leafSeqPair z).2 = z.payoff p := by
  classical
  rw [seqPayoffMat_eq_sum_filter_terminal]
  rw [Finset.sum_eq_single z]
  · rw [hnc.chanceWeight_eq_one z, one_mul]
  · intro z' hz' hne
    exfalso
    exact hne (hnc.leafSeqPair_injective (mem_filter.1 hz').2)
  · intro hmem
    exfalso
    exact hmem (mem_filter.2 ⟨mem_univ z, rfl⟩)

end SparsePayoffMatrix

section RealizationPlanMinimax

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- Given any vector `x` for player `false`, minimizing `x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)` over
valid realization plans `y` of player `true` attains a minimum whenever player `true` has perfect
recall. -/
theorem exists_isLeast_seqPayoff [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H true)]
    (hpr : T.PerfectRecall true) (x : SeqVar T false → ℝ) :
    ∃ u : ℝ, IsLeast
      ((fun y : SeqVar T true → ℝ => x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) ''
        {y | T.IsRealizationPlan true y}) u := by
  let _ := Fintype.ofFinite (H true)
  obtain ⟨u, hmax, _⟩ := exists_isGreatest_isLeast_seqLP (T := T) (i := true) hpr
    (-((T.seqPayoffMat false)ᵀ *ᵥ x))
  have himg : ((fun y => (-((T.seqPayoffMat false)ᵀ *ᵥ x)) ⬝ᵥ y) ''
      {y | T.IsRealizationPlan true y}) =
      ((fun y => -(x ⬝ᵥ (T.seqPayoffMat false *ᵥ y))) '' {y | T.IsRealizationPlan true y}) := by
    ext r
    simp_rw [dotProduct_neg_transpose_mulVec]
  rw [himg] at hmax
  exact ⟨-u, eval_isLeast_of_neg_isGreatest _ _ hmax⟩

open Classical in
/-- Given any vector `y` for player `true`, maximizing `x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)` over
valid realization plans `x` of player `false` attains a maximum whenever player `false` has
perfect recall. -/
theorem exists_isGreatest_seqPayoff [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)]
    (hpr : T.PerfectRecall false) (y : SeqVar T true → ℝ) :
    ∃ v : ℝ, IsGreatest
      ((fun x : SeqVar T false → ℝ => x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) ''
        {x | T.IsRealizationPlan false x}) v := by
  let _ := Fintype.ofFinite (H false)
  obtain ⟨v, hmax, _⟩ := exists_isGreatest_isLeast_seqLP (T := T) (i := false) hpr
    (T.seqPayoffMat false *ᵥ y)
  have himg : ((fun x => (T.seqPayoffMat false *ᵥ y) ⬝ᵥ x) '' {x | T.IsRealizationPlan false x}) =
      ((fun x => x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) '' {x | T.IsRealizationPlan false x}) := by
    ext r
    simp [dotProduct_comm]
  rw [himg] at hmax
  exact ⟨v, hmax⟩

open Classical in
/-- Worst-case sequence-form payoff `⨅ y, x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)` over all valid
realization plans `y` of player `true`. -/
noncomputable def ExtensiveTree.seqLowerVal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (x : SeqVar T false → ℝ) : ℝ :=
  ⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y},
    x ⬝ᵥ (T.seqPayoffMat false *ᵥ y.1)

open Classical in
/-- Worst-case sequence-form loss `⨆ x, x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)` over all valid
realization plans `x` of player `false`. -/
noncomputable def ExtensiveTree.seqUpperVal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (y : SeqVar T true → ℝ) : ℝ :=
  ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
    x.1 ⬝ᵥ (T.seqPayoffMat false *ᵥ y)

open Classical in
theorem isLeast_seqLowerVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H true)]
    (hpr : T.PerfectRecall true) (x : SeqVar T false → ℝ) :
    IsLeast
      ((fun y : SeqVar T true → ℝ => x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) ''
        {y | T.IsRealizationPlan true y})
      (T.seqLowerVal x) := by
  obtain ⟨u, hu⟩ := exists_isLeast_seqPayoff hpr x
  obtain ⟨y₀, hy₀, hy₀_eq⟩ := hu.1
  let _ : Nonempty {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} := ⟨⟨y₀, hy₀⟩⟩
  have hbdd : BddBelow (Set.range fun y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} =>
      x ⬝ᵥ (T.seqPayoffMat false *ᵥ y.1)) :=
    ⟨u, by rintro _ ⟨⟨y, hy⟩, rfl⟩; exact hu.2 ⟨y, hy, rfl⟩⟩
  have hval : T.seqLowerVal x = u :=
    le_antisymm ((ciInf_le hbdd ⟨y₀, hy₀⟩).trans_eq hy₀_eq)
      (le_ciInf fun ⟨y, hy⟩ => hu.2 ⟨y, hy, rfl⟩)
  rwa [hval]

open Classical in
theorem isGreatest_seqUpperVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)]
    (hpr : T.PerfectRecall false) (y : SeqVar T true → ℝ) :
    IsGreatest
      ((fun x : SeqVar T false → ℝ => x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) ''
        {x | T.IsRealizationPlan false x})
      (T.seqUpperVal y) := by
  obtain ⟨v, hv⟩ := exists_isGreatest_seqPayoff hpr y
  obtain ⟨x₀, hx₀, hx₀_eq⟩ := hv.1
  let _ : Nonempty {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} := ⟨⟨x₀, hx₀⟩⟩
  have hbdd : BddAbove (Set.range fun x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} =>
      x.1 ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) :=
    ⟨v, by rintro _ ⟨⟨x, hx⟩, rfl⟩; exact hv.2 ⟨x, hx, rfl⟩⟩
  have hval : T.seqUpperVal y = v :=
    le_antisymm (ciSup_le fun ⟨x, hx⟩ => hv.2 ⟨x, hx, rfl⟩)
      (hx₀_eq.symm.trans_le (le_ciSup hbdd ⟨x₀, hx₀⟩))
  rwa [hval]

theorem seqLowerVal_le [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H true)] (hpr : T.PerfectRecall true)
    (x : SeqVar T false → ℝ) {y : SeqVar T true → ℝ} (hy : T.IsRealizationPlan true y) :
    T.seqLowerVal x ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) :=
  (isLeast_seqLowerVal hpr x).2 ⟨y, hy, rfl⟩

open Classical in
theorem le_seqLowerVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : T.PerfectRecall true)
    {x : SeqVar T false → ℝ} {c : ℝ}
    (h : ∀ y, T.IsRealizationPlan true y → c ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) :
    c ≤ T.seqLowerVal x := by
  let β₀ := pureToBehavior (H := H) (Act := Act) (i := true) fun _ => Classical.arbitrary _
  let _ : Nonempty {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} :=
    ⟨⟨T.behaviorToRealizationPlan true β₀,
      isRealizationPlan_behaviorToRealizationPlan hpr (isBehaviorStrategy_pureToBehavior _)⟩⟩
  exact le_ciInf fun ⟨y, hy⟩ => h y hy

theorem le_seqUpperVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] (hpr : T.PerfectRecall false)
    {x : SeqVar T false → ℝ} (y : SeqVar T true → ℝ) (hx : T.IsRealizationPlan false x) :
    x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ T.seqUpperVal y :=
  (isGreatest_seqUpperVal hpr y).2 ⟨x, hx, rfl⟩

open Classical in
theorem seqUpperVal_le [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : T.PerfectRecall false)
    {y : SeqVar T true → ℝ} {c : ℝ}
    (h : ∀ x, T.IsRealizationPlan false x → x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ c) :
    T.seqUpperVal y ≤ c := by
  let β₀ := pureToBehavior (H := H) (Act := Act) (i := false) fun _ => Classical.arbitrary _
  let _ : Nonempty {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} :=
    ⟨⟨T.behaviorToRealizationPlan false β₀,
      isRealizationPlan_behaviorToRealizationPlan hpr (isBehaviorStrategy_pureToBehavior _)⟩⟩
  exact ciSup_le fun ⟨x, hx⟩ => h x hx

/-- Weak minimax inequality in sequence form: every feasible lower value is at most every feasible
upper value. -/
theorem seqLowerVal_le_seqUpperVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i)
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    (hx : T.IsRealizationPlan false x) (hy : T.IsRealizationPlan true y) :
    T.seqLowerVal x ≤ T.seqUpperVal y :=
  (seqLowerVal_le (hpr true) x hy).trans (le_seqUpperVal (hpr false) y hx)

open Classical in
private theorem seqLowerVal_seqUpperVal_eq_of_saddle [∀ i h, Fintype (Act i h)]
    [∀ i h, Nonempty (Act i h)] {T : ExtensiveTree Bool H Act}
    [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    (hx : T.IsRealizationPlan false x) (hy : T.IsRealizationPlan true y)
    (hbest0 : ∀ x', T.IsRealizationPlan false x' →
      x' ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y))
    (hbest1 : ∀ y', T.IsRealizationPlan true y' →
      x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y')) :
    T.seqLowerVal x = x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ∧
      T.seqUpperVal y = x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) :=
  ⟨le_antisymm (seqLowerVal_le (hpr true) x hy) (le_seqLowerVal (hpr true) hbest1),
   le_antisymm (seqUpperVal_le (hpr false) hbest0) (le_seqUpperVal (hpr false) y hx)⟩

namespace ExtensiveTree.IsZeroSum

open Classical in
/-- In a zero-sum extensive game, `β` is a behavioral Nash equilibrium iff it is a saddle point for
`T.evalBehavior _ false` over behavioral strategies. -/
theorem isBehaviorNash_iff_saddlePoint [∀ i h, Fintype (Act i h)]
    {T : ExtensiveTree Bool H Act} (hzs : T.IsZeroSum)
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    T.IsBehaviorNash β ↔
      (∀ i, IsBehaviorStrategy (β i)) ∧
        (∀ β₀ : ∀ h : H false, Act false h → ℝ, IsBehaviorStrategy β₀ →
          T.evalBehavior (fun | false => β₀ | true => β true) false ≤ T.evalBehavior β false) ∧
        (∀ β₁ : ∀ h : H true, Act true h → ℝ, IsBehaviorStrategy β₁ →
          T.evalBehavior β false ≤ T.evalBehavior (fun | false => β false | true => β₁) false) := by
  constructor
  · rintro ⟨hbeh, hopt⟩
    refine ⟨hbeh, fun β₀ hβ₀ => ?_, fun β₁ hβ₁ => ?_⟩
    · have h := hopt false β₀ hβ₀
      rwa [update_false_eq] at h
    · have h := hopt true β₁ hβ₁
      rw [hzs.evalBehavior_true, hzs.evalBehavior_true, neg_le_neg_iff, update_true_eq] at h
      exact h
  · rintro ⟨hbeh, h0, h1⟩
    refine ⟨hbeh, fun i β' hβ' => ?_⟩
    cases i with
    | false =>
      rw [update_false_eq]
      exact h0 β' hβ'
    | true =>
      rw [hzs.evalBehavior_true, hzs.evalBehavior_true, neg_le_neg_iff, update_true_eq]
      exact h1 β' hβ'

private noncomputable def planProfile [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    ∀ i : Bool, ∀ h : H i, Act i h → ℝ
  | false => T.realizationPlanToBehavior false (hpr false) x
  | true => T.realizationPlanToBehavior true (hpr true) y

private theorem planProfile_spec [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i)
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    (hx : T.IsRealizationPlan false x) (hy : T.IsRealizationPlan true y) :
    (∀ i, IsBehaviorStrategy (planProfile hpr x y i)) ∧
      T.behaviorToRealizationPlan false (planProfile hpr x y false) = x ∧
      T.behaviorToRealizationPlan true (planProfile hpr x y true) = y :=
  ⟨fun
    | false => isBehaviorStrategy_realizationPlanToBehavior (hpr false) hx
    | true => isBehaviorStrategy_realizationPlanToBehavior (hpr true) hy,
   behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hx,
   behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hy⟩

open Classical in
/-- In a zero-sum extensive game with perfect recall, `(x, y)` is a sequence-form Nash equilibrium
iff `(x, y)` is a saddle point of `x' ⬝ᵥ (T.seqPayoffMat false *ᵥ y')` on the sequence-form
polytopes. -/
theorem isSeqNash_iff_saddlePoint [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    T.IsSeqNash x y ↔
      T.IsRealizationPlan false x ∧ T.IsRealizationPlan true y ∧
        (∀ x', T.IsRealizationPlan false x' →
          x' ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)) ∧
        (∀ y', T.IsRealizationPlan true y' →
          x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y')) := by
  let _ := Fintype.ofFinite (H false)
  let _ := Fintype.ofFinite (H true)
  constructor
  · intro hnash
    have hcomp := (isSeqNash_iff_complementarity hpr x y).1 hnash
    obtain ⟨hx, hy⟩ := hcomp.1, hcomp.2.1
    obtain ⟨hbeh, hx_plan, hy_plan⟩ := planProfile_spec hpr hx hy
    have hbnash : T.IsBehaviorNash (planProfile hpr x y) := (isBehaviorNash_iff_isSeqNash hpr _).2
      ⟨hbeh, by simpa only [hx_plan, hy_plan] using hnash⟩
    obtain ⟨_, h0, h1⟩ := (hzs.isBehaviorNash_iff_saddlePoint _).1 hbnash
    refine ⟨hx, hy, fun x' hx' => ?_, fun y' hy' => ?_⟩
    · have hdev := h0 (T.realizationPlanToBehavior false (hpr false) x')
        (isBehaviorStrategy_realizationPlanToBehavior (hpr false) hx')
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat] at hdev
      simpa only [hx_plan, hy_plan,
        behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hx'] using hdev
    · have hdev := h1 (T.realizationPlanToBehavior true (hpr true) y')
        (isBehaviorStrategy_realizationPlanToBehavior (hpr true) hy')
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat] at hdev
      simpa only [hx_plan, hy_plan,
        behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hy'] using hdev
  · rintro ⟨hx, hy, h0, h1⟩
    obtain ⟨hbeh, hx_plan, hy_plan⟩ := planProfile_spec hpr hx hy
    have hbnash : T.IsBehaviorNash (planProfile hpr x y) := (hzs.isBehaviorNash_iff_saddlePoint _).2
      ⟨hbeh,
        fun β₀ hβ₀ => by
          rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat, hx_plan, hy_plan]
          exact h0 _ (isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ₀),
        fun β₁ hβ₁ => by
          rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat, hx_plan, hy_plan]
          exact h1 _ (isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ₁)⟩
    have hseq := ((isBehaviorNash_iff_isSeqNash hpr _).1 hbnash).2
    simpa only [hx_plan, hy_plan] using hseq

open Classical in
/-- **Sequence-form realization-plan minimax theorem** ([vonStengel1996], [vonStengel2007],
§3.10 & Theorem 3.13): the maximin problem `max_x min_y xᵀ A y` and minimax problem
`min_y max_x xᵀ A y` over the sequence-form polytopes `{x | E x = e, x ≥ 0}` both attain a common
value `v`, realized at a sequence-form Nash saddle point `(x*, y*)`. -/
theorem seq_minimax_duality [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    ∃ v : ℝ,
      IsGreatest (T.seqLowerVal '' {x | T.IsRealizationPlan false x}) v ∧
      IsLeast (T.seqUpperVal '' {y | T.IsRealizationPlan true y}) v ∧
      ∃ x y, T.IsSeqNash x y ∧ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) = v := by
  let _ := Fintype.ofFinite (H false)
  let _ := Fintype.ofFinite (H true)
  obtain ⟨v, x, y, _, _, hx, hy, _, _, hmid, _, _, hnash, _, _⟩ := hzs.exists_seq_lp_minimax hpr
  obtain ⟨_, _, hbest0, hbest1⟩ := (hzs.isSeqNash_iff_saddlePoint hpr x y).1 hnash
  obtain ⟨hlo_eq, hup_eq⟩ := seqLowerVal_seqUpperVal_eq_of_saddle hpr hx hy hbest0 hbest1
  have hlo : T.seqLowerVal x = v := hlo_eq.trans hmid
  have hup : T.seqUpperVal y = v := hup_eq.trans hmid
  refine ⟨v, ⟨⟨x, hx, hlo⟩, ?_⟩, ⟨⟨y, hy, hup⟩, ?_⟩, x, y, hnash, hmid⟩
  · rintro _ ⟨x', hx', rfl⟩
    exact (seqLowerVal_le_seqUpperVal hpr hx' hy).trans_eq hup
  · rintro _ ⟨y', hy', rfl⟩
    exact hlo.symm.trans_le (seqLowerVal_le_seqUpperVal hpr hx hy')

open Classical in
/-- **Explicit `max_x min_y = min_y max_x` identity over sequence-form polytopes**
([vonStengel1996], [vonStengel2007], §3.10):
`⨆ x, ⨅ y, x ⬝ᵥ (A *ᵥ y) = ⨅ y, ⨆ x, x ⬝ᵥ (A *ᵥ y)` over valid realization plans. -/
theorem seq_iSup_iInf_eq_iInf_iSup [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    (⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
        ⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y},
          x.1 ⬝ᵥ (T.seqPayoffMat false *ᵥ y.1)) =
      ⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y},
        ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
          x.1 ⬝ᵥ (T.seqPayoffMat false *ᵥ y.1) := by
  obtain ⟨v, ⟨⟨x₀, hx₀, hx₀_eq⟩, hmax⟩, ⟨⟨y₀, hy₀, hy₀_eq⟩, hmin⟩, _⟩ :=
    hzs.seq_minimax_duality hpr
  let _ : Nonempty {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} := ⟨⟨x₀, hx₀⟩⟩
  let _ : Nonempty {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} := ⟨⟨y₀, hy₀⟩⟩
  have hbdd_lo : BddAbove (Set.range fun x :
      {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} => T.seqLowerVal x.1) :=
    ⟨v, by rintro _ ⟨⟨x, hx⟩, rfl⟩; exact hmax ⟨x, hx, rfl⟩⟩
  have hbdd_up : BddBelow (Set.range fun y :
      {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} => T.seqUpperVal y.1) :=
    ⟨v, by rintro _ ⟨⟨y, hy⟩, rfl⟩; exact hmin ⟨y, hy, rfl⟩⟩
  have hleft : (⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
      T.seqLowerVal x.1) = v :=
    le_antisymm (ciSup_le fun ⟨x, hx⟩ => hmax ⟨x, hx, rfl⟩)
      (hx₀_eq.symm.trans_le (le_ciSup hbdd_lo ⟨x₀, hx₀⟩))
  have hright : (⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y},
      T.seqUpperVal y.1) = v :=
    le_antisymm ((ciInf_le hbdd_up ⟨y₀, hy₀⟩).trans_eq hy₀_eq)
      (le_ciInf fun ⟨y, hy⟩ => hmin ⟨y, hy, rfl⟩)
  change (⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x}, T.seqLowerVal x.1) =
    ⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y}, T.seqUpperVal y.1
  rw [hleft, hright]

open Classical in
/-- Maximin/minimax characterization of sequence-form Nash equilibria in two-player zero-sum
games with perfect recall: `(x, y)` is a sequence-form Nash equilibrium iff `x` maximizes
`T.seqLowerVal` and `y` minimizes `T.seqUpperVal`. -/
theorem isSeqNash_iff_maximin_minimax [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    T.IsSeqNash x y ↔
      (T.IsRealizationPlan false x ∧
        IsGreatest (T.seqLowerVal '' {x' | T.IsRealizationPlan false x'}) (T.seqLowerVal x)) ∧
      (T.IsRealizationPlan true y ∧
        IsLeast (T.seqUpperVal '' {y' | T.IsRealizationPlan true y'}) (T.seqUpperVal y)) := by
  obtain ⟨v, hmaxV, hminV, _⟩ := hzs.seq_minimax_duality hpr
  constructor
  · intro hnash
    obtain ⟨hx, hy, hbest0, hbest1⟩ := (hzs.isSeqNash_iff_saddlePoint hpr x y).1 hnash
    obtain ⟨hlo_eq, hup_eq⟩ := seqLowerVal_seqUpperVal_eq_of_saddle hpr hx hy hbest0 hbest1
    have hval : x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) = v :=
      le_antisymm (hlo_eq ▸ hmaxV.2 ⟨x, hx, rfl⟩) (hup_eq ▸ hminV.2 ⟨y, hy, rfl⟩)
    have hlo_v : T.seqLowerVal x = v := hlo_eq.trans hval
    have hup_v : T.seqUpperVal y = v := hup_eq.trans hval
    exact ⟨⟨hx, hlo_v.symm ▸ hmaxV⟩, ⟨hy, hup_v.symm ▸ hminV⟩⟩
  · rintro ⟨⟨hx, hx_max⟩, ⟨hy, hy_min⟩⟩
    have hlo_v : T.seqLowerVal x = v :=
      le_antisymm (hmaxV.2 ⟨x, hx, rfl⟩) (hx_max.2 hmaxV.1)
    have hup_v : T.seqUpperVal y = v :=
      le_antisymm (hy_min.2 hminV.1) (hminV.2 ⟨y, hy, rfl⟩)
    have hxy : x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) = v :=
      le_antisymm ((le_seqUpperVal (hpr false) y hx).trans_eq hup_v)
        (hlo_v.symm.trans_le (seqLowerVal_le (hpr true) x hy))
    refine (hzs.isSeqNash_iff_saddlePoint hpr x y).2 ⟨hx, hy, fun x' hx' => ?_, fun y' hy' => ?_⟩
    · exact (le_seqUpperVal (hpr false) y hx').trans_eq (hup_v.trans hxy.symm)
    · exact (hxy.trans hlo_v.symm).trans_le (seqLowerVal_le (hpr true) x hy')

end ExtensiveTree.IsZeroSum

namespace ExtensiveTree.IsSeqNash

open Classical in
/-- In a zero-sum extensive game with perfect recall, every sequence-form Nash equilibrium attains
both the `⨆ min` maximin value and the `⨅ max` minimax value. -/
theorem payoff_eq [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ} (hnash : T.IsSeqNash x y) :
    x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) =
      (⨆ x' : {x' : SeqVar T false → ℝ // T.IsRealizationPlan false x'},
        T.seqLowerVal x'.1) ∧
      x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) =
        ⨅ y' : {y' : SeqVar T true → ℝ // T.IsRealizationPlan true y'},
          T.seqUpperVal y'.1 := by
  obtain ⟨hx, hy, hbest0, hbest1⟩ := (hzs.isSeqNash_iff_saddlePoint hpr x y).1 hnash
  obtain ⟨v, ⟨⟨x₀, hx₀, hx₀_eq⟩, hmax⟩, ⟨⟨y₀, hy₀, hy₀_eq⟩, hmin⟩, _⟩ :=
    hzs.seq_minimax_duality hpr
  let _ : Nonempty {x' : SeqVar T false → ℝ // T.IsRealizationPlan false x'} := ⟨⟨x₀, hx₀⟩⟩
  let _ : Nonempty {y' : SeqVar T true → ℝ // T.IsRealizationPlan true y'} := ⟨⟨y₀, hy₀⟩⟩
  obtain ⟨hlo_eq, hup_eq⟩ := seqLowerVal_seqUpperVal_eq_of_saddle hpr hx hy hbest0 hbest1
  have hv1 : T.seqLowerVal x ≤ v := hmax ⟨x, hx, rfl⟩
  have hv2 : v ≤ T.seqUpperVal y := hmin ⟨y, hy, rfl⟩
  have hval : x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) = v := le_antisymm (hlo_eq ▸ hv1) (hup_eq ▸ hv2)
  have hbdd_lo : BddAbove (Set.range fun x' : {x' // T.IsRealizationPlan false x'} =>
      T.seqLowerVal x'.1) :=
    ⟨v, by rintro _ ⟨⟨x', hx'⟩, rfl⟩; exact hmax ⟨x', hx', rfl⟩⟩
  have hbdd_up : BddBelow (Set.range fun y' : {y' // T.IsRealizationPlan true y'} =>
      T.seqUpperVal y'.1) :=
    ⟨v, by rintro _ ⟨⟨y', hy'⟩, rfl⟩; exact hmin ⟨y', hy', rfl⟩⟩
  have hsup : (⨆ x' : {x' // T.IsRealizationPlan false x'}, T.seqLowerVal x'.1) = v :=
    le_antisymm (ciSup_le fun ⟨x', hx'⟩ => hmax ⟨x', hx', rfl⟩)
      (hx₀_eq.symm.trans_le (le_ciSup hbdd_lo ⟨x₀, hx₀⟩))
  have hinf : (⨅ y' : {y' // T.IsRealizationPlan true y'}, T.seqUpperVal y'.1) = v :=
    le_antisymm ((ciInf_le hbdd_up ⟨y₀, hy₀⟩).trans_eq hy₀_eq)
      (le_ciInf fun ⟨y', hy'⟩ => hmin ⟨y', hy', rfl⟩)
  exact ⟨hval.trans hsup.symm, hval.trans hinf.symm⟩

open Classical in
/-- **Interchangeability of sequence-form Nash equilibria** in two-player zero-sum games with
perfect recall: mixing strategies from two equilibrium profiles `(x₁, y₁)` and `(x₂, y₂)` preserves
equilibrium and yields the same value. -/
theorem interchange [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {x₁ x₂ : SeqVar T false → ℝ} {y₁ y₂ : SeqVar T true → ℝ}
    (h₁ : T.IsSeqNash x₁ y₁) (h₂ : T.IsSeqNash x₂ y₂) :
    T.IsSeqNash x₁ y₂ ∧
      x₁ ⬝ᵥ (T.seqPayoffMat false *ᵥ y₂) = x₁ ⬝ᵥ (T.seqPayoffMat false *ᵥ y₁) := by
  have hmm1 := (hzs.isSeqNash_iff_maximin_minimax hpr x₁ y₁).1 h₁
  have hmm2 := (hzs.isSeqNash_iff_maximin_minimax hpr x₂ y₂).1 h₂
  have hn12 : T.IsSeqNash x₁ y₂ :=
    (hzs.isSeqNash_iff_maximin_minimax hpr x₁ y₂).2 ⟨hmm1.1, hmm2.2⟩
  refine ⟨hn12, ?_⟩
  rw [(hn12.payoff_eq hpr hzs).1, (h₁.payoff_eq hpr hzs).1]

end ExtensiveTree.IsSeqNash

end RealizationPlanMinimax

section BehavioralAndMixedMinimax

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- Worst-case expected payoff `⨅ β₁, T.evalBehavior (false => β₀, true => β₁) false` over all
behavioral strategies `β₁` of player `true`. -/
noncomputable def ExtensiveTree.behaviorLowerVal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (β₀ : ∀ h : H false, Act false h → ℝ) : ℝ :=
  ⨅ β₁ : {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁},
    T.evalBehavior (fun | false => β₀ | true => β₁.1) false

open Classical in
/-- Worst-case expected loss `⨆ β₀, T.evalBehavior (false => β₀, true => β₁) false` over all
behavioral strategies `β₀` of player `false`. -/
noncomputable def ExtensiveTree.behaviorUpperVal [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (β₁ : ∀ h : H true, Act true h → ℝ) : ℝ :=
  ⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
    T.evalBehavior (fun | false => β₀.1 | true => β₁) false

open Classical in
/-- Under perfect recall for player `true`, behavioral lower value equals the sequence-form lower
value of the induced realization plan `T.behaviorToRealizationPlan false β₀`. -/
theorem behaviorLowerVal_eq_seqLowerVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H true)]
    (hpr : T.PerfectRecall true) (β₀ : ∀ h : H false, Act false h → ℝ) :
    T.behaviorLowerVal β₀ = T.seqLowerVal (T.behaviorToRealizationPlan false β₀) := by
  have hleast := isLeast_seqLowerVal hpr (T.behaviorToRealizationPlan false β₀)
  obtain ⟨yStar, hyStar, hyStar_eq⟩ := hleast.1
  let βStar := T.realizationPlanToBehavior true hpr yStar
  have hβStar : IsBehaviorStrategy βStar := isBehaviorStrategy_realizationPlanToBehavior hpr hyStar
  have hyStar_plan : T.behaviorToRealizationPlan true βStar = yStar :=
    behaviorToRealizationPlan_realizationPlanToBehavior hpr hyStar
  have heval_star : T.evalBehavior (fun | false => β₀ | true => βStar) false =
      T.seqLowerVal (T.behaviorToRealizationPlan false β₀) := by
    rw [evalBehavior_eq_seqPayoffMat]
    simpa [hyStar_plan] using hyStar_eq
  have hbdd : BddBelow (Set.range fun β₁ : {β₁ // IsBehaviorStrategy β₁} =>
      T.evalBehavior (fun | false => β₀ | true => β₁.1) false) := by
    refine ⟨T.seqLowerVal (T.behaviorToRealizationPlan false β₀), ?_⟩
    rintro _ ⟨⟨β₁, hβ₁⟩, rfl⟩
    dsimp only
    rw [evalBehavior_eq_seqPayoffMat]
    exact seqLowerVal_le hpr _ (isRealizationPlan_behaviorToRealizationPlan hpr hβ₁)
  let _ : Nonempty {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁} := ⟨⟨βStar, hβStar⟩⟩
  refine le_antisymm ((ciInf_le hbdd ⟨βStar, hβStar⟩).trans_eq heval_star) (le_ciInf ?_)
  rintro ⟨β₁, hβ₁⟩
  dsimp only
  rw [evalBehavior_eq_seqPayoffMat]
  exact seqLowerVal_le hpr _ (isRealizationPlan_behaviorToRealizationPlan hpr hβ₁)

open Classical in
/-- Under perfect recall for player `false`, behavioral upper value equals the sequence-form upper
value of the induced realization plan `T.behaviorToRealizationPlan true β₁`. -/
theorem behaviorUpperVal_eq_seqUpperVal [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)]
    (hpr : T.PerfectRecall false) (β₁ : ∀ h : H true, Act true h → ℝ) :
    T.behaviorUpperVal β₁ = T.seqUpperVal (T.behaviorToRealizationPlan true β₁) := by
  have hgreat := isGreatest_seqUpperVal hpr (T.behaviorToRealizationPlan true β₁)
  obtain ⟨xStar, hxStar, hxStar_eq⟩ := hgreat.1
  let βStar := T.realizationPlanToBehavior false hpr xStar
  have hβStar : IsBehaviorStrategy βStar := isBehaviorStrategy_realizationPlanToBehavior hpr hxStar
  have hxStar_plan : T.behaviorToRealizationPlan false βStar = xStar :=
    behaviorToRealizationPlan_realizationPlanToBehavior hpr hxStar
  have heval_star : T.evalBehavior (fun | false => βStar | true => β₁) false =
      T.seqUpperVal (T.behaviorToRealizationPlan true β₁) := by
    rw [evalBehavior_eq_seqPayoffMat]
    simpa [hxStar_plan] using hxStar_eq
  have hbdd : BddAbove (Set.range fun β₀ : {β₀ // IsBehaviorStrategy β₀} =>
      T.evalBehavior (fun | false => β₀.1 | true => β₁) false) := by
    refine ⟨T.seqUpperVal (T.behaviorToRealizationPlan true β₁), ?_⟩
    rintro _ ⟨⟨β₀, hβ₀⟩, rfl⟩
    dsimp only
    rw [evalBehavior_eq_seqPayoffMat]
    exact le_seqUpperVal hpr _ (isRealizationPlan_behaviorToRealizationPlan hpr hβ₀)
  let _ : Nonempty {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀} :=
    ⟨⟨βStar, hβStar⟩⟩
  refine le_antisymm (ciSup_le ?_) (heval_star.symm.trans_le (le_ciSup hbdd ⟨βStar, hβStar⟩))
  rintro ⟨β₀, hβ₀⟩
  dsimp only
  rw [evalBehavior_eq_seqPayoffMat]
  exact le_seqUpperVal hpr _ (isRealizationPlan_behaviorToRealizationPlan hpr hβ₀)

namespace ExtensiveTree.IsZeroSum

open Classical in
/-- **Behavioral minimax equality** ([vonStengel2007], §3.10): in a zero-sum extensive game with
perfect recall, maximizing the worst-case payoff over behavioral strategies equals minimizing the
opponent's worst-case loss. -/
theorem behavior_iSup_iInf_eq_iInf_iSup [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
        ⨅ β₁ : {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁},
          T.evalBehavior (fun | false => β₀.1 | true => β₁.1) false) =
      ⨅ β₁ : {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁},
        ⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
          T.evalBehavior (fun | false => β₀.1 | true => β₁.1) false := by
  have hmin :
      (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
          T.behaviorLowerVal β₀.1) =
        ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x}, T.seqLowerVal x.1 := by
    have hfn : (fun β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀} =>
          T.behaviorLowerVal β₀.1) =
        fun β₀ => T.seqLowerVal (T.behaviorToRealizationPlan false β₀.1) := by
      ext β₀
      exact behaviorLowerVal_eq_seqLowerVal (hpr true) β₀.1
    rw [hfn]
    obtain ⟨v, ⟨⟨xStar, hxStar, hxStar_eq⟩, hmax⟩, _⟩ := hzs.seq_minimax_duality hpr
    let βStar := T.realizationPlanToBehavior false (hpr false) xStar
    have hβStar : IsBehaviorStrategy βStar :=
      isBehaviorStrategy_realizationPlanToBehavior (hpr false) hxStar
    have hxStar_plan : T.behaviorToRealizationPlan false βStar = xStar :=
      behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hxStar
    let _ : Nonempty {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀} :=
      ⟨⟨βStar, hβStar⟩⟩
    let _ : Nonempty {x : SeqVar T false → ℝ // T.IsRealizationPlan false x} := ⟨⟨xStar, hxStar⟩⟩
    have hbdd_b : BddAbove (Set.range fun β₀ : {β₀ // IsBehaviorStrategy β₀} =>
        T.seqLowerVal (T.behaviorToRealizationPlan false β₀.1)) :=
      ⟨v, by
        rintro _ ⟨⟨β₀, hβ₀⟩, rfl⟩
        exact hmax ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ₀, rfl⟩⟩
    have hbdd_s : BddAbove (Set.range fun x : {x // T.IsRealizationPlan false x} =>
        T.seqLowerVal x.1) :=
      ⟨v, by rintro _ ⟨⟨x, hx⟩, rfl⟩; exact hmax ⟨x, hx, rfl⟩⟩
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun ⟨β₀, hβ₀⟩ => ?_
      exact le_ciSup hbdd_s ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ₀⟩
    · refine ciSup_le fun ⟨x, hx⟩ => ?_
      exact (hmax ⟨x, hx, rfl⟩).trans
        (hxStar_eq.symm.trans_le (hxStar_plan ▸ le_ciSup hbdd_b ⟨βStar, hβStar⟩))
  have hmax :
      (⨅ β₁ : {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁},
          T.behaviorUpperVal β₁.1) =
        ⨅ y : {y : SeqVar T true → ℝ // T.IsRealizationPlan true y}, T.seqUpperVal y.1 := by
    have hfn : (fun β₁ : {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁} =>
          T.behaviorUpperVal β₁.1) =
        fun β₁ => T.seqUpperVal (T.behaviorToRealizationPlan true β₁.1) := by
      ext β₁
      exact behaviorUpperVal_eq_seqUpperVal (hpr false) β₁.1
    rw [hfn]
    obtain ⟨v, _, ⟨⟨yStar, hyStar, hyStar_eq⟩, hmin'⟩, _⟩ := hzs.seq_minimax_duality hpr
    let βStar := T.realizationPlanToBehavior true (hpr true) yStar
    have hβStar : IsBehaviorStrategy βStar :=
      isBehaviorStrategy_realizationPlanToBehavior (hpr true) hyStar
    have hyStar_plan : T.behaviorToRealizationPlan true βStar = yStar :=
      behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hyStar
    let _ : Nonempty {β₁ : ∀ h : H true, Act true h → ℝ // IsBehaviorStrategy β₁} :=
      ⟨⟨βStar, hβStar⟩⟩
    let _ : Nonempty {y : SeqVar T true → ℝ // T.IsRealizationPlan true y} := ⟨⟨yStar, hyStar⟩⟩
    have hbdd_b : BddBelow (Set.range fun β₁ : {β₁ // IsBehaviorStrategy β₁} =>
        T.seqUpperVal (T.behaviorToRealizationPlan true β₁.1)) :=
      ⟨v, by
        rintro _ ⟨⟨β₁, hβ₁⟩, rfl⟩
        exact hmin' ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ₁, rfl⟩⟩
    have hbdd_s : BddBelow (Set.range fun y : {y // T.IsRealizationPlan true y} =>
        T.seqUpperVal y.1) :=
      ⟨v, by rintro _ ⟨⟨y, hy⟩, rfl⟩; exact hmin' ⟨y, hy, rfl⟩⟩
    refine le_antisymm ?_ ?_
    · refine le_ciInf fun ⟨y, hy⟩ => ?_
      exact ((ciInf_le hbdd_b ⟨βStar, hβStar⟩).trans_eq (by rw [hyStar_plan, hyStar_eq])).trans
        (hmin' ⟨y, hy, rfl⟩)
    · refine le_ciInf fun ⟨β₁, hβ₁⟩ => ?_
      exact ciInf_le hbdd_s ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ₁⟩
  change (⨆ β₀ : {β₀ // IsBehaviorStrategy β₀}, T.behaviorLowerVal β₀.1) =
    ⨅ β₁ : {β₁ // IsBehaviorStrategy β₁}, T.behaviorUpperVal β₁.1
  rw [hmin, hmax]
  exact hzs.seq_iSup_iInf_eq_iInf_iSup hpr

open Classical in
/-- The behavioral maximin value equals the sequence-form LP maximin value. -/
theorem behavior_minimax_eq_seq_minimax [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
        T.behaviorLowerVal β₀.1) =
      ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x}, T.seqLowerVal x.1 := by
  let _ : ∀ i, Finite (H i) := fun | false => inferInstance | true => inferInstance
  obtain ⟨β, hβ_nash⟩ := exists_isBehaviorNash hpr
  obtain ⟨_, hseq_nash⟩ := (isBehaviorNash_iff_isSeqNash hpr β).1 hβ_nash
  obtain ⟨_, h0, _⟩ := (hzs.isBehaviorNash_iff_saddlePoint β).1 hβ_nash
  obtain ⟨hbeh, _⟩ := (isBehaviorNash_iff_isSeqNash hpr β).1 hβ_nash
  have hlo_eq : T.behaviorLowerVal (β false) = T.evalBehavior β false := by
    rw [behaviorLowerVal_eq_seqLowerVal (hpr true)]
    have hseq_mm := (hzs.isSeqNash_iff_saddlePoint hpr _ _).1 hseq_nash
    rw [evalBehavior_eq_seqPayoffMat T β false]
    refine le_antisymm ?_ (le_seqLowerVal (hpr true) fun y' hy' => ?_)
    · exact seqLowerVal_le (hpr true) _
        (isRealizationPlan_behaviorToRealizationPlan (hpr true) (hbeh true))
    · exact hseq_mm.2.2.2 y' hy'
  let _ : Nonempty {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀} :=
    ⟨⟨β false, hbeh false⟩⟩
  have hbdd : BddAbove (Set.range fun β₀ : {β₀ // IsBehaviorStrategy β₀} =>
      T.behaviorLowerVal β₀.1) := by
    refine ⟨T.evalBehavior β false, ?_⟩
    rintro _ ⟨⟨β₀, hβ₀⟩, rfl⟩
    dsimp only
    rw [behaviorLowerVal_eq_seqLowerVal (hpr true)]
    refine (seqLowerVal_le (hpr true) _ (isRealizationPlan_behaviorToRealizationPlan (hpr true)
      (hbeh true))).trans ?_
    rw [← evalBehavior_eq_seqPayoffMat T (fun | false => β₀ | true => β true) false]
    exact h0 β₀ hβ₀
  have hsup : (⨆ β₀ : {β₀ // IsBehaviorStrategy β₀}, T.behaviorLowerVal β₀.1) =
      T.evalBehavior β false :=
    le_antisymm
      (ciSup_le fun ⟨β₀, hβ₀⟩ => by
        dsimp only
        rw [behaviorLowerVal_eq_seqLowerVal (hpr true)]
        refine (seqLowerVal_le (hpr true) _ (isRealizationPlan_behaviorToRealizationPlan (hpr true)
          (hbeh true))).trans ?_
        rw [← evalBehavior_eq_seqPayoffMat T (fun | false => β₀ | true => β true) false]
        exact h0 β₀ hβ₀)
      (hlo_eq.symm.trans_le (le_ciSup hbdd ⟨β false, hbeh false⟩))
  rw [hsup, evalBehavior_eq_seqPayoffMat, (hseq_nash.payoff_eq hpr hzs).1]

open Classical in
/-- **Maximin/minimax characterization of behavioral Nash equilibria** in two-player zero-sum
extensive games with perfect recall: `β` is a behavioral Nash equilibrium iff `β false` maximizes
`T.behaviorLowerVal` and `β true` minimizes `T.behaviorUpperVal`. -/
theorem isBehaviorNash_iff_maximin_minimax [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    T.IsBehaviorNash β ↔
      (IsBehaviorStrategy (β false) ∧
        IsGreatest (T.behaviorLowerVal '' {β₀ | IsBehaviorStrategy β₀})
          (T.behaviorLowerVal (β false))) ∧
      (IsBehaviorStrategy (β true) ∧
        IsLeast (T.behaviorUpperVal '' {β₁ | IsBehaviorStrategy β₁})
          (T.behaviorUpperVal (β true))) := by
  have hval_lo : T.behaviorLowerVal (β false) =
      T.seqLowerVal (T.behaviorToRealizationPlan false (β false)) :=
    behaviorLowerVal_eq_seqLowerVal (hpr true) (β false)
  have hval_up : T.behaviorUpperVal (β true) =
      T.seqUpperVal (T.behaviorToRealizationPlan true (β true)) :=
    behaviorUpperVal_eq_seqUpperVal (hpr false) (β true)
  have himg_lo : (T.behaviorLowerVal '' {β₀ | IsBehaviorStrategy β₀}) =
      (T.seqLowerVal '' {x | T.IsRealizationPlan false x}) := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨β₀, hβ₀, rfl⟩
      exact ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ₀,
        (behaviorLowerVal_eq_seqLowerVal (hpr true) β₀).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨T.realizationPlanToBehavior false (hpr false) x,
        isBehaviorStrategy_realizationPlanToBehavior (hpr false) hx,
        by rw [behaviorLowerVal_eq_seqLowerVal (hpr true),
          behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hx]⟩
  have himg_up : (T.behaviorUpperVal '' {β₁ | IsBehaviorStrategy β₁}) =
      (T.seqUpperVal '' {y | T.IsRealizationPlan true y}) := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨β₁, hβ₁, rfl⟩
      exact ⟨_, isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ₁,
        (behaviorUpperVal_eq_seqUpperVal (hpr false) β₁).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨T.realizationPlanToBehavior true (hpr true) y,
        isBehaviorStrategy_realizationPlanToBehavior (hpr true) hy,
        by rw [behaviorUpperVal_eq_seqUpperVal (hpr false),
          behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hy]⟩
  rw [isBehaviorNash_iff_isSeqNash hpr, hzs.isSeqNash_iff_maximin_minimax hpr,
    hval_lo, hval_up, himg_lo, himg_up]
  constructor
  · rintro ⟨hbeh, ⟨_, hx_max⟩, ⟨_, hy_min⟩⟩
    exact ⟨⟨hbeh false, hx_max⟩, ⟨hbeh true, hy_min⟩⟩
  · rintro ⟨⟨hβ₀, hx_max⟩, ⟨hβ₁, hy_min⟩⟩
    have hbeh : ∀ i, IsBehaviorStrategy (β i) := fun | false => hβ₀ | true => hβ₁
    exact ⟨hbeh,
      ⟨isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ₀, hx_max⟩,
      ⟨isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ₁, hy_min⟩⟩

end ExtensiveTree.IsZeroSum

namespace ExtensiveTree.IsBehaviorNash

open Classical in
/-- Every behavioral Nash equilibrium in a zero-sum game with perfect recall realizes both the
behavioral and sequence-form minimax game value. -/
theorem evalBehavior_eq [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {β : ∀ i, ∀ h : H i, Act i h → ℝ} (hβ : T.IsBehaviorNash β) :
    T.evalBehavior β false =
        (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
          T.behaviorLowerVal β₀.1) ∧
      T.evalBehavior β false =
        (⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
          T.seqLowerVal x.1) := by
  obtain ⟨_, hseq⟩ := (isBehaviorNash_iff_isSeqNash hpr β).1 hβ
  have heq : T.evalBehavior β false =
      ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x}, T.seqLowerVal x.1 := by
    rw [evalBehavior_eq_seqPayoffMat]
    exact (hseq.payoff_eq hpr hzs).1
  exact ⟨heq.trans (hzs.behavior_minimax_eq_seq_minimax hpr).symm, heq⟩

open Classical in
/-- **Interchangeability of behavioral Nash equilibria** in two-player zero-sum extensive games
with perfect recall: combining player `false`'s strategy from `β₁` with player `true`'s strategy
from `β₂` produces another behavioral Nash equilibrium with the same expected payoff. -/
theorem interchange [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {β₁ β₂ : ∀ i, ∀ h : H i, Act i h → ℝ}
    (h₁ : T.IsBehaviorNash β₁) (h₂ : T.IsBehaviorNash β₂) :
    T.IsBehaviorNash (fun | false => β₁ false | true => β₂ true) ∧
      T.evalBehavior (fun | false => β₁ false | true => β₂ true) false =
        T.evalBehavior β₁ false := by
  obtain ⟨hbeh₁, hseq₁⟩ := (isBehaviorNash_iff_isSeqNash hpr β₁).1 h₁
  obtain ⟨hbeh₂, hseq₂⟩ := (isBehaviorNash_iff_isSeqNash hpr β₂).1 h₂
  obtain ⟨hseq_int, hval_int⟩ := hseq₁.interchange hpr hzs hseq₂
  let β : ∀ i, ∀ h : H i, Act i h → ℝ := fun | false => β₁ false | true => β₂ true
  have hbeh : ∀ i, IsBehaviorStrategy (β i) := fun | false => hbeh₁ false | true => hbeh₂ true
  refine ⟨(isBehaviorNash_iff_isSeqNash hpr β).2 ⟨hbeh, hseq_int⟩, ?_⟩
  rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat]
  exact hval_int

end ExtensiveTree.IsBehaviorNash

namespace ExtensiveTree.IsZeroSum

open Classical in
/-- **Saddle-point certificate for finite extensive games**: checking that `β` consists of valid
behavior strategies and forms a saddle point around `v` immediately yields `T.IsBehaviorNash β`,
`T.IsSeqNash` for its realization plans, `T.evalBehavior β false = v`, and exact equality with
both behavioral and sequence-form minimax values. -/
theorem isBehaviorNash_of_saddle [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {β : ∀ i, ∀ h : H i, Act i h → ℝ} (v : ℝ)
    (hbeh : ∀ i, IsBehaviorStrategy (β i))
    (hup : ∀ β₀ : ∀ h : H false, Act false h → ℝ, IsBehaviorStrategy β₀ →
      T.evalBehavior (fun | false => β₀ | true => β true) false ≤ v)
    (hlo : ∀ β₁ : ∀ h : H true, Act true h → ℝ, IsBehaviorStrategy β₁ →
      v ≤ T.evalBehavior (fun | false => β false | true => β₁) false) :
    T.IsBehaviorNash β ∧
      T.IsSeqNash (T.behaviorToRealizationPlan false (β false))
        (T.behaviorToRealizationPlan true (β true)) ∧
      T.evalBehavior β false = v ∧
      (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
        T.behaviorLowerVal β₀.1) = v ∧
      (⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
        T.seqLowerVal x.1) = v := by
  have heq_prof : T.evalBehavior (fun | false => β false | true => β true) false =
      T.evalBehavior β false :=
    congrArg (fun f => T.evalBehavior f false) (bool_profile_eq β)
  have hev_le : T.evalBehavior β false ≤ v := heq_prof ▸ hup (β false) (hbeh false)
  have hle_ev : v ≤ T.evalBehavior β false := heq_prof ▸ hlo (β true) (hbeh true)
  have hev : T.evalBehavior β false = v := le_antisymm hev_le hle_ev
  have hnash : T.IsBehaviorNash β := (hzs.isBehaviorNash_iff_saddlePoint β).2
    ⟨hbeh, fun β₀ hβ₀ => hev.symm ▸ hup β₀ hβ₀, fun β₁ hβ₁ => hev.symm ▸ hlo β₁ hβ₁⟩
  have hseq : T.IsSeqNash (T.behaviorToRealizationPlan false (β false))
      (T.behaviorToRealizationPlan true (β true)) :=
    ((isBehaviorNash_iff_isSeqNash hpr β).1 hnash).2
  obtain ⟨hvb, hvs⟩ := hnash.evalBehavior_eq hpr hzs
  exact ⟨hnash, hseq, hev, hvb.symm.trans hev, hvs.symm.trans hev⟩

end ExtensiveTree.IsZeroSum

open Classical in
/-- Relating mixed realization plans to behavioral realization plans (`behaviorToMixed`): under
perfect recall, the product mixed strategy `behaviorToMixed β` induces the same realization plan
as `β`. -/
theorem mixedToRealizationPlan_behaviorToMixed {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} [DecidableEq ι] [∀ j, Fintype (H j)]
    [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β) :
    T.mixedToRealizationPlan i (behaviorToMixed β) = T.behaviorToRealizationPlan i β := by
  ext σ
  obtain ⟨z, _, hz⟩ := σ.2
  have hzn := hpr.noRepeatedInfoSet z
  rw [← hz, List.map_append] at hzn
  rw [ExtensiveTree.mixedToRealizationPlan_def]
  exact realizationProbMixed_behaviorToMixed hβ (List.Nodup.of_append_left hzn)

open Classical in
/-- Worst-case expected payoff `⨅ μ₁, T.evalMixed (false => μ₀, true => μ₁) false` over all
mixed strategies `μ₁` of player `true`. -/
noncomputable def ExtensiveTree.mixedLowerVal [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] (T : ExtensiveTree Bool H Act)
    (μ₀ : PureStrategy H Act false → ℝ) : ℝ :=
  ⨅ μ₁ : {μ₁ : PureStrategy H Act true → ℝ // IsMixedStrategy μ₁},
    T.evalMixed (fun | false => μ₀ | true => μ₁.1) false

open Classical in
/-- Worst-case expected loss `⨆ μ₀, T.evalMixed (false => μ₀, true => μ₁) false` over all mixed
strategies `μ₀` of player `false`. -/
noncomputable def ExtensiveTree.mixedUpperVal [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] (T : ExtensiveTree Bool H Act)
    (μ₁ : PureStrategy H Act true → ℝ) : ℝ :=
  ⨆ μ₀ : {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀},
    T.evalMixed (fun | false => μ₀.1 | true => μ₁) false

open Classical in
/-- Under perfect recall for player `true`, mixed lower value equals the sequence-form lower value
of `T.mixedToRealizationPlan false μ₀`. -/
theorem mixedLowerVal_eq_seqLowerVal [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : T.PerfectRecall true)
    (μ₀ : PureStrategy H Act false → ℝ) :
    T.mixedLowerVal μ₀ = T.seqLowerVal (T.mixedToRealizationPlan false μ₀) := by
  have hleast := isLeast_seqLowerVal hpr (T.mixedToRealizationPlan false μ₀)
  obtain ⟨yStar, hyStar, hyStar_eq⟩ := hleast.1
  let βStar := T.realizationPlanToBehavior true hpr yStar
  have hβStar : IsBehaviorStrategy βStar := isBehaviorStrategy_realizationPlanToBehavior hpr hyStar
  let μStar := behaviorToMixed βStar
  have hμStar : IsMixedStrategy μStar := isMixedStrategy_behaviorToMixed hβStar
  have hyStar_plan : T.mixedToRealizationPlan true μStar = yStar := by
    rw [mixedToRealizationPlan_behaviorToMixed hpr hβStar,
      behaviorToRealizationPlan_realizationPlanToBehavior hpr hyStar]
  have heval_star : T.evalMixed (fun | false => μ₀ | true => μStar) false =
      T.seqLowerVal (T.mixedToRealizationPlan false μ₀) := by
    rw [evalMixed_eq_seqPayoffMat]
    simpa [hyStar_plan] using hyStar_eq
  have hbdd : BddBelow (Set.range fun μ₁ : {μ₁ // IsMixedStrategy μ₁} =>
      T.evalMixed (fun | false => μ₀ | true => μ₁.1) false) := by
    refine ⟨T.seqLowerVal (T.mixedToRealizationPlan false μ₀), ?_⟩
    rintro _ ⟨⟨μ₁, hμ₁⟩, rfl⟩
    dsimp only
    rw [evalMixed_eq_seqPayoffMat]
    exact seqLowerVal_le hpr _ (isRealizationPlan_mixedToRealizationPlan hpr hμ₁)
  let _ : Nonempty {μ₁ : PureStrategy H Act true → ℝ // IsMixedStrategy μ₁} := ⟨⟨μStar, hμStar⟩⟩
  refine le_antisymm ((ciInf_le hbdd ⟨μStar, hμStar⟩).trans_eq heval_star) (le_ciInf ?_)
  rintro ⟨μ₁, hμ₁⟩
  dsimp only
  rw [evalMixed_eq_seqPayoffMat]
  exact seqLowerVal_le hpr _ (isRealizationPlan_mixedToRealizationPlan hpr hμ₁)

open Classical in
/-- Under perfect recall for player `false`, mixed upper value equals the sequence-form upper value
of `T.mixedToRealizationPlan true μ₁`. -/
theorem mixedUpperVal_eq_seqUpperVal [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : T.PerfectRecall false)
    (μ₁ : PureStrategy H Act true → ℝ) :
    T.mixedUpperVal μ₁ = T.seqUpperVal (T.mixedToRealizationPlan true μ₁) := by
  have hgreat := isGreatest_seqUpperVal hpr (T.mixedToRealizationPlan true μ₁)
  obtain ⟨xStar, hxStar, hxStar_eq⟩ := hgreat.1
  let βStar := T.realizationPlanToBehavior false hpr xStar
  have hβStar : IsBehaviorStrategy βStar := isBehaviorStrategy_realizationPlanToBehavior hpr hxStar
  let μStar := behaviorToMixed βStar
  have hμStar : IsMixedStrategy μStar := isMixedStrategy_behaviorToMixed hβStar
  have hxStar_plan : T.mixedToRealizationPlan false μStar = xStar := by
    rw [mixedToRealizationPlan_behaviorToMixed hpr hβStar,
      behaviorToRealizationPlan_realizationPlanToBehavior hpr hxStar]
  have heval_star : T.evalMixed (fun | false => μStar | true => μ₁) false =
      T.seqUpperVal (T.mixedToRealizationPlan true μ₁) := by
    rw [evalMixed_eq_seqPayoffMat]
    simpa [hxStar_plan] using hxStar_eq
  have hbdd : BddAbove (Set.range fun μ₀ : {μ₀ // IsMixedStrategy μ₀} =>
      T.evalMixed (fun | false => μ₀.1 | true => μ₁) false) := by
    refine ⟨T.seqUpperVal (T.mixedToRealizationPlan true μ₁), ?_⟩
    rintro _ ⟨⟨μ₀, hμ₀⟩, rfl⟩
    dsimp only
    rw [evalMixed_eq_seqPayoffMat]
    exact le_seqUpperVal hpr _ (isRealizationPlan_mixedToRealizationPlan hpr hμ₀)
  let _ : Nonempty {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀} := ⟨⟨μStar, hμStar⟩⟩
  refine le_antisymm (ciSup_le ?_) (heval_star.symm.trans_le (le_ciSup hbdd ⟨μStar, hμStar⟩))
  rintro ⟨μ₀, hμ₀⟩
  dsimp only
  rw [evalMixed_eq_seqPayoffMat]
  exact le_seqUpperVal hpr _ (isRealizationPlan_mixedToRealizationPlan hpr hμ₀)

namespace ExtensiveTree.IsZeroSum

open Classical in
/-- **Mixed minimax equality** in a zero-sum extensive game with perfect recall: mixed maximin
equals mixed minimax, matching the sequence-form and behavioral minimax values. -/
theorem mixed_iSup_iInf_eq_iInf_iSup [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    (⨆ μ₀ : {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀},
        ⨅ μ₁ : {μ₁ : PureStrategy H Act true → ℝ // IsMixedStrategy μ₁},
          T.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false) =
      ⨅ μ₁ : {μ₁ : PureStrategy H Act true → ℝ // IsMixedStrategy μ₁},
        ⨆ μ₀ : {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀},
          T.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false := by
  obtain ⟨v, ⟨⟨x₀, hx₀, hx₀_eq⟩, hmax⟩, ⟨⟨y₀, hy₀, hy₀_eq⟩, hmin⟩, _⟩ :=
    hzs.seq_minimax_duality hpr
  have h_lift : ∀ (i : Bool) (x : SeqVar T i → ℝ), T.IsRealizationPlan i x →
      IsMixedStrategy (behaviorToMixed (T.realizationPlanToBehavior i (hpr i) x)) ∧
        T.mixedToRealizationPlan i (behaviorToMixed (T.realizationPlanToBehavior i (hpr i) x)) =
          x := fun i x hx => by
    have hβ := isBehaviorStrategy_realizationPlanToBehavior (hpr i) hx
    exact ⟨isMixedStrategy_behaviorToMixed hβ,
      (mixedToRealizationPlan_behaviorToMixed (hpr i) hβ).trans
        (behaviorToRealizationPlan_realizationPlanToBehavior (hpr i) hx)⟩
  obtain ⟨hμ₀Star, hx₀_plan⟩ := h_lift false x₀ hx₀
  obtain ⟨hμ₁Star, hy₀_plan⟩ := h_lift true y₀ hy₀
  let μ₀Star := behaviorToMixed (T.realizationPlanToBehavior false (hpr false) x₀)
  let μ₁Star := behaviorToMixed (T.realizationPlanToBehavior true (hpr true) y₀)
  let _ : Nonempty {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀} := ⟨⟨μ₀Star, hμ₀Star⟩⟩
  let _ : Nonempty {μ₁ : PureStrategy H Act true → ℝ // IsMixedStrategy μ₁} := ⟨⟨μ₁Star, hμ₁Star⟩⟩
  have hfn_lo : (fun μ₀ : {μ₀ // IsMixedStrategy μ₀} => T.mixedLowerVal μ₀.1) =
      fun μ₀ => T.seqLowerVal (T.mixedToRealizationPlan false μ₀.1) := by
    ext μ₀; exact mixedLowerVal_eq_seqLowerVal (hpr true) μ₀.1
  have hfn_up : (fun μ₁ : {μ₁ // IsMixedStrategy μ₁} => T.mixedUpperVal μ₁.1) =
      fun μ₁ => T.seqUpperVal (T.mixedToRealizationPlan true μ₁.1) := by
    ext μ₁; exact mixedUpperVal_eq_seqUpperVal (hpr false) μ₁.1
  have hbdd_lo : BddAbove (Set.range fun μ₀ : {μ₀ // IsMixedStrategy μ₀} =>
      T.mixedLowerVal μ₀.1) := by
    rw [hfn_lo]
    exact ⟨v, by rintro _ ⟨⟨μ₀, hμ₀⟩, rfl⟩; exact hmax ⟨_, isRealizationPlan_mixedToRealizationPlan
      (hpr false) hμ₀, rfl⟩⟩
  have hbdd_up : BddBelow (Set.range fun μ₁ : {μ₁ // IsMixedStrategy μ₁} =>
      T.mixedUpperVal μ₁.1) := by
    rw [hfn_up]
    exact ⟨v, by rintro _ ⟨⟨μ₁, hμ₁⟩, rfl⟩; exact hmin ⟨_, isRealizationPlan_mixedToRealizationPlan
      (hpr true) hμ₁, rfl⟩⟩
  have hleft : (⨆ μ₀ : {μ₀ // IsMixedStrategy μ₀}, T.mixedLowerVal μ₀.1) = v := by
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun ⟨μ₀, hμ₀⟩ => ?_
      dsimp only
      rw [mixedLowerVal_eq_seqLowerVal (hpr true)]
      exact hmax ⟨_, isRealizationPlan_mixedToRealizationPlan (hpr false) hμ₀, rfl⟩
    · have h_eq : v = T.mixedLowerVal μ₀Star := by
        rw [mixedLowerVal_eq_seqLowerVal (hpr true), hx₀_plan, hx₀_eq]
      exact h_eq.trans_le (le_ciSup hbdd_lo ⟨μ₀Star, hμ₀Star⟩)
  have hright : (⨅ μ₁ : {μ₁ // IsMixedStrategy μ₁}, T.mixedUpperVal μ₁.1) = v := by
    refine le_antisymm ?_ ?_
    · refine (ciInf_le hbdd_up ⟨μ₁Star, hμ₁Star⟩).trans_eq ?_
      dsimp only
      rw [mixedUpperVal_eq_seqUpperVal (hpr false), hy₀_plan, hy₀_eq]
    · refine le_ciInf fun ⟨μ₁, hμ₁⟩ => ?_
      dsimp only
      rw [mixedUpperVal_eq_seqUpperVal (hpr false)]
      exact hmin ⟨_, isRealizationPlan_mixedToRealizationPlan (hpr true) hμ₁, rfl⟩
  change (⨆ μ₀ : {μ₀ // IsMixedStrategy μ₀}, T.mixedLowerVal μ₀.1) =
    ⨅ μ₁ : {μ₁ // IsMixedStrategy μ₁}, T.mixedUpperVal μ₁.1
  rw [hleft, hright]

open Classical in
/-- The mixed maximin value equals both the behavioral and sequence-form maximin values. -/
theorem mixed_minimax_eq_behavior_minimax [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    (⨆ μ₀ : {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀},
        T.mixedLowerVal μ₀.1) =
      ⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
        T.behaviorLowerVal β₀.1 := by
  obtain ⟨μ, hμ⟩ := CostGame.exists_isMixedNash (G := T.toCostGame)
  obtain ⟨hmix, hseq⟩ := (isMixedNash_toCostGame_iff_isSeqNash hpr μ).1 hμ
  let _ : Nonempty {μ₀ : PureStrategy H Act false → ℝ // IsMixedStrategy μ₀} :=
    ⟨⟨μ false, hmix false⟩⟩
  have hlo : T.mixedLowerVal (μ false) = T.evalMixed μ false := by
    rw [mixedLowerVal_eq_seqLowerVal (hpr true), evalMixed_eq_seqPayoffMat]
    have hss := (hzs.isSeqNash_iff_saddlePoint hpr _ _).1 hseq
    exact le_antisymm (seqLowerVal_le (hpr true) _ (isRealizationPlan_mixedToRealizationPlan
      (hpr true) (hmix true))) (le_seqLowerVal (hpr true) hss.2.2.2)
  have hbdd : BddAbove (Set.range fun μ₀ : {μ₀ // IsMixedStrategy μ₀} => T.mixedLowerVal μ₀.1) := by
    refine ⟨T.evalMixed μ false, ?_⟩
    rintro _ ⟨⟨μ₀, hμ₀⟩, rfl⟩
    dsimp only
    rw [mixedLowerVal_eq_seqLowerVal (hpr true)]
    refine (seqLowerVal_le (hpr true) _ (isRealizationPlan_mixedToRealizationPlan (hpr true)
      (hmix true))).trans ?_
    have hss := (hzs.isSeqNash_iff_saddlePoint hpr _ _).1 hseq
    rw [evalMixed_eq_seqPayoffMat]
    exact hss.2.2.1 _ (isRealizationPlan_mixedToRealizationPlan (hpr false) hμ₀)
  have hsup : (⨆ μ₀ : {μ₀ // IsMixedStrategy μ₀}, T.mixedLowerVal μ₀.1) = T.evalMixed μ false :=
    le_antisymm
      (ciSup_le fun ⟨μ₀, hμ₀⟩ => by
        dsimp only
        rw [mixedLowerVal_eq_seqLowerVal (hpr true)]
        refine (seqLowerVal_le (hpr true) _ (isRealizationPlan_mixedToRealizationPlan (hpr true)
          (hmix true))).trans ?_
        have hss := (hzs.isSeqNash_iff_saddlePoint hpr _ _).1 hseq
        rw [evalMixed_eq_seqPayoffMat]
        exact hss.2.2.1 _ (isRealizationPlan_mixedToRealizationPlan (hpr false) hμ₀))
      (hlo.symm.trans_le (le_ciSup hbdd ⟨μ false, hmix false⟩))
  rw [hsup, evalMixed_eq_seqPayoffMat, (hseq.payoff_eq hpr hzs).1,
    hzs.behavior_minimax_eq_seq_minimax hpr]

open Classical in
/-- Every mixed Nash equilibrium of `T.toCostGame` in a two-player zero-sum extensive game with
perfect recall attains the sequence-form and behavioral minimax value. -/
theorem isMixedNash_evalMixed_eq [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum)
    {μ : ∀ i, PureStrategy H Act i → ℝ} (hμ : T.toCostGame.IsMixedNash μ) :
    T.evalMixed μ false =
        (⨆ β₀ : {β₀ : ∀ h : H false, Act false h → ℝ // IsBehaviorStrategy β₀},
          T.behaviorLowerVal β₀.1) ∧
      T.evalMixed μ false =
        ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x},
          T.seqLowerVal x.1 := by
  obtain ⟨_, hseq⟩ := (isMixedNash_toCostGame_iff_isSeqNash hpr μ).1 hμ
  have heq : T.evalMixed μ false =
      ⨆ x : {x : SeqVar T false → ℝ // T.IsRealizationPlan false x}, T.seqLowerVal x.1 := by
    rw [evalMixed_eq_seqPayoffMat]
    exact (hseq.payoff_eq hpr hzs).1
  exact ⟨heq.trans (hzs.behavior_minimax_eq_seq_minimax hpr).symm, heq⟩

end ExtensiveTree.IsZeroSum

end BehavioralAndMixedMinimax

section PerfectInfoZeroSumBridge

open Classical in
/-- Expected payoff of a pure strategy profile realized as deterministic behavioral strategies
`fun i => pureToBehavior (s i)` equals `T.evalPure s`. -/
theorem ExtensiveTree.evalBehavior_pureToBehavior {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} [∀ i h, Fintype (Act i h)] [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) :
    ∀ (T : ExtensiveTree ι H Act),
      T.evalBehavior (fun i => pureToBehavior (s i)) = T.evalPure s
  | .leaf _ => rfl
  | @ExtensiveTree.chance _ _ _ C instF prob _ next => by
    let _ := instF
    ext j
    simp only [ExtensiveTree.evalBehavior, ExtensiveTree.evalPure]
    refine sum_congr rfl fun c _ => ?_
    rw [evalBehavior_pureToBehavior s (next c)]
  | .decision i h next => by
    ext j
    simp only [ExtensiveTree.evalBehavior, ExtensiveTree.evalPure, pureToBehavior]
    rw [sum_eq_single (s i h)]
    · simp only [Pi.single_eq_same, one_mul]
      rw [evalBehavior_pureToBehavior s (next (s i h))]
    · intro a _ ha
      simp [ha]
    · intro hmem
      exact absurd (mem_univ _) hmem

namespace PerfectInfoTree

/-- A two-player perfect-information game is zero-sum if the two players' payoffs sum to `0` at
every terminal leaf. -/
@[expose] def IsZeroSum (T : PerfectInfoTree Bool) : Prop :=
  ∀ z : LeafPath T, z.payoff false + z.payoff true = 0

theorem IsZeroSum.decision {p : Bool} {A : Type} [Fintype A] [Nonempty A]
    {next : A → PerfectInfoTree Bool} (hzs : (PerfectInfoTree.decision p next).IsZeroSum)
    (a : A) : (next a).IsZeroSum :=
  fun z => hzs (.decision a z)

theorem IsZeroSum.chance {C : Type} [Fintype C] {prob : C → ℝ} {hprob : IsMixedStrategy prob}
    {next : C → PerfectInfoTree Bool} (hzs : (PerfectInfoTree.chance prob hprob next).IsZeroSum)
    (c : C) : (next c).IsZeroSum :=
  fun z => hzs (.chance c z)

/-- A perfect-information tree is zero-sum iff its extensive-form embedding `T.toExtensiveTree`
satisfies `ExtensiveTree.IsZeroSum`. -/
theorem toExtensiveTree_isZeroSum_iff (T : PerfectInfoTree Bool) :
    T.toExtensiveTree.IsZeroSum ↔ T.IsZeroSum := by
  rw [ExtensiveTree.isZeroSum_iff]
  constructor
  · intro h z
    simpa [leafPathEquivTerminal_payoff] using h (leafPathEquivTerminal T z)
  · intro h z
    have hp := leafPathEquivTerminal_payoff ((leafPathEquivTerminal T).symm z)
    rw [(leafPathEquivTerminal T).apply_symm_apply z] at hp
    simpa [hp] using h ((leafPathEquivTerminal T).symm z)

theorem IsZeroSum.expectedPayoff_add_eq_zero :
    ∀ {T : PerfectInfoTree Bool}, T.IsZeroSum →
      ∀ (s : ∀ i, PureStrategy i T), T.expectedPayoff s false + T.expectedPayoff s true = 0
  | .leaf _, hzs, _ => hzs .leaf
  | @PerfectInfoTree.decision _ _ _ instF instN _, hzs, s => by
    let _ := instF
    let _ := instN
    exact (hzs.decision _).expectedPayoff_add_eq_zero _
  | @PerfectInfoTree.chance _ C instF prob _ next, hzs, s => by
    let _ := instF
    simp only [expectedPayoff_chance, ← sum_add_distrib, ← mul_add]
    exact sum_eq_zero fun c _ => by
      rw [(hzs.chance c).expectedPayoff_add_eq_zero _, mul_zero]

theorem IsZeroSum.backwardInduction_snd_add_eq_zero {T : PerfectInfoTree Bool}
    (hzs : T.IsZeroSum) :
    (T.backwardInduction).2 false + (T.backwardInduction).2 true = 0 := by
  rw [backwardInduction_snd]
  exact hzs.expectedPayoff_add_eq_zero (T.backwardInduction).1

open Classical in
/-- View a pure strategy profile on `T : PerfectInfoTree ι` as a deterministic behavioral strategy
profile on `T.toExtensiveTree`. -/
noncomputable def toExtensiveBehavior {ι : Type u} (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) (i : ι) (h : T.InfoSet i) : h.Act → ℝ :=
  pureToBehavior (s i).toExtensive h

open Classical in
theorem toExtensiveBehavior_apply {ι : Type u} (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) (i : ι) (h : T.InfoSet i) :
    T.toExtensiveBehavior s i h = Pi.single ((s i).toExtensive h) (1 : ℝ) := by
  simp [toExtensiveBehavior, pureToBehavior]

open Classical in
theorem isBehaviorStrategy_toExtensiveBehavior {ι : Type u} (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) (i : ι) :
    IsBehaviorStrategy (T.toExtensiveBehavior s i) :=
  isBehaviorStrategy_pureToBehavior (s i).toExtensive

open Classical in
theorem toExtensiveBehavior_evalBehavior {ι : Type u} (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) :
    T.toExtensiveTree.evalBehavior (T.toExtensiveBehavior s) = T.expectedPayoff s := by
  have heq : T.toExtensiveBehavior s = fun i => pureToBehavior (s i).toExtensive := rfl
  rw [heq, ExtensiveTree.evalBehavior_pureToBehavior, toExtensiveTree_evalPure]

open Classical in
theorem toExtensiveBehavior_decision {ι : Type u} (p : ι) {A : Type} {instF : Fintype A}
    {instN : Nonempty A} (next : A → PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)) (a : A) :
    (fun i (h : (next a).InfoSet i) =>
        (@PerfectInfoTree.decision ι p A instF instN next).toExtensiveBehavior s i
          (.decision a h)) =
      (next a).toExtensiveBehavior fun i => (s i).childDecision a := by
  ext i h x
  simp [toExtensiveBehavior_apply]

open Classical in
theorem toExtensiveBehavior_chance {ι : Type u} {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} (next : C → PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next)) (c : C) :
    (fun i (h : (next c).InfoSet i) =>
        (@PerfectInfoTree.chance ι C instF prob hprob next).toExtensiveBehavior s i
          (.chance c h)) =
      (next c).toExtensiveBehavior fun i => (s i).childChance c := by
  ext i h x
  simp [toExtensiveBehavior_apply]

open Classical in
/-- Under `T.toExtensiveBehavior`, behavioral Nash equilibria on `T.toExtensiveTree` coincide
with pure Nash equilibria of `T.toCostGame`. -/
theorem toExtensiveTree_isBehaviorNash_pure_iff (T : PerfectInfoTree Bool)
    (s : ∀ i, PureStrategy i T) :
    T.toExtensiveTree.IsBehaviorNash (T.toExtensiveBehavior s) ↔
      T.toCostGame.IsPureNash s := by
  have hplan : ∀ i,
      T.toExtensiveTree.behaviorToRealizationPlan i (T.toExtensiveBehavior s i) =
        T.toExtensiveTree.mixedToRealizationPlan i
          (Pi.single ((s i).toExtensive) (1 : ℝ)) := by
    intro i
    ext σ
    rw [ExtensiveTree.behaviorToRealizationPlan, ExtensiveTree.mixedToRealizationPlan_def]
    exact (realizationProbBehavior_pureToBehavior_eq _ _).trans
      (realizationProbMixed_single_eq _ _).symm
  rw [isBehaviorNash_iff_isSeqNash T.toExtensiveTree_perfectRecall, hplan false, hplan true]
  constructor
  · rintro ⟨_, hseq⟩
    have hmix : T.toExtensiveTree.toCostGame.IsMixedNash
        (fun i => Pi.single ((s i).toExtensive) (1 : ℝ)) :=
      (isMixedNash_toCostGame_iff_isSeqNash T.toExtensiveTree_perfectRecall _).2
        ⟨fun i => isMixedStrategy_single _, hseq⟩
    exact (toExtensiveTree_isPureNash_iff T s).1
      ((CostGame.isMixedNash_single_iff _ _).1 hmix)
  · intro hpure
    have hmix : T.toExtensiveTree.toCostGame.IsMixedNash
        (fun i => Pi.single ((s i).toExtensive) (1 : ℝ)) :=
      (CostGame.isMixedNash_single_iff _ _).2 ((toExtensiveTree_isPureNash_iff T s).2 hpure)
    exact ⟨isBehaviorStrategy_toExtensiveBehavior T s,
      ((isMixedNash_toCostGame_iff_isSeqNash T.toExtensiveTree_perfectRecall _).1 hmix).2⟩

/-- A behavioral strategy profile `β` on `T.toExtensiveTree` is a **behavioral subgame-perfect
equilibrium** (`IsBehaviorSPE`) if its restriction to every subgame of `T` is a behavioral Nash
equilibrium of that subgame's embedded extensive tree. -/
@[expose] def IsBehaviorSPE :
    (T : PerfectInfoTree Bool) → (∀ i, ∀ h : T.InfoSet i, h.Act → ℝ) → Prop
  | .leaf _, _ => True
  | @PerfectInfoTree.decision _ p A instF instN next, β =>
      (@PerfectInfoTree.decision Bool p A instF instN next).toExtensiveTree.IsBehaviorNash β ∧
        ∀ a, IsBehaviorSPE (next a) fun i h => β i (.decision a h)
  | @PerfectInfoTree.chance _ C instF prob hprob next, β =>
      (@PerfectInfoTree.chance Bool C instF prob hprob next).toExtensiveTree.IsBehaviorNash β ∧
        ∀ c, IsBehaviorSPE (next c) fun i h => β i (.chance c h)

/-- Every behavioral subgame-perfect equilibrium of `T` is a behavioral Nash equilibrium of
`T.toExtensiveTree`. -/
theorem IsBehaviorSPE.isBehaviorNash {T : PerfectInfoTree Bool}
    {β : ∀ i, ∀ h : T.InfoSet i, h.Act → ℝ} (hspe : T.IsBehaviorSPE β) :
    T.toExtensiveTree.IsBehaviorNash β := by
  cases T with
  | leaf _ => exact ⟨(fun _ h => nomatch h), fun _ _ _ => le_rfl⟩
  | decision _ _ => exact hspe.1
  | chance _ _ _ => exact hspe.1

open Classical in
/-- A pure strategy profile `s` is a pure subgame-perfect equilibrium iff its embedded behavioral
strategy `T.toExtensiveBehavior s` is a behavioral subgame-perfect equilibrium. -/
theorem isPureSPE_iff_isBehaviorSPE :
    ∀ (T : PerfectInfoTree Bool) (s : ∀ i, PureStrategy i T),
      T.IsPureSPE s ↔ T.IsBehaviorSPE (T.toExtensiveBehavior s)
  | .leaf _, _ => by simp [IsPureSPE, IsBehaviorSPE]
  | @PerfectInfoTree.decision _ p A instF instN next, s => by
    let _ := instF
    let _ := instN
    simp only [IsPureSPE, IsBehaviorSPE]
    rw [← toExtensiveTree_isBehaviorNash_pure_iff _ s]
    refine and_congr Iff.rfl (forall_congr' fun a => ?_)
    rw [toExtensiveBehavior_decision, isPureSPE_iff_isBehaviorSPE (next a)]
  | @PerfectInfoTree.chance _ C instF prob hprob next, s => by
    let _ := instF
    simp only [IsPureSPE, IsBehaviorSPE]
    rw [← toExtensiveTree_isBehaviorNash_pure_iff _ s]
    refine and_congr Iff.rfl (forall_congr' fun c => ?_)
    rw [toExtensiveBehavior_chance, isPureSPE_iff_isBehaviorSPE (next c)]

open Classical in
/-- Backward induction constructs an explicit behavioral subgame-perfect equilibrium of
`T.toExtensiveTree`. -/
theorem backwardInduction_isBehaviorSPE (T : PerfectInfoTree Bool) :
    T.IsBehaviorSPE (T.toExtensiveBehavior (T.backwardInduction).1) :=
  (isPureSPE_iff_isBehaviorSPE T (T.backwardInduction).1).1 (isPureSPE_backwardInduction T)

namespace IsZeroSum

open Classical in
/-- Backward induction constructs a sequence-form Nash equilibrium of `T.toExtensiveTree`. -/
theorem backwardInduction_isSeqNash (T : PerfectInfoTree Bool) :
    T.toExtensiveTree.IsSeqNash
      (T.toExtensiveTree.behaviorToRealizationPlan false
        (T.toExtensiveBehavior (T.backwardInduction).1 false))
      (T.toExtensiveTree.behaviorToRealizationPlan true
        (T.toExtensiveBehavior (T.backwardInduction).1 true)) :=
  ((isBehaviorNash_iff_isSeqNash T.toExtensiveTree_perfectRecall _).1
    (backwardInduction_isBehaviorSPE T).isBehaviorNash).2

open Classical in
/-- In a zero-sum perfect-information game, every behavioral Nash equilibrium `β` of
`T.toExtensiveTree` (regardless of continuation ties or off-path threats) attains the unique
backward-induction payoff vector `(T.backwardInduction).2`. -/
theorem isBehaviorNash_evalBehavior_eq_backwardInduction {T : PerfectInfoTree Bool}
    (hzs : T.IsZeroSum) {β : ∀ i, ∀ h : T.InfoSet i, h.Act → ℝ}
    (hβ : T.toExtensiveTree.IsBehaviorNash β) :
    T.toExtensiveTree.evalBehavior β = (T.backwardInduction).2 := by
  have hzsE : T.toExtensiveTree.IsZeroSum := (toExtensiveTree_isZeroSum_iff T).2 hzs
  have hbi : T.toExtensiveTree.IsBehaviorNash (T.toExtensiveBehavior (T.backwardInduction).1) :=
    (backwardInduction_isBehaviorSPE T).isBehaviorNash
  have h0_eq : T.toExtensiveTree.evalBehavior β false = (T.backwardInduction).2 false := by
    have h1 := hβ.evalBehavior_eq T.toExtensiveTree_perfectRecall hzsE
    have h2 := hbi.evalBehavior_eq T.toExtensiveTree_perfectRecall hzsE
    rw [h1.1, ← h2.1, toExtensiveBehavior_evalBehavior, ← backwardInduction_snd]
  ext i
  cases i with
  | false => exact h0_eq
  | true =>
    rw [hzsE.evalBehavior_true, h0_eq]
    linarith [hzs.backwardInduction_snd_add_eq_zero]

open Classical in
/-- The value of player `false`'s backward-induction solution equals both the sequence-form
maximin/minimax values and the behavioral maximin/minimax values of `T.toExtensiveTree`. -/
theorem backwardInduction_snd_eq_seq_minimax {T : PerfectInfoTree Bool} (hzs : T.IsZeroSum) :
    (T.backwardInduction).2 false =
        (⨆ x : {x : SeqVar T.toExtensiveTree false → ℝ //
            T.toExtensiveTree.IsRealizationPlan false x},
          T.toExtensiveTree.seqLowerVal x.1) ∧
      (T.backwardInduction).2 false =
        (⨅ y : {y : SeqVar T.toExtensiveTree true → ℝ //
            T.toExtensiveTree.IsRealizationPlan true y},
          T.toExtensiveTree.seqUpperVal y.1) ∧
      (T.backwardInduction).2 false =
        (⨆ β₀ : {β₀ : ∀ h : T.InfoSet false, h.Act → ℝ // IsBehaviorStrategy β₀},
          T.toExtensiveTree.behaviorLowerVal β₀.1) := by
  have hzsE : T.toExtensiveTree.IsZeroSum := (toExtensiveTree_isZeroSum_iff T).2 hzs
  have hbi : T.toExtensiveTree.IsBehaviorNash (T.toExtensiveBehavior (T.backwardInduction).1) :=
    (backwardInduction_isBehaviorSPE T).isBehaviorNash
  have heq := hbi.evalBehavior_eq T.toExtensiveTree_perfectRecall hzsE
  have hval : (T.backwardInduction).2 false =
      T.toExtensiveTree.evalBehavior (T.toExtensiveBehavior (T.backwardInduction).1) false := by
    rw [toExtensiveBehavior_evalBehavior, ← backwardInduction_snd]
  have hseq_eq :
      (⨆ x : {x : SeqVar T.toExtensiveTree false → ℝ //
          T.toExtensiveTree.IsRealizationPlan false x}, T.toExtensiveTree.seqLowerVal x.1) =
        ⨅ y : {y : SeqVar T.toExtensiveTree true → ℝ //
            T.toExtensiveTree.IsRealizationPlan true y}, T.toExtensiveTree.seqUpperVal y.1 :=
    hzsE.seq_iSup_iInf_eq_iInf_iSup T.toExtensiveTree_perfectRecall
  refine ⟨hval.trans heq.2, (hval.trans heq.2).trans hseq_eq, hval.trans heq.1⟩

open Classical in
/-- Every behavioral subgame-perfect equilibrium of a zero-sum perfect-information game attains
the backward-induction payoff vector `(T.backwardInduction).2`. -/
theorem isBehaviorSPE_evalBehavior_eq_backwardInduction {T : PerfectInfoTree Bool}
    (hzs : T.IsZeroSum) {β : ∀ i, ∀ h : T.InfoSet i, h.Act → ℝ} (hspe : T.IsBehaviorSPE β) :
    T.toExtensiveTree.evalBehavior β = (T.backwardInduction).2 :=
  hzs.isBehaviorNash_evalBehavior_eq_backwardInduction hspe.isBehaviorNash

open Classical in
/-- In a zero-sum decision game `.decision p next`, every behavioral subgame-perfect equilibrium
attains `((next a).backwardInduction).2` on every action branch `a`. -/
theorem isBehaviorSPE_decision_evalBehavior_eq_backwardInduction {p : Bool} {A : Type}
    [Fintype A] [Nonempty A] {next : A → PerfectInfoTree Bool}
    (hzs : (PerfectInfoTree.decision p next).IsZeroSum)
    {β : ∀ i, ∀ h : (PerfectInfoTree.decision p next).InfoSet i, h.Act → ℝ}
    (hspe : (PerfectInfoTree.decision p next).IsBehaviorSPE β) (a : A) :
    (next a).toExtensiveTree.evalBehavior (fun i h => β i (.decision a h)) =
      ((next a).backwardInduction).2 :=
  (hzs.decision a).isBehaviorNash_evalBehavior_eq_backwardInduction (hspe.2 a).isBehaviorNash

open Classical in
/-- In a zero-sum chance game `.chance prob hprob next`, every behavioral subgame-perfect
equilibrium attains `((next c).backwardInduction).2` on every chance branch `c`. -/
theorem isBehaviorSPE_chance_evalBehavior_eq_backwardInduction {C : Type} [Fintype C]
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree Bool}
    (hzs : (PerfectInfoTree.chance prob hprob next).IsZeroSum)
    {β : ∀ i, ∀ h : (PerfectInfoTree.chance prob hprob next).InfoSet i, h.Act → ℝ}
    (hspe : (PerfectInfoTree.chance prob hprob next).IsBehaviorSPE β) (c : C) :
    (next c).toExtensiveTree.evalBehavior (fun i h => β i (.chance c h)) =
      ((next c).backwardInduction).2 :=
  (hzs.chance c).isBehaviorNash_evalBehavior_eq_backwardInduction (hspe.2 c).isBehaviorNash

open Classical in
/-- Every pure Nash equilibrium (and hence every pure subgame-perfect equilibrium) of a zero-sum
perfect-information game has expected payoff equal to `(T.backwardInduction).2`. -/
theorem isPureNash_expectedPayoff_eq_backwardInduction {T : PerfectInfoTree Bool}
    (hzs : T.IsZeroSum) {s : ∀ i, PureStrategy i T} (hs : T.toCostGame.IsPureNash s) :
    T.expectedPayoff s = (T.backwardInduction).2 := by
  have hβ := (toExtensiveTree_isBehaviorNash_pure_iff T s).2 hs
  have hev := hzs.isBehaviorNash_evalBehavior_eq_backwardInduction hβ
  rwa [toExtensiveBehavior_evalBehavior] at hev

open Classical in
/-- Every mixed Nash equilibrium of `T.toCostGame` in a zero-sum perfect-information game attains
the unique backward-induction payoff vector `(T.backwardInduction).2`. -/
theorem isMixedNash_expectedPayoff_eq_backwardInduction {T : PerfectInfoTree Bool}
    (hzs : T.IsZeroSum) {μ : ∀ i, PureStrategy i T → ℝ} (hμ : T.toCostGame.IsMixedNash μ) :
    T.toExtensiveTree.evalMixed (fun i sE => μ i (PureStrategy.ofExtensive T sE)) =
      (T.backwardInduction).2 := by
  have hzsE : T.toExtensiveTree.IsZeroSum := (toExtensiveTree_isZeroSum_iff T).2 hzs
  have hmixE := (toExtensiveTree_isMixedNash_iff T μ).2 hμ
  have h0_eq :
      T.toExtensiveTree.evalMixed (fun i sE => μ i (PureStrategy.ofExtensive T sE)) false =
        (T.backwardInduction).2 false := by
    have hm := hzsE.isMixedNash_evalMixed_eq T.toExtensiveTree_perfectRecall hmixE
    exact hm.2.trans (hzs.backwardInduction_snd_eq_seq_minimax).1.symm
  ext i
  cases i with
  | false => exact h0_eq
  | true =>
    rw [hzsE.evalMixed_true, h0_eq]
    linarith [hzs.backwardInduction_snd_add_eq_zero]

end IsZeroSum

end PerfectInfoTree

end PerfectInfoZeroSumBridge

end Cslib.GameTheory.Extensive
