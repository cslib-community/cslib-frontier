/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.MixedStrategy
public import CslibFrontier.GameTheory.Strategic.Mixed
public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Extensive-form games with information sets and perfect recall

An extensive-form game with imperfect information (`ExtensiveTree ι H Act`) is a finite rooted
game tree over player set `ι`, information sets `H i` for each player `i`, and choice types
`Act i h` at each information set `h : H i` ([vonStengel2007], Section 3.7). Every node belonging
to `h` has the same choice type `Act i h`.

A *pure strategy* of player `i` (`PureStrategy H Act i`) assigns a choice `Act i h` to every
information set `h : H i`. A *behavior strategy* (`IsBehaviorStrategy`) assigns a mixed strategy
`IsMixedStrategy (β h)` independently at each `h : H i`. A *mixed strategy* is a probability
distribution `IsMixedStrategy μ` over `PureStrategy H Act i`.

Each terminal path `z : Terminal T` induces a player-`i` sequence `z.seq i : Seq H Act i` of
`(information set, action)` pairs. Under both mixed and behavior profiles, terminal-node
probabilities factor as the product of the chance-node probability (`z.chanceWeight`) and
player-wise sequence realization probabilities (`terminalProbMixed_eq`, `terminalProbBehavior_eq`).
Two strategies of player `i` are *realization-equivalent* if they induce the same terminal-node
distribution against every pure strategy profile of the other players (`RealizationEquivMixed`,
`RealizationEquivMixedBehavior`), which implies identical distributions and expected payoffs
against arbitrary mixed and behavior opponent profiles as well.

An extensive game satisfies *perfect recall* for player `i` (`PerfectRecall T i`,
[vonStengel2007], Section 3.10, p. 70) if all decision nodes of player `i` in the same
information set `h` are preceded by the same sequence of player-`i` choices. In particular, no
root-to-leaf path visits any information set of player `i` more than once
(`PerfectRecall.noRepeatedInfoSet`).

## Main definitions

* `Cslib.GameTheory.Extensive.ExtensiveTree`: finite extensive-form game trees with leaves,
  chance nodes, and player decision nodes tagged by information sets.
* `Cslib.GameTheory.Extensive.PureStrategy`: pure strategies `∀ h : H i, Act i h`.
* `Cslib.GameTheory.Extensive.IsBehaviorStrategy`: behavioral strategies.
* `Cslib.GameTheory.Extensive.behaviorToMixed`: product mixed strategy induced by a behavior
  strategy.
* `Cslib.GameTheory.Extensive.Terminal`: root-to-leaf paths in an extensive game tree.
* `Cslib.GameTheory.Extensive.Node`: internal and leaf nodes in an extensive game tree.
* `Cslib.GameTheory.Extensive.ExtensiveTree.toCostGame`: induced strategic game in cost form.
* `Cslib.GameTheory.Extensive.ExtensiveTree.RealizationEquivMixed`,
  `Cslib.GameTheory.Extensive.ExtensiveTree.RealizationEquivMixedBehavior`: realization equivalence.
* `Cslib.GameTheory.Extensive.ExtensiveTree.PerfectRecall`: perfect recall for player `i`.
* `Cslib.GameTheory.Extensive.ExtensiveTree.NoRepeatedInfoSet`: no absent-mindedness along any
  play.

## Main results

* `Cslib.GameTheory.Extensive.terminalProbPure_eq`,
  `Cslib.GameTheory.Extensive.terminalProbBehavior_eq`,
  `Cslib.GameTheory.Extensive.terminalProbMixed_eq`: sequence-factor
  decomposition of terminal reach probabilities.
* `Cslib.GameTheory.Extensive.realizationProbMixed_behaviorToMixed`: for a sequence without
  repeated information sets, the product mixed strategy matches the behavior realization
  probability.
* `Cslib.GameTheory.Extensive.ExtensiveTree.toCostGame_expectedCost`: strategic-form expected
  cost equals negated extensive-form mixed payoff.
* `Cslib.GameTheory.Extensive.ExtensiveTree.PerfectRecall.noRepeatedInfoSet`: perfect recall
  precludes visiting an information set twice on any play.

## References

* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Sections 3.7 and 3.10.
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset

universe u v

/-- A finite extensive-form game tree over player set `ι`, information sets `H i`, and choice
types `Act i h` at each information set `h : H i` ([vonStengel2007], Section 3.7). -/
inductive ExtensiveTree (ι : Type u) (H : ι → Type v) (Act : ∀ i, H i → Type) :
    Type (max u v 1)
  | leaf (payoff : ι → ℝ) : ExtensiveTree ι H Act
  | chance {C : Type} [Fintype C] (prob : C → ℝ) (hprob : IsMixedStrategy prob)
      (next : C → ExtensiveTree ι H Act) : ExtensiveTree ι H Act
  | decision (i : ι) (h : H i) (next : Act i h → ExtensiveTree ι H Act) :
      ExtensiveTree ι H Act

section Strategies

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

/-- A pure strategy of player `i` assigns an action at every information set `h : H i`. -/
abbrev PureStrategy (H : ι → Type v) (Act : ∀ i, H i → Type) (i : ι) : Type v :=
  ∀ h : H i, Act i h

/-- A choice pair `(h, a)` of player `i`. -/
abbrev Choice (H : ι → Type v) (Act : ∀ i, H i → Type) (i : ι) : Type v :=
  Σ h : H i, Act i h

/-- A sequence of choice pairs of player `i`. -/
abbrev Seq (H : ι → Type v) (Act : ∀ i, H i → Type) (i : ι) : Type v :=
  List (Choice H Act i)

/-- A behavior strategy of player `i` assigns a mixed strategy independently at each information
set `h : H i`. -/
@[expose] def IsBehaviorStrategy {i : ι} [∀ h, Fintype (Act i h)]
    (β : ∀ h : H i, Act i h → ℝ) : Prop :=
  ∀ h, IsMixedStrategy (β h)

/-- View a pure strategy of player `i` as a deterministic behavior strategy. -/
def pureToBehavior {i : ι} [∀ h, DecidableEq (Act i h)]
    (s : PureStrategy H Act i) (h : H i) : Act i h → ℝ :=
  Pi.single (s h) 1

@[simp]
theorem pureToBehavior_apply {i : ι} [∀ h, DecidableEq (Act i h)]
    (s : PureStrategy H Act i) (h : H i) (a : Act i h) :
    pureToBehavior s h a = Pi.single (M := fun _ => ℝ) (s h) (1 : ℝ) a := by
  simp [pureToBehavior]

theorem isBehaviorStrategy_pureToBehavior {i : ι} [∀ h, Fintype (Act i h)]
    [∀ h, DecidableEq (Act i h)] (s : PureStrategy H Act i) :
    IsBehaviorStrategy (pureToBehavior s) :=
  fun h => isMixedStrategy_single (s h)

/-- The product mixed strategy induced by a behavior strategy `β`: independently sample `s h`
from `β h` at each information set `h : H i`. -/
def behaviorToMixed {i : ι} [Fintype (H i)] (β : ∀ h : H i, Act i h → ℝ)
    (s : PureStrategy H Act i) : ℝ :=
  ∏ h : H i, β h (s h)

@[simp]
theorem behaviorToMixed_apply {i : ι} [Fintype (H i)] (β : ∀ h : H i, Act i h → ℝ)
    (s : PureStrategy H Act i) :
    behaviorToMixed β s = ∏ h : H i, β h (s h) := by
  simp [behaviorToMixed]

theorem isMixedStrategy_behaviorToMixed {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β) :
    IsMixedStrategy (behaviorToMixed β) := by
  refine isMixedStrategy_iff.2 ⟨fun s => prod_nonneg fun h _ => (hβ h).nonneg (s h), ?_⟩
  simp only [behaviorToMixed]
  rw [← Fintype.prod_sum (fun h a => β h a)]
  exact prod_eq_one fun h _ => (hβ h).sum_eq_one

/-- Pure strategy `s` matches sequence `σ` if `s h = a` for every `(h, a)` in `σ`. -/
@[expose] def MatchesSeq {i : ι} (s : PureStrategy H Act i) (σ : Seq H Act i) : Prop :=
  ∀ p ∈ σ, s p.1 = p.2

@[simp]
theorem matchesSeq_nil {i : ι} (s : PureStrategy H Act i) : MatchesSeq s [] :=
  fun _ hp => False.elim (List.not_mem_nil hp)

@[simp]
theorem matchesSeq_cons {i : ι} (s : PureStrategy H Act i) (p : Choice H Act i)
    (σ : Seq H Act i) :
    MatchesSeq s (p :: σ) ↔ s p.1 = p.2 ∧ MatchesSeq s σ := by
  simp [MatchesSeq]

theorem matchesSeq_append {i : ι} (s : PureStrategy H Act i) (σ₁ σ₂ : Seq H Act i) :
    MatchesSeq s (σ₁ ++ σ₂) ↔ MatchesSeq s σ₁ ∧ MatchesSeq s σ₂ := by
  simp only [MatchesSeq, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
    fun ⟨h₁, h₂⟩ p hp => hp.elim (h₁ p) (h₂ p)⟩

open Classical in
/-- The realization probability of sequence `σ` under mixed strategy `μ`: the total weight of
pure strategies matching `σ`. -/
noncomputable def realizationProbMixed {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] (μ : PureStrategy H Act i → ℝ) (σ : Seq H Act i) : ℝ :=
  ∑ s : PureStrategy H Act i, if MatchesSeq s σ then μ s else 0

open Classical in
/-- Unfolding equation for `realizationProbMixed`, whose body is not exposed. -/
theorem realizationProbMixed_def {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] (μ : PureStrategy H Act i → ℝ) (σ : Seq H Act i) :
    realizationProbMixed μ σ =
      ∑ s : PureStrategy H Act i, if MatchesSeq s σ then μ s else 0 := by
  rw [realizationProbMixed]

/-- The realization probability of sequence `σ` under behavior strategy `β`: the product of
`β h a` along `(h, a) ∈ σ`. -/
def realizationProbBehavior {i : ι} (β : ∀ h : H i, Act i h → ℝ)
    (σ : Seq H Act i) : ℝ :=
  (σ.map fun p => β p.1 p.2).prod

@[simp]
theorem realizationProbBehavior_nil {i : ι} (β : ∀ h : H i, Act i h → ℝ) :
    realizationProbBehavior β [] = 1 := by
  simp [realizationProbBehavior]

@[simp]
theorem realizationProbBehavior_cons {i : ι} (β : ∀ h : H i, Act i h → ℝ)
    (p : Choice H Act i) (σ : Seq H Act i) :
    realizationProbBehavior β (p :: σ) = β p.1 p.2 * realizationProbBehavior β σ := by
  simp [realizationProbBehavior]

theorem realizationProbBehavior_append {i : ι} (β : ∀ h : H i, Act i h → ℝ)
    (σ₁ σ₂ : Seq H Act i) :
    realizationProbBehavior β (σ₁ ++ σ₂) =
      realizationProbBehavior β σ₁ * realizationProbBehavior β σ₂ := by
  simp [realizationProbBehavior]

theorem realizationProbBehavior_nonneg {i : ι} [∀ h, Fintype (Act i h)]
    {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β) :
    ∀ σ : Seq H Act i, 0 ≤ realizationProbBehavior β σ
  | [] => zero_le_one
  | p :: σ => mul_nonneg ((hβ p.1).nonneg p.2) (realizationProbBehavior_nonneg hβ σ)

theorem realizationProbMixed_nonneg {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] {μ : PureStrategy H Act i → ℝ} (hμ : IsMixedStrategy μ)
    (σ : Seq H Act i) :
    0 ≤ realizationProbMixed μ σ := by
  classical
  refine sum_nonneg fun s _ => ?_
  split_ifs
  · exact hμ.nonneg s
  · exact le_rfl

theorem realizationProbMixed_nil {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] {μ : PureStrategy H Act i → ℝ} (hμ : IsMixedStrategy μ) :
    realizationProbMixed μ [] = 1 := by
  classical
  simpa [realizationProbMixed] using hμ.sum_eq_one

open Classical in
theorem realizationProbBehavior_pureToBehavior_eq {i : ι} [∀ h, DecidableEq (Act i h)]
    (s : PureStrategy H Act i) (σ : Seq H Act i) :
    realizationProbBehavior (pureToBehavior s) σ = if MatchesSeq s σ then 1 else 0 := by
  induction σ with
  | nil => simp
  | cons p σ ih =>
    rw [realizationProbBehavior_cons, ih]
    simp only [matchesSeq_cons]
    by_cases hp : s p.1 = p.2
    · simp [pureToBehavior, hp]
    · simp [pureToBehavior, hp]

open Classical in
theorem realizationProbMixed_single_eq {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] [∀ h, DecidableEq (Act i h)]
    (s : PureStrategy H Act i) (σ : Seq H Act i) :
    realizationProbMixed (Pi.single s (1 : ℝ)) σ = if MatchesSeq s σ then 1 else 0 := by
  simp only [realizationProbMixed]
  rw [sum_eq_single s]
  · simp
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro hmem
    exact absurd (mem_univ s) hmem

private theorem sum_pi_ite_eq {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {α : ι' → Type*}
    [∀ k, Fintype (α k)] (f : ∀ k, α k → ℝ) (P : ∀ k, α k → Prop)
    [∀ k, DecidablePred (P k)] :
    ∑ x : (∀ k, α k), (if ∀ k, P k (x k) then ∏ k, f k (x k) else 0) =
      ∏ k, ∑ a : α k, if P k a then f k a else 0 := by
  have h1 : ∀ x : (∀ k, α k),
      (if ∀ k, P k (x k) then ∏ k, f k (x k) else 0) =
        ∏ k, if P k (x k) then f k (x k) else 0 := by
    intro x
    split_ifs with hx
    · exact prod_congr rfl fun k _ => by simp [hx k]
    · push Not at hx
      obtain ⟨k, hk⟩ := hx
      exact (prod_eq_zero (mem_univ k) (by simp [hk])).symm
  simp_rw [h1]
  exact (Fintype.prod_sum fun k a => if P k a then f k a else 0).symm

/-- For a sequence `σ` that visits no information set twice, the product mixed strategy
`behaviorToMixed β` assigns `σ` the exact same realization probability as `β`. -/
theorem realizationProbMixed_behaviorToMixed {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β)
    {σ : Seq H Act i} (hnodup : (σ.map Sigma.fst).Nodup) :
    realizationProbMixed (behaviorToMixed β) σ = realizationProbBehavior β σ := by
  classical
  have hmatch : ∀ s : PureStrategy H Act i,
      MatchesSeq s σ ↔ ∀ h : H i, ∀ p ∈ σ, p.1 = h → (⟨h, s h⟩ : Choice H Act i) = p := by
    intro s
    constructor
    · intro hs h p hp heq
      rcases p with ⟨h', a'⟩
      dsimp only at heq
      subst heq
      exact congrArg (Sigma.mk h') (hs ⟨h', a'⟩ hp)
    · intro hs p hp
      exact eq_of_heq (Sigma.mk.inj_iff.1 (hs p.1 p hp rfl)).2
  simp only [realizationProbMixed, behaviorToMixed]
  calc ∑ s : PureStrategy H Act i, (if MatchesSeq s σ then ∏ h : H i, β h (s h) else 0)
      = ∑ s : PureStrategy H Act i,
          if ∀ h : H i, ∀ p ∈ σ, p.1 = h → (⟨h, s h⟩ : Choice H Act i) = p then
            ∏ h : H i, β h (s h)
          else 0 := by
        exact sum_congr rfl fun s _ => if_congr (hmatch s) rfl rfl
    _ = ∏ h : H i, ∑ a : Act i h,
          if ∀ p ∈ σ, p.1 = h → (⟨h, a⟩ : Choice H Act i) = p then β h a else 0 :=
        sum_pi_ite_eq (fun h a => β h a)
          (fun h a => ∀ p ∈ σ, p.1 = h → (⟨h, a⟩ : Choice H Act i) = p)
    _ = (σ.map fun p => β p.1 p.2).prod := by
        clear hmatch
        induction σ with
        | nil =>
          simp only [List.not_mem_nil, false_implies, implies_true, ↓reduceIte,
            List.map_nil, List.prod_nil]
          exact prod_eq_one fun h _ => (hβ h).sum_eq_one
        | cons q σ ih =>
          rcases q with ⟨qh, qa⟩
          rw [List.map_cons, List.nodup_cons] at hnodup
          rw [List.map_cons, List.prod_cons, ← ih hnodup.2]
          dsimp only at hnodup ⊢
          rw [← mul_prod_erase univ _ (mem_univ qh)]
          rw [← mul_prod_erase univ _ (mem_univ qh)]
          have hq : ∀ p ∈ σ, qh ≠ p.1 := fun p hp heq =>
            hnodup.1 (List.mem_map.2 ⟨p, hp, heq.symm⟩)
          have hsum : (∑ a : Act i qh,
              if ∀ p ∈ (⟨qh, qa⟩ :: σ), p.1 = qh → (⟨qh, a⟩ : Choice H Act i) = p
              then β qh a else 0) = β qh qa := by
            have hiff : ∀ a : Act i qh,
                (∀ p ∈ (⟨qh, qa⟩ :: σ), p.1 = qh → (⟨qh, a⟩ : Choice H Act i) = p) ↔
                  a = qa := by
              intro a
              constructor
              · intro h
                exact eq_of_heq (Sigma.mk.inj_iff.1 (h ⟨qh, qa⟩ List.mem_cons_self rfl)).2
              · rintro rfl p hp hp1
                rcases List.mem_cons.1 hp with rfl | hp
                · rfl
                · exact absurd hp1 (hq p hp).symm
            exact (sum_congr rfl fun a _ => if_congr (hiff a) rfl rfl).trans (by simp)
          have htail : (∑ a : Act i qh,
              if ∀ p ∈ σ, p.1 = qh → (⟨qh, a⟩ : Choice H Act i) = p then β qh a else 0) = 1 := by
            rw [← (hβ qh).sum_eq_one]
            exact sum_congr rfl fun a _ => ite_eq_left fun p hp hp1 => absurd hp1 (hq p hp).symm
          rw [hsum, htail, one_mul]
          congr 1
          refine prod_congr rfl fun h hh => ?_
          have hne : h ≠ qh := ne_of_mem_erase hh
          refine sum_congr rfl fun a _ => if_congr ⟨fun h1 p hp => h1 p (List.mem_cons_of_mem _ hp),
            fun h1 p hp hp1 => ?_⟩ rfl rfl
          rcases List.mem_cons.1 hp with rfl | hp
          · exact absurd hp1 hne.symm
          · exact h1 p hp hp1

end Strategies

section PathsAndNodes

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

/-- A root-to-leaf path in `T`. -/
inductive Terminal : ExtensiveTree ι H Act → Type (max u v 1)
  | leaf {w : ι → ℝ} : Terminal (.leaf w)
  | chance {C : Type} {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
      {next : C → ExtensiveTree ι H Act} (c : C) (sub : Terminal (next c)) :
      Terminal (@ExtensiveTree.chance ι H Act C instF prob hprob next)
  | decision {i : ι} {h : H i} {next : Act i h → ExtensiveTree ι H Act}
      (a : Act i h) (sub : Terminal (next a)) : Terminal (.decision i h next)

namespace Terminal

instance instNonempty [∀ i h, Nonempty (Act i h)] :
    (T : ExtensiveTree ι H Act) → Nonempty (Terminal T)
  | .leaf _ => ⟨.leaf⟩
  | @ExtensiveTree.chance _ _ _ _ _ _ hprob next =>
      let ⟨c, _⟩ := hprob.exists_pos
      let ⟨sub⟩ := instNonempty (next c)
      ⟨.chance c sub⟩
  | .decision _ _ next =>
      let a := Classical.arbitrary _
      let ⟨sub⟩ := instNonempty (next a)
      ⟨.decision a sub⟩

noncomputable instance instFintype [∀ i h, Fintype (Act i h)] :
    (T : ExtensiveTree ι H Act) → Fintype (Terminal T)
  | .leaf _ =>
      Fintype.ofEquiv PUnit.{max u v 1 + 1}
        { toFun := fun _ => .leaf
          invFun := fun _ => PUnit.unit
          left_inv := fun _ => rfl
          right_inv := fun z => by cases z; rfl }
  | @ExtensiveTree.chance _ _ _ C instF prob hprob next =>
      letI := instF
      letI := Classical.decEq C
      letI := fun c => instFintype (next c)
      let e : (Σ c : C, Terminal (next c)) ≃
          Terminal (@ExtensiveTree.chance ι H Act C instF prob hprob next) :=
        { toFun := fun p => .chance p.1 p.2
          invFun := fun z => match z with | .chance c sub => ⟨c, sub⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun z => by cases z; rfl }
      Fintype.ofEquiv _ e
  | .decision i h next =>
      letI := Classical.decEq (Act i h)
      letI := fun a => instFintype (next a)
      let e : (Σ a : Act i h, Terminal (next a)) ≃ Terminal (.decision i h next) :=
        { toFun := fun p => .decision p.1 p.2
          invFun := fun z => match z with | .decision a sub => ⟨a, sub⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun z => by cases z; rfl }
      Fintype.ofEquiv _ e

/-- Payoff vector at terminal node `z`. -/
def payoff : {T : ExtensiveTree ι H Act} → Terminal T → ι → ℝ
  | .leaf w, .leaf => w
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance _ sub => sub.payoff
  | .decision _ _ _, .decision _ sub => sub.payoff

@[simp]
theorem payoff_leaf (w : ι → ℝ) :
    (Terminal.leaf (H := H) (Act := Act) (w := w)).payoff = w := by
  simp [payoff]

@[simp]
theorem payoff_chance {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act} (c : C)
    (sub : Terminal (next c)) :
    (Terminal.chance (prob := prob) (hprob := hprob) c sub).payoff = sub.payoff := by
  simp [payoff]

@[simp]
theorem payoff_decision {i : ι} {h : H i} {next : Act i h → ExtensiveTree ι H Act}
    (a : Act i h) (sub : Terminal (next a)) :
    (Terminal.decision a sub).payoff = sub.payoff := by
  simp [payoff]

/-- Product of chance-node probabilities along terminal path `z`. -/
def chanceWeight : {T : ExtensiveTree ι H Act} → Terminal T → ℝ
  | .leaf _, .leaf => 1
  | @ExtensiveTree.chance _ _ _ _ _ prob _ _, .chance c sub => prob c * sub.chanceWeight
  | .decision _ _ _, .decision _ sub => sub.chanceWeight

@[simp]
theorem chanceWeight_leaf (w : ι → ℝ) :
    (Terminal.leaf (H := H) (Act := Act) (w := w)).chanceWeight = 1 := by
  simp [chanceWeight]

@[simp]
theorem chanceWeight_chance {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act} (c : C)
    (sub : Terminal (next c)) :
    (Terminal.chance (prob := prob) (hprob := hprob) c sub).chanceWeight =
      prob c * sub.chanceWeight := by
  simp [chanceWeight]

@[simp]
theorem chanceWeight_decision {i : ι} {h : H i} {next : Act i h → ExtensiveTree ι H Act}
    (a : Act i h) (sub : Terminal (next a)) :
    (Terminal.decision a sub).chanceWeight = sub.chanceWeight := by
  simp [chanceWeight]

theorem chanceWeight_nonneg : ∀ {T : ExtensiveTree ι H Act} (z : Terminal T), 0 ≤ z.chanceWeight
  | .leaf _, .leaf => zero_le_one
  | @ExtensiveTree.chance _ _ _ _ _ _ hprob _, .chance c sub =>
      mul_nonneg (hprob.nonneg c) (chanceWeight_nonneg sub)
  | .decision _ _ _, .decision _ sub => chanceWeight_nonneg sub

/-- Ordered sequence of `(information set, choice)` pairs made by player `i` along terminal path
`z`. -/
def seq [DecidableEq ι] (i : ι) :
    {T : ExtensiveTree ι H Act} → Terminal T → Seq H Act i
  | .leaf _, .leaf => []
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance _ sub => sub.seq i
  | .decision j h _, .decision a sub =>
      if hij : j = i then (match hij with | rfl => ⟨h, a⟩) :: sub.seq i else sub.seq i

@[simp]
theorem seq_leaf [DecidableEq ι] (i : ι) (w : ι → ℝ) :
    (Terminal.leaf (H := H) (Act := Act) (w := w)).seq i = [] := by
  simp [seq]

@[simp]
theorem seq_chance [DecidableEq ι] (i : ι) {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act}
    (c : C) (sub : Terminal (next c)) :
    (Terminal.chance (prob := prob) (hprob := hprob) c sub).seq i = sub.seq i := by
  simp [seq]

@[simp]
theorem seq_decision_self [DecidableEq ι] (i : ι) {h : H i}
    {next : Act i h → ExtensiveTree ι H Act} (a : Act i h) (sub : Terminal (next a)) :
    (Terminal.decision a sub).seq i = ⟨h, a⟩ :: sub.seq i := by
  simp [seq]

@[simp]
theorem seq_decision_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) {h : H j}
    {next : Act j h → ExtensiveTree ι H Act} (a : Act j h) (sub : Terminal (next a)) :
    (Terminal.decision a sub).seq i = sub.seq i := by
  simp [seq, hij]

end Terminal

/-- Probability of reaching terminal path `z` under pure strategy profile `s`. -/
def terminalProbPure [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) : {T : ExtensiveTree ι H Act} → Terminal T → ℝ
  | .leaf _, .leaf => 1
  | @ExtensiveTree.chance _ _ _ _ _ prob _ _, .chance c sub => prob c * terminalProbPure s sub
  | .decision i h _, .decision a sub => if s i h = a then terminalProbPure s sub else 0

@[simp]
theorem terminalProbPure_leaf [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) (w : ι → ℝ) :
    terminalProbPure s (Terminal.leaf (H := H) (Act := Act) (w := w)) = 1 := by
  simp [terminalProbPure]

@[simp]
theorem terminalProbPure_chance [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act} (c : C)
    (sub : Terminal (next c)) :
    terminalProbPure s (Terminal.chance (prob := prob) (hprob := hprob) c sub) =
      prob c * terminalProbPure s sub := by
  simp [terminalProbPure]

@[simp]
theorem terminalProbPure_decision [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) {i : ι} {h : H i}
    {next : Act i h → ExtensiveTree ι H Act} (a : Act i h) (sub : Terminal (next a)) :
    terminalProbPure s (Terminal.decision a sub) =
      if s i h = a then terminalProbPure s sub else 0 := by
  simp [terminalProbPure]

/-- Probability of reaching terminal path `z` under behavior strategy profile `β`. -/
def terminalProbBehavior (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    {T : ExtensiveTree ι H Act} → Terminal T → ℝ
  | .leaf _, .leaf => 1
  | @ExtensiveTree.chance _ _ _ _ _ prob _ _, .chance c sub =>
      prob c * terminalProbBehavior β sub
  | .decision i h _, .decision a sub => β i h a * terminalProbBehavior β sub

@[simp]
theorem terminalProbBehavior_leaf (β : ∀ i, ∀ h : H i, Act i h → ℝ) (w : ι → ℝ) :
    terminalProbBehavior β (Terminal.leaf (H := H) (Act := Act) (w := w)) = 1 := by
  simp [terminalProbBehavior]

@[simp]
theorem terminalProbBehavior_chance (β : ∀ i, ∀ h : H i, Act i h → ℝ) {C : Type}
    {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
    {next : C → ExtensiveTree ι H Act} (c : C) (sub : Terminal (next c)) :
    terminalProbBehavior β (Terminal.chance (prob := prob) (hprob := hprob) c sub) =
      prob c * terminalProbBehavior β sub := by
  simp [terminalProbBehavior]

@[simp]
theorem terminalProbBehavior_decision (β : ∀ i, ∀ h : H i, Act i h → ℝ) {i : ι} {h : H i}
    {next : Act i h → ExtensiveTree ι H Act} (a : Act i h) (sub : Terminal (next a)) :
    terminalProbBehavior β (Terminal.decision a sub) =
      β i h a * terminalProbBehavior β sub := by
  simp [terminalProbBehavior]

open Classical in
/-- Probability of reaching terminal path `z` under mixed strategy profile `μ`. -/
noncomputable def terminalProbMixed [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) {T : ExtensiveTree ι H Act} (z : Terminal T) : ℝ :=
  ∑ s : (∀ i, PureStrategy H Act i), (∏ i, μ i (s i)) * terminalProbPure s z

open Classical in
/-- Unfolding equation for `terminalProbMixed`, whose body is not exposed. -/
theorem terminalProbMixed_def [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) {T : ExtensiveTree ι H Act} (z : Terminal T) :
    terminalProbMixed μ z =
      ∑ s : (∀ i, PureStrategy H Act i), (∏ i, μ i (s i)) * terminalProbPure s z := by
  rw [terminalProbMixed]

open Classical in
/-- Sequence-factor decomposition of `terminalProbPure`. -/
theorem terminalProbPure_eq [Fintype ι] [DecidableEq ι] [∀ i h, DecidableEq (Act i h)]
    (s : ∀ i, PureStrategy H Act i) :
    ∀ {T : ExtensiveTree ι H Act} (z : Terminal T),
      terminalProbPure s z =
        z.chanceWeight * ∏ i, if MatchesSeq (s i) (z.seq i) then 1 else 0
  | .leaf _, .leaf => by simp
  | @ExtensiveTree.chance _ _ _ _ _ prob _ _, .chance c sub => by
    rw [terminalProbPure_chance, terminalProbPure_eq s sub, Terminal.chanceWeight_chance, mul_assoc]
    simp only [Terminal.seq_chance]
  | .decision j h _, .decision a sub => by
    rw [terminalProbPure_decision, terminalProbPure_eq s sub, Terminal.chanceWeight_decision]
    rw [← mul_prod_erase univ _ (mem_univ j)]
    rw [← mul_prod_erase univ (fun k =>
      if MatchesSeq (s k) ((Terminal.decision a sub).seq k) then (1 : ℝ) else 0) (mem_univ j)]
    have hother : ∀ k ∈ univ.erase j,
        (if MatchesSeq (s k) ((Terminal.decision a sub).seq k) then (1 : ℝ) else 0) =
          (if MatchesSeq (s k) (sub.seq k) then 1 else 0) := by
      intro k hk
      have hne : j ≠ k := (ne_of_mem_erase hk).symm
      simp [hne]
    rw [prod_congr rfl hother, Terminal.seq_decision_self]
    by_cases hsa : s j h = a
    · simp [hsa, matchesSeq_cons]
    · simp [hsa, matchesSeq_cons]

/-- Sequence-factor decomposition of `terminalProbBehavior`. -/
theorem terminalProbBehavior_eq [Fintype ι] [DecidableEq ι]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    ∀ {T : ExtensiveTree ι H Act} (z : Terminal T),
      terminalProbBehavior β z =
        z.chanceWeight * ∏ i, realizationProbBehavior (β i) (z.seq i)
  | .leaf _, .leaf => by simp
  | @ExtensiveTree.chance _ _ _ _ _ prob _ _, .chance c sub => by
    rw [terminalProbBehavior_chance, terminalProbBehavior_eq β sub, Terminal.chanceWeight_chance,
      mul_assoc]
    simp only [Terminal.seq_chance]
  | .decision j h _, .decision a sub => by
    rw [terminalProbBehavior, terminalProbBehavior_eq β sub, Terminal.chanceWeight]
    rw [← mul_prod_erase univ _ (mem_univ j)]
    rw [← mul_prod_erase univ (fun k =>
      realizationProbBehavior (β k) ((Terminal.decision a sub).seq k)) (mem_univ j)]
    have hother : ∀ k ∈ univ.erase j,
        realizationProbBehavior (β k) ((Terminal.decision a sub).seq k) =
          realizationProbBehavior (β k) (sub.seq k) := by
      intro k hk
      have hne : j ≠ k := (ne_of_mem_erase hk).symm
      simp [hne]
    rw [prod_congr rfl hother, Terminal.seq_decision_self, realizationProbBehavior_cons]
    ring

/-- Sequence-factor decomposition of `terminalProbMixed`. -/
theorem terminalProbMixed_eq [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) {T : ExtensiveTree ι H Act} (z : Terminal T) :
    terminalProbMixed μ z =
      z.chanceWeight * ∏ i, realizationProbMixed (μ i) (z.seq i) := by
  classical
  simp only [terminalProbMixed]
  have hterm : ∀ s : (∀ i, PureStrategy H Act i),
      (∏ i, μ i (s i)) * terminalProbPure s z =
        z.chanceWeight * ∏ i, (if MatchesSeq (s i) (z.seq i) then μ i (s i) else 0) := by
    intro s
    rw [terminalProbPure_eq s z]
    calc (∏ i, μ i (s i)) * (z.chanceWeight * ∏ i, if MatchesSeq (s i) (z.seq i) then 1 else 0)
        = z.chanceWeight * ∏ i, (μ i (s i) * if MatchesSeq (s i) (z.seq i) then 1 else 0) := by
          rw [← mul_assoc, mul_comm (∏ i, μ i (s i)) z.chanceWeight, mul_assoc, prod_mul_distrib]
      _ = z.chanceWeight * ∏ i, (if MatchesSeq (s i) (z.seq i) then μ i (s i) else 0) := by
          congr 1
          refine prod_congr rfl fun i _ => ?_
          split_ifs <;> simp
  simp_rw [hterm, ← mul_sum]
  congr 1
  simpa [realizationProbMixed] using
    (Fintype.prod_sum fun i (s_i : PureStrategy H Act i) =>
      if MatchesSeq s_i (z.seq i) then μ i s_i else 0).symm

/-- Expected payoff vector of tree `T` under pure profile `s`. -/
def ExtensiveTree.evalPure (s : ∀ i, PureStrategy H Act i) :
    ExtensiveTree ι H Act → ι → ℝ
  | .leaf w => w
  | @ExtensiveTree.chance _ _ _ _ instF prob _ next =>
      letI := instF
      fun j => ∑ c, prob c * ExtensiveTree.evalPure s (next c) j
  | .decision i h next => ExtensiveTree.evalPure s (next (s i h))

@[simp]
theorem ExtensiveTree.evalPure_leaf (s : ∀ i, PureStrategy H Act i) (w : ι → ℝ) :
    (@ExtensiveTree.leaf ι H Act w).evalPure s = w := by
  simp [ExtensiveTree.evalPure]

@[simp]
theorem ExtensiveTree.evalPure_chance (s : ∀ i, PureStrategy H Act i) {C : Type}
    {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
    {next : C → ExtensiveTree ι H Act} (j : ι) :
    (@ExtensiveTree.chance ι H Act C instF prob hprob next).evalPure s j =
      ∑ c, prob c * (next c).evalPure s j := by
  simp [ExtensiveTree.evalPure]

@[simp]
theorem ExtensiveTree.evalPure_decision (s : ∀ i, PureStrategy H Act i) (i : ι) (h : H i)
    (next : Act i h → ExtensiveTree ι H Act) :
    (ExtensiveTree.decision i h next).evalPure s = (next (s i h)).evalPure s := by
  simp [ExtensiveTree.evalPure]

/-- Expected payoff vector of tree `T` under behavior profile `β`. -/
def ExtensiveTree.evalBehavior [∀ i h, Fintype (Act i h)]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) : ExtensiveTree ι H Act → ι → ℝ
  | .leaf w => w
  | @ExtensiveTree.chance _ _ _ _ instF prob _ next =>
      letI := instF
      fun j => ∑ c, prob c * ExtensiveTree.evalBehavior β (next c) j
  | .decision i h next => fun j => ∑ a, β i h a * ExtensiveTree.evalBehavior β (next a) j

@[simp]
theorem ExtensiveTree.evalBehavior_leaf [∀ i h, Fintype (Act i h)]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) (w : ι → ℝ) :
    (@ExtensiveTree.leaf ι H Act w).evalBehavior β = w := by
  simp [ExtensiveTree.evalBehavior]

@[simp]
theorem ExtensiveTree.evalBehavior_chance [∀ i h, Fintype (Act i h)]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act} (j : ι) :
    (@ExtensiveTree.chance ι H Act C instF prob hprob next).evalBehavior β j =
      ∑ c, prob c * (next c).evalBehavior β j := by
  simp [ExtensiveTree.evalBehavior]

@[simp]
theorem ExtensiveTree.evalBehavior_decision [∀ i h, Fintype (Act i h)]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) (i : ι) (h : H i)
    (next : Act i h → ExtensiveTree ι H Act) (j : ι) :
    (ExtensiveTree.decision i h next).evalBehavior β j =
      ∑ a, β i h a * (next a).evalBehavior β j := by
  simp [ExtensiveTree.evalBehavior]

/-- Expected payoff vector of tree `T` under mixed profile `μ`. -/
noncomputable def ExtensiveTree.evalMixed [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) (T : ExtensiveTree ι H Act) (j : ι) : ℝ :=
  ∑ s : (∀ i, PureStrategy H Act i), (∏ i, μ i (s i)) * T.evalPure s j

/-- Unfolding equation for `ExtensiveTree.evalMixed`, whose body is not exposed. -/
theorem ExtensiveTree.evalMixed_def [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) (T : ExtensiveTree ι H Act) (j : ι) :
    T.evalMixed μ j =
      ∑ s : (∀ i, PureStrategy H Act i), (∏ i, μ i (s i)) * T.evalPure s j := by
  rw [ExtensiveTree.evalMixed]

theorem ExtensiveTree.evalPure_eq_sum_terminal [∀ i h, Fintype (Act i h)]
    [∀ i h, DecidableEq (Act i h)] (s : ∀ i, PureStrategy H Act i) :
    ∀ (T : ExtensiveTree ι H Act) (j : ι),
      T.evalPure s j = ∑ z : Terminal T, terminalProbPure s z * z.payoff j
  | .leaf w, j => by
    let e : PUnit.{max u v 1 + 1} ≃ Terminal (@ExtensiveTree.leaf ι H Act w) :=
      { toFun := fun _ => .leaf
        invFun := fun _ => PUnit.unit
        left_inv := fun _ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp]
    simp [e]
  | @ExtensiveTree.chance _ _ _ C instF prob hprob next, j => by
    let _ := instF
    let _ := Classical.decEq C
    let e : (Σ c : C, Terminal (next c)) ≃
        Terminal (@ExtensiveTree.chance ι H Act C instF prob hprob next) :=
      { toFun := fun p => .chance p.1 p.2
        invFun := fun z => match z with | .chance c sub => ⟨c, sub⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp, Fintype.sum_sigma]
    simp only [ExtensiveTree.evalPure, e, Equiv.coe_fn_mk, terminalProbPure, Terminal.payoff]
    refine sum_congr rfl fun c _ => ?_
    rw [ExtensiveTree.evalPure_eq_sum_terminal s (next c) j, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    ring
  | .decision i h next, j => by
    let _ := Classical.decEq (Act i h)
    let e : (Σ a : Act i h, Terminal (next a)) ≃ Terminal (.decision i h next) :=
      { toFun := fun p => .decision p.1 p.2
        invFun := fun z => match z with | .decision a sub => ⟨a, sub⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp, Fintype.sum_sigma]
    simp only [ExtensiveTree.evalPure, e, Equiv.coe_fn_mk, terminalProbPure, Terminal.payoff]
    rw [ExtensiveTree.evalPure_eq_sum_terminal s (next (s i h)) j]
    rw [sum_eq_single (s i h) (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp

theorem ExtensiveTree.evalBehavior_eq_sum_terminal [∀ i h, Fintype (Act i h)]
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    ∀ (T : ExtensiveTree ι H Act) (j : ι),
      T.evalBehavior β j = ∑ z : Terminal T, terminalProbBehavior β z * z.payoff j
  | .leaf w, j => by
    let e : PUnit.{max u v 1 + 1} ≃ Terminal (@ExtensiveTree.leaf ι H Act w) :=
      { toFun := fun _ => .leaf
        invFun := fun _ => PUnit.unit
        left_inv := fun _ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp]
    simp [e]
  | @ExtensiveTree.chance _ _ _ C instF prob hprob next, j => by
    let _ := instF
    let _ := Classical.decEq C
    let e : (Σ c : C, Terminal (next c)) ≃
        Terminal (@ExtensiveTree.chance ι H Act C instF prob hprob next) :=
      { toFun := fun p => .chance p.1 p.2
        invFun := fun z => match z with | .chance c sub => ⟨c, sub⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp, Fintype.sum_sigma]
    simp only [ExtensiveTree.evalBehavior, e, Equiv.coe_fn_mk, terminalProbBehavior,
      Terminal.payoff]
    refine sum_congr rfl fun c _ => ?_
    rw [ExtensiveTree.evalBehavior_eq_sum_terminal β (next c) j, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    ring
  | .decision i h next, j => by
    let _ := Classical.decEq (Act i h)
    let e : (Σ a : Act i h, Terminal (next a)) ≃ Terminal (.decision i h next) :=
      { toFun := fun p => .decision p.1 p.2
        invFun := fun z => match z with | .decision a sub => ⟨a, sub⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun z => by cases z; rfl }
    rw [← e.sum_comp, Fintype.sum_sigma]
    simp only [ExtensiveTree.evalBehavior, e, Equiv.coe_fn_mk, terminalProbBehavior,
      Terminal.payoff]
    refine sum_congr rfl fun a _ => ?_
    rw [ExtensiveTree.evalBehavior_eq_sum_terminal β (next a) j, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    ring

theorem ExtensiveTree.evalMixed_eq_sum_terminal [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    (μ : ∀ i, PureStrategy H Act i → ℝ) (T : ExtensiveTree ι H Act) (j : ι) :
    T.evalMixed μ j = ∑ z : Terminal T, terminalProbMixed μ z * z.payoff j := by
  classical
  simp only [ExtensiveTree.evalMixed, terminalProbMixed, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [ExtensiveTree.evalPure_eq_sum_terminal s T j, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  ring

/-- The strategic game in cost-minimization form induced by `T`. -/
def ExtensiveTree.toCostGame (T : ExtensiveTree ι H Act) :
    CostGame ι (fun i => PureStrategy H Act i) where
  cost i s := -T.evalPure s i

@[simp]
theorem ExtensiveTree.toCostGame_cost (T : ExtensiveTree ι H Act) (i : ι)
    (s : ∀ j, PureStrategy H Act j) :
    T.toCostGame.cost i s = -T.evalPure s i := by
  simp [ExtensiveTree.toCostGame]

/-- Under the induced strategic game `T.toCostGame`, `CostGame.expectedCost` equals the negated
extensive-form mixed payoff. -/
theorem ExtensiveTree.toCostGame_expectedCost [Fintype ι] [DecidableEq ι] [∀ i, Fintype (H i)]
    [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)] (T : ExtensiveTree ι H Act)
    (μ : ∀ i, PureStrategy H Act i → ℝ) (j : ι) :
    T.toCostGame.expectedCost μ j = -T.evalMixed μ j := by
  rw [CostGame.expectedCost_def, ExtensiveTree.evalMixed]
  simp only [ExtensiveTree.toCostGame, productWeight_def, mul_neg, sum_neg_distrib]

open Classical in
/-- Terminal-node probability when player `i` uses a sequence-factor function `r` and all other
players use pure strategies `s`. -/
noncomputable def terminalProbWithFactor [Fintype ι] [DecidableEq ι] (i : ι)
    (r : Seq H Act i → ℝ) (s : ∀ j, PureStrategy H Act j)
    {T : ExtensiveTree ι H Act} (z : Terminal T) : ℝ :=
  z.chanceWeight * r (z.seq i) *
    ∏ j ∈ univ.erase i, if MatchesSeq (s j) (z.seq j) then 1 else 0

open Classical in
/-- Unfolding equation for `terminalProbWithFactor`, whose body is not exposed. -/
theorem terminalProbWithFactor_def [Fintype ι] [DecidableEq ι] (i : ι)
    (r : Seq H Act i → ℝ) (s : ∀ j, PureStrategy H Act j)
    {T : ExtensiveTree ι H Act} (z : Terminal T) :
    terminalProbWithFactor i r s z =
      z.chanceWeight * r (z.seq i) *
        ∏ j ∈ univ.erase i, if MatchesSeq (s j) (z.seq j) then 1 else 0 := by
  rw [terminalProbWithFactor]

open Classical in
theorem terminalProbWithFactor_realizationProbMixed [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)] (i : ι)
    (μ : PureStrategy H Act i → ℝ) (s : ∀ j, PureStrategy H Act j)
    {T : ExtensiveTree ι H Act} (z : Terminal T) :
    terminalProbWithFactor i (realizationProbMixed μ) s z =
      terminalProbMixed
        (Function.update (fun j => (Pi.single (s j) (1 : ℝ) : PureStrategy H Act j → ℝ)) i μ)
        z := by
  rw [terminalProbMixed_eq, terminalProbWithFactor]
  rw [← mul_prod_erase univ _ (mem_univ i)]
  have hself : realizationProbMixed
      (Function.update (fun j => (Pi.single (s j) (1 : ℝ) : PureStrategy H Act j → ℝ)) i μ i)
        (z.seq i) = realizationProbMixed μ (z.seq i) := by
    rw [Function.update_self]
  have hother : ∀ j ∈ univ.erase i,
      realizationProbMixed
          (Function.update (fun j => (Pi.single (s j) (1 : ℝ) : PureStrategy H Act j → ℝ)) i μ j)
          (z.seq j) =
        if MatchesSeq (s j) (z.seq j) then 1 else 0 := by
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
    simp only [realizationProbMixed]
    rw [sum_eq_single (s j) (fun t _ ht => by simp [Pi.single_eq_of_ne ht]) (by simp)]
    simp
  rw [hself, prod_congr rfl hother]
  ring

theorem terminalProbWithFactor_realizationProbBehavior [Fintype ι] [DecidableEq ι]
    [∀ j h, DecidableEq (Act j h)] (i : ι) (β : ∀ h : H i, Act i h → ℝ)
    (s : ∀ j, PureStrategy H Act j) {T : ExtensiveTree ι H Act} (z : Terminal T) :
    terminalProbWithFactor i (realizationProbBehavior β) s z =
      terminalProbBehavior (Function.update (fun j => pureToBehavior (s j)) i β) z := by
  classical
  rw [terminalProbBehavior_eq, terminalProbWithFactor]
  rw [← mul_prod_erase univ _ (mem_univ i)]
  have hself : realizationProbBehavior
      (Function.update (fun j => pureToBehavior (s j)) i β i) (z.seq i) =
        realizationProbBehavior β (z.seq i) := by
    rw [Function.update_self]
  have hother : ∀ j ∈ univ.erase i,
      realizationProbBehavior (Function.update (fun j => pureToBehavior (s j)) i β j)
          (z.seq j) = if MatchesSeq (s j) (z.seq j) then 1 else 0 := by
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj), realizationProbBehavior_pureToBehavior_eq]
  rw [hself, prod_congr rfl hother]
  ring

namespace ExtensiveTree

/-- Two sequence-factor functions `r₁, r₂` of player `i` are **realization-equivalent**
([vonStengel2007], Section 3.10, p. 71) if they induce identical terminal-node probabilities against
every pure strategy profile of the remaining players. Note that [vonStengel2007] (p. 71) phrases
realization equivalence via node-reach probabilities, which coincides with equality of
terminal-leaf reach probabilities on nonempty-action finite trees. -/
@[expose] def RealizationEquivFactor [Fintype ι] [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (r₁ r₂ : Seq H Act i → ℝ) : Prop :=
  ∀ (s : ∀ j, PureStrategy H Act j) (z : Terminal T),
    terminalProbWithFactor i r₁ s z = terminalProbWithFactor i r₂ s z

/-- Realization equivalence of two mixed strategies of player `i`. -/
@[expose] def RealizationEquivMixed [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)]
    [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι)
    (μ₁ μ₂ : PureStrategy H Act i → ℝ) : Prop :=
  T.RealizationEquivFactor i (realizationProbMixed μ₁) (realizationProbMixed μ₂)

/-- Realization equivalence between a mixed strategy and a behavior strategy of player `i`. -/
@[expose] def RealizationEquivMixedBehavior [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)]
    [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι)
    (μ : PureStrategy H Act i → ℝ) (β : ∀ h : H i, Act i h → ℝ) : Prop :=
  T.RealizationEquivFactor i (realizationProbMixed μ) (realizationProbBehavior β)

theorem RealizationEquivFactor.of_forall_terminal_eq [Fintype ι] [DecidableEq ι]
    {T : ExtensiveTree ι H Act} {i : ι} {r₁ r₂ : Seq H Act i → ℝ}
    (h : ∀ z : Terminal T, r₁ (z.seq i) = r₂ (z.seq i)) :
    T.RealizationEquivFactor i r₁ r₂ := by
  intro s z
  simp only [terminalProbWithFactor, h z]

/-- Realization equivalence implies identical terminal-node probabilities against arbitrary
mixed opponent strategies. -/
theorem RealizationEquivFactor.terminalProbMixed_eq [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} [∀ h, Nonempty (Act i h)] {r₁ r₂ : Seq H Act i → ℝ}
    (heq : T.RealizationEquivFactor i r₁ r₂) (μ : ∀ j, PureStrategy H Act j → ℝ)
    (z : Terminal T) :
    z.chanceWeight * r₁ (z.seq i) *
        (∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j)) =
      z.chanceWeight * r₂ (z.seq i) *
        (∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j)) := by
  classical
  let s₀ : PureStrategy H Act i := fun h => Classical.arbitrary (Act i h)
  let g : ∀ j, PureStrategy H Act j → ℝ := fun j s_j =>
    if hj : j = i then if s_j = hj ▸ s₀ then 1 else 0 else μ j s_j
  have hprod : ∀ r : Seq H Act i → ℝ,
      z.chanceWeight * r (z.seq i) *
          (∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j)) =
        ∑ s : (∀ j, PureStrategy H Act j),
          (∏ j, g j (s j)) * terminalProbWithFactor i r s z := by
    intro r
    have hfactor : ∀ s : (∀ j, PureStrategy H Act j),
        (∏ j, g j (s j)) * terminalProbWithFactor i r s z =
          z.chanceWeight * r (z.seq i) *
            ∏ j, (if hj : j = i then if s j = hj ▸ s₀ then 1 else 0
              else if MatchesSeq (s j) (z.seq j) then μ j (s j) else 0) := by
      intro s
      simp only [terminalProbWithFactor]
      have hlhs : (∏ j, g j (s j)) *
          (∏ j ∈ univ.erase i, if MatchesSeq (s j) (z.seq j) then (1 : ℝ) else 0) =
          ∏ j, (if hj : j = i then if s j = hj ▸ s₀ then 1 else 0
            else if MatchesSeq (s j) (z.seq j) then μ j (s j) else 0) := by
        rw [← mul_prod_erase univ (fun j => g j (s j)) (mem_univ i),
          ← mul_prod_erase univ (fun j =>
            if hj : j = i then if s j = hj ▸ s₀ then (1 : ℝ) else 0
            else if MatchesSeq (s j) (z.seq j) then μ j (s j) else 0) (mem_univ i)]
        simp only [g, ↓reduceDIte]
        rw [mul_assoc]
        congr 1
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun j hj => ?_
        have hne : j ≠ i := ne_of_mem_erase hj
        simp only [hne, ↓reduceDIte]
        split_ifs <;> simp
      rw [← hlhs]
      ring
    simp_rw [hfactor, ← mul_sum]
    congr 1
    rw [(Fintype.prod_sum fun j (s_j : PureStrategy H Act j) =>
      if hj : j = i then if s_j = hj ▸ s₀ then (1 : ℝ) else 0
      else if MatchesSeq s_j (z.seq j) then μ j s_j else 0).symm]
    rw [← mul_prod_erase univ _ (mem_univ i)]
    have hi_one : (∑ s_i : PureStrategy H Act i,
        if h : i = i then if s_i = h ▸ s₀ then (1 : ℝ) else 0
        else if MatchesSeq s_i (z.seq i) then μ i s_i else 0) = 1 := by
      simp only [↓reduceDIte]
      rw [sum_eq_single s₀ (fun s_i _ hs => by simp [hs]) (by simp)]
      simp
    rw [hi_one, one_mul]
    refine prod_congr rfl fun j hj => ?_
    have hne : j ≠ i := ne_of_mem_erase hj
    simp [hne, realizationProbMixed]
  rw [hprod r₁, hprod r₂]
  refine sum_congr rfl fun s _ => ?_
  rw [heq s z]

/-- Realization equivalence of mixed strategies implies identical expected payoffs for all players
under arbitrary opponent mixed strategies. -/
theorem RealizationEquivMixed.evalMixed_eq [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} [∀ h, Nonempty (Act i h)]
    {μ₁ μ₂ : PureStrategy H Act i → ℝ}
    (heq : T.RealizationEquivMixed i μ₁ μ₂) (μ : ∀ j, PureStrategy H Act j → ℝ) (k : ι) :
    T.evalMixed (Function.update μ i μ₁) k = T.evalMixed (Function.update μ i μ₂) k := by
  simp only [ExtensiveTree.evalMixed_eq_sum_terminal]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbMixed_eq, terminalProbMixed_eq]
  have hterm : ∀ μ' : PureStrategy H Act i → ℝ,
      z.chanceWeight * ∏ j, realizationProbMixed (Function.update μ i μ' j) (z.seq j) =
        z.chanceWeight * realizationProbMixed μ' (z.seq i) *
          ∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j) := by
    intro μ'
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self, ← mul_assoc]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [hterm μ₁, hterm μ₂, heq.terminalProbMixed_eq μ z]

/-- Realization equivalence of a mixed strategy and a behavior strategy implies identical expected
payoffs against arbitrary opponent mixed strategies. -/
theorem RealizationEquivMixedBehavior.evalMixed_eq [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} [∀ h, Nonempty (Act i h)]
    {μ_i : PureStrategy H Act i → ℝ}
    {β_i : ∀ h : H i, Act i h → ℝ} (heq : T.RealizationEquivMixedBehavior i μ_i β_i)
    (μ : ∀ j, PureStrategy H Act j → ℝ) (k : ι) :
    T.evalMixed (Function.update μ i μ_i) k =
      ∑ z : Terminal T, (z.chanceWeight * realizationProbBehavior β_i (z.seq i) *
        ∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j)) * z.payoff k := by
  simp only [ExtensiveTree.evalMixed_eq_sum_terminal]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbMixed_eq]
  have hterm : z.chanceWeight * ∏ j, realizationProbMixed (Function.update μ i μ_i j) (z.seq j) =
      z.chanceWeight * realizationProbMixed μ_i (z.seq i) *
        ∏ j ∈ univ.erase i, realizationProbMixed (μ j) (z.seq j) := by
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self, ← mul_assoc]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [hterm, heq.terminalProbMixed_eq μ z]

end ExtensiveTree

/-- A node in `T`, represented by the path from the root. -/
inductive Node : ExtensiveTree ι H Act → Type (max u v 1)
  | here {T : ExtensiveTree ι H Act} : Node T
  | chance {C : Type} {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
      {next : C → ExtensiveTree ι H Act} (c : C) (sub : Node (next c)) :
      Node (@ExtensiveTree.chance ι H Act C instF prob hprob next)
  | decision {i : ι} {h : H i} {next : Act i h → ExtensiveTree ι H Act}
      (a : Act i h) (sub : Node (next a)) : Node (.decision i h next)

namespace Node

/-- Ordered sequence of `(information set, choice)` pairs made by player `i` strictly before
node `v`. -/
@[expose] def playerSeq [DecidableEq ι] (i : ι) :
    {T : ExtensiveTree ι H Act} → Node T → Seq H Act i
  | _, .here => []
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance _ sub => sub.playerSeq i
  | .decision j h _, .decision a sub =>
      if hij : j = i then (match hij with | rfl => ⟨h, a⟩) :: sub.playerSeq i
      else sub.playerSeq i

/-- `v.IsDecisionOf i h` holds when `v` is a decision node of player `i` at information set
`h`. -/
@[expose] def IsDecisionOf (i : ι) (h : H i) :
    {T : ExtensiveTree ι H Act} → Node T → Prop
  | .decision j h' _, .here => (⟨j, h'⟩ : Σ k, H k) = ⟨i, h⟩
  | _, .here => False
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance _ sub => sub.IsDecisionOf i h
  | .decision _ _ _, .decision _ sub => sub.IsDecisionOf i h

@[simp]
theorem isDecisionOf_leaf (i : ι) (h : H i) (w : ι → ℝ) :
    (Node.here (T := @ExtensiveTree.leaf ι H Act w)).IsDecisionOf i h ↔ False :=
  Iff.rfl

@[simp]
theorem isDecisionOf_chance_here (i : ι) (h : H i) {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act} :
    (Node.here (T := @ExtensiveTree.chance ι H Act C instF prob hprob next)).IsDecisionOf i h ↔
      False :=
  Iff.rfl

@[simp]
theorem isDecisionOf_decision_here (i : ι) (h : H i) (j : ι) (h' : H j)
    (next : Act j h' → ExtensiveTree ι H Act) :
    (Node.here (T := ExtensiveTree.decision j h' next)).IsDecisionOf i h ↔
      (⟨j, h'⟩ : Σ k, H k) = ⟨i, h⟩ :=
  Iff.rfl

@[simp]
theorem isDecisionOf_chance (i : ι) (h : H i) {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act}
    (c : C) (sub : Node (next c)) :
    (Node.chance (prob := prob) (hprob := hprob) c sub).IsDecisionOf i h ↔
      sub.IsDecisionOf i h :=
  Iff.rfl

@[simp]
theorem isDecisionOf_decision (i : ι) (h : H i) {j : ι} {h' : H j}
    {next : Act j h' → ExtensiveTree ι H Act} (a : Act j h') (sub : Node (next a)) :
    (Node.decision a sub).IsDecisionOf i h ↔ sub.IsDecisionOf i h :=
  Iff.rfl

@[simp]
theorem playerSeq_here [DecidableEq ι] (i : ι) (T : ExtensiveTree ι H Act) :
    (Node.here (T := T)).playerSeq i = [] :=
  rfl

@[simp]
theorem playerSeq_chance [DecidableEq ι] (i : ι) {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → ExtensiveTree ι H Act}
    (c : C) (sub : Node (next c)) :
    (Node.chance (prob := prob) (hprob := hprob) c sub).playerSeq i = sub.playerSeq i :=
  rfl

@[simp]
theorem playerSeq_decision_self [DecidableEq ι] (i : ι) {h : H i}
    {next : Act i h → ExtensiveTree ι H Act} (a : Act i h) (sub : Node (next a)) :
    (Node.decision a sub).playerSeq i = ⟨h, a⟩ :: sub.playerSeq i := by
  simp [playerSeq]

@[simp]
theorem playerSeq_decision_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) {h : H j}
    {next : Act j h → ExtensiveTree ι H Act} (a : Act j h) (sub : Node (next a)) :
    (Node.decision a sub).playerSeq i = sub.playerSeq i := by
  simp [playerSeq, hij]

end Node

namespace ExtensiveTree

/-- Information set `h : H i` occurs at some decision node of player `i` in `T`. -/
@[expose] def OccursInfoSet (T : ExtensiveTree ι H Act) (i : ι) (h : H i) : Prop :=
  ∃ v : Node T, v.IsDecisionOf i h

/-- **Perfect recall** for player `i` ([vonStengel2007], Section 3.10, p. 70): all decision nodes of
player `i` in the same information set `h : H i` are preceded by the same sequence of player-`i`
choices. -/
@[expose] def PerfectRecall [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) : Prop :=
  ∀ ⦃h : H i⦄ ⦃v₁ v₂ : Node T⦄,
    v₁.IsDecisionOf i h → v₂.IsDecisionOf i h → v₁.playerSeq i = v₂.playerSeq i

/-- No root-to-leaf play visits any information set of player `i` more than once. -/
@[expose] def NoRepeatedInfoSet [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) : Prop :=
  ∀ z : Terminal T, ((z.seq i).map Sigma.fst).Nodup

/-- If `T` has no repeated information sets for player `i`, then `behaviorToMixed β` is
realization-equivalent to `β` (in fact, agrees on all behavior opponents as well). -/
theorem NoRepeatedInfoSet.realizationEquivMixedBehavior_behaviorToMixed
    [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]
    [∀ j h, Fintype (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hnr : T.NoRepeatedInfoSet i) {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β) :
    T.RealizationEquivMixedBehavior i (behaviorToMixed β) β :=
  RealizationEquivFactor.of_forall_terminal_eq fun z =>
    realizationProbMixed_behaviorToMixed hβ (hnr z)

/-- When every player avoids visiting any information set twice, playing `behaviorToMixed (β j)`
in mixed strategies induces the same expected payoff vector as playing `β` in behavior
strategies. -/
theorem evalMixed_behaviorToMixed [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)]
    [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} (hnr : ∀ j, T.NoRepeatedInfoSet j)
    {β : ∀ j, ∀ h : H j, Act j h → ℝ} (hβ : ∀ j, IsBehaviorStrategy (β j)) (k : ι) :
    T.evalMixed (fun j => behaviorToMixed (β j)) k = T.evalBehavior β k := by
  rw [ExtensiveTree.evalMixed_eq_sum_terminal, ExtensiveTree.evalBehavior_eq_sum_terminal]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbMixed_eq, terminalProbBehavior_eq]
  congr 2
  exact prod_congr rfl fun j _ => realizationProbMixed_behaviorToMixed (hβ j) (hnr j z)

/-- Every chance node in `T` assigns positive probability to every outcome. -/
@[expose] def HasPositiveChance : ExtensiveTree ι H Act → Prop
  | .leaf _ => True
  | @ExtensiveTree.chance _ _ _ _ _ prob _ next =>
      (∀ c, 0 < prob c) ∧ ∀ c, HasPositiveChance (next c)
  | .decision _ _ next => ∀ a, HasPositiveChance (next a)

theorem HasPositiveChance.chanceWeight_pos :
    ∀ {T : ExtensiveTree ι H Act}, T.HasPositiveChance → ∀ z : Terminal T, 0 < z.chanceWeight
  | .leaf _, _, .leaf => one_pos
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, hpos, .chance c sub =>
      mul_pos (hpos.1 c) ((hpos.2 c).chanceWeight_pos sub)
  | .decision _ _ _, hpos, .decision a sub => (hpos a).chanceWeight_pos sub

private theorem exists_node_of_mem_seq [DecidableEq ι] {i : ι} {h : H i} :
    ∀ {T : ExtensiveTree ι H Act} (z : Terminal T),
      h ∈ (z.seq i).map Sigma.fst → ∃ v : Node T, v.IsDecisionOf i h
  | .leaf _, .leaf => fun hmem => by simp at hmem
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance c sub => fun hmem =>
      let ⟨v, hv⟩ := exists_node_of_mem_seq sub hmem
      ⟨.chance c v, hv⟩
  | .decision j h' _, .decision a sub => fun hmem => by
      by_cases hij : j = i
      · subst hij
        simp only [Terminal.seq_decision_self, List.map_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact ⟨.here, rfl⟩
        · obtain ⟨v, hv⟩ := exists_node_of_mem_seq sub hmem
          exact ⟨.decision a v, hv⟩
      · simp only [Terminal.seq_decision_ne hij] at hmem
        obtain ⟨v, hv⟩ := exists_node_of_mem_seq sub hmem
        exact ⟨.decision a v, hv⟩

/-- Perfect recall implies that no play visits any information set of player `i` twice. -/
theorem PerfectRecall.noRepeatedInfoSet [DecidableEq ι] :
    ∀ {T : ExtensiveTree ι H Act} {i : ι}, T.PerfectRecall i → T.NoRepeatedInfoSet i
  | .leaf _, _, _, .leaf => List.nodup_nil
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, _, hpr, .chance c sub =>
      PerfectRecall.noRepeatedInfoSet (fun h v₁ v₂ hv₁ hv₂ => by
        have := hpr (v₁ := .chance c v₁) (v₂ := .chance c v₂) hv₁ hv₂
        simpa using this) sub
  | .decision j h' next, i, hpr, .decision a sub => by
      have hsub : (next a).PerfectRecall i := fun h v₁ v₂ hv₁ hv₂ => by
        have := hpr (v₁ := .decision a v₁) (v₂ := .decision a v₂) hv₁ hv₂
        by_cases hij : j = i
        · subst hij
          simpa using this
        · simpa [hij] using this
      have hnodup := PerfectRecall.noRepeatedInfoSet hsub sub
      by_cases hij : j = i
      · subst hij
        simp only [Terminal.seq_decision_self, List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hnodup⟩
        obtain ⟨v, hv⟩ := exists_node_of_mem_seq sub hmem
        have heq := hpr (v₁ := .here) (v₂ := .decision a v) rfl hv
        simp only [Node.playerSeq_here, Node.playerSeq_decision_self] at heq
        exact absurd heq (List.cons_ne_nil _ _).symm
      · simp only [Terminal.seq_decision_ne hij]
        exact hnodup

end ExtensiveTree

end PathsAndNodes

end Cslib.GameTheory.Extensive
