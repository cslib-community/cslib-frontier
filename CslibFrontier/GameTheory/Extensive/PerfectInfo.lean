/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.MixedStrategy
public import CslibFrontier.GameTheory.Strategic.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Finite extensive games of perfect information and Zermelo's theorem

A finite extensive-form game of perfect information (`PerfectInfoTree ι`) is a finite rooted tree
whose nodes are terminal leaves with payoff vectors (`leaf`), decision nodes assigned to a player
with a nonempty finite action set (`decision`), and chance nodes with a probability distribution
(`chance`). A pure strategy of player `i` (`PureStrategy i T`) specifies an action at every
decision node of player `i` in `T`, including nodes in unreachable subtrees.

Every subgame of `T` is rooted at a node of `T`. A pure strategy profile is a *subgame-perfect
equilibrium* (`IsPureSPE`, [vonStengel2007], Section 3.8) if its restriction to every subgame is a
pure Nash equilibrium of that subgame's `CostGame` (`toCostGame`). By the one-shot deviation
principle (`isPureSPE_iff_oneShot`), this holds iff every decision node chooses a best response
given continuation equilibrium payoffs. Backward induction (`backwardInduction`, [vonStengel2007],
Algorithm 3.9 specialized to perfect-information trees) constructs a pure subgame-perfect
equilibrium (`isPureSPE_backwardInduction`), establishing Zermelo's theorem (`exists_isPureSPE`).

When continuation values at every decision node are pairwise distinct for the deciding player
(`HasNoContinuationTies`), the subgame-perfect equilibrium is unique
(`existsUnique_isPureSPE_of_hasNoContinuationTies`). In particular, for chance-free trees
(`IsDeterministic`) whose distinct leaves assign distinct payoffs to each player
(`HasDistinctLeafPayoffs`), there is a unique pure subgame-perfect equilibrium
(`existsUnique_isPureSPE`).

Contrast with `Cslib.GameTheory.PerfectInfoGame` in
`CslibFrontier.GameTheory.PerfectInformation`, which models two-player win/loss games on
descriptive set theory trees.

## Main definitions

* `Cslib.GameTheory.Extensive.PerfectInfoTree`: finite game trees of perfect information with
  leaves, decision nodes, and chance nodes.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.PureStrategy`: pure strategies of player `i` on `T`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.expectedPayoff`: expected payoff vector under a
  pure strategy profile.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toCostGame`: induced strategic game in cost form.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.IsPureSPE`: subgame-perfect equilibrium.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.BackwardInductionResult`,
  `Cslib.GameTheory.Extensive.PerfectInfoTree.backwardInduction`: backward induction strategy
  profile and equilibrium payoff vector.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.IsDeterministic`: absence of chance nodes.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.HasDistinctLeafPayoffs`: pairwise distinct leaf
  payoffs for every player.

## Main results

* `Cslib.GameTheory.Extensive.PerfectInfoTree.isPureSPE_iff_oneShot`: one-shot deviation
  principle for finite perfect-information trees.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.isPureSPE_backwardInduction`: backward induction
  produces a pure subgame-perfect equilibrium.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.exists_isPureSPE`: **Zermelo's theorem**
  ([vonStengel2007], Section 3.8, Algorithm 3.9): every finite perfect-information game tree has
  a pure subgame-perfect equilibrium (and hence a pure Nash equilibrium, `exists_isPureNash`).
* `Cslib.GameTheory.Extensive.PerfectInfoTree.existsUnique_isPureSPE`: uniqueness of the pure
  subgame-perfect equilibrium in deterministic trees with distinct leaf payoffs.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.existsUnique_isPureSPE_of_hasNoContinuationTies`:
  uniqueness when distinct actions at each decision node yield distinct continuation values for the
  deciding player.

## References

* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Section 3.8 and Algorithm 3.9.
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset

universe u

/-- A finite extensive-form game tree of perfect information over player set `ι`. -/
inductive PerfectInfoTree (ι : Type u) : Type (max u 1)
  | leaf (payoff : ι → ℝ) : PerfectInfoTree ι
  | decision (player : ι) {A : Type} [Fintype A] [Nonempty A]
      (next : A → PerfectInfoTree ι) : PerfectInfoTree ι
  | chance {C : Type} [Fintype C] (prob : C → ℝ) (hprob : IsMixedStrategy prob)
      (next : C → PerfectInfoTree ι) : PerfectInfoTree ι

namespace PerfectInfoTree

variable {ι : Type u}

/-- A pure strategy of player `i` on `T`: at every decision node of `T` belonging to `p`, it
supplies a map `p = i → A`, and recursively a strategy on every child subtree. -/
inductive PureStrategy (i : ι) : PerfectInfoTree ι → Type (max u 1)
  | leaf {w : ι → ℝ} : PureStrategy i (.leaf w)
  | decision {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
      {next : A → PerfectInfoTree ι} (choice : p = i → A)
      (sub : ∀ a, PureStrategy i (next a)) :
      PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)
  | chance {C : Type} {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
      {next : C → PerfectInfoTree ι} (sub : ∀ c, PureStrategy i (next c)) :
      PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next)

namespace PureStrategy

/-- Extract the function from `p = i` to `A` stored in a decision strategy. -/
def choiceFun {i p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)) : p = i → A :=
  match s with
  | .decision c _ => c

/-- Extract the chosen action when player `p` is the player to move at `.decision p next`. -/
def headChoice {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι}
    (s : PureStrategy p (@PerfectInfoTree.decision ι p A instF instN next)) : A :=
  s.choiceFun rfl

/-- Restrict a strategy at `.decision p next` to the child subtree for action `a`. -/
def childDecision {i p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)) (a : A) :
    PureStrategy i (next a) :=
  match s with
  | .decision _ sub => sub a

/-- Restrict a strategy at `.chance prob hprob next` to the child subtree for chance move `c`. -/
def childChance {i : ι} {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next)) (c : C) :
    PureStrategy i (next c) :=
  match s with
  | .chance sub => sub c

@[simp]
theorem choiceFun_decision {i p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι} (choice : p = i → A)
    (sub : ∀ a, PureStrategy i (next a)) :
    (PureStrategy.decision (instF := instF) (instN := instN) choice sub).choiceFun = choice := by
  simp [choiceFun]

@[simp]
theorem headChoice_decision {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι} (choice : p = p → A)
    (sub : ∀ a, PureStrategy p (next a)) :
    (PureStrategy.decision (instF := instF) (instN := instN) choice sub).headChoice =
      choice rfl := by
  simp [headChoice]

@[simp]
theorem childDecision_decision {i p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι} (choice : p = i → A)
    (sub : ∀ a, PureStrategy i (next a)) (a : A) :
    (PureStrategy.decision (instF := instF) (instN := instN) choice sub).childDecision a =
      sub a := by
  simp [childDecision]

@[simp]
theorem childChance_chance {i : ι} {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    (sub : ∀ c, PureStrategy i (next c)) (c : C) :
    (PureStrategy.chance (prob := prob) (hprob := hprob) sub).childChance c = sub c := by
  simp [childChance]

/-- Two pure strategies at a decision node coincide iff their root choices (when `p = i`) and
all child sub-strategies coincide. -/
theorem decision_ext {i p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι}
    {s₁ s₂ : PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)}
    (hhead : ∀ h : p = i, s₁.choiceFun h = s₂.choiceFun h)
    (hchild : ∀ a, s₁.childDecision a = s₂.childDecision a) : s₁ = s₂ := by
  rcases s₁ with ⟨c₁, sub₁⟩
  rcases s₂ with ⟨c₂, sub₂⟩
  exact congrArg₂ _ (funext hhead) (funext hchild)

/-- Two pure strategies at a chance node coincide iff all child sub-strategies coincide. -/
theorem chance_ext {i : ι} {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    {s₁ s₂ : PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next)}
    (hchild : ∀ c, s₁.childChance c = s₂.childChance c) : s₁ = s₂ := by
  rcases s₁ with ⟨sub₁⟩
  rcases s₂ with ⟨sub₂⟩
  exact congrArg _ (funext hchild)

/-- Every `PureStrategy i T` is nonempty because every decision node has `[Nonempty A]`. -/
instance instNonempty (i : ι) : (T : PerfectInfoTree ι) → Nonempty (PureStrategy i T)
  | .leaf _ => ⟨.leaf⟩
  | @PerfectInfoTree.decision _ _ A _ instN next =>
      letI := fun a => instNonempty i (next a)
      ⟨.decision (fun _ => @Classical.arbitrary A instN)
        (fun a => Classical.arbitrary (PureStrategy i (next a)))⟩
  | @PerfectInfoTree.chance _ _ _ _ _ next =>
      letI := fun c => instNonempty i (next c)
      ⟨.chance (fun c => Classical.arbitrary (PureStrategy i (next c)))⟩

/-- `PureStrategy i T` is finite for every player `i` and tree `T`. -/
noncomputable instance instFintype [DecidableEq ι] (i : ι) :
    (T : PerfectInfoTree ι) → Fintype (PureStrategy i T)
  | .leaf _ =>
      Fintype.ofEquiv PUnit.{max u 1 + 1}
        { toFun := fun _ => .leaf
          invFun := fun _ => PUnit.unit
          left_inv := fun _ => rfl
          right_inv := fun s => by cases s; rfl }
  | @PerfectInfoTree.decision _ p A instF instN next =>
      letI := instF
      letI := fun a => instFintype i (next a)
      letI := Classical.decEq A
      letI : Fintype (p = i → A) :=
        if h : p = i then
          Fintype.ofEquiv A
            { toFun := fun a _ => a
              invFun := fun f => f h
              left_inv := fun _ => rfl
              right_inv := fun f => funext fun h' => congrArg f (Subsingleton.elim h' h) }
        else
          Fintype.ofEquiv Unit
            { toFun := fun _ h' => absurd h' h
              invFun := fun _ => ()
              left_inv := fun _ => rfl
              right_inv := fun f => funext fun h' => absurd h' h }
      let e : ((p = i → A) × ∀ a, PureStrategy i (next a)) ≃
          PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next) :=
        { toFun := fun x => .decision x.1 x.2
          invFun := fun s => match s with | .decision c sub => (c, sub)
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun s => by cases s; rfl }
      Fintype.ofEquiv _ e
  | @PerfectInfoTree.chance _ C instF prob hprob next =>
      letI := instF
      letI := fun c => instFintype i (next c)
      letI := Classical.decEq C
      let e : (∀ c, PureStrategy i (next c)) ≃
          PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next) :=
        { toFun := fun sub => .chance sub
          invFun := fun s => match s with | .chance sub => sub
          left_inv := fun _ => rfl
          right_inv := fun s => by cases s; rfl }
      Fintype.ofEquiv _ e

end PureStrategy

/-- The expected payoff vector under a pure strategy profile `s`. -/
def expectedPayoff :
    (T : PerfectInfoTree ι) → (∀ i, PureStrategy i T) → ι → ℝ
  | .leaf w, _ => w
  | @PerfectInfoTree.decision _ p _ _ _ next, s =>
      let a := (s p).headChoice
      expectedPayoff (next a) fun i => (s i).childDecision a
  | @PerfectInfoTree.chance _ _ instF prob _ next, s =>
      letI := instF
      fun j => ∑ c, prob c * expectedPayoff (next c) (fun i => (s i).childChance c) j

@[simp]
theorem expectedPayoff_leaf (w : ι → ℝ) (s : ∀ i, PureStrategy i (.leaf w)) :
    expectedPayoff (.leaf w) s = w := by
  simp [expectedPayoff]

@[simp]
theorem expectedPayoff_decision (p : ι) {A : Type} {instF : Fintype A} {instN : Nonempty A}
    (next : A → PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)) :
    expectedPayoff (@PerfectInfoTree.decision ι p A instF instN next) s =
      expectedPayoff (next (s p).headChoice)
        (fun i => (s i).childDecision (s p).headChoice) := by
  simp [expectedPayoff]

theorem expectedPayoff_decision_of_headChoice_eq {p : ι} {A : Type} {instF : Fintype A}
    {instN : Nonempty A} {next : A → PerfectInfoTree ι}
    {s : ∀ i, PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)} {a : A}
    (ha : (s p).headChoice = a) :
    expectedPayoff (@PerfectInfoTree.decision ι p A instF instN next) s =
      expectedPayoff (next a) (fun i => (s i).childDecision a) := by
  rw [expectedPayoff_decision, ha]

@[simp]
theorem expectedPayoff_chance {C : Type} [Fintype C] (prob : C → ℝ)
    (hprob : IsMixedStrategy prob) (next : C → PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i (.chance prob hprob next)) (j : ι) :
    expectedPayoff (.chance prob hprob next) s j =
      ∑ c, prob c * expectedPayoff (next c) (fun i => (s i).childChance c) j := by
  simp [expectedPayoff]

/-- The strategic game in cost-minimization form induced by `T`: player `i`'s cost is its negated
expected payoff. -/
def toCostGame (T : PerfectInfoTree ι) : CostGame ι (fun i => PureStrategy i T) where
  cost i s := -T.expectedPayoff s i

@[simp]
theorem toCostGame_cost (T : PerfectInfoTree ι) (i : ι) (s : ∀ j, PureStrategy j T) :
    T.toCostGame.cost i s = -T.expectedPayoff s i := by
  simp [toCostGame]

/-- Output of backward induction on `T`: a pure strategy profile together with its equilibrium
payoff vector. -/
structure BackwardInductionResult (T : PerfectInfoTree ι) : Type (max u 1) where
  /-- The strategy profile chosen by backward induction. -/
  strategy : ∀ i, PureStrategy i T
  /-- The subgame-perfect equilibrium payoff vector induced by `strategy`. -/
  payoff : ι → ℝ

/-- **Backward induction** ([vonStengel2007], Algorithm 3.9 specialized to finite
perfect-information trees): computes a pure strategy profile and its equilibrium payoff vector by
bottom-up recursion. -/
noncomputable def backwardInduction :
    (T : PerfectInfoTree ι) → BackwardInductionResult T
  | .leaf w => ⟨fun _ => .leaf, w⟩
  | @PerfectInfoTree.decision _ p _ instF instN next =>
      letI := instF
      letI := instN
      let recRes := fun a => backwardInduction (next a)
      let aStar := (Finset.univ.exists_max_image (fun a => (recRes a).payoff p)
        Finset.univ_nonempty).choose
      let s := fun i => PureStrategy.decision (fun _ => aStar) fun a => (recRes a).strategy i
      ⟨s, (recRes aStar).payoff⟩
  | @PerfectInfoTree.chance _ _ instF prob _ next =>
      letI := instF
      let recRes := fun c => backwardInduction (next c)
      let s := fun i => PureStrategy.chance fun c => (recRes c).strategy i
      ⟨s, fun j => ∑ c, prob c * (recRes c).payoff j⟩

/-- The payoff vector returned by `backwardInduction` equals the expected payoff of its strategy
profile. -/
theorem backwardInduction_payoff :
    ∀ T : PerfectInfoTree ι,
      T.backwardInduction.payoff = T.expectedPayoff T.backwardInduction.strategy
  | .leaf _ => by simp [backwardInduction]
  | @PerfectInfoTree.decision _ p _ instF instN next => by
    let _ := instF
    let _ := instN
    simp only [backwardInduction, expectedPayoff_decision, PureStrategy.childDecision_decision]
    exact backwardInduction_payoff (next _)
  | @PerfectInfoTree.chance _ _ instF prob hprob next => by
    let _ := instF
    ext j
    simp only [backwardInduction, expectedPayoff_chance, PureStrategy.childChance_chance]
    exact sum_congr rfl fun c _ => by rw [backwardInduction_payoff (next c)]

@[simp]
theorem backwardInduction_leaf_payoff (w : ι → ℝ) :
    (PerfectInfoTree.leaf w).backwardInduction.payoff = w := by
  simp [backwardInduction]

@[simp]
theorem backwardInduction_chance_payoff {C : Type} [Fintype C] (prob : C → ℝ)
    (hprob : IsMixedStrategy prob) (next : C → PerfectInfoTree ι) (j : ι) :
    (PerfectInfoTree.chance prob hprob next).backwardInduction.payoff j =
      ∑ c, prob c * (next c).backwardInduction.payoff j := by
  simp [backwardInduction]

section SubgamePerfect

variable [DecidableEq ι]

/-- A pure strategy profile `s` is a **subgame-perfect equilibrium** (`IsPureSPE`,
[vonStengel2007], Section 3.8) of `T` if its restriction to every subgame of `T` is a pure Nash
equilibrium of that subgame. -/
@[expose] def IsPureSPE : (T : PerfectInfoTree ι) → (∀ i, PureStrategy i T) → Prop
  | .leaf _, _ => True
  | @PerfectInfoTree.decision _ p A instF instN next, s =>
      (@PerfectInfoTree.decision ι p A instF instN next).toCostGame.IsPureNash s ∧
        ∀ a, IsPureSPE (next a) fun i => (s i).childDecision a
  | @PerfectInfoTree.chance _ C instF prob hprob next, s =>
      (@PerfectInfoTree.chance ι C instF prob hprob next).toCostGame.IsPureNash s ∧
        ∀ c, IsPureSPE (next c) fun i => (s i).childChance c

/-- Every subgame-perfect equilibrium of `T` is a pure Nash equilibrium of `T.toCostGame`. -/
theorem IsPureSPE.isPureNash {T : PerfectInfoTree ι} {s : ∀ i, PureStrategy i T}
    (hs : T.IsPureSPE s) : T.toCostGame.IsPureNash s := by
  cases T with
  | leaf _ => exact fun _ _ => le_rfl
  | decision _ _ | chance _ _ _ => exact hs.1

/-- Local optimality at every decision node (the one-shot deviation condition): at every
`.decision p next`, player `p`'s chosen action achieves at least the payoff of any alternative
action given the continuation strategy profile. -/
@[expose] def IsLocallyOptimal : (T : PerfectInfoTree ι) → (∀ i, PureStrategy i T) → Prop
  | .leaf _, _ => True
  | @PerfectInfoTree.decision _ p _ _ _ next, s =>
      (∀ a, expectedPayoff (next a) (fun i => (s i).childDecision a) p ≤
        expectedPayoff (next (s p).headChoice)
          (fun i => (s i).childDecision (s p).headChoice) p) ∧
        ∀ a, IsLocallyOptimal (next a) fun i => (s i).childDecision a
  | @PerfectInfoTree.chance _ _ _ _ _ next, s =>
      ∀ c, IsLocallyOptimal (next c) fun i => (s i).childChance c

private theorem childDecision_update_eq {i p : ι} {A : Type} {instF : Fintype A}
    {instN : Nonempty A} {next : A → PerfectInfoTree ι}
    (s : ∀ j, PureStrategy j (@PerfectInfoTree.decision ι p A instF instN next))
    (σ' : PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next)) (a : A) :
    (fun j => (Function.update s i σ' j).childDecision a) =
      Function.update (fun j => (s j).childDecision a) i (σ'.childDecision a) := by
  funext j
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

private theorem childChance_update_eq {i : ι} {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    (s : ∀ j, PureStrategy j (@PerfectInfoTree.chance ι C instF prob hprob next))
    (σ' : PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next)) (c : C) :
    (fun j => (Function.update s i σ' j).childChance c) =
      Function.update (fun j => (s j).childChance c) i (σ'.childChance c) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

/-- **One-shot deviation principle** for finite extensive games of perfect information: a pure
strategy profile is a subgame-perfect equilibrium iff no player can strictly gain by a single
deviation at any decision node. -/
theorem isPureSPE_iff_oneShot :
    ∀ {T : PerfectInfoTree ι} {s : ∀ i, PureStrategy i T},
      T.IsPureSPE s ↔ T.IsLocallyOptimal s
  | .leaf w, s => by simp [IsPureSPE, IsLocallyOptimal]
  | @PerfectInfoTree.decision _ p A instF instN next, s => by
    refine ⟨fun ⟨hnash, hsub⟩ => ⟨fun a => ?_, fun a => isPureSPE_iff_oneShot.1 (hsub a)⟩,
      fun ⟨hroot, hsub⟩ => ?_⟩
    · have hdev := hnash p (.decision (fun _ => a) fun a' => (s p).childDecision a')
      simp only [toCostGame, neg_le_neg_iff, expectedPayoff_decision] at hdev
      rw [Function.update_self, PureStrategy.headChoice_decision] at hdev
      simpa [childDecision_update_eq] using hdev
    · have hspe := fun a => isPureSPE_iff_oneShot.2 (hsub a)
      refine ⟨fun i σ' => ?_, hspe⟩
      simp only [toCostGame, neg_le_neg_iff, expectedPayoff_decision, childDecision_update_eq]
      by_cases hi : i = p
      · subst hi
        rw [Function.update_self]
        exact (hroot σ'.headChoice).trans' (by
          simpa [toCostGame] using
            (hspe σ'.headChoice).isPureNash i (σ'.childDecision σ'.headChoice))
      · rw [Function.update_of_ne (Ne.symm hi)]
        simpa [toCostGame] using
          (hspe (s p).headChoice).isPureNash i (σ'.childDecision (s p).headChoice)
  | @PerfectInfoTree.chance _ C instF prob hprob next, s => by
    let _ := instF
    refine ⟨fun ⟨_, hsub⟩ c => isPureSPE_iff_oneShot.1 (hsub c), fun hsub => ?_⟩
    have hspe := fun c => isPureSPE_iff_oneShot.2 (hsub c)
    refine ⟨fun i σ' => ?_, hspe⟩
    simp only [toCostGame, expectedPayoff_chance, neg_le_neg_iff, childChance_update_eq]
    exact sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
      (by simpa [toCostGame] using (hspe c).isPureNash i (σ'.childChance c)) (hprob.nonneg c)

/-- Backward induction produces a pure subgame-perfect equilibrium ([vonStengel2007], Section 3.8,
Algorithm 3.9). -/
theorem isPureSPE_backwardInduction :
    ∀ T : PerfectInfoTree ι, T.IsPureSPE T.backwardInduction.strategy
  | .leaf _ => trivial
  | @PerfectInfoTree.decision _ p A instF instN next => by
    let _ := instF
    let _ := instN
    rw [isPureSPE_iff_oneShot]
    have hmax := (Finset.univ.exists_max_image
      (fun a => (next a).backwardInduction.payoff p) Finset.univ_nonempty).choose_spec
    refine ⟨fun a => ?_, fun a => ?_⟩
    · simp only [backwardInduction, PureStrategy.childDecision_decision]
      rw [← backwardInduction_payoff (next a), ← backwardInduction_payoff (next _)]
      exact hmax.2 a (mem_univ a)
    · simp only [backwardInduction, PureStrategy.childDecision_decision]
      exact (isPureSPE_iff_oneShot).1 (isPureSPE_backwardInduction (next a))
  | @PerfectInfoTree.chance _ C instF prob hprob next => by
    let _ := instF
    exact isPureSPE_iff_oneShot.2 fun c => by
      simpa only [backwardInduction, PureStrategy.childChance_chance] using
        isPureSPE_iff_oneShot.1 (isPureSPE_backwardInduction (next c))

/-- **Zermelo's theorem** ([vonStengel2007], Section 3.8, Algorithm 3.9): every finite game tree
of perfect information (with arbitrary finite player set and optional chance nodes) possesses a
pure subgame-perfect equilibrium. -/
theorem exists_isPureSPE (T : PerfectInfoTree ι) : ∃ s, T.IsPureSPE s :=
  ⟨T.backwardInduction.strategy, isPureSPE_backwardInduction T⟩

/-- Every finite game tree of perfect information possesses a pure Nash equilibrium in its
strategic form. -/
theorem exists_isPureNash (T : PerfectInfoTree ι) : ∃ s, T.toCostGame.IsPureNash s :=
  ⟨T.backwardInduction.strategy, (isPureSPE_backwardInduction T).isPureNash⟩

end SubgamePerfect

section Uniqueness

/-- A root-to-leaf path in `T`. -/
inductive LeafPath : PerfectInfoTree ι → Type (max u 1)
  | leaf {w : ι → ℝ} : LeafPath (.leaf w)
  | decision {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
      {next : A → PerfectInfoTree ι} (a : A) (sub : LeafPath (next a)) :
      LeafPath (@PerfectInfoTree.decision ι p A instF instN next)
  | chance {C : Type} {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
      {next : C → PerfectInfoTree ι} (c : C) (sub : LeafPath (next c)) :
      LeafPath (@PerfectInfoTree.chance ι C instF prob hprob next)

/-- The payoff vector at a terminal leaf of `T`. -/
def LeafPath.payoff : {T : PerfectInfoTree ι} → LeafPath T → ι → ℝ
  | .leaf w, .leaf => w
  | @PerfectInfoTree.decision _ _ _ _ _ _, .decision _ sub => sub.payoff
  | @PerfectInfoTree.chance _ _ _ _ _ _, .chance _ sub => sub.payoff

@[simp]
theorem LeafPath.payoff_leaf (w : ι → ℝ) :
    (LeafPath.leaf (w := w)).payoff = w := by
  simp [LeafPath.payoff]

@[simp]
theorem LeafPath.payoff_decision {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι} (a : A) (sub : LeafPath (next a)) :
    (LeafPath.decision (p := p) (instF := instF) (instN := instN) a sub).payoff = sub.payoff := by
  simp [LeafPath.payoff]

@[simp]
theorem LeafPath.payoff_chance {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι} (c : C)
    (sub : LeafPath (next c)) :
    (LeafPath.chance (prob := prob) (hprob := hprob) c sub).payoff = sub.payoff := by
  simp [LeafPath.payoff]

/-- A tree is deterministic if it contains no chance nodes. -/
@[expose] def IsDeterministic : PerfectInfoTree ι → Prop
  | .leaf _ => True
  | @PerfectInfoTree.decision _ _ _ _ _ next => ∀ a, IsDeterministic (next a)
  | @PerfectInfoTree.chance _ _ _ _ _ _ => False

/-- Distinct leaves of `T` assign distinct payoffs to every player. -/
@[expose] def HasDistinctLeafPayoffs (T : PerfectInfoTree ι) : Prop :=
  ∀ z₁ z₂ : LeafPath T, z₁ ≠ z₂ → ∀ i, z₁.payoff i ≠ z₂.payoff i

/-- No decision node in `T` has a tie in backward-induction continuation payoffs for the
deciding player across distinct actions. -/
@[expose] def HasNoContinuationTies : PerfectInfoTree ι → Prop
  | .leaf _ => True
  | @PerfectInfoTree.decision _ p _ _ _ next =>
      (∀ a₁ a₂, a₁ ≠ a₂ →
          (next a₁).backwardInduction.payoff p ≠ (next a₂).backwardInduction.payoff p) ∧
        ∀ a, HasNoContinuationTies (next a)
  | @PerfectInfoTree.chance _ _ _ _ _ next => ∀ c, HasNoContinuationTies (next c)

private theorem hasDistinctLeafPayoffs_childDecision {p : ι} {A : Type} {instF : Fintype A}
    {instN : Nonempty A} {next : A → PerfectInfoTree ι}
    (h : HasDistinctLeafPayoffs (@PerfectInfoTree.decision ι p A instF instN next)) (a : A) :
    HasDistinctLeafPayoffs (next a) := by
  intro z₁ z₂ hne i
  exact h (.decision a z₁) (.decision a z₂) (fun heq => by cases heq; exact hne rfl) i

/-- In a deterministic tree, the backward-induction payoff vector equals the payoff of some
terminal leaf. -/
theorem IsDeterministic.exists_leafPath_backwardInduction :
    ∀ {T : PerfectInfoTree ι}, T.IsDeterministic →
      ∃ z : LeafPath T, T.backwardInduction.payoff = z.payoff
  | .leaf _, _ => ⟨.leaf, rfl⟩
  | @PerfectInfoTree.decision _ p A instF instN next, hdet => by
    let _ := instF
    let _ := instN
    let aStar := (Finset.univ.exists_max_image
      (fun a => (next a).backwardInduction.payoff p) Finset.univ_nonempty).choose
    obtain ⟨z, hz⟩ := IsDeterministic.exists_leafPath_backwardInduction (hdet aStar)
    exact ⟨.decision aStar z, hz⟩
  | @PerfectInfoTree.chance _ _ _ _ _ _, hdet => False.elim hdet

/-- A deterministic tree with distinct leaf payoffs has no continuation ties. -/
theorem IsDeterministic.hasNoContinuationTies :
    ∀ {T : PerfectInfoTree ι}, T.IsDeterministic → T.HasDistinctLeafPayoffs →
      T.HasNoContinuationTies
  | .leaf _, _, _ => trivial
  | @PerfectInfoTree.decision _ p _ _ _ next, hdet, hdist => by
    refine ⟨fun a₁ a₂ hne => ?_, fun a =>
      IsDeterministic.hasNoContinuationTies (hdet a) (hasDistinctLeafPayoffs_childDecision hdist a)⟩
    obtain ⟨z₁, hz₁⟩ := IsDeterministic.exists_leafPath_backwardInduction (hdet a₁)
    obtain ⟨z₂, hz₂⟩ := IsDeterministic.exists_leafPath_backwardInduction (hdet a₂)
    rw [hz₁, hz₂]
    exact hdist (.decision a₁ z₁) (.decision a₂ z₂) (fun heq => by cases heq; exact hne rfl) p
  | @PerfectInfoTree.chance _ _ _ _ _ _, hdet, _ => False.elim hdet

/-- When distinct actions at every decision node yield distinct backward-induction continuation
payoffs for the deciding player, every pure subgame-perfect equilibrium coincides with
`backwardInduction`. -/
theorem eq_backwardInduction_of_isPureSPE [DecidableEq ι] :
    ∀ {T : PerfectInfoTree ι} {s : ∀ i, PureStrategy i T},
      T.HasNoContinuationTies → T.IsPureSPE s → s = T.backwardInduction.strategy
  | .leaf _, s, _, _ => funext fun i => by
    cases s i
    rfl
  | @PerfectInfoTree.decision _ p A instF instN next, s, ⟨htie, hsub⟩, hspe => by
    let _ := instF
    let _ := instN
    have hchild := fun a => eq_backwardInduction_of_isPureSPE (hsub a) (hspe.2 a)
    have hval (a : A) : expectedPayoff (next a) (fun i => (s i).childDecision a) =
        (next a).backwardInduction.payoff := by
      rw [hchild a, ← backwardInduction_payoff (next a)]
    have hopt := (isPureSPE_iff_oneShot.1 hspe).1
    have hex := Finset.univ.exists_max_image (fun a => (next a).backwardInduction.payoff p)
      Finset.univ_nonempty
    have ha : (s p).headChoice = hex.choose := by
      by_contra hne
      exact htie _ _ hne (le_antisymm (hex.choose_spec.2 _ (mem_univ _))
        (by simpa [hval] using hopt hex.choose))
    exact funext fun i => PureStrategy.decision_ext (fun | rfl => ha) fun a =>
      congrFun (hchild a) i
  | @PerfectInfoTree.chance _ _ instF prob hprob next, s, htie, hspe => by
    let _ := instF
    exact funext fun i => PureStrategy.chance_ext fun c =>
      congrFun (eq_backwardInduction_of_isPureSPE (htie c) (hspe.2 c)) i

/-- Under `HasNoContinuationTies`, `T` has a unique pure subgame-perfect equilibrium. -/
theorem existsUnique_isPureSPE_of_hasNoContinuationTies [DecidableEq ι]
    {T : PerfectInfoTree ι} (htie : T.HasNoContinuationTies) :
    ∃! s, T.IsPureSPE s :=
  ⟨T.backwardInduction.strategy, isPureSPE_backwardInduction T,
    fun _ hs => eq_backwardInduction_of_isPureSPE htie hs⟩

/-- **Uniqueness of pure subgame-perfect equilibrium**: every deterministic finite
perfect-information game tree with pairwise distinct leaf payoffs has a unique pure
subgame-perfect equilibrium (a corollary of `existsUnique_isPureSPE_of_hasNoContinuationTies`). -/
theorem existsUnique_isPureSPE [DecidableEq ι] {T : PerfectInfoTree ι}
    (hdet : T.IsDeterministic) (hdist : T.HasDistinctLeafPayoffs) :
    ∃! s, T.IsPureSPE s :=
  existsUnique_isPureSPE_of_hasNoContinuationTies (hdet.hasNoContinuationTies hdist)

end Uniqueness

end PerfectInfoTree

end Cslib.GameTheory.Extensive
