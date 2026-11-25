/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Extensive.Basic
public import CslibFrontier.GameTheory.Extensive.PerfectInfo
public import CslibFrontier.GameTheory.Extensive.SequenceForm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum

/-!
# Embedding perfect-information trees into extensive-form games

Every finite perfect-information game tree (`PerfectInfoTree ι`) embeds into an extensive-form game
tree (`ExtensiveTree`) in which each decision node of player `i` forms its own singleton information
set (`PerfectInfoTree.InfoSet`) ([vonStengel2007], Section 3.7).

Every node of `T.toExtensiveTree` matching an information set `h` of player `i` is unique
(`toExtensiveTree_isSingletonInfoSet`), so `T.toExtensiveTree` has perfect recall for every player
(`toExtensiveTree_perfectRecall`). Under the canonical pure-strategy bijection
`PureStrategy.toExtensiveEquiv`, extensive-form payoffs coincide with `T.expectedPayoff`
(`toExtensiveTree_evalPure`, `toExtensiveTree_evalPure_ofExtensive`), strategic-form pure and
mixed Nash equilibria coincide (`toExtensiveTree_isPureNash_iff`,
`toExtensiveTree_isMixedNash_iff`), backward induction yields a Nash equilibrium of the embedded
game (`toExtensiveTree_backwardInduction_isPureNash`), and Kuhn's theorem applies directly
(`toExtensiveTree_kuhn_theorem`).

## Main definitions

* `Cslib.GameTheory.Extensive.PerfectInfoTree.InfoSet`: decision nodes of player `i` inside `T`,
  serving as singleton information sets.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.InfoSet.Act`: available action type at
  `h : T.InfoSet i`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree`: canonical embedding of `T` into
  `ExtensiveTree`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.PureStrategy.toExtensiveEquiv`: bijection between
  `PerfectInfoTree.PureStrategy` and `Extensive.PureStrategy` on `T.toExtensiveTree`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.leafPathEquivTerminal`: bijection between root-to-leaf
  paths in `T` and terminal paths in `T.toExtensiveTree`.

## Main results

* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isSingletonInfoSet`: every
  information set of `T.toExtensiveTree` contains at most one decision node.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_perfectRecall`: every embedded
  perfect-information tree satisfies `PerfectRecall` for all players.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_noRepeatedInfoSet`: no play in
  `T.toExtensiveTree` visits any information set twice.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_evalPure`,
  `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_evalPure_ofExtensive`: pure payoffs
  agree under the embedding.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_backwardInduction_isPureNash`:
  backward induction produces a pure Nash equilibrium of `(T.toExtensiveTree).toCostGame`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isPureNash_iff`,
  `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isMixedNash_iff`: pure and mixed
  Nash equilibria match across `T.toCostGame` and `(T.toExtensiveTree).toCostGame`.
* `Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_kuhn_theorem`: Kuhn's theorem for
  `T.toExtensiveTree`.

## References

* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Sections 3.7–3.10.
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset

universe u v

namespace PerfectInfoTree

/-! ### Singleton information sets and the tree embedding -/

/-- Decision node of player `i` inside `T : PerfectInfoTree ι`, serving as its singleton
information set in `T.toExtensiveTree` ([vonStengel2007], Section 3.7). -/
inductive InfoSet {ι : Type u} (i : ι) : PerfectInfoTree ι → Type (max u 1)
  | here {A : Type} {instF : Fintype A} {instN : Nonempty A}
      {next : A → PerfectInfoTree ι} :
      InfoSet i (@PerfectInfoTree.decision ι i A instF instN next)
  | decision {p : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
      {next : A → PerfectInfoTree ι} (a : A) (sub : InfoSet i (next a)) :
      InfoSet i (@PerfectInfoTree.decision ι p A instF instN next)
  | chance {C : Type} {instF : Fintype C} {prob : C → ℝ} {hprob : IsMixedStrategy prob}
      {next : C → PerfectInfoTree ι} (c : C) (sub : InfoSet i (next c)) :
      InfoSet i (@PerfectInfoTree.chance ι C instF prob hprob next)

namespace InfoSet

/-- The finite nonempty action type available at singleton information set `h`. -/
@[expose, reducible] def Act {ι : Type u} {i : ι} :
    {T : PerfectInfoTree ι} → T.InfoSet i → Type
  | _, @InfoSet.here _ _ A _ _ _ => A
  | _, .decision _ sub => sub.Act
  | _, .chance _ sub => sub.Act

instance instFintypeAct {ι : Type u} {i : ι} :
    {T : PerfectInfoTree ι} → (h : T.InfoSet i) → Fintype h.Act
  | _, @InfoSet.here _ _ _ instF _ _ => instF
  | _, .decision _ sub => instFintypeAct sub
  | _, .chance _ sub => instFintypeAct sub

instance instNonemptyAct {ι : Type u} {i : ι} :
    {T : PerfectInfoTree ι} → (h : T.InfoSet i) → Nonempty h.Act
  | _, @InfoSet.here _ _ _ _ instN _ => instN
  | _, .decision _ sub => instNonemptyAct sub
  | _, .chance _ sub => instNonemptyAct sub

noncomputable instance instFintype {ι : Type u} [DecidableEq ι] (i : ι) :
    (T : PerfectInfoTree ι) → Fintype (T.InfoSet i)
  | .leaf _ =>
      Fintype.ofEquiv Empty
        { toFun := fun e => Empty.elim e
          invFun := fun h => nomatch h
          left_inv := fun e => Empty.elim e
          right_inv := fun h => nomatch h }
  | @PerfectInfoTree.decision _ p A instF instN next =>
      if hp : p = i then by
        subst hp
        letI := instF
        letI := Classical.decEq A
        letI := fun a => instFintype p (next a)
        exact Fintype.ofEquiv (PUnit.{max u 1 + 1} ⊕ Σ a : A, (next a).InfoSet p)
          { toFun := fun x => match x with
              | .inl .unit => .here
              | .inr ⟨a, sub⟩ => .decision a sub
            invFun := fun h => match h with
              | .here => .inl .unit
              | .decision a sub => .inr ⟨a, sub⟩
            left_inv := fun x => by cases x with | inl u => cases u; rfl | inr q => rfl
            right_inv := fun h => by cases h <;> rfl }
      else by
        letI := instF
        letI := Classical.decEq A
        letI := fun a => instFintype i (next a)
        exact Fintype.ofEquiv (Σ a : A, (next a).InfoSet i)
          { toFun := fun ⟨a, sub⟩ => .decision a sub
            invFun := fun h => match h with
              | .here => False.elim (hp rfl)
              | .decision a sub => ⟨a, sub⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun h => by
              cases h with
              | here => exact absurd rfl hp
              | decision _ _ => rfl }
  | @PerfectInfoTree.chance _ C instF prob hprob next =>
      letI := instF
      letI := Classical.decEq C
      letI := fun c => instFintype i (next c)
      Fintype.ofEquiv (Σ c : C, (next c).InfoSet i)
        { toFun := fun ⟨c, sub⟩ => .chance c sub
          invFun := fun h => match h with | .chance c sub => ⟨c, sub⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun h => by cases h; rfl }

end InfoSet

/-- Embed `T : PerfectInfoTree ι` into an extensive-form game with given information-set map `f`
and action-type equivalences `eqv`. -/
def toExtensiveTreeOn {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type} :
    (T : PerfectInfoTree ι) →
    (f : ∀ i, T.InfoSet i → H i) →
    (∀ i (h : T.InfoSet i), Act i (f i h) ≃ h.Act) →
    ExtensiveTree ι H Act
  | .leaf w, _, _ => .leaf w
  | @PerfectInfoTree.chance _ _ _ prob hprob next, f, eqv =>
      .chance prob hprob fun c =>
        toExtensiveTreeOn (next c) (fun i h => f i (.chance c h))
          (fun i h => eqv i (.chance c h))
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv =>
      .decision p (f p .here) fun a =>
        let a' := eqv p .here a
        toExtensiveTreeOn (next a') (fun i h => f i (.decision a' h))
          (fun i h => eqv i (.decision a' h))

@[simp]
theorem toExtensiveTreeOn_leaf {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}
    (w : ι → ℝ) (f : ∀ i, (PerfectInfoTree.leaf w).InfoSet i → H i)
    (eqv : ∀ i (h : (PerfectInfoTree.leaf w).InfoSet i), Act i (f i h) ≃ h.Act) :
    (PerfectInfoTree.leaf w).toExtensiveTreeOn f eqv = .leaf w := by
  simp [toExtensiveTreeOn]

@[simp]
theorem toExtensiveTreeOn_chance {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}
    {C : Type} [Fintype C] (prob : C → ℝ) (hprob : IsMixedStrategy prob)
    (next : C → PerfectInfoTree ι)
    (f : ∀ i, (PerfectInfoTree.chance prob hprob next).InfoSet i → H i)
    (eqv : ∀ i (h : (PerfectInfoTree.chance prob hprob next).InfoSet i),
      Act i (f i h) ≃ h.Act) :
    (PerfectInfoTree.chance prob hprob next).toExtensiveTreeOn f eqv =
      .chance prob hprob fun c =>
        toExtensiveTreeOn (next c) (fun i h => f i (.chance c h))
          (fun i h => eqv i (.chance c h)) := by
  simp [toExtensiveTreeOn]

@[simp]
theorem toExtensiveTreeOn_decision {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}
    (p : ι) {A : Type} [instF : Fintype A] [instN : Nonempty A]
    (next : A → PerfectInfoTree ι)
    (f : ∀ i, (@PerfectInfoTree.decision ι p A instF instN next).InfoSet i → H i)
    (eqv : ∀ i (h : (@PerfectInfoTree.decision ι p A instF instN next).InfoSet i),
      Act i (f i h) ≃ h.Act) :
    (@PerfectInfoTree.decision ι p A instF instN next).toExtensiveTreeOn f eqv =
      .decision p (f p .here) fun a =>
        let a' := eqv p .here a
        toExtensiveTreeOn (next a') (fun i h => f i (.decision a' h))
          (fun i h => eqv i (.decision a' h)) := by
  simp [toExtensiveTreeOn]

/-- Canonical embedding of a finite perfect-information tree `T` into `ExtensiveTree`, assigning
a singleton information set `T.InfoSet i` to each decision node of player `i`
([vonStengel2007], Section 3.7). -/
def toExtensiveTree {ι : Type u} (T : PerfectInfoTree ι) :
    ExtensiveTree ι T.InfoSet (fun _ h => h.Act) :=
  T.toExtensiveTreeOn (fun _ h => h) (fun _ _ => Equiv.refl _)

theorem toExtensiveTree_def {ι : Type u} (T : PerfectInfoTree ι) :
    T.toExtensiveTree = T.toExtensiveTreeOn (fun _ h => h) (fun _ _ => Equiv.refl _) := by
  rw [toExtensiveTree]

/-! ### Singleton information sets and perfect recall -/

private theorem exists_infoSet_of_isDecisionOf {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} {f : ∀ j, T.InfoSet j → H j}
      {eqv : ∀ j h, Act j (f j h) ≃ h.Act}
      {i : ι} {h₀ : H i} {v : Node (T.toExtensiveTreeOn f eqv)},
      v.IsDecisionOf i h₀ → ∃ h : T.InfoSet i, f i h = h₀
  | .leaf _, _, _, _, _, .here, hv => False.elim hv
  | @PerfectInfoTree.chance _ _ _ _ _ _, _, _, _, _, .here, hv => False.elim hv
  | @PerfectInfoTree.chance _ _ _ _ _ next, f, eqv, i, h₀, .chance c sub, hv => by
      obtain ⟨h, hh⟩ := exists_infoSet_of_isDecisionOf (T := next c) hv
      exact ⟨.chance c h, hh⟩
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, i, h₀, .here, hv => by
      have hp : p = i := (Sigma.mk.inj_iff.1 hv).1
      cases hp
      have hf : f p .here = h₀ := eq_of_heq (Sigma.mk.inj_iff.1 hv).2
      exact ⟨.here, hf⟩
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, i, h₀, .decision a sub, hv => by
      obtain ⟨h, hh⟩ := exists_infoSet_of_isDecisionOf (T := next (eqv p .here a)) hv
      exact ⟨.decision (eqv p .here a) h, hh⟩

/-- Whenever `f` maps distinct decision nodes to distinct information sets, every information set
of `T.toExtensiveTreeOn f eqv` contains at most one decision node. -/
theorem eq_of_isDecisionOf_toExtensiveTreeOn {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} {f : ∀ j, T.InfoSet j → H j}
      {eqv : ∀ j h, Act j (f j h) ≃ h.Act},
      (∀ j, Function.Injective (f j)) →
      ∀ {i : ι} {h₀ : H i} {v₁ v₂ : Node (T.toExtensiveTreeOn f eqv)},
        v₁.IsDecisionOf i h₀ → v₂.IsDecisionOf i h₀ → v₁ = v₂
  | .leaf _, _, _, _, _, _, .here, _, hv₁, _ => False.elim hv₁
  | @PerfectInfoTree.chance _ _ _ _ _ _, _, _, _, _, _, .here, _, hv₁, _ => False.elim hv₁
  | @PerfectInfoTree.chance _ _ _ _ _ _, _, _, _, _, _, .chance _ _, .here, _, hv₂ =>
      False.elim hv₂
  | @PerfectInfoTree.chance _ _ _ _ _ next, f, eqv, hf, i, h₀,
      .chance c₁ sub₁, .chance c₂ sub₂, hv₁, hv₂ => by
      obtain ⟨h₁, hh₁⟩ := exists_infoSet_of_isDecisionOf (T := next c₁) hv₁
      obtain ⟨h₂, hh₂⟩ := exists_infoSet_of_isDecisionOf (T := next c₂) hv₂
      have hinj := hf i (hh₁.trans hh₂.symm)
      cases hinj
      have hsub := eq_of_isDecisionOf_toExtensiveTreeOn (T := next c₁)
        (fun j _ _ he => by
          have := hf j he
          exact (InfoSet.chance.inj this).2 |> eq_of_heq) hv₁ hv₂
      subst hsub
      rfl
  | @PerfectInfoTree.decision _ p _ _ _ _, _, _, _, _, _, .here, .here, _, _ => rfl
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, hf, i, h₀,
      .here, .decision a₂ sub₂, hv₁, hv₂ => by
      have hp : p = i := (Sigma.mk.inj_iff.1 hv₁).1
      cases hp
      have hh₁ : f p .here = h₀ := eq_of_heq (Sigma.mk.inj_iff.1 hv₁).2
      obtain ⟨h₂, hh₂⟩ := exists_infoSet_of_isDecisionOf (T := next (eqv p .here a₂)) hv₂
      exact absurd (hf p (hh₁.trans hh₂.symm)) (by simp)
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, hf, i, h₀,
      .decision a₁ sub₁, .here, hv₁, hv₂ => by
      have hp : p = i := (Sigma.mk.inj_iff.1 hv₂).1
      cases hp
      have hh₂ : f p .here = h₀ := eq_of_heq (Sigma.mk.inj_iff.1 hv₂).2
      obtain ⟨h₁, hh₁⟩ := exists_infoSet_of_isDecisionOf (T := next (eqv p .here a₁)) hv₁
      exact absurd (hf p (hh₁.trans hh₂.symm)) (by simp)
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, hf, i, h₀,
      .decision a₁ sub₁, .decision a₂ sub₂, hv₁, hv₂ => by
      obtain ⟨h₁, hh₁⟩ := exists_infoSet_of_isDecisionOf (T := next (eqv p .here a₁)) hv₁
      obtain ⟨h₂, hh₂⟩ := exists_infoSet_of_isDecisionOf (T := next (eqv p .here a₂)) hv₂
      have hinj := hf i (hh₁.trans hh₂.symm)
      have ha' : eqv p .here a₁ = eqv p .here a₂ := (InfoSet.decision.inj hinj).1
      have ha : a₁ = a₂ := (eqv p .here).injective ha'
      subst ha
      have hsub := eq_of_isDecisionOf_toExtensiveTreeOn (T := next (eqv p .here a₁))
        (fun j _ _ he => by
          have := hf j he
          exact (InfoSet.decision.inj this).2 |> eq_of_heq) hv₁ hv₂
      subst hsub
      rfl

/-- Every information set of `T.toExtensiveTree` contains at most one decision node. -/
theorem toExtensiveTree_isSingletonInfoSet {ι : Type u} (T : PerfectInfoTree ι)
    {i : ι} {h : T.InfoSet i} {v₁ v₂ : Node T.toExtensiveTree}
    (hv₁ : v₁.IsDecisionOf i h) (hv₂ : v₂.IsDecisionOf i h) : v₁ = v₂ :=
  eq_of_isDecisionOf_toExtensiveTreeOn (T := T) (fun _ _ _ he => he) hv₁ hv₂

/-- Any embedded extensive-form game with injective information sets satisfies perfect recall for
every player. -/
theorem toExtensiveTreeOn_perfectRecall {ι : Type u} [DecidableEq ι] {H : ι → Type v}
    {Act : ∀ i, H i → Type} {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
    (eqv : ∀ j h, Act j (f j h) ≃ h.Act) (hf : ∀ j, Function.Injective (f j)) (i : ι) :
    (T.toExtensiveTreeOn f eqv).PerfectRecall i := by
  intro _ _ _ hv₁ hv₂
  rw [eq_of_isDecisionOf_toExtensiveTreeOn hf hv₁ hv₂]

/-- **Perfect recall of perfect-information games** ([vonStengel2007], Section 3.7, p. 67, and
Section 3.10, p. 70): the extensive-form embedding `T.toExtensiveTree` satisfies `PerfectRecall`
for every player `i`. -/
theorem toExtensiveTree_perfectRecall {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι)
    (i : ι) :
    T.toExtensiveTree.PerfectRecall i :=
  toExtensiveTreeOn_perfectRecall _ _ (fun _ _ _ he => he) i

/-- In `T.toExtensiveTree`, no play visits any information set of player `i` more than once. -/
theorem toExtensiveTree_noRepeatedInfoSet {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι)
    (i : ι) :
    T.toExtensiveTree.NoRepeatedInfoSet i :=
  (T.toExtensiveTree_perfectRecall i).noRepeatedInfoSet

/-! ### Strategy and payoff bridges -/

namespace PureStrategy

/-- Translate a `PerfectInfoTree` pure strategy `s` into an `ExtensiveTree` pure strategy on
`T.toExtensiveTree`. -/
def toExtensive {ι : Type u} {i : ι} :
    {T : PerfectInfoTree ι} → PureStrategy i T →
      Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i
  | _, s, .here => s.headChoice
  | _, s, .decision a h => (s.childDecision a).toExtensive h
  | _, s, .chance c h => (s.childChance c).toExtensive h

/-- Recover a `PerfectInfoTree` pure strategy from a pure strategy on `T.toExtensiveTree`. -/
def ofExtensive {ι : Type u} [DecidableEq ι] {i : ι} :
    (T : PerfectInfoTree ι) →
      Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i →
      PureStrategy i T
  | .leaf _, _ => .leaf
  | @PerfectInfoTree.decision _ p _ _ _ next, sE =>
      .decision (fun hp => by subst hp; exact sE .here) fun a =>
        ofExtensive (next a) fun h => sE (.decision a h)
  | @PerfectInfoTree.chance _ _ _ _ _ next, sE =>
      .chance fun c => ofExtensive (next c) fun h => sE (.chance c h)

@[simp]
theorem ofExtensive_leaf {ι : Type u} [DecidableEq ι] {i : ι} (w : ι → ℝ)
    (sE : Cslib.GameTheory.Extensive.PureStrategy
      (fun j => (PerfectInfoTree.leaf w).InfoSet j) (fun _ h => h.Act) i) :
    ofExtensive (.leaf w) sE = .leaf := by
  simp [ofExtensive]

@[simp]
theorem ofExtensive_decision {ι : Type u} [DecidableEq ι] {i : ι} (p : ι)
    {A : Type} {instF : Fintype A} {instN : Nonempty A} {next : A → PerfectInfoTree ι}
    (sE : Cslib.GameTheory.Extensive.PureStrategy
      (fun j => (@PerfectInfoTree.decision ι p A instF instN next).InfoSet j)
      (fun _ h => h.Act) i) :
    ofExtensive (@PerfectInfoTree.decision ι p A instF instN next) sE =
      .decision (fun hp => by subst hp; exact sE .here) fun a =>
        ofExtensive (next a) fun h => sE (.decision a h) := by
  simp [ofExtensive]

@[simp]
theorem ofExtensive_chance {ι : Type u} [DecidableEq ι] {i : ι} {C : Type} {instF : Fintype C}
    {prob : C → ℝ} {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    (sE : Cslib.GameTheory.Extensive.PureStrategy
      (fun j => (@PerfectInfoTree.chance ι C instF prob hprob next).InfoSet j)
      (fun _ h => h.Act) i) :
    ofExtensive (@PerfectInfoTree.chance ι C instF prob hprob next) sE =
      .chance fun c => ofExtensive (next c) fun h => sE (.chance c h) := by
  simp [ofExtensive]

@[simp]
theorem toExtensive_here {ι : Type u} {i : ι} {A : Type} {instF : Fintype A} {instN : Nonempty A}
    {next : A → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.decision ι i A instF instN next)) :
    s.toExtensive InfoSet.here = s.headChoice := by
  simp [toExtensive]

@[simp]
theorem toExtensive_decision {ι : Type u} {i p : ι} {A : Type} {instF : Fintype A}
    {instN : Nonempty A} {next : A → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.decision ι p A instF instN next))
    (a : A) (h : (next a).InfoSet i) :
    s.toExtensive (InfoSet.decision a h) = (s.childDecision a).toExtensive h := by
  simp [toExtensive]

@[simp]
theorem toExtensive_chance {ι : Type u} {i : ι} {C : Type} {instF : Fintype C} {prob : C → ℝ}
    {hprob : IsMixedStrategy prob} {next : C → PerfectInfoTree ι}
    (s : PureStrategy i (@PerfectInfoTree.chance ι C instF prob hprob next))
    (c : C) (h : (next c).InfoSet i) :
    s.toExtensive (InfoSet.chance c h) = (s.childChance c).toExtensive h := by
  simp [toExtensive]

@[simp]
theorem ofExtensive_toExtensive {ι : Type u} [DecidableEq ι] {i : ι} :
    ∀ {T : PerfectInfoTree ι} (s : PureStrategy i T),
      ofExtensive T s.toExtensive = s
  | .leaf _, .leaf => by simp
  | @PerfectInfoTree.decision _ p _ _ _ next, .decision c sub => by
      refine PureStrategy.decision_ext (fun hp => ?_) fun a => ?_
      · cases hp
        simp [ofExtensive]
      · simpa [ofExtensive] using ofExtensive_toExtensive (sub a)
  | @PerfectInfoTree.chance _ _ _ _ _ next, .chance sub =>
      PureStrategy.chance_ext fun c => by
        simpa [ofExtensive] using ofExtensive_toExtensive (sub c)

private theorem toExtensive_ofExtensive {ι : Type u} [DecidableEq ι] {i : ι} :
    ∀ {T : PerfectInfoTree ι} (h : T.InfoSet i)
      (sE : Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i),
      (ofExtensive T sE).toExtensive h = sE h
  | _, .here, _ => by simp [ofExtensive, toExtensive]
  | _, .decision a h, sE => by
      simpa [ofExtensive, toExtensive] using
        toExtensive_ofExtensive h (fun h' => sE (.decision a h'))
  | _, .chance c h, sE => by
      simpa [ofExtensive, toExtensive] using
        toExtensive_ofExtensive h (fun h' => sE (.chance c h'))

@[simp]
theorem toExtensive_ofExtensive_eq {ι : Type u} [DecidableEq ι] {i : ι}
    (T : PerfectInfoTree ι)
    (sE : Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i) :
    (ofExtensive T sE).toExtensive = sE := by
  ext h
  exact toExtensive_ofExtensive h sE

/-- Canonical bijection between `PerfectInfoTree.PureStrategy i T` and extensive-form pure
strategies on `T.toExtensiveTree`. -/
def toExtensiveEquiv {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι) (i : ι) :
    PureStrategy i T ≃
      Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i where
  toFun := toExtensive
  invFun := ofExtensive T
  left_inv := ofExtensive_toExtensive
  right_inv := toExtensive_ofExtensive_eq T

@[simp]
theorem toExtensiveEquiv_apply {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι) (i : ι)
    (s : PureStrategy i T) :
    toExtensiveEquiv T i s = s.toExtensive := by
  simp [toExtensiveEquiv]

@[simp]
theorem toExtensiveEquiv_symm_apply {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι) (i : ι)
    (sE : Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i) :
    (toExtensiveEquiv T i).symm sE = ofExtensive T sE := by
  simp [toExtensiveEquiv]

end PureStrategy

private def leafPathToTerminalOn {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
      (eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act),
      LeafPath T → Terminal (T.toExtensiveTreeOn f eqv)
  | .leaf _, _, _, .leaf => .leaf
  | @PerfectInfoTree.chance _ _ _ _ _ next, _, _, .chance c sub =>
      .chance c (leafPathToTerminalOn (T := next c) _ _ sub)
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, .decision a sub =>
      let b := (eqv p .here).symm a
      let sub' :
          Terminal
            ((next a).toExtensiveTreeOn (fun j h => f j (.decision a h))
              (fun j h => eqv j (.decision a h))) :=
        leafPathToTerminalOn (T := next a) _ _ sub
      .decision b (((eqv p .here).apply_symm_apply a).symm ▸ sub')

private def terminalToLeafPathOn {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} {f : ∀ j, T.InfoSet j → H j}
      {eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act},
      Terminal (T.toExtensiveTreeOn f eqv) → LeafPath T
  | .leaf _, _, _, .leaf => .leaf
  | @PerfectInfoTree.chance _ _ _ _ _ next, _, _, .chance c sub =>
      .chance c (terminalToLeafPathOn (T := next c) sub)
  | @PerfectInfoTree.decision _ p _ _ _ next, _, eqv, .decision a sub =>
      .decision (eqv p .here a) (terminalToLeafPathOn (T := next (eqv p .here a)) sub)

private theorem terminalToLeafPathOn_leafPathToTerminalOn {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
      (eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act) (z : LeafPath T),
      terminalToLeafPathOn (leafPathToTerminalOn f eqv z) = z
  | .leaf _, _, _, .leaf => rfl
  | @PerfectInfoTree.chance _ _ _ _ _ next, f, eqv, .chance c sub =>
      congrArg (LeafPath.chance c)
        (terminalToLeafPathOn_leafPathToTerminalOn (T := next c) _ _ sub)
  | @PerfectInfoTree.decision _ p A _ _ next, f, eqv, .decision a sub => by
      have ih := terminalToLeafPathOn_leafPathToTerminalOn (T := next a)
        (fun j h => f j (.decision a h)) (fun j h => eqv j (.decision a h)) sub
      have haux : ∀ (b : Act p (f p .here)) (heq : eqv p .here b = a),
          (LeafPath.decision (eqv p .here b)
              (terminalToLeafPathOn (heq.symm ▸
                leafPathToTerminalOn (T := next a) (fun j h => f j (.decision a h))
                  (fun j h => eqv j (.decision a h)) sub)) :
            LeafPath (.decision p next)) =
            LeafPath.decision a sub := by
        intro b heq
        cases heq
        exact congrArg (LeafPath.decision _) ih
      exact haux ((eqv p .here).symm a) ((eqv p .here).apply_symm_apply a)

private theorem leafPathToTerminalOn_terminalToLeafPathOn {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
      (eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act)
      (z : Terminal (T.toExtensiveTreeOn f eqv)),
      leafPathToTerminalOn f eqv (terminalToLeafPathOn z) = z
  | .leaf _, _, _, .leaf => rfl
  | @PerfectInfoTree.chance _ _ _ _ _ next, f, eqv, .chance c sub =>
      congrArg (Terminal.chance c)
        (leafPathToTerminalOn_terminalToLeafPathOn (T := next c) _ _ sub)
  | @PerfectInfoTree.decision _ p A _ _ next, f, eqv, .decision b sub => by
      have ih := leafPathToTerminalOn_terminalToLeafPathOn (T := next (eqv p .here b))
        (fun j h => f j (.decision (eqv p .here b) h))
        (fun j h => eqv j (.decision (eqv p .here b) h)) sub
      have haux : ∀ (b' : Act p (f p .here)) (hb' : b' = b)
          (heq : eqv p .here b' = eqv p .here b),
          (Terminal.decision b' (heq.symm ▸
              leafPathToTerminalOn (T := next (eqv p .here b))
                (fun j h => f j (.decision (eqv p .here b) h))
                (fun j h => eqv j (.decision (eqv p .here b) h))
                (terminalToLeafPathOn sub)) :
            Terminal ((@PerfectInfoTree.decision ι p A _ _ next).toExtensiveTreeOn f eqv)) =
            Terminal.decision b sub := by
        rintro _ rfl heq
        rw [ih]
      exact haux ((eqv p .here).symm (eqv p .here b)) ((eqv p .here).symm_apply_apply b)
        ((eqv p .here).apply_symm_apply (eqv p .here b))

/-- Bijection between root-to-leaf paths of `T` and terminal paths of `T.toExtensiveTree`. -/
def leafPathEquivTerminal {ι : Type u} (T : PerfectInfoTree ι) :
    LeafPath T ≃ Terminal T.toExtensiveTree where
  toFun := leafPathToTerminalOn (fun _ h => h) (fun _ _ => Equiv.refl _)
  invFun := terminalToLeafPathOn
  left_inv := terminalToLeafPathOn_leafPathToTerminalOn (fun _ h => h) (fun _ _ => Equiv.refl _)
  right_inv := leafPathToTerminalOn_terminalToLeafPathOn (fun _ h => h) (fun _ _ => Equiv.refl _)

private theorem leafPathToTerminalOn_payoff {ι : Type u} {H : ι → Type v}
    {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
      (eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act) (z : LeafPath T),
      (leafPathToTerminalOn f eqv z).payoff = z.payoff
  | .leaf w, f, eqv, .leaf =>
      (Terminal.payoff_leaf w).trans (LeafPath.payoff_leaf w).symm
  | @PerfectInfoTree.chance _ _ _ _ _ next, f, eqv, .chance c sub =>
      (Terminal.payoff_chance c _).trans
        ((leafPathToTerminalOn_payoff (T := next c) _ _ sub).trans
          (LeafPath.payoff_chance c sub).symm)
  | @PerfectInfoTree.decision _ p A instF instN next, f, eqv, .decision a sub => by
      have ih := leafPathToTerminalOn_payoff (T := next a)
        (fun j h => f j (.decision a h)) (fun j h => eqv j (.decision a h)) sub
      have haux : ∀ (b : Act p (f p .here)) (heq : eqv p .here b = a),
          (Terminal.decision b (heq.symm ▸
              leafPathToTerminalOn (T := next a) (fun j h => f j (.decision a h))
                (fun j h => eqv j (.decision a h)) sub) :
            Terminal (ExtensiveTree.decision p (f p .here) fun c =>
              (next (eqv p .here c)).toExtensiveTreeOn
                (fun j h => f j (.decision (eqv p .here c) h))
                (fun j h => eqv j (.decision (eqv p .here c) h)))).payoff =
            sub.payoff := by
        intro b heq
        cases heq
        exact (Terminal.payoff_decision b _).trans ih
      exact (haux ((eqv p .here).symm a) ((eqv p .here).apply_symm_apply a)).trans
        (LeafPath.payoff_decision (p := p) (instF := instF) (instN := instN) a sub).symm

@[simp]
theorem leafPathEquivTerminal_payoff {ι : Type u} {T : PerfectInfoTree ι} (z : LeafPath T) :
    ((leafPathEquivTerminal T) z).payoff = z.payoff :=
  leafPathToTerminalOn_payoff (fun _ h => h) (fun _ _ => Equiv.refl _) z

theorem toExtensiveTreeOn_evalPure {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type} :
    ∀ {T : PerfectInfoTree ι} (f : ∀ j, T.InfoSet j → H j)
      (eqv : ∀ j (h : T.InfoSet j), Act j (f j h) ≃ h.Act)
      (s : ∀ j, PureStrategy j T) (sE : ∀ j, Cslib.GameTheory.Extensive.PureStrategy H Act j),
      (∀ j (h : T.InfoSet j), eqv j h (sE j (f j h)) = (s j).toExtensive h) →
      (T.toExtensiveTreeOn f eqv).evalPure sE = T.expectedPayoff s
  | .leaf _, _, _, _, _, _ => by simp [toExtensiveTreeOn]
  | @PerfectInfoTree.chance _ _ instF prob hprob next, f, eqv, s, sE, hmatch => by
      let _ := instF
      ext k
      simp only [toExtensiveTreeOn, ExtensiveTree.evalPure_chance, expectedPayoff_chance]
      refine sum_congr rfl fun c _ => ?_
      have hsub := toExtensiveTreeOn_evalPure (T := next c)
        (fun j h => f j (.chance c h)) (fun j h => eqv j (.chance c h))
        (fun j => (s j).childChance c) sE fun j h => by
          simpa only [InfoSet.Act, PureStrategy.toExtensive_chance] using hmatch j (.chance c h)
      rw [hsub]
  | @PerfectInfoTree.decision _ p _ _ _ next, f, eqv, s, sE, hmatch => by
      simp only [toExtensiveTreeOn, ExtensiveTree.evalPure_decision, expectedPayoff_decision]
      have hhead : eqv p .here (sE p (f p .here)) = (s p).headChoice := by
        simpa only [InfoSet.Act, PureStrategy.toExtensive_here] using hmatch p .here
      rw [hhead]
      exact toExtensiveTreeOn_evalPure (T := next (s p).headChoice)
        (fun j h => f j (.decision (s p).headChoice h))
        (fun j h => eqv j (.decision (s p).headChoice h))
        (fun j => (s j).childDecision (s p).headChoice) sE
        fun j h => by
          simpa only [InfoSet.Act, PureStrategy.toExtensive_decision] using
            hmatch j (.decision (s p).headChoice h)

/-- Pure payoffs of `T.toExtensiveTree` equal `T.expectedPayoff` when strategies are translated
via `PureStrategy.toExtensive`. -/
theorem toExtensiveTree_evalPure {ι : Type u} (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) :
    T.toExtensiveTree.evalPure (fun i => (s i).toExtensive) = T.expectedPayoff s :=
  toExtensiveTreeOn_evalPure (T := T) (fun _ h => h) (fun _ _ => Equiv.refl _) s
    (fun i => (s i).toExtensive) (fun _ _ => rfl)

/-- Pure payoffs of `T.toExtensiveTree` equal `T.expectedPayoff` after pulling strategies back via
`PureStrategy.ofExtensive`. -/
theorem toExtensiveTree_evalPure_ofExtensive {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι)
    (sE : ∀ i, Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j)
      (fun _ h => h.Act) i) :
    T.toExtensiveTree.evalPure sE =
      T.expectedPayoff (fun i => PureStrategy.ofExtensive T (sE i)) := by
  have heq : sE = fun i => (PureStrategy.ofExtensive T (sE i)).toExtensive := by
    ext i h
    exact (congrFun ((PureStrategy.toExtensiveEquiv T i).right_inv (sE i)) h).symm
  conv_lhs => rw [heq]
  exact toExtensiveTree_evalPure T (fun i => PureStrategy.ofExtensive T (sE i))

/-- Equivalence of pure Nash equilibria between `T.toCostGame` and `(T.toExtensiveTree).toCostGame`.
-/
theorem toExtensiveTree_isPureNash_iff {ι : Type u} [DecidableEq ι] (T : PerfectInfoTree ι)
    (s : ∀ i, PureStrategy i T) :
    T.toExtensiveTree.toCostGame.IsPureNash (fun i => (s i).toExtensive) ↔
      T.toCostGame.IsPureNash s := by
  constructor
  · intro h i σ'
    have hdev := h i σ'.toExtensive
    have hupd : Function.update (fun j => (s j).toExtensive) i σ'.toExtensive =
        fun j => (Function.update s i σ' j).toExtensive := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    simpa [ExtensiveTree.toCostGame_cost, PerfectInfoTree.toCostGame_cost, hupd,
      toExtensiveTree_evalPure] using hdev
  · intro h i sE'
    let σ' := PureStrategy.ofExtensive T sE'
    have hsE' : sE' = σ'.toExtensive := (PureStrategy.toExtensiveEquiv T i).right_inv sE' |>.symm
    have hdev := h i σ'
    have hupd : Function.update (fun j => (s j).toExtensive) i σ'.toExtensive =
        fun j => (Function.update s i σ' j).toExtensive := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hsE']
    simp only [ExtensiveTree.toCostGame_cost, PerfectInfoTree.toCostGame_cost] at hdev ⊢
    rw [hupd, toExtensiveTree_evalPure, toExtensiveTree_evalPure]
    exact hdev

/-- Backward induction constructs a pure Nash equilibrium of the embedded game
`(T.toExtensiveTree).toCostGame`. -/
theorem toExtensiveTree_backwardInduction_isPureNash {ι : Type u} [DecidableEq ι]
    (T : PerfectInfoTree ι) :
    T.toExtensiveTree.toCostGame.IsPureNash
      (fun i => (T.backwardInduction.strategy i).toExtensive) :=
  (toExtensiveTree_isPureNash_iff T T.backwardInduction.strategy).2
    (isPureSPE_backwardInduction T).isPureNash

/-- Under the pure-strategy bijection, mixed Nash equilibria of `T.toCostGame` correspond
precisely to mixed Nash equilibria of `(T.toExtensiveTree).toCostGame`. -/
theorem toExtensiveTree_isMixedNash_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (T : PerfectInfoTree ι) [∀ i, DecidableEq (T.InfoSet i)]
    (μ : ∀ i, PureStrategy i T → ℝ) :
    T.toExtensiveTree.toCostGame.IsMixedNash
        (fun i sE => μ i (PureStrategy.ofExtensive T sE)) ↔
      T.toCostGame.IsMixedNash μ := by
  let e := fun i => PureStrategy.toExtensiveEquiv T i
  have hsum : ∀ i (g : PureStrategy i T → ℝ),
      ∑ sE : Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i,
        g ((e i).symm sE) = ∑ s : PureStrategy i T, g s :=
    fun i g => (e i).symm.sum_comp g
  have hprof : ∀ (q : ∀ i, PureStrategy i T → ℝ)
      (f : (∀ i, PureStrategy i T) → ℝ),
      (∑ sE : ∀ i,
          Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i,
        productWeight (fun i x => q i ((e i).symm x)) sE * f (fun i => (e i).symm (sE i))) =
      ∑ s : ∀ i, PureStrategy i T, productWeight q s * f s := by
    intro q f
    let π : (∀ i, PureStrategy i T) ≃
        ∀ i, Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i :=
      Equiv.piCongrRight e
    rw [← π.sum_comp]
    refine sum_congr rfl fun s _ => ?_
    simp [π, productWeight_def, e]
  have hevalMixed : ∀ (q : ∀ i, PureStrategy i T → ℝ) (i : ι),
      T.toExtensiveTree.toCostGame.expectedCost (fun j sE => q j ((e j).symm sE)) i =
        T.toCostGame.expectedCost q i := by
    intro q i
    rw [CostGame.expectedCost_def, CostGame.expectedCost_def]
    simp only [ExtensiveTree.toCostGame_cost, PerfectInfoTree.toCostGame_cost,
      toExtensiveTree_evalPure_ofExtensive]
    exact hprof q fun s => -T.expectedPayoff s i
  have hdevCost : ∀ (q : ∀ i, PureStrategy i T → ℝ) (i : ι) (sE : _),
      T.toExtensiveTree.toCostGame.deviationCost (fun j x => q j ((e j).symm x)) i sE =
        T.toCostGame.deviationCost q i ((e i).symm sE) := by
    intro q i sE
    rw [CostGame.deviationCost_def, CostGame.deviationCost_def]
    simp only [ExtensiveTree.toCostGame_cost, PerfectInfoTree.toCostGame_cost]
    have hupd : ∀ sE' : ∀ j,
        Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) j,
        T.toExtensiveTree.evalPure (Function.update sE' i sE) i =
          T.expectedPayoff (Function.update (fun j => (e j).symm (sE' j)) i ((e i).symm sE)) i := by
      intro sE'
      rw [toExtensiveTree_evalPure_ofExtensive]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp [e, PureStrategy.toExtensiveEquiv]
      · simp [hj, e, PureStrategy.toExtensiveEquiv]
    have hupd' : ∀ sE' : ∀ j,
        Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) j,
        -T.toExtensiveTree.evalPure (Function.update sE' i sE) i =
          -T.expectedPayoff (Function.update (fun j => (e j).symm (sE' j)) i ((e i).symm sE)) i :=
      fun sE' => congrArg Neg.neg (hupd sE')
    simp_rw [hupd']
    exact hprof q fun s => -T.expectedPayoff (Function.update s i ((e i).symm sE)) i
  have hpush : (fun i sE => μ i (PureStrategy.ofExtensive T sE)) =
      fun i sE => μ i ((e i).symm sE) := rfl
  rw [hpush]
  constructor
  · rintro ⟨hmix, hopt⟩
    refine ⟨fun i => isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩, fun i a => ?_⟩
    · simpa [e, (e i).left_inv s] using (hmix i).nonneg (e i s)
    · rw [← hsum i (μ i)]
      exact (hmix i).sum_eq_one
    · have h := hopt i ((e i) a)
      rw [hevalMixed, hdevCost] at h
      simpa [e] using h
  · rintro ⟨hmix, hopt⟩
    refine ⟨fun i => isMixedStrategy_iff.2 ⟨fun sE => (hmix i).nonneg ((e i).symm sE), ?_⟩,
      fun i sE => ?_⟩
    · rw [hsum i (μ i)]
      exact (hmix i).sum_eq_one
    · rw [hevalMixed, hdevCost]
      exact hopt i ((e i).symm sE)

/-- **Kuhn's theorem for embedded perfect-information games**: every mixed strategy `μ` of player
`i` in `T.toExtensiveTree` is realization-equivalent to an explicit behavioral strategy. -/
theorem toExtensiveTree_kuhn_theorem {ι : Type u} [Fintype ι] [DecidableEq ι]
    (T : PerfectInfoTree ι) {i : ι} [∀ j, DecidableEq (T.InfoSet j)]
    {μ : Cslib.GameTheory.Extensive.PureStrategy (fun j => T.InfoSet j) (fun _ h => h.Act) i → ℝ}
    (hμ : IsMixedStrategy μ) :
    let hpr := T.toExtensiveTree_perfectRecall i
    let β := T.toExtensiveTree.realizationPlanToBehavior i hpr
      (T.toExtensiveTree.mixedToRealizationPlan i μ)
    IsBehaviorStrategy β ∧
      T.toExtensiveTree.RealizationEquivMixedBehavior i μ β := by
  have hk := kuhn_theorem (T.toExtensiveTree_perfectRecall i) hμ
  exact ⟨hk.1, hk.2.2⟩

end PerfectInfoTree

end Cslib.GameTheory.Extensive
