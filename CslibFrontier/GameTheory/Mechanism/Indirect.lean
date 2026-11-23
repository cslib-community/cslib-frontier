/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Bayesian
public import CslibFrontier.GameTheory.Mechanism.Domains
public import CslibFrontier.GameTheory.Strategic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Incomplete-information games, indirect mechanisms, and the revelation principles

In §9.4 and §9.6 of [Nisan2007], direct-revelation mechanisms are placed inside the broader
framework of indirect (nondirect) protocols in which players hold private types `tᵢ ∈ Tᵢ` and
choose actions `xᵢ ∈ Xᵢ`:

* **Games with strict incomplete information** (`IncompleteInfoGame`, [Nisan2007],
  Definition 9.21): each player `i : ι` has a type space `T i`, an action space `X i`, and a
  private-value utility `utility i : T i → (∀ j, X j) → ℝ`. A strategy profile
  `s : ∀ i, T i → X i` is a *dominant-strategy equilibrium* (`IsDominantStrategyEquilibrium`) when
  each `s i (t i)` maximizes utility against all opponent action profiles, and an *ex-post Nash
  equilibrium* (`IsExPostNash`, Definition 9.22) when `fun j => s j (t j)` is a pure Nash
  equilibrium of the full-information game at every type profile `t`
  (`isExPostNash_iff_forall_isPureNash`).
* **Proposition 9.23**
  (`IncompleteInfoGame.IsExPostNash.isDominantStrategyEquilibrium_restrictRange`):
  restricting each player's action space `X i` to the actual range `Set.range (s i)` turns any
  ex-post Nash equilibrium `s` into a dominant-strategy equilibrium.
* **Indirect mechanisms and the Dominant-Strategy / Ex-Post-Nash Revelation Principles**
  (`IndirectMechanism`, Definition 9.24, Proposition 9.25 and Corollary 9.26): an indirect
  mechanism chooses an outcome `outcome x : Ω` and payments `payment x : ι → ℝ` from action
  profiles `x : ∀ i, X i`. Composing `M` with a dominant-strategy or ex-post-Nash equilibrium `s`
  yields the direct mechanism `M.revelation s` (`X' = T`) implementing the same social choice
  function `t ↦ M.outcome (fun j => s j (t j))` truthfully (`revelation_isTruthful`,
  `revelation_isTruthful_of_isExPostNash`, `exists_truthful_of_implementsInDominantStrategies`,
  `exists_truthful_of_implementsInExPostNash`) with identical equilibrium payments, and likewise
  yields a DSIC direct `Mechanism ι Ω` on valuation domains `V`
  (`IndirectMechanism.toMechanism_isDSICOn_of_isExPostNash`).
* **Bayesian games, Bayesian truthfulness (`IsBICOn`), and the Bayesian Revelation Principle**
  (`BayesianGame`, `BayesianMechanism`, `Mechanism.IsBICOn`, [Nisan2007], Definitions 9.40–9.43 and
  Proposition 9.44; [Harsanyi1967]; [Myerson1981]): adding independent prior measures
  `prior : ∀ i, Measure (T i)` (with discrete `PMF` specialization `BayesianGame.ofPMF`) defines
  interim utility via `Measure.pi` and Bayes–Nash equilibrium (`BayesianGame.IsBayesNash`,
  `BayesianGame.IsBayesNashOn`), bridged to `SingleParameter.Mechanism.IsBayesNash`
  (`SingleParameter.Mechanism.isBayesNash_iff_toBayesianGame`). Composing any Bayesian
  implementation `(M, s)` yields a truthful direct `BayesianMechanism` (`M.revelation s`) with
  identical ex-post, interim, and ex-ante expected payments
  (`BayesianMechanism.revelation_isTruthful`,
  `BayesianMechanism.exists_truthful_of_implementsInBayesNash`), as well as a BIC direct
  `Mechanism ι Ω` on valuation domains (`IndirectMechanism.toMechanism_isBICOn`).

## Main definitions

* `IncompleteInfoGame`: strict incomplete-information game ([Nisan2007], Definition 9.21).
* `IncompleteInfoGame.IsDominantStrategy`, `IncompleteInfoGame.IsDominantStrategyEquilibrium`,
  `IncompleteInfoGame.IsExPostNash`: equilibrium concepts ([Nisan2007], Definition 9.22).
* `IncompleteInfoGame.fullInfoCostGame`, `IncompleteInfoGame.restrictRange`: full-information slice
  and range-restricted game ([Nisan2007], Proposition 9.23).
* `IndirectMechanism`, `IndirectMechanism.toIncompleteInfoGame`,
  `IndirectMechanism.ImplementsInDominantStrategies`, `IndirectMechanism.ImplementsInExPostNash`,
  `IndirectMechanism.revelation`, `IndirectMechanism.IsTruthful`,
  `IndirectMechanism.toMechanism`: indirect mechanisms and direct-revelation simulation
  ([Nisan2007], Definition 9.24 and Proposition 9.25).
* `BayesianGame`, `BayesianGame.ofPMF`, `BayesianGame.interimUtility`,
  `BayesianGame.IsBayesNashOn`, `BayesianGame.IsBayesNash`: multi-parameter Bayesian games
  ([Nisan2007], Definitions 9.40–9.41).
* `SingleParameter.Mechanism.toBayesianGame`: single-parameter mechanisms as Bayesian games.
* `BayesianMechanism`, `BayesianMechanism.toBayesianGame`,
  `BayesianMechanism.ImplementsInBayesNash`, `BayesianMechanism.revelation`,
  `BayesianMechanism.IsTruthful`, `BayesianMechanism.interimPayment`: Bayesian mechanisms
  ([Nisan2007], Definitions 9.42–9.43).
* `Mechanism.interimUtility`, `Mechanism.IsBICOn`, `Mechanism.IsBIC`: Bayesian incentive
  compatibility on valuation domains `V : ι → Set (Ω → ℝ)`.

## Main results

* `IncompleteInfoGame.isExPostNash_iff_forall_isPureNash`: ex-post Nash equilibria are profiles
  that are pure Nash at every type profile.
* `IncompleteInfoGame.IsExPostNash.isDominantStrategyEquilibrium_restrictRange`:
  **Proposition 9.23** of [Nisan2007].
* `IndirectMechanism.revelation_isTruthful`,
  `IndirectMechanism.exists_truthful_of_implementsInDominantStrategies`: **Proposition 9.25
  (Dominant-Strategy Revelation Principle)** of [Nisan2007].
* `IndirectMechanism.revelation_isTruthful_of_isExPostNash`,
  `IndirectMechanism.exists_truthful_of_implementsInExPostNash`,
  `IndirectMechanism.toMechanism_isDSICOn_of_isExPostNash`: **Corollary 9.26 (Ex-Post-Nash
  Revelation Principle)** of [Nisan2007].
* `BayesianGame.isBayesNash_of_isExPostNash`: ex-post Nash equilibria are Bayes–Nash under
  integrability ([Nisan2007], §9.6.1).
* `SingleParameter.Mechanism.isBayesNash_iff_toBayesianGame`: bridge between
  `SingleParameter.Mechanism.IsBayesNash` and `BayesianGame.IsBayesNashOn`.
* `BayesianMechanism.revelation_isTruthful`,
  `BayesianMechanism.revelation_interimPayment_eq`,
  `BayesianMechanism.exists_truthful_of_implementsInBayesNash`,
  `IndirectMechanism.toMechanism_isBICOn`: **Proposition 9.44 (Bayesian Revelation Principle)** of
  [Nisan2007].

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [J. C. Harsanyi, *Games with incomplete information played by ``Bayesian''
  players*][Harsanyi1967]
* [P. Dasgupta, P. Hammond, E. Maskin, *The implementation of social choice
  rules*][DasguptaHammondMaskin1979]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory

/-! ### Strict incomplete-information games (§9.4.1, Definitions 9.21–9.22, Proposition 9.23) -/

/-- A game with independent private values and **strict incomplete information** ([Nisan2007],
Definition 9.21): player `i : ι` holds a private type `tᵢ : T i`, chooses an action `xᵢ : X i`, and
receives real-valued utility `utility i tᵢ x`. -/
structure IncompleteInfoGame (ι : Type*) (T X : ι → Type*) where
  /-- `utility i tᵢ x` is player `i`'s utility at private type `tᵢ` and action profile `x`. -/
  utility : ∀ i, T i → (∀ j, X j) → ℝ

namespace IncompleteInfoGame

variable {ι : Type*} {T X : ι → Type*} (G : IncompleteInfoGame ι T X)

/-- At a fixed type profile `t`, `G` induces a full-information strategic `CostGame` with costs
`-G.utility i (t i) x`. -/
@[expose] def fullInfoCostGame (t : ∀ i, T i) : CostGame ι X where
  cost i x := -G.utility i (t i) x

section Equilibrium

variable [DecidableEq ι]

/-- Strategy `si : T i → X i` is a **(weakly) dominant strategy** for player `i` ([Nisan2007],
Definition 9.22): for every private type `ti` and every action profile `x`, playing `si ti` gives
`i` at least as much utility as `x i`. -/
@[expose] def IsDominantStrategy (i : ι) (si : T i → X i) : Prop :=
  ∀ (ti : T i) (x : ∀ j, X j), G.utility i ti x ≤ G.utility i ti (Function.update x i (si ti))

/-- Equivalent two-deviation phrasing matching [Nisan2007], Definition 9.22 verbatim:
`uᵢ(tᵢ, x'ᵢ, x₋ᵢ) ≤ uᵢ(tᵢ, sᵢ(tᵢ), x₋ᵢ)`. -/
theorem isDominantStrategy_iff {i : ι} {si : T i → X i} :
    G.IsDominantStrategy i si ↔
      ∀ (ti : T i) (x : ∀ j, X j) (xi' : X i),
        G.utility i ti (Function.update x i xi') ≤ G.utility i ti (Function.update x i (si ti)) :=
  ⟨fun h ti x xi' => by simpa only [Function.update_idem] using h ti (Function.update x i xi'),
    fun h ti x => by simpa only [Function.update_eq_self] using h ti x (x i)⟩

/-- A strategy profile `s` is a **dominant-strategy equilibrium** if every `s i` is a dominant
strategy ([Nisan2007], Definition 9.22). -/
@[expose] def IsDominantStrategyEquilibrium (s : ∀ i, T i → X i) : Prop :=
  ∀ i, G.IsDominantStrategy i (s i)

/-- A strategy profile `s` is an **ex-post Nash equilibrium** ([Nisan2007], Definition 9.22): at
every type profile `t`, no player `i` can increase `G.utility i (t i)` by unilaterally deviating
from `s i (t i)` to another action `xi'`. -/
@[expose] def IsExPostNash (s : ∀ i, T i → X i) : Prop :=
  ∀ (i : ι) (t : ∀ j, T j) (xi' : X i),
    G.utility i (t i) (Function.update (fun j => s j (t j)) i xi') ≤
      G.utility i (t i) (fun j => s j (t j))

/-- `s` is an ex-post Nash equilibrium iff at every type profile `t`, the induced action profile
`fun j => s j (t j)` is a pure Nash equilibrium of `G.fullInfoCostGame t`. -/
theorem isExPostNash_iff_forall_isPureNash {s : ∀ i, T i → X i} :
    G.IsExPostNash s ↔ ∀ t, (G.fullInfoCostGame t).IsPureNash (fun j => s j (t j)) := by
  simp only [IsExPostNash, CostGame.IsPureNash, fullInfoCostGame, neg_le_neg_iff]
  exact ⟨fun h t i a => h i t a, fun h i t a => h t i a⟩

variable {G}

/-- Every dominant-strategy equilibrium is an ex-post Nash equilibrium. -/
theorem IsDominantStrategyEquilibrium.isExPostNash {s : ∀ i, T i → X i}
    (hs : G.IsDominantStrategyEquilibrium s) : G.IsExPostNash s := by
  intro i t xi'
  have h := (G.isDominantStrategy_iff.1 (hs i)) (t i) (fun j => s j (t j)) xi'
  rwa [Function.update_eq_self] at h

/-- Restrict each player's action space to the actual range `Set.range (s i)` of its strategy
`s i` ([Nisan2007], Proposition 9.23). -/
@[expose] def restrictRange (G : IncompleteInfoGame ι T X) (s : ∀ i, T i → X i) :
    IncompleteInfoGame ι T (fun i => Set.range (s i)) where
  utility i ti x := G.utility i ti fun j => (x j : X j)

/-- **Proposition 9.23** of [Nisan2007]: if `s` is an ex-post Nash equilibrium of `G`, then
restricting each action space `X i` to `Set.range (s i)` makes `s` (viewed via
`Set.rangeFactorization`) a dominant-strategy equilibrium of `G.restrictRange s`. -/
theorem IsExPostNash.isDominantStrategyEquilibrium_restrictRange {s : ∀ i, T i → X i}
    (hs : G.IsExPostNash s) :
    (G.restrictRange s).IsDominantStrategyEquilibrium
      (fun i => Set.rangeFactorization (s i)) := by
  intro i ti x
  choose t₀ ht₀ using fun j => (x j).2
  let t : ∀ j, T j := Function.update t₀ i ti
  have h1 : (fun j => (x j : X j)) =
      Function.update (fun j => s j (t j)) i (x i : X i) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
    · rw [Function.update_of_ne hj]
      simp only [t, Function.update_of_ne hj, ht₀ j]
  have h2 : (fun j => ((Function.update x i (Set.rangeFactorization (s i) ti) j :
      Set.range (s j)) : X j)) = fun j => s j (t j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [t, Function.update_self, Set.rangeFactorization_coe]
    · simp only [t, Function.update_of_ne hj, ht₀ j]
  simp only [restrictRange, h1, h2]
  simpa only [t, Function.update_self] using hs i t (x i : X i)

end Equilibrium

end IncompleteInfoGame

/-! ### Indirect mechanisms and Dominant-Strategy / Ex-Post Revelation Principles (§9.4.2–9.4.3) -/

/-- A general (possibly indirect / nondirect) mechanism with players `ι`, action spaces `X i`, and
outcome set `Ω` ([Nisan2007], Definition 9.24): given an action profile `x : ∀ i, X i`, it chooses
`outcome x` and charges player `i` the payment `payment x i`. -/
structure IndirectMechanism (ι : Type*) (X : ι → Type*) (Ω : Type*) where
  /-- Outcome rule mapping action profiles to outcomes in `Ω`. -/
  outcome : (∀ i, X i) → Ω
  /-- Payment rule: `payment x i` is the payment charged to player `i`. -/
  payment : (∀ i, X i) → ι → ℝ

namespace IndirectMechanism

variable {ι Ω : Type*} {T X : ι → Type*}

/-- The game with strict incomplete information induced by `M` under private-value valuations
`val : ∀ i, T i → Ω → ℝ` ([Nisan2007], Definition 9.24): `uᵢ(tᵢ, x) = vᵢ(tᵢ, a(x)) − pᵢ(x)`. -/
@[expose] def toIncompleteInfoGame (M : IndirectMechanism ι X Ω) (val : ∀ i, T i → Ω → ℝ) :
    IncompleteInfoGame ι T X where
  utility i ti x := val i ti (M.outcome x) - M.payment x i

/-- Simulate strategies `s : ∀ i, T i → X i` inside `M` to obtain a direct-revelation mechanism
(`X' = T`, [Nisan2007], proof of Proposition 9.25). -/
@[expose] def revelation (M : IndirectMechanism ι X Ω) (s : ∀ i, T i → X i) :
    IndirectMechanism ι T Ω where
  outcome t := M.outcome fun j => s j (t j)
  payment t := M.payment fun j => s j (t j)

/-- Convert an indirect mechanism `M` and valuation-indexed strategies `s : ∀ i, (Ω → ℝ) → X i`
into a `Cslib.GameTheory.Mechanism ι Ω`. -/
@[expose] def toMechanism (M : IndirectMechanism ι X Ω) (s : ∀ i, (Ω → ℝ) → X i) :
    Mechanism ι Ω where
  outcome b := M.outcome fun j => s j (b j)
  payment b := M.payment fun j => s j (b j)

section Implementation

variable [DecidableEq ι]

/-- `M` **implements `f` in dominant strategies** for valuations `val` if some dominant-strategy
equilibrium `s` of `M.toIncompleteInfoGame val` satisfies `M.outcome (s t) = f t` everywhere
([Nisan2007], Definition 9.24). -/
@[expose] def ImplementsInDominantStrategies (M : IndirectMechanism ι X Ω)
    (val : ∀ i, T i → Ω → ℝ) (f : (∀ i, T i) → Ω) : Prop :=
  ∃ s : ∀ i, T i → X i,
    (M.toIncompleteInfoGame val).IsDominantStrategyEquilibrium s ∧
      ∀ t, M.outcome (fun j => s j (t j)) = f t

/-- `M` **implements `f` in ex-post Nash equilibrium** for valuations `val` if some ex-post Nash
equilibrium `s` of `M.toIncompleteInfoGame val` satisfies `M.outcome (s t) = f t` everywhere
([Nisan2007], Definition 9.24). -/
@[expose] def ImplementsInExPostNash (M : IndirectMechanism ι X Ω)
    (val : ∀ i, T i → Ω → ℝ) (f : (∀ i, T i) → Ω) : Prop :=
  ∃ s : ∀ i, T i → X i,
    (M.toIncompleteInfoGame val).IsExPostNash s ∧
      ∀ t, M.outcome (fun j => s j (t j)) = f t

/-- A direct mechanism `D : IndirectMechanism ι T Ω` (`X = T`) is **incentive compatible
(truthful)** for valuations `val` if truthful reporting `fun _ => id` is a dominant-strategy
equilibrium. -/
@[expose] def IsTruthful (D : IndirectMechanism ι T Ω) (val : ∀ i, T i → Ω → ℝ) : Prop :=
  (D.toIncompleteInfoGame val).IsDominantStrategyEquilibrium fun _ => id

theorem ImplementsInDominantStrategies.implementsInExPostNash {M : IndirectMechanism ι X Ω}
    {val : ∀ i, T i → Ω → ℝ} {f : (∀ i, T i) → Ω}
    (h : M.ImplementsInDominantStrategies val f) : M.ImplementsInExPostNash val f := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨s, hs.isExPostNash, hf⟩

/-- **Corollary 9.26 (Ex-Post-Nash Revelation Principle, direct form)** ([Nisan2007], p. 225):
if `s` is an ex-post Nash equilibrium of `M` under `val`, then restricting action spaces to
`Set.range (s i)` (Proposition 9.23) and simulating `s` makes `M.revelation s` truthful in
dominant strategies. -/
theorem revelation_isTruthful_of_isExPostNash {M : IndirectMechanism ι X Ω}
    {val : ∀ i, T i → Ω → ℝ} {s : ∀ i, T i → X i}
    (hs : (M.toIncompleteInfoGame val).IsExPostNash s) :
    (M.revelation s).IsTruthful val := by
  have hdom := hs.isDominantStrategyEquilibrium_restrictRange
  intro i ti t
  have h := hdom i ti (fun j => Set.rangeFactorization (s j) (t j))
  have h1 : (fun j => ((Set.rangeFactorization (s j) (t j) : Set.range (s j)) : X j)) =
      fun j => s j (t j) := rfl
  have h2 : (fun j => ((Function.update (fun k => Set.rangeFactorization (s k) (t k)) i
      (Set.rangeFactorization (s i) ti) j : Set.range (s j)) : X j)) =
        fun j => s j (Function.update t i ti j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self, Set.rangeFactorization_coe]
    · simp only [Function.update_of_ne hj, Set.rangeFactorization_coe]
  simpa only [IncompleteInfoGame.restrictRange, toIncompleteInfoGame, revelation, h1, h2, id_eq]
    using h

/-- **Proposition 9.25 (Dominant-Strategy Revelation Principle, direct form)** ([Nisan2007],
pp. 224–225): if `s` is a dominant-strategy equilibrium of `M` under `val`, then `M.revelation s`
is truthful in dominant strategies. -/
theorem revelation_isTruthful {M : IndirectMechanism ι X Ω}
    {val : ∀ i, T i → Ω → ℝ} {s : ∀ i, T i → X i}
    (hs : (M.toIncompleteInfoGame val).IsDominantStrategyEquilibrium s) :
    (M.revelation s).IsTruthful val :=
  revelation_isTruthful_of_isExPostNash hs.isExPostNash

/-- **Proposition 9.25 (Dominant-Strategy Revelation Principle)** ([Nisan2007], p. 224): if an
indirect mechanism `M` implements `f` in dominant strategies, there exists a truthful direct
mechanism `D` with outcome rule `f` whose payments equal `M`'s equilibrium payments. -/
theorem exists_truthful_of_implementsInDominantStrategies {M : IndirectMechanism ι X Ω}
    {val : ∀ i, T i → Ω → ℝ} {f : (∀ i, T i) → Ω}
    (h : M.ImplementsInDominantStrategies val f) :
    ∃ s : ∀ i, T i → X i,
      (M.toIncompleteInfoGame val).IsDominantStrategyEquilibrium s ∧
      ∃ D : IndirectMechanism ι T Ω,
        D.IsTruthful val ∧ D.outcome = f ∧
        ∀ t, D.payment t = M.payment (fun j => s j (t j)) := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨s, hs, M.revelation s, revelation_isTruthful hs, funext hf, fun _ => rfl⟩

/-- **Corollary 9.26 (Ex-Post-Nash Revelation Principle)** ([Nisan2007], p. 225): if an indirect
mechanism `M` implements `f` in ex-post Nash equilibrium, there exists a truthful direct mechanism
`D` with outcome rule `f` whose payments equal `M`'s equilibrium payments. -/
theorem exists_truthful_of_implementsInExPostNash {M : IndirectMechanism ι X Ω}
    {val : ∀ i, T i → Ω → ℝ} {f : (∀ i, T i) → Ω}
    (h : M.ImplementsInExPostNash val f) :
    ∃ s : ∀ i, T i → X i,
      (M.toIncompleteInfoGame val).IsExPostNash s ∧
      ∃ D : IndirectMechanism ι T Ω,
        D.IsTruthful val ∧ D.outcome = f ∧
        ∀ t, D.payment t = M.payment (fun j => s j (t j)) := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨s, hs, M.revelation s, revelation_isTruthful_of_isExPostNash hs, funext hf, fun _ => rfl⟩

/-- **Valuation-domain Ex-Post / Dominant Revelation Principle**: if `s : ∀ i, (Ω → ℝ) → X i`
restricted to valuation domains `V : ι → Set (Ω → ℝ)` is an ex-post Nash equilibrium of `M`, then
`M.toMechanism s : Mechanism ι Ω` is DSIC on `V` (`IsDSICOn V`). -/
theorem toMechanism_isDSICOn_of_isExPostNash {M : IndirectMechanism ι X Ω}
    {V : ι → Set (Ω → ℝ)} {s : ∀ i, (Ω → ℝ) → X i}
    (hs : (M.toIncompleteInfoGame (T := fun i => V i) (fun _ v => v.1)).IsExPostNash
      (fun i v => s i v.1)) :
    (M.toMechanism s).IsDSICOn V := by
  have hD := revelation_isTruthful_of_isExPostNash hs
  intro i b v hb hv
  have h := hD i ⟨v, hv⟩ (fun j => ⟨b j, hb j⟩)
  have hupd : (fun j => s j ((Function.update (fun k => (⟨b k, hb k⟩ : V k)) i ⟨v, hv⟩ j : V j) :
      Ω → ℝ)) = fun j => s j (Function.update b i v j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  simpa only [toIncompleteInfoGame, revelation, Mechanism.utility, toMechanism, id_eq, hupd]
    using h

end Implementation

end IndirectMechanism

/-- View a direct `Mechanism ι Ω` as an `IndirectMechanism` with action space `Ω → ℝ`. -/
@[expose] def Mechanism.toIndirectMechanism {ι Ω : Type*} (M : Mechanism ι Ω) :
    IndirectMechanism ι (fun _ => Ω → ℝ) Ω where
  outcome := M.outcome
  payment := M.payment

/-! ### Multi-parameter Bayesian games and Bayesian Revelation Principle (§9.6, Defs 9.40–9.44) -/

/-- A game with independent private values and **Bayesian incomplete information** ([Nisan2007],
Definition 9.40; [Harsanyi1967]): extends `IncompleteInfoGame ι T X` with an independent prior
measure `prior i` on each player's type space `T i`. -/
structure BayesianGame (ι : Type*) (T X : ι → Type*) [∀ i, MeasurableSpace (T i)]
    extends IncompleteInfoGame ι T X where
  /-- Player `i`'s prior type distribution `Dᵢ`. -/
  prior : ∀ i, Measure (T i)

namespace BayesianGame

variable {ι : Type*} {T X : ι → Type*} [∀ i, MeasurableSpace (T i)]

/-- Construct a `BayesianGame` from discrete `PMF` priors via `PMF.toMeasure`. -/
@[expose] noncomputable def ofPMF (G : IncompleteInfoGame ι T X) (d : ∀ i, PMF (T i)) :
    BayesianGame ι T X where
  toIncompleteInfoGame := G
  prior i := (d i).toMeasure

instance isProbabilityMeasure_ofPMF (G : IncompleteInfoGame ι T X) (d : ∀ i, PMF (T i)) (i : ι) :
    IsProbabilityMeasure ((ofPMF G d).prior i) := by
  dsimp only [ofPMF]
  infer_instance

section Equilibrium

variable [Fintype ι] [DecidableEq ι]

/-- Player `i`'s **interim expected utility** at type `ti` when playing action `xi` while every
other player `j ≠ i` plays `s j (t j)` for `t ∼ Measure.pi B.prior` ([Nisan2007],
Definition 9.41). Overwriting coordinate `i` with `xi` makes the integrand independent of `t i`;
when `B.prior i` is a probability measure, integrating over `Measure.pi B.prior` agrees with the
expectation over `D₋ᵢ` (matching `SingleParameter.Mechanism.interimAllocation`). -/
@[expose] noncomputable def interimUtility (B : BayesianGame ι T X) (s : ∀ i, T i → X i)
    (i : ι) (ti : T i) (xi : X i) : ℝ :=
  ∫ t, B.utility i ti (Function.update (fun j => s j (t j)) i xi) ∂Measure.pi B.prior

/-- Strategy profile `s` is a **Bayes–Nash equilibrium on type supports `S`** if for every player
`i`, every type `ti ∈ S i`, and every deviation `xi' : X i`, playing `s i ti` maximizes interim
expected utility. -/
@[expose] def IsBayesNashOn (B : BayesianGame ι T X) (S : ∀ i, Set (T i))
    (s : ∀ i, T i → X i) : Prop :=
  ∀ (i : ι) (ti : T i), ti ∈ S i → ∀ (xi' : X i),
    B.interimUtility s i ti xi' ≤ B.interimUtility s i ti (s i ti)

/-- Strategy profile `s` is a **Bayes–Nash equilibrium** ([Nisan2007], Definition 9.41): for every
player `i`, type `ti : T i`, and action `xi' : X i`, `s i ti` maximizes
`B.interimUtility s i ti`. -/
@[expose] def IsBayesNash (B : BayesianGame ι T X) (s : ∀ i, T i → X i) : Prop :=
  B.IsBayesNashOn (fun _ => Set.univ) s

@[simp] theorem isBayesNashOn_univ_iff (B : BayesianGame ι T X) (s : ∀ i, T i → X i) :
    B.IsBayesNashOn (fun _ => Set.univ) s ↔ B.IsBayesNash s :=
  Iff.rfl

theorem isBayesNash_iff (B : BayesianGame ι T X) (s : ∀ i, T i → X i) :
    B.IsBayesNash s ↔
      ∀ (i : ι) (ti : T i) (xi' : X i),
        B.interimUtility s i ti xi' ≤ B.interimUtility s i ti (s i ti) :=
  ⟨fun h i ti xi' => h i ti trivial xi', fun h i ti _ xi' => h i ti xi'⟩

/-- Every ex-post Nash equilibrium is a Bayes–Nash equilibrium whenever interim utilities are
integrable ([Nisan2007], §9.6.1, p. 234). -/
theorem isBayesNash_of_isExPostNash {B : BayesianGame ι T X} {s : ∀ i, T i → X i}
    (hs : B.toIncompleteInfoGame.IsExPostNash s)
    (hint : ∀ i ti xi, Integrable
      (fun t => B.utility i ti (Function.update (fun j => s j (t j)) i xi))
      (Measure.pi B.prior)) :
    B.IsBayesNash s := by
  rw [isBayesNash_iff]
  intro i ti xi'
  refine integral_mono (hint i ti xi') (hint i ti (s i ti)) fun t => ?_
  let t' : ∀ j, T j := Function.update t i ti
  have h1 : Function.update (fun j => s j (t j)) i xi' =
      Function.update (fun j => s j (t' j)) i xi' := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self, Function.update_self]
    · simp only [t', Function.update_of_ne hj]
  have h2 : Function.update (fun j => s j (t j)) i (s i ti) = fun j => s j (t' j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [t', Function.update_self]
    · simp only [t', Function.update_of_ne hj]
  rw [h1, h2]
  simpa only [t', Function.update_self] using hs i t' xi'

end Equilibrium

end BayesianGame

/-! ### Bridge to `SingleParameter.Mechanism.IsBayesNash` -/

namespace SingleParameter.Mechanism

variable {ι : Type*}

/-- View a single-parameter sealed-bid mechanism `M` with independent priors `μ : ι → Measure ℝ`
as a `BayesianGame` with type spaces `ℝ` and legal nonnegative bid spaces `Set.Ici (0 : ℝ)`. -/
@[expose] def toBayesianGame (M : Mechanism ι) (μ : ι → Measure ℝ) :
    BayesianGame ι (fun _ => ℝ) (fun _ => Set.Ici (0 : ℝ)) where
  utility i v x := M.utility i v fun j => (x j : ℝ)
  prior := μ

/-- **Bridge between `SingleParameter.Mechanism.IsBayesNash` and `BayesianGame.IsBayesNashOn`**:
when allocations and payments under `β` are integrable against `Measure.pi μ` for probability
measures `μ j` supported on `Icc 0 (h j)`, `M.IsBayesNash μ h β` is equivalent to legal bidding on
`Icc 0 (h i)` together with `(M.toBayesianGame μ).IsBayesNashOn`. -/
theorem isBayesNash_iff_toBayesianGame [Fintype ι] [DecidableEq ι]
    (M : Mechanism ι) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : ι → ℝ) (β : ι → ℝ → ℝ)
    (hsupp : ∀ j, ∀ᵐ t ∂μ j, t ∈ Icc 0 (h j))
    (hintA : ∀ i (z : ℝ), Integrable
      (fun v => M.allocation (Function.update (fun j => max 0 (β j (v j))) i z) i)
      (Measure.pi μ))
    (hintP : ∀ i (z : ℝ), Integrable
      (fun v => M.payment (Function.update (fun j => max 0 (β j (v j))) i z) i)
      (Measure.pi μ)) :
    M.IsBayesNash μ h β ↔
      (∀ i, ∀ v ∈ Icc 0 (h i), 0 ≤ β i v) ∧
      (M.toBayesianGame μ).IsBayesNashOn (fun i => Icc 0 (h i))
        (fun i v => ⟨max 0 (β i v), Set.mem_Ici.2 (le_max_left 0 (β i v))⟩) := by
  let s : ∀ i, ℝ → Set.Ici (0 : ℝ) :=
    fun i v => ⟨max 0 (β i v), Set.mem_Ici.2 (le_max_left 0 (β i v))⟩
  have hbox : ∀ᵐ v ∂Measure.pi μ, ∀ j, v j ∈ Icc 0 (h j) := by
    rw [ae_all_iff]
    intro j
    exact (Measure.quasiMeasurePreserving_eval μ j).ae (hsupp j)
  have hinterim : ∀ (hβ : ∀ j, ∀ v ∈ Icc 0 (h j), 0 ≤ β j v) (i : ι) (v : ℝ)
      (z : Set.Ici (0 : ℝ)),
      (M.toBayesianGame μ).interimUtility s i v z =
        v * M.interimAllocation μ β i z.1 - M.interimPayment μ β i z.1 := by
    intro hβ i v z
    have hcoe : ∀ t : ι → ℝ,
        (fun j => ((Function.update (fun k => s k (t k)) i z j : Set.Ici (0 : ℝ)) : ℝ)) =
          Function.update (fun j => max 0 (β j (t j))) i z.1 := by
      intro t
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Function.update_self]
      · simp only [s, Function.update_of_ne hj]
    have hae_eq : ∀ᵐ t ∂Measure.pi μ,
        Function.update (fun j => max 0 (β j (t j))) i z.1 =
          Function.update (fun j => β j (t j)) i z.1 := by
      filter_upwards [hbox] with t ht
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Function.update_self]
      · simp only [Function.update_of_ne hj, max_eq_right (hβ j (t j) (ht j))]
    simp only [BayesianGame.interimUtility, toBayesianGame, Mechanism.utility, hcoe]
    rw [integral_sub ((hintA i z.1).const_mul v) (hintP i z.1), integral_const_mul]
    have hA : ∫ t, M.allocation (Function.update (fun j => max 0 (β j (t j))) i z.1) i
        ∂Measure.pi μ = M.interimAllocation μ β i z.1 :=
      integral_congr_ae (hae_eq.mono fun t ht => by dsimp only; rw [ht])
    have hP : ∫ t, M.payment (Function.update (fun j => max 0 (β j (t j))) i z.1) i
        ∂Measure.pi μ = M.interimPayment μ β i z.1 :=
      integral_congr_ae (hae_eq.mono fun t ht => by dsimp only; rw [ht])
    rw [hA, hP]
  constructor
  · intro hM
    have hβ : ∀ j, ∀ v ∈ Icc 0 (h j), 0 ≤ β j v := fun j v hv => (hM j v hv).1
    refine ⟨hβ, fun i v hv z => ?_⟩
    rw [hinterim hβ i v z, hinterim hβ i v (s i v)]
    simp only [s, max_eq_right (hβ i v hv)]
    exact (hM i v hv).2 z.1 z.2
  · rintro ⟨hβ, hB⟩ i v hv
    refine ⟨hβ i v hv, fun z hz => ?_⟩
    have := hB i v hv ⟨z, hz⟩
    rw [hinterim hβ i v ⟨z, hz⟩, hinterim hβ i v (s i v)] at this
    simpa only [s, max_eq_right (hβ i v hv)] using this

end SingleParameter.Mechanism

/-! ### Bayesian mechanisms, `IsBICOn`, and the Bayesian Revelation Principle (§9.6.1) -/

/-- A **Bayesian mechanism** ([Nisan2007], Definition 9.42): players have type spaces `T i` with
independent priors `prior i`, action spaces `X i`, valuations `valuation i : T i → Ω → ℝ`, an
outcome rule `outcome : (∀ i, X i) → Ω`, and payment rules `payment : (∀ i, X i) → ι → ℝ`. -/
structure BayesianMechanism (ι : Type*) (T X : ι → Type*) (Ω : Type*)
    [∀ i, MeasurableSpace (T i)] extends IndirectMechanism ι X Ω where
  /-- Player `i`'s prior distribution `Dᵢ` on `T i`. -/
  prior : ∀ i, Measure (T i)
  /-- Player `i`'s valuation function `vᵢ : Tᵢ → Ω → ℝ`. -/
  valuation : ∀ i, T i → Ω → ℝ

namespace BayesianMechanism

variable {ι Ω : Type*} {T X : ι → Type*} [∀ i, MeasurableSpace (T i)]

/-- The Bayesian game induced by `M` ([Nisan2007], Definition 9.42). -/
@[expose] def toBayesianGame (M : BayesianMechanism ι T X Ω) : BayesianGame ι T X where
  toIncompleteInfoGame := M.toIndirectMechanism.toIncompleteInfoGame M.valuation
  prior := M.prior

/-- Simulate strategies `s : ∀ i, T i → X i` inside `M` to obtain a direct-revelation
`BayesianMechanism` (`X' = T`, [Nisan2007], Proposition 9.44). -/
@[expose] def revelation (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i) :
    BayesianMechanism ι T T Ω where
  toIndirectMechanism := M.toIndirectMechanism.revelation s
  prior := M.prior
  valuation := M.valuation

section Implementation

variable [Fintype ι] [DecidableEq ι]

/-- `M` **implements `f` in the Bayesian sense** if some Bayes–Nash equilibrium `s` of
`M.toBayesianGame` satisfies `M.outcome (fun j => s j (t j)) = f t` everywhere ([Nisan2007],
Definition 9.42). -/
@[expose] def ImplementsInBayesNash (M : BayesianMechanism ι T X Ω) (f : (∀ i, T i) → Ω) : Prop :=
  ∃ s : ∀ i, T i → X i,
    M.toBayesianGame.IsBayesNash s ∧ ∀ t, M.outcome (fun j => s j (t j)) = f t

/-- A direct `BayesianMechanism` (`X = T`) is **truthful in the Bayesian sense** if the truthful
strategies `fun _ => id` form a Bayes–Nash equilibrium ([Nisan2007], Definition 9.43). -/
@[expose] def IsTruthful (D : BayesianMechanism ι T T Ω) : Prop :=
  D.toBayesianGame.IsBayesNash fun _ => id

/-- Interim expected payment of player `i` at action `xi` when other players follow `s`. -/
@[expose] noncomputable def interimPayment (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i)
    (i : ι) (xi : X i) : ℝ :=
  ∫ t, M.payment (Function.update (fun j => s j (t j)) i xi) i ∂Measure.pi M.prior

/-- In `M.revelation s`, truthful interim utility at report `ti'` equals `M`'s interim utility at
action `s i ti'`. -/
@[simp] theorem revelation_interimUtility_eq (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) (i : ι) (ti ti' : T i) :
    (M.revelation s).toBayesianGame.interimUtility (fun _ => id) i ti ti' =
      M.toBayesianGame.interimUtility s i ti (s i ti') := by
  simp only [BayesianGame.interimUtility, toBayesianGame, revelation,
    IndirectMechanism.toIncompleteInfoGame, IndirectMechanism.revelation, id_eq]
  congr 1; funext t
  rw [funext (Function.apply_update s t i ti')]

/-- In `M.revelation s`, interim expected payment at report `ti` is identical to `M`'s equilibrium
interim expected payment at `s i ti` ([Nisan2007], Proposition 9.44). -/
@[simp] theorem revelation_interimPayment_eq (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) (i : ι) (ti : T i) :
    (M.revelation s).interimPayment (fun _ => id) i ti =
      M.interimPayment s i (s i ti) := by
  simp only [interimPayment, revelation, IndirectMechanism.revelation, id_eq]
  congr 1; funext t
  rw [funext (Function.apply_update s t i ti)]

/-- **Proposition 9.44 (Bayesian Revelation Principle, direct form)** ([Nisan2007], p. 234): if
`s` is a Bayes–Nash equilibrium of `M`, then `M.revelation s` is truthful in the Bayesian sense. -/
theorem revelation_isTruthful {M : BayesianMechanism ι T X Ω} {s : ∀ i, T i → X i}
    (hs : M.toBayesianGame.IsBayesNash s) :
    (M.revelation s).IsTruthful := by
  rw [IsTruthful, BayesianGame.isBayesNash_iff]
  intro i ti ti'
  rw [revelation_interimUtility_eq, revelation_interimUtility_eq]
  exact (M.toBayesianGame.isBayesNash_iff s).1 hs i ti (s i ti')

/-- **Proposition 9.44 (Bayesian Revelation Principle)** ([Nisan2007], p. 234): if an indirect
Bayesian mechanism `M` implements `f` in Bayes–Nash equilibrium, there exists a truthful direct
Bayesian mechanism `D` implementing `f` with the same priors, valuations, and ex-post as well as
interim expected equilibrium payments. -/
theorem exists_truthful_of_implementsInBayesNash {M : BayesianMechanism ι T X Ω}
    {f : (∀ i, T i) → Ω} (h : M.ImplementsInBayesNash f) :
    ∃ s : ∀ i, T i → X i,
      M.toBayesianGame.IsBayesNash s ∧
      ∃ D : BayesianMechanism ι T T Ω,
        D.IsTruthful ∧ D.prior = M.prior ∧ D.valuation = M.valuation ∧ D.outcome = f ∧
        (∀ t, D.payment t = M.payment (fun j => s j (t j))) ∧
        ∀ i ti, D.interimPayment (fun _ => id) i ti = M.interimPayment s i (s i ti) := by
  obtain ⟨s, hs, hf⟩ := h
  exact ⟨s, hs, M.revelation s, revelation_isTruthful hs, rfl, rfl, funext hf,
    fun _ => rfl, fun i ti => revelation_interimPayment_eq M s i ti⟩

end Implementation

end BayesianMechanism

/-! ### Bayesian incentive compatibility (`IsBICOn`) directly on `Mechanism ι Ω` -/

namespace Mechanism

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

/-- Interim expected utility of agent `i` with true valuation `v` reporting `w` in direct
`Mechanism ι Ω` when other agents draw truthful valuations from `Measure.pi μ`. -/
@[expose] noncomputable def interimUtility [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (i : ι) (v w : Ω → ℝ) : ℝ :=
  ∫ b, M.utility i v (Function.update b i w) ∂Measure.pi μ

/-- **Bayesian incentive compatibility on valuation domains `V`** (`IsBICOn`, [Nisan2007],
Definition 9.43): for every agent `i` and valuations `v, w ∈ V i`, reporting `v` maximizes interim
expected utility against independent priors `μ`. -/
@[expose] def IsBICOn [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (v w : Ω → ℝ), v ∈ V i → w ∈ V i →
    M.interimUtility μ i v w ≤ M.interimUtility μ i v v

/-- Unrestricted Bayesian incentive compatibility (`V i = Set.univ`). -/
@[expose] def IsBIC [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) : Prop :=
  M.IsBICOn μ fun _ => Set.univ

@[simp] theorem isBICOn_univ_iff [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) :
    M.IsBICOn μ (fun _ => Set.univ) ↔ M.IsBIC μ :=
  Iff.rfl

end Mechanism

namespace IndirectMechanism

/-- **Valuation-domain Bayesian Revelation Principle**: if `s : ∀ i, (Ω → ℝ) → X i` is a
Bayes–Nash equilibrium on valuation domains `V : ι → Set (Ω → ℝ)` under priors `μ`, then the
simulated direct `M.toMechanism s : Mechanism ι Ω` satisfies `IsBICOn μ V`. -/
theorem toMechanism_isBICOn {ι Ω : Type*} {X : ι → Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (Ω → ℝ)] (M : IndirectMechanism ι X Ω) (μ : ι → Measure (Ω → ℝ))
    (V : ι → Set (Ω → ℝ)) {s : ∀ i, (Ω → ℝ) → X i}
    (hs : ({ toIncompleteInfoGame := M.toIncompleteInfoGame (fun _ (v : Ω → ℝ) => v)
             prior := μ } : BayesianGame ι (fun _ => Ω → ℝ) X).IsBayesNashOn V s) :
    (M.toMechanism s).IsBICOn μ V := by
  intro i v w hv hw
  have h := hs i v hv (s i w)
  have hupd : ∀ (b : ι → Ω → ℝ) (z : Ω → ℝ),
      (fun j => s j (Function.update b i z j)) =
        Function.update (fun j => s j (b j)) i (s i z) := fun b z =>
    funext (Function.apply_update s b i z)
  simpa only [Mechanism.interimUtility, Mechanism.utility, toMechanism,
    BayesianGame.interimUtility, toIncompleteInfoGame, hupd] using h

end IndirectMechanism

end Cslib.GameTheory
