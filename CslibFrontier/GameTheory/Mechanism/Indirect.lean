/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Bayesian
public import CslibFrontier.GameTheory.Mechanism.VCG
public import CslibFrontier.GameTheory.Strategic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate

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
  `BayesianGame.IsBayesNashOn`, with integrability `BayesianGame.HasIntegrableUtilityOn`), bridged
  to `SingleParameter.Mechanism.IsBayesNash`
  (`SingleParameter.Mechanism.isBayesNash_iff_toBayesianGame`). Under independent probability
  priors `[∀ i, IsProbabilityMeasure (M.prior i)]` and integrable interim utilities
  (`BayesianMechanism.ImplementsInBayesNash`), composing `(M, s)` yields a truthful direct
  `BayesianMechanism` (`M.revelation s`) with probability priors, integrable truthful interim
  utilities, identical ex-post and interim payment integrals, and identical ex-ante expected
  payments whenever equilibrium payments are product-measure integrable
  (`BayesianMechanism.exists_truthful_of_implementsInBayesNash`,
  `BayesianMechanism.revelation_integral_payment_eq`; see
  `BayesianMechanism.exists_truthful_hasIntegrableInterimPayment` for all-types interim-payment
  slice integrability), derived from the general measure-theoretic integral-preservation steps
  (`BayesianMechanism.revelation_isTruthful`, `BayesianMechanism.revelation_interimPayment_eq`,
  and `IndirectMechanism.toMechanism_isBICOn`).

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
  `BayesianGame.HasIntegrableUtilityOn`, `BayesianGame.HasIntegrableUtility`,
  `BayesianGame.IsBayesNashOn`, `BayesianGame.IsBayesNash`: multi-parameter Bayesian games
  ([Nisan2007], Definitions 9.40–9.41).
* `SingleParameter.Mechanism.toBayesianGame`: single-parameter mechanisms as Bayesian games.
* `BayesianMechanism`, `BayesianMechanism.toBayesianGame`,
  `BayesianMechanism.HasIntegrableInterimPayment`, `BayesianMechanism.ImplementsInBayesNash`,
  `BayesianMechanism.revelation`, `BayesianMechanism.IsTruthful`,
  `BayesianMechanism.interimPayment`: Bayesian mechanisms ([Nisan2007], Definitions 9.42–9.43).
* `Mechanism.interimUtility`, `Mechanism.HasIntegrableUtilityOn`, `Mechanism.HasIntegrableUtility`,
  `Mechanism.IsBICOn`, `Mechanism.IsBIC`: Bayesian incentive compatibility on valuation domains
  `V : ι → Set (Ω → ℝ)`.

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
* `BayesianMechanism.revelation_isTruthful`, `BayesianMechanism.revelation_interimPayment_eq`,
  `BayesianMechanism.revelation_hasIntegrableUtility`,
  `BayesianMechanism.revelation_hasIntegrableInterimPayment_iff`,
  `IndirectMechanism.toMechanism_hasIntegrableUtilityOn`,
  `IndirectMechanism.toMechanism_isBICOn`: general measure-theoretic integral- and
  integrability-preservation steps for direct simulation.
* `BayesianMechanism.interimUtility_eq_sub_interimPayment`,
  `BayesianMechanism.integral_payment_eq_integral_interimPayment`,
  `BayesianMechanism.revelation_integral_payment_eq`,
  `BayesianMechanism.exists_truthful_of_implementsInBayesNash`,
  `BayesianMechanism.exists_truthful_hasIntegrableInterimPayment`: **Proposition 9.44 (Bayesian
  Revelation Principle)** of [Nisan2007] with independent probability priors and integrable utility
  and payment expectations.

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
def fullInfoCostGame (t : ∀ i, T i) : CostGame ι X where
  cost i x := -G.utility i (t i) x

@[simp] theorem fullInfoCostGame_cost (t : ∀ i, T i) (i : ι) (x : ∀ j, X j) :
    (G.fullInfoCostGame t).cost i x = -G.utility i (t i) x := by
  rfl

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
def restrictRange (G : IncompleteInfoGame ι T X) (s : ∀ i, T i → X i) :
    IncompleteInfoGame ι T (fun i => Set.range (s i)) where
  utility i ti x := G.utility i ti fun j => (x j : X j)

omit [DecidableEq ι] in
@[simp] theorem restrictRange_utility (G : IncompleteInfoGame ι T X) (s : ∀ i, T i → X i)
    (i : ι) (ti : T i) (x : ∀ j, Set.range (s j)) :
    (G.restrictRange s).utility i ti x = G.utility i ti fun j => (x j : X j) := by
  rfl

/-- **Proposition 9.23** of [Nisan2007]: if `s` is an ex-post Nash equilibrium of `G`, then
restricting each action space `X i` to `Set.range (s i)` makes `s` (viewed via
`Set.rangeFactorization`) a dominant-strategy equilibrium of `G.restrictRange s`. -/
theorem IsExPostNash.isDominantStrategyEquilibrium_restrictRange {s : ∀ i, T i → X i}
    (hs : G.IsExPostNash s) :
    (G.restrictRange s).IsDominantStrategyEquilibrium
      (fun i => Set.rangeFactorization (s i)) := by
  intro i ti x
  choose t₀ ht₀ using fun j => (x j).property
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
def toIncompleteInfoGame (M : IndirectMechanism ι X Ω) (val : ∀ i, T i → Ω → ℝ) :
    IncompleteInfoGame ι T X where
  utility i ti x := val i ti (M.outcome x) - M.payment x i

@[simp] theorem toIncompleteInfoGame_utility (M : IndirectMechanism ι X Ω)
    (val : ∀ i, T i → Ω → ℝ) (i : ι) (ti : T i) (x : ∀ j, X j) :
    (M.toIncompleteInfoGame val).utility i ti x = val i ti (M.outcome x) - M.payment x i := by
  rfl

/-- Simulate strategies `s : ∀ i, T i → X i` inside `M` to obtain a direct-revelation mechanism
(`X' = T`, [Nisan2007], proof of Proposition 9.25). -/
def revelation (M : IndirectMechanism ι X Ω) (s : ∀ i, T i → X i) :
    IndirectMechanism ι T Ω where
  outcome t := M.outcome fun j => s j (t j)
  payment t := M.payment fun j => s j (t j)

@[simp] theorem revelation_outcome (M : IndirectMechanism ι X Ω) (s : ∀ i, T i → X i)
    (t : ∀ i, T i) : (M.revelation s).outcome t = M.outcome fun j => s j (t j) := by
  rfl

@[simp] theorem revelation_payment (M : IndirectMechanism ι X Ω) (s : ∀ i, T i → X i)
    (t : ∀ i, T i) : (M.revelation s).payment t = M.payment fun j => s j (t j) := by
  rfl

/-- Convert an indirect mechanism `M` and valuation-indexed strategies `s : ∀ i, (Ω → ℝ) → X i`
into a `Cslib.GameTheory.Mechanism ι Ω`. -/
def toMechanism (M : IndirectMechanism ι X Ω) (s : ∀ i, (Ω → ℝ) → X i) :
    Mechanism ι Ω where
  outcome b := M.outcome fun j => s j (b j)
  payment b := M.payment fun j => s j (b j)

@[simp] theorem toMechanism_outcome (M : IndirectMechanism ι X Ω) (s : ∀ i, (Ω → ℝ) → X i)
    (b : ι → Ω → ℝ) : (M.toMechanism s).outcome b = M.outcome fun j => s j (b j) := by
  rfl

@[simp] theorem toMechanism_payment (M : IndirectMechanism ι X Ω) (s : ∀ i, (Ω → ℝ) → X i)
    (b : ι → Ω → ℝ) : (M.toMechanism s).payment b = M.payment fun j => s j (b j) := by
  rfl

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
    (hs : (M.toIncompleteInfoGame (T := fun i => V i) (fun _ v => v.val)).IsExPostNash
      (fun i v => s i v.val)) :
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

/-! ### Bayesian games and the Bayesian revelation principle (§9.6.1, Defs 9.40–9.43, Prop 9.44) -/

/-- A game with independent private values and **Bayesian incomplete information** ([Nisan2007],
Definition 9.40; [Harsanyi1967]): extends `IncompleteInfoGame ι T X` with an independent prior
measure `prior i` on each player's type space `T i`. Each `prior i` is intended to carry
`IsProbabilityMeasure` (as in `SingleParameter.Mechanism.IsBayesNash`); if `prior j = 0` for some
`j`, then `Measure.pi prior = 0` and all interim utilities vanish identically. -/
structure BayesianGame (ι : Type*) (T X : ι → Type*) [∀ i, MeasurableSpace (T i)]
    extends IncompleteInfoGame ι T X where
  /-- Player `i`'s prior type distribution `Dᵢ`. -/
  prior : ∀ i, Measure (T i)

namespace BayesianGame

variable {ι : Type*} {T X : ι → Type*} [∀ i, MeasurableSpace (T i)]

/-- Construct a `BayesianGame` from discrete `PMF` priors via `PMF.toMeasure`. -/
noncomputable def ofPMF (G : IncompleteInfoGame ι T X) (d : ∀ i, PMF (T i)) :
    BayesianGame ι T X where
  toIncompleteInfoGame := G
  prior i := (d i).toMeasure

@[simp] theorem ofPMF_toIncompleteInfoGame (G : IncompleteInfoGame ι T X) (d : ∀ i, PMF (T i)) :
    (ofPMF G d).toIncompleteInfoGame = G := by
  rfl

@[simp] theorem ofPMF_prior (G : IncompleteInfoGame ι T X) (d : ∀ i, PMF (T i)) (i : ι) :
    (ofPMF G d).prior i = (d i).toMeasure := by
  rfl

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
noncomputable def interimUtility (B : BayesianGame ι T X) (s : ∀ i, T i → X i)
    (i : ι) (ti : T i) (xi : X i) : ℝ :=
  ∫ t, B.utility i ti (Function.update (fun j => s j (t j)) i xi) ∂Measure.pi B.prior

theorem interimUtility_def (B : BayesianGame ι T X) (s : ∀ i, T i → X i) (i : ι) (ti : T i)
    (xi : X i) :
    B.interimUtility s i ti xi =
      ∫ t, B.utility i ti (Function.update (fun j => s j (t j)) i xi) ∂Measure.pi B.prior := by
  rfl

/-- Strategy profile `s` has **integrable interim utilities** on type supports `S` if for every
player `i`, type `ti ∈ S i`, and action `xi : X i`, the payoff integrand in
`B.interimUtility s i ti xi` is Bochner-integrable against `Measure.pi B.prior`. Together with
`[∀ i, IsProbabilityMeasure (B.prior i)]`, this ensures every `B.interimUtility s i ti xi`
compared by `IsBayesNashOn` is a genuine probability expectation rather than a zero-measure or
`0`-fallback Bochner integral. -/
@[expose] def HasIntegrableUtilityOn (B : BayesianGame ι T X) (S : ∀ i, Set (T i))
    (s : ∀ i, T i → X i) : Prop :=
  ∀ (i : ι) (ti : T i), ti ∈ S i → ∀ (xi : X i),
    Integrable (fun t => B.utility i ti (Function.update (fun j => s j (t j)) i xi))
      (Measure.pi B.prior)

/-- Strategy profile `s` has integrable interim utilities at all types (`S i = Set.univ`). -/
abbrev HasIntegrableUtility (B : BayesianGame ι T X) (s : ∀ i, T i → X i) : Prop :=
  B.HasIntegrableUtilityOn (fun _ => Set.univ) s

theorem hasIntegrableUtility_iff (B : BayesianGame ι T X) (s : ∀ i, T i → X i) :
    B.HasIntegrableUtility s ↔
      ∀ (i : ι) (ti : T i) (xi : X i),
        Integrable (fun t => B.utility i ti (Function.update (fun j => s j (t j)) i xi))
          (Measure.pi B.prior) :=
  ⟨fun h i ti xi => h i ti trivial xi, fun h i ti _ xi => h i ti xi⟩

/-- Strategy profile `s` is a **Bayes–Nash equilibrium on type supports `S`** if for every player
`i`, every type `ti ∈ S i`, and every deviation `xi' : X i`, playing `s i ti` maximizes interim
expected utility. Each `B.prior i` is intended to carry `IsProbabilityMeasure`: if `B.prior j = 0`
for some `j`, then `Measure.pi B.prior = 0` and every interim utility is `0`. -/
@[expose] def IsBayesNashOn (B : BayesianGame ι T X) (S : ∀ i, Set (T i))
    (s : ∀ i, T i → X i) : Prop :=
  ∀ (i : ι) (ti : T i), ti ∈ S i → ∀ (xi' : X i),
    B.interimUtility s i ti xi' ≤ B.interimUtility s i ti (s i ti)

/-- Strategy profile `s` is a **Bayes–Nash equilibrium** ([Nisan2007], Definition 9.41): for every
player `i`, type `ti : T i`, and action `xi' : X i`, `s i ti` maximizes `B.interimUtility s i ti`.
Each `B.prior i` is intended to carry `IsProbabilityMeasure`: without it, `B.prior j = 0` makes
`Measure.pi B.prior = 0` and the condition holds vacuously. -/
abbrev IsBayesNash (B : BayesianGame ι T X) (s : ∀ i, T i → X i) : Prop :=
  B.IsBayesNashOn (fun _ => Set.univ) s

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
def toBayesianGame (M : Mechanism ι) (μ : ι → Measure ℝ) :
    BayesianGame ι (fun _ => ℝ) (fun _ => Set.Ici (0 : ℝ)) where
  utility i v x := M.utility i v fun j => (x j : ℝ)
  prior := μ

@[simp] theorem toBayesianGame_utility (M : Mechanism ι) (μ : ι → Measure ℝ) (i : ι) (v : ℝ)
    (x : ι → Set.Ici (0 : ℝ)) :
    (M.toBayesianGame μ).utility i v x = M.utility i v fun j => (x j : ℝ) := by
  rfl

@[simp] theorem toBayesianGame_prior (M : Mechanism ι) (μ : ι → Measure ℝ) :
    (M.toBayesianGame μ).prior = μ := by
  rfl

/-- **Bridge between `SingleParameter.Mechanism.IsBayesNash` and `BayesianGame.IsBayesNashOn`**:
when allocations and payments at nonnegative bids under `β` are integrable against `Measure.pi μ`
for probability measures `μ j` supported on `Icc 0 (h j)`, `M.IsBayesNash μ h β` is equivalent to
legal bidding on `Icc 0 (h i)` together with `(M.toBayesianGame μ).IsBayesNashOn`. -/
theorem isBayesNash_iff_toBayesianGame [Fintype ι] [DecidableEq ι]
    (M : Mechanism ι) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : ι → ℝ) (β : ι → ℝ → ℝ)
    (hsupp : ∀ j, ∀ᵐ t ∂μ j, t ∈ Icc 0 (h j))
    (hintA : ∀ i (z : ℝ), 0 ≤ z → Integrable
      (fun v => M.allocation (Function.update (fun j => max 0 (β j (v j))) i z) i)
      (Measure.pi μ))
    (hintP : ∀ i (z : ℝ), 0 ≤ z → Integrable
      (fun v => M.payment (Function.update (fun j => max 0 (β j (v j))) i z) i)
      (Measure.pi μ)) :
    M.IsBayesNash μ h β ↔
      (∀ i, ∀ v ∈ Icc 0 (h i), 0 ≤ β i v) ∧
      (M.toBayesianGame μ).IsBayesNashOn (fun i => Icc 0 (h i))
        (fun i v => ⟨max 0 (β i v), Set.mem_Ici.2 (le_max_left 0 (β i v))⟩) := by
  let s : ∀ i, ℝ → Set.Ici (0 : ℝ) :=
    fun i v => ⟨max 0 (β i v), Set.mem_Ici.2 (le_max_left 0 (β i v))⟩
  have hbox : ∀ᵐ v ∂Measure.pi μ, ∀ j, v j ∈ Icc 0 (h j) :=
    ae_all_iff.2 fun j => (Measure.quasiMeasurePreserving_eval μ j).ae (hsupp j)
  have hinterim : ∀ (hβ : ∀ j, ∀ v ∈ Icc 0 (h j), 0 ≤ β j v) (i : ι) (v : ℝ)
      (z : Set.Ici (0 : ℝ)),
      (M.toBayesianGame μ).interimUtility s i v z =
        v * M.interimAllocation μ β i z.val - M.interimPayment μ β i z.val := by
    intro hβ i v z
    have hcoe : ∀ t : ι → ℝ,
        (fun j => ((Function.update (fun k => s k (t k)) i z j : Set.Ici (0 : ℝ)) : ℝ)) =
          Function.update (fun j => max 0 (β j (t j))) i z.val := by
      intro t
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Function.update_self]
      · simp only [s, Function.update_of_ne hj]
    have hae_eq : ∀ᵐ t ∂Measure.pi μ,
        Function.update (fun j => max 0 (β j (t j))) i z.val =
          Function.update (fun j => β j (t j)) i z.val := by
      filter_upwards [hbox] with t ht
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Function.update_self]
      · simp only [Function.update_of_ne hj, max_eq_right (hβ j (t j) (ht j))]
    simp only [BayesianGame.interimUtility, toBayesianGame, Mechanism.utility, hcoe]
    rw [integral_sub ((hintA i z.val z.property).const_mul v) (hintP i z.val z.property),
        integral_const_mul]
    have hA : ∫ t, M.allocation (Function.update (fun j => max 0 (β j (t j))) i z.val) i
        ∂Measure.pi μ = M.interimAllocation μ β i z.val :=
      integral_congr_ae (hae_eq.mono fun t ht => by dsimp only; rw [ht])
    have hP : ∫ t, M.payment (Function.update (fun j => max 0 (β j (t j))) i z.val) i
        ∂Measure.pi μ = M.interimPayment μ β i z.val :=
      integral_congr_ae (hae_eq.mono fun t ht => by dsimp only; rw [ht])
    rw [hA, hP]
  constructor
  · intro hM
    have hβ : ∀ j, ∀ v ∈ Icc 0 (h j), 0 ≤ β j v := fun j v hv => (hM j v hv).1
    refine ⟨hβ, fun i v hv z => ?_⟩
    rw [hinterim hβ i v z, hinterim hβ i v (s i v)]
    simp only [s, max_eq_right (hβ i v hv)]
    exact (hM i v hv).2 z.val z.property
  · rintro ⟨hβ, hB⟩ i v hv
    refine ⟨hβ i v hv, fun z hz => ?_⟩
    have := hB i v hv ⟨z, hz⟩
    rw [hinterim hβ i v ⟨z, hz⟩, hinterim hβ i v (s i v)] at this
    simpa only [s, max_eq_right (hβ i v hv)] using this

end SingleParameter.Mechanism

/-! ### Bayesian mechanisms, `IsBICOn`, and the Bayesian Revelation Principle (§9.6.1) -/

/-- A **Bayesian mechanism** ([Nisan2007], Definition 9.42): players have type spaces `T i` with
independent priors `prior i`, action spaces `X i`, valuations `valuation i : T i → Ω → ℝ`, an
outcome rule `outcome : (∀ i, X i) → Ω`, and payment rules `payment : (∀ i, X i) → ι → ℝ`.
Each `prior i` is intended to carry `IsProbabilityMeasure`: if `prior j = 0` for some `j`, then
`Measure.pi prior = 0`, making interim utilities and interim payments identically `0`. -/
structure BayesianMechanism (ι : Type*) (T X : ι → Type*) (Ω : Type*)
    [∀ i, MeasurableSpace (T i)] extends IndirectMechanism ι X Ω where
  /-- Player `i`'s prior distribution `Dᵢ` on `T i`. -/
  prior : ∀ i, Measure (T i)
  /-- Player `i`'s valuation function `vᵢ : Tᵢ → Ω → ℝ`. -/
  valuation : ∀ i, T i → Ω → ℝ

namespace BayesianMechanism

variable {ι Ω : Type*} {T X : ι → Type*} [∀ i, MeasurableSpace (T i)]

/-- The Bayesian game induced by `M` ([Nisan2007], Definition 9.42). -/
def toBayesianGame (M : BayesianMechanism ι T X Ω) : BayesianGame ι T X where
  toIncompleteInfoGame := M.toIndirectMechanism.toIncompleteInfoGame M.valuation
  prior := M.prior

@[simp] theorem toBayesianGame_utility (M : BayesianMechanism ι T X Ω) (i : ι) (ti : T i)
    (x : ∀ j, X j) :
    M.toBayesianGame.utility i ti x = M.valuation i ti (M.outcome x) - M.payment x i := by
  rfl

@[simp] theorem toBayesianGame_prior (M : BayesianMechanism ι T X Ω) :
    M.toBayesianGame.prior = M.prior := by
  rfl

instance isProbabilityMeasure_toBayesianGame (M : BayesianMechanism ι T X Ω) (i : ι)
    [IsProbabilityMeasure (M.prior i)] :
    IsProbabilityMeasure (M.toBayesianGame.prior i) := by
  dsimp only [toBayesianGame]
  infer_instance

/-- Simulate strategies `s : ∀ i, T i → X i` inside `M` to obtain a direct-revelation
`BayesianMechanism` (`X' = T`, [Nisan2007], Proposition 9.44). -/
def revelation (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i) :
    BayesianMechanism ι T T Ω where
  toIndirectMechanism := M.toIndirectMechanism.revelation s
  prior := M.prior
  valuation := M.valuation

@[simp] theorem revelation_toIndirectMechanism (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) :
    (M.revelation s).toIndirectMechanism = M.toIndirectMechanism.revelation s := by
  rfl

@[simp] theorem revelation_prior (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i) :
    (M.revelation s).prior = M.prior := by
  rfl

@[simp] theorem revelation_valuation (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i) :
    (M.revelation s).valuation = M.valuation := by
  rfl

instance isProbabilityMeasure_revelation (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i)
    (i : ι) [IsProbabilityMeasure (M.prior i)] :
    IsProbabilityMeasure ((M.revelation s).prior i) := by
  dsimp only [revelation]
  infer_instance

section Implementation

variable [Fintype ι] [DecidableEq ι]

/-- Interim expected payment of player `i` at action `xi` when other players follow `s`. -/
noncomputable def interimPayment (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i)
    (i : ι) (xi : X i) : ℝ :=
  ∫ t, M.payment (Function.update (fun j => s j (t j)) i xi) i ∂Measure.pi M.prior

theorem interimPayment_def (M : BayesianMechanism ι T X Ω) (s : ∀ i, T i → X i) (i : ι)
    (xi : X i) :
    M.interimPayment s i xi =
      ∫ t, M.payment (Function.update (fun j => s j (t j)) i xi) i ∂Measure.pi M.prior := by
  rfl

/-- Strategy profile `s` has **integrable equilibrium interim payments** if for every player `i`
and type `ti`, the payment integrand in `M.interimPayment s i (s i ti)` is Bochner-integrable
against `Measure.pi M.prior`. -/
@[expose] def HasIntegrableInterimPayment (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) : Prop :=
  ∀ (i : ι) (ti : T i),
    Integrable (fun t => M.payment (Function.update (fun j => s j (t j)) i (s i ti)) i)
      (Measure.pi M.prior)

/-- `M` **implements `f` in the Bayesian sense** ([Nisan2007], Definition 9.42) if some
Bayes–Nash equilibrium `s` of `M.toBayesianGame` with integrable interim utilities satisfies
`M.outcome (fun j => s j (t j)) = f t` everywhere. Together with
`[∀ i, IsProbabilityMeasure (M.prior i)]`, this ensures the equilibrium comparisons are genuine
probability expectations. -/
@[expose] def ImplementsInBayesNash (M : BayesianMechanism ι T X Ω) (f : (∀ i, T i) → Ω) : Prop :=
  ∃ s : ∀ i, T i → X i,
    M.toBayesianGame.HasIntegrableUtility s ∧
    M.toBayesianGame.IsBayesNash s ∧
    ∀ t, M.outcome (fun j => s j (t j)) = f t

/-- A direct `BayesianMechanism` (`X = T`) is **truthful in the Bayesian sense** if the truthful
strategies `fun _ => id` form a Bayes–Nash equilibrium ([Nisan2007], Definition 9.43). -/
@[expose] def IsTruthful (D : BayesianMechanism ι T T Ω) : Prop :=
  D.toBayesianGame.IsBayesNash fun _ => id

/-- When player `i`'s utility integrand at `(ti, xi)` and payment integrand at `xi` are both
integrable against `Measure.pi M.prior`, the valuation integrand is also integrable and interim
quasilinear utility splits into expected valuation minus `M.interimPayment s i xi`. -/
theorem interimUtility_eq_sub_interimPayment {M : BayesianMechanism ι T X Ω}
    {s : ∀ i, T i → X i} {i : ι} {ti : T i} {xi : X i}
    (hintU : Integrable
      (fun t => M.toBayesianGame.utility i ti (Function.update (fun j => s j (t j)) i xi))
      (Measure.pi M.prior))
    (hintP : Integrable
      (fun t => M.payment (Function.update (fun j => s j (t j)) i xi) i)
      (Measure.pi M.prior)) :
    M.toBayesianGame.interimUtility s i ti xi =
      (∫ t, M.valuation i ti (M.outcome (Function.update (fun j => s j (t j)) i xi))
        ∂Measure.pi M.prior) - M.interimPayment s i xi := by
  have hintV : Integrable
      (fun t => M.valuation i ti (M.outcome (Function.update (fun j => s j (t j)) i xi)))
      (Measure.pi M.prior) := by
    refine (hintU.add hintP).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, toBayesianGame_utility, sub_add_cancel]
  simp only [BayesianGame.interimUtility, interimPayment, toBayesianGame_utility,
    toBayesianGame_prior]
  exact integral_sub hintV hintP

/-- Under independent probability priors, player `i`'s ex-ante expected equilibrium payment equals
the prior expectation of its interim equilibrium payment `M.interimPayment s i (s i ti)` (Fubini
over coordinate `i`). -/
theorem integral_payment_eq_integral_interimPayment (M : BayesianMechanism ι T X Ω)
    [∀ i, IsProbabilityMeasure (M.prior i)] (s : ∀ i, T i → X i) (i : ι)
    (hp : Integrable (fun t => M.payment (fun j => s j (t j)) i) (Measure.pi M.prior)) :
    ∫ t, M.payment (fun j => s j (t j)) i ∂Measure.pi M.prior =
      ∫ ti, M.interimPayment s i (s i ti) ∂M.prior i := by
  rw [← integral_integral_update_swap M.prior hp i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ti => ?_)
  simp only [interimPayment]
  congr 1; funext t
  rw [funext (Function.apply_update s t i ti)]

/-- In `M.revelation s`, truthful interim utility at report `ti'` equals `M`'s interim utility at
action `s i ti'` (general measure-theoretic integral-preservation step). -/
@[simp] theorem revelation_interimUtility_eq (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) (i : ι) (ti ti' : T i) :
    (M.revelation s).toBayesianGame.interimUtility (fun _ => id) i ti ti' =
      M.toBayesianGame.interimUtility s i ti (s i ti') := by
  simp only [BayesianGame.interimUtility, toBayesianGame, revelation,
    IndirectMechanism.toIncompleteInfoGame, IndirectMechanism.revelation, id_eq]
  congr 1; funext t
  rw [funext (Function.apply_update s t i ti')]

/-- General measure-theoretic integral-preservation step for [Nisan2007], Proposition 9.44: for
arbitrary prior measures, `(M.revelation s).interimPayment (fun _ => id) i ti` equals `M`'s
equilibrium interim integral `M.interimPayment s i (s i ti)`. -/
@[simp] theorem revelation_interimPayment_eq (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) (i : ι) (ti : T i) :
    (M.revelation s).interimPayment (fun _ => id) i ti =
      M.interimPayment s i (s i ti) := by
  simp only [interimPayment, revelation, IndirectMechanism.revelation, id_eq]
  congr 1; funext t
  rw [funext (Function.apply_update s t i ti)]

/-- Simulating `s` inside `M` preserves integrability of interim utilities: if `s` has integrable
interim utilities in `M`, then truthful reporting `fun _ => id` has integrable interim utilities
in `M.revelation s`. -/
theorem revelation_hasIntegrableUtility {M : BayesianMechanism ι T X Ω} {s : ∀ i, T i → X i}
    (hint : M.toBayesianGame.HasIntegrableUtility s) :
    (M.revelation s).toBayesianGame.HasIntegrableUtility (fun _ => id) := by
  intro i ti _ ti'
  refine (hint i ti trivial (s i ti')).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [toBayesianGame, revelation, IndirectMechanism.toIncompleteInfoGame,
    IndirectMechanism.revelation, id_eq]
  rw [funext (Function.apply_update s t i ti')]

/-- Truthful reporting in `M.revelation s` has integrable interim payments if and only if `s` has
integrable equilibrium interim payments in `M`. -/
@[simp] theorem revelation_hasIntegrableInterimPayment_iff (M : BayesianMechanism ι T X Ω)
    (s : ∀ i, T i → X i) :
    (M.revelation s).HasIntegrableInterimPayment (fun _ => id) ↔
      M.HasIntegrableInterimPayment s := by
  simp only [HasIntegrableInterimPayment, revelation, IndirectMechanism.revelation, id_eq]
  refine forall₂_congr fun i ti => ?_
  have heq : (fun t => M.payment (fun j => s j (Function.update t i ti j)) i) =
      fun t => M.payment (Function.update (fun j => s j (t j)) i (s i ti)) i := by
    funext t
    rw [funext (Function.apply_update s t i ti)]
  rw [heq]

/-- **Proposition 9.44 (Bayesian Revelation Principle, ex-ante payment expectation)**
([Nisan2007], §9.6.1, p. 234): under independent probability priors and product-measure integrable
equilibrium payments (which imply almost-everywhere integrable interim slices without requiring
integrability at null-measure exceptional types), player `i`'s ex-ante expected payment in
`M.revelation s` is integrable and equals both `M`'s ex-ante expected equilibrium payment and the
prior expectation of `M`'s interim equilibrium payments. -/
theorem revelation_integral_payment_eq {M : BayesianMechanism ι T X Ω}
    [∀ i, IsProbabilityMeasure (M.prior i)] {s : ∀ i, T i → X i} (i : ι)
    (hp : Integrable (fun t => M.payment (fun j => s j (t j)) i) (Measure.pi M.prior)) :
    Integrable (fun t => (M.revelation s).payment t i) (Measure.pi (M.revelation s).prior) ∧
      ∫ t, (M.revelation s).payment t i ∂Measure.pi (M.revelation s).prior =
        ∫ t, M.payment (fun j => s j (t j)) i ∂Measure.pi M.prior ∧
      ∫ t, (M.revelation s).payment t i ∂Measure.pi (M.revelation s).prior =
        ∫ ti, M.interimPayment s i (s i ti) ∂M.prior i :=
  ⟨hp, rfl, M.integral_payment_eq_integral_interimPayment s i hp⟩

/-- General measure-theoretic integral-preservation step for [Nisan2007], Proposition 9.44: for
arbitrary prior measures (without assuming probability normalization or integrability), if `s`
satisfies `IsBayesNash` in `M`, then `M.revelation s` satisfies `IsTruthful`. For the
source-facing probability-prior formulation with integrable utility and payment expectations, see
`exists_truthful_of_implementsInBayesNash`. -/
theorem revelation_isTruthful {M : BayesianMechanism ι T X Ω} {s : ∀ i, T i → X i}
    (hs : M.toBayesianGame.IsBayesNash s) :
    (M.revelation s).IsTruthful := by
  rw [IsTruthful, BayesianGame.isBayesNash_iff]
  intro i ti ti'
  rw [revelation_interimUtility_eq, revelation_interimUtility_eq]
  exact (M.toBayesianGame.isBayesNash_iff s).1 hs i ti (s i ti')

/-- **Proposition 9.44 (Bayesian Revelation Principle)** ([Nisan2007], §9.6.1, p. 234): under
independent probability priors `[∀ i, IsProbabilityMeasure (M.prior i)]`, if an indirect Bayesian
mechanism `M` implements `f` in Bayes–Nash equilibrium (`M.ImplementsInBayesNash f`), there exists
an implementing Bayes–Nash equilibrium `s` and a truthful direct Bayesian mechanism `D`
implementing `f` with the same probability priors and valuations, integrable truthful interim
utilities, identical ex-post and interim payment integrals, and—whenever player `i`'s equilibrium
payment in `M` is integrable against `Measure.pi M.prior`—integrable ex-ante payment in `D` with
identical ex-ante expected payment. Derived from the general integral-preservation steps
`revelation_isTruthful` and `revelation_interimPayment_eq`. -/
theorem exists_truthful_of_implementsInBayesNash {M : BayesianMechanism ι T X Ω}
    [∀ i, IsProbabilityMeasure (M.prior i)] {f : (∀ i, T i) → Ω}
    (h : M.ImplementsInBayesNash f) :
    ∃ s : ∀ i, T i → X i,
      M.toBayesianGame.HasIntegrableUtility s ∧
      M.toBayesianGame.IsBayesNash s ∧
      (∀ t, M.outcome (fun j => s j (t j)) = f t) ∧
      ∃ D : BayesianMechanism ι T T Ω,
        (∀ i, IsProbabilityMeasure (D.prior i)) ∧
        D.IsTruthful ∧
        D.toBayesianGame.HasIntegrableUtility (fun _ => id) ∧
        D.prior = M.prior ∧ D.valuation = M.valuation ∧ D.outcome = f ∧
        (∀ t, D.payment t = M.payment (fun j => s j (t j))) ∧
        (∀ i ti, D.interimPayment (fun _ => id) i ti = M.interimPayment s i (s i ti)) ∧
        ∀ i, Integrable (fun t => M.payment (fun j => s j (t j)) i) (Measure.pi M.prior) →
          Integrable (fun t => D.payment t i) (Measure.pi D.prior) ∧
          ∫ t, D.payment t i ∂Measure.pi D.prior =
            ∫ t, M.payment (fun j => s j (t j)) i ∂Measure.pi M.prior := by
  obtain ⟨s, hintU, hs, hf⟩ := h
  exact ⟨s, hintU, hs, hf, M.revelation s, fun _ => inferInstance, revelation_isTruthful hs,
    revelation_hasIntegrableUtility hintU, rfl, rfl, funext hf, fun _ => rfl,
    fun i ti => revelation_interimPayment_eq M s i ti, fun _ hp => ⟨hp, rfl⟩⟩

/-- All-types interim-payment corollary of `exists_truthful_of_implementsInBayesNash`: when an
implementing Bayes–Nash equilibrium `s` additionally has integrable interim payment slices at every
type `ti : T i` (`M.HasIntegrableInterimPayment s`), the simulated direct mechanism `D` also
satisfies `D.HasIntegrableInterimPayment (fun _ => id)`. -/
theorem exists_truthful_hasIntegrableInterimPayment {M : BayesianMechanism ι T X Ω}
    [∀ i, IsProbabilityMeasure (M.prior i)] {s : ∀ i, T i → X i} {f : (∀ i, T i) → Ω}
    (hintU : M.toBayesianGame.HasIntegrableUtility s)
    (hintP : M.HasIntegrableInterimPayment s)
    (hs : M.toBayesianGame.IsBayesNash s)
    (hf : ∀ t, M.outcome (fun j => s j (t j)) = f t) :
    ∃ D : BayesianMechanism ι T T Ω,
      (∀ i, IsProbabilityMeasure (D.prior i)) ∧
      D.IsTruthful ∧
      D.toBayesianGame.HasIntegrableUtility (fun _ => id) ∧
      D.HasIntegrableInterimPayment (fun _ => id) ∧
      D.prior = M.prior ∧ D.valuation = M.valuation ∧ D.outcome = f ∧
      (∀ t, D.payment t = M.payment (fun j => s j (t j))) ∧
      ∀ i ti, D.interimPayment (fun _ => id) i ti = M.interimPayment s i (s i ti) :=
  ⟨M.revelation s, fun _ => inferInstance, revelation_isTruthful hs,
    revelation_hasIntegrableUtility hintU,
    (revelation_hasIntegrableInterimPayment_iff M s).2 hintP,
    rfl, rfl, funext hf, fun _ => rfl, fun i ti => revelation_interimPayment_eq M s i ti⟩

end Implementation

end BayesianMechanism

/-! ### Bayesian incentive compatibility (`IsBICOn`) directly on `Mechanism ι Ω` -/

namespace Mechanism

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

/-- Interim expected utility of agent `i` with true valuation `v` reporting `w` in direct
`Mechanism ι Ω` when other agents draw truthful valuations from `Measure.pi μ`. -/
noncomputable def interimUtility [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (i : ι) (v w : Ω → ℝ) : ℝ :=
  ∫ b, M.utility i v (Function.update b i w) ∂Measure.pi μ

theorem interimUtility_def [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (i : ι) (v w : Ω → ℝ) :
    M.interimUtility μ i v w = ∫ b, M.utility i v (Function.update b i w) ∂Measure.pi μ := by
  rfl

/-- Direct mechanism `M` has **integrable interim utilities** on valuation domains `V` under priors
`μ` if for every agent `i` and valuations `v, w ∈ V i`, the payoff integrand in
`M.interimUtility μ i v w` is Bochner-integrable against `Measure.pi μ`. -/
@[expose] def HasIntegrableUtilityOn [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (v w : Ω → ℝ), v ∈ V i → w ∈ V i →
    Integrable (fun b => M.utility i v (Function.update b i w)) (Measure.pi μ)

/-- Unrestricted interim-utility integrability (`V i = Set.univ`). -/
abbrev HasIntegrableUtility [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) : Prop :=
  M.HasIntegrableUtilityOn μ fun _ => Set.univ

/-- **Bayesian incentive compatibility on valuation domains `V`** (`IsBICOn`, [Nisan2007],
Definition 9.43): for every agent `i` and valuations `v, w ∈ V i`, reporting `v` maximizes interim
expected utility against independent priors `μ`. Each `μ i` is intended to carry
`IsProbabilityMeasure` with `HasIntegrableUtilityOn μ V`. -/
@[expose] def IsBICOn [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (v w : Ω → ℝ), v ∈ V i → w ∈ V i →
    M.interimUtility μ i v w ≤ M.interimUtility μ i v v

/-- Unrestricted Bayesian incentive compatibility (`V i = Set.univ`). -/
abbrev IsBIC [MeasurableSpace (Ω → ℝ)] (M : Mechanism ι Ω)
    (μ : ι → Measure (Ω → ℝ)) : Prop :=
  M.IsBICOn μ fun _ => Set.univ

end Mechanism

namespace IndirectMechanism

/-- Simulating `s` via `M.toMechanism s` preserves integrability of interim utilities on valuation
domains `V`. -/
theorem toMechanism_hasIntegrableUtilityOn {ι Ω : Type*} {X : ι → Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace (Ω → ℝ)]
    (M : IndirectMechanism ι X Ω) (μ : ι → Measure (Ω → ℝ))
    (V : ι → Set (Ω → ℝ)) {s : ∀ i, (Ω → ℝ) → X i}
    (hint : ({ toIncompleteInfoGame := M.toIncompleteInfoGame (fun _ (v : Ω → ℝ) => v)
               prior := μ } : BayesianGame ι (fun _ => Ω → ℝ) X).HasIntegrableUtilityOn V s) :
    (M.toMechanism s).HasIntegrableUtilityOn μ V := by
  intro i v w hv hw
  have h := hint i v hv (s i w)
  have hupd : ∀ b : ι → Ω → ℝ,
      (fun j => s j (Function.update b i w j)) =
        Function.update (fun j => s j (b j)) i (s i w) := fun b =>
    funext (Function.apply_update s b i w)
  simpa only [Mechanism.utility, toMechanism, toIncompleteInfoGame, hupd] using h

/-- General measure-theoretic integral-preservation step for valuation-domain direct simulation: if
`s : ∀ i, (Ω → ℝ) → X i` satisfies `IsBayesNashOn V` under priors `μ`, then the simulated direct
`M.toMechanism s : Mechanism ι Ω` satisfies `IsBICOn μ V`. Pair with
`[∀ i, IsProbabilityMeasure (μ i)]` and `toMechanism_hasIntegrableUtilityOn` for genuine
probability expectations. -/
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
