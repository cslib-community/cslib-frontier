/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Correlated
public import CslibFrontier.GameTheory.Strategic.Smooth
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equilibrium hierarchy, composition, and Bayesian extension of smooth games

Roughgarden's smoothness framework [Roughgarden2015] extends pure Nash price-of-anarchy bounds
along two orthogonal axes:

1. **Across the complete-information equilibrium hierarchy** ([Roughgarden2015], Theorem 3.2):
   every `(λ, μ)`-smooth cost-minimization game with `μ < 1` has expected social cost at most
   `λ / (1 - μ)` times any benchmark profile at pure Nash equilibria, mixed Nash equilibria,
   correlated equilibria, and coarse correlated equilibria (with additive slack carried through for
   `ε`-approximate correlated equilibria).
2. **Across algebraic composition and incomplete information** ([Roughgarden2012];
   [SyrgkanisTardos2013]): `(λ, μ)`-smoothness is closed under nonnegative scaling, sum, and finite
   simultaneous composition, and transfers to pure Bayes–Nash equilibria under arbitrary independent
   finite type distributions.

## Main definitions

* `Cslib.GameTheory.CostGame.smul`, `Cslib.GameTheory.CostGame.add`,
  `Cslib.GameTheory.CostGame.simultaneous`: nonnegative scaling, sum, and finite simultaneous
  composition of cost-minimization games.
* `Cslib.GameTheory.BayesianCostGame`: an incomplete-information cost game with private player
  types `θ i : Θ i`, type-dependent feasible strategy sets `allowed i (θ i)`, and ex-post costs
  `cost i (θ i) s`.
* `Cslib.GameTheory.BayesianCostGame.IsSmooth`: universal `(λ, μ)`-smoothness across type profiles.
* `Cslib.GameTheory.BayesianCostGame.IsPureBayesNash`: pure Bayes–Nash equilibrium under
  independent finite type distributions `p`.

## Main results

* `Cslib.GameTheory.CostGame.IsSmooth.expected_socialCost_le_of_isApproxCorrelatedEquilibrium`,
  `Cslib.GameTheory.CostGame.IsSmooth.expected_socialCost_le_of_isCorrelatedEquilibrium`,
  `Cslib.GameTheory.CostGame.IsSmooth.expected_socialCost_le_of_isMixedNash`: smooth
  price-of-anarchy bounds for approximate correlated, correlated, and mixed Nash equilibria
  ([Roughgarden2015], Theorem 3.2).
* `Cslib.GameTheory.CostGame.IsSmooth.smul`, `Cslib.GameTheory.CostGame.IsSmooth.add`,
  `Cslib.GameTheory.CostGame.IsSmooth.simultaneous`: closure of `(λ, μ)`-smoothness under
  nonnegative scaling, sum, and simultaneous composition.
* `Cslib.GameTheory.BayesianCostGame.IsSmooth.expected_socialCost_le_of_isPureBayesNash`:
  Roughgarden's incomplete-information extension theorem ([Roughgarden2012]) — under independent
  type priors, every pure Bayes–Nash equilibrium of a `(λ, μ)`-smooth Bayesian cost game with
  `μ < 1` has expected social cost at most `λ / (1 - μ)` times the expected social cost of any
  feasible type-contingent benchmark.
* `Cslib.GameTheory.BayesianCostGame.isSmooth_ofCostGame`: any complete-information `(λ, μ)`-smooth
  cost game equipped with private feasible strategy sets is `(λ, μ)`-smooth as a Bayesian game.

## References

* [Roughgarden2012]
* [Roughgarden2015]
* [SyrgkanisTardos2013]
-/

public section

namespace Cslib.GameTheory

namespace CostGame

open Finset Function

section Hierarchy

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] {G : CostGame ι S}

/-- **Price of anarchy for approximate correlated equilibria in smooth games**
([Roughgarden2015], Theorem 3.2 with additive slack): if `G` is `(λ, μ)`-smooth with `μ < 1` and
`σ` is an `ε`-approximate correlated equilibrium, then
`E_{s ∼ σ}[socialCost s] ≤ (λ * socialCost s' + ∑ i, ε i) / (1 - μ)` for every profile `s'`. -/
theorem IsSmooth.expected_socialCost_le_of_isApproxCorrelatedEquilibrium {lam μ : ℝ}
    (hG : G.IsSmooth lam μ) (hμ : μ < 1) {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hσ : G.IsApproxCorrelatedEquilibrium ε σ) (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * G.socialCost s)
      ≤ (lam * G.socialCost s' + ∑ i, ε i) / (1 - μ) :=
  hG.expected_socialCost_le_of_forall_le hμ (fun i a => hσ i fun _ => a) s'

/-- **Price of anarchy for correlated equilibria in smooth games** ([Roughgarden2015],
Theorem 3.2): if `G` is `(λ, μ)`-smooth with `μ < 1` and `σ` is a correlated equilibrium, then
`E_{s ∼ σ}[socialCost s] ≤ λ / (1 - μ) * socialCost s'` for every profile `s'`. -/
theorem IsSmooth.expected_socialCost_le_of_isCorrelatedEquilibrium {lam μ : ℝ}
    (hG : G.IsSmooth lam μ) (hμ : μ < 1) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hσ : G.IsCorrelatedEquilibrium σ) (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * G.socialCost s) ≤ lam / (1 - μ) * G.socialCost s' :=
  hG.expected_socialCost_le hμ hσ.isCoarseCorrelatedEquilibrium s'

/-- **Price of anarchy for mixed Nash equilibria in smooth games** ([Roughgarden2015],
Theorem 3.2): if `G` is `(λ, μ)`-smooth with `μ < 1` and `p` is a mixed Nash equilibrium, then the
expected social cost under the product distribution of `p` is at most `λ / (1 - μ)` times the
social cost of every pure profile `s'`. -/
theorem IsSmooth.expected_socialCost_le_of_isMixedNash [∀ i, Fintype (S i)] {lam μ : ℝ}
    (hG : G.IsSmooth lam μ) (hμ : μ < 1) {p : ∀ i, S i → ℝ} (hp : G.IsMixedNash p)
    (s' : ∀ i, S i) :
    ∑ s, productWeight p s * G.socialCost s ≤ lam / (1 - μ) * G.socialCost s' := by
  have h := hG.expected_socialCost_le_of_isCorrelatedEquilibrium hμ hp.isCorrelatedEquilibrium s'
  rwa [productDist_sum (fun i => (hp.1 i).nonneg) (fun i => (hp.1 i).sum_eq_one)] at h

/-- Monotonicity of `(λ, μ)`-smoothness in the parameters when social costs are nonnegative on the
corresponding profiles. -/
theorem IsSmooth.mono {lam lam' μ μ' : ℝ} (hG : G.IsSmooth lam μ) (hlam : lam ≤ lam')
    (hμ : μ ≤ μ') (hnonneg : ∀ s, 0 ≤ G.socialCost s) : G.IsSmooth lam' μ' := fun s s' =>
  (hG s s').trans (add_le_add (mul_le_mul_of_nonneg_right hlam (hnonneg s'))
    (mul_le_mul_of_nonneg_right hμ (hnonneg s)))

end Hierarchy

section Composition

variable {ι : Type*} [Fintype ι]

/-- Scalar multiple `c • G` of a cost-minimization game: each player's cost is scaled by `c`. -/
@[expose] def smul {S : ι → Type*} (c : ℝ) (G : CostGame ι S) : CostGame ι S where
  cost i s := c * G.cost i s

@[simp]
theorem socialCost_smul {S : ι → Type*} (c : ℝ) (G : CostGame ι S) (s : ∀ i, S i) :
    (G.smul c).socialCost s = c * G.socialCost s := by
  simp only [socialCost, smul, mul_sum]

/-- Nonnegative scaling preserves `(λ, μ)`-smoothness. -/
theorem IsSmooth.smul [DecidableEq ι] {S : ι → Type*} {G : CostGame ι S} {lam μ c : ℝ}
    (hG : G.IsSmooth lam μ) (hc : 0 ≤ c) : (G.smul c).IsSmooth lam μ := by
  intro s s'
  rw [socialCost_smul, socialCost_smul]
  simp only [CostGame.smul, ← mul_sum]
  calc c * ∑ i, G.cost i (update s i (s' i))
      ≤ c * (lam * G.socialCost s' + μ * G.socialCost s) := mul_le_mul_of_nonneg_left (hG s s') hc
    _ = lam * (c * G.socialCost s') + μ * (c * G.socialCost s) := by ring

/-- Pointwise sum of two cost-minimization games sharing players and strategy spaces. -/
@[expose] def add {S : ι → Type*} (G₁ G₂ : CostGame ι S) : CostGame ι S where
  cost i s := G₁.cost i s + G₂.cost i s

@[simp]
theorem socialCost_add {S : ι → Type*} (G₁ G₂ : CostGame ι S) (s : ∀ i, S i) :
    (G₁.add G₂).socialCost s = G₁.socialCost s + G₂.socialCost s := by
  simp only [socialCost, add, sum_add_distrib]

/-- The sum of two `(λ, μ)`-smooth games on the same strategy spaces is `(λ, μ)`-smooth. -/
theorem IsSmooth.add [DecidableEq ι] {S : ι → Type*} {G₁ G₂ : CostGame ι S} {lam μ : ℝ}
    (h₁ : G₁.IsSmooth lam μ) (h₂ : G₂.IsSmooth lam μ) : (G₁.add G₂).IsSmooth lam μ := by
  intro s s'
  rw [socialCost_add, socialCost_add]
  simp only [CostGame.add, sum_add_distrib]
  linarith [h₁ s s', h₂ s s']

/-- **Simultaneous composition** of a finite family of cost-minimization games `G k`
([SyrgkanisTardos2013]): each player `i` chooses a component strategy `s i k : S k i` in every game
`k : κ` simultaneously and pays the sum of its component costs
`∑ k, (G k).cost i (fun j => s j k)`. -/
@[expose] def simultaneous {κ : Type*} [Fintype κ] {S : κ → ι → Type*}
    (G : ∀ k, CostGame ι (S k)) : CostGame ι (fun i => ∀ k, S k i) where
  cost i s := ∑ k, (G k).cost i (fun j => s j k)

@[simp]
theorem socialCost_simultaneous {κ : Type*} [Fintype κ] {S : κ → ι → Type*}
    (G : ∀ k, CostGame ι (S k)) (s : ∀ i k, S k i) :
    (simultaneous G).socialCost s = ∑ k, (G k).socialCost (fun j => s j k) := by
  simp only [socialCost, simultaneous]
  exact sum_comm

/-- **Simultaneous composition preserves `(λ, μ)`-smoothness**: if every component game `G k` is
`(λ, μ)`-smooth, then their simultaneous composition `CostGame.simultaneous G` is `(λ, μ)`-smooth
with the same parameters `(λ, μ)`. -/
theorem IsSmooth.simultaneous [DecidableEq ι] {κ : Type*} [Fintype κ] {S : κ → ι → Type*}
    {G : ∀ k, CostGame ι (S k)} {lam μ : ℝ} (hG : ∀ k, (G k).IsSmooth lam μ) :
    (CostGame.simultaneous G).IsSmooth lam μ := by
  intro s s'
  rw [socialCost_simultaneous, socialCost_simultaneous]
  simp only [CostGame.simultaneous]
  rw [sum_comm]
  have hupd (k : κ) (i : ι) : (fun j => update s i (s' i) j k) =
      update (fun j => s j k) i (s' i k) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [update_self, update_self]
    · rw [update_of_ne hj, update_of_ne hj]
  calc ∑ k, ∑ i, (G k).cost i (fun j => update s i (s' i) j k)
      = ∑ k, ∑ i, (G k).cost i (update (fun j => s j k) i (s' i k)) := by simp_rw [hupd]
    _ ≤ ∑ k, (lam * (G k).socialCost (fun j => s' j k) +
          μ * (G k).socialCost (fun j => s j k)) := sum_le_sum fun k _ => hG k _ _
    _ = lam * ∑ k, (G k).socialCost (fun j => s' j k) +
          μ * ∑ k, (G k).socialCost (fun j => s j k) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]

end Composition

end CostGame

/-! ### Incomplete-information (Bayesian) smooth cost games -/

/-- An incomplete-information (**Bayesian**) cost-minimization game with private types and
type-restricted strategy sets ([Roughgarden2012]). Each player `i : ι` has a private type `t : Θ i`,
a feasible set `allowed i t ⊆ S i` of ambient actions available to type `t`, and ex-post cost
`cost i t s` at ambient action profile `s : ∀ j, S j`. -/
structure BayesianCostGame (ι : Type*) (Θ : ι → Type*) (S : ι → Type*) where
  /-- Ambient actions available to player `i` when its private type is `t`. -/
  allowed : ∀ i, Θ i → Set (S i)
  /-- Ex-post cost of player `i` with private type `t` at ambient action profile `s`. -/
  cost : ∀ i, Θ i → (∀ j, S j) → ℝ

namespace BayesianCostGame

open Finset Function

variable {ι : Type*} {Θ : ι → Type*} {S : ι → Type*}

/-- The complete-information ex-post cost game realized at type profile `θ`. -/
@[expose] def exPostGame (B : BayesianCostGame ι Θ S) (θ : ∀ i, Θ i) : CostGame ι S where
  cost i s := B.cost i (θ i) s

/-- Ex-post social cost `∑ i, B.cost i (θ i) s` at type profile `θ` and action profile `s`. -/
@[expose] def socialCost [Fintype ι] (B : BayesianCostGame ι Θ S) (θ : ∀ i, Θ i)
    (s : ∀ i, S i) : ℝ :=
  ∑ i, B.cost i (θ i) s

/-- An ambient action profile `s` is feasible for type profile `θ` if `s i ∈ B.allowed i (θ i)` for
every player `i`. -/
@[expose] def IsFeasible (B : BayesianCostGame ι Θ S) (θ : ∀ i, Θ i) (s : ∀ i, S i) : Prop :=
  ∀ i, s i ∈ B.allowed i (θ i)

/-- Universal **`(λ, μ)`-smoothness** of a Bayesian cost game across feasible type-profile pairs
([Roughgarden2012]): for all type profiles `θ`, `θ'` and respective feasible action profiles `s`,
`s'`, evaluating player `i`'s unilateral deviation to `s' i` under type `θ' i` sums to at most
`lam * socialCost θ' s' + μ * socialCost θ s`. -/
@[expose] def IsSmooth [DecidableEq ι] [Fintype ι] (B : BayesianCostGame ι Θ S)
    (lam μ : ℝ) : Prop :=
  ∀ (θ θ' : ∀ i, Θ i) (s s' : ∀ i, S i), B.IsFeasible θ s → B.IsFeasible θ' s' →
    ∑ i, B.cost i (θ' i) (update s i (s' i)) ≤ lam * B.socialCost θ' s' + μ * B.socialCost θ s

/-- Equipping a complete-information `CostGame` with private feasible action sets `allowed i t`
(such as uncertain source-sink terminal pairs in routing games). -/
@[expose] def ofCostGame (G : CostGame ι S) (allowed : ∀ i, Θ i → Set (S i)) :
    BayesianCostGame ι Θ S where
  allowed := allowed
  cost i _ s := G.cost i s

/-- Any complete-information `(λ, μ)`-smooth cost game remains `(λ, μ)`-smooth when players have
private feasible action sets `allowed i t`, because player costs do not vary directly with types. -/
theorem isSmooth_ofCostGame [DecidableEq ι] [Fintype ι] {G : CostGame ι S}
    (allowed : ∀ i, Θ i → Set (S i)) {lam μ : ℝ} (hG : G.IsSmooth lam μ) :
    (ofCostGame G allowed).IsSmooth lam μ :=
  fun _ _ s s' _ _ => hG s s'

section BayesNash

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Θ i)]

/-- Interim expected cost of player `i` with type `t` playing ambient action `a` when all other
players `j ≠ i` draw `θ j ∼ p j` independently and play `β j (θ j)`. Because coordinate `i` of
`update (fun j => β j (θ j)) i a` does not depend on `θ i`, summing over full profiles `θ` weighted
by `productWeight p θ` avoids dividing by `p i t`. -/
@[expose] def interimCost (B : BayesianCostGame ι Θ S) (p : ∀ i, Θ i → ℝ)
    (β : ∀ i, Θ i → S i) (i : ι) (t : Θ i) (a : S i) : ℝ :=
  ∑ θ, productWeight p θ * B.cost i t (update (fun j => β j (θ j)) i a)

/-- A strategy profile `β : ∀ i, Θ i → S i` is a **pure Bayes–Nash equilibrium** of `B` under
independent type distributions `p` if every type is assigned a feasible action and no type can
strictly decrease its interim expected cost by deviating to another feasible action. -/
@[expose] def IsPureBayesNash (B : BayesianCostGame ι Θ S) (p : ∀ i, Θ i → ℝ)
    (β : ∀ i, Θ i → S i) : Prop :=
  (∀ i t, β i t ∈ B.allowed i t) ∧
    ∀ i t, ∀ a ∈ B.allowed i t, B.interimCost p β i t (β i t) ≤ B.interimCost p β i t a

/-- Averaging player `i`'s equilibrium interim cost over its own type `t ∼ p i` recovers its ex-post
expected cost under the product prior `productWeight p`. -/
theorem sum_mul_interimCost_eq (B : BayesianCostGame ι Θ S) (p : ∀ i, Θ i → ℝ)
    (β : ∀ i, Θ i → S i) {i : ι} (hp : ∑ t, p i t = 1) :
    ∑ t, p i t * B.interimCost p β i t (β i t) =
      ∑ θ, productWeight p θ * B.cost i (θ i) (fun j => β j (θ j)) := by
  have hupd (θ : ∀ j, Θ j) (t : Θ i) :
      B.cost i t (update (fun j => β j (θ j)) i (β i t)) =
        B.cost i (update θ i t i) (fun j => β j (update θ i t j)) := by
    rw [update_self]
    congr 1
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [update_self, update_self]
    · rw [update_of_ne hj, update_of_ne hj]
  simp only [interimCost, hupd]
  exact sum_mul_sum_productWeight_update p hp fun θ => B.cost i (θ i) (fun j => β j (θ j))

/-- **Roughgarden's incomplete-information smoothness extension theorem** ([Roughgarden2012]): if
`B` is `(λ, μ)`-smooth with `μ < 1`, `p` is an independent profile of probability distributions over
types, and `β` is a pure Bayes–Nash equilibrium, then for every feasible type-contingent benchmark
`s' : (∀ i, Θ i) → ∀ i, S i`,
`E_{θ ∼ p}[socialCost θ (β ∘ θ)] ≤ λ / (1 - μ) * E_{θ' ∼ p}[socialCost θ' (s' θ')]`. -/
theorem IsSmooth.expected_socialCost_le_of_isPureBayesNash {B : BayesianCostGame ι Θ S}
    {lam μ : ℝ} (hB : B.IsSmooth lam μ) (hμ : μ < 1) {p : ∀ i, Θ i → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) {β : ∀ i, Θ i → S i} (hβ : B.IsPureBayesNash p β)
    (s' : (∀ i, Θ i) → ∀ i, S i) (hs' : ∀ θ', B.IsFeasible θ' (s' θ')) :
    ∑ θ, productWeight p θ * B.socialCost θ (fun j => β j (θ j))
      ≤ lam / (1 - μ) * ∑ θ', productWeight p θ' * B.socialCost θ' (s' θ') := by
  have hp0 : ∀ i t, 0 ≤ p i t := fun i => (hp i).nonneg
  have hp1 : ∀ i, ∑ t, p i t = 1 := fun i => (hp i).sum_eq_one
  have htot : ∑ θ, productWeight p θ = 1 := sum_productWeight hp1
  have h1 : ∑ θ, productWeight p θ * B.socialCost θ (fun j => β j (θ j))
      = ∑ i, ∑ θ', productWeight p θ' * B.interimCost p β i (θ' i) (β i (θ' i)) := by
    simp only [socialCost, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_productWeight_mul_apply (fun j _ => hp1 j)
      (fun t => B.interimCost p β i t (β i t)), B.sum_mul_interimCost_eq p β (hp1 i)]
  have h2 : ∑ i, ∑ θ', productWeight p θ' * B.interimCost p β i (θ' i) (β i (θ' i))
      ≤ ∑ i, ∑ θ', productWeight p θ' * B.interimCost p β i (θ' i) (s' θ' i) :=
    sum_le_sum fun i _ => sum_le_sum fun θ' _ =>
      mul_le_mul_of_nonneg_left (hβ.2 i (θ' i) (s' θ' i) (hs' θ' i)) (productWeight_nonneg hp0 θ')
  have h3 : ∑ i, ∑ θ', productWeight p θ' * B.interimCost p β i (θ' i) (s' θ' i)
      = ∑ θ', productWeight p θ' * ∑ θ, productWeight p θ *
          ∑ i, B.cost i (θ' i) (update (fun j => β j (θ j)) i (s' θ' i)) := by
    rw [sum_comm]
    refine sum_congr rfl fun θ' _ => ?_
    simp only [interimCost, mul_sum]
    exact sum_comm
  have h4 : ∑ θ', productWeight p θ' * ∑ θ, productWeight p θ *
        ∑ i, B.cost i (θ' i) (update (fun j => β j (θ j)) i (s' θ' i))
      ≤ ∑ θ', productWeight p θ' * ∑ θ, productWeight p θ *
          (lam * B.socialCost θ' (s' θ') + μ * B.socialCost θ (fun j => β j (θ j))) :=
    sum_le_sum fun θ' _ => mul_le_mul_of_nonneg_left
      (sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left
        (hB θ θ' (fun j => β j (θ j)) (s' θ') (fun i => hβ.1 i (θ i)) (hs' θ'))
        (productWeight_nonneg hp0 θ))
      (productWeight_nonneg hp0 θ')
  have h5 : ∑ θ', productWeight p θ' * ∑ θ, productWeight p θ *
        (lam * B.socialCost θ' (s' θ') + μ * B.socialCost θ (fun j => β j (θ j)))
      = lam * (∑ θ', productWeight p θ' * B.socialCost θ' (s' θ')) +
          μ * (∑ θ, productWeight p θ * B.socialCost θ (fun j => β j (θ j))) := by
    have hring1 (w a b : ℝ) : w * (lam * a + μ * b) = lam * a * w + μ * (w * b) := by ring
    have hring2 (w a b : ℝ) : w * (lam * a + b) = lam * (w * a) + b * w := by ring
    have inner (θ' : ∀ i, Θ i) : ∑ θ, productWeight p θ *
          (lam * B.socialCost θ' (s' θ') + μ * B.socialCost θ (fun j => β j (θ j)))
        = lam * B.socialCost θ' (s' θ') +
            μ * ∑ θ, productWeight p θ * B.socialCost θ (fun j => β j (θ j)) := by
      simp only [hring1, sum_add_distrib, ← mul_sum, htot, mul_one]
    simp_rw [inner]
    simp only [hring2, sum_add_distrib, ← mul_sum, htot, mul_one]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- **Incomplete-information robust price of anarchy for smooth complete-information games**
([Roughgarden2012]): in any complete-information `(λ, μ)`-smooth cost game `G` with `μ < 1`,
restricting players to private feasible strategy sets `allowed i t` drawn from independent priors
`p` preserves the price-of-anarchy bound `λ / (1 - μ)` across all pure Bayes–Nash equilibria. -/
theorem expected_socialCost_ofCostGame_le_of_isPureBayesNash {G : CostGame ι S}
    (allowed : ∀ i, Θ i → Set (S i)) {lam μ : ℝ} (hG : G.IsSmooth lam μ) (hμ : μ < 1)
    {p : ∀ i, Θ i → ℝ} (hp : ∀ i, IsMixedStrategy (p i)) {β : ∀ i, Θ i → S i}
    (hβ : (ofCostGame G allowed).IsPureBayesNash p β)
    (s' : (∀ i, Θ i) → ∀ i, S i) (hs' : ∀ θ' i, s' θ' i ∈ allowed i (θ' i)) :
    ∑ θ, productWeight p θ * G.socialCost (fun j => β j (θ j))
      ≤ lam / (1 - μ) * ∑ θ', productWeight p θ' * G.socialCost (s' θ') :=
  (isSmooth_ofCostGame allowed hG).expected_socialCost_le_of_isPureBayesNash hμ hp hβ s' hs'

end BayesNash

end BayesianCostGame

end Cslib.GameTheory
