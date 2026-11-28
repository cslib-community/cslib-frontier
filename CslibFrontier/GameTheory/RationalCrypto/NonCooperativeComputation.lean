/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.GameTheory.MixedStrategy
public import CslibFrontier.GameTheory.Strategic.Correlated
public import CslibFrontier.GameTheory.Strategic.Payoff
public import CslibFrontier.Probability.Minimax.Value
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Correlated Equilibrium Min-Max Bounds and Non-Cooperatively Computable Functions

This module formalizes two results from Dodis and Rabin's chapter *Cryptography and Game Theory*
([DodisRabin2007], Chapter 8 of Nisan–Roughgarden–Tardos–Vazirani 2007):

1. **Correlated equilibrium min-max lower bound** ([DodisRabin2007], Section 8.4.2, Claim 8.4,
   p. 195): in any finite strategic payoff game `G : PayoffGame ι S` with nonempty action sets,
   player `i`'s correlated min-max value
   `v_i = min_{z_{-i} ∈ Δ(S_{-i})} max_{a ∈ S_i} u_i(a, z_{-i})` (`PayoffGame.correlatedMinMax`)
   is attained by a punishing correlated profile (`PayoffGame.exists_correlatedMinMax_punisher`),
   equals the zero-sum minimax value of the opponent-vs-player payoff matrix
   (`PayoffGame.isMinimaxValue_correlatedMinMax`), and lower-bounds player `i`'s conditional
   expected payoff `E[u_i(s) | s_i = a]` at every action `a` in the support of any correlated
   equilibrium `σ` (`PayoffGame.correlatedMinMax_le_condPayoff`).

2. **Non-cooperatively computable (`NCC`) and `k-NCC` functions** ([DodisRabin2007], Section 8.5.1,
   Definition 8.5, Theorem 8.6, Footnote 8, and "Collusions", pp. 197–199):
   - Parties hold private inputs `t : ∀ i, T i` drawn from a full-support prior `D` and wish to
     evaluate a single-output function `f : (∀ i, T i) → O` via a canonical mediator that evaluates
     `f` on the reported inputs and broadcasts an error message (`none`, written `⊥` in the source)
     if any party refuses to participate.
   - Utilities `u : ι → (ι → Bool) → ℝ` depend only on the correctness vector `c : ι → Bool` and
     satisfy **correctness** and **exclusivity** (`CorrectnessExclusivity`), and for the full
     characterization also **high-correctness priority** (`HighCorrectnessPriority`), where even
     the smallest input probability `ε = min_t D t` makes any correctness loss strictly worse than
     any exclusivity gain (`highCorrectnessPriority_iff_minProb`).
   - `IsNCC` (`Definition 8.5`) states that truthful reporting and obedience (`honestProfile`) form
     a pure Nash equilibrium of the mediated game `mediatedGame` (equivalently, the canonical
     mediated strategy is a correlated equilibrium of the function evaluation game); by linearity
     of expectation this rules out mixed/randomized unilateral deviations as well.
   - `IsKNCC` extends `IsNCC` to coalitions `C` of size at most `k` that pool their inputs and
     jointly choose reports and output interpretations (`CoalitionDev`), requiring Pareto
     `k`-resilience (no coalition can weakly improve all its members and strictly improve some
     member, matching `CostGame.IsStrongNash`); `k = 1` recovers `IsNCC` (`isKNCC_one_iff_isNCC`).
   - **Footnote 8** (`IsDominated.isReversible`, and `IsKDominated.isKReversible` for coalitions):
     every dominated non-constant function (in particular under `EveryInputMatters`) is reversible.
   - **Theorem 8.6** (`isNCC_iff_not_dominated_and_not_reversible`, p. 199) and its `k`-coalition
     characterization (`isKNCC_iff_not_kDominated_and_not_kReversible`, after "Collusions",
     p. 199): under correctness, exclusivity, high-correctness priority (which together with
     correctness automatically implies full support `∀ t, 0 < D t`, `HighCorrectnessPriority.pos`),
     `2 ≤ |ι|` (resp. `k < |ι|`), and non-constancy of `f` (strictly weaker than the source's
     p. 197 assumption `EveryInputMatters`), `f` is (`k`-)`NCC` iff it is neither (`k`-)dominated
     nor (`k`-)reversible, uniformly in the honest error-fallback strategy `fallback`.
   - **Boolean function witnesses:** matching the explicit examples in [DodisRabin2007], p. 199,
     `Cslib.parity n` (`n ≥ 2`) is reversible and not `NCC` (`not_isNCC_parity`), while odd-player
     majority `Cslib.majority (2 * m + 1)` (`m ≥ 1`) is `NCC` (`isNCC_majority`); as concrete
     Boolean corollaries of p. 198's domination rule, `Cslib.threshold n 1` (`OR`, `n ≥ 2`) and
     `Cslib.threshold n n` (`AND`, `n ≥ 2`) are dominated and not `NCC` (`not_isNCC_or`,
     `not_isNCC_and`); extending to coalitions, `Cslib.majority (2 * m + 1)` (`m ≥ 1`) is `k-NCC`
     if and only if `k ≤ m` (`isKNCC_majority_iff`).

## Main definitions

* `Cslib.GameTheory.PayoffGame.insertAction`, `Cslib.GameTheory.PayoffGame.payoffAgainst`,
  `Cslib.GameTheory.PayoffGame.bestResponsePayoff`, `Cslib.GameTheory.PayoffGame.correlatedMinMax`,
  `Cslib.GameTheory.PayoffGame.marginalWeight`, `Cslib.GameTheory.PayoffGame.condPayoff`:
  correlated min-max value and conditional equilibrium payoff.
* `Cslib.GameTheory.RationalCrypto.CorrectnessExclusivity`,
  `Cslib.GameTheory.RationalCrypto.HighCorrectnessPriority`: utility preference axioms.
* `Cslib.GameTheory.RationalCrypto.UnilateralDev`, `Cslib.GameTheory.RationalCrypto.honestProfile`,
  `Cslib.GameTheory.RationalCrypto.mediatedGame`, `Cslib.GameTheory.RationalCrypto.IsNCC`:
  mediated function evaluation game and non-cooperative computability (Definition 8.5).
* `Cslib.GameTheory.RationalCrypto.EveryInputMatters`,
  `Cslib.GameTheory.RationalCrypto.IsDominated`, `Cslib.GameTheory.RationalCrypto.IsReversible`:
  non-degeneracy, domination, and reversibility predicates.
* `Cslib.GameTheory.RationalCrypto.CoalitionDev`, `Cslib.GameTheory.RationalCrypto.IsKNCC`,
  `Cslib.GameTheory.RationalCrypto.IsKDominated`, `Cslib.GameTheory.RationalCrypto.IsKReversible`:
  coalitional `k-NCC` generalization.

## Main results

* `Cslib.GameTheory.PayoffGame.isMinimaxValue_correlatedMinMax`,
  `Cslib.GameTheory.PayoffGame.correlatedMinMax_le_bestResponsePayoff`,
  `Cslib.GameTheory.PayoffGame.exists_correlatedMinMax_punisher`: characterization and attainment
  of the correlated min-max value via von Neumann's minimax theorem.
* `Cslib.GameTheory.PayoffGame.correlatedMinMax_le_condPayoff`: **Claim 8.4** ([DodisRabin2007],
  p. 195) — in any correlated equilibrium, every action in a player's marginal support yields
  conditional expected payoff at least its correlated min-max value.
* `Cslib.GameTheory.RationalCrypto.IsDominated.isReversible`,
  `Cslib.GameTheory.RationalCrypto.IsKDominated.isKReversible`: **Footnote 8** ([DodisRabin2007],
  p. 199) and its `k`-coalition form.
* `Cslib.GameTheory.RationalCrypto.isNCC_iff_not_dominated_and_not_reversible`: **Theorem 8.6**
  ([DodisRabin2007], p. 199).
* `Cslib.GameTheory.RationalCrypto.isKNCC_iff_not_kDominated_and_not_kReversible`,
  `Cslib.GameTheory.RationalCrypto.isKNCC_one_iff_isNCC`: coalitional `k-NCC` characterization
  and exact `k = 1` correspondence.
* `Cslib.GameTheory.RationalCrypto.not_isNCC_parity`,
  `Cslib.GameTheory.RationalCrypto.not_isNCC_or`,
  `Cslib.GameTheory.RationalCrypto.not_isNCC_and`,
  `Cslib.GameTheory.RationalCrypto.isNCC_majority`,
  `Cslib.GameTheory.RationalCrypto.isKNCC_majority_iff`: canonical Boolean function witnesses.

## References

* [Y. Dodis and T. Rabin, *Cryptography and Game Theory*][DodisRabin2007], Section 8.4.2
  (Claim 8.4, p. 195) and Section 8.5.1 (Definition 8.5, Theorem 8.6, Footnote 8, and
  "Collusions", pp. 197–199)
-/

public section

namespace Cslib.GameTheory.PayoffGame

open Finset Function

section CorrelatedMinMax

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι]

/-- Insert player `i`'s action `a` into a joint strategy profile `s` of the remaining players
`P_{-i}`. -/
@[expose] def insertAction (i : ι) (a : S i)
    (s : ∀ j : { j : ι // j ≠ i }, S j.val) : ∀ j, S j :=
  fun j => if h : j = i then h ▸ a else s ⟨j, h⟩

@[simp]
theorem insertAction_self (i : ι) (a : S i) (s : ∀ j : { j : ι // j ≠ i }, S j.val) :
    insertAction i a s i = a := by
  simp [insertAction]

theorem insertAction_of_ne (i : ι) (a : S i) (s : ∀ j : { j : ι // j ≠ i }, S j.val)
    {j : ι} (h : j ≠ i) :
    insertAction i a s j = s ⟨j, h⟩ := by
  simp [insertAction, h]

@[simp]
theorem update_insertAction (i : ι) (a b : S i) (s : ∀ j : { j : ι // j ≠ i }, S j.val) :
    update (insertAction i a s) i b = insertAction i b s := by
  funext j
  by_cases h : j = i
  · subst h; simp [insertAction]
  · simp [insertAction, h]

@[simp]
theorem insertAction_proj (i : ι) (s : ∀ j, S j) :
    insertAction i (s i) (fun j : { j : ι // j ≠ i } => s j.val) = s := by
  funext j
  by_cases h : j = i
  · subst h; simp [insertAction]
  · simp [insertAction, h]

variable [Fintype ι] [∀ j, Fintype (S j)]

private theorem sum_insertAction_eq_sum_ite (i : ι) [DecidableEq (S i)] (a : S i)
    (f : (∀ j, S j) → ℝ) :
    ∑ s : ∀ j : { j : ι // j ≠ i }, S j.val, f (insertAction i a s) =
      ∑ s : ∀ j, S j, if s i = a then f s else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (insertAction i a) (fun s j => s j.val) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro s _
    simp
  · intro _ _
    exact Finset.mem_univ _
  · intro s _
    funext j
    exact insertAction_of_ne i a s j.property
  · intro s hs
    have hsi : s i = a := (Finset.mem_filter.mp hs).2
    rw [← hsi]
    exact insertAction_proj i s

/-- Player `i`'s expected payoff when playing pure action `a` against a correlated strategy
`z ∈ Δ(S_{-i})` of the remaining players ([DodisRabin2007], Section 8.4.2, p. 195). -/
noncomputable def payoffAgainst (G : PayoffGame ι S) (i : ι) (a : S i)
    (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) : ℝ :=
  ∑ s, z.weights s * G.payoff i (insertAction i a s)

theorem payoffAgainst_eq (G : PayoffGame ι S) (i : ι) (a : S i)
    (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) :
    G.payoffAgainst i a z = ∑ s, z.weights s * G.payoff i (insertAction i a s) := by
  rfl

/-- Player `i`'s best-response payoff `max_{a ∈ S_i} u_i(a, z_{-i})` against a correlated strategy
`z ∈ Δ(S_{-i})` of the remaining players. -/
noncomputable def bestResponsePayoff (G : PayoffGame ι S) (i : ι) [Nonempty (S i)]
    (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => G.payoffAgainst i a z

theorem payoffAgainst_le_bestResponsePayoff (G : PayoffGame ι S) (i : ι) [Nonempty (S i)]
    (a : S i) (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) :
    G.payoffAgainst i a z ≤ G.bestResponsePayoff i z := by
  exact Finset.le_sup' (fun b => G.payoffAgainst i b z) (Finset.mem_univ a)

theorem bestResponsePayoff_le_iff (G : PayoffGame ι S) (i : ι) [Nonempty (S i)]
    (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) {c : ℝ} :
    G.bestResponsePayoff i z ≤ c ↔ ∀ a : S i, G.payoffAgainst i a z ≤ c := by
  simp only [bestResponsePayoff, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

/-- Player `i`'s **correlated min-max value** `v_i = inf_{z_{-i} ∈ Δ(S_{-i})} max_{a ∈ S_i}
u_i(a, z_{-i})` ([DodisRabin2007], Section 8.4.2, p. 195), representing the worst expected payoff
that the remaining players `P_{-i}` can jointly enforce on `P_i`. When all action sets are
nonempty, this infimum is attained (`exists_correlatedMinMax_punisher`) and equals the zero-sum
minimax value (`isMinimaxValue_correlatedMinMax`). -/
noncomputable def correlatedMinMax (G : PayoffGame ι S) (i : ι) [Nonempty (S i)] : ℝ :=
  sInf (Set.range (G.bestResponsePayoff i))

/-- Marginal probability mass placed by profile distribution `σ` on player `i` receiving
recommendation `a`. -/
noncomputable def marginalWeight (σ : Convexity.StdSimplex ℝ (∀ j, S j))
    (i : ι) [DecidableEq (S i)] (a : S i) : ℝ :=
  ∑ s : ∀ j, S j, if s i = a then σ.weights s else 0

theorem marginalWeight_eq (σ : Convexity.StdSimplex ℝ (∀ j, S j))
    (i : ι) [DecidableEq (S i)] (a : S i) :
    marginalWeight σ i a = ∑ s : ∀ j, S j, if s i = a then σ.weights s else 0 := by
  rfl

/-- Conditional expected payoff `E_{s ∼ σ}[u_i(s) | s_i = a]` of player `i` given recommendation
`a` ([DodisRabin2007], Section 8.4.2, Claim 8.4, p. 195). Meaningful when
`0 < marginalWeight σ i a`. -/
noncomputable def condPayoff (G : PayoffGame ι S) (σ : Convexity.StdSimplex ℝ (∀ j, S j))
    (i : ι) [DecidableEq (S i)] (a : S i) : ℝ :=
  (∑ s : ∀ j, S j, if s i = a then σ.weights s * G.payoff i s else 0) / marginalWeight σ i a

theorem condPayoff_eq (G : PayoffGame ι S) (σ : Convexity.StdSimplex ℝ (∀ j, S j))
    (i : ι) [DecidableEq (S i)] (a : S i) :
    G.condPayoff σ i a =
      (∑ s : ∀ j, S j, if s i = a then σ.weights s * G.payoff i s else 0) /
        marginalWeight σ i a := by
  rfl

private theorem isLeast_range_bestResponsePayoff [∀ j, Nonempty (S j)]
    (G : PayoffGame ι S) (i : ι) :
    ∃ v, Cslib.Probability.IsMinimaxValue (fun s a => G.payoff i (insertAction i a s)) v ∧
      IsLeast (Set.range (G.bestResponsePayoff i)) v := by
  let M : (∀ j : { j : ι // j ≠ i }, S j.val) → S i → ℝ :=
    fun s a => G.payoff i (insertAction i a s)
  obtain ⟨v, hv⟩ := Cslib.Probability.exists_isMinimaxValue M
  refine ⟨v, hv, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hv.1
    have hle : G.bestResponsePayoff i z ≤ v := (G.bestResponsePayoff_le_iff i z).2 hz
    obtain ⟨a, ha⟩ := hv.exists_le z.weights_nonneg z.total_of_fintype
    have hge : v ≤ G.bestResponsePayoff i z :=
      ha.trans (G.payoffAgainst_le_bestResponsePayoff i a z)
    exact ⟨z, le_antisymm hle hge⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hv.exists_le z.weights_nonneg z.total_of_fintype
    exact ha.trans (G.payoffAgainst_le_bestResponsePayoff i a z)

/-- `G.correlatedMinMax i` is the unique von Neumann minimax value of the two-player zero-sum game
in which `P_{-i}` chooses `s_{-i}` to minimize `u_i(a, s_{-i})` and `P_i` chooses `a` to maximize
it. -/
theorem isMinimaxValue_correlatedMinMax [∀ j, Nonempty (S j)]
    (G : PayoffGame ι S) (i : ι) :
    Cslib.Probability.IsMinimaxValue (fun s a => G.payoff i (insertAction i a s))
      (G.correlatedMinMax i) := by
  obtain ⟨v, hv, hleast⟩ := G.isLeast_range_bestResponsePayoff i
  rwa [correlatedMinMax, hleast.csInf_eq]

/-- Every correlated strategy `z` of the remaining players allows player `i` a best-response
expected payoff of at least `G.correlatedMinMax i`. -/
theorem correlatedMinMax_le_bestResponsePayoff [∀ j, Nonempty (S j)]
    (G : PayoffGame ι S) (i : ι)
    (z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val)) :
    G.correlatedMinMax i ≤ G.bestResponsePayoff i z := by
  obtain ⟨v, _, hleast⟩ := G.isLeast_range_bestResponsePayoff i
  rw [correlatedMinMax, hleast.csInf_eq]
  exact hleast.2 ⟨z, rfl⟩

/-- The correlated min-max value is attained: the remaining players `P_{-i}` possess a correlated
punishment strategy `z ∈ Δ(S_{-i})` holding player `i`'s best-response payoff down to
`G.correlatedMinMax i` ([DodisRabin2007], Section 8.4.2, p. 195). -/
theorem exists_correlatedMinMax_punisher [∀ j, Nonempty (S j)]
    (G : PayoffGame ι S) (i : ι) :
    ∃ z : Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val),
      G.bestResponsePayoff i z = G.correlatedMinMax i := by
  obtain ⟨v, _, hleast⟩ := G.isLeast_range_bestResponsePayoff i
  rw [correlatedMinMax, hleast.csInf_eq]
  exact hleast.1

/-- Conditional distribution of `s_{-i}` given `s i = a` under `σ`, for an action `a` with positive
marginal weight. -/
private noncomputable def condOthersDist (σ : Convexity.StdSimplex ℝ (∀ j, S j))
    (i : ι) [DecidableEq (S i)] (a : S i) (ha : 0 < marginalWeight σ i a) :
    Convexity.StdSimplex ℝ (∀ j : { j : ι // j ≠ i }, S j.val) where
  weights := Finsupp.equivFunOnFinite.symm fun s =>
    σ.weights (insertAction i a s) / marginalWeight σ i a
  nonneg s := by
    change 0 ≤ σ.weights (insertAction i a s) / marginalWeight σ i a
    exact div_nonneg (σ.weights_nonneg (insertAction i a s)) ha.le
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change (∑ s : ∀ j : { j : ι // j ≠ i }, S j.val,
      σ.weights (insertAction i a s) / marginalWeight σ i a) = 1
    rw [← Finset.sum_div, sum_insertAction_eq_sum_ite i a (fun s => σ.weights s),
      ← marginalWeight_eq, div_self ha.ne']

private theorem payoffAgainst_condOthersDist (G : PayoffGame ι S)
    (σ : Convexity.StdSimplex ℝ (∀ j, S j)) (i : ι) [DecidableEq (S i)] (a b : S i)
    (ha : 0 < marginalWeight σ i a) :
    G.payoffAgainst i b (condOthersDist σ i a ha) =
      (∑ s : ∀ j, S j, if s i = a then σ.weights s * G.payoff i (update s i b) else 0) /
        marginalWeight σ i a := by
  rw [payoffAgainst_eq]
  have h1 : ∀ s : ∀ j : { j : ι // j ≠ i }, S j.val,
      (condOthersDist σ i a ha).weights s * G.payoff i (insertAction i b s) =
        (σ.weights (insertAction i a s) *
          G.payoff i (update (insertAction i a s) i b)) / marginalWeight σ i a := fun s => by
    change (σ.weights (insertAction i a s) / marginalWeight σ i a) *
        G.payoff i (insertAction i b s) = _
    rw [update_insertAction]
    ring
  simp_rw [h1]
  rw [← Finset.sum_div,
    sum_insertAction_eq_sum_ite i a (fun s => σ.weights s * G.payoff i (update s i b))]

/-- **Claim 8.4** ([DodisRabin2007], Section 8.4.2, p. 195): in any correlated equilibrium `σ` of a
finite strategic payoff game `G`, for every player `i` and every action `a` in the support of `σ`'s
`i`-th marginal (`0 < marginalWeight σ i a`), player `i`'s conditional expected payoff given
recommendation `a` is at least its correlated min-max value `G.correlatedMinMax i`. -/
theorem correlatedMinMax_le_condPayoff [∀ j, Nonempty (S j)]
    {G : PayoffGame ι S} {σ : Convexity.StdSimplex ℝ (∀ j, S j)}
    (hce : G.toCostGame.IsCorrelatedEquilibrium σ) (i : ι) [DecidableEq (S i)] {a : S i}
    (ha : 0 < marginalWeight σ i a) :
    G.correlatedMinMax i ≤ G.condPayoff σ i a := by
  let z := condOthersDist σ i a ha
  refine (G.correlatedMinMax_le_bestResponsePayoff i z).trans ?_
  rw [G.bestResponsePayoff_le_iff i z]
  intro b
  rw [payoffAgainst_condOthersDist, condPayoff_eq]
  refine div_le_div_of_nonneg_right ?_ ha.le
  have hcond :
      (∑ s : ∀ j, S j, σ.weights s * if s i = a then G.toCostGame.cost i s else 0) ≤
        ∑ s : ∀ j, S j,
          σ.weights s * if s i = a then G.toCostGame.cost i (update s i b) else 0 := by
    classical
    have hc := (CostGame.isCorrelatedEquilibrium_iff.mp hce) i a b
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at hc
    convert hc using 4
  have hL : (∑ s : ∀ j, S j, σ.weights s * if s i = a then G.toCostGame.cost i s else 0) =
      -(∑ s : ∀ j, S j, if s i = a then σ.weights s * G.payoff i s else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp [PayoffGame.toCostGame_cost]
  have hR : (∑ s : ∀ j, S j,
        σ.weights s * if s i = a then G.toCostGame.cost i (update s i b) else 0) =
      -(∑ s : ∀ j, S j, if s i = a then σ.weights s * G.payoff i (update s i b) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp [PayoffGame.toCostGame_cost]
  rw [hL, hR] at hcond
  linarith

end CorrelatedMinMax

end Cslib.GameTheory.PayoffGame

/-! ### Non-Cooperatively Computable (`NCC`) and `k-NCC` Functions -/

namespace Cslib.GameTheory.RationalCrypto

open Cslib.GameTheory Finset Function

section NCCDefinitions

variable {ι : Type*} {T : ι → Type*} {O : Type*}

/-- **Correctness and exclusivity** utility preferences for the function evaluation game
([DodisRabin2007], Section 8.5.1, p. 198):
* `correctness`: learning the true output (`c i = true`) strictly beats failing (`c' i = false`);
* `exclusivity`: holding player `i`'s own correctness fixed (`c i = c' i`), having strictly fewer
  other players succeed (`∀ j ≠ i, c j → c' j` and `∃ j ≠ i, ¬ c j ∧ c' j`) is strictly preferred.
-/
structure CorrectnessExclusivity (u : ι → (ι → Bool) → ℝ) : Prop where
  /-- Correctness preference: `c i = true` strictly beats `c' i = false`. -/
  correctness : ∀ i (c c' : ι → Bool), c i = true → c' i = false → u i c' < u i c
  /-- Exclusivity preference: given the same own correctness, fewer other correct players strictly
  increases utility. -/
  exclusivity : ∀ i (c c' : ι → Bool), c i = c' i →
    (∀ j, j ≠ i → c j = true → c' j = true) →
    (∃ j, j ≠ i ∧ c j = false ∧ c' j = true) →
    u i c' < u i c

/-- **High-correctness priority** ([DodisRabin2007], Section 8.5.1, p. 199): for every input
profile `t` (in particular at the minimum probability `ε = min_t D t`, see
`highCorrectnessPriority_iff_minProb`), any chance `D t` of losing correctness outweighs any
exclusivity gain on the complementary event `1 - D t`. -/
@[expose] def HighCorrectnessPriority (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ) : Prop :=
  ∀ i (c c' c'' : ι → Bool) (t : ∀ j, T j),
    c i = true → c' i = true → c'' i = false →
    (1 - D t) * u i c' + D t * u i c'' < u i c

/-- Under `CorrectnessExclusivity` on a nonempty player set, `HighCorrectnessPriority u D` implies
that the prior `D` has full support (`∀ t, 0 < D t`). -/
theorem HighCorrectnessPriority.pos [Nonempty ι] {u : ι → (ι → Bool) → ℝ}
    {D : (∀ i, T i) → ℝ} (hprio : HighCorrectnessPriority u D)
    (hu : CorrectnessExclusivity u) (t : ∀ j, T j) : 0 < D t := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hlt := hu.correctness i (fun _ => true) (fun _ => false) rfl rfl
  have hp := hprio i (fun _ => true) (fun _ => true) (fun _ => false) t rfl rfl rfl
  nlinarith

/-- Equivalence of `HighCorrectnessPriority` with the explicit minimum-probability inequality
`u_i(c) > (1 - ε) u_i(c') + ε u_i(c'')` where `ε = min_t D t` ([DodisRabin2007], p. 199). -/
theorem highCorrectnessPriority_iff_minProb [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)]
    [Nonempty (∀ j, T j)] {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ}
    (hu : CorrectnessExclusivity u) :
    HighCorrectnessPriority u D ↔
      let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty D
      ∀ i (c c' c'' : ι → Bool), c i = true → c' i = true → c'' i = false →
        (1 - ε) * u i c' + ε * u i c'' < u i c := by
  dsimp only
  set ε : ℝ := Finset.univ.inf' Finset.univ_nonempty D
  constructor
  · intro hprio i c c' c'' hc hc' hc''
    obtain ⟨t₀, -, ht₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty D
    rw [show ε = D t₀ from ht₀]
    exact hprio i c c' c'' t₀ hc hc' hc''
  · intro hmin i c c' c'' t hc hc' hc''
    have hle : ε ≤ D t := Finset.inf'_le D (Finset.mem_univ t)
    have hlt : u i c'' < u i c' := hu.correctness i c' c'' hc' hc''
    have hbound : (1 - D t) * u i c' + D t * u i c'' ≤ (1 - ε) * u i c' + ε * u i c'' := by
      nlinarith
    exact hbound.trans_lt (hmin i c c' c'' hc hc' hc'')

/-- Standing non-degeneracy assumption of [DodisRabin2007], Section 8.5.1, p. 197: every player's
input matters for `f` on at least one profile of the other players' inputs. -/
@[expose] def EveryInputMatters [DecidableEq ι] (f : (∀ i, T i) → O) : Prop :=
  ∀ i : ι, ∃ (t : ∀ j, T j) (a : T i), f (update t i a) ≠ f t

/-- If at least one player exists and every input matters, then `f` is non-constant. -/
theorem EveryInputMatters.exists_ne [DecidableEq ι] [Nonempty ι] {f : (∀ i, T i) → O}
    (h : EveryInputMatters f) : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨t, a, hne⟩ := h i
  exact ⟨update t i a, t, hne⟩

/-- A unilateral strategy of player `i` in the mediated function evaluation game
([DodisRabin2007], Section 8.5.1, p. 198): given true input `t_i`, player `i` sends `report t_i`
to the mediator (`none` = refuse / send invalid type `⊥`) and then outputs `interpret t_i reply`
upon receiving the mediator's reply (`some y` or error `none`). -/
structure UnilateralDev (T : ι → Type*) (O : Type*) (i : ι) where
  /-- Input reported to the mediator (`none` models submitting invalid type `⊥`). -/
  report : T i → Option (T i)
  /-- Output guess produced from the true type and the mediator's message (`none` = error). -/
  interpret : T i → Option O → O

/-- The **canonical honest strategy profile** ([DodisRabin2007], Section 8.5.1, p. 198): every
party reports its true input `some (t i)`, outputs `y` upon receiving `some y`, and uses
`fallback i (t i)` if another party triggers an error message `none`. -/
@[expose] def honestProfile (fallback : ∀ i, T i → O) : ∀ i, UnilateralDev T O i :=
  fun i => ⟨some, fun t_i m => m.getD (fallback i t_i)⟩

/-- Reply broadcast by the canonical mediator on strategy profile `s` and true input profile `t`:
`some (f t')` if every player reports a valid input `some (t' j)`, and `none` (error) otherwise. -/
def mediatorReply [Fintype ι] (f : (∀ i, T i) → O)
    (s : ∀ i, UnilateralDev T O i) (t : ∀ i, T i) : Option O :=
  if h : ∀ j, ((s j).report (t j)).isSome then
    some (f fun j => ((s j).report (t j)).get (h j))
  else
    none

/-- The **mediated function evaluation game** ([DodisRabin2007], Section 8.5.1, p. 198) in
normal-form `PayoffGame` representation: expected utility over `t ∼ D` when each player `j` runs
`s j` with the canonical mediator computing `f`. -/
def mediatedGame [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ) :
    PayoffGame ι (fun i => UnilateralDev T O i) where
  payoff i s := ∑ t : ∀ j, T j,
    D t * u i fun j => decide ((s j).interpret (t j) (mediatorReply f s t) = f t)

@[simp]
theorem mediatedGame_payoff [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ)
    (i : ι) (s : ∀ j, UnilateralDev T O j) :
    (mediatedGame f u D).payoff i s = ∑ t : ∀ j, T j,
      D t * u i fun j => decide ((s j).interpret (t j) (mediatorReply f s t) = f t) := by
  rfl

/-- **Definition 8.5** ([DodisRabin2007], Section 8.5.1, p. 198): a function `f` is
**non-cooperatively computable (`NCC`)** with respect to utilities `u`, input prior `D`, and
error-fallback rule `fallback` if the canonical honest profile is a Nash equilibrium of the
mediated game (equivalently, the canonical mediator strategy is a correlated equilibrium of the
function evaluation game). -/
@[expose] def IsNCC [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ)
    (fallback : ∀ i, T i → O) : Prop :=
  (mediatedGame f u D).IsPureNash (honestProfile fallback)

/-- A function `f` is **dominated** ([DodisRabin2007], Section 8.5.1, p. 198) if some player `i`
has an input `t_i` that fixes `f (t_i, t_{-i}) = c` independently of all other players' inputs. -/
@[expose] def IsDominated (f : (∀ i, T i) → O) : Prop :=
  ∃ (i : ι) (t_i : T i) (c : O), ∀ t : ∀ j, T j, t i = t_i → f t = c

/-- A function `f` is **reversible** ([DodisRabin2007], Section 8.5.1, pp. 198–199) if some
player `i` has an input `t_i`, another report `t'_i`, and a recovery map `g : O → O` (since `t_i`
is fixed, `g (·, t_i)` is `g`) such that `g (f (t'_i, t_{-i})) = f (t_i, t_{-i})` for all `t_{-i}`
and `f (t'_i, t_{-i}) ≠ f (t_i, t_{-i})` for at least one `t_{-i}`. -/
@[expose] def IsReversible [DecidableEq ι] (f : (∀ i, T i) → O) : Prop :=
  ∃ (i : ι) (t_i t'_i : T i) (g : O → O),
    (∀ t : ∀ j, T j, t i = t_i → g (f (update t i t'_i)) = f t) ∧
    ∃ t : ∀ j, T j, t i = t_i ∧ f (update t i t'_i) ≠ f t

/-! #### Coalitional (`k-NCC`) definitions ([DodisRabin2007], Section 8.5.1, p. 199) -/

/-- Replace the coordinates of `t` inside coalition `C` with the pooled values `rC`, leaving
outsiders `j ∉ C` unchanged. -/
@[expose] def patchProfile [DecidableEq ι] (C : Finset ι)
    (rC : ∀ j : C, T j.val) (t : ∀ j, T j) : ∀ j, T j :=
  fun j => if h : j ∈ C then rC ⟨j, h⟩ else t j

@[simp]
theorem patchProfile_mem [DecidableEq ι] {C : Finset ι} (rC : ∀ j : C, T j.val)
    (t : ∀ j, T j) {j : ι} (hj : j ∈ C) :
    patchProfile C rC t j = rC ⟨j, hj⟩ := by
  simp [patchProfile, hj]

@[simp]
theorem patchProfile_notMem [DecidableEq ι] {C : Finset ι} (rC : ∀ j : C, T j.val)
    (t : ∀ j, T j) {j : ι} (hj : j ∉ C) :
    patchProfile C rC t j = t j := by
  simp [patchProfile, hj]

@[simp]
theorem patchProfile_self [DecidableEq ι] (C : Finset ι) (t : ∀ j, T j) :
    patchProfile C (fun j : C => t j.val) t = t := by
  funext j
  by_cases hj : j ∈ C <;> simp [patchProfile, hj]

@[simp]
theorem patchProfile_patchProfile [DecidableEq ι] (C : Finset ι)
    (r₁ r₂ : ∀ j : C, T j.val) (t : ∀ j, T j) :
    patchProfile C r₁ (patchProfile C r₂ t) = patchProfile C r₁ t := by
  funext j
  by_cases hj : j ∈ C <;> simp [patchProfile, hj]

/-- A joint strategy of coalition `C` that pools the members' true inputs `t_C : ∀ j : C, T j.1`
to choose a joint report to the mediator (`none` = abort / `⊥`) and joint output guesses for all
members of `C` ([DodisRabin2007], Section 8.5.1, "Collusions", p. 199). -/
structure CoalitionDev (T : ι → Type*) (O : Type*) (C : Finset ι) where
  /-- Joint report to the mediator (`none` triggers the mediator's error broadcast). -/
  report : (∀ j : C, T j.val) → Option (∀ j : C, T j.val)
  /-- Joint output guesses for all members of `C` given pooled inputs and the mediator reply. -/
  interpret : (∀ j : C, T j.val) → Option O → C → O

/-- Output produced by player `j` on true input profile `t` when coalition `C` runs `dev` and
outsiders `j ∉ C` follow the honest strategy with error rule `fallback`. -/
private def coalitionOutput [DecidableEq ι] (f : (∀ i, T i) → O) (fallback : ∀ i, T i → O)
    (C : Finset ι) (dev : CoalitionDev T O C) (t : ∀ i, T i) (j : ι) : O :=
  let tC : ∀ m : C, T m.val := fun m => t m.val
  match dev.report tC with
  | some rC =>
    let y := f (patchProfile C rC t)
    if h : j ∈ C then dev.interpret tC (some y) ⟨j, h⟩ else y
  | none =>
    if h : j ∈ C then dev.interpret tC none ⟨j, h⟩ else fallback j (t j)

/-- Expected utility of player `i` over `t ∼ D` when coalition `C` runs `dev` and outsiders follow
`honestProfile fallback`. -/
def coalitionPayoff [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ)
    (fallback : ∀ i, T i → O) (C : Finset ι) (dev : CoalitionDev T O C) (i : ι) : ℝ :=
  ∑ t : ∀ j, T j,
    D t * u i fun j => decide (coalitionOutput f fallback C dev t j = f t)

/-- **`k`-Non-Cooperatively Computable (`k-NCC`)** functions ([DodisRabin2007], Section 8.5.1,
"Collusions", p. 199): no coalition `C` of size at most `k` has a Pareto-beneficial pooled-input
deviation (where every member `i ∈ C` weakly improves and some member strictly improves over the
canonical honest profile). -/
@[expose] def IsKNCC [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    (f : (∀ i, T i) → O) (k : ℕ) (u : ι → (ι → Bool) → ℝ) (D : (∀ i, T i) → ℝ)
    (fallback : ∀ i, T i → O) : Prop :=
  ∀ (C : Finset ι), C.card ≤ k → ∀ (dev : CoalitionDev T O C),
    (∀ i ∈ C, (mediatedGame f u D).payoff i (honestProfile fallback) ≤
      coalitionPayoff f u D fallback C dev i) →
    ∀ i ∈ C, coalitionPayoff f u D fallback C dev i ≤
      (mediatedGame f u D).payoff i (honestProfile fallback)

/-- A function `f` is **`k`-dominated** if some nonempty coalition `C` of size at most `k` has a
joint input `tC` that fixes `f t = c` independently of all outsiders' inputs. -/
@[expose] def IsKDominated (f : (∀ i, T i) → O) (k : ℕ) : Prop :=
  ∃ (C : Finset ι), C.Nonempty ∧ C.card ≤ k ∧
    ∃ (tC : ∀ j : C, T j.val) (c : O), ∀ t : ∀ j, T j, (∀ j : C, t j.val = tC j) → f t = c

/-- A function `f` is **`k`-reversible** if some nonempty coalition `C` of size at most `k` has
pooled inputs `tC`, alternate reports `rC`, and a recovery map `g : O → O` such that
`g (f (patchProfile C rC t)) = f t` on the entire `tC`-fiber while `f (patchProfile C rC t) ≠ f t`
on at least one profile `t` in the `tC`-fiber. -/
@[expose] def IsKReversible [DecidableEq ι] (f : (∀ i, T i) → O) (k : ℕ) : Prop :=
  ∃ (C : Finset ι), C.Nonempty ∧ C.card ≤ k ∧
    ∃ (tC rC : ∀ j : C, T j.val) (g : O → O),
      (∀ t : ∀ j, T j, (∀ j : C, t j.val = tC j) → g (f (patchProfile C rC t)) = f t) ∧
      ∃ t : ∀ j, T j, (∀ j : C, t j.val = tC j) ∧ f (patchProfile C rC t) ≠ f t

end NCCDefinitions

/-! ### Core Theorems: Footnote 8, `k-NCC` Characterization, and Theorem 8.6 -/

section NCCTheorems

variable {ι : Type*} {T : ι → Type*} {O : Type*}

/-- `IsKNCC` is antitone in the coalition bound `k`. -/
theorem IsKNCC.mono [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]
    {f : (∀ i, T i) → O} {k₁ k₂ : ℕ} {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ}
    {fallback : ∀ i, T i → O} (h : IsKNCC f k₂ u D fallback) (hle : k₁ ≤ k₂) :
    IsKNCC f k₁ u D fallback :=
  fun C hC dev hge => h C (hC.trans hle) dev hge

/-- **Coalitional Footnote 8**: every `k`-dominated non-constant function is `k`-reversible. -/
theorem IsKDominated.isKReversible [DecidableEq ι] {f : (∀ i, T i) → O} {k : ℕ}
    (hdom : IsKDominated f k) (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂) :
    IsKReversible f k := by
  obtain ⟨C, hCne, hCcard, tC, c, hfix⟩ := hdom
  obtain ⟨t₁, t₂, ht12⟩ := hne
  have hex : ∃ tStar : ∀ j, T j, f tStar ≠ c := by
    by_cases h1 : f t₁ = c
    · exact ⟨t₂, fun h2 => ht12 (h1.trans h2.symm)⟩
    · exact ⟨t₁, h1⟩
  obtain ⟨tStar, htStar⟩ := hex
  refine ⟨C, hCne, hCcard, tC, fun j => tStar j.val, fun _ => c, ?_, ?_⟩
  · intro t htC
    exact (hfix t htC).symm
  · refine ⟨patchProfile C tC tStar, fun j => patchProfile_mem tC tStar j.property, ?_⟩
    rw [patchProfile_patchProfile, patchProfile_self,
      hfix (patchProfile C tC tStar) fun j => patchProfile_mem tC tStar j.property]
    exact htStar

/-- Lift a single player's type `a : T i` to a pooled input on the singleton coalition `{i}`. -/
private def singletonVal {i : ι} (a : T i) : ∀ j : ({i} : Finset ι), T j.val :=
  fun j => (Finset.mem_singleton.mp j.property).symm ▸ a

private theorem singletonVal_self {i : ι} (a : T i) :
    singletonVal a ⟨i, Finset.mem_singleton_self i⟩ = a :=
  rfl

private theorem patchProfile_singleton [DecidableEq ι] {i : ι}
    (rC : ∀ j : ({i} : Finset ι), T j.val) (t : ∀ j, T j) :
    patchProfile {i} rC t = update t i (rC ⟨i, Finset.mem_singleton_self i⟩) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [patchProfile]
  · simp [patchProfile, hj]

/-- `1`-domination coincides with `IsDominated`. -/
theorem isKDominated_one_iff_isDominated {f : (∀ i, T i) → O} :
    IsKDominated f 1 ↔ IsDominated f := by
  classical
  constructor
  · rintro ⟨C, hCne, hCcard, tC, c, hfix⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hCcard (Finset.one_le_card.mpr hCne))
    refine ⟨i, tC ⟨i, Finset.mem_singleton_self i⟩, c, fun t hti => hfix t ?_⟩
    intro ⟨j, hj⟩
    obtain rfl := Finset.mem_singleton.mp hj
    exact hti
  · rintro ⟨i, t_i, c, hfix⟩
    exact ⟨{i}, Finset.singleton_nonempty i, by simp, singletonVal t_i, c,
      fun t ht => hfix t (ht ⟨i, Finset.mem_singleton_self i⟩)⟩

/-- `1`-reversibility coincides with `IsReversible`. -/
theorem isKReversible_one_iff_isReversible [DecidableEq ι] {f : (∀ i, T i) → O} :
    IsKReversible f 1 ↔ IsReversible f := by
  constructor
  · rintro ⟨C, hCne, hCcard, tC, rC, g, hg, t₀, ht₀, hne⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hCcard (Finset.one_le_card.mpr hCne))
    refine ⟨i, tC ⟨i, Finset.mem_singleton_self i⟩, rC ⟨i, Finset.mem_singleton_self i⟩, g, ?_, ?_⟩
    · intro t hti
      rw [← patchProfile_singleton rC t]
      exact hg t fun ⟨j, hj⟩ => by
        obtain rfl := Finset.mem_singleton.mp hj
        exact hti
    · refine ⟨t₀, ht₀ ⟨i, Finset.mem_singleton_self i⟩, ?_⟩
      rw [← patchProfile_singleton rC t₀]
      exact hne
  · rintro ⟨i, t_i, t'_i, g, hg, t₀, ht₀, hne⟩
    refine ⟨{i}, Finset.singleton_nonempty i, by simp, singletonVal t_i, singletonVal t'_i, g,
      ?_, ?_⟩
    · intro t ht
      rw [patchProfile_singleton, singletonVal_self]
      exact hg t (ht ⟨i, Finset.mem_singleton_self i⟩)
    · refine ⟨t₀, ?_, ?_⟩
      · intro ⟨j, hj⟩
        obtain rfl := Finset.mem_singleton.mp hj
        exact ht₀
      · rw [patchProfile_singleton, singletonVal_self]
        exact hne

/-- **Footnote 8** ([DodisRabin2007], Section 8.5.1, p. 199): every dominated non-constant function
(in particular under `EveryInputMatters`) is reversible. -/
theorem IsDominated.isReversible [DecidableEq ι] {f : (∀ i, T i) → O}
    (hdom : IsDominated f) (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂) :
    IsReversible f :=
  isKReversible_one_iff_isReversible.mp
    ((isKDominated_one_iff_isDominated.mpr hdom).isKReversible hne)

/-- Under `honestProfile`, the canonical mediator always broadcasts `some (f t)`. -/
@[simp]
theorem mediatorReply_honest [Fintype ι] (f : (∀ i, T i) → O) (fallback : ∀ i, T i → O)
    (t : ∀ i, T i) :
    mediatorReply f (honestProfile fallback) t = some (f t) := by
  simp [mediatorReply, honestProfile]

/-- Under a unilateral deviation `dev` of player `i` from `honestProfile`, the canonical mediator
returns `some (f (update t i a))` if `dev.report (t i) = some a` and `none` if `dev` aborts. -/
theorem mediatorReply_update_honest [Fintype ι] [DecidableEq ι] (f : (∀ i, T i) → O)
    (fallback : ∀ i, T i → O) (i : ι) (dev : UnilateralDev T O i) (t : ∀ j, T j) :
    mediatorReply f (update (honestProfile fallback) i dev) t =
      match dev.report (t i) with
      | some a => some (f (update t i a))
      | none => none := by
  cases hrep : dev.report (t i) with
  | none =>
    have hnot : ¬ ∀ j, ((update (honestProfile fallback) i dev j).report (t j)).isSome := by
      intro hall
      have hi := hall i
      rw [update_self, hrep] at hi
      simp at hi
    simp [mediatorReply, hnot]
  | some a =>
    have hall : ∀ j, ((update (honestProfile fallback) i dev j).report (t j)).isSome := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hrep]
      · simp [update_of_ne hj, honestProfile]
    simp only [mediatorReply, dite_eq_left hall]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp [hrep]
    · simp [update_of_ne hj, honestProfile]

variable [Fintype ι] [DecidableEq ι] [∀ j, Fintype (T j)] [DecidableEq O]

/-- Under the canonical honest profile, every player always outputs `f t`, so player `i`'s payoff
is `∑ t, D t * u i (fun _ => true)`. -/
private theorem payoff_mediatedGame_honest (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ)
    (D : (∀ i, T i) → ℝ) (fallback : ∀ i, T i → O) (i : ι) :
    (mediatedGame f u D).payoff i (honestProfile fallback) =
      ∑ t : ∀ j, T j, D t * u i (fun _ => true) := by
  simp [mediatedGame, mediatorReply_honest, honestProfile]

/-- When `D` is a probability distribution (`IsMixedStrategy D`), the honest expected payoff equals
`u i (fun _ => true)`. -/
theorem payoff_mediatedGame_honest_eq (f : (∀ i, T i) → O) (u : ι → (ι → Bool) → ℝ)
    {D : (∀ i, T i) → ℝ} (hD : IsMixedStrategy D) (fallback : ∀ i, T i → O) (i : ι) :
    (mediatedGame f u D).payoff i (honestProfile fallback) = u i (fun _ => true) := by
  rw [payoff_mediatedGame_honest, ← Finset.sum_mul, hD.sum_eq_one, one_mul]

/-- `1-NCC` coincides exactly with `IsNCC` (Definition 8.5). -/
theorem isKNCC_one_iff_isNCC {f : (∀ i, T i) → O} {u : ι → (ι → Bool) → ℝ}
    {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O} :
    IsKNCC f 1 u D fallback ↔ IsNCC f u D fallback := by
  constructor
  · intro hkncc i dev
    let cdev : CoalitionDev T O {i} :=
      { report := fun tC => (dev.report (tC ⟨i, Finset.mem_singleton_self i⟩)).map singletonVal
        interpret := fun tC m _ => dev.interpret (tC ⟨i, Finset.mem_singleton_self i⟩) m }
    have hpay : coalitionPayoff f u D fallback {i} cdev i =
        (mediatedGame f u D).payoff i (update (honestProfile fallback) i dev) := by
      simp only [coalitionPayoff, mediatedGame]
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 2
      funext j
      congr 1
      simp only [coalitionOutput, cdev, mediatorReply_update_honest]
      cases hrep : dev.report (t i) with
      | none =>
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, honestProfile]
      | some a =>
        by_cases hj : j = i
        · subst hj; simp [patchProfile_singleton, singletonVal_self]
        · simp [hj, patchProfile_singleton, singletonVal_self, honestProfile]
    by_contra hlt
    push Not at hlt
    have hle := hkncc {i} (by simp) cdev
      (fun j hj => by
        obtain rfl := Finset.mem_singleton.mp hj
        exact hpay ▸ hlt.le)
      i (Finset.mem_singleton_self i)
    rw [hpay] at hle
    exact hlt.not_ge hle
  · intro hncc C hC dev _ i hi
    obtain ⟨i', rfl⟩ := Finset.card_eq_one.mp
      (le_antisymm hC (Finset.one_le_card.mpr ⟨i, hi⟩))
    obtain rfl := Finset.mem_singleton.mp hi
    let udev : UnilateralDev T O i :=
      { report := fun a =>
          (dev.report (singletonVal a)).map fun rC => rC ⟨i, Finset.mem_singleton_self i⟩
        interpret := fun a m =>
          dev.interpret (singletonVal a) m ⟨i, Finset.mem_singleton_self i⟩ }
    have hpay : coalitionPayoff f u D fallback {i} dev i =
        (mediatedGame f u D).payoff i (update (honestProfile fallback) i udev) := by
      simp only [coalitionPayoff, mediatedGame]
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 2
      funext j
      congr 1
      have htC : (fun m : ({i} : Finset ι) => t m.val) = singletonVal (t i) := by
        funext ⟨m, hm⟩
        obtain rfl := Finset.mem_singleton.mp hm
        rfl
      simp only [coalitionOutput, htC, mediatorReply_update_honest, udev]
      cases hrep : dev.report (singletonVal (t i)) with
      | none =>
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, honestProfile]
      | some rC =>
        by_cases hj : j = i
        · subst hj; simp [patchProfile_singleton]
        · simp [hj, patchProfile_singleton, honestProfile]
    rw [hpay]
    exact hncc i udev

/-- Under high-correctness priority, any coalition deviation that causes member `i` to guess
wrongly on even a single input profile `t₀` strictly lowers `i`'s expected payoff below the
honest payoff. -/
private theorem coalitionPayoff_lt_honest_of_wrong {f : (∀ i, T i) → O}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hu : CorrectnessExclusivity u) (hD : IsMixedStrategy D)
    (hprio : HighCorrectnessPriority u D) {C : Finset ι} (dev : CoalitionDev T O C)
    {i : ι} {t₀ : ∀ j, T j} (hwrong : coalitionOutput f fallback C dev t₀ i ≠ f t₀) :
    coalitionPayoff f u D fallback C dev i <
      (mediatedGame f u D).payoff i (honestProfile fallback) := by
  let corr : (∀ j, T j) → ι → Bool :=
    fun t j => decide (coalitionOutput f fallback C dev t j = f t)
  let S_true : Finset (ι → Bool) := Finset.univ.filter fun c => c i = true
  let S_false : Finset (ι → Bool) := Finset.univ.filter fun c => c i = false
  have hSt_ne : S_true.Nonempty := ⟨fun _ => true, by simp [S_true]⟩
  have hSf_ne : S_false.Nonempty := ⟨fun _ => false, by simp [S_false]⟩
  obtain ⟨cMax, hcMax_mem, hcMax⟩ := Finset.exists_max_image S_true (u i) hSt_ne
  obtain ⟨cBad, hcBad_mem, hcBad⟩ := Finset.exists_max_image S_false (u i) hSf_ne
  have hcMax_i : cMax i = true := (Finset.mem_filter.mp hcMax_mem).2
  have hcBad_i : cBad i = false := (Finset.mem_filter.mp hcBad_mem).2
  let good : Finset (∀ j, T j) := Finset.univ.filter fun t => corr t i = true
  let bad : Finset (∀ j, T j) := Finset.univ.filter fun t => ¬ corr t i = true
  have hsplit : coalitionPayoff f u D fallback C dev i =
      (∑ t ∈ good, D t * u i (corr t)) + ∑ t ∈ bad, D t * u i (corr t) := by
    simp only [coalitionPayoff, good, bad, corr]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hsumD : (∑ t ∈ good, D t) + ∑ t ∈ bad, D t = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, hD.sum_eq_one]
  have hgood_le : ∑ t ∈ good, D t * u i (corr t) ≤ (∑ t ∈ good, D t) * u i cMax := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (hD.nonneg t)
    exact hcMax (corr t) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩)
  have hbad_le : ∑ t ∈ bad, D t * u i (corr t) ≤ (∑ t ∈ bad, D t) * u i cBad := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (hD.nonneg t)
    have hf : corr t i = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp ht).2
    exact hcBad (corr t) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)
  have ht0_mem : t₀ ∈ bad := by
    simp [bad, corr, hwrong]
  have hDt0_le : D t₀ ≤ ∑ t ∈ bad, D t :=
    Finset.single_le_sum (fun t _ => hD.nonneg t) ht0_mem
  have hlt_u : u i cBad < u i cMax := hu.correctness i cMax cBad hcMax_i hcBad_i
  have hprio0 := hprio i (fun _ => true) cMax cBad t₀ rfl hcMax_i hcBad_i
  have hgood_eq : ∑ t ∈ good, D t = 1 - ∑ t ∈ bad, D t := by linarith
  rw [hgood_eq] at hgood_le
  have hmono : (1 - ∑ t ∈ bad, D t) * u i cMax + (∑ t ∈ bad, D t) * u i cBad ≤
      (1 - D t₀) * u i cMax + D t₀ * u i cBad := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hDt0_le) (sub_pos.mpr hlt_u).le]
  rw [payoff_mediatedGame_honest_eq f u hD fallback i, hsplit]
  linarith

/-- Sufficiency direction of the `k-NCC` characterization: under correctness, exclusivity, and
high-correctness priority, any function that is neither `k`-dominated nor `k`-reversible is
`k-NCC` (for every honest fallback rule). -/
theorem isKNCC_of_not_kDominated_and_not_kReversible {f : (∀ i, T i) → O} {k : ℕ}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hu : CorrectnessExclusivity u) (hD : IsMixedStrategy D)
    (hprio : HighCorrectnessPriority u D)
    (hndom : ¬ IsKDominated f k) (hnrev : ¬ IsKReversible f k) :
    IsKNCC f k u D fallback := by
  intro C hCcard dev hge i hi
  have hall_mem : ∀ j ∈ C, ∀ t : ∀ m, T m, coalitionOutput f fallback C dev t j = f t := by
    intro j hj t
    by_contra hne
    have hlt := coalitionPayoff_lt_honest_of_wrong hu hD hprio dev hne
    exact hlt.not_ge (hge j hj)
  have hall_out : ∀ t : ∀ m, T m, ∀ j, j ∉ C → coalitionOutput f fallback C dev t j = f t := by
    intro t j hj
    let tC : ∀ m : C, T m.val := fun m => t m.val
    cases hrep : dev.report tC with
    | none =>
      exfalso
      refine hndom ⟨C, ⟨i, hi⟩, hCcard, tC, dev.interpret tC none ⟨i, hi⟩, fun t' ht' => ?_⟩
      have ht'C : (fun m : C => t' m.val) = tC := funext ht'
      have hi_eq := hall_mem i hi t'
      simp only [coalitionOutput, ht'C, hrep, hi, ↓reduceDIte] at hi_eq
      exact hi_eq.symm
    | some rC =>
      have hsame : f (patchProfile C rC t) = f t := by
        by_contra hne
        refine hnrev ⟨C, ⟨i, hi⟩, hCcard, tC, rC,
          fun y => dev.interpret tC (some y) ⟨i, hi⟩, ?_, t, fun _ => rfl, hne⟩
        intro t' ht'
        have ht'C : (fun m : C => t' m.val) = tC := funext ht'
        have hi_eq := hall_mem i hi t'
        simp only [coalitionOutput, ht'C, hrep, hi, ↓reduceDIte] at hi_eq
        exact hi_eq
      simp only [coalitionOutput, show (fun m : C => t m.val) = tC from rfl, hrep, hj, ↓reduceDIte]
      exact hsame
  have hall : ∀ t : ∀ m, T m, ∀ j, coalitionOutput f fallback C dev t j = f t := fun t j =>
    if hj : j ∈ C then hall_mem j hj t else hall_out t j hj
  have hpay_eq : coalitionPayoff f u D fallback C dev i =
      (mediatedGame f u D).payoff i (honestProfile fallback) := by
    rw [payoff_mediatedGame_honest]
    simp only [coalitionPayoff]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    funext j
    simp [hall t j]
  exact hpay_eq.le

/-- Necessity direction for `k`-reversibility: if `k < |ι|`, `D` has full support, and utilities
satisfy exclusivity, then no `k`-reversible function is `k-NCC`. -/
theorem IsKReversible.not_isKNCC {f : (∀ i, T i) → O} {k : ℕ}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hrev : IsKReversible f k) (hk : k < Fintype.card ι)
    (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsKNCC f k u D fallback := by
  classical
  intro hkncc
  obtain ⟨C, ⟨i₀, hi₀⟩, hCcard, tC, rC, g, hg, t₀, ht₀C, ht₀ne⟩ := hrev
  have hne_univ : C ≠ Finset.univ := fun h => by
    have : Fintype.card ι ≤ k := by simpa [h] using hCcard
    omega
  obtain ⟨jOut, hjOut⟩ : ∃ jOut : ι, jOut ∉ C := by
    by_contra hall
    push Not at hall
    exact hne_univ (Finset.eq_univ_iff_forall.mpr hall)
  let dev : CoalitionDev T O C :=
    { report := fun x => if x = tC then some rC else some x
      interpret := fun x m j =>
        match m with
        | some y => if x = tC then g y else y
        | none => fallback j.val (x j) }
  have hstrict : ∀ i ∈ C,
      (mediatedGame f u D).payoff i (honestProfile fallback) <
        coalitionPayoff f u D fallback C dev i := by
    intro i hi
    rw [payoff_mediatedGame_honest]
    simp only [coalitionPayoff]
    refine Finset.sum_lt_sum ?_ ⟨t₀, Finset.mem_univ _, ?_⟩
    · intro t _
      refine mul_le_mul_of_nonneg_left ?_ (hDpos t).le
      let xC : ∀ m : C, T m.val := fun m => t m.val
      by_cases hx : xC = tC
      · by_cases hfeq : f (patchProfile C rC t) = f t
        · have hcorr : (fun j => decide (coalitionOutput f fallback C dev t j = f t)) =
              fun _ => true := by
            funext j
            by_cases hj : j ∈ C
            · simp [coalitionOutput, dev, xC, hx, hj, hg t (congrFun hx)]
            · simp [coalitionOutput, dev, xC, hx, hj, hfeq]
          rw [hcorr]
        · refine (hu.exclusivity i _ (fun _ => true) ?_ (fun _ _ _ => rfl) ?_).le
          · simp [coalitionOutput, dev, xC, hx, hi, hg t (congrFun hx)]
          · refine ⟨jOut, fun heq => hjOut (heq ▸ hi), ?_, rfl⟩
            simp [coalitionOutput, dev, xC, hx, hjOut, hfeq]
      · have hcorr : (fun j => decide (coalitionOutput f fallback C dev t j = f t)) =
            fun _ => true := by
          funext j
          by_cases hj : j ∈ C
          · simp [coalitionOutput, dev, xC, hx, hj]
          · simp [coalitionOutput, dev, xC, hx, hj]
        rw [hcorr]
    · refine mul_lt_mul_of_pos_left ?_ (hDpos t₀)
      have hx0 : (fun m : C => t₀ m.val) = tC := funext ht₀C
      refine hu.exclusivity i _ (fun _ => true) ?_ (fun _ _ _ => rfl) ?_
      · simp [coalitionOutput, dev, hx0, hi, hg t₀ ht₀C]
      · refine ⟨jOut, fun heq => hjOut (heq ▸ hi), ?_, rfl⟩
        simp [coalitionOutput, dev, hx0, hjOut, ht₀ne]
  have hle := hkncc C hCcard dev (fun i hi => (hstrict i hi).le) i₀ hi₀
  exact (hstrict i₀ hi₀).not_ge hle

/-- Necessity direction for `k`-domination: no `k`-dominated non-constant function is `k-NCC`
for `k < |ι|`. -/
theorem IsKDominated.not_isKNCC {f : (∀ i, T i) → O} {k : ℕ}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hdom : IsKDominated f k) (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂)
    (hk : k < Fintype.card ι) (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsKNCC f k u D fallback :=
  (hdom.isKReversible hne).not_isKNCC hk hu hDpos

/-- **Coalitional `k-NCC` characterization** (after [DodisRabin2007], Section 8.5.1, "Collusions",
p. 199): for any `k < |ι|`, any non-constant function `f`, prior `D`, and utilities satisfying
correctness, exclusivity, and high-correctness priority (which implies full support
`∀ t, 0 < D t` by `HighCorrectnessPriority.pos`), `f` is `k-NCC` if and only if `f` is neither
`k`-dominated nor `k`-reversible (uniformly in `fallback`). -/
theorem isKNCC_iff_not_kDominated_and_not_kReversible
    {f : (∀ i, T i) → O} {k : ℕ} {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ}
    {fallback : ∀ i, T i → O} (hk : k < Fintype.card ι)
    (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂) (hu : CorrectnessExclusivity u)
    (hD : IsMixedStrategy D) (hprio : HighCorrectnessPriority u D) :
    IsKNCC f k u D fallback ↔ ¬ IsKDominated f k ∧ ¬ IsKReversible f k := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hDpos : ∀ t, 0 < D t := hprio.pos hu
  exact ⟨fun h => ⟨fun hd => hd.not_isKNCC hne hk hu hDpos h,
      fun hr => hr.not_isKNCC hk hu hDpos h⟩,
    fun ⟨hnd, hnr⟩ => isKNCC_of_not_kDominated_and_not_kReversible hu hD hprio hnd hnr⟩

/-- Every reversible function fails to be `NCC` when `2 ≤ |ι|`, `D` has full support, and
utilities satisfy exclusivity ([DodisRabin2007], Section 8.5.1, pp. 198–199). -/
theorem IsReversible.not_isNCC {f : (∀ i, T i) → O}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hrev : IsReversible f) (hcard : 2 ≤ Fintype.card ι)
    (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsNCC f u D fallback := by
  rw [← isKNCC_one_iff_isNCC]
  exact (isKReversible_one_iff_isReversible.mpr hrev).not_isKNCC (by omega) hu hDpos

/-- Every dominated non-constant function fails to be `NCC` when `2 ≤ |ι|`, `D` has full support,
and utilities satisfy exclusivity ([DodisRabin2007], Section 8.5.1, pp. 198–199). -/
theorem IsDominated.not_isNCC {f : (∀ i, T i) → O}
    {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ} {fallback : ∀ i, T i → O}
    (hdom : IsDominated f) (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂)
    (hcard : 2 ≤ Fintype.card ι) (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsNCC f u D fallback :=
  (hdom.isReversible hne).not_isNCC hcard hu hDpos

/-- **Theorem 8.6** ([DodisRabin2007], Section 8.5.1, p. 199): under correctness, exclusivity,
high-correctness priority (which implies full support `∀ t, 0 < D t` via
`HighCorrectnessPriority.pos`), input prior `D`, at least two players (`2 ≤ |ι|`), and
non-constancy of `f` (implied by the source's p. 197 standing assumption `EveryInputMatters f`),
`f` is non-cooperatively computable (`IsNCC`) if and only if `f` is neither dominated nor
reversible, uniformly in the honest error-fallback rule `fallback`. -/
theorem isNCC_iff_not_dominated_and_not_reversible
    {f : (∀ i, T i) → O} {u : ι → (ι → Bool) → ℝ} {D : (∀ i, T i) → ℝ}
    {fallback : ∀ i, T i → O} (hcard : 2 ≤ Fintype.card ι)
    (hne : ∃ t₁ t₂ : ∀ j, T j, f t₁ ≠ f t₂) (hu : CorrectnessExclusivity u)
    (hD : IsMixedStrategy D) (hprio : HighCorrectnessPriority u D) :
    IsNCC f u D fallback ↔ ¬ IsDominated f ∧ ¬ IsReversible f := by
  rw [← isKNCC_one_iff_isNCC, ← isKDominated_one_iff_isDominated,
    ← isKReversible_one_iff_isReversible]
  exact isKNCC_iff_not_kDominated_and_not_kReversible (by omega) hne hu hD hprio

end NCCTheorems

/-! ### Canonical Boolean Function Witnesses ([DodisRabin2007], Section 8.5.1, p. 199) -/

section BooleanWitnesses

open Cslib.BitString

/-- `Cslib.parity n` is reversible for every `n ≥ 1`: negating one's input negates the parity,
which is recovered by negating the mediator's reply ([DodisRabin2007], p. 199). -/
theorem isReversible_parity {n : ℕ} (hn : 1 ≤ n) : IsReversible (Cslib.parity n) := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨i0, false, true, Bool.not, ?_, fun _ => false, rfl, ?_⟩
  · intro t ht
    have hnot : update t i0 true = update t i0 (!t i0) := by simp [ht]
    rw [hnot, Cslib.parity_update_not, Bool.not_not]
  · have hnot : update (fun _ : Fin n => false) i0 true =
        update (fun _ : Fin n => false) i0 (!(fun _ : Fin n => false) i0) := by simp
    rw [hnot, Cslib.parity_update_not]
    cases Cslib.parity n (fun _ => false) <;> decide

/-- `Cslib.parity n` (`n ≥ 2`) is not `NCC` ([DodisRabin2007], p. 199). -/
theorem not_isNCC_parity {n : ℕ} (hn : 2 ≤ n) {u : Fin n → (Fin n → Bool) → ℝ}
    {D : BitString n → ℝ} {fallback : Fin n → Bool → Bool}
    (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsNCC (Cslib.parity n) u D fallback :=
  (isReversible_parity (by omega)).not_isNCC (by simpa using hn) hu hDpos

private theorem weight_eq_card_in_add_out {n : ℕ} (C : Finset (Fin n)) (x : BitString n) :
    weight x = (C.filter fun j => x j = true).card + (Cᶜ.filter fun j => x j = true).card := by
  have hdisj : Disjoint (C.filter fun j => x j = true) (Cᶜ.filter fun j => x j = true) :=
    Finset.disjoint_filter_filter disjoint_compl_right
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, Finset.union_compl, weight]

/-- Build a bit string equal to `tC` on `C` and equal to the indicator of `S` outside `C`. -/
private def extBit {n : ℕ} (C : Finset (Fin n)) (tC : C → Bool)
    (S : Finset (Fin n)) : BitString n :=
  fun j => if h : j ∈ C then tC ⟨j, h⟩ else decide (j ∈ S)

private theorem extBit_mem {n : ℕ} {C : Finset (Fin n)} (tC : C → Bool)
    (S : Finset (Fin n)) (j : C) :
    extBit C tC S j.val = tC j := by
  simp [extBit, j.property]

private theorem patchProfile_extBit {n : ℕ} (C : Finset (Fin n)) (tC rC : C → Bool)
    (S : Finset (Fin n)) :
    patchProfile C rC (extBit C tC S) = extBit C rC S := by
  funext j
  by_cases hj : j ∈ C <;> simp [patchProfile, extBit, hj]

private theorem card_filter_in_eq {n : ℕ} {C : Finset (Fin n)} (aC : C → Bool)
    (x : BitString n) (hx : ∀ m : C, x m.val = aC m) :
    (C.filter fun m => x m = true).card = #{m : C | aC m = true} := by
  refine Finset.card_bij (fun m hm => ⟨m, (Finset.mem_filter.mp hm).1⟩) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmC, hxm⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [← hx ⟨m, hmC⟩]⟩
  · intro _ _ _ _ h; exact congrArg Subtype.val h
  · intro ⟨m, hmC⟩ hm
    have ha := (Finset.mem_filter.mp hm).2
    exact ⟨m, Finset.mem_filter.mpr ⟨hmC, by rwa [hx ⟨m, hmC⟩]⟩, rfl⟩

private theorem weight_extBit {n : ℕ} {C : Finset (Fin n)} (tC : C → Bool)
    {S : Finset (Fin n)} (hS : S ⊆ Cᶜ) :
    weight (extBit C tC S) = #{j : C | tC j = true} + S.card := by
  rw [weight_eq_card_in_add_out C]
  congr 1
  · exact card_filter_in_eq tC (extBit C tC S) (extBit_mem tC S)
  · suffices (Cᶜ.filter fun j => extBit C tC S j = true) = S by rw [this]
    ext j
    rw [Finset.mem_filter, Finset.mem_compl]
    by_cases hj : j ∈ C
    · have hjS : j ∉ S := fun h => (Finset.mem_compl.mp (hS h)) hj
      simp [hj, hjS]
    · simp [extBit, hj]

private theorem threshold_extBit_eq_true {n j : ℕ} {C : Finset (Fin n)} (aC : C → Bool)
    {S : Finset (Fin n)} (hS : S ⊆ Cᶜ) (hle : j ≤ #{m : C | aC m = true} + S.card) :
    Cslib.threshold n j (extBit C aC S) = true := by
  rw [Cslib.threshold_eq_true_iff, weight_extBit aC hS]
  exact hle

private theorem threshold_extBit_eq_false {n j : ℕ} {C : Finset (Fin n)} (aC : C → Bool)
    {S : Finset (Fin n)} (hS : S ⊆ Cᶜ) (hlt : #{m : C | aC m = true} + S.card < j) :
    Cslib.threshold n j (extBit C aC S) = false := by
  rw [← Bool.not_eq_true, Cslib.threshold_eq_true_iff, weight_extBit aC hS]
  omega

/-- A threshold function `threshold n j` (`1 ≤ j ≤ n`) is non-constant. -/
private theorem exists_ne_threshold {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t₁ t₂ : BitString n, Cslib.threshold n j t₁ ≠ Cslib.threshold n j t₂ := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  have h1 : Cslib.threshold n j (fun _ => true) = true := by
    rw [Cslib.threshold_eq_true_iff, weight]
    simpa using hjn
  have h0 : Cslib.threshold n j (fun _ => false) = false := by
    rw [← Bool.not_eq_true, Cslib.threshold_eq_true_iff, weight]
    simp; omega
  rw [h1, h0]
  decide

/-- When `1 ≤ j ≤ k` and `j ≤ n`, any `j`-player coalition setting all its bits to `true` fixes
`threshold n j` to `true`, so `threshold n j` is `k`-dominated. -/
private theorem isKDominated_threshold_of_le {n j k : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hjk : j ≤ k) :
    IsKDominated (Cslib.threshold n j) k := by
  have hcard : j ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hjn
  obtain ⟨C, -, hCcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨C, Finset.card_pos.mp (by omega), by omega, fun _ => true, true, fun t ht => ?_⟩
  rw [Cslib.threshold_eq_true_iff, weight_eq_card_in_add_out C]
  have hsub : C ⊆ C.filter fun m => t m = true := fun m hm =>
    Finset.mem_filter.mpr ⟨hm, ht ⟨m, hm⟩⟩
  have hle : C.card ≤ (C.filter fun m => t m = true).card := Finset.card_le_card hsub
  omega

/-- When `1 ≤ j ≤ n` and `n - j < k`, any `(n - j + 1)`-player coalition setting all its bits to
`false` fixes `threshold n j` to `false`, so `threshold n j` is `k`-dominated. -/
private theorem isKDominated_threshold_of_sub_lt {n j k : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hsub : n - j < k) :
    IsKDominated (Cslib.threshold n j) k := by
  have hcard : n - j + 1 ≤ (Finset.univ : Finset (Fin n)).card := by simp; omega
  obtain ⟨C, -, hCcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨C, Finset.card_pos.mp (by omega), by omega, fun _ => false, false, fun t ht => ?_⟩
  rw [← Bool.not_eq_true, Cslib.threshold_eq_true_iff, weight_eq_card_in_add_out C]
  have hzero : (C.filter fun m => t m = true).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m hm
    simp [ht ⟨m, hm⟩]
  have hout : (Cᶜ.filter fun m => t m = true).card ≤ Cᶜ.card := Finset.card_filter_le _ _
  have hcompl : Cᶜ.card = n - C.card := by rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- `threshold n j` is not `k`-dominated whenever `k < j` and `j + k ≤ n`. -/
private theorem not_isKDominated_threshold {n j k : ℕ} (hkj : k < j) (hjk : j + k ≤ n) :
    ¬ IsKDominated (Cslib.threshold n j) k := by
  rintro ⟨C, -, hCcard, tC, c, hfix⟩
  have hcompl : Cᶜ.card = n - C.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hle : #{m : C | tC m = true} ≤ C.card := by
    simpa [Fintype.card_coe] using Finset.card_filter_le (Finset.univ : Finset C) _
  have hc1 := hfix (extBit C tC Cᶜ) (extBit_mem tC Cᶜ)
  have hc0 := hfix (extBit C tC ∅) (extBit_mem tC ∅)
  rw [threshold_extBit_eq_true tC subset_rfl (by omega)] at hc1
  rw [threshold_extBit_eq_false tC (Finset.empty_subset _)
    (by simp only [Finset.card_empty, add_zero]; omega)] at hc0
  exact Bool.false_ne_true (hc0.trans hc1.symm)

/-- `threshold n j` is not `k`-reversible whenever `k < j` and `j + k ≤ n`. -/
private theorem not_isKReversible_threshold {n j k : ℕ} (hkj : k < j) (hjk : j + k ≤ n) :
    ¬ IsKReversible (Cslib.threshold n j) k := by
  rintro ⟨C, -, hCcard, tC, rC, g, hg, t₀, ht₀C, ht₀ne⟩
  set wt := #{m : C | tC m = true}
  set wr := #{m : C | rC m = true}
  have hwt_le : wt ≤ C.card := by
    simpa [wt, Fintype.card_coe] using Finset.card_filter_le (Finset.univ : Finset C) _
  have hwr_le : wr ≤ C.card := by
    simpa [wr, Fintype.card_coe] using Finset.card_filter_le (Finset.univ : Finset C) _
  have hcompl : Cᶜ.card = n - C.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hne_w : wr ≠ wt := by
    intro heq
    apply ht₀ne
    have hw_eq : weight (patchProfile C rC t₀) = weight t₀ := by
      rw [weight_eq_card_in_add_out C (patchProfile C rC t₀), weight_eq_card_in_add_out C t₀]
      have hout : (Cᶜ.filter fun m => patchProfile C rC t₀ m = true) =
          Cᶜ.filter fun m => t₀ m = true :=
        Finset.filter_congr fun m hm => by simp [patchProfile_notMem rC t₀ (Finset.mem_compl.mp hm)]
      rw [hout]
      congr 1
      rw [card_filter_in_eq rC (patchProfile C rC t₀) (fun m => patchProfile_mem rC t₀ m.property),
        card_filter_in_eq tC t₀ ht₀C]
      exact heq
    simp only [Cslib.threshold_apply, hw_eq]
  have hstep (S₀ S₁ : Finset (Fin n)) (hS₀ : S₀ ⊆ Cᶜ) (hS₁ : S₁ ⊆ Cᶜ) {b : Bool}
      (h0r : Cslib.threshold n j (extBit C rC S₀) = b)
      (h0t : Cslib.threshold n j (extBit C tC S₀) = b)
      (h1r : Cslib.threshold n j (extBit C rC S₁) = b)
      (h1t : Cslib.threshold n j (extBit C tC S₁) = !b) : False := by
    have h0 := hg (extBit C tC S₀) (extBit_mem tC S₀)
    have h1 := hg (extBit C tC S₁) (extBit_mem tC S₁)
    rw [patchProfile_extBit, h0r, h0t] at h0
    rw [patchProfile_extBit, h1r, h1t] at h1
    cases b <;> exact Bool.false_ne_true (by simp_all)
  rcases lt_or_gt_of_ne hne_w with hlt | hgt
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := Cᶜ) (n := j - wt) (by omega)
    exact hstep ∅ S (Finset.empty_subset _) hSsub (b := false)
      (threshold_extBit_eq_false rC (Finset.empty_subset _)
        (by simp only [Finset.card_empty, add_zero]; omega))
      (threshold_extBit_eq_false tC (Finset.empty_subset _)
        (by simp only [Finset.card_empty, add_zero]; omega))
      (threshold_extBit_eq_false rC hSsub (by omega))
      (threshold_extBit_eq_true tC hSsub (by omega))
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := Cᶜ) (n := j - wr) (by omega)
    exact hstep Cᶜ S subset_rfl hSsub (b := true)
      (threshold_extBit_eq_true rC subset_rfl (by omega))
      (threshold_extBit_eq_true tC subset_rfl (by omega))
      (threshold_extBit_eq_true rC hSsub (by omega))
      (threshold_extBit_eq_false tC hSsub (by omega))

/-- `n`-bit disjunction (`Cslib.threshold n 1`, `n ≥ 2`) is dominated and hence not `NCC`: a
concrete Boolean corollary of the domination rule in [DodisRabin2007], Section 8.5.1, p. 198. -/
theorem not_isNCC_or {n : ℕ} (hn : 2 ≤ n) {u : Fin n → (Fin n → Bool) → ℝ}
    {D : BitString n → ℝ} {fallback : Fin n → Bool → Bool}
    (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsNCC (Cslib.threshold n 1) u D fallback :=
  (isKDominated_one_iff_isDominated.mp
    (isKDominated_threshold_of_le le_rfl (by omega) le_rfl)).not_isNCC
    (exists_ne_threshold le_rfl (by omega)) (by simpa using hn) hu hDpos

/-- `n`-bit conjunction (`Cslib.threshold n n`, `n ≥ 2`) is dominated and hence not `NCC`: a
concrete Boolean corollary of the domination rule in [DodisRabin2007], Section 8.5.1, p. 198. -/
theorem not_isNCC_and {n : ℕ} (hn : 2 ≤ n) {u : Fin n → (Fin n → Bool) → ℝ}
    {D : BitString n → ℝ} {fallback : Fin n → Bool → Bool}
    (hu : CorrectnessExclusivity u) (hDpos : ∀ t, 0 < D t) :
    ¬ IsNCC (Cslib.threshold n n) u D fallback :=
  (isKDominated_one_iff_isDominated.mp
    (isKDominated_threshold_of_sub_lt (by omega) le_rfl (by omega))).not_isNCC
    (exists_ne_threshold (by omega) le_rfl) (by simpa using hn) hu hDpos

/-- Exact `k-NCC` threshold for odd-player majority (`Cslib.majority (2 * m + 1)`, `m ≥ 1`):
under correctness, exclusivity, and high-correctness priority (which implies full support of `D`
by `HighCorrectnessPriority.pos`), majority on `2 * m + 1` parties is `k-NCC` if and only if
`k ≤ m` (no coalition of size `≤ m` dominates or reverses majority, whereas `m + 1` parties
dominate it). -/
theorem isKNCC_majority_iff {m k : ℕ} (hm : 1 ≤ m)
    {u : Fin (2 * m + 1) → (Fin (2 * m + 1) → Bool) → ℝ}
    {D : BitString (2 * m + 1) → ℝ} {fallback : Fin (2 * m + 1) → Bool → Bool}
    (hu : CorrectnessExclusivity u) (hD : IsMixedStrategy D)
    (hprio : HighCorrectnessPriority u D) :
    IsKNCC (Cslib.majority (2 * m + 1)) k u D fallback ↔ k ≤ m := by
  have hmaj : Cslib.majority (2 * m + 1) = Cslib.threshold (2 * m + 1) (m + 1) := by
    simp [Cslib.majority, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  rw [hmaj]
  constructor
  · intro hkncc
    by_contra hgt
    have hm1_le : m + 1 ≤ k := by omega
    have hdom : IsKDominated (Cslib.threshold (2 * m + 1) (m + 1)) (m + 1) :=
      isKDominated_threshold_of_le (by omega) (by omega) le_rfl
    exact hdom.not_isKNCC (exists_ne_threshold (by omega) (by omega))
      (by simp; omega) hu (hprio.pos hu) (hkncc.mono hm1_le)
  · intro hk
    exact isKNCC_of_not_kDominated_and_not_kReversible hu hD hprio
      (not_isKDominated_threshold (by omega) (by omega))
      (not_isKReversible_threshold (by omega) (by omega))

/-- Odd-player majority `Cslib.majority (2 * m + 1)` (`m ≥ 1`, i.e., `n ≥ 3` odd) is `NCC`
([DodisRabin2007], Section 8.5.1, p. 199). -/
theorem isNCC_majority {m : ℕ} (hm : 1 ≤ m)
    {u : Fin (2 * m + 1) → (Fin (2 * m + 1) → Bool) → ℝ}
    {D : BitString (2 * m + 1) → ℝ} {fallback : Fin (2 * m + 1) → Bool → Bool}
    (hu : CorrectnessExclusivity u) (hD : IsMixedStrategy D)
    (hprio : HighCorrectnessPriority u D) :
    IsNCC (Cslib.majority (2 * m + 1)) u D fallback :=
  isKNCC_one_iff_isNCC.mp ((isKNCC_majority_iff hm hu hD hprio).mpr hm)

end BooleanWitnesses

end Cslib.GameTheory.RationalCrypto
