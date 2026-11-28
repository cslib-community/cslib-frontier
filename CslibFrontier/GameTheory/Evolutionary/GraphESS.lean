/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgeConcentration
public import CslibFrontier.GameTheory.Evolutionary.Basic
public import Mathlib.Probability.ProductMeasure
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.IsolatedVertices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evolutionary game theory over graphs

This module formalizes [Suri2007], Section 29.4 (pp. 728–733, originating in Kearns and Suri 2006)
and Exercise 29.7 (p. 736): evolutionary stability when organisms interact only with their
neighbors in an infinite family of finite undirected graphs `G : ∀ n, SimpleGraph (Fin n)`.

## Model and definitions

In a finite simple graph `G : SimpleGraph V` (loopless, matching [Suri2007], p. 729,
`Γ(u) = {v ∈ V : (u, v) ∈ E}`), if each vertex `u` plays a mixed strategy `strat u : α → ℝ` in a
two-player game `F : BimatrixGame α α`, the neighborhood fitness of `u` is
`F.graphFitness G strat u = (∑ v ∈ G.neighborFinset u, F.payoff₁ (strat u) (strat v)) / |Γ(u)|`
(taking value `0` when `u` is isolated).

* `BimatrixGame.survivingMutants`: mutants `j ∈ M` with no incumbent neighbor `i ∉ M` of strictly
  higher fitness.
* `BimatrixGame.Contracts`: a mutant family `M` contracts when the surviving fraction
  `|survivingMutants| / n` tends to `0` ([Suri2007], Definition 29.13, p. 729; applied to linear
  mutant families as enforced by `IsEpsLinear`).
* `BimatrixGame.IsEpsLinear`: `ε'`-linear mutant families `ε n < |M_n| < ε' n` eventually
  ([Suri2007], Definition 29.14, p. 730).
* `BimatrixGame.IsGraphESS`: graph-theoretic ESS for an infinite graph family
  ([Suri2007], Definition 29.15, p. 730).

## Main results

* **Complete-graph characterization and converse analysis** ([Suri2007], pp. 730, 732–733):
  `BimatrixGame.isGraphESS_complete_iff` gives the exact characterization of `IsGraphESS` on the
  loopless complete-graph family `{K_n}`: every classical ESS is a graph ESS on `{K_n}`
  (`IsESS.isGraphESS_complete`), every graph ESS on `{K_n}` is a symmetric Nash equilibrium
  (`IsGraphESS.isNash_of_complete`) and satisfies the classical ESS condition whenever no mutant
  ties both `F(t|s) = F(s|s)` and `F(t|t) = F(s|t)` (`IsGraphESS.isESS_of_complete`). On loopless
  `K_n`, however, the unguarded converse claimed on pp. 732–733 fails for constant-column games
  with `F(s|s) < F(s|t)` such as `!![0, 1; 0, 1]`, because excluding self-loops shifts each
  mutant's fitness below each incumbent's by `(F(s|t) - F(s|s)) / (n - 1)`
  (`exists_isGraphESS_complete_not_isESS`).
* **Unconditional uniform fitness concentration and Lemma 29.17** ([Suri2007], p. 731): proved
  unconditionally from `SimpleGraph.binomialRandom_real_exists_many_badDegree_le` simultaneously
  over all adversarial linear-size mutant sets `M`, both in an additive form for arbitrary real
  payoffs (`tendsto_binomialRandom_real_forall_abnormalFitness_additive_le`) and in the source's
  multiplicative `(1 ± τ)` form with the exact bound `24 log n / (τ ^ 2 p)` for strictly positive
  payoffs (`tendsto_binomialRandom_real_forall_abnormalFitness_mul_le`).
* **Unconditional Theorem 29.16** ([Suri2007], pp. 731–732):
  `BimatrixGame.binomialRandom_infinitePi_isGraphESS` proves that for any finite bimatrix game `F`
  (arbitrary real payoffs) and any classical ESS `s`, if `p n = Ω(1 / n ^ c)` with `c < 1`,
  then almost surely (`∀ᵐ`) under `Measure.infinitePi (fun n => G(Fin n, p n))`, `s` is a graph
  ESS with respect to `F` and `G` (for all mixed mutant strategies `t ≠ s` and all adversarial
  `ε_t`-linear mutant families simultaneously).
* **Exercise 29.7** ([Suri2007], p. 736): for the symmetric `2 × 2` positive-payoff game
  `survivorWitnessGame = !![3, 2; 3, 1]` with classical ESS `![1, 0]` and mutant `![0, 1]`:
  - `exists_game_adversarial_linear_mutant_beats_all_incumbent_neighbors`: for any
    `p n = Ω(1 / n ^ c)` (`c < 1`) bounded away from `1` (`∃ q < 1, ∀ᶠ n, p n ≤ q`), almost
    surely (`∀ᵐ`) an adversary can construct for every `ε' > 0` an `ε'`-linear mutant family
    containing a mutant with at least one incumbent neighbor and strictly higher fitness than all
    of its incumbent neighbors;
  - `exists_game_adversarial_mutant_beats_all_incumbent_neighbors`: without the linear-size
    constraint (e.g. a singleton mutant, cf. Vickery 1987, p. 734), the same holds with
    probability tending to `1` for all `p n = Ω(1 / n ^ c)` (`0 ≤ c < 1`), including `p n = 1`;
  - `IsESS.eventually_forall_graphFitness_lt_complete`: at `p = 1` (`K_n`), every mutant in any
    `ε_t`-linear mutant family eventually has strictly lower fitness than every incumbent, showing
    that bounding `p` away from `1` is necessary for linear-size mutant sets.

## References

* [S. Suri, *Computational Evolutionary Game Theory*, Section 29.4, pp. 728–733, and Exercise 29.7,
  p. 736][Suri2007] (citing M. Kearns and S. Suri, 2006, and B. Bollobás, 2001, Theorem 2.15)
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter Matrix SimpleGraph
open scoped Finset Topology ENNReal

namespace Cslib.GameTheory.BimatrixGame

variable {α : Type*} [Fintype α]

/-! ### Neighborhood fitness and graphical ESS definitions -/

/-- The neighborhood fitness of vertex `u` in a simple graph `G` when vertices play strategies
`strat : V → α → ℝ` in game `F` ([Suri2007], Section 29.4, p. 729):
`F(u) = (∑ v ∈ Γ(u), F(s_u | s_v)) / |Γ(u)|`, taking value `0` when `u` is isolated. -/
noncomputable def graphFitness {V : Type*} [Fintype V] (F : BimatrixGame α α)
    (G : SimpleGraph V) (strat : V → α → ℝ) (u : V) : ℝ :=
  open Classical in
  (∑ v ∈ G.neighborFinset u, F.payoff₁ (strat u) (strat v)) / (G.neighborFinset u).card

/-- Evaluation formula for `graphFitness` with any `Fintype (G.neighborSet u)` instance. -/
theorem graphFitness_eq {V : Type*} [Fintype V] (F : BimatrixGame α α) (G : SimpleGraph V)
    (strat : V → α → ℝ) (u : V) [Fintype (G.neighborSet u)] :
    F.graphFitness G strat u =
      (∑ v ∈ G.neighborFinset u, F.payoff₁ (strat u) (strat v)) / (G.neighborFinset u).card := by
  unfold graphFitness
  have hfin : ∀ (inst₁ inst₂ : Fintype (G.neighborSet u)),
      @SimpleGraph.neighborFinset V G u inst₁ = @SimpleGraph.neighborFinset V G u inst₂ := by
    intro _ _; ext v; simp [SimpleGraph.mem_neighborFinset]
  rw [hfin _ _]

/-- An isolated vertex has neighborhood fitness `0` (by `0 / 0 = 0`). -/
theorem graphFitness_eq_zero_of_isIsolated {V : Type*} [Fintype V] (F : BimatrixGame α α)
    (G : SimpleGraph V) (strat : V → α → ℝ) {u : V} (hu : G.IsIsolated u) :
    F.graphFitness G strat u = 0 := by
  have : Fintype (G.neighborSet u) := Fintype.ofFinite _
  rw [graphFitness_eq]
  have hempty : G.neighborFinset u = ∅ := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    exact hu v
  simp [hempty]

/-- The mutants in `M` that survive against all of their incumbent neighbors: `j ∈ M` has no
incumbent neighbor `i ∉ M` with strictly higher fitness. -/
noncomputable def survivingMutants {V : Type*} [Fintype V] (F : BimatrixGame α α)
    (G : SimpleGraph V) (M : Finset V) (s t : α → ℝ) : Finset V :=
  open Classical in
  M.filter fun j =>
    ∀ i, i ∉ M → G.Adj j i →
      F.graphFitness G (fun u => if u ∈ M then t else s) i ≤
        F.graphFitness G (fun u => if u ∈ M then t else s) j

/-- Membership characterization of `survivingMutants`: a mutant survives iff it has no incumbent
neighbor of strictly higher fitness. -/
theorem mem_survivingMutants_iff {V : Type*} [Fintype V] [DecidableEq V] (F : BimatrixGame α α)
    (G : SimpleGraph V) (M : Finset V) (s t : α → ℝ) {j : V} :
    j ∈ F.survivingMutants G M s t ↔
      j ∈ M ∧ ¬∃ i, i ∉ M ∧ G.Adj j i ∧
        F.graphFitness G (fun u => if u ∈ M then t else s) j <
          F.graphFitness G (fun u => if u ∈ M then t else s) i := by
  unfold survivingMutants
  simp only [Finset.mem_filter, not_exists, not_and, not_lt]
  refine and_congr_right fun _ => forall₂_congr fun _ _ => imp_congr_right fun _ => ?_
  convert Iff.rfl using 2 <;> congr 1 <;>
    exact funext fun u => by by_cases hu : u ∈ M <;> simp [hu]

/-- A family of mutant sets `M` *contracts* in the graph family `G` under incumbent strategy `s`
and mutant strategy `t` ([Suri2007], Definition 29.13, p. 729) when all but `o(n)` mutants have an
incumbent neighbor of strictly higher fitness, i.e., `|survivingMutants| / n → 0`.
The source applies this predicate to families with `|M_n| ≥ ε n`, as enforced by `IsEpsLinear` in
Definition 29.15. -/
def Contracts (F : BimatrixGame α α) (G : ∀ n, SimpleGraph (Fin n))
    (M : ∀ n, Finset (Fin n)) (s t : α → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((F.survivingMutants (G n) (M n) s t).card : ℝ) / (n : ℝ)) atTop (𝓝 0)

theorem contracts_iff (F : BimatrixGame α α) (G : ∀ n, SimpleGraph (Fin n))
    (M : ∀ n, Finset (Fin n)) (s t : α → ℝ) :
    F.Contracts G M s t ↔
      Tendsto (fun n : ℕ => ((F.survivingMutants (G n) (M n) s t).card : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
  Iff.rfl

/-- A family of mutant sets `M` is *`ε'`-linear* ([Suri2007], Definition 29.14, p. 730) if there
exists `0 < ε < ε'` such that `ε n < |M_n| < ε' n` for all sufficiently large `n`. -/
def IsEpsLinear (ε' : ℝ) (M : ∀ n, Finset (Fin n)) : Prop :=
  ∃ ε, 0 < ε ∧ ε < ε' ∧ ∀ᶠ n : ℕ in atTop, ε * (n : ℝ) < (M n).card ∧ ((M n).card : ℝ) < ε' * n

theorem isEpsLinear_iff (ε' : ℝ) (M : ∀ n, Finset (Fin n)) :
    IsEpsLinear ε' M ↔
      ∃ ε, 0 < ε ∧ ε < ε' ∧
        ∀ᶠ n : ℕ in atTop, ε * (n : ℝ) < (M n).card ∧ ((M n).card : ℝ) < ε' * n :=
  Iff.rfl

/-- A mixed strategy `s` is an *evolutionarily stable strategy with respect to `F` and `G`*
([Suri2007], Definition 29.15, p. 730) if for every other mixed strategy `t ≠ s` there exists
`ε_t > 0` such that every `ε_t`-linear mutant family `M` playing `t` contracts. -/
def IsGraphESS (F : BimatrixGame α α) (G : ∀ n, SimpleGraph (Fin n)) (s : α → ℝ) : Prop :=
  IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s →
    ∃ εt > 0, ∀ M, IsEpsLinear εt M → F.Contracts G M s t

theorem isGraphESS_iff (F : BimatrixGame α α) (G : ∀ n, SimpleGraph (Fin n)) (s : α → ℝ) :
    F.IsGraphESS G s ↔
      IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s →
        ∃ εt > 0, ∀ M, IsEpsLinear εt M → F.Contracts G M s t :=
  Iff.rfl

theorem IsGraphESS.isMixedStrategy {F : BimatrixGame α α} {G : ∀ n, SimpleGraph (Fin n)}
    {s : α → ℝ} (h : F.IsGraphESS G s) : IsMixedStrategy s :=
  h.1

/-! ### Two-strategy neighborhood fitness formulas -/

/-- Under a two-strategy assignment (`t` on `M`, `s` outside `M`), the neighborhood fitness of
`u` is the weighted average of its payoff against `s` and against `t` determined by its incumbent
and mutant neighbor counts. -/
private theorem graphFitness_twoStrategy {V : Type*} [Fintype V] [DecidableEq V]
    (F : BimatrixGame α α) (G : SimpleGraph V) (M : Finset V) (s t : α → ℝ) (u : V) :
    F.graphFitness G (fun v => if v ∈ M then t else s) u =
      ((((Mᶜ : Finset V) : Set V) ∩ G.neighborSet u).ncard *
          F.payoff₁ (if u ∈ M then t else s) s +
        (((M : Set V) ∩ G.neighborSet u).ncard : ℝ) *
          F.payoff₁ (if u ∈ M then t else s) t) /
      ((((Mᶜ : Finset V) : Set V) ∩ G.neighborSet u).ncard +
        (((M : Set V) ∩ G.neighborSet u).ncard : ℝ)) := by
  have : Fintype (G.neighborSet u) := Fintype.ofFinite _
  rw [graphFitness_eq]
  have hM : ((M : Set V) ∩ G.neighborSet u).ncard = #((G.neighborFinset u).filter (· ∈ M)) := by
    have hcoe : ((M : Set V) ∩ G.neighborSet u) =
        (((G.neighborFinset u).filter (· ∈ M) : Finset V) : Set V) := by
      ext v; simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hcoe, Set.ncard_coe_finset]
  have hI : (((Mᶜ : Finset V) : Set V) ∩ G.neighborSet u).ncard =
      #((G.neighborFinset u).filter (· ∉ M)) := by
    have hcoe : (((Mᶜ : Finset V) : Set V) ∩ G.neighborSet u) =
        (((G.neighborFinset u).filter (· ∉ M) : Finset V) : Set V) := by
      ext v; simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hcoe, Set.ncard_coe_finset]
  have hcard : #(G.neighborFinset u) =
      #((G.neighborFinset u).filter (· ∉ M)) + #((G.neighborFinset u).filter (· ∈ M)) := by
    have hunion : (G.neighborFinset u).filter (· ∉ M) ∪ (G.neighborFinset u).filter (· ∈ M) =
        G.neighborFinset u := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint ((G.neighborFinset u).filter (· ∉ M))
        ((G.neighborFinset u).filter (· ∈ M)) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
    conv_lhs => rw [← hunion]
    exact Finset.card_union_of_disjoint hdisj
  have hsum : ∑ v ∈ G.neighborFinset u,
      F.payoff₁ (if u ∈ M then t else s) (if v ∈ M then t else s) =
      (#((G.neighborFinset u).filter (· ∉ M)) : ℝ) * F.payoff₁ (if u ∈ M then t else s) s +
      (#((G.neighborFinset u).filter (· ∈ M)) : ℝ) * F.payoff₁ (if u ∈ M then t else s) t := by
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset u) (· ∈ M)]
    have h1 : ∑ v ∈ (G.neighborFinset u).filter (· ∈ M),
        F.payoff₁ (if u ∈ M then t else s) (if v ∈ M then t else s) =
        (#((G.neighborFinset u).filter (· ∈ M)) : ℝ) * F.payoff₁ (if u ∈ M then t else s) t := by
      calc ∑ v ∈ (G.neighborFinset u).filter (· ∈ M),
            F.payoff₁ (if u ∈ M then t else s) (if v ∈ M then t else s)
          = ∑ _v ∈ (G.neighborFinset u).filter (· ∈ M), F.payoff₁ (if u ∈ M then t else s) t :=
            Finset.sum_congr rfl fun v hv => by simp [(Finset.mem_filter.1 hv).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ v ∈ (G.neighborFinset u).filter (· ∉ M),
        F.payoff₁ (if u ∈ M then t else s) (if v ∈ M then t else s) =
        (#((G.neighborFinset u).filter (· ∉ M)) : ℝ) * F.payoff₁ (if u ∈ M then t else s) s := by
      calc ∑ v ∈ (G.neighborFinset u).filter (· ∉ M),
            F.payoff₁ (if u ∈ M then t else s) (if v ∈ M then t else s)
          = ∑ _v ∈ (G.neighborFinset u).filter (· ∉ M), F.payoff₁ (if u ∈ M then t else s) s :=
            Finset.sum_congr rfl fun v hv => by simp [(Finset.mem_filter.1 hv).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, add_comm]
  rw [hM, hI, hsum, hcard, Nat.cast_add]

/-- Pure algebra for two-strategy neighborhood fitness when `dI` and `dM` lie within `1 ± η`
of `mI > 0` and `mM > 0`: for `0 ≤ η ≤ 1 / 2`, the mutant fraction `dM / (dI + dM)` lies within
`η` of `mM / (mI + mM)`, giving additive error at most `η * |y - x|`; and for `0 ≤ η ≤ 1 / 3`
and `x, y > 0`, the ratio lies within `1 ± 3 * η` of the expected weighted average. -/
private theorem weighted_avg_bounds {dI dM mI mM η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hmI : 0 < mI) (hmM : 0 < mM)
    (hI : |dI - mI| ≤ η * mI) (hM : |dM - mM| ≤ η * mM) :
    (∀ x y : ℝ,
      |(dI * x + dM * y) / (dI + dM) -
          ((mI / (mI + mM)) * x + (mM / (mI + mM)) * y)| ≤ η * |y - x|) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → η ≤ 1 / 3 →
      (1 - 3 * η) * ((mI / (mI + mM)) * x + (mM / (mI + mM)) * y) ≤
          (dI * x + dM * y) / (dI + dM) ∧
        (dI * x + dM * y) / (dI + dM) ≤
          (1 + 3 * η) * ((mI / (mI + mM)) * x + (mM / (mI + mM)) * y)) := by
  obtain ⟨hI_lo, hI_hi⟩ := abs_le.1 hI
  obtain ⟨hM_lo, hM_hi⟩ := abs_le.1 hM
  have hI_ge : (1 - η) * mI ≤ dI := by linarith
  have hI_le : dI ≤ (1 + η) * mI := by linarith
  have hM_ge : (1 - η) * mM ≤ dM := by linarith
  have hM_le : dM ≤ (1 + η) * mM := by linarith
  have hsum_m : 0 < mI + mM := by linarith
  have hsum_ge : (1 - η) * (mI + mM) ≤ dI + dM := by linarith
  have hsum_le : dI + dM ≤ (1 + η) * (mI + mM) := by linarith
  have hsum_pos : 0 < dI + dM := lt_of_lt_of_le (mul_pos (by linarith) hsum_m) hsum_ge
  have hfrac : |dM / (dI + dM) - mM / (mI + mM)| ≤ η := by
    have hnum_hi : dM * (mI + mM) - mM * (dI + dM) ≤ 2 * η * (mI * mM) := by
      have : dM * (mI + mM) - mM * (dI + dM) = dM * mI - mM * dI := by ring
      rw [this]; nlinarith
    have hnum_lo : -(2 * η * (mI * mM)) ≤ dM * (mI + mM) - mM * (dI + dM) := by
      have : dM * (mI + mM) - mM * (dI + dM) = dM * mI - mM * dI := by ring
      rw [this]; nlinarith
    have hprod_le : 4 * (mI * mM) ≤ (mI + mM) ^ 2 := by nlinarith [sq_nonneg (mI - mM)]
    have hden_ge : 2 * (mI * mM) ≤ (dI + dM) * (mI + mM) := by
      have h1 : (1 - η) * (mI + mM) ^ 2 ≤ (dI + dM) * (mI + mM) := by nlinarith [hsum_ge]
      nlinarith [sq_nonneg (mI + mM)]
    have hdiff : dM / (dI + dM) - mM / (mI + mM) =
        (dM * (mI + mM) - mM * (dI + dM)) / ((dI + dM) * (mI + mM)) := by
      field_simp
    rw [hdiff, abs_div, abs_of_pos (mul_pos hsum_pos hsum_m), div_le_iff₀ (mul_pos hsum_pos hsum_m)]
    have habs : |dM * (mI + mM) - mM * (dI + dM)| ≤ 2 * η * (mI * mM) :=
      abs_le.2 ⟨hnum_lo, hnum_hi⟩
    nlinarith [hden_ge]
  refine ⟨fun x y => ?_, fun x y hx hy hη3 => ?_⟩
  · have hlin : (dI * x + dM * y) / (dI + dM) -
        ((mI / (mI + mM)) * x + (mM / (mI + mM)) * y) =
        (dM / (dI + dM) - mM / (mI + mM)) * (y - x) := by
      field_simp; ring
    rw [hlin, abs_mul]
    exact mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
  · set μ : ℝ := (mI / (mI + mM)) * x + (mM / (mI + mM)) * y
    have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
    have hμ_eq : mI * x + mM * y = (mI + mM) * μ := by dsimp only [μ]; field_simp
    have hnum_lo : (1 - η) * ((mI + mM) * μ) ≤ dI * x + dM * y := by rw [← hμ_eq]; nlinarith
    have hnum_hi : dI * x + dM * y ≤ (1 + η) * ((mI + mM) * μ) := by rw [← hμ_eq]; nlinarith
    have hprod_pos : 0 < (mI + mM) * μ := mul_pos hsum_m hμ_pos
    constructor
    · rw [le_div_iff₀ hsum_pos]
      have h1 : (1 - 3 * η) * μ * (dI + dM) ≤ (1 - 3 * η) * μ * ((1 + η) * (mI + mM)) :=
        mul_le_mul_of_nonneg_left hsum_le (mul_nonneg (by linarith) hμ_pos.le)
      have hfac : (1 - 3 * η) * (1 + η) ≤ 1 - η := by nlinarith
      nlinarith
    · rw [div_le_iff₀ hsum_pos]
      have h1 : (1 + 3 * η) * μ * ((1 - η) * (mI + mM)) ≤ (1 + 3 * η) * μ * (dI + dM) :=
        mul_le_mul_of_nonneg_left hsum_ge (by positivity)
      have hfac : 1 + η ≤ (1 + 3 * η) * (1 - η) := by nlinarith
      nlinarith

/-- Shared fitness-closeness helper for a vertex `u` whose degrees into `M` and `Mᶜ` are within
`1 ± η` of `#M * p` and `#Mᶜ * p` respectively. Used by both Lemma 29.17 and Theorem 29.16. -/
private theorem graphFitness_bounds_of_regular {n : ℕ} (F : BimatrixGame α α)
    (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (s t : α → ℝ) {p η : ℝ}
    (hp : 0 < p) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hM_pos : 0 < (#M : ℝ)) (hI_pos : 0 < (#Mᶜ : ℝ)) {u : Fin n}
    (huM : |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * p| ≤
      η * ((#M : ℝ) * p))
    (huI : |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) -
      (#Mᶜ : ℝ) * p| ≤ η * ((#Mᶜ : ℝ) * p)) :
    (u ∉ M →
      |F.graphFitness G (fun v => if v ∈ M then t else s) u -
        ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t)| ≤
        η * |F.payoff₁ s t - F.payoff₁ s s|) ∧
    (u ∈ M →
      |F.graphFitness G (fun v => if v ∈ M then t else s) u -
        ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t)| ≤
        η * |F.payoff₁ t t - F.payoff₁ t s|) ∧
    (η ≤ 1 / 3 → (∀ i j, 0 < F.A i j) → IsMixedStrategy s → IsMixedStrategy t →
      (u ∉ M →
        (1 - 3 * η) *
            ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t) ≤
          F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
        F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
          (1 + 3 * η) *
            ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t)) ∧
      (u ∈ M →
        (1 - 3 * η) *
            ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t) ≤
          F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
        F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
          (1 + 3 * η) *
            ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t))) := by
  have hsum_mc : (#Mᶜ : ℝ) + (#M : ℝ) = (n : ℝ) := by
    have hle : #M ≤ n := by simpa using Finset.card_le_univ M
    have hnat : #Mᶜ + #M = n := by rw [Finset.card_compl, Fintype.card_fin]; omega
    exact_mod_cast hnat
  have hn_pos : (0 : ℝ) < n := by linarith
  have hmM : 0 < (#M : ℝ) * p := mul_pos hM_pos hp
  have hmI : 0 < (#Mᶜ : ℝ) * p := mul_pos hI_pos hp
  have hden : (#Mᶜ : ℝ) * p + (#M : ℝ) * p = (n : ℝ) * p := by rw [← add_mul, hsum_mc]
  have hshareM : ((#M : ℝ) * p) / ((#Mᶜ : ℝ) * p + (#M : ℝ) * p) = (#M : ℝ) / (n : ℝ) := by
    rw [hden, mul_div_mul_right _ _ hp.ne']
  have hshareI : ((#Mᶜ : ℝ) * p) / ((#Mᶜ : ℝ) * p + (#M : ℝ) * p) = 1 - (#M : ℝ) / (n : ℝ) := by
    rw [hden, mul_div_mul_right _ _ hp.ne', show (#Mᶜ : ℝ) = (n : ℝ) - (#M : ℝ) by linarith]
    field_simp
  have hwa := weighted_avg_bounds hη0 hη hmI hmM huI huM
  have hfit := graphFitness_twoStrategy F G M s t u
  refine ⟨fun hum => ?_, fun hum => ?_, fun hη3 hA hs ht => ⟨fun hum => ?_, fun hum => ?_⟩⟩
  · simp only [hum, ↓reduceIte] at hfit
    have h := hwa.1 (F.payoff₁ s s) (F.payoff₁ s t)
    rwa [hshareI, hshareM, ← hfit] at h
  · simp only [hum, ↓reduceIte] at hfit
    have h := hwa.1 (F.payoff₁ t s) (F.payoff₁ t t)
    rwa [hshareI, hshareM, ← hfit] at h
  · simp only [hum, ↓reduceIte] at hfit
    have h := hwa.2 (F.payoff₁ s s) (F.payoff₁ s t)
      (F.payoff₁_pos hA hs hs) (F.payoff₁_pos hA hs ht) hη3
    rwa [hshareI, hshareM, ← hfit] at h
  · simp only [hum, ↓reduceIte] at hfit
    have h := hwa.2 (F.payoff₁ t s) (F.payoff₁ t t)
      (F.payoff₁_pos hA ht hs) (F.payoff₁_pos hA ht ht) hη3
    rwa [hshareI, hshareM, ← hfit] at h

/-! ### Complete-graph characterization and converse analysis -/

/-- Exact fitness difference between an incumbent and a mutant on the loopless complete graph
`K_n = ⊤`. -/
private theorem graphFitness_complete_diff (F : BimatrixGame α α) {n : ℕ} (M : Finset (Fin n))
    (s t : α → ℝ) {i j : Fin n} (hi : i ∉ M) (hj : j ∈ M) :
    ((n - 1 : ℕ) : ℝ) *
      (F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M then t else s) i -
        F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M then t else s) j) =
      ((n : ℝ) - (#M : ℝ)) * (F.payoff₁ s s - F.payoff₁ t s) +
        (#M : ℝ) * (F.payoff₁ s t - F.payoff₁ t t) +
        (F.payoff₁ t t - F.payoff₁ s s) := by
  have hm1 : 1 ≤ #M := Finset.card_pos.2 ⟨j, hj⟩
  have hmn : #M < n := by
    have hlt : #M < #(univ : Finset (Fin n)) := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ M, fun heq => hi (heq ▸ mem_univ i)⟩)
    simpa using hlt
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hneighbor (u : Fin n) :
      ((⊤ : SimpleGraph (Fin n)).neighborSet u) = ({u}ᶜ : Set (Fin n)) := by
    ext v; simp [ne_comm]
  have hMi : ((M : Set (Fin n)) ∩ (⊤ : SimpleGraph (Fin n)).neighborSet i).ncard = #M := by
    rw [hneighbor, show (M : Set (Fin n)) ∩ ({i}ᶜ : Set (Fin n)) = (M : Set (Fin n)) from
      Set.inter_eq_left.2 fun v hv hvi => hi (hvi ▸ hv), Set.ncard_coe_finset]
  have hIi : (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩
      (⊤ : SimpleGraph (Fin n)).neighborSet i).ncard = n - 1 - #M := by
    rw [hneighbor]
    have hcoe : (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ ({i}ᶜ : Set (Fin n))) =
        (((Mᶜ.erase i : Finset (Fin n)) : Set (Fin n))) := by
      ext v; simp [and_comm]
    rw [hcoe, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_compl.2 hi),
      Finset.card_compl, Fintype.card_fin]
    omega
  have hMj : ((M : Set (Fin n)) ∩ (⊤ : SimpleGraph (Fin n)).neighborSet j).ncard = #M - 1 := by
    rw [hneighbor]
    have hcoe : ((M : Set (Fin n)) ∩ ({j}ᶜ : Set (Fin n))) =
        (((M.erase j : Finset (Fin n)) : Set (Fin n))) := by
      ext v; simp [and_comm]
    rw [hcoe, Set.ncard_coe_finset, Finset.card_erase_of_mem hj]
  have hIj : (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩
      (⊤ : SimpleGraph (Fin n)).neighborSet j).ncard = n - #M := by
    rw [hneighbor]
    have hcoe : (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ ({j}ᶜ : Set (Fin n))) =
        ((Mᶜ : Finset (Fin n)) : Set (Fin n)) :=
      Set.inter_eq_left.2 fun v hv hvj => (Finset.mem_compl.1 hv) (hvj ▸ hj)
    rw [hcoe, Set.ncard_coe_finset, Finset.card_compl, Fintype.card_fin]
  have hfi := graphFitness_twoStrategy F (⊤ : SimpleGraph (Fin n)) M s t i
  have hfj := graphFitness_twoStrategy F (⊤ : SimpleGraph (Fin n)) M s t j
  simp only [hi, ↓reduceIte, hIi, hMi] at hfi
  simp only [hj, ↓reduceIte, hIj, hMj] at hfj
  have hden_i : ((n - 1 - #M : ℕ) : ℝ) + (#M : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    have : n - 1 - #M + #M = n - 1 := by omega
    exact_mod_cast this
  have hden_j : ((n - #M : ℕ) : ℝ) + ((#M - 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    have : n - #M + (#M - 1) = n - 1 := by omega
    exact_mod_cast this
  rw [hfi, hfj, hden_i, hden_j, ← sub_div, mul_div_cancel₀ _ hn1_pos.ne']
  rw [Nat.cast_sub (by omega : #M ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : #M ≤ n), Nat.cast_sub hm1, Nat.cast_one]
  ring

/-- Helper: under the three-branch complete-graph payoff condition, there exists `0 < εt ≤ 1/2`
such that for every `εt`-linear mutant family `M`, eventually every mutant in `K_n` has strictly
lower fitness than every incumbent. -/
private theorem contracts_complete_of_payoff_cond (F : BimatrixGame α α) {s t : α → ℝ}
    (hcond : F.payoff₁ t s < F.payoff₁ s s ∨
      F.payoff₁ t s = F.payoff₁ s s ∧
        (F.payoff₁ t t < F.payoff₁ s t ∨
          F.payoff₁ t t = F.payoff₁ s t ∧ F.payoff₁ s s < F.payoff₁ s t)) :
    ∃ εt > 0, εt ≤ 1 / 2 ∧ ∀ M, IsEpsLinear εt M →
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ M n, ∀ i, i ∉ M n →
        F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j <
          F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i := by
  set a := F.payoff₁ s s
  set b := F.payoff₁ s t
  set c := F.payoff₁ t s
  set d := F.payoff₁ t t
  have hstep : ∀ εt > 0, εt ≤ 1 / 2 →
      (∀ M, IsEpsLinear εt M →
        ∀ᶠ n : ℕ in atTop,
          0 < ((n : ℝ) - (#(M n) : ℝ)) * (a - c) + (#(M n) : ℝ) * (b - d) + (d - a)) →
      ∃ εt > 0, εt ≤ 1 / 2 ∧ ∀ M, IsEpsLinear εt M →
        ∀ᶠ n : ℕ in atTop, ∀ j ∈ M n, ∀ i, i ∉ M n →
          F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j <
            F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i := by
    intro εt hεt hεt_half hpos
    refine ⟨εt, hεt, hεt_half, fun M hM => ?_⟩
    filter_upwards [hpos M hM, eventually_ge_atTop 2] with n hnum hn2 j hj i hi
    have hdiff := graphFitness_complete_diff F (M n) s t hi hj
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hprod : 0 < ((n - 1 : ℕ) : ℝ) *
        (F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i -
          F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j) := by
      rw [hdiff]; exact hnum
    have hsub : 0 < F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i -
        F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j :=
      pos_of_mul_pos_right hprod hn1_pos.le
    linarith
  rcases hcond with hlt | ⟨heq, hlt | ⟨heq2, hlt2⟩⟩
  · have hden : 0 < 2 * (|b - d| + (a - c) + 1) := by linarith [abs_nonneg (b - d)]
    let εt := min (1 / 2 : ℝ) ((a - c) / (2 * (|b - d| + (a - c) + 1)))
    have hεt : 0 < εt := lt_min (by norm_num) (div_pos (sub_pos.2 hlt) hden)
    refine hstep εt hεt (min_le_left _ _) fun M ⟨_, _, _, hM⟩ => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * |d - a| / (a - c) + 1)
    filter_upwards [hM, eventually_ge_atTop N] with n ⟨_, hhi⟩ hnN
    have hn_ge : 4 * |d - a| / (a - c) + 1 ≤ (n : ℝ) := le_trans hN.le (by exact_mod_cast hnN)
    have hn_pos : (0 : ℝ) < n := by
      have : 0 ≤ 4 * |d - a| / (a - c) := div_nonneg (by positivity) (sub_pos.2 hlt).le
      linarith
    have hεt1 : εt ≤ 1 / 2 := min_le_left _ _
    have hεt2 : εt ≤ (a - c) / (2 * (|b - d| + (a - c) + 1)) := min_le_right _ _
    have hm_le1 : (#(M n) : ℝ) ≤ (1 / 2) * (n : ℝ) := by nlinarith
    have hm_le2 : (#(M n) : ℝ) * (2 * (|b - d| + (a - c) + 1)) ≤ (a - c) * (n : ℝ) := by
      have h1 : εt * (2 * (|b - d| + (a - c) + 1)) ≤ a - c := (le_div_iff₀ hden).1 hεt2
      nlinarith
    have hbd : -((#(M n) : ℝ) * |b - d|) ≤ (#(M n) : ℝ) * (b - d) := by
      linarith [mul_le_mul_of_nonneg_left (neg_abs_le (b - d)) (Nat.cast_nonneg (#(M n)))]
    have hmain : (1 / 4) * (a - c) * (n : ℝ) ≤
        ((n : ℝ) - (#(M n) : ℝ)) * (a - c) + (#(M n) : ℝ) * (b - d) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (#(M n))]
    have hda : |d - a| < (1 / 4) * (a - c) * (n : ℝ) := by
      have h1 : 4 * |d - a| / (a - c) < (n : ℝ) := by linarith
      have h2 := (div_lt_iff₀ (sub_pos.2 hlt)).1 h1
      linarith
    linarith [neg_abs_le (d - a)]
  · refine hstep (1 / 2) (by norm_num) le_rfl fun M ⟨ε, hε0, _, hM⟩ => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (|d - a| / (ε * (b - d)) + 1)
    filter_upwards [hM, eventually_ge_atTop N] with n ⟨hlo, _⟩ hnN
    have hn_ge : |d - a| / (ε * (b - d)) < (n : ℝ) :=
      lt_of_lt_of_le (by linarith) (le_trans hN.le (by exact_mod_cast hnN))
    have hmul : |d - a| < ε * (b - d) * (n : ℝ) := by
      have hpos : 0 < ε * (b - d) := mul_pos hε0 (sub_pos.2 hlt)
      linarith [(div_lt_iff₀ hpos).1 hn_ge]
    have h1 : ε * (b - d) * (n : ℝ) < (#(M n) : ℝ) * (b - d) := by
      have := mul_lt_mul_of_pos_right hlo (sub_pos.2 hlt)
      linarith
    have h2 : a - c = 0 := by linarith
    rw [h2, mul_zero, zero_add]
    linarith [neg_abs_le (d - a)]
  · refine hstep (1 / 2) (by norm_num) le_rfl fun M _ => Eventually.of_forall fun _ => ?_
    have h1 : a - c = 0 := by linarith
    have h2 : b - d = 0 := by linarith
    rw [h1, h2, mul_zero, mul_zero, add_zero, zero_add]
    linarith

/-- **Exact characterization of `IsGraphESS` on the loopless complete-graph family `{K_n}`**
([Suri2007], pp. 730, 732–733): a mixed strategy `s` is a graph ESS on `fun _ => ⊤` iff for every
mixed strategy `t ≠ s`, either `F(t|s) < F(s|s)`, or `F(t|s) = F(s|s)` and `F(t|t) < F(s|t)`, or
`F(t|s) = F(s|s)`, `F(t|t) = F(s|t)`, and `F(s|s) < F(s|t)`.

The third branch is an artifact of loopless `K_n`: when `F(t|s) = F(s|s)` and `F(t|t) = F(s|t)`,
each mutant has one fewer mutant neighbor than each incumbent, shifting its fitness below each
incumbent's by `(F(s|t) - F(s|s)) / (n - 1)`. -/
theorem isGraphESS_complete_iff (F : BimatrixGame α α) (s : α → ℝ) :
    F.IsGraphESS (fun _ => ⊤) s ↔
      IsMixedStrategy s ∧ ∀ t, IsMixedStrategy t → t ≠ s →
        F.payoff₁ t s < F.payoff₁ s s ∨
          F.payoff₁ t s = F.payoff₁ s s ∧
            (F.payoff₁ t t < F.payoff₁ s t ∨
              F.payoff₁ t t = F.payoff₁ s t ∧ F.payoff₁ s s < F.payoff₁ s t) := by
  constructor
  · rintro ⟨hs, hgraph⟩
    refine ⟨hs, fun t ht hne => ?_⟩
    obtain ⟨εt, hεt, hcontract⟩ := hgraph t ht hne
    set a := F.payoff₁ s s
    set b := F.payoff₁ s t
    set c := F.payoff₁ t s
    set d := F.payoff₁ t t
    have htheta : ∀ θ, 0 < θ → θ < min (εt / 2) (1 / 2) →
        ∀ᶠ n : ℕ in atTop,
          0 < ((n : ℝ) - (⌊θ * (n : ℝ)⌋₊ : ℝ)) * (a - c) +
            (⌊θ * (n : ℝ)⌋₊ : ℝ) * (b - d) + (d - a) := by
      intro θ hθ0 hθ1
      have hθ_lt_half : θ < 1 / 2 := lt_of_lt_of_le hθ1 (min_le_right _ _)
      have hθ_lt_εt : θ < εt := lt_of_lt_of_le hθ1 ((min_le_left _ _).trans (by linarith))
      let M : ∀ n, Finset (Fin n) := fun n =>
        (univ : Finset (Fin n)).filter fun i => i.val < ⌊θ * (n : ℝ)⌋₊
      have hM_card : ∀ n, #(M n) = ⌊θ * (n : ℝ)⌋₊ := by
        intro n
        have hle : ⌊θ * (n : ℝ)⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith)
        have hbij : #(M n) = #(Finset.range ⌊θ * (n : ℝ)⌋₊) := by
          refine Finset.card_bij (fun i _ => i.val) (fun i hi => ?_) (fun _ _ _ _ h => Fin.ext h)
            (fun k hk => ?_)
          · exact Finset.mem_range.2 (Finset.mem_filter.1 hi).2
          · have hk' : k < ⌊θ * (n : ℝ)⌋₊ := Finset.mem_range.1 hk
            exact ⟨⟨k, lt_of_lt_of_le hk' hle⟩, Finset.mem_filter.2 ⟨mem_univ _, hk'⟩, rfl⟩
        rw [hbij, Finset.card_range]
      have hM_lin : IsEpsLinear εt M := by
        refine ⟨θ / 2, by linarith, by linarith, ?_⟩
        obtain ⟨N, hN⟩ := exists_nat_gt (2 / θ + 1)
        filter_upwards [eventually_ge_atTop N] with n hnN
        have hn_gt : 2 / θ < (n : ℝ) := lt_of_lt_of_le (by linarith)
          (le_trans hN.le (by exact_mod_cast hnN))
        have hθn : 2 < θ * (n : ℝ) := by linarith [(div_lt_iff₀ hθ0).1 hn_gt]
        rw [hM_card]
        constructor
        · have hlt := Nat.lt_floor_add_one (θ * (n : ℝ))
          linarith
        · have hle : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (by positivity)
          nlinarith
      have hcon := hcontract M hM_lin
      have hsmall : ∀ᶠ n : ℕ in atTop,
          ((F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t).card : ℝ) / (n : ℝ) < θ / 2 :=
        hcon.eventually (gt_mem_nhds (by linarith))
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / θ + 2)
      filter_upwards [hsmall, eventually_ge_atTop N] with n hsn hnN
      have hn_gt : 2 / θ + 1 < (n : ℝ) := lt_of_lt_of_le (by linarith)
        (le_trans hN.le (by exact_mod_cast hnN))
      have hn_pos : (0 : ℝ) < n := by
        have : 0 < 2 / θ := by positivity
        linarith
      have hθn : 2 < θ * (n : ℝ) := by
        have : 2 / θ < (n : ℝ) := by linarith
        linarith [(div_lt_iff₀ hθ0).1 this]
      have hM_gt : (θ / 2) * (n : ℝ) < (#(M n) : ℝ) := by
        rw [hM_card]
        have := Nat.lt_floor_add_one (θ * (n : ℝ))
        linarith
      have hS_lt : ((F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t).card : ℝ) <
          (#(M n) : ℝ) := by
        have h1 := (div_lt_iff₀ hn_pos).1 hsn
        linarith
      have hS_lt_nat : #(F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t) < #(M n) := by
        exact_mod_cast hS_lt
      have hsub : F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t ⊂ M n :=
        Finset.ssubset_iff_subset_ne.2
          ⟨fun j hj => (mem_survivingMutants_iff F ⊤ (M n) s t).1 hj |>.1,
            fun heq => lt_irrefl _ (heq ▸ hS_lt_nat)⟩
      obtain ⟨j, hjM, hjS⟩ := Finset.exists_of_ssubset hsub
      rw [mem_survivingMutants_iff, not_and, not_not] at hjS
      obtain ⟨i, hiM, _, hlt_fit⟩ := hjS hjM
      have hdiff := graphFitness_complete_diff F (M n) s t hiM hjM
      have hn2 : 2 ≤ n := by
        have : (1 : ℝ) < n := by
          have : 0 < 2 / θ := by positivity
          linarith
        exact_mod_cast this
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
      have hprod : 0 < ((n - 1 : ℕ) : ℝ) *
          (F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i -
            F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j) :=
        mul_pos hn1_pos (sub_pos.2 hlt_fit)
      rw [hdiff, hM_card] at hprod
      exact hprod
    have hca : c ≤ a := by
      by_contra! hlt_ca
      let θ := min (min (εt / 4) (1 / 4)) ((c - a) / (2 * (|b - d| + (c - a) + 1)))
      have hden : 0 < 2 * (|b - d| + (c - a) + 1) := by linarith [abs_nonneg (b - d)]
      have hθ0 : 0 < θ :=
        lt_min (lt_min (by linarith) (by norm_num)) (div_pos (sub_pos.2 hlt_ca) hden)
      have hθ1 : θ < min (εt / 2) (1 / 2) := lt_of_le_of_lt (min_le_left _ _)
        (lt_min (lt_of_le_of_lt (min_le_left _ _) (by linarith))
          (lt_of_le_of_lt (min_le_right _ _) (by norm_num)))
      have hθ_bd : θ * (2 * (|b - d| + (c - a) + 1)) ≤ c - a :=
        (le_div_iff₀ hden).1 (min_le_right _ _)
      have hθ_half : θ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
      obtain ⟨N, hN⟩ := exists_nat_gt (4 * |d - a| / (c - a) + 1)
      obtain ⟨n, hpos, hnN⟩ := ((htheta θ hθ0 hθ1).and (eventually_ge_atTop N)).exists
      have hn_gt : 4 * |d - a| / (c - a) < (n : ℝ) :=
        lt_of_lt_of_le (by linarith) (le_trans hN.le (by exact_mod_cast hnN))
      have hfl_le : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (by positivity)
      have hfl_q : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ (1 / 4) * (n : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hbd : (⌊θ * (n : ℝ)⌋₊ : ℝ) * (b - d) ≤ (⌊θ * (n : ℝ)⌋₊ : ℝ) * |b - d| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)
      have h1 : (⌊θ * (n : ℝ)⌋₊ : ℝ) * |b - d| ≤ (1 / 2) * (c - a) * (n : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hda : 4 * |d - a| < (c - a) * (n : ℝ) := by
        linarith [(div_lt_iff₀ (sub_pos.2 hlt_ca)).1 hn_gt]
      have h2 : (1 / 2) * (c - a) * (n : ℝ) + |d - a| ≤
          ((n : ℝ) - (⌊θ * (n : ℝ)⌋₊ : ℝ)) * (c - a) := by
        nlinarith [show (0 : ℝ) ≤ c - a by linarith]
      linarith [le_abs_self (d - a)]
    rcases hca.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      let θ := min (εt / 4) (1 / 4)
      have hθ0 : 0 < θ := lt_min (by linarith) (by norm_num)
      have hθ1 : θ < min (εt / 2) (1 / 2) :=
        lt_min (lt_of_le_of_lt (min_le_left _ _) (by linarith))
          (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
      have hev := htheta θ hθ0 hθ1
      have hdb : d ≤ b := by
        by_contra! hlt_db
        obtain ⟨N, hN⟩ := exists_nat_gt ((|d - a| / (d - b) + 2) / θ + 2)
        obtain ⟨n, hpos, hnN⟩ := (hev.and (eventually_ge_atTop N)).exists
        have h1 : a - c = 0 := by linarith
        rw [h1, mul_zero, zero_add] at hpos
        have hn_gt : (|d - a| / (d - b) + 2) / θ < (n : ℝ) :=
          lt_of_lt_of_le (by linarith) (le_trans hN.le (by exact_mod_cast hnN))
        have hθn : |d - a| / (d - b) + 2 < θ * (n : ℝ) := by
          linarith [(div_lt_iff₀ hθ0).1 hn_gt]
        have hfl_gt : |d - a| / (d - b) < (⌊θ * (n : ℝ)⌋₊ : ℝ) := by
          have := Nat.lt_floor_add_one (θ * (n : ℝ))
          linarith
        have hmul : |d - a| < (⌊θ * (n : ℝ)⌋₊ : ℝ) * (d - b) := by
          linarith [(div_lt_iff₀ (sub_pos.2 hlt_db)).1 hfl_gt]
        linarith [le_abs_self (d - a)]
      rcases hdb.lt_or_eq with hlt_db | heq_db
      · exact Or.inl hlt_db
      · refine Or.inr ⟨heq_db, ?_⟩
        obtain ⟨n, hpos⟩ := hev.exists
        have h1 : a - c = 0 := by linarith
        have h2 : b - d = 0 := by linarith
        rw [h1, h2, mul_zero, mul_zero, add_zero, zero_add] at hpos
        linarith
  · rintro ⟨hs, hcond⟩
    refine ⟨hs, fun t ht hne => ?_⟩
    obtain ⟨εt, hεt, hεt_half, hdom⟩ := contracts_complete_of_payoff_cond F (hcond t ht hne)
    refine ⟨εt, hεt, fun M hM => ?_⟩
    have ⟨_, _, _, hMev⟩ := hM
    have hzero : ∀ᶠ n : ℕ in atTop,
        ((F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t).card : ℝ) / (n : ℝ) = 0 := by
      filter_upwards [hdom M hM, hMev, eventually_ge_atTop 2] with n hlt ⟨_, hhi⟩ hn2
      have hcard_lt : #(M n) < n := by
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hlt_r : (#(M n) : ℝ) < (n : ℝ) := by nlinarith
        exact_mod_cast hlt_r
      have hinc : ∃ i : Fin n, i ∉ M n := by
        by_contra! hall
        have : M n = univ := Finset.eq_univ_iff_forall.2 hall
        rw [this, Finset.card_univ, Fintype.card_fin] at hcard_lt
        exact lt_irrefl _ hcard_lt
      obtain ⟨i, hiM⟩ := hinc
      have hempty : F.survivingMutants (⊤ : SimpleGraph (Fin n)) (M n) s t = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        rw [mem_survivingMutants_iff] at hj
        have hij : j ≠ i := fun heq => hiM (heq ▸ hj.1)
        exact hj.2 ⟨i, hiM, hij, hlt j hj.1 i hiM⟩
      simp [hempty]
    exact tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)

/-! ### Complete-graph corollaries and counterexample to unguarded converse -/

/-- Every classical ESS is a graph ESS on the complete-graph family `{K_n}` ([Suri2007],
Section 29.4, p. 730). -/
theorem IsESS.isGraphESS_complete {F : BimatrixGame α α} {s : α → ℝ} (hs : F.IsESS s) :
    F.IsGraphESS (fun _ => ⊤) s := by
  rw [isESS_iff_forall_lt_or] at hs
  rw [isGraphESS_complete_iff]
  exact ⟨hs.1, fun t ht hne => (hs.2 t ht hne).imp_right fun ⟨heq, hlt⟩ => ⟨heq, Or.inl hlt⟩⟩

/-- Every graph ESS on the complete-graph family `{K_n}` is a symmetric Nash equilibrium of any
symmetric game `F`. -/
theorem IsGraphESS.isNash_of_complete {F : BimatrixGame α α} (hF : F.B = F.Aᵀ) {s : α → ℝ}
    (hs : F.IsGraphESS (fun _ => ⊤) s) : F.IsNash s s := by
  classical
  rw [isGraphESS_complete_iff] at hs
  rcases F with ⟨A, B⟩
  obtain rfl : B = Aᵀ := hF
  have hbr : ({ A := A, B := Aᵀ } : BimatrixGame α α).IsBestResponse₁ s s := by
    rw [isBestResponse₁_iff_le_payoff₁]
    refine ⟨hs.1, fun i => ?_⟩
    let pi : α → ℝ := Pi.single i 1
    have hpi : IsMixedStrategy pi := isMixedStrategy_single i
    have hpay : ({ A := A, B := Aᵀ } : BimatrixGame α α).payoff₁ pi s = (A *ᵥ s) i := by
      simp [payoff₁_eq_dotProduct, pi]
    rw [← hpay]
    rcases eq_or_ne pi s with rfl | hne
    · exact le_rfl
    · rcases hs.2 pi hpi hne with hlt | ⟨heq, _⟩
      · exact hlt.le
      · exact heq.le
  simp only [isNash_iff, ← isBestResponse₁_swap, swap_mk, transpose_transpose, and_self]
  exact hbr

/-- **Conditional converse to Theorem 29.16 on loopless `{K_n}`** ([Suri2007], pp. 732–733): a
graph ESS on `{K_n}` is a classical ESS whenever no mutant `t ≠ s` ties both `F(t|s) = F(s|s)`
and `F(t|t) = F(s|t)` with `F(s|s) < F(s|t)`. -/
theorem IsGraphESS.isESS_of_complete {F : BimatrixGame α α} {s : α → ℝ}
    (hs : F.IsGraphESS (fun _ => ⊤) s)
    (hnotie : ∀ t, IsMixedStrategy t → t ≠ s →
      F.payoff₁ t s = F.payoff₁ s s → F.payoff₁ t t = F.payoff₁ s t →
        F.payoff₁ s t ≤ F.payoff₁ s s) :
    F.IsESS s := by
  rw [isGraphESS_complete_iff] at hs
  rw [isESS_iff_forall_lt_or]
  refine ⟨hs.1, fun t ht hne => ?_⟩
  rcases hs.2 t ht hne with hlt | ⟨heq, hlt | ⟨heq2, hlt2⟩⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hlt⟩
  · exact absurd hlt2 (not_lt.2 (hnotie t ht hne heq heq2))

/-- **Counterexample to the unguarded loopless converse on `{K_n}`**: in the symmetric `2 × 2`
constant-column game `!![0, 1; 0, 1]`, pure strategy `![1, 0]` is a graph ESS on `{K_n}` under
Definition 29.15 (because excluding self-loops lowers every mutant's fitness by `q / (n - 1)`
below every incumbent's), yet is not a classical ESS (indeed the game has no classical ESS). -/
theorem exists_isGraphESS_complete_not_isESS :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsGraphESS (fun _ => ⊤) s ∧ ¬F.IsESS s := by
  let F : BimatrixGame (Fin 2) (Fin 2) := ⟨!![0, 1; 0, 1], !![0, 1; 0, 1]ᵀ⟩
  let s : Fin 2 → ℝ := ![1, 0]
  refine ⟨F, s, rfl, ?_, ?_⟩
  · rw [isGraphESS_complete_iff]
    have hs : IsMixedStrategy s :=
      isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> norm_num [s],
        by simp [s, Fin.sum_univ_two]⟩
    refine ⟨hs, fun t ht hne => ?_⟩
    have ht1 : 0 < t 1 := by
      have hnn := ht.nonneg 1
      rcases hnn.lt_or_eq with hpos | h0
      · exact hpos
      · exfalso
        have hsum := ht.sum_eq_one
        rw [Fin.sum_univ_two, ← h0, add_zero] at hsum
        apply hne
        ext i
        fin_cases i
        · simpa [s] using hsum
        · simpa [s] using h0.symm
    have hpay : ∀ x, IsMixedStrategy x → ∀ y, F.payoff₁ x y = y 1 := by
      intro x hx y
      have hsum := hx.sum_eq_one
      rw [Fin.sum_univ_two] at hsum
      simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, F, Fin.sum_univ_two, of_apply,
        cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination y 1 * hsum
    rw [hpay t ht s, hpay s hs s, hpay t ht t, hpay s hs t]
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, by simpa [s] using ht1⟩⟩
  · intro hess
    have hno : ¬∃ u, F.IsESS u := by
      rw [exists_isESS_fin_two_iff]
      norm_num [F]
    exact hno ⟨s, hess⟩

/-- **Boundary witness for Exercise 29.7 at `p = 1` (`K_n`)**: for any classical ESS `s` and
mutant strategy `t ≠ s`, there is a threshold `εt > 0` such that for every `εt`-linear mutant
family `M`, eventually every mutant in `K_n` has strictly lower fitness than every incumbent. -/
theorem IsESS.eventually_forall_graphFitness_lt_complete {F : BimatrixGame α α} {s : α → ℝ}
    (hs : F.IsESS s) {t : α → ℝ} (ht : IsMixedStrategy t) (hne : t ≠ s) :
    ∃ εt > 0, ∀ M, IsEpsLinear εt M →
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ M n, ∀ i, i ∉ M n →
        F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) j <
          F.graphFitness (⊤ : SimpleGraph (Fin n)) (fun u => if u ∈ M n then t else s) i := by
  have hcond := (isESS_iff_forall_lt_or.1 hs).2 t ht hne
  obtain ⟨εt, hεt, _, hdom⟩ := contracts_complete_of_payoff_cond F
    (hcond.imp_right fun ⟨heq, hlt⟩ => ⟨heq, Or.inl hlt⟩)
  exact ⟨εt, hεt, hdom⟩

/-! ### Asymptotics and Borel–Cantelli helpers for `p n = Ω(1 / n ^ c)` -/

/-- General Borel–Cantelli helper on `Measure.infinitePi (fun n => G(Fin n, p n))`: whenever the
real failure probabilities `G(Fin n, p n).real (B n)` are summable, almost every graph family
eventually avoids `B n`. -/
private theorem ae_eventually_notMem_infinitePi_of_summable {p : ℕ → I}
    (B : ∀ n : ℕ, Set (SimpleGraph (Fin n)))
    (hsum : Summable fun n : ℕ => G(Fin n, p n).real (B n)) :
    ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)), ∀ᶠ n : ℕ in atTop, G n ∉ B n := by
  let μ := Measure.infinitePi fun n : ℕ => G(Fin n, p n)
  let E : ℕ → Set (∀ n : ℕ, SimpleGraph (Fin n)) := fun n => (fun G => G n) ⁻¹' B n
  have hmeas (n : ℕ) : μ (E n) = ENNReal.ofReal (G(Fin n, p n).real (B n)) := by
    have hmp := measurePreserving_eval_infinitePi (fun k : ℕ => G(Fin k, p k)) n
    rw [hmp.measure_preimage (MeasurableSet.of_discrete.nullMeasurableSet), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have htsum_ne_top : (∑' n : ℕ, μ (E n)) ≠ ⊤ := by
    simp_rw [hmeas]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [MeasureTheory.ae_finite_setOfPred_mem htsum_ne_top] with G hfin
  rcases hfin.bddAbove with ⟨N, hN⟩
  filter_upwards [eventually_gt_atTop N] with n hn hmem
  exact not_lt_of_ge (hN hmem) hn

/-- Specialization of `ae_eventually_notMem_infinitePi_of_summable` to exponential tails
`K * exp (-n)`. -/
private theorem ae_eventually_notMem_infinitePi_of_exp_neg {p : ℕ → I}
    (B : ∀ n : ℕ, Set (SimpleGraph (Fin n))) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᶠ n : ℕ in atTop, G(Fin n, p n).real (B n) ≤ K * Real.exp (-(n : ℝ))) :
    ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)), ∀ᶠ n : ℕ in atTop, G n ∉ B n := by
  refine ae_eventually_notMem_infinitePi_of_summable B ?_
  have hgeom : Summable fun n : ℕ => K * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left K
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  filter_upwards [hbound] with n hn
  rw [Real.norm_of_nonneg measureReal_nonneg]
  exact hn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_half_pow n le_rfl) hK)

/-- For `α > 0`, `Real.log n / n ^ α → 0` as `n → ∞`. -/
private theorem tendsto_log_div_rpow_nat {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ α) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- When `p n = Ω(1 / n ^ c)` with `c < 1`, `p n > 0` eventually and `log n / (n * p n) → 0`,
and `k n = ⌈log n / p n⌉₊` satisfies `log n ≤ k n * p n` and `k n / n → 0`. -/
private theorem dense_p_kCeil_props {p : ℕ → I} {c : ℝ} (hc1 : c < 1)
    (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) :
    (∀ᶠ n : ℕ in atTop, 0 < (p n : ℝ)) ∧
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ))) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, 1 * Real.log (n : ℝ) ≤ (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) * (p n : ℝ)) ∧
    Tendsto (fun n : ℕ => (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨a, ha, hp_ev⟩ := hp
  have h1c : 0 < 1 - c := sub_pos.2 hc1
  have hp_pos : ∀ᶠ n : ℕ in atTop, 0 < (p n : ℝ) := by
    filter_upwards [hp_ev, eventually_ge_atTop 1] with n hpn hn
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact lt_of_lt_of_le (by positivity) hpn
  have hlog_p : Tendsto (fun n : ℕ => Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (1 / a) * (Real.log (n : ℝ) / (n : ℝ) ^ (1 - c)))
        atTop (𝓝 0) := by
      simpa using (tendsto_log_div_rpow_nat h1c).const_mul (1 / a)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hp0 : (0 : ℝ) ≤ p n := unitInterval.nonneg (p n)
      positivity
    · filter_upwards [hp_ev, eventually_ge_atTop 1] with n hpn hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hnp : a * (n : ℝ) ^ (1 - c) ≤ (n : ℝ) * (p n : ℝ) := by
        have hrpow : (n : ℝ) * ((n : ℝ) ^ c)⁻¹ = (n : ℝ) ^ (1 - c) := by
          rw [Real.rpow_sub hn_pos, Real.rpow_one, div_eq_mul_inv]
        have hmul := mul_le_mul_of_nonneg_left hpn hn_pos.le
        calc a * (n : ℝ) ^ (1 - c) = (n : ℝ) * (a / (n : ℝ) ^ c) := by
              rw [div_eq_mul_inv, ← hrpow]; ring
          _ ≤ (n : ℝ) * (p n : ℝ) := hmul
      have hpos1 : 0 < a * (n : ℝ) ^ (1 - c) := by positivity
      calc Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ))
          ≤ Real.log (n : ℝ) / (a * (n : ℝ) ^ (1 - c)) :=
            div_le_div_of_nonneg_left hlog hpos1 hnp
        _ = (1 / a) * (Real.log (n : ℝ) / (n : ℝ) ^ (1 - c)) := by field_simp
  have hk_lo : ∀ᶠ n : ℕ in atTop,
      1 * Real.log (n : ℝ) ≤ (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) * (p n : ℝ) := by
    filter_upwards [hp_pos] with n hpn
    simpa only [one_mul] using (div_le_iff₀ hpn).1 (Nat.le_ceil (Real.log (n : ℝ) / (p n : ℝ)))
  have hk_small : Tendsto (fun n : ℕ => (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ)) + 1 / (n : ℝ))
        atTop (𝓝 0) := by
      simpa using hlog_p.add tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => by positivity) ?_
    filter_upwards [hp_pos, eventually_ge_atTop 1] with n hpn hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hceil : (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) ≤ Real.log (n : ℝ) / (p n : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hlog hpn.le)).le
    calc (⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ : ℝ) / (n : ℝ)
        ≤ (Real.log (n : ℝ) / (p n : ℝ) + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right hceil hn_pos.le
      _ = Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ)) + 1 / (n : ℝ) := by field_simp
  exact ⟨hp_pos, hlog_p, hk_lo, hk_small⟩

private theorem tendsto_div_nat_zero_of_eventually_le {k : ℕ → ℕ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hle : ∀ᶠ n : ℕ in atTop, (k n : ℝ) / (n : ℝ) ≤ u n) :
    Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => by positivity) hle

private theorem mul_rpow_one_sub_le_mul_p {n m : ℕ} {a c d p : ℝ} (hn : (0 : ℝ) < n)
    (ha : 0 ≤ a) (hm : (n : ℝ) / d ≤ (m : ℝ)) (hp : a / (n : ℝ) ^ c ≤ p) :
    (a / d) * (n : ℝ) ^ (1 - c) ≤ (m : ℝ) * p := by
  have hrpow : (n : ℝ) * ((n : ℝ) ^ c)⁻¹ = (n : ℝ) ^ (1 - c) := by
    rw [Real.rpow_sub hn, Real.rpow_one, div_eq_mul_inv]
  calc (a / d) * (n : ℝ) ^ (1 - c) = ((n : ℝ) / d) * (a / (n : ℝ) ^ c) := by
        rw [div_eq_mul_inv, ← hrpow]; ring
    _ ≤ (m : ℝ) * p := mul_le_mul hm hp (by positivity) (Nat.cast_nonneg _)

/-- Core exponential tail bound for uniform vertex-to-set degree concentration whenever `k n`
satisfies `κ * log n ≤ k n * p n` and `k n / n → 0`. -/
private theorem eventually_badDegree_le_exp_neg {p : ℕ → I}
    {ε₀ η κ : ℝ} (hε₀ : 0 < ε₀) (hη0 : 0 < η) (hη1 : η ≤ 1) (hκ : 0 < κ) (k : ℕ → ℕ)
    (hk_lo : ∀ᶠ n : ℕ in atTop, κ * Real.log (n : ℝ) ≤ (k n : ℝ) * (p n : ℝ))
    (hk_small : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      G(Fin n, p n).real {G | ∃ A : Finset (Fin n), ε₀ * (n : ℝ) ≤ (#A : ℝ) ∧
        2 * k n ≤ ({u : Fin n | η * ((#A : ℝ) * (p n : ℝ)) <
          |(((A : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
          Set (Fin n)).ncard} ≤
        3 * Real.exp (-(n : ℝ)) := by
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_big : ∀ᶠ n : ℕ in atTop,
      (2 * Real.log 2 + 1) * 24 / (η ^ 2 * κ * ε₀) ≤ Real.log (n : ℝ) :=
    hlog_inf.eventually (eventually_ge_atTop _)
  have hk_ratio : ∀ᶠ n : ℕ in atTop, (k n : ℝ) / (n : ℝ) ≤ η * ε₀ / 4 :=
    hk_small.eventually (eventually_le_nhds (by positivity))
  filter_upwards [hk_lo, hk_ratio, hlog_big, eventually_ge_atTop 1] with
    n hkn_lo hkn_rat hlogn hn1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let a₀ : ℕ := ⌈ε₀ * (n : ℝ)⌉₊
  have ha₀_ge : ε₀ * (n : ℝ) ≤ (a₀ : ℝ) := Nat.le_ceil _
  have hka : 4 * (k n : ℝ) ≤ η * (a₀ : ℝ) := by
    have h1 : (k n : ℝ) ≤ (η * ε₀ / 4) * (n : ℝ) := (div_le_iff₀ hn_pos).1 hkn_rat
    nlinarith
  have hsub : {G : SimpleGraph (Fin n) | ∃ A : Finset (Fin n), ε₀ * (n : ℝ) ≤ (#A : ℝ) ∧
      2 * k n ≤ ({u : Fin n | η * ((#A : ℝ) * (p n : ℝ)) <
        |(((A : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
        Set (Fin n)).ncard} ⊆
      {G | ∃ A : Finset (Fin n), a₀ ≤ #A ∧
        2 * k n ≤ ({u : Fin n | η * ((#A : ℝ) * (p n : ℝ)) <
          |(((A : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
          Set (Fin n)).ncard} := by
    rintro G ⟨A, hA, hbad⟩
    exact ⟨A, Nat.ceil_le.2 hA, hbad⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hbd := binomialRandom_real_exists_many_badDegree_le (V := Fin n) (p n) hη0 hη1 hka
  rw [Fintype.card_fin] at hbd
  refine hbd.trans ?_
  have h4eq : (4 : ℝ) ^ n = Real.exp ((n : ℝ) * (2 * Real.log 2)) := by
    have h4 : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
      rw [show (2 : ℝ) * Real.log 2 = ((2 : ℕ) : ℝ) * Real.log 2 by norm_num, Real.exp_nat_mul,
        Real.exp_log (by norm_num)]
      norm_num
    rw [h4, ← Real.exp_nat_mul]
  rw [mul_assoc, h4eq, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have hlog_mul : (2 * Real.log 2 + 1) * 24 ≤ η ^ 2 * κ * ε₀ * Real.log (n : ℝ) := by
    have hpos : 0 < η ^ 2 * κ * ε₀ := by positivity
    linarith [(div_le_iff₀ hpos).1 hlogn]
  have hkp_a₀ : κ * Real.log (n : ℝ) * (ε₀ * (n : ℝ)) ≤ (k n : ℝ) * (a₀ : ℝ) * (p n : ℝ) := by
    have h1 : κ * Real.log (n : ℝ) * (ε₀ * (n : ℝ)) ≤ ((k n : ℝ) * (p n : ℝ)) * (a₀ : ℝ) :=
      mul_le_mul hkn_lo ha₀_ge (by positivity)
        (mul_nonneg (Nat.cast_nonneg _) (unitInterval.nonneg _))
    linarith
  have hmain : (n : ℝ) * (2 * Real.log 2 + 1) * 24 ≤
      η ^ 2 * (k n : ℝ) * (a₀ : ℝ) * (p n : ℝ) := by
    have h1 : (n : ℝ) * ((2 * Real.log 2 + 1) * 24) ≤
        (n : ℝ) * (η ^ 2 * κ * ε₀ * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_mul hn_pos.le
    have h2 : η ^ 2 * (κ * Real.log (n : ℝ) * (ε₀ * (n : ℝ))) ≤
        η ^ 2 * ((k n : ℝ) * (a₀ : ℝ) * (p n : ℝ)) :=
      mul_le_mul_of_nonneg_left hkp_a₀ (sq_nonneg η)
    linarith
  linarith

/-- Complementary w.h.p. form of `eventually_badDegree_le_exp_neg`. -/
private theorem tendsto_goodDegree_one {p : ℕ → I}
    {ε₀ η κ : ℝ} (hε₀ : 0 < ε₀) (hη0 : 0 < η) (hη1 : η ≤ 1) (hκ : 0 < κ) (k : ℕ → ℕ)
    (hk_lo : ∀ᶠ n : ℕ in atTop, κ * Real.log (n : ℝ) ≤ (k n : ℝ) * (p n : ℝ))
    (hk_small : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ A : Finset (Fin n),
      ε₀ * (n : ℝ) ≤ (#A : ℝ) →
        ({u : Fin n | η * ((#A : ℝ) * (p n : ℝ)) <
          |(((A : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
          Set (Fin n)).ncard < 2 * k n}) atTop (𝓝 1) := by
  have hbad_ev := eventually_badDegree_le_exp_neg hε₀ hη0 hη1 hκ k hk_lo hk_small
  have hbad_zero : Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∃ A : Finset (Fin n),
      ε₀ * (n : ℝ) ≤ (#A : ℝ) ∧
        2 * k n ≤ ({u : Fin n | η * ((#A : ℝ) * (p n : ℝ)) <
          |(((A : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
          Set (Fin n)).ncard}) atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => 3 * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
      simpa using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall fun _ => measureReal_nonneg) hbad_ev
  have h1 := hbad_zero.const_sub 1
  rw [sub_zero] at h1
  refine h1.congr fun n => ?_
  rw [← probReal_compl_eq_one_sub .of_discrete]
  congr 1
  ext G
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_le]

/-! ### Unconditional Lemma 29.17 (additive and multiplicative forms) -/

/-- **Unconditional uniform additive fitness concentration** (generalizing [Suri2007], Lemma 29.17,
p. 731, to arbitrary real payoff matrices without positivity assumptions, simultaneously over all
adversarial mutant sets `M`): when `p n = Ω(1 / n ^ c)` (`0 ≤ c < 1`), for any `0 < ε₀`,
`0 < η ≤ 1 / 2`, any game `F`, and any strategies `s, t`, with probability tending to `1` in
`G(Fin n, p n)`, for every mutant set `M` with `ε₀ n ≤ |M|, |Mᶜ|`, all but at most
`4 * ⌈log n / p n⌉₊` vertices have fitness within `η * |F(s|t) - F(s|s)|` (for incumbents) or
`η * |F(t|t) - F(t|s)|` (for mutants) of the classical expected fitness at share `|M| / n`. -/
theorem tendsto_binomialRandom_real_forall_abnormalFitness_additive_le {p : ℕ → I} {c : ℝ}
    (hc1 : c < 1) (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ))
    (F : BimatrixGame α α) (s t : α → ℝ) {ε₀ η : ℝ} (hε₀ : 0 < ε₀) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ M : Finset (Fin n),
      ε₀ * (n : ℝ) ≤ (#M : ℝ) → ε₀ * (n : ℝ) ≤ (#Mᶜ : ℝ) →
        ({u : Fin n |
          if u ∈ M then
            η * |F.payoff₁ t t - F.payoff₁ t s| <
              |F.graphFitness G (fun v => if v ∈ M then t else s) u -
                ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t)|
          else
            η * |F.payoff₁ s t - F.payoff₁ s s| <
              |F.graphFitness G (fun v => if v ∈ M then t else s) u -
                ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t)|} :
          Set (Fin n)).ncard ≤ 4 * ⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊}) atTop (𝓝 1) := by
  let k : ℕ → ℕ := fun n => ⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊
  obtain ⟨hp_pos, _, hk_lo, hk_small⟩ := dense_p_kCeil_props hc1 hp
  have hgood_one := tendsto_goodDegree_one hε₀ hη0 (by linarith) one_pos k hk_lo hk_small
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hgood_one tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => measureReal_le_one)
  filter_upwards [hp_pos, eventually_ge_atTop 1] with n hpn hn1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine measureReal_mono (fun G hG M hM hI => ?_) (measure_ne_top _ _)
  let BM : Set (Fin n) := {u | η * ((#M : ℝ) * (p n : ℝ)) <
    |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * (p n : ℝ)|}
  let BI : Set (Fin n) := {u | η * ((#Mᶜ : ℝ) * (p n : ℝ)) <
    |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) -
      (#Mᶜ : ℝ) * (p n : ℝ)|}
  have hsub : {u : Fin n |
      if u ∈ M then
        η * |F.payoff₁ t t - F.payoff₁ t s| <
          |F.graphFitness G (fun v => if v ∈ M then t else s) u -
            ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t)|
      else
        η * |F.payoff₁ s t - F.payoff₁ s s| <
          |F.graphFitness G (fun v => if v ∈ M then t else s) u -
            ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t)|} ⊆
      BM ∪ BI := by
    intro u hu
    by_contra hunion
    have hreg := graphFitness_bounds_of_regular F G M s t hpn hη0.le hη1
      (lt_of_lt_of_le (by positivity) hM) (lt_of_lt_of_le (by positivity) hI)
      (not_lt.1 fun h => hunion (Or.inl h)) (not_lt.1 fun h => hunion (Or.inr h))
    simp only [Set.mem_ofPred_eq] at hu
    by_cases hum : u ∈ M
    · simp only [hum, ↓reduceIte] at hu
      linarith [hreg.2.1 hum]
    · simp only [hum, ↓reduceIte] at hu
      linarith [hreg.1 hum]
  have hBM : BM.ncard < 2 * k n := hG M hM
  have hBI : BI.ncard < 2 * k n := hG Mᶜ (by simpa using hI)
  have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le BM BI)
  dsimp only [k] at hBM hBI
  omega

/-- **Unconditional Lemma 29.17** ([Suri2007], Section 29.4.1, p. 731, stated without proof in the
source): for a game `F` with strictly positive payoffs (`0 < F.A i j`), mixed strategies `s, t`,
constants `0 < ε < 1`, `0 < τ < 1 / 6`, `0 ≤ c < 1`, and `p n = Ω(1 / n ^ c)`, with probability
tending to `1` in `G(Fin n, p n)`, simultaneously over all mutant sets `M` with
`min ε (1 - ε) * n ≤ |M|, |Mᶜ|`, at most `24 * log n / (τ ^ 2 * p n)` incumbents lie outside
`(1 ± τ) [(1 - ε_M) F(s|s) + ε_M F(s|t)]` and at most `24 * log n / (τ ^ 2 * p n)` mutants lie
outside `(1 ± τ) [(1 - ε_M) F(t|s) + ε_M F(t|t)]` (where `ε_M = |M| / n`, specializing to `ε`
when `|M| = ε n`).

Strict positivity `0 < F.A i j` ensures that the target fitnesses are positive, which is required
for a multiplicative `(1 ± τ)` range. -/
theorem tendsto_binomialRandom_real_forall_abnormalFitness_mul_le {p : ℕ → I} {c : ℝ}
    (hc1 : c < 1) (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ))
    (F : BimatrixGame α α) (hA : ∀ i j, 0 < F.A i j) {s t : α → ℝ}
    (hs : IsMixedStrategy s) (ht : IsMixedStrategy t)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1 / 6) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ M : Finset (Fin n),
      min ε (1 - ε) * (n : ℝ) ≤ (#M : ℝ) → min ε (1 - ε) * (n : ℝ) ≤ (#Mᶜ : ℝ) →
        (({u : Fin n | u ∉ M ∧ ¬(
          (1 - τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t) ≤
            F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
          F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
            (1 + τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t))} :
          Set (Fin n)).ncard : ℝ) ≤ 24 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) ∧
        (({u : Fin n | u ∈ M ∧ ¬(
          (1 - τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t) ≤
            F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
          F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
            (1 + τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t))} :
          Set (Fin n)).ncard : ℝ) ≤ 24 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ))})
      atTop (𝓝 1) := by
  let ε₀ : ℝ := min ε (1 - ε)
  have hε₀ : 0 < ε₀ := lt_min hε0 (sub_pos.2 hε1)
  let η : ℝ := τ / 3
  have hη0 : 0 < η := by dsimp only [η]; linarith
  have hη3 : η ≤ 1 / 3 := by dsimp only [η]; linarith
  let k : ℕ → ℕ := fun n => ⌊6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ))⌋₊
  obtain ⟨hp_pos, hlog_p, _, _⟩ := dense_p_kCeil_props hc1 hp
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio_ge2 : ∀ᶠ n : ℕ in atTop, 2 ≤ 6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) := by
    filter_upwards [hp_pos, hlog_inf.eventually (eventually_ge_atTop (τ ^ 2 / 3))] with n hpn hlog
    rw [le_div_iff₀ (by positivity)]
    have hp1 : (p n : ℝ) ≤ 1 := unitInterval.le_one (p n)
    nlinarith [sq_nonneg τ]
  have hk_lo : ∀ᶠ n : ℕ in atTop, (3 / τ ^ 2) * Real.log (n : ℝ) ≤ (k n : ℝ) * (p n : ℝ) := by
    filter_upwards [hp_pos, hratio_ge2] with n hpn hn
    have hfl : 6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) - 1 < (k n : ℝ) := by
      have := Nat.lt_floor_add_one (6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)))
      linarith
    have htwo : 6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) =
        2 * (3 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ))) := by ring
    have hhalf : 3 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) ≤ (k n : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf hpn.le
    calc (3 / τ ^ 2) * Real.log (n : ℝ) =
          3 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) * (p n : ℝ) := by field_simp
      _ ≤ (k n : ℝ) * (p n : ℝ) := hmul
  have hk_small : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine tendsto_div_nat_zero_of_eventually_le
      (by simpa using hlog_p.const_mul (6 / τ ^ 2)) ?_
    filter_upwards [hp_pos, eventually_ge_atTop 1] with n hpn hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hfl : (k n : ℝ) ≤ 6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) :=
      Nat.floor_le (by positivity)
    calc (k n : ℝ) / (n : ℝ) ≤ (6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ))) / (n : ℝ) :=
          div_le_div_of_nonneg_right hfl (Nat.cast_nonneg n)
      _ = (6 / τ ^ 2) * (Real.log (n : ℝ) / ((n : ℝ) * (p n : ℝ))) := by field_simp
  have hgood_one := tendsto_goodDegree_one hε₀ hη0 (by linarith) (by positivity) k hk_lo hk_small
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hgood_one tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => measureReal_le_one)
  filter_upwards [hp_pos, eventually_ge_atTop 1] with n hpn hn1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have h4k : (4 * k n : ℝ) ≤ 24 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) := by
    have hfl : (k n : ℝ) ≤ 6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) :=
      Nat.floor_le (by positivity)
    have h4eq : 24 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) =
        4 * (6 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ))) := by ring
    linarith
  refine measureReal_mono (fun G hG M hM hI => ?_) (measure_ne_top _ _)
  let BM : Set (Fin n) := {u | η * ((#M : ℝ) * (p n : ℝ)) <
    |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * (p n : ℝ)|}
  let BI : Set (Fin n) := {u | η * ((#Mᶜ : ℝ) * (p n : ℝ)) <
    |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) -
      (#Mᶜ : ℝ) * (p n : ℝ)|}
  have hBM : BM.ncard < 2 * k n := hG M hM
  have hBI : BI.ncard < 2 * k n := hG Mᶜ (by simpa using hI)
  have hunion_card : ((BM ∪ BI).ncard : ℝ) ≤ 24 * Real.log (n : ℝ) / (τ ^ 2 * (p n : ℝ)) := by
    have hnat : (BM ∪ BI).ncard ≤ 4 * k n := by
      have := Set.ncard_union_le BM BI
      omega
    exact (by exact_mod_cast hnat : ((BM ∪ BI).ncard : ℝ) ≤ (4 * k n : ℝ)).trans h4k
  have hgood_u : ∀ u, u ∉ BM ∪ BI →
      (u ∉ M →
        (1 - τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t) ≤
          F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
        F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
          (1 + τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t)) ∧
      (u ∈ M →
        (1 - τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t) ≤
          F.graphFitness G (fun v => if v ∈ M then t else s) u ∧
        F.graphFitness G (fun v => if v ∈ M then t else s) u ≤
          (1 + τ) * ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t)) := by
    intro u hu
    have hreg := (graphFitness_bounds_of_regular F G M s t hpn hη0.le (by linarith)
      (lt_of_lt_of_le (by positivity) hM) (lt_of_lt_of_le (by positivity) hI)
      (not_lt.1 fun h => hu (Or.inl h)) (not_lt.1 fun h => hu (Or.inr h))).2.2
      hη3 hA hs ht
    have h3η : 3 * η = τ := by dsimp only [η]; ring
    simpa only [h3η] using hreg
  constructor
  · refine le_trans ?_ hunion_card
    exact_mod_cast Set.ncard_le_ncard
      (fun u hu => by by_contra hnot; exact hu.2 ((hgood_u u hnot).1 hu.1)) (Set.toFinite _)
  · refine le_trans ?_ hunion_card
    exact_mod_cast Set.ncard_le_ncard
      (fun u hu => by by_contra hnot; exact hu.2 ((hgood_u u hnot).2 hu.1)) (Set.toFinite _)

/-! ### Unconditional Theorem 29.16 -/

/-- Almost-sure Bollobás non-neighborhood event along `Measure.infinitePi (fun n => G(Fin n, p n))`
for subsets of size at least `n / 4` and non-neighborhood threshold `δ n = n ^ (-(1 - c) / 2)`. -/
private theorem ae_eventually_nonNeighborhood_quarter {p : ℕ → I} {c : ℝ}
    (hc1 : c < 1) (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) :
    ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)),
      ∀ᶠ n : ℕ in atTop, ∀ U : Finset (Fin n), n / 4 ≤ #U →
        (({x : Fin n | x ∉ U ∧
          Disjoint ((G n).neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard : ℝ) <
          (n : ℝ) ^ (-((1 - c) / 2)) * (n : ℝ) := by
  obtain ⟨a, ha, hp_ev⟩ := hp
  let γ : ℝ := (1 - c) / 2
  have hγ : 0 < γ := by dsimp only [γ]; linarith
  have h1c : 0 < 1 - c := sub_pos.2 hc1
  let B : ∀ n : ℕ, Set (SimpleGraph (Fin n)) := fun n =>
    {G | ∃ U : Finset (Fin n), n / 4 ≤ #U ∧
      (n : ℝ) ^ (-γ) * (n : ℝ) ≤
        (({x : Fin n | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard :
          ℝ)}
  have hlog_γ : ∀ᶠ n : ℕ in atTop, 3 * Real.log (n : ℝ) ≤ a * (n : ℝ) ^ γ := by
    have hlim := tendsto_log_div_rpow_nat hγ
    filter_upwards [hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < a / 3)),
      eventually_ge_atTop 1] with n hn hn1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 := (div_le_iff₀ (Real.rpow_pos_of_pos hn_pos γ)).1 hn
    linarith
  have hlog_1c : ∀ᶠ n : ℕ in atTop,
      3 * (1 + γ * Real.log (n : ℝ)) ≤ (a / 8) * (n : ℝ) ^ (1 - c) := by
    have hlim1 := tendsto_log_div_rpow_nat h1c
    have hlim2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - c)) atTop atTop :=
      (tendsto_rpow_atTop h1c).comp tendsto_natCast_atTop_atTop
    filter_upwards [hlim1.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < a / (48 * γ))),
      hlim2.eventually (eventually_ge_atTop (48 / a)), eventually_ge_atTop 1] with n h1 h2 hn1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hr_pos : 0 < (n : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hn_pos _
    have hlog_le := (div_le_iff₀ hr_pos).1 h1
    have hterm1 : 3 ≤ (a / 16) * (n : ℝ) ^ (1 - c) := by
      have : 48 ≤ (n : ℝ) ^ (1 - c) * a := (div_le_iff₀ ha).1 h2
      linarith
    have hterm2 : 3 * γ * Real.log (n : ℝ) ≤ (a / 16) * (n : ℝ) ^ (1 - c) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_le (by positivity : (0 : ℝ) ≤ 3 * γ)
      have hsimp : 3 * γ * (a / (48 * γ) * (n : ℝ) ^ (1 - c)) =
          (a / 16) * (n : ℝ) ^ (1 - c) := by field_simp; ring
      linarith
    linarith
  have hCδ : ∀ᶠ n : ℕ in atTop, 3 ≤ (a / 8) * (n : ℝ) ^ γ := by
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
      (tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (eventually_ge_atTop (24 / a))] with n hn
    have : 24 ≤ (n : ℝ) ^ γ * a := (div_le_iff₀ ha).1 hn
    linarith
  have hbound : ∀ᶠ n : ℕ in atTop, G(Fin n, p n).real (B n) ≤ 1 * Real.exp (-(n : ℝ)) := by
    filter_upwards [hp_ev, hlog_γ, hlog_1c, hCδ, eventually_ge_atTop 8] with
      n hpn hlγ hl1c hcδ hn8
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcard_pos : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
    let δ : ℝ := (n : ℝ) ^ (-γ)
    let C : ℝ := ((n / 4 : ℕ) : ℝ) * (p n : ℝ)
    have hδ_pos : 0 < δ := Real.rpow_pos_of_pos hn_pos _
    have hquarter : (n : ℝ) / 8 ≤ ((n / 4 : ℕ) : ℝ) := by
      have hnat : n ≤ 8 * (n / 4) := by omega
      have hreal : (n : ℝ) ≤ 8 * ((n / 4 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    have hC_ge : (a / 8) * (n : ℝ) ^ (1 - c) ≤ C :=
      mul_rpow_one_sub_le_mul_p hn_pos ha.le hquarter hpn
    have hlog_cond :
        3 * Real.log (Fintype.card (Fin n)) ≤ δ * (p n : ℝ) * Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      have hprod : a * (n : ℝ) ^ γ ≤ δ * (p n : ℝ) * (n : ℝ) := by
        have hrpow : (n : ℝ) ^ (-γ) * ((n : ℝ) ^ c)⁻¹ * (n : ℝ) = (n : ℝ) ^ γ := by
          rw [← Real.rpow_neg hn_pos.le c, ← Real.rpow_add hn_pos]
          calc (n : ℝ) ^ (-γ + -c) * (n : ℝ)
              = (n : ℝ) ^ (-γ + -c) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = (n : ℝ) ^ (-γ + -c + 1) := (Real.rpow_add hn_pos _ _).symm
            _ = (n : ℝ) ^ γ := by congr 1; dsimp only [γ]; ring
        calc a * (n : ℝ) ^ γ = δ * (a / (n : ℝ) ^ c) * (n : ℝ) := by
              dsimp only [δ]; rw [div_eq_mul_inv, ← hrpow]; ring
          _ ≤ δ * (p n : ℝ) * (n : ℝ) := by gcongr
      linarith
    have hClog_cond : 3 * Real.log (Real.exp 1 / δ) ≤ C := by
      have hlog_eq : Real.log (Real.exp 1 / δ) = 1 + γ * Real.log (n : ℝ) := by
        rw [Real.log_div (Real.exp_pos 1).ne' hδ_pos.ne', Real.log_exp]
        dsimp only [δ]
        rw [Real.log_rpow hn_pos]
        ring
      rw [hlog_eq]
      linarith
    have hmain := binomialRandom_real_exists_large_nonNeighborhood_le (V := Fin n) hcard_pos (p n)
      hδ_pos (u := n / 4) le_rfl hlog_cond hClog_cond
    rw [Fintype.card_fin] at hmain
    refine hmain.trans ?_
    rw [one_mul, Real.exp_le_exp]
    have hexp_ge : 3 * (n : ℝ) ≤ C * δ * (n : ℝ) := by
      have h1 : (a / 8) * (n : ℝ) ^ γ * (n : ℝ) ≤ C * δ * (n : ℝ) := by
        have hrpow : (n : ℝ) ^ (1 - c) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ γ := by
          rw [← Real.rpow_add hn_pos]; congr 1; dsimp only [γ]; ring
        calc (a / 8) * (n : ℝ) ^ γ * (n : ℝ) =
              ((a / 8) * (n : ℝ) ^ (1 - c)) * δ * (n : ℝ) := by
                dsimp only [δ]; rw [← hrpow]; ring
          _ ≤ C * δ * (n : ℝ) := by gcongr
      have h2 : 3 * (n : ℝ) ≤ (a / 8) * (n : ℝ) ^ γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcδ hn_pos.le
      linarith
    linarith
  filter_upwards [ae_eventually_notMem_infinitePi_of_exp_neg B zero_le_one hbound] with G hG
  filter_upwards [hG] with n hn U hU
  by_contra! hge
  exact hn ⟨U, hU, hge⟩

/-- Almost-sure countable intersection of uniform degree concentration over all rational tolerances
`ε₀ = 1 / (r + 2)` and `η = 1 / (q + 4)`. -/
private theorem ae_eventually_forall_badDegree_lt {p : ℕ → I} {c : ℝ} (hc1 : c < 1)
    (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) :
    ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)),
      ∀ r q : ℕ, ∀ᶠ n : ℕ in atTop, ∀ A : Finset (Fin n),
        (1 / ((r : ℝ) + 2)) * (n : ℝ) ≤ (#A : ℝ) →
          ({u : Fin n | (1 / ((q : ℝ) + 4)) * ((#A : ℝ) * (p n : ℝ)) <
            |(((A : Set (Fin n)) ∩ (G n).neighborSet u).ncard : ℝ) - (#A : ℝ) * (p n : ℝ)|} :
            Set (Fin n)).ncard < 2 * ⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊ := by
  obtain ⟨_, _, hk_lo, hk_small⟩ := dense_p_kCeil_props hc1 hp
  rw [ae_all_iff]
  intro r
  rw [ae_all_iff]
  intro q
  let ε₀ : ℝ := 1 / ((r : ℝ) + 2)
  let η : ℝ := 1 / ((q : ℝ) + 4)
  have hε₀ : 0 < ε₀ := by positivity
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    dsimp only [η]
    rw [div_le_one (by positivity : (0 : ℝ) < (q : ℝ) + 4)]
    linarith [Nat.cast_nonneg (α := ℝ) q]
  have hbd := eventually_badDegree_le_exp_neg hε₀ hη0 hη1 one_pos
    (fun n => ⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊) hk_lo hk_small
  filter_upwards [ae_eventually_notMem_infinitePi_of_exp_neg _ (by norm_num) hbd] with G hG
  filter_upwards [hG] with n hn A hA
  by_contra! hge
  exact hn ⟨A, hA, hge⟩

/-- Deterministic step of Theorem 29.16: at a single size `n`, if `G` satisfies degree
concentration at tolerance `η` and the Bollobás non-neighborhood bound on `I' = Mᶜ \ Bad`, then
the surviving mutants have cardinality at most `4 * k + δ * n`. -/
private theorem survivingMutants_card_le_of_regular_and_nonNeighborhood {n k : ℕ}
    (F : BimatrixGame α α) (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (s t : α → ℝ)
    {p η Δ δ : ℝ} (hp : 0 < p) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hM_pos : 0 < (#M : ℝ)) (hI_half : (1 / 2) * (n : ℝ) ≤ (#Mᶜ : ℝ))
    (h4k_q : 4 * (k : ℝ) ≤ (1 / 4) * (n : ℝ))
    (hgap : Δ ≤ ((1 - (#M : ℝ) / n) * F.payoff₁ s s + ((#M : ℝ) / n) * F.payoff₁ s t) -
      ((1 - (#M : ℝ) / n) * F.payoff₁ t s + ((#M : ℝ) / n) * F.payoff₁ t t))
    (hη_sum : η * |F.payoff₁ s t - F.payoff₁ s s| + η * |F.payoff₁ t t - F.payoff₁ t s| < Δ)
    (hBM : ({u : Fin n | η * ((#M : ℝ) * p) <
      |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * p|} :
      Set (Fin n)).ncard < 2 * k)
    (hBI : ({u : Fin n | η * ((#Mᶜ : ℝ) * p) <
      |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#Mᶜ : ℝ) * p|} :
      Set (Fin n)).ncard < 2 * k)
    (hnon : ∀ U : Finset (Fin n), n / 4 ≤ #U →
      (({x : Fin n | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard :
        ℝ) < δ * (n : ℝ)) :
    ((F.survivingMutants G M s t).card : ℝ) ≤ 4 * (k : ℝ) + δ * (n : ℝ) := by
  let BM : Finset (Fin n) := univ.filter fun u =>
    η * ((#M : ℝ) * p) < |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * p|
  let BI : Finset (Fin n) := univ.filter fun u =>
    η * ((#Mᶜ : ℝ) * p) <
      |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#Mᶜ : ℝ) * p|
  have hBM_c : #BM < 2 * k := by
    have hcoe : ({u : Fin n | η * ((#M : ℝ) * p) <
        |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * p|} : Set (Fin n)) =
        (BM : Set (Fin n)) := by ext u; simp [BM]
    rwa [hcoe, Set.ncard_coe_finset] at hBM
  have hBI_c : #BI < 2 * k := by
    have hcoe : ({u : Fin n | η * ((#Mᶜ : ℝ) * p) <
        |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#Mᶜ : ℝ) * p|} :
        Set (Fin n)) = (BI : Set (Fin n)) := by ext u; simp [BI]
    rwa [hcoe, Set.ncard_coe_finset] at hBI
  let Bad : Finset (Fin n) := BM ∪ BI
  have hBad_card : #Bad ≤ 4 * k := by
    have hle := Finset.card_union_le BM BI
    dsimp only [Bad]
    omega
  have hI_pos : 0 < (#Mᶜ : ℝ) := by
    have hle : #M ≤ n := by simpa using Finset.card_le_univ M
    have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hM_pos (by exact_mod_cast hle)
    linarith
  have hnormal_lt : ∀ j ∈ M, j ∉ Bad → ∀ i, i ∉ M → i ∉ Bad →
      F.graphFitness G (fun v => if v ∈ M then t else s) j <
        F.graphFitness G (fun v => if v ∈ M then t else s) i := by
    intro j hjM hjB i hiM hiB
    have hreg_of : ∀ u, u ∉ Bad →
        |(((M : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#M : ℝ) * p| ≤
          η * ((#M : ℝ) * p) ∧
        |((((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet u).ncard : ℝ) - (#Mᶜ : ℝ) * p| ≤
          η * ((#Mᶜ : ℝ) * p) := by
      intro u hu
      constructor
      · by_contra! hgt
        exact hu (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, hgt⟩))
      · by_contra! hgt
        exact hu (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, hgt⟩))
    have ⟨hiM', hiI'⟩ := hreg_of i hiB
    have ⟨hjM', hjI'⟩ := hreg_of j hjB
    have hi_cl := (abs_le.1 ((graphFitness_bounds_of_regular F G M s t hp hη0 hη hM_pos hI_pos
      hiM' hiI').1 hiM)).1
    have hj_cl := (abs_le.1 ((graphFitness_bounds_of_regular F G M s t hp hη0 hη hM_pos hI_pos
      hjM' hjI').2.1 hjM)).2
    linarith
  let I' : Finset (Fin n) := Mᶜ \ Bad
  have hI'_card : n / 4 ≤ #I' := by
    have hI'_ge_real : (n : ℝ) / 4 ≤ (#I' : ℝ) := by
      have hnat : #Mᶜ ≤ #I' + #Bad := by
        have h1 := Finset.card_sdiff_add_card_inter Mᶜ Bad
        have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Mᶜ) (s₂ := Bad))
        dsimp only [I']
        omega
      have hreal : (#Mᶜ : ℝ) ≤ (#I' : ℝ) + (#Bad : ℝ) := by exact_mod_cast hnat
      have hbad_r : (#Bad : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hBad_card
      linarith
    have hnat_le : ((n / 4 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
      have : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
      have hreal : 4 * ((n / 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    exact_mod_cast (hnat_le.trans hI'_ge_real)
  let T : Set (Fin n) := {x : Fin n | x ∉ I' ∧ Disjoint (G.neighborSet x) (I' : Set (Fin n))}
  have hT_lt : (T.ncard : ℝ) < δ * (n : ℝ) := hnon I' hI'_card
  have hsurv_sub : (F.survivingMutants G M s t : Set (Fin n)) ⊆ (Bad : Set (Fin n)) ∪ T := by
    intro j hj
    rw [Finset.mem_coe, mem_survivingMutants_iff] at hj
    by_cases hjB : j ∈ Bad
    · exact Or.inl hjB
    · refine Or.inr ⟨fun hjI' => (Finset.mem_compl.1 (Finset.mem_sdiff.1 hjI').1) hj.1, ?_⟩
      refine Set.disjoint_left.2 fun i hi_adj hiI' => ?_
      have hi_mem := Finset.mem_sdiff.1 hiI'
      have hiM : i ∉ M := Finset.mem_compl.1 hi_mem.1
      exact hj.2 ⟨i, hiM, (G.mem_neighborSet j i).1 hi_adj, hnormal_lt j hj.1 hjB i hiM hi_mem.2⟩
  have hnat : #(F.survivingMutants G M s t) ≤ #Bad + T.ncard := by
    rw [← Set.ncard_coe_finset, ← Set.ncard_coe_finset (s := Bad)]
    exact (Set.ncard_le_ncard hsurv_sub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hreal : ((F.survivingMutants G M s t).card : ℝ) ≤ (#Bad : ℝ) + (T.ncard : ℝ) := by
    exact_mod_cast hnat
  have hbad_r : (#Bad : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hBad_card
  linarith

/-- **Unconditional Theorem 29.16** ([Suri2007], Section 29.4.1, pp. 731–732; Kearns and Suri
2006): for any finite two-player bimatrix game `F` (arbitrary real payoffs) and any classical
evolutionarily stable strategy `s` (`F.IsESS s`), if an infinite graph family `G` is drawn
independently from `G(Fin n, p n)` with `p n = Ω(1 / n ^ c)` and `c < 1` (note `p n ≤ 1`
automatically forces `0 ≤ c`), then almost surely (`∀ᵐ`) under
`Measure.infinitePi (fun n => G(Fin n, p n))`, `s` is a graph ESS with respect to `F` and `G` (for
all mixed mutant strategies `t ≠ s` and all adversarial `ε_t`-linear mutant families
simultaneously).

Both Lemma 29.17 and Theorem 29.18 are proved unconditionally inside the library rather than
assumed. As in `BimatrixGame.IsESS`, only `F.A` enters through `F.payoff₁` (the symmetric game's
fitness function when `F.B = F.Aᵀ`). -/
theorem binomialRandom_infinitePi_isGraphESS {p : ℕ → I} {c : ℝ} (hc1 : c < 1)
    (hp : ∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ))
    (F : BimatrixGame α α) {s : α → ℝ} (hs : F.IsESS s) :
    ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)), F.IsGraphESS G s := by
  let k : ℕ → ℕ := fun n => ⌈Real.log (n : ℝ) / (p n : ℝ)⌉₊
  obtain ⟨hp_pos, _, _, hk_small⟩ := dense_p_kCeil_props hc1 hp
  have hae_deg := ae_eventually_forall_badDegree_lt hc1 hp
  have hae_non := ae_eventually_nonNeighborhood_quarter hc1 hp
  filter_upwards [hae_deg, hae_non] with G hdeg hnon
  refine ⟨hs.isMixedStrategy, fun t ht hne => ?_⟩
  obtain ⟨ε₀', hε₀', hlt_ess⟩ := (isESS_iff.1 hs).2 t ht hne
  let εt : ℝ := min (ε₀' / 2) (1 / 2)
  have hεt_pos : 0 < εt := lt_min (by linarith) (by norm_num)
  have hεt_lt : εt < ε₀' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεt_half : εt ≤ 1 / 2 := min_le_right _ _
  refine ⟨εt, hεt_pos, fun M ⟨ε_lo, hε_lo0, hε_lo_lt, hM_ev⟩ => ?_⟩
  let g : ℝ → ℝ := fun x =>
    ((1 - x) * F.payoff₁ s s + x * F.payoff₁ s t) -
      ((1 - x) * F.payoff₁ t s + x * F.payoff₁ t t)
  have hg_lo : 0 < g ε_lo := sub_pos.2 (hlt_ess ε_lo hε_lo0 (hε_lo_lt.trans hεt_lt))
  have hg_hi : 0 < g εt := sub_pos.2 (hlt_ess εt hεt_pos hεt_lt)
  let Δ : ℝ := min (g ε_lo) (g εt)
  have hΔ : 0 < Δ := lt_min hg_lo hg_hi
  have hg_ge : ∀ x, ε_lo ≤ x → x ≤ εt → Δ ≤ g x := by
    intro x hx1 hx2
    have hdiff : 0 < εt - ε_lo := sub_pos.2 hε_lo_lt
    let lam : ℝ := (x - ε_lo) / (εt - ε_lo)
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.2 hx1) hdiff.le
    have hlam1 : lam ≤ 1 := (div_le_one hdiff).2 (by linarith)
    have hx_eq : x = (1 - lam) * ε_lo + lam * εt := by dsimp only [lam]; field_simp; ring
    have hg_aff : g x = (1 - lam) * g ε_lo + lam * g εt := by rw [hx_eq]; dsimp only [g]; ring
    rw [hg_aff]
    have h1 : Δ ≤ g ε_lo := min_le_left _ _
    have h2 : Δ ≤ g εt := min_le_right _ _
    nlinarith
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε_lo)
  have hεr_le : 1 / ((r : ℝ) + 2) ≤ ε_lo := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ hε_lo0).1 hr
    linarith
  have hεr_half : 1 / ((r : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  let L : ℝ := |F.payoff₁ s t - F.payoff₁ s s| + |F.payoff₁ t t - F.payoff₁ t s| + 1
  have hL : 0 < L := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (2 * L / Δ)
  let η : ℝ := 1 / ((q : ℝ) + 4)
  have hη0 : 0 < η := by positivity
  have hη_half : η ≤ 1 / 2 := by
    dsimp only [η]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Nat.cast_nonneg (α := ℝ) q]
  have hη_sum : η * |F.payoff₁ s t - F.payoff₁ s s| + η * |F.payoff₁ t t - F.payoff₁ t s| < Δ := by
    have h1 : 2 * L / Δ < (q : ℝ) + 4 := lt_of_lt_of_le hq (by linarith)
    have h2 : 2 * L < ((q : ℝ) + 4) * Δ := (div_lt_iff₀ hΔ).1 h1
    have hηL : η * L < Δ / 2 := by
      dsimp only [η]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    dsimp only [L] at hηL
    nlinarith
  have hγ : 0 < (1 - c) / 2 := by linarith
  have hδ_zero : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((1 - c) / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => 4 * ((k n : ℝ) / (n : ℝ)) + (n : ℝ) ^ (-((1 - c) / 2)))
      atTop (𝓝 0) := by
    simpa using (hk_small.const_mul 4).add hδ_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => by positivity) ?_
  have hk_quarter : ∀ᶠ n : ℕ in atTop, 4 * ((k n : ℝ) / (n : ℝ)) ≤ 1 / 4 :=
    (hk_small.const_mul 4).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hM_ev, hdeg r q, hnon, hp_pos, hk_quarter, eventually_ge_atTop 4] with
    n ⟨hM_lo, hM_hi⟩ hdeg_n hnon_n hpn hk_q hn4
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM_ge : (1 / ((r : ℝ) + 2)) * (n : ℝ) ≤ (#(M n) : ℝ) := by nlinarith
  have hI_half : (1 / 2) * (n : ℝ) ≤ (#(M n)ᶜ : ℝ) := by
    have hle : #(M n) ≤ n := by simpa using Finset.card_le_univ (M n)
    have hsum : (#(M n)ᶜ : ℝ) + (#(M n) : ℝ) = (n : ℝ) := by
      have : #(M n)ᶜ + #(M n) = n := by rw [Finset.card_compl, Fintype.card_fin]; omega
      exact_mod_cast this
    nlinarith
  have hI_ge : (1 / ((r : ℝ) + 2)) * (n : ℝ) ≤ (#(M n)ᶜ : ℝ) := by nlinarith
  have h4k_q : 4 * (k n : ℝ) ≤ (1 / 4) * (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hk_q hn_pos.le
    rw [mul_div_assoc', div_mul_cancel₀ _ hn_pos.ne'] at h1
    linarith
  have hgap : Δ ≤ ((1 - (#(M n) : ℝ) / n) * F.payoff₁ s s + ((#(M n) : ℝ) / n) * F.payoff₁ s t) -
      ((1 - (#(M n) : ℝ) / n) * F.payoff₁ t s + ((#(M n) : ℝ) / n) * F.payoff₁ t t) :=
    hg_ge ((#(M n) : ℝ) / (n : ℝ)) ((le_div_iff₀ hn_pos).2 hM_lo.le)
      ((div_le_iff₀ hn_pos).2 hM_hi.le)
  have hsurv := survivingMutants_card_le_of_regular_and_nonNeighborhood F (G n) (M n) s t
    hpn hη0.le hη_half (lt_of_lt_of_le (by positivity) hM_lo.le) hI_half h4k_q hgap hη_sum
    (hdeg_n (M n) hM_ge) (hdeg_n (M n)ᶜ hI_ge) hnon_n
  calc ((F.survivingMutants (G n) (M n) s t).card : ℝ) / (n : ℝ)
      ≤ (4 * (k n : ℝ) + (n : ℝ) ^ (-((1 - c) / 2)) * (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsurv hn_pos.le
    _ = 4 * ((k n : ℝ) / (n : ℝ)) + (n : ℝ) ^ (-((1 - c) / 2)) := by field_simp

/-! ### Exercise 29.7: adversarial mutant beating all incumbent neighbors -/

/-- A symmetric `2 × 2` positive-payoff witness game for [Suri2007], Exercise 29.7 (p. 736):
`A = !![3, 2; 3, 1]`, `B = Aᵀ`. Pure strategy `![1, 0]` is a classical ESS (`A 1 0 = A 0 0 = 3`
and `A 1 1 = 1 < 2 = A 0 1`), while under mutant strategy `![0, 1]`, an incumbent has fitness
`3 - ρ_i` and a mutant has fitness `3 - 2 * ρ_j`. Hence any non-isolated mutant `j` with no mutant
neighbors achieves fitness `3`, strictly exceeding every neighbor `i` (which has `ρ_i > 0`). -/
def survivorWitnessGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![3, 2; 3, 1], !![3, 2; 3, 1]ᵀ⟩

@[simp]
theorem survivorWitnessGame_A : survivorWitnessGame.A = !![3, 2; 3, 1] := by
  rw [survivorWitnessGame]

theorem survivorWitnessGame_symm : survivorWitnessGame.B = survivorWitnessGame.Aᵀ := by
  rw [survivorWitnessGame]

theorem survivorWitnessGame_isESS : survivorWitnessGame.IsESS ![1, 0] := by
  rw [isESS_fin_two_iff]
  refine ⟨isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]⟩, Or.inl ⟨rfl, Or.inr ⟨?_, ?_⟩⟩⟩ <;>
    norm_num [survivorWitnessGame]

/-- Deterministic core of Exercise 29.7: in `survivorWitnessGame`, if vertex `j ∈ M` has at least
one neighbor and no neighbor in `M`, then `j` has an incumbent neighbor and strictly higher
fitness than every incumbent neighbor. -/
private theorem survivorWitnessGame_beats_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (M : Finset (Fin n)) {j : Fin n} (hjM : j ∈ M)
    (hnoniso : ¬G.IsIsolated j) (hdisj : Disjoint (G.neighborSet j) (M : Set (Fin n))) :
    (∃ i, i ∉ M ∧ G.Adj j i) ∧
      ∀ i, i ∉ M → G.Adj j i →
        survivorWitnessGame.graphFitness G (fun u => if u ∈ M then ![0, 1] else ![1, 0]) i <
          survivorWitnessGame.graphFitness G (fun u => if u ∈ M then ![0, 1] else ![1, 0]) j := by
  have hpay_ss : survivorWitnessGame.payoff₁ ![1, 0] ![1, 0] = 3 := by
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame, Fin.sum_univ_two]
  have hpay_st : survivorWitnessGame.payoff₁ ![1, 0] ![0, 1] = 2 := by
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame, Fin.sum_univ_two]
  have hpay_ts : survivorWitnessGame.payoff₁ ![0, 1] ![1, 0] = 3 := by
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame, Fin.sum_univ_two]
  have hpay_tt : survivorWitnessGame.payoff₁ ![0, 1] ![0, 1] = 1 := by
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame, Fin.sum_univ_two]
  have hex : ∃ i, i ∉ M ∧ G.Adj j i := by
    by_contra! hnone
    apply hnoniso
    intro v hv
    exact hnone v (fun hvM => Set.disjoint_left.1 hdisj ((G.mem_neighborSet j v).2 hv) hvM) hv
  refine ⟨hex, fun i hiM hji => ?_⟩
  have hfit_j := graphFitness_twoStrategy survivorWitnessGame G M ![1, 0] ![0, 1] j
  simp only [hjM, ↓reduceIte, hpay_ts, hpay_tt] at hfit_j
  have hMj : ((M : Set (Fin n)) ∩ G.neighborSet j).ncard = 0 := by
    rw [Set.inter_comm, hdisj.inter_eq, Set.ncard_empty]
  have hIj_pos : 0 < (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet j).ncard := by
    obtain ⟨w, hwM, hjw⟩ := hex
    exact (Set.ncard_pos (Set.toFinite _)).2
      ⟨w, Finset.mem_compl.2 hwM, (G.mem_neighborSet j w).2 hjw⟩
  have hfit_j_eq :
      survivorWitnessGame.graphFitness G (fun u => if u ∈ M then ![0, 1] else ![1, 0]) j = 3 := by
    rw [hfit_j, hMj, Nat.cast_zero, zero_mul, add_zero, add_zero]
    have hpos : (0 : ℝ) < (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet j).ncard := by
      exact_mod_cast hIj_pos
    field_simp
  have hfit_i := graphFitness_twoStrategy survivorWitnessGame G M ![1, 0] ![0, 1] i
  simp only [hiM, ↓reduceIte, hpay_ss, hpay_st] at hfit_i
  have hMi_pos : 0 < ((M : Set (Fin n)) ∩ G.neighborSet i).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨j, hjM, (G.mem_neighborSet i j).2 hji.symm⟩
  have hMi_r : (0 : ℝ) < ((M : Set (Fin n)) ∩ G.neighborSet i).ncard := by exact_mod_cast hMi_pos
  have hIi_r : (0 : ℝ) ≤ (((Mᶜ : Finset (Fin n)) : Set (Fin n)) ∩ G.neighborSet i).ncard :=
    Nat.cast_nonneg _
  rw [hfit_j_eq, hfit_i, div_lt_iff₀ (by linarith)]
  linarith

/-- Shared tail bound for vertex `0` being isolated in `G(Fin n, p n)` when
`p n = Ω(1 / n ^ c)`. -/
private theorem eventually_isIsolated_zero_le_exp {p : ℕ → I} {c a : ℝ} (ha : 0 < a)
    (hp_lo : ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ hn0 : 0 < n,
      G(Fin n, p n).real {G | G.IsIsolated ⟨0, hn0⟩} ≤
        Real.exp (-((a / 2) * (n : ℝ) ^ (1 - c))) := by
  filter_upwards [hp_lo, eventually_ge_atTop 2] with n hpn hn2 hn0
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hiso : G(Fin n, p n).real {G | G.IsIsolated ⟨0, hn0⟩} = (1 - (p n : ℝ)) ^ (n - 1) := by
    have h := binomialRandom_real_isIsolated (V := Fin n) (p n) ⟨0, hn0⟩
    simpa [Fintype.card_fin] using h
  rw [hiso]
  have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  exact Real.one_sub_pow_le_exp (unitInterval.le_one (p n))
    (mul_rpow_one_sub_le_mul_p hn_pos ha.le hhalf hpn)

private theorem survivorWitness_mutant_isMixed : IsMixedStrategy (![0, 1] : Fin 2 → ℝ) :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩

private theorem survivorWitness_mutant_ne : (![0, 1] : Fin 2 → ℝ) ≠ ![1, 0] := fun h => by
  have h0 := congrFun h 0; norm_num at h0

/-- **Exercise 29.7 (linear-size adversary, `p` bounded away from `1`)** ([Suri2007], p. 736):
there exists a symmetric `2 × 2` game `F` (`survivorWitnessGame`), a classical ESS `s`
(`![1, 0]`), and a mutant mixed strategy `t ≠ s` (`![0, 1]`) such that for every
`p n = Ω(1 / n ^ c)` (`c < 1`) bounded away from `1` (`∃ q < 1, ∀ᶠ n, p n ≤ q`), almost surely
(`∀ᵐ`) under `Measure.infinitePi (fun n => G(Fin n, p n))`, for every `ε' > 0` an adversary can
construct an `ε'`-linear mutant family `M` such that eventually in `n` there is a mutant `j ∈ M n`
that has at least one incumbent neighbor and strictly higher fitness than every incumbent neighbor.

By `IsESS.eventually_forall_graphFitness_lt_complete`, bounding `p` away from `1` is necessary
when `M` is required to be `ε'`-linear (at `p = 1`, `G_n = K_n` and every mutant has strictly
lower fitness than every incumbent). -/
theorem exists_game_adversarial_linear_mutant_beats_all_incumbent_neighbors :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s t : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsESS s ∧ IsMixedStrategy t ∧ t ≠ s ∧
      ∀ {p : ℕ → I} {c : ℝ}, c < 1 →
        (∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) →
        (∃ q < (1 : ℝ), ∀ᶠ n : ℕ in atTop, (p n : ℝ) ≤ q) →
        ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)),
          ∀ ε' > 0, ∃ M : ∀ n, Finset (Fin n), IsEpsLinear ε' M ∧
            ∀ᶠ n : ℕ in atTop, ∃ j ∈ M n,
              (∃ i, i ∉ M n ∧ (G n).Adj j i) ∧
              ∀ i, i ∉ M n → (G n).Adj j i →
                F.graphFitness (G n) (fun u => if u ∈ M n then t else s) i <
                  F.graphFitness (G n) (fun u => if u ∈ M n then t else s) j := by
  refine ⟨survivorWitnessGame, ![1, 0], ![0, 1], survivorWitnessGame_symm,
    survivorWitnessGame_isESS, survivorWitness_mutant_isMixed, survivorWitness_mutant_ne, ?_⟩
  intro p c hc1 ⟨a, ha, hp_lo⟩ ⟨q, hq1, hp_hi⟩
  let q' : ℝ := max q (1 / 2)
  have hq'_pos : 0 < q' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq'_lt1 : q' < 1 := max_lt hq1 (by norm_num)
  let δ : ℝ := (1 - q') / (2 * q')
  have hδ0 : 0 < δ := div_pos (sub_pos.2 hq'_lt1) (by linarith)
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by linarith)]
    have : 1 / 2 ≤ q' := le_max_right _ _
    linarith
  have h1δ : (1 + δ) * q' = (1 + q') / 2 := by dsimp only [δ]; field_simp; ring
  let B_deg : ∀ n : ℕ, Set (SimpleGraph (Fin n)) := fun n =>
    if h : 0 < n then
      {G | ((1 + q') / 2) * (n : ℝ) ≤ ((G.neighborSet ⟨0, h⟩).ncard : ℝ)}
    else ∅
  let B_iso : ∀ n : ℕ, Set (SimpleGraph (Fin n)) := fun n =>
    if h : 0 < n then {G | G.IsIsolated ⟨0, h⟩} else ∅
  have hae_deg : ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)),
      ∀ᶠ n : ℕ in atTop, G n ∉ B_deg n := by
    refine ae_eventually_notMem_infinitePi_of_summable B_deg ?_
    let α0 : ℝ := δ ^ 2 * q' / 3
    have hα0 : 0 < α0 := by positivity
    have hgeom : Summable fun n : ℕ => (Real.exp (-α0)) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))
    refine Summable.of_norm_bounded_eventually_nat hgeom ?_
    filter_upwards [hp_hi, eventually_ge_atTop 1] with n hpn hn1
    have hn0 : 0 < n := by omega
    rw [Real.norm_of_nonneg measureReal_nonneg, ← Real.exp_nat_mul]
    simp only [B_deg, hn0, ↓reduceDIte]
    have hμ : ((Fintype.card (Fin n) - 1 : ℕ) : ℝ) * (p n : ℝ) ≤ q' * (n : ℝ) := by
      rw [Fintype.card_fin]
      have hsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      have hpq' : (p n : ℝ) ≤ q' := hpn.trans (le_max_left _ _)
      calc ((n - 1 : ℕ) : ℝ) * (p n : ℝ) ≤ (n : ℝ) * q' :=
            mul_le_mul hsub hpq' (unitInterval.nonneg _) (Nat.cast_nonneg n)
        _ = q' * (n : ℝ) := mul_comm _ _
    have h := binomialRandom_real_degree_ge_one_add_mul_of_le_one (V := Fin n) (p n) ⟨0, hn0⟩
      hμ hδ0.le hδ1
    have hmul : (1 + δ) * (q' * (n : ℝ)) = ((1 + q') / 2) * (n : ℝ) := by rw [← mul_assoc, h1δ]
    rw [hmul] at h
    refine h.trans (Real.exp_le_exp.2 ?_)
    dsimp only [α0]
    linarith
  have hae_iso : ∀ᵐ G ∂(Measure.infinitePi fun n : ℕ => G(Fin n, p n)),
      ∀ᶠ n : ℕ in atTop, G n ∉ B_iso n := by
    refine ae_eventually_notMem_infinitePi_of_summable B_iso ?_
    have h1c : 0 < 1 - c := sub_pos.2 hc1
    have hlog_bd : ∀ᶠ n : ℕ in atTop, 2 * Real.log (n : ℝ) ≤ (a / 2) * (n : ℝ) ^ (1 - c) := by
      have hlim := tendsto_log_div_rpow_nat h1c
      filter_upwards [hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < a / 4)),
        eventually_ge_atTop 1] with n hn hn1
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have h1 := (div_le_iff₀ (Real.rpow_pos_of_pos hn_pos (1 - c))).1 hn
      linarith
    have hinv2 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.2 one_lt_two
    refine Summable.of_norm_bounded_eventually_nat hinv2 ?_
    filter_upwards [eventually_isIsolated_zero_le_exp ha hp_lo, hlog_bd,
      eventually_ge_atTop 2] with n hiso hlog hn2
    have hn0 : 0 < n := by omega
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.norm_of_nonneg measureReal_nonneg]
    simp only [B_iso, hn0, ↓reduceDIte]
    refine (hiso hn0).trans ?_
    calc Real.exp (-((a / 2) * (n : ℝ) ^ (1 - c)))
        ≤ Real.exp (-(2 * Real.log (n : ℝ))) := Real.exp_le_exp.2 (by linarith)
      _ = (Real.exp (Real.log ((n : ℝ) ^ 2)))⁻¹ := by rw [Real.exp_neg, Real.log_pow]; norm_num
      _ = (1 : ℝ) / ((n : ℝ) ^ 2) := by rw [Real.exp_log (by positivity), one_div]
  filter_upwards [hae_deg, hae_iso] with G hdeg h_iso ε' hε'
  classical
  let θ : ℝ := min (ε' / 2) ((1 - q') / 4)
  have hθ0 : 0 < θ := lt_min (by linarith) (by linarith)
  have hθ_lt : θ < ε' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hθ_q : θ ≤ (1 - q') / 4 := min_le_right _ _
  let outside (n : ℕ) (h : 0 < n) : Finset (Fin n) :=
    (univ : Finset (Fin n)).filter fun v => v ≠ ⟨0, h⟩ ∧ ¬(G n).Adj ⟨0, h⟩ v
  let M : ∀ n : ℕ, Finset (Fin n) := fun n =>
    if h : 0 < n then
      if hm : ⌊θ * (n : ℝ)⌋₊ ≤ #(outside n h) then
        insert ⟨0, h⟩ (Finset.exists_subset_card_eq hm).choose
      else {⟨0, h⟩}
    else ∅
  have hgood_n : ∀ᶠ n : ℕ in atTop, ∃ h : 0 < n,
      ⌊θ * (n : ℝ)⌋₊ ≤ #(outside n h) ∧ ¬(G n).IsIsolated ⟨0, h⟩ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (1 - q') + 2)
    filter_upwards [hdeg, h_iso, eventually_ge_atTop N] with n hd hi hnN
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_of_lt_of_le (by positivity)
        (le_trans hN.le (by exact_mod_cast hnN))
      exact_mod_cast this
    simp only [B_deg, B_iso, hn0, ↓reduceDIte, Set.mem_ofPred_eq, not_le] at hd hi
    refine ⟨hn0, ?_, hi⟩
    have hcard_out : #(outside n hn0) + (((G n).neighborSet ⟨0, hn0⟩).ncard) + 1 = n := by
      have hnb : (((G n).neighborSet ⟨0, hn0⟩).ncard) = #((G n).neighborFinset ⟨0, hn0⟩) := by
        rw [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
      rw [hnb]
      have hpart : outside n hn0 ∪ (G n).neighborFinset ⟨0, hn0⟩ ∪ {⟨0, hn0⟩} = univ := by
        ext v
        simp only [Finset.mem_union, Finset.mem_singleton, mem_univ, true_and, iff_true, outside,
          Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        by_cases hv0 : v = ⟨0, hn0⟩
        · exact Or.inr hv0
        · by_cases hadj : (G n).Adj ⟨0, hn0⟩ v
          · exact Or.inl (Or.inr hadj)
          · exact Or.inl (Or.inl ⟨hv0, hadj⟩)
      have hd1 : Disjoint (outside n hn0) ((G n).neighborFinset ⟨0, hn0⟩) := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        exact (Finset.mem_filter.1 hv1).2.2 (((G n).mem_neighborFinset ⟨0, hn0⟩ v).1 hv2)
      have hd2 : Disjoint (outside n hn0 ∪ (G n).neighborFinset ⟨0, hn0⟩) {⟨0, hn0⟩} := by
        rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]
        exact ⟨fun h => (Finset.mem_filter.1 h).2.1 rfl,
          fun h => (G n).irrefl (((G n).mem_neighborFinset ⟨0, hn0⟩ ⟨0, hn0⟩).1 h)⟩
      have hsum := congrArg Finset.card hpart
      rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hsum
      exact hsum
    have hn_gt : 4 / (1 - q') < (n : ℝ) := lt_of_lt_of_le (by linarith)
      (le_trans hN.le (by exact_mod_cast hnN))
    have hq_n : 4 < (1 - q') * (n : ℝ) := by linarith [(div_lt_iff₀ (sub_pos.2 hq'_lt1)).1 hn_gt]
    have hreal : (#(outside n hn0) : ℝ) +
        (((G n).neighborSet ⟨0, hn0⟩).ncard : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast hcard_out
    have hfl : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (by positivity)
    have hle_real : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ (#(outside n hn0) : ℝ) := by nlinarith
    exact_mod_cast hle_real
  refine ⟨M, ?_, ?_⟩
  · refine ⟨θ / 2, by linarith, by linarith, ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (ε' - θ) + 2 / θ + 2)
    filter_upwards [hgood_n, eventually_ge_atTop N] with n ⟨hn0, hm, _⟩ hnN
    have hcardM : #(M n) = ⌊θ * (n : ℝ)⌋₊ + 1 := by
      simp only [M, hn0, hm, ↓reduceDIte]
      have hspec := (Finset.exists_subset_card_eq hm).choose_spec
      have h0not : ⟨0, hn0⟩ ∉ (Finset.exists_subset_card_eq hm).choose := fun hmem =>
        (Finset.mem_filter.1 (hspec.1 hmem)).2.1 rfl
      rw [Finset.card_insert_of_notMem h0not, hspec.2]
    rw [hcardM, Nat.cast_add, Nat.cast_one]
    have hfl_le : (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (by positivity)
    have hfl_gt : θ * (n : ℝ) < (⌊θ * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hn_gt1 : 2 / (ε' - θ) < (n : ℝ) := by
      have : 0 < 2 / θ := by positivity
      exact lt_of_lt_of_le (by linarith) (le_trans hN.le (by exact_mod_cast hnN))
    have hgap1 : 2 < (ε' - θ) * (n : ℝ) := by
      linarith [(div_lt_iff₀ (sub_pos.2 hθ_lt)).1 hn_gt1]
    constructor
    · have : 0 < 2 / (ε' - θ) := by positivity
      have hn_pos : (0 : ℝ) < n := by linarith
      nlinarith
    · linarith
  · filter_upwards [hgood_n] with n ⟨hn0, hm, hnoniso⟩
    have hspec := (Finset.exists_subset_card_eq hm).choose_spec
    have hM_eq : M n = insert ⟨0, hn0⟩ (Finset.exists_subset_card_eq hm).choose := by
      simp only [M, hn0, hm, ↓reduceDIte]
    have h0M : ⟨0, hn0⟩ ∈ M n := by rw [hM_eq]; exact Finset.mem_insert_self _ _
    have hdisj : Disjoint ((G n).neighborSet ⟨0, hn0⟩) (M n : Set (Fin n)) := by
      rw [Set.disjoint_left]
      intro v hv_adj hvM
      rw [Finset.mem_coe, hM_eq, Finset.mem_insert] at hvM
      rcases hvM with rfl | hvS
      · exact (G n).irrefl (((G n).mem_neighborSet _ _).1 hv_adj)
      · exact (Finset.mem_filter.1 (hspec.1 hvS)).2.2 (((G n).mem_neighborSet _ _).1 hv_adj)
    exact ⟨⟨0, hn0⟩, h0M, survivorWitnessGame_beats_neighbors (G n) (M n) h0M hnoniso hdisj⟩

/-- **Exercise 29.7 (unconstrained mutant set size, all `p n = Ω(1 / n ^ c)` including `p = 1`)**
([Suri2007], p. 736; cf. Vickery 1987, p. 734): for `survivorWitnessGame` with classical ESS
`![1, 0]` and mutant `![0, 1]`, for every `p n = Ω(1 / n ^ c)` (`0 ≤ c < 1`), with probability
tending to `1` in `G(Fin n, p n)`, the singleton mutant set `{0}` contains a mutant with an
incumbent neighbor and strictly higher fitness than all of its incumbent neighbors. -/
theorem exists_game_adversarial_mutant_beats_all_incumbent_neighbors :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s t : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsESS s ∧ IsMixedStrategy t ∧ t ≠ s ∧
      ∀ {p : ℕ → I} {c : ℝ}, c < 1 →
        (∃ a > 0, ∀ᶠ n : ℕ in atTop, a / (n : ℝ) ^ c ≤ (p n : ℝ)) →
        Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∃ M : Finset (Fin n), ∃ j ∈ M,
          (∃ i, i ∉ M ∧ G.Adj j i) ∧
          ∀ i, i ∉ M → G.Adj j i →
            F.graphFitness G (fun u => if u ∈ M then t else s) i <
              F.graphFitness G (fun u => if u ∈ M then t else s) j}) atTop (𝓝 1) := by
  refine ⟨survivorWitnessGame, ![1, 0], ![0, 1], survivorWitnessGame_symm,
    survivorWitnessGame_isESS, survivorWitness_mutant_isMixed, survivorWitness_mutant_ne, ?_⟩
  intro p c hc1 ⟨a, ha, hp_lo⟩
  have h1c : 0 < 1 - c := sub_pos.2 hc1
  have hlim_exp : Tendsto (fun n : ℕ => Real.exp (-((a / 2) * (n : ℝ) ^ (1 - c)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (((tendsto_rpow_atTop h1c).comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity))
  have hlow : Tendsto (fun n : ℕ => 1 - Real.exp (-((a / 2) * (n : ℝ) ^ (1 - c)))) atTop (𝓝 1) := by
    simpa using hlim_exp.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => measureReal_le_one)
  filter_upwards [eventually_isIsolated_zero_le_exp ha hp_lo, eventually_ge_atTop 2] with n hiso hn2
  have hn0 : 0 < n := by omega
  have hsub : {G : SimpleGraph (Fin n) | ¬G.IsIsolated ⟨0, hn0⟩} ⊆
      {G | ∃ M : Finset (Fin n), ∃ j ∈ M, (∃ i, i ∉ M ∧ G.Adj j i) ∧
        ∀ i, i ∉ M → G.Adj j i →
          survivorWitnessGame.graphFitness G
              (fun u => if u ∈ M then ![0, 1] else ![1, 0]) i <
            survivorWitnessGame.graphFitness G
              (fun u => if u ∈ M then ![0, 1] else ![1, 0]) j} := by
    intro G hG
    refine ⟨{⟨0, hn0⟩}, ⟨0, hn0⟩, Finset.mem_singleton_self _, ?_⟩
    have hdisj :
        Disjoint (G.neighborSet ⟨0, hn0⟩) (({⟨0, hn0⟩} : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_singleton, Set.disjoint_singleton_right]
      exact fun h => G.irrefl ((G.mem_neighborSet _ _).1 h)
    exact survivorWitnessGame_beats_neighbors G {⟨0, hn0⟩} (Finset.mem_singleton_self _) hG hdisj
  have hcompl : G(Fin n, p n).real {G | ¬G.IsIsolated ⟨0, hn0⟩} =
      1 - G(Fin n, p n).real {G | G.IsIsolated ⟨0, hn0⟩} := by
    have h1 := probReal_compl_eq_one_sub (μ := G(Fin n, p n))
      (s := {G | G.IsIsolated ⟨0, hn0⟩}) MeasurableSet.of_discrete
    have hset : ({G : SimpleGraph (Fin n) | G.IsIsolated ⟨0, hn0⟩})ᶜ =
        {G | ¬G.IsIsolated ⟨0, hn0⟩} := rfl
    rw [← hset, h1]
  have hmono := measureReal_mono hsub (measure_ne_top G(Fin n, p n) _)
  linarith [hiso hn0]

end Cslib.GameTheory.BimatrixGame
