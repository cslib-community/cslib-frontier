/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Probability.Azuma
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Multi-armed bandit feedback protocols and regret

In a `K`-armed bandit problem (`ι` a finite type of arms), a learner interacts with an environment
over `T` rounds under *partial-information (bandit) feedback*: in each round the learner selects a
single arm `a : ι` and observes **only** the scalar feedback `value : ℝ` (loss or reward) of that
pulled arm (`BanditStep`), never the counterfactual values of the unpulled arms
([AuerCesaBianchiFischer2002, §2]; [AuerCesaBianchiFreundSchapire2002, §2];
[BubeckCesaBianchi2012, §1.1]).

Because both `DeterministicPolicy` (`List (BanditStep ι) → ι`) and `RandomizedPolicy`
(`List (BanditStep ι) → PMF ι`) take only the `List (BanditStep ι)` transcript of earlier rounds,
causality and single-arm bandit feedback are enforced directly by the type signature.

This module sets up the two standard protocols and their regret benchmarks:

1. **Oblivious-adversarial `K`-armed bandits** (`ObliviousBandit`, `trajectoryPMF`, `expectedTotal`,
   `ObliviousBandit.pseudoRegret`): an oblivious adversary fixes a table `loss : ℕ → ι → ℝ` with
   entries in `[0, 1]` before interaction begins. Over `T` rounds, `pol : RandomizedPolicy ι`
   induces the sequential trajectory distribution `trajectoryPMF pol env T : PMF (Fin T → ι)`. Since
   the comparator `min_i ∑_{t < T} loss t i` is deterministic against an oblivious environment,
   expected regret against the best fixed arm coincides with pseudo-regret
   (`ObliviousBandit.pseudoRegret_eq_expectedRegret`,
   `ObliviousBandit.pseudoRegret_eq_sup_regretAt`).
2. **Stochastic `K`-armed bandits** (`StochasticBandit`, `runStochastic`,
   `StochasticBandit.expectedPulls`, `StochasticBandit.stochasticRegret`,
   `StochasticBandit.pseudoRegret`): following [AuerCesaBianchiFischer2002, §2] (locator not
   re-verified against primary PDF), each arm `i : ι` has an arbitrary reward probability measure
   `B.law i` on `ℝ` supported a.e. in `[0, 1]`, and successive plays of arm `i` yield independent
   draws from `B.law i` (`B.sampleMeasure T`). For every Borel-measurable `DeterministicPolicy`
   (`DeterministicPolicy.IsMeasurable`), Wald's identity
   (`StochasticBandit.stochasticRegret_eq_pseudoRegret`) identifies expected cumulative regret
   `T * μ* - 𝔼[∑_{t < T} r_t]` with the gap-weighted pull sum `∑ i, Δ_i * 𝔼[N_i(T)]`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Bandits.BanditStep`: one round's single-arm observation
  (`arm` and `value`).
* `Cslib.MachineLearning.OnlineLearning.Bandits.DeterministicPolicy`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.RandomizedPolicy`: causal partial-information
  bandit policies.
* `Cslib.MachineLearning.OnlineLearning.Bandits.pullCount`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.feedbackSum`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.empiricalMean`: per-arm statistics of a bandit
  transcript.
* `Cslib.MachineLearning.OnlineLearning.Bandits.trajectoryPMF`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.expectedTotal`: sequential arm-trajectory `PMF` and
  expected cumulative feedback on an oblivious table.
* `Cslib.MachineLearning.OnlineLearning.Bandits.ObliviousBandit`: `[0, 1]`-loss oblivious
  adversarial bandit environment and its regret / pseudo-regret.
* `Cslib.MachineLearning.OnlineLearning.Bandits.StochasticBandit`: stationary `[0, 1]`-reward
  stochastic bandit environment, successive-play sample space, and expected / pseudo-regret.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Bandits.expectedTotal_succ`: one-step conditional
  expectation recursion for `expectedTotal`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.ObliviousBandit.pseudoRegret_eq_expectedRegret`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.ObliviousBandit.pseudoRegret_eq_sup_regretAt`:
  equivalence of oblivious expected regret, pseudo-regret, and worst-comparator regret.
* `Cslib.MachineLearning.OnlineLearning.Bandits.StochasticBandit.expectedReward_eq_sum_mean`:
  Wald's identity for stochastic bandits.
* `Cslib.MachineLearning.OnlineLearning.Bandits.StochasticBandit.stochasticRegret_eq_pseudoRegret`:
  gap decomposition of stochastic regret.

## References

* [P. Auer, N. Cesa-Bianchi, P. Fischer, *Finite-Time Analysis of the Multiarmed Bandit
  Problem*][AuerCesaBianchiFischer2002]
* [P. Auer, N. Cesa-Bianchi, Y. Freund, R. E. Schapire, *The Nonstochastic Multiarmed Bandit
  Problem*][AuerCesaBianchiFreundSchapire2002]
* [S. Bubeck, N. Cesa-Bianchi, *Regret Analysis of Stochastic and Nonstochastic Multi-Armed Bandit
  Problems*][BubeckCesaBianchi2012]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Bandits

open Finset MeasureTheory
open scoped BigOperators

/-! ### Bandit transcripts, policies, and per-arm statistics -/

/-- One round's bandit observation: the arm `arm` pulled by the learner and the scalar feedback
`value` (loss or reward) observed on that arm alone. -/
structure BanditStep (ι : Type*) where
  /-- The arm pulled in that round. -/
  arm : ι
  /-- The scalar feedback (loss or reward) observed on `arm` in that round. -/
  value : ℝ

/-- A deterministic partial-information bandit policy: chooses the next arm solely as a function of
the list of `(arm, value)` observations from previous rounds. -/
structure DeterministicPolicy (ι : Type*) where
  /-- Next arm chosen after observing `hist`. -/
  choose : List (BanditStep ι) → ι

/-- A randomized partial-information bandit policy: maps the list of `(arm, value)` observations
from previous rounds to a discrete probability distribution over arms. -/
structure RandomizedPolicy (ι : Type*) where
  /-- Distribution over the next arm after observing `hist`. -/
  play : List (BanditStep ι) → PMF ι

/-- A deterministic bandit policy is Borel-measurable if, for every history length `t` and past arm
sequence `arms : Fin t → ι`, each decision fiber `{vals : Fin t → ℝ | pol.choose ... = i}` is
measurable. -/
def DeterministicPolicy.IsMeasurable {ι : Type*} (pol : DeterministicPolicy ι) : Prop :=
  ∀ (t : ℕ) (arms : Fin t → ι) (i : ι),
    MeasurableSet {vals : Fin t → ℝ | pol.choose (List.ofFn fun r => ⟨arms r, vals r⟩) = i}

theorem DeterministicPolicy.isMeasurable_def {ι : Type*} (pol : DeterministicPolicy ι) :
    pol.IsMeasurable = ∀ (t : ℕ) (arms : Fin t → ι) (i : ι),
      MeasurableSet {vals : Fin t → ℝ | pol.choose (List.ofFn fun r => ⟨arms r, vals r⟩) = i} := by
  rw [IsMeasurable]

section Stats

variable {ι : Type*} [DecidableEq ι]

/-- Number of times arm `i` was pulled in `hist`. -/
def pullCount (hist : List (BanditStep ι)) (i : ι) : ℕ :=
  hist.countP (fun s => decide (s.arm = i))

/-- Cumulative scalar feedback observed on arm `i` in `hist`. -/
def feedbackSum (hist : List (BanditStep ι)) (i : ι) : ℝ :=
  (hist.map fun s => if s.arm = i then s.value else 0).sum

/-- Empirical mean feedback observed on arm `i` in `hist` (`0` when `pullCount hist i = 0`). -/
noncomputable def empiricalMean (hist : List (BanditStep ι)) (i : ι) : ℝ :=
  feedbackSum hist i / pullCount hist i

theorem empiricalMean_def (hist : List (BanditStep ι)) (i : ι) :
    empiricalMean hist i = feedbackSum hist i / pullCount hist i := by
  rw [empiricalMean]

@[simp]
theorem pullCount_nil (i : ι) : pullCount ([] : List (BanditStep ι)) i = 0 := by
  simp [pullCount]

@[simp]
theorem pullCount_cons (s : BanditStep ι) (hist : List (BanditStep ι)) (i : ι) :
    pullCount (s :: hist) i = pullCount hist i + if s.arm = i then 1 else 0 := by
  simp [pullCount, List.countP_cons]

@[simp]
theorem pullCount_append (h₁ h₂ : List (BanditStep ι)) (i : ι) :
    pullCount (h₁ ++ h₂) i = pullCount h₁ i + pullCount h₂ i := by
  simp [pullCount, List.countP_append]

theorem pullCount_singleton (s : BanditStep ι) (i : ι) :
    pullCount [s] i = if s.arm = i then 1 else 0 := by
  simp [pullCount]

theorem pullCount_le_length (hist : List (BanditStep ι)) (i : ι) :
    pullCount hist i ≤ hist.length :=
  List.countP_le_length

@[simp]
theorem feedbackSum_nil (i : ι) : feedbackSum ([] : List (BanditStep ι)) i = 0 := by
  simp [feedbackSum]

@[simp]
theorem feedbackSum_cons (s : BanditStep ι) (hist : List (BanditStep ι)) (i : ι) :
    feedbackSum (s :: hist) i = (if s.arm = i then s.value else 0) + feedbackSum hist i := by
  simp [feedbackSum]

@[simp]
theorem feedbackSum_append (h₁ h₂ : List (BanditStep ι)) (i : ι) :
    feedbackSum (h₁ ++ h₂) i = feedbackSum h₁ i + feedbackSum h₂ i := by
  simp [feedbackSum, List.map_append, List.sum_append]

theorem feedbackSum_singleton (s : BanditStep ι) (i : ι) :
    feedbackSum [s] i = if s.arm = i then s.value else 0 := by
  simp [feedbackSum]

@[simp]
theorem empiricalMean_nil (i : ι) : empiricalMean ([] : List (BanditStep ι)) i = 0 := by
  simp [empiricalMean]

/-- Across all arms, pull counts partition the transcript length. -/
theorem sum_pullCount_eq_length [Fintype ι] (hist : List (BanditStep ι)) :
    ∑ i : ι, pullCount hist i = hist.length := by
  induction hist with
  | nil => simp
  | cons s rest ih =>
    simp only [pullCount_cons, sum_add_distrib, ih, List.length_cons]
    simp

/-- Across all arms, per-arm feedback sums partition the total observed feedback. -/
theorem sum_feedbackSum_eq [Fintype ι] (hist : List (BanditStep ι)) :
    ∑ i : ι, feedbackSum hist i = (hist.map BanditStep.value).sum := by
  induction hist with
  | nil => simp
  | cons s rest ih =>
    simp only [feedbackSum_cons, sum_add_distrib, ih, List.map_cons, List.sum_cons]
    simp

theorem pullCount_ofFn {n : ℕ} (f : Fin n → BanditStep ι) (i : ι) :
    pullCount (List.ofFn f) i = (univ.filter fun r : Fin n => (f r).arm = i).card := by
  unfold pullCount
  rw [List.countP_ofFn]
  simp

theorem feedbackSum_ofFn {n : ℕ} (f : Fin n → BanditStep ι) (i : ι) :
    feedbackSum (List.ofFn f) i = ∑ r : Fin n, if (f r).arm = i then (f r).value else 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ, feedbackSum_cons, ih, Fin.sum_univ_succ]

end Stats

/-! ### Oblivious-adversarial bandit protocol -/

section Oblivious

/-- Reconstruct the bandit transcript observed along arm sequence `traj : Fin T → ι` against an
oblivious feedback table `env : ℕ → ι → ℝ`. Only `env t (traj t)` is recorded at round `t`. -/
def historyOfArms {ι : Type*} (env : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) :
    List (BanditStep ι) :=
  List.ofFn fun t => ⟨traj t, env t (traj t)⟩

theorem historyOfArms_def {ι : Type*} (env : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) :
    historyOfArms env traj = List.ofFn fun t => ⟨traj t, env t (traj t)⟩ := by
  rw [historyOfArms]

@[simp]
theorem historyOfArms_zero {ι : Type*} (env : ℕ → ι → ℝ) (traj : Fin 0 → ι) :
    historyOfArms env traj = [] := by
  simp [historyOfArms]

theorem historyOfArms_snoc {ι : Type*} (env : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) (a : ι) :
    historyOfArms env (Fin.snoc (α := fun _ => ι) traj a) =
      historyOfArms env traj ++ [⟨a, env T a⟩] := by
  apply List.ext_getElem (by simp [historyOfArms])
  intro n hn1 hn2
  have hn1' : n < T + 1 := by simpa [historyOfArms] using hn1
  by_cases hn : n < T
  · have hn_len : n < (historyOfArms env traj).length := by simpa [historyOfArms] using hn
    rw [List.getElem_append_left hn_len]
    simp only [historyOfArms, List.getElem_ofFn]
    have hcast : (⟨n, hn1'⟩ : Fin (T + 1)) = (⟨n, hn⟩ : Fin T).castSucc := rfl
    rw [hcast, Fin.snoc_castSucc]
  · have heq : n = T := by omega
    have hge : (historyOfArms env traj).length ≤ n := by simp [historyOfArms, heq]
    rw [List.getElem_append_right hge]
    simp only [historyOfArms, List.getElem_ofFn, List.length_ofFn]
    subst heq
    have hlast : (⟨n, hn1'⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [hlast, Fin.snoc_last]
    simp

@[simp]
theorem length_historyOfArms {ι : Type*} (env : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) :
    (historyOfArms env traj).length = T := by
  simp [historyOfArms]

/-- Sequential arm-trajectory distribution induced by `pol : RandomizedPolicy ι` over `T` rounds
against an oblivious feedback table `env : ℕ → ι → ℝ`, defined via
`Cslib.Probability.PMF.seqProcess`. -/
noncomputable def trajectoryPMF {ι : Type*} (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ)
    (T : ℕ) : PMF (Fin T → ι) :=
  Cslib.Probability.PMF.seqProcess (fun _ prev => pol.play (historyOfArms env prev)) T

@[simp]
theorem trajectoryPMF_zero {ι : Type*} (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ) :
    trajectoryPMF pol env 0 = PMF.pure Fin.elim0 := by
  rw [trajectoryPMF, Cslib.Probability.PMF.seqProcess]

theorem trajectoryPMF_succ {ι : Type*} (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ) (T : ℕ) :
    trajectoryPMF pol env (T + 1) =
      (trajectoryPMF pol env T).bind fun prev =>
        (pol.play (historyOfArms env prev)).map (Fin.snoc (α := fun _ => ι) prev) := by
  rw [trajectoryPMF, Cslib.Probability.PMF.seqProcess]
  rfl

/-- Expected cumulative feedback collected by `pol` over `T` rounds on `env`. -/
noncomputable def expectedTotal {ι : Type*} [Fintype ι] (pol : RandomizedPolicy ι)
    (env : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  ∑ traj : Fin T → ι, (trajectoryPMF pol env T traj).toReal * ∑ t : Fin T, env t (traj t)

theorem expectedTotal_def {ι : Type*} [Fintype ι] (pol : RandomizedPolicy ι)
    (env : ℕ → ι → ℝ) (T : ℕ) :
    expectedTotal pol env T =
      ∑ traj : Fin T → ι, (trajectoryPMF pol env T traj).toReal * ∑ t : Fin T, env t (traj t) := by
  rw [expectedTotal]

@[simp]
theorem expectedTotal_zero {ι : Type*} [Fintype ι] (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ) :
    expectedTotal pol env 0 = 0 := by
  simp [expectedTotal]

/-- One-step tower property for `expectedTotal`: round `T`'s expected contribution conditions on the
earlier `T`-round trajectory `prev`. -/
theorem expectedTotal_succ {ι : Type*} [Fintype ι] (pol : RandomizedPolicy ι)
    (env : ℕ → ι → ℝ) (T : ℕ) :
    expectedTotal pol env (T + 1) =
      expectedTotal pol env T +
        ∑ prev : Fin T → ι, (trajectoryPMF pol env T prev).toReal *
          ∑ a : ι, (pol.play (historyOfArms env prev) a).toReal * env T a := by
  unfold expectedTotal
  rw [trajectoryPMF_succ, Cslib.Probability.PMF.sum_bind_mul]
  have hstep : ∀ prev : Fin T → ι,
      (∑ b : Fin (T + 1) → ι,
          (((pol.play (historyOfArms env prev)).map (Fin.snoc (α := fun _ => ι) prev)) b).toReal *
            ∑ t : Fin (T + 1), env t (b t)) =
        (∑ t : Fin T, env t (prev t)) +
          ∑ a : ι, (pol.play (historyOfArms env prev) a).toReal * env T a := by
    intro prev
    rw [Cslib.Probability.PMF.sum_map_mul]
    have hsnoc : ∀ a : ι,
        (∑ t : Fin (T + 1), env t (Fin.snoc (α := fun _ => ι) prev a t)) =
          (∑ t : Fin T, env t (prev t)) + env T a := fun a => by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    simp only [hsnoc, mul_add, sum_add_distrib, ← sum_mul,
      Cslib.Probability.PMF.sum_toReal, one_mul]
  simp only [hstep, mul_add, sum_add_distrib]

theorem expectedTotal_nonneg {ι : Type*} [Fintype ι] (pol : RandomizedPolicy ι)
    {env : ℕ → ι → ℝ} {T : ℕ} (h0 : ∀ t < T, ∀ i, 0 ≤ env t i) :
    0 ≤ expectedTotal pol env T :=
  sum_nonneg fun traj _ => mul_nonneg ENNReal.toReal_nonneg
    (sum_nonneg fun t _ => h0 t t.isLt (traj t))

/-- An oblivious adversarial `K`-armed bandit environment with `[0, 1]`-bounded losses
([BubeckCesaBianchi2012, §1.1, §3], locator not re-verified against primary PDF). -/
structure ObliviousBandit (ι : Type*) where
  /-- Round-by-round loss assignment fixed before interaction begins. -/
  loss : ℕ → ι → ℝ
  /-- Every arm's loss in every round lies in `[0, 1]`. -/
  mem_unitInterval : ∀ t i, loss t i ∈ Set.Icc (0 : ℝ) 1

namespace ObliviousBandit

variable {ι : Type*} (E : ObliviousBandit ι)

/-- Cumulative loss of fixed arm `i` over the first `T` rounds. -/
def cumLoss (T : ℕ) (i : ι) : ℝ :=
  ∑ t ∈ range T, E.loss t i

/-- Minimum cumulative loss of any single fixed arm in hindsight over `T` rounds. -/
noncomputable def bestCumLoss [Fintype ι] [Nonempty ι] (T : ℕ) : ℝ :=
  univ.inf' univ_nonempty (E.cumLoss T)

/-- Expected cumulative loss of policy `pol` on `E` over `T` rounds. -/
noncomputable def expectedLoss [Fintype ι] (pol : RandomizedPolicy ι) (T : ℕ) : ℝ :=
  expectedTotal pol E.loss T

/-- Expected regret of `pol` against comparator arm `i` over `T` rounds. -/
noncomputable def regretAt [Fintype ι] (pol : RandomizedPolicy ι) (T : ℕ) (i : ι) : ℝ :=
  E.expectedLoss pol T - E.cumLoss T i

theorem regretAt_def [Fintype ι] (pol : RandomizedPolicy ι) (T : ℕ) (i : ι) :
    E.regretAt pol T i = expectedTotal pol E.loss T - ∑ t ∈ range T, E.loss t i := by
  rw [regretAt, expectedLoss, cumLoss]

/-- Pseudo-regret `𝔼[∑_{t < T} ℓ_t(I_t)] - min_{i} ∑_{t < T} ℓ_t(i)` of `pol` over `T` rounds
([BubeckCesaBianchi2012, (1.1), §3], locator not re-verified against primary PDF). -/
noncomputable def pseudoRegret [Fintype ι] [Nonempty ι] (pol : RandomizedPolicy ι) (T : ℕ) : ℝ :=
  E.expectedLoss pol T - E.bestCumLoss T

/-- Expected regret `𝔼[∑_{t < T} ℓ_t(I_t) - min_i ∑_{t < T} ℓ_t(i)]` against an oblivious
environment equals `pseudoRegret` because the hindsight comparator `bestCumLoss` is
deterministic. -/
theorem pseudoRegret_eq_expectedRegret [Fintype ι] [Nonempty ι] (pol : RandomizedPolicy ι)
    (T : ℕ) :
    E.pseudoRegret pol T =
      ∑ traj : Fin T → ι, (trajectoryPMF pol E.loss T traj).toReal *
        ((∑ t : Fin T, E.loss t (traj t)) - E.bestCumLoss T) := by
  simp only [pseudoRegret, expectedLoss, expectedTotal, mul_sub, sum_sub_distrib, ← sum_mul,
    Cslib.Probability.PMF.sum_toReal, one_mul]

/-- `pseudoRegret` equals the maximum of `regretAt pol T i` across all comparator arms `i : ι`. -/
theorem pseudoRegret_eq_sup_regretAt [Fintype ι] [Nonempty ι] (pol : RandomizedPolicy ι)
    (T : ℕ) :
    E.pseudoRegret pol T = univ.sup' univ_nonempty (E.regretAt pol T) := by
  apply le_antisymm
  · obtain ⟨i, _, hi⟩ := exists_mem_eq_inf' univ_nonempty (E.cumLoss T)
    have hle : E.regretAt pol T i ≤ univ.sup' univ_nonempty (E.regretAt pol T) :=
      le_sup' (E.regretAt pol T) (mem_univ i)
    unfold pseudoRegret bestCumLoss regretAt at *
    linarith
  · rw [Finset.sup'_le_iff]
    intro i _
    have hle : E.bestCumLoss T ≤ E.cumLoss T i := inf'_le (E.cumLoss T) (mem_univ i)
    unfold pseudoRegret regretAt
    linarith

/-- Bounding `regretAt` uniformly by `B` against every arm `i` bounds `pseudoRegret` by `B`. -/
theorem pseudoRegret_le_of_forall [Fintype ι] [Nonempty ι] {pol : RandomizedPolicy ι} {T : ℕ}
    {B : ℝ} (h : ∀ i : ι, E.regretAt pol T i ≤ B) :
    E.pseudoRegret pol T ≤ B := by
  rw [E.pseudoRegret_eq_sup_regretAt]
  exact (Finset.sup'_le_iff _ _).mpr fun i _ => h i

end ObliviousBandit

end Oblivious

/-! ### Stochastic bandit protocol and Wald's regret decomposition -/

section Stochastic

/-- A stationary stochastic `K`-armed bandit problem with `[0, 1]`-bounded rewards
([AuerCesaBianchiFischer2002, §2, Theorem 1]; [BubeckCesaBianchi2012, §2.1], locators not
re-verified against primary PDF): each arm `i : ι` has a probability measure `law i` on `ℝ`
supported almost surely in `[0, 1]`. -/
structure StochasticBandit (ι : Type*) where
  /-- Reward probability distribution of each arm `i`. -/
  law : ι → Measure ℝ
  /-- Each arm's reward law is a probability measure. -/
  isProb : ∀ i, IsProbabilityMeasure (law i)
  /-- Rewards lie almost surely in `[0, 1]`. -/
  mem_unitInterval : ∀ i, ∀ᵐ x ∂(law i), x ∈ Set.Icc (0 : ℝ) 1

attribute [instance] StochasticBandit.isProb

/-- Execute deterministic policy `pol` for `t` rounds against a successive-play reward table
`X : ι × Fin T → ℝ` ([AuerCesaBianchiFischer2002, §2]): the `(s + 1)`-th pull of arm `a`
(`s = pullCount hist a < T`) yields reward `X (a, ⟨s, hs⟩)`. -/
def runStochastic {ι : Type*} [DecidableEq ι] (pol : DeterministicPolicy ι) {T : ℕ}
    (X : ι × Fin T → ℝ) : ℕ → List (BanditStep ι)
  | 0 => []
  | t + 1 =>
      let hist := runStochastic pol X t
      let a := pol.choose hist
      let s := pullCount hist a
      hist ++ [⟨a, if hs : s < T then X (a, ⟨s, hs⟩) else 0⟩]

section RunProperties

variable {ι : Type*} [DecidableEq ι] (pol : DeterministicPolicy ι) {T : ℕ} (X : ι × Fin T → ℝ)

@[simp]
theorem runStochastic_zero : runStochastic pol X 0 = [] := by
  rw [runStochastic]

theorem runStochastic_succ (t : ℕ) :
    runStochastic pol X (t + 1) =
      let hist := runStochastic pol X t
      let a := pol.choose hist
      let s := pullCount hist a
      hist ++ [⟨a, if hs : s < T then X (a, ⟨s, hs⟩) else 0⟩] := by
  rw [runStochastic]

@[simp]
theorem length_runStochastic (t : ℕ) : (runStochastic pol X t).length = t := by
  induction t with
  | zero => simp [runStochastic_zero]
  | succ t ih => simp [runStochastic_succ, ih]

theorem runStochastic_succ_of_lt {t : ℕ} (ht : t < T) :
    runStochastic pol X (t + 1) =
      let hist := runStochastic pol X t
      let a := pol.choose hist
      hist ++ [⟨a, X (a, ⟨pullCount hist a,
        (pullCount_le_length hist a).trans_lt
          (ht.trans_eq' (length_runStochastic pol X t).symm)⟩)⟩] := by
  rw [runStochastic_succ]
  dsimp only
  have hs : pullCount (runStochastic pol X t) (pol.choose (runStochastic pol X t)) < T :=
    (pullCount_le_length _ _).trans_lt (ht.trans_eq' (length_runStochastic pol X t).symm)
  split_ifs
  rfl

theorem pullCount_runStochastic_mono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (i : ι) :
    pullCount (runStochastic pol X t₁) i ≤ pullCount (runStochastic pol X t₂) i := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [runStochastic_succ, pullCount_append]
    exact ih.trans (Nat.le_add_right _ _)

/-- Per-arm cumulative reward in `runStochastic pol X t` (`t ≤ T`) equals the sum of the first
`pullCount` entries of arm `i`'s reward stack `X (i, ·)`. -/
theorem feedbackSum_runStochastic_eq {t : ℕ} (ht : t ≤ T) (i : ι) :
    feedbackSum (runStochastic pol X t) i =
      ∑ s : Fin T, if (s : ℕ) < pullCount (runStochastic pol X t) i then X (i, s) else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < T := Nat.lt_of_succ_le ht
    rw [runStochastic_succ_of_lt pol X ht', feedbackSum_append, ih ht'.le, feedbackSum_singleton,
      pullCount_append, pullCount_singleton]
    set hist := runStochastic pol X t
    set a := pol.choose hist
    set u := pullCount hist i
    by_cases ha : a = i
    · subst ha
      have hu : u < T :=
        (pullCount_le_length hist a).trans_lt (ht'.trans_eq' (length_runStochastic pol X t).symm)
      simp only [↓reduceIte]
      have hsplit : ∀ s : Fin T,
          (if (s : ℕ) < u + 1 then X (a, s) else 0) =
            (if (s : ℕ) < u then X (a, s) else 0) +
              if s = ⟨u, hu⟩ then X (a, ⟨u, hu⟩) else 0 := fun s => by
        by_cases h1 : (s : ℕ) < u
        · have hne : s ≠ ⟨u, hu⟩ := fun h => by
            have := congrArg Fin.val h
            dsimp at this
            omega
          simp [h1, Nat.lt_succ_of_lt h1, hne]
        · by_cases h2 : (s : ℕ) = u
          · have heq : s = ⟨u, hu⟩ := Fin.ext h2
            subst heq
            simp
          · have h3 : ¬ (s : ℕ) < u + 1 := by omega
            have hne : s ≠ ⟨u, hu⟩ := fun h => h2 (congrArg Fin.val h)
            simp [h1, h3, hne]
      simp_rw [hsplit]
      rw [sum_add_distrib]
      simp only [sum_ite_eq', mem_univ, ↓reduceIte]
      rfl
    · simp [ha]

/-- If arm `i` is pulled at most `s` times in the first `t` rounds (`t ≤ T`), modifying `X` at
`(i, s)` does not affect the transcript `runStochastic pol X t`. -/
theorem runStochastic_update_eq_of_pullCount_le {t : ℕ} (ht : t ≤ T) (i : ι) (s : Fin T) (z : ℝ)
    (hle : pullCount (runStochastic pol X t) i ≤ s) :
    runStochastic pol (Function.update X (i, s) z) t = runStochastic pol X t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < T := Nat.lt_of_succ_le ht
    have hprev_le : pullCount (runStochastic pol X t) i ≤ s :=
      (pullCount_runStochastic_mono pol X (Nat.le_succ t) i).trans hle
    have hprev := ih ht'.le hprev_le
    rw [runStochastic_succ_of_lt _ _ ht', runStochastic_succ_of_lt _ _ ht']
    simp only [hprev]
    set hist := runStochastic pol X t
    set a := pol.choose hist
    have hne : (a, (⟨pullCount hist a,
        (pullCount_le_length hist a).trans_lt
          (ht'.trans_eq' (length_runStochastic pol X t).symm)⟩ : Fin T)) ≠ (i, s) := by
      intro hpair
      rcases Prod.mk.inj hpair with ⟨rfl, hfin⟩
      have hval : pullCount hist a = (s : ℕ) := congrArg Fin.val hfin
      have hsucc : pullCount (runStochastic pol X (t + 1)) a = pullCount hist a + 1 := by
        rw [runStochastic_succ_of_lt pol X ht', pullCount_append, pullCount_singleton]
        simp [hist, a]
      omega
    rw [Function.update_of_ne hne]

/-- Crucial stopping-event invariance: whether arm `i` is pulled at least `s + 1` times in `t ≤ T`
rounds does not depend on the `(s + 1)`-th reward `X (i, s)` of arm `i`. -/
theorem lt_pullCount_runStochastic_update_iff {t : ℕ} (ht : t ≤ T) (i : ι) (s : Fin T) (z : ℝ) :
    (s : ℕ) < pullCount (runStochastic pol (Function.update X (i, s) z) t) i ↔
      (s : ℕ) < pullCount (runStochastic pol X t) i := by
  constructor
  · contrapose!
    intro hle
    rw [runStochastic_update_eq_of_pullCount_le pol X ht i s z hle]
    exact hle
  · contrapose!
    intro hle
    have hrestore : Function.update (Function.update X (i, s) z) (i, s) (X (i, s)) = X := by
      simp
    have h2 := runStochastic_update_eq_of_pullCount_le pol (Function.update X (i, s) z) ht i s
      (X (i, s)) hle
    rw [hrestore] at h2
    rw [h2]
    exact hle

/-- Measurability of `{X | pullCount (runStochastic pol X t) a = s}` given measurability of the
individual arm fibers up to round `t`. -/
private theorem measurableSet_pullCount_eq_of_arms [Finite ι] {t : ℕ}
    (hA : ∀ r : Fin t, ∀ i : ι,
      MeasurableSet {X : ι × Fin T → ℝ | ((runStochastic pol X t)[r.1]'(by simp)).arm = i})
    (a : ι) (s : ℕ) :
    MeasurableSet {X : ι × Fin T → ℝ | pullCount (runStochastic pol X t) a = s} := by
  let _ := Fintype.ofFinite ι
  have heq : {X : ι × Fin T → ℝ | pullCount (runStochastic pol X t) a = s} =
      ⋃ arms ∈ univ.filter (fun arms : Fin t → ι =>
          (univ.filter fun r : Fin t => arms r = a).card = s),
        ⋂ r : Fin t, {X | ((runStochastic pol X t)[r.1]'(by simp)).arm = arms r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, Set.mem_iInter]
    have hcnt : pullCount (runStochastic pol X t) a =
        (univ.filter fun r : Fin t =>
          ((runStochastic pol X t)[r.1]'(by simp)).arm = a).card := by
      have hl : runStochastic pol X t =
          List.ofFn (fun r : Fin t => (runStochastic pol X t)[r.1]'(by simp)) := by
        apply List.ext_getElem (by simp)
        intro n _ _
        simp
      conv_lhs => rw [hl]
      exact pullCount_ofFn _ a
    constructor
    · intro hs
      exact ⟨fun r => ((runStochastic pol X t)[r.1]'(by simp)).arm,
        by simpa [hcnt] using hs, fun _ => rfl⟩
    · rintro ⟨arms, hcard, harms⟩
      rw [hcnt, ← hcard]
      congr 1
      ext r
      simp [harms r]
  rw [heq]
  exact Set.Finite.measurableSet_biUnion (Finset.finite_toSet _) fun arms _ =>
    MeasurableSet.iInter fun r => hA r (arms r)

/-- Measurability of the arm-tuple and value-tuple of `runStochastic pol · t` when
`pol.IsMeasurable`. -/
theorem measurable_runStochastic_arms_and_vals [Finite ι]
    (hpol : pol.IsMeasurable) (t : ℕ) :
    (∀ r : Fin t, ∀ i : ι,
      MeasurableSet {X : ι × Fin T → ℝ | ((runStochastic pol X t)[r.1]'(by simp)).arm = i}) ∧
    (∀ r : Fin t,
      Measurable fun X : ι × Fin T → ℝ => ((runStochastic pol X t)[r.1]'(by simp)).value) := by
  let _ := Fintype.ofFinite ι
  induction t with
  | zero => exact ⟨fun r => r.elim0, fun r => r.elim0⟩
  | succ t ih =>
    obtain ⟨hA, hV⟩ := ih
    have hchoose : ∀ i : ι,
        MeasurableSet {X : ι × Fin T → ℝ | pol.choose (runStochastic pol X t) = i} := by
      intro i
      let valsFn : (ι × Fin T → ℝ) → (Fin t → ℝ) :=
        fun X r => ((runStochastic pol X t)[r.1]'(by simp)).value
      have hvals_meas : Measurable valsFn := Measurable.of_eval hV
      have heq : {X : ι × Fin T → ℝ | pol.choose (runStochastic pol X t) = i} =
          ⋃ arms : Fin t → ι,
            (⋂ r : Fin t, {X | ((runStochastic pol X t)[r.1]'(by simp)).arm = arms r}) ∩
              valsFn ⁻¹' {vals : Fin t → ℝ |
                pol.choose (List.ofFn fun r => ⟨arms r, vals r⟩) = i} := by
        ext X
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
          Set.mem_preimage]
        constructor
        · intro hX
          refine ⟨fun r => ((runStochastic pol X t)[r.1]'(by simp)).arm, fun _ => rfl, ?_⟩
          have hlist : (List.ofFn fun r : Fin t =>
              (⟨((runStochastic pol X t)[r.1]'(by simp)).arm, valsFn X r⟩ : BanditStep ι)) =
              runStochastic pol X t := by
            apply List.ext_getElem (by simp)
            intro n hn1 hn2
            simp [valsFn]
          simpa [hlist] using hX
        · rintro ⟨arms, harms, hval⟩
          have hlist : (List.ofFn fun r : Fin t =>
              (⟨arms r, valsFn X r⟩ : BanditStep ι)) = runStochastic pol X t := by
            apply List.ext_getElem (by simp)
            intro n hn1 hn2
            simp [valsFn, ← harms ⟨n, by simpa using hn2⟩]
          simpa [hlist] using hval
      rw [heq]
      exact MeasurableSet.iUnion fun arms =>
        (MeasurableSet.iInter fun r => hA r (arms r)).inter (hvals_meas (hpol t arms i))
    have hpull : ∀ (a : ι) (s : ℕ),
        MeasurableSet {X : ι × Fin T → ℝ | pullCount (runStochastic pol X t) a = s} :=
      measurableSet_pullCount_eq_of_arms pol hA
    constructor
    · intro r i
      refine Fin.lastCases ?_ (fun r₀ => ?_) r
      · have hlast : {X : ι × Fin T → ℝ |
            ((runStochastic pol X (t + 1))[(Fin.last t).1]'(by simp)).arm = i} =
            {X | pol.choose (runStochastic pol X t) = i} := by
          ext X
          simp [runStochastic_succ]
        rw [hlast]
        exact hchoose i
      · have hinit : {X : ι × Fin T → ℝ |
            ((runStochastic pol X (t + 1))[r₀.castSucc.1]'(by simp)).arm = i} =
            {X | ((runStochastic pol X t)[r₀.1]'(by simp)).arm = i} := by
          ext X
          simp [runStochastic_succ]
        rw [hinit]
        exact hA r₀ i
    · intro r
      refine Fin.lastCases ?_ (fun r₀ => ?_) r
      · have hlast : (fun X : ι × Fin T → ℝ =>
            ((runStochastic pol X (t + 1))[(Fin.last t).1]'(by simp)).value) =
            fun X => ∑ a : ι, ∑ s : Fin T,
              Set.indicator
                ({X | pol.choose (runStochastic pol X t) = a} ∩
                  {X | pullCount (runStochastic pol X t) a = s.1})
                (fun X => X (a, s)) X := by
          funext X
          have hget : ((runStochastic pol X (t + 1))[(Fin.last t).1]'(by simp)).value =
              if hs : pullCount (runStochastic pol X t)
                  (pol.choose (runStochastic pol X t)) < T then
                X (pol.choose (runStochastic pol X t), ⟨_, hs⟩)
              else 0 := by
            simp [runStochastic_succ]
          rw [hget]
          set a₀ := pol.choose (runStochastic pol X t)
          set s₀ := pullCount (runStochastic pol X t) a₀
          split_ifs with hs₀
          · rw [sum_eq_single a₀, sum_eq_single ⟨s₀, hs₀⟩]
            · simp [Set.indicator_of_mem, a₀, s₀]
            · intro b _ hb
              have hnot : X ∉ {X | pol.choose (runStochastic pol X t) = a₀} ∩
                  {X | pullCount (runStochastic pol X t) a₀ = b.1} := by
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and]
                intro _ hval
                exact hb (Fin.ext hval.symm)
              exact Set.indicator_of_notMem hnot _
            · simp
            · intro b _ hb
              refine sum_eq_zero fun s _ => ?_
              have hnot : X ∉ {X | pol.choose (runStochastic pol X t) = b} ∩
                  {X | pullCount (runStochastic pol X t) b = s.1} := by
                simp [a₀, hb.symm]
              exact Set.indicator_of_notMem hnot _
            · simp
          · symm
            refine sum_eq_zero fun b _ => sum_eq_zero fun s _ => ?_
            by_cases hb : a₀ = b
            · subst hb
              have hnot : X ∉ {X | pol.choose (runStochastic pol X t) = a₀} ∩
                  {X | pullCount (runStochastic pol X t) a₀ = s.1} := by
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and]
                intro _ hval
                exact hs₀ (by simp [s₀, hval])
              exact Set.indicator_of_notMem hnot _
            · have hnot : X ∉ {X | pol.choose (runStochastic pol X t) = b} ∩
                  {X | pullCount (runStochastic pol X t) b = s.1} := by
                simp [a₀, hb]
              exact Set.indicator_of_notMem hnot _
        rw [hlast]
        exact Finset.measurable_sum univ fun a _ => Finset.measurable_sum univ fun s _ =>
          (measurable_pi_apply (a, s)).indicator ((hchoose a).inter (hpull a s.1))
      · have hinit : (fun X : ι × Fin T → ℝ =>
            ((runStochastic pol X (t + 1))[r₀.castSucc.1]'(by simp)).value) =
            fun X => ((runStochastic pol X t)[r₀.1]'(r₀.isLt.trans_eq
              (length_runStochastic pol X t).symm)).value := by
          funext X
          simp [runStochastic_succ]
        rw [hinit]
        exact hV r₀

theorem measurableSet_pullCount_eq [Finite ι] (hpol : pol.IsMeasurable) (t : ℕ) (i : ι)
    (s : ℕ) :
    MeasurableSet {X : ι × Fin T → ℝ | pullCount (runStochastic pol X t) i = s} :=
  measurableSet_pullCount_eq_of_arms pol (measurable_runStochastic_arms_and_vals pol hpol t).1 i s

theorem measurable_pullCount [Finite ι] (hpol : pol.IsMeasurable) (t : ℕ) (i : ι) :
    Measurable fun X : ι × Fin T → ℝ => pullCount (runStochastic pol X t) i := by
  refine measurable_to_countable' fun s => ?_
  change MeasurableSet {X : ι × Fin T → ℝ | pullCount (runStochastic pol X t) i = s}
  exact measurableSet_pullCount_eq pol (T := T) hpol t i s

theorem measurableSet_lt_pullCount [Finite ι] (hpol : pol.IsMeasurable) (t : ℕ) (i : ι)
    (s : ℕ) :
    MeasurableSet {X : ι × Fin T → ℝ | s < pullCount (runStochastic pol X t) i} :=
  (measurable_pullCount pol (T := T) hpol t i) measurableSet_Ioi

end RunProperties

namespace StochasticBandit

variable {ι : Type*} (B : StochasticBandit ι)

/-- Expected reward `μ_i = ∫ x ∂(B.law i)` of arm `i`. -/
noncomputable def mean (i : ι) : ℝ :=
  ∫ x, x ∂(B.law i)

theorem mean_def (i : ι) : B.mean i = ∫ x, x ∂(B.law i) := by
  rw [mean]

/-- Highest expected reward `μ* = max_i μ_i` among all arms. -/
noncomputable def bestMean [Fintype ι] [Nonempty ι] : ℝ :=
  univ.sup' univ_nonempty B.mean

/-- Suboptimality gap `Δ_i = μ* - μ_i` of arm `i`. -/
noncomputable def gap [Fintype ι] [Nonempty ι] (i : ι) : ℝ :=
  B.bestMean - B.mean i

theorem gap_def [Fintype ι] [Nonempty ι] (i : ι) : B.gap i = B.bestMean - B.mean i := by
  rw [gap]

theorem integrable_id (i : ι) : Integrable id (B.law i) :=
  Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable (B.mem_unitInterval i)

theorem mean_mem_Icc (i : ι) : B.mean i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa [mean] using integral_mono_ae (integrable_const (0 : ℝ)) (B.integrable_id i)
      ((B.mem_unitInterval i).mono fun _ hx => hx.1)
  · simpa [mean] using integral_mono_ae (B.integrable_id i) (integrable_const (1 : ℝ))
      ((B.mem_unitInterval i).mono fun _ hx => hx.2)

theorem bestMean_mem_Icc [Fintype ι] [Nonempty ι] : B.bestMean ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty B.mean
  simpa [bestMean, ← hi] using B.mean_mem_Icc i

theorem mean_le_bestMean [Fintype ι] [Nonempty ι] (i : ι) : B.mean i ≤ B.bestMean :=
  le_sup' B.mean (mem_univ i)

theorem gap_nonneg [Fintype ι] [Nonempty ι] (i : ι) : 0 ≤ B.gap i :=
  sub_nonneg.mpr (B.mean_le_bestMean i)

theorem gap_le_one [Fintype ι] [Nonempty ι] (i : ι) : B.gap i ≤ 1 := by
  have h1 := (B.bestMean_mem_Icc).2
  have h2 := (B.mean_mem_Icc i).1
  unfold gap
  linarith

theorem exists_optimal_arm [Fintype ι] [Nonempty ι] :
    ∃ iStar : ι, B.mean iStar = B.bestMean ∧ B.gap iStar = 0 := by
  obtain ⟨iStar, _, hi⟩ := exists_mem_eq_sup' univ_nonempty B.mean
  exact ⟨iStar, hi.symm, by simp [gap, bestMean, hi]⟩

/-- Product measure on successive-play reward stacks `X : ι × Fin T → ℝ`
([AuerCesaBianchiFischer2002, §2]). -/
noncomputable def sampleMeasure [Fintype ι] (T : ℕ) : Measure (ι × Fin T → ℝ) :=
  Measure.pi fun p => B.law p.1

theorem sampleMeasure_def [Fintype ι] (T : ℕ) :
    B.sampleMeasure T = Measure.pi fun p => B.law p.1 := by
  rw [sampleMeasure]

instance [Fintype ι] (T : ℕ) : IsProbabilityMeasure (B.sampleMeasure T) := by
  unfold sampleMeasure
  infer_instance

/-- Expected number of times policy `pol` pulls arm `i` over `T` rounds. -/
noncomputable def expectedPulls [Fintype ι] [DecidableEq ι] (pol : DeterministicPolicy ι)
    (T : ℕ) (i : ι) : ℝ :=
  ∫ X, (pullCount (runStochastic pol X T) i : ℝ) ∂(B.sampleMeasure T)

theorem expectedPulls_def [Fintype ι] [DecidableEq ι] (pol : DeterministicPolicy ι)
    (T : ℕ) (i : ι) :
    B.expectedPulls pol T i =
      ∫ X, (pullCount (runStochastic pol X T) i : ℝ) ∂(B.sampleMeasure T) := by
  rw [expectedPulls]

/-- Expected cumulative reward collected by policy `pol` over `T` rounds. -/
noncomputable def expectedReward [Fintype ι] [DecidableEq ι] (pol : DeterministicPolicy ι)
    (T : ℕ) : ℝ :=
  ∫ X, ((runStochastic pol X T).map BanditStep.value).sum ∂(B.sampleMeasure T)

/-- Expected cumulative regret `T * μ* - 𝔼[∑_{t < T} r_t]` of policy `pol` over `T` rounds
([AuerCesaBianchiFischer2002, §2]). -/
noncomputable def stochasticRegret [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pol : DeterministicPolicy ι) (T : ℕ) : ℝ :=
  T * B.bestMean - B.expectedReward pol T

/-- Gap-weighted expected pull sum `∑ i, Δ_i * 𝔼[N_i(T)]` (pseudo-regret). -/
noncomputable def pseudoRegret [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pol : DeterministicPolicy ι) (T : ℕ) : ℝ :=
  ∑ i : ι, B.gap i * B.expectedPulls pol T i

theorem pseudoRegret_def [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pol : DeterministicPolicy ι) (T : ℕ) :
    B.pseudoRegret pol T = ∑ i : ι, B.gap i * B.expectedPulls pol T i := by
  rw [pseudoRegret]

section Wald

variable [Fintype ι] [DecidableEq ι]

theorem integrable_pullCount {pol : DeterministicPolicy ι} (hpol : pol.IsMeasurable) (T : ℕ)
    (i : ι) :
    Integrable (fun X => (pullCount (runStochastic pol X T) i : ℝ)) (B.sampleMeasure T) := by
  refine Integrable.of_mem_Icc 0 T ?_ (ae_of_all _ fun X => ⟨Nat.cast_nonneg _, ?_⟩)
  · exact ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp
      (measurable_pullCount pol hpol T i)).aemeasurable
  · exact_mod_cast (pullCount_le_length _ i).trans_eq (length_runStochastic pol X T)

theorem expectedPulls_nonneg (pol : DeterministicPolicy ι) (T : ℕ) (i : ι) :
    0 ≤ B.expectedPulls pol T i :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem sum_expectedPulls_eq {pol : DeterministicPolicy ι} (hpol : pol.IsMeasurable) (T : ℕ) :
    ∑ i : ι, B.expectedPulls pol T i = T := by
  unfold expectedPulls
  rw [← integral_finsetSum univ fun i _ => B.integrable_pullCount hpol T i]
  have hsum : ∀ X : ι × Fin T → ℝ,
      (∑ i : ι, (pullCount (runStochastic pol X T) i : ℝ)) = T := fun X => by
    exact_mod_cast (sum_pullCount_eq_length (runStochastic pol X T)).trans
      (length_runStochastic pol X T)
  simp [hsum]

omit [Fintype ι] in
/-- Pull count as a sum of tail indicators `∑_{s < T} 1_{s < N_i(T)}`. -/
private theorem natCast_pullCount_eq_sum_ite (pol : DeterministicPolicy ι) {T : ℕ}
    (X : ι × Fin T → ℝ) (i : ι) :
    (pullCount (runStochastic pol X T) i : ℝ) =
      ∑ s : Fin T, if (s : ℕ) < pullCount (runStochastic pol X T) i then (1 : ℝ) else 0 := by
  have hle : pullCount (runStochastic pol X T) i ≤ T :=
    (pullCount_le_length _ i).trans_eq (length_runStochastic pol X T)
  have hcard : (univ.filter fun s : Fin T => (s : ℕ) < pullCount (runStochastic pol X T) i).card =
      pullCount (runStochastic pol X T) i := by
    have hbij : Finset.map ⟨fun k : Fin (pullCount (runStochastic pol X T) i) =>
        (⟨k.1, k.isLt.trans_le hle⟩ : Fin T), fun a b h => Fin.ext (Fin.mk.inj h)⟩ univ =
        univ.filter fun s : Fin T => (s : ℕ) < pullCount (runStochastic pol X T) i := by
      ext s
      simp only [mem_map, mem_univ, true_and, mem_filter]
      exact ⟨fun ⟨k, hk⟩ => hk ▸ k.isLt, fun hs => ⟨⟨s.1, hs⟩, rfl⟩⟩
    rw [← hbij, card_map, card_fin]
  simp [sum_boole, hcard]

/-- **Wald's identity for stochastic bandits**: for every Borel-measurable deterministic policy
`pol`, the expected cumulative reward over `T` rounds is `∑ i, μ_i * 𝔼[N_i(T)]`. -/
theorem expectedReward_eq_sum_mean {pol : DeterministicPolicy ι}
    (hpol : pol.IsMeasurable) (T : ℕ) :
    B.expectedReward pol T = ∑ i : ι, B.mean i * B.expectedPulls pol T i := by
  unfold expectedReward
  have htot : ∀ X : ι × Fin T → ℝ,
      ((runStochastic pol X T).map BanditStep.value).sum =
        ∑ i : ι, ∑ s : Fin T,
          if (s : ℕ) < pullCount (runStochastic pol X T) i then X (i, s) else 0 := fun X => by
    rw [← sum_feedbackSum_eq]
    exact sum_congr rfl fun i _ => feedbackSum_runStochastic_eq pol X le_rfl i
  simp_rw [htot]
  have hint_term : ∀ (i : ι) (s : Fin T),
      Integrable (fun X : ι × Fin T → ℝ =>
        if (s : ℕ) < pullCount (runStochastic pol X T) i then X (i, s) else 0)
        (B.sampleMeasure T) := by
    intro i s
    have hcoord : Integrable (fun X : ι × Fin T → ℝ => X (i, s)) (B.sampleMeasure T) :=
      (measurePreserving_eval (fun p : ι × Fin T => B.law p.1) (i, s)).integrable_comp_of_integrable
        (B.integrable_id i)
    have hmeas : Measurable (fun X : ι × Fin T → ℝ =>
        if (s : ℕ) < pullCount (runStochastic pol X T) i then X (i, s) else 0) := by
      have heq : (fun X : ι × Fin T → ℝ =>
          if (s : ℕ) < pullCount (runStochastic pol X T) i then X (i, s) else 0) =
          Set.indicator {X | (s : ℕ) < pullCount (runStochastic pol X T) i}
            (fun X => X (i, s)) := by
        funext X
        by_cases h : (s : ℕ) < pullCount (runStochastic pol X T) i <;> simp [h]
      rw [heq]
      exact (measurable_pi_apply (i, s)).indicator (measurableSet_lt_pullCount pol hpol T i s)
    refine hcoord.norm.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun X => ?_)
    split_ifs <;> simp [abs_nonneg]
  rw [integral_finsetSum univ fun i _ =>
    integrable_finsetSum univ fun s _ => hint_term i s]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum univ fun s _ => hint_term i s]
  have hstep : ∀ s : Fin T,
      ∫ X, (if (s : ℕ) < pullCount (runStochastic pol X T) i then X (i, s) else 0)
        ∂(B.sampleMeasure T) =
        B.mean i * ∫ X, (if (s : ℕ) < pullCount (runStochastic pol X T) i then (1 : ℝ) else 0)
          ∂(B.sampleMeasure T) := by
    intro s
    unfold sampleMeasure
    have hfresh := integral_apply_eval_eq_integral_integral
      (μ := fun p : ι × Fin T => B.law p.1) (i := (i, s))
      (Φ := fun (X : ι × Fin T → ℝ) (z : ℝ) =>
        if (s : ℕ) < pullCount (runStochastic pol X T) i then z else 0)
      (fun X z => by
        funext w
        simp [lt_pullCount_runStochastic_update_iff pol X le_rfl i s z])
      (hint_term i s)
    rw [hfresh]
    have hinner : ∀ X : ι × Fin T → ℝ,
        (∫ z, (if (s : ℕ) < pullCount (runStochastic pol X T) i then z else 0) ∂B.law i) =
          B.mean i * (if (s : ℕ) < pullCount (runStochastic pol X T) i then (1 : ℝ) else 0) := by
      intro X
      by_cases h : (s : ℕ) < pullCount (runStochastic pol X T) i <;> simp [h, mean]
    simp_rw [hinner]
    exact integral_const_mul _ _
  simp_rw [hstep, ← mul_sum]
  congr 1
  unfold expectedPulls sampleMeasure
  have hind_int : ∀ s : Fin T,
      Integrable (fun X : ι × Fin T → ℝ =>
        if (s : ℕ) < pullCount (runStochastic pol X T) i then (1 : ℝ) else 0)
        (Measure.pi fun p : ι × Fin T => B.law p.1) := by
    intro s
    refine Integrable.of_mem_Icc 0 1 ?_ (ae_of_all _ fun X => by split_ifs <;> norm_num)
    have heq : (fun X : ι × Fin T → ℝ =>
        if (s : ℕ) < pullCount (runStochastic pol X T) i then (1 : ℝ) else 0) =
        Set.indicator {X | (s : ℕ) < pullCount (runStochastic pol X T) i} (fun _ => (1 : ℝ)) := by
      funext X
      by_cases h : (s : ℕ) < pullCount (runStochastic pol X T) i <;> simp [h]
    rw [heq]
    exact (measurable_const.indicator (measurableSet_lt_pullCount pol hpol T i s)).aemeasurable
  rw [← integral_finsetSum univ fun s _ => hind_int s]
  exact integral_congr_ae (ae_of_all _ fun X => (natCast_pullCount_eq_sum_ite pol X i).symm)

/-- **Stochastic regret decomposition** ([AuerCesaBianchiFischer2002, §2]): for every
Borel-measurable deterministic policy `pol`, expected cumulative regret equals the gap-weighted sum
of expected pull counts `∑ i, Δ_i * 𝔼[N_i(T)]`. -/
theorem stochasticRegret_eq_pseudoRegret [Nonempty ι] {pol : DeterministicPolicy ι}
    (hpol : pol.IsMeasurable) (T : ℕ) :
    B.stochasticRegret pol T = B.pseudoRegret pol T := by
  unfold stochasticRegret pseudoRegret gap
  rw [B.expectedReward_eq_sum_mean hpol T, ← B.sum_expectedPulls_eq hpol T,
    mul_comm _ B.bestMean, mul_sum]
  simp only [sub_mul, sum_sub_distrib]

end Wald

end StochasticBandit

end Stochastic

end Cslib.MachineLearning.OnlineLearning.Bandits
