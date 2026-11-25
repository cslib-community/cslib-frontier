/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.Linarith

/-!
# Dynamic VCG (dynamic pivot) mechanism for finite-horizon MDPs

In a dynamic mechanism design environment ([Parkes2007], §16.6, Theorem 16.28; [ParkesSingh2003];
[BergemannValimaki2010], locators not verified against primary PDF), a finite set of agents `ι`
interacts over a Markov decision process with finite state space `S`, finite nonempty action space
`K`, transition kernel `trans : S → K → PMF S`, discount factor `γ ≥ 0` (`γ = 1` gives the
undiscounted finite-horizon model of [Parkes2007], §16.6; `γ ∈ (0, 1)` gives discounted horizons
as in Exercise 16.8), and per-period agent valuations `val : ι → ℕ → S → K → ℝ`.

An efficient MDP policy `π*` maximizes expected discounted total social welfare
`W*(t, h, s)` over the remaining horizon `h` starting from time `t` and state `s`. For each agent
`i`, let `W*_{-i}(t, h, s)` be the optimal expected discounted social welfare of the remaining
agents `j ≠ i`. In the single-agent deviation model formalized here, the environment holds other
agents' true valuations `othersVal i` fixed (`env.val` encodes the true reported types of `j ≠ i`),
so `isTruthful` and `delayedUtility_le_truthful` establish *within-period / Markov-perfect
equilibrium truthfulness against truthful other agents* ([Parkes2007], Theorem 16.28;
[BergemannValimaki2010]), rather than dominant-strategy incentive compatibility (`DSIC`) under
arbitrary misreports by `j ≠ i`. The *dynamic VCG* (or *dynamic pivot*, *marginal-externality*)
per-period payment when taking action `k` at `(t, h + 1, s)` is
`pᵢ(t, h + 1, s, k) = W*_{-i}(t, h + 1, s) - (∑_{j ≠ i} rⱼ + γ · E[W*_{-i}(t + 1, h, s')])`.

## Main definitions

* `DynamicEnv`: finite-horizon Markovian dynamic mechanism design environment with discount factor
  `discount ≥ 0`, transition kernel `trans`, and per-period agent valuations `val`.
* `DynamicEnv.evalFrom`: expected discounted cumulative reward of any history-dependent policy
  `σ : List S → K`.
* `DynamicEnv.bellmanValue`, `DynamicEnv.bellmanAction`: Bellman optimal expected discounted value
  and maximizing Markov action for a reward stream `r`.
* `DynamicEnv.optimalValue`, `DynamicEnv.optimalValueWithout`: Bellman optimal expected welfare
  with all agents (`W*`) and without agent `i` (`W*_{-i}`).
* `DynamicEnv.optimalPolicy`, `DynamicEnv.optimalPolicyWithout`: efficient policies attaining
  `W*` and `W*_{-i}`.
* `DynamicEnv.pivotPayment`: per-period marginal-externality dynamic VCG payment.
* `DynamicEnv.agentUtility`: expected discounted cumulative utility of agent `i` under any
  history-dependent induced policy `σ`.
* `DynamicEnv.delayedUtility`: expected utility of an agent delaying arrival by `d` periods while
  the mechanism follows the without-`i` optimal policy.

## Main results

* `DynamicEnv.evalFrom_le_optimalValue`, `DynamicEnv.evalFrom_optimalPolicy`: Bellman optimality of
  `optimalPolicy` across *all* history-dependent policies.
* `DynamicEnv.evalFrom_le_optimalValueWithout`, `DynamicEnv.evalFrom_optimalPolicyWithout`,
  `DynamicEnv.pivotPayment_optimalPolicyWithout`: Bellman optimality of `optimalPolicyWithout` for
  `othersVal i` (`W*_{-i}`) and zero marginal-externality payments along it.
* `DynamicEnv.agentUtility_eq_totalVal_sub`: exact telescoping identity showing that for *every*
  history-dependent policy `σ`, agent `i`'s expected cumulative utility equals the expected total
  social welfare under `σ` minus the agent-independent baseline `W*_{-i}(t, h, s)`.
* `DynamicEnv.isTruthful`: within-period / Markov-perfect equilibrium truthfulness of dynamic VCG
  against truthful other agents — truthful reporting (inducing `optimalPolicy`) maximizes agent
  `i`'s expected discounted utility against every history-dependent deviation policy `σ` when
  other agents report truthfully (`othersVal i` fixed; [Parkes2007], Theorem 16.28;
  [ParkesSingh2003]; [BergemannValimaki2010], locators not verified against primary PDF).
* `DynamicEnv.pivotPayment_nonneg`: per-period no positive transfers (`0 ≤ pivotPayment`).
* `DynamicEnv.isIR`: within-period individual rationality at every period `t` and state `s` when
  agent `i`'s per-period valuations are nonnegative.
* `DynamicEnv.pivotPayment_optimalActionWithout`, `DynamicEnv.delayedUtility_le_truthful`:
  delaying arrival (while unserved and paying zero under the without-`i` optimal policy) cannot
  strictly improve expected utility against truthful other agents when `i`'s valuations are
  nonnegative.

## References

* [D. C. Parkes, *Online Mechanisms*][Parkes2007]
* [D. C. Parkes and S. Singh, *An MDP-Based Approach to Online Mechanism Design*][ParkesSingh2003]
* [D. Bergemann and J. Välimäki, *The Dynamic Pivot Mechanism*][BergemannValimaki2010]
-/

open scoped BigOperators

public section

namespace Cslib.GameTheory.OnlineMechanism.DynamicVCG

/-- A finite-horizon Markovian dynamic mechanism design environment with agents `ι`, states `S`,
actions `K`, discount factor `discount ≥ 0`, transition kernel `trans`, and per-period agent
valuations `val` ([Parkes2007], §16.6; [BergemannValimaki2010], locators not verified against
primary PDF). -/
structure DynamicEnv (ι S K : Type*) where
  /-- Per-period discount factor `γ ≥ 0` (`γ = 1` for undiscounted finite horizons). -/
  discount : ℝ
  /-- Nonnegativity of the discount factor. -/
  discount_nonneg : 0 ≤ discount
  /-- Markov state transition distribution given current state and chosen action. -/
  trans : S → K → PMF S
  /-- Per-period valuation `val i t s k` of agent `i` at period `t`, state `s`, and action `k`. -/
  val : ι → ℕ → S → K → ℝ

namespace DynamicEnv

section Valuations

variable {ι S K : Type*}

/-- Total per-period social valuation `∑ j, env.val j t s k`. -/
@[expose] def totalVal [Fintype ι] (env : DynamicEnv ι S K) (t : ℕ) (s : S) (k : K) : ℝ :=
  ∑ j : ι, env.val j t s k

/-- Per-period valuation of all agents other than `i`: `∑ j ∈ univ.erase i, env.val j t s k`. -/
@[expose] def othersVal [Fintype ι] [DecidableEq ι] (env : DynamicEnv ι S K) (i : ι)
    (t : ℕ) (s : S) (k : K) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, env.val j t s k

theorem val_add_othersVal [Fintype ι] [DecidableEq ι] (env : DynamicEnv ι S K) (i : ι)
    (t : ℕ) (s : S) (k : K) :
    env.val i t s k + env.othersVal i t s k = env.totalVal t s k :=
  Finset.add_sum_erase Finset.univ (fun j => env.val j t s k) (Finset.mem_univ i)

end Valuations

section Bellman

variable {ι S K : Type*} [Fintype S] [Fintype K] [Nonempty K]

/-- Expected discounted cumulative value of a per-period reward stream `r` under an arbitrary
history-dependent policy `σ : List S → K` over remaining horizon `h`, starting at period `t`,
state history `hist`, and current state `s`. -/
@[expose] noncomputable def evalFrom (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (σ : List S → K) : ℕ → ℕ → List S → S → ℝ
  | _, 0, _, _ => 0
  | t, h + 1, hist, s =>
    let k := σ (s :: hist)
    r t s k + env.discount *
      ∑ s' : S, (env.trans s k s').toReal * evalFrom env r σ (t + 1) h (s :: hist) s'

/-- Bellman optimal expected discounted value for an arbitrary per-period reward function `r`,
over remaining horizon `h` starting from period `t` and state `s`. -/
@[expose] noncomputable def bellmanValue (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ) :
    ℕ → ℕ → S → ℝ
  | _, 0, _ => 0
  | t, h + 1, s =>
    Finset.univ.sup' Finset.univ_nonempty fun k : K =>
      r t s k + env.discount *
        ∑ s' : S, (env.trans s k s').toReal * bellmanValue env r (t + 1) h s'

/-- One-step Bellman Q-value for reward `r` and action `k` at `(t, h + 1, s)`. -/
private noncomputable def qValue (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (t h : ℕ) (s : S) (k : K) : ℝ :=
  r t s k + env.discount *
    ∑ s' : S, (env.trans s k s').toReal * env.bellmanValue r (t + 1) h s'

private theorem qValue_le_bellmanValue (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (t h : ℕ) (s : S) (k : K) :
    env.qValue r t h s k ≤ env.bellmanValue r t (h + 1) s :=
  Finset.le_sup' (f := env.qValue r t h s) (Finset.mem_univ k)

private theorem exists_bellman_argmax (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (t h : ℕ) (s : S) :
    ∃ k : K, env.qValue r t h s k = env.bellmanValue r t (h + 1) s := by
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (env.qValue r t h s)
  exact ⟨k, hk.symm⟩

/-- An optimal Markov action achieving the Bellman maximum for reward `r` at `(t, h + 1, s)`. -/
noncomputable def bellmanAction (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (t h : ℕ) (s : S) : K :=
  Classical.choose (env.exists_bellman_argmax r t h s)

private theorem qValue_bellmanAction (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (t h : ℕ) (s : S) :
    env.qValue r t h s (env.bellmanAction r t h s) = env.bellmanValue r t (h + 1) s :=
  Classical.choose_spec (env.exists_bellman_argmax r t h s)

/-- Convert a Markov decision rule `act : ℕ → ℕ → S → K` (taking current time, remaining steps
after this decision, and current state) into a history-dependent strategy starting from `(t₀, h₀)`
with initial history length `len₀`. -/
@[expose] noncomputable def toHistoryPolicy (act : ℕ → ℕ → S → K) (t₀ h₀ len₀ : ℕ) :
    List S → K
  | [] => Classical.arbitrary K
  | s :: hist =>
    let elapsed := hist.length - len₀
    act (t₀ + elapsed) (h₀ - elapsed - 1) s

/-- Bellman optimality: no history-dependent policy can exceed `bellmanValue`. -/
theorem evalFrom_le_bellmanValue (env : DynamicEnv ι S K) (r : ℕ → S → K → ℝ)
    (σ : List S → K) (t h : ℕ) (hist : List S) (s : S) :
    env.evalFrom r σ t h hist s ≤ env.bellmanValue r t h s := by
  induction h generalizing t hist s with
  | zero => exact le_rfl
  | succ h ih =>
    have := env.discount_nonneg
    refine le_trans ?_ (env.qValue_le_bellmanValue r t h s (σ (s :: hist)))
    simp only [evalFrom, qValue]
    gcongr with s'
    exact ih _ _ _

/-- Evaluating `toHistoryPolicy (bellmanAction r)` attains `bellmanValue r` exactly. -/
private theorem evalFrom_toHistoryPolicy_bellmanAction (env : DynamicEnv ι S K)
    (r : ℕ → S → K → ℝ) (t₀ h₀ len₀ : ℕ) :
    ∀ (e : ℕ) (hist : List S) (s : S),
      hist.length = len₀ + e → e ≤ h₀ →
      env.evalFrom r (toHistoryPolicy (env.bellmanAction r) t₀ h₀ len₀)
        (t₀ + e) (h₀ - e) hist s = env.bellmanValue r (t₀ + e) (h₀ - e) s := by
  intro e hist s hlen hele
  generalize hrem : h₀ - e = rem
  induction rem generalizing e hist s with
  | zero => rfl
  | succ rem ih =>
    simp only [evalFrom, toHistoryPolicy]
    rw [show hist.length - len₀ = e by omega, show h₀ - e - 1 = rem by omega,
      ← env.qValue_bellmanAction r (t₀ + e) rem s, qValue]
    congr 2
    refine Finset.sum_congr rfl fun s' _ => ?_
    have hstep := ih (e + 1) (s :: hist) s' (by simp [hlen]; omega) (by omega) (by omega)
    rw [show t₀ + (e + 1) = t₀ + e + 1 by omega] at hstep
    rw [hstep]

end Bellman

section SocialWelfare

variable {ι S K : Type*} [Fintype ι] [Fintype S] [Fintype K] [Nonempty K]

/-- Optimal total expected discounted social welfare `W*(t, h, s)`. -/
@[expose] noncomputable def optimalValue (env : DynamicEnv ι S K) (t h : ℕ) (s : S) : ℝ :=
  env.bellmanValue env.totalVal t h s

/-- The efficient MDP policy `π*` for total horizon `h₀` starting at time `t₀` and history length
`len₀`. -/
@[expose] noncomputable def optimalPolicy (env : DynamicEnv ι S K) (t₀ h₀ len₀ : ℕ) :
    List S → K :=
  toHistoryPolicy (env.bellmanAction env.totalVal) t₀ h₀ len₀

/-- Bellman optimality for total social welfare: no history-dependent policy achieves higher
expected discounted welfare than `optimalValue`. -/
theorem evalFrom_le_optimalValue (env : DynamicEnv ι S K) (σ : List S → K)
    (t h : ℕ) (hist : List S) (s : S) :
    env.evalFrom env.totalVal σ t h hist s ≤ env.optimalValue t h s :=
  env.evalFrom_le_bellmanValue env.totalVal σ t h hist s

/-- The efficient MDP policy `optimalPolicy` attains `optimalValue` exactly. -/
theorem evalFrom_optimalPolicy (env : DynamicEnv ι S K) (t₀ h₀ : ℕ) (hist : List S) (s : S) :
    env.evalFrom env.totalVal (env.optimalPolicy t₀ h₀ hist.length) t₀ h₀ hist s =
      env.optimalValue t₀ h₀ s := by
  have h := env.evalFrom_toHistoryPolicy_bellmanAction env.totalVal t₀ h₀ hist.length 0 hist s
    (by simp) (Nat.zero_le h₀)
  simpa only [Nat.add_zero, Nat.sub_zero, optimalPolicy, optimalValue] using h

end SocialWelfare

section PivotMechanism

variable {ι S K : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Fintype K] [Nonempty K]

/-- Optimal expected discounted social welfare `W*_{-i}(t, h, s)` of all agents other than `i`. -/
@[expose] noncomputable def optimalValueWithout (env : DynamicEnv ι S K) (i : ι) (t h : ℕ)
    (s : S) : ℝ :=
  env.bellmanValue (env.othersVal i) t h s

/-- The without-`i` efficient MDP policy `π*_{-i}`. -/
@[expose] noncomputable def optimalPolicyWithout (env : DynamicEnv ι S K) (i : ι)
    (t₀ h₀ len₀ : ℕ) : List S → K :=
  toHistoryPolicy (env.bellmanAction (env.othersVal i)) t₀ h₀ len₀

/-- Bellman optimality without agent `i`: no history-dependent policy achieves higher expected
discounted without-`i` welfare than `optimalValueWithout`. -/
theorem evalFrom_le_optimalValueWithout (env : DynamicEnv ι S K) (i : ι) (σ : List S → K)
    (t h : ℕ) (hist : List S) (s : S) :
    env.evalFrom (env.othersVal i) σ t h hist s ≤ env.optimalValueWithout i t h s :=
  env.evalFrom_le_bellmanValue (env.othersVal i) σ t h hist s

/-- The without-`i` efficient MDP policy `optimalPolicyWithout` attains `optimalValueWithout`
exactly. -/
theorem evalFrom_optimalPolicyWithout (env : DynamicEnv ι S K) (i : ι) (t₀ h₀ : ℕ)
    (hist : List S) (s : S) :
    env.evalFrom (env.othersVal i) (env.optimalPolicyWithout i t₀ h₀ hist.length)
        t₀ h₀ hist s =
      env.optimalValueWithout i t₀ h₀ s := by
  have h := env.evalFrom_toHistoryPolicy_bellmanAction (env.othersVal i) t₀ h₀ hist.length 0
    hist s (by simp) (Nat.zero_le h₀)
  simpa only [Nat.add_zero, Nat.sub_zero, optimalPolicyWithout, optimalValueWithout] using h

/-- Per-period dynamic VCG (marginal-externality / dynamic pivot) payment charged to agent `i`
when action `k` is taken at period `t`, remaining horizon `h + 1`, and state `s`
([Parkes2007], §16.6; [ParkesSingh2003]; [BergemannValimaki2010], locators not verified against
primary PDF). -/
@[expose] noncomputable def pivotPayment (env : DynamicEnv ι S K) (i : ι)
    (t h : ℕ) (s : S) (k : K) : ℝ :=
  env.optimalValueWithout i t (h + 1) s -
    (env.othersVal i t s k +
      env.discount *
        ∑ s' : S, (env.trans s k s').toReal * env.optimalValueWithout i (t + 1) h s')

/-- Per-period No Positive Transfers: the dynamic pivot payment is always nonnegative. -/
theorem pivotPayment_nonneg (env : DynamicEnv ι S K) (i : ι) (t h : ℕ) (s : S) (k : K) :
    0 ≤ env.pivotPayment i t h s k := by
  unfold pivotPayment optimalValueWithout
  have := env.qValue_le_bellmanValue (env.othersVal i) t h s k
  unfold qValue at this
  linarith

/-- When the without-`i` optimal action is played, agent `i`'s marginal externality payment is `0`.
-/
theorem pivotPayment_optimalActionWithout (env : DynamicEnv ι S K) (i : ι)
    (t h : ℕ) (s : S) :
    env.pivotPayment i t h s (env.bellmanAction (env.othersVal i) t h s) = 0 := by
  unfold pivotPayment optimalValueWithout
  have := env.qValue_bellmanAction (env.othersVal i) t h s
  unfold qValue at this
  linarith

/-- After `e` steps from `(t₀, h₀, len₀)`, `optimalPolicyWithout` incurs zero pivot payment. -/
theorem pivotPayment_optimalPolicyWithout (env : DynamicEnv ι S K) (i : ι)
    {t₀ h₀ len₀ e : ℕ} (hist : List S) (hlen : hist.length = len₀ + e) (s : S) :
    env.pivotPayment i (t₀ + e) (h₀ - e - 1) s
      (env.optimalPolicyWithout i t₀ h₀ len₀ (s :: hist)) = 0 := by
  have hel : hist.length - len₀ = e := by omega
  unfold optimalPolicyWithout toHistoryPolicy
  dsimp only
  rw [hel]
  exact env.pivotPayment_optimalActionWithout i (t₀ + e) (h₀ - e - 1) s

/-- Expected discounted cumulative utility of agent `i` under dynamic VCG payments when the
mechanism executes history-dependent policy `σ` over remaining horizon `h` starting at `(t, s)`. -/
@[expose] noncomputable def agentUtility (env : DynamicEnv ι S K) (i : ι) (σ : List S → K) :
    ℕ → ℕ → List S → S → ℝ
  | _, 0, _, _ => 0
  | t, h + 1, hist, s =>
    let k := σ (s :: hist)
    (env.val i t s k - env.pivotPayment i t h s k) +
      env.discount *
        ∑ s' : S, (env.trans s k s').toReal * agentUtility env i σ (t + 1) h (s :: hist) s'

/-- Exact telescoping identity of Dynamic VCG: for *every* history-dependent policy `σ`, agent `i`'s
expected cumulative utility equals the expected total social welfare under `σ` minus the
agent-independent baseline `W*_{-i}(t, h, s)`. -/
theorem agentUtility_eq_totalVal_sub (env : DynamicEnv ι S K) (i : ι) (σ : List S → K)
    (t h : ℕ) (hist : List S) (s : S) :
    env.agentUtility i σ t h hist s =
      env.evalFrom env.totalVal σ t h hist s - env.optimalValueWithout i t h s := by
  induction h generalizing t hist s with
  | zero =>
    simp only [agentUtility, evalFrom, optimalValueWithout, bellmanValue, sub_self]
  | succ h ih =>
    simp only [agentUtility, evalFrom, pivotPayment, ih, mul_sub, Finset.sum_sub_distrib]
    linarith [env.val_add_othersVal i t s (σ (s :: hist))]

/-- Within-period / Markov-perfect equilibrium truthfulness of Dynamic VCG against truthful other
agents: holding the remaining agents' true valuations `othersVal i` fixed in `env.val`, truthful
reporting (inducing `optimalPolicy`) maximizes agent `i`'s expected discounted cumulative utility
over *all* history-dependent deviation policies `σ` (not DSIC under arbitrary misreports by `j ≠ i`;
[Parkes2007], Theorem 16.28; [ParkesSingh2003]; [BergemannValimaki2010], locators not verified
against primary PDF). -/
theorem isTruthful (env : DynamicEnv ι S K) (i : ι) (σ : List S → K)
    (t₀ h₀ : ℕ) (hist : List S) (s : S) :
    env.agentUtility i σ t₀ h₀ hist s ≤
      env.agentUtility i (env.optimalPolicy t₀ h₀ hist.length) t₀ h₀ hist s := by
  rw [env.agentUtility_eq_totalVal_sub i σ t₀ h₀ hist s,
    env.agentUtility_eq_totalVal_sub i (env.optimalPolicy t₀ h₀ hist.length) t₀ h₀ hist s,
    env.evalFrom_optimalPolicy t₀ h₀ hist s]
  linarith [env.evalFrom_le_optimalValue σ t₀ h₀ hist s]

/-- When agent `i`'s per-period valuations are nonnegative, total optimal welfare is at least
without-`i` optimal welfare (`W*_{-i} ≤ W*`). -/
theorem optimalValueWithout_le_optimalValue (env : DynamicEnv ι S K) (i : ι)
    (hnonneg : ∀ t s k, 0 ≤ env.val i t s k) (t h : ℕ) (s : S) :
    env.optimalValueWithout i t h s ≤ env.optimalValue t h s := by
  induction h generalizing t s with
  | zero => exact le_rfl
  | succ h ih =>
    have := env.discount_nonneg
    unfold optimalValueWithout optimalValue bellmanValue
    refine Finset.sup'_le _ _ fun k _ => le_trans ?_ (env.qValue_le_bellmanValue _ t h s k)
    have := env.val_add_othersVal i t s k
    simp only [qValue]
    gcongr with s'
    · linarith [hnonneg t s k]
    · exact ih _ _

/-- Within-period Individual Rationality of Dynamic VCG: whenever agent `i`'s per-period valuations
are nonnegative, truthful Dynamic VCG guarantees nonnegative expected continuation utility at every
period `t₀` and every state `s`
([BergemannValimaki2010]; [Parkes2007], §16.6, locators not verified against primary PDF). -/
theorem isIR (env : DynamicEnv ι S K) (i : ι) (hnonneg : ∀ t s k, 0 ≤ env.val i t s k)
    (t₀ h₀ : ℕ) (hist : List S) (s : S) :
    0 ≤ env.agentUtility i (env.optimalPolicy t₀ h₀ hist.length) t₀ h₀ hist s := by
  rw [env.agentUtility_eq_totalVal_sub, env.evalFrom_optimalPolicy]
  linarith [env.optimalValueWithout_le_optimalValue i hnonneg t₀ h₀ s]

/-- Expected discounted utility of agent `i` who arrives at `(t, h, s)` and delays reporting for `d`
periods (`d ≤ h`): during the `d` delay periods, the mechanism takes the without-`i` optimal action
and agent `i` gets `0` value and pays `0`; thereafter the mechanism follows `σ`. -/
@[expose] noncomputable def delayedUtility (env : DynamicEnv ι S K) (i : ι) (σ : List S → K) :
    ℕ → ℕ → ℕ → List S → S → ℝ
  | 0, t, h, hist, s => env.agentUtility i σ t h hist s
  | _ + 1, _, 0, _, _ => 0
  | d + 1, t, h + 1, hist, s =>
    let k := env.bellmanAction (env.othersVal i) t h s
    env.discount *
      ∑ s' : S, (env.trans s k s').toReal * delayedUtility env i σ d (t + 1) h (s :: hist) s'

/-- Arrival-delay within-period / Markov-perfect truthfulness of Dynamic VCG against truthful
other agents (`othersVal i` fixed in `env.val`): if agent `i` has nonnegative valuations, delaying
arrival by `d` periods (receiving zero value and paying zero while unreported under the without-`i`
optimal policy) and then inducing any history-dependent policy `σ` yields expected utility at most
truthful Dynamic VCG utility from arrival
([Parkes2007], §16.6, Theorem 16.28; [ParkesSingh2003], locators not verified against primary PDF).
-/
theorem delayedUtility_le_truthful (env : DynamicEnv ι S K) (i : ι)
    (hnonneg : ∀ t s k, 0 ≤ env.val i t s k) (σ : List S → K)
    (d t₀ h₀ : ℕ) (hist : List S) (s : S) :
    env.delayedUtility i σ d t₀ h₀ hist s ≤
      env.agentUtility i (env.optimalPolicy t₀ h₀ hist.length) t₀ h₀ hist s := by
  set len₀ := hist.length
  let stitched : List S → K := fun hs =>
    match hs with
    | [] => Classical.arbitrary K
    | s' :: rest =>
      let elapsed := rest.length - len₀
      if elapsed < d then
        env.bellmanAction (env.othersVal i) (t₀ + elapsed) (h₀ - elapsed - 1) s'
      else
        σ (s' :: rest)
  have hle_stitched :
      ∀ (d' : ℕ) (e : ℕ) (hs : List S) (s' : S),
        hs.length = len₀ + e → e + d' = d → e ≤ h₀ →
        env.delayedUtility i σ d' (t₀ + e) (h₀ - e) hs s' ≤
          env.agentUtility i stitched (t₀ + e) (h₀ - e) hs s' := by
    intro d'
    induction d' with
    | zero =>
      intro e hs s' hlen hed hele
      have hagree :
          ∀ (rem : ℕ) (t : ℕ) (hs' : List S) (s'' : S),
            len₀ + d ≤ hs'.length →
            env.agentUtility i σ t rem hs' s'' = env.agentUtility i stitched t rem hs' s'' := by
        intro rem
        induction rem with
        | zero => intro _ _ _ _; rfl
        | succ rem ihr =>
          intro t hs' s'' hlen'
          have hst : stitched (s'' :: hs') = σ (s'' :: hs') := ite_eq_right (by omega)
          have hlen'' : len₀ + d ≤ (s'' :: hs').length := by simp; omega
          simp only [agentUtility, hst, ihr (t + 1) (s'' :: hs') _ hlen'']
      simp only [delayedUtility]
      exact le_of_eq (hagree (h₀ - e) (t₀ + e) hs s' (by omega))
    | succ d' ih =>
      intro e hs s' hlen hed hele
      by_cases hrem0 : h₀ - e = 0
      · rw [hrem0]
        simp only [delayedUtility, agentUtility, le_rfl]
      · obtain ⟨rem, hrem⟩ := Nat.exists_eq_succ_of_ne_zero hrem0
        have hst : stitched (s' :: hs) = env.bellmanAction (env.othersVal i) (t₀ + e) rem s' := by
          simp only [stitched, show hs.length - len₀ = e by omega, show e < d by omega,
            ↓reduceIte, show h₀ - e - 1 = rem by omega]
        rw [hrem]
        simp only [delayedUtility, agentUtility, hst, env.pivotPayment_optimalActionWithout,
          sub_zero]
        have := env.discount_nonneg
        refine le_add_of_nonneg_of_le (hnonneg _ _ _) ?_
        gcongr with s''
        have hstep := ih (e + 1) (s' :: hs) s'' (by simp [hlen]; omega) (by omega) (by omega)
        rwa [show t₀ + (e + 1) = t₀ + e + 1 by omega, show h₀ - (e + 1) = rem by omega] at hstep
  have h1 := hle_stitched d 0 hist s (by simp [len₀]) (by omega) (Nat.zero_le h₀)
  simp only [Nat.add_zero, Nat.sub_zero] at h1
  exact h1.trans (env.isTruthful i stitched t₀ h₀ hist s)

end PivotMechanism

end DynamicEnv

end Cslib.GameTheory.OnlineMechanism.DynamicVCG
