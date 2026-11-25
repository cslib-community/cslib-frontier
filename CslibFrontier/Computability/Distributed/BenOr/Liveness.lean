/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.BenOr.Basic
public import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Tactic.ENNRealToReal
import CslibFrontier.Tactic.SuppCases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Pre-coin phase-scheduler termination step for Ben-Or's binary consensus

This module proves a **pre-coin phase-scheduler probabilistic termination step** for the
quorum-phase transition of `CslibFrontier.Computability.Distributed.BenOr.Basic` (after
[BenOr1983], §3, Protocol A, printed p. 28, toward Theorem 1(i) on printed p. 29; termination in
Ben-Or's full asynchronous scheduler model remains open in #7120).

**Scheduling restriction (#7120):** In [BenOr1983], §2 (printed pp. 27–28), an adversary schedule
chooses each primitive process step and message delivery using the current configuration and full
execution history, including outcomes of earlier local coin flips by processes that have already
completed step 3(c) of a round while slower processes are still collecting that round's `n - t`
messages. Here `probRun` instead models a **pre-coin per-phase state-adaptive scheduler**
`strat : ℕ → (P → ProcState) → PhaseSchedule P` that commits the entire phase-`r` quorum schedule
`strat r st` from the phase-`r` boundary state `st` *before* sampling the entire phase-`r` coin
vector from `coinLaw`, and bounds the non-decision marginal of that phased Markov process. Neither
`probRun` nor `CrashSchedule` in `Basic.lean` extends the probabilistic termination bound to §2
schedulers with arbitrary cross-round step/message interleavings (#7120).

Whenever `coinLaw : PMF (P → Bool)` places mass at least `p` on both unanimous coin vectors
`fun _ => true` and `fun _ => false`:

1. `phaseStep_lucky_coin` guarantees at least one of those two constant vectors aligns every
   process onto a common estimate at the end of phase `r`, bounding single-phase non-unanimity
   probability by `1 - p` (and by `0` once estimates are already unanimous).
2. By induction over `k` phases (`probRun_not_unanimous_le`), the probability that estimates are
   not yet unanimous after `k` phases is at most `(1 - p) ^ k`.
3. One additional valid phase deterministically turns unanimous estimates into unanimous decisions
   (`probRun_not_allDecided_le`), bounding the probability of `¬ AllDecided` after `k + 1` phases
   by `(1 - p) ^ k`, which converges to `0` as the phase count grows whenever `0 < p`
   (`tendsto_probRun_not_allDecided`).

Instantiating `coinLaw` gives two distinct coin regimes under this pre-coin phase-scheduler model:

* **Independent local fair coins (`localCoinLaw P`, step after [BenOr1983], §3, Protocol A):**
  restricted to pre-coin phase-boundary schedulers (#7120), sampling `coinLaw =
  uniformOfFintype (P → Bool)` (Protocol A step 3(c), printed p. 28) gives `p = (1 / 2) ^ |P|`,
  bounding non-decision probability after `k + 1` phases by `(1 - (1 / 2) ^ |P|) ^ k`
  (`probRun_localCoin_not_allDecided_le`) and tending to `0` as `m → ∞`
  (`tendsto_probRun_localCoin_not_allDecided`).
* **Common fair coin (`commonCoinLaw P`, separate shared-coin variant):** a separate variant not in
  [BenOr1983] (where coins are local to each process), supplying one shared uniform bit `b` to all
  processes per phase (`p = 1 / 2`) so non-decision probability after `k + 1` phases is at most
  `(1 / 2) ^ k` (`probRun_commonCoin_not_allDecided_le`,
  `tendsto_probRun_commonCoin_not_allDecided`).

## Main definitions

* `Cslib.Distributed.BenOr.probRun`: state distribution after `k` phases under a pre-coin per-phase
  state-adaptive scheduler `strat` and per-phase coin distribution `coinLaw`.
* `Cslib.Distributed.BenOr.commonCoinLaw`: separate shared-coin variant `PMF (P → Bool)` assigning
  `1 / 2` to each constant vector `fun _ => b`.
* `Cslib.Distributed.BenOr.localCoinLaw`: independent local fair coins
  `uniformOfFintype (P → Bool)` (after [BenOr1983], §3, Protocol A, step 3(c)).

## Main results

* `Cslib.Distributed.BenOr.probRun_not_unanimous_le`: pre-coin phase-scheduler parametric bound
  `(1 - p) ^ k` on non-unanimity after `k` phases whenever `∀ b, p ≤ coinLaw (fun _ => b)`.
* `Cslib.Distributed.BenOr.probRun_not_allDecided_le`: pre-coin phase-scheduler parametric bound
  `(1 - p) ^ k` on `¬ AllDecided` after `k + 1` phases.
* `Cslib.Distributed.BenOr.tendsto_probRun_not_allDecided`: under a pre-coin phase-boundary
  scheduler, non-decision probability tends to `0` as the phase count tends to `∞` whenever `0 < p`.
* `Cslib.Distributed.BenOr.probRun_commonCoin_not_allDecided_le`,
  `Cslib.Distributed.BenOr.tendsto_probRun_commonCoin_not_allDecided`: `(1 / 2) ^ k` tail bound and
  limit `0` for the separate common-coin variant under pre-coin phase-boundary schedulers.
* `Cslib.Distributed.BenOr.probRun_localCoin_not_allDecided_le`,
  `Cslib.Distributed.BenOr.tendsto_probRun_localCoin_not_allDecided`: pre-coin phase-scheduler step
  after [BenOr1983], §3 (`(1 - (1 / 2) ^ |P|) ^ k` tail bound and limit `0` for `probRun`; full §2
  asynchronous schedulers tracked in #7120).

## References

* [M. Ben-Or, *Another advantage of free choice: completely asynchronous agreement
  protocols*][BenOr1983]
-/

public section

namespace Cslib.Distributed.BenOr

open scoped ENNReal
open Cslib.Probability.PMF Filter

/-! ### Sequential probabilistic execution and coin laws -/

/-- State distribution after `k` phases of Ben-Or's protocol from initial inputs `inp`. At the
boundary of each phase `r`, the pre-coin per-phase state-adaptive scheduler `strat r st` commits
all processes' Stage-1 and Stage-2 quorums from the current global state `st`, before the phase-`r`
coin vector is sampled from `coinLaw`. -/
noncomputable def probRun {P : Type*} [Fintype P] (t : ℕ)
    (coinLaw : PMF (P → Bool))
    (strat : ℕ → (P → ProcState) → PhaseSchedule P)
    (inp : P → Bool) : ℕ → PMF (P → ProcState)
  | 0 => PMF.pure (initState inp)
  | r + 1 => (probRun t coinLaw strat inp r).bind fun st =>
      coinLaw.map fun c => phaseStep t (strat r st) c st

/-- Separate shared-coin variant (not in [BenOr1983]): sample one uniform bit `b : Bool` and supply
`fun _ => b` to all processes. -/
noncomputable def commonCoinLaw (P : Type*) : PMF (P → Bool) :=
  (uniformOfFintype Bool).map fun b _ => b

open Classical in
/-- Independent local fair coins (after [BenOr1983], §3, Protocol A, step 3(c), printed p. 28):
sample `c : P → Bool` uniformly from all `2 ^ |P|` coin assignments. -/
noncomputable def localCoinLaw (P : Type*) [Fintype P] : PMF (P → Bool) :=
  uniformOfFintype (P → Bool)

/-- Under `commonCoinLaw P`, each constant coin vector `fun _ => b` has mass at least `1 / 2`
(including when `P` is empty, where both constant vectors coincide and have mass `1`). -/
theorem half_le_commonCoinLaw (P : Type*) (b : Bool) :
    (1 / 2 : ℝ≥0∞) ≤ commonCoinLaw P (fun _ => b) := by
  classical
  rw [commonCoinLaw, PMF.map_apply, tsum_fintype]
  simpa [uniformOfFintype_apply, one_div] using Finset.single_le_sum
    (f := fun a : Bool =>
      if (fun _ : P => b) = (fun _ : P => a) then uniformOfFintype Bool a else 0)
    (fun _ _ => bot_le) (Finset.mem_univ b)

/-- On a nonempty process set `P`, `commonCoinLaw P` assigns probability `1 / 2` to each constant
coin vector `fun _ => b`. -/
theorem commonCoinLaw_const {P : Type*} [Nonempty P] (b : Bool) :
    commonCoinLaw P (fun _ => b) = (1 / 2 : ℝ≥0∞) := by
  classical
  obtain ⟨p₀⟩ := ‹Nonempty P›
  rw [commonCoinLaw, PMF.map_apply, tsum_eq_single b]
  · simp [uniformOfFintype_apply, one_div]
  · exact fun _ hb' => ite_eq_right fun h => hb' (congrFun h p₀).symm

/-- Under `localCoinLaw P`, every coin assignment `c : P → Bool` has probability `(1 / 2) ^ |P|`. -/
@[simp]
theorem localCoinLaw_apply {P : Type*} [Fintype P] (c : P → Bool) :
    localCoinLaw P c = (1 / 2 : ℝ≥0∞) ^ Fintype.card P := by
  classical
  rw [localCoinLaw, uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, one_div]

/-! ### Support invariants and single-phase probability bounds -/

private lemma singlePhase_not_unanimous_le {P : Type*} [Fintype P] (t : ℕ)
    {coinLaw : PMF (P → Bool)} {p : ℝ≥0∞}
    (hcoin : ∀ b : Bool, p ≤ coinLaw (fun _ => b))
    (sched : PhaseSchedule P) (st : P → ProcState) :
    (coinLaw.map fun c => phaseStep t sched c st).toOuterMeasure {st' | ¬ IsUnanimous st'} ≤
      1 - p := by
  obtain ⟨b, hb⟩ := phaseStep_lucky_coin t sched st
  refine toOuterMeasure_compl_le_one_sub _ {st' | IsUnanimous st'} ((hcoin b).trans ?_)
  rw [PMF.toOuterMeasure_map_apply, ← coinLaw.toOuterMeasure_apply_singleton]
  exact coinLaw.toOuterMeasure.mono (Set.singleton_subset_iff.mpr ⟨b, hb⟩)

private lemma singlePhase_not_unanimous_eq_zero {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) (coinLaw : PMF (P → Bool))
    {sched : PhaseSchedule P} (hv : sched.Valid t)
    {st : P → ProcState} (hu : IsUnanimous st) :
    (coinLaw.map fun c => phaseStep t sched c st).toOuterMeasure {st' | ¬ IsUnanimous st'} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro _ hsupp hnot; supp_cases hsupp with ⟨c, _, rfl⟩
  exact hnot (hu.phaseStep ht hv c)

private lemma probRun_support_estimateLocked {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) (coinLaw : PMF (P → Bool))
    {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (inp : P → Bool) :
    ∀ k, (∀ r < k, ∀ st, (strat r st).Valid t) →
      ∀ st ∈ (probRun t coinLaw strat inp k).support, EstimateLocked st
  | 0, _, _, hst => by supp_cases hst [probRun]; exact estimateLocked_initState inp
  | k + 1, hv, _, hst' => by
    supp_cases hst' [probRun] with ⟨st, hst, c, _, rfl⟩
    exact (probRun_support_estimateLocked ht coinLaw inp k
      (fun r hr => hv r (Nat.lt_succ_of_lt hr)) st hst).phaseStep ht
      (hv k (Nat.lt_succ_self k) st) c

private lemma singlePhase_not_allDecided_eq_zero {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) (coinLaw : PMF (P → Bool))
    {sched : PhaseSchedule P} (hv : sched.Valid t)
    {st : P → ProcState} (hlock : EstimateLocked st) (hu : IsUnanimous st) :
    (coinLaw.map fun c => phaseStep t sched c st).toOuterMeasure {st' | ¬ AllDecided st'} = 0 := by
  obtain ⟨b, hb⟩ := hu
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro _ hsupp hnot; supp_cases hsupp with ⟨c, _, rfl⟩
  exact hnot ⟨b, phaseStep_allDecided_of_est_eq ht hv c hlock hb⟩

/-! ### Parametric multi-phase tail bounds under pre-coin phase schedulers -/

/-- Pre-coin phase-scheduler non-unanimity step: when each phase's `PhaseSchedule` is committed
from the phase boundary state before `coinLaw` is sampled, if `coinLaw` assigns mass at least `p`
to both constant coin vectors `fun _ => true` and `fun _ => false` and `2 * t < |P|`, the
probability under `probRun` that process estimates are not unanimous after `k` phases is at most
`(1 - p) ^ k`. -/
theorem probRun_not_unanimous_le {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {coinLaw : PMF (P → Bool)} {p : ℝ≥0∞}
    (hcoin : ∀ b : Bool, p ≤ coinLaw (fun _ => b))
    {strat : ℕ → (P → ProcState) → PhaseSchedule P} (inp : P → Bool)
    (k : ℕ) (hv : ∀ r < k, ∀ st, (strat r st).Valid t) :
    (probRun t coinLaw strat inp k).toOuterMeasure {st | ¬ IsUnanimous st} ≤ (1 - p) ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using toOuterMeasure_le_one _ _
  | succ k ih =>
    rw [probRun, pow_succ]
    exact toOuterMeasure_bind_le_mul_ennreal _ _ {st | ¬ IsUnanimous st} {st | ¬ IsUnanimous st}
      (ih fun r hr => hv r (Nat.lt_succ_of_lt hr))
      (fun st _ _ => singlePhase_not_unanimous_le t hcoin (strat k st) st)
      (fun st _ h => singlePhase_not_unanimous_eq_zero ht coinLaw (hv k (Nat.lt_succ_self k) st)
        (Classical.not_not.mp h))

/-- Pre-coin phase-scheduler non-decision tail step: when each phase's `PhaseSchedule` is committed
from the phase boundary state before `coinLaw` is sampled, after `k + 1` phases (`k` coin-alignment
phases plus one deterministic decision phase) the probability under `probRun` that processes have
not all decided a common value is at most `(1 - p) ^ k`. -/
theorem probRun_not_allDecided_le {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {coinLaw : PMF (P → Bool)} {p : ℝ≥0∞}
    (hcoin : ∀ b : Bool, p ≤ coinLaw (fun _ => b))
    {strat : ℕ → (P → ProcState) → PhaseSchedule P} (inp : P → Bool)
    (k : ℕ) (hv : ∀ r < k + 1, ∀ st, (strat r st).Valid t) :
    (probRun t coinLaw strat inp (k + 1)).toOuterMeasure {st | ¬ AllDecided st} ≤ (1 - p) ^ k := by
  simpa only [probRun, mul_one] using toOuterMeasure_bind_le_mul_ennreal
    (probRun t coinLaw strat inp k)
    (fun st => coinLaw.map fun c => phaseStep t (strat k st) c st)
    {st | ¬ IsUnanimous st} {st | ¬ AllDecided st}
    (probRun_not_unanimous_le ht hcoin inp k fun r hr => hv r (Nat.lt_succ_of_lt hr))
    (fun _ _ _ => toOuterMeasure_le_one _ _)
    (fun st hsupp h => singlePhase_not_allDecided_eq_zero ht coinLaw
      (hv k (Nat.lt_succ_self k) st)
      (probRun_support_estimateLocked ht coinLaw inp k
        (fun r hr => hv r (Nat.lt_succ_of_lt hr)) st hsupp)
      (Classical.not_not.mp h))

/-- Pre-coin phase-scheduler convergence step: whenever `0 < p`, `∀ b, p ≤ coinLaw (fun _ => b)`,
and `strat` commits valid `n - t` phase quorums from each phase boundary state before `coinLaw` is
sampled, the non-decision marginal of `probRun` after `m` phases converges to `0` as `m → ∞`. -/
theorem tendsto_probRun_not_allDecided {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {coinLaw : PMF (P → Bool)} {p : ℝ≥0∞}
    (hp : 0 < p) (hcoin : ∀ b : Bool, p ≤ coinLaw (fun _ => b))
    {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (hv : ∀ r st, (strat r st).Valid t) (inp : P → Bool) :
    Tendsto (fun m => (probRun t coinLaw strat inp m).toOuterMeasure {st | ¬ AllDecided st})
      atTop (nhds 0) := by
  have hlt : 1 - p < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'
  have hpow : Tendsto (fun m : ℕ => (1 - p) ^ (m - 1)) atTop (nhds 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).comp (tendsto_sub_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  simpa only [Nat.add_sub_cancel] using
    probRun_not_allDecided_le ht hcoin inp k (fun r _ st => hv r st)

/-! ### Separate common-coin variant (`≤ (1 / 2) ^ k`) -/

private lemma one_sub_half_ennreal : (1 : ℝ≥0∞) - (1 / 2 : ℝ≥0∞) = 1 / 2 := by
  have : (1 / 2 : ℝ≥0∞) ≤ 1 := by norm_num
  ennreal_to_real; norm_num

/-- Pre-coin phase-scheduler tail bound for the separate common-coin variant (`commonCoinLaw P`,
not in [BenOr1983]): when each phase's quorums are committed from the phase boundary state before
sampling the shared coin and `2 * t < |P|`, the non-decision probability under `probRun` after
`k + 1` phases is at most `(1 / 2) ^ k`. -/
theorem probRun_commonCoin_not_allDecided_le {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (inp : P → Bool) (k : ℕ) (hv : ∀ r < k + 1, ∀ st, (strat r st).Valid t) :
    (probRun t (commonCoinLaw P) strat inp (k + 1)).toOuterMeasure {st | ¬ AllDecided st} ≤
      (1 / 2 : ℝ≥0∞) ^ k := by
  simpa only [one_sub_half_ennreal] using
    probRun_not_allDecided_le ht (half_le_commonCoinLaw P) inp k hv

/-- Pre-coin phase-scheduler convergence for the separate common-coin variant (`commonCoinLaw P`,
not in [BenOr1983]): when each phase's quorums are committed from the phase boundary state before
sampling the shared coin and `2 * t < |P|`, the non-decision marginal of `probRun` after `m` phases
tends to `0` as `m → ∞`. -/
theorem tendsto_probRun_commonCoin_not_allDecided {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (hv : ∀ r st, (strat r st).Valid t) (inp : P → Bool) :
    Tendsto
      (fun m => (probRun t (commonCoinLaw P) strat inp m).toOuterMeasure {st | ¬ AllDecided st})
      atTop (nhds 0) :=
  tendsto_probRun_not_allDecided ht (by simp [one_div]) (half_le_commonCoinLaw P) hv inp

/-! ### Independent local fair coins: pre-coin phase-scheduler step (`≤ (1 - (1 / 2) ^ |P|) ^ k`) -/

/-- Pre-coin phase-scheduler termination step (not the full asynchronous scheduler theorem of
[BenOr1983]; see #7120), after [BenOr1983], §3, Protocol A (printed p. 28): when each phase's
quorum schedule `strat r st` is committed from the phase boundary state `st` before sampling the
entire independent local coin vector `localCoinLaw P` and `2 * t < |P|`, the probability under
`probRun` that processes have not all decided a common value after `k + 1` phases is at most
`(1 - (1 / 2) ^ |P|) ^ k`. -/
theorem probRun_localCoin_not_allDecided_le {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (inp : P → Bool) (k : ℕ) (hv : ∀ r < k + 1, ∀ st, (strat r st).Valid t) :
    (probRun t (localCoinLaw P) strat inp (k + 1)).toOuterMeasure {st | ¬ AllDecided st} ≤
      (1 - (1 / 2 : ℝ≥0∞) ^ Fintype.card P) ^ k :=
  probRun_not_allDecided_le ht (fun b => (localCoinLaw_apply (fun _ => b)).ge) inp k hv

/-- Pre-coin phase-scheduler convergence step toward Theorem 1(i) of [BenOr1983] (§3, Protocol A,
printed pp. 28–29; full history-dependent asynchronous step/delivery schedulers of §2 remain
tracked in #7120): when each phase's quorum schedule `strat r st` is committed from the phase
boundary state `st` before sampling `localCoinLaw P` and `2 * t < |P|`, the non-decision marginal
of `probRun` after `m` phases tends to `0` as `m → ∞`. -/
theorem tendsto_probRun_localCoin_not_allDecided {P : Type*} [Fintype P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (hv : ∀ r st, (strat r st).Valid t) (inp : P → Bool) :
    Tendsto
      (fun m => (probRun t (localCoinLaw P) strat inp m).toOuterMeasure {st | ¬ AllDecided st})
      atTop (nhds 0) :=
  tendsto_probRun_not_allDecided ht (pos_iff_ne_zero.mpr (pow_ne_zero _ (by simp [one_div])))
    (fun b => (localCoinLaw_apply (fun _ => b)).ge) hv inp

end Cslib.Distributed.BenOr
