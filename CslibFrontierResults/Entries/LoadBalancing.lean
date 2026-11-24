/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.LoadBalancing.Basic
import CslibFrontier.GameTheory.LoadBalancing.MixedNash
import CslibFrontier.GameTheory.LoadBalancing.PureNash
import CslibFrontier.GameTheory.LoadBalancing.PurePoA

/-!
# Result registry entries for selfish load-balancing games
-/

open Cslib.GameTheory
open Cslib.GameTheory.LoadBalancingGame

register_result "load-balancing-pure-nash-characterization" where
  title := "Pure Nash equilibrium characterization and scheduling agreement for selfish \
    load-balancing games"
  topic := "game theory"
  sources := [
    { paper := Vocking2007, theorem := unverified, locator := unverified },
    { paper := KoutsoupiasPapadimitriou1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.isPureNash_iff,
    LoadBalancingGame.sum_weight_le_sum_speed_mul_optMakespan,
    LoadBalancingGame.IsIdentical.makespan_eq_scheduling,
    LoadBalancingGame.IsIdentical.optMakespan_eq_scheduling
  ]
  scope := "Over uniformly related load-balancing games LoadBalancingGame ι M with finite jobs \
    [Fintype ι] [DecidableEq ι], decidable machines [DecidableEq M], nonnegative job weights, \
    and strictly positive machine speeds: characterizes CostGame.IsPureNash via load A (A i) ≤ \
    load A k + weight i / speed k for all k ≠ A i ([Vocking2007]), proves the \
    speed-weighted volume lower bound on optMakespan, and identifies load, makespan, and \
    optMakespan on identical Fin n / Fin m instances with Cslib.Algorithms.Lean.Scheduling."

register_result "load-balancing-fip-pos-one" where
  title := "Finite improvement property, pure Nash existence, and price of stability 1 in \
    selfish load-balancing games"
  topic := "game theory"
  sources := [
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    UnrelatedLoadBalancingGame.hasFIP_of_pos,
    UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_optMakespan_of_pos,
    LoadBalancingGame.hasFIP,
    LoadBalancingGame.exists_isPureNash,
    LoadBalancingGame.exists_isPureNash_makespan_eq_optMakespan
  ]
  scope := "Establishes CostGame.HasFIP, pure Nash equilibrium existence, and price of stability 1 \
    (existence of a pure Nash equilibrium with makespan equal to optMakespan) for all finite \
    uniformly related load-balancing games including zero-weight jobs (via lexicographic descent \
    on sorted machine loads with CostGame.socialCost tie-breaking) and for finite unrelated \
    load-balancing games with strictly positive processing times ([Vocking2007])."

register_result "load-balancing-max-weight-best-response-convergence" where
  title := "Linear-step convergence of max-weight best-response dynamics on identical machines"
  topic := "game theory"
  sources := [
    { paper := EvenDarKesselmanMansour2003, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.IsIdentical.maxWeightBestResponse_injective,
    LoadBalancingGame.IsIdentical.maxWeightBestResponse_length_le,
    LoadBalancingGame.IsIdentical.exists_maxWeightBestResponse_isPureNash
  ]
  scope := "For any finite job set [Fintype ι] and finite nonempty identical machine set \
    (G.IsIdentical), every sequence of max-weight best-response steps activates each job at most \
    once (Function.Injective move), has length at most |ι|, and reaches a pure Nash equilibrium \
    from any initial assignment A₀ in at most |ι| steps ([EvenDarKesselmanMansour2003]; \
    [Vocking2007])."

register_result "load-balancing-lpt-pure-nash" where
  title := "Graham's LPT rule produces a pure Nash equilibrium on uniformly related and identical \
    machines"
  topic := "game theory"
  sources := [
    { paper := FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002,
      theorem := unverified,
      locator := unverified },
    { paper := Graham1969, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.IsRelatedLPT.isPureNash,
    LoadBalancingGame.exists_isPureNash_of_lptOrder,
    LoadBalancingGame.IsIdentical.isRelatedLPT_iff_isListSchedule,
    LoadBalancingGame.IsIdentical.isPureNash_lptSchedule,
    LoadBalancingGame.IsIdentical.makespan_lptSchedule_le
  ]
  scope := "On uniformly related machines with Fin n jobs sorted by non-increasing weight, greedy \
    post-insertion load minimization (IsRelatedLPT) produces a pure Nash equilibrium \
    ([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]). On \
    Fin m identical machines with [NeZero m], IsRelatedLPT coincides with \
    Scheduling.IsListSchedule and Graham's computable Scheduling.lptSchedule is itself a pure \
    Nash equilibrium achieving makespan ≤ (4 / 3 - 1 / (3m)) * optMakespan ([Graham1969])."

register_result "load-balancing-identical-pure-poa" where
  title := "Exact 2m / (m + 1) pure price of anarchy and tightness on m identical machines"
  topic := "game theory"
  sources := [
    { paper := FinnHorowitz1979, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.IsIdentical.makespan_le_of_isPureNash,
    LoadBalancingGame.IsIdentical.makespan_lt_two_mul_of_isPureNash,
    LoadBalancingGame.IsIdentical.makespan_le_four_thirds_of_isPureNash,
    LoadBalancingGame.isPureNash_finnHorowitzTightNE,
    LoadBalancingGame.makespan_finnHorowitzTightNE_eq_ratio,
    LoadBalancingGame.IsIdentical.makespan_eq_opt_of_three_jobs_two_machines,
    LoadBalancingGame.IsIdentical.makespan_le_optMakespan_add_of_weight_le
  ]
  scope := "For finite jobs on m = |M| ≥ 1 identical machines (G.IsIdentical), every pure Nash \
    equilibrium A satisfies makespan A ≤ (2m / (m + 1)) * optMakespan ([FinnHorowitz1979]; \
    [Vocking2007]), matched with equality for every m ≥ 1 on the explicit 2m-job \
    instance finnHorowitzTight m ([Vocking2007]). Also proves optimality of all \
    pure Nash equilibria for 3 jobs on 2 identical machines and the additive \
    small-job bound optMakespan + (1 - 1 / m) * B when ∀ i, weight i ≤ B ([Vocking2007])."

register_result "load-balancing-two-related-golden-ratio-poa" where
  title := "Exact golden-ratio pure price of anarchy on two uniformly related machines"
  topic := "game theory"
  sources := [
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.makespan_le_goldenRatio_mul_optMakespan,
    LoadBalancingGame.isPureNash_goldenRatioTightNE,
    LoadBalancingGame.makespan_goldenRatioTightNE
  ]
  scope := "For any finite set of jobs on Fin 2 uniformly related machines, every pure Nash \
    equilibrium satisfies makespan A ≤ ((1 + √5) / 2) * optMakespan, and the 2-job instance \
    goldenRatioTight attains exact equality ((1 + √5) / 2) * optMakespan ([Vocking2007])."

register_result "load-balancing-related-pure-poa-log-over-log-log" where
  title := "Factorial and O(log m / log log m) pure price of anarchy on uniformly related machines"
  topic := "game theory"
  sources := [
    { paper := CzumajVocking2002, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.card_speedPrefix_ge,
    LoadBalancingGame.factorial_le_card_of_makespan_ge,
    LoadBalancingGame.makespan_le_log_div_log_log_mul_optMakespan
  ]
  scope := "For finite uniformly related load-balancing games on M, proves the speed-prefix \
    chain bound (k + 1) * #(L_{k+1}) ≤ #(L_k) ([Vocking2007]), the factorial bound \
    (c + 1) * optMakespan ≤ makespan A → c! ≤ |M|, and for 3 ≤ |M| the explicit bound \
    makespan A ≤ (4 * log |M| / log (log |M|) + 3) * optMakespan ([CzumajVocking2002]; \
    [Vocking2007])."

register_result "load-balancing-unrelated-unbounded-pure-poa" where
  title := "Unbounded pure price of anarchy on two unrelated machines"
  topic := "game theory"
  sources := [
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_mul_optMakespan
  ]
  scope := "For every K ≥ 1, constructs a 2-job, 2-machine UnrelatedLoadBalancingGame with \
    optMakespan = 1 and a pure Nash equilibrium of makespan K * optMakespan."

register_result "load-balancing-mixed-nash-characterization-and-uniqueness" where
  title := "Mixed Nash deviation-cost characterization and uniqueness of totally mixed Nash \
    equilibria"
  topic := "game theory"
  sources := [
    { paper := KoutsoupiasPapadimitriou1999, theorem := unverified, locator := unverified },
    { paper := MavronicolasSpirakis2001, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.deviationCost_toCostGame,
    LoadBalancingGame.isMixedNash_iff,
    LoadBalancingGame.eq_of_isTotallyMixedNash,
    LoadBalancingGame.exists_isTotallyMixedNash_twoUnitRelated_iff,
    LoadBalancingGame.isTotallyMixedNash_twoUnitRelated_eq
  ]
  scope := "Proves the closed-form expected deviation cost E[ℓ_j] + (1 - p_i^j) * w_i / s_j and \
    mixed Nash support characterization ([Vocking2007]), uniqueness of totally \
    mixed Nash equilibria whenever all job weights are strictly positive and |ι| ≠ 1 \
    ([MavronicolasSpirakis2001]; [Vocking2007]), and the exact 1 / 2 < s < 2 \
    characterization and closed form for 2 unit jobs on 2 related machines of speeds (1, s) \
    ([Vocking2007])."

register_result "load-balancing-kp-two-identical-mixed-poa" where
  title := "Koutsoupias–Papadimitriou exact 3 / 2 mixed price of anarchy on two identical machines"
  topic := "game theory"
  sources := [
    { paper := KoutsoupiasPapadimitriou1999, theorem := unverified, locator := unverified },
    { paper := Vocking2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    LoadBalancingGame.IsIdentical.expectedMakespan_le_three_halves_mul_optMakespan,
    LoadBalancingGame.isMixedNash_kpTwoUnitUniform,
    LoadBalancingGame.expectedMakespan_kpTwoUnitUniform
  ]
  scope := "For any finite set of jobs with nonnegative weights on 2 identical machines, every \
    mixed Nash equilibrium p satisfies expectedMakespan p ≤ (3 / 2) * optMakespan \
    ([KoutsoupiasPapadimitriou1999]), attained with equality by the uniform mixed equilibrium on \
    2 unit jobs (kpTwoUnit / kpTwoUnitUniform)."
