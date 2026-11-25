/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound
import CslibFrontier.DataStructure.Dictionary.WordRAM.LowerBound

/-!
# Collected results: tight cell-probe and Word-RAM lower bounds for dynamic succinct dictionaries

Registers the cell-probe lower bounds (`CellProbe.LowerBound`, PR #5704, Milestone 4 of #3140)
and contrapositive Word-RAM transfer corollaries (`WordRAM.LowerBound`, PR #7973, Milestone 5 of
#3140) for dynamic succinct dictionaries from Li, Liang, Yu, and Zhou ([LiLiangYuZhou2023],
`arXiv:2306.02253v3`, where printed page `p` is PDF page `p + 1`).
-/

section
open Cslib.DataStructure.Dictionary.CellProbe

register_result "dict-cell-probe-iterlog-redundancy" where
  title := "Iterated-log cell-probe lower bound for dynamic succinct dictionaries"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.1 and Theorem 3.1",
      locator := "arXiv:2306.02253v3, Section 1, p. 1 (PDF p. 2); \
        Section 3, pp. 10–13 (PDF pp. 11–14); Section 7, pp. 26–27 (PDF pp. 27–28)" }
  ]
  theorems := [
    det_expectedSeqProbes_ge_of_iterLog_redundancy,
    expectedSeqProbes_ge_of_iterLog_redundancy,
    det_expectedSeqProbes_ge_iterLogStar,
    expectedSeqProbes_ge_iterLogStar
  ]
  scope := "Unconditional cell-probe lower bounds (no cryptographic or oracle assumptions) for \
    dynamic dictionaries over n keys in [U] with values in [V] under exact-history deterministic \
    IndexedScheme and private-coin zero-error (Las Vegas) randomized CellProbe.Randomized.Scheme \
    models with cells * w total memory bits. For every fixed α > 0, c_R ≥ 0, and c_w ≥ 0, a \
    uniform constant c > 0 is chosen before all varying parameters (U, V, n, k, cells, w) and \
    schemes: under 2 ≤ n, 4 * n ≤ U, n ^ (1 + α) ≤ U, 1 ≤ V, 1 ≤ k ≤ Nat.logStar n, \
    w ≤ c_w * (log₂ U + log₂ V), and \
    cells * w ≤ benchmarkBits U V n + c_R * n * max (Nat.iterLog k n) 1 (or \
    benchmarkBits U V n + c_R * n for the log* n specialization), any scheme exact on \
    validHistoriesUpTo U V n (4 * n + 1) incurs at least c * n * k (resp. c * n * log* n) \
    expected cell probes over the oblivious insertQueryDeleteDist distribution (4 * n charged \
    operations; correctness horizon 4 * n + 1 provides one trailing query step for decodeDict). \
    Exactness on admissible histories is an input hypothesis placed on the same scheme whose \
    probes are bounded (not proved by these endpoints); \
    CslibFrontierTests/DictLowerBoundMultilevel.lean proves that hypothesis for its concrete \
    two-cell fixture scheme. Space benchmark \
    benchmarkBits U V n = log₂ C(U, n) + n * log₂ V is bridged to Dynamic.optBits in \
    LowerBound.lean. Internal steps (OuterGame.lean Lemma 3.2, LowerBound.lean Lemma 8.1) use a \
    deterministic c = 1 probe cap and Step 6 Markov sub-conditioning for large values V > U ^ 3 \
    without adding hypotheses to the endpoints. Bounded-error Monte Carlo schemes and adaptive \
    sequence adversaries are not covered (see dict-wordram-iterlog-redundancy for the Word-RAM \
    transfer). Outside-fleet source checks: \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911577643, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911560173, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911573135, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016497849, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016914204, \
    and https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6028316750."

register_result "dict-cell-probe-sublinear-redundancy" where
  title := "Sublinear-redundancy and combined cell-probe lower bounds for dynamic succinct \
    dictionaries"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.2 and Theorem 6.1 (combined with Theorem 1.1)",
      locator := "arXiv:2306.02253v3, Section 1, pp. 1–2 (PDF pp. 2–3); \
        Section 6, pp. 25–26 (PDF pp. 26–27); Section 7, pp. 26–27 (PDF pp. 27–28)" }
  ]
  theorems := [
    det_expectedSeqProbes_ge_of_sublinear_redundancy,
    expectedSeqProbes_ge_of_sublinear_redundancy,
    det_expectedSeqProbes_ge_iterLogStar_add_log_div,
    expectedSeqProbes_ge_iterLogStar_add_log_div
  ]
  scope := "Unconditional cell-probe lower bounds (no cryptographic or oracle assumptions) for \
    dynamic dictionaries in the exact-history deterministic IndexedScheme and private-coin \
    zero-error (Las Vegas) randomized CellProbe.Randomized.Scheme models over the oblivious \
    insertQueryDeleteDist distribution (4 * n charged operations; correctness on \
    validHistoriesUpTo U V n (4 * n + 1)). For every fixed α > 0 and c_w ≥ 0 (plus c_R ≥ 0 for \
    the combined bound), a uniform constant c > 0 is chosen before all varying parameters \
    (U, V, n, R, cells, w) and schemes: under 2 ≤ n, 4 * n ≤ U, n ^ (1 + α) ≤ U, 1 ≤ V, \
    w ≤ c_w * (log₂ U + log₂ V), and cells * w ≤ benchmarkBits U V n + R, the standalone \
    endpoints assume R ≤ n and give c * n * log₂(n / max R 1) expected probes (vanishing at the \
    boundary R = n where log₂(n / max n 1) = 0), while the combined endpoints cover all \
    R ≤ c_R * n and give c * n * (log* n + max 0 (log₂(n / max R 1))). Exactness on admissible \
    histories is an input hypothesis placed on the same scheme whose probes are bounded (not \
    proved by these endpoints); CslibFrontierTests/DictLowerBoundMultilevel.lean proves that \
    hypothesis for its concrete two-cell fixture scheme. Bounded-error Monte Carlo schemes and \
    adaptive sequence adversaries are not covered (see dict-wordram-sublinear-redundancy for the \
    Word-RAM transfer). Outside-fleet source checks: \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911577643, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911560173, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911573135, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016497849, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016914204, \
    and https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6028316750."

register_result "dict-cell-probe-update-lower-bound" where
  title := "Update-only cell-probe lower bounds for dynamic succinct dictionaries with large values"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.3(1)–(2)",
      locator := "arXiv:2306.02253v3, Section 1, p. 2 (PDF p. 3); \
        Section 8, pp. 27–30 (PDF pp. 28–31)" }
  ]
  theorems := [
    det_expectedSeqProbes_update_ge_iterLog,
    expectedSeqProbes_update_ge_iterLog,
    det_expectedSeqProbes_update_ge_iterLogStar,
    expectedSeqProbes_update_ge_iterLogStar,
    det_expectedSeqProbes_update_ge_sublinear,
    expectedSeqProbes_update_ge_sublinear,
    det_expectedSeqProbes_update_ge_iterLogStar_add_log_div,
    expectedSeqProbes_update_ge_iterLogStar_add_log_div
  ]
  scope := "Unconditional update-only cell-probe lower bounds (no query-time constraint, no \
    cryptographic or oracle assumptions) for dynamic dictionaries under exact-history \
    deterministic IndexedScheme and private-coin zero-error (Las Vegas) randomized \
    CellProbe.Randomized.Scheme models over the oblivious insertDeleteDist distribution (3 * n \
    charged insert/delete updates). Correctness is assumed on validHistoriesUpTo U V n (3 * n + 1) \
    so one trailing query step witnesses decodeDict after the PUnit-returning updates without \
    charging that query in the probe sum. For every fixed α_V > 0 and c_w ≥ 0 (plus c_R ≥ 0 for \
    the iterLog, log* n, and combined variants), a uniform constant c > 0 is chosen before all \
    varying parameters (U, V, n, k, R, cells, w) and schemes under 2 ≤ n, 3 * n ≤ U, 1 ≤ V, \
    U ^ (2 + α_V) ≤ V * n ^ 2, and w ≤ c_w * (log₂ U + log₂ V): the iterated-log variants assume \
    1 ≤ k ≤ Nat.logStar n and cells * w ≤ benchmarkBits U V n + c_R * n * max (Nat.iterLog k n) 1 \
    to give c * n * k expected probes; the log* n variants assume \
    cells * w ≤ benchmarkBits U V n + c_R * n to give c * n * log* n expected probes; and the \
    sublinear (R ≤ n, vanishing at R = n) and combined (R ≤ c_R * n) variants take the allowed \
    redundancy R via cells * w ≤ benchmarkBits U V n + R to give c * n * log₂(n / max R 1) and \
    c * n * (log* n + max 0 (log₂(n / max R 1))) expected probes respectively. Proved via the \
    query-free modified inner game (Lemma 8.1) with internal deterministic c = 1 probe cap and \
    Step 6 Markov sub-conditioning (extra 2 * γ * m * log₂ U budget absorbed without strengthening \
    U ^ (2 + α_V) ≤ V * n ^ 2). Exactness on admissible histories (validHistoriesUpTo U V n \
    (3 * n + 1)) is an input hypothesis placed on the same scheme whose probes are bounded (not \
    proved by these endpoints); CslibFrontierTests/DictLowerBoundMultilevel.lean proves that \
    hypothesis for its concrete two-cell fixture scheme. Bounded-error Monte Carlo schemes and \
    adaptive adversaries are not covered (see dict-wordram-update-lower-bound for the Word-RAM \
    transfer). Outside-fleet source checks: \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911577643, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911573135, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-5911560173, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016497849, \
    https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6016914204, \
    and https://github.com/cslib-community/cslib-frontier/pull/5704#pullrequestreview-6028316750."

end

section
open Cslib.DataStructure.Dictionary.WordRAM

register_result "dict-wordram-iterlog-redundancy" where
  title := "Iterated-log Word-RAM lower bound for dynamic succinct dictionaries"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.1 and Theorem 3.1 (Section 1 footnote 1 Word-RAM transfer)",
      locator := "arXiv:2306.02253v3, Section 1, p. 1 and footnote 1 (PDF p. 2); \
        Section 3, pp. 10–13 (PDF pp. 11–14); Section 7, pp. 26–27 (PDF pp. 27–28)" }
  ]
  theorems := [
    expectedFlatTime_ge_of_iterLog_redundancy,
    expectedTotalCost_ge_of_iterLog_redundancy
  ]
  scope := "Contrapositive Word-RAM transfer (via CslibFrontier.DataStructure.CellProbe.OfWordRAM, \
    unconditional, no cryptographic or oracle assumptions) of dict-cell-probe-iterlog-redundancy \
    over any Word-RAM basis B. For every fixed α > 0, c_R ≥ 0, c_w ≥ 0, and persistent-register \
    bound r_max : ℕ, a uniform constant c > 0 is chosen before all varying parameters \
    (B, U, V, n, k, w, base, space / r_ds, k_init, params) and implementations: under 2 ≤ n, \
    4 * n ≤ U, n ^ (1 + α) ≤ U, 1 ≤ V, 1 ≤ k ≤ Nat.logStar n, and \
    w ≤ c_w * (log₂ U + log₂ V), expectedFlatTime_ge_of_iterLog_redundancy assumes \
    persCount input ≤ r_max, memory premise \
    (space + persCount input) * w ≤ benchmarkBits U V n + c_R * n * max (Nat.iterLog k n) 1, \
    initial PMF ν₀ bounded within [base, base + space), and finite zero-error realization \
    (ExecFlatProgramOps, T_ops ≠ ⊤) of Dynamic.spec U V n up to horizon 4 * n + 1. Via the \
    checked tightening bridge ExecFlatProgramOps.tighten_actualBodyTime, it lower-bounds the \
    exact intrinsic expected non-halt body-instruction count \
    flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops (with total executed \
    instructions flatExpectedTime = flatExpectedBodyTime + ops.length, and \
    flatExpectedBodyTime ≤ T_ops for any certified budget T_ops) by ENNReal.ofReal (c * n * k) \
    on oblivious insertQueryDeleteDist (specializing to Ω(n * log* n) at k = Nat.logStar n). \
    Here 2 * persCount input reload/spill cell probes per step are absorbed into \
    c_cp / (2 * r_max + 1) because no zero-body-instruction program (p_op[0]? = some (.halt _)) \
    realizes Dynamic.spec U V n for 1 ≤ n, 2 ≤ U, 1 ≤ V. The companion corollary \
    expectedTotalCost_ge_of_iterLog_redundancy bounds C.initPotential + E[totalCost C.charge] \
    (CLRS2009 §17.3) for any zero-error WordRAM.Randomized.StateTransitionImpl C (or deterministic \
    StateTransitionImpl.toRandomized) with persistentRegCount P ≤ r_max, memory premise \
    (C.space + persistentRegCount P) * w ≤ benchmarkBits U V n + c_R * n * max (Nat.iterLog k n) \
    1, and base/parameter word-fit hypotheses. Correctness/realization is an input hypothesis on \
    the same program or implementation whose running time is bounded (not proved by these \
    endpoints); CslibFrontierTests/DictLowerBoundWordRAM.lean proves those hypotheses for its \
    concrete Basis.standard two-slot fixture programs. Bounded-error Monte Carlo schemes and \
    adaptive sequence adversaries are not covered. Outside-fleet source checks: PR #5704 \
    (reviews 5911577643, 5911560173, 5911573135, 6016497849, 6016914204, 6028316750), \
    https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6031553531, \
    and https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6032172066."

register_result "dict-wordram-sublinear-redundancy" where
  title := "Sublinear-redundancy and combined Word-RAM lower bounds for dynamic succinct \
    dictionaries"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.2 and Theorem 6.1 (combined with Theorem 1.1; Section 1 footnote 1 \
        Word-RAM transfer)",
      locator := "arXiv:2306.02253v3, Section 1, pp. 1–2 and footnote 1 (PDF pp. 2–3); \
        Section 6, pp. 25–26 (PDF pp. 26–27); Section 7, pp. 26–27 (PDF pp. 27–28)" }
  ]
  theorems := [
    expectedFlatTime_ge_of_sublinear_redundancy,
    expectedFlatTime_ge_iterLogStar_add_log_div,
    expectedTotalCost_ge_of_sublinear_redundancy,
    expectedTotalCost_ge_iterLogStar_add_log_div
  ]
  scope := "Contrapositive Word-RAM transfer (via OfWordRAM, unconditional with no cryptographic \
    or oracle assumptions) of dict-cell-probe-sublinear-redundancy over any Word-RAM basis B. \
    For every fixed α > 0, c_w ≥ 0, and r_max : ℕ (plus c_R ≥ 0 for the combined bounds), a \
    uniform constant c > 0 is chosen before all varying parameters and implementations: under \
    2 ≤ n, 4 * n ≤ U, n ^ (1 + α) ≤ U, 1 ≤ V, w ≤ c_w * (log₂ U + log₂ V), and \
    persCount input ≤ r_max (resp. persistentRegCount P ≤ r_max), the allowed redundancy R is \
    given by (space + persCount input) * w ≤ benchmarkBits U V n + R for expectedFlatTime_* \
    (resp. (C.space + persistentRegCount P) * w ≤ benchmarkBits U V n + R for \
    expectedTotalCost_*). The standalone sublinear variants assume R ≤ n and give ENNReal.ofReal \
    (c * n * log₂(n / max R 1)) on oblivious insertQueryDeleteDist (vanishing at R = n where \
    log₂(n / max n 1) = 0); the combined variants cover all R ≤ c_R * n and give ENNReal.ofReal \
    (c * n * (log* n + max 0 (log₂(n / max R 1)))). Via ExecFlatProgramOps.tighten_actualBodyTime, \
    expectedFlatTime_* directly lower-bound the exact intrinsic expected non-halt body-instruction \
    count flatExpectedBodyTime (with flatExpectedTime = flatExpectedBodyTime + ops.length, and \
    flatExpectedBodyTime ≤ T_ops for any certified budget T_ops), while expectedTotalCost_* \
    bound C.initPotential + E[totalCost C.charge] (CLRS2009 §17.3). Correctness/realization up to \
    horizon 4 * n + 1 (ExecFlatProgramOps or StateTransitionImpl) is an input hypothesis on the \
    same program or implementation whose cost is bounded (not proved by these endpoints); \
    CslibFrontierTests/DictLowerBoundWordRAM.lean proves those hypotheses for its concrete \
    Basis.standard two-slot fixture programs. Bounded-error Monte Carlo schemes and adaptive \
    sequence adversaries are not covered. Outside-fleet source checks: PR #5704 \
    (reviews 5911577643, 5911560173, 5911573135, 6016497849, 6016914204, 6028316750), \
    https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6031553531, \
    and https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6032172066."

register_result "dict-wordram-update-lower-bound" where
  title := "Update-only Word-RAM lower bounds for dynamic succinct dictionaries with large values"
  topic := "algorithms"
  sources := [
    { paper := LiLiangYuZhou2023,
      theorem := "Theorem 1.3(1)–(2) (Section 1 footnote 1 Word-RAM transfer)",
      locator := "arXiv:2306.02253v3, Section 1, p. 1 footnote 1 and p. 2 (PDF pp. 2–3); \
        Section 8, pp. 27–30 (PDF pp. 28–31)" }
  ]
  theorems := [
    expectedFlatTime_update_ge_iterLog,
    expectedFlatTime_update_ge_sublinear,
    expectedFlatTime_update_ge_iterLogStar_add_log_div,
    expectedTotalCost_update_ge_iterLog,
    expectedTotalCost_update_ge_sublinear,
    expectedTotalCost_update_ge_iterLogStar_add_log_div
  ]
  scope := "Contrapositive update-only Word-RAM transfer (via OfWordRAM, no query-time constraint, \
    unconditional, no cryptographic or oracle assumptions) of dict-cell-probe-update-lower-bound \
    over any Word-RAM basis B on oblivious insertDeleteDist (3 * n charged updates; correctness \
    horizon 3 * n + 1 witnesses decodeDict via one trailing query without charging that query). \
    For every fixed α_V > 0, c_w ≥ 0, and r_max : ℕ (plus c_R ≥ 0 for the iterated-log and \
    combined variants), a uniform constant c > 0 is chosen before all varying parameters and \
    implementations under 2 ≤ n, 3 * n ≤ U, 1 ≤ V, U ^ (2 + α_V) ≤ V * n ^ 2, \
    w ≤ c_w * (log₂ U + log₂ V), and persCount input ≤ r_max (resp. persistentRegCount P ≤ r_max). \
    The iterated-log variants assume 1 ≤ k ≤ Nat.logStar n and memory budget \
    (space + persCount input) * w ≤ benchmarkBits U V n + c_R * n * max (Nat.iterLog k n) 1 \
    (resp. (C.space + persistentRegCount P) * w ≤ ...) to give ENNReal.ofReal (c * n * k) \
    (specializing to Ω(n * log* n) at k = Nat.logStar n); the sublinear (R ≤ n, vanishing at \
    R = n) and combined (R ≤ c_R * n) variants define the allowed redundancy R via \
    (space + persCount input) * w ≤ benchmarkBits U V n + R (resp. \
    (C.space + persistentRegCount P) * w ≤ benchmarkBits U V n + R) to give \
    ENNReal.ofReal (c * n * log₂(n / max R 1)) and \
    ENNReal.ofReal (c * n * (log* n + max 0 (log₂(n / max R 1)))). Via \
    ExecFlatProgramOps.tighten_actualBodyTime, expectedFlatTime_update_* directly lower-bound the \
    exact intrinsic expected non-halt body-instruction count flatExpectedBodyTime (with \
    flatExpectedTime = flatExpectedBodyTime + ops.length, and flatExpectedBodyTime ≤ T_ops for \
    any certified budget T_ops), while expectedTotalCost_update_* bound \
    C.initPotential + E[totalCost C.charge] (CLRS2009 §17.3). Correctness/realization \
    (ExecFlatProgramOps or StateTransitionImpl) is an input hypothesis on the same program or \
    implementation whose running time or budget is bounded (not proved by these endpoints); \
    CslibFrontierTests/DictLowerBoundWordRAM.lean proves those hypotheses for its concrete \
    Basis.standard two-slot fixture programs. Bounded-error Monte Carlo schemes and adaptive \
    adversaries are not covered. Outside-fleet source checks: PR #5704 \
    (reviews 5911577643, 5911560173, 5911573135, 6016497849, 6016914204, 6028316750), \
    https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6031553531, \
    and https://github.com/cslib-community/cslib-frontier/pull/7973#pullrequestreview-6032172066."

end
