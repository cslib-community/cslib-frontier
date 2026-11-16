/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate


public import CslibFrontier.Computability.Probabilistic.Oracle.Time.Basic
public import CslibFrontier.Computability.Probabilistic.Internal.Oracle.Time

/-!
# Explicit-time intrinsically halting oracle realizations

`Cslib.Probability.ComputesOracleInTimeOn input output t program` strengthens `IsOraclePPTOn` by
giving an explicit step schedule `t : α → ℕ` and requiring that one finite-control fair-coin oracle
machine realizes the complete joint output and external-state law across all shared stateful
handlers AND has actually halted (`final.1.tapes.state = none`) on every supported execution at
step `t a`.

As in the closed case (`CslibFrontier.Computability.Probabilistic.Time`), actual halting makes step
monotonicity (`ComputesOracleInTimeOn.mono`) hold unconditionally without requiring the larger
schedule to be computable. Every `t a`-step execution makes at most `t a` external queries, each of
word length at most `t a` (`ComputesOracleInTimeOn.query_bounds`). Because cryptographic security
bounds often track step count `t` and query count `q` separately (`q ≤ t`), this module also
defines `ComputesOracleInTimeAndQueriesOn` and parameterized `ComputesOracleInTimeAndQueries`.

Together with the clean-phase normalization compiler of
`CslibFrontier.Computability.Probabilistic.Oracle.Normalization`, `IsOraclePPTOn` and `IsOraclePPT`
are equivalent to `ComputesOracleInTimeOn` and `ComputesOracleInTime` under polynomially bounded
step schedules (`isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn`,
`isOraclePPT_iff_exists_polyBounded_computesOracleInTime`).

## Main definitions

* `Cslib.Probability.ComputesOracleInTimeOn`: uniform halting oracle-machine realization within an
  explicit step schedule.
* `Cslib.Probability.ComputesOracleInTime`: parameterized halting oracle-machine realization on a
  unary security parameter and auxiliary input length.
* `Cslib.Probability.ComputesOracleInTimeAndQueriesOn`,
  `Cslib.Probability.ComputesOracleInTimeAndQueries`: joint explicit `(t, q)` time-and-query bounds.

## Main results

* `Cslib.Probability.ComputesOracleInTimeOn.mono`: unconditional step-schedule monotonicity.
* `Cslib.Probability.ComputesOracleInTimeOn.congr`,
  `Cslib.Probability.ComputesOracleInTimeOn.length_le`: joint-law congruence and supported output
  length bound `≤ t a`.
* `Cslib.Probability.ComputesOracleInTimeOn.query_bounds`, `.isQueryBounded`: external query-count
  and query-length bounds `≤ t a`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computesOracleInTimeOn`: plain deterministic
  computations lift with exact step bound `t`.
* `Cslib.Probability.ComputesInTimeOn.computesOracleInTimeOn`,
  `Cslib.Probability.ComputesOracleInTimeOn.computesInTimeOn`: exact step-preserving lifts between
  closed and channel-free oracle realizations.
* `Cslib.Probability.ComputesOracleInTimeOn.uniform_bool`, `.query_take_pair`, `.query_take`,
  `.bind_sample_left`, `.bind_sample_right`, `.preprocess`, `.map`: quantitative primitives and
  buffered compositions with explicit machine-independent step bounds.
* `Cslib.Probability.isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn`,
  `Cslib.Probability.isOraclePPT_iff_exists_polyBounded_computesOracleInTime`: equivalence with
  `IsOraclePPTOn` and `IsOraclePPT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapters 3, 7.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Sections 3.11,
  4.1.
-/
