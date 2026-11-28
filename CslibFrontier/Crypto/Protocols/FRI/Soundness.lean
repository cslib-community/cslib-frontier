/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.BinaryBCS
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.BinarySoundness
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SymbolEncoding

/-!
# Smooth & Binary FRI Round-by-Round Soundness, Summed IOP Soundness, and BCS ROM Composition

This module proves unconditional round-by-round soundness
(`Cslib.Crypto.Protocols.BCS.IOPRoundByRoundSoundness`) and query-round escape bounds for the
multi-round smooth `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` FRI IOP `Cslib.Crypto.Protocols.FRI.friSmoothIOP`
and its 2-to-1 specialization `Cslib.Crypto.Protocols.FRI.friIOP`
([BenSassonBentovHoreshRiabzev2018], [BenSassonCarmonIshaiKoppartySaraf2020]), together with
conditional per-round commit-phase escape, summed commit-phase and full interactive FRI soundness
(via `CslibFrontier.Crypto.Protocols.BCS.Interactive`, mirroring the commit-phase bad-event sum in
the proof of Lemma 8.2 in [BenSassonCarmonIshaiKoppartySaraf2020, Section 8.2.1, p. 42] and its
combination with the query phase in the proof of Theorem 8.3 on p. 40), and two-channel BCS
random-oracle composition steps parameterized by per-round curve/line proximity-gap or
escape-probability hypotheses ([BenSassonChiesaSpooner2016], [ChiesaYogev2024]).

## Overview of the smooth integer-weight round-by-round invariant

For smooth parameters `params : FRISmoothParams F` (per-round arities `l⁽ⁱ⁾ = params.arity i =
2 ^ params.stepLog i ≥ 2`, cumulative log-reduction `params.cumLog i`, active domain size
`params.domainSize i = 2 ^ (d - cumLog i)`), an input word `stmt : OracleTable params.d F`, and any
partial verifier transcript `pref : List (OracleTable params.d F × FRIChal F params.d params.q)`
of length `i ≤ m`:

* `friSmoothTargetWord params stmt pref i hi : Fin (params.domainSize i) → F` is the expected
  round-`i` word: `stmt` at `i = 0`, and the `l⁽ⁱ⁻¹⁾`-to-1 coset folding `foldWord` of the
  `(i - 1)`-th prover oracle `π_{i-1}` at `z_{i-1}` for `i ≥ 1`.
* `friSmoothPreWeight params stmt pref i hi : Fin (params.domainSize i) → ℕ` is the pre-filter
  integer fiber weight before the round-`i` oracle check `π_i(j) = friSmoothTargetWord ...`:
  identically `1` at `i = 0`, and for `i ≥ 1` the `pushWeight` fiberwise sum of the previous round's
  filtered weight `friSmoothOracleFilterWeight`. It satisfies `friSmoothPreWeight ... j ≤
  2 ^ params.cumLog i` and `∑ j, friSmoothPreWeight ... j ≤ 2 ^ d` unconditionally for arbitrary
  malicious oracles, while applying the round-`i` oracle check yields `friSmoothOracleFilterWeight`,
  counting the exact number of initial starting points above `j` satisfying
  `friSmoothPrefixPasses ... i` (`card_filter_friSmoothPrefixPasses_eq`).
* A transcript prefix of length `i ≤ m` is **doomed** (`friSmoothDoomed params B stmt pref`) if
  every codeword `c ∈ params.rsCode i` has `friSmoothPreWeight`-weighted agreement at most `B` with
  `friSmoothTargetWord`. A complete transcript of length `m + 1` is doomed if at least one of the
  `q` queried starting points fails `friSmoothTranscriptSingleAccepts`.

All binary 2-to-1 `FRIParams` soundness theorems are proved as short corollaries of the smooth
theorems via `FRIParams.toSmooth`, `friIOP_eq_friSmoothIOP`, `friDoomed_iff_friSmoothDoomed`, and
`weightedLineEscapePerRound_iff_weightedCurveEscapePerRound`, with zero duplicated proofs and
unchanged public binary signatures.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friSmoothTargetWord`,
  `Cslib.Crypto.Protocols.FRI.friSmoothPreWeight`,
  `Cslib.Crypto.Protocols.FRI.friSmoothOracleFilterWeight`,
  `Cslib.Crypto.Protocols.FRI.friSmoothNextWeight`,
  `Cslib.Crypto.Protocols.FRI.friSmoothPrefixPasses`,
  `Cslib.Crypto.Protocols.FRI.friSmoothTranscriptSingleAccepts`,
  `Cslib.Crypto.Protocols.FRI.friSmoothFinalPasses`: smooth transcript state, pushed-forward fiber
  weights, and starting-point acceptance predicates.
* `Cslib.Crypto.Protocols.FRI.friSmoothCommitDoomed`,
  `Cslib.Crypto.Protocols.FRI.friSmoothDoomed`, `Cslib.Crypto.Protocols.FRI.friSmoothGoodStep`,
  `Cslib.Crypto.Protocols.FRI.friSmoothCommitGame`,
  `Cslib.Crypto.Protocols.FRI.friSmoothRoundEscape`, `Cslib.Crypto.Protocols.FRI.friSmoothSumError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothSupRBRError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothRBRError`: smooth round-by-round predicates, commit game, and
  summed / uniform escape error expressions.
* `Cslib.Crypto.Protocols.FRI.WeightedCurveGapPerRound`,
  `Cslib.Crypto.Protocols.FRI.WeightedCurveGapBound`,
  `Cslib.Crypto.Protocols.FRI.WeightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.UniqueCurveGapHypothesis`: polymorphic per-round degree-`(l⁽ⁱ⁾ - 1)`
  curve proximity-gap and escape-probability contracts (specializing to `WeightedLineGapPerRound`,
  `WeightedLineGapBound`, `WeightedLineEscapePerRound`, and `UniqueLineGapHypothesis` at
  `l⁽ⁱ⁾ = 2`).
* `Cslib.Crypto.Protocols.FRI.encZMod`, `Cslib.Crypto.Protocols.FRI.decZMod`: unsigned
  little-endian binary symbol codec for `ZMod p`.

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothIOP_rbrSound` & `Cslib.Crypto.Protocols.FRI.friIOP_rbrSound`:
  unconditional round-by-round soundness invariants for smooth and binary FRI.
* `Cslib.Crypto.Protocols.FRI.card_filter_friSmoothPrefixPasses_eq`,
  `Cslib.Crypto.Protocols.FRI.card_filter_friSmoothFinalPasses_le`,
  `Cslib.Crypto.Protocols.FRI.card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed`, &
  `Cslib.Crypto.Protocols.FRI.friSmoothQueryRound_escape_le`: unconditional starting-point counting
  and query-round escape bound `≤ (B / 2 ^ d) ^ q`.
* `Cslib.Crypto.Protocols.FRI.friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothCommitGame_le_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapPerRound_of_uniqueCurveGap`, &
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapBound_of_uniqueCurveGap`: conditional smooth commit,
  summed interactive IOP, and unique-decoding curve-upgrade steps (with binary counterparts
  `friCommitRound_escape_le_of_*`, `friCommitGame_le_of_*`, `friIOP_interactiveGame_le_of_*`,
  `weightedLineGapPerRound_of_uniqueLineGap`, and `weightedLineGapBound_of_uniqueLineGap` as
  corollaries).
* `Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_weightedCurveGap`,
  `FRI.friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_uniqueCurveGap`, and their binary
  counterparts `friBCS_romSoundness_bound_of_*`: conditional two-channel BCS ROM compositions.
* `Cslib.Crypto.Protocols.FRI.friDoomed_iff_friSmoothDoomed`,
  `Cslib.Crypto.Protocols.FRI.friGoodStep_iff_friSmoothGoodStep`,
  `Cslib.Crypto.Protocols.FRI.friCommitGame_eq_friSmoothCommitGame`, &
  `Cslib.Crypto.Protocols.FRI.weightedLineEscapePerRound_iff_weightedCurveEscapePerRound`: exact
  binary-to-smooth specialization bridges.
-/

