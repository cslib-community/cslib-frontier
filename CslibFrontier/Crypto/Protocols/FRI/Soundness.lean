/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Crypto.Protocols.BCS.Interactive
public import CslibFrontier.Crypto.Protocols.FRI.Protocol
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.PMF.UniformBound
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

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

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section SmoothParamHelpers

variable {F : Type} [Field F]

/-- Equivalence between `Fin (params.arity i * params.domainSize (i.val + 1))` and
`Fin (params.domainSize i.val)` for a smooth folding round `i : Fin params.m`. -/
private abbrev FRISmoothParams.fiberDomainEquiv (params : FRISmoothParams F) (i : Fin params.m) :
    Fin (params.arity i * params.domainSize (i.val + 1)) ≃ Fin (params.domainSize i.val) :=
  finCongr (params.domainSize_eq_arity_mul_succ i).symm

/-- Cumulative fiber-size product identity `2 ^ cumLog i * domainSize i = 2 ^ d` for `i ≤ m`. -/
theorem FRISmoothParams.two_pow_cumLog_mul_domainSize (params : FRISmoothParams F)
    {i : ℕ} (hi : i ≤ params.m) :
    2 ^ params.cumLog i * params.domainSize i = 2 ^ params.d := by
  have hle := params.cumLog_le_d hi
  simp only [FRISmoothParams.domainSize, ← pow_add]
  congr 1
  omega

/-- Cumulative dimension scaling identity `2 ^ cumLog i * dim i = dim 0` for `i ≤ m`. -/
theorem FRISmoothParams.two_pow_cumLog_mul_dim (params : FRISmoothParams F)
    {i : ℕ} (hi : i ≤ params.m) :
    2 ^ params.cumLog i * params.dim i = params.dim 0 := by
  have hle := params.cumLog_le_totalLog hi
  simp only [FRISmoothParams.dim, FRISmoothParams.cumLog, friCumLog_zero, Nat.sub_zero]
  have hexp : params.cumLog i + (params.totalLog - params.cumLog i) = params.totalLog := by omega
  calc 2 ^ params.cumLog i * (params.kFinal * 2 ^ (params.totalLog - params.cumLog i))
      = params.kFinal * (2 ^ params.cumLog i * 2 ^ (params.totalLog - params.cumLog i)) := by ring
    _ = params.kFinal * 2 ^ params.totalLog := by rw [← pow_add, hexp]

/-- Every round Reed–Solomon dimension `params.dim r` is at least `1`. -/
theorem FRISmoothParams.one_le_dim (params : FRISmoothParams F) (r : ℕ) : 1 ≤ params.dim r := by
  simp only [FRISmoothParams.dim]
  exact Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Each active round dimension fits inside its active coset size (`r ≤ m`). -/
theorem FRISmoothParams.dim_le_domainSize (params : FRISmoothParams F)
    {r : ℕ} (hr : r ≤ params.m) :
    params.dim r ≤ params.domainSize r := by
  have htot : params.totalLog ≤ params.d := params.htotal
  have hle : params.cumLog r ≤ params.totalLog := params.cumLog_le_totalLog hr
  have hsub : (params.d - params.totalLog) + (params.totalLog - params.cumLog r) =
      params.d - params.cumLog r := by omega
  calc params.dim r
      = params.kFinal * 2 ^ (params.totalLog - params.cumLog r) := rfl
    _ ≤ 2 ^ (params.d - params.totalLog) * 2 ^ (params.totalLog - params.cumLog r) :=
        Nat.mul_le_mul_right _ params.hkLe
    _ = params.domainSize r := by rw [FRISmoothParams.domainSize, ← pow_add, hsub]

/-- Transport the initial unique-decoding bound `2 * e + params.dim 0 ≤ 2 ^ params.d` to the
scaled round-`(i + 1)` unique-decoding bound
`2 * (e / 2 ^ cumLog (i + 1)) + params.dim (i + 1) ≤ params.domainSize (i + 1)`. -/
theorem FRISmoothParams.two_mul_div_add_dim_le (params : FRISmoothParams F) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) (i : Fin params.m) :
    2 * (e / 2 ^ params.cumLog (i.val + 1)) + params.dim (i.val + 1) ≤
      params.domainSize (i.val + 1) := by
  have hM_pos : 0 < 2 ^ params.cumLog (i.val + 1) := Nat.pow_pos (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hM_pos
  calc 2 ^ params.cumLog (i.val + 1) *
        (2 * (e / 2 ^ params.cumLog (i.val + 1)) + params.dim (i.val + 1))
      = 2 * (2 ^ params.cumLog (i.val + 1) * (e / 2 ^ params.cumLog (i.val + 1))) +
          2 ^ params.cumLog (i.val + 1) * params.dim (i.val + 1) := by ring
    _ ≤ 2 * e + params.dim 0 := by
        rw [params.two_pow_cumLog_mul_dim i.isLt]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_div_le e _)) _
    _ ≤ 2 ^ params.d := huniq
    _ = 2 ^ params.cumLog (i.val + 1) * params.domainSize (i.val + 1) :=
        (params.two_pow_cumLog_mul_domainSize i.isLt).symm

end SmoothParamHelpers

section SharedTranscriptAccessors

variable {F : Type} [Field F]

/-- Read the `k`-th committed prover oracle from a transcript prefix, defaulting to the zero table
if `k ≥ pref.length`. -/
@[expose] def prefOracle {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) : OracleTable d F :=
  match pref[k]? with
  | some (π, _) => π
  | none => fun _ => 0

/-- Read the `k`-th folding challenge scalar from a transcript prefix, defaulting to `0` if
`k ≥ pref.length`. -/
@[expose] def prefFoldScalar {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) : F :=
  match pref[k]? with
  | some (_, c) => c.foldScalar
  | none => 0

/-- Read the `k`-th round's `q` query starting indices from a transcript prefix, defaulting to `0`
if `k ≥ pref.length`. -/
@[expose] def prefQueryIdxs {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) :
    Fin q → Fin (2 ^ d) :=
  match pref[k]? with
  | some (_, c) => c.queryIdxs
  | none => fun _ => ⟨0, Nat.pow_pos (by omega)⟩

/-- Read the final round's `q` query starting indices from a transcript, defaulting to `0`. -/
abbrev prefFinalQueryIdxs (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    Fin params.q → Fin (2 ^ params.d) :=
  prefQueryIdxs pref params.m

theorem prefOracle_append_left {d q : ℕ}
    (pref extra : List (OracleTable d F × FRIChal F d q)) {k : ℕ} (hk : k < pref.length) :
    prefOracle (pref ++ extra) k = prefOracle pref k := by
  simp only [prefOracle, List.getElem?_append_left hk]

theorem prefOracle_append_self {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (π : OracleTable d F) (c : FRIChal F d q) :
    prefOracle (pref ++ [(π, c)]) pref.length = π := by
  simp only [prefOracle, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

theorem prefFoldScalar_append_left {d q : ℕ}
    (pref extra : List (OracleTable d F × FRIChal F d q)) {k : ℕ} (hk : k < pref.length) :
    prefFoldScalar (pref ++ extra) k = prefFoldScalar pref k := by
  simp only [prefFoldScalar, List.getElem?_append_left hk]

theorem prefFoldScalar_append_self {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (π : OracleTable d F) (c : FRIChal F d q) :
    prefFoldScalar (pref ++ [(π, c)]) pref.length = c.foldScalar := by
  simp only [prefFoldScalar, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

omit [Field F] in
private theorem prefQueryIdxs_append_self {m d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q))
    (hlen : pref.length = m) (π : OracleTable d F) (c : FRIChal F d q) :
    prefQueryIdxs (pref ++ [(π, c)]) m = c.queryIdxs := by
  simp only [prefQueryIdxs, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

theorem prefFinalQueryIdxs_append_self (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    prefFinalQueryIdxs params (pref ++ [(π, c)]) = c.queryIdxs :=
  prefQueryIdxs_append_self pref hlen π c

theorem prefOracle_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q)
    {k : ℕ} (hk : k < m + 1) :
    prefOracle (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) k = oracles ⟨k, hk⟩ := by
  simp only [prefOracle, List.getElem?_ofFn, hk, ↓reduceDIte]

theorem prefFoldScalar_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q)
    {k : ℕ} (hk : k < m + 1) :
    prefFoldScalar (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) k =
      (chals ⟨k, hk⟩).foldScalar := by
  simp only [prefFoldScalar, List.getElem?_ofFn, hk, ↓reduceDIte]

omit [Field F] in
private theorem prefQueryIdxs_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q) :
    prefQueryIdxs (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) m =
      (chals (Fin.last m)).queryIdxs := by
  simp only [prefQueryIdxs, List.getElem?_ofFn, Nat.lt_succ_self, ↓reduceDIte, Fin.last]

theorem prefFinalQueryIdxs_ofFn (params : FRIParams F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    prefFinalQueryIdxs params
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) =
      (chals (Fin.last params.m)).queryIdxs :=
  prefQueryIdxs_ofFn oracles chals

/-- Equivalence between `Fin (2 * 2 ^ (d - (j + 1)))` and `Fin (2 ^ (d - j))` for `j < d`. -/
@[expose] def reindexDoubleEquiv {d j : ℕ} (hj : j < d) :
    Fin (2 * 2 ^ (d - (j + 1))) ≃ Fin (2 ^ (d - j)) where
  toFun := reindexDouble hj
  invFun idx := ⟨idx.val, by
    have hsplit : 2 ^ (d - j) = 2 * 2 ^ (d - (j + 1)) := by
      have hsub : d - j = (d - (j + 1)) + 1 := by omega
      rw [hsub, pow_succ']
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SharedTranscriptAccessors

section SmoothTranscriptState

variable {F : Type} [Field F]

/-- Expected round-`i` word along a smooth transcript prefix `pref`: `stmt` at round `0`, and the
`l⁽ⁱ⁻¹⁾`-to-1 coset folding `foldWord` of `prefOracle pref (i - 1)` at `prefFoldScalar pref (i - 1)`
for round `i ≥ 1`. -/
@[expose] def friSmoothTargetWord (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (params.domainSize i) → F
  | 0, _ => restrictOracle (i := 0) stmt
  | i + 1, hi =>
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    foldWord (params.g ^ (2 ^ params.cumLog i)) (params.ω ^ (2 ^ params.cumLog i))
      (fun idx : Fin (params.arity ir * params.domainSize (i + 1)) =>
        restrictOracle (i := params.cumLog i) (prefOracle pref i)
          (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))
      (prefFoldScalar pref i)

/-- Pre-filter integer fiber weight `W̃_i : Fin (params.domainSize i) → ℕ` along a smooth transcript
prefix `pref`, prior to applying the round-`i` oracle consistency check `π_i = friSmoothTargetWord`:
identically `1` at `i = 0`, and for `i ≥ 1` the `pushWeight` fiberwise sum of the round-`(i - 1)`
filtered weight. -/
@[expose] def friSmoothPreWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (params.domainSize i) → ℕ
  | 0, _ => fun _ => 1
  | i + 1, hi =>
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    let prevTarget := friSmoothTargetWord params stmt pref i (Nat.le_of_succ_le hi)
    let prevWeight := friSmoothPreWeight params stmt pref i (Nat.le_of_succ_le hi)
    let prevOracle := restrictOracle (i := params.cumLog i) (prefOracle pref i)
    let filt : Fin (params.domainSize i) → ℕ :=
      fun y => if prevOracle y = prevTarget y then prevWeight y else 0
    pushWeight (a := params.arity ir)
      (fun idx => filt (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))

/-- Filtered smooth round-`i` weight for an explicit prover oracle `π`: retains `friSmoothPreWeight`
on coordinates where `π` agrees with `friSmoothTargetWord`, and zeroes all other coordinates. -/
@[expose] def friSmoothOracleFilterWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize i)) : ℕ :=
  if restrictOracle (i := params.cumLog i) π j = friSmoothTargetWord params stmt pref i hi j then
    friSmoothPreWeight params stmt pref i hi j
  else 0

/-- Pushed smooth round-`(i + 1)` weight induced by an explicit prover oracle `π` at round `i`
(independent of the round-`i` verifier challenge). -/
@[expose] def friSmoothNextWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    Fin (params.domainSize (i + 1)) → ℕ :=
  let ir : Fin params.m := ⟨i, hi⟩
  pushWeight (a := params.arity ir)
    (fun idx => friSmoothOracleFilterWeight params stmt pref i hi.le π
      (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))

private theorem friSmoothTargetWord_append (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friSmoothTargetWord params stmt (pref ++ extra) i hi =
      friSmoothTargetWord params stmt pref i hi := by
  cases i with
  | zero => rfl
  | succ k =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    simp only [friSmoothTargetWord, prefOracle_append_left pref extra hk,
      prefFoldScalar_append_left pref extra hk]

private theorem friSmoothPreWeight_append [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friSmoothPreWeight params stmt (pref ++ extra) i hi =
      friSmoothPreWeight params stmt pref i hi := by
  induction i with
  | zero => rfl
  | succ k ih =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    have htarget := friSmoothTargetWord_append params stmt pref extra (Nat.le_of_succ_le hi) hk.le
    have hweight := ih (Nat.le_of_succ_le hi) hk.le
    ext j
    simp only [friSmoothPreWeight, htarget, hweight, prefOracle_append_left pref extra hk]

private theorem friSmoothTargetWord_append_step (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friSmoothTargetWord params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      foldWord (params.g ^ (2 ^ params.cumLog pref.length))
        (params.ω ^ (2 ^ params.cumLog pref.length))
        (fun idx : Fin (params.arity ⟨pref.length, hpm⟩ * params.domainSize (pref.length + 1)) =>
          restrictOracle (i := params.cumLog pref.length) π
            (params.fiberDomainEquiv ⟨pref.length, hpm⟩ idx))
        c.foldScalar := by
  simp only [friSmoothTargetWord, prefOracle_append_self, prefFoldScalar_append_self]

private theorem friSmoothPreWeight_append_step [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friSmoothPreWeight params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      friSmoothNextWeight params stmt pref pref.length hpm π := by
  ext j
  have htarget := friSmoothTargetWord_append params stmt pref [(π, c)] hpm.le le_rfl
  have hweight := friSmoothPreWeight_append params stmt pref [(π, c)] hpm.le le_rfl
  simp only [friSmoothPreWeight, friSmoothNextWeight, friSmoothOracleFilterWeight, htarget,
    hweight, prefOracle_append_self]

private theorem friSmoothOracleFilterWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize i)) :
    friSmoothOracleFilterWeight params stmt pref i hi π j ≤
      friSmoothPreWeight params stmt pref i hi j := by
  unfold friSmoothOracleFilterWeight
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Pointwise bound on smooth pre-filter weights: `friSmoothPreWeight ... i j ≤ 2 ^ cumLog i`. -/
theorem friSmoothPreWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (params.domainSize i)),
      friSmoothPreWeight params stmt pref i hi j ≤ 2 ^ params.cumLog i
  | 0, _, _ => by simp [friSmoothPreWeight, FRISmoothParams.cumLog]
  | i + 1, hi, j => by
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    have ih := friSmoothPreWeight_le params stmt pref i (Nat.le_of_succ_le hi)
    have hpow : params.arity ir * 2 ^ params.cumLog i = 2 ^ params.cumLog (i + 1) := by
      rw [params.cumLog_succ ir, FRISmoothParams.arity, ← pow_add, add_comm]
    simp only [friSmoothPreWeight]
    refine (pushWeight_le (M := 2 ^ params.cumLog i) (fun idx => ?_) j).trans_eq hpow
    split_ifs
    · exact ih _
    · exact Nat.zero_le _

/-- Pointwise bound on smooth pushed weights: `friSmoothNextWeight ... i π j ≤ 2 ^ cumLog (i + 1)`.
-/
theorem friSmoothNextWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize (i + 1))) :
    friSmoothNextWeight params stmt pref i hi π j ≤ 2 ^ params.cumLog (i + 1) := by
  let ir : Fin params.m := ⟨i, hi⟩
  have hpow : params.arity ir * 2 ^ params.cumLog i = 2 ^ params.cumLog (i + 1) := by
    rw [params.cumLog_succ ir, FRISmoothParams.arity, ← pow_add, add_comm]
  simp only [friSmoothNextWeight]
  refine (pushWeight_le (M := 2 ^ params.cumLog i) (fun idx => ?_) j).trans_eq hpow
  exact (friSmoothOracleFilterWeight_le params stmt pref i hi.le π _).trans
    (friSmoothPreWeight_le params stmt pref i hi.le _)

/-- Total-weight bound on smooth pre-filter weights: `∑ j, friSmoothPreWeight ... i j ≤ 2 ^ d`. -/
theorem sum_friSmoothPreWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m),
      (∑ j : Fin (params.domainSize i), friSmoothPreWeight params stmt pref i hi j) ≤
        2 ^ params.d
  | 0, _ => by
    simp only [friSmoothPreWeight, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_univ, Fintype.card_fin, FRISmoothParams.domainSize, FRISmoothParams.cumLog,
      friCumLog_zero, Nat.sub_zero]
  | i + 1, hi => by
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    have ih := sum_friSmoothPreWeight_le params stmt pref i (Nat.le_of_succ_le hi)
    let filt : Fin (params.domainSize i) → ℕ :=
      fun y =>
        if restrictOracle (i := params.cumLog i) (prefOracle pref i) y =
            friSmoothTargetWord params stmt pref i (Nat.le_of_succ_le hi) y then
          friSmoothPreWeight params stmt pref i (Nat.le_of_succ_le hi) y
        else 0
    have hstep :
        (∑ j : Fin (params.domainSize (i + 1)), friSmoothPreWeight params stmt pref (i + 1) hi j) =
          ∑ idx : Fin (params.arity ir * params.domainSize (i + 1)),
            filt (params.fiberDomainEquiv ir idx) := by
      simp only [friSmoothPreWeight]
      exact sum_pushWeight (a := params.arity ir) (N := params.domainSize (i + 1))
        (fun idx => filt (params.fiberDomainEquiv ir idx))
    calc ∑ j : Fin (params.domainSize (i + 1)), friSmoothPreWeight params stmt pref (i + 1) hi j
        = ∑ idx : Fin (params.arity ir * params.domainSize (i + 1)),
            filt (params.fiberDomainEquiv ir idx) := hstep
      _ = ∑ y : Fin (params.domainSize i), filt y :=
            Equiv.sum_comp (params.fiberDomainEquiv ir) filt
      _ ≤ ∑ y : Fin (params.domainSize i),
            friSmoothPreWeight params stmt pref i (Nat.le_of_succ_le hi) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          dsimp only [filt]
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
      _ ≤ 2 ^ params.d := ih

/-- Total-weight bound on smooth pushed weights: `∑ j, friSmoothNextWeight ... i π j ≤ 2 ^ d`. -/
theorem sum_friSmoothNextWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (params.domainSize (i + 1)), friSmoothNextWeight params stmt pref i hi π j) ≤
      2 ^ params.d := by
  let ir : Fin params.m := ⟨i, hi⟩
  have hstep :
      (∑ j : Fin (params.domainSize (i + 1)), friSmoothNextWeight params stmt pref i hi π j) =
        ∑ idx : Fin (params.arity ir * params.domainSize (i + 1)),
          friSmoothOracleFilterWeight params stmt pref i hi.le π
            (params.fiberDomainEquiv ir idx) := by
    simp only [friSmoothNextWeight]
    exact sum_pushWeight (a := params.arity ir) (N := params.domainSize (i + 1))
      (fun idx => friSmoothOracleFilterWeight params stmt pref i hi.le π
        (params.fiberDomainEquiv ir idx))
  calc ∑ j : Fin (params.domainSize (i + 1)), friSmoothNextWeight params stmt pref i hi π j
      = ∑ idx : Fin (params.arity ir * params.domainSize (i + 1)),
          friSmoothOracleFilterWeight params stmt pref i hi.le π
            (params.fiberDomainEquiv ir idx) := hstep
    _ = ∑ y : Fin (params.domainSize i),
          friSmoothOracleFilterWeight params stmt pref i hi.le π y :=
          Equiv.sum_comp (params.fiberDomainEquiv ir) _
    _ ≤ ∑ y : Fin (params.domainSize i), friSmoothPreWeight params stmt pref i hi.le y :=
          Finset.sum_le_sum fun y _ => friSmoothOracleFilterWeight_le params stmt pref i hi.le π y
    _ ≤ 2 ^ params.d := sum_friSmoothPreWeight_le params stmt pref i hi.le

/-- Monotonicity of filtered weighted agreement for smooth FRI: replacing `friSmoothTargetWord` and
`friSmoothPreWeight` by an arbitrary prover oracle `π` and its filtered weight
`friSmoothOracleFilterWeight` cannot increase weighted agreement with any word `c`. -/
theorem sum_agree_friSmoothOracleFilterWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (c : Fin (params.domainSize i) → F) :
    (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := params.cumLog i) π j = c j),
      friSmoothOracleFilterWeight params stmt pref i hi π j) ≤
    ∑ j ∈ Finset.univ.filter (fun j => friSmoothTargetWord params stmt pref i hi j = c j),
      friSmoothPreWeight params stmt pref i hi j := by
  have hzero :
      (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := params.cumLog i) π j = c j),
        friSmoothOracleFilterWeight params stmt pref i hi π j) =
      ∑ j ∈ Finset.univ.filter (fun j =>
          restrictOracle (i := params.cumLog i) π j = c j ∧
            restrictOracle (i := params.cumLog i) π j =
              friSmoothTargetWord params stmt pref i hi j),
        friSmoothPreWeight params stmt pref i hi j := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun j => restrictOracle (i := params.cumLog i) π j = c j)
      (fun j => restrictOracle (i := params.cumLog i) π j =
        friSmoothTargetWord params stmt pref i hi j)]
    have hrest :
        (∑ j ∈ (Finset.univ.filter fun j => restrictOracle (i := params.cumLog i) π j = c j).filter
            (fun j => ¬ restrictOracle (i := params.cumLog i) π j =
              friSmoothTargetWord params stmt pref i hi j),
          friSmoothOracleFilterWeight params stmt pref i hi π j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne := (Finset.mem_filter.mp hj).2
      simp only [friSmoothOracleFilterWeight, hne, ↓reduceIte]
    rw [hrest, add_zero, Finset.filter_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    have heq := (Finset.mem_filter.mp hj).2.2
    simp only [friSmoothOracleFilterWeight, heq, ↓reduceIte]
  rw [hzero]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  have hmem := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.2.symm.trans hmem.1⟩

end SmoothTranscriptState

section SmoothStartingPointCounting

variable {F : Type} [Field F]

/-- Smooth prefix acceptance predicate for a starting index `s : Fin (2 ^ d)` through folding
rounds `0, ..., i - 1` along a transcript `pref`: round-0 binding `π_0(s) = stmt(s)` plus
`l⁽ᵏ⁾`-to-1 fiber folding checks for every `k < i`. -/
@[expose] def friSmoothPrefixPasses (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) : Prop :=
  prefOracle pref 0 s = stmt s ∧
  ∀ k : Fin params.m, k.val < i →
    foldFiber (params.g ^ (2 ^ params.cumLog k.val)) (params.ω ^ (2 ^ params.cumLog k.val))
      (fun t : Fin (params.arity k) => prefOracle pref k.val (friSmoothFiberIdx params k s t))
      (friSmoothFoldedFin params k s) (prefFoldScalar pref k.val) =
    prefOracle pref (k.val + 1) (friSmoothFoldedIdx params k s)

/-- Full single-query acceptance predicate evaluated on a smooth transcript list `pref` at starting
index `s : Fin (2 ^ d)`. -/
@[expose] def friSmoothTranscriptSingleAccepts (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) : Prop :=
  friSmoothPrefixPasses params stmt pref params.m s ∧
    prefOracle pref params.m (friSmoothFinalIdx params s) =
      friSmoothFinalCodeword params (prefOracle pref params.m) (friSmoothFinalFin params s)

/-- Smooth final-round acceptance predicate for a length-`m` prefix `pref` and final oracle `πFinal`
(manifestly independent of the final round's verifier challenge `c`). -/
@[expose] def friSmoothFinalPasses (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  (if params.m = 0 then πFinal s else prefOracle pref 0 s) = stmt s ∧
  (∀ k : Fin params.m,
    foldFiber (params.g ^ (2 ^ params.cumLog k.val)) (params.ω ^ (2 ^ params.cumLog k.val))
      (fun t : Fin (params.arity k) => prefOracle pref k.val (friSmoothFiberIdx params k s t))
      (friSmoothFoldedFin params k s) (prefFoldScalar pref k.val) =
    (if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1))
      (friSmoothFoldedIdx params k s)) ∧
  πFinal (friSmoothFinalIdx params s) =
    friSmoothFinalCodeword params πFinal (friSmoothFinalFin params s)

instance instDecidableFriSmoothPrefixPasses [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    Decidable (friSmoothPrefixPasses params stmt pref i s) := by
  unfold friSmoothPrefixPasses
  infer_instance

instance instDecidableFriSmoothFinalPasses [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    Decidable (friSmoothFinalPasses params stmt pref πFinal s) := by
  unfold friSmoothFinalPasses
  infer_instance

private theorem friSmoothTranscriptSingleAccepts_append_iff (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F)
    (c : FRIChal F params.d params.q) (s : Fin (2 ^ params.d)) :
    friSmoothTranscriptSingleAccepts params stmt (pref ++ [(πFinal, c)]) s ↔
      friSmoothFinalPasses params stmt pref πFinal s := by
  have h0 : prefOracle (pref ++ [(πFinal, c)]) 0 s =
      if params.m = 0 then πFinal s else prefOracle pref 0 s := by
    by_cases hm : params.m = 0
    · have hp0 : pref.length = 0 := hlen.trans hm
      simp only [hm, ↓reduceIte, ← hp0, prefOracle_append_self]
    · have hpos : 0 < pref.length := by omega
      simp only [hm, ↓reduceIte, prefOracle_append_left pref [(πFinal, c)] hpos]
  have hm_eq : prefOracle (pref ++ [(πFinal, c)]) params.m = πFinal := by
    rw [← hlen, prefOracle_append_self]
  simp only [friSmoothTranscriptSingleAccepts, friSmoothPrefixPasses, friSmoothFinalPasses, h0,
    hm_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  have hnext : ∀ k : Fin params.m,
      prefOracle (pref ++ [(πFinal, c)]) (k.val + 1) =
        if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1) := by
    intro k
    by_cases hlast : k.val + 1 = params.m
    · simp only [hlast, ↓reduceIte, hm_eq]
    · have hlt : k.val + 1 < pref.length := by omega
      simp only [hlast, ↓reduceIte, prefOracle_append_left pref [(πFinal, c)] hlt]
  constructor
  · intro h k
    have hk_lt : k.val < pref.length := by omega
    simpa only [prefOracle_append_left pref [(πFinal, c)] hk_lt,
      prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hnext k] using h k k.isLt
  · intro h k _
    have hk_lt : k.val < pref.length := by omega
    simpa only [prefOracle_append_left pref [(πFinal, c)] hk_lt,
      prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hnext k] using h k

private theorem friSmoothTranscriptSingleAccepts_ofFn_iff (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) :
    friSmoothTranscriptSingleAccepts params stmt
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) s ↔
      friSmoothSingleAccepts params stmt chals oracles s := by
  simp only [friSmoothTranscriptSingleAccepts, friSmoothPrefixPasses, friSmoothSingleAccepts,
    prefOracle_ofFn oracles chals (Nat.zero_lt_succ params.m),
    prefOracle_ofFn oracles chals (Nat.lt_succ_self params.m), and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro h k
    have hk1 : k.val < params.m + 1 := Nat.lt_succ_of_lt k.isLt
    have hk2 : k.val + 1 < params.m + 1 := Nat.succ_lt_succ k.isLt
    have hcs : (⟨k.val, hk1⟩ : Fin (params.m + 1)) = k.castSucc := rfl
    have hsc : (⟨k.val + 1, hk2⟩ : Fin (params.m + 1)) = k.succ := rfl
    simpa only [prefOracle_ofFn oracles chals hk1, prefFoldScalar_ofFn oracles chals hk1,
      prefOracle_ofFn oracles chals hk2, hcs, hsc] using h k k.isLt
  · intro h k _
    have hk1 : k.val < params.m + 1 := Nat.lt_succ_of_lt k.isLt
    have hk2 : k.val + 1 < params.m + 1 := Nat.succ_lt_succ k.isLt
    have hcs : (⟨k.val, hk1⟩ : Fin (params.m + 1)) = k.castSucc := rfl
    have hsc : (⟨k.val + 1, hk2⟩ : Fin (params.m + 1)) = k.succ := rfl
    simpa only [prefOracle_ofFn oracles chals hk1, prefFoldScalar_ofFn oracles chals hk1,
      prefOracle_ofFn oracles chals hk2, hcs, hsc] using h k

/-- Exact `a`-way mod-splitting helper: for `0 < a` and `j < N`, `s % N = j` splits disjointly into
`∃ t : Fin a, s % (a * N) = j + t.val * N`. -/
private theorem mod_eq_iff_exists_fiberIdx {a N s j : ℕ} (ha : 0 < a) (hj : j < N) :
    s % N = j ↔ ∃ t : Fin a, s % (a * N) = j + t.val * N := by
  have hN : 0 < N := by omega
  have hmod_mod : (s % (a * N)) % N = s % N := Nat.mod_mul_left_mod s a N
  constructor
  · intro h
    have hq_lt : (s % (a * N)) / N < a :=
      (Nat.div_lt_iff_lt_mul hN).mpr (Nat.mod_lt s (Nat.mul_pos ha hN))
    refine ⟨⟨(s % (a * N)) / N, hq_lt⟩, ?_⟩
    have hdecomp := Nat.div_add_mod (s % (a * N)) N
    rw [hmod_mod, h] at hdecomp
    linarith
  · rintro ⟨t, ht⟩
    rw [← hmod_mod, ht, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **Exact smooth starting-point counting identity**: for every round `i ≤ m` and active-domain
coordinate `j : Fin (params.domainSize i)`, the filtered weight
`friSmoothOracleFilterWeight ... i (prefOracle pref i) j` equals the exact number of initial
positions `s : Fin (2 ^ d)` with `s % params.domainSize i = j` that satisfy
`friSmoothPrefixPasses ... i s`. -/
theorem card_filter_friSmoothPrefixPasses_eq [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (params.domainSize i)),
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % params.domainSize i = j.val ∧ friSmoothPrefixPasses params stmt pref i s).card =
      friSmoothOracleFilterWeight params stmt pref i hi (prefOracle pref i) j := by
  intro i
  induction i with
  | zero =>
    intro hi j
    have hdom0 : params.domainSize 0 = 2 ^ params.d := by
      simp [FRISmoothParams.domainSize, FRISmoothParams.cumLog]
    let j₀ : Fin (2 ^ params.d) := ⟨j.val, hdom0 ▸ j.isLt⟩
    have hpred :
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % params.domainSize 0 = j.val ∧ friSmoothPrefixPasses params stmt pref 0 s) =
        if prefOracle pref 0 j₀ = stmt j₀ then {j₀} else ∅ := by
      ext s
      simp only [hdom0, Finset.mem_filter, Finset.mem_univ, true_and, friSmoothPrefixPasses,
        Nat.not_lt_zero, false_implies, implies_true, and_true, Nat.mod_eq_of_lt s.isLt]
      by_cases hok : prefOracle pref 0 j₀ = stmt j₀
      · simp only [hok, ↓reduceIte, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, _⟩
          exact Fin.ext hs
        · rintro rfl
          exact ⟨rfl, hok⟩
      · simp only [hok, ↓reduceIte, Finset.notMem_empty, iff_false, not_and]
        intro hs
        have hsj : s = j₀ := Fin.ext hs
        subst hsj
        exact hok
    rw [hpred]
    simp only [friSmoothOracleFilterWeight, friSmoothTargetWord, friSmoothPreWeight, restrictOracle]
    by_cases hok : prefOracle pref 0 j₀ = stmt j₀ <;> simp [hok, j₀]
  | succ k ih =>
    intro hi j
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    let kr : Fin params.m := ⟨k, hkm⟩
    let N : ℕ := params.domainSize (k + 1)
    let a : ℕ := params.arity kr
    have ha_pos : 0 < a := lt_of_lt_of_le (by omega) (params.two_le_arity kr)
    have hN_pos : 0 < N := Nat.pow_pos (by omega)
    have hsplit : params.domainSize k = a * N := params.domainSize_eq_arity_mul_succ kr
    have hstep_eq : ∀ s : Fin (2 ^ params.d), s.val % N = j.val →
        (friSmoothPrefixPasses params stmt pref (k + 1) s ↔
          friSmoothPrefixPasses params stmt pref k s ∧
            restrictOracle (i := params.cumLog (k + 1)) (prefOracle pref (k + 1)) j =
              friSmoothTargetWord params stmt pref (k + 1) hi j) := by
      intro s hs
      have hfin : friSmoothFoldedFin params kr s = j := Fin.ext hs
      have hidx : friSmoothFoldedIdx params kr s =
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ :=
        Fin.ext hs
      have hfib : ∀ t : Fin a,
          friSmoothFiberIdx params kr s t =
            ⟨(params.fiberDomainEquiv kr (fiberIdx j t)).val,
              lt_of_lt_of_le (params.fiberDomainEquiv kr (fiberIdx j t)).isLt
                (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ := by
        intro t
        apply Fin.ext
        simpa only [friSmoothFiberIdx, FRISmoothParams.fiberDomainEquiv, finCongr_apply,
          Fin.val_cast, fiberIdx, FRISmoothParams.domainSize, N] using congrArg (· + t.val * N) hs
      have hfold_eq :
          foldFiber (params.g ^ (2 ^ params.cumLog k)) (params.ω ^ (2 ^ params.cumLog k))
            (fun t : Fin a => prefOracle pref k (friSmoothFiberIdx params kr s t))
            (friSmoothFoldedFin params kr s) (prefFoldScalar pref k) =
          friSmoothTargetWord params stmt pref (k + 1) hi j := by
        rw [hfin]
        simp only [hfib, friSmoothTargetWord, foldWord_apply_eq_foldFiber]
        rfl
      have hrhs_eq :
          prefOracle pref (k + 1) (friSmoothFoldedIdx params kr s) =
            restrictOracle (i := params.cumLog (k + 1)) (prefOracle pref (k + 1)) j := by
        rw [hidx]
        rfl
      simp only [friSmoothPrefixPasses]
      constructor
      · rintro ⟨hbind, hall⟩
        refine ⟨⟨hbind, fun r hr => hall r (Nat.lt_succ_of_lt hr)⟩, ?_⟩
        have hlast := hall kr (Nat.lt_succ_self k)
        rw [hfold_eq, hrhs_eq] at hlast
        exact hlast.symm
      · rintro ⟨⟨hbind, hall⟩, hcur⟩
        refine ⟨hbind, fun r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
        · exact hall r hlt
        · have hr_eq : r = kr := Fin.ext heq
          subst hr_eq
          rw [hfold_eq, hrhs_eq]
          exact hcur.symm
    have hpre_split :
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % N = j.val ∧ friSmoothPrefixPasses params stmt pref k s).card =
        friSmoothPreWeight params stmt pref (k + 1) hi j := by
      let S : Fin a → Finset (Fin (2 ^ params.d)) := fun t =>
        Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % params.domainSize k = (params.fiberDomainEquiv kr (fiberIdx j t)).val ∧
            friSmoothPrefixPasses params stmt pref k s
      have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin a)) S := by
        intro t₁ _ t₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro s hs₁ hs₂
        have h1 := (Finset.mem_filter.mp hs₁).2.1
        have h2 := (Finset.mem_filter.mp hs₂).2.1
        have heq_val : j.val + t₁.val * N = j.val + t₂.val * N := h1.symm.trans h2
        have hmul : t₁.val * N = t₂.val * N := Nat.add_left_cancel heq_val
        exact hne (Fin.ext (Nat.eq_of_mul_eq_mul_right hN_pos hmul))
      have hunion :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friSmoothPrefixPasses params stmt pref k s) =
          Finset.univ.biUnion S := by
        ext s
        simp only [S, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, hsplit,
          FRISmoothParams.fiberDomainEquiv, finCongr_apply, Fin.val_cast, fiberIdx]
        rw [mod_eq_iff_exists_fiberIdx ha_pos j.isLt, exists_and_right]
      rw [hunion, Finset.card_biUnion hdisj]
      refine Finset.sum_congr rfl fun t _ => ?_
      exact ih hkm.le (params.fiberDomainEquiv kr (fiberIdx j t))
    by_cases hmatch :
        restrictOracle (i := params.cumLog (k + 1)) (prefOracle pref (k + 1)) j =
          friSmoothTargetWord params stmt pref (k + 1) hi j
    · have hfilt_eq :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friSmoothPrefixPasses params stmt pref (k + 1) s) =
          Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friSmoothPrefixPasses params stmt pref k s := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hs, hp⟩
          exact ⟨hs, ((hstep_eq s hs).mp hp).1⟩
        · rintro ⟨hs, hp⟩
          exact ⟨hs, (hstep_eq s hs).mpr ⟨hp, hmatch⟩⟩
      rw [hfilt_eq, hpre_split]
      simp only [friSmoothOracleFilterWeight, hmatch, ↓reduceIte]
    · have hempty :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friSmoothPrefixPasses params stmt pref (k + 1) s) = ∅ := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro hs hp
        exact hmatch ((hstep_eq s hs).mp hp).2
      rw [hempty, Finset.card_empty]
      simp only [friSmoothOracleFilterWeight, hmatch, ↓reduceIte]

/-- **Smooth final query-acceptance counting bound**: for a length-`m` prefix `pref` and any final
oracle `πFinal`, the number of starting indices `s : Fin (2 ^ d)` satisfying `friSmoothFinalPasses`
is at most the pre-filter weighted agreement of `friSmoothTargetWord ... m` with
`friSmoothFinalCodeword params πFinal`. -/
theorem card_filter_friSmoothFinalPasses_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      friSmoothFinalPasses params stmt pref πFinal s).card ≤
    ∑ j ∈ Finset.univ.filter (fun j =>
      friSmoothTargetWord params stmt pref params.m le_rfl j =
        friSmoothFinalCodeword params πFinal j),
      friSmoothPreWeight params stmt pref params.m le_rfl j := by
  let c₀ : FRIChal F params.d params.q := ⟨0, fun _ => ⟨0, Nat.pow_pos (by omega)⟩⟩
  let pref' := pref ++ [(πFinal, c₀)]
  let S := Finset.univ.filter fun s : Fin (2 ^ params.d) =>
    friSmoothFinalPasses params stmt pref πFinal s
  have hcard_eq :
      S.card =
        ∑ j : Fin (params.domainSize params.m),
          (S.filter fun s => friSmoothFinalFin params s = j).card :=
    Finset.card_eq_sum_card_fiberwise fun s _ => Finset.mem_univ _
  have hfiber :
      ∀ j : Fin (params.domainSize params.m),
        (S.filter fun s => friSmoothFinalFin params s = j).card =
          if restrictOracle (i := params.cumLog params.m) πFinal j =
              friSmoothFinalCodeword params πFinal j then
            friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j
          else 0 := by
    intro j
    have hbase := card_filter_friSmoothPrefixPasses_eq params stmt pref' params.m le_rfl j
    have hπm : prefOracle (pref ++ [(πFinal, c₀)]) params.m = πFinal := by
      simp only [← hlen, prefOracle_append_self]
    have htarg : friSmoothTargetWord params stmt pref' params.m le_rfl =
        friSmoothTargetWord params stmt pref params.m le_rfl :=
      friSmoothTargetWord_append params stmt pref [(πFinal, c₀)] le_rfl (by omega)
    have hwt : friSmoothPreWeight params stmt pref' params.m le_rfl =
        friSmoothPreWeight params stmt pref params.m le_rfl :=
      friSmoothPreWeight_append params stmt pref [(πFinal, c₀)] le_rfl (by omega)
    have hfw :
        friSmoothOracleFilterWeight params stmt pref' params.m le_rfl
            (prefOracle pref' params.m) j =
          friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j := by
      simp only [friSmoothOracleFilterWeight, pref', hπm, htarg, hwt]
    rw [hfw] at hbase
    by_cases hok : restrictOracle (i := params.cumLog params.m) πFinal j =
        friSmoothFinalCodeword params πFinal j
    · simp only [hok, ↓reduceIte]
      rw [← hbase]
      refine congrArg Finset.card ?_
      ext s
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        ← friSmoothTranscriptSingleAccepts_append_iff params stmt pref hlen πFinal c₀ s,
        friSmoothTranscriptSingleAccepts]
      constructor
      · rintro ⟨⟨hpref, _⟩, hfin⟩
        exact ⟨congrArg (Fin.val (n := params.domainSize params.m)) hfin, hpref⟩
      · rintro ⟨hmod, hpref⟩
        have hfin : friSmoothFinalFin params s = j := Fin.ext hmod
        refine ⟨⟨hpref, ?_⟩, hfin⟩
        have hidx : friSmoothFinalIdx params s =
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ :=
          Fin.ext hmod
        rw [hfin, hidx, hπm]
        exact hok
    · simp only [hok, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have hmem := Finset.mem_filter.mp hs
      have hpass := (Finset.mem_filter.mp hmem.1).2
      have hfin := hmem.2
      have hidx : friSmoothFinalIdx params s =
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ :=
        Fin.ext (congrArg (Fin.val (n := params.domainSize params.m)) hfin)
      have heq := hpass.2.2
      rw [hfin, hidx] at heq
      exact hok heq
  rw [hcard_eq]
  calc ∑ j : Fin (params.domainSize params.m),
          (S.filter fun s => friSmoothFinalFin params s = j).card
      = ∑ j : Fin (params.domainSize params.m),
          (if restrictOracle (i := params.cumLog params.m) πFinal j =
              friSmoothFinalCodeword params πFinal j then
            friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j
          else 0) := Finset.sum_congr rfl fun j _ => hfiber j
    _ = ∑ j ∈ Finset.univ.filter (fun j =>
          restrictOracle (i := params.cumLog params.m) πFinal j =
            friSmoothFinalCodeword params πFinal j),
          friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j := by
        rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j =>
          friSmoothTargetWord params stmt pref params.m le_rfl j =
            friSmoothFinalCodeword params πFinal j),
          friSmoothPreWeight params stmt pref params.m le_rfl j :=
        sum_agree_friSmoothOracleFilterWeight_le params stmt pref params.m le_rfl πFinal
          (friSmoothFinalCodeword params πFinal)

end SmoothStartingPointCounting

section SmoothRoundByRoundSoundness

variable {F : Type} [Field F]

/-- Smooth commit-round doomed predicate at round `i ≤ m`: no codeword in `params.rsCode i` achieves
`friSmoothPreWeight`-weighted agreement `> B` with `friSmoothTargetWord`. -/
@[expose] def friSmoothCommitDoomed [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) : Prop :=
  ∀ c ∈ params.rsCode i,
    (∑ j ∈ Finset.univ.filter (fun j => friSmoothTargetWord params stmt pref i hi j = c j),
      friSmoothPreWeight params stmt pref i hi j) ≤ B

private theorem friSmoothCommitDoomed_congr_round [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i₁ i₂ : ℕ} (h : i₁ = i₂) (hi₁ : i₁ ≤ params.m) (hi₂ : i₂ ≤ params.m) :
    friSmoothCommitDoomed params B stmt pref i₁ hi₁ ↔
      friSmoothCommitDoomed params B stmt pref i₂ hi₂ := by
  subst h
  rfl

/-- **Smooth FRI round-by-round doomed-state predicate**:
* For prefixes of length `i ≤ m`, `friSmoothCommitDoomed` holds at round `i`.
* For complete transcripts of length `m + 1`, at least one of the `q` queried starting positions
  fails `friSmoothTranscriptSingleAccepts`.
* For unreachable lengths `> m + 1`, holds trivially (`True`). -/
@[expose] def friSmoothDoomed [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) : Prop :=
  if h : pref.length ≤ params.m then
    friSmoothCommitDoomed params B stmt pref pref.length h
  else if pref.length = params.m + 1 then
    ∃ a : Fin params.q,
      ¬ friSmoothTranscriptSingleAccepts params stmt pref (prefQueryIdxs pref params.m a)
  else
    True

/-- **Smooth FRI round-by-round good-step predicate**: for `pref.length ≤ m`, extending `pref` by
`(π, c)` preserves `friSmoothDoomed`; for unreachable lengths `> m`, holds trivially (`True`) so the
escape event `{c | ¬ friSmoothGoodStep ... c}` is empty. -/
@[expose] def friSmoothGoodStep [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) : Prop :=
  if pref.length ≤ params.m then
    friSmoothDoomed params B stmt (pref ++ [(π, c)])
  else
    True

/-- **Unconditional round-by-round soundness invariant for smooth `friSmoothIOP`**: for every
distance threshold `e : ℕ`, `friSmoothIOP params` satisfies `IOPRoundByRoundSoundness` with respect
to `params.proximityLang e`, `friSmoothDoomed params (2 ^ params.d - e - 1)`, and
`friSmoothGoodStep params (2 ^ params.d - e - 1)`. -/
theorem friSmoothIOP_rbrSound [DecidableEq F] (params : FRISmoothParams F) (e : ℕ) :
    IOPRoundByRoundSoundness (friSmoothIOP params) (params.proximityLang e)
      (friSmoothDoomed params (2 ^ params.d - e - 1))
      (friSmoothGoodStep params (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot := by
    simp only [friSmoothDoomed, List.length_nil, Nat.zero_le, ↓reduceDIte, friSmoothCommitDoomed,
      friSmoothTargetWord, friSmoothPreWeight, restrictOracle, FRISmoothParams.domainSize,
      friCumLog_zero, Nat.sub_zero, Fin.eta, Finset.sum_const, smul_eq_mul, mul_one]
    intro c hc
    have he_lt : e < hammingDist stmt c := by
      by_contra hle
      exact hnot ⟨c, hc, Nat.le_of_not_lt hle⟩
    let S_eq := Finset.univ.filter fun j : Fin (2 ^ params.d) => stmt j = c j
    have hpart : S_eq.card + hammingDist stmt c = 2 ^ params.d := by
      rw [hammingDist]
      simpa only [S_eq, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 ^ params.d))))
          (fun j => stmt j = c j)
    change S_eq.card ≤ 2 ^ params.d - e - 1
    omega
  step_doomed stmt pref π c _ hgood := by
    by_cases h : pref.length ≤ params.m
    · simpa only [friSmoothGoodStep, h, ↓reduceIte] using hgood
    · have hgt : ¬ (pref ++ [(π, c)]).length ≤ params.m := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hne : (pref ++ [(π, c)]).length ≠ params.m + 1 := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [friSmoothDoomed, hgt, ↓reduceDIte, hne, ↓reduceIte]
  reject_of_doomed stmt oracles chals hdoomed := by
    set pref := List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)
    have hlen : pref.length = params.m + 1 := by simp [pref]
    have hnotle : ¬ pref.length ≤ params.m := by omega
    simp only [friSmoothDoomed, hnotle, ↓reduceDIte] at hdoomed
    simp only [hlen, ↓reduceIte] at hdoomed
    rw [prefQueryIdxs_ofFn oracles chals] at hdoomed
    obtain ⟨a, ha⟩ := hdoomed
    cases hacc : iopVerify (friSmoothIOP params) stmt chals oracles
    · rfl
    · exfalso
      have hall := (iopVerify_friSmoothIOP_eq_true_iff params stmt chals oracles).mp hacc a
      exact ha ((friSmoothTranscriptSingleAccepts_ofFn_iff params stmt oracles chals _).mpr hall)

omit [Field F] in
/-- Projecting a uniform `FRIChal F d q` onto its folding scalar `foldScalar` yields the uniform
distribution on `F`. -/
theorem uniformOfFintype_friChal_map_foldScalar [Fintype F] [Nonempty F] (d q : ℕ) :
    (PMF.uniformOfFintype (FRIChal F d q)).map FRIChal.foldScalar =
      PMF.uniformOfFintype F := by
  have : Nonempty (Fin q → Fin (2 ^ d)) := ⟨fun _ => ⟨0, Nat.two_pow_pos d⟩⟩
  let e : FRIChal F d q ≃ F × (Fin q → Fin (2 ^ d)) :=
    { toFun := fun c => (c.foldScalar, c.queryIdxs)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  calc (PMF.uniformOfFintype (FRIChal F d q)).map FRIChal.foldScalar
      = ((PMF.uniformOfFintype (FRIChal F d q)).map e).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype (F × (Fin q → Fin (2 ^ d)))).map Prod.fst := by
          rw [Cslib.Probability.PMF.uniformOfFintype_map_equiv e]
    _ = PMF.uniformOfFintype F := Cslib.Probability.PMF.uniformOfFintype_prod_map_fst

omit [Field F] in
/-- Cardinality of `FRIChal` elements whose `q` query starting indices all lie in `S`. -/
private theorem card_filter_queryIdxs_mem [Fintype F] {d q : ℕ}
    (S : Finset (Fin (2 ^ d))) :
    (Finset.univ.filter fun c : FRIChal F d q => ∀ a : Fin q, c.queryIdxs a ∈ S).card =
      Fintype.card F * S.card ^ q := by
  let e : {c : FRIChal F d q // ∀ a : Fin q, c.queryIdxs a ∈ S} ≃
      F × (Fin q → {s : Fin (2 ^ d) // s ∈ S}) :=
    { toFun := fun ⟨c, hc⟩ => (c.foldScalar, fun a => ⟨c.queryIdxs a, hc a⟩)
      invFun := fun ⟨z, f⟩ => ⟨⟨z, fun a => (f a).val⟩, fun a => (f a).property⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  calc (Finset.univ.filter fun c : FRIChal F d q => ∀ a : Fin q, c.queryIdxs a ∈ S).card
      = Fintype.card {c : FRIChal F d q // ∀ a : Fin q, c.queryIdxs a ∈ S} :=
        (Fintype.card_subtype _).symm
    _ = Fintype.card (F × (Fin q → {s : Fin (2 ^ d) // s ∈ S})) := Fintype.card_congr e
    _ = Fintype.card F * S.card ^ q := by
        simp [Fintype.card_prod, Fintype.card_coe]

/-- When `pref.length = m` and `pref` is doomed at threshold `B`, at most `B` starting points in
`Fin (2 ^ d)` pass `friSmoothFinalPasses` against any final oracle `π`. -/
theorem card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {stmt : OracleTable params.d F}
    {pref : List (OracleTable params.d F × FRIChal F params.d params.q)}
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref π s).card ≤ B := by
  have hcommit : friSmoothCommitDoomed params B stmt pref params.m le_rfl := by
    have hle : pref.length ≤ params.m := hlen.le
    simp only [friSmoothDoomed, hle, ↓reduceDIte] at hdoomed
    exact (friSmoothCommitDoomed_congr_round params B stmt pref hlen hle le_rfl).mp hdoomed
  exact (card_filter_friSmoothFinalPasses_le params stmt pref hlen π).trans
    (hcommit (friSmoothFinalCodeword params π) (friSmoothFinalCodeword_mem_rsCode params π))

/-- **Unconditional smooth query-round escape bound**: when `pref.length = m` and `pref` is doomed
at threshold `B`, the probability over a uniform `FRIChal` that all `q` query repetitions pass is
at most `(B / 2 ^ d) ^ q`. -/
theorem friSmoothQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  classical
  let goodS : Finset (Fin (2 ^ params.d)) :=
    Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref π s
  have hgoodS_card : goodS.card ≤ B :=
    card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params hlen π hdoomed
  have hbad_eq :
      {c : FRIChal F params.d params.q | ¬ friSmoothGoodStep params B stmt pref π c} =
      {c : FRIChal F params.d params.q | ∀ a : Fin params.q, c.queryIdxs a ∈ goodS} := by
    ext c
    have hle : pref.length ≤ params.m := hlen.le
    have hlen' : (pref ++ [(π, c)]).length = params.m + 1 := by
      simp [List.length_append, hlen]
    have hnotle' : ¬ (pref ++ [(π, c)]).length ≤ params.m := by omega
    simp only [Set.mem_ofPred_eq, friSmoothGoodStep, hle, ↓reduceIte, friSmoothDoomed, hnotle',
      ↓reduceDIte]
    simp only [hlen', ↓reduceIte, prefQueryIdxs_append_self pref hlen π c,
      not_exists, not_not, friSmoothTranscriptSingleAccepts_append_iff params stmt pref hlen π c,
      goodS, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hbad_eq]
  have hden_pos : 0 < (2 ^ params.d) ^ params.q := Nat.pow_pos (Nat.pow_pos (by omega))
  have hcard_bound :
      (2 ^ params.d) ^ params.q *
        (Finset.univ.filter fun c : FRIChal F params.d params.q =>
          ∀ a : Fin params.q, c.queryIdxs a ∈ goodS).card ≤
      B ^ params.q * Fintype.card (FRIChal F params.d params.q) := by
    rw [card_filter_queryIdxs_mem goodS, card_friChal]
    calc (2 ^ params.d) ^ params.q * (Fintype.card F * goodS.card ^ params.q)
        = goodS.card ^ params.q * (Fintype.card F * (2 ^ params.d) ^ params.q) := by ring
      _ ≤ B ^ params.q * (Fintype.card F * (2 ^ params.d) ^ params.q) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgoodS_card _)
  have hdiv := Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
    (α := FRIChal F params.d params.q)
    (P := fun c => ∀ a : Fin params.q, c.queryIdxs a ∈ goodS) hden_pos hcard_bound
  have hpow :
      (((B ^ params.q : ℕ) : ℝ≥0∞) / (((2 ^ params.d) ^ params.q : ℕ) : ℝ≥0∞)) =
        ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  exact hdiv.trans_eq hpow

/-- **Polymorphic per-round weighted degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap contract** across all
`m` smooth FRI folding rounds at agreement threshold `B` and per-round exceptional-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
@[expose] def WeightedCurveGapPerRound [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (B_commit : Fin params.m → ℕ) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (params.domainSize (i.val + 1)) → ℕ),
    (∀ j, W j ≤ 2 ^ params.cumLog (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F),
      (∀ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) →
        (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity i), u r j = v r j), W j) ≤
          B) →
      ∀ Z : Finset F,
        (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter
            (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j) →
        Z.card ≤ B_commit i

/-- Pointwise monotonicity of `WeightedCurveGapPerRound` in the per-round scalar budget. -/
theorem WeightedCurveGapPerRound.mono [DecidableEq F] {params : FRISmoothParams F} {B : ℕ}
    {B₁ B₂ : Fin params.m → ℕ} (hgap : WeightedCurveGapPerRound params B B₁)
    (hle : ∀ i : Fin params.m, B₁ i ≤ B₂ i) :
    WeightedCurveGapPerRound params B B₂ :=
  fun i W hW_le hW_sum u hno Z hZ =>
    (hgap i W hW_le hW_sum u hno Z hZ).trans (hle i)

/-- **Polymorphic uniform weighted curve proximity-gap contract** for all `m` smooth FRI folding
rounds at agreement threshold `B` and uniform bad-scalar budget `B_commit` (definitionally equal to
`WeightedCurveGapPerRound params B (fun _ => B_commit)`). -/
@[expose] def WeightedCurveGapBound [DecidableEq F] (params : FRISmoothParams F)
    (B B_commit : ℕ) : Prop :=
  WeightedCurveGapPerRound params B (fun _ => B_commit)

/-- **Polymorphic per-round weighted curve escape-probability contract** across all `m` smooth FRI
folding rounds at agreement threshold `B` and per-round escape probability budgets
`ε_commit : Fin params.m → ℝ≥0∞` (matching [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2]
with degree-`(l⁽ⁱ⁾ - 1)` curves). -/
@[expose] def WeightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (params.domainSize (i.val + 1)) → ℕ),
    (∀ j, W j ≤ 2 ^ params.cumLog (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F),
      (∀ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) →
        (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity i), u r j = v r j), W j) ≤
          B) →
      (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter
            (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j} ≤
        ε_commit i

/-- Pointwise monotonicity of `WeightedCurveEscapePerRound` in the per-round escape budget. -/
theorem WeightedCurveEscapePerRound.mono [Fintype F] [DecidableEq F]
    {params : FRISmoothParams F} {B : ℕ} {ε₁ ε₂ : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε₁)
    (hle : ∀ i : Fin params.m, ε₁ i ≤ ε₂ i) :
    WeightedCurveEscapePerRound params B ε₂ :=
  fun i W hW_le hW_sum u hno => (hesc i W hW_le hW_sum u hno).trans (hle i)

/-- Every integer per-round bad-scalar bound `WeightedCurveGapPerRound params B B_commit` induces a
per-round escape-probability bound `ε_commit i = B_commit i / |F|`. -/
theorem weightedCurveEscapePerRound_of_gapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params B B_commit) :
    WeightedCurveEscapePerRound params B
      (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  intro i W hW_le hW_sum u hno_corr
  classical
  let badZ : Finset F :=
    Finset.univ.filter fun z : F =>
      ∃ v ∈ params.rsCode (i.val + 1),
        B < ∑ j ∈ Finset.univ.filter
          (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j
  have hbadZ_card : badZ.card ≤ B_commit i :=
    hgap i W hW_le hW_sum u hno_corr badZ (fun z hz => (Finset.mem_filter.mp hz).2)
  have hcard_bound :
      Fintype.card F * (Finset.univ.filter fun z : F => z ∈ badZ).card ≤
        B_commit i * Fintype.card F := by
    have hfeq : (Finset.univ.filter fun z : F => z ∈ badZ) = badZ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfeq, mul_comm]
    exact Nat.mul_le_mul_right _ hbadZ_card
  have hdiv := Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
    (α := F) (P := fun z => z ∈ badZ) Fintype.card_pos hcard_bound
  have hset :
      {z : F | ∃ v ∈ params.rsCode (i.val + 1),
        B < ∑ j ∈ Finset.univ.filter
          (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j} =
      {z : F | z ∈ badZ} := by
    ext z
    simp only [Set.mem_ofPred_eq, badZ, Finset.mem_filter, Finset.mem_univ, true_and]
  rwa [hset]

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveEscapePerRound`)**:
when `pref.length < m` and `pref` is doomed at threshold `B`, the probability over a uniform
`FRIChal` that the `l⁽ⁱ⁾`-to-1 folded target escapes to `> B` weighted agreement with
`params.rsCode (pref.length + 1)` is at most `ε_commit ⟨pref.length, hpm⟩`. Reuses
`Folding.lean`'s `exists_mem_reedSolomon_weighted_agree_lift` and `foldWord_eq_sum_smul`. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      ε_commit ⟨pref.length, hpm⟩ := by
  let i : ℕ := pref.length
  let ir : Fin params.m := ⟨i, hpm⟩
  have hle : pref.length ≤ params.m := hpm.le
  have hcommit : friSmoothCommitDoomed params B stmt pref i hle := by
    simpa only [friSmoothDoomed, hle, ↓reduceDIte] using hdoomed
  let f : Fin (params.arity ir * params.domainSize (i + 1)) → F :=
    fun idx => restrictOracle (i := params.cumLog i) π (params.fiberDomainEquiv ir idx)
  let u : Fin (params.arity ir) → Fin (params.domainSize (i + 1)) → F :=
    foldComp (params.g ^ (2 ^ params.cumLog i)) (params.ω ^ (2 ^ params.cumLog i)) f
  let W_next := friSmoothNextWeight params stmt pref i hpm π
  have hno_corr :
      ∀ v : Fin (params.arity ir) → Fin (params.domainSize (i + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i + 1)) →
        (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity ir), u r j = v r j),
          W_next j) ≤ B := by
    intro v hv
    let S := Finset.univ.filter fun j : Fin (params.domainSize (i + 1)) =>
      ∀ r : Fin (params.arity ir), u r j = v r j
    have hgpow : (params.g ^ (2 ^ params.cumLog i)) ^ params.arity ir =
        params.g ^ (2 ^ params.cumLog (i + 1)) := by
      rw [params.cumLog_succ ir, FRISmoothParams.arity, ← pow_mul, ← pow_add]
    have hωpow : (params.ω ^ (2 ^ params.cumLog i)) ^ params.arity ir =
        params.ω ^ (2 ^ params.cumLog (i + 1)) := by
      rw [params.cumLog_succ ir, FRISmoothParams.arity, ← pow_mul, ← pow_add]
    have hsplit : params.domainSize i = params.arity ir * params.domainSize (i + 1) :=
      params.domainSize_eq_arity_mul_succ ir
    have hdim : params.dim i = params.arity ir * params.dim (i + 1) :=
      params.dim_eq_arity_mul_succ ir
    have hωi : IsPrimitiveRoot (params.ω ^ (2 ^ params.cumLog i))
        (params.arity ir * params.domainSize (i + 1)) := by
      simpa only [← hsplit] using
        isPrimitiveRoot_pow_two_pow params.hω (params.cumLog_le_d hle)
    have hv' : ∀ r : Fin (params.arity ir), v r ∈ reedSolomon
        (cosetPoint ((params.g ^ (2 ^ params.cumLog i)) ^ params.arity ir)
          ((params.ω ^ (2 ^ params.cumLog i)) ^ params.arity ir) (params.domainSize (i + 1)))
        (params.dim (i + 1)) := fun r => by
      simpa only [FRISmoothParams.rsCode, FRISmoothParams.eval, cosetEval, hgpow, hωpow] using hv r
    let W_filt : Fin (params.arity ir * params.domainSize (i + 1)) → ℕ :=
      fun idx => friSmoothOracleFilterWeight params stmt pref i hle π
        (params.fiberDomainEquiv ir idx)
    obtain ⟨c, hc_rs, -, hc_sum⟩ := exists_mem_reedSolomon_weighted_agree_lift
      (pow_ne_zero _ params.hg) (params.arity_cast_ne_zero ir) (Nat.pow_pos (by omega)) hωi f v
      hv' W_filt
    let c' : Fin (params.domainSize i) → F := fun y => c ((params.fiberDomainEquiv ir).symm y)
    have hc'_rs : c' ∈ params.rsCode i := by
      obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp hc_rs
      refine mem_reedSolomon.mpr ⟨p, hdim.symm ▸ hp, ?_⟩
      ext y
      exact congrFun hpeq ((params.fiberDomainEquiv ir).symm y)
    have hsum_eq :
        (∑ idx ∈ Finset.univ.filter (fun idx => f idx = c idx), W_filt idx) =
        ∑ y ∈ Finset.univ.filter (fun y => restrictOracle (i := params.cumLog i) π y = c' y),
          friSmoothOracleFilterWeight params stmt pref i hle π y := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine (Finset.sum_congr rfl fun idx _ => ?_).trans
        (Equiv.sum_comp (params.fiberDomainEquiv ir)
          (fun y => if restrictOracle (i := params.cumLog i) π y = c' y then
            friSmoothOracleFilterWeight params stmt pref i hle π y else 0))
      simp only [f, c', W_filt, Equiv.symm_apply_apply]
    calc ∑ j ∈ S, W_next j
        ≤ ∑ idx ∈ Finset.univ.filter (fun idx => f idx = c idx), W_filt idx := hc_sum
      _ = ∑ y ∈ Finset.univ.filter (fun y => restrictOracle (i := params.cumLog i) π y = c' y),
            friSmoothOracleFilterWeight params stmt pref i hle π y := hsum_eq
      _ ≤ ∑ y ∈ Finset.univ.filter (fun y => friSmoothTargetWord params stmt pref i hle y = c' y),
            friSmoothPreWeight params stmt pref i hle y :=
          sum_agree_friSmoothOracleFilterWeight_le params stmt pref i hle π c'
      _ ≤ B := hcommit c' hc'_rs
  let badScalar : Set F :=
    {z : F | ∃ v ∈ params.rsCode (i + 1),
      B < ∑ j ∈ Finset.univ.filter
        (fun j => (∑ r : Fin (params.arity ir), z ^ r.val • u r) j = v j), W_next j}
  have hbad_eq :
      {c : FRIChal F params.d params.q | ¬ friSmoothGoodStep params B stmt pref π c} =
      FRIChal.foldScalar ⁻¹' badScalar := by
    ext c
    have hlen' : (pref ++ [(π, c)]).length = i + 1 := by simp [i, List.length_append]
    have hle' : (pref ++ [(π, c)]).length ≤ params.m := by omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, friSmoothGoodStep, hle, ↓reduceIte,
      friSmoothDoomed, hle', ↓reduceDIte]
    rw [friSmoothCommitDoomed_congr_round params B stmt (pref ++ [(π, c)]) hlen' hle' hpm]
    simp only [friSmoothCommitDoomed, i, friSmoothTargetWord_append_step params stmt pref hpm π c,
      friSmoothPreWeight_append_step params stmt pref hpm π c, foldWord_eq_sum_smul, not_forall,
      not_le, exists_prop, badScalar, W_next, u, f, ir, Set.mem_ofPred_eq]
  rw [hbad_eq, ← PMF.toOuterMeasure_map_apply,
    uniformOfFintype_friChal_map_foldScalar params.d params.q]
  exact hesc ir W_next (friSmoothNextWeight_le params stmt pref i hpm π)
    (sum_friSmoothNextWeight_le params stmt pref i hpm π) u hno_corr

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveGapPerRound`)**:
discharging `WeightedCurveGapPerRound` is left to the caller. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      (B_commit ⟨pref.length, hpm⟩ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) stmt pref hpm π hdoomed

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveGapBound`)**:
discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveGap [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B B_commit : ℕ}
    (hgap : WeightedCurveGapBound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitRound_escape_le_of_weightedCurveGapPerRound params hgap stmt pref hpm π hdoomed

/-- Per-round escape budget vector for single-word `(m + 1)`-round `friSmoothIOP`: `ε_commit i` in
folding rounds `0 ≤ i < m`, and `((2 ^ d - e - 1) / 2 ^ d) ^ q` in the final query round `m`. -/
@[expose] noncomputable def friSmoothRoundEscape (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) (j : Fin (params.m + 1)) : ℝ≥0∞ :=
  if hj : j.val < params.m then
    ε_commit ⟨j.val, hj⟩
  else
    (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q

/-- Summed interactive smooth FRI soundness error
`(∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friSmoothSumError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ i : Fin params.m, ε_commit i) +
    (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q

theorem sum_friSmoothRoundEscape_eq_friSmoothSumError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 1), friSmoothRoundEscape params e ε_commit j) =
      friSmoothSumError params e ε_commit := by
  rw [Fin.sum_univ_castSucc, friSmoothSumError]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [friSmoothRoundEscape, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta]
  · simp only [friSmoothRoundEscape, Fin.val_last, lt_irrefl, ↓reduceDIte]

/-- Uniform per-round escape error `sup_j (friSmoothRoundEscape params e ε_commit j)` across all
`m + 1` rounds of `friSmoothIOP`. -/
@[expose] noncomputable def friSmoothSupRBRError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  Finset.univ.sup (friSmoothRoundEscape params e ε_commit)

/-- Uniform per-round escape error for smooth FRI: the maximum of the commit-round error
`B_commit / |F|` and the batched query-round error `((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friSmoothRBRError [Fintype F] (params : FRISmoothParams F)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  max ((B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    ((((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q)

theorem friSmoothSupRBRError_const_le_friSmoothRBRError [Fintype F] (params : FRISmoothParams F)
    (e B_commit : ℕ) :
    friSmoothSupRBRError params e (fun _ => (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
      friSmoothRBRError params e B_commit := by
  refine Finset.sup_le fun j _ => ?_
  by_cases hj : j.val < params.m
  · simp only [friSmoothRoundEscape, hj, ↓reduceDIte]
    exact le_max_left _ _
  · simp only [friSmoothRoundEscape, hj, ↓reduceDIte]
    exact le_max_right _ _

/-- **Conditional step (indexed smooth per-round escape bound assuming
`WeightedCurveEscapePerRound`)**: discharging `WeightedCurveEscapePerRound` is left to the caller.
-/
theorem friSmoothPerRoundEscape_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ (j : Fin (params.m + 1)) pref π,
      pref.length = j.val →
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRoundEscape params e ε_commit j := by
  intro stmt _ j pref π hlen hdoomed
  by_cases hj : j.val < params.m
  · have hpm : pref.length < params.m := hlen ▸ hj
    have hbound := friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params hesc
      stmt pref hpm π hdoomed
    have hidx : (⟨pref.length, hpm⟩ : Fin params.m) = ⟨j.val, hj⟩ := Fin.ext hlen
    rw [hidx] at hbound
    simpa only [friSmoothRoundEscape, hj, ↓reduceDIte] using hbound
  · have heq : j.val = params.m := by omega
    have hlen_m : pref.length = params.m := hlen.trans heq
    simpa only [friSmoothRoundEscape, hj, ↓reduceDIte] using
      friSmoothQueryRound_escape_le params (2 ^ params.d - e - 1) stmt pref hlen_m π hdoomed

/-- **Conditional step (all-prefix smooth `sup` RBR escape bound assuming
`WeightedCurveEscapePerRound`)**: discharging `WeightedCurveEscapePerRound` is left to the caller.
-/
theorem friSmoothRBREscape_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothSupRBRError params e ε_commit :=
  iopEscape_le_sup_of_perRound (friSmoothRoundEscape params e ε_commit)
    (friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params hesc)
    (fun _ _ pref _ _ hge => by
      have hgt : ¬ pref.length ≤ params.m := by omega
      simp only [friSmoothGoodStep, hgt, ↓reduceIte])

/-- **Conditional step (uniform smooth round-by-round escape bound assuming
`WeightedCurveGapBound`)**: discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothRBREscape_of_weightedCurveGap [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRBRError params e B_commit :=
  fun stmt hfar pref π hdoomed =>
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params
      (weightedCurveEscapePerRound_of_gapPerRound params hgap) stmt hfar pref π hdoomed).trans
      (friSmoothSupRBRError_const_le_friSmoothRBRError params e B_commit)

/-- Single-word smooth FRI commit-phase game: runs `m` interactive smooth folding rounds and samples
the final committed oracle `πFinal ← P pref`, returning `true` iff strictly more than `B` starting
points in `Fin (2 ^ d)` pass `friSmoothFinalPasses`. -/
@[expose] noncomputable def friSmoothCommitGame [Fintype F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) : PMF Bool :=
  (iopRunRounds P params.m []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friSmoothFinalPasses params stmt pref πFinal s) :=
        Classical.decPred _
      decide (B < (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref πFinal s).card)

/-- **Conditional step (single-word smooth FRI commit-phase union bound assuming
`WeightedCurveEscapePerRound`)**: for `stmt ∉ params.proximityLang e`, `friSmoothCommitGame` exceeds
agreement `B = 2 ^ d - e - 1` with probability at most `∑ i : Fin params.m, ε_commit i`. -/
theorem friSmoothCommitGame_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, ε_commit i := by
  have hrbr := friSmoothIOP_rbrSound params e
  refine iopCommitPhase_map_true_le_sum (hrbr.init_doomed stmt hfar) (hrbr.step_doomed stmt)
    params.m ε_commit (fun i pref π hlen hdoomed => ?_) P _ (fun pref πFinal hlen hdoomed => ?_)
  · have hpm : pref.length < params.m := hlen ▸ i.isLt
    have hbound := friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params hesc
      stmt pref hpm π hdoomed
    have hidx : (⟨pref.length, hpm⟩ : Fin params.m) = i := Fin.ext hlen
    rwa [hidx] at hbound
  · have hcard := card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params hlen πFinal hdoomed
    have hcongr :
        (@Finset.filter _ (fun s => friSmoothFinalPasses params stmt pref πFinal s)
          (Classical.decPred _) Finset.univ).card =
        (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref πFinal s).card := by
      congr 2
    exact decide_eq_false (not_lt_of_ge (hcongr.trans_le hcard))

/-- **Conditional step (single-word smooth FRI commit-phase union bound assuming
`WeightedCurveGapPerRound`)**: specializes `friSmoothCommitGame_le_of_weightedCurveEscapePerRound`
to integer bad-scalar budgets `B_commit : Fin params.m → ℕ`. -/
theorem friSmoothCommitGame_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitGame_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) hfar P

/-- **Conditional step (summed interactive soundness for single-word `friSmoothIOP` assuming
`WeightedCurveEscapePerRound`)**: for `stmt ∉ params.proximityLang e` and any adaptive prover `P`,
`iopInteractiveGame (friSmoothIOP params) stmt P true ≤ friSmoothSumError params e ε_commit`. -/
theorem friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      friSmoothSumError params e ε_commit :=
  (iopInteractiveGame_le_sum (friSmoothIOP_rbrSound params e)
    (friSmoothRoundEscape params e ε_commit)
    (friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params hesc) hfar P).trans_eq
    (sum_friSmoothRoundEscape_eq_friSmoothSumError params e ε_commit)

/-- **Conditional step (summed interactive soundness for single-word `friSmoothIOP` assuming
`WeightedCurveGapPerRound`)**: specializes
`friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound` to integer bad-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
theorem friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      friSmoothSumError params e (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) hfar P

end SmoothRoundByRoundSoundness

section SmoothUniqueDecodingUpgrade

variable {F : Type} [Field F]

/-- Unweighted degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap hypothesis across all `m` smooth FRI folding
rounds at unique-decoding radii `e / 2 ^ cumLog (i + 1)` (matching
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1]). -/
@[expose] def UniqueCurveGapHypothesis [DecidableEq F] (params : FRISmoothParams F) (e : ℕ) :
    Prop :=
  ∀ (i : Fin params.m)
    (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F) (Z : Finset F),
    (params.arity i - 1) * params.domainSize (i.val + 1) < Z.card →
    (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (∑ r : Fin (params.arity i), z ^ r.val • u r) v ≤
        e / 2 ^ params.cumLog (i.val + 1)) →
    ∃ D' : Finset (Fin (params.domainSize (i.val + 1))),
      ∃ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) ∧
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1) ≤ D'.card ∧
        ∀ j ∈ D', ∀ r : Fin (params.arity i), u r j = v r j

/-- **Conditional step (shrinking per-round smooth unique-decoding weighted upgrade)**: inside the
unique-decoding regime `2 * e + params.dim 0 ≤ 2 ^ d`, assuming `UniqueCurveGapHypothesis params e`
yields `WeightedCurveGapPerRound` via `Folding.lean`'s `weighted_agree_of_curve_many` with
telescoping budget `fun i => (params.arity i - 1) * params.domainSize (i.val + 1)` (whose sum over
all `m` rounds is `2 ^ d - 2 ^ (d - totalLog) < 2 ^ d`). This does not itself prove the unweighted
curve proximity-gap theorem. -/
theorem weightedCurveGapPerRound_of_uniqueCurveGap [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e) :
    WeightedCurveGapPerRound params (2 ^ params.d - e - 1)
      (fun i => (params.arity i - 1) * params.domainSize (i.val + 1)) := by
  intro i W hW_le _ u hno_corr Z hZ_good
  let N : ℕ := params.domainSize (i.val + 1)
  let M : ℕ := 2 ^ params.cumLog (i.val + 1)
  let a : ℕ := params.arity i
  have ha_ge1 : 1 ≤ a := le_trans (by omega) (params.two_le_arity i)
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := params.two_pow_cumLog_mul_domainSize i.isLt
  have huniq_i : 2 * (e / M) + params.dim (i.val + 1) ≤ N :=
    params.two_mul_div_add_dim_le huniq i
  have he_lt : e < 2 ^ params.d := by
    have hdim_pos : 1 ≤ params.dim 0 := params.one_le_dim 0
    omega
  by_contra hgt
  have hZ_gt : (a - 1) * N < Z.card := Nat.lt_of_not_ge hgt
  have hdist_of_wt : ∀ (z : F) (v : Fin N → F),
      2 ^ params.d - e - 1 <
        ∑ j ∈ Finset.univ.filter (fun j => (∑ r : Fin a, z ^ r.val • u r) j = v j), W j →
      hammingDist (∑ r : Fin a, z ^ r.val • u r) v ≤ e / M := by
    intro z v hv_wt
    let S_eq := Finset.univ.filter fun j : Fin N => (∑ r : Fin a, z ^ r.val • u r) j = v j
    have hsum_le : (∑ j ∈ S_eq, W j) ≤ M * S_eq.card := by
      calc (∑ j ∈ S_eq, W j)
          ≤ ∑ _j ∈ S_eq, M := Finset.sum_le_sum fun j _ => hW_le j
        _ = S_eq.card * M := by simp
        _ = M * S_eq.card := mul_comm _ _
    have hpart : S_eq.card + hammingDist (∑ r : Fin a, z ^ r.val • u r) v = N := by
      rw [hammingDist]
      simpa only [S_eq, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
          (fun j => (∑ r : Fin a, z ^ r.val • u r) j = v j)
    have hmul : M * hammingDist (∑ r : Fin a, z ^ r.val • u r) v ≤ e := by
      have hsub : M * S_eq.card + M * hammingDist (∑ r : Fin a, z ^ r.val • u r) v =
          2 ^ params.d := by
        rw [← mul_add, hpart, hMN]
      have hv_wt' : 2 ^ params.d - e - 1 < ∑ j ∈ S_eq, W j := hv_wt
      omega
    exact (Nat.le_div_iff_mul_le hM_pos).mpr (by simpa only [mul_comm] using hmul)
  have hZ_close :
      ∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
        hammingDist (∑ r : Fin a, z ^ r.val • u r) v ≤ e / M := by
    intro z hz
    obtain ⟨v, hv_rs, hv_wt⟩ := hZ_good z hz
    exact ⟨v, hv_rs, hdist_of_wt z v hv_wt⟩
  obtain ⟨D', v, hv_rs, hD'_card, hD'_agree⟩ := hgap i u Z hZ_gt hZ_close
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω (params.cumLog_le_d i.isLt)
  have hgood_curve :
      ∀ z ∈ Z,
        2 ^ params.d - e - 1 <
          ∑ j ∈ Finset.univ.filter (fun j : Fin N =>
            (∑ r : Fin a, z ^ r.val * u r j) = ∑ r : Fin a, z ^ r.val * v r j), W j := by
    intro z hz
    obtain ⟨w, hw_rs, hw_wt⟩ := hZ_good z hz
    have hdist_w : hammingDist (∑ r : Fin a, z ^ r.val • u r) w ≤ e / M := hdist_of_wt z w hw_wt
    have hcurve_rs : (∑ r : Fin a, z ^ r.val • v r) ∈ params.rsCode (i.val + 1) :=
      Submodule.sum_mem _ fun r _ => (params.rsCode (i.val + 1)).smul_mem _ (hv_rs r)
    have hdist_curve :
        hammingDist (∑ r : Fin a, z ^ r.val • u r) (∑ r : Fin a, z ^ r.val • v r) ≤ e / M := by
      have hsub :
          D' ⊆ Finset.univ.filter (fun j : Fin N =>
            (∑ r : Fin a, z ^ r.val • u r) j = (∑ r : Fin a, z ^ r.val • v r) j) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        exact Finset.sum_congr rfl fun r _ => by rw [hD'_agree j hj r]
      have hpart :
          (Finset.univ.filter fun j : Fin N =>
            (∑ r : Fin a, z ^ r.val • u r) j = (∑ r : Fin a, z ^ r.val • v r) j).card +
            hammingDist (∑ r : Fin a, z ^ r.val • u r) (∑ r : Fin a, z ^ r.val • v r) = N := by
        rw [hammingDist]
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
            (fun j => (∑ r : Fin a, z ^ r.val • u r) j = (∑ r : Fin a, z ^ r.val • v r) j)
      have hcard_le := Finset.card_le_card hsub
      dsimp only [M, N] at hpart hcard_le ⊢
      omega
    have hweq : w = ∑ r : Fin a, z ^ r.val • v r :=
      eq_of_hammingDist_le_reedSolomon hα_inj (by simpa only [Fintype.card_fin] using huniq_i)
        hw_rs hcurve_rs hdist_w hdist_curve
    rw [hweq] at hw_wt
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hw_wt
  have hW_card_le : (Finset.univ.filter fun j : Fin N => 0 < W j).card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (Finset.univ : Finset (Fin N)) _
  have hZ_filt : (a - 1) * (Finset.univ.filter fun j : Fin N => 0 < W j).card < Z.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_left (a - 1) hW_card_le) hZ_gt
  have hcorr := weighted_agree_of_curve_many ha_ge1 W u v Z (2 ^ params.d - e - 1) hZ_filt
    hgood_curve
  exact not_lt_of_ge (hno_corr v hv_rs) hcorr

/-- **Conditional step (uniform smooth unique-decoding weighted upgrade)**: inside the
unique-decoding regime `2 * e + params.dim 0 ≤ 2 ^ d`, assuming `UniqueCurveGapHypothesis params e`
yields uniform `WeightedCurveGapBound` with round-`0` budget `2 ^ d - 2 ^ (d - firstStepLog)` via
`FRISmoothParams.arity_sub_one_mul_domainSize_le_first`. -/
theorem weightedCurveGapBound_of_uniqueCurveGap [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1)
      (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) :=
  (weightedCurveGapPerRound_of_uniqueCurveGap params huniq hgap).mono
    params.arity_sub_one_mul_domainSize_le_first

end SmoothUniqueDecodingUpgrade

section SmoothBCSROMComposition

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness assuming
`WeightedCurveEscapePerRound`)**: composes `friSmoothIOP_rbrSound` and
`friSmoothRBREscape_of_weightedCurveEscapePerRound` (`friSmoothSupRBRError`) with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonChiesaSpooner2016],
[BenSassonCarmonIshaiKoppartySaraf2020]); discharging `WeightedCurveEscapePerRound` is left to the
caller. -/
theorem friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params hesc) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedCurveEscapePerRound`)**: bounds verifier Merkle
cost via `isCostBounded_bcsMTCost_friSmoothVerifyROM` (`q_V = params.proofOracleQueries *
(L_path + 1)`) and composes with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`; discharging
`WeightedCurveEscapePerRound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveEscapePerRound
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params hesc) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothVerifyROM params encSym x prf (hops x prf hmem))

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness assuming
`WeightedCurveGapBound`)**: discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_weightedCurveGap (params : FRISmoothParams F)
    {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveGap params hgap) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedCurveGapBound`)**: discharging
`WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap
    (params : FRISmoothParams F) {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveGap params hgap) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothVerifyROM params encSym x prf (hops x prf hmem))

/-- **Conditional step (unique-decoding smooth BCS-FRI ROM soundness assuming
`UniqueCurveGapHypothesis`)**: combines `weightedCurveGapBound_of_uniqueCurveGap`
(`B_commit = 2 ^ d - 2 ^ (d - firstStepLog)`) with
`friSmoothBCS_romSoundness_bound_of_weightedCurveGap`; discharging `UniqueCurveGapHypothesis` is
left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_uniqueCurveGap (params : FRISmoothParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_weightedCurveGap params
    (weightedCurveGapBound_of_uniqueCurveGap params huniq hgap) hdec σ hFS hMT

end SmoothBCSROMComposition

/-! ### Binary 2-to-1 Specialization & Preserved `FRIParams` Soundness API -/

section BinaryTranscriptAndBridges

variable {F : Type} [Field F]

/-- Expected round-`i` word along a binary transcript prefix `pref`: `stmt` at round `0`, and the
2-to-1 coset folding of `prefOracle pref i` at `prefFoldScalar pref i` for round `i + 1`. -/
@[expose] def friTargetWord (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (2 ^ (params.d - i)) → F
  | 0, _ => restrictOracle (i := 0) stmt
  | i + 1, hi =>
    have hjd : i < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm
    fold2 (params.g ^ (2 ^ i)) (params.ω ^ (2 ^ i))
      (fun idx : Fin (2 * 2 ^ (params.d - (i + 1))) =>
        restrictOracle (i := i) (prefOracle pref i) (reindexDouble hjd idx))
      (prefFoldScalar pref i)

/-- Pre-filter integer fiber weight `W̃_i : Fin (2 ^ (d - i)) → ℕ` along a binary transcript prefix
`pref`, prior to applying the round-`i` oracle consistency check `π_i = friTargetWord ... i`. -/
@[expose] def friPreWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (2 ^ (params.d - i)) → ℕ
  | 0, _ => fun _ => 1
  | i + 1, hi =>
    have hjd : i < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm
    let prevTarget := friTargetWord params stmt pref i (Nat.le_of_succ_le hi)
    let prevWeight := friPreWeight params stmt pref i (Nat.le_of_succ_le hi)
    let prevOracle := restrictOracle (i := i) (prefOracle pref i)
    let filt : Fin (2 ^ (params.d - i)) → ℕ :=
      fun y => if prevOracle y = prevTarget y then prevWeight y else 0
    fun j =>
      filt (reindexDouble hjd ⟨j.val, by omega⟩) +
        filt (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)

/-- Filtered round-`i` weight for an explicit prover oracle `π` in binary FRI. -/
@[expose] def friOracleFilterWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) : ℕ :=
  if restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j then
    friPreWeight params stmt pref i hi j
  else 0

/-- Pushed round-`(i + 1)` weight induced by an explicit prover oracle `π` at round `i` in binary
FRI. -/
@[expose] def friNextWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) : ℕ :=
  have hjd : i < params.d := lt_of_lt_of_le hi params.hm
  friOracleFilterWeight params stmt pref i hi.le π (reindexDouble hjd ⟨j.val, by omega⟩) +
    friOracleFilterWeight params stmt pref i hi.le π
      (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)

/-- Prefix acceptance predicate for a starting index `s : Fin (2 ^ d)` through folding rounds
`0, ..., i - 1` along a binary transcript `pref`. -/
@[expose] def friPrefixPasses (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) : Prop :=
  prefOracle pref 0 s = stmt s ∧
  ∀ k : Fin params.m, k.val < i →
    fold2Fiber
      (prefOracle pref k.val (friRoundPosIdx params k s))
      (prefOracle pref k.val (friRoundNegIdx params k s))
      (params.eval k.val (friRoundPosFin params k s))
      (prefFoldScalar pref k.val) =
    prefOracle pref (k.val + 1) (friRoundPosIdx params k s)

/-- Full single-query acceptance predicate evaluated on a binary transcript list `pref` at starting
index `s : Fin (2 ^ d)`. -/
@[expose] def friTranscriptSingleAccepts (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) : Prop :=
  friPrefixPasses params stmt pref params.m s ∧
    prefOracle pref params.m (friFinalIdx params s) =
      friFinalCodeword params (prefOracle pref params.m) (friFinalFin params s)

/-- Final-round acceptance predicate for a length-`m` binary prefix `pref` and final oracle
`πFinal`. -/
@[expose] def friFinalPasses (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  (if params.m = 0 then πFinal s else prefOracle pref 0 s) = stmt s ∧
  (∀ k : Fin params.m,
    fold2Fiber
      (prefOracle pref k.val (friRoundPosIdx params k s))
      (prefOracle pref k.val (friRoundNegIdx params k s))
      (params.eval k.val (friRoundPosFin params k s))
      (prefFoldScalar pref k.val) =
    (if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1))
      (friRoundPosIdx params k s)) ∧
  πFinal (friFinalIdx params s) = friFinalCodeword params πFinal (friFinalFin params s)

instance instDecidableFriPrefixPasses [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    Decidable (friPrefixPasses params stmt pref i s) := by
  unfold friPrefixPasses
  infer_instance

instance instDecidableFriFinalPasses [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    Decidable (friFinalPasses params stmt pref πFinal s) := by
  unfold friFinalPasses
  infer_instance

/-- Binary commit-round doomed predicate at round `i ≤ m`. -/
@[expose] def friCommitDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) : Prop :=
  ∀ c ∈ params.rsCode i,
    (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j) ≤ B

/-- **Binary FRI round-by-round doomed-state predicate**. -/
@[expose] def friDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) : Prop :=
  if h : pref.length ≤ params.m then
    friCommitDoomed params B stmt pref pref.length h
  else if pref.length = params.m + 1 then
    ∃ a : Fin params.q,
      ¬ friTranscriptSingleAccepts params stmt pref (prefFinalQueryIdxs params pref a)
  else
    True

/-- **Binary FRI round-by-round good-step predicate**. -/
@[expose] def friGoodStep [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) : Prop :=
  if pref.length ≤ params.m then
    friDoomed params B stmt (pref ++ [(π, c)])
  else
    True

/-- **Polymorphic per-round weighted line proximity-gap contract** across all `m` binary FRI
folding rounds at agreement threshold `B` and per-round exceptional-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
@[expose] def WeightedLineGapPerRound [DecidableEq F] (params : FRIParams F)
    (B : ℕ) (B_commit : Fin params.m → ℕ) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
    (∀ j, W j ≤ 2 ^ (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
      (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
      ∀ Z : Finset F,
        (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j) →
        Z.card ≤ B_commit i

/-- Pointwise monotonicity of `WeightedLineGapPerRound` in the per-round scalar budget. -/
theorem WeightedLineGapPerRound.mono [DecidableEq F] {params : FRIParams F} {B : ℕ}
    {B₁ B₂ : Fin params.m → ℕ} (hgap : WeightedLineGapPerRound params B B₁)
    (hle : ∀ i : Fin params.m, B₁ i ≤ B₂ i) :
    WeightedLineGapPerRound params B B₂ :=
  fun i W hW_le hW_sum u₀ u₁ hno Z hZ =>
    (hgap i W hW_le hW_sum u₀ u₁ hno Z hZ).trans (hle i)

/-- **Polymorphic uniform weighted line proximity-gap contract** for all `m` binary FRI folding
rounds at agreement threshold `B` and uniform bad-scalar budget `B_commit`. -/
@[expose] def WeightedLineGapBound [DecidableEq F] (params : FRIParams F)
    (B B_commit : ℕ) : Prop :=
  WeightedLineGapPerRound params B (fun _ => B_commit)

/-- **Polymorphic per-round weighted line escape-probability contract** across all `m` binary FRI
folding rounds at agreement threshold `B` and per-round escape probability budgets
`ε_commit : Fin params.m → ℝ≥0∞`. -/
@[expose] def WeightedLineEscapePerRound [Fintype F] [DecidableEq F] (params : FRIParams F)
    (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
    (∀ j, W j ≤ 2 ^ (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
      (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
      (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j} ≤
        ε_commit i

/-- Pointwise monotonicity of `WeightedLineEscapePerRound` in the per-round escape budget. -/
theorem WeightedLineEscapePerRound.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {B : ℕ} {ε₁ ε₂ : Fin params.m → ℝ≥0∞} (hesc : WeightedLineEscapePerRound params B ε₁)
    (hle : ∀ i : Fin params.m, ε₁ i ≤ ε₂ i) :
    WeightedLineEscapePerRound params B ε₂ :=
  fun i W hW_le hW_sum u₀ u₁ hno => (hesc i W hW_le hW_sum u₀ u₁ hno).trans (hle i)

/-- Per-round escape budget vector for single-word `(m + 1)`-round `friIOP`. -/
noncomputable abbrev friRoundEscape (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) (j : Fin (params.m + 1)) : ℝ≥0∞ :=
  friSmoothRoundEscape params.toSmooth e ε_commit j

/-- Summed interactive binary FRI soundness error
`(∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
noncomputable abbrev friSumError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  friSmoothSumError params.toSmooth e ε_commit

/-- Uniform per-round escape error `sup_j (friRoundEscape params e ε_commit j)`. -/
noncomputable abbrev friSupRBRError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  friSmoothSupRBRError params.toSmooth e ε_commit

/-- Uniform per-round escape error for binary FRI. -/
noncomputable abbrev friRBRError [Fintype F] (params : FRIParams F)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  friSmoothRBRError params.toSmooth e B_commit

/-- Single-word binary FRI commit-phase game. -/
@[expose] noncomputable def friCommitGame [Fintype F] (params : FRIParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) : PMF Bool :=
  (iopRunRounds P params.m []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friFinalPasses params stmt pref πFinal s) :=
        Classical.decPred _
      decide (B < (Finset.univ.filter fun s => friFinalPasses params stmt pref πFinal s).card)

/-- Unweighted line proximity-gap hypothesis across all `m` binary FRI folding rounds at
unique-decoding radii `e / 2 ^ (i + 1)` (matching [BenSassonCarmonIshaiKoppartySaraf2020,
Theorem 4.1]). -/
@[expose] def UniqueLineGapHypothesis [DecidableEq F] (params : FRIParams F) (e : ℕ) : Prop :=
  ∀ (i : Fin params.m) (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F) (Z : Finset F),
    2 ^ (params.d - (i.val + 1)) < Z.card →
    (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (u₀ + z • u₁) v ≤ e / 2 ^ (i.val + 1)) →
    ∃ D' : Finset (Fin (2 ^ (params.d - (i.val + 1)))),
      ∃ v₀ ∈ params.rsCode (i.val + 1), ∃ v₁ ∈ params.rsCode (i.val + 1),
        2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1) ≤ D'.card ∧
        ∀ j ∈ D', u₀ j = v₀ j ∧ u₁ j = v₁ j

private def toSmoothDomEquiv (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m) :
    Fin (2 ^ (params.d - i)) ≃ Fin (params.toSmooth.domainSize i) :=
  finCongr (by rw [params.toSmooth_domainSize hi])

private theorem toSmoothDomEquiv_val (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m)
    (j : Fin (2 ^ (params.d - i))) :
    (toSmoothDomEquiv params hi j).val = j.val :=
  rfl

private theorem mem_rsCode_iff_toSmooth (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m)
    (v : Fin (2 ^ (params.d - i)) → F) :
    v ∈ params.rsCode i ↔ (v ∘ (toSmoothDomEquiv params hi).symm) ∈ params.toSmooth.rsCode i := by
  have hci : params.toSmooth.cumLog i = i := params.toSmooth_cumLog hi
  have hdim : params.toSmooth.dim i = params.dim i := params.toSmooth_dim hi
  simp only [FRIParams.rsCode, FRISmoothParams.rsCode, mem_reedSolomon, hdim]
  constructor
  · rintro ⟨p, hp, hpeq⟩
    refine ⟨p, hp, ?_⟩
    ext y
    have hv := congrFun hpeq ((toSmoothDomEquiv params hi).symm y)
    simp only [Function.comp_apply, FRIParams.eval, FRISmoothParams.eval, cosetEval, cosetPoint,
      hci, toSmoothDomEquiv, finCongr_symm, finCongr_apply, Fin.val_cast] at hv ⊢
    exact hv
  · rintro ⟨p, hp, hpeq⟩
    refine ⟨p, hp, ?_⟩
    ext j
    have hv := congrFun hpeq (toSmoothDomEquiv params hi j)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, FRIParams.eval, FRISmoothParams.eval,
      cosetEval, cosetPoint, hci, toSmoothDomEquiv_val] at hv ⊢
    exact hv

private theorem friTargetWord_apply_eq_smooth (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    friTargetWord params stmt pref i hi j =
      friSmoothTargetWord params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j) := by
  cases i with
  | zero => rfl
  | succ k =>
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    have hkd : k < params.d := lt_of_lt_of_le hkm params.hm
    have hck : params.toSmooth.cumLog k = k := params.toSmooth_cumLog hkm.le
    have hdom : params.toSmooth.domainSize (k + 1) = 2 ^ (params.d - (k + 1)) :=
      params.toSmooth_domainSize hi
    have hsplit : 2 ^ (params.d - k) = 2 * 2 ^ (params.d - (k + 1)) :=
      params.domainSize_eq_two_mul_succ hkd
    have hωk : IsPrimitiveRoot (params.ω ^ (2 ^ k)) (2 * 2 ^ (params.d - (k + 1))) :=
      hsplit ▸ isPrimitiveRoot_pow_two_pow params.hω hkd.le
    simp only [friTargetWord, friSmoothTargetWord]
    rw [fold2_eq_foldWord (Nat.pow_pos (by omega)) hωk]
    simp only [foldWord_apply_eq_foldFiber, foldFiber, foldFiberComp, hck]
    change (∑ r : Fin 2, _) = (∑ r : Fin 2, _)
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    · congr 1
      · change (∑ t : Fin 2, _) = (∑ t : Fin 2, _)
        refine Finset.sum_congr rfl fun t _ => ?_
        have hidx :
            (reindexDouble hkd (fiberIdx j t)).val =
              (params.toSmooth.fiberDomainEquiv ⟨k, hkm⟩
                (fiberIdx (toSmoothDomEquiv params hi j) t)).val := by
          simp only [reindexDouble, FRISmoothParams.fiberDomainEquiv, finCongr_apply, Fin.val_cast,
            fiberIdx, toSmoothDomEquiv_val, hdom]
        simp only [restrictOracle, hdom, hidx]

private theorem pushWeight_toSmooth_eq_add (params : FRIParams F) {k : ℕ} (hkm : k < params.m)
    (f : Fin (2 ^ (params.d - k)) → ℕ)
    (g : Fin (params.toSmooth.domainSize k) → ℕ)
    (hfg : ∀ y, f y = g (toSmoothDomEquiv params hkm.le y))
    (j : Fin (2 ^ (params.d - (k + 1)))) :
    let hkd : k < params.d := lt_of_lt_of_le hkm params.hm
    f (reindexDouble hkd ⟨j.val, by omega⟩) +
        f (reindexDouble hkd ⟨j.val + 2 ^ (params.d - (k + 1)), by omega⟩) =
      pushWeight (a := params.toSmooth.arity ⟨k, hkm⟩)
        (fun idx => g (params.toSmooth.fiberDomainEquiv ⟨k, hkm⟩ idx))
        (toSmoothDomEquiv params hkm j) := by
  have hkd : k < params.d := lt_of_lt_of_le hkm params.hm
  have hdom1 : params.toSmooth.domainSize (k + 1) = 2 ^ (params.d - (k + 1)) :=
    params.toSmooth_domainSize hkm
  simp only [pushWeight]
  change _ = ∑ t : Fin 2, _
  rw [Fin.sum_univ_two]
  have h0 :
      toSmoothDomEquiv params hkm.le (reindexDouble hkd ⟨j.val, by omega⟩) =
        params.toSmooth.fiberDomainEquiv ⟨k, hkm⟩
          (fiberIdx (toSmoothDomEquiv params hkm j) (0 : Fin 2)) := by
    apply Fin.ext
    simp [toSmoothDomEquiv, FRISmoothParams.fiberDomainEquiv, reindexDouble, fiberIdx]
  have h1 :
      toSmoothDomEquiv params hkm.le
          (reindexDouble hkd ⟨j.val + 2 ^ (params.d - (k + 1)), by omega⟩) =
        params.toSmooth.fiberDomainEquiv ⟨k, hkm⟩
          (fiberIdx (toSmoothDomEquiv params hkm j) (1 : Fin 2)) := by
    apply Fin.ext
    simp [toSmoothDomEquiv, FRISmoothParams.fiberDomainEquiv, reindexDouble, fiberIdx, hdom1]
  rw [hfg, hfg, h0, h1]

private theorem friPreWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))),
      friPreWeight params stmt pref i hi j =
        friSmoothPreWeight params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j)
  | 0, _, _ => rfl
  | k + 1, hi, j => by
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    simp only [friPreWeight, friSmoothPreWeight]
    refine pushWeight_toSmooth_eq_add params hkm
      (fun y =>
        if restrictOracle (i := k) (prefOracle pref k) y =
            friTargetWord params stmt pref k hkm.le y then
          friPreWeight params stmt pref k hkm.le y
        else 0)
      (fun y =>
        if restrictOracle (i := params.toSmooth.cumLog k) (prefOracle pref k) y =
            friSmoothTargetWord params.toSmooth stmt pref k hkm.le y then
          friSmoothPreWeight params.toSmooth stmt pref k hkm.le y
        else 0)
      (fun y => ?_) j
    simp only [friPreWeight_apply_eq_smooth params stmt pref k hkm.le y,
      friTargetWord_apply_eq_smooth params stmt pref k hkm.le y]
    rfl

private theorem friOracleFilterWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F) (j : Fin (2 ^ (params.d - i))) :
    friOracleFilterWeight params stmt pref i hi π j =
      friSmoothOracleFilterWeight params.toSmooth stmt pref i hi π
        (toSmoothDomEquiv params hi j) := by
  simp only [friOracleFilterWeight, friSmoothOracleFilterWeight,
    friTargetWord_apply_eq_smooth params stmt pref i hi j,
    friPreWeight_apply_eq_smooth params stmt pref i hi j]
  rfl

private theorem friNextWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) :
    friNextWeight params stmt pref i hi π j =
      friSmoothNextWeight params.toSmooth stmt pref i hi π (toSmoothDomEquiv params hi j) :=
  pushWeight_toSmooth_eq_add params hi _ _
    (friOracleFilterWeight_apply_eq_smooth params stmt pref i hi.le π) j

private theorem friSmoothFinal_toSmooth_eq (params : FRIParams F)
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friSmoothFinalIdx params.toSmooth s = friFinalIdx params s ∧
    friSmoothFinalCodeword params.toSmooth πFinal (friSmoothFinalFin params.toSmooth s) =
      friFinalCodeword params πFinal (friFinalFin params s) :=
  ⟨friSmoothFinalIdx_toSmooth params s, by
    simp only [friSmoothFinalCodeword, friFinalCodeword, params.toSmooth_finalAnchorPoints,
      eval_toSmooth_final]⟩

private theorem friPrefixPasses_iff_smooth (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    friPrefixPasses params stmt pref i s ↔
      friSmoothPrefixPasses params.toSmooth stmt pref i s := by
  simp only [friPrefixPasses, friSmoothPrefixPasses]
  refine and_congr_right fun _ => forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [foldFiber_toSmooth_eq_fold2Fiber, friSmoothFiberIdx_toSmooth_zero,
    friSmoothFiberIdx_toSmooth_one, friSmoothFoldedIdx_toSmooth]

private theorem friTranscriptSingleAccepts_iff_smooth (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt pref s ↔
      friSmoothTranscriptSingleAccepts params.toSmooth stmt pref s := by
  obtain ⟨hidx, hcw⟩ := friSmoothFinal_toSmooth_eq params (prefOracle pref params.m) s
  simp only [friTranscriptSingleAccepts, friSmoothTranscriptSingleAccepts,
    friPrefixPasses_iff_smooth, hidx, hcw]

/-- Exact equivalence between binary `friFinalPasses` and smooth `friSmoothFinalPasses` at
`params.toSmooth`. -/
theorem friFinalPasses_iff_friSmoothFinalPasses (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friFinalPasses params stmt pref πFinal s ↔
      friSmoothFinalPasses params.toSmooth stmt pref πFinal s := by
  obtain ⟨hidx, hcw⟩ := friSmoothFinal_toSmooth_eq params πFinal s
  simp only [friFinalPasses, friSmoothFinalPasses, hidx, hcw]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  rw [foldFiber_toSmooth_eq_fold2Fiber, friSmoothFiberIdx_toSmooth_zero,
    friSmoothFiberIdx_toSmooth_one, friSmoothFoldedIdx_toSmooth]

private theorem friCommitDoomed_iff_smooth [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) :
    friCommitDoomed params B stmt pref i hi ↔
      friSmoothCommitDoomed params.toSmooth B stmt pref i hi := by
  let e := toSmoothDomEquiv params hi
  have hsum : ∀ c : Fin (2 ^ (params.d - i)) → F,
      (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
        friPreWeight params stmt pref i hi j) =
      ∑ y ∈ Finset.univ.filter (fun y =>
          friSmoothTargetWord params.toSmooth stmt pref i hi y = (c ∘ e.symm) y),
        friSmoothPreWeight params.toSmooth stmt pref i hi y := by
    intro c
    rw [Finset.sum_filter, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      (Equiv.sum_comp e (fun y =>
        if friSmoothTargetWord params.toSmooth stmt pref i hi y = (c ∘ e.symm) y then
          friSmoothPreWeight params.toSmooth stmt pref i hi y else 0))
    simp only [Function.comp_apply, Equiv.symm_apply_apply,
      friTargetWord_apply_eq_smooth params stmt pref i hi j,
      friPreWeight_apply_eq_smooth params stmt pref i hi j, e]
  constructor
  · intro h c' hc'
    have hc : (c' ∘ e) ∈ params.rsCode i := by
      rw [mem_rsCode_iff_toSmooth params hi]
      simpa only [e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hc'
    have hle := h (c' ∘ e) hc
    rw [hsum (c' ∘ e)] at hle
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hle
  · intro h c hc
    rw [hsum c]
    exact h (c ∘ e.symm) ((mem_rsCode_iff_toSmooth params hi c).mp hc)

/-- Exact equivalence between binary `friDoomed` and smooth `friSmoothDoomed` at `params.toSmooth`.
-/
theorem friDoomed_iff_friSmoothDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    friDoomed params B stmt pref ↔ friSmoothDoomed params.toSmooth B stmt pref := by
  unfold friDoomed friSmoothDoomed
  split_ifs with h1 h2
  · exact friCommitDoomed_iff_smooth params B stmt pref pref.length h1
  · exact exists_congr fun a =>
      not_congr (friTranscriptSingleAccepts_iff_smooth params stmt pref
        (prefQueryIdxs pref params.m a))
  · exact Iff.rfl

/-- Exact equivalence between binary `friGoodStep` and smooth `friSmoothGoodStep` at
`params.toSmooth`. -/
theorem friGoodStep_iff_friSmoothGoodStep [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) :
    friGoodStep params B stmt pref π c ↔ friSmoothGoodStep params.toSmooth B stmt pref π c := by
  unfold friGoodStep friSmoothGoodStep
  split_ifs
  · exact friDoomed_iff_friSmoothDoomed params B stmt (pref ++ [(π, c)])
  · exact Iff.rfl

/-- Exact equality between binary `friCommitGame` and smooth `friSmoothCommitGame` at
`params.toSmooth`. -/
theorem friCommitGame_eq_friSmoothCommitGame [Fintype F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params B stmt P = friSmoothCommitGame params.toSmooth B stmt P := by
  unfold friCommitGame friSmoothCommitGame
  congr 1
  funext pref
  congr 1
  funext πFinal
  congr 1
  congr 1
  have hfilt :
      (@Finset.filter _ (fun s => friFinalPasses params stmt pref πFinal s)
        (Classical.decPred _) Finset.univ) =
      (@Finset.filter _ (fun s => friSmoothFinalPasses params.toSmooth stmt pref πFinal s)
        (Classical.decPred _) Finset.univ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      friFinalPasses_iff_friSmoothFinalPasses]
  exact congrArg Finset.card hfilt

private theorem forall_fin_toSmooth_arity_iff (params : FRIParams F) (i : Fin params.m)
    (P : Fin (params.toSmooth.arity i) → Prop) :
    (∀ r : Fin (params.toSmooth.arity i), P r) ↔ P ⟨0, by simp⟩ ∧ P ⟨1, by simp⟩ := by
  constructor
  · intro h
    exact ⟨h ⟨0, by simp⟩, h ⟨1, by simp⟩⟩
  · rintro ⟨h0, h1⟩ r
    have hr : r.val = 0 ∨ r.val = 1 := by
      have hlt : r.val < 2 := by simpa only [params.toSmooth_arity i] using r.isLt
      omega
    rcases hr with hr0 | hr1
    · exact (Fin.ext hr0 : r = ⟨0, by simp⟩) ▸ h0
    · exact (Fin.ext hr1 : r = ⟨1, by simp⟩) ▸ h1

private theorem curveSum_toSmooth_eq_line {α : Type*} (params : FRIParams F) (i : Fin params.m)
    (u : Fin (params.toSmooth.arity i) → α → F) (z : F) :
    (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) =
      u ⟨0, by simp⟩ + z • u ⟨1, by simp⟩ := by
  change (∑ r : Fin 2, z ^ r.val • u ⟨r.val, by simp [r.isLt]⟩) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]

private theorem sum_filter_toSmooth_eq {params : FRIParams F} {i : ℕ} (hi : i ≤ params.m)
    (W : Fin (2 ^ (params.d - i)) → ℕ) (P : Fin (2 ^ (params.d - i)) → Prop)
    [DecidablePred P] [DecidablePred (fun y => P ((toSmoothDomEquiv params hi).symm y))] :
    (∑ j ∈ Finset.univ.filter P, W j) =
      ∑ y ∈ Finset.univ.filter (fun y => P ((toSmoothDomEquiv params hi).symm y)),
        (W ∘ (toSmoothDomEquiv params hi).symm) y := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (Equiv.sum_comp (toSmoothDomEquiv params hi) (fun y =>
      if P ((toSmoothDomEquiv params hi).symm y) then
        (W ∘ (toSmoothDomEquiv params hi).symm) y else 0))
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

private theorem curveToLineRound_transport [DecidableEq F] (params : FRIParams F)
    (i : Fin params.m) (B : ℕ)
    (W : Fin (params.toSmooth.domainSize (i.val + 1)) → ℕ)
    (hW_le : ∀ y, W y ≤ 2 ^ params.toSmooth.cumLog (i.val + 1))
    (hW_sum : ∑ y, W y ≤ 2 ^ params.d)
    (u : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F)
    (hno : ∀ v : Fin (params.toSmooth.arity i) →
        Fin (params.toSmooth.domainSize (i.val + 1)) → F,
      (∀ r, v r ∈ params.toSmooth.rsCode (i.val + 1)) →
      (∑ y ∈ Finset.univ.filter (fun y => ∀ r : Fin (params.toSmooth.arity i), u r y = v r y),
        W y) ≤ B) :
    let e := toSmoothDomEquiv params i.isLt
    let W' : Fin (2 ^ (params.d - (i.val + 1))) → ℕ := W ∘ e
    let u₀ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨0, by simp⟩ ∘ e
    let u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨1, by simp⟩ ∘ e
    (∀ j, W' j ≤ 2 ^ (i.val + 1)) ∧
    (∑ j, W' j ≤ 2 ^ params.d) ∧
    (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
      (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W' j) ≤ B) ∧
    ({z : F | ∃ v ∈ params.toSmooth.rsCode (i.val + 1),
        B < ∑ y ∈ Finset.univ.filter
          (fun y => (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) y = v y), W y} =
     {z : F | ∃ v ∈ params.rsCode (i.val + 1),
        B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W' j}) := by
  let e := toSmoothDomEquiv params i.isLt
  let W' : Fin (2 ^ (params.d - (i.val + 1))) → ℕ := W ∘ e
  let u₀ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨0, by simp⟩ ∘ e
  let u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨1, by simp⟩ ∘ e
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · simpa only [W', Function.comp_apply, params.toSmooth_cumLog i.isLt] using hW_le (e j)
  · dsimp only [W', Function.comp_apply]
    rwa [Equiv.sum_comp e W]
  · intro v₀ hv₀ v₁ hv₁
    let v : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F :=
      fun r => if r.val = 0 then v₀ ∘ e.symm else v₁ ∘ e.symm
    have hv : ∀ r, v r ∈ params.toSmooth.rsCode (i.val + 1) := fun r => by
      dsimp only [v]
      split_ifs
      · exact (mem_rsCode_iff_toSmooth params i.isLt v₀).mp hv₀
      · exact (mem_rsCode_iff_toSmooth params i.isLt v₁).mp hv₁
    have heq : (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W' j) =
        ∑ y ∈ Finset.univ.filter (fun y => ∀ r : Fin (params.toSmooth.arity i), u r y = v r y),
          W y := by
      rw [sum_filter_toSmooth_eq i.isLt W' (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j)]
      refine Finset.sum_congr ?_ fun y _ => by
        simp only [W', e, Function.comp_apply, Equiv.apply_symm_apply]
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u₀, u₁, v, e, Function.comp_apply,
        Equiv.apply_symm_apply]
      rw [forall_fin_toSmooth_arity_iff params i]
      simp only [Nat.one_ne_zero, ↓reduceIte, Function.comp_apply]
    rw [heq]
    exact hno v hv
  · ext z
    simp only [Set.mem_ofPred_eq, curveSum_toSmooth_eq_line]
    constructor
    · rintro ⟨v, hv, hgt⟩
      refine ⟨v ∘ e, (mem_rsCode_iff_toSmooth params i.isLt (v ∘ e)).mpr
        (by simpa only [e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hv),
        ?_⟩
      rw [sum_filter_toSmooth_eq i.isLt W' (fun j => (u₀ + z • u₁) j = (v ∘ e) j)]
      simpa only [W', u₀, u₁, e, Function.comp_apply, Equiv.apply_symm_apply, Pi.add_apply,
        Pi.smul_apply] using hgt
    · rintro ⟨v, hv, hgt⟩
      refine ⟨v ∘ e.symm, (mem_rsCode_iff_toSmooth params i.isLt v).mp hv, ?_⟩
      rw [sum_filter_toSmooth_eq i.isLt W' (fun j => (u₀ + z • u₁) j = v j)] at hgt
      simpa only [W', u₀, u₁, e, Function.comp_apply, Equiv.apply_symm_apply, Pi.add_apply,
        Pi.smul_apply] using hgt

private theorem lineToCurveRound_transport [DecidableEq F] (params : FRIParams F)
    (i : Fin params.m) (B : ℕ)
    (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ)
    (hW_le : ∀ j, W j ≤ 2 ^ (i.val + 1))
    (hW_sum : ∑ j, W j ≤ 2 ^ params.d)
    (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F)
    (hno : ∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
      (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) :
    let e := toSmoothDomEquiv params i.isLt
    let W' : Fin (params.toSmooth.domainSize (i.val + 1)) → ℕ := W ∘ e.symm
    let u : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F :=
      fun r => if r.val = 0 then u₀ ∘ e.symm else u₁ ∘ e.symm
    (∀ y, W' y ≤ 2 ^ params.toSmooth.cumLog (i.val + 1)) ∧
    (∑ y, W' y ≤ 2 ^ params.d) ∧
    (∀ v : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F,
      (∀ r, v r ∈ params.toSmooth.rsCode (i.val + 1)) →
      (∑ y ∈ Finset.univ.filter (fun y => ∀ r : Fin (params.toSmooth.arity i), u r y = v r y),
        W' y) ≤ B) ∧
    ({z : F | ∃ v ∈ params.rsCode (i.val + 1),
        B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j} =
     {z : F | ∃ v ∈ params.toSmooth.rsCode (i.val + 1),
        B < ∑ y ∈ Finset.univ.filter
          (fun y => (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) y = v y), W' y}) := by
  let e := toSmoothDomEquiv params i.isLt
  let W' : Fin (params.toSmooth.domainSize (i.val + 1)) → ℕ := W ∘ e.symm
  let u : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F :=
    fun r => if r.val = 0 then u₀ ∘ e.symm else u₁ ∘ e.symm
  refine ⟨fun y => ?_, ?_, ?_, ?_⟩
  · simpa only [W', Function.comp_apply, params.toSmooth_cumLog i.isLt] using hW_le (e.symm y)
  · dsimp only [W', Function.comp_apply]
    rwa [Equiv.sum_comp e.symm W]
  · intro v hv
    let v₀ : Fin (2 ^ (params.d - (i.val + 1))) → F := v ⟨0, by simp⟩ ∘ e
    let v₁ : Fin (2 ^ (params.d - (i.val + 1))) → F := v ⟨1, by simp⟩ ∘ e
    have hv₀ : v₀ ∈ params.rsCode (i.val + 1) :=
      (mem_rsCode_iff_toSmooth params i.isLt v₀).mpr
        (by simpa only [v₀, e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using
          hv ⟨0, by simp⟩)
    have hv₁ : v₁ ∈ params.rsCode (i.val + 1) :=
      (mem_rsCode_iff_toSmooth params i.isLt v₁).mpr
        (by simpa only [v₁, e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using
          hv ⟨1, by simp⟩)
    have heq :
        (∑ y ∈ Finset.univ.filter (fun y => ∀ r : Fin (params.toSmooth.arity i), u r y = v r y),
          W' y) =
        ∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j := by
      rw [sum_filter_toSmooth_eq i.isLt W (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j)]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u, v₀, v₁, e, Function.comp_apply,
        Equiv.apply_symm_apply]
      rw [forall_fin_toSmooth_arity_iff params i]
      simp only [Nat.one_ne_zero, ↓reduceIte, Function.comp_apply]
    rw [heq]
    exact hno v₀ hv₀ v₁ hv₁
  · ext z
    simp only [Set.mem_ofPred_eq, curveSum_toSmooth_eq_line]
    constructor
    · rintro ⟨v, hv, hgt⟩
      refine ⟨v ∘ e.symm, (mem_rsCode_iff_toSmooth params i.isLt v).mp hv, ?_⟩
      rw [sum_filter_toSmooth_eq i.isLt W (fun j => (u₀ + z • u₁) j = v j)] at hgt
      simpa only [W', u, e, Function.comp_apply, Pi.add_apply, Pi.smul_apply, Fin.val_zero,
        Fin.val_one, ↓reduceIte, Nat.one_ne_zero] using hgt
    · rintro ⟨v, hv, hgt⟩
      refine ⟨v ∘ e, (mem_rsCode_iff_toSmooth params i.isLt (v ∘ e)).mpr
        (by simpa only [e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hv),
        ?_⟩
      rw [sum_filter_toSmooth_eq i.isLt W (fun j => (u₀ + z • u₁) j = (v ∘ e) j)]
      simpa only [W', u, e, Function.comp_apply, Equiv.apply_symm_apply, Pi.add_apply,
        Pi.smul_apply, Fin.val_zero, Fin.val_one, ↓reduceIte, Nat.one_ne_zero] using hgt

/-- Exact equivalence between binary `WeightedLineGapPerRound` and smooth
`WeightedCurveGapPerRound` at `params.toSmooth`. -/
theorem weightedLineGapPerRound_iff_weightedCurveGapPerRound [DecidableEq F]
    (params : FRIParams F) (B : ℕ) (B_commit : Fin params.m → ℕ) :
    WeightedLineGapPerRound params B B_commit ↔
      WeightedCurveGapPerRound params.toSmooth B B_commit := by
  constructor
  · intro hline i W hW_le hW_sum u hno Z hZ
    obtain ⟨hW'_le, hW'_sum, hno', hset⟩ :=
      curveToLineRound_transport params i B W hW_le hW_sum u hno
    exact hline i _ hW'_le hW'_sum _ _ hno' Z fun z hz => by
      have hmem := hZ z hz
      exact (Set.ext_iff.mp hset z).mp hmem
  · intro hcurve i W hW_le hW_sum u₀ u₁ hno Z hZ
    obtain ⟨hW'_le, hW'_sum, hno', hset⟩ :=
      lineToCurveRound_transport params i B W hW_le hW_sum u₀ u₁ hno
    exact hcurve i _ hW'_le hW'_sum _ hno' Z fun z hz => by
      have hmem := hZ z hz
      exact (Set.ext_iff.mp hset z).mp hmem

/-- Exact equivalence between binary `WeightedLineEscapePerRound` and smooth
`WeightedCurveEscapePerRound` at `params.toSmooth`. -/
theorem weightedLineEscapePerRound_iff_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) :
    WeightedLineEscapePerRound params B ε_commit ↔
      WeightedCurveEscapePerRound params.toSmooth B ε_commit := by
  constructor
  · intro hline i W hW_le hW_sum u hno
    obtain ⟨hW'_le, hW'_sum, hno', hset⟩ :=
      curveToLineRound_transport params i B W hW_le hW_sum u hno
    rw [hset]
    exact hline i _ hW'_le hW'_sum _ _ hno'
  · intro hcurve i W hW_le hW_sum u₀ u₁ hno
    obtain ⟨hW'_le, hW'_sum, hno', hset⟩ :=
      lineToCurveRound_transport params i B W hW_le hW_sum u₀ u₁ hno
    rw [hset]
    exact hcurve i _ hW'_le hW'_sum _ hno'

private theorem uniqueLineGapHypothesis_to_smooth [DecidableEq F] (params : FRIParams F) {e : ℕ}
    (hgap : UniqueLineGapHypothesis params e) :
    UniqueCurveGapHypothesis params.toSmooth e := by
  intro i u Z hZ hclose
  let eqv := toSmoothDomEquiv params i.isLt
  have hdom : params.toSmooth.domainSize (i.val + 1) = 2 ^ (params.d - (i.val + 1)) :=
    params.toSmooth_domainSize i.isLt
  have hcum : params.toSmooth.cumLog (i.val + 1) = i.val + 1 := params.toSmooth_cumLog i.isLt
  have hZ' : 2 ^ (params.d - (i.val + 1)) < Z.card := by
    simpa only [params.toSmooth_arity i, Nat.reduceSub, one_mul, hdom] using hZ
  let u₀ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨0, by simp⟩ ∘ eqv
  let u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F := u ⟨1, by simp⟩ ∘ eqv
  have hclose' : ∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (u₀ + z • u₁) v ≤ e / 2 ^ (i.val + 1) := by
    intro z hz
    obtain ⟨v, hv, hd⟩ := hclose z hz
    refine ⟨v ∘ eqv, (mem_rsCode_iff_toSmooth params i.isLt (v ∘ eqv)).mpr
      (by simpa only [eqv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hv),
      ?_⟩
    rw [curveSum_toSmooth_eq_line, hcum] at hd
    have hhd : hammingDist (u₀ + z • u₁) (v ∘ eqv) =
        hammingDist (u ⟨0, by simp⟩ + z • u ⟨1, by simp⟩) v := by
      simp only [hammingDist]
      refine Finset.card_bij (fun j _ => eqv j) (fun j hj => ?_) (fun _ _ _ _ h => eqv.injective h)
        (fun y hy => ⟨eqv.symm y, ?_, eqv.apply_symm_apply y⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, u₀, u₁, Function.comp_apply,
          Pi.add_apply, Pi.smul_apply] at hj ⊢
        exact hj
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, u₀, u₁, Function.comp_apply,
          Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at hy ⊢
        exact hy
    rwa [hhd]
  obtain ⟨D', v₀, hv₀, v₁, hv₁, hD'_card, hD'_agree⟩ := hgap i u₀ u₁ Z hZ' hclose'
  let v : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F :=
    fun r => if r.val = 0 then v₀ ∘ eqv.symm else v₁ ∘ eqv.symm
  refine ⟨D'.image eqv, v, fun r => ?_, ?_, fun y hy => ?_⟩
  · dsimp only [v]
    split_ifs
    · exact (mem_rsCode_iff_toSmooth params i.isLt v₀).mp hv₀
    · exact (mem_rsCode_iff_toSmooth params i.isLt v₁).mp hv₁
  · rw [Finset.card_image_of_injective D' eqv.injective, hdom, hcum]
    exact hD'_card
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    refine (forall_fin_toSmooth_arity_iff params i _).mpr ?_
    simpa only [v, u₀, u₁, Function.comp_apply, Equiv.symm_apply_apply, Fin.val_zero, Fin.val_one,
      Nat.one_ne_zero, ↓reduceIte] using hD'_agree j hj

end BinaryTranscriptAndBridges

section BinaryCorollaries

variable {F : Type} [Field F]

theorem friTargetWord_append (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friTargetWord params stmt (pref ++ extra) i hi = friTargetWord params stmt pref i hi := by
  ext j
  rw [friTargetWord_apply_eq_smooth, friTargetWord_apply_eq_smooth,
    friSmoothTargetWord_append params.toSmooth stmt pref extra hi hlen]

theorem friPreWeight_append [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friPreWeight params stmt (pref ++ extra) i hi = friPreWeight params stmt pref i hi := by
  ext j
  rw [friPreWeight_apply_eq_smooth, friPreWeight_apply_eq_smooth,
    friSmoothPreWeight_append params.toSmooth stmt pref extra hi hlen]

theorem friTargetWord_append_step (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friTargetWord params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      fold2 (params.g ^ (2 ^ pref.length)) (params.ω ^ (2 ^ pref.length))
        (fun idx : Fin (2 * 2 ^ (params.d - (pref.length + 1))) =>
          restrictOracle (i := pref.length) π
            (reindexDouble (lt_of_lt_of_le hpm params.hm) idx))
        c.foldScalar := by
  simp only [friTargetWord, prefOracle_append_self, prefFoldScalar_append_self]

theorem friPreWeight_append_step [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friPreWeight params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      friNextWeight params stmt pref pref.length hpm π := by
  ext j
  rw [friPreWeight_apply_eq_smooth, friNextWeight_apply_eq_smooth,
    friSmoothPreWeight_append_step params.toSmooth stmt pref hpm π c]

theorem friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) :
    friOracleFilterWeight params stmt pref i hi π j ≤
      friPreWeight params stmt pref i hi j := by
  rw [friOracleFilterWeight_apply_eq_smooth, friPreWeight_apply_eq_smooth]
  exact friSmoothOracleFilterWeight_le params.toSmooth stmt pref i hi π _

/-- Pointwise bound on pre-filter weights: `friPreWeight ... i j ≤ 2 ^ i`. -/
theorem friPreWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    friPreWeight params stmt pref i hi j ≤ 2 ^ i := by
  rw [friPreWeight_apply_eq_smooth]
  simpa only [params.toSmooth_cumLog hi] using
    friSmoothPreWeight_le params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j)

/-- Pointwise bound on pushed weights `friNextWeight ... i π j ≤ 2 ^ (i + 1)`. -/
theorem friNextWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) :
    friNextWeight params stmt pref i hi π j ≤ 2 ^ (i + 1) := by
  rw [friNextWeight_apply_eq_smooth]
  simpa only [params.toSmooth_cumLog hi] using
    friSmoothNextWeight_le params.toSmooth stmt pref i hi π (toSmoothDomEquiv params hi j)

/-- Total-weight bound: `∑ j, friPreWeight ... i j ≤ 2 ^ d`. -/
theorem sum_friPreWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) :
    (∑ j : Fin (2 ^ (params.d - i)), friPreWeight params stmt pref i hi j) ≤ 2 ^ params.d := by
  have heq : (∑ j : Fin (2 ^ (params.d - i)), friPreWeight params stmt pref i hi j) =
      ∑ y : Fin (params.toSmooth.domainSize i),
        friSmoothPreWeight params.toSmooth stmt pref i hi y :=
    (Finset.sum_congr rfl fun j _ => friPreWeight_apply_eq_smooth params stmt pref i hi j).trans
      (Equiv.sum_comp (toSmoothDomEquiv params hi) _)
  rw [heq]
  exact sum_friSmoothPreWeight_le params.toSmooth stmt pref i hi

/-- Total-weight bound on pushed weights: `∑ j, friNextWeight ... i π j ≤ 2 ^ d`. -/
theorem sum_friNextWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (2 ^ (params.d - (i + 1))), friNextWeight params stmt pref i hi π j) ≤
      2 ^ params.d := by
  have heq : (∑ j : Fin (2 ^ (params.d - (i + 1))), friNextWeight params stmt pref i hi π j) =
      ∑ y : Fin (params.toSmooth.domainSize (i + 1)),
        friSmoothNextWeight params.toSmooth stmt pref i hi π y :=
    (Finset.sum_congr rfl fun j _ => friNextWeight_apply_eq_smooth params stmt pref i hi π j).trans
      (Equiv.sum_comp (toSmoothDomEquiv params hi) _)
  rw [heq]
  exact sum_friSmoothNextWeight_le params.toSmooth stmt pref i hi π

/-- Monotonicity of filtered weighted agreement in binary FRI. -/
theorem sum_agree_friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (c : Fin (2 ^ (params.d - i)) → F) :
    (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := i) π j = c j),
      friOracleFilterWeight params stmt pref i hi π j) ≤
    ∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j := by
  let e := toSmoothDomEquiv params hi
  have hlhs :
      (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := i) π j = c j),
        friOracleFilterWeight params stmt pref i hi π j) =
      ∑ y ∈ Finset.univ.filter (fun y =>
          restrictOracle (i := params.toSmooth.cumLog i) π y = (c ∘ e.symm) y),
        friSmoothOracleFilterWeight params.toSmooth stmt pref i hi π y := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      (Equiv.sum_comp e (fun y =>
        if restrictOracle (i := params.toSmooth.cumLog i) π y = (c ∘ e.symm) y then
          friSmoothOracleFilterWeight params.toSmooth stmt pref i hi π y else 0))
    simp only [Function.comp_apply, Equiv.symm_apply_apply,
      friOracleFilterWeight_apply_eq_smooth params stmt pref i hi π j]
    rfl
  have hrhs :
      (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
        friPreWeight params stmt pref i hi j) =
      ∑ y ∈ Finset.univ.filter (fun y =>
          friSmoothTargetWord params.toSmooth stmt pref i hi y = (c ∘ e.symm) y),
        friSmoothPreWeight params.toSmooth stmt pref i hi y := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      (Equiv.sum_comp e (fun y =>
        if friSmoothTargetWord params.toSmooth stmt pref i hi y = (c ∘ e.symm) y then
          friSmoothPreWeight params.toSmooth stmt pref i hi y else 0))
    simp only [Function.comp_apply, Equiv.symm_apply_apply,
      friTargetWord_apply_eq_smooth params stmt pref i hi j,
      friPreWeight_apply_eq_smooth params stmt pref i hi j, e]
  rw [hlhs, hrhs]
  exact sum_agree_friSmoothOracleFilterWeight_le params.toSmooth stmt pref i hi π (c ∘ e.symm)

theorem friTranscriptSingleAccepts_append_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F)
    (c : FRIChal F params.d params.q) (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt (pref ++ [(πFinal, c)]) s ↔
      friFinalPasses params stmt pref πFinal s := by
  rw [friTranscriptSingleAccepts_iff_smooth, friFinalPasses_iff_friSmoothFinalPasses]
  exact friSmoothTranscriptSingleAccepts_append_iff params.toSmooth stmt pref hlen πFinal c s

theorem friTranscriptSingleAccepts_ofFn_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) s ↔
      friSingleAccepts params stmt chals oracles s := by
  rw [friTranscriptSingleAccepts_iff_smooth, friSingleAccepts_iff_friSmoothSingleAccepts]
  exact friSmoothTranscriptSingleAccepts_ofFn_iff params.toSmooth stmt oracles chals s

/-- **Exact binary starting-point counting identity** (corollary of
`card_filter_friSmoothPrefixPasses_eq`). -/
theorem card_filter_friPrefixPasses_eq [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      s.val % 2 ^ (params.d - i) = j.val ∧ friPrefixPasses params stmt pref i s).card =
    friOracleFilterWeight params stmt pref i hi (prefOracle pref i) j := by
  rw [friOracleFilterWeight_apply_eq_smooth]
  have hfilt :
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % 2 ^ (params.d - i) = j.val ∧ friPrefixPasses params stmt pref i s) =
      Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % params.toSmooth.domainSize i = (toSmoothDomEquiv params hi j).val ∧
          friSmoothPrefixPasses params.toSmooth stmt pref i s := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, params.toSmooth_domainSize hi,
      toSmoothDomEquiv_val, friPrefixPasses_iff_smooth]
  rw [hfilt]
  exact card_filter_friSmoothPrefixPasses_eq params.toSmooth stmt pref i hi _

/-- **Binary final query-acceptance counting bound** (corollary of
`card_filter_friSmoothFinalPasses_le`). -/
theorem card_filter_friFinalPasses_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      friFinalPasses params stmt pref πFinal s).card ≤
    ∑ j ∈ Finset.univ.filter (fun j =>
      friTargetWord params stmt pref params.m le_rfl j =
        friFinalCodeword params πFinal j),
      friPreWeight params stmt pref params.m le_rfl j := by
  let e := toSmoothDomEquiv params le_rfl
  have hlhs :
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        friFinalPasses params stmt pref πFinal s) =
      Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        friSmoothFinalPasses params.toSmooth stmt pref πFinal s := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      friFinalPasses_iff_friSmoothFinalPasses]
  have hrhs :
      (∑ j ∈ Finset.univ.filter (fun j =>
        friTargetWord params stmt pref params.m le_rfl j = friFinalCodeword params πFinal j),
        friPreWeight params stmt pref params.m le_rfl j) =
      ∑ y ∈ Finset.univ.filter (fun y =>
        friSmoothTargetWord params.toSmooth stmt pref params.m le_rfl y =
          friSmoothFinalCodeword params.toSmooth πFinal y),
        friSmoothPreWeight params.toSmooth stmt pref params.m le_rfl y := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      (Equiv.sum_comp e (fun y =>
        if friSmoothTargetWord params.toSmooth stmt pref params.m le_rfl y =
            friSmoothFinalCodeword params.toSmooth πFinal y then
          friSmoothPreWeight params.toSmooth stmt pref params.m le_rfl y else 0))
    have hcw : friFinalCodeword params πFinal j =
        friSmoothFinalCodeword params.toSmooth πFinal (e j) := by
      simp only [friFinalCodeword, friSmoothFinalCodeword, params.toSmooth_finalAnchorPoints,
        FRIParams.eval, FRISmoothParams.eval, cosetEval, cosetPoint, params.toSmooth_cumLog le_rfl,
        e, toSmoothDomEquiv_val]
    rw [friTargetWord_apply_eq_smooth params stmt pref params.m le_rfl j,
      friPreWeight_apply_eq_smooth params stmt pref params.m le_rfl j, hcw]
  rw [hlhs, hrhs]
  exact card_filter_friSmoothFinalPasses_le params.toSmooth stmt pref hlen πFinal

/-- **Unconditional round-by-round soundness invariant for binary `friIOP`** (corollary of
`friSmoothIOP_rbrSound`). -/
theorem friIOP_rbrSound [DecidableEq F] (params : FRIParams F) (e : ℕ) :
    IOPRoundByRoundSoundness (friIOP params) (params.proximityLang e)
      (friDoomed params (2 ^ params.d - e - 1))
      (friGoodStep params (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot :=
    (friDoomed_iff_friSmoothDoomed params _ stmt []).mpr
      ((friSmoothIOP_rbrSound params.toSmooth e).init_doomed stmt
        (by simpa only [FRIParams.toSmooth_proximityLang] using hnot))
  step_doomed stmt pref π c hdoomed hgood :=
    (friDoomed_iff_friSmoothDoomed params _ stmt _).mpr
      ((friSmoothIOP_rbrSound params.toSmooth e).step_doomed stmt pref π c
        ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)
        ((friGoodStep_iff_friSmoothGoodStep params _ stmt pref π c).mp hgood))
  reject_of_doomed stmt oracles chals hdoomed := by
    rw [friIOP_eq_friSmoothIOP]
    exact (friSmoothIOP_rbrSound params.toSmooth e).reject_of_doomed stmt oracles chals
      ((friDoomed_iff_friSmoothDoomed params _ stmt _).mp hdoomed)

/-- When `pref.length = m` and `pref` is doomed at threshold `B`, at most `B` starting points in
`Fin (2 ^ d)` pass `friFinalPasses` against any final oracle `π`. -/
theorem card_filter_friFinalPasses_le_of_friDoomed [DecidableEq F] (params : FRIParams F)
    {B : ℕ} {stmt : OracleTable params.d F}
    {pref : List (OracleTable params.d F × FRIChal F params.d params.q)}
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (Finset.univ.filter fun s => friFinalPasses params stmt pref π s).card ≤ B := by
  have hfilt :
      (Finset.univ.filter fun s => friFinalPasses params stmt pref π s) =
      Finset.univ.filter fun s => friSmoothFinalPasses params.toSmooth stmt pref π s := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      friFinalPasses_iff_friSmoothFinalPasses]
  rw [hfilt]
  exact card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params.toSmooth hlen π
    ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- **Unconditional binary query-round escape bound** (corollary of
`friSmoothQueryRound_escape_le`). -/
theorem friQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  have hset : {c | ¬ friGoodStep params B stmt pref π c} =
      {c | ¬ friSmoothGoodStep params.toSmooth B stmt pref π c} := by
    ext c
    simp only [Set.mem_ofPred_eq, friGoodStep_iff_friSmoothGoodStep]
  rw [hset]
  exact friSmoothQueryRound_escape_le params.toSmooth B stmt pref hlen π
    ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- Every integer per-round bad-scalar bound `WeightedLineGapPerRound params B B_commit` induces a
per-round escape-probability bound `ε_commit i = B_commit i / |F|`. -/
theorem weightedLineEscapePerRound_of_gapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params B B_commit) :
    WeightedLineEscapePerRound params B
      (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  (weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params B _).mpr
    (weightedCurveEscapePerRound_of_gapPerRound params.toSmooth
      ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params B B_commit).mp hgap))

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineEscapePerRound`)**
(corollary of `friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound`). -/
theorem friCommitRound_escape_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params B ε_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      ε_commit ⟨pref.length, hpm⟩ := by
  have hset : {c | ¬ friGoodStep params B stmt pref π c} =
      {c | ¬ friSmoothGoodStep params.toSmooth B stmt pref π c} := by
    ext c
    simp only [Set.mem_ofPred_eq, friGoodStep_iff_friSmoothGoodStep]
  rw [hset]
  exact friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params B ε_commit).mp hesc)
    stmt pref hpm π ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineGapPerRound`)**. -/
theorem friCommitRound_escape_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      (B_commit ⟨pref.length, hpm⟩ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitRound_escape_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) stmt pref hpm π hdoomed

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineGapBound`)**. -/
theorem friCommitRound_escape_le_of_weightedLineGap [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B B_commit : ℕ}
    (hgap : WeightedLineGapBound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitRound_escape_le_of_weightedLineGapPerRound params hgap stmt pref hpm π hdoomed

theorem sum_friRoundEscape_eq_friSumError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 1), friRoundEscape params e ε_commit j) =
      friSumError params e ε_commit :=
  sum_friSmoothRoundEscape_eq_friSmoothSumError params.toSmooth e ε_commit

theorem friSupRBRError_const_le_friRBRError [Fintype F] (params : FRIParams F)
    (e B_commit : ℕ) :
    friSupRBRError params e (fun _ => (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
      friRBRError params e B_commit :=
  friSmoothSupRBRError_const_le_friSmoothRBRError params.toSmooth e B_commit

/-- **Conditional step (indexed binary per-round escape bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friPerRoundEscape_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ (j : Fin (params.m + 1)) pref π,
      pref.length = j.val →
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRoundEscape params e ε_commit j := by
  intro stmt hfar j pref π hlen hdoomed
  have hset : {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} =
      {c | ¬ friSmoothGoodStep params.toSmooth (2 ^ params.d - e - 1) stmt pref π c} := by
    ext c
    simp only [Set.mem_ofPred_eq, friGoodStep_iff_friSmoothGoodStep]
  rw [hset]
  exact friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    stmt (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) j pref π hlen
    ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)

/-- **Conditional step (all-prefix binary `sup` RBR escape bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friRBREscape_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSupRBRError params e ε_commit := by
  intro stmt hfar pref π hdoomed
  have hset : {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} =
      {c | ¬ friSmoothGoodStep params.toSmooth (2 ^ params.d - e - 1) stmt pref π c} := by
    ext c
    simp only [Set.mem_ofPred_eq, friGoodStep_iff_friSmoothGoodStep]
  rw [hset]
  exact friSmoothRBREscape_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    stmt (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) pref π
    ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)

/-- **Conditional step (uniform binary round-by-round escape bound assuming
`WeightedLineGapBound`)**. -/
theorem friRBREscape_of_weightedLineGap [Fintype F] [DecidableEq F] (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRBRError params e B_commit :=
  fun stmt hfar pref π hdoomed =>
    (friRBREscape_of_weightedLineEscapePerRound params
      (weightedLineEscapePerRound_of_gapPerRound params hgap) stmt hfar pref π hdoomed).trans
      (friSupRBRError_const_le_friRBRError params e B_commit)

/-- **Conditional step (single-word binary FRI commit-phase union bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friCommitGame_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤ ∑ i : Fin params.m, ε_commit i := by
  rw [friCommitGame_eq_friSmoothCommitGame]
  exact friSmoothCommitGame_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) P

/-- **Conditional step (single-word binary FRI commit-phase union bound assuming
`WeightedLineGapPerRound`)**. -/
theorem friCommitGame_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitGame_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) hfar P

/-- **Conditional step (summed interactive soundness for single-word `friIOP` assuming
`WeightedLineEscapePerRound`)**. -/
theorem friIOP_interactiveGame_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤ friSumError params e ε_commit := by
  rw [friIOP_eq_friSmoothIOP]
  exact friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) P

/-- **Conditional step (summed interactive soundness for single-word `friIOP` assuming
`WeightedLineGapPerRound`)**. -/
theorem friIOP_interactiveGame_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      friSumError params e (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friIOP_interactiveGame_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) hfar P

/-- Fiber-size product identity `2 ^ (i + 1) * 2 ^ (d - (i + 1)) = 2 ^ d` for a folding round
`i : Fin params.m`. -/
theorem FRIParams.fiber_mul_domainSize (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d := by
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_domainSize i.isLt] using
    params.toSmooth.two_pow_cumLog_mul_domainSize i.isLt

/-- Round-dimension scaling identity `2 ^ (i + 1) * params.dim (i + 1) = params.dim 0` for a
folding round `i : Fin params.m`. -/
theorem FRIParams.fiber_mul_dim (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * params.dim (i.val + 1) = params.dim 0 := by
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_dim i.isLt,
    params.toSmooth_dim (Nat.zero_le params.m)] using
    params.toSmooth.two_pow_cumLog_mul_dim i.isLt

/-- Every round Reed–Solomon dimension `params.dim r` is at least `1`. -/
theorem FRIParams.one_le_dim (params : FRIParams F) (r : ℕ) : 1 ≤ params.dim r := by
  simp only [FRIParams.dim]
  exact Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Each active round dimension fits inside its active coset size (`r ≤ m`). -/
theorem FRIParams.dim_le_domainSize (params : FRIParams F) {r : ℕ} (hr : r ≤ params.m) :
    params.dim r ≤ 2 ^ (params.d - r) := by
  simpa only [params.toSmooth_dim hr, params.toSmooth_domainSize hr] using
    params.toSmooth.dim_le_domainSize hr

/-- Exact geometric sum of active folded coset sizes across all `m` binary FRI folding rounds:
`∑ i : Fin params.m, 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d - 2 ^ (params.d - params.m)`. -/
theorem FRIParams.sum_domainSize_succ (params : FRIParams F) :
    (∑ i : Fin params.m, 2 ^ (params.d - (i.val + 1))) =
      2 ^ params.d - 2 ^ (params.d - params.m) := by
  have h := params.toSmooth.sum_arity_sub_one_mul_domainSize
  rw [params.toSmooth_totalLog] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [FRISmoothParams.arity, pow_one, Nat.reduceSub, one_mul,
    params.toSmooth_domainSize i.isLt]

/-- Transport the initial unique-decoding bound `2 * e + params.dim 0 ≤ 2 ^ params.d` to the
scaled round-`(i + 1)` unique-decoding bound. -/
theorem FRIParams.two_mul_div_add_dim_le (params : FRIParams F) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) (i : Fin params.m) :
    2 * (e / 2 ^ (i.val + 1)) + params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) := by
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le params.m)] using huniq
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_dim i.isLt,
    params.toSmooth_domainSize i.isLt] using
    params.toSmooth.two_mul_div_add_dim_le huniq' i

/-- **Conditional step (shrinking per-round binary unique-decoding weighted upgrade)** (corollary of
`weightedCurveGapPerRound_of_uniqueCurveGap`). -/
theorem weightedLineGapPerRound_of_uniqueLineGap [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1)
      (fun i => 2 ^ (params.d - (i.val + 1))) := by
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le params.m)] using huniq
  have hsm := weightedCurveGapPerRound_of_uniqueCurveGap params.toSmooth huniq'
    (uniqueLineGapHypothesis_to_smooth params hgap)
  rw [weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  refine hsm.mono fun i => ?_
  simp only [FRISmoothParams.arity, pow_one, Nat.reduceSub, one_mul,
    params.toSmooth_domainSize i.isLt, le_rfl]

/-- **Conditional step (uniform binary unique-decoding weighted upgrade)**. -/
theorem weightedLineGapBound_of_uniqueLineGap [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (2 ^ (params.d - 1)) :=
  (weightedLineGapPerRound_of_uniqueLineGap params huniq hgap).mono fun _ =>
    Nat.pow_le_pow_right (by omega)
      (Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le _)) _)

end BinaryCorollaries

section SymbolEncoding

/-- Computable unsigned little-endian binary symbol encoding for `ZMod p` via `Nat.bits`,
preserving the minimal bit-list word layout `Nat.bits x.val` (distinct from the sign-magnitude
`ZMod` encoding in `Turing.MultiTapeTM.encZMod`). -/
@[expose] def encZMod {p : ℕ} (x : ZMod p) : List Bool :=
  Nat.bits x.val

/-- Computable unsigned little-endian binary symbol decoding for `ZMod p` via
`Turing.MultiTapeTM.ofBits`. -/
@[expose] def decZMod (p : ℕ) (bs : List Bool) : ZMod p :=
  (Turing.MultiTapeTM.ofBits bs : ZMod p)

theorem leftInverse_decZMod_encZMod (p : ℕ) [NeZero p] :
    Function.LeftInverse (decZMod p) (encZMod (p := p)) := by
  intro x
  simp only [decZMod, encZMod, Turing.MultiTapeTM.ofBits_bits, ZMod.natCast_zmod_val]

end SymbolEncoding

section BCSROMComposition

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness assuming
`WeightedLineEscapePerRound`)** (corollary of
`friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound`). -/
theorem friBCS_romSoundness_bound_of_weightedLineEscapePerRound (params : FRIParams F)
    {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang] at hMT ⊢
  exact friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    hdec σ hFS hMT

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedLineEscapePerRound`)**. -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineEscapePerRound
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang,
    ← FRIParams.toSmooth_proofOracleQueries]
  exact friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveEscapePerRound
    params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    hdec σ hMT hFS hops

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness assuming
`WeightedLineGapBound`)**. -/
theorem friBCS_romSoundness_bound_of_weightedLineGap (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang] at hMT ⊢
  exact friSmoothBCS_romSoundness_bound_of_weightedCurveGap params.toSmooth
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap)
    hdec σ hFS hMT

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedLineGapBound`)**. -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang,
    ← FRIParams.toSmooth_proofOracleQueries]
  exact friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap params.toSmooth
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap)
    hdec σ hMT hFS hops

/-- **Conditional step (unique-decoding binary BCS-FRI ROM soundness assuming
`UniqueLineGapHypothesis`)**. -/
theorem friBCS_romSoundness_bound_of_uniqueLineGap (params : FRIParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_weightedLineGap params
    (weightedLineGapBound_of_uniqueLineGap params huniq hgap) hdec σ hFS hMT

end BCSROMComposition

end Cslib.Crypto.Protocols.FRI
