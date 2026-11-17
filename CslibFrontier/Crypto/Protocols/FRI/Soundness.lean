/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Crypto.Protocols.FRI.Protocol
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.PMF.UniformBound
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# FRI Round-by-Round Soundness and BCS Random-Oracle Composition

This module proves unconditional round-by-round soundness
(`Cslib.Crypto.Protocols.BCS.IOPRoundByRoundSoundness`) and query-round escape bounds for the
multi-round 2-to-1 FRI IOP `Cslib.Crypto.Protocols.FRI.friIOP` ([BenSassonBentovHoreshRiabzev2018],
[BenSassonCarmonIshaiKoppartySaraf2020]), together with conditional commit-round escape and
two-channel BCS random-oracle composition steps parameterized by a line proximity-gap hypothesis
([BenSassonChiesaSpooner2016], [ChiesaYogev2024]).

## Overview of the integer-weight round-by-round invariant

For an input word `stmt : OracleTable params.d F` and any partial verifier transcript
`pref : List (OracleTable params.d F × FRIChal F params.d params.q)` of length `i ≤ m`:

* `friTargetWord params stmt pref i hi : Fin (2 ^ (d - i)) → F` is the expected round-`i` word:
  `stmt` at `i = 0`, and the 2-to-1 coset folding of the `(i - 1)`-th prover oracle `π_{i-1}` at
  the `(i - 1)`-th folding scalar `z_{i-1}` for `i ≥ 1`.
* `friPreWeight params stmt pref i hi : Fin (2 ^ (d - i)) → ℕ` is the pre-filter integer fiber
  weight before applying the round-`i` oracle check `π_i(j) = friTargetWord ... i j`: identically
  `1` at `i = 0`, and for `i ≥ 1` the fiberwise sum of the previous round's filtered weight
  `friOracleFilterWeight` (counting initial starting points above `j` satisfying
  `friPrefixPasses ... (i - 1)`, i.e., round-0 binding and folding checks `k < i - 1`, before
  enforcing round `i`). It satisfies `friPreWeight ... j ≤ 2 ^ i` and
  `∑ j, friPreWeight ... j ≤ 2 ^ d` unconditionally for arbitrary malicious oracles, while applying
  the round-`i` oracle check yields `friOracleFilterWeight`, which counts the exact number of
  initial starting points above `j` satisfying `friPrefixPasses ... i`
  (`card_filter_friPrefixPasses_eq`).
* A transcript prefix of length `i ≤ m` is **doomed** (`friDoomed params B stmt pref`) if every
  codeword `c ∈ params.rsCode i` has `friPreWeight`-weighted agreement at most `B` with
  `friTargetWord`. A complete transcript of length `m + 1` is doomed if at least one of the `q`
  queried starting points fails `friTranscriptSingleAccepts`.

This yields:
1. Unconditional `IOPRoundByRoundSoundness` (`friIOP_rbrSound`).
2. Unconditional query-round escape bound `≤ (B / 2 ^ d) ^ q` (`friQueryRound_escape_le`).
3. **Conditional steps** assuming a line proximity-gap theorem (`WeightedLineGapBound` or
   `UniqueLineGapHypothesis`): commit-round escape `≤ B_commit / |F|`
   (`friCommitRound_escape_le_of_weightedLineGap`), uniform per-round escape
   (`friRBREscape_of_weightedLineGap`), and the unique-decoding weighted upgrade
   (`weightedLineGapBound_of_uniqueLineGap` with `B_commit = 2 ^ (d - 1)`). These do not by
   themselves discharge the general unconditional proximity-gap theorems of
   [BenSassonCarmonIshaiKoppartySaraf2020].
4. **Conditional BCS ROM composition steps** (`friBCS_romSoundness_bound_of_weightedLineGap`,
   `friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap`, and
   `friBCS_romSoundness_bound_of_uniqueLineGap`) composing the conditional RBR escape bounds with
   `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` and
   `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`, together with an unsigned
   little-endian binary symbol codec (`encZMod`, `decZMod`) built directly on `Nat.bits` and
   `Turing.MultiTapeTM.ofBits` (`leftInverse_decZMod_encZMod`).
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section TranscriptState

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

/-- Read the final round's `q` query starting indices from a transcript, defaulting to `0`. -/
@[expose] def prefFinalQueryIdxs (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    Fin params.q → Fin (2 ^ params.d) :=
  match pref[params.m]? with
  | some (_, c) => c.queryIdxs
  | none => fun _ => ⟨0, Nat.pow_pos (by omega)⟩

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

theorem prefFinalQueryIdxs_append_self (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    prefFinalQueryIdxs params (pref ++ [(π, c)]) = c.queryIdxs := by
  simp only [prefFinalQueryIdxs, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

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

theorem prefFinalQueryIdxs_ofFn (params : FRIParams F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    prefFinalQueryIdxs params
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) =
      (chals (Fin.last params.m)).queryIdxs := by
  simp only [prefFinalQueryIdxs, List.getElem?_ofFn, Nat.lt_succ_self, ↓reduceDIte, Fin.last]

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

/-- Expected round-`i` word along a transcript prefix `pref`: `stmt` at round `0`, and the 2-to-1
coset folding of `prefOracle pref i` at `prefFoldScalar pref i` for round `i + 1`. -/
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

/-- Pre-filter integer fiber weight `W̃_i : Fin (2 ^ (d - i)) → ℕ` along a transcript prefix `pref`,
prior to applying the round-`i` oracle consistency check `π_i = friTargetWord ... i`: identically
`1` at `i = 0`, and for `i ≥ 1` the fiber sum of the round-`(i - 1)` filtered weight
`friOracleFilterWeight` (which itself carries the complete `friPrefixPasses` count via
`card_filter_friPrefixPasses_eq`). -/
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

/-- Filtered round-`i` weight for an explicit prover oracle `π`: retains `friPreWeight` on
coordinates where `π` agrees with `friTargetWord`, and zeroes all other coordinates. -/
@[expose] def friOracleFilterWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) : ℕ :=
  if restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j then
    friPreWeight params stmt pref i hi j
  else 0

/-- Pushed round-`(i + 1)` weight induced by an explicit prover oracle `π` at round `i` (independent
of the round-`i` verifier challenge). -/
@[expose] def friNextWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) : ℕ :=
  have hjd : i < params.d := lt_of_lt_of_le hi params.hm
  friOracleFilterWeight params stmt pref i hi.le π (reindexDouble hjd ⟨j.val, by omega⟩) +
    friOracleFilterWeight params stmt pref i hi.le π
      (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)

theorem friTargetWord_append (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friTargetWord params stmt (pref ++ extra) i hi = friTargetWord params stmt pref i hi := by
  cases i with
  | zero => rfl
  | succ k =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    simp only [friTargetWord, prefOracle_append_left pref extra hk,
      prefFoldScalar_append_left pref extra hk]

theorem friPreWeight_append [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friPreWeight params stmt (pref ++ extra) i hi = friPreWeight params stmt pref i hi := by
  induction i with
  | zero => rfl
  | succ k ih =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    have htarget := friTargetWord_append params stmt pref extra (Nat.le_of_succ_le hi) hk.le
    have hweight := ih (Nat.le_of_succ_le hi) hk.le
    ext j
    simp only [friPreWeight, htarget, hweight, prefOracle_append_left pref extra hk]

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
  have htarget := friTargetWord_append params stmt pref [(π, c)] hpm.le le_rfl
  have hweight := friPreWeight_append params stmt pref [(π, c)] hpm.le le_rfl
  simp only [friPreWeight, friNextWeight, friOracleFilterWeight, htarget, hweight,
    prefOracle_append_self]

theorem friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) :
    friOracleFilterWeight params stmt pref i hi π j ≤
      friPreWeight params stmt pref i hi j := by
  unfold friOracleFilterWeight
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Pointwise bound on pre-filter weights: `friPreWeight ... i j ≤ 2 ^ i`. -/
theorem friPreWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))),
      friPreWeight params stmt pref i hi j ≤ 2 ^ i
  | 0, _, _ => by simp [friPreWeight]
  | i + 1, hi, j => by
    have ih := friPreWeight_le params stmt pref i (Nat.le_of_succ_le hi)
    simp only [friPreWeight]
    have h1 :
        (if restrictOracle (i := i) (prefOracle pref i)
            (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm) ⟨j.val, by omega⟩) =
            friTargetWord params stmt pref i (Nat.le_of_succ_le hi)
              (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm) ⟨j.val, by omega⟩)
          then friPreWeight params stmt pref i (Nat.le_of_succ_le hi)
            (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm) ⟨j.val, by omega⟩)
          else 0) ≤ 2 ^ i := by
      split_ifs
      · exact ih _
      · exact Nat.zero_le _
    have h2 :
        (if restrictOracle (i := i) (prefOracle pref i)
            (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm)
              ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩) =
            friTargetWord params stmt pref i (Nat.le_of_succ_le hi)
              (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm)
                ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)
          then friPreWeight params stmt pref i (Nat.le_of_succ_le hi)
            (reindexDouble (lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm)
              ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)
          else 0) ≤ 2 ^ i := by
      split_ifs
      · exact ih _
      · exact Nat.zero_le _
    rw [pow_succ']
    omega

/-- Pointwise bound on pushed weights `friNextWeight ... i π j ≤ 2 ^ (i + 1)`. -/
theorem friNextWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) :
    friNextWeight params stmt pref i hi π j ≤ 2 ^ (i + 1) := by
  have hjd : i < params.d := lt_of_lt_of_le hi params.hm
  simp only [friNextWeight]
  have h1 := (friOracleFilterWeight_le params stmt pref i hi.le π
      (reindexDouble hjd ⟨j.val, by omega⟩)).trans
    (friPreWeight_le params stmt pref i hi.le (reindexDouble hjd ⟨j.val, by omega⟩))
  have h2 := (friOracleFilterWeight_le params stmt pref i hi.le π
      (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)).trans
    (friPreWeight_le params stmt pref i hi.le
      (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩))
  rw [pow_succ']
  omega

/-- Helper: summing `W j + W (j + N)` over `j : Fin N` equals summing `W` over `Fin (2 ^ (d - i))`.
-/
private theorem sum_pair_reindexDouble {d i : ℕ} (hi : i < d)
    (W : Fin (2 ^ (d - i)) → ℕ) :
    (∑ j : Fin (2 ^ (d - (i + 1))),
      (W (reindexDouble hi ⟨j.val, by omega⟩) +
        W (reindexDouble hi ⟨j.val + 2 ^ (d - (i + 1)), by omega⟩))) =
      ∑ y : Fin (2 ^ (d - i)), W y := by
  have hpush := sum_pushWeight (a := 2) (N := 2 ^ (d - (i + 1)))
    (fun idx : Fin (2 * 2 ^ (d - (i + 1))) => W (reindexDouble hi idx))
  have hlhs :
      (∑ j : Fin (2 ^ (d - (i + 1))),
        pushWeight (a := 2) (fun idx : Fin (2 * 2 ^ (d - (i + 1))) => W (reindexDouble hi idx)) j) =
      ∑ j : Fin (2 ^ (d - (i + 1))),
        (W (reindexDouble hi ⟨j.val, by omega⟩) +
          W (reindexDouble hi ⟨j.val + 2 ^ (d - (i + 1)), by omega⟩)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pushWeight, Fin.sum_univ_two, fiberIdx, Fin.val_zero, Fin.val_one, zero_mul,
      add_zero, one_mul]
  rw [← hlhs, hpush]
  exact Equiv.sum_comp (reindexDoubleEquiv hi) W

/-- Total-weight bound: `∑ j, friPreWeight ... i j ≤ 2 ^ d`. -/
theorem sum_friPreWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m),
      (∑ j : Fin (2 ^ (params.d - i)), friPreWeight params stmt pref i hi j) ≤ 2 ^ params.d
  | 0, _ => by simp [friPreWeight]
  | i + 1, hi => by
    have ih := sum_friPreWeight_le params stmt pref i (Nat.le_of_succ_le hi)
    have hjd : i < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm
    let filt : Fin (2 ^ (params.d - i)) → ℕ :=
      fun y =>
        if restrictOracle (i := i) (prefOracle pref i) y =
            friTargetWord params stmt pref i (Nat.le_of_succ_le hi) y then
          friPreWeight params stmt pref i (Nat.le_of_succ_le hi) y
        else 0
    calc ∑ j : Fin (2 ^ (params.d - (i + 1))), friPreWeight params stmt pref (i + 1) hi j
        = ∑ y : Fin (2 ^ (params.d - i)), filt y := sum_pair_reindexDouble hjd filt
      _ ≤ ∑ y : Fin (2 ^ (params.d - i)),
            friPreWeight params stmt pref i (Nat.le_of_succ_le hi) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          dsimp only [filt]
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
      _ ≤ 2 ^ params.d := ih

/-- Total-weight bound on pushed weights: `∑ j, friNextWeight ... i π j ≤ 2 ^ d`. -/
theorem sum_friNextWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (2 ^ (params.d - (i + 1))), friNextWeight params stmt pref i hi π j) ≤
      2 ^ params.d := by
  have hjd : i < params.d := lt_of_lt_of_le hi params.hm
  calc ∑ j : Fin (2 ^ (params.d - (i + 1))), friNextWeight params stmt pref i hi π j
      = ∑ y : Fin (2 ^ (params.d - i)), friOracleFilterWeight params stmt pref i hi.le π y :=
        sum_pair_reindexDouble hjd (friOracleFilterWeight params stmt pref i hi.le π)
    _ ≤ ∑ y : Fin (2 ^ (params.d - i)), friPreWeight params stmt pref i hi.le y :=
        Finset.sum_le_sum fun y _ => friOracleFilterWeight_le params stmt pref i hi.le π y
    _ ≤ 2 ^ params.d := sum_friPreWeight_le params stmt pref i hi.le

/-- Monotonicity of filtered weighted agreement: replacing `friTargetWord` and `friPreWeight` by
an arbitrary prover oracle `π` and its filtered weight `friOracleFilterWeight` cannot increase
weighted agreement with any word `c`. -/
theorem sum_agree_friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (c : Fin (2 ^ (params.d - i)) → F) :
    (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := i) π j = c j),
      friOracleFilterWeight params stmt pref i hi π j) ≤
    ∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j := by
  have hzero :
      (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := i) π j = c j),
        friOracleFilterWeight params stmt pref i hi π j) =
      ∑ j ∈ Finset.univ.filter (fun j =>
          restrictOracle (i := i) π j = c j ∧
            restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j),
        friPreWeight params stmt pref i hi j := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun j => restrictOracle (i := i) π j = c j)
      (fun j => restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j)]
    have hrest :
        (∑ j ∈ (Finset.univ.filter fun j => restrictOracle (i := i) π j = c j).filter
            (fun j => ¬ restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j),
          friOracleFilterWeight params stmt pref i hi π j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne := (Finset.mem_filter.mp hj).2
      simp only [friOracleFilterWeight, hne, ↓reduceIte]
    rw [hrest, add_zero, Finset.filter_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    have heq := (Finset.mem_filter.mp hj).2.2
    simp only [friOracleFilterWeight, heq, ↓reduceIte]
  rw [hzero]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  have hmem := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.2.symm.trans hmem.1⟩

end TranscriptState

section StartingPointCounting

variable {F : Type} [Field F]

/-- Prefix acceptance predicate for a starting index `s : Fin (2 ^ d)` through folding rounds
`0, ..., i - 1` along a transcript `pref`: round-0 binding `π_0(s) = stmt(s)` plus folding checks
for every `k < i`. -/
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

/-- Full single-query acceptance predicate evaluated on a transcript list `pref` at starting index
`s : Fin (2 ^ d)`. -/
@[expose] def friTranscriptSingleAccepts (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) : Prop :=
  friPrefixPasses params stmt pref params.m s ∧
    prefOracle pref params.m (friFinalIdx params s) =
      friFinalCodeword params (prefOracle pref params.m) (friFinalFin params s)

/-- Final-round acceptance predicate for a length-`m` prefix `pref` and final oracle `πFinal`
(manifestly independent of the final round's verifier challenge `c`). -/
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

theorem friTranscriptSingleAccepts_append_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F)
    (c : FRIChal F params.d params.q) (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt (pref ++ [(πFinal, c)]) s ↔
      friFinalPasses params stmt pref πFinal s := by
  have h0 : prefOracle (pref ++ [(πFinal, c)]) 0 s =
      if params.m = 0 then πFinal s else prefOracle pref 0 s := by
    by_cases hm : params.m = 0
    · have hp0 : pref.length = 0 := hlen.trans hm
      simp only [hm, ↓reduceIte, ← hp0, prefOracle_append_self]
    · have hpos : 0 < pref.length := by omega
      simp only [hm, ↓reduceIte, prefOracle_append_left pref [(πFinal, c)] hpos]
  have hm_eq : prefOracle (pref ++ [(πFinal, c)]) params.m = πFinal := by
    rw [← hlen, prefOracle_append_self]
  simp only [friTranscriptSingleAccepts, friPrefixPasses, friFinalPasses, h0, hm_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro h k
    have hk_lt : k.val < pref.length := by omega
    have hk_next : prefOracle (pref ++ [(πFinal, c)]) (k.val + 1) =
        if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1) := by
      by_cases hlast : k.val + 1 = params.m
      · simp only [hlast, ↓reduceIte, hm_eq]
      · have hlt : k.val + 1 < pref.length := by omega
        simp only [hlast, ↓reduceIte, prefOracle_append_left pref [(πFinal, c)] hlt]
    simpa only [prefOracle_append_left pref [(πFinal, c)] hk_lt,
      prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hk_next] using h k k.isLt
  · intro h k _
    have hk_lt : k.val < pref.length := by omega
    have hk_next : prefOracle (pref ++ [(πFinal, c)]) (k.val + 1) =
        if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1) := by
      by_cases hlast : k.val + 1 = params.m
      · simp only [hlast, ↓reduceIte, hm_eq]
      · have hlt : k.val + 1 < pref.length := by omega
        simp only [hlast, ↓reduceIte, prefOracle_append_left pref [(πFinal, c)] hlt]
    simpa only [prefOracle_append_left pref [(πFinal, c)] hk_lt,
      prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hk_next] using h k

theorem friTranscriptSingleAccepts_ofFn_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) s ↔
      friSingleAccepts params stmt chals oracles s := by
  simp only [friTranscriptSingleAccepts, friPrefixPasses, friSingleAccepts,
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

/-- Exact mod-splitting helper: for `j < N`, `s % N = j` splits disjointly into
`s % (2 * N) = j` and `s % (2 * N) = j + N`. -/
private theorem mod_eq_iff_mod_two_mul_eq {s j N : ℕ} (hj : j < N) :
    s % N = j ↔ s % (2 * N) = j ∨ s % (2 * N) = j + N := by
  have hN : 0 < N := by omega
  have hrem := Nat.mod_lt s (by omega : 0 < 2 * N)
  have hmod_mod : (s % (2 * N)) % N = s % N := Nat.mod_mul_left_mod s 2 N
  constructor
  · intro h
    by_cases hlt : s % (2 * N) < N
    · left
      rw [← h, ← hmod_mod, Nat.mod_eq_of_lt hlt]
    · right
      have hsub : (s % (2 * N) - N) % N = s % N := by
        rw [← hmod_mod]
        have hadd : s % (2 * N) = (s % (2 * N) - N) + N := by omega
        conv_rhs => rw [hadd, Nat.add_mod_right]
      have hlt2 : s % (2 * N) - N < N := by omega
      rw [Nat.mod_eq_of_lt hlt2] at hsub
      omega
  · rintro (h | h)
    · rw [← hmod_mod, h, Nat.mod_eq_of_lt hj]
    · rw [← hmod_mod, h, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- **Exact starting-point counting identity**: for every round `i ≤ m` and active-domain
coordinate `j : Fin (2 ^ (d - i))`, the filtered weight
`friOracleFilterWeight ... i (prefOracle pref i) j` equals the exact number of initial positions
`s : Fin (2 ^ d)` with `s % 2 ^ (d - i) = j` that satisfy `friPrefixPasses ... i s`. -/
theorem card_filter_friPrefixPasses_eq [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))),
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % 2 ^ (params.d - i) = j.val ∧ friPrefixPasses params stmt pref i s).card =
      friOracleFilterWeight params stmt pref i hi (prefOracle pref i) j := by
  intro i
  induction i with
  | zero =>
    intro hi j
    have hpred :
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % 2 ^ (params.d - 0) = j.val ∧ friPrefixPasses params stmt pref 0 s) =
        if prefOracle pref 0 j = stmt j then {j} else ∅ := by
      ext s
      simp only [Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and, friPrefixPasses,
        Nat.not_lt_zero, false_implies, implies_true, and_true, Nat.mod_eq_of_lt s.isLt]
      by_cases hok : prefOracle pref 0 j = stmt j
      · simp only [hok, ↓reduceIte, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, _⟩
          exact Fin.ext hs
        · rintro rfl
          exact ⟨rfl, hok⟩
      · simp only [hok, ↓reduceIte, Finset.notMem_empty, iff_false, not_and]
        intro hs
        have hsj : s = j := Fin.ext hs
        subst hsj
        exact hok
    rw [hpred]
    simp only [friOracleFilterWeight, friTargetWord, friPreWeight, restrictOracle, Fin.eta]
    by_cases hok : prefOracle pref 0 j = stmt j <;> simp [hok]
  | succ k ih =>
    intro hi j
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    have hkd : k < params.d := lt_of_lt_of_le hkm params.hm
    let N := 2 ^ (params.d - (k + 1))
    have hsplit : 2 ^ (params.d - k) = 2 * N := params.domainSize_eq_two_mul_succ hkd
    have hstep_eq : ∀ s : Fin (2 ^ params.d), s.val % N = j.val →
        (friPrefixPasses params stmt pref (k + 1) s ↔
          friPrefixPasses params stmt pref k s ∧
            restrictOracle (i := k + 1) (prefOracle pref (k + 1)) j =
              friTargetWord params stmt pref (k + 1) hi j) := by
      intro s hs
      have hkf : (⟨k, hkm⟩ : Fin params.m).val = k := rfl
      have hpos : friRoundPosIdx params ⟨k, hkm⟩ s =
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ := by
        apply Fin.ext
        exact hs
      have hneg : friRoundNegIdx params ⟨k, hkm⟩ s =
          ⟨j.val + N, by
            have hle : 2 ^ (params.d - k) ≤ 2 ^ params.d :=
              Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
            omega⟩ := by
        apply Fin.ext
        simpa only [friRoundNegIdx, N] using congrArg (· + N) hs
      have hposfin : friRoundPosFin params ⟨k, hkm⟩ s =
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (by omega))⟩ := by
        apply Fin.ext
        exact hs
      have hfold_eq :
          fold2Fiber
            (prefOracle pref k (friRoundPosIdx params ⟨k, hkm⟩ s))
            (prefOracle pref k (friRoundNegIdx params ⟨k, hkm⟩ s))
            (params.eval k (friRoundPosFin params ⟨k, hkm⟩ s))
            (prefFoldScalar pref k) =
          friTargetWord params stmt pref (k + 1) hi j := by
        rw [hpos, hneg, hposfin]
        rfl
      have hrhs_eq :
          prefOracle pref (k + 1) (friRoundPosIdx params ⟨k, hkm⟩ s) =
            restrictOracle (i := k + 1) (prefOracle pref (k + 1)) j := by
        rw [hpos]
        rfl
      simp only [friPrefixPasses]
      constructor
      · rintro ⟨hbind, hall⟩
        refine ⟨⟨hbind, fun r hr => hall r (Nat.lt_succ_of_lt hr)⟩, ?_⟩
        have hlast := hall ⟨k, hkm⟩ (Nat.lt_succ_self k)
        rw [hfold_eq, hrhs_eq] at hlast
        exact hlast.symm
      · rintro ⟨⟨hbind, hall⟩, hcur⟩
        refine ⟨hbind, fun r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
        · exact hall r hlt
        · have hr_eq : r = ⟨k, hkm⟩ := Fin.ext heq
          subst hr_eq
          rw [hfold_eq, hrhs_eq]
          exact hcur.symm
    have hpre_split :
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % N = j.val ∧ friPrefixPasses params stmt pref k s).card =
        friPreWeight params stmt pref (k + 1) hi j := by
      let S₀ := Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % (2 ^ (params.d - k)) = j.val ∧ friPrefixPasses params stmt pref k s
      let S₁ := Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % (2 ^ (params.d - k)) = j.val + N ∧ friPrefixPasses params stmt pref k s
      have hdisj : Disjoint S₀ S₁ := by
        rw [Finset.disjoint_left]
        intro s hs₀ hs₁
        have h0 := (Finset.mem_filter.mp hs₀).2.1
        have h1 := (Finset.mem_filter.mp hs₁).2.1
        have hNpos : 0 < N := Nat.pow_pos (by omega)
        omega
      have hunion :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friPrefixPasses params stmt pref k s) = S₀ ∪ S₁ := by
        ext s
        simp only [S₀, S₁, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hsplit]
        rw [mod_eq_iff_mod_two_mul_eq j.isLt, or_and_right]
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      have h0 : S₀.card = friOracleFilterWeight params stmt pref k hkm.le (prefOracle pref k)
          (reindexDouble hkd ⟨j.val, by omega⟩) :=
        ih hkm.le (reindexDouble hkd ⟨j.val, by omega⟩)
      have h1 : S₁.card = friOracleFilterWeight params stmt pref k hkm.le (prefOracle pref k)
          (reindexDouble hkd ⟨j.val + N, by omega⟩) :=
        ih hkm.le (reindexDouble hkd ⟨j.val + N, by omega⟩)
      rw [h0, h1]
      rfl
    by_cases hmatch :
        restrictOracle (i := k + 1) (prefOracle pref (k + 1)) j =
          friTargetWord params stmt pref (k + 1) hi j
    · have hfilt_eq :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friPrefixPasses params stmt pref (k + 1) s) =
          Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friPrefixPasses params stmt pref k s := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hs, hp⟩
          exact ⟨hs, ((hstep_eq s hs).mp hp).1⟩
        · rintro ⟨hs, hp⟩
          exact ⟨hs, (hstep_eq s hs).mpr ⟨hp, hmatch⟩⟩
      rw [hfilt_eq, hpre_split]
      simp only [friOracleFilterWeight, hmatch, ↓reduceIte]
    · have hempty :
          (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
            s.val % N = j.val ∧ friPrefixPasses params stmt pref (k + 1) s) = ∅ := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro hs hp
        exact hmatch ((hstep_eq s hs).mp hp).2
      rw [hempty, Finset.card_empty]
      simp only [friOracleFilterWeight, hmatch, ↓reduceIte]

/-- **Final query-acceptance counting bound**: for a length-`m` prefix `pref` and any final oracle
`πFinal`, the number of starting indices `s : Fin (2 ^ d)` satisfying `friFinalPasses` equals the
filtered weighted agreement of `πFinal` with `friFinalCodeword params πFinal`, and is therefore at
most the pre-filter weighted agreement of `friTargetWord ... m` with `friFinalCodeword`. -/
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
  let c₀ : FRIChal F params.d params.q := ⟨0, fun _ => ⟨0, Nat.pow_pos (by omega)⟩⟩
  let pref' := pref ++ [(πFinal, c₀)]
  let S := Finset.univ.filter fun s : Fin (2 ^ params.d) =>
    friFinalPasses params stmt pref πFinal s
  have hcard_eq :
      S.card =
        ∑ j : Fin (2 ^ (params.d - params.m)),
          (S.filter fun s => friFinalFin params s = j).card := by
    exact Finset.card_eq_sum_card_fiberwise fun s _ => Finset.mem_univ _
  have hfiber :
      ∀ j : Fin (2 ^ (params.d - params.m)),
        (S.filter fun s => friFinalFin params s = j).card =
          if restrictOracle (i := params.m) πFinal j = friFinalCodeword params πFinal j then
            friOracleFilterWeight params stmt pref params.m le_rfl πFinal j
          else 0 := by
    intro j
    have hbase := card_filter_friPrefixPasses_eq params stmt pref' params.m le_rfl j
    have hπm : prefOracle (pref ++ [(πFinal, c₀)]) params.m = πFinal := by
      simp only [← hlen, prefOracle_append_self]
    have htarg : friTargetWord params stmt pref' params.m le_rfl =
        friTargetWord params stmt pref params.m le_rfl :=
      friTargetWord_append params stmt pref [(πFinal, c₀)] le_rfl (by omega)
    have hwt : friPreWeight params stmt pref' params.m le_rfl =
        friPreWeight params stmt pref params.m le_rfl :=
      friPreWeight_append params stmt pref [(πFinal, c₀)] le_rfl (by omega)
    have hfw :
        friOracleFilterWeight params stmt pref' params.m le_rfl (prefOracle pref' params.m) j =
          friOracleFilterWeight params stmt pref params.m le_rfl πFinal j := by
      simp only [friOracleFilterWeight, pref', hπm, htarg, hwt]
    rw [hfw] at hbase
    by_cases hok : restrictOracle (i := params.m) πFinal j = friFinalCodeword params πFinal j
    · simp only [hok, ↓reduceIte]
      rw [← hbase]
      refine congrArg Finset.card ?_
      ext s
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        ← friTranscriptSingleAccepts_append_iff params stmt pref hlen πFinal c₀ s,
        friTranscriptSingleAccepts]
      constructor
      · rintro ⟨⟨hpref, _⟩, hfin⟩
        exact ⟨congrArg (Fin.val (n := 2 ^ (params.d - params.m))) hfin, hpref⟩
      · rintro ⟨hmod, hpref⟩
        have hfin : friFinalFin params s = j := Fin.ext hmod
        refine ⟨⟨hpref, ?_⟩, hfin⟩
        have hidx : friFinalIdx params s =
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
      have hidx : friFinalIdx params s =
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ :=
        Fin.ext (congrArg (Fin.val (n := 2 ^ (params.d - params.m))) hfin)
      have heq := hpass.2.2
      rw [hfin, hidx] at heq
      exact hok heq
  rw [hcard_eq]
  calc ∑ j : Fin (2 ^ (params.d - params.m)), (S.filter fun s => friFinalFin params s = j).card
      = ∑ j : Fin (2 ^ (params.d - params.m)),
          (if restrictOracle (i := params.m) πFinal j = friFinalCodeword params πFinal j then
            friOracleFilterWeight params stmt pref params.m le_rfl πFinal j
          else 0) := Finset.sum_congr rfl fun j _ => hfiber j
    _ = ∑ j ∈ Finset.univ.filter (fun j =>
          restrictOracle (i := params.m) πFinal j = friFinalCodeword params πFinal j),
          friOracleFilterWeight params stmt pref params.m le_rfl πFinal j := by
        rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j =>
          friTargetWord params stmt pref params.m le_rfl j = friFinalCodeword params πFinal j),
          friPreWeight params stmt pref params.m le_rfl j :=
        sum_agree_friOracleFilterWeight_le params stmt pref params.m le_rfl πFinal
          (friFinalCodeword params πFinal)

end StartingPointCounting

section RoundByRoundSoundness

variable {F : Type} [Field F]

/-- Commit-round doomed predicate at round `i ≤ m`: no codeword in `params.rsCode i` achieves
`friPreWeight`-weighted agreement `> B` with `friTargetWord`. -/
@[expose] def friCommitDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) : Prop :=
  ∀ c ∈ params.rsCode i,
    (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j) ≤ B

private theorem friCommitDoomed_congr_round [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i₁ i₂ : ℕ} (h : i₁ = i₂) (hi₁ : i₁ ≤ params.m) (hi₂ : i₂ ≤ params.m) :
    friCommitDoomed params B stmt pref i₁ hi₁ ↔ friCommitDoomed params B stmt pref i₂ hi₂ := by
  subst h
  rfl

/-- **FRI round-by-round doomed-state predicate**:
* For prefixes of length `i ≤ m`, `friCommitDoomed` holds at round `i`.
* For complete transcripts of length `m + 1`, at least one of the `q` queried starting positions
  fails `friTranscriptSingleAccepts`.
* For unreachable lengths `> m + 1`, holds trivially (`True`). -/
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

/-- **FRI round-by-round good-step predicate**: for `pref.length ≤ m`, extending `pref` by
`(π, c)` preserves `friDoomed`; for unreachable lengths `> m`, holds trivially (`True`) so the
escape event `{c | ¬ friGoodStep ... c}` is empty. -/
@[expose] def friGoodStep [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) : Prop :=
  if pref.length ≤ params.m then
    friDoomed params B stmt (pref ++ [(π, c)])
  else
    True

/-- **Unconditional round-by-round soundness invariant for `friIOP`**: for every distance threshold
`e : ℕ`, `friIOP params` satisfies `IOPRoundByRoundSoundness` with respect to
`params.proximityLang e`, `friDoomed params (2 ^ params.d - e - 1)`, and
`friGoodStep params (2 ^ params.d - e - 1)`. -/
theorem friIOP_rbrSound [DecidableEq F] (params : FRIParams F) (e : ℕ) :
    IOPRoundByRoundSoundness (friIOP params) (params.proximityLang e)
      (friDoomed params (2 ^ params.d - e - 1))
      (friGoodStep params (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot := by
    simp only [friDoomed, List.length_nil, Nat.zero_le, ↓reduceDIte, friCommitDoomed,
      friTargetWord, friPreWeight, restrictOracle, Nat.sub_zero, Fin.eta, Finset.sum_const,
      smul_eq_mul, mul_one]
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
    · simpa only [friGoodStep, h, ↓reduceIte] using hgood
    · have hgt : ¬ (pref ++ [(π, c)]).length ≤ params.m := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hne : (pref ++ [(π, c)]).length ≠ params.m + 1 := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [friDoomed, hgt, ↓reduceDIte, hne, ↓reduceIte]
  reject_of_doomed stmt oracles chals hdoomed := by
    set pref := List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)
    have hlen : pref.length = params.m + 1 := by simp [pref]
    have hnotle : ¬ pref.length ≤ params.m := by omega
    simp only [friDoomed, hnotle, ↓reduceDIte] at hdoomed
    simp only [hlen, ↓reduceIte] at hdoomed
    rw [prefFinalQueryIdxs_ofFn params oracles chals] at hdoomed
    obtain ⟨a, ha⟩ := hdoomed
    cases hacc : iopVerify (friIOP params) stmt chals oracles
    · rfl
    · exfalso
      have hall := (iopVerify_friIOP_eq_true_iff params stmt chals oracles).mp hacc a
      exact ha ((friTranscriptSingleAccepts_ofFn_iff params stmt oracles chals _).mpr hall)

omit [Field F] in
/-- Cardinality of `FRIChal` elements whose `foldScalar` lies in `S : Finset F`. -/
private theorem card_filter_foldScalar_mem [Fintype F] [DecidableEq F] {d q : ℕ}
    (S : Finset F) :
    (Finset.univ.filter fun c : FRIChal F d q => c.foldScalar ∈ S).card =
      S.card * (2 ^ d) ^ q := by
  let e : {c : FRIChal F d q // c.foldScalar ∈ S} ≃
      {z : F // z ∈ S} × (Fin q → Fin (2 ^ d)) :=
    { toFun := fun ⟨c, hc⟩ => (⟨c.foldScalar, hc⟩, c.queryIdxs)
      invFun := fun ⟨⟨z, hz⟩, qs⟩ => ⟨⟨z, qs⟩, hz⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  calc (Finset.univ.filter fun c : FRIChal F d q => c.foldScalar ∈ S).card
      = Fintype.card {c : FRIChal F d q // c.foldScalar ∈ S} := (Fintype.card_subtype _).symm
    _ = Fintype.card ({z : F // z ∈ S} × (Fin q → Fin (2 ^ d))) := Fintype.card_congr e
    _ = S.card * (2 ^ d) ^ q := by
        simp [Fintype.card_prod, Fintype.card_coe]

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

/-- **Unconditional query-round escape bound**: when `pref.length = m` and `pref` is doomed at
threshold `B`, the probability over a uniform `FRIChal` that all `q` query repetitions pass is at
most `(B / 2 ^ d) ^ q`. -/
theorem friQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  classical
  have hcommit : friCommitDoomed params B stmt pref params.m le_rfl := by
    have hle : pref.length ≤ params.m := hlen.le
    simp only [friDoomed, hle, ↓reduceDIte] at hdoomed
    exact (friCommitDoomed_congr_round params B stmt pref hlen hle le_rfl).mp hdoomed
  let goodS : Finset (Fin (2 ^ params.d)) :=
    Finset.univ.filter fun s => friFinalPasses params stmt pref π s
  have hgoodS_card : goodS.card ≤ B :=
    (card_filter_friFinalPasses_le params stmt pref hlen π).trans
      (hcommit (friFinalCodeword params π) (friFinalCodeword_mem_rsCode params π))
  have hbad_eq :
      {c : FRIChal F params.d params.q | ¬ friGoodStep params B stmt pref π c} =
      {c : FRIChal F params.d params.q | ∀ a : Fin params.q, c.queryIdxs a ∈ goodS} := by
    ext c
    have hle : pref.length ≤ params.m := hlen.le
    have hlen' : (pref ++ [(π, c)]).length = params.m + 1 := by
      simp [List.length_append, hlen]
    have hnotle' : ¬ (pref ++ [(π, c)]).length ≤ params.m := by omega
    simp only [Set.mem_ofPred_eq, friGoodStep, hle, ↓reduceIte, friDoomed, hnotle', ↓reduceDIte]
    simp only [hlen', ↓reduceIte, prefFinalQueryIdxs_append_self params pref hlen π c, not_exists,
      not_not, friTranscriptSingleAccepts_append_iff params stmt pref hlen π c, goodS,
      Finset.mem_filter, Finset.mem_univ, true_and]
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

/-- **Polymorphic weighted line proximity-gap contract** for all `m` FRI folding rounds at
agreement threshold `B` and bad-scalar budget `B_commit`.

Discharged both by unique-decoding proximity gaps (via `weightedLineGapBound_of_uniqueLineGap` with
sharp `B_commit = 2 ^ (d - 1)`) and by Johnson-regime weighted correlated agreement
([BenSassonCarmonIshaiKoppartySaraf2020], Section 7). -/
@[expose] def WeightedLineGapBound [DecidableEq F] (params : FRIParams F)
    (B B_commit : ℕ) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
    (∀ j, W j ≤ 2 ^ (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
      (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
      ∀ Z : Finset F,
        (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j) →
        Z.card ≤ B_commit

/-- **Conditional step (commit-round escape bound assuming `WeightedLineGapBound`)**: when
`pref.length < m` and `pref` is doomed at threshold `B`, the probability over a uniform `FRIChal`
that the folded target escapes to `> B` weighted agreement with `params.rsCode (pref.length + 1)`
is at most `B_commit / Fintype.card F`. This does not discharge `WeightedLineGapBound` itself. -/
theorem friCommitRound_escape_le_of_weightedLineGap [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B B_commit : ℕ}
    (hgap : WeightedLineGapBound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  let i : ℕ := pref.length
  have hle : pref.length ≤ params.m := hpm.le
  have hjd : i < params.d := lt_of_lt_of_le hpm params.hm
  have hcommit : friCommitDoomed params B stmt pref i hle := by
    simpa only [friDoomed, hle, ↓reduceDIte] using hdoomed
  let f : Fin (2 * 2 ^ (params.d - (i + 1))) → F :=
    fun idx => restrictOracle (i := i) π (reindexDouble hjd idx)
  let u₀ := fold2Even f
  let u₁ := fold2Odd (params.g ^ (2 ^ i)) (params.ω ^ (2 ^ i)) f
  let W_next := friNextWeight params stmt pref i hpm π
  have hno_corr :
      ∀ v₀ ∈ params.rsCode (i + 1), ∀ v₁ ∈ params.rsCode (i + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W_next j) ≤ B := by
    intro v₀ hv₀ v₁ hv₁
    let S := Finset.univ.filter fun j : Fin (2 ^ (params.d - (i + 1))) =>
      u₀ j = v₀ j ∧ u₁ j = v₁ j
    have hgpow : (params.g ^ (2 ^ i)) ^ 2 = params.g ^ (2 ^ (i + 1)) := by
      rw [← pow_mul, ← pow_succ]
    have hωpow : (params.ω ^ (2 ^ i)) ^ 2 = params.ω ^ (2 ^ (i + 1)) := by
      rw [← pow_mul, ← pow_succ]
    have hsplit : 2 ^ (params.d - i) = 2 * 2 ^ (params.d - (i + 1)) :=
      params.domainSize_eq_two_mul_succ hjd
    have hdim : params.dim i = 2 * params.dim (i + 1) := params.dim_eq_two_mul_succ hpm
    have hωi : IsPrimitiveRoot (params.ω ^ (2 ^ i)) (2 * 2 ^ (params.d - (i + 1))) :=
      hsplit ▸ isPrimitiveRoot_pow_two_pow params.hω hjd.le
    have hv₀' : v₀ ∈ reedSolomon
        (cosetPoint ((params.g ^ (2 ^ i)) ^ 2) ((params.ω ^ (2 ^ i)) ^ 2)
          (2 ^ (params.d - (i + 1)))) (params.dim (i + 1)) := by
      simpa only [FRIParams.rsCode, FRIParams.eval, cosetEval, hgpow, hωpow] using hv₀
    have hv₁' : v₁ ∈ reedSolomon
        (cosetPoint ((params.g ^ (2 ^ i)) ^ 2) ((params.ω ^ (2 ^ i)) ^ 2)
          (2 ^ (params.d - (i + 1)))) (params.dim (i + 1)) := by
      simpa only [FRIParams.rsCode, FRIParams.eval, cosetEval, hgpow, hωpow] using hv₁
    let W_filt : Fin (2 * 2 ^ (params.d - (i + 1))) → ℕ :=
      fun idx => friOracleFilterWeight params stmt pref i hle π (reindexDouble hjd idx)
    obtain ⟨c, hc_rs, hc_sum⟩ := exists_mem_reedSolomon_weighted_agree_lift_two
      (pow_ne_zero _ params.hg) params.h2 (Nat.pow_pos (by omega)) hωi f hv₀' hv₁' W_filt
    let c' : Fin (2 ^ (params.d - i)) → F := fun y => c ((reindexDoubleEquiv hjd).symm y)
    have hc'_rs : c' ∈ params.rsCode i := by
      obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp hc_rs
      refine mem_reedSolomon.mpr ⟨p, hdim.symm ▸ hp, ?_⟩
      ext y
      have hval := congrFun hpeq ((reindexDoubleEquiv hjd).symm y)
      exact hval
    have hsum_eq :
        (∑ idx ∈ Finset.univ.filter (fun idx => f idx = c idx), W_filt idx) =
        ∑ y ∈ Finset.univ.filter (fun y => restrictOracle (i := i) π y = c' y),
          friOracleFilterWeight params stmt pref i hle π y := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine (Finset.sum_congr rfl fun idx _ => ?_).trans
        (Equiv.sum_comp (reindexDoubleEquiv hjd)
          (fun y => if restrictOracle (i := i) π y = c' y then
            friOracleFilterWeight params stmt pref i hle π y else 0))
      simp only [f, c', W_filt, reindexDoubleEquiv]
      rfl
    calc ∑ j ∈ S, W_next j
        ≤ ∑ idx ∈ Finset.univ.filter (fun idx => f idx = c idx), W_filt idx := hc_sum
      _ = ∑ y ∈ Finset.univ.filter (fun y => restrictOracle (i := i) π y = c' y),
            friOracleFilterWeight params stmt pref i hle π y := hsum_eq
      _ ≤ ∑ y ∈ Finset.univ.filter (fun y => friTargetWord params stmt pref i hle y = c' y),
            friPreWeight params stmt pref i hle y :=
          sum_agree_friOracleFilterWeight_le params stmt pref i hle π c'
      _ ≤ B := hcommit c' hc'_rs
  let _ : DecidablePred (fun z : F =>
      ∃ v ∈ params.rsCode (i + 1),
        B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W_next j) :=
    Classical.decPred _
  let badZ : Finset F :=
    Finset.univ.filter fun z : F =>
      ∃ v ∈ params.rsCode (i + 1),
        B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W_next j
  have hbadZ_card : badZ.card ≤ B_commit :=
    hgap ⟨i, hpm⟩ W_next (friNextWeight_le params stmt pref i hpm π)
      (sum_friNextWeight_le params stmt pref i hpm π) u₀ u₁ hno_corr badZ
      (fun z hz => (Finset.mem_filter.mp hz).2)
  have hbad_eq :
      {c : FRIChal F params.d params.q | ¬ friGoodStep params B stmt pref π c} =
      {c : FRIChal F params.d params.q | c.foldScalar ∈ badZ} := by
    ext c
    have hlen' : (pref ++ [(π, c)]).length = i + 1 := by simp [i, List.length_append]
    have hle' : (pref ++ [(π, c)]).length ≤ params.m := by omega
    simp only [Set.mem_ofPred_eq, friGoodStep, hle, ↓reduceIte, friDoomed, hle', ↓reduceDIte]
    rw [friCommitDoomed_congr_round params B stmt (pref ++ [(π, c)]) hlen' hle' hpm]
    simp only [friCommitDoomed, i, friTargetWord_append_step params stmt pref hpm π c,
      friPreWeight_append_step params stmt pref hpm π c, fold2_eq_line, not_forall, not_le,
      exists_prop, badZ, W_next, u₀, u₁, f, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hbad_eq]
  have hF_pos : 0 < Fintype.card F := Fintype.card_pos
  have hcard_bound :
      Fintype.card F *
        (Finset.univ.filter fun c : FRIChal F params.d params.q => c.foldScalar ∈ badZ).card ≤
      B_commit * Fintype.card (FRIChal F params.d params.q) := by
    rw [card_filter_foldScalar_mem badZ, card_friChal]
    calc Fintype.card F * (badZ.card * (2 ^ params.d) ^ params.q)
        = badZ.card * (Fintype.card F * (2 ^ params.d) ^ params.q) := by ring
      _ ≤ B_commit * (Fintype.card F * (2 ^ params.d) ^ params.q) :=
          Nat.mul_le_mul_right _ hbadZ_card
  exact Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
    (α := FRIChal F params.d params.q)
    (P := fun c => c.foldScalar ∈ badZ) hF_pos hcard_bound

/-- Uniform per-round escape error for FRI: the maximum of the commit-round error
`B_commit / |F|` and the batched query-round error `((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friRBRError [Fintype F] (params : FRIParams F)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  max ((B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    ((((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q)

/-- **Conditional step (uniform round-by-round escape bound assuming `WeightedLineGapBound`)**:
across ALL transcript prefixes `pref` (commit rounds `pref.length < m`, query round
`pref.length = m`, and unreachable lengths `pref.length > m`), the per-round escape probability is
at most `friRBRError params e B_commit`. Discharging `WeightedLineGapBound` is left to the caller.
-/
theorem friRBREscape_of_weightedLineGap [Fintype F] [DecidableEq F] (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRBRError params e B_commit := by
  intro stmt _ pref π hdoomed
  by_cases hlt : pref.length < params.m
  · exact (friCommitRound_escape_le_of_weightedLineGap params hgap stmt pref hlt π hdoomed).trans
      (le_max_left _ _)
  · by_cases heq : pref.length = params.m
    · exact (friQueryRound_escape_le params (2 ^ params.d - e - 1) stmt pref heq π hdoomed).trans
        (le_max_right _ _)
    · have hgt : ¬ pref.length ≤ params.m := by omega
      have hempty :
          {c : FRIChal F params.d params.q |
            ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} = ∅ := by
        ext c
        simp only [Set.mem_ofPred_eq, friGoodStep, hgt, ↓reduceIte, not_true_eq_false,
          Set.mem_empty_iff_false]
      rw [hempty]
      exact (MeasureTheory.OuterMeasure.empty _).trans_le zero_le

end RoundByRoundSoundness

section UniqueDecodingUpgrade

variable {F : Type} [Field F]

/-- Fiber-size product identity `2 ^ (i + 1) * 2 ^ (d - (i + 1)) = 2 ^ d` for a folding round
`i : Fin params.m`. -/
theorem FRIParams.fiber_mul_domainSize (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d := by
  have hle : i.val + 1 ≤ params.d := Nat.le_trans i.isLt params.hm
  rw [← pow_add, Nat.add_sub_of_le hle]

/-- Round-dimension scaling identity `2 ^ (i + 1) * params.dim (i + 1) = params.dim 0` for a
folding round `i : Fin params.m`. -/
theorem FRIParams.fiber_mul_dim (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * params.dim (i.val + 1) = params.dim 0 := by
  have hle : i.val + 1 ≤ params.m := i.isLt
  simp only [FRIParams.dim, Nat.sub_zero]
  calc 2 ^ (i.val + 1) * (params.kFinal * 2 ^ (params.m - (i.val + 1)))
      = params.kFinal * (2 ^ (i.val + 1) * 2 ^ (params.m - (i.val + 1))) := by ring
    _ = params.kFinal * 2 ^ params.m := by rw [← pow_add, Nat.add_sub_of_le hle]

/-- Every round Reed–Solomon dimension `params.dim r` is at least `1`. -/
theorem FRIParams.one_le_dim (params : FRIParams F) (r : ℕ) : 1 ≤ params.dim r := by
  simp only [FRIParams.dim]
  exact Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Transport the initial unique-decoding bound `2 * e + params.dim 0 ≤ 2 ^ params.d` to the
scaled round-`(i + 1)` unique-decoding bound
`2 * (e / 2 ^ (i + 1)) + params.dim (i + 1) ≤ 2 ^ (params.d - (i + 1))`. -/
theorem FRIParams.two_mul_div_add_dim_le (params : FRIParams F) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) (i : Fin params.m) :
    2 * (e / 2 ^ (i.val + 1)) + params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) := by
  have hM_pos : 0 < 2 ^ (i.val + 1) := Nat.pow_pos (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hM_pos
  calc 2 ^ (i.val + 1) * (2 * (e / 2 ^ (i.val + 1)) + params.dim (i.val + 1))
      = 2 * (2 ^ (i.val + 1) * (e / 2 ^ (i.val + 1))) +
          2 ^ (i.val + 1) * params.dim (i.val + 1) := by ring
    _ ≤ 2 * e + params.dim 0 := by
        rw [params.fiber_mul_dim i]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_div_le e _)) _
    _ ≤ 2 ^ params.d := huniq
    _ = 2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) := (params.fiber_mul_domainSize i).symm

/-- Unweighted line proximity-gap hypothesis across all `m` FRI folding rounds at unique-decoding
radii `e / 2 ^ (i + 1)` (matching [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 4.1). -/
@[expose] def UniqueLineGapHypothesis [DecidableEq F] (params : FRIParams F) (e : ℕ) : Prop :=
  ∀ (i : Fin params.m) (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F) (Z : Finset F),
    2 ^ (params.d - (i.val + 1)) < Z.card →
    (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (u₀ + z • u₁) v ≤ e / 2 ^ (i.val + 1)) →
    ∃ D' : Finset (Fin (2 ^ (params.d - (i.val + 1)))),
      ∃ v₀ ∈ params.rsCode (i.val + 1), ∃ v₁ ∈ params.rsCode (i.val + 1),
        2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1) ≤ D'.card ∧
        ∀ j ∈ D', u₀ j = v₀ j ∧ u₁ j = v₁ j

/-- **Conditional step (unique-decoding weighted upgrade)**: inside the unique-decoding regime
`2 * e + params.dim 0 ≤ 2 ^ d`, assuming `UniqueLineGapHypothesis params e` yields
`WeightedLineGapBound` via `weighted_agree_of_line_many` with `B_commit = 2 ^ (d - 1)`. This does
not itself prove the unweighted line proximity-gap theorem. -/
theorem weightedLineGapBound_of_uniqueLineGap [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (2 ^ (params.d - 1)) := by
  intro i W hW_le _ u₀ u₁ hno_corr Z hZ_good
  let N := 2 ^ (params.d - (i.val + 1))
  let M := 2 ^ (i.val + 1)
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := params.fiber_mul_domainSize i
  have huniq_i : 2 * (e / M) + params.dim (i.val + 1) ≤ N :=
    params.two_mul_div_add_dim_le huniq i
  have he_lt : e < 2 ^ params.d := by
    have hdim_pos : 1 ≤ params.dim 0 := params.one_le_dim 0
    omega
  have hN_le : N ≤ 2 ^ (params.d - 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le _)) _)
  by_contra hgt
  have hZ_gt : N < Z.card := lt_of_le_of_lt hN_le (Nat.lt_of_not_ge hgt)
  have hdist_of_wt : ∀ (z : F) (v : Fin N → F),
      2 ^ params.d - e - 1 < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j →
      hammingDist (u₀ + z • u₁) v ≤ e / M := by
    intro z v hv_wt
    let S_eq := Finset.univ.filter fun j : Fin N => (u₀ + z • u₁) j = v j
    have hsum_le : (∑ j ∈ S_eq, W j) ≤ M * S_eq.card := by
      calc (∑ j ∈ S_eq, W j)
          ≤ ∑ _j ∈ S_eq, M := Finset.sum_le_sum fun j _ => hW_le j
        _ = S_eq.card * M := by simp
        _ = M * S_eq.card := mul_comm _ _
    have hpart : S_eq.card + hammingDist (u₀ + z • u₁) v = N := by
      rw [hammingDist]
      simpa only [S_eq, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
          (fun j => (u₀ + z • u₁) j = v j)
    have hmul : M * hammingDist (u₀ + z • u₁) v ≤ e := by
      have hsub : M * S_eq.card + M * hammingDist (u₀ + z • u₁) v = 2 ^ params.d := by
        rw [← mul_add, hpart, hMN]
      have hv_wt' : 2 ^ params.d - e - 1 < ∑ j ∈ S_eq, W j := hv_wt
      omega
    exact (Nat.le_div_iff_mul_le hM_pos).mpr (by simpa only [mul_comm] using hmul)
  have hZ_close :
      ∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1), hammingDist (u₀ + z • u₁) v ≤ e / M := by
    intro z hz
    obtain ⟨v, hv_rs, hv_wt⟩ := hZ_good z hz
    exact ⟨v, hv_rs, hdist_of_wt z v hv_wt⟩
  obtain ⟨D', v₀, hv₀, v₁, hv₁, hD'_card, hD'_agree⟩ := hgap i u₀ u₁ Z hZ_gt hZ_close
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω (by have := i.isLt; have := params.hm; omega)
  have hgood_line :
      ∀ z ∈ Z,
        2 ^ params.d - e - 1 <
          ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = (v₀ + z • v₁) j), W j := by
    intro z hz
    obtain ⟨v, hv_rs, hv_wt⟩ := hZ_good z hz
    have hdist_v : hammingDist (u₀ + z • u₁) v ≤ e / M := hdist_of_wt z v hv_wt
    have hline_rs : v₀ + z • v₁ ∈ params.rsCode (i.val + 1) :=
      (params.rsCode (i.val + 1)).add_mem hv₀ ((params.rsCode (i.val + 1)).smul_mem z hv₁)
    have hdist_line : hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e / M := by
      have hsub : D' ⊆ Finset.univ.filter (fun j : Fin N => (u₀ + z • u₁) j = (v₀ + z • v₁) j) := by
        intro j hj
        obtain ⟨h0, h1⟩ := hD'_agree j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, h0, h1]
      have hpart :
          (Finset.univ.filter fun j : Fin N => (u₀ + z • u₁) j = (v₀ + z • v₁) j).card +
            hammingDist (u₀ + z • u₁) (v₀ + z • v₁) = N := by
        rw [hammingDist]
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
            (fun j => (u₀ + z • u₁) j = (v₀ + z • v₁) j)
      have hcard_le := Finset.card_le_card hsub
      dsimp only [M, N] at hpart hcard_le ⊢
      omega
    have hveq : v = v₀ + z • v₁ :=
      eq_of_hammingDist_le_reedSolomon hα_inj (by simpa only [Fintype.card_fin] using huniq_i)
        hv_rs hline_rs hdist_v hdist_line
    rwa [← hveq]
  have hcorr := weighted_agree_of_line_many W u₀ u₁ v₀ v₁ Z (2 ^ params.d - e - 1)
    (by simpa only [Fintype.card_fin] using hZ_gt) hgood_line
  exact not_lt_of_ge (hno_corr v₀ hv₀ v₁ hv₁) hcorr

end UniqueDecodingUpgrade

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

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness assuming
`WeightedLineGapBound`)**: composes `friIOP_rbrSound` and `friRBREscape_of_weightedLineGap` with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonChiesaSpooner2016],
[BenSassonCarmonIshaiKoppartySaraf2020]); discharging `WeightedLineGapBound` is left to the caller.
-/
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
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friIOP_rbrSound params e)
    (friRBREscape_of_weightedLineGap params hgap) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness with separate prover/verifier
Merkle budgets assuming `WeightedLineGapBound`)**: bounds verifier Merkle cost via
`isCostBounded_bcsMTCost_friVerifyROM` (`q_V = params.proofOracleQueries * (L_path + 1)`) and
composes with `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`; discharging
`WeightedLineGapBound` is left to the caller. -/
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
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friIOP_rbrSound params e)
    (friRBREscape_of_weightedLineGap params hgap) hdec 0 σ hMT hFS
    (fun x prf hmem => isCostBounded_bcsMTCost_friVerifyROM params encSym x prf (hops x prf hmem))

/-- **Conditional step (unique-decoding BCS-FRI ROM soundness assuming `UniqueLineGapHypothesis`)**:
combines `weightedLineGapBound_of_uniqueLineGap` (`B_commit = 2 ^ (d - 1)`) with
`friBCS_romSoundness_bound_of_weightedLineGap`; discharging `UniqueLineGapHypothesis` is left to
the caller. -/
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
