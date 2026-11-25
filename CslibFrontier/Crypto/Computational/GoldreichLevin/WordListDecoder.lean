/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldreichLevin.ListDecoding
public import CslibFrontier.Crypto.Computational.GoldreichLevin.WordDecoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-time word and oracle-PPT list decoders for Goldreich–Levin (Goldreich 2008, Thm. 7.8)

This module lifts the finite simultaneous Goldreich–Levin list decoders of
`CslibFrontier.Crypto.Computational.GoldreichLevin.ListDecoding` (`decode` and `decodePruned`) to:
1. **Deterministic polynomial-time word algorithms** (`wordListDecode` and `wordListDecodePruned`)
   that output duplicate-free candidate lists `List (List Bool)` certified by
   `ComputableInPolyTime`, and
2. **Uniform strict oracle-PPT algorithms** (`oracleListDecode` and `oracleListDecodePruned`) on a
   structured unary parameter record `ListDecodeParams` (`encListDecodeParams`), certified by
   `IsOraclePPTOn` (which supplies explicit polynomial step, query-count, and query-length bounds
   via `IsOraclePPTOn.query_bounds`) and achieving simultaneous success probability at least `1 / 2`
   against **every** Boolean oracle `B : BitString n → Bool` with no efficiency assumption on `B`.

## Main definitions

* `Cslib.Crypto.GoldreichLevin.ListDecodeParams`,
  `Cslib.Crypto.GoldreichLevin.encListDecodeParams`: unary input record `(dimension, precision)`
  encoded via `enc_structure`.
* `Cslib.Crypto.GoldreichLevin.dedupWords`: duplicate erasure on `List (List Bool)` via
  `List.eraseDupsBy`.
* `Cslib.Crypto.GoldreichLevin.wordListDecode`: unpruned polynomial-time word list decoder.
* `Cslib.Crypto.GoldreichLevin.wordEmpiricalHits`,
  `Cslib.Crypto.GoldreichLevin.wordPruneCandidates`,
  `Cslib.Crypto.GoldreichLevin.wordListDecodePruned`: empirical-agreement pruning and the two-stage
  pruned polynomial-time word list decoder.
* `Cslib.Crypto.GoldreichLevin.queryBatch`,
  `Cslib.Crypto.GoldreichLevin.lookupReply`: batch oracle querying and transcript lookup.
* `Cslib.Crypto.GoldreichLevin.oracleListDecode`,
  `Cslib.Crypto.GoldreichLevin.oracleListDecodePruned`: uniform strict oracle-PPT list decoders.
* `Cslib.Crypto.GoldreichLevin.predictorOracle`,
  `Cslib.Crypto.GoldreichLevin.bitStringOracle`: stateless oracle handlers for arbitrary Boolean
  functions `predictor : List Bool → Bool` and `B : BitString n → Bool`.

## Main results

* `Cslib.Crypto.GoldreichLevin.polyTime_wordListDecode`,
  `Cslib.Crypto.GoldreichLevin.polyTime_wordListDecodePruned`: uniform deterministic polynomial-time
  certificates jointly in `dimension`, `precision`, and any captured polynomial-time predictor.
* `Cslib.Crypto.GoldreichLevin.toFinset_wordListDecode`,
  `Cslib.Crypto.GoldreichLevin.toFinset_wordListDecodePruned`: exact agreement with the finite
  candidate sets `candidates` and `prunedCandidates`.
* `Cslib.Crypto.GoldreichLevin.length_wordListDecode_le`,
  `Cslib.Crypto.GoldreichLevin.wordListDecode_simultaneous_success_ge_half`,
  `Cslib.Crypto.GoldreichLevin.wordListDecodePruned_simultaneous_success_ge_half`: duplicate-free
  list-length bounds and `1 / 2` simultaneous success bounds on uniform mask and sample bit tapes.
* `Cslib.Crypto.GoldreichLevin.isOraclePPTOn_oracleListDecode`,
  `Cslib.Crypto.GoldreichLevin.isOraclePPTOn_oracleListDecodePruned`,
  `Cslib.Crypto.GoldreichLevin.oracleListDecode_query_bounds`,
  `Cslib.Crypto.GoldreichLevin.oracleListDecodePruned_query_bounds`: strict oracle-PPT certificates
  and polynomial query budgets.
* `Cslib.Crypto.GoldreichLevin.oracleListDecode_bitStringOracle_simultaneous_success_ge_half`,
  `Cslib.Crypto.GoldreichLevin.oracleListDecodePruned_bitStringOracle_simultaneous_success_ge_half`:
  simultaneous list-decoding theorems for `oracleListDecode` and `oracleListDecodePruned` against
  every Boolean oracle `B : BitString p.dimension → Bool`.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Theorem 7.8
  (p. 254) and Exercise 7.6 (see also the March 2007 draft `r4.pdf` [Goldreich2007DraftR4],
  Theorem 7.8 and Exercise 7.6).
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability BitString Turing.MultiTapeTM MeasureTheory
open scoped ENNReal

/-! ### 1. Structured parameters and joint mask-enumeration certificates -/

/-- Input parameters for the uniform Goldreich–Levin list decoder:
* `dimension`: the bit-length `n` of secret strings `x : BitString n` (encoded in unary),
* `precision`: the correlation denominator `p` for agreement threshold `1 / 2 + 1 / p`
  (encoded in unary). -/
structure ListDecodeParams where
  /-- Bit-length `n` of secret strings `x : BitString n`. -/
  dimension : ℕ
  /-- Correlation denominator `p` (with target agreement `1 / 2 + 1 / p`). -/
  precision : ℕ
  deriving DecidableEq, Repr

/-- Canonical unary pair encoding of `ListDecodeParams`. -/
enc_structure encListDecodeParams : ListDecodeParams where
  dimension : encUnary,
  precision : encUnary

attribute [fun_prop] encListDecodeParams_dimension_polyTime
  encListDecodeParams_precision_polyTime
  encListDecodeParams_mk_polyTime
  encListDecodeParams_dimension_inO
  encListDecodeParams_precision_inO

/-- Computing `listMaskCount` is polynomial-time from unary `dimension` and `precision`. -/
@[fun_prop]
theorem polyTime_listMaskCount {α : Type} {input : α ↪ List Bool} {dimension precision : α → ℕ}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary) :
    ComputableInPolyTime (fun a => listMaskCount (dimension a) (precision a)) input encUnary := by
  unfold listMaskCount
  fun_prop

/-- Computing `pruneSampleCount` is polynomial-time from unary `dimension` and `precision`. -/
@[fun_prop]
theorem polyTime_pruneSampleCount {α : Type} {input : α ↪ List Bool} {dimension precision : α → ℕ}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary) :
    ComputableInPolyTime (fun a => pruneSampleCount (dimension a) (precision a))
      input encUnary := by
  unfold pruneSampleCount
  fun_prop

/-- The encoded size of `enumList (listMaskCount n precision)` is bounded by a fixed polynomial in
`L` whenever `n ≤ L` and `precision ≤ L`. -/
theorem enumList_listMaskCount_budget {n precision L : ℕ} (hn : n ≤ L) (hp : precision ≤ L) :
    2 ^ listMaskCount n precision * (2 * listMaskCount n precision + 1) ≤
      (16 * L ^ 5 + 2) * (16 * L ^ 5 + 3) := by
  have hpow4 : precision ^ 4 ≤ L ^ 4 := Nat.pow_le_pow_left hp 4
  have hmul : n * precision ^ 4 ≤ L ^ 5 := by
    calc
      n * precision ^ 4 ≤ L * L ^ 4 := Nat.mul_le_mul hn hpow4
      _ = L ^ 5 := by ring
  have hguess : 2 ^ listMaskCount n precision ≤ 16 * L ^ 5 + 2 := by
    have h := guessCount_listMaskCount_le n precision
    linarith
  have hmask : 2 * listMaskCount n precision + 1 ≤ 16 * L ^ 5 + 3 := by
    have h := listMaskCount_le n precision
    linarith
  exact Nat.mul_le_mul hguess hmask

/-- Enumerating all `2 ^ listMaskCount p.1 p.2` parity guesses is polynomial-time jointly in
`p : ℕ × ℕ` under `(encPair encUnary encUnary)`. -/
@[fun_prop]
theorem polyTime_enumList_listMaskCount_pair :
    ComputableInPolyTime (fun p : ℕ × ℕ => enumList (listMaskCount p.1 p.2))
      (encPair encUnary encUnary) (encList encBits) := by
  refine ComputableInPolyTime.bitsEnumList (by fun_prop)
    (size := fun L => (16 * L ^ 5 + 2) * (16 * L ^ 5 + 3)) (by fun_prop) ?_
  intro p
  have hn : p.1 ≤ (encPair encUnary encUnary p).length := by
    simp [encPair_apply, encUnary_apply]
    omega
  have hp : p.2 ≤ (encPair encUnary encUnary p).length := by
    simp [encPair_apply, encUnary_apply]
  exact enumList_listMaskCount_budget hn hp

private theorem comp_prod_eq {α β γ δ : Type*} (f : β → γ → δ) (g : α → β) (h : α → γ) :
    ((fun p : β × γ => f p.1 p.2) ∘ fun a => (g a, h a)) = fun a => f (g a) (h a) :=
  rfl

/-- Enumerating all `2 ^ listMaskCount (dimension a) (precision a)` parity guesses is
polynomial-time from any unary `dimension` and `precision`. -/
@[fun_prop]
theorem polyTime_enumList_listMaskCount {α : Type} {input : α ↪ List Bool}
    {dimension precision : α → ℕ}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary) :
    ComputableInPolyTime (fun a => enumList (listMaskCount (dimension a) (precision a)))
      input (encList encBits) := by
  rw [← comp_prod_eq (fun n p => enumList (listMaskCount n p)) dimension precision]
  exact polyTime_enumList_listMaskCount_pair.comp (hdimension.prod hprecision)

/-- Computing `nonzeroSelectors (listMaskCount (dimension a) (precision a))` is polynomial-time
from any unary `dimension` and `precision`. -/
@[fun_prop]
theorem polyTime_nonzeroSelectors_listMaskCount {α : Type} {input : α ↪ List Bool}
    {dimension precision : α → ℕ}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary) :
    ComputableInPolyTime (fun a => nonzeroSelectors (listMaskCount (dimension a) (precision a)))
      input (encList encBits) := by
  unfold nonzeroSelectors
  exact ComputableInPolyTime.filterWithInput
    (polyTime_enumList_listMaskCount hdimension hprecision) (by fun_prop)

/-! ### 2. Duplicate erasure on candidate word lists (`dedupWords`) -/

/-- Erase duplicate bit-lists from `words`, preserving first-occurrence order. -/
def dedupWords (words : List (List Bool)) : List (List Bool) :=
  words.eraseDupsBy (fun a b => decide (a = b))

/-- `dedupWords` is computable in polynomial time on framed word lists. -/
@[fun_prop]
theorem polyTime_dedupWords {α : Type} {input : α ↪ List Bool}
    {words : α → List (List Bool)}
    (hwords : ComputableInPolyTime words input (encList encBits)) :
    ComputableInPolyTime (fun a => dedupWords (words a)) input (encList encBits) := by
  unfold dedupWords
  exact ComputableInPolyTime.eraseDupsByWithInput hwords
    (.decide_eq' (ComputableInPolyTime.fst _ _).snd' (ComputableInPolyTime.snd _ _))

/-- `dedupWords` preserves list membership. -/
@[simp]
theorem mem_dedupWords {words : List (List Bool)} {w : List Bool} :
    w ∈ dedupWords words ↔ w ∈ words :=
  List.mem_eraseDupsBy_eq

/-- `dedupWords` produces a duplicate-free list. -/
theorem nodup_dedupWords (words : List (List Bool)) : (dedupWords words).Nodup :=
  List.nodup_eraseDupsBy_eq words

/-- `dedupWords` preserves `toFinset`. -/
@[simp]
theorem toFinset_dedupWords (words : List (List Bool)) :
    (dedupWords words).toFinset = words.toFinset := by
  ext w
  simp

/-- The length of `dedupWords words` equals `words.toFinset.card`. -/
theorem length_dedupWords_eq_card_toFinset (words : List (List Bool)) :
    (dedupWords words).length = words.toFinset.card := by
  rw [← toFinset_dedupWords, List.toFinset_card_of_nodup (nodup_dedupWords words)]

/-! ### 3. Deterministic polynomial-time word list decoders -/

/-- Unpruned polynomial-time Goldreich–Levin word list decoder: generate all `2 ^ listMaskCount`
majority-vote candidates from `masks` and erase duplicate candidate words. -/
def wordListDecode (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) : List (List Bool) :=
  let count := listMaskCount dimension precision
  dedupWords (wordCandidates predictor dimension (listRows count dimension masks) (enumList count))

/-- `wordListDecode` is computable in polynomial time jointly in `dimension`, `precision`, `masks`,
and any captured polynomial-time predictor. -/
@[fun_prop]
theorem polyTime_wordListDecode {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {dimension precision : α → ℕ} {masks : α → List Bool}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hmasks : ComputableInPolyTime masks input encBits) :
    ComputableInPolyTime
      (fun a => wordListDecode (predictor a) (dimension a) (precision a) (masks a))
      input (encList encBits) := by
  unfold wordListDecode
  apply polyTime_dedupWords
  exact polyTime_wordCandidates hpredictor hdimension
    (ComputableInPolyTime.bitsRowsWithInput
      (polyTime_listMaskCount hdimension hprecision) hdimension hmasks)
    (polyTime_enumList_listMaskCount hdimension hprecision)

/-- `wordListDecode` always returns a duplicate-free list of words. -/
theorem nodup_wordListDecode (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) :
    (wordListDecode predictor dimension precision masks).Nodup :=
  nodup_dedupWords _

/-- The finite set of words returned by `wordListDecode` is the `List.ofFn` image of the finite
candidate set `candidates`. -/
theorem toFinset_wordListDecode (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) :
    (wordListDecode predictor dimension precision masks).toFinset =
      (candidates (fun query => predictor (List.ofFn query))
        (block (ofList (listMaskCount dimension precision * dimension) masks))).image
          List.ofFn := by
  unfold wordListDecode
  rw [toFinset_dedupWords, listRows_eq_ofFn, wordCandidates_eq_map]
  ext w
  simp

/-- For `x : BitString n`, `List.ofFn x` belongs to `wordListDecode predictor n precision masks` if
and only if `x` belongs to `candidates`. -/
@[simp]
theorem mem_wordListDecode_ofFn_iff (predictor : List Bool → Bool) {n precision : ℕ}
    (masks : List Bool) (x : BitString n) :
    List.ofFn x ∈ wordListDecode predictor n precision masks ↔
      x ∈ candidates (fun query => predictor (List.ofFn query))
        (block (ofList (listMaskCount n precision * n) masks)) := by
  simp only [← List.mem_toFinset, toFinset_wordListDecode, Finset.mem_image, List.ofFn_inj,
    exists_eq_right]

/-- Every word in `wordListDecode predictor n precision masks` is `List.ofFn x` for some
`x ∈ candidates`. -/
theorem mem_wordListDecode_iff (predictor : List Bool → Bool) {n precision : ℕ}
    (masks : List Bool) (w : List Bool) :
    w ∈ wordListDecode predictor n precision masks ↔
      ∃ x ∈ candidates (fun query => predictor (List.ofFn query))
        (block (ofList (listMaskCount n precision * n) masks)), List.ofFn x = w := by
  rw [← List.mem_toFinset, toFinset_wordListDecode, Finset.mem_image]

/-- The length of `wordListDecode` equals the cardinality of the finite candidate set
`candidates`. -/
theorem length_wordListDecode_eq_card (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) :
    (wordListDecode predictor dimension precision masks).length =
      (candidates (fun query => predictor (List.ofFn query))
        (block (ofList (listMaskCount dimension precision * dimension) masks))).card := by
  rw [← List.toFinset_card_of_nodup (nodup_wordListDecode predictor dimension precision masks),
    toFinset_wordListDecode, Finset.card_image_of_injective _ List.ofFn_injective]

/-- Explicit polynomial list-length bound on `wordListDecode`: at most
`2 ^ listMaskCount dimension precision ≤ 16 * dimension * precision ^ 4 + 2` candidates. -/
theorem length_wordListDecode_le (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) :
    (wordListDecode predictor dimension precision masks).length ≤
      16 * dimension * precision ^ 4 + 2 := by
  rw [length_wordListDecode_eq_card]
  exact (card_candidates_le _ _).trans (guessCount_listMaskCount_le dimension precision)

/-- Uniform mask bits under `wordListDecode` induce the `List.ofFn`-image of the finite `decode`
distribution on `toFinset`. -/
theorem uniform_wordListDecode_toFinset (predictor : List Bool → Bool) (dimension precision : ℕ) :
    ((uniformList (listMaskCount dimension precision * dimension)).map
        (fun masks => (wordListDecode predictor dimension precision masks).toFinset)) =
      (decode (n := dimension) (fun query => predictor (List.ofFn query))
        (listMaskCount dimension precision)).map (fun s => s.image List.ofFn) := by
  rw [decode, ← uniformList_blocks]
  simp only [PMF.map_comp, Function.comp_def, toFinset_wordListDecode]

/-- **Simultaneous word list-decoding success (`ℝ≥0∞`)**: for `0 < precision`, sampling a uniform
mask bit tape and running `wordListDecode` outputs a list containing `List.ofFn x` for every
`(1 / 2 + 1 / precision)`-correlated `x : BitString n` with probability at least `1 / 2`. -/
theorem wordListDecode_simultaneous_success_ge_half (predictor : List Bool → Bool) (n precision : ℕ)
    (hprec : 0 < precision) :
    (1 / 2 : ℝ≥0∞) ≤
      ((uniformList (listMaskCount n precision * n)).map
          (wordListDecode predictor n precision)).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤
              agreement (fun query => predictor (List.ofFn query)) x →
              List.ofFn x ∈ L) ∧
          L.Nodup ∧
          L.length ≤ 16 * n * precision ^ 4 + 2} := by
  let pred : BitString n → Bool := fun query => predictor (List.ofFn query)
  have hbase := decode_listMaskCount_simultaneous_success_ge_half pred hprec
  rw [decode, ← uniformList_blocks, PMF.map_comp, PMF.toOuterMeasure_map_apply] at hbase
  rw [PMF.toOuterMeasure_map_apply]
  refine hbase.trans ((uniformList (listMaskCount n precision * n)).toOuterMeasure.mono ?_)
  intro masks hmasks
  exact ⟨fun x hx => (mem_wordListDecode_ofFn_iff predictor masks x).mpr (hmasks x hx),
    nodup_wordListDecode predictor n precision masks,
    length_wordListDecode_le predictor n precision masks⟩

/-- **Simultaneous word list-decoding success (`ℝ`)**: real-probability form of
`wordListDecode_simultaneous_success_ge_half`. -/
theorem wordListDecode_simultaneous_success_toReal_ge_half (predictor : List Bool → Bool)
    (n precision : ℕ) (hprec : 0 < precision) :
    1 / 2 ≤
      (((uniformList (listMaskCount n precision * n)).map
          (wordListDecode predictor n precision)).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤
              agreement (fun query => predictor (List.ofFn query)) x →
              List.ofFn x ∈ L) ∧
          L.Nodup ∧
          L.length ≤ 16 * n * precision ^ 4 + 2}).toReal := by
  simpa [one_div] using ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (wordListDecode_simultaneous_success_ge_half predictor n precision hprec)

/-- Count empirical hits of `candidate` against `predictor` over a list of sample rows. -/
def wordEmpiricalHits (predictor : List Bool → Bool) (sampleRows : List (List Bool))
    (candidate : List Bool) : ℕ :=
  sampleRows.countP (fun row => predictor row == listDot candidate row)

/-- `wordEmpiricalHits` is computable in polynomial time jointly in `sampleRows`, `candidate`, and
any captured polynomial-time predictor. -/
@[fun_prop]
theorem polyTime_wordEmpiricalHits {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {sampleRows : α → List (List Bool)}
    {candidate : α → List Bool}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hsampleRows : ComputableInPolyTime sampleRows input (encList encBits))
    (hcandidate : ComputableInPolyTime candidate input encBits) :
    ComputableInPolyTime
      (fun a => wordEmpiricalHits (predictor a) (sampleRows a) (candidate a))
      input encUnary := by
  unfold wordEmpiricalHits
  exact ComputableInPolyTime.countPWithInput hsampleRows
    (hpredictor.beq (.bitsListDot
      (hcandidate.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _)))

/-- On `List.ofFn` sample rows and `List.ofFn x`, `wordEmpiricalHits` agrees with
`empiricalHits`. -/
theorem wordEmpiricalHits_eq_empiricalHits {n m : ℕ} (predictor : List Bool → Bool)
    (samples : Fin m → BitString n) (x : BitString n) :
    wordEmpiricalHits predictor (List.ofFn (fun j => List.ofFn (samples j))) (List.ofFn x) =
      empiricalHits (fun query => predictor (List.ofFn query)) samples x := by
  have hnodup : (List.finRange m).Nodup := List.nodup_finRange m
  have huniv : (List.finRange m).toFinset = (Finset.univ : Finset (Fin m)) := by
    ext j
    simp
  rw [wordEmpiricalHits, List.countP_eq_length_filter,
    List.ofFn_eq_map (f := fun j => List.ofFn (samples j)), List.filter_map,
    List.length_map, ← List.toFinset_card_of_nodup (hnodup.filter _), List.toFinset_filter,
    huniv, empiricalHits]
  congr 1
  ext j
  simp [listDot_ofFn]

/-- Filter and deduplicate a candidate word list by empirical agreement threshold `num / den` on
`sampleRows`. -/
def wordPruneCandidates (predictor : List Bool → Bool) (num den : ℕ)
    (sampleRows candidates : List (List Bool)) : List (List Bool) :=
  dedupWords (candidates.filter (fun candidate =>
    decide (sampleRows.length * num ≤ den * wordEmpiricalHits predictor sampleRows candidate)))

/-- `wordPruneCandidates` is computable in polynomial time. -/
@[fun_prop]
theorem polyTime_wordPruneCandidates {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {num den : α → ℕ}
    {sampleRows candidates : α → List (List Bool)}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hnum : ComputableInPolyTime num input encUnary)
    (hden : ComputableInPolyTime den input encUnary)
    (hsampleRows : ComputableInPolyTime sampleRows input (encList encBits))
    (hcandidates : ComputableInPolyTime candidates input (encList encBits)) :
    ComputableInPolyTime
      (fun a => wordPruneCandidates (predictor a) (num a) (den a) (sampleRows a) (candidates a))
      input (encList encBits) := by
  unfold wordPruneCandidates
  refine polyTime_dedupWords (ComputableInPolyTime.filterWithInput hcandidates ?_)
  have h1 := ComputableInPolyTime.fst input encBits
  have hsr := hsampleRows.comp h1
  have hhits := polyTime_wordEmpiricalHits (input := encPair input encBits)
    (predictor := fun p => predictor p.1)
    (hpredictor.comp ((h1.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)))
    hsr (ComputableInPolyTime.snd _ _)
  exact .unary_le' (((ComputableInPolyTime.length_list encBits).comp hsr).unary_mul' (hnum.comp h1))
    ((hden.comp h1).unary_mul' hhits)

/-- Two-stage pruned polynomial-time Goldreich–Levin word list decoder: generate candidate words
from `masks` using `listMaskCount dimension precision` masks, then prune them on
`pruneSampleCount dimension precision` sample words from `samples` at threshold
`(2 * precision + 3) / (4 * precision)`. -/
def wordListDecodePruned (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks samples : List Bool) : List (List Bool) :=
  wordPruneCandidates predictor (2 * precision + 3) (4 * precision)
    (listRows (pruneSampleCount dimension precision) dimension samples)
    (wordListDecode predictor dimension precision masks)

/-- `wordListDecodePruned` is computable in polynomial time jointly in `dimension`, `precision`,
`masks`, `samples`, and any captured polynomial-time predictor. -/
@[fun_prop]
theorem polyTime_wordListDecodePruned {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {dimension precision : α → ℕ}
    {masks samples : α → List Bool}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hmasks : ComputableInPolyTime masks input encBits)
    (hsamples : ComputableInPolyTime samples input encBits) :
    ComputableInPolyTime
      (fun a => wordListDecodePruned (predictor a) (dimension a) (precision a)
        (masks a) (samples a))
      input (encList encBits) := by
  unfold wordListDecodePruned
  fun_prop

/-- `wordListDecodePruned` always returns a duplicate-free list of words. -/
theorem nodup_wordListDecodePruned (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks samples : List Bool) :
    (wordListDecodePruned predictor dimension precision masks samples).Nodup :=
  nodup_dedupWords _

/-- The finite set of words returned by `wordListDecodePruned` is the `List.ofFn` image of
`prunedCandidates`. -/
theorem toFinset_wordListDecodePruned (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks samples : List Bool) :
    (wordListDecodePruned predictor dimension precision masks samples).toFinset =
      (prunedCandidates (fun query => predictor (List.ofFn query))
        (2 * precision + 3) (4 * precision)
        (block (ofList (listMaskCount dimension precision * dimension) masks))
        (block (ofList (pruneSampleCount dimension precision * dimension) samples))).image
          List.ofFn := by
  unfold wordListDecodePruned wordPruneCandidates
  rw [toFinset_dedupWords, List.toFinset_filter, toFinset_wordListDecode, listRows_eq_ofFn]
  ext w
  simp only [Finset.mem_filter, Finset.mem_image, List.length_ofFn, mem_prunedCandidates]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hpass⟩
    rw [wordEmpiricalHits_eq_empiricalHits, decide_eq_true_eq] at hpass
    exact ⟨x, ⟨hx, hpass⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hpass⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [wordEmpiricalHits_eq_empiricalHits, decide_eq_true_eq]
    exact hpass

/-- For `x : BitString n`, `List.ofFn x` belongs to `wordListDecodePruned` if and only if `x`
belongs to `prunedCandidates`. -/
@[simp]
theorem mem_wordListDecodePruned_ofFn_iff (predictor : List Bool → Bool) {n precision : ℕ}
    (masks samples : List Bool) (x : BitString n) :
    List.ofFn x ∈ wordListDecodePruned predictor n precision masks samples ↔
      x ∈ prunedCandidates (fun query => predictor (List.ofFn query))
        (2 * precision + 3) (4 * precision)
        (block (ofList (listMaskCount n precision * n) masks))
        (block (ofList (pruneSampleCount n precision * n) samples)) := by
  simp only [← List.mem_toFinset, toFinset_wordListDecodePruned, Finset.mem_image, List.ofFn_inj,
    exists_eq_right]

/-- The length of `wordListDecodePruned` equals the cardinality of `prunedCandidates`. -/
theorem length_wordListDecodePruned_eq_card (predictor : List Bool → Bool)
    (dimension precision : ℕ) (masks samples : List Bool) :
    (wordListDecodePruned predictor dimension precision masks samples).length =
      (prunedCandidates (fun query => predictor (List.ofFn query))
        (2 * precision + 3) (4 * precision)
        (block (ofList (listMaskCount dimension precision * dimension) masks))
        (block (ofList (pruneSampleCount dimension precision * dimension) samples))).card := by
  rw [← List.toFinset_card_of_nodup
      (nodup_wordListDecodePruned predictor dimension precision masks samples),
    toFinset_wordListDecodePruned, Finset.card_image_of_injective _ List.ofFn_injective]

/-- **Pruned simultaneous word list-decoding success (`ℝ≥0∞`)**: for `0 < precision`, sampling
independent uniform mask and sample bit tapes and running `wordListDecodePruned` succeeds with
probability at least `1 / 2` in returning a duplicate-free list `L` that:
1. contains `List.ofFn x` for every `x : BitString n` with `1 / 2 + 1 / precision ≤ agreement`,
2. contains only `List.ofFn x` for `x : BitString n` with `1 / 2 + 1 / (2 * precision) ≤ agreement`,
3. has length at most `precision ^ 2`. -/
theorem wordListDecodePruned_simultaneous_success_ge_half (predictor : List Bool → Bool)
    (n precision : ℕ) (hprec : 0 < precision) :
    (1 / 2 : ℝ≥0∞) ≤
      ((uniformList (listMaskCount n precision * n)).bind (fun masks =>
        (uniformList (pruneSampleCount n precision * n)).map
          (wordListDecodePruned predictor n precision masks))).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤
              agreement (fun query => predictor (List.ofFn query)) x →
              List.ofFn x ∈ L) ∧
          (∀ x : BitString n,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (precision : ℝ)) ≤
                agreement (fun query => predictor (List.ofFn query)) x) ∧
          L.Nodup ∧
          L.length ≤ precision ^ 2} := by
  let pred : BitString n → Bool := fun query => predictor (List.ofFn query)
  let k := listMaskCount n precision
  let m := pruneSampleCount n precision
  let num := 2 * precision + 3
  let den := 4 * precision
  have hdecode :
      decodePruned pred k m num den =
        ((uniformList (k * n)).bind (fun masks =>
          (uniformList (m * n)).map (fun samples => (masks, samples)))).map
            (fun ms => prunedCandidates pred num den
              (block (ofList (k * n) ms.1)) (block (ofList (m * n) ms.2))) := by
    rw [decodePruned, ← uniformList_blocks, ← uniformList_blocks]
    simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hword :
      ((uniformList (k * n)).bind (fun masks =>
        (uniformList (m * n)).map (wordListDecodePruned predictor n precision masks))) =
        ((uniformList (k * n)).bind (fun masks =>
          (uniformList (m * n)).map (fun samples => (masks, samples)))).map
            (fun ms => wordListDecodePruned predictor n precision ms.1 ms.2) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hbase := decodePruned_simultaneous_success_ge_half pred hprec
  rw [hdecode, PMF.toOuterMeasure_map_apply] at hbase
  rw [hword, PMF.toOuterMeasure_map_apply]
  refine hbase.trans (((uniformList (k * n)).bind (fun masks =>
    (uniformList (m * n)).map (fun samples => (masks, samples)))).toOuterMeasure.mono ?_)
  rintro ⟨masks, samples⟩ ⟨h1, h2, h3⟩
  exact ⟨fun x hx => (mem_wordListDecodePruned_ofFn_iff predictor masks samples x).mpr (h1 x hx),
    fun x hx => h2 x ((mem_wordListDecodePruned_ofFn_iff predictor masks samples x).mp hx),
    nodup_wordListDecodePruned predictor n precision masks samples,
    (length_wordListDecodePruned_eq_card predictor n precision masks samples).trans_le h3⟩

/-! ### 4. Uniform strict oracle-PPT list decoders (`oracleListDecode`, `oracleListDecodePruned`) -/

/-- All oracle queries made during candidate generation on `(dimension, rows, selectors)`. -/
def candidateQueries (dimension : ℕ) (rows selectors : List (List Bool)) : List (List Bool) :=
  (listSingles dimension).flatMap (fun coordinate =>
    selectors.map (fun selector =>
      coordinate.zipWith Bool.xor (listXorSelected dimension selector rows)))

/-- `candidateQueries` is computable in polynomial time. -/
@[fun_prop]
theorem polyTime_candidateQueries {α : Type} {input : α ↪ List Bool}
    {dimension : α → ℕ} {rows selectors : α → List (List Bool)}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hrows : ComputableInPolyTime rows input (encList encBits))
    (hselectors : ComputableInPolyTime selectors input (encList encBits)) :
    ComputableInPolyTime
      (fun a => candidateQueries (dimension a) (rows a) (selectors a))
      input (encList encBits) := by
  unfold candidateQueries
  refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.bitsSingles.comp hdimension) ?_
  have h1 := ComputableInPolyTime.fst input encBits
  refine ComputableInPolyTime.mapWithInput (hselectors.comp h1) ?_
  have hp := ComputableInPolyTime.fst (encPair input encBits) encBits
  have ha := h1.comp hp
  exact (ComputableInPolyTime.bitsZipWith Bool.xor).comp
    (hp.snd'.prod (ComputableInPolyTime.bitsXorSelected.comp
      ((hdimension.comp ha).prod ((ComputableInPolyTime.snd _ _).prod (hrows.comp ha)))))

/-- All oracle queries made by `wordListDecode` on `(dimension, precision)` and mask tape
`masks`. -/
def listDecodeQueries (dimension precision : ℕ) (masks : List Bool) : List (List Bool) :=
  let count := listMaskCount dimension precision
  candidateQueries dimension (listRows count dimension masks) (nonzeroSelectors count)

/-- `listDecodeQueries` is computable in polynomial time. -/
@[fun_prop]
theorem polyTime_listDecodeQueries {α : Type} {input : α ↪ List Bool}
    {dimension precision : α → ℕ} {masks : α → List Bool}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hmasks : ComputableInPolyTime masks input encBits) :
    ComputableInPolyTime
      (fun a => listDecodeQueries (dimension a) (precision a) (masks a))
      input (encList encBits) := by
  unfold listDecodeQueries
  exact polyTime_candidateQueries hdimension
    (ComputableInPolyTime.bitsRowsWithInput
      (polyTime_listMaskCount hdimension hprecision) hdimension hmasks)
    (polyTime_nonzeroSelectors_listMaskCount hdimension hprecision)

/-- All oracle queries made by `wordListDecodePruned` on `(dimension, precision)`, mask tape
`masks`, and sample tape `samples`. -/
def listDecodePrunedQueries (dimension precision : ℕ) (masks samples : List Bool) :
    List (List Bool) :=
  listDecodeQueries dimension precision masks ++
    listRows (pruneSampleCount dimension precision) dimension samples

/-- `listDecodePrunedQueries` is computable in polynomial time. -/
@[fun_prop]
theorem polyTime_listDecodePrunedQueries {α : Type} {input : α ↪ List Bool}
    {dimension precision : α → ℕ} {masks samples : α → List Bool}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary)
    (hmasks : ComputableInPolyTime masks input encBits)
    (hsamples : ComputableInPolyTime samples input encBits) :
    ComputableInPolyTime
      (fun a => listDecodePrunedQueries (dimension a) (precision a) (masks a) (samples a))
      input (encList encBits) := by
  unfold listDecodePrunedQueries
  exact ComputableInPolyTime.listAppend'
    (polyTime_listDecodeQueries hdimension hprecision hmasks)
    (ComputableInPolyTime.bitsRowsWithInput
      (polyTime_pruneSampleCount hdimension hprecision) hdimension hsamples)

/-- Look up the Boolean reply for `query` in a `(queries, replies)` transcript table. -/
def lookupReply (queries : List (List Bool)) (replies : List Bool) (query : List Bool) : Bool :=
  replies.getD (queries.idxOf query) false

/-- `lookupReply` is computable in polynomial time. -/
@[fun_prop]
theorem polyTime_lookupReply {α : Type} {input : α ↪ List Bool}
    {queries : α → List (List Bool)} {replies query : α → List Bool}
    (hqueries : ComputableInPolyTime queries input (encList encBits))
    (hreplies : ComputableInPolyTime replies input encBits)
    (hquery : ComputableInPolyTime query input encBits) :
    ComputableInPolyTime (fun a => lookupReply (queries a) (replies a) (query a))
      input encBool := by
  unfold lookupReply
  have hbeq : (List.instBEq : BEq (List Bool)) = instBEqOfDecidableEq :=
    congrArg BEq.mk <| funext fun a => funext fun b =>
      Bool.eq_iff_iff.mpr ((beq_iff_eq (a := a) (b := b)).trans decide_eq_true_iff.symm)
  have hidx : ComputableInPolyTime (fun a => (queries a).idxOf (query a)) input encUnary := by
    rw [hbeq, ← comp_prod_eq (fun qs q => @List.idxOf (List Bool) instBEqOfDecidableEq q qs)
      queries query]
    exact (ComputableInPolyTime.idxOf encBits).comp (hqueries.prod hquery)
  exact ComputableInPolyTime.bitsGetDWithInput hreplies hidx false

/-- Looking up `query ∈ queries` in `(queries, queries.map predictor)` returns `predictor query`. -/
theorem lookupReply_map_of_mem (predictor : List Bool → Bool)
    {queries : List (List Bool)} {query : List Bool} (hq : query ∈ queries) :
    lookupReply queries (queries.map predictor) query = predictor query := by
  unfold lookupReply
  have hlt : queries.idxOf query < queries.length := List.idxOf_lt_length_of_mem hq
  have hlt' : queries.idxOf query < (queries.map predictor).length := by simp [hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some,
    List.getElem_map, List.getElem_idxOf hlt]

/-- `wordCandidate` depends on `predictor` only at queries in `candidateQueries`. -/
theorem wordCandidate_congr {predictor₁ predictor₂ : List Bool → Bool} (dimension : ℕ)
    (rows selectors : List (List Bool)) (guess : List Bool)
    (hagree : ∀ q ∈ candidateQueries dimension rows selectors, predictor₁ q = predictor₂ q) :
    wordCandidate predictor₁ dimension rows selectors guess =
      wordCandidate predictor₂ dimension rows selectors guess := by
  unfold wordCandidate
  refine List.map_congr_left fun coordinate hcoord => ?_
  congr 1
  refine List.map_congr_left fun selector hsel => ?_
  have hmem :
      coordinate.zipWith Bool.xor (listXorSelected dimension selector rows) ∈
        candidateQueries dimension rows selectors := by
    unfold candidateQueries
    exact List.mem_flatMap.mpr ⟨coordinate, hcoord, List.mem_map.mpr ⟨selector, hsel, rfl⟩⟩
  rw [hagree _ hmem]

/-- `wordCandidates` depends on `predictor` only at queries in `candidateQueries`. -/
theorem wordCandidates_congr {predictor₁ predictor₂ : List Bool → Bool} (dimension : ℕ)
    (rows guesses : List (List Bool))
    (hagree : ∀ q ∈ candidateQueries dimension rows (guesses.filter (fun word => word.any id)),
      predictor₁ q = predictor₂ q) :
    wordCandidates predictor₁ dimension rows guesses =
      wordCandidates predictor₂ dimension rows guesses :=
  List.map_congr_left fun guess _ =>
    wordCandidate_congr dimension rows (guesses.filter (fun word => word.any id)) guess hagree

/-- `wordListDecode` depends on `predictor` only at queries in `listDecodeQueries`. -/
theorem wordListDecode_congr {predictor₁ predictor₂ : List Bool → Bool} (dimension precision : ℕ)
    (masks : List Bool)
    (hagree : ∀ q ∈ listDecodeQueries dimension precision masks, predictor₁ q = predictor₂ q) :
    wordListDecode predictor₁ dimension precision masks =
      wordListDecode predictor₂ dimension precision masks :=
  congrArg dedupWords (wordCandidates_congr dimension
    (listRows (listMaskCount dimension precision) dimension masks)
    (enumList (listMaskCount dimension precision)) hagree)

/-- `wordEmpiricalHits` depends on `predictor` only at queries in `sampleRows`. -/
theorem wordEmpiricalHits_congr {predictor₁ predictor₂ : List Bool → Bool}
    (sampleRows : List (List Bool)) (candidate : List Bool)
    (hagree : ∀ q ∈ sampleRows, predictor₁ q = predictor₂ q) :
    wordEmpiricalHits predictor₁ sampleRows candidate =
      wordEmpiricalHits predictor₂ sampleRows candidate := by
  unfold wordEmpiricalHits
  refine List.countP_congr fun row hrow => ?_
  rw [hagree row hrow]

/-- `wordListDecodePruned` depends on `predictor` only at queries in `listDecodePrunedQueries`. -/
theorem wordListDecodePruned_congr {predictor₁ predictor₂ : List Bool → Bool}
    (dimension precision : ℕ) (masks samples : List Bool)
    (hagree : ∀ q ∈ listDecodePrunedQueries dimension precision masks samples,
      predictor₁ q = predictor₂ q) :
    wordListDecodePruned predictor₁ dimension precision masks samples =
      wordListDecodePruned predictor₂ dimension precision masks samples := by
  unfold wordListDecodePruned wordPruneCandidates
  have h1 : ∀ q ∈ listDecodeQueries dimension precision masks, predictor₁ q = predictor₂ q :=
    fun q hq => hagree q (List.mem_append_left _ hq)
  have h2 : ∀ q ∈ listRows (pruneSampleCount dimension precision) dimension samples,
      predictor₁ q = predictor₂ q :=
    fun q hq => hagree q (List.mem_append_right _ hq)
  rw [wordListDecode_congr dimension precision masks h1]
  congr 1
  refine List.filter_congr fun candidate _ => ?_
  rw [wordEmpiricalHits_congr _ candidate h2]

/-- Running `wordListDecode` with `lookupReply queries (queries.map predictor)` where
`queries = listDecodeQueries dimension precision masks` equals `wordListDecode predictor`. -/
theorem wordListDecode_lookupReply_map (predictor : List Bool → Bool) (dimension precision : ℕ)
    (masks : List Bool) :
    let queries := listDecodeQueries dimension precision masks
    wordListDecode (lookupReply queries (queries.map predictor)) dimension precision masks =
      wordListDecode predictor dimension precision masks :=
  wordListDecode_congr dimension precision masks fun _ hq => lookupReply_map_of_mem predictor hq

/-- Running `wordListDecodePruned` with `lookupReply queries (queries.map predictor)` where
`queries = listDecodePrunedQueries dimension precision masks samples` equals
`wordListDecodePruned predictor`. -/
theorem wordListDecodePruned_lookupReply_map (predictor : List Bool → Bool)
    (dimension precision : ℕ) (masks samples : List Bool) :
    let queries := listDecodePrunedQueries dimension precision masks samples
    wordListDecodePruned (lookupReply queries (queries.map predictor))
        dimension precision masks samples =
      wordListDecodePruned predictor dimension precision masks samples :=
  wordListDecodePruned_congr dimension precision masks samples fun _ hq =>
    lookupReply_map_of_mem predictor hq

/-- One step of batch oracle querying: query `queries.getD replies.length []` on channel `()` and
append the first reply bit (defaulting to `false` if the reply is empty) to `replies`. -/
noncomputable def queryBatchStep (queries : List (List Bool)) (replies : List Bool) :
    WordOracleComp Unit (List Bool) :=
  (fun reply => replies ++ [reply.getD 0 false]) <$>
    (List.take 1 <$> ProbOracleComp.query ((), queries.getD replies.length []))

/-- `queryBatchStep` is a strict oracle-PPT step on `(queries, replies)`. -/
@[fun_prop]
theorem isOraclePPTOn_queryBatchStep :
    IsOraclePPTOn (encPair (encList encBits) encBits) encBits
      (fun pair => queryBatchStep pair.1 pair.2) := by
  unfold queryBatchStep
  exact (IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)).map_with
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.fst _ _).snd' (by polytime))

/-- Query every word in `queries` in order on channel `()`, returning the list of first reply
bits. -/
noncomputable def queryBatch (queries : List (List Bool)) : WordOracleComp Unit (List Bool) :=
  OracleComp.iterate queries.length (queryBatchStep queries) []

/-- `queryBatch` is strict oracle-PPT on framed query lists. -/
@[fun_prop]
theorem isOraclePPTOn_queryBatch :
    IsOraclePPTOn (encList encBits) encBits queryBatch := by
  unfold queryBatch
  refine IsOraclePPTOn.iterateWith_of_bounded_growth
    (by fun_prop) (by fun_prop) isOraclePPTOn_queryBatchStep
    (growth := fun _ => 1) (.const 1) ?_
  intro queries replies next hnext
  obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simp

/-- `queryBatch` composed with a polynomial-time query-list generator is uniform strict oracle
PPT. -/
@[fun_prop]
theorem isOraclePPTOn_queryBatch_comp {α : Type} {input : α ↪ List Bool}
    {queries : α → List (List Bool)}
    (hqueries : ComputableInPolyTime queries input (encList encBits)) :
    IsOraclePPTOn input encBits (fun a => queryBatch (queries a)) :=
  isOraclePPTOn_queryBatch.preprocess hqueries

/-- Stateless oracle handler on channel `Unit` that answers each query `q.2` with the 1-bit reply
`[predictor q.2]`. -/
noncomputable def predictorOracle (predictor : List Bool → Bool) :
    Unit × List Bool → StateT Unit PMF (List Bool) :=
  fun q s => PMF.pure ([predictor q.2], s)

/-- Extend an `n`-bit Boolean oracle `B : BitString n → Bool` to arbitrary bit lists via
`BitString.ofList n`. -/
def bitStringPredictor {n : ℕ} (B : BitString n → Bool) (query : List Bool) : Bool :=
  B (BitString.ofList n query)

/-- On `List.ofFn x` for `x : BitString n`, `bitStringPredictor B` equals `B x`. -/
@[simp]
theorem bitStringPredictor_ofFn {n : ℕ} (B : BitString n → Bool) (x : BitString n) :
    bitStringPredictor B (List.ofFn x) = B x := by
  simp [bitStringPredictor]

/-- Stateless oracle handler on channel `Unit` for an arbitrary `n`-bit Boolean function
`B : BitString n → Bool`. No efficiency assumption is placed on `B`. -/
noncomputable def bitStringOracle {n : ℕ} (B : BitString n → Bool) :
    Unit × List Bool → StateT Unit PMF (List Bool) :=
  predictorOracle (bitStringPredictor B)

private theorem runWith_iterate_queryBatchStep (predictor : List Bool → Bool)
    (queries : List (List Bool)) (s : Unit) :
    ∀ t ≤ queries.length,
      ProbOracleComp.runWith (predictorOracle predictor)
        (OracleComp.iterate t (queryBatchStep queries) []) s =
      PMF.pure ((queries.take t).map predictor, s) := by
  intro t ht
  induction t with
  | zero => simp [ProbOracleComp.runWith_pure]
  | succ t ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.runWith_bind, ih (Nat.le_of_succ_le ht),
      PMF.pure_bind]
    have hlt : t < queries.length := ht
    have hlen : ((queries.take t).map predictor).length = t := by
      rw [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
    have hget : queries.getD ((queries.take t).map predictor).length [] = queries[t] := by
      rw [hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    have htake : (queries.take (t + 1)).map predictor =
        (queries.take t).map predictor ++ [predictor queries[t]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
        List.map_singleton]
    rw [htake, queryBatchStep, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, hget, predictorOracle]
    simp [-List.map_take]

/-- Against `predictorOracle predictor`, `queryBatch queries` returns `queries.map predictor`. -/
theorem runWith_queryBatch_predictorOracle (predictor : List Bool → Bool)
    (queries : List (List Bool)) (s : Unit) :
    ProbOracleComp.runWith (predictorOracle predictor) (queryBatch queries) s =
      PMF.pure (queries.map predictor, s) := by
  simpa [queryBatch] using
    runWith_iterate_queryBatchStep predictor queries s queries.length le_rfl

/-- Uniform strict oracle-PPT Goldreich–Levin list decoder (unpruned): sample `listMaskCount`
random masks, batch-query the oracle on `listDecodeQueries`, and return the duplicate-free
candidate list `wordListDecode`. -/
noncomputable def oracleListDecode (p : ListDecodeParams) :
    WordOracleComp Unit (List (List Bool)) := do
  let masks ← ProbOracleComp.sample
    (BitString.sampleList (listMaskCount p.dimension p.precision * p.dimension))
  (fun replies => wordListDecode
    (lookupReply (listDecodeQueries p.dimension p.precision masks) replies)
    p.dimension p.precision masks) <$>
      queryBatch (listDecodeQueries p.dimension p.precision masks)

/-- `oracleListDecode` is a uniform strict oracle-PPT algorithm on `encListDecodeParams`. -/
@[fun_prop]
theorem isOraclePPTOn_oracleListDecode :
    IsOraclePPTOn encListDecodeParams (encList encBits) oracleListDecode := by
  ppt [oracleListDecode]

/-- Uniform polynomial bounds on the number of oracle queries and the length of every oracle query
made by `oracleListDecode`. -/
theorem oracleListDecode_query_bounds :
    ∃ c d : ℕ, ∀ p : ListDecodeParams,
      (oracleListDecode p).IsQueryBounded (c * ((encListDecodeParams p).length + 1) ^ d) ∧
      (oracleListDecode p).QueriesSatisfy fun request =>
        request.2.length ≤ c * ((encListDecodeParams p).length + 1) ^ d :=
  isOraclePPTOn_oracleListDecode.query_bounds

/-- Running `oracleListDecode p` against `predictorOracle predictor` induces the exact
`wordListDecode` distribution over uniform mask tapes. -/
theorem runWith_oracleListDecode_predictorOracle (predictor : List Bool → Bool)
    (p : ListDecodeParams) (s : Unit) :
    ProbOracleComp.runWith (predictorOracle predictor) (oracleListDecode p) s =
      ((uniformList (listMaskCount p.dimension p.precision * p.dimension)).map
        (wordListDecode predictor p.dimension p.precision)).map (·, s) := by
  unfold oracleListDecode
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbOracleComp.runWith_map, BitString.eval_sampleList, PMF.bind_map, Function.comp_def,
    runWith_queryBatch_predictorOracle, PMF.pure_map, Prod.map_apply, id_eq,
    wordListDecode_lookupReply_map, PMF.map_comp]
  rfl

/-- **Simultaneous oracle-PPT list decoding (`ℝ≥0∞`)**: for every Boolean oracle
`B : BitString p.dimension → Bool` (with no efficiency assumption on `B`) and `0 < p.precision`,
running `oracleListDecode p` against `bitStringOracle B` outputs with probability at least `1 / 2`
a duplicate-free list `L` of size at most `16 * p.dimension * p.precision ^ 4 + 2` that contains
`List.ofFn x` for every `x : BitString p.dimension` with
`1 / 2 + 1 / p.precision ≤ agreement B x`. -/
theorem oracleListDecode_bitStringOracle_simultaneous_success_ge_half
    (p : ListDecodeParams) (hprec : 0 < p.precision) (B : BitString p.dimension → Bool) :
    (1 / 2 : ℝ≥0∞) ≤
      ((ProbOracleComp.runWith (bitStringOracle B) (oracleListDecode p) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString p.dimension,
            1 / 2 + 1 / (p.precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
          L.Nodup ∧
          L.length ≤ 16 * p.dimension * p.precision ^ 4 + 2} := by
  rw [bitStringOracle, runWith_oracleListDecode_predictorOracle, PMF.map_comp]
  have hfst : Prod.fst ∘ (fun L : List (List Bool) => (L, ())) = id := rfl
  rw [hfst, PMF.map_id]
  simpa [bitStringPredictor_ofFn] using
    wordListDecode_simultaneous_success_ge_half (bitStringPredictor B) p.dimension p.precision hprec

/-- Uniform strict oracle-PPT Goldreich–Levin pruned list decoder: sample `listMaskCount` random
masks and `pruneSampleCount` random estimation points, batch-query the oracle on
`listDecodePrunedQueries`, and return the pruned duplicate-free candidate list
`wordListDecodePruned`. -/
noncomputable def oracleListDecodePruned (p : ListDecodeParams) :
    WordOracleComp Unit (List (List Bool)) := do
  let masks ← ProbOracleComp.sample
    (BitString.sampleList (listMaskCount p.dimension p.precision * p.dimension))
  let samples ← ProbOracleComp.sample
    (BitString.sampleList (pruneSampleCount p.dimension p.precision * p.dimension))
  (fun replies => wordListDecodePruned
    (lookupReply (listDecodePrunedQueries p.dimension p.precision masks samples) replies)
    p.dimension p.precision masks samples) <$>
      queryBatch (listDecodePrunedQueries p.dimension p.precision masks samples)

/-- `oracleListDecodePruned` is a uniform strict oracle-PPT algorithm on `encListDecodeParams`. -/
@[fun_prop]
theorem isOraclePPTOn_oracleListDecodePruned :
    IsOraclePPTOn encListDecodeParams (encList encBits) oracleListDecodePruned := by
  ppt [oracleListDecodePruned]

/-- Uniform polynomial bounds on the number of oracle queries and the length of every oracle query
made by `oracleListDecodePruned`. -/
theorem oracleListDecodePruned_query_bounds :
    ∃ c d : ℕ, ∀ p : ListDecodeParams,
      (oracleListDecodePruned p).IsQueryBounded (c * ((encListDecodeParams p).length + 1) ^ d) ∧
      (oracleListDecodePruned p).QueriesSatisfy fun request =>
        request.2.length ≤ c * ((encListDecodeParams p).length + 1) ^ d :=
  isOraclePPTOn_oracleListDecodePruned.query_bounds

/-- Running `oracleListDecodePruned p` against `predictorOracle predictor` induces the exact
`wordListDecodePruned` distribution over independent uniform mask and sample tapes. -/
theorem runWith_oracleListDecodePruned_predictorOracle (predictor : List Bool → Bool)
    (p : ListDecodeParams) (s : Unit) :
    ProbOracleComp.runWith (predictorOracle predictor) (oracleListDecodePruned p) s =
      (((uniformList (listMaskCount p.dimension p.precision * p.dimension)).bind (fun masks =>
        (uniformList (pruneSampleCount p.dimension p.precision * p.dimension)).map
          (wordListDecodePruned predictor p.dimension p.precision masks))).map (·, s)) := by
  unfold oracleListDecodePruned
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbOracleComp.runWith_map, BitString.eval_sampleList, PMF.bind_map, PMF.map_bind,
    Function.comp_def, runWith_queryBatch_predictorOracle, PMF.pure_map, Prod.map_apply, id_eq,
    wordListDecodePruned_lookupReply_map, PMF.map_comp]
  rfl

/-- **Pruned simultaneous oracle-PPT list decoding (`ℝ≥0∞`, Goldreich 2008 Theorem 7.8)**: for
every Boolean oracle `B : BitString p.dimension → Bool` (with no efficiency assumption on `B`) and
`0 < p.precision`, running `oracleListDecodePruned p` against `bitStringOracle B` succeeds with
probability at least `1 / 2` in returning a duplicate-free list `L` that:
1. contains `List.ofFn x` for every `x : BitString p.dimension` with
   `1 / 2 + 1 / p.precision ≤ agreement B x`,
2. contains only `List.ofFn x` for `x : BitString p.dimension` with
   `1 / 2 + 1 / (2 * p.precision) ≤ agreement B x`,
3. has length at most `p.precision ^ 2`. -/
theorem oracleListDecodePruned_bitStringOracle_simultaneous_success_ge_half
    (p : ListDecodeParams) (hprec : 0 < p.precision) (B : BitString p.dimension → Bool) :
    (1 / 2 : ℝ≥0∞) ≤
      ((ProbOracleComp.runWith (bitStringOracle B) (oracleListDecodePruned p) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString p.dimension,
            1 / 2 + 1 / (p.precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
          (∀ x : BitString p.dimension,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (p.precision : ℝ)) ≤ agreement B x) ∧
          L.Nodup ∧
          L.length ≤ p.precision ^ 2} := by
  rw [bitStringOracle, runWith_oracleListDecodePruned_predictorOracle, PMF.map_comp]
  have hfst : Prod.fst ∘ (fun L : List (List Bool) => (L, ())) = id := rfl
  rw [hfst, PMF.map_id]
  simpa [bitStringPredictor_ofFn] using
    wordListDecodePruned_simultaneous_success_ge_half (bitStringPredictor B) p.dimension p.precision
      hprec

/-- **Pruned simultaneous oracle-PPT list decoding (`ℝ`)**: real-probability form of
`oracleListDecodePruned_bitStringOracle_simultaneous_success_ge_half`. -/
theorem oracleListDecodePruned_bitStringOracle_simultaneous_success_toReal_ge_half
    (p : ListDecodeParams) (hprec : 0 < p.precision) (B : BitString p.dimension → Bool) :
    1 / 2 ≤
      (((ProbOracleComp.runWith (bitStringOracle B) (oracleListDecodePruned p) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString p.dimension,
            1 / 2 + 1 / (p.precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
          (∀ x : BitString p.dimension,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (p.precision : ℝ)) ≤ agreement B x) ∧
          L.Nodup ∧
          L.length ≤ p.precision ^ 2}).toReal := by
  simpa [one_div] using ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (oracleListDecodePruned_bitStringOracle_simultaneous_success_ge_half p hprec B)

end Cslib.Crypto.GoldreichLevin
