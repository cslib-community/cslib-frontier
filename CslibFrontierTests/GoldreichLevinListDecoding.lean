/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.GoldreichLevin.WordListDecoder

/-! Simultaneous Goldreich–Levin list decoding (Goldreich 2008 Theorem 7.8): Parseval correlation
bounds, finite and word-level list decoders, empirical-agreement pruning, and uniform strict
oracle-PPT certificates. -/

namespace CslibFrontierTests.GoldreichLevinListDecoding

open Cslib Cslib.Crypto Cslib.Crypto.GoldreichLevin Cslib.Probability
open Turing.MultiTapeTM Finset
open scoped ENNReal

private def noisy (r : BitString 2) : Bool := r 0 && r 1

-- Parseval's identity holds for any Boolean predictor on `BitString 2`: squared biases sum to 1.
example : (∑ x : BitString 2, (2 * agreement noisy x - 1) ^ 2) = 1 :=
  sum_two_mul_agreement_sub_one_sq noisy

-- At threshold `1 / 2 + 1 / 4 = 3 / 4`, at most `1 / (4 * (1 / 4) ^ 2) = 4` strings can correlate.
example :
    ((Finset.univ.filter (fun x : BitString 2 => 1 / 2 + 1 / 4 ≤ agreement noisy x)).card : ℝ) ≤
      1 / (4 * (1 / 4 : ℝ) ^ 2) :=
  card_filter_agreement_ge_le noisy (by norm_num)

-- Integer precision specialization: at `precision = 2`, at most `4 * 2 ^ 2 = 16` strings have
-- agreement at least `1 / 2 + 1 / (2 * 2) = 3 / 4`.
example :
    (Finset.univ.filter (fun x : BitString 2 =>
      1 / 2 + 1 / (2 * (2 : ℝ)) ≤ agreement noisy x)).card ≤ 2 ^ 2 :=
  card_filter_agreement_ge_half_inv_le noisy (by decide)

-- Finite simultaneous list decoding at `listMaskCount 2 2` succeeds with probability at least 1/2.
example :
    (1 / 2 : ℝ≥0∞) ≤
      (decode noisy (listMaskCount 2 2)).toOuterMeasure
        {list : Finset (BitString 2) |
          ∀ x : BitString 2, 1 / 2 + 1 / (2 : ℝ) ≤ agreement noisy x → x ∈ list} :=
  decode_listMaskCount_simultaneous_success_ge_half noisy (by decide)

-- Pruned finite simultaneous list decoding at `precision = 2` succeeds with probability at least
-- 1/2 and bounds the returned list cardinality by `2 ^ 2 = 4`.
example :
    (1 / 2 : ℝ≥0∞) ≤
      (decodePruned noisy (listMaskCount 2 2) (pruneSampleCount 2 2) 7 8).toOuterMeasure
        {list : Finset (BitString 2) |
          (∀ x : BitString 2, 1 / 2 + 1 / (2 : ℝ) ≤ agreement noisy x → x ∈ list) ∧
          (∀ x ∈ list, 1 / 2 + 1 / (2 * (2 : ℝ)) ≤ agreement noisy x) ∧
          list.card ≤ 2 ^ 2} :=
  decodePruned_simultaneous_success_ge_half noisy (by decide)

-- `dedupWords` removes duplicate words while preserving first-occurrence order.
example :
    dedupWords [[true, false], [false, false], [true, false], [true, true]] =
      [[true, false], [false, false], [true, true]] := by decide

-- Concrete execution of `wordListDecode` with a linear parity predictor recovers `[true, false]`
-- in a duplicate-free candidate list.
example :
    [true, false] ∈
      wordListDecode (fun query => BitString.listDot [true, false] query) 2 1 [false, false] ∧
    (wordListDecode
      (fun query => BitString.listDot [true, false] query) 2 1 [false, false]).Nodup := by
  decide

-- Concrete execution of `wordEmpiricalHits` and `wordPruneCandidates` on sample rows.
example :
    wordEmpiricalHits (fun query => BitString.listDot [true, false] query)
      [[false, false], [true, false], [false, true], [true, true]] [true, false] = 4 := by
  decide

example :
    wordPruneCandidates (fun query => BitString.listDot [true, false] query) 3 4
      [[false, false], [true, false], [false, true], [true, true]]
      [[true, false], [false, true], [true, false]] = [[true, false]] := by
  decide

-- `lookupReply` recovers the recorded Boolean answer for every queried word.
example :
    lookupReply [[false, true], [true, false]] [false, true] [true, false] = true ∧
    lookupReply [[false, true], [true, false]] [false, true] [false, false] = false := by
  decide

-- Uniform deterministic polynomial-time certificates for `wordListDecode` and
-- `wordListDecodePruned` with a captured predictor.
example :
    ComputableInPolyTime
      (fun p : ListDecodeParams × List Bool =>
        wordListDecode (fun query => BitString.listDot p.2 query)
          p.1.dimension p.1.precision p.2)
      (encPair encListDecodeParams encBits) (encList encBits) := by
  fun_prop

example :
    ComputableInPolyTime
      (fun p : ListDecodeParams × List Bool =>
        wordListDecodePruned (fun query => BitString.listDot p.2 query)
          p.1.dimension p.1.precision p.2 p.2)
      (encPair encListDecodeParams encBits) (encList encBits) := by
  fun_prop

-- Uniform strict oracle-PPT certificates and polynomial query bounds for `oracleListDecode` and
-- `oracleListDecodePruned`.
example : IsOraclePPTOn encListDecodeParams (encList encBits) oracleListDecode :=
  isOraclePPTOn_oracleListDecode

example : IsOraclePPTOn encListDecodeParams (encList encBits) oracleListDecodePruned :=
  isOraclePPTOn_oracleListDecodePruned

example :
    ∃ c d : ℕ, ∀ p : ListDecodeParams,
      (oracleListDecodePruned p).IsQueryBounded (c * ((encListDecodeParams p).length + 1) ^ d) ∧
      (oracleListDecodePruned p).QueriesSatisfy fun request =>
        request.2.length ≤ c * ((encListDecodeParams p).length + 1) ^ d :=
  oracleListDecodePruned_query_bounds

-- Simultaneous success against any arbitrary Boolean oracle `B : BitString n → Bool`, with no
-- efficiency assumption on `B`.
example (n precision : ℕ) (hprec : 0 < precision) (B : BitString n → Bool) :
    let p : ListDecodeParams := ⟨n, precision⟩
    1 / 2 ≤
      (((ProbOracleComp.runWith (bitStringOracle B) (oracleListDecodePruned p) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
          (∀ x : BitString n,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement B x) ∧
          L.Nodup ∧
          L.length ≤ precision ^ 2}).toReal :=
  oracleListDecodePruned_bitStringOracle_simultaneous_success_toReal_ge_half
    ⟨n, precision⟩ hprec B

end CslibFrontierTests.GoldreichLevinListDecoding
