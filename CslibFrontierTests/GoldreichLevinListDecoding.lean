/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Crypto.Computational.GoldreichLevin.Nonuniform
import CslibFrontier.Crypto.Computational.GoldreichLevin.WordListDecoder
import CslibFrontier.Foundations.Data.BitString.Support.Equiv
import Mathlib.Tactic.NormNum

/-! Simultaneous Goldreich–Levin list decoding (Goldreich 2008, Theorem 7.8, p. 254): Parseval
correlation bounds, finite and word-level list decoders, empirical-agreement pruning, and uniform
strict oracle-PPT certificates checked through ordinary module imports. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichLevinListDecoding

open Cslib Cslib.Crypto Cslib.Crypto.GoldreichLevin Cslib.Probability
open Turing.MultiTapeTM Finset
open scoped ENNReal

private def noisy (r : BitString 2) : Bool := r 0 && r 1

-- `BitString.supportEquiv` sends a bit string to its support `{i | x i = true}`.
example : BitString.supportEquiv ![true, false] = ({0} : Finset (Fin 2)) := by decide

-- `noisy` (`r 0 && r 1`) agrees with the all-zero parity `0 ⬝ᵥ r = false` on 3 of the 4 inputs,
-- so `(0 : BitString 2)` belongs to the heavy set at `precision = 4` (`1 / 2 + 1 / 4 = 3 / 4`).
private theorem agreement_noisy_zero : 1 / 2 + 1 / (4 : ℝ) ≤ agreement noisy 0 := by
  have hcard : #{r : BitString 2 | noisy r = (0 : BitString 2) ⬝ᵥ r} = 3 := by decide
  rw [agreement_eq_card_div, hcard]
  norm_num

-- Parseval's identity holds for any Boolean predictor on `BitString 2`: squared biases sum to 1.
example : (∑ x : BitString 2, (2 * agreement noisy x - 1) ^ 2) = 1 :=
  sum_two_mul_agreement_sub_one_sq noisy

-- At threshold `1 / 2 + 1 / 4 = 3 / 4`, at most `1 / (4 * (1 / 4) ^ 2) = 4` strings can correlate.
example :
    ((Finset.univ.filter (fun x : BitString 2 => 1 / 2 + 1 / 4 ≤ agreement noisy x)).card : ℝ) ≤
      1 / (4 * (1 / 4 : ℝ) ^ 2) :=
  card_filter_agreement_ge_le noisy (by norm_num)

-- Integer precision specialization: at `precision = 2`, at most `2 ^ 2 = 4` strings have
-- agreement at least `1 / 2 + 1 / (2 * 2) = 3 / 4`.
example :
    (Finset.univ.filter (fun x : BitString 2 =>
      1 / 2 + 1 / (2 * (2 : ℝ)) ≤ agreement noisy x)).card ≤ 2 ^ 2 :=
  card_filter_agreement_ge_half_inv_le noisy (by decide)

-- Finite simultaneous list decoding at `precision = 4` (`listMaskCount 2 4`) succeeds with
-- probability at least 1/2, non-vacuously recovering `(0 : BitString 2)` (`agreement_noisy_zero`).
example :
    (1 / 2 : ℝ≥0∞) ≤
      (decode noisy (listMaskCount 2 4)).toOuterMeasure
        {list : Finset (BitString 2) |
          (∀ x : BitString 2, 1 / 2 + 1 / (4 : ℝ) ≤ agreement noisy x → x ∈ list) ∧
          (0 : BitString 2) ∈ list} := by
  refine (decode_listMaskCount_simultaneous_success_ge_half noisy (by decide)).trans
    ((decode noisy (listMaskCount 2 4)).toOuterMeasure.mono fun list hlist => ?_)
  exact ⟨hlist, hlist 0 agreement_noisy_zero⟩

-- Pruned finite simultaneous list decoding at `precision = 4` (empirical threshold `11 / 16`)
-- succeeds with probability at least 1/2, non-vacuously retaining `(0 : BitString 2)` while
-- bounding the returned list cardinality by `4 ^ 2 = 16`.
example :
    (1 / 2 : ℝ≥0∞) ≤
      (decodePruned noisy (listMaskCount 2 4) (pruneSampleCount 2 4) 11 16).toOuterMeasure
        {list : Finset (BitString 2) |
          (∀ x : BitString 2, 1 / 2 + 1 / (4 : ℝ) ≤ agreement noisy x → x ∈ list) ∧
          (0 : BitString 2) ∈ list ∧
          (∀ x ∈ list, 1 / 2 + 1 / (2 * (4 : ℝ)) ≤ agreement noisy x) ∧
          list.card ≤ 4 ^ 2} := by
  refine (decodePruned_simultaneous_success_ge_half noisy (by decide)).trans
    ((decodePruned noisy (listMaskCount 2 4) (pruneSampleCount 2 4) 11 16).toOuterMeasure.mono
      fun list ⟨hall, hsound, hcard⟩ => ?_)
  exact ⟨hall, hall 0 agreement_noisy_zero, hsound, hcard⟩

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

-- General simultaneous success against any arbitrary Boolean oracle `B : BitString n → Bool`,
-- together with membership of any heavy string `x₀`.
private theorem oracleListDecodePruned_mem_of_agreement (n precision : ℕ) (hprec : 0 < precision)
    (B : BitString n → Bool) (x₀ : BitString n)
    (hx₀ : 1 / 2 + 1 / (precision : ℝ) ≤ agreement B x₀) :
    let p : ListDecodeParams := ⟨n, precision⟩
    1 / 2 ≤
      (((ProbOracleComp.runWith (bitStringOracle B) (oracleListDecodePruned p) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
          List.ofFn x₀ ∈ L ∧
          (∀ x : BitString n,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement B x) ∧
          L.Nodup ∧
          L.length ≤ precision ^ 2}).toReal := by
  let p : ListDecodeParams := ⟨n, precision⟩
  let dist := (ProbOracleComp.runWith (bitStringOracle B) (oracleListDecodePruned p) ()).map
    Prod.fst
  have h := oracleListDecodePruned_bitStringOracle_simultaneous_success_ge_half p hprec B
  have hmono :
      (1 / 2 : ℝ≥0∞) ≤
        dist.toOuterMeasure
          {L : List (List Bool) |
            (∀ x : BitString n,
              1 / 2 + 1 / (precision : ℝ) ≤ agreement B x → List.ofFn x ∈ L) ∧
            List.ofFn x₀ ∈ L ∧
            (∀ x : BitString n,
              List.ofFn x ∈ L →
                1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement B x) ∧
            L.Nodup ∧
            L.length ≤ precision ^ 2} :=
    h.trans (dist.toOuterMeasure.mono fun L ⟨hall, hsound, hnodup, hlen⟩ =>
      ⟨hall, hall x₀ hx₀, hsound, hnodup, hlen⟩)
  have hhalf : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have hmono' := ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top dist _) hmono
  rwa [hhalf] at hmono'

-- Concrete non-vacuous instance on `noisy` (`r 0 && r 1`) at `precision = 4` with heavy string `0`.
example :
    1 / 2 ≤
      (((ProbOracleComp.runWith (bitStringOracle noisy) (oracleListDecodePruned ⟨2, 4⟩) ()).map
          Prod.fst).toOuterMeasure
        {L : List (List Bool) |
          (∀ x : BitString 2,
            1 / 2 + 1 / (4 : ℝ) ≤ agreement noisy x → List.ofFn x ∈ L) ∧
          List.ofFn (0 : BitString 2) ∈ L ∧
          (∀ x : BitString 2,
            List.ofFn x ∈ L →
              1 / 2 + 1 / (2 * (4 : ℝ)) ≤ agreement noisy x) ∧
          L.Nodup ∧
          L.length ≤ 4 ^ 2}).toReal :=
  oracleListDecodePruned_mem_of_agreement 2 4 (by decide) noisy 0 agreement_noisy_zero

-- General simultaneous success against any arbitrary Boolean oracle `B : BitString n → Bool`.
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
