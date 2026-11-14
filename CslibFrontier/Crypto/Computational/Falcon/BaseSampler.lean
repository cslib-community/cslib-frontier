/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Falcon v1.2 BaseSampler

Falcon v1.2 Algorithm 12 draws a uniform 72-bit integer `u` and returns the number of entries of
Table 3.1's reverse cumulative distribution table which are strictly greater than `u`. This module
implements that fixed 18-comparison scan and proves that every output `z ∈ {0, ..., 18}` has the
exact table mass `pdt[z] / 2^72`.

This is only the nonnegative `BaseSampler` leaf of `SamplerZ`. It has no rejection event: the
independent sign bit and `BerExp` rejection loop occur later. Falcon v1.2 also states the Rényi
discrepancy `R₅₁₃(χ || D_{ℤ⁺,σmax}) ≤ 1 + 2⁻⁷⁸` after equation (3.33). That analytic
statement is not formalized here: the library currently has neither a Rényi-divergence API nor a
half-Gaussian distribution with Falcon's convention.

At the source level, the closed sampler consumes exactly 72 fair bits and scans all 18 thresholds,
performing 18 comparisons and 18 conditional increments. The threshold payload is `18 * 72 =
1296` bits and the result fits in five bits. There is no external oracle or handler. These facts do
not assign a native program encoding, step count, workspace bound, installed-table framing, or
constant-time certificate; in particular, an installed-artifact account must charge the table
either inline in the program or once as a separate occurrence, not both.

## Main definitions

* `Cslib.Crypto.Falcon.BaseSamplerOutput`: the exact output range `Fin 19`.
* `Cslib.Crypto.Falcon.baseSamplerProbabilityNumerators`: Table 3.1's 19 `pdt` entries.
* `Cslib.Crypto.Falcon.baseSamplerReverseCumulativeThresholds`: the 18 RCDT entries compared by
  Algorithm 12.
* `Cslib.Crypto.Falcon.baseSamplerFromWord`: Algorithm 12's deterministic full-table scan.
* `Cslib.Crypto.Falcon.baseSampler`: the scan applied to exactly 72 fair bits.

## Main results

* `Cslib.Crypto.Falcon.baseSampler_probabilityNumerators_sum`: the table has total mass `2^72`.
* `Cslib.Crypto.Falcon.baseSampler_reverseCumulativeThreshold_eq_sum`: the RCDT entries are the
  reverse cumulative sums of `pdt`.
* `Cslib.Crypto.Falcon.eval_baseSampler`: every output has exact mass `pdt[z] / 2^72`.
* `Cslib.Crypto.Falcon.support_baseSampler`: all 19 outputs occur.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-Based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Section 3.9.3, equations (3.32)--(3.33), Table 3.1 and
  Algorithm 12.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/sign.c::gaussian0_sampler`, lines 969--1030.
* [National Institute of Standards and Technology, *Post-Quantum Cryptography
  Standardization*][NISTPQC2026].
-/

public section

namespace Cslib.Crypto.Falcon

open Probability
open scoped BigOperators ENNReal

/-- The output range `0, ..., 18` of Falcon v1.2 Algorithm 12. -/
abbrev BaseSamplerOutput := Fin 19

/-- The scaled masses `pdt[i] = 2^72 · χ(i)` from Falcon v1.2 Table 3.1. -/
@[expose] def baseSamplerProbabilityNumerators : List ℕ :=
  [1697680241746640300030,
   1459943456642912959616,
   928488355018011056515,
   436693944817054414619,
   151893140790369201013,
   39071441848292237840,
   7432604049020375675,
   1045641569992574730,
   108788995549429682,
   8370422445201343,
   476288472308334,
   20042553305308,
   623729532807,
   14354889437,
   244322621,
   3075302,
   28626,
   197,
   1]

@[simp] theorem baseSampler_probabilityNumerators_length :
    baseSamplerProbabilityNumerators.length = 19 := by
  rfl

/-- The scaled probability numerator for an output of Algorithm 12. -/
@[expose] def baseSamplerProbabilityNumerator (z : BaseSamplerOutput) : ℕ :=
  baseSamplerProbabilityNumerators.get
    ⟨z.val, by simpa only [baseSampler_probabilityNumerators_length] using z.isLt⟩

/-- The reverse cumulative thresholds compared by Falcon v1.2 Algorithm 12.

Table 3.1 prints a final RCDT value `0` at index 18, but Algorithm 12 compares precisely the first
18 entries, indexed `0, ..., 17`. -/
@[expose] def baseSamplerReverseCumulativeThresholds : List ℕ :=
  [3024686241123004913666,
   1564742784480091954050,
   636254429462080897535,
   199560484645026482916,
   47667343854657281903,
   8595902006365044063,
   1163297957344668388,
   117656387352093658,
   8867391802663976,
   496969357462633,
   20680885154299,
   638331848991,
   14602316184,
   247426747,
   3104126,
   28824,
   198,
   1]

@[simp] theorem baseSampler_reverseCumulativeThresholds_length :
    baseSamplerReverseCumulativeThresholds.length = 18 := by
  rfl

/-- One RCDT entry from Table 3.1. -/
@[expose] def baseSamplerReverseCumulativeThreshold (i : Fin 18) : ℕ :=
  baseSamplerReverseCumulativeThresholds.get
    ⟨i.val, by simpa only [baseSampler_reverseCumulativeThresholds_length] using i.isLt⟩

/-- The 19 `pdt` numerators sum to the complete 72-bit sampling range. -/
theorem baseSampler_probabilityNumerators_sum :
    baseSamplerProbabilityNumerators.sum = 2 ^ 72 := by
  norm_num [baseSamplerProbabilityNumerators]

/-- Each RCDT entry is the sum of all later `pdt` entries. -/
theorem baseSampler_reverseCumulativeThreshold_eq_sum (i : Fin 18) :
    baseSamplerReverseCumulativeThreshold i =
      ∑ z : BaseSamplerOutput with i.val < z.val, baseSamplerProbabilityNumerator z := by
  fin_cases i <;>
    norm_num [baseSamplerReverseCumulativeThreshold, baseSamplerReverseCumulativeThresholds,
      baseSamplerProbabilityNumerator, baseSamplerProbabilityNumerators, Fin.sum_univ_succ]

/-- Every compared RCDT entry fits in the 72-bit word used by Algorithm 12. -/
theorem baseSamplerReverseCumulativeThreshold_lt_twoPow (i : Fin 18) :
    baseSamplerReverseCumulativeThreshold i < 2 ^ 72 := by
  fin_cases i <;>
    norm_num [baseSamplerReverseCumulativeThreshold, baseSamplerReverseCumulativeThresholds]

/-- The number of random bits consumed by the denotational Algorithm 12 sampler. -/
def baseSamplerRandomBits : ℕ := 72

/-- The number of threshold comparisons in Algorithm 12's fixed full-table scan. -/
def baseSamplerThresholdComparisons : ℕ := 18

/-- The number of conditional increments in Algorithm 12's fixed full-table scan. -/
def baseSamplerConditionalIncrements : ℕ := 18

/-- The unframed threshold payload: 18 entries of 72 bits each. -/
def baseSamplerThresholdPayloadBits : ℕ := 18 * 72

@[simp] theorem baseSampler_thresholdPayloadBits_eq : baseSamplerThresholdPayloadBits = 1296 := by
  rfl

/-- The number of RCDT thresholds strictly greater than `u`.

This is the full fixed scan in Algorithm 12, lines 3--4. -/
@[expose] def baseSamplerComparisonCount (u : ℕ) : ℕ :=
  baseSamplerReverseCumulativeThresholds.countP fun threshold => decide (u < threshold)

/-- Falcon v1.2 Algorithm 12 on a 72-bit word, defined totally on naturals.

The result bound follows from the fixed 18-entry table. The probabilistic sampler below supplies
only words below `2^72`. -/
@[expose] def baseSamplerFromWord (u : ℕ) : BaseSamplerOutput :=
  ⟨baseSamplerComparisonCount u, by
    have h := List.countP_le_length
      (l := baseSamplerReverseCumulativeThresholds)
      (p := fun threshold => decide (u < threshold))
    rw [baseSampler_reverseCumulativeThresholds_length] at h
    omega⟩

/-- Falcon v1.2 `BaseSampler`: draw exactly 72 fair bits, then run Algorithm 12's fixed scan. -/
noncomputable def baseSampler : ProbComp BaseSamplerOutput := do
  let u ← ProbComp.sampleBinaryNat baseSamplerRandomBits
  return baseSamplerFromWord u

private def baseSamplerCutoffs : List ℕ :=
  2 ^ 72 :: baseSamplerReverseCumulativeThresholds ++ [0]

@[simp] private theorem baseSamplerCutoffs_length : baseSamplerCutoffs.length = 20 := by
  simp [baseSamplerCutoffs]

private def baseSamplerLowerCutoff (z : BaseSamplerOutput) : ℕ :=
  baseSamplerCutoffs.get
    ⟨z.val + 1, by rw [baseSamplerCutoffs_length]; omega⟩

private def baseSamplerUpperCutoff (z : BaseSamplerOutput) : ℕ :=
  baseSamplerCutoffs.get
    ⟨z.val, by rw [baseSamplerCutoffs_length]; omega⟩

private theorem baseSamplerProbabilityNumerator_eq_cutoff_sub (z : BaseSamplerOutput) :
    baseSamplerProbabilityNumerator z =
      baseSamplerUpperCutoff z - baseSamplerLowerCutoff z := by
  fin_cases z <;>
    norm_num [baseSamplerProbabilityNumerator, baseSamplerProbabilityNumerators,
      baseSamplerUpperCutoff, baseSamplerLowerCutoff, baseSamplerCutoffs,
      baseSamplerReverseCumulativeThresholds]

private theorem baseSamplerUpperCutoff_le (z : BaseSamplerOutput) :
    baseSamplerUpperCutoff z ≤ 2 ^ 72 := by
  fin_cases z <;>
    norm_num [baseSamplerUpperCutoff, baseSamplerCutoffs,
      baseSamplerReverseCumulativeThresholds]

private theorem baseSamplerFromWord_eq_iff (u : ℕ) (hu : u < 2 ^ 72)
    (z : BaseSamplerOutput) :
    baseSamplerFromWord u = z ↔
      baseSamplerLowerCutoff z ≤ u ∧ u < baseSamplerUpperCutoff z := by
  change baseSamplerComparisonCount u = z.val ↔ _
  fin_cases z <;>
    simp only [baseSamplerComparisonCount, baseSamplerReverseCumulativeThresholds,
      List.countP_cons, List.countP_nil, decide_eq_true_eq, baseSamplerLowerCutoff,
      baseSamplerUpperCutoff, baseSamplerCutoffs]
  all_goals split_ifs <;> omega

private theorem baseSampler_fiber_card (z : BaseSamplerOutput) :
    Nat.card {u : Fin (2 ^ 72) // baseSamplerFromWord u.val = z} =
      baseSamplerProbabilityNumerator z := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfiber :
      (Finset.univ.filter (fun u : Fin (2 ^ 72) => baseSamplerFromWord u.val = z)).map
          Fin.valEmbedding =
        Finset.Ico (baseSamplerLowerCutoff z) (baseSamplerUpperCutoff z) := by
    ext u
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (baseSamplerFromWord_eq_iff v.val v.isLt z).mp hv
    · intro hu
      exact ⟨⟨u, hu.2.trans_le (baseSamplerUpperCutoff_le z)⟩,
        (baseSamplerFromWord_eq_iff u
          (hu.2.trans_le (baseSamplerUpperCutoff_le z)) z).mpr hu, rfl⟩
  rw [← Finset.card_map (f := Fin.valEmbedding), hfiber, Nat.card_Ico,
    baseSamplerProbabilityNumerator_eq_cutoff_sub]

/-- Algorithm 12 returns every `z ∈ {0, ..., 18}` with exact mass `pdt[z] / 2^72`. -/
theorem eval_baseSampler (z : BaseSamplerOutput) :
    ProbComp.eval baseSampler z =
      (baseSamplerProbabilityNumerator z : ENNReal) / 2 ^ 72 := by
  simp only [baseSampler, baseSamplerRandomBits, ProbComp.eval_map,
    ProbComp.eval_sampleBinaryNat, PMF.map_comp]
  rw [Cslib.Probability.PMF.uniformOfFintype_map_apply, Fintype.card_fin,
    baseSampler_fiber_card]

/-- Every Table 3.1 output has positive integer mass. -/
theorem baseSamplerProbabilityNumerator_pos (z : BaseSamplerOutput) :
    0 < baseSamplerProbabilityNumerator z := by
  fin_cases z <;>
    norm_num [baseSamplerProbabilityNumerator, baseSamplerProbabilityNumerators]

/-- Every value `0, ..., 18` occurs in the exact BaseSampler distribution. -/
@[simp] theorem support_baseSampler : (ProbComp.eval baseSampler).support = Set.univ := by
  ext z
  rw [Set.mem_univ, iff_true, PMF.mem_support_iff, eval_baseSampler]
  have hz := baseSamplerProbabilityNumerator_pos z
  positivity

end Cslib.Crypto.Falcon
