/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.SaksZhouSeed
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Packed queries for entries of the Saks–Zhou iteration

Each query selects a common hash-and-shift seed and two compact configuration IDs. Its value is
the final rounded numerator at that pair of IDs. The input word stays in a separate read-only
component. Out-of-range identifiers return zero.

## Main definitions

* `SaksZhouEntry` stores a seed and two binary compact identifiers.
* `saksZhouEntryValue` is the final rounded numerator requested by the query.

## Main results

* `sum_saksZhouBaseCounts_le` bounds the row numerators on the entire compact box.
* `saksZhouEntryValue_div` expresses the real rounded entry as the packed query's answer divided
  by its fixed-point denominator.

## Main definitions

* `SaksZhouEntry` contains the packed seed, row and column of a query.
* `saksZhouEntryValue` evaluates the final integer numerator for a query.

## Main results

* `saksZhouEntryValue_div` identifies each real entry with its dyadic numerator.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open Cslib.Probability.SaksZhou MultiTapeNTM.ConfigurationGraph MultiTapeTM Matrix

/-- The packed seed and the two compact configuration IDs of one rounded entry. -/
structure SaksZhouEntry where
  /-- Packed Toeplitz seed bits followed by the rounding shifts. -/
  seed : ℕ
  /-- Source ID of the requested matrix entry. -/
  row : ℕ
  /-- Destination ID of the requested matrix entry. -/
  column : ℕ

/-- Encodes the seed, row and column in binary, framing the first two fields in this order. -/
enc_structure encSaksZhouEntry : SaksZhouEntry logspace where
  seed : encNat, row : encNat, column : encNat

/-- The number of rounding rounds, also the depth of Nisan's generator within each round. -/
@[expose] def saksZhouLevels (clk n : ℕ) : ℕ := Nat.sqrt (clk * (Nat.log2 n + 2) + 1) + 1

/-- The number of fractional bits retained after each round. -/
@[expose] def saksZhouPrecision (clk n : ℕ) : ℕ := 5 * (clk * (Nat.log2 n + 2) + 1) + 5

variable {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State)

/-- At denominator `2^d` each of the two possible coin outcomes contributes `2^(d-1)` to
its successor. This matrix counts both outcomes when they have the same successor. -/
@[expose] noncomputable def saksZhouBaseCounts (d B : ℕ) (w : List Bool) :
    Matrix (Fin (vertexBound (k := k) B)) (Fin (vertexBound (k := k) B)) ℕ :=
  fun i j => coinCountWithSymbol M B w.length i j w[queryIndex (k := k) B i]? * 2 ^ (d - 1)

/-- With at least one fractional bit, the integer base counts at denominator `2 ^ d` represent
the normalized compact-configuration transition matrix. -/
theorem compactCoinMatrix_eq_saksZhouBaseCounts_div {d : ℕ} (hd : 0 < d) (B : ℕ) (w : List Bool)
    (u v : Fin (vertexBound (k := k) B)) :
    compactCoinMatrix M ℝ B w u v = (saksZhouBaseCounts M d B w u v : ℝ) / 2 ^ d := by
  have he : d - 1 + 1 = d := by omega
  simp only [compactCoinMatrix, saksZhouBaseCounts, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← he, pow_succ]
  simp only [Nat.add_sub_cancel]
  field_simp

/-- The dyadic base counts have total numerator at most `2 ^ d` for every compact identifier,
including unreachable or malformed identifiers. -/
theorem sum_saksZhouBaseCounts_le {d : ℕ} (hd : 0 < d) (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) : ∑ v, saksZhouBaseCounts M d B w u v ≤ 2 ^ d := by
  have h := compactCoinMatrix_mulVec_one_le (machine := M) (R := ℝ) B w u
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] at h
  simp_rw [compactCoinMatrix_eq_saksZhouBaseCounts_div M hd B w] at h
  rw [← Finset.sum_div, div_le_one (by positivity)] at h
  exact_mod_cast h

/-- Final integer numerator of the rounded Saks–Zhou iteration on the enumerated configuration
box, extended by zero to IDs beyond the box. -/
@[expose] noncomputable def saksZhouEntryValue (c clk : ℕ) (q : SaksZhouEntry × List Bool) : ℕ :=
  let w := q.2
  let B := radix (radixExponent State c) w.length
  let N := vertexBound (k := k) B
  let s := saksZhouLevels clk w.length
  let d := saksZhouPrecision clk w.length
  let b := 2 * (5 * d)
  let seed := nisanShiftSeedOfNat b s s d q.1.seed
  if hi : q.1.row < N then
    if hj : q.1.column < N then
      nisanSnapCounts (Equiv.refl _) b d s seed.1 (saksZhouBaseCounts M d B w)
        s seed.2 ⟨_, hi⟩ ⟨_, hj⟩
    else 0
  else 0

/-- On a seed packed from the low hash bits and the subsequent shifts, the real iterated entry
is exactly the queried numerator divided by the grid denominator. -/
theorem saksZhouEntryValue_div (c clk z : ℕ) (w : List Bool) :
    let B := radix (radixExponent State c) w.length
    let s := saksZhouLevels clk w.length
    let d := saksZhouPrecision clk w.length
    let b := 2 * (5 * d)
    let seed := nisanShiftSeedOfNat b s s d z
    ∀ i j : Fin (vertexBound (k := k) B),
      snapIter d (fun Q => bitNisanPow (Equiv.refl _) b s Q seed.1)
        (compactCoinMatrix M ℝ B w) s seed.2 i j =
          (saksZhouEntryValue M c clk (⟨z, i, j⟩, w) : ℝ) / 2 ^ d := by
  intro B s d b seed i j
  have hd : 0 < d := by simp only [d, saksZhouPrecision]; omega
  simp only [saksZhouEntryValue]
  split_ifs with hi hj
  · exact snapIter_bitNisanPow_eq_counts (Equiv.refl _) (by dsimp only [b]; omega : d ≤ b) seed.1
      _ _ (compactCoinMatrix_eq_saksZhouBaseCounts_div M hd B w) s seed.2 i j
  · exact (hj j.isLt).elim
  · exact (hi i.isLt).elim

end Turing.MultiTapePTM.ConfigurationGraph
