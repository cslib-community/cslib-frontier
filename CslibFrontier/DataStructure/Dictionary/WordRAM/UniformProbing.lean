/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.Spec
public import CslibFrontier.DataStructure.Dictionary.DoubleHashing
public import CslibFrontier.DataStructure.Dictionary.UniformProbing
public import CslibFrontier.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import CslibFrontier.Computability.WordRAM.ExactNotation
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega

/-!
# Self-Contained Open-Addressed Permutation-Probing Dictionary on the Word-RAM

This file implements a self-contained open-addressed permutation-probing dictionary realizing
`Cslib.DataStructure.Dictionary.spec U V n_max` (`query` and `insert` up to `n_max` distinct keys)
on the Word-RAM (`Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard`), combining the
power-of-two odd-stride double-hashing construction of
[Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition (MIT Press,
2009), Section 11.4, "Double hashing", pp. 269–277][CLRS2009], the `k`-wise independence double
hashing analysis of [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
Randomness*, STOC 1990, pp. 224–234; extended NYU Courant Technical Report `TR1995-687`, May 1995,
pp. 1–2, 4–7, 37–39][SchmidtSiegel1990], and Mikkel Thorup's Double Tabulation
([M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence*, FOCS
2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13][Thorup2013], Theorem 1(a) and Lemma 2).

## Design and reuse of `Cslib.DataStructure.Dictionary.UniformProbing` and `DoubleHashing`

In the ideal uniform-probing model (`CslibFrontier/DataStructure/Dictionary/UniformProbing.lean`),
each key
`u : Fin U` is assigned an independent random permutation `π u : Equiv.Perm (Fin m)`. Storing an
explicit table of `U` permutations requires `Ω(U)` words when `U = poly(n_max) ≫ n_max`.

To achieve a self-contained `O_{c_exp}(n_max + 1)`-word data structure with assumption-free
`O_{c_exp}(1)` expected operation time whenever `U ≤ max n_max 4 ^ c_exp`, we construct for each key
`u : Fin U` a full-cycle affine permutation of `m = 2 ^ M` slots
(`M = bucketBits n_max = Nat.clog 2 (32 * max n_max 4)`):
`probePerm θ u i = (h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M`, where `h₁(u) ∈ Fin (2 ^ M)` and
`h₂(u) ∈ Fin (2 ^ (M - 1))` are independent instances of Mikkel Thorup's Double Tabulation
(`Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation`, with `c = 2 * max c_exp 1`, `d = 8 * c`,
and `b = (1 + Nat.clog 2 (max n_max 4)) / 2`).

Because `2 * h₂(u) + 1` is always odd and therefore coprime to `2 ^ M`, `probePerm θ u` is a
bijection on `Fin (2 ^ M)` for **every** seed `θ` and key `u`
(`DoubleHashing.bijective_oddStrideSeq`).
We maintain `DoubleHashing.OrderedTableRep (probePerm θ)` on the concrete Word-RAM slot arrays and
bound the expected probe count by `probeBound c_exp n_max` across **all** capacities `n_max : ℕ`:
at most `3` probes once `doubleTabThreshold c_exp ≤ n_max`
(`DoubleHashing.expect_probeCount_oddStride_doubleTab_le`) and at most `doubleTabThreshold c_exp`
below it (`DoubleHashing.expect_probeCount_oddStride_unconditional_le`). This yields an
assumption-free expected operation charge `charge c_exp n_max`, which is at most the
`O_{c_exp}(1)` bound `expectedOpCharge c_exp` independent of `n_max` and `U`, and equals the
threshold-free `hashEvalSteps c_exp + 47` above the threshold, together with
`space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) = O_{c_exp}(n_max + 1)` words of memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.bucketBits`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.numBuckets`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.numChars`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.tupleLen`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.charBits`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.singleTabSpace`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.slotOffset`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.space`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.spaceFactor`: table dimension parameters
  and
  memory footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.Seed`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.seedLaw`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.primaryHash`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.rawStrideHash`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.strideHash`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.probePerm`: Double Tabulation seed space,
  uniform seed law, primary and odd-stride hashes, and full-cycle probe permutation.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.extractSlots`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.Rep`: slot-array extractor and Word-RAM
  representation invariant (`DoubleHashing.OrderedTableRep`).
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.allocSpan`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.initSetup`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.opCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.subroutineCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.probeBound`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.charge`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.expectedOpCharge`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.impl`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.implStandard`: structured Word-RAM
  programs and assumption-free `Randomized.StateTransitionImpl` certificates over `Basis.exact` and
  `Basis.standard`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.space_le`:
  `space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) = O_{c_exp}(n_max + 1)` across all `n_max`.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.setup_exec_spec`: randomized seed and table
  initialization in `setupSteps c_exp n_max = O_{c_exp}(n_max + 1)` instructions.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.opCode_execWithin`: every `query` or
  `insert` operation on key `u` executes in at most
  `opPathSteps c_exp θ T u = 13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8`
  instructions.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.seq_expected_amortized`: assumption-free
  expected operation time `charge c_exp n_max` across any admissible sequence
  `ops : List (Dictionary.Op U)` whenever `U ≤ max n_max 4 ^ c_exp`.
* `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.charge_le_expectedOpCharge`,
  `Cslib.DataStructure.Dictionary.WordRAM.UniformProbing.charge_of_le`: the charge is at most the
  `O_{c_exp}(1)` bound `expectedOpCharge c_exp` for every `n_max`, and equals
  `hashEvalSteps c_exp + 47` (at most `3` expected probes) once `doubleTabThreshold c_exp ≤ n_max`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
  Randomness*][SchmidtSiegel1990] (STOC 1990, pp. 224–234; NYU Courant Technical Report
  `TR1995-687`, May 1995, pp. 1–2, 4–7, 37–39)
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13)
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.WordRAM.UniformProbing

open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.DoubleHashing
open Cslib.DataStructure.Dictionary.UniformProbing
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation
open Cslib.Probability
open Cslib.WordRAM
open scoped BigOperators ENNReal

/-! ## Section 1: Table Parameters, Seed Space, and Full-Cycle Probe Permutations -/

/-- Log₂ of the power-of-2 table size: `M = ⌈log₂ (32 * max n_max 4)⌉ ≥ 7`. -/
def bucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

/-- Power-of-2 number of open-addressed table slots `m = 2 ^ bucketBits n_max ≥ 32 * max n_max 4`.
-/
def numBuckets (n_max : ℕ) : ℕ :=
  2 ^ bucketBits n_max

/-- Number of base-`2 ^ b` characters `c = 2 * max c_exp 1` for Double Tabulation under
`U ≤ max n_max 4 ^ c_exp`. -/
abbrev numChars (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableC c_exp

/-- Intermediate tuple length `d = 8 * numChars c_exp = 16 * max c_exp 1` for Double Tabulation. -/
abbrev tupleLen (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableD c_exp

/-- Character bit-width `b = (1 + Nat.clog 2 (max n_max 4)) / 2` for Double Tabulation. -/
abbrev charBits (n_max : ℕ) : ℕ :=
  DoubleTabulation.provableB n_max

/-- Memory footprint `(numChars c_exp + 1) * tupleLen c_exp * 2 ^ charBits n_max` words of a single
Double Tabulation table (`T₁` and `T₂`). -/
def singleTabSpace (c_exp n_max : ℕ) : ℕ :=
  DoubleTabulation.space (numChars c_exp) (tupleLen c_exp) (charBits n_max)

/-- Offset `2 * singleTabSpace c_exp n_max` of the open-addressed slot arrays relative to `base`
(after the primary hash table at `[base, base + singleTabSpace c_exp n_max)` and the stride hash
table at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`). -/
def slotOffset (c_exp n_max : ℕ) : ℕ :=
  2 * singleTabSpace c_exp n_max

/-- Total memory footprint `slotOffset c_exp n_max + 3 * numBuckets n_max` words in
`[base, base + space c_exp n_max)`. -/
def space (c_exp n_max : ℕ) : ℕ :=
  slotOffset c_exp n_max + 3 * numBuckets n_max

/-- Explicit `O_{c_exp}(1)` linear-space factor bounding `space c_exp n_max` by
`spaceFactor c_exp * (n_max + 1)` across every `n_max : ℕ`. -/
def spaceFactor (c_exp : ℕ) : ℕ :=
  32 * (numChars c_exp + 1) * tupleLen c_exp + 768

theorem seven_le_bucketBits (n_max : ℕ) : 7 ≤ bucketBits n_max := by
  dsimp only [bucketBits]
  calc
    7 = Nat.clog 2 (2 ^ 7) := (Nat.clog_pow 2 7 (by decide)).symm
    _ ≤ Nat.clog 2 (32 * max n_max 4) := Nat.clog_mono_right 2 (by omega)

theorem two_le_bucketBits (n_max : ℕ) : 2 ≤ bucketBits n_max :=
  le_trans (by decide : 2 ≤ 7) (seven_le_bucketBits n_max)

theorem bucketBits_pos (n_max : ℕ) : 0 < bucketBits n_max :=
  lt_of_lt_of_le (by decide : 0 < 7) (seven_le_bucketBits n_max)

theorem thirtyTwo_mul_max_le_numBuckets (n_max : ℕ) :
    32 * max n_max 4 ≤ numBuckets n_max :=
  Nat.le_pow_clog (by decide) (32 * max n_max 4)

theorem four_le_numBuckets (n_max : ℕ) : 4 ≤ numBuckets n_max := by
  have := thirtyTwo_mul_max_le_numBuckets n_max; omega

theorem four_mul_le_numBuckets (n_max : ℕ) : 4 * n_max ≤ numBuckets n_max := by
  have := thirtyTwo_mul_max_le_numBuckets n_max; omega

theorem two_mul_le_numBuckets (n_max : ℕ) : 2 * n_max ≤ numBuckets n_max := by
  have := four_mul_le_numBuckets n_max; omega

theorem lt_numBuckets (n_max : ℕ) : n_max < numBuckets n_max := by
  have := thirtyTwo_mul_max_le_numBuckets n_max; omega

theorem numBuckets_pos (n_max : ℕ) : 0 < numBuckets n_max :=
  lt_of_lt_of_le (by decide : 0 < 4) (four_le_numBuckets n_max)

instance instNonemptyFinNumBuckets (n_max : ℕ) : Nonempty (Fin (numBuckets n_max)) :=
  ⟨⟨0, numBuckets_pos n_max⟩⟩

theorem numBuckets_le_mul_add_one (n_max : ℕ) :
    numBuckets n_max ≤ 256 * (n_max + 1) := by
  have hclog := Nat.clog_le_of_le_pow
    (le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (32 * max n_max 4)))
  have hlog := Nat.pow_log_le_self 2 (show 32 * max n_max 4 ≠ 0 by omega)
  have hpow : numBuckets n_max ≤ 2 * 2 ^ Nat.log 2 (32 * max n_max 4) := by
    calc numBuckets n_max ≤ 2 ^ (Nat.log 2 (32 * max n_max 4) + 1) :=
          Nat.pow_le_pow_right (by decide) hclog
      _ = 2 * 2 ^ Nat.log 2 (32 * max n_max 4) := by ring
  omega

/-- **All-`n_max` linear space bound (`O_{c_exp}(n_max + 1)`)**:
for every `c_exp, n_max : ℕ`, `space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1)`. -/
theorem space_le (c_exp n_max : ℕ) :
    space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) := by
  have h4 := DoubleTabulation.two_pow_provableB_le n_max
  have htab : singleTabSpace c_exp n_max ≤
      16 * (numChars c_exp + 1) * tupleLen c_exp * (n_max + 1) := by
    calc singleTabSpace c_exp n_max
        ≤ (numChars c_exp + 1) * tupleLen c_exp * (16 * (n_max + 1)) :=
          Nat.mul_le_mul_left _ (by dsimp only [charBits]; omega)
      _ = 16 * (numChars c_exp + 1) * tupleLen c_exp * (n_max + 1) := by ring
  have hbuck := numBuckets_le_mul_add_one n_max
  dsimp only [space, slotOffset, spaceFactor]
  nlinarith

/-- Combined Double Tabulation seed `DoubleHashSeed c_exp n_max (bucketBits n_max)` consisting of
the primary hash seed `(T₁, T₂)` and the half-range stride hash seed `(S₁, S₂)`. -/
abbrev Seed (c_exp n_max : ℕ) : Type :=
  DoubleHashing.DoubleHashSeed c_exp n_max (bucketBits n_max)

/-- Uniform reference distribution over `Seed c_exp n_max`. -/
noncomputable def seedLaw (c_exp n_max : ℕ) : PMF (Seed c_exp n_max) :=
  PMF.uniformOfFintype (Seed c_exp n_max)

/-- Double Tabulation primary slot `h₁(u) ∈ Fin (numBuckets n_max)`. -/
def primaryHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (numBuckets n_max) :=
  match θ with
  | ((T₁, T₂), _) =>
    doubleTabHash (numChars c_exp) (tupleLen c_exp) (charBits n_max) U (bucketBits n_max)
      T₁ T₂ u

/-- Double Tabulation half-range stride index `h₂(u) ∈ Fin (2 ^ (bucketBits n_max - 1))`. -/
def rawStrideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (2 ^ (bucketBits n_max - 1)) :=
  match θ with
  | (_, (S₁, S₂)) =>
    doubleTabHash (numChars c_exp) (tupleLen c_exp) (charBits n_max) U
      (bucketBits n_max - 1) S₁ S₂ u

theorem two_mul_rawStrideHash_add_one_lt {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    2 * (rawStrideHash θ u).val + 1 < numBuckets n_max := by
  have := (rawStrideHash θ u).isLt
  have : 2 * 2 ^ (bucketBits n_max - 1) = numBuckets n_max := by
    rw [numBuckets, ← pow_succ', Nat.sub_add_cancel (bucketBits_pos n_max)]
  omega

/-- Odd probe stride `2 * (rawStrideHash θ u).val + 1 ∈ Fin (numBuckets n_max)`. -/
def strideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (numBuckets n_max) :=
  ⟨2 * (rawStrideHash θ u).val + 1, two_mul_rawStrideHash_add_one_lt θ u⟩

@[simp]
theorem val_strideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    (strideHash θ u).val = 2 * (rawStrideHash θ u).val + 1 :=
  rfl

/-- Full-cycle double-hashing probe permutation
`probePerm θ u : Equiv.Perm (Fin (numBuckets n_max))` sending probe index `i` to
`(h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M`. -/
noncomputable def probePerm {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Equiv.Perm (Fin (numBuckets n_max)) :=
  DoubleHashing.doubleHashOddStridePerm c_exp n_max U (bucketBits n_max) θ u

@[simp]
theorem val_probePerm {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U)
    (i : Fin (numBuckets n_max)) :
    (probePerm θ u i).val =
      ((primaryHash θ u).val + i.val * (strideHash θ u).val) % numBuckets n_max := by
  rcases θ with ⟨⟨T₁, T₂⟩, ⟨S₁, S₂⟩⟩
  rw [probePerm, DoubleHashing.doubleHashOddStridePerm, DoubleHashing.doubleTabOddStridePerm,
    DoubleHashing.twoStageOddStridePerm_apply]
  exact DoubleHashing.val_oddStridePerm _ _ u i

@[simp]
theorem probePerm_zero {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    probePerm θ u ⟨0, numBuckets_pos n_max⟩ = primaryHash θ u :=
  Fin.ext (by simpa [val_probePerm] using Nat.mod_eq_of_lt (primaryHash θ u).isLt)

/-- One step of the Word-RAM probe loop `(slot + stride) &&& (2 ^ M - 1)` advances from
`probePerm θ u ⟨i, _⟩` to `probePerm θ u ⟨i + 1, _⟩`. -/
private theorem val_probePerm_succ {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U)
    {i : ℕ} (hi : i + 1 < numBuckets n_max) :
    (probePerm θ u ⟨i + 1, hi⟩).val =
      ((probePerm θ u ⟨i, by omega⟩).val + (strideHash θ u).val) &&&
        (numBuckets n_max - 1) := by
  have hm : numBuckets n_max - 1 = 2 ^ bucketBits n_max - 1 := rfl
  rw [hm, Nat.and_two_pow_sub_one_eq_mod, val_probePerm, val_probePerm]
  simp [numBuckets, Nat.add_mul, one_mul, Nat.add_assoc]

/-! ## Section 2: Concrete Slot Extraction and Representation Invariant -/

/-- Well-formedness of the flat open-addressed slot arrays at
`[base + slotOffset c_exp n_max, base + slotOffset c_exp n_max + 3 * numBuckets n_max)`:
each `used[j]` word is `0` or `1`, and whenever `used[j] = 1`, `key[j] < U`. -/
def SlotArrayWF (base c_exp U n_max : ℕ) (mem : ℕ → ℕ) : Prop :=
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  ∀ j : Fin m,
    (mem (sBase + j.val) = 0 ∨ mem (sBase + j.val) = 1) ∧
    (mem (sBase + j.val) = 1 → mem (sBase + m + j.val) < U)

/-- Extract the abstract open-addressed table `UniformProbing.Table U (numBuckets n_max)` from
Word-RAM memory `mem`. -/
def extractSlots (base c_exp U n_max : ℕ) (mem : ℕ → ℕ) :
    UniformProbing.Table U (numBuckets n_max) :=
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  fun j =>
    if mem (sBase + j.val) = 0 then none
    else if h : mem (sBase + m + j.val) < U then
      some (⟨mem (sBase + m + j.val), h⟩, mem (sBase + 2 * m + j.val))
    else none

theorem extractSlots_eq_none_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (j : Fin (numBuckets n_max)) :
    extractSlots base c_exp U n_max mem j = none ↔
      mem (base + slotOffset c_exp n_max + j.val) = 0 := by
  rcases hwf j with ⟨h0 | h1, hkey⟩ <;> simp [extractSlots, *]

theorem extractSlots_eq_some_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (j : Fin (numBuckets n_max))
    (u : Fin U) (v : ℕ) :
    extractSlots base c_exp U n_max mem j = some (u, v) ↔
      mem (base + slotOffset c_exp n_max + j.val) = 1 ∧
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) = u.val ∧
      mem (base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val) = v := by
  rcases hwf j with ⟨h0 | h1, hkey⟩ <;> simp [extractSlots, Fin.ext_iff, *]

attribute [local wram_arith] slotOffset space

local macro "layout_omega" : tactic => `(tactic| first | omega | wram_omega)

/-- Every slot-array cell (`k ∈ {0, 1, 2}` for `used`, `key`, `val`) lies in the allocated
footprint `[base, base + space c_exp n_max)`. -/
private theorem slotAddr_mem_footprint {base c_exp n_max : ℕ} (k : ℕ) (hk : k < 3)
    (j : Fin (numBuckets n_max)) :
    base + slotOffset c_exp n_max + k * numBuckets n_max + j.val ∈
      (Block.mk base (space c_exp n_max)).footprint := by
  have := j.isLt
  have hk_mul : k * numBuckets n_max ≤ 2 * numBuckets n_max :=
    Nat.mul_le_mul_right _ (by omega)
  exact Block.mem_footprint.mpr ⟨by wram_omega, by wram_omega [hk_mul]⟩

theorem mem_otherOccupiedSlots_extractSlots_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (u : Fin U) (j : Fin (numBuckets n_max)) :
    j ∈ otherOccupiedSlots (extractSlots base c_exp U n_max mem) u ↔
      mem (base + slotOffset c_exp n_max + j.val) = 1 ∧
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) ≠ u.val := by
  rw [mem_otherOccupiedSlots_iff]
  refine ⟨fun ⟨u', v', hsome, hne⟩ => ?_, fun ⟨h1, hne⟩ => ?_⟩
  · rcases (extractSlots_eq_some_iff hwf j u' v').mp hsome with ⟨h1, hkey, _⟩
    exact ⟨h1, hkey ▸ Fin.val_ne_of_ne hne⟩
  · refine ⟨⟨_, (hwf j).2 h1⟩, _, (extractSlots_eq_some_iff hwf _ _ _).mpr ⟨h1, rfl, rfl⟩,
      fun heq => hne (congrArg Fin.val heq)⟩

/-- Coupled representation invariant `Rep w base c_exp U V n_max θ s x` on `Data 16`:
* `x.Bounded w`;
* `x.regs 0 = base`;
* `DoubleTabulation.SeedRep` holds for `θ.1` at `[base, base + singleTabSpace c_exp n_max)` and
  for `θ.2` at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`;
* `SlotArrayWF base c_exp U n_max x.mem` and
  `DoubleHashing.OrderedTableRep (probePerm θ) s (extractSlots base c_exp U n_max x.mem)` hold on
  the slot arrays;
* `(Dictionary.dom s).card ≤ n_max` and `Dictionary.ValuesBounded V s`. -/
structure Rep (w base c_exp U V n_max : ℕ) (θ : Seed c_exp n_max) (s : Dictionary.State U)
    (x : Data 16) : Prop where
  bounded : x.Bounded w
  regs_base : x.regs 0 = base
  primary_rep : DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
    (bucketBits n_max) θ.1 x.mem
  stride_rep : DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp)
    (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) θ.2 x.mem
  slot_wf : SlotArrayWF base c_exp U n_max x.mem
  table_rep : DoubleHashing.OrderedTableRep (probePerm θ) s
    (extractSlots base c_exp U n_max x.mem)
  dom_le : (Dictionary.dom s).card ≤ n_max
  vals_bounded : Dictionary.ValuesBounded V s

theorem Rep.unique {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s₁ s₂ : Dictionary.State U} {x : Data 16}
    (h₁ : Rep w base c_exp U V n_max θ s₁ x) (h₂ : Rep w base c_exp U V n_max θ s₂ x) :
    s₁ = s₂ := by
  funext u
  rcases h : s₁ u with _ | v₁
  · rcases h' : s₂ u with _ | v₂
    · rfl
    · obtain ⟨_, hT⟩ := h₂.table_rep.toTableRep.key_spec u v₂ h'
      exact h.symm.trans (h₁.table_rep.toTableRep.slot_spec _ u v₂ hT).1
  · obtain ⟨_, hT⟩ := h₁.table_rep.toTableRep.key_spec u v₁ h
    exact (h₂.table_rep.toTableRep.slot_spec _ u v₁ hT).1.symm

theorem SlotArrayWF.congr_mem {base c_exp U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, mem' a = mem a)
    (hwf : SlotArrayWF base c_exp U n_max mem) :
    SlotArrayWF base c_exp U n_max mem' := fun j => by
  simpa only [SlotArrayWF,
    hmem _ (by simpa using slotAddr_mem_footprint (base := base) (c_exp := c_exp) 0 (by decide) j),
    hmem _ (by simpa using slotAddr_mem_footprint (base := base) (c_exp := c_exp) 1 (by decide) j)]
    using hwf j

theorem extractSlots_congr_mem {base c_exp U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, mem' a = mem a) :
    extractSlots base c_exp U n_max mem' = extractSlots base c_exp U n_max mem := by
  funext j
  simp only [extractSlots,
    hmem _ (by simpa using slotAddr_mem_footprint (base := base) (c_exp := c_exp) 0 (by decide) j),
    hmem _ (by simpa using slotAddr_mem_footprint (base := base) (c_exp := c_exp) 1 (by decide) j),
    hmem _ (slotAddr_mem_footprint 2 (by decide) j)]

theorem Rep.congr {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max} {s : Dictionary.State U}
    {x x' : Data 16}
    (hbdd : x'.Bounded w) (hbase : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x'.mem a = x.mem a)
    (hrep : Rep w base c_exp U V n_max θ s x) :
    Rep w base c_exp U V n_max θ s x' := by
  have hst : DoubleTabulation.space (numChars c_exp) (tupleLen c_exp) (charBits n_max) =
      singleTabSpace c_exp n_max := rfl
  have htab : ∀ a, base ≤ a → a < base + 2 * singleTabSpace c_exp n_max → x'.mem a = x.mem a :=
    fun a hlo hhi => hmem a (Block.mem_footprint.mpr ⟨hlo, by wram_omega⟩)
  exact ⟨hbdd, hbase.trans hrep.regs_base,
    hrep.primary_rep.congr_mem fun a hlo hhi => htab a hlo (by omega),
    hrep.stride_rep.congr_mem fun a hlo hhi => htab a (by omega) (by omega),
    hrep.slot_wf.congr_mem hmem, extractSlots_congr_mem hmem ▸ hrep.table_rep,
    hrep.dom_le, hrep.vals_bounded⟩

private theorem slotArrayWF_of_zero {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset c_exp n_max + j.val) = 0) :
    SlotArrayWF base c_exp U n_max mem :=
  fun j => ⟨.inl (hz j), by rw [hz j]; omega⟩

private theorem extractSlots_eq_emptyTable_of_zero {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset c_exp n_max + j.val) = 0) :
    extractSlots base c_exp U n_max mem = emptyTable U (numBuckets n_max) := by
  funext j
  simp [extractSlots, emptyTable, hz j]

/-! ## Section 3: Register Layout, Allocation, and Randomized Initialization -/

/-- Register `0` (`baseReg`, persistent): holds the base memory address `base`. -/
abbrev regBase : Fin 16 := 0

/-- Register `1` (`curReg`): loop condition / Double Tabulation key input. -/
abbrev regCond : Fin 16 := 1

/-- Register `2` (`zeroReg`): memory address / Double Tabulation output. -/
abbrev regAddr : Fin 16 := 2

/-- Register `3` (`oneReg`): current probe slot `slot ∈ Fin (numBuckets n_max)`. -/
abbrev regSlot : Fin 16 := 3

/-- Register `4`: slot array base address `base + slotOffset c_exp n_max`. -/
abbrev regSlotBase : Fin 16 := 4

/-- Register `5`: bucket mask `numBuckets n_max - 1`. -/
abbrev regMaskM : Fin 16 := 5

/-- Register `6`: odd probe stride `strideHash θ u`. -/
abbrev regStride : Fin 16 := 6

/-- Register `7`: table size `numBuckets n_max`. -/
abbrev regM : Fin 16 := 7

/-- Register `8`: constant `0` during probing / general scratch. -/
abbrev regZero : Fin 16 := 8

/-- Register `12` (`output`): operation tag (`0` for `query`, `1` for `insert`) on input; decoded
return value (`0` for `none`/`()`, `v + 1` for `some v`) on output. -/
abbrev regOp : Fin 16 := 12

/-- Register `13`: input key `u.val < U`. -/
abbrev regU : Fin 16 := 13

/-- Register `14` (`frontierReg`): input value `v < V` for `insert` / allocation frontier. -/
abbrev regV : Fin 16 := 14

/-- Register `15`: temporary register saving `primaryHash θ u` across the second hash evaluation. -/
abbrev regSave : Fin 16 := 15

/-- Register injection `Fin 12 → Fin 16` embedding `DoubleTabulation` into registers `0..11`
(preserving `regOp = 12`, `regU = 13`, `regV = 14`, `regSave = 15`). -/
def dtMap : Fin 12 → Fin 16 :=
  Fin.castLE (by decide)

private theorem injective_dtMap : Function.Injective dtMap :=
  Fin.castLE_injective _

/-- Allocation program `allocSpan c_exp n_max` (`3` instructions): copies `frontierReg` (`regV`) to
`baseReg` (`regBase`) and advances `frontierReg` by `space c_exp n_max`. -/
def allocSpan (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regBase regV))
  (.seq (.op (.const regCond (space c_exp n_max)))
        (.op (.exactBin .add regV regBase regCond)))

theorem allocSpan_execWithin {w base c_exp n_max : ℕ} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hfr : x.regs regV = base) :
    ∃ x₁ : Data 16,
      ExecWithin w (allocSpan c_exp n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs regBase = base ∧
      x₁.regs regV = base + space c_exp n_max := by
  wram_exec [allocSpan, hfr]
  wram_simp

private theorem fits_of_space {w base c_exp n_max : ℕ} (hS : Fits w (base + space c_exp n_max)) :
    Fits w (base + singleTabSpace c_exp n_max) ∧
    Fits w (base + singleTabSpace c_exp n_max + singleTabSpace c_exp n_max) ∧
    Fits w (2 ^ charBits n_max) ∧
    Fits w (2 ^ charBits n_max - 1) ∧
    Fits w (2 ^ bucketBits n_max) ∧
    Fits w (2 ^ bucketBits n_max - 1) ∧
    Fits w (2 ^ (bucketBits n_max - 1)) ∧
    Fits w (2 ^ (bucketBits n_max - 1) - 1) ∧
    Fits w 1 := by
  have hd : 1 ≤ tupleLen c_exp := by
    have := DoubleTabulation.one_le_provableC c_exp
    dsimp only [tupleLen, DoubleTabulation.provableD]; omega
  have hpowB_le : 2 ^ charBits n_max ≤ singleTabSpace c_exp n_max :=
    (one_mul _).symm.trans_le <| Nat.mul_le_mul_right _ <|
      Nat.mul_pos (Nat.succ_pos _) hd
  have hM1_le : 2 ^ (bucketBits n_max - 1) ≤ numBuckets n_max :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ 1)
  have h4 := four_le_numBuckets n_max
  have hM : 2 ^ bucketBits n_max = numBuckets n_max := rfl
  exact ⟨hS.of_le (by wram_omega), hS.of_le (by wram_omega), hS.of_le (by wram_omega),
    hS.of_le (by wram_omega), hS.of_le (by wram_omega), hS.of_le (by wram_omega),
    hS.of_le (by wram_omega), hS.of_le (by wram_omega), hS.of_le (by wram_omega)⟩

/-- Deterministic 2-instruction glue advancing `regBase` by `singleTabSpace c_exp n_max`. -/
def initMidCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
        (.op (.exactBin .add regBase regBase regCond))

/-- Closed-form machine state after `initMidCode c_exp n_max`. -/
private def initMidData (base c_exp n_max : ℕ) (d : Data 16) : Data 16 :=
  (d.set regCond (singleTabSpace c_exp n_max)).set regBase (base + singleTabSpace c_exp n_max)

/-- Deterministic 2-instruction glue restoring `regBase` from `base + singleTabSpace c_exp n_max`
back to `base`. -/
def initPostCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
        (.op (.exactBin .sub regBase regBase regCond))

/-- Closed-form machine state after `initPostCode c_exp n_max`. -/
private def initPostData (base c_exp n_max : ℕ) (d : Data 16) : Data 16 :=
  (d.set regCond (singleTabSpace c_exp n_max)).set regBase base

/-- Complete randomized setup program `initSetup c_exp n_max`: resamples the primary Double
Tabulation seed at `[base, base + singleTabSpace c_exp n_max)` and the stride Double Tabulation
seed at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`. -/
def initSetup (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max)).rename dtMap)
  (.seq (initMidCode c_exp n_max)
  (.seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max - 1)).rename dtMap)
        (initPostCode c_exp n_max)))

/-- Total instruction count
`2 * resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) + 4` of
`initSetup c_exp n_max`. -/
def setupSteps (c_exp n_max : ℕ) : ℕ :=
  2 * DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) + 4

/-- Extract the combined seed `Seed c_exp n_max` from machine state `y`. -/
private def extractSeedPair (base c_exp n_max : ℕ) (y : Data 16) : Seed c_exp n_max :=
  (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      (bucketBits n_max) y.mem,
    DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
      (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem)

/-- Output state distribution of `DoubleTabulation.resampleCode` renamed into `Data 16` at
table address `addr` and output bit-width `M`. -/
private noncomputable def resampleInitPMF (addr c_exp n_max M : ℕ) (x : Data 16) : PMF (Data 16) :=
  (((fun z => (z.1.extend dtMap x, z.2)) <$>
    DoubleTabulation.resampleComp addr (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      M (x.comap dtMap)).eval).map Prod.fst

/-- Output state distribution of `initSetup c_exp n_max`. -/
private noncomputable def initSetupPMF (base c_exp n_max : ℕ) (x₁ : Data 16) : PMF (Data 16) :=
  (resampleInitPMF base c_exp n_max (bucketBits n_max) x₁).bind fun y₁ =>
    (resampleInitPMF (base + singleTabSpace c_exp n_max) c_exp n_max (bucketBits n_max - 1)
      (initMidData base c_exp n_max y₁)).map (initPostData base c_exp n_max)

/-- Coupled `(Seed × Data 16)` distribution produced by `initSetup c_exp n_max`. -/
private noncomputable def initSeedStatePMF (base c_exp n_max : ℕ) (x₁ : Data 16) :
    PMF (Seed c_exp n_max × Data 16) :=
  (initSetupPMF base c_exp n_max x₁).map fun y => (extractSeedPair base c_exp n_max y, y)

private theorem mem_support_resampleInitPMF {addr c_exp n_max M : ℕ} {x y : Data 16}
    (hbase : x.regs regBase = addr)
    (hy : y ∈ (resampleInitPMF addr c_exp n_max M x).support) :
    DoubleTabulation.SeedRep addr (numChars c_exp) (tupleLen c_exp) (charBits n_max) M
      (DoubleTabulation.extractSeed addr (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        M y.mem) y.mem ∧
    y.regs regBase = addr ∧
    y.regs regV = x.regs regV ∧
    (∀ a, a < addr ∨ addr + singleTabSpace c_exp n_max ≤ a → y.mem a = x.mem a) := by
  rw [resampleInitPMF, ProbComp.eval_map, PMF.map_comp] at hy
  supp_cases hy with ⟨z, hz, rfl⟩
  rw [ProbComp.support_eval] at hz
  obtain ⟨hbase', hrep, hframe, -⟩ := DoubleTabulation.mem_support_resampleComp hbase hz
  refine ⟨hrep, ?_, Data.extend_regs_of_notMem _ _
    (fun ⟨i, h⟩ => (by decide : ¬regV.val < 12) (congrArg Fin.val h ▸ i.isLt)), hframe⟩
  change ((z.1.extend dtMap x).comap dtMap).regs 0 = addr
  rwa [Data.comap_extend injective_dtMap]

private theorem map_extractSeed_resampleInitPMF (addr c_exp n_max M : ℕ) (x : Data 16) :
    (resampleInitPMF addr c_exp n_max M x).map
        (fun y => DoubleTabulation.extractSeed addr (numChars c_exp) (tupleLen c_exp)
          (charBits n_max) M y.mem) =
      PMF.uniformOfFintype
        (DoubleTabTopSeed (numChars c_exp) (tupleLen c_exp) (charBits n_max) ×
          DoubleTabBotSeed (tupleLen c_exp) (charBits n_max) M) := by
  dsimp only [resampleInitPMF]
  rw [ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  exact DoubleTabulation.map_extractSeed_eval_resampleComp
    addr (numChars c_exp) (tupleLen c_exp) (charBits n_max) M (x.comap dtMap)

private theorem resampleInit_execCodeDist {w addr c_exp n_max M : ℕ} {x : Data 16}
    (hbase : x.regs regBase = addr)
    (hfit_end : Fits w (addr + singleTabSpace c_exp n_max))
    (hfit_mask_b : Fits w (2 ^ charBits n_max - 1))
    (hfit_mask_M : Fits w (2 ^ M - 1)) (hfit_1 : Fits w 1) :
    ExecCodeDist w
      ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        M).rename dtMap) x (resampleInitPMF addr c_exp n_max M x)
      (DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max)) := by
  refine ExecCodeDist.of_execRand_le
    ((DoubleTabulation.resampleCode_execRand (x := x.comap dtMap) hbase hfit_end
      hfit_mask_b hfit_mask_M hfit_1).rename injective_dtMap) fun z hz => ?_
  supp_cases hz with ⟨z₀, hz₀, rfl⟩
  exact (DoubleTabulation.mem_support_resampleComp hbase hz₀).2.2.2.le

/-- **Exact uniformity of the sampled seed pair**: the seed marginal of `initSeedStatePMF` is the
exact product uniform distribution `seedLaw c_exp n_max`. -/
private theorem map_fst_initSeedStatePMF (base c_exp n_max : ℕ) (x₁ : Data 16) :
    (initSeedStatePMF base c_exp n_max x₁).map Prod.fst = seedLaw c_exp n_max := by
  have hstride (y₁ : Data 16) :
      ((resampleInitPMF (base + singleTabSpace c_exp n_max) c_exp n_max (bucketBits n_max - 1)
        (initMidData base c_exp n_max y₁)).map (initPostData base c_exp n_max)).map
          (extractSeedPair base c_exp n_max) =
        (PMF.uniformOfFintype _).map fun S =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp)
            (charBits n_max) (bucketBits n_max) y₁.mem, S) := by
    set μ := resampleInitPMF (base + singleTabSpace c_exp n_max) c_exp n_max
      (bucketBits n_max - 1) (initMidData base c_exp n_max y₁)
    have hcongr : (μ.map (initPostData base c_exp n_max)).map (extractSeedPair base c_exp n_max) =
        μ.map fun y =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp)
            (charBits n_max) (bucketBits n_max) y₁.mem,
           DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
            (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem) := by
      rw [PMF.map_comp]
      refine PMF.map_congr_on_support _ _ _ fun y hy => Prod.ext ?_ rfl
      have hfr := (mem_support_resampleInitPMF (by simp +decide [initMidData]) hy).2.2.2
      exact DoubleTabulation.extractSeed_congr_mem fun a _ hhi => hfr a (.inl hhi)
    rw [hcongr]
    change μ.map ((fun S => (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp)
      (charBits n_max) (bucketBits n_max) y₁.mem, S)) ∘
      fun y : Data 16 => DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max)
        (numChars c_exp) (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem) = _
    rw [← PMF.map_comp, map_extractSeed_resampleInitPMF]
  rw [initSeedStatePMF, PMF.map_comp]
  change (initSetupPMF base c_exp n_max x₁).map (extractSeedPair base c_exp n_max) = _
  simp_rw [initSetupPMF, PMF.map_bind, hstride]
  change (resampleInitPMF base c_exp n_max (bucketBits n_max) x₁).bind
      ((fun P => (PMF.uniformOfFintype _).map (P, ·)) ∘ fun y₁ => DoubleTabulation.extractSeed base
        (numChars c_exp) (tupleLen c_exp) (charBits n_max) (bucketBits n_max) y₁.mem) = _
  rw [← PMF.bind_map, map_extractSeed_resampleInitPMF]
  exact PMF.uniformOfFintype_prod _ _

private theorem initSetup_execCodeDist {w base c_exp n_max : ℕ} {x₁ : Data 16}
    (hbase : x₁.regs regBase = base) (hS : Fits w (base + space c_exp n_max)) :
    ExecCodeDist w (initSetup c_exp n_max) x₁ (initSetupPMF base c_exp n_max x₁)
      (setupSteps c_exp n_max) := by
  obtain ⟨hbt, hb2t, hst, hmb, _, hmM, _, hmM1, h1⟩ := fits_of_space hS
  have hfit_base : Fits w base := by fits
  unfold initSetup initMidCode initPostCode
  refine WP.Dist.execCodeDist ?_
  wram_rand_call (resampleInit_execCodeDist hbase hbt hmb hmM h1) with y₁ hy₁
  · wram_rand_exec [(mem_support_resampleInitPMF hbase hy₁).2.1]
    wram_rand_call (resampleInit_execCodeDist rfl hb2t hmb hmM1 h1) with y₃ hy₃
    · wram_rand_exec [(mem_support_resampleInitPMF rfl hy₃).2.1, Nat.add_sub_cancel base _]
    · exact ⟨(PMF.bind_pure_comp _ _).symm, by norm_cast⟩
  · dsimp only [initSetupPMF, initMidData, initPostData, setupSteps]
    exact ⟨rfl, by norm_cast; omega⟩

/-- Full `Randomized.StateTransitionImpl.setup_exec` certificate for `initSetup c_exp n_max`. -/
theorem setup_exec_spec {w base c_exp U V n_max : ℕ} {x₁ : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hx₁ : x₁.Bounded w) (hbase : x₁.regs regBase = base)
    (hfr : x₁.regs regV = base + space c_exp n_max)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (Seed c_exp n_max × Data 16),
      ExecCodeDist w (initSetup c_exp n_max) x₁ (ν₀.map Prod.snd) (setupSteps c_exp n_max) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw c_exp n_max θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs regV = base + space c_exp n_max ∧
        Rep w base c_exp U V n_max p.1 (Dictionary.empty U) p.2 ∧
        (0 : ℕ) ≤ 0 ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x₁.mem p.2.mem := by
  have hexec := initSetup_execCodeDist hbase hS
  refine ⟨initSeedStatePMF base c_exp n_max x₁,
    hexec.congr_dist (by rw [initSeedStatePMF, PMF.map_comp]; exact (PMF.map_id _).symm) le_rfl,
    fun θ => by rw [map_fst_initSeedStatePMF, one_mul], fun p hp => ?_⟩
  dsimp only [initSeedStatePMF] at hp
  supp_cases hp with ⟨y, hy, rfl⟩
  have hbdd_y : y.Bounded w := hexec.bounded hx₁ y hy
  dsimp only [initSetupPMF] at hy
  supp_cases hy with ⟨y₁, hy₁, y₃, hy₃, rfl⟩
  obtain ⟨hprim_rep₁, -, hv₁, hframe₁⟩ := mem_support_resampleInitPMF hbase hy₁
  obtain ⟨hstr_rep, -, hv₃, hframe₃⟩ :=
    mem_support_resampleInitPMF (by simp +decide [initMidData]) hy₃
  have hbelow : ∀ a < base + singleTabSpace c_exp n_max, y₃.mem a = y₁.mem a :=
    fun a h => hframe₃ a (.inl h)
  have hst : DoubleTabulation.space (numChars c_exp) (tupleLen c_exp) (charBits n_max) =
      singleTabSpace c_exp n_max := rfl
  have hprim_rep : DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp)
      (charBits n_max) (bucketBits n_max)
      (extractSeedPair base c_exp n_max (initPostData base c_exp n_max y₃)).1 y₃.mem := by
    change DoubleTabulation.SeedRep _ _ _ _ _ (DoubleTabulation.extractSeed _ _ _ _ _ y₃.mem) _
    rw [DoubleTabulation.extractSeed_congr_mem fun a _ h => hbelow a (hst ▸ h)]
    exact hprim_rep₁.congr_mem fun a _ h => hbelow a (hst ▸ h)
  have houtside : ∀ a, a < base ∨ base + slotOffset c_exp n_max ≤ a → y₃.mem a = x₁.mem a :=
    fun a ha => (hframe₃ a (by wram_omega)).trans (hframe₁ a (by wram_omega))
  have hz_slots : ∀ j : Fin (numBuckets n_max),
      y₃.mem (base + slotOffset c_exp n_max + j.val) = 0 := fun j =>
    (houtside _ (.inr (by omega))).trans (hz _ (by
      simpa using slotAddr_mem_footprint (base := base) (c_exp := c_exp) 0 (by omega) j))
  refine ⟨by simpa +decide [initPostData, initMidData, hv₁, hfr] using hv₃,
    ⟨hbdd_y, by simp +decide [initPostData], hprim_rep, hstr_rep,
      slotArrayWF_of_zero hz_slots,
      (extractSlots_eq_emptyTable_of_zero hz_slots).symm ▸ DoubleHashing.OrderedTableRep.empty _,
      by simp, Dictionary.valuesBounded_empty U V⟩,
    le_rfl, Modifies.block_iff.mpr fun a ha => houtside a (by wram_omega)⟩

/-! ## Section 4: Lookup and Insertion Operations (`opCode`) -/

/-- Probe inspection snippet `probeCheckCode` (`≤ 9` instructions): checks whether the slot in
`regSlot` belongs to `otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u` (i.e.,
`used[slot] = 1` and `key[slot] ≠ u.val`), storing `1` in `regCond` if so and `0` otherwise. -/
def probeCheckCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regCond 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regCond regAddr))
                (.branch (.eq regCond regU)
                  (.op (.const regCond 0))
                  (.op (.const regCond 1)))))))

private theorem probeCheckCode_execWithin {w base c_exp U n_max : ℕ} {d : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hwf : SlotArrayWF base c_exp U n_max d.mem)
    (u : Fin U) (slot : Fin (numBuckets n_max))
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot = slot.val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0)
    (hu : d.regs regU = u.val) :
    ∃ d' : Data 16,
      ExecWithin w probeCheckCode d d' 9 ∧
      d'.mem = d.mem ∧
      d'.regs regCond =
        (if slot ∈ otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u then 1 else 0) ∧
      ∀ r : Fin 16, r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
  have hslot_lt := slot.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have hused := (hwf slot).1
  have haddr : base + slotOffset c_exp n_max + slot.val + numBuckets n_max =
      base + slotOffset c_exp n_max + numBuckets n_max + slot.val := by omega
  wram_exec [probeCheckCode, hsbase, hslot, hm, hzero, hu, haddr]
  all_goals
    refine ⟨?_, ?_, fun r hr₁ hr₂ => ?_⟩
    all_goals wram_simp [mem_otherOccupiedSlots_extractSlots_iff hwf]
  all_goals split_ifs <;> omega

/-- One iteration of the probe loop (`≤ 11` instructions): advances `regSlot` by `regStride` modulo
`numBuckets n_max` (`regMaskM`) and runs `probeCheckCode`. -/
def probeStepCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regSlot regSlot regStride))
  (.seq (.op (.exactBin .and regSlot regSlot regMaskM))
        probeCheckCode)

/-- Probe loop: continues advancing `regSlot` while `0 < regCond` (i.e., while `regSlot` is occupied
by a key other than `u`). -/
def probeLoop : Code .exact 16 :=
  .loop (.lt regZero regCond) probeStepCode

private theorem probeLoop_execWithin_aux {w base c_exp U n_max : ℕ} (θ : Seed c_exp n_max)
    (hS : Fits w (base + space c_exp n_max))
    {mem : ℕ → ℕ} (hwf : SlotArrayWF base c_exp U n_max mem)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max mem) u).card < numBuckets n_max) :
    let T := extractSlots base c_exp U n_max mem
    let O := otherOccupiedSlots T u
    let k := missedProbes O (probePerm θ u)
    ∀ (rem i : ℕ) (hi_lt : i < numBuckets n_max) (d : Data 16),
      i + rem = k → d.mem = mem →
      d.regs regSlotBase = base + slotOffset c_exp n_max →
      d.regs regMaskM = numBuckets n_max - 1 →
      d.regs regStride = (strideHash θ u).val →
      d.regs regM = numBuckets n_max →
      d.regs regZero = 0 → d.regs regU = u.val →
      d.regs regSlot = (probePerm θ u ⟨i, hi_lt⟩).val →
      d.regs regCond = (if probePerm θ u ⟨i, hi_lt⟩ ∈ O then 1 else 0) →
      ∃ d' : Data 16,
        ExecWithin w probeLoop d d' (13 * rem + 2) ∧
        d'.mem = mem ∧
        d'.regs regSlot = (targetSlot (probePerm θ) T u hO).val ∧
        ∀ r : Fin 16, r ≠ regSlot → r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
  intro T O k rem
  have hk_lt : k < numBuckets n_max := missedProbes_lt_of_card_lt hO (probePerm θ u)
  induction rem with
  | zero =>
    intro i hi_lt d hik hmem _ _ _ _ hzero _ hslot hcond
    have hidx : (⟨i, hi_lt⟩ : Fin (numBuckets n_max)) = probeSlotIndex O (probePerm θ u) hO :=
      Fin.ext (by omega : i = k)
    have hnot : probePerm θ u ⟨i, hi_lt⟩ ∉ O := hidx ▸ notMem_apply_probeSlotIndex hO
    have hc : ¬(Cond.lt regZero regCond).Holds d := by simp [Cond.Holds, hzero, hcond, hnot]
    exact ⟨d, (Exec.loop_exit hc).within, hmem,
      hslot.trans (congrArg (fun j => (probePerm θ u j).val) hidx), fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    intro i hi_lt d hik hmem hsbase hmask hstride hm hzero hu hslot hcond
    have hi1_lt : i + 1 < numBuckets n_max := by omega
    have hmem_i : probePerm θ u ⟨i, hi_lt⟩ ∈ O :=
      mem_of_lt_probeSlotIndex hO (i := ⟨i, hi_lt⟩) (by
        change i < missedProbes O (probePerm θ u); omega)
    have hc : (Cond.lt regZero regCond).Holds d := by simp [Cond.Holds, hzero, hcond, hmem_i]
    have := (probePerm θ u ⟨i, hi_lt⟩).isLt
    have := (probePerm θ u ⟨i + 1, hi1_lt⟩).isLt
    have := (strideHash θ u).isLt
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    wram_exec (disch := first | fits | layout_omega)
      [probeStepCode, hslot, hstride, hmask, ← val_probePerm_succ θ u hi1_lt]
    wram_call (probeCheckCode_execWithin hS (by wram_simp [hmem]; exact hwf) u
      (probePerm θ u ⟨i + 1, hi1_lt⟩) (by wram_simp [hsbase]) (by wram_simp)
      (by wram_simp [hm]) (by wram_simp [hzero]) (by wram_simp [hu]))
      with s3 ⟨hs3_mem, hs3_cond, hs3_regs⟩
    wram_simp [hmem] at hs3_mem hs3_cond
    have hs3_frame : ∀ r : Fin 16, r ≠ regSlot → r ≠ regAddr → r ≠ regCond →
        s3.regs r = d.regs r := by
      intro r hr₁ hr₂ hr₃; rw [hs3_regs r hr₂ hr₃]; wram_simp
    have hs3_slot : s3.regs regSlot = (probePerm θ u ⟨i + 1, hi1_lt⟩).val := by
      rw [hs3_regs _ (by decide) (by decide)]; wram_simp
    have : (11 : ℕ) + (13 * rem + 2) ≤ 13 * (rem + 1) + 2 := by omega
    wram_call (ih (i + 1) hi1_lt s3 (by omega) hs3_mem
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) hs3_slot hs3_cond)
      with d' ⟨hd'_mem, hd'_slot, hd'_regs⟩
    exact ⟨by simp only [Nat.mul_add]; omega, hd'_mem, hd'_slot, by regs_frame⟩

/-- Deterministic 3-instruction glue between the primary and stride `DoubleTabulation.evalCode`
calls: saves `(primaryHash θ u).val` from `regAddr` into `regSave` and advances `regBase` by
`singleTabSpace c_exp n_max`. -/
def opMidEvalCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regSave regAddr))
  (.seq (.op (.const regAddr (singleTabSpace c_exp n_max)))
        (.op (.exactBin .add regBase regBase regAddr)))

/-- Deterministic 11-instruction glue after the stride `DoubleTabulation.evalCode` call:
restores `regBase = base`, forms `regStride = 2 * regAddr + 1`, restores `regSlot = regSave`,
and initializes `regSlotBase`, `regMaskM`, `regM`, and `regZero`. -/
def opPostEvalCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
  (.seq (.op (.exactBin .sub regBase regBase regCond))
  (.seq (.op (.const regCond 1))
  (.seq (.op (.exactBin .add regStride regAddr regAddr))
  (.seq (.op (.exactBin .add regStride regStride regCond))
  (.seq (.op (.copy regSlot regSave))
  (.seq (.op (.const regSlotBase (slotOffset c_exp n_max)))
  (.seq (.op (.exactBin .add regSlotBase regBase regSlotBase))
  (.seq (.op (.const regMaskM (numBuckets n_max - 1)))
  (.seq (.op (.const regM (numBuckets n_max)))
        (.op (.const regZero 0)))))))))))

/-- Hash evaluation and probe-register setup `opEvalHashesCode c_exp n_max`: evaluates
`primaryHash θ u` into `regSlot`, `strideHash θ u` into `regStride`, and initializes
`regSlotBase`, `regMaskM`, `regM`, and `regZero`. -/
def opEvalHashesCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regCond regU))
  (.seq ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename
          dtMap)
  (.seq (opMidEvalCode c_exp n_max)
  (.seq ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename
          dtMap)
        (opPostEvalCode c_exp n_max))))

/-- Exact deterministic instruction count
`2 * DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp) + 15 = O_{c_exp}(1)` of
`opEvalHashesCode c_exp n_max` (independent of `n_max` and `U`). -/
def hashEvalSteps (c_exp : ℕ) : ℕ :=
  2 * DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp) + 15

private theorem opEvalHashesCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hrep : Rep w base c_exp U V n_max θ s x) (u : Fin U)
    (hu_fit : Fits w u.val) (hu : x.regs regU = u.val) :
    ∃ d : Data 16,
      ExecWithin w (opEvalHashesCode c_exp n_max) x d (hashEvalSteps c_exp) ∧
      d.mem = x.mem ∧
      d.regs regBase = base ∧
      d.regs regSlot = (probePerm θ u ⟨0, numBuckets_pos n_max⟩).val ∧
      d.regs regSlotBase = base + slotOffset c_exp n_max ∧
      d.regs regMaskM = numBuckets n_max - 1 ∧
      d.regs regStride = (strideHash θ u).val ∧
      d.regs regM = numBuckets n_max ∧
      d.regs regZero = 0 ∧
      d.regs regOp = x.regs regOp ∧
      d.regs regU = u.val ∧
      d.regs regV = x.regs regV := by
  obtain ⟨hfit_btab, hfit_b2tab, hfit_powB, _, hfit_powM, hfit_mask_M, hfit_powM1, _, _⟩ :=
    fits_of_space hS
  have := two_mul_rawStrideHash_add_one_lt θ u
  have hval : (rawStrideHash θ u).val + (rawStrideHash θ u).val + 1 = (strideHash θ u).val := by
    rw [val_strideHash]; omega
  rcases θ with ⟨⟨T₁, T₂⟩, ⟨S₁, S₂⟩⟩
  refine WP.exists_execWithin (WP.Exact.toWP ?_)
  unfold opEvalHashesCode opMidEvalCode opPostEvalCode
  wram_exec [hu]
  wram_call (DoubleTabulation.evalCode_exec u (x := (x.set regCond u.val).comap dtMap)
    (by simp only [Data.comap_regs]; wram_simp; exact hrep.regs_base)
    (by simp only [Data.comap_regs]; wram_simp) hrep.primary_rep hfit_btab hfit_powB hfit_powM
    hu_fit) renamed injective_dtMap with yP ⟨⟨hyP_mem, hyP_base, hyP_key, hyP_out⟩, hyP_frame⟩
  change yP.regs regBase = base at hyP_base
  change yP.regs regAddr = (primaryHash ((T₁, T₂), (S₁, S₂)) u).val at hyP_out
  wram_exec (disch := first | fits | layout_omega) [hyP_base, hyP_out]
  wram_call (DoubleTabulation.evalCode_exec u
    (x := (((yP.set regSave (primaryHash ((T₁, T₂), (S₁, S₂)) u).val).set regAddr
      (singleTabSpace c_exp n_max)).set regBase
      (base + singleTabSpace c_exp n_max)).comap dtMap)
    (by simp only [Data.comap_regs]; wram_simp)
    (by simp only [Data.comap_regs]; wram_simp [hyP_key])
    (by simp only [Data.comap_mem, Data.set_mem, hyP_mem]; exact hrep.stride_rep)
    hfit_b2tab hfit_powB hfit_powM1 hu_fit)
    renamed injective_dtMap with yS ⟨⟨hyS_mem, hyS_base, -, hyS_out⟩, hyS_frame⟩
  change yS.regs regBase = base + singleTabSpace c_exp n_max at hyS_base
  change yS.regs regAddr = (rawStrideHash ((T₁, T₂), (S₁, S₂)) u).val at hyS_out
  wram_exec (disch := first | fits | layout_omega) [hyS_base, hyS_out, hyS_frame, hval]
  rw [probePerm_zero]
  wram_simp [hyS_frame, hyP_frame, hyS_mem, hyP_mem, hu, hashEvalSteps]
  omega

/-- Lookup completion program `finishQueryCode` (`≤ 9` instructions): inspects `used[regSlot]`;
if `0`, writes `0` (`none`) into `regOp`, and if `1`, loads `val[regSlot]` and writes
`val[regSlot] + 1` (`some v`) into `regOp`. -/
def finishQueryCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regOp 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regOp regAddr))
          (.seq (.op (.const regCond 1))
                (.op (.exactBin .add regOp regOp regCond))))))))

private theorem finishQueryCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x d : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hV : Fits w V)
    (hrep : Rep w base c_exp U V n_max θ s x)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot =
      (targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0) :
    ∃ y : Data 16,
      ExecWithin w finishQueryCode d y 9 ∧
      y.mem = x.mem ∧
      y.regs regBase = base ∧
      y.regs regOp = (match s u with | none => 0 | some v => v + 1) := by
  set slot := targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO
  have htarget := hrep.table_rep.toTableRep.apply_targetSlot u hO
  have hslot_lt := slot.isLt
  unfold finishQueryCode
  cases hsu : s u with
  | none =>
    have hused0 := (extractSlots_eq_none_iff hrep.slot_wf slot).mp (by simpa [hsu] using htarget)
    wram_exec (disch := first | fits | layout_omega) [hsbase, hslot, hmem, hused0, hzero, hbase]
    wram_simp [hmem, hbase]
  | some v =>
    obtain ⟨hused1, _, hval_eq⟩ :=
      (extractSlots_eq_some_iff hrep.slot_wf slot u v).mp (by simpa [hsu] using htarget)
    have hv_lt : v < V := hrep.vals_bounded u v hsu
    have haddr : base + slotOffset c_exp n_max + slot.val + numBuckets n_max + numBuckets n_max =
        base + slotOffset c_exp n_max + 2 * numBuckets n_max + slot.val := by omega
    wram_exec (disch := first | fits | layout_omega)
      [hsbase, hslot, hmem, hused1, hzero, hm, haddr, hval_eq, hbase]
    wram_simp [hmem, hbase]

/-- Insertion completion program `finishInsertCode` (`8` instructions): writes `used[regSlot] := 1`,
`key[regSlot] := regU`, `val[regSlot] := regV`, and sets `regOp := 0`. -/
def finishInsertCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.const regCond 1))
  (.seq (.op (.store regAddr regCond))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regU))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regV))
        (.op (.const regOp 0))))))))

/-- Memory update produced by writing `(1, u.val, v)` into `used`/`key`/`val` arrays at `slot`. -/
private def insertSlotMem (base c_exp n_max : ℕ) (mem : ℕ → ℕ)
    (slot : Fin (numBuckets n_max)) (u v : ℕ) : ℕ → ℕ :=
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  Function.update (Function.update (Function.update mem (sBase + slot.val) 1)
    (sBase + m + slot.val) u) (sBase + 2 * m + slot.val) v

private theorem insertSlotMem_eq_self_of_ne {base c_exp n_max : ℕ} {mem : ℕ → ℕ}
    {slot j : Fin (numBuckets n_max)} {u v : ℕ} (hjs : j ≠ slot) :
    let sBase := base + slotOffset c_exp n_max
    let m := numBuckets n_max
    let mem' := insertSlotMem base c_exp n_max mem slot u v
    mem' (sBase + j.val) = mem (sBase + j.val) ∧
    mem' (sBase + m + j.val) = mem (sBase + m + j.val) ∧
    mem' (sBase + 2 * m + j.val) = mem (sBase + 2 * m + j.val) := by
  have := slot.isLt; have := j.isLt; have := Fin.val_ne_of_ne hjs
  exact ⟨by update_simp [insertSlotMem], by update_simp [insertSlotMem],
    by update_simp [insertSlotMem]⟩

private theorem insertSlotMem_self {base c_exp n_max : ℕ} {mem : ℕ → ℕ}
    {slot : Fin (numBuckets n_max)} {u v : ℕ} :
    let sBase := base + slotOffset c_exp n_max
    let m := numBuckets n_max
    let mem' := insertSlotMem base c_exp n_max mem slot u v
    mem' (sBase + slot.val) = 1 ∧
    mem' (sBase + m + slot.val) = u ∧
    mem' (sBase + 2 * m + slot.val) = v := by
  have := numBuckets_pos n_max
  exact ⟨by update_simp [insertSlotMem], by update_simp [insertSlotMem],
    by update_simp [insertSlotMem]⟩

private theorem slotArrayWF_insertSlotMem {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (slot : Fin (numBuckets n_max))
    (u : Fin U) (v : ℕ) :
    SlotArrayWF base c_exp U n_max (insertSlotMem base c_exp n_max mem slot u.val v) := fun j => by
  rcases eq_or_ne j slot with rfl | hjs
  · obtain ⟨h0, h1, _⟩ := insertSlotMem_self (base := base) (c_exp := c_exp) (mem := mem)
      (slot := j) (u := u.val) (v := v)
    exact ⟨.inr h0, fun _ => h1.trans_lt u.isLt⟩
  · obtain ⟨h0, h1, _⟩ := insertSlotMem_eq_self_of_ne (base := base) (c_exp := c_exp) (mem := mem)
      (u := u.val) (v := v) hjs
    simpa only [SlotArrayWF, h0, h1] using hwf j

private theorem extractSlots_insertSlotMem {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (slot : Fin (numBuckets n_max))
    (u : Fin U) (v : ℕ) :
    extractSlots base c_exp U n_max (insertSlotMem base c_exp n_max mem slot u.val v) =
      Function.update (extractSlots base c_exp U n_max mem) slot (some (u, v)) := by
  funext j
  by_cases hjs : j = slot
  · subst hjs
    rw [Function.update_self, extractSlots_eq_some_iff (slotArrayWF_insertSlotMem hwf j u v)]
    exact insertSlotMem_self
  · have ⟨h0, h1, h2⟩ := insertSlotMem_eq_self_of_ne (base := base) (c_exp := c_exp) (mem := mem)
      (u := u.val) (v := v) hjs
    rw [Function.update_of_ne hjs]
    simp only [extractSlots, h0, h1, h2]

private theorem finishInsertCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x d : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hrep : Rep w base c_exp U V n_max θ s x)
    (u : Fin U) (v : ℕ)
    (hvalid : (Dictionary.spec U V n_max).valid s (.insert u v))
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot =
      (targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hu : d.regs regU = u.val)
    (hv : d.regs regV = v) :
    ∃ y : Data 16,
      ExecWithin w finishInsertCode d y 8 ∧
      y.regs regBase = base ∧
      y.regs regOp = 0 ∧
      DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        (bucketBits n_max) θ.1 y.mem ∧
      DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp) (tupleLen c_exp)
        (charBits n_max) (bucketBits n_max - 1) θ.2 y.mem ∧
      SlotArrayWF base c_exp U n_max y.mem ∧
      DoubleHashing.OrderedTableRep (probePerm θ) (Function.update s u (some v))
        (extractSlots base c_exp U n_max y.mem) ∧
      (Dictionary.dom (Function.update s u (some v))).card ≤ n_max ∧
      Dictionary.ValuesBounded V (Function.update s u (some v)) ∧
      Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  set slot := targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO
  have hslot_lt := slot.isLt
  have ha1 : base + slotOffset c_exp n_max + slot.val + numBuckets n_max =
      base + slotOffset c_exp n_max + numBuckets n_max + slot.val := by omega
  have ha2 : base + slotOffset c_exp n_max + numBuckets n_max + slot.val + numBuckets n_max =
      base + slotOffset c_exp n_max + 2 * numBuckets n_max + slot.val := by omega
  refine WP.exists_execWithin ?_
  wram_exec (disch := first | fits | layout_omega) [finishInsertCode,
    hsbase, hslot, hm, hu, hv, ha1, ha2]
  have hmem_eq : ((((((((d.set regAddr (base + slotOffset c_exp n_max + slot.val)).set regCond 1
      ).write (base + slotOffset c_exp n_max + slot.val) 1).set regAddr
      (base + slotOffset c_exp n_max + numBuckets n_max + slot.val)).write
      (base + slotOffset c_exp n_max + numBuckets n_max + slot.val) u.val).set regAddr
      (base + slotOffset c_exp n_max + 2 * numBuckets n_max + slot.val)).write
      (base + slotOffset c_exp n_max + 2 * numBuckets n_max + slot.val) v).set regOp 0).mem =
      insertSlotMem base c_exp n_max x.mem slot u.val v := by
    simp only [Data.set_mem, Data.write_mem, hmem]; rfl
  have hbelow : ∀ a < base + slotOffset c_exp n_max,
      insertSlotMem base c_exp n_max x.mem slot u.val v a = x.mem a :=
    fun a h => by update_simp [insertSlotMem]
  rw [hmem_eq]
  refine ⟨by wram_simp [hbase],
    by wram_simp,
    hrep.primary_rep.congr_mem fun a _ h =>
      hbelow a (by dsimp only [slotOffset, singleTabSpace] at h ⊢; omega),
    hrep.stride_rep.congr_mem fun a _ h =>
      hbelow a (by dsimp only [slotOffset, singleTabSpace] at h ⊢; omega),
    slotArrayWF_insertSlotMem hrep.slot_wf slot u v, ?_,
    Dictionary.card_dom_step_le_of_valid (V := V) hrep.dom_le (o := .insert u v) hvalid,
    Dictionary.valuesBounded_step_of_valid (n_max := n_max) hrep.vals_bounded
      (o := .insert u v) hvalid,
    Modifies.block_iff.mpr fun a ha => by
      dsimp only [space] at ha
      update_simp [insertSlotMem]⟩
  rw [extractSlots_insertSlotMem hrep.slot_wf slot u v,
    ← tableInsert_eq_update_targetSlot (numBuckets_pos n_max) (probePerm θ) _ u v hO]
  exact hrep.table_rep.tableInsert (numBuckets_pos n_max) u v hO

/-- Complete operation body `opCode c_exp n_max` for both `query` and `insert`. -/
def opCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (opEvalHashesCode c_exp n_max)
  (.seq probeCheckCode
  (.seq probeLoop
        (.branch (.eq regOp regZero) finishQueryCode finishInsertCode)))

/-- Exact pathwise instruction budget
`13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8` for `opCode c_exp n_max` on table
`T` and key `u`. -/
noncomputable def opPathSteps (c_exp U n_max : ℕ) (θ : Seed c_exp n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U) : ℕ :=
  13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8

/-- Worst-case instruction bound `13 * numBuckets n_max + hashEvalSteps c_exp + 8` for
`opCode`. -/
def opSteps (c_exp n_max : ℕ) : ℕ :=
  13 * numBuckets n_max + hashEvalSteps c_exp + 8

theorem opPathSteps_le_opSteps {c_exp U n_max : ℕ} (θ : Seed c_exp n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < numBuckets n_max) :
    opPathSteps c_exp U n_max θ T u ≤ opSteps c_exp n_max := by
  dsimp only [opPathSteps, opSteps, probeCount, unsuccessfulProbes]
  have hlt := missedProbes_lt_of_card_lt hO (probePerm θ u)
  omega

/-- Key extracted from a `Dictionary.Op U`. -/
def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .query u => u
  | .insert u _ => u

/-- Operation tag (`0` for `query`, `1` for `insert`). -/
def opTag {U : ℕ} : Dictionary.Op U → ℕ
  | .query _ => 0
  | .insert _ _ => 1

/-- Encoded output word in `regOp` after executing `op` from state `s`. -/
def opOutWord {U : ℕ} (s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .query u => match s u with | none => 0 | some v => v + 1
  | .insert _ _ => 0

/-- **Pathwise correctness and complexity of `opCode c_exp n_max`**: for any seed `θ`, dictionary
state `s`, machine state `x` satisfying `Rep w base c_exp U V n_max θ s x`, and admissible operation
`op`, `opCode c_exp n_max` halts deterministically in at most
`opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) (opKey op)`
`≤ opSteps c_exp n_max` instructions, preserving `Rep` for
`((Dictionary.spec U V n_max).stepFn s op).1`, writing `opOutWord s op` into `regOp`, and modifying
memory only within `[base, base + space c_exp n_max)`. -/
theorem opCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hV : Fits w V)
    (hrep : Rep w base c_exp U V n_max θ s x) (op : Dictionary.Op U)
    (hvalid : (Dictionary.spec U V n_max).valid s op)
    (hu_fit : Fits w (opKey op).val)
    (hop : x.regs regOp = opTag op)
    (hu : x.regs regU = (opKey op).val)
    (hv : ∀ u v, op = .insert u v → x.regs regV = v) :
    ∃ y : Data 16,
      ExecWithin w (opCode c_exp n_max) x y
        (opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) (opKey op)) ∧
      Rep w base c_exp U V n_max θ ((Dictionary.spec U V n_max).stepFn s op).1 y ∧
      y.regs regOp = opOutWord s op ∧
      Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  have hO :
      (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) (opKey op)).card <
        numBuckets n_max :=
    lt_of_le_of_lt (hrep.table_rep.toTableRep.card_otherOccupiedSlots_le (opKey op))
      (lt_of_le_of_lt hrep.dom_le (lt_numBuckets n_max))
  refine WP.exists_execWithin (WP.bounded hrep.bounded ?_)
  unfold opCode
  wram_call (opEvalHashesCode_execWithin hS hrep (opKey op) hu_fit hu) with d1
    ⟨hd1_mem, hd1_base, hd1_slot, hd1_sbase, hd1_mask, hd1_stride, hd1_m,
      hd1_zero, hd1_op, hd1_u, hd1_v⟩
  wram_call (probeCheckCode_execWithin hS (hd1_mem.symm ▸ hrep.slot_wf) (opKey op)
    (probePerm θ (opKey op) ⟨0, numBuckets_pos n_max⟩)
    hd1_sbase hd1_slot hd1_m hd1_zero hd1_u) with d2 ⟨hd2_mem, hd2_cond, hd2_regs⟩
  wram_call (probeLoop_execWithin_aux θ hS hrep.slot_wf (opKey op) hO _ 0 (numBuckets_pos n_max) d2
    (zero_add _) (by mem_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by rwa [hd1_mem] at hd2_cond))
    with d3 ⟨hd3_mem, hd3_slot, hd3_regs⟩
  have hd3_op : d3.regs regOp = opTag op := by regs_frame
  have hd3_zero : d3.regs regZero = 0 := by regs_frame
  cases op with
  | query u₀ =>
    wram_exec [hd3_op, hd3_zero, opTag]
    wram_call (finishQueryCode_execWithin hS hV hrep u₀ hO hd3_mem (by regs_frame)
      (by regs_frame) hd3_slot (by regs_frame) (by regs_frame)) with y ⟨hy_mem, hy_base, hy_op⟩
    intro hbdd
    exact ⟨by dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey]; omega,
      hrep.congr hbdd (hy_base.trans hrep.regs_base.symm) fun a _ => by rw [hy_mem],
      hy_op, fun a _ => hy_mem ▸ rfl⟩
  | insert u₀ v₀ =>
    have hv₀ : x.regs regV = v₀ := hv u₀ v₀ rfl
    wram_exec [hd3_op, hd3_zero, opTag]
    wram_call (finishInsertCode_execWithin hS hrep u₀ v₀ hvalid hO hd3_mem (by regs_frame)
      (by regs_frame) hd3_slot (by regs_frame) (by regs_frame) (by regs_frame))
      with y ⟨hy_base, hy_op, hy_prim, hy_str, hy_wf, hy_trep, hy_dom, hy_vals, hy_mod⟩
    intro hbdd
    exact ⟨by dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey]; omega,
      ⟨hbdd, hy_base, hy_prim, hy_str, hy_wf, hy_trep, hy_dom, hy_vals⟩, hy_op, hy_mod⟩

/-! ## Section 5: `SubroutineCode`, `StateTransitionImpl`, and Expected Probe / Collision Bounds -/

/-- Relocatable `SubroutineCode` over `Basis.exact` (`16` registers, `0` runtime init parameters)
for the open-addressed permutation-probing dictionary. -/
def subroutineCode (c_exp n_max : ℕ) : SubroutineCode .exact 16 0 where
  allocSpan := allocSpan c_exp n_max
  initSetup := initSetup c_exp n_max
  code := opCode c_exp n_max
  frontierReg := regV
  baseReg := regBase
  initParams := Fin.elim0
  curReg := regCond
  zeroReg := regAddr
  oneReg := regSlot
  incCur := .exactBin .add regCond regCond regSlot
  input := fun i => decide (i ≠ regBase)
  output := regOp

/-- Standalone argument encoder for `Dictionary.Op U` on `16` registers. -/
def encodeOp {U : ℕ} : Dictionary.Op U → Fin 16 → ℕ
  | .query u, i =>
      if i = regOp then 0
      else if i = regU then u.val
      else 0
  | .insert u v, i =>
      if i = regOp then 1
      else if i = regU then u.val
      else if i = regV then v
      else 0

/-- Partial argument-matching predicate for inline and standalone callers. -/
def argMatch {U : ℕ} (op : Dictionary.Op U) (regs : Fin 16 → ℕ) : Prop :=
  regs regOp = opTag op ∧
  regs regU = (opKey op).val ∧
  ∀ u v, op = .insert u v → regs regV = v

/-- Output decoder reading typed operation observations from final registers. -/
def decodeOp {U V n_max : ℕ} : (op : Dictionary.Op U) → (Fin 16 → ℕ) →
    Option ((Dictionary.spec U V n_max).Result op)
  | .query _, regs => some (if regs regOp = 0 then none else some (regs regOp - 1))
  | .insert _ _, _ => some ()

theorem encode_matches {c_exp U n_max : ℕ} (op : Dictionary.Op U) (regs : Fin 16 → ℕ) :
    argMatch op
      (fun i => if (subroutineCode c_exp n_max).input i then encodeOp op i else regs i) := by
  cases op with
  | query u =>
    exact ⟨rfl, by simp +decide [subroutineCode, encodeOp, opKey], fun _ _ h => nomatch h⟩
  | insert u v =>
    refine ⟨rfl, by simp +decide [subroutineCode, encodeOp, opKey], ?_⟩
    rintro _ _ ⟨⟩
    simp +decide [subroutineCode, encodeOp]

theorem arguments_fit {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val)
    (hV : Fits w V)
    {s : Dictionary.State U} (op : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s op)
    (i : Fin 16) :
    Fits w (encodeOp op i) := by
  have hfit1 : Fits w 1 := (fits_of_space hS).2.2.2.2.2.2.2.2
  cases op with
  | query u => dsimp only [encodeOp]; split_ifs <;> first | exact fits_zero w | exact hU_fit u
  | insert u v =>
    dsimp only [encodeOp]
    split_ifs <;> first | exact hfit1 | exact hU_fit u | exact hV.of_le hv.2.le | exact fits_zero w

private theorem decodeOp_eq_step {U V n_max : ℕ} {s : Dictionary.State U}
    (op : Dictionary.Op U) (regs : Fin 16 → ℕ)
    (h : regs regOp = opOutWord s op) :
    decodeOp (V := V) (n_max := n_max) op regs =
      some ((Dictionary.spec U V n_max).stepFn s op).2 := by
  cases op with
  | query u => cases hsu : s u <;> simp [decodeOp, Dictionary.spec, opOutWord, h, hsu]
  | insert u v => rfl

/-- Expected per-operation instruction charge
`13 * doubleTabThreshold c_exp + hashEvalSteps c_exp + 8 = O_{c_exp}(1)` for both `query` and
`insert` (independent of `n_max` and `U`). It bounds `charge c_exp n_max` at every capacity
(`charge_le_expectedOpCharge`). -/
def expectedOpCharge (c_exp : ℕ) : ℕ :=
  13 * doubleTabThreshold c_exp + hashEvalSteps c_exp + 8

/-- Expected probe-count bound at capacity `n_max`: `3` once `doubleTabThreshold c_exp ≤ n_max`
(`DoubleHashing.expect_probeCount_oddStride_doubleTab_le`), and below the threshold the cap
`doubleTabThreshold c_exp` on the deterministic probe count `n_max + 1`. -/
def probeBound (c_exp n_max : ℕ) : ℕ :=
  if doubleTabThreshold c_exp ≤ n_max then 3 else doubleTabThreshold c_exp

/-- Expected per-operation instruction charge
`13 * probeBound c_exp n_max + hashEvalSteps c_exp + 8` at capacity `n_max`, for both `query` and
`insert`. It is at most `expectedOpCharge c_exp` for every `n_max`, and equals the threshold-free
`hashEvalSteps c_exp + 47` once `doubleTabThreshold c_exp ≤ n_max` (`charge_of_le`). -/
def charge (c_exp n_max : ℕ) : ℕ :=
  13 * probeBound c_exp n_max + hashEvalSteps c_exp + 8

theorem probeBound_le_doubleTabThreshold (c_exp n_max : ℕ) :
    probeBound c_exp n_max ≤ doubleTabThreshold c_exp := by
  have := four_le_doubleTabThreshold c_exp
  dsimp only [probeBound]
  split_ifs <;> omega

theorem charge_le_expectedOpCharge (c_exp n_max : ℕ) :
    charge c_exp n_max ≤ expectedOpCharge c_exp := by
  have := probeBound_le_doubleTabThreshold c_exp n_max
  dsimp only [charge, expectedOpCharge]; omega

/-- Above the Double Tabulation threshold the per-operation charge is
`13 * 3 + hashEvalSteps c_exp + 8`, independent of `doubleTabThreshold c_exp`. -/
theorem charge_of_le {c_exp n_max : ℕ} (hge : doubleTabThreshold c_exp ≤ n_max) :
    charge c_exp n_max = hashEvalSteps c_exp + 47 := by
  simp only [charge, probeBound, hge, ↓reduceIte]; omega

private noncomputable instance instDecidableExistsOrderedTableProbe {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (u : Fin U) :
    DecidablePred (fun k : ℕ =>
      ∃ T : UniformProbing.Table U (numBuckets n_max),
        DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k) :=
  Classical.decPred _

private noncomputable def orderedProbeSet {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (u : Fin U) : Finset ℕ :=
  (Finset.range (n_max + 2)).filter fun k =>
    ∃ T : UniformProbing.Table U (numBuckets n_max),
      DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k

private theorem orderedProbeSet_nonempty {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (orderedProbeSet π s u).Nonempty := by
  obtain ⟨T₀, hrep₀⟩ := DoubleHashing.exists_orderedTableRep π s
    (le_of_lt (lt_of_le_of_lt hdom (lt_numBuckets n_max)))
  have hle := probeCount_le_add_one hrep₀.toTableRep hdom u
  exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T₀, hrep₀, rfl⟩⟩

private noncomputable def maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    UniformProbing.Table U (numBuckets n_max) :=
  Classical.choose (Finset.mem_filter.mp
    (Finset.max'_mem _ (orderedProbeSet_nonempty π s hdom u))).2

private theorem orderedTableRep_maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    DoubleHashing.OrderedTableRep π s (maxOrderedTable π s hdom u) :=
  (Classical.choose_spec (Finset.mem_filter.mp
    (Finset.max'_mem _ (orderedProbeSet_nonempty π s hdom u))).2).1

private theorem probeCount_le_maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    {s : Dictionary.State U} (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U)
    {T : UniformProbing.Table U (numBuckets n_max)}
    (hrep : DoubleHashing.OrderedTableRep π s T) :
    probeCount T u (π u) ≤ probeCount (maxOrderedTable π s hdom u) u (π u) := by
  have hspec := Classical.choose_spec (Finset.mem_filter.mp
    (Finset.max'_mem _ (orderedProbeSet_nonempty π s hdom u))).2
  have hle := probeCount_le_add_one hrep.toTableRep hdom u
  change probeCount T u (π u) ≤ probeCount (Classical.choose _) u (π u)
  rw [hspec.2]
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T, hrep, rfl⟩)

/-- Parametric affine expectation bound `E[13 * f + (hashEvalSteps c_exp + 8)] ≤ 13 * B + ...`. -/
private theorem expect_probeLinear_le {α : Type*} {c_exp : ℕ} (μ : PMF α)
    (f : α → ℕ) (B : ℝ≥0∞) (hB : (∑' a, μ a * (f a : ℝ≥0∞)) ≤ B) :
    (∑' a, μ a * ((13 * f a + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞)) ≤
      13 * B + (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
  have hterm (a : α) :
      μ a * ((13 * f a + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞) =
        13 * (μ a * (f a : ℝ≥0∞)) + μ a * (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
    push_cast; ring
  simp_rw [hterm]
  rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  gcongr

private theorem tsum_probeCount_le {α : Type*} {c_exp U n_max : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    {s : Dictionary.State U} (u : Fin U)
    (ν : PMF (Seed c_exp n_max × α))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ seedLaw c_exp n_max θ)
    (T_probe : Seed c_exp n_max × α → ℕ)
    (hT : ∀ p ∈ ν.support,
      (Dictionary.dom s).card ≤ n_max ∧
      ∃ T : UniformProbing.Table U (numBuckets n_max),
        DoubleHashing.OrderedTableRep (probePerm p.1) s T ∧
        T_probe p ≤ probeCount T u (probePerm p.1 u)) :
    (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ (probeBound c_exp n_max : ℝ≥0∞) := by
  obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
  have hdom : (Dictionary.dom s).card ≤ n_max := (hT p₀ hp₀).1
  let T_max : Seed c_exp n_max → UniformProbing.Table U (numBuckets n_max) :=
    fun θ => maxOrderedTable (probePerm θ) s hdom u
  have hrep_max : ∀ θ : Seed c_exp n_max,
      DoubleHashing.OrderedTableRep (probePerm θ) s (T_max θ) :=
    fun θ => orderedTableRep_maxOrderedTable (probePerm θ) s hdom u
  have hpt : ∀ p, ν p * (T_probe p : ℝ≥0∞) ≤
      ν p * (probeCount (T_max p.1) u (probePerm p.1 u) : ℝ≥0∞) := fun p => by
    by_cases hp : p ∈ ν.support
    · obtain ⟨_, T, hrep_T, hle⟩ := hT p hp
      exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (hle.trans (probeCount_le_maxOrderedTable _ hdom u hrep_T))) zero_le
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hp]
  calc (∑' p, ν p * (T_probe p : ℝ≥0∞))
      ≤ ∑' p, ν p * (probeCount (T_max p.1) u (probePerm p.1 u) : ℝ≥0∞) := tsum_le_tsum hpt
    _ = ∑' θ, (ν.map Prod.fst) θ * (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
          (fun θ => (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞))).symm
    _ ≤ ∑' θ, seedLaw c_exp n_max θ * (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞) :=
        tsum_le_tsum fun θ => mul_le_mul_of_nonneg_right (hseed θ) zero_le
    _ ≤ (probeBound c_exp n_max : ℝ≥0∞) := by
        dsimp only [probeBound]; split_ifs with hge
        · exact_mod_cast DoubleHashing.expect_probeCount_oddStride_doubleTab_le
            hge hU (thirtyTwo_mul_max_le_numBuckets n_max) hrep_max hdom u
        · have h3 : (3 : ℝ≥0∞) ≤ doubleTabThreshold c_exp := by
            have := four_le_doubleTabThreshold c_exp; exact_mod_cast (by omega : 3 ≤ _)
          rw [← max_eq_left h3]
          exact DoubleHashing.expect_probeCount_oddStride_unconditional_le
            hU (thirtyTwo_mul_max_le_numBuckets n_max) hrep_max hdom u

theorem step_exec_spec {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (ν : PMF (Seed c_exp n_max × Data 16))
    (hv : (Dictionary.spec U V n_max).valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * seedLaw c_exp n_max θ)
    (hsupp : ∀ p ∈ ν.support, Rep w base c_exp U V n_max p.1 s p.2 ∧ argMatch o p.2.regs) :
    ∃ (μ_step : Seed c_exp n_max × Data 16 → PMF (Seed c_exp n_max × Data 16))
      (T_step : Seed c_exp n_max × Data 16 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (opCode c_exp n_max) p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decodeOp (V := V) (n_max := n_max) o q.2.regs =
            some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
          Rep w base c_exp U V n_max q.1 ((Dictionary.spec U V n_max).stepFn s o).1 q.2 ∧
          Modifies (Block.mk base (space c_exp n_max)).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ 1 * seedLaw c_exp n_max θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, μ_step p q * ((0 : ℕ) : ℝ≥0∞))) ≤
        (charge c_exp n_max : ℝ≥0∞) + ∑' p, ν p * ((0 : ℕ) : ℝ≥0∞) := by
  classical
  let T_probe (p : Seed c_exp n_max × Data 16) : ℕ :=
    if p ∈ ν.support then
      probeCount (extractSlots base c_exp U n_max p.2.mem) (opKey o) (probePerm p.1 (opKey o))
    else 0
  let yOf (p : Seed c_exp n_max × Data 16) : Data 16 :=
    if hp : p ∈ ν.support then
      Classical.choose (opCode_execWithin hS hV (hsupp p hp).1 o hv (hU_fit (opKey o))
        (hsupp p hp).2.1 (hsupp p hp).2.2.1 (hsupp p hp).2.2.2)
    else p.2
  refine ⟨fun p => PMF.pure (p.1, yOf p),
    fun p => ((13 * T_probe p + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨e, hrep_y, hout, hmod⟩ := Classical.choose_spec
      (opCode_execWithin hS hV (hsupp p hp).1 o hv (hU_fit (opKey o))
        (hsupp p hp).2.1 (hsupp p hp).2.2.1 (hsupp p hp).2.2.2)
    have hy : yOf p = _ := dite_eq_left hp
    refine ⟨?_, fun q hq => ?_⟩
    · simpa only [PMF.pure_map, hy, T_probe, hp, ↓reduceIte, opPathSteps] using
        ExecCodeDist.of_execWithin e
    · obtain rfl : q = (p.1, yOf p) := by simpa using hq
      exact ⟨decodeOp_eq_step o _ (by rwa [hy]), hy ▸ hrep_y, hy ▸ hmod⟩
  · exact fun θ' => by simpa [PMF.map_bind] using hseed θ'
  · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
    have hprobe := tsum_probeCount_le (s := s) hU (opKey o) ν
      (fun θ => by simpa only [one_mul] using hseed θ) T_probe
      fun p hp => ⟨(hsupp p hp).1.dom_le, _, (hsupp p hp).1.table_rep,
        by simp only [T_probe, hp, ↓reduceIte, le_rfl]⟩
    refine (expect_probeLinear_le ν T_probe _ hprobe).trans_eq ?_
    dsimp only [charge]; push_cast; ring

/-- **Composable randomized Word-RAM `StateTransitionImpl` certificate over `Basis.exact`** for the
open-addressed odd-stride double-hashing dictionary realizing `Dictionary.spec U V n_max` with
$O_{c_{\exp}}(1)$ expected operation time (`charge c_exp n_max ≤ expectedOpCharge c_exp`, and
`hashEvalSteps c_exp + 47` once `doubleTabThreshold c_exp ≤ n_max`) and
$O_{c_{\exp}}(n_{\max} + 1)$ space (`space c_exp n_max`) for every `n_max : ℕ` whenever
`U ≤ max n_max 4 ^ c_exp`. -/
noncomputable abbrev impl {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp) :
    Randomized.StateTransitionImpl (subroutineCode c_exp n_max)
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  Randomized.StateTransitionImpl.ofFn
    (Seed := Seed c_exp n_max)
    (seedLaw := seedLaw c_exp n_max)
    (seedSlack := 1)
    (space := space c_exp n_max)
    (spanTime := 3)
    (setupTime := (setupSteps c_exp n_max : ℝ≥0∞))
    (initPotential := 0)
    (charge := fun _ _ => charge c_exp n_max)
    (rep := Rep w base c_exp U V n_max)
    (potential := fun _ _ => 0)
    (encode := encodeOp)
    (argMatch := argMatch)
    (decode := decodeOp)
    (bounded := fun hrep => hrep.bounded)
    (arguments_fit := fun o hv i _ => arguments_fit hS hU_fit hV o hv i)
    (encode_matches := encode_matches)
    (rep_supported := fun {θ s x x'} hregs hmem hbdd hrep => by
      have hbase : x'.regs regBase = x.regs regBase := hregs regBase rfl
      exact hrep.congr hbdd hbase hmem)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by
      dsimp only [subroutineCode]
      decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      dsimp only [subroutineCode] at h1 hfit ⊢
      simp [Op.exactBin, Op.eval, StandardOp.evalExact, Data.put, h1, hfit])
    (span_exec := fun {x} _ hfr _ => by
      obtain ⟨x₁, he, hm, hb, hfr'⟩ := allocSpan_execWithin hS hfr
      exact ⟨x₁, he, hm, hb, hfr', fun j => Fin.elim0 j⟩)
    (setup_exec := fun {x₁} hx₁ hb hfr _ hz =>
      setup_exec_spec hS hx₁ hb hfr hz)
    (step_exec := fun {s} o ν hv hseed hsupp =>
      step_exec_spec hS hU_fit hV hU o ν hv hseed hsupp)

/-- Standard-basis (`Basis.standard`) randomized `StateTransitionImpl` certificate for the
open-addressed
odd-stride double-hashing dictionary. -/
noncomputable abbrev implStandard {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp) :
    Randomized.StateTransitionImpl (subroutineCode c_exp n_max).toStandard
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (impl hS hU_fit hV hU).toStandard

/-- **End-to-end multi-operation expected-time theorem (`seq_expected_amortized`)**:
from fresh zeroed memory `[base, base + space c_exp n_max)`, initializing the odd-stride
double-hashing dictionary (`initFresh`) and executing the subroutine operation bodies
(`ExecStepsOfFn`) across any admissible operation history `ops : List (Dictionary.Op U)` fixed
independently of the sampled seed (oblivious adversary) takes at most
`3 + setupSteps c_exp n_max + ops.length * charge c_exp n_max` expected Word-RAM instructions
whenever `U ≤ max n_max 4 ^ c_exp`. The per-operation charge is at most the $O_{c_{\exp}}(1)$ bound
`expectedOpCharge c_exp` for every `n_max : ℕ` (`charge_le_expectedOpCharge`) and equals
`hashEvalSteps c_exp + 47` once `doubleTabThreshold c_exp ≤ n_max` (`charge_of_le`). -/
theorem seq_expected_amortized {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp)
    {x : Data 16} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs regV = base)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_final : PMF (Seed c_exp n_max × Data 16)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode c_exp n_max).initFresh x (ν₀.map Prod.snd)
        (impl (V := V) hS hU_fit hV hU).initTime ∧
      (impl (V := V) hS hU_fit hV hU).ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final
        T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ seedLaw c_exp n_max θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base c_exp U V n_max p.1
          ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      (impl (V := V) hS hU_fit hV hU).initTime + T_ops ≤
        (3 + setupSteps c_exp n_max : ℝ≥0∞) +
          ((Dictionary.spec U V n_max).totalCost (fun _ _ => charge c_exp n_max)
            (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hbound⟩ :=
    (impl (V := V) hS hU_fit hV hU).seq_expected_amortized_ofFn ops hx hfr
      (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps,
    fun θ => by simpa only [one_mul] using hseed_final θ, hrep_final, ?_⟩
  simpa only [Randomized.StateTransitionImpl.initTime, impl,
    Randomized.StateTransitionImpl.ofFn, Nat.cast_zero, mul_zero, tsum_zero, add_zero,
    Nat.cast_add, Nat.cast_ofNat] using hbound

/-- **Ideal uniform-probing expected-step corollary (`≤ hashEvalSteps c_exp + 34`)**:
when the probe permutation `π` is drawn uniformly from `Equiv.Perm (Fin (numBuckets n_max))` on a
table `T` with at most `n_max` other occupied slots (`(otherOccupiedSlots T u).card ≤ n_max`), the
expected Word-RAM step count `13 * probeCount T u π + hashEvalSteps c_exp + 8` is at most
`hashEvalSteps c_exp + 34` (combining `expect_probeLinear_le` with `B = 2` from
`UniformProbing.expect_unsuccessfulProbes_le_two`). -/
theorem expect_idealProbeSteps_le {c_exp U n_max : ℕ}
    (T : Fin (numBuckets n_max) → Option (Fin U × ℕ)) (u : Fin U)
    (hcard : (UniformProbing.otherOccupiedSlots T u).card ≤ n_max) :
    (∑' π : Equiv.Perm (Fin (numBuckets n_max)),
      (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) π *
        ((13 * UniformProbing.probeCount T u π + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞)) ≤
      (hashEvalSteps c_exp + 34 : ℝ≥0∞) := by
  have h4 := four_mul_le_numBuckets n_max
  exact (expect_probeLinear_le (PMF.uniformOfFintype _) (fun π => probeCount T u π) 2
    (UniformProbing.expect_unsuccessfulProbes_le_two (numBuckets_pos n_max) (by omega))).trans_eq
    (by ring)

end Cslib.DataStructure.Dictionary.WordRAM.UniformProbing
