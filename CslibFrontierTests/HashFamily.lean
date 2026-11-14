/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.BitString.LinearHash
import CslibFrontier.Probability.BitString.SubsetSum
import CslibFrontier.Probability.HashFamily.MultiplyShift
import CslibFrontier.Probability.HashFamily.Polynomial
import CslibFrontier.Probability.PairwiseIndependentHash.Affine
import CslibFrontier.Probability.PairwiseIndependentHash.Universal
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for universal and Δ-universal hash families

The affine family over `ZMod 3` is universal and Δ-universal through pairwise independence; Boolean
matrices and subset sums are Δ-universal; a constant family is not universal for any bound below
`1`; and the bounds are exact for a two-element family. Fixed-length polynomial evaluation uses a
three-point subset of `ZMod 5`; Carter–Wegman polynomial evaluation is evaluated over `ZMod 5`, and
multiply-shift on `4`-bit words, where its collision bound is attained.
-/

namespace CslibFrontierTests.HashFamily

open Cslib Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The affine maps `ZMod 3 → ZMod 3` are `1 / 3`-universal, two-universal, and
`1 / 3`-Δ-universal; Boolean `2 × 3` matrices are `1 / 4`-XOR-universal and `1 / 4`-universal;
and subset sums with weights in `ZMod 5` are `1 / 5`-Δ-universal on binary words of length `2`. -/
example :
    IsUniversalHash
      (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3))) affineHash
      (Fintype.card (Fin 1 → ZMod 3) : ℝ≥0∞)⁻¹ ∧
    IsTwoUniversal
      (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3))) affineHash ∧
    IsDeltaUniversalHash
      (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3)))
      affineHash (Fintype.card (Fin 1 → ZMod 3) : ℝ≥0∞)⁻¹ ∧
    IsDeltaUniversalHash (PMF.uniformOfFintype (Fin 2 → BitString 3))
      BitString.LinearHash.hash (4 : ℝ≥0∞)⁻¹ ∧
    IsUniversalHash (PMF.uniformOfFintype (Fin 2 → BitString 3)) BitString.LinearHash.hash
      (4 : ℝ≥0∞)⁻¹ ∧
    IsDeltaUniversalHash (PMF.uniformOfFintype (Fin 2 → ZMod 5))
      (BitString.SubsetSum.hash (ι := Fin 2)) (5 : ℝ≥0∞)⁻¹ := by
  refine ⟨isPairwiseIndependentHash_affineHash.isUniversalHash,
    isPairwiseIndependentHash_affineHash.isTwoUniversal,
    isPairwiseIndependentHash_affineHash.isDeltaUniversalHash,
    ?_, ?_, ?_⟩
  · simpa using BitString.LinearHash.isDeltaUniversalHash 3 2
  · simpa using (BitString.LinearHash.isDeltaUniversalHash 3 2).isUniversalHash
  · simpa using BitString.SubsetSum.isDeltaUniversalHash (ι := Fin 2) (G := ZMod 5)

/-- A constant family always collides, so it is not universal for any bound below `1`;
selecting one of two input bits with a uniform key collides on `(0, 0)` and `(1, 0)` with
probability `1 / 2` and is `1 / 2`-universal. -/
example :
    ¬IsUniversalHash (PMF.uniformOfFintype Bool) (fun _ (_ : Bool) => (0 : ZMod 2)) (1 / 2) ∧
    (PMF.uniformOfFintype Bool).toOuterMeasure
      {key | (if key then (false, false).1 else (false, false).2) =
        (if key then (true, false).1 else (true, false).2)} = 2⁻¹ ∧
    IsUniversalHash (PMF.uniformOfFintype Bool)
      (fun key (input : Bool × Bool) => if key then input.1 else input.2)
      (Fintype.card Bool : ℝ≥0∞)⁻¹ := by
  refine ⟨fun h => ?_, ?_, isTwoUniversal_iff_sum_ite_le.mpr <| ?_⟩
  · have h := h false true (by decide)
    rw [PMF.toOuterMeasure_uniformOfFintype] at h
    have h' := ENNReal.toReal_mono (by norm_num) h
    norm_num at h'
  · rw [PMF.toOuterMeasure_uniformOfFintype]
    simp [Finset.filter_insert, Finset.filter_singleton]
  · rintro ⟨a, b⟩ ⟨c, d⟩ hne
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply] at *

/-! ### Carter–Wegman polynomial evaluation over `ZMod 5` -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def finThreeToZModFive : Fin 3 ↪ ZMod 5 := Fin.castLEEmb (by decide : 3 ≤ 5)

private def restrictedX : Fin 2 → ZMod 5 := ![1, 0]

private def restrictedY : Fin 2 → ZMod 5 := ![0, 0]

/-- The two distinct messages `X` and `Y` collide at exactly the embedded point `0`, so the
restricted three-point seed space has a nonempty collision set. -/
example :
    restrictedX ≠ restrictedY ∧
    (Finset.univ.filter fun s : Fin 3 =>
      coeffPolyHash (finThreeToZModFive s) restrictedX =
        coeffPolyHash (finThreeToZModFive s) restrictedY).card = 1 := by
  decide

/-- Source-order Horner evaluation agrees with the reversed ascending-coefficient API and with
the fixed-length specialization of the monic variable-length API. -/
example :
    coeffPolyHash (3 : ZMod 5) restrictedX =
        polynomialHash (restrictedX ∘ Fin.rev) 3 ∧
      polyHash (3 : ZMod 5) (List.ofFn restrictedX) =
        3 ^ 2 + coeffPolyHash 3 restrictedX :=
  ⟨coeffPolyHash_eq_polynomialHash_rev 3 restrictedX, polyHash_ofFn_eq 3 restrictedX⟩

/-- The restricted-domain theorem gives the nontrivial bound `2 / 3 < 1` for the three-point
embedding into `ZMod 5`. -/
example :
    IsUniversalHash (PMF.uniformOfFintype (Fin 3))
        (fun s (x : Fin 2 → ZMod 5) => coeffPolyHash (finThreeToZModFive s) x) (2 / 3) ∧
      (2 / 3 : ℝ≥0∞) < 1 := by
  refine ⟨?_, by norm_num⟩
  simpa using isUniversalHash_coeffPolyHash_of_embedding finThreeToZModFive 2

/-- The empty coefficient vector evaluates to zero. -/
example (k : ZMod 5) (x : Fin 0 → ZMod 5) : coeffPolyHash k x = 0 := by
  simp [coeffPolyHash]

/-- Sampling the evaluation point from all of `ZMod 5` gives the full-field specialization. -/
example :
    IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (x : Fin 2 → ZMod 5) => coeffPolyHash k x)
      (2 / Fintype.card (ZMod 5)) :=
  isUniversalHash_coeffPolyHash 2

/-- `Hpoly` of `(1, 2)` at key `3` is `4`, `Hxpoly` is `2`, and `()` and `(0)` collide at key `1`
but not at key `2`. -/
example :
    -- At key 3, Hpoly is 3² + 3 + 2 = 14 = 4 modulo 5; Hxpoly is 3 · 4 = 2.
    polyHash (3 : ZMod 5) [1, 2] = 4 ∧
    xpolyHash (3 : ZMod 5) [1, 2] = 2 ∧
    -- The key power separates [] and [0] at key 2; at key 1, 1 = 1 + 0.
    polyHash (1 : ZMod 5) [] = polyHash 1 [0] ∧
    polyHash (2 : ZMod 5) [] ≠ polyHash 2 [0] := by decide

/-- Messages of length at most `2` collide with probability at most `2 / 5` under `polyHash`,
and `xpolyHash` is `3 / 5`-Δ-universal. -/
example :
    IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (m : {m : List (ZMod 5) // m.length ≤ 2}) => polyHash k m) (2 / 5) ∧
    IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (m : {m : List (ZMod 5) // m.length ≤ 2}) => xpolyHash k m) (3 / 5) := by
  refine ⟨by simpa using isUniversalHash_polyHash (F := ZMod 5) 2, ?_⟩
  have h := isDeltaUniversalHash_xpolyHash (F := ZMod 5) 2
  norm_num at h
  exact h

/-! ### Multiply-shift on `4`-bit words -/

/-- Multiply-shift evaluations and collision counts on `4`-bit words: half of the eight
multipliers make `3` and `1` collide in the top two bits, matching `2 ^ (4 - 2) = 4`. -/
example :
    -- Multiplier 2 · 3 + 1 = 7 gives products 21 ≡ 5 (mod 16) and 7, both with top bits 01.
    multiplyShift 4 2 3 3 = 1 ∧ multiplyShift 4 2 3 1 = 1 ∧
    -- Multiplier 3 gives products 9 and 3, which differ in the top two bits.
    multiplyShift 4 2 1 3 = 2 ∧ multiplyShift 4 2 1 1 = 0 ∧
    (Finset.univ.filter fun b => multiplyShift 4 2 b 3 = multiplyShift 4 2 b 1).card = 4 ∧
    (Finset.univ.filter fun b => multiplyShift 4 2 b 3 = multiplyShift 4 2 b 1).card ≤
      2 ^ (4 - 2) ∧
    IsUniversalHash (PMF.uniformOfFintype (Fin (2 ^ (4 - 1)))) (multiplyShift 4 2)
      (2 / 2 ^ 2) :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    card_filter_multiplyShift_eq_le (by norm_num) (by norm_num) (by decide),
    isUniversalHash_multiplyShift (by norm_num) (by norm_num)⟩

end CslibFrontierTests.HashFamily
