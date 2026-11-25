/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelWitness
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalDeterminantFeasibility
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Fixed-width witnesses for critical feasibility

The witness is a framed list of derivative-sign entries and a binary shift, with room for
padding. Its width is computable in unary from the binary quotient dimension and unary
test count. Decoding any word yields a bounded label and shift. Every label and shift used
in the determinant criterion can be represented by a word of the prescribed width.

This adapts `RootLabelWitnessEncoding` and `CodedCriticalCriterion` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier label types and framing.

## Main results

* `exists_zero_iff_neg_criticalFeasibilityDeterminant` characterizes a real zero of a bounded
  nonnegative source by an accepting fixed-width determinant witness.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem

/-- Raw witness fields for the critical determinant test. -/
structure CriticalFeasibilityWitness where
  /-- Derivative-sign entries, read through the bounded label decoder. -/
  label : List RootLabelTestCode
  /-- Shift, reduced modulo the quotient dimension plus one. -/
  shift : ℕ

/-- Frame the derivative-sign list and append the binary shift. -/
enc_structure encCriticalFeasibilityWitness : CriticalFeasibilityWitness where
  label : encRootLabelCode,
  shift : encNat

private def rootLabelTestCodeDecoder : Decoder encRootLabelTestCode :=
  (Decoder.pair Decoder.nat Decoder.nat).map
    (fun (index, sign) => ⟨index, sign⟩) (fun t => (t.index, t.sign)) (fun _ => rfl) (fun _ => rfl)

private def witnessDecoder : Decoder encCriticalFeasibilityWitness :=
  (Decoder.pair (Decoder.list rootLabelTestCodeDecoder) Decoder.nat).map
    (fun (label, shift) => ⟨label, shift⟩) (fun t => (t.label, t.shift))
    (fun _ => rfl) (fun _ => rfl)

/-- The outer frame delimits the witness. Bits after the frame are padding. -/
abbrev encPaddedCriticalFeasibilityWitness :
    (CriticalFeasibilityWitness × List Bool) ↪ List Bool :=
  encPair encCriticalFeasibilityWitness encBits

/-- Read a witness from a word, using the total framed decoder. -/
def decodeCriticalFeasibilityWitness (word : List Bool) : CriticalFeasibilityWitness :=
  ((Decoder.pair witnessDecoder Decoder.bits).decode word).1

/-- Decoding and returning the framed witness takes polynomial time on every word. -/
theorem decodeCriticalFeasibilityWitness_polyTime :
    ComputableInPolyTime decodeCriticalFeasibilityWitness encBits encCriticalFeasibilityWitness :=
  (fst encCriticalFeasibilityWitness encBits).comp
    (Decoder.pair witnessDecoder Decoder.bits).computableInPolyTime

/-- The framed decoder recovers the witness for any padding suffix. -/
theorem decodeCriticalFeasibilityWitness_enc (w : CriticalFeasibilityWitness)
    (padding : List Bool) :
    decodeCriticalFeasibilityWitness (encPaddedCriticalFeasibilityWitness (w, padding)) = w := by
  rw [decodeCriticalFeasibilityWitness, Decoder.decode_enc]

/-- Bit width for a padded witness with quotient dimension `D` and at most `N`
derivative-sign entries. -/
def criticalFeasibilityWitnessWidth (D N : ℕ) : ℕ :=
  2 * (2 * (N * (4 * D.size + 7)) + 1 + D.size) + 1

/-- The prescribed width is polynomial-time computable even in unary. -/
theorem criticalFeasibilityWitnessWidth_polyTime {α : Type} {enc : α ↪ List Bool}
    {D N : α → ℕ} (hD : ComputableInPolyTime D enc encNat)
    (hN : ComputableInPolyTime N enc encUnary) :
    ComputableInPolyTime (fun w => criticalFeasibilityWitnessWidth (D w) (N w))
      enc encUnary := by
  have hsize := binary_size.comp hD
  exact unary_add' (unary_mul' (.const 2) (unary_add'
    (unary_add' (unary_mul' (.const 2) (unary_mul' hN
      (unary_add' (unary_mul' (.const 4) hsize) (.const 7)))) (.const 1)) hsize)) (.const 1)

private theorem exists_padded_witness {D N e : ℕ} (L : List (Fin D × SignType))
    (hL : L.length ≤ N) (he : e ≤ D) :
    ∃ word : List Bool, word.length = criticalFeasibilityWitnessWidth D N ∧
      decodeCriticalFeasibilityWitness word = ⟨encodeRootLabel L, e⟩ := by
  let w : CriticalFeasibilityWitness := ⟨encodeRootLabel L, e⟩
  let length := (encCriticalFeasibilityWitness w).length
  let width := criticalFeasibilityWitnessWidth D N
  let padding := List.replicate (width - (2 * length + 1)) false
  have hlength : length ≤ 2 * (N * (4 * D.size + 7)) + 1 + D.size := by
    have := length_encRootLabelCode_encodeRootLabel_le L hL
    have := Nat.size_le_size he
    simp only [length, w, encCriticalFeasibilityWitness_apply, encCriticalFeasibilityWitnessFields,
      length_encPair, encNat_apply, Nat.size_eq_bits_len]
    omega
  refine ⟨encPaddedCriticalFeasibilityWitness (w, padding), ?_,
    decodeCriticalFeasibilityWitness_enc w padding⟩
  rw [encPaddedCriticalFeasibilityWitness, length_encPair]
  simp only [encBits_apply, padding, List.length_replicate, width,
    criticalFeasibilityWitnessWidth]
  omega

/-- The determinant at the bounded derivative-sign label and shift read from a witness word. -/
@[expose] noncomputable def criticalFeasibilityDeterminant {n ell : ℕ} (hell : 1 ≤ ell) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (word : List Bool) : ℤ :=
  let w := decodeCriticalFeasibilityWitness word
  let L := decodeRootLabel (D := ell ^ n) (pow_pos (by omega) _) (n * ell.size) w.label
  criticalLabelDeterminant hell b F hF L (w.shift % (ell ^ n + 1))

/-- A bounded nonnegative source has a real zero exactly when some witness of the prescribed
width makes its decoded critical determinant negative. Soundness uses only bounded decoding,
so arbitrary padding or malformed witness bits cannot cause a false positive. -/
theorem exists_zero_iff_neg_criticalFeasibilityDeterminant {n ell b : ℕ}
    (hell : 2 ≤ ell) (heven : Even (ell + 1)) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (hFn : ∀ x, 0 ≤ eval x (F.map (Int.castRingHom ℝ))) :
    (∃ x, eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ word : List Bool, word.length = criticalFeasibilityWitnessWidth (ell ^ n) (n * ell.size) ∧
        criticalFeasibilityDeterminant (by omega) b F hF word < 0 := by
  rw [exists_zero_iff_exists_neg_criticalLabelDeterminant hell heven F hF hb hFn]
  have hD : 0 < ell ^ n := pow_pos (by omega) _
  refine ⟨fun ⟨L, hL, e, he, hneg⟩ => ?_, fun ⟨word, _, hneg⟩ =>
    ⟨_, decodeRootLabel_length_le hD _ _, _,
      Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _)), hneg⟩⟩
  obtain ⟨word, hw, hdecode⟩ := exists_padded_witness L hL he
  exact ⟨word, hw, by
    simpa only [criticalFeasibilityDeterminant, hdecode, decodeRootLabel_encodeRootLabel hD L hL,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le he)] using hneg⟩

end Cslib.Complexity.RealAlgebraic
