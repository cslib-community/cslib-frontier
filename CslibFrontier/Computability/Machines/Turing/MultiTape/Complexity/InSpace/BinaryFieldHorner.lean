/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryField
public import CslibFrontier.Foundations.FieldTheory.Finite.HornerCoordinates
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Binary-label Horner evaluation with a supplied modulus

The coefficient of degree `i` is the width-bit block at offset `width * i` in a binary label.
Horner evaluation visits these blocks in descending order with a binary counter. The supplied
modulus and evaluation point remain available throughout; no coefficient table is constructed.
This component belongs to the native weight-generator development in #6747. Modulus selection,
seed access and the full generator are separate components.

## Main results

* `HornerInput.evaluate_inSpace`: linear workspace for the packed evaluation request.
-/

public section

namespace Turing.BinaryField

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib Cslib.BinaryField

/-- Runtime data for evaluating a polynomial packed into a binary label. The coefficient width
is the degree `modulus.length - 1`; the coefficient count is supplied in binary. -/
structure HornerInput where
  /-- Little-endian modulus coefficients. -/
  modulus : List Bool
  /-- Coordinate word of the evaluation point. -/
  point : List Bool
  /-- Coefficients packed least-significant block first. -/
  label : ℕ
  /-- Number of coefficient blocks, including any leading zero blocks. -/
  count : ℕ

/-- Framed modulus and point words followed by the binary label and coefficient count. -/
enc_structure encHornerInput : HornerInput where
  modulus : encCoefficients, point : encCoefficients, label : encNat, count : encNat

private def coefficient (p : HornerInput) (i : ℕ) : List Bool :=
  let width := p.modulus.length - 1
  BitString.lowBits width (p.label >>> (width * i))

/-- Evaluate the packed coefficient blocks at the supplied point, reducing products modulo
the supplied polynomial. A request with zero coefficient blocks returns the empty word. -/
def HornerInput.evaluate (p : HornerInput) : List Bool :=
  hornerBits (p.modulus.length - 1) (fieldMulMod p.modulus) p.point
    (fun i : Fin p.count => coefficient p i)

/-- Each coefficient supplied to Horner is the fixed-width block at its binary offset. -/
theorem HornerInput.evaluate_eq (p : HornerInput) :
    p.evaluate =
      hornerBits (p.modulus.length - 1) (fieldMulMod p.modulus) p.point
        (fun i : Fin p.count => BitString.lowBits (p.modulus.length - 1)
          (p.label >>> ((p.modulus.length - 1) * i.val))) := by
  unfold HornerInput.evaluate coefficient
  rfl

private theorem coefficient_inSpace :
    ComputableInSpace (fun p : HornerInput × ℕ => coefficient p.1 p.2)
      (encPair encHornerInput encNat) encCoefficients
      (fun p => (encPair encHornerInput encNat p).length) := by
  have hp := fst encHornerInput encNat
  have hm := encHornerInput_modulus_budget hp
  have hl := encHornerInput_label_budget hp
  have hw := budget_natPred (budget_length hm)
  have ho := budget_natMul hw (snd encHornerInput encNat)
  have hs := budget_comp_linear natShiftRight (budget_prod hl ho)
  have hpair := budget_prod hw hs
  have hwidth : (fun p : HornerInput × ℕ => p.1.modulus.length - 1) ≼
      fun p => (encPair encHornerInput encNat p).length := .of_le fun p => by
    have hm := encHornerInput_modulus_length_le p.1
    have hl := length_le_length_encList encBool p.1.modulus
    change p.1.modulus.length - 1 ≤ (encPair encHornerInput encNat p).length
    rw [length_encPair]
    change (encList encBool p.1.modulus).length ≤ (encHornerInput p.1).length at hm
    omega
  exact (lowBits_inSpace.comp hpair).weaken
    ((BigOLe.refl _).add (hwidth.add hpair.length_le))

private abbrev HornerState := HornerInput × ℕ × List Bool

private def encHornerState := encPair encHornerInput (encPair encNat encCoefficients)

private def hornerAdvance (s : HornerState) : HornerState :=
  let i := s.2.1 - 1
  (s.1, i, BitString.listXor (s.1.modulus.length - 1)
    [coefficient s.1 i, fieldMulMod s.1.modulus s.2.2 s.1.point])

private theorem listXor_eq_zipWith {width : ℕ} {u v : List Bool}
    (hu : u.length = width) (hv : v.length = width) :
    BitString.listXor width [u, v] = u.zipWith xor v := by
  rw [BitString.listXor_pair, BitString.ofFn_add, BitString.ofFn_ofList hu,
    BitString.ofFn_ofList hv]

private theorem hornerAdvance_inSpace :
    ComputableInSpace hornerAdvance encHornerState encHornerState
      (fun s => (encHornerState s).length) := by
  have hp := fst encHornerInput (encPair encNat encCoefficients)
  have hr := snd encHornerInput (encPair encNat encCoefficients)
  have hi := budget_natPred (fst' hr)
  have hm := encHornerInput_modulus_budget hp
  have hx := encHornerInput_point_budget hp
  have ha := snd' hr
  have hc := budget_comp_linear coefficient_inSpace (budget_prod hp hi)
  have hmul := budget_comp_linear fieldMulMod_inSpace (encMulInput_mk_budget hm ha hx)
  have hword := budget_comp_linear xor_inSpace (budget_prod hc hmul)
  exact (budget_prod hp (budget_prod hi hword)).of_enc_eq fun s => by
    simp only [hornerAdvance, encHornerState]
    rw [listXor_eq_zipWith (by simp [coefficient]) (by simp)]

private theorem horner_input (p : HornerInput) (n k : ℕ) (acc : List Bool) :
    (hornerAdvance^[k] (p, n, acc)).1 = p := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Function.iterate_succ_apply', hornerAdvance] using ih

private theorem horner_counter (p : HornerInput) (n k : ℕ) (acc : List Bool) :
    (hornerAdvance^[k] (p, n, acc)).2.1 = n - k := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', hornerAdvance, ih, Nat.sub_sub]

private theorem horner_word_length (p : HornerInput) (k : ℕ) :
    (hornerAdvance^[k] (p, p.count, [])).2.2.length ≤ p.modulus.length - 1 := by
  cases k with
  | zero => simp
  | succ k => simp [Function.iterate_succ_apply', hornerAdvance, horner_input]

private theorem horner_state_length (p : HornerInput) (k : ℕ) :
    (encHornerState (hornerAdvance^[k] (p, p.count, []))).length ≤
      8 * ((encHornerInput p).length + 1) := by
  have hc := length_encNat_mono (Nat.sub_le p.count k)
  rw [← horner_counter p p.count k []] at hc
  have hw := horner_word_length p k
  have hm := encHornerInput_modulus_length_le p
  have hn := encHornerInput_count_length_le p
  simp only [encCoefficients, length_encList, encBool_apply, List.length_singleton,
    List.map_const', List.sum_replicate, smul_eq_mul] at hm
  simp only [encHornerState, length_encPair, horner_input, encCoefficients,
    length_encList, encBool_apply, List.length_singleton, List.map_const', List.sum_replicate,
    smul_eq_mul]
  omega

private theorem horner_agrees (p : HornerInput) :
    (hornerAdvance^[p.count] (p, p.count, [])).2.2 = p.evaluate := by
  let step := fun s : ℕ × List Bool =>
    (s.1 - 1, BitString.listXor (p.modulus.length - 1)
      [coefficient p (s.1 - 1), fieldMulMod p.modulus s.2 p.point])
  have h (k : ℕ) (s : ℕ × List Bool) :
      hornerAdvance^[k] (p, s) = (p, step^[k] s) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Function.iterate_succ_apply', ih, hornerAdvance, step]
  rw [h]
  exact (hornerBits_eq_iterate (p.modulus.length - 1) (fieldMulMod p.modulus) p.point
    (coefficient p) p.count).symm

/-- Packed Horner evaluation uses workspace linear in the encoded request length. -/
theorem HornerInput.evaluate_inSpace :
    ComputableInSpace HornerInput.evaluate encHornerInput encCoefficients
      (fun p => (encHornerInput p).length) := by
  let : Inhabited HornerState := ⟨⟨⟨[], [], 0, 0⟩, 0, []⟩⟩
  have hid : ComputableInSpace (fun p => p) encHornerInput encHornerInput
      (fun p => (encHornerInput p).length) := of_inO ComputableInO.id'
  have hn := encHornerInput_count_budget hid
  have hinit : ComputableInSpace (fun p => (p, p.count, [])) encHornerInput encHornerState
      (fun p => (encHornerInput p).length) :=
    budget_prod hid (budget_prod hn (budget_const (encB := encCoefficients) [] (.refl _)))
  have h := budget_iterate hn hinit hornerAdvance_inSpace (fun p k _ => horner_state_length p k)
    (.of_le_linear 8 8 fun p => by omega)
  have hout := budget_comp_linear (snd encHornerInput (encPair encNat encCoefficients)) h
  exact (budget_comp_linear (snd encNat encCoefficients) hout).of_enc_eq
    fun p => congrArg encCoefficients (horner_agrees p).symm

end Turing.BinaryField
