/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedProduct
public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Signed

/-! # Native operand addresses and the local sign correction for the reduced tree -/

@[expose] public section
namespace Cslib.Circuits.Frontier.FastContraction

open Polynomial BitString Boolean Boolean.CarrySaveQuery
open ConvolutionOperand.Signed

/-- Read the single selected coefficient bit, if the native signed router requests one. -/
def signedRead {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (a : ConvolutionOperand.Signed.Query) : Bool :=
  (source a).elim false fun j =>
    (if a.right then (v.coeff j.1).val else (u.coeff j.1).val).testBit j.2

private theorem signedRead_mk {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ)
    (t : List Bool) (b : ℕ) (carry right : Bool) :
    let a : ConvolutionOperand.Signed.Query := ⟨q, p, i, t, b, carry, right⟩
    signedRead u v a = if live a then
      readPath u v (2 * q) (diagonal a) (t.drop 2) b carry right else false := by
  dsimp only
  unfold signedRead source
  split <;> rfl

private theorem component_pair {w : ℕ} (a b : BitString w) (i : Fin w) (carry : Bool) :
    component (Fin.append a b) carry i = if carry then b i else a i := by
  cases carry
  · exact congrFun (fstBits_append _ _) i
  · exact congrFun (sndBits_append _ _) i

private theorem component_negative {p : ℕ} (a : BitString p) (i : Fin p) (carry : Bool) :
    component (SignedSum.negative a) carry i = if carry then decide (i.val = 0) else !a i := by
  rw [SignedSum.negative, component_pair]
  congr 1
  rw [equivFin_symm_apply, Nat.testBit_mod_two_pow]
  apply Bool.eq_iff_iff.mpr
  simp [i.isLt, Nat.testBit_one_eq_true_iff_self_eq_zero]

private theorem component_diagonal {p d : ℕ} (u v : (ZMod (2 ^ p))[X]) (hv : v.natDegree < d)
    (k : ℕ) (t : List Bool) (i : Fin p) (carry : Bool) :
    component (diagonalLeaves d k u v t) carry i =
      (readPath u v d k t i.val carry false && readPath u v d k t i.val carry true) := by
  have h := value_flat_eq_and u v hv k t carry i
  rw [value_operandLeaves, value_operandLeaves] at h
  simpa only [Boolean.CarrySaveQuery.value, i.isLt, ↓reduceDIte, tree, diagonalLeaves] using h

private theorem fst_diagonal {p d : ℕ} (u v : (ZMod (2 ^ p))[X]) (hv : v.natDegree < d)
    (k : ℕ) (t : List Bool) (i : Fin p) :
    diagonalLeaves d k u v t (Fin.castAdd p i) =
      (readPath u v d k t i.val false false && readPath u v d k t i.val false true) :=
  component_diagonal u v hv k t i false

/-- The only inputs to a signed leaf gate are the two possible operand bits and a local sign bit. -/
def signedGate (v : Fin 7 → Bool) : Bool := (v 0 && v 1) ^^ v 2

/-- A continuation for an operand selects exactly one list and coefficient/bit address. The
other ports answer the correction predicate on short metadata. -/
def signedBit {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ) (path : List Bool)
    (bit : ℕ) (carry : Bool) (j : Fin 7) : Bool :=
  let req (right : Bool) : ConvolutionOperand.Signed.Query := ⟨q, p, i, path, bit, carry, right⟩
  if j = 0 then signedRead u v (req false) else if j = 1 then signedRead u v (req true)
  else correction (req false)

/-- Both possible carry flags have the native single-port interpretation. -/
def signedPorts {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ) (j : Fin 7) (t : List Bool) :
    BitString (p + p) := Fin.append (fun b => signedBit u v q i t b.val false j)
      (fun b => signedBit u v q i t b.val true j)

private theorem value_port {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ) (j : Fin 7)
    (t : List Bool) (b : Fin p) (carry : Bool) :
    Boolean.CarrySaveQuery.value (signedPorts u v q i j) ⟨t, 0, carry, b.val⟩ =
      signedBit u v q i t b.val carry j := by
  cases carry <;> simp [Boolean.CarrySaveQuery.value, signedPorts, tree, component_pair]

/-- Every leaf of the signed tree obeys the same fixed gate. -/
theorem value_reduced_eq_gate {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ)
    (hv : v.natDegree < 2 * q) (t : List Bool) (carry : Bool) (b : Fin p) :
    Boolean.CarrySaveQuery.value (reducedLeaves q i u v) ⟨t, 0, carry, b.val⟩ =
      signedGate (fun j => Boolean.CarrySaveQuery.value (signedPorts u v q i j)
        ⟨t, 0, carry, b.val⟩) := by
  simp only [value_port, signedGate, signedBit, show (1 : Fin 7) ≠ 0 by decide,
    show (2 : Fin 7) ≠ 0 by decide, show (2 : Fin 7) ≠ 1 by decide, ↓reduceIte]
  rcases t with _ | ⟨a, _ | ⟨c, t⟩⟩
  all_goals try cases a
  all_goals try cases c
  all_goals cases carry <;> by_cases hl : i < q <;>
    simp [Boolean.CarrySaveQuery.value, tree, reducedLeaves, SignedSum.leaves, signedRead_mk,
      correction, live, tag, diagonal, BitString.binaryValue, component_pair, component_negative,
      component_diagonal u v hv, fst_diagonal u v hv, hl, b.isLt]

end Cslib.Circuits.Frontier.FastContraction
