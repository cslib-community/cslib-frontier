/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProduct
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.ConvolutionPath
public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Path

/-!
# Streamed convolution queries in the contraction ring

Canonical input coordinates feed the outer row-selection tree and inner shifted product tree.
Their terminal router reads a single selected operand address. The two claims for a nonzero
partial-product bit are combined by conjunction.
-/

public section
namespace Cslib.Circuits.Frontier.FastContraction

open Polynomial SparseTrinomial GaloisRingArith
open Boolean.CarrySaveQuery

/-- Binary coefficient word of a polynomial, including zero beyond its degree. -/
noncomputable def coeffWord {p : ℕ} (u : (ZMod (2 ^ p))[X]) (j : ℕ) : BitString p :=
  (BitString.equivFin p).symm ⟨(u.coeff j).val, ZMod.val_lt _⟩

/-- Word on the second side of row j, padded with zeros for negative indices. -/
noncomputable def diagonalWord {p : ℕ} (v : (ZMod (2 ^ p))[X]) (k j : ℕ) : BitString p :=
  (BitString.equivFin p).symm ⟨(if j ≤ k then v.coeff (k - j) else 0).val, ZMod.val_lt _⟩

/-- A single streamed diagonal, with one final carry-lookahead addition. -/
@[expose] noncomputable def streamedCoeff (d p k : ℕ) (u v : (ZMod (2 ^ p))[X]) : ZMod (2 ^ p) :=
  ((BitString.equivFin p (InnerProduct.result (fun j : Fin d => coeffWord u j.val)
    (fun j : Fin d => diagonalWord v k j.val))) : ℕ)

theorem streamedCoeff_eq (d p k : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    streamedCoeff d p k u v = convolutionCircuit d p k u v := by
  rw [streamedCoeff, InnerProduct.val_result, convolutionCircuit,
    Boolean.Modular.val_eval_innerProduct]
  simp only [coefficientWords, BitString.block_blocksEquiv_symm, coeffWord, diagonalWord,
    Equiv.apply_symm_apply]

/-- The native coefficient output is computed by two or three streamed convolution trees. -/
theorem mul_getD_eq_streamed (m p : ℕ) (c d : List ℕ) (i : Fin (modulus m).length) :
    ((mul p (modulus m) c d).getD i.val 0 : ZMod (2 ^ p)) = reducedCoeff (3 ^ modulusExp m)
      (fun k => streamedCoeff (modulus m).length p k
        (representative m p (val p (modulus m) c)) (representative m p (val p (modulus m) d)))
      i.val := by
  simpa only [streamedCoeff_eq] using mul_getD_eq_reduced m p c d i

/-- Evaluate a single router result on the selected input. Absent requests return zero. -/
@[expose] def readOperand {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (a : ConvolutionOperand.Input) : Bool :=
  (ConvolutionOperand.run a).elim false fun j =>
    (if a.right then (v.coeff j.1).val else (u.coeff j.1).val).testBit j.2

/-- A real shifted-product leaf agrees with the conjunction of the two routed input bits.
The result also handles diagonals outside the coefficient window and carry/shift padding. -/
theorem leaf_eq_routed {d p : ℕ} (u v : (ZMod (2 ^ p))[X]) (hv : v.natDegree < d)
    (k : ℕ) (j : Fin d) (shift : List Bool) (carry : Bool) (i : Fin p) :
    Boolean.CarrySaveQuery.value
        (Multiplication.leaves (coeffWord u j.val) (diagonalWord v k j.val))
        ⟨shift, 0, carry, i.val⟩ =
      (readOperand u v ⟨d, p, k, j.val, BitString.binaryValue shift, i.val, carry, false⟩ &&
       readOperand u v ⟨d, p, k, j.val, BitString.binaryValue shift, i.val, carry, true⟩) := by
  rw [Multiplication.value_leaf]
  cases carry
  · by_cases hs : BitString.binaryValue shift ≤ i.val
    · have hs' : BitString.binaryValue shift < p := hs.trans_lt i.isLt
      by_cases hj : j.val ≤ k
      · by_cases hk : k - j.val < d
        · simp [readOperand, ConvolutionOperand.run, ConvolutionOperand.active, coeffWord,
            diagonalWord, BitString.equivFin_symm_apply, hs, hs', hj, hk, i.isLt, j.isLt]
        · have hz : v.coeff (k - j.val) = 0 := coeff_eq_zero_of_natDegree_lt
            (hv.trans_le (Nat.le_of_not_gt hk))
          simp [readOperand, ConvolutionOperand.run, ConvolutionOperand.active, diagonalWord,
            BitString.equivFin_symm_apply, hs, hs', hj, hk, hz, i.isLt, j.isLt]
      · simp [readOperand, ConvolutionOperand.run, ConvolutionOperand.active, diagonalWord,
          BitString.equivFin_symm_apply, hs, hs', hj, j.isLt]
    · simp [readOperand, ConvolutionOperand.run, ConvolutionOperand.active, hs]
  · simp [readOperand, ConvolutionOperand.run, ConvolutionOperand.active]

/-- Read one operand bit for a flat path and return zero for an absent request. -/
@[expose] noncomputable def readPath {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (d k : ℕ)
    (path : List Bool) (i : ℕ) (carry right : Bool) : Bool :=
  readOperand u v (ConvolutionOperand.unpack ⟨d, p, k, path, i, carry, right⟩)

/-- The word pair exposed to the carry-save evaluator by one operand continuation. -/
noncomputable def operandLeaves {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (d k : ℕ)
    (right : Bool) (path : List Bool) : BitString (p + p) :=
  Fin.append (fun i => readPath u v d k path i.val false right)
    (fun i => readPath u v d k path i.val true right)

private theorem component_append {p : ℕ} (a b : BitString p) (i : Fin p) (carry : Bool) :
    component (Fin.append a b) carry i = if carry then b i else a i := by
  cases carry
  · exact congrFun (BitString.fstBits_append a b) i
  · exact congrFun (BitString.sndBits_append a b) i

/-- The semantic leaf of an individual operand is its one routed input bit. -/
theorem value_operandLeaves {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (d k : ℕ)
    (path : List Bool) (i : Fin p) (carry right : Bool) :
    Boolean.CarrySaveQuery.value (operandLeaves u v d k right) ⟨path, 0, carry, i.val⟩ =
      readPath u v d k path i.val carry right := by
  cases carry <;> simp [Boolean.CarrySaveQuery.value, tree, operandLeaves, component_append]

/-- The carry word of a routed partial product is zero on each operand. -/
@[simp] theorem readPath_carry {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (d k : ℕ)
    (path : List Bool) (i : ℕ) (right : Bool) : readPath u v d k path i true right = false := by
  simp [readPath, readOperand, ConvolutionOperand.unpack, ConvolutionOperand.run,
    ConvolutionOperand.active]

/-- Each leaf of the single physical tree is a conjunction of two native operand lookups. -/
theorem value_flat_eq_and {d p : ℕ} (u v : (ZMod (2 ^ p))[X]) (hv : v.natDegree < d)
    (k : ℕ) (path : List Bool) (carry : Bool) (i : Fin p) :
    Boolean.CarrySaveQuery.value (InnerProduct.flatLeaves (fun j : Fin d => coeffWord u j.val)
      (fun j : Fin d => diagonalWord v k j.val)) ⟨path, 0, carry, i.val⟩ =
      ((Boolean.CarrySaveQuery.value (operandLeaves u v d k false) ⟨path, 0, carry, i.val⟩) &&
       (Boolean.CarrySaveQuery.value (operandLeaves u v d k true) ⟨path, 0, carry, i.val⟩)) := by
  simp only [Boolean.CarrySaveQuery.value, i.isLt, ↓reduceDIte, tree, operandLeaves,
    component_append]
  let j := BitString.binaryValue (path.take (Nat.clog 2 d))
  let ss := path.drop (Nat.clog 2 d)
  by_cases hj : j < d
  · have hh := leaf_eq_routed u v hv k ⟨j, hj⟩ ss carry i
    cases carry <;> simpa only [Boolean.CarrySaveQuery.value, i.isLt, ↓reduceDIte, tree,
      InnerProduct.flatLeaves, j, hj, Bool.false_eq_true, ↓reduceIte, readPath,
      ConvolutionOperand.unpack, ss] using hh
  · cases carry <;>
      simp [InnerProduct.flatLeaves, j, hj, readPath, ConvolutionOperand.unpack, readOperand,
        ConvolutionOperand.run, ConvolutionOperand.active, component_append] at *

end Cslib.Circuits.Frontier.FastContraction
