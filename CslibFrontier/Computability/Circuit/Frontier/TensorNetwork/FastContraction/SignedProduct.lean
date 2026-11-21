/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProductQuery
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.SignedSum

/-!
# One streamed tree for a reduced contraction-ring product

The tree prepends two tag bits to its row and partial-product fields. Its negative diagonal
is represented by complementing its partial-product bits and carrying one at each leaf.
-/

@[expose] public section
namespace Cslib.Circuits.Frontier.FastContraction

open Polynomial SparseTrinomial GaloisRingArith BitString Boolean Boolean.CarrySaveQuery

/-- All padded partial-product leaves of an ordinary convolution diagonal. -/
noncomputable def diagonalLeaves {p : ℕ} (d k : ℕ) (u v : (ZMod (2 ^ p))[X]) :=
  InnerProduct.flatLeaves (fun j : Fin d => coeffWord u j.val)
    (fun j : Fin d => diagonalWord v k j.val)

/-- The carry of a single shifted partial product is zero, also on padded rows. -/
theorem diagonalLeaves_carry {p : ℕ} (d k : ℕ) (u v : (ZMod (2 ^ p))[X]) (t : List Bool) :
    sndBits (diagonalLeaves d k u v t) = fun _ => false := by
  dsimp only [diagonalLeaves, InnerProduct.flatLeaves]
  split
  · exact Multiplication.component_partialPair_carry _ _ _
  · exact sndBits_append _ _

/-- The value of the flat tree before finishing is already the desired diagonal residue. -/
theorem sum_diagonal {p : ℕ} (d k : ℕ) (u v : (ZMod (2 ^ p))[X]) (hu : u.natDegree < d) :
    SignedSum.sum (diagonalLeaves d k u v) (Nat.clog 2 d + Nat.clog 2 p) = (u * v).coeff k := by
  let leaves := diagonalLeaves d k u v
  let L := Nat.clog 2 d + Nat.clog 2 p
  calc
    _ = SignedSum.residue ((carryLookaheadAdd p).eval interpretation (tree leaves L [])) := by
      rw [SignedSum.residue, val_eval_carryLookaheadAdd_pair, pairVal_tree_mod, ZMod.natCast_mod]
      rfl
    _ = streamedCoeff d p k u v := congrArg (fun n : ℕ => (n : ZMod (2 ^ p)))
      (InnerProduct.val_flat (fun j : Fin d => coeffWord u j.val)
        (fun j : Fin d => diagonalWord v k j.val))
    _ = (u * v).coeff k := (streamedCoeff_eq _ _ _ _ _).trans
      (convolutionCircuit_eq_coeff _ _ _ _ _ hu)

/-- The positive, negative and optional third diagonals of the trinomial remainder. -/
noncomputable def reducedLeaves {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    List Bool → BitString (p + p) :=
  SignedSum.leaves (decide (i < q)) (diagonalLeaves (2 * q) i u v)
    (diagonalLeaves (2 * q) (if i < q then i + 2 * q else i + q) u v)
    (diagonalLeaves (2 * q) (i + 3 * q) u v)

/-- A fixed two-bit tag and the two logarithmic paths suffice for the reduced coefficient. -/
theorem residue_reducedTree {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hu : u.natDegree < 2 * q) :
    SignedSum.residue ((carryLookaheadAdd p).eval interpretation
      (tree (reducedLeaves q i u v) (Nat.clog 2 (2 * q) + Nat.clog 2 p + 2) [])) =
      reducedCoeff q (u * v).coeff i := by
  rw [reducedLeaves, SignedSum.eval _ _ _ _ _ (diagonalLeaves_carry _ _ _ _)]
  simp only [sum_diagonal _ _ _ _ hu]
  by_cases h : i < q <;> simp [reducedCoeff, h]

/-- One queried bit of the native contraction-ring product, including modular underflow. -/
theorem bit_reducedTree (m p : ℕ) (x y : Ring p (modulus m)) (i : Fin (modulus m).length)
    (bit : Fin p) :
    let q := 3 ^ modulusExp m
    (carryLookaheadAdd p).eval interpretation (tree (reducedLeaves q i.val
      (representative m p x) (representative m p y)) (Nat.clog 2 (2 * q) + Nat.clog 2 p + 2) [])
      bit = ((representative m p (x * y)).coeff i.val).val.testBit bit.val := by
  intro q
  let a := representative m p x
  let b := representative m p y
  let word := (carryLookaheadAdd p).eval interpretation
    (tree (reducedLeaves q i.val a b) (Nat.clog 2 (2 * q) + Nat.clog 2 p + 2) [])
  have hu : a.natDegree < 2 * q := by
    simpa only [q, a, length_modulus] using natDegree_representative_lt m p x
  have h : SignedSum.residue word = (representative m p (x * y)).coeff i.val := by
    rw [representative_mul_coeff, residue_reducedTree _ _ _ _ hu]
    simp only [convolutionCircuit_eq_coeff _ _ _ _ _ (natDegree_representative_lt _ _ _)]
    rfl
  have hv := congrArg ZMod.val h
  simp only [SignedSum.residue, ZMod.val_natCast, Nat.mod_eq_of_lt (equivFin p word).isLt] at hv
  exact (testBit_equivFin word bit).symm.trans (congrArg (fun n : ℕ => n.testBit bit.val) hv)

end Cslib.Circuits.Frontier.FastContraction
