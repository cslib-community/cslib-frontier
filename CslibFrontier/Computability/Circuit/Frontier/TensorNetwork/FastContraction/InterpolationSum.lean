/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.InterpolationGrid

/-!
# Coefficient-bit sums for interpolation

The quotient representative is linear over the base residues. Its coefficient at a chosen
ring coordinate therefore distributes through an arbitrary finite sum. A single carry-save
tree counts those word-valued terms modulo the requested precision, with zero padding. This
applies both to the numerator polynomial products and to the final Lagrange combination.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.InterpolationGrid

open Polynomial GaloisRingArith SparseTrinomial BitString Boolean Boolean.CarrySaveQuery

/-- The sum's first operand is the residue word, and its second operand is zero. -/
@[expose] noncomputable def residuePair (p : ℕ) (z : ZMod (2 ^ p)) : BitString (p + p) :=
  Fin.append ((equivFin p).symm ⟨z.val, ZMod.val_lt _⟩) (fun _ => false)

/-- An out-of-range sum path contributes zero. Every valid path names a single operand. -/
@[expose] noncomputable def terms {p : ℕ} (n : ℕ) (f : ℕ → ZMod (2 ^ p))
    (path : List Bool) : BitString (p + p) :=
  residuePair p (if binaryValue path < n then f (binaryValue path) else 0)

/-- An operand continuation reads at most its selected result bit. -/
theorem component_residuePair (p : ℕ) (z : ZMod (2 ^ p)) (carry : Bool) (bit : Fin p) :
    component (residuePair p z) carry bit = if carry then false else z.val.testBit bit.val := by
  cases carry <;> simp only [residuePair, component, Bool.false_eq_true, ↓reduceIte,
    fstBits_append, sndBits_append, equivFin_symm_apply]

/-- A genuine binary carry-save tree for an arbitrary signed modular sum, read at one bit. -/
theorem bit_sum (p n : ℕ) (f : ℕ → ZMod (2 ^ p)) (b : Fin p) :
    (carryLookaheadAdd p).eval interpretation (tree (terms n f) (Nat.clog 2 n) []) b =
      (∑ j ∈ Finset.range n, f j).val.testBit b.val := by
  let rows (j : ℕ) := if j < n then f j else 0
  have hsum : (∑ j ∈ Finset.range (2 ^ Nat.clog 2 n), rows j) =
      ∑ j ∈ Finset.range n, f j := by
    have hs : Finset.range n ⊆ Finset.range (2 ^ Nat.clog 2 n) :=
      Finset.range_mono (Nat.le_pow_clog (by decide : 1 < 2) n)
    calc
      _ = ∑ j ∈ Finset.range n, rows j := (Finset.sum_subset hs fun j _ hj => by
        have h := Finset.mem_range.not.mp hj
        simp [rows, h]).symm
      _ = _ := Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  have hcast : ((∑ j ∈ Finset.range (2 ^ Nat.clog 2 n), (rows j).val : ℕ) : ZMod (2 ^ p)) =
      ∑ j ∈ Finset.range n, f j := by simp [hsum]
  have hval := congrArg ZMod.val hcast
  simp only [ZMod.val_natCast] at hval
  rw [← testBit_equivFin ((carryLookaheadAdd p).eval interpretation
    (tree (terms n f) (Nat.clog 2 n) [])) b, val_eval_carryLookaheadAdd_pair, pairVal_tree_mod]
  change (leafSum (fun path => (fun j => residuePair p (rows j)) (binaryValue path))
    (Nat.clog 2 n) [] % 2 ^ p).testBit b.val = _
  rw [leafSum_binaryValue (fun j => residuePair p (rows j)) (Nat.clog 2 n) []]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add, residuePair, pairVal_append,
    Equiv.apply_symm_apply, val_equivFin_false, Nat.add_zero]
  rw [hval]

/-- A coordinate of a quotient-ring sum is the modular sum of the selected operand coordinates. -/
theorem bit_ringSum (m p n : ℕ) (f : ℕ → Ring p (modulus m)) (r : Fin (modulus m).length)
    (b : Fin p) :
    (carryLookaheadAdd p).eval interpretation (tree
      (terms n (fun j => (representative m p (f j)).coeff r.val)) (Nat.clog 2 n) []) b =
      ((representative m p (∑ j ∈ Finset.range n, f j)).coeff r.val).val.testBit b.val := by
  rw [bit_sum]
  simp [representative]

/-- At a numerator product, the carry-save terms are exactly the products of the two
children's interpolation coefficients on the addressed diagonal. -/
theorem bit_numerator_succ (m p n i base level k : ℕ) (r : Fin (modulus m).length) (b : Fin p) :
    let f := linearFactor m p n i
    let left := blockProduct f base level
    let right := blockProduct f (base + 2 ^ level) level
    (carryLookaheadAdd p).eval interpretation (tree (terms (k + 1)
      (fun t => (representative m p (left.coeff t * right.coeff (k - t))).coeff r.val))
      (Nat.clog 2 (k + 1)) []) b =
      ((representative m p ((blockProduct f base (level + 1)).coeff k)).coeff
        r.val).val.testBit b.val := by
  dsimp only
  rw [bit_ringSum, numerator_succ_coeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun u v => (blockProduct (linearFactor m p n i) base level).coeff u *
      (blockProduct (linearFactor m p n i) (base + 2 ^ level) level).coeff v)]

/-- The Lagrange summand at a single coefficient of the interpolating polynomial. Its
numerator is the root of the balanced product, and the denominator is the native ring inverse. -/
@[expose] noncomputable def summand (m p n k : ℕ) (y : List (List ℕ)) (j : ℕ) :=
  val p (modulus m) (y.getD j []) * val p (modulus m) (GaloisRingArith.inv p (modulus m)
    (basisDen p (modulus m) (points m n) j)) *
    (blockProduct (linearFactor m p n j) 0 (Nat.clog 2 n)).coeff k

/-- At a genuine node the summand is built solely from the value word, inverse of the
balanced denominator, and coefficient of the balanced numerator. -/
theorem summand_eq (m p n k : ℕ) (y : List (List ℕ)) (j : Fin n)
    (hn : n ≤ 2 ^ (modulus m).length) :
    summand m p n k y j = val p (modulus m) (y.getD j []) *
      _root_.Ring.inverse (product m p n j.val 0 (Nat.clog 2 n)) *
      (blockProduct (linearFactor m p n j.val) 0 (Nat.clog 2 n)).coeff k := by
  rw [inverse_product_root _ _ _ j hn]
  rfl

/-- The streamed sum agrees with the coefficient of the actual list-based interpolation;
this identity also handles an empty list of nodes. -/
theorem bit_interp (m p n k : ℕ) (y : List (List ℕ)) (r : Fin (modulus m).length) (b : Fin p) :
    (carryLookaheadAdd p).eval interpretation (tree (terms n
      (fun j => (representative m p (summand m p n k y j)).coeff r.val)) (Nat.clog 2 n) []) b =
      ((representative m p ((pval p (modulus m)
        (interp p (modulus m) (points m n) y)).coeff k)).coeff r.val).val.testBit b.val := by
  rw [bit_ringSum]
  apply congrArg (fun x : Ring p (modulus m) =>
    ((representative m p x).coeff r.val).val.testBit b.val)
  rw [pval_interp, Polynomial.finsetSum_coeff]
  have hn : (points m n).length = n := by simp [points]
  rw [hn]
  apply Finset.sum_congr rfl
  intro j hj
  have num := numerator_root m p n ⟨j, Finset.mem_range.mp hj⟩
  rw [pval_basisNum, hn] at num
  simp only [summand, num, Polynomial.coeff_C_mul]

end Cslib.Circuits.Frontier.FastContraction.InterpolationGrid
