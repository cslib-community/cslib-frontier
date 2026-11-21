/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedProduct
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Truncated
import Mathlib.Data.List.GetD

/-!
# Balanced products for the standard interpolation grid

The node with index `i` has the binary digits of `i` as polynomial coefficients. Each leaf of a
Lagrange denominator is either the identity or a difference of two such nodes. Its bits can be
read directly from the two indices. Every internal product splits into two adjacent intervals
and uses the existing reduced-product coefficient tree.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.InterpolationGrid

open Polynomial GaloisRingArith SparseTrinomial Boolean Boolean.CarrySaveQuery

/-- The ordered list of actual zero-one lifted interpolation points. -/
@[expose] def points (m n : ℕ) : List (List ℕ) :=
  (List.range n).map (FastContraction.digits (modulus m).length)

/-- A single grid point in the contraction ring. -/
@[expose] noncomputable def node (m p i : ℕ) : Ring p (modulus m) :=
  val p (modulus m) (FastContraction.digits (modulus m).length i)

private theorem get_point (m n : ℕ) (i : Fin n) :
    (points m n).getD i.val [] = FastContraction.digits (modulus m).length i.val := by
  rw [List.getD_eq_getElem _ _ (by simp [points])]
  simp [points]

/-- One denominator factor; missing leaves and the omitted center index contribute one. -/
@[expose] noncomputable def factor (m p n i j : ℕ) : Ring p (modulus m) :=
  if j < n ∧ j ≠ i then node m p i - node m p j else 1

/-- A balanced interval product used for both the numerator polynomial and its denominator. -/
@[expose] def blockProduct {R : Type*} [CommMonoid R] (f : ℕ → R) (base level : ℕ) : R :=
  ∏ j ∈ Finset.range (2 ^ level), f (base + j)

@[simp] theorem blockProduct_zero {R : Type*} [CommMonoid R] (f : ℕ → R) (base : ℕ) :
    blockProduct f base 0 = f base := by simp [blockProduct]

/-- Every internal node has precisely two adjacent child intervals. -/
theorem blockProduct_succ {R : Type*} [CommMonoid R] (f : ℕ → R) (base level : ℕ) :
    blockProduct f base (level + 1) =
      blockProduct f base level * blockProduct f (base + 2 ^ level) level := by
  simp only [blockProduct, pow_succ, Nat.mul_two, Finset.prod_range_add, Nat.add_assoc]

/-- The identity-padded dyadic product includes exactly the noncentral grid indices. -/
theorem blockProduct_padded {R : Type*} [CommMonoid R] (f : ℕ → R) (n i : ℕ) :
    blockProduct (fun j => if j < n ∧ j ≠ i then f j else 1) 0 (Nat.clog 2 n) =
      ∏ j ∈ (Finset.range n).erase i, f j := by
  let g (j : ℕ) := if j < n ∧ j ≠ i then f j else 1
  have hs : (Finset.range n).erase i ⊆ Finset.range (2 ^ Nat.clog 2 n) := by
    intro j hj
    exact Finset.mem_range.mpr ((Finset.mem_range.mp (Finset.mem_of_mem_erase hj)).trans_le
      (Nat.le_pow_clog (by decide : 1 < 2) n))
  simp only [blockProduct, Nat.zero_add]
  calc
    _ = ∏ j ∈ (Finset.range n).erase i, g j := (Finset.prod_subset hs fun j _ hj => by
      have hn : ¬ (j < n ∧ j ≠ i) := fun h => hj (Finset.mem_erase.mpr
        ⟨h.2, Finset.mem_range.mpr h.1⟩)
      simp [g, hn]).symm
    _ = _ := Finset.prod_congr rfl fun j hj => ite_eq_left
      ⟨Finset.mem_range.mp (Finset.mem_of_mem_erase hj), (Finset.mem_erase.mp hj).1⟩

/-- Denominator product on a padded dyadic interval. -/
@[expose] noncomputable def product (m p n i base level : ℕ) : Ring p (modulus m) :=
  blockProduct (factor m p n i) base level

/-- The root of the balanced tree computes the native Lagrange denominator exactly. -/
theorem product_root (m p n : ℕ) (i : Fin n) :
    product m p n i.val 0 (Nat.clog 2 n) =
      val p (modulus m) (basisDen p (modulus m) (points m n) i) := by
  unfold product factor
  rw [blockProduct_padded, val_basisDen]
  simp only [points, List.length_map, List.length_range]
  apply Finset.prod_congr rfl
  intro j hj
  have hlt := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  change _ = val p _ ((points m n).getD i.val []) - val p _ ((points m n).getD j [])
  rw [get_point m n i, get_point m n ⟨j, hlt⟩]
  rfl

/-- Below the residue-field cardinality every denominator is a unit, also at precision zero. -/
theorem isUnit_product_root (m p n : ℕ) (i : Fin n) (hn : n ≤ 2 ^ (modulus m).length) :
    IsUnit (product m p n i.val 0 (Nat.clog 2 n)) := by
  rw [product_root, val_basisDen, IsUnit.prod_iff]
  intro j hj
  have hi : i.val < (points m n).length := by simp [points]
  have hj' := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  exact isUnit_val_sub_digits (P := p) (irreducible_modulus m) hn
    (i := ⟨i.val, hi⟩) (j := ⟨j, hj'⟩) fun heq =>
      (Finset.mem_erase.mp hj).1 (congrArg Fin.val heq).symm

/-- Inverting the product root supplies precisely the inverse used in native interpolation. -/
theorem inverse_product_root (m p n : ℕ) (i : Fin n) (hn : n ≤ 2 ^ (modulus m).length) :
    _root_.Ring.inverse (product m p n i.val 0 (Nat.clog 2 n)) =
      val p (modulus m) (GaloisRingArith.inv p (modulus m)
        (basisDen p (modulus m) (points m n) i)) := by
  have hu := isUnit_product_root m p n i hn
  rw [product_root] at hu ⊢
  exact (val_inv_of_isUnit (irreducible_modulus m) hu).symm

/-- A coefficient of a standard point is the corresponding input-index bit. -/
theorem coeff_node (m p i : ℕ) (r : Fin (modulus m).length) :
    (representative m p (node m p i)).coeff r.val = (if i.testBit r.val then 1 else 0) := by
  simp only [representative, node, coeff_modByMonicHom_val, r.isLt, ite_true]
  rw [List.getD_eq_getElem _ _ (by simp [FastContraction.digits])]
  simp [FastContraction.digits]

private theorem coeff_one (m p : ℕ) (r : Fin (modulus m).length) :
    (representative m p 1).coeff r.val = (if r.val = 0 then 1 else 0) := by
  rw [← val_one (p := p) (fl := modulus m)]
  simp only [representative, coeff_modByMonicHom_val, r.isLt, ite_true]
  rw [List.getD_eq_getElem _ _ (by simp [one])]
  simp [one]

/-- Local bit of one denominator factor. Modular subtraction of a one from a zero sets all
precision bits, and the positive coefficient one only sets the low bit. -/
@[expose] def factorBit (n i j r bit : ℕ) : Bool :=
  if j < n ∧ j ≠ i then
    if i.testBit r then !j.testBit r && decide (bit = 0) else j.testBit r
  else decide (r = 0 ∧ bit = 0)

private theorem val_neg_one {n : ℕ} (hn : 0 < n) : (-1 : ZMod n).val = n - 1 := by
  cases n with
  | zero => omega
  | succ k => exact ZMod.val_neg_one k

/-- Direct lookup equals the quotient representative bit, uniformly for the signed difference
and identity padding. -/
theorem factorBit_eq (m p n i j : ℕ) (r : Fin (modulus m).length) (b : Fin p) :
    factorBit n i j r.val b.val =
      ((representative m p (factor m p n i j)).coeff r.val).val.testBit b.val := by
  have hpos := b.isLt
  have h1 : (1 : ZMod (2 ^ p)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hb : Nat.testBit 1 b.val = decide (b.val = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero]
  by_cases hj : j < n ∧ j ≠ i
  · rw [factor, ite_eq_left hj]
    have hsub : (representative m p (node m p i - node m p j)).coeff r.val =
        (representative m p (node m p i)).coeff r.val -
          (representative m p (node m p j)).coeff r.val := by
      simp [representative, map_sub]
    rw [hsub, coeff_node, coeff_node]
    cases hi : i.testBit r.val <;> cases ht : j.testBit r.val <;>
      simp [factorBit, hj, hi, ht, h1, val_neg_one (by positivity : 0 < 2 ^ p),
        Nat.testBit_two_pow_sub_one, b.isLt, hb]
  · rw [factor, ite_eq_right hj, coeff_one]
    by_cases hr : r.val = 0 <;> simp [factorBit, hj, hr, h1, hb]

/-- Every internal bit query directly uses the signed reduced product of its two child values. -/
theorem bit_product_succ (m p n i base level : ℕ) (r : Fin (modulus m).length) (b : Fin p) :
    let q := 3 ^ modulusExp m
    let left := product m p n i base level
    let right := product m p n i (base + 2 ^ level) level
    (carryLookaheadAdd p).eval interpretation (tree (reducedLeaves q r.val
      (representative m p left) (representative m p right))
      (Nat.clog 2 (2 * q) + Nat.clog 2 p + 2) []) b =
      ((representative m p (product m p n i base (level + 1))).coeff r.val).val.testBit b.val := by
  simp only [product, blockProduct_succ]
  exact bit_reducedTree m p _ _ r b

/-- A numerator factor in the interpolation variable; padding contributes a constant one. -/
@[expose] noncomputable def linearFactor (m p n i j : ℕ) : (Ring p (modulus m))[X] :=
  if j < n ∧ j ≠ i then X - C (node m p j) else 1

/-- The same balanced product computes all coefficients of the native numerator polynomial. -/
theorem numerator_root (m p n : ℕ) (i : Fin n) :
    blockProduct (linearFactor m p n i.val) 0 (Nat.clog 2 n) =
      pval p (modulus m) (basisNum p (modulus m) (points m n) i.val) := by
  unfold linearFactor
  rw [blockProduct_padded, pval_basisNum]
  simp only [points, List.length_map, List.length_range]
  apply Finset.prod_congr rfl
  intro j hj
  have hlt := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  change _ = X - C (val p _ ((points m n).getD j []))
  rw [get_point m n ⟨j, hlt⟩]
  rfl

/-- The constant term of the linear numerator factor is the negative of the lifted node.
Its linear coefficient is one. These cases are separate from denominator differences. -/
@[expose] def linearBit (n i j k r bit : ℕ) : Bool :=
  if j < n ∧ j ≠ i then
    if k = 0 then j.testBit r else decide (k = 1 ∧ r = 0 ∧ bit = 0)
  else decide (k = 0 ∧ r = 0 ∧ bit = 0)

/-- Bit-level leaf semantics for every numerator coefficient, including padded factors. -/
theorem linearBit_eq (m p n i j k : ℕ) (r : Fin (modulus m).length) (b : Fin p) :
    linearBit n i j k r.val b.val =
      ((representative m p ((linearFactor m p n i j).coeff k)).coeff r.val).val.testBit b.val := by
  have hp := b.isLt
  have h1 : (1 : ZMod (2 ^ p)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hb : Nat.testBit 1 b.val = decide (b.val = 0) := Bool.eq_iff_iff.mpr (by
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero])
  have hz : (representative m p 0).coeff r.val = 0 := by simp [representative]
  have hn : (representative m p (-node m p j)).coeff r.val =
      -(representative m p (node m p j)).coeff r.val := by simp [representative]
  have hone : ((representative m p 1).coeff r.val).val.testBit b.val =
      decide (r.val = 0 ∧ b.val = 0) := by
    rw [coeff_one]
    by_cases hr : r.val = 0 <;> simp [hr, h1, hb]
  have hneg : ((representative m p (-node m p j)).coeff r.val).val.testBit b.val =
      j.testBit r.val := by
    rw [hn, coeff_node]
    cases j.testBit r.val <;> simp [val_neg_one (by positivity : 0 < 2 ^ p), b.isLt]
  by_cases h : j < n ∧ j ≠ i
  · have hpoly : linearFactor m p n i j = X - C (node m p j) := ite_eq_left h
    rw [linearBit, ite_eq_left h, hpoly, Polynomial.coeff_sub]
    by_cases hk : k = 0
    · subst k
      simp [hneg]
    · by_cases h₁ : k = 1
      · subst k
        simp [hone]
      · simp [hk, h₁, Ne.symm h₁, coeff_X, coeff_C, hz]
  · have hpoly : linearFactor m p n i j = 1 := ite_eq_right h
    rw [linearBit, ite_eq_right h, hpoly, Polynomial.coeff_one]
    by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte, true_and, false_and, hone, hz,
      ZMod.val_zero, Nat.zero_testBit, decide_false]

/-- The coefficient query at an internal numerator node is a convolution of the two child
coefficient arrays over the contraction ring. -/
theorem numerator_succ_coeff (m p n i base level k : ℕ) :
    let f := linearFactor m p n i
    (blockProduct f base (level + 1)).coeff k =
      ∑ t ∈ Finset.antidiagonal k,
        (blockProduct f base level).coeff t.1 *
          (blockProduct f (base + 2 ^ level) level).coeff t.2 := by
  dsimp only
  rw [blockProduct_succ, Polynomial.coeff_mul]

end Cslib.Circuits.Frontier.FastContraction.InterpolationGrid
