/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Roots
public import CslibFrontier.Foundations.Algebra.DFT
import CslibFrontier.Foundations.Data.BitString.Binary
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# The inverse NTT in ML-DSA matrix expansion

[FIPS 204][NISTFIPS204], §2.5, equation (2.1), orders the odd powers of 1753 by reversing
eight bits. Twisting each coefficient by the corresponding power of 1753 reduces the forward
transform to `Cslib.dft` at `1753²`. Undoing the permutation and twist identifies `fromNTT`,
the coefficient conversion used by `Xofs.expandA`, with the scaled DFT at a negative index.
Consequently an entire matrix of uniform NTT entries remains uniform after this conversion.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private abbrev F := ZMod 8380417

private instance : Fact (Nat.Prime 8380417) := ⟨by norm_num1⟩

private theorem bitRev_involutive : Function.Involutive bitRev8 := by
  intro i
  apply Fin.ext
  have h := BitString.lowBits_lsbValue (BitString.lowBits 8 i.val).reverse
  simp only [List.length_reverse, BitString.length_lowBits] at h
  change BitString.lsbValue (BitString.lowBits 8
    (BitString.lsbValue (BitString.lowBits 8 i.val).reverse)).reverse = i.val
  rw [h, List.reverse_reverse]
  exact BitString.lsbValue_lowBits i.isLt

/-- The direct forward NTT of equation (2.1), evaluating the coefficient polynomial at each
bit-reversed odd power of 1753. -/
def toNTT (coeffs : Poly) : Poly := fun i =>
  dft ((1753 : F) ^ 2) (fun j => coeffs j * (1753 : F) ^ j.val) (bitRev8 i)

private theorem fromNTT_get (v : Poly) (j : Fin 256) :
    (fromNTT v).get j = 8347681 * ∑ i, v i * ((nttNode (bitRev8 i))⁻¹) ^ j.val := by
  unfold fromNTT
  simp only [Vector.get_ofFn]
  apply congrArg (fun x : F => 8347681 * x)
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : F => v i * x)
  change (1753 : F) ^ ((511 - 2 * (bitRev8 i).val) * j.val % 512) = _
  rw [← orderOf_zeta, pow_mod_orderOf, pow_mul]
  apply congrArg (fun x : F => x ^ j.val)
  apply eq_inv_of_mul_eq_one_left
  rw [nttNode, ← pow_add]
  have h : 511 - 2 * (bitRev8 i).val + (2 * (bitRev8 i).val + 1) = 512 := by
    have := (bitRev8 i).isLt
    lia
  rw [h, ← orderOf_zeta, pow_orderOf_eq_one]

private theorem square_primitive : IsPrimitiveRoot ((1753 : F) ^ 2) 256 :=
  (IsPrimitiveRoot.iff_orderOf.mpr orderOf_zeta).pow_of_dvd (by decide : 2 ≠ 0) (by decide)

private theorem node_inverse_pow (i j : Fin 256) :
    (nttNode i)⁻¹ ^ j.val = ((1753 : F) ^ j.val)⁻¹ *
      ((1753 : F) ^ 2) ^ (i.val * (-j : Fin 256).val) := by
  let ω : F := 1753 ^ 2
  have hinv : ω ^ (-j : Fin 256).val = (ω ^ j.val)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, ← pow_mod_orderOf, ← square_primitive.eq_orderOf]
    change ω ^ (((-j : Fin 256).val + j.val) % 256) = 1
    rw [← Fin.val_add, neg_add_cancel]
    exact pow_zero _
  change (nttNode i)⁻¹ ^ j.val = _ * ω ^ _
  rw [nttNode, pow_add, pow_one, pow_mul, mul_inv_rev, mul_pow, inv_pow]
  rw [Nat.mul_comm i.val, pow_mul, hinv, inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  simp only [ω, ← pow_mul, Nat.mul_assoc, Nat.mul_comm j.val i.val]

/-- The executable inverse table is an ordinary DFT at the negative index, with the input
permutation undone and the inverse twist and inverse length applied to the output. -/
theorem fromNTT_eq_dft (v : Poly) (j : Fin 256) :
    (fromNTT v).get j = 8347681 * (((1753 : ZMod 8380417) ^ j.val)⁻¹ *
      dft ((1753 : ZMod 8380417) ^ 2) (fun i => v (bitRev8 i)) (-j)) := by
  rw [fromNTT_get, dft]
  apply congrArg (fun x : F => 8347681 * x)
  rw [Finset.mul_sum]
  let e : Fin 256 ≃ Fin 256 := ⟨bitRev8, bitRev8, bitRev_involutive, bitRev_involutive⟩
  refine Fintype.sum_equiv e _ _ fun i => ?_
  change v i * _ = _ * (v (bitRev8 (bitRev8 i)) * _)
  rw [bitRev_involutive, node_inverse_pow]
  change v i * (_ * ((1753 : F) ^ 2) ^ ((bitRev8 i).val * (-j : Fin 256).val)) =
    _ * (v i * ((1753 : F) ^ 2) ^ ((bitRev8 i).val * (-j : Fin 256).val))
  ac_rfl

/-- Converting the forward transform recovers every coefficient of the original polynomial. -/
theorem fromNTT_toNTT : Function.LeftInverse (fun v => (fromNTT v).get) toNTT := by
  intro v
  funext j
  change (fromNTT (toNTT v)).get j = v j
  rw [fromNTT_eq_dft]
  simp only [toNTT, bitRev_involutive _]
  rw [dft_dft_neg square_primitive.isPrincipalRoot]
  have hζ : ((1753 : F) ^ j.val) ≠ 0 := pow_ne_zero _ (by decide +kernel)
  have hlen : (8347681 : F) * 256 = 1 := by decide +kernel
  push_cast
  field_simp [hζ]
  linear_combination v j * hlen

/-- Evaluating a converted polynomial in the FIPS order recovers all its input NTT values. -/
theorem toNTT_fromNTT : Function.LeftInverse toNTT (fun v => (fromNTT v).get) :=
  fromNTT_toNTT.rightInverse_of_card_le le_rfl

/-- NTT coordinates and coefficient coordinates are equivalent by the two explicit transforms.
The forward direction is the actual inverse transform called for each entry of `Xofs.expandA`. -/
@[expose] def fromNTTEquiv : Poly ≃ Poly where
  toFun v := (fromNTT v).get
  invFun := toNTT
  left_inv := toNTT_fromNTT
  right_inv := fromNTT_toNTT

/-- The equivalence applies the exact coefficient conversion used inside `Xofs.expandA`. -/
theorem fromNTTEquiv_apply (v : Poly) : fromNTTEquiv v = (fromNTT v).get := by
  rw [← fromNTTEquiv.toFun_as_coe]
  rfl

/-- Entrywise application of the FIPS matrix expansion's inverse NTT transports a uniform
NTT matrix to a uniform coefficient matrix, including the joint law of all its entries. -/
theorem uniformOfFintype_map_fromNTT (s : Level) :
    (PMF.uniformOfFintype (PublicMatrix s)).map (fun A i j => (fromNTT (A i j)).get) =
      PMF.uniformOfFintype (PublicMatrix s) := by
  let e : PublicMatrix s ≃ PublicMatrix s := fromNTTEquiv.mapMatrix
  have he (A : PublicMatrix s) : e A = fun i j => (fromNTT (A i j)).get := by
    apply Matrix.ext
    intro i j
    rw [show e A = A.map fromNTTEquiv by exact Equiv.mapMatrix_apply .., Matrix.map_apply]
    exact fromNTTEquiv_apply (A i j)
  rw [← funext he]
  exact Probability.PMF.uniformOfFintype_map_equiv e

end Cslib.Crypto.MLDSA.FIPS204
