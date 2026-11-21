/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProduct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.PolyTime.GaloisRingArithmetic.ResidueSeed
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Polynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-!
# Local residue inversion on a short candidate word

At precision one, a whole input has only as many bits as the degree of the selected trinomial.
The degree is polynomial in the binary size of the scale. Once a candidate residue word has
been supplied, this native function checks an output coordinate in polynomial time in that
short word and the binary scale.
-/

@[expose] public section
namespace Cslib.Circuits.Frontier.FastContraction.ResidueInverse

open Turing.MultiTapeTM ComputableInPolyTime GaloisRingArith

/-- The middle exponent can be constructed in unary from a binary scale. -/
theorem half_polyTime :
    ComputableInPolyTime (fun m => 3 ^ modulusExp m) encNat encUnary := by
  have harg := unary_add' (unary_mul' (const 4) binary_log_two) (const 2)
  have he := binary_log_two.comp (unary_to_binary.comp harg)
  have hpow := binary_pow.comp ((const 3).prod he)
  exact binary_to_unary_bounded hpow ((unary_pow 2).comp harg) three_pow_modulusExp_le

/-- The entire sparse trinomial list costs only polynomial time in the binary scale. -/
theorem modulus_binary_polyTime : ComputableInPolyTime modulus encNat (encList encNat) := by
  have hrange := range.comp (unary_mul' (const 2) half_polyTime)
  have hi := snd encNat encUnary
  have half := half_polyTime.comp (fst encNat encUnary)
  have ht := decide_or (decide_eq' hi (const 0)) (decide_eq' hi half)
  have hbody : ComputableInPolyTime (fun q : ℕ × ℕ =>
      if q.2 = 0 ∨ q.2 = 3 ^ modulusExp q.1 then 1 else 0) (encPair encNat encUnary) encNat :=
    (ite ht (const (encOut := encNat) 1) (const 0)).of_enc_eq fun _ => by
      simp only [decide_eq_true_eq, Function.comp_apply]
  exact mapWithInput (f := fun m i => if i = 0 ∨ i = 3 ^ modulusExp m then 1 else 0) hrange hbody

/-- The guessed complete residue fits within a polynomial in the binary scale length. -/
theorem degree_le_size (m : ℕ) : (modulus m).length ≤ 2 * (4 * m.size + 2) ^ 2 := by
  rw [length_modulus]
  refine Nat.mul_le_mul_left _ ((three_pow_modulusExp_le m).trans ?_)
  gcongr
  exact (Nat.log_mono_right (Nat.lt_size_self m).le).trans (by simp)

/-- Binary scale, output coefficient index and a candidate residue word. -/
structure Input where
  /-- The contraction scale. -/
  scale : ℕ
  /-- Requested output coefficient. -/
  index : ℕ
  /-- One bit for each coefficient of the guessed residue input. -/
  guess : List Bool

/-- The two indices are binary and the candidate coefficients are unframed bits. -/
enc_structure encInput : Input where scale : encNat, index : encNat, guess : encBits

/-- Transform the bits into a one-bit coefficient list and compute the selected inverse digit. -/
def run (p : Input) : Bool :=
  ((GaloisRingArith.inv 1 (modulus p.scale) (p.guess.map Bool.toNat)).getD p.index 0).testBit 0

/-- A native fixed machine computes the selected inverse residue bit on any candidate word. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encBool := by
  have hword := (map (of_finite (encIn := encBool) (encOut := encNat) Bool.toNat)).comp
    (bitsToList.comp encInput_guess_deg.computableInPolyTime)
  have hinv := computableInPolyTime_inv (const 1)
    (modulus_binary_polyTime.comp encInput_scale_deg.computableInPolyTime) hword
  exact binary_testBit (listGetD_binary 0 hinv encInput_index_deg.computableInPolyTime) (const 0)

/-- Agrees with an actual inverse coordinate for a unit in the residue ring. -/
theorem run_eq_inverse (m : ℕ) (i : Fin (modulus m).length) (guess : List Bool)
    (h : IsUnit (val 1 (modulus m) (guess.map Bool.toNat))) :
    run ⟨m, i.val, guess⟩ =
      ((representative m 1 (_root_.Ring.inverse (val 1 (modulus m) (guess.map Bool.toNat)))).coeff
        i.val).val.testBit 0 := by
  rw [← val_inv_of_isUnit (irreducible_modulus m) h]
  rw [representative, coeff_modByMonicHom_val, ite_eq_left i.isLt, ZMod.val_natCast,
    Nat.testBit_mod_two_pow]
  simp [run]

end Cslib.Circuits.Frontier.FastContraction.ResidueInverse
