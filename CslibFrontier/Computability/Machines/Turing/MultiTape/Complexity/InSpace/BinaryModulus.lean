/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryIrreducible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FindCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Outer binary-field modulus search in native space

Search in increasing code order for the existing field modulus of the requested degree,
using the native binary irreducibility test. The binary upper bound and each live candidate
have length at most linear in the degree. The output is the modulus coefficient word,
least significant coefficient first.

## Main results

* `Turing.BinaryField.modulusBitsScan_inSpace`: native modulus search in space linear in
  the numeric degree.
* `Turing.BinaryField.modulusBitsScan_inSpace_of_irreducible`: native space for the modulus
  search given the irreducibility test certificate.
-/

public section

namespace Turing.BinaryField

open Cslib Cslib.BinaryField MultiTapeTM MultiTapeTM.ComputableInSpace

private theorem modulusTest_inSpace
    (ht : ComputableInSpace isIrreducibleCode encNat encBool (fun m => (encNat m).length)) :
    ComputableInSpace (fun p : ℕ × ℕ => Nat.log 2 p.2 == p.1 && isIrreducibleCode p.2)
      (encPair encNat encNat) encBool (fun p => (encPair encNat encNat p).length) := by
  have hm := snd encNat encNat
  have hlog := budget_natPred (budget_comp_linear natSize hm)
  have hdegree := budget_natEq hlog (fst encNat encNat)
  have hirr := budget_comp_linear ht hm
  exact (budget_boolAnd hdegree hirr).of_enc_eq fun p => by
    simp only [← Nat.log2_eq_log_two, Nat.log2_eq_size_sub_one, beq_eq_decide]

/-- Given native binary irreducibility testing, select the existing modulus in space linear
in the numeric degree. The input is the binary degree and the output is its raw
little-endian coefficient word. -/
theorem modulusBitsScan_inSpace_of_irreducible
    (ht : ComputableInSpace isIrreducibleCode encNat encBool (fun m => (encNat m).length)) :
    ComputableInSpace modulusBitsScan encNat encBits (fun w => w + 1) := by
  have hin : (fun w => (encNat w).length) ≼ fun w => w + 1 :=
    .of_le fun w => (length_encNat_le_self w).trans (Nat.le_succ w)
  have hw := budget_id hin
  have hcount := budget_natPow_variable (budget_const (encB := encNat) 2)
    (budget_natSucc hw) (.of_le_linear 6 0 fun w => by
      have hlen := length_encNat_le_self (w + 1)
      have htwo : (encNat 2).length = 2 := rfl
      rw [htwo]
      omega)
  have harg := budget_prod hw (budget_prod (budget_const (encB := encNat) 0) hcount)
  have hscan := budget_comp_linear (ComputableInSpace.findCode (modulusTest_inSpace ht)) harg
  exact (budget_optionGetD 0 hscan).of_enc_eq fun w => by
    rw [modulusBitsScan_eq_findCode]
    rfl

/-- The native binary irreducibility test gives modulus search in space linear in the degree. -/
theorem modulusBitsScan_inSpace :
    ComputableInSpace modulusBitsScan encNat encBits (fun w => w + 1) :=
  modulusBitsScan_inSpace_of_irreducible isIrreducibleCode_inSpace

end Turing.BinaryField
