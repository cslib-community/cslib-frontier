/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelWitness
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalDeterminantFeasibility
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalLabelDeterminantEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# The sign of the critical label determinant

Above a common prime cutoff the source evaluator gives the residues of the determinant
for the decoded label and bounded shift. The binary magnitude exponent and these residues
give the sign at counting level `F_(a+24)` for a controlled source at level `F_a`.

This adapts `ControlledNormAccess` and `ControlledNormComputability` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The source's coded determinant and resource
budgets are replaced by the frontier derivative-sign decoder, shifted label and
shared coefficient norm bounds.

## Main results

* `Cslib.Complexity.RealAlgebraic.Controlled.criticalLabelDeterminantSign_mem` constructs the
  sign algorithm directly from controlled source access.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem

/-- A controlled source supplies the sign of the critical quotient determinant at
level `F_(a+24)`. The degree bound is `d + 1`, the witness code is decoded to the
bounded derivative-sign list, and the binary shift is reduced modulo the quotient
dimension plus one. -/
theorem criticalLabelDeterminantSign_mem {α : Type} {n : α → ℕ} {enc : α ↪ List Bool}
    {a : ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc) {d e : α → ℕ}
    {data : α → List RootLabelTestCode} (hdpos : ∀ w, 1 ≤ d w)
    (hdegree : ∀ w, (P w).totalDegree ≤ d w + 1)
    (hd : ComputableInPolyTime d enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode) :
    (fun w =>
      let ell := d w + 1
      let D := ell ^ n w
      let label := decodeRootLabel (D := D) (by positivity) (n w * ell.size) (data w)
      (criticalLabelDeterminant (by omega : 1 ≤ ell) (C.massExponent w) (P w)
        (hdegree w) label (e w % (D + 1))).sign) ∈ CountingFunction (a + 24) enc encIntBin := by
  let ell (w : α) := d w + 1
  let D (w : α) := ell w ^ n w
  let determinant (w : α) := criticalLabelDeterminant (by dsimp only [ell]; omega : 1 ≤ ell w)
    (C.massExponent w) (P w) (hdegree w)
    (decodeRootLabel (D := D w) (by dsimp only [D, ell]; positivity) (n w * (ell w).size) (data w))
    (e w % (D w + 1))
  let cutoff (w : α) := max (C.cutoff w)
    (criticalLabelDeterminantPrimeCutoff (n w) (d w) (C.massExponent w))
  let R : IntegerResidueAccess determinant := {
    magnitudeExponent := fun w => criticalLabelDeterminantExponent (n w) (ell w) (C.massExponent w)
    admissible := fun w p => p.Prime ∧ cutoff w < p
    modulus_pos := fun _ _ hp => hp.1.pos
    residue := fun (w, p) => criticalLabelDeterminantResidue p (n w) (d w)
      (C.massExponent w) (e w) (data w) (fun z => C.evaluate (w, p, z))
    magnitude_le := fun w => natAbs_criticalLabelDeterminant_le
      (Nat.succ_le_succ (hdpos w)) _ _ (C.mass_le w) _
      (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _)))
    residue_eq := by
      intro w p ⟨hp, hcut⟩
      let : Fact p.Prime := ⟨hp⟩
      let : NeZero p := ⟨hp.ne_zero⟩
      have hcast := criticalLabelDeterminantResidue_cast (d w) (hdpos w) (C.massExponent w)
        (e w) (P w) (hdegree w) (C.mass_le w) ((le_max_right _ _).trans_lt hcut) (data w)
        (fun z => C.evaluate (w, p, z)) fun z => by
          rw [C.evaluate_eq w p z hp ((le_max_left _ _).trans_lt hcut),
            evaluation, ZMod.natCast_zmod_val, eval_map]
      have hval := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (criticalLabelDeterminantResidue_lt hp.pos _ _ _ _ _ _)] at hval
      exact hval.trans (by
        simpa only [Int.toNat_natCast] using
          congrArg Int.toNat (ZMod.val_intCast (n := p) (determinant w)))
  }
  have hR : R.InCountingFunction (a + 21) enc := by
    refine ⟨criticalLabelDeterminantExponent_polyTime C.arity_computable
      (binary_add' hd (.const 1)) C.mass_computable, ?_⟩
    have hf := fst enc encNat
    exact criticalLabelDeterminantResidue_mem (Decoder.pair E Decoder.nat) (snd enc encNat)
      (C.arity_computable.comp hf) (hd.comp hf) (C.mass_computable.comp hf)
      (he.comp hf) (hdata.comp hf)
      (CountingFunction.preprocess C.evaluate_mem
        (input := encPair (encPair enc encNat) (encList encNat))
        (g := fun ((w, p), z) => (w, p, z)) (by fun_prop))
  simpa only [show max (a + 21) 5 = a + 21 by omega, Nat.add_assoc] using
    R.sign_mem_CountingFunction E hR
      (binary_max' C.cutoff_computable
        (criticalLabelDeterminantPrimeCutoff_polyTime C.arity_computable hd C.mass_computable))
      fun _ _ hp => ⟨(Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).1,
        (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.1⟩

end Cslib.Complexity.RealAlgebraic.Controlled
