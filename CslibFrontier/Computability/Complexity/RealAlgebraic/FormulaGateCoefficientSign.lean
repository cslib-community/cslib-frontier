/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
public import CslibFrontier.Computability.Complexity.RealAlgebraic.FormulaGateCoefficientEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Signs of indexed formula gate coefficients

The gate coefficient norm and prime interpolation cutoff give the bounds needed by
Frontier's residue-sign theorem. This composes the residue access of the indexed
family in `LeanCanny.ETR.FormulaAtomPolynomials.access` at lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183` with sign recovery.
The coordinate-value computation for the critical-point family remains open.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Logic.RealArithmetic Turing.MultiTapeTM ComputableInPolyTime

/-- An indexed substituted gate coefficient has a sign computation at level
`max (a + 1) 5 + 3` when its coordinate evaluator at Kronecker points has level `a`. The word and
all numeric bounds and indices use raw bit strings and binary naturals. The coordinate
query receives an instance, a binary modulus and a binary field element, and returns a
framed list of binary residues. Its semantic guarantee is only needed at primes above
the supplied coordinate cutoff and at the canonical field representatives. -/
theorem formulaWordGateCoefficientSign_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {word : α → List Bool}
    (coordinates : (w : α) → Fin (word w).length → Polynomial (Polynomial ℤ))
    {gate i j inner outer massExponent pointCutoff : α → ℕ}
    {point : (α × ℕ) × ℕ → List ℕ}
    (hword : ComputableInPolyTime word enc encBits)
    (hgate : ComputableInPolyTime gate enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat)
    (hinner : ComputableInPolyTime inner enc encNat)
    (houter : ComputableInPolyTime outer enc encNat)
    (hmass : ComputableInPolyTime massExponent enc encNat)
    (hcutoff : ComputableInPolyTime pointCutoff enc encNat)
    (hpoint : point ∈ CountingFunction a (encPair (encPair enc encNat) encNat) (encList encNat))
    (hinnerBound : ∀ w k, (Polynomial.Bivariate.swap (coordinates w k)).natDegree ≤ inner w)
    (houterBound : ∀ w k, (coordinates w k).natDegree ≤ outer w)
    (hmassBound : ∀ w k, (coordinates w k).bivariateCoeffNorm1 ≤ 2 ^ massExponent w)
    (hpointEq : ∀ w p, p.Prime → pointCutoff w < p → ∀ z < p, ∀ k : Fin (word w).length,
      (((point ((w, p), z))[k.val]?.getD 0 : ℕ) : ZMod p) =
        Polynomial.aevalAeval (z : ZMod p)
          ((z : ZMod p) ^ formulaWordGateKroneckerRadix (word w) (inner w)) (coordinates w k)) :
    (fun w => (((formulaWordGatePolynomial (word w) (gate w) (coordinates w)).coeff
      (j w)).coeff (i w)).sign) ∈ CountingFunction (max (a + 1) 5 + 3) enc encIntBin := by
  let P (w : α) := formulaWordGatePolynomial (word w) (gate w) (coordinates w)
  let radix (w : α) := formulaWordGateKroneckerRadix (word w) (inner w)
  let cutoff (w : α) :=
    max (pointCutoff w) (formulaWordGateCoefficientPrimeCutoff (word w) (inner w) (outer w))
  let exponent (w : α) := formulaWordGateTermBudget (word w) * (massExponent w + 1)
  let R : IntegerResidueAccess (fun w => ((P w).coeff (j w)).coeff (i w)) := {
    magnitudeExponent := exponent
    admissible := fun w p => p.Prime ∧ cutoff w < p
    modulus_pos := fun _ _ hp => hp.1.pos
    residue := fun (w, p) =>
      let modulus := max p 1
      formulaWordGateCoefficientResidue (word w) (gate w) modulus (radix w) (i w) (j w)
        (fun z => point ((w, modulus), z))
    magnitude_le := fun w => by
      calc
        _ ≤ ((P w).coeff (j w)).coeffNorm1 := Polynomial.natAbs_coeff_le_coeffNorm1 _ _
        _ ≤ (P w).bivariateCoeffNorm1 := Polynomial.coeffNorm1_coeff_le_bivariateCoeffNorm1 _ _
        _ ≤ (2 * 2 ^ massExponent w) ^ formulaWordGateTermBudget (word w) :=
          formulaWordGatePolynomial_bivariateCoeffNorm1_le _ _ _ Nat.one_le_two_pow (hmassBound w)
        _ = 2 ^ exponent w := by
          change _ = 2 ^ (formulaWordGateTermBudget (word w) * (massExponent w + 1))
          rw [← pow_succ', ← pow_mul, Nat.mul_comm (massExponent w + 1)]
    residue_eq := by
      intro w p ⟨hp, hcut⟩
      let : Fact p.Prime := ⟨hp⟩
      have hsource := (le_max_left _ _).trans_lt hcut
      have hgateCutoff := (le_max_right _ _).trans_lt hcut
      obtain ⟨hr, hdegree⟩ := formulaWordGateCoefficientPrimeCutoff_bounds (word w) (gate w)
        (coordinates w) (hinnerBound w) (houterBound w) hgateCutoff
      dsimp only
      rw [max_eq_left hp.pos,
        formulaWordGateCoefficientResidue_eq_val (word w) (gate w) (coordinates w)
          (i w) (j w) (fun z => point ((w, p), z)) hr hdegree (hpointEq w p hp hsource)]
      simpa only [Int.toNat_natCast] using
        congrArg Int.toNat (ZMod.val_intCast (n := p) (((P w).coeff (j w)).coeff (i w)))
  }
  have hR : R.InCountingFunction (a + 1) enc := by
    refine ⟨binary_mul' (formulaWordGateTermBudget_polyTime hword)
      (binary_add' hmass (.const 1)), ?_⟩
    have hw := fst enc encNat
    have hp := binary_max' (snd enc encNat) (.const 1)
    have hr := (formulaWordGateKroneckerRadix_polyTime hword hinner).comp hw
    have hargs := ((hw.prod hp).comp (fst (encPair enc encNat) encNat)).prod
      (snd (encPair enc encNat) encNat)
    change (fun (w, p) => formulaWordGateCoefficientResidue (word w) (gate w) (max p 1)
      (radix w) (i w) (j w) (fun z => point ((w, max p 1), z))) ∈
        CountingFunction (a + 1) (encPair enc encNat) encNat
    exact formulaWordGateCoefficientResidue_mem (point := fun ((w, p), z) =>
      point ((w, max p 1), z)) (Decoder.pair D Decoder.nat)
      (hword.comp hw) (hgate.comp hw) hp (fun _ => (le_max_right _ _ : 1 ≤ _))
      hr (hi.comp hw) (hj.comp hw) (CountingFunction.preprocess hpoint hargs)
  have hL : ComputableInPolyTime cutoff enc encNat :=
    binary_max' hcutoff (formulaWordGateCoefficientPrimeCutoff_polyTime hword hinner houter)
  exact R.sign_mem_CountingFunction D hR hL fun _ _ h => by
    have hp := Nat.mem_primesLE_sdiff_primesLE_iff.mp h
    exact ⟨hp.1, hp.2.1⟩

end Cslib.Complexity.RealAlgebraic
