/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCandidates
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Signs of doubly indexed coordinate characteristic coefficients

The zero-centered deformation gives a bivariate characteristic polynomial for each coordinate.
One further coefficient sum extracts a coordinate-value coefficient of an addressed deformation
coefficient. The norm bound and the prime-window sign algorithm then recover its integer sign
from the residues at a fixed counting level over the controlled source evaluator.

This composes the coordinate evaluator adapted from lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183` with the coefficient extraction and sign recovery
in [OpenAI2026CountingHierarchy], Lemma 2.4 and Proposition 2.6, for the polynomial in
Proposition 6.3, equation (6.11). Highest nonzero deformation coefficient selection and real
coordinate coverage remain open in
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

private theorem candidateCoefficientResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d i j k : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    (fun (w, p) => coefficientResidue p (k w) (fun t =>
      criticalCoordinateCandidateValue p (n w) (d w) (i w) (j w) t
        (fun z => C.evaluate (w, p, z)))) ∈
          CountingFunction (a + 12) (encPair enc encNat) encNat := by
  let queryEnc := encPair enc encNat
  have hw := fst enc encNat
  have hquery := fst queryEnc encNat
  have hvalue := CountingFunction.preprocess C.evaluate_mem
    (input := encPair (encPair queryEnc encNat) (encList encNat))
    (g := fun (((w, p), _), z) => (w, p, z)) (by fun_prop)
  let evaluate (q : (α × ℕ) × ℕ) :=
    criticalCoordinateCandidateValue q.1.2 (n q.1.1) (d q.1.1) (i q.1.1) (j q.1.1) q.2
      (fun z => C.evaluate (q.1.1, q.1.2, z))
  have hc : evaluate ∈ CountingFunction (a + 11) (encPair queryEnc encNat) encNat :=
    criticalCoordinateCandidateValue_mem (a := a)
      (Decoder.pair (Decoder.pair E Decoder.nat) Decoder.nat)
      ((snd enc encNat).comp hquery) (C.arity_computable.comp (hw.comp hquery))
      (hd.comp (hw.comp hquery)) (hi.comp (hw.comp hquery)) (hj.comp (hw.comp hquery))
      (snd queryEnc encNat) hvalue
  exact coefficientResidue_mem (p := fun q : α × ℕ => q.2)
    (k := fun q => k q.1) (value := evaluate) (Decoder.pair E Decoder.nat)
    (snd enc encNat) (hk.comp hw) hc

/-- A controlled input at level `a` yields the sign of the coefficient at any binary pair
of deformation and coordinate-value indices at level `a + 15`. The coordinate index
and pure-power exponent minus one are binary, and the source arity is unary. -/
theorem criticalCoordinateCandidateCoefficientSign_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d j k : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    (fun w => (((Polynomial.Bivariate.swap (parametricCoordinatePolynomial
      (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).coeff (j w)).coeff (k w)).sign) ∈
        CountingFunction (a + 15) enc encIntBin := by
  let P (w : α) := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
  let Q (w : α) := (Polynomial.Bivariate.swap (P w)).coeff (j w)
  let D (w : α) := (d w + 1) ^ n w
  let indexBound (w : α) := max (max (D w * D w) (coordinateParameterDegreeBound (n w) (d w)))
    (max (j w) (k w))
  let cutoff (w : α) := max (C.cutoff w)
    (max ((d w + 1) * (D w + n w * d w + 1) + 1) (indexBound w + 1))
  let R : IntegerResidueAccess (fun w => (Q w).coeff (k w)) := {
    magnitudeExponent := fun w => parametricCoordinateCoeffNormExponent (n w) (d w + 1)
      (C.massExponent w)
    admissible := fun w p => p.Prime ∧ cutoff w < p
    modulus_pos := fun _ _ hp => hp.1.pos
    residue := fun (w, p) => coefficientResidue p (k w) (fun t =>
      criticalCoordinateCandidateValue p (n w) (d w) (i w).val (j w) t
        (fun z => C.evaluate (w, p, z)))
    magnitude_le := fun w =>
      (Polynomial.natAbs_coeff_le_coeffNorm1 _ _).trans
        ((Polynomial.coeffNorm1_coeff_swap_le _ _).trans
          (parametricCoordinatePolynomial_bivariateCoeffNorm1_le (Nat.succ_le_succ (hdpos w))
            _ _ (C.mass_le w) _))
    residue_eq := by
      intro w p ⟨hp, hcut⟩
      let : Fact p.Prime := ⟨hp⟩
      dsimp only [cutoff] at hcut
      have hsource : C.cutoff w < p := (le_max_left _ _).trans_lt hcut
      have hcrit : (d w + 1) * (D w + n w * d w + 1) + 1 < p := by omega
      have ha : indexBound w < p - 1 := by omega
      have ⟨⟨hdegree, hparam⟩, hj', hk'⟩ :
          ((D w * D w < p - 1) ∧ coordinateParameterDegreeBound (n w) (d w) < p - 1) ∧
            j w < p - 1 ∧ k w < p - 1 := by simpa only [indexBound, max_lt_iff] using ha
      let φ := Int.castRingHom (ZMod p)
      have hQ : ((Q w).map φ).natDegree < p - 1 := by
        have h := (Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap
          (Polynomial.Bivariate.swap (P w)) (j w)).trans_eq
          (congrArg Polynomial.natDegree (Polynomial.Bivariate.swap_swap_apply (P w)))
        have hD : D w ≤ D w * D w := Nat.le_mul_of_pos_right _ (by dsimp only [D]; positivity)
        exact Polynomial.natDegree_map_le.trans_lt
          (h.trans ((parametricCoordinatePolynomial_natDegree _ _ _ _).le.trans hD)
            |>.trans_lt hdegree)
      have hvalue (z : List ℕ) :
          (C.evaluate (w, p, z) : ZMod p) =
            eval₂ φ (fun l : Fin (n w) => ((z[l.val]?.getD 0 : ℕ) : ZMod p)) (F w) := by
        rw [C.evaluate_eq w p z hp hsource, evaluation, ZMod.natCast_zmod_val]
      have heval (t : ℕ) (_ : t < p) :
          (criticalCoordinateCandidateValue p (n w) (d w) (i w).val (j w) t
            (fun z => C.evaluate (w, p, z)) : ZMod p) = ((Q w).map φ).eval (t : ZMod p) := by
        rw [criticalCoordinateCandidateValue_cast (d w) (hdpos w) (F w) (hF w) (i w)
          (j w) t hcrit hdegree hparam hj' _ hvalue, Polynomial.eval_map]
      dsimp only
      rw [coefficientResidue_eq_val _ _ _ hQ hk' heval, Polynomial.coeff_map]
      simpa only [φ, Int.coe_castRingHom, Int.toNat_natCast] using
        congrArg Int.toNat (ZMod.val_intCast (n := p) ((Q w).coeff (k w)))
  }
  have hell := binary_add' hd (.const 1)
  have hD : ComputableInPolyTime D enc encNat := binary_pow' hell C.arity_computable
  have ha : ComputableInPolyTime indexBound enc encNat :=
    binary_max' (binary_max' (binary_mul' hD hD)
      (coordinateParameterDegreeBound_polyTime C.arity_computable hd)) (binary_max' hj hk)
  have hcutoff : ComputableInPolyTime cutoff enc encNat :=
    binary_max' C.cutoff_computable
      (binary_max' (binary_add' (binary_mul' hell
        (binary_add' (binary_add' hD (binary_mul' (unary_to_binary.comp C.arity_computable) hd))
          (.const 1))) (.const 1)) (binary_add' ha (.const 1)))
  have hR : R.InCountingFunction (a + 12) enc := by
    refine ⟨parametricCoordinateCoeffNormExponent_polyTime C.arity_computable
      hell C.mass_computable, ?_⟩
    exact candidateCoefficientResidue_mem C E hd hi hj hk
  have hsign := R.sign_mem_CountingFunction E hR hcutoff (fun _ _ hp =>
    let h := Nat.mem_primesLE_sdiff_primesLE_iff.mp hp
    ⟨h.1, h.2.1⟩)
  have hmax : max (a + 12) 5 = a + 12 := max_eq_left (by omega)
  simpa only [hmax, Nat.add_assoc] using hsign

end Cslib.Complexity.RealAlgebraic.Controlled
