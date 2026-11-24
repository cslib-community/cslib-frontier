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
public import CslibFrontier.Computability.Complexity.RealAlgebraic.FingerprintRootLabelEvaluation
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Derivative
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.BoundedSearch
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelPrecision
import CslibFrontier.Computability.Complexity.RealAlgebraic.UnivariateDerivativeEvaluation
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import Mathlib.Tactic.GCongr

/-!
# Signs of doubly indexed coordinate characteristic coefficients

The zero-centered deformation gives a bivariate characteristic polynomial for each coordinate.
One further coefficient sum extracts a coordinate-value coefficient of an addressed deformation
coefficient. The norm bound and the prime-window sign algorithm then recover its integer sign
from the residues at a fixed counting level over the controlled source evaluator.

This composes the coordinate evaluator adapted from lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183` with the coefficient extraction and sign recovery
in [OpenAI2026CountingHierarchy], Lemma 2.4 and Proposition 2.6, for the polynomial in
Proposition 6.3, equation (6.11). The natural degree in the deformation parameter counts
the thresholds strictly below its highest nonzero coefficient index. Using that binary index
in the addressed evaluator gives uniform modular access to the values and coefficients of the
leading deformation coefficient. Coefficient and binary-order derivative queries use the same
counting level as value queries. For derivatives, the counting sum uses an addressed deformation
index before substituting the integer degree, so the sum does not increase the final level.
The prescribed-root fingerprint evaluator also delays this substitution, preserving the
`a + 20` counting bound of `ControlledIndexedLabels` in lean-canny at the pinned revision.
For supplied fingerprint parameters, `criticalCoordinateFingerprintLabels` packages this
evaluator as a controlled univariate family with binary degree, norm and cutoff bounds.
The leading deformation coefficients themselves form a controlled family at level `a + 18`.
The counting endpoints remain open in
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

private theorem coordinateCoefficient_natDegree_le {n ell : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (i : Fin n) (j : ℕ) :
    ((Polynomial.Bivariate.swap (parametricCoordinatePolynomial hell F hF i)).coeff j).natDegree
      ≤ ell ^ n := by
  refine (Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap _ _).trans_eq ?_
  rw [Polynomial.Bivariate.swap_swap_apply, parametricCoordinatePolynomial_natDegree]

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

private theorem addressedCoordinateCoefficientResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {p d i j k : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hd : ComputableInPolyTime d enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    (fun w => coefficientResidue (p w) (k w) (fun t =>
      criticalCoordinateCandidateValue (p w) (n w) (d w) (i w) (j w) t
        (fun z => C.evaluate (w, p w, z)))) ∈ CountingFunction (a + 12) enc encNat :=
  CountingFunction.preprocess (candidateCoefficientResidue_mem C E hd hi hj hk)
    (ComputableInPolyTime.id'.prod hp)

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
        have h := coordinateCoefficient_natDegree_le (by omega : 1 ≤ d w + 1)
          (F w) (hF w) (i w) (j w)
        have hD : D w ≤ D w * D w := Nat.le_mul_of_pos_right _ (by dsimp only [D]; positivity)
        exact Polynomial.natDegree_map_le.trans_lt (h.trans hD |>.trans_lt hdegree)
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

open Classical in
/-- The natural degree in the deformation parameter has a binary counting-function
certificate at level `a + 18` from a controlled source at level `a`. It is the highest
nonzero coefficient index, with zero as the natural degree of the zero polynomial. -/
theorem criticalCoordinateParameterNatDegree_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    (fun w => (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
      (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).natDegree) ∈
        CountingFunction (a + 18) enc encNat := by
  let P (w : α) := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
  let Q (w : α) := Polynomial.Bivariate.swap (P w)
  let encAddr := encPair enc encNat
  let encCoeff := encPair encAddr encNat
  let decAddr := Decoder.pair E Decoder.nat
  let decCoeff := Decoder.pair decAddr Decoder.nat
  let rowEnd (w : α) := (d w + 1) ^ n w + 1
  let degreeBound (w : α) := coordinateParameterDegreeBound (n w) (d w)
  have hrowEnd : ComputableInPolyTime rowEnd enc encNat :=
    binary_add' (binary_pow' (binary_add' hd (.const 1)) C.arity_computable) (.const 1)
  have hbound : ComputableInPolyTime degreeBound enc encNat :=
    coordinateParameterDegreeBound_polyTime C.arity_computable hd
  have hw := fst enc encNat
  have haddr := fst encAddr encNat
  have hbase := hw.comp haddr
  let C' := C.preprocess (fun q : (α × ℕ) × ℕ => q.1.1) hbase
  have hsign := C'.criticalCoordinateCandidateCoefficientSign_mem
    (d := fun q : (α × ℕ) × ℕ => d q.1.1) decCoeff
    (fun ((w, _), _) => i w) (fun ((w, _), _) => hdpos w) (fun ((w, _), _) => hF w)
    (hd.comp hbase) (hi.comp hbase) ((snd enc encNat).comp haddr) (snd encAddr encNat)
  have hnonzero : (fun ((w, j), k) => decide (((Q w).coeff j).coeff k ≠ 0)) ∈
      CountingFunction (a + 15) encCoeff encBool := by
    have htest : ComputableInPolyTime (fun x : ℤ => decide (0 < x.natAbs)) encIntBin encBool :=
      binary_lt' (.const 0) intBin_natAbs
    have hsignNonzero (x : ℤ) : 0 < x.sign.natAbs ↔ x ≠ 0 :=
      Int.natAbs_pos.trans (not_congr Int.sign_eq_zero_iff_zero)
    simpa only [Function.comp_apply, hsignNonzero, Q, P] using CountingFunction.map hsign htest
  let rowNonzero (q : α × ℕ) :=
    decide (∃ k < rowEnd q.1, decide (((Q q.1).coeff q.2).coeff k ≠ 0) = true)
  have hrow : rowNonzero ∈ CountingFunction (a + 16) encAddr encBool :=
    CountingFunction.exists_range decAddr hnonzero (hrowEnd.comp hw)
  have hrowEq (w : α) (j : ℕ) : rowNonzero (w, j) = true ↔ (Q w).coeff j ≠ 0 := by
    simp only [rowNonzero, decide_eq_true_eq]
    constructor
    · rintro ⟨k, _, hk⟩ hzero
      exact hk (by rw [hzero, Polynomial.coeff_zero])
    · intro hj
      have hdeg := Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap (Q w) j
      rw [show Polynomial.Bivariate.swap (Q w) = P w from
        Polynomial.Bivariate.swap_swap_apply (P w),
        parametricCoordinatePolynomial_natDegree] at hdeg
      exact ⟨_, Nat.lt_succ_of_le hdeg, by
        rwa [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]⟩
  let above (q : (α × ℕ) × ℕ) := decide (q.1.2 < q.2) && rowNonzero (q.1.1, q.2)
  have habove : above ∈ CountingFunction (a + 16) encCoeff encBool := by
    have hlt := binary_lt' ((snd enc encNat).comp haddr) (snd encAddr encNat)
    have hquery : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => (q.1.1, q.2))
        encCoeff encAddr := hbase.prod (snd encAddr encNat)
    exact CountingFunction.map
      (CountingFunction.prod (CountingFunction.of_polyTime hlt)
        (CountingFunction.preprocess hrow hquery)) bool_and
  let hasAbove (q : α × ℕ) := decide (∃ j < degreeBound q.1 + 1, above (q, j) = true)
  have hhas : hasAbove ∈ CountingFunction (a + 17) encAddr encBool :=
    CountingFunction.exists_range decAddr habove ((binary_add' hbound (.const 1)).comp hw)
  have hdegBound (w : α) : (Q w).natDegree ≤ degreeBound w :=
    parametricCoordinatePolynomial_natDegree_swap_le _ (hdpos w) _ _ _
  have hhasEq (w : α) (t : ℕ) : hasAbove (w, t) = true ↔ t < (Q w).natDegree := by
    simp only [hasAbove, above, decide_eq_true_eq, Bool.and_eq_true, hrowEq]
    constructor
    · rintro ⟨j, _, ht, hj⟩
      exact ht.trans_le (Polynomial.le_natDegree_of_ne_zero hj)
    · intro ht
      have hQ : Q w ≠ 0 := fun h => by simp [h] at ht
      exact ⟨_, Nat.lt_succ_of_le (hdegBound w), ht, by
        rwa [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]⟩
  have hsum := CountingFunction.sum_range E
    (CountingFunction.map hhas (ComputableInPolyTime.of_finite Bool.toNat)) hbound
  convert hsum using 1
  funext w
  have hval (t : ℕ) : (hasAbove (w, t)).toNat = if t < (Q w).natDegree then 1 else 0 := by
    by_cases ht : t < (Q w).natDegree
    · simp [ht, (hhasEq w t).mpr ht]
    · have hf : hasAbove (w, t) = false :=
        Bool.eq_false_iff.mpr (fun h => ht ((hhasEq w t).mp h))
      simp [ht, hf]
  change (Q w).natDegree = ∑ t ∈ Finset.range (degreeBound w), (hasAbove (w, t)).toNat
  simp only [hval]
  rw [← Finset.sum_subset (Finset.range_mono (hdegBound w))]
  · rw [Finset.sum_congr rfl (fun t ht => ite_eq_left (Finset.mem_range.mp ht))]
    simp
  · intro t _ ht
    exact ite_eq_right (fun h => ht (Finset.mem_range.mpr h))

/-- Evaluate the leading deformation coefficient at the queried coordinate value modulo the
queried modulus, using the controlled source evaluator. The query supplies the instance,
modulus, and value, in that order. The degree is taken before reduction modulo the modulus. -/
noncomputable def criticalCoordinateLeadingValue {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) : α × (ℕ × ℕ) → ℕ
  | (w, p, t) =>
    let P := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
    criticalCoordinateCandidateValue p (n w) (d w) (i w).val
      (Polynomial.Bivariate.swap P).natDegree t (fun z => C.evaluate (w, p, z))

/-- A controlled source at level `a` supplies the leading deformation-coefficient evaluator
at level `a + 18`. The modulus, value, coordinate index and exponent parameter are binary. -/
theorem criticalCoordinateLeadingValue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    C.criticalCoordinateLeadingValue i hF ∈
      CountingFunction (a + 18) (encPair enc (encPair encNat encNat)) encNat := by
  let encArgs := encPair encNat encNat
  let encQuery := encPair enc encArgs
  let encIndexed := encPair encQuery encNat
  let decQuery := Decoder.pair E (Decoder.pair Decoder.nat Decoder.nat)
  have hquery := fst encQuery encNat
  have hw := (fst enc encArgs).comp hquery
  have hargs := (snd enc encArgs).comp hquery
  have hp := (fst encNat encNat).comp hargs
  have ht := (snd encNat encNat).comp hargs
  have hvalue := CountingFunction.preprocess C.evaluate_mem
    (input := encPair encIndexed (encList encNat))
    (g := fun (((w, p, _), _), z) => (w, p, z)) (by fun_prop)
  have haddressed := criticalCoordinateCandidateValue_mem (a := a)
    (Decoder.pair decQuery Decoder.nat) hp (C.arity_computable.comp hw) (hd.comp hw) (hi.comp hw)
    (snd encQuery encNat) ht hvalue
  have hdegree := C.criticalCoordinateParameterNatDegree_mem E i hdpos hF hd hi
  exact CountingFunction.comp_with (CountingFunction.mono (by omega) haddressed)
    (CountingFunction.preprocess hdegree (fst enc encArgs))

/-- Above the source and interpolation cutoffs, the leading coordinate evaluator agrees
with the integer leading deformation coefficient evaluated in the prime field. -/
theorem criticalCoordinateLeadingValue_cast {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (hd : 1 ≤ d w)
    {p : ℕ} [Fact p.Prime] (t : ℕ) (hsource : C.cutoff w < p)
    (hcut : (d w + 1) * ((d w + 1) ^ n w + n w * d w + 1) + 1 < p)
    (hdegree : (d w + 1) ^ n w * (d w + 1) ^ n w < p - 1)
    (hparam : coordinateParameterDegreeBound (n w) (d w) < p - 1) :
    (C.criticalCoordinateLeadingValue i hF (w, p, t) : ZMod p) =
      (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
        (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).leadingCoeff.eval₂
        (Int.castRingHom (ZMod p)) (t : ZMod p) := by
  let P := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
  let Q := Polynomial.Bivariate.swap P
  have hj : Q.natDegree < p - 1 :=
    (parametricCoordinatePolynomial_natDegree_swap_le (d w) hd (F w) (hF w) (i w)).trans_lt hparam
  have hv (z : List ℕ) : (C.evaluate (w, p, z) : ZMod p) = eval₂ (Int.castRingHom (ZMod p))
      (fun k : Fin (n w) => ((z[k.val]?.getD 0 : ℕ) : ZMod p)) (F w) := by
    rw [C.evaluate_eq w p z (Fact.out : p.Prime) hsource, evaluation, ZMod.natCast_zmod_val]
  change (criticalCoordinateCandidateValue p (n w) (d w) (i w).val Q.natDegree t
    (fun z => C.evaluate (w, p, z)) : ZMod p) = Q.leadingCoeff.eval₂ _ _
  rw [← Polynomial.coeff_natDegree]
  exact criticalCoordinateCandidateValue_cast (d w) hd (F w) (hF w) (i w) Q.natDegree t
    hcut hdegree hparam hj _ hv

/-- Extract the coefficient at the queried coordinate-value exponent, modulo the queried
modulus, from the leading deformation coefficient selected over the integers. The query
supplies the instance, modulus, and exponent, in that order. -/
noncomputable def criticalCoordinateLeadingCoefficientResidue {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) : α × (ℕ × ℕ) → ℕ
  | (w, p, k) => coefficientResidue p k (fun t => C.criticalCoordinateLeadingValue i hF (w, p, t))

/-- Selecting the integer deformation degree and extracting an addressed coordinate-value
coefficient both fit in level `a + 18`. The queried modulus and exponent are binary. -/
theorem criticalCoordinateLeadingCoefficientResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    C.criticalCoordinateLeadingCoefficientResidue i hF ∈
      CountingFunction (a + 18) (encPair enc (encPair encNat encNat)) encNat := by
  let encArgs := encPair encNat encNat
  let encQuery := encPair enc encArgs
  let decQuery := Decoder.pair E (Decoder.pair Decoder.nat Decoder.nat)
  have hquery := fst encQuery encNat
  have hw := (fst enc encArgs).comp hquery
  have hargs := (snd enc encArgs).comp hquery
  have hp := (fst encNat encNat).comp hargs
  have hk := (snd encNat encNat).comp hargs
  let C' := C.preprocess (fun (((w, _, _), _) : (α × (ℕ × ℕ)) × ℕ) => w) hw
  have haddressed := addressedCoordinateCoefficientResidue_mem C'
    (Decoder.pair decQuery Decoder.nat) hp (hd.comp hw) (hi.comp hw) (snd encQuery encNat) hk
  have hdegree := C.criticalCoordinateParameterNatDegree_mem E i hdpos hF hd hi
  exact CountingFunction.comp_with (CountingFunction.mono (by omega) haddressed)
    (CountingFunction.preprocess hdegree (fst enc encArgs))

/-- At an admissible prime and exponent, the coefficient query gives the reduction of the
corresponding integer coefficient of the selected leading deformation coefficient. -/
theorem criticalCoordinateLeadingCoefficientResidue_cast {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (hd : 1 ≤ d w)
    {p : ℕ} [Fact p.Prime] (k : ℕ) (hsource : C.cutoff w < p)
    (hcut : (d w + 1) * ((d w + 1) ^ n w + n w * d w + 1) + 1 < p)
    (hdegree : (d w + 1) ^ n w * (d w + 1) ^ n w < p - 1)
    (hparam : coordinateParameterDegreeBound (n w) (d w) < p - 1) (hk : k < p - 1) :
    (C.criticalCoordinateLeadingCoefficientResidue i hF (w, p, k) : ZMod p) =
      ((Polynomial.Bivariate.swap (parametricCoordinatePolynomial
        (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).leadingCoeff.coeff k : ZMod p) := by
  let P := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
  let Q := Polynomial.Bivariate.swap P
  let φ := Int.castRingHom (ZMod p)
  have hQ : (Q.leadingCoeff.map φ).natDegree < p - 1 := by
    rw [← Polynomial.coeff_natDegree]
    have h := coordinateCoefficient_natDegree_le (by omega : 1 ≤ d w + 1)
      (F w) (hF w) (i w) Q.natDegree
    have hD : (d w + 1) ^ n w ≤ (d w + 1) ^ n w * (d w + 1) ^ n w :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact Polynomial.natDegree_map_le.trans_lt (h.trans hD |>.trans_lt hdegree)
  have hvalue (t : ℕ) (_ : t < p) :
      (C.criticalCoordinateLeadingValue i hF (w, p, t) : ZMod p) =
        (Q.leadingCoeff.map φ).eval (t : ZMod p) := by
    rw [C.criticalCoordinateLeadingValue_cast i hF w hd t hsource hcut hdegree hparam,
      Polynomial.eval_map]
  change (coefficientResidue p k (fun t => C.criticalCoordinateLeadingValue i hF (w, p, t)) :
    ZMod p) = (Q.leadingCoeff.coeff k : ZMod p)
  rw [coefficientResidue_cast _ _ _ hQ hk hvalue, Polynomial.coeff_map]
  rfl

private noncomputable def addressedCoordinateDerivativeResidue {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (w : α) (p d i j k z : ℕ) : ℕ :=
  univariateDerivativeResidue p ((d + 1) ^ n w) k z (fun e =>
    coefficientResidue p e (fun t =>
      criticalCoordinateCandidateValue p (n w) d i j t (fun u => C.evaluate (w, p, u))))

private theorem addressedCoordinateDerivativeResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {p d i j k z : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat)
    (hk : ComputableInPolyTime k enc encNat) (hz : ComputableInPolyTime z enc encNat) :
    (fun w => addressedCoordinateDerivativeResidue C w (p w) (d w) (i w) (j w) (k w) (z w)) ∈
      CountingFunction (a + 13) enc encNat := by
  have hw := fst enc encNat
  let C' := C.preprocess (fun (q : α × ℕ) => q.1) hw
  have hc := addressedCoordinateCoefficientResidue_mem C' (Decoder.pair E Decoder.nat)
    (hp.comp hw) (hd.comp hw) (hi.comp hw) (hj.comp hw) (snd enc encNat)
  have hD := binary_pow' (binary_add' hd (.const 1)) C.arity_computable
  have hderivative := univariateDerivativeResidue_mem E hp hD hk hz hc
  rw [max_eq_left (show 3 ≤ a + 12 by omega)] at hderivative
  exact hderivative

/-- Evaluate the derivative of binary order `k` at `z` modulo `p`, for the leading
deformation coefficient selected over the integers. -/
noncomputable def criticalCoordinateLeadingDerivativeResidue {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (p k z : ℕ) : ℕ :=
  univariateDerivativeResidue p ((d w + 1) ^ n w) k z
    (fun j => C.criticalCoordinateLeadingCoefficientResidue i hF (w, p, j))

/-- Binary modulus, derivative order and evaluation-point queries give a derivative
evaluator at counting level `a + 18`. -/
theorem criticalCoordinateLeadingDerivativeResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d p k z : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (hp : ComputableInPolyTime p enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hz : ComputableInPolyTime z enc encNat) :
    (fun w => C.criticalCoordinateLeadingDerivativeResidue i hF w (p w) (k w) (z w)) ∈
      CountingFunction (a + 18) enc encNat := by
  have hw := fst enc encNat
  let C' := C.preprocess (fun (q : α × ℕ) => q.1) hw
  have hderivative := addressedCoordinateDerivativeResidue_mem C' (Decoder.pair E Decoder.nat)
    (hp.comp hw) (hd.comp hw) (hi.comp hw) (snd enc encNat) (hk.comp hw) (hz.comp hw)
  have hdegree := C.criticalCoordinateParameterNatDegree_mem E i hdpos hF hd hi
  exact CountingFunction.comp_with (CountingFunction.mono (by omega) hderivative) hdegree

/-- Above the source and interpolation cutoffs, the derivative residue agrees with evaluation
of the integer derivative. This holds for all orders, including beyond the degree. -/
theorem criticalCoordinateLeadingDerivativeResidue_cast {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (hd : 1 ≤ d w)
    {p : ℕ} [Fact p.Prime] (k z : ℕ) (hsource : C.cutoff w < p)
    (hcut : (d w + 1) * ((d w + 1) ^ n w + n w * d w + 1) + 1 < p)
    (hdegree : (d w + 1) ^ n w * (d w + 1) ^ n w < p - 1)
    (hparam : coordinateParameterDegreeBound (n w) (d w) < p - 1) :
    (C.criticalCoordinateLeadingDerivativeResidue i hF w p k z : ZMod p) =
      (Polynomial.derivative^[k] (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
        (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).leadingCoeff).eval₂
          (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  let D := (d w + 1) ^ n w
  let P := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
  let Q := Polynomial.Bivariate.swap P
  let φ := Int.castRingHom (ZMod p)
  have hD : D < p - 1 := (Nat.le_mul_of_pos_right D (by positivity)).trans_lt hdegree
  have hQ : (Q.leadingCoeff.map φ).natDegree ≤ D := by
    rw [← Polynomial.coeff_natDegree]
    exact Polynomial.natDegree_map_le.trans
      (coordinateCoefficient_natDegree_le (by omega) (F w) (hF w) (i w) Q.natDegree)
  have hcoeff (j : ℕ) (hj : j ≤ D) :
      (C.criticalCoordinateLeadingCoefficientResidue i hF (w, p, j) : ZMod p) =
        (Q.leadingCoeff.map φ).coeff j := by
    rw [C.criticalCoordinateLeadingCoefficientResidue_cast i hF w hd j hsource hcut hdegree
      hparam (hj.trans_lt hD), Polynomial.coeff_map]
    rfl
  change (univariateDerivativeResidue p D k z _ : ZMod p) =
    (Polynomial.derivative^[k] Q.leadingCoeff).eval₂ φ (z : ZMod p)
  rw [univariateDerivativeResidue_cast _ hQ (hD.trans_le (Nat.sub_le _ _)) _ hcoeff,
    Polynomial.iterate_derivative_map, Polynomial.eval_map]

/-- Evaluate the prescribed-root fingerprint label for the leading deformation coefficient
of a coordinate characteristic polynomial, using the constant qualifying polynomial `1`.
The evaluation modulus `p` and the fingerprint modulus `μ` are independent. -/
noncomputable def criticalCoordinateFingerprintLabelResidue {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (p μ t z : ℕ) (target : ℤ) : ℕ :=
  fingerprintRootLabelResidue p ((d w + 1) ^ n w)
    (parametricCoordinateCoeffNormExponent (n w) (d w + 1) (C.massExponent w))
    μ t target 1 (fun k => C.criticalCoordinateLeadingDerivativeResidue i hF w p k z)

/-- The coordinate fingerprint evaluator has counting level `a + 20` with binary queries.
Evaluate the fingerprint label at an addressed deformation index first, then substitute the
integer deformation degree. -/
theorem criticalCoordinateFingerprintLabelResidue_mem {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d p μ t z : α → ℕ} {target : α → ℤ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (hp : ComputableInPolyTime p enc encNat) (hμ : ComputableInPolyTime μ enc encNat)
    (ht : ComputableInPolyTime t enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (htarget : ComputableInPolyTime target enc encIntBin) :
    (fun w => C.criticalCoordinateFingerprintLabelResidue i hF w (p w) (μ w) (t w) (z w)
      (target w)) ∈ CountingFunction (a + 20) enc encNat := by
  let encIndexed := encPair enc encNat
  let decIndexed := Decoder.pair E Decoder.nat
  have hw := fst enc encNat
  have hindexed := fst encIndexed encNat
  have hsource := hw.comp hindexed
  let C' := C.preprocess (fun (q : (α × ℕ) × ℕ) => q.1.1) hsource
  have hderivative := addressedCoordinateDerivativeResidue_mem C'
    (Decoder.pair decIndexed Decoder.nat) (hp.comp hsource) (hd.comp hsource) (hi.comp hsource)
    ((snd enc encNat).comp hindexed) (snd encIndexed encNat) (hz.comp hsource)
  have hell := binary_add' hd (.const 1)
  have hD := binary_pow' hell C.arity_computable
  have hb :=
    parametricCoordinateCoeffNormExponent_polyTime C.arity_computable hell C.mass_computable
  have hlabel := fingerprintRootLabelResidue_mem decIndexed (hp.comp hw) (hD.comp hw) (hb.comp hw)
    (hμ.comp hw) (ht.comp hw) (htarget.comp hw) (CountingFunction.of_polyTime (.const 1))
    hderivative
  have hdegree := C.criticalCoordinateParameterNatDegree_mem E i hdpos hF hd hi
  exact CountingFunction.comp_with hlabel (CountingFunction.mono (by omega) hdegree)

/-- Above the source and interpolation cutoffs, the coordinate fingerprint residue agrees with
the integer prescribed-root label evaluated in the prime field. -/
theorem criticalCoordinateFingerprintLabelResidue_cast {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) {d : α → ℕ} (i : (w : α) → Fin (n w))
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (w : α) (hd : 1 ≤ d w)
    {p : ℕ} [Fact p.Prime] (μ t z : ℕ) (hμ : μ ≠ 0) (target : ℤ) (hsource : C.cutoff w < p)
    (hcut : (d w + 1) * ((d w + 1) ^ n w + n w * d w + 1) + 1 < p)
    (hdegree : (d w + 1) ^ n w * (d w + 1) ^ n w < p - 1)
    (hparam : coordinateParameterDegreeBound (n w) (d w) < p - 1) :
    (C.criticalCoordinateFingerprintLabelResidue i hF w p μ t z target : ZMod p) =
      (Polynomial.fingerprintIntegerRootLabel
        (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
          (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).leadingCoeff
        1 ((d w + 1) ^ n w)
        (parametricCoordinateCoeffNormExponent (n w) (d w + 1) (C.massExponent w)) μ t target).eval₂
          (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  rw [criticalCoordinateFingerprintLabelResidue]
  refine fingerprintRootLabelResidue_cast _ 1 _ _ μ t hμ target (z : ZMod p) 1 _ (by simp) ?_
  intro k
  exact C.criticalCoordinateLeadingDerivativeResidue_cast i hF w hd (k.val + 1) z
    hsource hcut hdegree hparam

private theorem univariate_bounds (P : Polynomial ℤ) :
    let Q := (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm P
    Q.totalDegree ≤ P.natDegree ∧ Q.coeffNorm1 = P.coeffNorm1 := by
  intro Q
  have hcoeff (e : Fin 1 →₀ ℕ) : Q.coeff e = P.coeff (e default) :=
    MvPolynomial.coeff_uniqueAlgEquiv_symm ℤ P e
  have hs (e : Fin 1 →₀ ℕ) : e ∈ Q.support ↔ e default ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, Polynomial.mem_support_iff, hcoeff]
  constructor
  · rw [MvPolynomial.totalDegree]
    refine Finset.sup_le_iff.mpr fun e he => ?_
    have hsum : e.sum (fun _ k => k) = e default := by
      conv_lhs => rw [Finsupp.unique_single e]
      exact Finsupp.sum_single_index (by rfl)
    rw [hsum]
    exact Polynomial.le_natDegree_of_mem_supp _ ((hs e).mp he)
  · unfold MvPolynomial.coeffNorm1 Polynomial.coeffNorm1
    refine Finset.sum_bij (fun e _ => e default) (fun e he => (hs e).mp he) ?_ ?_ ?_
    · intro e _ f _ hef
      apply Finsupp.ext
      intro i
      rw [Subsingleton.elim i (default : Fin 1)]
      exact hef
    · intro k hk
      refine ⟨Finsupp.single default k, (hs _).mpr ?_, Finsupp.single_eq_same⟩
      rwa [Finsupp.single_eq_same]
    · intro e _
      rw [hcoeff]

private theorem leadingCoordinateBounds {n d mass : ℕ} (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hmass : F.coeffNorm1 ≤ 2 ^ mass) (i : Fin n) :
    let P := parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i
    let Q := (Polynomial.Bivariate.swap P).leadingCoeff
    Q.natDegree ≤ (d + 1) ^ n ∧
      Q.coeffNorm1 ≤ 2 ^ parametricCoordinateCoeffNormExponent n (d + 1) mass := by
  intro P Q
  rw [show Q = (Polynomial.Bivariate.swap P).coeff (Polynomial.Bivariate.swap P).natDegree
    from Polynomial.coeff_natDegree.symm]
  exact ⟨coordinateCoefficient_natDegree_le (by omega) F hF i _,
    (Polynomial.coeffNorm1_coeff_swap_le P _).trans
      (parametricCoordinatePolynomial_bivariateCoeffNorm1_le (by omega) F hF hmass i)⟩

private def leadingCoordinateCutoff (n d source : ℕ) : ℕ :=
  let D := (d + 1) ^ n
  max source (max ((d + 1) * (D + n * d + 1) + 1)
    (max (D * D) (coordinateParameterDegreeBound n d) + 1))

private theorem leadingCoordinateCutoff_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d source : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hs : ComputableInPolyTime source enc encNat) :
    ComputableInPolyTime (fun w => leadingCoordinateCutoff (n w) (d w) (source w)) enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hD := binary_pow' hell hn
  have hH := binary_max' (binary_mul' hD hD) (coordinateParameterDegreeBound_polyTime hn hd)
  have hK := binary_add' (binary_mul' hell (binary_add'
    (binary_add' hD (binary_mul' (unary_to_binary.comp hn) hd)) (.const 1))) (.const 1)
  exact binary_max' hs (binary_max' hK (binary_add' hH (.const 1)))

private theorem leadingCoordinateCutoff_spec {n d source p : ℕ}
    (h : leadingCoordinateCutoff n d source < p) :
    source < p ∧ (d + 1) * ((d + 1) ^ n + n * d + 1) + 1 < p ∧
      (d + 1) ^ n * (d + 1) ^ n < p - 1 ∧ coordinateParameterDegreeBound n d < p - 1 := by
  simp only [leadingCoordinateCutoff, max_lt_iff] at h
  have hbound : max ((d + 1) ^ n * (d + 1) ^ n) (coordinateParameterDegreeBound n d) <
      p - 1 := by omega
  exact ⟨h.1, h.2.1, max_lt_iff.mp hbound⟩

private theorem evaluation_univariate (P : Polynomial ℤ) (p : ℕ) (z : List ℕ) :
    evaluation ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm P) p z =
      (P.eval₂ (Int.castRingHom (ZMod p)) (z.getD 0 0 : ZMod p)).val := by
  rw [evaluation, MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  have hzero : (default : Fin 1).val = 0 := rfl
  rw [hzero, ← List.getD_eq_getElem?_getD]

/-- Package the leading deformation coefficient of the selected coordinate characteristic
polynomial as a controlled univariate family. Evaluation at level `a + 18` computes the
deformation degree over the integers and then reads that coefficient modulo the query prime. -/
noncomputable def criticalCoordinateEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    let Q (w : α) := (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
      (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w))).leadingCoeff
    Controlled (fun w => (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm (Q w)) enc (a + 18) := by
  intro Q
  have hell := binary_add' hd (.const 1)
  have hb (w : α) := leadingCoordinateBounds (hdpos w) (F w) (hF w) (C.mass_le w) (i w)
  refine {
    arity_computable := .const 1
    degreeBound := fun w => (d w + 1) ^ n w
    degree_computable := binary_pow' hell C.arity_computable
    degree_le := fun w => (univariate_bounds (Q w)).1.trans (hb w).1
    massExponent := fun w =>
      parametricCoordinateCoeffNormExponent (n w) (d w + 1) (C.massExponent w)
    mass_computable :=
      parametricCoordinateCoeffNormExponent_polyTime C.arity_computable hell C.mass_computable
    mass_le := fun w => (univariate_bounds (Q w)).2.trans_le (hb w).2
    cutoff := fun w => leadingCoordinateCutoff (n w) (d w) (C.cutoff w)
    cutoff_computable := leadingCoordinateCutoff_polyTime C.arity_computable hd C.cutoff_computable
    evaluate := fun (w, p, z) => C.criticalCoordinateLeadingValue i hF (w, p, z.getD 0 0) % p
    evaluate_mem := ?_
    evaluate_eq := ?_
  }
  · let args := encPair encNat (encList encNat)
    have hw := fst enc args
    have hargs := snd enc args
    have hp := (fst encNat (encList encNat)).comp hargs
    have hz := (listGetD (encA := encNat) 0).comp
      (((snd encNat (encList encNat)).comp hargs).prod (.const 0))
    have hres := CountingFunction.preprocess (C.criticalCoordinateLeadingValue_mem E i hdpos hF
      hd hi) (hw.prod (hp.prod hz))
    exact CountingFunction.map (CountingFunction.prod hres (CountingFunction.of_polyTime hp))
      binary_mod
  · intro w p z hp hc
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨hsource, hK, hdegree, hparam⟩ := leadingCoordinateCutoff_spec hc
    have hr := C.criticalCoordinateLeadingValue_cast i hF w (hdpos w) (z.getD 0 0)
      hsource hK hdegree hparam
    rw [evaluation_univariate]
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hr

/-- The coordinate-equation bounds depend only on the arity, deformation degree,
source norm exponent and source prime cutoff. -/
theorem criticalCoordinateEquations_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (u v : α) (hn : n u = n v) (hduv : d u = d v)
    (hm : C.massExponent u = C.massExponent v) (hc : C.cutoff u = C.cutoff v) :
    let equations := C.criticalCoordinateEquations E i hdpos hF hd hi
    equations.degreeBound u = equations.degreeBound v ∧
      equations.massExponent u = equations.massExponent v ∧
      equations.cutoff u = equations.cutoff v := by
  simp [criticalCoordinateEquations, hn, hduv, hm, hc]

/-- Package the coordinate fingerprint polynomials for supplied binary parameters as a controlled
univariate family. The degree and norm bounds use a supplied upper bound on the modulus.
The polynomials and evaluator use the actual modulus. This adapts the controlled-family step of
lean-canny's `ControlledIndexedLabels` at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. -/
noncomputable def criticalCoordinateFingerprintLabels {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d μ μBound t : α → ℕ} {target : α → ℤ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (hμ : ComputableInPolyTime μ enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (htarget : ComputableInPolyTime target enc encIntBin)
    (hμpos : ∀ w, 0 < μ w) (hμBound : ComputableInPolyTime μBound enc encNat)
    (hμle : ∀ w, μ w ≤ μBound w)
    (htargetBound : ∀ w, (target w).natAbs ≤ (d w + 1) ^ n w * μ w) :
    let P (w : α) := parametricCoordinatePolynomial (by omega : 1 ≤ d w + 1) (F w) (hF w) (i w)
    let D (w : α) := (d w + 1) ^ n w
    let b (w : α) := parametricCoordinateCoeffNormExponent (n w) (d w + 1) (C.massExponent w)
    Controlled (fun w => (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
      (Polynomial.fingerprintIntegerRootLabel (Polynomial.Bivariate.swap (P w)).leadingCoeff
        1 (D w) (b w) (μ w) (t w) (target w))) enc (a + 20) := by
  intro P D b
  let L (w : α) := Polynomial.fingerprintIntegerRootLabel
    (Polynomial.Bivariate.swap (P w)).leadingCoeff 1 (D w) (b w) (μ w) (t w) (target w)
  let B (w : α) := Polynomial.derivativeRootLabelPrecision (D w) (b w)
  let M (w : α) := D w * μBound w
  let β (w : α) := Polynomial.iterateDerivativeNormExponent (D w) (b w)
  have hell := binary_add' hd (.const 1)
  have hD : ComputableInPolyTime D enc encNat := binary_pow' hell C.arity_computable
  have hb : ComputableInPolyTime b enc encNat :=
    parametricCoordinateCoeffNormExponent_polyTime C.arity_computable hell C.mass_computable
  have hB : ComputableInPolyTime B enc encNat := derivativeRootLabelPrecision_polyTime hD hb
  have hM : ComputableInPolyTime M enc encNat := binary_mul' hD hμBound
  have hβ : ComputableInPolyTime β enc encNat := iterateDerivativeNormExponent_polyTime hD hb
  have hscale := binary_mul' (.const 2) (binary_add' hM (.const 1))
  have hprecision := binary_add' (binary_mul' (.const 2) hB) (.const 1)
  have hslots := binary_add' hD (.const 1)
  have hL (w : α) : (L w).natDegree ≤ Polynomial.fingerprintLabelDegreeBound (D w) (B w) (M w)
      (D w) ∧ (L w).coeffNorm1 ≤ 2 ^ Polynomial.fingerprintLabelNormExponent (D w) (B w)
        (M w) (β w) := by
    obtain ⟨hn, hm⟩ := leadingCoordinateBounds (hdpos w) (F w) (hF w) (C.mass_le w) (i w)
    obtain ⟨hdegree, hnorm⟩ :=
      Polynomial.fingerprintIntegerRootLabel_bounds (q := 1) (t w) (hμpos w) hn
        (by simp) hm (by rw [Polynomial.coeffNorm1_one]; exact Nat.one_le_two_pow) (htargetBound w)
    have hweight : D w * μ w ≤ M w := Nat.mul_le_mul_left _ (hμle w)
    refine ⟨hdegree.trans ?_, hnorm.trans (Nat.pow_le_pow_right (by decide) ?_)⟩
    · unfold Polynomial.fingerprintLabelDegreeBound
      gcongr
    · unfold Polynomial.fingerprintLabelNormExponent
      have hsize := Nat.size_le_size hweight
      gcongr
  refine {
    arity_computable := .const 1
    degreeBound := fun w => Polynomial.fingerprintLabelDegreeBound (D w) (B w) (M w) (D w)
    degree_computable := binary_mul' (.const 2)
      (binary_mul' hslots (binary_mul' (binary_mul' hscale hprecision) hD))
    degree_le := fun w => (univariate_bounds (L w)).1.trans (hL w).1
    massExponent := fun w => Polynomial.fingerprintLabelNormExponent (D w) (B w) (M w) (β w)
    mass_computable := ?_
    mass_le := fun w => (univariate_bounds (L w)).2.trans_le (hL w).2
    cutoff := fun w => leadingCoordinateCutoff (n w) (d w) (C.cutoff w)
    cutoff_computable := leadingCoordinateCutoff_polyTime C.arity_computable hd C.cutoff_computable
    evaluate := fun (w, p, z) =>
      C.criticalCoordinateFingerprintLabelResidue i hF w p (μ w) (t w) (z.getD 0 0) (target w) % p
    evaluate_mem := ?_
    evaluate_eq := ?_
  }
  · have hsize := unary_to_binary.comp (binary_size.comp hM)
    have hterm := binary_mul' (binary_mul' hscale hprecision) (binary_add' hprecision hβ)
    exact binary_add'
      (binary_mul' (.const 2) (binary_add'
        (binary_add' hsize (binary_mul' hslots (binary_add' hterm (.const 1)))) (.const 1)))
      (.const 4)
  · let args := encPair encNat (encList encNat)
    have hw := fst enc args
    have hargs := snd enc args
    have hp := (fst encNat (encList encNat)).comp hargs
    have hz := (listGetD (encA := encNat) 0).comp
      (((snd encNat (encList encNat)).comp hargs).prod (.const 0))
    let CQ := C.preprocess (fun q : α × (ℕ × List ℕ) => q.1) hw
    have hres := CQ.criticalCoordinateFingerprintLabelResidue_mem
      (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
      (fun q => i q.1) (fun q => hdpos q.1) (fun q => hF q.1)
      (hd.comp hw) (hi.comp hw) hp (hμ.comp hw) (ht.comp hw) hz (htarget.comp hw)
    exact CountingFunction.map (CountingFunction.prod hres (CountingFunction.of_polyTime hp))
      binary_mod
  · intro w p z hp hc
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨hsource, hK, hdegree, hparam⟩ := leadingCoordinateCutoff_spec hc
    have hr := C.criticalCoordinateFingerprintLabelResidue_cast i hF w (hdpos w)
      (μ w) (t w) (z.getD 0 0) (Nat.ne_of_gt (hμpos w)) (target w) hsource hK hdegree hparam
    rw [evaluation_univariate]
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hr

/-- The fingerprint bounds depend only on the source arity, deformation degree, source
norm exponent and cutoff, and the common modulus bound. -/
theorem criticalCoordinateFingerprintLabels_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d μ μBound t : α → ℕ} {target : α → ℤ}
    (i : (w : α) → Fin (n w)) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (hμ : ComputableInPolyTime μ enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (htarget : ComputableInPolyTime target enc encIntBin)
    (hμpos : ∀ w, 0 < μ w) (hμBound : ComputableInPolyTime μBound enc encNat)
    (hμle : ∀ w, μ w ≤ μBound w)
    (htargetBound : ∀ w, (target w).natAbs ≤ (d w + 1) ^ n w * μ w)
    (u v : α) (hn : n u = n v) (hduv : d u = d v)
    (hm : C.massExponent u = C.massExponent v) (hc : C.cutoff u = C.cutoff v)
    (hcap : μBound u = μBound v) :
    let labels := C.criticalCoordinateFingerprintLabels E i hdpos hF hd hi hμ ht htarget
      hμpos hμBound hμle htargetBound
    labels.degreeBound u = labels.degreeBound v ∧
      labels.massExponent u = labels.massExponent v ∧
      labels.cutoff u = labels.cutoff v := by
  simp [criticalCoordinateFingerprintLabels, hn, hduv, hm, hc, hcap]

end Cslib.Complexity.RealAlgebraic.Controlled
