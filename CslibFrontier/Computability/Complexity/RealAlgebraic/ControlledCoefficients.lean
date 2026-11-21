/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Complexity.RealAlgebraic.MultivariateCoefficients
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured

/-!
# Indexed coefficients of controlled integer families

A polynomial-time list of binary exponents specifies one coefficient. The
uniform grid algorithm supplies its residues at one higher function level.
The original logarithmic mass bound also bounds that integer coefficient,
so Frontier's residue-sign theorem applies without expanding the polynomial.
The prime cutoff depends only on the controlled family and primary instance, uniformly
in every coefficient address. Entries beyond the arity are ignored and missing entries
are zero; addresses of total degree above the source degree bound return zero directly.

Adapted from [lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/ControlledCoefficients.lean).

## Main definitions

* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientAccess`: uniform residue access to
  coefficients addressed by binary exponents.

## Main results

* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientAccess_mem`: coefficient residues in
  the next function level.
* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientSign_mem`: signs from those residues.

## References

* [OpenAI, *Existential--universal real sentences in the counting hierarchy*]
  [OpenAI2026CountingHierarchy], Definition 2.3 (p. 6) and Lemma 2.4 (p. 7).
  This module supplies the scalar, all-variable coefficient-extraction ingredient;
  partial extraction retaining a polynomial in parameters is tracked by
  [#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM MvPolynomial
open scoped BigOperators

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}

/-- An address-independent cutoff covering evaluator correctness and Fourier non-aliasing. -/
@[expose] def coefficientCutoff (C : Controlled P enc a) (w : α) : ℕ :=
  max (C.cutoff w) (C.degreeBound w + 1)

theorem coefficientCutoff_polyTime (C : Controlled P enc a) :
    ComputableInPolyTime C.coefficientCutoff enc encNat :=
  ComputableInPolyTime.binary_max' C.cutoff_computable
    (ComputableInPolyTime.binary_add' C.degree_computable (.const 1))

/-- The coefficient is a mathematical integer; its actual realizing function
uses only the controlled evaluator and short grid addresses. -/
@[expose] noncomputable def coefficientAccess (C : Controlled P enc a)
    (e : (w : α) → Fin (n w) →₀ ℕ) (β : α → List ℕ)
    (hβ : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    IntegerResidueAccess (fun w => (P w).coeff (e w)) where
  magnitudeExponent := C.massExponent
  admissible := fun w p => p.Prime ∧ C.coefficientCutoff w < p
  modulus_pos := fun _ _ hp => hp.1.pos
  residue := fun (w, modulus) =>
    if C.degreeBound w < ((β w).take (n w)).sum then 0 else
      multivariateCoefficientResidue modulus (n w) (β w)
        (fun coordinates => C.evaluate (w, modulus, coordinates))
  magnitude_le w := (MvPolynomial.natAbs_coeff_le_coeffNorm1 _ _).trans (C.mass_le w)
  residue_eq w p hp := by
    dsimp only
    let : Fact p.Prime := ⟨hp.1⟩
    have hcut := hp.2
    change max (C.cutoff w) (C.degreeBound w + 1) < p at hcut
    have hold : C.cutoff w < p := by omega
    have sum_take (m : ℕ) (l : List ℕ) :
        (l.take m).sum = ∑ i : Fin m, l[i.val]?.getD 0 := by
      induction m generalizing l with
      | zero => simp
      | succ m ih =>
        cases l with
        | nil => simp
        | cons x l =>
          simpa [Fin.sum_univ_succ] using congrArg (x + ·) (ih l)
    have hindex : (e w).sum (fun _ k => k) = ((β w).take (n w)).sum := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), sum_take]
      exact Finset.sum_congr rfl fun i _ => (hβ w i).symm
    by_cases hhigh : C.degreeBound w < ((β w).take (n w)).sum
    · have hz : (P w).coeff (e w) = 0 := by
        apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        change (P w).totalDegree < (e w).sum (fun _ k => k)
        rw [hindex]
        exact (C.degree_le w).trans_lt hhigh
      simp only [hhigh, ↓reduceIte, hz, Int.zero_emod, Int.toNat_zero]
    rw [ite_eq_right hhigh]
    let Q := (P w).map (Int.castRingHom (ZMod p))
    have hmap : Q.totalDegree ≤ (P w).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    have hQ : Q.totalDegree < p - 1 := by
      have := C.degree_le w
      omega
    have he (i : Fin (n w)) : e w i < p - 1 := by
      have hi : e w i ≤ (e w).sum (fun _ k => k) :=
        Finsupp.single_eval_le_sum (e w) (g := id) rfl (fun _ => Nat.zero_le _) i
      rw [hindex] at hi
      omega
    have hvalue (r : ℕ) (_hr : r < p ^ n w) :
        (C.evaluate (w, p, gridPoint p (n w) r) : ZMod p) =
          MvPolynomial.eval
            (fun i : Fin (n w) => (((gridPoint p (n w) r)[i.val]?.getD 0 : ℕ) : ZMod p)) Q := by
      rw [C.evaluate_eq w p _ hp.1 hold]
      simp only [evaluation, ZMod.natCast_zmod_val, Q, MvPolynomial.eval_map]
    have hres := multivariateCoefficientResidue_eq_val Q (e w) (β w)
      (fun z => C.evaluate (w, p, z)) hQ he (hβ w) hvalue
    rw [hres]
    simp only [Q, MvPolynomial.coeff_map, Int.coe_castRingHom]
    simpa only [Int.toNat_natCast] using
      congrArg Int.toNat (ZMod.val_intCast (n := p) ((P w).coeff (e w)))

/-- All indexed coefficient residues use a single oracle at one higher level. -/
theorem coefficientAccess_mem (C : Controlled P enc a) (E : Decoder enc)
    (e : (w : α) → Fin (n w) →₀ ℕ) {β : α → List ℕ}
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (he : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    (C.coefficientAccess e β he).InCountingFunction (a + 1) enc := by
  have hvalue := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) C.evaluate_mem
    (g := fun ((w, modulus), coordinates) => (w, modulus, coordinates)) (by fun_prop)
  have htotal := ComputableInPolyTime.binary_sum.comp
    (ComputableInPolyTime.listTakeWithInput hβ C.arity_computable)
  have hguard := (ComputableInPolyTime.binary_lt.comp
    (C.degree_computable.prod htotal)).comp (ComputableInPolyTime.fst enc encNat)
  have hgrid := multivariateCoefficientResidue_mem (Decoder.pair E Decoder.nat)
    (ComputableInPolyTime.snd enc encNat)
    (C.arity_computable.comp (ComputableInPolyTime.fst enc encNat))
    (hβ.comp (ComputableInPolyTime.fst enc encNat)) hvalue
  refine ⟨C.mass_computable, ?_⟩
  simpa only [coefficientAccess, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime hguard)
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0)) hgrid

/-- Signs of arbitrary addressed coefficients have a fixed CH bound. -/
theorem coefficientSign_mem (C : Controlled P enc a) (E : Decoder enc)
    (e : (w : α) → Fin (n w) →₀ ℕ) {β : α → List ℕ}
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (he : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    (fun w => ((P w).coeff (e w)).sign) ∈
      CountingFunction (max (a + 1) 5 + 3) enc encIntBin := by
  apply IntegerResidueAccess.sign_mem_CountingFunction E (C.coefficientAccess e β he)
    (C.coefficientAccess_mem E e hβ he) C.coefficientCutoff_polyTime
  intro w p hp
  exact ⟨Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩,
    (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.1⟩

end Cslib.Complexity.RealAlgebraic.Controlled
