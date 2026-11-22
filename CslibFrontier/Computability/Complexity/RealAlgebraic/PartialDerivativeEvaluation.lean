/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.TranslatedCoefficientEvaluation

/-!
# First and second partial derivatives in one additional counting level

The first- and second-partial evaluators extract short addressed coefficients of a translated
polynomial. Both use one coefficient sum, so a uniform `F_a` evaluator gives `F_(a+1)` access.
The second-partial evaluator includes factor two when its two coordinates coincide.

Correctness requires total degree below `p - 1`, with primes `p > 2` for first partials
and `p > 3` for second partials.
Variable arity is supplied in unary, with binary derivative indices, modulus and point
coordinates; missing coordinates are zero. The auxiliary coefficient-address lists are local
implementation details, with their polynomial-time construction charged in each certificate.

Adapted from the
[address construction](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PartialDerivativeAddresses.lean)
and
[derivative evaluators](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PartialDerivativeEvaluation.lean)
in lean-canny.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

private def firstPartialAddress (n i : ℕ) : List ℕ :=
  (List.range n).map (fun k => if k = i then 1 else 0)

private def secondPartialAddress (n i j : ℕ) : List ℕ :=
  (List.range n).map (fun k => (if k = j then 1 else 0) + (if k = i then 1 else 0))

private theorem firstPartialAddress_get {n k : ℕ} (i : ℕ) (hk : k < n) :
    (firstPartialAddress n i)[k]?.getD 0 = if k = i then 1 else 0 := by
  simp [firstPartialAddress, hk]

private theorem secondPartialAddress_get {n k : ℕ} (i j : ℕ) (hk : k < n) :
    (secondPartialAddress n i j)[k]?.getD 0 =
      (if k = j then 1 else 0) + (if k = i then 1 else 0) := by
  simp [secondPartialAddress, hk]

private theorem firstPartialAddress_polyTime {α : Type} {enc : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun w => firstPartialAddress (n w) (i w)) enc (encList encNat) := by
  have hk := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hi' := hi.comp (ComputableInPolyTime.fst enc encUnary)
  have htest : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = i q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hi'
  have hval : ComputableInPolyTime (fun q : α × ℕ => if q.2 = i q.1 then 1 else 0)
      (encPair enc encUnary) encNat := by
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (.const (1 : ℕ)) (.const 0)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hval

private theorem secondPartialAddress_polyTime {α : Type} {enc : α ↪ List Bool} {n i j : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun w => secondPartialAddress (n w) (i w) (j w))
      enc (encList encNat) := by
  have hk := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have hi' := hi.comp (ComputableInPolyTime.fst enc encUnary)
  have hj' := hj.comp (ComputableInPolyTime.fst enc encUnary)
  have htesti : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = i q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hi'
  have htestj : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 = j q.1)) (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hk hj'
  have hval := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.ite' htestj (.const (1 : ℕ)) (.const 0))
    (ComputableInPolyTime.ite' htesti (.const (1 : ℕ)) (.const 0))
  simp only [decide_eq_true_eq] at hval
  have hres := ComputableInPolyTime.mapWithInput
    (f := fun w k => (if k = j w then 1 else 0) + (if k = i w then 1 else 0))
    (ComputableInPolyTime.range.comp hn) hval
  simpa only [secondPartialAddress, decide_eq_true_eq, Function.comp_apply] using hres

/-- Evaluate one formal partial derivative by a translated coefficient sum. -/
@[expose] noncomputable def firstPartialResidue (p n i : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  translatedCoefficientResidue p n
    ((List.range n).map (fun k => if k = i then 1 else 0)) z value

/-- A mixed or repeated second partial, multiplying by two when its indices coincide. -/
@[expose] noncomputable def secondPartialResidue (p n i j : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  (translatedCoefficientResidue p n
    ((List.range n).map (fun k => (if k = j then 1 else 0) + (if k = i then 1 else 0))) z value *
    (if i = j then 2 else 1)) % p

theorem firstPartialResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n i : α → ℕ} {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => firstPartialResidue (p w) (n w) (i w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat :=
  translatedCoefficientResidue_mem E hp hn (firstPartialAddress_polyTime hn hi) hz hv

theorem secondPartialResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n i j : α → ℕ} {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => secondPartialResidue (p w) (n w) (i w) (j w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat := by
  classical
  have hcoeff := translatedCoefficientResidue_mem E hp hn
    (secondPartialAddress_polyTime hn hi hj) hz hv
  have htest : ComputableInPolyTime (fun w => decide (i w = j w)) enc encBool := by fun_prop
  have hfactor : ComputableInPolyTime (fun w => if i w = j w then 2 else 1) enc encNat := by
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (.const (2 : ℕ)) (.const 1)
  simpa only [secondPartialResidue, secondPartialAddress, decide_eq_true_eq] using
    CountingFunction.nat_mod
      (CountingFunction.nat_mul hcoeff (CountingFunction.of_polyTime hfactor))
      (CountingFunction.of_polyTime hp)

theorem firstPartialResidue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (i : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 2 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (firstPartialResidue p n i.val z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) (pderiv i F) := by
  classical
  change (translatedCoefficientResidue p n (firstPartialAddress n i.val) z value : ZMod p) = _
  rw [translatedCoefficientResidue_cast F (Finsupp.single i 1)
    (firstPartialAddress n i.val) z value hF (by
      intro j
      simp only [Finsupp.single_apply]
      split_ifs <;> omega) (by
      intro j
      rw [firstPartialAddress_get _ j.isLt]
      simp only [Finsupp.single_apply, Fin.val_inj, eq_comm]) hv]
  exact (first_derivative_translation_coeff _ F i).symm

theorem secondPartialResidue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (i j : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun k : Fin n => ((y[k.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (secondPartialResidue p n i.val j.val z value : ZMod p) =
      eval (fun k : Fin n => ((z[k.val]?.getD 0 : ℕ) : ZMod p)) (pderiv j (pderiv i F)) := by
  classical
  change (((translatedCoefficientResidue p n (secondPartialAddress n i.val j.val) z value *
    (if i.val = j.val then 2 else 1)) % p : ℕ) : ZMod p) = _
  rw [ZMod.natCast_mod, Nat.cast_mul,
    translatedCoefficientResidue_cast F (Finsupp.single j 1 + Finsupp.single i 1)
      (secondPartialAddress n i.val j.val) z value hF (by
        intro k
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs <;> omega) (by
        intro k
        rw [secondPartialAddress_get _ _ k.isLt]
        simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.val_inj, eq_comm]) hv,
    second_derivative_translation_coeff]
  congr 1
  by_cases hij : i = j
  · subst j
    simp
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

end Cslib.Complexity.RealAlgebraic
