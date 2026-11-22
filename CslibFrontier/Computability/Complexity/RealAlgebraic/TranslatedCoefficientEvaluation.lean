/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.TranslatedPoint
public import CslibFrontier.Foundations.Data.MvPolynomial.ShiftDerivatives
public import CslibFrontier.Computability.Complexity.RealAlgebraic.MultivariateCoefficients

/-!
# Translated coefficients in one additional counting level

`translatedCoefficientResidue` uses the existing grid sum after polynomial-time modular
point translation. A uniform `F_a` evaluation oracle therefore yields an `F_(a+1)` coefficient
evaluator; the variable arity is unary and the modulus, exponents and coordinates are binary.
Correctness requires a prime field, total degree below `p - 1`, and each requested exponent
below `p - 1`. The same total function is certified on every input.

Adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/TranslatedCoefficientEvaluation.lean).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

/-- One grid coefficient sum after modular translation of each evaluation point. -/
@[expose] noncomputable def translatedCoefficientResidue (p n : ℕ) (β z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  multivariateCoefficientResidue p n β (fun y => value (translatedPoint p n z y))

theorem translatedCoefficientResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {β z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => translatedCoefficientResidue (p w) (n w) (β w) (z w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 1) enc encNat := by
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hshift := translatedPoint_polyTime (hp.comp hf) (hn.comp hf) (hz.comp hf)
    (ComputableInPolyTime.snd enc (encList encNat))
  have hvalue := CountingFunction.preprocess hv (hf.prod hshift)
  simpa only [translatedCoefficientResidue, Function.comp_apply] using
    multivariateCoefficientResidue_mem E hp hn hβ hvalue

theorem translatedCoefficientResidue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (e : Fin n →₀ ℕ) (β z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1)
    (he : ∀ i, e i < p - 1) (hβ : ∀ i : Fin n, β[i.val]?.getD 0 = e i)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (translatedCoefficientResidue p n β z value : ZMod p) =
      (shift (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p)) F).coeff e := by
  apply multivariateCoefficientResidue_cast _ e β _
    ((totalDegree_shift_le _ F).trans_lt hF) he hβ
  intro s _hs
  rw [hv, eval_shift]
  apply congrArg (fun y : Fin n → ZMod p => eval y F)
  funext i
  rw [translatedPoint_get _ _ i.isLt, ZMod.natCast_mod, Nat.cast_add, add_comm]

end Cslib.Complexity.RealAlgebraic
