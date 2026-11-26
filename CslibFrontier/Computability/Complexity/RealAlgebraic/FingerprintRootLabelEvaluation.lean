/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.SignLabelEvaluation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.FingerprintIntegerRootLabel
import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelPrecision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod

/-!
# Modular evaluation of a prescribed-root fingerprint label

Binary-addressed derivative residues and a qualifying residue give the integer label's
value at an evaluation prime. The weights are computed by modular powers in the
fingerprint modulus, which is independent of the evaluation prime.

Adapted from `FingerprintRootLabelEvaluation` and `PrescribedRootLabelEvaluation`
in lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM

/-- Evaluate the fingerprint label modulo `p` using weights modulo `μ`. Slot zero
uses the qualifying value. Slot `i > 0` uses the residue of derivative order `i`.
The signed target is reduced modulo the evaluation modulus. -/
noncomputable def fingerprintRootLabelResidue (p D b μ t : ℕ) (target : ℤ)
    (qualifier : ℕ) (derivativeValue : ℕ → ℕ) : ℕ :=
  fingerprintLabelResidue p (Polynomial.derivativeRootLabelPrecision D b) (D * μ) D
    (fun i => if i = 0 then qualifier else derivativeValue i)
    (fun i => powMod μ t i) (target % (p : ℤ)).toNat

/-- A level-`a` source for the qualifying and addressed derivative residues gives
an evaluator at level `a + 7`. All scalar parameters have binary encodings. -/
theorem fingerprintRootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D b μ t qualifier : α → ℕ} {target : α → ℤ}
    {derivativeValue : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hμ : ComputableInPolyTime μ enc encNat)
    (ht : ComputableInPolyTime t enc encNat) (htarget : ComputableInPolyTime target enc encIntBin)
    (hqualifier : qualifier ∈ CountingFunction a enc encNat)
    (hderivative : derivativeValue ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => fingerprintRootLabelResidue (p w) (D w) (b w) (μ w) (t w) (target w)
      (qualifier w) (fun i => derivativeValue (w, i))) ∈ CountingFunction (a + 7) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hzero : ComputableInPolyTime (fun w : α × ℕ => decide (w.2 = 0))
      (encPair enc encNat) encBool := by fun_prop
  have hvalue := CountingFunction.ite (CountingFunction.of_polyTime hzero)
    (CountingFunction.preprocess hqualifier hf) hderivative
  simp only [decide_eq_true_eq] at hvalue
  have hweight := computableInPolyTime_powMod (hμ.comp hf) (ht.comp hf) hi
  exact fingerprintLabelResidue_mem E hp (derivativeRootLabelPrecision_polyTime hD hb)
    (ComputableInPolyTime.binary_mul' hD hμ) hD hvalue (CountingFunction.of_polyTime hweight)
    (CountingFunction.of_polyTime (ComputableInPolyTime.intBin_emodNat' htarget hp))

/-- At a prime the modular evaluator agrees with the actual integer root label when
the qualifying test and addressed derivatives are supplied at the evaluation point.
Only positive derivative orders up through `D` are queried. -/
theorem fingerprintRootLabelResidue_cast {p : ℕ} [Fact p.Prime] (f q : Polynomial ℤ)
    (D b μ t : ℕ) (hμ : μ ≠ 0) (target : ℤ) (z : ZMod p)
    (qualifier : ℕ) (derivativeValue : ℕ → ℕ)
    (hq : (qualifier : ZMod p) = q.eval₂ (Int.castRingHom (ZMod p)) z)
    (hderivative : ∀ i : Fin D, (derivativeValue (i.val + 1) : ZMod p) =
      (Polynomial.derivative^[i.val + 1] f).eval₂ (Int.castRingHom (ZMod p)) z) :
    (fingerprintRootLabelResidue p D b μ t target qualifier derivativeValue : ZMod p) =
      (Polynomial.fingerprintIntegerRootLabel f q D b μ t target).eval₂
        (Int.castRingHom (ZMod p)) z := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have htarget : ((target % (p : ℤ)).toNat : ZMod p) = (target : ZMod p) := by
    have he : (target % (p : ℤ)).toNat = (target : ZMod p).val := by
      simpa only [Int.toNat_natCast] using
        (congrArg Int.toNat (ZMod.val_intCast (n := p) target)).symm
    rw [he, ZMod.natCast_zmod_val]
  rw [fingerprintRootLabelResidue, Polynomial.fingerprintIntegerRootLabel]
  refine fingerprintLabelResidue_cast _ _ _ _ _ _ _ _ _ ?_ ?_ htarget
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero, ite_true, Polynomial.fingerprintRootLabelTests, Fin.cases_zero]
        using hq
    · simpa only [Fin.val_succ, Nat.succ_ne_zero, ite_false, Polynomial.fingerprintRootLabelTests,
        Fin.cases_succ] using hderivative j
  · intro i
    rw [powMod_of_ne_zero hμ]

end Cslib.Complexity.RealAlgebraic
