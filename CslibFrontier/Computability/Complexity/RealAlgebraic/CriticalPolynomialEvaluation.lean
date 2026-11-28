/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalNumericEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.PartialDerivativeEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native evaluators for the critical objective and lower relations

Construct modular evaluations of the actual deformed potential and its pure-power critical
relations from uniform evaluation access to the input polynomial. The objective preserves
its counting level; first derivatives cost one additional level. No critical-relation evaluator
is assumed of the construction. Correctness has the stated finite-field degree and prime bounds.

Ported from `LeanCanny.CountingHierarchy.CriticalPolynomialEvaluation` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. This constructs the generic critical-system component;
controlled-family bounds and full feasibility endpoints remain
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).

For relative characteristic coefficients, `zeroObjectiveValue` evaluates the zero-centered
objective. `zeroObjectiveValue_mem` preserves the source evaluator's counting level with the
`encInstancePoint` input encoding, and `zeroObjectiveValue_cast` proves agreement with the actual
polynomial over a prime field. These come from `LeanCanny.CountingHierarchy.ZeroCenterEvaluation`
and `ZeroCenterCorrectness` at the same commit.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial MvPolynomial.CriticalSystem

/-- Evaluate a constructed pure-power lower relation by modular arithmetic. -/
@[expose] noncomputable def criticalLowerValue (p n ell u i : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  modularSub p (powMod p (criticalCenterResidue p ell i) ell)
    (u * firstPartialResidue p n i z value)

/-- Evaluate the deformed objective using the input polynomial evaluator. -/
@[expose] noncomputable def criticalObjectiveValue (p n ell u : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  (criticalPotentialResidue p n ell z + (ell + 1) * u * value z) % p

private def zeroPotentialResidue (p n ell : ℕ) (z : List ℕ) : ℕ :=
  unaryModularSum n p (fun i => powMod p (z[i]?.getD 0) (ell + 1))

/-- Evaluate the zero-centered deformed objective using the input polynomial evaluator. -/
def zeroObjectiveValue (p n ell u : ℕ) (z : List ℕ) (value : List ℕ → ℕ) : ℕ :=
  (zeroPotentialResidue p n ell z + (ell + 1) * u * value z) % p

/-- A framed instance followed by the native list encoding of its binary coordinates. -/
abbrev encInstancePoint {α : Type} (enc : α ↪ List Bool) : (α × List ℕ) ↪ List Bool :=
  encPair enc (encList encNat)

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

theorem criticalLowerValue_mem (E : Decoder enc) {p n ell u i : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => criticalLowerValue (p w) (n w) (ell w) (u w) (i w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hcenter := criticalCenterResidue_polyTime hp hell hi
  have hc := computableInPolyTime_powMod hp hcenter hell
  have hd := firstPartialResidue_mem E hp hn hi hz hv
  exact modularSub_mem (CountingFunction.of_polyTime hp) (CountingFunction.of_polyTime hc)
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hu) hd)

private theorem deformedValue_mem {p ell u potential : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hpotential : ComputableInPolyTime potential enc encNat)
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => (potential w + (ell w + 1) * u w * value (w, z w)) % p w) ∈
      CountingFunction a enc encNat := by
  have hscale := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_add' hell (.const 1)) hu
  have hvalue := CountingFunction.preprocess hv (ComputableInPolyTime.id'.prod hz)
  have hterm := CountingFunction.nat_mul (CountingFunction.of_polyTime hscale) hvalue
  have hsum := CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hpotential) hterm)
      ComputableInPolyTime.binary_add
  exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

theorem criticalObjectiveValue_mem {p n ell u : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => criticalObjectiveValue (p w) (n w) (ell w) (u w) (z w) (fun y => value (w, y))) ∈
      CountingFunction a enc encNat :=
  deformedValue_mem hp hell hu hz (criticalPotentialResidue_polyTime hp hn hell hz) hv

/-- Evaluating the zero-centered objective preserves the input evaluator's counting level. -/
theorem zeroObjectiveValue_mem {p n ell u : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => zeroObjectiveValue (p w) (n w) (ell w) (u w) (z w) (fun y => value (w, y))) ∈
      CountingFunction a enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hx : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0)
      (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp hf) hi
  have ht := computableInPolyTime_powMod (hp.comp hf) hx
    (ComputableInPolyTime.binary_add' (hell.comp hf) (.const 1))
  have hpotential : ComputableInPolyTime (fun w => zeroPotentialResidue (p w) (n w) (ell w) (z w))
      enc encNat := by
    simpa only [zeroPotentialResidue, Function.comp_apply] using
      unaryModularSum_polyTime hn hp ht
  exact deformedValue_mem hp hell hu hz hpotential hv

theorem criticalLowerValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (i : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 2 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalLowerValue p n ell u i.val z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
        (criticalLower ell (fun j : Fin n => ((separatedCenters ell j : ℕ) : ZMod p))
          (u : ZMod p) F i) := by
  rw [criticalLowerValue, modularSub_cast (Fact.out : p.Prime).pos,
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    criticalCenterResidue_cast]
  simp only [Nat.cast_mul]
  rw [firstPartialResidue_cast F i z value hF hp hv,
    criticalLower, map_sub, map_mul, eval_C, eval_C]
  simp only [separatedCenters, Nat.cast_pow, Nat.cast_mul]

theorem criticalObjectiveValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (z : List ℕ) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalObjectiveValue p n ell u z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
        (deformedPolynomial ell (fun j : Fin n => ((separatedCenters ell j : ℕ) : ZMod p))
          (u : ZMod p) F) := by
  rw [criticalObjectiveValue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    criticalPotentialResidue_cast, hv, deformedPolynomial, map_add, map_mul, eval_C]

/-- Over the prime field, the residue gives the value of the zero-centered deformed polynomial. -/
theorem zeroObjectiveValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (hell : 1 ≤ ell)
    (z : List ℕ) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (zeroObjectiveValue p n ell u z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
        (deformedPolynomial ell (fun _ => 0) (u : ZMod p) F) := by
  rw [zeroObjectiveValue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    hv, deformedPolynomial, map_add, map_mul, eval_C]
  congr 1
  rw [zeroPotentialResidue, unaryModularSum_cast, potentialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    zero_pow (by omega : ell ≠ 0), zero_pow (Nat.succ_ne_zero ell), mul_zero, map_zero,
    zero_mul, sub_zero, add_zero, map_pow, eval_X]

end Cslib.Complexity.RealAlgebraic
