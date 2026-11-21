/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.UnaryModularList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Modular evaluation of separated critical potentials

Centers and potential summands use modular powers, including when the corresponding integer
centers are exponentially large. Unary arity permits the bounded sum without expanding any
large power. Correctness identifies the values with the actual separated potential polynomial.

Extracted from the center/potential portion of
`LeanCanny.CountingHierarchy.CriticalNumericEvaluation`
at lean-canny commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`. Specialization and root-label
bounds are separate later work under
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial MvPolynomial.CriticalSystem
open scoped BigOperators

/-- Compute a separated center without constructing its unreduced power. -/
@[expose] def criticalCenterResidue (p ell i : ℕ) : ℕ := powMod p (4 * ell) (i + 1)

/-- One separated-potential summand, evaluated by modular powering. -/
@[expose] def criticalPotentialTermResidue (p ell i x : ℕ) : ℕ :=
  (modularSub p (powMod p x (ell + 1))
      ((ell + 1) * powMod p (criticalCenterResidue p ell i) ell * x) +
    (ell + 1) * powMod p (criticalCenterResidue p ell i) (ell + 1)) % p

/-- The total separated potential, summed over unary-many coordinates. -/
@[expose] noncomputable def criticalPotentialResidue (p n ell : ℕ) (z : List ℕ) : ℕ :=
  unaryModularSum n (max 1 p) (fun i => criticalPotentialTermResidue p ell i (z[i]?.getD 0))

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem criticalCenterResidue_polyTime {p ell i : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hell : ComputableInPolyTime ell enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun w => criticalCenterResidue (p w) (ell w) (i w)) enc encNat :=
  computableInPolyTime_powMod hp (ComputableInPolyTime.binary_mul' (.const 4) hell)
    (ComputableInPolyTime.binary_add' hi (.const 1))

@[fun_prop] theorem criticalPotentialTermResidue_polyTime {p ell i x : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hell : ComputableInPolyTime ell enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun w => criticalPotentialTermResidue (p w) (ell w) (i w) (x w))
      enc encNat := by
  have hcenter := criticalCenterResidue_polyTime hp hell hi
  have he := ComputableInPolyTime.binary_add' hell (.const 1)
  have hfirst := computableInPolyTime_powMod hp hx he
  have hlinear := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_mul' he (computableInPolyTime_powMod hp hcenter hell)) hx
  have hlast := ComputableInPolyTime.binary_mul' he (computableInPolyTime_powMod hp hcenter he)
  exact ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_add' (modularSub_polyTime hp hfirst hlinear) hlast).prod hp)

/-- The separated potential is polynomial-time computable with unary arity. -/
@[fun_prop] theorem criticalPotentialResidue_polyTime {p n ell : α → ℕ} {z : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => criticalPotentialResidue (p w) (n w) (ell w) (z w))
      enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hx : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0)
      (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp hf) hi
  have ht := criticalPotentialTermResidue_polyTime (hp.comp hf) (hell.comp hf) hi hx
  simpa only [criticalPotentialResidue, Function.comp_apply] using
    unaryModularSum_polyTime hn (ComputableInPolyTime.binary_max' (.const 1) hp) ht

theorem criticalCenterResidue_cast {p : ℕ} [Fact p.Prime] (ell i : ℕ) :
    (criticalCenterResidue p ell i : ZMod p) = ((4 * ell : ℕ) : ZMod p) ^ (i + 1) := by
  rw [criticalCenterResidue, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow]

theorem criticalPotentialResidue_cast {p n : ℕ} [Fact p.Prime] (ell : ℕ) (z : List ℕ) :
    (criticalPotentialResidue p n ell z : ZMod p) =
      eval (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p))
        (potentialPolynomial ell (fun i : Fin n => ((separatedCenters ell i : ℕ) : ZMod p))) := by
  rw [criticalPotentialResidue, max_eq_right (Fact.out : p.Prime).one_le, unaryModularSum_cast,
    potentialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [criticalPotentialTermResidue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, Nat.cast_pow,
    modularSub_cast (Fact.out : p.Prime).pos, criticalCenterResidue_cast,
    map_add, map_sub, map_mul, map_pow, eval_X, eval_C, separatedCenters]

end Cslib.Complexity.RealAlgebraic
