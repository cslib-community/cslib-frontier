/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledRelativeValue
public import CslibFrontier.Foundations.Data.MvPolynomial.PowerSection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Controlled fixed-power sections

Evaluate a power section by inserting a modular power before calling the original evaluator.
For a relative critical-value polynomial with degree parameter `d`, the section specializes
the penalty to the `((d + 1) ^ n + 1)`st power of the critical value. This preserves the
counting level and the prime cutoff. Adapted from `PowerSectionPolynomial` and
`RelativePowerSection` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
The fiberwise nonvanishing argument and the two-block criterion remain open under
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

private def sectionPoint (e p : ℕ) (z : List ℕ) : List ℕ :=
  z[0]?.getD 0 :: powMod p (z[0]?.getD 0) e :: z.drop 1

private theorem sectionPoint_polyTime {α : Type} {enc : α ↪ List Bool}
    {e p : α → ℕ} {z : α → List ℕ} (he : ComputableInPolyTime e enc encNat)
    (hp : ComputableInPolyTime p enc encNat) (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => sectionPoint (e w) (p w) (z w)) enc (encList encNat) := by
  have hhead : ComputableInPolyTime (fun w => (z w)[0]?.getD 0) enc encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      listGetD_binary 0 hz (const 0)
  exact (cons encNat).comp (hhead.prod ((cons encNat).comp
    ((computableInPolyTime_powMod hp hhead he).prod (listDropWithInput hz (const 1)))))

private theorem evaluation_sectionPoint {m e p : ℕ} (hp : p.Prime)
    (P : MvPolynomial (Fin (m + 2)) ℤ) (z : List ℕ) :
    evaluation P p (sectionPoint e p z) = evaluation (MvPolynomial.powerSection e P) p z := by
  let t : ZMod p := (z[0]?.getD 0 : ℕ)
  let x (i : Fin m) : ZMod p := (z[i.succ.val]?.getD 0 : ℕ)
  have hz : (fun i : Fin (m + 1) => ((z[i.val]?.getD 0 : ℕ) : ZMod p)) = Fin.cons t x :=
    (Fin.cons_self_tail _).symm
  have hpoint : (fun i : Fin (m + 2) =>
      (((sectionPoint e p z)[i.val]?.getD 0 : ℕ) : ZMod p)) = Fin.cons t (Fin.cons (t ^ e) x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · simp only [sectionPoint, Fin.val_succ, Fin.val_zero, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, Fin.cons_succ, Fin.cons_zero, t,
        powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow]
    · simp only [sectionPoint, Fin.val_succ, List.getElem?_cons_succ, List.getElem?_drop,
        Fin.cons_succ, x, Nat.add_comm 1 k.val]
  rw [evaluation, evaluation, hpoint, hz, eval₂_powerSection]

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}

/-- Take the power section of a controlled family using a binary-computable exponent and
a unary trailing arity. Evaluation stays at the original counting level. -/
noncomputable def powerSection {P : (w : α) → MvPolynomial (Fin (m w + 2)) ℤ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (e : α → ℕ) (he : ComputableInPolyTime e enc encNat) :
    Controlled (fun w => MvPolynomial.powerSection (e w) (P w)) enc a where
  arity_computable := unary_add' hm (.const 1)
  degreeBound w := C.degreeBound w * (e w + 1)
  degree_computable := binary_mul' C.degree_computable (binary_add' he (.const 1))
  degree_le w := (totalDegree_powerSection_le _ _).trans (Nat.mul_le_mul_right _ (C.degree_le w))
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (coeffNorm1_powerSection_le _ _).trans (C.mass_le w)
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate := fun (w, p, z) => C.evaluate (w, p, sectionPoint (e w) p z)
  evaluate_mem := by
    have hw := fst enc (encPair encNat (encList encNat))
    have hpoint := snd enc (encPair encNat (encList encNat))
    have hp := (fst encNat (encList encNat)).comp hpoint
    have hz := (snd encNat (encList encNat)).comp hpoint
    exact CountingFunction.preprocess C.evaluate_mem
      (hw.prod (hp.prod (sectionPoint_polyTime (he.comp hw) hp hz)))
  evaluate_eq w p z hp hcut :=
    (C.evaluate_eq w p _ hp hcut).trans (evaluation_sectionPoint hp _ _)

/-- Specialize the even-degree relative critical-value family by substituting the critical
value raised to the quotient dimension plus one for the penalty. -/
noncomputable def relativeValueSection {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => finiteRelativeValueSection
      (by omega : 1 ≤ 2 * (C.degreeBound w + 1) + 1) (P w)
      ((C.degree_le w).trans (by omega))) enc (a + 10) := by
  have hd := binary_mul' (.const 2) (binary_add' C.degree_computable (.const 1))
  exact (C.relativeValueFamily E hn hm).powerSection hm _
    (binary_add' (binary_pow' (binary_add' hd (.const 1)) hn) (.const 1))

end Cslib.Complexity.RealAlgebraic.Controlled
