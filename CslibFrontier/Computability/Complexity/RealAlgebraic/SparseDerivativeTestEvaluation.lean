/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.UnivariateDerivativeEvaluation
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Modular evaluation of sparse derivative tests

The qualifying test occupies slot zero. Later slots look up positive derivative orders from
the list and return zero for missing entries. The lookup and dispatch preserve the counting
level of derivative evaluation when the qualifying value is available at that level.

Adapted from `LeanCanny.CountingHierarchy.BinaryDerivativeTestEvaluation` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Turing.MultiTapeTM

/-- Select the qualifying residue at slot zero or evaluate the addressed derivative.
The orders are binary naturals, with zero reserved for a missing test. -/
@[expose] noncomputable def sparseDerivativeTestResidue (p D z base : ℕ)
    (c : ℕ → ℕ) (orders : List ℕ) (i : ℕ) : ℕ :=
  if i = 0 then base else
    let k := orders.getD (i - 1) 0
    if k = 0 then 0 else univariateDerivativeResidue p D k z c

/-- Binary list lookup and dispatch require no additional counting-hierarchy level. -/
theorem sparseDerivativeTestResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D z base : α → ℕ} {orders : α → List ℕ} {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hbase : base ∈ CountingFunction (max a 3 + 1) enc encNat)
    (horders : ComputableInPolyTime orders enc (encList encNat))
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w : α × ℕ => sparseDerivativeTestResidue (p w.1) (D w.1) (z w.1) (base w.1)
      (fun j => c (w.1, j)) (orders w.1) w.2) ∈
        CountingFunction (max a 3 + 1) (encPair enc encNat) encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hindex := ComputableInPolyTime.binary_sub' hi (.const 1)
  have hk := ComputableInPolyTime.listGetD_binary (encA := encNat) 0 (horders.comp hf) hindex
  have hc' := CountingFunction.preprocess hc
    (g := fun w : (α × ℕ) × ℕ => (w.1.1, w.2)) (input := encPair (encPair enc encNat) encNat)
    (by fun_prop)
  have hderivative := univariateDerivativeResidue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hD.comp hf) hk (hz.comp hf) hc'
  have hmissing := CountingFunction.ite
    (CountingFunction.of_polyTime (ComputableInPolyTime.decide_eq' hk (.const 0)))
    (CountingFunction.of_polyTime (.const 0)) hderivative
  simpa only [sparseDerivativeTestResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite
      (CountingFunction.of_polyTime (ComputableInPolyTime.decide_eq' hi (.const 0)))
      (CountingFunction.preprocess hbase hf) hmissing

/-- Encoding each test by its positive derivative order gives the same evaluation as
`Polynomial.sparseRootLabelTests`, including the qualifying slot and zero padding. -/
theorem sparseDerivativeTestResidue_cast {p D N : ℕ} [Fact p.Prime]
    (q b₀ : Polynomial ℤ) (z base : ℕ) (c : ℕ → ℕ)
    (L : List (Fin D × SignType)) (hD : q.natDegree ≤ D) (hprime : D < p)
    (hc : ∀ j ≤ D, (c j : ZMod p) = (q.map (Int.castRingHom (ZMod p))).coeff j)
    (hbase : (base : ZMod p) = b₀.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p))
    (i : Fin (N + 1)) :
    (sparseDerivativeTestResidue p D z base c (L.map (fun t => t.1.val + 1)) i.val : ZMod p) =
      (Polynomial.sparseRootLabelTests q b₀ N L i).1.eval₂ (Int.castRingHom (ZMod p))
        (z : ZMod p) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [sparseDerivativeTestResidue, Fin.val_zero, ite_true,
      Polynomial.sparseRootLabelTests, Fin.cases_zero] using hbase
  · simp only [sparseDerivativeTestResidue, Fin.val_succ, Nat.add_one_ne_zero,
      ite_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_map,
      Polynomial.sparseRootLabelTests, Fin.cases_succ]
    cases L[j.val]? with
    | none => simp
    | some t =>
      simp only [Option.map_some, Option.getD_some, Nat.add_one_ne_zero,
        ite_false, Option.elim_some]
      rw [univariateDerivativeResidue_cast (q.map (Int.castRingHom (ZMod p)))
        (Polynomial.natDegree_map_le.trans hD) hprime c hc,
        Polynomial.iterate_derivative_map, Polynomial.eval_map]

end Cslib.Complexity.RealAlgebraic
