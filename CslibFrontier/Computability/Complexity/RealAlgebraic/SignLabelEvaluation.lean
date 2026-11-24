/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.UnaryModularList
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomial
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
import CslibFrontier.Computability.Complexity.RealAlgebraic.DyadicSignEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Modular evaluation of an integer sign label

The dyadic test evaluations contribute three counting levels. The denominator products and
the sum of squares range over the unary number of tests, so they stay at that level. Products
with one denominator omitted are evaluated directly, including when a denominator is zero.

The weighted fingerprint label uses binary-length addresses for its denominator products.
Its evaluator agrees with the integer label at every prime.

Adapted from `RootLabelModularEvaluation`, `RootLabelModularCorrectness`, `RootLabelEvaluation`,
and `FingerprintModularCorrectness` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the precisions of the integer labels.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM
open scoped BigOperators

private theorem prod_omit_eq {R : Type*} [CommMonoid R] {n : ℕ} (d : Fin n → R) (i : Fin n) :
    (∏ j : Fin n, if j = i then 1 else d j) = ∏ j ∈ Finset.univ.erase i, d j := by
  rw [← Finset.prod_ite_mem_eq (Finset.univ.erase i) d]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, ite_not]

private def clearedSignLabelResidue (p m : ℕ) (den num target : ℕ → ℕ) : ℕ :=
  let common := unaryModularProduct m p den
  modularSub p (powMod p common 2) (4 * unaryModularSum m p fun i =>
    let omitted := unaryModularProduct m p (fun j => if j = i then 1 else den j)
    powMod p (modularSub p (num i) (target i * den i) * omitted) 2)

private theorem clearedSignLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {p m : α → ℕ} {den num target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hm : ComputableInPolyTime m enc encUnary) (hpos : ∀ w, 0 < p w)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat)
    (htarget : target ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => clearedSignLabelResidue (p w) (m w)
      (fun i => den (w, i)) (fun i => num (w, i)) (fun i => target (w, i))) ∈
        CountingFunction a enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hp' := CountingFunction.of_polyTime (a := a) (hp.comp hf)
  have hden' := CountingFunction.preprocess hden
    (input := encPair (encPair enc encNat) encNat)
    (g := fun w : (α × ℕ) × ℕ => (w.1.1, w.2)) (by fun_prop)
  have heq : ComputableInPolyTime (fun w : (α × ℕ) × ℕ => decide (w.2 = w.1.2))
      (encPair (encPair enc encNat) encNat) encBool := by fun_prop
  have hfactor := CountingFunction.ite (CountingFunction.of_polyTime heq)
    (CountingFunction.of_polyTime (.const 1)) hden'
  simp only [decide_eq_true_eq] at hfactor
  have homit := unaryModularProduct_mem (hm.comp hf) (hp.comp hf) (fun w => hpos w.1) hfactor
  have hdiff := modularSub_mem hp' hnum (CountingFunction.nat_mul htarget hden)
  have hterm := CountingFunction.powMod hp' (CountingFunction.nat_mul hdiff homit)
    (CountingFunction.of_polyTime (.const 2))
  have hsum := unaryModularSum_mem hm hp hpos hterm
  have hcommon := unaryModularProduct_mem hm hp hpos hden
  exact modularSub_mem (CountingFunction.of_polyTime hp)
    (CountingFunction.powMod (CountingFunction.of_polyTime hp) hcommon
      (CountingFunction.of_polyTime (.const 2)))
    (CountingFunction.nat_mul (CountingFunction.of_polyTime (.const 4)) hsum)

/-- Evaluate the cleared sign label from addressed test values and target residues. A zero
input modulus is treated as one to keep the modular aggregation total. -/
noncomputable def signLabelResidue (p B m : ℕ) (value target : ℕ → ℕ) : ℕ :=
  let q := max 1 p
  clearedSignLabelResidue q m (fun i => signTestDenominatorResidue q B (m + 1) (value i))
    (fun i => signTestNumeratorResidue q B (m + 1) (value i)) target

/-- A unary number of cleared tests preserves the level `F_(a+3)` of the dyadic evaluations. -/
theorem signLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B m : α → ℕ} {value target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hm : ComputableInPolyTime m enc encUnary)
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat)
    (ht : target ∈ CountingFunction (a + 3) (encPair enc encNat) encNat) :
    (fun w => signLabelResidue (p w) (B w) (m w)
      (fun i => value (w, i)) (fun i => target (w, i))) ∈ CountingFunction (a + 3) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hq := ComputableInPolyTime.binary_max' (.const 1) hp
  have hs : ComputableInPolyTime (fun w => m w + 1) enc encNat :=
    ComputableInPolyTime.binary_add' (ComputableInPolyTime.unary_to_binary.comp hm) (.const 1)
  have htests := signTestResidues_mem (Decoder.pair E Decoder.nat) (hq.comp hf)
    (hB.comp hf) (hs.comp hf) hv
  have hpos (w : α) : 0 < max 1 (p w) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  simpa only [signLabelResidue, Function.comp_apply] using
    clearedSignLabelResidue_mem hq hm hpos htests.1 htests.2 ht

/-- At every prime, the evaluator agrees with the integer sign label, including when some
cleared denominators vanish. Only test and target values at genuine indices are needed. -/
theorem signLabelResidue_cast {p m : ℕ} [Fact p.Prime] (B : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) (x : ZMod p)
    (value target : ℕ → ℕ)
    (hv : ∀ i : Fin m, (value i.val : ZMod p) = (g i).eval₂ (Int.castRingHom (ZMod p)) x)
    (ht : ∀ i : Fin m, (target i.val : ZMod p) = ((t i : ℤ) : ZMod p)) :
    (signLabelResidue p B m value target : ZMod p) =
      (Polynomial.signLabelPolynomial B g t).eval₂ (Int.castRingHom (ZMod p)) x := by
  let f := (Polynomial.dyadicSignProduct B (m + 1)).eval₂ (Int.castRingHom (ZMod p))
  let v (i : Fin m) := (g i).eval₂ (Int.castRingHom (ZMod p)) x
  let d (i : Fin m) := f (v i) + f (-v i)
  let den (i : ℕ) := signTestDenominatorResidue p B (m + 1) (value i)
  let num (i : ℕ) := signTestNumeratorResidue p B (m + 1) (value i)
  have hden (i : Fin m) : (den i.val : ZMod p) = d i := by
    simpa only [den, d, f, v, ← hv i] using (signTestResidues_cast (p := p) B (m + 1)
      (value i.val)).1
  have hnum (i : Fin m) : (num i.val : ZMod p) = f (v i) - f (-v i) := by
    simpa only [num, f, v, ← hv i] using (signTestResidues_cast (p := p) B (m + 1)
      (value i.val)).2
  have hp : p.Prime := Fact.out
  rw [signLabelResidue, max_eq_right hp.one_le]
  change (clearedSignLabelResidue p m den num target : ZMod p) = _
  rw [clearedSignLabelResidue, modularSub_cast hp.pos, powMod_of_ne_zero hp.ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, unaryModularProduct_cast, Nat.cast_mul, Nat.cast_ofNat,
    unaryModularSum_cast, Polynomial.signLabelPolynomial]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_comp, Polynomial.eval₂_neg, Int.coe_castRingHom,
    Int.cast_ofNat]
  change (∏ i : Fin m, (den i.val : ZMod p)) ^ 2 - _ =
    (∏ i, d i) ^ 2 - 4 * ∑ i, ((f (v i) - f (-v i) - ((t i : ℤ) : ZMod p) * d i) *
      ∏ j ∈ Finset.univ.erase i, d j) ^ 2
  simp only [hden]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow, Nat.cast_mul,
    modularSub_cast hp.pos, Nat.cast_mul, hnum, ht, hden, unaryModularProduct_cast]
  simp only [Nat.cast_ite, Nat.cast_one, Fin.val_inj, hden]
  rw [prod_omit_eq]

/-- Evaluate the cleared fingerprint label from addressed test residues. The test at
index zero qualifies the point and weight `i` attaches to test `i + 1`. Both the
common denominator and its omitted-factor products use binary factor counts.
A zero modulus is treated as one. -/
noncomputable def fingerprintLabelResidue (p B M m : ℕ) (value weight : ℕ → ℕ)
    (target : ℕ) : ℕ :=
  let q := max 1 p
  let den (i : ℕ) := signTestDenominatorResidue q B (M + 1) (value i)
  let num (i : ℕ) := signTestNumeratorResidue q B (M + 1) (value i)
  let common := primeFieldRangeProduct q (m + 1) den
  let cleared (i : ℕ) :=
    num i * primeFieldRangeProduct q (m + 1) (fun j => if j = i then 1 else den j)
  let weighted := (∑ i ∈ Finset.range m, weight i * cleared (i + 1)) % q
  let score := modularSub q weighted (target * common)
  let qualifier := modularSub q (cleared 0) common
  modularSub q (powMod q common 2) (4 * (powMod q score 2 + powMod q qualifier 2))

/-- At every prime the addressed residue evaluator gives the integer fingerprint label.
Only genuine test and weight indices need correct values, and denominators may vanish. -/
theorem fingerprintLabelResidue_cast {p m : ℕ} [Fact p.Prime] (B M : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ) (x : ZMod p)
    (value weight : ℕ → ℕ) (targetValue : ℕ)
    (hv : ∀ i : Fin (m + 1), (value i.val : ZMod p) = (g i).eval₂ (Int.castRingHom (ZMod p)) x)
    (hw : ∀ i : Fin m, (weight i.val : ZMod p) = (w i : ZMod p))
    (ht : (targetValue : ZMod p) = (target : ZMod p)) :
    (fingerprintLabelResidue p B M m value weight targetValue : ZMod p) =
      (Polynomial.fingerprintLabelPolynomial B M g w target).eval₂
        (Int.castRingHom (ZMod p)) x := by
  let f := (Polynomial.dyadicSignProduct B (M + 1)).eval₂ (Int.castRingHom (ZMod p))
  let v (i : Fin (m + 1)) := (g i).eval₂ (Int.castRingHom (ZMod p)) x
  let d (i : Fin (m + 1)) := f (v i) + f (-v i)
  let t (i : Fin (m + 1)) := (f (v i) - f (-v i)) * ∏ j ∈ Finset.univ.erase i, d j
  let den (i : ℕ) := signTestDenominatorResidue p B (M + 1) (value i)
  let num (i : ℕ) := signTestNumeratorResidue p B (M + 1) (value i)
  let P := primeFieldRangeProduct p (m + 1) den
  let T (i : ℕ) := num i * primeFieldRangeProduct p (m + 1) (fun j => if j = i then 1 else den j)
  let S := ∑ i ∈ Finset.range m, weight i * T (i + 1)
  have htests (i : Fin (m + 1)) :
      (den i.val : ZMod p) = d i ∧ (num i.val : ZMod p) = f (v i) - f (-v i) := by
    simpa only [den, num, d, f, v, ← hv i] using
      signTestResidues_cast (p := p) B (M + 1) (value i.val)
  have hP : (P : ZMod p) = ∏ i, d i := by
    dsimp only [P]
    rw [primeFieldRangeProduct_cast]
    exact Finset.prod_congr rfl fun i _ => (htests i).1
  have hT (i : Fin (m + 1)) : (T i.val : ZMod p) = t i := by
    dsimp only [T]
    rw [Nat.cast_mul, (htests i).2, primeFieldRangeProduct_cast]
    simp only [t, Nat.cast_ite, Nat.cast_one, Fin.val_inj, fun j => (htests j).1, prod_omit_eq]
  have hS : (S : ZMod p) = ∑ i : Fin m, (w i : ZMod p) * t i.succ := by
    dsimp only [S]
    rw [Nat.cast_sum, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul, hw i]
    exact congrArg ((w i : ZMod p) * ·) (hT i.succ)
  have hzero : (T 0 : ZMod p) = t 0 := hT 0
  have hp : p.Prime := Fact.out
  rw [fingerprintLabelResidue, max_eq_right hp.one_le]
  change (modularSub p (powMod p P 2)
    (4 * (powMod p (modularSub p (S % p) (targetValue * P)) 2 +
      powMod p (modularSub p (T 0) P) 2)) : ZMod p) = _
  simp only [modularSub_cast hp.pos, powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, hP, hS, ht, hzero]
  simp only [Polynomial.fingerprintLabelPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_comp, Polynomial.eval₂_neg, Int.coe_castRingHom,
    Int.cast_ofNat, Int.cast_natCast, d, t, f, v]

end Cslib.Complexity.RealAlgebraic
