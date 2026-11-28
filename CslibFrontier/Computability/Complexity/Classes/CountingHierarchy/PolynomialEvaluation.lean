/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial evaluation from modular coefficient access

Summing weighted coefficient residues up to a binary degree bound uses one counting level.
The correctness statement applies to every positive modulus. Adapted from
`LeanCanny.CountingHierarchy.binaryPolynomialValue` at lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- Evaluate the coefficient stream through index `D` at `t` modulo `p`. -/
noncomputable def polynomialResidue (p D t : ℕ) (coeff : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range (D + 1), coeff k * powMod p t k) % p

/-- A positive modulus gives a canonical natural residue. -/
theorem polynomialResidue_lt {p : ℕ} (hp : 0 < p) (D t : ℕ) (coeff : ℕ → ℕ) :
    polynomialResidue p D t coeff < p :=
  Nat.mod_lt _ hp

/-- Evaluation uses one counting level above its coefficient access.
The modulus, evaluation point, degree bound, and coefficient index are binary. -/
theorem polynomialResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D t : α → ℕ} {coeff : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (ht : ComputableInPolyTime t enc encNat)
    (hc : coeff ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => polynomialResidue (p w) (D w) (t w) (fun k => coeff (w, k))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hw := fst enc encNat
  have hpow := computableInPolyTime_powMod (hp.comp hw) (ht.comp hw) (snd enc encNat)
  exact CountingFunction.nat_mod
    (CountingFunction.sum_range E (CountingFunction.nat_mul hc (CountingFunction.of_polyTime hpow))
      (binary_add' hD (.const 1)))
    (CountingFunction.of_polyTime hp)

/-- A complete sequence of mapped coefficients gives evaluation over `ZMod p`. -/
theorem polynomialResidue_cast {R : Type*} [Semiring R] {p : ℕ} (hp : p ≠ 0)
    (φ : R →+* ZMod p) (P : Polynomial R) (D t : ℕ) (hD : P.natDegree ≤ D)
    (coeff : ℕ → ℕ) (hc : ∀ k ≤ D, (coeff k : ZMod p) = φ (P.coeff k)) :
    (polynomialResidue p D t coeff : ZMod p) = P.eval₂ φ (t : ZMod p) := by
  rw [polynomialResidue, ZMod.natCast_mod, Nat.cast_sum,
    Polynomial.eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hD)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_mul, powMod_of_ne_zero hp, ZMod.natCast_mod, Nat.cast_pow,
    hc k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

end Cslib.Complexity
