/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.Coordinates
import Mathlib.Algebra.BigOperators.Fin

/-!
# Horner evaluation of binary coordinate words

`hornerBits` evaluates a polynomial whose coefficients are coordinate words, using a supplied
multiplication operation. Coefficients are indexed in increasing degree; evaluation processes
them from highest to lowest degree and retains one accumulator. This is the evaluator used by
the Justesen code family, shared with its native workspace implementation.

`fieldOfBits_hornerBits` identifies the result with polynomial evaluation whenever the supplied
multiplication agrees with multiplication in the chosen binary-field basis.
-/

public section

namespace Cslib.BinaryField

/-- Evaluate coefficient words in increasing-degree order using Horner's rule. Missing bits
are zero and each addition returns exactly `b` coordinates; the empty polynomial returns `[]`. -/
def hornerBits (b : ℕ) (mul : List Bool → List Bool → List Bool) (x : List Bool)
    {k : ℕ} (coeff : Fin k → List Bool) : List Bool :=
  Fin.foldr k (fun i acc => BitString.listXor b [coeff i, mul acc x]) []

/-- Horner's fold can be executed with a descending counter and one accumulator. The
coefficient function is queried only at indices below `k`; no list of indices is allocated. -/
theorem hornerBits_eq_iterate (b : ℕ) (mul : List Bool → List Bool → List Bool)
    (x : List Bool) (coeff : ℕ → List Bool) (k : ℕ) :
    hornerBits b mul x (fun i : Fin k => coeff i) =
      ((fun s : ℕ × List Bool =>
        (s.1 - 1, BitString.listXor b [coeff (s.1 - 1), mul s.2 x]))^[k] (k, [])).2 := by
  let step := fun s : ℕ × List Bool =>
    (s.1 - 1, BitString.listXor b [coeff (s.1 - 1), mul s.2 x])
  have h (n : ℕ) (acc : List Bool) :
      step^[n] (n, acc) =
        (0, Fin.foldr n (fun i acc => BitString.listXor b [coeff i, mul acc x]) acc) := by
    induction n generalizing acc with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, show step (n + 1, acc) =
        (n, BitString.listXor b [coeff n, mul acc x]) by simp [step], ih,
        Fin.foldr_succ_last]
      rfl
  exact (congrArg Prod.snd (h k [])).symm

/-- Horner evaluation agrees with the sum of the represented monomials. -/
theorem fieldOfBits_hornerBits {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {b k : ℕ} (B : Module.Basis (Fin b) (ZMod 2) F)
    {mul : List Bool → List Bool → List Bool}
    (hmul : ∀ a b, fieldOfBits B (mul a b) =
      fieldOfBits B a * fieldOfBits B b)
    (x : List Bool) (coeff : Fin k → List Bool) :
    fieldOfBits B (hornerBits b mul x coeff) =
      ∑ i, fieldOfBits B (coeff i) * fieldOfBits B x ^ i.val := by
  induction k with
  | zero => simp [hornerBits]
  | succ k ih =>
    unfold hornerBits
    simp only [Fin.foldr_succ, fieldOfBits_listXor, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hmul]
    rw [show fieldOfBits B (Fin.foldr k
        (fun i acc => BitString.listXor b [coeff i.succ, mul acc x]) []) = _ from
      ih (fun i => coeff i.succ)]
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      Finset.sum_mul, mul_assoc]

end Cslib.BinaryField
