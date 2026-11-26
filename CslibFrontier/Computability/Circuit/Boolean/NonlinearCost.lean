/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SpectralNorm

/-!
# Fourier bounds from the number of nonlinear gates

`nonlinearCost I` charges one for a nonaffine Boolean operation and zero for an affine one.
For a basis of fan-in at most two, this counts precisely the AND-type gates: XOR, negation,
constants and projections are free. The count is syntactic; an AND gate reading the same wire
twice still costs one. Circuit fanout and reuse of nonlinear intermediate values are unrestricted.

Every affine Boolean function has Fourier norm one, and every Boolean function on at most two
bits has Fourier norm at most two. The joint workspace bound of `SpectralNorm` therefore gives
Fourier norm at most `2 ^ m` for an output of a circuit with nonlinear cost `m`.
Every output Fourier coefficient is also an integer multiple of `2 ^ (-m)`. This denominator
invariant can give lower bounds even when the Fourier norm is small; `MajorityNonlinear`
applies it to majority.

## Main definitions

* `Cslib.Circuits.Boolean.nonlinearCost`: the zero-or-one cost of a Boolean operation.

## Main results

* `Cslib.Circuits.Circuit.sum_abs_fourierCoeff_signVal_eval_le_two_pow_nonlinearCost`:
  the Fourier norm of any output is at most two to the number of nonaffine gates.
* `Cslib.Circuits.Circuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost`:
  each output coefficient has denominator dividing two to the number of nonaffine gates.
-/

public section

namespace Cslib.Circuits

open Finset BitString

universe u

namespace Boolean

variable {σ : Signature.{u}}

/-- Charge one for a nonaffine Boolean operation, and zero for an affine operation.
For fan-in at most two this is the number of AND-type gates, with XOR and negation free. -/
@[expose] def nonlinearCost (I : Interpretation σ Bool) (op : σ.Op) : ℕ :=
  if IsAffine (I op) then 0 else 1

/-- Exactly the affine operations have zero nonlinear cost. -/
@[simp] theorem nonlinearCost_eq_zero_iff (I : Interpretation σ Bool) (op : σ.Op) :
    nonlinearCost I op = 0 ↔ IsAffine (I op) := by
  simp [nonlinearCost]

/-- The Fourier norm of a gate with fan-in at most two is bounded by its nonlinear cost. -/
theorem sum_abs_fourierCoeff_le_two_pow_nonlinearCost (I : Interpretation σ Bool)
    (op : σ.Op) (hArity : σ.Arity op ≤ 2) :
    ∑ S, |fourierCoeff (fun x => signVal (I op x)) S| ≤ (2 : ℝ) ^ nonlinearCost I op := by
  by_cases h : IsAffine (I op)
  · simp [nonlinearCost, h, sum_abs_fourierCoeff_signVal_eq_one_of_isAffine h]
  · simpa [nonlinearCost, h] using
      sum_abs_fourierCoeff_signVal_le_two_of_card_le_two
        (by simpa only [Fintype.card_fin] using hArity) (I op)

private theorem exists_fourierCoeff_eq_intCast_div_two_pow_nonlinearCost
    (I : Interpretation σ Bool) (op : σ.Op) (hArity : σ.Arity op ≤ 2)
    (S : Finset (Fin (σ.Arity op))) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (I op x)) S =
      z / (2 : ℝ) ^ nonlinearCost I op := by
  by_cases h : IsAffine (I op)
  · simpa [nonlinearCost, h] using exists_fourierCoeff_signVal_eq_intCast_of_isAffine h S
  · simpa [nonlinearCost, h] using
      exists_fourierCoeff_signVal_eq_intCast_div_two_of_card_le_two
        (by simpa only [Fintype.card_fin] using hArity) (I op) S

end Boolean

/-- A circuit over any Boolean basis of fan-in at most two has output Fourier norm at most
`2 ^ m`, where `m` counts nonaffine gates. Affine gates and arbitrary wire reuse are free. -/
theorem Circuit.sum_abs_fourierCoeff_signVal_eval_le_two_pow_nonlinearCost
    {σ : Signature.{u}} {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (hArity : ∀ op, σ.Arity op ≤ 2) (j : Fin m) :
    ∑ S, |fourierCoeff (fun x => signVal (c.eval I x j)) S| ≤
      (2 : ℝ) ^ c.program.cost (Boolean.nonlinearCost I) :=
  c.sum_abs_fourierCoeff_signVal_eval_le_two_pow_cost I (Boolean.nonlinearCost I)
    (fun op => Boolean.sum_abs_fourierCoeff_le_two_pow_nonlinearCost I op (hArity op)) j

/-- Every Fourier coefficient of a circuit with `m` nonaffine binary gates is an integer
multiple of `2 ^ (-m)`. Affine gates, fanout and arbitrary reuse are free. -/
theorem Circuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost
    {σ : Signature.{u}} {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (hArity : ∀ op, σ.Arity op ≤ 2) (j : Fin m) (S : Finset (Fin n)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (c.eval I x j)) S =
      z / (2 : ℝ) ^ c.program.cost (Boolean.nonlinearCost I) :=
  c.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_cost I (Boolean.nonlinearCost I)
    (fun op => Boolean.exists_fourierCoeff_eq_intCast_div_two_pow_nonlinearCost I op
      (hArity op)) j S

end Cslib.Circuits
