/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Pairing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Data.Nat.Size

/-!
# Polynomial-time arithmetic on unary counters

Arithmetic on `encUnary`, built from Christian Reitwiessner's encodings and machine calculus.
Addition concatenates the unary words; multiplication folds addition while keeping a quadratic
bound on the accumulator. Fixed powers and fixed polynomials follow by composition. These
operations support polynomially bounded counters and list enumeration in reductions.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.indexed_polynomial_bound`: a uniform polynomial
  bound over a polynomially bounded range of indices, without computing the selected index.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_add`, `.unary_sub`, `.unary_mul`:
  arithmetic on unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_min`, `.unary_max`:
  the smaller and larger of two unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_le`, `.unary_lt`, `.unary_pair`:
  comparisons and the natural-number pairing function.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_le'`, `.unary_lt'`: comparisons of computed
  operands with the intermediate unary encodings fixed for automation.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_pow`, `.unary_eval`:
  evaluation of a fixed power or polynomial, with input and output in unary.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_to_binary`:
  conversion from unary to the binary encoding `encNat`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The indexed bound is adapted from Cslib/Computability/Probabilistic/Encoding.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Interpret one Boolean as a unary zero or one. -/
@[fun_prop]
theorem bool_toUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite _

/-- Efficient unary values share a polynomial bound over a polynomially bounded range of
indices. Selecting an index does not require a computable choice. -/
theorem indexed_polynomial_bound {f : ℕ → ℕ → ℕ} {count : ℕ → ℕ}
    (hf : ComputableInPolyTime (fun input => f input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hcount : Cslib.PolynomiallyBounded count) :
    ∃ c d : ℕ, ∀ n i, i < count n → f n i ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hf⟩ := hf.polyBounded_length.exists_le
  have hpoly : Cslib.PolynomiallyBounded (fun n => c * (2 * n + count n + 2) ^ d) := by fun_prop
  obtain ⟨C, D, hpoly⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  refine ⟨C, D, fun n i hi => ?_⟩
  have h := hf (n, i)
  simp only [length_encPair, encUnary_apply, List.length_replicate] at h
  exact h.trans ((Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d)).trans (hpoly n))

/-- Addition of unary naturals, by concatenating their encodings. -/
@[fun_prop]
theorem unary_add : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encUnary encUnary) encUnary :=
  ((ComputableInDegree.fst encUnary encUnary).append
    (ComputableInDegree.snd encUnary encUnary)
    (fun _ => by simp only [encUnary_apply, List.replicate_add])).computableInPolyTime

/-- Multiplication of unary naturals, by repeated addition. -/
@[fun_prop]
theorem unary_mul : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encUnary encUnary) encUnary := by
  have hq := fst (encPair encUnary encUnary) encBool
  have h := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encUnary)
    (par := fun p : ℕ × ℕ => p.1) (list := fun p => List.replicate p.2 true)
    (step := fun a n _ => n + a) (fst encUnary encUnary)
    ((of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp (snd encUnary encUnary))
    (const 0) (unary_add.comp (hq.snd'.prod hq.fst'))
    (growth := Prod.fst) (fst encUnary encUnary).polyBounded
    (by intros; simp)
  simpa [List.foldl_const, Nat.mul_comm] using h

/-- Take the smaller of two unary naturals. -/
@[fun_prop]
theorem unary_min : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encUnary) encUnary :=
  ComputableInDegree.unary_min.computableInPolyTime

/-- Take the larger of two unary naturals. -/
@[fun_prop]
theorem unary_max : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + (p.2 - p.1))
      (encPair encUnary encUnary) encUnary := by fun_prop
  convert h using 1
  funext p
  omega

/-- Equality of computed unary counters, fixing the intermediate encoding for proof search. -/
@[fun_prop]
theorem unary_beq {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a == right a) input encBool :=
  ComputableInPolyTime.beq hleft hright

/-- The natural-number pairing function, with both arguments and the result in unary. -/
@[fun_prop]
theorem unary_pair : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have hleft : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 * p.2 + p.1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hright : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.1 + p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  simpa [Nat.pair] using unary_lt.ite' hleft hright

/-- A fixed power of a unary natural. -/
@[fun_prop]
theorem unary_pow (d : ℕ) : ComputableInPolyTime (fun n : ℕ => n ^ d)
    encUnary encUnary := by
  induction d with
  | zero => simpa using (const (encIn := encUnary) (encOut := encUnary) 1)
  | succ d ih => simpa only [pow_succ, Function.comp_def] using unary_mul.comp (ih.prod id')

/-- Evaluate a fixed polynomial on unary naturals, with its result also in unary. -/
@[fun_prop]
theorem unary_eval (p : Polynomial ℕ) : ComputableInPolyTime p.eval encUnary encUnary := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Function.comp_def] using unary_add.comp (hp.prod hq)
  | monomial d c =>
    simpa only [Polynomial.eval_monomial, Function.comp_def] using
      unary_mul.comp ((const c).prod (unary_pow d))

end Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Add two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a + right a) input encUnary :=
  unary_add.comp (hleft.prod hright)

/-- Subtract two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a - right a) input encUnary :=
  unary_sub.comp (hleft.prod hright)

/-- Multiply two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a * right a) input encUnary :=
  unary_mul.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime
