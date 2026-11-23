/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.Freivalds

/-!
# Freivalds' Matrix-Product Verification

Freivalds' algorithm (`[Freivalds1977]`, `[Freivalds1979]`; `[MitzenmacherUpfal2017]`, Section 1.3;
`[MotwaniRaghavan95]`, Section 7.1) checks a claimed product `A * B = C` without multiplying
matrices. It draws random vectors `x` and accepts when `A *ᵥ (B *ᵥ x) = C *ᵥ x` for every
drawn vector, evaluating three matrix-vector products and one vector comparison per trial.

This module defines the single-vector check `check` and the randomized verifier `verify` as a
`ProbComp` program that samples `k` vectors uniformly and tests `check` on each. Entries of `x` are
drawn from a finite set `S` and encoded in the ring by `e : S → R`. The soundness analysis needs
only that every nonzero `d` makes `s ↦ d * e s` injective (see
`Cslib.Probability.card_filter_mulVec_eq_mul_card_le`). A machine-level implementation on the
randomized word RAM with explicit instruction and `rand`-call bounds lives in
`CslibFrontier.Algorithms.WordRAM.Freivalds`.

## Source Conventions

* **Matrices:** `A : Matrix (Fin l) (Fin m) R`, `B : Matrix (Fin m) (Fin n) R` and
  `C : Matrix (Fin l) (Fin n) R` are rectangular over any ring `R` with decidable equality,
  rather than the square matrices over the integers modulo `2` of `[MitzenmacherUpfal2017]`,
  Section 1.3.
* **Random vectors:** `verify e k` draws all `k` vectors `Fin k → Fin n → S` from one uniform
  law. This is the product of `k` independent uniform vectors.
* **Error:** one-sided. A correct product is accepted with probability `1`
  (`eval_verify_of_mul_eq`). An incorrect product is accepted with probability at most
  `(1/|S|)^k` (`eval_verify_true_le`): `(1/2)^k` for `0`/`1` vectors over any ring
  (`eval_verify_bool_true_le` with `Cslib.Probability.bit`, the case `k = 1` being
  `[MitzenmacherUpfal2017]`, Theorem 1.4),
  and `(1/|F|)^k` for uniform vectors over a finite field (`eval_verify_field_true_le`).

## Main definitions

* `Cslib.Algorithms.Lean.Freivalds.check`: one deterministic check `A *ᵥ (B *ᵥ x) = C *ᵥ x`.
* `Cslib.Algorithms.Lean.Freivalds.verify`: the randomized verifier with `k` uniform vectors.

## Main results

* `check_eq_decide`: associativity identity `check A B C x = decide ((A * B) *ᵥ x = C *ᵥ x)`.
* `eval_verify`: exact output distribution of `verify`.
* `eval_verify_of_mul_eq`: perfect completeness.
* `eval_verify_true_le`: soundness error at most `(1/|S|)^k` for any admissible encoding.
* `eval_verify_bool_true_le`: soundness error at most `(1/2)^k` for `0`/`1` vectors.
* `eval_verify_field_true_le`: soundness error at most `(1/|F|)^k` over a finite field `F`.

## References

* [R. Freivalds, *Probabilistic machines can use less running time*][Freivalds1977]
* [R. Freivalds, *Fast probabilistic algorithms*][Freivalds1979]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
-/

public section

namespace Cslib.Algorithms.Lean.Freivalds

open scoped Matrix ENNReal
open Cslib.Probability

variable {R : Type} [Ring R] [DecidableEq R] {l m n : ℕ}

/-- One deterministic Freivalds check: compute `B *ᵥ x`, `A *ᵥ (B *ᵥ x)` and `C *ᵥ x`, and
compare `A *ᵥ (B *ᵥ x)` with `C *ᵥ x`. -/
@[expose]
def check (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (x : Fin n → R) : Bool :=
  decide (A *ᵥ (B *ᵥ x) = C *ᵥ x)

/-- By associativity of matrix-vector multiplication, `check` tests `(A * B) *ᵥ x = C *ᵥ x`. -/
@[simp] theorem check_eq_decide (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) (x : Fin n → R) :
    check A B C x = decide ((A * B) *ᵥ x = C *ᵥ x) := by
  rw [check, Matrix.mulVec_mulVec]

/-- Freivalds' randomized verifier: draw `k` independent uniform vectors in `Fin n → S`, encode
their entries with `e`, and accept when every vector passes `check A B C`. -/
noncomputable def verify {S : Type} [Fintype S] [Nonempty S] (e : S → R) (k : ℕ)
    (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin l) (Fin n) R) : ProbComp Bool := do
  let xs ← ProbComp.uniform (Fin k → Fin n → S)
  pure (decide (∀ t, check A B C (e ∘ xs t) = true))

section Soundness

variable {S : Type} [Fintype S] [Nonempty S]

/-- The law of the verifier: the indicator that all `k` checks pass, pushed forward from the
uniform law on `Fin k → Fin n → S`. -/
theorem eval_verify (e : S → R) (k : ℕ) (A : Matrix (Fin l) (Fin m) R)
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin l) (Fin n) R) :
    ProbComp.eval (verify e k A B C) = (PMF.uniformOfFintype (Fin k → Fin n → S)).map
      fun xs => decide (∀ t, (A * B) *ᵥ (e ∘ xs t) = C *ᵥ (e ∘ xs t)) := by
  rw [verify, ProbComp.eval_bind, ProbComp.eval_uniform]
  simp only [ProbComp.eval_pure, check_eq_decide, decide_eq_true_eq]
  rfl

/-- Perfect completeness: a correct product is always accepted. -/
theorem eval_verify_of_mul_eq (e : S → R) (k : ℕ) {A : Matrix (Fin l) (Fin m) R}
    {B : Matrix (Fin m) (Fin n) R} {C : Matrix (Fin l) (Fin n) R} (h : A * B = C) :
    ProbComp.eval (verify e k A B C) = PMF.pure true := by
  simp only [eval_verify, h, implies_true, decide_true]
  exact PMF.map_const _ _

/-- Soundness: if `A * B ≠ C`, the verifier accepts with probability at most `(1/|S|)^k`. -/
theorem eval_verify_true_le {e : S → R}
    (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s) (k : ℕ)
    {A : Matrix (Fin l) (Fin m) R} {B : Matrix (Fin m) (Fin n) R}
    {C : Matrix (Fin l) (Fin n) R} (h : A * B ≠ C) :
    ProbComp.eval (verify e k A B C) true ≤ ((Fintype.card S : ℝ≥0∞)⁻¹) ^ k := by
  have hbound := toOuterMeasure_forall_mulVec_eq_le (κ := Fin k) (S := S) he h
  rw [Fintype.card_fin] at hbound
  rw [eval_verify, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  convert hbound using 2
  ext xs
  simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.mem_ofPred_eq]

end Soundness

/-- Freivalds' verifier with `0`/`1` vectors accepts an incorrect product with probability at
most `(1/2)^k`. The case `k = 1` is `[MitzenmacherUpfal2017]`, Theorem 1.4. -/
theorem eval_verify_bool_true_le (k : ℕ) {A : Matrix (Fin l) (Fin m) R}
    {B : Matrix (Fin m) (Fin n) R} {C : Matrix (Fin l) (Fin n) R} (h : A * B ≠ C) :
    ProbComp.eval (verify bit k A B C) true ≤ 2⁻¹ ^ k := by
  have := eval_verify_true_le (S := Bool) (e := bit) injective_mul_bit k h
  rwa [Fintype.card_bool, Nat.cast_ofNat] at this

/-- Over a finite field with uniform vectors, Freivalds' verifier accepts an incorrect product
with probability at most `(1/|F|)^k`. -/
theorem eval_verify_field_true_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (k : ℕ)
    {A : Matrix (Fin l) (Fin m) F} {B : Matrix (Fin m) (Fin n) F}
    {C : Matrix (Fin l) (Fin n) F} (h : A * B ≠ C) :
    ProbComp.eval (verify id k A B C) true ≤ ((Fintype.card F : ℝ≥0∞)⁻¹) ^ k :=
  eval_verify_true_le (fun _ hd => mul_right_injective₀ hd) k h

end Cslib.Algorithms.Lean.Freivalds
