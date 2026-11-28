/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Robust
import CslibFrontier.Foundations.Data.Code.BerlekampWelch
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete Tests and Counterexamples for Robust Shamir Reconstruction

Exercises `Cslib.Crypto.Protocols.SecretSharing.Shamir` robust reconstruction, error detection,
and Welch–Berlekamp key equations:

1. **Single-error recovery & key equation (`n = 4, t = 1, e = 1` over `ZMod 7`):** honest shares
   `(5, 0, 2, 4)` for secret `3`, tampered at party `2` (`2 ↦ 6`); verifies `robustReconstruct`
   detects tampering at `e = 0`, recovers `some 3` at `e = 1`, and checks an explicit
   `BerlekampWelch.IsSolution` `(E, Q)`.
2. **Two-error BGW recovery & unnormalized key equation (`n = 7, t = 2, e = 2` over `ZMod 11`):**
   honest shares for `f(X) = 5 + 3 X + 4 X^2` with 2 corrupted parties; verifies detection at
   `e = 0`, recovery of `some 5` at `e = 2`, and `keyEquation_div_eq` on a non-monic,
   degree-`1 < 2` error locator `E' = 2 * (X - 2)` for a single-error word.
3. **Boundary necessity (`n = 3, t = 1` over `ZMod 5`):** explicit ambiguity witness at
   `3 * t = n` where two distinct secrets `1 ≠ 2` both lie within Hamming distance `1` of
   `w₃ = ![1, 1, 4]`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.ShamirRobust

open Finset
open Cslib.Code
open Cslib.Crypto.Protocols.SecretSharing.Shamir

private local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem eval_tailPolynomial_eq_sum {F : Type*} [Field F] {n : ℕ} (r : Fin n → F)
    (hn : 0 < n) (x : F) :
    (Polynomial.tailPolynomial n r).eval x = ∑ i : Fin n, r i * x ^ (i : ℕ) := by
  have hnat : (Polynomial.tailPolynomial n r).natDegree < n := by
    by_cases hp : Polynomial.tailPolynomial n r = 0
    · rwa [hp, _root_.Polynomial.natDegree_zero]
    · exact (_root_.Polynomial.natDegree_lt_iff_degree_lt hp).2
        (Polynomial.tailPolynomial_degree_lt n r)
  rw [_root_.Polynomial.eval_eq_sum_range' hnat, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.tailPolynomial_coeff n r i]

/-! ### 1. `n = 4, t = 1, e = 1` over `ZMod 7` -/

private def params4 : Params (ZMod 7) (Fin 4) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 7)
  point_injective := by decide
  point_nonzero := by decide

private def r4 : Randomness params4 := ![2]
private def w4 : Fin 4 → ZMod 7 := ![5, 0, 6, 4]

private theorem share4_eq : share params4 r4 3 = ![5, 0, 2, 4] := by
  funext i
  rw [share, Polynomial.sharingPolynomial_eval, eval_tailPolynomial_eq_sum r4 (by decide)]
  fin_cases i <;> decide

example :
    robustReconstruct params4 0 w4 = none ∧
      robustReconstruct params4 1 w4 = some 3 := by
  have hdist : hammingDist (share params4 r4 3) w4 = 1 := by
    rw [share4_eq]
    decide
  refine ⟨?_, ?_⟩
  · exact robustReconstruct_zero_eq_none_of_errors params4 (r := r4) (a₀ := 3)
      (by omega) (by rw [hdist]; decide)
  · exact robustReconstruct_bgw_eq_some params4 (r := r4) (by decide) (by rw [hdist]; decide)

example :
    let E : _root_.Polynomial (ZMod 7) := _root_.Polynomial.X - _root_.Polynomial.C 3
    let f : _root_.Polynomial (ZMod 7) :=
      _root_.Polynomial.C 3 + _root_.Polynomial.C 2 * _root_.Polynomial.X
    let Q : _root_.Polynomial (ZMod 7) := f * E
    BerlekampWelch.IsSolution params4.point w4 1 (params4.threshold + 1) E Q ∧
      (Q /ₘ E).eval 0 = 3 := by
  intro E f Q
  have hE : E.Monic := _root_.Polynomial.monic_X_sub_C 3
  have hEdeg : E.natDegree = 1 := _root_.Polynomial.natDegree_X_sub_C 3
  have hf : f.degree < (params4.threshold + 1 : ℕ) := by
    calc f.degree
        ≤ max (_root_.Polynomial.C (3 : ZMod 7)).degree
            (_root_.Polynomial.C (2 : ZMod 7) * _root_.Polynomial.X).degree :=
          _root_.Polynomial.degree_add_le _ _
      _ < ((params4.threshold + 1 : ℕ) : WithBot ℕ) := by
          refine max_lt ?_ ?_
          · exact lt_of_le_of_lt (_root_.Polynomial.degree_C_le) (by decide)
          · calc (_root_.Polynomial.C (2 : ZMod 7) * _root_.Polynomial.X).degree
                ≤ (_root_.Polynomial.C (2 : ZMod 7)).degree + _root_.Polynomial.X.degree :=
                  _root_.Polynomial.degree_mul_le _ _
              _ ≤ (0 : WithBot ℕ) + 1 := add_le_add (_root_.Polynomial.degree_C_le)
                  (_root_.Polynomial.degree_X_le)
              _ < ((params4.threshold + 1 : ℕ) : WithBot ℕ) := by decide
  have hQdeg : Q.degree < ((1 + (params4.threshold + 1) : ℕ) : WithBot ℕ) := by
    have hf0 : f ≠ 0 := by
      intro h0
      have hc : (3 : ZMod 7) = 0 := by
        simpa [f] using congrArg (fun p : _root_.Polynomial (ZMod 7) => p.coeff 0) h0
      exact absurd hc (by decide)
    have hfnat : f.natDegree < params4.threshold + 1 :=
      (_root_.Polynomial.natDegree_lt_iff_degree_lt hf0).2 hf
    calc Q.degree
        ≤ f.degree + E.degree := _root_.Polynomial.degree_mul_le f E
      _ = ((f.natDegree + E.natDegree : ℕ) : WithBot ℕ) := by
          rw [_root_.Polynomial.degree_eq_natDegree hf0,
            _root_.Polynomial.degree_eq_natDegree hE.ne_zero, Nat.cast_add]
      _ < ((1 + (params4.threshold + 1) : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega)
  have heval : ∀ i : Fin 4, Q.eval (params4.point i) = w4 i * E.eval (params4.point i) := by
    intro i
    rw [_root_.Polynomial.eval_mul]
    fin_cases i <;>
      (dsimp only [f, E]
       simp only [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
         _root_.Polynomial.eval_sub, _root_.Polynomial.eval_X, _root_.Polynomial.eval_C]
       decide)
  have hsol : BerlekampWelch.IsSolution params4.point w4 1 (params4.threshold + 1) E Q :=
    ⟨hE, hEdeg, hQdeg, heval⟩
  refine ⟨hsol, ?_⟩
  have hdiv : Q /ₘ E = f := by
    rw [show Q = f * E from rfl, mul_comm, _root_.Polynomial.mul_divByMonic_cancel_left f hE]
  rw [hdiv]
  simp [f]

/-! ### 2. `n = 7, t = 2, e = 2` over `ZMod 11` -/

private def params7 : Params (ZMod 11) (Fin 7) where
  threshold := 2
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 11)
  point_injective := by decide
  point_nonzero := by decide

private def r7 : Randomness params7 := ![3, 4]
-- Honest shares for `5 + 3 X + 4 X^2` at `1..7 (mod 11)`: `![1, 5, 6, 4, 10, 2, 2]`.
private def w7Two : Fin 7 → ZMod 11 := ![1, 9, 6, 4, 10, 0, 2]
private def w7One : Fin 7 → ZMod 11 := ![1, 9, 6, 4, 10, 2, 2]

private theorem share7_eq : share params7 r7 5 = ![1, 5, 6, 4, 10, 2, 2] := by
  funext i
  rw [share, Polynomial.sharingPolynomial_eval, eval_tailPolynomial_eq_sum r7 (by decide)]
  fin_cases i <;> decide

example :
    robustReconstruct params7 0 w7Two = none ∧
      robustReconstruct params7 2 w7Two = some 5 := by
  have hdist : hammingDist (share params7 r7 5) w7Two = 2 := by
    rw [share7_eq]
    decide
  refine ⟨?_, ?_⟩
  · exact robustReconstruct_zero_eq_none_of_errors params7 (r := r7) (a₀ := 5)
      (by omega) (by rw [hdist]; decide)
  · exact robustReconstruct_bgw_eq_some params7 (r := r7) (by decide) (by rw [hdist]; decide)

example :
    let E' : _root_.Polynomial (ZMod 11) :=
      _root_.Polynomial.C 2 * (_root_.Polynomial.X - _root_.Polynomial.C 2)
    let Q' : _root_.Polynomial (ZMod 11) :=
      Polynomial.sharingPolynomial (5 : ZMod 11)
        (Polynomial.tailPolynomial params7.threshold r7) * E'
    (Q' / E').eval 0 = 5 := by
  intro E' Q'
  have hdist : hammingDist (share params7 r7 5) w7One ≤ 2 := by
    rw [share7_eq]
    decide
  have hE0 : E' ≠ 0 := by
    refine mul_ne_zero (_root_.Polynomial.C_ne_zero.2 (by decide))
      (_root_.Polynomial.X_sub_C_ne_zero 2)
  have hEdeg : E'.natDegree ≤ 2 := by
    dsimp only [E']
    rw [_root_.Polynomial.natDegree_C_mul (by decide : (2 : ZMod 11) ≠ 0),
      _root_.Polynomial.natDegree_X_sub_C]
    decide
  have hQdeg : Q'.degree < ((2 + (params7.threshold + 1) : ℕ) : WithBot ℕ) := by
    have hf : (Polynomial.sharingPolynomial (5 : ZMod 11)
        (Polynomial.tailPolynomial params7.threshold r7)).degree <
        ((params7.threshold + 1 : ℕ) : WithBot ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ (5 : ZMod 11)
          params7.threshold r7
    have hf0 : Polynomial.sharingPolynomial (5 : ZMod 11)
        (Polynomial.tailPolynomial params7.threshold r7) ≠ 0 := by
      intro h0
      have hc : (5 : ZMod 11) = 0 := by
        simpa [Polynomial.coeff_zero_sharingPolynomial] using
          congrArg (fun p : _root_.Polynomial (ZMod 11) => p.coeff 0) h0
      exact absurd hc (by decide)
    have hfnat : (Polynomial.sharingPolynomial (5 : ZMod 11)
        (Polynomial.tailPolynomial params7.threshold r7)).natDegree < params7.threshold + 1 :=
      (_root_.Polynomial.natDegree_lt_iff_degree_lt hf0).2 hf
    calc Q'.degree
        ≤ (Polynomial.sharingPolynomial (5 : ZMod 11)
            (Polynomial.tailPolynomial params7.threshold r7)).degree + E'.degree :=
          _root_.Polynomial.degree_mul_le _ _
      _ = (((Polynomial.sharingPolynomial (5 : ZMod 11)
            (Polynomial.tailPolynomial params7.threshold r7)).natDegree + E'.natDegree : ℕ) :
            WithBot ℕ) := by
          rw [_root_.Polynomial.degree_eq_natDegree hf0,
            _root_.Polynomial.degree_eq_natDegree hE0, Nat.cast_add]
      _ < ((2 + (params7.threshold + 1) : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega)
  have heval : ∀ i : Fin 7, Q'.eval (params7.point i) = w7One i * E'.eval (params7.point i) := by
    intro i
    dsimp only [Q']
    rw [_root_.Polynomial.eval_mul]
    have hs : (Polynomial.sharingPolynomial (5 : ZMod 11)
        (Polynomial.tailPolynomial params7.threshold r7)).eval (params7.point i) =
        share params7 r7 5 i := rfl
    rw [hs, share7_eq]
    fin_cases i <;>
      (dsimp only [E']
       simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_sub,
         _root_.Polynomial.eval_X, _root_.Polynomial.eval_C]
       decide)
  exact (keyEquation_div_eq params7 (by decide) hdist hE0 hEdeg hQdeg heval).2.2

/-! ### 3. Boundary necessity at `3 * t = n` (`n = 3, t = 1` over `ZMod 5`) -/

private def params3 : Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

private def r3₁ : Randomness params3 := ![0]
private def r3₂ : Randomness params3 := ![4]
private def w3 : Fin 3 → ZMod 5 := ![1, 1, 4]

example :
    hammingDist (share params3 r3₁ 1) w3 ≤ params3.threshold ∧
      hammingDist (share params3 r3₂ 2) w3 ≤ params3.threshold ∧
      (1 : ZMod 5) ≠ 2 := by
  have hs1 : share params3 r3₁ 1 = ![1, 1, 1] := by
    funext i
    rw [share, Polynomial.sharingPolynomial_eval, eval_tailPolynomial_eq_sum r3₁ (by decide)]
    fin_cases i <;> decide
  have hs2 : share params3 r3₂ 2 = ![1, 0, 4] := by
    funext i
    rw [share, Polynomial.sharingPolynomial_eval, eval_tailPolynomial_eq_sum r3₂ (by decide)]
    fin_cases i <;> decide
  rw [hs1, hs2]
  decide

end CslibFrontierTests.Crypto.ShamirRobust
